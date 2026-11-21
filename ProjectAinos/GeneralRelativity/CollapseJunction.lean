/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.Collapse
public import ProjectAinos.GeneralRelativity.Tolman
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinatePullback
public import ProjectAinos.SmoothGeometry.Lorentzian.WeakJunction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The weak Einstein equations of the Oppenheimer–Snyder collapse

Landau–Lifshitz, §§102–103. The flat dust ball `dustInterior` (crunch at `τ_c`, boundary shell
`χ = χ_b`) is matched to the Lemaître chart `lemaitre` on the shell `R = τ_c` when
`9 M τ_c² = 2 χ_b³` (`junction_oppenheimerSnyder`). Here the glued metric is shown to solve the
Einstein equations across the boundary, in the sense of distributions, without a surface layer.

* `isEinstein_dustInterior`, `isEinstein_lemaitre`: the comoving charts solve `G = κT` with the
  dust (`comovingDust`) and in vacuum, by `IsEinstein.pullback` from `isEinstein_dustData` (through
  `toCartesian`) and from `Tolman.ParabolicData.isEinstein_lemaitre`.
* **The adapted chart** `(T, n, θ, φ)` on a collar `collar` of the boundary `n = 0`, with `n` the
  proper distance from the boundary and `∂_n` its unit normal there:
  - outside, `exteriorMap`: the chart of Painlevé and Gullstrand shifted by the boundary radius
    `r_b(T) = a(T)χ_b` (`boundaryRadius`), `r = n + r_b(T)`, `R − τ = (2/3) r √(r/2M)`;
    `exteriorMetric` is the pullback of `lemaitre`, with the coefficients `exteriorCoeff`:
    `ds² = −dT² + (dn + (√(2M/r) + ṙ_b) dT)² + r² dΩ²`;
  - inside, `interiorMap`: `χ = χ_b + n/a(τ)` with the proper time of the dust corrected at second
    order, `τ = T + n²/(2(τ_c − T))` (`interiorTime`); `interiorMetric` is the pullback of
    `dustInterior` (`interiorCoeff`). Without the correction the shear of the slices `τ = const`
    makes `∂_n g_{Tn}` jump by `−1/(τ_c − T)`, a co-ordinate artefact;
  - `coefficient_eq_on_boundary`, `coefficient_normal_on_boundary`: on `n = 0` both metrics are
    `−dT² + dn² + r_b² dΩ²` (`boundaryCoeff`); `fderiv_interiorMetric`, `fderiv_exteriorMetric`,
    `fderiv_eq_on_boundary`: their normal derivatives agree (`normalDeriv`), using
    `−ṙ_b = √(2M/r_b)` (`sqrt_two_mul_div_boundaryRadius`).
* `junction_adapted`: in the adapted chart the induced metrics and the second fundamental forms
  of the boundary are those of the comoving shells `R = τ_c` and `χ = χ_b` of
  `junction_oppenheimerSnyder` (`exteriorMap_boundary`, `interiorMap_boundary`), and the two
  second fundamental forms agree.
* **`contDiffOn_glue`**: the glued metric is `C¹` on the collar; **`contDiffOn_glue_iff_junction`**:
  since the components `g_{nμ}` have equal normal derivatives, it is `C¹` exactly because the
  second fundamental forms agree (`contDiffOn_glue_iff_secondFundamental`).
* **`isWeakEinstein_oppenheimerSnyder`**: the glued metric solves the weak Einstein equations on
  the collar with the dust `chartDust` (`T_{ik} = ρ(τ) ∂_iτ ∂_kτ`) inside and vacuum outside
  (`isWeakEinstein_glue`).
* **A genuine surface layer**: `shellMetric R₀ s`, `ds² = −dT² + dn² + (R₀ + s n)² dΩ²`, glued to
  the flat metric `shellMetric R₀ 1` along the sphere `n = 0`, has the surface density
  `[K_TT] − h_TT [K] = 2(s − 1)/R₀` (`shell_surface_density`), and for `s ≠ 1` its weak Einstein
  tensor differs from the integrals of the two smooth Einstein tensors on a test density
  (`exists_surface_layer`).

The glued metric is `C^{1,1}` but not `C²`: the density jumps across the boundary. The chart covers
the boundary for all `T < τ_c` and the angles `0 < θ < π`.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology Real

namespace ProjectAinos.GeneralRelativity.CollapseJunction

open SmoothGeometry CoordinateMetric Collapse

local notation "E" => MinkowskiModel 3

variable {M τc χb κ : ℝ}

/-! ### The Einstein equations in the two comoving charts -/

/-- The dust of density `ρ(τ) = 4/(3κ(τ_c − τ)²)` at rest in the comoving chart:
`T_{ik} = ρ δ_i^τ δ_k^τ`. -/
def comovingDust (κ τc : ℝ) (x : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i k => dustDensity κ τc (x 0) * (if i = 0 then 1 else 0) * (if k = 0 then 1 else 0)

/-- The spherical co-ordinates are smooth. -/
theorem contDiff_toCartesian : ContDiff ℝ ∞ toCartesian := by
  refine contDiff_pi.2 fun i => ?_
  have h1 : ContDiff ℝ ∞ fun x : E => x 1 := contDiff_apply ℝ (fun _ => ℝ) 1
  have hs2 : ContDiff ℝ ∞ fun x : E => Real.sin (x 2) :=
    Real.contDiff_sin.comp (contDiff_apply ℝ (fun _ => ℝ) 2)
  have hc2 : ContDiff ℝ ∞ fun x : E => Real.cos (x 2) :=
    Real.contDiff_cos.comp (contDiff_apply ℝ (fun _ => ℝ) 2)
  have hs3 : ContDiff ℝ ∞ fun x : E => Real.sin (x 3) :=
    Real.contDiff_sin.comp (contDiff_apply ℝ (fun _ => ℝ) 3)
  have hc3 : ContDiff ℝ ∞ fun x : E => Real.cos (x 3) :=
    Real.contDiff_cos.comp (contDiff_apply ℝ (fun _ => ℝ) 3)
  fin_cases i
  · exact contDiff_apply ℝ (fun _ => ℝ) 0
  · exact (h1.mul hs2).mul hc3
  · exact (h1.mul hs2).mul hs3
  · exact h1.mul hc2

/-- **The flat dust ball solves the Einstein equations in comoving co-ordinates**: the pullback of
`isEinstein_dustData` by the spherical co-ordinates `toCartesian`. -/
theorem isEinstein_dustInterior (hτc : 0 < τc) (hκ : κ ≠ 0) :
    (dustInterior hτc).metric.IsEinstein κ 0 (comovingDust κ τc) := by
  have h := (isEinstein_dustData hτc hκ).pullback (FLRW.metric (dustData hτc))
    (dustInterior hτc).metric (F := toCartesian) (contDiff_toCartesian.contDiffOn)
    (fun x hx => toCartesian_mem hτc hx) (fun x _ v w => by
      rw [(hasFDerivAt_toCartesian x).fderiv, form_toCartesian])
  intro x hx i k
  rw [h x hx i k]
  congr 1
  simp only [pullbackTensor, FLRW.perfectFluidStress, FLRW.fluidCovector, Matrix.of_apply,
    (hasFDerivAt_toCartesian x).fderiv, toCartesianDeriv_apply, comovingDust]
  simp [Fin.sum_univ_four, dustData, toCartesian, Pi.single_apply]
  by_cases hk : k = 0 <;> by_cases hi : i = 0 <;> simp [hk, hi, eq_comm]


/-- The radius of the co-ordinates of Lemaître of `Tolman` is the radius of `Collapse`. -/
theorem tolman_lemaitreRadius (M : ℝ) (x : E) :
    Tolman.lemaitreRadius (2 * M) (x 0) (x 1) = lemaitreRadius M x := by
  simp only [Tolman.lemaitreRadius, Tolman.parabolicRadius, Collapse.lemaitreRadius, id]
  congr 1
  ring

/-- **The Lemaître chart of `Collapse` is a vacuum solution**: it is the metric of the parabolic
data `Tolman.ParabolicData.lemaitre` (`ParabolicData.isEinstein_lemaitre`). -/
theorem isEinstein_lemaitre (hM : 0 < M) (hκ : κ ≠ 0) :
    (lemaitre hM).metric.IsEinstein κ 0 0 := by
  have hrg : 0 < 2 * M := by positivity
  set P := Tolman.ParabolicData.lemaitre (2 * M) hrg
  have hm : MapsTo (id : E → E) lemaitreDomain (Tolman.domain P.toData) := fun x hx =>
    ⟨⟨mem_univ _, hx.1⟩, hx.2.1, hx.2.2⟩
  have h := (Tolman.ParabolicData.isEinstein_lemaitre (2 * M) hrg hκ).pullback
    (Tolman.metric P.toData) (lemaitre hM).metric (F := id) contDiffOn_id hm (fun x hx v w => by
      rw [fderiv_id, Tolman.lemaitre_eq P (rg := 2 * M) (hm hx) rfl
        (by simp [P, Tolman.ParabolicData.lemaitre]) rfl
        (by simp [P, Tolman.ParabolicData.lemaitre]), Tolman.lemaitreForm,
        diagonalForm_apply, ComovingData.metric_form_apply]
      simp only [ContinuousLinearMap.id_apply, id, EddingtonFinkelstein.sum_four,
        tolman_lemaitreRadius]
      simp [lemaitre]
      ring)
  intro x hx i k
  rw [h x hx i k]
  simp [pullbackTensor, Tolman.dustStress]


/-! ### The adapted chart of the junction -/

/-- The radius `r_b(T) = a(T) χ_b` of the boundary of the ball at the proper time `T`. -/
def boundaryRadius (τc χb T : ℝ) : ℝ := dustScale τc T * χb

/-- The rate `ṙ_b = −(2/3) r_b/(τ_c − T)` of the boundary. -/
def boundaryRate (τc χb T : ℝ) : ℝ := -(2 / 3) * boundaryRadius τc χb T / (τc - T)

theorem boundaryRadius_pos (hτc : 0 < τc) (hχ : 0 < χb) {T : ℝ} (hT : T < τc) :
    0 < boundaryRadius τc χb T :=
  mul_pos (dustScale_pos hτc hT) hχ

theorem hasDerivAt_boundaryRadius (hτc : 0 < τc) {T : ℝ} (hT : T < τc) :
    HasDerivAt (boundaryRadius τc χb) (boundaryRate τc χb T) T := by
  refine ((hasDerivAt_dustScale hτc hT).mul_const χb).congr_deriv ?_
  simp only [boundaryRate, boundaryRadius]
  ring

theorem contDiffOn_boundaryRadius (hτc : 0 < τc) :
    ContDiffOn ℝ ∞ (boundaryRadius τc χb) (Iio τc) :=
  (contDiffOn_dustScale hτc).mul contDiffOn_const

/-- With the mass relation `9 M τ_c² = 2 χ_b³`, the speed of the boundary is the speed
`√(2M/r)` of fall from rest at infinity: `−ṙ_b = √(2M/r_b)`. -/
theorem sqrt_two_mul_div_boundaryRadius (hM : 0 < M) (hτc : 0 < τc) (hχ : 0 < χb)
    (hmass : 9 * M * τc ^ 2 = 2 * χb ^ 3) {T : ℝ} (hT : T < τc) :
    Real.sqrt (2 * M / boundaryRadius τc χb T) = -boundaryRate τc χb T := by
  have hr := dustScale_mul_eq_lemaitreRadius hM hτc hχ hmass (θ := 0) (φ := 0) hT
  have hx : (![T, τc, 0, 0] : E) 0 < (![T, τc, 0, 0] : E) 1 := hT
  rw [boundaryRadius, ← hr, sqrt_two_mul_div_lemaitreRadius hM hx, boundaryRate, boundaryRadius,
    ← hr]
  change 2 / 3 * lemaitreRadius M ![T, τc, 0, 0] / (τc - T) = _
  ring

/-- The time `τ = T + n²/(2(τ_c − T))` of the interior chart, a correction of second order in the
distance `n` from the boundary. -/
def interiorTime (τc : ℝ) (x : E) : ℝ := x 0 + x 1 ^ 2 / (2 * (τc - x 0))

/-- **The interior chart** `(T, n, θ, φ) ↦ (τ, χ, θ, φ)` with `τ = T + n²/(2(τ_c − T))` and
`χ = χ_b + n/a(τ)`: `n` is the proper distance from the boundary along the slice `τ = const`. -/
def interiorMap (τc χb : ℝ) (x : E) : E :=
  ![interiorTime τc x, χb + x 1 / dustScale τc (interiorTime τc x), x 2, x 3]

/-- **The exterior chart** `(T, n, θ, φ) ↦ (τ, R, θ, φ)` of the Lemaître co-ordinates with
`τ = T`, `r = n + r_b(T)` and `R − τ = (2/3) r √(r/2M)`: the chart of Painlevé and Gullstrand,
`ds² = −dτ² + (dr + √(2M/r) dτ)² + r² dΩ²`, shifted by the boundary radius. -/
def exteriorMap (M τc χb : ℝ) (x : E) : E :=
  ![x 0, x 0 + 2 / 3 * (x 1 + boundaryRadius τc χb (x 0)) *
    Real.sqrt ((x 1 + boundaryRadius τc χb (x 0)) / (2 * M)), x 2, x 3]

theorem continuous_dustScale (τc : ℝ) : Continuous (dustScale τc) :=
  (Real.continuous_rpow_const (by norm_num)).comp
    ((continuous_const.sub continuous_id).div_const τc)

theorem continuous_boundaryRadius (τc χb : ℝ) : Continuous (boundaryRadius τc χb) :=
  (continuous_dustScale τc).mul continuous_const

/-- An open set where a function continuous on an open set is positive. -/
theorem isOpen_pos {O : Set E} (hO : IsOpen O) {f : E → ℝ} (hf : ContinuousOn f O) :
    IsOpen (O ∩ f ⁻¹' Ioi 0) :=
  hf.isOpen_inter_preimage hO isOpen_Ioi

/-- The open set `0 < θ < π` of the chart. -/
theorem isOpen_angle : IsOpen {x : E | 0 < x 2 ∧ x 2 < π} :=
  (isOpen_lt (continuous_const (y := (0 : ℝ))) (continuous_apply 2)).inter
    (isOpen_lt (continuous_apply 2) (continuous_const (y := π)))

/-- The open set `T < τ_c` of the chart. -/
theorem isOpen_lt_crunch (τc : ℝ) : IsOpen {x : E | x 0 < τc} :=
  isOpen_lt (continuous_apply 0) continuous_const

theorem continuousOn_interiorTime (τc : ℝ) :
    ContinuousOn (interiorTime τc) {x : E | x 0 < τc} := by
  refine (continuous_apply 0).continuousOn.add ((((continuous_apply 1).pow 2).continuousOn).div
    (continuous_const.mul (continuous_const.sub (continuous_apply 0))).continuousOn
      fun x hx => ?_)
  have : 0 < τc - x 0 := sub_pos.mpr hx
  positivity

/-- The domain of the interior chart: `T < τ_c`, `τ < τ_c`, `χ > 0`, `0 < θ < π`. -/
def interiorDomain (hτc : 0 < τc) (χb : ℝ) : Opens E :=
  ⟨{x | x 0 < τc ∧ interiorTime τc x < τc ∧ 0 < χb + x 1 / dustScale τc (interiorTime τc x) ∧
      0 < x 2 ∧ x 2 < π}, by
    have hO1 := (continuousOn_interiorTime τc).isOpen_inter_preimage (isOpen_lt_crunch τc)
      (isOpen_Iio (a := τc))
    have hχ : ContinuousOn (fun x => χb + x 1 / dustScale τc (interiorTime τc x))
        ({x : E | x 0 < τc} ∩ interiorTime τc ⁻¹' Iio τc) :=
      continuousOn_const.add ((continuous_apply 1).continuousOn.div
        ((continuous_dustScale τc).comp_continuousOn
          ((continuousOn_interiorTime τc).mono inter_subset_left))
        fun x hx => (dustScale_pos hτc hx.2).ne')
    have h := (isOpen_pos hO1 hχ).inter isOpen_angle
    convert h using 1
    ext x
    simp [and_assoc]⟩

/-- The domain of the exterior chart: `T < τ_c`, `r = n + r_b(T) > 0`, `0 < θ < π`. -/
def exteriorDomain (τc χb : ℝ) : Opens E :=
  ⟨{x | x 0 < τc ∧ 0 < x 1 + boundaryRadius τc χb (x 0) ∧ 0 < x 2 ∧ x 2 < π},
    (isOpen_lt_crunch τc).inter ((isOpen_lt (continuous_const (y := (0 : ℝ)))
      ((continuous_apply 1).add ((continuous_boundaryRadius τc χb).comp
        (continuous_apply 0)))).inter isOpen_angle)⟩

/-- **The collar of the boundary**, where both charts are defined. -/
def collar (hτc : 0 < τc) (χb : ℝ) : Opens E := interiorDomain hτc χb ⊓ exteriorDomain τc χb

/-- The boundary `n = 0` of the collar is the whole surface `T < τ_c`, `0 < θ < π`. -/
theorem mem_collar_of_boundary (hτc : 0 < τc) (hχ : 0 < χb) {x : E} (hT : x 0 < τc)
    (hn : x 1 = 0) (hθ : 0 < x 2) (hθ' : x 2 < π) : x ∈ collar hτc χb := by
  have hτ : interiorTime τc x = x 0 := by simp [interiorTime, hn]
  refine ⟨⟨hT, by rw [hτ]; exact hT, by rw [hτ, hn]; simpa using hχ, hθ, hθ'⟩,
    ⟨hT, by rw [hn, zero_add]; exact boundaryRadius_pos hτc hχ hT, hθ, hθ'⟩⟩


/-! #### The derivatives of the charts -/

/-- `∂τ/∂T = 1 + n²/(2(τ_c − T)²)`. -/
def timeRateT (τc : ℝ) (x : E) : ℝ := 1 + x 1 ^ 2 / (2 * (τc - x 0) ^ 2)

/-- `∂τ/∂n = n/(τ_c − T)`. -/
def timeRateN (τc : ℝ) (x : E) : ℝ := x 1 / (τc - x 0)

/-- The Hubble rate `H = ȧ/a = −(2/3)/(τ_c − τ)` of the dust at the time `τ` of the chart. -/
def hubble (τc : ℝ) (x : E) : ℝ := -(2 / 3) / (τc - interiorTime τc x)

/-- The Jacobian of the interior chart. -/
def interiorDeriv (τc : ℝ) (x : E) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ![timeRateT τc x * v 0 + timeRateN τc x * v 1,
        (-(x 1 * hubble τc x * timeRateT τc x) * v 0 +
          (1 - x 1 * hubble τc x * timeRateN τc x) * v 1) / dustScale τc (interiorTime τc x),
        v 2, v 3]
      map_add' := fun v w => by
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := fun c v => by
        funext i
        fin_cases i <;> simp <;> ring }

theorem interiorDeriv_apply (τc : ℝ) (x v : E) :
    interiorDeriv τc x v = ![timeRateT τc x * v 0 + timeRateN τc x * v 1,
      (-(x 1 * hubble τc x * timeRateT τc x) * v 0 +
        (1 - x 1 * hubble τc x * timeRateN τc x) * v 1) / dustScale τc (interiorTime τc x),
      v 2, v 3] := rfl

theorem hasFDerivAt_interiorTime {x : E} (hx : x 0 < τc) :
    HasFDerivAt (interiorTime τc)
      (timeRateT τc x • (ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ) +
        timeRateN τc x • (ContinuousLinearMap.proj 1 : E →L[ℝ] ℝ)) x := by
  have hs : τc - x 0 ≠ 0 := (sub_pos.mpr hx).ne'
  have h0 : HasFDerivAt (fun y : E => y 0) (ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 0 x
  have h1 : HasFDerivAt (fun y : E => y 1) (ContinuousLinearMap.proj 1 : E →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 1 x
  have hq := SphericalAnsatz.hasFDerivAt_div (h1.pow 2) ((h0.const_sub τc).const_mul 2)
    (mul_ne_zero two_ne_zero hs)
  refine (h0.add hq).congr_fderiv ?_
  ext v
  simp [timeRateT, timeRateN]
  field_simp
  ring

theorem hasFDerivAt_interiorMap (hτc : 0 < τc) {x : E} (hx : x ∈ interiorDomain hτc χb) :
    HasFDerivAt (interiorMap τc χb) (interiorDeriv τc x) x := by
  obtain ⟨hx0, hτ, -, -, -⟩ := hx
  have hT := hasFDerivAt_interiorTime hx0
  have ha := (hasDerivAt_dustScale hτc hτ).comp_hasFDerivAt x hT
  have hapos := dustScale_pos hτc hτ
  have hs : τc - interiorTime τc x ≠ 0 := (sub_pos.mpr hτ).ne'
  have h1 : HasFDerivAt (fun y : E => y 1) (ContinuousLinearMap.proj 1 : E →L[ℝ] ℝ) x :=
    hasFDerivAt_apply 1 x
  have hq := SphericalAnsatz.hasFDerivAt_div h1 ha hapos.ne'
  refine hasFDerivAt_pi'' fun i => ?_
  fin_cases i
  · refine hT.congr_fderiv ?_
    ext v
    simp [interiorDeriv_apply]
  · refine (hq.const_add χb).congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      interiorDeriv_apply, hubble]
    simp
    field_simp
    ring
  · refine (hasFDerivAt_apply 2 x).congr_fderiv ?_
    ext v
    simp [interiorDeriv_apply]
  · refine (hasFDerivAt_apply 3 x).congr_fderiv ?_
    ext v
    simp [interiorDeriv_apply]


/-- The areal radius `r = n + r_b(T)` of the exterior chart. -/
def exteriorRadius (τc χb : ℝ) (x : E) : ℝ := x 1 + boundaryRadius τc χb (x 0)

/-- `√(r/2M) = ∂R/∂r`, the inverse of the speed of fall from rest at infinity. -/
def exteriorScale (M τc χb : ℝ) (x : E) : ℝ := Real.sqrt (exteriorRadius τc χb x / (2 * M))

/-- The Jacobian of the exterior chart. -/
def exteriorDeriv (M τc χb : ℝ) (x : E) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ![v 0, (1 + exteriorScale M τc χb x * boundaryRate τc χb (x 0)) * v 0 +
        exteriorScale M τc χb x * v 1, v 2, v 3]
      map_add' := fun v w => by
        funext i
        fin_cases i <;> simp
        ring
      map_smul' := fun c v => by
        funext i
        fin_cases i <;> simp
        ring }

theorem exteriorDeriv_apply (M τc χb : ℝ) (x v : E) :
    exteriorDeriv M τc χb x v = ![v 0, (1 + exteriorScale M τc χb x * boundaryRate τc χb (x 0)) *
      v 0 + exteriorScale M τc χb x * v 1, v 2, v 3] := rfl

theorem exteriorScale_pos (hM : 0 < M) {x : E} (hx : x ∈ exteriorDomain τc χb) :
    0 < exteriorScale M τc χb x :=
  Real.sqrt_pos.mpr (div_pos hx.2.1 (by positivity))

theorem exteriorScale_sq (hM : 0 < M) {x : E} (hx : x ∈ exteriorDomain τc χb) :
    exteriorScale M τc χb x ^ 2 = exteriorRadius τc χb x / (2 * M) :=
  Real.sq_sqrt (div_pos hx.2.1 (by positivity)).le

theorem hasFDerivAt_exteriorRadius (hτc : 0 < τc) {x : E} (hx : x 0 < τc) :
    HasFDerivAt (exteriorRadius τc χb)
      ((ContinuousLinearMap.proj 1 : E →L[ℝ] ℝ) +
        boundaryRate τc χb (x 0) • (ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ)) x :=
  (hasFDerivAt_apply 1 x).add (SchwarzschildExterior.hasFDerivAt_coord 0
    (hasDerivAt_boundaryRadius hτc hx))

theorem hasFDerivAt_exteriorMap (hM : 0 < M) (hτc : 0 < τc) {x : E}
    (hx : x ∈ exteriorDomain τc χb) :
    HasFDerivAt (exteriorMap M τc χb) (exteriorDeriv M τc χb x) x := by
  have hr := hasFDerivAt_exteriorRadius (χb := χb) hτc hx.1
  have hpos : 0 < exteriorRadius τc χb x / (2 * M) := div_pos hx.2.1 (by positivity)
  have hS : HasFDerivAt (exteriorScale M τc χb)
      ((1 / (2 * exteriorScale M τc χb x)) • ((2 * M)⁻¹ •
        ((ContinuousLinearMap.proj 1 : E →L[ℝ] ℝ) +
          boundaryRate τc χb (x 0) • (ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ)))) x := by
    have h := (hr.const_mul (2 * M)⁻¹).sqrt (by rw [← div_eq_inv_mul]; exact hpos.ne')
    convert h using 2
    · simp [exteriorScale, div_eq_inv_mul]
    · simp [exteriorScale, div_eq_inv_mul]
  have hSpos := exteriorScale_pos hM hx
  have hS2 := exteriorScale_sq hM hx
  have hR := (hasFDerivAt_apply 0 x).add ((hr.const_mul (2 / 3)).mul hS)
  refine hasFDerivAt_pi'' fun i => ?_
  fin_cases i
  · refine (hasFDerivAt_apply 0 x).congr_fderiv ?_
    ext v
    simp [exteriorDeriv_apply]
  · refine hR.congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      exteriorDeriv_apply]
    change _ = (1 + exteriorScale M τc χb x * boundaryRate τc χb (x 0)) * v 0 +
      exteriorScale M τc χb x * v 1
    have hre : exteriorRadius τc χb x = 2 * M * exteriorScale M τc χb x ^ 2 := by
      rw [hS2]
      field_simp
    simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [hre]
    have hS0 := hSpos.ne'
    field_simp
    ring
  · refine (hasFDerivAt_apply 2 x).congr_fderiv ?_
    ext v
    simp [exteriorDeriv_apply]
  · refine (hasFDerivAt_apply 3 x).congr_fderiv ?_
    ext v
    simp [exteriorDeriv_apply]


/-! #### The charts are smooth local diffeomorphisms -/

theorem contDiffOn_interiorTime (τc : ℝ) :
    ContDiffOn ℝ ∞ (interiorTime τc) {x : E | x 0 < τc} := by
  refine (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn.add
    ((((contDiff_apply ℝ (fun _ => ℝ) 1).pow 2).contDiffOn).div
      (contDiffOn_const.mul (contDiffOn_const.sub (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn))
      fun x hx => ?_)
  have : 0 < τc - x 0 := sub_pos.mpr hx
  positivity

theorem contDiffOn_interiorMap (hτc : 0 < τc) (χb : ℝ) :
    ContDiffOn ℝ ∞ (interiorMap τc χb) (interiorDomain hτc χb) := by
  have hT : ContDiffOn ℝ ∞ (interiorTime τc) (interiorDomain hτc χb) :=
    (contDiffOn_interiorTime τc).mono fun x hx => hx.1
  have ha : ContDiffOn ℝ ∞ (fun x => dustScale τc (interiorTime τc x)) (interiorDomain hτc χb) :=
    (contDiffOn_dustScale hτc).comp hT fun x hx => hx.2.1
  refine contDiffOn_pi.2 fun i => ?_
  fin_cases i
  · exact hT
  · exact contDiffOn_const.add ((contDiff_apply ℝ (fun _ => ℝ) 1).contDiffOn.div ha
      fun x hx => (dustScale_pos hτc hx.2.1).ne')
  · exact (contDiff_apply ℝ (fun _ => ℝ) 2).contDiffOn
  · exact (contDiff_apply ℝ (fun _ => ℝ) 3).contDiffOn

theorem contDiffOn_exteriorMap (hM : 0 < M) (hτc : 0 < τc) (χb : ℝ) :
    ContDiffOn ℝ ∞ (exteriorMap M τc χb) (exteriorDomain τc χb) := by
  have hr : ContDiffOn ℝ ∞ (exteriorRadius τc χb) (exteriorDomain τc χb) :=
    (contDiff_apply ℝ (fun _ => ℝ) 1).contDiffOn.add ((contDiffOn_boundaryRadius hτc).comp
      (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn fun x hx => hx.1)
  have hS : ContDiffOn ℝ ∞ (exteriorScale M τc χb) (exteriorDomain τc χb) :=
    (hr.div_const (2 * M)).sqrt fun x hx => (div_pos hx.2.1 (by positivity)).ne'
  refine contDiffOn_pi.2 fun i => ?_
  fin_cases i
  · exact (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn
  · exact (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn.add ((contDiffOn_const.mul hr).mul hS)
  · exact (contDiff_apply ℝ (fun _ => ℝ) 2).contDiffOn
  · exact (contDiff_apply ℝ (fun _ => ℝ) 3).contDiffOn

theorem mapsTo_interiorMap (hτc : 0 < τc) (χb : ℝ) :
    MapsTo (interiorMap τc χb) (interiorDomain hτc χb) (dustInterior hτc).domain :=
  fun _ hx => ⟨hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2⟩

theorem mapsTo_exteriorMap (hM : 0 < M) (χb : ℝ) :
    MapsTo (exteriorMap M τc χb) (exteriorDomain τc χb) (lemaitre hM).domain := by
  intro x hx
  have hS := exteriorScale_pos hM hx
  have hr := hx.2.1
  refine ⟨?_, hx.2.2.1, hx.2.2.2⟩
  change x 0 < x 0 + 2 / 3 * exteriorRadius τc χb x * exteriorScale M τc χb x
  have : 0 < 2 / 3 * exteriorRadius τc χb x * exteriorScale M τc χb x := by
    have : 0 < exteriorRadius τc χb x := hr
    positivity
  linarith

/-- An injective continuous linear endomorphism of the model is invertible. -/
theorem isInvertible_of_injective {L : E →L[ℝ] E} (h : Function.Injective L) :
    L.IsInvertible :=
  ⟨(L.toLinearMap.linearEquivOfInjective h rfl).toContinuousLinearEquiv, rfl⟩

theorem isInvertible_interiorDeriv (hτc : 0 < τc) {x : E} (hx : x ∈ interiorDomain hτc χb) :
    (interiorDeriv τc x).IsInvertible := by
  refine isInvertible_of_injective fun v w hvw => ?_
  have ha := (dustScale_pos hτc hx.2.1).ne'
  have hT : 0 < timeRateT τc x := by
    simp only [timeRateT]
    positivity
  have e0 := congrFun hvw 0
  have e1 := congrFun hvw 1
  have e2 := congrFun hvw 2
  have e3 := congrFun hvw 3
  simp only [interiorDeriv_apply] at e0 e1 e2 e3
  simp at e0 e1 e2 e3
  field_simp at e1
  have hp : timeRateT τc x * (v 0 - w 0) = 0 := by
    linear_combination (1 - x 1 * hubble τc x * timeRateN τc x) * e0 - timeRateN τc x * e1
  have hq : timeRateT τc x * (v 1 - w 1) = 0 := by
    linear_combination (x 1 * hubble τc x * timeRateT τc x) * e0 + timeRateT τc x * e1
  have hp' := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hT.ne')
  have hq' := sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left hT.ne')
  funext i
  fin_cases i
  · exact hp'
  · exact hq'
  · exact e2
  · exact e3

theorem isInvertible_exteriorDeriv (hM : 0 < M) {x : E} (hx : x ∈ exteriorDomain τc χb) :
    (exteriorDeriv M τc χb x).IsInvertible := by
  refine isInvertible_of_injective fun v w hvw => ?_
  have hS := (exteriorScale_pos hM hx).ne'
  have e0 := congrFun hvw 0
  have e1 := congrFun hvw 1
  have e2 := congrFun hvw 2
  have e3 := congrFun hvw 3
  simp only [exteriorDeriv_apply] at e0 e1 e2 e3
  simp at e0 e1 e2 e3
  rw [e0] at e1
  have h1 : exteriorScale M τc χb x * (v 1 - w 1) = 0 := by linear_combination e1
  have h1' := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hS)
  funext i
  fin_cases i
  · exact e0
  · exact h1'
  · exact e2
  · exact e3

/-- **The metric of the dust ball in the adapted chart**, the pullback of `dustInterior` by
`interiorMap`. -/
def interiorMetric (hτc : 0 < τc) (χb : ℝ) :
    CoordinateMetric .timeNegative 3 (interiorDomain hτc χb) :=
  (dustInterior hτc).metric.pullback (interiorMap τc χb) (contDiffOn_interiorMap hτc χb)
    (mapsTo_interiorMap hτc χb) fun x hx => by
      rw [(hasFDerivAt_interiorMap hτc hx).fderiv]
      exact isInvertible_interiorDeriv hτc hx

/-- **The Schwarzschild field outside the ball in the adapted chart**, the pullback of the
Lemaître chart by `exteriorMap`. -/
def exteriorMetric (hM : 0 < M) (hτc : 0 < τc) (χb : ℝ) :
    CoordinateMetric .timeNegative 3 (exteriorDomain τc χb) :=
  (lemaitre hM).metric.pullback (exteriorMap M τc χb) (contDiffOn_exteriorMap hM hτc χb)
    (mapsTo_exteriorMap hM χb) fun x hx => by
      rw [(hasFDerivAt_exteriorMap hM hτc hx).fderiv]
      exact isInvertible_exteriorDeriv hM hx


/-! #### The coefficients of the two metrics -/

/-- The coefficients of the interior metric:
`ds² = τ_T²(−1 + (nH)²) dT² + 2(−τ_Tτ_n − nHτ_T(1 − nHτ_n)) dT dn + (−τ_n² + (1 − nHτ_n)²) dn²
  + (a(τ)χ_b + n)² dΩ²`. -/
def interiorCoeff (τc χb : ℝ) (x : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![-timeRateT τc x ^ 2 + (x 1 * hubble τc x * timeRateT τc x) ^ 2,
      -(timeRateT τc x * timeRateN τc x) -
        x 1 * hubble τc x * timeRateT τc x * (1 - x 1 * hubble τc x * timeRateN τc x), 0, 0],
    ![-(timeRateT τc x * timeRateN τc x) -
        x 1 * hubble τc x * timeRateT τc x * (1 - x 1 * hubble τc x * timeRateN τc x),
      -timeRateN τc x ^ 2 + (1 - x 1 * hubble τc x * timeRateN τc x) ^ 2, 0, 0],
    ![0, 0, (dustScale τc (interiorTime τc x) * χb + x 1) ^ 2, 0],
    ![0, 0, 0, (dustScale τc (interiorTime τc x) * χb + x 1) ^ 2 * Real.sin (x 2) ^ 2]]

theorem coefficient_interiorMetric (hτc : 0 < τc) {x : E} (hx : x ∈ interiorDomain hτc χb) :
    (interiorMetric hτc χb).coefficient x = interiorCoeff τc χb x := by
  have ha := (dustScale_pos hτc hx.2.1).ne'
  ext i j
  change (interiorMetric hτc χb).form x (Pi.single i 1) (Pi.single j 1) = _
  rw [interiorMetric, pullback_form_apply, (hasFDerivAt_interiorMap hτc hx).fderiv,
    ComovingData.metric_form_apply, interiorDeriv_apply, interiorDeriv_apply]
  simp only [dustInterior, interiorMap, interiorCoeff]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> first | ring1 | simp


/-- The Lemaître radius at the image of the exterior chart is `r = n + r_b(T)`. -/
theorem lemaitreRadius_exteriorMap (hM : 0 < M) {x : E} (hx : x ∈ exteriorDomain τc χb) :
    lemaitreRadius M (exteriorMap M τc χb x) = exteriorRadius τc χb x := by
  have hy := (mapsTo_exteriorMap (τc := τc) hM χb hx).1
  have hr : 0 < exteriorRadius τc χb x := hx.2.1
  have hS2 := exteriorScale_sq hM hx
  have h3 := lemaitreRadius_cube hM hy
  refine (pow_left_inj₀ (lemaitreRadius_pos hM hy).le hr.le three_ne_zero).mp ?_
  rw [h3]
  change 9 / 2 * M * (x 0 + 2 / 3 * exteriorRadius τc χb x * exteriorScale M τc χb x - x 0) ^ 2 =
    exteriorRadius τc χb x ^ 3
  have : (x 0 + 2 / 3 * exteriorRadius τc χb x * exteriorScale M τc χb x - x 0) ^ 2 =
      4 / 9 * exteriorRadius τc χb x ^ 2 * exteriorScale M τc χb x ^ 2 := by ring
  rw [this, hS2]
  field_simp
  ring

/-- The coefficients of the exterior metric, with `V = 1/√(r/2M) = √(2M/r)`:
`ds² = (−1 + (V + ṙ_b)²) dT² + 2(V + ṙ_b) dT dn + dn² + r² dΩ²`. -/
def exteriorCoeff (M τc χb : ℝ) (x : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![-1 + ((exteriorScale M τc χb x)⁻¹ + boundaryRate τc χb (x 0)) ^ 2,
      (exteriorScale M τc χb x)⁻¹ + boundaryRate τc χb (x 0), 0, 0],
    ![(exteriorScale M τc χb x)⁻¹ + boundaryRate τc χb (x 0), 1, 0, 0],
    ![0, 0, exteriorRadius τc χb x ^ 2, 0],
    ![0, 0, 0, exteriorRadius τc χb x ^ 2 * Real.sin (x 2) ^ 2]]

theorem coefficient_exteriorMetric (hM : 0 < M) (hτc : 0 < τc) {x : E}
    (hx : x ∈ exteriorDomain τc χb) :
    (exteriorMetric hM hτc χb).coefficient x = exteriorCoeff M τc χb x := by
  have hS := (exteriorScale_pos hM hx).ne'
  have hre : exteriorRadius τc χb x = 2 * M * exteriorScale M τc χb x ^ 2 := by
    rw [exteriorScale_sq hM hx]
    field_simp
  have hL := lemaitreRadius_exteriorMap hM hx
  ext i j
  change (exteriorMetric hM hτc χb).form x (Pi.single i 1) (Pi.single j 1) = _
  rw [exteriorMetric, pullback_form_apply, (hasFDerivAt_exteriorMap hM hτc hx).fderiv,
    ComovingData.metric_form_apply, exteriorDeriv_apply, exteriorDeriv_apply]
  simp only [lemaitre, hL, exteriorCoeff]
  rw [hre]
  fin_cases i <;> fin_cases j <;> simp [exteriorMap] <;> field_simp


/-! #### The normal derivatives on the boundary -/

/-- The normal derivative `∂_n g_{pq}` of a coordinate metric at `z` is the derivative along the
line `s ↦ z + (s − z¹) e₁` of a closed form of its coefficients. -/
theorem fderiv_normal_eq {U : Opens E} (g : CoordinateMetric .timeNegative 3 U)
    {C : E → Matrix (Fin 4) (Fin 4) ℝ} (hC : ∀ x ∈ U, g.coefficient x = C x) {z : E}
    (hz : z ∈ U) {p q : Fin 4} {c : ℝ}
    (hline : HasDerivAt (fun s => C (Function.update z 1 s) p q) c (z 1)) :
    fderiv ℝ (fun y => g.coefficient y p q) z (Pi.single 1 1) = c := by
  have hd : DifferentiableAt ℝ (fun y => g.coefficient y p q) z :=
    ((g.coefficient_contDiffOn p q).contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt
      (by simp)
  rw [fderiv_single_eq_deriv_update hd]
  have hcont : Continuous fun s : ℝ => Function.update z 1 s := by fun_prop
  have hev : (fun s => g.coefficient (Function.update z 1 s) p q) =ᶠ[𝓝 (z 1)]
      fun s => C (Function.update z 1 s) p q := by
    have hmem : (Function.update z 1 (z 1)) ∈ U := by rwa [Function.update_eq_self]
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (U.isOpen.mem_nhds hmem)] with s hs
    rw [hC _ hs]
  rw [hev.deriv_eq, hline.deriv]

/-- The normal derivatives `∂_n g_{pq}` on the boundary, the same on both sides:
`∂_n g_{Tn} = −1/(3(τ_c − T))`, `∂_n g_{θθ} = 2r_b`, `∂_n g_{φφ} = 2r_b sin²θ`, the others zero. -/
def normalDeriv (τc χb T θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![0, -(1 / 3) / (τc - T), 0, 0], ![-(1 / 3) / (τc - T), 0, 0, 0],
    ![0, 0, 2 * boundaryRadius τc χb T, 0],
    ![0, 0, 0, 2 * boundaryRadius τc χb T * Real.sin θ ^ 2]]

theorem hasDerivAt_sq_div (c : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2 / c) 0 0 := by
  simpa using (hasDerivAt_pow 2 (0 : ℝ)).div_const c

/-- **The normal derivatives of the interior metric** on the boundary. -/
theorem fderiv_interiorMetric (hτc : 0 < τc) {z : E} (hz : z ∈ interiorDomain hτc χb)
    (hz1 : z 1 = 0) (p q : Fin 4) :
    fderiv ℝ (fun y => (interiorMetric hτc χb).coefficient y p q) z (Pi.single 1 1) =
      normalDeriv τc χb (z 0) (z 2) p q := by
  set T := z 0 with hT
  have hu : 0 < τc - T := sub_pos.mpr hz.1
  have hu' := hu.ne'
  -- the functions along the line
  have eT (s : ℝ) : timeRateT τc (Function.update z 1 s) = 1 + s ^ 2 / (2 * (τc - T) ^ 2) := by
    simp [timeRateT, hT]
  have eN (s : ℝ) : timeRateN τc (Function.update z 1 s) = s / (τc - T) := by
    simp [timeRateN, hT]
  have eτ (s : ℝ) : interiorTime τc (Function.update z 1 s) = T + s ^ 2 / (2 * (τc - T)) := by
    simp [interiorTime, hT]
  have eH (s : ℝ) : hubble τc (Function.update z 1 s) =
      -(2 / 3) / (τc - (T + s ^ 2 / (2 * (τc - T)))) := by
    simp [hubble, eτ]
  have hTT : HasDerivAt (fun s : ℝ => 1 + s ^ 2 / (2 * (τc - T) ^ 2)) 0 0 := by
    simpa using (hasDerivAt_sq_div (2 * (τc - T) ^ 2)).const_add 1
  have hTN : HasDerivAt (fun s : ℝ => s / (τc - T)) (1 / (τc - T)) 0 :=
    (hasDerivAt_id 0).div_const _
  have hτ : HasDerivAt (fun s : ℝ => T + s ^ 2 / (2 * (τc - T))) 0 0 := by
    simpa using (hasDerivAt_sq_div (2 * (τc - T))).const_add T
  have hH : HasDerivAt (fun s : ℝ => -(2 / 3) / (τc - (T + s ^ 2 / (2 * (τc - T))))) 0 0 := by
    have h := ((hτ.const_sub τc).inv (by simpa using hu')).const_mul (-(2 / 3))
    have e : (fun s : ℝ => -(2 / 3) / (τc - (T + s ^ 2 / (2 * (τc - T))))) =
        fun s => -(2 / 3) * (τc - (T + s ^ 2 / (2 * (τc - T))))⁻¹ := by
      funext s
      rw [div_eq_mul_inv]
    rw [e]
    convert h using 1
    simp
  have ha : HasDerivAt (fun s : ℝ => dustScale τc (T + s ^ 2 / (2 * (τc - T)))) 0 0 := by
    have h := (hasDerivAt_dustScale hτc (by simpa using hz.1)).comp (0 : ℝ) hτ
    exact h.congr_deriv (by simp)
  -- the coefficients along the line
  set H : ℝ → ℝ := fun s => -(2 / 3) / (τc - (T + s ^ 2 / (2 * (τc - T)))) with hHdef
  set TT : ℝ → ℝ := fun s => 1 + s ^ 2 / (2 * (τc - T) ^ 2) with hTTdef
  set TN : ℝ → ℝ := fun s => s / (τc - T) with hTNdef
  set A : ℝ → ℝ := fun s => dustScale τc (T + s ^ 2 / (2 * (τc - T))) with hAdef
  have hline (s : ℝ) : interiorCoeff τc χb (Function.update z 1 s) = Matrix.of
      ![![-TT s ^ 2 + (s * H s * TT s) ^ 2,
          -(TT s * TN s) - s * H s * TT s * (1 - s * H s * TN s), 0, 0],
        ![-(TT s * TN s) - s * H s * TT s * (1 - s * H s * TN s),
          -TN s ^ 2 + (1 - s * H s * TN s) ^ 2, 0, 0],
        ![0, 0, (A s * χb + s) ^ 2, 0],
        ![0, 0, 0, (A s * χb + s) ^ 2 * Real.sin (z 2) ^ 2]] := by
    simp only [interiorCoeff, eT, eN, eH, eτ, Function.update_self]
    rw [Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1)]
  have h00 : HasDerivAt (fun s => -TT s ^ 2 + (s * H s * TT s) ^ 2) 0 0 := by
    have h := (hTT.pow 2).fun_neg.fun_add ((((hasDerivAt_id' (0 : ℝ)).fun_mul hH).fun_mul
      hTT).pow 2)
    convert h using 1
    simp [hTTdef, hHdef]
  have h01 : HasDerivAt (fun s => -(TT s * TN s) - s * H s * TT s * (1 - s * H s * TN s))
      (-(1 / 3) / (τc - T)) 0 := by
    have h := ((hTT.fun_mul hTN).fun_neg).fun_sub ((((hasDerivAt_id' (0 : ℝ)).fun_mul hH).fun_mul
      hTT).fun_mul ((((hasDerivAt_id' (0 : ℝ)).fun_mul hH).fun_mul hTN).const_sub 1))
    convert h using 1
    simp [hTTdef, hHdef, hTNdef]
    field_simp
    ring
  have h11 : HasDerivAt (fun s => -TN s ^ 2 + (1 - s * H s * TN s) ^ 2) 0 0 := by
    have h := (hTN.pow 2).fun_neg.fun_add (((((hasDerivAt_id' (0 : ℝ)).fun_mul hH).fun_mul
      hTN).const_sub 1).pow 2)
    convert h using 1
    simp [hTNdef]
  have h22 : HasDerivAt (fun s => (A s * χb + s) ^ 2) (2 * boundaryRadius τc χb T) 0 := by
    have h := ((ha.mul_const χb).fun_add (hasDerivAt_id' (0 : ℝ))).pow 2
    convert h using 1
    simp [hAdef, boundaryRadius]
  have h33 : HasDerivAt (fun s => (A s * χb + s) ^ 2 * Real.sin (z 2) ^ 2)
      (2 * boundaryRadius τc χb T * Real.sin (z 2) ^ 2) 0 :=
    h22.mul_const _
  rw [fderiv_normal_eq (interiorMetric hτc χb) (fun x hx => coefficient_interiorMetric hτc hx) hz
    (c := normalDeriv τc χb T (z 2) p q)]
  simp only [hline, hz1]
  fin_cases p <;> fin_cases q <;> simp [normalDeriv, hasDerivAt_const] <;>
    first | exact h00 | exact h11 | exact h22 | exact h33 | (convert h01 using 1; ring)


/-- On the boundary `√(2M/r_b) = 1/√(r_b/2M) = −ṙ_b`. -/
theorem inv_exteriorScale_boundary (hM : 0 < M) (hτc : 0 < τc) (hχ : 0 < χb)
    (hmass : 9 * M * τc ^ 2 = 2 * χb ^ 3) {T : ℝ} (hT : T < τc) :
    (Real.sqrt (boundaryRadius τc χb T / (2 * M)))⁻¹ = -boundaryRate τc χb T := by
  rw [← Real.sqrt_inv, inv_div, sqrt_two_mul_div_boundaryRadius hM hτc hχ hmass hT]

/-- **The normal derivatives of the exterior metric** on the boundary are those of the interior
metric (`fderiv_interiorMetric`), with the mass relation `9 M τ_c² = 2 χ_b³`. -/
theorem fderiv_exteriorMetric (hM : 0 < M) (hτc : 0 < τc) (hχ : 0 < χb)
    (hmass : 9 * M * τc ^ 2 = 2 * χb ^ 3) {z : E} (hz : z ∈ exteriorDomain τc χb)
    (hz1 : z 1 = 0) (p q : Fin 4) :
    fderiv ℝ (fun y => (exteriorMetric hM hτc χb).coefficient y p q) z (Pi.single 1 1) =
      normalDeriv τc χb (z 0) (z 2) p q := by
  set T := z 0 with hT
  have hT' : T < τc := hz.1
  have hu : 0 < τc - T := sub_pos.mpr hT'
  have hrb := boundaryRadius_pos hτc hχ hT'
  set rb := boundaryRadius τc χb T with hrbdef
  set rd := boundaryRate τc χb T with hrddef
  have hS0 : 0 < rb / (2 * M) := by positivity
  set S : ℝ → ℝ := fun s => Real.sqrt ((s + rb) / (2 * M)) with hSdef
  have eR (s : ℝ) : exteriorRadius τc χb (Function.update z 1 s) = s + rb := by
    simp [exteriorRadius, hrbdef, hT]
  have eS (s : ℝ) : exteriorScale M τc χb (Function.update z 1 s) = S s := by
    simp [exteriorScale, eR, hSdef]
  have hline (s : ℝ) : exteriorCoeff M τc χb (Function.update z 1 s) = Matrix.of
      ![![-1 + ((S s)⁻¹ + rd) ^ 2, (S s)⁻¹ + rd, 0, 0], ![(S s)⁻¹ + rd, 1, 0, 0],
        ![0, 0, (s + rb) ^ 2, 0], ![0, 0, 0, (s + rb) ^ 2 * Real.sin (z 2) ^ 2]] := by
    simp only [exteriorCoeff, eS, eR]
    rw [Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1),
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1)]
  set σ := Real.sqrt (rb / (2 * M)) with hσdef
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hS0
  have hSd : HasDerivAt S ((1 / (2 * M)) / (2 * σ)) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).add_const rb).div_const (2 * M)).sqrt
      (by simpa using hS0.ne')
    convert h using 1
    simp [hσdef]
  have hS0' : S 0 = σ := by simp [hSdef, hσdef]
  have hSinv : HasDerivAt (fun s => (S s)⁻¹) (-((1 / (2 * M)) / (2 * σ)) / S 0 ^ 2) 0 :=
    hSd.inv (by rw [hS0']; exact hσpos.ne')
  have hval : (S 0)⁻¹ = -rd := by
    rw [hS0']
    exact inv_exteriorScale_boundary hM hτc hχ hmass hT'
  have hsq : σ ^ 2 = rb / (2 * M) := Real.sq_sqrt hS0.le
  have h00 : HasDerivAt (fun s => -1 + ((S s)⁻¹ + rd) ^ 2) 0 0 := by
    have h : HasDerivAt (fun s => -1 + ((S s)⁻¹ + rd) ^ 2)
        ((2 : ℕ) * ((S 0)⁻¹ + rd) ^ (2 - 1) * (-((1 / (2 * M)) / (2 * σ)) / S 0 ^ 2)) 0 :=
      ((hSinv.add_const rd).pow 2).const_add (-1)
    refine h.congr_deriv ?_
    rw [hval]
    simp
  have h01 : HasDerivAt (fun s => (S s)⁻¹ + rd) (-(1 / 3) / (τc - T)) 0 := by
    refine (hSinv.add_const rd).congr_deriv ?_
    rw [hS0']
    have hinv : σ⁻¹ = 2 / 3 * rb / (τc - T) := by
      rw [← hS0', hval, hrddef, boundaryRate, ← hrbdef]
      ring
    have hσ1 : σ * (2 * rb) = 3 * (τc - T) := by
      have := congrArg (fun t => t * σ * (3 * (τc - T))) hinv
      field_simp at this
      linarith
    have hσ2 : σ ^ 2 * (2 * M) = rb := by
      rw [hsq]
      field_simp
    have hM0 : M ≠ 0 := hM.ne'
    have hu0 : τc - T ≠ 0 := hu.ne'
    have hσ0 : σ ≠ 0 := hσpos.ne'
    field_simp
    linear_combination (2 * σ) * hσ2 + hσ1
  have h22 : HasDerivAt (fun s => (s + rb) ^ 2) (2 * rb) 0 := by
    have h := ((hasDerivAt_id' (0 : ℝ)).add_const rb).pow 2
    convert h using 1
    simp
  have h33 : HasDerivAt (fun s => (s + rb) ^ 2 * Real.sin (z 2) ^ 2)
      (2 * rb * Real.sin (z 2) ^ 2) 0 := h22.mul_const _
  rw [fderiv_normal_eq (exteriorMetric hM hτc χb)
    (fun x hx => coefficient_exteriorMetric hM hτc hx) hz (c := normalDeriv τc χb T (z 2) p q)]
  simp only [hline, hz1]
  fin_cases p <;> fin_cases q <;>
    simp only [normalDeriv, Matrix.of_apply] <;>
    first | exact h00 | exact h01 | exact h22 | exact h33 | exact hasDerivAt_const _ _


/-! ### The glued metric -/

/-- On the boundary both metrics are `−dT² + dn² + r_b² dΩ²`. -/
def boundaryCoeff (τc χb T θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, boundaryRadius τc χb T ^ 2, 0],
    ![0, 0, 0, boundaryRadius τc χb T ^ 2 * Real.sin θ ^ 2]]

theorem coefficient_interiorMetric_boundary (hτc : 0 < τc) {z : E}
    (hz : z ∈ interiorDomain hτc χb) (hz1 : z 1 = 0) :
    (interiorMetric hτc χb).coefficient z = boundaryCoeff τc χb (z 0) (z 2) := by
  rw [coefficient_interiorMetric hτc hz]
  have hτ : interiorTime τc z = z 0 := by simp [interiorTime, hz1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [interiorCoeff, boundaryCoeff, timeRateT, timeRateN, hz1, hτ, boundaryRadius]

theorem coefficient_exteriorMetric_boundary (hM : 0 < M) (hτc : 0 < τc) (hχ : 0 < χb)
    (hmass : 9 * M * τc ^ 2 = 2 * χb ^ 3) {z : E} (hz : z ∈ exteriorDomain τc χb)
    (hz1 : z 1 = 0) :
    (exteriorMetric hM hτc χb).coefficient z = boundaryCoeff τc χb (z 0) (z 2) := by
  rw [coefficient_exteriorMetric hM hτc hz]
  have hS : (exteriorScale M τc χb z)⁻¹ + boundaryRate τc χb (z 0) = 0 := by
    rw [exteriorScale, exteriorRadius, hz1, zero_add,
      inv_exteriorScale_boundary hM hτc hχ hmass hz.1]
    ring
  have hr : exteriorRadius τc χb z = boundaryRadius τc χb (z 0) := by
    simp [exteriorRadius, hz1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exteriorCoeff, boundaryCoeff, hS, hr]

theorem collar_le_interior (hτc : 0 < τc) : collar hτc χb ≤ interiorDomain hτc χb :=
  inf_le_left

theorem collar_le_exterior (hτc : 0 < τc) : collar hτc χb ≤ exteriorDomain τc χb :=
  inf_le_right

section Glued

variable (hM : 0 < M) (hτc : 0 < τc) (hχ : 0 < χb) (hmass : 9 * M * τc ^ 2 = 2 * χb ^ 3)
include hM hτc hχ hmass

/-- **The glued metric is continuous**: the two metrics agree on the boundary `n = 0`. -/
theorem coefficient_eq_on_boundary {y : E} (hy : y ∈ collar hτc χb) (hy1 : y 1 = 0) :
    (interiorMetric hτc χb).coefficient y = (exteriorMetric hM hτc χb).coefficient y := by
  rw [coefficient_interiorMetric_boundary hτc (collar_le_interior hτc hy) hy1,
    coefficient_exteriorMetric_boundary hM hτc hχ hmass (collar_le_exterior hτc hy) hy1]

/-- **`∂_n` is the unit normal of the boundary**: `g_{nμ} = δ_{nμ}` on `n = 0`. -/
theorem coefficient_normal_on_boundary {y : E} (hy : y ∈ collar hτc χb) (hy1 : y 1 = 0)
    (μ : Fin 4) :
    (exteriorMetric hM hτc χb).coefficient y 1 μ = if μ = 1 then 1 else 0 := by
  rw [coefficient_exteriorMetric_boundary hM hτc hχ hmass (collar_le_exterior hτc hy) hy1]
  fin_cases μ <;> simp [boundaryCoeff]

/-- **The normal derivatives agree on the boundary.** -/
theorem fderiv_eq_on_boundary {z : E} (hz : z ∈ collar hτc χb) (hz1 : z 1 = 0) (p q : Fin 4) :
    fderiv ℝ (fun x => (exteriorMetric hM hτc χb).coefficient x p q) z (Pi.single 1 1) =
      fderiv ℝ (fun x => (interiorMetric hτc χb).coefficient x p q) z (Pi.single 1 1) := by
  rw [fderiv_exteriorMetric hM hτc hχ hmass (collar_le_exterior hτc hz) hz1,
    fderiv_interiorMetric hτc (collar_le_interior hτc hz) hz1]

end Glued


/-! ### The junction conditions in the adapted chart -/

/-- The boundary point `(T, 0, θ, φ)` is the point `(T, χ_b, θ, φ)` of the dust ball. -/
theorem interiorMap_boundary {z : E} (hz1 : z 1 = 0) :
    interiorMap τc χb z = ![z 0, χb, z 2, z 3] := by
  have hτ : interiorTime τc z = z 0 := by simp [interiorTime, hz1]
  ext i
  fin_cases i <;> simp [interiorMap, hτ, hz1]

/-- The boundary point `(T, 0, θ, φ)` is the point `(T, τ_c, θ, φ)` of the Lemaître shell
`R = τ_c` (`junction_oppenheimerSnyder` with `R_b = τ_c`). -/
theorem exteriorMap_boundary (hM : 0 < M) (hτc : 0 < τc) (hχ : 0 < χb)
    (hmass : 9 * M * τc ^ 2 = 2 * χb ^ 3) {z : E} (hz : z ∈ exteriorDomain τc χb)
    (hz1 : z 1 = 0) : exteriorMap M τc χb z = ![z 0, τc, z 2, z 3] := by
  have hrb := boundaryRadius_pos hτc hχ hz.1
  have hu : 0 < τc - z 0 := sub_pos.mpr hz.1
  have hS : Real.sqrt (boundaryRadius τc χb (z 0) / (2 * M)) =
      3 / 2 * (τc - z 0) / boundaryRadius τc χb (z 0) := by
    have h := inv_exteriorScale_boundary hM hτc hχ hmass hz.1
    rw [boundaryRate] at h
    have h' := congrArg (·⁻¹) h
    simp only [inv_inv] at h'
    rw [h']
    field_simp
  ext i
  fin_cases i
  · simp [exteriorMap]
  · simp only [exteriorMap, hz1, zero_add, hS]
    simp
    field_simp
    ring
  · simp [exteriorMap]
  · simp [exteriorMap]

section Glued

variable (hM : 0 < M) (hτc : 0 < τc) (hχ : 0 < χb) (hmass : 9 * M * τc ^ 2 = 2 * χb ^ 3)
include hM hτc hχ hmass

/-- **The second fundamental forms in the adapted chart are those of the comoving shells**
(`junction_oppenheimerSnyder`): on the boundary, for the normal `∂_n`, `K = (½ ∂_n g_{ab})` of the
exterior is the second fundamental form of the Lemaître shell `R = τ_c`, that of the interior is
the one of the dust shell `χ = χ_b`, and the two agree: `K = diag(0, r_b, r_b sin²θ)`. The induced
metrics agree likewise. -/
theorem junction_adapted {z : E} (hz : z ∈ collar hτc χb) (hz1 : z 1 = 0) :
    (exteriorMetric hM hτc χb).secondFundamental 1 1 z =
        (lemaitre hM).metric.secondFundamental 1 1 ![z 0, τc, z 2, z 3] ∧
      (interiorMetric hτc χb).secondFundamental 1 1 z =
        (dustInterior hτc).metric.secondFundamental 1 1 ![z 0, χb, z 2, z 3] ∧
      (exteriorMetric hM hτc χb).secondFundamental 1 1 z =
        (interiorMetric hτc χb).secondFundamental 1 1 z ∧
      (exteriorMetric hM hτc χb).inducedMetric 1 z =
        (lemaitre hM).metric.inducedMetric 1 ![z 0, τc, z 2, z 3] ∧
      (interiorMetric hτc χb).inducedMetric 1 z =
        (dustInterior hτc).metric.inducedMetric 1 ![z 0, χb, z 2, z 3] := by
  have hzi := collar_le_interior hτc hz
  have hze := collar_le_exterior hτc hz
  have hT : z 0 < τc := hz.1.1
  have hθ : z 2 ∈ Ioo 0 π := ⟨hz.1.2.2.2.1, hz.1.2.2.2.2⟩
  have hL : (![z 0, τc, z 2, z 3] : E) ∈ lemaitreDomain := ⟨hT, hθ.1, hθ.2⟩
  have hD : (![z 0, χb, z 2, z 3] : E) ∈ dustDomain τc := ⟨hT, hχ, hθ.1, hθ.2⟩
  have hrL : lemaitreRadius M ![z 0, τc, z 2, z 3] = boundaryRadius τc χb (z 0) := by
    rw [dustScale_mul_eq_lemaitreRadius hM hτc hχ hmass hT, boundaryRadius]
  have hKe : (exteriorMetric hM hτc χb).secondFundamental 1 1 z =
      Matrix.diagonal ![0, boundaryRadius τc χb (z 0),
        boundaryRadius τc χb (z 0) * Real.sin (z 2) ^ 2] := by
    ext a b
    rw [secondFundamental_apply, coefficient_exteriorMetric_boundary hM hτc hχ hmass hze hz1,
      fderiv_exteriorMetric hM hτc hχ hmass hze hz1]
    fin_cases a <;> fin_cases b <;> simp [boundaryCoeff, normalDeriv, Fin.succAbove]
    ring
  have hKi : (interiorMetric hτc χb).secondFundamental 1 1 z =
      Matrix.diagonal ![0, boundaryRadius τc χb (z 0),
        boundaryRadius τc χb (z 0) * Real.sin (z 2) ^ 2] := by
    ext a b
    rw [secondFundamental_apply, coefficient_interiorMetric_boundary hτc hzi hz1,
      fderiv_interiorMetric hτc hzi hz1]
    fin_cases a <;> fin_cases b <;> simp [boundaryCoeff, normalDeriv, Fin.succAbove]
    ring
  have hKL : (lemaitre hM).metric.secondFundamental 1 1 ![z 0, τc, z 2, z 3] =
      Matrix.diagonal ![0, boundaryRadius τc χb (z 0),
        boundaryRadius τc χb (z 0) * Real.sin (z 2) ^ 2] := by
    rw [ComovingData.secondFundamental_eq _ hL, shellEnergy_lemaitre hM hL.1]
    simp [lemaitre, hrL]
  have hKD : (dustInterior hτc).metric.secondFundamental 1 1 ![z 0, χb, z 2, z 3] =
      Matrix.diagonal ![0, boundaryRadius τc χb (z 0),
        boundaryRadius τc χb (z 0) * Real.sin (z 2) ^ 2] := by
    rw [ComovingData.secondFundamental_eq _ hD, shellEnergy_dustInterior hτc hD]
    simp [dustInterior, boundaryRadius]
  refine ⟨hKe.trans hKL.symm, hKi.trans hKD.symm, hKe.trans hKi.symm, ?_, ?_⟩
  · ext a b
    rw [inducedMetric_apply, coefficient_exteriorMetric_boundary hM hτc hχ hmass hze hz1,
      ComovingData.inducedMetric_eq]
    fin_cases a <;> fin_cases b <;> simp [boundaryCoeff, Fin.succAbove, lemaitre, hrL]
  · ext a b
    rw [inducedMetric_apply, coefficient_interiorMetric_boundary hτc hzi hz1,
      ComovingData.inducedMetric_eq]
    fin_cases a <;> fin_cases b <;> simp [boundaryCoeff, Fin.succAbove, dustInterior,
      boundaryRadius]

end Glued


/-! ### The Einstein equations of the glued metric -/

/-- The dust of the ball in the adapted chart: `T_{ik} = ρ(τ) ∂_iτ ∂_kτ`, with `τ` the proper
time of the dust (`interiorTime`) and `ρ = 4/(3κ(τ_c − τ)²)`. -/
def chartDust (κ τc : ℝ) (x : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i k => dustDensity κ τc (interiorTime τc x) *
    (![timeRateT τc x, timeRateN τc x, 0, 0] : Fin 4 → ℝ) i *
    (![timeRateT τc x, timeRateN τc x, 0, 0] : Fin 4 → ℝ) k

theorem pullbackTensor_comovingDust (hτc : 0 < τc) {x : E} (hx : x ∈ interiorDomain hτc χb) :
    pullbackTensor (interiorMap τc χb) (comovingDust κ τc) x = chartDust κ τc x := by
  ext i k
  simp only [pullbackTensor, comovingDust, chartDust, Matrix.of_apply,
    (hasFDerivAt_interiorMap hτc hx).fderiv, interiorDeriv_apply]
  fin_cases i <;> fin_cases k <;> simp [interiorMap]

/-- The pulled-back Einstein equations of the interior chart. -/
theorem isEinstein_interiorMetric (hτc : 0 < τc) (hκ : κ ≠ 0) :
    (interiorMetric hτc χb).IsEinstein κ 0 (chartDust κ τc) := by
  have h := IsEinstein.pullback_metric (dustInterior hτc).metric (contDiffOn_interiorMap hτc χb)
    (mapsTo_interiorMap hτc χb) (fun x hx => by
      rw [(hasFDerivAt_interiorMap hτc hx).fderiv]
      exact isInvertible_interiorDeriv hτc hx) (isEinstein_dustInterior hτc hκ)
  intro x hx i k
  rw [← pullbackTensor_comovingDust hτc hx]
  exact h x hx i k

/-- The pulled-back vacuum equations of the exterior chart. -/
theorem isEinstein_exteriorMetric (hM : 0 < M) (hτc : 0 < τc) (hκ : κ ≠ 0) :
    (exteriorMetric hM hτc χb).IsEinstein κ 0 0 := by
  have h := IsEinstein.pullback_metric (lemaitre hM).metric (contDiffOn_exteriorMap hM hτc χb)
    (mapsTo_exteriorMap hM χb) (fun x hx => by
      rw [(hasFDerivAt_exteriorMap hM hτc hx).fderiv]
      exact isInvertible_exteriorDeriv hM hx) (isEinstein_lemaitre hM hκ)
  intro x hx i k
  exact (h x hx i k).trans (by simp [pullbackTensor])

theorem continuousOn_chartDust (hτc : 0 < τc) (κ : ℝ) (i k : Fin 4) :
    ContinuousOn (fun x => chartDust κ τc x i k) (interiorDomain hτc χb) := by
  have hT : ContinuousOn (interiorTime τc) (interiorDomain hτc χb) :=
    (continuousOn_interiorTime τc).mono fun x hx => hx.1
  have hρ : ContinuousOn (fun x => dustDensity κ τc (interiorTime τc x))
      (interiorDomain hτc χb) := by
    by_cases hκ : κ = 0
    · simp only [dustDensity, hκ, zero_mul, mul_zero, div_zero]
      exact continuousOn_const
    refine continuousOn_const.div ((continuousOn_const.mul
      ((continuousOn_const.sub hT).pow 2))) fun x hx => ?_
    have : 0 < τc - interiorTime τc x := sub_pos.mpr hx.2.1
    positivity
  have hs : ContinuousOn (fun x : E => τc - x 0) (interiorDomain hτc χb) :=
    continuousOn_const.sub (continuous_apply 0).continuousOn
  have hs0 (x : E) (hx : x ∈ interiorDomain hτc χb) : τc - x 0 ≠ 0 := (sub_pos.mpr hx.1).ne'
  have hTT : ContinuousOn (timeRateT τc) (interiorDomain hτc χb) :=
    continuousOn_const.add (((continuous_apply 1).pow 2).continuousOn.div
      (continuousOn_const.mul (hs.pow 2)) fun x hx => by
        have := hs0 x hx
        positivity)
  have hTN : ContinuousOn (timeRateN τc) (interiorDomain hτc χb) :=
    (continuous_apply 1).continuousOn.div hs hs0
  have hv (j : Fin 4) : ContinuousOn
      (fun x => (![timeRateT τc x, timeRateN τc x, 0, 0] : Fin 4 → ℝ) j)
      (interiorDomain hτc χb) := by
    fin_cases j
    · exact hTT
    · exact hTN
    · exact continuousOn_const
    · exact continuousOn_const
  exact (hρ.mul (hv i)).mul (hv k)

section Glued

variable (hM : 0 < M) (hτc : 0 < τc) (hχ : 0 < χb) (hmass : 9 * M * τc ^ 2 = 2 * χb ^ 3)
include hM hτc hχ hmass

/-- **The glued metric of the Oppenheimer–Snyder collapse is `C¹`** on the collar of the boundary
(in fact `C^{1,1}`: its second derivatives jump with the density): the two metrics agree on the
boundary with all their first derivatives. -/
theorem contDiffOn_glue (p q : Fin 4) :
    ContDiffOn ℝ 1 (fun x => glue 1 (interiorMetric hτc χb).coefficient
      (exteriorMetric hM hτc χb).coefficient x p q) (collar hτc χb) :=
  ((contDiffOn_glue_coefficient_iff 1 (interiorMetric hτc χb) (exteriorMetric hM hτc χb)
    (collar hτc χb).isOpen (fun _ hx _ => collar_le_interior hτc hx)
    (fun _ hx _ => collar_le_exterior hτc hx)
    fun _ hy hy1 => coefficient_eq_on_boundary hM hτc hχ hmass hy hy1).mpr
    fun _ hz hz1 p q => fderiv_eq_on_boundary hM hτc hχ hmass hz hz1 p q) p q

/-- **`C¹` exactly because the second fundamental forms agree** (`junction_adapted`,
`junction_oppenheimerSnyder`): in the adapted chart the components `g_{nμ}` have equal normal
derivatives on the boundary, so by `contDiffOn_glue_iff_secondFundamental` the glued metric is
`C¹` if and only if the second fundamental forms of the boundary agree, which they do. -/
theorem contDiffOn_glue_iff_junction :
    (∀ p q, ContDiffOn ℝ 1 (fun x => glue 1 (interiorMetric hτc χb).coefficient
      (exteriorMetric hM hτc χb).coefficient x p q) (collar hτc χb)) ↔
      ∀ z ∈ collar hτc χb, z 1 = 0 → (exteriorMetric hM hτc χb).secondFundamental 1 1 z =
        (interiorMetric hτc χb).secondFundamental 1 1 z :=
  contDiffOn_glue_iff_secondFundamental 1 (interiorMetric hτc χb) (exteriorMetric hM hτc χb)
    (collar hτc χb).isOpen (fun _ hx _ => collar_le_interior hτc hx)
    (fun _ hx _ => collar_le_exterior hτc hx) (mul_one 1)
    (fun _ hy hy1 => coefficient_eq_on_boundary hM hτc hχ hmass hy hy1)
    (fun _ hy hy1 μ => coefficient_normal_on_boundary hM hτc hχ hmass hy hy1 μ)
    fun _ hz hz1 μ => fderiv_eq_on_boundary hM hτc hχ hmass hz hz1 1 μ

/-- **The Oppenheimer–Snyder metric solves the Einstein equations without a surface layer**: the
glued metric (the flat dust ball inside, the Schwarzschild field outside, in the adapted chart)
satisfies the weak Einstein equations `⟨G, φ⟩ = κ ∫ T_{ik} φ^{ik}` on the collar of the boundary
for every test tensor density `φ`, with `T` the dust inside and zero outside. -/
theorem isWeakEinstein_oppenheimerSnyder (hκ : κ ≠ 0) :
    IsWeakEinstein (collar hτc χb) (glue 1 (interiorMetric hτc χb).coefficient
      (exteriorMetric hM hτc χb).coefficient) κ (glue 1 (chartDust κ τc) 0) :=
  isWeakEinstein_glue 1 (interiorMetric hτc χb) (exteriorMetric hM hτc χb)
    (collar hτc χb).isOpen (fun _ hx _ => collar_le_interior hτc hx)
    (fun _ hx _ => collar_le_exterior hτc hx) (mul_one 1)
    (fun _ hy hy1 => coefficient_eq_on_boundary hM hτc hχ hmass hy hy1)
    (fun _ hy hy1 μ => coefficient_normal_on_boundary hM hτc hχ hmass hy hy1 μ)
    (fun _ hz hz1 => (junction_adapted hM hτc hχ hmass hz hz1).2.2.1)
    (continuousOn_chartDust hτc κ) (fun _ _ => continuousOn_const)
    (fun x hx _ j l => by
      have h := isEinstein_interiorMetric (χb := χb) hτc hκ x (collar_le_interior hτc hx) j l
      simpa using h)
    fun x hx _ j l => by
      have h := isEinstein_exteriorMetric (χb := χb) hM hτc hκ x (collar_le_exterior hτc hx) j l
      simpa using h

end Glued


/-! ### A genuine surface layer -/

section Shell

variable {R₀ s : ℝ}

/-- The domain `R₀ + s n > 0`, `0 < θ < π` of the metric `shellMetric R₀ s`. -/
def shellDomain (R₀ s : ℝ) : Opens E :=
  ⟨{x | 0 < R₀ + s * x 1 ∧ 0 < x 2 ∧ x 2 < π},
    (isOpen_lt (continuous_const (y := (0 : ℝ))) (continuous_const.add
      (continuous_const.mul (continuous_apply 1)))).inter isOpen_angle⟩

/-- The coefficients `(−1, 1, (R₀ + s n)², (R₀ + s n)² sin²θ)`. -/
def shellCoeffs (R₀ s : ℝ) (x : E) : Fin 4 → ℝ :=
  ![-1, 1, (R₀ + s * x 1) ^ 2, (R₀ + s * x 1) ^ 2 * Real.sin (x 2) ^ 2]

/-- **A static test metric** `ds² = −dT² + dn² + (R₀ + s n)² dΩ²`: for `s = 1` it is flat space in
spherical co-ordinates about the sphere `n = 0` of radius `R₀`; for `s ≠ 1` its areal radius grows
at the rate `s` across the sphere (as `√(1 − 2M/R₀)` for a Schwarzschild exterior). -/
def shellMetric (R₀ s : ℝ) : CoordinateMetric .timeNegative 3 (shellDomain R₀ s) :=
  ofDiagonal (shellCoeffs R₀ s) (fun i => by
      have hr : ContDiff ℝ ∞ fun x : E => (R₀ + s * x 1) ^ 2 :=
        (contDiff_const.add (contDiff_const.mul (contDiff_apply ℝ (fun _ => ℝ) 1))).pow 2
      have hsin : ContDiff ℝ ∞ fun x : E => Real.sin (x 2) ^ 2 :=
        (Real.contDiff_sin.comp (contDiff_apply ℝ (fun _ => ℝ) 2)).pow 2
      fin_cases i
      · simpa [shellCoeffs] using contDiffOn_const
      · simpa [shellCoeffs] using contDiffOn_const
      · simpa [shellCoeffs] using hr.contDiffOn
      · simpa [shellCoeffs] using (hr.mul hsin).contDiffOn)
    (fun x _ => by simp [shellCoeffs])
    (fun x hx α => by
      have h1 := hx.1
      have h2 := Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2
      fin_cases α <;> simp [shellCoeffs] <;> positivity)

/-- The collar where both test metrics are defined. -/
def shellCollar (R₀ s : ℝ) : Opens E := shellDomain R₀ 1 ⊓ shellDomain R₀ s

/-- The second fundamental form of the sphere `n = 0` for `shellMetric R₀ t`:
`K = diag(0, tR₀, tR₀ sin²θ)`. -/
theorem secondFundamental_shellMetric {t : ℝ} {y : E} (hy1 : y 1 = 0) :
    (shellMetric R₀ t).secondFundamental 1 1 y =
      Matrix.diagonal ![0, t * R₀, t * R₀ * Real.sin (y 2) ^ 2] := by
  have h1 : HasFDerivAt (fun w : E => w 1) (ContinuousLinearMap.proj 1 : E →L[ℝ] ℝ) y :=
    hasFDerivAt_apply 1 y
  have hr := ((h1.const_mul t).const_add R₀).pow 2
  have hs2 : HasFDerivAt (fun w : E => Real.sin (w 2) ^ 2)
      ((2 * Real.sin (y 2) * Real.cos (y 2)) • (ContinuousLinearMap.proj 2 : E →L[ℝ] ℝ)) y := by
    have h := (SchwarzschildExterior.hasFDerivAt_coord 2 (Real.hasDerivAt_sin (y 2))).pow 2
    convert h using 1
    ext v
    simp
    ring
  have hd : fderiv ℝ (fun w : E => (R₀ + t * w 1) ^ 2) y (Pi.single 1 1) = 2 * R₀ * t := by
    rw [hr.fderiv]
    simp [hy1]
  have hd2 : fderiv ℝ (fun w : E => (R₀ + t * w 1) ^ 2 * Real.sin (w 2) ^ 2) y
      (Pi.single 1 1) = 2 * R₀ * t * Real.sin (y 2) ^ 2 := by
    rw [(hr.fun_mul hs2).fderiv]
    simp [hy1]
    ring
  rw [shellMetric, secondFundamental_ofDiagonal]
  congr 1
  funext a
  have hc1 : shellCoeffs R₀ t y 1 = 1 := rfl
  rw [hc1, abs_one, Real.sqrt_one]
  fin_cases a
  · simp [shellCoeffs]
  · change 1 / (2 * 1) * fderiv ℝ (fun w : E => (R₀ + t * w 1) ^ 2) y (Pi.single 1 1) = _
    rw [hd]
    simp
    ring
  · change 1 / (2 * 1) * fderiv ℝ (fun w : E => (R₀ + t * w 1) ^ 2 * Real.sin (w 2) ^ 2) y
      (Pi.single 1 1) = _
    rw [hd2]
    simp
    ring

/-- The induced metric of the sphere `n = 0`: `h = diag(−1, R₀², R₀² sin²θ)`. -/
theorem inducedMetric_shellMetric {t : ℝ} {y : E} (hy1 : y 1 = 0) :
    (shellMetric R₀ t).inducedMetric 1 y =
      Matrix.diagonal ![-1, R₀ ^ 2, R₀ ^ 2 * Real.sin (y 2) ^ 2] := by
  rw [shellMetric, inducedMetric_ofDiagonal]
  congr 1
  funext a
  fin_cases a <;> simp [shellCoeffs, Fin.succAbove, hy1]

/-- The jump of the second fundamental forms gives the surface density
`[K_TT] − h_TT [K] = 2(s − 1)/R₀`. -/
theorem shell_surface_density (hR : 0 < R₀) {y : E} (hy : y ∈ shellCollar R₀ s) (hy1 : y 1 = 0) :
    ((shellMetric R₀ s).secondFundamental 1 1 y 0 0 -
        (shellMetric R₀ 1).secondFundamental 1 1 y 0 0) -
      (shellMetric R₀ s).inducedMetric 1 y 0 0 * ∑ c, ∑ e,
        ((shellMetric R₀ s).inducedMetric 1 y)⁻¹ c e *
          ((shellMetric R₀ s).secondFundamental 1 1 y c e -
            (shellMetric R₀ 1).secondFundamental 1 1 y c e) = 2 * (s - 1) / R₀ := by
  have hsin := (Real.sin_pos_of_pos_of_lt_pi hy.1.2.1 hy.1.2.2).ne'
  have hR0 := hR.ne'
  have hinv : (Matrix.diagonal ![-1, R₀ ^ 2, R₀ ^ 2 * Real.sin (y 2) ^ 2])⁻¹ =
      Matrix.diagonal ![-1, (R₀ ^ 2)⁻¹, (R₀ ^ 2 * Real.sin (y 2) ^ 2)⁻¹] := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hR0]
    field_simp
  rw [secondFundamental_shellMetric hy1, secondFundamental_shellMetric hy1,
    inducedMetric_shellMetric hy1, hinv]
  simp only [Fin.sum_univ_three, Matrix.diagonal_apply]
  simp
  field_simp
  ring


/-- **A mismatched normal derivative produces a genuine surface term.** For `s ≠ 1` the flat
region `n < 0` (`shellMetric R₀ 1`) glued to `shellMetric R₀ s` on `n ≥ 0` is continuous across
the sphere `n = 0`, with `∂_n` its unit normal, but its second fundamental forms jump; for a
test density `φ = b(x) dT ⊗ dT` with a bump `b` at a point of the sphere, the weak Einstein tensor
differs from the integrals of the two smooth Einstein tensors by the surface term
`−∫ 2(s − 1)/R₀ b dy ≠ 0` (`weakEinstein_glue`, `shell_surface_density`). -/
theorem exists_surface_layer (hR : 0 < R₀) (hs : s ≠ 1) :
    ∃ φ : E → Matrix (Fin 4) (Fin 4) ℝ, IsTestDensity (shellCollar R₀ s) φ ∧
      weakEinstein (glue 1 (shellMetric R₀ 1).coefficient (shellMetric R₀ s).coefficient) φ ≠
        (∫ x in {x : E | x 1 < 0}, ∑ j, ∑ l,
            einsteinOf (shellMetric R₀ 1).coefficient x j l * φ x j l) +
          ∫ x in {x : E | 0 < x 1}, ∑ j, ∑ l,
            einsteinOf (shellMetric R₀ s).coefficient x j l * φ x j l := by
  set c : E := ![0, 0, π / 2, 0] with hc
  set r : ℝ := min (R₀ / (2 * (1 + |s|))) (1 / 2) with hrdef
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr1 : r ≤ 1 / 2 := min_le_right _ _
  have hrR : r ≤ R₀ / (2 * (1 + |s|)) := min_le_left _ _
  let b : ContDiffBump c := ⟨r / 2, r, by positivity, by linarith⟩
  -- the closed ball about `c` lies in the collar
  have hball : Metric.closedBall c r ⊆ shellCollar R₀ s := by
    intro x hx
    rw [Metric.mem_closedBall, dist_pi_le_iff hr.le] at hx
    have h1 := hx 1
    have h2 := hx 2
    simp only [hc, Real.dist_eq] at h1 h2
    simp at h1 h2
    have hx1 : |x 1| ≤ R₀ / (2 * (1 + |s|)) := h1.trans hrR
    have hpos : 0 < 1 + |s| := by positivity
    have hsx : |s * x 1| ≤ |s| * (R₀ / (2 * (1 + |s|))) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hx1 (abs_nonneg s)
    have hb1 : |s| * (R₀ / (2 * (1 + |s|))) < R₀ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg s]
    have hb2 : R₀ / (2 * (1 + |s|)) < R₀ := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg s]
    have hθ := abs_le.mp h2
    have hpi := Real.two_le_pi
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · have := (abs_le.mp hx1).1
      show 0 < R₀ + 1 * x 1
      linarith
    · linarith
    · linarith
    · have := (abs_le.mp hsx).1
      show 0 < R₀ + s * x 1
      linarith
    · linarith
    · linarith
  set φ : E → Matrix (Fin 4) (Fin 4) ℝ :=
    fun x => Matrix.of fun i j => if i = 0 ∧ j = 0 then b x else 0 with hφdef
  have hφ0 (x : E) (hx : b x = 0) : φ x = 0 := by
    ext i j
    simp [hφdef, hx]
  have hsupp : Function.support φ ⊆ Function.support b := fun x hx h => hx (hφ0 x h)
  have hφt : IsTestDensity (shellCollar R₀ s) φ := by
    refine ⟨fun j l => ?_, b.hasCompactSupport.mono hsupp, ?_⟩
    · by_cases h : j = 0 ∧ l = 0
      · simpa [hφdef, h] using b.contDiff
      · simpa [hφdef, h] using contDiff_const (c := (0 : ℝ))
    · refine (closure_mono hsupp).trans ?_
      change tsupport b ⊆ _
      rw [b.tsupport_eq]
      exact hball
  refine ⟨φ, hφt, ?_⟩
  have hε : (1 : ℝ) * 1 = 1 := mul_one 1
  rw [weakEinstein_glue 1 (shellMetric R₀ 1) (shellMetric R₀ s) (shellCollar R₀ s).isOpen
    (fun x hx _ => hx.1) (fun x hx _ => hx.2) hε
    (fun y hy hy1 => by
      rw [shellMetric, shellMetric, coefficient_ofDiagonal, coefficient_ofDiagonal]
      congr 1
      funext i
      fin_cases i <;> simp [shellCoeffs, hy1])
    (fun y hy hy1 μ => by
      rw [shellMetric, coefficient_ofDiagonal]
      fin_cases μ <;> simp [shellCoeffs]) hφt]
  -- the surface term
  set f : (Fin 3 → ℝ) → ℝ := fun y => b (Fin.insertNth 1 0 y) with hfdef
  have hS (y : Fin 3 → ℝ) : ∑ a, ∑ b',
        ((shellMetric R₀ s).secondFundamental 1 1 (Fin.insertNth 1 0 y) a b' -
            (shellMetric R₀ 1).secondFundamental 1 1 (Fin.insertNth 1 0 y) a b' -
          (shellMetric R₀ s).inducedMetric 1 (Fin.insertNth 1 0 y) a b' * ∑ c', ∑ e,
            ((shellMetric R₀ s).inducedMetric 1 (Fin.insertNth 1 0 y))⁻¹ c' e *
              ((shellMetric R₀ s).secondFundamental 1 1 (Fin.insertNth 1 0 y) c' e -
                (shellMetric R₀ 1).secondFundamental 1 1 (Fin.insertNth 1 0 y) c' e)) *
          φ (Fin.insertNth 1 0 y) (Fin.succAbove 1 a) (Fin.succAbove 1 b') =
      2 * (s - 1) / R₀ * f y := by
    by_cases hb : b (Fin.insertNth 1 0 y) = 0
    · simp [hφ0 _ hb, hfdef, hb]
    · have hy : (Fin.insertNth 1 0 y : E) ∈ shellCollar R₀ s :=
        hball (b.tsupport_eq ▸ subset_tsupport _ hb)
      have hy1 : (Fin.insertNth 1 (0 : ℝ) y : E) 1 = 0 := Fin.insertNth_apply_same _ _ _
      rw [← shell_surface_density hR hy hy1]
      simp only [Fin.sum_univ_three, hφdef, Matrix.of_apply, hfdef]
      simp [Fin.succAbove]
  rw [integral_congr_ae (Eventually.of_forall hS), integral_const_mul]
  -- the bump on the sphere has a positive integral
  set y₀ : Fin 3 → ℝ := ![0, π / 2, 0] with hy₀
  have hιc : (Fin.insertNth 1 (0 : ℝ) y₀ : E) = c := by
    ext j
    fin_cases j <;> simp [hy₀, hc] <;> rfl
  have hdist (y y' : Fin 3 → ℝ) :
      dist (Fin.insertNth 1 (0 : ℝ) y : E) (Fin.insertNth 1 (0 : ℝ) y') = dist y y' := by
    apply le_antisymm
    · rw [dist_pi_le_iff dist_nonneg]
      intro j
      refine Fin.succAboveCases 1 ?_ (fun i => ?_) j
      · simp
      · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
        exact dist_le_pi_dist y y' i
    · rw [dist_pi_le_iff dist_nonneg]
      intro i
      have h := dist_le_pi_dist (Fin.insertNth 1 (0 : ℝ) y : E) (Fin.insertNth 1 0 y')
        (Fin.succAbove 1 i)
      rwa [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove] at h
  have hfc : Continuous f :=
    b.continuous.comp (Continuous.finInsertNth (A := fun _ => ℝ) 1 continuous_const
      continuous_id)
  have hfK : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_closedBall y₀ r) fun y hy => ?_
    refine b.zero_of_le_dist ?_
    have h := hdist y y₀
    rw [hιc] at h
    rw [h]
    rw [Metric.mem_closedBall, not_le] at hy
    exact hy.le
  have hpos : 0 < ∫ y, f y := by
    rw [integral_pos_iff_support_of_nonneg (fun y => b.nonneg) (hfc.integrable_of_hasCompactSupport
      hfK)]
    refine lt_of_lt_of_le (Metric.measure_ball_pos volume y₀ hr) (measure_mono fun y hy => ?_)
    refine (b.pos_of_mem_ball ?_).ne'
    have h := hdist y y₀
    rw [hιc] at h
    rw [Metric.mem_ball, h]
    exact hy
  have hne : 2 * (s - 1) / R₀ * ∫ y, f y ≠ 0 := by
    have : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    have := hR.ne'
    positivity
  intro h
  apply hne
  linarith

end Shell

end ProjectAinos.GeneralRelativity.CollapseJunction
