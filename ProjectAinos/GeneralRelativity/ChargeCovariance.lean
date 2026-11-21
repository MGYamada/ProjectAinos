/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.AsymptoticCharge
public import ProjectAinos.SmoothGeometry.Lorentzian.HyperplaneFlux
public import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorCovariance
import Mathlib.Tactic

/-!
# The four-vector character of the energy and momentum

Landau–Lifshitz, §96 (after (96.17)) and §105: the energy and momentum `P^i` of matter and
gravitational field form a four-vector under linear Lorentz changes of the co-ordinates. With the
charges `P^i(t) = lim ½ ∮ h^{i0α} n_α dA` of the slice `x⁰ = t` (`charge`, `AsymptoticCharge.lean`)
and the co-ordinates `x'` with `x = L x'` (`CoordinateMetric.linearPullback`):

* `tiltTime`, `tiltSlope`, `mulVec_vector_eq`: the slice `x'⁰ = t` is, in the co-ordinates `x`,
  the hyperplane `x⁰ = t/M₀₀ + ⟪v, x⟫` with `v_β = −M_{0β}/M₀₀`, `M = L⁻¹`, over the point
  `tiltSpace L t y` of space; `det_tiltLinear`, `det_submatrix_succ`: its spatial map has the
  determinant `det L · M₀₀`.
* `integral_comp_affine`: the change of variables `∫ G(A y + q) dy = |det A|⁻¹ ∫ G`.
* `integral_totalDensity_linearPullback`: the integral of `|g'|(G'^{i0} + t'^{i0})` over the slice
  `x'⁰ = t` is `|det L| M^i_a` times the flux of the conserved current `|g| (G^{ak} + t^{ak})`
  through the tilted hyperplane (`Hyperplane.graphFlux`).
* `charge_linearPullback`: **the charges transform as a four-vector**: if the total density is
  `O(r⁻⁴)` uniformly on the wedge between the slice `x⁰ = c₀` and the tilted hyperplane, then
  `P'^i(t) = |det L| Σ_a M^i_a P^a(c₀)`.
* `GalileanBoundsAt`, `IsGalileanOnWedge`: the decay `g − η = O(1/r)`, `∂g = O(1/r²)`,
  `∂²g = O(1/r³)` at a point and uniformly on the wedge; `GalileanBoundsAt.abs_totalDensity_le`:
  outside matter the total density is `O(r⁻⁴)`; `IsAsymptoticallyGalilean.isGalileanOnWedge`:
  uniform decay on all slices gives every wedge (the proved instance).
* `charge_linearPullback_of_einstein`: the transformation law with the Einstein equations,
  matter of compact spatial support on the wedge and the decay of the metric on the wedge.
* `lorentz_det_sq`, `lorentz_inv`: a Lorentz matrix `Lᵀ η L = η` has `(det L)² = 1` and
  `L⁻¹ = η Lᵀ η`, so `L⁻¹₀₀ = L₀₀`; `charge_lorentz`: **for an orthochronous Lorentz matrix,
  `P'^i = (L⁻¹)^i_a P^a`**.

**Passive and active.** `g' = linearPullback g L` is the same field in the co-ordinates `x'` with
`x = L x'`; `P'` are the components of the same four-vector `P` in these co-ordinates, so the
law is `P' = L⁻¹ P`, the contravariant law of the components. Read actively, `g'` is the field
`g` moved by `L⁻¹`, and its four-momentum is `L⁻¹ P`.

* Instance: `charge_linearPullback_minkowski`: Minkowski space has zero charges in every linearly
  transformed co-ordinate system.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter TopologicalSpace
open scoped Topology ContDiff Matrix

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry SmoothGeometry.CoordinateMetric SmoothGeometry.Minkowski
  SmoothGeometry.Hyperplane

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The tilted hyperplane of a linear change of co-ordinates -/

variable (L : Matrix (Fin 4) (Fin 4) ℝ)

/-- The time `t/M₀₀` at the spatial origin of the hyperplane `x'⁰ = t`, `M = L⁻¹`. -/
def tiltTime (t : ℝ) : ℝ := t / L⁻¹ 0 0

/-- The slope `v_β = −M_{0β}/M₀₀` of the hyperplane `x'⁰ = t`, `M = L⁻¹`. -/
def tiltSlope : E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm fun β => -(L⁻¹ 0 β.succ / L⁻¹ 0 0)

theorem tiltSlope_apply (β : Fin 3) : tiltSlope L β = -(L⁻¹ 0 β.succ / L⁻¹ 0 0) := rfl

/-- The point of space below the event `L (t, y)`. -/
def tiltSpace (t : ℝ) (y : E3) : E3 := space (L *ᵥ vector t y)

/-- The linear part `y ↦ space (L (0, y))` of `tiltSpace`. -/
def tiltLinear : E3 →L[ℝ] E3 :=
  space.comp ((matrixMap L).comp
    ((Wave.timeSpaceEquiv.symm : ℝ × E3 →L[ℝ] MinkowskiModel 3).comp
      (ContinuousLinearMap.inr ℝ ℝ E3)))

theorem tiltLinear_apply (y : E3) : tiltLinear L y = space (L *ᵥ vector 0 y) := by
  simp [tiltLinear]

theorem vector_add_vector (t s : ℝ) (y z : E3) :
    vector t y + vector s z = (vector (t + s) (y + z) : MinkowskiModel 3) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [vector]

theorem tiltSpace_eq (t : ℝ) (y : E3) : tiltSpace L t y = tiltLinear L y + tiltSpace L t 0 := by
  rw [tiltLinear_apply, tiltSpace, tiltSpace, ← map_add, ← Matrix.mulVec_add, vector_add_vector,
    zero_add, add_zero]

/-- **The slice `x'⁰ = t` is the tilted hyperplane** `x⁰ = t/M₀₀ + ⟪v, x⟫` in the co-ordinates
`x = L x'`. -/
theorem mulVec_vector_eq (hL : L.det ≠ 0) (hM : L⁻¹ 0 0 ≠ 0) (t : ℝ) (y : E3) :
    L *ᵥ vector t y = vector (tiltTime L t + inner ℝ (tiltSlope L) (tiltSpace L t y))
      (tiltSpace L t y) := by
  set X := L *ᵥ vector t y with hXdef
  have hX : L⁻¹ *ᵥ X = vector t y := by
    rw [hXdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hL),
      Matrix.one_mulVec]
  have h0 := congrFun hX 0
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, vector_zero] at h0
  have e1 : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := rfl
  have e2 : (Fin.succ (1 : Fin 3) : Fin 4) = 2 := rfl
  have e3 : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl
  have hX0 : X 0 = (t - (L⁻¹ 0 1 * X 1 + L⁻¹ 0 2 * X 2 + L⁻¹ 0 3 * X 3)) / L⁻¹ 0 0 := by
    rw [eq_div_iff hM]
    linarith
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [vector_zero, tiltTime, tiltSpace, PiLp.inner_apply, tiltSlope_apply, space_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_three, e1, e2, e3]
    rw [← hXdef, hX0]
    field_simp
    ring
  · simp [tiltSpace, hXdef]

/-- The matrix of `tiltLinear` is the spatial block of `L`. -/
theorem det_tiltLinear :
    LinearMap.det (tiltLinear L : E3 →ₗ[ℝ] E3) = (L.submatrix Fin.succ Fin.succ).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  congr 1
  ext β α
  simp [LinearMap.toMatrix_apply, tiltLinear_apply, vector_zero_single]

/-- The cofactor of `L₀₀`: `det(L_{αβ}) = det L · (L⁻¹)₀₀`. -/
theorem det_submatrix_succ (hL : L.det ≠ 0) :
    (L.submatrix Fin.succ Fin.succ).det = L.det * L⁻¹ 0 0 := by
  have h := Matrix.adjugate_fin_succ_eq_det_submatrix L 0 0
  rw [Fin.succAbove_zero] at h
  rw [Matrix.inv_def, Matrix.smul_apply, h, Ring.inverse_eq_inv', smul_eq_mul]
  simp only [Fin.val_zero, add_zero, pow_zero, one_mul]
  field_simp

/-! ### The change of variables -/

/-- **The affine change of variables** `∫ G(A y + q) dy = |det A|⁻¹ ∫ G` on `ℝ³`. -/
theorem integral_comp_affine {A : E3 →L[ℝ] E3} (hA : LinearMap.det (A : E3 →ₗ[ℝ] E3) ≠ 0)
    (q : E3) (G : E3 → ℝ) :
    ∫ y, G (A y + q) = |LinearMap.det (A : E3 →ₗ[ℝ] E3)|⁻¹ * ∫ z, G z := by
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure E3)) hA
  have hemb : MeasurableEmbedding (A : E3 → E3) :=
    ((LinearMap.equivOfDetNeZero (A : E3 →ₗ[ℝ] E3) hA).toContinuousLinearEquiv.toHomeomorph
      ).measurableEmbedding
  rw [ContinuousLinearMap.coe_coe] at hmap
  calc ∫ y, G (A y + q) = ∫ z, G (z + q) ∂(Measure.map A volume) :=
        (hemb.integral_map (fun z => G (z + q))).symm
    _ = |LinearMap.det (A : E3 →ₗ[ℝ] E3)|⁻¹ * ∫ z, G (z + q) := by
        rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv,
          smul_eq_mul]
    _ = _ := by rw [integral_add_right_eq_self]

/-- An integrable function composed with an invertible affine map is integrable. -/
theorem integrable_comp_affine {A : E3 →L[ℝ] E3} (hA : LinearMap.det (A : E3 →ₗ[ℝ] E3) ≠ 0)
    (q : E3) {G : E3 → ℝ} (hG : Integrable G) : Integrable fun y => G (A y + q) := by
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure E3)) hA
  have hemb : MeasurableEmbedding (A : E3 → E3) :=
    ((LinearMap.equivOfDetNeZero (A : E3 →ₗ[ℝ] E3) hA).toContinuousLinearEquiv.toHomeomorph
      ).measurableEmbedding
  rw [ContinuousLinearMap.coe_coe] at hmap
  have h : Integrable (fun z => G (z + q)) (Measure.map A volume) := by
    rw [hmap]
    exact (hG.comp_add_right q).smul_measure ENNReal.ofReal_ne_top
  exact hemb.integrable_map_iff.mp h

/-! ### The charges in the transformed co-ordinates -/

variable {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} (g : CoordinateMetric σ 3 U)

/-- The conserved current `k ↦ |g| (G^{ak} + t^{ak})` of the free index `a`. -/
def totalCurrent (a : Fin 4) : Fin 4 → MinkowskiModel 3 → ℝ := fun k z => g.totalDensity z a k

variable {L}

/-- `Σ_b M_{ib'} M_{0b} T_b = M_{ib'} M₀₀ (T₀ − Σ_α v_α T_α)` with `v_α = −M_{0α}/M₀₀`. -/
theorem sum_inv_zero_mul (hM : L⁻¹ 0 0 ≠ 0) (c : ℝ) (T : Fin 4 → ℝ) :
    ∑ b, c * L⁻¹ 0 b * T b =
      c * (L⁻¹ 0 0 * (T 0 - ∑ α : Fin 3, tiltSlope L α * T α.succ)) := by
  simp only [Fin.sum_univ_succ (f := fun b => c * L⁻¹ 0 b * T b), tiltSlope_apply]
  simp only [Fin.sum_univ_three]
  field_simp
  ring

/-- **The integrand on a transformed slice is the flux integrand on the tilted hyperplane**:
`|g'| (G'^{i0} + t'^{i0})(t, y) = (det L)² M^i_a M₀₀ (J_a⁰ − Σ_α v_α J_a^α)` at the point
`L (t, y) = (t/M₀₀ + ⟪v, z⟫, z)`, `z = tiltSpace L t y`. -/
theorem totalDensity_linearPullback_slice (hL : L.det ≠ 0) (hM : L⁻¹ 0 0 ≠ 0) {t : ℝ} {y : E3}
    (hy : L *ᵥ vector t y ∈ U) (i : Fin 4) :
    (g.linearPullback L hL).totalDensity (vector t y) i 0 =
      L.det ^ 2 * ∑ a, L⁻¹ i a * (L⁻¹ 0 0 *
        graphIntegrand (totalCurrent g a) (tiltTime L t) (tiltSlope L) (tiltSpace L t y)) := by
  rw [totalDensity_linearPullback g (mem_pullbackOpens.mpr hy)]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_inv_zero_mul hM, graphIntegrand, ← mulVec_vector_eq L hL hM t y]
  rfl

/-- **The charge integral of the transformed slice**: if the flux integrands of the currents
`J_a` on the tilted hyperplane are integrable, then
`∫ |g'| (G'^{i0} + t'^{i0})(t, y) dy = |det L| Σ_a M^i_a ∫ (J_a⁰ − Σ_α v_α J_a^α)`. -/
theorem integral_totalDensity_linearPullback (hL : L.det ≠ 0) (hM : 0 < L⁻¹ 0 0) {t : ℝ}
    (hU : ∀ y, L *ᵥ vector t y ∈ U)
    (hint : ∀ a, Integrable (graphIntegrand (totalCurrent g a) (tiltTime L t) (tiltSlope L)))
    (i : Fin 4) :
    (Integrable fun y => (g.linearPullback L hL).totalDensity (vector t y) i 0) ∧
      ∫ y, (g.linearPullback L hL).totalDensity (vector t y) i 0 =
        |L.det| * ∑ a, L⁻¹ i a * graphFlux (totalCurrent g a) (tiltTime L t) (tiltSlope L) := by
  have hA : LinearMap.det (tiltLinear L : E3 →ₗ[ℝ] E3) ≠ 0 := by
    rw [det_tiltLinear, det_submatrix_succ L hL]
    exact mul_ne_zero hL hM.ne'
  have hpt (y : E3) := totalDensity_linearPullback_slice g hL hM.ne' (hU y) i
  have hsp (G : E3 → ℝ) : (fun y => G (tiltSpace L t y)) =
      fun y => G (tiltLinear L y + tiltSpace L t 0) :=
    funext fun y => by rw [tiltSpace_eq L t y]
  have hcomp (a : Fin 4) : Integrable fun y =>
      graphIntegrand (totalCurrent g a) (tiltTime L t) (tiltSlope L) (tiltSpace L t y) := by
    rw [hsp (graphIntegrand (totalCurrent g a) (tiltTime L t) (tiltSlope L))]
    exact integrable_comp_affine hA _ (hint a)
  have hint' (a : Fin 4) : Integrable fun y => L⁻¹ i a * (L⁻¹ 0 0 *
      graphIntegrand (totalCurrent g a) (tiltTime L t) (tiltSlope L) (tiltSpace L t y)) :=
    ((hcomp a).const_mul _).const_mul _
  refine ⟨?_, ?_⟩
  · simp only [hpt]
    exact (integrable_finsetSum _ fun a _ => hint' a).const_mul _
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_finsetSum _ fun a _ => hint' a]
  have hval (a : Fin 4) : ∫ y, L⁻¹ i a * (L⁻¹ 0 0 *
      graphIntegrand (totalCurrent g a) (tiltTime L t) (tiltSlope L) (tiltSpace L t y)) =
      L⁻¹ i a * (L⁻¹ 0 0 * (|L.det * L⁻¹ 0 0|⁻¹ *
        graphFlux (totalCurrent g a) (tiltTime L t) (tiltSlope L))) := by
    rw [integral_const_mul, integral_const_mul,
      hsp (graphIntegrand (totalCurrent g a) (tiltTime L t) (tiltSlope L)),
      integral_comp_affine hA, det_tiltLinear, det_submatrix_succ L hL]
    rfl
  simp only [hval]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hd : L.det ^ 2 = |L.det| ^ 2 := (sq_abs _).symm
  have hd0 : 0 < |L.det| := abs_pos.mpr hL
  rw [abs_mul, abs_of_pos hM, hd]
  field_simp

/-- **The energy and momentum transform as a four-vector** (Landau–Lifshitz §96): let `M = L⁻¹`
with `M₀₀ > 0`, and let the wedge between the slice `x⁰ = c₀` and the hyperplane `x'⁰ = t`
(`x⁰ = t/M₀₀ + ⟪v, x⟫`) lie in `U`, with the total density `|g| (G^{ak} + t^{ak})` at most
`K/‖y‖⁴` on the wedge beyond a radius `R₀`. Then the charges of the co-ordinates `x'` with
`x = L x'` on the slice `x'⁰ = t` are `P'^i(t) = |det L| Σ_a M^i_a P^a(c₀)`. -/
theorem charge_linearPullback (hL : L.det ≠ 0) (hM : 0 < L⁻¹ 0 0) (t c₀ : ℝ)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ (tiltTime L t) (tiltSlope L) s y ∈ U)
    {R₀ K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, R₀ ≤ ‖y‖ → ∀ a k,
      |g.totalDensity (wedgePoint c₀ (tiltTime L t) (tiltSlope L) s y) a k| ≤ K / ‖y‖ ^ 4)
    (i : Fin 4) :
    charge (g.linearPullback L hL) t i = |L.det| * ∑ a, L⁻¹ i a * charge g c₀ a := by
  set c₁ := tiltTime L t
  set v := tiltSlope L
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hslice : ∀ y : E3, vector c₀ y ∈ U := fun y => by
    simpa [wedgePoint_zero] using hW 0 h0 y
  have hgraph : ∀ y : E3, vector (c₁ + inner ℝ v y) y ∈ U := fun y => by
    simpa [wedgePoint_one] using hW 1 h1 y
  have hU' : ∀ y : E3, L *ᵥ vector t y ∈ U := fun y => by
    rw [mulVec_vector_eq L hL hM.ne' t y]
    exact hgraph _
  -- the slice integrands of `g`
  have hint₀ (a : Fin 4) : Integrable fun y : E3 => g.totalDensity (vector c₀ y) a 0 :=
    integrable_of_le_div_pow_four (continuous_totalDensity_slice hslice a 0) hK
      fun y hy => by simpa [wedgePoint_zero] using hdecay 0 h0 y hy a 0
  -- the flux integrands on the tilted hyperplane
  have hcg (a k : Fin 4) : Continuous fun y : E3 =>
      g.totalDensity (vector (c₁ + inner ℝ v y) y) a k := by
    have h := (g.contDiffOn_totalDensity a k).continuousOn.comp_continuous
      (contDiff_wedgePoint c₀ c₁ v 1 (n := 0)).continuous (fun y => hW 1 h1 y)
    simpa [Function.comp_def, wedgePoint_one] using h
  have hint₁ (a : Fin 4) : Integrable (graphIntegrand (totalCurrent g a) c₁ v) := by
    refine integrable_of_le_div_pow_four (R := R₀) (K := (1 + ∑ α : Fin 3, |v α|) * K) ?_
      (by positivity) fun y hy => ?_
    · exact (hcg a 0).sub (continuous_finsetSum _ fun α _ => continuous_const.mul (hcg a α.succ))
    · have hd (k : Fin 4) : |g.totalDensity (vector (c₁ + inner ℝ v y) y) a k| ≤ K / ‖y‖ ^ 4 := by
        simpa [wedgePoint_one] using hdecay 1 h1 y hy a k
      unfold graphIntegrand totalCurrent
      have hs : |∑ α : Fin 3, v α * g.totalDensity (vector (c₁ + inner ℝ v y) y) a α.succ| ≤
          ∑ α : Fin 3, |v α| * (K / ‖y‖ ^ 4) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hd α.succ) (abs_nonneg _))
      calc _ ≤ |g.totalDensity (vector (c₁ + inner ℝ v y) y) a 0| +
            |∑ α : Fin 3, v α * g.totalDensity (vector (c₁ + inner ℝ v y) y) a α.succ| :=
            abs_sub _ _
        _ ≤ K / ‖y‖ ^ 4 + ∑ α : Fin 3, |v α| * (K / ‖y‖ ^ 4) := add_le_add (hd 0) hs
        _ = (1 + ∑ α : Fin 3, |v α|) * K / ‖y‖ ^ 4 := by
          rw [← Finset.sum_mul]
          ring
  -- the tilted fluxes are the slice integrals
  have hflux (a : Fin 4) : ∫ y : E3, g.totalDensity (vector c₀ y) a 0 =
      graphFlux (totalCurrent g a) c₁ v :=
    integral_eq_graphFlux (J := totalCurrent g a) U.isOpen
      (fun k => (g.contDiffOn_totalDensity a k).of_le (by simp))
      (fun z hz => g.sum_fderiv_totalDensity hz a) hW hK
      (fun s hs y hy k => hdecay s hs y hy a k) (hint₀ a) (hint₁ a)
  have hcharge (a : Fin 4) : charge g c₀ a = ∫ y : E3, g.totalDensity (vector c₀ y) a 0 :=
    (tendsto_surfaceCharge_of_integrable hslice (hint₀ a)).limUnder_eq
  obtain ⟨hint', hval⟩ := integral_totalDensity_linearPullback g hL hM hU' hint₁ i
  have hslice' : ∀ y : E3, vector t y ∈ pullbackOpens U L := fun y => mem_pullbackOpens.mpr (hU' y)
  have hc' : charge (g.linearPullback L hL) t i =
      ∫ y, (g.linearPullback L hL).totalDensity (vector t y) i 0 :=
    (tendsto_surfaceCharge_of_integrable hslice' hint').limUnder_eq
  rw [hc', hval]
  simp only [hcharge, hflux]
  rfl

/-! ### Decay at an event and on the wedge -/

/-- **The decay of a metric at an event `z` at the distance `r`**: `z ∈ U`,
`|g_{ab} − η_{ab}| ≤ C/r`, `|∂_c g_{ab}| ≤ C/r²` and `|∂_c ∂_e g_{ab}| ≤ C/r³`. -/
structure GalileanBoundsAt (g : CoordinateMetric σ 3 U) (z : MinkowskiModel 3) (r C : ℝ) :
    Prop where
  /-- The event lies in `U`. -/
  mem : z ∈ U
  /-- `|g_{ab} − η_{ab}| ≤ C/r`. -/
  coefficient_le : ∀ a b, |g.coefficient z a b - minkowskiCoefficient σ a b| ≤ C / r
  /-- `|∂_c g_{ab}| ≤ C/r²`. -/
  fderiv_le : ∀ a b c,
    |fderiv ℝ (fun w => g.coefficient w a b) z (Pi.single c 1)| ≤ C / r ^ 2
  /-- `|∂_c ∂_e g_{ab}| ≤ C/r³`. -/
  secondDerivative_le : ∀ a b c e, |g.secondDerivative z a b c e| ≤ C / r ^ 3

namespace GalileanBoundsAt

variable {g} {z : MinkowskiModel 3} {r C : ℝ}

theorem coefficient_near (h : GalileanBoundsAt g z r C) (hr : 0 < r) (hC : 8 * C ≤ r)
    (a b : Fin 4) : |g.coefficient z a b - minkowskiCoefficient σ a b| ≤ 1 / 8 := by
  refine (h.coefficient_le a b).trans ?_
  rw [div_le_iff₀ hr]
  linarith

theorem abs_inv_le (h : GalileanBoundsAt g z r C) (hr : 0 < r) (hC : 8 * C ≤ r) (a b : Fin 4) :
    |(g.coefficient z)⁻¹ a b| ≤ 2 :=
  (inv_bound_of_near_minkowski (h.coefficient_near hr hC)).2.1 a b

theorem densityOf_sq_le (h : GalileanBoundsAt g z r C) (hr : 0 < r) (hC : 8 * C ≤ r) :
    densityOf g.coefficient z ^ 2 ≤ 384 := by
  rw [densityOf, Real.sq_sqrt (abs_nonneg _)]
  exact (inv_bound_of_near_minkowski (h.coefficient_near hr hC)).2.2

theorem abs_christoffelOf_le (h : GalileanBoundsAt g z r C) (hr : 0 < r) (hC : 8 * C ≤ r)
    (k i j : Fin 4) : |christoffelOf g.coefficient z k i j| ≤ 12 * C / r ^ 2 := by
  have hD := h.fderiv_le
  unfold christoffelOf
  have hterm (l : Fin 4) : |(g.coefficient z)⁻¹ k l *
      (fderiv ℝ (fun w => g.coefficient w j l) z (Pi.single i 1) +
       fderiv ℝ (fun w => g.coefficient w l i) z (Pi.single j 1) -
       fderiv ℝ (fun w => g.coefficient w i j) z (Pi.single l 1)) / 2| ≤ 3 * C / r ^ 2 := by
    rw [mul_div_assoc]
    have h3 : |(fderiv ℝ (fun w => g.coefficient w j l) z (Pi.single i 1) +
        fderiv ℝ (fun w => g.coefficient w l i) z (Pi.single j 1) -
        fderiv ℝ (fun w => g.coefficient w i j) z (Pi.single l 1)) / 2| ≤ 3 * C / r ^ 2 / 2 := by
      obtain ⟨h1, h1'⟩ := abs_le.mp (hD j l i)
      obtain ⟨h2, h2'⟩ := abs_le.mp (hD l i j)
      obtain ⟨h3, h3'⟩ := abs_le.mp (hD i j l)
      rw [abs_div, abs_two]
      refine div_le_div_of_nonneg_right ?_ zero_le_two
      refine abs_le.mpr ⟨?_, ?_⟩ <;> rw [mul_div_assoc] <;> linarith
    calc _ ≤ 2 * (3 * C / r ^ 2 / 2) := abs_mul_le_mul_of_le (h.abs_inv_le hr hC k l) h3
      _ = 3 * C / r ^ 2 := by ring
  calc _ ≤ ((4 : ℕ) : ℝ) * (3 * C / r ^ 2) := abs_sum_fin_le hterm
    _ = 12 * C / r ^ 2 := by push_cast; ring

/-- **The pseudotensor decays like `r⁻⁴`** at an event with the decay of the metric. -/
theorem abs_pseudotensor_le (h : GalileanBoundsAt g z r C) (hr : 0 < r) (hC : 8 * C ≤ r)
    (i k : Fin 4) : |g.pseudotensor z i k| ≤ 1327104 * C ^ 2 / r ^ 4 := by
  rw [pseudotensor_eq h.mem]
  have hb := abs_pseudoBraces_le (n := 4) (K := 2) (B := 12 * C / r ^ 2)
    (fun a b => h.abs_inv_le hr hC a b) (fun a b c => h.abs_christoffelOf_le hr hC a b c) i k
  rw [abs_div, abs_two]
  calc _ ≤ 18 * ((4 : ℕ) : ℝ) ^ 4 * 2 ^ 2 * (12 * C / r ^ 2) ^ 2 / 2 :=
        div_le_div_of_nonneg_right hb zero_le_two
    _ = 1327104 * C ^ 2 / r ^ 4 := by
      field_simp
      norm_num
      ring

/-- **The total density decays like `r⁻⁴` outside matter**: with `G^{ik} = κ T^{ik}` and
`T^{ik}(z) = 0`, `|g| |G^{ik} + t^{ik}| ≤ K/r⁴`, `K = decayConstant C`. -/
theorem abs_totalDensity_le (h : GalileanBoundsAt g z r C) (hr : 0 < r) (hC : 8 * C ≤ r)
    {κ : ℝ} {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {i k : Fin 4}
    (hm : T z i k = 0) : |g.totalDensity z i k| ≤ decayConstant C / r ^ 4 := by
  rw [g.totalDensity_eq hT h.mem, hm, mul_zero, zero_add, abs_mul, abs_of_nonneg (sq_nonneg _),
    decayConstant, mul_div_assoc]
  exact mul_le_mul (h.densityOf_sq_le hr hC) (h.abs_pseudotensor_le hr hC i k) (abs_nonneg _)
    (by norm_num)

end GalileanBoundsAt

/-- On a slice that is Galilean at large distances, the events beyond `R₀` have the decay. -/
theorem IsAsymptoticallyGalileanAt.galileanBoundsAt {g : CoordinateMetric σ 3 U} {t R₀ C : ℝ}
    (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3} (hx : R₀ ≤ ‖x‖) :
    GalileanBoundsAt g (vector t x) ‖x‖ C :=
  ⟨h.mem x hx, h.coefficient_le x hx, h.fderiv_le x hx, h.secondDerivative_le x hx⟩

/-- **A metric Galilean at large distances uniformly on the wedge** between the slice `x⁰ = c₀`
and the hyperplane `x⁰ = c₁ + ⟪v, x⟫`: the wedge lies in `U`, and its events above `‖y‖ ≥ R₀`
have the decay at the distance `‖y‖`. -/
structure IsGalileanOnWedge (g : CoordinateMetric σ 3 U) (c₀ c₁ : ℝ) (v : E3) (R₀ C : ℝ) :
    Prop where
  /-- The radius beyond which the bounds hold is positive. -/
  radius_pos : 0 < R₀
  /-- The wedge lies in `U`. -/
  mem : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ U
  /-- The decay beyond `R₀`. -/
  bounds : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, R₀ ≤ ‖y‖ →
    GalileanBoundsAt g (wedgePoint c₀ c₁ v s y) ‖y‖ C

/-- **The proved instance**: a metric on all of space-time that is Galilean at large distances on
every slice with the same constants is so on every wedge. -/
theorem IsAsymptoticallyGalilean.isGalileanOnWedge {g : CoordinateMetric σ 3 ⊤} {R₀ C : ℝ}
    (h : IsAsymptoticallyGalilean g R₀ C) (c₀ c₁ : ℝ) (v : E3) :
    IsGalileanOnWedge g c₀ c₁ v R₀ C :=
  ⟨(h 0).radius_pos, fun _ _ _ => trivial,
    fun s _ y hy => (h (wedgeTime c₀ c₁ v s y)).galileanBoundsAt hy⟩

/-- On the wedge, outside matter, the total density decays like `r⁻⁴`. -/
theorem IsGalileanOnWedge.abs_totalDensity_le {g : CoordinateMetric σ 3 U} {c₀ c₁ : ℝ} {v : E3}
    {R₀ C : ℝ} (h : IsGalileanOnWedge g c₀ c₁ v R₀ C) {κ : ℝ}
    {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {Rm : ℝ}
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, Rm ≤ ‖y‖ → ∀ a k, T (wedgePoint c₀ c₁ v s y) a k = 0) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, max (max R₀ (8 * C)) Rm ≤ ‖y‖ → ∀ a k,
      |g.totalDensity (wedgePoint c₀ c₁ v s y) a k| ≤ decayConstant C / ‖y‖ ^ 4 := by
  intro s hs y hy a k
  have hR := le_of_max_le_left (le_of_max_le_left hy)
  have hC := le_of_max_le_right (le_of_max_le_left hy)
  exact (h.bounds s hs y hR).abs_totalDensity_le (h.radius_pos.trans_le hR) hC hT
    (hm s hs y (le_of_max_le_right hy) a k)

/-- **The four-vector character with the Einstein equations** (Landau–Lifshitz §§96, 105): if
`G^{ik} = κ T^{ik}` on `U`, the metric is Galilean at large distances uniformly on the wedge
between the slice `x⁰ = c₀` and the slice `x'⁰ = t` of the co-ordinates `x = L x'`
(`M₀₀ > 0`, `M = L⁻¹`), and the matter vanishes on the wedge beyond a radius, then
`P'^i(t) = |det L| Σ_a M^i_a P^a(c₀)`. -/
theorem charge_linearPullback_of_einstein {g : CoordinateMetric σ 3 U} {κ : ℝ}
    {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) (hL : L.det ≠ 0)
    (hM : 0 < L⁻¹ 0 0) (t c₀ : ℝ) {R₀ C Rm : ℝ}
    (hg : IsGalileanOnWedge g c₀ (tiltTime L t) (tiltSlope L) R₀ C)
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, Rm ≤ ‖y‖ → ∀ a k,
      T (wedgePoint c₀ (tiltTime L t) (tiltSlope L) s y) a k = 0) (i : Fin 4) :
    charge (g.linearPullback L hL) t i = |L.det| * ∑ a, L⁻¹ i a * charge g c₀ a :=
  charge_linearPullback g hL hM t c₀ hg.mem (decayConstant_nonneg C)
    (hg.abs_totalDensity_le hT hm) i

/-! ### Lorentz matrices -/

theorem minkowskiCoefficient_mul_self (σ : LorentzConvention) :
    minkowskiCoefficient σ * minkowskiCoefficient σ = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with a
  exact lorentzSign_sq σ a

/-- A Lorentz matrix `Lᵀ η L = η` has `(det L)² = 1`. -/
theorem lorentz_det_sq (hLor : Lᵀ * minkowskiCoefficient σ * L = minkowskiCoefficient σ) :
    L.det ^ 2 = 1 := by
  have h := congrArg Matrix.det hLor
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hη : (minkowskiCoefficient σ).det ≠ 0 := by
    have h1 := congrArg Matrix.det (minkowskiCoefficient_mul_self σ)
    rw [Matrix.det_mul, Matrix.det_one] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have : (L.det ^ 2 - 1) * (minkowskiCoefficient σ).det = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · linarith
  · exact absurd h' hη

/-- The inverse of a Lorentz matrix is `η Lᵀ η`. -/
theorem lorentz_inv (hLor : Lᵀ * minkowskiCoefficient σ * L = minkowskiCoefficient σ) :
    L⁻¹ = minkowskiCoefficient σ * Lᵀ * minkowskiCoefficient σ := by
  refine Matrix.inv_eq_left_inv ?_
  calc minkowskiCoefficient σ * Lᵀ * minkowskiCoefficient σ * L =
      minkowskiCoefficient σ * (Lᵀ * minkowskiCoefficient σ * L) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hLor, minkowskiCoefficient_mul_self]

/-- `(L⁻¹)₀₀ = L₀₀` for a Lorentz matrix. -/
theorem lorentz_inv_zero_zero
    (hLor : Lᵀ * minkowskiCoefficient σ * L = minkowskiCoefficient σ) : L⁻¹ 0 0 = L 0 0 := by
  rw [lorentz_inv hLor]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  have h := lorentzSign_sq σ (0 : Fin 4)
  linear_combination L 0 0 * h

/-- A Lorentz matrix is invertible. -/
theorem lorentz_det_ne_zero (hLor : Lᵀ * minkowskiCoefficient σ * L = minkowskiCoefficient σ) :
    L.det ≠ 0 := by
  intro h0
  have hd := lorentz_det_sq hLor
  rw [h0] at hd
  norm_num at hd

/-- A Lorentz matrix has `|det L| = 1`. -/
theorem lorentz_abs_det (hLor : Lᵀ * minkowskiCoefficient σ * L = minkowskiCoefficient σ) :
    |L.det| = 1 := by
  have h2 : |L.det| ^ 2 = 1 := by rw [sq_abs]; exact lorentz_det_sq hLor
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).mp h2

/-- **The charges are a four-vector under orthochronous Lorentz transformations** (Landau–Lifshitz
§96): for `Lᵀ η L = η` with `L₀₀ > 0`, under the hypotheses of `charge_linearPullback`,
`P'^i(t) = Σ_a (L⁻¹)^i_a P^a(c₀)`, `L⁻¹ = η Lᵀ η` (`lorentz_inv`). -/
theorem charge_lorentz (g : CoordinateMetric σ 3 U)
    (hLor : Lᵀ * minkowskiCoefficient σ * L = minkowskiCoefficient σ) (hL : L.det ≠ 0)
    (h00 : 0 < L 0 0) (t c₀ : ℝ)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ (tiltTime L t) (tiltSlope L) s y ∈ U)
    {R₀ K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, R₀ ≤ ‖y‖ → ∀ a k,
      |g.totalDensity (wedgePoint c₀ (tiltTime L t) (tiltSlope L) s y) a k| ≤ K / ‖y‖ ^ 4)
    (i : Fin 4) :
    charge (g.linearPullback L hL) t i = ∑ a, L⁻¹ i a * charge g c₀ a := by
  rw [charge_linearPullback g hL (by rw [lorentz_inv_zero_zero hLor]; exact h00) t c₀ hW hK
    hdecay i, lorentz_abs_det hLor, one_mul]

/-! ### Minkowski space -/

theorem totalDensity_minkowski {U : Opens (MinkowskiModel 3)} {z : MinkowskiModel 3} (hz : z ∈ U)
    (i k : Fin 4) : (CoordinateMetric.minkowski σ 3 U).totalDensity z i k = 0 := by
  rw [totalDensity, raisedEinstein_minkowski hz, pseudotensor_minkowski hz, add_zero, mul_zero]

/-- Minkowski space is Galilean at large distances on every wedge, an instance of
`IsGalileanOnWedge`. -/
theorem isGalileanOnWedge_minkowski (σ : LorentzConvention) (c₀ c₁ : ℝ) (v : E3) :
    IsGalileanOnWedge (CoordinateMetric.minkowski σ 3 ⊤) c₀ c₁ v 1 0 :=
  (isAsymptoticallyGalilean_minkowski σ).isGalileanOnWedge c₀ c₁ v

/-- **Minkowski space has zero charges in every linearly transformed co-ordinate system**, the
instance of `charge_linearPullback`. -/
theorem charge_linearPullback_minkowski (σ : LorentzConvention) (hL : L.det ≠ 0)
    (hM : 0 < L⁻¹ 0 0) (t c₀ : ℝ) (i : Fin 4) :
    charge ((CoordinateMetric.minkowski σ 3 ⊤).linearPullback L hL) t i = 0 := by
  rw [charge_linearPullback (CoordinateMetric.minkowski σ 3 ⊤) hL hM t c₀ (fun _ _ _ => trivial)
    le_rfl (R₀ := 1) (fun s _ y _ a k => by
      rw [totalDensity_minkowski (U := ⊤) (TopologicalSpace.Opens.mem_top _), abs_zero,
        zero_div]) i]
  simp [(tendsto_surfaceCharge_minkowski σ c₀ _).limUnder_eq, charge]

end ProjectAinos.GeneralRelativity
