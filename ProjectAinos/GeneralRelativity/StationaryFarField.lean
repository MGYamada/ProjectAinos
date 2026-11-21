/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.LinearizedRadiation
public import ProjectAinos.GeneralRelativity.Kerr
public import ProjectAinos.Electrodynamics.Multipole
public import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorFlux
import Mathlib.Tactic

/-!
# The stationary field at large distances from bodies, at linear order

Landau–Lifshitz, §105, (105.15)–(105.16), in the linearized theory about
`η = diag(−1, 1, 1, 1)` of `LinearizedRadiation.lean` (`c = 1`, `κ = 8πG`). The gauge is the
harmonic gauge of the retarded perturbation, and the co-ordinates are the Cartesian co-ordinates
of `η`, centred at the centre of mass of the source.

* `StationarySource S a`: a smooth symmetric field `S_{ab}(x)` of lower-index stresses on space,
  vanishing for `‖x‖ > a` and conserved, `Σ_γ ∂_γ S_{γb} = 0`; `staticStress S` is the
  time-independent stress on space-time, a `LocalizedStress` (`localizedStress`), so that the
  linearized Einstein equations `δG(h) = κ T` hold (`linearizedEinstein_static`) for
  `h = metricPerturbation κ T`, the solution in harmonic gauge.
* `retardedPerturbation_static`: **the field is the Newton potential of the source**,
  `h̄_{ik}(t, x) = 2κ N[S_{ik}](x)`, the solution of the component Poisson equations
  `Δh̄_{ik} = −2κ S_{ik}`.
* The moments, from the conservation by the divergence theorem on balls
  (`integral_fderiv_mul_eq_zero`): `integral_momentum_eq_zero` (`∫ S_{0α} = 0`),
  `currentDipole_antisymm` (`∫ S_{0α} y_β` is antisymmetric), `integral_stress_eq_zero` and
  `stressDipole_eq_zero` (`∫ S_{αβ} = 0`, `∫ S_{αβ} y_γ = 0`).
* **The far field.** For a mass-centred source (`∫ S₀₀ y = 0`) with the mass `M = ∫ S₀₀` and the
  angular momentum `J_{αβ} = ∫ (y_α S_{0β} − y_β S_{0α})`, uniformly on `‖x‖ > a`:
  `abs_hbar_zero_zero_sub_le`: `h̄₀₀ = 2κM/(4π r) + O(r⁻³)`;
  `abs_hbar_zero_succ_sub_le`: `h̄_{0α} = −(κ/4π) Σ_β J_{αβ} x_β/r³ + O(r⁻³)` (the current dipole);
  `abs_hbar_succ_succ_le`: `h̄_{αβ} = O(r⁻³)`; hence `h₀₀ = κM/(4πr) + O(r⁻³)`,
  `h_{αβ} = δ_{αβ} κM/(4πr) + O(r⁻³)` (`abs_metricPerturbation_zero_zero_sub_le`,
  `abs_metricPerturbation_succ_succ_sub_le`). With `κ = 8π`: `g₀₀ = −1 + 2M/r`,
  `g_{αβ} = (1 + 2M/r) δ_{αβ}`, `g_{0α} = −2 J_{αβ} x_β/r³`.
* **The surface integrals.** `massFlux_eq`: the flux of `∇h̄₀₀` through every sphere of radius
  `R > a` is `−2κM`; `angularMomentumFlux_eq`: the flux of
  `x_α ∇h̄_{0β} − x_β ∇h̄_{0α} − e_α h̄_{0β} + e_β h̄_{0α}` is `−2κ J_{αβ}`. So the coefficients of
  the far field are the surface integrals, exactly beyond the source.
* **Kerr** (`Kerr.abs_gtt_add_le`, `Kerr.abs_gtp_add_le`, `Kerr.gtp_zero_spin`): in
  Boyer–Lindquist co-ordinates `g_tt = −1 + 2M/r + O(r⁻³)` and `g_tφ = −2Ma(1 − χ²)/r + O(r⁻³)`,
  `g_tφ = 0` for `a = 0`; `abs_spinField_sub_gtp_le`: **the linear field of a source of angular
  momentum `J₁₂ = −Ma` about the third axis has `h(∂_t, ∂_φ) = g_tφ + O(r⁻²)`** at the point of
  polar co-ordinates `(r, χ, φ)`, with `κ = 8π`; `abs_metricPerturbation_zero_zero_sub_gtt_le`:
  `h₀₀ = g_tt + 1 + O(r⁻³)` for the mass `M`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff RealInnerProductSpace

namespace ProjectAinos.GeneralRelativity.StationaryFarField

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Potential
open Electrodynamics Electrodynamics.Multipole LinearizedRadiation SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Stationary sources -/

/-- **A stationary source**: a smooth symmetric field `S_{ab}(x)` of lower-index stresses on
space with its support in the ball `‖x‖ ≤ a`, conserved in the flat sense `Σ_γ ∂_γ S_{γb} = 0`
(the time derivatives vanish). -/
structure StationarySource (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (a : ℝ) : Prop where
  /-- The radius is nonnegative. -/
  radius_nonneg : 0 ≤ a
  /-- The components are smooth. -/
  contDiff : ∀ i k, ContDiff ℝ ∞ fun x => S x i k
  /-- The stresses are symmetric. -/
  symm : ∀ x i k, S x i k = S x k i
  /-- The conservation `Σ_γ ∂_γ S_{γb} = 0`. -/
  conserved : ∀ x b, ∑ γ : Fin 3, fderiv ℝ (fun y => S y γ.succ b) x
    (EuclideanSpace.single γ 1) = 0
  /-- The support lies in the ball of radius `a`. -/
  support : ∀ x : E3, a < ‖x‖ → S x = 0

/-- The time-independent stress `T(t, x) = S(x)` on space-time. -/
def staticStress (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (z : Spacetime) : Matrix (Fin 4) (Fin 4) ℝ :=
  S (space z)

theorem space_single_zero : space (Pi.single 0 1 : MinkowskiModel 3) = 0 := by
  have h := congrArg Prod.snd Wave.timeSpaceEquiv_single_zero
  simpa only [Wave.timeSpaceEquiv_apply] using h

theorem space_single_succ (α : Fin 3) :
    space (Pi.single α.succ 1 : MinkowskiModel 3) = EuclideanSpace.single α 1 := by
  have h := congrArg Prod.snd (Wave.timeSpaceEquiv_single_succ α)
  simpa only [Wave.timeSpaceEquiv_apply] using h

/-- The derivative of a static function `z ↦ f(space z)`. -/
theorem fderiv_comp_space {f : E3 → ℝ} {z : Spacetime}
    (hf : DifferentiableAt ℝ f (space z)) (v : Spacetime) :
    fderiv ℝ (fun w => f (space w)) z v = fderiv ℝ f (space z) (space v) := by
  have h := hf.hasFDerivAt.comp z space.hasFDerivAt
  rw [show (fun w => f (space w)) = f ∘ space from rfl, h.fderiv]
  rfl

variable {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ}

namespace StationarySource

/-- The components vanish outside the ball. -/
theorem apply_eq_zero (hS : StationarySource S a) {x : E3} (hx : a < ‖x‖) (i k : Fin 4) :
    S x i k = 0 := by
  rw [hS.support x hx]
  rfl

theorem tsupport_subset (hS : StationarySource S a) (i k : Fin 4) :
    tsupport (fun x => S x i k) ⊆ closedBall 0 a :=
  closure_minimal (fun x hx => by
    by_contra h
    rw [mem_closedBall, dist_zero_right, not_le] at h
    exact hx (hS.apply_eq_zero h i k)) isClosed_closedBall

theorem hasCompactSupport (hS : StationarySource S a) (i k : Fin 4) :
    HasCompactSupport fun x => S x i k :=
  hasCompactSupport_of_tsupport_subset (hS.tsupport_subset i k)

theorem continuous (hS : StationarySource S a) (i k : Fin 4) : Continuous fun x => S x i k :=
  (hS.contDiff i k).continuous

/-- **The static stress of a stationary source is a localized stress tensor.** -/
theorem localizedStress (hS : StationarySource S a) : LocalizedStress (staticStress S) a where
  radius_nonneg := hS.radius_nonneg
  contDiff i k := (hS.contDiff i k).comp space.contDiff
  symm z i k := hS.symm (space z) i k
  conserved z b := by
    have hd (c : Fin 4) : DifferentiableAt ℝ (fun x => S x c b) (space z) :=
      (hS.contDiff c b).differentiable (by simp) _
    simp only [staticStress]
    rw [Fin.sum_univ_succ]
    simp only [fderiv_comp_space (hd _), space_single_zero, map_zero, mul_zero, zero_add,
      space_single_succ, lorentzSign_succ, one_mul]
    exact hS.conserved (space z) b
  support t x hx := by
    simp only [staticStress, space_vector]
    exact hS.support x hx

end StationarySource

/-- **The linearized Einstein equations** `δG_{jk}(h) = κ T_{jk}` for the static source, with
`h = metricPerturbation κ T` in harmonic gauge. -/
theorem linearizedEinstein_static {κ : ℝ} (hS : StationarySource S a) (z : Spacetime)
    (j k : Fin 4) :
    CoordinateMetric.linearizedEinstein .timeNegative (metricPerturbation κ (staticStress S)) z
      j k = κ * staticStress S z j k :=
  linearizedEinstein_retardedPerturbation hS.localizedStress z j k

/-- **The field of a static source is the Newton potential**:
`h̄_{ik}(z) = 2κ N[S_{ik}](space z)`. -/
theorem retardedPerturbation_static (κ : ℝ) (z : Spacetime) (i k : Fin 4) :
    retardedPerturbation κ (staticStress S) z i k =
      2 * κ * newtonPotential (fun x => S x i k) (space z) := by
  rw [retardedPerturbation_apply, retardedScalar_eq, newtonPotential_apply]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [staticStress, map_sub, space_vector, newtonKernel]
  rw [div_eq_inv_mul]

/-! ### Moments from the conservation -/

/-- **The integral of `∇f · V` vanishes for a conserved field `V` of compact support**, by the
divergence theorem on a ball containing the support: `div (f V) = ∇f · V`. -/
theorem integral_fderiv_mul_eq_zero {V : Fin 3 → E3 → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hV : ∀ γ, ContDiff ℝ 1 (V γ)) (hsupp : ∀ γ (y : E3), a < ‖y‖ → V γ y = 0)
    (hdiv : ∀ y, ∑ γ, fderiv ℝ (V γ) y (EuclideanSpace.single γ 1) = 0) {f : E3 → ℝ}
    (hf : ContDiff ℝ 1 f) :
    ∫ y, ∑ γ, fderiv ℝ f y (EuclideanSpace.single γ 1) * V γ y = 0 := by
  set W : Fin 3 → E3 → ℝ := fun γ y => f y * V γ y with hWdef
  have hW (γ : Fin 3) : ContDiffOn ℝ 1 (W γ) univ := (hf.mul (hV γ)).contDiffOn
  have hR : 0 ≤ a + 1 := by linarith
  have h := Sphere.flux_sub_flux isOpen_univ hW le_rfl hR (fun _ _ _ => mem_univ _)
  have hfluxR : Sphere.flux W (a + 1) = 0 := by
    unfold Sphere.flux
    have hz (n : sphere (0 : E3) 1) :
        (a + 1) ^ 2 * ∑ α, W α ((a + 1) • (n : E3)) * (n : E3) α = 0 := by
      have hn : a < ‖(a + 1) • (n : E3)‖ := by
        rw [norm_smul, norm_eq_of_mem_sphere n, mul_one, Real.norm_eq_abs, abs_of_nonneg hR]
        linarith
      simp [hWdef, hsupp _ _ hn]
    simp [hz]
  rw [hfluxR, Sphere.flux_zero, sub_zero, setIntegral_congr_set (Sphere.shell_zero_ae_eq _)] at h
  have hpt (y : E3) : Sphere.divergence W y =
      ∑ γ, fderiv ℝ f y (EuclideanSpace.single γ 1) * V γ y := by
    unfold Sphere.divergence
    have hγ (γ : Fin 3) : fderiv ℝ (W γ) y (EuclideanSpace.single γ 1) =
        f y * fderiv ℝ (V γ) y (EuclideanSpace.single γ 1) +
          fderiv ℝ f y (EuclideanSpace.single γ 1) * V γ y := by
      rw [show W γ = fun y => f y * V γ y from rfl,
        fderiv_fun_mul (hf.differentiable one_ne_zero y) ((hV γ).differentiable one_ne_zero y)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    simp only [hγ, Finset.sum_add_distrib, ← Finset.mul_sum, hdiv y, mul_zero, zero_add]
  simp only [hpt] at h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at h
  · exact h.symm
  · intro y hy
    have hy' : a < ‖y‖ := by
      rw [mem_ball_zero_iff, not_lt] at hy
      linarith
    simp [hsupp _ _ hy']

/-- The derivative of a co-ordinate: `∂_γ y_α = δ_{γα}`. -/
theorem fderiv_coord (y : E3) (α γ : Fin 3) :
    fderiv ℝ (fun y : E3 => y α) y (EuclideanSpace.single γ 1) = if γ = α then 1 else 0 := by
  have h : (fun y : E3 => y α) = (EuclideanSpace.proj α : E3 →L[ℝ] ℝ) := rfl
  rw [h, ContinuousLinearMap.fderiv]
  by_cases hγ : γ = α
  · subst hγ
    simp
  · simp [hγ, Ne.symm hγ]

theorem contDiff_coord {n : WithTop ℕ∞} (α : Fin 3) : ContDiff ℝ n fun y : E3 => y α :=
  (EuclideanSpace.proj α : E3 →L[ℝ] ℝ).contDiff

/-- The derivative of a product of co-ordinates: `∂_γ (y_α y_β) = δ_{γα} y_β + y_α δ_{γβ}`. -/
theorem fderiv_coord_mul_coord (y : E3) (α β γ : Fin 3) :
    fderiv ℝ (fun y : E3 => y α * y β) y (EuclideanSpace.single γ 1) =
      (if γ = α then 1 else 0) * y β + y α * (if γ = β then 1 else 0) := by
  rw [fderiv_fun_mul ((contDiff_coord (n := 1) α).differentiable one_ne_zero y)
    ((contDiff_coord (n := 1) β).differentiable one_ne_zero y)]
  simp only [add_apply, smul_apply, smul_eq_mul, fderiv_coord]
  ring

namespace StationarySource

theorem integrable (hS : StationarySource S a) (i k : Fin 4) : Integrable fun x => S x i k :=
  (hS.continuous i k).integrable_of_hasCompactSupport (hS.hasCompactSupport i k)

theorem integrable_mul_coord (hS : StationarySource S a) (i k : Fin 4) (β : Fin 3) :
    Integrable fun x : E3 => S x i k * x β :=
  ((hS.continuous i k).mul (contDiff_coord (n := 0) β).continuous).integrable_of_hasCompactSupport
    ((hS.hasCompactSupport i k).mul_right)

/-- The identity `∫ ∇f · S_{·b} = 0` of a stationary source. -/
theorem integral_fderiv_mul (hS : StationarySource S a) (b : Fin 4) {f : E3 → ℝ}
    (hf : ContDiff ℝ 1 f) :
    ∫ y, ∑ γ : Fin 3, fderiv ℝ f y (EuclideanSpace.single γ 1) * S y γ.succ b = 0 :=
  integral_fderiv_mul_eq_zero hS.radius_nonneg (V := fun γ y => S y γ.succ b)
    (fun γ => (hS.contDiff _ _).of_le (by simp)) (fun γ y hy => hS.apply_eq_zero hy _ _)
    (fun y => hS.conserved y b) hf

/-- **The momentum of a stationary source vanishes**: `∫ S_{0α} = 0`. -/
theorem integral_momentum_eq_zero (hS : StationarySource S a) (α : Fin 3) :
    ∫ y, S y 0 α.succ = 0 := by
  have h := hS.integral_fderiv_mul 0 (contDiff_coord α)
  simp only [fderiv_coord, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at h
  simpa [hS.symm _ α.succ 0] using h

/-- **The stresses of a stationary source integrate to zero**: `∫ S_{αβ} = 0`. -/
theorem integral_stress_eq_zero (hS : StationarySource S a) (α β : Fin 3) :
    ∫ y, S y α.succ β.succ = 0 := by
  have h := hS.integral_fderiv_mul β.succ (contDiff_coord α)
  simpa only [fderiv_coord, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] using h

/-- The identity `∫ (y_β S_{αb} + y_α S_{βb}) = 0`. -/
theorem integral_coord_mul_add (hS : StationarySource S a) (b : Fin 4) (α β : Fin 3) :
    (∫ y, S y α.succ b * y β) + ∫ y, S y β.succ b * y α = 0 := by
  have h := hS.integral_fderiv_mul b ((contDiff_coord α).mul (contDiff_coord β))
  simp only [fderiv_coord_mul_coord, add_mul, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
  have e : (fun y : E3 => y β * S y α.succ b + y α * S y β.succ b) =
      fun y => S y α.succ b * y β + S y β.succ b * y α := funext fun y => by ring
  rw [e, integral_add (hS.integrable_mul_coord _ _ β) (hS.integrable_mul_coord _ _ α)] at h
  exact h

end StationarySource

/-- The mass `M = ∫ S₀₀` of the source. -/
def massOf (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) : ℝ := ∫ y, S y 0 0

/-- The current dipole `d_{αβ} = ∫ S_{0α} y_β`. -/
def currentDipole (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (α β : Fin 3) : ℝ :=
  ∫ y, S y 0 α.succ * y β

/-- The angular momentum `J_{αβ} = ∫ (y_α S_{0β} − y_β S_{0α})`. -/
def angularMomentum (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (α β : Fin 3) : ℝ :=
  ∫ y, (y α * S y 0 β.succ - y β * S y 0 α.succ)

/-- The stress dipole `X_{γαβ} = ∫ y_γ S_{αβ}`. -/
def stressDipole (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (γ α β : Fin 3) : ℝ :=
  ∫ y, S y α.succ β.succ * y γ

namespace StationarySource

/-- **The current dipole is antisymmetric**: `d_{αβ} = −d_{βα}`. -/
theorem currentDipole_antisymm (hS : StationarySource S a) (α β : Fin 3) :
    currentDipole S α β = -currentDipole S β α := by
  have h := hS.integral_coord_mul_add 0 α β
  simp only [currentDipole]
  have e1 : ∫ y, S y 0 α.succ * y β = ∫ y, S y α.succ 0 * y β :=
    integral_congr_ae (Eventually.of_forall fun y => by dsimp only; rw [hS.symm y 0 α.succ])
  have e2 : ∫ y, S y 0 β.succ * y α = ∫ y, S y β.succ 0 * y α :=
    integral_congr_ae (Eventually.of_forall fun y => by dsimp only; rw [hS.symm y 0 β.succ])
  rw [e1, e2]
  linarith

/-- The current dipole is half the angular momentum: `d_{αβ} = −J_{αβ}/2`. -/
theorem currentDipole_eq (hS : StationarySource S a) (α β : Fin 3) :
    currentDipole S α β = -(angularMomentum S α β / 2) := by
  have h := hS.currentDipole_antisymm α β
  have hJ : angularMomentum S α β = currentDipole S β α - currentDipole S α β := by
    rw [angularMomentum, integral_sub]
    · simp only [currentDipole]
      congr 1 <;> exact integral_congr_ae (Eventually.of_forall fun y => by ring)
    · exact (hS.integrable_mul_coord 0 β.succ α).congr (Eventually.of_forall fun y => by ring)
    · exact (hS.integrable_mul_coord 0 α.succ β).congr (Eventually.of_forall fun y => by ring)
  rw [hJ]
  linarith

/-- **The stress dipole of a stationary source vanishes**: `∫ y_γ S_{αβ} = 0`. -/
theorem stressDipole_eq_zero (hS : StationarySource S a) (γ α β : Fin 3) :
    stressDipole S γ α β = 0 := by
  -- antisymmetric in the first two indices, symmetric in the last two
  have hA (p q r : Fin 3) : stressDipole S p q r = -stressDipole S q p r := by
    have h := hS.integral_coord_mul_add r.succ q p
    simp only [stressDipole]
    linarith
  have hS' (p q r : Fin 3) : stressDipole S p q r = stressDipole S p r q :=
    integral_congr_ae (Eventually.of_forall fun y => by dsimp only; rw [hS.symm y q.succ r.succ])
  have h1 := hA γ α β
  have h2 := hS' α γ β
  have h3 := hA α β γ
  have h4 := hS' β α γ
  have h5 := hA β γ α
  have h6 := hS' γ β α
  linarith

end StationarySource

/-! ### The far field -/

/-- The moment `∫ |S_{ik}| ‖y‖²` that bounds the remainders. -/
def secondAbsMoment (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (i k : Fin 4) : ℝ :=
  ∫ y, |S y i k| * ‖y‖ ^ 2

/-- The dipole moment of a component in the co-ordinates: `⟪d, x⟫ = Σ_β x_β ∫ S_{ik} y_β`. -/
theorem inner_dipoleMoment_eq (hS : StationarySource S a) (i k : Fin 4) (x : E3) :
    ⟪dipoleMoment (fun y => S y i k), x⟫ = ∑ β : Fin 3, x β * ∫ y, S y i k * y β := by
  rw [inner_dipoleMoment (hS.continuous i k) (hS.hasCompactSupport i k)]
  have hpt (y : E3) : S y i k * ⟪x, y⟫ = ∑ β : Fin 3, x β * (S y i k * y β) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ fun β _ => (hS.integrable_mul_coord i k β).const_mul _]
  exact Finset.sum_congr rfl fun β _ => integral_const_mul _ _

/-- The dipole expansion of the field component `h̄_{ik} = 2κ N[S_{ik}]`. -/
theorem abs_hbar_sub_le (hS : StationarySource S a) (κ : ℝ) {z : Spacetime}
    (hz : a < ‖space z‖) (i k : Fin 4) :
    |retardedPerturbation κ (staticStress S) z i k -
        2 * κ * ((∫ y, S y i k) / (4 * π * ‖space z‖)) -
        2 * κ * ((∑ β : Fin 3, space z β * ∫ y, S y i k * y β) / (4 * π * ‖space z‖ ^ 3))| ≤
      2 * |κ| * (secondAbsMoment S i k / (4 * π * (‖space z‖ - a) ^ 3)) := by
  have h := abs_newtonPotential_sub_dipole_le (hS.continuous i k) (hS.tsupport_subset i k) hz
  rw [inner_dipoleMoment_eq hS] at h
  rw [retardedPerturbation_static, ← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **The mass monopole**: for a mass-centred source, `h̄₀₀ = 2κM/(4πr) + O(r⁻³)` uniformly on
`r = ‖x‖ > a`. -/
theorem abs_hbar_zero_zero_sub_le (hS : StationarySource S a)
    (hc : ∀ β : Fin 3, ∫ y, S y 0 0 * y β = 0) (κ : ℝ) {z : Spacetime} (hz : a < ‖space z‖) :
    |retardedPerturbation κ (staticStress S) z 0 0 - 2 * κ * massOf S / (4 * π * ‖space z‖)| ≤
      2 * |κ| * (secondAbsMoment S 0 0 / (4 * π * (‖space z‖ - a) ^ 3)) := by
  have h := abs_hbar_sub_le hS κ hz 0 0
  simp only [hc, mul_zero, Finset.sum_const_zero, zero_div, sub_zero] at h
  rw [massOf, mul_div_assoc]
  exact h

/-- **The current dipole**: `h̄_{0α} = 2κ Σ_β d_{αβ} x_β/(4πr³) + O(r⁻³)`, the monopole
`∫ S_{0α}` being zero. -/
theorem abs_hbar_zero_succ_sub_le (hS : StationarySource S a) (κ : ℝ) {z : Spacetime}
    (hz : a < ‖space z‖) (α : Fin 3) :
    |retardedPerturbation κ (staticStress S) z 0 α.succ -
        2 * κ * ((∑ β : Fin 3, currentDipole S α β * space z β) / (4 * π * ‖space z‖ ^ 3))| ≤
      2 * |κ| * (secondAbsMoment S 0 α.succ / (4 * π * (‖space z‖ - a) ^ 3)) := by
  have h := abs_hbar_sub_le hS κ hz 0 α.succ
  rw [hS.integral_momentum_eq_zero α, zero_div, mul_zero, sub_zero] at h
  have he : ∑ β : Fin 3, space z β * ∫ y, S y 0 α.succ * y β =
      ∑ β : Fin 3, currentDipole S α β * space z β :=
    Finset.sum_congr rfl fun β _ => mul_comm _ _
  rwa [he] at h

/-- **The stresses**: `h̄_{αβ} = O(r⁻³)`, since their monopole and dipole vanish. -/
theorem abs_hbar_succ_succ_le (hS : StationarySource S a) (κ : ℝ) {z : Spacetime}
    (hz : a < ‖space z‖) (α β : Fin 3) :
    |retardedPerturbation κ (staticStress S) z α.succ β.succ| ≤
      2 * |κ| * (secondAbsMoment S α.succ β.succ / (4 * π * (‖space z‖ - a) ^ 3)) := by
  have h := abs_hbar_sub_le hS κ hz α.succ β.succ
  have hd : ∀ γ : Fin 3, ∫ y, S y α.succ β.succ * y γ = 0 := fun γ =>
    hS.stressDipole_eq_zero γ α β
  simp only [hS.integral_stress_eq_zero α β, hd, mul_zero, Finset.sum_const_zero, zero_div,
    sub_zero] at h
  exact h

/-! ### The metric perturbation -/

variable {T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ}

theorem metricPerturbation_zero_zero (κ : ℝ) (z : Spacetime) :
    metricPerturbation κ T z 0 0 = (retardedPerturbation κ T z 0 0 +
      ∑ γ : Fin 3, retardedPerturbation κ T z γ.succ γ.succ) / 2 := by
  rw [metricPerturbation, CoordinateMetric.traceReverse_apply, CoordinateMetric.metricMatrix_apply]
  simp [CoordinateMetric.flatTrace, Fin.sum_univ_succ (n := 3), lorentzSign,
    LorentzConvention.timeSign]
  ring

theorem metricPerturbation_zero_succ (κ : ℝ) (z : Spacetime) (α : Fin 3) :
    metricPerturbation κ T z 0 α.succ = retardedPerturbation κ T z 0 α.succ := by
  rw [metricPerturbation, CoordinateMetric.traceReverse_apply, CoordinateMetric.metricMatrix_apply]
  simp [(Fin.succ_ne_zero α).symm]

theorem metricPerturbation_succ_succ (κ : ℝ) (z : Spacetime) (α β : Fin 3) :
    metricPerturbation κ T z α.succ β.succ = retardedPerturbation κ T z α.succ β.succ -
      (if α = β then (-retardedPerturbation κ T z 0 0 +
        ∑ γ : Fin 3, retardedPerturbation κ T z γ.succ γ.succ) / 2 else 0) := by
  rw [metricPerturbation, CoordinateMetric.traceReverse_apply, CoordinateMetric.metricMatrix_apply]
  by_cases h : α = β
  · subst h
    simp [CoordinateMetric.flatTrace, Fin.sum_univ_succ (n := 3), lorentzSign,
      LorentzConvention.timeSign, Fin.succ_ne_zero]
  · simp [h]

/-- **`h₀₀ = κM/(4πr) + O(r⁻³)`** for a mass-centred source; with `κ = 8π`, `g₀₀ = −1 + 2M/r`. -/
theorem abs_metricPerturbation_zero_zero_sub_le (hS : StationarySource S a)
    (hc : ∀ β : Fin 3, ∫ y, S y 0 0 * y β = 0) (κ : ℝ) {z : Spacetime} (hz : a < ‖space z‖) :
    |metricPerturbation κ (staticStress S) z 0 0 - κ * massOf S / (4 * π * ‖space z‖)| ≤
      |κ| * ((secondAbsMoment S 0 0 + ∑ γ : Fin 3, secondAbsMoment S γ.succ γ.succ) /
        (4 * π * (‖space z‖ - a) ^ 3)) := by
  have h0 := abs_hbar_zero_zero_sub_le hS hc κ hz
  have hs := fun γ : Fin 3 => abs_hbar_succ_succ_le hS κ hz γ γ
  rw [metricPerturbation_zero_zero]
  have heq : (retardedPerturbation κ (staticStress S) z 0 0 +
      ∑ γ : Fin 3, retardedPerturbation κ (staticStress S) z γ.succ γ.succ) / 2 -
        κ * massOf S / (4 * π * ‖space z‖) =
      (retardedPerturbation κ (staticStress S) z 0 0 - 2 * κ * massOf S / (4 * π * ‖space z‖)) /
        2 + (∑ γ : Fin 3, retardedPerturbation κ (staticStress S) z γ.succ γ.succ) / 2 := by ring
  rw [heq]
  have hsum := (Finset.abs_sum_le_sum_abs (fun γ : Fin 3 =>
    retardedPerturbation κ (staticStress S) z γ.succ γ.succ) Finset.univ).trans
    (Finset.sum_le_sum fun γ _ => hs γ)
  calc _ ≤ |(retardedPerturbation κ (staticStress S) z 0 0 -
          2 * κ * massOf S / (4 * π * ‖space z‖)) / 2| +
        |(∑ γ : Fin 3, retardedPerturbation κ (staticStress S) z γ.succ γ.succ) / 2| :=
        abs_add_le _ _
    _ ≤ 2 * |κ| * (secondAbsMoment S 0 0 / (4 * π * (‖space z‖ - a) ^ 3)) / 2 +
        (∑ γ : Fin 3, 2 * |κ| * (secondAbsMoment S γ.succ γ.succ /
          (4 * π * (‖space z‖ - a) ^ 3))) / 2 := by
        rw [abs_div, abs_div, abs_two]
        gcongr
    _ = _ := by
        rw [← Finset.mul_sum, ← Finset.sum_div]
        ring

/-- **`h_{αβ} = δ_{αβ} κM/(4πr) + O(r⁻³)`** for a mass-centred source; with `κ = 8π`,
`g_{αβ} = (1 + 2M/r) δ_{αβ}`. -/
theorem abs_metricPerturbation_succ_succ_sub_le (hS : StationarySource S a)
    (hc : ∀ β : Fin 3, ∫ y, S y 0 0 * y β = 0) (κ : ℝ) {z : Spacetime} (hz : a < ‖space z‖)
    (α β : Fin 3) :
    |metricPerturbation κ (staticStress S) z α.succ β.succ -
        (if α = β then κ * massOf S / (4 * π * ‖space z‖) else 0)| ≤
      |κ| * ((2 * secondAbsMoment S α.succ β.succ + secondAbsMoment S 0 0 +
        ∑ γ : Fin 3, secondAbsMoment S γ.succ γ.succ) / (4 * π * (‖space z‖ - a) ^ 3)) := by
  have h0 := abs_hbar_zero_zero_sub_le hS hc κ hz
  have hab := abs_hbar_succ_succ_le hS κ hz α β
  have hs := fun γ : Fin 3 => abs_hbar_succ_succ_le hS κ hz γ γ
  have hd : 0 < 4 * π * (‖space z‖ - a) ^ 3 := by
    have : 0 < ‖space z‖ - a := by linarith
    positivity
  have hE (i k : Fin 4) : 0 ≤ secondAbsMoment S i k :=
    integral_nonneg fun y => by positivity
  rw [metricPerturbation_succ_succ]
  have hsum := (Finset.abs_sum_le_sum_abs (fun γ : Fin 3 =>
    retardedPerturbation κ (staticStress S) z γ.succ γ.succ) Finset.univ).trans
    (Finset.sum_le_sum fun γ _ => hs γ)
  rw [← Finset.mul_sum, ← Finset.sum_div] at hsum
  by_cases h : α = β
  · subst h
    simp only [↓reduceIte]
    have heq : retardedPerturbation κ (staticStress S) z α.succ α.succ -
        (-retardedPerturbation κ (staticStress S) z 0 0 +
          ∑ γ : Fin 3, retardedPerturbation κ (staticStress S) z γ.succ γ.succ) / 2 -
        κ * massOf S / (4 * π * ‖space z‖) =
        retardedPerturbation κ (staticStress S) z α.succ α.succ +
          (retardedPerturbation κ (staticStress S) z 0 0 -
            2 * κ * massOf S / (4 * π * ‖space z‖)) / 2 -
          (∑ γ : Fin 3, retardedPerturbation κ (staticStress S) z γ.succ γ.succ) / 2 := by ring
    rw [heq]
    calc _ ≤ |retardedPerturbation κ (staticStress S) z α.succ α.succ| +
          |(retardedPerturbation κ (staticStress S) z 0 0 -
            2 * κ * massOf S / (4 * π * ‖space z‖)) / 2| +
          |(∑ γ : Fin 3, retardedPerturbation κ (staticStress S) z γ.succ γ.succ) / 2| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 2 * |κ| * (secondAbsMoment S α.succ α.succ / (4 * π * (‖space z‖ - a) ^ 3)) +
          2 * |κ| * (secondAbsMoment S 0 0 / (4 * π * (‖space z‖ - a) ^ 3)) / 2 +
          2 * |κ| * ((∑ γ : Fin 3, secondAbsMoment S γ.succ γ.succ) /
            (4 * π * (‖space z‖ - a) ^ 3)) / 2 := by
          rw [abs_div, abs_div, abs_two]
          exact add_le_add (add_le_add hab (div_le_div_of_nonneg_right h0 zero_le_two))
            (div_le_div_of_nonneg_right hsum zero_le_two)
      _ = _ := by ring
  · simp only [h, ↓reduceIte, sub_zero]
    refine hab.trans ?_
    have h1 : 0 ≤ secondAbsMoment S 0 0 + ∑ γ : Fin 3, secondAbsMoment S γ.succ γ.succ :=
      add_nonneg (hE 0 0) (Finset.sum_nonneg fun (γ : Fin 3) _ => hE γ.succ γ.succ)
    have h2 : 2 * |κ| * (secondAbsMoment S α.succ β.succ / (4 * π * (‖space z‖ - a) ^ 3)) =
        |κ| * (2 * secondAbsMoment S α.succ β.succ / (4 * π * (‖space z‖ - a) ^ 3)) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hd.le)
      (abs_nonneg κ)

/-- **The current dipole in the angular momentum**: `h̄_{0α} = −(κ/4π) Σ_β J_{αβ} x_β/r³ + O(r⁻³)`;
with `κ = 8π`, `g_{0α} = −2 J_{αβ} x_β/r³`. -/
theorem abs_hbar_zero_succ_sub_angularMomentum_le (hS : StationarySource S a) (κ : ℝ)
    {z : Spacetime} (hz : a < ‖space z‖) (α : Fin 3) :
    |retardedPerturbation κ (staticStress S) z 0 α.succ +
        κ * (∑ β : Fin 3, angularMomentum S α β * space z β) / (4 * π * ‖space z‖ ^ 3)| ≤
      2 * |κ| * (secondAbsMoment S 0 α.succ / (4 * π * (‖space z‖ - a) ^ 3)) := by
  have h := abs_hbar_zero_succ_sub_le hS κ hz α
  have he : 2 * κ * ((∑ β : Fin 3, currentDipole S α β * space z β) / (4 * π * ‖space z‖ ^ 3)) =
      -(κ * (∑ β : Fin 3, angularMomentum S α β * space z β) / (4 * π * ‖space z‖ ^ 3)) := by
    simp only [hS.currentDipole_eq]
    rw [show ∑ β : Fin 3, -(angularMomentum S α β / 2) * space z β =
      -((∑ β : Fin 3, angularMomentum S α β * space z β) / 2) by
        rw [Finset.sum_div, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun β _ => by ring]
    ring
  rwa [he, sub_neg_eq_add] at h

/-! ### The surface integrals -/

theorem contDiff_potential (hS : StationarySource S a) (i k : Fin 4) :
    ContDiff ℝ 3 (newtonPotential fun x => S x i k) := by
  have h := contDiff_newtonPotential (n := 3) (hS.hasCompactSupport i k)
    ((hS.contDiff i k).of_le (by simp))
  exact_mod_cast h

/-- `Δ (c f) = c Δ f`. -/
theorem coordLaplacian_const_mul {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x : E3) :
    coordLaplacian (fun y => c * f y) x = c * coordLaplacian f x := by
  unfold coordLaplacian
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun y => fderiv ℝ (fun y => c * f y) y (EuclideanSpace.single i 1)) =
      fun y => c * fderiv ℝ f y (EuclideanSpace.single i 1) := funext fun y => by
    rw [fderiv_const_mul (hf.differentiable (by simp) y), smul_apply, smul_eq_mul]
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by simp) x
  rw [h1, fderiv_const_mul hd, smul_apply, smul_eq_mul]

/-- **Poisson's equation for the field**: `Δ(2κ N[S_{ik}]) = −2κ S_{ik}`. -/
theorem coordLaplacian_field (hS : StationarySource S a) (κ : ℝ) (i k : Fin 4) (x : E3) :
    coordLaplacian (fun y => 2 * κ * newtonPotential (fun x => S x i k) y) x =
      -(2 * κ * S x i k) := by
  have hφ := contDiff_potential hS i k
  rw [coordLaplacian_const_mul (hφ.of_le (by norm_num)),
    coordLaplacian_eq_laplacian ((hφ.of_le (by norm_num)).contDiffAt),
    laplacian_newtonPotential (hS.hasCompactSupport i k) ((hS.contDiff i k).of_le (by simp))]
  ring

/-- The field on the slice `x⁰ = t` is the Newton potential. -/
theorem field_slice (κ : ℝ) (t : ℝ) (i k : Fin 4) :
    (fun y => retardedPerturbation κ (staticStress S) (vector t y) i k) =
      fun y => 2 * κ * newtonPotential (fun x => S x i k) y :=
  funext fun y => by rw [retardedPerturbation_static, space_vector]

/-- The integral of a function supported in the closed ball of radius `a` over the shell
`0 < ‖y‖ < R`, `R > a`, is its integral over space. -/
theorem integral_shell_eq {f : E3 → ℝ} (hf : ∀ y : E3, a < ‖y‖ → f y = 0) {R : ℝ}
    (hR : a < R) : ∫ y in Sphere.shell 0 R, f y = ∫ y, f y := by
  rw [setIntegral_congr_set (Sphere.shell_zero_ae_eq R)]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => hf y ?_
  rw [mem_ball_zero_iff, not_lt] at hy
  linarith

/-- The flux `∮ ∇h̄₀₀ · n dA` through the sphere of radius `R` in the slice `x⁰ = t`. -/
def massFlux (κ : ℝ) (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (t R : ℝ) : ℝ :=
  Sphere.flux (fun γ x => fderiv ℝ (fun y => retardedPerturbation κ (staticStress S) (vector t y)
    0 0) x (EuclideanSpace.single γ 1)) R

/-- **The mass is the surface integral**: beyond the source, `∮ ∇h̄₀₀ · n dA = −2κM` exactly. -/
theorem massFlux_eq (hS : StationarySource S a) (κ t : ℝ) {R : ℝ} (hR : a < R) :
    massFlux κ S t R = -(2 * κ * massOf S) := by
  have hφ := contDiff_potential hS 0 0
  have hR0 : 0 ≤ R := hS.radius_nonneg.trans hR.le
  rw [massFlux, field_slice]
  have hV (γ : Fin 3) : ContDiffOn ℝ 1 (fun x => fderiv ℝ (fun y => 2 * κ *
      newtonPotential (fun x => S x 0 0) y) x (EuclideanSpace.single γ 1)) univ :=
    (((contDiff_const.mul hφ).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const).contDiffOn
  have h := Sphere.flux_sub_flux isOpen_univ hV le_rfl hR0 (fun _ _ _ => mem_univ _)
  rw [Sphere.flux_zero, sub_zero] at h
  rw [h]
  have hdiv (x : E3) : Sphere.divergence (fun γ x => fderiv ℝ (fun y => 2 * κ *
      newtonPotential (fun x => S x 0 0) y) x (EuclideanSpace.single γ 1)) x =
      -(2 * κ * S x 0 0) := coordLaplacian_field hS κ 0 0 x
  simp only [hdiv]
  rw [integral_shell_eq (a := a) (fun y hy => by rw [hS.apply_eq_zero hy, mul_zero, neg_zero]) hR,
    integral_neg, integral_const_mul, massOf]

/-- The field `h̄_{0δ}` on the slice `x⁰ = t`. -/
def momentumPotential (κ : ℝ) (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (δ : Fin 3)
    (y : E3) : ℝ :=
  retardedPerturbation κ (staticStress S) (vector t y) 0 δ.succ

/-- The flux of `x_α ∇h̄_{0β} − x_β ∇h̄_{0α} − e_α h̄_{0β} + e_β h̄_{0α}` through the sphere of
radius `R` in the slice `x⁰ = t`. -/
def angularMomentumFlux (κ : ℝ) (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (α β : Fin 3)
    (R : ℝ) : ℝ :=
  Sphere.flux (fun γ x => x α * fderiv ℝ (momentumPotential κ S t β) x (EuclideanSpace.single γ 1)
    - x β * fderiv ℝ (momentumPotential κ S t α) x (EuclideanSpace.single γ 1)
    - (if γ = α then 1 else 0) * momentumPotential κ S t β x
    + (if γ = β then 1 else 0) * momentumPotential κ S t α x) R

/-- **The angular momentum is the surface integral**: beyond the source,
`∮ (x_α ∇h̄_{0β} − x_β ∇h̄_{0α} − e_α h̄_{0β} + e_β h̄_{0α}) · n dA = −2κ J_{αβ}` exactly. -/
theorem angularMomentumFlux_eq (hS : StationarySource S a) (κ t : ℝ) (α β : Fin 3) {R : ℝ}
    (hR : a < R) : angularMomentumFlux κ S t α β R = -(2 * κ * angularMomentum S α β) := by
  have hR0 : 0 ≤ R := hS.radius_nonneg.trans hR.le
  have hψ (δ : Fin 3) : momentumPotential κ S t δ =
      fun y => 2 * κ * newtonPotential (fun x => S x 0 δ.succ) y := field_slice κ t 0 δ.succ
  have hc (δ : Fin 3) : ContDiff ℝ 3 (momentumPotential κ S t δ) := by
    rw [hψ]
    exact contDiff_const.mul (contDiff_potential hS 0 δ.succ)
  have hd1 (δ : Fin 3) (x : E3) : DifferentiableAt ℝ (momentumPotential κ S t δ) x :=
    (hc δ).differentiable (by norm_num) x
  have hd2 (δ γ : Fin 3) (x : E3) : DifferentiableAt ℝ
      (fun y => fderiv ℝ (momentumPotential κ S t δ) y (EuclideanSpace.single γ 1)) x :=
    (((hc δ).fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num) x
  have hcoord (δ : Fin 3) (x : E3) : DifferentiableAt ℝ (fun y : E3 => y δ) x :=
    (contDiff_coord (n := 1) δ).differentiable one_ne_zero x
  have hV (γ : Fin 3) : ContDiffOn ℝ 1 (fun x => x α * fderiv ℝ (momentumPotential κ S t β) x
      (EuclideanSpace.single γ 1) - x β * fderiv ℝ (momentumPotential κ S t α) x
        (EuclideanSpace.single γ 1) - (if γ = α then 1 else 0) * momentumPotential κ S t β x +
      (if γ = β then 1 else 0) * momentumPotential κ S t α x) univ := by
    refine ContDiff.contDiffOn ?_
    refine (((contDiff_coord α).mul ?_).sub ((contDiff_coord β).mul ?_)).sub
      (contDiff_const.mul ((hc β).of_le (by norm_num))) |>.add
        (contDiff_const.mul ((hc α).of_le (by norm_num)))
    · exact ((hc β).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    · exact ((hc α).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h := Sphere.flux_sub_flux isOpen_univ hV le_rfl hR0 (fun _ _ _ => mem_univ _)
  rw [Sphere.flux_zero, sub_zero] at h
  rw [angularMomentumFlux, h]
  have hdiv (x : E3) : Sphere.divergence (fun γ x => x α * fderiv ℝ (momentumPotential κ S t β) x
      (EuclideanSpace.single γ 1) - x β * fderiv ℝ (momentumPotential κ S t α) x
        (EuclideanSpace.single γ 1) - (if γ = α then 1 else 0) * momentumPotential κ S t β x +
      (if γ = β then 1 else 0) * momentumPotential κ S t α x) x =
      x α * coordLaplacian (momentumPotential κ S t β) x -
        x β * coordLaplacian (momentumPotential κ S t α) x := by
    unfold Sphere.divergence coordLaplacian
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hγ : HasFDerivAt (fun x : E3 => x α * fderiv ℝ (momentumPotential κ S t β) x
        (EuclideanSpace.single γ 1) - x β * fderiv ℝ (momentumPotential κ S t α) x
          (EuclideanSpace.single γ 1) - (if γ = α then 1 else 0) * momentumPotential κ S t β x +
        (if γ = β then 1 else 0) * momentumPotential κ S t α x) _ x :=
      (((((hcoord α x).hasFDerivAt.mul (hd2 β γ x).hasFDerivAt).sub
        ((hcoord β x).hasFDerivAt.mul (hd2 α γ x).hasFDerivAt)).sub
          ((hd1 β x).hasFDerivAt.const_mul _)).add ((hd1 α x).hasFDerivAt.const_mul _))
    beta_reduce
    rw [hγ.fderiv]
    have hc1 := fderiv_coord x α γ
    have hc2 := fderiv_coord x β γ
    rw [← (hcoord α x).hasFDerivAt.fderiv, ← (hcoord β x).hasFDerivAt.fderiv]
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, hc1, hc2]
    ring
  have hlap (δ : Fin 3) (x : E3) : coordLaplacian (momentumPotential κ S t δ) x =
      -(2 * κ * S x 0 δ.succ) := by
    rw [hψ]
    exact coordLaplacian_field hS κ 0 δ.succ x
  simp only [hdiv, hlap]
  rw [integral_shell_eq (a := a) (fun y hy => by simp [hS.apply_eq_zero hy]) hR, angularMomentum,
    ← integral_const_mul, ← integral_neg]
  congr 1
  funext y
  ring

/-! ### Comparison with the Kerr exterior -/

/-- **The zero-spin limit**: `g_tφ = 0` for `a = 0`. -/
theorem gtp_zero_spin (M r c : ℝ) : Kerr.gtp M 0 r c = 0 := by
  simp [Kerr.gtp]

theorem sig_pos {a r c : ℝ} (hr : 0 < r) : 0 < Kerr.sig a r c := by
  unfold Kerr.sig
  positivity

theorem sq_le_sig (a r c : ℝ) : r ^ 2 ≤ Kerr.sig a r c := by
  unfold Kerr.sig
  nlinarith [sq_nonneg (a * c)]

/-- **The leading spin term of Kerr**: `|g_tφ + 2Ma(1 − χ²)/r| ≤ 2|M||a|³/r³`. -/
theorem abs_gtp_add_le {M a r c : ℝ} (hr : 0 < r) (hc : c ^ 2 ≤ 1) :
    |Kerr.gtp M a r c + 2 * M * a * (1 - c ^ 2) / r| ≤ 2 * |M| * |a| ^ 3 / r ^ 3 := by
  have hS := sig_pos (a := a) (c := c) hr
  have heq : Kerr.gtp M a r c + 2 * M * a * (1 - c ^ 2) / r =
      2 * M * a * ((1 - c ^ 2) * (a ^ 2 * c ^ 2)) / (r * Kerr.sig a r c) := by
    unfold Kerr.gtp
    field_simp
    unfold Kerr.sig
    ring
  have h1 : 0 ≤ 1 - c ^ 2 := by linarith
  have hnum : |2 * M * a * ((1 - c ^ 2) * (a ^ 2 * c ^ 2))| ≤ 2 * |M| * |a| ^ 3 := by
    rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg (by positivity :
      0 ≤ (1 - c ^ 2) * (a ^ 2 * c ^ 2))]
    have h2 : (1 - c ^ 2) * (a ^ 2 * c ^ 2) ≤ |a| ^ 2 := by
      rw [sq_abs]
      nlinarith [sq_nonneg c, sq_nonneg a, mul_nonneg (sq_nonneg a) (sq_nonneg c)]
    calc 2 * |M| * |a| * ((1 - c ^ 2) * (a ^ 2 * c ^ 2)) ≤ 2 * |M| * |a| * |a| ^ 2 := by gcongr
      _ = 2 * |M| * |a| ^ 3 := by ring
  rw [heq, abs_div, abs_of_pos (by positivity : 0 < r * Kerr.sig a r c)]
  calc _ ≤ 2 * |M| * |a| ^ 3 / (r * Kerr.sig a r c) := div_le_div_of_nonneg_right hnum (by
        positivity)
    _ ≤ 2 * |M| * |a| ^ 3 / r ^ 3 := by
        gcongr
        calc r ^ 3 = r * r ^ 2 := by ring
          _ ≤ r * Kerr.sig a r c := by gcongr; exact sq_le_sig a r c

/-- **The leading mass term of Kerr**: `|g_tt + 1 − 2M/r| ≤ 2|M|a²/r³`. -/
theorem abs_gtt_add_le {M a r c : ℝ} (hr : 0 < r) (hc : c ^ 2 ≤ 1) :
    |Kerr.gtt M a r c + 1 - 2 * M / r| ≤ 2 * |M| * a ^ 2 / r ^ 3 := by
  have hS := sig_pos (a := a) (c := c) hr
  have heq : Kerr.gtt M a r c + 1 - 2 * M / r = -(2 * M * (a ^ 2 * c ^ 2)) /
      (r * Kerr.sig a r c) := by
    unfold Kerr.gtt
    field_simp
    unfold Kerr.sig
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos (by positivity : 0 < r * Kerr.sig a r c), abs_mul,
    abs_mul, abs_two, abs_of_nonneg (by positivity : 0 ≤ a ^ 2 * c ^ 2)]
  calc _ ≤ 2 * |M| * a ^ 2 / (r * Kerr.sig a r c) := by
        gcongr
        nlinarith [sq_nonneg a]
    _ ≤ 2 * |M| * a ^ 2 / r ^ 3 := by
        gcongr
        calc r ^ 3 = r * r ^ 2 := by ring
          _ ≤ r * Kerr.sig a r c := by gcongr; exact sq_le_sig a r c

/-- The point with the polar co-ordinates `(r, χ = cos θ, φ)`. -/
def polarPoint (r c φ : ℝ) : E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![r * √(1 - c ^ 2) * Real.cos φ,
    r * √(1 - c ^ 2) * Real.sin φ, r * c]

theorem polarPoint_zero (r c φ : ℝ) : polarPoint r c φ 0 = r * √(1 - c ^ 2) * Real.cos φ := rfl
theorem polarPoint_one (r c φ : ℝ) : polarPoint r c φ 1 = r * √(1 - c ^ 2) * Real.sin φ := rfl
theorem polarPoint_two (r c φ : ℝ) : polarPoint r c φ 2 = r * c := rfl

theorem polarPoint_sq (r c φ : ℝ) (hc : c ^ 2 ≤ 1) :
    polarPoint r c φ 0 ^ 2 + polarPoint r c φ 1 ^ 2 = r ^ 2 * (1 - c ^ 2) := by
  rw [polarPoint_zero, polarPoint_one, mul_pow, mul_pow, mul_pow, mul_pow,
    Real.sq_sqrt (by linarith)]
  have h := Real.cos_sq_add_sin_sq φ
  linear_combination r ^ 2 * (1 - c ^ 2) * h

theorem norm_polarPoint {r : ℝ} (hr : 0 ≤ r) (c φ : ℝ) (hc : c ^ 2 ≤ 1) :
    ‖polarPoint r c φ‖ = r := by
  have h := EuclideanSpace.real_norm_sq_eq (polarPoint r c φ)
  rw [Fin.sum_univ_three, polarPoint_sq r c φ hc, polarPoint_two] at h
  have h2 : ‖polarPoint r c φ‖ ^ 2 = r ^ 2 := by rw [h]; ring
  exact (pow_left_inj₀ (norm_nonneg _) hr two_ne_zero).mp h2

/-- `J_{βα} = −J_{αβ}`. -/
theorem angularMomentum_antisymm (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (α β : Fin 3) :
    angularMomentum S β α = -angularMomentum S α β := by
  rw [angularMomentum, angularMomentum, ← integral_neg]
  congr 1
  funext y
  ring

theorem angularMomentum_self (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (α : Fin 3) :
    angularMomentum S α α = 0 := by
  simp [angularMomentum]

/-- The component `h(∂_t, ∂_φ) = −x₂ h₀₁ + x₁ h₀₂` of the metric perturbation, with
`∂_φ = −x₂ e₁ + x₁ e₂` about the third axis. -/
def spinComponent (κ : ℝ) (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (z : Spacetime) : ℝ :=
  metricPerturbation κ (staticStress S) z 0 (0 : Fin 3).succ * -(space z 1) +
    metricPerturbation κ (staticStress S) z 0 (1 : Fin 3).succ * space z 0

/-- **The leading spin term of the Kerr exterior** (Landau–Lifshitz (105.16) against (104.1)):
for a stationary source of angular momentum `J₁₂ = −Ma` about the third axis (`J₁₃ = J₂₃ = 0`;
the axes are numbered from `0` in the code, `J₁₂ = angularMomentum S 0 1`,
with `S_{0α} = −T^{0α}` the lower-index momentum density, so that the mechanical angular
momentum is `Ma`), the linear field with `κ = 8π` has, at the point of polar co-ordinates
`(r, χ, φ)` beyond the source, `h(∂_t, ∂_φ) = g_tφ + O(r⁻²)` with the Kerr coefficient
`g_tφ = −2Mar(1 − χ²)/Σ`; both are `−2Ma(1 − χ²)/r` at leading order. -/
theorem abs_spinComponent_sub_gtp_le (hS : StationarySource S a) {M₀ a₀ : ℝ}
    (hJ : angularMomentum S 0 1 = -(M₀ * a₀)) (hJ2 : angularMomentum S 0 2 = 0)
    (hJ3 : angularMomentum S 1 2 = 0) (t : ℝ) {r c φ : ℝ} (hr : a < r) (hc : c ^ 2 ≤ 1) :
    |spinComponent (8 * π) S (vector t (polarPoint r c φ)) - Kerr.gtp M₀ a₀ r c| ≤
      4 * (secondAbsMoment S 0 (0 : Fin 3).succ + secondAbsMoment S 0 (1 : Fin 3).succ) * r /
          (r - a) ^ 3 + 2 * |M₀| * |a₀| ^ 3 / r ^ 3 := by
  have hr0 : 0 < r := lt_of_le_of_lt hS.radius_nonneg hr
  set x := polarPoint r c φ with hxdef
  have hx : ‖x‖ = r := norm_polarPoint hr0.le c φ hc
  have hz : a < ‖space (vector t x)‖ := by rw [space_vector, hx]; exact hr
  have h1 := abs_hbar_zero_succ_sub_angularMomentum_le hS (8 * π) hz 0
  have h2 := abs_hbar_zero_succ_sub_angularMomentum_le hS (8 * π) hz 1
  rw [space_vector, hx] at h1 h2
  have hJ10 : angularMomentum S 1 0 = M₀ * a₀ := by
    rw [angularMomentum_antisymm, hJ, neg_neg]
  have hJ21 : angularMomentum S 1 2 = 0 := hJ3
  simp only [Fin.sum_univ_three, angularMomentum_self, hJ, hJ2, hJ10, hJ21, zero_mul,
    zero_add, add_zero] at h1 h2
  have hpi : 0 < π := Real.pi_pos
  have hra : 0 < r - a := by linarith
  set E1 := secondAbsMoment S 0 (0 : Fin 3).succ
  set E2 := secondAbsMoment S 0 (1 : Fin 3).succ
  set A := retardedPerturbation (8 * π) (staticStress S) (vector t x) 0 (0 : Fin 3).succ
  set B := retardedPerturbation (8 * π) (staticStress S) (vector t x) 0 (1 : Fin 3).succ
  have hκ : 2 * |8 * π| * (E1 / (4 * π * (r - a) ^ 3)) = 4 * E1 / (r - a) ^ 3 := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < 8 * π)]
    field_simp
    ring
  have hκ2 : 2 * |8 * π| * (E2 / (4 * π * (r - a) ^ 3)) = 4 * E2 / (r - a) ^ 3 := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < 8 * π)]
    field_simp
    ring
  rw [hκ] at h1
  rw [hκ2] at h2
  have hspin : spinComponent (8 * π) S (vector t x) = A * -(x 1) + B * x 0 := by
    simp only [spinComponent, metricPerturbation_zero_succ, space_vector]
    rfl
  have hlead : (A + 8 * π * (-(M₀ * a₀) * x 1) / (4 * π * r ^ 3)) * -(x 1) +
      (B + 8 * π * (M₀ * a₀ * x 0) / (4 * π * r ^ 3)) * x 0 =
      A * -(x 1) + B * x 0 + 2 * M₀ * a₀ * (1 - c ^ 2) / r := by
    have hsq := polarPoint_sq r c φ hc
    rw [← hxdef] at hsq
    have e : 8 * π * (-(M₀ * a₀) * x 1) / (4 * π * r ^ 3) * -(x 1) +
        8 * π * (M₀ * a₀ * x 0) / (4 * π * r ^ 3) * x 0 =
        2 * M₀ * a₀ * (x 0 ^ 2 + x 1 ^ 2) / r ^ 3 := by
      field_simp
      ring
    have e2 : 2 * M₀ * a₀ * (r ^ 2 * (1 - c ^ 2)) / r ^ 3 = 2 * M₀ * a₀ * (1 - c ^ 2) / r := by
      field_simp
    rw [hsq, e2] at e
    linear_combination e
  have hx0 : |x 0| ≤ r := by
    rw [← hx, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le x 0
  have hx1 : |x 1| ≤ r := by
    rw [← hx, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le x 1
  have hK := abs_gtp_add_le (M := M₀) (a := a₀) hr0 hc
  rw [hspin]
  have heq : A * -(x 1) + B * x 0 - Kerr.gtp M₀ a₀ r c =
      ((A + 8 * π * (-(M₀ * a₀) * x 1) / (4 * π * r ^ 3)) * -(x 1) +
        (B + 8 * π * (M₀ * a₀ * x 0) / (4 * π * r ^ 3)) * x 0) -
        (Kerr.gtp M₀ a₀ r c + 2 * M₀ * a₀ * (1 - c ^ 2) / r) := by
    rw [hlead]
    ring
  rw [heq]
  calc _ ≤ |(A + 8 * π * (-(M₀ * a₀) * x 1) / (4 * π * r ^ 3)) * -(x 1)| +
        |(B + 8 * π * (M₀ * a₀ * x 0) / (4 * π * r ^ 3)) * x 0| +
        |Kerr.gtp M₀ a₀ r c + 2 * M₀ * a₀ * (1 - c ^ 2) / r| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 4 * E1 / (r - a) ^ 3 * r + 4 * E2 / (r - a) ^ 3 * r + 2 * |M₀| * |a₀| ^ 3 / r ^ 3 := by
        rw [abs_mul, abs_mul, abs_neg]
        exact add_le_add (add_le_add (mul_le_mul h1 hx1 (abs_nonneg _) ((abs_nonneg _).trans h1))
          (mul_le_mul h2 hx0 (abs_nonneg _) ((abs_nonneg _).trans h2))) hK
    _ = _ := by ring

/-- **The leading mass term of the Kerr exterior**: for a mass-centred stationary source of mass
`M`, the linear field with `κ = 8π` has `h₀₀ = g_tt + 1 + O(r⁻³)` at every point at the distance
`r` beyond the source, for every value of `χ` and of the Kerr parameter `a`. -/
theorem abs_metricPerturbation_zero_zero_sub_gtt_le (hS : StationarySource S a)
    (hc : ∀ β : Fin 3, ∫ y, S y 0 0 * y β = 0) (t : ℝ) {x : E3} (hx : a < ‖x‖) (a₀ c : ℝ)
    (hc' : c ^ 2 ≤ 1) :
    |metricPerturbation (8 * π) (staticStress S) (vector t x) 0 0 -
        (Kerr.gtt (massOf S) a₀ ‖x‖ c + 1)| ≤
      2 * (secondAbsMoment S 0 0 + ∑ γ : Fin 3, secondAbsMoment S γ.succ γ.succ) /
          (‖x‖ - a) ^ 3 + 2 * |massOf S| * a₀ ^ 2 / ‖x‖ ^ 3 := by
  have hr0 : 0 < ‖x‖ := lt_of_le_of_lt hS.radius_nonneg hx
  have hz : a < ‖space (vector t x)‖ := by rw [space_vector]; exact hx
  have h := abs_metricPerturbation_zero_zero_sub_le hS hc (8 * π) hz
  rw [space_vector] at h
  have hpi : 0 < π := Real.pi_pos
  have hra : 0 < ‖x‖ - a := by linarith
  have hK := abs_gtt_add_le (M := massOf S) (a := a₀) hr0 hc'
  have e1 : 8 * π * massOf S / (4 * π * ‖x‖) = 2 * massOf S / ‖x‖ := by
    field_simp
    ring
  have e2 : |8 * π| * ((secondAbsMoment S 0 0 + ∑ γ : Fin 3, secondAbsMoment S γ.succ γ.succ) /
      (4 * π * (‖x‖ - a) ^ 3)) = 2 * (secondAbsMoment S 0 0 +
        ∑ γ : Fin 3, secondAbsMoment S γ.succ γ.succ) / (‖x‖ - a) ^ 3 := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < 8 * π)]
    field_simp
    ring
  rw [e1, e2] at h
  have heq : metricPerturbation (8 * π) (staticStress S) (vector t x) 0 0 -
      (Kerr.gtt (massOf S) a₀ ‖x‖ c + 1) =
      (metricPerturbation (8 * π) (staticStress S) (vector t x) 0 0 - 2 * massOf S / ‖x‖) -
        (Kerr.gtt (massOf S) a₀ ‖x‖ c + 1 - 2 * massOf S / ‖x‖) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add h hK)

/-! ### A rotating source -/

/-- A planar momentum density gives an angular momentum about the third axis only:
`S_{03} = 0` implies `J_{α3} = 0`. -/
theorem StationarySource.angularMomentum_eq_zero_of_planar (hS : StationarySource S a)
    (hp : ∀ y, S y 0 (2 : Fin 3).succ = 0) (α : Fin 3) : angularMomentum S α 2 = 0 := by
  have h1 := hS.currentDipole_eq α 2
  have h2 := hS.currentDipole_antisymm α 2
  have hp' : ∀ y, S y 0 3 = 0 := hp
  have h3 : currentDipole S 2 α = 0 := by simp [currentDipole, hp']
  rw [h3, neg_zero] at h2
  linarith

/-- The radial profile `f(x) = ψ(1 − ‖x‖²)` with the smooth transition `ψ`, supported in the unit
ball, with `f(0) = 1`. -/
def rotProfile (x : E3) : ℝ := Real.smoothTransition (1 - ‖x‖ ^ 2)

theorem contDiff_rotProfile : ContDiff ℝ ∞ rotProfile :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem rotProfile_eq_zero {x : E3} (hx : 1 < ‖x‖) : rotProfile x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by nlinarith [norm_nonneg x])

theorem rotProfile_zero : rotProfile 0 = 1 := by
  simp [rotProfile, Real.smoothTransition.one_of_one_le]

theorem rotProfile_neg (x : E3) : rotProfile (-x) = rotProfile x := by
  simp [rotProfile]

/-- `∂_γ f = −2ψ'(1 − ‖x‖²) x_γ`. -/
theorem fderiv_rotProfile (x : E3) (γ : Fin 3) :
    fderiv ℝ rotProfile x (EuclideanSpace.single γ 1) =
      -(2 * deriv Real.smoothTransition (1 - ‖x‖ ^ 2)) * x γ := by
  have hg : HasDerivAt (fun s => Real.smoothTransition (1 - s))
      (-deriv Real.smoothTransition (1 - ‖x‖ ^ 2)) (‖x‖ ^ 2) := by
    have h := (Wave.hasDerivAt_smoothTransition (1 - ‖x‖ ^ 2)).comp (‖x‖ ^ 2)
      ((hasDerivAt_id (‖x‖ ^ 2)).const_sub 1)
    exact h.congr_deriv (by ring)
  have h := hasFDerivAt_comp_normSq hg
  rw [show rotProfile = fun z => Real.smoothTransition (1 - ‖z‖ ^ 2) from rfl, h.fderiv]
  simp [EuclideanSpace.inner_single_right]

/-- **A rotating source**: the density `m f`, the momentum density `ν f (−x₂, x₁, 0)` in the
lower-index components `S_{0α}`, and no stresses; it is conserved since `div (ν f (−x₂, x₁, 0)) = 0`
for the radial `f`. -/
def rotSource (m ν : ℝ) (x : E3) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i k =>
    if i = 0 ∧ k = 0 then m * rotProfile x
    else if (i = 0 ∧ k = 1) ∨ (i = 1 ∧ k = 0) then -(ν * x 1 * rotProfile x)
    else if (i = 0 ∧ k = 2) ∨ (i = 2 ∧ k = 0) then ν * x 0 * rotProfile x
    else 0

theorem contDiff_coord_mul_rotProfile (c : ℝ) (β : Fin 3) :
    ContDiff ℝ ∞ fun x : E3 => c * x β * rotProfile x :=
  (contDiff_const.mul (contDiff_coord β)).mul contDiff_rotProfile

theorem rotSource_stress (m ν : ℝ) (y : E3) (γ β : Fin 3) :
    rotSource m ν y γ.succ β.succ = 0 := by
  fin_cases γ <;> fin_cases β <;> simp [rotSource]

/-- **The instance**: the rotating source is a stationary source in the unit ball. -/
theorem stationarySource_rotSource (m ν : ℝ) : StationarySource (rotSource m ν) 1 where
  radius_nonneg := zero_le_one
  contDiff i k := by
    have h0 : ContDiff ℝ ∞ fun x : E3 => m * rotProfile x := contDiff_const.mul contDiff_rotProfile
    have h1 := (contDiff_coord_mul_rotProfile ν 1).neg
    have h2 := contDiff_coord_mul_rotProfile ν 0
    fin_cases i <;> fin_cases k <;> simp [rotSource] <;> first | exact contDiff_const | assumption
  symm x i k := by
    fin_cases i <;> fin_cases k <;> simp [rotSource]
  conserved x b := by
    have hf (y : E3) := contDiff_rotProfile.differentiable (by simp) y
    have hc (β : Fin 3) (y : E3) := (contDiff_coord (n := 1) β).differentiable one_ne_zero y
    refine Fin.cases ?_ (fun β => ?_) b
    · have e1 : (fun y => rotSource m ν y (0 : Fin 3).succ 0) =
          fun y => -ν * (y 1 * rotProfile y) := funext fun y => by simp [rotSource]; ring
      have e2 : (fun y => rotSource m ν y (1 : Fin 3).succ 0) =
          fun y => ν * (y 0 * rotProfile y) := funext fun y => by simp [rotSource]; ring
      have e3 : (fun y => rotSource m ν y (2 : Fin 3).succ 0) = fun _ => 0 :=
        funext fun y => by simp [rotSource]
      have hd1 : DifferentiableAt ℝ (fun y : E3 => y 1 * rotProfile y) x := (hc 1 x).mul (hf x)
      have hd0 : DifferentiableAt ℝ (fun y : E3 => y 0 * rotProfile y) x := (hc 0 x).mul (hf x)
      rw [Fin.sum_univ_three, e1, e2, e3, fderiv_const_mul hd1, fderiv_const_mul hd0,
        fderiv_fun_mul (hc 1 x) (hf x), fderiv_fun_mul (hc 0 x) (hf x)]
      simp only [smul_apply, add_apply, smul_eq_mul, fderiv_coord, fderiv_rotProfile,
        fderiv_const_apply, zero_apply]
      simp
      ring
    · have e (γ : Fin 3) : (fun y => rotSource m ν y γ.succ β.succ) = fun _ => 0 :=
        funext fun y => rotSource_stress m ν y γ β
      simp [e]
  support x hx := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [rotSource, rotProfile_eq_zero hx]

/-- The rotating source is mass-centred: `∫ S₀₀ y_β = 0`, by the symmetry `y ↦ −y`. -/
theorem rotSource_massCentred (m ν : ℝ) (β : Fin 3) :
    ∫ y, rotSource m ν y 0 0 * y β = 0 := by
  have h := integral_neg_eq_self (fun y : E3 => rotSource m ν y 0 0 * y β) volume
  have h2 : (fun y : E3 => rotSource m ν (-y) 0 0 * (-y) β) =
      fun y => -(rotSource m ν y 0 0 * y β) := funext fun y => by
    simp [rotSource, rotProfile_neg]
  rw [h2, integral_neg] at h
  linarith

/-- The momentum of the rotating source lies in the plane of the first two axes. -/
theorem rotSource_planar (m ν : ℝ) (y : E3) : rotSource m ν y 0 (2 : Fin 3).succ = 0 := by
  simp [rotSource]

/-- The rotating source is not zero: `S₀₀(0) = m`. -/
theorem rotSource_zero_zero (m ν : ℝ) : rotSource m ν 0 0 0 = m := by
  simp [rotSource, rotProfile_zero]

end ProjectAinos.GeneralRelativity.StationaryFarField
