/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.RadiationReaction.RadiusScaling
public import ProjectAinos.SmoothGeometry.ODE.DistributedDelay
import Mathlib.Tactic

/-!
# The self-consistent motion of a rigid charge in the linear model

Landau–Lifshitz, *The Classical Theory of Fields*, §75, with `c = 1` and the units with
`div E = ρ`. A rigid charge `eη(x − R(t))` with a profile `η` supported in `‖z‖ ≤ b` is expanded to
the first order in the displacement `R`: the density is `ρ₀ + ρ₁` with `ρ₀ = eη(x)`
(`restCharge`) and `ρ₁ = −e ∇η(x) · R(t)` (`linearCharge`), and the current is
`𝐣₁ = e Ṙ(t) η(x)` (`linearCurrent`); `hasDerivAt_rigidCharge_smul` and
`hasDerivAt_rigidCurrent_smul` identify them as the derivatives of `rigidCharge` and
`rigidCurrent` along `εR` at `ε = 0`. The field is the retarded field: the Coulomb field `E₀` of
`ρ₀` (`restField`) and the retarded field `E₁` of `(ρ₁, 𝐣₁)` (`linearField`). The **linear
self-force** (`linearSelfForce`) is the first-order part `∫ (ρ₀ E₁ + ρ₁ E₀)` of the Lorentz force
`∫ ρ (E + 𝐯 × B)` of the charge on itself; the magnetic force is of the second order.

* **The convolution** `linearSelfForce_eq` (S1): for a `C²` profile vanishing outside a ball and
  invariant under the linear isometries of space, and a `C²` path,
  `Fᵢ(t) = −(2/3) e² ∫∫ η(x) η(x − y) R̈ᵢ(t − ‖y‖)/(4π‖y‖) dy dx`. The terms with the second
  derivatives of `η` are reduced by integration by parts, by the isotropy
  (`integral_mul_profileDeriv2_eq_zero`, `integral_mul_profileDeriv2_diag`) and by the retarded
  identity of the wave operator (`sum_retardedIntegral_profileDeriv2`), which contributes `1/3` of
  the term of the vector potential.
* `linearSelfForce_eq_delayOp`: the force is `−K R̈` for the delay datum `selfDelayData` on
  `ℝ³ × ℝ³` with the weight `selfWeight` `(2/3) e² η(x) η(x − y)/(4π‖y‖)` and the delay `‖y‖`,
  bounded by `2b` (`linearSelfForce_congr`, `linearSelfForce_congr_path`: the force at `t`
  depends only on the path on `[t − 2b, t]`). The moments: `integral_selfWeight` (`∫ w = (4/3) U`,
  the electromagnetic mass of `selfMass_isotropic`) and `integral_selfWeight_mul_delay`
  (`∫ w τ = (2/3)(e²/4π)` for a profile of mass one, the damping constant, independent of the
  size). `continuity_linear`: the linear source is conserved.
* `linearSelfForce_inertial`, `linearMotion_inertial`: an inertial path with no external force is
  an exact solution.
* **The equation of motion** `m₀ R̈ = F + F_self[R]` with the bare mass `m₀` (S2):
  `linearMotion_iff` (it is the delay equation `m₀ R̈ + K R̈ = F` of
  `SmoothGeometry.DistributedDelay`); `exists_linearMotion`, `linearMotion_unique` and
  `existsUnique_linearMotion`: for `m₀ ≠ 0`, a rate `γ ≥ 0` with
  `q_γ = ∫ |w| e^{−γτ} < |m₀|` (which exists for every `m₀ ≠ 0`, `exists_rate_selfWeight`), a
  force of growth `e^{γt}` and a compatible `C²` history, there is exactly one global `C²`
  solution, and `linearMotion_unique_of_Icc`: two solutions that agree on the history interval
  `[−2b, 0]` agree for `t ≥ 0`; `norm_sub_le_linearMotion`: Lipschitz dependence on the force and
  the history, `‖ΔR̈(t)‖ ≤ e^{γt}(C + qH)/(|m₀| − q_γ)`, uniform in time when `q < |m₀|`. For a
  nonnegative charge `q = (4/3) U` (`integral_abs_selfWeight`), which is `(4/3) U(η)/a` for the
  profile of radius `a` (`integral_abs_selfWeight_scaledProfile`).
* **Runaways**: `exists_runaway_linearMotion`: for `m₀ < 0 < m₀ + (4/3) U` (positive observed
  mass, electromagnetic mass above it, the small charges at a fixed observed mass) the free
  equation has the solutions `e^{γt} c` with `γ > 0`.

**Scope.** The model is the first order in the displacement: the retarded field of the rigid
charge along the path, with the time delay `‖x − y‖` across the charge, expanded linearly in `R`.
The self-force of the fully retarded rigid charge (whose delay depends on the path) and of a
relativistic extended charge are not treated here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.RadiationReaction

open SmoothGeometry SmoothGeometry.Wave SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Derivatives of a profile -/

/-- The partial derivative `∂ₖη`. -/
def profileDeriv (η : E3 → ℝ) (k : Fin 3) (z : E3) : ℝ :=
  fderiv ℝ η z (EuclideanSpace.single k 1)

/-- The second partial derivative `∂ᵢ∂ₖη`. -/
def profileDeriv2 (η : E3 → ℝ) (i k : Fin 3) (z : E3) : ℝ :=
  fderiv ℝ (profileDeriv η k) z (EuclideanSpace.single i 1)

section Profile

variable {η : E3 → ℝ}

theorem contDiff_profileDeriv (hη : ContDiff ℝ 2 η) (k : Fin 3) :
    ContDiff ℝ 1 (profileDeriv η k) :=
  (hη.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem continuous_profileDeriv2 (hη : ContDiff ℝ 2 η) (i k : Fin 3) :
    Continuous (profileDeriv2 η i k) :=
  ((contDiff_profileDeriv hη k).continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The derivative of a function vanishing outside a ball vanishes outside the ball. -/
theorem fderiv_eq_zero_of_far {G : E3 → ℝ} {b : ℝ} (hG : ∀ z : E3, b < ‖z‖ → G z = 0) {z : E3}
    (hz : b < ‖z‖) : fderiv ℝ G z = 0 := by
  have h : G =ᶠ[𝓝 z] fun _ => 0 :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
      fun y hy => hG y hy
  rw [h.fderiv_eq, fderiv_const_apply]

theorem profileDeriv_eq_zero {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (k : Fin 3) {z : E3}
    (hz : b < ‖z‖) : profileDeriv η k z = 0 := by
  simp [profileDeriv, fderiv_eq_zero_of_far hb hz]

theorem profileDeriv2_eq_zero {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (i k : Fin 3) {z : E3}
    (hz : b < ‖z‖) : profileDeriv2 η i k z = 0 := by
  simp [profileDeriv2, fderiv_eq_zero_of_far (fun y hy => profileDeriv_eq_zero hb k hy) hz]

/-- The derivative of `∂ₖη` is the second derivative of `η` applied to `eₖ`. -/
theorem fderiv_profileDeriv_apply (hη : ContDiff ℝ 2 η) (k : Fin 3) (z v : E3) :
    fderiv ℝ (profileDeriv η k) z v = fderiv ℝ (fderiv ℝ η) z v (EuclideanSpace.single k 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ η) z :=
    (hη.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z
  change fderiv ℝ (fun z => fderiv ℝ η z (EuclideanSpace.single k 1)) z v = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- The second derivatives of a `C²` profile are symmetric. -/
theorem profileDeriv2_comm (hη : ContDiff ℝ 2 η) (i k : Fin 3) (z : E3) :
    profileDeriv2 η i k z = profileDeriv2 η k i z := by
  have hs := (hη.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
  simp only [profileDeriv2, fderiv_profileDeriv_apply hη]
  exact hs _ _

end Profile

/-! ### Isotropy of the second derivatives -/

section Isotropy

variable {η : E3 → ℝ}

/-- The chain rule along a linear isometry. -/
theorem fderiv_comp_isometry (L : E3 ≃ₗᵢ[ℝ] E3) {φ : E3 → ℝ} {z : E3}
    (hφ : DifferentiableAt ℝ φ (L z)) (v : E3) :
    fderiv ℝ (fun y => φ (L y)) z v = fderiv ℝ φ (L z) (L v) := by
  have h : HasFDerivAt (fun y => φ (L y))
      ((fderiv ℝ φ (L z)).comp (L.toContinuousLinearEquiv : E3 →L[ℝ] E3)) z :=
    hφ.hasFDerivAt.comp z (L.toContinuousLinearEquiv : E3 →L[ℝ] E3).hasFDerivAt
  rw [h.fderiv]
  rfl

/-- For a profile invariant under `L`: `Dη(z) u = Dη(Lz)(Lu)`. -/
theorem fderiv_apply_of_invariant (L : E3 ≃ₗᵢ[ℝ] E3) (hrot : ∀ x, η (L x) = η x)
    (hη : Differentiable ℝ η) (z u : E3) : fderiv ℝ η z u = fderiv ℝ η (L z) (L u) := by
  have he : η = fun y => η (L y) := funext fun y => (hrot y).symm
  conv_lhs => rw [he]
  exact fderiv_comp_isometry L (hη _) u

/-- For a `C²` profile invariant under `L`: `D²η(z)(v, u) = D²η(Lz)(Lv, Lu)`. -/
theorem fderiv_fderiv_apply_of_invariant (L : E3 ≃ₗᵢ[ℝ] E3) (hrot : ∀ x, η (L x) = η x)
    (hη : ContDiff ℝ 2 η) (z u v : E3) :
    fderiv ℝ (fun y => fderiv ℝ η y u) z v =
      fderiv ℝ (fun y => fderiv ℝ η y (L u)) (L z) (L v) := by
  have he : (fun y => fderiv ℝ η y u) = fun y => (fun y' => fderiv ℝ η y' (L u)) (L y) :=
    funext fun y => fderiv_apply_of_invariant L hrot (hη.differentiable (by norm_num)) y u
  rw [he]
  refine fderiv_comp_isometry L (φ := fun y' => fderiv ℝ η y' (L u)) ?_ v
  exact ((hη.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) _).clm_apply
    (differentiableAt_const _)

theorem coordReflection_single_self (i : Fin 3) :
    coordReflection i (EuclideanSpace.single i 1) = -EuclideanSpace.single i 1 := by
  ext l
  rw [coordReflection_apply]
  split_ifs with h
  · rfl
  · simp [h]

theorem coordReflection_single_of_ne {i k : Fin 3} (hik : i ≠ k) :
    coordReflection i (EuclideanSpace.single k 1) = EuclideanSpace.single k 1 := by
  ext l
  rw [coordReflection_apply]
  split_ifs with h
  · subst h
    simp [hik]
  · rfl

theorem coordSwap_single (i k : Fin 3) :
    coordSwap i k (EuclideanSpace.single k 1) = EuclideanSpace.single i 1 := by
  ext l
  rw [coordSwap_apply]
  simp only [PiLp.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]

/-- The reflection of the coordinate `i` reverses the mixed second derivatives `∂ᵢ∂ₖη`. -/
theorem profileDeriv2_coordReflection {i k : Fin 3} (hik : i ≠ k)
    (hrot : ∀ x, η (coordReflection i x) = η x) (hη : ContDiff ℝ 2 η) (z : E3) :
    profileDeriv2 η i k (coordReflection i z) = -profileDeriv2 η i k z := by
  have h := fderiv_fderiv_apply_of_invariant (coordReflection i) hrot hη z
    (EuclideanSpace.single k 1) (EuclideanSpace.single i 1)
  rw [coordReflection_single_self, coordReflection_single_of_ne hik, map_neg] at h
  change profileDeriv2 η i k z = -profileDeriv2 η i k (coordReflection i z) at h
  rw [h, neg_neg]

/-- The exchange of the coordinates `i`, `k` exchanges `∂ᵢ²η` and `∂ₖ²η`. -/
theorem profileDeriv2_coordSwap (i k : Fin 3) (hrot : ∀ x, η (coordSwap i k x) = η x)
    (hη : ContDiff ℝ 2 η) (z : E3) :
    profileDeriv2 η i i (coordSwap i k z) = profileDeriv2 η k k z := by
  have h := fderiv_fderiv_apply_of_invariant (coordSwap i k) hrot hη z
    (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)
  rw [coordSwap_single] at h
  exact h.symm

/-- **A rotation of the variables** in the double integral with a derivative of the profile:
for `η` and `K` invariant under `L`, `∫∫ η(x) K(y) D(x − y) = ∫∫ η(x) K(y) D(L(x − y))`. -/
theorem integral_mul_kernel_sub_comp (L : E3 ≃ₗᵢ[ℝ] E3) (hrot : ∀ x, η (L x) = η x)
    {K : E3 → ℝ} (hK : ∀ y, K (L y) = K y) (D : E3 → ℝ) :
    ∫ x, η x * ∫ y, K y * D (x - y) = ∫ x, η x * ∫ y, K y * D (L (x - y)) := by
  have hmp := L.measurePreserving
  rw [← hmp.integral_comp' (f := L.toMeasurableEquiv)]
  congr 1
  funext x
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv]
  rw [hrot x, ← hmp.integral_comp' (f := L.toMeasurableEquiv)]
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv, ← map_sub, hK]

/-- **Isotropy, off the diagonal**: for an invariant profile and an invariant kernel,
`∫∫ η(x) K(y) ∂ᵢ∂ₖη(x − y) = 0` for `i ≠ k`. -/
theorem integral_mul_profileDeriv2_eq_zero
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (hη : ContDiff ℝ 2 η)
    {K : E3 → ℝ} (hK : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (y : E3), K (f y) = K y) {i k : Fin 3}
    (hik : i ≠ k) : ∫ x, η x * ∫ y, K y * profileDeriv2 η i k (x - y) = 0 := by
  have h := integral_mul_kernel_sub_comp (coordReflection i) (hrot _) (hK _)
    (profileDeriv2 η i k)
  simp only [profileDeriv2_coordReflection hik (hrot _) hη, mul_neg, integral_neg] at h
  linarith

/-- **Isotropy, on the diagonal**: for an invariant profile and an invariant kernel,
`∫∫ η(x) K(y) ∂ᵢ²η(x − y)` does not depend on `i`. -/
theorem integral_mul_profileDeriv2_diag
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (hη : ContDiff ℝ 2 η)
    {K : E3 → ℝ} (hK : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (y : E3), K (f y) = K y) (i k : Fin 3) :
    ∫ x, η x * ∫ y, K y * profileDeriv2 η i i (x - y) =
      ∫ x, η x * ∫ y, K y * profileDeriv2 η k k (x - y) := by
  have h := integral_mul_kernel_sub_comp (coordSwap i k) (hrot _) (hK _) (profileDeriv2 η i i)
  simp only [profileDeriv2_coordSwap i k (hrot _) hη] at h
  exact h

end Isotropy

/-! ### The linear model -/

/-- The charge `eη(x)` at rest, as a static density on `ℝ × ℝ³`. -/
def restCharge (e : ℝ) (η : E3 → ℝ) : ℝ × E3 → ℝ := fun p => e * η p.2

/-- The first-order density `ρ₁ = −e ∇η(x) · R(t)` of the rigid charge displaced by `R(t)`. -/
def linearCharge (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) : ℝ × E3 → ℝ :=
  fun p => -(e * fderiv ℝ η p.2 (R p.1))

/-- The first-order current `𝐣₁ = e Ṙ(t) η(x)` of the displaced rigid charge. -/
def linearCurrent (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (k : Fin 3) : ℝ × E3 → ℝ :=
  fun p => e * deriv R p.1 k * η p.2

/-- The Coulomb field `E₀` of the charge at rest, the retarded field of `restCharge`. -/
def restField (e : ℝ) (η : E3 → ℝ) (i : Fin 3) : ℝ × E3 → ℝ :=
  electricOf (retardedIntegral (restCharge e η)) (fun _ _ => 0) i

/-- The first-order retarded field `E₁ = −∇φ₁ − ∂ₜ𝐚₁` of `(ρ₁, 𝐣₁)`. -/
def linearField (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (i : Fin 3) : ℝ × E3 → ℝ :=
  electricOf (retardedIntegral (linearCharge e η R))
    (fun k => retardedIntegral (linearCurrent e η R k)) i

/-- **The linear self-force** `Fᵢ(t) = ∫ (ρ₀ E₁ᵢ + ρ₁ E₀ᵢ)(t, x) dx`, the part of the first order in
the displacement of the Lorentz force `∫ ρ (E + 𝐯 × B)` of the retarded field of the rigid charge
on itself (the zeroth order `∫ ρ₀ E₀` vanishes, and `𝐯 × B` is of the second order). -/
def linearSelfForce (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (t : ℝ) (i : Fin 3) : ℝ :=
  (∫ x, restCharge e η (t, x) * linearField e η R i (t, x)) +
    ∫ x, linearCharge e η R (t, x) * restField e η i (t, x)

section Model

variable {e : ℝ} {η : E3 → ℝ} {R : ℝ → E3}

/-- The rigid charge at rest is `restCharge`. -/
theorem rigidCharge_zero (e : ℝ) (η : E3 → ℝ) :
    rigidCharge e η (fun _ => 0) = restCharge e η := by
  funext p
  simp [rigidCharge, restCharge]

/-- **The first-order density is the derivative of the rigid charge**: along the displacement
`εR`, `d/dε eη(x − εR(t))` at `ε = 0` is `linearCharge`. -/
theorem hasDerivAt_rigidCharge_smul (hη : Differentiable ℝ η) (R : ℝ → E3) (p : ℝ × E3) :
    HasDerivAt (fun ε : ℝ => rigidCharge e η (fun s => ε • R s) p) (linearCharge e η R p) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => p.2 - ε • R p.1) (-R p.1) 0 := by
    have := (hasDerivAt_const (0 : ℝ) p.2).fun_sub ((hasDerivAt_id' (0 : ℝ)).smul_const (R p.1))
    simpa using this
  have h2 := ((hη _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1).const_mul e
  simp only [zero_smul, sub_zero, map_neg] at h2
  simpa [rigidCharge, linearCharge, Function.comp_def] using h2

/-- **The first-order current is the derivative of the rigid current** along `εR` at `ε = 0`. -/
theorem hasDerivAt_rigidCurrent_smul (hη : Differentiable ℝ η) (hR : Differentiable ℝ R)
    (k : Fin 3) (p : ℝ × E3) :
    HasDerivAt (fun ε : ℝ => rigidCurrent e η (fun s => ε • R s) k p)
      (linearCurrent e η R k p) 0 := by
  have hd : ∀ ε : ℝ, deriv (fun s => ε • R s) p.1 = ε • deriv R p.1 := fun ε =>
    ((hR p.1).hasDerivAt.const_smul ε).deriv
  have hf : (fun ε : ℝ => rigidCurrent e η (fun s => ε • R s) k p) =
      fun ε => (e * deriv R p.1 k) * (ε * η (p.2 - ε • R p.1)) := by
    funext ε
    simp only [rigidCurrent, hd, PiLp.smul_apply, smul_eq_mul]
    ring
  have h1 : HasDerivAt (fun ε : ℝ => p.2 - ε • R p.1) (-R p.1) 0 := by
    have := (hasDerivAt_const (0 : ℝ) p.2).fun_sub ((hasDerivAt_id' (0 : ℝ)).smul_const (R p.1))
    simpa using this
  have h2 : HasDerivAt (fun ε : ℝ => η (p.2 - ε • R p.1)) (fderiv ℝ η p.2 (-R p.1)) 0 := by
    have := (hη _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    simpa [Function.comp_def] using this
  have h3 := ((hasDerivAt_id' (0 : ℝ)).fun_mul h2).const_mul (e * deriv R p.1 k)
  rw [hf]
  convert h3 using 1
  simp [linearCurrent]

/-! ### Supports and smoothness -/

theorem spatialSupport_slice {b : ℝ} (c : ℝ → ℝ) {G : E3 → ℝ}
    (hG : ∀ z : E3, b < ‖z‖ → G z = 0) : SpatialSupport b (fun p : ℝ × E3 => c p.1 * G p.2) :=
  fun p hp => by simp [hG _ hp]

theorem spatialSupport_static {b : ℝ} {G : E3 → ℝ} (hG : ∀ z : E3, b < ‖z‖ → G z = 0) :
    SpatialSupport b (fun p : ℝ × E3 => G p.2) :=
  fun _ hp => hG _ hp

theorem spatialSupport_restCharge {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) :
    SpatialSupport b (restCharge e η) :=
  fun p hp => by simp [restCharge, hb _ hp]

theorem spatialSupport_linearCharge {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) :
    SpatialSupport b (linearCharge e η R) :=
  fun p hp => by simp [linearCharge, fderiv_eq_zero_of_far hb hp]

theorem spatialSupport_linearCurrent {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (k : Fin 3) :
    SpatialSupport b (linearCurrent e η R k) :=
  fun p hp => by simp [linearCurrent, hb _ hp]

theorem contDiff_mul_slice {n : ℕ∞} {c : ℝ → ℝ} {G : E3 → ℝ} (hc : ContDiff ℝ n c)
    (hG : ContDiff ℝ n G) : ContDiff ℝ n (fun p : ℝ × E3 => c p.1 * G p.2) :=
  (hc.comp contDiff_fst).mul (hG.comp contDiff_snd)

theorem contDiff_linearCharge (hη : ContDiff ℝ 2 η) (hR : ContDiff ℝ 2 R) :
    ContDiff ℝ 1 (linearCharge e η R) :=
  (contDiff_const.mul (((hη.fderiv_right (m := 1) (by norm_num)).comp contDiff_snd).clm_apply
    ((hR.of_le (by norm_num)).comp contDiff_fst))).neg

/-- The velocity of a `C²` path is `C¹`. -/
theorem contDiff_deriv_path (hR : ContDiff ℝ 2 R) : ContDiff ℝ 1 (deriv R) :=
  ((contDiff_succ_iff_deriv (n := 1)).mp hR).2.2

theorem contDiff_linearCurrent (hη : ContDiff ℝ 2 η) (hR : ContDiff ℝ 2 R) (k : Fin 3) :
    ContDiff ℝ 1 (linearCurrent e η R k) :=
  (contDiff_const.mul (((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).contDiff.comp
    (contDiff_deriv_path hR)).comp contDiff_fst)).mul ((hη.of_le (by norm_num)).comp contDiff_snd)

/-! ### Derivatives of the sources -/

/-- The first-order density in coordinates: `ρ₁ = Σₖ Rₖ(t) (−e ∂ₖη(x))`. -/
theorem linearCharge_eq_sum (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) :
    linearCharge e η R = fun p => ∑ k, R p.1 k * (-(e * profileDeriv η k p.2)) := by
  funext p
  simp only [linearCharge, profileDeriv]
  rw [clm_apply_eq_sum (fderiv ℝ η p.2) (R p.1), Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem fderiv_neg_const_mul_profileDeriv (hη : ContDiff ℝ 2 η) (e : ℝ) (i k : Fin 3)
    (z : E3) :
    fderiv ℝ (fun z => -(e * profileDeriv η k z)) z (EuclideanSpace.single i 1) =
      -(e * profileDeriv2 η i k z) := by
  have hd : DifferentiableAt ℝ (profileDeriv η k) z :=
    (contDiff_profileDeriv hη k).differentiable one_ne_zero z
  rw [fderiv_fun_neg, fderiv_const_mul hd]
  rfl

/-- `∂ᵢρ₁ = Σₖ Rₖ(t) (−e ∂ᵢ∂ₖη(x))`. -/
theorem spaceDeriv_linearCharge (hη : ContDiff ℝ 2 η) (hR : ContDiff ℝ 2 R) (i : Fin 3)
    (p : ℝ × E3) :
    spaceDeriv i (linearCharge e η R) p =
      ∑ k, R p.1 k * (-(e * profileDeriv2 η i k p.2)) := by
  have hc : ∀ k, Differentiable ℝ fun s => R s k := fun k =>
    ((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).contDiff.comp hR).differentiable (by norm_num)
  have hG : ∀ k, Differentiable ℝ fun z => -(e * profileDeriv η k z) := fun k =>
    ((contDiff_const.mul (contDiff_profileDeriv hη k)).neg).differentiable one_ne_zero
  have hdk : ∀ k, Differentiable ℝ
      (fun q : ℝ × E3 => R q.1 k * (-(e * profileDeriv η k q.2))) := fun k =>
    ((hc k).comp differentiable_fst).mul ((hG k).comp differentiable_snd)
  rw [linearCharge_eq_sum]
  rw [spaceDeriv_fun_sum _ fun k _ => hdk k p]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [spaceDeriv_mul_slice (hc k) (hG k) i, fderiv_neg_const_mul_profileDeriv hη]

/-- `∂ₜ𝐣₁ᵢ = e R̈ᵢ(t) η(x)`. -/
theorem timeDeriv_linearCurrent (hη : ContDiff ℝ 2 η) (hR : ContDiff ℝ 2 R) (i : Fin 3) :
    timeDeriv (linearCurrent e η R i) = fun p => e * deriv (deriv R) p.1 i * η p.2 := by
  have hd : Differentiable ℝ (deriv R) := (contDiff_deriv_path hR).differentiable one_ne_zero
  have hc : ∀ s, HasDerivAt (fun s => e * deriv R s i) (e * deriv (deriv R) s i) s := fun s =>
    (hasDerivAt_component_path (hd s).hasDerivAt i).const_mul e
  exact timeDeriv_mul_slice hc (hη.differentiable (by norm_num))

/-- `∂ᵢρ₀ = e ∂ᵢη(x)`. -/
theorem spaceDeriv_restCharge (hη : ContDiff ℝ 2 η) (i : Fin 3) :
    spaceDeriv i (restCharge e η) = fun p => e * profileDeriv η i p.2 :=
  spaceDeriv_mul_slice (c := fun _ => e) (differentiable_const e)
    (hη.differentiable (by norm_num)) i

/-- `∂ₖ(e ∂ᵢη(x)) = e ∂ₖ∂ᵢη(x)`. -/
theorem spaceDeriv_static_profileDeriv (hη : ContDiff ℝ 2 η) (i k : Fin 3) :
    spaceDeriv k (fun p : ℝ × E3 => e * profileDeriv η i p.2) =
      fun p => e * profileDeriv2 η k i p.2 :=
  spaceDeriv_mul_slice (c := fun _ => e) (differentiable_const e)
    ((contDiff_profileDeriv hη i).differentiable one_ne_zero) k

/-! ### Linearity of the retarded integral on sources in a cylinder -/

theorem retardedIntegral_neg' (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    retardedIntegral (fun q => -f q) p = -retardedIntegral f p := by
  simp only [retardedIntegral, smul_neg, integral_neg]

theorem retardedIntegral_sub' {b : ℝ} {f g : ℝ × E3 → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfs : SpatialSupport b f) (hgs : SpatialSupport b g) (p : ℝ × E3) :
    retardedIntegral (fun q => f q - g q) p = retardedIntegral f p - retardedIntegral g p := by
  simp only [retardedIntegral, smul_sub]
  exact integral_sub (hfs.subluminalSupport.integrable hf p)
    (hgs.subluminalSupport.integrable hg p)

theorem retardedIntegral_sum' {b : ℝ} {f : Fin 3 → ℝ × E3 → ℝ} (hf : ∀ k, Continuous (f k))
    (hfs : ∀ k, SpatialSupport b (f k)) (p : ℝ × E3) :
    retardedIntegral (fun q => ∑ k, f k q) p = ∑ k, retardedIntegral (f k) p :=
  retardedIntegral_finsetSum _ fun k _ => (hfs k).subluminalSupport.integrable (hf k) p

/-! ### The fields -/

/-- **The first-order field**:
`E₁ᵢ(t, x) = Σₖ R[Rₖ ⊗ e∂ᵢ∂ₖη](t, x) − R[R̈ᵢ ⊗ eη](t, x)` with the retarded integral `R`. -/
theorem linearField_eq (hη : ContDiff ℝ 2 η) {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hR : ContDiff ℝ 2 R) (i : Fin 3) (p : ℝ × E3) :
    linearField e η R i p =
      ∑ k, retardedIntegral (fun q => R q.1 k * (e * profileDeriv2 η i k q.2)) p -
        retardedIntegral (fun q => deriv (deriv R) q.1 i * (e * η q.2)) p := by
  have hcR : ∀ k, Continuous fun s => R s k := fun k =>
    ((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).continuous.comp hR.continuous)
  have hcont : ∀ k, Continuous fun q : ℝ × E3 => R q.1 k * (-(e * profileDeriv2 η i k q.2)) :=
    fun k => ((hcR k).comp continuous_fst).mul
      ((continuous_const.mul (continuous_profileDeriv2 hη i k)).neg.comp continuous_snd)
  have hsupp : ∀ k, SpatialSupport b
      fun q : ℝ × E3 => R q.1 k * (-(e * profileDeriv2 η i k q.2)) := fun k =>
    spatialSupport_slice (fun s => R s k) (G := fun z => -(e * profileDeriv2 η i k z))
      fun z hz => by
      simp [profileDeriv2_eq_zero hb i k hz]
  simp only [linearField, electricOf]
  rw [spaceDeriv_retardedIntegral (contDiff_linearCharge hη hR)
      (spatialSupport_linearCharge hb).subluminalSupport i,
    timeDeriv_retardedIntegral (contDiff_linearCurrent hη hR i)
      (spatialSupport_linearCurrent hb i).subluminalSupport,
    timeDeriv_linearCurrent hη hR i]
  have h1 : spaceDeriv i (linearCharge e η R) =
      fun q => ∑ k, R q.1 k * (-(e * profileDeriv2 η i k q.2)) :=
    funext fun q => spaceDeriv_linearCharge hη hR i q
  have h2 : (fun q : ℝ × E3 => e * deriv (deriv R) q.1 i * η q.2) =
      fun q => deriv (deriv R) q.1 i * (e * η q.2) := funext fun q => by ring
  rw [h1, h2, retardedIntegral_sum' hcont hsupp]
  have h3 : ∀ k, retardedIntegral (fun q => R q.1 k * (-(e * profileDeriv2 η i k q.2))) p =
      -retardedIntegral (fun q => R q.1 k * (e * profileDeriv2 η i k q.2)) p := fun k => by
    rw [← retardedIntegral_neg']
    congr 1
    funext q
    ring
  simp only [h3, Finset.sum_neg_distrib, neg_neg]

/-- **The Coulomb field of the charge at rest**: `E₀ᵢ = −R[e∂ᵢη]`. -/
theorem restField_eq (hη : ContDiff ℝ 2 η) {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (i : Fin 3) (p : ℝ × E3) :
    restField e η i p = -retardedIntegral (fun q => e * profileDeriv η i q.2) p := by
  have hρ : ContDiff ℝ 1 (restCharge e η) :=
    (contDiff_const.mul (hη.comp contDiff_snd)).of_le (by norm_num)
  simp only [restField, electricOf]
  rw [spaceDeriv_retardedIntegral hρ (spatialSupport_restCharge hb).subluminalSupport i,
    spaceDeriv_restCharge hη, timeDeriv_zero, sub_zero]

/-- **The linear source is conserved**: `∂ₜρ₁ + div 𝐣₁ = 0`, so its retarded potentials satisfy
the gauge of Lorenz and the equations of Maxwell (`lorenz_retardedPotential`,
`maxwell_retardedPotential`). -/
theorem continuity_linear (hη : ContDiff ℝ 2 η) (hR : ContDiff ℝ 2 R) (p : ℝ × E3) :
    timeDeriv (linearCharge e η R) p + ∑ k, spaceDeriv k (linearCurrent e η R k) p = 0 := by
  have hd : Differentiable ℝ R := hR.differentiable (by norm_num)
  have hηd : Differentiable ℝ η := hη.differentiable (by norm_num)
  have hc : ∀ k, Differentiable ℝ fun s => e * deriv R s k := fun k =>
    (differentiable_const e).mul (((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).contDiff.comp
      (contDiff_deriv_path hR)).differentiable one_ne_zero)
  have hj : ∀ k, spaceDeriv k (linearCurrent e η R k) p =
      e * deriv R p.1 k * profileDeriv η k p.2 := fun k => by
    have := spaceDeriv_mul_slice (hc k) hηd k
    exact congrFun this p
  have hcR : ∀ k, HasDerivAt (fun s => R s k) (deriv R p.1 k) p.1 := fun k =>
    hasDerivAt_component_path (hd p.1).hasDerivAt k
  have ht : timeDeriv (linearCharge e η R) p =
      ∑ k, deriv R p.1 k * (-(e * profileDeriv η k p.2)) := by
    rw [linearCharge_eq_sum]
    have hdk : ∀ k, Differentiable ℝ
        (fun q : ℝ × E3 => R q.1 k * (-(e * profileDeriv η k q.2))) := fun k =>
      ((((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).contDiff.comp hR).differentiable
        (by norm_num)).comp differentiable_fst).mul
        ((((contDiff_const.mul (contDiff_profileDeriv hη k)).neg).differentiable
          one_ne_zero).comp differentiable_snd)
    rw [timeDeriv_fun_sum _ fun k _ => hdk k p]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := timeDeriv_mul_slice (fun s => hasDerivAt_component_path (hd s).hasDerivAt k)
      ((((contDiff_const.mul (contDiff_profileDeriv hη k)).neg).differentiable one_ne_zero) :
        Differentiable ℝ fun z => -(e * profileDeriv η k z))
    exact congrFun this p
  rw [ht, Finset.sum_congr rfl fun k _ => hj k, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  ring


end Model

/-! ### The self-force as a convolution -/

section Force

variable {e : ℝ} {η : E3 → ℝ} {R : ℝ → E3}

theorem hasCompactSupport_of_far {G : E3 → ℝ} {b : ℝ} (hG : ∀ z : E3, b < ‖z‖ → G z = 0) :
    HasCompactSupport G :=
  HasCompactSupport.intro (isCompact_closedBall 0 b) fun z hz => hG z (by simpa using hz)

/-- The charge against a continuous function of space-time is integrable over space. -/
theorem integrable_profile_mul {G : E3 → ℝ} (hG : Continuous G) {b : ℝ}
    (hGb : ∀ z : E3, b < ‖z‖ → G z = 0) {g : ℝ × E3 → ℝ} (hg : Continuous g) (t : ℝ) :
    Integrable fun x => G x * g (t, x) :=
  (hG.mul (hg.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
    (hasCompactSupport_of_far hGb).mul_right

/-- The retarded integral of a continuous slice in a cylinder is continuous. -/
theorem continuous_retardedIntegral_slice {b : ℝ} {c : ℝ → ℝ} {G : E3 → ℝ} (hc : Continuous c)
    (hG : Continuous G) (hGb : ∀ z : E3, b < ‖z‖ → G z = 0) :
    Continuous (retardedIntegral fun q : ℝ × E3 => c q.1 * G q.2) :=
  continuous_retardedIntegral ((hc.comp continuous_fst).mul (hG.comp continuous_snd))
    (spatialSupport_slice c hGb).subluminalSupport

/-- **Integration by parts** against the charge: `∫ e∂ₖη Φ(t, ·) = −∫ eη ∂ₖΦ(t, ·)`. -/
theorem integral_profileDeriv_mul (hη : ContDiff ℝ 2 η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {Φ : ℝ × E3 → ℝ} (hΦ : ContDiff ℝ 1 Φ) (t : ℝ)
    (k : Fin 3) :
    ∫ x, e * profileDeriv η k x * Φ (t, x) = -∫ x, e * η x * spaceDeriv k Φ (t, x) := by
  have hρ : ContDiff ℝ 1 (restCharge e η) :=
    (contDiff_const.mul (hη.comp contDiff_snd)).of_le (by norm_num)
  have h := integral_mul_spaceDeriv (w := fun z => Φ (t, z))
    (hΦ.comp (contDiff_const.prodMk contDiff_id)) hρ (spatialSupport_restCharge hb) t k
  rw [spaceDeriv_restCharge hη] at h
  have h1 : (fun x => e * profileDeriv η k x * Φ (t, x)) =
      fun z => Φ (t, z) * (e * profileDeriv η k z) := funext fun x => by ring
  have h2 : (fun x => e * η x * spaceDeriv k Φ (t, x)) =
      fun z => fderiv ℝ (fun z => Φ (t, z)) z (EuclideanSpace.single k 1) *
        restCharge e η (t, z) := by
    funext x
    rw [← spaceDeriv_eq_fderiv_slice ((hΦ.differentiable one_ne_zero) (t, x)) k]
    simp only [restCharge]
    ring
  rw [h1, h2]
  exact h

/-- **The self-force before the isotropy**:
`Fᵢ(t) = Σₖ ∫ eη R[(Rₖ − Rₖ(t)) ⊗ e∂ᵢ∂ₖη](t, ·) − ∫ eη R[R̈ᵢ ⊗ eη](t, ·)`. -/
theorem linearSelfForce_eq_sum (hη : ContDiff ℝ 2 η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hR : ContDiff ℝ 2 R) (t : ℝ) (i : Fin 3) :
    linearSelfForce e η R t i =
      ∑ k, (∫ x, e * η x *
        retardedIntegral (fun q => (R q.1 k - R t k) * (e * profileDeriv2 η i k q.2)) (t, x)) -
      ∫ x, e * η x * retardedIntegral (fun q => deriv (deriv R) q.1 i * (e * η q.2)) (t, x) := by
  have hηc : Continuous η := hη.continuous
  have hcR : ∀ k, Continuous fun s => R s k := fun k =>
    ((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).continuous.comp hR.continuous)
  have hcA : Continuous fun s => deriv (deriv R) s i :=
    (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.comp
      (((contDiff_succ_iff_deriv (n := 0)).mp (contDiff_deriv_path hR)).2.2.continuous)
  have hG2 : ∀ k, Continuous fun z => e * profileDeriv2 η i k z := fun k =>
    continuous_const.mul (continuous_profileDeriv2 hη i k)
  have hG2b : ∀ k, ∀ z : E3, b < ‖z‖ → e * profileDeriv2 η i k z = 0 := fun k z hz => by
    rw [profileDeriv2_eq_zero hb i k hz, mul_zero]
  have hηb : ∀ z : E3, b < ‖z‖ → e * η z = 0 := fun z hz => by rw [hb z hz, mul_zero]
  have heη : Continuous fun z => e * η z := continuous_const.mul hηc
  have heηb : ∀ z : E3, b < ‖z‖ → e * η z = 0 := hηb
  -- the retarded integrals that appear
  set A : Fin 3 → ℝ × E3 → ℝ := fun k =>
    retardedIntegral fun q => R q.1 k * (e * profileDeriv2 η i k q.2) with hA
  set S : Fin 3 → ℝ × E3 → ℝ := fun k =>
    retardedIntegral fun q => (fun _ => (1 : ℝ)) q.1 * (e * profileDeriv2 η i k q.2) with hS
  set B : ℝ × E3 → ℝ :=
    retardedIntegral fun q => deriv (deriv R) q.1 i * (e * η q.2) with hB
  have hAc : ∀ k, Continuous (A k) := fun k =>
    continuous_retardedIntegral_slice (hcR k) (hG2 k) (hG2b k)
  have hSc : ∀ k, Continuous (S k) := fun k =>
    continuous_retardedIntegral_slice continuous_const (hG2 k) (hG2b k)
  have hBc : Continuous B := continuous_retardedIntegral_slice hcA heη heηb
  -- the term `ρ₀ E₁`
  have hterm1 : ∫ x, restCharge e η (t, x) * linearField e η R i (t, x) =
      ∑ k, (∫ x, e * η x * A k (t, x)) - ∫ x, e * η x * B (t, x) := by
    have hpt : (fun x => restCharge e η (t, x) * linearField e η R i (t, x)) =
        fun x => (∑ k, e * η x * A k (t, x)) - e * η x * B (t, x) := by
      funext x
      rw [linearField_eq hη hb hR i (t, x), mul_sub, Finset.mul_sum]
      rfl
    rw [hpt, integral_sub (integrable_finsetSum _ fun k _ =>
      integrable_profile_mul heη heηb (hAc k) t) (integrable_profile_mul heη heηb hBc t),
      integral_finsetSum _ fun k _ => integrable_profile_mul heη heηb (hAc k) t]
  -- the term `ρ₁ E₀`
  set Φ : ℝ × E3 → ℝ := retardedIntegral fun q => e * profileDeriv η i q.2 with hΦ
  have hΦs : ContDiff ℝ 1 (fun q : ℝ × E3 => e * profileDeriv η i q.2) :=
    contDiff_const.mul ((contDiff_profileDeriv hη i).comp contDiff_snd)
  have hΦsupp : SpatialSupport b (fun q : ℝ × E3 => e * profileDeriv η i q.2) :=
    spatialSupport_static (G := fun z => e * profileDeriv η i z) fun z hz => by
      rw [profileDeriv_eq_zero hb i hz, mul_zero]
  have hΦc : ContDiff ℝ 1 Φ := contDiff_retardedIntegral hΦs hΦsupp.subluminalSupport
  have hdΦ : ∀ k, spaceDeriv k Φ = S k := fun k => by
    rw [hΦ, spaceDeriv_retardedIntegral hΦs hΦsupp.subluminalSupport,
      spaceDeriv_static_profileDeriv hη i k]
    simp only [hS, one_mul]
    congr 1
    funext q
    rw [profileDeriv2_comm hη k i]
  have hterm2 : ∫ x, linearCharge e η R (t, x) * restField e η i (t, x) =
      -∑ k, R t k * ∫ x, e * η x * S k (t, x) := by
    have hpt : (fun x => linearCharge e η R (t, x) * restField e η i (t, x)) =
        fun x => ∑ k, R t k * (e * profileDeriv η k x * Φ (t, x)) := by
      funext x
      rw [restField_eq hη hb i (t, x), linearCharge_eq_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hΦ]
      ring
    have hint : ∀ k, Integrable fun x => e * profileDeriv η k x * Φ (t, x) := fun k =>
      integrable_profile_mul (G := fun z => e * profileDeriv η k z) (b := b)
        (continuous_const.mul (contDiff_profileDeriv hη k).continuous)
        (fun z hz => by simp [profileDeriv_eq_zero hb k hz]) hΦc.continuous t
    rw [hpt, integral_finsetSum _ fun k _ => (hint k).const_mul _, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_profileDeriv_mul hη hb hΦc t k, hdΦ k, mul_neg]
  -- the combination
  have hcomb : ∀ k, (∫ x, e * η x * A k (t, x)) - R t k * ∫ x, e * η x * S k (t, x) =
      ∫ x, e * η x *
        retardedIntegral (fun q => (R q.1 k - R t k) * (e * profileDeriv2 η i k q.2)) (t, x) := by
    intro k
    rw [← integral_const_mul, ← integral_sub (integrable_profile_mul heη heηb (hAc k) t)
      ((integrable_profile_mul heη heηb (hSc k) t).const_mul _)]
    congr 1
    funext x
    have hsplit : retardedIntegral (fun q => (R q.1 k - R t k) * (e * profileDeriv2 η i k q.2))
        (t, x) = A k (t, x) - R t k * S k (t, x) := by
      have h1 : (fun q : ℝ × E3 => (R q.1 k - R t k) * (e * profileDeriv2 η i k q.2)) =
          fun q => R q.1 k * (e * profileDeriv2 η i k q.2) -
            R t k * ((fun _ => (1 : ℝ)) q.1 * (e * profileDeriv2 η i k q.2)) := by
        funext q
        ring
      rw [h1, retardedIntegral_sub' (f := fun q => R q.1 k * (e * profileDeriv2 η i k q.2))
          (g := fun q => R t k * ((fun _ => (1 : ℝ)) q.1 * (e * profileDeriv2 η i k q.2)))
          (((hcR k).comp continuous_fst).mul ((hG2 k).comp continuous_snd))
          (continuous_const.mul ((continuous_const.comp continuous_fst).mul
          ((hG2 k).comp continuous_snd))) (spatialSupport_slice (fun s => R s k) (hG2b k))
          (fun q hq => by simp [hG2b k _ hq]), retardedIntegral_const_mul]
    rw [hsplit]
    ring
  rw [linearSelfForce, hterm1, hterm2, ← Finset.sum_congr rfl fun k _ => hcomb k,
    Finset.sum_sub_distrib]
  ring

/-- **The retarded identity for the Laplacian of the profile**: for a `C²` function `h` of the
time with `h(t) = 0`, `Σⱼ R[h ⊗ ∂ⱼ²η](t, x) = R[ḧ ⊗ η](t, x)`. This is
`∫ □f(t − ‖y‖, x − y)/(4π‖y‖) dy = f(t, x)` for `f = h ⊗ η`. -/
theorem sum_retardedIntegral_profileDeriv2 (hη : ContDiff ℝ 2 η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) {t : ℝ}
    (ht : h t = 0) (x : E3) :
    ∑ j, retardedIntegral (fun q => h q.1 * profileDeriv2 η j j q.2) (t, x) =
      retardedIntegral (fun q => deriv (deriv h) q.1 * η q.2) (t, x) := by
  set f : ℝ × E3 → ℝ := fun q => h q.1 * η q.2 with hf
  have hf2 : ContDiff ℝ 2 f := contDiff_mul_slice hh hη
  have hfs : SpatialSupport b f := spatialSupport_slice h hb
  have hw := integral_wave_div_norm_of_subluminalSupport hf2 hfs.subluminalSupport t x
  have hh1 : ContDiff ℝ 1 (deriv h) := ((contDiff_succ_iff_deriv (n := 1)).mp hh).2.2
  have hh0 : Continuous (deriv (deriv h)) :=
    ((contDiff_succ_iff_deriv (n := 0)).mp hh1).2.2.continuous
  have hdh : ∀ s, HasDerivAt h (deriv h s) s := fun s =>
    ((hh.differentiable (by norm_num)) s).hasDerivAt
  have hdh' : ∀ s, HasDerivAt (deriv h) (deriv (deriv h) s) s := fun s =>
    ((hh1.differentiable one_ne_zero) s).hasDerivAt
  have hηd : Differentiable ℝ η := hη.differentiable (by norm_num)
  have hwave : waveOperator f =
      fun q => deriv (deriv h) q.1 * η q.2 - ∑ j, h q.1 * profileDeriv2 η j j q.2 := by
    funext q
    have ht1 : timeDeriv f = fun q => deriv h q.1 * η q.2 := timeDeriv_mul_slice hdh hηd
    have ht2 : timeDeriv (fun q : ℝ × E3 => deriv h q.1 * η q.2) =
        fun q => deriv (deriv h) q.1 * η q.2 := timeDeriv_mul_slice hdh' hηd
    have hs : ∀ j, spaceDeriv j (spaceDeriv j f) =
        fun q => h q.1 * profileDeriv2 η j j q.2 := fun j => by
      rw [spaceDeriv_mul_slice (hh.differentiable (by norm_num)) hηd j]
      exact spaceDeriv_mul_slice (hh.differentiable (by norm_num))
        ((contDiff_profileDeriv hη j).differentiable one_ne_zero) j
    simp only [waveOperator, ht1, ht2, hs]
  have hzero : retardedIntegral (waveOperator f) (t, x) = 0 := by
    rw [retardedIntegral_apply, hw, hf]
    simp [ht]
  have hc1 : Continuous fun q : ℝ × E3 => deriv (deriv h) q.1 * η q.2 :=
    (hh0.comp continuous_fst).mul (hη.continuous.comp continuous_snd)
  have hc2 : ∀ j, Continuous fun q : ℝ × E3 => h q.1 * profileDeriv2 η j j q.2 := fun j =>
    (hh.continuous.comp continuous_fst).mul ((continuous_profileDeriv2 hη j j).comp
      continuous_snd)
  have hs2 : ∀ j, SpatialSupport b fun q : ℝ × E3 => h q.1 * profileDeriv2 η j j q.2 :=
    fun j => spatialSupport_slice h fun z hz => profileDeriv2_eq_zero hb j j hz
  rw [hwave, retardedIntegral_sub' hc1 (continuous_finsetSum _ fun j _ => hc2 j)
    (spatialSupport_slice _ hb) (fun q hq => by simp [(hs2 _) q hq]),
    retardedIntegral_sum' hc2 hs2] at hzero
  linarith

/-- The double integral of the charge against a retarded slice:
`∫ eη(x) R[g ⊗ eG](t, x) dx = e² ∫∫ η(x) (g(t − ‖y‖)/(4π‖y‖)) G(x − y) dy dx`. -/
theorem integral_mul_retardedIntegral_slice (e : ℝ) (η : E3 → ℝ) (g : ℝ → ℝ) (G : E3 → ℝ)
    (t : ℝ) :
    ∫ x, e * η x * retardedIntegral (fun q => g q.1 * (e * G q.2)) (t, x) =
      e ^ 2 * ∫ x, η x * ∫ y, g (t - ‖y‖) / (4 * π * ‖y‖) * G (x - y) := by
  have hin : ∀ x, retardedIntegral (fun q => g q.1 * (e * G q.2)) (t, x) =
      e * ∫ y, g (t - ‖y‖) / (4 * π * ‖y‖) * G (x - y) := fun x => by
    rw [retardedIntegral_apply, ← integral_const_mul]
    congr 1
    funext y
    simp only
    ring
  calc ∫ x, e * η x * retardedIntegral (fun q => g q.1 * (e * G q.2)) (t, x) =
      ∫ x, e ^ 2 * (η x * ∫ y, g (t - ‖y‖) / (4 * π * ‖y‖) * G (x - y)) := by
        congr 1
        funext x
        rw [hin x]
        ring
    _ = _ := integral_const_mul _ _

/-- **The linear self-force of an isotropic charge** (Landau–Lifshitz §75 in the linear model,
S1): for a `C²` profile `η` vanishing outside `‖z‖ ≤ b` and invariant under the linear isometries
of space, and a `C²` path `R`,

  `Fᵢ(t) = −(2/3) ∫ eη(x) R[R̈ᵢ ⊗ eη](t, x) dx = −(2/3) e² ∫∫ η(x) η(x − y) R̈ᵢ(t − ‖y‖)/(4π‖y‖)`.

The scalar potential contributes `+1/3` and the vector potential `−1` of this integral. -/
theorem linearSelfForce_eq (hη : ContDiff ℝ 2 η) {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (hR : ContDiff ℝ 2 R) (t : ℝ)
    (i : Fin 3) :
    linearSelfForce e η R t i =
      -(2 / 3) * ∫ x, e * η x *
        retardedIntegral (fun q => deriv (deriv R) q.1 i * (e * η q.2)) (t, x) := by
  rw [linearSelfForce_eq_sum hη hb hR t i]
  set T := ∫ x, e * η x *
    retardedIntegral (fun q => deriv (deriv R) q.1 i * (e * η q.2)) (t, x) with hT
  set g : ℝ → ℝ := fun s => R s i - R t i with hg
  have hKinv : ∀ (h : ℝ → ℝ) (f : E3 ≃ₗᵢ[ℝ] E3) (y : E3),
      (fun y : E3 => h (t - ‖y‖) / (4 * π * ‖y‖)) (f y) =
        (fun y : E3 => h (t - ‖y‖) / (4 * π * ‖y‖)) y := fun h f y => by
    simp only [LinearIsometryEquiv.norm_map]
  -- the terms off the diagonal vanish
  have hoff : ∀ k, k ≠ i → ∫ x, e * η x *
      retardedIntegral (fun q => (R q.1 k - R t k) * (e * profileDeriv2 η i k q.2)) (t, x) =
        0 := by
    intro k hk
    rw [integral_mul_retardedIntegral_slice e η (fun s => R s k - R t k),
      integral_mul_profileDeriv2_eq_zero hrot hη (hKinv (fun s => R s k - R t k)) (Ne.symm hk),
      mul_zero]
  rw [Finset.sum_eq_single i (fun k _ hk => hoff k hk) (by simp)]
  -- the diagonal terms are equal
  set N : Fin 3 → ℝ := fun j => ∫ x, e * η x *
    retardedIntegral (fun q => g q.1 * (e * profileDeriv2 η j j q.2)) (t, x) with hN
  have hdiag : ∀ j, N j = N i := fun j => by
    simp only [hN]
    rw [integral_mul_retardedIntegral_slice, integral_mul_retardedIntegral_slice,
      integral_mul_profileDeriv2_diag hrot hη (hKinv g) j i]
  -- the trace
  have hgC : ContDiff ℝ 2 g :=
    ((EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff.comp hR).sub contDiff_const
  have hgdd : deriv (deriv g) = fun s => deriv (deriv R) s i := by
    have hd1 : deriv g = fun s => deriv R s i := funext fun s =>
      ((hasDerivAt_component_path ((hR.differentiable (by norm_num)) s).hasDerivAt i).sub_const
        (R t i)).deriv
    rw [hd1]
    funext s
    exact (hasDerivAt_component_path (((contDiff_deriv_path hR).differentiable one_ne_zero)
      s).hasDerivAt i).deriv
  have htrace : ∑ j, N j = T := by
    simp only [hN]
    have hint : ∀ j, Integrable fun x => e * η x *
        retardedIntegral (fun q => g q.1 * (e * profileDeriv2 η j j q.2)) (t, x) := fun j =>
      integrable_profile_mul (G := fun z => e * η z) (b := b) (continuous_const.mul hη.continuous)
        (fun z hz => by simp [hb z hz])
        (continuous_retardedIntegral_slice (G := fun z => e * profileDeriv2 η j j z) (b := b)
          hgC.continuous (continuous_const.mul (continuous_profileDeriv2 hη j j))
          fun z hz => by simp [profileDeriv2_eq_zero hb j j hz]) t
    rw [← integral_finsetSum _ fun j _ => hint j, hT]
    congr 1
    funext x
    rw [← Finset.mul_sum]
    congr 1
    have h1 : ∀ j, retardedIntegral (fun q => g q.1 * (e * profileDeriv2 η j j q.2)) (t, x) =
        e * retardedIntegral (fun q => g q.1 * profileDeriv2 η j j q.2) (t, x) := fun j => by
      rw [← retardedIntegral_const_mul]
      congr 1
      funext q
      ring
    have h2 : retardedIntegral (fun q => deriv (deriv R) q.1 i * (e * η q.2)) (t, x) =
        e * retardedIntegral (fun q => deriv (deriv g) q.1 * η q.2) (t, x) := by
      rw [← retardedIntegral_const_mul, hgdd]
      congr 1
      funext q
      ring
    simp only [h1, ← Finset.mul_sum, h2]
    rw [sum_retardedIntegral_profileDeriv2 hη hb hgC (by simp [hg]) x]
  have h3 : 3 * N i = T := by
    rw [← htrace, Fin.sum_univ_three, hdiag 0, hdiag 1, hdiag 2]
    ring
  have hNi : N i = ∫ x, e * η x *
      retardedIntegral (fun q => (R q.1 i - R t i) * (e * profileDeriv2 η i i q.2)) (t, x) := rfl
  rw [← hNi]
  linarith

end Force

/-! ### The self-force as a distributed delay -/

open SmoothGeometry.DistributedDelay

/-- The weight `w(x, y) = (2/3) e² η(x) η(x − y)/(4π‖y‖)` of the self-force on `ℝ³ × ℝ³`. -/
def selfWeight (e : ℝ) (η : E3 → ℝ) (p : E3 × E3) : ℝ :=
  2 / 3 * e ^ 2 * (η p.1 * η (p.1 - p.2)) * Potential.newtonKernel p.2

/-- The delay `τ(x, y) = ‖y‖` of the self-force, the light time across the charge. -/
def selfDelay (p : E3 × E3) : ℝ := ‖p.2‖

section Delay

variable {e : ℝ} {η : E3 → ℝ} {R : ℝ → E3}

theorem measurable_newtonKernel : Measurable Potential.newtonKernel := by
  unfold Potential.newtonKernel
  exact (continuous_const.mul continuous_norm).measurable.inv

theorem selfWeight_eq_zero_of_far {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {p : E3 × E3}
    (hp : selfWeight e η p ≠ 0) : ‖p.2‖ ≤ 2 * b := by
  have h1 : η p.1 ≠ 0 := fun h => hp (by simp [selfWeight, h])
  have h2 : η (p.1 - p.2) ≠ 0 := fun h => hp (by simp [selfWeight, h])
  have hx : ‖p.1‖ ≤ b := not_lt.mp fun h => h1 (hb _ h)
  have hy : ‖p.1 - p.2‖ ≤ b := not_lt.mp fun h => h2 (hb _ h)
  have := norm_le_norm_add_norm_sub' p.2 p.1
  rw [norm_sub_rev] at this
  linarith

/-- **The delay datum of the self-force**: the weight `selfWeight` is integrable on `ℝ³ × ℝ³`,
and the delay `‖y‖` is at most `2b` on its support. -/
theorem selfDelayData (hη : Continuous η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) :
    DelayData (volume : Measure (E3 × E3)) (selfWeight e η) selfDelay (2 * b) where
  integrable := by
    obtain ⟨M, hM⟩ := hη.bounded_above_of_compact_support (hasCompactSupport_of_far hb)
    have hηi : Integrable η := hη.integrable_of_hasCompactSupport (hasCompactSupport_of_far hb)
    have hk := integrable_indicator_newtonKernel 1 (2 * b)
    have hprod : Integrable (fun p : E3 × E3 => |η p.1| *
        (closedBall (0 : E3) (2 * b)).indicator (fun y => 1 * Potential.newtonKernel y) p.2)
        ((volume : Measure E3).prod volume) := hηi.abs.mul_prod hk
    rw [Measure.volume_eq_prod]
    refine (hprod.const_mul (2 / 3 * e ^ 2 * M)).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (((measurable_const.mul ((hη.comp continuous_fst).measurable.mul
        (hη.comp (continuous_fst.sub continuous_snd)).measurable)).mul
        (measurable_newtonKernel.comp measurable_snd))).aestronglyMeasurable
    · by_cases hp : selfWeight e η p = 0
      · rw [hp, norm_zero]
        have : 0 ≤ M := (norm_nonneg _).trans (hM 0)
        have h0 : 0 ≤ (closedBall (0 : E3) (2 * b)).indicator
            (fun y => 1 * Potential.newtonKernel y) p.2 :=
          Set.indicator_nonneg (fun y _ => by
            rw [one_mul, Potential.newtonKernel]
            positivity) _
        positivity
      · have hy : p.2 ∈ closedBall (0 : E3) (2 * b) := by
          rw [mem_closedBall_zero_iff]
          exact selfWeight_eq_zero_of_far hb hp
        rw [Set.indicator_of_mem hy, one_mul, selfWeight, Real.norm_eq_abs]
        have hN : 0 ≤ Potential.newtonKernel p.2 := by
          rw [Potential.newtonKernel]
          positivity
        simp only [abs_mul, abs_of_nonneg hN, abs_of_nonneg (show (0 : ℝ) ≤ 2 / 3 by norm_num),
          abs_of_nonneg (sq_nonneg e)]
        have h2 : |η (p.1 - p.2)| ≤ M := by simpa using hM (p.1 - p.2)
        have : 2 / 3 * e ^ 2 * (|η p.1| * |η (p.1 - p.2)|) * Potential.newtonKernel p.2 ≤
            2 / 3 * e ^ 2 * (|η p.1| * M) * Potential.newtonKernel p.2 := by
          gcongr
        linarith
  measurable := (continuous_norm.comp continuous_snd).measurable
  nonneg _ := norm_nonneg _
  bound_nonneg := by linarith
  le _ hp := selfWeight_eq_zero_of_far hb hp

/-- The delay is positive almost everywhere on `ℝ³ × ℝ³`. -/
theorem ae_selfDelay_pos : ∀ᵐ p ∂(volume : Measure (E3 × E3)), 0 < selfDelay p := by
  rw [Measure.volume_eq_prod]
  have h : {p : E3 × E3 | ¬ 0 < selfDelay p} = univ ×ˢ {0} := by
    ext p
    simp [selfDelay]
  rw [ae_iff, h, Measure.prod_prod, measure_singleton, mul_zero]

theorem selfWeight_nonneg (hη0 : ∀ z, 0 ≤ η z) (p : E3 × E3) : 0 ≤ selfWeight e η p := by
  have hN : 0 ≤ Potential.newtonKernel p.2 := by
    rw [Potential.newtonKernel]
    positivity
  have := hη0 p.1
  have := hη0 (p.1 - p.2)
  unfold selfWeight
  positivity

/-- The iterated form of an integral against the self weight. -/
theorem integral_selfWeight_mul (hη : Continuous η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {g : E3 → ℝ} (hg : Continuous g) :
    ∫ p, selfWeight e η p * g p.2 =
      2 / 3 * e ^ 2 * ∫ x, η x * ∫ y, Potential.newtonKernel y * g y * η (x - y) := by
  obtain ⟨C, hC⟩ := isCompact_closedBall (0 : E3) (2 * b) |>.exists_bound_of_continuousOn
    hg.continuousOn
  have hint : Integrable (fun p : E3 × E3 => selfWeight e η p * g p.2)
      ((volume : Measure E3).prod volume) := by
    have hd := (selfDelayData (e := e) hη hb0 hb).integrable
    rw [Measure.volume_eq_prod] at hd
    refine (hd.abs.mul_const C).mono' (hd.aestronglyMeasurable.mul
      (hg.comp continuous_snd).aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
    by_cases hp : selfWeight e η p = 0
    · simp [hp]
    · rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := hC p.2 (by rw [mem_closedBall_zero_iff]; exact selfWeight_eq_zero_of_far hb hp)
      simpa using this
  rw [Measure.volume_eq_prod, integral_prod _ hint, ← integral_const_mul]
  congr 1
  funext x
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1
  funext y
  simp only [selfWeight]
  ring

/-- **The linear self-force as a distributed delay** (S1):
`Fᵢ(t) = −∫∫ w(x, y) R̈ᵢ(t − ‖y‖) dx dy` with `w = selfWeight`, so that `F = −K R̈` with the
operator of `selfDelayData`, of finite memory `2b`. -/
theorem linearSelfForce_eq_integral (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    (hR : ContDiff ℝ 2 R) (t : ℝ) (i : Fin 3) :
    linearSelfForce e η R t i = -∫ p, selfWeight e η p * deriv (deriv R) (t - ‖p.2‖) i := by
  have hA : Continuous fun s => deriv (deriv R) s i :=
    (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.comp
      (((contDiff_succ_iff_deriv (n := 0)).mp (contDiff_deriv_path hR)).2.2.continuous)
  rw [linearSelfForce_eq hη hb hrot hR t i, integral_mul_retardedIntegral_slice e η
    (fun s => deriv (deriv R) s i) η t,
    integral_selfWeight_mul hη.continuous hb0 hb (g := fun y => deriv (deriv R) (t - ‖y‖) i)
      (hA.comp (continuous_const.sub continuous_norm))]
  have h : ∀ x, ∫ y, deriv (deriv R) (t - ‖y‖) i / (4 * π * ‖y‖) * η (x - y) =
      ∫ y, Potential.newtonKernel y * deriv (deriv R) (t - ‖y‖) i * η (x - y) := fun x => by
    congr 1
    funext y
    rw [Potential.newtonKernel]
    ring
  simp only [h]
  ring

theorem continuous_deriv_deriv (hR : ContDiff ℝ 2 R) : Continuous (deriv (deriv R)) :=
  ((contDiff_succ_iff_deriv (n := 0)).mp (contDiff_deriv_path hR)).2.2.continuous

/-- **The linear self-force is `−K R̈`** for the delay datum `selfDelayData`. -/
theorem linearSelfForce_eq_delayOp (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    (hR : ContDiff ℝ 2 R) (t : ℝ) (i : Fin 3) :
    linearSelfForce e η R t i =
      -(delayOp volume (selfWeight e η) selfDelay (deriv (deriv R)) t) i := by
  rw [linearSelfForce_eq_integral hη hb0 hb hrot hR t i, delayOp]
  congr 1
  have h := (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).integral_comp_comm
    ((selfDelayData (e := e) hη.continuous hb0 hb).integrable_smul (continuous_deriv_deriv hR) t)
  simpa [selfDelay] using h

/-- **Finite memory**: the linear self-force at `t` depends only on the acceleration on
`[t − 2b, t]`. -/
theorem linearSelfForce_congr (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {R₁ R₂ : ℝ → E3} (h₁ : ContDiff ℝ 2 R₁) (h₂ : ContDiff ℝ 2 R₂) {t : ℝ}
    (h : ∀ s ∈ Icc (t - 2 * b) t, deriv (deriv R₁) s = deriv (deriv R₂) s) (i : Fin 3) :
    linearSelfForce e η R₁ t i = linearSelfForce e η R₂ t i := by
  rw [linearSelfForce_eq_delayOp hη hb0 hb hrot h₁, linearSelfForce_eq_delayOp hη hb0 hb hrot h₂,
    (selfDelayData hη.continuous hb0 hb).delayOp_congr h]

/-- **The electromagnetic mass**: `∫ w = (4/3) U` with the self-energy `U`, which is the mass
`δm` of `selfMass_isotropic` for an isotropic profile. -/
theorem integral_selfWeight (hη : Continuous η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) :
    ∫ p, selfWeight e η p = 4 / 3 * selfEnergy e η := by
  have h := integral_selfWeight_mul (e := e) hη hb0 hb (g := fun _ => 1) continuous_const
  simp only [mul_one] at h
  rw [h, selfEnergy]
  ring

/-- **The damping constant**: `∫ w τ = (2/3)(e²/4π)(∫ η)²`, independent of the size of the
charge. -/
theorem integral_selfWeight_mul_delay (hη : Continuous η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) :
    ∫ p, selfWeight e η p * selfDelay p = 2 / 3 * (e ^ 2 / (4 * π)) * (∫ z, η z) ^ 2 := by
  have h := integral_selfWeight_mul (e := e) hη hb0 hb (g := fun y => ‖y‖) continuous_norm
  simp only [selfDelay]
  rw [h]
  have hin : ∀ x, ∫ y, Potential.newtonKernel y * ‖y‖ * η (x - y) = (4 * π)⁻¹ * ∫ z, η z := by
    intro x
    rw [← integral_sub_left_eq_self (fun z => η z) volume x, ← integral_const_mul]
    refine integral_congr_ae ((Measure.ae_ne volume (0 : E3)).mono fun y hy => ?_)
    have : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    simp only [Potential.newtonKernel]
    field_simp
  simp only [hin]
  rw [integral_mul_const]
  ring

/-- **An inertial motion without force is an exact solution**: the linear self-force of
`R(t) = R₀ + tV` vanishes. -/
theorem linearSelfForce_inertial (hη : ContDiff ℝ 2 η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    (R₀ V : E3) (t : ℝ) (i : Fin 3) :
    linearSelfForce e η (fun s => R₀ + s • V) t i = 0 := by
  have hR : ContDiff ℝ 2 (fun s : ℝ => R₀ + s • V) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hd : deriv (fun s : ℝ => R₀ + s • V) = fun _ => V := funext fun s => by
    have := ((hasDerivAt_id' s).smul_const V).const_add R₀
    simpa using this.deriv
  rw [linearSelfForce_eq hη hb hrot hR t i, hd]
  simp

/-- **Finite memory, for the path**: if two `C²` paths agree on `[t − 2b, t]` with `b > 0`, their
linear self-forces at `t` agree. -/
theorem linearSelfForce_congr_path (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 < b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {R₁ R₂ : ℝ → E3} (h₁ : ContDiff ℝ 2 R₁) (h₂ : ContDiff ℝ 2 R₂) {t : ℝ}
    (h : ∀ s ∈ Icc (t - 2 * b) t, R₁ s = R₂ s) (i : Fin 3) :
    linearSelfForce e η R₁ t i = linearSelfForce e η R₂ t i := by
  refine linearSelfForce_congr hη hb0.le hb hrot h₁ h₂ (fun s hs => ?_) i
  have hcl : IsClosed {s | deriv (deriv R₁) s = deriv (deriv R₂) s} :=
    isClosed_eq (continuous_deriv_deriv h₁) (continuous_deriv_deriv h₂)
  have hsub : Ioo (t - 2 * b) t ⊆ {s | deriv (deriv R₁) s = deriv (deriv R₂) s} := by
    intro s hs'
    have hev : R₁ =ᶠ[𝓝 s] R₂ :=
      Filter.eventually_of_mem (Ioo_mem_nhds hs'.1 hs'.2) fun r hr => h r (Ioo_subset_Icc_self hr)
    have hev' : deriv R₁ =ᶠ[𝓝 s] deriv R₂ := hev.deriv
    exact hev'.deriv_eq
  have hlt : t - 2 * b < t := by linarith
  have := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ioo hlt.ne] at this
  exact this hs


end Delay

/-! ### The equation of motion (S2) -/

section Motion

variable {e : ℝ} {η : E3 → ℝ}

/-- The equation of motion `m₀ R̈ = F + F_self[R]` in components is the delay equation
`m₀ R̈ + K R̈ = F` of `selfDelayData`. -/
theorem linearMotion_iff (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {R : ℝ → E3} (hR : ContDiff ℝ 2 R) (m₀ : ℝ) (F : ℝ → E3) (t : ℝ) :
    (∀ i, m₀ * deriv (deriv R) t i = F t i + linearSelfForce e η R t i) ↔
      m₀ • deriv (deriv R) t +
        delayOp volume (selfWeight e η) selfDelay (deriv (deriv R)) t = F t := by
  simp only [linearSelfForce_eq_delayOp hη hb0 hb hrot hR]
  constructor
  · intro h
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    linarith [h i]
  · intro h i
    have := congrArg (fun v : E3 => v i) h
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at this
    linarith

/-- **An inertial motion without force is an exact solution** of `m₀ R̈ = F + F_self[R]`. -/
theorem linearMotion_inertial (hη : ContDiff ℝ 2 η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    (m₀ : ℝ) (R₀ V : E3) (t : ℝ) (i : Fin 3) :
    m₀ * deriv (deriv fun s : ℝ => R₀ + s • V) t i =
      (fun _ : ℝ => (0 : E3)) t i + linearSelfForce e η (fun s => R₀ + s • V) t i := by
  have hd : deriv (fun s : ℝ => R₀ + s • V) = fun _ => V := funext fun s => by
    have := ((hasDerivAt_id' s).smul_const V).const_add R₀
    simpa using this.deriv
  rw [linearSelfForce_inertial hη hb hrot, hd]
  simp

/-- The path `h + ∫∫ u` with the acceleration `ḧ + u`. -/
theorem deriv_deriv_add_doublePrimitive {h u : ℝ → E3} (hh : ContDiff ℝ 2 h)
    (hu : Continuous u) :
    deriv (deriv fun s => h s + doublePrimitive u s) = fun s => deriv (deriv h) s + u s :=
  funext fun t => by
    rw [deriv_deriv_add hh (contDiff_doublePrimitive hu), deriv_deriv_doublePrimitive hu]

/-- The delay equation for the path `h + ∫∫ u` from the delay equation of the deviation `u`. -/
theorem delayEq_add_doublePrimitive (hη : Continuous η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {m₀ : ℝ} {F h u : ℝ → E3} (hh : ContDiff ℝ 2 h)
    (hu : Continuous u) {t : ℝ}
    (hut : m₀ • u t + delayOp volume (selfWeight e η) selfDelay u t =
      F t - m₀ • deriv (deriv h) t -
        delayOp volume (selfWeight e η) selfDelay (deriv (deriv h)) t) :
    m₀ • deriv (deriv fun s => h s + doublePrimitive u s) t +
      delayOp volume (selfWeight e η) selfDelay
        (deriv (deriv fun s => h s + doublePrimitive u s)) t = F t := by
  have hd := selfDelayData (e := e) hη hb0 hb
  rw [deriv_deriv_add_doublePrimitive hh hu, smul_add,
    hd.delayOp_add (continuous_deriv_deriv hh) hu]
  calc m₀ • deriv (deriv h) t + m₀ • u t +
        (delayOp volume (selfWeight e η) selfDelay (deriv (deriv h)) t +
          delayOp volume (selfWeight e η) selfDelay u t) =
      (m₀ • u t + delayOp volume (selfWeight e η) selfDelay u t) +
        (m₀ • deriv (deriv h) t +
          delayOp volume (selfWeight e η) selfDelay (deriv (deriv h)) t) := by abel
    _ = F t := by rw [hut]; abel

/-- **Existence at fixed radius** (S2): let `m₀ ≠ 0` and let `γ ≥ 0` be a rate with
`q_γ = ∫ |w| e^{−γτ} < |m₀|` (such rates exist for every `m₀ ≠ 0`, `exists_rate_selfWeight`). For
a `C²` history `h` with bounded acceleration, a continuous force with `‖F(t)‖ ≤ C e^{γt}` for
`t ≥ 0`, and the compatibility of the history with the equation at `t = 0`, there is a `C²` path
`R` that equals `h` for `t ≤ 0` and satisfies `m₀ R̈ = F + F_self[R]` for `t ≥ 0`, with
`‖R̈(t) − ḧ(t)‖ ≤ (C + (|m₀| + q)H) e^{γt}/(|m₀| − q_γ)`. -/
theorem exists_linearMotion (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {m₀ γ : ℝ} (hγ : 0 ≤ γ) (hq : weightNorm volume (selfWeight e η) selfDelay γ < |m₀|)
    {F : ℝ → E3} (hF : Continuous F) {CF : ℝ}
    (hCF : ∀ t, 0 ≤ t → ‖F t‖ ≤ CF * Real.exp (γ * t)) {h : ℝ → E3} (hh : ContDiff ℝ 2 h)
    {H : ℝ} (hH : ∀ t, ‖deriv (deriv h) t‖ ≤ H)
    (hcompat : ∀ i, m₀ * deriv (deriv h) 0 i = F 0 i + linearSelfForce e η h 0 i) :
    ∃ R : ℝ → E3, ContDiff ℝ 2 R ∧ (∀ t ≤ 0, R t = h t) ∧
      (∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R) t i = F t i + linearSelfForce e η R t i) ∧
      ∀ t, ‖deriv (deriv R) t - deriv (deriv h) t‖ ≤
        (CF + (|m₀| + ∫ p, |selfWeight e η p|) * H) /
          (|m₀| - weightNorm volume (selfWeight e η) selfDelay γ) * Real.exp (γ * t) := by
  have hd := selfDelayData (e := e) hη.continuous hb0 hb
  set K : (ℝ → E3) → ℝ → E3 := delayOp volume (selfWeight e η) selfDelay with hK
  set q := ∫ p, |selfWeight e η p| with hqdef
  have hq0 : 0 ≤ q := integral_nonneg fun _ => abs_nonneg _
  have hac : Continuous (deriv (deriv h)) := continuous_deriv_deriv hh
  obtain ⟨f, hf⟩ : ∃ f : ℝ → E3,
      f = fun t => F t - m₀ • deriv (deriv h) t - K (deriv (deriv h)) t := ⟨_, rfl⟩
  have hfc : Continuous f := by
    rw [hf]
    exact (hF.sub (hac.const_smul m₀)).sub (hd.continuous_delayOp hac)
  have hf0 : f 0 = 0 := by
    have := (linearMotion_iff hη hb0 hb hrot hh m₀ F 0).mp hcompat
    rw [hf]
    simp only [hK, ← this]
    abel
  obtain ⟨g, hg⟩ : ∃ g : ℝ → E3, g = fun t => f (max t 0) := ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hg]
    exact hfc.comp (continuous_id.max continuous_const)
  have hg0 : ∀ t ≤ 0, g t = 0 := fun t ht => by simp [hg, max_eq_right ht, hf0]
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  have hgb : ∀ t, 0 ≤ t → ‖g t‖ ≤ (CF + (|m₀| + q) * H) * Real.exp (γ * t) := by
    intro t ht
    have he1 : 1 ≤ Real.exp (γ * t) := Real.one_le_exp (mul_nonneg hγ ht)
    simp only [hg, max_eq_left ht, hf]
    have h1 := norm_sub_le (F t - m₀ • deriv (deriv h) t) (K (deriv (deriv h)) t)
    have h2 := norm_sub_le (F t) (m₀ • deriv (deriv h) t)
    have h3 : ‖m₀ • deriv (deriv h) t‖ ≤ |m₀| * H := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hH t) (abs_nonneg _)
    have h4 : ‖K (deriv (deriv h)) t‖ ≤ q * H := hd.norm_delayOp_le_of_bound hH t
    have h5 : (|m₀| + q) * H ≤ (|m₀| + q) * H * Real.exp (γ * t) :=
      le_mul_of_one_le_right (by positivity) he1
    have h6 := hCF t ht
    calc ‖F t - m₀ • deriv (deriv h) t - K (deriv (deriv h)) t‖ ≤
        CF * Real.exp (γ * t) + (|m₀| + q) * H := by linarith
      _ ≤ CF * Real.exp (γ * t) + (|m₀| + q) * H * Real.exp (γ * t) := by linarith
      _ = (CF + (|m₀| + q) * H) * Real.exp (γ * t) := by ring
  obtain ⟨u, huc, hu0, hueq, hub⟩ := exists_solution hd hγ hq hgc hg0 hgb
  have hDc : ContDiff ℝ 2 (doublePrimitive u) := contDiff_doublePrimitive huc
  refine ⟨fun s => h s + doublePrimitive u s, hh.add hDc, fun t ht => ?_, fun t ht => ?_,
    fun t => ?_⟩
  · simp [doublePrimitive_eq_zero_of_le hu0 ht]
  · rw [linearMotion_iff hη hb0 hb hrot (hh.add hDc)]
    refine delayEq_add_doublePrimitive hη.continuous hb0 hb hh huc ?_
    have := hueq t
    simp only [hg, max_eq_left ht, hf] at this
    exact this
  · rw [deriv_deriv_add_doublePrimitive hh huc, add_sub_cancel_left]
    exact hub t

/-- **Uniqueness at fixed radius** (S2): if `q_γ < |m₀|` for some rate `γ ≥ 0`, two `C²` paths
that agree for `t ≤ 0` and satisfy `m₀ R̈ = F + F_self[R]` for `t ≥ 0` with the same force are
equal. -/
theorem linearMotion_unique (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {m₀ γ : ℝ} (hγ : 0 ≤ γ) (hq : weightNorm volume (selfWeight e η) selfDelay γ < |m₀|)
    {F R₁ R₂ : ℝ → E3} (h₁ : ContDiff ℝ 2 R₁) (h₂ : ContDiff ℝ 2 R₂)
    (hpast : ∀ t ≤ 0, R₁ t = R₂ t)
    (hm₁ : ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R₁) t i = F t i + linearSelfForce e η R₁ t i)
    (hm₂ : ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R₂) t i = F t i + linearSelfForce e η R₂ t i) :
    R₁ = R₂ := by
  have hd := selfDelayData (e := e) hη.continuous hb0 hb
  have hacc0 := deriv_deriv_eq_of_eq_on_Iic h₁ h₂ hpast
  have hacc1 := eq_of_delay hd hγ hq (continuous_deriv_deriv h₁) (continuous_deriv_deriv h₂)
    (fun s hs => hacc0 s hs.2) fun t ht => by
      rw [(linearMotion_iff hη hb0 hb hrot h₁ m₀ F t).mp (hm₁ t ht),
        (linearMotion_iff hη hb0 hb hrot h₂ m₀ F t).mp (hm₂ t ht)]
  have hsub : ∀ s, deriv (deriv fun s => R₁ s - R₂ s) s =
      deriv (deriv R₁) s - deriv (deriv R₂) s := fun s => by
    have h1 : deriv (fun s => R₁ s - R₂ s) = fun s => deriv R₁ s - deriv R₂ s := funext fun s =>
      deriv_sub ((h₁.differentiable (by norm_num)) s) ((h₂.differentiable (by norm_num)) s)
    rw [h1]
    exact deriv_sub (((contDiff_deriv_path h₁).differentiable one_ne_zero) s)
      (((contDiff_deriv_path h₂).differentiable one_ne_zero) s)
  funext t
  have hzero := eq_zero_of_deriv_deriv_eq_zero (h₁.sub h₂) (fun s => by
    rw [hsub s]
    rcases le_or_gt s 0 with hs | hs
    · rw [hacc0 s hs, sub_self]
    · rw [hacc1 s hs.le, sub_self]) (fun s hs => by simp [hpast s hs]) t
  exact sub_eq_zero.mp hzero

/-- A `C¹` function with vanishing derivative on `[0, ∞)` is constant there. -/
theorem eq_of_deriv_eq_zero_Ici {g : ℝ → E3} (hg : ∀ s, HasDerivAt g (deriv g s) s)
    (h0 : ∀ s, 0 ≤ s → deriv g s = 0) {t : ℝ} (ht : 0 ≤ t) : g t = g 0 := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Ici 0) (f := g) (C := 0)
    (fun x _ => (hg x).hasDerivWithinAt) (fun x hx => by rw [h0 x hx, norm_zero])
    (convex_Ici 0) (mem_Ici.mpr le_rfl) ht
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
  exact this

/-- **Uniqueness from the history on `[−2b, 0]`** (S2): if `q_γ < |m₀|` for some rate `γ ≥ 0`, two
`C²` solutions of `m₀ R̈ = F + F_self[R]` for `t ≥ 0` with the same force that agree on
`[−2b, 0]` (`b > 0`) agree for all `t ≥ 0`. -/
theorem linearMotion_unique_of_Icc (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 < b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {m₀ γ : ℝ} (hγ : 0 ≤ γ) (hq : weightNorm volume (selfWeight e η) selfDelay γ < |m₀|)
    {F R₁ R₂ : ℝ → E3} (h₁ : ContDiff ℝ 2 R₁) (h₂ : ContDiff ℝ 2 R₂)
    (hpast : ∀ t ∈ Icc (-(2 * b)) 0, R₁ t = R₂ t)
    (hm₁ : ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R₁) t i = F t i + linearSelfForce e η R₁ t i)
    (hm₂ : ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R₂) t i = F t i + linearSelfForce e η R₂ t i) :
    ∀ t, 0 ≤ t → R₁ t = R₂ t := by
  have hd := selfDelayData (e := e) hη.continuous hb0.le hb
  have hlt : -(2 * b) < 0 := by linarith
  -- the accelerations and the velocities agree on the history
  have hloc : ∀ s ∈ Ioo (-(2 * b)) 0, R₁ =ᶠ[𝓝 s] R₂ := fun s hs =>
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) fun r hr => hpast r (Ioo_subset_Icc_self hr)
  have hcl : ∀ {f g : ℝ → ℝ → E3} (_ : Continuous (f 0)) (_ : Continuous (g 0))
      (_ : ∀ s ∈ Ioo (-(2 * b)) 0, f 0 s = g 0 s), ∀ s ∈ Icc (-(2 * b)) 0, f 0 s = g 0 s := by
    intro f g hf hg hfg s hs
    have hc : IsClosed {s | f 0 s = g 0 s} := isClosed_eq hf hg
    have := hc.closure_subset_iff.mpr hfg
    rw [closure_Ioo hlt.ne] at this
    exact this hs
  have hacc0 : ∀ s ∈ Icc (-(2 * b)) 0, deriv (deriv R₁) s = deriv (deriv R₂) s :=
    hcl (f := fun _ => deriv (deriv R₁)) (g := fun _ => deriv (deriv R₂))
      (continuous_deriv_deriv h₁) (continuous_deriv_deriv h₂) fun s hs =>
        (hloc s hs).deriv.deriv_eq
  have hvel0 : deriv R₁ 0 = deriv R₂ 0 :=
    hcl (f := fun _ => deriv R₁) (g := fun _ => deriv R₂) (contDiff_deriv_path h₁).continuous
      (contDiff_deriv_path h₂).continuous (fun s hs => (hloc s hs).deriv_eq) 0
      ⟨hlt.le, le_rfl⟩
  have hacc1 := eq_of_delay hd hγ hq (continuous_deriv_deriv h₁) (continuous_deriv_deriv h₂)
    hacc0 fun t ht => by
      rw [(linearMotion_iff hη hb0.le hb hrot h₁ m₀ F t).mp (hm₁ t ht),
        (linearMotion_iff hη hb0.le hb hrot h₂ m₀ F t).mp (hm₂ t ht)]
  -- the difference has zero acceleration, velocity and position at `0`
  set g : ℝ → E3 := fun s => R₁ s - R₂ s with hg
  have hgd : ∀ s, HasDerivAt g (deriv R₁ s - deriv R₂ s) s := fun s =>
    ((h₁.differentiable (by norm_num)) s).hasDerivAt.sub
      ((h₂.differentiable (by norm_num)) s).hasDerivAt
  have hgv : ∀ s, HasDerivAt (fun s => deriv R₁ s - deriv R₂ s)
      (deriv (deriv R₁) s - deriv (deriv R₂) s) s := fun s =>
    (((contDiff_deriv_path h₁).differentiable one_ne_zero) s).hasDerivAt.sub
      (((contDiff_deriv_path h₂).differentiable one_ne_zero) s).hasDerivAt
  have hv : ∀ t, 0 ≤ t → deriv R₁ t - deriv R₂ t = 0 := fun t ht => by
    have := eq_of_deriv_eq_zero_Ici (g := fun s => deriv R₁ s - deriv R₂ s)
      (fun s => by rw [(hgv s).deriv]; exact hgv s)
      (fun s hs => by rw [(hgv s).deriv, hacc1 s hs, sub_self]) ht
    rw [this, hvel0, sub_self]
  intro t ht
  have := eq_of_deriv_eq_zero_Ici (g := g) (fun s => by rw [(hgd s).deriv]; exact hgd s)
    (fun s hs => by rw [(hgd s).deriv, hv s hs]) ht
  have h0 : g 0 = 0 := by
    simp only [hg, hpast 0 ⟨hlt.le, le_rfl⟩, sub_self]
  rw [h0] at this
  exact sub_eq_zero.mp this


/-- **Existence and uniqueness at fixed radius** (S2), combined: under the hypotheses of
`exists_linearMotion` there is exactly one `C²` path that equals the history for `t ≤ 0` and
satisfies `m₀ R̈ = F + F_self[R]` for `t ≥ 0`. -/
theorem existsUnique_linearMotion (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {m₀ γ : ℝ} (hγ : 0 ≤ γ) (hq : weightNorm volume (selfWeight e η) selfDelay γ < |m₀|)
    {F : ℝ → E3} (hF : Continuous F) {CF : ℝ}
    (hCF : ∀ t, 0 ≤ t → ‖F t‖ ≤ CF * Real.exp (γ * t)) {h : ℝ → E3} (hh : ContDiff ℝ 2 h)
    {H : ℝ} (hH : ∀ t, ‖deriv (deriv h) t‖ ≤ H)
    (hcompat : ∀ i, m₀ * deriv (deriv h) 0 i = F 0 i + linearSelfForce e η h 0 i) :
    ∃! R : ℝ → E3, ContDiff ℝ 2 R ∧ (∀ t ≤ 0, R t = h t) ∧
      ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R) t i = F t i + linearSelfForce e η R t i := by
  obtain ⟨R, hR, hRh, hRm, -⟩ :=
    exists_linearMotion hη hb0 hb hrot hγ hq hF hCF hh hH hcompat
  refine ⟨R, ⟨hR, hRh, hRm⟩, fun R' ⟨hR', hR'h, hR'm⟩ => ?_⟩
  exact linearMotion_unique hη hb0 hb hrot hγ hq hR' hR (fun t ht => by rw [hR'h t ht, hRh t ht])
    hR'm hRm

/-- **Lipschitz dependence on the data** (S2): two solutions of `m₀ R̈ = F + F_self[R]` for
`t ≥ 0` with `‖F₁ − F₂‖ ≤ C e^{γt}` on `[0, T]` and `‖R̈₁ − R̈₂‖ ≤ H` on `[−2b, 0]` satisfy
`‖R̈₁(t) − R̈₂(t)‖ ≤ e^{γt}(C + qH)/(|m₀| − q_γ)` on `[0, T]`, with `q = ∫ |w|`. For
`q < |m₀|` the rate `γ = 0` gives a bound uniform in time. -/
theorem norm_sub_le_linearMotion (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {m₀ γ : ℝ} (hγ : 0 ≤ γ) (hq : weightNorm volume (selfWeight e η) selfDelay γ < |m₀|)
    {F₁ F₂ R₁ R₂ : ℝ → E3} (h₁ : ContDiff ℝ 2 R₁) (h₂ : ContDiff ℝ 2 R₂)
    (hm₁ : ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R₁) t i = F₁ t i + linearSelfForce e η R₁ t i)
    (hm₂ : ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R₂) t i = F₂ t i + linearSelfForce e η R₂ t i)
    {T C H : ℝ} (hF : ∀ t ∈ Icc 0 T, ‖F₁ t - F₂ t‖ ≤ C * Real.exp (γ * t))
    (hH : ∀ s ∈ Icc (-(2 * b)) 0, ‖deriv (deriv R₁) s - deriv (deriv R₂) s‖ ≤ H) :
    ∀ t ∈ Icc 0 T, ‖deriv (deriv R₁) t - deriv (deriv R₂) t‖ ≤
      (C + (∫ p, |selfWeight e η p|) * H) /
        (|m₀| - weightNorm volume (selfWeight e η) selfDelay γ) * Real.exp (γ * t) := by
  have hd := selfDelayData (e := e) hη.continuous hb0 hb
  have hc₁ := continuous_deriv_deriv h₁
  have hc₂ := continuous_deriv_deriv h₂
  refine norm_le_of_delay hd hγ hq (u := fun s => deriv (deriv R₁) s - deriv (deriv R₂) s)
    (hc₁.sub hc₂) hH fun t ht => ?_
  rw [hd.delayOp_sub hc₁ hc₂, smul_sub]
  have e₁ := (linearMotion_iff hη hb0 hb hrot h₁ m₀ F₁ t).mp (hm₁ t ht.1)
  have e₂ := (linearMotion_iff hη hb0 hb hrot h₂ m₀ F₂ t).mp (hm₂ t ht.1)
  have : m₀ • deriv (deriv R₁) t - m₀ • deriv (deriv R₂) t +
      (delayOp volume (selfWeight e η) selfDelay (deriv (deriv R₁)) t -
        delayOp volume (selfWeight e η) selfDelay (deriv (deriv R₂)) t) = F₁ t - F₂ t := by
    rw [← e₁, ← e₂]
    abel
  rw [this]
  exact hF t ht

/-- **A rate for every bare mass** (S2): for every `m₀ ≠ 0` there are arbitrarily large rates
`γ ≥ 0` with `q_γ < |m₀|`, since the delay `‖y‖` is positive almost everywhere. -/
theorem exists_rate_selfWeight (hη : Continuous η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {m₀ : ℝ} (hm₀ : m₀ ≠ 0) (γ₀ : ℝ) :
    ∃ γ, γ₀ ≤ γ ∧ 0 ≤ γ ∧ weightNorm volume (selfWeight e η) selfDelay γ < |m₀| :=
  (selfDelayData (e := e) hη hb0 hb).exists_weightNorm_lt ae_selfDelay_pos hm₀ γ₀

/-- The norm of the weight of a nonnegative charge is the electromagnetic mass `(4/3) U`. -/
theorem integral_abs_selfWeight (hη : Continuous η) (hη0 : ∀ z, 0 ≤ η z) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) :
    ∫ p, |selfWeight e η p| = 4 / 3 * selfEnergy e η := by
  simp only [abs_of_nonneg (selfWeight_nonneg hη0 _)]
  exact integral_selfWeight hη hb0 hb

/-- **The dependence on the radius**: for the profile `ηₐ` of radius `a` of a nonnegative profile,
the norm of the weight is `(4/3) U(η)/a`; the delay is at most `2ab`. -/
theorem integral_abs_selfWeight_scaledProfile (hη : Continuous η) (hη0 : ∀ z, 0 ≤ η z)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {a : ℝ} (ha : 0 < a) :
    ∫ p, |selfWeight e (scaledProfile a η) p| = 4 / 3 * selfEnergy e η / a := by
  have hc : Continuous (scaledProfile a η) :=
    continuous_const.mul (hη.comp (continuous_const_smul a⁻¹))
  have h0 : ∀ z, 0 ≤ scaledProfile a η z := fun z =>
    mul_nonneg (inv_nonneg.mpr (by positivity)) (hη0 _)
  rw [integral_abs_selfWeight hc h0 (mul_nonneg ha.le hb0)
    (fun z hz => scaledProfile_eq_zero ha hb hz), selfEnergy_scaledProfile e ha]
  ring

/-- **Runaway solutions for a negative bare mass**: for a nonnegative charge with
`m₀ < 0 < m₀ + (4/3) U` (the observed mass is positive and the electromagnetic mass exceeds it),
there is a rate `γ > 0` such that `R(t) = e^{γt} c` solves `m₀ R̈ = F_self[R]` without force for
every `c`. -/
theorem exists_runaway_linearMotion (hη : ContDiff ℝ 2 η) (hη0 : ∀ z, 0 ≤ η z) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) {m₀ : ℝ} (hm₀ : m₀ < 0)
    (hm : 0 < m₀ + 4 / 3 * selfEnergy e η) :
    ∃ γ, 0 < γ ∧ ∀ (c : E3) (t : ℝ) (i : Fin 3),
      m₀ * deriv (deriv fun s => Real.exp (γ * s) • c) t i =
        linearSelfForce e η (fun s => Real.exp (γ * s) • c) t i := by
  have hd := selfDelayData (e := e) hη.continuous hb0 hb
  rw [← integral_selfWeight hη.continuous hb0 hb] at hm
  obtain ⟨γ, hγ, hsol⟩ := exists_runaway (E := E3) hd ae_selfDelay_pos (selfWeight_nonneg hη0)
    hm₀ hm
  refine ⟨γ, hγ, fun c t i => ?_⟩
  have hd1 : ∀ s, HasDerivAt (fun s => Real.exp (γ * s) • c) ((γ * Real.exp (γ * s)) • c) s :=
    fun s => by
      have := (((hasDerivAt_id' s).const_mul γ).exp).smul_const c
      simpa [mul_comm] using this
  have hd2 : ∀ s, HasDerivAt (fun s => (γ * Real.exp (γ * s)) • c)
      ((γ * (γ * Real.exp (γ * s))) • c) s := fun s => by
    have := ((((hasDerivAt_id' s).const_mul γ).exp).const_mul γ).smul_const c
    simpa [mul_comm, mul_assoc] using this
  have hdd : deriv (deriv fun s => Real.exp (γ * s) • c) =
      fun s => (γ ^ 2) • (Real.exp (γ * s) • c) := by
    rw [show deriv (fun s => Real.exp (γ * s) • c) = fun s => (γ * Real.exp (γ * s)) • c from
      funext fun s => (hd1 s).deriv]
    funext s
    rw [(hd2 s).deriv, smul_smul]
    ring_nf
  have hR : ContDiff ℝ 2 (fun s => Real.exp (γ * s) • c) :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).smul contDiff_const
  have heq := (linearMotion_iff (e := e) hη hb0 hb hrot hR m₀ (fun _ => 0) t).mpr ?_
  · simpa using heq i
  · rw [hdd, DelayData.delayOp_smul, smul_comm m₀, ← smul_add, hsol c t, smul_zero]

end Motion

end ProjectAinos.Electrodynamics.RadiationReaction
