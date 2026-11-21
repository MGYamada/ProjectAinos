/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.RadiationReaction.RigidChargeDynamics
public import ProjectAinos.Electrodynamics.RadiationReaction.Rectilinear
import Mathlib.Tactic

/-!
# The self-consistent motion and the reduced equation of radiation damping

Landau–Lifshitz, *The Classical Theory of Fields*, §75, with `c = 1` and the units with
`div E = ρ`, in the linear model of `RigidChargeDynamics`: a rigid charge of a nonnegative
isotropic `C²` profile `η` of mass one, supported in `‖z‖ ≤ b`, with the electromagnetic mass
`δm = (4/3) U` (`selfMass_isotropic`), the observed mass `m` and the bare mass `m₀ = m − δm`.

* **The reduced equation** (Landau–Lifshitz (75.10) in the reduced form of §76):
  `m v̇ = F + (2/3)(e²/4π) Ḟ/m`. `effectiveAcceleration` is `F/m + (2/3)(e²/4π) Ḟ/m²` and
  `effectivePath` the path with this acceleration, the position `R₀` and the velocity `V` at
  `t = 0` (`effectivePath_reduced`, `deriv_deriv_effectivePath`, `effectivePath_of_nonpos`).
* **The comparison** (S3) `norm_sub_effectivePath_le`: in the regime `2δm < m` at a fixed radius
  (so that `δm < m₀`), for the slow force `F(t) = κ² f(κt)` switched on at `t = 0` and the
  inertial motion `R₀ + tV` before, the solution `R` of `m₀ R̈ = F + F_self[R]` and the path `X` of
  the reduced equation satisfy, for `t ≥ 0`,

    `‖R̈ − Ẍ‖ ≤ C κ⁴`, `‖Ṙ − Ẋ‖ ≤ C κ⁴ t`, `‖R − X‖ ≤ C κ⁴ t²/2`

  with `C = ((M₁/m)² B₂ + b M₁ (B₂/m + κ M₁ B₃/m²))/(m − 2δm)`, `M₁ = (2/3)(e²/4π)` and bounds `B₂`,
  `B₃` of `f''`, `f'''`. The damping term of the reduced equation is exactly
  `Ẍ − F/m = κ³ (M₁/m²) f'(κt)` (`deriv_deriv_effectivePath_sub`), so on the slow interval
  `t ≤ T/κ` the errors of the acceleration, velocity and position (`Cκ⁴`, `CTκ³`, `CT²κ²/2`) are
  smaller by a factor `κ` than the contributions of the damping term (`κ³`, `κ²`, `κ`)
  (`norm_sub_effectivePath_le_slow`). Existence of the solution: `exists_slowMotion`.
* **The radius**: `norm_sub_effectivePath_le_scaledProfile` writes the constants for the profile
  `ηₐ` of radius `a`: `δm = (4/3) U(η)/a`, the regime `a > (8/3) U(η)/m`, and the constant grows
  linearly in `a` through the second moment of the delay.
* **Instances**: `effectiveComparison_radialBump`, for the radial bump, a mass above the
  threshold and the force `pulse(s − 2) e₀` (`pulseForce`); `exists_runaway_radialBump`, the
  runaways of the radial bump with a negative bare mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.RadiationReaction

open SmoothGeometry SmoothGeometry.Wave SmoothGeometry.DistributedDelay

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The reduced equation -/

/-- The acceleration `F/m + (2/3)(e²/4π) Ḟ/m²` of the reduced equation
`m v̇ = F + (2/3)(e²/4π) Ḟ/m`. -/
def effectiveAcceleration (e m : ℝ) (F : ℝ → E3) (t : ℝ) : E3 :=
  m⁻¹ • F t + (2 / 3 * (e ^ 2 / (4 * π)) / m ^ 2) • deriv F t

/-- The path of the reduced equation with the position `R₀` and the velocity `V` at `t = 0`. -/
def effectivePath (e m : ℝ) (F : ℝ → E3) (R₀ V : E3) (t : ℝ) : E3 :=
  R₀ + t • V + doublePrimitive (effectiveAcceleration e m F) t

section Reduced

variable {e m : ℝ} {F : ℝ → E3}

theorem continuous_effectiveAcceleration (hF : ContDiff ℝ 1 F) :
    Continuous (effectiveAcceleration e m F) := by
  have h0 := hF.continuous
  have h1 := ((contDiff_succ_iff_deriv (n := 0)).mp hF).2.2.continuous
  unfold effectiveAcceleration
  fun_prop

theorem contDiff_inertial (R₀ V : E3) : ContDiff ℝ 2 fun t : ℝ => R₀ + t • V :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

theorem deriv_inertial (R₀ V : E3) : deriv (fun t : ℝ => R₀ + t • V) = fun _ => V :=
  funext fun s => by
    have := ((hasDerivAt_id' s).smul_const V).const_add R₀
    simpa using this.deriv

theorem deriv_deriv_inertial (R₀ V : E3) (t : ℝ) :
    deriv (deriv fun t : ℝ => R₀ + t • V) t = 0 := by
  rw [deriv_inertial]
  simp

theorem contDiff_effectivePath (hF : ContDiff ℝ 1 F) (R₀ V : E3) :
    ContDiff ℝ 2 (effectivePath e m F R₀ V) :=
  (contDiff_inertial R₀ V).add (contDiff_doublePrimitive (continuous_effectiveAcceleration hF))

/-- The path of the reduced equation has the acceleration `effectiveAcceleration`. -/
theorem deriv_deriv_effectivePath (hF : ContDiff ℝ 1 F) (R₀ V : E3) (t : ℝ) :
    deriv (deriv (effectivePath e m F R₀ V)) t = effectiveAcceleration e m F t := by
  have h := deriv_deriv_add (contDiff_inertial R₀ V)
    (contDiff_doublePrimitive (continuous_effectiveAcceleration (e := e) (m := m) hF)) t
  rw [deriv_deriv_inertial, zero_add,
    deriv_deriv_doublePrimitive (continuous_effectiveAcceleration hF)] at h
  exact h

/-- **The reduced equation**: `m Ẍ = F + (2/3)(e²/4π) Ḟ/m`. -/
theorem effectivePath_reduced (hm : m ≠ 0) (hF : ContDiff ℝ 1 F) (R₀ V : E3) (t : ℝ) :
    m • deriv (deriv (effectivePath e m F R₀ V)) t =
      F t + (2 / 3 * (e ^ 2 / (4 * π)) / m) • deriv F t := by
  rw [deriv_deriv_effectivePath hF, effectiveAcceleration, smul_add, smul_smul, smul_smul,
    mul_inv_cancel₀ hm, one_smul]
  congr 2
  field_simp

/-- **The damping term**: `Ẍ − F/m = (2/3)(e²/4π) Ḟ/m²`. -/
theorem deriv_deriv_effectivePath_sub (hF : ContDiff ℝ 1 F) (R₀ V : E3) (t : ℝ) :
    deriv (deriv (effectivePath e m F R₀ V)) t - m⁻¹ • F t =
      (2 / 3 * (e ^ 2 / (4 * π)) / m ^ 2) • deriv F t := by
  rw [deriv_deriv_effectivePath hF, effectiveAcceleration, add_sub_cancel_left]

/-- For a force that vanishes for `t ≤ 0`, the path of the reduced equation is the inertial
motion for `t ≤ 0`. -/
theorem effectivePath_of_nonpos (hF : ContDiff ℝ 1 F) (hF0 : ∀ t ≤ 0, F t = 0) (R₀ V : E3)
    {t : ℝ} (ht : t ≤ 0) : effectivePath e m F R₀ V t = R₀ + t • V := by
  have hF'0 : ∀ s ≤ 0, deriv F s = 0 :=
    eq_zero_of_lt_zero ((contDiff_succ_iff_deriv (n := 0)).mp hF).2.2.continuous
      fun s hs => deriv_eq_zero_of_lt_zero hF0 hs
  have ha0 : ∀ s ≤ 0, effectiveAcceleration e m F s = 0 := fun s hs => by
    simp [effectiveAcceleration, hF0 s hs, hF'0 s hs]
  simp [effectivePath, doublePrimitive_eq_zero_of_le ha0 ht]

end Reduced

/-! ### The slow force -/

section Slow

variable {f : ℝ → E3}

theorem contDiff_slowForce {n : ℕ∞} (hf : ContDiff ℝ n f) (κ : ℝ) :
    ContDiff ℝ n fun t => κ ^ 2 • f (κ * t) := by
  have h : ContDiff ℝ n fun t => f (κ * t) := hf.comp (contDiff_const.mul contDiff_id)
  exact h.const_smul (κ ^ 2)

/-- The derivatives of the slow force `κ² f(κt)`. -/
theorem deriv_slowForce (hf : ContDiff ℝ 3 f) (κ : ℝ) :
    deriv (fun t => κ ^ 2 • f (κ * t)) = (fun t => κ ^ 3 • deriv f (κ * t)) ∧
      deriv (deriv fun t => κ ^ 2 • f (κ * t)) = (fun t => κ ^ 4 • deriv (deriv f) (κ * t)) ∧
      deriv (deriv (deriv fun t => κ ^ 2 • f (κ * t))) =
        fun t => κ ^ 5 • deriv (deriv (deriv f)) (κ * t) := by
  have hf1 : ContDiff ℝ 2 (deriv f) := ((contDiff_succ_iff_deriv (n := 2)).mp hf).2.2
  have hf2 : ContDiff ℝ 1 (deriv (deriv f)) := ((contDiff_succ_iff_deriv (n := 1)).mp hf1).2.2
  have d1 : deriv (fun t => κ ^ 2 • f (κ * t)) = fun t => κ ^ 3 • deriv f (κ * t) := by
    rw [deriv_smul_comp_mul (E := E3) (hf.differentiable (by norm_num)) (κ ^ 2) κ]
    funext t
    rw [show κ ^ 2 * κ = κ ^ 3 by ring]
  have d2 : deriv (deriv fun t => κ ^ 2 • f (κ * t)) =
      fun t => κ ^ 4 • deriv (deriv f) (κ * t) := by
    rw [d1, deriv_smul_comp_mul (E := E3) (hf1.differentiable (by norm_num)) (κ ^ 3) κ]
    funext t
    rw [show κ ^ 3 * κ = κ ^ 4 by ring]
  refine ⟨d1, d2, ?_⟩
  rw [d2, deriv_smul_comp_mul (E := E3) (hf2.differentiable one_ne_zero) (κ ^ 4) κ]
  funext t
  rw [show κ ^ 4 * κ = κ ^ 5 by ring]

end Slow

/-! ### The comparison -/

section Comparison

variable {e : ℝ} {η : E3 → ℝ}

/-- **The acceleration stays close to the reduced acceleration**: in the regime `2δm < m`, for
the slow force `κ² f(κt)` and the inertial motion before `t = 0`,
`‖R̈ − Ẍ‖ ≤ ((M₁/m)² B₂ + b M₁ (B₂/m + κ M₁ B₃/m²)) κ⁴/(m − 2δm)` at all times. -/
theorem norm_accel_sub_effective_le (hη : ContDiff ℝ 2 η) (hη0 : ∀ z, 0 ≤ η z) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (hη1 : ∫ z, η z = 1) {m : ℝ}
    (hreg : 8 / 3 * selfEnergy e η < m) {f : ℝ → E3} (hf : ContDiff ℝ 3 f)
    (hf0 : ∀ s ≤ 0, f s = 0) {B₂ B₃ : ℝ} (hB₂ : ∀ s, ‖deriv (deriv f) s‖ ≤ B₂)
    (hB₃ : ∀ s, ‖deriv (deriv (deriv f)) s‖ ≤ B₃) {κ : ℝ} (hκ : 0 ≤ κ) (R₀ V : E3)
    {R : ℝ → E3} (hR : ContDiff ℝ 2 R) (hpast : ∀ t ≤ 0, R t = R₀ + t • V)
    (hmot : ∀ t, 0 ≤ t → ∀ i, (m - 4 / 3 * selfEnergy e η) * deriv (deriv R) t i =
      (κ ^ 2 • f (κ * t)) i + linearSelfForce e η R t i) (t : ℝ) :
    ‖deriv (deriv R) t -
        deriv (deriv (effectivePath e m (fun s => κ ^ 2 • f (κ * s)) R₀ V)) t‖ ≤
      ((2 / 3 * (e ^ 2 / (4 * π)) / m) ^ 2 * B₂ +
        b * (2 / 3 * (e ^ 2 / (4 * π))) *
          (B₂ / m + κ * (2 / 3 * (e ^ 2 / (4 * π))) * B₃ / m ^ 2)) /
        (m - 8 / 3 * selfEnergy e η) * κ ^ 4 := by
  set M₁ := 2 / 3 * (e ^ 2 / (4 * π)) with hM₁def
  set U := selfEnergy e η with hU
  have hd := selfDelayData (e := e) hη.continuous hb0 hb
  have hw : ∫ p, selfWeight e η p = 4 / 3 * U := integral_selfWeight hη.continuous hb0 hb
  have hwa : ∫ p, |selfWeight e η p| = 4 / 3 * U :=
    integral_abs_selfWeight hη.continuous hη0 hb0 hb
  have hwτ : ∫ p, selfWeight e η p * selfDelay p = M₁ := by
    rw [integral_selfWeight_mul_delay hη.continuous hb0 hb, hη1, one_pow, mul_one]
  have hδm0 : 0 ≤ 4 / 3 * U := by
    rw [← hwa]
    exact integral_nonneg fun _ => abs_nonneg _
  set m₀ := m - 4 / 3 * U with hm₀
  have hm₀pos : 4 / 3 * U < m₀ := by
    rw [hm₀]
    linarith
  have hmpos : 0 < m := by linarith
  have habs : |m₀| = m₀ := abs_of_pos (by linarith)
  have hq : ∫ p, |selfWeight e η p| < |m₀| := by rw [hwa, habs]; exact hm₀pos
  have hM₁0 : 0 ≤ M₁ := by
    rw [hM₁def]
    positivity
  -- the slow force
  set F : ℝ → E3 := fun s => κ ^ 2 • f (κ * s) with hF
  have hF3 : ContDiff ℝ 3 F := contDiff_slowForce hf κ
  have hF0 : ∀ s ≤ 0, F s = 0 := fun s hs => by
    simp [hF, hf0 (κ * s) (mul_nonpos_of_nonneg_of_nonpos hκ hs)]
  obtain ⟨-, hd2, hd3⟩ := deriv_slowForce hf κ
  have hB₂' : ∀ s, ‖deriv (deriv F) s‖ ≤ κ ^ 4 * B₂ := fun s => by
    rw [hd2, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hB₂ _) (by positivity)
  have hB₃' : ∀ s, ‖deriv (deriv (deriv F)) s‖ ≤ κ ^ 5 * B₃ := fun s => by
    rw [hd3, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hB₃ _) (by positivity)
  -- the solution as a delay equation
  have hu0 : ∀ s ≤ 0, deriv (deriv R) s = 0 := fun s hs => by
    rw [deriv_deriv_eq_of_eq_on_Iic hR (contDiff_inertial R₀ V) hpast s hs,
      deriv_deriv_inertial]
  have hsol : ∀ s, 0 ≤ s → m₀ • deriv (deriv R) s +
      delayOp volume (selfWeight e η) selfDelay (deriv (deriv R)) s = F s := fun s hs =>
    (linearMotion_iff hη hb0 hb hrot hR m₀ F s).mp (hmot s hs)
  have hmain := norm_sub_reduced_le hd hq (m := m) (M₁ := M₁)
    (Q₂ := ∫ p, |selfWeight e η p| * selfDelay p ^ 2) (by rw [hw, hm₀]; ring) hmpos.ne'
    hwτ.symm rfl hF3 hF0 hB₂' hB₃' (continuous_deriv_deriv hR) hu0 hsol t
  have hacc : deriv (deriv (effectivePath e m F R₀ V)) t =
      m⁻¹ • F t + (M₁ / m ^ 2) • deriv F t :=
    deriv_deriv_effectivePath (hF3.of_le (by norm_num)) R₀ V t
  rw [hacc]
  refine hmain.trans ?_
  -- the second moment
  have hQ : ∫ p, |selfWeight e η p| * selfDelay p ^ 2 ≤ 2 * b * M₁ := by
    have := hd.integral_abs_mul_sq_le
    have h2 : ∫ p, |selfWeight e η p| * selfDelay p = M₁ := by
      rw [← hwτ]
      congr 1
      funext p
      rw [abs_of_nonneg (selfWeight_nonneg hη0 p)]
    rwa [h2] at this
  rw [hwa, habs, abs_of_pos hmpos, abs_of_nonneg hM₁0]
  have hD : 0 < m - 8 / 3 * U := by linarith
  have hden' : m₀ - 4 / 3 * U = m - 8 / 3 * U := by rw [hm₀]; ring
  rw [hden', show ((M₁ / m) ^ 2 * B₂ + b * M₁ * (B₂ / m + κ * M₁ * B₃ / m ^ 2)) /
      (m - 8 / 3 * U) * κ ^ 4 = ((M₁ / m) ^ 2 * B₂ + b * M₁ * (B₂ / m + κ * M₁ * B₃ / m ^ 2)) *
      κ ^ 4 / (m - 8 / 3 * U) by ring]
  refine div_le_div_of_nonneg_right ?_ hD.le
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ 0)
  have hB₃0 : 0 ≤ B₃ := (norm_nonneg _).trans (hB₃ 0)
  have hfac : 0 ≤ κ ^ 4 * B₂ / m + M₁ * (κ ^ 5 * B₃) / m ^ 2 := by positivity
  have h1 : (∫ p, |selfWeight e η p| * selfDelay p ^ 2) / 2 *
      (κ ^ 4 * B₂ / m + M₁ * (κ ^ 5 * B₃) / m ^ 2) ≤
      b * M₁ * (κ ^ 4 * B₂ / m + M₁ * (κ ^ 5 * B₃) / m ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hfac
  have h2 : (M₁ / m) ^ 2 * (κ ^ 4 * B₂) + b * M₁ * (κ ^ 4 * B₂ / m + M₁ * (κ ^ 5 * B₃) / m ^ 2) =
      ((M₁ / m) ^ 2 * B₂ + b * M₁ * (B₂ / m + κ * M₁ * B₃ / m ^ 2)) * κ ^ 4 := by
    field_simp
  linarith

/-- **The self-consistent motion and the reduced equation** (Landau–Lifshitz §75 in the linear
model, S3): in the regime `2δm < m` at a fixed radius, for the slow force `F(t) = κ² f(κt)`
switched on at `t = 0` (`f` is `C³`, vanishes for `s ≤ 0`, `‖f''‖ ≤ B₂`, `‖f'''‖ ≤ B₃`) and the
inertial motion `R₀ + tV` before, every `C²` solution `R` of `m₀ R̈ = F + F_self[R]`
(`m₀ = m − δm`) and the path `X` of the reduced equation `m Ẍ = F + (2/3)(e²/4π) Ḟ/m` with the
same data satisfy, for `t ≥ 0`,

  `‖R̈ − Ẍ‖ ≤ C κ⁴`,  `‖Ṙ − Ẋ‖ ≤ C κ⁴ t`,  `‖R − X‖ ≤ C κ⁴ t²/2`,

with `C = ((M₁/m)² B₂ + b M₁ (B₂/m + κ M₁ B₃/m²))/(m − 2δm)` and `M₁ = (2/3)(e²/4π)`. -/
theorem norm_sub_effectivePath_le (hη : ContDiff ℝ 2 η) (hη0 : ∀ z, 0 ≤ η z) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (hη1 : ∫ z, η z = 1) {m : ℝ}
    (hreg : 8 / 3 * selfEnergy e η < m) {f : ℝ → E3} (hf : ContDiff ℝ 3 f)
    (hf0 : ∀ s ≤ 0, f s = 0) {B₂ B₃ : ℝ} (hB₂ : ∀ s, ‖deriv (deriv f) s‖ ≤ B₂)
    (hB₃ : ∀ s, ‖deriv (deriv (deriv f)) s‖ ≤ B₃) {κ : ℝ} (hκ : 0 ≤ κ) (R₀ V : E3)
    {R : ℝ → E3} (hR : ContDiff ℝ 2 R) (hpast : ∀ t ≤ 0, R t = R₀ + t • V)
    (hmot : ∀ t, 0 ≤ t → ∀ i, (m - 4 / 3 * selfEnergy e η) * deriv (deriv R) t i =
      (κ ^ 2 • f (κ * t)) i + linearSelfForce e η R t i) {t : ℝ} (ht : 0 ≤ t) :
    let X := effectivePath e m (fun s => κ ^ 2 • f (κ * s)) R₀ V
    let C := ((2 / 3 * (e ^ 2 / (4 * π)) / m) ^ 2 * B₂ +
        b * (2 / 3 * (e ^ 2 / (4 * π))) *
          (B₂ / m + κ * (2 / 3 * (e ^ 2 / (4 * π))) * B₃ / m ^ 2)) /
        (m - 8 / 3 * selfEnergy e η)
    ‖deriv (deriv R) t - deriv (deriv X) t‖ ≤ C * κ ^ 4 ∧
      ‖deriv R t - deriv X t‖ ≤ C * κ ^ 4 * t ∧ ‖R t - X t‖ ≤ C * κ ^ 4 * t ^ 2 / 2 := by
  intro X C
  have hacc := norm_accel_sub_effective_le hη hη0 hb0 hb hrot hη1 hreg hf hf0 hB₂ hB₃ hκ R₀ V
    hR hpast hmot
  have hF1 : ContDiff ℝ 1 fun s => κ ^ 2 • f (κ * s) :=
    (contDiff_slowForce hf κ).of_le (by norm_num)
  have hX : ContDiff ℝ 2 X := contDiff_effectivePath hF1 R₀ V
  have hF0 : ∀ s ≤ 0, κ ^ 2 • f (κ * s) = 0 := fun s hs => by
    simp [hf0 (κ * s) (mul_nonpos_of_nonneg_of_nonpos hκ hs)]
  have hg0 : ∀ s ≤ 0, R s - X s = 0 := fun s hs => by
    rw [hpast s hs, show X s = R₀ + s • V from effectivePath_of_nonpos hF1 hF0 R₀ V hs, sub_self]
  have hd1 : deriv (fun s => R s - X s) = fun s => deriv R s - deriv X s := funext fun s =>
    deriv_sub ((hR.differentiable (by norm_num)) s) ((hX.differentiable (by norm_num)) s)
  have hd2 : ∀ s, deriv (deriv fun s => R s - X s) s =
      deriv (deriv R) s - deriv (deriv X) s := fun s => by
    rw [hd1]
    exact deriv_sub (((contDiff_deriv_path hR).differentiable one_ne_zero) s)
      (((contDiff_deriv_path hX).differentiable one_ne_zero) s)
  have hbd := norm_le_of_deriv_deriv_le (hR.sub hX) hg0 (C := C * κ ^ 4)
    (fun s => by rw [hd2]; exact hacc s) ht
  rw [hd1] at hbd
  exact ⟨hacc t, hbd.1, hbd.2⟩

/-- **On the slow interval** `0 ≤ t ≤ T/κ` the velocity and the position differ by at most
`C T κ³` and `C T² κ²/2`, one order of `κ` below the contributions `κ²` and `κ` of the damping
term `Ẍ − F/m = κ³ (M₁/m²) f'(κt)` to the velocity and the position. -/
theorem norm_sub_effectivePath_le_slow (hη : ContDiff ℝ 2 η) (hη0 : ∀ z, 0 ≤ η z) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (hη1 : ∫ z, η z = 1) {m : ℝ}
    (hreg : 8 / 3 * selfEnergy e η < m) {f : ℝ → E3} (hf : ContDiff ℝ 3 f)
    (hf0 : ∀ s ≤ 0, f s = 0) {B₂ B₃ : ℝ} (hB₂ : ∀ s, ‖deriv (deriv f) s‖ ≤ B₂)
    (hB₃ : ∀ s, ‖deriv (deriv (deriv f)) s‖ ≤ B₃) {κ : ℝ} (hκ : 0 < κ) (R₀ V : E3)
    {R : ℝ → E3} (hR : ContDiff ℝ 2 R) (hpast : ∀ t ≤ 0, R t = R₀ + t • V)
    (hmot : ∀ t, 0 ≤ t → ∀ i, (m - 4 / 3 * selfEnergy e η) * deriv (deriv R) t i =
      (κ ^ 2 • f (κ * t)) i + linearSelfForce e η R t i) {T t : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T / κ) :
    let X := effectivePath e m (fun s => κ ^ 2 • f (κ * s)) R₀ V
    let C := ((2 / 3 * (e ^ 2 / (4 * π)) / m) ^ 2 * B₂ +
        b * (2 / 3 * (e ^ 2 / (4 * π))) *
          (B₂ / m + κ * (2 / 3 * (e ^ 2 / (4 * π))) * B₃ / m ^ 2)) /
        (m - 8 / 3 * selfEnergy e η)
    ‖deriv R t - deriv X t‖ ≤ C * T * κ ^ 3 ∧ ‖R t - X t‖ ≤ C * T ^ 2 * κ ^ 2 / 2 ∧
      deriv (deriv X) t - m⁻¹ • (κ ^ 2 • f (κ * t)) =
        (κ ^ 3 * (2 / 3 * (e ^ 2 / (4 * π)) / m ^ 2)) • deriv f (κ * t) := by
  intro X C
  obtain ⟨h1, h2, h3⟩ := norm_sub_effectivePath_le hη hη0 hb0 hb hrot hη1 hreg hf hf0 hB₂ hB₃
    hκ.le R₀ V hR hpast hmot ht
  have hC0 : 0 ≤ C := by
    have h0 : (0 : ℝ) * κ ^ 4 ≤ C * κ ^ 4 := by
      rw [zero_mul]
      exact (norm_nonneg _).trans h1
    exact le_of_mul_le_mul_right h0 (by positivity)
  have htk : κ * t ≤ T := by
    rw [le_div_iff₀ hκ] at htT
    linarith
  have hT0 : 0 ≤ T := le_trans (mul_nonneg hκ.le ht) htk
  refine ⟨h2.trans ?_, h3.trans ?_, ?_⟩
  · calc C * κ ^ 4 * t = C * κ ^ 3 * (κ * t) := by ring
      _ ≤ C * κ ^ 3 * T := mul_le_mul_of_nonneg_left htk (by positivity)
      _ = C * T * κ ^ 3 := by ring
  · have hsq : (κ * t) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (mul_nonneg hκ.le ht) htk 2
    calc C * κ ^ 4 * t ^ 2 / 2 = C * κ ^ 2 * (κ * t) ^ 2 / 2 := by ring
      _ ≤ C * κ ^ 2 * T ^ 2 / 2 := by gcongr
      _ = C * T ^ 2 * κ ^ 2 / 2 := by ring
  · have hF1 : ContDiff ℝ 1 fun s => κ ^ 2 • f (κ * s) :=
      (contDiff_slowForce hf κ).of_le (by norm_num)
    rw [deriv_deriv_effectivePath_sub hF1, (deriv_slowForce hf κ).1, smul_smul]
    ring_nf

end Comparison

/-! ### Existence, the radius and an instance -/

section Instances

variable {e : ℝ} {η : E3 → ℝ}

/-- **The solution exists** in the setting of `norm_sub_effectivePath_le`: for a bounded slow
force switched on at `t = 0` and the inertial motion before, the equation
`m₀ R̈ = F + F_self[R]` with `m₀ = m − δm` and `2δm < m` has a `C²` solution, unique by
`linearMotion_unique`. -/
theorem exists_slowMotion (hη : ContDiff ℝ 2 η) (hη0 : ∀ z, 0 ≤ η z) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {m : ℝ} (hreg : 8 / 3 * selfEnergy e η < m) {f : ℝ → E3} (hf : Continuous f)
    (hf0 : ∀ s ≤ 0, f s = 0) {B₀ : ℝ} (hB₀ : ∀ s, ‖f s‖ ≤ B₀) (κ : ℝ) (R₀ V : E3) :
    ∃ R : ℝ → E3, ContDiff ℝ 2 R ∧ (∀ t ≤ 0, R t = R₀ + t • V) ∧
      ∀ t, 0 ≤ t → ∀ i, (m - 4 / 3 * selfEnergy e η) * deriv (deriv R) t i =
        (κ ^ 2 • f (κ * t)) i + linearSelfForce e η R t i := by
  have hwa : ∫ p, |selfWeight e η p| = 4 / 3 * selfEnergy e η :=
    integral_abs_selfWeight hη.continuous hη0 hb0 hb
  have hδm0 : 0 ≤ 4 / 3 * selfEnergy e η := by
    rw [← hwa]
    exact integral_nonneg fun _ => abs_nonneg _
  have hq : weightNorm volume (selfWeight e η) selfDelay 0 < |m - 4 / 3 * selfEnergy e η| := by
    rw [DelayData.weightNorm_zero, hwa, abs_of_pos (by linarith)]
    linarith
  have hFc : Continuous fun t => κ ^ 2 • f (κ * t) := by
    have := hf
    fun_prop
  obtain ⟨R, hR, hRh, hRm, -⟩ := exists_linearMotion hη hb0 hb hrot le_rfl hq hFc
    (CF := κ ^ 2 * B₀) (fun t _ => by
      rw [zero_mul, Real.exp_zero, mul_one, norm_smul, Real.norm_of_nonneg (sq_nonneg κ)]
      exact mul_le_mul_of_nonneg_left (hB₀ _) (sq_nonneg κ))
    (contDiff_inertial R₀ V) (H := 0) (fun t => by rw [deriv_deriv_inertial, norm_zero])
    (fun i => by
      rw [deriv_deriv_inertial, linearSelfForce_inertial hη hb hrot]
      simp [hf0 0 le_rfl])
  exact ⟨R, hR, hRh, hRm⟩

/-- **The comparison for the profile of radius `a`** (S3 with the radius explicit): for a
nonnegative isotropic `C²` profile `η` of mass one vanishing outside the unit ball, its profile
`ηₐ` of radius `a` has `δm = (4/3) U(η)/a`; in the regime `(8/3) U(η)/a < m` the solution with
the bare mass `m − (4/3) U(η)/a` satisfies `‖R̈ − Ẍ‖ ≤ C(a) κ⁴` with
`C(a) = ((M₁/m)² B₂ + a M₁ (B₂/m + κ M₁ B₃/m²))/(m − (8/3) U(η)/a)`, and the bounds of the
velocity and the position of `norm_sub_effectivePath_le`. -/
theorem norm_sub_effectivePath_le_scaledProfile (hη : ContDiff ℝ 2 η) (hη0 : ∀ z, 0 ≤ η z)
    (hb : ∀ z : E3, 1 < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    (hη1 : ∫ z, η z = 1) {a m : ℝ} (ha : 0 < a) (hreg : 8 / 3 * selfEnergy e η / a < m)
    {f : ℝ → E3} (hf : ContDiff ℝ 3 f) (hf0 : ∀ s ≤ 0, f s = 0) {B₂ B₃ : ℝ}
    (hB₂ : ∀ s, ‖deriv (deriv f) s‖ ≤ B₂) (hB₃ : ∀ s, ‖deriv (deriv (deriv f)) s‖ ≤ B₃)
    {κ : ℝ} (hκ : 0 ≤ κ) (R₀ V : E3) {R : ℝ → E3} (hR : ContDiff ℝ 2 R)
    (hpast : ∀ t ≤ 0, R t = R₀ + t • V)
    (hmot : ∀ t, 0 ≤ t → ∀ i, (m - 4 / 3 * selfEnergy e η / a) * deriv (deriv R) t i =
      (κ ^ 2 • f (κ * t)) i + linearSelfForce e (scaledProfile a η) R t i) {t : ℝ}
    (ht : 0 ≤ t) :
    let X := effectivePath e m (fun s => κ ^ 2 • f (κ * s)) R₀ V
    let C := ((2 / 3 * (e ^ 2 / (4 * π)) / m) ^ 2 * B₂ +
        a * (2 / 3 * (e ^ 2 / (4 * π))) *
          (B₂ / m + κ * (2 / 3 * (e ^ 2 / (4 * π))) * B₃ / m ^ 2)) /
        (m - 8 / 3 * selfEnergy e η / a)
    ‖deriv (deriv R) t - deriv (deriv X) t‖ ≤ C * κ ^ 4 ∧
      ‖deriv R t - deriv X t‖ ≤ C * κ ^ 4 * t ∧ ‖R t - X t‖ ≤ C * κ ^ 4 * t ^ 2 / 2 := by
  have hU : selfEnergy e (scaledProfile a η) = selfEnergy e η / a := by
    rw [selfEnergy_scaledProfile e ha, inv_mul_eq_div]
  have hηa : ContDiff ℝ 2 (scaledProfile a η) :=
    contDiff_const.mul (hη.comp (contDiff_id.const_smul a⁻¹))
  have hηa0 : ∀ z, 0 ≤ scaledProfile a η z := fun z =>
    mul_nonneg (inv_nonneg.mpr (by positivity)) (hη0 _)
  have hηab : ∀ z : E3, a < ‖z‖ → scaledProfile a η z = 0 := fun z hz =>
    scaledProfile_eq_zero ha hb (by rwa [mul_one])
  have h := norm_sub_effectivePath_le (e := e) hηa hηa0 ha.le hηab
    (scaledProfile_comp_isometry hrot a) (by rw [integral_scaledProfile ha, hη1])
    (m := m) (by rw [hU]; linarith [show 8 / 3 * (selfEnergy e η / a) =
      8 / 3 * selfEnergy e η / a by ring]) hf hf0 hB₂ hB₃ hκ R₀ V hR hpast
    (fun t ht i => by
      rw [hU, show 4 / 3 * (selfEnergy e η / a) = 4 / 3 * selfEnergy e η / a by ring]
      exact hmot t ht i) ht
  simp only [hU, show 8 / 3 * (selfEnergy e η / a) = 8 / 3 * selfEnergy e η / a by ring] at h
  exact h

/-- The derivatives of a smooth function of compact support are bounded. -/
theorem exists_bound_iterate_deriv {g : ℝ → E3} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (k : ℕ) : ∃ B, ∀ s, ‖deriv^[k] g s‖ ≤ B := by
  have hck : HasCompactSupport (deriv^[k] g) := by
    induction k with
    | zero => exact hc
    | succ k ih => rw [Function.iterate_succ_apply']; exact ih.deriv
  exact (ContDiff.iterate_deriv k hg).continuous.bounded_above_of_compact_support hck

/-- The pulse `pulse(s − 2) e₀`, a smooth force switched on after `s = 1`. -/
def pulseForce (s : ℝ) : E3 := pulse (s - 2) • EuclideanSpace.single 0 1

theorem contDiff_pulseForce : ContDiff ℝ ∞ pulseForce :=
  (contDiff_pulse.comp (contDiff_id.sub contDiff_const)).smul contDiff_const

theorem pulseForce_eq_zero {s : ℝ} (hs : s ≤ 0) : pulseForce s = 0 := by
  simp [pulseForce, pulse_eq_zero_of_lt (by linarith : s - 2 < -1)]

theorem hasCompactSupport_pulseForce : HasCompactSupport pulseForce := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 3)) fun s hs => ?_
  have : 1 < |s - 2| := by
    rcases not_and_or.mp hs with h | h
    · rw [abs_of_neg (by linarith [not_le.mp h])]
      linarith [not_le.mp h]
    · rw [abs_of_pos (by linarith [not_le.mp h])]
      linarith [not_le.mp h]
  simp [pulseForce, pulse_eq_zero this]

/-- **An instance of the comparison**: the radial bump of radius one, any charge, the observed
mass `m = (8/3) U + 1` above the threshold and the force `κ² pulse(κt − 2) e₀`: the solution
exists and stays within `C κ⁴`, `C κ⁴ t` and `C κ⁴ t²/2` of the reduced motion. -/
theorem effectiveComparison_radialBump (e : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (R₀ V : E3) :
    ∃ (C : ℝ) (R : ℝ → E3), ContDiff ℝ 2 R ∧ (∀ t ≤ 0, R t = R₀ + t • V) ∧
      (∀ t, 0 ≤ t → ∀ i,
        (8 / 3 * selfEnergy e radialBump + 1 - 4 / 3 * selfEnergy e radialBump) *
            deriv (deriv R) t i =
          (κ ^ 2 • pulseForce (κ * t)) i + linearSelfForce e radialBump R t i) ∧
      ∀ t, 0 ≤ t →
        ‖deriv (deriv R) t - deriv (deriv (effectivePath e (8 / 3 * selfEnergy e radialBump + 1)
            (fun s => κ ^ 2 • pulseForce (κ * s)) R₀ V)) t‖ ≤ C * κ ^ 4 ∧
        ‖R t - effectivePath e (8 / 3 * selfEnergy e radialBump + 1)
            (fun s => κ ^ 2 • pulseForce (κ * s)) R₀ V t‖ ≤ C * κ ^ 4 * t ^ 2 / 2 := by
  have hη : ContDiff ℝ 2 radialBump := contDiff_radialBump.of_le (by simp)
  have hb : ∀ z : E3, 1 < ‖z‖ → radialBump z = 0 := fun z hz => radialBump_eq_zero hz
  obtain ⟨B₀, hB₀⟩ := exists_bound_iterate_deriv contDiff_pulseForce
    hasCompactSupport_pulseForce 0
  obtain ⟨B₂, hB₂⟩ := exists_bound_iterate_deriv contDiff_pulseForce
    hasCompactSupport_pulseForce 2
  obtain ⟨B₃, hB₃⟩ := exists_bound_iterate_deriv contDiff_pulseForce
    hasCompactSupport_pulseForce 3
  have hreg : 8 / 3 * selfEnergy e radialBump < 8 / 3 * selfEnergy e radialBump + 1 := by
    linarith
  obtain ⟨R, hR, hRh, hRm⟩ := exists_slowMotion (e := e) hη radialBump_nonneg zero_le_one hb
    radialBump_comp_isometry hreg contDiff_pulseForce.continuous
    (fun s hs => pulseForce_eq_zero hs) (B₀ := B₀) (fun s => by simpa using hB₀ s) κ R₀ V
  set m := 8 / 3 * selfEnergy e radialBump + 1 with hm
  set M₁ := 2 / 3 * (e ^ 2 / (4 * π)) with hM₁
  refine ⟨((M₁ / m) ^ 2 * B₂ + 1 * M₁ * (B₂ / m + κ * M₁ * B₃ / m ^ 2)) /
    (m - 8 / 3 * selfEnergy e radialBump), R, hR, hRh, hRm, fun t ht => ?_⟩
  have h := norm_sub_effectivePath_le hη radialBump_nonneg zero_le_one hb radialBump_comp_isometry
    integral_radialBump hreg (contDiff_pulseForce.of_le (by simp))
    (fun s hs => pulseForce_eq_zero hs) (B₂ := B₂) (B₃ := B₃)
    (fun s => by simpa using hB₂ s) (fun s => by simpa using hB₃ s) hκ R₀ V hR hRh hRm ht
  exact ⟨h.1, h.2.2⟩

/-- **An instance of the runaways**: for a nonzero charge on the radial bump and the bare mass
`m₀ = −(2/3) U` (observed mass `(2/3) U > 0`), the free equation has the solutions `e^{γt} c` with
some `γ > 0`. -/
theorem exists_runaway_radialBump {e : ℝ} (he : e ≠ 0) :
    ∃ γ, 0 < γ ∧ ∀ (c : E3) (t : ℝ) (i : Fin 3),
      -(2 / 3 * selfEnergy e radialBump) * deriv (deriv fun s => Real.exp (γ * s) • c) t i =
        linearSelfForce e radialBump (fun s => Real.exp (γ * s) • c) t i := by
  have hU := selfEnergy_radialBump_pos he
  exact exists_runaway_linearMotion (contDiff_radialBump.of_le (by simp)) radialBump_nonneg
    zero_le_one (fun z hz => radialBump_eq_zero hz) radialBump_comp_isometry (by linarith)
    (by linarith)

end Instances

end ProjectAinos.Electrodynamics.RadiationReaction
