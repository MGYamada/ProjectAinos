/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.RadiationReaction
import Mathlib.Tactic

/-!
# The selection of the physical solutions in rectilinear motion

Landau–Lifshitz, *The Classical Theory of Fields*, §76 (with §75 for the free equation), with
`c = 1`, the signature `(−+++)` and the units with `div E = ρ` of `lorentzDiracForce`.

A rectilinear motion in the proper time has the four-velocity `u = (cosh ϑ, sinh ϑ, 0, 0)` with
the rapidity `ϑ(τ)` (`rectilinearVelocity`) and the unit spacelike direction of motion
`n = (sinh ϑ, cosh ϑ, 0, 0)` (`rectilinearDirection`); the proper acceleration is `α = ϑ′`.

* **The projected equation**: `lorentzDiracForce_rectilinear` (`g = (2/3)(e²/4π) α′ n`),
  `lorentzDirac_rectilinear_iff` (a four-force `F` drives the motion, `m u̇ = F + g`, exactly when
  `F = (mα − (2/3)(e²/4π) α′) n`) and `lorentzDirac_rectilinear_force_iff`: for the external
  four-force `f n` the equation of Lorentz and Dirac is `mα = f + mτ₀ α′` with
  `mτ₀ = (2/3)(e²/4π)` (`radiationTime`, `lorentzDirac_rectilinear_iff_radiationTime`); the
  projection on `n` is `minkowskiForm_lorentzDirac_rectilinear`.
* **The scalar equation** `mα = f + mτ₀ α′` for a continuous compactly supported proper force:
  the selected acceleration `selectedAcceleration`
  `α(τ) = (mτ₀)⁻¹ ∫_τ^∞ exp(−(s − τ)/τ₀) f(s) ds` solves it (`selectedAcceleration_solves`) and
  is smooth for smooth `f`; every solution is `α + C exp(τ/τ₀)` (`solution_iff`); the selected
  one is the only solution bounded as `τ → +∞` (`eq_selectedAcceleration_of_bounded`) and every
  other one is a runaway (`tendsto_abs_of_ne_selectedAcceleration`); it vanishes after the force
  (`selectedAcceleration_eq_zero_of_le`), and for a positive pulse it is positive before the
  pulse starts (`selectedAcceleration_preacceleration`, the preacceleration), with the precursor
  `α(τ) = exp((τ − T₁)/τ₀) α(T₁)` (`selectedAcceleration_before`). Instance: `pulse`.
* **Zero force**: `selectedAcceleration_zero` and `rectilinear_free_eq_zero`, which derives the
  uniqueness of the bounded free motion from `abrahamLorentz_free_eq_zero`.
* **The world line**: `selectedRapidity` `ϑ = ϑ₀ + ∫₀^τ α`; its four-velocity solves the covariant
  equation `m u̇ = f n + g` (`selected_lorentzDirac`), and every rectilinear solution of the
  covariant equation is the selected world line or a runaway
  (`rectilinear_lorentzDirac_selection`, `rectilinear_lorentzDirac_eq_selected`,
  `rectilinear_lorentzDirac_runaway`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Real
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.RadiationReaction

open SmoothGeometry SpecialRelativity

/-! ### Rectilinear motion -/

/-- The four-velocity `(cosh ϑ, sinh ϑ, 0, 0)` of a rectilinear motion with the rapidity `ϑ(τ)`. -/
def rectilinearVelocity (ϑ : ℝ → ℝ) (τ : ℝ) : Spacetime :=
  ![Real.cosh (ϑ τ), Real.sinh (ϑ τ), 0, 0]

/-- The unit spacelike direction of motion `(sinh ϑ, cosh ϑ, 0, 0)`, orthogonal to the
four-velocity. -/
def rectilinearDirection (ϑ : ℝ → ℝ) (τ : ℝ) : Spacetime :=
  ![Real.sinh (ϑ τ), Real.cosh (ϑ τ), 0, 0]

theorem minkowskiForm_rectilinearVelocity (ϑ : ℝ → ℝ) (τ : ℝ) :
    minkowskiForm .timeNegative 3 (rectilinearVelocity ϑ τ) (rectilinearVelocity ϑ τ) = -1 := by
  simp [minkowskiForm_apply, Fin.sum_univ_succ, lorentzSign, rectilinearVelocity]
  nlinarith [Real.cosh_sq_sub_sinh_sq (ϑ τ)]

theorem minkowskiForm_rectilinearDirection (ϑ : ℝ → ℝ) (τ : ℝ) :
    minkowskiForm .timeNegative 3 (rectilinearDirection ϑ τ) (rectilinearDirection ϑ τ) = 1 := by
  simp [minkowskiForm_apply, Fin.sum_univ_succ, lorentzSign, rectilinearDirection]
  nlinarith [Real.cosh_sq_sub_sinh_sq (ϑ τ)]

theorem minkowskiForm_rectilinearDirection_velocity (ϑ : ℝ → ℝ) (τ : ℝ) :
    minkowskiForm .timeNegative 3 (rectilinearDirection ϑ τ) (rectilinearVelocity ϑ τ) = 0 := by
  simp [minkowskiForm_apply, Fin.sum_univ_succ, lorentzSign, rectilinearDirection,
    rectilinearVelocity]
  ring

theorem rectilinearDirection_ne_zero (ϑ : ℝ → ℝ) (τ : ℝ) : rectilinearDirection ϑ τ ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [rectilinearDirection] at this
  exact (Real.cosh_pos (ϑ τ)).ne' this

theorem contDiff_rectilinearVelocity {n : WithTop ℕ∞} {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ n ϑ) :
    ContDiff ℝ n (rectilinearVelocity ϑ) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact Real.contDiff_cosh.comp hϑ
  · exact Real.contDiff_sinh.comp hϑ
  · exact contDiff_const
  · exact contDiff_const

theorem hasDerivAt_rectilinearVelocity {ϑ : ℝ → ℝ} {ϑ' τ : ℝ} (h : HasDerivAt ϑ ϑ' τ) :
    HasDerivAt (rectilinearVelocity ϑ) (ϑ' • rectilinearDirection ϑ τ) τ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [rectilinearVelocity, rectilinearDirection, mul_comm] using h.cosh
  · simpa [rectilinearVelocity, rectilinearDirection, mul_comm] using h.sinh
  · simpa [rectilinearVelocity, rectilinearDirection] using hasDerivAt_const τ (0 : ℝ)
  · simpa [rectilinearVelocity, rectilinearDirection] using hasDerivAt_const τ (0 : ℝ)

theorem hasDerivAt_rectilinearDirection {ϑ : ℝ → ℝ} {ϑ' τ : ℝ} (h : HasDerivAt ϑ ϑ' τ) :
    HasDerivAt (rectilinearDirection ϑ) (ϑ' • rectilinearVelocity ϑ τ) τ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [rectilinearVelocity, rectilinearDirection, mul_comm] using h.sinh
  · simpa [rectilinearVelocity, rectilinearDirection, mul_comm] using h.cosh
  · simpa [rectilinearVelocity, rectilinearDirection] using hasDerivAt_const τ (0 : ℝ)
  · simpa [rectilinearVelocity, rectilinearDirection] using hasDerivAt_const τ (0 : ℝ)

/-- The four-acceleration of a rectilinear motion is `u̇ = α n` with `α = ϑ′`. -/
theorem deriv_rectilinearVelocity {ϑ : ℝ → ℝ} (hϑ : Differentiable ℝ ϑ) :
    deriv (rectilinearVelocity ϑ) = fun τ => deriv ϑ τ • rectilinearDirection ϑ τ :=
  funext fun τ => (hasDerivAt_rectilinearVelocity (hϑ τ).hasDerivAt).deriv

/-- The proper acceleration: `u̇ · u̇ = α²`. -/
theorem minkowskiForm_deriv_rectilinearVelocity {ϑ : ℝ → ℝ} (hϑ : Differentiable ℝ ϑ) (τ : ℝ) :
    minkowskiForm .timeNegative 3 (deriv (rectilinearVelocity ϑ) τ)
      (deriv (rectilinearVelocity ϑ) τ) = deriv ϑ τ ^ 2 := by
  rw [deriv_rectilinearVelocity hϑ]
  simp only [map_smul, smul_apply, smul_eq_mul,
    minkowskiForm_rectilinearDirection]
  ring

/-- `ü = α′ n + α² u`. -/
theorem deriv_deriv_rectilinearVelocity {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ) (τ : ℝ) :
    deriv (deriv (rectilinearVelocity ϑ)) τ =
      deriv (deriv ϑ) τ • rectilinearDirection ϑ τ +
        deriv ϑ τ ^ 2 • rectilinearVelocity ϑ τ := by
  have hd1 : Differentiable ℝ ϑ := hϑ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv ϑ) :=
    (ContDiff.deriv' (n := 1) hϑ).differentiable (by norm_num)
  rw [deriv_rectilinearVelocity hd1]
  have h : HasDerivAt (fun σ => deriv ϑ σ • rectilinearDirection ϑ σ) _ τ :=
    (hd2 τ).hasDerivAt.smul (hasDerivAt_rectilinearDirection (hd1 τ).hasDerivAt)
  rw [h.deriv, smul_smul, ← sq, add_comm]

/-- **The force of Lorentz and Dirac in rectilinear motion** is `(2/3)(e²/4π) α′ n`. -/
theorem lorentzDiracForce_rectilinear (e : ℝ) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ) (τ : ℝ) :
    lorentzDiracForce e (rectilinearVelocity ϑ) τ =
      (2 / 3 * (e ^ 2 / (4 * π)) * deriv (deriv ϑ) τ) • rectilinearDirection ϑ τ := by
  rw [lorentzDiracForce, deriv_deriv_rectilinearVelocity hϑ]
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul, minkowskiForm_rectilinearDirection_velocity, minkowskiForm_rectilinearVelocity]
  module

/-- **The projection onto the direction of motion**: `(m u̇ − g) · n = mα − (2/3)(e²/4π) α′`. -/
theorem minkowskiForm_lorentzDirac_rectilinear (m e : ℝ) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ)
    (τ : ℝ) :
    minkowskiForm .timeNegative 3
        (m • deriv (rectilinearVelocity ϑ) τ - lorentzDiracForce e (rectilinearVelocity ϑ) τ)
        (rectilinearDirection ϑ τ) =
      m * deriv ϑ τ - 2 / 3 * (e ^ 2 / (4 * π)) * deriv (deriv ϑ) τ := by
  rw [lorentzDiracForce_rectilinear e hϑ, deriv_rectilinearVelocity (hϑ.differentiable (by simp))]
  simp only [map_sub, map_smul, sub_apply, smul_apply,
    smul_eq_mul, minkowskiForm_rectilinearDirection]
  ring

/-- **The four-forces that drive a rectilinear motion**: the equation of Lorentz and Dirac
`m u̇ = F + g` holds exactly when `F = (mα − (2/3)(e²/4π) α′) n`; in particular the external force
is along the direction of motion and orthogonal to `u`. -/
theorem lorentzDirac_rectilinear_iff (m e : ℝ) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ) (F : Spacetime)
    (τ : ℝ) :
    m • deriv (rectilinearVelocity ϑ) τ = F + lorentzDiracForce e (rectilinearVelocity ϑ) τ ↔
      F = (m * deriv ϑ τ - 2 / 3 * (e ^ 2 / (4 * π)) * deriv (deriv ϑ) τ) •
        rectilinearDirection ϑ τ := by
  rw [lorentzDiracForce_rectilinear e hϑ, deriv_rectilinearVelocity (hϑ.differentiable (by simp))]
  constructor
  · intro h
    rw [eq_sub_of_add_eq h.symm]
    module
  · intro h
    rw [h]
    module

/-- **The equation of Lorentz and Dirac for a rectilinear motion** under the external four-force
`f(τ) n` is the scalar equation `mα = f + (2/3)(e²/4π) α′` for the proper acceleration. -/
theorem lorentzDirac_rectilinear_force_iff (m e : ℝ) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ)
    (f : ℝ → ℝ) (τ : ℝ) :
    m • deriv (rectilinearVelocity ϑ) τ =
        f τ • rectilinearDirection ϑ τ + lorentzDiracForce e (rectilinearVelocity ϑ) τ ↔
      m * deriv ϑ τ = f τ + 2 / 3 * (e ^ 2 / (4 * π)) * deriv (deriv ϑ) τ := by
  rw [lorentzDirac_rectilinear_iff m e hϑ]
  constructor
  · intro h
    have := smul_left_injective ℝ (rectilinearDirection_ne_zero ϑ τ) h
    linarith
  · intro h
    congr 1
    linarith

/-! ### The equation `mα = f + mτ₀ α′` -/

section Scalar

variable {m τ₀ : ℝ} {f : ℝ → ℝ}

/-- **The selected proper acceleration**
`α(τ) = (mτ₀)⁻¹ ∫_τ^∞ exp(−(s − τ)/τ₀) f(s) ds` for the proper force `f`. -/
def selectedAcceleration (m τ₀ : ℝ) (f : ℝ → ℝ) (τ : ℝ) : ℝ :=
  (m * τ₀)⁻¹ * ∫ s in Ioi τ, Real.exp (-(s - τ) / τ₀) * f s

/-- Without force the selected acceleration vanishes. -/
theorem selectedAcceleration_zero (m τ₀ : ℝ) : selectedAcceleration m τ₀ 0 = 0 := by
  funext τ
  simp [selectedAcceleration]

/-- **No acceleration after the force**: if `f = 0` after `T`, the selected acceleration vanishes
from `T` on. -/
theorem selectedAcceleration_eq_zero_of_le {T : ℝ} (hT : ∀ s, T < s → f s = 0) {τ : ℝ}
    (hτ : T ≤ τ) : selectedAcceleration m τ₀ f τ = 0 := by
  rw [selectedAcceleration, setIntegral_eq_zero_of_forall_eq_zero
    (fun s hs => by rw [hT s (lt_of_le_of_lt hτ hs), mul_zero]), mul_zero]

/-- A compactly supported force vanishes after some time. -/
theorem exists_eq_zero_of_lt (hfc : HasCompactSupport f) : ∃ T, ∀ s, T < s → f s = 0 := by
  obtain ⟨T, hT⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine ⟨T, fun s hs => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have := hT hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith [le_abs_self s]

/-- For a function vanishing after `T`, the integral over `(τ, ∞)` is the integral from `τ`
to `T`. -/
theorem setIntegral_Ioi_eq_intervalIntegral {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {T : ℝ} (hT : ∀ s, T < s → g s = 0) (τ : ℝ) :
    ∫ s in Ioi τ, g s = ∫ s in τ..T, g s := by
  have hi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  rcases le_or_gt τ T with h | h
  · rw [intervalIntegral.integral_of_le h, ← Ioc_union_Ioi_eq_Ioi h,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi.integrableOn hi.integrableOn,
      setIntegral_eq_zero_of_forall_eq_zero (t := Ioi T) (fun s hs => hT s hs), add_zero]
  · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le h.le,
      setIntegral_eq_zero_of_forall_eq_zero (t := Ioi τ) (fun s hs => hT s (lt_trans h hs)),
      setIntegral_eq_zero_of_forall_eq_zero (t := Ioc T τ) (fun s hs => hT s hs.1), neg_zero]

/-- The selected acceleration with an integrating factor:
`α(τ) = (mτ₀)⁻¹ e^{τ/τ₀} ∫_τ^T e^{−s/τ₀} f(s) ds` when `f = 0` after `T`. -/
theorem selectedAcceleration_eq (hf : Continuous f) (hfc : HasCompactSupport f) {T : ℝ}
    (hT : ∀ s, T < s → f s = 0) (τ : ℝ) :
    selectedAcceleration m τ₀ f τ =
      (m * τ₀)⁻¹ * (Real.exp (τ / τ₀) * ∫ s in τ..T, Real.exp (-s / τ₀) * f s) := by
  have hg : Continuous fun s => Real.exp (-s / τ₀) * f s := by fun_prop
  have hgc : HasCompactSupport fun s => Real.exp (-s / τ₀) * f s := hfc.mul_left
  rw [selectedAcceleration, ← setIntegral_Ioi_eq_intervalIntegral hg hgc
    (fun s hs => by simp [hT s hs]) τ]
  congr 1
  rw [← integral_const_mul]
  congr 1
  funext s
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem exp_div_mul_exp_neg_div (τ τ₀ : ℝ) : Real.exp (τ / τ₀) * Real.exp (-τ / τ₀) = 1 := by
  rw [← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero]

/-- **The derivative of the selected acceleration**: `α′ = α/τ₀ − f/(mτ₀)`. -/
theorem hasDerivAt_selectedAcceleration (hf : Continuous f)
    (hfc : HasCompactSupport f) (τ : ℝ) :
    HasDerivAt (selectedAcceleration m τ₀ f)
      (τ₀⁻¹ * selectedAcceleration m τ₀ f τ - (m * τ₀)⁻¹ * f τ) τ := by
  obtain ⟨T, hT⟩ := exists_eq_zero_of_lt hfc
  have hrep := funext (selectedAcceleration_eq (m := m) (τ₀ := τ₀) hf hfc hT)
  have hg : Continuous fun s => Real.exp (-s / τ₀) * f s := by fun_prop
  have hG : HasDerivAt (fun σ => ∫ s in σ..T, Real.exp (-s / τ₀) * f s)
      (-(Real.exp (-τ / τ₀) * f τ)) τ := by
    refine (hg.integral_hasStrictDerivAt T τ).hasDerivAt.neg.congr_of_eventuallyEq
      (Eventually.of_forall fun σ => ?_)
    exact intervalIntegral.integral_symm T σ
  have hE : HasDerivAt (fun σ => Real.exp (σ / τ₀)) (Real.exp (τ / τ₀) * (1 / τ₀)) τ :=
    ((hasDerivAt_id τ).div_const τ₀).exp
  have h := (hE.mul hG).const_mul (m * τ₀)⁻¹
  rw [hrep]
  convert h using 1
  simp only [mul_neg, ← mul_assoc (Real.exp (τ / τ₀)), exp_div_mul_exp_neg_div, one_mul]
  ring

/-- **The selected acceleration solves the equation** `mα = f + mτ₀ α′`. -/
theorem selectedAcceleration_solves (hm : m ≠ 0) (hτ₀ : τ₀ ≠ 0) (hf : Continuous f)
    (hfc : HasCompactSupport f) (τ : ℝ) :
    m * selectedAcceleration m τ₀ f τ =
      f τ + m * τ₀ * deriv (selectedAcceleration m τ₀ f) τ := by
  rw [(hasDerivAt_selectedAcceleration hf hfc τ).deriv]
  field_simp
  ring

theorem differentiable_selectedAcceleration (hf : Continuous f)
    (hfc : HasCompactSupport f) : Differentiable ℝ (selectedAcceleration m τ₀ f) := fun τ =>
  (hasDerivAt_selectedAcceleration hf hfc τ).differentiableAt

/-- For a smooth force the selected acceleration is smooth. -/
theorem contDiff_selectedAcceleration (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) : ContDiff ℝ ∞ (selectedAcceleration m τ₀ f) := by
  have hd : deriv (selectedAcceleration m τ₀ f) =
      fun τ => τ₀⁻¹ * selectedAcceleration m τ₀ f τ - (m * τ₀)⁻¹ * f τ :=
    funext fun τ => (hasDerivAt_selectedAcceleration hf.continuous hfc τ).deriv
  have hdiff := differentiable_selectedAcceleration (m := m) (τ₀ := τ₀) hf.continuous hfc
  have key : ∀ n : ℕ, ContDiff ℝ n (selectedAcceleration m τ₀ f) := by
    intro n
    induction n with
    | zero => exact contDiff_zero.mpr hdiff.continuous
    | succ n ih =>
      rw [Nat.cast_succ]
      refine contDiff_succ_iff_deriv.mpr ⟨hdiff, by simp, ?_⟩
      rw [hd]
      exact (contDiff_const.mul ih).sub (contDiff_const.mul (contDiff_infty.mp hf n))
  exact contDiff_infty.mpr key

/-- A function with `β′ = c β` is `β(0) e^{cτ}`. -/
theorem eq_mul_exp_of_hasDerivAt {β : ℝ → ℝ} {c : ℝ} (h : ∀ τ, HasDerivAt β (c * β τ) τ)
    (τ : ℝ) : β τ = β 0 * Real.exp (c * τ) := by
  have hg : ∀ σ, HasDerivAt (fun σ => Real.exp (-c * σ) * β σ) 0 σ := fun σ => by
    have h1 : HasDerivAt (fun σ => Real.exp (-c * σ)) (Real.exp (-c * σ) * (-c * 1)) σ :=
      ((hasDerivAt_id' σ).const_mul (-c)).exp
    convert h1.mul (h σ) using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun σ => (hg σ).differentiableAt)
    (fun σ => (hg σ).deriv) τ 0
  simp only [mul_zero, Real.exp_zero, one_mul] at hc
  calc β τ = Real.exp (c * τ) * (Real.exp (-c * τ) * β τ) := by
        rw [← mul_assoc, ← Real.exp_add, show c * τ + -c * τ = 0 by ring, Real.exp_zero, one_mul]
    _ = β 0 * Real.exp (c * τ) := by rw [hc]; ring

/-- **The solutions of `mα = f + mτ₀ α′`**: a differentiable `α` is a solution exactly when
`α = α_sel + C e^{τ/τ₀}` for a constant `C`, with the selected acceleration `α_sel`. -/
theorem solution_iff (hm : m ≠ 0) (hτ₀ : τ₀ ≠ 0) (hf : Continuous f) (hfc : HasCompactSupport f)
    {α : ℝ → ℝ} (hα : Differentiable ℝ α) :
    (∀ τ, m * α τ = f τ + m * τ₀ * deriv α τ) ↔
      ∃ C, ∀ τ, α τ = selectedAcceleration m τ₀ f τ + C * Real.exp (τ / τ₀) := by
  constructor
  · intro h
    refine ⟨α 0 - selectedAcceleration m τ₀ f 0, fun τ => ?_⟩
    have hβd : ∀ σ, HasDerivAt (fun σ => α σ - selectedAcceleration m τ₀ f σ)
        (τ₀⁻¹ * (α σ - selectedAcceleration m τ₀ f σ)) σ := fun σ => by
      have h1 := (hα σ).hasDerivAt.sub
        (hasDerivAt_selectedAcceleration (m := m) (τ₀ := τ₀) hf hfc σ)
      convert h1 using 1
      have hda : deriv α σ = τ₀⁻¹ * α σ - (m * τ₀)⁻¹ * f σ := by
        field_simp
        linarith [h σ]
      rw [hda]
      ring
    have := eq_mul_exp_of_hasDerivAt hβd τ
    rw [show τ / τ₀ = τ₀⁻¹ * τ by ring]
    linarith
  · rintro ⟨C, hC⟩ τ
    have hαe : α = fun σ => selectedAcceleration m τ₀ f σ + C * Real.exp (σ / τ₀) := funext hC
    have hd : HasDerivAt α (τ₀⁻¹ * selectedAcceleration m τ₀ f τ - (m * τ₀)⁻¹ * f τ +
        C * (Real.exp (τ / τ₀) * (1 / τ₀))) τ := by
      rw [hαe]
      exact (hasDerivAt_selectedAcceleration hf hfc τ).add
        ((((hasDerivAt_id τ).div_const τ₀).exp).const_mul C)
    rw [hd.deriv, hC τ]
    field_simp
    ring

theorem tendsto_abs_mul_exp {C : ℝ} (hC : C ≠ 0) (hτ₀ : 0 < τ₀) :
    Tendsto (fun τ => |C| * Real.exp (τ / τ₀)) atTop atTop :=
  Tendsto.const_mul_atTop (abs_pos.mpr hC)
    (Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const hτ₀))

/-- **The selection**: the selected acceleration is the only solution of `mα = f + mτ₀ α′` that
stays bounded as `τ → +∞`. -/
theorem eq_selectedAcceleration_of_bounded (hm : m ≠ 0) (hτ₀ : 0 < τ₀) (hf : Continuous f)
    (hfc : HasCompactSupport f) {α : ℝ → ℝ} (hα : Differentiable ℝ α)
    (h : ∀ τ, m * α τ = f τ + m * τ₀ * deriv α τ) {M τ₁ : ℝ}
    (hb : ∀ τ, τ₁ ≤ τ → |α τ| ≤ M) : α = selectedAcceleration m τ₀ f := by
  obtain ⟨C, hC⟩ := (solution_iff hm hτ₀.ne' hf hfc hα).mp h
  obtain ⟨T, hT⟩ := exists_eq_zero_of_lt hfc
  have hC0 : C = 0 := by
    by_contra hne
    obtain ⟨τ, hτ⟩ := (((tendsto_abs_mul_exp hne hτ₀).eventually_gt_atTop M).and
      (eventually_ge_atTop (max τ₁ T))).exists
    have h1 := hb τ (le_trans (le_max_left _ _) hτ.2)
    rw [hC τ, selectedAcceleration_eq_zero_of_le hT (le_trans (le_max_right _ _) hτ.2), zero_add,
      abs_mul, abs_of_pos (Real.exp_pos _)] at h1
    linarith [hτ.1]
  funext τ
  rw [hC τ, hC0, zero_mul, add_zero]

/-- **The runaways**: every other solution of `mα = f + mτ₀ α′` has `|α| → ∞` as `τ → +∞`. -/
theorem tendsto_abs_of_ne_selectedAcceleration (hm : m ≠ 0) (hτ₀ : 0 < τ₀) (hf : Continuous f)
    (hfc : HasCompactSupport f) {α : ℝ → ℝ} (hα : Differentiable ℝ α)
    (h : ∀ τ, m * α τ = f τ + m * τ₀ * deriv α τ) (hne : α ≠ selectedAcceleration m τ₀ f) :
    Tendsto (fun τ => |α τ|) atTop atTop := by
  obtain ⟨C, hC⟩ := (solution_iff hm hτ₀.ne' hf hfc hα).mp h
  obtain ⟨T, hT⟩ := exists_eq_zero_of_lt hfc
  have hC0 : C ≠ 0 := fun h0 => hne (funext fun τ => by rw [hC τ, h0, zero_mul, add_zero])
  refine (tendsto_abs_mul_exp hC0 hτ₀).congr' ?_
  filter_upwards [eventually_ge_atTop T] with τ hτ
  rw [hC τ, selectedAcceleration_eq_zero_of_le hT hτ, zero_add, abs_mul,
    abs_of_pos (Real.exp_pos _)]

/-- For a nonnegative force, positive at `s₀`, the selected acceleration is positive at every
`τ < s₀`. -/
theorem selectedAcceleration_pos (hm : 0 < m) (hτ₀ : 0 < τ₀) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hf0 : ∀ s, 0 ≤ f s) {s₀ : ℝ} (hs₀ : 0 < f s₀) {τ : ℝ}
    (hτ : τ < s₀) : 0 < selectedAcceleration m τ₀ f τ := by
  rw [selectedAcceleration]
  refine mul_pos (inv_pos.mpr (mul_pos hm hτ₀)) ?_
  have hgc : Continuous fun s => Real.exp (-(s - τ) / τ₀) * f s := by fun_prop
  have hgi : Integrable fun s => Real.exp (-(s - τ) / τ₀) * f s :=
    hgc.integrable_of_hasCompactSupport hfc.mul_left
  have hg0 : ∀ s, 0 ≤ Real.exp (-(s - τ) / τ₀) * f s := fun s =>
    mul_nonneg (Real.exp_pos _).le (hf0 s)
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hg0) hgi.integrableOn]
  have hopen : IsOpen ((Function.support fun s => Real.exp (-(s - τ) / τ₀) * f s) ∩ Ioi τ) :=
    hgc.isOpen_support.inter isOpen_Ioi
  exact hopen.measure_pos volume ⟨s₀, (mul_pos (Real.exp_pos _) hs₀).ne', hτ⟩

/-- **Preacceleration**: for a nonnegative pulse that starts at `T₁` and is positive somewhere,
the selected acceleration is positive at every `τ < T₁`, where the force still vanishes. -/
theorem selectedAcceleration_preacceleration (hm : 0 < m) (hτ₀ : 0 < τ₀) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hf0 : ∀ s, 0 ≤ f s) {s₀ : ℝ} (hs₀ : 0 < f s₀) {T₁ : ℝ}
    (hT₁ : ∀ s, s < T₁ → f s = 0) {τ : ℝ} (hτ : τ < T₁) :
    f τ = 0 ∧ 0 < selectedAcceleration m τ₀ f τ := by
  have hle : T₁ ≤ s₀ := not_lt.mp fun h => hs₀.ne' (hT₁ s₀ h)
  exact ⟨hT₁ τ hτ, selectedAcceleration_pos hm hτ₀ hf hfc hf0 hs₀ (lt_of_lt_of_le hτ hle)⟩

/-- **The precursor**: before a force that starts at `T₁`, the selected acceleration is
`α(τ) = e^{(τ − T₁)/τ₀} α(T₁)`. -/
theorem selectedAcceleration_before (hf : Continuous f) (hfc : HasCompactSupport f) {T₁ : ℝ}
    (hT₁ : ∀ s, s < T₁ → f s = 0) {τ : ℝ} (hτ : τ ≤ T₁) :
    selectedAcceleration m τ₀ f τ =
      Real.exp ((τ - T₁) / τ₀) * selectedAcceleration m τ₀ f T₁ := by
  have hT₁' : ∀ s, s ≤ T₁ → f s = 0 := by
    intro s hs
    rcases hs.lt_or_eq with h | rfl
    · exact hT₁ s h
    · have h1 : Tendsto f (𝓝[<] s) (𝓝 (f s)) := hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h0 : Tendsto f (𝓝[<] s) (𝓝 0) := tendsto_const_nhds.congr'
        (eventually_nhdsWithin_of_forall fun x hx => (hT₁ x hx).symm)
      exact tendsto_nhds_unique h1 h0
  obtain ⟨T, hT⟩ := exists_eq_zero_of_lt hfc
  have hg : Continuous fun s => Real.exp (-s / τ₀) * f s := by fun_prop
  have hz : ∫ s in τ..T₁, Real.exp (-s / τ₀) * f s = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_]
    · simp
    · rw [uIcc_of_le hτ] at hs
      simp [hT₁' s hs.2]
  rw [selectedAcceleration_eq hf hfc hT τ, selectedAcceleration_eq hf hfc hT T₁,
    ← intervalIntegral.integral_add_adjacent_intervals (b := T₁) (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _), hz, zero_add,
    show Real.exp (τ / τ₀) = Real.exp ((τ - T₁) / τ₀) * Real.exp (T₁ / τ₀) by
      rw [← Real.exp_add]; congr 1; ring]
  ring

end Scalar

/-! ### An instance: a smooth positive pulse -/

/-- The smooth pulse `exp(−1/(1 − s²))` on `(−1, 1)`, `0` outside. -/
def pulse (s : ℝ) : ℝ := expNegInvGlue (1 - s ^ 2)

theorem contDiff_pulse : ContDiff ℝ ∞ pulse :=
  (expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_const.sub (contDiff_id.pow 2))

theorem pulse_nonneg (s : ℝ) : 0 ≤ pulse s := expNegInvGlue.nonneg _

theorem pulse_eq_zero {s : ℝ} (hs : 1 < |s|) : pulse s = 0 :=
  expNegInvGlue.zero_of_nonpos (by nlinarith [sq_abs s, abs_nonneg s])

theorem hasCompactSupport_pulse : HasCompactSupport pulse :=
  HasCompactSupport.intro (isCompact_closedBall 0 1) fun s hs =>
    pulse_eq_zero (by simpa [Real.norm_eq_abs] using hs)

theorem pulse_zero_pos : 0 < pulse 0 := by
  simpa [pulse] using expNegInvGlue.pos_of_pos one_pos

theorem pulse_eq_zero_of_lt {s : ℝ} (hs : s < -1) : pulse s = 0 :=
  pulse_eq_zero (by rw [abs_of_neg (by linarith)]; linarith)

/-- **The preacceleration of the pulse**: the selected acceleration for the pulse is positive at
every `τ < −1`, before the pulse starts. -/
theorem selectedAcceleration_pulse {m τ₀ : ℝ} (hm : 0 < m) (hτ₀ : 0 < τ₀) {τ : ℝ}
    (hτ : τ < -1) : pulse τ = 0 ∧ 0 < selectedAcceleration m τ₀ pulse τ :=
  selectedAcceleration_preacceleration hm hτ₀ contDiff_pulse.continuous hasCompactSupport_pulse
    pulse_nonneg pulse_zero_pos (fun _ hs => pulse_eq_zero_of_lt hs) hτ

/-! ### Zero force -/

/-- **The free rectilinear motion against the equation of Abraham and Lorentz**: a rectilinear
solution of the free equation of Lorentz and Dirac `m u̇ = g` with bounded proper acceleration for
`τ ≥ 0` is uniform, `α = 0`. The rapidity is a solution of the free equation of Abraham and
Lorentz, and `abrahamLorentz_free_eq_zero` applies; this agrees with `selectedAcceleration_zero`.
-/
theorem rectilinear_free_eq_zero (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {ϑ : ℝ → ℝ}
    (hϑ : ContDiff ℝ 2 ϑ)
    (h : ∀ τ, m • deriv (rectilinearVelocity ϑ) τ = lorentzDiracForce e (rectilinearVelocity ϑ) τ)
    {C : ℝ} (hC : ∀ τ, 0 ≤ τ → |deriv ϑ τ| ≤ C) (τ : ℝ) : deriv ϑ τ = 0 := by
  set w : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1 with hw
  have hd1 : Differentiable ℝ ϑ := hϑ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv ϑ) :=
    (ContDiff.deriv' (n := 1) hϑ).differentiable (by norm_num)
  have hv : ContDiff ℝ 2 fun σ => ϑ σ • w := hϑ.smul contDiff_const
  have hdv : deriv (fun σ => ϑ σ • w) = fun σ => deriv ϑ σ • w :=
    funext fun σ => ((hd1 σ).hasDerivAt.smul_const w).deriv
  have hddv : ∀ σ, deriv (fun σ => deriv ϑ σ • w) σ = deriv (deriv ϑ) σ • w := fun σ =>
    ((hd2 σ).hasDerivAt.smul_const w).deriv
  have hscalar : ∀ σ, m * deriv ϑ σ = 2 / 3 * (e ^ 2 / (4 * π)) * deriv (deriv ϑ) σ :=
    fun σ => by
      have := (lorentzDirac_rectilinear_force_iff m e hϑ 0 σ).mp (by simpa using h σ)
      simpa using this
  have hAL : ∀ σ, m • deriv (fun σ => ϑ σ • w) σ =
      (2 / 3 * (e ^ 2 / (4 * π))) • deriv (deriv fun σ => ϑ σ • w) σ := fun σ => by
    rw [hdv, hddv]
    simp only [smul_smul, hscalar]
  have hb : ∀ σ, 0 ≤ σ → ‖deriv (fun σ => ϑ σ • w) σ‖ ≤ C := fun σ hσ => by
    rw [hdv]
    simpa [hw, norm_smul] using hC σ hσ
  have := abrahamLorentz_free_eq_zero e m he hm hv hAL hb τ
  rw [hdv] at this
  simpa [hw] using this

/-! ### The world line -/

/-- The time `τ₀ = (2/3)(e²/4π)/m` of radiation damping. -/
def radiationTime (e m : ℝ) : ℝ := 2 / 3 * (e ^ 2 / (4 * π)) / m

theorem radiationTime_pos {e m : ℝ} (he : e ≠ 0) (hm : 0 < m) : 0 < radiationTime e m :=
  div_pos (dampingConstant_pos he) hm

theorem mul_radiationTime (e : ℝ) {m : ℝ} (hm : m ≠ 0) :
    m * radiationTime e m = 2 / 3 * (e ^ 2 / (4 * π)) := by
  rw [radiationTime]
  field_simp

/-- **The equation of Lorentz and Dirac for a rectilinear motion** in the form
`mα = f + mτ₀ α′` with the time of radiation damping `τ₀ = (2/3)(e²/4π)/m`. -/
theorem lorentzDirac_rectilinear_iff_radiationTime (e : ℝ) {m : ℝ} (hm : m ≠ 0) {ϑ : ℝ → ℝ}
    (hϑ : ContDiff ℝ 2 ϑ) (f : ℝ → ℝ) (τ : ℝ) :
    m • deriv (rectilinearVelocity ϑ) τ =
        f τ • rectilinearDirection ϑ τ + lorentzDiracForce e (rectilinearVelocity ϑ) τ ↔
      m * deriv ϑ τ = f τ + m * radiationTime e m * deriv (deriv ϑ) τ := by
  rw [mul_radiationTime e hm]
  exact lorentzDirac_rectilinear_force_iff m e hϑ f τ

/-- The rapidity `ϑ(τ) = ϑ₀ + ∫₀^τ α` of the selected acceleration. -/
def selectedRapidity (m τ₀ : ℝ) (f : ℝ → ℝ) (ϑ₀ τ : ℝ) : ℝ :=
  ϑ₀ + ∫ σ in (0 : ℝ)..τ, selectedAcceleration m τ₀ f σ

section WorldLine

variable {m τ₀ : ℝ} {f : ℝ → ℝ}

theorem hasDerivAt_selectedRapidity (hf : Continuous f) (hfc : HasCompactSupport f) (ϑ₀ τ : ℝ) :
    HasDerivAt (selectedRapidity m τ₀ f ϑ₀) (selectedAcceleration m τ₀ f τ) τ := by
  have hc := (differentiable_selectedAcceleration (m := m) (τ₀ := τ₀) hf hfc).continuous
  exact ((hc.integral_hasStrictDerivAt 0 τ).hasDerivAt).const_add ϑ₀

theorem deriv_selectedRapidity (hf : Continuous f) (hfc : HasCompactSupport f) (ϑ₀ : ℝ) :
    deriv (selectedRapidity m τ₀ f ϑ₀) = selectedAcceleration m τ₀ f :=
  funext fun τ => (hasDerivAt_selectedRapidity hf hfc ϑ₀ τ).deriv

theorem selectedRapidity_zero (m τ₀ : ℝ) (f : ℝ → ℝ) (ϑ₀ : ℝ) :
    selectedRapidity m τ₀ f ϑ₀ 0 = ϑ₀ := by
  simp [selectedRapidity]

theorem contDiff_selectedRapidity (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (ϑ₀ : ℝ) :
    ContDiff ℝ ∞ (selectedRapidity m τ₀ f ϑ₀) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun τ => (hasDerivAt_selectedRapidity hf.continuous hfc ϑ₀ τ).differentiableAt, ?_⟩
  rw [deriv_selectedRapidity hf.continuous hfc]
  exact contDiff_selectedAcceleration hf hfc

/-- The selected world line is inertial after the force: `u̇ = 0` once `f = 0`. -/
theorem deriv_selectedVelocity_eq_zero_of_le (hf : Continuous f) (hfc : HasCompactSupport f)
    (ϑ₀ : ℝ) {T : ℝ} (hT : ∀ s, T < s → f s = 0) {τ : ℝ} (hτ : T ≤ τ) :
    deriv (rectilinearVelocity (selectedRapidity m τ₀ f ϑ₀)) τ = 0 := by
  rw [deriv_rectilinearVelocity fun σ =>
      (hasDerivAt_selectedRapidity hf hfc ϑ₀ σ).differentiableAt]
  simp only [deriv_selectedRapidity hf hfc, selectedAcceleration_eq_zero_of_le hT hτ, zero_smul]

end WorldLine

/-- **The selected world line solves the equation of Lorentz and Dirac**: for a smooth compactly
supported proper force `f`, the rectilinear motion with the selected rapidity has a smooth unit
four-velocity `u` with `m u̇ = f n + g`, with the force `g = lorentzDiracForce e u` of the library
and the external four-force `f n` along the direction of motion. -/
theorem selected_lorentzDirac (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (ϑ₀ τ : ℝ) :
    m • deriv (rectilinearVelocity (selectedRapidity m (radiationTime e m) f ϑ₀)) τ =
      f τ • rectilinearDirection (selectedRapidity m (radiationTime e m) f ϑ₀) τ +
        lorentzDiracForce e (rectilinearVelocity (selectedRapidity m (radiationTime e m) f ϑ₀))
          τ := by
  have hτ₀ := (radiationTime_pos he hm).ne'
  have hϑ := contDiff_selectedRapidity (m := m) (τ₀ := radiationTime e m) hf hfc ϑ₀
  rw [lorentzDirac_rectilinear_force_iff m e (hϑ.of_le (by simp)) f τ,
    deriv_selectedRapidity hf.continuous hfc, ← mul_radiationTime e hm.ne']
  exact selectedAcceleration_solves hm.ne' hτ₀ hf.continuous hfc τ

/-- The selected four-velocity is smooth. -/
theorem contDiff_selectedVelocity (m τ₀ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (ϑ₀ : ℝ) :
    ContDiff ℝ ∞ (rectilinearVelocity (selectedRapidity m τ₀ f ϑ₀)) :=
  contDiff_rectilinearVelocity (contDiff_selectedRapidity hf hfc ϑ₀)

/-- **The rectilinear solutions of the equation of Lorentz and Dirac**: if the four-velocity of
a rectilinear motion with a `C²` rapidity solves `m u̇ = f n + g`, then its proper acceleration is
`α = α_sel + C e^{τ/τ₀}` for a constant `C`. -/
theorem rectilinear_lorentzDirac_selection (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ)
    (h : ∀ τ, m • deriv (rectilinearVelocity ϑ) τ =
      f τ • rectilinearDirection ϑ τ + lorentzDiracForce e (rectilinearVelocity ϑ) τ) :
    ∃ C, ∀ τ, deriv ϑ τ =
      selectedAcceleration m (radiationTime e m) f τ + C * Real.exp (τ / radiationTime e m) := by
  have hτ₀ := (radiationTime_pos he hm).ne'
  have hd2 : Differentiable ℝ (deriv ϑ) :=
    (ContDiff.deriv' (n := 1) hϑ).differentiable (by norm_num)
  refine (solution_iff hm.ne' hτ₀ hf hfc hd2).mp fun τ => ?_
  rw [mul_radiationTime e hm.ne']
  exact (lorentzDirac_rectilinear_force_iff m e hϑ f τ).mp (h τ)

/-- **The selection of the physical world line**: a rectilinear solution of `m u̇ = f n + g` whose
proper acceleration stays bounded as `τ → +∞` is the selected world line with its initial
rapidity: `ϑ = ϑ(0) + ∫₀^τ α_sel`. -/
theorem rectilinear_lorentzDirac_eq_selected (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ)
    (h : ∀ τ, m • deriv (rectilinearVelocity ϑ) τ =
      f τ • rectilinearDirection ϑ τ + lorentzDiracForce e (rectilinearVelocity ϑ) τ)
    {M τ₁ : ℝ} (hb : ∀ τ, τ₁ ≤ τ → |deriv ϑ τ| ≤ M) :
    ϑ = selectedRapidity m (radiationTime e m) f (ϑ 0) := by
  have hτ₀ := radiationTime_pos he hm
  have hd1 : Differentiable ℝ ϑ := hϑ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv ϑ) :=
    (ContDiff.deriv' (n := 1) hϑ).differentiable (by norm_num)
  have hα : deriv ϑ = selectedAcceleration m (radiationTime e m) f :=
    eq_selectedAcceleration_of_bounded hm.ne' hτ₀ hf hfc hd2 (fun τ => by
      rw [mul_radiationTime e hm.ne']
      exact (lorentzDirac_rectilinear_force_iff m e hϑ f τ).mp (h τ)) hb
  have hz : ∀ σ, HasDerivAt (fun σ => ϑ σ - selectedRapidity m (radiationTime e m) f (ϑ 0) σ)
      0 σ := fun σ => by
    have := (hd1 σ).hasDerivAt.sub
      (hasDerivAt_selectedRapidity (m := m) (τ₀ := radiationTime e m) hf hfc (ϑ 0) σ)
    rwa [hα, sub_self] at this
  funext τ
  have := is_const_of_deriv_eq_zero (fun σ => (hz σ).differentiableAt) (fun σ => (hz σ).deriv)
    τ 0
  simp only [selectedRapidity_zero, sub_self] at this
  linarith

/-- **The runaways of the equation of Lorentz and Dirac**: every other rectilinear solution of
`m u̇ = f n + g` has a proper acceleration `|α| → ∞` as `τ → +∞`. -/
theorem rectilinear_lorentzDirac_runaway (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ)
    (h : ∀ τ, m • deriv (rectilinearVelocity ϑ) τ =
      f τ • rectilinearDirection ϑ τ + lorentzDiracForce e (rectilinearVelocity ϑ) τ)
    (hne : deriv ϑ ≠ selectedAcceleration m (radiationTime e m) f) :
    Tendsto (fun τ => |deriv ϑ τ|) atTop atTop := by
  have hd2 : Differentiable ℝ (deriv ϑ) :=
    (ContDiff.deriv' (n := 1) hϑ).differentiable (by norm_num)
  refine tendsto_abs_of_ne_selectedAcceleration hm.ne' (radiationTime_pos he hm) hf hfc hd2
    (fun τ => ?_) hne
  rw [mul_radiationTime e hm.ne']
  exact (lorentzDirac_rectilinear_force_iff m e hϑ f τ).mp (h τ)

end ProjectAinos.Electrodynamics.RadiationReaction
