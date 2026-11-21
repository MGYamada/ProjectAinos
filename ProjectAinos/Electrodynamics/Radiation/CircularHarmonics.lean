/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.Synchrotron
public import ProjectAinos.Electrodynamics.Radiation.CollisionSpectrum
public import ProjectAinos.SpecialFunctions.Kapteyn
import Mathlib.Tactic

/-! # Polarized radiation harmonics of a circular orbit

In the far observer's time a transverse component of the electric amplitude is the
second derivative of the transverse retarded position times −e/(4π). On a circle
the retarded phase is the inverse Kepler map. This identifies the Fourier coefficients
of the observed field with Bessel functions at the actual viewing angle.
-/

@[expose] public section
noncomputable section

open Complex Filter MeasureTheory Set Function
open scoped Real Topology ContDiff
namespace ProjectAinos.Electrodynamics.Radiation.Synchrotron
open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity SubluminalWorldline
open CollisionSpectrum SpecialFunctions.Kapteyn SmoothGeometry.Fourier.PeriodicSeries

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Fourier coefficient of a polarized far-zone electric amplitude in observer time,
with angular frequency Ω and period 2π in the phase M = Ωt. -/
def observedHarmonic (e : ℝ) (w : SubluminalWorldline) (n p : E3) (Ω : ℝ) (m : ℤ) : ℂ :=
  coefficient (fun M => ((inner ℝ p (observedAmplitude e w n (M/Ω)) : ℝ) : ℂ)) m

/-- Parseval's energy identity for one polarized far-field signal measured by the observer.
For a circular orbit this interval is one full period in phase. -/
theorem harmonic_parseval (e : ℝ) (w : SubluminalWorldline) {n : E3} (hn : ‖n‖ = 1)
    (p : E3) (Ω : ℝ) : HasSum (fun m : ℤ => ‖observedHarmonic e w n p Ω m‖^2)
      ((2*π)⁻¹ * ∫ M in -π..π, (inner ℝ p (observedAmplitude e w n (M/Ω)))^2) := by
  have h : Continuous (fun M : ℝ => observedAmplitude e w n (M/Ω)) :=
    ((continuous_amplitude w e hn).comp (continuous_retardedOfObserver w hn)).comp
      (continuous_id.div_const Ω)
  have hp : Continuous (fun M : ℝ => ((inner ℝ p (observedAmplitude e w n (M/Ω)) : ℝ) : ℂ)) :=
    continuous_ofReal.comp (continuous_const.inner h)
  simpa only [observedHarmonic, norm_real, Real.norm_eq_abs, sq_abs] using hasSum_sq hp

private def position (w : SubluminalWorldline) (n p : E3) (Ω M : ℝ) : ℂ :=
  (inner ℝ p (w.r (retardedOfObserver w n (M/Ω))) : ℝ)

private def velocity (e : ℝ) (w : SubluminalWorldline) (n p : E3) (Ω M : ℝ) : ℂ :=
  (inner ℝ p (velocityAmplitude e n (deriv w.r (retardedOfObserver w n (M/Ω)))) : ℝ)

private theorem deriv_position (e : ℝ) (w : SubluminalWorldline) {n : E3} (hn : ‖n‖ = 1)
    {p : E3} (hp : inner ℝ p n = 0) {Ω : ℝ} (hΩ : Ω ≠ 0) (M : ℝ) :
    velocity e w n p Ω M = -(e : ℂ)*Ω/(4*π)*deriv (position w n p Ω) M := by
  let τ := retardedOfObserver w n (M/Ω)
  have hτ := (hasDerivAt_retardedOfObserver w hn (M/Ω)).comp M ((hasDerivAt_id M).div_const Ω)
  have hx := (w.differentiable_r τ).hasDerivAt.scomp M hτ
  have hd := ((hasDerivAt_const M p).inner ℝ hx).ofReal_comp
  have he : deriv (position w n p Ω) M = _ := hd.deriv
  rw [he, velocity, velocityAmplitude, Relativistic.cross_cross, real_inner_smul_right,
    inner_sub_right,
    real_inner_smul_right, real_inner_smul_right, hp, real_inner_self_eq_norm_sq, hn]
  simp only [one_pow, mul_zero, one_mul, zero_sub, inner_zero_left, add_zero, real_inner_smul_right]
  dsimp only [τ]
  push_cast
  field_simp [ofReal_ne_zero.mpr hΩ]

private theorem deriv_velocity (e : ℝ) (w : SubluminalWorldline) {n : E3} (hn : ‖n‖ = 1)
    (p : E3) (Ω M : ℝ) : HasDerivAt (velocity e w n p Ω)
      (↑(inner ℝ p (observedAmplitude e w n (M/Ω))) / (Ω : ℂ)) M := by
  have hv := (hasDerivAt_velocityAmplitude_retardedOfObserver w e hn (M/Ω)).scomp M
    ((hasDerivAt_id M).div_const Ω)
  convert ((hasDerivAt_const M p).inner ℝ hv).ofReal_comp using 1
  · rfl
  simp only [inner_zero_left, add_zero, real_inner_smul_right]
  push_cast
  ring

private theorem from_position (e : ℝ) (w : SubluminalWorldline) {n p : E3} (hn : ‖n‖ = 1)
    (hp : inner ℝ p n = 0) {Ω : ℝ} (hΩ : Ω ≠ 0) {m : ℤ} (hm : m ≠ 0)
    {P : ℝ → ℂ} (hP : position w n p Ω = P) (hc : ContDiff ℝ 2 P) (hper : Periodic P (2*π)) :
    observedHarmonic e w n p Ω m = (e : ℂ)*Ω^2*m^2/(4*π)*coefficient P m := by
  let c : ℂ := -(e : ℂ)*Ω/(4*π)
  have hv : velocity e w n p Ω = fun M => c * deriv P M := by
    funext M
    simp only [← hP]
    exact deriv_position e w hn hp hΩ M
  have hd (M : ℝ) : ((inner ℝ p (observedAmplitude e w n (M/Ω)) : ℝ) : ℂ) =
      ((Ω : ℂ)*c) * deriv (deriv P) M := by
    have h := (deriv_velocity e w hn p Ω M).deriv
    have h' : HasDerivAt (fun s => c * deriv P s) (c * deriv (deriv P) M) M :=
      ((hc.deriv' (n := 1)).differentiable one_ne_zero M).hasDerivAt.const_mul c
    rw [hv, h'.deriv] at h
    have H := (eq_div_iff (ofReal_ne_zero.mpr hΩ)).mp h
    linear_combination -H
  unfold observedHarmonic
  simp_rw [hd]
  rw [coefficient_const_mul (hc.deriv' (n := 1) |>.continuous_deriv le_rfl),
    coefficient_second hc hper hm]
  dsimp only [c]
  ring

local notation "ex" => (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E3)
local notation "ey" => (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : E3)
local notation "ez" => (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E3)

/-- Observer in the yz plane, with components c along y and q along z. -/
def viewingDirection (c q : ℝ) : E3 := c • ey + q • ez

/-- Second transverse polarization vector for this viewing direction. -/
def meridianPolarization (c q : ℝ) : E3 := q • ey - c • ez

/-- Radial polarization vector at orbital phase α. -/
def radialAxis (α : ℝ) : E3 := Real.cos α • ex + Real.sin α • ey

/-- Tangent to the circular orbit at phase α. -/
def tangentAxis (α : ℝ) : E3 := -Real.sin α • ex + Real.cos α • ey

/-- An observation direction in the meridian of azimuth α, measured from the y axis. -/
def viewingAt (α c q : ℝ) : E3 := c • tangentAxis α + q • ez

/-- Unit polarization in the meridian when c² + q² = 1. -/
def meridianAt (α c q : ℝ) : E3 := q • tangentAxis α - c • ez

private theorem unit (α : ℝ) {c q : ℝ} (h : c^2+q^2 = 1) : ‖viewingAt α c q‖ = 1 := by
  have he : inner ℝ (viewingAt α c q) (viewingAt α c q) = 1 := by
    rw [LienardWiechert.inner_eq_sum]
    simp [viewingAt, tangentAxis]
    linear_combination h + c^2 * Real.sin_sq_add_cos_sq α
  rw [real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (viewingAt α c q)]

private theorem viewing (R Ω : ℝ) (hs : |R*Ω| < 1) (α c q t : ℝ) :
    Ω * observerTime (circular R Ω hs) (viewingAt α c q) t - α =
      meanAnomaly (R*Ω*c) (Ω*t-α) := by
  change Ω * (t - inner ℝ (viewingAt α c q) (circularPath R Ω t)) - α = _
  simp [viewingAt, tangentAxis, circularPath, LienardWiechert.inner_eq_sum, meanAnomaly,
    Real.sin_sub]
  ring

private theorem retarded {R Ω c q : ℝ} (α : ℝ) (hs : |R*Ω| < 1)
    (hu : c^2+q^2 = 1) (hΩ : Ω ≠ 0) (he : |R*Ω*c| < 1) (M : ℝ) :
    Ω*retardedOfObserver (circular R Ω hs) (viewingAt α c q) (M/Ω) - α =
      eccentricAnomaly (R*Ω*c) (M-α) := by
  let τ := retardedOfObserver (circular R Ω hs) (viewingAt α c q) (M/Ω)
  have H := viewing R Ω hs α c q τ
  rw [observerTime_retardedOfObserver _ (unit α hu), mul_div_cancel₀ _ hΩ] at H
  change Ω*τ-α = _
  rw [H, eccentric_mean he]

/-- The two transverse harmonics in any viewing direction. Rotating the meridian through
α changes both coefficients by the same unit complex phase. -/
theorem circular_harmonics_at (e α : ℝ) {R Ω c q : ℝ} (hs : |R*Ω| < 1) (hΩ : Ω ≠ 0)
    (hu : c^2+q^2 = 1) (m : ℤ) (hm : m ≠ 0) :
    let w := circular R Ω hs
    let n := viewingAt α c q
    let x := (m : ℝ)*(R*Ω*c)
    let phase := exp (-((m : ℂ)*α)*I)
    observedHarmonic e w n (radialAxis α) Ω m =
      phase * (e*Ω^2*R*m/(4*π) * deriv (besselJ m) x) ∧
    observedHarmonic e w n (meridianAt α c q) Ω m =
      phase * (e*Ω^2*R*q*m/(8*π*I) * (besselJ (m-1 : ℤ) x + besselJ (m+1 : ℤ) x)) := by
  let w := circular R Ω hs
  let n := viewingAt α c q
  let η := R*Ω*c
  have hc : |c| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg q]
  have he : |η| < 1 := by
    dsimp [η]
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hc).trans_lt hs
  have hx : inner ℝ (radialAxis α) n = 0 := by
    simp [n, viewingAt, radialAxis, tangentAxis, LienardWiechert.inner_eq_sum]
    ring
  have hq : inner ℝ (meridianAt α c q) n = 0 := by
    simp [n, viewingAt, meridianAt, tangentAxis, LienardWiechert.inner_eq_sum]
    linear_combination c*q * Real.sin_sq_add_cos_sq α
  let C (t : ℝ) : ℂ := (Real.cos (eccentricAnomaly η t) : ℝ)
  let S (t : ℝ) : ℂ := (Real.sin (eccentricAnomaly η t) : ℝ)
  have hC : ContDiff ℝ 2 C := ofRealCLM.contDiff.comp
    (Real.contDiff_cos.comp ((contDiff_eccentric he).of_le (by simp)))
  have hS : ContDiff ℝ 2 S := ofRealCLM.contDiff.comp
    (Real.contDiff_sin.comp ((contDiff_eccentric he).of_le (by simp)))
  have hpC : Periodic C (2*π) := fun t => by
    simp only [C, eccentric_add_period he, Real.cos_add_two_pi]
  have hpS : Periodic S (2*π) := fun t => by
    simp only [S, eccentric_add_period he, Real.sin_add_two_pi]
  have axisPos (τ : ℝ) :
      inner ℝ (radialAxis α) (circularPath R Ω τ) = R*Real.cos (Ω*τ-α) := by
    simp [radialAxis, circularPath, LienardWiechert.inner_eq_sum, Real.cos_sub]
    ring
  have meridianPos (τ : ℝ) : inner ℝ (meridianAt α c q) (circularPath R Ω τ) =
      R*q*Real.sin (Ω*τ-α) := by
    simp [circularPath, meridianAt, tangentAxis, LienardWiechert.inner_eq_sum, Real.sin_sub]
    ring
  have hp₁ : position w n (radialAxis α) Ω = fun t => (R : ℂ)*C (t-α) := by
    funext t
    change ((inner ℝ (radialAxis α) (circularPath R Ω (retardedOfObserver w n (t/Ω))) : ℝ) : ℂ) = _
    rw [axisPos, retarded α hs hu hΩ he, ofReal_mul]
  have hp₂ : position w n (meridianAt α c q) Ω = fun t => ((R*q : ℝ) : ℂ)*S (t-α) := by
    funext t
    change ((inner ℝ (meridianAt α c q)
      (circularPath R Ω (retardedOfObserver w n (t/Ω))) : ℝ) : ℂ) = _
    rw [meridianPos, retarded α hs hu hΩ he, ofReal_mul]
  have shift : ContDiff ℝ 2 (fun t : ℝ => t-α) := contDiff_id.sub contDiff_const
  have h₁ := from_position e w (unit α hu) hx hΩ hm hp₁ (contDiff_const.mul (hC.comp shift))
    (fun t => by rw [show t+2*π-α=t-α+2*π by ring, hpC])
  have h₂ := from_position e w (unit α hu) hq hΩ hm hp₂ (contDiff_const.mul (hS.comp shift))
    (fun t => by rw [show t+2*π-α=t-α+2*π by ring, hpS])
  rw [coefficient_const_mul (f := fun t => C (t-α)) (hC.comp shift).continuous,
    coefficient_translate hpC,
    show coefficient C m = _ from coefficient_cos he m hm] at h₁
  rw [coefficient_const_mul (f := fun t => S (t-α)) (hS.comp shift).continuous,
    coefficient_translate hpS,
    show coefficient S m = _ from coefficient_sin he m hm] at h₂
  dsimp only [η] at h₁ h₂
  constructor
  · rw [h₁]
    push_cast
    field_simp [Int.cast_ne_zero.mpr hm, Real.pi_ne_zero]
  · rw [h₂]
    push_cast
    field_simp [Int.cast_ne_zero.mpr hm, Real.pi_ne_zero, I_ne_zero]
    ring

/-- Polarized harmonics in the yz meridian, including the rotation axis. -/
theorem circular_harmonics (e : ℝ) {R Ω c q : ℝ} (hs : |R*Ω| < 1) (hΩ : Ω ≠ 0)
    (hu : c^2+q^2 = 1) (m : ℤ) (hm : m ≠ 0) :
    let w := circular R Ω hs
    let n := viewingDirection c q
    let x := (m : ℝ)*(R*Ω*c)
    observedHarmonic e w n ex Ω m =
      e*Ω^2*R*m/(4*π) * deriv (besselJ m) x ∧
    observedHarmonic e w n (meridianPolarization c q) Ω m =
      e*Ω^2*R*q*m/(8*π*I) * (besselJ (m-1 : ℤ) x + besselJ (m+1 : ℤ) x) := by
  simpa [radialAxis, tangentAxis, viewingAt, viewingDirection, meridianAt, meridianPolarization]
    using circular_harmonics_at e 0 hs hΩ hu m hm

end ProjectAinos.Electrodynamics.Radiation.Synchrotron
