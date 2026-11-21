/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Hankel
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-! # Continuation of the outgoing Hankel function to the upper half-plane

Displacing each Schläfli ray to Im t = −π/2 gives the Macdonald integral. In the
first quadrant both representations converge absolutely and agree. This supplies the
Hankel values and derivatives on the positive imaginary axis used in Coulomb scattering.
-/

@[expose] public section
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Real Topology
namespace ProjectAinos.SpecialFunctions.Bessel
open Schlaefli

private def W (a z w : ℂ) := exp (-z*sinh w+a*w)
private def edge (R s : ℝ) : ℂ := R-s*I
private def coeff (a : ℂ) := exp (-(a*(π/2))*I)
private def angular (a z : ℂ) (s : ℝ) := exp ((z*Real.sin s-a*s)*I)
private def Kline (a z : ℂ) (t : ℝ) := exp (-(-I*z)*Real.cosh t+a*t)
private def halfArc (a z : ℂ) := ∫ t in 0..π/2, angular a z t
private def halfLine (a z : ℂ) := ∫ t : ℝ in Ioi 0, Kline a z t

private theorem along (a z : ℂ) (R : ℝ) :
    W a z (edge R (π/2)) = coeff a*Kline a z R := by
  rw [W,edge,sinh_sub,cosh_mul_I,sinh_mul_I,← ofReal_cos,← ofReal_sin,
    Real.cos_pi_div_two,Real.sin_pi_div_two,coeff,Kline,← exp_add]
  simp only [ofReal_zero,ofReal_one,mul_zero,one_mul,zero_sub,ofReal_div,ofReal_ofNat,ofReal_cosh]
  congr 1
  ring

private theorem exp_re (a z : ℂ) (R s : ℝ) :
    ‖W a z (edge R s)‖ = Real.exp (-(z.re*Real.sinh R*Real.cos s+
      z.im*Real.cosh R*Real.sin s)+a.re*R+a.im*s) := by
  rw [W,edge,sinh_sub,cosh_mul_I,sinh_mul_I,← ofReal_cos,← ofReal_sin,
    ← ofReal_cosh,← ofReal_sinh,norm_exp]
  congr 1
  simp [mul_re,mul_im]
  simp only [← ofReal_cos,← ofReal_sin,← ofReal_sinh,ofReal_re]
  ring

private theorem rim {a z : ℂ} (hz : 0 < z.re) (hi : 0 < z.im) :
    ∀ᶠ R : ℝ in atTop, ∀ s ∈ Icc 0 (π/2), ‖W a z (edge R s)‖ ≤ Real.exp (-R) := by
  let p := min z.re z.im
  have hp : 0 < p := lt_min hz hi
  filter_upwards [eventually_ge_atTop (0:ℝ),eventually_ge_atTop (2*(|a.re|+2)/p),
    eventually_ge_atTop (p+|a.im| * (π/2))] with R hR h₁ h₂
  intro s hs
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2,Real.pi_pos])
  have hcos := Real.cos_nonneg_of_mem_Icc (show s ∈ Icc (-(π/2)) (π/2) from
    ⟨by linarith [hs.1,Real.pi_pos],hs.2⟩)
  have H : 1 ≤ Real.cos s+Real.sin s := by
    nlinarith [Real.sin_sq_add_cos_sq s, mul_nonneg hcos hsin]
  have hS := Real.sinh_nonneg_iff.mpr hR
  have h₃ : p*Real.sinh R ≤ z.re*Real.sinh R*Real.cos s+z.im*Real.cosh R*Real.sin s := by
    have h₄ := Real.cosh_sub_sinh R
    have h₅ : Real.sinh R ≤ Real.cosh R := by linarith [Real.exp_pos (-R)]
    nlinarith only [mul_le_mul_of_nonneg_left H (mul_nonneg hp.le hS),
      mul_le_mul_of_nonneg_right (min_le_left z.re z.im) (mul_nonneg hS hcos),
      mul_le_mul_of_nonneg_right (mul_le_mul (min_le_right z.re z.im) h₅ hS hi.le) hsin]
  have h₄ : R^2/2 ≤ Real.cosh R := by
    have h := (Real.hasSum_cosh R).summable.le_tsum 1 (fun n _ => by rw [pow_mul]; positivity)
    rw [(Real.hasSum_cosh R).tsum_eq] at h
    norm_num at h
    exact h
  have h₅ : R^2/2-1 ≤ Real.sinh R := by
    linarith [Real.cosh_sub_sinh R, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hR)]
  rw [exp_re,Real.exp_le_exp]
  rw [div_le_iff₀ hp] at h₁
  nlinarith only [h₃,h₂,mul_le_mul_of_nonneg_left h₅ hp.le,
    mul_le_mul_of_nonneg_right h₁ hR, mul_le_mul_of_nonneg_right (le_abs_self a.re) hR,
    mul_le_mul (le_abs_self a.im) hs.2 hs.1 (abs_nonneg a.im)]

private theorem segment {f F : ℂ → ℂ} (hF : ∀ w, HasDerivAt F (f w) w)
    (hf : Continuous f) (w v : ℂ) (R : ℝ) :
    F (w+v*R)-F w = ∫ t in 0..R, v*f (w+v*t) := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => F (w+v*s)) (v*f (w+v*t)) t := by
    have h := (((hasDerivAt_id' (t : ℂ)).const_mul v).const_add w)
    convert ((hF _).comp (t : ℂ) h).comp_ofReal using 1
    · rfl
    · simp; ring
  symm
  simpa only [ofReal_zero,mul_zero,add_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := R) (fun t _ => hd t)
      (Continuous.intervalIntegrable (by fun_prop) ..)

private theorem ray_rotation (a z : ℂ) (hz : 0 < z.re) (hi : 0 < z.im) :
    ray a z = -I*halfArc a z+coeff a*halfLine a z := by
  have hw : Differentiable ℂ (W a z) := by unfold W; fun_prop
  obtain ⟨F,h⟩ := hw.isExactOn_univ
  have hF (w : ℂ) := h w (mem_univ w)
  have S := segment hF hw.continuous
  have hd (R : ℝ) : F (edge R (π/2))-F (R : ℂ) = ∫ s in 0..π/2, -I*W a z (edge R s) := by
    simpa only [edge,neg_mul,sub_eq_add_neg,mul_comm I] using S R (-I) (π/2)
  have hshift : Tendsto (fun R : ℝ => F (edge R (π/2))-F (R : ℂ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun R : ℝ => Real.exp (-R)*(π/2)) atTop (𝓝 0) by
      simpa only [zero_mul,Function.comp_apply] using
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const (π/2))
    filter_upwards [rim (a := a) hz hi] with R hR
    rw [hd]
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := Real.exp (-R)) ?_).trans_eq
    · rw [sub_zero,abs_of_pos (by positivity : 0 < π/2)]
    · intro t ht
      rw [uIoc_of_le (by positivity : 0 ≤ π/2)] at ht
      simpa only [norm_mul,norm_neg,norm_I,one_mul] using hR t ⟨ht.1.le, ht.2⟩
  have horig : Tendsto (fun R : ℝ => F (R : ℂ)-F 0) atTop (𝓝 (ray a z)) := by
    have h := intervalIntegral_tendsto_integral_Ioi 0 (integrable_ray a z hz) (tendsto_id (α := ℝ))
    apply h.congr
    intro R
    simpa only [id_eq,zero_add,one_mul,W,ofReal_sinh] using (S 0 1 R).symm
  have hlow : Tendsto (fun R : ℝ => F (edge R (π/2))-F (edge 0 (π/2))) atTop
      (𝓝 (coeff a*halfLine a z)) := by
    have hI : Integrable (Kline a z) := integrable_macdonald a (-I*z) (by simpa)
    apply ((intervalIntegral_tendsto_integral_Ioi 0 hI.integrableOn
      (tendsto_id (α := ℝ))).const_mul
      (coeff a)).congr
    intro R
    have h := S (edge 0 (π/2)) 1 R
    have he (t : ℝ) : edge 0 (π/2)+1*(t : ℂ) = edge t (π/2) := by unfold edge; push_cast; ring
    simp_rw [he,one_mul,along,intervalIntegral.integral_const_mul] at h
    exact h.symm
  have hzero := hd 0
  have hu (s : ℝ) : W a z (edge 0 s) = angular a z s := by
    simp only [W,edge,ofReal_zero,zero_sub,sinh_neg,sinh_mul_I,angular,ofReal_sin]
    congr 1
    ring
  simp_rw [hu,intervalIntegral.integral_const_mul] at hzero
  have he := (hlow.sub horig).sub hshift
  have H : (coeff a*halfLine a z-ray a z)-0 = F 0-F (edge 0 (π/2)) :=
    tendsto_nhds_unique he (tendsto_const_nhds.congr fun R => by ring)
  change F (edge 0 (π/2))-F 0 = -I*halfArc a z at hzero
  linear_combination -H + hzero

private theorem arc_split (a z : ℂ) :
    arc a z = halfArc a z+exp (-(a*π)*I)*halfArc (-a) z := by
  have hc : Continuous (angular a z) := by unfold angular; fun_prop
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π/2) (angular a z) π
  rw [sub_zero,show π-π/2=π/2 by ring] at h
  have H (s : ℝ) : angular a z (π-s) = exp (-(a*π)*I)*angular (-a) z s := by
    rw [angular,angular,Real.sin_pi_sub,← exp_add,ofReal_sub]
    congr 1
    ring
  simp_rw [H,intervalIntegral.integral_const_mul] at h
  change (∫ t in 0..π, angular a z t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (π/2))
    (hc.intervalIntegrable (π/2) π),← h]
  rfl

private theorem Ksplit (a z : ℂ) (hi : 0 < z.im) :
    halfLine a z + halfLine (-a) z = 2*macdonald a (-I*z) := by
  have hI : Integrable (Kline a z) := integrable_macdonald a (-I*z) (by simpa)
  have H := integral_add_compl measurableSet_Ioi hI (s := Ioi (0 : ℝ))
  rw [compl_Ioi] at H
  have he (t : ℝ) : Kline a z (-t) = Kline (-a) z t := by simp [Kline]
  have h := integral_comp_neg_Ioi 0 (Kline a z)
  simp only [neg_zero,he] at h
  rw [← h] at H
  change _ = 2*((∫ t : ℝ, Kline a z t)/2)
  rw [← H]
  unfold halfLine
  ring

/-- Upper-half-plane continuation of the outgoing Hankel function, regular on the
positive imaginary axis. -/
def hankelFirstUpper (a z : ℂ) :=
  -2*I/π * exp (-(a*(π/2))*I) * macdonald a (-I*z)

/-- Agreement of the upper- and right-half-plane Schläfli contours on their overlap. -/
theorem hankelFirstUpper_eq (a z : ℂ) (hr : 0 < z.re) (hi : 0 < z.im) :
    hankelFirstUpper a z = hankelFirst a z := by
  have h : exp (-(a*π)*I)*coeff (-a) = coeff a := by
    unfold coeff
    rw [← exp_add]
    congr 1
    ring
  rw [hankelFirstUpper,hankelFirst,arc_split,ray_rotation a z hr hi,ray_rotation (-a) z hr hi]
  change -2*I/π*coeff a*macdonald a (-I*z) = _
  have hk := Ksplit a z hi
  field_simp [Real.pi_ne_zero]
  rw [neg_mul] at hk
  rw [show -(I*(π : ℂ)*a) = -(a*π)*I by ring]
  linear_combination I*coeff a*hk + I*halfLine (-a) z*h -
    (halfArc a z+exp (-(a*π)*I)*halfArc (-a) z)*I_sq

/-- Argument derivative of the continuation throughout the upper half-plane. -/
theorem deriv_hankelFirstUpper (a z : ℂ) (hi : 0 < z.im) :
    deriv (hankelFirstUpper a) z =
      -2/π * exp (-(a*(π/2))*I) * deriv (macdonald a) (-I*z) := by
  have hm := (hasDerivAt_macdonald a (-I*z) (by simpa)).differentiableAt.hasDerivAt
  have h := ((hm.comp z ((hasDerivAt_id' z).const_mul (-I))).const_mul
    (-2*I/π*exp (-(a*(π/2))*I))).deriv
  change deriv (fun w => -2*I/π*exp (-(a*(π/2))*I)*macdonald a (-I*w)) z = _
  rw [show deriv (fun w => -2*I/π*exp (-(a*(π/2))*I)*macdonald a (-I*w)) z = _ from h]
  linear_combination 2/π*exp (-(a*(π/2))*I)*deriv (macdonald a) (-I*z)*I_sq

/-- Values of the outgoing function and derivative at imaginary order and argument.
The real exponential is the same Coulomb factor that appears in the scattering integral. -/
theorem hankel_imaginary (η : ℝ) {k : ℝ} (hk : 0 < k) :
    let a := -(η : ℂ)*I
    let d := (Real.exp (-η*(π/2)) : ℂ)
    hankelFirstUpper a (I*k) = -2*I/π*d*macdonald a k ∧
      deriv (hankelFirstUpper a) (I*k) = -2/π*d*deriv (macdonald a) k := by
  have h : -(I : ℂ)*(I*k) = k := by linear_combination -(k : ℂ)*I_sq
  have ha : exp (-((-(η : ℂ)*I)*(π/2))*I) = (Real.exp (-η*(π/2)) : ℂ) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    linear_combination (η : ℂ)*π/2*I_sq
  dsimp only
  rw [hankelFirstUpper,deriv_hankelFirstUpper _ _ (by simpa),h,ha]
  exact ⟨rfl,rfl⟩

end ProjectAinos.SpecialFunctions.Bessel
