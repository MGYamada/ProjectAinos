/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.AiryVertical
public import ProjectAinos.SpecialFunctions.BesselContour
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # The Airy transition of the integer Bessel harmonics

For n = 2r³, displace Bessel's contour by −i/r before rescaling the angle. The resulting
Gaussian majorant is integrable for the coefficient and its argument derivative. The
complex sine remainder controls the cubic approximation for every bounded detuning u.
-/

@[expose] public section
noncomputable section

open Complex Filter MeasureTheory Set
open scoped Real Topology
namespace ProjectAinos.SpecialFunctions.Bessel
open Airy

private def rescaledSin (r : ℝ) (z : ℂ) := (r : ℂ)*sin (z/r)
private def cubicPart (r : ℝ) (z : ℂ) := 2*(r : ℂ)^3*(z/r-sin (z/r))
private def scaled (r u s : ℝ) :=
  exp (-(cubicPart r (s-I) + u*rescaledSin r (s-I))*I)
private def profile (u s : ℝ) := integrand u (1+s*I)

private theorem cubic_limit (z : ℂ) :
    Tendsto (fun r : ℝ => cubicPart r z) atTop (𝓝 (z^3/3)) := by
  let err (r : ℝ) := (r : ℂ)^3 * (sin (z/r) - (z/r-(z/r)^3/6))
  have he : Tendsto err atTop (𝓝 0) := by
    have hp : Tendsto (fun r : ℝ => r^2) atTop atTop := tendsto_pow_atTop two_ne_zero
    have hlim : Tendsto (fun r : ℝ => (‖z‖^5 / 100)/r^2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hp
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop ‖z‖] with r hr hz
    have h : ‖z/(r : ℂ)‖ = ‖z‖/r := by rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have H := Complex.sin_bound (x := z/r) (by rw [h]; exact (div_le_one hr).mpr hz)
    rw [h] at H
    change ‖(r : ℂ)^3 * _‖ ≤ _
    rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left H (pow_nonneg hr.le 3)).trans_eq (by field_simp)
  have h := (he.const_mul 2).const_sub (z^3/3)
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hr' := ofReal_ne_zero.mpr hr.ne'
  unfold cubicPart
  dsimp only [err]
  field_simp
  ring

private theorem sin_limit (z : ℂ) : Tendsto (fun r : ℝ => rescaledSin r z) atTop (𝓝 z) := by
  have hp : Tendsto (fun r : ℝ => r^2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hq : Tendsto (fun r : ℝ => 1/r^2) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hp
  have h := ((cubic_limit z).div_const 2).mul ((continuous_ofReal.tendsto _).comp hq)
  have H := h.const_sub z
  simp only [ofReal_zero, mul_zero, sub_zero] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hr' := ofReal_ne_zero.mpr hr.ne'
  unfold cubicPart rescaledSin
  dsimp only [Function.comp_apply]
  push_cast
  field_simp
  ring

private theorem phase_limit {l : Filter ℕ} {r u : ℕ → ℝ} {B : ℝ}
    (hr : Tendsto r l atTop) (hu : ∀ᶠ j in l, |u j| ≤ B) (s : ℝ) :
    Tendsto (fun j => scaled (r j) (u j) s - profile (u j) s) l (𝓝 0) := by
  let z : ℂ := s-I
  let w : ℂ := 1+s*I
  have hD := ((cubic_limit z).comp hr).sub_const (z^3/3)
  have hV := ((sin_limit z).comp hr).sub_const z
  simp only [sub_self, Function.comp_apply] at hD hV
  have hU : Tendsto (fun j => (u j : ℂ)*(rescaledSin (r j) z-z)) l (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun j => B*‖rescaledSin (r j) z-z‖) l (𝓝 0) by
      simpa only [norm_zero, mul_zero] using hV.norm.const_mul B)
    filter_upwards [hu] with j hj
    simpa only [norm_mul, norm_real, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hj (norm_nonneg (rescaledSin (r j) z-z))
  let δ (j : ℕ) := -((cubicPart (r j) z-z^3/3) + u j*(rescaledSin (r j) z-z))*I
  have hd : Tendsto δ l (𝓝 0) := by
    unfold δ
    simpa only [zero_add, neg_zero, zero_mul] using (hD.add hU).neg.mul_const I
  have hd' := ((continuous_exp.tendsto _).comp hd).sub_const 1
  simp only [exp_zero, sub_self, Function.comp_apply] at hd'
  have hzw : z = (-I)*w := by dsimp [z,w]; linear_combination (s : ℂ)*I_sq
  have hw : -(z^3/3)*I = w^3/3 := by
    calc -(z^3/3)*I = (-I)^4*w^3/3 := by rw [hzw]; ring
         _ = _ := by rw [show (4 : ℕ) = 2*2 by rfl, pow_mul]; simp
  have hz : -z*I = -w := by dsimp [z,w]; linear_combination I_sq
  have hid (j : ℕ) : scaled (r j) (u j) s - profile (u j) s =
      profile (u j) s * (exp (δ j)-1) := by
    rw [mul_sub, mul_one, scaled, profile, integrand, ← exp_add]
    congr 2
    dsimp only [δ]
    change -(cubicPart (r j) z + ↑(u j)*rescaledSin (r j) z)*I =
      w^3/3 - ↑(u j)*w + _
    linear_combination hw + (u j : ℂ)*hz
  simp_rw [hid]
  apply squeeze_zero_norm' _ (show Tendsto (fun j => Real.exp (1/3+B) * ‖exp (δ j)-1‖) l (𝓝 0) by
    simpa only [norm_zero, mul_zero] using hd'.norm.const_mul (Real.exp (1/3+B)))
  filter_upwards [hu] with j hj
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [profile, integrand, norm_exp, Real.exp_le_exp]
  simp [pow_succ, Complex.mul_re, Complex.mul_im, div_ofNat_re]
  nlinarith [neg_abs_le (u j), sq_nonneg s]

private theorem sinh_bound {h : ℝ} (hp : 0 ≤ h) (hh : h ≤ 1) :
    Real.sinh h ≤ h+h^3 := by
  have H := Complex.sin_bound (x := (h : ℂ)*I) (by simpa [norm_mul, abs_of_nonneg hp] using hh)
  have he : sin ((h : ℂ)*I) - ((h : ℂ)*I-((h : ℂ)*I)^3/6) =
      ((Real.sinh h - (h+h^3/6) : ℝ) : ℂ)*I := by
    rw [sin_mul_I, ← ofReal_sinh, mul_pow, pow_succ I 2, I_sq]
    push_cast
    ring
  rw [he] at H
  simp only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg hp] at H
  have h5 := pow_le_pow_of_le_one hp hh (show 3 ≤ 5 by norm_num)
  linarith [le_abs_self (Real.sinh h - (h+h^3/6)), pow_nonneg hp 3]

private theorem cosine_gap {t : ℝ} (ht : |t| ≤ π) :
    2*t^2/π^2 ≤ 1-Real.cos t := by
  have h := Real.mul_le_sin (x := |t|/2) (by positivity) (by linarith)
  have h' : |t|/π ≤ Real.sin (|t|/2) := by
    convert h using 1
    ring
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ |t|/π) h' 2
  have hc := Real.cos_two_mul_eq_one_sub (|t|/2)
  rw [mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ) ≠ 0), Real.cos_abs] at hc
  rw [div_pow, sq_abs] at hs
  rw [mul_div_assoc, hc]
  linarith

private theorem scaled_modulus {r : ℝ} (hr : 0 < r) (u s : ℝ) :
    ‖scaled r u s‖ = Real.exp (-2*r^2+(2*r^3-u*r)*Real.cos (s/r)*Real.sinh (1/r)) := by
  have ht : ((s : ℂ)-I)/r = ((s/r : ℝ) : ℂ) - ((1/r : ℝ) : ℂ)*I := by push_cast; ring
  rw [scaled, norm_exp]
  congr 1
  have ha : -(cubicPart r (s-I) + u*rescaledSin r (s-I))*I =
      -(2*(r : ℂ)^2*((s : ℂ)-I) - ((2*r^3-u*r : ℝ) : ℂ)*sin (((s : ℂ)-I)/r))*I := by
    unfold cubicPart rescaledSin
    push_cast
    field_simp [ofReal_ne_zero.mpr hr.ne']
    ring
  rw [ha, ht, sin_sub, cos_mul_I, sin_mul_I, ← ofReal_sin, ← ofReal_cos, ← ofReal_cosh,
    ← ofReal_sinh, mul_I_re, neg_im]
  simp only [sub_im, mul_im, mul_re, ofReal_re, ofReal_im, I_im,
    sub_re, I_re, zero_sub, mul_zero, zero_mul, mul_one, add_zero, ← ofReal_pow,
    re_ofNat, im_ofNat]
  ring

private theorem gaussian {r u s B : ℝ} (hr : 1 ≤ r) (hB : B ≤ r^2)
    (hu : |u| ≤ B) (hs : |s| ≤ π*r) :
    ‖scaled r u s‖ ≤ Real.exp (2+2*B)*Real.exp (-(2/π^2)*s^2) := by
  have hr' : 0 < r := by linarith
  have hinv : 1/r ≤ 1 := (div_le_one hr').mpr hr
  let d := Real.sinh (1/r)
  have hd₀ : 1/r ≤ d := Real.self_le_sinh_iff.mpr (by positivity)
  have hd₁ : d ≤ 1/r+(1/r)^3 := sinh_bound (by positivity) hinv
  have hd : 0 ≤ d := (by positivity : 0 ≤ 1/r).trans hd₀
  have hr3 : 0 < r^3 := by positivity
  have hrd : r*d ≤ 2 := by
    have h := mul_le_mul_of_nonneg_left hd₁ hr'.le
    have h' : r*(1/r+(1/r)^3) = 1+(1/r)^2 := by field_simp
    rw [h'] at h
    nlinarith [pow_le_pow_left₀ (by positivity : 0 ≤ 1/r) hinv 2]
  have hbase : 2*r^3*d - 2*r^2 ≤ 2 := by
    have h := mul_le_mul_of_nonneg_left hd₁ (show 0 ≤ 2*r^3 by positivity)
    field_simp at h
    nlinarith
  have hB₀ := (abs_nonneg u).trans hu
  have hu' := mul_le_mul ((neg_le_abs u).trans hu) hrd (mul_nonneg hr'.le hd) hB₀
  have ha : r^3 ≤ 2*r^3-u*r := by
    nlinarith [mul_nonneg hr'.le (show 0 ≤ r^2-u by linarith [le_abs_self u])]
  have hprod : r^2 ≤ (2*r^3-u*r)*d := by
    have H := mul_le_mul ha hd₀ (by positivity) (hr3.le.trans ha)
    rwa [show r^3*(1/r) = r^2 by field_simp] at H
  have hc := cosine_gap (t := s/r) (by rw [abs_div, abs_of_pos hr']; exact (div_le_iff₀ hr').mpr hs)
  have H := mul_le_mul hprod hc (by positivity) (hr'.le.trans (by nlinarith [hprod]))
  have he : r^2*(2*(s/r)^2/π^2) = (2/π^2)*s^2 := by field_simp
  rw [he] at H
  rw [scaled_modulus hr', ← Real.exp_add, Real.exp_le_exp]
  change -2*r^2+(2*r^3-u*r)*Real.cos (s/r)*d ≤ _
  linarith only [H, hbase, hu']

private def size (s : ℝ) := 3 + Real.cosh 1 * |s|
private def weight (k : Bool) (r s : ℝ) : ℂ := if k then I*rescaledSin r (s-I) else 1
private def weightLimit (k : Bool) (s : ℝ) : ℂ := if k then 1+s*I else 1

private theorem sine_size {r : ℝ} (hr : 1 ≤ r) (s : ℝ) :
    ‖rescaledSin r (s-I)‖ ≤ 2+Real.cosh 1 * |s| := by
  have hp : 0 < r := by linarith
  have hinv : 1/r ≤ 1 := (div_le_one hp).mpr hr
  have hinv' : 0 ≤ 1/r := by positivity
  have hs := sinh_bound hinv' hinv
  have hrd : r*Real.sinh (1/r) ≤ 2 := by
    apply (mul_le_mul_of_nonneg_left hs hp.le).trans
    rw [show r*(1/r+(1/r)^3) = 1+(1/r)^2 by field_simp]
    nlinarith [pow_le_pow_left₀ hinv' hinv 2]
  have ht : ((s : ℂ)-I)/r = ((s/r : ℝ) : ℂ) - ((1/r : ℝ) : ℂ)*I := by push_cast; ring
  rw [rescaledSin, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hp, ht, sin_sub,
    cos_mul_I, sin_mul_I, ← ofReal_sin, ← ofReal_cos, ← ofReal_sinh, ← ofReal_cosh]
  apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hp.le).trans
  simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one,
    abs_of_pos (Real.cosh_pos _), abs_of_nonneg (Real.sinh_nonneg_iff.mpr hinv')]
  have hd : Real.cosh (1/r) ≤ Real.cosh 1 :=
    Real.cosh_le_cosh.mpr (by rwa [abs_of_nonneg hinv', abs_one])
  have h := mul_le_mul (Real.abs_sin_le_abs (x := s/r)) hd
    (Real.cosh_pos _).le (abs_nonneg _)
  rw [abs_div, abs_of_pos hp] at h
  have hc := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one (s/r)) (Real.sinh_nonneg_iff.mpr hinv')
  have he : r*(|s|/r*Real.cosh 1) = Real.cosh 1*|s| := by field_simp
  linarith [mul_le_mul_of_nonneg_left h hp.le, mul_le_mul_of_nonneg_left hc hp.le]

private theorem weight_bound (k : Bool) {r : ℝ} (hr : 1 ≤ r) (s : ℝ) :
    ‖weight k r s‖ ≤ size s := by
  cases k <;> simp only [weight, ↓reduceIte, Bool.false_eq_true, norm_one, norm_mul, norm_I,
    one_mul, size]
  · linarith [mul_nonneg (Real.cosh_pos 1).le (abs_nonneg s)]
  · linarith [sine_size hr s]

private theorem limit_weight_bound (k : Bool) (s : ℝ) : ‖weightLimit k s‖ ≤ size s := by
  have h := mul_le_mul_of_nonneg_right (Real.one_le_cosh 1) (abs_nonneg s)
  cases k <;> simp only [weightLimit, ↓reduceIte, Bool.false_eq_true, norm_one, size]
  · linarith [mul_nonneg (Real.cosh_pos 1).le (abs_nonneg s)]
  · have H := norm_add_le (1 : ℂ) ((s : ℂ)*I)
    simp only [norm_one, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs] at H
    linarith

private theorem profile_norm (u s : ℝ) :
    ‖profile u s‖ = Real.exp (1/3-u)*Real.exp (-s^2) := by
  rw [profile, integrand, norm_exp, ← Real.exp_add]
  congr 1
  simp [pow_succ, Complex.mul_re, Complex.mul_im, div_ofNat_re]
  ring

private def major (C a s : ℝ) := size s * (Real.exp C * Real.exp (-a*s^2))

private theorem integrable_major (C : ℝ) {a : ℝ} (ha : 0 < a) : Integrable (major C a) := by
  have h₁ := (integrable_exp_neg_mul_sq ha).const_mul 3
  have h₂ := (integrable_mul_exp_neg_mul_sq ha).norm.const_mul (Real.cosh 1)
  apply ((h₁.add h₂).const_mul (Real.exp C)).congr
  filter_upwards with s
  simp [major, size, norm_mul, Real.norm_eq_abs]
  ring

private theorem model_bound (k : Bool) {u B : ℝ} (hu : |u| ≤ B) (s : ℝ) :
    ‖weightLimit k s * profile u s‖ ≤ major (1/3+B) 1 s := by
  rw [norm_mul, profile_norm, major, neg_mul, one_mul]
  gcongr
  · unfold size; positivity
  · exact limit_weight_bound k s
  · linarith [neg_abs_le u]

private def truncated (k : Bool) (r u : ℝ) :=
  (Ioc (-π*r) (π*r)).indicator (fun s => weight k r s * scaled r u s)

private theorem truncated_bound (k : Bool) {r u B : ℝ} (hr : 1 ≤ r) (hB : B ≤ r^2)
    (hu : |u| ≤ B) (s : ℝ) :
    ‖truncated k r u s‖ ≤ major (2+2*B) (2/π^2) s := by
  by_cases h : s ∈ Ioc (-π*r) (π*r)
  · rw [truncated, indicator_of_mem h, norm_mul, major]
    exact mul_le_mul (weight_bound k hr s) (gaussian hr hB hu (abs_le.mpr
      ⟨by linarith [h.1],h.2⟩)) (norm_nonneg _) (by unfold size; positivity)
  · rw [truncated, indicator_of_notMem h, norm_zero]
    unfold major size
    positivity

private theorem pointwise {r u : ℕ → ℝ} {B : ℝ} (hr : Tendsto r atTop atTop)
    (hu : ∀ᶠ j in atTop, |u j| ≤ B) (k : Bool) (s : ℝ) :
    Tendsto (fun j => truncated k (r j) (u j) s - weightLimit k s * profile (u j) s)
      atTop (𝓝 0) := by
  have hx := phase_limit hr hu s
  have hw : Tendsto (fun j => weight k (r j) s) atTop (𝓝 (weightLimit k s)) := by
    cases k
    · exact tendsto_const_nhds
    · have H := ((sin_limit ((s : ℂ)-I)).comp hr).const_mul I
      have he : I*((s : ℂ)-I) = 1+s*I := by linear_combination -I_sq
      change Tendsto (fun j => I*rescaledSin (r j) (s-I)) _ (𝓝 (1+s*I))
      simpa only [he, Function.comp_apply] using H
  have hw' := hw.sub_const (weightLimit k s)
  rw [sub_self] at hw'
  have hP : ∀ᶠ j in atTop, ‖profile (u j) s‖ ≤ Real.exp (1/3+B) := by
    filter_upwards [hu] with j hj
    rw [profile_norm, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [neg_abs_le (u j), sq_nonneg s]
  have H₂ : Tendsto (fun j => (weight k (r j) s-weightLimit k s)*profile (u j) s) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto
      (fun j => ‖weight k (r j) s-weightLimit k s‖ * Real.exp (1/3+B)) atTop (𝓝 0) by
        simpa using hw'.norm.mul_const (Real.exp (1/3+B)))
    filter_upwards [hP] with j hj
    rw [norm_mul]
    gcongr
  have H := (hw.mul hx).add H₂
  rw [mul_zero, zero_add] at H
  apply H.congr'
  filter_upwards [(hr.const_mul_atTop Real.pi_pos).eventually_gt_atTop |s|] with j hj
  have h : s ∈ Ioc (-π*r j) (π*r j) := ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
  rw [truncated, indicator_of_mem h]
  ring

private theorem cont_scaled (r u : ℝ) : Continuous (scaled r u) := by
  unfold scaled cubicPart rescaledSin
  fun_prop

private theorem cont_model (k : Bool) (u : ℝ) :
    Continuous (fun s => weightLimit k s*profile u s) := by
  cases k <;> simp only [weightLimit, Bool.false_eq_true, ↓reduceIte, profile, integrand] <;>
    fun_prop

private theorem cont_weight (k : Bool) (r : ℝ) : Continuous (weight k r) := by
  cases k <;> unfold weight rescaledSin <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

private theorem integrable_trunc (k : Bool) (r u : ℝ) : Integrable (truncated k r u) :=
  (integrable_indicator_iff measurableSet_Ioc).mpr
    (((cont_weight k r).mul (cont_scaled r u)).continuousOn.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self)

private theorem integrable_model (k : Bool) (u : ℝ) :
    Integrable (fun s => weightLimit k s * profile u s) :=
  (integrable_major (1/3+|u|) zero_lt_one).mono' (cont_model k u).aestronglyMeasurable
    (ae_of_all _ (model_bound k (le_refl |u|)))

private theorem integral_limit {r u : ℕ → ℝ} {B : ℝ} (hr : Tendsto r atTop atTop)
    (hu : ∀ᶠ j in atTop, |u j| ≤ B) (k : Bool) :
    Tendsto (fun j => (∫ s, truncated k (r j) (u j) s) -
      ∫ s, weightLimit k s * profile (u j) s) atTop (𝓝 0) := by
  let M := major (2+2*B) (2/π^2) + major (1/3+B) 1
  have hm : Integrable M := (integrable_major _ (by positivity)).add
    (integrable_major _ zero_lt_one)
  have hp := (tendsto_pow_atTop (n := 2) two_ne_zero).comp hr
  simp_rw [← integral_sub (integrable_trunc k _ _) (integrable_model k _)]
  rw [← integral_zero (α := ℝ) (G := ℂ) (μ := volume)]
  refine tendsto_integral_filter_of_dominated_convergence M ?_ ?_ hm ?_
  · exact Eventually.of_forall fun j => (integrable_trunc k _ _).aestronglyMeasurable.sub
      (cont_model k _).aestronglyMeasurable
  · filter_upwards [hr.eventually_ge_atTop 1, hp.eventually_ge_atTop B, hu] with j hj hB hU
    exact ae_of_all _ fun s => (norm_sub_le _ _).trans (add_le_add
      (truncated_bound k hj hB hU s) (model_bound k hU s))
  · exact ae_of_all _ (pointwise hr hu k)

private theorem rescaled_kernel {r : ℝ} {n : ℕ} (hn : (n : ℝ) = 2*r^3) (u s : ℝ) :
    scaled r u s = fourierKernel n (n-u*r) (s/r - (1/r : ℝ)*I) := by
  have hn' := congrArg ofReal hn
  unfold scaled fourierKernel cubicPart rescaledSin
  congr 2
  push_cast at hn' ⊢
  rw [hn']
  have he : ((s : ℂ)-I)/r = s/r - (1/r : ℂ)*I := by ring
  rw [he]
  ring

private theorem trunc_integral {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : (n : ℝ) = 2*r^3) (u : ℝ) :
    (∫ s, truncated false r u s) = 2*π*r*besselJ n (n-u*r : ℝ) ∧
    (∫ s, truncated true r u s) = 2*π*(r : ℂ)^2*deriv (besselJ n) (n-u*r : ℝ) := by
  have hab : -π*r ≤ π*r := by nlinarith [Real.pi_pos]
  have h (f : ℝ → ℂ) := intervalIntegral.integral_comp_div (a := -π*r) (b := π*r) f hr.ne'
  simp only [mul_div_cancel_right₀ _ hr.ne', Complex.real_smul] at h
  simp only [truncated, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hab,
    weight, Bool.false_eq_true, ↓reduceIte, one_mul, rescaled_kernel hn]
  constructor
  · have H := h (fun t : ℝ => fourierKernel n (n-u*r) (t-(1/r : ℝ)*I))
    rw [integral_shift] at H
    simp only [ofReal_div] at H ⊢
    rw [H]
    push_cast
    ring
  · have H := h (fun t : ℝ => I*sin (t-(1/r : ℝ)*I)*fourierKernel n (n-u*r) (t-(1/r : ℝ)*I))
    rw [integral_shift_deriv] at H
    have ht (s : ℝ) : I*rescaledSin r (s-I)*fourierKernel n (n-u*r) (s/r-(1/r : ℝ)*I) =
        (r : ℂ)*(I*sin (s/r-(1/r : ℝ)*I)*fourierKernel n (n-u*r) (s/r-(1/r : ℝ)*I)) := by
      unfold rescaledSin
      rw [show ((s : ℂ)-I)/r = (s/r-(1/r : ℝ)*I) by push_cast; ring]
      ring
    simp only [ofReal_div] at ht H ⊢
    simp_rw [ht, intervalIntegral.integral_const_mul, H]
    push_cast
    ring

/-- Cubic scale for an integer harmonic n. -/
def turningScale (n : ℕ) : ℝ := ((n : ℝ)/2)^(1/3 : ℝ)

/-- The angular scale diverges with harmonic order. -/
theorem tendsto_turningScale : Tendsto turningScale atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : 0 < (1/3 : ℝ))).comp
    (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : 0 < (2 : ℝ)))

/-- The real scale parametrizes the integer order exactly. -/
theorem turningScale_cube (n : ℕ) : (n : ℝ) = 2 * turningScale n ^ 3 := by
  simp only [turningScale, ← Real.rpow_mul_natCast (by positivity : 0 ≤ (n : ℝ)/2)]
  norm_num
  ring

/-- Both Bessel harmonics in the turning region. For r = (n/2)⅓ and any bounded moving
detuning u, r Jₙ(n−ur) tends to Ai(u) in absolute difference, and r² J′ₙ(n−ur) to −Ai′(u).
In particular the estimates apply across the turning point u = 0. -/
theorem turning_point_along {d : ℕ → ℕ} (hd : Tendsto d atTop atTop)
    {u : ℕ → ℝ} {B : ℝ} (hu : ∀ᶠ n in atTop, |u n| ≤ B) :
    Tendsto (fun n : ℕ => (turningScale (d n) : ℂ) *
      besselJ (d n) (d n-u n*turningScale (d n) : ℝ) - ai (u n)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (turningScale (d n) : ℂ)^2 *
      deriv (besselJ (d n)) (d n-u n*turningScale (d n) : ℝ) + deriv ai (u n)) atTop (𝓝 0) := by
  have hr : Tendsto (fun n => turningScale (d n)) atTop atTop := tendsto_turningScale.comp hd
  have hp := hr.eventually (eventually_gt_atTop (0 : ℝ))
  have hc : (2*(π : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have H (k : Bool) := (integral_limit hr hu k).div_const (2*π : ℂ)
  simp only [zero_div] at H
  constructor
  · apply (H false).congr'
    filter_upwards [hp] with n hn
    rw [(trunc_integral hn (turningScale_cube (d n)) _).1]
    simp only [weightLimit, Bool.false_eq_true, ↓reduceIte, one_mul, profile, integral_vertical]
    field_simp
  · apply (H true).congr'
    filter_upwards [hp] with n hn
    rw [(trunc_integral hn (turningScale_cube (d n)) _).2]
    simp only [weightLimit, ↓reduceIte, profile]
    have hi := integral_vertical_deriv (u n)
    simp only [neg_mul, integral_neg] at hi
    rw [neg_eq_iff_eq_neg.mp hi]
    field_simp
    ring

/-- Consecutive harmonics at bounded, moving detuning. -/
theorem turning_point {u : ℕ → ℝ} {B : ℝ} (hu : ∀ᶠ n in atTop, |u n| ≤ B) :
    Tendsto (fun n : ℕ => (turningScale n : ℂ) *
      besselJ n (n-u n*turningScale n : ℝ) - ai (u n)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (turningScale n : ℂ)^2 * deriv (besselJ n) (n-u n*turningScale n : ℝ) +
      deriv ai (u n)) atTop (𝓝 0) :=
  turning_point_along (d := id) tendsto_id hu


private theorem gaussian_tail {r u s : ℝ} (hr : 1 ≤ r) (hu : 0 ≤ u) (hu' : u ≤ 2*r^2)
    (hs : |s| ≤ π*r) :
    ‖scaled r u s‖ ≤ Real.exp (-u/2) * (Real.exp 2 * Real.exp (-(1/(2*π^2))*s^2)) := by
  have hp : 0 < r := by linarith
  have h := gaussian (B := 0) (u := 0) hr (sq_nonneg r) (by simp) hs
  rw [scaled_modulus hp, ← Real.exp_add, Real.exp_le_exp] at h
  simp only [zero_mul, sub_zero, mul_zero, add_zero] at h
  have ha : (1/(2*π^2))*s^2 ≤ r^2/2 := by
    have H := pow_le_pow_left₀ (abs_nonneg s) hs 2
    rw [sq_abs, mul_pow] at H
    have hπ : 0 < π^2 := by positivity
    field_simp
    linarith
  let a := 1/(2*π^2)
  let C := Real.cos (s/r)*Real.sinh (1/r)
  have h₀ : -2*r^2+2*r^3*C ≤ 2-a*s^2 := by
    have ha' : 0 ≤ a*s^2 := by dsimp [a]; positivity
    have he : 2/π^2 = 4*a := by dsimp [a]; ring
    rw [he] at h
    dsimp only [C]
    linarith only [h, ha']
  have h₁ : -2*r^2 ≤ 2-(2*r^2)/2-a*s^2 := by linarith [sq_nonneg r]
  rw [scaled_modulus hp, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  change -2*r^2+(2*r^3-u*r)*Real.cos (s/r)*Real.sinh (1/r) ≤ -u/2+(2+ -a*s^2)
  apply le_of_mul_le_mul_left (a := 2*r^2) _ (by positivity)
  dsimp only [C] at h₀
  nlinarith only [mul_nonneg (sub_nonneg.mpr hu') (sub_nonneg.mpr h₀),
    mul_nonneg hu (sub_nonneg.mpr h₁)]

/-- A single exponential majorant below the turning point, from zero physical argument
up to the full harmonic order. It controls integration over the whole subcritical range. -/
theorem turning_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ turningScale n →
    ∀ u : ℝ, 0 ≤ u → u ≤ 2*turningScale n^2 →
      ‖(turningScale n : ℂ)*besselJ n (n-u*turningScale n : ℝ)‖ ≤ C*Real.exp (-u/2) := by
  let a := 1/(2*π^2)
  let g (s : ℝ) := Real.exp 2 * Real.exp (-a*s^2)
  have hg : Integrable g :=
    (integrable_exp_neg_mul_sq (show 0 < a by dsimp [a]; positivity)).const_mul _
  have hG : 0 ≤ ∫ s : ℝ, g s := integral_nonneg fun _ => by dsimp [g]; positivity
  refine ⟨(∫ s : ℝ, g s)/(2*π), by positivity, fun n hn u hu hu' => ?_⟩
  let r := turningScale n
  have hr : 0 < r := by dsimp [r]; linarith
  have h (s : ℝ) : ‖truncated false r u s‖ ≤ Real.exp (-u/2)*g s := by
    by_cases hs : s ∈ Ioc (-π*r) (π*r)
    · rw [truncated, indicator_of_mem hs]
      simp only [weight, Bool.false_eq_true, ↓reduceIte, one_mul]
      exact gaussian_tail hn hu hu' (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩)
    · rw [truncated, indicator_of_notMem hs, norm_zero]
      dsimp [g]
      positivity
  have H := norm_integral_le_of_norm_le (hg.const_mul (Real.exp (-u/2))) (ae_of_all _ h)
  rw [(trunc_integral hr (turningScale_cube n) u).1, integral_const_mul,
    mul_assoc (2*(π : ℂ)), norm_mul, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] at H
  calc
    _ ≤ (Real.exp (-u/2)*(∫ s : ℝ, g s))/(2*π) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith only [H])
    _ = _ := by ring

/-- The Airy profile decays exponentially on the positive real axis. -/
theorem airy_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖ai u‖ ≤ C*Real.exp (-u) := by
  let g (s : ℝ) := Real.exp (1/3) * Real.exp (-s^2)
  have hg : Integrable g := by
    simpa only [neg_one_mul] using
      (integrable_exp_neg_mul_sq zero_lt_one).const_mul (Real.exp (1/3))
  have hG : 0 ≤ ∫ s : ℝ, g s := integral_nonneg fun _ => by dsimp [g]; positivity
  refine ⟨(∫ s : ℝ, g s)/(2*π), by positivity, fun u => ?_⟩
  have h (s : ℝ) : ‖profile u s‖ ≤ Real.exp (-u)*g s := by
    rw [profile_norm, sub_eq_neg_add, Real.exp_add, mul_assoc]
  have H := norm_integral_le_of_norm_le (hg.const_mul (Real.exp (-u))) (ae_of_all _ h)
  change ‖∫ s : ℝ, integrand u (1+s*I)‖ ≤ _ at H
  rw [integral_vertical, norm_mul, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, integral_const_mul] at H
  calc
    _ ≤ (Real.exp (-u)*(∫ s : ℝ, g s))/(2*π) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith only [H])
    _ = _ := by ring

end ProjectAinos.SpecialFunctions.Bessel
