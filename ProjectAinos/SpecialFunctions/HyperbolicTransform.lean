/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Macdonald
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # Hyperbolic Fourier integrals of imaginary order

For |η| < k the real phase k sinh t + η t has positive derivative. Its weighted
Fourier integrals deform to the horizontal line Im t = −π/2. A primitive of the
entire numerator accounts for endpoints before passing to the infinite contour.
-/

@[expose] public section
noncomputable section
open Complex MeasureTheory Set Filter
open scoped Real Topology
namespace ProjectAinos.SpecialFunctions.Bessel

/-- The two integrable Jacobian weights of the hyperbolic phase. True selects the
sinh velocity numerator, false the cosh numerator. -/
def scatteringKernel (p : Bool) (k η t : ℝ) : ℂ :=
  exp (-((k*Real.sinh t+η*t : ℝ) : ℂ)*I) *
    (((if p then k+η*Real.cosh t else η*Real.sinh t)/(k*Real.cosh t+η)^2 : ℝ) : ℂ)

private def phase (k η : ℝ) (z : ℂ) := exp (-(k*sinh z+η*z)*I)
private def denom (k η : ℝ) (z : ℂ) := k*cosh z+η
private def num (p : Bool) (z : ℂ) := if p then sinh z else cosh z
private def vel (p : Bool) (k η : ℝ) (z : ℂ) := num p z / denom k η z
private def accel (p : Bool) (k η : ℝ) (z : ℂ) :=
  (if p then k+η*cosh z else η*sinh z)/denom k η z^2
private def entire (p : Bool) (k η : ℝ) (z : ℂ) := I*num p z*phase k η z

private theorem kernel_real (p : Bool) (k η t : ℝ) :
    scatteringKernel p k η t = phase k η t*accel p k η t := by
  cases p <;> simp [scatteringKernel,phase,accel,denom]

private theorem deriv_phase (k η : ℝ) (z : ℂ) :
    HasDerivAt (phase k η) (phase k η z*(-denom k η z*I)) z := by
  have h := ((((hasDerivAt_sinh z).const_mul (k : ℂ)).add
    ((hasDerivAt_id' z).const_mul (η : ℂ))).neg.mul_const I).cexp
  convert h using 1
  · rfl
  dsimp only [phase,denom]
  rw [mul_one]
  rfl

private theorem deriv_vel (p : Bool) (k η : ℝ) {z : ℂ} (hz : denom k η z ≠ 0) :
    HasDerivAt (vel p k η) (accel p k η z) z := by
  have hd := ((hasDerivAt_cosh z).const_mul (k : ℂ)).add_const (η : ℂ)
  have h := cosh_sq_sub_sinh_sq z
  cases p
  · apply ((hasDerivAt_cosh z).div hd hz).congr_deriv
    change (_-_) / _ = (η*sinh z)/_
    unfold denom
    ring
  · apply ((hasDerivAt_sinh z).div hd hz).congr_deriv
    change (_-_) / _ = (k+η*cosh z)/_
    unfold denom
    congr 1
    linear_combination (k : ℂ)*h

private theorem primitive (p : Bool) (k η : ℝ) :
    ∃ F : ℂ → ℂ, ∀ z, HasDerivAt F (entire p k η z) z := by
  have h : Differentiable ℂ (entire p k η) := by
    cases p <;> unfold entire num phase <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  obtain ⟨F,hF⟩ := h.isExactOn_univ
  exact ⟨F,fun z => hF z (mem_univ z)⟩

private def corrected (F : ℂ → ℂ) (p : Bool) (k η : ℝ) (z : ℂ) :=
  F z + vel p k η z*phase k η z

private theorem deriv_corrected {p : Bool} {k η : ℝ} {F : ℂ → ℂ}
    (hF : ∀ z, HasDerivAt F (entire p k η z) z) {z : ℂ} (hz : denom k η z ≠ 0) :
    HasDerivAt (corrected F p k η) (phase k η z * accel p k η z) z := by
  apply ((hF z).add ((deriv_vel p k η hz).mul (deriv_phase k η z))).congr_deriv
  dsimp only [entire,vel]
  field_simp [hz]
  ring

private theorem hyp_bounds (z : ℂ) :
    ‖cosh z‖ ≤ Real.exp |z.re| ∧ ‖sinh z‖ ≤ Real.exp |z.re| ∧
      Real.exp |z.re|-1 ≤ 2*‖cosh z‖ := by
  have hb₁ : ‖exp z‖ ≤ Real.exp |z.re|  := by
    rw [norm_exp]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  have hb₂ : ‖exp (-z)‖ ≤ Real.exp |z.re| := by
    rw [norm_exp,neg_re]; exact Real.exp_le_exp.mpr (neg_le_abs _)
  have h : 2*‖cosh z‖ = ‖exp z+exp (-z)‖ := by rw [← two_cosh, norm_mul, norm_ofNat]
  have h' : 2*‖sinh z‖ = ‖exp z-exp (-z)‖ := by rw [← two_sinh, norm_mul, norm_ofNat]
  refine ⟨by linarith [norm_add_le (exp z) (exp (-z))],
    by linarith [norm_sub_le (exp z) (exp (-z))], ?_⟩
  rw [h]
  rcases le_total 0 z.re with hz|hz
  · rw [abs_of_nonneg hz, ← norm_exp]
    have ha : ‖exp (-z)‖ ≤ 1 := by simp [norm_exp,hz]
    have H' := norm_sub_norm_le (exp z) (exp z+exp (-z))
    simpa only [sub_add_cancel_left, norm_neg] using
      (show ‖exp z‖-1 ≤ ‖exp z+exp (-z)‖ by
        simp only [sub_add_cancel_left, norm_neg] at H'
        linarith)
  · rw [abs_of_nonpos hz, ← neg_re, ← norm_exp]
    have ha : ‖exp z‖ ≤ 1 := by simp [norm_exp,hz]
    have H := norm_sub_norm_le (exp (-z)) (exp z+exp (-z))
    rw [show exp (-z)-(exp z+exp (-z)) = -exp z by ring, norm_neg] at H
    linarith

private theorem large {k η : ℝ} (hk : 0 < k) {z : ℂ}
    (hz : 4+8*|η|/k ≤ Real.exp |z.re|) :
    denom k η z ≠ 0 ∧ ‖vel true k η z‖ ≤ 8/k ∧ ‖vel false k η z‖ ≤ 8/k ∧
      ∀ p, ‖accel p k η z‖ ≤ (64*(k+|η|)/k^2)*Real.exp (-|z.re|) := by
  let E := Real.exp |z.re|
  have hE : 0 < E := Real.exp_pos _
  have he : 1 ≤ E := Real.one_le_exp (abs_nonneg _)
  have hh := hyp_bounds z
  have hprod : k*E/8 ≤ ‖denom k η z‖ := by
    have h := norm_sub_norm_le ((k : ℂ)*cosh z) (denom k η z)
    simp only [denom, sub_add_cancel_left, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos hk] at h
    have h' : 4*k+8*|η| ≤ E*k := by
      have H := mul_le_mul_of_nonneg_right hz hk.le
      dsimp only [E]
      field_simp at H
      linarith
    dsimp only [E,denom] at h' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hh.2.2 hk.le]
  have hd : 0 < ‖denom k η z‖ := lt_of_lt_of_le (by positivity) hprod
  have hn (p : Bool) : ‖num p z‖ ≤ E := by
    cases p
    · exact hh.1
    · exact hh.2.1
  have hv (p : Bool) : ‖vel p k η z‖ ≤ 8/k := by
    rw [vel, norm_div, div_le_div_iff₀ hd hk]
    nlinarith [mul_le_mul_of_nonneg_right (hn p) hk.le]
  refine ⟨norm_pos_iff.mp hd,hv true,hv false,fun p => ?_⟩
  have hN : ‖(if p then (k : ℂ)+η*cosh z else η*sinh z)‖ ≤ (k+|η|)*E := by
    cases p
    · simp only [Bool.false_eq_true,↓reduceIte,norm_mul,norm_real,Real.norm_eq_abs]
      nlinarith [mul_le_mul_of_nonneg_left hh.2.1 (abs_nonneg η),mul_nonneg hk.le hE.le]
    · simp only [↓reduceIte]
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_real,Real.norm_eq_abs,norm_real,Real.norm_eq_abs,abs_of_pos hk]
      nlinarith [mul_le_mul_of_nonneg_left hh.1 (abs_nonneg η),mul_le_mul_of_nonneg_left he hk.le]
  rw [accel,norm_div,norm_pow,Real.exp_neg]
  change _ / _ ≤ (64*(k+|η|)/k^2)*E⁻¹
  rw [div_le_iff₀ (sq_pos_of_pos hd)]
  apply hN.trans
  field_simp
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ k*E/8) hprod 2
  nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ k+|η| by positivity)]

private def edge (x s : ℝ) : ℂ := x-s*I

private theorem edge_re (x s : ℝ) : (edge x s).re = x := by simp [edge]

private theorem phase_edge (k η x s : ℝ) :
    ‖phase k η (edge x s)‖ = Real.exp (-(k*Real.cosh x*Real.sin s+η*s)) := by
  rw [phase,edge,sinh_sub,cosh_mul_I,sinh_mul_I,← ofReal_cos,← ofReal_sin,
    ← ofReal_sinh,← ofReal_cosh,norm_exp]
  congr 1
  simp [mul_im,mul_re]
  rw [← ofReal_sin,ofReal_re]
  ring

private def topLine (x : ℝ) := edge x (π/2)
private def decay (η : ℝ) := Real.exp (-η*(π/2))

private theorem phase_top (k η x : ℝ) :
    phase k η (topLine x) =
      (decay η : ℂ)*exp (-(k : ℂ)*Real.cosh x + (-(η : ℂ)*I)*x) := by
  rw [phase,topLine,edge,sinh_sub,cosh_mul_I,sinh_mul_I,← ofReal_sin,← ofReal_cos,
    Real.sin_pi_div_two,Real.cos_pi_div_two,ofReal_zero,mul_zero,ofReal_one,one_mul,zero_sub,
    ← ofReal_cosh,decay,ofReal_exp,← exp_add]
  congr 1
  push_cast
  linear_combination (η : ℂ)*(π : ℂ)/2*I_sq + (k : ℂ)*cosh (x : ℂ)*I_sq

private def kernelK (a : ℂ) (k t : ℝ) := exp (-(k : ℂ)*Real.cosh t+a*t)

private theorem top_entire (p : Bool) (k η x : ℝ) :
    let a := -(η : ℂ)*I
    entire p k η (topLine x) = (decay η : ℂ)/2 *
      (kernelK (a+1) k x + (if p then (1 : ℂ) else -1)*kernelK (a-1) k x) := by
  let a := -(η : ℂ)*I
  have add (b : ℂ) : kernelK (a+b) k x = exp (b*x)*kernelK a k x := by
    unfold kernelK
    rw [← exp_add]
    congr 1
    ring
  have sub : kernelK (a-1) k x = exp (-(x : ℂ))*kernelK a k x := by
    simpa only [sub_eq_add_neg, neg_one_mul] using add (-1)
  dsimp only
  change _ = _*(kernelK (a+1) k x + _*kernelK (a-1) k x)
  rw [add,sub,one_mul,entire,phase_top]
  change I * num p (topLine x) * (_*kernelK a k x) = _
  have hs : sinh (topLine x) = -cosh (x : ℂ)*I := by
    rw [topLine,edge,sinh_sub,cosh_mul_I,sinh_mul_I,← ofReal_cos,← ofReal_sin,
      Real.cos_pi_div_two,Real.sin_pi_div_two]
    simp
  have hc : cosh (topLine x) = -sinh (x : ℂ)*I := by
    rw [topLine,edge,cosh_sub,cosh_mul_I,sinh_mul_I,← ofReal_cos,← ofReal_sin,
      Real.cos_pi_div_two,Real.sin_pi_div_two]
    simp
  cases p <;> simp only [num, Bool.false_eq_true, ↓reduceIte,hc,hs] <;> simp only [cosh,sinh]
  · linear_combination -(decay η : ℂ)*kernelK a k x*(exp (x : ℂ)-exp (-(x : ℂ)))/2*I_sq
  · linear_combination -(decay η : ℂ)*kernelK a k x*(exp (x : ℂ)+exp (-(x : ℂ)))/2*I_sq

private theorem top_integrable (p : Bool) {k : ℝ} (hk : 0 < k) (η : ℝ) :
    Integrable (fun t => entire p k η (topLine t)) := by
  let a := -(η : ℂ)*I
  have hi (b : ℂ) : Integrable (kernelK b k) := integrable_macdonald b k hk
  simpa only [top_entire, a, Pi.add_apply] using
    (((hi (a+1)).add ((hi (a-1)).const_mul (if p then (1 : ℂ) else -1))).const_mul
      ((decay η : ℂ)/2))

private theorem integral_top (p : Bool) {k : ℝ} (hk : 0 < k) (η : ℝ) :
    let a := -(η : ℂ)*I
    (∫ t : ℝ, entire p k η (topLine t)) = if p then
      -2*(decay η : ℂ)*deriv (macdonald a) k else 2*(decay η : ℂ)*a/k*macdonald a k := by
  let a := -(η : ℂ)*I
  have hi (b : ℂ) : Integrable (kernelK b k) := integrable_macdonald b k hk
  have hv (b : ℂ) : (∫ t : ℝ, kernelK b k t) = 2*macdonald b k := by unfold kernelK macdonald; ring
  simp_rw [top_entire,integral_const_mul,integral_add (hi _) ((hi _).const_mul _),
    integral_const_mul,hv]
  cases p
  · simp only [Bool.false_eq_true, ↓reduceIte,neg_one_mul]
    have h := macdonald_recurrence a (k : ℂ) hk
    dsimp only [a] at h
    rw [neg_mul] at h
    field_simp [ofReal_ne_zero.mpr hk.ne']
    linear_combination (decay η : ℂ)*h
  · simp only [↓reduceIte,one_mul]
    rw [(hasDerivAt_macdonald _ _ hk).deriv]
    ring

private theorem norm_real_kernel (p : Bool) (k η x : ℝ) :
    ‖scatteringKernel p k η x‖ = ‖accel p k η (x : ℂ)‖ := by
  rw [kernel_real,norm_mul]
  have h : ‖phase k η (x : ℂ)‖ = 1 := by simpa [edge] using phase_edge k η x 0
  rw [h,one_mul]

private theorem kernel_integrable (p : Bool) {k η : ℝ} (hk : |η| < k) :
    Integrable (scatteringKernel p k η) := by
  have hk' : 0 < k := (abs_nonneg η).trans_lt hk
  have hn (t : ℝ) : 0 < k*Real.cosh t+η := by
    linarith [mul_le_mul_of_nonneg_left (Real.one_le_cosh t) hk'.le, neg_abs_le η]
  have hc : Continuous (scatteringKernel p k η) := by
    cases p <;> unfold scatteringKernel <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
      fun_prop (disch := intros; first | positivity | exact pow_ne_zero _ (hn _).ne')
  apply hc.locallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    (g := fun t => Real.exp (-t))
  · filter_upwards with t
    simp only [Function.comp_apply,norm_real_kernel]
    cases p <;> simp [accel,denom,cosh_neg,sinh_neg]
  · apply Asymptotics.IsBigO.of_bound (64*(k+|η|)/k^2)
    filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop (4+8*|η|/k),
      eventually_ge_atTop (0 : ℝ)] with t ht ht'
    simpa only [norm_real_kernel,ofReal_re,abs_of_nonneg ht',Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using
      (large hk' (z := (t : ℂ)) (by simpa only [ofReal_re,abs_of_nonneg ht'] using ht)).2.2.2 p
  · exact ⟨Ioi 0,Ioi_mem_atTop _,integrableOn_exp_neg_Ioi 0⟩

private theorem real_nonzero {k η : ℝ} (hk : |η| < k) (x : ℝ) : denom k η x ≠ 0 := by
  have hc : 0 < k*Real.cosh x+η := by
    linarith [mul_le_mul_of_nonneg_left (Real.one_le_cosh x) ((abs_nonneg _).trans hk.le),
      neg_abs_le η]
  exact (show denom k η x = ((k*Real.cosh x+η : ℝ) : ℂ) by simp [denom]) ▸ ofReal_ne_zero.mpr hc.ne'

private theorem vert_bound {p : Bool} {k η : ℝ} (hk : 0 < k) {F : ℂ → ℂ}
    (hF : ∀ z, HasDerivAt F (entire p k η z) z) {x : ℝ} (hx : 4+8*|η|/k ≤ Real.exp |x|) :
    let C := Real.exp (|η| * (π/2))*(64*(k+|η|)/k^2)
    ‖corrected F p k η (topLine x)-corrected F p k η x‖ ≤ C*Real.exp (-|x|)*(π/2) := by
  let A := corrected F p k η
  let C := Real.exp (|η| * (π/2))*(64*(k+|η|)/k^2)
  let g (s : ℝ) := (-I)*(phase k η (edge x s)*accel p k η (edge x s))
  have hl (s : ℝ) := large hk (z := edge x s) (by rwa [edge_re])
  have hd (s : ℝ) : HasDerivAt (fun t => A (edge x t)) (g s) s := by
    have he : HasDerivAt (edge x) (-I) s := by
      have h := (((hasDerivAt_id s).ofReal_comp.mul_const I).const_sub (x : ℂ))
      change HasDerivAt (fun t : ℝ => (x : ℂ)-(t : ℂ)*I) (-I) s
      simpa only [id_eq,ofReal_one,one_mul] using h
    exact (deriv_corrected hF (hl s).1).scomp s he
  have hb (s : ℝ) (hs : s ∈ Ico 0 (π/2)) : ‖g s‖ ≤ C*Real.exp (-|x|) := by
    have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2,Real.pi_pos])
    have hη := mul_le_mul (neg_le_abs η) hs.2.le hs.1 (abs_nonneg η)
    have hphase : ‖phase k η (edge x s)‖ ≤ Real.exp (|η| * (π/2)) := by
      rw [phase_edge,Real.exp_le_exp]
      linarith [mul_nonneg (mul_nonneg hk.le (Real.cosh_pos x).le) hsin]
    simp only [g,norm_mul,norm_neg,norm_I,one_mul]
    have h := mul_le_mul hphase ((hl s).2.2.2 p) (norm_nonneg _) (Real.exp_pos _).le
    rwa [edge_re, ← mul_assoc] at h
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (fun s _ => (hd s).hasDerivWithinAt)
    hb (π/2) (right_mem_Icc.mpr (by positivity))
  simpa only [topLine,edge,ofReal_zero,zero_mul,sub_zero] using h

private theorem endpoint_limit {p : Bool} {k η : ℝ} (hk : 0 < k) {F : ℂ → ℂ}
    (hF : ∀ z, HasDerivAt F (entire p k η z) z) {x : ℝ → ℝ}
    (hx : Tendsto (fun R => |x R|) atTop atTop) :
    Tendsto (fun R => corrected F p k η (x R) - F (topLine (x R))) atTop (𝓝 0) := by
  let C := Real.exp (|η| * (π/2))*(64*(k+|η|)/k^2)
  have he := Real.tendsto_exp_atTop.comp hx
  have hL := he.eventually_ge_atTop (4+8*|η|/k)
  have hneg := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hx)
  have hcos : Tendsto (fun R => Real.cosh (x R)) atTop atTop := by
    apply tendsto_atTop_mono (fun R => ?_) (he.atTop_div_const (by norm_num : 0 < (2:ℝ)))
    rw [← Real.cosh_abs (x R),Real.cosh_eq]
    dsimp only [Function.comp_apply]
    linarith [Real.exp_pos (-|x R|)]
  have he' := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hcos.const_mul_atTop hk))
  have h₁ : Tendsto (fun R => corrected F p k η (x R)-corrected F p k η (topLine (x R)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun R => C*Real.exp (-|x R|)*(π/2)) atTop (𝓝 0)
      by simpa only [mul_zero,zero_mul,Function.comp_apply] using
           (hneg.const_mul C).mul_const (π/2))
    filter_upwards [hL] with R h
    rw [norm_sub_rev]
    exact vert_bound hk hF h
  have h₂ : Tendsto (fun R => vel p k η (topLine (x R))*phase k η (topLine (x R)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto
      (fun R => (8/k*decay η)*Real.exp (-(k*Real.cosh (x R))))
      atTop (𝓝 0) by simpa only [mul_zero,Function.comp_apply] using he'.const_mul (8/k*decay η))
    filter_upwards [hL] with R h
    have hlarge := large hk (z := topLine (x R)) (by rwa [topLine,edge_re])
    have hv : ‖vel p k η (topLine (x R))‖ ≤ 8/k := by cases p <;> tauto
    rw [norm_mul, topLine, phase_edge,Real.sin_pi_div_two,mul_one,neg_add,Real.exp_add]
    dsimp only [topLine] at hv
    dsimp [decay]
    rw [neg_mul]
    nlinarith [mul_le_mul_of_nonneg_right hv (mul_nonneg (Real.exp_pos (-(k*Real.cosh (x R)))).le
      (Real.exp_pos (-(η*(π/2)))).le)]
  have h := h₁.add h₂
  simp only [add_zero] at h
  exact h.congr fun R => by dsimp [corrected]; ring

/-- Evaluation of the two hyperbolic orbit integrals for both signs of the real phase
parameter η. The real-line integral is absolutely convergent for |η| < k. -/
theorem scattering_transform (p : Bool) {k η : ℝ} (hk : |η| < k) :
    let a := -(η : ℂ)*I
    (∫ u : ℝ, scatteringKernel p k η u) = if p then
      -2*(Real.exp (-η*(π/2)) : ℝ)*deriv (macdonald a) k
      else 2*(Real.exp (-η*(π/2)) : ℝ)*a/k*macdonald a k := by
  have hk' := (abs_nonneg _).trans_lt hk
  obtain ⟨F,hF⟩ := primitive p k η
  let G := corrected F p k η
  have hA (R : ℝ) : (∫ t in -R..R, scatteringKernel p k η t) = G R-G (-R : ℝ) := by
    have hcont : Continuous (scatteringKernel p k η) := by
      have hn (t : ℝ) : k*Real.cosh t+η ≠ 0 := by exact_mod_cast
        (show ((k*Real.cosh t+η : ℝ) : ℂ) ≠ 0 by simpa [denom] using real_nonzero hk t)
      cases p <;> unfold scatteringKernel <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
        fun_prop (disch := intros; exact pow_ne_zero _ (hn _))
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => by
      rw [kernel_real]; exact (deriv_corrected hF (real_nonzero hk t)).comp_ofReal)
      (hcont.intervalIntegrable ..)
  have hB (R : ℝ) : (∫ t in -R..R, entire p k η (topLine t)) =
      F (topLine R)-F (topLine (-R)) := by
    have hl (t : ℝ) : HasDerivAt (fun s => F (topLine s)) (entire p k η (topLine t)) t := by
      have h := (hF (topLine t)).comp (t : ℂ) ((hasDerivAt_id' (t : ℂ)).sub_const ((π/2 : ℝ)*I))
      simpa only [Function.comp_def,mul_one,topLine,edge] using h.comp_ofReal
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hl t)
      ((top_integrable p hk' η).intervalIntegrable ..)
  have hplus := endpoint_limit (x := id) hk' hF
    (tendsto_id.congr' ((eventually_ge_atTop (0:ℝ)).mono fun R h => (abs_of_nonneg h).symm))
  have hminus := endpoint_limit (x := fun R => -R) hk' hF
    (tendsto_id.congr' ((eventually_ge_atTop (0:ℝ)).mono fun R h => by simp [abs_of_nonneg h]))
  have h := hplus.sub hminus
  simp only [id_eq,sub_zero] at h
  have h' : Tendsto (fun R : ℝ => (∫ t in -R..R, scatteringKernel p k η t) -
      ∫ t in -R..R, entire p k η (topLine t)) atTop (𝓝 0) := by
    apply h.congr
    intro R
    rw [hA,hB]
    dsimp only [G]
    ring
  have H := (intervalIntegral_tendsto_integral (kernel_integrable p hk) tendsto_neg_atTop_atBot
    (tendsto_id (α := ℝ))).sub (intervalIntegral_tendsto_integral (top_integrable p hk' η)
      tendsto_neg_atTop_atBot (tendsto_id (α := ℝ)))
  have H' := sub_eq_zero.mp (tendsto_nhds_unique H h')
  rw [H',integral_top p hk']
  rfl

end ProjectAinos.SpecialFunctions.Bessel
