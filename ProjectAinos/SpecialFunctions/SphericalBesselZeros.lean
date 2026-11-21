/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Bessel
public import ProjectAinos.SpecialFunctions.SphericalBesselEquation
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! # Positive zeros of spherical Bessel functions

Rolle's theorem applied to jₗ(x)/xˡ gives a zero of the next degree between two
positive zeros of the current degree. The Wronskian gives simplicity in every degree.
-/

@[expose] public section
noncomputable section
open Set Complex
open scoped Real ContDiff
namespace ProjectAinos.SpecialFunctions.Bessel

private theorem real_value (n : ℕ) {x : ℝ} (hx : x ≠ 0) : (sphericalJ n x).im = 0 := by
  have hz := ofReal_ne_zero.mpr hx
  induction n using Nat.twoStepInduction with
  | zero => simp [sphericalJ_zero_order hz, ← ofReal_sin, ← ofReal_div]
  | one => simp [sphericalJ_one_order hz, ← ofReal_sin, ← ofReal_cos, ← ofReal_pow, ← ofReal_div]
  | more n h₀ h₁ =>
    have h := congrArg Complex.im (sphericalJ_recurrence x n)
    simp [mul_im,h₀,h₁] at h
    exact h.resolve_left hx

private theorem dquot (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (sphericalJ n y).re / y^n)
      (-(sphericalJ (n+1) x).re / x^n) x := by
  have h := ((hasDerivAt_sphericalJ n (ofReal_ne_zero.mpr hx.ne')).real_of_complex).div
    ((hasDerivAt_id x).pow n) (pow_ne_zero _ hx.ne')
  apply h.congr_deriv
  simp only [id_eq,Pi.pow_apply,sub_re, ← ofReal_natCast, ← ofReal_div,mul_re,
    ofReal_re,ofReal_im,zero_mul,sub_zero]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_one,pow_succ,Nat.cast_succ]
    field_simp
    ring

/-- Every positive interval between two zeros of jₙ contains a zero of jₙ₊₁. -/
theorem sphericalJ_zero_between (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (h₁ : sphericalJ n a = 0) (h₂ : sphericalJ n b = 0) :
    ∃ c ∈ Ioo a b, sphericalJ (n+1) c = 0 := by
  obtain ⟨c,hc,hd⟩ := exists_hasDerivAt_eq_zero hab
    (fun t ht => (dquot n (ha.trans_le ht.1)).continuousAt.continuousWithinAt)
    (by simp [h₁,h₂]) (fun t ht => dquot n (ha.trans ht.1))
  refine ⟨c,hc,Complex.ext ?_ (real_value _ (ha.trans hc.1).ne')⟩
  simpa [(pow_ne_zero n (ha.trans hc.1).ne')] using hd

/-- Every angular degree has an unbounded sequence of positive regular Bessel zeros. -/
theorem sphericalJ_zeros_unbounded (n : ℕ) (R : ℝ) :
    ∃ x : ℝ, R < x ∧ 0 < x ∧ sphericalJ n x = 0 := by
  induction n generalizing R with
  | zero =>
    obtain ⟨m,hm⟩ := exists_nat_gt (max R 0 / π)
    have h := (div_lt_iff₀ Real.pi_pos).mp hm
    have hp : 0 < m*π := (le_max_right R 0).trans_lt h
    refine ⟨m*π,(le_max_left R 0).trans_lt h,hp,?_⟩
    rw [sphericalJ_zero_order (ofReal_ne_zero.mpr hp.ne'),← ofReal_sin,Real.sin_nat_mul_pi]
    simp
  | succ n ih =>
    obtain ⟨a,hR,ha,h₁⟩ := ih R
    obtain ⟨b,hab,_,h₂⟩ := ih a
    obtain ⟨c,hc,h₃⟩ := sphericalJ_zero_between n ha hab h₁ h₂
    exact ⟨c,hR.trans hc.1,ha.trans hc.1,h₃⟩

/-- A nonzero zero of the regular spherical Bessel function is simple. -/
theorem sphericalJ_simple (n : ℕ) {z : ℂ} (hz : z ≠ 0) (h : sphericalJ n z = 0) :
    deriv (sphericalJ n) z ≠ 0 := by
  intro hd
  exact (one_div_ne_zero (pow_ne_zero 2 hz)) (by simpa [h,hd] using (spherical_wronskian n hz).symm)

/-- The smooth squared-radius dipole profile vanishes at each positive zero of j₁(kr).
This uses the conserved Wronskian of r F₃/₂(r²) with sin(kr). -/
theorem radialProfile_dipole_zero {k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hz : sphericalJ 1 ((k*r : ℝ) : ℂ) = 0) : radialProfile (5/2) k (r^2) = 0 := by
  let F := radialProfile (3/2) k
  let u (t : ℝ) := t*F (t^2)
  let v (t : ℝ) := F (t^2)+2*t^2*deriv F (t^2)
  have hF : ContDiff ℝ ∞ F := contDiff_radialProfile ..
  have hF' : ContDiff ℝ ∞ (deriv F) := (show ContDiff ℝ (∞+1) F by simpa using hF).deriv'
  have d {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
      HasDerivAt (fun t => f (t^2)) (deriv f (x^2)*(2*x)) x := by
    simpa [Function.comp_def] using
      (hf.differentiable (by simp) _).hasDerivAt.comp x ((hasDerivAt_id' x).pow 2)
  have du (t : ℝ) : HasDerivAt u (v t) t := by
    apply ((hasDerivAt_id' t).mul (d hF t)).congr_deriv
    dsimp [v]; ring
  have dv (t : ℝ) : HasDerivAt v (-k^2*u t) t := by
    apply ((d hF t).add (((((hasDerivAt_id' t).pow 2).const_mul 2)).mul (d hF' t))).congr_deriv
    have H := radialProfile_equation (3/2) k (t^2)
    change 4*t^2*deriv (deriv F) (t^2)+4*(3/2)*deriv F (t^2)+k^2*F (t^2)=0 at H
    dsimp [u]
    linear_combination t*H
  let W (t : ℝ) := v t*Real.sin (k*t)-k*u t*Real.cos (k*t)
  have dW (t : ℝ) : HasDerivAt W 0 t := by
    have dt := (hasDerivAt_id' t).const_mul k
    apply (((dv t).mul dt.sin).sub (((du t).const_mul k).mul dt.cos)).congr_deriv
    ring
  have hW := is_const_of_deriv_eq_zero (fun t => (dW t).differentiableAt)
    (fun t => (dW t).deriv) r 0
  have hp := mul_pos hk hr
  rw [sphericalJ_one_order (ofReal_ne_zero.mpr hp.ne'),← ofReal_sin,← ofReal_cos,
    ← ofReal_pow,← ofReal_div,← ofReal_div,← ofReal_sub,ofReal_eq_zero] at hz
  field_simp [hp.ne'] at hz
  have he : Real.sin (k*r) = k*r*Real.cos (k*r) := by linarith only [hz]
  have hs : Real.sin (k*r) ≠ 0 := by
    intro h
    have hc := (mul_eq_zero.mp (he.symm.trans h)).resolve_left hp.ne'
    simpa [h,hc] using Real.sin_sq_add_cos_sq (k*r)
  simp [W,u,v] at hW
  have hF₁ : deriv F (r^2) = -(k^2)/4*radialProfile (5/2) k (r^2) := by
    simpa [F,show (3/2+1 : ℝ) = 5/2 by norm_num] using
      (hasDerivAt_radialProfile (3/2) k (r^2)).deriv
  rw [hF₁] at hW
  have h : k^2*r^2*Real.sin (k*r)*radialProfile (5/2) k (r^2)=0 := by
    linear_combination -2*hW+2*F (r^2)*(he)
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hk.ne')
    (pow_ne_zero _ hr.ne')) hs)

end ProjectAinos.SpecialFunctions.Bessel
