/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.BesselIntegral
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-! # Angular integral of a squared Bessel harmonic

The Cauchy product of the factorial series, summed by Vandermonde's identity, yields a
single series for Jₘ². Integration over solid angle cancels the central factorials,
leaving the integral of the doubled order J₂ₘ in the synchrotron harmonic power.
-/

@[expose] public section
noncomputable section

open Complex MeasureTheory Finset Set
open scoped Real
namespace ProjectAinos.SpecialFunctions.Bessel

private theorem fact (k : ℕ) : (k.factorial : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)

private def term (m j : ℕ) (z : ℂ) :=
  (z/2)^m * (-(z/2)^2)^j / ((j.factorial : ℂ)*(m+j).factorial)

private def common (m j : ℕ) (z : ℂ) :=
  (-1 : ℂ)^j * (z/2)^(2*(m+j)) / (((m+j).factorial : ℂ)^2)
private def squareTerm (m j : ℕ) (z : ℂ) := common m j z * ((2*(m+j)).choose j : ℂ)

private theorem pair (m i j h : ℕ) (hh : i+j=h) (z : ℂ) :
    term m i z * term m j z =
      common m h z * (((m+h).choose i : ℂ)*((m+h).choose j : ℂ)) := by
  rw [Nat.cast_choose ℂ (by omega : i ≤ m+h), Nat.cast_choose ℂ (by omega : j ≤ m+h),
    show m+h-i = m+j by omega, show m+h-j = m+i by omega]
  have hpow : (z/2)^(2*(m+h)) = (z/2)^m * ((z/2)^2)^i * (z/2)^m * ((z/2)^2)^j := by
    simp only [← pow_mul, ← pow_add]
    congr 1
    omega
  have he (k : ℕ) : (-(z/2)^2)^k = (-1 : ℂ)^k * ((z/2)^2)^k := by
    rw [← mul_pow, neg_one_mul]
  unfold term common
  rw [hpow, he, he, ← hh, pow_add (-1 : ℂ)]
  have f₁ := fact i
  have f₂ := fact j
  have f₃ := fact (m+i)
  have f₄ := fact (m+j)
  have f₅ := fact (m+(i+j))
  field_simp

private theorem square_series (m : ℕ) (z : ℂ) :
    HasSum (fun h => squareTerm m h z) (besselJ m z ^ 2) := by
  have ha : HasSum (fun j => term m j z) (besselJ m z) := hasSum_nat m z
  have hn := ha.summable.norm
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hn hn).of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hn hn, ha.tsum_eq, ← sq] at hsum
  apply hsum.congr_fun
  intro h
  unfold squareTerm
  rw [two_mul, Nat.add_choose_eq]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ij hij => (pair m _ _ _ (mem_antidiagonal.mp hij) z).symm

private theorem sine_moment (k : ℕ) : (∫ θ in 0..π, Real.sin θ ^ (2*k+1)) =
    (2:ℝ)^(2*k+1)*((k.factorial : ℝ)^2)/(2*k+1).factorial := by
  induction k with
  | zero => norm_num [integral_sin]
  | succ k ih =>
    have hn : 2*(k+1)+1 = (2*k+1)+2 := by omega
    rw [hn, integral_sin_pow, Real.sin_zero, Real.sin_pi, zero_pow (by omega : 2*k+1+1 ≠ 0),
      zero_mul, zero_mul, sub_self, zero_div, zero_add, ih]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
    push_cast
    field_simp
    ring

private theorem norm_squareTerm_mono (m j : ℕ) {z w : ℂ} (h : ‖z‖ ≤ ‖w‖) :
    ‖squareTerm m j z‖ ≤ ‖squareTerm m j w‖ := by
  simp only [squareTerm, common, norm_mul, norm_div, norm_pow]
  gcongr

private theorem integral_term (m j : ℕ) (z : ℂ) :
    (∫ θ in 0..π, (Real.sin θ : ℂ) * squareTerm m j (z*Real.sin θ)) =
      2 * ∫ t in (0 : ℝ)..1, term (2*m) j (2*z*t) := by
  let k := m+j
  have hl (s : ℝ) : (s : ℂ)*squareTerm m j (z*s) =
      squareTerm m j z * ((s^(2*k+1) : ℝ) : ℂ) := by
    unfold squareTerm common
    rw [show z*s/2 = z/2*s by ring, mul_pow]
    dsimp only [k]
    push_cast
    rw [pow_succ]
    ring
  have hr (t : ℝ) : term (2*m) j (2*z*t) =
      term (2*m) j (2*z) * ((t^(2*k) : ℝ) : ℂ) := by
    unfold term
    rw [show 2*z*t/2 = (2*z/2)*t by ring]
    simp only [mul_pow, ofReal_pow, ← mul_neg]
    dsimp only [k]
    rw [Nat.mul_add, pow_add (t : ℂ), pow_mul]
    ring
  simp_rw [hl, hr, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  rw [sine_moment, _root_.integral_pow]
  simp only [one_pow, zero_pow (by omega : 2*k+1 ≠ 0), sub_zero, squareTerm, common, term,
    Nat.cast_choose ℂ (by omega : j ≤ 2*(m+j)), show 2*(m+j)-j = 2*m+j by omega]
  dsimp only [k]
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hpow : (-(z)^2)^j = (-1 : ℂ)^j * (z^2)^j := by rw [← mul_pow, neg_one_mul]
  push_cast
  rw [show 2*z/2 = z by ring, hpow, pow_succ (2 : ℂ), div_pow, Nat.mul_add, pow_add z,
    pow_mul z 2 j]
  have hn : ((2 : ℂ) * (m + j) + 1) ≠ 0 := by exact_mod_cast (by omega : 2*(m+j)+1 ≠ 0)
  have hn' : ((2 : ℂ)*m+2*j+1) ≠ 0 := by exact_mod_cast (by omega : 2*m+2*j+1 ≠ 0)
  have f₁ := fact j
  have f₂ := fact (m+j)
  have f₃ := fact (2*m+j)
  have f₄ := fact (2*m+2*j)
  have f₅ := fact (2*(m+j))
  field_simp

private theorem term_norm_mono (m j : ℕ) {z w : ℂ} (h : ‖z‖ ≤ ‖w‖) :
    ‖term m j z‖ ≤ ‖term m j w‖ := by
  simp only [term, norm_mul, norm_div, norm_pow, norm_neg]
  gcongr

/-- The polar angular average of the squared mth Bessel harmonic, for arbitrary complex z
and every nonnegative order. The doubled-order integral uses a fixed unit interval. -/
theorem integral_sin_bessel_sq (m : ℕ) (z : ℂ) :
    (∫ θ in 0..π, (Real.sin θ : ℂ) * besselJ m (z*Real.sin θ)^2) =
      2 * ∫ t in (0 : ℝ)..1, besselJ (2*m : ℕ) (2*z*t) := by
  have hl := intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := π)
    (μ := volume) (F := fun (j : ℕ) θ => (Real.sin θ : ℂ)*squareTerm m j (z*Real.sin θ))
    (fun j _ => ‖squareTerm m j z‖)
    (fun _ => Continuous.aestronglyMeasurable (by unfold squareTerm common; fun_prop))
    (fun j => ae_of_all _ fun θ _ => by
      have hθ : ‖(Real.sin θ : ℂ)‖ ≤ 1 := by
        simpa only [norm_real, Real.norm_eq_abs] using Real.abs_sin_le_one θ
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) hθ).trans
      apply norm_squareTerm_mono
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) hθ)
    (ae_of_all _ fun _ _ => (square_series m z).summable.norm)
    intervalIntegrable_const (ae_of_all _ fun θ _ => (square_series m (z*Real.sin θ)).mul_left _)
  have hr := intervalIntegral.hasSum_integral_of_dominated_convergence (a := (0 : ℝ)) (b := 1)
    (μ := volume) (F := fun (j : ℕ) (t : ℝ) => term (2*m) j (2*z*t))
    (fun j _ => ‖term (2*m) j (2*z)‖)
    (fun _ => Continuous.aestronglyMeasurable (by unfold term; fun_prop))
    (fun j => ae_of_all _ fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      apply term_norm_mono
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      exact mul_le_of_le_one_right (norm_nonneg _) ht.2)
    (ae_of_all _ fun _ _ => (hasSum_nat (2*m) (2*z)).summable.norm)
    intervalIntegrable_const (ae_of_all _ fun t _ => hasSum_nat (2*m) (2*z*t))
  simp only [integral_term] at hl
  exact hl.unique (hr.mul_left 2)

private def lineBessel (k : ℤ) (z : ℂ) (t : ℝ) := besselJ k (2*z*t)

private theorem line_cont (k : ℤ) (z : ℂ) : Continuous (lineBessel k z) :=
  (continuous_iff_continuousAt.mpr fun x => (analyticAt_besselJ_int k x).continuousAt).comp
    (continuous_const.mul continuous_ofReal)

private theorem line_deriv (k : ℤ) (z : ℂ) (t : ℝ) : HasDerivAt (lineBessel k z)
    (deriv (besselJ k) (2*z*t)*(2*z)) t := by
  have h := (analyticAt_besselJ_int k (2*z*t)).differentiableAt.hasDerivAt
  change HasDerivAt (fun s : ℝ => besselJ k (2*z*(s : ℂ))) _ t
  convert (h.comp (t : ℂ) ((hasDerivAt_id' (t : ℂ)).const_mul (2*z))).comp_ofReal using 1
  · rfl
  · rw [mul_one]

private theorem adjacent_average (m : ℕ) (z : ℂ) :
    let k : ℤ := 2*(m+1)
    z * ((∫ t in (0:ℝ)..1, lineBessel (k-2) z t) -
      2*(∫ t in (0:ℝ)..1, lineBessel k z t) + ∫ t in (0:ℝ)..1, lineBessel (k+2) z t) =
        2*deriv (besselJ k) (2*z) := by
  let k : ℤ := 2*(m+1)
  have hd (t : ℝ) : HasDerivAt (fun s => lineBessel (k-1) z s - lineBessel (k+1) z s)
      (z*(lineBessel (k-2) z t-2*lineBessel k z t+lineBessel (k+2) z t)) t := by
    convert (line_deriv (k-1) z t).sub (line_deriv (k+1) z t) using 1
    have h := twice_deriv_int (k-1) (2*z*t)
    have h' := twice_deriv_int (k+1) (2*z*t)
    rw [show k-1-1=k-2 by ring, sub_add_cancel] at h
    rw [add_sub_cancel_right, show k+1+1=k+2 by ring] at h'
    unfold lineBessel
    linear_combination -z*h + z*h'
  have hi (d : ℤ) : IntervalIntegrable (lineBessel d z) volume 0 1 :=
    (line_cont d z).intervalIntegrable ..
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun t _ => hd t)
    ((((hi _).sub ((hi _).const_mul 2)).add (hi _)).const_mul z)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add ((hi _).sub
    ((hi _).const_mul 2)) (hi _), intervalIntegral.integral_sub (hi _) ((hi _).const_mul 2),
    intervalIntegral.integral_const_mul] at h
  have hm : ((k-1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by dsimp [k]; omega)
  have hp : ((k+1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by dsimp [k]; omega)
  simpa only [lineBessel, ofReal_zero, ofReal_one, mul_zero, mul_one, besselJ_zero,
    hm, hp, ↓reduceIte, sub_zero, ← twice_deriv_int] using h

/-- The polar angular integral of the synchrotron Bessel combination in harmonic m+1.
Multiplication by z includes the zero-argument case. -/
theorem integral_angular_combination (m : ℕ) (b z : ℂ) :
    z * (∫ θ in 0..π, (Real.sin θ : ℂ) *
      (b^2/2*(besselJ m (z*Real.sin θ)^2 + besselJ (m+2 : ℕ) (z*Real.sin θ)^2) -
        besselJ (m+1 : ℕ) (z*Real.sin θ)^2)) =
      2*b^2*deriv (besselJ (2*(m+1) : ℕ)) (2*z) +
        2*z*(b^2-1)*∫ t in (0 : ℝ)..1, besselJ (2*(m+1) : ℕ) (2*z*t) := by
  let f (k : ℕ) (θ : ℝ) := (Real.sin θ : ℂ) * besselJ k (z*Real.sin θ)^2
  have hc (k : ℕ) : Continuous (besselJ (k : ℂ)) :=
    continuous_iff_continuousAt.mpr fun x => (analyticAt_besselJ_int (k : ℤ) x).continuousAt
  have hi (k : ℕ) : IntervalIntegrable (f k) volume 0 π := by
    have hs := continuous_ofReal.comp Real.continuous_sin
    exact (hs.mul (((hc k).comp (continuous_const.mul hs)).pow 2)).intervalIntegrable ..
  have he (θ : ℝ) : (Real.sin θ : ℂ) *
      (b^2/2*(besselJ m (z*Real.sin θ)^2 + besselJ (m+2 : ℕ) (z*Real.sin θ)^2) -
        besselJ (m+1 : ℕ) (z*Real.sin θ)^2) =
      b^2/2*(f m θ + f (m+2) θ) - f (m+1) θ := by unfold f; ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub (((hi m).add (hi (m+2))).const_mul _) (hi (m+1)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hi m) (hi (m+2))]
  dsimp only [f]
  simp_rw [integral_sin_bessel_sq]
  have h := adjacent_average m z
  dsimp only [lineBessel] at h
  rw [show (2*((m : ℤ)+1)-2) = ((2*m : ℕ) : ℤ) by push_cast; ring,
    show (2*((m : ℤ)+1)+2) = ((2*(m+2) : ℕ) : ℤ) by push_cast; ring,
    show 2*((m : ℤ)+1) = ((2*(m+1) : ℕ) : ℤ) by push_cast; ring] at h
  simp only [Int.cast_natCast] at h
  linear_combination b^2*h

end ProjectAinos.SpecialFunctions.Bessel
