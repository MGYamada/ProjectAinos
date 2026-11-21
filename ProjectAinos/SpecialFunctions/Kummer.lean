/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

/-! # Kummer's confluent hypergeometric function

The regularized series is entire in its argument and obeys the differential equation
even at poles of the lower parameter. Multiplying by Γ(b) gives the standard
normalization away from these poles. At negative integral upper parameter the series
terminates, giving the generalized Laguerre polynomials.
-/

@[expose] public section
noncomputable section
open Complex FormalMultilinearSeries Polynomial
open scoped Nat
namespace ProjectAinos.SpecialFunctions.Kummer

private abbrev F (a b : ℂ) := regularizedHGFun {a} {b}
private abbrev c (a b : ℂ) := regularizedHGFunCoeff {a} {b}
private abbrev P (a b : ℂ) := regularizedHGFunSeries {a} {b}

private theorem rad (a b : ℂ) : (P a b).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top (by simp)

private theorem coeff_next (a b : ℂ) (n : ℕ) :
    (n+1 : ℂ)*c a b (n+1) = a*c (a+1) (b+1) n := by
  simp [c,regularizedHGFunCoeff,Nat.factorial_succ,ascPochhammer_succ_left,eval_comp,
    add_comm,add_left_comm]
  field_simp

private theorem coeff_balance (a b : ℂ) (n : ℕ) :
    (b+n)*(a*c (a+1) (b+1) n) = (a+n)*c a b n := by
  have h := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (b+n)
  have hp : a*(ascPochhammer ℂ n).eval (a+1) = (a+n)*(ascPochhammer ℂ n).eval a := by
    have he := congrArg (eval a) ((ascPochhammer_succ_left ℂ n).symm.trans
      (ascPochhammer_succ_right ℂ n))
    simpa [eval_comp,mul_comm] using he
  simp only [c,regularizedHGFunCoeff,Multiset.map_singleton,Multiset.prod_singleton,
    div_eq_mul_inv,mul_inv,show b+1+n=b+n+1 by ring]
  rw [h]
  linear_combination (b+n)*(↑(n !) : ℂ)⁻¹*(Gamma (b+n+1))⁻¹*hp

private theorem series (a b z : ℂ) : HasSum (fun n : ℕ => z^n*c a b n) (F a b z) := by
  simpa [F,P,c,regularizedHGFun,apply_eq_pow_smul_coeff,smul_eq_mul] using
    ((P a b).hasFPowerSeriesOnBall (by rw [rad]; simp)).hasSum (y := z) (by rw [rad]; simp)

private theorem dF (a b z : ℂ) : HasDerivAt (F a b) (a*F (a+1) (b+1) z) z := by
  have hs := ((P a b).hasFPowerSeriesOnBall (by rw [rad]; simp)).fderiv.hasSum (y := z)
    (by rw [rad]; simp)
  have h := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).hasSum hs
  have he : deriv (F a b) z = a*F (a+1) (b+1) z := by
    apply HasSum.unique _ ((series (a+1) (b+1) z).mul_left a)
    change HasSum _ ((fderiv ℂ (P a b).sum z) 1)
    simp only [zero_add,ContinuousLinearMap.apply_apply,apply_eq_pow_smul_coeff,_root_.smul_apply,
      derivSeries_coeff_one,P,regularizedHGFunSeries_coeff,smul_eq_mul,nsmul_eq_mul,
      Nat.cast_succ,coeff_next] at h
    exact h.congr_fun fun n => by ring
  rw [← he]
  exact (analyticAt_regularizedHGFun_of_card_le (by simp) z).differentiableAt.hasDerivAt

private theorem weighted (a b z : ℂ) :
    HasSum (fun n : ℕ => z^n*(n*c a b n)) (z*(a*F (a+1) (b+1) z)) := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one,Nat.cast_zero,zero_mul,mul_zero,sub_zero,Nat.cast_succ,
    coeff_next,pow_succ]
  exact (((series (a+1) (b+1) z).mul_left a).mul_left z).congr_fun fun n => by ring

/-- Classical confluent hypergeometric function ₁F₁(a;b;z). -/
def M (a b z : ℂ) := Gamma b * regularizedHGFun {a} {b} z

/-- The defining series has infinite radius in z. -/
theorem hasSum_M (a b z : ℂ) :
    HasSum (fun n : ℕ => Gamma b*z^n*regularizedHGFunCoeff {a} {b} n) (M a b z) :=
  ((series a b z).mul_left (Gamma b)).congr_fun fun n => by ring

/-- Normalization at the origin for each admissible lower parameter. -/
theorem M_zero (a b : ℂ) (hb : ∀ n : ℕ, b ≠ -n) : M a b 0 = 1 := by
  simp [M,regularizedHGFunCoeff,Gamma_ne_zero hb]

/-- The argument derivative, in a form valid without dividing by the lower parameter. -/
theorem hasDerivAt_M (a b z : ℂ) : HasDerivAt (M a b)
    (Gamma b*(a*regularizedHGFun {a+1} {b+1} z)) z := (dF a b z).const_mul _

/-- Kummer's differential equation for arbitrary complex parameters. -/
theorem equation (a b z : ℂ) :
    z*deriv (deriv (M a b)) z+(b-z)*deriv (M a b) z = a*M a b z := by
  have h : z*(a*((a+1)*F (a+1+1) (b+1+1) z))+b*(a*F (a+1) (b+1) z) =
      z*(a*F (a+1) (b+1) z)+a*F a b z := by
    apply HasSum.unique (L := .unconditional _) (f := fun n : ℕ => z^n*((a+n)*c a b n))
    · have hs := ((weighted (a+1) (b+1) z).mul_left a).add
        (((series (a+1) (b+1) z).mul_left a).mul_left b)
      rw [show z*(a*((a+1)*F (a+1+1) (b+1+1) z)) = a*(z*((a+1)*F (a+1+1) (b+1+1) z)) by ring]
      exact hs.congr_fun fun n => by rw [← coeff_balance]; ring
    · exact ((weighted a b z).add ((series a b z).mul_left a)).congr_fun fun n => by ring
  have hd : deriv (M a b) = fun w => Gamma b*(a*F (a+1) (b+1) w) :=
    funext fun w => (hasDerivAt_M a b w).deriv
  rw [hd,(((dF (a+1) (b+1) z).const_mul a).const_mul (Gamma b)).deriv,M]
  linear_combination Gamma b*h

/-- Coefficients of Lₙᵅ, polynomial in α even at negative integral α. -/
def laguerreCoeff (n : ℕ) (α : ℂ) (j : ℕ) : ℂ :=
  (ascPochhammer ℂ j).eval (-(n : ℂ)) * (ascPochhammer ℂ (n-j)).eval (α+1+j) / ((n !)*(j !))

/-- The generalized Laguerre polynomial Lₙᵅ in the classical normalization. -/
def laguerre (n : ℕ) (α : ℂ) : ℂ[X] :=
  ∑ j ∈ Finset.range (n+1), monomial j (laguerreCoeff n α j)

private theorem coeff_laguerre (n j : ℕ) (hj : j ≤ n) (α : ℂ)
    (hb : ∀ m : ℕ, α+1 ≠ -m) :
    laguerreCoeff n α j = (ascPochhammer ℂ n).eval (α+1)/(n !) *
      (Gamma (α+1)*regularizedHGFunCoeff {-(n : ℂ)} {α+1} j) := by
  have hb' (m : ℕ) : α+1+j ≠ -m := by
    intro he
    apply hb (m+j)
    push_cast
    linear_combination he
  rw [laguerreCoeff,← Gamma_add_nat_div_Gamma_eq _ hb,← Gamma_add_nat_div_Gamma_eq _ hb']
  simp only [regularizedHGFunCoeff,Multiset.map_singleton,Multiset.prod_singleton,
    Nat.cast_sub hj,show α+1+j+(n-j : ℂ)=α+1+n by ring]
  field_simp [Gamma_ne_zero hb,Gamma_ne_zero hb']

/-- The terminating confluent hypergeometric representation of Lₙᵅ. -/
theorem laguerre_eval (n : ℕ) (α z : ℂ) (hb : ∀ m : ℕ, α+1 ≠ -m) :
    (laguerre n α).eval z = (ascPochhammer ℂ n).eval (α+1)/(n !) * M (-n) (α+1) z := by
  have h := ((hasSum_M (-n) (α+1) z).mul_left ((ascPochhammer ℂ n).eval (α+1)/(n !))).tsum_eq
  rw [← h,tsum_eq_sum (s := Finset.range (n+1)) (fun j hj => ?_)]
  · simp only [laguerre,eval_finsetSum,eval_monomial]
    apply Finset.sum_congr rfl
    intro j hj
    rw [coeff_laguerre _ _ (by simpa using hj) _ hb]
    ring
  · have hj' : n < j := by simpa using hj
    rw [regularizedHGFunCoeff_eq_zero_left _ _ j n (by simp) hj']
    ring

private theorem tail_zero (n j : ℕ) (α : ℂ) (hj : n < j) : laguerreCoeff n α j = 0 := by
  simp [laguerreCoeff,ascPochhammer_eval_neg_coe_nat_of_lt hj]

/-- Taylor coefficients of the terminating polynomial at every degree. -/
theorem coeff_laguerre_polynomial (n j : ℕ) (α : ℂ) :
    (laguerre n α).coeff j = laguerreCoeff n α j := by
  simp only [laguerre,finsetSum_coeff,coeff_monomial,Finset.sum_ite_eq',Finset.mem_range]
  split_ifs with h
  · rfl
  · exact (tail_zero _ _ _ (by omega)).symm

private theorem balance (n j : ℕ) (α : ℂ) :
    (j+1 : ℂ)*(α+1+j)*laguerreCoeff n α (j+1) = (j-n : ℂ)*laguerreCoeff n α j := by
  rcases lt_trichotomy j n with hj | rfl | hj
  · obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
    have h₁ : n-(j+1)=m := by omega
    have h₂ : n-j=m+1 := by omega
    simp only [laguerreCoeff,h₁,h₂,ascPochhammer_succ_eval (k := -(n : ℂ)),
      ascPochhammer_succ_left ℂ m,eval_mul,eval_X,eval_comp,eval_add,eval_one,
      Nat.cast_succ,Nat.factorial_succ,Nat.cast_mul]
    field_simp
    ring
  · simp [tail_zero]
  · rw [tail_zero n j α hj,tail_zero n (j+1) α (by omega)]
    ring

private theorem coeff_euler (p : ℂ[X]) (j : ℕ) :
    (X*p.derivative).coeff j = j*p.coeff j := by
  cases j with
  | zero => simp
  | succ j => rw [coeff_X_mul,coeff_derivative,mul_comm,Nat.cast_succ]

/-- Laguerre's differential equation, including exceptional integral α. -/
theorem laguerre_equation (n : ℕ) (α : ℂ) :
    let p := laguerre n α
    X*p.derivative.derivative+(C (α+1)-X)*p.derivative+C (n : ℂ)*p = 0 := by
  dsimp only
  ext j
  simp only [sub_mul,coeff_add,coeff_sub,coeff_C_mul,coeff_euler,coeff_derivative,
    coeff_laguerre_polynomial,coeff_zero]
  linear_combination balance n j α

/-- Normalization at the origin in the Laguerre convention. -/
theorem laguerre_zero (n : ℕ) (α : ℂ) :
    (laguerre n α).eval 0 = (ascPochhammer ℂ n).eval (α+1)/(n !) := by
  simp [← coeff_zero_eq_eval_zero,coeff_laguerre_polynomial,laguerreCoeff]

end ProjectAinos.SpecialFunctions.Kummer
