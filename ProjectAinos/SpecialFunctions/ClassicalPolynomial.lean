/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Jacobi and Gegenbauer polynomials

The differentiated Rodrigues recurrence constructs the Jacobi polynomials over ℂ
without divisions by parameter-dependent factors. The Gegenbauer raising recurrence
uses the normalization Cₙᵅ(1) = (2α)ₙ/n!. Both differential equations are polynomial
identities at all parameter values.
-/

@[expose] public section
noncomputable section
open Polynomial
open scoped Nat
namespace ProjectAinos.SpecialFunctions.ClassicalPolynomial

/-- Jacobi polynomial Pₙ⁽ᵃ˒ᵇ⁾ in Rodrigues normalization. -/
def jacobi : ℕ → ℂ → ℂ → ℂ[X]
  | 0, _, _ => 1
  | n+1, a, b =>
    let p := jacobi n (a+1) (b+1)
    C ((2*((n : ℂ)+1))⁻¹) *
      ((C (a-b)+C (a+b+2)*X)*p-(1-X^2)*p.derivative)

private abbrev q : ℂ[X] := 1-X^2
private abbrev A (a b : ℂ) : ℂ[X] := C (a-b)+C (a+b+2)*X

private theorem Ad (a b : ℂ) : derivative (A a b) = C (a+b+2) := by simp [A,derivative_mul]

private theorem step (n : ℕ) (a b : ℂ) :
    C (2*((n : ℂ)+1))*jacobi (n+1) a b =
      A a b*jacobi n (a+1) (b+1)-q*(jacobi n (a+1) (b+1)).derivative := by
  have hn : 2*((n : ℂ)+1) ≠ 0 := mul_ne_zero (by norm_num)
    (by exact_mod_cast Nat.succ_ne_zero n)
  rw [jacobi,← mul_assoc,← C_mul,mul_inv_cancel₀ hn,C_1,one_mul]

private theorem step_deriv (n : ℕ) (a b : ℂ)
    (h : let p := jacobi n (a+1) (b+1)
         q*p.derivative.derivative - A (a+1) (b+1)*p.derivative +
           C ((n : ℂ)*(n+(a+1)+(b+1)+1))*p = 0) :
    C (2 : ℂ)*(jacobi (n+1) a b).derivative =
      C ((n : ℂ)+a+b+2)*jacobi n (a+1) (b+1) := by
  let p := jacobi n (a+1) (b+1)
  change q*p.derivative.derivative-A (a+1) (b+1)*p.derivative+_*p=0 at h
  have hd := congrArg derivative (step n a b)
  simp only [Ad,derivative_mul,derivative_sub,derivative_C,zero_mul,zero_add] at hd
  have ha : A (a+1) (b+1) = A a b+2*X := by simp [A,map_ofNat]; ring
  rw [ha] at h
  apply mul_left_cancel₀ (C_ne_zero.mpr (show (n : ℂ)+1 ≠ 0 by exact_mod_cast Nat.succ_ne_zero n))
  dsimp only [p] at h ⊢
  simp only [map_mul,map_add,map_ofNat,map_natCast,map_one,derivative_one,
    derivative_pow,derivative_X] at h hd ⊢
  linear_combination hd - h

/-- Jacobi's equation in polynomial form on the full complex plane. -/
theorem jacobi_equation (n : ℕ) (a b : ℂ) :
    let p := jacobi n a b
    (1-X^2)*p.derivative.derivative - (C (a-b)+C (a+b+2)*X)*p.derivative +
      C ((n : ℂ)*(n+a+b+1))*p = 0 := by
  induction n generalizing a b with
  | zero => simp [jacobi]
  | succ n ih =>
    have h := step_deriv n a b (ih (a+1) (b+1))
    have hd := congrArg derivative h
    simp only [derivative_mul,derivative_C,zero_mul,zero_add] at hd
    have hs := step n a b
    dsimp only
    change q*(jacobi (n+1) a b).derivative.derivative -
      A a b*(jacobi (n+1) a b).derivative+_*_=0
    have hd' := congrArg (fun f : ℂ[X] => q*f) hd
    have h' := congrArg (fun f : ℂ[X] => A a b*f) h
    apply mul_left_cancel₀ (by norm_num : (2 : ℂ[X]) ≠ 0)
    simp only [map_mul,map_add,map_ofNat,map_natCast,map_one,Nat.cast_succ] at hd' h' hs ⊢
    linear_combination hd' - h' + ((n : ℂ[X])+C a+C b+2)*hs

/-- Parameter shift of the Jacobi derivative. -/
theorem jacobi_derivative (n : ℕ) (a b : ℂ) :
    C (2 : ℂ)*(jacobi (n+1) a b).derivative =
      C ((n : ℂ)+a+b+2)*jacobi n (a+1) (b+1) :=
  step_deriv n a b (jacobi_equation n (a+1) (b+1))

/-- Jacobi's value at the right endpoint. -/
theorem jacobi_one (n : ℕ) (a b : ℂ) :
    (jacobi n a b).eval 1 = (ascPochhammer ℂ n).eval (a+1)/(n !) := by
  induction n generalizing a b with
  | zero => simp [jacobi]
  | succ n ih =>
    simp only [jacobi,eval_mul,eval_sub,eval_add,eval_C,eval_X,eval_one,eval_pow,
      one_pow,sub_self,zero_mul,sub_zero,mul_one,ih,ascPochhammer_succ_left,
      eval_comp,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
    field_simp
    ring

/-- Gegenbauer's ultraspherical polynomial Cₙˡ in the generating-function normalization. -/
def gegenbauer (l : ℂ) : ℕ → ℂ[X]
  | 0 => 1
  | n+1 =>
    let p := gegenbauer l n
    C (((n : ℂ)+1)⁻¹)*(C (n+2*l)*X*p-(1-X^2)*p.derivative)

private theorem raise (l : ℂ) (n : ℕ) :
    C ((n : ℂ)+1)*gegenbauer l (n+1) =
      C (n+2*l)*X*gegenbauer l n-q*(gegenbauer l n).derivative := by
  rw [gegenbauer,← mul_assoc,← C_mul,mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n),
    C_1,one_mul]

/-- Ultraspherical differential equation, for arbitrary complex parameter. -/
theorem gegenbauer_equation (l : ℂ) (n : ℕ) :
    let p := gegenbauer l n
    (1-X^2)*p.derivative.derivative-C (2*l+1)*X*p.derivative+C (n*(n+2*l))*p = 0 := by
  induction n with
  | zero => simp [gegenbauer]
  | succ n ih =>
    let p := gegenbauer l n
    let s := gegenbauer l (n+1)
    change q*p.derivative.derivative-_*X*p.derivative+_*p=0 at ih
    have hr := raise l n
    have hd := congrArg derivative hr
    change C ((n : ℂ)+1)*s = _*X*p-q*p.derivative at hr
    simp only [derivative_mul,derivative_C,zero_mul,zero_add,derivative_X,mul_one,
      derivative_sub] at hd
    have h : s.derivative = C (n+2*l)*p+X*p.derivative := by
      apply mul_left_cancel₀ (C_ne_zero.mpr
        (show (n : ℂ)+1 ≠ 0 by exact_mod_cast Nat.succ_ne_zero n))
      dsimp only [s,p] at ih ⊢
      simp only [map_mul,map_add,map_ofNat,map_natCast,map_one,derivative_one,
        derivative_pow,derivative_X] at ih hd ⊢
      linear_combination hd - ih
    have hh := congrArg derivative h
    simp only [derivative_add,derivative_mul,derivative_C,zero_mul,zero_add,derivative_X,
      one_mul] at hh
    change q*s.derivative.derivative-_*X*s.derivative+_*s=0
    rw [hh,h]
    simp [map_ofNat] at hr ih ⊢
    linear_combination X*ih + ((n : ℂ[X])+2*C l+1)*hr

/-- Endpoint normalization of the ultraspherical family. -/
theorem gegenbauer_one (l : ℂ) (n : ℕ) :
    (gegenbauer l n).eval 1 = (ascPochhammer ℂ n).eval (2*l)/(n !) := by
  induction n with
  | zero => simp [gegenbauer]
  | succ n ih =>
    simp [gegenbauer,ih,ascPochhammer_succ_eval,Nat.factorial_succ]
    field_simp
    ring

end ProjectAinos.SpecialFunctions.ClassicalPolynomial
