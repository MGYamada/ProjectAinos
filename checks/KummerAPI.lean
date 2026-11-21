/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.Kummer

noncomputable section
open Complex Polynomial ProjectAinos.SpecialFunctions.Kummer
open scoped Nat

example : ℂ → ℂ → ℂ → ℂ := M
example : ℕ → ℂ → ℕ → ℂ := laguerreCoeff
example : ℕ → ℂ → ℂ[X] := laguerre

example (a b z : ℂ) :
    HasSum (fun n : ℕ => Gamma b*z^n*regularizedHGFunCoeff {a} {b} n) (M a b z) :=
  hasSum_M a b z

example (a b : ℂ) (hb : ∀ n : ℕ, b ≠ -n) : M a b 0 = 1 :=
  M_zero a b hb

example (a b z : ℂ) : HasDerivAt (M a b)
    (Gamma b*(a*regularizedHGFun {a+1} {b+1} z)) z :=
  hasDerivAt_M a b z

example (a b z : ℂ) :
    z*deriv (deriv (M a b)) z+(b-z)*deriv (M a b) z = a*M a b z :=
  equation a b z

example (n : ℕ) (α z : ℂ) (hb : ∀ m : ℕ, α+1 ≠ -m) :
    (laguerre n α).eval z = (ascPochhammer ℂ n).eval (α+1)/(n !) * M (-n) (α+1) z :=
  laguerre_eval n α z hb

example (n j : ℕ) (α : ℂ) :
    (laguerre n α).coeff j = laguerreCoeff n α j :=
  coeff_laguerre_polynomial n j α

example (n : ℕ) (α : ℂ) :
    let p := laguerre n α
    X*p.derivative.derivative+(C (α+1)-X)*p.derivative+C (n : ℂ)*p = 0 :=
  laguerre_equation n α

example (n : ℕ) (α : ℂ) :
    (laguerre n α).eval 0 = (ascPochhammer ℂ n).eval (α+1)/(n !) :=
  laguerre_zero n α
