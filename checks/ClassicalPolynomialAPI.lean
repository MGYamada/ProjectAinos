/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.ClassicalPolynomial

noncomputable section
open Polynomial ProjectAinos.SpecialFunctions.ClassicalPolynomial
open scoped Nat

example : ℕ → ℂ → ℂ → ℂ[X] := jacobi
example : ℂ → ℕ → ℂ[X] := gegenbauer

example (n : ℕ) (a b : ℂ) :
    let p := jacobi n a b
    (1-X^2)*p.derivative.derivative - (C (a-b)+C (a+b+2)*X)*p.derivative +
      C ((n : ℂ)*(n+a+b+1))*p = 0 :=
  jacobi_equation n a b

example (n : ℕ) (a b : ℂ) :
    C (2 : ℂ)*(jacobi (n+1) a b).derivative =
      C ((n : ℂ)+a+b+2)*jacobi n (a+1) (b+1) :=
  jacobi_derivative n a b

example (n : ℕ) (a b : ℂ) :
    (jacobi n a b).eval 1 = (ascPochhammer ℂ n).eval (a+1)/(n !) :=
  jacobi_one n a b

example (l : ℂ) (n : ℕ) :
    let p := gegenbauer l n
    (1-X^2)*p.derivative.derivative-C (2*l+1)*X*p.derivative+C (n*(n+2*l))*p = 0 :=
  gegenbauer_equation l n

example (l : ℂ) (n : ℕ) :
    (gegenbauer l n).eval 1 = (ascPochhammer ℂ n).eval (2*l)/(n !) :=
  gegenbauer_one l n
