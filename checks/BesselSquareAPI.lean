/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SpecialFunctions.BesselSquare

noncomputable section
open Complex MeasureTheory
open scoped Real
open ProjectAinos.SpecialFunctions.Bessel

example (m : ℕ) (z : ℂ) :
    (∫ θ in 0..π, (Real.sin θ : ℂ) * besselJ m (z*Real.sin θ)^2) =
      2 * ∫ t in (0 : ℝ)..1, besselJ (2*m : ℕ) (2*z*t) :=
  integral_sin_bessel_sq m z

example (m : ℕ) (b z : ℂ) :
    z * (∫ θ in 0..π, (Real.sin θ : ℂ) *
      (b^2/2*(besselJ m (z*Real.sin θ)^2 + besselJ (m+2 : ℕ) (z*Real.sin θ)^2) -
        besselJ (m+1 : ℕ) (z*Real.sin θ)^2)) =
      2*b^2*deriv (besselJ (2*(m+1) : ℕ)) (2*z) +
        2*z*(b^2-1)*∫ t in (0 : ℝ)..1, besselJ (2*(m+1) : ℕ) (2*z*t) :=
  integral_angular_combination m b z
