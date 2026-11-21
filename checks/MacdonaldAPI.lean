/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.HyperbolicTransform
import ProjectAinos.SpecialFunctions.HankelUpper

noncomputable section
open Complex MeasureTheory
open scoped Real
open ProjectAinos.SpecialFunctions.Bessel

example : Bool → ℝ → ℝ → ℝ → ℂ := scatteringKernel

example (p : Bool) {k η : ℝ} (hk : |η| < k) :
    let a := -(η : ℂ)*I
    (∫ u : ℝ, scatteringKernel p k η u) = if p then
      -2*(Real.exp (-η*(π/2)) : ℝ)*deriv (macdonald a) k
      else 2*(Real.exp (-η*(π/2)) : ℝ)*a/k*macdonald a k :=
  scattering_transform p hk

example (a z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => exp (-z * Real.sinh t + a * t)) (Set.Ioi 0) :=
  Schlaefli.integrable_ray a z hz

example : ℂ → ℂ → ℂ := hankelFirstUpper

example (a z : ℂ) (hr : 0 < z.re) (hi : 0 < z.im) :
    hankelFirstUpper a z = hankelFirst a z :=
  hankelFirstUpper_eq a z hr hi

example (a z : ℂ) (hi : 0 < z.im) :
    deriv (hankelFirstUpper a) z =
      -2/π * exp (-(a*(π/2))*I) * deriv (macdonald a) (-I*z) :=
  deriv_hankelFirstUpper a z hi

example (η : ℝ) {k : ℝ} (hk : 0 < k) :
    let a := -(η : ℂ)*I
    let d := (Real.exp (-η*(π/2)) : ℂ)
    hankelFirstUpper a (I*k) = -2*I/π*d*macdonald a k ∧
      deriv (hankelFirstUpper a) (I*k) = -2/π*d*deriv (macdonald a) k :=
  hankel_imaginary η hk
