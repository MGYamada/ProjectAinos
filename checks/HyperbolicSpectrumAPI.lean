/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.Electrodynamics.Radiation.HyperbolicSpectrum

noncomputable section
open Filter MeasureTheory Set
open scoped Real Topology FourierTransform
namespace ProjectAinos.Electrodynamics.Radiation.CoulombRadiation
open Mechanics.Scattering Mechanics.Scattering.Coulomb Collision

example : ℝ → ℝ → ℝ → ℝ → ℝ := hyperbolicTime

example (a : ℝ) {ρ v : ℝ} (hρ : 0 < ρ) (hv : 0 < v) (u : ℝ) :
    let t := hyperbolicTime a ρ v u
    let r := hyp a ρ*Real.cosh u+a
    orbitRadius a ρ v t = r ∧
      Real.cos (orbitAngle a ρ v t) = (hyp a ρ+a*Real.cosh u)/r ∧
      Real.sin (orbitAngle a ρ v t) = ρ*Real.sinh u/r :=
  hyperbolic_orbit a hρ hv u

example (e a : ℝ) {ρ v ν : ℝ} (hρ : 0 < ρ) (hv : 0 < v)
    (hν : 0 < ν) :
    let ω := 2*π*ν
    let k := ω*hyp a ρ/v
    let η := ω*a/v
    let b := -(η : ℂ)*Complex.I
    let A := 2*e*ω*a*Real.exp (-η*(π/2))
    𝓕 (fun t => ((e • acceleration a ρ v t).1 : ℂ)) ν =
        -(A : ℂ)*deriv (SpecialFunctions.Bessel.macdonald b) k ∧
      𝓕 (fun t => ((e • acceleration a ρ v t).2 : ℂ)) ν =
        -Complex.I*A*(ρ/hyp a ρ : ℝ)*SpecialFunctions.Bessel.macdonald b k :=
  hyperbolic_harmonics e a hρ hv hν

example (e a : ℝ) {ρ v ν : ℝ} (hρ : 0 < ρ) (hv : 0 < v)
    (hν : 0 < ν) :
    let ω := 2*π*ν
    let k := ω*hyp a ρ/v
    let η := ω*a/v
    let b := -(η : ℂ)*Complex.I
    spectralDensity (fun t => e • acceleration a ρ v t) ν =
      2/3*(4*π)⁻¹*(2*e*ω*a*Real.exp (-η*(π/2)))^2 *
      (‖deriv (SpecialFunctions.Bessel.macdonald b) k‖^2 +
        (ρ/hyp a ρ)^2*‖SpecialFunctions.Bessel.macdonald b k‖^2) :=
  spectrum_hyperbolic_macdonald e a hρ hv hν

example (e a : ℝ) {ρ v : ℝ} (hρ : 0 < ρ) (hv : 0 < v) :
    𝓕 (fun t => ((e • acceleration a ρ v t).1 : ℂ)) 0 = (2*e*v*a/hyp a ρ : ℝ) ∧
      𝓕 (fun t => ((e • acceleration a ρ v t).2 : ℂ)) 0 = 0 :=
  hyperbolic_zero e a hρ hv

example (e a : ℝ) {ρ v ν : ℝ} (hρ : 0 < ρ) (hv : 0 < v)
    (hν : 0 < ν) :
    let ω := 2*π*ν
    let η := ω*a/v
    let b := -(η : ℂ)*Complex.I
    let z := Complex.I*(ω*hyp a ρ/v : ℝ)
    spectralDensity (fun t => e • acceleration a ρ v t) ν =
      2/3*(4*π)⁻¹*(π*e*ω*a)^2 *
      (‖deriv (SpecialFunctions.Bessel.hankelFirstUpper b) z‖^2 +
        (ρ/hyp a ρ)^2*‖SpecialFunctions.Bessel.hankelFirstUpper b z‖^2) :=
  spectrum_hyperbolic_hankel e a hρ hv hν

end ProjectAinos.Electrodynamics.Radiation.CoulombRadiation
