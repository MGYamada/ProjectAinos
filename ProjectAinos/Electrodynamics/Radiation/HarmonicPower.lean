/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.CircularHarmonics
public import ProjectAinos.SpecialFunctions.BesselSquare
import Mathlib.Tactic

/-! # Angular and angle-integrated power of circular radiation harmonics

A positive Fourier line of a real field collects its positive and negative frequencies.
The two transverse powers are independent of azimuth. Their integral over solid angle
is expressed through the Bessel function and its derivative at twice the harmonic order.
-/

@[expose] public section
noncomputable section
open Complex MeasureTheory
open scoped Real
namespace ProjectAinos.Electrodynamics.Radiation.Synchrotron
open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity SubluminalWorldline
open SpecialFunctions.Bessel

/-- Power per unit solid angle in the pair of frequencies ±mΩ, in the transverse basis
of the meridian α. -/
def linePower (e α R Ω c q : ℝ) (hs : |R*Ω| < 1) (m : ℕ) : ℝ :=
  let w := circular R Ω hs
  let n := viewingAt α c q
  2*(‖observedHarmonic e w n (radialAxis α) Ω m‖^2 +
    ‖observedHarmonic e w n (meridianAt α c q) Ω m‖^2)

private theorem real_bessel (k : ℤ) (x : ℝ) : ((besselJ k x).re : ℂ) = besselJ k x := by
  rw [integral k x, ofReal_re]

/-- Angular power of a nonzero harmonic, with its azimuthal independence explicit. -/
theorem linePower_eq (e α : ℝ) {R Ω c q : ℝ} (hs : |R*Ω| < 1) (hΩ : Ω ≠ 0)
    (hu : c^2+q^2 = 1) (m : ℕ) :
    let j := m+1
    let x := (j : ℝ)*(R*Ω*c)
    (linePower e α R Ω c q hs j : ℂ) = 2*(e*Ω*j/(4*π) : ℝ)^2 *
      (((R*Ω : ℝ) : ℂ)^2/2*(besselJ m x^2 + besselJ (m+2 : ℕ) x^2) - besselJ j x^2) := by
  let j : ℤ := (m : ℤ)+1
  have hj : j ≠ 0 := by dsimp [j]; omega
  let x := (j : ℝ)*(R*Ω*c)
  let A := (besselJ (j-1 : ℤ) x).re
  let B := (besselJ (j+1 : ℤ) x).re
  let D := (besselJ j x).re
  have ha : besselJ (j-1 : ℤ) x = (A : ℂ) := (real_bessel _ _).symm
  have hb : besselJ (j+1 : ℤ) x = (B : ℂ) := (real_bessel _ _).symm
  have hd : besselJ j x = (D : ℂ) := (real_bessel _ _).symm
  have hder := twice_deriv_int j x
  rw [ha, hb] at hder
  have hder' : deriv (besselJ j) x = ((A-B)/2 : ℝ) := by push_cast; linear_combination hder/2
  have hrec := recurrence_int j x
  rw [ha, hb, hd] at hrec
  have hr : x*(A+B) = 2*j*D := by exact_mod_cast hrec
  have hD : D = R*Ω*c*(A+B)/2 := by
    dsimp only [x] at hr
    apply mul_left_cancel₀ (Int.cast_ne_zero.mpr hj : (j : ℝ) ≠ 0)
    linarith only [hr]
  obtain ⟨h₁,h₂⟩ := circular_harmonics_at e α hs hΩ hu j hj
  change _ = _ * (_ * deriv (besselJ j) x) at h₁
  change _ = _ * (_ * (besselJ (j-1 : ℤ) x + besselJ (j+1 : ℤ) x)) at h₂
  rw [hder'] at h₁
  rw [ha, hb] at h₂
  let F : ℝ := e*Ω*j/(4*π)
  have hN : ‖cexp (-((j : ℂ)*α)*I)‖ = 1 := by simp [norm_exp]
  have he₁ : (e*Ω^2*R*j/(4*π) : ℂ) * (((A-B)/2 : ℝ) : ℂ) =
      ((F*(R*Ω)*(A-B)/2 : ℝ) : ℂ) := by dsimp [F]; push_cast; ring
  have he₂ : (e*Ω^2*R*q*j/(8*π*I) : ℂ) * ((A : ℂ)+B) =
      ((F*(R*Ω)*q*(A+B)/2 : ℝ) : ℂ)/I := by dsimp [F]; push_cast; ring
  have hp : linePower e α R Ω c q hs (m+1) =
      2*((F*(R*Ω)*(A-B)/2)^2 + (F*(R*Ω)*q*(A+B)/2)^2) := by
    change 2*(‖observedHarmonic _ _ _ _ _ j‖^2+‖observedHarmonic _ _ _ _ _ j‖^2) = _
    rw [h₁,h₂,he₁,he₂]
    simp only [norm_mul, hN, one_mul, norm_div, norm_I, div_one, norm_real, Real.norm_eq_abs,
      mul_pow, div_pow, sq_abs]
  have eqr : 2*((F*(R*Ω)*(A-B)/2)^2 + (F*(R*Ω)*q*(A+B)/2)^2) =
      2*F^2*((R*Ω)^2/2*(A^2+B^2)-D^2) := by
    rw [hD]
    linear_combination (F*(R*Ω)*(A+B))^2/2 * hu
  have hm : (j-1 : ℤ) = (m : ℤ) := by dsimp [j]; omega
  have hm' : (j+1 : ℤ) = ((m+2 : ℕ) : ℤ) := by dsimp [j]; omega
  dsimp only
  rw [hp, eqr]
  dsimp only [F]
  rw [hm, Int.cast_natCast] at ha
  rw [hm', Int.cast_natCast] at hb
  have hj' : j = ((m+1 : ℕ) : ℤ) := by simp [j]
  rw [hj', Int.cast_natCast] at hd
  dsimp only [x] at ha hb hd
  simp only [hj', Int.cast_natCast] at ha hb hd ⊢
  rw [ha, hb, hd]
  push_cast
  ring

/-- Integral of a harmonic's power over all observing directions in polar coordinates. -/
def harmonicPower (e R Ω : ℝ) (hs : |R*Ω| < 1) (m : ℕ) : ℝ :=
  ∫ θ in 0..π, Real.sin θ *
    ∫ α in 0..2*π, linePower e α R Ω (Real.sin θ) (Real.cos θ) hs m

/-- The angle-integrated synchrotron line involves J₂ⱼ and its argument derivative.
The formula uses j = m+1 and z = jβ, with β = RΩ in units of light speed. -/
theorem harmonicPower_eq (e : ℝ) {R Ω : ℝ} (hs : |R*Ω| < 1) (hΩ : Ω ≠ 0) (m : ℕ) :
    let j := m+1
    let β := R*Ω
    let z := (j : ℝ)*β
    let F := e*Ω*j/(4*π)
    (z : ℂ) * harmonicPower e R Ω hs j = 4*π*(F : ℂ)^2 *
      (2*(β : ℂ)^2 * deriv (besselJ (2*j : ℕ)) (2*z) +
        2*z*((β : ℂ)^2-1)*∫ t in (0 : ℝ)..1, besselJ (2*j : ℕ) (2*z*t)) := by
  let j := m+1
  let β := R*Ω
  let z : ℝ := j*β
  let F : ℝ := e*Ω*j/(4*π)
  let g (θ : ℝ) := (β : ℂ)^2/2 *
    (besselJ m (z*Real.sin θ)^2 + besselJ (m+2 : ℕ) (z*Real.sin θ)^2) -
    besselJ j (z*Real.sin θ)^2
  have hp (θ α : ℝ) : (linePower e α R Ω (Real.sin θ) (Real.cos θ) hs j : ℂ) =
      2*(F : ℂ)^2*g θ := by
    have H := linePower_eq e α hs hΩ (Real.sin_sq_add_cos_sq θ) m
    dsimp only at H
    dsimp only [F, g, z, β, j]
    simpa only [← mul_assoc, ofReal_mul, ofReal_pow] using H
  have ht (θ : ℝ) : ((Real.sin θ * ∫ α in 0..2*π,
      linePower e α R Ω (Real.sin θ) (Real.cos θ) hs j : ℝ) : ℂ) =
      4*π*(F : ℂ)^2*((Real.sin θ : ℂ)*g θ) := by
    rw [ofReal_mul, ← intervalIntegral.integral_ofReal]
    simp_rw [hp]
    rw [intervalIntegral.integral_const, sub_zero, real_smul]
    push_cast
    ring
  dsimp only
  change (z : ℂ)*((∫ θ in 0..π, _ : ℝ) : ℂ) = _
  rw [← intervalIntegral.integral_ofReal]
  change (z : ℂ)*(∫ θ in 0..π, ((Real.sin θ * ∫ α in 0..2*π,
    linePower e α R Ω (Real.sin θ) (Real.cos θ) hs j : ℝ) : ℂ)) = _
  simp_rw [ht, intervalIntegral.integral_const_mul]
  have h := integral_angular_combination m (β : ℂ) (z : ℂ)
  change (z : ℂ)*(∫ θ in 0..π, (Real.sin θ : ℂ)*g θ) = _ at h
  rw [← mul_assoc, mul_comm (z : ℂ), mul_assoc, h]

end ProjectAinos.Electrodynamics.Radiation.Synchrotron
