/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.CoulombRadiation
public import ProjectAinos.SpecialFunctions.HyperbolicTransform
public import ProjectAinos.SpecialFunctions.HankelUpper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-! # Hyperbolic anomaly of the scattering orbit in ED §70

In the anomaly u the Cartesian components are H+a cosh u and ρ sinh u. The time
satisfies v∞ t = H sinh u+a u for both signs of the Coulomb coupling.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set
open scoped Real Topology FourierTransform
namespace ProjectAinos.Electrodynamics.Radiation.CoulombRadiation
open Mechanics.Scattering Mechanics.Scattering.Coulomb Collision

/-- Time since closest approach in terms of the hyperbolic anomaly. -/
def hyperbolicTime (a ρ v u : ℝ) := (hyp a ρ*Real.sinh u+a*u)/v

private def D (a ρ u : ℝ) := hyp a ρ*Real.cosh u+a
private def X (a ρ u : ℝ) := hyp a ρ+a*Real.cosh u
private def Y (ρ u : ℝ) := ρ*Real.sinh u
private def angle (a ρ u : ℝ) := 2*Real.arctan (Y ρ u/(D a ρ u+X a ρ u))

private theorem d_pos (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) : 0 < D a ρ u := by
  have h := mul_le_mul_of_nonneg_left (Real.one_le_cosh u) (hyp_pos a hρ).le
  dsimp only [D]
  linarith [abs_lt_hyp a hρ, neg_abs_le a]

private theorem dx_pos (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) :
    0 < D a ρ u + X a ρ u := by
  have h : 0 < hyp a ρ+a := by linarith [abs_lt_hyp a hρ, neg_abs_le a]
  exact (mul_pos h (by positivity : 0 < 1+Real.cosh u)).trans_eq (by dsimp [D,X]; ring)

private theorem xy (a ρ u : ℝ) : X a ρ u^2 + Y ρ u^2 = D a ρ u^2 := by
  dsimp only [X,Y,D]
  linear_combination -(hyp a ρ)^2 * Real.cosh_sq_sub_sinh_sq u -
    Real.sinh u^2 * hyp_sq a ρ + a^2 * Real.cosh_sq_sub_sinh_sq u

private theorem half (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) :
    1+(Y ρ u/(D a ρ u+X a ρ u))^2 = 2*D a ρ u/(D a ρ u+X a ρ u) := by
  field_simp [(dx_pos a hρ u).ne']
  linear_combination xy a ρ u

private theorem cos_angle (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) :
    Real.cos (angle a ρ u) = X a ρ u/D a ρ u := by
  rw [angle, Real.cos_two_mul, Real.cos_sq_arctan, half a hρ]
  field_simp [(dx_pos a hρ u).ne', (d_pos a hρ u).ne']
  ring

private theorem sin_angle (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) :
    Real.sin (angle a ρ u) = Y ρ u/D a ρ u := by
  let p := Y ρ u/(D a ρ u+X a ρ u)
  have h : Real.sin (Real.arctan p) = p*Real.cos (Real.arctan p) := by
    rw [Real.sin_arctan, Real.cos_arctan]
    ring
  rw [angle, Real.sin_two_mul]
  change 2*Real.sin (Real.arctan p)*Real.cos (Real.arctan p) = _
  rw [h, show 2*(p*Real.cos (Real.arctan p))*Real.cos (Real.arctan p) =
    2*p*Real.cos (Real.arctan p)^2 by ring, Real.cos_sq_arctan]
  dsimp only [p]
  rw [half a hρ]
  field_simp [(dx_pos a hρ u).ne', (d_pos a hρ u).ne']

private theorem deriv_angle (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) :
    HasDerivAt (angle a ρ) (ρ/D a ρ u) u := by
  have hD := ((Real.hasDerivAt_cosh u).const_mul (hyp a ρ)).add_const a
  have hX := ((Real.hasDerivAt_cosh u).const_mul a).const_add (hyp a ρ)
  have hY := (Real.hasDerivAt_sinh u).const_mul ρ
  have h := (((hY.div (hD.add hX) (dx_pos a hρ u).ne').arctan).const_mul 2)
  apply h.congr_deriv
  change 2*(1/(1+(Y ρ u/(D a ρ u+X a ρ u))^2)*
    ((ρ*Real.cosh u*(D a ρ u+X a ρ u)-
    Y ρ u*(hyp a ρ*Real.sinh u+a*Real.sinh u))/(D a ρ u+X a ρ u)^2)) = _
  rw [half a hρ]
  field_simp [(dx_pos a hρ u).ne', (d_pos a hρ u).ne']
  dsimp [D,X,Y]
  linear_combination ρ*(hyp a ρ+a)*Real.cosh_sq_sub_sinh_sq u

private theorem conic (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) :
    hyp a ρ*Real.cos (angle a ρ u)-a=ρ^2/D a ρ u := by
  rw [cos_angle a hρ]
  field_simp [(d_pos a hρ u).ne']
  dsimp only [D,X]
  linear_combination hyp_sq a ρ

private theorem time_deriv (a ρ v u : ℝ) : HasDerivAt (hyperbolicTime a ρ v)
    (D a ρ u/v) u := by
  unfold hyperbolicTime D
  simpa only [mul_one, Pi.add_apply] using
    ((((Real.hasDerivAt_sinh u).const_mul (hyp a ρ)).add
      ((hasDerivAt_id' u).const_mul a)).div_const v)

private theorem time_angle (a : ℝ) {ρ v : ℝ} (hρ : 0 < ρ) (hv : 0 < v) (u : ℝ) :
    timeOfAngle a ρ v (angle a ρ u) = hyperbolicTime a ρ v u := by
  let φ := angle a ρ
  let g (p : ℝ) := ρ^4/(ρ*v*(hyp a ρ*Real.cos p-a)^2)
  have hd : Continuous (fun s => ρ/D a ρ s) := continuous_const.div
    ((continuous_const.mul Real.continuous_cosh).add continuous_const) (fun s => (d_pos a hρ s).ne')
  have hg : ContinuousOn g (φ '' uIcc 0 u) := by
    apply continuousOn_const.div
      ((continuous_const.mul
        (((continuous_const.mul Real.continuous_cos).sub continuous_const).pow 2)).continuousOn)
    rintro _ ⟨s,_,rfl⟩
    change ρ*v*(hyp a ρ*Real.cos (angle a ρ s)-a)^2 ≠ 0
    rw [conic a hρ]
    have := d_pos a hρ s
    positivity
  have h := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := u)
    (fun s _ => deriv_angle a hρ s) hd.continuousOn hg
  have hf (s : ℝ) : (g ∘ φ) s * (ρ/D a ρ s) = D a ρ s/v := by
    simp only [Function.comp_apply,g,φ,conic a hρ]
    field_simp [(d_pos a hρ s).ne',hρ.ne',hv.ne']
  have h0 : angle a ρ 0 = 0 := by simp [angle,Y]
  rw [h0] at h
  unfold timeOfAngle
  rw [← h]
  change (∫ s in 0..u, (g ∘ φ) s * (ρ/D a ρ s)) = _
  simp_rw [hf]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => time_deriv a ρ v t)
    (((continuous_const.mul Real.continuous_cosh).add continuous_const).div_const v
      |>.intervalIntegrable ..)]
  simp [hyperbolicTime]

private theorem angle_range (a : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) :
    angle a ρ u ∈ Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ) := by
  let p := Y ρ u/(D a ρ u+X a ρ u)
  have hπ : |angle a ρ u| ≤ π := by
    change |2*Real.arctan p| ≤ π
    rw [abs_le]
    constructor <;> linarith [Real.arctan_lt_pi_div_two p, Real.neg_pi_div_two_lt_arctan p]
  have he : Real.cos (asymptoteAngle a ρ) = a/hyp a ρ :=
    Real.cos_arccos (abs_le.mp (abs_div_hyp_lt_one a hρ).le).1
      (abs_le.mp (abs_div_hyp_lt_one a hρ).le).2
  have hcos : Real.cos (asymptoteAngle a ρ) < Real.cos |angle a ρ u| := by
    rw [he, Real.cos_abs, div_lt_iff₀ (hyp_pos a hρ)]
    linarith [conic a hρ u, div_pos (sq_pos_of_pos hρ) (d_pos a hρ u)]
  have hlt := (Real.strictAntiOn_cos.lt_iff_gt
    (show asymptoteAngle a ρ ∈ Icc 0 π from ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩)
    ⟨abs_nonneg _,hπ⟩).mp hcos
  exact abs_lt.mp hlt

/-- Radius and direction of the library's scattering solution at the hyperbolic time T(u). -/
theorem hyperbolic_orbit (a : ℝ) {ρ v : ℝ} (hρ : 0 < ρ) (hv : 0 < v) (u : ℝ) :
    let t := hyperbolicTime a ρ v u
    let r := hyp a ρ*Real.cosh u+a
    orbitRadius a ρ v t = r ∧
      Real.cos (orbitAngle a ρ v t) = (hyp a ρ+a*Real.cosh u)/r ∧
      Real.sin (orbitAngle a ρ v t) = ρ*Real.sinh u/r := by
  have hr := angle_range a hρ u
  rw [← range_orbitAngle hρ hv] at hr
  obtain ⟨t,ht⟩ := hr
  have h := time_angle a hρ hv u
  rw [← ht, timeOfAngle_orbitAngle hρ hv] at h
  dsimp only
  rw [← h, ht, cos_angle a hρ, sin_angle a hρ]
  refine ⟨?_,rfl,rfl⟩
  have h' := conic a hρ u
  rw [← ht, cos_orbitAngle hρ hv] at h'
  have hD := (d_pos a hρ u).ne'
  have hR := (orbitRadius_pos (a := a) hρ v t).ne'
  field_simp [hD,hR] at h'
  change _ = D a ρ u
  nlinarith [sq_pos_of_pos hρ]

private theorem time_surj (a : ℝ) {ρ v : ℝ} (hρ : 0 < ρ) (hv : 0 < v) :
    Function.Surjective (hyperbolicTime a ρ v) := by
  have hH := hyp_pos a hρ
  have hs : 0 < (hyp a ρ+a)/v := div_pos (by linarith [abs_lt_hyp a hρ, neg_abs_le a]) hv
  have ht : Tendsto (hyperbolicTime a ρ v) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (tendsto_id.const_mul_atTop hs)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    change (hyp a ρ+a)/v*t ≤ (hyp a ρ*Real.sinh t+a*t)/v
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr ht) hH.le]
  apply (show Continuous (hyperbolicTime a ρ v) from
    continuous_iff_continuousAt.mpr fun u => (time_deriv a ρ v u).continuousAt).surjective ht
  exact (tendsto_neg_atTop_atBot.comp (ht.comp tendsto_neg_atBot_atTop)).congr fun u => by
    simp [hyperbolicTime]
    ring

private theorem time_mono (a : ℝ) {ρ v : ℝ} (hρ : 0 < ρ) (hv : 0 < v) :
    StrictMono (hyperbolicTime a ρ v) := strictMono_of_deriv_pos fun u => by
  rw [(time_deriv a ρ v u).deriv]
  exact div_pos (d_pos a hρ u) hv

private theorem transform_anomaly (p : Bool) (e a : ℝ) {ρ v ν : ℝ}
    (hρ : 0 < ρ) (hv : 0 < v) (hν : 0 < ν) :
    let ω := 2*π*ν
    let k := ω*hyp a ρ/v
    let η := ω*a/v
    𝓕 (fun t => ((if p then (e • acceleration a ρ v t).1 else
      (e • acceleration a ρ v t).2 : ℝ) : ℂ)) ν =
      ((e*ω*(if p then a else ρ) : ℝ) : ℂ) *
        ∫ u : ℝ, SpecialFunctions.Bessel.scatteringKernel p k η u := by
  let T := hyperbolicTime a ρ v
  let ω := 2*π*ν
  let k := ω*hyp a ρ/v
  let η := ω*a/v
  have hω : 0 < ω := by dsimp [ω]; positivity
  have hf (f : ℝ → ℂ) : (∫ t : ℝ, f t) = ∫ u : ℝ, (D a ρ u/v) • f (T u) := by
    have h := integral_image_eq_integral_abs_deriv_smul (f := T) (f' := fun u => D a ρ u/v)
      MeasurableSet.univ (fun u _ => (time_deriv a ρ v u).hasDerivWithinAt)
      (time_mono a hρ hv).injective.injOn f
    rw [image_univ, (time_surj a hρ hv).range_eq, Measure.restrict_univ] at h
    simpa only [abs_of_pos (div_pos (d_pos a hρ _) hv)] using h
  dsimp only
  rw [Real.fourier_real_eq_integral_exp_smul, hf, ← integral_const_mul]
  congr 1
  funext u
  obtain ⟨hR,hc,hs⟩ := hyperbolic_orbit a hρ hv u
  change orbitRadius a ρ v (T u) = D a ρ u at hR
  change Real.cos (orbitAngle a ρ v (T u)) = X a ρ u/D a ρ u at hc
  change Real.sin (orbitAngle a ρ v (T u)) = Y ρ u/D a ρ u at hs
  have he : -2*π*T u*ν = -(k*Real.sinh u+η*u) := by dsimp [T,hyperbolicTime,k,η,ω]; ring
  have hden : k*Real.cosh u+η = ω/v*D a ρ u := by dsimp [k,η,D]; ring
  have hk : k+η*Real.cosh u = ω/v*X a ρ u := by dsimp [k,η,X]; ring
  have hη : η*Real.sinh u = ω*a/v*Real.sinh u := rfl
  change _ = ((e*ω*(if p then a else ρ) : ℝ) : ℂ) * SpecialFunctions.Bessel.scatteringKernel p k η u
  simp only [SpecialFunctions.Bessel.scatteringKernel, fst_smul_acceleration,
    snd_smul_acceleration,hR,hc,hs,Complex.real_smul,smul_eq_mul,he,hden,hk,hη]
  have hD := (d_pos a hρ u).ne'
  cases p <;> simp only [Bool.false_eq_true,↓reduceIte] <;> push_cast <;>
    field_simp [Complex.ofReal_ne_zero.mpr hD,Complex.ofReal_ne_zero.mpr hv.ne',
      Complex.ofReal_ne_zero.mpr hω.ne']
  dsimp only [Y]
  push_cast
  ring

/-- Both velocity-change Fourier components, in terms of K and K′ at imaginary order.
Here ω is the angular frequency and k and η are dimensionless. -/
theorem hyperbolic_harmonics (e a : ℝ) {ρ v ν : ℝ} (hρ : 0 < ρ) (hv : 0 < v)
    (hν : 0 < ν) :
    let ω := 2*π*ν
    let k := ω*hyp a ρ/v
    let η := ω*a/v
    let b := -(η : ℂ)*Complex.I
    let A := 2*e*ω*a*Real.exp (-η*(π/2))
    𝓕 (fun t => ((e • acceleration a ρ v t).1 : ℂ)) ν =
        -(A : ℂ)*deriv (SpecialFunctions.Bessel.macdonald b) k ∧
      𝓕 (fun t => ((e • acceleration a ρ v t).2 : ℂ)) ν =
        -Complex.I*A*(ρ/hyp a ρ : ℝ)*SpecialFunctions.Bessel.macdonald b k := by
  let ω := 2*π*ν
  let k := ω*hyp a ρ/v
  let η := ω*a/v
  have hω : 0 < ω := by dsimp [ω]; positivity
  have hk : |η| < k := by
    dsimp only [η,k]
    rw [abs_div,abs_of_pos hv,abs_mul,abs_of_pos hω]
    gcongr
    exact abs_lt_hyp _ hρ
  have h (p : Bool) := transform_anomaly p e a hρ hv hν
  have hT := SpecialFunctions.Bessel.scattering_transform (k := k) (η := η)
  have h₁ := h true
  have h₂ := h false
  dsimp only [Bool.false_eq_true,↓reduceIte] at h₁ h₂ ⊢
  change _ = _*∫ u : ℝ, SpecialFunctions.Bessel.scatteringKernel true k η u at h₁
  change _ = _*∫ u : ℝ, SpecialFunctions.Bessel.scatteringKernel false k η u at h₂
  rw [hT true hk] at h₁
  rw [hT false hk] at h₂
  simp only [Bool.false_eq_true, ↓reduceIte] at h₁ h₂
  constructor
  · rw [h₁]
    dsimp only [k,η,ω]
    push_cast
    ring
  · rw [h₂]
    dsimp only [k,η,ω]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hv.ne', Complex.ofReal_ne_zero.mpr (hyp_pos a hρ).ne',
      Real.pi_ne_zero, Complex.ofReal_ne_zero.mpr hν.ne']

/-- The spectral density of the hyperbolic collision at each positive frequency, including
both signs and zero value of the interaction strength a. -/
theorem spectrum_hyperbolic_macdonald (e a : ℝ) {ρ v ν : ℝ} (hρ : 0 < ρ) (hv : 0 < v)
    (hν : 0 < ν) :
    let ω := 2*π*ν
    let k := ω*hyp a ρ/v
    let η := ω*a/v
    let b := -(η : ℂ)*Complex.I
    spectralDensity (fun t => e • acceleration a ρ v t) ν =
      2/3*(4*π)⁻¹*(2*e*ω*a*Real.exp (-η*(π/2)))^2 *
      (‖deriv (SpecialFunctions.Bessel.macdonald b) k‖^2 +
        (ρ/hyp a ρ)^2*‖SpecialFunctions.Bessel.macdonald b k‖^2) := by
  obtain ⟨hx,hy⟩ := hyperbolic_harmonics e a hρ hv hν
  rw [spectralDensity,hx,hy]
  dsimp only
  simp only [norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    mul_pow,sq_abs,norm_div,div_pow]
  ring

/-- Hankel form of the Coulomb collision spectrum at imaginary order and argument. -/
theorem spectrum_hyperbolic_hankel (e a : ℝ) {ρ v ν : ℝ} (hρ : 0 < ρ) (hv : 0 < v)
    (hν : 0 < ν) :
    let ω := 2*π*ν
    let η := ω*a/v
    let b := -(η : ℂ)*Complex.I
    let z := Complex.I*(ω*hyp a ρ/v : ℝ)
    spectralDensity (fun t => e • acceleration a ρ v t) ν =
      2/3*(4*π)⁻¹*(π*e*ω*a)^2 *
      (‖deriv (SpecialFunctions.Bessel.hankelFirstUpper b) z‖^2 +
        (ρ/hyp a ρ)^2*‖SpecialFunctions.Bessel.hankelFirstUpper b z‖^2) := by
  let ω := 2*π*ν
  let k := ω*hyp a ρ/v
  let η := ω*a/v
  have hk : 0 < k := by dsimp [k,ω]; positivity [hyp_pos a hρ]
  obtain ⟨hx,hy⟩ := SpecialFunctions.Bessel.hankel_imaginary η hk
  rw [spectrum_hyperbolic_macdonald e a hρ hv hν]
  dsimp only
  rw [hx,hy]
  simp only [norm_mul,norm_neg,norm_div,Complex.norm_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,abs_of_pos (Real.exp_pos _)]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
  dsimp only [k,η,ω]
  field_simp

/-- At zero frequency the net transverse impulse vanishes and the longitudinal
impulse is 2eva/H, for either sign of a. -/
theorem hyperbolic_zero (e a : ℝ) {ρ v : ℝ} (hρ : 0 < ρ) (hv : 0 < v) :
    𝓕 (fun t => ((e • acceleration a ρ v t).1 : ℂ)) 0 = (2*e*v*a/hyp a ρ : ℝ) ∧
      𝓕 (fun t => ((e • acceleration a ρ v t).2 : ℂ)) 0 = 0 := by
  let φ := asymptoteAngle a ρ
  have hφ : 0 ≤ φ := Real.arccos_nonneg _
  have hc : Real.sin φ = ρ/hyp a ρ := by
    rw [show φ = Real.arccos (a/hyp a ρ) by rfl,Real.sin_arccos]
    have hh := hyp_sq a ρ
    have hp := hyp_pos a hρ
    rw [← Real.sqrt_sq (show 0 ≤ ρ/hyp a ρ by positivity)]
    congr 1
    field_simp
    nlinarith
  rw [fourier_acceleration_fst e a hρ hv, fourier_acceleration_snd e a hρ hv]
  simp only [mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul]
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show -φ ≤ φ by linarith),
    ← intervalIntegral.integral_of_le (show -φ ≤ φ by linarith),
    intervalIntegral.integral_ofReal,intervalIntegral.integral_ofReal,integral_cos,integral_sin]
  simp only [Real.cos_neg,Real.sin_neg,hc,sub_self,Complex.ofReal_zero,mul_zero,and_true]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hρ.ne',Complex.ofReal_ne_zero.mpr (hyp_pos a hρ).ne']
  ring

end ProjectAinos.Electrodynamics.Radiation.CoulombRadiation
