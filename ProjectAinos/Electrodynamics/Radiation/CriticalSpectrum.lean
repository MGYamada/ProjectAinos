/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.HarmonicPower
public import ProjectAinos.SpecialFunctions.BesselTurningIntegral
public import ProjectAinos.SpecialFunctions.AiryMacdonald
import Mathlib.Tactic

/-! # The synchrotron spectrum in the critical frequency and angle range

The large-order limit of both transverse components holds for moving speeds and inclinations.
In units r = (n/2)^(1/3), bounded r/γ selects n = O(γ³), and bounded r q selects the
angular layer about the plane of the orbit. These physical bounds control the Airy argument.
-/

@[expose] public section
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Real Topology
namespace ProjectAinos.Electrodynamics.Radiation.Synchrotron
open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity SubluminalWorldline
open SpecialFunctions.Bessel SpecialFunctions.Airy

/-- Airy argument for the nth harmonic at tangential viewing component c and speed β. -/
def detuning (n : ℕ) (β c : ℝ) : ℝ := 2 * turningScale n ^ 2 * (1-β*c)

/-- The critical frequency variable satisfies n/γ³ = 2(r/γ)³. -/
theorem critical_frequency (n : ℕ) (R Ω : ℝ) :
    (n : ℝ) / gamma R Ω ^ 3 = 2 * (turningScale n / gamma R Ω)^3 := by
  rw [turningScale_cube n, div_pow]
  ring

/-- Two transverse observed field coefficients after multiplication by 4πr²/(nΩ). -/
def scaledHarmonics (e R Ω c q : ℝ) (hs : |R*Ω| < 1) (n : ℕ) : ℂ × ℂ :=
  let p : ℂ := 4*π*(turningScale n : ℂ)^2/(Ω*n)
  let w := circular R Ω hs
  let v := viewingDirection c q
  (p * observedHarmonic e w v (EuclideanSpace.single 0 1) Ω n,
    p * observedHarmonic e w v (meridianPolarization c q) Ω n)

private theorem scale_components (e : ℝ) {R Ω c q : ℝ} (hs : |R*Ω| < 1) (hΩ : Ω ≠ 0)
    (hu : c^2+q^2 = 1) (hc : c ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    let r := turningScale n
    let x := (n : ℝ)*(R*Ω*c)
    scaledHarmonics e R Ω c q hs n =
      ((e*(R*Ω) : ℝ) * ((r : ℂ)^2*deriv (besselJ n) x),
        ((e*r*q/c : ℝ) : ℂ)/I * ((r : ℂ)*besselJ n x)) := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  obtain ⟨ha,hb⟩ := circular_harmonics e hs hΩ hu (n : ℤ) hn'
  dsimp only at ha hb ⊢
  simp only [Int.cast_natCast] at ha hb
  let x := (n : ℝ)*(R*Ω*c)
  have h := recurrence_int (n : ℤ) (x : ℂ)
  simp only [Int.cast_natCast] at h
  dsimp only [x] at h
  push_cast at h
  have hd : (R*Ω*c : ℂ)*(besselJ ((n : ℂ)-1) (n*(R*Ω*c)) +
      besselJ ((n : ℂ)+1) (n*(R*Ω*c))) = 2*besselJ n (n*(R*Ω*c)) := by
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn : (n : ℂ) ≠ 0)
    linear_combination h
  rw [scaledHarmonics, ha, hb]
  push_cast
  apply Prod.ext
  · dsimp only
    field_simp [Nat.cast_ne_zero.mpr hn, ofReal_ne_zero.mpr hΩ, Real.pi_ne_zero]
  · dsimp only
    generalize besselJ ((n : ℂ)-1) (n*(R*Ω*c)) = A at hd ⊢
    generalize besselJ ((n : ℂ)+1) (n*(R*Ω*c)) = B at hd ⊢
    generalize besselJ n (n*(R*Ω*c)) = D at hd ⊢
    field_simp [Nat.cast_ne_zero.mpr hn, ofReal_ne_zero.mpr hΩ, Real.pi_ne_zero,
      ofReal_ne_zero.mpr hc, I_ne_zero]
    linear_combination 4*(e : ℂ)*q*(turningScale n : ℂ)^2*hd

private theorem bounded_product {a g : ℕ → ℂ} {B : ℝ} (ha : ∀ᶠ n in atTop, ‖a n‖ ≤ B)
    (hg : Tendsto g atTop (𝓝 0)) : Tendsto (fun n => a n*g n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (show Tendsto (fun n => B*‖g n‖) atTop (𝓝 0) by
    simpa only [norm_zero, mul_zero] using hg.norm.const_mul B)
  filter_upwards [ha] with n hn
  simpa only [norm_mul] using mul_le_mul_of_nonneg_right hn (norm_nonneg (g n))

private theorem physical_bounds {n : ℕ} {R Ω c q B : ℝ}
    (hs : |R*Ω| < 1) (hβ : 0 ≤ R*Ω) (hu : c^2+q^2 = 1) (hc : 0 ≤ c)
    (hr : 2*(|B|+1) ≤ turningScale n) (hf : |turningScale n / gamma R Ω| ≤ B)
    (ha : |turningScale n * q| ≤ B) :
    0 < detuning n (R*Ω) c ∧ |detuning n (R*Ω) c| ≤ 4*B^2 ∧
      1/2 ≤ c ∧ |turningScale n*q/c| ≤ 2*B := by
  let r := turningScale n
  let β := R*Ω
  have hr' : 0 < r := by dsimp [r]; linarith [abs_nonneg B]
  have hβ' : β < 1 := (le_abs_self _).trans_lt hs
  have hc' : c ≤ 1 := by nlinarith [sq_nonneg q]
  have hb := (abs_nonneg _).trans ha
  have hq : |q| < 1/2 := by
    rw [abs_mul, abs_of_pos hr'] at ha
    by_contra! H
    have H' := mul_le_mul_of_nonneg_left H hr'.le
    dsimp only [r] at H'
    linarith [le_abs_self B]
  have hc2 : 1/2 ≤ c := by
    rw [abs_lt] at hq
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1/2 - q) (by linarith : 0 ≤ 1/2 + q)]
  have hbc : β*c < 1 := (mul_le_of_le_one_right hβ hc').trans_lt hβ'
  have hpos : 0 < detuning n β c := by
    change 0 < 2*r^2*(1-β*c)
    positivity
  have hsq (a : ℝ) (h : |a| ≤ B) : a^2 ≤ B^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) h 2
  have hv : (r/gamma R Ω)^2 = r^2*(1-β^2) := by
    rw [div_pow, gamma_sq hs, div_inv_eq_mul]
  have H := hsq _ hf
  change (r/gamma R Ω)^2 ≤ B^2 at H
  rw [hv] at H
  have H' := hsq _ ha
  have he : 1-β*c ≤ (1-β^2)+q^2 := by
    have h₁ : β^2*c^2 ≤ β*c := by nlinarith [mul_nonneg (mul_nonneg hβ hc) (sub_nonneg.mpr hbc.le)]
    nlinarith [mul_nonneg (sub_nonneg.mpr (show β^2 ≤ 1 by nlinarith))
      (sq_nonneg q), congrArg (β^2 * ·) hu]
  refine ⟨hpos, ?_, hc2, ?_⟩
  · rw [abs_of_pos hpos]
    change 2*r^2*(1-β*c) ≤ _
    change (r*q)^2 ≤ B^2 at H'
    nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg r)]
  · rw [abs_div, abs_of_pos (lt_of_lt_of_le (by norm_num) hc2), div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hc2 hb]

/-- Airy profiles of the polarized field, uniformly for bounded scaled frequency and angle.
The latitude and the radius may vary at every harmonic, with fixed nonzero Ω. -/
theorem critical_airy (e : ℝ) {Ω B : ℝ} (hΩ : Ω ≠ 0) (R c q : ℕ → ℝ)
    (hs : ∀ n, |R n*Ω| < 1) (hβ : ∀ n, 0 ≤ R n*Ω)
    (hu : ∀ n, c n^2 + q n^2 = 1) (hc : ∀ n, 0 ≤ c n)
    (hf : ∀ᶠ n in atTop, |turningScale n / gamma (R n) Ω| ≤ B)
    (ha : ∀ᶠ n in atTop, |turningScale n*q n| ≤ B) :
    let u n := detuning n (R n*Ω) (c n)
    let H n := scaledHarmonics e (R n) Ω (c n) (q n) (hs n) n
    Tendsto (fun n => (H n).1 + (e*(R n*Ω) : ℝ) * deriv ai (u n)) atTop (𝓝 0) ∧
    Tendsto (fun n => (H n).2 - ((e*turningScale n*q n/c n : ℝ) : ℂ)/I * ai (u n))
      atTop (𝓝 0) := by
  let u n := detuning n (R n*Ω) (c n)
  have he := tendsto_turningScale.eventually (eventually_ge_atTop (2*(|B|+1)))
  have hb := (he.and (hf.and ha)).mono fun n h =>
    physical_bounds (hs n) (hβ n) (hu n) (hc n) h.1 h.2.1 h.2.2
  obtain ⟨hJ,hD⟩ := turning_point (u := u) (hb.mono fun n h => h.2.1)
  have h₁ := bounded_product (B := |e|) (a := fun n => ((e*(R n*Ω) : ℝ) : ℂ))
    (Eventually.of_forall fun n => by
      simpa only [norm_real, Real.norm_eq_abs, abs_mul e] using
        mul_le_of_le_one_right (abs_nonneg e) (hs n).le) hD
  have h₂ := bounded_product (B := |e| * (2*B))
    (a := fun n => ((e*turningScale n*q n/c n : ℝ) : ℂ)/I)
    (hb.mono fun n h => by
      rw [norm_div, norm_I, div_one, norm_real, Real.norm_eq_abs,
        show e*turningScale n*q n/c n=e*(turningScale n*q n/c n) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_left h.2.2.2 (abs_nonneg e)) hJ
  have hx (n : ℕ) : (n : ℝ)-u n*turningScale n=(n : ℝ)*(R n*Ω*c n) := by
    rw [turningScale_cube n]
    dsimp only [u, detuning]
    ring
  have hcoeff := (hb.and (eventually_gt_atTop (0 : ℕ))).mono fun n h =>
    scale_components e (hs n) hΩ (hu n) (by linarith [h.1.2.2.1] : c n ≠ 0) h.2.ne'
  constructor
  · apply h₁.congr'
    filter_upwards [hcoeff] with n h
    rw [h, hx]
    dsimp only
    ring
  · apply h₂.congr'
    filter_upwards [hcoeff] with n h
    rw [h, hx]
    dsimp only
    ring

/-- Two Macdonald profiles for the electric field. The first is polarized in the plane
of the orbit, the second in the observing meridian. -/
def macdonaldProfiles (e : ℝ) (n : ℕ) (β c q : ℝ) : ℂ × ℂ :=
  let b := √(detuning n β c)
  let ξ := (2*b^3/3 : ℝ)
  (((e*β : ℝ) : ℂ) * ((b^2 : ℝ) / ((√3 : ℝ)*π) * macdonald (2/3) ξ),
    ((e*turningScale n*q/c : ℝ) : ℂ)/I * (b / ((√3 : ℝ)*π) * macdonald (1/3) ξ))

private theorem profiles_eq (e β c q : ℝ) (n : ℕ) (hp : 0 < detuning n β c) :
    let u := detuning n β c
    macdonaldProfiles e n β c q = (-((e*β : ℝ) : ℂ) * deriv ai u,
      ((e*turningScale n*q/c : ℝ) : ℂ)/I * ai u) := by
  let b := √(detuning n β c)
  have h := ai_sq_macdonald (Real.sqrt_pos.mpr hp)
  have h' := deriv_ai_sq_macdonald (Real.sqrt_pos.mpr hp)
  rw [Real.sq_sqrt hp.le] at h h'
  dsimp only [macdonaldProfiles]
  rw [h, h', Real.sq_sqrt hp.le]
  push_cast
  ring_nf

private theorem norm_square_limit {f g : ℕ → ℂ} {B : ℝ} (hg : ∀ᶠ n in atTop, ‖g n‖ ≤ B)
    (hd : Tendsto (fun n => f n-g n) atTop (𝓝 0)) :
    Tendsto (fun n => ‖f n‖^2-‖g n‖^2) atTop (𝓝 0) := by
  have hnorm := hd.norm
  simp only [norm_zero] at hnorm
  have h1 := hnorm.eventually_le_const (by norm_num : (0:ℝ) < 1)
  apply squeeze_zero_norm' _ (show Tendsto (fun n => ‖f n-g n‖*(2*B+1)) atTop (𝓝 0) by
    simpa only [zero_mul] using hnorm.mul_const (2*B+1))
  filter_upwards [hg,h1] with n hn h
  rw [sq_sub_sq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖f n‖+‖g n‖)]
  rw [mul_comm (‖f n‖+‖g n‖)]
  exact mul_le_mul (abs_norm_sub_norm_le _ _) (by linarith [norm_sub_norm_le (f n) (g n)])
    (by positivity) (norm_nonneg _)

/-- The observed angular power spectrum in the joint critical frequency and inclination
range. Either scaled variable may vary throughout a bounded set as n tends to infinity. -/
theorem critical_spectrum (e : ℝ) {Ω B : ℝ} (hΩ : Ω ≠ 0) (R c q : ℕ → ℝ)
    (hs : ∀ n, |R n*Ω| < 1) (hβ : ∀ n, 0 ≤ R n*Ω)
    (hu : ∀ n, c n^2 + q n^2 = 1) (hc : ∀ n, 0 ≤ c n)
    (hf : ∀ᶠ n in atTop, |turningScale n / gamma (R n) Ω| ≤ B)
    (ha : ∀ᶠ n in atTop, |turningScale n*q n| ≤ B) :
    let K n := macdonaldProfiles e n (R n*Ω) (c n) (q n)
    Tendsto (fun n => (4*π*turningScale n^2/(Ω*n))^2 * linePower e 0 (R n) Ω (c n) (q n)
      (hs n) n - 2*(‖(K n).1‖^2 + ‖(K n).2‖^2)) atTop (𝓝 0) := by
  let H n := scaledHarmonics e (R n) Ω (c n) (q n) (hs n) n
  let K n := macdonaldProfiles e n (R n*Ω) (c n) (q n)
  let u n := detuning n (R n*Ω) (c n)
  have hb := ((tendsto_turningScale.eventually (eventually_ge_atTop (2*(|B|+1)))).and
    (hf.and ha)).mono fun n h => physical_bounds (hs n) (hβ n) (hu n) (hc n) h.1 h.2.1 h.2.2
  obtain ⟨h₁,h₂⟩ := critical_airy e hΩ R c q hs hβ hu hc hf ha
  have hK := hb.mono fun n h => profiles_eq e (R n*Ω) (c n) (q n) n h.1
  have hD₁ : Tendsto (fun n => (H n).1-(K n).1) atTop (𝓝 0) := by
    apply h₁.congr'
    filter_upwards [hK] with n h
    simp [K,h,H]
  have hD₂ : Tendsto (fun n => (H n).2-(K n).2) atTop (𝓝 0) := by
    apply h₂.congr'
    filter_upwards [hK] with n h
    rw [show K n = _ from h]
  have hA : Differentiable ℂ ai := fun z => (hasDerivAt_ai z).differentiableAt
  have hcont : Continuous (fun x : ℝ => ai (x : ℂ)) :=
    hA.continuous.comp continuous_ofReal
  have hcont' : Continuous (fun x : ℝ => deriv ai (x : ℂ)) :=
    hA.deriv.continuous.comp continuous_ofReal
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := 0) (b := 4*B^2)).exists_bound_of_continuousOn
    hcont.continuousOn
  obtain ⟨D,hD⟩ := (isCompact_Icc (a := 0) (b := 4*B^2)).exists_bound_of_continuousOn
    hcont'.continuousOn
  have hbound₁ : ∀ᶠ n in atTop, ‖(K n).1‖ ≤ |e| * D := by
    filter_upwards [hb,hK] with n hn hk
    rw [show K n = _ from hk]
    dsimp only
    rw [norm_mul, norm_neg, norm_real, Real.norm_eq_abs, abs_mul]
    apply mul_le_mul ((mul_le_of_le_one_right (abs_nonneg e) (hs n).le)) (hD (u n)
      ⟨hn.1.le, (le_abs_self _).trans hn.2.1⟩) (norm_nonneg _) (abs_nonneg _)
  have hbound₂ : ∀ᶠ n in atTop, ‖(K n).2‖ ≤ (|e| * (2*B))*M := by
    filter_upwards [hb,hK] with n hn hk
    rw [show K n = _ from hk]
    dsimp only
    rw [norm_mul, norm_div, norm_I, div_one, norm_real, Real.norm_eq_abs,
      show e*turningScale n*q n/c n=e*(turningScale n*q n/c n) by ring, abs_mul]
    apply mul_le_mul (mul_le_mul_of_nonneg_left hn.2.2.2 (abs_nonneg e)) (hM (u n)
      ⟨hn.1.le, (le_abs_self _).trans hn.2.1⟩) (norm_nonneg _)
      (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans hn.2.2.2))
  have ht := ((norm_square_limit hbound₁ hD₁).add (norm_square_limit hbound₂ hD₂)).const_mul 2
  simp only [add_zero, mul_zero] at ht
  apply ht.congr
  intro n
  dsimp only [H, scaledHarmonics, linePower, K]
  simp only [viewingAt, viewingDirection, meridianAt, meridianPolarization, tangentAxis,
    radialAxis, Real.sin_zero, Real.cos_zero, neg_zero, zero_smul, one_smul, zero_add, add_zero]
  simp only [norm_mul, norm_div, norm_pow, norm_real, Real.norm_eq_abs, norm_natCast, norm_ofNat,
    mul_pow, div_pow, sq_abs, abs_of_pos Real.pi_pos]
  ring

/-- Macdonald form of the positive-argument Airy function in the total-power integral. -/
def integratedProfile (u : ℝ) : ℂ :=
  (√u : ℂ) / ((√3 : ℝ)*π) * macdonald (1/3) (2*(√u)^3/3 : ℝ)

private theorem integratedProfile_eq {u : ℝ} (h : 0 < u) : integratedProfile u = ai u := by
  simpa only [integratedProfile, Real.sq_sqrt h.le] using
    (ai_sq_macdonald (Real.sqrt_pos.mpr h)).symm

private theorem scaled_total (e : ℝ) {R Ω : ℝ} (hs : |R*Ω| < 1) (hΩ : Ω ≠ 0) (m : ℕ) :
    let j := m+1
    let d := 2*j
    let r := turningScale d
    let β := R*Ω
    let x : ℝ := d*β
    (((4*π*β*r^2/(Ω^2*j))*harmonicPower e R Ω hs j : ℝ) : ℂ) =
      (e : ℂ)^2*(2*(β : ℂ)^2*((r : ℂ)^2*deriv (besselJ d) x) -
        (((r/gamma R Ω)^2 : ℝ) : ℂ)*(∫ t in (0 : ℝ)..x, besselJ d t)) := by
  let j := m+1
  let z : ℝ := (j : ℝ)*(R*Ω)
  let d := 2*j
  let r := turningScale d
  change (((4*π*(R*Ω)*r^2/(Ω^2*j))*harmonicPower e R Ω hs j : ℝ) : ℂ) =
    (e : ℂ)^2*(2*((R*Ω : ℝ) : ℂ)^2*((r : ℂ)^2*deriv (besselJ d) (d*(R*Ω) : ℝ)) -
    (((r/gamma R Ω)^2 : ℝ) : ℂ)*(∫ t in (0 : ℝ)..(d*(R*Ω) : ℝ), besselJ d t))
  have hx : (d : ℝ)*(R*Ω) = 2*z := by dsimp [d,z]; push_cast; ring
  have hi := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun t : ℝ => besselJ d t) (2*z)
  simp only [mul_zero, mul_one, real_smul, ofReal_mul, ofReal_ofNat] at hi
  have h := harmonicPower_eq e hs hΩ m
  dsimp only at h
  change (z : ℂ)*harmonicPower e R Ω hs j = _ at h
  change _ = 4*π*((e*Ω*j/(4*π) : ℝ) : ℂ)^2 *
    (2*((R*Ω : ℝ) : ℂ)^2 * deriv (besselJ d) (2*(z : ℂ)) +
      2*(z : ℂ)*(((R*Ω : ℝ) : ℂ)^2-1)*∫ t in (0 : ℝ)..1, besselJ d (2*(z : ℂ)*t)) at h
  rw [hx, ← hi, div_pow, gamma_sq hs, div_inv_eq_mul]
  have hj : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  dsimp only [z] at h ⊢
  push_cast at h ⊢
  field_simp [hj, ofReal_ne_zero.mpr hΩ, Real.pi_ne_zero] at h ⊢
  linear_combination (r : ℂ)^2*h

/-- The continuum limit of the angle-integrated line powers at critical frequencies.
The K₂/₃ term comes from the doubled-order derivative. The remaining improper integral
of K₁/₃ includes the entire subcritical interval. -/
theorem critical_total_power (e : ℝ) {Ω B : ℝ} (hΩ : Ω ≠ 0) (R : ℕ → ℝ)
    (hs : ∀ m, |R m*Ω| < 1) (hβ : ∀ m, 0 ≤ R m*Ω)
    (hf : ∀ᶠ m in atTop, |turningScale (2*(m+1)) / gamma (R m) Ω| ≤ B) :
    let j (m : ℕ) := m+1
    let r m := turningScale (2*j m)
    let β (m : ℕ) : ℝ := R m*Ω
    let u (m : ℕ) : ℝ := 2*r m^2*(1-β m)
    Tendsto (fun m => (((4*π*β m*r m^2/(Ω^2*j m))*harmonicPower e (R m) Ω (hs m) (j m) : ℝ) : ℂ)
      - (e : ℂ)^2*(2*(β m : ℂ)^2 *
        (((u m : ℂ)/((√3 : ℝ)*π)) * macdonald (2/3) (2*(√(u m))^3/3 : ℝ)) -
        (((r m/gamma (R m) Ω)^2 : ℝ) : ℂ)*(∫ v : ℝ in Set.Ioi 0, integratedProfile (u m+v))))
      atTop (𝓝 0) := by
  let d (m : ℕ) := 2*(m+1)
  let r m := turningScale (d m)
  let β m := R m*Ω
  let u m := 2*r m^2*(1-β m)
  have hd : Tendsto d atTop atTop := tendsto_atTop_atTop.mpr fun k =>
    ⟨k,fun m hm => by dsimp [d]; omega⟩
  have hpos (m : ℕ) : 0 < u m := by
    have hr : 0 < r m := by
      dsimp [r, d, turningScale]
      positivity
    have H : β m < 1 := (le_abs_self _).trans_lt (hs m)
    dsimp [u]
    positivity
  have H (m : ℕ) : (r m/gamma (R m) Ω)^2 = r m^2*(1-(β m)^2) := by
    rw [div_pow, gamma_sq (hs m), div_inv_eq_mul]
  have hg : ∀ᶠ m in atTop, (r m/gamma (R m) Ω)^2 ≤ B^2 := by
    filter_upwards [hf] with m hm
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hm 2
  have hU : ∀ᶠ m in atTop, 0 ≤ u m ∧ u m ≤ 2*B^2 := by
    filter_upwards [hg] with m hm
    refine ⟨(hpos m).le, ?_⟩
    rw [H] at hm
    have h₁ : β m ≤ 1 := (le_abs_self _).trans (hs m).le
    have he := mul_nonneg (hβ m) (sub_nonneg.mpr h₁)
    dsimp only [u]
    nlinarith [mul_nonneg (sq_nonneg (r m)) he]
  have hp := turning_primitive hd hU
  have hD := (turning_point_along (u := u) (B := 2*B^2) hd
    (hU.mono fun m hm => by simpa only [abs_of_nonneg hm.1] using hm.2)).2
  have h₁ := bounded_product (a := fun m => 2*(β m : ℂ)^2) (B := 2)
    (Eventually.of_forall fun m => by
      rw [norm_mul, norm_ofNat, norm_pow, norm_real, Real.norm_eq_abs]
      nlinarith [pow_le_pow_left₀ (abs_nonneg _) (hs m).le 2]) hD
  have h₂ := bounded_product (a := fun m => (((r m/gamma (R m) Ω)^2 : ℝ) : ℂ)) (B := B^2)
    (hg.mono fun m hm => by rwa [norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]) hp
  have h := (h₁.sub h₂).const_mul ((e : ℂ)^2)
  simp only [sub_zero, mul_zero] at h
  apply h.congr
  intro m
  have hx : (d m : ℝ)-u m*turningScale (d m)=(d m : ℝ)*β m := by
    rw [turningScale_cube (d m)]
    dsimp only [u,r]
    ring
  have hK := deriv_ai_sq_macdonald (Real.sqrt_pos.mpr (hpos m))
  rw [Real.sq_sqrt (hpos m).le] at hK
  have hI : (∫ v : ℝ in Set.Ioi 0, integratedProfile (u m+v)) =
      ∫ v : ℝ in Set.Ioi 0, ai (u m+v : ℝ) :=
    setIntegral_congr_fun measurableSet_Ioi fun v hv => integratedProfile_eq (by linarith [hpos m,
      show 0 < v from hv])
  dsimp only
  rw [scaled_total e (hs m) hΩ m]
  change _ = _ - (e : ℂ)^2*(2*(β m : ℂ)^2 *
    ((u m : ℂ)/((√3 : ℝ)*π)*macdonald (2/3) (2*(√(u m))^3/3 : ℝ)) -
    (((r m/gamma (R m) Ω)^2 : ℝ) : ℂ)*(∫ v : ℝ in Set.Ioi 0, integratedProfile (u m+v)))
  rw [hx, hK, hI]
  dsimp only [d, r, β]
  ring

end ProjectAinos.Electrodynamics.Radiation.Synchrotron
