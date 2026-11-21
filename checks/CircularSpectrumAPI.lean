/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.Radiation.CriticalSpectrum

noncomputable section
open Complex Filter MeasureTheory Set Function
open scoped Real Topology
namespace ProjectAinos.Electrodynamics.Radiation.Synchrotron
open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity SubluminalWorldline
open SpecialFunctions.Bessel SpecialFunctions.Airy CollisionSpectrum
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ex" => (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : E3)

example : ℝ → SubluminalWorldline → E3 → E3 → ℝ → ℤ → ℂ := observedHarmonic
example : ℝ → ℝ → E3 := viewingDirection
example : ℝ → ℝ → E3 := meridianPolarization
example : ℝ → E3 := radialAxis
example : ℝ → E3 := tangentAxis
example : ℝ → ℝ → ℝ → E3 := viewingAt
example : ℝ → ℝ → ℝ → E3 := meridianAt
example : (e α R Ω c q : ℝ) → |R*Ω| < 1 → ℕ → ℝ := linePower
example : (e R Ω : ℝ) → |R*Ω| < 1 → ℕ → ℝ := harmonicPower

example (e α : ℝ) {R Ω c q : ℝ} (hs : |R*Ω| < 1) (hΩ : Ω ≠ 0)
    (hu : c^2+q^2 = 1) (m : ℤ) (hm : m ≠ 0) :
    let w := circular R Ω hs
    let n := viewingAt α c q
    let x := (m : ℝ)*(R*Ω*c)
    let phase := exp (-((m : ℂ)*α)*I)
    observedHarmonic e w n (radialAxis α) Ω m =
      phase * (e*Ω^2*R*m/(4*π) * deriv (besselJ m) x) ∧
    observedHarmonic e w n (meridianAt α c q) Ω m =
      phase * (e*Ω^2*R*q*m/(8*π*I) * (besselJ (m-1 : ℤ) x + besselJ (m+1 : ℤ) x)) :=
  circular_harmonics_at e α hs hΩ hu m hm

example (e : ℝ) {R Ω c q : ℝ} (hs : |R*Ω| < 1) (hΩ : Ω ≠ 0)
    (hu : c^2+q^2 = 1) (m : ℤ) (hm : m ≠ 0) :
    let w := circular R Ω hs
    let n := viewingDirection c q
    let x := (m : ℝ)*(R*Ω*c)
    observedHarmonic e w n ex Ω m =
      e*Ω^2*R*m/(4*π) * deriv (besselJ m) x ∧
    observedHarmonic e w n (meridianPolarization c q) Ω m =
      e*Ω^2*R*q*m/(8*π*I) * (besselJ (m-1 : ℤ) x + besselJ (m+1 : ℤ) x) :=
  circular_harmonics e hs hΩ hu m hm

example (e α : ℝ) {R Ω c q : ℝ} (hs : |R*Ω| < 1) (hΩ : Ω ≠ 0)
    (hu : c^2+q^2 = 1) (m : ℕ) :
    let j := m+1
    let x := (j : ℝ)*(R*Ω*c)
    (linePower e α R Ω c q hs j : ℂ) = 2*(e*Ω*j/(4*π) : ℝ)^2 *
      (((R*Ω : ℝ) : ℂ)^2/2*(besselJ m x^2 + besselJ (m+2 : ℕ) x^2) - besselJ j x^2) :=
  linePower_eq e α hs hΩ hu m

example (e : ℝ) {R Ω : ℝ} (hs : |R*Ω| < 1) (hΩ : Ω ≠ 0) (m : ℕ) :
    let j := m+1
    let β := R*Ω
    let z := (j : ℝ)*β
    let F := e*Ω*j/(4*π)
    (z : ℂ) * harmonicPower e R Ω hs j = 4*π*(F : ℂ)^2 *
      (2*(β : ℂ)^2 * deriv (besselJ (2*j : ℕ)) (2*z) +
        2*z*((β : ℂ)^2-1)*∫ t in (0 : ℝ)..1, besselJ (2*j : ℕ) (2*z*t)) :=
  harmonicPower_eq e hs hΩ m

example : ℕ → ℝ → ℝ → ℝ := detuning
example : (e R Ω c q : ℝ) → |R*Ω| < 1 → ℕ → ℂ × ℂ := scaledHarmonics
example : ℝ → ℕ → ℝ → ℝ → ℝ → ℂ × ℂ := macdonaldProfiles

example (n : ℕ) (R Ω : ℝ) :
    (n : ℝ) / gamma R Ω ^ 3 = 2 * (turningScale n / gamma R Ω)^3 :=
  critical_frequency n R Ω

example (e : ℝ) {Ω B : ℝ} (hΩ : Ω ≠ 0) (R c q : ℕ → ℝ)
    (hs : ∀ n, |R n*Ω| < 1) (hβ : ∀ n, 0 ≤ R n*Ω)
    (hu : ∀ n, c n^2 + q n^2 = 1) (hc : ∀ n, 0 ≤ c n)
    (hf : ∀ᶠ n in atTop, |turningScale n / gamma (R n) Ω| ≤ B)
    (ha : ∀ᶠ n in atTop, |turningScale n*q n| ≤ B) :
    let u n := detuning n (R n*Ω) (c n)
    let H n := scaledHarmonics e (R n) Ω (c n) (q n) (hs n) n
    Tendsto (fun n => (H n).1 + (e*(R n*Ω) : ℝ) * deriv ai (u n)) atTop (𝓝 0) ∧
    Tendsto (fun n => (H n).2 - ((e*turningScale n*q n/c n : ℝ) : ℂ)/I * ai (u n))
      atTop (𝓝 0) :=
  critical_airy e hΩ R c q hs hβ hu hc hf ha

example (e : ℝ) {Ω B : ℝ} (hΩ : Ω ≠ 0) (R c q : ℕ → ℝ)
    (hs : ∀ n, |R n*Ω| < 1) (hβ : ∀ n, 0 ≤ R n*Ω)
    (hu : ∀ n, c n^2 + q n^2 = 1) (hc : ∀ n, 0 ≤ c n)
    (hf : ∀ᶠ n in atTop, |turningScale n / gamma (R n) Ω| ≤ B)
    (ha : ∀ᶠ n in atTop, |turningScale n*q n| ≤ B) :
    let K n := macdonaldProfiles e n (R n*Ω) (c n) (q n)
    Tendsto (fun n => (4*π*turningScale n^2/(Ω*n))^2 * linePower e 0 (R n) Ω (c n) (q n)
      (hs n) n - 2*(‖(K n).1‖^2 + ‖(K n).2‖^2)) atTop (𝓝 0) :=
  critical_spectrum e hΩ R c q hs hβ hu hc hf ha

example : ℝ → ℂ := integratedProfile

example (e : ℝ) {Ω B : ℝ} (hΩ : Ω ≠ 0) (R : ℕ → ℝ)
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
      atTop (𝓝 0) :=
  critical_total_power e hΩ R hs hβ hf

example (e : ℝ) (w : SubluminalWorldline) {n : E3} (hn : ‖n‖ = 1)
    (p : E3) (Ω : ℝ) : HasSum (fun m : ℤ => ‖observedHarmonic e w n p Ω m‖^2)
      ((2*π)⁻¹ * ∫ M in -π..π, (inner ℝ p (observedAmplitude e w n (M/Ω)))^2) :=
  harmonic_parseval e w hn p Ω

end ProjectAinos.Electrodynamics.Radiation.Synchrotron
