/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.HyperbolicCompleteness
import ProjectAinos.SpecialFunctions.HyperbolicSpectrum

noncomputable section
open Complex Filter Set MeasureTheory FourierTransform
open scoped Real FourierTransform Topology ContDiff SchwartzMap
open ProjectAinos.SpecialFunctions.Hyperbolic ProjectAinos.SpecialFunctions.SphericalHarmonics

example : ℕ → (ℝ → ℂ) → ℝ → ℂ := laplacian
example : ℕ → ℝ → ℝ := potential
example : ℕ → (ℝ → ℂ) → ℝ → ℂ := raise
example : (ℝ → ℂ) → ℕ → ℝ → ℂ := raised
example : ℝ → ℝ → ℂ := sineSeed
example : ℕ → ℝ → ℝ → ℂ := harmonic
example : Measure ℝ := radialVolume
example : IsFiniteMeasureOnCompacts radialVolume := inferInstance
example : Type := Space

example (l : ℕ) {g : ℝ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    (Real.sinh r : ℂ)*laplacian l (fun t => g t/(Real.sinh t : ℂ)) r =
      deriv (deriv g) r-(1+potential l r : ℝ)*g r :=
  conjugate l hr hg

example {g : ℝ → ℂ} {w : ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (he : ∀ r : ℝ, 0 < r → deriv (deriv g) r = -w*g r) (l : ℕ) {r : ℝ} (hr : 0 < r) :
    laplacian l (fun t => raised g l t/(Real.sinh t : ℂ)) r =
      -(1+w)*(raised g l r/(Real.sinh r : ℂ)) :=
  raised_equation hg he l hr

example (l : ℕ) (k : ℝ) {r : ℝ} (hr : 0 < r) :
    laplacian l (harmonic l k) r = -(1+(k : ℂ)^2)*harmonic l k r :=
  harmonic_equation l k hr

example (l : ℕ) (g : 𝓢(ℝ,ℂ)) (hg : ∀ t, g (-t) = -g t)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun v : ℝ => (I*(2*π*v : ℝ)*𝓕 g v)*harmonic l (2*π*v) r) ∧
      raised g l r/(Real.sinh r : ℂ) =
        ∫ v : ℝ, (I*(2*π*v : ℝ)*𝓕 g v)*harmonic l (2*π*v) r :=
  harmonic_synthesis l g hg hr

example (l : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) {B : ℝ}
    (hB : ∀ s ≥ B, F s = 0) :
    ∃ g : 𝓢(ℝ,ℂ), (∀ t, g (-t) = -g t) ∧ ∀ r : ℝ, 0 < r →
      Integrable (fun v : ℝ => (I*(2*π*v : ℝ)*𝓕 g v)*harmonic l (2*π*v) r) ∧
      (Real.sinh r : ℂ)^l*F (Real.cosh r) =
        ∫ v : ℝ, (I*(2*π*v : ℝ)*𝓕 g v)*harmonic l (2*π*v) r :=
  expand_channel l hF hB

example (E : ℝ) :
    1 ≤ E ↔ ∀ ε : ℝ, 0 < ε → ∃ g : 𝓢(ℝ,ℂ), (∀ t, g (-t) = -g t) ∧
      0 < (∫ r : ℝ, ‖g r‖^2) ∧ (∫ r : ℝ, ‖((1-E : ℝ) : ℂ)*g r-deriv (deriv g) r‖^2) ≤
        ε^2*(∫ r : ℝ, ‖g r‖^2) :=
  approximate_iff E

example (f : ℝ → ℝ) :
    (∫ s, f s ∂radialVolume) = ∫ r : ℝ in Ioi 0, Real.sinh r^2*f (Real.cosh r) :=
  radialVolume_integral f

example (f : Space) (orth : ∀ n (i : Fin (2*n+1)) (g : 𝓢(ℝ,ℂ)),
    (∀ t, g (-t) = -g t) →
    (∫ s, (∫ v : ℝ, (I*(2*π*v : ℝ)*𝓕 g v)*harmonic n (2*π*v) (Real.arcosh s)).re *
      inner ℝ (((realBasis n i : l2Space 3 n) : Lp ℝ 2 (surfaceMeasure 3))) (f s)
      ∂radialVolume) = 0) : f = 0 :=
  complete f orth

example (l : ℕ) (E : ℝ) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (h₀ : u 0 = 0)
    (hL : IntegrableOn (fun r => u r^2) (Ioi 0))
    (hD : IntegrableOn (fun r => deriv u r^2) (Ioi 0))
    (he : ∀ r : ℝ, 0 < r → deriv (deriv u) r = (1+potential l r-E)*u r) :
    EqOn u 0 (Ici 0) :=
  no_bound_state l E hu h₀ hL hD he
