/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.GeneralRelativity.CurvedCosmology

noncomputable section
open Set Filter
open scoped ContDiff Topology
open ProjectAinos.SmoothGeometry ProjectAinos.SmoothGeometry.CoordinateMetric
open ProjectAinos.SmoothGeometry.IsotropicRicci
open ProjectAinos.GeneralRelativity.FLRW hiding hubble
open ProjectAinos.GeneralRelativity.CosmologicalModels
open ProjectAinos.GeneralRelativity.CurvedPerturbation
open ProjectAinos.SpecialFunctions.HarmonicPolynomial
open ProjectAinos.GeneralRelativity
local notation "E" => MinkowskiModel 3

example : Data → ℝ → ℝ := hubble
example : ℝ → (E → ℝ) → E → ℝ := spatialLaplacian
example : Data → (E → ℝ) → ℝ → E → Matrix (Fin 4) (Fin 4) ℝ := metricFamily
example : Data → ℝ → (ℝ → ℝ) → (E → ℝ) → (E → ℝ) → (E → Fin 4 → ℝ) →
    ℝ → E → Fin 4 → Fin 4 → ℝ := dustSource
example : Data → ℝ → (ℝ → ℝ) → (E → ℝ) → (E → ℝ) → (E → Fin 4 → ℝ) → E → Prop :=
  LinearizedDustAt
example : (ℝ → ℝ) → (E → ℝ) → E → ℝ := separated
example : Data → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → (E → ℝ) → E → ℝ := contrast
example : Data → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (E → ℝ) → E → Fin 4 → ℝ := covelocity
example : Data → ℝ → ℝ := decay
example : Data → ℝ → ℝ → ℝ := growth
example : Data → (ℝ → ℝ) → ℝ → Prop := Evolution
example : ℝ → E → ℝ := chartCoordinate
example {l : ℕ} : harmonics 3 l → ℝ → (ℝ → ℝ) → E → ℝ := chartHarmonic
example {l : ℕ} : harmonics 3 l → ℕ → E → ℝ := closedHarmonic
example {l : ℕ} : harmonics 3 l → ℝ → E → ℝ := openHarmonic

example {D : Data} {t : ℝ} (ht : t ∈ D.I) :
    HasDerivAt (hubble D)
      ((deriv (deriv D.a) t*D.a t-deriv D.a t^2)/D.a t^2) t :=
  hasDerivAt_hubble ht

example {D : Data} (hN : D.N=D.a) {x : E} (hx : x ∈ domain D) (u : E → ℝ) :
    metricFamily D u 0 x = (FLRW.metric D).coefficient x :=
  metricFamily_zero hN hx u

example {D : Data} (hN : D.N=D.a) {κ : ℝ} {ρ : ℝ → ℝ}
    (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0)) {t : ℝ} (ht : t ∈ D.I) :
    κ*ρ t*D.a t^2 = 3*((hubble D t)^2+D.k) ∧
    2*deriv (hubble D) t+(hubble D t)^2+D.k=0 :=
  conformal_dust_eq hN hB ht

example {D : Data} (hN : D.N=D.a) {κ : ℝ} {ρ : ℝ → ℝ}
    (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0)) {x : E} (hx : x ∈ domain D)
    {u : E → ℝ} (hu : ContDiffAt ℝ ∞ u x) (δ : E → ℝ) (V : E → Fin 4 → ℝ) :
    let H := hubble D (x 0)
    let a := D.a (x 0)
    LinearizedDustAt D κ ρ u δ V x ↔
      secondPartial u x 0 0 + 3*H*part u 0 x-2*D.k*u x=0 ∧
      κ*ρ (x 0)*a^2/2*δ x = spatialLaplacian D.k u x-3*H*(part u 0 x+H*u x)+3*D.k*u x ∧
      ∀ i : Fin 4, i≠0 → κ*ρ (x 0)*a*V x i = -2*(secondPartial u x i 0+H*part u i x) :=
  linearizedDustAt_iff hN hB hx hu δ V

example {D : Data} (hN : D.N=D.a) {κ : ℝ} {ρ φ : ℝ → ℝ}
    (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0)) {x : E} (hx : x ∈ domain D)
    (hm : κ*ρ (x 0)≠0) (hφ : ContDiffAt ℝ ∞ φ (x 0)) (Q : E → ℝ) (hQ : ContDiffAt ℝ ∞ Q x)
    (h₀ : ∀ᶠ y in 𝓝 x, part Q 0 y=0) (q : ℝ) (he : spatialLaplacian D.k Q x = -q*Q x)
    (ht : deriv (deriv φ) (x 0)+3*hubble D (x 0)*deriv φ (x 0)-2*D.k*φ (x 0)=0) :
    LinearizedDustAt D κ ρ (separated φ Q) (contrast D κ ρ φ q Q) (covelocity D κ ρ φ Q) x :=
  single_mode hN hB hx hm hφ Q hQ h₀ q he ht

example {D : Data} (hN : D.N=D.a) {κ : ℝ} {ρ : ℝ → ℝ}
    (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0)) (hc : Continuous D.a)
    (b : ℝ) {t : ℝ} (ht : t ∈ D.I) :
    Evolution D (decay D) t ∧ Evolution D (growth D b) t ∧
      decay D t*deriv (growth D b) t-deriv (decay D) t*growth D b t =
        ((hubble D t)^2+D.k)/(2*(D.a t)^2) :=
  dust_amplitudes hN hB hc b ht

example (D : Data) (hc : Continuous D.a) (b : ℝ) :
    ContDiffOn ℝ ∞ (decay D) D.I ∧ ContDiffOn ℝ ∞ (growth D b) D.I :=
  smooth_amplitudes D hc b

example {l : ℕ} (p : harmonics 3 l) (k : ℝ) {F : ℝ → ℝ} {x : E}
    (hx : psi k x ≠ 0) (hf : ContDiffAt ℝ ∞ F (chartCoordinate k x)) :
    let s := chartCoordinate k x
    spatialLaplacian k (chartHarmonic p k F) x =
      k*(MvPolynomial.eval (fun j : Fin 3 => x j.succ) p.val.val)*(psi k x)^(-(l : ℤ))*
        ((1-s^2)*deriv (deriv F) s-(2*l+3)*s*deriv F s-(l : ℝ)*(l+2)*F s) :=
  chartHarmonic_laplacian p k hx hf

example {l : ℕ} (p : harmonics 3 l) (k : ℝ) {F : ℝ → ℝ} {x : E}
    (hx : psi k x ≠ 0) (hf : ContDiffAt ℝ ∞ F (chartCoordinate k x)) :
    ContDiffAt ℝ ∞ (chartHarmonic p k F) x :=
  smooth_chartHarmonic p k hx hf

example {l : ℕ} (p : harmonics 3 l) (k : ℝ) {F : ℝ → ℝ} {x : E}
    (hx : psi k x ≠ 0) (hf : ContDiffAt ℝ ∞ F (chartCoordinate k x)) :
    ∀ᶠ y in 𝓝 x, part (chartHarmonic p k F) 0 y=0 :=
  chartHarmonic_time p k hx hf

example {l : ℕ} (p : harmonics 3 l) (m : ℕ) (x : E) :
    spatialLaplacian 1 (closedHarmonic p m) x =
      -((l+m : ℕ) : ℝ)*(l+m+2)*closedHarmonic p m x :=
  closedHarmonic_equation p m x

example {l : ℕ} (p : harmonics 3 l) (ξ : ℝ) {x : E}
    (hx : 0 < psi (-1) x) :
    spatialLaplacian (-1) (openHarmonic p ξ) x = -(1+ξ^2)*openHarmonic p ξ x :=
  openHarmonic_equation p ξ hx

example {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ) {l : ℕ}
    (p : harmonics 3 l) (m : ℕ) (b : ℝ) {x : E} (hx : x ∈ domain (closedDust A hA)) :
    let D := closedDust A hA
    let ρ := dustDensity κ (6*A) D.a
    let q := ((l+m : ℕ) : ℝ)*(l+m+2)
    let Q := closedHarmonic p m
    ∀ φ ∈ ({decay D,growth D b} : Set (ℝ → ℝ)), LinearizedDustAt D κ ρ
      (separated φ Q) (contrast D κ ρ φ q Q) (covelocity D κ ρ φ Q) x :=
  closed_dust_modes hA hκ p m b hx

example {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ) {l : ℕ}
    (p : harmonics 3 l) (ξ b : ℝ) {x : E} (hx : x ∈ domain (openDust A hA)) :
    let D := openDust A hA
    let ρ := dustDensity κ (6*A) D.a
    let Q := openHarmonic p ξ
    ∀ φ ∈ ({decay D,growth D b} : Set (ℝ → ℝ)), LinearizedDustAt D κ ρ
      (separated φ Q) (contrast D κ ρ φ (1+ξ^2) Q) (covelocity D κ ρ φ Q) x :=
  open_dust_modes hA hκ p ξ b hx
