/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SpecialRelativity.ManyBodyMeasure

/-! Public consumers of the measure of the final states of several particles at a fixed total
momentum: the foliation of the future timelike momenta by mass shells, the measure defined by
peeling off the last particle with its measurability in the total momentum, the integration
formula against the product of the shell measures, the disintegration, the covariance, the
support and the total mass, the cross-section of several outgoing particles, and instances with
three particles.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace ProjectAinos.SpecialRelativity.ManyBody

open SmoothGeometry SmoothGeometry.Minkowski FutureShell TwoBodyFibre

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable (m : ℕ → ℝ)

example (m₃ m₄ : ℝ) : region 3 m₃ m₄ = massRegion (m₃ + m₄) :=
  region_eq_massRegion m₃ m₄

example (S : ℝ) : IsOpen (massRegion S) :=
  isOpen_massRegion S

example (S : ℝ) : MeasurableSet (massRegion S) :=
  measurableSet_massRegion S

example : massRegion 0 = {Q : MinkowskiModel 3 | FutureTimelike Q} :=
  massRegion_zero

example (S t : ℝ) (K : Fin 3 → ℝ) :
    (Fin.cons t K : MinkowskiModel 3) ∈ massRegion S ↔
      t ∈ Ioi (Real.sqrt (S ^ 2 + ∑ i, K i ^ 2)) :=
  cons_mem_massRegion_iff S t K

example {S M : ℝ} (hS : 0 ≤ S) (hM : S < M) (K : Fin 3 → ℝ) :
    point M K ∈ massRegion S :=
  point_mem_massRegion hS hM K

example {M : ℝ} (hM : 0 < M) (K : Fin 3 → ℝ) :
    invariantMass (point M K) = M :=
  invariantMass_point hM K

example :
    Continuous fun z : ℝ × (Fin 3 → ℝ) => energy z.1 z.2 :=
  continuous_energy_mass

example : Measurable fun z : ℝ × (Fin 3 → ℝ) => point z.1 z.2 :=
  measurable_point_mass

example (K : Fin 3 → ℝ) {M : ℝ} (hM : 0 < M) :
    HasDerivAt (fun M : ℝ => energy M K) (M / energy M K) M :=
  hasDerivAt_energy_mass K hM

example (K : Fin 3 → ℝ) {S : ℝ} (hS : 0 ≤ S) :
    StrictMonoOn (fun M : ℝ => energy M K) (Ioi S) :=
  strictMonoOn_energy_mass K hS

example (K : Fin 3 → ℝ) {S : ℝ} (hS : 0 ≤ S) :
    (fun M : ℝ => energy M K) '' Ioi S = Ioi (Real.sqrt (S ^ 2 + ∑ i, K i ^ 2)) :=
  image_energy_mass K hS

example {S : ℝ} (hS : 0 ≤ S) {h : MinkowskiModel 3 → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ Q in massRegion S, h Q =
      ∫⁻ M in Ioi S, ∫⁻ K, ENNReal.ofReal (M / energy M K) * h (point M K) :=
  lintegral_massRegion hS hh

example {S : ℝ} (hS : 0 ≤ S) {h : MinkowskiModel 3 → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ Q in massRegion S, h Q =
      ∫⁻ M in Ioi S, ENNReal.ofReal M * ∫⁻ K, h (point M K) ∂(FutureShell.measure 3 M) :=
  lintegral_massRegion_shell hS hh

example {h : MinkowskiModel 3 → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ Q in {Q : MinkowskiModel 3 | FutureTimelike Q}, h Q =
      ∫⁻ M in Ioi 0, ENNReal.ofReal M * ∫⁻ K, h (point M K) ∂(FutureShell.measure 3 M) :=
  lintegral_futureTimelike hh

example {d : ℕ} :
    Continuous fun z : ℝ × (Fin d → ℝ) => energy z.1 z.2 :=
  continuous_energy_mass'

example (m₄ : ℝ) :
    Measurable fun z : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => labFirst z.1 m₄ z.2.1 z.2.2 :=
  measurable_labFirst_mass m₄

example (m₄ : ℝ) :
    Measurable fun z : ℝ × ℝ => restMomentum z.1 m₄ z.2 :=
  measurable_restMomentum_mass m₄

example (m₄ : ℝ) :
    Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 =>
      fibrePair z.1.1 m₄ z.1.2 z.2 :=
  measurable_fibrePair_mass m₄

example (m₄ : ℝ) :
    Measurable fun z : ℝ × MinkowskiModel 3 => fibreWeight z.1 m₄ z.2 :=
  measurable_fibreWeight_mass m₄

example {m₃ m₄ : ℝ} (P : MinkowskiModel 3)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(fibreMeasure m₃ m₄ P) =
      fibreWeight m₃ m₄ P * ∫⁻ n, f (fibrePair m₃ m₄ P n) ∂Sphere.sphereMeasure :=
  lintegral_fibreMeasure' P hf

example (m' : ℝ) :
    Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 =>
      interMomentum z.1.1 m' z.1.2 z.2 :=
  measurable_interMomentum m'

example : massSum m 0 = m 0 + m 1 :=
  massSum_zero m

example (k : ℕ) : massSum m (k + 1) = massSum m k + m (k + 2) :=
  massSum_succ m k

example (hm : ∀ i, 0 ≤ m i) (k : ℕ) : 0 ≤ massSum m k :=
  massSum_nonneg m hm k

example (S m' : ℝ) :
    Measurable fun z : MinkowskiModel 3 × ℝ => window S m' z.1 z.2 :=
  measurable_window S m'

example {S m' M : ℝ} {P : MinkowskiModel 3} (h : S < M ∧ M < invariantMass P - m') :
    window S m' P M = ENNReal.ofReal M :=
  window_of_mem h

example {S m' M : ℝ} {P : MinkowskiModel 3}
    (h : ¬(S < M ∧ M < invariantMass P - m')) : window S m' P M = 0 :=
  window_of_notMem h

example :
    ∀ k : ℕ, Measurable fun z : MinkowskiModel 3 × Param k => weight m k z.1 z.2 :=
  measurable_weight m

example :
    ∀ k : ℕ, Measurable fun z : MinkowskiModel 3 × Param k => phase m k z.1 z.2 :=
  measurable_phase m

example (k : ℕ) (P : MinkowskiModel 3) : Measurable (weight m k P) :=
  measurable_weight_right m k P

example (k : ℕ) (P : MinkowskiModel 3) : Measurable (phase m k P) :=
  measurable_phase_right m k P

example (k : ℕ) (P : MinkowskiModel 3) {f : Config k → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂(manyMeasure m k P) = ∫⁻ θ, weight m k P θ * f (phase m k P θ) ∂(base k) :=
  lintegral_manyMeasure m k P hf

example (k : ℕ) {α : Type*} [MeasurableSpace α]
    {F : α × Config k → ℝ≥0∞} (hF : Measurable F) {g : α → MinkowskiModel 3}
    (hg : Measurable g) :
    Measurable fun a => ∫⁻ x, F (a, x) ∂(manyMeasure m k (g a)) :=
  measurable_lintegral_manyMeasure m k hF hg

example (P : MinkowskiModel 3) :
    manyMeasure m 0 P = fibreMeasure (m 0) (m 1) P :=
  manyMeasure_zero m P

example (m' : ℝ) (P : MinkowskiModel 3) :
    Measurable fun a : ℝ × sphere (0 : E3) 1 => fibrePair a.1 m' P a.2 :=
  measurable_fibrePair_mass_right m' P

example (m' : ℝ) (P : MinkowskiModel 3) :
    Measurable fun a : ℝ × sphere (0 : E3) 1 => interMomentum a.1 m' P a.2 :=
  measurable_interMomentum_right m' P

example (k : ℕ) {f : Config (k + 1) → ℝ≥0∞} (hf : Measurable f)
    (M : ℝ) :
    Measurable fun y : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ∫⁻ x, f ((x, y.2) : Config k × (Fin 3 → ℝ)) ∂(manyMeasure m k (point M y.1)) :=
  measurable_lintegral_point m k hf M

example (k : ℕ) (P : MinkowskiModel 3)
    {f : Config (k + 1) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(manyMeasure m (k + 1) P) =
      ∫⁻ M, window (massSum m k) (m (k + 2)) P M *
        ∫⁻ y, (∫⁻ x, f ((x, y.2) : Config k × (Fin 3 → ℝ)) ∂(manyMeasure m k (point M y.1)))
          ∂(fibreMeasure M (m (k + 2)) P) :=
  lintegral_manyMeasure_succ m k P hf

example {S : ℝ} (hS : 0 ≤ S) (m' : ℝ)
    {H : (Fin 3 → ℝ) × MinkowskiModel 3 → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ π, (∫⁻ Q in massRegion S, H (π, Q)) ∂(FutureShell.measure 3 m') =
      ∫⁻ M in Ioi S, ENNReal.ofReal M *
        ∫⁻ y, H (y.2, point M y.1)
          ∂((FutureShell.measure 3 M).prod (FutureShell.measure 3 m')) :=
  lintegral_shell_foliation hS m' hH

example {S m' M : ℝ} (hS : 0 ≤ S) (hm' : 0 ≤ m') (hM : S < M)
    {P : MinkowskiModel 3} (hP : P ∈ region 3 M m') : P ∈ massRegion (S + m') :=
  mem_massRegion_of_mem_region hS hm' hM hP

example {S m' M : ℝ} (hS : 0 ≤ S) (hm' : 0 ≤ m') (hM : S < M)
    {P : MinkowskiModel 3} (hP : 0 < time P) : P ∈ region 3 M m' ↔ M < invariantMass P - m' :=
  mem_region_iff hS hm' hM hP

example {S m' : ℝ} (hS : 0 ≤ S) (hm' : 0 ≤ m')
    {J : ℝ × MinkowskiModel 3 → ℝ≥0∞} (hJ : Measurable J) :
    ∫⁻ M in Ioi S, ENNReal.ofReal M * ∫⁻ P in region 3 M m', J (M, P) =
      ∫⁻ P in massRegion (S + m'), ∫⁻ M, window S m' P M * J (M, P) :=
  lintegral_mass_region_swap hS hm' hJ

example (m' : ℝ)
    {G : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) → ℝ≥0∞} (hG : Measurable G) :
    Measurable fun z : ℝ × MinkowskiModel 3 => ∫⁻ y, G (z.1, y) ∂(fibreMeasure z.1 m' z.2) :=
  measurable_lintegral_fibreMeasure m' hG

example (hm : ∀ i, 0 ≤ m i) :
    ∀ (k : ℕ) {f : Config k → ℝ≥0∞}, Measurable f →
      ∫⁻ x, f x ∂(shellProd m k) =
        ∫⁻ P in massRegion (massSum m k), ∫⁻ x, f x ∂(manyMeasure m k P) :=
  lintegral_shellProd m hm

example (k : ℕ) : Measurable (manyMeasure m k) :=
  measurable_manyMeasure m k

example (hm : ∀ i, 0 ≤ m i) (k : ℕ) :
    shellProd m k = (volume.restrict (massRegion (massSum m k))).bind (manyMeasure m k) :=
  shellProd_eq_bind m hm k

example (L : orthochronousLorentzGroup 3) : ∀ k : ℕ, Measurable (act m L k) :=
  measurable_act m L

example (S m' : ℝ) (L : orthochronousLorentzGroup 3) (P : MinkowskiModel 3)
    (M : ℝ) : window S m' (L.val.val P) M = window S m' P M :=
  window_lorentz S m' L P M

example (hm : ∀ i, 0 ≤ m i) (L : orthochronousLorentzGroup 3) :
    ∀ (k : ℕ) {P : MinkowskiModel 3}, P ∈ massRegion (massSum m k) →
      ∀ {f : Config k → ℝ≥0∞}, Measurable f →
        ∫⁻ x, f (act m L k x) ∂(manyMeasure m k P) =
          ∫⁻ x, f x ∂(manyMeasure m k (L.val.val P)) :=
  lintegral_comp_act m hm L

example (hm : ∀ i, 0 ≤ m i) (k : ℕ) {P : MinkowskiModel 3}
    (hP : P ∈ massRegion (massSum m k)) (L : orthochronousLorentzGroup 3) :
    Measure.map (act m L k) (manyMeasure m k P) = manyMeasure m k (L.val.val P) :=
  map_manyMeasure m hm k hP L

example : invariantMass (Fin.cons 4 0 : MinkowskiModel 3) = 4 :=
  invariantMass_rest

example :
    (Fin.cons 4 0 : MinkowskiModel 3) ∈ massRegion (massSum (fun _ => 1) 1) ∧
      0 < manyMeasure (fun _ => 1) 1 (Fin.cons 4 0) univ :=
  manyMeasure_one_pos

example : ∀ k : ℕ, Measurable (totalMomentum m k) :=
  measurable_totalMomentum m

example (hm : ∀ i, 0 ≤ m i) :
    ∀ (k : ℕ) {P : MinkowskiModel 3}, P ∈ massRegion (massSum m k) →
      manyMeasure m k P {x | totalMomentum m k x ≠ P} = 0 :=
  manyMeasure_totalMomentum_ne m hm

example (hm : ∀ i, 0 ≤ m i) (k : ℕ) {P : MinkowskiModel 3}
    (hP : P ∈ massRegion (massSum m k)) :
    ∀ᵐ x ∂(manyMeasure m k P), totalMomentum m k x = P :=
  ae_totalMomentum_eq m hm k hP

example {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (h : m₃ + m₄ < M) :
    restMomentum m₃ m₄ M ≤ M / 2 :=
  restMomentum_le_half hm₃ hm₄ h

example {m₃ m₄ : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) {P : MinkowskiModel 3}
    (hP : P ∈ region 3 m₃ m₄) : fibreMeasure m₃ m₄ P univ ≤ ENNReal.ofReal (2 * Real.pi) :=
  fibreMeasure_univ_le hm₃ hm₄ hP

example (hm : ∀ i, 0 ≤ m i) :
    ∀ (k : ℕ) {P : MinkowskiModel 3}, P ∈ massRegion (massSum m k) →
      manyMeasure m k P univ ≤
        ENNReal.ofReal ((2 * Real.pi) ^ (k + 1) * invariantMass P ^ (2 * k)) :=
  manyMeasure_univ_le m hm

example (hm : ∀ i, 0 ≤ m i) (k : ℕ) {P : MinkowskiModel 3}
    (hP : P ∈ massRegion (massSum m k)) : manyMeasure m k P univ < ∞ :=
  manyMeasure_univ_lt_top m hm k hP

example (L : orthochronousLorentzGroup 3) :
    ∀ (k : ℕ) (x : Config k), act m L⁻¹ k (act m L k x) = x :=
  act_inv_act m L

example (hm : ∀ i, 0 ≤ m i) (k : ℕ) {p₁ p₂ : MinkowskiModel 3}
    (hP : p₁ + p₂ ∈ massRegion (massSum m k)) (L : orthochronousLorentzGroup 3)
    {W W' : Config k → ℝ} (hW : ∀ x, W' (act m L k x) = W x) (S : Set (Config k)) :
    manyCrossSection m k W' (L.val.val p₁) (L.val.val p₂) (act m L k '' S) =
      manyCrossSection m k W p₁ p₂ S :=
  manyCrossSection_covariant m hm k hP L hW S

example :
    ∃ p₁ p₂ : MinkowskiModel 3, 0 < fluxFactor p₁ p₂ ∧
      p₁ + p₂ ∈ massRegion (massSum (fun _ => 1) 1) ∧
      0 < manyCrossSection (fun _ => 1) 1 (fun _ => 1) p₁ p₂ univ ∧
      ∀ L : orthochronousLorentzGroup 3,
        manyCrossSection (fun _ => 1) 1 (fun _ => 1) (L.val.val p₁) (L.val.val p₂)
            (act (fun _ => 1) L 1 '' univ) =
          manyCrossSection (fun _ => 1) 1 (fun _ => 1) p₁ p₂ univ :=
  exists_manyCrossSection_pos

example (L : orthochronousLorentzGroup 3) (k : ℕ) : Config k ≃ᵐ Config k :=
  actEquiv m L k

example (L : orthochronousLorentzGroup 3) (k : ℕ) (x : Config k) :
    actEquiv m L k x = act m L k x :=
  rfl

example (k : ℕ) (P : MinkowskiModel 3) :
    manyMeasure m k P = Measure.map (phase m k P) ((base k).withDensity (weight m k P)) :=
  rfl

end ProjectAinos.SpecialRelativity.ManyBody
