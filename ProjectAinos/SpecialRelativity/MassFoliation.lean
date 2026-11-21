/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.TwoBodyCoarea
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The foliation of the future timelike momenta by mass shells

The momenta `Q` with a positive energy and a rest mass above `S ≥ 0` form the open set
`massRegion S`; for `S = 0` it is the open future timelike cone (`massRegion_zero`). It is
foliated by the future mass shells `M > S`, and the Lebesgue measure `d⁴Q` is

`d⁴Q = M dM · d³K/E_M(K)`, `E_M(K) = √(M² + |K|²)`

(`lintegral_massRegion_shell`, Landau–Lifshitz, *The Classical Theory of Fields*, §12): at a fixed
space momentum `K` the energy is substituted by `Q⁰ = √(M² + |K|²)`, of derivative `M/Q⁰`
(`hasDerivAt_energy_mass`), and then the order of the integrals is exchanged
(`lintegral_massRegion`).
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace ProjectAinos.SpecialRelativity.ManyBody

open SmoothGeometry SmoothGeometry.Minkowski FutureShell TwoBodyFibre

/-- The momenta with a positive energy and a rest mass above `S`. -/
def massRegion (S : ℝ) : Set (MinkowskiModel 3) :=
  {P | 0 < time P ∧ S ^ 2 < intervalQuadratic P}

theorem region_eq_massRegion (m₃ m₄ : ℝ) : region 3 m₃ m₄ = massRegion (m₃ + m₄) := rfl

theorem isOpen_massRegion (S : ℝ) : IsOpen (massRegion S) :=
  (isOpen_lt continuous_const time.continuous).inter
    (isOpen_lt continuous_const (pair.continuous₂.comp (continuous_id.prodMk continuous_id)))

theorem measurableSet_massRegion (S : ℝ) : MeasurableSet (massRegion S) :=
  (isOpen_massRegion S).measurableSet

/-- For `S = 0` the region is the open future timelike cone. -/
theorem massRegion_zero : massRegion 0 = {Q : MinkowskiModel 3 | FutureTimelike Q} := by
  ext Q
  simp only [massRegion, mem_ofPred_eq, futureTimelike_iff, Timelike]
  constructor
  · rintro ⟨ht, hQ⟩
    exact ⟨by simpa using hQ, ht⟩
  · rintro ⟨hQ, ht⟩
    exact ⟨ht, by simpa using hQ⟩

/-- The momentum `(t, K)` is in `massRegion S` if and only if `t > √(S² + |K|²)`. -/
theorem cons_mem_massRegion_iff (S t : ℝ) (K : Fin 3 → ℝ) :
    (Fin.cons t K : MinkowskiModel 3) ∈ massRegion S ↔
      t ∈ Ioi (Real.sqrt (S ^ 2 + ∑ i, K i ^ 2)) := by
  change 0 < t ∧ S ^ 2 < intervalQuadratic (Fin.cons t K : MinkowskiModel 3) ↔
    Real.sqrt (S ^ 2 + ∑ i, K i ^ 2) < t
  rw [FreeParticle.intervalQuadratic_cons]
  constructor
  · rintro ⟨ht, hQ⟩
    exact (Real.sqrt_lt' ht).mpr (by linarith)
  · intro ht
    have htpos : 0 < t := lt_of_le_of_lt (Real.sqrt_nonneg _) ht
    have h := (Real.sqrt_lt' htpos).mp ht
    exact ⟨htpos, by linarith⟩

/-- A point of the shell of mass `M` is in `massRegion S` for `0 ≤ S < M`. -/
theorem point_mem_massRegion {S M : ℝ} (hS : 0 ≤ S) (hM : S < M) (K : Fin 3 → ℝ) :
    point M K ∈ massRegion S := by
  have hdom : K ∈ domain 3 M := by
    rw [domain_eq_univ (by linarith : M ≠ 0)]
    exact mem_univ K
  refine ⟨(point_mem hdom).2, ?_⟩
  rw [(point_mem hdom).1]
  nlinarith

/-- The rest mass of a point of the shell of mass `M ≥ 0` is `M`. -/
theorem invariantMass_point {M : ℝ} (hM : 0 < M) (K : Fin 3 → ℝ) :
    invariantMass (point M K) = M := by
  have hdom : K ∈ domain 3 M := by
    rw [domain_eq_univ hM.ne']
    exact mem_univ K
  rw [invariantMass, properSpeed, (point_mem hdom).1, Real.sqrt_sq hM.le]

/-! ### The energy as a function of the mass -/

theorem continuous_energy_mass :
    Continuous fun z : ℝ × (Fin 3 → ℝ) => energy z.1 z.2 :=
  Real.continuous_sqrt.comp ((continuous_fst.pow 2).add (continuous_sum_sq.comp continuous_snd))

theorem measurable_point_mass : Measurable fun z : ℝ × (Fin 3 → ℝ) => point z.1 z.2 := by
  have h : Measurable fun z : ℝ × (Fin 3 → ℝ) =>
      (Fin.cons (energy z.1 z.2) z.2 : MinkowskiModel 3) :=
    measurable_cons.comp (continuous_energy_mass.measurable.prodMk measurable_snd)
  exact h

/-- The derivative of the energy `√(M² + |K|²)` in the mass: `M/E`. -/
theorem hasDerivAt_energy_mass (K : Fin 3 → ℝ) {M : ℝ} (hM : 0 < M) :
    HasDerivAt (fun M : ℝ => energy M K) (M / energy M K) M := by
  have hs := sum_sq_nonneg K
  have hpos : 0 < M ^ 2 + ∑ i, K i ^ 2 := by positivity
  have h1 : HasDerivAt (fun M : ℝ => M ^ 2 + ∑ i, K i ^ 2) (2 * M) M := by
    simpa using (hasDerivAt_pow 2 M).add_const (∑ i, K i ^ 2)
  refine (h1.sqrt hpos.ne').congr_deriv ?_
  have hE : 0 < Real.sqrt (M ^ 2 + ∑ i, K i ^ 2) := Real.sqrt_pos.mpr hpos
  rw [energy]
  field_simp

theorem strictMonoOn_energy_mass (K : Fin 3 → ℝ) {S : ℝ} (hS : 0 ≤ S) :
    StrictMonoOn (fun M : ℝ => energy M K) (Ioi S) := by
  intro a ha b hb hab
  have ha' : 0 ≤ a := le_trans hS (le_of_lt ha)
  exact Real.sqrt_lt_sqrt (add_nonneg (sq_nonneg a) (sum_sq_nonneg K)) (by nlinarith)

theorem image_energy_mass (K : Fin 3 → ℝ) {S : ℝ} (hS : 0 ≤ S) :
    (fun M : ℝ => energy M K) '' Ioi S = Ioi (Real.sqrt (S ^ 2 + ∑ i, K i ^ 2)) := by
  have hs := sum_sq_nonneg K
  ext t
  constructor
  · rintro ⟨M, hM, rfl⟩
    have hM' : S < M := hM
    exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  · intro ht
    have ht' : Real.sqrt (S ^ 2 + ∑ i, K i ^ 2) < t := ht
    have htpos : 0 < t := lt_of_le_of_lt (Real.sqrt_nonneg _) ht'
    have ht2 : S ^ 2 + ∑ i, K i ^ 2 < t ^ 2 := (Real.sqrt_lt' htpos).mp ht'
    have hM : S < Real.sqrt (t ^ 2 - ∑ i, K i ^ 2) := (Real.lt_sqrt hS).mpr (by linarith)
    refine ⟨Real.sqrt (t ^ 2 - ∑ i, K i ^ 2), hM, ?_⟩
    change Real.sqrt (Real.sqrt (t ^ 2 - ∑ i, K i ^ 2) ^ 2 + ∑ i, K i ^ 2) = t
    rw [Real.sq_sqrt (by nlinarith [sq_nonneg S]), sub_add_cancel, Real.sqrt_sq htpos.le]

/-! ### The foliation -/

/-- **The foliation by mass shells** in the Lebesgue measure:
`∫_{Q⁰ > 0, M_Q > S} h d⁴Q = ∫_{M > S} ∫ (M/E_M(K)) h(E_M(K), K) d³K dM`. -/
theorem lintegral_massRegion {S : ℝ} (hS : 0 ≤ S) {h : MinkowskiModel 3 → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ Q in massRegion S, h Q =
      ∫⁻ M in Ioi S, ∫⁻ K, ENNReal.ofReal (M / energy M K) * h (point M K) := by
  rw [← lintegral_indicator (measurableSet_massRegion S),
    lintegral_minkowski (hh.indicator (measurableSet_massRegion S))]
  have h1 : ∀ K : Fin 3 → ℝ, ∫⁻ t, (massRegion S).indicator h (Fin.cons t K) =
      ∫⁻ M in Ioi S, ENNReal.ofReal (M / energy M K) * h (point M K) := by
    intro K
    have hind : (fun t : ℝ => (massRegion S).indicator h (Fin.cons t K)) =
        (Ioi (Real.sqrt (S ^ 2 + ∑ i, K i ^ 2))).indicator
          (fun t : ℝ => h (Fin.cons t K : MinkowskiModel 3)) := by
      funext t
      by_cases ht : (Fin.cons t K : MinkowskiModel 3) ∈ massRegion S
      · rw [indicator_of_mem ht, indicator_of_mem ((cons_mem_massRegion_iff S t K).mp ht)]
      · rw [indicator_of_notMem ht,
          indicator_of_notMem (fun h' => ht ((cons_mem_massRegion_iff S t K).mpr h'))]
    rw [hind, lintegral_indicator measurableSet_Ioi, ← image_energy_mass K hS,
      lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
        (fun M hM => (hasDerivAt_energy_mass K
          (lt_of_le_of_lt hS hM)).hasDerivWithinAt) (strictMonoOn_energy_mass K hS).injOn]
    refine setLIntegral_congr_fun measurableSet_Ioi fun M hM => ?_
    have hM' : 0 < M := lt_of_le_of_lt hS hM
    have hE : 0 < energy M K := Real.sqrt_pos.mpr (by
      have := sum_sq_nonneg K
      positivity)
    rw [abs_of_pos (div_pos hM' hE)]
    rfl
  rw [lintegral_congr h1]
  have hm : Measurable fun z : (Fin 3 → ℝ) × ℝ =>
      ENNReal.ofReal (z.2 / energy z.2 z.1) * h (point z.2 z.1) := by
    have hsw : Measurable fun z : (Fin 3 → ℝ) × ℝ => (z.2, z.1) :=
      measurable_snd.prodMk measurable_fst
    have he : Measurable fun z : (Fin 3 → ℝ) × ℝ => energy z.2 z.1 :=
      continuous_energy_mass.measurable.comp hsw
    have hp : Measurable fun z : (Fin 3 → ℝ) × ℝ => point z.2 z.1 :=
      measurable_point_mass.comp hsw
    exact (ENNReal.measurable_ofReal.comp (measurable_snd.div he)).mul (hh.comp hp)
  exact lintegral_lintegral_swap hm.aemeasurable

/-- **`d⁴Q = M dM · d³K/E_M(K)`**: the foliation by the shell measures of `FutureShell.measure`. -/
theorem lintegral_massRegion_shell {S : ℝ} (hS : 0 ≤ S) {h : MinkowskiModel 3 → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ Q in massRegion S, h Q =
      ∫⁻ M in Ioi S, ENNReal.ofReal M * ∫⁻ K, h (point M K) ∂(FutureShell.measure 3 M) := by
  rw [lintegral_massRegion hS hh]
  refine setLIntegral_congr_fun measurableSet_Ioi fun M hM => ?_
  have hM' : 0 < M := lt_of_le_of_lt hS hM
  have hp : Measurable fun K : Fin 3 → ℝ => h (point M K) := hh.comp continuous_point.measurable
  rw [FutureShell.measure, domain_eq_univ hM'.ne', Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul _ measurable_density hp,
    ← lintegral_const_mul _ (measurable_density.mul hp)]
  refine lintegral_congr fun K => ?_
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hM'.le, div_eq_mul_inv]

/-- The foliation of the open future timelike cone: `d⁴Q = M dM · d³K/E_M(K)` for `M > 0`. -/
theorem lintegral_futureTimelike {h : MinkowskiModel 3 → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ Q in {Q : MinkowskiModel 3 | FutureTimelike Q}, h Q =
      ∫⁻ M in Ioi 0, ENNReal.ofReal M * ∫⁻ K, h (point M K) ∂(FutureShell.measure 3 M) := by
  rw [← massRegion_zero]
  exact lintegral_massRegion_shell le_rfl hh

end ProjectAinos.SpecialRelativity.ManyBody
