/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SpecialRelativity.TwoBodyCoarea

/-! Public consumers of the measure of the final states of two particles at a fixed total
momentum: polar co-ordinates for nonnegative functions, the rest frame and the fibre over a
regular total momentum, the measure of the fibre with its covariance and the cross-section of two
outgoing particles, and the integration formula that identifies the measure of the fibre as the
constrained product of the two shell measures.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace ProjectAinos.SmoothGeometry.Sphere

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {F : E → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂μ = ∫⁻ n, (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * F (r • (n : E))) ∂μ.toSphere :=
  lintegral_eq_lintegral_sphere_Ioi μ hF

example {n : ℕ} [NeZero n] {F : (Fin n → ℝ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ e : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ (n - 1)) * F (r • WithLp.ofLp (e : EuclideanSpace ℝ (Fin n))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere :=
  lintegral_pi_eq_lintegral_sphere_Ioi hF

end ProjectAinos.SmoothGeometry.Sphere

namespace ProjectAinos.SpecialRelativity.TwoBodyFibre

open SmoothGeometry SmoothGeometry.Minkowski FutureShell FreeParticle

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {d : ℕ} {m₃ m₄ : ℝ} {P : MinkowskiModel 3}

example {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (h : m₃ + m₄ < M) :
    0 < kallen (M ^ 2) (m₃ ^ 2) (m₄ ^ 2) :=
  kallen_sq_pos hm₃ hm₄ h

example {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (h : m₃ + m₄ < M) :
    0 < restMomentum m₃ m₄ M :=
  restMomentum_pos hm₃ hm₄ h

example {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (h : m₃ + m₄ < M) :
    restMomentum m₃ m₄ M ^ 2 = kallen (M ^ 2) (m₃ ^ 2) (m₄ ^ 2) / (4 * M ^ 2) :=
  restMomentum_sq hm₃ hm₄ h

example {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (h : m₃ + m₄ < M) :
    Real.sqrt (m₃ ^ 2 + restMomentum m₃ m₄ M ^ 2) = (M ^ 2 + m₃ ^ 2 - m₄ ^ 2) / (2 * M) :=
  sqrt_restEnergy_first hm₃ hm₄ h

example {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (h : m₃ + m₄ < M) :
    Real.sqrt (m₄ ^ 2 + restMomentum m₃ m₄ M ^ 2) = (M ^ 2 + m₄ ^ 2 - m₃ ^ 2) / (2 * M) :=
  sqrt_restEnergy_second hm₃ hm₄ h

example {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    (h : m₃ + m₄ < M) :
    Real.sqrt (m₃ ^ 2 + restMomentum m₃ m₄ M ^ 2) +
      Real.sqrt (m₄ ^ 2 + restMomentum m₃ m₄ M ^ 2) = M :=
  sqrt_add_sqrt_restMomentum hm₃ hm₄ h

example {m₃ m₄ r : ℝ} (hr : 0 ≤ r) :
    restMomentum m₃ m₄ (Real.sqrt (m₃ ^ 2 + r ^ 2) + Real.sqrt (m₄ ^ 2 + r ^ 2)) = r :=
  restMomentum_sqrt_add_sqrt hr

example {m₃ m₄ r : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hr : 0 < r) :
    m₃ + m₄ < Real.sqrt (m₃ ^ 2 + r ^ 2) + Real.sqrt (m₄ ^ 2 + r ^ 2) :=
  add_lt_sqrt_add_sqrt hm₃ hm₄ hr

example (k : Fin d → ℝ) : 0 ≤ ∑ i, k i ^ 2 :=
  sum_sq_nonneg k

example {k : Fin d → ℝ} (hk : k ≠ 0) : 0 < ∑ i, k i ^ 2 :=
  sum_sq_pos hk

example (k : Fin d → ℝ) : ∑ i, (-k) i ^ 2 = ∑ i, k i ^ 2 :=
  sum_neg_sq k

example (k K : Fin d → ℝ) (c : ℝ) :
    ∑ i, (k + c • K) i ^ 2 =
      ∑ i, k i ^ 2 + 2 * c * ∑ i, K i * k i + c ^ 2 * ∑ i, K i ^ 2 :=
  sum_add_smul_sq k K c

example (K k : Fin d → ℝ) :
    (∑ i, K i * k i) ^ 2 ≤ (∑ i, K i ^ 2) * ∑ i, k i ^ 2 :=
  sq_sum_mul_le K k

example (m : ℝ) (k : Fin d → ℝ) : energy m (-k) = energy m k :=
  energy_neg m k

example (m : ℝ) (k : Fin d → ℝ) : 0 ≤ energy m k :=
  energy_nonneg m k

example (m : ℝ) (k : Fin d → ℝ) : energy m k ^ 2 = m ^ 2 + ∑ i, k i ^ 2 :=
  energy_sq' m k

example (m : ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) : k ∈ domain d m :=
  mem_domain_of_ne_zero m hk

example {P : MinkowskiModel d} (hP : FutureTimelike P) :
    0 < invariantMass P :=
  invariantMass_pos hP

example {P : MinkowskiModel d} (hP : FutureTimelike P) :
    (restVelocity P).val = (time P)⁻¹ • space P :=
  restVelocity_val hP

example {P : MinkowskiModel d} (hP : FutureTimelike P) :
    (restVelocity P).gamma = time P / invariantMass P :=
  gamma_restVelocity hP

example {P : MinkowskiModel d} (hP : FutureTimelike P) :
    (labBoost P).val.val (invariantMass P • timeAxis d) = P :=
  labBoost_apply_rest hP

example {P : MinkowskiModel d} (hP : FutureTimelike P) (m : ℝ)
    (k : Fin d → ℝ) : action m (labBoost P) k = labSpace P (energy m k) k :=
  action_labBoost hP m k

example {P : MinkowskiModel d} (hM : 0 < invariantMass P) (hT : 0 < time P)
    (hQ : time P ^ 2 = invariantMass P ^ 2 + ∑ i, spaceMomentum P i ^ 2) {m E : ℝ}
    {k : Fin d → ℝ} (hE : E ^ 2 = m ^ 2 + ∑ i, k i ^ 2)
    (hpos : 0 ≤ time P * E + ∑ i, spaceMomentum P i * k i) :
    energy m (labSpace P E k) =
      (time P * E + ∑ i, spaceMomentum P i * k i) / invariantMass P :=
  energy_labSpace hM hT hQ hE hpos

example (k : Fin d → ℝ) : 0 ≤ pairMass m₃ m₄ k :=
  pairMass_nonneg k

example (m : ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) : 0 < energy m k :=
  energy_pos_of_ne_zero m hk

example {k : Fin d → ℝ} (hk : k ≠ 0) : 0 < pairMass m₃ m₄ k :=
  pairMass_pos hk

example (m : ℝ) (k : Fin d → ℝ) :
    energy m k = Real.sqrt (m ^ 2 + Real.sqrt (∑ i, k i ^ 2) ^ 2) :=
  energy_eq_sqrt m k

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) {k : Fin d → ℝ} (hk : k ≠ 0) :
    m₃ + m₄ < pairMass m₃ m₄ k :=
  add_lt_pairMass hm₃ hm₄ hk

example (k : Fin d → ℝ) :
    restMomentum m₃ m₄ (pairMass m₃ m₄ k) = Real.sqrt (∑ i, k i ^ 2) :=
  restMomentum_pairMass k

example (K k : Fin d → ℝ) :
    time (totalOf m₃ m₄ K k) = Real.sqrt (pairMass m₃ m₄ k ^ 2 + ∑ i, K i ^ 2) :=
  time_totalOf K k

example (K k : Fin d → ℝ) : spaceMomentum (totalOf m₃ m₄ K k) = K :=
  spaceMomentum_totalOf K k

example (K k : Fin d → ℝ) :
    intervalQuadratic (totalOf m₃ m₄ K k) = pairMass m₃ m₄ k ^ 2 :=
  intervalQuadratic_totalOf K k

example (K k : Fin d → ℝ) :
    invariantMass (totalOf m₃ m₄ K k) = pairMass m₃ m₄ k :=
  invariantMass_totalOf K k

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : 0 < pairMass m₃ m₄ k) :
    FutureTimelike (totalOf m₃ m₄ K k) :=
  futureTimelike_totalOf K hk

example (K k : Fin d → ℝ) :
    labFirst m₃ m₄ K k = k + ((∑ i, K i * k i) / (pairMass m₃ m₄ k * (pairMass m₃ m₄ k +
      Real.sqrt (pairMass m₃ m₄ k ^ 2 + ∑ i, K i ^ 2))) + energy m₃ k / pairMass m₃ m₄ k) • K :=
  labFirst_eq K k

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : 0 < pairMass m₃ m₄ k) :
    K - labFirst m₃ m₄ K k = labSpace (totalOf m₃ m₄ K k) (energy m₄ k) (-k) :=
  sub_labFirst K hk

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : 0 < pairMass m₃ m₄ k) :
    labFirst m₃ m₄ K k = action m₃ (labBoost (totalOf m₃ m₄ K k)) k :=
  labFirst_eq_action K hk

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : 0 < pairMass m₃ m₄ k) :
    K - labFirst m₃ m₄ K k = action m₄ (labBoost (totalOf m₃ m₄ K k)) (-k) :=
  sub_labFirst_eq_action K hk

example (k : Fin d → ℝ) :
    point m₃ k + point m₄ (-k) = pairMass m₃ m₄ k • timeAxis d :=
  point_add_point_neg k

example : Continuous (total (d := d) m₃ m₄) :=
  continuous_total

example : IsOpen (region d m₃ m₄) :=
  isOpen_region

example : IsOpen (regular d m₃ m₄) :=
  isOpen_regular

example : MeasurableSet (region d m₃ m₄) :=
  measurableSet_region

example : MeasurableSet (regular d m₃ m₄) :=
  measurableSet_regular

example {P : MinkowskiModel d} (hP : P ∈ region d m₃ m₄) :
    FutureTimelike P :=
  futureTimelike_of_mem_region hP

example {P : MinkowskiModel d} (hP : P ∈ region d m₃ m₄) :
    intervalQuadratic P = invariantMass P ^ 2 :=
  intervalQuadratic_eq_sq hP

example {P : MinkowskiModel d} (hP : P ∈ region d m₃ m₄) :
    time P ^ 2 = invariantMass P ^ 2 + ∑ i, spaceMomentum P i ^ 2 :=
  time_sq_of_mem_region hP

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) {P : MinkowskiModel d}
    (hP : P ∈ region d m₃ m₄) : m₃ + m₄ < invariantMass P :=
  add_lt_invariantMass hm₃ hm₄ hP

example (L : orthochronousLorentzGroup d) {P : MinkowskiModel d}
    (hP : P ∈ region d m₃ m₄) : L.val.val P ∈ region d m₃ m₄ :=
  lorentz_mem_region L hP

example (L : orthochronousLorentzGroup d) (P : MinkowskiModel d) :
    invariantMass (L.val.val P) = invariantMass P :=
  invariantMass_lorentz' L P

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (K : Fin d → ℝ) {k : Fin d → ℝ}
    (hk : k ≠ 0) : totalOf m₃ m₄ K k ∈ region d m₃ m₄ :=
  totalOf_mem_region hm₃ hm₄ K hk

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    total m₃ m₄ (labFirst m₃ m₄ K k, K - labFirst m₃ m₄ K k) = totalOf m₃ m₄ K k :=
  total_labFirst K hk

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    labFirst m₃ m₄ K k ∈ domain d m₃ :=
  labFirst_mem_domain K hk

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    K - labFirst m₃ m₄ K k ∈ domain d m₄ :=
  sub_labFirst_mem_domain K hk

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    (labFirst m₃ m₄ K k, K - labFirst m₃ m₄ K k) ∈ fibre m₃ m₄ (totalOf m₃ m₄ K k) :=
  labFirst_mem_fibre K hk

example {P : MinkowskiModel d} (hP : FutureTimelike P)
    {x : (Fin d → ℝ) × (Fin d → ℝ)} (hx : x ∈ fibre m₃ m₄ P) :
    action m₄ (labBoost P)⁻¹ x.2 = -action m₃ (labBoost P)⁻¹ x.1 ∧
      pairMass m₃ m₄ (action m₃ (labBoost P)⁻¹ x.1) = invariantMass P :=
  rest_of_mem_fibre hP hx

example {m : ℝ} (L : orthochronousLorentzGroup d) {π : Fin d → ℝ}
    (hπ : π ∈ domain d m) : action m L (action m L⁻¹ π) = π :=
  action_action_inv L hπ

example {m : ℝ} (L : orthochronousLorentzGroup d) {π : Fin d → ℝ}
    (hπ : π ∈ domain d m) : action m L⁻¹ (action m L π) = π :=
  action_inv_action L hπ

example (c : ℝ) (v : Fin d → ℝ) : ∑ i, (c • v) i ^ 2 = c ^ 2 * ∑ i, v i ^ 2 :=
  sum_smul_sq c v

example : Continuous (pairMass (d := d) m₃ m₄) :=
  continuous_pairMass

example : Continuous fun K : Fin d → ℝ => ∑ i, K i ^ 2 :=
  continuous_sum_sq

example : Continuous fun z : (Fin d → ℝ) × (Fin d → ℝ) => ∑ i, z.1 i * z.2 i :=
  continuous_dot

example :
    Measurable fun z : (Fin d → ℝ) × (Fin d → ℝ) => labFirst m₃ m₄ z.1 z.2 :=
  measurable_labFirst

example :
    Continuous fun M : ℝ => Real.sqrt (kallen (M ^ 2) (m₃ ^ 2) (m₄ ^ 2)) :=
  continuous_restMomentum_num

example : Measurable (restMomentum m₃ m₄) :=
  measurable_restMomentum

example : Continuous (invariantMass (d := d)) :=
  continuous_invariantMass

example (n : sphere (0 : E3) 1) : ∑ i, sphereVec n i ^ 2 = 1 :=
  sum_sphereVec_sq n

example : Continuous sphereVec :=
  continuous_sphereVec

example :
    Measurable fun z : MinkowskiModel 3 × sphere (0 : E3) 1 => fibrePair m₃ m₄ z.1 z.2 :=
  measurable_fibrePair

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (n : sphere (0 : E3) 1) : restMomentum m₃ m₄ (invariantMass P) • sphereVec n ≠ 0 :=
  restVec_ne_zero hm₃ hm₄ hP n

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (n : sphere (0 : E3) 1) :
    pairMass m₃ m₄ (restMomentum m₃ m₄ (invariantMass P) • sphereVec n) = invariantMass P :=
  pairMass_restVec hm₃ hm₄ hP n

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (n : sphere (0 : E3) 1) :
    totalOf m₃ m₄ (spaceMomentum P) (restMomentum m₃ m₄ (invariantMass P) • sphereVec n) = P :=
  totalOf_restVec hm₃ hm₄ hP n

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (n : sphere (0 : E3) 1) :
    fibrePair m₃ m₄ P n =
      (action m₃ (labBoost P) (restMomentum m₃ m₄ (invariantMass P) • sphereVec n),
        action m₄ (labBoost P) (-(restMomentum m₃ m₄ (invariantMass P) • sphereVec n))) :=
  fibrePair_eq_action hm₃ hm₄ hP n

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (n : sphere (0 : E3) 1) : fibrePair m₃ m₄ P n ∈ fibre m₃ m₄ P :=
  fibrePair_mem_fibre hm₃ hm₄ hP n

example (hP : P ∈ region 3 m₃ m₄)
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hx : x ∈ fibre m₃ m₄ P) :
    ∑ i, (action m₃ (labBoost P)⁻¹ x.1) i ^ 2 = restMomentum m₃ m₄ (invariantMass P) ^ 2 :=
  sum_sq_rest_of_mem_fibre hP hx

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hx : x ∈ fibre m₃ m₄ P) :
    fibreDirection m₃ m₄ P x ∈ sphere (0 : E3) 1 :=
  fibreDirection_mem_sphere hm₃ hm₄ hP hx

example (hP : P ∈ region 3 m₃ m₄) {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hx : x ∈ fibre m₃ m₄ P) :
    TwoBodyDecay P (point m₃ x.1) (point m₄ x.2) (invariantMass P) m₃ m₄ :=
  twoBodyDecay_of_mem_fibre hP hx

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hx : x ∈ fibre m₃ m₄ P) :
    (twoBodyDecay_of_mem_fibre hP hx).restFrame.restForm
        (observerMomentum (twoBodyDecay_of_mem_fibre hP hx).restFrame (point m₃ x.1))
        (observerMomentum (twoBodyDecay_of_mem_fibre hP hx).restFrame (point m₃ x.1)) =
      restMomentum m₃ m₄ (invariantMass P) ^ 2 :=
  restForm_of_mem_fibre hm₃ hm₄ hP hx

example (P : MinkowskiModel 3) : Measurable (fibrePair m₃ m₄ P) :=
  measurable_fibrePair_right P

example (P : MinkowskiModel 3)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(fibreMeasure m₃ m₄ P) =
      ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P) *
        ∫⁻ n, f (fibrePair m₃ m₄ P n) ∂Sphere.sphereMeasure :=
  lintegral_fibreMeasure P hf

example : Sphere.sphereMeasure univ = ENNReal.ofReal (4 * Real.pi) :=
  sphereMeasure_univ

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄) :
    fibreMeasure m₃ m₄ P univ =
      ENNReal.ofReal (4 * Real.pi * restMomentum m₃ m₄ (invariantMass P) / invariantMass P) :=
  fibreMeasure_univ hm₃ hm₄ hP

example (P : MinkowskiModel 3) : MeasurableSet (fibre m₃ m₄ P) :=
  measurableSet_fibre P

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄) :
    fibreMeasure m₃ m₄ P (fibre m₃ m₄ P)ᶜ = 0 :=
  fibreMeasure_compl_fibre hm₃ hm₄ hP

example {R : LorentzGroup 3} (hR : R ∈ rotationGroup 3)
    (n : sphere (0 : E3) 1) :
    sphereVec (Sphere.sphereMap (rotationIsometry hR) n) = spaceLinear R (sphereVec n) :=
  sphereVec_sphereMap hR n

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (L : orthochronousLorentzGroup 3) (hL : L.val.val (invariantMass P • timeAxis 3) = P) :
    fibreMeasure m₃ m₄ P =
      ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P) •
        Measure.map (fun n => (action m₃ L (restMomentum m₃ m₄ (invariantMass P) • sphereVec n),
          action m₄ L (-(restMomentum m₃ m₄ (invariantMass P) • sphereVec n))))
          Sphere.sphereMeasure :=
  fibreMeasure_eq_of_apply hm₃ hm₄ hP L hL

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (L : orthochronousLorentzGroup 3) :
    Measure.map (Prod.map (action m₃ L) (action m₄ L)) (fibreMeasure m₃ m₄ P) =
      fibreMeasure m₃ m₄ (L.val.val P) :=
  map_fibreMeasure hm₃ hm₄ hP L

example {d : ℕ} {m : ℝ} (L : orthochronousLorentzGroup d)
    {π : Fin d → ℝ} (hπ : π ∉ domain d m) : action m L π = π :=
  action_of_notMem_domain L hπ

example {d : ℕ} {m : ℝ} (L : orthochronousLorentzGroup d)
    (π : Fin d → ℝ) : action m L⁻¹ (action m L π) = π :=
  action_inv_action' L π

example (L : orthochronousLorentzGroup 3) :
    MeasurableEmbedding (Prod.map (action m₃ L) (action m₄ L)) :=
  measurableEmbedding_prodMap_action L

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α}
    {φ : α → β} (hφ : MeasurableEmbedding φ) {W : α → ℝ} {W' : β → ℝ}
    (hW : ∀ y, W' (φ y) = W y) (F : ℝ) (S : Set α) :
    crossSection (Measure.map φ ν) W' F (φ '' S) = crossSection ν W F S :=
  crossSection_map hφ hW F S

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    {p₁ p₂ : MinkowskiModel 3} (hP : p₁ + p₂ ∈ region 3 m₃ m₄) (L : orthochronousLorentzGroup 3)
    {W W' : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    (hW : ∀ x, W' (Prod.map (action m₃ L) (action m₄ L) x) = W x)
    (S : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ))) :
    twoBodyCrossSection m₃ m₄ W' (L.val.val p₁) (L.val.val p₂)
        (Prod.map (action m₃ L) (action m₄ L) '' S) =
      twoBodyCrossSection m₃ m₄ W p₁ p₂ S :=
  twoBodyCrossSection_covariant hm₃ hm₄ hP L hW S

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    {p₁ p₂ : MinkowskiModel 3} (hP : p₁ + p₂ ∈ region 3 m₃ m₄) (c : ℝ) :
    twoBodyCrossSection m₃ m₄ (fun _ => c) p₁ p₂ univ =
      (4 * fluxFactor p₁ p₂)⁻¹ * (4 * Real.pi * restMomentum m₃ m₄ (invariantMass (p₁ + p₂)) /
        invariantMass (p₁ + p₂) * c) :=
  twoBodyCrossSection_const_univ hm₃ hm₄ hP c

example :
    ∃ (p₁ p₂ : MinkowskiModel 3) (β : Velocity 3), β ≠ Velocity.zero 3 ∧
      0 < fluxFactor p₁ p₂ ∧ p₁ + p₂ ∈ region 3 1 1 ∧
      0 < twoBodyCrossSection 1 1 (fun _ => 1) p₁ p₂ univ ∧
      twoBodyCrossSection 1 1 (fun _ => 1) ((boost β).val p₁) ((boost β).val p₂)
          (Prod.map (action 1 (boostOrthochronous β)) (action 1 (boostOrthochronous β)) '' univ) =
        twoBodyCrossSection 1 1 (fun _ => 1) p₁ p₂ univ :=
  exists_twoBodyCrossSection_covariant

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {f' : E →L[ℝ] ℝ} {x : E} (hf : HasFDerivAt f f' x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => (f y)⁻¹) (-(f x ^ 2)⁻¹ • f') x :=
  hasFDerivAt_inv_comp hf hx

example (a b : ℝ) (K k w : Fin d → ℝ) :
    dotCovector (a • K + b • k) w = a * ∑ i, K i * w i + b * ∑ i, k i * w i :=
  dotCovector_smul_add_smul a b K k w

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    HasFDerivAt (labFirst m₃ m₄ K) (labDeriv m₃ m₄ K k) k :=
  hasFDerivAt_labFirst K hk

example (K k : Fin d → ℝ) :
    time (totalOf m₃ m₄ K k) ^ 2 = pairMass m₃ m₄ k ^ 2 + ∑ i, K i ^ 2 :=
  time_totalOf_sq K k

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    0 < time (totalOf m₃ m₄ K k) :=
  time_totalOf_pos K hk

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) (m : ℝ) :
    |∑ i, K i * k i| < time (totalOf m₃ m₄ K k) * energy m k :=
  abs_dot_lt K hk m

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    energy m₃ (labFirst m₃ m₄ K k) =
      (time (totalOf m₃ m₄ K k) * energy m₃ k + ∑ i, K i * k i) / pairMass m₃ m₄ k :=
  energy_labFirst K hk

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    energy m₄ (K - labFirst m₃ m₄ K k) =
      (time (totalOf m₃ m₄ K k) * energy m₄ k - ∑ i, K i * k i) / pairMass m₃ m₄ k :=
  energy_sub_labFirst K hk

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    (labDeriv m₃ m₄ K k).det =
      (time (totalOf m₃ m₄ K k) * energy m₃ k + ∑ i, K i * k i) *
        (time (totalOf m₃ m₄ K k) * energy m₄ k - ∑ i, K i * k i) /
      (pairMass m₃ m₄ k * time (totalOf m₃ m₄ K k) * energy m₃ k * energy m₄ k) :=
  det_labDeriv K hk

example (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    ENNReal.ofReal |(labDeriv m₃ m₄ K k).det| *
        (ENNReal.ofReal (energy m₃ (labFirst m₃ m₄ K k))⁻¹ *
          ENNReal.ofReal (energy m₄ (K - labFirst m₃ m₄ K k))⁻¹) =
      ENNReal.ofReal (pairMass m₃ m₄ k /
        (time (totalOf m₃ m₄ K k) * energy m₃ k * energy m₄ k)) :=
  jacobian_mul_density K hk

example (K : Fin d → ℝ) : InjOn (labFirst m₃ m₄ K) {k | k ≠ 0} :=
  injOn_labFirst K

example (K : Fin d → ℝ) : MeasurableSet (regSlice d m₃ m₄ K) :=
  measurableSet_regSlice K

example (x : (Fin d → ℝ) × (Fin d → ℝ)) :
    spaceMomentum (total m₃ m₄ x) = x.1 + x.2 :=
  spaceMomentum_total x

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) : pairMass m₃ m₄ (0 : Fin d → ℝ) = m₃ + m₄ :=
  pairMass_zero hm₃ hm₄

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (K : Fin d → ℝ) :
    labFirst m₃ m₄ K '' {k | k ≠ 0} = regSlice d m₃ m₄ K :=
  image_labFirst hm₃ hm₄ K

example : Measurable (pairDensity (d := d) m₃ m₄) :=
  measurable_pairDensity

example (K : Fin d → ℝ) :
    Continuous fun k : Fin d → ℝ => time (totalOf m₃ m₄ K k) :=
  continuous_time_totalOf K

example (K : Fin d → ℝ) : Measurable (restWeight (d := d) m₃ m₄ K) :=
  measurable_restWeight K

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (K : Fin 3 → ℝ)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} :
    ∫⁻ π, (regular 3 m₃ m₄).indicator (fun x => f x * pairDensity m₃ m₄ x) (π, K - π) =
      ∫⁻ k, restWeight m₃ m₄ K k * f (labFirst m₃ m₄ K k, K - labFirst m₃ m₄ K k) :=
  lintegral_slice hm₃ hm₄ K

example (m r : ℝ) (n : sphere (0 : E3) 1) :
    energy m (r • sphereVec n) = Real.sqrt (m ^ 2 + r ^ 2) :=
  energy_smul_sphereVec m r n

example (r : ℝ) (n : sphere (0 : E3) 1) :
    pairMass m₃ m₄ (r • sphereVec n) = radialMass m₃ m₄ r :=
  pairMass_smul_sphereVec r n

example (K : Fin 3 → ℝ) (r : ℝ) (n : sphere (0 : E3) 1) :
    totalOf m₃ m₄ K (r • sphereVec n) =
      (Fin.cons (radialEnergy m₃ m₄ (∑ i, K i ^ 2) r) K : MinkowskiModel 3) :=
  totalOf_smul_sphereVec K r n

example (m : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r : ℝ => Real.sqrt (m ^ 2 + r ^ 2)) (r / Real.sqrt (m ^ 2 + r ^ 2)) r :=
  hasDerivAt_sqrt_sq_add m hr

example {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) :
    HasDerivAt (radialEnergy m₃ m₄ s)
      (r * radialMass m₃ m₄ r ^ 2 / (radialEnergy m₃ m₄ s r * Real.sqrt (m₃ ^ 2 + r ^ 2) *
        Real.sqrt (m₄ ^ 2 + r ^ 2))) r :=
  hasDerivAt_radialEnergy hs hr

example {m a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Real.sqrt (m ^ 2 + a ^ 2) < Real.sqrt (m ^ 2 + b ^ 2) :=
  sqrt_sq_add_lt ha hab

example {s : ℝ} (hs : 0 ≤ s) :
    StrictMonoOn (radialEnergy m₃ m₄ s) (Ioi 0) :=
  strictMonoOn_radialEnergy hs

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) {s : ℝ} (hs : 0 ≤ s) :
    radialEnergy m₃ m₄ s '' Ioi 0 = Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + s)) :=
  image_radialEnergy hm₃ hm₄ hs

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (K : Fin 3 → ℝ) (n : sphere (0 : E3) 1)
    (f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * (restWeight m₃ m₄ K (r • sphereVec n) *
        f (labFirst m₃ m₄ K (r • sphereVec n), K - labFirst m₃ m₄ K (r • sphereVec n))) =
      ∫⁻ t in Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + ∑ i, K i ^ 2)),
        ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass (Fin.cons t K : MinkowskiModel 3)) /
          invariantMass (Fin.cons t K : MinkowskiModel 3)) *
          f (fibrePair m₃ m₄ (Fin.cons t K) n) :=
  lintegral_radial hm₃ hm₄ K n f

example :
    Measurable fun z : ℝ × (Fin d → ℝ) => (Fin.cons z.1 z.2 : MinkowskiModel d) :=
  measurable_cons

example {F : MinkowskiModel d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ P, F P = ∫⁻ K : Fin d → ℝ, ∫⁻ t : ℝ, F (Fin.cons t K) :=
  lintegral_minkowski hF

example (t : ℝ) (K : Fin 3 → ℝ) :
    (Fin.cons t K : MinkowskiModel 3) ∈ region 3 m₃ m₄ ↔
      t ∈ Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + ∑ i, K i ^ 2)) :=
  cons_mem_region_iff t K

example (K : Fin d → ℝ) : Measurable (labFirst m₃ m₄ K) :=
  measurable_labFirst_right K

example :
    Measurable fun P : MinkowskiModel 3 =>
      ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P) :=
  measurable_fibreWeight

example {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f)
    (K : Fin 3 → ℝ) :
    Measurable fun z : ℝ × sphere (0 : E3) 1 => fibreIntegrand m₃ m₄ f K z.2 z.1 :=
  measurable_fibreIntegrand hf K

example (f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in regular 3 m₃ m₄, f x ∂((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)) =
      ∫⁻ x, (regular 3 m₃ m₄).indicator (fun x => f x * pairDensity m₃ m₄ x) x :=
  setLIntegral_prod_measure f hf

example {G : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x = ∫⁻ K, ∫⁻ π, G (π, K - π) :=
  lintegral_prod_sub hG

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (K : Fin 3 → ℝ)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ π, (regular 3 m₃ m₄).indicator (fun x => f x * pairDensity m₃ m₄ x) (π, K - π) =
      ∫⁻ n, (∫⁻ t in Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + ∑ i, K i ^ 2)),
        fibreIntegrand m₃ m₄ f K n t) ∂Sphere.sphereMeasure :=
  lintegral_slice_eq hm₃ hm₄ K hf

example {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f)
    (K : Fin 3 → ℝ) :
    ∫⁻ t, (region 3 m₃ m₄).indicator (fun P : MinkowskiModel 3 =>
        ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P) *
          ∫⁻ n, f (fibrePair m₃ m₄ P n) ∂Sphere.sphereMeasure) (Fin.cons t K) =
      ∫⁻ n, (∫⁻ t in Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + ∑ i, K i ^ 2)),
        fibreIntegrand m₃ m₄ f K n t) ∂Sphere.sphereMeasure :=
  lintegral_region_slice hf K

example {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ P in region 3 m₃ m₄, ∫⁻ x, f x ∂(fibreMeasure m₃ m₄ P) =
      ∫⁻ K : Fin 3 → ℝ, ∫⁻ n, (∫⁻ t in Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + ∑ i, K i ^ 2)),
        fibreIntegrand m₃ m₄ f K n t) ∂Sphere.sphereMeasure :=
  setLIntegral_region_eq hf

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in regular 3 m₃ m₄, f x ∂((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)) =
      ∫⁻ P in region 3 m₃ m₄, ∫⁻ x, f x ∂(fibreMeasure m₃ m₄ P) :=
  lintegral_regular_eq hm₃ hm₄ hf

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f)
    (hsupp : ∀ x ∉ regular 3 m₃ m₄, f x = 0) :
    ∫⁻ x, f x ∂((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)) =
      ∫⁻ P in region 3 m₃ m₄, ∫⁻ x, f x ∂(fibreMeasure m₃ m₄ P) :=
  lintegral_eq_of_support hm₃ hm₄ hf hsupp

example : Measurable (fibreMeasure m₃ m₄) :=
  measurable_fibreMeasure

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) :
    ((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)).restrict (regular 3 m₃ m₄) =
      (volume.restrict (region 3 m₃ m₄)).bind (fibreMeasure m₃ m₄) :=
  restrict_regular_eq_bind hm₃ hm₄

example {U W : MinkowskiModel d} (hU : 0 < intervalQuadratic U)
    (hW : pair U W = 0) (hQ : intervalQuadratic W = 0) : W = 0 :=
  eq_zero_of_pair_eq_zero hU hW hQ

example (a b : ℝ) (p q : MinkowskiModel d) :
    intervalQuadratic (a • p - b • q) =
      a ^ 2 * intervalQuadratic p - 2 * a * b * pair p q + b ^ 2 * intervalQuadratic q :=
  intervalQuadratic_smul_sub_smul a b p q

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    {x : (Fin d → ℝ) × (Fin d → ℝ)} (h₃ : x.1 ∈ domain d m₃) (h₄ : x.2 ∈ domain d m₄)
    (hx : x ∉ regular d m₃ m₄) : x.1 ∈ Submodule.span ℝ {x.1 + x.2} :=
  mem_span_of_notMem_regular hm₃ hm₄ h₃ h₄ hx

example (K : Fin 3 → ℝ) : Submodule.span ℝ {K} ≠ ⊤ :=
  span_singleton_ne_top K

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (K : Fin 3 → ℝ) :
    volume {π : Fin 3 → ℝ | π ∈ domain 3 m₃ ∧ K - π ∈ domain 3 m₄ ∧
      (π, K - π) ∉ regular 3 m₃ m₄} = 0 :=
  volume_irregular_slice hm₃ hm₄ K

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) :
    ((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)) (regular 3 m₃ m₄)ᶜ = 0 :=
  prod_regular_compl hm₃ hm₄

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)) =
      ∫⁻ P in region 3 m₃ m₄, ∫⁻ x, f x ∂(fibreMeasure m₃ m₄ P) :=
  lintegral_prod_eq hm₃ hm₄ hf

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) :
    (FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄) =
      (volume.restrict (region 3 m₃ m₄)).bind (fibreMeasure m₃ m₄) :=
  prod_eq_bind hm₃ hm₄

example {r : ℝ} (hr : 0 < r) :
    HasDerivAt (radialMass m₃ m₄)
      (r * radialMass m₃ m₄ r / (Real.sqrt (m₃ ^ 2 + r ^ 2) * Real.sqrt (m₄ ^ 2 + r ^ 2))) r :=
  hasDerivAt_radialMass hr

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄) :
    sphere (0 : E3) 1 ≃ᵐ fibre m₃ m₄ P :=
  fibreEquiv hm₃ hm₄ hP

example (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄) (n : sphere (0 : E3) 1) :
    (fibreEquiv hm₃ hm₄ hP n : (Fin 3 → ℝ) × (Fin 3 → ℝ)) = fibrePair m₃ m₄ P n :=
  rfl

example (P : MinkowskiModel 3) : IsFiniteMeasure (fibreMeasure m₃ m₄ P) :=
  inferInstance

example (m : ℝ) (L : orthochronousLorentzGroup d) :
    ⇑(actionHomeomorph m L) = action m L := rfl

example (m : ℝ) (L : orthochronousLorentzGroup d) :
    ⇑(actionHomeomorph m L).symm = action m L⁻¹ := rfl

example (m₃ m₄ : ℝ) (K k : Fin d → ℝ) :
    labGrad m₃ m₄ K k =
      (pairMass m₃ m₄ k * (pairMass m₃ m₄ k + Real.sqrt (pairMass m₃ m₄ k ^ 2 + ∑ i, K i ^ 2)))⁻¹ •
          K +
        ((energy m₄ k - energy m₃ k - (∑ i, K i * k i) /
            Real.sqrt (pairMass m₃ m₄ k ^ 2 + ∑ i, K i ^ 2)) /
          (pairMass m₃ m₄ k * energy m₃ k * energy m₄ k)) • k := rfl

end ProjectAinos.SpecialRelativity.TwoBodyFibre
