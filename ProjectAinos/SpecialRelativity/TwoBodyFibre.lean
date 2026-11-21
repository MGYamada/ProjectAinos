/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.ShellMeasure
public import ProjectAinos.SpecialRelativity.Decay
public import ProjectAinos.SmoothGeometry.Euclidean.SphereIntegral
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Two particles with a given total momentum

Two particles with the masses `m₃, m₄ ≥ 0` are described by their space momenta `(π₃, π₄)` in
the charts of their future mass shells (`FutureShell.point`). Their total momentum is
`total m₃ m₄ (π₃, π₄) = p₃ + p₄`. A total momentum `P` is *regular* if it is future timelike with
a rest mass `M = √Q(P) > m₃ + m₄` (`region`); the pairs with a regular total momentum are
`regular`, and the pairs with the total momentum `P` are the *fibre* `fibre m₃ m₄ P`
(Landau–Lifshitz, *The Classical Theory of Fields*, §§11–12).

**The rest frame.** In the rest frame of `P` the two particles have the space momenta `k` and
`−k` with `|k| = q = √λ(M², m₃², m₄²)/(2M)` (`restMomentum`), and the energies
`√(m₃² + q²) = (M² + m₃² − m₄²)/2M` and `√(m₄² + q²) = (M² + m₄² − m₃²)/2M`
(`sqrt_restEnergy_first`, `sqrt_restEnergy_second`). Conversely the rest mass of the pair with the
rest momenta `k, −k` is `pairMass m₃ m₄ k = E₃(k) + E₄(k)`, and its rest momentum is `|k|`
(`restMomentum_pairMass`).

**The boost.** `labBoost P` is the boost that brings the rest frame of `P` to the frame of the
co-ordinates: it maps `M e₀` to `P` (`labBoost_apply_rest`). In the chart of a shell it acts by
the explicit formula `labSpace P E k = k + (⟨K, k⟩/(M(M + P⁰)) + E/M) K`, `K` the space momentum
of `P` (`action_labBoost`). Its energy is `(P⁰E + ⟨K, k⟩)/M` (`energy_labSpace`).

**The fibre.** For a space momentum `K` and a rest momentum `k`, `totalOf m₃ m₄ K k` is the total
momentum with the space part `K` and the rest mass `pairMass m₃ m₄ k`, and
`labFirst m₃ m₄ K k` is the space momentum of the first particle in the frame of the
co-ordinates; the second has `K − labFirst m₃ m₄ K k`. For `P` in the region and a unit vector
`n`, `fibrePair m₃ m₄ P n` is the pair with the rest momenta `±q n`. It is a point of the fibre
(`fibrePair_mem_fibre`), it is the image of the rest pair under `labBoost P`
(`fibrePair_eq_action`), and `fibreEquiv` is a measurable equivalence between the unit sphere and
the fibre. A point of the fibre is a decay in the sense of §11 (`twoBodyDecay_of_mem_fibre`).
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Metric

namespace ProjectAinos.SpecialRelativity.TwoBodyFibre

open SmoothGeometry SmoothGeometry.Minkowski FutureShell

variable {d : ℕ}

/-! ### The momentum in the rest frame -/

/-- The length `q = √λ(M², m₃², m₄²)/(2M)` of the space momenta of the two particles in the rest
frame of a pair of rest mass `M`. -/
def restMomentum (m₃ m₄ M : ℝ) : ℝ := Real.sqrt (kallen (M ^ 2) (m₃ ^ 2) (m₄ ^ 2)) / (2 * M)

/-- Källén's function is positive above the threshold. -/
theorem kallen_sq_pos {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (h : m₃ + m₄ < M) :
    0 < kallen (M ^ 2) (m₃ ^ 2) (m₄ ^ 2) := by
  rw [kallen_sq]
  have h1 : (m₃ + m₄) ^ 2 < M ^ 2 := by nlinarith
  have h2 : (m₃ - m₄) ^ 2 < M ^ 2 := by nlinarith
  exact mul_pos (by linarith) (by linarith)

theorem restMomentum_pos {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (h : m₃ + m₄ < M) :
    0 < restMomentum m₃ m₄ M :=
  div_pos (Real.sqrt_pos.mpr (kallen_sq_pos hm₃ hm₄ h)) (by linarith)

theorem restMomentum_sq {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (h : m₃ + m₄ < M) :
    restMomentum m₃ m₄ M ^ 2 = kallen (M ^ 2) (m₃ ^ 2) (m₄ ^ 2) / (4 * M ^ 2) := by
  have hM : 0 < M := by linarith
  rw [restMomentum, div_pow, Real.sq_sqrt (kallen_sq_pos hm₃ hm₄ h).le]
  ring

/-- The energy of the first particle in the rest frame: `√(m₃² + q²) = (M² + m₃² − m₄²)/2M`. -/
theorem sqrt_restEnergy_first {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (h : m₃ + m₄ < M) :
    Real.sqrt (m₃ ^ 2 + restMomentum m₃ m₄ M ^ 2) = (M ^ 2 + m₃ ^ 2 - m₄ ^ 2) / (2 * M) := by
  have hM : 0 < M := by linarith
  have hnn : 0 ≤ (M ^ 2 + m₃ ^ 2 - m₄ ^ 2) / (2 * M) := by
    have : m₄ ^ 2 ≤ M ^ 2 := by nlinarith
    exact div_nonneg (by nlinarith) (by linarith)
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) hnn, restMomentum_sq hm₃ hm₄ h, kallen]
  field_simp
  ring

/-- The energy of the second particle in the rest frame: `√(m₄² + q²) = (M² + m₄² − m₃²)/2M`. -/
theorem sqrt_restEnergy_second {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (h : m₃ + m₄ < M) :
    Real.sqrt (m₄ ^ 2 + restMomentum m₃ m₄ M ^ 2) = (M ^ 2 + m₄ ^ 2 - m₃ ^ 2) / (2 * M) := by
  have hM : 0 < M := by linarith
  have hnn : 0 ≤ (M ^ 2 + m₄ ^ 2 - m₃ ^ 2) / (2 * M) := by
    have : m₃ ^ 2 ≤ M ^ 2 := by nlinarith
    exact div_nonneg (by nlinarith) (by linarith)
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) hnn, restMomentum_sq hm₃ hm₄ h, kallen]
  field_simp
  ring

/-- The energies in the rest frame add up to the rest mass. -/
theorem sqrt_add_sqrt_restMomentum {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    (h : m₃ + m₄ < M) :
    Real.sqrt (m₃ ^ 2 + restMomentum m₃ m₄ M ^ 2) +
      Real.sqrt (m₄ ^ 2 + restMomentum m₃ m₄ M ^ 2) = M := by
  have hM : 0 < M := by linarith
  rw [sqrt_restEnergy_first hm₃ hm₄ h, sqrt_restEnergy_second hm₃ hm₄ h]
  field_simp
  ring

/-- The rest momentum of the pair of rest mass `√(m₃² + r²) + √(m₄² + r²)` is `r`. -/
theorem restMomentum_sqrt_add_sqrt {m₃ m₄ r : ℝ} (hr : 0 ≤ r) :
    restMomentum m₃ m₄ (Real.sqrt (m₃ ^ 2 + r ^ 2) + Real.sqrt (m₄ ^ 2 + r ^ 2)) = r := by
  set a := Real.sqrt (m₃ ^ 2 + r ^ 2) with ha
  set b := Real.sqrt (m₄ ^ 2 + r ^ 2) with hb
  have ha2 : a ^ 2 = m₃ ^ 2 + r ^ 2 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = m₄ ^ 2 + r ^ 2 := Real.sq_sqrt (by positivity)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hk : kallen ((a + b) ^ 2) (m₃ ^ 2) (m₄ ^ 2) = (2 * (a + b) * r) ^ 2 := by
    have h3 : m₃ ^ 2 = a ^ 2 - r ^ 2 := by linarith
    have h4 : m₄ ^ 2 = b ^ 2 - r ^ 2 := by linarith
    rw [kallen, h3, h4]
    ring
  rw [restMomentum, hk, Real.sqrt_sq (by positivity)]
  rcases eq_or_lt_of_le (add_nonneg ha0 hb0) with h0 | hpos
  · have hab : a = 0 ∧ b = 0 := ⟨by linarith, by linarith⟩
    have hr0 : r = 0 := by nlinarith
    rw [← h0, hr0]
    simp
  · field_simp

/-- Above zero rest momentum the rest mass is above the threshold. -/
theorem add_lt_sqrt_add_sqrt {m₃ m₄ r : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hr : 0 < r) :
    m₃ + m₄ < Real.sqrt (m₃ ^ 2 + r ^ 2) + Real.sqrt (m₄ ^ 2 + r ^ 2) := by
  have h3 : m₃ < Real.sqrt (m₃ ^ 2 + r ^ 2) := by
    exact (Real.lt_sqrt hm₃).mpr (by nlinarith [sq_pos_of_pos hr])
  have h4 : m₄ < Real.sqrt (m₄ ^ 2 + r ^ 2) := by
    exact (Real.lt_sqrt hm₄).mpr (by nlinarith [sq_pos_of_pos hr])
  linarith

/-! ### Sums of squares -/

theorem sum_sq_nonneg (k : Fin d → ℝ) : 0 ≤ ∑ i, k i ^ 2 :=
  Finset.sum_nonneg fun i _ => sq_nonneg (k i)

theorem sum_sq_pos {k : Fin d → ℝ} (hk : k ≠ 0) : 0 < ∑ i, k i ^ 2 := by
  refine lt_of_le_of_ne (sum_sq_nonneg k) fun h0 => hk ?_
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (k j)).mp h0.symm i
    (Finset.mem_univ i)
  exact pow_eq_zero_iff two_ne_zero |>.mp hi

theorem sum_neg_sq (k : Fin d → ℝ) : ∑ i, (-k) i ^ 2 = ∑ i, k i ^ 2 := by
  simp

theorem sum_add_smul_sq (k K : Fin d → ℝ) (c : ℝ) :
    ∑ i, (k + c • K) i ^ 2 =
      ∑ i, k i ^ 2 + 2 * c * ∑ i, K i * k i + c ^ 2 * ∑ i, K i ^ 2 := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Cauchy–Schwarz for the scalar product of `Fin d → ℝ`. -/
theorem sq_sum_mul_le (K k : Fin d → ℝ) :
    (∑ i, K i * k i) ^ 2 ≤ (∑ i, K i ^ 2) * ∑ i, k i ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem energy_neg (m : ℝ) (k : Fin d → ℝ) : energy m (-k) = energy m k := by
  rw [energy, energy, sum_neg_sq]

theorem energy_nonneg (m : ℝ) (k : Fin d → ℝ) : 0 ≤ energy m k := Real.sqrt_nonneg _

theorem energy_sq' (m : ℝ) (k : Fin d → ℝ) : energy m k ^ 2 = m ^ 2 + ∑ i, k i ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg m) (sum_sq_nonneg k))

theorem mem_domain_of_ne_zero (m : ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) : k ∈ domain d m :=
  add_pos_of_nonneg_of_pos (sq_nonneg m) (sum_sq_pos hk)

/-! ### The boost from the rest frame -/

open scoped Classical in
/-- The velocity of the centre of momentum of `P`; zero if `P` is not future timelike. -/
def restVelocity (P : MinkowskiModel d) : Velocity d :=
  if hP : FutureTimelike P then Velocity.ofObserver (centreOfMomentum P hP) else Velocity.zero d

/-- The boost that brings the rest frame of `P` to the frame of the co-ordinates. -/
def labBoost (P : MinkowskiModel d) : orthochronousLorentzGroup d :=
  boostOrthochronous (restVelocity P).neg

theorem invariantMass_pos {P : MinkowskiModel d} (hP : FutureTimelike P) :
    0 < invariantMass P :=
  properSpeed_pos hP

theorem restVelocity_val {P : MinkowskiModel d} (hP : FutureTimelike P) :
    (restVelocity P).val = (time P)⁻¹ • space P := by
  have hM := invariantMass_pos hP
  simp only [restVelocity, hP, ↓reduceDIte]
  change (time (fourVelocity P))⁻¹ • space (fourVelocity P) = _
  have hM' : properSpeed P ≠ 0 := ne_of_gt hM
  rw [fourVelocity, map_smul, map_smul, smul_eq_mul, smul_smul]
  congr 1
  field_simp

theorem gamma_restVelocity {P : MinkowskiModel d} (hP : FutureTimelike P) :
    (restVelocity P).gamma = time P / invariantMass P := by
  simp only [restVelocity, hP, ↓reduceDIte]
  rw [Velocity.gamma_ofObserver]
  change time (fourVelocity P) = _
  rw [fourVelocity, map_smul, smul_eq_mul, div_eq_inv_mul]
  rfl

/-- `labBoost P` maps the rest momentum `M e₀` to `P`. -/
theorem labBoost_apply_rest {P : MinkowskiModel d} (hP : FutureTimelike P) :
    (labBoost P).val.val (invariantMass P • timeAxis d) = P := by
  have hM := invariantMass_pos hP
  have hobs : (restVelocity P).observer.velocity = (invariantMass P)⁻¹ • P := by
    simp only [restVelocity, hP, ↓reduceDIte]
    rw [Velocity.observer_ofObserver]
    rfl
  have h1 := boost_observer (restVelocity P)
  rw [hobs, map_smul] at h1
  have h2 : (boost (restVelocity P)).val P = invariantMass P • timeAxis d := by
    rw [← h1, smul_smul, mul_inv_cancel₀ (ne_of_gt hM), one_smul]
  change (boost (restVelocity P).neg).val (invariantMass P • timeAxis d) = P
  rw [boost_neg_inverse, ← h2]
  exact (boost (restVelocity P)).val.symm_apply_apply P

/-! ### The explicit formula of the boost -/

/-- The space momentum, in the frame of the co-ordinates, of a particle with the energy `E` and
the space momentum `k` in the rest frame of `P`:
`k + (⟨K, k⟩/(M(M + P⁰)) + E/M) K`. -/
def labSpace (P : MinkowskiModel d) (E : ℝ) (k : Fin d → ℝ) : Fin d → ℝ :=
  k + ((∑ i, spaceMomentum P i * k i) / (invariantMass P * (invariantMass P + time P)) +
    E / invariantMass P) • spaceMomentum P

/-- The boost `labBoost P` acts in the chart of a shell by `labSpace`. -/
theorem action_labBoost {P : MinkowskiModel d} (hP : FutureTimelike P) (m : ℝ)
    (k : Fin d → ℝ) : action m (labBoost P) k = labSpace P (energy m k) k := by
  have hM := invariantMass_pos hP
  have hT : 0 < time P := lt_of_le_of_lt (norm_nonneg _) hP
  have hval := restVelocity_val hP
  have hγ := gamma_restVelocity hP
  rw [labBoost, action_boost_eq]
  have hcoord : velocityCoord (restVelocity P).neg = -(time P)⁻¹ • spaceMomentum P := by
    funext i
    change -((restVelocity P).val i) = _
    rw [hval]
    simp [spaceMomentum]
  have hsum : ∑ j, velocityCoord (restVelocity P).neg j * k j =
      -(time P)⁻¹ * ∑ j, spaceMomentum P j * k j := by
    rw [hcoord, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [boostMap, hsum, hcoord, Velocity.gamma_neg, hγ, labSpace, smul_smul]
  congr 2
  have h1 : invariantMass P + time P ≠ 0 := by linarith
  field_simp
  ring

/-- The energy of the particle in the frame of the co-ordinates: `(P⁰E + ⟨K, k⟩)/M`. -/
theorem energy_labSpace {P : MinkowskiModel d} (hM : 0 < invariantMass P) (hT : 0 < time P)
    (hQ : time P ^ 2 = invariantMass P ^ 2 + ∑ i, spaceMomentum P i ^ 2) {m E : ℝ}
    {k : Fin d → ℝ} (hE : E ^ 2 = m ^ 2 + ∑ i, k i ^ 2)
    (hpos : 0 ≤ time P * E + ∑ i, spaceMomentum P i * k i) :
    energy m (labSpace P E k) =
      (time P * E + ∑ i, spaceMomentum P i * k i) / invariantMass P := by
  have h1 : invariantMass P + time P ≠ 0 := by linarith
  have hnn : 0 ≤ m ^ 2 + ∑ i, (labSpace P E k) i ^ 2 :=
    add_nonneg (sq_nonneg m) (sum_sq_nonneg _)
  rw [energy, Real.sqrt_eq_iff_eq_sq hnn (div_nonneg hpos hM.le), labSpace, sum_add_smul_sq]
  set A := ∑ i, spaceMomentum P i * k i
  set s := ∑ i, spaceMomentum P i ^ 2
  have hm : m ^ 2 = E ^ 2 - ∑ i, k i ^ 2 := by linarith
  have hs : s = time P ^ 2 - invariantMass P ^ 2 := by linarith
  rw [hm, hs]
  field_simp
  ring

/-! ### Pairs with opposite rest momenta -/

/-- The rest mass `E₃(k) + E₄(k)` of the pair with the rest momenta `k` and `−k`. -/
def pairMass (m₃ m₄ : ℝ) (k : Fin d → ℝ) : ℝ := energy m₃ k + energy m₄ k

/-- The total momentum with the space part `K` and the rest mass `pairMass m₃ m₄ k`. -/
def totalOf (m₃ m₄ : ℝ) (K k : Fin d → ℝ) : MinkowskiModel d :=
  Fin.cons (Real.sqrt (pairMass m₃ m₄ k ^ 2 + ∑ i, K i ^ 2)) K

/-- The space momentum, in the frame of the co-ordinates, of the first particle of the pair with
the rest momenta `k`, `−k` and the total space momentum `K`. -/
def labFirst (m₃ m₄ : ℝ) (K k : Fin d → ℝ) : Fin d → ℝ :=
  labSpace (totalOf m₃ m₄ K k) (energy m₃ k) k

variable {m₃ m₄ : ℝ}

theorem pairMass_nonneg (k : Fin d → ℝ) : 0 ≤ pairMass m₃ m₄ k :=
  add_nonneg (energy_nonneg _ _) (energy_nonneg _ _)

theorem energy_pos_of_ne_zero (m : ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) : 0 < energy m k :=
  energy_pos (mem_domain_of_ne_zero m hk)

theorem pairMass_pos {k : Fin d → ℝ} (hk : k ≠ 0) : 0 < pairMass m₃ m₄ k :=
  add_pos (energy_pos_of_ne_zero _ hk) (energy_pos_of_ne_zero _ hk)

/-- The energy with the length of the space momentum. -/
theorem energy_eq_sqrt (m : ℝ) (k : Fin d → ℝ) :
    energy m k = Real.sqrt (m ^ 2 + Real.sqrt (∑ i, k i ^ 2) ^ 2) := by
  rw [energy, Real.sq_sqrt (sum_sq_nonneg k)]

/-- Above zero rest momentum the rest mass of the pair is above the threshold. -/
theorem add_lt_pairMass (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) {k : Fin d → ℝ} (hk : k ≠ 0) :
    m₃ + m₄ < pairMass m₃ m₄ k := by
  rw [pairMass, energy_eq_sqrt, energy_eq_sqrt]
  exact add_lt_sqrt_add_sqrt hm₃ hm₄ (Real.sqrt_pos.mpr (sum_sq_pos hk))

/-- The rest momentum of the pair is the length of `k`. -/
theorem restMomentum_pairMass (k : Fin d → ℝ) :
    restMomentum m₃ m₄ (pairMass m₃ m₄ k) = Real.sqrt (∑ i, k i ^ 2) := by
  rw [pairMass, energy_eq_sqrt, energy_eq_sqrt]
  exact restMomentum_sqrt_add_sqrt (Real.sqrt_nonneg _)

theorem time_totalOf (K k : Fin d → ℝ) :
    time (totalOf m₃ m₄ K k) = Real.sqrt (pairMass m₃ m₄ k ^ 2 + ∑ i, K i ^ 2) := rfl

theorem spaceMomentum_totalOf (K k : Fin d → ℝ) : spaceMomentum (totalOf m₃ m₄ K k) = K := rfl

theorem intervalQuadratic_totalOf (K k : Fin d → ℝ) :
    intervalQuadratic (totalOf m₃ m₄ K k) = pairMass m₃ m₄ k ^ 2 := by
  rw [totalOf, FreeParticle.intervalQuadratic_cons,
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sum_sq_nonneg K))]
  ring

theorem invariantMass_totalOf (K k : Fin d → ℝ) :
    invariantMass (totalOf m₃ m₄ K k) = pairMass m₃ m₄ k := by
  rw [invariantMass, properSpeed, intervalQuadratic_totalOf, Real.sqrt_sq (pairMass_nonneg k)]

theorem futureTimelike_totalOf (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : 0 < pairMass m₃ m₄ k) :
    FutureTimelike (totalOf m₃ m₄ K k) := by
  refine (futureTimelike_iff _).mpr ⟨?_, ?_⟩
  · change 0 < intervalQuadratic _
    rw [intervalQuadratic_totalOf]
    positivity
  · rw [time_totalOf]
    exact Real.sqrt_pos.mpr (by have := sum_sq_nonneg K; positivity)

/-- The explicit formula `labFirst K k = k + (⟨K, k⟩/(M(M + P⁰)) + E₃/M) K`. -/
theorem labFirst_eq (K k : Fin d → ℝ) :
    labFirst m₃ m₄ K k = k + ((∑ i, K i * k i) / (pairMass m₃ m₄ k * (pairMass m₃ m₄ k +
      Real.sqrt (pairMass m₃ m₄ k ^ 2 + ∑ i, K i ^ 2))) + energy m₃ k / pairMass m₃ m₄ k) • K := by
  rw [labFirst, labSpace, invariantMass_totalOf, time_totalOf, spaceMomentum_totalOf]

/-- The second particle: `K − labFirst K k` is the momentum with the rest momentum `−k`. -/
theorem sub_labFirst (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : 0 < pairMass m₃ m₄ k) :
    K - labFirst m₃ m₄ K k = labSpace (totalOf m₃ m₄ K k) (energy m₄ k) (-k) := by
  rw [labFirst, labSpace, labSpace, invariantMass_totalOf, spaceMomentum_totalOf]
  have hT : 0 ≤ time (totalOf m₃ m₄ K k) := Real.sqrt_nonneg _
  have h1 : pairMass m₃ m₄ k + time (totalOf m₃ m₄ K k) ≠ 0 := by linarith
  have h2 : pairMass m₃ m₄ k ≠ 0 := ne_of_gt hk
  have hM : pairMass m₃ m₄ k = energy m₃ k + energy m₄ k := rfl
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, mul_neg,
    Finset.sum_neg_distrib]
  field_simp
  rw [hM]
  ring

/-- The first particle is the image of the rest momentum `k` under the boost. -/
theorem labFirst_eq_action (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : 0 < pairMass m₃ m₄ k) :
    labFirst m₃ m₄ K k = action m₃ (labBoost (totalOf m₃ m₄ K k)) k :=
  (action_labBoost (futureTimelike_totalOf K hk) m₃ k).symm

/-- The second particle is the image of the rest momentum `−k` under the boost. -/
theorem sub_labFirst_eq_action (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : 0 < pairMass m₃ m₄ k) :
    K - labFirst m₃ m₄ K k = action m₄ (labBoost (totalOf m₃ m₄ K k)) (-k) := by
  rw [sub_labFirst K hk, action_labBoost (futureTimelike_totalOf K hk), energy_neg]

/-- The rest momenta of the pair add up to `M e₀`. -/
theorem point_add_point_neg (k : Fin d → ℝ) :
    point m₃ k + point m₄ (-k) = pairMass m₃ m₄ k • timeAxis d := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [point, timeAxis, pairMass, energy_neg]
  · simp [point, timeAxis]

/-! ### The region and the fibre -/

/-- The regular total momenta: future timelike, with a rest mass above `m₃ + m₄`. -/
def region (d : ℕ) (m₃ m₄ : ℝ) : Set (MinkowskiModel d) :=
  {P | 0 < time P ∧ (m₃ + m₄) ^ 2 < intervalQuadratic P}

/-- The total momentum of a pair of space momenta on the two shells. -/
def total (m₃ m₄ : ℝ) (x : (Fin d → ℝ) × (Fin d → ℝ)) : MinkowskiModel d :=
  point m₃ x.1 + point m₄ x.2

/-- The pairs with a regular total momentum. -/
def regular (d : ℕ) (m₃ m₄ : ℝ) : Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {x | x.1 ∈ domain d m₃ ∧ x.2 ∈ domain d m₄ ∧ total m₃ m₄ x ∈ region d m₃ m₄}

/-- The fibre over `P`: the pairs with the total momentum `P`. -/
def fibre (m₃ m₄ : ℝ) (P : MinkowskiModel d) : Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {x | x.1 ∈ domain d m₃ ∧ x.2 ∈ domain d m₄ ∧ total m₃ m₄ x = P}

theorem continuous_total : Continuous (total (d := d) m₃ m₄) :=
  (continuous_point.comp continuous_fst).add (continuous_point.comp continuous_snd)

theorem isOpen_region : IsOpen (region d m₃ m₄) :=
  (isOpen_lt continuous_const time.continuous).inter
    (isOpen_lt continuous_const (pair.continuous₂.comp (continuous_id.prodMk continuous_id)))

theorem isOpen_regular : IsOpen (regular d m₃ m₄) :=
  (isOpen_domain.preimage continuous_fst).inter
    ((isOpen_domain.preimage continuous_snd).inter (isOpen_region.preimage continuous_total))

theorem measurableSet_region : MeasurableSet (region d m₃ m₄) := isOpen_region.measurableSet

theorem measurableSet_regular : MeasurableSet (regular d m₃ m₄) := isOpen_regular.measurableSet

theorem futureTimelike_of_mem_region {P : MinkowskiModel d} (hP : P ∈ region d m₃ m₄) :
    FutureTimelike P :=
  (futureTimelike_iff P).mpr ⟨lt_of_le_of_lt (sq_nonneg _) hP.2, hP.1⟩

theorem intervalQuadratic_eq_sq {P : MinkowskiModel d} (hP : P ∈ region d m₃ m₄) :
    intervalQuadratic P = invariantMass P ^ 2 :=
  (Real.sq_sqrt (lt_of_le_of_lt (sq_nonneg _) hP.2).le).symm

theorem time_sq_of_mem_region {P : MinkowskiModel d} (hP : P ∈ region d m₃ m₄) :
    time P ^ 2 = invariantMass P ^ 2 + ∑ i, spaceMomentum P i ^ 2 := by
  have h := intervalQuadratic_eq_sq hP
  rw [intervalQuadratic_eq] at h
  linarith

theorem add_lt_invariantMass (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) {P : MinkowskiModel d}
    (hP : P ∈ region d m₃ m₄) : m₃ + m₄ < invariantMass P := by
  rw [invariantMass, properSpeed]
  exact (Real.lt_sqrt (add_nonneg hm₃ hm₄)).mpr hP.2

/-- An orthochronous Lorentz transformation maps the region to itself. -/
theorem lorentz_mem_region (L : orthochronousLorentzGroup d) {P : MinkowskiModel d}
    (hP : P ∈ region d m₃ m₄) : L.val.val P ∈ region d m₃ m₄ := by
  refine ⟨?_, by rw [LorentzGroup.preserves_interval]; exact hP.2⟩
  have hfc : FutureCausal (L.val.val P) := (L.property P).mpr (futureTimelike_of_mem_region hP).le
  have hne : L.val.val P ≠ 0 := by
    intro h0
    have hP0 : P = 0 := L.val.val.injective (h0.trans (map_zero _).symm)
    have h := hP.1
    rw [hP0, map_zero] at h
    exact lt_irrefl _ h
  exact time_pos_of_futureCausal_ne_zero hfc hne

theorem invariantMass_lorentz' (L : orthochronousLorentzGroup d) (P : MinkowskiModel d) :
    invariantMass (L.val.val P) = invariantMass P :=
  invariantMass_lorentz L.val P

/-- For `k ≠ 0` the total momentum `totalOf K k` is regular. -/
theorem totalOf_mem_region (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (K : Fin d → ℝ) {k : Fin d → ℝ}
    (hk : k ≠ 0) : totalOf m₃ m₄ K k ∈ region d m₃ m₄ := by
  have hlt := add_lt_pairMass (m₃ := m₃) (m₄ := m₄) hm₃ hm₄ hk
  refine ⟨(futureTimelike_iff _ |>.mp (futureTimelike_totalOf K (pairMass_pos hk))).2, ?_⟩
  rw [intervalQuadratic_totalOf]
  have h0 : 0 ≤ m₃ + m₄ := add_nonneg hm₃ hm₄
  nlinarith

/-- For `k ≠ 0` the pair `(labFirst K k, K − labFirst K k)` has the total momentum
`totalOf K k`. -/
theorem total_labFirst (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    total m₃ m₄ (labFirst m₃ m₄ K k, K - labFirst m₃ m₄ K k) = totalOf m₃ m₄ K k := by
  have hM := pairMass_pos (m₃ := m₃) (m₄ := m₄) hk
  have hk' : -k ≠ 0 := neg_ne_zero.mpr hk
  rw [total]
  dsimp only
  rw [sub_labFirst_eq_action K hM, labFirst_eq_action K hM,
    point_action _ (mem_domain_of_ne_zero m₃ hk), point_action _ (mem_domain_of_ne_zero m₄ hk'),
    ← map_add, point_add_point_neg, ← invariantMass_totalOf K k]
  exact labBoost_apply_rest (futureTimelike_totalOf K hM)

theorem labFirst_mem_domain (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    labFirst m₃ m₄ K k ∈ domain d m₃ := by
  rw [labFirst_eq_action K (pairMass_pos hk)]
  exact action_mem _ (mem_domain_of_ne_zero m₃ hk)

theorem sub_labFirst_mem_domain (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    K - labFirst m₃ m₄ K k ∈ domain d m₄ := by
  rw [sub_labFirst_eq_action K (pairMass_pos hk)]
  exact action_mem _ (mem_domain_of_ne_zero m₄ (neg_ne_zero.mpr hk))

/-- The pair `(labFirst K k, K − labFirst K k)` is in the fibre over `totalOf K k`. -/
theorem labFirst_mem_fibre (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    (labFirst m₃ m₄ K k, K - labFirst m₃ m₄ K k) ∈ fibre m₃ m₄ (totalOf m₃ m₄ K k) :=
  ⟨labFirst_mem_domain K hk, sub_labFirst_mem_domain K hk, total_labFirst K hk⟩

/-- The rest momenta of a point of the fibre: under the inverse boost, the two momenta are
opposite and their energies add up to the rest mass. -/
theorem rest_of_mem_fibre {P : MinkowskiModel d} (hP : FutureTimelike P)
    {x : (Fin d → ℝ) × (Fin d → ℝ)} (hx : x ∈ fibre m₃ m₄ P) :
    action m₄ (labBoost P)⁻¹ x.2 = -action m₃ (labBoost P)⁻¹ x.1 ∧
      pairMass m₃ m₄ (action m₃ (labBoost P)⁻¹ x.1) = invariantMass P := by
  have hsum : point m₃ (action m₃ (labBoost P)⁻¹ x.1) + point m₄ (action m₄ (labBoost P)⁻¹ x.2) =
      invariantMass P • timeAxis d := by
    rw [point_action _ hx.1, point_action _ hx.2.1, ← map_add]
    change (labBoost P).val.val.symm (total m₃ m₄ x) = _
    rw [hx.2.2, LinearEquiv.symm_apply_eq]
    exact (labBoost_apply_rest hP).symm
  have hspace := congrArg spaceMomentum hsum
  have htime := congrArg time hsum
  have hsp : action m₃ (labBoost P)⁻¹ x.1 + action m₄ (labBoost P)⁻¹ x.2 = 0 := by
    funext j
    have := congrFun hspace j
    simpa [spaceMomentum, point, timeAxis] using this
  have h2 : action m₄ (labBoost P)⁻¹ x.2 = -action m₃ (labBoost P)⁻¹ x.1 :=
    eq_neg_of_add_eq_zero_right hsp
  refine ⟨h2, ?_⟩
  rw [map_add, time_point, time_point, h2, energy_neg] at htime
  simpa [timeAxis, pairMass] using htime

theorem action_action_inv {m : ℝ} (L : orthochronousLorentzGroup d) {π : Fin d → ℝ}
    (hπ : π ∈ domain d m) : action m L (action m L⁻¹ π) = π := by
  rw [← action_mul _ _ hπ, mul_inv_cancel, action_one]

theorem action_inv_action {m : ℝ} (L : orthochronousLorentzGroup d) {π : Fin d → ℝ}
    (hπ : π ∈ domain d m) : action m L⁻¹ (action m L π) = π := by
  rw [← action_mul _ _ hπ, inv_mul_cancel, action_one]

theorem sum_smul_sq (c : ℝ) (v : Fin d → ℝ) : ∑ i, (c • v) i ^ 2 = c ^ 2 * ∑ i, v i ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

/-! ### Measurability -/

theorem continuous_pairMass : Continuous (pairMass (d := d) m₃ m₄) :=
  continuous_energy.add continuous_energy

theorem continuous_sum_sq : Continuous fun K : Fin d → ℝ => ∑ i, K i ^ 2 :=
  continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2

theorem continuous_dot : Continuous fun z : (Fin d → ℝ) × (Fin d → ℝ) => ∑ i, z.1 i * z.2 i :=
  continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)

theorem measurable_labFirst :
    Measurable fun z : (Fin d → ℝ) × (Fin d → ℝ) => labFirst m₃ m₄ z.1 z.2 := by
  simp only [labFirst_eq]
  have hM : Measurable fun z : (Fin d → ℝ) × (Fin d → ℝ) => pairMass m₃ m₄ z.2 :=
    (continuous_pairMass.comp continuous_snd).measurable
  have hT : Measurable fun z : (Fin d → ℝ) × (Fin d → ℝ) =>
      Real.sqrt (pairMass m₃ m₄ z.2 ^ 2 + ∑ i, z.1 i ^ 2) :=
    (Real.continuous_sqrt.comp (((continuous_pairMass.comp continuous_snd).pow 2).add
      (continuous_sum_sq.comp continuous_fst))).measurable
  have hE : Measurable fun z : (Fin d → ℝ) × (Fin d → ℝ) => energy m₃ z.2 :=
    (continuous_energy.comp continuous_snd).measurable
  exact measurable_snd.add ((((continuous_dot.measurable).div (hM.mul (hM.add hT))).add
    (hE.div hM)).smul measurable_fst)

theorem continuous_restMomentum_num :
    Continuous fun M : ℝ => Real.sqrt (kallen (M ^ 2) (m₃ ^ 2) (m₄ ^ 2)) := by
  unfold kallen
  fun_prop

theorem measurable_restMomentum : Measurable (restMomentum m₃ m₄) :=
  continuous_restMomentum_num.measurable.div (measurable_const.mul measurable_id)

theorem continuous_invariantMass : Continuous (invariantMass (d := d)) :=
  Real.continuous_sqrt.comp (pair.continuous₂.comp (continuous_id.prodMk continuous_id))

/-! ### The fibre over a regular total momentum -/

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- A point of the unit sphere of `ℝ³` as a vector of `Fin 3 → ℝ`. -/
def sphereVec (n : sphere (0 : E3) 1) : Fin 3 → ℝ := WithLp.ofLp (n : E3)

theorem sum_sphereVec_sq (n : sphere (0 : E3) 1) : ∑ i, sphereVec n i ^ 2 = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq (n : E3)
  rw [norm_eq_of_mem_sphere n, one_pow] at h
  exact h.symm

theorem continuous_sphereVec : Continuous sphereVec :=
  (PiLp.continuous_ofLp 2 _).comp continuous_subtype_val

/-- The pair of the fibre over `P` with the rest momenta `q n` and `−q n`. -/
def fibrePair (m₃ m₄ : ℝ) (P : MinkowskiModel 3) (n : sphere (0 : E3) 1) :
    (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
  (labFirst m₃ m₄ (spaceMomentum P) (restMomentum m₃ m₄ (invariantMass P) • sphereVec n),
    spaceMomentum P -
      labFirst m₃ m₄ (spaceMomentum P) (restMomentum m₃ m₄ (invariantMass P) • sphereVec n))

theorem measurable_fibrePair :
    Measurable fun z : MinkowskiModel 3 × sphere (0 : E3) 1 => fibrePair m₃ m₄ z.1 z.2 := by
  have hK : Measurable fun z : MinkowskiModel 3 × sphere (0 : E3) 1 => spaceMomentum z.1 :=
    (contDiff_spaceMomentum.continuous.comp continuous_fst).measurable
  have hk : Measurable fun z : MinkowskiModel 3 × sphere (0 : E3) 1 =>
      restMomentum m₃ m₄ (invariantMass z.1) • sphereVec z.2 :=
    (measurable_restMomentum.comp (continuous_invariantMass.comp continuous_fst).measurable).smul
      (continuous_sphereVec.comp continuous_snd).measurable
  have h1 := (measurable_labFirst (m₃ := m₃) (m₄ := m₄)).comp (hK.prodMk hk)
  exact h1.prodMk (hK.sub h1)

variable {P : MinkowskiModel 3}

theorem restVec_ne_zero (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (n : sphere (0 : E3) 1) : restMomentum m₃ m₄ (invariantMass P) • sphereVec n ≠ 0 := by
  intro h0
  have h := congrArg (fun v : Fin 3 → ℝ => ∑ i, v i ^ 2) h0
  simp only [sum_smul_sq, sum_sphereVec_sq, mul_one, Pi.zero_apply] at h
  have hq := restMomentum_pos hm₃ hm₄ (add_lt_invariantMass hm₃ hm₄ hP)
  have : restMomentum m₃ m₄ (invariantMass P) ^ 2 = 0 := by simpa using h
  exact (pow_pos hq 2).ne' this

theorem pairMass_restVec (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (n : sphere (0 : E3) 1) :
    pairMass m₃ m₄ (restMomentum m₃ m₄ (invariantMass P) • sphereVec n) = invariantMass P := by
  rw [pairMass, energy, energy, sum_smul_sq, sum_sphereVec_sq, mul_one]
  exact sqrt_add_sqrt_restMomentum hm₃ hm₄ (add_lt_invariantMass hm₃ hm₄ hP)

/-- The total momentum of the pair with the rest momenta `±q n` is `P`. -/
theorem totalOf_restVec (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (n : sphere (0 : E3) 1) :
    totalOf m₃ m₄ (spaceMomentum P) (restMomentum m₃ m₄ (invariantMass P) • sphereVec n) = P := by
  rw [totalOf, pairMass_restVec hm₃ hm₄ hP n, ← time_sq_of_mem_region hP,
    Real.sqrt_sq hP.1.le]
  exact cons_time_spaceMomentum P

/-- The pair `fibrePair m₃ m₄ P n` is the image under `labBoost P` of the rest pair
`(q n, −q n)`. -/
theorem fibrePair_eq_action (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (n : sphere (0 : E3) 1) :
    fibrePair m₃ m₄ P n =
      (action m₃ (labBoost P) (restMomentum m₃ m₄ (invariantMass P) • sphereVec n),
        action m₄ (labBoost P) (-(restMomentum m₃ m₄ (invariantMass P) • sphereVec n))) := by
  have hM := pairMass_pos (m₃ := m₃) (m₄ := m₄) (restVec_ne_zero hm₃ hm₄ hP n)
  have h := totalOf_restVec hm₃ hm₄ hP n
  refine Prod.ext ?_ ?_
  · change labFirst m₃ m₄ _ _ = _
    rw [labFirst_eq_action _ hM, h]
  · change spaceMomentum P - labFirst m₃ m₄ _ _ = _
    rw [sub_labFirst_eq_action _ hM, h]

/-- The pair `fibrePair m₃ m₄ P n` is in the fibre over `P`. -/
theorem fibrePair_mem_fibre (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (n : sphere (0 : E3) 1) : fibrePair m₃ m₄ P n ∈ fibre m₃ m₄ P := by
  have h := labFirst_mem_fibre (m₃ := m₃) (m₄ := m₄) (spaceMomentum P)
    (restVec_ne_zero hm₃ hm₄ hP n)
  rwa [totalOf_restVec hm₃ hm₄ hP n] at h

/-- The rest momentum of a point of the fibre has the length `q`. -/
theorem sum_sq_rest_of_mem_fibre (hP : P ∈ region 3 m₃ m₄)
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hx : x ∈ fibre m₃ m₄ P) :
    ∑ i, (action m₃ (labBoost P)⁻¹ x.1) i ^ 2 = restMomentum m₃ m₄ (invariantMass P) ^ 2 := by
  obtain ⟨-, hM⟩ := rest_of_mem_fibre (futureTimelike_of_mem_region hP) hx
  have h := restMomentum_pairMass (m₃ := m₃) (m₄ := m₄) (action m₃ (labBoost P)⁻¹ x.1)
  rw [hM] at h
  rw [h, Real.sq_sqrt (sum_sq_nonneg _)]

/-- The direction in the rest frame of a point of the fibre. -/
def fibreDirection (m₃ m₄ : ℝ) (P : MinkowskiModel 3) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : E3 :=
  WithLp.toLp 2 ((restMomentum m₃ m₄ (invariantMass P))⁻¹ • action m₃ (labBoost P)⁻¹ x.1)

theorem fibreDirection_mem_sphere (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hx : x ∈ fibre m₃ m₄ P) :
    fibreDirection m₃ m₄ P x ∈ sphere (0 : E3) 1 := by
  have hq := restMomentum_pos hm₃ hm₄ (add_lt_invariantMass hm₃ hm₄ hP)
  have h2 : ‖fibreDirection m₃ m₄ P x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change ∑ i, ((restMomentum m₃ m₄ (invariantMass P))⁻¹ •
      action m₃ (labBoost P)⁻¹ x.1) i ^ 2 = 1
    rw [sum_smul_sq, sum_sq_rest_of_mem_fibre hP hx, inv_pow,
      inv_mul_cancel₀ (pow_pos hq 2).ne']
  rw [mem_sphere_zero_iff_norm]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

/-- **The fibre is a sphere.** For a regular total momentum `P`, the map
`n ↦ fibrePair m₃ m₄ P n` is a measurable equivalence between the unit sphere of `ℝ³` and the
fibre over `P`. -/
def fibreEquiv (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄) :
    sphere (0 : E3) 1 ≃ᵐ fibre m₃ m₄ P where
  toFun n := ⟨fibrePair m₃ m₄ P n, fibrePair_mem_fibre hm₃ hm₄ hP n⟩
  invFun x := ⟨fibreDirection m₃ m₄ P x, fibreDirection_mem_sphere hm₃ hm₄ hP x.2⟩
  left_inv n := by
    have hq := restMomentum_pos hm₃ hm₄ (add_lt_invariantMass hm₃ hm₄ hP)
    have hdom := mem_domain_of_ne_zero m₃ (restVec_ne_zero hm₃ hm₄ hP n)
    apply Subtype.ext
    change WithLp.toLp 2 ((restMomentum m₃ m₄ (invariantMass P))⁻¹ •
      action m₃ (labBoost P)⁻¹ (fibrePair m₃ m₄ P n).1) = (n : E3)
    rw [fibrePair_eq_action hm₃ hm₄ hP n]
    dsimp only
    rw [action_inv_action _ hdom, smul_smul, inv_mul_cancel₀ hq.ne', one_smul]
    rfl
  right_inv x := by
    have hq := restMomentum_pos hm₃ hm₄ (add_lt_invariantMass hm₃ hm₄ hP)
    obtain ⟨h2, -⟩ := rest_of_mem_fibre (futureTimelike_of_mem_region hP) x.2
    apply Subtype.ext
    change fibrePair m₃ m₄ P ⟨fibreDirection m₃ m₄ P x, _⟩ = (x : (Fin 3 → ℝ) × (Fin 3 → ℝ))
    rw [fibrePair_eq_action hm₃ hm₄ hP]
    have hv : restMomentum m₃ m₄ (invariantMass P) •
        sphereVec ⟨fibreDirection m₃ m₄ P x, fibreDirection_mem_sphere hm₃ hm₄ hP x.2⟩ =
        action m₃ (labBoost P)⁻¹ (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)).1 := by
      change restMomentum m₃ m₄ (invariantMass P) • ((restMomentum m₃ m₄ (invariantMass P))⁻¹ •
        action m₃ (labBoost P)⁻¹ (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)).1) = _
      rw [smul_smul, mul_inv_cancel₀ hq.ne', one_smul]
    rw [hv, ← h2, action_action_inv _ x.2.1, action_action_inv _ x.2.2.1]
  measurable_toFun :=
    (measurable_fibrePair.comp (measurable_const.prodMk measurable_id)).subtype_mk
  measurable_invFun := by
    refine Measurable.subtype_mk ?_
    have h1 : Continuous fun x : fibre m₃ m₄ P => (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)).1 :=
      continuous_fst.comp continuous_subtype_val
    have h2 : Continuous fun x : fibre m₃ m₄ P =>
        (restMomentum m₃ m₄ (invariantMass P))⁻¹ •
          action m₃ (labBoost P)⁻¹ (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)).1 :=
      have h3 : Continuous fun x : fibre m₃ m₄ P =>
          action m₃ (labBoost P)⁻¹ (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)).1 :=
        (continuous_action _).comp h1
      h3.const_smul (restMomentum m₃ m₄ (invariantMass P))⁻¹
    exact ((PiLp.continuous_toLp 2 _).comp h2).measurable

/-- A point of the fibre is a decay of a particle of mass `M` and momentum `P` into two
particles (§11). -/
theorem twoBodyDecay_of_mem_fibre (hP : P ∈ region 3 m₃ m₄) {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hx : x ∈ fibre m₃ m₄ P) :
    TwoBodyDecay P (point m₃ x.1) (point m₄ x.2) (invariantMass P) m₃ m₄ where
  conservation := hx.2.2.symm
  parent := intervalQuadratic_eq_sq hP
  first := (point_mem hx.1).1
  second := (point_mem hx.2.1).1
  mass_pos := invariantMass_pos (futureTimelike_of_mem_region hP)
  future := futureTimelike_of_mem_region hP

/-- In the frame of the centre of momentum (§11) the momenta of the points of the fibre have the
length `q = restMomentum m₃ m₄ M`. -/
theorem restForm_of_mem_fibre (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hx : x ∈ fibre m₃ m₄ P) :
    (twoBodyDecay_of_mem_fibre hP hx).restFrame.restForm
        (observerMomentum (twoBodyDecay_of_mem_fibre hP hx).restFrame (point m₃ x.1))
        (observerMomentum (twoBodyDecay_of_mem_fibre hP hx).restFrame (point m₃ x.1)) =
      restMomentum m₃ m₄ (invariantMass P) ^ 2 :=
  (twoBodyDecay_of_mem_fibre hP hx).momentum_sq_first.trans
    (restMomentum_sq hm₃ hm₄ (add_lt_invariantMass hm₃ hm₄ hP)).symm

end ProjectAinos.SpecialRelativity.TwoBodyFibre
