/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.CurvedScalarUniqueness
public import ProjectAinos.SpecialFunctions.GegenbauerCompleteness
public import ProjectAinos.SpecialFunctions.SphericalPolarCompleteness
public import ProjectAinos.SpecialFunctions.SphericalBasis
public import ProjectAinos.SpecialFunctions.SphericalAddition
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic

/-!
# Completeness of the scalar harmonics of `S³` and the expansion of general data

Landau–Lifshitz, §115, the closed universe. On a time slice of the stereographic chart the
volume of the unit three-sphere is `ψ⁻³ d³x`, `ψ = 1 + |x|²/4` (`chartWeight`), and `chartPair t`
is the pairing of two functions on the slice for this measure.

* `integral_Ioi_chartRadius`: with `r = 2 tan(θ/2)` (`chartRadius`),
  `∫₀^∞ r² ψ⁻³ g(r) dr = ∫₀^π sin² θ g(r(θ)) dθ`.
* `sphereBasis l`: the surface-orthonormal basis `realBasis l` of the harmonics of degree `l` on
  `S²`, as harmonic polynomials; `closedONHarmonic`: the closed harmonics built from it, and
  `chartPair_closedONHarmonic`: **they are orthogonal on every slice**, with the squared norms
  `closedNorm (l, m) = ∫₀^π Fₘ(cos θ)² sin^{2l+2} θ dθ > 0`.
* `abs_restrict_sphereBasis_le`: by the addition theorem the orthonormal spherical harmonics are
  bounded by `√((2l + 1)/(4π))`, and `abs_closedONHarmonic_le`: a normalized closed harmonic is
  bounded on the whole chart by that constant times a bound of its polar profile `sinˡ θ Fₘ(cos θ)`.
* `eq_zero_of_chartPair`: **completeness**: a bounded continuous function on a slice that is
  orthogonal to every closed harmonic vanishes. In polar co-ordinates
  (`integral_eq_integral_Ioi_sphere`) the angular coefficient of degree `l` is orthogonal to every
  `sin^{l+2} θ Fₘ(cos θ)`, hence zero (`eq_zero_of_integral_gegenbauer`), and a continuous
  function on `S²` orthogonal to every spherical harmonic is zero
  (`eq_zero_of_integral_mul_restrict`).
* `closedCoeff u i t`: the coefficient `⟨u(t), Yᵢ⟩/‖Yᵢ‖²` of data `u`; `chartPair_tsum`: the
  coefficients of a uniformly summably bounded series are recovered term by term, and
  `tsum_closedCoeff_eq`: **the expansion of bounded continuous data reconstructs the data**
  wherever its terms are uniformly summably bounded on the slice.
* `IsClosedExpandable A hA u`: **the explicit class of data**: bounded and continuous on the
  slices, with coefficients smooth in time, uniformly summably bounded terms on the slices and an
  expansion converging with two derivatives (`IsC2Series`). `IsClosedExpandable.tsum_eq`: such
  data are the sum of their expansion on the whole chart;
  `IsClosedExpandable.scalarSystemAt_slice_iff` (from `closed_data_scalarSystemAt_slice_iff`):
  **the scalar system of the data holds on a time slice if and only if every coefficient
  satisfies its evolution equation**, by `scalarSystemAt_slice_iff` with the unique coefficients
  `hasUniqueCoefficients_closedON`.
* The class contains every series of closed harmonics of the class with the coefficients of the
  series (`isClosedExpandable_tsum`), every finite expansion (`isClosedExpandable_finite`) and
  genuinely infinite expansions with all coefficients nonzero
  (`exists_isClosedExpandable_infinite`, by a diagonal choice against the bounds of the harmonics
  and their derivatives on growing balls).

The orthonormal bases are used because the basis `harmonicsBasis` of `CurvedScalarUniqueness` is
chosen without control of its conditioning: the terms `cᵢ Yᵢ` of an expansion in it can be large
while their sums over a degree are small, so no summable bound of the terms follows from bounds
of the data. What is not proved here is that every smooth function on `S³` belongs to the class:
that needs the rapid decay `⟨u, Y⟩ = λ⁻ᵏ ⟨Δᵏu, Y⟩` of the coefficients of smooth data and bounds
polynomial in the degree for the chart derivatives of order `≤ 2` of the normalized harmonics; of
the latter only the angular factor of order `0` is bounded here.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory Real
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.CurvedPerturbation

open SmoothGeometry CoordinateMetric FLRW IsotropicRicci CosmologicalModels
open ProjectAinos.SpecialFunctions ProjectAinos.SpecialFunctions.SphericalHarmonics
  ProjectAinos.SpecialFunctions.HarmonicPolynomial ProjectAinos.SpecialFunctions.ClassicalPolynomial

local notation "E" => MinkowskiModel 3
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The chart measure of a time slice -/

/-- The point `(t, y)` of the chart. -/
def slicePoint (t : ℝ) (y : E3) : E := Fin.cons t fun j => y j

@[simp] theorem slicePoint_zero (t : ℝ) (y : E3) : slicePoint t y 0 = t := rfl

theorem chartPoint_eq_slicePoint (t r : ℝ) (u : E3) : chartPoint t r u = slicePoint t (r • u) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp [chartPoint, slicePoint]

theorem continuous_slicePoint (t : ℝ) : Continuous (slicePoint t) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · change Continuous fun y : E3 => y j
    exact (EuclideanSpace.proj (𝕜 := ℝ) j).continuous

/-- The spatial co-ordinates of a point of the chart. -/
def spatialPart (x : E) : E3 := WithLp.toLp 2 fun j => x j.succ

theorem slicePoint_spatialPart (x : E) : slicePoint (x 0) (spatialPart x) = x := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  rfl

theorem psi_slicePoint (t : ℝ) (y : E3) : psi 1 (slicePoint t y) = 1 + ‖y‖ ^ 2 / 4 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [psi, slicePoint, show (1 : Fin 4) = Fin.succ 0 from rfl,
    show (2 : Fin 4) = Fin.succ 1 from rfl, show (3 : Fin 4) = Fin.succ 2 from rfl,
    Fin.cons_succ]
  ring

/-- The density `ψ⁻³` of the volume of the unit three-sphere in the stereographic chart. -/
def chartWeight (y : E3) : ℝ := ((1 + ‖y‖ ^ 2 / 4) ^ 3)⁻¹

theorem chartWeight_pos (y : E3) : 0 < chartWeight y := by unfold chartWeight; positivity

theorem continuous_chartWeight : Continuous chartWeight := by
  unfold chartWeight
  exact (by fun_prop : Continuous fun y : E3 => (1 + ‖y‖ ^ 2 / 4) ^ 3).inv₀ fun y => by positivity

theorem chartWeight_smul {r : ℝ} (hr : 0 ≤ r) (u : UnitSphere 3) :
    chartWeight (r • (u : E3)) = ((1 + r ^ 2 / 4) ^ 3)⁻¹ := by
  simp [chartWeight, norm_smul, abs_of_nonneg hr]

theorem integrable_chartWeight : Integrable chartWeight := by
  have h : Integrable (fun y : E3 => (1 + ‖y‖) ^ (-(6 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  refine (h.const_mul 512).mono' continuous_chartWeight.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (chartWeight_pos y).le, chartWeight]
  have ha := norm_nonneg y
  have h1 : (1 + ‖y‖) ^ 2 ≤ 8 * (1 + ‖y‖ ^ 2 / 4) := by nlinarith [sq_nonneg (‖y‖ - 1)]
  have h2 : (1 + ‖y‖) ^ 6 ≤ 512 * (1 + ‖y‖ ^ 2 / 4) ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) h1 3
    calc (1 + ‖y‖) ^ 6 = ((1 + ‖y‖) ^ 2) ^ 3 := by ring
      _ ≤ (8 * (1 + ‖y‖ ^ 2 / 4)) ^ 3 := this
      _ = 512 * (1 + ‖y‖ ^ 2 / 4) ^ 3 := by ring
  rw [show (-(6 : ℝ)) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
    Real.rpow_natCast]
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  calc (1 : ℝ) = (1 + ‖y‖) ^ 6 * ((1 + ‖y‖) ^ 6)⁻¹ := by field_simp
    _ ≤ 512 * (1 + ‖y‖ ^ 2 / 4) ^ 3 * ((1 + ‖y‖) ^ 6)⁻¹ :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 512 * ((1 + ‖y‖) ^ 6)⁻¹ * (1 + ‖y‖ ^ 2 / 4) ^ 3 := by ring

/-- The pairing of two functions on the slice at time `t` for the volume of `S³`. -/
def chartPair (t : ℝ) (f g : E → ℝ) : ℝ :=
  ∫ y, f (slicePoint t y) * g (slicePoint t y) * chartWeight y

/-- Bounded continuous functions on a slice have integrable products with the weight. -/
theorem integrable_chartPair {t : ℝ} {f g : E → ℝ} (hf : Continuous fun y => f (slicePoint t y))
    (hg : Continuous fun y => g (slicePoint t y)) {Bf Bg : ℝ}
    (hBf : ∀ y, |f (slicePoint t y)| ≤ Bf) (hBg : ∀ y, |g (slicePoint t y)| ≤ Bg) :
    Integrable fun y => f (slicePoint t y) * g (slicePoint t y) * chartWeight y := by
  refine (integrable_chartWeight.const_mul (Bf * Bg)).mono'
    ((hf.mul hg).mul continuous_chartWeight).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (chartWeight_pos y)]
  have h0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf y)
  exact mul_le_mul_of_nonneg_right (mul_le_mul (hBf y) (hBg y) (abs_nonneg _) h0)
    (chartWeight_pos y).le

/-! ### The radial change of variables -/

theorem one_add_cos_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 π) : 0 < 1 + cos θ := by
  have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
  rw [cos_pi] at this; linarith

theorem hasDerivAt_chartRadius {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt chartRadius (2 / (1 + cos θ)) θ := by
  have hc := one_add_cos_pos hθ
  have h := (((hasDerivAt_sin θ).const_mul 2).div ((hasDerivAt_cos θ).const_add 1) hc.ne')
  refine h.congr_deriv ?_
  have hsc := sin_sq_add_cos_sq θ
  field_simp
  nlinarith [hsc]

theorem continuousOn_chartRadius : ContinuousOn chartRadius (Ioo 0 π) :=
  fun _ hθ => (hasDerivAt_chartRadius hθ).continuousAt.continuousWithinAt

theorem chartRadius_arctan {r : ℝ} (hr : 0 < r) :
    2 * arctan (r / 2) ∈ Ioo 0 π ∧ chartRadius (2 * arctan (r / 2)) = r := by
  set a := arctan (r / 2)
  have ha0 : 0 < a := arctan_pos.mpr (by positivity)
  have ha1 : a < π / 2 := arctan_lt_pi_div_two _
  have hcos : 0 < cos a := cos_pos_of_mem_Ioo ⟨by linarith, ha1⟩
  refine ⟨⟨by positivity, by linarith⟩, ?_⟩
  have htan : sin a / cos a = r / 2 := by rw [← tan_eq_sin_div_cos, tan_arctan]
  simp only [chartRadius, sin_two_mul, cos_two_mul]
  have : 1 + (2 * cos a ^ 2 - 1) = 2 * cos a ^ 2 := by ring
  rw [this]
  field_simp
  field_simp at htan
  linarith

theorem image_chartRadius : chartRadius '' Ioo 0 π = Ioi 0 := by
  ext r
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact (chartRadius_spec hθ).1
  · intro hr
    exact ⟨_, (chartRadius_arctan hr).1, (chartRadius_arctan hr).2⟩

theorem injOn_chartRadius : InjOn chartRadius (Ioo 0 π) := by
  intro θ hθ θ' hθ' h
  have e := (chartRadius_spec hθ).2.2
  rw [h, (chartRadius_spec hθ').2.2] at e
  exact injOn_cos ⟨hθ'.1.le, hθ'.2.le⟩ ⟨hθ.1.le, hθ.2.le⟩ e |>.symm

/-- **The radial change of variables** `r = 2 tan(θ/2)`: `r² ψ⁻³ dr = sin² θ dθ`. -/
theorem integral_Ioi_chartRadius (g : ℝ → ℝ) :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * (((1 + r ^ 2 / 4) ^ 3)⁻¹ * g r) =
      ∫ θ in Ioo 0 π, sin θ ^ 2 * g (chartRadius θ) := by
  rw [← image_chartRadius, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun θ hθ => (hasDerivAt_chartRadius hθ).hasDerivWithinAt) injOn_chartRadius]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hc := one_add_cos_pos hθ
  have hψ : 1 + chartRadius θ ^ 2 / 4 = 2 / (1 + cos θ) := by
    have h1 := (chartRadius_spec hθ).2.2
    have hp : 0 < 1 + chartRadius θ ^ 2 / 4 := by positivity
    field_simp at h1 ⊢
    linarith
  have hsc := sin_sq_add_cos_sq θ
  simp only [smul_eq_mul, abs_of_pos (show 0 < 2 / (1 + cos θ) by positivity), hψ]
  simp only [chartRadius]
  field_simp

/-! ### Closed harmonics from orthonormal bases -/

/-- The surface-orthonormal basis `realBasis l` of the spherical harmonics of degree `l`, as
harmonic polynomials. -/
def sphereBasis (l : ℕ) (j : Fin (2 * l + 1)) : harmonics 3 l :=
  (harmonicsEquivL2 (by norm_num) l).symm (realBasis l j)

theorem representative_realBasis (l : ℕ) (j : Fin (2 * l + 1)) :
    representative 3 l (realBasis l j) = onSphere 3 (sphereBasis l j).val.val := by
  rw [← representative_harmonicsEquivL2 (by norm_num) l (sphereBasis l j)]
  simp [sphereBasis]

/-- **The basis is orthonormal for the surface measure.** -/
theorem integral_sphereBasis (l : ℕ) (j k : Fin (2 * l + 1)) :
    ∫ u, restrict 3 l (sphereBasis l j).val u * restrict 3 l (sphereBasis l k).val u
      ∂(surfaceMeasure 3) = if j = k then 1 else 0 := by
  have ho := (realBasis l).orthonormal
  rw [orthonormal_iff_ite] at ho
  rw [← ho j k]
  change _ = inner ℝ (realBasis l j).val (realBasis l k).val
  rw [L2.inner_def]
  have hj := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (surfaceMeasure 3)
    (representative 3 l (realBasis l j))
  have hk := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (surfaceMeasure 3)
    (representative 3 l (realBasis l k))
  rw [toLp_representative] at hj hk
  refine integral_congr_ae ?_
  filter_upwards [hj, hk] with u hu hv
  rw [real_inner_comm, RCLike.inner_apply, hu, hv, representative_realBasis,
    representative_realBasis]
  simp only [conj_trivial]
  rfl

/-- The closed harmonic of an index, built from the orthonormal basis. -/
def closedONHarmonic (i : ClosedIndex) : E → ℝ := closedHarmonic (sphereBasis i.1.1 i.2) i.1.2

/-- The squared norm `∫₀^π Fₘ(cos θ)² sin^{2l+2} θ dθ` of the closed harmonics of degrees
`(l, m)`. -/
def closedNorm (lm : ℕ × ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..π, gegenbauerReal lm.1 lm.2 (cos θ) * gegenbauerReal lm.1 lm.2 (cos θ) *
    sin θ ^ (2 * lm.1 + 2)

theorem closedNorm_pos (lm : ℕ × ℕ) : 0 < closedNorm lm :=
  integral_gegenbauerReal_sq_pos lm.1 lm.2

/-- The pairing of two closed harmonics separates into an angular and a polar integral. -/
theorem chartPair_closedHarmonic {l l' : ℕ} (p : harmonics 3 l) (q : harmonics 3 l') (m m' : ℕ)
    (t : ℝ) :
    chartPair t (closedHarmonic p m) (closedHarmonic q m') =
      (∫ u, restrict 3 l p.val u * restrict 3 l' q.val u ∂(surfaceMeasure 3)) *
        ∫ θ in Ioo 0 π, sin θ ^ 2 * (sin θ ^ l * gegenbauerReal l m (cos θ) *
          (sin θ ^ l' * gegenbauerReal l' m' (cos θ))) := by
  unfold chartPair
  rw [SmoothGeometry.Sphere.integral_eq_integral_sphere_mul _
    (fun u => restrict 3 l p.val u * restrict 3 l' q.val u)
    (fun r => ((1 + r ^ 2 / 4) ^ 3)⁻¹ * ((r / (1 + r ^ 2 / 4)) ^ l *
      gegenbauerReal l m (2 / (1 + r ^ 2 / 4) - 1) * ((r / (1 + r ^ 2 / 4)) ^ l' *
        gegenbauerReal l' m' (2 / (1 + r ^ 2 / 4) - 1))))
    (fun n r hr => by
      rw [← chartPoint_eq_slicePoint, closedHarmonic_chartPoint, closedHarmonic_chartPoint,
        chartWeight_smul hr.le]
      ring)]
  congr 1
  rw [integral_Ioi_chartRadius]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  obtain ⟨-, h1, h2⟩ := chartRadius_spec hθ
  simp only [h1, h2]

/-- **Orthogonality of the closed harmonics** on every slice. -/
theorem chartPair_closedONHarmonic (t : ℝ) (i j : ClosedIndex) :
    chartPair t (closedONHarmonic i) (closedONHarmonic j) =
      if i = j then closedNorm i.1 else 0 := by
  obtain ⟨⟨l, m⟩, a⟩ := i
  obtain ⟨⟨l', m'⟩, b⟩ := j
  simp only [closedONHarmonic]
  rw [chartPair_closedHarmonic]
  by_cases hl : l = l'
  · subst hl
    rw [integral_sphereBasis]
    by_cases hab : a = b
    · subst hab
      simp only [↓reduceIte, one_mul]
      by_cases hm : m = m'
      · subst hm
        simp only [↓reduceIte, closedNorm]
        rw [intervalIntegral.integral_of_le pi_pos.le, integral_Ioc_eq_integral_Ioo]
        refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
        ring
      · have hne : (⟨(l, m), a⟩ : ClosedIndex) ≠ ⟨(l, m'), a⟩ := by
          intro h
          exact hm (congrArg (fun i : ClosedIndex => i.1.2) h)
        simp only [hne, ↓reduceIte]
        have h0 := integral_gegenbauerReal_mul_eq_zero l hm
        rw [intervalIntegral.integral_of_le pi_pos.le, integral_Ioc_eq_integral_Ioo] at h0
        refine Eq.trans ?_ h0
        refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
        ring
    · have hne : (⟨(l, m), a⟩ : ClosedIndex) ≠ ⟨(l, m'), b⟩ := by
        intro h
        rw [Sigma.mk.inj_iff] at h
        obtain ⟨h1, h2⟩ := h
        have hm : m = m' := congrArg Prod.snd h1
        subst hm
        exact hab (eq_of_heq h2)
      simp [hab, hne]
  · have hne : (⟨(l, m), a⟩ : ClosedIndex) ≠ ⟨(l', m'), b⟩ := by
      intro h
      exact hl (congrArg (fun i : ClosedIndex => i.1.1) h)
    rw [integral_mul_eq_zero (by norm_num) hl (restrict_mem_space _) (restrict_mem_space _)]
    simp [hne]

/-! ### Bounds of the normalized harmonics -/

/-- **The addition theorem bounds the orthonormal spherical harmonics**:
`|Yₗⱼ(u)| ≤ √((2l + 1)/(4π))` on `S²`. -/
theorem abs_restrict_sphereBasis_le (l : ℕ) (j : Fin (2 * l + 1)) (u : UnitSphere 3) :
    |restrict 3 l (sphereBasis l j).val u| ≤ √((2 * l + 1) / (4 * π)) := by
  have h := addition (realBasis l) u u
  rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow, Legendre.polynomial_eval_one,
    mul_one] at h
  have hrep (i : Fin (2 * l + 1)) : representative 3 l (realBasis l i) u =
      restrict 3 l (sphereBasis l i).val u := by
    rw [representative_realBasis]; rfl
  simp only [hrep] at h
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  rw [← h, sq]
  exact Finset.single_le_sum (f := fun i => restrict 3 l (sphereBasis l i).val u *
    restrict 3 l (sphereBasis l i).val u) (fun i _ => mul_self_nonneg _) (Finset.mem_univ j)

/-- **The normalized closed harmonics are bounded by their polar profile**: if
`|sinˡ θ Fₘ(cos θ)| ≤ S` on `[0, π]`, then `|Yᵢ| ≤ √((2l + 1)/(4π)) S` on the whole chart. -/
theorem abs_closedONHarmonic_le (i : ClosedIndex) {S : ℝ}
    (hS : ∀ θ ∈ Icc 0 π, |sin θ ^ i.1.1 * gegenbauerReal i.1.1 i.1.2 (cos θ)| ≤ S) (x : E) :
    |closedONHarmonic i x| ≤ √((2 * i.1.1 + 1) / (4 * π)) * S := by
  obtain ⟨r, hr, u, hx⟩ := exists_chartPoint x
  rw [← hx]
  have hY := abs_restrict_sphereBasis_le i.1.1 i.2 u
  have hprof : |(r / (1 + r ^ 2 / 4)) ^ i.1.1 * gegenbauerReal i.1.1 i.1.2
      (2 / (1 + r ^ 2 / 4) - 1)| ≤ S := by
    rcases eq_or_lt_of_le hr with h0 | hpos
    · subst h0
      have := hS 0 ⟨le_rfl, pi_pos.le⟩
      norm_num at this ⊢
      exact this
    · obtain ⟨hθ, e⟩ := chartRadius_arctan hpos
      obtain ⟨-, h1, h2⟩ := chartRadius_spec hθ
      rw [e] at h1 h2
      rw [h1, h2]
      exact hS _ ⟨hθ.1.le, hθ.2.le⟩
  simp only [closedONHarmonic]
  rw [closedHarmonic_chartPoint, abs_mul, mul_comm]
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hprof
  exact mul_le_mul hY hprof (abs_nonneg _) (Real.sqrt_nonneg _)

/-! ### Completeness on a time slice -/

theorem continuous_closedHarmonic {l : ℕ} (p : harmonics 3 l) (m : ℕ) :
    Continuous (closedHarmonic p m) :=
  (contDiff_iff_contDiffAt.mpr fun x => smooth_chartHarmonic p 1
    (show (0 : ℝ) < psi 1 x by unfold psi; positivity).ne'
    (contDiff_gegenbauerReal l m).contDiffAt).continuous

theorem continuous_closedHarmonic_slice {l : ℕ} (p : harmonics 3 l) (m : ℕ) (t : ℝ) :
    Continuous fun y => closedHarmonic p m (slicePoint t y) :=
  (continuous_closedHarmonic p m).comp (continuous_slicePoint t)

/-- The orthonormal basis of the harmonics of degree `l` on `S²` as a basis of polynomials. -/
def sphereModuleBasis (l : ℕ) : Module.Basis (Fin (2 * l + 1)) ℝ (harmonics 3 l) :=
  (realBasis l).toBasis.map (harmonicsEquivL2 (by norm_num) l).symm

theorem sphereModuleBasis_apply (l : ℕ) (j : Fin (2 * l + 1)) :
    sphereModuleBasis l j = sphereBasis l j := by
  simp [sphereModuleBasis, sphereBasis]

/-- A closed harmonic is a finite combination of the orthonormal ones. -/
theorem closedHarmonic_eq_sum {l : ℕ} (p : harmonics 3 l) (m : ℕ) (x : E) :
    closedHarmonic p m x = ∑ j : Fin (2 * l + 1),
      (sphereModuleBasis l).repr p j * closedONHarmonic ⟨(l, m), j⟩ x := by
  conv_lhs => rw [← (sphereModuleBasis l).sum_repr p]
  rw [closedHarmonic_sum]
  simp only [sphereModuleBasis_apply, closedONHarmonic]

theorem chartPair_closedHarmonic_eq_zero {g : E → ℝ} {t : ℝ}
    (hc : Continuous fun y => g (slicePoint t y)) {B : ℝ} (hB : ∀ y, |g (slicePoint t y)| ≤ B)
    (h : ∀ i : ClosedIndex, chartPair t g (closedONHarmonic i) = 0) {l : ℕ}
    (p : harmonics 3 l) (m : ℕ) : chartPair t g (closedHarmonic p m) = 0 := by
  have hint (j : Fin (2 * l + 1)) : Integrable fun y => g (slicePoint t y) *
      closedONHarmonic ⟨(l, m), j⟩ (slicePoint t y) * chartWeight y := by
    obtain ⟨C, hC⟩ := exists_bound_closedHarmonic (sphereBasis l j) m
    exact integrable_chartPair hc (continuous_closedHarmonic_slice _ _ t) hB fun y => hC _
  unfold chartPair
  simp only [closedHarmonic_eq_sum p m, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ fun j _ => ?_]
  · refine Finset.sum_eq_zero fun j _ => ?_
    have e : (fun y => g (slicePoint t y) * ((sphereModuleBasis l).repr p j *
        closedONHarmonic ⟨(l, m), j⟩ (slicePoint t y)) * chartWeight y) = fun y =>
        (sphereModuleBasis l).repr p j * (g (slicePoint t y) *
          closedONHarmonic ⟨(l, m), j⟩ (slicePoint t y) * chartWeight y) := by
      funext y; ring
    rw [e, integral_const_mul]
    have := h ⟨(l, m), j⟩
    unfold chartPair at this
    rw [this, mul_zero]
  · exact ((hint j).const_mul ((sphereModuleBasis l).repr p j)).congr
      (Eventually.of_forall fun y => by simp only; ring)

/-- The angular coefficient of degree `l` of `g` on the sphere `|y| = r` of the slice. -/
def angularCoeff (g : E → ℝ) (t : ℝ) {l : ℕ} (q : harmonics 3 l) (r : ℝ) : ℝ :=
  ∫ u, g (slicePoint t (r • (u : E3))) * restrict 3 l q.val u ∂(surfaceMeasure 3)

theorem continuous_angularCoeff {g : E → ℝ} {t : ℝ} (hc : Continuous fun y => g (slicePoint t y))
    {l : ℕ} (q : harmonics 3 l) : Continuous (angularCoeff g t q) := by
  have hu : Continuous (Function.uncurry fun (r : ℝ) (u : UnitSphere 3) =>
      g (slicePoint t (r • (u : E3))) * restrict 3 l q.val u) :=
    (hc.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))).mul
      ((continuous_restrict q).comp continuous_snd)
  have := continuous_parametric_integral_of_continuous (μ := surfaceMeasure 3) hu isCompact_univ
  simp only [Measure.restrict_univ] at this
  exact this

theorem abs_angularCoeff_le {g : E → ℝ} {t : ℝ} {B : ℝ} (hB : ∀ y, |g (slicePoint t y)| ≤ B)
    {l : ℕ} (q : harmonics 3 l) {C : ℝ} (hC : ∀ u, |restrict 3 l q.val u| ≤ C) (r : ℝ) :
    |angularCoeff g t q r| ≤ B * C * (surfaceMeasure 3).real univ := by
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hB _) (hC u) (abs_nonneg _) ((abs_nonneg _).trans (hB 0))

/-- **The pairing with a closed harmonic in polar co-ordinates.** -/
theorem chartPair_closedHarmonic_polar {g : E → ℝ} {t : ℝ}
    (hc : Continuous fun y => g (slicePoint t y)) {B : ℝ} (hB : ∀ y, |g (slicePoint t y)| ≤ B)
    {l : ℕ} (q : harmonics 3 l) (m : ℕ) :
    chartPair t g (closedHarmonic q m) = ∫ θ in Ioo 0 π, sin θ ^ 2 *
      (sin θ ^ l * gegenbauerReal l m (cos θ) * angularCoeff g t q (chartRadius θ)) := by
  obtain ⟨C, hC⟩ := exists_bound_closedHarmonic q m
  have hF := integrable_chartPair hc (continuous_closedHarmonic_slice q m t) hB fun y => hC _
  unfold chartPair
  rw [integral_eq_integral_Ioi_sphere _ hF]
  have e : ∀ r ∈ Ioi (0 : ℝ), r ^ 2 * ∫ u, g (slicePoint t (r • (u : E3))) *
      closedHarmonic q m (slicePoint t (r • (u : E3))) * chartWeight (r • (u : E3))
        ∂(surfaceMeasure 3) = r ^ 2 * (((1 + r ^ 2 / 4) ^ 3)⁻¹ * ((r / (1 + r ^ 2 / 4)) ^ l *
          gegenbauerReal l m (2 / (1 + r ^ 2 / 4) - 1) * angularCoeff g t q r)) := by
    intro r hr
    congr 1
    unfold angularCoeff
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [← chartPoint_eq_slicePoint, closedHarmonic_chartPoint, chartWeight_smul (le_of_lt hr),
      chartPoint_eq_slicePoint]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_Ioi_chartRadius]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  obtain ⟨-, h1, h2⟩ := chartRadius_spec hθ
  simp only [h1, h2]

/-- **Completeness of the closed harmonics**: a bounded continuous function on a time slice of
the chart that is orthogonal to every closed harmonic vanishes on the slice. -/
theorem eq_zero_of_chartPair {g : E → ℝ} {t : ℝ} (hc : Continuous fun y => g (slicePoint t y))
    {B : ℝ} (hB : ∀ y, |g (slicePoint t y)| ≤ B)
    (h : ∀ i : ClosedIndex, chartPair t g (closedONHarmonic i) = 0) :
    ∀ x : E, x 0 = t → g x = 0 := by
  -- the angular coefficients vanish on every sphere
  have hG : ∀ (l : ℕ) (q : harmonics 3 l) (r : ℝ), 0 < r → angularCoeff g t q r = 0 := by
    intro l q r hr
    obtain ⟨C, -, hC⟩ := exists_bound_restrict q
    have hcont : ContinuousOn (fun θ => angularCoeff g t q (chartRadius θ)) (Ioo 0 π) :=
      (continuous_angularCoeff hc q).comp_continuousOn continuousOn_chartRadius
    have hz := eq_zero_of_integral_gegenbauer l hcont
      (B := B * C * (surfaceMeasure 3).real univ)
      (fun θ _ => abs_angularCoeff_le hB q hC _) (fun m => by
        refine Eq.trans ?_ (chartPair_closedHarmonic_eq_zero hc hB h q m)
        rw [chartPair_closedHarmonic_polar hc hB]
        refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
        ring)
    obtain ⟨hθ, e⟩ := chartRadius_arctan hr
    have := hz _ hθ
    rwa [e] at this
  -- the function vanishes on every sphere
  have hsph : ∀ r : ℝ, 0 < r → ∀ u : UnitSphere 3, g (slicePoint t (r • (u : E3))) = 0 := by
    intro r hr
    have hf : Continuous fun u : UnitSphere 3 => g (slicePoint t (r • (u : E3))) :=
      hc.comp (continuous_subtype_val.const_smul r)
    have := eq_zero_of_integral_mul_restrict hf fun l q => hG l q r hr
    exact fun u => congrFun this u
  have hne : ∀ y : E3, y ≠ 0 → g (slicePoint t y) = 0 := by
    intro y hy
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have := hsph ‖y‖ hn ⟨‖y‖⁻¹ • y, by simp [norm_smul, hn.ne']⟩
    simpa [smul_smul, hn.ne'] using this
  have hall : ∀ y : E3, g (slicePoint t y) = 0 := by
    have hcl : IsClosed {y : E3 | g (slicePoint t y) = 0} := isClosed_eq hc continuous_const
    have hsub : ({0}ᶜ : Set E3) ⊆ {y : E3 | g (slicePoint t y) = 0} := fun y hy => hne y hy
    intro y
    exact hcl.closure_subset_iff.mpr hsub ((dense_compl_singleton (0 : E3)).closure_eq ▸
      mem_univ y)
  intro x hx
  rw [← slicePoint_spatialPart x, hx]
  exact hall _

/-! ### The expansion of data -/

/-- The coefficient `⟨u(t), Yᵢ⟩/‖Yᵢ‖²` of the closed harmonic `Yᵢ` in data `u` at time `t`. -/
def closedCoeff (u : E → ℝ) (i : ClosedIndex) (t : ℝ) : ℝ :=
  chartPair t u (closedONHarmonic i) / closedNorm i.1

theorem continuous_closedONHarmonic_slice (i : ClosedIndex) (t : ℝ) :
    Continuous fun y => closedONHarmonic i (slicePoint t y) :=
  continuous_closedHarmonic_slice _ _ t

theorem exists_bound_closedONHarmonic (i : ClosedIndex) :
    ∃ C, ∀ x : E, |closedONHarmonic i x| ≤ C :=
  exists_bound_closedHarmonic _ _

/-- A uniformly summably bounded series of closed harmonics is continuous on the slice. -/
theorem continuous_tsum_slice {a : ClosedIndex → ℝ} {t : ℝ} {M : ClosedIndex → ℝ}
    (hM : Summable M) (hb : ∀ i y, |a i * closedONHarmonic i (slicePoint t y)| ≤ M i) :
    Continuous fun y => ∑' i, a i * closedONHarmonic i (slicePoint t y) :=
  continuous_tsum (fun i => continuous_const.mul (continuous_closedONHarmonic_slice i t)) hM
    fun i y => by rw [Real.norm_eq_abs]; exact hb i y

/-- A uniformly summably bounded series of closed harmonics is bounded on the slice. -/
theorem abs_tsum_slice_le {a : ClosedIndex → ℝ} {t : ℝ} {M : ClosedIndex → ℝ}
    (hM : Summable M) (hb : ∀ i y, |a i * closedONHarmonic i (slicePoint t y)| ≤ M i) (y : E3) :
    |∑' i, a i * closedONHarmonic i (slicePoint t y)| ≤ ∑' i, M i := by
  have hs : Summable fun i => ‖a i * closedONHarmonic i (slicePoint t y)‖ :=
    hM.of_nonneg_of_le (fun _ => norm_nonneg _) fun i => by
      rw [Real.norm_eq_abs]; exact hb i y
  rw [← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum (fun i => by
    rw [Real.norm_eq_abs]; exact hb i y) hM)

/-- **Term-by-term pairing**: the coefficient of `Yⱼ` in a uniformly summably bounded series of
the orthogonal closed harmonics is `aⱼ`. -/
theorem chartPair_tsum {a : ClosedIndex → ℝ} {t : ℝ} {M : ClosedIndex → ℝ} (hM : Summable M)
    (hb : ∀ i y, |a i * closedONHarmonic i (slicePoint t y)| ≤ M i) (j : ClosedIndex) :
    chartPair t (fun x => ∑' i, a i * closedONHarmonic i x) (closedONHarmonic j) =
      a j * closedNorm j.1 := by
  obtain ⟨C, hC⟩ := exists_bound_closedONHarmonic j
  have hYc := continuous_closedONHarmonic_slice j t
  set F : ClosedIndex → E3 → ℝ := fun i y => a i *
    closedONHarmonic i (slicePoint t y) * closedONHarmonic j (slicePoint t y) * chartWeight y
  have hFi (i : ClosedIndex) : Integrable (F i) := by
    obtain ⟨Ci, hCi⟩ := exists_bound_closedONHarmonic i
    refine ((integrable_chartPair (continuous_closedONHarmonic_slice i t) hYc
      (fun y => hCi _) fun y => hC _).const_mul (a i)).congr
      (Eventually.of_forall fun y => ?_)
    simp only [F]; ring
  have hFn (i : ClosedIndex) : ∫ y, ‖F i y‖ ≤ M i * C * ∫ y, chartWeight y := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (integrable_chartWeight.const_mul _) (Eventually.of_forall fun y => ?_)
    simp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (chartWeight_pos y)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hb i y) (hC _) (abs_nonneg _)
      ((abs_nonneg _).trans (hb i y))) (chartWeight_pos y).le
  have hsum : Summable fun i => ∫ y, ‖F i y‖ :=
    ((hM.mul_right C).mul_right _).of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _) hFn
  have hex := integral_tsum_of_summable_integral_norm hFi hsum
  unfold chartPair
  have e : (fun y => (∑' i, a i * closedONHarmonic i (slicePoint t y)) *
      closedONHarmonic j (slicePoint t y) * chartWeight y) = fun y => ∑' i, F i y := by
    funext y
    simp only [F]
    rw [tsum_mul_right, tsum_mul_right]
  rw [e, ← hex]
  have hFint (i : ClosedIndex) : ∫ y, F i y = a i * if i = j then closedNorm i.1 else 0 := by
    rw [← chartPair_closedONHarmonic t i j]
    unfold chartPair
    rw [← integral_const_mul]
    congr 1; funext y; simp only [F]; ring
  simp only [hFint]
  rw [tsum_eq_single j (fun i hi => by simp [hi])]
  simp

/-- **The expansion reconstructs the data**: if the terms of the expansion of bounded continuous
data are uniformly summably bounded on a slice, the expansion converges to the data there. -/
theorem tsum_closedCoeff_eq {u : E → ℝ} {t : ℝ} (hc : Continuous fun y => u (slicePoint t y))
    {B : ℝ} (hB : ∀ y, |u (slicePoint t y)| ≤ B)
    (hM : ∃ M : ClosedIndex → ℝ, Summable M ∧
      ∀ i y, |closedCoeff u i t * closedONHarmonic i (slicePoint t y)| ≤ M i) :
    ∀ x : E, x 0 = t → ∑' i, closedCoeff u i t * closedONHarmonic i x = u x := by
  obtain ⟨M, hM, hb⟩ := hM
  set v : E → ℝ := fun x => ∑' i, closedCoeff u i t * closedONHarmonic i x
  have hvc : Continuous fun y => v (slicePoint t y) := continuous_tsum_slice hM hb
  have hvB : ∀ y, |v (slicePoint t y)| ≤ ∑' i, M i := abs_tsum_slice_le hM hb
  set w : E → ℝ := fun x => v x - u x
  have hwc : Continuous fun y => w (slicePoint t y) := hvc.sub hc
  have hwB : ∀ y, |w (slicePoint t y)| ≤ ∑' i, M i + B := fun y =>
    (abs_sub _ _).trans (add_le_add (hvB y) (hB y))
  have horth (j : ClosedIndex) : chartPair t w (closedONHarmonic j) = 0 := by
    obtain ⟨C, hC⟩ := exists_bound_closedONHarmonic j
    have hYc := continuous_closedONHarmonic_slice j t
    have hv := integrable_chartPair hvc hYc hvB fun y => hC _
    have hu := integrable_chartPair hc hYc hB fun y => hC _
    have hsplit : chartPair t w (closedONHarmonic j) =
        chartPair t v (closedONHarmonic j) - chartPair t u (closedONHarmonic j) := by
      unfold chartPair
      rw [← integral_sub hv hu]
      congr 1; funext y; simp only [w]; ring
    rw [hsplit, chartPair_tsum hM hb]
    unfold closedCoeff
    rw [div_mul_cancel₀ _ (closedNorm_pos j.1).ne', sub_self]
  intro x hx
  have := eq_zero_of_chartPair hwc hwB horth x hx
  simp only [w, v] at this
  linarith

/-- **The coefficients of a series**: for a series of closed harmonics with time-dependent
coefficients, uniformly summably bounded on the slice at time `t`, the coefficient of the data at
`t` is the coefficient of the series. -/
theorem closedCoeff_tsum {φ : ClosedIndex → ℝ → ℝ} {t : ℝ} {M : ClosedIndex → ℝ}
    (hM : Summable M) (hb : ∀ i y, |φ i t * closedONHarmonic i (slicePoint t y)| ≤ M i)
    (i : ClosedIndex) :
    closedCoeff (fun x => ∑' j, φ j (x 0) * closedONHarmonic j x) i t = φ i t := by
  unfold closedCoeff
  have e : chartPair t (fun x => ∑' j, φ j (x 0) * closedONHarmonic j x) (closedONHarmonic i) =
      chartPair t (fun x => ∑' j, φ j t * closedONHarmonic j x) (closedONHarmonic i) := rfl
  rw [e, chartPair_tsum hM hb, mul_div_cancel_right₀ _ (closedNorm_pos i.1).ne']

/-! ### Unique coefficients and the scalar system of data -/

/-- The closed harmonics built from the orthonormal bases are a family of separated modes. -/
theorem isModeFamily_closedON {A : ℝ} (hA : 0 < A) {φ : ClosedIndex → ℝ → ℝ}
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) :
    IsModeFamily (closedDust A hA) φ closedONHarmonic
      (fun i => ((i.1.1 + i.1.2 : ℕ) : ℝ) * (i.1.1 + i.1.2 + 2)) where
  smooth_time := hφ
  smooth_space i _ hx := smooth_chartHarmonic (sphereBasis i.1.1 i.2) 1 (psi_pos hx).ne'
    (contDiff_gegenbauerReal i.1.1 i.1.2).contDiffAt
  static i _ hx := (chartHarmonic_time (sphereBasis i.1.1 i.2) 1 (psi_pos hx).ne'
    (contDiff_gegenbauerReal i.1.1 i.1.2).contDiffAt).self_of_nhds
  eigen i x _ := by
    change spatialLaplacian 1 (closedHarmonic (sphereBasis i.1.1 i.2) i.1.2) x =
      _ * closedHarmonic (sphereBasis i.1.1 i.2) i.1.2 x
    simpa only [neg_mul] using closedHarmonic_equation (sphereBasis i.1.1 i.2) i.1.2 x

/-- **The closed harmonics built from the orthonormal bases have unique coefficients on every
time slice.** -/
theorem hasUniqueCoefficients_closedON {A : ℝ} (hA : 0 < A) {t : ℝ}
    (ht : t ∈ (closedDust A hA).I) :
    HasUniqueCoefficients (slice (closedDust A hA) t) closedONHarmonic := by
  intro c ⟨M, hM, hb⟩ h i
  have hmem (x : E) (hx : x 0 = t) : x ∈ slice (closedDust A hA) t :=
    ⟨⟨by rw [hx]; exact ht, by show 0 < psi 1 x; unfold psi; positivity⟩, hx⟩
  let P : (lm : ℕ × ℕ) → harmonics 3 lm.1 := fun lm =>
    ∑ j : Fin (2 * lm.1 + 1), c ⟨lm, j⟩ • sphereModuleBasis lm.1 j
  have hP (lm : ℕ × ℕ) (x : E) : closedHarmonic (P lm) lm.2 x =
      ∑ j : Fin (2 * lm.1 + 1), c ⟨lm, j⟩ * closedONHarmonic ⟨lm, j⟩ x := by
    rw [closedHarmonic_sum]
    simp only [sphereModuleBasis_apply, closedONHarmonic]
  have hMs : Summable fun lm : ℕ × ℕ => ∑ j : Fin (2 * lm.1 + 1), M ⟨lm, j⟩ := by
    have := hM.sigma (f := M)
    simpa only [tsum_fintype] using this
  have hP0 := closedHarmonic_coeff_eq_zero P hMs (t := t) (fun lm x hx => by
      rw [hP]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
        hb ⟨lm, j⟩ x (hmem x hx)))
    (fun x hx => by
      have hsum : Summable fun j : ClosedIndex => c j * closedONHarmonic j x :=
        hM.of_norm_bounded fun j => by rw [Real.norm_eq_abs]; exact hb j x (hmem x hx)
      have hs := hsum.hasSum.sigma (fun lm => hasSum_fintype _)
      simp only [hP]
      rw [hs.tsum_eq]
      exact h x (hmem x hx))
  obtain ⟨lm, j⟩ := i
  have h0 : ∑ j' : Fin (2 * lm.1 + 1), c ⟨lm, j'⟩ • sphereModuleBasis lm.1 j' = 0 := hP0 lm
  have h2 := congrArg (fun v => (sphereModuleBasis lm.1).repr v j) h0
  simp only [map_sum, map_smul, Module.Basis.repr_self, map_zero, Finsupp.coe_zero, Pi.zero_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply] at h2
  simpa using h2

/-- The scalar system at `x` depends on the potential only through its germ at `x`. -/
theorem scalarSystemAt_congr {D : Data} {κ : ℝ} {ρ : ℝ → ℝ} {u v δ : E → ℝ}
    {V : E → Fin 4 → ℝ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    ScalarSystemAt D κ ρ u δ V x ↔ ScalarSystemAt D κ ρ v δ V x := by
  have hp (i : Fin 4) : part u i x = part v i x := by simp only [part]; rw [h.fderiv_eq]
  have hf : fderiv ℝ u =ᶠ[𝓝 x] fderiv ℝ v := h.eventuallyEq_nhds.mono fun y hy => hy.fderiv_eq
  have hs (a b : Fin 4) : secondPartial u x a b = secondPartial v x a b := by
    have hfb : (fun z => fderiv ℝ u z (Pi.single b 1)) =ᶠ[𝓝 x]
        fun z => fderiv ℝ v z (Pi.single b 1) := hf.mono fun y hy => by simp only [hy]
    simp only [secondPartial]
    rw [hfb.fderiv_eq]
  have hu : u x = v x := h.eq_of_nhds
  simp only [ScalarSystemAt, spatialLaplacian, hp, hs, hu]

/-- **The scalar system of general closed data**: for bounded continuous data whose expansion in
the orthonormal closed harmonics has smooth coefficients, converges with two derivatives and is
uniformly summably bounded on the slices, the scalar system holds on a time slice (with the
density contrast and covelocity of the modes) if and only if every coefficient satisfies its
evolution equation at that time. -/
theorem closed_data_scalarSystemAt_slice_iff {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ) {u : E → ℝ}
    (hcont : ∀ t ∈ (closedDust A hA).I, Continuous fun y => u (slicePoint t y))
    (hbdd : ∀ t ∈ (closedDust A hA).I, ∃ B, ∀ y, |u (slicePoint t y)| ≤ B)
    (hcoef : ∀ t ∈ (closedDust A hA).I, ∃ M : ClosedIndex → ℝ, Summable M ∧
      ∀ i y, |closedCoeff u i t * closedONHarmonic i (slicePoint t y)| ≤ M i)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (closedCoeff u i) (closedDust A hA).I)
    (hS : IsC2Series (domain (closedDust A hA))
      fun i => separated (closedCoeff u i) (closedONHarmonic i)) {t : ℝ}
    (ht : t ∈ (closedDust A hA).I)
    (hR : ∃ M : ClosedIndex → ℝ, Summable M ∧ ∀ i, ∀ y ∈ slice (closedDust A hA) t,
      |evolutionResidual (closedDust A hA) (closedCoeff u i) t * closedONHarmonic i y| ≤ M i) :
    (∀ y ∈ slice (closedDust A hA) t, ScalarSystemAt (closedDust A hA) κ
      (dustDensity κ (6 * A) (closedDust A hA).a) u
      (fun y => ∑' i, contrast (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
        (closedCoeff u i) (((i.1.1 + i.1.2 : ℕ) : ℝ) * (i.1.1 + i.1.2 + 2))
        (closedONHarmonic i) y)
      (fun y j => ∑' i, covelocity (closedDust A hA) κ
        (dustDensity κ (6 * A) (closedDust A hA).a) (closedCoeff u i) (closedONHarmonic i) y j)
      y) ↔ ∀ i, Evolution (closedDust A hA) (closedCoeff u i) t := by
  have heq : ∀ x ∈ domain (closedDust A hA),
      (∑' i, separated (closedCoeff u i) (closedONHarmonic i) x) = u x := by
    intro x hx
    obtain ⟨B, hB⟩ := hbdd (x 0) (time_mem hx)
    exact tsum_closedCoeff_eq (hcont _ (time_mem hx)) hB (hcoef _ (time_mem hx)) x rfl
  have hev (y : E) (hy : y ∈ domain (closedDust A hA)) :
      (fun z => ∑' i, separated (closedCoeff u i) (closedONHarmonic i) z) =ᶠ[𝓝 y] u := by
    filter_upwards [(domain (closedDust A hA)).isOpen.mem_nhds hy] with z hz
    exact heq z hz
  rw [← scalarSystemAt_slice_iff (κ := κ) (ρ := dustDensity κ (6 * A) (closedDust A hA).a)
    (isModeFamily_closedON hA hφ) hS
    (mul_pos hκ (dustDensity_pos hκ (by positivity) ((closedDust A hA).a_pos t ht))).ne'
    (hasUniqueCoefficients_closedON hA ht) hR]
  exact forall₂_congr fun y hy => (scalarSystemAt_congr (hev y hy.1)).symm

/-! ### The class of expandable closed data -/

/-- **Expandable data on the closed dust universe**: on every slice the data are bounded and
continuous, and their expansion in the orthonormal closed harmonics has smooth coefficients, is
uniformly summably bounded on the slices and converges with two derivatives. -/
structure IsClosedExpandable (A : ℝ) (hA : 0 < A) (u : E → ℝ) : Prop where
  /-- The data are continuous on every slice. -/
  continuous_slice : ∀ t ∈ (closedDust A hA).I, Continuous fun y => u (slicePoint t y)
  /-- The data are bounded on every slice. -/
  bounded_slice : ∀ t ∈ (closedDust A hA).I, ∃ B, ∀ y, |u (slicePoint t y)| ≤ B
  /-- The terms of the expansion are uniformly summably bounded on every slice. -/
  summable_slice : ∀ t ∈ (closedDust A hA).I, ∃ M : ClosedIndex → ℝ, Summable M ∧
    ∀ i y, |closedCoeff u i t * closedONHarmonic i (slicePoint t y)| ≤ M i
  /-- The coefficients are smooth in time. -/
  smooth_coeff : ∀ i, ContDiffOn ℝ ∞ (closedCoeff u i) (closedDust A hA).I
  /-- The expansion converges with two derivatives. -/
  isC2Series : IsC2Series (domain (closedDust A hA))
    fun i => separated (closedCoeff u i) (closedONHarmonic i)

/-- **Expandable data are the sum of their expansion** on the whole chart. -/
theorem IsClosedExpandable.tsum_eq {A : ℝ} {hA : 0 < A} {u : E → ℝ}
    (h : IsClosedExpandable A hA u) {x : E} (hx : x ∈ domain (closedDust A hA)) :
    ∑' i, separated (closedCoeff u i) (closedONHarmonic i) x = u x := by
  obtain ⟨B, hB⟩ := h.bounded_slice (x 0) (time_mem hx)
  exact tsum_closedCoeff_eq (h.continuous_slice _ (time_mem hx)) hB
    (h.summable_slice _ (time_mem hx)) x rfl

/-- **The scalar system of expandable closed data** holds on a time slice if and only if every
coefficient satisfies its evolution equation at that time. -/
theorem IsClosedExpandable.scalarSystemAt_slice_iff {A κ : ℝ} {hA : 0 < A} (hκ : 0 < κ)
    {u : E → ℝ} (h : IsClosedExpandable A hA u) {t : ℝ} (ht : t ∈ (closedDust A hA).I)
    (hR : ∃ M : ClosedIndex → ℝ, Summable M ∧ ∀ i, ∀ y ∈ slice (closedDust A hA) t,
      |evolutionResidual (closedDust A hA) (closedCoeff u i) t * closedONHarmonic i y| ≤ M i) :
    (∀ y ∈ slice (closedDust A hA) t, ScalarSystemAt (closedDust A hA) κ
      (dustDensity κ (6 * A) (closedDust A hA).a) u
      (fun y => ∑' i, contrast (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
        (closedCoeff u i) (((i.1.1 + i.1.2 : ℕ) : ℝ) * (i.1.1 + i.1.2 + 2))
        (closedONHarmonic i) y)
      (fun y j => ∑' i, covelocity (closedDust A hA) κ
        (dustDensity κ (6 * A) (closedDust A hA).a) (closedCoeff u i) (closedONHarmonic i) y j)
      y) ↔ ∀ i, Evolution (closedDust A hA) (closedCoeff u i) t :=
  closed_data_scalarSystemAt_slice_iff hA hκ h.continuous_slice h.bounded_slice
    h.summable_slice h.smooth_coeff h.isC2Series ht hR

/-- Series converging with two derivatives on an open set depend only on the terms there. -/
theorem IsC2Series.congr {ι : Type*} {U : Set E} (hU : IsOpen U) {f g : ι → E → ℝ}
    (hf : IsC2Series U f) (hfg : ∀ i, ∀ x ∈ U, f i x = g i x) : IsC2Series U g where
  local_bound x hx := by
    obtain ⟨ε, hε, hεU, b, hb, h⟩ := hf.local_bound x hx
    refine ⟨ε, hε, hεU, b, hb, fun i y hy => ?_⟩
    have hev : f i =ᶠ[𝓝 y] g i := by
      filter_upwards [hU.mem_nhds (hεU hy)] with z hz using hfg i z hz
    have hev' : fderiv ℝ (f i) =ᶠ[𝓝 y] fderiv ℝ (g i) :=
      hev.eventuallyEq_nhds.mono fun z hz => hz.fderiv_eq
    obtain ⟨d0, d1, c0, c1, c2⟩ := h i y hy
    refine ⟨d0.congr_of_eventuallyEq hev.symm, d1.congr_of_eventuallyEq hev'.symm, ?_, ?_, ?_⟩
    · rw [← hev.eq_of_nhds]; exact c0
    · rw [← hev.fderiv_eq]; exact c1
    · rw [← hev'.fderiv_eq]; exact c2

/-- **Series of closed harmonics are expandable data**: a series with smooth coefficients,
converging with two derivatives and uniformly summably bounded on the slices, is expandable data
whose coefficients are those of the series. -/
theorem isClosedExpandable_tsum {A : ℝ} (hA : 0 < A) {φ : ClosedIndex → ℝ → ℝ}
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I)
    (hS : IsC2Series (domain (closedDust A hA)) fun i => separated (φ i) (closedONHarmonic i))
    (hb : ∀ t ∈ (closedDust A hA).I, ∃ M : ClosedIndex → ℝ, Summable M ∧
      ∀ i y, |φ i t * closedONHarmonic i (slicePoint t y)| ≤ M i) :
    IsClosedExpandable A hA (fun x => ∑' j, φ j (x 0) * closedONHarmonic j x) ∧
      ∀ i, ∀ t ∈ (closedDust A hA).I,
        closedCoeff (fun x => ∑' j, φ j (x 0) * closedONHarmonic j x) i t = φ i t := by
  have hcoef : ∀ i, ∀ t ∈ (closedDust A hA).I,
      closedCoeff (fun x => ∑' j, φ j (x 0) * closedONHarmonic j x) i t = φ i t := by
    intro i t ht
    obtain ⟨M, hM, hbM⟩ := hb t ht
    exact closedCoeff_tsum hM hbM i
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun i => ?_, ?_⟩, hcoef⟩
  · obtain ⟨M, hM, hbM⟩ := hb t ht
    exact continuous_tsum_slice hM hbM
  · obtain ⟨M, hM, hbM⟩ := hb t ht
    exact ⟨_, abs_tsum_slice_le hM hbM⟩
  · obtain ⟨M, hM, hbM⟩ := hb t ht
    exact ⟨M, hM, fun i y => by rw [hcoef i t ht]; exact hbM i y⟩
  · exact (hφ i).congr fun t ht => hcoef i t ht
  · refine hS.congr (domain (closedDust A hA)).isOpen fun i x hx => ?_
    simp only [separated]
    rw [hcoef i _ (time_mem hx)]

/-- **Finite expansions are expandable data.** -/
theorem isClosedExpandable_finite {A : ℝ} (hA : 0 < A) (s : Finset ClosedIndex)
    {φ : ClosedIndex → ℝ → ℝ} (h0 : ∀ i ∉ s, φ i = 0)
    (hφ : ∀ i ∈ s, ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) :
    IsClosedExpandable A hA (fun x => ∑' j, φ j (x 0) * closedONHarmonic j x) := by
  classical
  have hφ' (i : ClosedIndex) : ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I := by
    by_cases hi : i ∈ s
    · exact hφ i hi
    · rw [h0 i hi]; exact contDiffOn_const
  refine (isClosedExpandable_tsum hA hφ' ?_ fun t _ => ?_).1
  · refine IsC2Series.of_finite_support (domain (closedDust A hA)).isOpen s
      (fun i hi => by funext y; simp [separated, h0 i hi]) fun i hi x hx => ?_
    have hQ : ContDiffAt ℝ ∞ (closedONHarmonic i) x :=
      smooth_chartHarmonic (sphereBasis i.1.1 i.2) 1 (psi_pos hx).ne'
        (contDiff_gegenbauerReal i.1.1 i.1.2).contDiffAt
    have hφx : ContDiffAt ℝ ∞ (φ i) (x 0) :=
      (hφ i hi).contDiffAt ((closedDust A hA).isOpen_I.mem_nhds (time_mem hx))
    exact ((hφx.comp x (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0).contDiffAt).mul hQ).of_le
      (by norm_num)
  · choose C hC using fun i : ClosedIndex => exists_bound_closedONHarmonic i
    refine ⟨fun i => if i ∈ s then |φ i t| * C i else 0,
      summable_of_ne_finset_zero (s := s) fun i hi => by simp [hi], fun i y => ?_⟩
    by_cases hi : i ∈ s
    · simp only [hi, ↓reduceIte, abs_mul]
      exact mul_le_mul_of_nonneg_left (hC i _) (abs_nonneg _)
    · simp [hi, h0 i hi]

theorem contDiff_closedONHarmonic (i : ClosedIndex) : ContDiff ℝ ∞ (closedONHarmonic i) :=
  contDiff_iff_contDiffAt.mpr fun x => smooth_chartHarmonic (sphereBasis i.1.1 i.2) 1
    (show (0 : ℝ) < psi 1 x by unfold psi; positivity).ne'
    (contDiff_gegenbauerReal i.1.1 i.1.2).contDiffAt

/-- The closed harmonics and their first two derivatives are bounded on balls. -/
theorem exists_bound_closedONHarmonic_ball (i : ClosedIndex) (R : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ y ∈ Metric.closedBall (0 : E) R, ‖closedONHarmonic i y‖ ≤ K ∧
      ‖fderiv ℝ (closedONHarmonic i) y‖ ≤ K ∧
        ‖fderiv ℝ (fderiv ℝ (closedONHarmonic i)) y‖ ≤ K := by
  have h := contDiff_closedONHarmonic i
  have c1 : Continuous (fderiv ℝ (closedONHarmonic i)) := h.continuous_fderiv (by simp)
  have c2 : Continuous fun y : E => ‖fderiv ℝ (fderiv ℝ (closedONHarmonic i)) y‖ := by
    exact ((h.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)).norm
  obtain ⟨K0, hK0⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    h.continuous.continuousOn
  obtain ⟨K1, hK1⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    c1.continuousOn
  obtain ⟨K2, hK2⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    c2.continuousOn
  refine ⟨max (max K0 K1) (max K2 0), by positivity, fun y hy => ⟨?_, ?_, ?_⟩⟩
  · exact (hK0 y hy).trans (le_max_of_le_left (le_max_left _ _))
  · exact (hK1 y hy).trans (le_max_of_le_left (le_max_right _ _))
  · have h2 := hK2 y hy
    rw [Real.norm_eq_abs] at h2
    exact ((le_abs_self _).trans h2).trans (le_max_of_le_right (le_max_left _ _))

/-- **Genuinely infinite expandable data**: there are expandable data whose coefficients are all
nonzero (constant in time), by a diagonal choice of the coefficients against the bounds of the
harmonics on growing balls; their evolution residuals are summably bounded on every slice, so all
the hypotheses of `IsClosedExpandable.scalarSystemAt_slice_iff` hold. -/
theorem exists_isClosedExpandable_infinite {A : ℝ} (hA : 0 < A) :
    ∃ c : ClosedIndex → ℝ, (∀ i, 0 < c i) ∧
      IsClosedExpandable A hA (fun x => ∑' j, c j * closedONHarmonic j x) ∧
      (∀ i, ∀ t ∈ (closedDust A hA).I,
        closedCoeff (fun x => ∑' j, c j * closedONHarmonic j x) i t = c i) ∧
      ∀ t ∈ (closedDust A hA).I, ∃ M : ClosedIndex → ℝ, Summable M ∧
        ∀ i, ∀ y ∈ slice (closedDust A hA) t, |evolutionResidual (closedDust A hA)
          (closedCoeff (fun x => ∑' j, c j * closedONHarmonic j x) i) t *
            closedONHarmonic i y| ≤ M i := by
  choose K hK0 hK using fun (i : ClosedIndex) (n : ℕ) =>
    exists_bound_closedONHarmonic_ball i n
  choose C hC using fun i : ClosedIndex => exists_bound_closedONHarmonic i
  set e : ClosedIndex → ℕ := Encodable.encode
  have he : Function.Injective e := Encodable.encode_injective
  set c : ClosedIndex → ℝ := fun i => (2 ^ e i)⁻¹ / (1 + K i (e i) + |C i|)
  have hc (i : ClosedIndex) : 0 < c i := by
    have := hK0 i (e i); simp only [c]; positivity
  have hgeom : Summable fun i : ClosedIndex => ((2 : ℝ) ^ e i)⁻¹ := by
    have := summable_geometric_two.comp_injective he
    refine this.congr fun i => ?_
    simp [Function.comp, one_div, inv_pow]
  have hcK (i : ClosedIndex) : c i * K i (e i) ≤ (2 ^ e i)⁻¹ := by
    have h0 := hK0 i (e i)
    simp only [c]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (0 : ℝ) < (2 ^ e i)⁻¹ := by positivity
    nlinarith [abs_nonneg (C i)]
  have hcC (i : ClosedIndex) : c i * |C i| ≤ (2 ^ e i)⁻¹ := by
    have h0 := hK0 i (e i)
    simp only [c]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (0 : ℝ) < (2 ^ e i)⁻¹ := by positivity
    nlinarith [abs_nonneg (C i)]
  -- the terms and their derivatives
  have hd (i : ClosedIndex) := (contDiff_closedONHarmonic i).differentiable (by simp)
  have hd1 (i : ClosedIndex) := ((contDiff_closedONHarmonic i).fderiv_right (m := 1)
    (by simp)).differentiable (by simp)
  have hf1 (i : ClosedIndex) : fderiv ℝ (separated (fun _ => c i) (closedONHarmonic i)) =
      fun z => c i • fderiv ℝ (closedONHarmonic i) z := by
    funext z
    exact fderiv_const_mul (hd i z) (c i)
  have hf2 (i : ClosedIndex) (y : E) :
      fderiv ℝ (fderiv ℝ (separated (fun _ => c i) (closedONHarmonic i))) y =
        c i • fderiv ℝ (fderiv ℝ (closedONHarmonic i)) y := by
    rw [hf1]
    exact fderiv_fun_const_smul (hd1 i y) (c i)
  have hS : IsC2Series (domain (closedDust A hA))
      fun i => separated (fun _ => c i) (closedONHarmonic i) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨ε0, hε0, hball⟩ := Metric.isOpen_iff.mp (domain (closedDust A hA)).isOpen x hx
    set N : ℕ := ⌈‖x‖⌉₊ + 1
    refine ⟨min ε0 1, lt_min hε0 one_pos, (Metric.ball_subset_ball (min_le_left _ _)).trans hball,
      fun i => c i * K i (max N (e i)), ?_, fun i y hy => ?_⟩
    · have hfin : (e ⁻¹' (Finset.range N : Set ℕ)).Finite :=
        (Finset.range N).finite_toSet.preimage he.injOn
      have hsf : Summable fun i : ClosedIndex =>
          if e i < N then c i * K i (max N (e i)) else 0 := by
        refine summable_of_ne_finset_zero (s := hfin.toFinset) fun i hi => ?_
        simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Finset.coe_range,
          Set.mem_Iio] at hi
        simp [hi]
      refine ((hgeom.add hsf)).of_nonneg_of_le
        (fun i => mul_nonneg (hc i).le (hK0 i _)) fun i => ?_
      by_cases h : e i < N
      · simp only [h, ↓reduceIte]
        have : (0 : ℝ) ≤ (2 ^ e i)⁻¹ := by positivity
        linarith
      · simp only [h, ↓reduceIte, add_zero, show max N (e i) = e i by omega]
        exact hcK i
    · have hy0 : y ∈ Metric.closedBall (0 : E) (max N (e i) : ℕ) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        have h1 : ‖y‖ ≤ ‖x‖ + 1 := by
          have := Metric.mem_ball.mp hy
          rw [dist_eq_norm] at this
          have h2 := norm_le_insert' y x
          linarith [min_le_right ε0 1]
        have h3 : ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
        have h4 : ((N : ℕ) : ℝ) ≤ ((max N (e i) : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
        have h5 : ((N : ℕ) : ℝ) = (⌈‖x‖⌉₊ : ℝ) + 1 := by simp [N]
        linarith
      obtain ⟨k0, k1, k2⟩ := hK i _ y hy0
      have hci := (hc i).le
      refine ⟨(hd i y).const_mul (c i), ?_, ?_, ?_, ?_⟩
      · rw [hf1]; exact (hd1 i y).const_smul (c i)
      · change ‖c i * closedONHarmonic i y‖ ≤ _
        rw [norm_mul, Real.norm_of_nonneg hci]
        exact mul_le_mul_of_nonneg_left k0 hci
      · rw [hf1]
        refine (ContinuousLinearMap.opNorm_smul_le (c i) _).trans ?_
        rw [Real.norm_of_nonneg hci]
        exact mul_le_mul_of_nonneg_left k1 hci
      · rw [hf2]
        refine (ContinuousLinearMap.opNorm_smul_le (c i) _).trans ?_
        rw [Real.norm_of_nonneg hci]
        exact mul_le_mul_of_nonneg_left k2 hci
  have hb : ∀ t ∈ (closedDust A hA).I, ∃ M : ClosedIndex → ℝ, Summable M ∧
      ∀ i y, |(fun _ : ℝ => c i) t * closedONHarmonic i (slicePoint t y)| ≤ M i := by
    intro t _
    refine ⟨fun i => (2 ^ e i)⁻¹, hgeom, fun i y => ?_⟩
    simp only
    rw [abs_mul, abs_of_pos (hc i)]
    exact (mul_le_mul_of_nonneg_left ((hC i _).trans (le_abs_self _)) (hc i).le).trans (hcC i)
  obtain ⟨h1, h2⟩ := isClosedExpandable_tsum hA (φ := fun i _ => c i)
    (fun i => contDiffOn_const) hS hb
  refine ⟨c, hc, h1, h2, fun t ht => ⟨fun i => 2 * (2 ^ e i)⁻¹, hgeom.mul_left 2,
    fun i y _ => ?_⟩⟩
  set u : E → ℝ := fun x => ∑' j, c j * closedONHarmonic j x
  have hev : closedCoeff u i =ᶠ[𝓝 t] fun _ => c i := by
    filter_upwards [(closedDust A hA).isOpen_I.mem_nhds ht] with s hs using h2 i s hs
  have hd : deriv (closedCoeff u i) =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
    hev.eventuallyEq_nhds.mono fun s hs => hs.deriv_eq.trans (deriv_const s (c i))
  have hres : evolutionResidual (closedDust A hA) (closedCoeff u i) t = -2 * c i := by
    simp only [evolutionResidual, hd.deriv_eq, hev.deriv_eq, hev.eq_of_nhds,
      deriv_const]
    change 0 + 3 * hubble (closedDust A hA) t * 0 - 2 * 1 * c i = _
    ring
  rw [hres, abs_mul, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), abs_of_pos (hc i)]
  have := mul_le_mul_of_nonneg_left ((hC i y).trans (le_abs_self _)) (hc i).le
  nlinarith [hcC i]

end ProjectAinos.GeneralRelativity.CurvedPerturbation
