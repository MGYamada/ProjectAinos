/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.CurvedScalarSeries
public import ProjectAinos.SpecialFunctions.GegenbauerOrthogonality
public import ProjectAinos.SpecialFunctions.SphericalOrthogonality
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic

/-!
# Uniqueness of the coefficients of the scalar harmonics of `S³`

Landau–Lifshitz, §115. The closed scalar harmonics `closedHarmonic p m` (a solid harmonic
`p ∈ harmonics 3 l` times the Gegenbauer profile `Fₘ = Re Cₘ^{(l+1)}` of the zeroth ambient
co-ordinate, eigenvalue `n(n + 2)`, `n = l + m`) are linearly independent in the sense used for
expansions, and the expansions of closed dust perturbations solve the scalar system exactly when
their modes do.

* `closedHarmonic_chartPoint`: on the sphere `|x| = r` of the chart,
  `closedHarmonic p m (r u) = sinˡ θ · Fₘ(cos θ) · p(u)` with `r = 2 tan(θ/2)` (`chartPoint`,
  `chartRadius`): the chart is stereographic and `θ` is the polar angle on `S³`.
  `exists_bound_closedHarmonic`: the closed harmonics are bounded on the chart.
* `closedHarmonic_coeff_eq_zero`: **uniqueness of the coefficients**: if
  `Σ_{l,m} closedHarmonic (P_{l,m}) m` converges absolutely and uniformly on a time slice and
  vanishes there, every `P_{l,m} ∈ harmonics 3 l` is zero. The proof integrates against a
  spherical harmonic on the spheres `|x| = r` (orthogonality of the degrees on `S²`,
  `SphericalHarmonics.integral_mul_eq_zero`) and then in the polar angle against
  `Fₘ(cos θ) sin^{l+2} θ` (orthogonality of the Gegenbauer profiles,
  `ClassicalPolynomial.integral_gegenbauerReal_mul_eq_zero`).
* `isModeFamily_closed`, `isModeFamily_open`: the closed harmonics and the open harmonics with
  given frequencies are families of separated modes; `closed_scalarSystemAt_dust`,
  `open_scalarSystemAt_dust`: **an expansion in them converging with two derivatives, each mode
  with a dust time function (`IsDustTime`), solves the scalar system on the whole chart**.
* `hasUniqueCoefficients_closed`: the closed harmonics built from bases of the solid harmonics
  (`ClosedIndex`, `closedBasisHarmonic`) have unique coefficients on every time slice, and
  `closed_scalarSystemAt_slice_iff`: **an expansion of a closed dust perturbation in such modes,
  converging with two derivatives and with summable residuals, solves the scalar system on a
  time slice if and only if every mode satisfies its evolution equation at that time**;
  `closed_finite_scalarSystemAt_slice_iff`: in particular every finite expansion
  (`isC2Series_closedBasis_finite`, `exists_residual_bound_finite`).
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

/-! ### The closed harmonics on the spheres of the chart -/

/-- The chart point `(t, r u)`. -/
def chartPoint (t r : ℝ) (u : E3) : E := Fin.cons t fun j => r * u j

@[simp] theorem chartPoint_zero (t r : ℝ) (u : E3) : chartPoint t r u 0 = t := rfl

theorem chartPoint_succ (t r : ℝ) (u : E3) (j : Fin 3) : chartPoint t r u j.succ = r * u j := rfl

theorem sum_sq_of_mem_sphere (u : UnitSphere 3) : ∑ j : Fin 3, (u : E3) j ^ 2 = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq (u : E3)
  rw [norm_eq_of_mem_sphere u, one_pow] at h
  exact h.symm

theorem psi_chartPoint (t r : ℝ) (u : UnitSphere 3) : psi 1 (chartPoint t r u) = 1 + r ^ 2 / 4 := by
  have h := sum_sq_of_mem_sphere u
  simp only [Fin.sum_univ_three] at h
  simp only [psi, show (1 : Fin 4) = Fin.succ 0 from rfl, show (2 : Fin 4) = Fin.succ 1 from rfl,
    show (3 : Fin 4) = Fin.succ 2 from rfl, chartPoint_succ]
  linear_combination r ^ 2 / 4 * h

/-- **A closed harmonic on the sphere `|x| = r` of the chart**. -/
theorem closedHarmonic_chartPoint {l : ℕ} (p : harmonics 3 l) (m : ℕ) (t r : ℝ)
    (u : UnitSphere 3) :
    closedHarmonic p m (chartPoint t r u) = (r / (1 + r ^ 2 / 4)) ^ l *
      gegenbauerReal l m (2 / (1 + r ^ 2 / 4) - 1) * restrict 3 l p.val u := by
  have hpsi := psi_chartPoint t r u
  have hψ : (0 : ℝ) < 1 + r ^ 2 / 4 := by positivity
  have hx : (fun j : Fin 3 => chartPoint t r u j.succ) = ⇑(r • (u : E3)) := by
    funext j; simp [chartPoint_succ]
  have hhom : (p.val.val).IsHomogeneous l :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mp p.val.property
  have he := eval_smul hhom r (u : E3)
  simp only [closedHarmonic, chartHarmonic, chartCoordinate, hpsi, hx, he, gegenbauerReal]
  change r ^ l * MvPolynomial.eval (u : E3) p.val.val * (1 + r ^ 2 / 4) ^ (-(l : ℤ)) * _ =
    _ * _ * MvPolynomial.eval (u : E3) p.val.val
  rw [zpow_neg, zpow_natCast, div_pow]
  field_simp

theorem continuous_restrict {l : ℕ} (p : harmonics 3 l) : Continuous (restrict 3 l p.val) := by
  change Continuous fun u : UnitSphere 3 => MvPolynomial.eval (u : E3) p.val.val
  exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp continuous_subtype_val)

theorem restrict_mem_space {l : ℕ} (p : harmonics 3 l) : restrict 3 l p.val ∈ space 3 l :=
  ⟨p.val, p.property, rfl⟩

/-- The chart radius `r = 2 sin θ/(1 + cos θ) = 2 tan(θ/2)` of the polar angle `θ`. -/
def chartRadius (θ : ℝ) : ℝ := 2 * sin θ / (1 + cos θ)

theorem chartRadius_spec {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 < chartRadius θ ∧ chartRadius θ / (1 + chartRadius θ ^ 2 / 4) = sin θ ∧
      2 / (1 + chartRadius θ ^ 2 / 4) - 1 = cos θ := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hc : 0 < 1 + cos θ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
    rw [cos_pi] at this; linarith
  have hsc := sin_sq_add_cos_sq θ
  have hψ : 1 + chartRadius θ ^ 2 / 4 = 2 / (1 + cos θ) := by
    simp only [chartRadius]
    field_simp
    nlinarith
  refine ⟨by unfold chartRadius; positivity, ?_, ?_⟩
  · rw [hψ]; simp only [chartRadius]; field_simp
  · rw [hψ]; field_simp; ring

/-! ### Uniqueness of the coefficients -/

/-- The surface measure of `S²`. -/
abbrev sphereMeasure : Measure (UnitSphere 3) := (volume : Measure E3).toSphere

theorem exists_bound_restrict {l : ℕ} (p : harmonics 3 l) :
    ∃ C, 0 ≤ C ∧ ∀ u, |restrict 3 l p.val u| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := UnitSphere 3)).exists_bound_of_continuousOn
    (continuous_restrict p).continuousOn
  exact ⟨max C 0, le_max_right _ _, fun u =>
    (show |restrict 3 l p.val u| ≤ C by simpa using hC u (mem_univ _)).trans (le_max_left _ _)⟩

/-- **Uniqueness of the coefficients of the closed harmonics**: an absolutely and uniformly
summable series of closed harmonics that vanishes on a time slice of the chart has vanishing
coefficients. -/
theorem closedHarmonic_coeff_eq_zero (P : (lm : ℕ × ℕ) → harmonics 3 lm.1) {M : ℕ × ℕ → ℝ}
    (hM : Summable M) {t : ℝ} (hb : ∀ lm, ∀ x : E, x 0 = t → |closedHarmonic (P lm) lm.2 x| ≤ M lm)
    (h : ∀ x : E, x 0 = t → ∑' lm, closedHarmonic (P lm) lm.2 x = 0) (lm₀ : ℕ × ℕ) :
    P lm₀ = 0 := by
  obtain ⟨L, m₀⟩ := lm₀
  set q : harmonics 3 L := P (L, m₀)
  obtain ⟨Cq, hCq0, hCq⟩ := exists_bound_restrict q
  set σS : ℝ := (sphereMeasure Set.univ).toReal
  -- the angular pairings
  let a : ℕ → ℝ := fun m => ∫ u, restrict 3 L (P (L, m)).val u * restrict 3 L q.val u ∂sphereMeasure
  have hM0 (lm : ℕ × ℕ) : 0 ≤ M lm :=
    (abs_nonneg _).trans (hb lm (chartPoint t 0 0) rfl)
  -- the terms integrated against `q` on the sphere `|x| = r`
  have hterm (r : ℝ) (lm : ℕ × ℕ) : ∫ u, closedHarmonic (P lm) lm.2 (chartPoint t r u) *
      restrict 3 L q.val u ∂sphereMeasure =
      (r / (1 + r ^ 2 / 4)) ^ lm.1 * gegenbauerReal lm.1 lm.2 (2 / (1 + r ^ 2 / 4) - 1) *
        ∫ u, restrict 3 lm.1 (P lm).val u * restrict 3 L q.val u ∂sphereMeasure := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun u => by
      simp only [closedHarmonic_chartPoint]; ring)
  have hcont (r : ℝ) (lm : ℕ × ℕ) : Continuous fun u : UnitSphere 3 =>
      closedHarmonic (P lm) lm.2 (chartPoint t r u) * restrict 3 L q.val u := by
    simp only [closedHarmonic_chartPoint]
    exact (continuous_const.mul (continuous_restrict _)).mul (continuous_restrict q)
  have hbound (r : ℝ) (lm : ℕ × ℕ) (u : UnitSphere 3) :
      ‖closedHarmonic (P lm) lm.2 (chartPoint t r u) * restrict 3 L q.val u‖ ≤ M lm * Cq := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hb lm _ rfl) (hCq u) (abs_nonneg _) (hM0 lm)
  have hint (r : ℝ) (lm : ℕ × ℕ) : Integrable (fun u : UnitSphere 3 =>
      closedHarmonic (P lm) lm.2 (chartPoint t r u) * restrict 3 L q.val u) sphereMeasure :=
    (integrable_const (M lm * Cq)).mono' (hcont r lm).aestronglyMeasurable
      (ae_of_all _ (hbound r lm))
  have hnorm (r : ℝ) (lm : ℕ × ℕ) : ∫ u, ‖closedHarmonic (P lm) lm.2 (chartPoint t r u) *
      restrict 3 L q.val u‖ ∂sphereMeasure ≤ M lm * Cq * σS := by
    have := norm_integral_le_of_norm_le_const (μ := sphereMeasure)
      (f := fun u => ‖closedHarmonic (P lm) lm.2 (chartPoint t r u) * restrict 3 L q.val u‖)
      (C := M lm * Cq) (ae_of_all _ fun u => by rw [norm_norm]; exact hbound r lm u)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at this
    simpa [σS, measureReal_def] using this
  -- step A: on each sphere, the series of the Gegenbauer profiles vanishes
  have stepA (r : ℝ) : ∑' m, (r / (1 + r ^ 2 / 4)) ^ L *
      gegenbauerReal L m (2 / (1 + r ^ 2 / 4) - 1) * a m = 0 := by
    have hsum : Summable fun lm => ∫ u, ‖closedHarmonic (P lm) lm.2 (chartPoint t r u) *
        restrict 3 L q.val u‖ ∂sphereMeasure :=
      ((hM.mul_right Cq).mul_right σS).of_nonneg_of_le
        (fun _ => integral_nonneg fun _ => norm_nonneg _) (hnorm r)
    have h1 := integral_tsum_of_summable_integral_norm (hint r) hsum
    have h2 : ∫ u, ∑' lm, closedHarmonic (P lm) lm.2 (chartPoint t r u) *
        restrict 3 L q.val u ∂sphereMeasure = 0 := by
      refine integral_eq_zero_of_ae (ae_of_all _ fun u => ?_)
      beta_reduce
      rw [Pi.zero_apply, tsum_mul_right, h _ rfl, zero_mul]
    rw [h2] at h1
    simp only [hterm] at h1
    have hz (lm : ℕ × ℕ) (hl : lm.1 ≠ L) :
        ∫ u, restrict 3 lm.1 (P lm).val u * restrict 3 L q.val u ∂sphereMeasure = 0 :=
      integral_mul_eq_zero (by norm_num) hl (restrict_mem_space _) (restrict_mem_space q)
    rw [← Function.Injective.tsum_eq (g := fun m : ℕ => (L, m))
      (fun m m' e => (Prod.mk.inj e).2) (fun lm hlm => ?_)] at h1
    · exact h1
    · by_cases hl : lm.1 = L
      · exact ⟨lm.2, Prod.ext hl.symm rfl⟩
      · exact absurd (by rw [Function.mem_support] at hlm; simp [hz lm hl] at hlm) id
  -- step B: in the polar angle
  have stepB (θ : ℝ) (hθ : θ ∈ Ioo 0 π) :
      ∑' m, sin θ ^ L * gegenbauerReal L m (cos θ) * a m = 0 := by
    obtain ⟨-, h1, h2⟩ := chartRadius_spec hθ
    have := stepA (chartRadius θ)
    rwa [h1, h2] at this
  have boundB (θ : ℝ) (hθ : θ ∈ Ioo 0 π) (m : ℕ) :
      |sin θ ^ L * gegenbauerReal L m (cos θ) * a m| ≤ M (L, m) * Cq * σS := by
    obtain ⟨-, h1, h2⟩ := chartRadius_spec hθ
    have e := hterm (chartRadius θ) (L, m)
    simp only [h1, h2] at e
    rw [← e, ← Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans (hnorm _ (L, m))
  -- step C: integrate against the profile of degree m₀
  set w : ℝ → ℝ := fun θ => gegenbauerReal L m₀ (cos θ) * sin θ ^ (L + 2)
  have hwπ : w π = 0 := by
    show gegenbauerReal L m₀ (cos π) * sin π ^ (L + 2) = 0
    simp
  have hw : Continuous w :=
    ((continuous_gegenbauerReal L m₀).comp continuous_cos).mul (continuous_sin.pow _)
  obtain ⟨Bw, hBw⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := π)).exists_bound_of_continuousOn
    hw.continuousOn
  have hBw0 : 0 ≤ Bw := (norm_nonneg _).trans (hBw 0 ⟨le_rfl, pi_pos.le⟩)
  let G : ℕ → ℝ → ℝ := fun m θ => sin θ ^ L * gegenbauerReal L m (cos θ) * a m * w θ
  have hGcont (m : ℕ) : Continuous (G m) :=
    (((continuous_sin.pow _).mul ((continuous_gegenbauerReal L m).comp continuous_cos)).mul
      continuous_const).mul hw
  have hGb (m : ℕ) : ∀ θ ∈ Ioc 0 π, ‖G m θ‖ ≤ M (L, m) * Cq * σS * Bw := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.2 with he | hlt
    · have h0 : G m θ = 0 := by simp [G, he, hwπ]
      rw [h0, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (hM0 _) hCq0) ENNReal.toReal_nonneg) hBw0
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (boundB θ ⟨hθ.1, hlt⟩ m) (hBw θ ⟨hθ.1.le, hθ.2⟩) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (hM0 _) hCq0) ENNReal.toReal_nonneg)
  have hGint (m : ℕ) : Integrable (G m) (volume.restrict (Ioc 0 π)) :=
    ((hGcont m).integrableOn_Icc (a := 0) (b := π)).mono_set Ioc_subset_Icc_self
  have hGsum : Summable fun m => ∫ θ, ‖G m θ‖ ∂(volume.restrict (Ioc 0 π)) := by
    refine ((((hM.comp_injective (fun m m' e => (Prod.mk.inj e).2 :
      Function.Injective fun m : ℕ => (L, m))).mul_right Cq).mul_right σS).mul_right
        (Bw * π)).of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
        (fun m => ?_)
    have := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc 0 π))
      (f := fun θ => ‖G m θ‖) (C := M (L, m) * Cq * σS * Bw)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun θ hθ => by
        rw [norm_norm]; exact hGb m θ hθ))
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at this
    simp only [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal pi_pos.le, measureReal_def] at this
    calc _ ≤ M (L, m) * Cq * σS * Bw * π := this
      _ = _ := by simp only [Function.comp]; ring
  have hC := integral_tsum_of_summable_integral_norm hGint hGsum
  have hzero : ∫ θ, ∑' m, G m θ ∂(volume.restrict (Ioc 0 π)) = 0 := by
    refine integral_eq_zero_of_ae ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun θ hθ => ?_))
    rcases eq_or_lt_of_le hθ.2 with he | hlt
    · simp [G, he, hwπ]
    · simp only [G]
      rw [tsum_mul_right, stepB θ ⟨hθ.1, hlt⟩, zero_mul]; rfl
  rw [hzero] at hC
  have hGeq (m : ℕ) : ∫ θ, G m θ ∂(volume.restrict (Ioc 0 π)) = a m *
      ∫ θ in (0 : ℝ)..π, gegenbauerReal L m (cos θ) * gegenbauerReal L m₀ (cos θ) *
        sin θ ^ (2 * L + 2) := by
    rw [intervalIntegral.integral_of_le pi_pos.le, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun θ => by simp only [G, w]; ring)
  simp only [hGeq] at hC
  rw [tsum_eq_single m₀ (fun m hm => by
    rw [integral_gegenbauerReal_mul_eq_zero L hm, mul_zero])] at hC
  have ha : a m₀ = 0 :=
    (mul_eq_zero.mp hC).resolve_right (integral_gegenbauerReal_sq_pos L m₀).ne'
  -- step D: the harmonic itself vanishes
  have hsq : (fun u => restrict 3 L q.val u * restrict 3 L q.val u) =ᵐ[sphereMeasure] 0 := by
    refine (integral_eq_zero_iff_of_nonneg (fun u => mul_self_nonneg _) ?_).mp ha
    exact (continuous_restrict q).mul (continuous_restrict q) |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hq : restrict 3 L q.val = 0 := by
    have := (Continuous.ae_eq_iff_eq sphereMeasure
      ((continuous_restrict q).mul (continuous_restrict q)) continuous_const).mp hsq
    funext u
    have h : restrict 3 L q.val u * restrict 3 L q.val u = 0 := congrFun this u
    simpa using h
  have := restrict_injective (by norm_num : 0 < 3) L (show restrict 3 L q.val = restrict 3 L 0 by
    rw [hq, map_zero])
  exact Subtype.ext this

/-! ### Families of closed and open harmonics -/

variable {ι : Type*}

/-- **The closed harmonics are a family of separated modes** of the closed dust universe, with
the eigenvalues `n(n + 2)`, `n = l + m`. -/
theorem isModeFamily_closed {A : ℝ} (hA : 0 < A) (l : ι → ℕ) (p : ∀ i, harmonics 3 (l i))
    (m : ι → ℕ) {φ : ι → ℝ → ℝ} (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) :
    IsModeFamily (closedDust A hA) φ (fun i => closedHarmonic (p i) (m i))
      (fun i => ((l i + m i : ℕ) : ℝ) * (l i + m i + 2)) where
  smooth_time := hφ
  smooth_space i _ hx :=
    smooth_chartHarmonic (p i) 1 (psi_pos hx).ne' (contDiff_gegenbauerReal (l i) (m i)).contDiffAt
  static i _ hx := (chartHarmonic_time (p i) 1 (psi_pos hx).ne'
    (contDiff_gegenbauerReal (l i) (m i)).contDiffAt).self_of_nhds
  eigen i x _ := by
    change spatialLaplacian 1 (closedHarmonic (p i) (m i)) x = _
    simpa only [neg_mul] using closedHarmonic_equation (p i) (m i) x

/-- **The open harmonics with given frequencies are a family of separated modes** of the open
dust universe, with the eigenvalues `1 + ξ²`. -/
theorem isModeFamily_open {A : ℝ} (hA : 0 < A) (l : ι → ℕ) (p : ∀ i, harmonics 3 (l i))
    (ξ : ι → ℝ) {φ : ι → ℝ → ℝ} (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (openDust A hA).I) :
    IsModeFamily (openDust A hA) φ (fun i => openHarmonic (p i) (ξ i)) (fun i => 1 + ξ i ^ 2) where
  smooth_time := hφ
  smooth_space i _ hx := smooth_chartHarmonic (p i) (-1) (psi_pos hx).ne'
    (Hyperbolic.smooth_ambientProfile_at (ξ i) (l i) (one_le_chartCoordinate (psi_pos hx)))
  static i _ hx := (chartHarmonic_time (p i) (-1) (psi_pos hx).ne'
    (Hyperbolic.smooth_ambientProfile_at (ξ i) (l i)
      (one_le_chartCoordinate (psi_pos hx)))).self_of_nhds
  eigen i _ hx := openHarmonic_equation (p i) (ξ i) (psi_pos hx)

/-- The dust time functions: either solution of the evolution equation. -/
def IsDustTime (D : Data) (φ : ℝ → ℝ) : Prop := ∃ b : ℝ, φ = decay D ∨ φ = growth D b

theorem IsDustTime.evolution {D : Data} (hN : D.N = D.a) {κ : ℝ} {ρ : ℝ → ℝ}
    (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0)) (hc : Continuous D.a)
    {φ : ℝ → ℝ} (hφ : IsDustTime D φ) {t : ℝ} (ht : t ∈ D.I) : Evolution D φ t := by
  obtain ⟨b, h | h⟩ := hφ <;> subst h
  · exact (dust_amplitudes hN hB hc b ht).1
  · exact (dust_amplitudes hN hB hc b ht).2.1

theorem IsDustTime.contDiffOn {D : Data} (hc : Continuous D.a) {φ : ℝ → ℝ}
    (hφ : IsDustTime D φ) : ContDiffOn ℝ ∞ φ D.I := by
  obtain ⟨b, h | h⟩ := hφ <;> subst h
  · exact (smooth_amplitudes D hc b).1
  · exact (smooth_amplitudes D hc b).2

theorem continuous_closedDust_a {A : ℝ} (hA : 0 < A) : Continuous (closedDust A hA).a := by
  change Continuous (fun t => A * (1 - Real.cos t)); fun_prop

theorem continuous_openDust_a {A : ℝ} (hA : 0 < A) : Continuous (openDust A hA).a := by
  change Continuous (fun t => A * (Real.cosh t - 1)); fun_prop

/-- **An expansion of a closed dust perturbation in closed harmonics** converging with two
derivatives, each mode with a dust time function, solves the scalar system on the whole chart. -/
theorem closed_scalarSystemAt_dust {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ) (l : ι → ℕ)
    (p : ∀ i, harmonics 3 (l i)) (m : ι → ℕ) {φ : ι → ℝ → ℝ}
    (hφ : ∀ i, IsDustTime (closedDust A hA) (φ i))
    (hS : IsC2Series (domain (closedDust A hA))
      fun i => separated (φ i) (closedHarmonic (p i) (m i))) {x : E}
    (hx : x ∈ domain (closedDust A hA)) :
    ScalarSystemAt (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
      (fun y => ∑' i, separated (φ i) (closedHarmonic (p i) (m i)) y)
      (fun y => ∑' i, contrast (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
        (φ i) (((l i + m i : ℕ) : ℝ) * (l i + m i + 2)) (closedHarmonic (p i) (m i)) y)
      (fun y j => ∑' i, covelocity (closedDust A hA) κ
        (dustDensity κ (6 * A) (closedDust A hA).a) (φ i) (closedHarmonic (p i) (m i)) y j) x :=
  scalarSystemAt_tsum (isModeFamily_closed hA l p m fun i =>
      (hφ i).contDiffOn (continuous_closedDust_a hA)) hS hx
    (mul_pos hκ (dustDensity_pos hκ (by positivity) (a_pos_of_mem hx))).ne'
    fun i => (hφ i).evolution rfl (isEinstein_closedDust hA hκ.ne') (continuous_closedDust_a hA)
      (time_mem hx)

/-- **An expansion of an open dust perturbation in open harmonics** with given frequencies,
converging with two derivatives, each mode with a dust time function, solves the scalar system on
the whole chart. -/
theorem open_scalarSystemAt_dust {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ) (l : ι → ℕ)
    (p : ∀ i, harmonics 3 (l i)) (ξ : ι → ℝ) {φ : ι → ℝ → ℝ}
    (hφ : ∀ i, IsDustTime (openDust A hA) (φ i))
    (hS : IsC2Series (domain (openDust A hA))
      fun i => separated (φ i) (openHarmonic (p i) (ξ i))) {x : E}
    (hx : x ∈ domain (openDust A hA)) :
    ScalarSystemAt (openDust A hA) κ (dustDensity κ (6 * A) (openDust A hA).a)
      (fun y => ∑' i, separated (φ i) (openHarmonic (p i) (ξ i)) y)
      (fun y => ∑' i, contrast (openDust A hA) κ (dustDensity κ (6 * A) (openDust A hA).a)
        (φ i) (1 + ξ i ^ 2) (openHarmonic (p i) (ξ i)) y)
      (fun y j => ∑' i, covelocity (openDust A hA) κ
        (dustDensity κ (6 * A) (openDust A hA).a) (φ i) (openHarmonic (p i) (ξ i)) y j) x :=
  scalarSystemAt_tsum (isModeFamily_open hA l p ξ fun i =>
      (hφ i).contDiffOn (continuous_openDust_a hA)) hS hx
    (mul_pos hκ (dustDensity_pos hκ (by positivity) (a_pos_of_mem hx))).ne'
    fun i => (hφ i).evolution rfl (isEinstein_openDust hA hκ.ne') (continuous_openDust_a hA)
      (time_mem hx)

/-! ### Closed harmonics from bases of the solid harmonics -/

instance finiteDimensional_harmonics (l : ℕ) : FiniteDimensional ℝ (harmonics 3 l) := by
  let : FiniteDimensional ℝ (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ l) :=
    (Submodule.fg_iff_finiteDimensional _).mp (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  infer_instance

instance free_harmonics (l : ℕ) : Module.Free ℝ (harmonics 3 l) :=
  Module.Free.of_divisionRing ℝ (harmonics 3 l)

/-- A basis of the solid harmonics of degree `l`, indexed by `Fin (2l + 1)`. -/
def harmonicsBasis (l : ℕ) : Module.Basis (Fin (2 * l + 1)) ℝ (harmonics 3 l) :=
  Module.finBasisOfFinrankEq ℝ (harmonics 3 l) (finrank_harmonics_three l)

/-- The index of the closed harmonics built from bases: the degrees `(l, m)` and an element of
a basis of `harmonics 3 l`. -/
abbrev ClosedIndex := Σ lm : ℕ × ℕ, Fin (2 * lm.1 + 1)

/-- The basis element of `harmonics 3 l` of an index. -/
def closedBasis (i : ClosedIndex) : harmonics 3 i.1.1 := harmonicsBasis i.1.1 i.2

/-- The closed harmonic of an index. -/
def closedBasisHarmonic (i : ClosedIndex) : E → ℝ := closedHarmonic (closedBasis i) i.1.2

theorem closedHarmonic_sum {l : ℕ} (m : ℕ) {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    (b : κ → harmonics 3 l) (x : E) :
    closedHarmonic (∑ j ∈ s, c j • b j) m x = ∑ j ∈ s, c j * closedHarmonic (b j) m x := by
  simp only [closedHarmonic, chartHarmonic, Submodule.coe_sum, Submodule.coe_smul,
    map_sum, MvPolynomial.smul_eval, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The closed harmonics built from bases are a family of separated modes. -/
theorem isModeFamily_closedBasis {A : ℝ} (hA : 0 < A) {φ : ClosedIndex → ℝ → ℝ}
    (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) :
    IsModeFamily (closedDust A hA) φ closedBasisHarmonic
      (fun i => ((i.1.1 + i.1.2 : ℕ) : ℝ) * (i.1.1 + i.1.2 + 2)) where
  smooth_time := hφ
  smooth_space i _ hx := smooth_chartHarmonic (closedBasis i) 1 (psi_pos hx).ne'
    (contDiff_gegenbauerReal i.1.1 i.1.2).contDiffAt
  static i _ hx := (chartHarmonic_time (closedBasis i) 1 (psi_pos hx).ne'
    (contDiff_gegenbauerReal i.1.1 i.1.2).contDiffAt).self_of_nhds
  eigen i x _ := by
    change spatialLaplacian 1 (closedHarmonic (closedBasis i) i.1.2) x =
      _ * closedHarmonic (closedBasis i) i.1.2 x
    simpa only [neg_mul] using closedHarmonic_equation (closedBasis i) i.1.2 x

/-- **Closed harmonics built from bases have unique coefficients on every time slice.** -/
theorem hasUniqueCoefficients_closed {A : ℝ} (hA : 0 < A) {t : ℝ}
    (ht : t ∈ (closedDust A hA).I) :
    HasUniqueCoefficients (slice (closedDust A hA) t) closedBasisHarmonic := by
  intro c ⟨M, hM, hb⟩ h i
  have hmem (x : E) (hx : x 0 = t) : x ∈ slice (closedDust A hA) t :=
    ⟨⟨by rw [hx]; exact ht, by show 0 < psi 1 x; unfold psi; positivity⟩, hx⟩
  have hM0 (j : ClosedIndex) : 0 ≤ M j :=
    (abs_nonneg _).trans (hb j _ (hmem (chartPoint t 0 0) rfl))
  let P : (lm : ℕ × ℕ) → harmonics 3 lm.1 := fun lm =>
    ∑ j : Fin (2 * lm.1 + 1), c ⟨lm, j⟩ • harmonicsBasis lm.1 j
  have hP (lm : ℕ × ℕ) (x : E) : closedHarmonic (P lm) lm.2 x =
      ∑ j : Fin (2 * lm.1 + 1), c ⟨lm, j⟩ * closedBasisHarmonic ⟨lm, j⟩ x :=
    closedHarmonic_sum _ _ _ _ x
  have hMs : Summable fun lm : ℕ × ℕ =>
      ∑ j : Fin (2 * lm.1 + 1), M ⟨lm, j⟩ := by
    have := hM.sigma (f := M)
    simpa only [tsum_fintype] using this
  have hP0 := closedHarmonic_coeff_eq_zero P hMs (t := t) (fun lm x hx => by
      rw [hP]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
        hb ⟨lm, j⟩ x (hmem x hx)))
    (fun x hx => by
      have hsum : Summable fun j : ClosedIndex => c j * closedBasisHarmonic j x :=
        hM.of_norm_bounded fun j => by rw [Real.norm_eq_abs]; exact hb j x (hmem x hx)
      have hs := hsum.hasSum.sigma (fun lm => hasSum_fintype _)
      simp only [hP]
      rw [hs.tsum_eq]
      exact h x (hmem x hx))
  obtain ⟨lm, j⟩ := i
  have h0 : ∑ j' : Fin (2 * lm.1 + 1), c ⟨lm, j'⟩ • harmonicsBasis lm.1 j' = 0 := hP0 lm
  have h2 := congrArg (fun v => (harmonicsBasis lm.1).repr v j) h0
  simp only [map_sum, map_smul, Module.Basis.repr_self, map_zero, Finsupp.coe_zero, Pi.zero_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply] at h2
  simpa using h2

/-- **On a time slice of the closed dust universe, an expansion in closed harmonics built from
bases, converging with two derivatives and with summable evolution residuals, solves the scalar
system if and only if every mode satisfies its evolution equation at that time.** -/
theorem closed_scalarSystemAt_slice_iff {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ)
    {φ : ClosedIndex → ℝ → ℝ} (hφ : ∀ i, ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I)
    (hS : IsC2Series (domain (closedDust A hA))
      fun i => separated (φ i) (closedBasisHarmonic i)) {t : ℝ}
    (ht : t ∈ (closedDust A hA).I)
    (hM : ∃ M : ClosedIndex → ℝ, Summable M ∧ ∀ i, ∀ y ∈ slice (closedDust A hA) t,
      |evolutionResidual (closedDust A hA) (φ i) t * closedBasisHarmonic i y| ≤ M i) :
    (∀ y ∈ slice (closedDust A hA) t, ScalarSystemAt (closedDust A hA) κ
      (dustDensity κ (6 * A) (closedDust A hA).a)
      (fun y => ∑' i, separated (φ i) (closedBasisHarmonic i) y)
      (fun y => ∑' i, contrast (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
        (φ i) (((i.1.1 + i.1.2 : ℕ) : ℝ) * (i.1.1 + i.1.2 + 2)) (closedBasisHarmonic i) y)
      (fun y j => ∑' i, covelocity (closedDust A hA) κ
        (dustDensity κ (6 * A) (closedDust A hA).a) (φ i) (closedBasisHarmonic i) y j) y) ↔
      ∀ i, Evolution (closedDust A hA) (φ i) t := by
  exact scalarSystemAt_slice_iff (isModeFamily_closedBasis hA hφ) hS
    (mul_pos hκ (dustDensity_pos hκ (by positivity) ((closedDust A hA).a_pos t ht))).ne'
    (hasUniqueCoefficients_closed hA ht) hM

/-! ### Finite expansions -/

/-- Every point of the chart lies on a sphere `|x| = r` about the origin. -/
theorem exists_chartPoint (x : E) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ u : UnitSphere 3, chartPoint (x 0) r u = x := by
  set v : E3 := WithLp.toLp 2 fun j : Fin 3 => x j.succ
  by_cases hv : v = 0
  · refine ⟨0, le_rfl, ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩, ?_⟩
    funext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rfl
    · have := congrArg (fun w : E3 => w j) hv
      simp only [v, PiLp.zero_apply] at this
      rw [chartPoint_succ, zero_mul]
      exact this.symm
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨‖v‖, norm_nonneg _, ⟨‖v‖⁻¹ • v, by simp [norm_smul, hn]⟩, ?_⟩
    funext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rfl
    · rw [chartPoint_succ]
      simp only [PiLp.smul_apply, smul_eq_mul, v]
      rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

/-- **The closed harmonics are bounded on the chart.** -/
theorem exists_bound_closedHarmonic {l : ℕ} (p : harmonics 3 l) (m : ℕ) :
    ∃ C, ∀ x : E, |closedHarmonic p m x| ≤ C := by
  obtain ⟨Cp, hCp0, hCp⟩ := exists_bound_restrict p
  obtain ⟨CF, hCF⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_gegenbauerReal l m).continuousOn
  refine ⟨CF * Cp, fun x => ?_⟩
  obtain ⟨r, hr, u, hx⟩ := exists_chartPoint x
  rw [← hx, closedHarmonic_chartPoint]
  have hψ : 0 < 1 + r ^ 2 / 4 := by positivity
  have h1 : 0 ≤ r / (1 + r ^ 2 / 4) := div_nonneg hr hψ.le
  have h2 : r / (1 + r ^ 2 / 4) ≤ 1 := by
    rw [div_le_one hψ]; nlinarith [sq_nonneg (r / 2 - 1)]
  have hs : 2 / (1 + r ^ 2 / 4) - 1 ∈ Icc (-1 : ℝ) 1 := by
    have h3 : 2 / (1 + r ^ 2 / 4) ≤ 2 := by
      rw [div_le_iff₀ hψ]; nlinarith [sq_nonneg r]
    have h4 : 0 < 2 / (1 + r ^ 2 / 4) := by positivity
    constructor <;> linarith
  have hF := hCF _ hs
  rw [Real.norm_eq_abs] at hF
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg h1]
  have hpow : (r / (1 + r ^ 2 / 4)) ^ l ≤ 1 := pow_le_one₀ h1 h2
  calc (r / (1 + r ^ 2 / 4)) ^ l * |gegenbauerReal l m (2 / (1 + r ^ 2 / 4) - 1)| *
        |restrict 3 l p.val u| ≤ 1 * CF * Cp :=
      mul_le_mul (mul_le_mul hpow hF (abs_nonneg _) zero_le_one) (hCp u) (abs_nonneg _)
        (mul_nonneg zero_le_one ((norm_nonneg _).trans (hCF 1 ⟨by norm_num, le_rfl⟩)))
    _ = CF * Cp := by ring

/-- **Finite expansions in closed harmonics are series of the class.** -/
theorem isC2Series_closedBasis_finite {A : ℝ} (hA : 0 < A) (s : Finset ClosedIndex)
    {φ : ClosedIndex → ℝ → ℝ} (h0 : ∀ i ∉ s, φ i = 0)
    (hφ : ∀ i ∈ s, ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) :
    IsC2Series (domain (closedDust A hA)) fun i => separated (φ i) (closedBasisHarmonic i) := by
  refine IsC2Series.of_finite_support (domain (closedDust A hA)).isOpen s
    (fun i hi => by funext y; simp [separated, h0 i hi]) fun i hi x hx => ?_
  have hQ : ContDiffAt ℝ ∞ (closedBasisHarmonic i) x :=
    smooth_chartHarmonic (closedBasis i) 1 (psi_pos hx).ne'
      (contDiff_gegenbauerReal i.1.1 i.1.2).contDiffAt
  have hφx : ContDiffAt ℝ ∞ (φ i) (x 0) :=
    (hφ i hi).contDiffAt ((closedDust A hA).isOpen_I.mem_nhds (time_mem hx))
  exact ((hφx.comp x (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0).contDiffAt).mul hQ).of_le
    (by norm_num)

/-- The residuals of a finite expansion are summably bounded on every slice. -/
theorem exists_residual_bound_finite {A : ℝ} (hA : 0 < A) (s : Finset ClosedIndex)
    {φ : ClosedIndex → ℝ → ℝ} (h0 : ∀ i ∉ s, φ i = 0) (t : ℝ) :
    ∃ M : ClosedIndex → ℝ, Summable M ∧ ∀ i, ∀ y ∈ slice (closedDust A hA) t,
      |evolutionResidual (closedDust A hA) (φ i) t * closedBasisHarmonic i y| ≤ M i := by
  classical
  choose C hC using fun i : ClosedIndex => exists_bound_closedHarmonic (closedBasis i) i.1.2
  refine ⟨fun i => if i ∈ s then |evolutionResidual (closedDust A hA) (φ i) t| * C i else 0,
    summable_of_ne_finset_zero (s := s) fun i hi => by simp [hi], fun i y _ => ?_⟩
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC i y) (abs_nonneg _)
  · simp [hi, h0 i hi, evolutionResidual]

/-- **A finite expansion of a closed dust perturbation in closed harmonics solves the scalar
system on a time slice if and only if every mode satisfies its evolution equation** at that
time. -/
theorem closed_finite_scalarSystemAt_slice_iff {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ)
    (s : Finset ClosedIndex) {φ : ClosedIndex → ℝ → ℝ} (h0 : ∀ i ∉ s, φ i = 0)
    (hφ : ∀ i ∈ s, ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) {t : ℝ}
    (ht : t ∈ (closedDust A hA).I) :
    (∀ y ∈ slice (closedDust A hA) t, ScalarSystemAt (closedDust A hA) κ
      (dustDensity κ (6 * A) (closedDust A hA).a)
      (fun y => ∑' i, separated (φ i) (closedBasisHarmonic i) y)
      (fun y => ∑' i, contrast (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
        (φ i) (((i.1.1 + i.1.2 : ℕ) : ℝ) * (i.1.1 + i.1.2 + 2)) (closedBasisHarmonic i) y)
      (fun y j => ∑' i, covelocity (closedDust A hA) κ
        (dustDensity κ (6 * A) (closedDust A hA).a) (φ i) (closedBasisHarmonic i) y j) y) ↔
      ∀ i, Evolution (closedDust A hA) (φ i) t := by
  have hφ' (i : ClosedIndex) : ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I := by
    by_cases hi : i ∈ s
    · exact hφ i hi
    · rw [h0 i hi]; exact contDiffOn_const
  exact closed_scalarSystemAt_slice_iff hA hκ hφ' (isC2Series_closedBasis_finite hA s h0 hφ) ht
    (exists_residual_bound_finite hA s h0 t)

end ProjectAinos.GeneralRelativity.CurvedPerturbation
