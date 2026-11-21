/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.GegenbauerOrthogonality
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-!
# Completeness of the Gegenbauer profiles in the polar angle

For an integer `l ≥ 0` the real profiles `Fₘ = Re Cₘ^{(l+1)}` (`gegenbauerReal`) of degree `m`
span the real polynomials, and a bounded continuous function of the polar angle orthogonal to all
`sin^{l+2} θ · Fₘ(cos θ)` vanishes:

* `gegenbauer_coeff`: `Cₙ^{(λ)}` has degree `n` with the leading coefficient
  `gegenbauerLead λ n = ∏_{j < n} (2j + 2λ)/(j + 1)`, from the raising recursion; for `λ = l + 1`
  it is the positive real number `gegenbauerLeadReal l n` (`gegenbauerLead_eq`).
* `gegenbauerReal_eq_eval`: `Fₘ` is the evaluation of the real polynomial `gegenbauerRealPoly l m`
  of degree `m` with leading coefficient `gegenbauerLeadReal l m`; hence
  `exists_gegenbauer_combination`: **every real polynomial of degree `≤ N` is a combination of
  `F₀, …, F_N`**.
* `eq_zero_of_integral_gegenbauer`: **completeness in the polar angle**: a function `f` bounded and
  continuous on `(0, π)` with `∫_{(0,π)} f(θ) sin^{l+2} θ Fₘ(cos θ) dθ = 0` for every `m` vanishes
  on `(0, π)`. The orthogonality extends to all polynomials in `cos θ`, then by the Weierstrass
  approximation theorem to the continuous function `f(arccos s)(1 − s²)` of `s ∈ [−1, 1]`, which
  gives `∫ f² sin^{l+4} = 0`.
-/

@[expose] public section

noncomputable section

open Polynomial Real Set Filter MeasureTheory
open scoped Topology

namespace ProjectAinos.SpecialFunctions.ClassicalPolynomial

/-! ### The leading coefficient -/

/-- The leading coefficient `∏_{j < n} (2j + 2λ)/(j + 1)` of `Cₙ^{(λ)}`. -/
def gegenbauerLead (l : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => gegenbauerLead l n * (2 * n + 2 * l) / (n + 1)

/-- **The coefficients of the Gegenbauer polynomial**: `Cₙ^{(λ)}` has degree at most `n`, with
the coefficient `gegenbauerLead λ n` of `Xⁿ`. -/
theorem gegenbauer_coeff (l : ℂ) (n : ℕ) :
    (gegenbauer l n).coeff n = gegenbauerLead l n ∧
      ∀ k, n < k → (gegenbauer l n).coeff k = 0 := by
  induction n with
  | zero =>
    refine ⟨by simp [gegenbauer, gegenbauerLead], fun k hk => ?_⟩
    simp [gegenbauer, coeff_one]
    omega
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    set p := gegenbauer l n
    have hrec : gegenbauer l (n + 1) =
        C (((n : ℂ) + 1)⁻¹) * (C ((n : ℂ) + 2 * l) * (X * p) - (derivative p - X ^ 2 *
          derivative p)) := by
      simp only [gegenbauer, p]; ring
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    refine ⟨?_, fun k hk => ?_⟩
    · rw [hrec, coeff_C_mul, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_sub, coeff_derivative,
        coeff_X_pow_mul', h1, h2 (n + 1 + 1) (by omega)]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        simp [gegenbauerLead]
      · obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
        have h2le : 2 ≤ j + 1 + 1 := by omega
        simp only [h2le, ↓reduceIte, show j + 1 + 1 - 2 = j by omega, coeff_derivative, h1]
        simp only [gegenbauerLead]
        push_cast
        field_simp
        ring
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [hrec, coeff_C_mul, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_sub, coeff_derivative,
        coeff_X_pow_mul', h2 j (by omega), h2 (j + 1 + 1) (by omega)]
      split_ifs with h
      · rw [coeff_derivative, h2 (j + 1 - 2 + 1) (by omega)]; simp
      · simp

/-- The leading coefficient for `λ = l + 1`, a positive real number. -/
def gegenbauerLeadReal (l : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => gegenbauerLeadReal l n * (2 * n + 2 * (l + 1)) / (n + 1)

theorem gegenbauerLeadReal_pos (l n : ℕ) : 0 < gegenbauerLeadReal l n := by
  induction n with
  | zero => simp [gegenbauerLeadReal]
  | succ n ih => simp only [gegenbauerLeadReal]; positivity

theorem gegenbauerLead_eq (l n : ℕ) :
    gegenbauerLead ((l : ℂ) + 1) n = (gegenbauerLeadReal l n : ℂ) := by
  induction n with
  | zero => simp [gegenbauerLead, gegenbauerLeadReal]
  | succ n ih => simp only [gegenbauerLead, gegenbauerLeadReal, ih]; push_cast; ring

/-! ### The real profiles as real polynomials -/

/-- The real polynomial `Σ_k Re(cₖ) Xᵏ` of the profile `Fₘ = Re Cₘ^{(l+1)}`. -/
def gegenbauerRealPoly (l m : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1), C ((gegenbauer ((l : ℂ) + 1) m).coeff k).re * X ^ k

theorem gegenbauerReal_eq_eval (l m : ℕ) (s : ℝ) :
    gegenbauerReal l m s = (gegenbauerRealPoly l m).eval s := by
  have hdeg : (gegenbauer ((l : ℂ) + 1) m).natDegree < m + 1 := by
    rw [Nat.lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
    exact (gegenbauer_coeff _ m).2
  simp only [gegenbauerReal, eval_eq_sum_range' hdeg, gegenbauerRealPoly, eval_finsetSum,
    eval_mul, eval_C, eval_pow, eval_X, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]

theorem gegenbauerRealPoly_coeff (l m k : ℕ) :
    (gegenbauerRealPoly l m).coeff k = ((gegenbauer ((l : ℂ) + 1) m).coeff k).re := by
  simp only [gegenbauerRealPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hk : k ≤ m
  · rw [Finset.sum_eq_single k (fun j _ hj => by simp [Ne.symm hj])
      (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
    simp
  · rw [Finset.sum_eq_zero (fun j hj => by
      have := Finset.mem_range.mp hj
      simp [show k ≠ j by omega]), (gegenbauer_coeff _ m).2 k (by omega)]
    simp

theorem gegenbauerRealPoly_natDegree_le (l m : ℕ) : (gegenbauerRealPoly l m).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [gegenbauerRealPoly_coeff, (gegenbauer_coeff _ m).2 k hk, Complex.zero_re]

theorem gegenbauerRealPoly_coeff_self (l m : ℕ) :
    (gegenbauerRealPoly l m).coeff m = gegenbauerLeadReal l m := by
  rw [gegenbauerRealPoly_coeff, (gegenbauer_coeff _ m).1, gegenbauerLead_eq, Complex.ofReal_re]

/-- **The profiles span the polynomials**: every real polynomial of degree at most `N` is a
combination of `F₀, …, F_N`. -/
theorem exists_gegenbauer_combination (l N : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ N) :
    ∃ c : ℕ → ℝ, ∀ s, P.eval s = ∑ m ∈ Finset.range (N + 1), c m * gegenbauerReal l m s := by
  induction N generalizing P with
  | zero =>
    refine ⟨fun _ => P.coeff 0, fun s => ?_⟩
    rw [eq_C_of_natDegree_le_zero hP]
    simp [gegenbauerReal, gegenbauer]
  | succ N ih =>
    set a := P.coeff (N + 1) / gegenbauerLeadReal l (N + 1)
    set Q := P - C a * gegenbauerRealPoly l (N + 1)
    have hQ : Q.natDegree ≤ N := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      simp only [Q, coeff_sub, coeff_C_mul]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with h | h
      · rw [← h, gegenbauerRealPoly_coeff_self]
        simp only [a]
        field_simp [(gegenbauerLeadReal_pos l (N + 1)).ne']
        ring
      · rw [natDegree_le_iff_coeff_eq_zero.mp hP k (by omega),
          natDegree_le_iff_coeff_eq_zero.mp (gegenbauerRealPoly_natDegree_le l (N + 1)) k
            (by omega)]
        ring
    obtain ⟨c, hc⟩ := ih Q hQ
    refine ⟨fun m => if m = N + 1 then a else c m, fun s => ?_⟩
    have e : P = Q + C a * gegenbauerRealPoly l (N + 1) := by simp [Q]
    rw [Finset.sum_range_succ]
    simp only [ite_true]
    rw [e, eval_add, hc, eval_mul, eval_C, ← gegenbauerReal_eq_eval]
    congr 1
    exact Finset.sum_congr rfl fun m hm => by
      simp [show m ≠ N + 1 from (Finset.mem_range.mp hm).ne]

/-! ### Completeness in the polar angle -/

/-- A function bounded and continuous on `(0, π)` is integrable there. -/
theorem integrableOn_Ioo_of_bounded {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo 0 π)) {B : ℝ}
    (hB : ∀ θ ∈ Ioo 0 π, |f θ| ≤ B) :
    IntegrableOn f (Ioo 0 π) := by
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) π)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  refine Integrable.of_bound (hf.aestronglyMeasurable measurableSet_Ioo) B ?_
  exact (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun θ hθ => by
    rw [Real.norm_eq_abs]; exact hB θ hθ)

private theorem abs_sin_pow_le (n : ℕ) (θ : ℝ) : |sin θ ^ n| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_sin_le_one θ)

private theorem term_bound (l : ℕ) {f g : ℝ → ℝ} {B C : ℝ} {θ : ℝ} (hf : |f θ| ≤ B)
    (hg : |g (cos θ)| ≤ C) (hB : 0 ≤ B) :
    |f θ * sin θ ^ (l + 2) * g (cos θ)| ≤ B * C := by
  rw [abs_mul, abs_mul]
  calc |f θ| * |sin θ ^ (l + 2)| * |g (cos θ)| ≤ B * 1 * C :=
        mul_le_mul (mul_le_mul hf (abs_sin_pow_le _ θ) (abs_nonneg _) hB) hg (abs_nonneg _)
          (by positivity)
    _ = B * C := by ring

private theorem integrable_term (l : ℕ) {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo 0 π)) {B : ℝ}
    (hB : ∀ θ ∈ Ioo 0 π, |f θ| ≤ B) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1)) :
    IntegrableOn (fun θ => f θ * sin θ ^ (l + 2) * g (cos θ)) (Ioo 0 π) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hg
  have hgc : ContinuousOn (fun θ => g (cos θ)) (Ioo 0 π) :=
    hg.comp continuous_cos.continuousOn fun θ _ => ⟨neg_one_le_cos θ, cos_le_one θ⟩
  refine integrableOn_Ioo_of_bounded ((hf.mul (continuous_sin.pow _).continuousOn).mul hgc)
    (B := B * C) fun θ hθ => term_bound l (hB θ hθ) ?_ ((abs_nonneg _).trans (hB θ hθ))
  simpa using hC (cos θ) ⟨neg_one_le_cos θ, cos_le_one θ⟩

private theorem cos_mem_Ioo {θ : ℝ} (hθ : θ ∈ Ioo 0 π) : cos θ ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · have := cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
    rwa [cos_pi] at this
  · have := cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2.le hθ.1
    rwa [cos_zero] at this

/-- **Completeness of the Gegenbauer profiles in the polar angle**: a bounded continuous function
on `(0, π)` orthogonal to every `sin^{l+2} θ · Fₘ(cos θ)` vanishes. -/
theorem eq_zero_of_integral_gegenbauer (l : ℕ) {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo 0 π))
    {B : ℝ} (hB : ∀ θ ∈ Ioo 0 π, |f θ| ≤ B)
    (h : ∀ m, ∫ θ in Ioo 0 π, f θ * sin θ ^ (l + 2) * gegenbauerReal l m (cos θ) = 0) :
    ∀ θ ∈ Ioo 0 π, f θ = 0 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (π / 2) ⟨by positivity, by linarith [pi_pos]⟩)
  -- orthogonality to every polynomial in `cos θ`
  have hpoly (P : ℝ[X]) : ∫ θ in Ioo 0 π, f θ * sin θ ^ (l + 2) * P.eval (cos θ) = 0 := by
    obtain ⟨c, hc⟩ := exists_gegenbauer_combination l P.natDegree P le_rfl
    simp only [hc, Finset.mul_sum]
    rw [integral_finsetSum _ fun m _ => ?_]
    · refine Finset.sum_eq_zero fun m _ => ?_
      have e : (fun θ => f θ * sin θ ^ (l + 2) * (c m * gegenbauerReal l m (cos θ))) =
          fun θ => c m * (f θ * sin θ ^ (l + 2) * gegenbauerReal l m (cos θ)) := by
        funext θ; ring
      rw [e, integral_const_mul, h m, mul_zero]
    · have := (integrable_term l hf hB (continuous_gegenbauerReal l m).continuousOn).const_mul
        (c m)
      refine this.congr (ae_of_all _ fun θ => ?_)
      simp only; ring
  -- the continuous function `f(arccos s)(1 − s²)` on `[−1, 1]`
  set hfun : ℝ → ℝ := fun s => if s ∈ Ioo (-1 : ℝ) 1 then f (arccos s) * (1 - s ^ 2) else 0
  have hbound (s : ℝ) : |hfun s| ≤ B * |1 - s ^ 2| := by
    simp only [hfun]
    split_ifs with hs
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hB _ ⟨arccos_pos.mpr hs.2, arccos_lt_pi.mpr hs.1⟩)
        (abs_nonneg _)
    · simp only [abs_zero]; positivity
  have hend (s : ℝ) (hs : s = -1 ∨ s = 1) : ContinuousAt hfun s := by
    have h0 : hfun s = 0 := by
      rcases hs with rfl | rfl <;> simp [hfun]
    have hlim : Tendsto (fun y : ℝ => B * |1 - y ^ 2|) (𝓝 s) (𝓝 0) := by
      have := (show Continuous fun y : ℝ => B * |1 - y ^ 2| by fun_prop).tendsto s
      rcases hs with rfl | rfl <;> simpa using this
    rw [ContinuousAt, h0]
    exact squeeze_zero_norm (fun y => by rw [Real.norm_eq_abs]; exact hbound y) hlim
  have hcont : ContinuousOn hfun (Icc (-1) 1) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · exact (hend s (Or.inl h1.symm)).continuousWithinAt
    rcases eq_or_lt_of_le hs.2 with h2 | h2
    · exact (hend s (Or.inr h2)).continuousWithinAt
    have hmem : Ioo (-1 : ℝ) 1 ∈ 𝓝 s := isOpen_Ioo.mem_nhds ⟨h1, h2⟩
    have hev : (fun s => f (arccos s) * (1 - s ^ 2)) =ᶠ[𝓝 s] hfun := by
      filter_upwards [hmem] with y hy
      simp only [hfun, hy, ↓reduceIte]
    have hc : ContinuousAt (fun s => f (arccos s) * (1 - s ^ 2)) s := by
      refine ContinuousAt.mul ?_ (by fun_prop)
      exact (hf.continuousAt (isOpen_Ioo.mem_nhds ⟨arccos_pos.mpr h2,
        arccos_lt_pi.mpr h1⟩)).comp continuous_arccos.continuousAt
    exact (hc.congr hev).continuousWithinAt
  have hcos (θ : ℝ) : cos θ ∈ Icc (-1 : ℝ) 1 := ⟨neg_one_le_cos θ, cos_le_one θ⟩
  -- `∫ f² sin^{l+4} = 0`
  have heq : ∫ θ in Ioo 0 π, f θ * sin θ ^ (l + 2) * (f θ * sin θ ^ 2) =
      ∫ θ in Ioo 0 π, f θ * sin θ ^ (l + 2) * hfun (cos θ) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
    simp only [hfun, cos_mem_Ioo hθ, ↓reduceIte, arccos_cos hθ.1.le hθ.2.le, ← sin_sq]
  have hsmall (ε : ℝ) (hε : 0 < ε) :
      |∫ θ in Ioo 0 π, f θ * sin θ ^ (l + 2) * hfun (cos θ)| ≤ ε := by
    set δ := ε / (B * π + 1)
    obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-1) 1 hfun hcont δ
      (by positivity)
    have hPc : ContinuousOn (fun s => P.eval s - hfun s) (Icc (-1) 1) :=
      P.continuous.continuousOn.sub hcont
    have e : ∫ θ in Ioo 0 π, f θ * sin θ ^ (l + 2) * hfun (cos θ) =
        -∫ θ in Ioo 0 π, f θ * sin θ ^ (l + 2) * (P.eval (cos θ) - hfun (cos θ)) := by
      rw [eq_neg_iff_add_eq_zero, ← integral_add (integrable_term l hf hB hcont)
        (integrable_term l hf hB hPc)]
      refine Eq.trans ?_ (hpoly P)
      congr 1; funext θ; ring
    rw [e, abs_neg, ← Real.norm_eq_abs]
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (0 : ℝ) π)
      (f := fun θ => f θ * sin θ ^ (l + 2) * (P.eval (cos θ) - hfun (cos θ))) (C := B * δ)
      (by simp) fun θ hθ => by
        rw [Real.norm_eq_abs]
        exact term_bound l (g := fun s => P.eval s - hfun s) (hB θ hθ) (hP _ (hcos θ)).le hB0
    refine hb.trans ?_
    rw [Real.volume_real_Ioo_of_le pi_pos.le, sub_zero]
    have : B * δ * π = ε * (B * π) / (B * π + 1) := by simp only [δ]; ring
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith [pi_pos, mul_nonneg hB0 pi_pos.le]
  have hsq : ∫ θ in Ioo 0 π, f θ * sin θ ^ (l + 2) * (f θ * sin θ ^ 2) = 0 := by
    rw [heq]
    by_contra hne
    have := hsmall (|∫ θ in Ioo 0 π, f θ * sin θ ^ (l + 2) * hfun (cos θ)| / 2)
      (by positivity)
    linarith [abs_pos.mpr hne]
  -- the integrand vanishes
  intro θ₀ hθ₀
  by_contra hne
  set G : ℝ → ℝ := fun θ => f θ * sin θ ^ (l + 2) * (f θ * sin θ ^ 2)
  have hG (θ : ℝ) : G θ = (f θ) ^ 2 * sin θ ^ (l + 4) := by simp only [G]; ring
  have hGnn : ∀ θ ∈ Ioo 0 π, 0 ≤ G θ := fun θ hθ => by
    rw [hG]
    exact mul_nonneg (sq_nonneg _) (pow_nonneg (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le _)
  have hGpos : 0 < G θ₀ := by
    rw [hG]
    exact mul_pos (by positivity) (pow_pos (sin_pos_of_pos_of_lt_pi hθ₀.1 hθ₀.2) _)
  have hGc : ContinuousOn G (Ioo 0 π) :=
    ((hf.mul (continuous_sin.pow _).continuousOn).mul (hf.mul
      (continuous_sin.pow _).continuousOn))
  have hGint : IntegrableOn G (Ioo 0 π) := by
    refine integrableOn_Ioo_of_bounded hGc (B := B * B) fun θ hθ => ?_
    rw [hG, abs_mul, abs_pow, abs_pow]
    have h1 : |sin θ| ^ (l + 4) ≤ 1 := pow_le_one₀ (abs_nonneg _) (abs_sin_le_one θ)
    have h2 : |f θ| ^ 2 ≤ B * B := by
      rw [sq]; exact mul_self_le_mul_self (abs_nonneg _) (hB θ hθ)
    nlinarith [pow_nonneg (abs_nonneg (f θ)) 2, pow_nonneg (abs_nonneg (sin θ)) (l + 4)]
  have hpos : 0 < ∫ θ in Ioo 0 π, G θ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ hGnn)) hGint]
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
      (hGc.isOpen_inter_preimage isOpen_Ioo isOpen_Ioi) θ₀ ⟨hθ₀, hGpos⟩
    have hsub : Ioo (θ₀ - δ) (θ₀ + δ) ⊆ Function.support G ∩ Ioo 0 π := by
      intro θ hθ
      have hm := hball (show θ ∈ Metric.ball θ₀ δ by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hθ.1, hθ.2])
      exact ⟨ne_of_gt hm.2, hm.1⟩
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    simp [hδ]
  exact hpos.ne' hsq

end ProjectAinos.SpecialFunctions.ClassicalPolynomial
