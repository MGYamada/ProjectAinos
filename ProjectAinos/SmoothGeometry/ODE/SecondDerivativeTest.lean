/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# A positive second variation of a length functional gives a longer curve

The analytic step of the second variation of proper time, without differentiating under the
integral sign.

* `SecondDerivativeTest.add_le_of_le_deriv`: **a second-order Taylor bound**: if `f'' ≥ m` on
  `[0, ε]`, then `f(ε) ≥ f(0) + ε f'(0) + m ε²/2`; `SecondDerivativeTest.le_add_of_deriv_le`:
  the bound from above.
* `SecondDerivativeTest.sqrt_ge`: `√y ≥ (3y − y²)/2` for every real `y`.
* `SecondDerivativeTest.exists_lt_integral_sqrt`: **a family `φ(ε, s)` with `φ(0, s) = 1`,
  `∂_ε φ(0, s) = 0` and `∫₀ᴸ ∂²_ε φ(0, s) ds > 0`, with `∂²_ε φ` continuous on a rectangle, has
  `φ(ε, ·) > 0` and `∫₀ᴸ √φ(ε, s) ds > L` for some small `ε > 0`.** For the squared speed
  `φ = −g(ċ_ε, ċ_ε)` of a variation of a unit-speed timelike curve, the varied curve is timelike
  and longer.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace ProjectAinos.SmoothGeometry.SecondDerivativeTest

/-- **A second-order Taylor bound from below**: if `f' = f₁`, `f₁' = f₂` on `[0, ε]` and
`f₂ ≥ m` there, then `f(0) + ε f₁(0) + m ε²/2 ≤ f(ε)`. -/
theorem add_le_of_le_deriv {f f₁ f₂ : ℝ → ℝ} {ε m : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ t ∈ Icc 0 ε, HasDerivAt f (f₁ t) t) (hf₁ : ∀ t ∈ Icc 0 ε, HasDerivAt f₁ (f₂ t) t)
    (hm : ∀ t ∈ Icc 0 ε, m ≤ f₂ t) : f 0 + ε * f₁ 0 + m * ε ^ 2 / 2 ≤ f ε := by
  have h0 : (0 : ℝ) ∈ Icc 0 ε := ⟨le_rfl, hε⟩
  have hε' : ε ∈ Icc 0 ε := ⟨hε, le_rfl⟩
  -- the first derivative grows at least like `m t`
  have hd₁ (t : ℝ) (ht : t ∈ Icc 0 ε) :
      HasDerivAt (fun t => f₁ t - f₁ 0 - m * t) (f₂ t - m) t := by
    have h := ((hf₁ t ht).sub_const (f₁ 0)).fun_sub ((hasDerivAt_id' t).const_mul m)
    convert h using 1
    ring
  have hmono₁ : MonotoneOn (fun t => f₁ t - f₁ 0 - m * t) (Icc 0 ε) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 ε)
      (fun t ht => (hd₁ t ht).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Icc]
      exact fun t ht => (hd₁ t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hd₁ t (Ioo_subset_Icc_self ht)).deriv]
      linarith [hm t (Ioo_subset_Icc_self ht)]
  have hpos₁ (t : ℝ) (ht : t ∈ Icc 0 ε) : 0 ≤ f₁ t - f₁ 0 - m * t := by
    have h := hmono₁ h0 ht ht.1
    simp only [sub_self, mul_zero] at h
    exact h
  have hd (t : ℝ) (ht : t ∈ Icc 0 ε) :
      HasDerivAt (fun t => f t - f 0 - t * f₁ 0 - m * t ^ 2 / 2) (f₁ t - f₁ 0 - m * t) t := by
    have h := (((hf t ht).sub_const (f 0)).fun_sub ((hasDerivAt_id' t).mul_const (f₁ 0))).fun_sub
      (((hasDerivAt_pow 2 t).const_mul m).div_const 2)
    convert h using 1
    rw [show ((2 : ℕ) : ℝ) * t ^ (2 - 1) = 2 * t by norm_num]
    ring
  have hmono : MonotoneOn (fun t => f t - f 0 - t * f₁ 0 - m * t ^ 2 / 2) (Icc 0 ε) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 ε)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Icc]
      exact fun t ht => (hd t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hd t (Ioo_subset_Icc_self ht)).deriv]
      exact hpos₁ t (Ioo_subset_Icc_self ht)
  have h := hmono h0 hε' hε
  simp only [sub_self, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, zero_div] at h
  linarith

/-- **A second-order Taylor bound from above**: if `f' = f₁`, `f₁' = f₂` on `[0, ε]` and
`f₂ ≤ M` there, then `f(ε) ≤ f(0) + ε f₁(0) + M ε²/2`. -/
theorem le_add_of_deriv_le {f f₁ f₂ : ℝ → ℝ} {ε M : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ t ∈ Icc 0 ε, HasDerivAt f (f₁ t) t) (hf₁ : ∀ t ∈ Icc 0 ε, HasDerivAt f₁ (f₂ t) t)
    (hM : ∀ t ∈ Icc 0 ε, f₂ t ≤ M) : f ε ≤ f 0 + ε * f₁ 0 + M * ε ^ 2 / 2 := by
  have h := add_le_of_le_deriv (f := fun t => -f t) (f₁ := fun t => -f₁ t)
    (f₂ := fun t => -f₂ t) (m := -M) hε (fun t ht => (hf t ht).neg) (fun t ht => (hf₁ t ht).neg)
    (fun t ht => neg_le_neg (hM t ht))
  linarith

/-- `√y ≥ (3y − y²)/2` for every real `y`: with `x = √y ≥ 0`, the difference is
`x (x − 1)² (x + 2)/2`. -/
theorem sqrt_ge (y : ℝ) : (3 * y - y ^ 2) / 2 ≤ Real.sqrt y := by
  rcases le_or_gt y 0 with hy | hy
  · have h : 3 * y - y ^ 2 ≤ 0 := by nlinarith [sq_nonneg y]
    linarith [Real.sqrt_nonneg y]
  · set x := Real.sqrt y with hx
    have hx0 : 0 ≤ x := Real.sqrt_nonneg y
    have hxy : y = x ^ 2 := (Real.sq_sqrt hy.le).symm
    rw [hxy]
    nlinarith [mul_nonneg (mul_nonneg hx0 (sq_nonneg (x - 1))) (by linarith : (0 : ℝ) ≤ x + 2)]

/-- **A positive second variation gives a longer curve.** Let `φ(ε, s)` be defined for
`ε ∈ [0, ε₀]` and `s ∈ [0, L]`, with `∂_ε φ = φ₁` and `∂_ε φ₁ = φ₂`, `φ₂` continuous on the
rectangle, `φ(ε, ·)` continuous, `φ(0, s) = 1`, `φ₁(0, s) = 0` and `∫₀ᴸ φ₂(0, s) ds > 0`. Then for
some `ε ∈ (0, ε₀]`, `φ(ε, s) > 0` on `[0, L]` and `∫₀ᴸ √φ(ε, s) ds > L`. -/
theorem exists_lt_integral_sqrt {φ φ₁ φ₂ : ℝ → ℝ → ℝ} {L ε₀ : ℝ} (hL : 0 < L) (hε₀ : 0 < ε₀)
    (h1 : ∀ s ∈ Icc 0 L, ∀ ε ∈ Icc 0 ε₀, HasDerivAt (fun e => φ e s) (φ₁ ε s) ε)
    (h2 : ∀ s ∈ Icc 0 L, ∀ ε ∈ Icc 0 ε₀, HasDerivAt (fun e => φ₁ e s) (φ₂ ε s) ε)
    (h3 : ContinuousOn (fun q : ℝ × ℝ => φ₂ q.1 q.2) (Icc 0 ε₀ ×ˢ Icc 0 L))
    (h4 : ∀ ε ∈ Icc 0 ε₀, ContinuousOn (φ ε) (Icc 0 L))
    (h5 : ∀ s ∈ Icc 0 L, φ 0 s = 1 ∧ φ₁ 0 s = 0)
    (h6 : 0 < ∫ s in (0 : ℝ)..L, φ₂ 0 s) :
    ∃ ε ∈ Ioc 0 ε₀, (∀ s ∈ Icc 0 L, 0 < φ ε s) ∧ L < ∫ s in (0 : ℝ)..L, Real.sqrt (φ ε s) := by
  set A := ∫ s in (0 : ℝ)..L, φ₂ 0 s with hA
  set K := Icc 0 ε₀ ×ˢ Icc 0 L with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn h3
  set M := max M₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hbound (q : ℝ × ℝ) (hq : q ∈ K) : |φ₂ q.1 q.2| ≤ M :=
    (by simpa [Real.norm_eq_abs] using hM₀ q hq : |φ₂ q.1 q.2| ≤ M₀).trans (le_max_left _ _)
  set η := A / (2 * L) with hη
  have hηpos : 0 < η := div_pos h6 (by linarith)
  obtain ⟨δ, hδ, hδK⟩ := Metric.uniformContinuousOn_iff.mp
    (hKc.uniformContinuousOn_of_continuous h3) η hηpos
  set B := L * M ^ 2 + M + 1 with hB
  have hBpos : 0 < B := by positivity
  set ε := min ε₀ (min (δ / 2) (min 1 (min (A / (2 * B)) (1 / B)))) with hεdef
  have hεpos : 0 < ε := by
    refine lt_min hε₀ (lt_min (by linarith) (lt_min one_pos (lt_min ?_ ?_)))
    · exact div_pos h6 (by linarith)
    · exact div_pos one_pos hBpos
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεδ : ε < δ := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεA : ε ≤ A / (2 * B) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hεB : ε ≤ 1 / B := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  -- the pointwise bounds
  have hsub (s : ℝ) (hs : s ∈ Icc 0 L) (t : ℝ) (ht : t ∈ Icc 0 ε) :
      (t, s) ∈ K := ⟨⟨ht.1, ht.2.trans hεε₀⟩, hs⟩
  have hlow (s : ℝ) (hs : s ∈ Icc 0 L) :
      1 + (φ₂ 0 s - η) * ε ^ 2 / 2 ≤ φ ε s := by
    have h := add_le_of_le_deriv (f := fun e => φ e s) (f₁ := fun e => φ₁ e s)
      (f₂ := fun e => φ₂ e s) (m := φ₂ 0 s - η) hεpos.le
      (fun t ht => h1 s hs t ⟨ht.1, ht.2.trans hεε₀⟩)
      (fun t ht => h2 s hs t ⟨ht.1, ht.2.trans hεε₀⟩) (fun t ht => by
        have hd := hδK (0, s) (hsub s hs 0 ⟨le_rfl, hεpos.le⟩) (t, s) (hsub s hs t ht) (by
          rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq, zero_sub, abs_neg,
            abs_of_nonneg ht.1]
          exact ht.2.trans_lt hεδ)
        rw [Real.dist_eq] at hd
        have := abs_sub_lt_iff.mp hd
        linarith)
    simp only [(h5 s hs).1, (h5 s hs).2, mul_zero, add_zero] at h
    linarith
  have hlowM (s : ℝ) (hs : s ∈ Icc 0 L) : 1 - M * ε ^ 2 / 2 ≤ φ ε s := by
    have h := add_le_of_le_deriv (f := fun e => φ e s) (f₁ := fun e => φ₁ e s)
      (f₂ := fun e => φ₂ e s) (m := -M) hεpos.le
      (fun t ht => h1 s hs t ⟨ht.1, ht.2.trans hεε₀⟩)
      (fun t ht => h2 s hs t ⟨ht.1, ht.2.trans hεε₀⟩)
      (fun t ht => neg_le_of_abs_le (hbound (t, s) (hsub s hs t ht)))
    simp only [(h5 s hs).1, (h5 s hs).2, mul_zero, add_zero] at h
    linarith
  have hupM (s : ℝ) (hs : s ∈ Icc 0 L) : φ ε s ≤ 1 + M * ε ^ 2 / 2 := by
    have h := le_add_of_deriv_le (f := fun e => φ e s) (f₁ := fun e => φ₁ e s)
      (f₂ := fun e => φ₂ e s) (M := M) hεpos.le
      (fun t ht => h1 s hs t ⟨ht.1, ht.2.trans hεε₀⟩)
      (fun t ht => h2 s hs t ⟨ht.1, ht.2.trans hεε₀⟩)
      (fun t ht => le_of_abs_le (hbound (t, s) (hsub s hs t ht)))
    simp only [(h5 s hs).1, (h5 s hs).2, mul_zero, add_zero] at h
    linarith
  have hMε : M * ε ^ 2 < 1 := by
    have h : M * ε ^ 2 ≤ M * (1 / B) := mul_le_mul_of_nonneg_left (hε2.trans hεB) hM0
    have h' : M * (1 / B) < 1 := by
      rw [mul_one_div, div_lt_one hBpos]
      linarith [mul_nonneg hL.le (sq_nonneg M)]
    linarith
  have hpos (s : ℝ) (hs : s ∈ Icc 0 L) : 0 < φ ε s := by
    linarith [hlowM s hs]
  -- the square root
  have hsq (s : ℝ) (hs : s ∈ Icc 0 L) :
      1 + (φ₂ 0 s - η) * ε ^ 2 / 4 - M ^ 2 * ε ^ 4 / 8 ≤ Real.sqrt (φ ε s) := by
    have hr := sqrt_ge (φ ε s)
    set x := φ ε s - 1 with hx
    have hx1 : (φ₂ 0 s - η) * ε ^ 2 / 2 ≤ x := by linarith [hlow s hs]
    have hx2 : |x| ≤ M * ε ^ 2 / 2 := abs_le.mpr ⟨by linarith [hlowM s hs], by linarith [hupM s hs]⟩
    have hxsq : x ^ 2 ≤ (M * ε ^ 2 / 2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg x) hx2 2
    have hrw : (3 * φ ε s - φ ε s ^ 2) / 2 = 1 + x / 2 - x ^ 2 / 2 := by
      rw [hx]
      ring
    rw [hrw] at hr
    nlinarith
  -- integration
  have hcont₂ : ContinuousOn (fun s => φ₂ 0 s) (Icc 0 L) :=
    h3.comp (continuousOn_const.prodMk continuousOn_id) fun s hs => ⟨⟨le_rfl, hε₀.le⟩, hs⟩
  have hint₂ : IntervalIntegrable (fun s => φ₂ 0 s) volume 0 L :=
    (hcont₂.mono (by rw [uIcc_of_le hL.le])).intervalIntegrable
  have hintsq : IntervalIntegrable (fun s => Real.sqrt (φ ε s)) volume 0 L :=
    (((h4 ε ⟨hεpos.le, hεε₀⟩).sqrt).mono (by rw [uIcc_of_le hL.le])).intervalIntegrable
  have hintlow : IntervalIntegrable
      (fun s => 1 + (φ₂ 0 s - η) * ε ^ 2 / 4 - M ^ 2 * ε ^ 4 / 8) volume 0 L := by
    have hc : ContinuousOn (fun s => 1 + (φ₂ 0 s - η) * ε ^ 2 / 4 - M ^ 2 * ε ^ 4 / 8)
        (Icc 0 L) :=
      ((continuousOn_const.add ((hcont₂.sub continuousOn_const).mul continuousOn_const |>.div_const
        4)).sub continuousOn_const)
    exact (hc.mono (by rw [uIcc_of_le hL.le])).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hL.le hintlow hintsq hsq
  have hcalc : (∫ s in (0 : ℝ)..L, (1 + (φ₂ 0 s - η) * ε ^ 2 / 4 - M ^ 2 * ε ^ 4 / 8)) =
      L + (A - η * L) * ε ^ 2 / 4 - L * (M ^ 2 * ε ^ 4 / 8) := by
    have he : (fun s => 1 + (φ₂ 0 s - η) * ε ^ 2 / 4 - M ^ 2 * ε ^ 4 / 8) =
        fun s => (ε ^ 2 / 4) * φ₂ 0 s + (1 - η * ε ^ 2 / 4 - M ^ 2 * ε ^ 4 / 8) := by
      funext s
      ring
    rw [he, intervalIntegral.integral_add (hint₂.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, ← hA]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [hcalc] at hmono
  refine ⟨ε, ⟨hεpos, hεε₀⟩, hpos, lt_of_lt_of_le ?_ hmono⟩
  have hηL : A - η * L = A / 2 := by
    rw [hη]
    field_simp
    ring
  rw [hηL]
  have hLM : L * M ^ 2 * ε ^ 2 ≤ A / 2 := by
    have h : L * M ^ 2 * ε ^ 2 ≤ L * M ^ 2 * (A / (2 * B)) :=
      mul_le_mul_of_nonneg_left (hε2.trans hεA) (by positivity)
    have h' : L * M ^ 2 * (A / (2 * B)) ≤ A / 2 := by
      rw [show L * M ^ 2 * (A / (2 * B)) = (L * M ^ 2 / B) * (A / 2) by field_simp]
      have hfr : L * M ^ 2 / B ≤ 1 := by
        rw [div_le_one hBpos]
        linarith
      nlinarith
    linarith
  have hε4 : 0 < ε ^ 2 := by positivity
  nlinarith

end ProjectAinos.SmoothGeometry.SecondDerivativeTest
