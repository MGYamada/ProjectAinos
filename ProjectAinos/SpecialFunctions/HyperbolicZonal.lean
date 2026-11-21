/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! # Smooth continuation of the zonal hyperbolic harmonic through the pole

The squared geodesic radius is a smooth coordinate near s=1, since the even Taylor
series of cosh has linear coefficient 1/2 in r². The corresponding odd sine and
hyperbolic sine series, divided by r, are regular and nonzero in the denominator at zero.
-/

@[expose] public section
noncomputable section
open Filter Set FormalMultilinearSeries
open scoped ContDiff Topology Nat
namespace ProjectAinos.SpecialFunctions.Hyperbolic

private abbrev coeff (j n : ℕ) : ℝ := (((2*n+j) ! : ℕ) : ℝ)⁻¹
private abbrev series (j : ℕ) := ofScalars ℝ (coeff j)
private abbrev S (j : ℕ) : ℝ → ℝ := ofScalarsSum (coeff j)

private theorem at_zero (j : ℕ) : HasFPowerSeriesAt (S j) (series j) 0 := by
  apply ((series j).hasFPowerSeriesOnBall ?_).hasFPowerSeriesAt
  have h := (series j).le_radius_of_bound 1 (r := 1) (fun n => by
    rw [ofScalars_norm]; simp only [NNReal.coe_one,one_pow,mul_one,coeff,Real.norm_eq_abs,
      abs_inv,abs_of_nonneg (Nat.cast_nonneg ((2*n+j)!) : (0 : ℝ) ≤ _)]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (2*n+j)))
  exact lt_of_lt_of_le (by norm_num) h

private theorem zeroS (j : ℕ) : S j 0= ((j ! : ℕ) : ℝ)⁻¹ := by simp [S,coeff]
private theorem Csq (r : ℝ) : S 0 (r^2)=Real.cosh r := by
  rw [S,ofScalars_sum_eq,Real.cosh_eq_tsum]
  apply tsum_congr
  intro n; simp [coeff,smul_eq_mul,← pow_mul,div_eq_inv_mul]
private theorem Shsq (r : ℝ) : r*S 1 (r^2)=Real.sinh r := by
  rw [S,ofScalars_sum_eq,Real.sinh_eq_tsum,← tsum_mul_left]
  apply tsum_congr
  intro n; simp [coeff,smul_eq_mul,pow_succ,div_eq_inv_mul]; ring
private theorem Ssq (r : ℝ) : r*S 1 (-r^2)=Real.sin r := by
  rw [S,ofScalars_sum_eq,Real.sin_eq_tsum,← tsum_mul_left]
  apply tsum_congr
  intro n; simp [coeff,smul_eq_mul,pow_succ,div_eq_inv_mul]; ring

private theorem inverse_exists :
    ∃ R : ℝ → ℝ, ContDiffAt ℝ ∞ R 1 ∧ R 1=0 ∧ ∀ᶠ t in 𝓝 0, R (S 0 t)=t := by
  have d : HasDerivAt (S 0) (1/2) 0 := by
    apply (at_zero 0).hasDerivAt.congr_deriv
    norm_num [series,ofScalars_apply_eq,coeff]
  have h := (at_zero 0).analyticAt.contDiffAt (n := ∞)
  have he := d.hasFDerivAt_equiv (by norm_num)
  let e := h.toOpenPartialHomeomorph (S 0) he (by simp)
  have h₀ : S 0 0=1 := by simp
  refine ⟨e.symm,?_,?_,?_⟩
  · rw [← h₀]; exact h.to_localInverse he (by simp)
  · rw [← h₀]; exact h.localInverse_apply_image he (by simp)
  · filter_upwards [e.open_source.mem_nhds (h.mem_toOpenPartialHomeomorph_source he (by simp))]
      with t ht using e.left_inv ht

private def inv := inverse_exists.choose

private def germ (k s : ℝ) := S 1 (-k^2*inv s)/S 1 (inv s)

/-- The real zonal profile normalized to one at the pole, smoothly continued across s=1. -/
private def continued (k s : ℝ) : ℝ :=
  if 1 < s then (if k=0 then Real.arcosh s else Real.sin (k*Real.arcosh s)/k)/
    Real.sinh (Real.arcosh s)
  else germ k s

private theorem continued_one (k : ℝ) : continued k 1=1 := by
  have hi : inv 1=0 := inverse_exists.choose_spec.2.1
  simp [continued,germ,hi]

/-- Away from the pole the profile is sin(kr)/(k sinh r), including the threshold seed r. -/
private theorem continued_cosh (k : ℝ) {r : ℝ} (hr : 0 < r) :
    continued k (Real.cosh r) =
      (if k=0 then r else Real.sin (k*r)/k)/Real.sinh r := by
  simp [continued,Real.one_lt_cosh.mpr hr.ne',Real.arcosh_cosh hr.le]

/-- The spatial profile is smooth in the ambient coordinate throughout the physical half-line. -/
private theorem smooth_continued (k : ℝ) {s : ℝ} (hs : 1 ≤ s) :
    ContDiffAt ℝ ∞ (continued k) s := by
  rcases hs.eq_or_lt with rfl | hs
  · obtain ⟨hR,h₀,hI⟩ := inverse_exists.choose_spec
    change ContDiffAt ℝ ∞ inv 1 at hR
    change inv 1=0 at h₀
    change ∀ᶠ t in 𝓝 0, inv (S 0 t)=t at hI
    have hS := (at_zero 1).analyticAt.contDiffAt (n := ∞)
    have hG : ContDiffAt ℝ ∞ (germ k) 1 := by
      apply (ContDiffAt.comp 1 (g := S 1) _ (contDiffAt_const.mul hR)).div
        (ContDiffAt.comp 1 (g := S 1) _ hR) _
      · simpa [h₀] using hS
      · simpa [h₀] using hS
      · simp [h₀]
    have hr : ContinuousAt Real.arcosh 1 := by
      unfold Real.arcosh
      fun_prop (disch := norm_num)
    have hc : Tendsto (fun t => Real.arcosh t^2) (𝓝 1) (𝓝 0) := by
      simpa [Pi.pow_def] using (hr.pow 2).tendsto
    apply hG.congr_of_eventuallyEq
    filter_upwards [hc.eventually hI] with t ht
    by_cases h : 1<t
    · let r := Real.arcosh t
      have hpos : 0 < r := Real.arcosh_pos h
      have he : Real.cosh r=t := Real.cosh_arcosh h.le
      change inv (S 0 (r^2))=r^2 at ht
      rw [Csq,he] at ht
      rw [← he,continued_cosh k hpos,he]
      unfold germ
      rw [ht]
      have hh := Shsq r
      have hn := (Real.sinh_pos_iff.mpr hpos).ne'
      have hS₁ : S 1 (r^2) ≠ 0 := by intro e; rw [e,mul_zero] at hh; exact hn hh.symm
      by_cases hk : k=0
      · subst k
        norm_num [zeroS]
        field_simp [hn,hS₁]; linear_combination hh
      · simp only [hk,ite_false]
        have hsin := Ssq (k*r)
        rw [show -(k*r)^2 = -k^2*r^2 by ring] at hsin
        field_simp [hk,hn,hS₁]
        simp only [neg_mul] at hsin
        linear_combination -S 1 (r^2)*hsin + k*S 1 (-(k^2*r^2))*hh
    · simp [continued,h]
  · have eq : continued k =ᶠ[𝓝 s] fun t => (if k=0 then Real.arcosh t
        else Real.sin (k*Real.arcosh t)/k)/Real.sinh (Real.arcosh t) := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      exact ite_eq_left (show 1<t from ht)
    apply ContDiffAt.congr_of_eventuallyEq _ eq
    have hd := Real.contDiffAt_arcosh (n := ∞) hs
    split <;> fun_prop (disch := exact (Real.sinh_pos_iff.mpr (Real.arcosh_pos hs)).ne')

/-- Smooth real extension in the ambient coordinate of the regular geodesic zonal solution. -/
theorem exists_zonalProfile (k : ℝ) : ∃ f : ℝ → ℝ,
    (∀ s ≥ 1, ContDiffAt ℝ ∞ f s) ∧ f 1=1 ∧ ∀ r : ℝ, 0 < r →
      f (Real.cosh r)=(if k=0 then r else Real.sin (k*r)/k)/Real.sinh r :=
  ⟨continued k,fun _ hs => smooth_continued k hs,continued_one k,fun _ hr => continued_cosh k hr⟩

/-- The normalized zonal harmonic, continued smoothly across s=1 in the ambient coordinate. -/
def zonalProfile (k : ℝ) := (exists_zonalProfile k).choose

theorem smooth_zonalProfile (k : ℝ) {s : ℝ} (hs : 1 ≤ s) : ContDiffAt ℝ ∞ (zonalProfile k) s :=
  (exists_zonalProfile k).choose_spec.1 s hs

@[simp] theorem zonalProfile_one (k : ℝ) : zonalProfile k 1=1 :=
  (exists_zonalProfile k).choose_spec.2.1

theorem zonalProfile_cosh (k : ℝ) {r : ℝ} (hr : 0 < r) : zonalProfile k (Real.cosh r)=
    (if k=0 then r else Real.sin (k*r)/k)/Real.sinh r :=
  (exists_zonalProfile k).choose_spec.2.2 r hr

end ProjectAinos.SpecialFunctions.Hyperbolic
