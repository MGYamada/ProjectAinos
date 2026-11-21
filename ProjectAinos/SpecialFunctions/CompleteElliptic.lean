/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.JacobiElliptic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic

/-! # Complete elliptic integrals of modulus k

The first kind is the quarter period of Jacobi's amplitude. On the real open interval
|k| < 1, the first and second kind satisfy the coupled modulus derivative identities.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set
open scoped Real Topology
namespace ProjectAinos.SpecialFunctions.Elliptic
open JacobiElliptic SmoothGeometry.NonlinearODE

/-- Complete elliptic integral of the first kind in the modulus convention. -/
def K (k : ℝ) := ∫ t in 0..π/2, (amplitudeField k t)⁻¹

/-- Complete elliptic integral of the second kind in the modulus convention. -/
def E (k : ℝ) := ∫ t in 0..π/2, amplitudeField k t

/-- At zero modulus both complete integrals have value π/2. -/
theorem zero : K 0 = π/2 ∧ E 0 = π/2 := by simp [K,E,amplitudeField]

/-- The endpoint of the first quarter period has amplitude π/2. -/
theorem am_K {k : ℝ} (hk : k^2 < 1) : am k (K k) = π/2 :=
  flow_scalarTime (contDiff_amplitudeField hk) (amplitudeField_pos hk) (abs_amplitudeField_le k) _

/-- The existing Jacobi half-period is twice the first integral. -/
theorem halfPeriod_eq {k : ℝ} (hk : k^2 < 1) : halfPeriod k = 2*K k := by
  let f (t : ℝ) := (amplitudeField k t)⁻¹
  have hf : Continuous f := (contDiff_amplitudeField hk).continuous.inv₀
    (fun t => (amplitudeField_pos hk t).ne')
  have sym (t : ℝ) : f (π-t) = f t := by simp [f,amplitudeField,Real.sin_pi_sub]
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π/2) f π
  simp_rw [sym] at h
  rw [sub_zero,show π-π/2=π/2 by ring] at h
  change (∫ t in 0..π, f t) = 2*∫ t in 0..π/2, f t
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 (π/2))
    (hf.intervalIntegrable (π/2) π),← h,two_mul]

private def val (p : Bool) (k t : ℝ) := if p then (amplitudeField k t)⁻¹ else amplitudeField k t
private def slope (p : Bool) (k t : ℝ) := if p then k*Real.sin t^2/(amplitudeField k t)^3
  else -k*Real.sin t^2/amplitudeField k t

private theorem dval {k : ℝ} (hk : k^2 < 1) (p : Bool) (t : ℝ) :
    HasDerivAt (fun l => val p l t) (slope p k t) k := by
  have h := ((((hasDerivAt_id' k).pow 2).mul_const (Real.sin t^2)).const_sub 1).sqrt
    (one_sub_pos hk t).ne'
  have h' : HasDerivAt (fun l => amplitudeField l t) (-k*Real.sin t^2/amplitudeField k t) k := by
    apply h.congr_deriv
    simp only [amplitudeField,Pi.pow_apply,mul_one]
    ring
  cases p
  · exact h'
  · apply (h'.inv (amplitudeField_pos hk t).ne').congr_deriv
    change _ = k*Real.sin t^2/amplitudeField k t^3
    ring

private theorem meas (p : Bool) (k : ℝ) : Measurable (val p k) := by
  cases p <;> unfold val amplitudeField <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

private theorem deriv_int (p : Bool) {k : ℝ} (hk : k^2 < 1) :
    HasDerivAt (fun l : ℝ => ∫ t in 0..π/2, val p l t) (∫ t in 0..π/2, slope p k t) k := by
  let b := (1+|k|)/2
  have hb : |k| < b := by dsimp [b]; linarith [(sq_lt_one_iff_abs_lt_one k).mp hk]
  have hsub {l : ℝ} (hl : l ∈ Icc (-b) b) : l^2 < 1 := by
    apply (sq_lt_one_iff_abs_lt_one _).mpr
    exact (abs_le.mpr hl).trans_lt (by dsimp [b]; linarith [(sq_lt_one_iff_abs_lt_one k).mp hk])
  let S := Icc (-b) b ×ˢ uIcc 0 (π/2)
  have hc : ContinuousOn (fun x : ℝ × ℝ => slope p x.1 x.2) S := by
    have hF : Continuous (fun x : ℝ × ℝ => amplitudeField x.1 x.2) := by
      unfold amplitudeField
      fun_prop
    have hP (x : ℝ × ℝ) (hx : x ∈ S) := (amplitudeField_pos (hsub hx.1) x.2).ne'
    cases p
    · exact ((continuous_fst.neg.mul
        ((Real.continuous_sin.comp continuous_snd).pow 2)).continuousOn).div
        hF.continuousOn hP
    · exact ((continuous_fst.mul
        ((Real.continuous_sin.comp continuous_snd).pow 2)).continuousOn).div
        (hF.pow 3).continuousOn (fun x hx => pow_ne_zero _ (hP x hx))
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn hc
  have hval : Continuous (val p k) := by
    cases p
    · exact (contDiff_amplitudeField hk).continuous
    · exact (contDiff_amplitudeField hk).continuous.inv₀ (fun t => (amplitudeField_pos hk t).ne')
  have hm : Measurable (slope p k) := by
    cases p <;> unfold slope amplitudeField <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := val p) (F' := slope p) (bound := fun _ => C)
    (Icc_mem_nhds (abs_lt.mp hb).1 (abs_lt.mp hb).2)
    (Eventually.of_forall fun l => (meas p l).aestronglyMeasurable) (hval.intervalIntegrable ..)
    hm.aestronglyMeasurable (Eventually.of_forall fun t ht l hl =>
      hC (l,t) ⟨hl,uIoc_subset_uIcc ht⟩) intervalIntegrable_const
    (Eventually.of_forall fun t _ l hl => dval (hsub hl) p t)).2

/-- Modulus derivative of E, including k=0 in the multiplied identity. -/
theorem deriv_E {k : ℝ} (hk : k^2 < 1) : k*deriv E k = E k-K k := by
  have h : deriv E k = ∫ t in 0..π/2, slope false k t := (deriv_int false hk).deriv
  have hc := (contDiff_amplitudeField hk).continuous
  have hi : Continuous (fun t => (amplitudeField k t)⁻¹) :=
    hc.inv₀ (fun t => (amplitudeField_pos hk t).ne')
  rw [h, E, K, ← intervalIntegral.integral_sub (hc.intervalIntegrable ..)
    (hi.intervalIntegrable ..),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  change k*(-k*Real.sin t^2/amplitudeField k t) = amplitudeField k t-(amplitudeField k t)⁻¹
  field_simp [(amplitudeField_pos hk t).ne']
  linarith [amplitudeField_sq hk t]

/-- Modulus derivative of K in terms of both complete elliptic integrals. -/
theorem deriv_K {k : ℝ} (hk : k^2 < 1) : k*(1-k^2)*deriv K k = E k-(1-k^2)*K k := by
  have h : deriv K k = ∫ t in 0..π/2, slope true k t := (deriv_int true hk).deriv
  let f := amplitudeField k
  let g (t : ℝ) := Real.sin t*Real.cos t/f t
  let g' (t : ℝ) := (Real.cos t^2-Real.sin t^2)/f t +
    k^2*Real.sin t^2*Real.cos t^2/f t^3
  have hn (t : ℝ) : f t ≠ 0 := (amplitudeField_pos hk t).ne'
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    apply (((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).div
      (hasDerivAt_amplitudeField hk t) (hn t)).congr_deriv
    change ( _ * f t - _ * _) / f t^2 = _
    dsimp only [g']
    change _ = _/amplitudeField k t+_/amplitudeField k t^3
    dsimp only [f,Pi.mul_apply]
    field_simp [(amplitudeField_pos hk t).ne']
    ring
  have hc := (contDiff_amplitudeField hk).continuous
  have hcf : Continuous f := hc
  have hg' : Continuous g' := by
    dsimp [g']
    fun_prop (disch := intros; first | apply hn | exact pow_ne_zero _ (hn _))
  have hzero := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π/2)
    (fun t _ => hg t) (hg'.intervalIntegrable ..)
  simp [g, Real.cos_pi_div_two] at hzero
  have he (t : ℝ) : f t-(1-k^2)*(f t)⁻¹ =
      k*(1-k^2)*slope true k t+k^2*g' t := by
    have hf := amplitudeField_sq hk t
    change f t^2 = _ at hf
    dsimp only [g',slope,↓reduceIte]
    change _ = k*(1-k^2)*(k*Real.sin t^2/f t^3)+_
    field_simp [hn]
    rw [show Real.cos t^2 = 1-Real.sin t^2 by linarith [Real.sin_sq_add_cos_sq t]]
    linear_combination (f t^2+k^2*Real.sin t^2)*hf
  have hs : Continuous (slope true k) :=
    (continuous_const.mul (Real.continuous_sin.pow 2)).div (hc.pow 3)
      (fun t => pow_ne_zero 3 (hn t))
  have hi : Continuous (fun t => (amplitudeField k t)⁻¹) := hcf.inv₀ hn
  rw [h,E,K,← intervalIntegral.integral_const_mul (1-k^2),
    ← intervalIntegral.integral_sub (hc.intervalIntegrable ..)
      ((hi.intervalIntegrable ..).const_mul _)]
  change _ = ∫ t in 0..π/2, f t-(1-k^2)*(f t)⁻¹
  simp_rw [he]
  rw [intervalIntegral.integral_add ((hs.intervalIntegrable ..).const_mul _)
    ((hg'.intervalIntegrable ..).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,hzero,mul_zero,add_zero]

end ProjectAinos.SpecialFunctions.Elliptic
