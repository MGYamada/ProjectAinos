/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Schlaefli
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-! # Small and large argument estimates for the real Schläfli ray -/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Real
open scoped Topology

namespace ProjectAinos.SpecialFunctions.Bessel.Schlaefli

/-- The ray integral of real order on the real axis. -/
def realRay (a x : ℝ) := ∫ t : ℝ in Ioi 0, Real.exp (-x*Real.sinh t+a*t)

theorem ofReal_realRay (a x : ℝ) : (realRay a x : ℂ) = ray a x := by
  unfold realRay ray
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  push_cast
  rfl

private def density (p u y : ℝ) := y^(p-1)*Real.exp (-y+u^2/y)

private theorem rescale (p : ℝ) {u : ℝ} (hu : 0 < u) :
    u^p*realRay p (2*u) = ∫ y in Ioi u, density p u y := by
  have h := integral_comp_mul_left_Ioi' (density p u) 1 hu
  simp only [mul_one,smul_eq_mul] at h
  have e := integral_comp_exp_Ioi (fun y => u*density p u (u*y)) 0
  simp only [Real.exp_zero,smul_eq_mul] at e
  rw [← h,← integral_const_mul,← e,realRay,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have ht := Real.exp_pos t
  have hpow := Real.mul_rpow (z := p) hu.le ht.le
  dsimp only
  rw [density,Real.rpow_sub_one (mul_pos hu ht).ne',hpow,← Real.exp_mul,
    Real.sinh_eq,Real.exp_neg,show -(2*u)*((Real.exp t-(Real.exp t)⁻¹)/2)+p*t =
      p*t+(-(u*Real.exp t)+u^2/(u*Real.exp t)) by field_simp; ring,Real.exp_add]
  rw [mul_comm p t]
  field_simp

/-- The change of variables y=u exp(t) reveals the exact Gamma coefficient of the ray. -/
theorem tendsto_scaled_ray {p : ℝ} (hp : 0 < p) :
    Tendsto (fun u : ℝ => u^p*realRay p (2*u)) (𝓝[>] 0) (𝓝 (Real.Gamma p)) := by
  let G (u y : ℝ) := (Ioi u).indicator (density p u) y
  have hG : (fun u : ℝ => u^p*realRay p (2*u)) =ᶠ[𝓝[>] 0] fun u => ∫ y in Ioi 0, G u y := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [rescale p hu,show (∫ y in Ioi 0, G u y) = ∫ y in Ioi 0 ∩ Ioi u, density p u y from
      setIntegral_indicator measurableSet_Ioi,Ioi_inter_Ioi,max_eq_right (le_of_lt hu)]
  have hInt := Real.GammaIntegral_convergent hp
  rw [Real.Gamma_eq_integral hp]
  apply Filter.Tendsto.congr' hG.symm
  apply tendsto_integral_filter_of_dominated_convergence
    (fun y : ℝ => Real.exp 1*(Real.exp (-y)*y^(p-1)))
  · refine Eventually.of_forall fun u => ?_
    exact ((show Measurable (density p u) by unfold density; fun_prop).indicator
      measurableSet_Ioi).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ)<1 by norm_num)))] with u hu hu'
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy₀ : 0 < y := hy
    have hu₀ : 0 < u := hu
    have hu₁ : u < 1 := hu'
    by_cases huy : u < y
    · rw [show G u y = density p u y from indicator_of_mem huy _,density,
        Real.norm_eq_abs,abs_of_nonneg (by positivity),
        show Real.exp 1*(Real.exp (-y)*y^(p-1)) = y^(p-1)*Real.exp (-y+1) by
          rw [Real.exp_add]; ring]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy₀.le _)
      apply Real.exp_le_exp.mpr
      have h := (div_le_iff₀ hy₀).mpr (show u^2 ≤ 1*y by nlinarith [mul_pos hu₀ (sub_pos.mpr hu₁)])
      linarith
    · rw [show G u y = 0 from indicator_of_notMem huy _,norm_zero]; positivity
  · exact hInt.const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy₀ : 0 < y := hy
    have hc : ContinuousAt (fun u : ℝ => density p u y) 0 := by unfold density; fun_prop
    have lim := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    have lim' : Tendsto (fun u => density p u y) (𝓝[>] 0) (𝓝 (Real.exp (-y)*y^(p-1))) := by
      simpa [density,mul_comm] using lim
    apply lim'.congr'
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hy₀)] with u hu
    exact (indicator_of_mem (show y ∈ Ioi u from hu) _).symm

/-- A negative-order ray has a finite limit at the origin. -/
theorem tendsto_realRay_zero {a : ℝ} (ha : a < 0) :
    Tendsto (fun x : ℝ => realRay a x) (𝓝[>] 0) (𝓝 (-1/a)) := by
  have e := integral_exp_mul_Ioi ha 0
  simp only [mul_zero,Real.exp_zero] at e
  rw [← e]
  unfold realRay
  apply tendsto_integral_filter_of_dominated_convergence (fun t => Real.exp (a*t))
  · exact Eventually.of_forall fun _ => by fun_prop
  · filter_upwards [self_mem_nhdsWithin] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_le_exp]
    linarith [mul_nonneg (show 0 ≤ x from le_of_lt hx) (Real.sinh_nonneg_iff.mpr (le_of_lt ht))]
  · exact integrableOn_exp_mul_Ioi ha 0
  · filter_upwards with t
    have hc : ContinuousAt (fun x : ℝ => Real.exp (-x*Real.sinh t+a*t)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))

/-- An exponential majorant controls the ray for orders below its argument. -/
theorem realRay_bounds (a : ℝ) {x : ℝ} (hx : 0 < x) (ha : a < x) :
    0 ≤ realRay a x ∧ realRay a x ≤ 1/(x-a) := by
  constructor
  · exact integral_nonneg fun _ => (Real.exp_pos _).le
  · have h := integral_exp_mul_Ioi (sub_neg.mpr ha) 0
    simp only [mul_zero,Real.exp_zero] at h
    have hi := (integrable_ray (a : ℂ) (x : ℂ) hx).norm
    have hreal : IntegrableOn (fun t : ℝ => Real.exp (-x*Real.sinh t+a*t)) (Ioi 0) volume := by
      unfold IntegrableOn
      simpa only [Complex.norm_exp,Complex.add_re,Complex.re_mul_ofReal,
        Complex.neg_re,Complex.ofReal_re] using hi
    unfold realRay
    calc
      _ ≤ ∫ t : ℝ in Ioi 0, Real.exp ((a-x)*t) := by
        apply setIntegral_mono_on hreal (integrableOn_exp_mul_Ioi (sub_neg.mpr ha) 0)
          measurableSet_Ioi
        intro t ht
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr (le_of_lt ht)) hx.le]
      _ = _ := by rw [h,← neg_sub x a,div_neg,neg_div,neg_neg]

end ProjectAinos.SpecialFunctions.Bessel.Schlaefli
