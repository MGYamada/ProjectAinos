/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.BesselTurningPoint
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # The Bessel primitive at its turning point

The integral from zero to an argument n−ur has a moving endpoint. The subcritical
exponential bound controls the part outside every fixed Airy window.
-/

@[expose] public section
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Real Topology
namespace ProjectAinos.SpecialFunctions.Bessel
open Airy

private def truncatedLine (n : ℕ) (u : ℝ) :=
  let r := turningScale n
  (Iic (2*r^2-u)).indicator (fun v : ℝ => (r : ℂ)*besselJ n (n-(u+v)*r : ℝ))

private theorem continuous_line (n : ℕ) : Continuous (besselJ (n : ℂ)) :=
  continuous_iff_continuousAt.mpr fun x => (analyticAt_besselJ_int (n : ℤ) x).continuousAt

private theorem measurable_line (n : ℕ) (u : ℝ) : StronglyMeasurable (truncatedLine n u) := by
  apply StronglyMeasurable.indicator _ measurableSet_Iic
  exact (continuous_const.mul ((continuous_line n).comp
    (continuous_ofReal.comp (continuous_const.sub
      ((continuous_const.add continuous_id).mul continuous_const))))).stronglyMeasurable

private theorem line_integral (n : ℕ) {u : ℝ}
    (hu : u ≤ 2*turningScale n^2) :
    (∫ v : ℝ in Ioi 0, truncatedLine n u v) = ∫ x in 0..(n-u*turningScale n),
      besselJ n (x : ℝ) := by
  let r := turningScale n
  let L := 2*r^2-u
  have hL : 0 ≤ L := sub_nonneg.mpr hu
  have h := intervalIntegral.smul_integral_comp_sub_mul (a := 0) (b := L)
    (fun x : ℝ => besselJ n x) r ((n : ℝ)-u*r)
  have hx (v : ℝ) : (n : ℝ)-(u+v)*r = n-u*r-r*v := by ring
  have h₀ : (n : ℝ)-u*r-r*L = 0 := by
    change (n : ℝ)-u*r-r*(2*r^2-u) = 0
    linear_combination turningScale_cube n
  rw [h₀, mul_zero, sub_zero, real_smul] at h
  unfold truncatedLine
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    inter_comm, Ioi_inter_Iic, ← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_const_mul]
  change (r : ℂ)*(∫ v in 0..L, besselJ n ((n-(u+v)*r : ℝ) : ℂ)) = _
  simp_rw [hx]
  exact h

/-- Uniform Airy approximation to the integral of J from zero to n−ur, for positive
bounded detuning, along any sequence of orders tending to infinity. -/
theorem turning_primitive {d : ℕ → ℕ} (hd : Tendsto d atTop atTop) {u : ℕ → ℝ} {B : ℝ}
    (hu : ∀ᶠ n in atTop, 0 ≤ u n ∧ u n ≤ B) :
    Tendsto (fun n =>
      (∫ x in (0 : ℝ)..(d n-u n*turningScale (d n)), besselJ (d n) x) -
      ∫ v : ℝ in Ioi 0, ai (u n+v : ℝ)) atTop (𝓝 0) := by
  let r n := turningScale (d n)
  have hr : Tendsto r atTop atTop := tendsto_turningScale.comp hd
  have hr₂ : Tendsto (fun n => r n^2) atTop atTop := (tendsto_pow_atTop two_ne_zero).comp hr
  obtain ⟨C,hC,hJ⟩ := turning_bound
  obtain ⟨A,hA,hAi⟩ := airy_bound
  let g (v : ℝ) := Real.exp (-(1/2)*v)
  have hg : IntegrableOn g (Ioi 0) := integrableOn_exp_mul_Ioi (by norm_num) 0
  have hmodel (v u : ℝ) (hv : 0 ≤ v) (hu : 0 ≤ u) : ‖ai (u+v : ℝ)‖ ≤ A*g v := by
    exact (hAi _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hA)
  have hline (n : ℕ) (hr : 1 ≤ r n) {v : ℝ} (hv : 0 ≤ v) (hu : 0 ≤ u n) :
      ‖truncatedLine (d n) (u n) v‖ ≤ C*g v := by
    by_cases h : v ≤ 2*r n^2-u n
    · rw [truncatedLine, indicator_of_mem (show v ∈ Iic _ from h)]
      exact (hJ _ hr _ (add_nonneg hu hv) (by linarith)).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC)
    · rw [truncatedLine, indicator_of_notMem (show v ∉ Iic _ from h), norm_zero]
      exact mul_nonneg hC (Real.exp_pos _).le
  have hc (n : ℕ) : Continuous (fun v : ℝ => ai (u n+v : ℝ)) :=
    (show Differentiable ℂ ai from fun x => (hasDerivAt_ai x).differentiableAt).continuous.comp
      (continuous_ofReal.comp (continuous_const.add continuous_id))
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hv : ∀ᵐ v ∂μ, 0 < v := ae_restrict_mem measurableSet_Ioi
  have H : Tendsto (fun n => ∫ v : ℝ, (truncatedLine (d n) (u n) v-ai (u n+v : ℝ)) ∂μ)
      atTop (𝓝 0) := by
    rw [← integral_zero (μ := μ) (G := ℂ)]
    refine tendsto_integral_filter_of_dominated_convergence (fun v => (C+A)*g v)
      (Eventually.of_forall fun n => (measurable_line _ _).aestronglyMeasurable.sub
        (hc n).aestronglyMeasurable) ?_ (hg.const_mul _) ?_
    · filter_upwards [hu,hr.eventually_ge_atTop 1] with n hn h
      filter_upwards [hv] with v hv'
      exact (norm_sub_le _ _).trans ((add_le_add (hline n h hv'.le hn.1)
        (hmodel v (u n) hv'.le hn.1)).trans_eq (by ring))
    · filter_upwards [hv] with v hv'
      have h := (turning_point_along hd (B := B+v) (u := fun n => u n+v)
        (hu.mono fun n hn => by rw [abs_of_nonneg (add_nonneg hn.1 hv'.le)]; linarith [hn.2])).1
      apply h.congr'
      filter_upwards [hr₂.eventually_ge_atTop (B+v), hu] with n hr' hn
      rw [truncatedLine, indicator_of_mem (show v ∈ Iic _ from by
        change v ≤ 2*r n^2-u n
        linarith [sq_nonneg (r n), hn.2])]
  apply H.congr'
  filter_upwards [hu, hr.eventually_ge_atTop 1, hr₂.eventually_ge_atTop B] with n hn hr' hB
  have hi₁ : Integrable (truncatedLine (d n) (u n)) μ :=
    (hg.const_mul C).mono' (measurable_line _ _).aestronglyMeasurable
      (hv.mono fun _ h => hline n hr' h.le hn.1)
  have hi₂ : Integrable (fun v : ℝ => ai (u n+v : ℝ)) μ :=
    (hg.const_mul A).mono' (hc n).aestronglyMeasurable
      (hv.mono fun v h => hmodel v (u n) h.le hn.1)
  rw [integral_sub hi₁ hi₂]
  dsimp only [μ]
  rw [line_integral _ (by change u n ≤ 2*r n^2; linarith [hn.2])]

end ProjectAinos.SpecialFunctions.Bessel
