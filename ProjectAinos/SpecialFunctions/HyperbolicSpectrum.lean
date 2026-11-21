/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.HyperbolicHarmonics
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! # Absence of bound states in the hyperbolic radial equations

For a regular finite-energy eigenfunction u = sinh(r) f(r), the radial virial
quantity r[u'² + (E−1−V)u²] + uu' has derivative 2u'²−rV'u² ≥ 0. Its value
at the pole and square integrability at infinity force it to vanish identically.
-/

@[expose] public section
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff
namespace ProjectAinos.SpecialFunctions.Hyperbolic

private theorem dp (l : ℕ) {r : ℝ} (hr : 0 < r) : HasDerivAt (potential l)
    (-(2*(l : ℝ)*(l+1)*Real.cosh r)/Real.sinh r^3) r := by
  have h := ((hasDerivAt_const r ((l : ℝ)*(l+1))).div ((Real.hasDerivAt_sinh r).pow 2)
    (pow_ne_zero _ (Real.sinh_pos_iff.mpr hr).ne'))
  apply h.congr_deriv
  simp only [zero_mul,zero_sub,Nat.cast_ofNat,Nat.reduceSub,pow_one,Pi.pow_apply]
  field_simp

/-- A regular finite-energy channel has no L² eigenfunction at any real energy.
The Dirichlet value at zero is that of u = sinh(r) f for a regular spatial mode. -/
theorem no_bound_state (l : ℕ) (E : ℝ) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (h₀ : u 0 = 0)
    (hL : IntegrableOn (fun r => u r^2) (Ioi 0))
    (hD : IntegrableOn (fun r => deriv u r^2) (Ioi 0))
    (he : ∀ r : ℝ, 0 < r → deriv (deriv u) r = (1+potential l r-E)*u r) :
    EqOn u 0 (Ici 0) := by
  let d := deriv u
  let V := potential l
  let J (r : ℝ) := r*(d r^2+(E-1-V r)*u r^2)+u r*d r
  let L := (l : ℝ)*(l+1)
  have hL₀ : 0 ≤ L := by dsimp [L]; positivity
  have hdu : ContDiff ℝ 1 d := (contDiff_succ_iff_deriv.mp hu).2.2
  have du (r : ℝ) : HasDerivAt u (d r) r := (hu.differentiable (by norm_num) r).hasDerivAt
  have dd (r : ℝ) (hr : 0 < r) : HasDerivAt d ((1+V r-E)*u r) r := by
    rw [← he r hr]
    exact (hdu.differentiable (by norm_num) r).hasDerivAt
  have dJ (r : ℝ) (hr : 0 < r) : HasDerivAt J
      (2*d r^2+r*(2*L*Real.cosh r/Real.sinh r^3)*u r^2) r := by
    have h := ((hasDerivAt_id' r).mul (((dd r hr).pow 2).add
      (((dp l hr).const_sub (E-1)).mul ((du r).pow 2)))).add ((du r).mul (dd r hr))
    apply h.congr_deriv
    dsimp only [id_eq,Pi.pow_apply,Pi.mul_apply,Pi.add_apply,L]
    ring
  have hmono : MonotoneOn J (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact fun r hr => (dJ r hr).continuousAt.continuousWithinAt
    · exact fun r hr => (dJ r (interior_subset hr)).differentiableAt.differentiableWithinAt
    · intro r hr
      have h : 0 < r := interior_subset hr
      rw [(dJ r h).deriv]
      positivity [Real.sinh_pos_iff.mpr h,Real.cosh_pos r]
  have hJ₀ : Tendsto J (𝓝[>] 0) (𝓝 0) := by
    have hx : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hs := (Real.hasDerivAt_sinh 0).tendsto_slope_zero_right
    have h := (du 0).tendsto_slope_zero_right
    simp only [zero_add,h₀,sub_zero,Real.sinh_zero,Real.cosh_zero,smul_eq_mul] at hs h
    have hratio := h.div hs one_ne_zero
    have hu₀ := hu.continuous.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
    have hd₀ := hdu.continuous.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
    rw [h₀] at hu₀
    have h₁ := (hx.mul ((hd₀.pow 2).add (hu₀.pow 2 |>.const_mul (E-1)))).add (hu₀.mul hd₀)
    have h₂ := (hx.mul_const L).mul (hratio.pow 2)
    have H := h₁.sub h₂
    simp only [zero_mul,add_zero,sub_zero] at H
    apply H.congr'
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    dsimp only [J,V,potential,L,Pi.div_apply]
    field_simp [hr.ne',(Real.sinh_pos_iff.mpr hr).ne']
    ring
  have hnn (r : ℝ) (hr : 0 < r) : 0 ≤ J r := by
    apply le_of_tendsto hJ₀
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (Iio_mem_nhds hr) : Iio r ∈ 𝓝[>] (0 : ℝ))]
      with t ht ht' using hmono ht hr (show t < r from ht').le
  have hnp (r : ℝ) (hr : 0 < r) : J r ≤ 0 := by
    by_contra! h
    let b := max r 1
    let K := (|E-1|+2)/J r
    have H : IntegrableOn (fun t => K*(d t^2+u t^2)) (Ioi b) :=
      ((hD.add hL).mono_set (Ioi_subset_Ioi (hr.le.trans (le_max_left r 1)))).const_mul _
    apply not_integrableOn_Ioi_inv (a := b)
    apply H.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hbt : b < t := ht
    have ht₁ : 1 ≤ t := (le_max_right r 1).trans hbt.le
    have ht₀ : 0 < t := by linarith
    have hv : 0 ≤ V t := by dsimp [V,potential]; positivity
    have hm := hmono hr ht₀ ((le_max_left r 1).trans hbt.le)
    have hJ : J r ≤ t*((|E-1|+2)*(d t^2+u t^2)) := by
      apply hm.trans
      dsimp only [J]
      have h₁ : u t*d t ≤ d t^2+u t^2 := by nlinarith [sq_nonneg (u t-d t)]
      nlinarith only [h₁,
        mul_le_mul_of_nonneg_right ht₁ (add_nonneg (sq_nonneg (d t)) (sq_nonneg (u t))),
        mul_nonneg (mul_nonneg ht₀.le hv) (sq_nonneg (u t)),
        mul_le_mul_of_nonneg_right (le_abs_self (E-1)) (mul_nonneg ht₀.le (sq_nonneg (u t))),
        mul_nonneg (mul_nonneg ht₀.le (abs_nonneg (E-1))) (sq_nonneg (d t)),
        mul_nonneg ht₀.le (sq_nonneg (u t)),mul_nonneg ht₀.le (sq_nonneg (d t))]
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht₀)]
    dsimp only [K]
    calc
      t⁻¹ = J r/(t*J r) := by field_simp
      _ ≤ (t*((|E-1|+2)*(d t^2+u t^2)))/(t*J r) := by gcongr
      _ = _ := by field_simp
  have hz {r : ℝ} (hr : 0 < r) := le_antisymm (hnp r hr) (hnn r hr)
  have hd0 (r : ℝ) (hr : 0 < r) : d r = 0 := by
    have hh : J =ᶠ[𝓝 r] (fun _ => 0) := by
      filter_upwards [Ioi_mem_nhds hr] with t ht using hz ht
    have h := (dJ r hr).deriv.symm.trans hh.deriv_eq
    rw [deriv_const] at h
    have ha : 0 ≤ r*(2*L*Real.cosh r/Real.sinh r^3)*u r^2 := by
      positivity [Real.cosh_pos r,Real.sinh_pos_iff.mpr hr]
    nlinarith [sq_nonneg (d r)]
  intro r hr
  rcases eq_or_lt_of_le hr with h | h
  · simpa [← h] using h₀
  · obtain ⟨c,hc,hh⟩ := exists_deriv_eq_slope u h hu.continuous.continuousOn
      (hu.differentiable (by norm_num)).differentiableOn
    change d c = _ at hh
    rw [hd0 c hc.1,h₀,sub_zero,sub_zero] at hh
    exact (div_eq_zero_iff.mp hh.symm).resolve_right h.ne'

end ProjectAinos.SpecialFunctions.Hyperbolic
