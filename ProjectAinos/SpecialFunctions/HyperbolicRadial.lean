/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.HyperbolicHarmonics
public import ProjectAinos.SpecialFunctions.HyperbolicZonal
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! # Regular hyperbolic modes in the ambient coordinate s = cosh r

The degree-ℓ radial coefficient factors as sinh(r)ˡ times the ℓ-th derivative of the
zonal profile. They solve the hyperbolic Gegenbauer equation up to and including the pole.
-/

@[expose] public section
noncomputable section
open Set Filter Complex
open scoped ContDiff Topology
namespace ProjectAinos.SpecialFunctions.Hyperbolic

private def seed (k r : ℝ) := if k=0 then r else Real.sin (k*r)/k

private theorem seed_eq (k r : ℝ) : sineSeed k r = ((seed k r : ℝ) : ℂ) := by
  by_cases h : k=0 <;> simp [seed,sineSeed,h]

private theorem free_eq (k r : ℝ) : deriv (deriv (seed k)) r = -k^2*seed k r := by
  by_cases h : k=0
  · subst k
    show deriv (deriv (fun t : ℝ => if (0 : ℝ)=0 then t else _)) r=_
    simp [seed]
  · have d (s : ℝ) : HasDerivAt (seed k) (Real.cos (k*s)) s := by
      unfold seed
      simpa [h] using ((((hasDerivAt_id' s).const_mul k).sin).div_const k)
    rw [show deriv (seed k) = fun s => Real.cos (k*s) from funext fun s => (d s).deriv,
      (((hasDerivAt_id' r).const_mul k).cos).deriv]
    simp [seed,h]; field_simp

/-- The real radial profile of degree ℓ, after removing sinh(r)ˡ. -/
def ambientProfile (k : ℝ) (l : ℕ) := deriv^[l] (zonalProfile k)

/-- Removing the geometric vanishing factor leaves a smooth profile, including at the pole. -/
theorem smooth_ambientProfile_at (k : ℝ) (l : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    ContDiffAt ℝ ∞ (ambientProfile k l) s := by
  induction l with
  | zero => exact smooth_zonalProfile k hs
  | succ l ih =>
    simpa only [ambientProfile,Function.iterate_succ_apply'] using
      ih.derivWithin (m := ∞) (by simp)

theorem smooth_ambientProfile (k : ℝ) (l : ℕ) : ContDiffOn ℝ ∞ (ambientProfile k l) (Ioi 1) :=
  fun _ hs => (smooth_ambientProfile_at k l (le_of_lt hs)).contDiffWithinAt

private theorem ladder (k : ℝ) (l : ℕ) {r : ℝ} (hr : 0 < r) :
    raised (sineSeed k) l r =
      ((Real.sinh r^(l+1)*ambientProfile k l (Real.cosh r) : ℝ) : ℂ) := by
  induction l generalizing r with
  | zero =>
    change sineSeed k r = ↑(Real.sinh r^(0+1)*zonalProfile k (Real.cosh r))
    rw [zonalProfile_cosh k hr,seed_eq]
    congr 1
    change seed k r = Real.sinh r^(0+1)*(seed k r/Real.sinh r)
    field_simp [(Real.sinh_pos_iff.mpr hr).ne']; ring
  | succ l ih =>
    let F := ambientProfile k l
    have hF := ((smooth_ambientProfile k l).contDiffAt (isOpen_Ioi.mem_nhds
      (Real.one_lt_cosh.mpr hr.ne'))).differentiableAt (by simp)
    have eq : raised (sineSeed k) l =ᶠ[𝓝 r] fun y =>
        ((Real.sinh y^(l+1)*F (Real.cosh y) : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds hr] with y hy using ih hy
    have d := (((Real.hasDerivAt_sinh r).pow (l+1)).mul
      (hF.hasDerivAt.comp r (Real.hasDerivAt_cosh r))).ofReal_comp
    change HasDerivAt (fun y : ℝ => ((Real.sinh y^(l+1)*F (Real.cosh y) : ℝ) : ℂ)) _ r at d
    rw [raised,raise,eq.deriv_eq,d.deriv,eq.eq_of_nhds]
    rw [show ambientProfile k (l+1)=deriv F by
      simp only [ambientProfile,F,Function.iterate_succ_apply']]
    change _ = ((Real.sinh r^(l+1+1)*deriv F (Real.cosh r) : ℝ) : ℂ)
    push_cast
    simp only [Function.comp_apply,Pi.pow_apply]
    have hn : Complex.sinh (r : ℂ)≠0 := by
      rw [← ofReal_sinh]; exact ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hr).ne'
    field_simp [hn]
    push_cast
    ring

/-- Geodesic radial modes are exactly the ambient profiles times sinh(r)ˡ. -/
theorem harmonic_eq_ambient (k : ℝ) (l : ℕ) {r : ℝ} (hr : 0 < r) :
    harmonic l k r = ((Real.sinh r^l*ambientProfile k l (Real.cosh r) : ℝ) : ℂ) := by
  simp only [harmonic,hr.ne',ite_false,ladder k l hr,← ofReal_div,ofReal_inj,pow_succ]
  field_simp [(Real.sinh_pos_iff.mpr hr).ne']

private theorem base_eq (k : ℝ) {s : ℝ} (hs : 1 < s) :
    let F := ambientProfile k 0
    (s^2-1)*deriv (deriv F) s+3*s*deriv F s+(1+k^2)*F s=0 := by
  let F := ambientProfile k 0
  let r := Real.arcosh s
  have hr : 0 < r := Real.arcosh_pos hs
  have hcos : Real.cosh r=s := Real.cosh_arcosh hs.le
  have hsh := (Real.sinh_pos_iff.mpr hr).ne'
  have sm := smooth_ambientProfile k 0
  have hF (t : ℝ) (ht : 0<t) : ContDiffAt ℝ ∞ F (Real.cosh t) :=
    sm.contDiffAt (isOpen_Ioi.mem_nhds (Real.one_lt_cosh.mpr ht.ne'))
  have eq (t : ℝ) (ht : 0<t) : Real.sinh t*F (Real.cosh t)=seed k t := by
    change Real.sinh t*zonalProfile k (Real.cosh t)=seed k t
    rw [zonalProfile_cosh k ht]
    change Real.sinh t*(seed k t/Real.sinh t)=_
    field_simp [(Real.sinh_pos_iff.mpr ht).ne']
  let V (t : ℝ) := Real.cosh t*F (Real.cosh t)+Real.sinh t^2*deriv F (Real.cosh t)
  have d (t : ℝ) (ht : 0<t) : HasDerivAt (seed k) (V t) t := by
    have e : seed k =ᶠ[𝓝 t] fun y => Real.sinh y*F (Real.cosh y) := by
      filter_upwards [Ioi_mem_nhds ht] with y hy using (eq y hy).symm
    apply (((Real.hasDerivAt_sinh t).mul (((hF t ht).differentiableAt (by simp)).hasDerivAt.comp t
      (Real.hasDerivAt_cosh t))).congr_of_eventuallyEq e).congr_deriv
    dsimp [V]; ring
  have eV : deriv (seed k) =ᶠ[𝓝 r] V := by
    filter_upwards [Ioi_mem_nhds hr] with t ht using (d t ht).deriv
  have dt := ((Real.hasDerivAt_cosh r).mul
    (((hF r hr).differentiableAt (by simp)).hasDerivAt.comp r (Real.hasDerivAt_cosh r))).add
    (((Real.hasDerivAt_sinh r).pow 2).mul
      ((((hF r hr).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt.comp r
        (Real.hasDerivAt_cosh r)))
  have h := free_eq k r
  rw [eV.deriv_eq,(show HasDerivAt V _ r from dt).deriv,← eq r hr] at h
  dsimp only [Function.comp_apply,Pi.pow_apply] at h
  rw [hcos] at h
  have hcs := Real.cosh_sq_sub_sinh_sq r
  rw [hcos] at hcs
  apply mul_left_cancel₀ hsh
  change Real.sinh r*((s^2-1)*deriv (deriv F) s+3*s*deriv F s+(1+k^2)*F s)=Real.sinh r*0
  linear_combination h+Real.sinh r*deriv (deriv F) s*hcs

/-- The open-slice Gegenbauer equation at every real spectral parameter. -/
private theorem open_equation (k : ℝ) (l : ℕ) {s : ℝ} (hs : 1 < s) :
    let F := ambientProfile k l
    (s^2-1)*deriv (deriv F) s+(2*l+3)*s*deriv F s+
      ((l : ℝ)*(l+2)+1+k^2)*F s=0 := by
  induction l generalizing s with
  | zero => simpa using base_eq k hs
  | succ l ih =>
    let F := ambientProfile k l
    have hf : ContDiffAt ℝ ∞ F s := (smooth_ambientProfile k l).contDiffAt (Ioi_mem_nhds hs)
    have hd := hf.derivWithin (m := ∞) (by simp)
    have hdd := hd.derivWithin (m := ∞) (by simp)
    let U (t : ℝ) := (t^2-1)*deriv (deriv F) t+(2*l+3)*t*deriv F t+
      ((l : ℝ)*(l+2)+1+k^2)*F t
    have eq : U =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hs] with t ht using ih ht
    have d := (((((hasDerivAt_id' s).pow 2).sub_const 1).mul
      (hdd.differentiableAt (by simp)).hasDerivAt).add
        (((hasDerivAt_id' s).const_mul (2*(l : ℝ)+3)).mul
          (hd.differentiableAt (by simp)).hasDerivAt))
      |>.add (((hf.differentiableAt (by simp)).hasDerivAt).const_mul ((l : ℝ)*(l+2)+1+k^2))
    have h := (show HasDerivAt U _ s from d).deriv.symm.trans eq.deriv_eq
    simp only [deriv_const,Pi.pow_apply] at h
    rw [show ambientProfile k (l+1)=deriv F by
      simp only [ambientProfile,F,Function.iterate_succ_apply']]
    change (s^2-1)*deriv (deriv (deriv F)) s+(2*((l+1 : ℕ) : ℝ)+3)*s*deriv (deriv F) s+
      (((l+1 : ℕ) : ℝ)*((l+1 : ℕ)+2)+1+k^2)*deriv F s=0
    push_cast
    linear_combination h

/-- The Gegenbauer equation holds at the pole as well as on every geodesic sphere. -/
theorem ambient_equation (k : ℝ) (l : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    let F := ambientProfile k l
    (s^2-1)*deriv (deriv F) s+(2*l+3)*s*deriv F s+
      ((l : ℝ)*(l+2)+1+k^2)*F s=0 := by
  rcases hs.eq_or_lt with rfl | h
  · let F := ambientProfile k l
    let U (t : ℝ) := (t^2-1)*deriv (deriv F) t+(2*l+3)*t*deriv F t+
      ((l : ℝ)*(l+2)+1+k^2)*F t
    have hf : ContDiffAt ℝ ∞ F 1 := smooth_ambientProfile_at k l (le_refl 1)
    have hd := hf.derivWithin (m := ∞) (by simp)
    have hdd := hd.derivWithin (m := ∞) (by simp)
    have hc : ContinuousAt U 1 := by
      unfold U
      fun_prop (disch := first | exact hf.continuousAt | exact hd.continuousAt
                               | exact hdd.continuousAt)
    have eq : U =ᶠ[𝓝[>] 1] fun _ => 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht using open_equation k l ht
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' eq.symm)
  · exact open_equation k l h

end ProjectAinos.SpecialFunctions.Hyperbolic
