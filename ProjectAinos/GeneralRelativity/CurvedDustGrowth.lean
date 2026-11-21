/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.CurvedPerturbation
import Mathlib.Tactic

/-! # Two independent dust amplitudes, including the closed turnaround

For conformal time let H = a′/a. The two solutions H/a² and
1−2(H/a²)∫a² dη have Wronskian (H²+k)/(2a²). Neither formula divides by H.
-/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ProjectAinos.GeneralRelativity.CurvedPerturbation
open FLRW

/-- The first scalar gravitational-potential mode. -/
def decay (D : Data) (t : ℝ) := hubble D t/(D.a t)^2

/-- The second scalar gravitational-potential mode. The time origin changes the
multiple of the first mode. -/
def growth (D : Data) (b t : ℝ) := 1-2*decay D t*(∫ s in b..t, (D.a s)^2)

/-- Conformal-time evolution equation for a dust potential. -/
def Evolution (D : Data) (φ : ℝ → ℝ) (t : ℝ) : Prop :=
  deriv (deriv φ) t+3*hubble D t*deriv φ t-2*D.k*φ t=0

/-- Both temporal modes solve the evolution equation; their Wronskian is positive wherever
the dust density and coupling are positive, even at maximal expansion. -/
theorem dust_amplitudes {D : Data} (hN : D.N=D.a) {κ : ℝ} {ρ : ℝ → ℝ}
    (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0)) (hc : Continuous D.a)
    (b : ℝ) {t : ℝ} (ht : t ∈ D.I) :
    Evolution D (decay D) t ∧ Evolution D (growth D b) t ∧
      decay D t*deriv (growth D b) t-deriv (decay D) t*growth D b t =
        ((hubble D t)^2+D.k)/(2*(D.a t)^2) := by
  let H := hubble D
  let a := D.a
  let I (s : ℝ) := ∫ y in b..s, (a y)^2
  have hH {s : ℝ} (hs : s ∈ D.I) : HasDerivAt H (-(H s^2+D.k)/2) s := by
    apply (hasDerivAt_hubble hs).differentiableAt.hasDerivAt.congr_deriv
    linarith only [(conformal_dust_eq hN hB hs).2]
  have ha {s : ℝ} (hs : s ∈ D.I) : HasDerivAt a (H s*a s) s := by
    apply (hasDerivAt_of_contDiffOn D.isOpen_I D.contDiffOn_a hs).congr_deriv
    simp [H,hubble,a,(D.a_pos s hs).ne']
  have na {s : ℝ} (hs : s ∈ D.I) : a s ≠ 0 := (D.a_pos s hs).ne'
  have hi (s : ℝ) : HasDerivAt I (a s^2) s :=
    intervalIntegral.integral_hasDerivAt_right ((hc.pow 2).intervalIntegrable ..)
      (hc.pow 2).stronglyMeasurable.stronglyMeasurableAtFilter (hc.pow 2).continuousAt
  let v (s : ℝ) := -(5*H s^2+D.k)/(2*a s^2)
  have dd {s : ℝ} (hs : s ∈ D.I) : HasDerivAt (decay D) (v s) s := by
    apply ((hH hs).div ((ha hs).pow 2) (pow_ne_zero _ (na hs))).congr_deriv
    dsimp [v]; field_simp [na hs]; ring
  have v' : HasDerivAt v (-3*H t*v t+2*D.k*decay D t) t := by
    apply ((((((hH ht).pow 2).const_mul 5).add_const D.k).neg).div
      (((ha ht).pow 2).const_mul 2) (mul_ne_zero (by norm_num) (pow_ne_zero _ (na ht)))).congr_deriv
    dsimp [v,decay]
    change _ = -3*H t*(-(5*H t^2+D.k)/(2*a t^2))+2*D.k*(H t/a t^2)
    field_simp [na ht]; ring
  let w (s : ℝ) := -2*v s*I s-2*decay D s*a s^2
  have dg {s : ℝ} (hs : s ∈ D.I) : HasDerivAt (growth D b) (w s) s := by
    apply ((((dd hs).const_mul 2).mul (hi s)).const_sub 1).congr_deriv
    dsimp [w]; ring
  have w' : HasDerivAt w (-3*H t*w t+2*D.k*growth D b t) t := by
    apply ((((v'.const_mul (-2)).mul (hi t))).sub
      (((dd ht).const_mul 2).mul ((ha ht).pow 2))).congr_deriv
    dsimp [w,growth,v,decay]
    change _ = -3*H t*(-2*(-(5*H t^2+D.k)/(2*a t^2))*I t-2*(H t/a t^2)*a t^2)+
      2*D.k*(1-2*(H t/a t^2)*I t)
    dsimp only [H,a,I]
    field_simp [(D.a_pos t ht).ne']; ring
  have hdv : deriv (decay D) =ᶠ[𝓝 t] v := by
    filter_upwards [D.isOpen_I.mem_nhds ht] with s hs using (dd hs).deriv
  have hdw : deriv (growth D b) =ᶠ[𝓝 t] w := by
    filter_upwards [D.isOpen_I.mem_nhds ht] with s hs using (dg hs).deriv
  refine ⟨?_,?_,?_⟩
  · unfold Evolution
    rw [hdv.deriv_eq,v'.deriv,(dd ht).deriv]
    dsimp [H]; ring
  · unfold Evolution
    rw [hdw.deriv_eq,w'.deriv,(dg ht).deriv]
    dsimp [H]; ring
  · rw [(dg ht).deriv,(dd ht).deriv]
    dsimp [v,w,growth,decay,H,a,I]
    field_simp [(D.a_pos t ht).ne']; ring

/-- Smoothness of both potentials on the background interval. -/
theorem smooth_amplitudes (D : Data) (hc : Continuous D.a) (b : ℝ) :
    ContDiffOn ℝ ∞ (decay D) D.I ∧ ContDiffOn ℝ ∞ (growth D b) D.I := by
  have hs : ContDiffOn ℝ ∞ (hubble D) D.I :=
    (contDiffOn_deriv_of_contDiffOn D.isOpen_I D.contDiffOn_a).div D.contDiffOn_a
      fun t ht => (D.a_pos t ht).ne'
  have hd : ContDiffOn ℝ ∞ (decay D) D.I := hs.div (D.contDiffOn_a.pow 2)
    fun t ht => pow_ne_zero _ (D.a_pos t ht).ne'
  let F (t : ℝ) := ∫ s in b..t, D.a s^2
  have he (t : ℝ) : HasDerivAt F (D.a t^2) t :=
    intervalIntegral.integral_hasDerivAt_right ((hc.pow 2).intervalIntegrable ..)
      (hc.pow 2).stronglyMeasurable.stronglyMeasurableAtFilter (hc.pow 2).continuousAt
  have hF : ContDiffOn ℝ ∞ F D.I := (contDiffOn_infty_iff_deriv_of_isOpen D.isOpen_I).mpr
    ⟨fun t _ => (he t).differentiableAt.differentiableWithinAt,
      (D.contDiffOn_a.pow 2).congr fun t _ => (he t).deriv⟩
  exact ⟨hd,contDiffOn_const.sub ((contDiffOn_const.mul hd).mul hF)⟩

end ProjectAinos.GeneralRelativity.CurvedPerturbation
