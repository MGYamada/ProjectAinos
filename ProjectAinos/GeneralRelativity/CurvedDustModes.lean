/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.CurvedPerturbation
import Mathlib.Tactic

/-! # Separated scalar dust modes in curved FLRW universes -/

@[expose] public section
noncomputable section
open Set Filter ContinuousLinearMap
open scoped ContDiff Topology
namespace ProjectAinos.GeneralRelativity.CurvedPerturbation
open SmoothGeometry CoordinateMetric FLRW IsotropicRicci
local notation "E" => MinkowskiModel 3

/-- The longitudinal potential of one spatial mode in conformal time. -/
def separated (φ : ℝ → ℝ) (Q : E → ℝ) (x : E) := φ (x 0)*Q x

private theorem sep_part {φ : ℝ → ℝ} {Q : E → ℝ} {x : E} (hφ : DifferentiableAt ℝ φ (x 0))
    (hQ : DifferentiableAt ℝ Q x) (i : Fin 4) :
    part (separated φ Q) i x =
      (if i=0 then deriv φ (x 0)*Q x else 0)+φ (x 0)*part Q i x := by
  change fderiv ℝ (fun z : E => φ (z 0)*Q z) x (Pi.single i 1)=_
  have h := (hasFDerivAt_time hφ.hasDerivAt).mul hQ.hasFDerivAt
  change HasFDerivAt (fun z : E => φ (z 0)*Q z) _ x at h
  rw [h.fderiv]
  by_cases hi : i=0 <;>
    simp [smul_apply,proj_apply,add_apply,smul_eq_mul,part,hi,eq_comm,mul_comm,add_comm]

private theorem sep_jets {φ : ℝ → ℝ} {Q : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ (x 0)) (hQ : ContDiffAt ℝ ∞ Q x)
    (h₀ : ∀ᶠ y in 𝓝 x, part Q 0 y=0) :
    part (separated φ Q) 0 x=deriv φ (x 0)*Q x ∧
    secondPartial (separated φ Q) x 0 0=deriv (deriv φ) (x 0)*Q x ∧
    (∀ i : Fin 4, i≠0 → secondPartial (separated φ Q) x i 0=deriv φ (x 0)*part Q i x) ∧
    ∀ k, spatialLaplacian k (separated φ Q) x=φ (x 0)*spatialLaplacian k Q x := by
  have hφ' : ContDiffAt ℝ ∞ (deriv φ) (x 0) := hφ.derivWithin (by simp)
  have hf := hφ.differentiableAt (by simp)
  have hq := hQ.differentiableAt (by simp)
  have hp := (hφ.of_le (m := 1) (by simp)).eventually (by simp)
  have hnear : ∀ᶠ z : E in 𝓝 x, DifferentiableAt ℝ φ (z 0) :=
    ((continuous_apply 0 : Continuous (fun z : E => z 0)).continuousAt.tendsto.eventually hp).mono
      fun _ hz => hz.differentiableAt one_ne_zero
  have ev (i : Fin 4) : part (separated φ Q) i =ᶠ[𝓝 x] (if i=0 then separated (deriv φ) Q
      else separated φ (part Q i)) := by
    filter_upwards [hnear,eventually_differentiableAt hQ,h₀] with y hy hyQ hy₀
    by_cases hi : i=0 <;>
      simp [sep_part (hy) hyQ,hi,hy₀,separated]
  have sec (i j : Fin 4) : secondPartial (separated φ Q) x i j=
      part (if j=0 then separated (deriv φ) Q else separated φ (part Q j)) i x :=
    congrArg (fun T : E →L[ℝ] ℝ => T (Pi.single i 1)) (ev j).fderiv_eq
  have hs (i : Fin 4) (hi : i≠0) : secondPartial (separated φ Q) x i i =
      φ (x 0)*secondPartial Q x i i := by
    rw [sec]
    simp only [hi,ite_false]
    exact (sep_part hf (differentiableAt_partial hQ (Pi.single i 1)) i).trans (by
      simp only [hi,ite_false,zero_add]; rfl)
  refine ⟨by simpa [separated] using (ev 0).eq_of_nhds,?_,?_,?_⟩
  · rw [sec]
    simp [sep_part (hφ'.differentiableAt (by simp)) hq,h₀.self_of_nhds]
  · intro i hi
    rw [sec]
    simp [sep_part (hφ'.differentiableAt (by simp)) hq,hi]
  · intro k
    simp [spatialLaplacian,hs,sep_part hf hq]
    ring

/-- Density contrast of a scalar harmonic with positive-Laplacian eigenvalue q. -/
def contrast (D : Data) (κ : ℝ) (ρ φ : ℝ → ℝ) (q : ℝ) (Q : E → ℝ) (x : E) :=
  let t := x 0
  2*((3*D.k-q)*φ t-3*hubble D t*(deriv φ t+hubble D t*φ t))*Q x/(κ*ρ t*D.a t^2)

/-- Spatial covelocity perturbation of the same harmonic. -/
def covelocity (D : Data) (κ : ℝ) (ρ φ : ℝ → ℝ) (Q : E → ℝ) (x : E) (i : Fin 4) :=
  -2*(deriv φ (x 0)+hubble D (x 0)*φ (x 0))*part Q i x/(κ*ρ (x 0)*D.a (x 0))

/-- A spatial eigenfunction and either solution of the scalar evolution equation give a
metric, density and velocity solving all the first-order Einstein equations with dust. -/
theorem single_mode {D : Data} (hN : D.N=D.a) {κ : ℝ} {ρ φ : ℝ → ℝ}
    (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0)) {x : E} (hx : x ∈ domain D)
    (hm : κ*ρ (x 0)≠0) (hφ : ContDiffAt ℝ ∞ φ (x 0)) (Q : E → ℝ) (hQ : ContDiffAt ℝ ∞ Q x)
    (h₀ : ∀ᶠ y in 𝓝 x, part Q 0 y=0) (q : ℝ) (he : spatialLaplacian D.k Q x = -q*Q x)
    (ht : deriv (deriv φ) (x 0)+3*hubble D (x 0)*deriv φ (x 0)-2*D.k*φ (x 0)=0) :
    LinearizedDustAt D κ ρ (separated φ Q) (contrast D κ ρ φ q Q) (covelocity D κ ρ φ Q) x := by
  have hu : ContDiffAt ℝ ∞ (separated φ Q) x :=
    (hφ.comp x (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0).contDiffAt).mul hQ
  apply (linearizedDustAt_iff hN hB hx hu _ _).mpr
  obtain ⟨h₁,h₂,h₃,h₄⟩ := sep_jets hφ hQ h₀
  rw [h₁,h₂,h₄,he]
  have ha := (a_pos_of_mem hx).ne'
  obtain ⟨hκ,hρ⟩ := mul_ne_zero_iff.mp hm
  refine ⟨?_,?_,?_⟩
  · unfold separated
    linear_combination Q x*ht
  · unfold contrast separated
    field_simp [hκ,hρ,ha]; ring
  · intro i hi
    rw [h₃ i hi,sep_part (hφ.differentiableAt (by simp)) (hQ.differentiableAt (by simp))]
    simp only [hi,ite_false,zero_add]
    unfold covelocity
    field_simp [hκ,hρ,ha]

end ProjectAinos.GeneralRelativity.CurvedPerturbation
