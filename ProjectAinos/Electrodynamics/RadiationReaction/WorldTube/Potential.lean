/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.RadiationReaction.WorldTube.Retarded
import Mathlib.Tactic

/-!
# The four-potential of Liénard and Wiechert in the proper time

For a charge `e` on a world line `z(τ)` in the proper time (`ProperWorldline`), the four-potential
of Liénard and Wiechert is `A_μ = (e/4π) u_μ/ρ` at the retarded time `τ` of the event `x`, with
the separation `R = x − z(τ)` and the retarded distance `ρ = −R · u` (`lwPotential`; at rest
`A = −φ dt` with the potential of Coulomb `φ = e/(4πr)`).

* `hasFDerivAt_retardedProperTime`: at an event with a retarded time, `∂_μ τ = R_μ/(R · u)`, from
  the derivative of `(x − z(τ(x)))² = 0`.
* **The field** `fieldTensor_lwPotential`: the curvature `F_{μν} = ∂_μ A_ν − ∂_ν A_μ` of the
  potential is `retardedField`, `F = −(e/4π)(R ∧ a/ρ² + (1 + R · a) R ∧ u/ρ³)`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace ProjectAinos.Electrodynamics.RadiationReaction.WorldTube

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity

local notation "η" => minkowskiForm LorentzConvention.timeNegative 3

/-- **The four-potential of Liénard and Wiechert** `A_μ = (e/4π) u_μ/ρ` of a charge `e` on the
world line `w`, at the retarded proper time of the event. -/
def lwPotential (e : ℝ) (w : ProperWorldline) : Potential := fun x =>
  oneCovector.symm ((e / (4 * Real.pi) *
    (-η (x - w.z (w.retardedProperTime x)) (w.vel (w.retardedProperTime x)))⁻¹) •
      η (w.vel (w.retardedProperTime x)))

namespace ProperWorldline

variable {w : ProperWorldline}

/-- **The derivative of the retarded proper time**: `dτ(v) = (R · v)/(R · u)`. -/
theorem hasFDerivAt_retardedProperTime {x : Spacetime} {τ₀ : ℝ} (h : w.IsRetarded x τ₀) :
    HasFDerivAt w.retardedProperTime
      ((η (x - w.z τ₀) (w.vel τ₀))⁻¹ • η (x - w.z τ₀)) x := by
  have hτ := retardedProperTime_eq h
  have hD := ((contDiffAt_retardedProperTime h).differentiableAt (by norm_num)).hasFDerivAt
  set D := fderiv ℝ w.retardedProperTime x with hDdef
  have hz : HasFDerivAt (fun y => w.z (w.retardedProperTime y))
      ((ContinuousLinearMap.toSpanSingleton ℝ (w.vel τ₀)).comp D) x := by
    have h1 := (w.hasDerivAt_z (w.retardedProperTime x)).hasFDerivAt
    have h2 := h1.comp x hD
    rw [hτ] at h2
    exact h2
  have hR : HasFDerivAt (fun y => y - w.z (w.retardedProperTime y))
      (ContinuousLinearMap.id ℝ Spacetime -
        (ContinuousLinearMap.toSpanSingleton ℝ (w.vel τ₀)).comp D) x :=
    (hasFDerivAt_id x).sub hz
  have hg := ((minkowskiForm .timeNegative 3).hasFDerivAt.comp x hR).clm_apply hR
  have hg0 : HasFDerivAt (fun y => η (y - w.z (w.retardedProperTime y))
      (y - w.z (w.retardedProperTime y))) (0 : Spacetime →L[ℝ] ℝ) x := by
    refine (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq ?_
    filter_upwards [eventually_isRetarded h] with y hy
    exact hy.1
  have huniq := hg.unique hg0
  set R := x - w.z τ₀ with hRdef
  have hRx : x - w.z (w.retardedProperTime x) = R := by rw [hτ]
  have hRu : η R (w.vel τ₀) ≠ 0 := by
    have := retardedDistance_pos h
    intro h0
    rw [← hRdef, h0] at this
    simp at this
  have key : ∀ v, η R v = D v * η R (w.vel τ₀) := by
    intro v
    have h1 := congrArg (fun L : Spacetime →L[ℝ] ℝ => L v) huniq
    simp only [add_apply, ContinuousLinearMap.comp_apply, Function.comp_apply,
      ContinuousLinearMap.flip_apply, sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, zero_apply, hRx] at h1
    rw [minkowskiForm_symmetric _ (v - D v • w.vel τ₀) R] at h1
    simp only [map_sub, map_smul, smul_eq_mul] at h1
    linarith
  have hDeq : D = (η R (w.vel τ₀))⁻¹ • η R := by
    ext v
    rw [smul_apply, smul_eq_mul, key v]
    field_simp
  rw [← hDeq]
  exact hD

end ProperWorldline

/-- **The retarded field is the curvature of the four-potential of Liénard and Wiechert**: at
every event with a retarded time, `∂_μ A_ν − ∂_ν A_μ = F_{μν}` for `A_μ = (e/4π) u_μ/ρ` and
`F = −(e/4π)(R ∧ a/ρ² + (1 + R · a) R ∧ u/ρ³)`. -/
theorem fieldTensor_lwPotential (e : ℝ) (w : ProperWorldline) {x : Spacetime} {τ₀ : ℝ}
    (h : w.IsRetarded x τ₀) : fieldTensor (lwPotential e w) x = retardedField e w x := by
  have hτ := ProperWorldline.retardedProperTime_eq h
  have hD := ProperWorldline.hasFDerivAt_retardedProperTime h
  have hRu : η (x - w.z τ₀) (w.vel τ₀) ≠ 0 := by
    have := ProperWorldline.retardedDistance_pos h
    intro h0
    rw [h0] at this
    simp at this
  have hz : HasFDerivAt (fun y => w.z (w.retardedProperTime y))
      ((ContinuousLinearMap.toSpanSingleton ℝ (w.vel τ₀)).comp
        ((η (x - w.z τ₀) (w.vel τ₀))⁻¹ • η (x - w.z τ₀))) x := by
    have h2 := (w.hasDerivAt_z (w.retardedProperTime x)).hasFDerivAt.comp x hD
    rw [hτ] at h2
    exact h2
  have hU : HasFDerivAt (fun y => w.vel (w.retardedProperTime y))
      ((ContinuousLinearMap.toSpanSingleton ℝ (w.acc τ₀)).comp
        ((η (x - w.z τ₀) (w.vel τ₀))⁻¹ • η (x - w.z τ₀))) x := by
    have h2 := (w.hasDerivAt_vel (w.retardedProperTime x)).hasFDerivAt.comp x hD
    rw [hτ] at h2
    exact h2
  have hR := (hasFDerivAt_id x).sub hz
  have hρ1 := ((minkowskiForm .timeNegative 3).hasFDerivAt.comp x hR).clm_apply hU
  have hρ : HasFDerivAt (fun y => -η (y - w.z (w.retardedProperTime y))
      (w.vel (w.retardedProperTime y))) _ x := hρ1.fun_neg
  have hρ0 : -(η (x - w.z (w.retardedProperTime x)) (w.vel (w.retardedProperTime x))) ≠ 0 := by
    rw [hτ]; exact neg_ne_zero.mpr hRu
  have hφ1 : HasFDerivAt (fun y => (-η (y - w.z (w.retardedProperTime y))
      (w.vel (w.retardedProperTime y)))⁻¹) _ x := (hasFDerivAt_inv hρ0).comp x hρ
  have hφ : HasFDerivAt (fun y => e / (4 * Real.pi) * (-η (y - w.z (w.retardedProperTime y))
      (w.vel (w.retardedProperTime y)))⁻¹) _ x := HasFDerivAt.const_mul hφ1 (e / (4 * Real.pi))
  have hηU : HasFDerivAt (fun y => η (w.vel (w.retardedProperTime y))) _ x :=
    (minkowskiForm .timeNegative 3).hasFDerivAt.comp x hU
  have hG : HasFDerivAt (fun y => (e / (4 * Real.pi) * (-η (y - w.z (w.retardedProperTime y))
      (w.vel (w.retardedProperTime y)))⁻¹) • η (w.vel (w.retardedProperTime y))) _ x :=
    HasFDerivAt.smul hφ hηU
  have hA := HasFDerivAt.comp x (oneCovector.symm : FourCovector ≃L[ℝ] OneForm).hasFDerivAt hG
  have hAf : fderiv ℝ (lwPotential e w) x = _ := hA.fderiv
  refine ContinuousAlternatingMap.ext fun v => ?_
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, fieldTensor_apply, hAf, retardedField, hτ, bivector_apply, lwVector]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, neg_apply, Function.comp_apply,
    ContinuousLinearMap.flip_apply, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, map_smul, map_add, map_sub, hτ,
    Pi.sub_apply, id_eq]
  rw [minkowskiForm_symmetric _ (v 0) (w.vel τ₀), minkowskiForm_symmetric _ (v 1) (w.vel τ₀),
    minkowskiForm_symmetric _ (w.acc τ₀) (v 0), minkowskiForm_symmetric _ (w.acc τ₀) (v 1),
    w.vel_unit]
  have hRu' : η x (w.vel τ₀) - η (w.z τ₀) (w.vel τ₀) ≠ 0 := by
    simpa [map_sub] using hRu
  field_simp
  ring

end ProjectAinos.Electrodynamics.RadiationReaction.WorldTube
