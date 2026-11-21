/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.PerturbationModeSplit
import Mathlib.Tactic

/-!
# The residual synchronous gauge modes lie in the scalar and vector sectors

Landau–Lifshitz, §115. The synchronous reference system leaves the time shift `gaugeMode`
(`λ = 6Fn²t^{−1/3}`, `μ = λ + 4F/t`) and the spatial co-ordinate changes: the scalar one
`spatialGaugeMode` (`λ = μ = c`) and the vector one, `σ = c` constant in a vector mode
(`vectorGauge_solution`). Their amplitudes lie in single sectors of the decomposition
(`scalarAmp_mem_scalar`, `vectorAmp_mem_vector`, with longitudinal velocities
`longVec_smul_self`), so the split of a solution into scalar, vector and tensor parts
(`ModeSplit.linearizedEinsteinDust_mode_iff_split`) keeps every gauge mode whole in its
sector: the scalar gauge modes in the scalar part and the vector gauge mode in the vector part,
and the tensor part contains no gauge mode.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.CosmologicalPerturbation.ModeSplit

open SmoothGeometry CoordinateMetric FLRW
open SmoothGeometry.ScalarVectorTensor (Mat3 scalarPart vectorPart tensorPart longVec transVec
  longProj)

local notation "E" => MinkowskiModel 3

variable {n : Fin 3 → ℝ}

/-- The scalar amplitude is `λ nn/n² + ((μ − λ)/3) δ`. -/
theorem scalarAmp_eq (lam mu : ℝ → ℝ) (t : ℝ) :
    scalarAmp n lam mu t =
      lam t • longProj n + ((mu t - lam t) / 3) • ScalarVectorTensor.delta ℝ := by
  funext α β
  simp only [scalarAmp, longitudinal, kron, longProj, ScalarVectorTensor.delta, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, ScalarVectorTensor.nsq, nsq]
  ring

/-- **The scalar modes lie in the scalar sector.** -/
theorem scalarAmp_mem_scalar (hn : nsq n ≠ 0) (lam mu : ℝ → ℝ) (t : ℝ) :
    scalarPart n (scalarAmp n lam mu t) = scalarAmp n lam mu t ∧
      vectorPart n (scalarAmp n lam mu t) = 0 ∧ tensorPart n (scalarAmp n lam mu t) = 0 := by
  have hn' : ScalarVectorTensor.nsq n ≠ 0 := hn
  simp only [scalarAmp_eq, map_add, map_smul, ScalarVectorTensor.scalarPart_longProj hn',
    ScalarVectorTensor.scalarPart_delta hn', ScalarVectorTensor.vectorPart_longProj hn',
    ScalarVectorTensor.vectorPart_delta hn', ScalarVectorTensor.tensorPart_longProj hn',
    ScalarVectorTensor.tensorPart_delta hn', smul_zero, add_zero, and_self]

/-- The velocities `w n` of the scalar modes are longitudinal. -/
theorem longVec_smul_self (hn : nsq n ≠ 0) (w : ℝ) :
    longVec n (w • n) = w • n ∧ transVec n (w • n) = 0 := by
  have hn' : ScalarVectorTensor.nsq n ≠ 0 := hn
  have h : longVec n n = n := by
    funext α
    rw [ScalarVectorTensor.longVec_apply, ScalarVectorTensor.dot_self, div_self hn', one_mul]
  refine ⟨by rw [map_smul, h], ?_⟩
  funext α
  simp [ScalarVectorTensor.transVec_apply, map_smul, h]

/-- **The vector modes lie in the vector sector**: for `e · n = 0`, the amplitude
`n ⊗ e + e ⊗ n` has no scalar and no tensor part. -/
theorem vectorAmp_mem_vector (hn : nsq n ≠ 0) {e : Fin 3 → ℝ} (he : ∑ γ, n γ * e γ = 0) :
    scalarPart n (vectorAmp n e) = 0 ∧ vectorPart n (vectorAmp n e) = vectorAmp n e ∧
      tensorPart n (vectorAmp n e) = 0 := by
  have hn' : ScalarVectorTensor.nsq n ≠ 0 := hn
  have hc : ScalarVectorTensor.contract n (vectorAmp n e) = fun β => nsq n * e β := by
    funext β
    have := ScalarVectorTensor.sum_mul_sym n e β
    simp only [ScalarVectorTensor.contract, vectorAmp, ScalarVectorTensor.dot, he, zero_mul,
      add_zero] at this ⊢
    exact (Finset.sum_congr rfl fun γ _ => by ring).trans this
  have hs : ScalarVectorTensor.sandwich n (vectorAmp n e) = 0 := by
    simp only [ScalarVectorTensor.sandwich, hc]
    rw [← Finset.sum_congr rfl fun γ _ => (mul_assoc (nsq n) (e γ) (n γ)).symm,
      ← Finset.mul_sum]
    simp only [mul_comm (e _) (n _), he, mul_zero]
  have ht : ScalarVectorTensor.trace (vectorAmp n e) = 0 := by
    simp only [ScalarVectorTensor.trace, vectorAmp]
    rw [← Finset.sum_congr rfl fun γ _ => (two_mul (n γ * e γ)).trans (by ring), ← Finset.mul_sum,
      he, mul_zero]
  have hsh : ScalarVectorTensor.shear n (vectorAmp n e) = fun β => nsq n * e β := by
    funext β; simp [ScalarVectorTensor.shear, ScalarVectorTensor.longCoeff, hc, hs]
  have hS : scalarPart n (vectorAmp n e) = 0 := by
    funext α β
    simp [ScalarVectorTensor.scalarPart_apply, ScalarVectorTensor.longCoeff, hs, ht]
  have hV : vectorPart n (vectorAmp n e) = vectorAmp n e := by
    funext α β
    rw [ScalarVectorTensor.vectorPart_apply, hsh]
    simp only [vectorAmp]
    field_simp
    simp only [ScalarVectorTensor.nsq, nsq]
    ring
  refine ⟨hS, hV, ?_⟩
  rw [ScalarVectorTensor.tensorPart_eq, hS, hV, sub_zero, sub_self]

variable {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}

/-- **The vector gauge mode**: a vector mode with a constant amplitude `σ = c`, without density
contrast and velocity, solves the linearized equations on a dust background; it is the change
of the spatial co-ordinates along the transverse field `c e sin(n · x)`. -/
theorem vectorGauge_solution (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) (hn : n ≠ 0) {e : Fin 3 → ℝ}
    (he : ∑ γ, n γ * e γ = 0) (he0 : e ≠ 0) (c : ℝ) :
    LinearizedEinsteinDust B κ ρ (vectorMode n e fun _ => c) (fun _ => 0) (fun _ _ => 0) := by
  have hv : (fun (_ : E) (_ : Fin 3) => (0 : ℝ)) =
      fun z α => (fun _ : ℝ => (0 : ℝ)) (z 0) * e α * Real.cos (phase n z) := by
    funext z α; simp
  rw [hv]
  refine (vectorMode_iff hB hn he he0 contDiffOn_const fun _ => 0).mpr fun t _ => ?_
  simp

end ProjectAinos.GeneralRelativity.CosmologicalPerturbation.ModeSplit
