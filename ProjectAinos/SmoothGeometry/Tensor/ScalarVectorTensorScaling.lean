/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Tensor.ScalarVectorTensor
import Mathlib.Tactic

/-!
# The scalar–vector–tensor projections depend only on the direction of the wave vector

For a nonzero scalar `c`, the projections of `ScalarVectorTensor` for the wave vector `c • n` are
those for `n` (`scalarPart_smul_left`, `vectorPart_smul_left`, `tensorPart_smul_left`,
`longVec_smul_left`, `transVec_smul_left`): `|n|²` scales by `c²` (`nsq_smul_left`), the
contraction and the transverse vector by `c` and the longitudinal coefficient not at all. For a
real wave vector the projections are therefore functions of the unit vector `n/|n|`; this gives
the bounds on their entries used in the Fourier analysis of §115.
-/

@[expose] public section

namespace ProjectAinos.SmoothGeometry.ScalarVectorTensor

variable {K : Type*} [Field K] (n : Fin 3 → K) (M : Mat3 K) (V : Fin 3 → K)

theorem nsq_smul_left (c : K) : nsq (c • n) = c ^ 2 * nsq n := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem contract_smul_left (c : K) : contract (c • n) M = c • contract n M := by
  funext β
  simp only [contract, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem sandwich_smul_left (c : K) : sandwich (c • n) M = c ^ 2 * sandwich n M := by
  simp only [sandwich, contract_smul_left, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_smul_left (c : K) : dot (c • n) V = c * dot n V := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

variable {c : K}

theorem longCoeff_smul_left (hc : c ≠ 0) : longCoeff (c • n) M = longCoeff n M := by
  simp only [longCoeff, sandwich_smul_left, nsq_smul_left]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)

theorem shear_smul_left (hc : c ≠ 0) : shear (c • n) M = c • shear n M := by
  funext β
  simp only [shear, contract_smul_left, longCoeff_smul_left n M hc, Pi.smul_apply, smul_eq_mul]
  ring

theorem ratio_smul_left (hc : c ≠ 0) (α β : Fin 3) :
    (c • n) α * (c • n) β / nsq (c • n) = n α * n β / nsq n := by
  simp only [Pi.smul_apply, smul_eq_mul, nsq_smul_left]
  rw [show c * n α * (c * n β) = c ^ 2 * (n α * n β) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)

theorem scalarPart_smul_left (hc : c ≠ 0) : scalarPart (c • n) = scalarPart n :=
  LinearMap.ext fun M => funext fun α => funext fun β => by
    simp only [scalarPart_apply, longCoeff_smul_left n M hc, ratio_smul_left n hc]

theorem vectorPart_smul_left (hc : c ≠ 0) : vectorPart (c • n) = vectorPart n :=
  LinearMap.ext fun M => funext fun α => funext fun β => by
    simp only [vectorPart_apply, shear_smul_left n M hc, nsq_smul_left, Pi.smul_apply,
      smul_eq_mul]
    rw [show c * n α * (c * shear n M β) + c * shear n M α * (c * n β) =
      c ^ 2 * (n α * shear n M β + shear n M α * n β) by ring]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)

theorem tensorPart_smul_left (hc : c ≠ 0) : tensorPart (c • n) = tensorPart n := by
  simp only [tensorPart, scalarPart_smul_left n hc, vectorPart_smul_left n hc]

theorem longVec_smul_left (hc : c ≠ 0) : longVec (c • n) = longVec n :=
  LinearMap.ext fun V => funext fun α => by
    simp only [longVec_apply, dot_smul_left, nsq_smul_left, Pi.smul_apply, smul_eq_mul]
    rw [show c * dot n V / (c ^ 2 * nsq n) * (c * n α) =
      (c ^ 2 * (dot n V * n α)) / (c ^ 2 * nsq n) by ring,
      mul_div_mul_left _ _ (pow_ne_zero 2 hc)]
    ring

theorem transVec_smul_left (hc : c ≠ 0) : transVec (c • n) = transVec n := by
  simp only [transVec, longVec_smul_left n hc]

end ProjectAinos.SmoothGeometry.ScalarVectorTensor
