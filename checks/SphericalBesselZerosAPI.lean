/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.SphericalBesselZeros

noncomputable section
open Set Complex ProjectAinos.SpecialFunctions.Bessel



example (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (h₁ : sphericalJ n a = 0) (h₂ : sphericalJ n b = 0) :
    ∃ c ∈ Ioo a b, sphericalJ (n+1) c = 0 :=
  sphericalJ_zero_between n ha hab h₁ h₂

example (n : ℕ) (R : ℝ) :
    ∃ x : ℝ, R < x ∧ 0 < x ∧ sphericalJ n x = 0 :=
  sphericalJ_zeros_unbounded n R

example (n : ℕ) {z : ℂ} (hz : z ≠ 0) (h : sphericalJ n z = 0) :
    deriv (sphericalJ n) z ≠ 0 :=
  sphericalJ_simple n hz h

example {k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hz : sphericalJ 1 ((k*r : ℝ) : ℂ) = 0) : radialProfile (5/2) k (r^2) = 0 :=
  radialProfile_dipole_zero hk hr hz
