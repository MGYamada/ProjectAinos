/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.Electrodynamics.SphericalCavity

noncomputable section
open ProjectAinos.SpecialRelativity ProjectAinos.Electrodynamics
open ProjectAinos.Electrodynamics.CavityModes ProjectAinos.SpecialFunctions.Bessel

example : ℝ → Potential := sphereMode

example (k : ℝ) (x : Spacetime) : VacuumMaxwellAt (sphereMode k) x :=
  sphereMode_maxwell k x

example {k R : ℝ} (hk : 0 < k) (hR : 0 < R)
    (hz : sphericalJ 1 ((k*R : ℝ) : ℂ) = 0) (x : Spacetime)
    (hx : x 1^2+x 2^2+x 3^2=R^2) :
    (∀ i, electricField (fieldTensor (sphereMode k)) i x=0) ∧
      ∑ i : Fin 3, x i.succ*magneticField (fieldTensor (sphereMode k)) i x=0 :=
  sphereMode_wall hk hR hz x hx

example {R : ℝ} (hR : 0 < R) (A : ℝ) :
    ∃ k : ℝ, A < k ∧ 0 < k ∧ sphericalJ 1 ((k*R : ℝ) : ℂ)=0 ∧
      0 < magneticField (fieldTensor (sphereMode k)) 2 0 :=
  exists_sphereMode hR A
