/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.HyperbolicRadial

noncomputable section
open Set ProjectAinos.SpecialFunctions.Hyperbolic
open scoped ContDiff
example : ℝ → ℝ → ℝ := zonalProfile

example (k : ℝ) : ∃ f : ℝ → ℝ, (∀ s ≥ 1, ContDiffAt ℝ ∞ f s) ∧ f 1=1 ∧
    ∀ r : ℝ, 0 < r → f (Real.cosh r)=(if k=0 then r else Real.sin (k*r)/k)/Real.sinh r :=
  exists_zonalProfile k

example (k : ℝ) {s : ℝ} (hs : 1 ≤ s) : ContDiffAt ℝ ∞ (zonalProfile k) s :=
  smooth_zonalProfile k hs

example (k : ℝ) : zonalProfile k 1=1 := zonalProfile_one k

example (k : ℝ) {r : ℝ} (hr : 0 < r) : zonalProfile k (Real.cosh r)=
    (if k=0 then r else Real.sin (k*r)/k)/Real.sinh r := zonalProfile_cosh k hr

example (k : ℝ) : ambientProfile k 0 1=1 := zonalProfile_one k

example (k : ℝ) (l : ℕ) {s : ℝ} (hs : 1 ≤ s) : ContDiffAt ℝ ∞ (ambientProfile k l) s :=
  smooth_ambientProfile_at k l hs

example : ℝ → ℕ → ℝ → ℝ := ambientProfile

example (k : ℝ) (l : ℕ) : ContDiffOn ℝ ∞ (ambientProfile k l) (Ioi 1) :=
  smooth_ambientProfile k l

example (k : ℝ) (l : ℕ) {r : ℝ} (hr : 0 < r) :
    harmonic l k r = ((Real.sinh r^l*ambientProfile k l (Real.cosh r) : ℝ) : ℂ) :=
  harmonic_eq_ambient k l hr

example (k : ℝ) (l : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    let F := ambientProfile k l
    (s^2-1)*deriv (deriv F) s+(2*l+3)*s*deriv F s+
      ((l : ℝ)*(l+2)+1+k^2)*F s=0 :=
  ambient_equation k l hs
