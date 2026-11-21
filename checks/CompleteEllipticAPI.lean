/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.CompleteElliptic

noncomputable section
open scoped Real
open ProjectAinos.SpecialFunctions.Elliptic ProjectAinos.SpecialFunctions.JacobiElliptic

example : ℝ → ℝ := K
example : ℝ → ℝ := E

example : K 0 = π/2 ∧ E 0 = π/2 :=
  zero

example {k : ℝ} (hk : k^2 < 1) : am k (K k) = π/2 :=
  am_K hk

example {k : ℝ} (hk : k^2 < 1) : halfPeriod k = 2*K k :=
  halfPeriod_eq hk

example {k : ℝ} (hk : k^2 < 1) : k*deriv E k = E k-K k :=
  deriv_E hk

example {k : ℝ} (hk : k^2 < 1) : k*(1-k^2)*deriv K k = E k-(1-k^2)*K k :=
  deriv_K hk
