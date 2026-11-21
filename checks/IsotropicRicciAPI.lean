/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SmoothGeometry.Lorentzian.IsotropicRicci

noncomputable section
open ProjectAinos.SmoothGeometry ProjectAinos.SmoothGeometry.CoordinateMetric
open ProjectAinos.SmoothGeometry.IsotropicRicci
open scoped ContDiff
local notation "E" => MinkowskiModel 3

example : (E → ℝ) → Fin 4 → E → ℝ := part
example : (E → ℝ) → (E → ℝ) → E → Matrix (Fin 4) (Fin 4) ℝ := metric
example : (E → ℝ) → (E → ℝ) → E → Fin 4 → Fin 4 → ℝ := ricciTable

example {f s : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hs : ContDiffAt ℝ ∞ s x) (i j : Fin 4) :
    ricciOf (metric f s) x i j = ricciTable f s x i j :=
  ricci_eq hf hs i j
