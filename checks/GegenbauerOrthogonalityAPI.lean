/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SpecialFunctions.GegenbauerOrthogonality

/-! Public consumers of the orthogonality of the Gegenbauer polynomials in the polar angle
(the radial factors of the scalar harmonics of `S³`, Landau–Lifshitz, §115): Gegenbauer's
equation for the real profiles, the angular Wronskian and its derivative, orthogonality for
distinct degrees and positivity of the squared norms.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology

namespace ProjectAinos.SpecialFunctions.ClassicalPolynomial

open Polynomial Real

example : ℕ → ℕ → ℕ → ℝ → ℝ :=
  @angularWronskian

example : ∀ (l m m' : ℕ), angularWronskian l m m' π = 0 :=
  @angularWronskian_pi

example : ∀ (l m m' : ℕ), angularWronskian l m m' 0 = 0 :=
  @angularWronskian_zero

example : ∀ (l m : ℕ), ContDiff ℝ ∞ (gegenbauerReal l m) :=
  @contDiff_gegenbauerReal

example : ∀ (p : ℂ[X]), ContDiff ℝ ∞ (realEval p) :=
  @contDiff_realEval

example : ∀ (l m : ℕ), Continuous (gegenbauerReal l m) :=
  @continuous_gegenbauerReal

example : ∀ (p : ℂ[X]), Continuous (realEval p) :=
  @continuous_realEval

example : ℕ → ℕ → ℝ :=
  @gegenbauerEigen

example : ∀ (l : ℕ), Injective (gegenbauerEigen l) :=
  @gegenbauerEigen_injective

example : ℕ → ℕ → ℝ → ℝ :=
  @gegenbauerReal

example : ∀ (l m : ℕ), gegenbauerReal l m = realEval (gegenbauer (↑l + 1) m) :=
  @gegenbauerReal_eq

example : ∀ (l m : ℕ) (s : ℝ),
    have p := gegenbauer (↑l + 1) m;
    (1 - s ^ 2) * realEval (derivative (derivative p)) s -
          (2 * ↑l + 3) * s * realEval (derivative p) s +
        ↑m * (↑m + 2 * ↑l + 2) * realEval p s =
      0 :=
  @gegenbauerReal_equation

example : ∀ (l m : ℕ), 0 < gegenbauerReal l m 1 :=
  @gegenbauerReal_one_pos

example : ∀ (l m m' : ℕ) (θ : ℝ),
    HasDerivAt (angularWronskian l m m')
      ((gegenbauerEigen l m' - gegenbauerEigen l m) * sin θ ^ (2 * l + 2) *
        (gegenbauerReal l m (cos θ) * gegenbauerReal l m' (cos θ)))
      θ :=
  @hasDerivAt_angularWronskian

example : ∀ (p : ℂ[X]) (s : ℝ), HasDerivAt (realEval p) (realEval (derivative p) s) s :=
  @hasDerivAt_realEval

example : ∀ (l : ℕ) {m m' : ℕ},
    m ≠ m' →
      ∫ (θ : ℝ) in 0..π,
          gegenbauerReal l m (cos θ) * gegenbauerReal l m' (cos θ) * sin θ ^ (2 * l + 2) =
        0 :=
  @integral_gegenbauerReal_mul_eq_zero

example : ∀ (l m : ℕ),
    0 <
      ∫ (θ : ℝ) in 0..π,
        gegenbauerReal l m (cos θ) * gegenbauerReal l m (cos θ) * sin θ ^ (2 * l + 2) :=
  @integral_gegenbauerReal_sq_pos

example : ℂ[X] → ℝ → ℝ :=
  @realEval

end ProjectAinos.SpecialFunctions.ClassicalPolynomial
