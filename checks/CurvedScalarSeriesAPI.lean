/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.CurvedScalarSeries
import ProjectAinos.GeneralRelativity.CurvedScalarUniqueness

/-! Public consumers of the expansions of curved scalar perturbations in separated modes
(Landau–Lifshitz, §115, closed and open universes in the longitudinal gauge): the scalar system,
series converging with two derivatives and term-by-term differentiation, families of separated
modes, the equivalence of the scalar system of an expansion with the evolution equations of its
modes under unique coefficients, the uniqueness of the coefficients of the closed harmonics of
`S³`, and finite expansions.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

universe u_1 u_2

open Set Filter Function MeasureTheory
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.CurvedPerturbation

open SmoothGeometry CoordinateMetric FLRW IsotropicRicci CosmologicalModels
open ProjectAinos.SpecialFunctions ProjectAinos.SpecialFunctions.SphericalHarmonics
  ProjectAinos.SpecialFunctions.HarmonicPolynomial ProjectAinos.SpecialFunctions.ClassicalPolynomial

example : {ι : Type u_1} → Set (MinkowskiModel 3) → (ι → MinkowskiModel 3 → ℝ) → Prop :=
  @HasUniqueCoefficients

example : {ι : Type u_1} → Set (MinkowskiModel 3) → (ι → MinkowskiModel 3 → ℝ) → Prop :=
  @IsC2Series

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsC2Series U f →
      ∀ {y : MinkowskiModel 3}, y ∈ U → ∀ (i : ι), DifferentiableAt ℝ (fderiv ℝ (f i)) y :=
  @IsC2Series.differentiableAt_fderiv

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsC2Series U f →
      ∀ {y : MinkowskiModel 3},
        y ∈ U →
          (fderiv ℝ fun (w : MinkowskiModel 3) => ∑' (i : ι), f i w) =ᶠ[𝓝 y]
            fun (w : MinkowskiModel 3) => ∑' (i : ι), fderiv ℝ (f i) w :=
  @IsC2Series.fderiv_eventuallyEq

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsC2Series U f →
      ∀ {y : MinkowskiModel 3},
        y ∈ U →
          HasFDerivAt (fun (w : MinkowskiModel 3) => ∑' (i : ι), f i w)
            (∑' (i : ι), fderiv ℝ (f i) y) y :=
  @IsC2Series.hasFDerivAt

example : ∀ {ι : Type u_1} {f : ι → MinkowskiModel 3 → ℝ} {x : MinkowskiModel 3} {ε : ℝ}
    {b : ι → ℝ},
    Summable b →
      (∀ (i : ι),
          ∀ y ∈ Metric.ball x ε,
            DifferentiableAt ℝ (f i) y ∧
              DifferentiableAt ℝ (fderiv ℝ (f i)) y ∧
                ‖f i y‖ ≤ b i ∧ ‖fderiv ℝ (f i) y‖ ≤ b i ∧ ‖fderiv ℝ (fderiv ℝ (f i)) y‖ ≤ b i) →
        0 < ε →
          ∀ {z : MinkowskiModel 3},
            z ∈ Metric.ball x ε →
              HasFDerivAt (fun (w : MinkowskiModel 3) => ∑' (i : ι), f i w)
                (∑' (i : ι), fderiv ℝ (f i) z) z :=
  @IsC2Series.hasFDerivAt_of_mem

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsC2Series U f →
      ∀ {y : MinkowskiModel 3},
        y ∈ U →
          ∀ (v : MinkowskiModel 3),
            (Summable fun (i : ι) =>
                (ContinuousLinearMap.apply ℝ ℝ) v ∘SL fderiv ℝ (fderiv ℝ (f i)) y) ∧
              HasFDerivAt
                (fun (z : MinkowskiModel 3) =>
                  (fderiv ℝ (fun (w : MinkowskiModel 3) => ∑' (i : ι), f i w) z) v)
                (∑' (i : ι), (ContinuousLinearMap.apply ℝ ℝ) v ∘SL fderiv ℝ (fderiv ℝ (f i)) y) y :=
  @IsC2Series.hasFDerivAt_part_tsum

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsC2Series U f →
      ∀ {y : MinkowskiModel 3},
        y ∈ U →
          ∀ (k : ℝ),
            HasSum (fun (i : ι) => spatialLaplacian k (f i) y)
              (spatialLaplacian k (fun (w : MinkowskiModel 3) => ∑' (i : ι), f i w) y) :=
  @IsC2Series.hasSum_spatialLaplacian

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ} [Finite ι],
    IsOpen U → (∀ (i : ι), ∀ x ∈ U, ContDiffAt ℝ 2 (f i) x) → IsC2Series U f :=
  @IsC2Series.of_finite

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsOpen U →
      ∀ (s : Finset ι),
        (∀ i ∉ s, f i = 0) → (∀ i ∈ s, ∀ x ∈ U, ContDiffAt ℝ 2 (f i) x) → IsC2Series U f :=
  @IsC2Series.of_finite_support

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsC2Series U f →
      ∀ {y : MinkowskiModel 3},
        y ∈ U →
          ∀ (j : Fin 4),
            part (fun (w : MinkowskiModel 3) => ∑' (i : ι), f i w) j y =
              ∑' (i : ι), part (f i) j y :=
  @IsC2Series.part_tsum

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsC2Series U f →
      ∀ {y : MinkowskiModel 3},
        y ∈ U →
          ∀ (i : ι) (a c : Fin 4),
            secondPartial (f i) y a c =
              ((fderiv ℝ (fderiv ℝ (f i)) y) (Pi.single a 1)) (Pi.single c 1) :=
  @IsC2Series.secondPartial_eq

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsC2Series U f →
      ∀ {y : MinkowskiModel 3},
        y ∈ U →
          ∀ (a c : Fin 4),
            secondPartial (fun (w : MinkowskiModel 3) => ∑' (i : ι), f i w) y a c =
              ∑' (i : ι), secondPartial (f i) y a c :=
  @IsC2Series.secondPartial_tsum

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsC2Series U f → ∀ {y : MinkowskiModel 3}, y ∈ U → Summable fun (i : ι) => f i y :=
  @IsC2Series.summable

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsC2Series U f → ∀ {y : MinkowskiModel 3}, y ∈ U → Summable fun (i : ι) => fderiv ℝ (f i) y :=
  @IsC2Series.summable_fderiv

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsC2Series U f →
      ∀ {y : MinkowskiModel 3}, y ∈ U → ∀ (j : Fin 4), Summable fun (i : ι) => part (f i) j y :=
  @IsC2Series.summable_part

example : ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)} {f : ι → MinkowskiModel 3 → ℝ},
    IsC2Series U f →
      ∀ {y : MinkowskiModel 3},
        y ∈ U → ∀ (a c : Fin 4), Summable fun (i : ι) => secondPartial (f i) y a c :=
  @IsC2Series.summable_secondPartial

example : {ι : Type u_1} → Data → (ι → ℝ → ℝ) → (ι → MinkowskiModel 3 → ℝ) → (ι → ℝ) → Prop :=
  @IsModeFamily

example : ∀ {ι : Type u_1} {D : Data} {φ : ι → ℝ → ℝ} {Q : ι → MinkowskiModel 3 → ℝ} {q : ι → ℝ},
    IsModeFamily D φ Q q →
      ∀ {x : MinkowskiModel 3},
        x ∈ domain D →
          ∀ (i : ι),
            part (separated (φ i) (Q i)) 0 x = deriv (φ i) (x 0) * Q i x ∧
              secondPartial (separated (φ i) (Q i)) x 0 0 = deriv (deriv (φ i)) (x 0) * Q i x ∧
                (∀ (j : Fin 4),
                    j ≠ 0 →
                      secondPartial (separated (φ i) (Q i)) x j 0 =
                        deriv (φ i) (x 0) * part (Q i) j x) ∧
                  (∀ (j : Fin 4),
                      j ≠ 0 → part (separated (φ i) (Q i)) j x = φ i (x 0) * part (Q i) j x) ∧
                    spatialLaplacian D.k (separated (φ i) (Q i)) x = -q i * (φ i (x 0) * Q i x) :=
  @IsModeFamily.jets

example : Data →
    ℝ →
      (ℝ → ℝ) →
        (MinkowskiModel 3 → ℝ) →
          (MinkowskiModel 3 → ℝ) → (MinkowskiModel 3 → Fin 4 → ℝ) → MinkowskiModel 3 → Prop :=
  @ScalarSystemAt

example : Data → (ℝ → ℝ) → ℝ → ℝ :=
  @evolutionResidual

example : ∀ {D : Data} (φ : ℝ → ℝ) (t : ℝ), Evolution D φ t ↔ evolutionResidual D φ t = 0 :=
  @evolution_iff

example : ∀ {ι : Type u_1} {D : Data} {κ : ℝ} {ρ : ℝ → ℝ} {φ : ι → ℝ → ℝ}
    {Q : ι → MinkowskiModel 3 → ℝ} {q : ι → ℝ},
    IsModeFamily D φ Q q →
      (IsC2Series ↑(domain D) fun (i : ι) => separated (φ i) (Q i)) →
        ∀ {t : ℝ},
          κ * ρ t ≠ 0 →
            HasUniqueCoefficients (slice D t) Q →
              (∃ (M : ι → ℝ),
                  Summable M ∧
                    ∀ (i : ι), ∀ y ∈ slice D t, |evolutionResidual D (φ i) t * Q i y| ≤ M i) →
                (∀ y ∈ slice D t,
                    ScalarSystemAt D κ ρ
                      (fun (y : MinkowskiModel 3) => ∑' (i : ι), separated (φ i) (Q i) y)
                      (fun (y : MinkowskiModel 3) => ∑' (i : ι), contrast D κ ρ (φ i) (q i) (Q i) y)
                      (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                        ∑' (i : ι), covelocity D κ ρ (φ i) (Q i) y j)
                      y) →
                  ∀ (i : ι), Evolution D (φ i) t :=
  @evolution_of_scalarSystemAt

example : ∀ {D : Data},
    D.N = D.a →
      ∀ {κ : ℝ} {ρ : ℝ → ℝ},
        (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0) →
          ∀ {x : MinkowskiModel 3},
            x ∈ domain D →
              ∀ {u : MinkowskiModel 3 → ℝ},
                ContDiffAt ℝ ∞ u x →
                  ∀ (δ : MinkowskiModel 3 → ℝ) (V : MinkowskiModel 3 → Fin 4 → ℝ),
                    LinearizedDustAt D κ ρ u δ V x ↔ ScalarSystemAt D κ ρ u δ V x :=
  @linearizedDustAt_iff_scalarSystemAt

example : ∀ {ι : Type u_1} {D : Data} {κ : ℝ} {ρ : ℝ → ℝ} {φ : ι → ℝ → ℝ}
    {Q : ι → MinkowskiModel 3 → ℝ} {q : ι → ℝ},
    D.N = D.a →
      (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0) →
        IsModeFamily D φ Q q →
          (IsC2Series ↑(domain D) fun (i : ι) => separated (φ i) (Q i)) →
            ∀ {x : MinkowskiModel 3},
              x ∈ domain D →
                κ * ρ (x 0) ≠ 0 →
                  ContDiffAt ℝ ∞ (fun (y : MinkowskiModel 3) => ∑' (i : ι), separated (φ i) (Q i) y)
                      x →
                    (∀ (i : ι), Evolution D (φ i) (x 0)) →
                      LinearizedDustAt D κ ρ
                        (fun (y : MinkowskiModel 3) => ∑' (i : ι), separated (φ i) (Q i) y)
                        (fun (y : MinkowskiModel 3) =>
                          ∑' (i : ι), contrast D κ ρ (φ i) (q i) (Q i) y)
                        (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                          ∑' (i : ι), covelocity D κ ρ (φ i) (Q i) y j)
                        x :=
  @linearizedDustAt_tsum

example : ∀ {φ : ℝ → ℝ} {Q : MinkowskiModel 3 → ℝ} {x : MinkowskiModel 3},
    DifferentiableAt ℝ φ (x 0) →
      DifferentiableAt ℝ Q x →
        ∀ (i : Fin 4),
          part (separated φ Q) i x =
            (if i = 0 then deriv φ (x 0) * Q x else 0) + φ (x 0) * part Q i x :=
  @part_separated

example : ∀ {ι : Type u_1} {D : Data} {κ : ℝ} {ρ : ℝ → ℝ} {φ : ι → ℝ → ℝ}
    {Q : ι → MinkowskiModel 3 → ℝ} {q : ι → ℝ},
    IsModeFamily D φ Q q →
      (IsC2Series ↑(domain D) fun (i : ι) => separated (φ i) (Q i)) →
        ∀ {t : ℝ},
          κ * ρ t ≠ 0 →
            HasUniqueCoefficients (slice D t) Q →
              (∃ (M : ι → ℝ),
                  Summable M ∧
                    ∀ (i : ι), ∀ y ∈ slice D t, |evolutionResidual D (φ i) t * Q i y| ≤ M i) →
                ((∀ y ∈ slice D t,
                    ScalarSystemAt D κ ρ
                      (fun (y : MinkowskiModel 3) => ∑' (i : ι), separated (φ i) (Q i) y)
                      (fun (y : MinkowskiModel 3) => ∑' (i : ι), contrast D κ ρ (φ i) (q i) (Q i) y)
                      (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                        ∑' (i : ι), covelocity D κ ρ (φ i) (Q i) y j)
                      y) ↔
                  ∀ (i : ι), Evolution D (φ i) t) :=
  @scalarSystemAt_slice_iff

example : ∀ {ι : Type u_1} {D : Data} {κ : ℝ} {ρ : ℝ → ℝ} {φ : ι → ℝ → ℝ}
    {Q : ι → MinkowskiModel 3 → ℝ} {q : ι → ℝ},
    IsModeFamily D φ Q q →
      (IsC2Series ↑(domain D) fun (i : ι) => separated (φ i) (Q i)) →
        ∀ {x : MinkowskiModel 3},
          x ∈ domain D →
            κ * ρ (x 0) ≠ 0 →
              (∀ (i : ι), Evolution D (φ i) (x 0)) →
                ScalarSystemAt D κ ρ
                  (fun (y : MinkowskiModel 3) => ∑' (i : ι), separated (φ i) (Q i) y)
                  (fun (y : MinkowskiModel 3) => ∑' (i : ι), contrast D κ ρ (φ i) (q i) (Q i) y)
                  (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                    ∑' (i : ι), covelocity D κ ρ (φ i) (Q i) y j)
                  x :=
  @scalarSystemAt_tsum

example : ∀ {ι : Type u_1} {D : Data} {κ : ℝ} {ρ : ℝ → ℝ} {φ : ι → ℝ → ℝ}
    {Q : ι → MinkowskiModel 3 → ℝ} {q : ι → ℝ},
    IsModeFamily D φ Q q →
      (IsC2Series ↑(domain D) fun (i : ι) => separated (φ i) (Q i)) →
        ∀ {x : MinkowskiModel 3},
          x ∈ domain D →
            κ * ρ (x 0) ≠ 0 →
              (ScalarSystemAt D κ ρ
                  (fun (y : MinkowskiModel 3) => ∑' (i : ι), separated (φ i) (Q i) y)
                  (fun (y : MinkowskiModel 3) => ∑' (i : ι), contrast D κ ρ (φ i) (q i) (Q i) y)
                  (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                    ∑' (i : ι), covelocity D κ ρ (φ i) (Q i) y j)
                  x ↔
                ∑' (i : ι), evolutionResidual D (φ i) (x 0) * Q i x = 0) :=
  @scalarSystemAt_tsum_iff

example : ∀ {φ : ℝ → ℝ} {Q : MinkowskiModel 3 → ℝ} {x : MinkowskiModel 3},
    ContDiffAt ℝ ∞ φ (x 0) →
      ContDiffAt ℝ ∞ Q x →
        (∀ᶠ (y : MinkowskiModel 3) in 𝓝 x, part Q 0 y = 0) →
          part (separated φ Q) 0 x = deriv φ (x 0) * Q x ∧
            secondPartial (separated φ Q) x 0 0 = deriv (deriv φ) (x 0) * Q x ∧
              (∀ (i : Fin 4),
                  i ≠ 0 → secondPartial (separated φ Q) x i 0 = deriv φ (x 0) * part Q i x) ∧
                (∀ (i : Fin 4), i ≠ 0 → part (separated φ Q) i x = φ (x 0) * part Q i x) ∧
                  ∀ (k : ℝ),
                    spatialLaplacian k (separated φ Q) x = φ (x 0) * spatialLaplacian k Q x :=
  @separated_jets

example : Data → ℝ → Set (MinkowskiModel 3) :=
  @slice

example : Type :=
  @ClosedIndex

example : Data → (ℝ → ℝ) → Prop :=
  @IsDustTime

example : ∀ {D : Data}, Continuous D.a → ∀ {φ : ℝ → ℝ}, IsDustTime D φ → ContDiffOn ℝ ∞ φ D.I :=
  @IsDustTime.contDiffOn

example : ∀ {D : Data},
    D.N = D.a →
      ∀ {κ : ℝ} {ρ : ℝ → ℝ},
        (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0) →
          Continuous D.a → ∀ {φ : ℝ → ℝ}, IsDustTime D φ → ∀ {t : ℝ}, t ∈ D.I → Evolution D φ t :=
  @IsDustTime.evolution

example : ℝ → ℝ → EuclideanSpace ℝ (Fin 3) → MinkowskiModel 3 :=
  @chartPoint

example : ∀ (t r : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (j : Fin 3),
    chartPoint t r u j.succ = r * u.ofLp j :=
  @chartPoint_succ

example : ∀ (t r : ℝ) (u : EuclideanSpace ℝ (Fin 3)), chartPoint t r u 0 = t :=
  @chartPoint_zero

example : ℝ → ℝ :=
  @chartRadius

example : ∀ {θ : ℝ},
    θ ∈ Ioo 0 Real.pi →
      0 < chartRadius θ ∧
        chartRadius θ / (1 + chartRadius θ ^ 2 / 4) = Real.sin θ ∧
          2 / (1 + chartRadius θ ^ 2 / 4) - 1 = Real.cos θ :=
  @chartRadius_spec

example : (i : ClosedIndex) → ↥(harmonics 3 i.fst.1) :=
  @closedBasis

example : ClosedIndex → MinkowskiModel 3 → ℝ :=
  @closedBasisHarmonic

example : ∀ {l : ℕ} (p : ↥(harmonics 3 l)) (m : ℕ) (t r : ℝ) (u : ↑(UnitSphere 3)),
    closedHarmonic p m (chartPoint t r ↑u) =
      (r / (1 + r ^ 2 / 4)) ^ l * gegenbauerReal l m (2 / (1 + r ^ 2 / 4) - 1) *
        (SphericalHarmonics.restrict 3 l) (↑p) u :=
  @closedHarmonic_chartPoint

example : ∀ (P : (lm : ℕ × ℕ) → ↥(harmonics 3 lm.1)) {M : ℕ × ℕ → ℝ},
    Summable M →
      ∀ {t : ℝ},
        (∀ (lm : ℕ × ℕ) (x : MinkowskiModel 3), x 0 = t → |closedHarmonic (P lm) lm.2 x| ≤ M lm) →
          (∀ (x : MinkowskiModel 3), x 0 = t → ∑' (lm : ℕ × ℕ), closedHarmonic (P lm) lm.2 x = 0) →
            ∀ (lm₀ : ℕ × ℕ), P lm₀ = 0 :=
  @closedHarmonic_coeff_eq_zero

example : ∀ {l : ℕ} (m : ℕ) {κ : Type u_2} (s : Finset κ) (c : κ → ℝ) (b : κ → ↥(harmonics 3 l))
    (x : MinkowskiModel 3),
    closedHarmonic (∑ j ∈ s, c j • b j) m x = ∑ j ∈ s, c j * closedHarmonic (b j) m x :=
  @closedHarmonic_sum

example : ∀ {A κ : ℝ} (hA : 0 < A),
    0 < κ →
      ∀ (s : Finset ClosedIndex) {φ : ClosedIndex → ℝ → ℝ},
        (∀ i ∉ s, φ i = 0) →
          (∀ i ∈ s, ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) →
            ∀ {t : ℝ},
              t ∈ (closedDust A hA).I →
                ((∀ y ∈ slice (closedDust A hA) t,
                    ScalarSystemAt (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
                      (fun (y : MinkowskiModel 3) =>
                        ∑' (i : ClosedIndex), separated (φ i) (closedBasisHarmonic i) y)
                      (fun (y : MinkowskiModel 3) =>
                        ∑' (i : ClosedIndex),
                          contrast (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
                            (φ i) (↑(i.fst.1 + i.fst.2) * (↑i.fst.1 + ↑i.fst.2 + 2))
                            (closedBasisHarmonic i) y)
                      (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                        ∑' (i : ClosedIndex),
                          covelocity (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
                            (φ i) (closedBasisHarmonic i) y j)
                      y) ↔
                  ∀ (i : ClosedIndex), Evolution (closedDust A hA) (φ i) t) :=
  @closed_finite_scalarSystemAt_slice_iff

example : ∀ {ι : Type u_1} {A κ : ℝ} (hA : 0 < A),
    0 < κ →
      ∀ (l : ι → ℕ) (p : (i : ι) → ↥(harmonics 3 (l i))) (m : ι → ℕ) {φ : ι → ℝ → ℝ},
        (∀ (i : ι), IsDustTime (closedDust A hA) (φ i)) →
          (IsC2Series ↑(domain (closedDust A hA)) fun (i : ι) =>
              separated (φ i) (closedHarmonic (p i) (m i))) →
            ∀ {x : MinkowskiModel 3},
              x ∈ domain (closedDust A hA) →
                ScalarSystemAt (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
                  (fun (y : MinkowskiModel 3) =>
                    ∑' (i : ι), separated (φ i) (closedHarmonic (p i) (m i)) y)
                  (fun (y : MinkowskiModel 3) =>
                    ∑' (i : ι),
                      contrast (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a) (φ i)
                        (↑(l i + m i) * (↑(l i) + ↑(m i) + 2)) (closedHarmonic (p i) (m i)) y)
                  (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                    ∑' (i : ι),
                      covelocity (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
                        (φ i) (closedHarmonic (p i) (m i)) y j)
                  x :=
  @closed_scalarSystemAt_dust

example : ∀ {A κ : ℝ} (hA : 0 < A),
    0 < κ →
      ∀ {φ : ClosedIndex → ℝ → ℝ},
        (∀ (i : ClosedIndex), ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) →
          (IsC2Series ↑(domain (closedDust A hA)) fun (i : ClosedIndex) =>
              separated (φ i) (closedBasisHarmonic i)) →
            ∀ {t : ℝ},
              t ∈ (closedDust A hA).I →
                (∃ (M : ClosedIndex → ℝ),
                    Summable M ∧
                      ∀ (i : ClosedIndex),
                        ∀ y ∈ slice (closedDust A hA) t,
                          |evolutionResidual (closedDust A hA) (φ i) t * closedBasisHarmonic i y| ≤
                            M i) →
                  ((∀ y ∈ slice (closedDust A hA) t,
                      ScalarSystemAt (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
                        (fun (y : MinkowskiModel 3) =>
                          ∑' (i : ClosedIndex), separated (φ i) (closedBasisHarmonic i) y)
                        (fun (y : MinkowskiModel 3) =>
                          ∑' (i : ClosedIndex),
                            contrast (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
                              (φ i) (↑(i.fst.1 + i.fst.2) * (↑i.fst.1 + ↑i.fst.2 + 2))
                              (closedBasisHarmonic i) y)
                        (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                          ∑' (i : ClosedIndex),
                            covelocity (closedDust A hA) κ
                              (dustDensity κ (6 * A) (closedDust A hA).a) (φ i)
                              (closedBasisHarmonic i) y j)
                        y) ↔
                    ∀ (i : ClosedIndex), Evolution (closedDust A hA) (φ i) t) :=
  @closed_scalarSystemAt_slice_iff

example : ∀ {A : ℝ} (hA : 0 < A), Continuous (closedDust A hA).a :=
  @continuous_closedDust_a

example : ∀ {A : ℝ} (hA : 0 < A), Continuous (openDust A hA).a :=
  @continuous_openDust_a

example : ∀ {l : ℕ} (p : ↥(harmonics 3 l)), Continuous ((SphericalHarmonics.restrict 3 l) ↑p) :=
  @continuous_restrict

example : ∀ {l : ℕ} (p : ↥(harmonics 3 l)) (m : ℕ),
    ∃ (C : ℝ), ∀ (x : MinkowskiModel 3), |closedHarmonic p m x| ≤ C :=
  @exists_bound_closedHarmonic

example : ∀ {l : ℕ} (p : ↥(harmonics 3 l)),
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (u : ↑(UnitSphere 3)), |(SphericalHarmonics.restrict 3 l) (↑p) u| ≤ C :=
  @exists_bound_restrict

example : ∀ (x : MinkowskiModel 3),
    ∃ (r : ℝ), 0 ≤ r ∧ ∃ (u : ↑(UnitSphere 3)), chartPoint (x 0) r ↑u = x :=
  @exists_chartPoint

example : ∀ {A : ℝ} (hA : 0 < A) (s : Finset ClosedIndex) {φ : ClosedIndex → ℝ → ℝ},
    (∀ i ∉ s, φ i = 0) →
      ∀ (t : ℝ),
        ∃ (M : ClosedIndex → ℝ),
          Summable M ∧
            ∀ (i : ClosedIndex),
              ∀ y ∈ slice (closedDust A hA) t,
                |evolutionResidual (closedDust A hA) (φ i) t * closedBasisHarmonic i y| ≤ M i :=
  @exists_residual_bound_finite

example : (l : ℕ) → Module.Basis (Fin (2 * l + 1)) ℝ ↥(harmonics 3 l) :=
  @harmonicsBasis

example : ∀ {A : ℝ} (hA : 0 < A) {t : ℝ},
    t ∈ (closedDust A hA).I →
      HasUniqueCoefficients (slice (closedDust A hA) t) closedBasisHarmonic :=
  @hasUniqueCoefficients_closed

example : ∀ {A : ℝ} (hA : 0 < A) (s : Finset ClosedIndex) {φ : ClosedIndex → ℝ → ℝ},
    (∀ i ∉ s, φ i = 0) →
      (∀ i ∈ s, ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) →
        IsC2Series ↑(domain (closedDust A hA)) fun (i : ClosedIndex) =>
          separated (φ i) (closedBasisHarmonic i) :=
  @isC2Series_closedBasis_finite

example : ∀ {ι : Type u_1} {A : ℝ} (hA : 0 < A) (l : ι → ℕ) (p : (i : ι) → ↥(harmonics 3 (l i)))
    (m : ι → ℕ) {φ : ι → ℝ → ℝ},
    (∀ (i : ι), ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) →
      IsModeFamily (closedDust A hA) φ (fun (i : ι) => closedHarmonic (p i) (m i)) fun (i : ι) =>
        ↑(l i + m i) * (↑(l i) + ↑(m i) + 2) :=
  @isModeFamily_closed

example : ∀ {A : ℝ} (hA : 0 < A) {φ : ClosedIndex → ℝ → ℝ},
    (∀ (i : ClosedIndex), ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) →
      IsModeFamily (closedDust A hA) φ closedBasisHarmonic fun (i : ClosedIndex) =>
        ↑(i.fst.1 + i.fst.2) * (↑i.fst.1 + ↑i.fst.2 + 2) :=
  @isModeFamily_closedBasis

example : ∀ {ι : Type u_1} {A : ℝ} (hA : 0 < A) (l : ι → ℕ) (p : (i : ι) → ↥(harmonics 3 (l i)))
    (ξ : ι → ℝ) {φ : ι → ℝ → ℝ},
    (∀ (i : ι), ContDiffOn ℝ ∞ (φ i) (openDust A hA).I) →
      IsModeFamily (openDust A hA) φ (fun (i : ι) => openHarmonic (p i) (ξ i)) fun (i : ι) =>
        1 + ξ i ^ 2 :=
  @isModeFamily_open

example : ∀ {ι : Type u_1} {A κ : ℝ} (hA : 0 < A),
    0 < κ →
      ∀ (l : ι → ℕ) (p : (i : ι) → ↥(harmonics 3 (l i))) (ξ : ι → ℝ) {φ : ι → ℝ → ℝ},
        (∀ (i : ι), IsDustTime (openDust A hA) (φ i)) →
          (IsC2Series ↑(domain (openDust A hA)) fun (i : ι) =>
              separated (φ i) (openHarmonic (p i) (ξ i))) →
            ∀ {x : MinkowskiModel 3},
              x ∈ domain (openDust A hA) →
                ScalarSystemAt (openDust A hA) κ (dustDensity κ (6 * A) (openDust A hA).a)
                  (fun (y : MinkowskiModel 3) =>
                    ∑' (i : ι), separated (φ i) (openHarmonic (p i) (ξ i)) y)
                  (fun (y : MinkowskiModel 3) =>
                    ∑' (i : ι),
                      contrast (openDust A hA) κ (dustDensity κ (6 * A) (openDust A hA).a) (φ i)
                        (1 + ξ i ^ 2) (openHarmonic (p i) (ξ i)) y)
                  (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                    ∑' (i : ι),
                      covelocity (openDust A hA) κ (dustDensity κ (6 * A) (openDust A hA).a) (φ i)
                        (openHarmonic (p i) (ξ i)) y j)
                  x :=
  @open_scalarSystemAt_dust

example : ∀ (t r : ℝ) (u : ↑(UnitSphere 3)), psi 1 (chartPoint t r ↑u) = 1 + r ^ 2 / 4 :=
  @psi_chartPoint

example : ∀ {l : ℕ} (p : ↥(harmonics 3 l)), (SphericalHarmonics.restrict 3 l) ↑p ∈ space 3 l :=
  @restrict_mem_space

example : Measure ↑(UnitSphere 3) :=
  @sphereMeasure

example : ∀ (u : ↑(UnitSphere 3)), ∑ j : Fin 3, (u : EuclideanSpace ℝ (Fin 3)).ofLp j ^ 2 = 1 :=
  @sum_sq_of_mem_sphere

end ProjectAinos.GeneralRelativity.CurvedPerturbation
