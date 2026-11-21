/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SpecialFunctions.GegenbauerCompleteness
import ProjectAinos.SpecialFunctions.SphericalPolarCompleteness
import ProjectAinos.SpecialFunctions.SineTransformUniqueness
import ProjectAinos.GeneralRelativity.CurvedScalarCompleteness
import ProjectAinos.GeneralRelativity.CurvedOpenSynthesis

/-! Public consumers of the completeness of the scalar harmonics and the expansion of general
data (Landau–Lifshitz, §115, closed and open universes in the longitudinal gauge): completeness of
the Gegenbauer profiles in the polar angle, polar co-ordinates and completeness of the spherical
harmonics on `S²`, uniqueness for the Fourier sine transform, the chart measure of `S³`, the
orthogonality and completeness of the closed harmonics, expandable closed data and their scalar
system, syntheses converging with two derivatives, and the scalar system of zonal syntheses on
`H³`.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

universe u_1 u_2

open Set Filter Function MeasureTheory Real
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.CurvedPerturbation

open SmoothGeometry CoordinateMetric FLRW IsotropicRicci CosmologicalModels
open ProjectAinos.SpecialFunctions ProjectAinos.SpecialFunctions.SphericalHarmonics
  ProjectAinos.SpecialFunctions.HarmonicPolynomial ProjectAinos.SpecialFunctions.ClassicalPolynomial
  ProjectAinos.SpecialFunctions.SineTransform

/-! ProjectAinos.SpecialFunctions.GegenbauerCompleteness -/

example :
    ∀ (l n : ℕ), 0 < gegenbauerLeadReal l n :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.gegenbauerLeadReal_pos

example :
    ∀ (l m k : ℕ), (gegenbauerRealPoly l m).coeff k = ((gegenbauer (↑l + 1) m).coeff k).re :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.gegenbauerRealPoly_coeff

example :
    ℕ → ℕ → Polynomial ℝ :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.gegenbauerRealPoly

example :
    ∀ {f : ℝ → ℝ},
      ContinuousOn f (Ioo 0 π) →
        ∀ {B : ℝ}, (∀ θ ∈ Ioo 0 π, |f θ| ≤ B) → IntegrableOn f (Ioo 0 π) volume :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.integrableOn_Ioo_of_bounded

example :
    ∀ (l m : ℕ), (gegenbauerRealPoly l m).natDegree ≤ m :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.gegenbauerRealPoly_natDegree_le

example :
    ∀ (l n : ℕ), gegenbauerLead (↑l + 1) n = ↑(gegenbauerLeadReal l n) :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.gegenbauerLead_eq

example :
    ∀ (l N : ℕ) (P : Polynomial ℝ),
      P.natDegree ≤ N →
        ∃ (c : ℕ → ℝ),
          ∀ (s : ℝ),
            Polynomial.eval s P = ∑ m ∈ Finset.range (N + 1), c m * gegenbauerReal l m s :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.exists_gegenbauer_combination

example :
    ℕ → ℕ → ℝ :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.gegenbauerLeadReal

example :
    ℂ → ℕ → ℂ :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.gegenbauerLead

example :
    ∀ (l m : ℕ), (gegenbauerRealPoly l m).coeff m = gegenbauerLeadReal l m :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.gegenbauerRealPoly_coeff_self

example :
    ∀ (l : ℂ) (n : ℕ),
      (gegenbauer l n).coeff n = gegenbauerLead l n ∧
        ∀ (k : ℕ), n < k → (gegenbauer l n).coeff k = 0 :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.gegenbauer_coeff

example :
    ∀ (l m : ℕ) (s : ℝ), gegenbauerReal l m s = Polynomial.eval s (gegenbauerRealPoly l m) :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.gegenbauerReal_eq_eval

example :
    ∀ (l : ℕ) {f : ℝ → ℝ}, ContinuousOn f (Ioo 0 π) → ∀ {B : ℝ}, (∀ θ ∈ Ioo 0 π, |f θ| ≤ B) →
      (∀ (m : ℕ), ∫ θ in Ioo 0 π, f θ * sin θ ^ (l + 2) * gegenbauerReal l m (cos θ) = 0) →
        ∀ θ ∈ Ioo 0 π, f θ = 0 :=
  @ProjectAinos.SpecialFunctions.ClassicalPolynomial.eq_zero_of_integral_gegenbauer

/-! ProjectAinos.SpecialFunctions.SphericalPolarCompleteness -/

example :
    ∀ (F : EuclideanSpace ℝ (Fin 3) → ℝ),
      Integrable F volume →
        ∫ (x : EuclideanSpace ℝ (Fin 3)), F x =
          ∫ (r : ℝ) in Ioi 0, r ^ 2 * ∫ (u : ↑(UnitSphere 3)), F (r • ↑u) ∂surfaceMeasure 3 :=
  @ProjectAinos.SpecialFunctions.SphericalHarmonics.integral_eq_integral_Ioi_sphere

example :
    ∀ {f : ↑(UnitSphere 3) → ℝ}, Continuous f →
      (∀ (l : ℕ) (p : ↥(harmonics 3 l)),
        ∫ (u : ↑(UnitSphere 3)), f u * restrict 3 l p.val u ∂surfaceMeasure 3 = 0) → f = 0 :=
  @ProjectAinos.SpecialFunctions.SphericalHarmonics.eq_zero_of_integral_mul_restrict

example :
    ∀ (f g h : C(↑(UnitSphere 3), ℝ)),
      |∫ (u : ↑(UnitSphere 3)), f u * g u ∂surfaceMeasure 3 -
            ∫ (u : ↑(UnitSphere 3)), f u * h u ∂surfaceMeasure 3| ≤
        ‖f‖ * ‖g - h‖ * (surfaceMeasure 3).real univ :=
  @ProjectAinos.SpecialFunctions.SphericalHarmonics.abs_integral_mul_sub_le

/-! ProjectAinos.SpecialFunctions.SineTransformUniqueness -/

example :
    ∀ (ξ ρ : ℝ), 0 < ξ → 0 ≤ ρ → |sin (ξ * ρ) / ξ| ≤ ρ :=
  @ProjectAinos.SpecialFunctions.SineTransform.abs_sin_mul_div_le

example :
    ∀ {f : ℝ → ℂ},
      Integrable f volume → (∀ (w : ℝ), FourierTransform.fourier f w = 0) → f =ᵐ[volume] 0 :=
  @ProjectAinos.SpecialFunctions.SineTransform.ae_eq_zero_of_fourier_eq_zero

example :
    ∀ {c : ℝ → ℝ},
      IntegrableOn c (Ioi 0) volume →
        (∀ (ρ : ℝ), 0 < ρ → ∫ (ξ : ℝ) in Ioi 0, c ξ * (sin (ξ * ρ) / ξ) = 0) →
          c =ᵐ[volume.restrict (Ioi 0)] 0 :=
  @ProjectAinos.SpecialFunctions.SineTransform.ae_eq_zero_of_integral_sin_div

/-! ProjectAinos.GeneralRelativity.CurvedScalarCompleteness -/

example :
    (l : ℕ) → Module.Basis (Fin (2 * l + 1)) ℝ ↥(harmonics 3 l) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.sphereModuleBasis

example :
    ∀ {A κ : ℝ} {hA : 0 < A},
      0 < κ →
        ∀ {u : MinkowskiModel 3 → ℝ},
          IsClosedExpandable A hA u →
            ∀ {t : ℝ},
              t ∈ (closedDust A hA).I →
                (∃ (M : ClosedIndex → ℝ),
                    Summable M ∧
                      ∀ (i : ClosedIndex),
                        ∀ y ∈ slice (closedDust A hA) t,
                          |evolutionResidual (closedDust A hA) (closedCoeff u i) t *
                                closedONHarmonic i y| ≤
                            M i) →
                  ((∀ y ∈ slice (closedDust A hA) t,
                      ScalarSystemAt (closedDust A hA) κ
                        (dustDensity κ (6 * A) (closedDust A hA).a) u
                        (fun (y : MinkowskiModel 3) =>
                          ∑' (i : ClosedIndex),
                            contrast (closedDust A hA) κ
                              (dustDensity κ (6 * A) (closedDust A hA).a) (closedCoeff u i)
                              (↑(i.fst.1 + i.fst.2) * (↑i.fst.1 + ↑i.fst.2 + 2))
                              (closedONHarmonic i) y)
                        (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                          ∑' (i : ClosedIndex),
                            covelocity (closedDust A hA) κ
                              (dustDensity κ (6 * A) (closedDust A hA).a) (closedCoeff u i)
                              (closedONHarmonic i) y j)
                        y) ↔
                    ∀ (i : ClosedIndex), Evolution (closedDust A hA) (closedCoeff u i) t) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsClosedExpandable.scalarSystemAt_slice_iff

example :
    (MinkowskiModel 3 → ℝ) → ℝ → {l : ℕ} → ↥(harmonics 3 l) → ℝ → ℝ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.angularCoeff

example :
    ∀ (i : ClosedIndex) (t : ℝ),
      Continuous fun (y : EuclideanSpace ℝ (Fin 3)) => closedONHarmonic i (slicePoint t y) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.continuous_closedONHarmonic_slice

example :
    ℝ → (MinkowskiModel 3 → ℝ) → (MinkowskiModel 3 → ℝ) → ℝ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.chartPair

example :
    ∀ {a : ClosedIndex → ℝ} {t : ℝ} {M : ClosedIndex → ℝ},
      Summable M →
        (∀ (i : ClosedIndex) (y : EuclideanSpace ℝ (Fin 3)),
            |a i * closedONHarmonic i (slicePoint t y)| ≤ M i) →
          ∀ (j : ClosedIndex),
            chartPair t
                (fun (x : MinkowskiModel 3) => ∑' (i : ClosedIndex), a i * closedONHarmonic i x)
                (closedONHarmonic j) =
              a j * closedNorm j.fst :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.chartPair_tsum

example :
    ∀ {t : ℝ} {f g : MinkowskiModel 3 → ℝ},
      (Continuous fun (y : EuclideanSpace ℝ (Fin 3)) => f (slicePoint t y)) →
        (Continuous fun (y : EuclideanSpace ℝ (Fin 3)) => g (slicePoint t y)) →
          ∀ {Bf Bg : ℝ},
            (∀ (y : EuclideanSpace ℝ (Fin 3)), |f (slicePoint t y)| ≤ Bf) →
              (∀ (y : EuclideanSpace ℝ (Fin 3)), |g (slicePoint t y)| ≤ Bg) →
                Integrable
                  (fun (y : EuclideanSpace ℝ (Fin 3)) =>
                    f (slicePoint t y) * g (slicePoint t y) * chartWeight y)
                  volume :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.integrable_chartPair

example :
    ∀ (l : ℕ) (j : Fin (2 * l + 1)),
      (representative 3 l) ((realBasis l) j) = (onSphere 3) ↑↑(sphereBasis l j) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.representative_realBasis

example :
    Integrable chartWeight volume :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.integrable_chartWeight

example :
    ∀ {a : ClosedIndex → ℝ} {t : ℝ} {M : ClosedIndex → ℝ},
      Summable M →
        (∀ (i : ClosedIndex) (y : EuclideanSpace ℝ (Fin 3)),
            |a i * closedONHarmonic i (slicePoint t y)| ≤ M i) →
          ∀ (y : EuclideanSpace ℝ (Fin 3)),
            |∑' (i : ClosedIndex), a i * closedONHarmonic i (slicePoint t y)| ≤
              ∑' (i : ClosedIndex), M i :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.abs_tsum_slice_le

example :
    ∀ {l : ℕ} (p : ↥(harmonics 3 l)) (m : ℕ), Continuous (closedHarmonic p m) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.continuous_closedHarmonic

example :
    ∀ {u : MinkowskiModel 3 → ℝ} {t : ℝ},
      (Continuous fun (y : EuclideanSpace ℝ (Fin 3)) => u (slicePoint t y)) →
        ∀ {B : ℝ},
          (∀ (y : EuclideanSpace ℝ (Fin 3)), |u (slicePoint t y)| ≤ B) →
            (∃ (M : ClosedIndex → ℝ),
                Summable M ∧
                  ∀ (i : ClosedIndex) (y : EuclideanSpace ℝ (Fin 3)),
                    |closedCoeff u i t * closedONHarmonic i (slicePoint t y)| ≤ M i) →
              ∀ (x : MinkowskiModel 3),
                x 0 = t → ∑' (i : ClosedIndex), closedCoeff u i t * closedONHarmonic i x = u x :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.tsum_closedCoeff_eq

example :
    ContinuousOn chartRadius (Ioo 0 π) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.continuousOn_chartRadius

example :
    chartRadius '' Ioo 0 π = Ioi 0 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.image_chartRadius

example :
    ∀ (l : ℕ) (j : Fin (2 * l + 1)), (sphereModuleBasis l) j = sphereBasis l j :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.sphereModuleBasis_apply

example :
    ∀ (i : ClosedIndex), ∃ (C : ℝ), ∀ (x : MinkowskiModel 3), |closedONHarmonic i x| ≤ C :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.exists_bound_closedONHarmonic

example :
    ∀ {g : MinkowskiModel 3 → ℝ} {t : ℝ}, (Continuous fun y => g (slicePoint t y)) →
      ∀ {B : ℝ}, (∀ (y : EuclideanSpace ℝ (Fin 3)), |g (slicePoint t y)| ≤ B) →
        (∀ (i : ClosedIndex), chartPair t g (closedONHarmonic i) = 0) →
          ∀ (x : MinkowskiModel 3), x 0 = t → g x = 0 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.eq_zero_of_chartPair

example :
    ∀ (x : MinkowskiModel 3), slicePoint (x 0) (spatialPart x) = x :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.slicePoint_spatialPart

example :
    ∀ (l : ℕ) (j k : Fin (2 * l + 1)),
      ∫ (u : ↑(UnitSphere 3)),
          (SphericalHarmonics.restrict 3 l) (↑(sphereBasis l j)) u *
            (SphericalHarmonics.restrict 3 l) (↑(sphereBasis l k)) u ∂surfaceMeasure 3 =
        if j = k then 1 else 0 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.integral_sphereBasis

example :
    ∀ (t r : ℝ) (u : EuclideanSpace ℝ (Fin 3)), chartPoint t r u = slicePoint t (r • u) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.chartPoint_eq_slicePoint

example :
    MinkowskiModel 3 → EuclideanSpace ℝ (Fin 3) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.spatialPart

example :
    ∀ {A : ℝ} (hA : 0 < A) {φ : ClosedIndex → ℝ → ℝ},
      (∀ (i : ClosedIndex), ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) →
        IsModeFamily (closedDust A hA) φ closedONHarmonic fun (i : ClosedIndex) =>
          ↑(i.fst.1 + i.fst.2) * (↑i.fst.1 + ↑i.fst.2 + 2) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.isModeFamily_closedON

example :
    ∀ {A : ℝ} (hA : 0 < A) {t : ℝ},
      t ∈ (closedDust A hA).I →
        HasUniqueCoefficients (slice (closedDust A hA) t) closedONHarmonic :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.hasUniqueCoefficients_closedON

example :
    ∀ (l : ℕ) (j : Fin (2 * l + 1)) (u : ↑(UnitSphere 3)),
      |(SphericalHarmonics.restrict 3 l) (↑(sphereBasis l j)) u| ≤ √((2 * ↑l + 1) / (4 * π)) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.abs_restrict_sphereBasis_le

example :
    ∀ (i : ClosedIndex) {S : ℝ},
      (∀ θ ∈ Icc 0 π, |sin θ ^ i.fst.1 * gegenbauerReal i.fst.1 i.fst.2 (cos θ)| ≤ S) →
        ∀ (x : MinkowskiModel 3), |closedONHarmonic i x| ≤ √((2 * ↑i.fst.1 + 1) / (4 * π)) * S :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.abs_closedONHarmonic_le

example :
    ∀ {r : ℝ}, 0 < r → 2 * arctan (r / 2) ∈ Ioo 0 π ∧ chartRadius (2 * arctan (r / 2)) = r :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.chartRadius_arctan

example :
    ∀ (lm : ℕ × ℕ), 0 < closedNorm lm :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.closedNorm_pos

example :
    (A : ℝ) → 0 < A → (MinkowskiModel 3 → ℝ) → Prop :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsClosedExpandable

example :
    (MinkowskiModel 3 → ℝ) → ClosedIndex → ℝ → ℝ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.closedCoeff

example :
    ∀ {A : ℝ} (hA : 0 < A),
      ∃ (c : ClosedIndex → ℝ),
        (∀ (i : ClosedIndex), 0 < c i) ∧
          (IsClosedExpandable A hA fun (x : MinkowskiModel 3) =>
              ∑' (j : ClosedIndex), c j * closedONHarmonic j x) ∧
            (∀ (i : ClosedIndex),
                ∀ t ∈ (closedDust A hA).I,
                  closedCoeff
                      (fun (x : MinkowskiModel 3) =>
                        ∑' (j : ClosedIndex), c j * closedONHarmonic j x)
                      i t =
                    c i) ∧
              ∀ t ∈ (closedDust A hA).I,
                ∃ (M : ClosedIndex → ℝ),
                  Summable M ∧
                    ∀ (i : ClosedIndex),
                      ∀ y ∈ slice (closedDust A hA) t,
                        |evolutionResidual (closedDust A hA)
                                (closedCoeff
                                  (fun (x : MinkowskiModel 3) =>
                                    ∑' (j : ClosedIndex), c j * closedONHarmonic j x)
                                  i)
                                t *
                              closedONHarmonic i y| ≤
                          M i :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.exists_isClosedExpandable_infinite

example :
    (l : ℕ) → Fin (2 * l + 1) → ↥(harmonics 3 l) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.sphereBasis

example :
    ∀ {ι : Type u_1} {U : Set (MinkowskiModel 3)},
      IsOpen U →
        ∀ {f g : ι → MinkowskiModel 3 → ℝ},
          IsC2Series U f → (∀ (i : ι), ∀ x ∈ U, f i x = g i x) → IsC2Series U g :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsC2Series.congr

example :
    ∀ (i : ClosedIndex), ContDiff ℝ ∞ (closedONHarmonic i) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.contDiff_closedONHarmonic

example :
    ∀ {A : ℝ} (hA : 0 < A) {φ : ClosedIndex → ℝ → ℝ},
      (∀ (i : ClosedIndex), ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) →
        (IsC2Series ↑(domain (closedDust A hA)) fun (i : ClosedIndex) =>
            separated (φ i) (closedONHarmonic i)) →
          (∀ t ∈ (closedDust A hA).I,
              ∃ (M : ClosedIndex → ℝ),
                Summable M ∧
                  ∀ (i : ClosedIndex) (y : EuclideanSpace ℝ (Fin 3)),
                    |φ i t * closedONHarmonic i (slicePoint t y)| ≤ M i) →
            (IsClosedExpandable A hA fun (x : MinkowskiModel 3) =>
                ∑' (j : ClosedIndex), φ j (x 0) * closedONHarmonic j x) ∧
              ∀ (i : ClosedIndex),
                ∀ t ∈ (closedDust A hA).I,
                  closedCoeff
                      (fun (x : MinkowskiModel 3) =>
                        ∑' (j : ClosedIndex), φ j (x 0) * closedONHarmonic j x)
                      i t =
                    φ i t :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.isClosedExpandable_tsum

example :
    ∀ {θ : ℝ}, θ ∈ Ioo 0 π → HasDerivAt chartRadius (2 / (1 + cos θ)) θ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.hasDerivAt_chartRadius

example :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.chartWeight

example :
    ∀ {g : MinkowskiModel 3 → ℝ} {t B : ℝ},
      (∀ (y : EuclideanSpace ℝ (Fin 3)), |g (slicePoint t y)| ≤ B) →
        ∀ {l : ℕ} (q : ↥(harmonics 3 l)) {C : ℝ},
          (∀ (u : ↑(UnitSphere 3)), |(SphericalHarmonics.restrict 3 l) (↑q) u| ≤ C) →
            ∀ (r : ℝ), |angularCoeff g t q r| ≤ B * C * (surfaceMeasure 3).real univ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.abs_angularCoeff_le

example :
    ℝ → EuclideanSpace ℝ (Fin 3) → MinkowskiModel 3 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.slicePoint

example :
    Continuous chartWeight :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.continuous_chartWeight

example :
    ∀ {l : ℕ} (p : ↥(harmonics 3 l)) (m : ℕ) (x : MinkowskiModel 3),
      closedHarmonic p m x =
        ∑ j : Fin (2 * l + 1), ((sphereModuleBasis l).repr p) j * closedONHarmonic ⟨(l, m), j⟩ x :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.closedHarmonic_eq_sum

example :
    ∀ (t : ℝ) (i j : ClosedIndex),
      chartPair t (closedONHarmonic i) (closedONHarmonic j) =
        if i = j then closedNorm i.fst else 0 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.chartPair_closedONHarmonic

example :
    ∀ (t : ℝ), Continuous (slicePoint t) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.continuous_slicePoint

example :
    ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 3)), slicePoint t y 0 = t :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.slicePoint_zero

example :
    ∀ (g : ℝ → ℝ),
      ∫ (r : ℝ) in Ioi 0, r ^ 2 * (((1 + r ^ 2 / 4) ^ 3)⁻¹ * g r) =
        ∫ (θ : ℝ) in Ioo 0 π, sin θ ^ 2 * g (chartRadius θ) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.integral_Ioi_chartRadius

example :
    ℕ × ℕ → ℝ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.closedNorm

example :
    ∀ {A : ℝ} {hA : 0 < A} {u : MinkowskiModel 3 → ℝ},
      IsClosedExpandable A hA u →
        ∀ {x : MinkowskiModel 3},
          x ∈ domain (closedDust A hA) →
            ∑' (i : ClosedIndex), separated (closedCoeff u i) (closedONHarmonic i) x = u x :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsClosedExpandable.tsum_eq

example :
    ∀ {A : ℝ} (hA : 0 < A) (s : Finset ClosedIndex) {φ : ClosedIndex → ℝ → ℝ},
      (∀ i ∉ s, φ i = 0) →
        (∀ i ∈ s, ContDiffOn ℝ ∞ (φ i) (closedDust A hA).I) →
          IsClosedExpandable A hA fun (x : MinkowskiModel 3) =>
            ∑' (j : ClosedIndex), φ j (x 0) * closedONHarmonic j x :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.isClosedExpandable_finite

example :
    ClosedIndex → MinkowskiModel 3 → ℝ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.closedONHarmonic

example :
    ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 3)), psi 1 (slicePoint t y) = 1 + ‖y‖ ^ 2 / 4 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.psi_slicePoint

example :
    ∀ {φ : ClosedIndex → ℝ → ℝ} {t : ℝ} {M : ClosedIndex → ℝ},
      Summable M →
        (∀ (i : ClosedIndex) (y : EuclideanSpace ℝ (Fin 3)),
            |φ i t * closedONHarmonic i (slicePoint t y)| ≤ M i) →
          ∀ (i : ClosedIndex),
            closedCoeff
                (fun (x : MinkowskiModel 3) =>
                  ∑' (j : ClosedIndex), φ j (x 0) * closedONHarmonic j x)
                i t =
              φ i t :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.closedCoeff_tsum

example :
    InjOn chartRadius (Ioo 0 π) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.injOn_chartRadius

example :
    ∀ {a : ClosedIndex → ℝ} {t : ℝ} {M : ClosedIndex → ℝ},
      Summable M →
        (∀ (i : ClosedIndex) (y : EuclideanSpace ℝ (Fin 3)),
            |a i * closedONHarmonic i (slicePoint t y)| ≤ M i) →
          Continuous fun (y : EuclideanSpace ℝ (Fin 3)) =>
            ∑' (i : ClosedIndex), a i * closedONHarmonic i (slicePoint t y) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.continuous_tsum_slice

example :
    ∀ {r : ℝ}, 0 ≤ r → ∀ (u : ↑(UnitSphere 3)), chartWeight (r • ↑u) = ((1 + r ^ 2 / 4) ^ 3)⁻¹ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.chartWeight_smul

example :
    ∀ {g : MinkowskiModel 3 → ℝ} {t : ℝ},
      (Continuous fun (y : EuclideanSpace ℝ (Fin 3)) => g (slicePoint t y)) →
        ∀ {B : ℝ},
          (∀ (y : EuclideanSpace ℝ (Fin 3)), |g (slicePoint t y)| ≤ B) →
            (∀ (i : ClosedIndex), chartPair t g (closedONHarmonic i) = 0) →
              ∀ {l : ℕ} (p : ↥(harmonics 3 l)) (m : ℕ), chartPair t g (closedHarmonic p m) = 0 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.chartPair_closedHarmonic_eq_zero

example :
    ∀ {g : MinkowskiModel 3 → ℝ} {t : ℝ},
      (Continuous fun (y : EuclideanSpace ℝ (Fin 3)) => g (slicePoint t y)) →
        ∀ {l : ℕ} (q : ↥(harmonics 3 l)), Continuous (angularCoeff g t q) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.continuous_angularCoeff

example :
    ∀ {g : MinkowskiModel 3 → ℝ} {t : ℝ},
      (Continuous fun (y : EuclideanSpace ℝ (Fin 3)) => g (slicePoint t y)) →
        ∀ {B : ℝ},
          (∀ (y : EuclideanSpace ℝ (Fin 3)), |g (slicePoint t y)| ≤ B) →
            ∀ {l : ℕ} (q : ↥(harmonics 3 l)) (m : ℕ),
              chartPair t g (closedHarmonic q m) =
                ∫ (θ : ℝ) in Ioo 0 π,
                  sin θ ^ 2 *
                    (sin θ ^ l * gegenbauerReal l m (cos θ) *
                      angularCoeff g t q (chartRadius θ)) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.chartPair_closedHarmonic_polar

example :
    ∀ (i : ClosedIndex) (R : ℝ),
      ∃ (K : ℝ),
        0 ≤ K ∧
          ∀ y ∈ Metric.closedBall 0 R,
            ‖closedONHarmonic i y‖ ≤ K ∧
              ‖fderiv ℝ (closedONHarmonic i) y‖ ≤ K ∧
                ‖fderiv ℝ (fderiv ℝ (closedONHarmonic i)) y‖ ≤ K :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.exists_bound_closedONHarmonic_ball

example :
    ∀ (y : EuclideanSpace ℝ (Fin 3)), 0 < chartWeight y :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.chartWeight_pos

example :
    ∀ {A κ : ℝ} (hA : 0 < A),
      0 < κ →
        ∀ {u : MinkowskiModel 3 → ℝ},
          (∀ t ∈ (closedDust A hA).I,
              Continuous fun (y : EuclideanSpace ℝ (Fin 3)) => u (slicePoint t y)) →
            (∀ t ∈ (closedDust A hA).I,
                ∃ (B : ℝ), ∀ (y : EuclideanSpace ℝ (Fin 3)), |u (slicePoint t y)| ≤ B) →
              (∀ t ∈ (closedDust A hA).I,
                  ∃ (M : ClosedIndex → ℝ),
                    Summable M ∧
                      ∀ (i : ClosedIndex) (y : EuclideanSpace ℝ (Fin 3)),
                        |closedCoeff u i t * closedONHarmonic i (slicePoint t y)| ≤ M i) →
                (∀ (i : ClosedIndex), ContDiffOn ℝ ∞ (closedCoeff u i) (closedDust A hA).I) →
                  (IsC2Series ↑(domain (closedDust A hA)) fun (i : ClosedIndex) =>
                      separated (closedCoeff u i) (closedONHarmonic i)) →
                    ∀ {t : ℝ},
                      t ∈ (closedDust A hA).I →
                        (∃ (M : ClosedIndex → ℝ),
                            Summable M ∧
                              ∀ (i : ClosedIndex),
                                ∀ y ∈ slice (closedDust A hA) t,
                                  |evolutionResidual (closedDust A hA) (closedCoeff u i) t *
                                        closedONHarmonic i y| ≤
                                    M i) →
                          ((∀ y ∈ slice (closedDust A hA) t,
                              ScalarSystemAt (closedDust A hA) κ
                                (dustDensity κ (6 * A) (closedDust A hA).a) u
                                (fun (y : MinkowskiModel 3) =>
                                  ∑' (i : ClosedIndex),
                                    contrast (closedDust A hA) κ
                                      (dustDensity κ (6 * A) (closedDust A hA).a)
                                      (closedCoeff u i)
                                      (↑(i.fst.1 + i.fst.2) * (↑i.fst.1 + ↑i.fst.2 + 2))
                                      (closedONHarmonic i) y)
                                (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                                  ∑' (i : ClosedIndex),
                                    covelocity (closedDust A hA) κ
                                      (dustDensity κ (6 * A) (closedDust A hA).a)
                                      (closedCoeff u i) (closedONHarmonic i) y j)
                                y) ↔
                            ∀ (i : ClosedIndex),
                              Evolution (closedDust A hA) (closedCoeff u i) t) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.closed_data_scalarSystemAt_slice_iff

example :
    ∀ {θ : ℝ}, θ ∈ Ioo 0 π → 0 < 1 + cos θ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.one_add_cos_pos

example :
    ∀ {D : Data} {κ : ℝ} {ρ : ℝ → ℝ} {u v δ : MinkowskiModel 3 → ℝ}
      {V : MinkowskiModel 3 → Fin 4 → ℝ} {x : MinkowskiModel 3},
      u =ᶠ[𝓝 x] v → (ScalarSystemAt D κ ρ u δ V x ↔ ScalarSystemAt D κ ρ v δ V x) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.scalarSystemAt_congr

example :
    ∀ {l l' : ℕ} (p : ↥(harmonics 3 l)) (q : ↥(harmonics 3 l')) (m m' : ℕ) (t : ℝ),
      chartPair t (closedHarmonic p m) (closedHarmonic q m') =
        (∫ (u : ↑(UnitSphere 3)),
            (SphericalHarmonics.restrict 3 l) (↑p) u *
              (SphericalHarmonics.restrict 3 l') (↑q) u ∂surfaceMeasure 3) *
          ∫ (θ : ℝ) in Ioo 0 π,
            sin θ ^ 2 *
              (sin θ ^ l * gegenbauerReal l m (cos θ) *
                (sin θ ^ l' * gegenbauerReal l' m' (cos θ))) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.chartPair_closedHarmonic

example :
    ∀ {l : ℕ} (p : ↥(harmonics 3 l)) (m : ℕ) (t : ℝ),
      Continuous fun (y : EuclideanSpace ℝ (Fin 3)) => closedHarmonic p m (slicePoint t y) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.continuous_closedHarmonic_slice

/-! ProjectAinos.GeneralRelativity.CurvedOpenSynthesis -/

example :
    ∀ {D : Data},
      D.k = -1 →
        ∀ {ξ : ℝ},
          0 < ξ →
            ∀ {x : MinkowskiModel 3}, x ∈ puncturedDomain D → openZonal ξ x = zonalWave (ξ, x) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.openZonal_eq_zonalWave

example :
    Data → Set (MinkowskiModel 3) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.puncturedDomain

example :
    ℝ → MinkowskiModel 3 → ℝ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.openZonal

example :
    ∀ (D : Data), IsOpen (puncturedDomain D) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.isOpen_puncturedDomain

example :
    ∀ {U : Set (MinkowskiModel 3)} {μ : Measure ℝ} {f : ℝ → MinkowskiModel 3 → ℝ},
      IsC2Synthesis U μ f →
        ∀ {y : MinkowskiModel 3},
          y ∈ U →
            ∀ (j : Fin 4),
              HasIntegral μ (fun (ξ : ℝ) => part (f ξ) j y)
                (part (fun (w : MinkowskiModel 3) => ∫ (ξ : ℝ), f ξ w ∂μ) j y) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsC2Synthesis.part_integral

example :
    ∀ {A : ℝ} (hA : 0 < A),
      (∀ (ξ : ℝ), ContDiffOn ℝ ∞ (fun (_ : ℝ) => unitDensity ξ) (openDust A hA).I) ∧
        (IsC2Synthesis (puncturedDomain (openDust A hA)) (volume.restrict (Ioi 0))
            fun (ξ : ℝ) => separated (fun (_ : ℝ) => unitDensity ξ) (openZonal ξ)) ∧
          (∀ (t : ℝ),
              IntegrableOn
                (fun (ξ : ℝ) =>
                  evolutionResidual (openDust A hA) (fun (_ : ℝ) => unitDensity ξ) t)
                (Ioi 0) volume) ∧
            ¬unitDensity =ᵐ[volume.restrict (Ioi 0)] 0 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.unitDensity_synthesis_hypotheses

example :
    ∀ {U : Set (MinkowskiModel 3)} {μ : Measure ℝ} {f : ℝ → MinkowskiModel 3 → ℝ},
      IsC2Synthesis U μ f →
        ∀ {y : MinkowskiModel 3},
          y ∈ U →
            ∀ (v : MinkowskiModel 3),
              Integrable
                  (fun (ξ : ℝ) =>
                    (ContinuousLinearMap.apply ℝ ℝ) v ∘SL fderiv ℝ (fderiv ℝ (f ξ)) y)
                  μ ∧
                HasFDerivAt
                  (fun (z : MinkowskiModel 3) =>
                    (fderiv ℝ (fun (w : MinkowskiModel 3) => ∫ (ξ : ℝ), f ξ w ∂μ) z) v)
                  (∫ (ξ : ℝ),
                    (ContinuousLinearMap.apply ℝ ℝ) v ∘SL fderiv ℝ (fderiv ℝ (f ξ)) y ∂μ)
                  y :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsC2Synthesis.hasFDerivAt_part

example :
    ∀ {g : MinkowskiModel 3 → ℝ} {y : MinkowskiModel 3},
      DifferentiableAt ℝ (fderiv ℝ g) y →
        ∀ (a c : Fin 4),
          secondPartial g y a c = ((fderiv ℝ (fderiv ℝ g) y) (Pi.single a 1)) (Pi.single c 1) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsC2Synthesis.secondPartial_eq

example :
    ∀ {A : ℝ} (hA : 0 < A) {ξ : ℝ},
      0 < ξ →
        ∀ {y : MinkowskiModel 3},
          y ∈ puncturedDomain (openDust A hA) →
            separated (fun (_ : ℝ) => unitDensity ξ) (openZonal ξ) y =
                unitDensity ξ * zonalWave (ξ, y) ∧
              fderiv ℝ (separated (fun (_ : ℝ) => unitDensity ξ) (openZonal ξ)) y =
                  unitDensity ξ • fderiv ℝ (fun (z : MinkowskiModel 3) => zonalWave (ξ, z)) y ∧
                fderiv ℝ (fderiv ℝ (separated (fun (_ : ℝ) => unitDensity ξ) (openZonal ξ))) y =
                    unitDensity ξ •
                      fderiv ℝ
                        (fun (w : MinkowskiModel 3) =>
                          fderiv ℝ (fun (z : MinkowskiModel 3) => zonalWave (ξ, z)) w)
                        y ∧
                  DifferentiableAt ℝ (separated (fun (_ : ℝ) => unitDensity ξ) (openZonal ξ))
                      y ∧
                    DifferentiableAt ℝ
                      (fderiv ℝ (separated (fun (_ : ℝ) => unitDensity ξ) (openZonal ξ))) y :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.unitDensity_jets

example :
    ∀ {μ : Measure ℝ} {g h : ℝ → ℝ} {v : ℝ}, HasIntegral μ g v → g =ᵐ[μ] h → HasIntegral μ h v :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.HasIntegral.congr_ae

example :
    ∀ {U : Set (MinkowskiModel 3)} {μ : Measure ℝ} {f : ℝ → MinkowskiModel 3 → ℝ},
      IsC2Synthesis U μ f →
        ∀ {y : MinkowskiModel 3},
          y ∈ U →
            HasFDerivAt (fun (w : MinkowskiModel 3) => ∫ (ξ : ℝ), f ξ w ∂μ)
              (∫ (ξ : ℝ), fderiv ℝ (f ξ) y ∂μ) y :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsC2Synthesis.hasFDerivAt

example :
    ∀ {ξ : ℝ}, ξ ∈ Icc 1 2 → unitDensity ξ = 1 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.unitDensity_of_mem

example :
    Data → ℝ → Set (MinkowskiModel 3) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.puncturedSlice

example :
    ∀ {A : ℝ} (hA : 0 < A) {t : ℝ},
      t ∈ (openDust A hA).I →
        ∀ {c : ℝ → ℝ},
          IntegrableOn c (Ioi 0) volume →
            (∀ x ∈ puncturedSlice (openDust A hA) t,
                ∫ (ξ : ℝ) in Ioi 0, c ξ * openZonal ξ x = 0) →
              c =ᵐ[volume.restrict (Ioi 0)] 0 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.ae_eq_zero_of_integral_openZonal

example :
    ∀ {A : ℝ} (hA : 0 < A),
      IsC2Synthesis (puncturedDomain (openDust A hA)) (volume.restrict (Ioi 0)) fun (ξ : ℝ) =>
        separated (fun (_ : ℝ) => unitDensity ξ) (openZonal ξ) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.isC2Synthesis_unitDensity

example :
    ↥(harmonics 3 0) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.harmonicOne

example :
    ∀ {μ : Measure ℝ} {g h : ℝ → ℝ} {v w : ℝ},
      HasIntegral μ g v → HasIntegral μ h w → HasIntegral μ (fun (ξ : ℝ) => g ξ + h ξ) (v + w) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.HasIntegral.add

example :
    ∀ {D : Data} {κ : ℝ} {ρ : ℝ → ℝ} {φ : ℝ → ℝ → ℝ} {Q : ℝ → MinkowskiModel 3 → ℝ} {q : ℝ → ℝ}
      {μ : Measure ℝ} {U : Set (MinkowskiModel 3)},
      IsModeFamily D φ Q q →
        (IsC2Synthesis U μ fun (ξ : ℝ) => separated (φ ξ) (Q ξ)) →
          ∀ {x : MinkowskiModel 3},
            x ∈ U →
              x ∈ domain D →
                κ * ρ (x 0) ≠ 0 →
                  (ScalarSystemAt D κ ρ
                      (fun (y : MinkowskiModel 3) => ∫ (ξ : ℝ), separated (φ ξ) (Q ξ) y ∂μ)
                      (fun (y : MinkowskiModel 3) =>
                        ∫ (ξ : ℝ), contrast D κ ρ (φ ξ) (q ξ) (Q ξ) y ∂μ)
                      (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                        ∫ (ξ : ℝ), covelocity D κ ρ (φ ξ) (Q ξ) y j ∂μ)
                      x ↔
                    ∫ (ξ : ℝ), evolutionResidual D (φ ξ) (x 0) * Q ξ x ∂μ = 0) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.scalarSystemAt_integral_iff

example :
    ∀ (ξ : ℝ) (x : MinkowskiModel 3),
      openZonal ξ x = Hyperbolic.zonalProfile ξ (chartCoordinate (-1) x) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.openZonal_eq

example :
    ℝ × MinkowskiModel 3 → ℝ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.zonalWave

example :
    ∀ {A : ℝ} (hA : 0 < A) {φ : ℝ → ℝ → ℝ},
      (∀ (ξ : ℝ), ContDiffOn ℝ ∞ (φ ξ) (openDust A hA).I) →
        IsModeFamily (openDust A hA) φ openZonal fun (ξ : ℝ) => 1 + ξ ^ 2 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.isModeFamily_openZonal

example :
    ¬unitDensity =ᵐ[volume.restrict (Ioi 0)] 0 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.not_unitDensity_ae_eq_zero

example :
    Data → Set (ℝ × MinkowskiModel 3) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.zonalParam

example :
    ∀ {A κ : ℝ} (hA : 0 < A),
      0 < κ →
        ∀ {φ : ℝ → ℝ → ℝ},
          (∀ (ξ : ℝ), ContDiffOn ℝ ∞ (φ ξ) (openDust A hA).I) →
            (IsC2Synthesis (puncturedDomain (openDust A hA)) (volume.restrict (Ioi 0))
                fun (ξ : ℝ) => separated (φ ξ) (openZonal ξ)) →
              ∀ {t : ℝ},
                t ∈ (openDust A hA).I →
                  IntegrableOn (fun (ξ : ℝ) => evolutionResidual (openDust A hA) (φ ξ) t)
                      (Ioi 0) volume →
                    ((∀ y ∈ puncturedSlice (openDust A hA) t,
                        ScalarSystemAt (openDust A hA) κ
                          (dustDensity κ (6 * A) (openDust A hA).a)
                          (fun (y : MinkowskiModel 3) =>
                            ∫ (ξ : ℝ) in Ioi 0, separated (φ ξ) (openZonal ξ) y)
                          (fun (y : MinkowskiModel 3) =>
                            ∫ (ξ : ℝ) in Ioi 0,
                              contrast (openDust A hA) κ
                                (dustDensity κ (6 * A) (openDust A hA).a) (φ ξ) (1 + ξ ^ 2)
                                (openZonal ξ) y)
                          (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                            ∫ (ξ : ℝ) in Ioi 0,
                              covelocity (openDust A hA) κ
                                (dustDensity κ (6 * A) (openDust A hA).a) (φ ξ) (openZonal ξ) y
                                j)
                          y) ↔
                      ∀ᵐ (ξ : ℝ) ∂volume.restrict (Ioi 0), Evolution (openDust A hA) (φ ξ) t) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.open_zonal_scalarSystemAt_slice_iff

example :
    ∀ {U : Set (MinkowskiModel 3)} {μ : Measure ℝ} {f : ℝ → MinkowskiModel 3 → ℝ},
      IsC2Synthesis U μ f →
        ∀ {y : MinkowskiModel 3},
          y ∈ U →
            ∀ (a c : Fin 4),
              HasIntegral μ (fun (ξ : ℝ) => secondPartial (f ξ) y a c)
                (secondPartial (fun (w : MinkowskiModel 3) => ∫ (ξ : ℝ), f ξ w ∂μ) y a c) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsC2Synthesis.secondPartial_integral

example :
    ∀ {A : ℝ} (hA : 0 < A) {t : ℝ},
      t ∈ (openDust A hA).I →
        ∀ {ρ : ℝ},
          0 < ρ → ∃ x ∈ puncturedSlice (openDust A hA) t, chartCoordinate (-1) x = cosh ρ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.exists_puncturedSlice_cosh

example :
    Measurable unitDensity :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.measurable_unitDensity

example :
    ∀ {U : Set (MinkowskiModel 3)} {μ : Measure ℝ} {f : ℝ → MinkowskiModel 3 → ℝ},
      IsC2Synthesis U μ f →
        ∀ {y : MinkowskiModel 3}, y ∈ U → Integrable (fun (ξ : ℝ) => f ξ y) μ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsC2Synthesis.integrable

example :
    ∀ {D : Data},
      D.k = -1 →
        ∀ {p : ℝ × MinkowskiModel 3},
          p ∈ zonalParam D →
            ContDiffAt ℝ ∞
                (fun (q : ℝ × MinkowskiModel 3) =>
                  fderiv ℝ (fun (z : MinkowskiModel 3) => zonalWave (q.1, z)) q.2)
                p ∧
              ContDiffAt ℝ ∞
                (fun (q : ℝ × MinkowskiModel 3) =>
                  fderiv ℝ
                    (fun (w : MinkowskiModel 3) =>
                      fderiv ℝ (fun (z : MinkowskiModel 3) => zonalWave (q.1, z)) w)
                    q.2)
                p :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.contDiffAt_zonalWave_derivs

example :
    Integrable unitDensity volume :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.integrable_unitDensity

example :
    ∀ {μ : Measure ℝ} {g h : ℝ → ℝ} {v w : ℝ},
      HasIntegral μ g v → HasIntegral μ h w → HasIntegral μ (fun (ξ : ℝ) => g ξ - h ξ) (v - w) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.HasIntegral.sub

example :
    ℝ → ℝ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.unitDensity

example :
    ∀ {μ : Measure ℝ} {g : ℝ → ℝ} {v : ℝ},
      HasIntegral μ g v → ∀ (c : ℝ), HasIntegral μ (fun (ξ : ℝ) => c * g ξ) (c * v) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.HasIntegral.mul_left

example :
    ∀ {D : Data},
      D.k = -1 →
        ∀ {p : ℝ × MinkowskiModel 3},
          0 < p.1 → p.2 ∈ puncturedDomain D → ContDiffAt ℝ ∞ zonalWave p :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.contDiffAt_zonalWave

example :
    ∀ {ξ : ℝ}, ξ ∉ Icc 1 2 → unitDensity ξ = 0 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.unitDensity_of_not_mem

example :
    ∀ {U : Set (MinkowskiModel 3)} {μ : Measure ℝ} {f : ℝ → MinkowskiModel 3 → ℝ},
      IsC2Synthesis U μ f →
        ∀ {y : MinkowskiModel 3}, y ∈ U → Integrable (fun (ξ : ℝ) => fderiv ℝ (f ξ) y) μ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsC2Synthesis.integrable_fderiv

example :
    Set (MinkowskiModel 3) → Measure ℝ → (ℝ → MinkowskiModel 3 → ℝ) → Prop :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsC2Synthesis

example :
    ∀ {D : Data} {x : MinkowskiModel 3},
      x ∈ puncturedDomain D → D.k = -1 → 1 < chartCoordinate (-1) x :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.one_lt_chartCoordinate_of_mem

example :
    ∀ {μ : Measure ℝ} {g h : ℝ → ℝ} {v : ℝ},
      HasIntegral μ g v → (∀ (ξ : ℝ), g ξ = h ξ) → HasIntegral μ h v :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.HasIntegral.congr_fun

example :
    Measure ℝ → (ℝ → ℝ) → ℝ → Prop :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.HasIntegral

example :
    ∀ {D : Data} {x : MinkowskiModel 3},
      x ∈ puncturedDomain D → D.k = -1 → 0 < psi (-1) x ∧ psi (-1) x < 1 :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.psi_lt_one_of_mem

example :
    ∀ {U : Set (MinkowskiModel 3)} {μ : Measure ℝ} {f : ℝ → MinkowskiModel 3 → ℝ},
      IsC2Synthesis U μ f →
        ∀ {y : MinkowskiModel 3},
          y ∈ U →
            (fderiv ℝ fun (w : MinkowskiModel 3) => ∫ (ξ : ℝ), f ξ w ∂μ) =ᶠ[𝓝 y]
              fun (z : MinkowskiModel 3) => ∫ (ξ : ℝ), fderiv ℝ (f ξ) z ∂μ :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsC2Synthesis.fderiv_eventuallyEq

example :
    ∀ {U : Set (MinkowskiModel 3)} {μ : Measure ℝ} {f : ℝ → MinkowskiModel 3 → ℝ},
      IsC2Synthesis U μ f →
        ∀ {y : MinkowskiModel 3},
          y ∈ U →
            ∀ (k : ℝ),
              HasIntegral μ (fun (ξ : ℝ) => spatialLaplacian k (f ξ) y)
                (spatialLaplacian k (fun (w : MinkowskiModel 3) => ∫ (ξ : ℝ), f ξ w ∂μ) y) :=
  @ProjectAinos.GeneralRelativity.CurvedPerturbation.IsC2Synthesis.spatialLaplacian_integral

end ProjectAinos.GeneralRelativity.CurvedPerturbation
