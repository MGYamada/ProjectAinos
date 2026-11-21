/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Fourier.WeightedSynthesis
import ProjectAinos.SmoothGeometry.Tensor.ScalarVectorTensorScaling

/-! Public consumers of the Fourier synthesis of weighted integrable amplitudes (Landau–Lifshitz,
§115, without a cutoff in the frequencies): the invariance of the scalar–vector–tensor
projections under dilations of the wave vector, the weighted amplitudes and their closure
properties, dominated differentiation of the synthesis, the injectivity of the Fourier transform
on `L¹`, the converse of the inversion, and the bounds of dilation-invariant coefficients.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

universe u_1 u_2 u_3

open Set Filter Function MeasureTheory
open scoped ContDiff Topology ComplexConjugate FourierTransform RealInnerProductSpace SchwartzMap

namespace ProjectAinos.SmoothGeometry.ScalarVectorTensor

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) (c : K),
    contract (c • n) M = c • contract n M :=
  @contract_smul_left

example : ∀ {K : Type u_1} [Field K] (n V : Fin 3 → K) (c : K),
    dot (c • n) V = c * dot n V :=
  @dot_smul_left

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) {c : K},
    c ≠ 0 → longCoeff (c • n) M = longCoeff n M :=
  @longCoeff_smul_left

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) {c : K},
    c ≠ 0 → longVec (c • n) = longVec n :=
  @longVec_smul_left

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (c : K), nsq (c • n) = c ^ 2 * nsq n :=
  @nsq_smul_left

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) {c : K},
    c ≠ 0 → ∀ (α β : Fin 3), (c • n) α * (c • n) β / nsq (c • n) = n α * n β / nsq n :=
  @ratio_smul_left

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) (c : K),
    sandwich (c • n) M = c ^ 2 * sandwich n M :=
  @sandwich_smul_left

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) {c : K},
    c ≠ 0 → scalarPart (c • n) = scalarPart n :=
  @scalarPart_smul_left

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) {c : K},
    c ≠ 0 → shear (c • n) M = c • shear n M :=
  @shear_smul_left

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) {c : K},
    c ≠ 0 → tensorPart (c • n) = tensorPart n :=
  @tensorPart_smul_left

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) {c : K},
    c ≠ 0 → transVec (c • n) = transVec n :=
  @transVec_smul_left

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) {c : K},
    c ≠ 0 → vectorPart (c • n) = vectorPart n :=
  @vectorPart_smul_left

end ProjectAinos.SmoothGeometry.ScalarVectorTensor

namespace ProjectAinos.SmoothGeometry.Fourier

example : Set ℝ → ℕ → (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) → Prop :=
  @IsWeightedAmplitude

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsWeightedAmplitude I 1 G →
      ∀ {t : ℝ}, t ∈ I → ∀ (c : Fin 4), AEStronglyMeasurable (partialSymbol c G t) volume :=
  @IsWeightedAmplitude.aestronglyMeasurable_partialSymbol

example : ∀ {I : Set ℝ} {k : ℕ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsOpen I →
      IsWeightedAmplitude I k G →
        ∀ {G' : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
          (∀ t ∈ I, G' t = G t) → IsWeightedAmplitude I k G' :=
  @IsWeightedAmplitude.congr

example : ∀ {I : Set ℝ} {k : ℕ} {F : EuclideanSpace ℝ (Fin 3) → ℂ},
    AEStronglyMeasurable F volume →
      Integrable (fun (ξ : EuclideanSpace ℝ (Fin 3)) => (1 + ‖ξ‖) ^ k * ‖F ξ‖) volume →
        IsWeightedAmplitude I k fun (_ : ℝ) => F :=
  @IsWeightedAmplitude.const

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsOpen I →
      IsWeightedAmplitude I 1 G →
        ∀ {z : MinkowskiModel 3}, z ∈ slab I → DifferentiableAt ℝ (synthesis G) z :=
  @IsWeightedAmplitude.differentiableAt_synthesis

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsOpen I →
      IsWeightedAmplitude I 1 G →
        ∀ {z : MinkowskiModel 3},
          z ∈ slab I →
            ∀ (c : Fin 4),
              (fderiv ℝ (synthesis G) z) (Pi.single c 1) = synthesis (partialSymbol c G) z :=
  @IsWeightedAmplitude.fderiv_synthesis_single

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsOpen I →
      IsWeightedAmplitude I 1 G →
        ∀ {z : MinkowskiModel 3},
          z ∈ slab I →
            HasFDerivAt (synthesis G) (∫ (ξ : EuclideanSpace ℝ (Fin 3)), integrandDeriv G z ξ) z :=
  @IsWeightedAmplitude.hasFDerivAt_synthesis

example : ∀ {I : Set ℝ} {k : ℕ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsWeightedAmplitude I k G → ∀ {t : ℝ}, t ∈ I → Integrable (G t) volume :=
  @IsWeightedAmplitude.integrable

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsWeightedAmplitude I 1 G →
      ∀ {z : MinkowskiModel 3}, z ∈ slab I → Integrable (integrandDeriv G z) volume :=
  @IsWeightedAmplitude.integrable_integrandDeriv

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsOpen I →
      IsWeightedAmplitude I 1 G →
        IsHermitian I G → ∀ (c : Fin 4), IsHermitian I (partialSymbol c G) :=
  @IsWeightedAmplitude.isHermitian_partialSymbol

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsOpen I → IsWeightedAmplitude I 1 G → IsHermitian I G → IsHermitian I (timeDeriv G) :=
  @IsWeightedAmplitude.isHermitian_timeDeriv

example : ∀ {I : Set ℝ} {k : ℕ},
    IsOpen I →
      ∀ {ι : Type u_1} [Fintype ι] {p : ℕ} {m : ι → EuclideanSpace ℝ (Fin 3) → ℂ}
        {G : ι → ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {C : ℝ},
        (∀ (i : ι), AEStronglyMeasurable (m i) volume) →
          (∀ (i : ι) (ξ : EuclideanSpace ℝ (Fin 3)), ‖m i ξ‖ ≤ C * (1 + ‖ξ‖) ^ p) →
            (∀ (i : ι), IsWeightedAmplitude I (k + p) (G i)) →
              IsWeightedAmplitude I k fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
                ∑ i : ι, m i ξ * G i t ξ :=
  @IsWeightedAmplitude.linComb

example : ∀ {I : Set ℝ} {k : ℕ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsWeightedAmplitude I k G → ∀ {k' : ℕ}, k' ≤ k → IsWeightedAmplitude I k' G :=
  @IsWeightedAmplitude.mono

example : ∀ {I : Set ℝ} {k : ℕ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsOpen I →
      ∀ {p : ℕ} {m : EuclideanSpace ℝ (Fin 3) → ℂ} {C : ℝ},
        AEStronglyMeasurable m volume →
          (∀ (ξ : EuclideanSpace ℝ (Fin 3)), ‖m ξ‖ ≤ C * (1 + ‖ξ‖) ^ p) →
            IsWeightedAmplitude I (k + p) G →
              IsWeightedAmplitude I k fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => m ξ * G t ξ :=
  @IsWeightedAmplitude.mul_left

example : ∀ {I : Set ℝ} {k : ℕ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsOpen I →
      IsWeightedAmplitude I (k + 1) G →
        ∀ (c : Fin 4), IsWeightedAmplitude I k (partialSymbol c G) :=
  @IsWeightedAmplitude.partialSymbol

example : ∀ {I : Set ℝ} {k : ℕ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsWeightedAmplitude I (k + 1) G → IsWeightedAmplitude I k (timeDeriv G) :=
  @IsWeightedAmplitude.timeDeriv

example : ∀ {I : Set ℝ} {k : ℕ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsWeightedAmplitude I (k + 1) G →
      ∀ {t : ℝ},
        t ∈ I →
          ∀ (m : EuclideanSpace ℝ (Fin 3) → ℂ) (ξ : EuclideanSpace ℝ (Fin 3)),
            timeDeriv (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => m ξ * G t ξ) t ξ =
              m ξ * timeDeriv G t ξ :=
  @IsWeightedAmplitude.timeDeriv_mul_left

example : ∀ {f : EuclideanSpace ℝ (Fin 3) → ℂ},
    Integrable f volume →
      (∀ (w : EuclideanSpace ℝ (Fin 3)), 𝓕 f w = 0) → ∀ᵐ (ξ : EuclideanSpace ℝ (Fin 3)), f ξ = 0 :=
  @ae_eq_zero_of_fourier_eq_zero

example : ∀ {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {t : ℝ},
    Integrable (G t) volume →
      (∀ (x : EuclideanSpace ℝ (Fin 3)), synthesis G (spacetimePoint t x) = 0) →
        ∀ᵐ (ξ : EuclideanSpace ℝ (Fin 3)), G t ξ = 0 :=
  @ae_eq_zero_of_synthesis_eq_zero'

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsWeightedAmplitude I 1 G →
      ∀ {z : MinkowskiModel 3}, z ∈ slab I → AEStronglyMeasurable (integrandDeriv G z) volume :=
  @aestronglyMeasurable_integrandDeriv

example : ∀ {f : EuclideanSpace ℝ (Fin 3) → ℂ},
    ContinuousOn f {ξ : EuclideanSpace ℝ (Fin 3) | ξ ≠ 0} → AEStronglyMeasurable f volume :=
  @aestronglyMeasurable_of_continuousOn_ne_zero

example : ∀ {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {z : MinkowskiModel 3},
    AEStronglyMeasurable (G (z 0)) volume → AEStronglyMeasurable (synthesisIntegrand G z) volume :=
  @aestronglyMeasurable_synthesisIntegrand

example : ∀ (z : MinkowskiModel 3),
    Continuous fun (ξ : EuclideanSpace ℝ (Fin 3)) =>
      Complex.exp (↑(2 * Real.pi * ⟪ξ, spatialPoint z⟫) * Complex.I) :=
  @continuous_phase

example : ∀ (γ : Fin 3),
    Continuous fun (ξ : EuclideanSpace ℝ (Fin 3)) => 2 * ↑Real.pi * ↑(ξ.ofLp γ) * Complex.I :=
  @continuous_spaceMultiplier

example : Fin 4 → MinkowskiModel 3 →L[ℝ] ℂ :=
  @coordCLM

example : ∀ (c : Fin 4) (v : MinkowskiModel 3), (coordCLM c) v = ↑(v c) :=
  @coordCLM_apply

example : ∀ {f : EuclideanSpace ℝ (Fin 3) → ℂ},
    ContinuousOn f {ξ : EuclideanSpace ℝ (Fin 3) | ξ ≠ 0} →
      (∀ (c : ℝ), 0 < c → ∀ (ξ : EuclideanSpace ℝ (Fin 3)), f (c • ξ) = f ξ) →
        ∃ (C : ℝ), ∀ (ξ : EuclideanSpace ℝ (Fin 3)), ‖f ξ‖ ≤ C :=
  @exists_bound_of_scale_invariant

example : ∀ {g : EuclideanSpace ℝ (Fin 3) → ℝ},
    ContDiff ℝ ∞ g →
      HasCompactSupport g →
        ∃ (ψ : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ)), ∀ (x : EuclideanSpace ℝ (Fin 3)), ψ x = ↑(g x) :=
  @exists_schwartz_eq

example : (innerₗ (EuclideanSpace ℝ (Fin 3))).flip = innerₗ (EuclideanSpace ℝ (Fin 3)) :=
  @flip_innerₗ

example : (-innerₗ (EuclideanSpace ℝ (Fin 3))).flip = -innerₗ (EuclideanSpace ℝ (Fin 3)) :=
  @flip_neg_innerₗ

example : ∀ {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {t : ℝ},
    Integrable (G t) volume →
      Integrable (fun (x : EuclideanSpace ℝ (Fin 3)) => synthesis G (spacetimePoint t x)) volume →
        (𝓕 fun (x : EuclideanSpace ℝ (Fin 3)) => synthesis G (spacetimePoint t x)) =ᵐ[volume] G t :=
  @fourier_synthesis_ae

example : ∀ {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {z : MinkowskiModel 3}
    {ξ : EuclideanSpace ℝ (Fin 3)},
    HasDerivAt (fun (s : ℝ) => G s ξ) (timeDeriv G (z 0) ξ) (z 0) →
      HasFDerivAt (fun (w : MinkowskiModel 3) => synthesisIntegrand G w ξ) (integrandDeriv G z ξ)
        z :=
  @hasFDerivAt_synthesisIntegrand

example : ∀ (f : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ)) (k : ℕ),
    Integrable (fun (ξ : EuclideanSpace ℝ (Fin 3)) => (1 + ‖ξ‖) ^ k * ‖f ξ‖) volume :=
  @integrable_one_add_norm_pow_mul

example : ∀ {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {z : MinkowskiModel 3},
    Integrable (G (z 0)) volume → Integrable (synthesisIntegrand G z) volume :=
  @integrable_synthesisIntegrand

example : ∀ {φ f : EuclideanSpace ℝ (Fin 3) → ℂ},
    Integrable φ volume →
      Integrable f volume →
        ∫ (ξ : EuclideanSpace ℝ (Fin 3)), 𝓕⁻ φ ξ * f ξ =
          ∫ (x : EuclideanSpace ℝ (Fin 3)), φ x * 𝓕⁻ f x :=
  @integral_fourierInv_smul_eq

example : ∀ {φ f : EuclideanSpace ℝ (Fin 3) → ℂ},
    Integrable φ volume →
      Integrable f volume →
        ∫ (ξ : EuclideanSpace ℝ (Fin 3)), 𝓕 φ ξ * f ξ =
          ∫ (x : EuclideanSpace ℝ (Fin 3)), φ x * 𝓕 f x :=
  @integral_fourier_smul_eq

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) →
    MinkowskiModel 3 → EuclideanSpace ℝ (Fin 3) → MinkowskiModel 3 →L[ℝ] ℂ :=
  @integrandDeriv

example : ∀ (G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (z : MinkowskiModel 3)
    (ξ : EuclideanSpace ℝ (Fin 3)) (v : MinkowskiModel 3),
    (integrandDeriv G z ξ) v = ∑ c : Fin 4, synthesisIntegrand (partialSymbol c G) z ξ * ↑(v c) :=
  @integrandDeriv_apply

example : ∀ (G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (z : MinkowskiModel 3)
    (ξ : EuclideanSpace ℝ (Fin 3)) (c : Fin 4),
    (integrandDeriv G z ξ) (Pi.single c 1) = synthesisIntegrand (partialSymbol c G) z ξ :=
  @integrandDeriv_single

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
    IsOpen I →
      ∀ {G' : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
        (∀ t ∈ I, G' t = G t) → ∀ (j : ℕ), ∀ t ∈ I, timeDeriv^[j] G' t = timeDeriv^[j] G t :=
  @iterate_timeDeriv_congr

example : ∀ (F : EuclideanSpace ℝ (Fin 3) → ℂ) (j : ℕ),
    (timeDeriv^[j + 1] fun (_ : ℝ) => F) = fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0 :=
  @iterate_timeDeriv_const

example : ∀ {I : Set ℝ},
    IsOpen I →
      ∀ {ι : Type u_1} [Fintype ι] (m : ι → EuclideanSpace ℝ (Fin 3) → ℂ)
        (G : ι → ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (j : ℕ),
        (∀ (i : ι),
            ∀ l < j,
              ∀ t ∈ I,
                ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
                  HasDerivAt (fun (s : ℝ) => timeDeriv^[l] (G i) s ξ) (timeDeriv^[l + 1] (G i) t ξ)
                    t) →
          ∀ t ∈ I,
            ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
              timeDeriv^[j] (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => ∑ i : ι, m i ξ * G i t ξ)
                  t ξ =
                ∑ i : ι, m i ξ * timeDeriv^[j] (G i) t ξ :=
  @iterate_timeDeriv_linComb

example : ∀ {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {z : MinkowskiModel 3}
    {ξ : EuclideanSpace ℝ (Fin 3)} {b : ℝ},
    (∀ (j m : ℕ), j + m ≤ 1 → (1 + ‖ξ‖) ^ m * ‖timeDeriv^[j] G (z 0) ξ‖ ≤ b) →
      ‖integrandDeriv G z ξ‖ ≤ ((2 * Real.pi + 1) * ∑ c : Fin 4, ‖coordCLM c‖) * b :=
  @norm_integrandDeriv_le

example : ∀ (γ : Fin 3) (ξ : EuclideanSpace ℝ (Fin 3)),
    ‖2 * ↑Real.pi * ↑(ξ.ofLp γ) * Complex.I‖ ≤ 2 * Real.pi * (1 + ‖ξ‖) ^ 1 :=
  @norm_spaceMultiplier_le

example : ∀ (G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (z : MinkowskiModel 3)
    (ξ : EuclideanSpace ℝ (Fin 3)), ‖synthesisIntegrand G z ξ‖ = ‖G (z 0) ξ‖ :=
  @norm_synthesisIntegrand

example : Fin 4 → (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) → ℝ → EuclideanSpace ℝ (Fin 3) → ℂ :=
  @partialSymbol

example : ∀ (G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (γ : Fin 3),
    partialSymbol γ.succ G = fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
      2 * ↑Real.pi * ↑(ξ.ofLp γ) * Complex.I * G t ξ :=
  @partialSymbol_succ

example : ∀ (G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ), partialSymbol 0 G = timeDeriv G :=
  @partialSymbol_zero

example : ∀ (F : EuclideanSpace ℝ (Fin 3) → ℂ),
    (timeDeriv fun (_ : ℝ) => F) = fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0 :=
  @timeDeriv_const

end ProjectAinos.SmoothGeometry.Fourier
