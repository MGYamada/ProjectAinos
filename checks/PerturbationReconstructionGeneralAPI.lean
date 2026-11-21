/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.PerturbationReconstructionGeneral

/-! Public consumers of the reconstruction of a flat cosmological perturbation from its scalar,
vector and tensor modes without a cutoff in the frequencies (Landau–Lifshitz, §115): weighted
Fourier data, the equivalence of the linearized Einstein equations with dust and the equations of
almost every frequency, the decomposition into the three sectors, the reconstruction by Fourier
inversion, a perturbation with Schwartz slices whose transform does not vanish at `ξ = 0`, and
the spatial co-ordinate mode with a Schwartz profile as a solution beyond the compact spectrum.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

universe u_1 u_2 u_3

open Set Filter Function MeasureTheory
open scoped ContDiff Topology ComplexConjugate FourierTransform RealInnerProductSpace SchwartzMap

namespace ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Reconstruction

open ProjectAinos.SmoothGeometry ProjectAinos.SmoothGeometry.Fourier

example : Set ℝ →
    (MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ) →
      (MinkowskiModel 3 → ℝ) → (MinkowskiModel 3 → Fin 3 → ℝ) → Prop :=
  @HasIntegrableSpectrum

example : ∀ {I : Set ℝ} {h : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ} {δ : MinkowskiModel 3 → ℝ}
    {v : MinkowskiModel 3 → Fin 3 → ℝ},
    HasIntegrableSpectrum I h δ v →
      IsWeightedData I (fourierMetric h) (fourierScalar δ) (fourierVector v) :=
  @HasIntegrableSpectrum.isWeightedData

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {h : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ}
    {δ : MinkowskiModel 3 → ℝ} {v : MinkowskiModel 3 → Fin 3 → ℝ},
    HasIntegrableSpectrum B.I h δ v →
      (LinearizedEinsteinDust B κ ρ h δ v ↔
        ∀ t ∈ B.I,
          ∀ᵐ (ξ : EuclideanSpace ℝ (Fin 3)),
            FrequencyEq B κ ρ (fourierMetric h) (fourierScalar δ) (fourierVector v) t ξ) :=
  @HasIntegrableSpectrum.linearizedEinsteinDust_iff

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {h : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ}
    {δ : MinkowskiModel 3 → ℝ} {v : MinkowskiModel 3 → Fin 3 → ℝ},
    HasIntegrableSpectrum B.I h δ v →
      (∀ z ∈ FLRW.domain B.toData,
          ∀ (α β : Fin 3),
            h z α β =
              fieldOf (scalarData (fourierMetric h)) z α β +
                  fieldOf (vectorData (fourierMetric h)) z α β +
                fieldOf (tensorData (fourierMetric h)) z α β) ∧
        (∀ z ∈ FLRW.domain B.toData,
            ∀ (α : Fin 3),
              v z α =
                vectorOf (longData (fourierVector v)) z α +
                  vectorOf (transData (fourierVector v)) z α) ∧
          (LinearizedEinsteinDust B κ ρ h δ v ↔
            LinearizedEinsteinDust B κ ρ (fieldOf (scalarData (fourierMetric h))) δ
                (vectorOf (longData (fourierVector v))) ∧
              LinearizedEinsteinDust B κ ρ (fieldOf (vectorData (fourierMetric h)))
                  (fun (_ : MinkowskiModel 3) => 0) (vectorOf (transData (fourierVector v))) ∧
                LinearizedEinsteinDust B κ ρ (fieldOf (tensorData (fourierMetric h)))
                  (fun (_ : MinkowskiModel 3) => 0) fun (_ : MinkowskiModel 3) (_ : Fin 3) =>
                  0) :=
  @HasIntegrableSpectrum.reconstruction

example : Set ℝ →
    (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
      (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) → (ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ) → Prop :=
  @IsWeightedData

example : ∀ {z : MinkowskiModel 3} {B : Background}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      z ∈ slab B.I →
        ∀ (α β : Fin 3),
          fieldOf hh z α β =
            fieldOf (scalarData hh) z α β + fieldOf (vectorData hh) z α β +
              fieldOf (tensorData hh) z α β :=
  @IsWeightedData.fieldOf_eq_add

example : ∀ {B : Background} {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      ∀ {t : ℝ},
        t ∈ B.I →
          ∀ (Λ : ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ),
            (∀ (x : EuclideanSpace ℝ (Fin 3)),
                synthesis
                    (fun (s : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
                      (Λ s) fun (j : JetIdx) => jetAmp hh dd vv j s ξ)
                    (spacetimePoint t x) =
                  0) ↔
              ∀ᵐ (ξ : EuclideanSpace ℝ (Fin 3)),
                ((Λ t) fun (j : JetIdx) => jetAmp hh dd vv j t ξ) = 0 :=
  @IsWeightedData.form_eq_zero_iff

example : ∀ {B : Background} {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      ∀ {t : ℝ},
        t ∈ B.I →
          ∀ (α β : Fin 3),
            Integrable (fun (x : EuclideanSpace ℝ (Fin 3)) => fieldOf hh (spacetimePoint t x) α β)
                volume →
              (𝓕 fun (x : EuclideanSpace ℝ (Fin 3)) =>
                  ((fieldOf hh (spacetimePoint t x) α β : ℝ) : ℂ)) =ᵐ[volume]
                fun (ξ : EuclideanSpace ℝ (Fin 3)) => hh t ξ α β :=
  @IsWeightedData.fourier_fieldOf_ae

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      ∀ {t : ℝ},
        t ∈ B.I →
          ∀ {ξ : EuclideanSpace ℝ (Fin 3)},
            ξ ≠ 0 →
              (FrequencyEq B κ ρ hh dd vv t ξ ↔
                FrequencyEq B κ ρ (scalarData hh) dd (longData vv) t ξ ∧
                  FrequencyEq B κ ρ (vectorData hh)
                      (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0) (transData vv) t ξ ∧
                    FrequencyEq B κ ρ (tensorData hh)
                      (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0)
                      (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) (_ : Fin 3) => 0) t ξ) :=
  @IsWeightedData.frequencyEq_iff_split

example : ∀ {B : Background} {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      ∀ {t : ℝ},
        t ∈ B.I →
          ∀ (Λ : ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ),
            Integrable
              (fun (ξ : EuclideanSpace ℝ (Fin 3)) =>
                (Λ t) fun (j : JetIdx) => jetAmp hh dd vv j t ξ)
              volume :=
  @IsWeightedData.integrable_form

example : ∀ {B : Background} {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv → ∀ (j : JetIdx), IsWeightedAmplitude B.I 0 (jetAmp hh dd vv j) :=
  @IsWeightedData.isWeightedAmplitude_jetAmp

example : ∀ {B : Background} {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv → IsWeightedData B.I (scalarData hh) dd (longData vv) :=
  @IsWeightedData.isWeightedData_scalar

example : ∀ {B : Background} {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      IsWeightedData B.I (tensorData hh) (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0)
        fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) (_ : Fin 3) => 0 :=
  @IsWeightedData.isWeightedData_tensor

example : ∀ {B : Background} {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      IsWeightedData B.I (vectorData hh) (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0)
        (transData vv) :=
  @IsWeightedData.isWeightedData_vector

example : ∀ {B : Background} {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      ∀ (L : EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ →ₗ[ℂ] ScalarVectorTensor.Mat3 ℂ)
        {t : ℝ},
        t ∈ B.I →
          ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
            jet1 (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => (L ξ) (hh t ξ)) t ξ =
              (L ξ) (jet1 hh t ξ) :=
  @IsWeightedData.jet1_linearMap

example : ∀ {B : Background} {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      ∀ (L : EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ →ₗ[ℂ] ScalarVectorTensor.Mat3 ℂ)
        {t : ℝ},
        t ∈ B.I →
          ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
            jet2 (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => (L ξ) (hh t ξ)) t ξ =
              (L ξ) (jet2 hh t ξ) :=
  @IsWeightedData.jet2_linearMap

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      (LinearizedEinsteinDust B κ ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) ↔
        ∀ t ∈ B.I, ∀ᵐ (ξ : EuclideanSpace ℝ (Fin 3)), FrequencyEq B κ ρ hh dd vv t ξ) :=
  @IsWeightedData.linearizedEinsteinDust_iff

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      (LinearizedEinsteinDust B κ ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) ↔
        LinearizedEinsteinDust B κ ρ (fieldOf (scalarData hh)) (scalarOf dd)
            (vectorOf (longData vv)) ∧
          LinearizedEinsteinDust B κ ρ (fieldOf (vectorData hh)) (fun (_ : MinkowskiModel 3) => 0)
              (vectorOf (transData vv)) ∧
            LinearizedEinsteinDust B κ ρ (fieldOf (tensorData hh)) (fun (_ : MinkowskiModel 3) => 0)
              fun (_ : MinkowskiModel 3) (_ : Fin 3) => 0) :=
  @IsWeightedData.linearizedEinsteinDust_iff_split

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      ∀ {t : ℝ},
        t ∈ B.I →
          ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (α : Fin 3),
            ((mixedForm κ ρ t α) fun (j : JetIdx) => jetAmp hh dd vv j t ξ) =
              ScalarVectorTensor.resMixed (fourierCoeffs B κ ρ t) (wave ξ) (jet1 hh t ξ) (vv t ξ)
                α :=
  @IsWeightedData.mixedForm_jetAmp

example : ∀ {z : MinkowskiModel 3} {B : Background}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      z ∈ slab B.I →
        ∀ (c e : Fin 4) (α β : Fin 3),
          ↑(ddh (fieldOf hh) c e z α β) = synthesis (dsym c (dsym e (amp hh α β))) z :=
  @IsWeightedData.ofReal_ddh_fieldOf

example : ∀ {z : MinkowskiModel 3} {B : Background}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      z ∈ slab B.I →
        ∀ (c : Fin 4) (α β : Fin 3),
          ↑(dh (fieldOf hh) c z α β) = synthesis (dsym c (amp hh α β)) z :=
  @IsWeightedData.ofReal_dh_fieldOf

example : ∀ {z : MinkowskiModel 3} {B : Background}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      z ∈ slab B.I → ∀ (α β : Fin 3), ↑(fieldOf hh z α β) = synthesis (amp hh α β) z :=
  @IsWeightedData.ofReal_fieldOf

example : ∀ {z : MinkowskiModel 3} {B : Background}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv → z ∈ slab B.I → ↑(scalarOf dd z) = synthesis dd z :=
  @IsWeightedData.ofReal_scalarOf

example : ∀ {z : MinkowskiModel 3} {B : Background}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      z ∈ slab B.I → ∀ (α : Fin 3), ↑(vectorOf vv z α) = synthesis (vamp vv α) z :=
  @IsWeightedData.ofReal_vectorOf

example : ∀ {z : MinkowskiModel 3} {B : Background}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      z ∈ slab B.I →
        realJet (fieldOf hh) (scalarOf dd) (vectorOf vv) z = fun (j : JetIdx) =>
          synthesis (jetAmp hh dd vv j) z :=
  @IsWeightedData.realJet_eq

example : ∀ {z : MinkowskiModel 3} {B : Background}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      z ∈ slab B.I →
        ∀ (Λ : ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ),
          synthesis
              (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
                (Λ t) fun (j : JetIdx) => jetAmp hh dd vv j t ξ)
              z =
            (Λ (z 0)) (realJet (fieldOf hh) (scalarOf dd) (vectorOf vv) z) :=
  @IsWeightedData.synthesis_form

example : ∀ {B : Background} {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      ∀ (L : EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ →ₗ[ℂ] ScalarVectorTensor.Mat3 ℂ)
        {t : ℝ},
        t ∈ B.I →
          ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (α β : Fin 3),
            timeDeriv (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => (L ξ) (hh t ξ) α β) t ξ =
              (L ξ) (jet1 hh t ξ) α β :=
  @IsWeightedData.timeDeriv_linearMap

example : ∀ {B : Background} {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      ∀ (L : EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ →ₗ[ℂ] ScalarVectorTensor.Mat3 ℂ)
        {t : ℝ},
        t ∈ B.I →
          ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (α β : Fin 3),
            timeDeriv (timeDeriv fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => (L ξ) (hh t ξ) α β) t
                ξ =
              (L ξ) (jet2 hh t ξ) α β :=
  @IsWeightedData.timeDeriv_timeDeriv_linearMap

example : ∀ {z : MinkowskiModel 3} {B : Background}
    {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
    {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
    IsWeightedData B.I hh dd vv →
      z ∈ slab B.I →
        ∀ (α : Fin 3), vectorOf vv z α = vectorOf (longData vv) z α + vectorOf (transData vv) z α :=
  @IsWeightedData.vectorOf_eq_add

example : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ :=
  @bumpMetric

example : EuclideanSpace ℝ (Fin 3) → ℂ :=
  @bumpProfile

example : MinkowskiModel 3 → ℝ :=
  @bumpScalar

example : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ) :=
  @bumpSchwartz

example : MinkowskiModel 3 → Fin 3 → ℝ :=
  @bumpVector

example : ContDiff ℝ ∞ bumpProfile :=
  @contDiff_bumpProfile

example : ∀ (α β : Fin 3),
    ContinuousOn (fun (ξ : EuclideanSpace ℝ (Fin 3)) => ScalarVectorTensor.longProj (wave ξ) α β)
      nonzero :=
  @continuousOn_longProj_wave

example : Continuous fourierBump :=
  @continuous_fourierBump

example : ∀ (c : Fin 4) (G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ), dsym c G = partialSymbol c G :=
  @dsym_eq_partialSymbol

example : ∀ {ε : ℝ},
    0 < ε → ∀ (t : ℝ), ∃ (ξ : EuclideanSpace ℝ (Fin 3)), ‖ξ‖ < ε ∧ gaugeData t ξ ≠ 0 :=
  @exists_gaugeData_ne_zero

example : EuclideanSpace ℝ (Fin 3) → ℂ :=
  @fourierBump

example : fourierBump = ⇑(𝓕 bumpSchwartz : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :=
  @fourierBump_eq

example : ∀ (ξ : EuclideanSpace ℝ (Fin 3)), fourierBump (-ξ) = (starRingEnd ℂ) (fourierBump ξ) :=
  @fourierBump_neg

example : fourierBump 0 = ((∫ (x : EuclideanSpace ℝ (Fin 3)), unitBump x : ℝ) : ℂ) :=
  @fourierBump_zero

example : fourierBump 0 ≠ 0 :=
  @fourierBump_zero_ne_zero

example : ∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) (α β : Fin 3),
    fourierMetric bumpMetric t ξ α β = fourierBump ξ :=
  @fourierMetric_bump

example : ∀ (t : ℝ), fourierScalar bumpScalar t = fourierBump :=
  @fourierScalar_bump

example : ∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) (α : Fin 3),
    fourierVector bumpVector t ξ α = fourierBump ξ :=
  @fourierVector_bump

example : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ :=
  @gaugeData

example : ∀ {s : ℝ},
    0 < s → ∀ (t : ℝ), gaugeData t (s • Packet.ξ₀) 2 2 = fourierBump (s • Packet.ξ₀) :=
  @gaugeData_smul_ξ₀

example : HasCompactSupport bumpProfile :=
  @hasCompactSupport_bumpProfile

example : ∀ (I : Set ℝ), HasIntegrableSpectrum I bumpMetric bumpScalar bumpVector :=
  @hasIntegrableSpectrum_bump

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {k : ℕ},
    IsOpen I →
      IsWeightedAmplitude I (k + 1) G → ∀ (c : Fin 4), IsWeightedAmplitude I k (dsym c G) :=
  @isWeightedAmplitude_dsym

example : ∀ (I : Set ℝ) (k : ℕ), IsWeightedAmplitude I k fun (_ : ℝ) => fourierBump :=
  @isWeightedAmplitude_fourierBump

example : ∀ {I : Set ℝ} {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ} {k : ℕ},
    IsOpen I →
      ∀ (L : EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ →ₗ[ℂ] ScalarVectorTensor.Mat3 ℂ),
        (∀ (γ δ α β : Fin 3),
            ContinuousOn
              (fun (ξ : EuclideanSpace ℝ (Fin 3)) => (L ξ) (Pi.single γ (Pi.single δ 1)) α β)
              nonzero) →
          (∀ (c : ℝ), 0 < c → ∀ (ξ : EuclideanSpace ℝ (Fin 3)), L (c • ξ) = L ξ) →
            (∀ (γ δ : Fin 3), IsWeightedAmplitude I k (amp hh γ δ)) →
              ∀ (α β : Fin 3),
                IsWeightedAmplitude I k fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
                  (L ξ) (hh t ξ) α β :=
  @isWeightedAmplitude_linearMap

example : ∀ {I : Set ℝ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ} {k : ℕ},
    IsOpen I →
      ∀ (L : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℂ) →ₗ[ℂ] Fin 3 → ℂ),
        (∀ (γ α : Fin 3),
            ContinuousOn (fun (ξ : EuclideanSpace ℝ (Fin 3)) => (L ξ) (Pi.single γ 1) α) nonzero) →
          (∀ (c : ℝ), 0 < c → ∀ (ξ : EuclideanSpace ℝ (Fin 3)), L (c • ξ) = L ξ) →
            (∀ (γ : Fin 3), IsWeightedAmplitude I k (vamp vv γ)) →
              ∀ (α : Fin 3),
                IsWeightedAmplitude I k fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
                  (L ξ) (vv t ξ) α :=
  @isWeightedAmplitude_linearMap_vec

example : ∀ {I : Set ℝ},
    IsOpen I →
      IsWeightedData I gaugeData (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0)
        fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) (_ : Fin 3) => 0 :=
  @isWeightedData_gaugeData

example : ∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)), jet1 gaugeData t ξ = 0 :=
  @jet1_gaugeData

example : ∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)), jet2 gaugeData t ξ = 0 :=
  @jet2_gaugeData

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ},
    (FLRW.metric B.toData).IsEinstein κ 0 (FLRW.perfectFluidStress B.toData ρ fun (_ : ℝ) => 0) →
      LinearizedEinsteinDust B κ ρ (fieldOf gaugeData) (fun (_ : MinkowskiModel 3) => 0)
        fun (_ : MinkowskiModel 3) (_ : Fin 3) => 0 :=
  @linearizedEinsteinDust_gaugeData

example : ∀ {c : ℝ},
    0 < c →
      ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (α β : Fin 3),
        ScalarVectorTensor.longProj (wave (c • ξ)) α β = ScalarVectorTensor.longProj (wave ξ) α β :=
  @longProj_wave_smul

example : ScalarVectorTensor.longProj (wave Packet.ξ₀) 2 2 = 1 :=
  @longProj_wave_ξ₀

example : ∀ {c : ℝ},
    0 < c →
      ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
        ScalarVectorTensor.longVec (wave (c • ξ)) = ScalarVectorTensor.longVec (wave ξ) :=
  @longVec_wave_smul

example : ∀ {I : Set ℝ} {t : ℝ},
    t ∈ I →
      ∀ {K : Set (EuclideanSpace ℝ (Fin 3))},
        0 ∉ K → ¬HasCompactSpectrum I K bumpMetric bumpScalar bumpVector :=
  @not_hasCompactSpectrum_bump

example : ∀ {I : Set ℝ} {t : ℝ},
    t ∈ I →
      ∀ {K : Set (EuclideanSpace ℝ (Fin 3))},
        IsCompact K →
          0 ∉ K →
            ¬IsFourierData I K gaugeData (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0)
                fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) (_ : Fin 3) => 0 :=
  @not_isFourierData_gaugeData

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {z : MinkowskiModel 3},
    IsOpen I →
      IsWeightedAmplitude I 1 G →
        IsHermitian I G →
          z ∈ slab I →
            ∀ (c : Fin 4),
              ↑((fderiv ℝ (fun (w : MinkowskiModel 3) => (synthesis G w).re) z) (Pi.single c 1)) =
                synthesis (dsym c G) z :=
  @ofReal_fderiv_re_of_isAmplitude

example : ∀ {c : ℝ},
    0 < c →
      ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
        ScalarVectorTensor.scalarPart (wave (c • ξ)) = ScalarVectorTensor.scalarPart (wave ξ) :=
  @scalarPart_wave_smul

example : ∀ {c : ℝ},
    0 < c →
      ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
        ScalarVectorTensor.tensorPart (wave (c • ξ)) = ScalarVectorTensor.tensorPart (wave ξ) :=
  @tensorPart_wave_smul

example : ∀ {c : ℝ},
    0 < c →
      ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
        ScalarVectorTensor.transVec (wave (c • ξ)) = ScalarVectorTensor.transVec (wave ξ) :=
  @transVec_wave_smul

example : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) :=
  @unitBump

example : ∀ {c : ℝ},
    0 < c →
      ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
        ScalarVectorTensor.vectorPart (wave (c • ξ)) = ScalarVectorTensor.vectorPart (wave ξ) :=
  @vectorPart_wave_smul

example : ∀ (c : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)), wave (c • ξ) = ↑c • wave ξ :=
  @wave_smul

end ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Reconstruction
