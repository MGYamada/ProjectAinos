/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.PerturbationReconstruction
import ProjectAinos.GeneralRelativity.PerturbationModeSplit
import ProjectAinos.GeneralRelativity.PerturbationPacket
import ProjectAinos.GeneralRelativity.PerturbationGaugeSector
import ProjectAinos.GeneralRelativity.CurvedScalarReconstruction

/-! Public consumers of the reconstruction of a flat cosmological perturbation from its scalar,
vector and tensor modes (Landau–Lifshitz, §115): the scalar–vector–tensor projections of a
`3 × 3` matrix and the symbols of the linearized equations, the Fourier synthesis of amplitudes
with a fixed compact spectrum, the equivalence of the linearized Einstein equations with dust and
the equations of the frequencies, the decomposition into the three sectors, the reconstruction by
Fourier inversion, the split of a single plane wave into the scalar, vector and tensor modes, and
a test packet with scalar and tensor components.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

universe u_1 u_2 u_3

open Set Filter Function MeasureTheory
open scoped ContDiff Topology ComplexConjugate FourierTransform RealInnerProductSpace SchwartzMap

namespace ProjectAinos.SmoothGeometry.ScalarVectorTensor

example : (K : Type u_1) → [Field K] → Mat3 K :=
  @delta

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → contract n ((tensorPart n) M) = 0 :=
  @contract_tensorPart

example : ∀ {K : Type u_1} [Field K] (n V W : Fin 3 → K), dot n (V - W) = dot n V - dot n W :=
  @dot_sub

example : ∀ {K : Type u_1} [Field K] (n V : Fin 3 → K) [CharZero K],
  (transVec (-n)) V = (transVec n) V :=
  @transVec_neg

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → longCoeff n ((vectorPart n) M) = 0 :=
  @longCoeff_vectorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K}, nsq n ≠ 0 → trace (longProj n) = 1 :=
  @trace_longProj

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → shear n ((scalarPart n) M) = 0 :=
  @shear_scalarPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K}, nsq n ≠ 0 → contract n (longProj n) = n :=
  @contract_longProj

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (P : Coeffs K) (F₀ F₁ F₂ : Mat3 K) (D : K)
  [CharZero K],
  nsq n ≠ 0 →
    resSpace P n ((vectorPart n) F₀) ((vectorPart n) F₁) ((vectorPart n) F₂) 0 =
      (vectorPart n) (resSpace P n F₀ F₁ F₂ D) :=
  @resSpace_vectorPart

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → K :=
  @nsq

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K),
  dot n ((mix n) M) = sandwich n M - nsq n * trace M :=
  @dot_mix

example : ∀ {K : Type u_1} [Field K] (n V : Fin 3 → K) (α : Fin 3),
  (longVec n) V α = dot n V / nsq n * n α :=
  @longVec_apply

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} [CharZero K],
  nsq n ≠ 0 → (tensorPart n) (delta K) = 0 :=
  @tensorPart_delta

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (V : Fin 3 → K),
  nsq n ≠ 0 → (transVec n) ((longVec n) V) = 0 :=
  @transVec_longVec

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (scalarPart n) ((tensorPart n) M) = 0 :=
  @scalarPart_tensorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (transVec n) ((mix n) M) = (mix n) ((vectorPart n) M) :=
  @transVec_mix

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → (Fin 3 → K) →ₗ[K] Fin 3 → K :=
  @longVec

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K),
  (scalarPart n) M + (vectorPart n) M + (tensorPart n) M = M :=
  @scalarPart_add_vectorPart_add_tensorPart

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → Mat3 K →ₗ[K] Mat3 K :=
  @tensorPart

example : ∀ {K : Type u_1} [Field K] (n v : Fin 3 → K) (β : Fin 3),
  ∑ γ : Fin 3, n γ * (n γ * v β + v γ * n β) = nsq n * v β + dot n v * n β :=
  @sum_mul_sym

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) [CharZero K] (α β : Fin 3),
  (scalarPart n) M α β = (scalarPart n) M β α :=
  @scalarPart_symm

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (op n) ((tensorPart n) M) = nsq n • (tensorPart n) M :=
  @op_tensorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M N : Mat3 K),
  shear n (M + N) = shear n M + shear n N :=
  @shear_add

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → (Fin 3 → K) →ₗ[K] Fin 3 → K :=
  @transVec

example : ∀ {K : Type u_1} [Field K] (n V : Fin 3 → K) [CharZero K],
  (longVec (-n)) V = (longVec n) V :=
  @longVec_neg

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) [CharZero K],
  (tensorPart (-n)) M = (tensorPart n) M :=
  @tensorPart_neg

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K),
  nsq n ≠ 0 → longCoeff n ((op n) M) = nsq n * trace M - sandwich n M :=
  @longCoeff_op

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K), ∑ γ : Fin 3, n γ * n γ = nsq n :=
  @sum_mul_self

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) [CharZero K],
  (scalarPart (-n)) M = (scalarPart n) M :=
  @scalarPart_neg

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) [CharZero K],
  (vectorPart (-n)) M = (vectorPart n) M :=
  @vectorPart_neg

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) [CharZero K] (α β : Fin 3),
  (vectorPart n) M α β = (vectorPart n) M β α :=
  @vectorPart_symm

example : {K : Type u_1} →
  [Field K] → Coeffs K → (Fin 3 → K) → Mat3 K → Mat3 K → Mat3 K → K → (Fin 3 → K) → Prop :=
  @SymbolEq

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K}, nsq n ≠ 0 → shear n (longProj n) = 0 :=
  @shear_longProj

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (tensorPart n) ((op n) M) = (op n) ((tensorPart n) M) :=
  @tensorPart_op

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) (α β : Fin 3),
  (vectorPart n) M α β = (n α * shear n M β + shear n M α * n β) / nsq n :=
  @vectorPart_apply

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K), contract n 0 = 0 :=
  @contract_zero

example : ∀ {K : Type u_1} [Field K] (M N : Mat3 K), trace (M - N) = trace M - trace N :=
  @trace_sub

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (V : Fin 3 → K),
  nsq n ≠ 0 → dot n ((longVec n) V) = dot n V :=
  @dot_longVec

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K}, nsq n ≠ 0 → (op n) (longProj n) = 0 :=
  @op_longProj

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K), dot n n = nsq n :=
  @dot_self

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (longVec n) ((mix n) M) = (mix n) ((scalarPart n) M) :=
  @longVec_mix

example : ∀ {K : Type u_1} [Field K] (L : (Fin 3 → K) →ₗ[K] Fin 3 → K) (V : Fin 3 → K) (α : Fin 3),
  L V α = ∑ γ : Fin 3, V γ * L (Pi.single γ 1) α :=
  @linearMap_vec_apply_eq_sum

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → shear n ((tensorPart n) M) = 0 :=
  @shear_tensorPart

example : ∀ {K : Type u_1} [Field K] (n V W : Fin 3 → K), dot n (V + W) = dot n V + dot n W :=
  @dot_add

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K}, nsq n ≠ 0 → sandwich n (longProj n) = nsq n :=
  @sandwich_longProj

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → Mat3 K → Fin 3 → K :=
  @contract

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (c : K) (V : Fin 3 → K),
  dot n (c • V) = c * dot n V :=
  @dot_smul

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → ((vectorPart n) M = 0 ↔ shear n M = 0) :=
  @vectorPart_eq_zero_iff

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (vectorPart n) ((scalarPart n) M) = 0 :=
  @vectorPart_scalarPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) (σ : K →+* K),
  (∀ (γ : Fin 3), σ (n γ) = n γ) →
    ∀ (β : Fin 3), shear n (fun (α β : Fin 3) => σ (M α β)) β = σ (shear n M β) :=
  @shear_map

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) (c : K),
  shear n (c • M) = c • shear n M :=
  @shear_smul

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M N : Mat3 K),
  sandwich n (M + N) = sandwich n M + sandwich n N :=
  @sandwich_add

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → Mat3 K →ₗ[K] Mat3 K :=
  @vectorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → trace ((tensorPart n) M) = 0 :=
  @trace_tensorPart

example : {K : Type u_1} → [Field K] → Coeffs K → Mat3 K → Mat3 K → K → K :=
  @resTime

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) (c : K),
  contract n (c • M) = c • contract n M :=
  @contract_smul

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K] (α β : Fin 3),
  (scalarPart n) M α β =
    (3 * longCoeff n M - trace M) / 2 * (n α * n β / nsq n - delta K α β / 3) +
      trace M * (delta K α β / 3) :=
  @scalarPart_eq

example : ∀ {K : Type u_1} [Field K], trace (0 : Mat3 K) = 0 :=
  @trace_zero

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (P : Coeffs K) (F₁ : Mat3 K) (V : Fin 3 → K)
  [CharZero K],
  nsq n ≠ 0 →
    resMixed P n ((vectorPart n) F₁) ((transVec n) V) = (transVec n) (resMixed P n F₁ V) :=
  @resMixed_vectorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → trace ((scalarPart n) M) = trace M :=
  @trace_scalarPart

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K), nsq (-n) = nsq n :=
  @nsq_neg

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (scalarPart n) ((vectorPart n) M) = 0 :=
  @scalarPart_vectorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (V : Fin 3 → K) [CharZero K] (σ : K →+* K),
  (∀ (γ : Fin 3), σ (n γ) = n γ) →
    ∀ (α : Fin 3), (transVec n) (fun (γ : Fin 3) => σ (V γ)) α = σ ((transVec n) V α) :=
  @transVec_map

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K] (σ : K →+* K),
  (∀ (γ : Fin 3), σ (n γ) = n γ) →
    ∀ (α β : Fin 3),
      (scalarPart n) (fun (α β : Fin 3) => σ (M α β)) α β = σ ((scalarPart n) M α β) :=
  @scalarPart_map

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) (α : Fin 3),
  (mix n) M α = contract n M α - n α * trace M :=
  @mix_apply

example : ∀ {K : Type u_1} [Field K] (P : Coeffs K) (n : Fin 3 → K), SymbolEq P n 0 0 0 0 0 :=
  @symbolEq_zero

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → contract n ((vectorPart n) M) = shear n M :=
  @contract_vectorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (op n) ((vectorPart n) M) = 0 :=
  @op_vectorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K),
  nsq n ≠ 0 → trace ((vectorPart n) M) = 0 :=
  @trace_vectorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} [CharZero K],
  nsq n ≠ 0 → (scalarPart n) (delta K) = delta K :=
  @scalarPart_delta

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M N : Mat3 K),
  contract n (M - N) = contract n M - contract n N :=
  @contract_sub

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M N : Mat3 K),
  contract n (M + N) = contract n M + contract n N :=
  @contract_add

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K),
  nsq n ≠ 0 → shear n ((op n) M) = 0 :=
  @shear_op

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (scalarPart n) ((scalarPart n) M) = (scalarPart n) M :=
  @scalarPart_scalarPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) (σ : K →+* K),
  (∀ (γ : Fin 3), σ (n γ) = n γ) →
    (longCoeff n fun (α β : Fin 3) => σ (M α β)) = σ (longCoeff n M) :=
  @longCoeff_map

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K), sandwich n (delta K) = nsq n :=
  @sandwich_delta

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) (α β : Fin 3),
  (op n) M α β =
    nsq n * M α β + n α * n β * trace M - n α * contract n M β - n β * contract n M α :=
  @op_apply

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (P : Coeffs K) (F₀ F₁ F₂ : Mat3 K)
  (V : Fin 3 → K) [CharZero K],
  nsq n ≠ 0 →
    (SymbolEq P n ((vectorPart n) F₀) ((vectorPart n) F₁) ((vectorPart n) F₂) 0
        ((transVec n) V) ↔
      P.mixC • shear n F₁ + P.dens • (transVec n) V = 0 ∧
        (P.c₁ - P.src) • (vectorPart n) F₀ + P.c₂ • (vectorPart n) F₁ +
            P.c₃ • (vectorPart n) F₂ =
          0) :=
  @symbolEq_vector_iff

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K] (σ : K →+* K),
  (∀ (γ : Fin 3), σ (n γ) = n γ) →
    ∀ (α β : Fin 3),
      (tensorPart n) (fun (α β : Fin 3) => σ (M α β)) α β = σ ((tensorPart n) M α β) :=
  @tensorPart_map

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (vectorPart n) ((op n) M) = (op n) ((vectorPart n) M) :=
  @vectorPart_op

example : ∀ {K : Type u_1} [Field K] (M N : Mat3 K), trace (M + N) = trace M + trace N :=
  @trace_add

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → contract n ((scalarPart n) M) = fun (β : Fin 3) => longCoeff n M * n β :=
  @contract_scalarPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → longCoeff n ((scalarPart n) M) = longCoeff n M :=
  @longCoeff_scalarPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (tensorPart n) ((scalarPart n) M) = 0 :=
  @tensorPart_scalarPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (tensorPart n) ((vectorPart n) M) = 0 :=
  @tensorPart_vectorPart

example : {K : Type u_1} → [Field K] → Coeffs K → (Fin 3 → K) → Mat3 K → (Fin 3 → K) → Fin 3 → K :=
  @resMixed

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (tensorPart n) ((tensorPart n) M) = (tensorPart n) M :=
  @tensorPart_tensorPart

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K), shear (-n) M = -shear n M :=
  @shear_neg

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K}, nsq n ≠ 0 → shear n (delta K) = 0 :=
  @shear_delta

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → sandwich n ((tensorPart n) M) = 0 :=
  @sandwich_tensorPart

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (c : K),
  (dot n fun (β : Fin 3) => c * n β) = c * nsq n :=
  @dot_smul_self

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → sandwich n ((vectorPart n) M) = 0 :=
  @sandwich_vectorPart

example : ∀ {K : Type u_1} [Field K], trace (delta K) = 3 :=
  @trace_delta

example : Type u_1 → Type u_1 :=
  @Mat3

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → shear n ((vectorPart n) M) = shear n M :=
  @shear_vectorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K},
  nsq n ≠ 0 → (scalarPart n) (longProj n) = longProj n :=
  @scalarPart_longProj

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (scalarPart n) ((op n) M) = (op n) ((scalarPart n) M) :=
  @scalarPart_op

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (V : Fin 3 → K),
  nsq n ≠ 0 → dot n ((transVec n) V) = 0 :=
  @dot_transVec

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → Mat3 K → K :=
  @sandwich

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → Mat3 K :=
  @longProj

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K),
  dot n (contract n M) = sandwich n M :=
  @dot_contract

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (P : Coeffs K) (F₁ F₂ : Mat3 K) (D : K)
  [CharZero K],
  nsq n ≠ 0 → resTime P ((scalarPart n) F₁) ((scalarPart n) F₂) D = resTime P F₁ F₂ D :=
  @resTime_scalarPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K),
  (tensorPart n) M = M - (scalarPart n) M - (vectorPart n) M :=
  @tensorPart_eq

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (V : Fin 3 → K),
  nsq n ≠ 0 → (longVec n) ((transVec n) V) = 0 :=
  @longVec_transVec

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (vectorPart n) ((tensorPart n) M) = 0 :=
  @vectorPart_tensorPart

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → Mat3 K →ₗ[K] Fin 3 → K :=
  @mix

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K), contract n (delta K) = n :=
  @contract_delta

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) (α β : Fin 3),
  (tensorPart n) M α β = M α β - (scalarPart n) M α β - (vectorPart n) M α β :=
  @tensorPart_apply

example : ∀ {K : Type u_1} [Field K] (L : Mat3 K →ₗ[K] Mat3 K) (M : Mat3 K) (α β : Fin 3),
  L M α β = ∑ γ : Fin 3, ∑ δ : Fin 3, M γ δ * L (Pi.single γ (Pi.single δ 1)) α β :=
  @linearMap_apply_eq_sum

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K),
  nsq n ≠ 0 → dot n (shear n M) = 0 :=
  @dot_shear

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K), longCoeff (-n) M
    = longCoeff n M :=
  @longCoeff_neg

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (vectorPart n) ((vectorPart n) M) = (vectorPart n) M :=
  @vectorPart_vectorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K}, nsq n ≠ 0 → (vectorPart n) (delta K) = 0 :=
  @vectorPart_delta

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K),
  contract n ((op n) M) = fun (β : Fin 3) => (nsq n * trace M - sandwich n M) * n β :=
  @contract_op

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K}, nsq n ≠ 0 → (vectorPart n) (longProj n) = 0 :=
  @vectorPart_longProj

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (P : Coeffs K) (F₁ F₂ : Mat3 K),
  nsq n ≠ 0 → resTime P ((vectorPart n) F₁) ((vectorPart n) F₂) 0 = 0 :=
  @resTime_vectorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (V : Fin 3 → K) [CharZero K] (σ : K →+* K),
  (∀ (γ : Fin 3), σ (n γ) = n γ) →
    ∀ (α : Fin 3), (longVec n) (fun (γ : Fin 3) => σ (V γ)) α = σ ((longVec n) V α) :=
  @longVec_map

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) (α β : Fin 3),
  (scalarPart n) M α β =
    longCoeff n M * (n α * n β / nsq n) +
      (trace M - longCoeff n M) / 2 * (delta K α β - n α * n β / nsq n) :=
  @scalarPart_apply

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K), sandwich n 0 = 0 :=
  @sandwich_zero

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K), dot n 0 = 0 :=
  @dot_zero

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (P : Coeffs K) (F₀ F₁ F₂ : Mat3 K) (D : K)
  [CharZero K],
  nsq n ≠ 0 →
    resSpace P n ((scalarPart n) F₀) ((scalarPart n) F₁) ((scalarPart n) F₂) D =
      (scalarPart n) (resSpace P n F₀ F₁ F₂ D) :=
  @resSpace_scalarPart

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) [CharZero K],
  (∀ (α β : Fin 3), M α β = M β α) →
    ∀ (α β : Fin 3), (tensorPart n) M α β = (tensorPart n) M β α :=
  @tensorPart_symm

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K] (σ : K →+* K),
  (∀ (γ : Fin 3), σ (n γ) = n γ) →
    ∀ (α β : Fin 3),
      (vectorPart n) (fun (α β : Fin 3) => σ (M α β)) α β = σ ((vectorPart n) M α β) :=
  @vectorPart_map

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (mix n) ((vectorPart n) M) = shear n M :=
  @mix_vectorPart

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M N : Mat3 K),
  sandwich n (M - N) = sandwich n M - sandwich n N :=
  @sandwich_sub

example : {K : Type u_1} → [Field K] → Mat3 K → K :=
  @trace

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (V : Fin 3 → K),
  nsq n ≠ 0 → (longVec n) ((longVec n) V) = (longVec n) V :=
  @longVec_longVec

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K}, nsq n ≠ 0 → (tensorPart n) (longProj n) = 0 :=
  @tensorPart_longProj

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → (Fin 3 → K) → K :=
  @dot

example : ∀ {K : Type u_1} [Field K] (n V : Fin 3 → K) (α : Fin 3),
  (transVec n) V α = V α - (longVec n) V α :=
  @transVec_apply

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (P : Coeffs K) (F₀ F₁ F₂ : Mat3 K)
  [CharZero K],
  nsq n ≠ 0 →
    (SymbolEq P n ((tensorPart n) F₀) ((tensorPart n) F₁) ((tensorPart n) F₂) 0 0 ↔
      (nsq n / 2 + P.c₁ - P.src) • (tensorPart n) F₀ + P.c₂ • (tensorPart n) F₁ +
          P.c₃ • (tensorPart n) F₂ =
        0) :=
  @symbolEq_tensor_iff

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (P : Coeffs K) (F₀ F₁ F₂ : Mat3 K) (D : K)
  (V : Fin 3 → K) [CharZero K],
  nsq n ≠ 0 →
    (SymbolEq P n F₀ F₁ F₂ D V ↔
      SymbolEq P n ((scalarPart n) F₀) ((scalarPart n) F₁) ((scalarPart n) F₂) D
          ((longVec n) V) ∧
        SymbolEq P n ((vectorPart n) F₀) ((vectorPart n) F₁) ((vectorPart n) F₂) 0
            ((transVec n) V) ∧
          SymbolEq P n ((tensorPart n) F₀) ((tensorPart n) F₁) ((tensorPart n) F₂) 0 0) :=
  @symbolEq_iff

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (P : Coeffs K) (F₁ F₂ : Mat3 K) [CharZero K],
  nsq n ≠ 0 → resTime P ((tensorPart n) F₁) ((tensorPart n) F₂) 0 = 0 :=
  @resTime_tensorPart

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → Mat3 K →ₗ[K] Mat3 K :=
  @scalarPart

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → Mat3 K → Fin 3 → K :=
  @shear

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K),
  sandwich n ((op n) M) = (nsq n * trace M - sandwich n M) * nsq n :=
  @sandwich_op

example : Type u_2 → Type u_2 :=
  @Coeffs

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → Mat3 K →ₗ[K] Mat3 K :=
  @op

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (P : Coeffs K) (F₁ : Mat3 K) (V : Fin 3 → K)
  [CharZero K],
  nsq n ≠ 0 → resMixed P n ((scalarPart n) F₁) ((longVec n) V) = (longVec n) (resMixed P n F₁ V) :=
  @resMixed_scalarPart

example : ∀ {K : Type u_1} [Field K] (M : Mat3 K) (c : K), trace (c • M) = c * trace M :=
  @trace_smul

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (P : Coeffs K) (F₀ F₁ F₂ : Mat3 K) (D : K)
  [CharZero K],
  nsq n ≠ 0 →
    resSpace P n ((tensorPart n) F₀) ((tensorPart n) F₁) ((tensorPart n) F₂) 0 =
      (tensorPart n) (resSpace P n F₀ F₁ F₂ D) :=
  @resSpace_tensorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K),
  trace ((op n) M) = 2 * (nsq n * trace M - sandwich n M) :=
  @trace_op

example : ∀ {K : Type u_1} [Field K] (n V : Fin 3 → K), (longVec n) V + (transVec n) V = V :=
  @longVec_add_transVec

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → longCoeff n ((tensorPart n) M) = 0 :=
  @longCoeff_tensorPart

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (V : Fin 3 → K),
  nsq n ≠ 0 → (transVec n) ((transVec n) V) = (transVec n) V :=
  @transVec_transVec

example : ∀ {K : Type u_1} [Field K] (n : Fin 3 → K) (M : Mat3 K) (c : K),
  sandwich n (c • M) = c * sandwich n M :=
  @sandwich_smul

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → (mix n) ((tensorPart n) M) = 0 :=
  @mix_tensorPart

example : {K : Type u_1} → [Field K] → (Fin 3 → K) → Mat3 K → K :=
  @longCoeff

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (M : Mat3 K) [CharZero K],
  nsq n ≠ 0 → sandwich n ((scalarPart n) M) = sandwich n M :=
  @sandwich_scalarPart

example : {K : Type u_1} → [Field K] → Coeffs K → (Fin 3 → K) → Mat3 K → Mat3 K → Mat3 K → K
    → Mat3 K :=
  @resSpace

example : ∀ {K : Type u_1} [Field K] {n : Fin 3 → K} (P : Coeffs K) (F₁ : Mat3 K) [CharZero K],
  nsq n ≠ 0 → resMixed P n ((tensorPart n) F₁) 0 = 0 :=
  @resMixed_tensorPart

end ProjectAinos.SmoothGeometry.ScalarVectorTensor

namespace ProjectAinos.SmoothGeometry.Fourier

example : ∀ {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {z : MinkowskiModel 3},
  (∀ (ξ : EuclideanSpace ℝ (Fin 3)), G (z 0) (-ξ) = (starRingEnd ℂ) (G (z 0) ξ)) →
    ↑(synthesis G z).re = synthesis G z :=
  @ofReal_re_synthesis

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G → ∀ {t : ℝ}, t ∈ I → ContDiff ℝ ∞ (G t) :=
  @IsCompactAmplitude.contDiff_slice

example : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)), spacetimePoint t x 0 = t :=
  @spacetimePoint_zero

example : ℝ → EuclideanSpace ℝ (Fin 3) → MinkowskiModel 3 :=
  @spacetimePoint

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) → MinkowskiModel 3 → ℂ :=
  @synthesis

example : ∀ {P : Type u_1} {V : Type u_2} {F : Type u_3} [NormedAddCommGroup P]
  [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : P → V → F} {U : Set P},
  IsOpen U →
    ContDiffOn ℝ 1 (↿Φ) (U ×ˢ Set.univ) →
      ∀ {p : P},
        p ∈ U →
          ∀ (ξ : V),
            HasFDerivAt (fun (q : P) => Φ q ξ)
              (fderiv ℝ ↿Φ (p, ξ) ∘SL ContinuousLinearMap.inl ℝ P V) p :=
  @hasFDerivAt_fderiv_uncurry

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsOpen I →
    IsCompactAmplitude I K G →
      ∀ {z : MinkowskiModel 3},
        z ∈ slab I →
          ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (v : MinkowskiModel 3) {D : ℂ},
            HasDerivAt (fun (s : ℝ) => synthesisIntegrand G (z + s • v) ξ) D 0 →
              (fderiv ℝ (fun (w : MinkowskiModel 3) => synthesisIntegrand G w ξ) z) v = D :=
  @fderiv_integrand_eq

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G → ∀ {t : ℝ}, t ∈ I → Continuous (G t) :=
  @IsCompactAmplitude.continuous

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsOpen I →
    IsCompact K →
      IsCompactAmplitude I K G →
        ∀ {z : MinkowskiModel 3},
          z ∈ slab I → (fderiv ℝ (synthesis G) z) (Pi.single 0 1) = synthesis (timeDeriv G) z :=
  @fderiv_synthesis_time

example : ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (z : MinkowskiModel 3),
  inner ℝ ξ (spatialPoint z) = ∑ γ : Fin 3, ξ.ofLp γ * z γ.succ :=
  @inner_spatialPoint

example : ∀ (z : MinkowskiModel 3),
    synthesis (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0) z = 0 :=
  @synthesis_zero

example : ∀ {P : Type u_1} {V : Type u_2} {F : Type u_3} [NormedAddCommGroup P]
  [NormedSpace ℝ P] [ProperSpace P] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {μ : MeasureTheory.Measure V} [MeasureTheory.IsFiniteMeasureOnCompacts μ]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : P → V → F} {U : Set P}
  {K : Set V},
  IsOpen U →
    IsCompact K →
      ContDiffOn ℝ 1 (↿Φ) (U ×ˢ Set.univ) →
        (∀ p ∈ U, ∀ ξ ∉ K, Φ p ξ = 0) →
          ∀ {p₀ : P},
            p₀ ∈ U →
              HasFDerivAt (fun (p : P) => ∫ (ξ : V), Φ p ξ ∂μ)
                (∫ (ξ : V), fderiv ℝ ↿Φ (p₀, ξ) ∘SL ContinuousLinearMap.inl ℝ P V ∂μ) p₀ :=
  @hasFDerivAt_integral_of_compact

example : ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] (Λ : ℝ → (ι → ℂ) →ₗ[ℂ] ℂ)
  (G : ι → ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) {z : MinkowskiModel 3},
  (∀ (i : ι), MeasureTheory.Integrable (synthesisIntegrand (G i) z) MeasureTheory.volume) →
    synthesis (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => (Λ t) fun (i : ι) => G i t ξ) z =
      (Λ (z 0)) fun (i : ι) => synthesis (G i) z :=
  @synthesis_linearMap

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G →
    ∀ (c : ℂ), IsCompactAmplitude I K fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => c * G t ξ :=
  @IsCompactAmplitude.const_mul

example : MinkowskiModel 3 →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  @spatialPoint

example : ∀ {G₁ G₂ : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {z : MinkowskiModel 3},
  MeasureTheory.Integrable (synthesisIntegrand G₁ z) MeasureTheory.volume →
    MeasureTheory.Integrable (synthesisIntegrand G₂ z) MeasureTheory.volume →
      synthesis (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => G₁ t ξ - G₂ t ξ) z =
        synthesis G₁ z - synthesis G₂ z :=
  @synthesis_sub

example : ∀ {P : Type u_1} {V : Type u_2} {F : Type u_3} [NormedAddCommGroup P]
  [NormedSpace ℝ P] [ProperSpace P] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {μ : MeasureTheory.Measure V} [MeasureTheory.IsFiniteMeasureOnCompacts μ]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : P → V → F} {U : Set P}
  {K : Set V},
  IsOpen U →
    IsCompact K →
      ContDiffOn ℝ 1 (↿Φ) (U ×ˢ Set.univ) →
        (∀ p ∈ U, ∀ ξ ∉ K, Φ p ξ = 0) →
          ∀ {p₀ : P}, p₀ ∈ U → DifferentiableAt ℝ (fun (p : P) => ∫ (ξ : V), Φ p ξ ∂μ) p₀ :=
  @differentiableAt_integral_of_compact

example : ∀ {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {t : ℝ},
  Continuous (G t) →
    MeasureTheory.Integrable (G t) MeasureTheory.volume →
      (∀ (x : EuclideanSpace ℝ (Fin 3)), synthesis G (spacetimePoint t x) = 0) →
        ∀ (ξ : EuclideanSpace ℝ (Fin 3)), G t ξ = 0 :=
  @eq_zero_of_synthesis_eq_zero

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsOpen I →
    IsCompact K →
      IsCompactAmplitude I K G →
        ∀ {z : MinkowskiModel 3},
          z ∈ slab I →
            ∀ (γ : Fin 3),
              (fderiv ℝ (synthesis G) z) (Pi.single γ.succ 1) =
                synthesis
                  (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
                    2 * ↑Real.pi * ↑(ξ.ofLp γ) * Complex.I * G t ξ)
                  z :=
  @fderiv_synthesis_space

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G →
    IsCompact K →
      ∀ {t : ℝ},
        t ∈ I →
          MeasureTheory.Integrable
            (fun (x : EuclideanSpace ℝ (Fin 3)) => synthesis G (spacetimePoint t x))
            MeasureTheory.volume :=
  @integrable_synthesis_slice

example : ∀ {P : Type u_1} {V : Type u_2} {F : Type u_3} [NormedAddCommGroup P]
  [NormedSpace ℝ P] [ProperSpace P] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {μ : MeasureTheory.Measure V} [MeasureTheory.IsFiniteMeasureOnCompacts μ]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : P → V → F} {U : Set P}
  {K : Set V},
  IsOpen U →
    IsCompact K →
      ContDiffOn ℝ 1 (↿Φ) (U ×ˢ Set.univ) →
        (∀ p ∈ U, ∀ ξ ∉ K, Φ p ξ = 0) →
          ∀ {p₀ : P},
            p₀ ∈ U →
              ∀ (v : P),
                (fderiv ℝ (fun (p : P) => ∫ (ξ : V), Φ p ξ ∂μ) p₀) v =
                  ∫ (ξ : V), (fderiv ℝ (fun (p : P) => Φ p ξ) p₀) v ∂μ :=
  @fderiv_integral_apply

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G →
    IsOpen I →
      ∀ {t : ℝ},
        t ∈ I →
          ∀ (m : EuclideanSpace ℝ (Fin 3) → ℂ) (ξ : EuclideanSpace ℝ (Fin 3)),
            timeDeriv (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => m ξ * G t ξ) t ξ =
              m ξ * timeDeriv G t ξ :=
  @timeDeriv_mul_left

example : ∀ {G₁ G₂ : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {z : MinkowskiModel 3},
  MeasureTheory.Integrable (synthesisIntegrand G₁ z) MeasureTheory.volume →
    MeasureTheory.Integrable (synthesisIntegrand G₂ z) MeasureTheory.volume →
      synthesis (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => G₁ t ξ + G₂ t ξ) z =
        synthesis G₁ z + synthesis G₂ z :=
  @synthesis_add

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G →
    ∀ {z : MinkowskiModel 3},
      z ∈ slab I → ∀ {ξ : EuclideanSpace ℝ (Fin 3)}, ξ ∉ K → synthesisIntegrand G z ξ = 0 :=
  @IsCompactAmplitude.integrand_eq_zero

example : ∀ (z : MinkowskiModel 3) (γ : Fin 3), (spatialPoint z).ofLp γ = z γ.succ :=
  @spatialPoint_apply

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G →
    IsCompact K →
      ∀ (γ : Fin 3),
        IsCompactAmplitude I K fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
          2 * ↑Real.pi * ↑(ξ.ofLp γ) * Complex.I * G t ξ :=
  @IsCompactAmplitude.space

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsOpen I →
    IsCompactAmplitude I K G →
      ∀ {z : MinkowskiModel 3},
        z ∈ slab I →
          ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (γ : Fin 3),
            (fderiv ℝ (fun (w : MinkowskiModel 3) => synthesisIntegrand G w ξ) z)
                (Pi.single γ.succ 1) =
              synthesisIntegrand
                (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
                  2 * ↑Real.pi * ↑(ξ.ofLp γ) * Complex.I * G t ξ)
                z ξ :=
  @fderiv_integrand_space

example : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) (γ : Fin 3), spacetimePoint t x γ.succ
    = x.ofLp γ :=
  @spacetimePoint_succ

example : ∀ {ι : Type u_1} [Fintype ι] (c : ι → ℝ → ℂ) (G : ι → ℝ → EuclideanSpace ℝ (Fin 3) → ℂ)
  {z : MinkowskiModel 3},
  (∀ (i : ι), MeasureTheory.Integrable (synthesisIntegrand (G i) z) MeasureTheory.volume) →
    synthesis (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => ∑ i : ι, c i t * G i t ξ) z =
      ∑ i : ι, c i (z 0) * synthesis (G i) z :=
  @synthesis_fintype_sum

example : ∀ {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {z : MinkowskiModel 3},
  (∀ (ξ : EuclideanSpace ℝ (Fin 3)), G (z 0) (-ξ) = (starRingEnd ℂ) (G (z 0) ξ)) →
    (starRingEnd ℂ) (synthesis G z) = synthesis G z :=
  @conj_synthesis

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G →
    IsCompact K → ∀ {t : ℝ}, t ∈ I → MeasureTheory.Integrable (G t) MeasureTheory.volume :=
  @IsCompactAmplitude.integrable

example : ∀ (γ : Fin 3),
  ContDiff ℝ ∞ fun (ξ : EuclideanSpace ℝ (Fin 3)) => 2 * ↑Real.pi * ↑(ξ.ofLp γ) * Complex.I :=
  @contDiff_spaceMultiplier

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsHermitian I G →
    ∀ {m : EuclideanSpace ℝ (Fin 3) → ℂ},
      (∀ (ξ : EuclideanSpace ℝ (Fin 3)), m (-ξ) = (starRingEnd ℂ) (m ξ)) →
        IsHermitian I fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => m ξ * G t ξ :=
  @IsHermitian.mul_left

example : ∀ {I : Set ℝ} {G₁ G₂ : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsHermitian I G₁ →
    IsHermitian I G₂ →
      IsHermitian I fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => G₁ t ξ + G₂ t ξ :=
  @IsHermitian.add

example : ContDiff ℝ ∞ fun (q : MinkowskiModel 3 × EuclideanSpace ℝ (Fin 3)) =>
  Complex.exp (↑(2 * Real.pi * inner ℝ q.2 (spatialPoint q.1)) * Complex.I) :=
  @contDiff_phase

example : ∀ (G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)),
  synthesis G (spacetimePoint t x) = FourierTransformInv.fourierInv (G t) x :=
  @synthesis_spacetimePoint

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G → IsOpen I → IsCompactAmplitude I K (timeDeriv G) :=
  @IsCompactAmplitude.timeDeriv

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G →
    ∀ {f : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
      ContDiffOn ℝ ∞ (Function.uncurry f) (I ×ˢ Set.univ) →
        IsCompactAmplitude I K fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => f t ξ * G t ξ :=
  @IsCompactAmplitude.mul_smooth

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))},
  IsCompactAmplitude I K fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0 :=
  @IsCompactAmplitude.zero

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G →
    IsCompact K →
      ∀ {t : ℝ},
        t ∈ I →
          Continuous fun (x : EuclideanSpace ℝ (Fin 3)) => synthesis G (spacetimePoint t x) :=
  @continuous_synthesis_slice

example : ∀ {G₁ G₂ : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {z : MinkowskiModel 3},
  (∀ (ξ : EuclideanSpace ℝ (Fin 3)), G₁ (z 0) ξ = G₂ (z 0) ξ) → synthesis G₁ z = synthesis G₂ z :=
  @synthesis_congr

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) → ℝ → EuclideanSpace ℝ (Fin 3) → ℂ :=
  @timeDeriv

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {ι : Type u_1} (s : Finset ι)
  {G : ι → ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  (∀ i ∈ s, IsCompactAmplitude I K (G i)) →
    IsCompactAmplitude I K fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => ∑ i ∈ s, G i t ξ :=
  @IsCompactAmplitude.sum

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsOpen I → IsCompact K → IsCompactAmplitude I K G → ContDiffOn ℝ ∞ (synthesis G) (slab I) :=
  @contDiffOn_synthesis

example : ∀ {I : Set ℝ}, IsOpen I → IsOpen (slab I) :=
  @isOpen_slab

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G →
    IsCompact K →
      ∀ {t : ℝ},
        t ∈ I →
          (FourierTransform.fourier fun (x : EuclideanSpace ℝ (Fin 3)) =>
              synthesis G (spacetimePoint t x)) =
            G t :=
  @fourier_synthesis_slice

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G → ContDiffOn ℝ ∞ (↿(synthesisIntegrand G)) (slab I ×ˢ Set.univ) :=
  @IsCompactAmplitude.contDiffOn_integrand

example : Set ℝ → (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) → Prop :=
  @IsHermitian

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G →
    IsOpen I →
      ∀ {t : ℝ},
        t ∈ I →
          ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
            HasDerivAt (fun (s : ℝ) => G s ξ) (timeDeriv G t ξ) t :=
  @IsCompactAmplitude.hasDerivAt

example : ∀ (f : MinkowskiModel 3 → ℂ) {z : MinkowskiModel 3},
  (Continuous fun (x : EuclideanSpace ℝ (Fin 3)) => f (spacetimePoint (z 0) x)) →
    MeasureTheory.Integrable (fun (x : EuclideanSpace ℝ (Fin 3)) => f (spacetimePoint (z 0) x))
        MeasureTheory.volume →
      MeasureTheory.Integrable
          (FourierTransform.fourier fun (x : EuclideanSpace ℝ (Fin 3)) =>
            f (spacetimePoint (z 0) x))
          MeasureTheory.volume →
        synthesis
            (fun (t : ℝ) =>
              FourierTransform.fourier fun (x : EuclideanSpace ℝ (Fin 3)) =>
                f (spacetimePoint t x))
            z =
          f z :=
  @synthesis_fourier

example : ∀ {P : Type u_1} {V : Type u_2} {F : Type u_3} [NormedAddCommGroup P]
  [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : P → V → F} {U : Set P},
  ContDiffOn ℝ 1 (↿Φ) (U ×ˢ Set.univ) → ∀ {p : P}, p ∈ U → Continuous (Φ p) :=
  @continuous_of_contDiffOn

example : Set ℝ → Set (EuclideanSpace ℝ (Fin 3)) → (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) → Prop :=
  @IsCompactAmplitude

example : ∀ {I : Set ℝ} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsHermitian I G →
    ∀ (γ : Fin 3),
      IsHermitian I fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
        2 * ↑Real.pi * ↑(ξ.ofLp γ) * Complex.I * G t ξ :=
  @IsHermitian.space

example : ∀ {g : MinkowskiModel 3 → ℂ} {z : MinkowskiModel 3},
  DifferentiableAt ℝ g z →
    ∀ (v : MinkowskiModel 3),
      (fderiv ℝ (fun (w : MinkowskiModel 3) => (g w).re) z) v = ((fderiv ℝ g z) v).re :=
  @fderiv_re

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsOpen I →
    IsCompactAmplitude I K G →
      ∀ {z : MinkowskiModel 3},
        z ∈ slab I →
          ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
            (fderiv ℝ (fun (w : MinkowskiModel 3) => synthesisIntegrand G w ξ) z)
                (Pi.single 0 1) =
              synthesisIntegrand (timeDeriv G) z ξ :=
  @fderiv_integrand_time

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G →
    IsCompact K →
      ∀ {z : MinkowskiModel 3},
        z ∈ slab I → MeasureTheory.Integrable (synthesisIntegrand G z) MeasureTheory.volume :=
  @IsCompactAmplitude.integrable_integrand

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G → IsCompact K → ∀ {t : ℝ}, t ∈ I → HasCompactSupport (G t) :=
  @IsCompactAmplitude.hasCompactSupport

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsOpen I →
    IsCompact K →
      IsCompactAmplitude I K G →
        ∀ {z : MinkowskiModel 3},
          z ∈ slab I →
            ∀ (v : MinkowskiModel 3),
              (fderiv ℝ (synthesis G) z) v =
                ∫ (ξ : EuclideanSpace ℝ (Fin 3)),
                  (fderiv ℝ (fun (w : MinkowskiModel 3) => synthesisIntegrand G w ξ) z) v :=
  @fderiv_synthesis

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ}
  (hG : IsCompactAmplitude I K G) (hK : IsCompact K) {t : ℝ} (ht : t ∈ I),
  (fun (x : EuclideanSpace ℝ (Fin 3)) => synthesis G (spacetimePoint t x)) =
    ⇑(𝓕⁻ ((hG.hasCompactSupport hK ht).toSchwartzMap (hG.contDiff_slice ht) :
      𝓢(EuclideanSpace ℝ (Fin 3), ℂ)) : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ)) :=
  @synthesis_slice_eq_schwartz

example : ∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ),
  (∀ (x : EuclideanSpace ℝ (Fin 3)), (starRingEnd ℂ) (f x) = f x) →
    ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
      FourierTransform.fourier f (-ξ) = (starRingEnd ℂ) (FourierTransform.fourier f ξ) :=
  @fourier_neg_of_real

example : ∀ {P : Type u_1} {V : Type u_2} {F : Type u_3} [NormedAddCommGroup P]
  [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : MeasureTheory.Measure V}
  [MeasureTheory.IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {Φ : P → V → F} {U : Set P} {K : Set V},
  IsCompact K →
    ContDiffOn ℝ 1 (↿Φ) (U ×ˢ Set.univ) →
      (∀ p ∈ U, ∀ ξ ∉ K, Φ p ξ = 0) → ∀ {p : P}, p ∈ U → MeasureTheory.Integrable (Φ p) μ :=
  @integrable_of_contDiffOn

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsOpen I →
    IsCompact K →
      IsCompactAmplitude I K G →
        ∀ {z : MinkowskiModel 3}, z ∈ slab I → DifferentiableAt ℝ (synthesis G) z :=
  @differentiableAt_synthesis

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G₁ G₂ : ℝ
    → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G₁ →
    IsCompactAmplitude I K G₂ →
      IsCompactAmplitude I K fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => G₁ t ξ + G₂ t ξ :=
  @IsCompactAmplitude.add

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsHermitian I G → IsCompactAmplitude I K G → IsOpen I → IsHermitian I (timeDeriv G) :=
  @IsHermitian.timeDeriv

example : ∀ (z : MinkowskiModel 3), spacetimePoint (z 0) (spatialPoint z) = z :=
  @spacetimePoint_eq

example : Set ℝ → Set (MinkowskiModel 3) :=
  @slab

example : ∀ (G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (z : MinkowskiModel 3),
  synthesis G z = ∫ (ξ : EuclideanSpace ℝ (Fin 3)), synthesisIntegrand G z ξ :=
  @synthesis_eq

example : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)), spatialPoint (spacetimePoint t x) = x :=
  @spatialPoint_spacetimePoint

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsCompactAmplitude I K G →
    IsCompact K →
      ∀ {m : EuclideanSpace ℝ (Fin 3) → ℂ} {W : Set (EuclideanSpace ℝ (Fin 3))},
        IsOpen W →
          K ⊆ W →
            ContDiffOn ℝ ∞ m W →
              IsCompactAmplitude I K fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => m ξ * G t ξ :=
  @IsCompactAmplitude.mul_left

example : ∀ {P : Type u_1} {V : Type u_2} {F : Type u_3} [NormedAddCommGroup P]
  [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : P → V → F} {U : Set P}
  {K : Set V},
  IsOpen U →
    IsCompact K →
      (∀ p ∈ U, ∀ ξ ∉ K, Φ p ξ = 0) →
        ∀ {p : P}, p ∈ U → ∀ {ξ : V}, ξ ∉ K → fderiv ℝ ↿Φ (p, ξ) = 0 :=
  @fderiv_uncurry_eq_zero

example : ∀ (c : ℝ → ℂ) (G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (z : MinkowskiModel 3),
  synthesis (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => c t * G t ξ) z =
    c (z 0) * synthesis G z :=
  @synthesis_const_mul

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) → MinkowskiModel 3 → EuclideanSpace ℝ (Fin 3) → ℂ :=
  @synthesisIntegrand

end ProjectAinos.SmoothGeometry.Fourier

namespace ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Reconstruction

open ProjectAinos.SmoothGeometry ProjectAinos.SmoothGeometry.Fourier

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData I K hh dd vv →
    IsCompact K →
      0 ∉ K →
        ∀
          (L :
            EuclideanSpace ℝ (Fin 3) →
              ScalarVectorTensor.Mat3 ℂ →ₗ[ℂ] ScalarVectorTensor.Mat3 ℂ),
          (∀ (γ δ α β : Fin 3),
              ContDiffOn ℝ ∞
                (fun (ξ : EuclideanSpace ℝ (Fin 3)) => (L ξ) (Pi.single γ (Pi.single δ 1)) α β)
                nonzero) →
            ∀ (α β : Fin 3),
              IsCompactAmplitude I K fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
                (L ξ) (hh t ξ) α β :=
  @isCompactAmplitude_linearMap

example : Background → ℝ → (ℝ → ℝ) → ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ :=
  @timeForm

example : (ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ) → Fin 3 → ℝ → EuclideanSpace ℝ (Fin 3) → ℂ :=
  @vamp

example : ∀ (a b : ℝ) (w : ℂ),
  2 * ↑Real.pi * ↑a * Complex.I * (2 * ↑Real.pi * ↑b * Complex.I * w) =
    -(↑(2 * Real.pi * a) * ↑(2 * Real.pi * b) * w) :=
  @two_pi_I_mul

example : Fin 3 → JetIdx :=
  @JetIdx.velocity

example : IsOpen nonzero :=
  @isOpen_nonzero

example : ∀ (h : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ) (δ : MinkowskiModel 3 → ℝ)
  (v : MinkowskiModel 3 → Fin 3 → ℝ) (z : MinkowskiModel 3) (a a_1 : Fin 3),
  realJet h δ v z (JetIdx.value a a_1) = ↑(h z a a_1) :=
  @realJet.eq_3

example : ∀ (M : ScalarVectorTensor.Mat3 ℂ) (α β : Fin 3),
  ContDiffOn ℝ ∞
    (fun (ξ : EuclideanSpace ℝ (Fin 3)) => (ScalarVectorTensor.tensorPart (wave ξ)) M α β)
    nonzero :=
  @contDiffOn_tensorPart_wave

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
  {h : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ} {δ : MinkowskiModel 3 → ℝ}
  {v : MinkowskiModel 3 → Fin 3 → ℝ},
  HasCompactSpectrum B.I K h δ v →
    IsCompact K →
      0 ∉ K →
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
                    (fun (_ : MinkowskiModel 3) => 0)
                    fun (_ : MinkowskiModel 3) (_ : Fin 3) => 0) :=
  @HasCompactSpectrum.reconstruction

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))}, 0 ∉ K → K ⊆ nonzero :=
  @subset_nonzero

example : Type :=
  @JetIdx

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    ∀ {t : ℝ},
      t ∈ B.I → ∀ {ξ : EuclideanSpace ℝ (Fin 3)}, ξ ∉ K → FrequencyEq B κ ρ hh dd vv t ξ :=
  @frequencyEq_of_notMem

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} (h : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ)
  (δ : MinkowskiModel 3 → ℝ) (v : MinkowskiModel 3 → Fin 3 → ℝ) (z : MinkowskiModel 3)
  (α : Fin 3),
  ↑(linRicci B h z 0 α.succ - κ * linDust B ρ h δ v z 0 α.succ) =
      (mixedForm κ ρ (z 0) α) (realJet h δ v z) ∧
    ↑(linRicci B h z α.succ 0 - κ * linDust B ρ h δ v z α.succ 0) =
      (mixedForm κ ρ (z 0) α) (realJet h δ v z) :=
  @residual_mixed

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {z : MinkowskiModel 3} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K →
      z ∈ slab B.I →
        ∀ (c e : Fin 4) (α β : Fin 3),
          ↑(ddh (fieldOf hh) c e z α β) = synthesis (dsym c (dsym e (amp hh α β))) z :=
  @ofReal_ddh_fieldOf

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
  ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ :=
  @jet1

example : Type :=
  @JetIdx.proxyType

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) → MinkowskiModel 3 → ℝ :=
  @scalarOf

example : ∀ (M : ScalarVectorTensor.Mat3 ℂ) (α β : Fin 3),
  ContDiffOn ℝ ∞
    (fun (ξ : EuclideanSpace ℝ (Fin 3)) => (ScalarVectorTensor.vectorPart (wave ξ)) M α β)
    nonzero :=
  @contDiffOn_vectorPart_wave

example : (x x_1 : JetIdx) → Decidable (x = x_1) :=
  @instDecidableEqJetIdx.decEq

example : Fin 3 → Fin 3 → JetIdx :=
  @JetIdx.value

example : ∀ (hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ)
  (dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ)
  (a a_1 : Fin 3), jetAmp hh dd vv (JetIdx.value a a_1) = amp hh a a_1 :=
  @jetAmp.eq_3

example : Fin 4 → (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) → ℝ → EuclideanSpace ℝ (Fin 3) → ℂ :=
  @dsym

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {z : MinkowskiModel 3} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    z ∈ slab B.I → ∀ (α β : Fin 3), ↑(fieldOf hh z α β) = synthesis (amp hh α β) z :=
  @ofReal_fieldOf

example : Background → ℝ → (ℝ → ℝ) → ℝ → ScalarVectorTensor.Coeffs ℂ :=
  @fourierCoeffs

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsOpen I →
    IsCompactAmplitude I K G →
      ∀ {t : ℝ},
        t ∈ I →
          ∀ (γ : Fin 3) (ξ : EuclideanSpace ℝ (Fin 3)),
            dsym 0 (dsym γ.succ G) t ξ =
              2 * ↑Real.pi * ↑(ξ.ofLp γ) * Complex.I * timeDeriv G t ξ :=
  @dsym_zero_succ

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K →
      0 ∉ K →
        IsFourierData B.I K (vectorData hh) (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0)
          (transData vv) :=
  @isFourierData_vector

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    ∀ (L : EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ →ₗ[ℂ] ScalarVectorTensor.Mat3 ℂ)
      {t : ℝ},
      t ∈ B.I →
        ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
          jet1 (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => (L ξ) (hh t ξ)) t ξ =
            (L ξ) (jet1 hh t ξ) :=
  @jet1_linearMap

example : EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ :=
  @wave

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {z : MinkowskiModel 3} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K →
      0 ∉ K →
        z ∈ slab B.I →
          ∀ (α : Fin 3),
            vectorOf vv z α = vectorOf (longData vv) z α + vectorOf (transData vv) z α :=
  @vectorOf_eq_add

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K → ∀ (j : JetIdx), IsCompactAmplitude B.I K (jetAmp hh dd vv j) :=
  @isCompactAmplitude_jetAmp

example : ∀ (γ : Fin 3), ContDiff ℝ ∞ fun (ξ : EuclideanSpace ℝ (Fin 3)) => wave ξ γ :=
  @contDiff_wave

example : (MinkowskiModel 3 → ℝ) → ℝ → EuclideanSpace ℝ (Fin 3) → ℂ :=
  @fourierScalar

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
  (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) →
    (ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ) → JetIdx → ℝ → EuclideanSpace ℝ (Fin 3) → ℂ :=
  @jetAmp

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K →
      0 ∉ K →
        IsFourierData B.I K (tensorData hh) (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0)
          fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) (_ : Fin 3) => 0 :=
  @isFourierData_tensor

example : ∀ (G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ), dsym 0 G = timeDeriv G :=
  @dsym_zero

example : (vectorOf fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) (_ : Fin 3) => 0) =
  fun (_ : MinkowskiModel 3) (_ : Fin 3) => 0 :=
  @vectorOf_zero

example : ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (γ : Fin 3), (starRingEnd ℂ) (wave ξ γ) = wave ξ γ :=
  @conj_wave

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    ∀ (L : EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ →ₗ[ℂ] ScalarVectorTensor.Mat3 ℂ)
      {t : ℝ},
      t ∈ B.I →
        ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (α β : Fin 3),
          timeDeriv (timeDeriv fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => (L ξ) (hh t ξ) α β)
              t ξ =
            (L ξ) (jet2 hh t ξ) α β :=
  @timeDeriv_timeDeriv_linearMap

example : ∀ {f : EuclideanSpace ℝ (Fin 3) → ℂ},
  ContDiffOn ℝ ∞ f {ξ : EuclideanSpace ℝ (Fin 3) | ξ ≠ 0} →
    ContDiffOn ℝ ∞
      (fun (ξ : EuclideanSpace ℝ (Fin 3)) => f ξ / ScalarVectorTensor.nsq (wave ξ))
      {ξ : EuclideanSpace ℝ (Fin 3) | ξ ≠ 0} :=
  @ContDiffOn.div_nsq_wave

example : JetIdx :=
  @JetIdx.density

example : ∀ (h : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ) (δ : MinkowskiModel 3 → ℝ)
  (v : MinkowskiModel 3 → Fin 3 → ℝ) (z : MinkowskiModel 3),
  realJet h δ v z JetIdx.density = ↑(δ z) :=
  @realJet.eq_4

example : ∀ (hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ)
  (dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ)
  (a : Fin 3), jetAmp hh dd vv (JetIdx.velocity a) = vamp vv a :=
  @jetAmp.eq_5

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K →
      0 ∉ K →
        ∀ {t : ℝ},
          t ∈ B.I →
            ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
              FrequencyEq B κ ρ hh dd vv t ξ ↔
                FrequencyEq B κ ρ (scalarData hh) dd (longData vv) t ξ ∧
                  FrequencyEq B κ ρ (vectorData hh)
                      (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0) (transData vv) t ξ ∧
                    FrequencyEq B κ ρ (tensorData hh)
                      (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0)
                      (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) (_ : Fin 3) => 0) t ξ :=
  @frequencyEq_iff_split

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ}
  (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)),
  ((timeForm B κ ρ t) fun (j : JetIdx) => jetAmp hh dd vv j t ξ) =
    ScalarVectorTensor.resTime (fourierCoeffs B κ ρ t) (jet1 hh t ξ) (jet2 hh t ξ) (dd t ξ) :=
  @timeForm_jetAmp

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    ∀ {t : ℝ},
      t ∈ B.I →
        ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (α : Fin 3),
          ((mixedForm κ ρ t α) fun (j : JetIdx) => jetAmp hh dd vv j t ξ) =
            ScalarVectorTensor.resMixed (fourierCoeffs B κ ρ t) (wave ξ) (jet1 hh t ξ) (vv t ξ)
              α :=
  @mixedForm_jetAmp

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData I K hh dd vv →
    IsCompact K →
      0 ∉ K →
        ∀ (L : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℂ) →ₗ[ℂ] Fin 3 → ℂ),
          (∀ (γ α : Fin 3),
              ContDiffOn ℝ ∞ (fun (ξ : EuclideanSpace ℝ (Fin 3)) => (L ξ) (Pi.single γ 1) α)
                nonzero) →
            ∀ (α : Fin 3),
              IsCompactAmplitude I K fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
                (L ξ) (vv t ξ) α :=
  @isCompactAmplitude_linearMap_vec

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} (h : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ)
  (δ : MinkowskiModel 3 → ℝ) (v : MinkowskiModel 3 → Fin 3 → ℝ) (z : MinkowskiModel 3),
  ↑(linRicci B h z 0 0 - κ * linDust B ρ h δ v z 0 0) = (timeForm B κ ρ (z 0)) (realJet h δ v z) :=
  @residual_time

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ}
  (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) (α β : Fin 3),
  ((spaceForm B κ ρ t α β) fun (j : JetIdx) => jetAmp hh dd vv j t ξ) =
    ScalarVectorTensor.resSpace (fourierCoeffs B κ ρ t) (wave ξ) (hh t ξ) (jet1 hh t ξ)
      (jet2 hh t ξ) (dd t ξ) α β :=
  @spaceForm_jetAmp

example : ∀ (M : ScalarVectorTensor.Mat3 ℂ),
  ContDiffOn ℝ ∞
    (fun (ξ : EuclideanSpace ℝ (Fin 3)) => ScalarVectorTensor.longCoeff (wave ξ) M) nonzero :=
  @contDiffOn_longCoeff_wave

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ}
  {z : MinkowskiModel 3},
  IsOpen I →
    IsCompact K →
      IsCompactAmplitude I K G →
        z ∈ slab I →
          ∀ (c : Fin 4), (fderiv ℝ (synthesis G) z) (Pi.single c 1) = synthesis (dsym c G) z :=
  @fderiv_synthesis_dsym

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
  ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ :=
  @jet2

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
  MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ :=
  @fieldOf

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    ∀ (L : EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ →ₗ[ℂ] ScalarVectorTensor.Mat3 ℂ)
      {t : ℝ},
      t ∈ B.I →
        ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
          jet2 (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => (L ξ) (hh t ξ)) t ξ =
            (L ξ) (jet2 hh t ξ) :=
  @jet2_linearMap

example : Fin 4 → Fin 4 → Fin 3 → Fin 3 → JetIdx :=
  @JetIdx.second

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {z : MinkowskiModel 3} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K →
      z ∈ slab B.I →
        realJet (fieldOf hh) (scalarOf dd) (vectorOf vv) z = fun (j : JetIdx) =>
          synthesis (jetAmp hh dd vv j) z :=
  @realJet_eq

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {z : MinkowskiModel 3} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K →
      z ∈ slab B.I →
        ∀ (Λ : ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ),
          synthesis
              (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
                (Λ t) fun (j : JetIdx) => jetAmp hh dd vv j t ξ)
              z =
            (Λ (z 0)) (realJet (fieldOf hh) (scalarOf dd) (vectorOf vv) z) :=
  @synthesis_form

example : ContDiff ℝ ∞ fun (ξ : EuclideanSpace ℝ (Fin 3)) => ScalarVectorTensor.nsq (wave ξ) :=
  @contDiff_nsq_wave

example : Fin 4 → Fin 3 → Fin 3 → JetIdx :=
  @JetIdx.first

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {z : MinkowskiModel 3} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K →
      z ∈ slab B.I →
        ∀ (c : Fin 4) (α β : Fin 3),
          ↑(dh (fieldOf hh) c z α β) = synthesis (dsym c (amp hh α β)) z :=
  @ofReal_dh_fieldOf

example : ∀ (L : ScalarVectorTensor.Mat3 ℂ →ₗ[ℂ] ScalarVectorTensor.Mat3 ℂ)
  {M : ℝ → ScalarVectorTensor.Mat3 ℂ} {M' : ScalarVectorTensor.Mat3 ℂ} {t : ℝ},
  (∀ (α β : Fin 3), HasDerivAt (fun (s : ℝ) => M s α β) (M' α β) t) →
    ∀ (α β : Fin 3), HasDerivAt (fun (s : ℝ) => L (M s) α β) (L M' α β) t :=
  @hasDerivAt_linearMap_apply

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} (h : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ)
  (δ : MinkowskiModel 3 → ℝ) (v : MinkowskiModel 3 → Fin 3 → ℝ) (z : MinkowskiModel 3)
  (α β : Fin 3),
  ↑(linRicci B h z α.succ β.succ - κ * linDust B ρ h δ v z α.succ β.succ) =
    (spaceForm B κ ρ (z 0) α β) (realJet h δ v z) :=
  @residual_space

example : ∀ (M : ScalarVectorTensor.Mat3 ℂ) (α β : Fin 3),
  ContDiffOn ℝ ∞
    (fun (ξ : EuclideanSpace ℝ (Fin 3)) => (ScalarVectorTensor.scalarPart (wave ξ)) M α β)
    nonzero :=
  @contDiffOn_scalarPart_wave

example : ∀ (M : ScalarVectorTensor.Mat3 ℂ) (β : Fin 3),
  ContDiffOn ℝ ∞
    (fun (ξ : EuclideanSpace ℝ (Fin 3)) => ScalarVectorTensor.shear (wave ξ) M β) nonzero :=
  @contDiffOn_shear_wave

example : (ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ) → ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ :=
  @longData

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
  {h : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ} {δ : MinkowskiModel 3 → ℝ}
  {v : MinkowskiModel 3 → Fin 3 → ℝ},
  HasCompactSpectrum B.I K h δ v →
    IsCompact K →
      (LinearizedEinsteinDust B κ ρ h δ v ↔
        ∀ t ∈ B.I,
          ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
            FrequencyEq B κ ρ (fourierMetric h) (fourierScalar δ) (fourierVector v) t ξ) :=
  @HasCompactSpectrum.linearizedEinsteinDust_iff

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ}
  {z : MinkowskiModel 3},
  IsOpen I →
    IsCompact K →
      IsCompactAmplitude I K G →
        IsHermitian I G →
          z ∈ slab I →
            ∀ (c : Fin 4),
              ↑((fderiv ℝ (fun (w : MinkowskiModel 3) => (synthesis G w).re) z)
                    (Pi.single c 1)) =
                synthesis (dsym c G) z :=
  @ofReal_fderiv_re

example : ∀ (G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (γ : Fin 3),
  dsym γ.succ G = fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
    2 * ↑Real.pi * ↑(ξ.ofLp γ) * Complex.I * G t ξ :=
  @dsym_succ

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {h : MinkowskiModel 3 → Fin 3
    → Fin 3 → ℝ}
  {δ : MinkowskiModel 3 → ℝ} {v : MinkowskiModel 3 → Fin 3 → ℝ},
  HasCompactSpectrum I K h δ v →
    IsFourierData I K (fourierMetric h) (fourierScalar δ) (fourierVector v) :=
  @HasCompactSpectrum.isFourierData

example : Background →
  ℝ →
    (ℝ → ℝ) →
      (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
        (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) →
          (ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ) → ℝ → EuclideanSpace ℝ (Fin 3) → Prop :=
  @FrequencyEq

example : (MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ) →
  (MinkowskiModel 3 → ℝ) → (MinkowskiModel 3 → Fin 3 → ℝ) → MinkowskiModel 3 → JetIdx → ℂ :=
  @realJet

example : (_ : Fin 4) × (_ : Fin 4) × (_ : Fin 3) × Fin 3 ⊕
    (_ : Fin 4) × (_ : Fin 3) × Fin 3 ⊕ (_ : Fin 3) × Fin 3 ⊕ Unit ⊕ Fin 3 ≃
  JetIdx :=
  @JetIdx.proxyTypeEquiv

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
  Fin 3 → Fin 3 → ℝ → EuclideanSpace ℝ (Fin 3) → ℂ :=
  @amp

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsOpen I →
    IsCompactAmplitude I K G → IsHermitian I G → ∀ (c : Fin 4), IsHermitian I (dsym c G) :=
  @isHermitian_dsym

example : ∀ (V : Fin 3 → ℂ) (α : Fin 3),
  ContDiffOn ℝ ∞
    (fun (ξ : EuclideanSpace ℝ (Fin 3)) => (ScalarVectorTensor.longVec (wave ξ)) V α) nonzero :=
  @contDiffOn_longVec_wave

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv → IsCompact K → IsPerturbation B (fieldOf hh) :=
  @isPerturbation_fieldOf

example : ∀ (ξ : EuclideanSpace ℝ (Fin 3)), wave (-ξ) = -wave ξ :=
  @wave_neg

example : (MinkowskiModel 3 → Fin 3 → ℝ) → ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ :=
  @fourierVector

example : ∀ (V : Fin 3 → ℂ) (α : Fin 3),
  ContDiffOn ℝ ∞
    (fun (ξ : EuclideanSpace ℝ (Fin 3)) => (ScalarVectorTensor.transVec (wave ξ)) V α) nonzero :=
  @contDiffOn_transVec_wave

example : Set (EuclideanSpace ℝ (Fin 3)) :=
  @nonzero

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
  ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ :=
  @vectorData

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
  ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ :=
  @scalarData

example : (MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ) →
  ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ :=
  @fourierMetric

example : ∀ {ξ : EuclideanSpace ℝ (Fin 3)}, ξ ≠ 0 → ScalarVectorTensor.nsq (wave ξ) ≠ 0 :=
  @nsq_wave_ne_zero

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    ∀ (L : EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ →ₗ[ℂ] ScalarVectorTensor.Mat3 ℂ)
      {t : ℝ},
      t ∈ B.I →
        ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (α β : Fin 3),
          timeDeriv (fun (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => (L ξ) (hh t ξ) α β) t ξ =
            (L ξ) (jet1 hh t ξ) α β :=
  @timeDeriv_linearMap

example : (ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ) → ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ :=
  @transData

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {z : MinkowskiModel 3} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K →
      0 ∉ K →
        z ∈ slab B.I →
          ∀ (α β : Fin 3),
            fieldOf hh z α β =
              fieldOf (scalarData hh) z α β + fieldOf (vectorData hh) z α β +
                fieldOf (tensorData hh) z α β :=
  @fieldOf_eq_add

example : Set ℝ →
  Set (EuclideanSpace ℝ (Fin 3)) →
    (MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ) →
      (MinkowskiModel 3 → ℝ) → (MinkowskiModel 3 → Fin 3 → ℝ) → Prop :=
  @HasCompactSpectrum

example : Background → ℝ → (ℝ → ℝ) → ℝ → Fin 3 → Fin 3 → (JetIdx → ℂ) →ₗ[ℂ] ℂ :=
  @spaceForm

example : ∀ (B : Background), ↑(FLRW.domain B.toData) = slab B.I :=
  @domain_eq_slab

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {h h' : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ}
  {δ δ' : MinkowskiModel 3 → ℝ} {v v' : MinkowskiModel 3 → Fin 3 → ℝ},
  (∀ z ∈ FLRW.domain B.toData, h z = h' z) →
    (∀ z ∈ FLRW.domain B.toData, δ z = δ' z) →
      (∀ z ∈ FLRW.domain B.toData, v z = v' z) →
        (LinearizedEinsteinDust B κ ρ h δ v ↔ LinearizedEinsteinDust B κ ρ h' δ' v') :=
  @linearizedEinsteinDust_congr

example : ℝ → (ℝ → ℝ) → ℝ → Fin 3 → (JetIdx → ℂ) →ₗ[ℂ] ℂ :=
  @mixedForm

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData I K hh dd vv →
    IsCompact K →
      HasCompactSpectrum I K (fieldOf hh) (scalarOf dd) (vectorOf vv) ∧
        ∀ t ∈ I,
          fourierMetric (fieldOf hh) t = hh t ∧
            fourierScalar (scalarOf dd) t = dd t ∧ fourierVector (vectorOf vv) t = vv t :=
  @IsFourierData.hasCompactSpectrum

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K → 0 ∉ K → IsFourierData B.I K (scalarData hh) dd (longData vv) :=
  @isFourierData_scalar

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K →
      ∀ {t : ℝ},
        t ∈ B.I →
          ∀ (Λ : ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ),
            (∀ (x : EuclideanSpace ℝ (Fin 3)),
                synthesis
                    (fun (s : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) =>
                      (Λ s) fun (j : JetIdx) => jetAmp hh dd vv j s ξ)
                    (spacetimePoint t x) =
                  0) ↔
              ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
                ((Λ t) fun (j : JetIdx) => jetAmp hh dd vv j t ξ) = 0 :=
  @form_eq_zero_iff

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {z : MinkowskiModel 3} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv → z ∈ slab B.I → ↑(scalarOf dd z) = synthesis dd z :=
  @ofReal_scalarOf

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
  ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ :=
  @tensorData

example : ∀ (M : ScalarVectorTensor.Mat3 ℂ) (β : Fin 3),
  ContDiff ℝ ∞ fun (ξ : EuclideanSpace ℝ (Fin 3)) => ScalarVectorTensor.contract (wave ξ) M β :=
  @contDiff_contract_wave

example : (ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ) → MinkowskiModel 3 → Fin 3 → ℝ :=
  @vectorOf

example : (scalarOf fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0)
    = fun (_ : MinkowskiModel 3) => 0 :=
  @scalarOf_zero

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K →
      0 ∉ K →
        (LinearizedEinsteinDust B κ ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) ↔
          LinearizedEinsteinDust B κ ρ (fieldOf (scalarData hh)) (scalarOf dd)
              (vectorOf (longData vv)) ∧
            LinearizedEinsteinDust B κ ρ (fieldOf (vectorData hh))
                (fun (_ : MinkowskiModel 3) => 0) (vectorOf (transData vv)) ∧
              LinearizedEinsteinDust B κ ρ (fieldOf (tensorData hh))
                (fun (_ : MinkowskiModel 3) => 0) fun (_ : MinkowskiModel 3) (_ : Fin 3) => 0) :=
  @linearizedEinsteinDust_iff_split

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {G : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ},
  IsOpen I →
    IsCompact K → IsCompactAmplitude I K G → ∀ (c : Fin 4), IsCompactAmplitude I K (dsym c G) :=
  @isCompactAmplitude_dsym

example : ∀ (h : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ) (δ : MinkowskiModel 3 → ℝ)
  (v : MinkowskiModel 3 → Fin 3 → ℝ) (z : MinkowskiModel 3) (a : Fin 3),
  realJet h δ v z (JetIdx.velocity a) = ↑(v z a) :=
  @realJet.eq_5

example : ∀ (hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ)
  (dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ),
  jetAmp hh dd vv JetIdx.density = dd :=
  @jetAmp.eq_4

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {B : Background} {κ : ℝ} {ρ : ℝ → ℝ}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    IsCompact K →
      (LinearizedEinsteinDust B κ ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) ↔
        ∀ t ∈ B.I, ∀ (ξ : EuclideanSpace ℝ (Fin 3)), FrequencyEq B κ ρ hh dd vv t ξ) :=
  @linearizedEinsteinDust_iff_frequencyEq

example : ∀ {K : Set (EuclideanSpace ℝ (Fin 3))} {z : MinkowskiModel 3} {B : Background}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  IsFourierData B.I K hh dd vv →
    z ∈ slab B.I → ∀ (α : Fin 3), ↑(vectorOf vv z α) = synthesis (vamp vv α) z :=
  @ofReal_vectorOf

example : Set ℝ →
  Set (EuclideanSpace ℝ (Fin 3)) →
    (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
      (ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) → (ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ) → Prop :=
  @IsFourierData

example : ∀ {I : Set ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {z : MinkowskiModel 3}
  {h : MinkowskiModel 3 → Fin 3 → Fin 3 → ℝ} {δ : MinkowskiModel 3 → ℝ}
  {v : MinkowskiModel 3 → Fin 3 → ℝ},
  HasCompactSpectrum I K h δ v →
    IsCompact K →
      z ∈ slab I →
        h z = fieldOf (fourierMetric h) z ∧
          δ z = scalarOf (fourierScalar δ) z ∧ v z = vectorOf (fourierVector v) z :=
  @HasCompactSpectrum.eq_synthesis

end ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Reconstruction

namespace ProjectAinos.GeneralRelativity.CosmologicalPerturbation.ModeSplit

open ProjectAinos.SmoothGeometry

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
  EuclideanSpace ℝ (Fin 3) → ℝ → Fin 3 → Fin 3 → ℝ :=
  @reAmp

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  Reconstruction.IsFourierData B.I K hh dd vv →
    ∀ {ξ : EuclideanSpace ℝ (Fin 3)},
      ξ ≠ 0 →
        ((∀ t ∈ B.I, Reconstruction.FrequencyEq B κ ρ hh dd vv t ξ) ↔
          (LinearizedEinsteinDust B κ ρ (mode (reAmp hh ξ) Real.cos (waveR ξ))
              (fun (z : MinkowskiModel 3) => (dd (z 0) ξ).re * Real.cos (phase (waveR ξ) z))
              fun (z : MinkowskiModel 3) (α : Fin 3) =>
              (vv (z 0) ξ α).im * -Real.sin (phase (waveR ξ) z)) ∧
            LinearizedEinsteinDust B κ ρ (mode (imAmp hh ξ) Real.cos (waveR ξ))
              (fun (z : MinkowskiModel 3) => (dd (z 0) ξ).im * Real.cos (phase (waveR ξ) z))
              fun (z : MinkowskiModel 3) (α : Fin 3) =>
              -(vv (z 0) ξ α).re * -Real.sin (phase (waveR ξ) z)) :=
  @frequencyEq_iff_planeWaves

example : ∀ {B : Background} {K : Set (EuclideanSpace ℝ (Fin 3))}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  Reconstruction.IsFourierData B.I K hh dd vv →
    ∀ {t : ℝ},
      t ∈ B.I →
        ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
          (Fd (reAmp hh ξ) t = fun (α β : Fin 3) => (Reconstruction.jet1 hh t ξ α β).re) ∧
            Fd (imAmp hh ξ) t = fun (α β : Fin 3) => (Reconstruction.jet1 hh t ξ α β).im :=
  @Fd_reAmp

example : ∀ {B : Background} {F : ℝ → Fin 3 → Fin 3 → ℝ},
  IsAmplitude B F →
    ∀ (L : ScalarVectorTensor.Mat3 ℝ →ₗ[ℝ] ScalarVectorTensor.Mat3 ℝ),
      (∀ (t : ℝ) (α β : Fin 3), L (F t) α β = L (F t) β α) → IsAmplitude B (projAmp L F) :=
  @isAmplitude_projAmp

example : ∀ {B : Background} {F : ℝ → Fin 3 → Fin 3 → ℝ},
  IsAmplitude B F →
    ∀ {t : ℝ},
      t ∈ B.I →
        ∀ (L : ScalarVectorTensor.Mat3 ℝ →ₗ[ℝ] ScalarVectorTensor.Mat3 ℝ),
          Fdd (projAmp L F) t = L (Fdd F t) :=
  @Fdd_projAmp

example : ∀ {B : Background} {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3 → ℝ},
  IsAmplitude B F → ContDiffOn ℝ ∞ (lamOf n F) B.I :=
  @contDiffOn_lamOf

example : ∀ {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3 → ℝ},
  mode (projAmp (ScalarVectorTensor.scalarPart n) F) Real.cos n =
    scalarMode n (lamOf n F) (muOf F) :=
  @mode_scalarPart_eq

example : (ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ) →
  EuclideanSpace ℝ (Fin 3) → ℝ → Fin 3 → Fin 3 → ℝ :=
  @imAmp

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3 → ℝ}
  {k k₁ : ℝ → ℝ},
  IsAmplitude B F →
    IsProfile k k₁ →
      nsq n ≠ 0 →
        (∃ (s : ℝ), k s ≠ 0) →
          (∃ (s : ℝ), k₁ s ≠ 0) →
            ∀ (dc : ℝ → ℝ) (V : ℝ → Fin 3 → ℝ),
              (LinearizedEinsteinDust B κ ρ (mode F k n)
                  (fun (z : MinkowskiModel 3) => dc (z 0) * k (phase n z))
                  fun (z : MinkowskiModel 3) (α : Fin 3) => V (z 0) α * k₁ (phase n z)) ↔
                (LinearizedEinsteinDust B κ ρ
                    (mode (projAmp (ScalarVectorTensor.scalarPart n) F) k n)
                    (fun (z : MinkowskiModel 3) => dc (z 0) * k (phase n z))
                    fun (z : MinkowskiModel 3) (α : Fin 3) =>
                    projVel (ScalarVectorTensor.longVec n) V (z 0) α * k₁ (phase n z)) ∧
                  (LinearizedEinsteinDust B κ ρ
                      (mode (projAmp (ScalarVectorTensor.vectorPart n) F) k n)
                      (fun (_ : MinkowskiModel 3) => 0)
                      fun (z : MinkowskiModel 3) (α : Fin 3) =>
                      projVel (ScalarVectorTensor.transVec n) V (z 0) α * k₁ (phase n z)) ∧
                    LinearizedEinsteinDust B κ ρ
                      (mode (projAmp (ScalarVectorTensor.tensorPart n) F) k n)
                      (fun (_ : MinkowskiModel 3) => 0)
                      fun (_ : MinkowskiModel 3) (_ : Fin 3) => 0 :=
  @linearizedEinsteinDust_mode_iff_split

example : (Fin 3 → ℝ) → (ℝ → Fin 3 → Fin 3 → ℝ) → ℝ → ℝ :=
  @lamOf

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3 → ℝ},
  IsAmplitude B F →
    nsq n ≠ 0 →
      ∀ (dc : ℝ → ℝ) (V : ℝ → Fin 3 → ℝ),
        (∀ t ∈ B.I, ModeEq B κ ρ F n dc V t) ↔
          (∀ t ∈ B.I,
              ModeEq B κ ρ (projAmp (ScalarVectorTensor.scalarPart n) F) n dc
                (projVel (ScalarVectorTensor.longVec n) V) t) ∧
            (∀ t ∈ B.I,
                ModeEq B κ ρ (projAmp (ScalarVectorTensor.vectorPart n) F) n (fun (_ : ℝ) => 0)
                  (projVel (ScalarVectorTensor.transVec n) V) t) ∧
              ∀ t ∈ B.I,
                ModeEq B κ ρ (projAmp (ScalarVectorTensor.tensorPart n) F) n (fun (_ : ℝ) => 0)
                  (fun (_ : ℝ) (_ : Fin 3) => 0) t :=
  @modeEq_iff_split

example : ∀ {B : Background} {K : Set (EuclideanSpace ℝ (Fin 3))}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  Reconstruction.IsFourierData B.I K hh dd vv →
    ∀ (ξ : EuclideanSpace ℝ (Fin 3)), IsAmplitude B (reAmp hh ξ) ∧ IsAmplitude B (imAmp hh ξ) :=
  @isAmplitude_reAmp

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ},
  (FLRW.metric B.toData).IsEinstein κ 0 (FLRW.perfectFluidStress B.toData ρ fun (_ : ℝ) => 0) →
    ∀ {t : ℝ}, t ∈ B.I → (realCoeffs B κ ρ t).c₁ = (realCoeffs B κ ρ t).src :=
  @realCoeffs_c₁

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3
    → ℝ} (dc : ℝ → ℝ)
  (V : ℝ → Fin 3 → ℝ) (t : ℝ),
  ModeEq B κ ρ F n dc V t ↔
    ScalarVectorTensor.SymbolEq (realCoeffs B κ ρ t) n (F t) (Fd F t) (Fdd F t) (dc t) (V t) :=
  @modeEq_iff_symbolEq

example : ∀ {B : Background} {K : Set (EuclideanSpace ℝ (Fin 3))}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  Reconstruction.IsFourierData B.I K hh dd vv →
    ∀ {t : ℝ},
      t ∈ B.I →
        ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
          (Fdd (reAmp hh ξ) t = fun (α β : Fin 3) => (Reconstruction.jet2 hh t ξ α β).re) ∧
            Fdd (imAmp hh ξ) t = fun (α β : Fin 3) => (Reconstruction.jet2 hh t ξ α β).im :=
  @Fdd_reAmp

example : ∀ {B : Background} {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3 → ℝ},
  IsAmplitude B F → IsAmplitude B (projAmp (ScalarVectorTensor.scalarPart n) F) :=
  @isAmplitude_scalarPart

example : ∀ {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3 → ℝ},
  projAmp (ScalarVectorTensor.scalarPart n) F = scalarAmp n (lamOf n F) (muOf F) :=
  @projAmp_scalarPart_eq

example : ∀ {B : Background} {F : ℝ → Fin 3 → Fin 3 → ℝ},
  IsAmplitude B F →
    ∀ {t : ℝ},
      t ∈ B.I →
        ∀ (L : ScalarVectorTensor.Mat3 ℝ →ₗ[ℝ] ScalarVectorTensor.Mat3 ℝ),
          Fd (projAmp L F) t = L (Fd F t) :=
  @Fd_projAmp

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3 → ℝ},
  (FLRW.metric B.toData).IsEinstein κ 0 (FLRW.perfectFluidStress B.toData ρ fun (_ : ℝ) => 0) →
    IsAmplitude B F →
      nsq n ≠ 0 →
        ∀ (V : ℝ → Fin 3 → ℝ),
          (∀ t ∈ B.I,
              ModeEq B κ ρ (projAmp (ScalarVectorTensor.vectorPart n) F) n (fun (_ : ℝ) => 0)
                (projVel (ScalarVectorTensor.transVec n) V) t) ↔
            ∀ t ∈ B.I,
              (∀ (β : Fin 3),
                  ScalarVectorTensor.shear n (Fdd F t) β +
                      3 * (deriv B.a t / B.a t) * ScalarVectorTensor.shear n (Fd F t) β =
                    0) ∧
                ∀ (α : Fin 3),
                  ScalarVectorTensor.shear n (Fd F t) α / 2 +
                      κ * ρ t * (ScalarVectorTensor.transVec n) (V t) α =
                    0 :=
  @vector_sector_iff

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3 → ℝ},
  (FLRW.metric B.toData).IsEinstein κ 0 (FLRW.perfectFluidStress B.toData ρ fun (_ : ℝ) => 0) →
    IsAmplitude B F →
      nsq n ≠ 0 →
        ((∀ t ∈ B.I,
            ModeEq B κ ρ (projAmp (ScalarVectorTensor.tensorPart n) F) n (fun (_ : ℝ) => 0)
              (fun (_ : ℝ) (_ : Fin 3) => 0) t) ↔
          ∀ t ∈ B.I,
            ∀ (α β : Fin 3),
              Fdd (projAmp (ScalarVectorTensor.tensorPart n) F) t α β +
                    3 * (deriv B.a t / B.a t) *
                      Fd (projAmp (ScalarVectorTensor.tensorPart n) F) t α β +
                  nsq n / B.a t ^ 2 * projAmp (ScalarVectorTensor.tensorPart n) F t α β =
                0) :=
  @tensor_sector_iff

example : Background → ℝ → (ℝ → ℝ) → ℝ → ScalarVectorTensor.Coeffs ℝ :=
  @realCoeffs

example : Background →
  ℝ → (ℝ → ℝ) → (ℝ → Fin 3 → Fin 3 → ℝ) → (Fin 3 → ℝ) → (ℝ → ℝ) → (ℝ → Fin 3 → ℝ) → ℝ → Prop :=
  @ModeEq

example : ((Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ) → (ℝ → Fin 3 → ℝ) → ℝ → Fin 3 → ℝ :=
  @projVel

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3 → ℝ},
  (FLRW.metric B.toData).IsEinstein κ 0 (FLRW.perfectFluidStress B.toData ρ fun (_ : ℝ) => 0) →
    n ≠ 0 →
      IsAmplitude B F →
        ∀ (dc : ℝ → ℝ) (V : ℝ → Fin 3 → ℝ),
          (LinearizedEinsteinDust B κ ρ
              (mode (projAmp (ScalarVectorTensor.scalarPart n) F) Real.cos n)
              (fun (z : MinkowskiModel 3) => dc (z 0) * Real.cos (phase n z))
              fun (z : MinkowskiModel 3) (α : Fin 3) =>
              (ScalarVectorTensor.longVec n) (V (z 0)) α * -Real.sin (phase n z)) ↔
            ∀ t ∈ B.I,
              deriv (deriv (lamOf n F)) t + 3 * (deriv B.a t / B.a t) * deriv (lamOf n F) t +
                    nsq n * (muOf F t - lamOf n F t) / (3 * B.a t ^ 2) =
                  0 ∧
                deriv (deriv (muOf F)) t + 3 * (deriv B.a t / B.a t) * deriv (muOf F) t +
                      nsq n * (muOf F t - lamOf n F t) / (3 * B.a t ^ 2) =
                    0 ∧
                  κ * ρ t * dc t =
                      -(deriv (deriv (muOf F)) t +
                          2 * (deriv B.a t / B.a t) * deriv (muOf F) t) ∧
                    deriv (muOf F) t - deriv (lamOf n F) t =
                      -(3 * κ * ρ t * (-ScalarVectorTensor.dot n (V t) / nsq n)) :=
  @scalar_sector_iff

example : (ScalarVectorTensor.Mat3 ℝ →ₗ[ℝ] ScalarVectorTensor.Mat3 ℝ) →
  (ℝ → Fin 3 → Fin 3 → ℝ) → ℝ → Fin 3 → Fin 3 → ℝ :=
  @projAmp

example : ∀ {B : Background} {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3 → ℝ},
  IsAmplitude B F → IsAmplitude B (projAmp (ScalarVectorTensor.vectorPart n) F) :=
  @isAmplitude_vectorPart

example : ∀ {B : Background} {F : ℝ → Fin 3 → Fin 3 → ℝ}, IsAmplitude B F
    → ContDiffOn ℝ ∞ (muOf F) B.I :=
  @contDiffOn_muOf

example : ∀ {B : Background} {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3 → ℝ},
  IsAmplitude B F → IsAmplitude B (projAmp (ScalarVectorTensor.tensorPart n) F) :=
  @isAmplitude_tensorPart

example : ∀ (L : ScalarVectorTensor.Mat3 ℝ →ₗ[ℝ] ScalarVectorTensor.Mat3 ℝ)
  {M : ℝ → ScalarVectorTensor.Mat3 ℝ} {M' : ScalarVectorTensor.Mat3 ℝ} {t : ℝ},
  (∀ (α β : Fin 3), HasDerivAt (fun (s : ℝ) => M s α β) (M' α β) t) →
    ∀ (α β : Fin 3), HasDerivAt (fun (s : ℝ) => L (M s) α β) (L M' α β) t :=
  @hasDerivAt_linearMap_apply

example : EuclideanSpace ℝ (Fin 3) → Fin 3 → ℝ :=
  @waveR

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))}
  {hh : ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ}
  {dd : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ} {vv : ℝ → EuclideanSpace ℝ (Fin 3) → Fin 3 → ℂ},
  Reconstruction.IsFourierData B.I K hh dd vv →
    ∀ {t : ℝ},
      t ∈ B.I →
        ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
          Reconstruction.FrequencyEq B κ ρ hh dd vv t ξ ↔
            ModeEq B κ ρ (reAmp hh ξ) (waveR ξ) (fun (t : ℝ) => (dd t ξ).re)
                (fun (t : ℝ) (α : Fin 3) => (vv t ξ α).im) t ∧
              ModeEq B κ ρ (imAmp hh ξ) (waveR ξ) (fun (t : ℝ) => (dd t ξ).im)
                (fun (t : ℝ) (α : Fin 3) => -(vv t ξ α).re) t :=
  @frequencyEq_iff_modeEq

example : (ℝ → Fin 3 → Fin 3 → ℝ) → ℝ → ℝ :=
  @muOf

end ProjectAinos.GeneralRelativity.CosmologicalPerturbation.ModeSplit

namespace ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Packet

open ProjectAinos.SmoothGeometry ProjectAinos.SmoothGeometry.Fourier
open ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Reconstruction

example : ScalarVectorTensor.Mat3 ℂ :=
  @plusC

example : ∀ {c : ℝ} {τ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (t : ℝ) {ξ : EuclideanSpace ℝ (Fin 3)},
  ξ ≠ 0 → tensorData (packetMetric c τ) t ξ = ((profile ξ : ℂ) * (τ t ξ : ℂ)) • polarization ξ :=
  @tensorData_packet

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {c : ℝ} {τ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ},
  (FLRW.metric B.toData).IsEinstein κ 0 (FLRW.perfectFluidStress B.toData ρ fun (_ : ℝ) => 0) →
    ContDiffOn ℝ ∞ (Function.uncurry τ) (B.I ×ˢ Set.univ) →
      (∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)), τ t (-ξ) = τ t ξ) →
        ∀ {t : ℝ},
          t ∈ B.I →
            ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
              FrequencyEq B κ ρ (packetMetric c τ)
                  (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0)
                  (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) (_ : Fin 3) => 0) t ξ ↔
                profile ξ = 0 ∨
                  polarization ξ = 0 ∨
                    deriv (deriv fun (s : ℝ) => τ s ξ) t +
                          3 * (deriv B.a t / B.a t) * deriv (fun (s : ℝ) => τ s ξ) t +
                        nsqR ξ / B.a t ^ 2 * τ t ξ =
                      0 :=
  @frequencyEq_packet_iff

example : ∀ (ξ : EuclideanSpace ℝ (Fin 3)), ScalarVectorTensor.nsq (wave ξ) = ↑(nsqR ξ) :=
  @nsq_wave_eq

example : ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (α β : Fin 3),
  (starRingEnd ℂ) (polarization ξ α β) = polarization ξ α β :=
  @conj_polarization

example : EuclideanSpace ℝ (Fin 3) → ℝ :=
  @nsqR

example : ∀ {B : Background} {c : ℝ} {τ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ},
  ContDiffOn ℝ ∞ (Function.uncurry τ) (B.I ×ˢ Set.univ) →
    (∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)), τ t (-ξ) = τ t ξ) →
      IsFourierData B.I spectrum (packetMetric c τ)
        (fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0)
        fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) (_ : Fin 3) => 0 :=
  @isFourierData_packet

example : ∀ {B : Background} {c : ℝ} {τ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ},
  ContDiffOn ℝ ∞ (Function.uncurry τ) (B.I ×ˢ Set.univ) →
    ∀ {t : ℝ},
      t ∈ B.I →
        ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
          jet1 (packetMetric c τ) t ξ =
            ((profile ξ : ℂ) * ((deriv (fun (s : ℝ) => τ s ξ) t : ℝ) : ℂ)) • polarization ξ :=
  @jet1_packet

example : ∀ {c : ℝ} {τ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (t : ℝ) {ξ : EuclideanSpace ℝ (Fin 3)},
  ξ ≠ 0 →
    scalarData (packetMetric c τ) t ξ =
      ((profile ξ : ℂ) * (c : ℂ)) • ScalarVectorTensor.longProj (wave ξ) :=
  @scalarData_packet

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {c : ℝ},
  (FLRW.metric B.toData).IsEinstein κ 0 (FLRW.perfectFluidStress B.toData ρ fun (_ : ℝ) => 0) →
    LinearizedEinsteinDust B κ ρ
      (fieldOf (packetMetric c fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin 3)) => 0))
      (fun (_ : MinkowskiModel 3) => 0) fun (_ : MinkowskiModel 3) (_ : Fin 3) => 0 :=
  @linearizedEinsteinDust_packet_zero

example : ContDiff ℝ ∞ profile :=
  @contDiff_profile

example : EuclideanSpace ℝ (Fin 3) → ℝ :=
  @profile

example : EuclideanSpace ℝ (Fin 3) :=
  @ξ₀

example : 0 ∉ spectrum :=
  @zero_notMem_spectrum

example : ∀ {ξ : EuclideanSpace ℝ (Fin 3)}, ξ ∉ spectrum → profile ξ = 0 :=
  @profile_eq_zero

example : ∀ (α β : Fin 3), plusC α β = plusC β α :=
  @plusC_symm

example : ∀ {B : Background} {c : ℝ} {τ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ},
  ContDiffOn ℝ ∞ (Function.uncurry τ) (B.I ×ˢ Set.univ) →
    ∀ {t : ℝ},
      t ∈ B.I →
        ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
          jet2 (packetMetric c τ) t ξ =
            ((profile ξ : ℂ) * ((deriv (deriv fun (s : ℝ) => τ s ξ) t : ℝ) : ℂ)) • polarization ξ :=
  @jet2_packet

example : ∀ (ξ : EuclideanSpace ℝ (Fin 3)) (α β : Fin 3),
  (starRingEnd ℂ) (ScalarVectorTensor.longProj (wave ξ) α β) =
    ScalarVectorTensor.longProj (wave ξ) α β :=
  @conj_longProj

example : ∀ {c : ℝ} {τ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (t : ℝ) {ξ : EuclideanSpace ℝ (Fin 3)},
  ξ ≠ 0 → vectorData (packetMetric c τ) t ξ = 0 :=
  @vectorData_packet

example : ContDiffBump ξ₀ :=
  @bump

example : IsCompact spectrum :=
  @isCompact_spectrum

example : Set (EuclideanSpace ℝ (Fin 3)) :=
  @spectrum

example : ∀ (ξ : EuclideanSpace ℝ (Fin 3)), profile (-ξ) = profile ξ :=
  @profile_neg

example : ∀ (I : Set ℝ),
  IsCompactAmplitude I spectrum fun (_ : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) => (profile ξ : ℂ) :=
  @isCompactAmplitude_profile

example : ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
  ScalarVectorTensor.longProj (wave (-ξ)) = ScalarVectorTensor.longProj (wave ξ) :=
  @longProj_wave_neg

example : ∀ {c : ℝ} {τ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)),
  packetMetric c τ t ξ =
    ↑(profile ξ) • (↑c • ScalarVectorTensor.longProj (wave ξ) + ↑(τ t ξ) • polarization ξ) :=
  @packetMetric_eq

example : EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ :=
  @polarization

example : ℝ →
  (ℝ → EuclideanSpace ℝ (Fin 3) → ℝ) → ℝ → EuclideanSpace ℝ (Fin 3) → ScalarVectorTensor.Mat3 ℂ :=
  @packetMetric

example : ∀ {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {c : ℝ} {τ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ},
  (FLRW.metric B.toData).IsEinstein κ 0 (FLRW.perfectFluidStress B.toData ρ fun (_ : ℝ) => 0) →
    ContDiffOn ℝ ∞ (Function.uncurry τ) (B.I ×ˢ Set.univ) →
      (∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)), τ t (-ξ) = τ t ξ) →
        ((LinearizedEinsteinDust B κ ρ (fieldOf (packetMetric c τ))
            (fun (_ : MinkowskiModel 3) => 0) fun (_ : MinkowskiModel 3) (_ : Fin 3) => 0) ↔
          ∀ t ∈ B.I,
            ∀ (ξ : EuclideanSpace ℝ (Fin 3)),
              profile ξ ≠ 0 →
                polarization ξ ≠ 0 →
                  deriv (deriv fun (s : ℝ) => τ s ξ) t +
                        3 * (deriv B.a t / B.a t) * deriv (fun (s : ℝ) => τ s ξ) t +
                      nsqR ξ / B.a t ^ 2 * τ t ξ =
                    0) :=
  @linearizedEinsteinDust_packet_iff

example : ∀ (ξ : EuclideanSpace ℝ (Fin 3)), polarization (-ξ) = polarization ξ :=
  @polarization_neg

example : ∀ {c : ℝ} {τ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (t : ℝ),
  packetMetric c τ t ξ₀ 2 2 = ↑(profile ξ₀) * (↑c + ↑(τ t ξ₀) * polarization ξ₀ 2 2) :=
  @packetMetric_ξ₀

example : ∀ {c : ℝ} {τ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ},
  c ≠ 0 → ∀ (t : ℝ), τ t ξ₀ = 0 → packetMetric c τ t ξ₀ ≠ 0 :=
  @packetMetric_ne_zero

example : ‖ξ₀‖ = 1 :=
  @norm_ξ₀

example : 0 < profile ξ₀ :=
  @profile_ξ₀_pos

example : (fun (α β : Fin 3) => (starRingEnd ℂ) (plusC α β)) = plusC :=
  @conj_plusC

example : ∀ {B : Background} {c : ℝ} {τ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ},
  ContDiffOn ℝ ∞ (Function.uncurry τ) (B.I ×ˢ Set.univ) →
    (∀ (t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)), τ t (-ξ) = τ t ξ) →
      HasCompactSpectrum B.I spectrum (fieldOf (packetMetric c τ))
        (fun (_ : MinkowskiModel 3) => 0) fun (_ : MinkowskiModel 3) (_ : Fin 3) => 0 :=
  @hasCompactSpectrum_packet

end ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Packet

namespace ProjectAinos.GeneralRelativity.CosmologicalPerturbation.ModeSplit

open ProjectAinos.SmoothGeometry

example : ∀ {n : Fin 3 → ℝ},
  nsq n ≠ 0 →
    ∀ {e : Fin 3 → ℝ},
      ∑ γ : Fin 3, n γ * e γ = 0 →
        (ScalarVectorTensor.scalarPart n) (vectorAmp n e) = 0 ∧
          (ScalarVectorTensor.vectorPart n) (vectorAmp n e) = vectorAmp n e ∧
            (ScalarVectorTensor.tensorPart n) (vectorAmp n e) = 0 :=
  @vectorAmp_mem_vector

example : ∀ {n : Fin 3 → ℝ},
  nsq n ≠ 0 →
    ∀ (w : ℝ),
      (ScalarVectorTensor.longVec n) (w • n) = w • n ∧
        (ScalarVectorTensor.transVec n) (w • n) = 0 :=
  @longVec_smul_self

example : ∀ {n : Fin 3 → ℝ},
  nsq n ≠ 0 →
    ∀ (lam mu : ℝ → ℝ) (t : ℝ),
      (ScalarVectorTensor.scalarPart n) (scalarAmp n lam mu t) = scalarAmp n lam mu t ∧
        (ScalarVectorTensor.vectorPart n) (scalarAmp n lam mu t) = 0 ∧
          (ScalarVectorTensor.tensorPart n) (scalarAmp n lam mu t) = 0 :=
  @scalarAmp_mem_scalar

example : ∀ {n : Fin 3 → ℝ} {B : Background} {κ : ℝ} {ρ : ℝ → ℝ},
  (FLRW.metric B.toData).IsEinstein κ 0 (FLRW.perfectFluidStress B.toData ρ fun (_ : ℝ) => 0) →
    n ≠ 0 →
      ∀ {e : Fin 3 → ℝ},
        ∑ γ : Fin 3, n γ * e γ = 0 →
          e ≠ 0 →
            ∀ (c : ℝ),
              LinearizedEinsteinDust B κ ρ (vectorMode n e fun (_ : ℝ) => c)
                (fun (_ : MinkowskiModel 3) => 0) fun (_ : MinkowskiModel 3) (_ : Fin 3) => 0 :=
  @vectorGauge_solution

example : ∀ {n : Fin 3 → ℝ} (lam mu : ℝ → ℝ) (t : ℝ),
  scalarAmp n lam mu t =
    lam t • ScalarVectorTensor.longProj n + ((mu t - lam t) / 3) • ScalarVectorTensor.delta ℝ :=
  @scalarAmp_eq

end ProjectAinos.GeneralRelativity.CosmologicalPerturbation.ModeSplit

namespace ProjectAinos.GeneralRelativity.CurvedPerturbation

open ProjectAinos.SmoothGeometry ProjectAinos.SmoothGeometry.CoordinateMetric
open ProjectAinos.GeneralRelativity.FLRW ProjectAinos.SmoothGeometry.IsotropicRicci
open ProjectAinos.GeneralRelativity.CosmologicalModels ProjectAinos.SpecialFunctions

example : ∀ {A κ : ℝ} (hA : 0 < A),
  0 < κ →
    ∀ {ι : Type u_1} (s : Finset ι) (l : ι → ℕ)
      (p : (i : ι) → ↥(HarmonicPolynomial.harmonics 3 (l i))) (ξ b : ι → ℝ) (φ : ι → ℝ → ℝ),
      (∀ i ∈ s, φ i ∈ ({decay (openDust A hA), growth (openDust A hA) (b i)} : Set (ℝ → ℝ))) →
        ∀ (c : ι → ℝ) {x : MinkowskiModel 3},
          x ∈ domain (openDust A hA) →
            LinearizedDustAt (openDust A hA) κ (dustDensity κ (6 * A) (openDust A hA).a)
              (fun (y : MinkowskiModel 3) =>
                ∑ i ∈ s, c i * separated (φ i) (openHarmonic (p i) (ξ i)) y)
              (fun (y : MinkowskiModel 3) =>
                ∑ i ∈ s,
                  c i *
                    contrast (openDust A hA) κ (dustDensity κ (6 * A) (openDust A hA).a) (φ i)
                      (1 + ξ i ^ 2) (openHarmonic (p i) (ξ i)) y)
              (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                ∑ i ∈ s,
                  c i *
                    covelocity (openDust A hA) κ (dustDensity κ (6 * A) (openDust A hA).a) (φ i)
                      (openHarmonic (p i) (ξ i)) y j)
              x :=
  @open_dust_expansion

example : ∀ {u w : MinkowskiModel 3 → ℝ} {x : MinkowskiModel 3} {D : Data},
  D.N = D.a →
    ∀ {κ : ℝ} {ρ : ℝ → ℝ},
      (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0) →
        x ∈ domain D →
          ContDiffAt ℝ ∞ u x →
            ContDiffAt ℝ ∞ w x →
              ∀ {δ δ' : MinkowskiModel 3 → ℝ} {V V' : MinkowskiModel 3 → Fin 4 → ℝ},
                LinearizedDustAt D κ ρ u δ V x →
                  LinearizedDustAt D κ ρ w δ' V' x →
                    LinearizedDustAt D κ ρ (fun (y : MinkowskiModel 3) => u y + w y)
                      (fun (y : MinkowskiModel 3) => δ y + δ' y)
                      (fun (y : MinkowskiModel 3) (i : Fin 4) => V y i + V' y i) x :=
  @linearizedDustAt_add

example : ∀ {u w : MinkowskiModel 3 → ℝ} {x : MinkowskiModel 3},
  DifferentiableAt ℝ u x →
    DifferentiableAt ℝ w x →
      ∀ (i : Fin 4),
        part (fun (y : MinkowskiModel 3) => u y + w y) i x = part u i x + part w i x :=
  @part_add

example : ∀ {x : MinkowskiModel 3} {φ : ℝ → ℝ},
  ContDiffAt ℝ ∞ φ (x 0) →
    ∀ {Q : MinkowskiModel 3 → ℝ}, ContDiffAt ℝ ∞ Q x → ContDiffAt ℝ ∞ (separated φ Q) x :=
  @contDiffAt_separated

example : ∀ {u : MinkowskiModel 3 → ℝ} {x : MinkowskiModel 3} {D : Data},
  D.N = D.a →
    ∀ {κ : ℝ} {ρ : ℝ → ℝ},
      (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0) →
        x ∈ domain D →
          ContDiffAt ℝ ∞ u x →
            ∀ (c : ℝ) {δ : MinkowskiModel 3 → ℝ} {V : MinkowskiModel 3 → Fin 4 → ℝ},
              LinearizedDustAt D κ ρ u δ V x →
                LinearizedDustAt D κ ρ (fun (y : MinkowskiModel 3) => c * u y)
                  (fun (y : MinkowskiModel 3) => c * δ y)
                  (fun (y : MinkowskiModel 3) (i : Fin 4) => c * V y i) x :=
  @linearizedDustAt_const_mul

example : ∀ {x : MinkowskiModel 3}, 0 < psi (-1) x → 1 ≤ chartCoordinate (-1) x :=
  @one_le_chartCoordinate

example : ∀ {u : MinkowskiModel 3 → ℝ} {x : MinkowskiModel 3},
  ContDiffAt ℝ ∞ u x →
    ∀ (c : ℝ) (a b : Fin 4),
      secondPartial (fun (y : MinkowskiModel 3) => c * u y) x a b = c * secondPartial u x a b :=
  @secondPartial_const_mul

example : ∀ {u w : MinkowskiModel 3 → ℝ} {x : MinkowskiModel 3},
  ContDiffAt ℝ ∞ u x →
    ContDiffAt ℝ ∞ w x →
      ∀ (a b : Fin 4),
        secondPartial (fun (y : MinkowskiModel 3) => u y + w y) x a b =
          secondPartial u x a b + secondPartial w x a b :=
  @secondPartial_add

example : ∀ {A κ : ℝ} (hA : 0 < A),
  0 < κ →
    ∀ {ι : Type u_1} (s : Finset ι) (l : ι → ℕ)
      (p : (i : ι) → ↥(HarmonicPolynomial.harmonics 3 (l i))) (m : ι → ℕ) (b : ι → ℝ)
      (φ : ι → ℝ → ℝ),
      (∀ i ∈ s, φ i ∈ ({decay (closedDust A hA), growth (closedDust A hA) (b i)} : Set (ℝ → ℝ))) →
        ∀ (c : ι → ℝ) {x : MinkowskiModel 3},
          x ∈ domain (closedDust A hA) →
            LinearizedDustAt (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
              (fun (y : MinkowskiModel 3) =>
                ∑ i ∈ s, c i * separated (φ i) (closedHarmonic (p i) (m i)) y)
              (fun (y : MinkowskiModel 3) =>
                ∑ i ∈ s,
                  c i *
                    contrast (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
                      (φ i) (↑(l i + m i) * (↑(l i) + ↑(m i) + 2)) (closedHarmonic (p i) (m i))
                      y)
              (fun (y : MinkowskiModel 3) (j : Fin 4) =>
                ∑ i ∈ s,
                  c i *
                    covelocity (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
                      (φ i) (closedHarmonic (p i) (m i)) y j)
              x :=
  @closed_dust_expansion

example : ∀ {u : MinkowskiModel 3 → ℝ} {x : MinkowskiModel 3},
  ContDiffAt ℝ ∞ u x →
    ∀ (c k : ℝ),
      spatialLaplacian k (fun (y : MinkowskiModel 3) => c * u y) x = c * spatialLaplacian k u x :=
  @spatialLaplacian_const_mul

example : ∀ {u w : MinkowskiModel 3 → ℝ} {x : MinkowskiModel 3},
  ContDiffAt ℝ ∞ u x →
    ContDiffAt ℝ ∞ w x →
      ∀ (k : ℝ),
        spatialLaplacian k (fun (y : MinkowskiModel 3) => u y + w y) x =
          spatialLaplacian k u x + spatialLaplacian k w x :=
  @spatialLaplacian_add

example : ∀ {x : MinkowskiModel 3} {D : Data},
  D.N = D.a →
    ∀ {κ : ℝ} {ρ : ℝ → ℝ},
      (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0) →
        ∀ {ι : Type u_1} (s : Finset ι),
          x ∈ domain D →
            ∀ (c : ι → ℝ) {U Δ : ι → MinkowskiModel 3 → ℝ}
              {W : ι → MinkowskiModel 3 → Fin 4 → ℝ},
              (∀ i ∈ s, ContDiffAt ℝ ∞ (U i) x) →
                (∀ i ∈ s, LinearizedDustAt D κ ρ (U i) (Δ i) (W i) x) →
                  LinearizedDustAt D κ ρ (fun (y : MinkowskiModel 3) => ∑ i ∈ s, c i * U i y)
                    (fun (y : MinkowskiModel 3) => ∑ i ∈ s, c i * Δ i y)
                    (fun (y : MinkowskiModel 3) (j : Fin 4) => ∑ i ∈ s, c i * W i y j) x :=
  @linearizedDustAt_sum

example : ∀ {u : MinkowskiModel 3 → ℝ} {x : MinkowskiModel 3},
  DifferentiableAt ℝ u x →
    ∀ (c : ℝ) (i : Fin 4), part (fun (y : MinkowskiModel 3) => c * u y) i x = c * part u i x :=
  @part_const_mul

end ProjectAinos.GeneralRelativity.CurvedPerturbation
