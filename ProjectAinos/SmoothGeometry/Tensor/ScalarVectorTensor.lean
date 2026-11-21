/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# The scalar–vector–tensor decomposition of a 3 × 3 matrix

Over a field `K` of characteristic zero, for a wave vector `n : Fin 3 → K` with
`|n|² = Σ n_γ² ≠ 0`, a matrix `M` (written as a function `Fin 3 → Fin 3 → K`, `Mat3 K`) splits
into three parts, the algebraic
form of the decomposition of a perturbation of a flat space into scalar, vector and tensor
modes (Landau–Lifshitz, §115):

* `scalarPart n M = a nn/|n|² + b (δ − nn/|n|²)` with `a = nMn/|n|²` (`longCoeff`) and
  `b = (tr M − a)/2`; it is `λ (nn/|n|² − δ/3) + μ δ/3` with `λ = (3a − tr M)/2` and
  `μ = tr M` (`scalarPart_eq`);
* `vectorPart n M = (n ⊗ u + u ⊗ n)/|n|²` with the transverse vector `u = nM − a n`
  (`shear`, `dot_shear`);
* `tensorPart n M = M − scalarPart n M − vectorPart n M`, traceless and transverse
  (`trace_tensorPart`, `contract_tensorPart`).

The three maps are linear, idempotent and mutually orthogonal, and they sum to the identity
(`scalarPart_scalarPart`, …, `scalarPart_add_vectorPart_add_tensorPart`); for vectors,
`longVec n V = (n·V/|n|²) n` and `transVec n V = V − longVec n V`. None of this uses the
symmetry of `M`.

The symbols of the linearized equations of a flat perturbation commute with the split:
`op n M = |n|² M + nn tr M − n ⊗ nM − nM ⊗ n`, the symbol of twice the variation of the
spatial Ricci tensor for `∂_α ↦ i n_α`, preserves each part (`scalarPart_op`, `vectorPart_op`,
`tensorPart_op`, with `op_vectorPart = 0` and `op_tensorPart = |n|² tensorPart`), and
`mix n M = nM − n tr M` maps the scalar part to the longitudinal vectors and the vector part to
the transverse ones (`longVec_mix`, `transVec_mix`, `mix_tensorPart = 0`).

`SymbolEq P n F₀ F₁ F₂ D V` is the system `resTime = 0`, `resMixed = 0`, `resSpace = 0` of the
equations `δR_{ik} = κ δS_{ik}` of a single frequency, for the jets `F₀, F₁, F₂` of the metric
perturbation (the value and the first two time derivatives), the density contrast `D` and the
velocity `V`, with the background coefficients `P` (`Coeffs`). `symbolEq_iff` is the
**decomposition**: the system holds if and only if it holds separately for the scalar part
(with `D` and the longitudinal velocity), for the vector part (with the transverse velocity and
no density) and for the tensor part (with neither).
-/

@[expose] public section

namespace ProjectAinos.SmoothGeometry.ScalarVectorTensor

open Finset

/-- A `3 × 3` matrix, as a function of the two indices. -/
abbrev Mat3 (K : Type*) := Fin 3 → Fin 3 → K

variable {K : Type*} [Field K]

/-! ### The observables -/

/-- `|n|² = n₁² + n₂² + n₃²`. -/
def nsq (n : Fin 3 → K) : K := ∑ γ, n γ ^ 2

variable (K) in
/-- The Kronecker symbol `δ_{αβ}`. -/
def delta : Mat3 K := fun α β => if α = β then 1 else 0

/-- The trace `M_γγ`. -/
def trace (M : Mat3 K) : K := ∑ γ, M γ γ

/-- The contraction `(nM)_β = n_γ M_{γβ}`. -/
def contract (n : Fin 3 → K) (M : Mat3 K) (β : Fin 3) : K := ∑ γ, n γ * M γ β

/-- `nMn = (nM)_β n_β`. -/
def sandwich (n : Fin 3 → K) (M : Mat3 K) : K := ∑ β, contract n M β * n β

/-- The scalar product `n · V`. -/
def dot (n V : Fin 3 → K) : K := ∑ γ, n γ * V γ

section Observables

variable (n : Fin 3 → K) (M N : Mat3 K) (c : K)

@[simp] theorem trace_add : trace (M + N) = trace M + trace N := by
  simp [trace, Finset.sum_add_distrib]

@[simp] theorem trace_sub : trace (M - N) = trace M - trace N := by
  simp [trace, Finset.sum_sub_distrib]

@[simp] theorem trace_smul : trace (c • M) = c * trace M := by
  simp [trace, Finset.mul_sum]

@[simp] theorem trace_zero : trace (0 : Mat3 K) = 0 := by simp [trace]

@[simp] theorem trace_delta : trace (delta K) = 3 := by
  simp [trace, delta]

@[simp] theorem contract_add : contract n (M + N) = contract n M + contract n N := by
  funext β; simp [contract, mul_add, Finset.sum_add_distrib]

@[simp] theorem contract_sub : contract n (M - N) = contract n M - contract n N := by
  funext β; simp [contract, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem contract_smul : contract n (c • M) = c • contract n M := by
  funext β; simp [contract, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

@[simp] theorem contract_zero : contract n (0 : Mat3 K) = 0 := by
  funext β; simp [contract]

@[simp] theorem contract_delta : contract n (delta K) = n := by
  funext β; simp [contract, delta]

@[simp] theorem sandwich_add : sandwich n (M + N) = sandwich n M + sandwich n N := by
  simp [sandwich, add_mul, Finset.sum_add_distrib]

@[simp] theorem sandwich_sub : sandwich n (M - N) = sandwich n M - sandwich n N := by
  simp [sandwich, sub_mul, Finset.sum_sub_distrib]

@[simp] theorem sandwich_smul : sandwich n (c • M) = c * sandwich n M := by
  simp [sandwich, Finset.mul_sum, mul_assoc]

@[simp] theorem sandwich_zero : sandwich n (0 : Mat3 K) = 0 := by simp [sandwich]

theorem sum_mul_self : ∑ γ, n γ * n γ = nsq n :=
  Finset.sum_congr rfl fun γ _ => by ring

@[simp] theorem sandwich_delta : sandwich n (delta K) = nsq n := by
  simp [sandwich, sum_mul_self]

theorem dot_contract : dot n (contract n M) = sandwich n M := by
  simp only [dot, sandwich]
  exact Finset.sum_congr rfl fun γ _ => mul_comm _ _

theorem dot_self : dot n n = nsq n := sum_mul_self n

@[simp] theorem dot_add (V W : Fin 3 → K) : dot n (V + W) = dot n V + dot n W := by
  simp [dot, mul_add, Finset.sum_add_distrib]

@[simp] theorem dot_sub (V W : Fin 3 → K) : dot n (V - W) = dot n V - dot n W := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem dot_smul (V : Fin 3 → K) : dot n (c • V) = c * dot n V := by
  simp [dot, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

@[simp] theorem dot_zero : dot n (0 : Fin 3 → K) = 0 := by simp [dot]

/-- `n · (c n) = c |n|²`. -/
theorem dot_smul_self : dot n (fun β => c * n β) = c * nsq n := by
  rw [← sum_mul_self, dot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `Σ_γ n_γ (n_γ v_β + v_γ n_β) = |n|² v_β + (n · v) n_β`. -/
theorem sum_mul_sym (v : Fin 3 → K) (β : Fin 3) :
    ∑ γ, n γ * (n γ * v β + v γ * n β) = nsq n * v β + dot n v * n β := by
  rw [← sum_mul_self, dot, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

end Observables

/-! ### The projections -/

/-- The longitudinal coefficient `a = nMn/|n|²`. -/
def longCoeff (n : Fin 3 → K) (M : Mat3 K) : K := sandwich n M / nsq n

/-- The transverse vector `u_β = (nM)_β − a n_β` of a matrix. -/
def shear (n : Fin 3 → K) (M : Mat3 K) (β : Fin 3) : K := contract n M β - longCoeff n M * n β

/-- **The scalar part** `a nn/|n|² + b (δ − nn/|n|²)`, `a = nMn/|n|²`, `b = (tr M − a)/2`. -/
def scalarPart (n : Fin 3 → K) : Mat3 K →ₗ[K] Mat3 K where
  toFun M α β := longCoeff n M * (n α * n β / nsq n) +
    (trace M - longCoeff n M) / 2 * (delta K α β - n α * n β / nsq n)
  map_add' M N := by funext α β; simp only [longCoeff, sandwich_add, trace_add, Pi.add_apply]; ring
  map_smul' c M := by
    funext α β; simp only [longCoeff, sandwich_smul, trace_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

/-- **The vector part** `(n ⊗ u + u ⊗ n)/|n|²` with the transverse vector `u` (`shear`). -/
def vectorPart (n : Fin 3 → K) : Mat3 K →ₗ[K] Mat3 K where
  toFun M α β := (n α * shear n M β + shear n M α * n β) / nsq n
  map_add' M N := by
    funext α β; simp only [shear, longCoeff, contract_add, sandwich_add, Pi.add_apply]; ring
  map_smul' c M := by
    funext α β; simp only [shear, longCoeff, contract_smul, sandwich_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]; ring

/-- **The tensor part** `M − scalarPart n M − vectorPart n M`. -/
def tensorPart (n : Fin 3 → K) : Mat3 K →ₗ[K] Mat3 K :=
  LinearMap.id - scalarPart n - vectorPart n

/-- The longitudinal part `(n·V/|n|²) n` of a vector. -/
def longVec (n : Fin 3 → K) : (Fin 3 → K) →ₗ[K] (Fin 3 → K) where
  toFun V α := dot n V / nsq n * n α
  map_add' V W := by funext α; simp only [dot_add, Pi.add_apply]; ring
  map_smul' c V := by
    funext α; simp only [dot_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The transverse part `V − (n·V/|n|²) n` of a vector. -/
def transVec (n : Fin 3 → K) : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := LinearMap.id - longVec n

section Projections

variable (n : Fin 3 → K) (M : Mat3 K) (V : Fin 3 → K)

variable [CharZero K]

omit [CharZero K] in
theorem scalarPart_apply (α β : Fin 3) : scalarPart n M α β = longCoeff n M * (n α * n β / nsq n) +
    (trace M - longCoeff n M) / 2 * (delta K α β - n α * n β / nsq n) := rfl

omit [CharZero K] in
theorem vectorPart_apply (α β : Fin 3) :
    vectorPart n M α β = (n α * shear n M β + shear n M α * n β) / nsq n := rfl

omit [CharZero K] in
theorem tensorPart_apply (α β : Fin 3) :
    tensorPart n M α β = M α β - scalarPart n M α β - vectorPart n M α β := rfl

omit [CharZero K] in
theorem longVec_apply (α : Fin 3) : longVec n V α = dot n V / nsq n * n α := rfl

omit [CharZero K] in
theorem transVec_apply (α : Fin 3) : transVec n V α = V α - longVec n V α := rfl

omit [CharZero K] in
/-- The three parts sum to the matrix. -/
theorem scalarPart_add_vectorPart_add_tensorPart :
    scalarPart n M + vectorPart n M + tensorPart n M = M := by
  funext α β; simp [tensorPart_apply]

omit [CharZero K] in
/-- The two parts of a vector sum to the vector. -/
theorem longVec_add_transVec : longVec n V + transVec n V = V := by
  funext α; simp [transVec_apply]

/-- The scalar and vector parts are symmetric. -/
theorem scalarPart_symm (α β : Fin 3) : scalarPart n M α β = scalarPart n M β α := by
  simp only [scalarPart_apply, delta]
  by_cases h : α = β
  · subst h; rfl
  · simp only [h, Ne.symm h, ite_false]; ring

theorem vectorPart_symm (α β : Fin 3) : vectorPart n M α β = vectorPart n M β α := by
  simp only [vectorPart_apply]; ring

/-- The tensor part of a symmetric matrix is symmetric. -/
theorem tensorPart_symm (hM : ∀ α β, M α β = M β α) (α β : Fin 3) :
    tensorPart n M α β = tensorPart n M β α := by
  simp only [tensorPart_apply, hM α β, scalarPart_symm n M α β, vectorPart_symm n M α β]

variable {n}

omit [CharZero K] in
/-- `n · u = 0`: the vector `u` of `vectorPart` is transverse. -/
theorem dot_shear (hn : nsq n ≠ 0) : dot n (shear n M) = 0 := by
  have e : dot n (shear n M) = dot n (contract n M) - longCoeff n M * nsq n := by
    rw [← dot_smul_self, ← dot_sub]; rfl
  rw [e, dot_contract, longCoeff, div_mul_cancel₀ _ hn, sub_self]

@[simp] theorem trace_scalarPart (hn : nsq n ≠ 0) : trace (scalarPart n M) = trace M := by
  simp only [trace, scalarPart_apply, delta, Fin.sum_univ_three, nsq] at *
  simp only [Fin.isValue, ite_true]
  field_simp
  ring

@[simp] theorem contract_scalarPart (hn : nsq n ≠ 0) :
    contract n (scalarPart n M) = fun β => longCoeff n M * n β := by
  funext β
  have hN : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 ≠ 0 := by simpa [nsq, Fin.sum_univ_three] using hn
  simp only [contract, scalarPart_apply, delta, nsq, Fin.sum_univ_three]
  fin_cases β <;> simp <;> field_simp <;> ring

@[simp] theorem sandwich_scalarPart (hn : nsq n ≠ 0) :
    sandwich n (scalarPart n M) = sandwich n M := by
  rw [sandwich, contract_scalarPart M hn, ← dot, dot_comm, dot_smul_self, longCoeff,
    div_mul_cancel₀ _ hn]
where dot_comm : dot (fun β => longCoeff n M * n β) n = dot n (fun β => longCoeff n M * n β) :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

@[simp] theorem longCoeff_scalarPart (hn : nsq n ≠ 0) :
    longCoeff n (scalarPart n M) = longCoeff n M := by
  rw [longCoeff, sandwich_scalarPart M hn, longCoeff]

@[simp] theorem shear_scalarPart (hn : nsq n ≠ 0) : shear n (scalarPart n M) = 0 := by
  funext β; simp [shear, contract_scalarPart M hn, longCoeff_scalarPart M hn]

omit [CharZero K] in
@[simp] theorem trace_vectorPart (hn : nsq n ≠ 0) : trace (vectorPart n M) = 0 := by
  have e : trace (vectorPart n M) = 2 * dot n (shear n M) / nsq n := by
    simp only [trace, vectorPart_apply, dot, ← Finset.sum_div, Finset.mul_sum]
    exact congrArg (· / nsq n) (Finset.sum_congr rfl fun _ _ => by ring)
  rw [e, dot_shear M hn, mul_zero, zero_div]

@[simp] theorem contract_vectorPart (hn : nsq n ≠ 0) :
    contract n (vectorPart n M) = shear n M := by
  funext β
  have e : contract n (vectorPart n M) β =
      (∑ γ, n γ * (n γ * shear n M β + shear n M γ * n β)) / nsq n := by
    simp only [contract, vectorPart_apply, Finset.sum_div]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e, sum_mul_sym, dot_shear M hn]
  field_simp
  ring

@[simp] theorem sandwich_vectorPart (hn : nsq n ≠ 0) : sandwich n (vectorPart n M) = 0 := by
  rw [sandwich, contract_vectorPart M hn]
  have := dot_shear M hn
  simp only [dot] at this
  rw [← this]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

@[simp] theorem longCoeff_vectorPart (hn : nsq n ≠ 0) : longCoeff n (vectorPart n M) = 0 := by
  rw [longCoeff, sandwich_vectorPart M hn, zero_div]

@[simp] theorem shear_vectorPart (hn : nsq n ≠ 0) : shear n (vectorPart n M) = shear n M := by
  funext β; simp [shear, contract_vectorPart M hn, longCoeff_vectorPart M hn]

omit [CharZero K] in
theorem tensorPart_eq : tensorPart n M = M - scalarPart n M - vectorPart n M := rfl

@[simp] theorem trace_tensorPart (hn : nsq n ≠ 0) : trace (tensorPart n M) = 0 := by
  rw [tensorPart_eq, trace_sub, trace_sub, trace_scalarPart M hn, trace_vectorPart M hn]; ring

/-- The tensor part is transverse: `n_γ T_{γβ} = 0`. -/
@[simp] theorem contract_tensorPart (hn : nsq n ≠ 0) : contract n (tensorPart n M) = 0 := by
  rw [tensorPart_eq, contract_sub, contract_sub, contract_scalarPart M hn,
    contract_vectorPart M hn]
  funext β; simp [shear]

@[simp] theorem sandwich_tensorPart (hn : nsq n ≠ 0) : sandwich n (tensorPart n M) = 0 := by
  simp [sandwich, contract_tensorPart M hn]

@[simp] theorem longCoeff_tensorPart (hn : nsq n ≠ 0) : longCoeff n (tensorPart n M) = 0 := by
  rw [longCoeff, sandwich_tensorPart M hn, zero_div]

@[simp] theorem shear_tensorPart (hn : nsq n ≠ 0) : shear n (tensorPart n M) = 0 := by
  funext β; simp [shear, contract_tensorPart M hn, longCoeff_tensorPart M hn]

omit [CharZero K] in
theorem shear_add (N : Mat3 K) : shear n (M + N) = shear n M + shear n N := by
  funext β; simp only [shear, longCoeff, contract_add, sandwich_add, Pi.add_apply]; ring

omit [CharZero K] in
theorem shear_smul (c : K) : shear n (c • M) = c • shear n M := by
  funext β; simp only [shear, longCoeff, contract_smul, sandwich_smul, Pi.smul_apply,
    smul_eq_mul]; ring

/-- The vector part vanishes if and only if the transverse vector does. -/
theorem vectorPart_eq_zero_iff (hn : nsq n ≠ 0) : vectorPart n M = 0 ↔ shear n M = 0 := by
  constructor
  · intro h
    rw [← contract_vectorPart M hn, h, contract_zero]
  · intro h
    funext α β
    simp [vectorPart_apply, h]

/-! #### Idempotence and orthogonality -/

theorem scalarPart_scalarPart (hn : nsq n ≠ 0) :
    scalarPart n (scalarPart n M) = scalarPart n M := by
  funext α β
  rw [scalarPart_apply, longCoeff_scalarPart M hn, trace_scalarPart M hn, scalarPart_apply]

theorem scalarPart_vectorPart (hn : nsq n ≠ 0) : scalarPart n (vectorPart n M) = 0 := by
  funext α β
  rw [scalarPart_apply, longCoeff_vectorPart M hn, trace_vectorPart M hn]
  simp

theorem scalarPart_tensorPart (hn : nsq n ≠ 0) : scalarPart n (tensorPart n M) = 0 := by
  funext α β
  rw [scalarPart_apply, longCoeff_tensorPart M hn, trace_tensorPart M hn]
  simp

theorem vectorPart_scalarPart (hn : nsq n ≠ 0) : vectorPart n (scalarPart n M) = 0 := by
  funext α β
  rw [vectorPart_apply, shear_scalarPart M hn]
  simp

theorem vectorPart_vectorPart (hn : nsq n ≠ 0) :
    vectorPart n (vectorPart n M) = vectorPart n M := by
  funext α β
  rw [vectorPart_apply, shear_vectorPart M hn, vectorPart_apply]

theorem vectorPart_tensorPart (hn : nsq n ≠ 0) : vectorPart n (tensorPart n M) = 0 := by
  funext α β
  rw [vectorPart_apply, shear_tensorPart M hn]
  simp

theorem tensorPart_scalarPart (hn : nsq n ≠ 0) : tensorPart n (scalarPart n M) = 0 := by
  rw [tensorPart_eq, scalarPart_scalarPart M hn, vectorPart_scalarPart M hn]; simp

theorem tensorPart_vectorPart (hn : nsq n ≠ 0) : tensorPart n (vectorPart n M) = 0 := by
  rw [tensorPart_eq, scalarPart_vectorPart M hn, vectorPart_vectorPart M hn]; simp

theorem tensorPart_tensorPart (hn : nsq n ≠ 0) :
    tensorPart n (tensorPart n M) = tensorPart n M := by
  conv_lhs => rw [tensorPart_eq, scalarPart_tensorPart M hn, vectorPart_tensorPart M hn]
  simp

omit [CharZero K] in
@[simp] theorem dot_longVec (hn : nsq n ≠ 0) : dot n (longVec n V) = dot n V := by
  have : longVec n V = fun α => dot n V / nsq n * n α := rfl
  rw [this, dot_smul_self, div_mul_cancel₀ _ hn]

omit [CharZero K] in
@[simp] theorem dot_transVec (hn : nsq n ≠ 0) : dot n (transVec n V) = 0 := by
  have : transVec n V = V - longVec n V := rfl
  rw [this, dot_sub, dot_longVec V hn, sub_self]

omit [CharZero K] in
theorem longVec_longVec (hn : nsq n ≠ 0) : longVec n (longVec n V) = longVec n V := by
  funext α; rw [longVec_apply, dot_longVec V hn, longVec_apply]

omit [CharZero K] in
theorem longVec_transVec (hn : nsq n ≠ 0) : longVec n (transVec n V) = 0 := by
  funext α; rw [longVec_apply, dot_transVec V hn]; simp

omit [CharZero K] in
theorem transVec_longVec (hn : nsq n ≠ 0) : transVec n (longVec n V) = 0 := by
  funext α; rw [transVec_apply, longVec_longVec V hn]; simp

omit [CharZero K] in
theorem transVec_transVec (hn : nsq n ≠ 0) : transVec n (transVec n V) = transVec n V := by
  funext α; rw [transVec_apply, longVec_transVec V hn]; simp

/-- The Kronecker symbol is scalar. -/
@[simp] theorem scalarPart_delta (hn : nsq n ≠ 0) : scalarPart n (delta K) = delta K := by
  funext α β
  rw [scalarPart_apply, longCoeff, sandwich_delta, trace_delta, div_self hn]
  ring

omit [CharZero K] in
@[simp] theorem shear_delta (hn : nsq n ≠ 0) : shear n (delta K) = 0 := by
  funext β; simp [shear, longCoeff, div_self hn]

omit [CharZero K] in
@[simp] theorem vectorPart_delta (hn : nsq n ≠ 0) : vectorPart n (delta K) = 0 := by
  funext α β; rw [vectorPart_apply, shear_delta hn]; simp

@[simp] theorem tensorPart_delta (hn : nsq n ≠ 0) : tensorPart n (delta K) = 0 := by
  rw [tensorPart_eq, scalarPart_delta hn, vectorPart_delta hn]; simp

/-- **The parameters of L&L**: the scalar part is `λ (nn/|n|² − δ/3) + μ δ/3` with
`λ = (3a − tr M)/2` and `μ = tr M`. -/
theorem scalarPart_eq (α β : Fin 3) :
    scalarPart n M α β = (3 * longCoeff n M - trace M) / 2 * (n α * n β / nsq n -
      delta K α β / 3) + trace M * (delta K α β / 3) := by
  rw [scalarPart_apply]; ring

end Projections


/-! ### Compatibility with the reflection `n ↦ −n` and with ring homomorphisms -/

section Symmetries

variable (n : Fin 3 → K) (M : Mat3 K) (V : Fin 3 → K)

variable [CharZero K]

omit [CharZero K] in
theorem nsq_neg : nsq (-n) = nsq n := by simp [nsq]

omit [CharZero K] in
theorem longCoeff_neg : longCoeff (-n) M = longCoeff n M := by
  simp only [longCoeff, sandwich, contract, nsq_neg, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
    mul_neg, neg_neg]

omit [CharZero K] in
theorem shear_neg : shear (-n) M = -shear n M := by
  funext β; simp only [shear, longCoeff_neg, contract, Pi.neg_apply, neg_mul,
    Finset.sum_neg_distrib, mul_neg]; ring

theorem scalarPart_neg : scalarPart (-n) M = scalarPart n M := by
  funext α β; simp only [scalarPart_apply, longCoeff_neg, nsq_neg, Pi.neg_apply]; ring

theorem vectorPart_neg : vectorPart (-n) M = vectorPart n M := by
  funext α β; simp only [vectorPart_apply, shear_neg, nsq_neg, Pi.neg_apply]; ring

theorem tensorPart_neg : tensorPart (-n) M = tensorPart n M := by
  rw [tensorPart_eq, tensorPart_eq, scalarPart_neg, vectorPart_neg]

theorem longVec_neg : longVec (-n) V = longVec n V := by
  funext α; simp only [longVec_apply, dot, nsq_neg, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

theorem transVec_neg : transVec (-n) V = transVec n V := by
  funext α; rw [transVec_apply, transVec_apply, longVec_neg]

variable (σ : K →+* K) {n}

omit [CharZero K] in
theorem longCoeff_map (hσ : ∀ γ, σ (n γ) = n γ) :
    longCoeff n (fun α β => σ (M α β)) = σ (longCoeff n M) := by
  simp only [longCoeff, sandwich, contract, nsq, map_div₀, map_sum, map_mul, map_pow, hσ]

omit [CharZero K] in
theorem shear_map (hσ : ∀ γ, σ (n γ) = n γ) (β : Fin 3) :
    shear n (fun α β => σ (M α β)) β = σ (shear n M β) := by
  simp only [shear, longCoeff_map M σ hσ, contract, map_sub, map_sum, map_mul, hσ]

theorem scalarPart_map (hσ : ∀ γ, σ (n γ) = n γ) (α β : Fin 3) :
    scalarPart n (fun α β => σ (M α β)) α β = σ (scalarPart n M α β) := by
  simp only [scalarPart_apply, longCoeff_map M σ hσ, trace, delta, nsq, map_add, map_sub,
    map_mul, map_div₀, map_sum, map_pow, hσ, map_ofNat, apply_ite σ, map_one, map_zero]

theorem vectorPart_map (hσ : ∀ γ, σ (n γ) = n γ) (α β : Fin 3) :
    vectorPart n (fun α β => σ (M α β)) α β = σ (vectorPart n M α β) := by
  simp only [vectorPart_apply, shear_map M σ hσ, nsq, map_add, map_mul, map_div₀, map_sum,
    map_pow, hσ]

theorem tensorPart_map (hσ : ∀ γ, σ (n γ) = n γ) (α β : Fin 3) :
    tensorPart n (fun α β => σ (M α β)) α β = σ (tensorPart n M α β) := by
  simp only [tensorPart_apply, scalarPart_map M σ hσ, vectorPart_map M σ hσ, map_sub]

theorem longVec_map (hσ : ∀ γ, σ (n γ) = n γ) (α : Fin 3) :
    longVec n (fun γ => σ (V γ)) α = σ (longVec n V α) := by
  simp only [longVec_apply, dot, nsq, map_mul, map_div₀, map_sum, map_pow, hσ]

theorem transVec_map (hσ : ∀ γ, σ (n γ) = n γ) (α : Fin 3) :
    transVec n (fun γ => σ (V γ)) α = σ (transVec n V α) := by
  simp only [transVec_apply, longVec_map V σ hσ, map_sub]

end Symmetries

/-- A linear map of matrices in terms of its values on the matrix units. -/
theorem linearMap_apply_eq_sum (L : Mat3 K →ₗ[K] Mat3 K) (M : Mat3 K) (α β : Fin 3) :
    L M α β = ∑ γ, ∑ δ, M γ δ * L (Pi.single γ (Pi.single δ 1)) α β := by
  have hM : M = ∑ γ, ∑ δ, M γ δ • (Pi.single γ (Pi.single δ 1) : Mat3 K) := by
    funext a b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
      mul_zero, ite_apply, Pi.zero_apply]
    simp [Finset.sum_ite_eq]
  conv_lhs => rw [hM]
  simp [map_sum, map_smul, Finset.sum_apply]

/-- A linear map of vectors in terms of its values on the unit vectors. -/
theorem linearMap_vec_apply_eq_sum (L : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) (V : Fin 3 → K)
    (α : Fin 3) : L V α = ∑ γ, V γ * L (Pi.single γ 1) α := by
  have hV : V = ∑ γ, V γ • (Pi.single γ 1 : Fin 3 → K) := by
    funext a
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hV]
  simp [map_sum, map_smul, Finset.sum_apply]

/-! ### The longitudinal projector -/

/-- The longitudinal projector `nn/|n|²`. -/
def longProj (n : Fin 3 → K) : Mat3 K := fun α β => n α * n β / nsq n

section LongProj

variable {n : Fin 3 → K}

theorem trace_longProj (hn : nsq n ≠ 0) : trace (longProj n) = 1 := by
  simp only [trace, longProj, ← Finset.sum_div, sum_mul_self, div_self hn]

theorem contract_longProj (hn : nsq n ≠ 0) : contract n (longProj n) = n := by
  funext β
  simp only [contract, longProj]
  rw [show (∑ γ, n γ * (n γ * n β / nsq n)) = (∑ γ, n γ * n γ) * n β / nsq n by
    rw [Finset.sum_mul, Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ => by ring,
    sum_mul_self]
  field_simp

theorem sandwich_longProj (hn : nsq n ≠ 0) : sandwich n (longProj n) = nsq n := by
  simp only [sandwich, contract_longProj hn, sum_mul_self]

variable [CharZero K]

omit [CharZero K] in
theorem scalarPart_longProj (hn : nsq n ≠ 0) : scalarPart n (longProj n) = longProj n := by
  funext α β
  rw [scalarPart_apply, longCoeff, sandwich_longProj hn, trace_longProj hn, div_self hn]
  simp [longProj]

omit [CharZero K] in
theorem shear_longProj (hn : nsq n ≠ 0) : shear n (longProj n) = 0 := by
  funext β; simp [shear, longCoeff, contract_longProj hn, sandwich_longProj hn, div_self hn]

omit [CharZero K] in
theorem vectorPart_longProj (hn : nsq n ≠ 0) : vectorPart n (longProj n) = 0 := by
  funext α β; rw [vectorPart_apply, shear_longProj hn]; simp

omit [CharZero K] in
theorem tensorPart_longProj (hn : nsq n ≠ 0) : tensorPart n (longProj n) = 0 := by
  rw [tensorPart_eq, scalarPart_longProj hn, vectorPart_longProj hn]; simp

end LongProj

/-! ### The symbols of the linearized equations -/

/-- `op n M = |n|² M + nn tr M − n ⊗ nM − nM ⊗ n`: twice the symbol of the variation
`δP_{αβ} = ½ (∂_γ∂_α h_{γβ} + ∂_γ∂_β h_{γα} − ∂_γ∂_γ h_{αβ} − ∂_α∂_β h)` of the spatial
Ricci tensor for `∂_α ↦ i n_α`. -/
def op (n : Fin 3 → K) : Mat3 K →ₗ[K] Mat3 K where
  toFun M α β := nsq n * M α β + n α * n β * trace M - n α * contract n M β -
    n β * contract n M α
  map_add' M N := by funext α β; simp only [trace_add, contract_add, Pi.add_apply]; ring
  map_smul' c M := by
    funext α β; simp only [trace_smul, contract_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

/-- `mix n M = nM − n tr M`, the symbol of `∂_γ ∂ₜ h_{γα} − ∂ₜ ∂_α h` up to the factor of the
time derivative. -/
def mix (n : Fin 3 → K) : Mat3 K →ₗ[K] (Fin 3 → K) where
  toFun M α := contract n M α - n α * trace M
  map_add' M N := by funext α; simp only [trace_add, contract_add, Pi.add_apply]; ring
  map_smul' c M := by
    funext α; simp only [trace_smul, contract_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

section Symbols

variable {n : Fin 3 → K} (M : Mat3 K)

variable [CharZero K]

omit [CharZero K] in
theorem op_apply (α β : Fin 3) : op n M α β = nsq n * M α β + n α * n β * trace M -
    n α * contract n M β - n β * contract n M α := rfl

omit [CharZero K] in
theorem mix_apply (α : Fin 3) : mix n M α = contract n M α - n α * trace M := rfl

omit [CharZero K] in
theorem trace_op : trace (op n M) = 2 * (nsq n * trace M - sandwich n M) := by
  simp only [trace, op_apply, contract, sandwich, nsq, Fin.sum_univ_three]; ring

omit [CharZero K] in
theorem contract_op : contract n (op n M) = fun β => (nsq n * trace M - sandwich n M) * n β := by
  funext β
  simp only [contract, op_apply, trace, sandwich, nsq, Fin.sum_univ_three]; ring

omit [CharZero K] in
theorem sandwich_op : sandwich n (op n M) = (nsq n * trace M - sandwich n M) * nsq n := by
  rw [sandwich, contract_op, ← dot]
  have : dot (fun β => (nsq n * trace M - sandwich n M) * n β) n =
      dot n (fun β => (nsq n * trace M - sandwich n M) * n β) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [this, dot_smul_self]

omit [CharZero K] in
theorem longCoeff_op (hn : nsq n ≠ 0) : longCoeff n (op n M) = nsq n * trace M - sandwich n M := by
  rw [longCoeff, sandwich_op, mul_div_cancel_right₀ _ hn]

omit [CharZero K] in
theorem shear_op (hn : nsq n ≠ 0) : shear n (op n M) = 0 := by
  funext β; simp [shear, contract_op, longCoeff_op M hn]

/-- The symbol `op` maps the scalar part to the scalar part of its image. -/
theorem scalarPart_op (hn : nsq n ≠ 0) : scalarPart n (op n M) = op n (scalarPart n M) := by
  funext α β
  rw [scalarPart_apply, longCoeff_op M hn, trace_op, op_apply, trace_scalarPart M hn,
    contract_scalarPart M hn, scalarPart_apply]
  simp only [longCoeff]
  field_simp
  ring

/-- The symbol `op` annihilates the vector part. -/
theorem op_vectorPart (hn : nsq n ≠ 0) : op n (vectorPart n M) = 0 := by
  funext α β
  rw [op_apply, trace_vectorPart M hn, contract_vectorPart M hn, vectorPart_apply]
  simp only [Pi.zero_apply]
  field_simp
  ring

theorem vectorPart_op (hn : nsq n ≠ 0) : vectorPart n (op n M) = op n (vectorPart n M) := by
  rw [op_vectorPart M hn]
  funext α β; rw [vectorPart_apply, shear_op M hn]; simp

theorem tensorPart_op (hn : nsq n ≠ 0) : tensorPart n (op n M) = op n (tensorPart n M) := by
  rw [tensorPart_eq, tensorPart_eq, map_sub, map_sub, scalarPart_op M hn, vectorPart_op M hn,
    op_vectorPart M hn]

/-- On the tensor part, `op` is the multiplication by `|n|²`. -/
theorem op_tensorPart (hn : nsq n ≠ 0) : op n (tensorPart n M) = nsq n • tensorPart n M := by
  funext α β
  rw [op_apply, trace_tensorPart M hn, contract_tensorPart M hn]
  simp

omit [CharZero K] in
theorem dot_mix : dot n (mix n M) = sandwich n M - nsq n * trace M := by
  have : mix n M = contract n M - fun α => trace M * n α := by
    funext α; simp only [mix_apply, Pi.sub_apply]; ring
  rw [this, dot_sub, dot_contract, dot_smul_self]; ring

/-- `mix` maps the scalar part to the longitudinal vectors. -/
theorem longVec_mix (hn : nsq n ≠ 0) : longVec n (mix n M) = mix n (scalarPart n M) := by
  funext α
  rw [longVec_apply, dot_mix, mix_apply, contract_scalarPart M hn, trace_scalarPart M hn]
  simp only [longCoeff]
  field_simp

/-- `mix` maps the vector part to the transverse vectors. -/
theorem transVec_mix (hn : nsq n ≠ 0) : transVec n (mix n M) = mix n (vectorPart n M) := by
  funext α
  rw [transVec_apply, longVec_mix M hn, mix_apply, mix_apply, mix_apply,
    contract_scalarPart M hn, trace_scalarPart M hn, contract_vectorPart M hn,
    trace_vectorPart M hn, shear]
  ring

@[simp] theorem mix_tensorPart (hn : nsq n ≠ 0) : mix n (tensorPart n M) = 0 := by
  funext α; rw [mix_apply, contract_tensorPart M hn, trace_tensorPart M hn]; simp

theorem mix_vectorPart (hn : nsq n ≠ 0) : mix n (vectorPart n M) = shear n M := by
  funext α; rw [mix_apply, contract_vectorPart M hn, trace_vectorPart M hn]; simp

omit [CharZero K] in
theorem op_longProj (hn : nsq n ≠ 0) : op n (longProj n) = 0 := by
  funext α β
  rw [op_apply, trace_longProj hn, contract_longProj hn]
  simp only [longProj, Pi.zero_apply]
  field_simp
  ring

end Symbols

/-- The coefficients of the linearized equations of a flat background at one time: the Hubble
rate `H = ȧ/a` (`hub`), `κρ` (`dens`), the factor `mixC` of the mixed equation, the
coefficients `c₁ = 2ȧ² + aä`, `c₂ = (3/2) aȧ`, `c₃ = a²/2`, `c₄ = aȧ/2` of the spatial
equation and `src = κρa²/2`. -/
structure Coeffs (K : Type*) where
  /-- The Hubble rate `ȧ/a`. -/
  hub : K
  /-- `κρ`. -/
  dens : K
  /-- The factor of the mixed equation (`½` for a real profile, `i/2` for `e^{in·x}`). -/
  mixC : K
  /-- The coefficient of `h` in `δR_{αβ}`. -/
  c₁ : K
  /-- The coefficient of `∂ₜh` in `δR_{αβ}`. -/
  c₂ : K
  /-- The coefficient of `∂ₜ²h` in `δR_{αβ}`. -/
  c₃ : K
  /-- The coefficient of `∂ₜ tr h δ_{αβ}` in `δR_{αβ}`. -/
  c₄ : K
  /-- `κρa²/2`, the factor of the spatial source. -/
  src : K

/-- The residual `δR₀₀ − κ δS₀₀ = −½ tr F₂ − H tr F₁ − ½ κρ D` of one frequency. -/
def resTime (P : Coeffs K) (F₁ F₂ : Mat3 K) (D : K) : K :=
  -trace F₂ / 2 - P.hub * trace F₁ - P.dens * D / 2

/-- The residual `δR₀α − κ δS₀α = c (nF₁ − n tr F₁) + κρ V` of one frequency. -/
def resMixed (P : Coeffs K) (n : Fin 3 → K) (F₁ : Mat3 K) (V : Fin 3 → K) : Fin 3 → K :=
  P.mixC • mix n F₁ + P.dens • V

/-- The residual `δR_{αβ} − κ δS_{αβ}` of one frequency:
`½ op F₀ + c₁ F₀ + c₂ F₁ + c₃ F₂ + (c₄ tr F₁ − s D) δ − s F₀`. -/
def resSpace (P : Coeffs K) (n : Fin 3 → K) (F₀ F₁ F₂ : Mat3 K) (D : K) : Mat3 K :=
  (2⁻¹ : K) • op n F₀ + P.c₁ • F₀ + P.c₂ • F₁ + P.c₃ • F₂ +
    (P.c₄ * trace F₁ - P.src * D) • delta K - P.src • F₀

/-- **The equations of one frequency**: the three residuals vanish. -/
def SymbolEq (P : Coeffs K) (n : Fin 3 → K) (F₀ F₁ F₂ : Mat3 K) (D : K) (V : Fin 3 → K) :
    Prop :=
  resTime P F₁ F₂ D = 0 ∧ resMixed P n F₁ V = 0 ∧ resSpace P n F₀ F₁ F₂ D = 0

section Split

variable {n : Fin 3 → K} (P : Coeffs K) (F₀ F₁ F₂ : Mat3 K) (D : K) (V : Fin 3 → K)

variable [CharZero K]

theorem resTime_scalarPart (hn : nsq n ≠ 0) :
    resTime P (scalarPart n F₁) (scalarPart n F₂) D = resTime P F₁ F₂ D := by
  simp [resTime, trace_scalarPart _ hn]

omit [CharZero K] in
theorem resTime_vectorPart (hn : nsq n ≠ 0) :
    resTime P (vectorPart n F₁) (vectorPart n F₂) 0 = 0 := by
  simp [resTime, trace_vectorPart _ hn]

theorem resTime_tensorPart (hn : nsq n ≠ 0) :
    resTime P (tensorPart n F₁) (tensorPart n F₂) 0 = 0 := by
  simp [resTime, trace_tensorPart _ hn]

theorem resMixed_scalarPart (hn : nsq n ≠ 0) :
    resMixed P n (scalarPart n F₁) (longVec n V) = longVec n (resMixed P n F₁ V) := by
  simp only [resMixed, map_add, map_smul, longVec_mix F₁ hn]

theorem resMixed_vectorPart (hn : nsq n ≠ 0) :
    resMixed P n (vectorPart n F₁) (transVec n V) = transVec n (resMixed P n F₁ V) := by
  simp only [resMixed, map_add, map_smul, transVec_mix F₁ hn]

theorem resMixed_tensorPart (hn : nsq n ≠ 0) : resMixed P n (tensorPart n F₁) 0 = 0 := by
  simp [resMixed, mix_tensorPart F₁ hn]

theorem resSpace_scalarPart (hn : nsq n ≠ 0) :
    resSpace P n (scalarPart n F₀) (scalarPart n F₁) (scalarPart n F₂) D =
      scalarPart n (resSpace P n F₀ F₁ F₂ D) := by
  simp only [resSpace, map_add, map_sub, map_smul, scalarPart_op F₀ hn, scalarPart_delta hn,
    trace_scalarPart _ hn]

theorem resSpace_vectorPart (hn : nsq n ≠ 0) :
    resSpace P n (vectorPart n F₀) (vectorPart n F₁) (vectorPart n F₂) 0 =
      vectorPart n (resSpace P n F₀ F₁ F₂ D) := by
  simp only [resSpace, map_add, map_sub, map_smul, vectorPart_op F₀ hn, vectorPart_delta hn,
    trace_vectorPart _ hn, mul_zero, sub_zero, zero_smul, smul_zero]

theorem resSpace_tensorPart (hn : nsq n ≠ 0) :
    resSpace P n (tensorPart n F₀) (tensorPart n F₁) (tensorPart n F₂) 0 =
      tensorPart n (resSpace P n F₀ F₁ F₂ D) := by
  simp only [resSpace, map_add, map_sub, map_smul, tensorPart_op F₀ hn, tensorPart_delta hn,
    trace_tensorPart _ hn, mul_zero, sub_zero, zero_smul, smul_zero]

/-- **The scalar–vector–tensor decomposition of the equations of one frequency**: for `n` with
`|n|² ≠ 0`, the system holds if and only if it holds for the scalar parts of the jets with the
density contrast and the longitudinal velocity, for the vector parts with the transverse velocity
and no density contrast, and for the tensor parts alone. -/
theorem symbolEq_iff (hn : nsq n ≠ 0) :
    SymbolEq P n F₀ F₁ F₂ D V ↔
      SymbolEq P n (scalarPart n F₀) (scalarPart n F₁) (scalarPart n F₂) D (longVec n V) ∧
      SymbolEq P n (vectorPart n F₀) (vectorPart n F₁) (vectorPart n F₂) 0 (transVec n V) ∧
      SymbolEq P n (tensorPart n F₀) (tensorPart n F₁) (tensorPart n F₂) 0 0 := by
  simp only [SymbolEq, resTime_scalarPart P F₁ F₂ D hn, resTime_vectorPart P F₁ F₂ hn,
    resTime_tensorPart P F₁ F₂ hn, resMixed_scalarPart P F₁ V hn,
    resMixed_vectorPart P F₁ V hn, resMixed_tensorPart P F₁ hn,
    resSpace_scalarPart P F₀ F₁ F₂ D hn, resSpace_vectorPart P F₀ F₁ F₂ D hn,
    resSpace_tensorPart P F₀ F₁ F₂ D hn, true_and]
  constructor
  · rintro ⟨h0, h1, h2⟩
    simp [h0, h1, h2]
  · rintro ⟨⟨h0, h1, h2⟩, ⟨h1', h2'⟩, h2''⟩
    refine ⟨h0, ?_, ?_⟩
    · rw [← longVec_add_transVec n (resMixed P n F₁ V), h1, h1', add_zero]
    · rw [← scalarPart_add_vectorPart_add_tensorPart n (resSpace P n F₀ F₁ F₂ D), h2, h2',
        h2'', add_zero, add_zero]


/-- **The tensor sector**: for the tensor parts of the jets, the system is the single equation
`(|n|²/2 + c₁ − s) T₀ + c₂ T₁ + c₃ T₂ = 0`. -/
theorem symbolEq_tensor_iff (hn : nsq n ≠ 0) :
    SymbolEq P n (tensorPart n F₀) (tensorPart n F₁) (tensorPart n F₂) 0 0 ↔
      (nsq n / 2 + P.c₁ - P.src) • tensorPart n F₀ + P.c₂ • tensorPart n F₁ +
        P.c₃ • tensorPart n F₂ = 0 := by
  have h0 : resTime P (tensorPart n F₁) (tensorPart n F₂) 0 = 0 := resTime_tensorPart P F₁ F₂ hn
  have h1 : resMixed P n (tensorPart n F₁) 0 = 0 := resMixed_tensorPart P F₁ hn
  have h2 : resSpace P n (tensorPart n F₀) (tensorPart n F₁) (tensorPart n F₂) 0 =
      (nsq n / 2 + P.c₁ - P.src) • tensorPart n F₀ + P.c₂ • tensorPart n F₁ +
        P.c₃ • tensorPart n F₂ := by
    simp only [resSpace, op_tensorPart _ hn, trace_tensorPart _ hn]
    funext α β
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [SymbolEq, h0, h1, h2, true_and]

/-- **The vector sector**: for the vector parts of the jets and a transverse velocity, the system
is `c u₁ + κρ V = 0` for the transverse vector `u₁` of `F₁` and
`(c₁ − s) V₀ + c₂ V₁ + c₃ V₂ = 0` for the vector parts. -/
theorem symbolEq_vector_iff (hn : nsq n ≠ 0) :
    SymbolEq P n (vectorPart n F₀) (vectorPart n F₁) (vectorPart n F₂) 0 (transVec n V) ↔
      P.mixC • shear n F₁ + P.dens • transVec n V = 0 ∧
        (P.c₁ - P.src) • vectorPart n F₀ + P.c₂ • vectorPart n F₁ +
          P.c₃ • vectorPart n F₂ = 0 := by
  have h0 : resTime P (vectorPart n F₁) (vectorPart n F₂) 0 = 0 := resTime_vectorPart P F₁ F₂ hn
  have h1 : resMixed P n (vectorPart n F₁) (transVec n V) =
      P.mixC • shear n F₁ + P.dens • transVec n V := by
    simp only [resMixed, mix_vectorPart _ hn]
  have h2 : resSpace P n (vectorPart n F₀) (vectorPart n F₁) (vectorPart n F₂) 0 =
      (P.c₁ - P.src) • vectorPart n F₀ + P.c₂ • vectorPart n F₁ + P.c₃ • vectorPart n F₂ := by
    simp only [resSpace, op_vectorPart _ hn, trace_vectorPart _ hn]
    funext α β
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  simp only [SymbolEq, h0, h1, h2, true_and]

omit [CharZero K] in
/-- The equations hold for vanishing jets. -/
theorem symbolEq_zero (n : Fin 3 → K) : SymbolEq P n 0 0 0 0 0 := by
  refine ⟨by simp [resTime], ?_, ?_⟩
  · funext α; simp [resMixed]
  · funext α β; simp [resSpace]

end Split

end ProjectAinos.SmoothGeometry.ScalarVectorTensor
