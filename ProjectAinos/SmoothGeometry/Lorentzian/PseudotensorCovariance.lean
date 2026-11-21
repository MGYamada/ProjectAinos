/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorFlux
import Mathlib.Tactic

/-!
# The superpotential under a linear change of co-ordinates

Landau–Lifshitz, §96: the pseudotensor is not a tensor, but under a *linear* change of the
co-ordinates it transforms as a tensor. For a coordinate metric `g` on an open set `U` of the
model and an invertible matrix `L`, the co-ordinates `x'` with `x = L x'` give the metric
`g'(x')(v, w) = g(L x')(L v, L w)` on the open set `L⁻¹ U` (`CoordinateMetric.linearPullback`).
With `M = L⁻¹`:

* `coefficient_linearPullback`: `g' = Lᵀ g L`; `inv_coefficient_linearPullback`:
  `g'^{-1} = M g^{-1} Mᵀ`; `densityOf_sq_linearPullback`: `|g'| = (det L)² |g|`.
* `superpotentialDensity_linearPullback`: `λ'^{iklm}(x') = (det L)² M^i_a M^k_b M^l_c M^m_e
  λ^{abce}(L x')`, a tensor density of weight two.
* `sum_fderiv_contract`: the divergence of a contravariant index is invariant,
  `∂'_m (M^m_e Λ^e(L x')) = (∂_e Λ^e)(L x')`.
* `superpotential_linearPullback`: `h'^{ikl}(x') = (det L)² M^i_a M^k_b M^l_c h^{abc}(L x')`;
  `totalDensity_linearPullback`: **the total density transforms as a tensor density**,
  `|g'| (G'^{ik} + t'^{ik})(x') = (det L)² M^i_a M^k_b |g| (G^{ab} + t^{ab})(L x')`; for
  `|det L| = 1`, as a tensor.
* `sum_fderiv_totalDensity`: the total density is conserved, `∂_k (|g| (G^{ik} + t^{ik})) = 0`.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Matrix

namespace ProjectAinos.SmoothGeometry

namespace CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

/-! ### The linear map of a matrix -/

/-- The continuous linear map `x ↦ L x` of a matrix. -/
def matrixMap (L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' L)

@[simp] theorem matrixMap_apply (L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : matrixMap L x = L *ᵥ x := by
  simp [matrixMap]

/-- The open set `L⁻¹ U` of the co-ordinates `x'` with `L x' ∈ U`. -/
def pullbackOpens (U : Opens (MinkowskiModel d)) (L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Opens (MinkowskiModel d) :=
  ⟨matrixMap L ⁻¹' U, U.isOpen.preimage (matrixMap L).continuous⟩

theorem mem_pullbackOpens {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d} :
    x ∈ pullbackOpens U L ↔ L *ᵥ x ∈ U := by
  change matrixMap L x ∈ U ↔ _
  rw [matrixMap_apply]

/-- The linear map of an invertible matrix, as a continuous linear equivalence. -/
def matrixEquiv (L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hL : L.det ≠ 0) :
    MinkowskiModel d ≃L[ℝ] MinkowskiModel d :=
  (LinearMap.equivOfDetNeZero (Matrix.toLin' L)
    (by rwa [LinearMap.det_toLin'])).toContinuousLinearEquiv

@[simp] theorem matrixEquiv_apply (L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hL : L.det ≠ 0)
    (x : MinkowskiModel d) : matrixEquiv L hL x = L *ᵥ x := by
  simp [matrixEquiv]

/-! ### Sums -/

/-- `Σ_{a,b,c,e} f_{ab} g_{ce} = (Σ_{a,b} f_{ab}) (Σ_{c,e} g_{ce})`. -/
theorem sum_mul_sum_four {n : ℕ} (f g : Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, f a b) * (∑ c, ∑ e, g c e) = ∑ a, ∑ b, ∑ c, ∑ e, f a b * g c e := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]

/-- Moving the outer sum of four innermost. -/
theorem sum_comm_four {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ e, ∑ a, ∑ b, ∑ c, F e a b c = ∑ a, ∑ b, ∑ c, ∑ e, F e a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- Moving the outer sum of three innermost. -/
theorem sum_comm_three {n : ℕ} (F : Fin n → Fin n → Fin n → ℝ) :
    ∑ e, ∑ a, ∑ b, F e a b = ∑ a, ∑ b, ∑ e, F e a b := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-! ### The metric in linearly transformed co-ordinates -/

variable (g : CoordinateMetric σ d U)

/-- **The metric in the co-ordinates `x'` with `x = L x'`**: `g'(x')(v, w) = g(L x')(L v, L w)` on
the open set `L⁻¹ U`. -/
def linearPullback (L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hL : L.det ≠ 0) :
    CoordinateMetric σ d (pullbackOpens U L) where
  form x := (g.form (matrixMap L x)).bilinearComp (matrixMap L) (matrixMap L)
  smooth := by
    refine contDiffOn_clm_apply.mpr fun v => contDiffOn_clm_apply.mpr fun w => ?_
    simp only [ContinuousLinearMap.bilinearComp_apply]
    exact ((g.smooth.comp (matrixMap L).contDiff.contDiffOn fun _ hx => hx).clm_apply
      contDiffOn_const).clm_apply contDiffOn_const
  signature x hx := by
    obtain ⟨e, he⟩ := g.signature (matrixMap L x) hx
    refine ⟨(matrixEquiv L hL).trans e, fun v w => ?_⟩
    rw [ContinuousLinearMap.bilinearComp_apply, he]
    simp

variable {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {hL : L.det ≠ 0}

theorem form_linearPullback (x v w : MinkowskiModel d) :
    (g.linearPullback L hL).form x v w = g.form (L *ᵥ x) (L *ᵥ v) (L *ᵥ w) := by
  simp [linearPullback]

/-- `g' = Lᵀ g(L x') L`. -/
theorem coefficient_linearPullback (x : MinkowskiModel d) :
    (g.linearPullback L hL).coefficient x = Lᵀ * g.coefficient (L *ᵥ x) * L := by
  ext i j
  rw [coefficient, Matrix.of_apply, form_linearPullback, form_apply]
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply,
    Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- `g'^{-1} = M g^{-1} Mᵀ` with `M = L⁻¹`. -/
theorem inv_coefficient_linearPullback (x : MinkowskiModel d) (i k : Fin (d + 1)) :
    ((g.linearPullback L hL).coefficient x)⁻¹ i k =
      ∑ a, ∑ b, L⁻¹ i a * L⁻¹ k b * (g.coefficient (L *ᵥ x))⁻¹ a b := by
  rw [coefficient_linearPullback, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    ← Matrix.transpose_nonsing_inv]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- `|g'| = (det L)² |g|`. -/
theorem densityOf_sq_linearPullback (x : MinkowskiModel d) :
    densityOf (g.linearPullback L hL).coefficient x ^ 2 =
      L.det ^ 2 * densityOf g.coefficient (L *ᵥ x) ^ 2 := by
  rw [densityOf, densityOf, Real.sq_sqrt (abs_nonneg _), Real.sq_sqrt (abs_nonneg _),
    coefficient_linearPullback, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, abs_mul,
    abs_mul, ← sq_abs L.det]
  ring

/-! ### The superpotential density -/

/-- **The superpotential density is a tensor density of weight two**:
`λ'^{iklm}(x') = (det L)² M^m_e (M^i_a M^k_b M^l_c λ^{abce}(L x'))`. -/
theorem superpotentialDensity_linearPullback (x : MinkowskiModel d) (i k l m : Fin (d + 1)) :
    (g.linearPullback L hL).superpotentialDensity x i k l m =
      L.det ^ 2 * ∑ e, L⁻¹ m e * ∑ a, ∑ b, ∑ c,
        L⁻¹ i a * L⁻¹ k b * L⁻¹ l c * g.superpotentialDensity (L *ᵥ x) a b c e := by
  unfold superpotentialDensity
  rw [densityOf_sq_linearPullback, inv_coefficient_linearPullback,
    inv_coefficient_linearPullback, inv_coefficient_linearPullback,
    inv_coefficient_linearPullback, sum_mul_sum_four, sum_mul_sum_four]
  have h2 : ∑ a, ∑ b, ∑ c, ∑ e, L⁻¹ i a * L⁻¹ l b * (g.coefficient (L *ᵥ x))⁻¹ a b *
      (L⁻¹ k c * L⁻¹ m e * (g.coefficient (L *ᵥ x))⁻¹ c e) =
      ∑ a, ∑ c, ∑ b, ∑ e, L⁻¹ i a * L⁻¹ l b * (g.coefficient (L *ᵥ x))⁻¹ a b *
        (L⁻¹ k c * L⁻¹ m e * (g.coefficient (L *ᵥ x))⁻¹ c e) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [h2]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  conv_rhs => rw [sum_comm_four]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  ring

/-! ### Divergences under a linear change of co-ordinates -/

/-- The derivative of `w ↦ f(L w)` along the axis `m` is `Σ_n L_{nm} ∂_n f(L x)`. -/
theorem fderiv_comp_mulVec {f : MinkowskiModel d → ℝ} {x : MinkowskiModel d}
    (hf : DifferentiableAt ℝ f (L *ᵥ x)) (m : Fin (d + 1)) :
    fderiv ℝ (fun w => f (L *ᵥ w)) x (Pi.single m 1) =
      ∑ n, L n m * fderiv ℝ f (L *ᵥ x) (Pi.single n 1) := by
  have hf' : DifferentiableAt ℝ f (matrixMap L x) := by rwa [matrixMap_apply]
  have h := hf'.hasFDerivAt.comp x (matrixMap L).hasFDerivAt
  have he : (fun w => f (L *ᵥ w)) = f ∘ matrixMap L := funext fun w => by simp
  rw [he, h.fderiv, ContinuousLinearMap.comp_apply, matrixMap_apply, matrixMap_apply,
    Matrix.mulVec_single_one]
  have hcol : L.col m = ∑ n, L n m • (Pi.single n 1 : MinkowskiModel d) := by
    ext j
    simp [Pi.single_apply]
  rw [hcol, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- `Σ_m M_{me} Σ_n L_{nm} y_n = y_e` for `M = L⁻¹`. -/
theorem sum_inv_mul_sum (hL : L.det ≠ 0) (y : Fin (d + 1) → ℝ) (e : Fin (d + 1)) :
    ∑ m, L⁻¹ m e * ∑ n, L n m * y n = y e := by
  have h1 : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv L (isUnit_iff_ne_zero.mpr hL)
  calc ∑ m, L⁻¹ m e * ∑ n, L n m * y n = ∑ n, (∑ m, L n m * L⁻¹ m e) * y n := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
    _ = ∑ n, (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) n e * y n :=
        Finset.sum_congr rfl fun n _ => by rw [← Matrix.mul_apply, h1]
    _ = y e := by simp [Matrix.one_apply]

/-- **The divergence of a contravariant index is invariant under a linear change of the
co-ordinates**: if `F^m(w) = M^m_e Λ^e(L w)` near `x`, then `∂_m F^m(x) = (∂_e Λ^e)(L x)`. -/
theorem sum_fderiv_contract (hL : L.det ≠ 0) {F Λ : Fin (d + 1) → MinkowskiModel d → ℝ}
    {x : MinkowskiModel d} (hΛ : ∀ e, DifferentiableAt ℝ (Λ e) (L *ᵥ x))
    (hF : ∀ m, F m =ᶠ[𝓝 x] fun w => ∑ e, L⁻¹ m e * Λ e (L *ᵥ w)) :
    ∑ m, fderiv ℝ (F m) x (Pi.single m 1) = ∑ e, fderiv ℝ (Λ e) (L *ᵥ x) (Pi.single e 1) := by
  have hd (e : Fin (d + 1)) : DifferentiableAt ℝ (fun w => Λ e (L *ᵥ w)) x := by
    have h := ((hΛ e).comp x ((matrixMap L).differentiableAt (x := x)))
    simpa [Function.comp_def] using h
  have hm (m : Fin (d + 1)) : fderiv ℝ (F m) x (Pi.single m 1) =
      ∑ e, L⁻¹ m e * ∑ n, L n m * fderiv ℝ (Λ e) (L *ᵥ x) (Pi.single n 1) := by
    rw [(hF m).fderiv_eq, fderiv_fun_sum fun e _ => (hd e).const_mul _, sum_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [fderiv_const_mul (hd e), smul_apply, smul_eq_mul,
      fderiv_comp_mulVec (hΛ e)]
  simp only [hm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h := sum_inv_mul_sum hL (fun n => fderiv ℝ (Λ e) (L *ᵥ x) (Pi.single n 1)) e
  rw [← h]

/-! ### The superpotential and the total density -/

/-- **The superpotential transforms as a tensor density of weight two**:
`h'^{ikl}(x') = (det L)² M^i_a M^k_b M^l_c h^{abc}(L x')` on `L⁻¹ U`. -/
theorem superpotential_linearPullback {x : MinkowskiModel d} (hx : x ∈ pullbackOpens U L)
    (i k l : Fin (d + 1)) :
    (g.linearPullback L hL).superpotential x i k l =
      L.det ^ 2 * ∑ a, ∑ b, ∑ c, L⁻¹ i a * L⁻¹ k b * L⁻¹ l c * g.superpotential (L *ᵥ x) a b c := by
  have hU := U.isOpen.mem_nhds (mem_pullbackOpens.mp hx)
  have hlam (a b c e : Fin (d + 1)) :
      DifferentiableAt ℝ (fun z => g.superpotentialDensity z a b c e) (L *ᵥ x) :=
    ((g.contDiffOn_superpotentialDensity a b c e).contDiffAt hU).differentiableAt (by simp)
  set Λ : Fin (d + 1) → MinkowskiModel d → ℝ := fun e z => L.det ^ 2 * ∑ a, ∑ b, ∑ c,
    L⁻¹ i a * L⁻¹ k b * L⁻¹ l c * g.superpotentialDensity z a b c e with hΛdef
  have hΛd (e : Fin (d + 1)) : HasFDerivAt (Λ e) (L.det ^ 2 • ∑ a, ∑ b, ∑ c,
      (L⁻¹ i a * L⁻¹ k b * L⁻¹ l c) • fderiv ℝ (fun z => g.superpotentialDensity z a b c e)
        (L *ᵥ x)) (L *ᵥ x) :=
    (HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ => HasFDerivAt.fun_sum
      fun c _ => (hlam a b c e).hasFDerivAt.const_mul _).const_mul _
  have hF (m : Fin (d + 1)) : (fun w => (g.linearPullback L hL).superpotentialDensity w i k l m)
      =ᶠ[𝓝 x] fun w => ∑ e, L⁻¹ m e * Λ e (L *ᵥ w) := Eventually.of_forall fun w => by
    simp only [hΛdef]
    rw [superpotentialDensity_linearPullback, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  have h := sum_fderiv_contract hL (fun e => (hΛd e).differentiableAt) hF
  unfold superpotential
  rw [h]
  simp only [(hΛd _).fderiv, smul_apply, sum_apply, smul_eq_mul]
  rw [← Finset.mul_sum, sum_comm_four]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]

/-- **The total density is conserved**: `∂_k (|g| (G^{ik} + t^{ik})) = 0` on `U`. -/
theorem sum_fderiv_totalDensity {z : MinkowskiModel d} (hz : z ∈ U) (i : Fin (d + 1)) :
    ∑ k, fderiv ℝ (fun w => g.totalDensity w i k) z (Pi.single k 1) = 0 := by
  have hU := U.isOpen.mem_nhds hz
  have hev (k : Fin (d + 1)) : (fun w => g.totalDensity w i k) =ᶠ[𝓝 z]
      fun w => (1 / 2 : ℝ) * ∑ l, fderiv ℝ (fun v => g.superpotential v i k l) w
        (Pi.single l 1) :=
    eventually_of_mem hU fun w hw => by
      simp only
      rw [g.sum_fderiv_superpotential hw]
      ring
  have hd (k : Fin (d + 1)) : DifferentiableAt ℝ
      (fun w => ∑ l, fderiv ℝ (fun v => g.superpotential v i k l) w (Pi.single l 1)) z :=
    DifferentiableAt.fun_sum fun l _ =>
      ((((g.contDiffOn_superpotential i k l).fderiv_of_isOpen U.isOpen (m := ∞)
        (by simp)).clm_apply contDiffOn_const).contDiffAt hU).differentiableAt (by simp)
  have h := g.divergence_divergence_superpotential hz i
  calc ∑ k, fderiv ℝ (fun w => g.totalDensity w i k) z (Pi.single k 1) =
        ∑ k, (1 / 2 : ℝ) * fderiv ℝ (fun w => ∑ l, fderiv ℝ (fun v => g.superpotential v i k l) w
          (Pi.single l 1)) z (Pi.single k 1) :=
        Finset.sum_congr rfl fun k _ => by
          rw [(hev k).fderiv_eq, fderiv_const_mul (hd k), smul_apply, smul_eq_mul]
    _ = 0 := by rw [← Finset.mul_sum, h, mul_zero]

/-- **The total density transforms as a tensor density of weight two**:
`|g'| (G'^{ik} + t'^{ik})(x') = (det L)² M^i_a M^k_b |g| (G^{ab} + t^{ab})(L x')` on `L⁻¹ U`;
for `|det L| = 1` it transforms as a tensor. -/
theorem totalDensity_linearPullback {x : MinkowskiModel d} (hx : x ∈ pullbackOpens U L)
    (i k : Fin (d + 1)) :
    (g.linearPullback L hL).totalDensity x i k =
      L.det ^ 2 * ∑ a, ∑ b, L⁻¹ i a * L⁻¹ k b * g.totalDensity (L *ᵥ x) a b := by
  have hLx := mem_pullbackOpens.mp hx
  have hU := U.isOpen.mem_nhds hLx
  have hh (a b c : Fin (d + 1)) :
      DifferentiableAt ℝ (fun z => g.superpotential z a b c) (L *ᵥ x) :=
    ((g.contDiffOn_superpotential a b c).contDiffAt hU).differentiableAt (by simp)
  set Λ : Fin (d + 1) → MinkowskiModel d → ℝ := fun c z => L.det ^ 2 * ∑ a, ∑ b,
    L⁻¹ i a * L⁻¹ k b * g.superpotential z a b c with hΛdef
  have hΛd (c : Fin (d + 1)) : HasFDerivAt (Λ c) (L.det ^ 2 • ∑ a, ∑ b,
      (L⁻¹ i a * L⁻¹ k b) • fderiv ℝ (fun z => g.superpotential z a b c) (L *ᵥ x)) (L *ᵥ x) :=
    (HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ =>
      (hh a b c).hasFDerivAt.const_mul _).const_mul _
  have hF (l : Fin (d + 1)) : (fun w => (g.linearPullback L hL).superpotential w i k l)
      =ᶠ[𝓝 x] fun w => ∑ c, L⁻¹ l c * Λ c (L *ᵥ w) :=
    eventually_of_mem ((pullbackOpens U L).isOpen.mem_nhds hx) fun w hw => by
      show (g.linearPullback L hL).superpotential w i k l = ∑ c, L⁻¹ l c * (L.det ^ 2 *
        ∑ a, ∑ b, L⁻¹ i a * L⁻¹ k b * g.superpotential (L *ᵥ w) a b c)
      rw [g.superpotential_linearPullback hw]
      simp only [Finset.mul_sum]
      conv_rhs => rw [sum_comm_three]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => by ring
  have h := sum_fderiv_contract hL (fun c => (hΛd c).differentiableAt) hF
  have h2 := (g.linearPullback L hL).sum_fderiv_superpotential hx i k
  rw [h] at h2
  simp only [(hΛd _).fderiv, smul_apply, sum_apply, smul_eq_mul] at h2
  rw [← Finset.mul_sum, sum_comm_three] at h2
  have h4 : ∑ a, ∑ b, ∑ c, L⁻¹ i a * L⁻¹ k b *
      fderiv ℝ (fun z => g.superpotential z a b c) (L *ᵥ x) (Pi.single c 1) =
      ∑ a, ∑ b, L⁻¹ i a * L⁻¹ k b * (2 * g.totalDensity (L *ᵥ x) a b) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [← g.sum_fderiv_superpotential hLx, Finset.mul_sum]
  rw [h4] at h2
  have h5 : ∑ a, ∑ b, L⁻¹ i a * L⁻¹ k b * (2 * g.totalDensity (L *ᵥ x) a b) =
      2 * ∑ a, ∑ b, L⁻¹ i a * L⁻¹ k b * g.totalDensity (L *ᵥ x) a b := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [h5] at h2
  linarith

end CoordinateMetric

end ProjectAinos.SmoothGeometry
