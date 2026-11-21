/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CurvedLinearization

/-!
# Leibniz rules for covariant derivatives of coefficient arrays

For a coordinate metric `g` on an open set `U` with `Γ = christoffelOf g.coefficient`, this file
adds the covariant derivative of a covector field and the rules that move a derivative through an
index raised with `g^{-1}`; they all express the compatibility `∇g^{-1} = 0` in co-ordinates.

* `covDerivOne`: `∇_a w_i = ∂_a w_i − Γ^b_{ai} w_b`; `covDerivLowThree`: the covariant derivative
  `∇_m p_{ijl}` of an array with three lower indices.
* `fderiv_raise`: `∂_m (g^{il} q_l) = −Γ^i_{mb} g^{bl} q_l + g^{il} ∇_m q_l`.
* `covDerivThree_raise`: `∇_m (g^{kl} p_{ijl}) = g^{kl} ∇_m p_{ijl}`; with `symbolLower` and
  `covDerivLowThree_symbolLower` this gives `covDerivThree_symbolChristoffel`: the covariant
  derivative of `Q(w, A)` is `Q(∇w, A) + Q(w, ∇A)`.
* `fderiv_trace`: `∂_m (g^{il} T_{il}) = g^{il} ∇_m T_{il}`; `fderiv_tensorPairing`: the
  derivative of the full contraction `⟨A, B⟩ = g^{ce} g^{df} A_{cd} B_{ef}` (`tensorPairing`) is
  `⟨∇A, B⟩ + ⟨A, ∇B⟩`, with `∇_m A` as a matrix (`covDerivMatrix`).
* `covDerivTwo_mul`: `∇_m (u_i v_j) = ∇_m u_i v_j + u_i ∇_m v_j`, `covDerivOne_smul`,
  `covDerivOne_raise_contract`: the Leibniz rule for `(w·A)_k = g^{ml} w_l A_{mk}`.
* `covDerivOne_gradient_symm`: `∇_i ∂_j ψ = ∇_j ∂_i ψ`; `gradientCovector_gradientNorm`:
  `∂_m g(dψ, dψ) = 2 k^a ∇_m ∂_a ψ`, with `k = (dψ)^♯`; `covDerivTwo_symm`: `∇_m A_{pq}` is
  symmetric for a symmetric field; `covDerivOne_congr`: the derivative depends on the germ.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

section Definitions

variable (g : CoordinateMetric σ d U)

/-- The covariant derivative `∇_a w_i = ∂_a w_i − Γ^b_{ai} w_b` of a covector field. -/
def covDerivOne (w : MinkowskiModel d → Fin (d + 1) → ℝ) (x : MinkowskiModel d)
    (a i : Fin (d + 1)) : ℝ :=
  fderiv ℝ (fun z => w z i) x (Pi.single a 1) - ∑ b, christoffelOf g.coefficient x b a i * w x b

/-- The covariant derivative `∇_m p_{ijl} = ∂_m p_{ijl} − Γ^b_{mi} p_{bjl} − Γ^b_{mj} p_{ibl}
− Γ^b_{ml} p_{ijb}` of an array with three lower indices. -/
def covDerivLowThree (p : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (x : MinkowskiModel d) (m i j l : Fin (d + 1)) : ℝ :=
  fderiv ℝ (fun z => p z i j l) x (Pi.single m 1) -
    ∑ b, (christoffelOf g.coefficient x b m i * p x b j l +
      christoffelOf g.coefficient x b m j * p x i b l +
      christoffelOf g.coefficient x b m l * p x i j b)

end Definitions

/-- The lowered symbol `½ (w_i A_{jl} + w_j A_{li} − w_l A_{ij})`, with
`Q(w, A)^k_{ij} = g^{kl} symbolLower w A i j l`. -/
def symbolLower {n : ℕ} (w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (i j l : Fin n) : ℝ :=
  (w i * A j l + w j * A l i - w l * A i j) / 2

variable {g : CoordinateMetric σ d U}

theorem differentiableAt_coefficient_inv {x : MinkowskiModel d} (hx : x ∈ U)
    (a b : Fin (d + 1)) : DifferentiableAt ℝ (fun z => (g.coefficient z)⁻¹ a b) x :=
  ((g.contDiffOn_coefficient_inv a b).contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt
    (by simp)

theorem differentiableAt_christoffelOf {x : MinkowskiModel d} (hx : x ∈ U)
    (a b c : Fin (d + 1)) : DifferentiableAt ℝ (fun z => christoffelOf g.coefficient z a b c) x :=
  ((g.contDiffOn_christoffelOf a b c).contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt
    (by simp)

theorem differentiableAt_of_contDiffOn {f : MinkowskiModel d → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    {x : MinkowskiModel d} (hx : x ∈ U) : DifferentiableAt ℝ f x :=
  (hf.contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt (by simp)

/-! ### Raising an index -/

/-- **The derivative of a raised covector**:
`∂_m (g^{il} q_l) = −Γ^i_{mb} g^{bl} q_l + g^{il} ∇_m q_l`. -/
theorem fderiv_raise {q : MinkowskiModel d → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U) (hq : ∀ l, DifferentiableAt ℝ (fun z => q z l) x) (i m : Fin (d + 1)) :
    fderiv ℝ (fun z => ∑ l, (g.coefficient z)⁻¹ i l * q z l) x (Pi.single m 1) =
      -∑ b, christoffelOf g.coefficient x i m b * ∑ l, (g.coefficient x)⁻¹ b l * q x l +
        ∑ l, (g.coefficient x)⁻¹ i l * g.covDerivOne q x m l := by
  rw [fderiv_sum_mul _ (fun l _ => differentiableAt_coefficient_inv hx i l) (fun l _ => hq l)]
  simp only [g.fderiv_coefficient_inv hx]
  set Γ := christoffelOf g.coefficient x
  set G := (g.coefficient x)⁻¹
  unfold covDerivOne
  have h1 : ∑ l, (-∑ e, (Γ i m e * G e l + Γ l m e * G i e)) * q x l =
      -∑ b, Γ i m b * ∑ l, G b l * q x l - ∑ l, G i l * ∑ b, Γ b m l * q x b := by
    have e1 : ∑ l, ∑ e, Γ i m e * G e l * q x l = ∑ b, Γ i m b * ∑ l, G b l * q x l := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have e2 : ∑ l, ∑ e, Γ l m e * G i e * q x l = ∑ l, G i l * ∑ b, Γ b m l * q x b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [← e1, ← e2]
    simp only [neg_mul, Finset.sum_neg_distrib, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    ring
  rw [Finset.sum_add_distrib, h1]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Raising the index of a lowered three-array commutes with the covariant derivative:
`∇_m (g^{kl} p_{ijl}) = g^{kl} ∇_m p_{ijl}`. -/
theorem covDerivThree_raise {p : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hx : x ∈ U) (hp : ∀ i j l, DifferentiableAt ℝ (fun z => p z i j l) x)
    (m k i j : Fin (d + 1)) :
    g.covDerivThree (fun z k i j => ∑ l, (g.coefficient z)⁻¹ k l * p z i j l) x m k i j =
      ∑ l, (g.coefficient x)⁻¹ k l * g.covDerivLowThree p x m i j l := by
  unfold covDerivThree
  rw [fderiv_raise (q := fun z l => p z i j l) hx (fun l => hp i j l) k m]
  set Γ := christoffelOf g.coefficient x
  set G := (g.coefficient x)⁻¹
  unfold covDerivOne covDerivLowThree
  have e1 : ∑ b, (Γ k m b * ∑ l, G b l * p x i j l - Γ b m i * ∑ l, G k l * p x b j l -
      Γ b m j * ∑ l, G k l * p x i b l) =
      ∑ b, Γ k m b * ∑ l, G b l * p x i j l -
        ∑ l, G k l * ∑ b, (Γ b m i * p x b j l + Γ b m j * p x i b l) := by
    have e2 : ∑ b, (Γ b m i * ∑ l, G k l * p x b j l + Γ b m j * ∑ l, G k l * p x i b l) =
        ∑ l, G k l * ∑ b, (Γ b m i * p x b j l + Γ b m j * p x i b l) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ => by ring
    rw [← e2]
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [e1]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  ring

/-- `Q(w, A)` with the index raised from `symbolLower`. -/
theorem symbolChristoffel_eq_sum (w : Fin (d + 1) → ℝ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.symbolChristoffel w A x k i j = ∑ l, (g.coefficient x)⁻¹ k l * symbolLower w A i j l := by
  unfold symbolChristoffel symbolLower
  exact Finset.sum_congr rfl fun l _ => by ring

/-- The Leibniz rule for the lowered symbol:
`∇_m (½ (w_i A_{jl} + w_j A_{li} − w_l A_{ij})) = symbolLower (∇_m w) A + symbolLower w (∇_m A)`. -/
theorem covDerivLowThree_symbolLower {w : MinkowskiModel d → Fin (d + 1) → ℝ}
    {A : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hw : ∀ i, DifferentiableAt ℝ (fun z => w z i) x)
    (hA : ∀ p q, DifferentiableAt ℝ (fun z => A z p q) x) (m i j l : Fin (d + 1)) :
    g.covDerivLowThree (fun z => symbolLower (w z) (A z)) x m i j l =
      symbolLower (fun c => g.covDerivOne w x m c) (A x) i j l +
        symbolLower (w x) (Matrix.of fun p q => g.covDerivTwo A x m p q) i j l := by
  have hd (p q c : Fin (d + 1)) : fderiv ℝ (fun z => w z c * A z p q) x (Pi.single m 1) =
      fderiv ℝ (fun z => w z c) x (Pi.single m 1) * A x p q +
        w x c * fderiv ℝ (fun z => A z p q) x (Pi.single m 1) := by
    rw [fderiv_fun_mul (hw c) (hA p q)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hf : fderiv ℝ (fun z => symbolLower (w z) (A z) i j l) x (Pi.single m 1) =
      (fderiv ℝ (fun z => w z i * A z j l) x (Pi.single m 1) +
        fderiv ℝ (fun z => w z j * A z l i) x (Pi.single m 1) -
        fderiv ℝ (fun z => w z l * A z i j) x (Pi.single m 1)) / 2 := by
    have e : (fun z => symbolLower (w z) (A z) i j l) = fun z =>
        (w z i * A z j l + w z j * A z l i - w z l * A z i j) * (2 : ℝ)⁻¹ := by
      funext z
      simp only [symbolLower, div_eq_mul_inv]
    rw [e, fderiv_mul_const ((((hw i).fun_mul (hA j l)).fun_add ((hw j).fun_mul
      (hA l i))).fun_sub ((hw l).fun_mul (hA i j))), fderiv_fun_sub (((hw i).fun_mul
      (hA j l)).fun_add ((hw j).fun_mul (hA l i))) ((hw l).fun_mul (hA i j)),
      fderiv_fun_add ((hw i).fun_mul (hA j l)) ((hw j).fun_mul (hA l i))]
    simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  unfold covDerivLowThree
  rw [hf, hd, hd, hd]
  unfold covDerivOne covDerivTwo symbolLower
  simp only [Matrix.of_apply]
  set Γ := christoffelOf g.coefficient x
  simp only [mul_sub, sub_mul, Finset.mul_sum, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div, sub_div, add_div]
  simp only [Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  ring

/-- **The Leibniz rule for `Q(w, A)`**: `∇_m Q(w, A) = Q(∇_m w, A) + Q(w, ∇_m A)`. -/
theorem covDerivThree_symbolChristoffel {w : MinkowskiModel d → Fin (d + 1) → ℝ}
    {A : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U) (hw : ∀ i, DifferentiableAt ℝ (fun z => w z i) x)
    (hA : ∀ p q, DifferentiableAt ℝ (fun z => A z p q) x) (m k i j : Fin (d + 1)) :
    g.covDerivThree (fun z => g.symbolChristoffel (w z) (A z) z) x m k i j =
      g.symbolChristoffel (fun c => g.covDerivOne w x m c) (A x) x k i j +
        g.symbolChristoffel (w x) (Matrix.of fun p q => g.covDerivTwo A x m p q) x k i j := by
  have hfun : (fun z => g.symbolChristoffel (w z) (A z) z) =
      fun z k i j => ∑ l, (g.coefficient z)⁻¹ k l * symbolLower (w z) (A z) i j l :=
    funext fun z => funext fun k => funext fun i => funext fun j =>
      symbolChristoffel_eq_sum _ _ _ _ _ _
  have hp (i j l : Fin (d + 1)) :
      DifferentiableAt ℝ (fun z => symbolLower (w z) (A z) i j l) x := by
    unfold symbolLower
    simp only [div_eq_mul_inv]
    exact ((((hw i).fun_mul (hA j l)).fun_add ((hw j).fun_mul (hA l i))).fun_sub
      ((hw l).fun_mul (hA i j))).mul_const (2 : ℝ)⁻¹
  rw [hfun, covDerivThree_raise (p := fun z => symbolLower (w z) (A z)) hx hp,
    symbolChristoffel_eq_sum, symbolChristoffel_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [covDerivLowThree_symbolLower hw hA, mul_add]

/-! ### Traces and contractions -/

/-- **The derivative of a trace**: `∂_m (g^{il} T_{il}) = g^{il} ∇_m T_{il}`. -/
theorem fderiv_trace {T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hx : x ∈ U) (hT : ∀ p q, DifferentiableAt ℝ (fun z => T z p q) x)
    (m : Fin (d + 1)) :
    fderiv ℝ (fun z => ∑ i, ∑ l, (g.coefficient z)⁻¹ i l * T z i l) x (Pi.single m 1) =
      ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * g.covDerivTwo T x m i l := by
  rw [fderiv_fun_sum (fun i _ => DifferentiableAt.fun_sum fun l _ =>
    (differentiableAt_coefficient_inv hx i l).fun_mul (hT i l)), _root_.sum_apply]
  refine (Finset.sum_congr rfl fun i _ =>
    fderiv_raise (q := fun z l => T z i l) hx (fun l => hT i l) i m).trans ?_
  set Γ := christoffelOf g.coefficient x
  set G := (g.coefficient x)⁻¹
  unfold covDerivOne covDerivTwo
  have key : ∑ i, ∑ b, Γ i m b * ∑ l, G b l * T x i l =
      ∑ i, ∑ l, G i l * ∑ b, Γ b m i * T x b l := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ => by ring
  have e1 : ∑ i, (-∑ b, Γ i m b * ∑ l, G b l * T x i l +
      ∑ l, G i l * (fderiv ℝ (fun z => T z i l) x (Pi.single m 1) - ∑ b, Γ b m l * T x i b)) =
      -∑ i, ∑ b, Γ i m b * ∑ l, G b l * T x i l +
        ∑ i, ∑ l, G i l * (fderiv ℝ (fun z => T z i l) x (Pi.single m 1) -
          ∑ b, Γ b m l * T x i b) := by
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [e1, key, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_add_distrib]
  ring

/-- The full contraction `⟨A, B⟩ = g^{ce} g^{df} A_{cd} B_{ef}` of two matrices at `x`. -/
def tensorPairing (g : CoordinateMetric σ d U) (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : ℝ :=
  ∑ c, ∑ e, (g.coefficient x)⁻¹ c e * ∑ p, ∑ q, (g.coefficient x)⁻¹ p q * (A c p * B e q)

/-- The covariant derivative of a matrix field as a matrix, `(∇_m A)_{pq}`. -/
def covDerivMatrix (g : CoordinateMetric σ d U)
    (A : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (m : Fin (d + 1)) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun p q => g.covDerivTwo A x m p q

/-- **The derivative of the full contraction**: `∂_m ⟨A, B⟩ = ⟨∇_m A, B⟩ + ⟨A, ∇_m B⟩`. -/
theorem fderiv_tensorPairing {A B : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hx : x ∈ U) (hA : ∀ p q, DifferentiableAt ℝ (fun z => A z p q) x)
    (hB : ∀ p q, DifferentiableAt ℝ (fun z => B z p q) x) (m : Fin (d + 1)) :
    fderiv ℝ (fun z => tensorPairing g (A z) (B z) z) x (Pi.single m 1) =
      tensorPairing g (g.covDerivMatrix A x m) (B x) x +
        tensorPairing g (A x) (g.covDerivMatrix B x m) x := by
  set N : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := fun z =>
    Matrix.of fun c e => ∑ p, ∑ q, (g.coefficient z)⁻¹ p q * (A z c p * B z e q) with hNdef
  have hN (c e : Fin (d + 1)) : DifferentiableAt ℝ (fun z => N z c e) x := by
    show DifferentiableAt ℝ (fun z => ∑ p, ∑ q, (g.coefficient z)⁻¹ p q * (A z c p * B z e q)) x
    exact DifferentiableAt.fun_sum fun p _ => DifferentiableAt.fun_sum fun q _ =>
      (differentiableAt_coefficient_inv hx p q).fun_mul ((hA c p).fun_mul (hB e q))
  have hfun : (fun z => tensorPairing g (A z) (B z) z) =
      fun z => ∑ c, ∑ e, (g.coefficient z)⁻¹ c e * N z c e := rfl
  rw [hfun, fderiv_trace hx hN]
  have hT (c e : Fin (d + 1)) (p q : Fin (d + 1)) :
      DifferentiableAt ℝ (fun z => (Matrix.of fun p q => A z c p * B z e q :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) p q) x := (hA c p).fun_mul (hB e q)
  have hdN (c e : Fin (d + 1)) : fderiv ℝ (fun z => N z c e) x (Pi.single m 1) =
      ∑ p, ∑ q, (g.coefficient x)⁻¹ p q * g.covDerivTwo
        (fun z => Matrix.of fun p q => A z c p * B z e q) x m p q :=
    fderiv_trace (T := fun z => Matrix.of fun p q => A z c p * B z e q) hx (hT c e) m
  set Γ := christoffelOf g.coefficient x
  set G := (g.coefficient x)⁻¹
  have hprod (c e p q : Fin (d + 1)) :
      fderiv ℝ (fun z => A z c p * B z e q) x (Pi.single m 1) =
        fderiv ℝ (fun z => A z c p) x (Pi.single m 1) * B x e q +
          A x c p * fderiv ℝ (fun z => B z e q) x (Pi.single m 1) := by
    rw [fderiv_fun_mul (hA c p) (hB e q)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hcovN (c e : Fin (d + 1)) : g.covDerivTwo N x m c e = ∑ p, ∑ q, G p q *
      (g.covDerivTwo A x m c p * B x e q + A x c p * g.covDerivTwo B x m e q) := by
    have h1 : g.covDerivTwo N x m c e = fderiv ℝ (fun z => N z c e) x (Pi.single m 1) -
        ∑ b, (Γ b m c * N x b e + Γ b m e * N x c b) := rfl
    have h2 (p q : Fin (d + 1)) :
        g.covDerivTwo (fun z => Matrix.of fun p q => A z c p * B z e q) x m p q =
          fderiv ℝ (fun z => A z c p) x (Pi.single m 1) * B x e q +
            A x c p * fderiv ℝ (fun z => B z e q) x (Pi.single m 1) -
            ∑ b, (Γ b m p * A x c b * B x e q + Γ b m q * A x c p * B x e b) := by
      unfold covDerivTwo
      simp only [Matrix.of_apply, hprod]
      congr 1
      exact Finset.sum_congr rfl fun b _ => by ring
    have hNx (b e' : Fin (d + 1)) : N x b e' = ∑ p, ∑ q, G p q * (A x b p * B x e' q) := rfl
    rw [h1, hdN]
    simp only [h2, hNx]
    have t1 : ∑ b, Γ b m c * ∑ p, ∑ q, G p q * (A x b p * B x e q) =
        ∑ p, ∑ q, G p q * ∑ b, Γ b m c * A x b p * B x e q := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun b _ => by ring
    have t2 : ∑ b, Γ b m e * ∑ p, ∑ q, G p q * (A x c p * B x b q) =
        ∑ p, ∑ q, G p q * ∑ b, Γ b m e * A x c p * B x b q := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun b _ => by ring
    rw [Finset.sum_add_distrib, t1, t2, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold covDerivTwo
    simp only [mul_sub, sub_mul, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
      Finset.sum_add_distrib]
    simp only [mul_assoc, mul_comm, mul_left_comm]
    ring
  simp only [hcovN]
  unfold tensorPairing covDerivMatrix
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Matrix.of_apply]
  ring

/-! ### Products -/

/-- The Leibniz rule for a product of covectors: `∇_m (u_i v_j) = ∇_m u_i v_j + u_i ∇_m v_j`. -/
theorem covDerivTwo_mul {u v : MinkowskiModel d → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hu : ∀ i, DifferentiableAt ℝ (fun z => u z i) x)
    (hv : ∀ i, DifferentiableAt ℝ (fun z => v z i) x) (m i j : Fin (d + 1)) :
    g.covDerivTwo (fun z => Matrix.of fun i j => u z i * v z j) x m i j =
      g.covDerivOne u x m i * v x j + u x i * g.covDerivOne v x m j := by
  unfold covDerivTwo covDerivOne
  simp only [Matrix.of_apply]
  rw [fderiv_fun_mul (hu i) (hv j)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  simp only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  ring

/-- The Leibniz rule `∇_m (f w)_i = ∂_m f w_i + f ∇_m w_i`. -/
theorem covDerivOne_smul {f : MinkowskiModel d → ℝ} {w : MinkowskiModel d → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hf : DifferentiableAt ℝ f x)
    (hw : ∀ i, DifferentiableAt ℝ (fun z => w z i) x) (m i : Fin (d + 1)) :
    g.covDerivOne (fun z => f z • w z) x m i =
      gradientCovector f x m * w x i + f x * g.covDerivOne w x m i := by
  unfold covDerivOne gradientCovector
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [fderiv_fun_mul hf (hw i)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, mul_sub, Finset.mul_sum]
  simp only [mul_assoc, mul_comm]
  ring

/-- **The Leibniz rule for a contraction** `(w·A)_j = (g^{ml} w_l) A_{mj}`:
`∇_c (w·A)_j = (g^{ml} ∇_c w_l) A_{mj} + (g^{ml} w_l) ∇_c A_{mj}`. -/
theorem covDerivOne_raise_contract {w : MinkowskiModel d → Fin (d + 1) → ℝ}
    {A : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U) (hw : ∀ i, DifferentiableAt ℝ (fun z => w z i) x)
    (hA : ∀ p q, DifferentiableAt ℝ (fun z => A z p q) x) (c j : Fin (d + 1)) :
    g.covDerivOne (fun z j => ∑ m, (∑ l, (g.coefficient z)⁻¹ m l * w z l) * A z m j) x c j =
      ∑ m, (∑ l, (g.coefficient x)⁻¹ m l * g.covDerivOne w x c l) * A x m j +
        ∑ m, (∑ l, (g.coefficient x)⁻¹ m l * w x l) * g.covDerivTwo A x c m j := by
  have hK (m : Fin (d + 1)) :
      DifferentiableAt ℝ (fun z => ∑ l, (g.coefficient z)⁻¹ m l * w z l) x :=
    DifferentiableAt.fun_sum fun l _ => (differentiableAt_coefficient_inv hx m l).fun_mul (hw l)
  have hd : fderiv ℝ (fun z => ∑ m, (∑ l, (g.coefficient z)⁻¹ m l * w z l) * A z m j) x
      (Pi.single c 1) = ∑ m, ((-∑ b, christoffelOf g.coefficient x m c b *
        ∑ l, (g.coefficient x)⁻¹ b l * w x l + ∑ l, (g.coefficient x)⁻¹ m l *
          g.covDerivOne w x c l) * A x m j + (∑ l, (g.coefficient x)⁻¹ m l * w x l) *
          fderiv ℝ (fun z => A z m j) x (Pi.single c 1)) := by
    rw [fderiv_sum_mul _ (fun m _ => hK m) (fun m _ => hA m j)]
    simp only [fderiv_raise hx hw]
  have hcd : g.covDerivOne (fun z j => ∑ m, (∑ l, (g.coefficient z)⁻¹ m l * w z l) * A z m j) x
      c j = fderiv ℝ (fun z => ∑ m, (∑ l, (g.coefficient z)⁻¹ m l * w z l) * A z m j) x
        (Pi.single c 1) - ∑ b, christoffelOf g.coefficient x b c j *
          ∑ m, (∑ l, (g.coefficient x)⁻¹ m l * w x l) * A x m b := rfl
  rw [hcd, hd]
  unfold covDerivOne
  set Γ := christoffelOf g.coefficient x
  set G := (g.coefficient x)⁻¹
  set K : Fin (d + 1) → ℝ := fun m => ∑ l, G m l * w x l
  have hKe (m : Fin (d + 1)) : ∑ l, G m l * w x l = K m := rfl
  simp only [hKe]
  unfold covDerivTwo
  have t1 : ∑ m, (∑ b, Γ m c b * K b) * A x m j = ∑ m, K m * ∑ b, Γ b c m * A x b j := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun b _ => by ring
  have t2 : ∑ b, Γ b c j * ∑ m, K m * A x m b = ∑ m, K m * ∑ b, Γ b c j * A x m b := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun b _ => by ring
  simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, t1, t2]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- The covariant derivative of a gradient is symmetric: `∇_i ∂_j ψ = ∇_j ∂_i ψ`. -/
theorem covDerivOne_gradient_symm {ψ : MinkowskiModel d → ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U) (hψ : ContDiffAt ℝ 2 ψ x) (i j : Fin (d + 1)) :
    g.covDerivOne (gradientCovector ψ) x i j = g.covDerivOne (gradientCovector ψ) x j i := by
  unfold covDerivOne
  have h : fderiv ℝ (fun z => gradientCovector ψ z j) x (Pi.single i 1) =
      fderiv ℝ (fun z => gradientCovector ψ z i) x (Pi.single j 1) :=
    secondPartial_comm hψ i j
  rw [h]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by rw [g.christoffelOf_coefficient_symm hx b i j]

/-- **The derivative of the norm of a gradient**: `∂_m g(dψ, dψ) = 2 k^a ∇_m ∂_a ψ` with
`k = (dψ)^♯` (`gradientField`). -/
theorem gradientCovector_gradientNorm {ψ : MinkowskiModel d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U)
    {x : MinkowskiModel d} (hx : x ∈ U) (m : Fin (d + 1)) :
    gradientCovector (g.gradientNorm ψ) x m =
      2 * ∑ a, g.gradientField ψ x a * g.covDerivOne (gradientCovector ψ) x m a := by
  have hk (i : Fin (d + 1)) : DifferentiableAt ℝ (fun z => gradientCovector ψ z i) x :=
    differentiableAt_of_contDiffOn (contDiffOn_gradientCovector hψ i) hx
  have hfun : g.gradientNorm ψ = fun z => ∑ i, ∑ j, (g.coefficient z)⁻¹ i j *
      (Matrix.of fun i j => gradientCovector ψ z i * gradientCovector ψ z j :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) i j := by
    funext z
    unfold gradientNorm
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp only [Matrix.of_apply]; ring
  change fderiv ℝ (g.gradientNorm ψ) x (Pi.single m 1) = _
  rw [hfun, fderiv_trace (T := fun z => Matrix.of fun i j => gradientCovector ψ z i *
    gradientCovector ψ z j) hx (fun p q => (hk p).fun_mul (hk q))]
  simp only [covDerivTwo_mul hk hk]
  set G := (g.coefficient x)⁻¹
  set H := g.covDerivOne (gradientCovector ψ) x
  set K := g.gradientField ψ x
  have hG (a b : Fin (d + 1)) : G a b = G b a := g.coefficient_inv_symmetric hx a b
  have hK (a : Fin (d + 1)) : K a = ∑ j, G a j * gradientCovector ψ x j := rfl
  have a1 : ∑ i, ∑ j, G i j * (H m i * gradientCovector ψ x j) = ∑ a, K a * H m a := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hK, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have a2 : ∑ i, ∑ j, G i j * (gradientCovector ψ x i * H m j) = ∑ a, K a * H m a := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hK, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hG i j]; ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [a1, a2]
  ring

/-! ### Symmetry and locality -/

/-- The covariant derivative of a field of symmetric matrices is symmetric in the last two
indices. -/
theorem covDerivTwo_symm {A : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hA : ∀ z ∈ U, ∀ i j, A z i j = A z j i) {x : MinkowskiModel d} (hx : x ∈ U)
    (m p q : Fin (d + 1)) : g.covDerivTwo A x m p q = g.covDerivTwo A x m q p := by
  have hd : fderiv ℝ (fun z => A z p q) x = fderiv ℝ (fun z => A z q p) x :=
    Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (U.isOpen.mem_nhds hx)
      fun z hz => hA z hz p q)
  unfold covDerivTwo
  rw [hd]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by rw [hA x hx b q, hA x hx p b]; ring

theorem covDerivOne_congr {w w' : MinkowskiModel d → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hw : w =ᶠ[𝓝 x] w') (a i : Fin (d + 1)) : g.covDerivOne w x a i = g.covDerivOne w' x a i := by
  have hd : fderiv ℝ (fun z => w z i) x = fderiv ℝ (fun z => w' z i) x :=
    Filter.EventuallyEq.fderiv_eq (hw.mono fun z hz => congrFun hz i)
  unfold covDerivOne
  rw [hd, hw.eq_of_nhds]

end ProjectAinos.SmoothGeometry.CoordinateMetric
