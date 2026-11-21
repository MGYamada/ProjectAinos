/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateCurvature
public import ProjectAinos.GeneralRelativity.NewtonianBounds
import Mathlib.Tactic

/-! # The Ricci tensor of the post-Newtonian metric family

Landau–Lifshitz, §106, the field equations of the second approximation, in the coordinates
`(t, x)` of `NewtonianCoordinates` with `ε = c⁻²`.

* `ricciOf_eq_ricciJet`: for coefficients `C²` at `y` and invertible near `y`, the coordinate
  Ricci tensor is the polynomial `ricciJet` in `C(y)⁻¹`, `∂C(y)` and `∂²C(y)`
  (`hasFDerivAt_inv_apply`: `∂C⁻¹ = −C⁻¹ ∂C C⁻¹`).
* `pnCoefficient`: the family `g_tt = −c² − 2Φ − 2(Φ² + ψ)/c²`, `g_ti = B_i/c²`,
  `g_ij = (1 − 2Φ/c²)δ_ij` of arbitrary potentials; `pnInverse` and
  `pnCoefficient_mul_inverse`: the exact inverse (Schur complement); `jet1_pnCoefficient`,
  `jet2_pnCoefficient`: its jets (`sd`: second partials in increasing order, by the symmetry of
  second derivatives); `ricciOf_pnCoefficient`: its Ricci tensor is `ricciJet` of these.
* `IsExp`: first-order expansions `f = f₀ + εf₁ + O(ε²)` uniformly on a set, closed under sums and
  products (the macro `exp_on`); `exp_inverse`, `exp_jet1`, `exp_jet2` and the components
  `exp_ricci_tt`, `exp_ricci_ti`, `exp_ricci_it`, `exp_ricci_ij`.
* `abs_ricciOf_pnCoefficient_sub_le`: **the Ricci tensor of the family to the order `c⁻²`**: for
  potentials `C²` on an open set `W` with values and two derivatives bounded by `K`
  (`PotentialBounds`), `|R_jk − R⁽⁰⁾_jk − c⁻²R⁽¹⁾_jk| ≤ C/c⁴` on `W` for `c ≥ 8(K² + K + 1) + 1`,
  with `R_tt = ΔΦ + c⁻²(4ΦΔΦ + Δψ + ∂_t(3∂_tΦ + ∇ · B))`, `R_tα = −(ΔB_α − ∂_α∇ · B −
  4∂_t∂_αΦ)/2c²`, `R_αβ = ΔΦ δ_αβ/c²` (`ricciLeading`, `ricciFirst`). The sizes are `R_tt = O(1)`,
  `R_tα = R_αβ = O(c⁻²)`; in `x⁰ = ct` the errors are `O(c⁻⁶)`, `O(c⁻⁵)`, `O(c⁻⁴)`.
* Instance: `potentialBounds_zero`.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.PostNewtonianRicci

open SmoothGeometry SmoothGeometry.CoordinateMetric NewtonianMetricFamily

/-! ### The Ricci tensor from the two-jet of the coefficients -/

section Jet

variable {d : ℕ}

/-- The first derivatives `∂_m C_{ab}` of the coefficients at `y`. -/
def jet1 (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d)
    (m a b : Fin (d + 1)) : ℝ :=
  fderiv ℝ (fun z => C z a b) y (Pi.single m 1)

/-- The second derivatives `∂_m ∂_n C_{ab}` of the coefficients at `y`. -/
def jet2 (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d)
    (m n a b : Fin (d + 1)) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ (fun w => C w a b) z (Pi.single n 1)) y (Pi.single m 1)

/-- The Christoffel symbols of the first kind `Γ_{l,ij} = ½(∂_i C_{jl} + ∂_j C_{li} − ∂_l C_{ij})`
of an array `D m a b = ∂_m C_{ab}`. -/
def lowerJet (D : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ) (i j l : Fin (d + 1)) : ℝ :=
  (D i j l + D j l i - D l i j) / 2

/-- The Christoffel symbols `Γ^k_{ij} = M^{kl} Γ_{l,ij}` from an inverse `M` and a first jet. -/
def gamJet (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (D : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ) (k i j : Fin (d + 1)) : ℝ :=
  ∑ l, M k l * lowerJet D i j l

/-- The derivative `∂_m Γ^k_{ij}` from the inverse `M`, the first jet `D` and the second jet `D₂`,
with `∂_m M^{kl} = −M^{kp} ∂_m C_{pq} M^{ql}`. -/
def dGamJet (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (D : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (D₂ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ) (m k i j : Fin (d + 1)) :
    ℝ :=
  ∑ l, ((-∑ p, ∑ q, M k p * D m p q * M q l) * lowerJet D i j l + M k l * lowerJet (D₂ m) i j l)

/-- The Ricci tensor `R_{jk} = ∂_i Γ^i_{jk} − ∂_j Γ^i_{ik} + Γ^i_{ia} Γ^a_{jk} − Γ^i_{ja} Γ^a_{ik}`
as a polynomial in the inverse and the two-jet. -/
def ricciJet (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (D : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (D₂ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ) (j k : Fin (d + 1)) : ℝ :=
  ∑ i, (dGamJet M D D₂ i i j k - dGamJet M D D₂ j i i k +
    ∑ a, (gamJet M D i i a * gamJet M D a j k - gamJet M D i j a * gamJet M D a i k))

variable {C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {y : MinkowskiModel d}

theorem christoffelOf_eq_gamJet (z : MinkowskiModel d) (k i j : Fin (d + 1)) :
    christoffelOf C z k i j = gamJet (C z)⁻¹ (jet1 C z) k i j := by
  simp only [christoffelOf, gamJet, lowerJet, jet1, mul_div_assoc]

/-- The derivative of the entries of the inverse, `∂_m C^{kl} = −C^{kp} ∂_m C_{pq} C^{ql}`. -/
theorem hasFDerivAt_inv_apply (hC : ∀ a b, DifferentiableAt ℝ (fun z => C z a b) y)
    (hdet : ∀ᶠ z in 𝓝 y, (C z).det ≠ 0) (k l : Fin (d + 1)) :
    DifferentiableAt ℝ (fun z => (C z)⁻¹ k l) y ∧
      fderiv ℝ (fun z => (C z)⁻¹ k l) y = -∑ p, ∑ q, (C y)⁻¹ k p • (C y)⁻¹ q l •
        fderiv ℝ (fun z => C z p q) y := by
  have hdC : DifferentiableAt ℝ (fun z => (fun a b => C z a b : Fin (d + 1) → Fin (d + 1) → ℝ)) y :=
    differentiableAt_pi.mpr fun a => differentiableAt_pi.mpr fun b => hC a b
  have hinv (k l : Fin (d + 1)) : DifferentiableAt ℝ (fun z => (C z)⁻¹ k l) y := by
    have h := (contDiffAt_matrix_inv_apply (A := fun a b => C y a b) hdet.self_of_nhds k l
      ).differentiableAt (by simp)
    exact h.comp y hdC
  refine ⟨hinv k l, ?_⟩
  -- differentiate `Σ_m C_{pm} C^{ml} = δ_{pl}`
  have hid (p : Fin (d + 1)) : fderiv ℝ (fun z => ∑ m, C z p m * (C z)⁻¹ m l) y = 0 := by
    have hev : (fun z => ∑ m, C z p m * (C z)⁻¹ m l) =ᶠ[𝓝 y] fun _ =>
        (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) p l := by
      filter_upwards [hdet] with z hz
      have h := Matrix.mul_nonsing_inv (C z) (isUnit_iff_ne_zero.mpr hz)
      simpa [Matrix.mul_apply] using congrFun (congrFun h p) l
    rw [hev.fderiv_eq]
    simp
  have hprod (p : Fin (d + 1)) : fderiv ℝ (fun z => ∑ m, C z p m * (C z)⁻¹ m l) y =
      ∑ m, (C y p m • fderiv ℝ (fun z => (C z)⁻¹ m l) y +
        (C y)⁻¹ m l • fderiv ℝ (fun z => C z p m) y) := by
    have h : HasFDerivAt (fun z => ∑ m, C z p m * (C z)⁻¹ m l)
        (∑ m, (C y p m • fderiv ℝ (fun z => (C z)⁻¹ m l) y +
          (C y)⁻¹ m l • fderiv ℝ (fun z => C z p m) y)) y :=
      HasFDerivAt.fun_sum fun m _ => (hC p m).hasFDerivAt.mul (hinv m l).hasFDerivAt
    exact h.fderiv
  have hkey : ∑ p, (C y)⁻¹ k p • fderiv ℝ (fun z => ∑ m, C z p m * (C z)⁻¹ m l) y = 0 := by
    simp [hid]
  rw [Finset.sum_congr rfl fun p _ => by rw [hprod p]] at hkey
  simp only [smul_add, Finset.smul_sum, Finset.sum_add_distrib, smul_smul] at hkey
  have hC1 : ∑ p, ∑ m, ((C y)⁻¹ k p * C y p m) • fderiv ℝ (fun z => (C z)⁻¹ m l) y =
      fderiv ℝ (fun z => (C z)⁻¹ k l) y := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have h := Matrix.nonsing_inv_mul (C y) (isUnit_iff_ne_zero.mpr hdet.self_of_nhds)
    have hm (m : Fin (d + 1)) : ∑ p, (C y)⁻¹ k p * C y p m =
        (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) k m := by
      simpa [Matrix.mul_apply] using congrFun (congrFun h k) m
    simp only [hm, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
  rw [hC1] at hkey
  rw [eq_neg_of_add_eq_zero_left hkey]
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [smul_smul]

/-- **The Ricci tensor from the two-jet.** If the coefficients are `C²` at `y` and invertible
near `y`, then `ricciOf C y = ricciJet (C y)⁻¹ ∂C ∂²C` at `y`. -/
theorem ricciOf_eq_ricciJet (hC : ∀ a b, ContDiffAt ℝ 2 (fun z => C z a b) y)
    (hdet : ∀ᶠ z in 𝓝 y, (C z).det ≠ 0) (j k : Fin (d + 1)) :
    ricciOf C y j k = ricciJet (C y)⁻¹ (jet1 C y) (jet2 C y) j k := by
  have hC1 (a b : Fin (d + 1)) : DifferentiableAt ℝ (fun z => C z a b) y :=
    (hC a b).differentiableAt (by norm_num)
  have hD (n a b : Fin (d + 1)) :
      DifferentiableAt ℝ (fun z => fderiv ℝ (fun w => C w a b) z (Pi.single n 1)) y :=
    (((hC a b).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const _)
  have hΓ (m k i j : Fin (d + 1)) :
      fderiv ℝ (fun z => christoffelOf C z k i j) y (Pi.single m 1) =
        dGamJet (C y)⁻¹ (jet1 C y) (jet2 C y) m k i j := by
    have hinv (l : Fin (d + 1)) := hasFDerivAt_inv_apply hC1 hdet k l
    have hL (l : Fin (d + 1)) : HasFDerivAt (fun z => lowerJet (jet1 C z) i j l)
        ((1 / 2 : ℝ) • (fderiv ℝ (fun z => jet1 C z i j l) y +
          fderiv ℝ (fun z => jet1 C z j l i) y - fderiv ℝ (fun z => jet1 C z l i j) y)) y := by
      have h := ((((hD i j l).hasFDerivAt.add (hD j l i).hasFDerivAt).sub
        (hD l i j).hasFDerivAt).const_mul (1 / 2 : ℝ))
      refine h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
      simp only [lowerJet, jet1, Pi.add_apply, Pi.sub_apply]
      ring
    have hS : HasFDerivAt (fun z => ∑ l, (C z)⁻¹ k l * lowerJet (jet1 C z) i j l)
        (∑ l, ((C y)⁻¹ k l • (1 / 2 : ℝ) • (fderiv ℝ (fun z => jet1 C z i j l) y +
          fderiv ℝ (fun z => jet1 C z j l i) y - fderiv ℝ (fun z => jet1 C z l i j) y) +
          lowerJet (jet1 C y) i j l • fderiv ℝ (fun z => (C z)⁻¹ k l) y)) y :=
      HasFDerivAt.fun_sum fun l _ => (hinv l).1.hasFDerivAt.mul (hL l)
    have hfun : (fun z => christoffelOf C z k i j) =
        fun z => ∑ l, (C z)⁻¹ k l * lowerJet (jet1 C z) i j l :=
      funext fun z => christoffelOf_eq_gamJet z k i j
    rw [hfun, hS.fderiv]
    simp only [FunLike.coe_sum, Finset.sum_apply, dGamJet]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [(hinv l).2]
    simp only [add_apply, smul_apply, neg_apply, FunLike.coe_sum, Finset.sum_apply,
      sub_apply, smul_eq_mul, lowerJet, jet1, jet2]
    have e : ∑ x, ∑ x_1, (C y)⁻¹ k x * ((C y)⁻¹ x_1 l *
        fderiv ℝ (fun z => C z x x_1) y (Pi.single m 1)) = ∑ p, ∑ q, (C y)⁻¹ k p *
          fderiv ℝ (fun z => C z p q) y (Pi.single m 1) * (C y)⁻¹ q l :=
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    simp only [e]
    ring
  unfold ricciOf ricciJet
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hΓ, hΓ]
  simp only [christoffelOf_eq_gamJet]

end Jet

/-! ### The post-Newtonian coefficients -/

local notation "E" => NewtonianCoordinates
local notation "S" => NewtonianSpace

/-- The partial derivative `∂_m g`. -/
def pd (g : E → ℝ) (q : E) (m : Fin 4) : ℝ := fderiv ℝ g q (Pi.single m 1)

/-- The second partial derivative `∂_m ∂_n g`. -/
def pd2 (g : E → ℝ) (q : E) (m n : Fin 4) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ g z (Pi.single n 1)) q (Pi.single m 1)

/-- The second partial derivative with the indices in increasing order. -/
def sd (g : E → ℝ) (q : E) (m n : Fin 4) : ℝ := if m ≤ n then pd2 g q m n else pd2 g q n m

theorem pd2_eq_fderiv_fderiv {g : E → ℝ} {q : E} (hg : ContDiffAt ℝ 2 g q) (m n : Fin 4) :
    pd2 g q m n = fderiv ℝ (fderiv ℝ g) q (Pi.single m 1) (Pi.single n 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) q :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [pd2, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem pd2_comm {g : E → ℝ} {q : E} (hg : ContDiffAt ℝ 2 g q) (m n : Fin 4) :
    pd2 g q m n = pd2 g q n m := by
  rw [pd2_eq_fderiv_fderiv hg, pd2_eq_fderiv_fderiv hg]
  exact (hg.isSymmSndFDerivAt (by simp)) _ _

theorem pd2_eq_sd {g : E → ℝ} {q : E} (hg : ContDiffAt ℝ 2 g q) (m n : Fin 4) :
    pd2 g q m n = sd g q m n := by
  unfold sd
  split_ifs
  · rfl
  · exact pd2_comm hg m n

/-- The spatial factor `s = 1 − 2Φ/c²`. -/
def spatialFactor (Φ : E → ℝ) (c : ℝ) (q : E) : ℝ := 1 - 2 * epsilon c * Φ q

/-- **The post-Newtonian metric family** of the potentials `Φ`, `ψ`, `B`:
`g_tt = −c² − 2Φ − 2(Φ² + ψ)/c²`, `g_ti = B_i/c²`, `g_ij = (1 − 2Φ/c²) δ_ij`. -/
def pnCoefficient (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-c ^ 2 - 2 * Φ q - 2 * epsilon c * (Φ q ^ 2 + ψ q), epsilon c * B q 0,
      epsilon c * B q 1, epsilon c * B q 2;
    epsilon c * B q 0, spatialFactor Φ c q, 0, 0;
    epsilon c * B q 1, 0, spatialFactor Φ c q, 0;
    epsilon c * B q 2, 0, 0, spatialFactor Φ c q]

/-- The denominator `D = s (1 + 2εΦ + 2ε²(Φ² + ψ)) + ε³ |B|²` of the inverse. -/
def pnDenom (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) : ℝ :=
  spatialFactor Φ c q * (1 + 2 * epsilon c * Φ q + 2 * epsilon c ^ 2 * (Φ q ^ 2 + ψ q)) +
    epsilon c ^ 3 * (B q 0 ^ 2 + B q 1 ^ 2 + B q 2 ^ 2)

/-- The spatial block `δ_ij/s − ε³B_iB_j/(sD)` of the inverse. -/
def pnSpatialInverse (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (i j : Fin 3) : ℝ :=
  (if i = j then 1 else 0) * (spatialFactor Φ c q)⁻¹ -
    epsilon c ^ 3 * B q i * B q j * (spatialFactor Φ c q)⁻¹ * (pnDenom Φ ψ B c q)⁻¹

/-- **The inverse of the post-Newtonian coefficients**, by the Schur complement:
`g^{tt} = −εs/D`, `g^{ti} = ε²B_i/D`, `g^{ij} = δ_ij/s − ε³B_iB_j/(sD)`. -/
def pnInverse (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-epsilon c * spatialFactor Φ c q * (pnDenom Φ ψ B c q)⁻¹,
      epsilon c ^ 2 * B q 0 * (pnDenom Φ ψ B c q)⁻¹,
      epsilon c ^ 2 * B q 1 * (pnDenom Φ ψ B c q)⁻¹,
      epsilon c ^ 2 * B q 2 * (pnDenom Φ ψ B c q)⁻¹;
    epsilon c ^ 2 * B q 0 * (pnDenom Φ ψ B c q)⁻¹, pnSpatialInverse Φ ψ B c q 0 0,
      pnSpatialInverse Φ ψ B c q 0 1, pnSpatialInverse Φ ψ B c q 0 2;
    epsilon c ^ 2 * B q 1 * (pnDenom Φ ψ B c q)⁻¹, pnSpatialInverse Φ ψ B c q 1 0,
      pnSpatialInverse Φ ψ B c q 1 1, pnSpatialInverse Φ ψ B c q 1 2;
    epsilon c ^ 2 * B q 2 * (pnDenom Φ ψ B c q)⁻¹, pnSpatialInverse Φ ψ B c q 2 0,
      pnSpatialInverse Φ ψ B c q 2 1, pnSpatialInverse Φ ψ B c q 2 2]

theorem pnCoefficient_mul_inverse {Φ ψ : E → ℝ} {B : E → S} {c : ℝ} (hc : c ≠ 0) {q : E}
    (hs : spatialFactor Φ c q ≠ 0) (hD : pnDenom Φ ψ B c q ≠ 0) :
    pnCoefficient Φ ψ B c q * pnInverse Φ ψ B c q = 1 := by
  have he : epsilon c ≠ 0 := inv_ne_zero (pow_ne_zero 2 hc)
  have hc2 : c ^ 2 = (epsilon c)⁻¹ := by simp [epsilon]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, pnCoefficient, pnInverse, pnSpatialInverse, hc2] <;>
    field_simp <;> simp only [pnDenom, spatialFactor] <;> ring

/-- The component `B_j` of the vector potential as a function. -/
def comp (B : E → S) (j : Fin 3) : E → ℝ := fun z => B z j

theorem comp_eq (B : E → S) (j : Fin 3) : comp B j = fun z => B z j := rfl

/-- The first jet `∂_m g_{ab}` of the post-Newtonian coefficients. -/
def pnJet1 (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (m : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-2 * pd Φ q m - 2 * epsilon c * (2 * Φ q * pd Φ q m + pd ψ q m),
      epsilon c * pd (comp B 0) q m, epsilon c * pd (comp B 1) q m, epsilon c * pd (comp B 2) q m;
    epsilon c * pd (comp B 0) q m, -2 * epsilon c * pd Φ q m, 0, 0;
    epsilon c * pd (comp B 1) q m, 0, -2 * epsilon c * pd Φ q m, 0;
    epsilon c * pd (comp B 2) q m, 0, 0, -2 * epsilon c * pd Φ q m]

/-- The second jet `∂_m ∂_n g_{ab}` of the post-Newtonian coefficients. -/
def pnJet2 (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (m n : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![-2 * sd Φ q m n - 2 * epsilon c * (2 * (pd Φ q m * pd Φ q n + Φ q * sd Φ q m n) +
        sd ψ q m n),
      epsilon c * sd (comp B 0) q m n, epsilon c * sd (comp B 1) q m n,
      epsilon c * sd (comp B 2) q m n;
    epsilon c * sd (comp B 0) q m n, -2 * epsilon c * sd Φ q m n, 0, 0;
    epsilon c * sd (comp B 1) q m n, 0, -2 * epsilon c * sd Φ q m n, 0;
    epsilon c * sd (comp B 2) q m n, 0, 0, -2 * epsilon c * sd Φ q m n]

section Jets

variable {Φ ψ : E → ℝ} {B : E → S} {q : E}

theorem jet1_pnCoefficient (c : ℝ) (hΦ : DifferentiableAt ℝ Φ q) (hψ : DifferentiableAt ℝ ψ q)
    (hB : ∀ j, DifferentiableAt ℝ (comp B j) q) (m a b : Fin 4) :
    jet1 (d := 3) (pnCoefficient Φ ψ B c) q m a b = pnJet1 Φ ψ B c q m a b := by
  have hB0 : DifferentiableAt ℝ (fun z => B z 0) q := hB 0
  have hB1 : DifferentiableAt ℝ (fun z => B z 1) q := hB 1
  have hB2 : DifferentiableAt ℝ (fun z => B z 2) q := hB 2
  fin_cases a <;> fin_cases b <;>
    simp (disch := fun_prop) [jet1, pnCoefficient, pnJet1, spatialFactor, pd, comp_eq,
      fderiv_fun_sub, fderiv_fun_add, fderiv_const_mul, fderiv_fun_pow]
  all_goals ring

theorem jet2_pnCoefficient (c : ℝ) {W : Set E} (hW : IsOpen W) (hq : q ∈ W)
    (hΦ : ∀ z ∈ W, ContDiffAt ℝ 2 Φ z) (hψ : ∀ z ∈ W, ContDiffAt ℝ 2 ψ z)
    (hB : ∀ z ∈ W, ∀ j, ContDiffAt ℝ 2 (comp B j) z) (m n a b : Fin 4) :
    jet2 (d := 3) (pnCoefficient Φ ψ B c) q m n a b = pnJet2 Φ ψ B c q m n a b := by
  have hev : (fun z => fderiv ℝ (fun w => pnCoefficient Φ ψ B c w a b) z (Pi.single n 1)) =ᶠ[𝓝 q]
      fun z => pnJet1 Φ ψ B c z n a b := by
    filter_upwards [hW.mem_nhds hq] with z hz
    exact jet1_pnCoefficient c ((hΦ z hz).differentiableAt (by norm_num))
      ((hψ z hz).differentiableAt (by norm_num))
      (fun j => (hB z hz j).differentiableAt (by norm_num)) n a b
  have hd (g : E → ℝ) (hg : ContDiffAt ℝ 2 g q) :
      DifferentiableAt ℝ (fun z => fderiv ℝ g z (Pi.single n 1)) q :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const _)
  have hΦ1 := (hΦ q hq).differentiableAt (by norm_num)
  have hΦ2 := hd Φ (hΦ q hq)
  have hψ2 := hd ψ (hψ q hq)
  have hB0 : DifferentiableAt ℝ (fun z => fderiv ℝ (fun w => B w 0) z (Pi.single n 1)) q :=
    hd _ (hB q hq 0)
  have hB1 : DifferentiableAt ℝ (fun z => fderiv ℝ (fun w => B w 1) z (Pi.single n 1)) q :=
    hd _ (hB q hq 1)
  have hB2 : DifferentiableAt ℝ (fun z => fderiv ℝ (fun w => B w 2) z (Pi.single n 1)) q :=
    hd _ (hB q hq 2)
  have hsΦ := pd2_eq_sd (hΦ q hq) m n
  have hsψ := pd2_eq_sd (hψ q hq) m n
  have hs0 := pd2_eq_sd (hB q hq 0) m n
  have hs1 := pd2_eq_sd (hB q hq 1) m n
  have hs2 := pd2_eq_sd (hB q hq 2) m n
  simp only [pd2, comp_eq] at hsΦ hsψ hs0 hs1 hs2
  rw [jet2, hev.fderiv_eq]
  fin_cases a <;> fin_cases b <;>
    simp (disch := fun_prop) [pnJet1, pnJet2, pd, comp_eq, fderiv_fun_sub, fderiv_fun_add,
      fderiv_const_mul, fderiv_fun_mul, ← hsΦ, ← hsψ, ← hs0, ← hs1, ← hs2]
  all_goals ring

end Jets

/-! ### Expansions to first order with a uniform remainder -/

/-- A real function bounded on a set. -/
def BoundedOn {α : Type} (T : Set α) (F : α → ℝ) : Prop :=
  ∃ C, 0 ≤ C ∧ ∀ x ∈ T, |F x| ≤ C

/-- `f = f₀ + ε f₁ + O(ε²)` uniformly on `T`, with bounded coefficients and `0 ≤ ε ≤ 1`. -/
structure IsExp {α : Type} (T : Set α) (ε f f₀ f₁ : α → ℝ) : Prop where
  eps : ∀ p ∈ T, 0 ≤ ε p ∧ ε p ≤ 1
  b0 : BoundedOn T f₀
  b1 : BoundedOn T f₁
  rem : ∃ C, 0 ≤ C ∧ ∀ p ∈ T, |f p - (f₀ p + ε p * f₁ p)| ≤ C * ε p ^ 2

section IsExp

variable {α : Type} {T : Set α} {ε f g f₀ f₁ g₀ g₁ : α → ℝ}

theorem BoundedOn.add' (hf : BoundedOn T f) (hg : BoundedOn T g) :
    BoundedOn T (fun x => f x + g x) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  exact ⟨C + D, by positivity, fun x hx => (abs_add_le _ _).trans (add_le_add (hf x hx) (hg x hx))⟩

theorem BoundedOn.mul' (hf : BoundedOn T f) (hg : BoundedOn T g) :
    BoundedOn T (fun x => f x * g x) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C * D, by positivity, fun x hx => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hf x hx) (hg x hx) (abs_nonneg _) hC

theorem BoundedOn.neg' (hf : BoundedOn T f) : BoundedOn T (fun x => -f x) := by
  obtain ⟨C, hC, hf⟩ := hf
  exact ⟨C, hC, fun x hx => by rw [abs_neg]; exact hf x hx⟩

theorem BoundedOn.const' (a : ℝ) : BoundedOn T (fun _ => a) :=
  ⟨|a|, abs_nonneg a, fun _ _ => le_rfl⟩

theorem BoundedOn.of_le' {C : ℝ} (h : ∀ x ∈ T, |f x| ≤ C) : BoundedOn T f :=
  ⟨max C 0, le_max_right _ _, fun x hx => (h x hx).trans (le_max_left _ _)⟩

theorem BoundedOn.sum' {ι : Type} [Fintype ι] {K : ι → α → ℝ}
    (hK : ∀ i, BoundedOn T (K i)) : BoundedOn T (fun x => ∑ i, K i x) := by
  choose C hC hb using hK
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC i, fun x hx => ?_⟩
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hb i x hx)

theorem IsExp.bounded (h : IsExp T ε f f₀ f₁) : BoundedOn T f := by
  obtain ⟨C₀, hC₀, h₀⟩ := h.b0
  obtain ⟨C₁, hC₁, h₁⟩ := h.b1
  obtain ⟨C, hC, hr⟩ := h.rem
  refine ⟨C₀ + C₁ + C, by positivity, fun p hp => ?_⟩
  obtain ⟨he0, he1⟩ := h.eps p hp
  have h2 : ε p ^ 2 ≤ 1 := by nlinarith
  have h3 : |ε p * f₁ p| ≤ C₁ := by
    rw [abs_mul, abs_of_nonneg he0]
    exact (mul_le_of_le_one_left (abs_nonneg _) he1).trans (h₁ p hp)
  calc |f p| = |(f p - (f₀ p + ε p * f₁ p)) + f₀ p + ε p * f₁ p| := by ring_nf
    _ ≤ |f p - (f₀ p + ε p * f₁ p)| + |f₀ p| + |ε p * f₁ p| := by
        refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C * 1 + C₀ + C₁ := by
        gcongr
        · exact (hr p hp).trans (mul_le_mul_of_nonneg_left h2 hC)
        · exact h₀ p hp
    _ = C₀ + C₁ + C := by ring

theorem IsExp.const (hε : ∀ p ∈ T, 0 ≤ ε p ∧ ε p ≤ 1) (a : ℝ) :
    IsExp T ε (fun _ => a) (fun _ => a) (fun _ => 0) :=
  ⟨hε, BoundedOn.const' a, BoundedOn.const' 0, ⟨0, le_rfl, fun p _ => by simp⟩⟩

theorem IsExp.eps_self (hε : ∀ p ∈ T, 0 ≤ ε p ∧ ε p ≤ 1) :
    IsExp T ε (fun p => ε p) (fun _ => 0) (fun _ => 1) :=
  ⟨hε, BoundedOn.const' 0, BoundedOn.const' 1, ⟨0, le_rfl, fun p _ => by simp⟩⟩

theorem IsExp.of_eq {f₂ : α → ℝ} (hε : ∀ p ∈ T, 0 ≤ ε p ∧ ε p ≤ 1) (h₀ : BoundedOn T f₀)
    (h₁ : BoundedOn T f₁) (h₂ : BoundedOn T f₂)
    (h : ∀ p ∈ T, f p = f₀ p + ε p * f₁ p + ε p ^ 2 * f₂ p) : IsExp T ε f f₀ f₁ := by
  obtain ⟨C, hC, h₂⟩ := h₂
  refine ⟨hε, h₀, h₁, ⟨C, hC, fun p hp => ?_⟩⟩
  rw [h p hp, show f₀ p + ε p * f₁ p + ε p ^ 2 * f₂ p - (f₀ p + ε p * f₁ p) =
    ε p ^ 2 * f₂ p by ring, abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm]
  exact mul_le_mul_of_nonneg_right (h₂ p hp) (sq_nonneg _)

theorem IsExp.atom (hε : ∀ p ∈ T, 0 ≤ ε p ∧ ε p ≤ 1) (hf : BoundedOn T f) :
    IsExp T ε f f (fun _ => 0) :=
  IsExp.of_eq (f₂ := fun _ => 0) hε hf (BoundedOn.const' 0) (BoundedOn.const' 0)
    fun p _ => by ring

theorem IsExp.add (hf : IsExp T ε f f₀ f₁) (hg : IsExp T ε g g₀ g₁) :
    IsExp T ε (fun p => f p + g p) (fun p => f₀ p + g₀ p) (fun p => f₁ p + g₁ p) := by
  obtain ⟨C, hC, hf'⟩ := hf.rem
  obtain ⟨D, hD, hg'⟩ := hg.rem
  refine ⟨hf.eps, hf.b0.add' hg.b0, hf.b1.add' hg.b1, ⟨C + D, by positivity, fun p hp => ?_⟩⟩
  calc |f p + g p - (f₀ p + g₀ p + ε p * (f₁ p + g₁ p))| =
      |(f p - (f₀ p + ε p * f₁ p)) + (g p - (g₀ p + ε p * g₁ p))| := by ring_nf
    _ ≤ C * ε p ^ 2 + D * ε p ^ 2 := (abs_add_le _ _).trans (add_le_add (hf' p hp) (hg' p hp))
    _ = (C + D) * ε p ^ 2 := by ring

theorem IsExp.neg (hf : IsExp T ε f f₀ f₁) :
    IsExp T ε (fun p => -f p) (fun p => -f₀ p) (fun p => -f₁ p) := by
  obtain ⟨C, hC, hf'⟩ := hf.rem
  refine ⟨hf.eps, hf.b0.neg', hf.b1.neg', ⟨C, hC, fun p hp => ?_⟩⟩
  rw [show -f p - (-f₀ p + ε p * -f₁ p) = -(f p - (f₀ p + ε p * f₁ p)) by ring, abs_neg]
  exact hf' p hp

theorem IsExp.sub (hf : IsExp T ε f f₀ f₁) (hg : IsExp T ε g g₀ g₁) :
    IsExp T ε (fun p => f p - g p) (fun p => f₀ p - g₀ p) (fun p => f₁ p - g₁ p) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem IsExp.mul (hf : IsExp T ε f f₀ f₁) (hg : IsExp T ε g g₀ g₁) :
    IsExp T ε (fun p => f p * g p) (fun p => f₀ p * g₀ p)
      (fun p => f₀ p * g₁ p + f₁ p * g₀ p) := by
  obtain ⟨C, hC, hf'⟩ := hf.rem
  obtain ⟨D, hD, hg'⟩ := hg.rem
  obtain ⟨Bg, hBg, hbg⟩ := hg.bounded
  obtain ⟨B₀, hB₀, hb₀⟩ := hf.b0
  obtain ⟨B₁, hB₁, hb₁⟩ := hf.b1
  obtain ⟨G₁, hG₁, hg₁⟩ := hg.b1
  refine ⟨hf.eps, hf.b0.mul' hg.b0, (hf.b0.mul' hg.b1).add' (hf.b1.mul' hg.b0),
    ⟨C * Bg + (B₀ + B₁) * D + B₁ * G₁, by positivity, fun p hp => ?_⟩⟩
  obtain ⟨he0, he1⟩ := hf.eps p hp
  have e : f p * g p - (f₀ p * g₀ p + ε p * (f₀ p * g₁ p + f₁ p * g₀ p)) =
      (f p - (f₀ p + ε p * f₁ p)) * g p + (f₀ p + ε p * f₁ p) * (g p - (g₀ p + ε p * g₁ p)) +
        ε p ^ 2 * (f₁ p * g₁ p) := by ring
  have hF : |f₀ p + ε p * f₁ p| ≤ B₀ + B₁ := by
    refine (abs_add_le _ _).trans (add_le_add (hb₀ p hp) ?_)
    rw [abs_mul, abs_of_nonneg he0]
    exact (mul_le_of_le_one_left (abs_nonneg _) he1).trans (hb₁ p hp)
  have h1 : |(f p - (f₀ p + ε p * f₁ p)) * g p| ≤ C * Bg * ε p ^ 2 := by
    rw [abs_mul]
    calc |f p - (f₀ p + ε p * f₁ p)| * |g p| ≤ C * ε p ^ 2 * Bg :=
          mul_le_mul (hf' p hp) (hbg p hp) (abs_nonneg _) (by positivity)
      _ = C * Bg * ε p ^ 2 := by ring
  have h2 : |(f₀ p + ε p * f₁ p) * (g p - (g₀ p + ε p * g₁ p))| ≤ (B₀ + B₁) * D * ε p ^ 2 := by
    rw [abs_mul]
    calc |f₀ p + ε p * f₁ p| * |g p - (g₀ p + ε p * g₁ p)| ≤ (B₀ + B₁) * (D * ε p ^ 2) :=
          mul_le_mul hF (hg' p hp) (abs_nonneg _) (by positivity)
      _ = (B₀ + B₁) * D * ε p ^ 2 := by ring
  have h3 : |ε p ^ 2 * (f₁ p * g₁ p)| ≤ B₁ * G₁ * ε p ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hb₁ p hp) (hg₁ p hp) (abs_nonneg _) hB₁)
      (sq_nonneg _)
  rw [e]
  calc _ ≤ |(f p - (f₀ p + ε p * f₁ p)) * g p| +
        |(f₀ p + ε p * f₁ p) * (g p - (g₀ p + ε p * g₁ p))| + |ε p ^ 2 * (f₁ p * g₁ p)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C * Bg * ε p ^ 2 + (B₀ + B₁) * D * ε p ^ 2 + B₁ * G₁ * ε p ^ 2 := by gcongr
    _ = _ := by ring

theorem IsExp.pow_two (hf : IsExp T ε f f₀ f₁) :
    IsExp T ε (fun p => f p ^ 2) (fun p => f₀ p * f₀ p)
      (fun p => f₀ p * f₁ p + f₁ p * f₀ p) := by
  simpa only [sq] using hf.mul hf

theorem IsExp.pow_three (hf : IsExp T ε f f₀ f₁) :
    IsExp T ε (fun p => f p ^ 3) (fun p => f₀ p * f₀ p * f₀ p)
      (fun p => f₀ p * f₀ p * f₁ p + (f₀ p * f₁ p + f₁ p * f₀ p) * f₀ p) := by
  have h := (hf.mul hf).mul hf
  simp only [pow_succ, pow_zero, one_mul]
  exact h

theorem IsExp.div_const (hf : IsExp T ε f f₀ f₁) (a : ℝ) :
    IsExp T ε (fun p => f p / a) (fun p => f₀ p / a) (fun p => f₁ p / a) := by
  have h := hf.mul (IsExp.const hf.eps a⁻¹)
  simp only [mul_zero, zero_add] at h
  simpa only [div_eq_mul_inv] using h

theorem IsExp.sum {ι : Type} [Fintype ι] [Nonempty ι] {F F₀ F₁ : ι → α → ℝ}
    (h : ∀ i, IsExp T ε (F i) (F₀ i) (F₁ i)) :
    IsExp T ε (fun p => ∑ i, F i p) (fun p => ∑ i, F₀ i p) (fun p => ∑ i, F₁ i p) := by
  choose C hC hr using fun i => (h i).rem
  refine ⟨(h (Classical.arbitrary ι)).eps, BoundedOn.sum' fun i => (h i).b0,
    BoundedOn.sum' fun i => (h i).b1, ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC i,
      fun p hp => ?_⟩⟩
  have e : ∑ i, F i p - (∑ i, F₀ i p + ε p * ∑ i, F₁ i p) =
      ∑ i, (F i p - (F₀ i p + ε p * F₁ i p)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [e, Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hr i p hp)

theorem IsExp.congr {f₀' f₁' : α → ℝ} (h : IsExp T ε f f₀ f₁) (h₀ : ∀ p ∈ T, f₀ p = f₀' p)
    (h₁ : ∀ p ∈ T, f₁ p = f₁' p) : IsExp T ε f f₀' f₁' := by
  obtain ⟨C₀, hC₀, b₀⟩ := h.b0
  obtain ⟨C₁, hC₁, b₁⟩ := h.b1
  obtain ⟨C, hC, hr⟩ := h.rem
  exact ⟨h.eps, ⟨C₀, hC₀, fun p hp => h₀ p hp ▸ b₀ p hp⟩, ⟨C₁, hC₁, fun p hp => h₁ p hp ▸ b₁ p hp⟩,
    ⟨C, hC, fun p hp => by rw [← h₀ p hp, ← h₁ p hp]; exact hr p hp⟩⟩

theorem IsExp.congr_left {f' : α → ℝ} (h : IsExp T ε f f₀ f₁) (hf : ∀ p ∈ T, f p = f' p) :
    IsExp T ε f' f₀ f₁ := by
  obtain ⟨C, hC, hr⟩ := h.rem
  exact ⟨h.eps, h.b0, h.b1, ⟨C, hC, fun p hp => by rw [← hf p hp]; exact hr p hp⟩⟩

end IsExp

/-- Decompose an expansion of a polynomial expression into expansions of its atoms. -/
local macro "exp_on" : tactic => `(tactic| repeat' first
  | intro _
  | with_reducible apply_assumption
  | with_reducible apply IsExp.const
  | with_reducible apply IsExp.add
  | with_reducible apply IsExp.sub
  | with_reducible apply IsExp.mul
  | with_reducible apply IsExp.neg
  | with_reducible apply IsExp.pow_two
  | with_reducible apply IsExp.pow_three
  | with_reducible apply IsExp.div_const
  | with_reducible apply IsExp.sum)

/-! ### The expansions of the inverse and of the jets -/

/-- The leading part of the inverse, `diag(0, 1, 1, 1)`. -/
def inv0 : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The part of order `c⁻²` of the inverse, `diag(−1, 2Φ, 2Φ, 2Φ)`. -/
def inv1 (Φ : E → ℝ) (q : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 0, 0; 0, 2 * Φ q, 0, 0; 0, 0, 2 * Φ q, 0; 0, 0, 0, 2 * Φ q]

/-- The leading part of the first jet. -/
def jet10 (Φ : E → ℝ) (q : E) (m : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-2 * pd Φ q m, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- The part of order `c⁻²` of the first jet. -/
def jet11 (Φ ψ : E → ℝ) (B : E → S) (q : E) (m : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-2 * (2 * Φ q * pd Φ q m + pd ψ q m), pd (comp B 0) q m, pd (comp B 1) q m,
      pd (comp B 2) q m;
    pd (comp B 0) q m, -2 * pd Φ q m, 0, 0;
    pd (comp B 1) q m, 0, -2 * pd Φ q m, 0;
    pd (comp B 2) q m, 0, 0, -2 * pd Φ q m]

/-- The leading part of the second jet. -/
def jet20 (Φ : E → ℝ) (q : E) (m n : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-2 * sd Φ q m n, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- The part of order `c⁻²` of the second jet. -/
def jet21 (Φ ψ : E → ℝ) (B : E → S) (q : E) (m n : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-2 * (2 * (pd Φ q m * pd Φ q n + Φ q * sd Φ q m n) + sd ψ q m n), sd (comp B 0) q m n,
      sd (comp B 1) q m n, sd (comp B 2) q m n;
    sd (comp B 0) q m n, -2 * sd Φ q m n, 0, 0;
    sd (comp B 1) q m n, 0, -2 * sd Φ q m n, 0;
    sd (comp B 2) q m n, 0, 0, -2 * sd Φ q m n]

/-- The parameters `(c, q)` with `c ≥ c₁` and `q ∈ W`. -/
def pnSet (W : Set E) (c₁ : ℝ) : Set (ℝ × E) := {p | c₁ ≤ p.1 ∧ p.2 ∈ W}

/-- The bounds of the potentials on `W` used for the expansion: values, first and second partial
derivatives at most `K`. -/
structure PotentialBounds (Φ ψ : E → ℝ) (B : E → S) (W : Set E) (K : ℝ) : Prop where
  nonneg : 0 ≤ K
  value : ∀ q ∈ W, |Φ q| ≤ K ∧ |ψ q| ≤ K ∧ ∀ j, |B q j| ≤ K
  first : ∀ q ∈ W, ∀ m, |pd Φ q m| ≤ K ∧ |pd ψ q m| ≤ K ∧ ∀ j, |pd (comp B j) q m| ≤ K
  second : ∀ q ∈ W, ∀ m n, |sd Φ q m n| ≤ K ∧ |sd ψ q m n| ≤ K ∧ ∀ j, |sd (comp B j) q m n| ≤ K

/-- **An instance of the bounds**: the zero potentials (Minkowski space) on all of space-time. -/
theorem potentialBounds_zero :
    PotentialBounds (fun _ => 0) (fun _ => 0) (fun _ => 0) Set.univ 0 := by
  have h0 (j : Fin 3) : comp (fun _ => (0 : S)) j = fun _ => 0 := rfl
  refine ⟨le_rfl, fun q _ => by simp, fun q _ m => ?_, fun q _ m n => ?_⟩
  · simp [pd, h0]
  · simp [sd, pd2, h0]

section Setting

variable {Φ ψ : E → ℝ} {B : E → S} {W : Set E} {K : ℝ}

/-- The threshold `c₁ = 8(K² + K + 1) + 1` of the expansion. -/
def threshold (K : ℝ) : ℝ := 8 * (K ^ 2 + K + 1) + 1

theorem eps_bounds {c : ℝ} (hK : 0 ≤ K) (hc : threshold K ≤ c) :
    0 ≤ epsilon c ∧ epsilon c ≤ 1 ∧ epsilon c * (K ^ 2 + K + 1) ≤ 1 / 8 := by
  have h1 : 1 ≤ c := by unfold threshold at hc; nlinarith
  refine ⟨epsilon_nonneg c, epsilon_le_one h1, ?_⟩
  have hc2 : 8 * (K ^ 2 + K + 1) ≤ c ^ 2 := by unfold threshold at hc; nlinarith
  rw [epsilon, inv_mul_le_iff₀ (by positivity)]
  nlinarith

theorem spatialFactor_ge {c : ℝ} {q : E} (hb : PotentialBounds Φ ψ B W K) (hq : q ∈ W)
    (hc : threshold K ≤ c) : 3 / 4 ≤ spatialFactor Φ c q := by
  obtain ⟨he0, -, he⟩ := eps_bounds hb.nonneg hc
  have hΦ := (hb.value q hq).1
  have h1 : epsilon c * |Φ q| ≤ 1 / 8 := by
    have := mul_le_mul_of_nonneg_left hΦ he0
    nlinarith [sq_nonneg K, hb.nonneg]
  have h2 : -(epsilon c * |Φ q|) ≤ epsilon c * Φ q := by
    rw [neg_le, ← mul_neg]
    exact mul_le_mul_of_nonneg_left (neg_le_abs _) he0
  have h3 : epsilon c * Φ q ≤ epsilon c * |Φ q| := mul_le_mul_of_nonneg_left (le_abs_self _) he0
  unfold spatialFactor
  linarith

theorem pnDenom_ge {c : ℝ} {q : E} (hb : PotentialBounds Φ ψ B W K) (hq : q ∈ W)
    (hc : threshold K ≤ c) : 3 / 8 ≤ pnDenom Φ ψ B c q := by
  obtain ⟨he0, he1, he⟩ := eps_bounds hb.nonneg hc
  have hs := spatialFactor_ge hb hq hc
  obtain ⟨hΦ, hψ, -⟩ := hb.value q hq
  have hK := hb.nonneg
  have hΦ' := abs_le.mp hΦ
  have hψ' := abs_le.mp hψ
  have hΦ2 : Φ q ^ 2 ≤ K ^ 2 := by nlinarith
  have ha : 1 / 2 ≤ 1 + 2 * epsilon c * Φ q + 2 * epsilon c ^ 2 * (Φ q ^ 2 + ψ q) := by
    have e1 : -(epsilon c * K) ≤ epsilon c * Φ q := by nlinarith
    have e2 : epsilon c * K ≤ 1 / 8 := by nlinarith
    have e3 : epsilon c ^ 2 * (Φ q ^ 2 + ψ q) ≥ -(epsilon c ^ 2 * K) := by nlinarith
    have e4 : epsilon c ^ 2 * K ≤ 1 / 8 := by nlinarith
    linarith
  have hB : 0 ≤ epsilon c ^ 3 * (B q 0 ^ 2 + B q 1 ^ 2 + B q 2 ^ 2) := by positivity
  unfold pnDenom
  nlinarith

end Setting

/-! ### The Ricci tensor of the family as a polynomial in the jets -/

section Reduction

variable {Φ ψ : E → ℝ} {B : E → S} {W : Set E} {K : ℝ}

theorem contDiffAt_pnCoefficient (c : ℝ) {q : E} (hΦ : ContDiffAt ℝ 2 Φ q)
    (hψ : ContDiffAt ℝ 2 ψ q) (hB : ∀ j, ContDiffAt ℝ 2 (comp B j) q) (a b : Fin 4) :
    ContDiffAt ℝ 2 (fun z => pnCoefficient Φ ψ B c z a b) q := by
  have hB0 : ContDiffAt ℝ 2 (fun z => B z 0) q := hB 0
  have hB1 : ContDiffAt ℝ 2 (fun z => B z 1) q := hB 1
  have hB2 : ContDiffAt ℝ 2 (fun z => B z 2) q := hB 2
  fin_cases a <;> fin_cases b <;> simp [pnCoefficient, spatialFactor] <;> fun_prop

theorem pnCoefficient_inv {c : ℝ} {q : E} (hb : PotentialBounds Φ ψ B W K) (hq : q ∈ W)
    (hc : threshold K ≤ c) : (pnCoefficient Φ ψ B c q)⁻¹ = pnInverse Φ ψ B c q := by
  have hc0 : c ≠ 0 := by unfold threshold at hc; nlinarith [hb.nonneg]
  exact Matrix.inv_eq_right_inv (pnCoefficient_mul_inverse hc0
    (by linarith [spatialFactor_ge hb hq hc]) (by linarith [pnDenom_ge hb hq hc]))

/-- **The Ricci tensor of the post-Newtonian family** at a point of `W`, for `c ≥ c₁`, is the
polynomial `ricciJet` in the inverse `pnInverse` and the jets `pnJet1`, `pnJet2`. -/
theorem ricciOf_pnCoefficient (hW : IsOpen W) (hΦ : ∀ z ∈ W, ContDiffAt ℝ 2 Φ z)
    (hψ : ∀ z ∈ W, ContDiffAt ℝ 2 ψ z) (hB : ∀ z ∈ W, ∀ j, ContDiffAt ℝ 2 (comp B j) z)
    (hb : PotentialBounds Φ ψ B W K) {c : ℝ} (hc : threshold K ≤ c) {q : E} (hq : q ∈ W)
    (j k : Fin 4) :
    ricciOf (d := 3) (pnCoefficient Φ ψ B c) q j k =
      ricciJet (pnInverse Φ ψ B c q) (pnJet1 Φ ψ B c q) (pnJet2 Φ ψ B c q) j k := by
  have hc0 : c ≠ 0 := by unfold threshold at hc; nlinarith [hb.nonneg]
  have hdet : ∀ᶠ z in 𝓝 q, (pnCoefficient Φ ψ B c z).det ≠ 0 := by
    filter_upwards [hW.mem_nhds hq] with z hz
    exact Matrix.det_ne_zero_of_right_inverse (pnCoefficient_mul_inverse hc0
      (by linarith [spatialFactor_ge hb hz hc]) (by linarith [pnDenom_ge hb hz hc]))
  rw [ricciOf_eq_ricciJet (fun a b => contDiffAt_pnCoefficient c (hΦ q hq) (hψ q hq)
    (hB q hq) a b) hdet, pnCoefficient_inv hb hq hc]
  have h1 : jet1 (d := 3) (pnCoefficient Φ ψ B c) q = fun m a b => pnJet1 Φ ψ B c q m a b :=
    funext fun m => funext fun a => funext fun b => jet1_pnCoefficient c
      ((hΦ q hq).differentiableAt (by norm_num)) ((hψ q hq).differentiableAt (by norm_num))
      (fun i => (hB q hq i).differentiableAt (by norm_num)) m a b
  have h2 : jet2 (d := 3) (pnCoefficient Φ ψ B c) q = fun m n a b => pnJet2 Φ ψ B c q m n a b :=
    funext fun m => funext fun n => funext fun a => funext fun b =>
      jet2_pnCoefficient c hW hq hΦ hψ hB m n a b
  rw [h1, h2]

end Reduction

section Expansions

variable {Φ ψ : E → ℝ} {B : E → S} {W : Set E} {K : ℝ}

theorem pnSet_eps (hK : 0 ≤ K) : ∀ p ∈ pnSet W (threshold K),
    0 ≤ epsilon p.1 ∧ epsilon p.1 ≤ 1 :=
  fun _ hp => ⟨(eps_bounds hK hp.1).1, (eps_bounds hK hp.1).2.1⟩

theorem boundedOn_of_W {g : E → ℝ} (h : ∀ q ∈ W, |g q| ≤ K) :
    BoundedOn (pnSet W (threshold K)) (fun p => g p.2) :=
  BoundedOn.of_le' fun p hp => h p.2 hp.2

theorem exp_sigma (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => (spatialFactor Φ p.1 p.2)⁻¹) (fun _ => 1) (fun p => 2 * Φ p.2) := by
  have hs (p : ℝ × E) (hp : p ∈ pnSet W (threshold K)) : spatialFactor Φ p.1 p.2 ≠ 0 := by
    linarith [spatialFactor_ge hb hp.2 hp.1]
  refine IsExp.of_eq (f₂ := fun p => 4 * Φ p.2 ^ 2 * (spatialFactor Φ p.1 p.2)⁻¹)
    (pnSet_eps hb.nonneg) (BoundedOn.const' 1) ?_ ?_ fun p hp => ?_
  · exact (BoundedOn.const' 2).mul' (boundedOn_of_W fun q hq => (hb.value q hq).1)
  · have hσ : BoundedOn (pnSet W (threshold K)) (fun p => (spatialFactor Φ p.1 p.2)⁻¹) :=
      BoundedOn.of_le' (C := 4 / 3) fun p hp => by
        have h := spatialFactor_ge hb hp.2 hp.1
        rw [abs_of_pos (inv_pos.mpr (by linarith))]
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
    have hΦ := boundedOn_of_W (K := K) (W := W) fun q hq => (hb.value q hq).1
    obtain ⟨C, hC, h⟩ := ((BoundedOn.const' 4).mul' (hΦ.mul' hΦ)).mul' hσ
    exact ⟨C, hC, fun p hp => by
      have := h p hp
      simp only at this ⊢
      rw [show 4 * Φ p.2 ^ 2 * (spatialFactor Φ p.1 p.2)⁻¹ =
        4 * (Φ p.2 * Φ p.2) * (spatialFactor Φ p.1 p.2)⁻¹ by ring]
      exact this⟩
  · have h := hs p hp
    simp only [spatialFactor] at h ⊢
    field_simp
    ring

theorem exp_delta (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => (pnDenom Φ ψ B p.1 p.2)⁻¹) (fun _ => 1) (fun _ => 0) := by
  have hK := hb.nonneg
  have hδ : BoundedOn (pnSet W (threshold K)) (fun p => (pnDenom Φ ψ B p.1 p.2)⁻¹) :=
    BoundedOn.of_le' (C := 8 / 3) fun p hp => by
      have h := pnDenom_ge hb hp.2 hp.1
      rw [abs_of_pos (inv_pos.mpr (by linarith)), inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
  set d₂ : ℝ × E → ℝ := fun p => 2 * ψ p.2 - 2 * Φ p.2 ^ 2 -
    4 * epsilon p.1 * Φ p.2 * (Φ p.2 ^ 2 + ψ p.2) +
      epsilon p.1 * (B p.2 0 ^ 2 + B p.2 1 ^ 2 + B p.2 2 ^ 2) with hd₂
  have hdb : BoundedOn (pnSet W (threshold K)) d₂ := by
    have hΦ := boundedOn_of_W (K := K) (W := W) fun q hq => (hb.value q hq).1
    have hψ := boundedOn_of_W (K := K) (W := W) fun q hq => (hb.value q hq).2.1
    have hB (j : Fin 3) := boundedOn_of_W (K := K) (W := W) (g := fun q => B q j)
      fun q hq => (hb.value q hq).2.2 j
    have hε : BoundedOn (pnSet W (threshold K)) (fun p => epsilon p.1) :=
      BoundedOn.of_le' (C := 1) fun p hp => by
        rw [abs_of_nonneg (eps_bounds hK hp.1).1]; exact (eps_bounds hK hp.1).2.1
    obtain ⟨C, hC, h⟩ := (((((BoundedOn.const' 2).mul' hψ).add'
      ((BoundedOn.const' (-2)).mul' (hΦ.mul' hΦ))).add' ((((BoundedOn.const' (-4)).mul' hε).mul'
      hΦ).mul' ((hΦ.mul' hΦ).add' hψ))).add' (hε.mul' (((hB 0).mul' (hB 0)).add'
      ((hB 1).mul' (hB 1)) |>.add' ((hB 2).mul' (hB 2)))))
    exact ⟨C, hC, fun p hp => by
      have := h p hp
      simp only [hd₂] at this ⊢
      convert this using 2
      ring⟩
  refine IsExp.of_eq (f₂ := fun p => -(d₂ p * (pnDenom Φ ψ B p.1 p.2)⁻¹)) (pnSet_eps hK)
    (BoundedOn.const' 1) (BoundedOn.const' 0) (hdb.mul' hδ).neg' fun p hp => ?_
  have hD : pnDenom Φ ψ B p.1 p.2 = 1 + epsilon p.1 ^ 2 * d₂ p := by
    simp only [pnDenom, spatialFactor, hd₂]
    ring
  have hD0 : pnDenom Φ ψ B p.1 p.2 ≠ 0 := by linarith [pnDenom_ge hb hp.2 hp.1]
  have hinv : (pnDenom Φ ψ B p.1 p.2)⁻¹ * pnDenom Φ ψ B p.1 p.2 = 1 := inv_mul_cancel₀ hD0
  linear_combination hinv - (pnDenom Φ ψ B p.1 p.2)⁻¹ * hD

/-- The expansions of the atoms of the jets. -/
theorem exp_atoms (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => epsilon p.1) (fun _ => 0)
      (fun _ => 1) ∧
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => Φ p.2) (fun p => Φ p.2)
      (fun _ => 0) ∧
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => ψ p.2) (fun p => ψ p.2)
      (fun _ => 0) ∧
    (∀ j, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => B p.2 j)
      (fun p => B p.2 j) (fun _ => 0)) ∧
    (∀ m, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => pd Φ p.2 m)
      (fun p => pd Φ p.2 m) (fun _ => 0)) ∧
    (∀ m, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => pd ψ p.2 m)
      (fun p => pd ψ p.2 m) (fun _ => 0)) ∧
    (∀ j m, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => pd (comp B j) p.2 m)
      (fun p => pd (comp B j) p.2 m) (fun _ => 0)) ∧
    (∀ m n, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => sd Φ p.2 m n)
      (fun p => sd Φ p.2 m n) (fun _ => 0)) ∧
    (∀ m n, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => sd ψ p.2 m n)
      (fun p => sd ψ p.2 m n) (fun _ => 0)) ∧
    (∀ j m n, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => sd (comp B j) p.2 m n) (fun p => sd (comp B j) p.2 m n) (fun _ => 0)) := by
  have he := pnSet_eps (W := W) hb.nonneg
  refine ⟨IsExp.eps_self he, IsExp.atom he (boundedOn_of_W fun q hq => (hb.value q hq).1),
    IsExp.atom he (boundedOn_of_W fun q hq => (hb.value q hq).2.1),
    fun j => IsExp.atom he (boundedOn_of_W (g := fun q => B q j) fun q hq =>
      (hb.value q hq).2.2 j),
    fun m => IsExp.atom he (boundedOn_of_W fun q hq => (hb.first q hq m).1),
    fun m => IsExp.atom he (boundedOn_of_W fun q hq => (hb.first q hq m).2.1),
    fun j m => IsExp.atom he (boundedOn_of_W fun q hq => (hb.first q hq m).2.2 j),
    fun m n => IsExp.atom he (boundedOn_of_W fun q hq => (hb.second q hq m n).1),
    fun m n => IsExp.atom he (boundedOn_of_W fun q hq => (hb.second q hq m n).2.1),
    fun j m n => IsExp.atom he (boundedOn_of_W fun q hq => (hb.second q hq m n).2.2 j)⟩

theorem exp_inverse (hb : PotentialBounds Φ ψ B W K) (a b : Fin 4) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => pnInverse Φ ψ B p.1 p.2 a b) (fun _ => inv0 a b) (fun p => inv1 Φ p.2 a b) := by
  obtain ⟨hε, hΦ, -, hB, -⟩ := exp_atoms hb
  have he := pnSet_eps (W := W) hb.nonneg
  have hσ := exp_sigma hb
  have hδ := exp_delta hb
  have hs : IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => spatialFactor Φ p.1 p.2) (fun _ => 1) (fun p => -2 * Φ p.2) := by
    apply IsExp.congr
    · simp only [spatialFactor]
      exp_on
    · intro p _; ring
    · intro p _; ring
  fin_cases a <;> fin_cases b <;>
    (apply IsExp.congr
     focus
       simp [pnInverse, pnSpatialInverse]
       exp_on
     all_goals intro p _
     all_goals simp [inv0, inv1])

theorem exp_jet1 (hb : PotentialBounds Φ ψ B W K) (m a b : Fin 4) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => pnJet1 Φ ψ B p.1 p.2 m a b) (fun p => jet10 Φ p.2 m a b)
      (fun p => jet11 Φ ψ B p.2 m a b) := by
  obtain ⟨hε, hΦ, hψ, hB, hpΦ, hpψ, hpB, -⟩ := exp_atoms hb
  have he := pnSet_eps (W := W) hb.nonneg
  have hpΦm := hpΦ m
  have hpψm := hpψ m
  have hpB0 := hpB 0 m
  have hpB1 := hpB 1 m
  have hpB2 := hpB 2 m
  fin_cases a <;> fin_cases b <;>
    (apply IsExp.congr
     focus
       simp [pnJet1]
       exp_on
     all_goals intro p _
     all_goals simp [jet10, jet11])

theorem exp_jet2 (hb : PotentialBounds Φ ψ B W K) (m n a b : Fin 4) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => pnJet2 Φ ψ B p.1 p.2 m n a b) (fun p => jet20 Φ p.2 m n a b)
      (fun p => jet21 Φ ψ B p.2 m n a b) := by
  obtain ⟨hε, hΦ, hψ, hB, hpΦ, hpψ, hpB, hsΦ, hsψ, hsB⟩ := exp_atoms hb
  have he := pnSet_eps (W := W) hb.nonneg
  have hpΦm := hpΦ m
  have hpΦn := hpΦ n
  have hsΦm := hsΦ m n
  have hsψm := hsψ m n
  have hsB0 := hsB 0 m n
  have hsB1 := hsB 1 m n
  have hsB2 := hsB 2 m n
  fin_cases a <;> fin_cases b <;>
    (apply IsExp.congr
     focus
       simp [pnJet2]
       exp_on
     all_goals intro p _
     all_goals simp [jet20, jet21])

/-- The flat spatial Laplacian `Σ_α ∂_α² g` at `q`. -/
def lap (g : E → ℝ) (q : E) : ℝ := sd g q 1 1 + sd g q 2 2 + sd g q 3 3

/-- The time derivative of the divergence, `∂_t ∇ · B`. -/
def dtDiv (B : E → S) (q : E) : ℝ := sd (comp B 0) q 0 1 + sd (comp B 1) q 0 2 + sd (comp B 2) q 0 3

/-- **The time-time component to first order**: `R_tt = ΔΦ + c⁻²(4ΦΔΦ + Δψ + ∂_t(3∂_tΦ + ∇ · B))`
up to `O(c⁻⁴)`. -/
theorem exp_ricci_tt (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        0 0)
      (fun p => lap Φ p.2)
      (fun p => 4 * Φ p.2 * lap Φ p.2 + lap ψ p.2 + 3 * sd Φ p.2 0 0 + dtDiv B p.2) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, lap, dtDiv]
  all_goals ring

/-- The gradient of the divergence, `∂_α ∇ · B`. -/
def gradDiv (B : E → S) (q : E) (α : Fin 3) : ℝ :=
  sd (comp B 0) q α.succ 1 + sd (comp B 1) q α.succ 2 + sd (comp B 2) q α.succ 3

theorem exp_ricci_t0 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        0 1)
      (fun _ => 0)
      (fun p => -(lap (comp B 0) p.2 - gradDiv B p.2 0 - 4 * sd Φ p.2 0 1) / 2) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, lap, gradDiv, comp_eq]
  all_goals ring

theorem exp_ricci_t1 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        0 2)
      (fun _ => 0)
      (fun p => -(lap (comp B 1) p.2 - gradDiv B p.2 1 - 4 * sd Φ p.2 0 2) / 2) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, lap, gradDiv, comp_eq]
  all_goals ring

theorem exp_ricci_t2 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        0 3)
      (fun _ => 0)
      (fun p => -(lap (comp B 2) p.2 - gradDiv B p.2 2 - 4 * sd Φ p.2 0 3) / 2) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, lap, gradDiv, comp_eq]
  all_goals ring

theorem exp_ricci_s00 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        1 1)
      (fun _ => 0) (fun p => lap Φ p.2) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, lap, comp_eq]
  all_goals ring

theorem exp_ricci_s01 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        1 2)
      (fun _ => 0) (fun _ => 0) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, comp_eq]

theorem exp_ricci_s02 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        1 3)
      (fun _ => 0) (fun _ => 0) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, comp_eq]

theorem exp_ricci_s10 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        2 1)
      (fun _ => 0) (fun _ => 0) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, comp_eq]

theorem exp_ricci_s11 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        2 2)
      (fun _ => 0) (fun p => lap Φ p.2) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, lap, comp_eq]
  all_goals ring

theorem exp_ricci_s12 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        2 3)
      (fun _ => 0) (fun _ => 0) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, comp_eq]

theorem exp_ricci_s20 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        3 1)
      (fun _ => 0) (fun _ => 0) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, comp_eq]

theorem exp_ricci_s21 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        3 2)
      (fun _ => 0) (fun _ => 0) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, comp_eq]

theorem exp_ricci_s22 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        3 3)
      (fun _ => 0) (fun p => lap Φ p.2) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, lap, comp_eq]
  all_goals ring

theorem exp_ricci_r0 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        1 0)
      (fun _ => 0)
      (fun p => -(lap (comp B 0) p.2 - gradDiv B p.2 0 - 4 * sd Φ p.2 0 1) / 2) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, lap, gradDiv, comp_eq]
  all_goals ring

theorem exp_ricci_r1 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        2 0)
      (fun _ => 0)
      (fun p => -(lap (comp B 1) p.2 - gradDiv B p.2 1 - 4 * sd Φ p.2 0 2) / 2) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, lap, gradDiv, comp_eq]
  all_goals ring

theorem exp_ricci_r2 (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        3 0)
      (fun _ => 0)
      (fun p => -(lap (comp B 2) p.2 - gradDiv B p.2 2 - 4 * sd Φ p.2 0 3) / 2) := by
  have he := pnSet_eps (W := W) hb.nonneg
  have hM := exp_inverse hb
  have hJ1 := exp_jet1 hb
  have hJ2 := exp_jet2 hb
  apply IsExp.congr
  focus
    simp only [ricciJet, dGamJet, gamJet, lowerJet]
    exp_on
  all_goals intro p _
  all_goals simp (config := {decide := true}) [Fin.sum_univ_four, inv0, inv1, jet10, jet11,
    jet20, jet21, sd, lap, gradDiv, comp_eq]
  all_goals ring

/-- **The time-space components to first order**:
`R_tα = −(1/2c²)(ΔB_α − ∂_α ∇ · B − 4 ∂_t∂_α Φ)` up to `O(c⁻⁴)`. -/
theorem exp_ricci_ti (hb : PotentialBounds Φ ψ B W K) (α : Fin 3) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        0 α.succ)
      (fun _ => 0)
      (fun p => -(lap (comp B α) p.2 - gradDiv B p.2 α - 4 * sd Φ p.2 0 α.succ) / 2) := by
  fin_cases α
  · exact exp_ricci_t0 hb
  · exact exp_ricci_t1 hb
  · exact exp_ricci_t2 hb

/-- **The space-space components to first order**: `R_αβ = c⁻² ΔΦ δ_αβ` up to `O(c⁻⁴)`. -/
theorem exp_ricci_ij (hb : PotentialBounds Φ ψ B W K) (α β : Fin 3) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        α.succ β.succ)
      (fun _ => 0) (fun p => if α = β then lap Φ p.2 else 0) := by
  fin_cases α <;> fin_cases β <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
    Fin.reduceFinMk, ↓reduceIte, Fin.reduceEq]
  · exact exp_ricci_s00 hb
  · exact exp_ricci_s01 hb
  · exact exp_ricci_s02 hb
  · exact exp_ricci_s10 hb
  · exact exp_ricci_s11 hb
  · exact exp_ricci_s12 hb
  · exact exp_ricci_s20 hb
  · exact exp_ricci_s21 hb
  · exact exp_ricci_s22 hb

theorem exp_ricci_it (hb : PotentialBounds Φ ψ B W K) (α : Fin 3) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        α.succ 0)
      (fun _ => 0)
      (fun p => -(lap (comp B α) p.2 - gradDiv B p.2 α - 4 * sd Φ p.2 0 α.succ) / 2) := by
  fin_cases α
  · exact exp_ricci_r0 hb
  · exact exp_ricci_r1 hb
  · exact exp_ricci_r2 hb

end Expansions

/-! ### The field equations of the second approximation -/

/-- The leading part `R⁽⁰⁾` of the Ricci tensor of the family in the coordinates `(t, x)`. -/
def ricciLeading (Φ : E → ℝ) (q : E) (j k : Fin 4) : ℝ := if j = 0 ∧ k = 0 then lap Φ q else 0

/-- The part `R⁽¹⁾` of order `c⁻²` of the Ricci tensor of the family:
`4ΦΔΦ + Δψ + ∂_t(3∂_tΦ + ∇ · B)` (time-time), `−(ΔB_α − ∂_α ∇ · B − 4∂_t∂_αΦ)/2`
(time-space) and `ΔΦ δ_αβ` (space-space). -/
def ricciFirst (Φ ψ : E → ℝ) (B : E → S) (q : E) (j k : Fin 4) : ℝ :=
  Fin.cases (Fin.cases (4 * Φ q * lap Φ q + lap ψ q + 3 * sd Φ q 0 0 + dtDiv B q)
      (fun β => -(lap (comp B β) q - gradDiv B q β - 4 * sd Φ q 0 β.succ) / 2) k)
    (fun α => Fin.cases (-(lap (comp B α) q - gradDiv B q α - 4 * sd Φ q 0 α.succ) / 2)
      (fun β => if α = β then lap Φ q else 0) k) j

section Field

variable {Φ ψ : E → ℝ} {B : E → S} {W : Set E} {K : ℝ}

theorem exp_ricci (hb : PotentialBounds Φ ψ B W K) (j k : Fin 4) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        j k)
      (fun p => ricciLeading Φ p.2 j k) (fun p => ricciFirst Φ ψ B p.2 j k) := by
  refine Fin.cases ?_ (fun α => ?_) j <;> refine Fin.cases ?_ (fun β => ?_) k
  · exact (exp_ricci_tt hb).congr (fun p _ => by simp [ricciLeading])
      (fun p _ => by simp [ricciFirst])
  · exact (exp_ricci_ti hb β).congr (fun p _ => by simp [ricciLeading, Fin.succ_ne_zero])
      (fun p _ => by simp [ricciFirst])
  · exact (exp_ricci_it hb α).congr (fun p _ => by simp [ricciLeading, Fin.succ_ne_zero])
      (fun p _ => by simp [ricciFirst])
  · exact (exp_ricci_ij hb α β).congr (fun p _ => by simp [ricciLeading, Fin.succ_ne_zero])
      (fun p _ => by simp [ricciFirst])

/-- **The Ricci tensor of the post-Newtonian family to the order `c⁻²`, uniformly (target (1),
geometric part).** For potentials `C²` on an open set `W` with values and first two derivatives
bounded by `K` there, every component of the coordinate Ricci tensor of the family in `(t, x)`
satisfies `|R_jk − R⁽⁰⁾_jk − c⁻² R⁽¹⁾_jk| ≤ C/c⁴` on `W` for all `c ≥ c₁ = 8(K² + K + 1) + 1`:
`R_tt = ΔΦ + c⁻²(4ΦΔΦ + Δψ + ∂_t(3∂_tΦ + ∇ · B))`, `R_tα = −(ΔB_α − ∂_α∇ · B − 4∂_t∂_αΦ)/2c²`,
`R_αβ = ΔΦ δ_αβ/c²`. -/
theorem abs_ricciOf_pnCoefficient_sub_le (hW : IsOpen W) (hΦ : ∀ z ∈ W, ContDiffAt ℝ 2 Φ z)
    (hψ : ∀ z ∈ W, ContDiffAt ℝ 2 ψ z) (hB : ∀ z ∈ W, ∀ j, ContDiffAt ℝ 2 (comp B j) z)
    (hb : PotentialBounds Φ ψ B W K) :
    ∃ C, 0 ≤ C ∧ ∀ c, threshold K ≤ c → ∀ q ∈ W, ∀ j k : Fin 4,
      |ricciOf (d := 3) (pnCoefficient Φ ψ B c) q j k -
        (ricciLeading Φ q j k + epsilon c * ricciFirst Φ ψ B q j k)| ≤ C / c ^ 4 := by
  choose C hC0 hC using fun j k => (exp_ricci hb j k).rem
  refine ⟨∑ j, ∑ k, C j k, Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hC0 j k,
    fun c hc q hq j k => ?_⟩
  have hp : ((c, q) : ℝ × E) ∈ pnSet W (threshold K) := ⟨hc, hq⟩
  have h := hC j k (c, q) hp
  rw [← ricciOf_pnCoefficient hW hΦ hψ hB hb hc hq j k] at h
  have hc4 : epsilon c ^ 2 = 1 / c ^ 4 := by rw [epsilon, inv_pow, ← pow_mul, one_div]
  simp only at h
  rw [hc4] at h
  refine h.trans ?_
  rw [mul_one_div]
  have hle : C j k ≤ ∑ j, ∑ k, C j k :=
    (Finset.single_le_sum (fun k _ => hC0 j k) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun k _ => hC0 j k)
        (Finset.mem_univ j))
  have hc0 : 0 < c := by unfold threshold at hc; nlinarith [hb.nonneg]
  exact div_le_div_of_nonneg_right hle (by positivity)


end Field

end ProjectAinos.GeneralRelativity.PostNewtonianRicci
