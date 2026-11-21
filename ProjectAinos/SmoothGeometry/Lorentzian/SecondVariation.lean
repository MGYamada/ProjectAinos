/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CovariantLeibniz

/-!
# The second variation of the Ricci tensor along `g + s h`

For a coordinate metric `g` on an open set `U` and a smooth symmetric field `h` of coefficient
matrices, this file computes the second derivative in `s` at `0` of the Ricci tensor of
`g + s h`, with the Levi-Civita connection `Γ` of `g` and `δΓ = curvedChristoffel h`.

* `christoffelOf_perturbation_eq`: the exact identity `Γ(g + s h) = Γ + s E(s)` where the
  matrix of `g + s h` is invertible, with `E(s) = (g + s h)^{-1} X` (`christoffelQuotient`),
  `X_{lij} = ½ (∂_i h_{jl} + ∂_j h_{li} − ∂_l h_{ij}) − h_{lb} Γ^b_{ij}`
  (`christoffelDifferenceLow`); `christoffelQuotient_zero`: `E(0) = δΓ`;
  `hasDerivAt_christoffelQuotient`: `∂_s E(0) = −g^{-1} h δΓ` (`raiseContract`).
* `ricciOf_eq_of_christoffel`: for any connection `Γ + D`,
  `Ric(Γ + D) = Ric(Γ) + ∇_i D^i_{jk} − ∇_j D^i_{ik} + D^i_{ia} D^a_{jk} − D^i_{ja} D^a_{ik}`
  (`palatini`, `christoffelQuadratic`).
* **The second variation.** `hasDerivAt_deriv_ricciOf_perturbation` and
  `deriv_deriv_ricciOf_perturbation`: the derivative at `0` of `s ↦ d/ds Ric(g + s h)` is
  `secondRicci g h = −2 ∇_i (g^{-1} h δΓ)^i_{jk} + 2 ∇_j (g^{-1} h δΓ)^i_{ik}
  + 2 (δΓ^i_{ia} δΓ^a_{jk} − δΓ^i_{ja} δΓ^a_{ik})`, and `s ↦ Ric(g + s h)` is differentiable
  near `0` (`eventually_differentiableAt_ricciOf_perturbation`), so the statement is not a junk
  value of `deriv`.
* `eventually_ricciOf_perturbation`: `Ric(g + s h) = Ric(g) + s p(s) + s² q(s)` near `s = 0`, with
  the smooth coefficients `secondVariationLinear` and `secondVariationQuadratic`;
  `hasDerivAt_deriv_mul_add` is the calculus of `c + s p(s) + s² q(s)` used for the second
  derivative.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology Matrix

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

/-- The quadratic part `P^i_{ia} P'^a_{jk} − P^i_{ja} P'^a_{ik}` of the Ricci tensor of a
connection, bilinear in two arrays. -/
def christoffelQuadratic {n : ℕ} (P P' : Fin n → Fin n → Fin n → ℝ) (j k : Fin n) : ℝ :=
  ∑ i, ∑ a, (P i i a * P' a j k - P i j a * P' a i k)

section Definitions

variable (g : CoordinateMetric σ d U)

/-- The array `(g^{-1} h P)^k_{ij} = g^{kl} h_{lm} P^m_{ij}`. -/
def raiseContract (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ) (z : MinkowskiModel d)
    (k i j : Fin (d + 1)) : ℝ :=
  ∑ l, (g.coefficient z)⁻¹ k l * ∑ m, h z l m * P z m i j

/-- **The second variation of the Ricci tensor** along `g + s h`:
`−2 ∇_i (g^{-1} h δΓ)^i_{jk} + 2 ∇_j (g^{-1} h δΓ)^i_{ik} + 2 (δΓ^i_{ia} δΓ^a_{jk}
− δΓ^i_{ja} δΓ^a_{ik})`. -/
def secondRicci (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  -2 * g.palatini (g.raiseContract h (g.curvedChristoffel h)) x j k +
    2 * christoffelQuadratic (g.curvedChristoffel h x) (g.curvedChristoffel h x) j k

/-- The lowered array `X_{lij} = ½ (∂_i h_{jl} + ∂_j h_{li} − ∂_l h_{ij}) − h_{lb} Γ^b_{ij}`. -/
def christoffelDifferenceLow (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (z : MinkowskiModel d) (l i j : Fin (d + 1)) : ℝ :=
  (fderiv ℝ (fun y => h y j l) z (Pi.single i 1) + fderiv ℝ (fun y => h y l i) z (Pi.single j 1) -
    fderiv ℝ (fun y => h y i j) z (Pi.single l 1)) / 2 -
    ∑ b, h z l b * christoffelOf g.coefficient z b i j

/-- The exact difference quotient `E(s, z) = (g + s h)^{-1} X` of the Christoffel symbols. -/
def christoffelQuotient (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (p : ℝ × MinkowskiModel d) (k i j : Fin (d + 1)) : ℝ :=
  ∑ l, (g.perturbationFamily h p)⁻¹ k l * g.christoffelDifferenceLow h p.2 l i j

end Definitions

variable {g : CoordinateMetric σ d U} {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

/-! ### The connection of `g + s h` -/

/-- **The exact Christoffel symbols of `g + s h`**: `Γ(g + s h) = Γ + s E(s)` at a point of `U`
where `g + s h` is invertible. -/
theorem christoffelOf_perturbation_eq (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {s : ℝ} {z : MinkowskiModel d} (hz : z ∈ U) (hdet : (g.perturbationFamily h (s, z)).det ≠ 0)
    (k i j : Fin (d + 1)) :
    christoffelOf (fun y => g.coefficient y + s • h y) z k i j =
      christoffelOf g.coefficient z k i j + s * g.christoffelQuotient h (s, z) k i j := by
  have hgd (a b : Fin (d + 1)) : DifferentiableAt ℝ (fun y => g.coefficient y a b) z :=
    differentiableAt_of_contDiffOn (g.coefficient_contDiffOn a b) hz
  have hhd (a b : Fin (d + 1)) : DifferentiableAt ℝ (fun y => h y a b) z :=
    differentiableAt_of_contDiffOn (hh a b) hz
  have hfd (a b c : Fin (d + 1)) :
      fderiv ℝ (fun y => (g.coefficient y + s • h y) a b) z (Pi.single c 1) =
        fderiv ℝ (fun y => g.coefficient y a b) z (Pi.single c 1) +
          s * fderiv ℝ (fun y => h y a b) z (Pi.single c 1) := by
    have e : (fun y => (g.coefficient y + s • h y) a b) =
        fun y => g.coefficient y a b + s * h y a b := by
      funext y; simp [Matrix.add_apply, Matrix.smul_apply]
    rw [e, fderiv_fun_add (hgd a b) ((hhd a b).const_mul s), fderiv_const_mul (hhd a b)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  set M := g.perturbationFamily h (s, z)
  set Gz := g.coefficient z
  set v : Fin (d + 1) → ℝ := fun l =>
    (fderiv ℝ (fun y => g.coefficient y j l) z (Pi.single i 1) +
      fderiv ℝ (fun y => g.coefficient y l i) z (Pi.single j 1) -
      fderiv ℝ (fun y => g.coefficient y i j) z (Pi.single l 1)) / 2
  set w : Fin (d + 1) → ℝ := fun l =>
    (fderiv ℝ (fun y => h y j l) z (Pi.single i 1) + fderiv ℝ (fun y => h y l i) z (Pi.single j 1) -
      fderiv ℝ (fun y => h y i j) z (Pi.single l 1)) / 2
  set u : Fin (d + 1) → ℝ := Gz⁻¹ *ᵥ v
  have hM : M = Gz + s • h z := rfl
  have hGu : Gz *ᵥ u = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (g.coefficient_det_ne_zero ⟨z, hz⟩)), Matrix.one_mulVec]
  have hMinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have hlhs : christoffelOf (fun y => g.coefficient y + s • h y) z k i j =
      (M⁻¹ *ᵥ (v + s • w)) k := by
    unfold christoffelOf
    beta_reduce
    rw [show g.coefficient z + s • h z = M from rfl]
    simp only [hfd, Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, v, w]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hΓ : christoffelOf g.coefficient z k i j = u k := by
    unfold christoffelOf
    simp only [u, Matrix.mulVec, dotProduct, v]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hE : g.christoffelQuotient h (s, z) k i j = (M⁻¹ *ᵥ (w - h z *ᵥ u)) k := by
    unfold christoffelQuotient christoffelDifferenceLow
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, w, u, v]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 2
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    unfold christoffelOf
    exact Finset.sum_congr rfl fun m _ => by ring
  have key : M⁻¹ *ᵥ (v + s • w) = u + s • (M⁻¹ *ᵥ (w - h z *ᵥ u)) := by
    have hv : v = M *ᵥ u - s • (h z *ᵥ u) := by
      rw [hM, Matrix.add_mulVec, Matrix.smul_mulVec, hGu]
      abel
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_sub]
    module
  rw [hlhs, hΓ, hE, key]
  simp

/-- `E(0) = δΓ`: at `s = 0` the difference quotient is the linearized Christoffel symbols. -/
theorem christoffelQuotient_zero (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {z : MinkowskiModel d}
    (hz : z ∈ U) (k i j : Fin (d + 1)) :
    g.christoffelQuotient h (0, z) k i j = g.curvedChristoffel h z k i j := by
  have hP : g.perturbationFamily h (0, z) = g.coefficient z := by simp [perturbationFamily]
  have hsymΓ (a b c : Fin (d + 1)) : christoffelOf g.coefficient z a b c =
      christoffelOf g.coefficient z a c b := g.christoffelOf_coefficient_symm hz a b c
  have hd : fderiv ℝ (fun y => h y i j) z = fderiv ℝ (fun y => h y j i) z :=
    Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (U.isOpen.mem_nhds hz)
      fun y hy => hs y hy i j)
  unfold christoffelQuotient curvedChristoffel christoffelDifferenceLow covDerivTwo
  rw [hP]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hX : ∑ b, (christoffelOf g.coefficient z b i j * h z b l +
        christoffelOf g.coefficient z b i l * h z j b) +
      ∑ b, (christoffelOf g.coefficient z b j l * h z b i +
        christoffelOf g.coefficient z b j i * h z l b) -
      ∑ b, (christoffelOf g.coefficient z b l i * h z b j +
        christoffelOf g.coefficient z b l j * h z i b) =
      2 * ∑ b, h z l b * christoffelOf g.coefficient z b i j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hsymΓ b l i, hsymΓ b l j, hsymΓ b j i, hs z hz j b, hs z hz b i, hs z hz b l]
    ring
  rw [mul_div_assoc]
  congr 1
  linarith [hX]

/-- The entries of `g + s h` are smooth in `(s, z)` and its determinant is eventually nonzero
near `(0, x)`. -/
theorem eventually_perturbationFamily (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {x : MinkowskiModel d} (hx : x ∈ U) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), x), p.2 ∈ U ∧ (g.perturbationFamily h p).det ≠ 0 := by
  have hdet0 : (g.perturbationFamily h ((0 : ℝ), x)).det ≠ 0 := by
    simpa [perturbationFamily] using g.coefficient_det_ne_zero ⟨x, hx⟩
  have hcont : ContinuousAt (fun p => (g.perturbationFamily h p).det) ((0 : ℝ), x) := by
    have hC : ContinuousAt (fun p => fun i j => g.perturbationFamily h p i j) ((0 : ℝ), x) :=
      continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
        (contDiffAt_perturbationFamily hh (p := ((0 : ℝ), x)) hx i j).continuousAt
    exact (MetricDensity.contDiff_matrix_det (r := 0)).continuous.continuousAt.comp
      (f := fun p => fun i j => g.perturbationFamily h p i j) hC
  have hU : ∀ᶠ p in 𝓝 ((0 : ℝ), x), p.2 ∈ U :=
    continuous_snd.continuousAt.preimage_mem_nhds (U.isOpen.mem_nhds hx)
  exact hU.and (hcont.eventually_ne hdet0)

theorem contDiffOn_christoffelDifferenceLow (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (l i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => g.christoffelDifferenceLow h z l i j) U := by
  unfold christoffelDifferenceLow
  exact ((((contDiffOn_partial (hh j l) _).add (contDiffOn_partial (hh l i) _)).sub
    (contDiffOn_partial (hh i j) _)).div_const 2).sub
    (ContDiffOn.sum fun b _ => (hh l b).mul (g.contDiffOn_christoffelOf b i j))

/-- The difference quotient is smooth in `(s, z)` where `g + s h` is invertible. -/
theorem contDiffAt_christoffelQuotient (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {p : ℝ × MinkowskiModel d} (hp : p.2 ∈ U) (hdet : (g.perturbationFamily h p).det ≠ 0)
    (k i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => g.christoffelQuotient h q k i j) p := by
  unfold christoffelQuotient
  refine ContDiffAt.sum fun l _ => ?_
  refine (contDiffAt_familyInv (fun a b => contDiffAt_perturbationFamily hh hp a b) hdet k l).mul
    ?_
  exact ((contDiffOn_christoffelDifferenceLow hh l i j).contDiffAt
    (U.isOpen.mem_nhds hp)).comp p contDiffAt_snd

/-- **The derivative of the difference quotient**: `∂_s E(0) = −g^{-1} h δΓ`. -/
theorem hasDerivAt_christoffelQuotient (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {z : MinkowskiModel d} (hz : z ∈ U) (k i j : Fin (d + 1)) :
    HasDerivAt (fun s => g.christoffelQuotient h (s, z) k i j)
      (-g.raiseContract h (g.curvedChristoffel h) z k i j) 0 := by
  set Gz := g.coefficient z
  have hent (a b : Fin (d + 1)) :
      HasDerivAt (fun s => g.perturbationFamily h (s, z) a b) (h z a b) 0 := by
    have e : (fun s => g.perturbationFamily h (s, z) a b) = fun s => Gz a b + s * h z a b :=
      funext fun s => g.perturbationFamily_apply h (s, z) a b
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (h z a b)).const_add (Gz a b)
  have hP : g.perturbationFamily h (0, z) = Gz := by simp [perturbationFamily, Gz]
  have hdet : (g.perturbationFamily h (0, z)).det ≠ 0 := by
    rw [hP]; exact g.coefficient_det_ne_zero ⟨z, hz⟩
  have hinv (l : Fin (d + 1)) : HasDerivAt (fun s => (g.perturbationFamily h (s, z))⁻¹ k l)
      (-(Gz⁻¹ * h z * Gz⁻¹) k l) 0 := by
    have := hasDerivAt_matrix_inv (M := fun s => g.perturbationFamily h (s, z)) hent hdet k l
    simpa only [hP] using this
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun l _ =>
    (hinv l).mul_const (g.christoffelDifferenceLow h z l i j)
  unfold christoffelQuotient
  convert hsum using 1
  -- the value of the derivative
  have hδ (m : Fin (d + 1)) : g.curvedChristoffel h z m i j =
      ∑ l, Gz⁻¹ m l * g.christoffelDifferenceLow h z l i j := by
    rw [← christoffelQuotient_zero hs hz m i j]
    unfold christoffelQuotient
    rw [hP]
  set X : Fin (d + 1) → ℝ := fun l => g.christoffelDifferenceLow h z l i j
  have e1 : ∑ l, -(Gz⁻¹ * h z * Gz⁻¹) k l * X l = -(Gz⁻¹ *ᵥ (h z *ᵥ (Gz⁻¹ *ᵥ X))) k := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, neg_mul, Finset.sum_neg_distrib]
  have e2 : g.raiseContract h (g.curvedChristoffel h) z k i j =
      (Gz⁻¹ *ᵥ (h z *ᵥ (Gz⁻¹ *ᵥ X))) k := by
    unfold raiseContract
    simp only [hδ, Matrix.mulVec, dotProduct, X, Gz]
  rw [e1, e2]

/-! ### The Ricci tensor of a connection `Γ + D` -/

/-- **The Ricci tensor of `Γ + D`**: if the Christoffel symbols of `C` are `Γ + D` near `x`,
`Ric(C) = Ric(g) + ∇_i D^i_{jk} − ∇_j D^i_{ik} + D^i_{ia} D^a_{jk} − D^i_{ja} D^a_{ik}`. -/
theorem ricciOf_eq_of_christoffel {C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {D : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U)
    (hC : ∀ᶠ z in 𝓝 x, ∀ k i j,
      christoffelOf C z k i j = christoffelOf g.coefficient z k i j + D z k i j)
    (hD : ∀ a b c, DifferentiableAt ℝ (fun z => D z a b c) x) (j k : Fin (d + 1)) :
    ricciOf C x j k = ricciOf g.coefficient x j k + g.palatini D x j k +
      christoffelQuadratic (D x) (D x) j k := by
  have hfd (a b c : Fin (d + 1)) (v : MinkowskiModel d) :
      fderiv ℝ (fun z => christoffelOf C z a b c) x v =
        fderiv ℝ (fun z => christoffelOf g.coefficient z a b c) x v +
          fderiv ℝ (fun z => D z a b c) x v := by
    rw [Filter.EventuallyEq.fderiv_eq (hC.mono fun z hz => hz a b c),
      fderiv_fun_add (differentiableAt_christoffelOf hx a b c) (hD a b c)]
    rfl
  have hval (a b c : Fin (d + 1)) :
      christoffelOf C x a b c = christoffelOf g.coefficient x a b c + D x a b c :=
    hC.self_of_nhds a b c
  have hsymΓ (a b c : Fin (d + 1)) : christoffelOf g.coefficient x a b c =
      christoffelOf g.coefficient x a c b := g.christoffelOf_coefficient_symm hx a b c
  set Γ := christoffelOf g.coefficient x
  unfold ricciOf palatini covDerivThree christoffelQuadratic
  simp only [hfd, hval]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have key : ∑ a, ((Γ i i a + D x i i a) * (Γ a j k + D x a j k) -
      (Γ i j a + D x i j a) * (Γ a i k + D x a i k)) =
      ∑ a, (Γ i i a * Γ a j k - Γ i j a * Γ a i k) +
        (∑ b, (Γ i i b * D x b j k - Γ b i j * D x i b k - Γ b i k * D x i j b) -
          ∑ b, (Γ i j b * D x b i k - Γ b j i * D x i b k - Γ b j k * D x i i b)) +
        ∑ a, (D x i i a * D x a j k - D x i j a * D x a i k) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hsymΓ b j i]
    ring
  rw [key]
  ring

/-- The quadratic part is homogeneous of degree two. -/
theorem christoffelQuadratic_smul {n : ℕ} (c : ℝ) (P : Fin n → Fin n → Fin n → ℝ) (j k : Fin n) :
    christoffelQuadratic (c • P) (c • P) j k = c ^ 2 * christoffelQuadratic P P j k := by
  unfold christoffelQuadratic
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring

/-- The Palatini form is linear under a constant factor. -/
theorem palatini_const_smul (c : ℝ)
    {P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hP : ∀ a b e, DifferentiableAt ℝ (fun z => P z a b e) x) (j k : Fin (d + 1)) :
    g.palatini (fun z => c • P z) x j k = c * g.palatini P x j k := by
  have h := palatini_smul (g := g) (f := fun _ => c) (differentiableAt_const c) hP j k
  have h0 (i : Fin (d + 1)) : gradientCovector (fun _ : MinkowskiModel d => c) x i = 0 := by
    simp [gradientCovector]
  simpa [h0] using h

/-- The Palatini form changes sign with its argument. -/
theorem palatini_neg {P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hP : ∀ a b e, DifferentiableAt ℝ (fun z => P z a b e) x)
    (j k : Fin (d + 1)) :
    g.palatini (fun z => -P z) x j k = -g.palatini P x j k := by
  have h := palatini_const_smul (g := g) (-1) hP j k
  simpa using h

/-! ### A second derivative -/

/-- The second derivative at `0` of `c + s p(s) + s² q(s)` for `C²` functions `p, q`. -/
theorem hasDerivAt_deriv_mul_add {p q : ℝ → ℝ} (hp : ContDiffAt ℝ 2 p 0)
    (hq : ContDiffAt ℝ 2 q 0) (c : ℝ) :
    HasDerivAt (deriv (fun s => c + s * p s + s ^ 2 * q s)) (2 * deriv p 0 + 2 * q 0) 0 := by
  have hpd : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ p s :=
    (hp.eventually (by simp)).mono fun s hs => hs.differentiableAt (by simp)
  have hqd : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ q s :=
    (hq.eventually (by simp)).mono fun s hs => hs.differentiableAt (by simp)
  have hderiv : deriv (fun s => c + s * p s + s ^ 2 * q s) =ᶠ[𝓝 0]
      fun s => p s + s * deriv p s + (2 * s * q s + s ^ 2 * deriv q s) := by
    filter_upwards [hpd, hqd] with s hps hqs
    have h1 : HasDerivAt (fun s => s * p s) (1 * p s + s * deriv p s) s :=
      (hasDerivAt_id s).mul hps.hasDerivAt
    have h2 : HasDerivAt (fun s => s ^ 2 * q s)
        ((↑2 * s ^ (2 - 1) * 1) * q s + s ^ 2 * deriv q s) s :=
      ((hasDerivAt_id s).pow 2).mul hqs.hasDerivAt
    have h3 := ((hasDerivAt_const s c).fun_add h1).fun_add h2
    rw [h3.deriv]
    simp only [Nat.add_one_sub_one, pow_one, mul_one, one_mul, zero_add]
  have hdp : DifferentiableAt ℝ (deriv p) 0 := by
    have h := (hp.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := (1 : ℝ)))
    exact h.differentiableAt (by simp)
  have hdq : DifferentiableAt ℝ (deriv q) 0 := by
    have h := (hq.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := (1 : ℝ)))
    exact h.differentiableAt (by simp)
  have hp0 : HasDerivAt p (deriv p 0) 0 := (hp.differentiableAt (by simp)).hasDerivAt
  have hq0 : HasDerivAt q (deriv q 0) 0 := (hq.differentiableAt (by simp)).hasDerivAt
  have hG := (hp0.add ((hasDerivAt_id (0 : ℝ)).mul hdp.hasDerivAt)).add
    ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul hq0).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul hdq.hasDerivAt))
  refine (hG.congr_of_eventuallyEq hderiv).congr_deriv ?_
  simp
  ring

/-! ### The second variation -/

/-- The first-order coefficient `p(s) = ∇_i E(s)^i_{jk} − ∇_j E(s)^i_{ik}`. -/
def secondVariationLinear (g : CoordinateMetric σ d U)
    (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) (s : ℝ) : ℝ :=
  g.palatini (fun z => g.christoffelQuotient h (s, z)) x j k

/-- The second-order coefficient `q(s) = E(s)^i_{ia} E(s)^a_{jk} − E(s)^i_{ja} E(s)^a_{ik}`. -/
def secondVariationQuadratic (g : CoordinateMetric σ d U)
    (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) (s : ℝ) : ℝ :=
  christoffelQuadratic (g.christoffelQuotient h (s, x)) (g.christoffelQuotient h (s, x)) j k

/-- **The Ricci tensor along the family**: near `s = 0`,
`Ric(g + s h) = Ric(g) + s p(s) + s² q(s)`. -/
theorem eventually_ricciOf_perturbation (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    (fun s : ℝ => ricciOf (fun z => g.coefficient z + s • h z) x j k) =ᶠ[𝓝 0]
      fun s => ricciOf g.coefficient x j k + s * g.secondVariationLinear h x j k s +
        s ^ 2 * g.secondVariationQuadratic h x j k s := by
  have hW := (eventually_perturbationFamily (g := g) hh hx).curry_nhds
  filter_upwards [hW] with s hs
  have hsx : (s, x).2 ∈ U ∧ (g.perturbationFamily h (s, x)).det ≠ 0 := hs.self_of_nhds
  have hC : ∀ᶠ z in 𝓝 x, ∀ k i j, christoffelOf (fun y => g.coefficient y + s • h y) z k i j =
      christoffelOf g.coefficient z k i j +
        (fun z k i j => s * g.christoffelQuotient h (s, z) k i j) z k i j := by
    filter_upwards [hs] with z hz
    exact fun k i j => christoffelOf_perturbation_eq hh hz.1 hz.2 k i j
  have hE (a b c : Fin (d + 1)) :
      DifferentiableAt ℝ (fun z => g.christoffelQuotient h (s, z) a b c) x := by
    have h1 := (contDiffAt_christoffelQuotient (g := g) hh hsx.1 hsx.2 a b c).differentiableAt
      (by simp)
    exact h1.comp x ((differentiableAt_const s).prodMk differentiableAt_id)
  have hD (a b c : Fin (d + 1)) :
      DifferentiableAt ℝ (fun z => s * g.christoffelQuotient h (s, z) a b c) x :=
    (hE a b c).const_mul s
  rw [ricciOf_eq_of_christoffel hx hC hD]
  have hpal : g.palatini (fun z k i j => s * g.christoffelQuotient h (s, z) k i j) x j k =
      s * g.secondVariationLinear h x j k s := by
    have := palatini_const_smul (g := g) s (P := fun z => g.christoffelQuotient h (s, z)) hE j k
    exact this
  have hq : christoffelQuadratic (fun k i j => s * g.christoffelQuotient h (s, x) k i j)
      (fun k i j => s * g.christoffelQuotient h (s, x) k i j) j k =
      s ^ 2 * g.secondVariationQuadratic h x j k s :=
    christoffelQuadratic_smul s _ j k
  rw [hpal, hq]

theorem contDiffAt_secondVariationLinear (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (g.secondVariationLinear h x j k) 0 := by
  have hdet : (g.perturbationFamily h ((0 : ℝ), x)).det ≠ 0 := by
    simpa [perturbationFamily] using g.coefficient_det_ne_zero ⟨x, hx⟩
  have hΦ (a b c : Fin (d + 1)) := contDiffAt_christoffelQuotient (g := g) hh
    (p := ((0 : ℝ), x)) hx hdet a b c
  have hpath : ContDiffAt ℝ ∞ (fun s : ℝ => (s, x)) 0 := contDiffAt_id.prodMk contDiffAt_const
  have hval (a b c : Fin (d + 1)) :
      ContDiffAt ℝ ∞ (fun s : ℝ => g.christoffelQuotient h (s, x) a b c) 0 := by
    have := (hΦ a b c).comp (0 : ℝ) hpath
    exact this
  have hder (a b c : Fin (d + 1)) (v : MinkowskiModel d) :
      ContDiffAt ℝ ∞ (fun s : ℝ =>
        fderiv ℝ (fun z => g.christoffelQuotient h (s, z) a b c) x v) 0 := by
    have := (contDiffAt_fderiv_snd (hΦ a b c) v).comp (0 : ℝ) hpath
    exact this
  unfold secondVariationLinear palatini covDerivThree
  refine ContDiffAt.sum fun i _ => ?_
  refine ((hder i j k _).add (ContDiffAt.sum fun b _ => ?_)).sub
    ((hder i i k _).add (ContDiffAt.sum fun b _ => ?_))
  · exact ((contDiffAt_const.mul (hval b j k)).sub (contDiffAt_const.mul (hval i b k))).sub
      (contDiffAt_const.mul (hval i j b))
  · exact ((contDiffAt_const.mul (hval b i k)).sub (contDiffAt_const.mul (hval i b k))).sub
      (contDiffAt_const.mul (hval i i b))

theorem contDiffAt_secondVariationQuadratic (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (g.secondVariationQuadratic h x j k) 0 := by
  have hdet : (g.perturbationFamily h ((0 : ℝ), x)).det ≠ 0 := by
    simpa [perturbationFamily] using g.coefficient_det_ne_zero ⟨x, hx⟩
  have hpath : ContDiffAt ℝ ∞ (fun s : ℝ => (s, x)) 0 := contDiffAt_id.prodMk contDiffAt_const
  have hval (a b c : Fin (d + 1)) :
      ContDiffAt ℝ ∞ (fun s : ℝ => g.christoffelQuotient h (s, x) a b c) 0 := by
    have := (contDiffAt_christoffelQuotient (g := g) hh (p := ((0 : ℝ), x)) hx hdet a b c).comp
      (0 : ℝ) hpath
    exact this
  unfold secondVariationQuadratic christoffelQuadratic
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun a _ =>
    ((hval i i a).mul (hval a j k)).sub ((hval i j a).mul (hval a i k))

/-- The derivative of the first-order coefficient: `p'(0) = −∇·(g^{-1} h δΓ)`. -/
theorem hasDerivAt_secondVariationLinear (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    HasDerivAt (g.secondVariationLinear h x j k)
      (-g.palatini (g.raiseContract h (g.curvedChristoffel h)) x j k) 0 := by
  have hdet : (g.perturbationFamily h ((0 : ℝ), x)).det ≠ 0 := by
    simpa [perturbationFamily] using g.coefficient_det_ne_zero ⟨x, hx⟩
  have hΦ (a b c : Fin (d + 1)) := contDiffAt_christoffelQuotient (g := g) hh
    (p := ((0 : ℝ), x)) hx hdet a b c
  set R := g.raiseContract h (g.curvedChristoffel h)
  -- the derivative in `s` of `E(s, z)` at `0` is `−R(z)` near `x`
  have hslice (a b c : Fin (d + 1)) :
      (fun z => fderiv ℝ (fun q => g.christoffelQuotient h q a b c) ((0 : ℝ), z) (1, 0)) =ᶠ[𝓝 x]
        fun z => -R z a b c := by
    have hev := ((hΦ a b c).of_le (m := 1) (by simp)).eventually (by simp)
    have hev' : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ 1 (fun q => g.christoffelQuotient h q a b c)
        ((0 : ℝ), z) := by
      have hc : Tendsto (fun z : MinkowskiModel d => ((0 : ℝ), z)) (𝓝 x) (𝓝 ((0 : ℝ), x)) :=
        (continuous_const.prodMk continuous_id).tendsto' _ _ (by simp)
      exact hc.eventually hev
    filter_upwards [hev', U.isOpen.mem_nhds hx] with z hz hzU
    exact (hasDerivAt_slice (hz.differentiableAt (by simp))).unique
      (hasDerivAt_christoffelQuotient hs hzU a b c)
  have hder (a b c : Fin (d + 1)) (v : MinkowskiModel d) :
      HasDerivAt (fun s : ℝ => fderiv ℝ (fun z => g.christoffelQuotient h (s, z) a b c) x v)
        (fderiv ℝ (fun z => -R z a b c) x v) 0 := by
    have h1 := hasDerivAt_fderiv_slice (hΦ a b c) v
    rwa [Filter.EventuallyEq.fderiv_eq (hslice a b c)] at h1
  have hval (a b c : Fin (d + 1)) :
      HasDerivAt (fun s : ℝ => g.christoffelQuotient h (s, x) a b c) (-R x a b c) 0 :=
    hasDerivAt_christoffelQuotient hs hx a b c
  have hRd (a b c : Fin (d + 1)) : DifferentiableAt ℝ (fun z => R z a b c) x := by
    have hδ (m : Fin (d + 1)) : DifferentiableAt ℝ (fun z => g.curvedChristoffel h z m b c) x :=
      differentiableAt_of_contDiffOn (contDiffOn_curvedChristoffel hh m b c) hx
    exact DifferentiableAt.fun_sum fun l _ => (differentiableAt_coefficient_inv hx a l).fun_mul
      (DifferentiableAt.fun_sum fun m _ =>
        (differentiableAt_of_contDiffOn (hh l m) hx).fun_mul (hδ m))
  rw [← palatini_neg hRd]
  unfold secondVariationLinear palatini covDerivThree
  refine HasDerivAt.fun_sum fun i _ => ?_
  refine ((hder i j k _).add (HasDerivAt.fun_sum fun b _ => ?_)).sub
    ((hder i i k _).add (HasDerivAt.fun_sum fun b _ => ?_))
  · exact ((((hval b j k).const_mul _).sub ((hval i b k).const_mul _)).sub
      ((hval i j b).const_mul _))
  · exact ((((hval b i k).const_mul _).sub ((hval i b k).const_mul _)).sub
      ((hval i i b).const_mul _))

/-- The value `q(0) = δΓ^i_{ia} δΓ^a_{jk} − δΓ^i_{ja} δΓ^a_{ik}`. -/
theorem secondVariationQuadratic_zero (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    g.secondVariationQuadratic h x j k 0 =
      christoffelQuadratic (g.curvedChristoffel h x) (g.curvedChristoffel h x) j k := by
  unfold secondVariationQuadratic
  have e : g.christoffelQuotient h (0, x) = g.curvedChristoffel h x :=
    funext fun a => funext fun b => funext fun c => christoffelQuotient_zero hs hx a b c
  rw [e]

/-- The Ricci tensor of `g + s h` is differentiable in `s` near `0`. -/
theorem eventually_differentiableAt_ricciOf_perturbation
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ (fun s : ℝ => ricciOf (fun z => g.coefficient z + s • h z) x j k) s := by
  have hp := contDiffAt_secondVariationLinear (g := g) hh hx j k
  have hq := contDiffAt_secondVariationQuadratic (g := g) hh hx j k
  have hev := eventually_ricciOf_perturbation (g := g) hh hx j k
  have hF : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun s => ricciOf g.coefficient x j k +
      s * g.secondVariationLinear h x j k s + s ^ 2 * g.secondVariationQuadratic h x j k s) s := by
    filter_upwards [(hp.of_le (m := 1) (by simp)).eventually (by simp),
      (hq.of_le (m := 1) (by simp)).eventually (by simp)] with s hps hqs
    exact ((differentiableAt_const _).add (differentiableAt_id.mul
      (hps.differentiableAt (by simp)))).add
      ((differentiableAt_id.pow 2).mul (hqs.differentiableAt (by simp)))
  filter_upwards [hev.eventually_nhds, hF] with s hs hFs
  exact hFs.congr_of_eventuallyEq hs

/-- **The second variation of the Ricci tensor** (target of §108): the derivative at `s = 0`
of `s ↦ d/ds Ric(g + s h)` is `secondRicci g h`. -/
theorem hasDerivAt_deriv_ricciOf_perturbation (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    HasDerivAt (deriv fun s : ℝ => ricciOf (fun z => g.coefficient z + s • h z) x j k)
      (g.secondRicci h x j k) 0 := by
  have hp := contDiffAt_secondVariationLinear (g := g) hh hx j k
  have hq := contDiffAt_secondVariationQuadratic (g := g) hh hx j k
  have hev := eventually_ricciOf_perturbation (g := g) hh hx j k
  have h2 := hasDerivAt_deriv_mul_add (hp.of_le (by simp)) (hq.of_le (by simp))
    (ricciOf g.coefficient x j k)
  rw [(hasDerivAt_secondVariationLinear hh hs hx j k).deriv,
    secondVariationQuadratic_zero hs hx] at h2
  have hd : deriv (fun s : ℝ => ricciOf (fun z => g.coefficient z + s • h z) x j k) =ᶠ[𝓝 0]
      deriv (fun s => ricciOf g.coefficient x j k + s * g.secondVariationLinear h x j k s +
        s ^ 2 * g.secondVariationQuadratic h x j k s) := hev.deriv
  refine (h2.congr_of_eventuallyEq hd).congr_deriv ?_
  unfold secondRicci
  ring

theorem deriv_deriv_ricciOf_perturbation (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    deriv (deriv fun s : ℝ => ricciOf (fun z => g.coefficient z + s • h z) x j k) 0 =
      g.secondRicci h x j k :=
  (hasDerivAt_deriv_ricciOf_perturbation hh hs hx j k).deriv

end ProjectAinos.SmoothGeometry.CoordinateMetric
