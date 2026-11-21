/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateConservation
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateKilling
public import ProjectAinos.SmoothGeometry.Lorentzian.ChristoffelCertificate
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateFirstVariation
public import ProjectAinos.SmoothGeometry.Lorentzian.CurvatureSymmetry

/-!
# The Christoffel symbols and the curvature of a coordinate metric as multilinear maps

For a metric given by coefficients on an open set `U` of the model space:

* `CoordinateMetric.chr`: the Christoffel symbols as a smooth bilinear map,
  `Γ(z)(a, b)^k = Γ^k_{ij}(z) a^i b^j`; `chr_symm`, `fderiv_chr_symm`: it and its derivative are
  symmetric; `fderiv_form_apply`: **metric compatibility**,
  `∂_v g(a, b) = g(Γ(v, a), b) + g(a, Γ(v, b))`.
* `CoordinateMetric.curv`: the curvature
  `R(a, b)c = (∂_a Γ)(b, c) − (∂_b Γ)(a, c) + Γ(a, Γ(b, c)) − Γ(b, Γ(a, c))`, whose components are
  `curvatureOf (christoffelOf C)` (`curv_single`) and which is the native curvature tensor
  (`toLorentzMetric_curvature`); `curv_pair_swap`: `g(R(a, b)c, e) = −g(R(a, b)e, c)`;
  `ricciOf_eq_sum_curv`: `Ric(u, u) = Σ_i (R(e_i, u)u)^i`.
* `CoordinateMetric.hasDerivAt_form_along`, `CoordinateMetric.hasDerivAt_chr_along`: the
  derivatives of `g(X, Y)` and `Γ(X, Y)` along a curve, with metric compatibility built in.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

local notation "E" => MinkowskiModel d

/-- Instance search does not find this one by itself. -/
local instance : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] E) :=
  @NormedSpace.toIsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] E) _ _ _

/-! ### Multilinear maps on the model space -/

/-- A trilinear map is determined by its values on the standard basis. -/
theorem clm3_sum {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] F) (v a b : E) :
    T v a b = ∑ p, ∑ i, ∑ j, (v p * a i * b j) •
      T (Pi.single p 1) (Pi.single i 1) (Pi.single j 1) := by
  have hv : T v = ∑ p, v p • T (Pi.single p 1) := by
    conv_lhs => rw [pi_eq_sum_univ' v]
    rw [map_sum]
    simp only [map_smul]
  have ha (p : Fin (d + 1)) :
      T (Pi.single p 1) a = ∑ i, a i • T (Pi.single p 1) (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' a]
    rw [map_sum]
    simp only [map_smul]
  have hb (p i : Fin (d + 1)) : T (Pi.single p 1) (Pi.single i 1) b =
      ∑ j, b j • T (Pi.single p 1) (Pi.single i 1) (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ' b]
    rw [map_sum]
    simp only [map_smul]
  rw [hv]
  simp only [sum_apply, smul_apply, ha, hb, Finset.smul_sum, smul_smul, mul_assoc]

/-- The bilinear map `(a, b) ↦ a^i b^j e_k`. -/
def elemBilin (k i j : Fin (d + 1)) : E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) i).smulRight
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) j).smulRight
      (Pi.single k 1 : E))

theorem elemBilin_apply (k i j : Fin (d + 1)) (a b : E) (l : Fin (d + 1)) :
    elemBilin k i j a b l = if l = k then a i * b j else 0 := by
  simp only [elemBilin, smulRight_apply, proj_apply, smul_apply, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul]
  split_ifs <;> ring

/-! ### The Christoffel symbols -/

variable (g : CoordinateMetric σ d U)

/-- **The Christoffel symbols as a bilinear map**, `Γ(z)(a, b)^k = Γ^k_{ij}(z) a^i b^j`. -/
def chr (z : E) : E →L[ℝ] E →L[ℝ] E :=
  ∑ k, ∑ i, ∑ j, christoffelOf g.coefficient z k i j • elemBilin k i j

theorem chr_apply (z a b : E) (l : Fin (d + 1)) :
    g.chr z a b l = ∑ i, ∑ j, christoffelOf g.coefficient z l i j * a i * b j := by
  simp only [chr, sum_apply, smul_apply, Finset.sum_apply, Pi.smul_apply, elemBilin_apply,
    smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single l (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  simp only [ite_true]
  ring

theorem chr_single_left (z Y : E) (i l : Fin (d + 1)) :
    g.chr z (Pi.single i 1) Y l = ∑ j, christoffelOf g.coefficient z l i j * Y j := by
  rw [chr_apply]
  simp [Pi.single_apply]

theorem chr_single (z : E) (p i : Fin (d + 1)) :
    g.chr z (Pi.single p 1) (Pi.single i 1) = fun l => christoffelOf g.coefficient z l p i := by
  funext l
  rw [chr_apply]
  simp [Pi.single_apply]

theorem contDiffOn_chr : ContDiffOn ℝ ∞ g.chr U := by
  unfold chr
  exact ContDiffOn.sum fun k _ => ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    (g.contDiffOn_christoffelOf k i j).smul contDiffOn_const

/-- The derivative of the Christoffel symbols. -/
theorem fderiv_chr_apply {z : E} (hz : z ∈ U) (v a b : E) (l : Fin (d + 1)) :
    fderiv ℝ g.chr z v a b l =
      ∑ i, ∑ j, fderiv ℝ (fun w => christoffelOf g.coefficient w l i j) z v * a i * b j := by
  have hD : HasFDerivAt g.chr (fderiv ℝ g.chr z) z :=
    ((g.contDiffOn_chr.contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have h1 := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) l).hasFDerivAt.comp
    z ((hD.clm_apply (hasFDerivAt_const a z)).clm_apply (hasFDerivAt_const b z)))
  have hd (i j : Fin (d + 1)) :
      HasFDerivAt (fun w => christoffelOf g.coefficient w l i j)
        (fderiv ℝ (fun w => christoffelOf g.coefficient w l i j) z) z :=
    (((g.contDiffOn_christoffelOf l i j).contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt
      (by simp)).hasFDerivAt
  have h2 : HasFDerivAt (fun w => ∑ i, ∑ j, christoffelOf g.coefficient w l i j * a i * b j)
      (∑ i, ∑ j, (a i * b j) • fderiv ℝ (fun w => christoffelOf g.coefficient w l i j) z) z := by
    refine HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => ?_
    have h := (hd i j).mul_const (a i * b j)
    simp only [mul_assoc] at h ⊢
    exact h
  have heq : (fun w => ∑ i, ∑ j, christoffelOf g.coefficient w l i j * a i * b j) =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ) l) ∘
        fun w => g.chr w a b := by
    funext w
    simp only [Function.comp_apply, proj_apply, chr_apply]
  rw [heq] at h2
  have h3 := h1.unique h2
  have h4 := congrArg (fun L : E →L[ℝ] ℝ => L v) h3
  simp only [comp_apply, proj_apply, sum_apply, smul_apply,
    smul_eq_mul, comp_zero, zero_add, flip_apply] at h4
  rw [show fderiv ℝ g.chr z v a b l = _ from h4]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The Christoffel symbols are symmetric**: `Γ(a, b) = Γ(b, a)`. -/
theorem chr_symm {z : E} (hz : z ∈ U) (a b : E) : g.chr z a b = g.chr z b a := by
  funext l
  rw [chr_apply, chr_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [g.christoffelOf_coefficient_symm hz]
  ring

/-- **The derivative of the Christoffel symbols is symmetric** in its two arguments. -/
theorem fderiv_chr_symm {z : E} (hz : z ∈ U) (v a b : E) :
    fderiv ℝ g.chr z v a b = fderiv ℝ g.chr z v b a := by
  funext l
  rw [g.fderiv_chr_apply hz, g.fderiv_chr_apply hz, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : (fun w => christoffelOf g.coefficient w l j i) =ᶠ[𝓝 z]
      fun w => christoffelOf g.coefficient w l i j :=
    eventually_of_mem (U.isOpen.mem_nhds hz) fun w hw => g.christoffelOf_coefficient_symm hw l j i
  rw [h.fderiv_eq]
  ring

/-- The metric is symmetric. -/
theorem form_comm {z : E} (hz : z ∈ U) (a b : E) : g.form z a b = g.form z b a := by
  obtain ⟨e, he⟩ := g.signature z hz
  rw [he, he, minkowskiForm_symmetric]

/-- The metric on a basis vector: `g(X, e_j) = C_{lj} X^l`. -/
theorem form_single_right' (z X : E) (j : Fin (d + 1)) :
    g.form z X (Pi.single j 1) = ∑ l, g.coefficient z l j * X l := g.form_single_right z X j

theorem fderiv_form_single {z : E} (hz : z ∈ U) (p i j : Fin (d + 1)) :
    fderiv ℝ g.form z (Pi.single p 1) (Pi.single i 1) (Pi.single j 1) =
      fderiv ℝ (fun w => g.coefficient w i j) z (Pi.single p 1) := by
  have hF : HasFDerivAt g.form (fderiv ℝ g.form z) z :=
    ((g.smooth.contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have h := (hF.clm_apply (hasFDerivAt_const (Pi.single i 1 : E) z)).clm_apply
    (hasFDerivAt_const (Pi.single j 1 : E) z)
  have hc : (fun w => g.coefficient w i j) = fun w => g.form w (Pi.single i 1) (Pi.single j 1) :=
    funext fun w => rfl
  rw [hc, h.fderiv]
  simp

/-- **Metric compatibility**: `∂_v g(a, b) = g(Γ(v, a), b) + g(a, Γ(v, b))`. -/
theorem fderiv_form_apply {z : E} (hz : z ∈ U) (v a b : E) :
    fderiv ℝ g.form z v a b = g.form z (g.chr z v a) b + g.form z a (g.chr z v b) := by
  let T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := (compL ℝ E E (E →L[ℝ] ℝ) (g.form z)).comp (g.chr z)
  have hT (v a b : E) : T v a b = g.form z (g.chr z v a) b := rfl
  have h2 : g.form z a (g.chr z v b) = T v b a := by
    rw [hT, g.form_comm hz]
  rw [← hT, h2, clm3_sum (fderiv ℝ g.form z), clm3_sum T v a b, clm3_sum T v b a]
  conv_rhs => arg 2; arg 2; ext p; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_form_single g hz, fderiv_coefficient (g := g) hz, hT, hT, chr_single, chr_single,
    form_single_right', form_single_right']
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [g.coefficient_symmetric hz i l]
  ring

/-! ### The curvature -/

/-- **The curvature** `R(a, b)c = (∂_a Γ)(b, c) − (∂_b Γ)(a, c) + Γ(a, Γ(b, c)) − Γ(b, Γ(a, c))`. -/
def curv (z a b c : E) : E :=
  fderiv ℝ g.chr z a b c - fderiv ℝ g.chr z b a c + g.chr z a (g.chr z b c) -
    g.chr z b (g.chr z a c)

@[simp] theorem curv_self (z a b : E) : g.curv z a a b = 0 := by
  rw [curv]
  abel

/-- The composition `(a, b, c) ↦ Γ(a, Γ(b, c))` as a trilinear map. -/
def chrComp (z : E) : E →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  (compL ℝ E E E).bilinearComp (g.chr z) (g.chr z)

theorem chrComp_apply (z a b c : E) : g.chrComp z a b c = g.chr z a (g.chr z b c) := rfl

/-- **The curvature is trilinear**: it is determined by its components. -/
theorem curv_expand (z a b c : E) :
    g.curv z a b c = ∑ p, ∑ i, ∑ j, (a p * b i * c j) •
      g.curv z (Pi.single p 1) (Pi.single i 1) (Pi.single j 1) := by
  have h1 := clm3_sum (F := E) (fderiv ℝ g.chr z) a b c
  have h2 := clm3_sum (F := E) (fderiv ℝ g.chr z) b a c
  have h3 := clm3_sum (F := E) (g.chrComp z) a b c
  have h4 := clm3_sum (F := E) (g.chrComp z) b a c
  rw [chrComp_apply] at h3 h4
  simp only [chrComp_apply] at h3 h4
  rw [Finset.sum_comm] at h2 h4
  simp only [curv, h1, h2, h3, h4, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, smul_sub,
    smul_add]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  rw [show b i * a p * c j = a p * b i * c j by ring]

/-- The components of the curvature are `curvatureOf (christoffelOf C)`. -/
theorem curv_single {z : E} (hz : z ∈ U) (l i j k : Fin (d + 1)) :
    g.curv z (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) l =
      curvatureOf (christoffelOf g.coefficient) z l i j k := by
  simp only [curv, Pi.sub_apply, Pi.add_apply, g.fderiv_chr_apply hz, chr_single,
    chr_single_left, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, curvatureOf]
  rw [Finset.sum_sub_distrib]
  ring

/-- **The curvature of the coefficients is the native curvature tensor.** -/
theorem toLorentzMetric_curvature (y : U) (a b c : E) :
    (g.toLorentzMetric.curvature y a b c : E) = g.curv y a b c := by
  have h1 := clm3_sum (F := E) (g.toLorentzMetric.curvature y) a b c
  refine h1.trans ?_
  rw [g.curv_expand]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  congr 1
  funext l
  rw [g.curv_single y.2]
  have h := g.toLorentzMetric_chartCurvature y y l p i j
  rw [LorentzMetric.chartCurvature, physicalChart_tangentMap, physicalChart_chartField,
    physicalChart_chartField, physicalChart_chartField] at h
  exact h

/-- **The lowered curvature is antisymmetric in its last pair**:
`g(R(a, b)c, e) = −g(R(a, b)e, c)`. -/
theorem curv_pair_swap {z : E} (hz : z ∈ U) (a b c e : E) :
    g.form z (g.curv z a b c) e = -g.form z (g.curv z a b e) c := by
  have h := g.toLorentzMetric.curvature_pair_swap ⟨z, hz⟩ a b c e
  have h1 := g.toLorentzMetric_curvature ⟨z, hz⟩ a b c
  have h2 := g.toLorentzMetric_curvature ⟨z, hz⟩ a b e
  change g.form z _ e = -g.form z _ c at h
  rw [← h1, ← h2]
  exact h

/-- **The Ricci tensor is the trace of the curvature**: `Ric(u, u) = Σ_i (R(e_i, u)u)^i`. -/
theorem ricciOf_eq_sum_curv {z : E} (hz : z ∈ U) (u : E) :
    ∑ j, ∑ k, ricciOf g.coefficient z j k * u j * u k = ∑ i, g.curv z (Pi.single i 1) u u i := by
  have h (i : Fin (d + 1)) : g.curv z (Pi.single i 1) u u i =
      ∑ j, ∑ k, curvatureOf (christoffelOf g.coefficient) z i i j k * u j * u k := by
    rw [g.curv_expand z (Pi.single i 1) u u]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, g.curv_single hz, Pi.single_apply]
    rw [Finset.sum_eq_single i (fun p _ hp => by simp [hp]) (by simp)]
    simp only [ite_true, one_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp only [show ∀ j k, ricciOf g.coefficient z j k =
    ∑ i, curvatureOf (christoffelOf g.coefficient) z i i j k from fun j k => rfl, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]

/-! ### Derivatives along a curve -/

/-- **The derivative of `g(X, Y)` along a curve**, with metric compatibility:
`(g(X, Y))' = g(Γ(γ', X) + X', Y) + g(X, Γ(γ', Y) + Y')`. -/
theorem hasDerivAt_form_along {γ X Y : ℝ → E} {γ' X' Y' : E} {t : ℝ} (hγt : γ t ∈ U)
    (hγ : HasDerivAt γ γ' t) (hX : HasDerivAt X X' t) (hY : HasDerivAt Y Y' t) :
    HasDerivAt (fun t => g.form (γ t) (X t) (Y t))
      (g.form (γ t) (g.chr (γ t) γ' (X t) + X') (Y t) +
        g.form (γ t) (X t) (g.chr (γ t) γ' (Y t) + Y')) t := by
  have hF := ((g.smooth.contDiffAt (U.isOpen.mem_nhds hγt)).differentiableAt (by simp)).hasFDerivAt
  have h00 := hF.comp_hasDerivAt t hγ
  have h0 : HasDerivAt (fun t => g.form (γ t)) (fderiv ℝ g.form (γ t) γ') t := h00
  have h1 : HasDerivAt (fun t => g.form (γ t) (X t))
      (fderiv ℝ g.form (γ t) γ' (X t) + g.form (γ t) X') t := h0.clm_apply hX
  have h2 : HasDerivAt (fun t => g.form (γ t) (X t) (Y t))
      ((fderiv ℝ g.form (γ t) γ' (X t) + g.form (γ t) X') (Y t) +
        g.form (γ t) (X t) Y') t := h1.clm_apply hY
  refine h2.congr_deriv ?_
  rw [add_apply, g.fderiv_form_apply hγt, map_add, map_add, add_apply]
  ring

/-- **The derivative of `Γ(X, Y)` along a curve**:
`(Γ(X, Y))' = (∂_{γ'} Γ)(X, Y) + Γ(X', Y) + Γ(X, Y')`. -/
theorem hasDerivAt_chr_along {γ X Y : ℝ → E} {γ' X' Y' : E} {t : ℝ} (hγt : γ t ∈ U)
    (hγ : HasDerivAt γ γ' t) (hX : HasDerivAt X X' t) (hY : HasDerivAt Y Y' t) :
    HasDerivAt (fun t => g.chr (γ t) (X t) (Y t))
      (fderiv ℝ g.chr (γ t) γ' (X t) (Y t) + g.chr (γ t) X' (Y t) + g.chr (γ t) (X t) Y') t := by
  have hF := ((g.contDiffOn_chr.contDiffAt (U.isOpen.mem_nhds hγt)).differentiableAt
    (by simp)).hasFDerivAt
  have h00 := hF.comp_hasDerivAt t hγ
  have h0 : HasDerivAt (fun t => g.chr (γ t)) (fderiv ℝ g.chr (γ t) γ') t := h00
  have h1 : HasDerivAt (fun t => g.chr (γ t) (X t))
      (fderiv ℝ g.chr (γ t) γ' (X t) + g.chr (γ t) X') t := h0.clm_apply hX
  have h2 : HasDerivAt (fun t => g.chr (γ t) (X t) (Y t))
      ((fderiv ℝ g.chr (γ t) γ' (X t) + g.chr (γ t) X') (Y t) +
        g.chr (γ t) (X t) Y') t := h1.clm_apply hY
  refine h2.congr_deriv ?_
  rw [add_apply]

end ProjectAinos.SmoothGeometry.CoordinateMetric
