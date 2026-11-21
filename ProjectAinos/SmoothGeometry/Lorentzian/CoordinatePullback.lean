/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateEinsteinEquation
public import ProjectAinos.SmoothGeometry.Lorentzian.CurvatureNaturality
public import ProjectAinos.SmoothGeometry.Manifold.OpenTangent

/-!
# The Einstein tensor of coordinate metrics under a change of co-ordinates

Let `g` be a coordinate metric on an open set `V` and `F` a smooth map from an open set `U` into
`V`. A coordinate metric `g'` on `U` is the **pullback** of `g` by `F` when
`g'(x)(v, w) = g(F x)(DF v, DF w)` at every point of `U`.

* `restrictMap`, `contMDiff_restrictMap`, `mfderiv_restrictMap`: the map `U → V` of the open
  submanifolds, smooth, with the manifold derivative `DF`.
* `einsteinOf_pullback`: **the Einstein tensor transforms as a covariant two-tensor**,
  `G'_{ik}(x) = G_{ab}(F x) ∂_i F^a ∂_k F^b`. It follows from the naturality of the native curvature
  (`LorentzMetric.curvature_naturality_of_metric`), of the Ricci tensor and of the scalar
  curvature, and from the identification of the native Einstein tensor in the inclusion charts
  with `einsteinOf` (`toLorentzMetric_einstein_chartField`).
* `coefficient_pullback`: `g'_{ik}(x) = g_{ab}(F x) ∂_i F^a ∂_k F^b`.
* `IsEinstein.pullback`: the Einstein equations `G + Λg = κT` hold for the pullback with the
  pulled-back tensor `T'_{ik} = T_{ab}(F x) ∂_i F^a ∂_k F^b` (`pullbackTensor`).
* `pullback`, `pullback_form_apply`, `IsEinstein.pullback_metric`: the pullback of a coordinate
  metric by a smooth map with invertible derivative is a coordinate metric, and solves the
  pulled-back Einstein equations.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U V : Opens (MinkowskiModel d)}

/-- The map `F` as a map `U → V` of open submanifolds of the model. -/
def restrictMap (F : MinkowskiModel d → MinkowskiModel d) (hF : MapsTo F U V) (x : U) : V :=
  ⟨F x, hF x.2⟩

theorem contMDiff_restrictMap {F : MinkowskiModel d → MinkowskiModel d}
    (hF : ContDiffOn ℝ ∞ F U) (hm : MapsTo F U V) :
    ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ (restrictMap F hm) := by
  apply (ContMDiff.subtypeVal_comp_iff V _).mp
  exact hF.contMDiffOn.comp_contMDiff (contMDiff_subtype_val (U := U)) (fun z => z.property)

/-- The manifold derivative of the restricted map is the Fréchet derivative of `F`. -/
theorem mfderiv_restrictMap {F : MinkowskiModel d → MinkowskiModel d}
    (hF : ContDiffOn ℝ ∞ F U) (hm : MapsTo F U V) (z : U)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) z) :
    (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (restrictMap F hm) z v :
      MinkowskiModel d) = fderiv ℝ F z v := by
  have hf := contMDiff_restrictMap hF hm
  have h₁ := congrArg (fun L => L v) (mfderiv_comp z
    ((contMDiff_subtype_val (U := V) (n := ∞)).mdifferentiableAt (by simp))
    ((hf z).mdifferentiableAt (by simp)))
  change mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d)
      (Subtype.val ∘ restrictMap F hm) z v =
    mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) Subtype.val (restrictMap F hm z)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (restrictMap F hm) z v) at h₁
  rw [Manifold.mfderiv_subtype_val_apply] at h₁
  rw [← h₁]
  have hFd : DifferentiableAt ℝ F z :=
    (hF.contDiffAt (U.isOpen.mem_nhds z.property)).differentiableAt (by simp)
  have hcomp : (Subtype.val ∘ restrictMap F hm) = F ∘ (Subtype.val : U → MinkowskiModel d) :=
    rfl
  rw [hcomp, mfderiv_comp z hFd.mdifferentiableAt
    ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiableAt (by simp))]
  rw [ContinuousLinearMap.comp_apply, Manifold.mfderiv_subtype_val_apply, mfderiv_eq_fderiv]
  rfl

/-- A bilinear form on the model is determined by its coefficients:
`B(v, w) = Σ_{a,b} B(e_a, e_b) v^a w^b`. -/
theorem bilinear_eq_sum (B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (v w : MinkowskiModel d) :
    B v w = ∑ a, ∑ b, B (Pi.single a 1) (Pi.single b 1) * v a * w b := by
  conv_lhs => rw [pi_eq_sum_univ' v, pi_eq_sum_univ' w]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

variable (g : CoordinateMetric σ d V) (g' : CoordinateMetric σ d U)
  {F : MinkowskiModel d → MinkowskiModel d}

/-- **The coefficients of a pullback metric**: `g'_{ik}(x) = g_{ab}(F x) ∂_i F^a ∂_k F^b`. -/
theorem coefficient_pullback
    (hform : ∀ x ∈ U, ∀ v w, g'.form x v w = g.form (F x) (fderiv ℝ F x v) (fderiv ℝ F x w))
    {x : MinkowskiModel d} (hx : x ∈ U) (i k : Fin (d + 1)) :
    g'.coefficient x i k = ∑ a, ∑ b, g.coefficient (F x) a b *
      fderiv ℝ F x (Pi.single i 1) a * fderiv ℝ F x (Pi.single k 1) b := by
  change g'.form x (Pi.single i 1) (Pi.single k 1) = _
  rw [hform x hx, bilinear_eq_sum]
  rfl

/-- **The Einstein tensor transforms as a covariant two-tensor** under a smooth map that pulls
the metric back: `G'_{ik}(x) = G_{ab}(F x) ∂_i F^a ∂_k F^b`. -/
theorem einsteinOf_pullback (hF : ContDiffOn ℝ ∞ F U) (hm : MapsTo F U V)
    (hform : ∀ x ∈ U, ∀ v w, g'.form x v w = g.form (F x) (fderiv ℝ F x v) (fderiv ℝ F x w))
    {x : MinkowskiModel d} (hx : x ∈ U) (i k : Fin (d + 1)) :
    einsteinOf g'.coefficient x i k = ∑ a, ∑ b, einsteinOf g.coefficient (F x) a b *
      fderiv ℝ F x (Pi.single i 1) a * fderiv ℝ F x (Pi.single k 1) b := by
  let x' : U := ⟨x, hx⟩
  let f := restrictMap F hm
  have hf := contMDiff_restrictMap hF hm
  have hmetric : ∀ y v w, g'.toLorentzMetric.form y v w =
      g.toLorentzMetric.form (f y)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y v)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y w) := by
    intro y v w
    have h1 := mfderiv_restrictMap hF hm y v
    have h2 := mfderiv_restrictMap hF hm y w
    change g'.form y v w = g.form (F y) _ _
    rw [h1, h2]
    exact hform y y.property v w
  have hinv := g'.toLorentzMetric.isInvertible_of_metric g.toLorentzMetric x' (f x') _
    (hmetric x')
  obtain ⟨e, he⟩ := hinv
  have hR : ∀ u v w, e (g'.toLorentzMetric.curvature x' u v w) =
      g.toLorentzMetric.curvature (f x') (e u) (e v) (e w) := by
    intro u v w
    have h := g'.toLorentzMetric.curvature_naturality_of_metric g.toLorentzMetric hf hmetric
      x' u v w
    rw [← he] at h
    exact h
  have hformE : ∀ u v, g'.toLorentzMetric.form x' u v =
      g.toLorentzMetric.form (f x') (e u) (e v) := by
    intro u v
    rw [hmetric x' u v, ← he]
    rfl
  have hRic := g'.toLorentzMetric.ricci_naturality g.toLorentzMetric x' (f x') e hR
  have hS := g'.toLorentzMetric.scalarCurvature_naturality g.toLorentzMetric x' (f x') e hformE hR
  have hE : ∀ u v, g'.toLorentzMetric.einstein x' u v =
      g.toLorentzMetric.einstein (f x') (e u) (e v) := by
    intro u v
    rw [LorentzMetric.einstein_apply, LorentzMetric.einstein_apply, hRic, hS, hformE]
  have hev (u : MinkowskiModel d) : (e u : MinkowskiModel d) = fderiv ℝ F x u := by
    rw [← mfderiv_restrictMap hF hm x' u, ← he]
    rfl
  have hl := g'.toLorentzMetric_einstein_chartField x' x' i k
  rw [physicalChart_chartField, physicalChart_chartField] at hl
  rw [← hl]
  refine (hE (Pi.single i 1) (Pi.single k 1)).trans ?_
  rw [hev (Pi.single i 1), hev (Pi.single k 1)]
  let B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ := g.toLorentzMetric.einstein (f x')
  change B (fderiv ℝ F x (Pi.single i 1)) (fderiv ℝ F x (Pi.single k 1)) = _
  rw [bilinear_eq_sum B]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hb := g.toLorentzMetric_einstein_chartField (f x') (f x') a b
  rw [physicalChart_chartField, physicalChart_chartField] at hb
  change B (Pi.single a 1) (Pi.single b 1) * _ * _ = _
  rw [show B (Pi.single a 1) (Pi.single b 1) = einsteinOf g.coefficient (F x) a b from hb]

/-- The tensor `T'_{ik}(x) = T_{ab}(F x) ∂_i F^a ∂_k F^b` pulled back by `F`. -/
def pullbackTensor (F : MinkowskiModel d → MinkowskiModel d)
    (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun i k => ∑ a, ∑ b, T (F x) a b *
    fderiv ℝ F x (Pi.single i 1) a * fderiv ℝ F x (Pi.single k 1) b

/-- **The Einstein equations are covariant**: if `g` solves `G + Λg = κT` on `V`, its pullback
`g'` by `F` solves them on `U` with the pulled-back tensor. -/
theorem IsEinstein.pullback {κ Λ : ℝ} {T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (h : g.IsEinstein κ Λ T) (hF : ContDiffOn ℝ ∞ F U) (hm : MapsTo F U V)
    (hform : ∀ x ∈ U, ∀ v w, g'.form x v w = g.form (F x) (fderiv ℝ F x v) (fderiv ℝ F x w)) :
    g'.IsEinstein κ Λ (pullbackTensor F T) := by
  intro x hx i k
  rw [einsteinOf_pullback g g' hF hm hform hx, coefficient_pullback g g' hform hx]
  simp only [pullbackTensor, Matrix.of_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hab := h (F x) (hm hx) a b
  calc einsteinOf g.coefficient (F x) a b * fderiv ℝ F x (Pi.single i 1) a *
          fderiv ℝ F x (Pi.single k 1) b +
        Λ * (g.coefficient (F x) a b * fderiv ℝ F x (Pi.single i 1) a *
          fderiv ℝ F x (Pi.single k 1) b)
      = (einsteinOf g.coefficient (F x) a b + Λ * g.coefficient (F x) a b) *
          fderiv ℝ F x (Pi.single i 1) a * fderiv ℝ F x (Pi.single k 1) b := by ring
    _ = _ := by rw [hab]; ring


/-- **The pullback of a coordinate metric** `g` on `V` by a smooth map `F : U → V` with invertible
derivative: `g'(x)(v, w) = g(F x)(DF v, DF w)`. -/
def pullback (g : CoordinateMetric σ d V) (F : MinkowskiModel d → MinkowskiModel d)
    (hF : ContDiffOn ℝ ∞ F U) (hm : MapsTo F U V)
    (hinv : ∀ x ∈ U, (fderiv ℝ F x).IsInvertible) : CoordinateMetric σ d U where
  form x := (g.form (F x)).bilinearComp (fderiv ℝ F x) (fderiv ℝ F x)
  smooth := by
    refine contDiffOn_clm_apply.2 fun v => contDiffOn_clm_apply.2 fun w => ?_
    intro z hz
    refine ContDiffAt.contDiffWithinAt ?_
    have hFz := hF.contDiffAt (U.isOpen.mem_nhds hz)
    have hDF : ContDiffAt ℝ ∞ (fderiv ℝ F) z :=
      (hF.fderiv_of_isOpen (m := ∞) U.isOpen (by simp)).contDiffAt (U.isOpen.mem_nhds hz)
    have hB : ContDiffAt ℝ ∞ (fun y => g.form (F y)) z :=
      ContDiffAt.comp (f := F) z (g.smooth.contDiffAt (V.isOpen.mem_nhds (hm hz))) hFz
    exact (hB.clm_apply (hDF.clm_apply contDiffAt_const)).clm_apply
      (hDF.clm_apply contDiffAt_const)
  signature := by
    intro z hz
    obtain ⟨e, he⟩ := hinv z hz
    obtain ⟨j, hj⟩ := g.signature _ (hm hz)
    refine ⟨e.trans j, fun v w => ?_⟩
    have hv (u : MinkowskiModel d) : fderiv ℝ F z u = e u := by rw [← he]; rfl
    simp only [ContinuousLinearMap.bilinearComp_apply, hv, hj]
    rfl

theorem pullback_form_apply (g : CoordinateMetric σ d V) {F : MinkowskiModel d → MinkowskiModel d}
    (hF : ContDiffOn ℝ ∞ F U) (hm : MapsTo F U V)
    (hinv : ∀ x ∈ U, (fderiv ℝ F x).IsInvertible) (x v w : MinkowskiModel d) :
    (g.pullback F hF hm hinv).form x v w = g.form (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) :=
  rfl

/-- The Einstein equations of a pullback metric, with the pulled-back tensor. -/
theorem IsEinstein.pullback_metric (g : CoordinateMetric σ d V)
    {F : MinkowskiModel d → MinkowskiModel d} (hF : ContDiffOn ℝ ∞ F U) (hm : MapsTo F U V)
    (hinv : ∀ x ∈ U, (fderiv ℝ F x).IsInvertible) {κ Λ : ℝ}
    {T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (h : g.IsEinstein κ Λ T) :
    (g.pullback F hF hm hinv).IsEinstein κ Λ (pullbackTensor F T) :=
  h.pullback g _ hF hm fun x _ v w => pullback_form_apply g hF hm hinv x v w

end ProjectAinos.SmoothGeometry.CoordinateMetric
