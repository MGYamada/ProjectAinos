/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Tensor.ShapeDerivativeEvaluation
public import ProjectAinos.SmoothGeometry.Lorentzian.CurvatureDerivative
public import ProjectAinos.SmoothGeometry.Lorentzian.TwoFormRaised

/-! # The Levi-Civita connection on every tensor shape

The Levi-Civita connection of a Lorentz metric induces through `Tensor.Shape.connection` a
covariant derivative on each tensor shape. `Γ^l_{ik}` is `chartChristoffel e x l i k`, the
component `l` of `∇_{∂_i} ∂_k`, and `dx^j` is `chartCovector e x j`.

* `leviCivita_isLocallyRegular`: the connection maps `C^(n+1)` fields to `C^n` sections, so the
  induced derivative of a smooth tensor of any shape is smooth (`shapeCovariantDerivative`).
* `shapeConnection_cotangent_chart`: `(∇_i α)_k = ∂_i α_k − Γ^l_{ik} α_l`.
* `shapeConnection_endomorphism_chart`:
  `(∇_i A)^j_k = ∂_i A^j_k + Γ^j_{il} A^l_k − Γ^l_{ik} A^j_l`.
* `shapeConnection_chartCovector`: `∇_i dx^j = −Γ^j_{ik} dx^k`.
* `shapeConnection_contravariant_two_chart`:
  `(∇_i T)^{jk} = ∂_i T^{jk} + Γ^j_{il} T^{lk} + Γ^k_{il} T^{jl}`.
* `shapeConnection_form`: metric compatibility, `∇g = 0`.
-/

@[expose] public section
noncomputable section

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "E" => MinkowskiModel d
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- The Levi-Civita connection maps locally `C^(n+1)` fields to locally `C^n` sections. -/
theorem leviCivita_isLocallyRegular :
    Tensor.SmoothBundle.Connection.IsLocallyRegular (A := Tensor.SmoothBundle.tangent I (M := M))
      g.leviCivita :=
  fun _ _ _ hσ => g.contMDiffAt_leviCivita hσ

/-- The covariant derivative of a smooth tensor of shape `s`, a smooth tensor of shape
`hom tangent s`. -/
def shapeCovariantDerivative (s : Tensor.Shape) (T : (s.bundle I (M := M)).Section I) :
    ((Tensor.Shape.hom .tangent s).bundle I (M := M)).Section I :=
  Tensor.Shape.covariantDerivative g.leviCivita_isLocallyRegular s T

/-- The components `(∇_i α)_k = ∂_i α_k − Γ^l_{ik} α_l` of the covariant derivative of a covector
field in a chart. -/
theorem shapeConnection_cotangent_chart {α : ∀ x : M, TM x →L[ℝ] ℝ} {x : M}
    (hα : MDifferentiableAt I ((I).prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y (α y)) x)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : x ∈ e.source) (i k : Fin (d + 1)) :
    Tensor.Shape.cotangent.connection g.leviCivita α x (chartField e (Pi.single i 1) x)
        (chartField e (Pi.single k 1) x) =
      mvfderiv I (fun y => α y (chartField e (Pi.single k 1) y)) x
          (chartField e (Pi.single i 1) x) -
        ∑ l, g.chartChristoffel e x l i k * α x (chartField e (Pi.single l 1) x) := by
  rw [Tensor.Shape.connection_hom_apply g.leviCivita .tangent .scalar hα
    (chartField_mdifferentiableAt he hx _), Tensor.Shape.connection_scalar_apply,
    Tensor.Shape.connection_tangent, g.leviCivita_chartField_eq_sum he hx i k]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- The components `(∇_i A)^j_k = ∂_i A^j_k + Γ^j_{il} A^l_k − Γ^l_{ik} A^j_l` of the covariant
derivative of a field of endomorphisms in a chart, with `A^j_k = (A ∂_k)^j`. -/
theorem shapeConnection_endomorphism_chart {A : ∀ x : M, TM x →L[ℝ] TM x} {x : M}
    (hA : ContMDiffAt I ((I).prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y => TotalSpace.mk' (E →L[ℝ] E) y (A y)) x)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : x ∈ e.source) (i j k : Fin (d + 1)) :
    chartTangentMap e x ((Tensor.Shape.hom .tangent .tangent).connection g.leviCivita A x
        (chartField e (Pi.single i 1) x) (chartField e (Pi.single k 1) x)) j =
      mvfderiv I (fun y => chartTangentMap e y (A y (chartField e (Pi.single k 1) y)) j) x
          (chartField e (Pi.single i 1) x) +
        ∑ l, g.chartChristoffel e x j i l *
          chartTangentMap e x (A x (chartField e (Pi.single k 1) x)) l -
        ∑ l, g.chartChristoffel e x l i k *
          chartTangentMap e x (A x (chartField e (Pi.single l 1) x)) j := by
  have hk := chartField_contMDiffAt he hx (Pi.single k 1)
  have hV : ContMDiffAt I ((I).prod I) 1
      (T% (fun y => A y (chartField e (Pi.single k 1) y))) x :=
    hA.clm_bundle_apply (hk.of_le (by simp))
  rw [Tensor.Shape.connection_hom_apply g.leviCivita .tangent .tangent
    (hA.mdifferentiableAt (by simp)) (chartField_mdifferentiableAt he hx _),
    Tensor.Shape.connection_tangent, g.leviCivita_chartField_eq_sum he hx i k, map_sub,
    Pi.sub_apply, g.leviCivita_chart_components he hx hV]
  simp [map_sum, map_smul, Pi.single_apply]

/-- The covariant derivative of a coordinate covector on the coordinate fields:
`(∇_i dx^j)_k = −Γ^j_{ik}`. -/
theorem shapeConnection_chartCovector_apply {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (i j k : Fin (d + 1)) :
    Tensor.Shape.cotangent.connection g.leviCivita (fun y => chartCovector e y j) x
        (chartField e (Pi.single i 1) x) (chartField e (Pi.single k 1) x) =
      -g.chartChristoffel e x j i k := by
  rw [g.shapeConnection_cotangent_chart
    ((chartCovector_contMDiffAt he hx j).mdifferentiableAt (by simp)) he hx i k]
  have heq : (fun y => chartCovector e y j (chartField e (Pi.single k 1) y)) =ᶠ[𝓝 x]
      fun _ => (Pi.single k 1 : E) j := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact congrFun (chartTangentMap_field he hy (Pi.single k 1)) j
  rw [mvfderiv_congr_of_eventuallyEq heq, mvfderiv_const]
  simp [chartCovector, chartTangentMap_field he hx, Pi.single_apply]

/-- The covariant derivative of a coordinate covector: `∇_i dx^j = −Γ^j_{ik} dx^k`. -/
theorem shapeConnection_chartCovector {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (i j : Fin (d + 1)) :
    Tensor.Shape.cotangent.connection g.leviCivita (fun y => chartCovector e y j) x
        (chartField e (Pi.single i 1) x) =
      -∑ k, g.chartChristoffel e x j i k • chartCovector e x k := by
  have h := Tensor.covector_eq_sum x (chartTangentEquiv he hx)
    (Tensor.Shape.cotangent.connection g.leviCivita (fun y => chartCovector e y j) x
      (chartField e (Pi.single i 1) x))
  refine h.trans ?_
  simp only [chartTangentEquiv_symm, g.shapeConnection_chartCovector_apply he hx]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => neg_smul _ (chartCovector e x k)

/-- The components `(∇_i T)^{jk} = ∂_i T^{jk} + Γ^j_{il} T^{lk} + Γ^k_{il} T^{jl}` of the
covariant derivative of a contravariant two-tensor in a chart, with `T^{jk} = T(dx^j, dx^k)`.
Instance search finds no norm on `(E →L ℝ) →L (E →L ℝ) →L ℝ`, so the model is written as that of
the shape. -/
theorem shapeConnection_contravariant_two_chart
    {T : ∀ x : M, ((Tensor.Shape.mixed 2 0).bundle I (M := M)).Fiber x} {x : M}
    (hT : MDifferentiableAt I ((I).prod 𝓘(ℝ, ((Tensor.Shape.mixed 2 0).bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' ((Tensor.Shape.mixed 2 0).bundle I (M := M)).Model y (T y)) x)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : x ∈ e.source) (i j k : Fin (d + 1)) :
    (Tensor.Shape.mixed 2 0).connection g.leviCivita T x (chartField e (Pi.single i 1) x)
        (chartCovector e x j) (chartCovector e x k) =
      mvfderiv I (fun y => T y (chartCovector e y j) (chartCovector e y k)) x
          (chartField e (Pi.single i 1) x) +
        ∑ l, g.chartChristoffel e x j i l * T x (chartCovector e x l) (chartCovector e x k) +
        ∑ l, g.chartChristoffel e x k i l * T x (chartCovector e x j) (chartCovector e x l) := by
  have hα (j : Fin (d + 1)) := (chartCovector_contMDiffAt he hx j).mdifferentiableAt (by simp)
  have h₁ := Tensor.Shape.connection_hom_apply g.leviCivita .cotangent (.hom .cotangent .scalar)
    hT (hα j) (chartField e (Pi.single i 1) x)
  have h₂ := Tensor.Shape.connection_hom_apply g.leviCivita .cotangent .scalar
    (L := fun y => T y (chartCovector e y j)) (hT.clm_bundle_apply (hα j)) (hα k)
    (chartField e (Pi.single i 1) x)
  beta_reduce at h₁ h₂
  refine (congrArg (fun A => A (chartCovector e x k)) h₁).trans ?_
  simp only [sub_apply]
  rw [h₂, g.shapeConnection_chartCovector he hx i j, g.shapeConnection_chartCovector he hx i k,
    Tensor.Shape.connection_scalar_apply]
  simp only [map_neg, map_sum, map_smul, neg_apply, sum_apply, smul_apply, smul_eq_mul]
  ring

/-- Metric compatibility: the covariant derivative of the metric vanishes. -/
theorem shapeConnection_form :
    (Tensor.Shape.covariant 2).connection g.leviCivita (fun y => g.form y) = 0 := by
  funext x
  ext u v w
  have h := Tensor.Shape.connection_covariant_two_apply g.leviCivita ⟨g.form, g.smooth⟩ x u v w
  have hV := mdifferentiableAt_extend I E v
  have hW := mdifferentiableAt_extend I E w
  have h₂ := Tensor.bilinearCovariantDerivative_apply g.leviCivita ⟨g.form, g.smooth⟩ hV hW u
  simp only [extend_apply_self] at h₂
  have h₃ := g.leviCivita_metricCompatible u hV hW
  simp only [extend_apply_self] at h₃
  refine (h.trans h₂).trans ?_
  change mvfderiv I (fun y => g.form y (extend E v y) (extend E w y)) x u -
    g.form x (g.leviCivita (extend E v) x u) w - g.form x v (g.leviCivita (extend E w) x u) = 0
  rw [h₃]
  ring

end ProjectAinos.SmoothGeometry.LorentzMetric
