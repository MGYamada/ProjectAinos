/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.InertialDerivatives
public import ProjectAinos.SmoothGeometry.Lorentzian.CurvatureNaturality
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateFirstVariation
public import ProjectAinos.SmoothGeometry.Lorentzian.ChristoffelCertificate

/-!
# The Kretschmann scalar

The quadratic curvature invariant `R_{abcd} R^{abcd}` of a Lorentz metric, written without a
choice of basis as `K = −g^{ac} g^{bf} tr(R(e_a, e_b) ∘ R(e_c, e_f))`: the trace pairing of the
curvature endomorphisms `R(u, v) = (w ↦ R(u, v) w)`, contracted twice with the inverse metric
(`LorentzMetric.kretschmann`). With the antisymmetry `R_{lkab} = −R_{klab}` the two forms agree.

* `LorentzMetric.kretschmann_naturality`, `LorentzMetric.kretschmann_isometry`: **the scalar is
  invariant**: a tangent isomorphism that preserves the metric and intertwines the curvature
  preserves it, and so does every smooth metric-preserving map `f : M → N` between Lorentz
  manifolds of the same dimension, `K_g(x) = K_h(f(x))`.
* `LorentzMetric.kretschmann_chart`: in any chart,
  `K = −Σ g^{ac} g^{bf} R^k_{lab} R^l_{kcf}` (`kretschmannContraction`) with the curvature
  components `R^l_{kij} = (R(∂_i, ∂_j)∂_k)^l` and the inverse metric of the chart.
* `LorentzMetric.kretschmann_contMDiffAt`, `LorentzMetric.kretschmann_continuousAt`: the scalar
  is a smooth function on the manifold.
* `CoordinateMetric.kretschmannOf`, `CoordinateMetric.toLorentzMetric_kretschmann`: for a
  metric given by coefficients on an open set of the model, the scalar is the classical formula
  in the Christoffel symbols of the coefficients and their inverse.
-/

@[expose] public section
noncomputable section

open Bundle FiberBundle ContinuousLinearMap Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

/-- **The contraction of the Kretschmann scalar** from curvature components
`R l i j k = (R(∂_i, ∂_j)∂_k)^l` and inverse metric components `G`:
`−Σ G^{ac} G^{bf} R^k_{lab} R^l_{kcf}`. -/
def kretschmannContraction {d : ℕ} (R : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : ℝ :=
  -∑ a, ∑ c, (∑ b, ∑ f, (∑ k, ∑ l, R k a b l * R l c f k) * G b f) * G a c

namespace LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "E" => MinkowskiModel d
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- The trace pairing `(A, B) ↦ tr(A ∘ B)` of the endomorphisms of a tangent space. -/
def tracePairing (x : M) : (TM x →L[ℝ] TM x) →L[ℝ] (TM x →L[ℝ] TM x) →L[ℝ] ℝ :=
  (compL ℝ (TM x →L[ℝ] TM x) (TM x →L[ℝ] TM x) ℝ (Tensor.traceL E)).comp
    (compL ℝ (TM x) (TM x) (TM x))

omit [IsManifold I ∞ M] in
theorem tracePairing_apply (x : M) (A B : TM x →L[ℝ] TM x) :
    tracePairing x A B = LinearMap.trace ℝ E (A.comp B).toLinearMap := rfl

/-- `(v, w) ↦ tr(R(u, v) ∘ R(u', w))`. -/
def curvatureTraceForm (x : M) (u u' : TM x) : TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  (tracePairing x).bilinearComp (g.curvature x u) (g.curvature x u')

theorem curvatureTraceForm_apply (x : M) (u u' v w : TM x) :
    g.curvatureTraceForm x u u' v w =
      tracePairing x (g.curvature x u v) (g.curvature x u' w) := rfl

theorem curvatureTraceForm_add_left (x : M) (u₁ u₂ u' : TM x) :
    g.curvatureTraceForm x (u₁ + u₂) u' =
      g.curvatureTraceForm x u₁ u' + g.curvatureTraceForm x u₂ u' := by
  ext v w
  simp only [curvatureTraceForm_apply, map_add, add_apply]

theorem curvatureTraceForm_smul_left (x : M) (c : ℝ) (u u' : TM x) :
    g.curvatureTraceForm x (c • u) u' = c • g.curvatureTraceForm x u u' := by
  ext v w
  simp only [curvatureTraceForm_apply, map_smul, smul_apply]

theorem curvatureTraceForm_add_right (x : M) (u u'₁ u'₂ : TM x) :
    g.curvatureTraceForm x u (u'₁ + u'₂) =
      g.curvatureTraceForm x u u'₁ + g.curvatureTraceForm x u u'₂ := by
  ext v w
  simp only [curvatureTraceForm_apply, map_add, add_apply]

theorem curvatureTraceForm_smul_right (x : M) (c : ℝ) (u u' : TM x) :
    g.curvatureTraceForm x u (c • u') = c • g.curvatureTraceForm x u u' := by
  ext v w
  simp only [curvatureTraceForm_apply, map_smul, smul_apply]

/-- The bilinear form `(u, u') ↦ g^{vw} tr(R(u, v) ∘ R(u', w))`. -/
def curvatureSquareForm (x : M) : TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  have : T2Space (TM x) := FiberBundle.t2Space E TM x
  have : FiniteDimensional ℝ (TM x) := VectorBundle.finiteDimensional ℝ E TM x
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (TM x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (TM x →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun u u' => g.contract x (g.curvatureTraceForm x u u'))
        (fun u₁ u₂ u' => by
          simp only [curvatureTraceForm_add_left, contract_add])
        (fun c u u' => by
          simp only [curvatureTraceForm_smul_left, contract_smul, smul_eq_mul])
        (fun u u'₁ u'₂ => by
          simp only [curvatureTraceForm_add_right, contract_add])
        (fun c u u' => by
          simp only [curvatureTraceForm_smul_right, contract_smul, smul_eq_mul]))

theorem curvatureSquareForm_apply (x : M) (u u' : TM x) :
    g.curvatureSquareForm x u u' = g.contract x (g.curvatureTraceForm x u u') := rfl

/-- **The Kretschmann scalar** `R_{abcd} R^{abcd}`, written without a basis as
`−g^{ac} g^{bf} tr(R(e_a, e_b) ∘ R(e_c, e_f))`. -/
def kretschmann (x : M) : ℝ := -g.contract x (g.curvatureSquareForm x)

/-! ### Invariance -/

section Naturality

variable {N : Type} [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]

/-- **The Kretschmann scalar is invariant**: a tangent isomorphism that preserves the metric and
intertwines the curvature tensors preserves it. -/
theorem kretschmann_naturality (h : LorentzMetric σ d N) (x : M) (y : N)
    (e : TM x ≃L[ℝ] TangentSpace I y)
    (he : ∀ u v, g.form x u v = h.form y (e u) (e v))
    (hR : ∀ u v w, e (g.curvature x u v w) = h.curvature y (e u) (e v) (e w)) :
    g.kretschmann x = h.kretschmann y := by
  have hT (u v u' v' : TM x) :
      tracePairing x (g.curvature x u v) (g.curvature x u' v') =
        tracePairing y (h.curvature y (e u) (e v)) (h.curvature y (e u') (e v')) := by
    have hc : ((h.curvature y (e u) (e v)).comp (h.curvature y (e u') (e v'))).toLinearMap =
        e.toLinearEquiv.conj ((g.curvature x u v).comp (g.curvature x u' v')).toLinearMap := by
      ext w
      obtain ⟨z, rfl⟩ := e.surjective w
      change h.curvature y (e u) (e v) (h.curvature y (e u') (e v') (e z)) =
        e (g.curvature x u v (g.curvature x u' v' (e.symm (e z))))
      rw [e.symm_apply_apply, ← hR, ← hR]
    rw [tracePairing_apply, tracePairing_apply, hc]
    exact (LinearMap.trace_conj' _ e.toLinearEquiv).symm
  unfold kretschmann
  congr 1
  refine g.contract_naturality h x y e he _ _ fun u u' => ?_
  rw [curvatureSquareForm_apply, curvatureSquareForm_apply]
  exact g.contract_naturality h x y e he _ _ fun v v' => hT u v u' v'

/-- **The Kretschmann scalar is invariant under smooth metric-preserving maps**: for a smooth map
`f : M → N` between Lorentz manifolds of the same dimension whose differential preserves the
metric, `K_g(x) = K_h(f(x))`. The map need not be injective. -/
theorem kretschmann_isometry (h : LorentzMetric σ d N) {f : M → N}
    (hf : ContMDiff I I ∞ f)
    (hmetric : ∀ y v w, g.form y v w = h.form (f y) (mfderiv I I f y v) (mfderiv I I f y w))
    (x : M) : g.kretschmann x = h.kretschmann (f x) := by
  obtain ⟨e, he⟩ := g.isInvertible_of_metric h x (f x) _ (hmetric x)
  have he' (u : TM x) : e u = mfderiv I I f x u := by
    rw [← he]
    rfl
  refine g.kretschmann_naturality h x (f x) e (fun u v => by rw [he', he', hmetric x])
    fun u v w => ?_
  rw [he', he', he', he']
  exact g.curvature_naturality_of_metric h hf hmetric x u v w

end Naturality

/-! ### Components in a chart -/

omit [IsManifold I ∞ M] in
/-- The trace of `A ∘ B` in the basis of a chart. -/
theorem tracePairing_chart {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (A B : TM x →L[ℝ] TM x) :
    tracePairing x A B = ∑ k, ∑ l, chartTangentMap e x (A (chartField e (Pi.single l 1) x)) k *
      chartTangentMap e x (B (chartField e (Pi.single k 1) x)) l := by
  let c := chartTangentEquiv he hx
  have h := Tensor.traceL_eq_sum E (Pi.basisFun ℝ (Fin (d + 1)))
    (c.toContinuousLinearMap.comp ((A.comp B).comp c.symm.toContinuousLinearMap))
  have hc : Tensor.traceL E
      (c.toContinuousLinearMap.comp ((A.comp B).comp c.symm.toContinuousLinearMap)) =
      tracePairing x A B :=
    LinearMap.trace_conj' (A.comp B).toLinearMap c.toLinearEquiv
  rw [← hc, h]
  simp only [Pi.basisFun_repr, Pi.basisFun_apply, comp_apply,
    ContinuousLinearEquiv.coe_coe, c, chartTangentEquiv_symm, chartTangentEquiv_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_lhs => rw [← chartField_tangentMap he hx (B (chartField e (Pi.single k 1) x)),
    chartField_eq_sum]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- **The Kretschmann scalar in a chart**: `K = −Σ g^{ac} g^{bf} R^k_{lab} R^l_{kcf}` with the
curvature components `R^l_{kij} = (R(∂_i, ∂_j)∂_k)^l` (`chartCurvature e x l i j k`) and the
inverse metric of the chart. -/
theorem kretschmann_chart {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) :
    g.kretschmann x =
      kretschmannContraction (g.chartCurvature e x) (Matrix.of (g.chartInverse e x)) := by
  rw [kretschmann, g.contract_chart he hx, kretschmannContraction]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [curvatureSquareForm_apply, g.contract_chart he hx]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun f _ => ?_
  rw [curvatureTraceForm_apply, tracePairing_chart he hx]
  rfl

/-- **The Kretschmann scalar is smooth.** -/
theorem kretschmann_contMDiffAt (x : M) : ContMDiffAt I 𝓘(ℝ) ∞ g.kretschmann x := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source E x
  have heq : g.kretschmann =ᶠ[𝓝 x]
      fun y =>
        kretschmannContraction (g.chartCurvature e y) (Matrix.of (g.chartInverse e y)) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy using g.kretschmann_chart he hy
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
  have hR (l i j k : Fin (d + 1)) := g.chartCurvature_contMDiffAt he hx l i j k
  have hG (i j : Fin (d + 1)) := g.chartInverse_contMDiffAt he hx i j
  unfold kretschmannContraction
  refine ContMDiffAt.neg (contMDiffAt_finsetSum fun a _ => contMDiffAt_finsetSum fun c _ => ?_)
  refine ContMDiffAt.mul (contMDiffAt_finsetSum fun b _ => contMDiffAt_finsetSum fun f _ => ?_)
    (hG a c)
  refine ContMDiffAt.mul (contMDiffAt_finsetSum fun k _ => contMDiffAt_finsetSum fun l _ => ?_)
    (hG b f)
  exact (hR k a b l).mul (hR l c f k)

/-- The Kretschmann scalar is continuous. -/
theorem kretschmann_continuousAt (x : M) : ContinuousAt g.kretschmann x :=
  (g.kretschmann_contMDiffAt x).continuousAt

end LorentzMetric

namespace CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

/-- **The Kretschmann scalar of a matrix of coefficients**, from the curvature components
`curvatureOf (christoffelOf C)` and the inverse matrix. -/
def kretschmannOf (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (y : MinkowskiModel d) : ℝ :=
  kretschmannContraction (curvatureOf (christoffelOf C) y) (C y)⁻¹

/-- **The Kretschmann scalar of a coordinate metric** is the classical formula in its
coefficients. -/
theorem toLorentzMetric_kretschmann (g : CoordinateMetric σ d U) (y : U) :
    g.toLorentzMetric.kretschmann y = kretschmannOf g.coefficient y := by
  rw [g.toLorentzMetric.kretschmann_chart (physicalChart_mem y) (by simp), kretschmannOf]
  have hR : g.toLorentzMetric.chartCurvature (physicalChart y) y =
      curvatureOf (christoffelOf g.coefficient) y := by
    funext l i j k
    rw [g.toLorentzMetric_chartCurvature y y]
    rfl
  have hG : Matrix.of (g.toLorentzMetric.chartInverse (physicalChart y) y) =
      (g.coefficient y)⁻¹ := by
    ext i j
    exact g.chartInverse_physicalChart y y i j
  rw [hR, hG]

/-- The Kretschmann scalar of a coordinate metric, computed from any table of Christoffel symbols
that agrees with those of the coefficients near the point. -/
theorem toLorentzMetric_kretschmann_of_table (g : CoordinateMetric σ d U) (y : U)
    {G : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    (hG : ∀ᶠ z in 𝓝 (y : MinkowskiModel d), ∀ k i j,
      christoffelOf g.coefficient z k i j = G z k i j) :
    g.toLorentzMetric.kretschmann y =
      kretschmannContraction (curvatureOf G y) (g.coefficient y)⁻¹ := by
  rw [g.toLorentzMetric.kretschmann_chart (physicalChart_mem y) (by simp)]
  have hR : g.toLorentzMetric.chartCurvature (physicalChart y) y = curvatureOf G y := by
    funext l i j k
    exact toLorentzMetric_chartCurvature_eq_curvatureOf g y y hG l i j k
  have hI : Matrix.of (g.toLorentzMetric.chartInverse (physicalChart y) y) =
      (g.coefficient y)⁻¹ := by
    ext i j
    exact g.chartInverse_physicalChart y y i j
  rw [hR, hI]

end CoordinateMetric

end ProjectAinos.SmoothGeometry
