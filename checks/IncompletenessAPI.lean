/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.Kretschmann
import ProjectAinos.SmoothGeometry.Lorentzian.ProperTimeVariation
import ProjectAinos.SmoothGeometry.Lorentzian.FocalPoints
import ProjectAinos.SmoothGeometry.ODE.SecondDerivativeTest
import ProjectAinos.GeneralRelativity.KasnerIncompleteness
import ProjectAinos.GeneralRelativity.SingularityTheorem

/-! Public consumers of geodesic incompleteness (Landau–Lifshitz §119): the Kretschmann scalar and
its invariance, the curvature singularity of the Kasner metrics along the comoving geodesic, the
second variation of proper time, the shortness of maximizing normal geodesics and focusing
incompleteness, with the synchronous and Kasner instances. Default elaborator options are
intentional: these checks must not rely on the implementation's transparency settings. Every
statement is pinned with its type.
-/

noncomputable section

open Set Filter TopologicalSpace ContinuousLinearMap MeasureTheory
open scoped Manifold ContDiff Topology

/-! ### The Kretschmann scalar -/

section Kretschmann

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

example (x : M)
    (A B : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    tracePairing x A B = LinearMap.trace ℝ (MinkowskiModel d) (A.comp B).toLinearMap :=
  tracePairing_apply x A B

example (x : M) (u u' v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.curvatureTraceForm x u u' v w =
      tracePairing x (g.curvature x u v) (g.curvature x u' w) :=
  g.curvatureTraceForm_apply x u u' v w

example (x : M) (u₁ u₂ u' : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.curvatureTraceForm x (u₁ + u₂) u' =
      g.curvatureTraceForm x u₁ u' + g.curvatureTraceForm x u₂ u' :=
  g.curvatureTraceForm_add_left x u₁ u₂ u'

example (x : M) (c : ℝ) (u u' : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.curvatureTraceForm x (c • u) u' = c • g.curvatureTraceForm x u u' :=
  g.curvatureTraceForm_smul_left x c u u'

example (x : M) (u u'₁ u'₂ : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.curvatureTraceForm x u (u'₁ + u'₂) =
      g.curvatureTraceForm x u u'₁ + g.curvatureTraceForm x u u'₂ :=
  g.curvatureTraceForm_add_right x u u'₁ u'₂

example (x : M) (c : ℝ) (u u' : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.curvatureTraceForm x u (c • u') = c • g.curvatureTraceForm x u u' :=
  g.curvatureTraceForm_smul_right x c u u'

example (x : M) (u u' : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.curvatureSquareForm x u u' = g.contract x (g.curvatureTraceForm x u u') :=
  g.curvatureSquareForm_apply x u u'

example (x : M) : g.kretschmann x = -g.contract x (g.curvatureSquareForm x) := rfl

example {N : Type} [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
    [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N] (h : LorentzMetric σ d N) (x : M) (y : N)
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
    (he : ∀ u v, g.form x u v = h.form y (e u) (e v))
    (hR : ∀ u v w, e (g.curvature x u v w) = h.curvature y (e u) (e v) (e w)) :
    g.kretschmann x = h.kretschmann y :=
  g.kretschmann_naturality h x y e he hR

example {N : Type} [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
    [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N] (h : LorentzMetric σ d N) {f : M → N}
    (hf : ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ f)
    (hmetric : ∀ y v w, g.form y v w =
      h.form (f y) (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y v)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y w))
    (x : M) : g.kretschmann x = h.kretschmann (f x) :=
  g.kretschmann_isometry h hf hmetric x

example {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source)
    (A B : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    tracePairing x A B = ∑ k, ∑ l, chartTangentMap e x (A (chartField e (Pi.single l 1) x)) k *
      chartTangentMap e x (B (chartField e (Pi.single k 1) x)) l :=
  tracePairing_chart he hx A B

example {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source) :
    g.kretschmann x =
      kretschmannContraction (g.chartCurvature e x) (Matrix.of (g.chartInverse e x)) :=
  g.kretschmann_chart he hx

example (x : M) : ContMDiffAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ) ∞ g.kretschmann x :=
  g.kretschmann_contMDiffAt x

example (x : M) : ContinuousAt g.kretschmann x := g.kretschmann_continuousAt x

end ProjectAinos.SmoothGeometry.LorentzMetric

namespace ProjectAinos.SmoothGeometry

example {d : ℕ} (R : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    kretschmannContraction R G =
      -∑ a, ∑ c, (∑ b, ∑ f, (∑ k, ∑ l, R k a b l * R l c f k) * G b f) * G a c := rfl

namespace CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

example (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d) :
    kretschmannOf C y = kretschmannContraction (curvatureOf (christoffelOf C) y) (C y)⁻¹ := rfl

example (g : CoordinateMetric σ d U) (y : U) :
    g.toLorentzMetric.kretschmann y = kretschmannOf g.coefficient y :=
  g.toLorentzMetric_kretschmann y

example (g : CoordinateMetric σ d U) (y : U)
    {G : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    (hG : ∀ᶠ z in 𝓝 (y : MinkowskiModel d), ∀ k i j,
      christoffelOf g.coefficient z k i j = G z k i j) :
    g.toLorentzMetric.kretschmann y =
      kretschmannContraction (curvatureOf G y) (g.coefficient y)⁻¹ :=
  g.toLorentzMetric_kretschmann_of_table y hG

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end Kretschmann

/-! ### The Kasner singularity -/

section KasnerIncompleteness

namespace ProjectAinos.GeneralRelativity.Kasner

open SmoothGeometry CoordinateMetric LorentzMetric

variable {D : Data} {x : MinkowskiModel 3}

example (α : Fin 3) (x : MinkowskiModel 3) : curvTime D α x = accel D α (x 0) := rfl

example (α : Fin 3) (x : MinkowskiModel 3) :
    curvSpace D α x = D.a α (x 0) * deriv (deriv (D.a α)) (x 0) := rfl

example (α β : Fin 3) (x : MinkowskiModel 3) :
    curvMixed D α β x = hubble D α (x 0) * gammaSpatial D β x := rfl

example (hx : x ∈ domain D) (l i j k : Fin 4) :
    curvatureOf (christoffel D) x l i j k = riemann D x l i j k :=
  curvatureOf_christoffel_eq hx l i j k

example (t : ℝ) : kretschmannScalar D t =
    4 * ∑ α, accel D α t ^ 2 + 4 * (hubble D 0 t ^ 2 * hubble D 1 t ^ 2 +
      hubble D 0 t ^ 2 * hubble D 2 t ^ 2 + hubble D 1 t ^ 2 * hubble D 2 t ^ 2) := rfl

example (y : domain D) :
    (metric D).toLorentzMetric.kretschmann y = kretschmannScalar D ((y : MinkowskiModel 3) 0) :=
  kretschmann_metric y

example (p : Fin 3 → ℝ) {t : ℝ} (ht : 0 < t) :
    kretschmannScalar (kasner p) t =
      (4 * ∑ α, p α ^ 2 * (p α - 1) ^ 2 +
        4 * (p 0 ^ 2 * p 1 ^ 2 + p 0 ^ 2 * p 2 ^ 2 + p 1 ^ 2 * p 2 ^ 2)) / t ^ 4 :=
  kretschmannScalar_kasner p ht

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) {t : ℝ} (ht : 0 < t) :
    kretschmannScalar (kasner p) t = -16 * (p 0 * p 1 * p 2) / t ^ 4 :=
  kretschmannScalar_kasner_of_vacuum h1 h2 ht

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hp : p ≠ ![1, 0, 0] ∧ p ≠ ![0, 1, 0] ∧ p ≠ ![0, 0, 1]) : p 0 * p 1 * p 2 < 0 :=
  kasner_prod_neg h1 h2 hp

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (y : domain (kasner p)) :
    (metric (kasner p)).toLorentzMetric.kretschmann y =
      -16 * (p 0 * p 1 * p 2) / (y : MinkowskiModel 3) 0 ^ 4 :=
  kretschmann_kasner h1 h2 y

example (y : domain (kasner ![1, 0, 0])) (l i j k : Fin 4) :
    (metric (kasner ![1, 0, 0])).toLorentzMetric.chartCurvature (physicalChart y) y l i j k =
      0 :=
  riemann_kasner_flat y l i j k

example (y : domain (kasner ![1, 0, 0])) :
    (metric (kasner ![1, 0, 0])).toLorentzMetric.kretschmann y = 0 :=
  kretschmann_kasner_flat y

example {p : Fin 3 → ℝ} {z : MinkowskiModel 3} : z ∈ domain (kasner p) ↔ 0 < z 0 :=
  mem_domain_kasner

example (x₀ : MinkowskiModel 3) (s : ℝ) : comovingPoint x₀ s = x₀ - s • Pi.single 0 1 := rfl

example (x₀ : MinkowskiModel 3) (s : ℝ) : comovingPoint x₀ s 0 = x₀ 0 - s :=
  comovingPoint_zero x₀ s

example (x₀ : MinkowskiModel 3) (s : ℝ) :
    HasDerivAt (comovingPoint x₀) (-(Pi.single 0 1 : MinkowskiModel 3)) s :=
  hasDerivAt_comovingPoint x₀ s

variable {p : Fin 3 → ℝ} {x₀ : domain (kasner p)} {s : ℝ}

example (hs : s < (x₀ : MinkowskiModel 3) 0) :
    (comovingPast p x₀ s : MinkowskiModel 3) = comovingPoint x₀ s :=
  comovingPast_val hs

example (hs : s < (x₀ : MinkowskiModel 3) 0) :
    (fun s => (comovingPast p x₀ s : MinkowskiModel 3)) =ᶠ[𝓝 s] comovingPoint x₀ :=
  comovingPast_eventuallyEq hs

example (hs : s < (x₀ : MinkowskiModel 3) 0) :
    (curveVelocity (comovingPast p x₀) s : MinkowskiModel 3) = -Pi.single 0 1 :=
  curveVelocity_comovingPast hs

example (hs : s < (x₀ : MinkowskiModel 3) 0) :
    (metric (kasner p)).toLorentzMetric.form (comovingPast p x₀ s)
      (curveVelocity (comovingPast p x₀) s) (curveVelocity (comovingPast p x₀) s) = -1 :=
  form_curveVelocity_comovingPast hs

example : (metric (kasner p)).toLorentzMetric.IsGeodesicOn (Iio ((x₀ : MinkowskiModel 3) 0))
    (comovingPast p x₀) :=
  isGeodesicOn_comovingPast

example (hs0 : 0 ≤ s) (hs : s < (x₀ : MinkowskiModel 3) 0) :
    properTime (metric (kasner p)).toLorentzMetric (comovingPast p x₀) 0 s = s :=
  properTime_comovingPast hs0 hs

example {K : Set (domain (kasner p))} (hK : IsCompact K) :
    ∀ᶠ s in 𝓝[<] ((x₀ : MinkowskiModel 3) 0), comovingPast p x₀ s ∉ K :=
  eventually_comovingPast_notMem hK

example (q : domain (kasner p)) :
    ¬ Tendsto (comovingPast p x₀) (𝓝[<] ((x₀ : MinkowskiModel 3) 0)) (𝓝 q) :=
  not_tendsto_comovingPast q

example : Tendsto (fun s => (comovingPast p x₀ s : MinkowskiModel 3))
    (𝓝[<] ((x₀ : MinkowskiModel 3) 0)) (𝓝 (comovingPoint x₀ ((x₀ : MinkowskiModel 3) 0))) :=
  tendsto_comovingPast_val

example (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) (hs : s < (x₀ : MinkowskiModel 3) 0) :
    (metric (kasner p)).toLorentzMetric.kretschmann (comovingPast p x₀ s) =
      -16 * (p 0 * p 1 * p 2) / ((x₀ : MinkowskiModel 3) 0 - s) ^ 4 :=
  kretschmann_comovingPast h1 h2 hs

example (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hp : p ≠ ![1, 0, 0] ∧ p ≠ ![0, 1, 0] ∧ p ≠ ![0, 0, 1]) :
    Tendsto (fun s => (metric (kasner p)).toLorentzMetric.kretschmann (comovingPast p x₀ s))
      (𝓝[<] ((x₀ : MinkowskiModel 3) 0)) atTop :=
  tendsto_kretschmann_comovingPast h1 h2 hp

example (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hp : p ≠ ![1, 0, 0] ∧ p ≠ ![0, 1, 0] ∧ p ≠ ![0, 0, 1]) (F : MinkowskiModel 3 → ℝ)
    (hF : ∀ᶠ z in 𝓝 (comovingPoint x₀ ((x₀ : MinkowskiModel 3) 0)),
      ∀ hz : z ∈ domain (kasner p),
        F z = (metric (kasner p)).toLorentzMetric.kretschmann ⟨z, hz⟩) :
    ¬ ContinuousAt F (comovingPoint x₀ ((x₀ : MinkowskiModel 3) 0)) :=
  not_continuousAt_of_eq_kretschmann h1 h2 hp F hF

example (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hp : p ≠ ![1, 0, 0] ∧ p ≠ ![0, 1, 0] ∧ p ≠ ![0, 0, 1]) {N : Type} [TopologicalSpace N]
    [ChartedSpace (MinkowskiModel 3) N] [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ N]
    (h : LorentzMetric .timeNegative 3 N)
    {f : domain (kasner p) → N} (hf : ContMDiff 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) ∞ f)
    (hmetric : ∀ y v w, (metric (kasner p)).toLorentzMetric.form y v w =
      h.form (f y) (mfderiv 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) f y v)
        (mfderiv 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) f y w)) (q : N) :
    ¬ Tendsto (fun s => f (comovingPast p x₀ s)) (𝓝[<] ((x₀ : MinkowskiModel 3) 0)) (𝓝 q) :=
  not_tendsto_of_isometry h1 h2 hp h hf hmetric q

example (z : MinkowskiModel 3) :
    milne z = ![z 0 * Real.cosh (z 1), z 0 * Real.sinh (z 1), z 2, z 3] := rfl

example : ContDiff ℝ ∞ milne := contDiff_milne

example (z v : MinkowskiModel 3) :
    fderiv ℝ milne z v = ![Real.cosh (z 1) * v 0 + z 0 * Real.sinh (z 1) * v 1,
      Real.sinh (z 1) * v 0 + z 0 * Real.cosh (z 1) * v 1, v 2, v 3] :=
  fderiv_milne_apply z v

example (y : domain (kasner ![1, 0, 0])) : milneEmbedding y = milne y := rfl

example : ContMDiff 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) ∞ milneEmbedding :=
  contMDiff_milneEmbedding

example (y : domain (kasner ![1, 0, 0])) (v : MinkowskiModel 3) :
    mfderiv 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) milneEmbedding y v =
      fderiv ℝ milne y v :=
  mfderiv_milneEmbedding y v

example (y : domain (kasner ![1, 0, 0])) (v w : MinkowskiModel 3) :
    (metric (kasner ![1, 0, 0])).toLorentzMetric.form y v w =
      (minkowskiMetric .timeNegative 3).form (milneEmbedding y)
        (mfderiv 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) milneEmbedding y v)
        (mfderiv 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) milneEmbedding y w) :=
  form_milneEmbedding y v w

example (x₀ : domain (kasner ![1, 0, 0])) :
    ∃ f : domain (kasner ![1, 0, 0]) → MinkowskiModel 3,
      ContMDiff 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) ∞ f ∧
      (∀ y v w, (metric (kasner ![1, 0, 0])).toLorentzMetric.form y v w =
        (minkowskiMetric .timeNegative 3).form (f y)
          (mfderiv 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) f y v)
          (mfderiv 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) f y w)) ∧
      ∃ q : MinkowskiModel 3, Tendsto (fun s => f (comovingPast ![1, 0, 0] x₀ s))
        (𝓝[<] ((x₀ : MinkowskiModel 3) 0)) (𝓝 q) :=
  exists_isometry_tendsto_flat x₀

end ProjectAinos.GeneralRelativity.Kasner

end KasnerIncompleteness

/-! ### The second derivative test -/

section SecondDerivativeTest

namespace ProjectAinos.SmoothGeometry.SecondDerivativeTest

example {f f₁ f₂ : ℝ → ℝ} {ε m : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ t ∈ Icc 0 ε, HasDerivAt f (f₁ t) t) (hf₁ : ∀ t ∈ Icc 0 ε, HasDerivAt f₁ (f₂ t) t)
    (hm : ∀ t ∈ Icc 0 ε, m ≤ f₂ t) : f 0 + ε * f₁ 0 + m * ε ^ 2 / 2 ≤ f ε :=
  add_le_of_le_deriv hε hf hf₁ hm

example {f f₁ f₂ : ℝ → ℝ} {ε M : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ t ∈ Icc 0 ε, HasDerivAt f (f₁ t) t) (hf₁ : ∀ t ∈ Icc 0 ε, HasDerivAt f₁ (f₂ t) t)
    (hM : ∀ t ∈ Icc 0 ε, f₂ t ≤ M) : f ε ≤ f 0 + ε * f₁ 0 + M * ε ^ 2 / 2 :=
  le_add_of_deriv_le hε hf hf₁ hM

example (y : ℝ) : (3 * y - y ^ 2) / 2 ≤ Real.sqrt y := sqrt_ge y

example {φ φ₁ φ₂ : ℝ → ℝ → ℝ} {L ε₀ : ℝ} (hL : 0 < L) (hε₀ : 0 < ε₀)
    (h1 : ∀ s ∈ Icc 0 L, ∀ ε ∈ Icc 0 ε₀, HasDerivAt (fun e => φ e s) (φ₁ ε s) ε)
    (h2 : ∀ s ∈ Icc 0 L, ∀ ε ∈ Icc 0 ε₀, HasDerivAt (fun e => φ₁ e s) (φ₂ ε s) ε)
    (h3 : ContinuousOn (fun q : ℝ × ℝ => φ₂ q.1 q.2) (Icc 0 ε₀ ×ˢ Icc 0 L))
    (h4 : ∀ ε ∈ Icc 0 ε₀, ContinuousOn (φ ε) (Icc 0 L))
    (h5 : ∀ s ∈ Icc 0 L, φ 0 s = 1 ∧ φ₁ 0 s = 0)
    (h6 : 0 < ∫ s in (0 : ℝ)..L, φ₂ 0 s) :
    ∃ ε ∈ Ioc 0 ε₀, (∀ s ∈ Icc 0 L, 0 < φ ε s) ∧ L < ∫ s in (0 : ℝ)..L, Real.sqrt (φ ε s) :=
  exists_lt_integral_sqrt hL hε₀ h1 h2 h3 h4 h5 h6

end ProjectAinos.SmoothGeometry.SecondDerivativeTest

end SecondDerivativeTest

/-! ### The Christoffel symbols and the curvature as multilinear maps -/

section ProperTimeVariation

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}
  (g : CoordinateMetric σ d U)

example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] F)
    (v a b : MinkowskiModel d) :
    T v a b = ∑ p, ∑ i, ∑ j, (v p * a i * b j) •
      T (Pi.single p 1) (Pi.single i 1) (Pi.single j 1) :=
  clm3_sum T v a b

example (k i j : Fin (d + 1)) (a b : MinkowskiModel d) (l : Fin (d + 1)) :
    elemBilin k i j a b l = if l = k then a i * b j else 0 :=
  elemBilin_apply k i j a b l

example (z a b : MinkowskiModel d) (l : Fin (d + 1)) :
    g.chr z a b l = ∑ i, ∑ j, christoffelOf g.coefficient z l i j * a i * b j :=
  g.chr_apply z a b l

example (z Y : MinkowskiModel d) (i l : Fin (d + 1)) :
    g.chr z (Pi.single i 1) Y l = ∑ j, christoffelOf g.coefficient z l i j * Y j :=
  g.chr_single_left z Y i l

example (z : MinkowskiModel d) (p i : Fin (d + 1)) :
    g.chr z (Pi.single p 1) (Pi.single i 1) = fun l => christoffelOf g.coefficient z l p i :=
  g.chr_single z p i

example : ContDiffOn ℝ ∞ g.chr U := g.contDiffOn_chr

example {z : MinkowskiModel d} (hz : z ∈ U) (v a b : MinkowskiModel d) (l : Fin (d + 1)) :
    fderiv ℝ g.chr z v a b l =
      ∑ i, ∑ j, fderiv ℝ (fun w => christoffelOf g.coefficient w l i j) z v * a i * b j :=
  g.fderiv_chr_apply hz v a b l

example {z : MinkowskiModel d} (hz : z ∈ U) (a b : MinkowskiModel d) :
    g.chr z a b = g.chr z b a :=
  g.chr_symm hz a b

example {z : MinkowskiModel d} (hz : z ∈ U) (v a b : MinkowskiModel d) :
    fderiv ℝ g.chr z v a b = fderiv ℝ g.chr z v b a :=
  g.fderiv_chr_symm hz v a b

example {z : MinkowskiModel d} (hz : z ∈ U) (a b : MinkowskiModel d) :
    g.form z a b = g.form z b a :=
  g.form_comm hz a b

example (z X : MinkowskiModel d) (j : Fin (d + 1)) :
    g.form z X (Pi.single j 1) = ∑ l, g.coefficient z l j * X l :=
  g.form_single_right' z X j

example {z : MinkowskiModel d} (hz : z ∈ U) (p i j : Fin (d + 1)) :
    fderiv ℝ g.form z (Pi.single p 1) (Pi.single i 1) (Pi.single j 1) =
      fderiv ℝ (fun w => g.coefficient w i j) z (Pi.single p 1) :=
  g.fderiv_form_single hz p i j

example {z : MinkowskiModel d} (hz : z ∈ U) (v a b : MinkowskiModel d) :
    fderiv ℝ g.form z v a b = g.form z (g.chr z v a) b + g.form z a (g.chr z v b) :=
  g.fderiv_form_apply hz v a b

example (z a b c : MinkowskiModel d) :
    g.curv z a b c = fderiv ℝ g.chr z a b c - fderiv ℝ g.chr z b a c +
      g.chr z a (g.chr z b c) - g.chr z b (g.chr z a c) := rfl

example (z a b : MinkowskiModel d) : g.curv z a a b = 0 := g.curv_self z a b

example (z a b c : MinkowskiModel d) : g.chrComp z a b c = g.chr z a (g.chr z b c) :=
  g.chrComp_apply z a b c

example (z a b c : MinkowskiModel d) :
    g.curv z a b c = ∑ p, ∑ i, ∑ j, (a p * b i * c j) •
      g.curv z (Pi.single p 1) (Pi.single i 1) (Pi.single j 1) :=
  g.curv_expand z a b c

example {z : MinkowskiModel d} (hz : z ∈ U) (l i j k : Fin (d + 1)) :
    g.curv z (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) l =
      curvatureOf (christoffelOf g.coefficient) z l i j k :=
  g.curv_single hz l i j k

example (y : U) (a b c : MinkowskiModel d) :
    (g.toLorentzMetric.curvature y a b c : MinkowskiModel d) = g.curv y a b c :=
  g.toLorentzMetric_curvature y a b c

example {z : MinkowskiModel d} (hz : z ∈ U) (a b c e : MinkowskiModel d) :
    g.form z (g.curv z a b c) e = -g.form z (g.curv z a b e) c :=
  g.curv_pair_swap hz a b c e

example {z : MinkowskiModel d} (hz : z ∈ U) (u : MinkowskiModel d) :
    ∑ j, ∑ k, ricciOf g.coefficient z j k * u j * u k = ∑ i, g.curv z (Pi.single i 1) u u i :=
  g.ricciOf_eq_sum_curv hz u

example {γ X Y : ℝ → MinkowskiModel d} {γ' X' Y' : MinkowskiModel d} {t : ℝ} (hγt : γ t ∈ U)
    (hγ : HasDerivAt γ γ' t) (hX : HasDerivAt X X' t) (hY : HasDerivAt Y Y' t) :
    HasDerivAt (fun t => g.form (γ t) (X t) (Y t))
      (g.form (γ t) (g.chr (γ t) γ' (X t) + X') (Y t) +
        g.form (γ t) (X t) (g.chr (γ t) γ' (Y t) + Y')) t :=
  g.hasDerivAt_form_along hγt hγ hX hY

example {γ X Y : ℝ → MinkowskiModel d} {γ' X' Y' : MinkowskiModel d} {t : ℝ} (hγt : γ t ∈ U)
    (hγ : HasDerivAt γ γ' t) (hX : HasDerivAt X X' t) (hY : HasDerivAt Y Y' t) :
    HasDerivAt (fun t => g.chr (γ t) (X t) (Y t))
      (fderiv ℝ g.chr (γ t) γ' (X t) (Y t) + g.chr (γ t) X' (Y t) + g.chr (γ t) (X t) Y') t :=
  g.hasDerivAt_chr_along hγt hγ hX hY

end ProjectAinos.SmoothGeometry.CoordinateMetric

end ProperTimeVariation

/-! ### Maximizing normal geodesics and focusing incompleteness -/

section FocalPoints

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {d : ℕ} {U : Opens (MinkowskiModel d)} {g : CoordinateMetric .timeNegative d U}

example (γ : ℝ → MinkowskiModel d) (L : ℝ) (hγ : g.IsGeodesicSegment γ L) :
    ContDiff ℝ 2 γ ∧ (∀ s ∈ Icc 0 L, γ s ∈ U) ∧
      ∀ s ∈ Icc 0 L, deriv (deriv γ) s = -g.chr (γ s) (deriv γ s) (deriv γ s) :=
  ⟨hγ.contDiff, hγ.mem, hγ.geodesic⟩

example (c : ℝ → MinkowskiModel d) (T : ℝ) (hc : g.IsTimelikeCurve c T) :
    (∀ s ∈ Icc 0 T, c s ∈ U) ∧ (∀ s ∈ Icc 0 T, DifferentiableAt ℝ c s) ∧
      ContinuousOn (deriv c) (Icc 0 T) ∧
        ∀ s ∈ Icc 0 T, g.form (c s) (deriv c s) (deriv c s) < 0 :=
  ⟨hc.mem, hc.differentiableAt, hc.continuousOn_deriv, hc.timelike⟩

example (c : ℝ → MinkowskiModel d) (T : ℝ) :
    g.curveProperTime c T = ∫ s in (0 : ℝ)..T, Real.sqrt (-g.form (c s) (deriv c s) (deriv c s)) :=
  rfl

example (z : MinkowskiModel d) :
    g.sliceNormal z =
      fun k => -(Real.sqrt (-(g.coefficient z)⁻¹ 0 0))⁻¹ * (g.coefficient z)⁻¹ k 0 :=
  rfl

example (z X Y : MinkowskiModel d) :
    g.sliceSecondForm z X Y = -g.form z (g.chr z X Y) (g.sliceNormal z) := rfl

example (z : MinkowskiModel d) :
    g.sliceExpansion z = ∑ α, ∑ β, (g.spatialCoefficient z)⁻¹ α β *
      g.sliceSecondForm z (Pi.single α.succ 1) (Pi.single β.succ 1) := rfl

example {z : MinkowskiModel d} (hz : z ∈ U) : (g.coefficient z)⁻¹ * g.coefficient z = 1 :=
  coefficient_inv_mul hz

example {z : MinkowskiModel d} (hz : z ∈ U) (X : MinkowskiModel d) :
    g.form z (g.sliceNormal z) X = -(Real.sqrt (-(g.coefficient z)⁻¹ 0 0))⁻¹ * X 0 :=
  form_sliceNormal hz X

example {z : MinkowskiModel d} (hq : (g.coefficient z)⁻¹ 0 0 < 0) :
    g.sliceNormal z 0 = Real.sqrt (-(g.coefficient z)⁻¹ 0 0) :=
  sliceNormal_zero hq

example {z : MinkowskiModel d} (hz : z ∈ U) (hq : (g.coefficient z)⁻¹ 0 0 < 0) :
    g.form z (g.sliceNormal z) (g.sliceNormal z) = -1 :=
  form_sliceNormal_self hz hq

example (ξ : Fin d → ℝ) : (sliceVector ξ : MinkowskiModel d) = Fin.cons 0 ξ := rfl

example (ξ : Fin d → ℝ) : sliceVector ξ 0 = 0 := sliceVector_zero ξ

example (ξ : Fin d → ℝ) (α : Fin d) : sliceVector ξ α.succ = ξ α := sliceVector_succ ξ α

example (z : MinkowskiModel d) (ξ η : Fin d → ℝ) :
    g.form z (sliceVector ξ) (sliceVector η) =
      ∑ α, ∑ β, g.spatialCoefficient z α β * ξ α * η β :=
  form_sliceVector z ξ η

example {z : MinkowskiModel d} (hz : z ∈ U) (hq : (g.coefficient z)⁻¹ 0 0 < 0) :
    (g.spatialCoefficient z).PosDef :=
  spatialCoefficient_posDef hz hq

example (ξ : Fin d → ℝ) :
    sliceVector ξ = ∑ α, ξ α • (Pi.single α.succ 1 : MinkowskiModel d) :=
  sliceVector_eq_sum ξ

example (z : MinkowskiModel d) (ξ η : Fin d → ℝ) :
    g.sliceSecondForm z (sliceVector ξ) (sliceVector η) =
      ∑ α, ∑ β, ξ α * η β * g.sliceSecondForm z (Pi.single α.succ 1) (Pi.single β.succ 1) :=
  sliceSecondForm_sliceVector z ξ η

example {z : MinkowskiModel d} (hz : z ∈ U) (hq : (g.coefficient z)⁻¹ 0 0 < 0) :
    ∃ F : Fin d → MinkowskiModel d, (∀ i, F i 0 = 0) ∧
      (∀ i j, g.form z (F i) (F j) = if i = j then 1 else 0) ∧
      ∑ i, g.sliceSecondForm z (F i) (F i) = g.sliceExpansion z :=
  exists_orthonormal_slice hz hq

example {z : MinkowskiModel d} (hz : z ∈ U) (A : MinkowskiModel d →L[ℝ] MinkowskiModel d)
    (f : Fin (d + 1) → MinkowskiModel d) (η : Fin (d + 1) → ℝ) (hη : ∀ a, η a * η a = 1)
    (horth : ∀ a b, g.form z (f a) (f b) = if a = b then η a else 0) :
    ∑ l, A (Pi.single l 1) l = ∑ a, η a * g.form z (A (f a)) (f a) :=
  trace_eq_sum_orthonormal hz A f η hη horth

variable {γ : ℝ → MinkowskiModel d} {L : ℝ}

example (hγ : g.IsGeodesicSegment γ L) (s : ℝ) : HasDerivAt γ (deriv γ s) s :=
  hγ.hasDerivAt s

example (hγ : g.IsGeodesicSegment γ L) : ContDiff ℝ 1 (deriv γ) := hγ.contDiff_deriv

example (hγ : g.IsGeodesicSegment γ L) (s : ℝ) :
    HasDerivAt (deriv γ) (deriv (deriv γ) s) s :=
  hγ.hasDerivAt_deriv s

example (hγ : g.IsGeodesicSegment γ L) : Continuous (deriv γ) := hγ.continuous_deriv

example (hL : 0 ≤ L) (s : ℝ) : g.transportCoeff γ L hL s =
    -g.chr (γ (projIcc 0 L hL s)) (deriv γ (projIcc 0 L hL s)) := rfl

example (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) : Continuous (g.transportCoeff γ L hL) :=
  continuous_transportCoeff hγ hL

example (hL : 0 ≤ L) {s : ℝ} (hs : s ∈ Icc 0 L) :
    g.transportCoeff γ L hL s = -g.chr (γ s) (deriv γ s) :=
  transportCoeff_of_mem hL hs

example (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) (s : ℝ) :
    g.transportCurve hγ hL s = g.transportCoeff γ L hL s := rfl

example (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) (v : MinkowskiModel d) (s : ℝ) :
    g.parallelField hγ hL v s = LinearODE.propagator (g.transportCurve hγ hL) s 0 v := rfl

example (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) (v : MinkowskiModel d) (s : ℝ) :
    HasDerivAt (g.parallelField hγ hL v)
      (g.transportCoeff γ L hL s (g.parallelField hγ hL v s)) s :=
  hasDerivAt_parallelField hγ hL v s

example (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) (v : MinkowskiModel d) :
    g.parallelField hγ hL v 0 = v :=
  parallelField_zero hγ hL v

example (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) (v : MinkowskiModel d) :
    Continuous (g.parallelField hγ hL v) :=
  continuous_parallelField hγ hL v

example (hγ : g.IsGeodesicSegment γ L) {V W V' W' : ℝ → MinkowskiModel d}
    (hV : ∀ s ∈ Icc 0 L, HasDerivAt V (V' s) s) (hW : ∀ s ∈ Icc 0 L, HasDerivAt W (W' s) s)
    (hV' : ∀ s ∈ Icc 0 L, V' s = -g.chr (γ s) (deriv γ s) (V s))
    (hW' : ∀ s ∈ Icc 0 L, W' s = -g.chr (γ s) (deriv γ s) (W s)) :
    ∀ s ∈ Icc 0 L, g.form (γ s) (V s) (W s) = g.form (γ 0) (V 0) (W 0) :=
  form_eq_of_parallel hγ hV hW hV' hW'

example (x u w w' : MinkowskiModel d) (ε : ℝ) :
    g.varSpeed x u w w' ε = -g.form (x + ε • w) (u + ε • w') (u + ε • w') := rfl

example (x u w w' : MinkowskiModel d) (ε : ℝ) :
    g.varSpeed₁ x u w w' ε =
      -2 * g.form (x + ε • w) (w' + g.chr (x + ε • w) w (u + ε • w')) (u + ε • w') := rfl

example (y v w w' : MinkowskiModel d) :
    g.varSpeed₂Expr y v w w' =
      -2 * (g.form y (g.chr y w (w' + g.chr y w v) + (fderiv ℝ g.chr y w w v + g.chr y w w')) v +
        g.form y (w' + g.chr y w v) (w' + g.chr y w v)) := rfl

example (x u w w' : MinkowskiModel d) (ε : ℝ) :
    g.varSpeed₂ x u w w' ε = g.varSpeed₂Expr (x + ε • w) (u + ε • w') w w' := rfl

example (x w : MinkowskiModel d) (ε : ℝ) : HasDerivAt (fun e : ℝ => x + e • w) w ε :=
  hasDerivAt_line x w ε

example {x u w w' : MinkowskiModel d} {ε : ℝ} (hx : x + ε • w ∈ U) :
    HasDerivAt (g.varSpeed x u w w') (g.varSpeed₁ x u w w' ε) ε :=
  hasDerivAt_varSpeed hx

example {x u w w' : MinkowskiModel d} {ε : ℝ} (hx : x + ε • w ∈ U) :
    HasDerivAt (g.varSpeed₁ x u w w') (g.varSpeed₂ x u w w' ε) ε :=
  hasDerivAt_varSpeed₁ hx

example {x : MinkowskiModel d} (hx : x ∈ U) (u w w' : MinkowskiModel d) :
    g.varSpeed₂ x u w w' 0 =
      -2 * (g.form x (g.chr x u (g.chr x w w) +
          (fderiv ℝ g.chr x u w w + g.chr x w' w + g.chr x w w')) u +
        g.form x (w' + g.chr x u w) (w' + g.chr x u w) + g.form x (g.curv x w u w) u) :=
  varSpeed₂_zero hx u w w'

example {T : Type} [TopologicalSpace T] {S : Set T} {y a b : T → MinkowskiModel d}
    (hy : ContinuousOn y S) (hyU : MapsTo y S U) (ha : ContinuousOn a S) (hb : ContinuousOn b S) :
    ContinuousOn (fun t => g.form (y t) (a t) (b t)) S :=
  continuousOn_form_apply hy hyU ha hb

example {T : Type} [TopologicalSpace T] {S : Set T} {y a b : T → MinkowskiModel d}
    (hy : ContinuousOn y S) (hyU : MapsTo y S U) (ha : ContinuousOn a S) (hb : ContinuousOn b S) :
    ContinuousOn (fun t => g.chr (y t) (a t) (b t)) S :=
  continuousOn_chr_apply hy hyU ha hb

example {T : Type} [TopologicalSpace T] {S : Set T} {y v a b : T → MinkowskiModel d}
    (hy : ContinuousOn y S) (hyU : MapsTo y S U) (hv : ContinuousOn v S)
    (ha : ContinuousOn a S) (hb : ContinuousOn b S) :
    ContinuousOn (fun t => fderiv ℝ g.chr (y t) (v t) (a t) (b t)) S :=
  continuousOn_fderiv_chr_apply hy hyU hv ha hb

example {T : Type} [TopologicalSpace T] {S : Set T} {y v w w' : T → MinkowskiModel d}
    (hy : ContinuousOn y S) (hyU : MapsTo y S U) (hv : ContinuousOn v S)
    (hw : ContinuousOn w S) (hw' : ContinuousOn w' S) :
    ContinuousOn (fun t => g.varSpeed₂Expr (y t) (v t) (w t) (w' t)) S :=
  continuousOn_varSpeed₂Expr hy hyU hv hw hw'

example {γ : ℝ → MinkowskiModel d} {L M : ℝ} (hγ : ContinuousOn γ (Icc 0 L))
    (hU : MapsTo γ (Icc 0 L) U) (hM : 0 ≤ M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Icc 0 ε₀, ∀ s ∈ Icc 0 L, ∀ w : MinkowskiModel d, ‖w‖ ≤ M →
      γ s + ε • w ∈ U :=
  exists_tube (U := U) hγ hU hM

example (hγ : g.IsGeodesicSegment γ L) {W W' : ℝ → MinkowskiModel d} {s : ℝ}
    (hs : s ∈ Icc 0 L) (hW : HasDerivAt W (W' s) s) :
    HasDerivAt (fun s => g.form (γ s) (g.chr (γ s) (W s) (W s)) (deriv γ s))
      (g.form (γ s) (g.chr (γ s) (deriv γ s) (g.chr (γ s) (W s) (W s)) +
        (fderiv ℝ g.chr (γ s) (deriv γ s) (W s) (W s) + g.chr (γ s) (W' s) (W s) +
          g.chr (γ s) (W s) (W' s))) (deriv γ s)) s :=
  hasDerivAt_boundaryTerm hγ hs hW

example (x a b : MinkowskiModel d) (c : ℝ) :
    g.curv x (c • a) b (c • a) = (c * c) • g.curv x a b a :=
  curv_smul_smul x a b c

example {x : MinkowskiModel d} (hx : x ∈ U) (u : MinkowskiModel d) (Ef : Fin d → MinkowskiModel d)
    (huu : g.form x u u = -1) (hEu : ∀ i, g.form x (Ef i) u = 0)
    (hEE : ∀ i j, g.form x (Ef i) (Ef j) = if i = j then 1 else 0) :
    ∑ i, g.form x (g.curv x (Ef i) u (Ef i)) u =
      -∑ j, ∑ k, ricciOf g.coefficient x j k * u j * u k :=
  sum_curv_frame hx u Ef huu hEu hEE

example {τ C L ν : ℝ} (hν : ν * ν = 1) (hC : 0 < C) (hL : 0 < L)
    {γ : ℝ → MinkowskiModel d} (hγ : g.IsGeodesicSegment γ L) (hγ0 : γ 0 0 = τ)
    (hn : deriv γ 0 = ν • g.sliceNormal (γ 0)) (hq : (g.coefficient (γ 0))⁻¹ 0 0 < 0)
    (hRic : ∀ s ∈ Icc 0 L,
      0 ≤ ∑ j, ∑ k, ricciOf g.coefficient (γ s) j k * deriv γ s j * deriv γ s k)
    (hθ : ν * g.sliceExpansion (γ 0) ≤ -C)
    (hmax : ∀ (c : ℝ → MinkowskiModel d) (T : ℝ), g.IsTimelikeCurve c T → c 0 0 = τ →
      c T = γ L → g.curveProperTime c T ≤ L) :
    L ≤ d / C :=
  length_le_of_maximizing hν hC hL hγ hγ0 hn hq hRic hθ hmax

example (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) {ν : ℝ} (hν : ν * ν = 1)
    (hn : deriv γ 0 = ν • g.sliceNormal (γ 0)) (hq : (g.coefficient (γ 0))⁻¹ 0 0 < 0) :
    ∀ s ∈ Icc 0 L, g.form (γ s) (deriv γ s) (deriv γ s) = -1 :=
  hγ.form_deriv_self hL hν hn hq

example {z : MinkowskiModel d} (hz : z ∈ U) (hq : (g.coefficient z)⁻¹ 0 0 < 0)
    {v : MinkowskiModel d} (hv : g.form z v v < 0) : v 0 ≠ 0 :=
  zero_ne_of_timelike hz hq hv

example {c : ℝ → MinkowskiModel d} {T : ℝ} (hT : 0 ≤ T)
    (hc : ∀ s ∈ Icc 0 T, g.form (c s) (deriv c s) (deriv c s) = -1) :
    g.curveProperTime c T = T :=
  curveProperTime_eq_of_unit hT hc

example (hγ : g.IsGeodesicSegment γ L) (hL : 0 < L) {ν : ℝ}
    (hν : ν * ν = 1) (hn : deriv γ 0 = ν • g.sliceNormal (γ 0))
    (htime : ∀ s ∈ Icc 0 L, (g.coefficient (γ s))⁻¹ 0 0 < 0) :
    0 < ν * (γ L 0 - γ 0 0) :=
  hγ.time_lt hL hν hn htime

example {τ C ν : ℝ} (hν : ν * ν = 1) (hC : 0 < C)
    (htime : ∀ z ∈ U, (g.coefficient z)⁻¹ 0 0 < 0)
    (hRic : ∀ z ∈ U, ∀ v : MinkowskiModel d, g.form z v v < 0 →
      0 ≤ ∑ j, ∑ k, ricciOf g.coefficient z j k * v j * v k)
    (hθ : ∀ z ∈ U, z 0 = τ → ν * g.sliceExpansion z ≤ -C)
    (hmax : ∀ p ∈ U, 0 < ν * (p 0 - τ) → ∃ (σ : ℝ → MinkowskiModel d) (ℓ : ℝ), 0 < ℓ ∧
      g.IsGeodesicSegment σ ℓ ∧ σ 0 0 = τ ∧ deriv σ 0 = ν • g.sliceNormal (σ 0) ∧ σ ℓ = p ∧
      ∀ (c : ℝ → MinkowskiModel d) (T : ℝ), g.IsTimelikeCurve c T → c 0 0 = τ → c T = p →
        g.curveProperTime c T ≤ ℓ)
    {γ : ℝ → MinkowskiModel d} {L : ℝ} (hL : 0 < L) (hγ : g.IsGeodesicSegment γ L)
    (hγ0 : γ 0 0 = τ) (hn : deriv γ 0 = ν • g.sliceNormal (γ 0)) :
    L ≤ d / C :=
  length_le_of_focusing hν hC htime hRic hθ hmax hL hγ hγ0 hn

namespace IsSynchronous

variable (hs : g.IsSynchronous) {z : MinkowskiModel d}

example (hz : z ∈ U) : (g.coefficient z)⁻¹ 0 0 = -1 := hs.coefficient_inv_zero_zero hz

example (hz : z ∈ U) : g.sliceNormal z = Pi.single 0 1 := hs.sliceNormal_eq hz

example (hz : z ∈ U) (α β : Fin d) :
    g.sliceSecondForm z (Pi.single α.succ 1) (Pi.single β.succ 1) = g.metricRate z α β / 2 :=
  hs.sliceSecondForm_eq hz α β

example (hz : z ∈ U) : g.sliceExpansion z = g.expansion z := hs.sliceExpansion_eq hz

example (hz : z ∈ U) (v : MinkowskiModel d) : -g.form z v v ≤ v 0 ^ 2 := hs.neg_form_le hz v

example {φ : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn φ (Icc a b))
    (hne : ∀ s ∈ Icc a b, φ s ≠ 0) (ha : 0 < φ a) : ∀ s ∈ Icc a b, 0 < φ s :=
  pos_of_ne_zero hc hne ha

example {c : ℝ → MinkowskiModel d} {T : ℝ} (hT : 0 ≤ T) (hc : g.IsTimelikeCurve c T) :
    g.curveProperTime c T ≤ |c T 0 - c 0 0| :=
  hs.curveProperTime_le hT hc

example {x₀ : MinkowskiModel d} {ν L : ℝ}
    (hmem : ∀ s ∈ Icc 0 L, x₀ + (ν * s) • (Pi.single 0 1 : MinkowskiModel d) ∈ U) :
    g.IsGeodesicSegment (fun s => x₀ + (ν * s) • (Pi.single 0 1 : MinkowskiModel d)) L :=
  hs.isGeodesicSegment_timeLine hmem

example {τ C ν : ℝ} (hν : ν * ν = 1) (hC : 0 < C)
    (hU : ∀ z ∈ U, ∀ t ∈ uIcc τ (z 0), z + (t - z 0) • (Pi.single 0 1 : MinkowskiModel d) ∈ U)
    (hRic : ∀ z ∈ U, ∀ v : MinkowskiModel d, g.form z v v < 0 →
      0 ≤ ∑ j, ∑ k, ricciOf g.coefficient z j k * v j * v k)
    (hθ : ∀ z ∈ U, z 0 = τ → ν * g.expansion z ≤ -C)
    {γ : ℝ → MinkowskiModel d} {L : ℝ} (hL : 0 < L) (hγ : g.IsGeodesicSegment γ L)
    (hγ0 : γ 0 0 = τ) (hn : deriv γ 0 = ν • (Pi.single 0 1 : MinkowskiModel d)) :
    L ≤ d / C :=
  hs.length_le_of_focusing hν hC hU hRic hθ hL hγ hγ0 hn

end IsSynchronous

end ProjectAinos.SmoothGeometry.CoordinateMetric

end FocalPoints

/-! ### The singularity theorem and its instances -/

section SingularityTheorem

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry LorentzMetric CoordinateMetric

example (B : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ) (v w : MinkowskiModel 3) :
    B v w = ∑ j, ∑ k, v j * w k * B (Pi.single j 1) (Pi.single k 1) :=
  clm2_sum B v w

example {U : Opens (MinkowskiModel 3)} (g : CoordinateMetric .timeNegative 3 U) (y : U)
    (v : MinkowskiModel 3) :
    g.toLorentzMetric.ricci y v v = ∑ j, ∑ k, ricciOf g.coefficient y j k * v j * v k :=
  toLorentzMetric_ricci_self g y v

example {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric .timeNegative 3 U}
    {κ Λ : ℝ} {T : Tensor.SmoothBilinear («I» := 𝓘(ℝ, MinkowskiModel 3)) (M := U)}
    (hE : g.toLorentzMetric.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g.toLorentzMetric T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0) :
    ∀ z ∈ U, ∀ v : MinkowskiModel 3, g.form z v v < 0 →
      0 ≤ ∑ j, ∑ k, ricciOf g.coefficient z j k * v j * v k :=
  ricciOf_timelike_nonneg hE hT hκ hΛ

example {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric .timeNegative 3 U}
    (hs : g.IsSynchronous) {κ Λ : ℝ}
    {T : Tensor.SmoothBilinear («I» := 𝓘(ℝ, MinkowskiModel 3)) (M := U)}
    (hE : g.toLorentzMetric.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g.toLorentzMetric T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0)
    {τ C ν : ℝ} (hν : ν * ν = 1) (hC : 0 < C)
    (hU : ∀ z ∈ U, ∀ t ∈ uIcc τ (z 0), z + (t - z 0) • (Pi.single 0 1 : MinkowskiModel 3) ∈ U)
    (hθ : ∀ z ∈ U, z 0 = τ → ν * g.expansion z ≤ -C)
    {γ : ℝ → MinkowskiModel 3} {L : ℝ} (hL : 0 < L) (hγ : g.IsGeodesicSegment γ L)
    (hγ0 : γ 0 0 = τ) (hn : deriv γ 0 = ν • (Pi.single 0 1 : MinkowskiModel 3)) :
    L ≤ 3 / C :=
  IsSynchronous.length_le_of_einstein hs hE hT hκ hΛ hν hC hU hθ hL hγ hγ0 hn

namespace Kasner

example (p : Fin 3 → ℝ) {x₀ : MinkowskiModel 3} {T : ℝ} (hT : T < x₀ 0) :
    (Kasner.metric (Kasner.kasner p)).IsGeodesicSegment
      (fun s => x₀ + (-1 * s) • (Pi.single 0 1 : MinkowskiModel 3)) T :=
  isGeodesicSegment_timeLine_past p hT

example (p : Fin 3 → ℝ) {x₀ : MinkowskiModel 3} {T : ℝ} (hT : T < x₀ 0) :
    (Kasner.metric (Kasner.kasner p)).IsTimelikeCurve
      (fun s : ℝ => x₀ + (-1 * s) • (Pi.single 0 1 : MinkowskiModel 3)) T :=
  isTimelikeCurve_timeLine_past p hT

example {D : Kasner.Data} (hI : (D.I).OrdConnected) {τ : ℝ} (hτ : τ ∈ D.I) :
    ∀ z ∈ Kasner.domain D, ∀ t ∈ uIcc τ (z 0),
      z + (t - z 0) • (Pi.single 0 1 : MinkowskiModel 3) ∈ Kasner.domain D :=
  domain_timeLine hI hτ

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) {τ : ℝ}
    (hτ : 0 < τ) {γ : ℝ → MinkowskiModel 3} {L : ℝ} (hL : 0 < L)
    (hγ : (Kasner.metric (Kasner.kasner p)).IsGeodesicSegment γ L) (hγ0 : γ 0 0 = τ)
    (hn : deriv γ 0 = -(Pi.single 0 1 : MinkowskiModel 3)) :
    L ≤ 3 * τ :=
  length_le_past h1 h2 hτ hL hγ hγ0 hn

example {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1)
    (h2 : ∑ α, p α ^ 2 = 1) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {τ : ℝ} (hτ : τ < 0)
    {γ : ℝ → MinkowskiModel 3} {L : ℝ} (hL : 0 < L)
    (hγ : (Kasner.metric (Kasner.dustKasner p t₀ ht₀).reverse).IsGeodesicSegment γ L)
    (hγ0 : γ 0 0 = τ) (hn : deriv γ 0 = (Pi.single 0 1 : MinkowskiModel 3)) :
    L ≤ 3 / (1 / -τ + 1 / (-τ + t₀)) :=
  length_le_reverse_dustKasner h1 h2 ht₀ hτ hL hγ hγ0 hn

end Kasner

end ProjectAinos.GeneralRelativity

end SingularityTheorem
