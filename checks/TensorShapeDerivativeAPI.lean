/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.ShapeDerivativeExamples

/-! Public consumers of the covariant derivative on every tensor shape: the connections of
mathlib on the scalar bundle and on hom bundles, the recursion over `Tensor.Shape`, the Leibniz
rules, local regularity and smoothness, the recovery of the bilinear and trilinear derivatives,
the chart formulas for the Levi-Civita connection on covectors, endomorphisms and contravariant
two-tensors, metric compatibility, and the curved conformally flat regression. Default
elaborator options are intentional. Every statement is pinned with its type. -/
noncomputable section

open Bundle FiberBundle ContinuousLinearMap

open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.Tensor

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "TM" => TangentSpace I (M := M)

namespace SmoothBundle

example (A : SmoothBundle I (M := M)) : Type := Connection A

example (A : SmoothBundle I (M := M)) : Connection A = CovariantDerivative I A.Model A.Fiber :=
  rfl

example {f : ∀ x, (scalar I (M := M)).Fiber x} {x : M} :
    MDifferentiableAt I (I.prod 𝓘(ℝ)) (fun y => TotalSpace.mk' ℝ y (f y)) x ↔
      MDifferentiableAt I 𝓘(ℝ) (fun y => (f y : ℝ)) x :=
  mdifferentiableAt_scalar_iff

example : Connection (scalar I (M := M)) := scalarConnection

example (f : ∀ x, (scalar I (M := M)).Fiber x) (x : M) :
    scalarConnection f x = mvfderiv I (fun y => (f y : ℝ)) x := rfl

variable {A B : SmoothBundle I (M := M)}

example (cA : Connection A) (cB : Connection B) (L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x) (x : M)
    (U : ∀ x, TM x) (w : ∀ x, A.Fiber x) :
    homDerivativeAux cA cB L x U w = cB (fun y => L y (w y)) x (U x) - L x (cA w x (U x)) :=
  rfl

example (cA : Connection A) (cB : Connection B) (L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x) (x : M)
    (w : ∀ x, A.Fiber x) :
    TensorialAt I E (fun U => homDerivativeAux cA cB L x U w) x :=
  homDerivativeAux_tensorial_direction cA cB L x w

example (cA : Connection A) (cB : Connection B) {L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x} {x : M}
    (hL : MDifferentiableAt I (I.prod 𝓘(ℝ, A.Model →L[ℝ] B.Model))
      (fun y => TotalSpace.mk' (A.Model →L[ℝ] B.Model) y (L y)) x) (U : ∀ x, TM x) :
    TensorialAt I A.Model (fun w => homDerivativeAux cA cB L x U w) x :=
  homDerivativeAux_tensorial_section cA cB hL U

example (cA : Connection A) (cB : Connection B) (L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x) (x : M) :
    TM x →L[ℝ] A.Fiber x →L[ℝ] B.Fiber x :=
  homConnectionFun cA cB L x

example (cA : Connection A) (cB : Connection B) {L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x} {x : M}
    (hL : MDifferentiableAt I (I.prod 𝓘(ℝ, A.Model →L[ℝ] B.Model))
      (fun y => TotalSpace.mk' (A.Model →L[ℝ] B.Model) y (L y)) x)
    {w : ∀ x, A.Fiber x}
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, A.Model)) (fun y => TotalSpace.mk' A.Model y (w y)) x)
    (u : TM x) :
    homConnectionFun cA cB L x u (w x) = cB (fun y => L y (w y)) x u - L x (cA w x u) :=
  homConnectionFun_apply cA cB hL hw u

example (cA : Connection A) (cB : Connection B) : Connection (hom I A B) :=
  homConnection cA cB

example (cA : Connection A) (cB : Connection B) {L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x} {x : M}
    (hL : MDifferentiableAt I (I.prod 𝓘(ℝ, A.Model →L[ℝ] B.Model))
      (fun y => TotalSpace.mk' (A.Model →L[ℝ] B.Model) y (L y)) x)
    {w : ∀ x, A.Fiber x}
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, A.Model)) (fun y => TotalSpace.mk' A.Model y (w y)) x)
    (u : TM x) :
    homConnection cA cB L x u (w x) = cB (fun y => L y (w y)) x u - L x (cA w x u) :=
  homConnection_apply cA cB hL hw u

example (c : Connection A) : Prop := c.IsLocallyRegular

example (c : Connection A) :
    c.IsLocallyRegular ↔ ∀ (n : ℕ∞) {σ : ∀ x, A.Fiber x} {x : M},
      ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) (n + 1)
        (fun y => TotalSpace.mk' A.Model y (σ y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] A.Model)) n
        (fun y => TotalSpace.mk' (E →L[ℝ] A.Model) y (c σ y)) x :=
  Iff.rfl

example {c : Connection A} (hc : c.IsLocallyRegular) (n : ℕ∞) :
    CovariantDerivative.ContMDiffCovariantDerivative c n :=
  hc.contMDiffCovariantDerivative n

example {n : ℕ∞ω} {f : ∀ x, (scalar I (M := M)).Fiber x} {x : M} :
    ContMDiffAt I (I.prod 𝓘(ℝ)) n (fun y => TotalSpace.mk' ℝ y (f y)) x ↔
      ContMDiffAt I 𝓘(ℝ) n (fun y => (f y : ℝ)) x :=
  contMDiffAt_scalar_iff

example {n : ℕ∞} {f : M → ℝ} {X : ∀ x, TM x} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x)
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (fun y => TotalSpace.mk' E y (X y)) x) :
    ContMDiffAt I 𝓘(ℝ) n (fun y => mvfderiv I f y (X y)) x :=
  contMDiffAt_mvfderiv_apply hf hX

example : (scalarConnection (I := I) (M := M)).IsLocallyRegular :=
  scalarConnection_isLocallyRegular

example {cA : Connection A} {cB : Connection B} (hA : cA.IsLocallyRegular)
    (hB : cB.IsLocallyRegular) : (homConnection cA cB).IsLocallyRegular :=
  homConnection_isLocallyRegular hA hB

end SmoothBundle

namespace Shape

variable (cov : CovariantDerivative I E (TangentSpace I (M := M)))

example (s : Shape) : (s.bundle I (M := M)).Connection := s.connection cov

example : Shape.scalar.connection cov = SmoothBundle.scalarConnection :=
  connection_scalar cov

example : Shape.tangent.connection cov = cov := connection_tangent cov

example (a b : Shape) :
    (Shape.hom a b).connection cov =
      SmoothBundle.homConnection (a.connection cov) (b.connection cov) :=
  connection_hom cov a b

example (f : M → ℝ) (x : M) : Shape.scalar.connection cov f x = mvfderiv I f x :=
  connection_scalar_apply cov f x

example (a b : Shape)
    {L : ∀ x, (a.bundle I (M := M)).Fiber x →L[ℝ] (b.bundle I (M := M)).Fiber x} {x : M}
    (hL : MDifferentiableAt I
      (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model →L[ℝ] (b.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' ((a.bundle I (M := M)).Model →L[ℝ] (b.bundle I (M := M)).Model)
        y (L y)) x)
    {w : ∀ x, (a.bundle I (M := M)).Fiber x}
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (a.bundle I (M := M)).Model y (w y)) x) (u : TM x) :
    (Shape.hom a b).connection cov L x u (w x) =
      b.connection cov (fun y => L y (w y)) x u - L x (a.connection cov w x u) :=
  connection_hom_apply cov a b hL hw u

example (a b : Shape)
    {L : ∀ x, (a.bundle I (M := M)).Fiber x →L[ℝ] (b.bundle I (M := M)).Fiber x} {x : M}
    (hL : MDifferentiableAt I
      (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model →L[ℝ] (b.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' ((a.bundle I (M := M)).Model →L[ℝ] (b.bundle I (M := M)).Model)
        y (L y)) x)
    {w : ∀ x, (a.bundle I (M := M)).Fiber x}
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (a.bundle I (M := M)).Model y (w y)) x) (u : TM x) :
    b.connection cov (fun y => L y (w y)) x u =
      (Shape.hom a b).connection cov L x u (w x) + L x (a.connection cov w x u) :=
  connection_apply_section cov a b hL hw u

example (a b : Shape)
    {L : ∀ x, (a.bundle I (M := M)).Fiber x →L[ℝ] (b.bundle I (M := M)).Fiber x} {x : M}
    (hL : MDifferentiableAt I
      (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model →L[ℝ] (b.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' ((a.bundle I (M := M)).Model →L[ℝ] (b.bundle I (M := M)).Model)
        y (L y)) x)
    {w w' : ∀ x, (a.bundle I (M := M)).Fiber x}
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (a.bundle I (M := M)).Model y (w y)) x)
    (hw' : MDifferentiableAt I (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (a.bundle I (M := M)).Model y (w' y)) x)
    (hww' : w x = w' x) (u : TM x) :
    b.connection cov (fun y => L y (w y)) x u - L x (a.connection cov w x u) =
      b.connection cov (fun y => L y (w' y)) x u - L x (a.connection cov w' x u) :=
  connection_hom_correction_eq cov a b hL hw hw' hww' u

example (s : Shape) {T T' : ∀ x, (s.bundle I (M := M)).Fiber x} {x : M}
    (hT : MDifferentiableAt I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T y)) x)
    (hT' : MDifferentiableAt I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T' y)) x) :
    s.connection cov (T + T') x = s.connection cov T x + s.connection cov T' x :=
  connection_add cov s hT hT'

example (s : Shape) {f : M → ℝ} {T : ∀ x, (s.bundle I (M := M)).Fiber x}
    {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hT : MDifferentiableAt I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T y)) x) :
    s.connection cov (f • T) x =
      f x • s.connection cov T x + (mvfderiv I f x).smulRight (T x) :=
  connection_smul cov s hf hT

example (s : Shape) (c : ℝ) {T : ∀ x, (s.bundle I (M := M)).Fiber x}
    {x : M} (hT : MDifferentiableAt I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T y)) x) :
    s.connection cov (c • T) x = c • s.connection cov T x :=
  connection_const_smul cov s c hT

example (s : Shape) {T T' : ∀ x, (s.bundle I (M := M)).Fiber x} {x : M}
    (hT : MDifferentiableAt I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T y)) x)
    (hT' : MDifferentiableAt I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T' y)) x)
    (hTT' : ∀ᶠ y in 𝓝 x, T y = T' y) :
    s.connection cov T x = s.connection cov T' x :=
  connection_congr cov s hT hT' hTT'

variable {cov}

example (hcov : SmoothBundle.Connection.IsLocallyRegular
      (A := SmoothBundle.tangent I (M := M)) cov) (s : Shape) :
    (s.connection cov).IsLocallyRegular :=
  connection_isLocallyRegular hcov s

example (hcov : SmoothBundle.Connection.IsLocallyRegular
      (A := SmoothBundle.tangent I (M := M)) cov) (s : Shape)
    {T : ∀ x, (s.bundle I (M := M)).Fiber x}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model)) ∞
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (s.bundle I (M := M)).Model)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] (s.bundle I (M := M)).Model) y
        (s.connection cov T y)) :=
  contMDiff_connection hcov s hT

example (hcov : SmoothBundle.Connection.IsLocallyRegular
      (A := SmoothBundle.tangent I (M := M)) cov) (s : Shape)
    (T : (s.bundle I (M := M)).Section I) :
    ((Shape.hom .tangent s).bundle I (M := M)).Section I :=
  covariantDerivative hcov s T

example (hcov : SmoothBundle.Connection.IsLocallyRegular
      (A := SmoothBundle.tangent I (M := M)) cov) (s : Shape)
    (T : (s.bundle I (M := M)).Section I)
    (e : Trivialization ((Shape.hom .tangent s).bundle I (M := M)).Model
      (TotalSpace.proj : TotalSpace _ ((Shape.hom .tangent s).bundle I (M := M)).Fiber → M))
    [MemTrivializationAtlas e] :
    ContMDiffOn I 𝓘(ℝ, ((Shape.hom .tangent s).bundle I (M := M)).Model) ∞
      (SmoothBundle.coefficients I _ e (covariantDerivative hcov s T)) e.baseSet :=
  coefficients_covariantDerivative_contMDiffOn hcov s T e

example (hcov : SmoothBundle.Connection.IsLocallyRegular
      (A := SmoothBundle.tangent I (M := M)) cov) (s : Shape)
    (T : (s.bundle I (M := M)).Section I) (x : M) :
    covariantDerivative hcov s T x = s.connection cov T x :=
  covariantDerivative_apply hcov s T x

variable (cov)

example (B : SmoothBilinear (I := I) (M := M)) (x : M) (u v w : TM x) :
    (Shape.covariant 2).connection cov (fun y => B y) x u v w =
      bilinearCovariantDerivative cov B x v w u :=
  connection_covariant_two_apply cov B x u v w

example {R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x}
    (hR : IsSmoothTrilinear R) (x : M) (u v w z : TM x) :
    (Shape.hom .tangent (.hom .tangent (.hom .tangent .tangent))).connection cov R x u v w z =
      trilinearCovariantDerivative cov R hR x v w z u :=
  connection_trilinear_apply cov hR x u v w z

end Shape
end ProjectAinos.SmoothGeometry.Tensor

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "E" => MinkowskiModel d
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

example :
    Tensor.SmoothBundle.Connection.IsLocallyRegular (A := Tensor.SmoothBundle.tangent I (M := M))
      g.leviCivita :=
  g.leviCivita_isLocallyRegular

example (s : Tensor.Shape) (T : (s.bundle I (M := M)).Section I) :
    ((Tensor.Shape.hom .tangent s).bundle I (M := M)).Section I :=
  g.shapeCovariantDerivative s T

example (s : Tensor.Shape) (T : (s.bundle I (M := M)).Section I) (x : M) :
    g.shapeCovariantDerivative s T x = s.connection g.leviCivita T x := rfl

example {α : ∀ x : M, TM x →L[ℝ] ℝ} {x : M}
    (hα : MDifferentiableAt I ((I).prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y (α y)) x)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : x ∈ e.source) (i k : Fin (d + 1)) :
    Tensor.Shape.cotangent.connection g.leviCivita α x (chartField e (Pi.single i 1) x)
        (chartField e (Pi.single k 1) x) =
      mvfderiv I (fun y => α y (chartField e (Pi.single k 1) y)) x
          (chartField e (Pi.single i 1) x) -
        ∑ l, g.chartChristoffel e x l i k * α x (chartField e (Pi.single l 1) x) :=
  g.shapeConnection_cotangent_chart hα he hx i k

example {A : ∀ x : M, TM x →L[ℝ] TM x} {x : M}
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
          chartTangentMap e x (A x (chartField e (Pi.single l 1) x)) j :=
  g.shapeConnection_endomorphism_chart hA he hx i j k

example {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (i j k : Fin (d + 1)) :
    Tensor.Shape.cotangent.connection g.leviCivita (fun y => chartCovector e y j) x
        (chartField e (Pi.single i 1) x) (chartField e (Pi.single k 1) x) =
      -g.chartChristoffel e x j i k :=
  g.shapeConnection_chartCovector_apply he hx i j k

example {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (i j : Fin (d + 1)) :
    Tensor.Shape.cotangent.connection g.leviCivita (fun y => chartCovector e y j) x
        (chartField e (Pi.single i 1) x) =
      -∑ k, g.chartChristoffel e x j i k • chartCovector e x k :=
  g.shapeConnection_chartCovector he hx i j

example {T : ∀ x : M, ((Tensor.Shape.mixed 2 0).bundle I (M := M)).Fiber x} {x : M}
    (hT : MDifferentiableAt I ((I).prod 𝓘(ℝ, ((Tensor.Shape.mixed 2 0).bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' ((Tensor.Shape.mixed 2 0).bundle I (M := M)).Model y (T y)) x)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : x ∈ e.source) (i j k : Fin (d + 1)) :
    (Tensor.Shape.mixed 2 0).connection g.leviCivita T x (chartField e (Pi.single i 1) x)
        (chartCovector e x j) (chartCovector e x k) =
      mvfderiv I (fun y => T y (chartCovector e y j) (chartCovector e y k)) x
          (chartField e (Pi.single i 1) x) +
        ∑ l, g.chartChristoffel e x j i l * T x (chartCovector e x l) (chartCovector e x k) +
        ∑ l, g.chartChristoffel e x k i l * T x (chartCovector e x j) (chartCovector e x l) :=
  g.shapeConnection_contravariant_two_chart hT he hx i j k

example : (Tensor.Shape.covariant 2).connection g.leviCivita (fun y => g.form y) = 0 :=
  g.shapeConnection_form

end ProjectAinos.SmoothGeometry.LorentzMetric

namespace ProjectAinos.SmoothGeometry.ExponentialConformalExample

open TopologicalSpace LorentzMetric CoordinateMetric

local notation "E" => MinkowskiModel 3
local notation "η" => minkowskiForm LorentzConvention.timeNegative 3

example :
    (Tensor.Shape.covariant 2).connection metric.toLorentzMetric.leviCivita
      (fun y => metric.toLorentzMetric.form y) = 0 :=
  metric_shapeConnection_form

example (x y : (⊤ : Opens E)) (u v w : E) :
    mvfderiv 𝓘(ℝ, E) (fun z => metric.toLorentzMetric.form z (chartField (physicalChart x) v z)
        (chartField (physicalChart x) w z)) y (chartField (physicalChart x) u y) =
      2 * u 3 * Real.exp (2 * (y : E) 3) * η v w :=
  metric_mvfderiv_form_chartField x y u v w

example (x y : (⊤ : Opens E)) (j i k : Fin 4) :
    metric.toLorentzMetric.chartChristoffel (physicalChart x) y j i k =
      connection (Pi.single i 1) (Pi.single k 1) j :=
  metric_chartChristoffel x y j i k

example (x y : (⊤ : Opens E)) (i k : Fin 4) :
    Tensor.Shape.cotangent.connection metric.toLorentzMetric.leviCivita
        (fun z => chartCovector (physicalChart x) z 3) y
        (chartField (physicalChart x) (Pi.single i 1) y)
        (chartField (physicalChart x) (Pi.single k 1) y) =
      η (Pi.single i 1) (Pi.single k 1) -
        2 * (Pi.single i 1 : E) 3 * (Pi.single k 1 : E) 3 :=
  metric_shapeConnection_dz x y i k

example (x y : (⊤ : Opens E)) :
    Tensor.Shape.cotangent.connection metric.toLorentzMetric.leviCivita
        (fun z => chartCovector (physicalChart x) z 3) y
        (chartField (physicalChart x) (Pi.single 0 1) y)
        (chartField (physicalChart x) (Pi.single 0 1) y) = -1 :=
  metric_shapeConnection_dz_ne_zero x y

end ProjectAinos.SmoothGeometry.ExponentialConformalExample
