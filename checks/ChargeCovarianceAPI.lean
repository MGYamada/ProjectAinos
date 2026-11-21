/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.ChargeCovarianceIsotropic
import ProjectAinos.GeneralRelativity.StationaryFarField

/-! Public consumers of the four-vector character of the gravitational energy and momentum and of
the stationary far field (Landau–Lifshitz §§96, 105): the flux of a conserved current through
tilted hyperplanes and the wedge estimate, the tensor law of the superpotential and of the total
density under linear changes of the co-ordinates, the transformation `P' = |det L| L⁻¹ P` of the
charges with the decay hypotheses on the wedge and the Lorentz case, Minkowski space and the
boosted isotropic metric as instances, and the linearized stationary field of a conserved
localized source with its mass monopole, current dipole, surface integrals and the comparison
with the Kerr exterior. Default elaborator options are intentional: these checks must not rely on
the implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section

section HyperplaneFlux

open MeasureTheory Set Metric Real Filter

open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.Hyperplane

open Minkowski

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c : ℝ) (v y : E3) :
    ℝ :=
  graphIntegrand J c v y

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c : ℝ) (v : E3) :
    ℝ :=
  graphFlux J c v

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c : ℝ) (v : E3) (R : ℝ) :
    ℝ :=
  graphFluxBall J c v R

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c : ℝ) (y : E3) :
    graphIntegrand J c 0 y = J 0 (vector c y) :=
  graphIntegrand_zero J c y

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c : ℝ) :
    graphFlux J c 0 = ∫ y, J 0 (vector c y) :=
  graphFlux_zero J c

example (t : ℝ) (y : E3) :
    vector t y 1 = y 0 :=
  vector_one t y

example (t : ℝ) (y : E3) :
    vector t y 2 = y 1 :=
  vector_two t y

example (t : ℝ) (y : E3) :
    vector t y 3 = y 2 :=
  vector_three t y

example (v : E3) (α : Fin 3) :
    MinkowskiModel 3 :=
  graphTangent v α

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c : ℝ) (v y : E3) :
    graphIntegrand J c v y = (Matrix.of fun i j : Fin 4 =>
      Fin.cases (J i (vector (c + inner ℝ v y) y)) (fun α => graphTangent v α i) j).det :=
  graphIntegrand_eq_det J c v y

example (c₀ : ℝ) (c₁ : ℝ) (v : E3) (s : ℝ) (y : E3) :
    ℝ :=
  wedgeTime c₀ c₁ v s y

example (c₀ : ℝ) (c₁ : ℝ) (v : E3) (s : ℝ) (y : E3) :
    MinkowskiModel 3 :=
  wedgePoint c₀ c₁ v s y

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c₀ : ℝ) (c₁ : ℝ) (v : E3) (s : ℝ) (y : E3) :
    ℝ :=
  wedgeIntegrand J c₀ c₁ v s y

example (c₀ : ℝ) (c₁ : ℝ) (v : E3) (y : E3) :
    ℝ :=
  wedgeSpeed c₀ c₁ v y

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c₀ : ℝ) (c₁ : ℝ) (v : E3) (s : ℝ) (α : Fin 3) (y : E3) :
    ℝ :=
  wedgeField J c₀ c₁ v s α y

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c₀ : ℝ) (c₁ : ℝ) (v : E3) (s : ℝ) (y : E3) :
    ℝ :=
  wedgeDeriv J c₀ c₁ v s y

example (c₀ : ℝ) (c₁ : ℝ) (v : E3) (y : E3) :
    wedgePoint c₀ c₁ v 0 y = vector c₀ y :=
  wedgePoint_zero c₀ c₁ v y

example (c₀ : ℝ) (c₁ : ℝ) (v : E3) (y : E3) :
    wedgePoint c₀ c₁ v 1 y = vector (c₁ + inner ℝ v y) y :=
  wedgePoint_one c₀ c₁ v y

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c₀ : ℝ) (c₁ : ℝ) (v : E3) (y : E3) :
    wedgeIntegrand J c₀ c₁ v 0 y = J 0 (vector c₀ y) :=
  wedgeIntegrand_zero J c₀ c₁ v y

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c₀ : ℝ) (c₁ : ℝ) (v : E3) (y : E3) :
    wedgeIntegrand J c₀ c₁ v 1 y = graphIntegrand J c₁ v y :=
  wedgeIntegrand_one J c₀ c₁ v y

example (c₀ : ℝ) (c₁ : ℝ) (v : E3) (s : ℝ) (y : E3) :
    wedgePoint c₀ c₁ v s y = Wave.timeSpaceEquiv.symm (wedgeTime c₀ c₁ v s y, y) :=
  wedgePoint_eq c₀ c₁ v s y

example (c₀ : ℝ) (c₁ : ℝ) (v : E3) :
    Continuous fun p : ℝ × E3 => wedgePoint c₀ c₁ v p.1 p.2 :=
  continuous_wedgePoint c₀ c₁ v

example (c₀ : ℝ) (c₁ : ℝ) (v : E3) (s : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun y => wedgePoint c₀ c₁ v s y :=
  contDiff_wedgePoint c₀ c₁ v s

example (c₀ : ℝ) (c₁ : ℝ) (v : E3) {n : WithTop ℕ∞} :
    ContDiff ℝ n (wedgeSpeed c₀ c₁ v) :=
  contDiff_wedgeSpeed c₀ c₁ v

example (c₀ : ℝ) (c₁ : ℝ) (v : E3) (s : ℝ) (y : E3) :
    HasDerivAt (fun s => wedgePoint c₀ c₁ v s y)
      (wedgeSpeed c₀ c₁ v y • (Pi.single 0 1 : MinkowskiModel 3)) s :=
  hasDerivAt_wedgePoint c₀ c₁ v s y

example (c₀ : ℝ) (c₁ : ℝ) (v : E3) (s : ℝ) (y : E3) :
    HasFDerivAt (fun y => wedgePoint c₀ c₁ v s y)
      ((Wave.timeSpaceEquiv.symm : ℝ × E3 →L[ℝ] MinkowskiModel 3).comp
        ((s • innerSL ℝ v).prod (ContinuousLinearMap.id ℝ E3))) y :=
  hasFDerivAt_wedgePoint_space c₀ c₁ v s y

example (a : ℝ) (α : Fin 3) :
    vector a (EuclideanSpace.single α 1) =
      a • (Pi.single 0 1 : MinkowskiModel 3) + Pi.single α.succ 1 :=
  vector_single a α

example (c₀ : ℝ) (c₁ : ℝ) (v : E3) {f : MinkowskiModel 3 → ℝ} {s : ℝ} {y : E3}
    (hf : DifferentiableAt ℝ f (wedgePoint c₀ c₁ v s y)) (α : Fin 3) :
    fderiv ℝ (fun y => f (wedgePoint c₀ c₁ v s y)) y (EuclideanSpace.single α 1) =
      s * v α * fderiv ℝ f (wedgePoint c₀ c₁ v s y) (Pi.single 0 1) +
        fderiv ℝ f (wedgePoint c₀ c₁ v s y) (Pi.single α.succ 1) :=
  fderiv_comp_wedgePoint c₀ c₁ v hf α

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c₀ : ℝ) (c₁ : ℝ) (v : E3) {s : ℝ} {y : E3}
    (hJ : ∀ k, DifferentiableAt ℝ (J k) (wedgePoint c₀ c₁ v s y)) :
    HasDerivAt (fun s => wedgeIntegrand J c₀ c₁ v s y) (wedgeDeriv J c₀ c₁ v s y) s :=
  hasDerivAt_wedgeIntegrand J c₀ c₁ v hJ

example (J : Fin 4 → MinkowskiModel 3 → ℝ) (c₀ : ℝ) (c₁ : ℝ) (v : E3) {s : ℝ} {y : E3}
    (hJ : ∀ k, DifferentiableAt ℝ (J k) (wedgePoint c₀ c₁ v s y))
    (hdiv : ∑ k, fderiv ℝ (J k) (wedgePoint c₀ c₁ v s y) (Pi.single k 1) = 0) :
    Sphere.divergence (wedgeField J c₀ c₁ v s) y = -wedgeDeriv J c₀ c₁ v s y :=
  divergence_wedgeField J c₀ c₁ v hJ hdiv

example {c₀ : ℝ} {c₁ : ℝ} {v : E3} {O : Set (MinkowskiModel 3)} (hO : IsOpen O)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ O) (R : ℝ) :
    ∃ δ > 0, ∀ s ∈ Icc (-δ) (1 + δ), ∀ y ∈ closedBall (0 : E3) R,
      wedgePoint c₀ c₁ v s y ∈ O :=
  exists_wedge_nhds hO hW R

example {J : Fin 4 → MinkowskiModel 3 → ℝ} {c₀ : ℝ} {c₁ : ℝ} {v : E3} {O : Set (MinkowskiModel 3)}
    (hJ : ∀ k, ContinuousOn (J k) O) :
    ContinuousOn (fun p : ℝ × E3 => wedgeIntegrand J c₀ c₁ v p.1 p.2)
      {p | wedgePoint c₀ c₁ v p.1 p.2 ∈ O} :=
  continuousOn_wedgeIntegrand hJ

example {J : Fin 4 → MinkowskiModel 3 → ℝ} {c₀ : ℝ} {c₁ : ℝ} {v : E3} {O : Set (MinkowskiModel 3)}
    (hO : IsOpen O) (hJ : ∀ k, ContDiffOn ℝ 1 (J k) O) :
    ContinuousOn (fun p : ℝ × E3 => wedgeDeriv J c₀ c₁ v p.1 p.2)
      {p | wedgePoint c₀ c₁ v p.1 p.2 ∈ O} :=
  continuousOn_wedgeDeriv hO hJ

example {J : Fin 4 → MinkowskiModel 3 → ℝ} {c₀ : ℝ} {c₁ : ℝ} {v : E3} {O : Set (MinkowskiModel 3)}
    (hO : IsOpen O) (hJ : ∀ k, ContDiffOn ℝ 1 (J k) O)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ O) (R : ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => ∫ y in ball (0 : E3) R, wedgeIntegrand J c₀ c₁ v s y)
      (∫ y in ball (0 : E3) R, wedgeDeriv J c₀ c₁ v s y) s :=
  hasDerivAt_integral_ball_wedge hO hJ hW R hs

example {J : Fin 4 → MinkowskiModel 3 → ℝ} {c₀ : ℝ} {c₁ : ℝ} {v : E3} {O : Set (MinkowskiModel 3)}
    (hO : IsOpen O) (hJ : ∀ k, ContDiffOn ℝ 1 (J k) O)
    (hdiv : ∀ z ∈ O, ∑ k, fderiv ℝ (J k) z (Pi.single k 1) = 0)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ O) {R : ℝ} (hR : 0 ≤ R) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ y in ball (0 : E3) R, wedgeDeriv J c₀ c₁ v s y =
      -Sphere.flux (wedgeField J c₀ c₁ v s) R :=
  integral_ball_wedgeDeriv hO hJ hdiv hW hR hs

example {J : Fin 4 → MinkowskiModel 3 → ℝ} {c₀ : ℝ} {c₁ : ℝ} {v : E3} {O : Set (MinkowskiModel 3)}
    (hO : IsOpen O) (hJ : ∀ k, ContDiffOn ℝ 1 (J k) O)
    (hdiv : ∀ z ∈ O, ∑ k, fderiv ℝ (J k) z (Pi.single k 1) = 0)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ O) {R B : ℝ} (hR : 0 ≤ R)
    (hB : ∀ s ∈ Icc (0 : ℝ) 1, |Sphere.flux (wedgeField J c₀ c₁ v s) R| ≤ B) :
    |(∫ y in ball (0 : E3) R, wedgeIntegrand J c₀ c₁ v 1 y) -
      ∫ y in ball (0 : E3) R, wedgeIntegrand J c₀ c₁ v 0 y| ≤ B :=
  abs_integral_ball_wedge_sub_le hO hJ hdiv hW hR hB

example {J : Fin 4 → MinkowskiModel 3 → ℝ} {c₀ : ℝ} {c₁ : ℝ} {v : E3} {R₀ K : ℝ}
    (hdecay : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, R₀ ≤ ‖y‖ → ∀ k,
      |J k (wedgePoint c₀ c₁ v s y)| ≤ K / ‖y‖ ^ 4)
    {s R : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hR : 0 < R) (hRR : R₀ ≤ R) :
    |Sphere.flux (wedgeField J c₀ c₁ v s) R| ≤
      12 * π * ((|c₁ - c₀| + ‖v‖ * R) * K) / R ^ 2 :=
  abs_flux_wedgeField_le hdecay hs hR hRR

example {J : Fin 4 → MinkowskiModel 3 → ℝ} {c₀ : ℝ} {c₁ : ℝ} {v : E3} {O : Set (MinkowskiModel 3)}
    (hO : IsOpen O) (hJ : ∀ k, ContDiffOn ℝ 1 (J k) O)
    (hdiv : ∀ z ∈ O, ∑ k, fderiv ℝ (J k) z (Pi.single k 1) = 0)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ O) {R₀ K : ℝ}
    (hdecay : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, R₀ ≤ ‖y‖ → ∀ k,
      |J k (wedgePoint c₀ c₁ v s y)| ≤ K / ‖y‖ ^ 4)
    {R : ℝ} (hR : 0 < R) (hRR : R₀ ≤ R) :
    |graphFluxBall J c₁ v R - ∫ y in ball (0 : E3) R, J 0 (vector c₀ y)| ≤
      12 * π * ((|c₁ - c₀| + ‖v‖ * R) * K) / R ^ 2 :=
  abs_graphFluxBall_sub_le hO hJ hdiv hW hdecay hR hRR

example {f : E3 → ℝ} (hf : Integrable f) :
    Tendsto (fun R => ∫ y in ball (0 : E3) R, f y) atTop (𝓝 (∫ y, f y)) :=
  tendsto_integral_ball hf

example {J : Fin 4 → MinkowskiModel 3 → ℝ} {c₀ : ℝ} {c₁ : ℝ} {v : E3} {O : Set (MinkowskiModel 3)}
    (hO : IsOpen O) (hJ : ∀ k, ContDiffOn ℝ 1 (J k) O)
    (hdiv : ∀ z ∈ O, ∑ k, fderiv ℝ (J k) z (Pi.single k 1) = 0)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ O) {R₀ K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, R₀ ≤ ‖y‖ → ∀ k,
      |J k (wedgePoint c₀ c₁ v s y)| ≤ K / ‖y‖ ^ 4)
    (h₀ : Integrable fun y : E3 => J 0 (vector c₀ y)) (h₁ : Integrable (graphIntegrand J c₁ v)) :
    ∫ y, J 0 (vector c₀ y) = graphFlux J c₁ v :=
  integral_eq_graphFlux hO hJ hdiv hW hK hdecay h₀ h₁

end ProjectAinos.SmoothGeometry.Hyperplane

end HyperplaneFlux

section PseudotensorCovariance

open Set Filter TopologicalSpace

open scoped Topology ContDiff Matrix

namespace ProjectAinos.SmoothGeometry

namespace CoordinateMetric

example {d : ℕ} (L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d :=
  matrixMap L

example {d : ℕ} (L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) :
    matrixMap L x = L *ᵥ x :=
  matrixMap_apply L x

example {d : ℕ} (U : Opens (MinkowskiModel d)) (L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Opens (MinkowskiModel d) :=
  pullbackOpens U L

example {d : ℕ} {U : Opens (MinkowskiModel d)} {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} :
    x ∈ pullbackOpens U L ↔ L *ᵥ x ∈ U :=
  mem_pullbackOpens

example {d : ℕ} (L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hL : L.det ≠ 0) :
    MinkowskiModel d ≃L[ℝ] MinkowskiModel d :=
  matrixEquiv L hL

example {d : ℕ} (L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hL : L.det ≠ 0) (x : MinkowskiModel d) :
    matrixEquiv L hL x = L *ᵥ x :=
  matrixEquiv_apply L hL x

example {n : ℕ} (f g : Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, f a b) * (∑ c, ∑ e, g c e) = ∑ a, ∑ b, ∑ c, ∑ e, f a b * g c e :=
  sum_mul_sum_four f g

example {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ e, ∑ a, ∑ b, ∑ c, F e a b c = ∑ a, ∑ b, ∑ c, ∑ e, F e a b c :=
  sum_comm_four F

example {n : ℕ} (F : Fin n → Fin n → Fin n → ℝ) :
    ∑ e, ∑ a, ∑ b, F e a b = ∑ a, ∑ b, ∑ e, F e a b :=
  sum_comm_three F

example {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
    (L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hL : L.det ≠ 0) :
    CoordinateMetric σ d (pullbackOpens U L) :=
  linearPullback g L hL

example {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
    {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {hL : L.det ≠ 0} (x v w : MinkowskiModel d) :
    (g.linearPullback L hL).form x v w = g.form (L *ᵥ x) (L *ᵥ v) (L *ᵥ w) :=
  form_linearPullback g x v w

example {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
    {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {hL : L.det ≠ 0} (x : MinkowskiModel d) :
    (g.linearPullback L hL).coefficient x = Lᵀ * g.coefficient (L *ᵥ x) * L :=
  coefficient_linearPullback g x

example {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
    {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {hL : L.det ≠ 0} (x : MinkowskiModel d)
    (i k : Fin (d + 1)) :
    ((g.linearPullback L hL).coefficient x)⁻¹ i k =
      ∑ a, ∑ b, L⁻¹ i a * L⁻¹ k b * (g.coefficient (L *ᵥ x))⁻¹ a b :=
  inv_coefficient_linearPullback g x i k

example {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
    {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {hL : L.det ≠ 0} (x : MinkowskiModel d) :
    densityOf (g.linearPullback L hL).coefficient x ^ 2 =
      L.det ^ 2 * densityOf g.coefficient (L *ᵥ x) ^ 2 :=
  densityOf_sq_linearPullback g x

example {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
    {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {hL : L.det ≠ 0} (x : MinkowskiModel d)
    (i k l m : Fin (d + 1)) :
    (g.linearPullback L hL).superpotentialDensity x i k l m =
      L.det ^ 2 * ∑ e, L⁻¹ m e * ∑ a, ∑ b, ∑ c,
        L⁻¹ i a * L⁻¹ k b * L⁻¹ l c * g.superpotentialDensity (L *ᵥ x) a b c e :=
  superpotentialDensity_linearPullback g x i k l m

example {d : ℕ} {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {f : MinkowskiModel d → ℝ}
    {x : MinkowskiModel d} (hf : DifferentiableAt ℝ f (L *ᵥ x)) (m : Fin (d + 1)) :
    fderiv ℝ (fun w => f (L *ᵥ w)) x (Pi.single m 1) =
      ∑ n, L n m * fderiv ℝ f (L *ᵥ x) (Pi.single n 1) :=
  fderiv_comp_mulVec hf m

example {d : ℕ} {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (hL : L.det ≠ 0) (y : Fin (d + 1) → ℝ)
    (e : Fin (d + 1)) :
    ∑ m, L⁻¹ m e * ∑ n, L n m * y n = y e :=
  sum_inv_mul_sum hL y e

example {d : ℕ} {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (hL : L.det ≠ 0)
    {F Λ : Fin (d + 1) → MinkowskiModel d → ℝ} {x : MinkowskiModel d}
    (hΛ : ∀ e, DifferentiableAt ℝ (Λ e) (L *ᵥ x))
    (hF : ∀ m, F m =ᶠ[𝓝 x] fun w => ∑ e, L⁻¹ m e * Λ e (L *ᵥ w)) :
    ∑ m, fderiv ℝ (F m) x (Pi.single m 1) = ∑ e, fderiv ℝ (Λ e) (L *ᵥ x) (Pi.single e 1) :=
  sum_fderiv_contract hL hΛ hF

example {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
    {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {hL : L.det ≠ 0} {x : MinkowskiModel d}
    (hx : x ∈ pullbackOpens U L) (i k l : Fin (d + 1)) :
    (g.linearPullback L hL).superpotential x i k l =
      L.det ^ 2 * ∑ a, ∑ b, ∑ c, L⁻¹ i a * L⁻¹ k b * L⁻¹ l c * g.superpotential (L *ᵥ x) a b c :=
  superpotential_linearPullback g hx i k l

example {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
    {z : MinkowskiModel d} (hz : z ∈ U) (i : Fin (d + 1)) :
    ∑ k, fderiv ℝ (fun w => g.totalDensity w i k) z (Pi.single k 1) = 0 :=
  sum_fderiv_totalDensity g hz i

example {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
    {L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {hL : L.det ≠ 0} {x : MinkowskiModel d}
    (hx : x ∈ pullbackOpens U L) (i k : Fin (d + 1)) :
    (g.linearPullback L hL).totalDensity x i k =
      L.det ^ 2 * ∑ a, ∑ b, L⁻¹ i a * L⁻¹ k b * g.totalDensity (L *ᵥ x) a b :=
  totalDensity_linearPullback g hx i k

end CoordinateMetric

end ProjectAinos.SmoothGeometry

end PseudotensorCovariance

section ChargeCovariance

open MeasureTheory Set Metric Real Filter TopologicalSpace

open scoped Topology ContDiff Matrix

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry SmoothGeometry.CoordinateMetric SmoothGeometry.Minkowski
  SmoothGeometry.Hyperplane

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (L : Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) :
    ℝ :=
  tiltTime L t

example (L : Matrix (Fin 4) (Fin 4) ℝ) :
    E3 :=
  tiltSlope L

example (L : Matrix (Fin 4) (Fin 4) ℝ) (β : Fin 3) :
    tiltSlope L β = -(L⁻¹ 0 β.succ / L⁻¹ 0 0) :=
  tiltSlope_apply L β

example (L : Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (y : E3) :
    E3 :=
  tiltSpace L t y

example (L : Matrix (Fin 4) (Fin 4) ℝ) :
    E3 →L[ℝ] E3 :=
  tiltLinear L

example (L : Matrix (Fin 4) (Fin 4) ℝ) (y : E3) :
    tiltLinear L y = space (L *ᵥ vector 0 y) :=
  tiltLinear_apply L y

example (t s : ℝ) (y z : E3) :
    vector t y + vector s z = (vector (t + s) (y + z) : MinkowskiModel 3) :=
  vector_add_vector t s y z

example (L : Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (y : E3) :
    tiltSpace L t y = tiltLinear L y + tiltSpace L t 0 :=
  tiltSpace_eq L t y

example (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det ≠ 0) (hM : L⁻¹ 0 0 ≠ 0) (t : ℝ) (y : E3) :
    L *ᵥ vector t y = vector (tiltTime L t + inner ℝ (tiltSlope L) (tiltSpace L t y))
      (tiltSpace L t y) :=
  mulVec_vector_eq L hL hM t y

example (L : Matrix (Fin 4) (Fin 4) ℝ) :
    LinearMap.det (tiltLinear L : E3 →ₗ[ℝ] E3) = (L.submatrix Fin.succ Fin.succ).det :=
  det_tiltLinear L

example (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det ≠ 0) :
    (L.submatrix Fin.succ Fin.succ).det = L.det * L⁻¹ 0 0 :=
  det_submatrix_succ L hL

example {A : E3 →L[ℝ] E3} (hA : LinearMap.det (A : E3 →ₗ[ℝ] E3) ≠ 0) (q : E3) (G : E3 → ℝ) :
    ∫ y, G (A y + q) = |LinearMap.det (A : E3 →ₗ[ℝ] E3)|⁻¹ * ∫ z, G z :=
  integral_comp_affine hA q G

example {A : E3 →L[ℝ] E3} (hA : LinearMap.det (A : E3 →ₗ[ℝ] E3) ≠ 0) (q : E3) {G : E3 → ℝ}
    (hG : Integrable G) :
    Integrable fun y => G (A y + q) :=
  integrable_comp_affine hA q hG

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} (g : CoordinateMetric σ 3 U)
    (a : Fin 4) :
    Fin 4 → MinkowskiModel 3 → ℝ :=
  totalCurrent g a

example {L : Matrix (Fin 4) (Fin 4) ℝ} (hM : L⁻¹ 0 0 ≠ 0) (c : ℝ) (T : Fin 4 → ℝ) :
    ∑ b, c * L⁻¹ 0 b * T b =
      c * (L⁻¹ 0 0 * (T 0 - ∑ α : Fin 3, tiltSlope L α * T α.succ)) :=
  sum_inv_zero_mul hM c T

example {L : Matrix (Fin 4) (Fin 4) ℝ} {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)}
    (g : CoordinateMetric σ 3 U) (hL : L.det ≠ 0) (hM : L⁻¹ 0 0 ≠ 0) {t : ℝ} {y : E3}
    (hy : L *ᵥ vector t y ∈ U) (i : Fin 4) :
    (g.linearPullback L hL).totalDensity (vector t y) i 0 =
      L.det ^ 2 * ∑ a, L⁻¹ i a * (L⁻¹ 0 0 *
        graphIntegrand (totalCurrent g a) (tiltTime L t) (tiltSlope L) (tiltSpace L t y)) :=
  totalDensity_linearPullback_slice g hL hM hy i

example {L : Matrix (Fin 4) (Fin 4) ℝ} {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)}
    (g : CoordinateMetric σ 3 U) (hL : L.det ≠ 0) (hM : 0 < L⁻¹ 0 0) {t : ℝ}
    (hU : ∀ y, L *ᵥ vector t y ∈ U)
    (hint : ∀ a, Integrable (graphIntegrand (totalCurrent g a) (tiltTime L t) (tiltSlope L)))
    (i : Fin 4) :
    (Integrable fun y => (g.linearPullback L hL).totalDensity (vector t y) i 0) ∧
      ∫ y, (g.linearPullback L hL).totalDensity (vector t y) i 0 =
        |L.det| * ∑ a, L⁻¹ i a * graphFlux (totalCurrent g a) (tiltTime L t) (tiltSlope L) :=
  integral_totalDensity_linearPullback g hL hM hU hint i

example {L : Matrix (Fin 4) (Fin 4) ℝ} {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)}
    (g : CoordinateMetric σ 3 U) (hL : L.det ≠ 0) (hM : 0 < L⁻¹ 0 0) (t c₀ : ℝ)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ (tiltTime L t) (tiltSlope L) s y ∈ U) {R₀ K : ℝ}
    (hK : 0 ≤ K)
    (hdecay : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, R₀ ≤ ‖y‖ → ∀ a k,
      |g.totalDensity (wedgePoint c₀ (tiltTime L t) (tiltSlope L) s y) a k| ≤ K / ‖y‖ ^ 4)
    (i : Fin 4) :
    charge (g.linearPullback L hL) t i = |L.det| * ∑ a, L⁻¹ i a * charge g c₀ a :=
  charge_linearPullback g hL hM t c₀ hW hK hdecay i

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} (g : CoordinateMetric σ 3 U)
    (z : MinkowskiModel 3) (r C : ℝ) :
    Prop :=
  GalileanBoundsAt g z r C

namespace GalileanBoundsAt

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric σ 3 U}
    {z : MinkowskiModel 3} {r : ℝ} {C : ℝ} (h : GalileanBoundsAt g z r C) (hr : 0 < r)
    (hC : 8 * C ≤ r) (a b : Fin 4) :
    |g.coefficient z a b - minkowskiCoefficient σ a b| ≤ 1 / 8 :=
  coefficient_near h hr hC a b

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric σ 3 U}
    {z : MinkowskiModel 3} {r : ℝ} {C : ℝ} (h : GalileanBoundsAt g z r C) (hr : 0 < r)
    (hC : 8 * C ≤ r) (a b : Fin 4) :
    |(g.coefficient z)⁻¹ a b| ≤ 2 :=
  abs_inv_le h hr hC a b

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric σ 3 U}
    {z : MinkowskiModel 3} {r : ℝ} {C : ℝ} (h : GalileanBoundsAt g z r C) (hr : 0 < r)
    (hC : 8 * C ≤ r) :
    densityOf g.coefficient z ^ 2 ≤ 384 :=
  densityOf_sq_le h hr hC

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric σ 3 U}
    {z : MinkowskiModel 3} {r : ℝ} {C : ℝ} (h : GalileanBoundsAt g z r C) (hr : 0 < r)
    (hC : 8 * C ≤ r) (k i j : Fin 4) :
    |christoffelOf g.coefficient z k i j| ≤ 12 * C / r ^ 2 :=
  abs_christoffelOf_le h hr hC k i j

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric σ 3 U}
    {z : MinkowskiModel 3} {r : ℝ} {C : ℝ} (h : GalileanBoundsAt g z r C) (hr : 0 < r)
    (hC : 8 * C ≤ r) (i k : Fin 4) :
    |g.pseudotensor z i k| ≤ 1327104 * C ^ 2 / r ^ 4 :=
  abs_pseudotensor_le h hr hC i k

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric σ 3 U}
    {z : MinkowskiModel 3} {r : ℝ} {C : ℝ} (h : GalileanBoundsAt g z r C) (hr : 0 < r)
    (hC : 8 * C ≤ r) {κ : ℝ} {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {i k : Fin 4} (hm : T z i k = 0) :
    |g.totalDensity z i k| ≤ decayConstant C / r ^ 4 :=
  abs_totalDensity_le h hr hC hT hm

end GalileanBoundsAt

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric σ 3 U}
    {t R₀ C : ℝ} (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3} (hx : R₀ ≤ ‖x‖) :
    GalileanBoundsAt g (vector t x) ‖x‖ C :=
  IsAsymptoticallyGalileanAt.galileanBoundsAt h hx

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} (g : CoordinateMetric σ 3 U)
    (c₀ c₁ : ℝ) (v : E3) (R₀ C : ℝ) :
    Prop :=
  IsGalileanOnWedge g c₀ c₁ v R₀ C

example {σ : LorentzConvention} {g : CoordinateMetric σ 3 ⊤} {R₀ C : ℝ}
    (h : IsAsymptoticallyGalilean g R₀ C) (c₀ c₁ : ℝ) (v : E3) :
    IsGalileanOnWedge g c₀ c₁ v R₀ C :=
  IsAsymptoticallyGalilean.isGalileanOnWedge h c₀ c₁ v

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} {g : CoordinateMetric σ 3 U}
    {c₀ c₁ : ℝ} {v : E3} {R₀ C : ℝ} (h : IsGalileanOnWedge g c₀ c₁ v R₀ C) {κ : ℝ}
    {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {Rm : ℝ}
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, Rm ≤ ‖y‖ → ∀ a k, T (wedgePoint c₀ c₁ v s y) a k = 0) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, max (max R₀ (8 * C)) Rm ≤ ‖y‖ → ∀ a k,
      |g.totalDensity (wedgePoint c₀ c₁ v s y) a k| ≤ decayConstant C / ‖y‖ ^ 4 :=
  IsGalileanOnWedge.abs_totalDensity_le h hT hm

example {L : Matrix (Fin 4) (Fin 4) ℝ} {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)}
    {g : CoordinateMetric σ 3 U} {κ : ℝ} {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) (hL : L.det ≠ 0) (hM : 0 < L⁻¹ 0 0)
    (t c₀ : ℝ) {R₀ C Rm : ℝ} (hg : IsGalileanOnWedge g c₀ (tiltTime L t) (tiltSlope L) R₀ C)
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, Rm ≤ ‖y‖ → ∀ a k,
      T (wedgePoint c₀ (tiltTime L t) (tiltSlope L) s y) a k = 0)
    (i : Fin 4) :
    charge (g.linearPullback L hL) t i = |L.det| * ∑ a, L⁻¹ i a * charge g c₀ a :=
  charge_linearPullback_of_einstein hT hL hM t c₀ hg hm i

example (σ : LorentzConvention) :
    minkowskiCoefficient σ * minkowskiCoefficient σ = 1 :=
  minkowskiCoefficient_mul_self σ

example {L : Matrix (Fin 4) (Fin 4) ℝ} {σ : LorentzConvention}
    (hLor : Lᵀ * minkowskiCoefficient σ * L = minkowskiCoefficient σ) :
    L.det ^ 2 = 1 :=
  lorentz_det_sq hLor

example {L : Matrix (Fin 4) (Fin 4) ℝ} {σ : LorentzConvention}
    (hLor : Lᵀ * minkowskiCoefficient σ * L = minkowskiCoefficient σ) :
    L⁻¹ = minkowskiCoefficient σ * Lᵀ * minkowskiCoefficient σ :=
  lorentz_inv hLor

example {L : Matrix (Fin 4) (Fin 4) ℝ} {σ : LorentzConvention}
    (hLor : Lᵀ * minkowskiCoefficient σ * L = minkowskiCoefficient σ) :
    L⁻¹ 0 0 = L 0 0 :=
  lorentz_inv_zero_zero hLor

example {L : Matrix (Fin 4) (Fin 4) ℝ} {σ : LorentzConvention}
    (hLor : Lᵀ * minkowskiCoefficient σ * L = minkowskiCoefficient σ) :
    L.det ≠ 0 :=
  lorentz_det_ne_zero hLor

example {L : Matrix (Fin 4) (Fin 4) ℝ} {σ : LorentzConvention}
    (hLor : Lᵀ * minkowskiCoefficient σ * L = minkowskiCoefficient σ) :
    |L.det| = 1 :=
  lorentz_abs_det hLor

example {L : Matrix (Fin 4) (Fin 4) ℝ} {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)}
    (g : CoordinateMetric σ 3 U) (hLor : Lᵀ * minkowskiCoefficient σ * L = minkowskiCoefficient σ)
    (hL : L.det ≠ 0) (h00 : 0 < L 0 0) (t c₀ : ℝ)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ (tiltTime L t) (tiltSlope L) s y ∈ U) {R₀ K : ℝ}
    (hK : 0 ≤ K)
    (hdecay : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, R₀ ≤ ‖y‖ → ∀ a k,
      |g.totalDensity (wedgePoint c₀ (tiltTime L t) (tiltSlope L) s y) a k| ≤ K / ‖y‖ ^ 4)
    (i : Fin 4) :
    charge (g.linearPullback L hL) t i = ∑ a, L⁻¹ i a * charge g c₀ a :=
  charge_lorentz g hLor hL h00 t c₀ hW hK hdecay i

example {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)} {z : MinkowskiModel 3} (hz : z ∈ U)
    (i k : Fin 4) :
    (CoordinateMetric.minkowski σ 3 U).totalDensity z i k = 0 :=
  totalDensity_minkowski hz i k

example (σ : LorentzConvention) (c₀ c₁ : ℝ) (v : E3) :
    IsGalileanOnWedge (CoordinateMetric.minkowski σ 3 ⊤) c₀ c₁ v 1 0 :=
  isGalileanOnWedge_minkowski σ c₀ c₁ v

example {L : Matrix (Fin 4) (Fin 4) ℝ} (σ : LorentzConvention) (hL : L.det ≠ 0) (hM : 0 < L⁻¹ 0 0)
    (t c₀ : ℝ) (i : Fin 4) :
    charge ((CoordinateMetric.minkowski σ 3 ⊤).linearPullback L hL) t i = 0 :=
  charge_linearPullback_minkowski σ hL hM t c₀ i

end ProjectAinos.GeneralRelativity

end ChargeCovariance

section ChargeCovarianceIsotropic

open MeasureTheory Set Metric Real Filter TopologicalSpace

open scoped Topology ContDiff Matrix

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry SmoothGeometry.CoordinateMetric SmoothGeometry.Minkowski
  SmoothGeometry.Hyperplane

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example :
    space (Pi.single 0 1 : MinkowskiModel 3) = 0 :=
  space_single_zero

example {f : E3 → ℝ} {z : MinkowskiModel 3} (hf : DifferentiableAt ℝ f (space z))
    (v : MinkowskiModel 3) :
    fderiv ℝ (fun w => f (space w)) z v = fderiv ℝ f (space z) (space v) :=
  fderiv_comp_space hf v

example (M R₀ : ℝ) (x : E3) :
    ℝ :=
  isoPotential M R₀ x

example (M R₀ : ℝ) (x : E3) :
    ℝ :=
  isoQ₁ M R₀ x

example (M R₀ : ℝ) (x : E3) :
    ℝ :=
  isoQ₂ M R₀ x

example (i k : Fin 4) (β γ : Fin 3) :
    ℝ :=
  isoCoeffOne i k β γ

example (i k : Fin 4) (β γ : Fin 3) :
    ℝ :=
  isoCoeffTwo i k β γ

example (M R₀ : ℝ) (i k : Fin 4) (β γ : Fin 3) (x : E3) :
    ℝ :=
  isoLam M R₀ i k β γ x

example {M : ℝ} {R₀ : ℝ} (σ : LorentzConvention) (hM : 0 ≤ M) (hR : 2 * M < R₀)
    (z : MinkowskiModel 3) (i : Fin 4) :
    isotropicCoefficient σ M R₀ z i ≠ 0 :=
  isotropicCoefficient_ne_zero σ hM hR z i

example {M : ℝ} {R₀ : ℝ} (σ : LorentzConvention) (hM : 0 ≤ M) (hR : 2 * M < R₀)
    (z : MinkowskiModel 3) (i : Fin 4) (β : Fin 3) :
    |∏ j, isotropicCoefficient σ M R₀ z j| * (isotropicCoefficient σ M R₀ z i)⁻¹ *
        (isotropicCoefficient σ M R₀ z β.succ)⁻¹ =
      if i = 0 then isoQ₁ M R₀ (space z) else isoQ₂ M R₀ (space z) :=
  iso_density_inv σ hM hR z i β

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀}
    (z : MinkowskiModel 3) (i k : Fin 4) (β γ : Fin 3) :
    (isotropicMetric σ M R₀ hM hR).superpotentialDensity z i k β.succ γ.succ =
      isoLam M R₀ i k β γ (space z) :=
  superpotentialDensity_isotropicMetric_spatial z i k β γ

example {M : ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀) (y : E3) :
    HasFDerivAt (isoPotential M R₀) ((2 * M) • fderiv ℝ (isotropicProfile R₀) y) y :=
  hasFDerivAt_isoPotential hR₀ y

example {M : ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀) (y u : E3) :
    fderiv ℝ (isoQ₁ M R₀) y u =
      -(2 * (1 + isoPotential M R₀ y) * (2 * M * fderiv ℝ (isotropicProfile R₀) y u)) :=
  fderiv_isoQ₁ hR₀ y u

example {M : ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀) (y u : E3) :
    fderiv ℝ (isoQ₂ M R₀) y u =
      -(2 * isoPotential M R₀ y * (2 * M * fderiv ℝ (isotropicProfile R₀) y u)) :=
  fderiv_isoQ₂ hR₀ y u

example {R₀ : ℝ} (hR₀ : 0 < R₀) (x u : E3) :
    DifferentiableAt ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y u) x :=
  differentiableAt_fderiv_profile hR₀ x u

example {M : ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀) (x u v : E3) :
    fderiv ℝ (fun y => fderiv ℝ (isoQ₁ M R₀) y u) x v =
      -(2 * (2 * M * fderiv ℝ (isotropicProfile R₀) x v) *
          (2 * M * fderiv ℝ (isotropicProfile R₀) x u) +
        2 * (1 + isoPotential M R₀ x) *
          (2 * M * fderiv ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y u) x v)) :=
  fderiv_fderiv_isoQ₁ hR₀ x u v

example {M : ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀) (x u v : E3) :
    fderiv ℝ (fun y => fderiv ℝ (isoQ₂ M R₀) y u) x v =
      -(2 * (2 * M * fderiv ℝ (isotropicProfile R₀) x v) *
          (2 * M * fderiv ℝ (isotropicProfile R₀) x u) +
        2 * isoPotential M R₀ x *
          (2 * M * fderiv ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y u) x v)) :=
  fderiv_fderiv_isoQ₂ hR₀ x u v

example {M : ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ContDiff ℝ ∞ (isoQ₁ M R₀) :=
  contDiff_isoQ₁ hR₀

example {M : ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ContDiff ℝ ∞ (isoQ₂ M R₀) :=
  contDiff_isoQ₂ hR₀

example {M : ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀) (x u : E3) :
    DifferentiableAt ℝ (fun y => fderiv ℝ (isoQ₁ M R₀) y u) x :=
  differentiableAt_fderiv_isoQ₁ hR₀ x u

example {M : ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀) (x u : E3) :
    DifferentiableAt ℝ (fun y => fderiv ℝ (isoQ₂ M R₀) y u) x :=
  differentiableAt_fderiv_isoQ₂ hR₀ x u

example {M : ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀) (i k : Fin 4) (β γ : Fin 3) (x u : E3) :
    fderiv ℝ (isoLam M R₀ i k β γ) x u = isoCoeffOne i k β γ * fderiv ℝ (isoQ₁ M R₀) x u +
      isoCoeffTwo i k β γ * fderiv ℝ (isoQ₂ M R₀) x u :=
  fderiv_isoLam hR₀ i k β γ x u

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀}
    (z : MinkowskiModel 3) :
    (isotropicMetric σ M R₀ hM hR).coefficient z =
      (isotropicMetric σ M R₀ hM hR).coefficient (vector 0 (space z)) :=
  coefficient_isotropicMetric_static z

example (σ : LorentzConvention) (M R₀ : ℝ) (hM : 0 ≤ M) (hR : 2 * M < R₀) (i k l m : Fin 4) (x : E3)
    :
    ℝ :=
  isoLamS σ M R₀ hM hR i k l m x

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀}
    (z : MinkowskiModel 3) (i k l m : Fin 4) :
    (isotropicMetric σ M R₀ hM hR).superpotentialDensity z i k l m =
      isoLamS σ M R₀ hM hR i k l m (space z) :=
  superpotentialDensity_isotropicMetric_static z i k l m

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀} (i k l m : Fin 4) :
    ContDiff ℝ ∞ (isoLamS σ M R₀ hM hR i k l m) :=
  contDiff_isoLamS i k l m

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀} (i k : Fin 4)
    (β γ : Fin 3) :
    isoLamS σ M R₀ hM hR i k β.succ γ.succ = isoLam M R₀ i k β γ :=
  isoLamS_spatial i k β γ

example (σ : LorentzConvention) (M R₀ : ℝ) (hM : 0 ≤ M) (hR : 2 * M < R₀) (i k l : Fin 4) (x : E3) :
    ℝ :=
  isoHS σ M R₀ hM hR i k l x

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀}
    (z : MinkowskiModel 3) (i k l : Fin 4) :
    (isotropicMetric σ M R₀ hM hR).superpotential z i k l = isoHS σ M R₀ hM hR i k l (space z) :=
  superpotential_isotropicMetric_static z i k l

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀} (i k l : Fin 4) :
    ContDiff ℝ ∞ (isoHS σ M R₀ hM hR i k l) :=
  contDiff_isoHS i k l

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀}
    (z : MinkowskiModel 3) (i k : Fin 4) :
    (isotropicMetric σ M R₀ hM hR).totalDensity z i k = (1 / 2) * ∑ β : Fin 3,
      fderiv ℝ (isoHS σ M R₀ hM hR i k β.succ) (space z) (EuclideanSpace.single β 1) :=
  totalDensity_isotropicMetric z i k

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀}
    (z : MinkowskiModel 3) (i k : Fin 4) :
    (isotropicMetric σ M R₀ hM hR).totalDensity z i k = (1 / 2) * ∑ β : Fin 3, ∑ γ : Fin 3,
      (isoCoeffOne i k β γ * fderiv ℝ (fun y => fderiv ℝ (isoQ₁ M R₀) y
          (EuclideanSpace.single γ 1)) (space z) (EuclideanSpace.single β 1) +
        isoCoeffTwo i k β γ * fderiv ℝ (fun y => fderiv ℝ (isoQ₂ M R₀) y
          (EuclideanSpace.single γ 1)) (space z) (EuclideanSpace.single β 1)) :=
  totalDensity_isotropicMetric_eq z i k

example (β γ : Fin 3) :
    isoCoeffOne 0 0 β γ = if β = γ then 1 else 0 :=
  isoCoeffOne_zero_zero β γ

example (β γ : Fin 3) :
    isoCoeffTwo 0 0 β γ = 0 :=
  isoCoeffTwo_zero_zero β γ

example {i k : Fin 4} (h : ¬(i = 0 ∧ k = 0)) (β γ : Fin 3) :
    isoCoeffOne i k β γ = 0 :=
  isoCoeffOne_eq_zero h β γ

example (i k : Fin 4) (β γ : Fin 3) :
    |isoCoeffTwo i k β γ| ≤ 1 :=
  abs_isoCoeffTwo_le i k β γ

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀}
    {z : MinkowskiModel 3} (hz : 2 * R₀ < ‖space z‖) :
    (isotropicMetric σ M R₀ hM hR).totalDensity z 0 0 = -(4 * M ^ 2 / ‖space z‖ ^ 4) :=
  totalDensity_isotropicMetric_zero_zero hz

example (x : E3) (γ : Fin 3) :
    |inner ℝ x (EuclideanSpace.single γ (1 : ℝ))| ≤ ‖x‖ :=
  abs_inner_single_le x γ

example (β γ : Fin 3) :
    |inner ℝ (EuclideanSpace.single β (1 : ℝ)) (EuclideanSpace.single γ (1 : ℝ))| ≤ 1 :=
  abs_inner_single_single_le β γ

example {R₀ : ℝ} (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ < ‖x‖) (γ : Fin 3) :
    |fderiv ℝ (isotropicProfile R₀) x (EuclideanSpace.single γ 1)| ≤ 1 / ‖x‖ ^ 2 :=
  abs_fderiv_profile_le hR₀ hx γ

example {R₀ : ℝ} (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ < ‖x‖) (β γ : Fin 3) :
    |fderiv ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y (EuclideanSpace.single γ 1)) x
      (EuclideanSpace.single β 1)| ≤ 4 / ‖x‖ ^ 3 :=
  abs_fderiv_fderiv_profile_le hR₀ hx β γ

example {M : ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ < ‖x‖) (β γ : Fin 3) :
    |fderiv ℝ (fun y => fderiv ℝ (isoQ₂ M R₀) y (EuclideanSpace.single γ 1)) x
      (EuclideanSpace.single β 1)| ≤ 40 * M ^ 2 / ‖x‖ ^ 4 :=
  abs_fderiv_fderiv_isoQ₂_le hR₀ hx β γ

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀}
    {z : MinkowskiModel 3} (hz : 2 * R₀ < ‖space z‖) (i k : Fin 4) :
    |(isotropicMetric σ M R₀ hM hR).totalDensity z i k| ≤ 180 * M ^ 2 / ‖space z‖ ^ 4 :=
  abs_totalDensity_isotropicMetric_le hz i k

example {M : ℝ} {R₀ : ℝ} (α β γ : Fin 3) :
    isoLam M R₀ α.succ 0 β γ = fun _ => 0 :=
  isoLam_succ_zero α β γ

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀} (t : ℝ) (α : Fin 3)
    :
    charge (isotropicMetric σ M R₀ hM hR) t α.succ = 0 :=
  charge_isotropicMetric_succ t α

example (β : ℝ) :
    ℝ :=
  boostFactor β

example {β : ℝ} (hβ : |β| < 1) :
    0 < boostFactor β :=
  boostFactor_pos hβ

example {β : ℝ} (hβ : |β| < 1) :
    boostFactor β ^ 2 * (1 - β ^ 2) = 1 :=
  boostFactor_sq hβ

example (β : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  boost β

example (σ : LorentzConvention) {β : ℝ} (hβ : |β| < 1) :
    (boost β)ᵀ * minkowskiCoefficient σ * boost β = minkowskiCoefficient σ :=
  boost_lorentz σ hβ

example (σ : LorentzConvention) {β : ℝ} (hβ : |β| < 1) :
    (boost β).det ≠ 0 :=
  boost_det_ne_zero σ hβ

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀} (c₀ c₁ : ℝ) (v : E3)
    :
    IsGalileanOnWedge (isotropicMetric σ M R₀ hM hR) c₀ c₁ v (3 * R₀) (8 * M) :=
  isGalileanOnWedge_isotropicMetric c₀ c₁ v

example (σ : LorentzConvention) {β : ℝ} (hβ : |β| < 1) :
    (boost β)⁻¹ 0 0 = boostFactor β ∧ (boost β)⁻¹ 1 0 = -(boostFactor β * β) ∧
      (boost β)⁻¹ 2 0 = 0 ∧ (boost β)⁻¹ 3 0 = 0 :=
  boost_inv_col σ hβ

example {σ : LorentzConvention} {M : ℝ} {R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀} {β : ℝ}
    (hβ : |β| < 1) (hL : (boost β).det ≠ 0) (t : ℝ) :
    charge ((isotropicMetric σ M R₀ hM hR).linearPullback (boost β) hL) t 0 =
        8 * π * M * boostFactor β ∧
      charge ((isotropicMetric σ M R₀ hM hR).linearPullback (boost β) hL) t 1 =
        -(8 * π * M * boostFactor β * β) ∧
      charge ((isotropicMetric σ M R₀ hM hR).linearPullback (boost β) hL) t 2 = 0 ∧
      charge ((isotropicMetric σ M R₀ hM hR).linearPullback (boost β) hL) t 3 = 0 :=
  charge_boost_isotropicMetric hβ hL t

end ProjectAinos.GeneralRelativity

end ChargeCovarianceIsotropic

section StationaryFarField

open MeasureTheory Filter Set Metric Real

open scoped Topology ContDiff RealInnerProductSpace

namespace ProjectAinos.GeneralRelativity.StationaryFarField

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Potential

open Electrodynamics Electrodynamics.Multipole LinearizedRadiation SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (a : ℝ) :
    Prop :=
  StationarySource S a

example (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (z : Spacetime) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  staticStress S z

example :
    space (Pi.single 0 1 : MinkowskiModel 3) = 0 :=
  space_single_zero

example (α : Fin 3) :
    space (Pi.single α.succ 1 : MinkowskiModel 3) = EuclideanSpace.single α 1 :=
  space_single_succ α

example {f : E3 → ℝ} {z : Spacetime} (hf : DifferentiableAt ℝ f (space z)) (v : Spacetime) :
    fderiv ℝ (fun w => f (space w)) z v = fderiv ℝ f (space z) (space v) :=
  fderiv_comp_space hf v

namespace StationarySource

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) {x : E3}
    (hx : a < ‖x‖) (i k : Fin 4) :
    S x i k = 0 :=
  apply_eq_zero hS hx i k

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (i k : Fin 4) :
    tsupport (fun x => S x i k) ⊆ closedBall 0 a :=
  tsupport_subset hS i k

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (i k : Fin 4) :
    HasCompactSupport fun x => S x i k :=
  hasCompactSupport hS i k

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (i k : Fin 4) :
    Continuous fun x => S x i k :=
  continuous hS i k

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) :
    LocalizedStress (staticStress S) a :=
  localizedStress hS

end StationarySource

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} {κ : ℝ} (hS : StationarySource S a)
    (z : Spacetime) (j k : Fin 4) :
    CoordinateMetric.linearizedEinstein .timeNegative (metricPerturbation κ (staticStress S)) z
      j k = κ * staticStress S z j k :=
  linearizedEinstein_static hS z j k

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} (κ : ℝ) (z : Spacetime) (i k : Fin 4) :
    retardedPerturbation κ (staticStress S) z i k =
      2 * κ * newtonPotential (fun x => S x i k) (space z) :=
  retardedPerturbation_static κ z i k

example {V : Fin 3 → E3 → ℝ} {a : ℝ} (ha : 0 ≤ a) (hV : ∀ γ, ContDiff ℝ 1 (V γ))
    (hsupp : ∀ γ (y : E3), a < ‖y‖ → V γ y = 0)
    (hdiv : ∀ y, ∑ γ, fderiv ℝ (V γ) y (EuclideanSpace.single γ 1) = 0) {f : E3 → ℝ}
    (hf : ContDiff ℝ 1 f) :
    ∫ y, ∑ γ, fderiv ℝ f y (EuclideanSpace.single γ 1) * V γ y = 0 :=
  integral_fderiv_mul_eq_zero ha hV hsupp hdiv hf

example (y : E3) (α γ : Fin 3) :
    fderiv ℝ (fun y : E3 => y α) y (EuclideanSpace.single γ 1) = if γ = α then 1 else 0 :=
  fderiv_coord y α γ

example {n : WithTop ℕ∞} (α : Fin 3) :
    ContDiff ℝ n fun y : E3 => y α :=
  contDiff_coord α

example (y : E3) (α β γ : Fin 3) :
    fderiv ℝ (fun y : E3 => y α * y β) y (EuclideanSpace.single γ 1) =
      (if γ = α then 1 else 0) * y β + y α * (if γ = β then 1 else 0) :=
  fderiv_coord_mul_coord y α β γ

namespace StationarySource

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (i k : Fin 4) :
    Integrable fun x => S x i k :=
  integrable hS i k

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (i k : Fin 4)
    (β : Fin 3) :
    Integrable fun x : E3 => S x i k * x β :=
  integrable_mul_coord hS i k β

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (b : Fin 4)
    {f : E3 → ℝ} (hf : ContDiff ℝ 1 f) :
    ∫ y, ∑ γ : Fin 3, fderiv ℝ f y (EuclideanSpace.single γ 1) * S y γ.succ b = 0 :=
  integral_fderiv_mul hS b hf

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (α : Fin 3) :
    ∫ y, S y 0 α.succ = 0 :=
  integral_momentum_eq_zero hS α

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (α β : Fin 3) :
    ∫ y, S y α.succ β.succ = 0 :=
  integral_stress_eq_zero hS α β

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (b : Fin 4)
    (α β : Fin 3) :
    (∫ y, S y α.succ b * y β) + ∫ y, S y β.succ b * y α = 0 :=
  integral_coord_mul_add hS b α β

end StationarySource

example (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) :
    ℝ :=
  massOf S

example (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (α β : Fin 3) :
    ℝ :=
  currentDipole S α β

example (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (α β : Fin 3) :
    ℝ :=
  angularMomentum S α β

example (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (γ α β : Fin 3) :
    ℝ :=
  stressDipole S γ α β

namespace StationarySource

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (α β : Fin 3) :
    currentDipole S α β = -currentDipole S β α :=
  currentDipole_antisymm hS α β

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (α β : Fin 3) :
    currentDipole S α β = -(angularMomentum S α β / 2) :=
  currentDipole_eq hS α β

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (γ α β : Fin 3) :
    stressDipole S γ α β = 0 :=
  stressDipole_eq_zero hS γ α β

end StationarySource

example (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (i k : Fin 4) :
    ℝ :=
  secondAbsMoment S i k

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (i k : Fin 4)
    (x : E3) :
    ⟪dipoleMoment (fun y => S y i k), x⟫ = ∑ β : Fin 3, x β * ∫ y, S y i k * y β :=
  inner_dipoleMoment_eq hS i k x

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (κ : ℝ)
    {z : Spacetime} (hz : a < ‖space z‖) (i k : Fin 4) :
    |retardedPerturbation κ (staticStress S) z i k -
        2 * κ * ((∫ y, S y i k) / (4 * π * ‖space z‖)) -
        2 * κ * ((∑ β : Fin 3, space z β * ∫ y, S y i k * y β) / (4 * π * ‖space z‖ ^ 3))| ≤
      2 * |κ| * (secondAbsMoment S i k / (4 * π * (‖space z‖ - a) ^ 3)) :=
  abs_hbar_sub_le hS κ hz i k

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a)
    (hc : ∀ β : Fin 3, ∫ y, S y 0 0 * y β = 0) (κ : ℝ) {z : Spacetime} (hz : a < ‖space z‖) :
    |retardedPerturbation κ (staticStress S) z 0 0 - 2 * κ * massOf S / (4 * π * ‖space z‖)| ≤
      2 * |κ| * (secondAbsMoment S 0 0 / (4 * π * (‖space z‖ - a) ^ 3)) :=
  abs_hbar_zero_zero_sub_le hS hc κ hz

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (κ : ℝ)
    {z : Spacetime} (hz : a < ‖space z‖) (α : Fin 3) :
    |retardedPerturbation κ (staticStress S) z 0 α.succ -
        2 * κ * ((∑ β : Fin 3, currentDipole S α β * space z β) / (4 * π * ‖space z‖ ^ 3))| ≤
      2 * |κ| * (secondAbsMoment S 0 α.succ / (4 * π * (‖space z‖ - a) ^ 3)) :=
  abs_hbar_zero_succ_sub_le hS κ hz α

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (κ : ℝ)
    {z : Spacetime} (hz : a < ‖space z‖) (α β : Fin 3) :
    |retardedPerturbation κ (staticStress S) z α.succ β.succ| ≤
      2 * |κ| * (secondAbsMoment S α.succ β.succ / (4 * π * (‖space z‖ - a) ^ 3)) :=
  abs_hbar_succ_succ_le hS κ hz α β

example {T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ} (κ : ℝ) (z : Spacetime) :
    metricPerturbation κ T z 0 0 = (retardedPerturbation κ T z 0 0 +
      ∑ γ : Fin 3, retardedPerturbation κ T z γ.succ γ.succ) / 2 :=
  metricPerturbation_zero_zero κ z

example {T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ} (κ : ℝ) (z : Spacetime) (α : Fin 3) :
    metricPerturbation κ T z 0 α.succ = retardedPerturbation κ T z 0 α.succ :=
  metricPerturbation_zero_succ κ z α

example {T : Spacetime → Matrix (Fin 4) (Fin 4) ℝ} (κ : ℝ) (z : Spacetime) (α β : Fin 3) :
    metricPerturbation κ T z α.succ β.succ = retardedPerturbation κ T z α.succ β.succ -
      (if α = β then (-retardedPerturbation κ T z 0 0 +
        ∑ γ : Fin 3, retardedPerturbation κ T z γ.succ γ.succ) / 2 else 0) :=
  metricPerturbation_succ_succ κ z α β

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a)
    (hc : ∀ β : Fin 3, ∫ y, S y 0 0 * y β = 0) (κ : ℝ) {z : Spacetime} (hz : a < ‖space z‖) :
    |metricPerturbation κ (staticStress S) z 0 0 - κ * massOf S / (4 * π * ‖space z‖)| ≤
      |κ| * ((secondAbsMoment S 0 0 + ∑ γ : Fin 3, secondAbsMoment S γ.succ γ.succ) /
        (4 * π * (‖space z‖ - a) ^ 3)) :=
  abs_metricPerturbation_zero_zero_sub_le hS hc κ hz

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a)
    (hc : ∀ β : Fin 3, ∫ y, S y 0 0 * y β = 0) (κ : ℝ) {z : Spacetime} (hz : a < ‖space z‖)
    (α β : Fin 3) :
    |metricPerturbation κ (staticStress S) z α.succ β.succ -
        (if α = β then κ * massOf S / (4 * π * ‖space z‖) else 0)| ≤
      |κ| * ((2 * secondAbsMoment S α.succ β.succ + secondAbsMoment S 0 0 +
        ∑ γ : Fin 3, secondAbsMoment S γ.succ γ.succ) / (4 * π * (‖space z‖ - a) ^ 3)) :=
  abs_metricPerturbation_succ_succ_sub_le hS hc κ hz α β

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (κ : ℝ)
    {z : Spacetime} (hz : a < ‖space z‖) (α : Fin 3) :
    |retardedPerturbation κ (staticStress S) z 0 α.succ +
        κ * (∑ β : Fin 3, angularMomentum S α β * space z β) / (4 * π * ‖space z‖ ^ 3)| ≤
      2 * |κ| * (secondAbsMoment S 0 α.succ / (4 * π * (‖space z‖ - a) ^ 3)) :=
  abs_hbar_zero_succ_sub_angularMomentum_le hS κ hz α

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (i k : Fin 4) :
    ContDiff ℝ 3 (newtonPotential fun x => S x i k) :=
  contDiff_potential hS i k

example {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x : E3) :
    coordLaplacian (fun y => c * f y) x = c * coordLaplacian f x :=
  coordLaplacian_const_mul hf c x

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (κ : ℝ)
    (i k : Fin 4) (x : E3) :
    coordLaplacian (fun y => 2 * κ * newtonPotential (fun x => S x i k) y) x =
      -(2 * κ * S x i k) :=
  coordLaplacian_field hS κ i k x

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} (κ : ℝ) (t : ℝ) (i k : Fin 4) :
    (fun y => retardedPerturbation κ (staticStress S) (vector t y) i k) =
      fun y => 2 * κ * newtonPotential (fun x => S x i k) y :=
  field_slice κ t i k

example {a : ℝ} {f : E3 → ℝ} (hf : ∀ y : E3, a < ‖y‖ → f y = 0) {R : ℝ} (hR : a < R) :
    ∫ y in Sphere.shell 0 R, f y = ∫ y, f y :=
  integral_shell_eq hf hR

example (κ : ℝ) (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (t R : ℝ) :
    ℝ :=
  massFlux κ S t R

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (κ t : ℝ) {R : ℝ}
    (hR : a < R) :
    massFlux κ S t R = -(2 * κ * massOf S) :=
  massFlux_eq hS κ t hR

example (κ : ℝ) (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (δ : Fin 3) (y : E3) :
    ℝ :=
  momentumPotential κ S t δ y

example (κ : ℝ) (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (t : ℝ) (α β : Fin 3) (R : ℝ) :
    ℝ :=
  angularMomentumFlux κ S t α β R

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) (κ t : ℝ)
    (α β : Fin 3) {R : ℝ} (hR : a < R) :
    angularMomentumFlux κ S t α β R = -(2 * κ * angularMomentum S α β) :=
  angularMomentumFlux_eq hS κ t α β hR

example (M r c : ℝ) :
    Kerr.gtp M 0 r c = 0 :=
  gtp_zero_spin M r c

example {a r c : ℝ} (hr : 0 < r) :
    0 < Kerr.sig a r c :=
  sig_pos hr

example (a r c : ℝ) :
    r ^ 2 ≤ Kerr.sig a r c :=
  sq_le_sig a r c

example {M a r c : ℝ} (hr : 0 < r) (hc : c ^ 2 ≤ 1) :
    |Kerr.gtp M a r c + 2 * M * a * (1 - c ^ 2) / r| ≤ 2 * |M| * |a| ^ 3 / r ^ 3 :=
  abs_gtp_add_le hr hc

example {M a r c : ℝ} (hr : 0 < r) (hc : c ^ 2 ≤ 1) :
    |Kerr.gtt M a r c + 1 - 2 * M / r| ≤ 2 * |M| * a ^ 2 / r ^ 3 :=
  abs_gtt_add_le hr hc

example (r c φ : ℝ) :
    E3 :=
  polarPoint r c φ

example (r c φ : ℝ) :
    polarPoint r c φ 0 = r * √(1 - c ^ 2) * Real.cos φ :=
  polarPoint_zero r c φ

example (r c φ : ℝ) :
    polarPoint r c φ 1 = r * √(1 - c ^ 2) * Real.sin φ :=
  polarPoint_one r c φ

example (r c φ : ℝ) :
    polarPoint r c φ 2 = r * c :=
  polarPoint_two r c φ

example (r c φ : ℝ) (hc : c ^ 2 ≤ 1) :
    polarPoint r c φ 0 ^ 2 + polarPoint r c φ 1 ^ 2 = r ^ 2 * (1 - c ^ 2) :=
  polarPoint_sq r c φ hc

example {r : ℝ} (hr : 0 ≤ r) (c φ : ℝ) (hc : c ^ 2 ≤ 1) :
    ‖polarPoint r c φ‖ = r :=
  norm_polarPoint hr c φ hc

example (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (α β : Fin 3) :
    angularMomentum S β α = -angularMomentum S α β :=
  angularMomentum_antisymm S α β

example (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (α : Fin 3) :
    angularMomentum S α α = 0 :=
  angularMomentum_self S α

example (κ : ℝ) (S : E3 → Matrix (Fin 4) (Fin 4) ℝ) (z : Spacetime) :
    ℝ :=
  spinComponent κ S z

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a) {M₀ a₀ : ℝ}
    (hJ : angularMomentum S 0 1 = -(M₀ * a₀)) (hJ2 : angularMomentum S 0 2 = 0)
    (hJ3 : angularMomentum S 1 2 = 0) (t : ℝ) {r c φ : ℝ} (hr : a < r) (hc : c ^ 2 ≤ 1) :
    |spinComponent (8 * π) S (vector t (polarPoint r c φ)) - Kerr.gtp M₀ a₀ r c| ≤
      4 * (secondAbsMoment S 0 (0 : Fin 3).succ + secondAbsMoment S 0 (1 : Fin 3).succ) * r /
          (r - a) ^ 3 + 2 * |M₀| * |a₀| ^ 3 / r ^ 3 :=
  abs_spinComponent_sub_gtp_le hS hJ hJ2 hJ3 t hr hc

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a)
    (hc : ∀ β : Fin 3, ∫ y, S y 0 0 * y β = 0) (t : ℝ) {x : E3} (hx : a < ‖x‖) (a₀ c : ℝ)
    (hc' : c ^ 2 ≤ 1) :
    |metricPerturbation (8 * π) (staticStress S) (vector t x) 0 0 -
        (Kerr.gtt (massOf S) a₀ ‖x‖ c + 1)| ≤
      2 * (secondAbsMoment S 0 0 + ∑ γ : Fin 3, secondAbsMoment S γ.succ γ.succ) /
          (‖x‖ - a) ^ 3 + 2 * |massOf S| * a₀ ^ 2 / ‖x‖ ^ 3 :=
  abs_metricPerturbation_zero_zero_sub_gtt_le hS hc t hx a₀ c hc'

example {S : E3 → Matrix (Fin 4) (Fin 4) ℝ} {a : ℝ} (hS : StationarySource S a)
    (hp : ∀ y, S y 0 (2 : Fin 3).succ = 0) (α : Fin 3) :
    angularMomentum S α 2 = 0 :=
  StationarySource.angularMomentum_eq_zero_of_planar hS hp α

example (x : E3) :
    ℝ :=
  rotProfile x

example :
    ContDiff ℝ ∞ rotProfile :=
  contDiff_rotProfile

example {x : E3} (hx : 1 < ‖x‖) :
    rotProfile x = 0 :=
  rotProfile_eq_zero hx

example :
    rotProfile 0 = 1 :=
  rotProfile_zero

example (x : E3) :
    rotProfile (-x) = rotProfile x :=
  rotProfile_neg x

example (x : E3) (γ : Fin 3) :
    fderiv ℝ rotProfile x (EuclideanSpace.single γ 1) =
      -(2 * deriv Real.smoothTransition (1 - ‖x‖ ^ 2)) * x γ :=
  fderiv_rotProfile x γ

example (m ν : ℝ) (x : E3) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  rotSource m ν x

example (c : ℝ) (β : Fin 3) :
    ContDiff ℝ ∞ fun x : E3 => c * x β * rotProfile x :=
  contDiff_coord_mul_rotProfile c β

example (m ν : ℝ) (y : E3) (γ β : Fin 3) :
    rotSource m ν y γ.succ β.succ = 0 :=
  rotSource_stress m ν y γ β

example (m ν : ℝ) :
    StationarySource (rotSource m ν) 1 :=
  stationarySource_rotSource m ν

example (m ν : ℝ) (β : Fin 3) :
    ∫ y, rotSource m ν y 0 0 * y β = 0 :=
  rotSource_massCentred m ν β

example (m ν : ℝ) (y : E3) :
    rotSource m ν y 0 (2 : Fin 3).succ = 0 :=
  rotSource_planar m ν y

example (m ν : ℝ) :
    rotSource m ν 0 0 0 = m :=
  rotSource_zero_zero m ν

end ProjectAinos.GeneralRelativity.StationaryFarField

end StationaryFarField
