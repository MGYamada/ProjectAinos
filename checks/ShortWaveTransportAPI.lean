/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.CovariantLeibniz
import ProjectAinos.SmoothGeometry.Lorentzian.SecondVariation
import ProjectAinos.GeneralRelativity.ShortWaveTransport
import ProjectAinos.GeneralRelativity.EffectiveStress

/-! Public consumers of short gravitational waves on a curved background beyond the eikonal
(Landau–Lifshitz §108): the Leibniz rules of the coordinate covariant derivatives, the covariant
form of the transport term with the transport equation on the transverse polarizations and for
the full amplitude, the second variation of the Ricci tensor along `g + s h`, its short-wave
expansion and phase average, and the effective stress of the waves with its symmetry, trace,
conservation and the flux of §110, with flat and plane-wave instances. Default elaborator options
are intentional: these checks must not rely on the implementation's transparency settings. Every
statement is pinned with its type. -/

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

section Definitions

variable (g : CoordinateMetric σ d U)

example (w : MinkowskiModel d → Fin (d + 1) → ℝ) (x : MinkowskiModel d)
    (a i : Fin (d + 1)) : ℝ :=
  covDerivOne g w x a i

example (p : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (x : MinkowskiModel d) (m i j l : Fin (d + 1)) : ℝ :=
  covDerivLowThree g p x m i j l

end Definitions

example {n : ℕ} (w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (i j l : Fin n) : ℝ :=
  symbolLower w A i j l

variable {g : CoordinateMetric σ d U}

example {x : MinkowskiModel d} (hx : x ∈ U)
    (a b : Fin (d + 1)) : DifferentiableAt ℝ (fun z => (g.coefficient z)⁻¹ a b) x :=
  differentiableAt_coefficient_inv hx a b

example {x : MinkowskiModel d} (hx : x ∈ U)
    (a b c : Fin (d + 1)) : DifferentiableAt ℝ (fun z => christoffelOf g.coefficient z a b c) x :=
  differentiableAt_christoffelOf hx a b c

example {f : MinkowskiModel d → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    {x : MinkowskiModel d} (hx : x ∈ U) : DifferentiableAt ℝ f x :=
  differentiableAt_of_contDiffOn hf hx

example {q : MinkowskiModel d → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U) (hq : ∀ l, DifferentiableAt ℝ (fun z => q z l) x) (i m : Fin (d + 1)) :
    fderiv ℝ (fun z => ∑ l, (g.coefficient z)⁻¹ i l * q z l) x (Pi.single m 1) =
      -∑ b, christoffelOf g.coefficient x i m b * ∑ l, (g.coefficient x)⁻¹ b l * q x l +
        ∑ l, (g.coefficient x)⁻¹ i l * g.covDerivOne q x m l :=
  fderiv_raise hx hq i m

example {p : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hx : x ∈ U) (hp : ∀ i j l, DifferentiableAt ℝ (fun z => p z i j l) x)
    (m k i j : Fin (d + 1)) :
    g.covDerivThree (fun z k i j => ∑ l, (g.coefficient z)⁻¹ k l * p z i j l) x m k i j =
      ∑ l, (g.coefficient x)⁻¹ k l * g.covDerivLowThree p x m i j l :=
  covDerivThree_raise hx hp m k i j

example (w : Fin (d + 1) → ℝ) (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.symbolChristoffel w A x k i j = ∑ l, (g.coefficient x)⁻¹ k l * symbolLower w A i j l :=
  symbolChristoffel_eq_sum w A x k i j

example {w : MinkowskiModel d → Fin (d + 1) → ℝ}
    {A : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hw : ∀ i, DifferentiableAt ℝ (fun z => w z i) x)
    (hA : ∀ p q, DifferentiableAt ℝ (fun z => A z p q) x) (m i j l : Fin (d + 1)) :
    g.covDerivLowThree (fun z => symbolLower (w z) (A z)) x m i j l =
      symbolLower (fun c => g.covDerivOne w x m c) (A x) i j l +
        symbolLower (w x) (Matrix.of fun p q => g.covDerivTwo A x m p q) i j l :=
  covDerivLowThree_symbolLower hw hA m i j l

example {w : MinkowskiModel d → Fin (d + 1) → ℝ}
    {A : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U) (hw : ∀ i, DifferentiableAt ℝ (fun z => w z i) x)
    (hA : ∀ p q, DifferentiableAt ℝ (fun z => A z p q) x) (m k i j : Fin (d + 1)) :
    g.covDerivThree (fun z => g.symbolChristoffel (w z) (A z) z) x m k i j =
      g.symbolChristoffel (fun c => g.covDerivOne w x m c) (A x) x k i j +
        g.symbolChristoffel (w x) (Matrix.of fun p q => g.covDerivTwo A x m p q) x k i j :=
  covDerivThree_symbolChristoffel hx hw hA m k i j

example {T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hx : x ∈ U) (hT : ∀ p q, DifferentiableAt ℝ (fun z => T z p q) x)
    (m : Fin (d + 1)) :
    fderiv ℝ (fun z => ∑ i, ∑ l, (g.coefficient z)⁻¹ i l * T z i l) x (Pi.single m 1) =
      ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * g.covDerivTwo T x m i l :=
  fderiv_trace hx hT m

example (g : CoordinateMetric σ d U) (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : ℝ :=
  tensorPairing g A B x

example (g : CoordinateMetric σ d U)
    (A : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (m : Fin (d + 1)) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  covDerivMatrix g A x m

example {A B : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hx : x ∈ U) (hA : ∀ p q, DifferentiableAt ℝ (fun z => A z p q) x)
    (hB : ∀ p q, DifferentiableAt ℝ (fun z => B z p q) x) (m : Fin (d + 1)) :
    fderiv ℝ (fun z => tensorPairing g (A z) (B z) z) x (Pi.single m 1) =
      tensorPairing g (g.covDerivMatrix A x m) (B x) x +
        tensorPairing g (A x) (g.covDerivMatrix B x m) x :=
  fderiv_tensorPairing hx hA hB m

example {u v : MinkowskiModel d → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hu : ∀ i, DifferentiableAt ℝ (fun z => u z i) x)
    (hv : ∀ i, DifferentiableAt ℝ (fun z => v z i) x) (m i j : Fin (d + 1)) :
    g.covDerivTwo (fun z => Matrix.of fun i j => u z i * v z j) x m i j =
      g.covDerivOne u x m i * v x j + u x i * g.covDerivOne v x m j :=
  covDerivTwo_mul hu hv m i j

example {f : MinkowskiModel d → ℝ} {w : MinkowskiModel d → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hf : DifferentiableAt ℝ f x)
    (hw : ∀ i, DifferentiableAt ℝ (fun z => w z i) x) (m i : Fin (d + 1)) :
    g.covDerivOne (fun z => f z • w z) x m i =
      gradientCovector f x m * w x i + f x * g.covDerivOne w x m i :=
  covDerivOne_smul hf hw m i

example {w : MinkowskiModel d → Fin (d + 1) → ℝ}
    {A : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U) (hw : ∀ i, DifferentiableAt ℝ (fun z => w z i) x)
    (hA : ∀ p q, DifferentiableAt ℝ (fun z => A z p q) x) (c j : Fin (d + 1)) :
    g.covDerivOne (fun z j => ∑ m, (∑ l, (g.coefficient z)⁻¹ m l * w z l) * A z m j) x c j =
      ∑ m, (∑ l, (g.coefficient x)⁻¹ m l * g.covDerivOne w x c l) * A x m j +
        ∑ m, (∑ l, (g.coefficient x)⁻¹ m l * w x l) * g.covDerivTwo A x c m j :=
  covDerivOne_raise_contract hx hw hA c j

example {ψ : MinkowskiModel d → ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U) (hψ : ContDiffAt ℝ 2 ψ x) (i j : Fin (d + 1)) :
    g.covDerivOne (gradientCovector ψ) x i j = g.covDerivOne (gradientCovector ψ) x j i :=
  covDerivOne_gradient_symm hx hψ i j

example {ψ : MinkowskiModel d → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U)
    {x : MinkowskiModel d} (hx : x ∈ U) (m : Fin (d + 1)) :
    gradientCovector (g.gradientNorm ψ) x m =
      2 * ∑ a, g.gradientField ψ x a * g.covDerivOne (gradientCovector ψ) x m a :=
  gradientCovector_gradientNorm hψ hx m

example {A : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hA : ∀ z ∈ U, ∀ i j, A z i j = A z j i) {x : MinkowskiModel d} (hx : x ∈ U)
    (m p q : Fin (d + 1)) : g.covDerivTwo A x m p q = g.covDerivTwo A x m q p :=
  covDerivTwo_symm hA hx m p q

example {w w' : MinkowskiModel d → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hw : w =ᶠ[𝓝 x] w') (a i : Fin (d + 1)) : g.covDerivOne w x a i = g.covDerivOne w' x a i :=
  covDerivOne_congr hw a i

end ProjectAinos.SmoothGeometry.CoordinateMetric

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology Matrix

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

example {n : ℕ} (P P' : Fin n → Fin n → Fin n → ℝ) (j k : Fin n) : ℝ :=
  christoffelQuadratic P P' j k

section Definitions

variable (g : CoordinateMetric σ d U)

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ) (z : MinkowskiModel d)
    (k i j : Fin (d + 1)) : ℝ :=
  raiseContract g h P z k i j

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  secondRicci g h x j k

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (z : MinkowskiModel d) (l i j : Fin (d + 1)) : ℝ :=
  christoffelDifferenceLow g h z l i j

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (p : ℝ × MinkowskiModel d) (k i j : Fin (d + 1)) : ℝ :=
  christoffelQuotient g h p k i j

end Definitions

variable {g : CoordinateMetric σ d U} {h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {s : ℝ} {z : MinkowskiModel d} (hz : z ∈ U) (hdet : (g.perturbationFamily h (s, z)).det ≠ 0)
    (k i j : Fin (d + 1)) :
    christoffelOf (fun y => g.coefficient y + s • h y) z k i j =
      christoffelOf g.coefficient z k i j + s * g.christoffelQuotient h (s, z) k i j :=
  christoffelOf_perturbation_eq hh hz hdet k i j

example (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {z : MinkowskiModel d}
    (hz : z ∈ U) (k i j : Fin (d + 1)) :
    g.christoffelQuotient h (0, z) k i j = g.curvedChristoffel h z k i j :=
  christoffelQuotient_zero hs hz k i j

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {x : MinkowskiModel d} (hx : x ∈ U) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), x), p.2 ∈ U ∧ (g.perturbationFamily h p).det ≠ 0 :=
  eventually_perturbationFamily hh hx

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (l i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => g.christoffelDifferenceLow h z l i j) U :=
  contDiffOn_christoffelDifferenceLow hh l i j

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {p : ℝ × MinkowskiModel d} (hp : p.2 ∈ U) (hdet : (g.perturbationFamily h p).det ≠ 0)
    (k i j : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (fun q => g.christoffelQuotient h q k i j) p :=
  contDiffAt_christoffelQuotient hh hp hdet k i j

example (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {z : MinkowskiModel d} (hz : z ∈ U) (k i j : Fin (d + 1)) :
    HasDerivAt (fun s => g.christoffelQuotient h (s, z) k i j)
      (-g.raiseContract h (g.curvedChristoffel h) z k i j) 0 :=
  hasDerivAt_christoffelQuotient hs hz k i j

example {C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {D : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hx : x ∈ U)
    (hC : ∀ᶠ z in 𝓝 x, ∀ k i j,
      christoffelOf C z k i j = christoffelOf g.coefficient z k i j + D z k i j)
    (hD : ∀ a b c, DifferentiableAt ℝ (fun z => D z a b c) x) (j k : Fin (d + 1)) :
    ricciOf C x j k = ricciOf g.coefficient x j k + g.palatini D x j k +
      christoffelQuadratic (D x) (D x) j k :=
  ricciOf_eq_of_christoffel hx hC hD j k

example {n : ℕ} (c : ℝ) (P : Fin n → Fin n → Fin n → ℝ) (j k : Fin n) :
    christoffelQuadratic (c • P) (c • P) j k = c ^ 2 * christoffelQuadratic P P j k :=
  christoffelQuadratic_smul c P j k

example (c : ℝ)
    {P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ} {x : MinkowskiModel d}
    (hP : ∀ a b e, DifferentiableAt ℝ (fun z => P z a b e) x) (j k : Fin (d + 1)) :
    g.palatini (fun z => c • P z) x j k = c * g.palatini P x j k :=
  palatini_const_smul c hP j k

example {P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    {x : MinkowskiModel d} (hP : ∀ a b e, DifferentiableAt ℝ (fun z => P z a b e) x)
    (j k : Fin (d + 1)) :
    g.palatini (fun z => -P z) x j k = -g.palatini P x j k :=
  palatini_neg hP j k

example {p q : ℝ → ℝ} (hp : ContDiffAt ℝ 2 p 0)
    (hq : ContDiffAt ℝ 2 q 0) (c : ℝ) :
    HasDerivAt (deriv (fun s => c + s * p s + s ^ 2 * q s)) (2 * deriv p 0 + 2 * q 0) 0 :=
  hasDerivAt_deriv_mul_add hp hq c

example (g : CoordinateMetric σ d U)
    (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) (s : ℝ) : ℝ :=
  secondVariationLinear g h x j k s

example (g : CoordinateMetric σ d U)
    (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) (s : ℝ) : ℝ :=
  secondVariationQuadratic g h x j k s

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    (fun s : ℝ => ricciOf (fun z => g.coefficient z + s • h z) x j k) =ᶠ[𝓝 0]
      fun s => ricciOf g.coefficient x j k + s * g.secondVariationLinear h x j k s +
        s ^ 2 * g.secondVariationQuadratic h x j k s :=
  eventually_ricciOf_perturbation hh hx j k

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (g.secondVariationLinear h x j k) 0 :=
  contDiffAt_secondVariationLinear hh hx j k

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (g.secondVariationQuadratic h x j k) 0 :=
  contDiffAt_secondVariationQuadratic hh hx j k

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    HasDerivAt (g.secondVariationLinear h x j k)
      (-g.palatini (g.raiseContract h (g.curvedChristoffel h)) x j k) 0 :=
  hasDerivAt_secondVariationLinear hh hs hx j k

example (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    g.secondVariationQuadratic h x j k 0 =
      christoffelQuadratic (g.curvedChristoffel h x) (g.curvedChristoffel h x) j k :=
  secondVariationQuadratic_zero hs hx j k

example
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      DifferentiableAt ℝ (fun s : ℝ => ricciOf (fun z => g.coefficient z + s • h z) x j k) s :=
  eventually_differentiableAt_ricciOf_perturbation hh hx j k

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    HasDerivAt (deriv fun s : ℝ => ricciOf (fun z => g.coefficient z + s • h z) x j k)
      (g.secondRicci h x j k) 0 :=
  hasDerivAt_deriv_ricciOf_perturbation hh hs hx j k

example (hh : ∀ i j, ContDiffOn ℝ ∞ (fun z => h z i j) U)
    (hs : ∀ z ∈ U, ∀ i j, h z i j = h z j i) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    deriv (deriv fun s : ℝ => ricciOf (fun z => g.coefficient z + s • h z) x j k) 0 =
      g.secondRicci h x j k :=
  deriv_deriv_ricciOf_perturbation hh hs hx j k

end ProjectAinos.SmoothGeometry.CoordinateMetric

open Set Filter TopologicalSpace
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.ShortWave

open SmoothGeometry CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

section Definitions

variable (g : CoordinateMetric σ d U)

example (ψ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) (i j : Fin (d + 1)) : ℝ :=
  waveHessian g ψ x i j

example (ψ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) : ℝ :=
  rayExpansion g ψ x

example (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  rayDerivative g ψ a x j k

example (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  transportOperator g ψ a x j k

example (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (k : Fin (d + 1)) : ℝ :=
  amplitudeDivergence g a x k

example (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (k : Fin (d + 1)) : ℝ :=
  traceGradient g a x k

example (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (k : Fin (d + 1)) : ℝ :=
  harmonicGauge g a x k

example (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  contractionDerivative g ψ a x j k

end Definitions

section Expansion

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

example {x : MinkowskiModel d} (hx : x ∈ U)
    (F : Fin (d + 1) → Fin (d + 1) → ℝ) :
    ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * F i l = ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * F l i :=
  sum_coefficient_inv_swap hx F

example {x : MinkowskiModel d} (hx : x ∈ U) (X : Fin (d + 1) → ℝ) :
    ∑ i, gradientCovector ψ x i * ∑ l, (g.coefficient x)⁻¹ i l * X l / 2 =
      ∑ l, g.gradientField ψ x l * X l / 2 :=
  sum_mul_coefficient_inv hx X

example (hψ : ContDiffOn ℝ ∞ ψ U) {x : MinkowskiModel d} (hx : x ∈ U)
    (i j : Fin (d + 1)) : waveHessian g ψ x i j = waveHessian g ψ x j i :=
  waveHessian_symm hψ hx i j

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    transportTerm g ψ a x j k =
      -transportOperator g ψ a x j k / 2 +
        (contractionDerivative g ψ a x j k + contractionDerivative g ψ a x k j) / 2 +
        (gradientCovector ψ x j * amplitudeDivergence g a x k +
          gradientCovector ψ x k * amplitudeDivergence g a x j) / 2 -
        (gradientCovector ψ x j * traceGradient g a x k +
          gradientCovector ψ x k * traceGradient g a x j) / 2 -
        waveHessian g ψ x j k * amplitudeTrace g (a x) x / 2 :=
  transportTerm_eq hψ ha has hx j k

end Expansion

section Gauge

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    contractionDerivative g ψ a x j k =
      g.covDerivOne (fun z => contractAmplitude g (gradientCovector ψ z) (a z) z) x j k :=
  contractionDerivative_eq hψ ha hx j k

example (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U)
    {x : MinkowskiModel d} (hx : x ∈ U) (j : Fin (d + 1)) :
    gradientCovector (fun z => amplitudeTrace g (a z) z) x j = traceGradient g a x j :=
  gradientCovector_amplitudeTrace ha hx j

example (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U)
    {x : MinkowskiModel d} (hx : x ∈ U) :
    DifferentiableAt ℝ (fun z => amplitudeTrace g (a z) z) x :=
  differentiableAt_amplitudeTrace ha hx

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    contractionDerivative g ψ a x j k =
      traceGradient g a x j * gradientCovector ψ x k / 2 +
        amplitudeTrace g (a x) x * waveHessian g ψ x j k / 2 :=
  contractionDerivative_of_gauge hψ ha hg hx j k

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    transportTerm g ψ a x j k =
      -transportOperator g ψ a x j k / 2 +
        (gradientCovector ψ x j * harmonicGauge g a x k +
          gradientCovector ψ x k * harmonicGauge g a x j) / 2 :=
  transportTerm_of_gauge hψ ha has hg hx j k

example (k : Fin (d + 1) → ℝ) (e : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Prop :=
  IsTransversePolarization k e

example (k : Fin (d + 1) → ℝ) (e : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : Prop :=
  IsTTPolarization g k e x

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) {e : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (he : IsTransversePolarization (gradientCovector ψ x) e) :
    ∑ j, ∑ k, e j k * transportTerm g ψ a x j k =
      -(∑ j, ∑ k, e j k * transportOperator g ψ a x j k) / 2 :=
  sum_transverse_transportTerm hψ ha has hg hx he

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) :
    (∀ e, IsTTPolarization g (gradientCovector ψ x) e x →
        ∑ j, ∑ k, e j k * transportTerm g ψ a x j k = 0) ↔
      ∀ e, IsTTPolarization g (gradientCovector ψ x) e x →
        ∑ j, ∑ k, e j k * transportOperator g ψ a x j k = 0 :=
  transverse_transportTerm_iff hψ ha has hg hx

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) (hnull : g.gradientNorm ψ x = 0)
    {e : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (he : IsTransversePolarization (gradientCovector ψ x) e) (ε : ℝ) :
    ∑ j, ∑ k, e j k *
        familyRicciDeriv (g.perturbationFamily (fun z => Real.cos (ψ z / ε) • a z)) x j k =
      ε⁻¹ * Real.sin (ψ x / ε) * (∑ j, ∑ k, e j k * transportOperator g ψ a x j k) / 2 +
        Real.cos (ψ x / ε) * ∑ j, ∑ k, e j k * familyRicciDeriv (g.perturbationFamily a) x j k :=
  sum_transverse_familyRicciDeriv_shortWave hψ ha has hg hx hnull he ε

example {f : MinkowskiModel d → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (hf : DifferentiableAt ℝ f x) (k : Fin (d + 1)) :
    harmonicGauge g (fun z => f z • a z) x k =
      ∑ m, raiseCovector g (gradientCovector f x) x m *
          (a x m k - g.coefficient x m k * amplitudeTrace g (a x) x / 2) +
        f x * harmonicGauge g a x k :=
  harmonicGauge_smul ha hx hf k

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (ε : ℝ) (k : Fin (d + 1)) :
    harmonicGauge g (fun z => Real.cos (ψ z / ε) • a z) x k =
      -(ε⁻¹ * Real.sin (ψ x / ε)) * ∑ m, raiseCovector g (gradientCovector ψ x) x m *
          (a x m k - g.coefficient x m k * amplitudeTrace g (a x) x / 2) +
        Real.cos (ψ x / ε) * harmonicGauge g a x k :=
  harmonicGauge_shortWave hψ ha hx ε k

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) (hB : ∀ k, harmonicGauge g a x k = 0)
    (j k : Fin (d + 1)) :
    transportTerm g ψ a x j k = -transportOperator g ψ a x j k / 2 :=
  transportTerm_of_harmonic hψ ha has hg hx hB j k

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) (hB : ∀ k, harmonicGauge g a x k = 0) :
    (∀ j k, transportTerm g ψ a x j k = 0) ↔ ∀ j k, transportOperator g ψ a x j k = 0 :=
  transportTerm_eq_zero_iff hψ ha has hg hx hB

end Gauge

section Flat

example (κ : Fin (d + 1) → ℝ)
    {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (hA : ∀ i j, A i j = A j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    transportTerm (minkowski σ d U) (fun y => ∑ i, κ i * y i) (fun _ => A) x j k = 0 :=
  transportTerm_minkowski_const κ hA hx j k

end Flat

namespace PlaneWave

open ExactPlaneWave

variable {D : Data}

example (x : MinkowskiModel 3) (b j : Fin 4) :
    ∑ l, rayDirection l * christoffel D x b l j = 0 :=
  sum_rayDirection_christoffel x b j

example (x : MinkowskiModel 3) (i j : Fin 4) :
    ∑ b, christoffel D x b i j * nullCovector b = 0 :=
  sum_christoffel_nullCovector x i j

example {x : MinkowskiModel 3} (hx : x ∈ domain D) (i j : Fin 4) :
    waveHessian (metric D) retarded x i j = 0 :=
  waveHessian_retarded hx i j

example {x : MinkowskiModel 3} (hx : x ∈ domain D) :
    rayExpansion (metric D) retarded x = 0 :=
  rayExpansion_retarded hx

example {x : MinkowskiModel 3} (hx : x ∈ domain D) (m p q : Fin 4) :
    (metric D).covDerivTwo (fun _ => crossAmplitude) x m p q =
      -∑ b, (christoffel D x b m p * crossAmplitude b q +
        christoffel D x b m q * crossAmplitude p b) :=
  covDerivTwo_cross hx m p q

example {x : MinkowskiModel 3} (hx : x ∈ domain D) (j k : Fin 4) :
    rayDerivative (metric D) retarded (fun _ => crossAmplitude) x j k = 0 :=
  rayDerivative_cross hx j k

example {x : MinkowskiModel 3} (hx : x ∈ domain D) (j k : Fin 4) :
    transportOperator (metric D) retarded (fun _ => crossAmplitude) x j k = 0 :=
  transportOperator_cross hx j k

example {x : MinkowskiModel 3} (hx : x ∈ domain D) (k : Fin 4) :
    harmonicGauge (metric D) (fun _ => crossAmplitude) x k = 0 :=
  harmonicGauge_cross hx k

example : ContDiffOn ℝ ∞ retarded (domain D) :=
  contDiffOn_retarded_domain

example (i j : Fin 4) : crossAmplitude i j = crossAmplitude j i :=
  crossAmplitude_symm i j

example {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    IsShortWaveGauge (metric D) (gradientCovector retarded z) crossAmplitude z :=
  isShortWaveGauge_cross_retarded hz

example (z : MinkowskiModel 3) :
    IsTTPolarization (metric D) (gradientCovector retarded z) crossAmplitude z :=
  isTTPolarization_cross z

example {x : MinkowskiModel 3} (hx : x ∈ domain D) (j k : Fin 4) :
    transportTerm (metric D) retarded (fun _ => crossAmplitude) x j k = 0 :=
  transportTerm_cross hx j k

example {x : MinkowskiModel 3} (hx : x ∈ domain D) (ε : ℝ)
    (j k : Fin 4) :
    familyRicciDeriv ((metric D).perturbationFamily
        (fun z => Real.cos (retarded z / ε) • crossAmplitude)) x j k =
      Real.cos (retarded x / ε) *
        familyRicciDeriv ((metric D).perturbationFamily (fun _ => crossAmplitude)) x j k :=
  familyRicciDeriv_cross_shortWave hx ε j k

end PlaneWave

section Longitudinal

open ExactPlaneWave PlaneWave

example (z : MinkowskiModel 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  longitudinalAmplitude z

example (z : MinkowskiModel 3) (m p q : Fin 4) :
    (minkowski .timeNegative 3 ⊤).covDerivTwo longitudinalAmplitude z m p q =
      (if m = 1 then 1 else 0) * crossAmplitude p q :=
  covDerivTwo_longitudinalAmplitude z m p q

example (z : MinkowskiModel 3) (i j : Fin 4) :
    waveHessian (minkowski .timeNegative 3 ⊤) retarded z i j = 0 :=
  waveHessian_minkowski_retarded z i j

example (z : MinkowskiModel 3) :
    (minkowski .timeNegative 3 ⊤).gradientField retarded z = rayDirection :=
  gradientField_minkowski_retarded z

example (z : MinkowskiModel 3) :
    IsShortWaveGauge (minkowski .timeNegative 3 ⊤) (gradientCovector retarded z)
      (longitudinalAmplitude z) z :=
  isShortWaveGauge_longitudinal z

example (z : MinkowskiModel 3) :
    transportOperator (minkowski .timeNegative 3 ⊤) retarded longitudinalAmplitude z = 0 ∧
      harmonicGauge (minkowski .timeNegative 3 ⊤) longitudinalAmplitude z 2 = 1 ∧
      transportTerm (minkowski .timeNegative 3 ⊤) retarded longitudinalAmplitude z 0 2 = 1 / 2 :=
  transportTerm_longitudinal z

end Longitudinal

end ProjectAinos.GeneralRelativity.ShortWave

open Set Filter TopologicalSpace Real
open scoped ContDiff Topology Matrix

namespace ProjectAinos.GeneralRelativity.ShortWave

open SmoothGeometry CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

section Definitions

variable (g : CoordinateMetric σ d U)

example (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (z : MinkowskiModel d) :
    Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ :=
  waveSymbol g ψ a z

example (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  quadraticLeading g ψ a x j k

example (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  oscillatingTerm g ψ a x j k

example (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (θ : ℝ) (j k : Fin (d + 1)) : ℝ :=
  stressProfile g ψ a x θ j k

example (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  secondRicciFirst g ψ a x j k

example (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  secondRicciZero g a x j k

end Definitions

section Expansion

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

example {n : ℕ} (c c' : ℝ) (P P' : Fin n → Fin n → Fin n → ℝ)
    (j k : Fin n) :
    christoffelQuadratic (c • P + c' • P') (c • P + c' • P') j k =
      c ^ 2 * christoffelQuadratic P P j k +
        c * c' * (christoffelQuadratic P P' j k + christoffelQuadratic P' P j k) +
        c' ^ 2 * christoffelQuadratic P' P' j k :=
  christoffelQuadratic_add_smul c c' P P' j k

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (b c e : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => waveSymbol g ψ a z b c e) U :=
  contDiffOn_waveSymbol hψ ha b c e

example (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U)
    {P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    (hP : ∀ b c e, ContDiffOn ℝ ∞ (fun z => P z b c e) U) (k i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => g.raiseContract a P z k i j) U :=
  contDiffOn_raiseContract ha hP k i j

example {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    g.secondRicci (fun z => F (ψ z) • a z) x j k / 2 =
      F (ψ x) ^ 2 * secondRicciZero g a x j k +
        F (ψ x) * deriv F (ψ x) * secondRicciFirst g ψ a x j k +
        deriv F (ψ x) ^ 2 * (quadraticLeading g ψ a x j k - oscillatingTerm g ψ a x j k) -
        F (ψ x) * deriv (deriv F) (ψ x) * oscillatingTerm g ψ a x j k :=
  secondRicci_phase hF hψ ha hx j k

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (ε : ℝ) (j k : Fin (d + 1)) :
    g.secondRicci (fun z => Real.cos (ψ z / ε) • a z) x j k / 2 =
      ε⁻¹ ^ 2 * stressProfile g ψ a x (ψ x / ε) j k -
        ε⁻¹ * (Real.sin (ψ x / ε) * Real.cos (ψ x / ε)) * secondRicciFirst g ψ a x j k +
        Real.cos (ψ x / ε) ^ 2 * secondRicciZero g a x j k :=
  secondRicci_shortWave hψ ha hx ε j k

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    Tendsto (fun ε : ℝ => ε ^ 2 * (g.secondRicci (fun z => Real.cos (ψ z / ε) • a z) x j k / 2) -
      stressProfile g ψ a x (ψ x / ε) j k) (𝓝[≠] 0) (𝓝 0) :=
  tendsto_secondRicci_shortWave hψ ha hx j k

end Expansion

example (Φ : ℝ → ℝ) : ℝ :=
  phaseAverage Φ

example : ∫ θ in (0 : ℝ)..2 * π, Real.sin θ ^ 2 = π :=
  integral_sin_sq_two_pi

example : ∫ θ in (0 : ℝ)..2 * π, Real.cos (2 * θ) = 0 :=
  integral_cos_two_mul_two_pi

example (X Y : ℝ) :
    phaseAverage (fun θ => Real.sin θ ^ 2 * X + Real.cos (2 * θ) * Y) = X / 2 :=
  phaseAverage_sin_sq_add_cos X Y

section Average

variable (g : CoordinateMetric σ d U)

example (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  averagedSecondRicci g ψ a x j k

example (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (κ : ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  effectiveStress g ψ a κ x j k

end Average

section AverageLemmas

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

example (x : MinkowskiModel d) (j k : Fin (d + 1)) :
    averagedSecondRicci g ψ a x j k = quadraticLeading g ψ a x j k / 2 :=
  averagedSecondRicci_eq x j k

end AverageLemmas

section Algebra

example {n : ℕ} {G A : Matrix (Fin n) (Fin n) ℝ}
    {κ : Fin n → ℝ} (hG : ∀ p q, G p q = G q p) (hA : ∀ p q, A p q = A q p)
    (hgauge : ∀ b, ∑ m, (∑ l, G m l * κ l) * A m b =
      κ b * (∑ l, ∑ m, G l m * A l m) / 2)
    (hnull : ∑ m, (∑ l, G m l * κ l) * κ m = 0) (j k : Fin n) :
    christoffelQuadratic (fun i j b => ∑ l, G i l * (κ j * A b l + κ b * A l j - κ l * A j b) / 2)
      (fun i j b => ∑ l, G i l * (κ j * A b l + κ b * A l j - κ l * A j b) / 2) j k =
      -((∑ c, ∑ e, G c e * ∑ p, ∑ q, G p q * (A c p * A e q)) -
        (∑ l, ∑ m, G l m * A l m) ^ 2 / 2) * κ j * κ k / 4 :=
  christoffelQuadratic_symbol_of_gauge hG hA hgauge hnull j k

end Algebra

section Stress

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

example {x : MinkowskiModel d} (hx : x ∈ U)
    (has : ∀ i j, a x i j = a x j i) (hg : IsShortWaveGauge g (gradientCovector ψ x) (a x) x)
    (hnull : g.gradientNorm ψ x = 0) (j k : Fin (d + 1)) :
    quadraticLeading g ψ a x j k =
      -(tensorPairing g (a x) (a x) x - amplitudeTrace g (a x) x ^ 2 / 2) *
        gradientCovector ψ x j * gradientCovector ψ x k / 4 :=
  quadraticLeading_of_gauge hx has hg hnull j k

example {x : MinkowskiModel d} (hx : x ∈ U)
    (has : ∀ i j, a x i j = a x j i) (hg : IsShortWaveGauge g (gradientCovector ψ x) (a x) x)
    (hnull : g.gradientNorm ψ x = 0) (j k : Fin (d + 1)) :
    averagedSecondRicci g ψ a x j k =
      -(tensorPairing g (a x) (a x) x - amplitudeTrace g (a x) x ^ 2 / 2) *
        gradientCovector ψ x j * gradientCovector ψ x k / 8 :=
  averagedSecondRicci_of_gauge hx has hg hnull j k

example (κ : ℝ) (x : MinkowskiModel d) (j k : Fin (d + 1)) :
    effectiveStress g ψ a κ x j k = effectiveStress g ψ a κ x k j :=
  effectiveStress_symm κ x j k

example (κ : ℝ) {x : MinkowskiModel d} (hnull : g.gradientNorm ψ x = 0) :
    ∑ j, ∑ k, (g.coefficient x)⁻¹ j k * effectiveStress g ψ a κ x j k = 0 :=
  effectiveStress_trace κ hnull

example {κ : ℝ} (hκ : κ ≠ 0) {x : MinkowskiModel d}
    (hx : x ∈ U) (has : ∀ i j, a x i j = a x j i)
    (hg : IsShortWaveGauge g (gradientCovector ψ x) (a x) x) (hnull : g.gradientNorm ψ x = 0)
    (j k : Fin (d + 1)) :
    averagedSecondRicci g ψ a x j k = -κ * (effectiveStress g ψ a κ x j k -
      g.coefficient x j k * (∑ p, ∑ q, (g.coefficient x)⁻¹ p q *
        effectiveStress g ψ a κ x p q) / 2) :=
  averagedSecondRicci_eq_effectiveStress hκ hx has hg hnull j k

end Stress

section Conservation

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

example (M B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) :
    tensorPairing g M B x = ∑ c, ∑ p, M c p *
      ∑ e, ∑ q, (g.coefficient x)⁻¹ c e * ((g.coefficient x)⁻¹ p q * B e q) :=
  tensorPairing_eq_raise M B x

example {x : MinkowskiModel d} (hx : x ∈ U)
    (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    tensorPairing g A B x = tensorPairing g B A x :=
  tensorPairing_symm hx A B

example (c : Fin (d + 1) → ℝ)
    (C : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) :
    tensorPairing g (Matrix.of fun p q => ∑ l, c l * C l p q) B x =
      ∑ l, c l * tensorPairing g (C l) B x :=
  tensorPairing_sum_left c C B x

example (c : ℝ) (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : tensorPairing g (c • A) B x = c * tensorPairing g A B x :=
  tensorPairing_smul_left c A B x

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (hnull : ∀ z ∈ U, g.gradientNorm ψ z = 0) {x : MinkowskiModel d} (hx : x ∈ U)
    (k : Fin (d + 1)) : ∑ l, g.gradientField ψ x l * waveHessian g ψ x l k = 0 :=
  sum_gradientField_waveHessian hψ hnull hx k

example (κ : ℝ) (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U)
    (hnull : ∀ z ∈ U, g.gradientNorm ψ z = 0) {x : MinkowskiModel d} (hx : x ∈ U)
    (htr : ∀ j k, transportOperator g ψ a x j k = 0) (k : Fin (d + 1)) :
    ∑ j, ∑ l, (g.coefficient x)⁻¹ j l *
      g.covDerivTwo (fun z => Matrix.of fun j k => effectiveStress g ψ a κ z j k) x l j k = 0 :=
  effectiveStress_conserved κ hψ ha hnull hx htr k

end Conservation

section Flux

example (z : MinkowskiModel d) :
    ((minkowski σ d U).coefficient z)⁻¹ = Minkowski.metricMatrix σ d :=
  coefficient_inv_minkowski z

example (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (z : MinkowskiModel d) :
    tensorPairing (minkowski σ d U) A B z =
      ∑ c, ∑ p, lorentzSign σ c * lorentzSign σ p * (A c p * B c p) :=
  tensorPairing_minkowski A B z

example (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (z : MinkowskiModel d) :
    amplitudeTrace (minkowski σ d U) A z = flatTrace σ A :=
  amplitudeTrace_minkowski A z

example : lorentzSign (d := 3) .timeNegative 0 = -1 :=
  lorentzSign_timeNegative_zero

example (α : Fin 3) :
    lorentzSign (d := 3) .timeNegative α.succ = 1 :=
  lorentzSign_timeNegative_succ α

example (A : Matrix (Fin 4) (Fin 4) ℝ) :
    flatTrace .timeNegative A = -A 0 0 + A 1 1 + A 2 2 + A 3 3 :=
  flatTrace_timeNegative A

example {n : EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ a b, A a b = A b a)
    (hg : ∀ b, A 0 b = -∑ α : Fin 3, n α * A α.succ b) :
    (∑ c : Fin 4, ∑ p : Fin 4, lorentzSign .timeNegative c * lorentzSign .timeNegative p *
        (traceReverse .timeNegative A c p * traceReverse .timeNegative A c p)) -
      flatTrace .timeNegative (traceReverse .timeNegative A) ^ 2 / 2 =
      Wave.ttSquare n (fun i j => A i.succ j.succ) :=
  pairing_traceReverse_of_gauge hA hg

example (κv : Fin (d + 1) → ℝ)
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (κ : ℝ) (z : MinkowskiModel d)
    (j k : Fin (d + 1)) :
    effectiveStress (minkowski σ d U) (fun y => ∑ i, κv i * y i) (fun _ => A) κ z j k =
      ((∑ c, ∑ p, lorentzSign σ c * lorentzSign σ p * (A c p * A c p)) -
        flatTrace σ A ^ 2 / 2) * κv j * κv k / (8 * κ) :=
  effectiveStress_minkowski_linear κv A κ z j k

example {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1)
    {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ a b, A a b = A b a)
    (hg : ∀ b, A 0 b = -∑ α : Fin 3, n α * A α.succ b) (κ : ℝ) (z : MinkowskiModel 3) :
    -∑ α : Fin 3, effectiveStress (minkowski .timeNegative 3 ⊤)
        (fun y => ∑ i, Wave.waveCovector n i * y i) (fun _ => traceReverse .timeNegative A) κ z
        0 α.succ * n α =
      Wave.ttSquare n (fun i j => A i.succ j.succ) / (8 * κ) :=
  effectiveStress_flux hn hA hg κ z

example {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1)
    {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ a b, A a b = A b a)
    (hg : ∀ b, A 0 b = -∑ α : Fin 3, n α * A α.succ b) (c : ℝ) :
    Wave.planeFlux n (traceReverse .timeNegative (c • A)) =
      c ^ 2 * Wave.ttSquare n (fun i j => A i.succ j.succ) / 4 :=
  planeFlux_traceReverse_smul hn hA hg c

example {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1)
    {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ a b, A a b = A b a)
    (hg : ∀ b, A 0 b = -∑ α : Fin 3, n α * A α.succ b) (κ : ℝ) (z : MinkowskiModel 3) :
    -∑ α : Fin 3, effectiveStress (minkowski .timeNegative 3 ⊤)
        (fun y => ∑ i, Wave.waveCovector n i * y i) (fun _ => traceReverse .timeNegative A) κ z
        0 α.succ * n α =
      phaseAverage fun θ =>
        Wave.planeFlux n (traceReverse .timeNegative ((-Real.sin θ) • A)) / κ :=
  effectiveStress_flux_eq_average hn hA hg κ z

end Flux

section Gradient

variable (g : CoordinateMetric σ d U)

example (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  gradientSquare g h x j k

variable {g} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

example (c₁ c₂ c₃ c₄ : ℝ)
    (A₁ A₂ B₁ B₂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) :
    tensorPairing g (c₁ • A₁ + c₂ • A₂) (c₃ • B₁ + c₄ • B₂) x =
      c₁ * c₃ * tensorPairing g A₁ B₁ x + c₁ * c₄ * tensorPairing g A₁ B₂ x +
        c₂ * c₃ * tensorPairing g A₂ B₁ x + c₂ * c₄ * tensorPairing g A₂ B₂ x :=
  tensorPairing_add_smul c₁ c₂ c₃ c₄ A₁ A₂ B₁ B₂ x

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    {ε : ℝ} (hε : ε ≠ 0) (j : Fin (d + 1)) :
    g.covDerivMatrix (fun z => (ε * Real.cos (ψ z / ε)) • a z) x j =
      (-(Real.sin (ψ x / ε) * gradientCovector ψ x j)) • a x +
        (ε * Real.cos (ψ x / ε)) • g.covDerivMatrix a x j :=
  covDerivMatrix_shortWave hψ ha hx hε j

example (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    Tendsto (fun ε : ℝ => gradientSquare g (fun z => (ε * Real.cos (ψ z / ε)) • a z) x j k -
      Real.sin (ψ x / ε) ^ 2 * ((tensorPairing g (a x) (a x) x -
        amplitudeTrace g (a x) x ^ 2 / 2) * gradientCovector ψ x j * gradientCovector ψ x k))
      (𝓝[≠] 0) (𝓝 0) :=
  tendsto_gradientSquare_shortWave hψ ha hx j k

example (κ : ℝ) (x : MinkowskiModel d) (j k : Fin (d + 1)) :
    effectiveStress g ψ a κ x j k = phaseAverage (fun θ => Real.sin θ ^ 2 *
      ((tensorPairing g (a x) (a x) x - amplitudeTrace g (a x) x ^ 2 / 2) *
        gradientCovector ψ x j * gradientCovector ψ x k)) / (4 * κ) :=
  effectiveStress_eq_average_gradient κ x j k

end Gradient

namespace PlaneWave

open ExactPlaneWave

variable {D : Data}

example {x : MinkowskiModel 3} (hx : x ∈ domain D) (κ : ℝ) (j k : Fin 4) :
    effectiveStress (metric D) retarded (fun _ => crossAmplitude) κ x j k =
      nullCovector j * nullCovector k /
        (4 * κ * D.a (retarded x) ^ 2 * D.b (retarded x) ^ 2) :=
  effectiveStress_cross hx κ j k

example (κ : ℝ) {x : MinkowskiModel 3} (hx : x ∈ domain D)
    (k : Fin 4) :
    ∑ j, ∑ l, ((metric D).coefficient x)⁻¹ j l * (metric D).covDerivTwo
      (fun z => Matrix.of fun j k => effectiveStress (metric D) retarded
        (fun _ => crossAmplitude) κ z j k) x l j k = 0 :=
  effectiveStress_cross_conserved κ hx k

example {κ : ℝ} (hκ : κ ≠ 0) {x : MinkowskiModel 3}
    (hx : x ∈ domain D) (j k : Fin 4) :
    averagedSecondRicci (metric D) retarded (fun _ => crossAmplitude) x j k =
      -κ * (effectiveStress (metric D) retarded (fun _ => crossAmplitude) κ x j k -
        (metric D).coefficient x j k * (∑ p, ∑ q, ((metric D).coefficient x)⁻¹ p q *
          effectiveStress (metric D) retarded (fun _ => crossAmplitude) κ x p q) / 2) :=
  averagedSecondRicci_cross hκ hx j k

end PlaneWave

example : EuclideanSpace ℝ (Fin 3) :=
  unitZ

example (κ : ℝ) (z : MinkowskiModel 3) :
    -∑ α : Fin 3, effectiveStress (minkowski .timeNegative 3 ⊤)
        (fun y => ∑ i, Wave.waveCovector unitZ i * y i)
        (fun _ => traceReverse .timeNegative PlaneWave.crossAmplitude) κ z 0 α.succ * unitZ α =
      1 / (4 * κ) :=
  effectiveStress_flux_cross κ z

end ProjectAinos.GeneralRelativity.ShortWave
