/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CovariantLeibniz
public import ProjectAinos.GeneralRelativity.ShortWave

/-!
# The transport of the amplitude of a short gravitational wave

Landau–Lifshitz, §108. For the short wave `h = a cos(ψ/ε)` on a background coordinate metric `g`,
`familyRicciDeriv_shortWave` gives the coefficient of `−ε⁻¹ sin(ψ/ε)` in `δRic[h]` as the exact
array `R₁ = transportTerm`. This file writes it covariantly, with `k = dψ`, `k^♯ = gradientField`,
`∇_i k_j = waveHessian` and `∇_m a_{pq} = covDerivTwo`.

* `transportTerm_eq`: for a smooth phase and a smooth symmetric amplitude, exactly,
  `R₁ = −½ (2∇_k a + θ a) + ½ (W_{jk} + W_{kj}) + ½ (k_j D_k + k_k D_j) − ½ (k_j T_k + k_k T_j)
  − ½ (∇_j k_k) tr a`, with the transport operator `2∇_k a + θ a` (`transportOperator`,
  `θ = ∇·k^♯` the `rayExpansion`), `W = ∇(k·a)` written by the Leibniz rule
  (`contractionDerivative`), `D = div a` (`amplitudeDivergence`) and `T = ∇ tr a`
  (`traceGradient`). No hypothesis on the background or on `ψ` is needed.
* `transportTerm_of_gauge`: in the gauge `k^a ā_{ab} = 0` on `U` (`IsShortWaveGauge`),
  `R₁ = −½ (2∇_k a + θ a) + ½ (k_j B_k + k_k B_j)`, where `B = div ā = harmonicGauge a` is the
  longitudinal part.
* **The transverse polarizations.** `sum_transverse_transportTerm`: for a symmetric `e^{jk}` with
  `e^{jk} k_k = 0`, `e^{jk} R₁_{jk} = −½ e^{jk} (2∇_k a + θ a)_{jk}`; hence
  `transverse_transportTerm_iff`: the `ε⁻¹` order vanishes on all transverse (in particular all
  transverse traceless) polarizations exactly when the transport equation holds on them, and
  `sum_transverse_familyRicciDeriv_shortWave`: on a null phase,
  `e^{jk} δRic[a cos(ψ/ε)]_{jk} = ½ ε⁻¹ sin(ψ/ε) e^{jk} (2∇_k a + θa)_{jk} + cos(ψ/ε) e^{jk}
  δRic[a]_{jk}`.
* **The full amplitude.** `harmonicGauge_shortWave`: the harmonic gauge vector of the family is
  `div h̄ = −ε⁻¹ sin(ψ/ε) k^a ā_{ab} + cos(ψ/ε) div ā`; its two orders are the gauge of the
  amplitude and the next-order condition `div ā = 0`. With both, `transportTerm_of_harmonic`:
  `R₁ = −½ (2∇_k a + θ a)`, so `transportTerm_eq_zero_iff`: the `ε⁻¹` order vanishes exactly when
  the full amplitude satisfies the transport equation `2∇_k a + (∇·k) a = 0`.
* **Instances.** Flat space with a linear null phase and a constant amplitude in the gauge
  (`transportTerm_minkowski_const`), and the cross amplitude on every diagonal plane wave of §109
  (`PlaneWave.transportTerm_cross`): the rays have `θ = 0` and the cross amplitude is transported
  and satisfies `div ā = 0`, so `δRic[a cos(u/ε)] = cos(u/ε) δRic[a]` exactly
  (`PlaneWave.familyRicciDeriv_cross_shortWave`); the cross polarization is transverse traceless
  (`PlaneWave.isTTPolarization_cross`).
* **The longitudinal terms are not zero in general.** `transportTerm_longitudinal`: in flat space
  the amplitude `a = z¹ e₊ₓ` with the phase `u = t − z` is in the gauge and transported, but
  `div ā ≠ 0`, and the `ε⁻¹` coefficient `R₁_{02} = ½` does not vanish; only its transverse
  projection does. The next-order gauge condition is needed for the full amplitude.

The transport identities need no field equation for the background: the Ricci-flat hypothesis of
the outline enters only at order `ε⁰`.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.ShortWave

open SmoothGeometry CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

section Definitions

variable (g : CoordinateMetric σ d U)

/-- The covariant Hessian `∇_i k_j = ∇_i ∂_j ψ` of a phase. -/
def waveHessian (ψ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) (i j : Fin (d + 1)) : ℝ :=
  g.covDerivOne (gradientCovector ψ) x i j

/-- The expansion `θ = ∇·k^♯ = g^{il} ∇_i k_l` of the rays. -/
def rayExpansion (ψ : MinkowskiModel d → ℝ) (x : MinkowskiModel d) : ℝ :=
  ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * waveHessian g ψ x i l

/-- The derivative `∇_k a_{jl} = k^m ∇_m a_{jl}` along the rays. -/
def rayDerivative (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  ∑ l, g.gradientField ψ x l * g.covDerivTwo a x l j k

/-- **The transport operator** `2∇_k a + θ a` of the amplitude. -/
def transportOperator (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  2 * rayDerivative g ψ a x j k + rayExpansion g ψ x * a x j k

/-- The divergence `D_k = g^{il} ∇_i a_{lk}` of the amplitude. -/
def amplitudeDivergence (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (k : Fin (d + 1)) : ℝ :=
  ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * g.covDerivTwo a x i l k

/-- The gradient `T_k = g^{il} ∇_k a_{il} = ∂_k tr a` of the trace (`fderiv_trace`). -/
def traceGradient (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (k : Fin (d + 1)) : ℝ :=
  ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * g.covDerivTwo a x k i l

/-- **The harmonic gauge vector** `B_k = ∇^i ā_{ik} = D_k − ½ T_k`, the divergence of the trace
reverse of a field of matrices. -/
def harmonicGauge (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (k : Fin (d + 1)) : ℝ :=
  amplitudeDivergence g a x k - traceGradient g a x k / 2

/-- The covariant derivative `∇_j (k·a)_k = (∇_j k^m) a_{mk} + k^m ∇_j a_{mk}` of the
contraction, written by the Leibniz rule (`covDerivOne_raise_contract`). -/
def contractionDerivative (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  ∑ m, (∑ l, (g.coefficient x)⁻¹ m l * waveHessian g ψ x j l) * a x m k +
    ∑ m, g.gradientField ψ x m * g.covDerivTwo a x j m k

end Definitions

/-! ### The covariant form of the transport term -/

section Expansion

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

/-- A double sum against the symmetric inverse metric may have its indices exchanged. -/
theorem sum_coefficient_inv_swap {x : MinkowskiModel d} (hx : x ∈ U)
    (F : Fin (d + 1) → Fin (d + 1) → ℝ) :
    ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * F i l = ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * F l i := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by
    rw [g.coefficient_inv_symmetric hx l i]

/-- Contracting a covector with a raised index: `k_i g^{il} X_l = (k^♯)^l X_l`. -/
theorem sum_mul_coefficient_inv {x : MinkowskiModel d} (hx : x ∈ U) (X : Fin (d + 1) → ℝ) :
    ∑ i, gradientCovector ψ x i * ∑ l, (g.coefficient x)⁻¹ i l * X l / 2 =
      ∑ l, g.gradientField ψ x l * X l / 2 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [gradientField, Finset.sum_mul, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by rw [g.coefficient_inv_symmetric hx l i]; ring

theorem waveHessian_symm (hψ : ContDiffOn ℝ ∞ ψ U) {x : MinkowskiModel d} (hx : x ∈ U)
    (i j : Fin (d + 1)) : waveHessian g ψ x i j = waveHessian g ψ x j i :=
  covDerivOne_gradient_symm hx ((hψ.contDiffAt (U.isOpen.mem_nhds hx)).of_le (by simp)) i j

/-- **The covariant expansion of the transport term.** For a smooth phase `ψ` and a smooth
symmetric amplitude `a`, the coefficient `R₁` of `−ε⁻¹ sin(ψ/ε)` in `δRic[a cos(ψ/ε)]` is
`−½ (2∇_k a + θ a) + ½ (W_{jk} + W_{kj}) + ½ (k_j D_k + k_k D_j) − ½ (k_j T_k + k_k T_j)
− ½ (∇_j k_k) tr a`. -/
theorem transportTerm_eq (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    transportTerm g ψ a x j k =
      -transportOperator g ψ a x j k / 2 +
        (contractionDerivative g ψ a x j k + contractionDerivative g ψ a x k j) / 2 +
        (gradientCovector ψ x j * amplitudeDivergence g a x k +
          gradientCovector ψ x k * amplitudeDivergence g a x j) / 2 -
        (gradientCovector ψ x j * traceGradient g a x k +
          gradientCovector ψ x k * traceGradient g a x j) / 2 -
        waveHessian g ψ x j k * amplitudeTrace g (a x) x / 2 := by
  have hkd (i : Fin (d + 1)) : DifferentiableAt ℝ (fun z => gradientCovector ψ z i) x :=
    differentiableAt_of_contDiffOn (contDiffOn_gradientCovector hψ i) hx
  have had (p q : Fin (d + 1)) : DifferentiableAt ℝ (fun z => a z p q) x :=
    differentiableAt_of_contDiffOn (ha p q) hx
  set G := (g.coefficient x)⁻¹ with hGdef
  set H := waveHessian g ψ x with hHdef
  set κ := gradientCovector ψ x with hκdef
  set A := a x with hAdef
  set K := g.gradientField ψ x with hKdef
  set C : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ := fun m p q => g.covDerivTwo a x m p q
    with hCdef
  have hG (p q : Fin (d + 1)) : G p q = G q p := g.coefficient_inv_symmetric hx p q
  have hH (p q : Fin (d + 1)) : H p q = H q p := waveHessian_symm hψ hx p q
  have hA (p q : Fin (d + 1)) : A p q = A q p := has x hx p q
  have hC (m p q : Fin (d + 1)) : C m p q = C m q p := covDerivTwo_symm has hx m p q
  have hK (l : Fin (d + 1)) : K l = ∑ i, G l i * κ i := rfl
  have hsw := sum_coefficient_inv_swap (g := g) hx
  -- the Palatini part through the Leibniz rule
  have hpal : g.palatini (fun z => g.symbolChristoffel (gradientCovector ψ z) (a z) z) x j k =
      ∑ i, (g.symbolChristoffel (fun c => H i c) A x i j k +
        g.symbolChristoffel κ (Matrix.of fun p q => C i p q) x i j k -
        (g.symbolChristoffel (fun c => H j c) A x i i k +
          g.symbolChristoffel κ (Matrix.of fun p q => C j p q) x i i k)) := by
    unfold palatini
    simp only [covDerivThree_symbolChristoffel (w := gradientCovector ψ) hx hkd had]
    rfl
  -- the six pieces
  have Pa : ∑ i, κ i * g.curvedChristoffel a x i j k =
      (∑ m, K m * C j m k + ∑ m, K m * C k m j - rayDerivative g ψ a x j k) / 2 := by
    unfold curvedChristoffel
    rw [sum_mul_coefficient_inv hx]
    unfold rayDerivative
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun l _ => by
      rw [covDerivTwo_symm has hx j k l, hKdef]
      ring
  have Pb : ∑ i, g.curvedChristoffel a x i i k = traceGradient g a x k / 2 := by
    unfold curvedChristoffel traceGradient
    have e1 : ∑ i, ∑ l, G i l * C l i k = ∑ i, ∑ l, G i l * C i k l := by
      rw [hsw (fun i l => C l i k)]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [hC i l k]
    have e2 : ∑ i, ∑ l, G i l * C k l i = ∑ i, ∑ l, G i l * C k i l :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [hC k l i]
    have e3 : ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * (g.covDerivTwo a x i k l +
        g.covDerivTwo a x k l i - g.covDerivTwo a x l i k) / 2 =
        (∑ i, ∑ l, G i l * C i k l + ∑ i, ∑ l, G i l * C k l i -
          ∑ i, ∑ l, G i l * C l i k) / 2 := by
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    rw [e3, e1, e2]
    ring
  have Pc : ∑ i, g.symbolChristoffel (fun c => H i c) A x i j k =
      (∑ m, (∑ l, G m l * H j l) * A m k + ∑ m, (∑ l, G m l * H k l) * A m j -
        rayExpansion g ψ x * A j k) / 2 := by
    unfold symbolChristoffel rayExpansion
    have e1 (p q : Fin (d + 1)) : ∑ i, ∑ l, G i l * (H i p * A q l) =
        ∑ m, (∑ l, G m l * H p l) * A m q := by
      rw [hsw]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by rw [hH l p, hA q i]; ring
    have e3 : ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * (H i j * A k l + H i k * A l j -
        H i l * A j k) / 2 = (∑ i, ∑ l, G i l * (H i j * A k l) +
          ∑ i, ∑ l, G i l * (H i k * A j l) - (∑ i, ∑ l, G i l * H i l) * A j k) / 2 := by
      simp only [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by
        rw [hA l j]; ring
    rw [e3, e1, e1]
  have Pd : ∑ i, g.symbolChristoffel κ (Matrix.of fun p q => C i p q) x i j k =
      (κ j * amplitudeDivergence g a x k + κ k * amplitudeDivergence g a x j -
        rayDerivative g ψ a x j k) / 2 := by
    unfold symbolChristoffel amplitudeDivergence rayDerivative
    simp only [Matrix.of_apply]
    have e1 : ∑ i, ∑ l, G i l * (κ l * C i j k) = ∑ l, K l * C l j k := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hK, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    have e3 : ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * (κ j * C i k l + κ k * C i l j -
        κ l * C i j k) / 2 = (κ j * ∑ i, ∑ l, G i l * C i l k +
          κ k * ∑ i, ∑ l, G i l * C i l j - ∑ i, ∑ l, G i l * (κ l * C i j k)) / 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by
        rw [hC i k l]; ring
    rw [e3, e1]
  have Pe : ∑ i, g.symbolChristoffel (fun c => H j c) A x i i k =
      H j k * amplitudeTrace g A x / 2 := by
    unfold symbolChristoffel amplitudeTrace
    have e1 : ∑ i, ∑ l, G i l * (H j l * A i k) = ∑ i, ∑ l, G i l * (H j i * A k l) := by
      rw [hsw]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [hA l k]
    have e3 : ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * (H j i * A k l + H j k * A l i -
        H j l * A i k) / 2 = (∑ i, ∑ l, G i l * (H j i * A k l) +
          H j k * ∑ i, ∑ l, G i l * A i l - ∑ i, ∑ l, G i l * (H j l * A i k)) / 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by
        rw [hA l i]; ring
    rw [e3, e1]
    ring
  have Pf : ∑ i, g.symbolChristoffel κ (Matrix.of fun p q => C j p q) x i i k =
      κ k * traceGradient g a x j / 2 := by
    unfold symbolChristoffel traceGradient
    simp only [Matrix.of_apply]
    have e1 : ∑ i, ∑ l, G i l * (κ l * C j i k) = ∑ i, ∑ l, G i l * (κ i * C j k l) := by
      rw [hsw]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [hC j l k]
    have e3 : ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * (κ i * C j k l + κ k * C j l i -
        κ l * C j i k) / 2 = (∑ i, ∑ l, G i l * (κ i * C j k l) +
          κ k * ∑ i, ∑ l, G i l * C j i l - ∑ i, ∑ l, G i l * (κ l * C j i k)) / 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by
        rw [hC j l i]; ring
    rw [e3, e1]
    ring
  -- assemble
  have hgc : gradientContraction κ (g.curvedChristoffel a x) j k =
      ∑ i, κ i * g.curvedChristoffel a x i j k - κ j * ∑ i, g.curvedChristoffel a x i i k := by
    unfold gradientContraction
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have hpal' : ∑ i, (g.symbolChristoffel (fun c => H i c) A x i j k +
      g.symbolChristoffel κ (Matrix.of fun p q => C i p q) x i j k -
      (g.symbolChristoffel (fun c => H j c) A x i i k +
        g.symbolChristoffel κ (Matrix.of fun p q => C j p q) x i i k)) =
      ∑ i, g.symbolChristoffel (fun c => H i c) A x i j k +
        ∑ i, g.symbolChristoffel κ (Matrix.of fun p q => C i p q) x i j k -
        (∑ i, g.symbolChristoffel (fun c => H j c) A x i i k +
          ∑ i, g.symbolChristoffel κ (Matrix.of fun p q => C j p q) x i i k) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  unfold transportTerm
  rw [hpal, hgc, hpal', Pa, Pb, Pc, Pd, Pe, Pf]
  unfold transportOperator contractionDerivative
  ring

end Expansion

/-! ### The gauge and the longitudinal terms -/

section Gauge

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

/-- The contraction derivative is the covariant derivative of `(k·a)_k = k^m a_{mk}`. -/
theorem contractionDerivative_eq (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    contractionDerivative g ψ a x j k =
      g.covDerivOne (fun z => contractAmplitude g (gradientCovector ψ z) (a z) z) x j k := by
  have h := covDerivOne_raise_contract (g := g) (w := gradientCovector ψ) (A := a) hx
    (fun i => differentiableAt_of_contDiffOn (contDiffOn_gradientCovector hψ i) hx)
    (fun p q => differentiableAt_of_contDiffOn (ha p q) hx) j k
  exact h.symm

/-- The derivative of the trace: `∂_j tr a = T_j`. -/
theorem gradientCovector_amplitudeTrace (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U)
    {x : MinkowskiModel d} (hx : x ∈ U) (j : Fin (d + 1)) :
    gradientCovector (fun z => amplitudeTrace g (a z) z) x j = traceGradient g a x j :=
  fderiv_trace hx (fun p q => differentiableAt_of_contDiffOn (ha p q) hx) j

theorem differentiableAt_amplitudeTrace (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U)
    {x : MinkowskiModel d} (hx : x ∈ U) :
    DifferentiableAt ℝ (fun z => amplitudeTrace g (a z) z) x :=
  DifferentiableAt.fun_sum fun l _ => DifferentiableAt.fun_sum fun m _ =>
    (differentiableAt_coefficient_inv hx l m).fun_mul (differentiableAt_of_contDiffOn (ha l m) hx)

/-- In the gauge on `U`, `∇_j (k·a)_k = ½ (∂_j tr a) k_k + ½ (tr a) ∇_j k_k`. -/
theorem contractionDerivative_of_gauge (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    contractionDerivative g ψ a x j k =
      traceGradient g a x j * gradientCovector ψ x k / 2 +
        amplitudeTrace g (a x) x * waveHessian g ψ x j k / 2 := by
  rw [contractionDerivative_eq hψ ha hx]
  have hev : (fun z => contractAmplitude g (gradientCovector ψ z) (a z) z) =ᶠ[𝓝 x]
      fun z => (2⁻¹ * amplitudeTrace g (a z) z) • gradientCovector ψ z := by
    filter_upwards [U.isOpen.mem_nhds hx] with z hz
    funext b
    rw [(isShortWaveGauge_iff hz _ _).mp (hg z hz) b]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hτ := differentiableAt_amplitudeTrace (g := g) ha hx
  rw [covDerivOne_congr hev, covDerivOne_smul (hτ.const_mul _)
    (fun i => differentiableAt_of_contDiffOn (contDiffOn_gradientCovector hψ i) hx)]
  have hd : gradientCovector (fun z => 2⁻¹ * amplitudeTrace g (a z) z) x j =
      2⁻¹ * traceGradient g a x j := by
    unfold gradientCovector
    rw [fderiv_const_mul hτ, _root_.smul_apply, smul_eq_mul]
    exact congrArg _ (gradientCovector_amplitudeTrace ha hx j)
  rw [hd]
  unfold waveHessian
  ring

/-- **The transport term in the gauge** `k^a ā_{ab} = 0` on `U`:
`R₁ = −½ (2∇_k a + θ a) + ½ (k_j B_k + k_k B_j)` with `B = div ā` (`harmonicGauge`). -/
theorem transportTerm_of_gauge (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    transportTerm g ψ a x j k =
      -transportOperator g ψ a x j k / 2 +
        (gradientCovector ψ x j * harmonicGauge g a x k +
          gradientCovector ψ x k * harmonicGauge g a x j) / 2 := by
  rw [transportTerm_eq hψ ha has hx, contractionDerivative_of_gauge hψ ha hg hx,
    contractionDerivative_of_gauge hψ ha hg hx, waveHessian_symm hψ hx k j]
  unfold harmonicGauge
  ring

/-- A transverse polarization at `x`: a symmetric `e^{jk}` with `e^{jk} k_k = 0`. -/
def IsTransversePolarization (k : Fin (d + 1) → ℝ) (e : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Prop :=
  (∀ i j, e i j = e j i) ∧ ∀ i, ∑ j, e i j * k j = 0

variable (g) in
/-- A transverse traceless polarization: transverse, with `g_{jk} e^{jk} = 0`. -/
def IsTTPolarization (k : Fin (d + 1) → ℝ) (e : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : Prop :=
  IsTransversePolarization k e ∧ ∑ i, ∑ j, g.coefficient x i j * e i j = 0

/-- **The transport equation on the transverse polarizations.** In the gauge on `U`, for a
transverse polarization `e`, `e^{jk} R₁_{jk} = −½ e^{jk} (2∇_k a + θ a)_{jk}`: the longitudinal
terms drop out. -/
theorem sum_transverse_transportTerm (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) {e : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (he : IsTransversePolarization (gradientCovector ψ x) e) :
    ∑ j, ∑ k, e j k * transportTerm g ψ a x j k =
      -(∑ j, ∑ k, e j k * transportOperator g ψ a x j k) / 2 := by
  obtain ⟨hes, het⟩ := he
  simp only [transportTerm_of_gauge hψ ha has hg hx]
  set κ := gradientCovector ψ x
  set B := harmonicGauge g a x
  have h1 : ∑ j, ∑ k, e j k * (κ j * B k) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := het k
    calc ∑ j, e j k * (κ j * B k) = (∑ j, e k j * κ j) * B k := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by rw [hes j k]; ring
      _ = 0 := by rw [this, zero_mul]
  have h2 : ∑ j, ∑ k, e j k * (κ k * B j) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have := het j
    calc ∑ k, e j k * (κ k * B j) = (∑ k, e j k * κ k) * B j := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := by rw [this, zero_mul]
  have e1 (j k : Fin (d + 1)) : e j k * (-transportOperator g ψ a x j k / 2 +
      (κ j * B k + κ k * B j) / 2) = -(e j k * transportOperator g ψ a x j k) / 2 +
        e j k * (κ j * B k) / 2 + e j k * (κ k * B j) / 2 := by ring
  simp only [e1, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_neg_distrib]
  rw [h1, h2]
  ring

/-- **The `ε⁻¹` order on the transverse traceless polarizations is the transport equation.** -/
theorem transverse_transportTerm_iff (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) :
    (∀ e, IsTTPolarization g (gradientCovector ψ x) e x →
        ∑ j, ∑ k, e j k * transportTerm g ψ a x j k = 0) ↔
      ∀ e, IsTTPolarization g (gradientCovector ψ x) e x →
        ∑ j, ∑ k, e j k * transportOperator g ψ a x j k = 0 := by
  refine forall_congr' fun e => imp_congr_right fun he => ?_
  rw [sum_transverse_transportTerm hψ ha has hg hx he.1]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **The linearized Ricci tensor of a short wave on the transverse polarizations.** For a null
phase and an amplitude in the gauge, `e^{jk} δRic[a cos(ψ/ε)]_{jk} = ½ ε⁻¹ sin(ψ/ε)
e^{jk} (2∇_k a + θ a)_{jk} + cos(ψ/ε) e^{jk} δRic[a]_{jk}`, exactly, for every `ε`. -/
theorem sum_transverse_familyRicciDeriv_shortWave (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) (hnull : g.gradientNorm ψ x = 0)
    {e : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (he : IsTransversePolarization (gradientCovector ψ x) e) (ε : ℝ) :
    ∑ j, ∑ k, e j k *
        familyRicciDeriv (g.perturbationFamily (fun z => Real.cos (ψ z / ε) • a z)) x j k =
      ε⁻¹ * Real.sin (ψ x / ε) * (∑ j, ∑ k, e j k * transportOperator g ψ a x j k) / 2 +
        Real.cos (ψ x / ε) * ∑ j, ∑ k, e j k * familyRicciDeriv (g.perturbationFamily a) x j k := by
  have hS (j k : Fin (d + 1)) : shortWaveSymbol g (gradientCovector ψ x) (a x) x j k = 0 := by
    rw [shortWaveSymbol_of_gauge hx (hg x hx)]
    have : covectorNorm g (gradientCovector ψ x) x = 0 := hnull
    rw [this]
    ring
  simp only [familyRicciDeriv_shortWave hψ ha has hx ε, hS, mul_zero, zero_sub]
  have hT := sum_transverse_transportTerm hψ ha has hg hx he
  have e1 : ∑ j, ∑ k, e j k * (-(ε⁻¹ * Real.sin (ψ x / ε) * transportTerm g ψ a x j k) +
      Real.cos (ψ x / ε) * familyRicciDeriv (g.perturbationFamily a) x j k) =
      -(ε⁻¹ * Real.sin (ψ x / ε)) * ∑ j, ∑ k, e j k * transportTerm g ψ a x j k +
        Real.cos (ψ x / ε) * ∑ j, ∑ k, e j k * familyRicciDeriv (g.perturbationFamily a) x j k := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e1, hT]
  ring

/-! ### The full amplitude and the next-order gauge -/

/-- The harmonic gauge vector of `f a`: `B[f a]_k = (df)^m ā_{mk} + f B[a]_k`. -/
theorem harmonicGauge_smul {f : MinkowskiModel d → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (hf : DifferentiableAt ℝ f x) (k : Fin (d + 1)) :
    harmonicGauge g (fun z => f z • a z) x k =
      ∑ m, raiseCovector g (gradientCovector f x) x m *
          (a x m k - g.coefficient x m k * amplitudeTrace g (a x) x / 2) +
        f x * harmonicGauge g a x k := by
  have had (p q : Fin (d + 1)) : DifferentiableAt ℝ (fun z => a z p q) x :=
    differentiableAt_of_contDiffOn (ha p q) hx
  unfold harmonicGauge amplitudeDivergence traceGradient
  simp only [covDerivTwo_smul hf had]
  unfold amplitudeTrace
  set G := (g.coefficient x)⁻¹
  set w := gradientCovector f x
  set τ := ∑ l, ∑ m, G l m * a x l m
  have hgauge : ∑ m, raiseCovector g w x m * (a x m k - g.coefficient x m k * τ / 2) =
      ∑ i, ∑ l, G i l * (w i * a x l k) - w k * τ / 2 := by
    have h1 : ∑ m, raiseCovector g w x m * g.coefficient x m k = w k :=
      sum_raiseCovector_mul_coefficient hx w k
    have h2 : ∑ m, raiseCovector g w x m * (a x m k - g.coefficient x m k * τ / 2) =
        ∑ m, raiseCovector g w x m * a x m k -
          (∑ m, raiseCovector g w x m * g.coefficient x m k) * τ / 2 := by
      rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [h2, h1]
    congr 1
    unfold raiseCovector
    rw [sum_coefficient_inv_swap hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hgauge]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div, add_div,
    τ]
  simp only [mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv]
  ring

/-- **The harmonic gauge of the short-wave family.** For `h = a cos(ψ/ε)`, exactly,
`div h̄ = −ε⁻¹ sin(ψ/ε) k^m ā_{mk} + cos(ψ/ε) div ā`: the two orders are the gauge
`k^m ā_{mk} = 0` of `IsShortWaveGauge` and the next-order condition `div ā = 0`. -/
theorem harmonicGauge_shortWave (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (ε : ℝ) (k : Fin (d + 1)) :
    harmonicGauge g (fun z => Real.cos (ψ z / ε) • a z) x k =
      -(ε⁻¹ * Real.sin (ψ x / ε)) * ∑ m, raiseCovector g (gradientCovector ψ x) x m *
          (a x m k - g.coefficient x m k * amplitudeTrace g (a x) x / 2) +
        Real.cos (ψ x / ε) * harmonicGauge g a x k := by
  have hψd : DifferentiableAt ℝ ψ x := differentiableAt_of_contDiffOn hψ hx
  have hF (u : ℝ) : HasDerivAt (fun u => Real.cos (u / ε)) (-(Real.sin (u / ε) * ε⁻¹)) u := by
    have h := ((hasDerivAt_id u).div_const ε).cos
    simpa [div_eq_mul_inv] using h
  have hf : DifferentiableAt ℝ (fun z => Real.cos (ψ z / ε)) x :=
    (hF (ψ x)).differentiableAt.comp x hψd
  rw [harmonicGauge_smul ha hx hf]
  have hgc : gradientCovector (fun z => Real.cos (ψ z / ε)) x =
      (-(ε⁻¹ * Real.sin (ψ x / ε))) • gradientCovector ψ x := by
    funext i
    rw [gradientCovector_comp (F := fun u => Real.cos (u / ε)) (hF (ψ x)).differentiableAt hψd,
      (hF (ψ x)).deriv]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hr (c : ℝ) (w : Fin (d + 1) → ℝ) (m : Fin (d + 1)) :
      raiseCovector g (c • w) x m = c * raiseCovector g w x m := by
    unfold raiseCovector
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [hgc]
  simp only [hr, mul_assoc, ← Finset.mul_sum]

/-- **The transport term of an amplitude in the full harmonic gauge**: with `k^a ā_{ab} = 0` on
`U` and `div ā = 0` at `x`, `R₁ = −½ (2∇_k a + θ a)`. -/
theorem transportTerm_of_harmonic (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) (hB : ∀ k, harmonicGauge g a x k = 0)
    (j k : Fin (d + 1)) :
    transportTerm g ψ a x j k = -transportOperator g ψ a x j k / 2 := by
  rw [transportTerm_of_gauge hψ ha has hg hx, hB, hB]
  ring

/-- **The transport equation for the full amplitude** (target of §108): in the harmonic gauge
to the first two orders, the `ε⁻¹` coefficient of `δRic[a cos(ψ/ε)]` vanishes exactly when
`2∇_k a + (∇·k) a = 0`. -/
theorem transportTerm_eq_zero_iff (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (has : ∀ z ∈ U, ∀ i j, a z i j = a z j i)
    (hg : ∀ z ∈ U, IsShortWaveGauge g (gradientCovector ψ z) (a z) z)
    {x : MinkowskiModel d} (hx : x ∈ U) (hB : ∀ k, harmonicGauge g a x k = 0) :
    (∀ j k, transportTerm g ψ a x j k = 0) ↔ ∀ j k, transportOperator g ψ a x j k = 0 := by
  simp only [transportTerm_of_harmonic hψ ha has hg hx hB]
  constructor
  · intro h j k; linarith [h j k]
  · intro h j k; rw [h j k]; ring

end Gauge

/-! ### Instances -/

section Flat

/-- **Flat instance.** On the Minkowski background, a linear phase with a constant symmetric
amplitude has a vanishing transport term: the rays are straight, `θ = 0`, and the amplitude is
parallel. -/
theorem transportTerm_minkowski_const (κ : Fin (d + 1) → ℝ)
    {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (hA : ∀ i j, A i j = A j i)
    {x : MinkowskiModel d} (hx : x ∈ U) (j k : Fin (d + 1)) :
    transportTerm (minkowski σ d U) (fun y => ∑ i, κ i * y i) (fun _ => A) x j k = 0 := by
  have hψ : ContDiffOn ℝ ∞ (fun y : MinkowskiModel d => ∑ i, κ i * y i) U :=
    (ContDiff.sum fun i _ => contDiff_const.mul
      (contDiff_apply ℝ (fun _ : Fin (d + 1) => ℝ) i)).contDiffOn
  have hW (i l : Fin (d + 1)) :
      waveHessian (minkowski σ d U) (fun y => ∑ i, κ i * y i) x i l = 0 := by
    unfold waveHessian covDerivOne
    have hc : (fun z => gradientCovector (fun y : MinkowskiModel d => ∑ i, κ i * y i) z l) =
        fun _ => κ l := funext fun z => gradientCovector_linear κ z l
    simp [hc, minkowski_christoffelOf hx]
  have hC (m p q : Fin (d + 1)) : (minkowski σ d U).covDerivTwo (fun _ => A) x m p q = 0 := by
    simp [covDerivTwo, minkowski_christoffelOf hx]
  rw [transportTerm_eq (a := fun _ => A) hψ (fun _ _ => contDiffOn_const) (fun _ _ => hA) hx]
  simp [transportOperator, rayDerivative, rayExpansion, contractionDerivative, amplitudeDivergence,
    traceGradient, hW, hC]

end Flat

namespace PlaneWave

open ExactPlaneWave

variable {D : Data}

/-- The Christoffel symbols along the ray direction vanish: `k^l Γ^b_{lj} = 0` for
`k = (−1, 0, 0, −1)`. -/
theorem sum_rayDirection_christoffel (x : MinkowskiModel 3) (b j : Fin 4) :
    ∑ l, rayDirection l * christoffel D x b l j = 0 := by
  fin_cases b <;> fin_cases j <;> simp [Fin.sum_univ_four, rayDirection, christoffel]

/-- The Christoffel symbols contracted with `du = (1, 0, 0, −1)` vanish:
`Γ^b_{ij} ℓ_b = 0`. -/
theorem sum_christoffel_nullCovector (x : MinkowskiModel 3) (i j : Fin 4) :
    ∑ b, christoffel D x b i j * nullCovector b = 0 := by
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, nullCovector, christoffel]

/-- The rays of a plane wave are parallel: `∇_i ∂_j u = 0`. -/
theorem waveHessian_retarded {x : MinkowskiModel 3} (hx : x ∈ domain D) (i j : Fin 4) :
    waveHessian (metric D) retarded x i j = 0 := by
  unfold waveHessian covDerivOne
  have hc : (fun z => gradientCovector retarded z j) = fun _ => nullCovector j :=
    funext fun z => gradientCovector_retarded z j
  rw [hc]
  simp [christoffelOf_eq hx, gradientCovector_retarded, sum_christoffel_nullCovector]

theorem rayExpansion_retarded {x : MinkowskiModel 3} (hx : x ∈ domain D) :
    rayExpansion (metric D) retarded x = 0 := by
  simp [rayExpansion, waveHessian_retarded hx]

/-- The covariant derivative of the constant cross amplitude. -/
theorem covDerivTwo_cross {x : MinkowskiModel 3} (hx : x ∈ domain D) (m p q : Fin 4) :
    (metric D).covDerivTwo (fun _ => crossAmplitude) x m p q =
      -∑ b, (christoffel D x b m p * crossAmplitude b q +
        christoffel D x b m q * crossAmplitude p b) := by
  simp [covDerivTwo, christoffelOf_eq hx]

/-- **The cross amplitude is transported along the rays**: `∇_k a = 0`. -/
theorem rayDerivative_cross {x : MinkowskiModel 3} (hx : x ∈ domain D) (j k : Fin 4) :
    rayDerivative (metric D) retarded (fun _ => crossAmplitude) x j k = 0 := by
  unfold rayDerivative
  simp only [gradientField_retarded hx, covDerivTwo_cross hx]
  have h : ∑ l, rayDirection l * -∑ b, (christoffel D x b l j * crossAmplitude b k +
      christoffel D x b l k * crossAmplitude j b) =
      -∑ b, ((∑ l, rayDirection l * christoffel D x b l j) * crossAmplitude b k +
        (∑ l, rayDirection l * christoffel D x b l k) * crossAmplitude j b) := by
    simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => by ring
  rw [h]
  simp [sum_rayDirection_christoffel]

theorem transportOperator_cross {x : MinkowskiModel 3} (hx : x ∈ domain D) (j k : Fin 4) :
    transportOperator (metric D) retarded (fun _ => crossAmplitude) x j k = 0 := by
  simp [transportOperator, rayDerivative_cross hx, rayExpansion_retarded hx]

/-- **The cross amplitude satisfies the next-order gauge** `div ā = 0`. -/
theorem harmonicGauge_cross {x : MinkowskiModel 3} (hx : x ∈ domain D) (k : Fin 4) :
    harmonicGauge (metric D) (fun _ => crossAmplitude) x k = 0 := by
  unfold harmonicGauge amplitudeDivergence traceGradient
  simp only [covDerivTwo_cross hx, coefficient_inv_metric hx, Matrix.diagonal_apply, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  fin_cases k <;> simp [Fin.sum_univ_four, christoffel, crossAmplitude]

theorem contDiffOn_retarded_domain : ContDiffOn ℝ ∞ retarded (domain D) :=
  contDiff_retarded.contDiffOn

theorem crossAmplitude_symm (i j : Fin 4) : crossAmplitude i j = crossAmplitude j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem isShortWaveGauge_cross_retarded {z : MinkowskiModel 3} (hz : z ∈ domain D) :
    IsShortWaveGauge (metric D) (gradientCovector retarded z) crossAmplitude z := by
  have h : gradientCovector retarded z = nullCovector := funext (gradientCovector_retarded z)
  rw [h]
  exact isShortWaveGauge_cross hz

/-- The cross polarization `e^{12} = e^{21} = 1` is transverse and traceless for `du`. -/
theorem isTTPolarization_cross (z : MinkowskiModel 3) :
    IsTTPolarization (metric D) (gradientCovector retarded z) crossAmplitude z := by
  have h : gradientCovector retarded z = nullCovector := funext (gradientCovector_retarded z)
  rw [h]
  refine ⟨⟨crossAmplitude_symm, fun i => ?_⟩, ?_⟩
  · fin_cases i <;> simp [Fin.sum_univ_four, crossAmplitude, nullCovector]
  · simp [Fin.sum_univ_four, coefficient_metric, crossAmplitude]

/-- **The curved instance of the transport equation**: on every diagonal plane wave of §109 the
cross wave `a cos(u/ε)` has a vanishing transport term. -/
theorem transportTerm_cross {x : MinkowskiModel 3} (hx : x ∈ domain D) (j k : Fin 4) :
    transportTerm (metric D) retarded (fun _ => crossAmplitude) x j k = 0 := by
  have h := transportTerm_of_harmonic (g := metric D) (a := fun _ => crossAmplitude)
    contDiffOn_retarded_domain (fun _ _ => contDiffOn_const)
    (fun _ _ i j => crossAmplitude_symm i j) (fun z hz => isShortWaveGauge_cross_retarded hz) hx
    (harmonicGauge_cross hx) j k
  rw [h, transportOperator_cross hx]
  ring

/-- **The cross wave on a plane wave is exact to two orders**: for every `ε`,
`δRic[a cos(u/ε)] = cos(u/ε) δRic[a]`; the `ε⁻²` and `ε⁻¹` orders vanish. -/
theorem familyRicciDeriv_cross_shortWave {x : MinkowskiModel 3} (hx : x ∈ domain D) (ε : ℝ)
    (j k : Fin 4) :
    familyRicciDeriv ((metric D).perturbationFamily
        (fun z => Real.cos (retarded z / ε) • crossAmplitude)) x j k =
      Real.cos (retarded x / ε) *
        familyRicciDeriv ((metric D).perturbationFamily (fun _ => crossAmplitude)) x j k := by
  have h := familyRicciDeriv_shortWave (g := metric D) (a := fun _ => crossAmplitude)
    contDiffOn_retarded_domain (fun _ _ => contDiffOn_const)
    (fun _ _ i j => crossAmplitude_symm i j) hx ε j k
  have hg : gradientCovector retarded x = nullCovector := funext (gradientCovector_retarded x)
  rw [h, transportTerm_cross hx, hg, shortWaveSymbol_cross hx]
  ring

end PlaneWave

/-! ### The longitudinal terms in flat space -/

section Longitudinal

open ExactPlaneWave PlaneWave

/-- The amplitude `a(z) = z¹ e₊ₓ` of a cross wave whose strength varies across the rays. -/
def longitudinalAmplitude (z : MinkowskiModel 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  z 1 • crossAmplitude

theorem covDerivTwo_longitudinalAmplitude (z : MinkowskiModel 3) (m p q : Fin 4) :
    (minkowski .timeNegative 3 ⊤).covDerivTwo longitudinalAmplitude z m p q =
      (if m = 1 then 1 else 0) * crossAmplitude p q := by
  rw [covDerivTwo_minkowski (Set.mem_univ z)]
  have h : (fun y : MinkowskiModel 3 => longitudinalAmplitude y p q) =
      fun y => crossAmplitude p q * y 1 := by
    funext y
    simp only [longitudinalAmplitude, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [h, fderiv_const_mul (differentiableAt_apply (𝕜 := ℝ) (1 : Fin 4) z)]
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [(hasFDerivAt_apply (1 : Fin 4) z).fderiv]
  simp only [ContinuousLinearMap.proj_apply, Pi.single_apply]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · ring

theorem waveHessian_minkowski_retarded (z : MinkowskiModel 3) (i j : Fin 4) :
    waveHessian (minkowski .timeNegative 3 ⊤) retarded z i j = 0 := by
  unfold waveHessian covDerivOne
  have hc : (fun y => gradientCovector retarded y j) = fun _ => nullCovector j :=
    funext fun y => gradientCovector_retarded y j
  rw [hc]
  have hz : z ∈ (⊤ : Opens (MinkowskiModel 3)) := trivial
  simp [minkowski_christoffelOf hz]

theorem gradientField_minkowski_retarded (z : MinkowskiModel 3) :
    (minkowski .timeNegative 3 ⊤).gradientField retarded z = rayDirection := by
  have hc : (minkowski .timeNegative 3 ⊤).coefficient z =
      Minkowski.metricMatrix .timeNegative 3 := by
    rw [minkowski_coefficient]; rfl
  funext i
  simp only [gradientField, hc, metricMatrix_inv, gradientCovector_retarded, metricMatrix_apply,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  fin_cases i <;> simp [lorentzSign, nullCovector, rayDirection]

theorem isShortWaveGauge_longitudinal (z : MinkowskiModel 3) :
    IsShortWaveGauge (minkowski .timeNegative 3 ⊤) (gradientCovector retarded z)
      (longitudinalAmplitude z) z := by
  have hc : (minkowski .timeNegative 3 ⊤).coefficient z =
      Minkowski.metricMatrix .timeNegative 3 := by
    rw [minkowski_coefficient]; rfl
  rw [isShortWaveGauge_iff (Set.mem_univ z)]
  intro b
  have htr : amplitudeTrace (minkowski .timeNegative 3 ⊤) (longitudinalAmplitude z) z = 0 := by
    simp [amplitudeTrace, hc, metricMatrix_inv, metricMatrix_apply, Fin.sum_univ_four,
      longitudinalAmplitude, crossAmplitude]
  rw [htr]
  have hr : raiseCovector (minkowski .timeNegative 3 ⊤) (gradientCovector retarded z) z =
      rayDirection := by
    rw [← gradientField_minkowski_retarded z]
    rfl
  simp only [contractAmplitude, hr, mul_zero, zero_div]
  fin_cases b <;> simp [Fin.sum_univ_four, rayDirection, longitudinalAmplitude, crossAmplitude]

/-- **The longitudinal terms in flat space.** For the null phase `u = t − z` and the amplitude
`a = z¹ e₊ₓ`, which is in the gauge `k^a ā_{ab} = 0` and satisfies the transport equation
`2∇_k a + θ a = 0`, the next-order gauge fails, `(div ā)₂ = 1`, and the `ε⁻¹` coefficient of
`δRic[a cos(u/ε)]` is not zero: `R₁_{02} = ½ k₀ (div ā)₂ = ½`. It vanishes on the transverse
polarizations (`sum_transverse_transportTerm`). -/
theorem transportTerm_longitudinal (z : MinkowskiModel 3) :
    transportOperator (minkowski .timeNegative 3 ⊤) retarded longitudinalAmplitude z = 0 ∧
      harmonicGauge (minkowski .timeNegative 3 ⊤) longitudinalAmplitude z 2 = 1 ∧
      transportTerm (minkowski .timeNegative 3 ⊤) retarded longitudinalAmplitude z 0 2 = 1 / 2 := by
  have hc : ((minkowski .timeNegative 3 ⊤).coefficient z)⁻¹ =
      Minkowski.metricMatrix .timeNegative 3 := by
    rw [minkowski_coefficient]; exact metricMatrix_inv
  have hψ : ContDiffOn ℝ ∞ retarded (⊤ : Opens (MinkowskiModel 3)) := contDiff_retarded.contDiffOn
  have ha : ∀ i j, ContDiffOn ℝ ∞ (fun y => longitudinalAmplitude y i j)
      (⊤ : Opens (MinkowskiModel 3)) := fun i j => by
    have : (fun y : MinkowskiModel 3 => longitudinalAmplitude y i j) =
        fun y => y 1 * crossAmplitude i j := by
      funext y; simp [longitudinalAmplitude]
    rw [this]
    exact ((contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 1).mul contDiff_const).contDiffOn
  have has : ∀ y ∈ (⊤ : Opens (MinkowskiModel 3)), ∀ i j,
      longitudinalAmplitude y i j = longitudinalAmplitude y j i := fun y _ i j => by
    simp only [longitudinalAmplitude, Matrix.smul_apply, crossAmplitude_symm i j]
  have hOp : ∀ j k, transportOperator (minkowski .timeNegative 3 ⊤) retarded
      longitudinalAmplitude z j k = 0 := by
    intro j k
    simp only [transportOperator, rayDerivative, rayExpansion, waveHessian_minkowski_retarded,
      gradientField_minkowski_retarded, covDerivTwo_longitudinalAmplitude, mul_zero,
      Finset.sum_const_zero, zero_mul, add_zero]
    simp [rayDirection]
  have hB : harmonicGauge (minkowski .timeNegative 3 ⊤) longitudinalAmplitude z 2 = 1 := by
    simp only [harmonicGauge, amplitudeDivergence, traceGradient, hc,
      covDerivTwo_longitudinalAmplitude, metricMatrix_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp [lorentzSign, crossAmplitude]
  refine ⟨funext fun j => funext fun k => hOp j k, hB, ?_⟩
  have hB0 : harmonicGauge (minkowski .timeNegative 3 ⊤) longitudinalAmplitude z 0 = 0 := by
    simp only [harmonicGauge, amplitudeDivergence, traceGradient, hc,
      covDerivTwo_longitudinalAmplitude, metricMatrix_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp [lorentzSign, crossAmplitude]
  rw [transportTerm_of_gauge hψ ha has (fun y _ => isShortWaveGauge_longitudinal y)
    (Set.mem_univ z), hOp, hB, hB0, gradientCovector_retarded, gradientCovector_retarded]
  simp [nullCovector]

end Longitudinal

end ProjectAinos.GeneralRelativity.ShortWave
