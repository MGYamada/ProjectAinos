/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.SecondVariation
public import ProjectAinos.GeneralRelativity.ShortWaveTransport
public import ProjectAinos.SmoothGeometry.Wave.TransverseTraceless
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The effective energy-momentum of short gravitational waves

Landau–Lifshitz, §108 (Isaacson's effective stress). On a background coordinate metric `g` the
second variation of the Ricci tensor along `g + s h` is `secondRicci g h`
(`SmoothGeometry/Lorentzian/SecondVariation.lean`); the quadratic term of `Ric(g + s h)` is
`(s²/2) secondRicci g h`. For the short wave `h = a cos(ψ/ε)` with the Isaacson amplitude
`s = ε` this term is of order one.

* `secondRicci_phase`, `secondRicci_shortWave`: the exact expansion
  `½ secondRicci[a cos(ψ/ε)] = ε⁻² Φ(ψ/ε) − ε⁻¹ sin cos (ψ/ε) M₁ + cos²(ψ/ε) M₀`, with the
  `ε`-independent coefficients `M₁, M₀` and the **profile**
  `Φ(θ) = sin²θ Q·Q + cos 2θ Λ(k, g^{-1} a Q)` (`stressProfile`), `Q = Q(dψ, a)`;
  `tendsto_secondRicci_shortWave`: `(ε²/2) secondRicci[a cos(ψ/ε)] − Φ(ψ/ε) → 0`.
* **The average over a wavelength.** `phaseAverage Φ = (2π)⁻¹ ∫₀^{2π} Φ`; the averaged quadratic
  Ricci tensor `⟨R⁽²⁾⟩ = phaseAverage Φ` (`averagedSecondRicci`) is `½ Q·Q`
  (`averagedSecondRicci_eq`). In the gauge `k^a ā_{ab} = 0` with `k` null,
  `averagedSecondRicci_of_gauge`: `⟨R⁽²⁾⟩_{jk} = −⅛ (a_{cd} a^{cd} − ½ (tr a)²) k_j k_k`.
* **The effective stress.** `effectiveStress g ψ a κ`:
  `t_{jk} = (a_{cd} a^{cd} − ½ (tr a)²) k_j k_k / (8κ)`, in the units `G_{ik} = κ T_{ik}` of §110
  (`κ = 8π` for `G = 1`, which gives `1/64π`). `averagedSecondRicci_eq_effectiveStress`:
  `⟨R⁽²⁾⟩_{jk} = −κ (t_{jk} − ½ g_{jk} tr t)`, so `Ric(g) + ⟨R⁽²⁾⟩ = 0` is the Einstein equation
  with the source `t`. `effectiveStress_eq_average_gradient`: `t_{jk} = (1/4κ) ⟨∇_j h_{cd}
  ∇_k h^{cd} − ½ ∇_j h ∇_k h⟩` for `h = ε a cos(ψ/ε)`, by `tendsto_gradientSquare_shortWave` (the
  `(1/32π) ⟨∇h ∇h⟩` of Isaacson in the trace-free gauge).
* **Properties.** `effectiveStress_symm`, `effectiveStress_trace` (traceless for a null phase)
  and `effectiveStress_conserved`: `∇^j t_{jk} = 0` given the transport equation
  `2∇_k a + θ a = 0` at the point and a null phase on `U`.
* **The flux of §110.** `effectiveStress_flux`: for a plane wave in Minkowski space with
  `k = (1, −n)` and an amplitude `a = Ā − ½ η tr Ā` with `Ā` in harmonic gauge, the radial
  flux `t^{0α} n_α` is `ttSquare n S̄ / 8κ`, the phase average of the plane-wave flux
  `planeFlux n (−sin θ a) / κ` of the pseudotensor used for `gravitationalPower`
  (`effectiveStress_flux_eq_average`).
* **Instances.** On every diagonal plane wave of §109 the cross wave has
  `t_{jk} = ℓ_j ℓ_k / (4κ a² b²)` (`PlaneWave.effectiveStress_cross`), which is conserved
  (`PlaneWave.effectiveStress_cross_conserved`) and is the source of the averaged curvature
  (`PlaneWave.averagedSecondRicci_cross`); in Minkowski space the cross wave along `e_z` has the
  flux `1/4κ` (`effectiveStress_flux_cross`).

The averaging is the phase average of the order-one coefficient of the quadratic term with the
Isaacson scaling `s = ε`. The cubic and higher terms of `Ric(g + ε a cos(ψ/ε))` are not
estimated, and a weak limit against test functions is not stated.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace Real
open scoped ContDiff Topology Matrix

namespace ProjectAinos.GeneralRelativity.ShortWave

open SmoothGeometry CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

/-! ### The short-wave expansion of the second variation -/

section Definitions

variable (g : CoordinateMetric σ d U)

/-- The symbol `Q(dψ, a)` of the wave as a field of arrays. -/
def waveSymbol (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (z : MinkowskiModel d) :
    Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ :=
  g.symbolChristoffel (gradientCovector ψ z) (a z) z

/-- The leading quadratic term `Q·Q = Q^i_{ia} Q^a_{jk} − Q^i_{ja} Q^a_{ik}`. -/
def quadraticLeading (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  christoffelQuadratic (waveSymbol g ψ a x) (waveSymbol g ψ a x) j k

/-- The oscillating term `Λ(k, g^{-1} a Q)`, with the coefficient `cos 2θ`. -/
def oscillatingTerm (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  gradientContraction (gradientCovector ψ x) (g.raiseContract a (waveSymbol g ψ a) x) j k

/-- **The profile** `Φ(θ) = sin²θ Q·Q + cos 2θ Λ(k, g^{-1} a Q)` of the quadratic term at the
fast phase `θ = ψ/ε`. -/
def stressProfile (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (θ : ℝ) (j k : Fin (d + 1)) : ℝ :=
  Real.sin θ ^ 2 * quadraticLeading g ψ a x j k + Real.cos (2 * θ) * oscillatingTerm g ψ a x j k

/-- The coefficient of `sin cos (ψ/ε) ε⁻¹`:
`M₁ = δΓ[a]·Q + Q·δΓ[a] − 2Λ(k, g^{-1} a δΓ[a]) − ∇·(g^{-1} a Q)`. -/
def secondRicciFirst (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  christoffelQuadratic (g.curvedChristoffel a x) (waveSymbol g ψ a x) j k +
    christoffelQuadratic (waveSymbol g ψ a x) (g.curvedChristoffel a x) j k -
    2 * gradientContraction (gradientCovector ψ x)
      (g.raiseContract a (g.curvedChristoffel a) x) j k -
    g.palatini (g.raiseContract a (waveSymbol g ψ a)) x j k

/-- The coefficient of `cos² (ψ/ε)`: `M₀ = δΓ[a]·δΓ[a] − ∇·(g^{-1} a δΓ[a]) = ½ secondRicci a`. -/
def secondRicciZero (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  christoffelQuadratic (g.curvedChristoffel a x) (g.curvedChristoffel a x) j k -
    g.palatini (g.raiseContract a (g.curvedChristoffel a)) x j k

end Definitions

section Expansion

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

theorem christoffelQuadratic_add_smul {n : ℕ} (c c' : ℝ) (P P' : Fin n → Fin n → Fin n → ℝ)
    (j k : Fin n) :
    christoffelQuadratic (c • P + c' • P') (c • P + c' • P') j k =
      c ^ 2 * christoffelQuadratic P P j k +
        c * c' * (christoffelQuadratic P P' j k + christoffelQuadratic P' P j k) +
        c' ^ 2 * christoffelQuadratic P' P' j k := by
  unfold christoffelQuadratic
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring

theorem contDiffOn_waveSymbol (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) (b c e : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => waveSymbol g ψ a z b c e) U :=
  contDiffOn_symbolChristoffel hψ ha b c e

theorem contDiffOn_raiseContract (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U)
    {P : MinkowskiModel d → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ}
    (hP : ∀ b c e, ContDiffOn ℝ ∞ (fun z => P z b c e) U) (k i j : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun z => g.raiseContract a P z k i j) U := by
  unfold raiseContract
  exact ContDiffOn.sum fun l _ => (g.contDiffOn_coefficient_inv k l).mul
    (ContDiffOn.sum fun m _ => (ha l m).mul (hP m i j))

/-- **The second variation of a profile wave.** For a smooth profile `F`,
`½ secondRicci[F(ψ) a] = F² M₀ + F F' M₁ + F'² (Q·Q − Λ) − F F'' Λ` with `Λ = Λ(k, g^{-1} a Q)`,
all at `ψ(x)`, exactly. -/
theorem secondRicci_phase {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    g.secondRicci (fun z => F (ψ z) • a z) x j k / 2 =
      F (ψ x) ^ 2 * secondRicciZero g a x j k +
        F (ψ x) * deriv F (ψ x) * secondRicciFirst g ψ a x j k +
        deriv F (ψ x) ^ 2 * (quadraticLeading g ψ a x j k - oscillatingTerm g ψ a x j k) -
        F (ψ x) * deriv (deriv F) (ψ x) * oscillatingTerm g ψ a x j k := by
  have hU := U.isOpen.mem_nhds hx
  have hF1 : ContDiff ℝ ∞ (deriv F) := by simpa using hF.iterate_deriv 1
  have hF2 : ContDiff ℝ ∞ (deriv (deriv F)) := by simpa using hF.iterate_deriv 2
  have hFd (u : ℝ) : DifferentiableAt ℝ F u := hF.differentiable (by simp) u
  have hF1d (u : ℝ) : DifferentiableAt ℝ (deriv F) u := hF1.differentiable (by simp) u
  have hψd {z : MinkowskiModel d} (hz : z ∈ U) : DifferentiableAt ℝ ψ z :=
    differentiableAt_of_contDiffOn hψ hz
  have had {z : MinkowskiModel d} (hz : z ∈ U) (p q : Fin (d + 1)) :
      DifferentiableAt ℝ (fun y => a y p q) z := differentiableAt_of_contDiffOn (ha p q) hz
  set Q := waveSymbol g ψ a
  set P₁ := g.raiseContract a (g.curvedChristoffel a)
  set P₂ := g.raiseContract a Q
  -- the linearized Christoffel symbols of `F(ψ) a`
  have hΓ (z : MinkowskiModel d) (hz : z ∈ U) :
      g.curvedChristoffel (fun z => F (ψ z) • a z) z =
        F (ψ z) • g.curvedChristoffel a z + deriv F (ψ z) • Q z := by
    funext b c e
    rw [curvedChristoffel_smul (f := fun z => F (ψ z)) ((hFd _).comp z (hψd hz)) (had hz) b c e]
    have hgc : gradientCovector (fun z => F (ψ z)) z = deriv F (ψ z) • gradientCovector ψ z :=
      funext fun i => gradientCovector_comp (hFd _) (hψd hz) i
    rw [hgc, symbolChristoffel_smul]
    rfl
  -- the raised contraction
  have hR : g.raiseContract (fun z => F (ψ z) • a z)
      (g.curvedChristoffel (fun z => F (ψ z) • a z)) =ᶠ[𝓝 x]
      fun z => (F (ψ z) ^ 2) • P₁ z + (F (ψ z) * deriv F (ψ z)) • P₂ z := by
    filter_upwards [hU] with z hz
    funext b c e
    unfold raiseContract at *
    rw [hΓ z hz]
    simp only [P₁, P₂, raiseContract, Pi.add_apply, Pi.smul_apply, Matrix.smul_apply,
      smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring
  have hP₁ (b c e : Fin (d + 1)) : DifferentiableAt ℝ (fun z => P₁ z b c e) x :=
    differentiableAt_of_contDiffOn (contDiffOn_raiseContract ha
      (fun b c e => contDiffOn_curvedChristoffel ha b c e) b c e) hx
  have hP₂ (b c e : Fin (d + 1)) : DifferentiableAt ℝ (fun z => P₂ z b c e) x :=
    differentiableAt_of_contDiffOn (contDiffOn_raiseContract ha
      (fun b c e => contDiffOn_waveSymbol hψ ha b c e) b c e) hx
  have hφ₁ : DifferentiableAt ℝ (fun z => F (ψ z) ^ 2) x :=
    ((hFd _).comp x (hψd hx)).pow 2
  have hφ₂ : DifferentiableAt ℝ (fun z => F (ψ z) * deriv F (ψ z)) x :=
    ((hFd _).comp x (hψd hx)).mul ((hF1d _).comp x (hψd hx))
  have hP₂' (b c e : Fin (d + 1)) :
      DifferentiableAt ℝ (fun z => ((F (ψ z) * deriv F (ψ z)) • P₂ z) b c e) x :=
    hφ₂.mul (hP₂ b c e)
  -- the derivatives of the two coefficients
  have hd₁ (i : Fin (d + 1)) : gradientCovector (fun z => F (ψ z) ^ 2) x i =
      2 * F (ψ x) * deriv F (ψ x) * gradientCovector ψ x i := by
    have hD : HasDerivAt (fun u => F u ^ 2) (2 * F (ψ x) * deriv F (ψ x)) (ψ x) := by
      have := (hFd (ψ x)).hasDerivAt.fun_pow 2
      convert this using 1
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    rw [gradientCovector_comp (F := fun u => F u ^ 2) hD.differentiableAt (hψd hx), hD.deriv]
  have hd₂ (i : Fin (d + 1)) : gradientCovector (fun z => F (ψ z) * deriv F (ψ z)) x i =
      (deriv F (ψ x) ^ 2 + F (ψ x) * deriv (deriv F) (ψ x)) * gradientCovector ψ x i := by
    have hD : HasDerivAt (fun u => F u * deriv F u)
        (deriv F (ψ x) ^ 2 + F (ψ x) * deriv (deriv F) (ψ x)) (ψ x) := by
      have := (hFd (ψ x)).hasDerivAt.mul (hF1d (ψ x)).hasDerivAt
      convert this using 1
      ring
    rw [gradientCovector_comp (F := fun u => F u * deriv F u) hD.differentiableAt (hψd hx),
      hD.deriv]
  have hpal : g.palatini (g.raiseContract (fun z => F (ψ z) • a z)
      (g.curvedChristoffel (fun z => F (ψ z) • a z))) x j k =
      F (ψ x) ^ 2 * g.palatini P₁ x j k +
        2 * F (ψ x) * deriv F (ψ x) * gradientContraction (gradientCovector ψ x) (P₁ x) j k +
        (F (ψ x) * deriv F (ψ x) * g.palatini P₂ x j k +
          (deriv F (ψ x) ^ 2 + F (ψ x) * deriv (deriv F) (ψ x)) *
            gradientContraction (gradientCovector ψ x) (P₂ x) j k) := by
    rw [palatini_congr hR, palatini_smul_add (f := fun z => F (ψ z) ^ 2) hφ₁ hP₁ hP₂',
      palatini_smul (f := fun z => F (ψ z) * deriv F (ψ z)) hφ₂ hP₂]
    simp only [hd₁, hd₂]
    unfold gradientContraction
    simp only [Finset.mul_sum]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    · congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
  have hquad : christoffelQuadratic (g.curvedChristoffel (fun z => F (ψ z) • a z) x)
      (g.curvedChristoffel (fun z => F (ψ z) • a z) x) j k =
      F (ψ x) ^ 2 * christoffelQuadratic (g.curvedChristoffel a x) (g.curvedChristoffel a x) j k +
        F (ψ x) * deriv F (ψ x) * (christoffelQuadratic (g.curvedChristoffel a x) (Q x) j k +
          christoffelQuadratic (Q x) (g.curvedChristoffel a x) j k) +
        deriv F (ψ x) ^ 2 * christoffelQuadratic (Q x) (Q x) j k := by
    rw [hΓ x hx, christoffelQuadratic_add_smul]
  unfold secondRicci
  rw [hpal, hquad]
  unfold secondRicciZero secondRicciFirst quadraticLeading oscillatingTerm
  ring

/-- **The second variation of the short wave** `a cos(ψ/ε)`, exactly, for every `ε`:
`½ secondRicci[a cos(ψ/ε)] = ε⁻² Φ(ψ/ε) − ε⁻¹ sin(ψ/ε) cos(ψ/ε) M₁ + cos²(ψ/ε) M₀`. -/
theorem secondRicci_shortWave (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (ε : ℝ) (j k : Fin (d + 1)) :
    g.secondRicci (fun z => Real.cos (ψ z / ε) • a z) x j k / 2 =
      ε⁻¹ ^ 2 * stressProfile g ψ a x (ψ x / ε) j k -
        ε⁻¹ * (Real.sin (ψ x / ε) * Real.cos (ψ x / ε)) * secondRicciFirst g ψ a x j k +
        Real.cos (ψ x / ε) ^ 2 * secondRicciZero g a x j k := by
  have hF : ContDiff ℝ ∞ (fun u => Real.cos (u / ε)) :=
    Real.contDiff_cos.comp (contDiff_id.div_const ε)
  have hd1 (u : ℝ) : HasDerivAt (fun u => Real.cos (u / ε)) (-(Real.sin (u / ε) * ε⁻¹)) u := by
    have h := ((hasDerivAt_id u).div_const ε).cos
    simpa [div_eq_mul_inv] using h
  have hd1' : deriv (fun u => Real.cos (u / ε)) = fun u => -(Real.sin (u / ε) * ε⁻¹) :=
    funext fun u => (hd1 u).deriv
  have hd2 (u : ℝ) : HasDerivAt (fun u => -(Real.sin (u / ε) * ε⁻¹))
      (-(Real.cos (u / ε) * ε⁻¹ * ε⁻¹)) u := by
    have h := (((hasDerivAt_id u).div_const ε).sin.mul_const ε⁻¹).fun_neg
    simpa [div_eq_mul_inv] using h
  have hd2' : deriv (deriv (fun u => Real.cos (u / ε))) =
      fun u => -(Real.cos (u / ε) * ε⁻¹ * ε⁻¹) := by
    rw [hd1']
    exact funext fun u => (hd2 u).deriv
  rw [secondRicci_phase hF hψ ha hx, hd2', hd1']
  unfold stressProfile
  rw [Real.cos_two_mul]
  have hsc := Real.cos_sq_add_sin_sq (ψ x / ε)
  linear_combination (-ε⁻¹ ^ 2 * oscillatingTerm g ψ a x j k) * hsc

/-- **The quadratic term with the Isaacson amplitude.** With `s = ε`, the quadratic term
`(s²/2) secondRicci[a cos(ψ/ε)]` of `Ric(g + s a cos(ψ/ε))` is the profile at the fast phase up
to `O(ε)`: `(ε²/2) secondRicci[a cos(ψ/ε)] − Φ(ψ/ε) → 0` as `ε → 0`. -/
theorem tendsto_secondRicci_shortWave (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    Tendsto (fun ε : ℝ => ε ^ 2 * (g.secondRicci (fun z => Real.cos (ψ z / ε) • a z) x j k / 2) -
      stressProfile g ψ a x (ψ x / ε) j k) (𝓝[≠] 0) (𝓝 0) := by
  set M₁ := secondRicciFirst g ψ a x j k
  set M₀ := secondRicciZero g a x j k
  have hexp (ε : ℝ) (hε : ε ≠ 0) :
      ε ^ 2 * (g.secondRicci (fun z => Real.cos (ψ z / ε) • a z) x j k / 2) -
        stressProfile g ψ a x (ψ x / ε) j k =
      -(ε * (Real.sin (ψ x / ε) * Real.cos (ψ x / ε)) * M₁) +
        ε ^ 2 * (Real.cos (ψ x / ε) ^ 2 * M₀) := by
    rw [secondRicci_shortWave hψ ha hx ε j k]
    field_simp
    ring
  refine squeeze_zero_norm' (a := fun ε : ℝ => |ε| * |M₁| + ε ^ 2 * |M₀|) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hexp ε hε, Real.norm_eq_abs]
    have hs := Real.abs_sin_le_one (ψ x / ε)
    have hc := Real.abs_cos_le_one (ψ x / ε)
    have h1 : |ε * (Real.sin (ψ x / ε) * Real.cos (ψ x / ε)) * M₁| ≤ |ε| * |M₁| := by
      rw [abs_mul, abs_mul, abs_mul]
      have hsc : |Real.sin (ψ x / ε)| * |Real.cos (ψ x / ε)| ≤ 1 := by
        nlinarith [abs_nonneg (Real.sin (ψ x / ε)), abs_nonneg (Real.cos (ψ x / ε))]
      nlinarith [abs_nonneg ε, abs_nonneg M₁, mul_nonneg (abs_nonneg ε) (abs_nonneg M₁),
        mul_nonneg (abs_nonneg (Real.sin (ψ x / ε))) (abs_nonneg (Real.cos (ψ x / ε)))]
    have h2 : |ε ^ 2 * (Real.cos (ψ x / ε) ^ 2 * M₀)| ≤ ε ^ 2 * |M₀| := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, sq_abs]
      have hc2 : |Real.cos (ψ x / ε)| ^ 2 ≤ 1 := by
        nlinarith [abs_nonneg (Real.cos (ψ x / ε))]
      nlinarith [sq_nonneg ε, abs_nonneg M₀, mul_nonneg (sq_nonneg ε) (abs_nonneg M₀),
        sq_nonneg (Real.cos (ψ x / ε))]
    calc |-(ε * (Real.sin (ψ x / ε) * Real.cos (ψ x / ε)) * M₁) +
          ε ^ 2 * (Real.cos (ψ x / ε) ^ 2 * M₀)|
        ≤ |-(ε * (Real.sin (ψ x / ε) * Real.cos (ψ x / ε)) * M₁)| +
            |ε ^ 2 * (Real.cos (ψ x / ε) ^ 2 * M₀)| := abs_add_le _ _
      _ ≤ |ε| * |M₁| + ε ^ 2 * |M₀| := by rw [abs_neg]; linarith
  · have hc : Continuous fun ε : ℝ => |ε| * |M₁| + ε ^ 2 * |M₀| := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

end Expansion

/-! ### The average over a wavelength -/

/-- **The phase average** `(2π)⁻¹ ∫₀^{2π} Φ(θ) dθ` of a function of the fast phase. -/
def phaseAverage (Φ : ℝ → ℝ) : ℝ := (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, Φ θ

theorem integral_sin_sq_two_pi : ∫ θ in (0 : ℝ)..2 * π, Real.sin θ ^ 2 = π := by
  rw [integral_sin_sq]
  simp

theorem integral_cos_two_mul_two_pi : ∫ θ in (0 : ℝ)..2 * π, Real.cos (2 * θ) = 0 := by
  have h : (fun θ : ℝ => Real.cos (2 * θ)) = fun θ => 1 - 2 * Real.sin θ ^ 2 := by
    funext θ
    rw [Real.cos_two_mul, ← Real.cos_sq_add_sin_sq θ]
    ring
  have hc : Continuous fun θ : ℝ => 2 * Real.sin θ ^ 2 := by fun_prop
  rw [h, intervalIntegral.integral_sub (f := fun _ => (1 : ℝ))
    (g := fun θ => 2 * Real.sin θ ^ 2) intervalIntegrable_const (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_sin_sq_two_pi]
  simp

/-- The phase average of `sin²θ X + cos 2θ Y` is `X/2`. -/
theorem phaseAverage_sin_sq_add_cos (X Y : ℝ) :
    phaseAverage (fun θ => Real.sin θ ^ 2 * X + Real.cos (2 * θ) * Y) = X / 2 := by
  unfold phaseAverage
  have h1 : Continuous fun θ : ℝ => Real.sin θ ^ 2 * X := by fun_prop
  have h2 : Continuous fun θ : ℝ => Real.cos (2 * θ) * Y := by fun_prop
  rw [intervalIntegral.integral_add (f := fun θ => Real.sin θ ^ 2 * X)
    (g := fun θ => Real.cos (2 * θ) * Y) (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    integral_sin_sq_two_pi, integral_cos_two_mul_two_pi]
  field_simp
  ring

section Average

variable (g : CoordinateMetric σ d U)

/-- **The averaged quadratic Ricci tensor** `⟨R⁽²⁾⟩_{jk}`: the phase average of the profile, the
order-one part of `(ε²/2) secondRicci[a cos(ψ/ε)]` averaged over a wavelength. -/
def averagedSecondRicci (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  phaseAverage fun θ => stressProfile g ψ a x θ j k

/-- **The effective stress of the waves** (Isaacson):
`t_{jk} = (a_{cd} a^{cd} − ½ (tr a)²) k_j k_k / (8κ)` with `k = dψ`, in the units
`G_{ik} = κ T_{ik}`. -/
def effectiveStress (ψ : MinkowskiModel d → ℝ)
    (a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (κ : ℝ) (x : MinkowskiModel d)
    (j k : Fin (d + 1)) : ℝ :=
  (tensorPairing g (a x) (a x) x - amplitudeTrace g (a x) x ^ 2 / 2) * gradientCovector ψ x j *
    gradientCovector ψ x k / (8 * κ)

end Average

section AverageLemmas

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

/-- **The averaged quadratic Ricci tensor is `½ Q·Q`**: the oscillating term averages out. -/
theorem averagedSecondRicci_eq (x : MinkowskiModel d) (j k : Fin (d + 1)) :
    averagedSecondRicci g ψ a x j k = quadraticLeading g ψ a x j k / 2 := by
  unfold averagedSecondRicci stressProfile
  exact phaseAverage_sin_sq_add_cos _ _

end AverageLemmas

/-! ### The algebra of the leading term in the gauge -/

section Algebra

/-- **The leading quadratic term of a null wave in the gauge.** For a symmetric inverse metric
`G`, a symmetric amplitude `A` and a covector `κ` with `K = Gκ`, `Σ K^m A_{mb} = ½ τ κ_b`
(the gauge, `τ = G^{lm} A_{lm}`) and `κ·K = 0` (null), the symbol
`Q^i_{jb} = ½ G^{il} (κ_j A_{bl} + κ_b A_{lj} − κ_l A_{jb})` has
`Q^i_{ia} Q^a_{jk} − Q^i_{ja} Q^a_{ik} = −¼ (A·A − ½ τ²) κ_j κ_k`. -/
theorem christoffelQuadratic_symbol_of_gauge {n : ℕ} {G A : Matrix (Fin n) (Fin n) ℝ}
    {κ : Fin n → ℝ} (hG : ∀ p q, G p q = G q p) (hA : ∀ p q, A p q = A q p)
    (hgauge : ∀ b, ∑ m, (∑ l, G m l * κ l) * A m b =
      κ b * (∑ l, ∑ m, G l m * A l m) / 2)
    (hnull : ∑ m, (∑ l, G m l * κ l) * κ m = 0) (j k : Fin n) :
    christoffelQuadratic (fun i j b => ∑ l, G i l * (κ j * A b l + κ b * A l j - κ l * A j b) / 2)
      (fun i j b => ∑ l, G i l * (κ j * A b l + κ b * A l j - κ l * A j b) / 2) j k =
      -((∑ c, ∑ e, G c e * ∑ p, ∑ q, G p q * (A c p * A e q)) -
        (∑ l, ∑ m, G l m * A l m) ^ 2 / 2) * κ j * κ k / 4 := by
  set τ := ∑ l, ∑ m, G l m * A l m
  set K : Fin n → ℝ := fun m => ∑ l, G m l * κ l
  set B : Fin n → Fin n → ℝ := fun i b => ∑ l, G i l * A b l
  set P2 := ∑ c, ∑ e, G c e * ∑ p, ∑ q, G p q * (A c p * A e q)
  set q : Fin n → Fin n → Fin n → ℝ := fun i j b => (κ j * B i b + κ b * B i j - K i * A j b) / 2
  have hQ : (fun i j b => ∑ l, G i l * (κ j * A b l + κ b * A l j - κ l * A j b) / 2) = q := by
    funext i j b
    simp only [q, B, K, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun l _ => by rw [hA l j]; ring
  have g1 (b : Fin n) : ∑ m, K m * A m b = κ b * τ / 2 := hgauge b
  have n1 : ∑ m, K m * κ m = 0 := hnull
  have n2 : ∑ m, κ m * K m = 0 := by rw [← n1]; exact Finset.sum_congr rfl fun m _ => by ring
  have a1 (b : Fin n) : ∑ i, κ i * B i b = κ b * τ / 2 := by
    rw [← g1 b]
    simp only [B, K, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by
      rw [hG i l, hA b l]; ring
  have a2 (i : Fin n) : ∑ b, B i b * K b = K i * τ / 2 := by
    simp only [B, Finset.sum_mul]
    rw [Finset.sum_comm]
    have h (l : Fin n) : ∑ b, G i l * A b l * K b = G i l * (κ l * τ / 2) := by
      rw [← g1 l, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    simp only [h, K, Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun l _ => by ring
  have a4 : ∑ i, B i i = τ := rfl
  have a5 : ∑ i, ∑ b, B i b * B b i = P2 := by
    simp only [B, P2, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun l _ => Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
      Finset.sum_congr rfl fun i _ => ?_
    rw [hG i m, hA i l]
    ring
  have hqa (b : Fin n) : ∑ i, q i i b = κ b * τ / 2 := by
    simp only [q]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, a1, ← Finset.mul_sum,
      a4, g1]
    ring
  have hprod (i b : Fin n) : q i j b * q b i k =
      (κ j * (κ i * B i b * B b k) + κ j * κ k * (B i b * B b i) - κ j * (B i b * K b * A i k) +
        (κ i * B i j) * (κ b * B b k) + κ k * (B i j * (κ b * B b i)) -
        (κ b * K b) * (B i j * A i k) - (K i * κ i) * (A j b * B b k) -
        κ k * (A j b * (B b i * K i)) + (K b * A j b) * (K i * A i k)) / 4 := by
    simp only [q]
    ring
  have hq1 (b : Fin n) : q b j k = (κ j * B b k + κ k * B b j - K b * A j k) / 2 := rfl
  clear_value q
  clear_value B K τ P2
  -- the first part
  have part1 : ∑ i, ∑ b, q i i b * q b j k = τ ^ 2 * κ j * κ k / 4 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hqa, hq1]
    have e : ∑ b, κ b * τ / 2 * ((κ j * B b k + κ k * B b j - K b * A j k) / 2) =
        τ / 4 * (κ j * ∑ b, κ b * B b k + κ k * ∑ b, κ b * B b j - (∑ b, κ b * K b) * A j k) := by
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e, a1, a1, n2]
    ring
  -- the second part, term by term
  have S1 : ∑ i, ∑ b, κ j * (κ i * B i b * B b k) = κ j * κ k * τ ^ 2 / 4 := by
    rw [Finset.sum_comm]
    have h (b : Fin n) : ∑ i, κ j * (κ i * B i b * B b k) = κ j * (κ b * τ / 2) * B b k := by
      rw [← a1 b, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [h]
    have e : ∑ b, κ j * (κ b * τ / 2) * B b k = κ j * τ / 2 * ∑ b, κ b * B b k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e, a1]
    ring
  have S2 : ∑ i, ∑ b, κ j * κ k * (B i b * B b i) = κ j * κ k * P2 := by
    rw [← a5, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  have S3 : ∑ i, ∑ b, κ j * (B i b * K b * A i k) = κ j * κ k * τ ^ 2 / 4 := by
    have h (i : Fin n) : ∑ b, κ j * (B i b * K b * A i k) = κ j * (K i * τ / 2) * A i k := by
      rw [← a2 i, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    simp only [h]
    have e : ∑ i, κ j * (K i * τ / 2) * A i k = κ j * τ / 2 * ∑ i, K i * A i k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, g1]
    ring
  have S4 : ∑ i, ∑ b, (κ i * B i j) * (κ b * B b k) = κ j * κ k * τ ^ 2 / 4 := by
    rw [← Finset.sum_mul_sum, a1, a1]
    ring
  have S5 : ∑ i, ∑ b, κ k * (B i j * (κ b * B b i)) = κ j * κ k * τ ^ 2 / 4 := by
    have h (i : Fin n) : ∑ b, κ k * (B i j * (κ b * B b i)) = κ k * B i j * (κ i * τ / 2) := by
      rw [← a1 i, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    simp only [h]
    have e : ∑ i, κ k * B i j * (κ i * τ / 2) = κ k * τ / 2 * ∑ i, κ i * B i j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, a1]
    ring
  have S6 : ∑ i, ∑ b, (κ b * K b) * (B i j * A i k) = 0 := by
    rw [Finset.sum_comm, ← Finset.sum_mul_sum, n2, zero_mul]
  have S7 : ∑ i, ∑ b, (K i * κ i) * (A j b * B b k) = 0 := by
    rw [← Finset.sum_mul_sum, n1, zero_mul]
  have S8 : ∑ i, ∑ b, κ k * (A j b * (B b i * K i)) = κ j * κ k * τ ^ 2 / 4 := by
    rw [Finset.sum_comm]
    have h (b : Fin n) : ∑ i, κ k * (A j b * (B b i * K i)) = κ k * A j b * (K b * τ / 2) := by
      rw [← a2 b, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [h]
    have e : ∑ b, κ k * A j b * (K b * τ / 2) = κ k * τ / 2 * ∑ b, K b * A b j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [hA j b]; ring
    rw [e, g1]
    ring
  have S9 : ∑ i, ∑ b, (K b * A j b) * (K i * A i k) = κ j * κ k * τ ^ 2 / 4 := by
    rw [Finset.sum_comm, ← Finset.sum_mul_sum]
    have e : ∑ b, K b * A j b = κ j * τ / 2 := by
      rw [← g1 j]
      exact Finset.sum_congr rfl fun b _ => by rw [hA j b]
    rw [e, g1]
    ring
  have part2 : ∑ i, ∑ b, q i j b * q b i k = κ j * κ k * (P2 + τ ^ 2 / 2) / 4 := by
    simp only [hprod, ← Finset.sum_div]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [S1, S2, S3, S4, S5, S6, S7, S8, S9]
    ring
  rw [hQ]
  unfold christoffelQuadratic
  simp only [Finset.sum_sub_distrib]
  rw [part1, part2]
  ring

end Algebra

/-! ### The effective stress -/

section Stress

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

/-- **The leading quadratic term of a null wave in the gauge**:
`Q·Q = −¼ (a_{cd} a^{cd} − ½ (tr a)²) k_j k_k`. -/
theorem quadraticLeading_of_gauge {x : MinkowskiModel d} (hx : x ∈ U)
    (has : ∀ i j, a x i j = a x j i) (hg : IsShortWaveGauge g (gradientCovector ψ x) (a x) x)
    (hnull : g.gradientNorm ψ x = 0) (j k : Fin (d + 1)) :
    quadraticLeading g ψ a x j k =
      -(tensorPairing g (a x) (a x) x - amplitudeTrace g (a x) x ^ 2 / 2) *
        gradientCovector ψ x j * gradientCovector ψ x k / 4 := by
  have hgauge := (isShortWaveGauge_iff hx _ _).mp hg
  have hn : ∑ m, (∑ l, (g.coefficient x)⁻¹ m l * gradientCovector ψ x l) *
      gradientCovector ψ x m = 0 := by
    rw [← hnull]
    unfold gradientNorm
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
  exact christoffelQuadratic_symbol_of_gauge (G := (g.coefficient x)⁻¹) (A := a x)
    (fun p q => g.coefficient_inv_symmetric hx p q) has hgauge hn j k

/-- **The averaged quadratic Ricci tensor of a null wave in the gauge**:
`⟨R⁽²⁾⟩_{jk} = −⅛ (a_{cd} a^{cd} − ½ (tr a)²) k_j k_k`. -/
theorem averagedSecondRicci_of_gauge {x : MinkowskiModel d} (hx : x ∈ U)
    (has : ∀ i j, a x i j = a x j i) (hg : IsShortWaveGauge g (gradientCovector ψ x) (a x) x)
    (hnull : g.gradientNorm ψ x = 0) (j k : Fin (d + 1)) :
    averagedSecondRicci g ψ a x j k =
      -(tensorPairing g (a x) (a x) x - amplitudeTrace g (a x) x ^ 2 / 2) *
        gradientCovector ψ x j * gradientCovector ψ x k / 8 := by
  rw [averagedSecondRicci_eq, quadraticLeading_of_gauge hx has hg hnull]
  ring

theorem effectiveStress_symm (κ : ℝ) (x : MinkowskiModel d) (j k : Fin (d + 1)) :
    effectiveStress g ψ a κ x j k = effectiveStress g ψ a κ x k j := by
  unfold effectiveStress
  ring

/-- **The effective stress is traceless** for a null phase: `g^{jk} t_{jk} = 0`. -/
theorem effectiveStress_trace (κ : ℝ) {x : MinkowskiModel d} (hnull : g.gradientNorm ψ x = 0) :
    ∑ j, ∑ k, (g.coefficient x)⁻¹ j k * effectiveStress g ψ a κ x j k = 0 := by
  unfold effectiveStress
  have e : ∑ j, ∑ k, (g.coefficient x)⁻¹ j k *
      ((tensorPairing g (a x) (a x) x - amplitudeTrace g (a x) x ^ 2 / 2) *
        gradientCovector ψ x j * gradientCovector ψ x k / (8 * κ)) =
      (tensorPairing g (a x) (a x) x - amplitudeTrace g (a x) x ^ 2 / 2) / (8 * κ) *
        g.gradientNorm ψ x := by
    unfold gradientNorm
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e, hnull, mul_zero]

/-- **The effective stress is the source of the averaged curvature**:
`⟨R⁽²⁾⟩_{jk} = −κ (t_{jk} − ½ g_{jk} g^{ab} t_{ab})`, so the averaged order-one equation
`Ric(g) + ⟨R⁽²⁾⟩ = 0` is the Einstein equation `Ric(g) = κ (t − ½ g tr t)` with the source `t`. -/
theorem averagedSecondRicci_eq_effectiveStress {κ : ℝ} (hκ : κ ≠ 0) {x : MinkowskiModel d}
    (hx : x ∈ U) (has : ∀ i j, a x i j = a x j i)
    (hg : IsShortWaveGauge g (gradientCovector ψ x) (a x) x) (hnull : g.gradientNorm ψ x = 0)
    (j k : Fin (d + 1)) :
    averagedSecondRicci g ψ a x j k = -κ * (effectiveStress g ψ a κ x j k -
      g.coefficient x j k * (∑ p, ∑ q, (g.coefficient x)⁻¹ p q *
        effectiveStress g ψ a κ x p q) / 2) := by
  rw [effectiveStress_trace κ hnull, averagedSecondRicci_of_gauge hx has hg hnull]
  unfold effectiveStress
  field_simp
  ring

end Stress

/-! ### Conservation -/

section Conservation

variable {g : CoordinateMetric σ d U} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

/-- The full contraction with the second matrix raised. -/
theorem tensorPairing_eq_raise (M B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) :
    tensorPairing g M B x = ∑ c, ∑ p, M c p *
      ∑ e, ∑ q, (g.coefficient x)⁻¹ c e * ((g.coefficient x)⁻¹ p q * B e q) := by
  unfold tensorPairing
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun q _ => by ring

theorem tensorPairing_symm {x : MinkowskiModel d} (hx : x ∈ U)
    (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    tensorPairing g A B x = tensorPairing g B A x := by
  have hG (p q : Fin (d + 1)) : (g.coefficient x)⁻¹ p q = (g.coefficient x)⁻¹ q p :=
    g.coefficient_inv_symmetric hx p q
  unfold tensorPairing
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hG c e]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by rw [hG p q]; ring

/-- The full contraction is linear in the first matrix. -/
theorem tensorPairing_sum_left (c : Fin (d + 1) → ℝ)
    (C : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) :
    tensorPairing g (Matrix.of fun p q => ∑ l, c l * C l p q) B x =
      ∑ l, c l * tensorPairing g (C l) B x := by
  simp only [tensorPairing_eq_raise, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun e _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun p _ =>
    Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun c' _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c' _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun e _ =>
      Finset.sum_congr rfl fun q _ => by ring

theorem tensorPairing_smul_left (c : ℝ) (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : tensorPairing g (c • A) B x = c * tensorPairing g A B x := by
  unfold tensorPairing
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- The transverse derivative of a null phase: `k^l ∇_l k_k = ½ ∂_k g(dψ, dψ) = 0`. -/
theorem sum_gradientField_waveHessian (hψ : ContDiffOn ℝ ∞ ψ U)
    (hnull : ∀ z ∈ U, g.gradientNorm ψ z = 0) {x : MinkowskiModel d} (hx : x ∈ U)
    (k : Fin (d + 1)) : ∑ l, g.gradientField ψ x l * waveHessian g ψ x l k = 0 := by
  have h := gradientCovector_gradientNorm (g := g) hψ hx k
  have h0 : gradientCovector (g.gradientNorm ψ) x k = 0 := by
    have hz : g.gradientNorm ψ =ᶠ[𝓝 x] fun _ => 0 :=
      Filter.eventually_of_mem (U.isOpen.mem_nhds hx) hnull
    simp [gradientCovector, hz.fderiv_eq]
  rw [h0] at h
  have e : ∑ l, g.gradientField ψ x l * waveHessian g ψ x l k =
      ∑ a, g.gradientField ψ x a * g.covDerivOne (gradientCovector ψ) x k a :=
    Finset.sum_congr rfl fun l _ => by rw [waveHessian_symm hψ hx l k]; rfl
  rw [e]
  linarith

/-- **The effective stress is conserved to leading order** (target of §108): for a null phase
on `U` and an amplitude that satisfies the transport equation `2∇_k a + θ a = 0` at `x`,
`∇^j t_{jk} = g^{jl} ∇_l t_{jk} = 0`. -/
theorem effectiveStress_conserved (κ : ℝ) (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U)
    (hnull : ∀ z ∈ U, g.gradientNorm ψ z = 0) {x : MinkowskiModel d} (hx : x ∈ U)
    (htr : ∀ j k, transportOperator g ψ a x j k = 0) (k : Fin (d + 1)) :
    ∑ j, ∑ l, (g.coefficient x)⁻¹ j l *
      g.covDerivTwo (fun z => Matrix.of fun j k => effectiveStress g ψ a κ z j k) x l j k = 0 := by
  have hkd (i : Fin (d + 1)) : DifferentiableAt ℝ (fun z => gradientCovector ψ z i) x :=
    differentiableAt_of_contDiffOn (contDiffOn_gradientCovector hψ i) hx
  have had (p q : Fin (d + 1)) : DifferentiableAt ℝ (fun z => a z p q) x :=
    differentiableAt_of_contDiffOn (ha p q) hx
  set P : MinkowskiModel d → ℝ := fun z => tensorPairing g (a z) (a z) z with hPdef
  set T : MinkowskiModel d → ℝ := fun z => amplitudeTrace g (a z) z with hTdef
  have hPd : DifferentiableAt ℝ P x := by
    show DifferentiableAt ℝ (fun z => ∑ c, ∑ e, (g.coefficient z)⁻¹ c e *
      ∑ p, ∑ q, (g.coefficient z)⁻¹ p q * (a z c p * a z e q)) x
    exact DifferentiableAt.fun_sum fun c _ => DifferentiableAt.fun_sum fun e _ =>
      (differentiableAt_coefficient_inv hx c e).fun_mul (DifferentiableAt.fun_sum fun p _ =>
        DifferentiableAt.fun_sum fun q _ => (differentiableAt_coefficient_inv hx p q).fun_mul
          ((had c p).fun_mul (had e q)))
  have hTd : DifferentiableAt ℝ T x := differentiableAt_amplitudeTrace ha hx
  set f : MinkowskiModel d → ℝ := fun z => (8 * κ)⁻¹ * P z - (16 * κ)⁻¹ * (T z * T z)
    with hfdef
  have hfun : (fun z => Matrix.of fun j k => effectiveStress g ψ a κ z j k) = fun z =>
      f z • (Matrix.of fun j k => gradientCovector ψ z j * gradientCovector ψ z k :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) := by
    funext z
    ext j k
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, effectiveStress, f, P, T]
    ring
  have hTT : DifferentiableAt ℝ (fun z => T z * T z) x := hTd.fun_mul hTd
  have hfd : DifferentiableAt ℝ f x := (hPd.const_mul _).fun_sub (hTT.const_mul _)
  have hdf (l : Fin (d + 1)) : gradientCovector f x l = (8 * κ)⁻¹ * gradientCovector P x l -
      (16 * κ)⁻¹ * (2 * T x * gradientCovector T x l) := by
    unfold gradientCovector
    rw [hfdef, fderiv_fun_sub (hPd.const_mul _) (hTT.const_mul _), fderiv_const_mul hPd,
      fderiv_const_mul hTT, fderiv_fun_mul hTd hTd]
    simp only [_root_.sub_apply, _root_.smul_apply, _root_.add_apply, smul_eq_mul]
    ring
  rw [hfun]
  simp only [covDerivTwo_smul (a := fun z => (Matrix.of fun j k => gradientCovector ψ z j *
    gradientCovector ψ z k : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)) hfd
    (fun p q => (hkd p).fun_mul (hkd q)), covDerivTwo_mul hkd hkd, Matrix.of_apply]
  set G := (g.coefficient x)⁻¹
  set κv := gradientCovector ψ x
  set K := g.gradientField ψ x
  set H := g.covDerivOne (gradientCovector ψ) x
  set θ := rayExpansion g ψ x
  set R := rayDerivative g ψ a x
  have hG (p q : Fin (d + 1)) : G p q = G q p := g.coefficient_inv_symmetric hx p q
  have hH (p q : Fin (d + 1)) : H p q = H q p := waveHessian_symm hψ hx p q
  have hK (l : Fin (d + 1)) : K l = ∑ j, G l j * κv j := rfl
  have hR (p q : Fin (d + 1)) : R p q = -(θ / 2) * a x p q := by
    have := htr p q
    unfold transportOperator at this
    linarith
  -- the derivative of the pairing and of the trace along the rays
  have hdP (l : Fin (d + 1)) : gradientCovector P x l =
      2 * tensorPairing g (g.covDerivMatrix a x l) (a x) x := by
    unfold gradientCovector
    rw [fderiv_tensorPairing hx had had l, tensorPairing_symm hx (a x)]
    ring
  have hdT (l : Fin (d + 1)) : gradientCovector T x l = traceGradient g a x l :=
    gradientCovector_amplitudeTrace ha hx l
  have hKP : ∑ l, K l * gradientCovector P x l = -(θ * P x) := by
    simp only [hdP]
    have e : ∑ l, K l * (2 * tensorPairing g (g.covDerivMatrix a x l) (a x) x) =
        2 * tensorPairing g (Matrix.of fun p q => ∑ l, K l * g.covDerivMatrix a x l p q)
          (a x) x := by
      rw [tensorPairing_sum_left, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hM : (Matrix.of fun p q => ∑ l, K l * g.covDerivMatrix a x l p q) = (-(θ / 2)) • a x := by
      ext p q
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, covDerivMatrix]
      exact hR p q
    rw [e, hM, tensorPairing_smul_left]
    simp only [P]
    ring
  have hKT : ∑ l, K l * gradientCovector T x l = -(θ / 2) * T x := by
    simp only [hdT]
    have e1 : ∑ l, K l * traceGradient g a x l = ∑ i, ∑ m, G i m * R i m := by
      unfold traceGradient
      simp only [R, rayDerivative, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
    rw [e1]
    simp only [hR, T, amplitudeTrace, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
  have hKf : ∑ l, K l * gradientCovector f x l = -(θ * f x) := by
    simp only [hdf, mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ l, K l * ((8 * κ)⁻¹ * gradientCovector P x l) =
        (8 * κ)⁻¹ * ∑ l, K l * gradientCovector P x l := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    have e2 : ∑ l, K l * ((16 * κ)⁻¹ * (2 * T x * gradientCovector T x l)) =
        (16 * κ)⁻¹ * (2 * T x) * ∑ l, K l * gradientCovector T x l := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [e1, e2, hKP, hKT]
    simp only [f]
    ring
  -- the three contractions
  have p1 : ∑ j, ∑ l, G j l * (gradientCovector f x l * (κv j * κv k)) =
      κv k * ∑ l, K l * gradientCovector f x l := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hK, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hG j l]; ring
  have p2 : ∑ j, ∑ l, G j l * (f x * (H l j * κv k)) = f x * κv k * θ := by
    simp only [θ, rayExpansion, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by
      rw [hH l j]
      show G j l * (f x * (H j l * κv k)) = f x * κv k * (G j l * H j l)
      ring
  have p3 : ∑ j, ∑ l, G j l * (f x * (κv j * H l k)) = f x * ∑ l, K l * H l k := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hK, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hG j l]; ring
  have hKH : ∑ l, K l * H l k = 0 := sum_gradientField_waveHessian hψ hnull hx k
  simp only [mul_add, Finset.sum_add_distrib]
  rw [p1, p2, p3, hKf, hKH]
  ring

end Conservation

/-! ### The flux of a plane wave in Minkowski space -/

section Flux

theorem coefficient_inv_minkowski (z : MinkowskiModel d) :
    ((minkowski σ d U).coefficient z)⁻¹ = Minkowski.metricMatrix σ d := by
  have hc : (minkowski σ d U).coefficient z = Minkowski.metricMatrix σ d := by
    rw [minkowski_coefficient]; rfl
  rw [hc, metricMatrix_inv]

/-- The full contraction in Minkowski space: `A·B = Σ η^{cc} η^{pp} A_{cp} B_{cp}`. -/
theorem tensorPairing_minkowski (A B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (z : MinkowskiModel d) :
    tensorPairing (minkowski σ d U) A B z =
      ∑ c, ∑ p, lorentzSign σ c * lorentzSign σ p * (A c p * B c p) := by
  unfold tensorPairing
  simp only [coefficient_inv_minkowski, metricMatrix_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun p _ => by ring

/-- The trace in Minkowski space is the flat trace. -/
theorem amplitudeTrace_minkowski (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (z : MinkowskiModel d) :
    amplitudeTrace (minkowski σ d U) A z = flatTrace σ A := by
  unfold amplitudeTrace flatTrace
  simp only [coefficient_inv_minkowski, metricMatrix_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem lorentzSign_timeNegative_zero : lorentzSign (d := 3) .timeNegative 0 = -1 := by
  simp [lorentzSign]

theorem lorentzSign_timeNegative_succ (α : Fin 3) :
    lorentzSign (d := 3) .timeNegative α.succ = 1 := by
  simp [lorentzSign]

theorem flatTrace_timeNegative (A : Matrix (Fin 4) (Fin 4) ℝ) :
    flatTrace .timeNegative A = -A 0 0 + A 1 1 + A 2 2 + A 3 3 := by
  simp only [flatTrace, Fin.sum_univ_succ, Fin.sum_univ_zero, lorentzSign, Fin.succ_ne_zero,
    ite_true, ite_false]
  simp
  ring

/-- **The invariant of a plane wave in harmonic gauge**: for `a = Ā − ½ η tr Ā` with `Ā`
symmetric and `Ā₀ᵦ = −Σ_α n_α Ā_{αb}`, `a_{cd} a^{cd} − ½ (tr a)² = ttSquare n S̄`. -/
theorem pairing_traceReverse_of_gauge {n : EuclideanSpace ℝ (Fin 3)}
    {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ a b, A a b = A b a)
    (hg : ∀ b, A 0 b = -∑ α : Fin 3, n α * A α.succ b) :
    (∑ c : Fin 4, ∑ p : Fin 4, lorentzSign .timeNegative c * lorentzSign .timeNegative p *
        (traceReverse .timeNegative A c p * traceReverse .timeNegative A c p)) -
      flatTrace .timeNegative (traceReverse .timeNegative A) ^ 2 / 2 =
      Wave.ttSquare n (fun i j => A i.succ j.succ) := by
  have s0 := lorentzSign_timeNegative_zero
  have s1 := lorentzSign_timeNegative_succ 0
  have s2 := lorentzSign_timeNegative_succ 1
  have s3 := lorentzSign_timeNegative_succ 2
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at s1 s2
  have s3' : lorentzSign (d := 3) .timeNegative 3 = 1 := s3
  have h0 := hg 0
  have h1 := hg 1
  have h2 := hg 2
  have h3 := hg 3
  have h10 := hA 1 0
  have h20 := hA 2 0
  have h30 := hA 3 0
  have h21 := hA 2 1
  have h31 := hA 3 1
  have h32 := hA 3 2
  simp only [Fin.sum_univ_three, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.isValue,
    Fin.reduceSucc, h10, h20, h30, h21, h31, h32] at h0 h1 h2 h3
  rw [h1, h2, h3] at h0
  simp only [Wave.ttSquare, traceReverse_apply, flatTrace_timeNegative, Fin.sum_univ_four,
    Fin.sum_univ_three, metricMatrix_apply, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.reduceSucc, Fin.reduceEq, ite_true, ite_false, s0, s1, s2, s3', h10, h20, h30, h21, h31,
    h32]
  rw [h0, h1, h2, h3]
  ring

/-- The effective stress of a plane wave with constant amplitude in Minkowski space. -/
theorem effectiveStress_minkowski_linear (κv : Fin (d + 1) → ℝ)
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (κ : ℝ) (z : MinkowskiModel d)
    (j k : Fin (d + 1)) :
    effectiveStress (minkowski σ d U) (fun y => ∑ i, κv i * y i) (fun _ => A) κ z j k =
      ((∑ c, ∑ p, lorentzSign σ c * lorentzSign σ p * (A c p * A c p)) -
        flatTrace σ A ^ 2 / 2) * κv j * κv k / (8 * κ) := by
  unfold effectiveStress
  rw [tensorPairing_minkowski, amplitudeTrace_minkowski, gradientCovector_linear,
    gradientCovector_linear]

/-- **The energy flux of the effective stress** of a plane wave in Minkowski space: for
`k = (1, −n)`, `‖n‖ = 1`, and `a = Ā − ½ η tr Ā` with `Ā` symmetric in harmonic gauge, the
radial flux `t^{0α} n_α = −Σ_α t_{0α} n_α` is `ttSquare n S̄ / 8κ`. -/
theorem effectiveStress_flux {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1)
    {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ a b, A a b = A b a)
    (hg : ∀ b, A 0 b = -∑ α : Fin 3, n α * A α.succ b) (κ : ℝ) (z : MinkowskiModel 3) :
    -∑ α : Fin 3, effectiveStress (minkowski .timeNegative 3 ⊤)
        (fun y => ∑ i, Wave.waveCovector n i * y i) (fun _ => traceReverse .timeNegative A) κ z
        0 α.succ * n α =
      Wave.ttSquare n (fun i j => A i.succ j.succ) / (8 * κ) := by
  simp only [effectiveStress_minkowski_linear]
  rw [← pairing_traceReverse_of_gauge hA hg]
  have hn' := Wave.sum_sq_eq_one hn
  have k0 : Wave.waveCovector n 0 = 1 := rfl
  have k1 : Wave.waveCovector n (0 : Fin 3).succ = -n 0 := rfl
  have k2 : Wave.waveCovector n (1 : Fin 3).succ = -n 1 := rfl
  have k3 : Wave.waveCovector n (2 : Fin 3).succ = -n 2 := rfl
  simp only [Fin.sum_univ_three, k0, k1, k2, k3]
  set X := (∑ c : Fin 4, ∑ p : Fin 4, lorentzSign .timeNegative c * lorentzSign .timeNegative p *
        (traceReverse .timeNegative A c p * traceReverse .timeNegative A c p)) -
      flatTrace .timeNegative (traceReverse .timeNegative A) ^ 2 / 2
  have e : -(X * 1 * -n 0 / (8 * κ) * n 0 + X * 1 * -n 1 / (8 * κ) * n 1 +
      X * 1 * -n 2 / (8 * κ) * n 2) = X * (n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2) / (8 * κ) := by ring
  rw [e, hn', mul_one]

/-- The plane-wave flux of §110 for the amplitude `c Ā` is `c²` times that of `Ā`. -/
theorem planeFlux_traceReverse_smul {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1)
    {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ a b, A a b = A b a)
    (hg : ∀ b, A 0 b = -∑ α : Fin 3, n α * A α.succ b) (c : ℝ) :
    Wave.planeFlux n (traceReverse .timeNegative (c • A)) =
      c ^ 2 * Wave.ttSquare n (fun i j => A i.succ j.succ) / 4 := by
  have hA' : ∀ a b, (c • A) a b = (c • A) b a := fun a b => by
    simp only [Matrix.smul_apply, smul_eq_mul, hA a b]
  have hg' : ∀ b, (c • A) 0 b = -∑ α : Fin 3, n α * (c • A) α.succ b := fun b => by
    simp only [Matrix.smul_apply, smul_eq_mul, hg b, Finset.mul_sum, mul_neg]
    congr 1
    exact Finset.sum_congr rfl fun α _ => by ring
  rw [Wave.planeFlux_traceReverse hn hA' hg']
  have e : (fun i j : Fin 3 => (c • A) i.succ j.succ) = fun i j => c * A i.succ j.succ := by
    funext i j; simp only [Matrix.smul_apply, smul_eq_mul]
  rw [e, Wave.ttSquare_mul]

/-- **The flux normalization against §110**: the energy flux of the effective stress of a plane
wave `h = ε a cos(ψ/ε)` in Minkowski space, whose derivative is `∂_c h = −sin(ψ/ε) k_c a + O(ε)`,
is the phase average of the plane-wave flux `planeFlux n (−sin θ a) / κ` of the quadratic
pseudotensor (the integrand of `gravitationalPower`). -/
theorem effectiveStress_flux_eq_average {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1)
    {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : ∀ a b, A a b = A b a)
    (hg : ∀ b, A 0 b = -∑ α : Fin 3, n α * A α.succ b) (κ : ℝ) (z : MinkowskiModel 3) :
    -∑ α : Fin 3, effectiveStress (minkowski .timeNegative 3 ⊤)
        (fun y => ∑ i, Wave.waveCovector n i * y i) (fun _ => traceReverse .timeNegative A) κ z
        0 α.succ * n α =
      phaseAverage fun θ =>
        Wave.planeFlux n (traceReverse .timeNegative ((-Real.sin θ) • A)) / κ := by
  rw [effectiveStress_flux hn hA hg]
  have e : (fun θ => Wave.planeFlux n (traceReverse .timeNegative ((-Real.sin θ) • A)) / κ) =
      fun θ => Real.sin θ ^ 2 * (Wave.ttSquare n (fun i j => A i.succ j.succ) / (4 * κ)) +
        Real.cos (2 * θ) * 0 := by
    funext θ
    rw [planeFlux_traceReverse_smul hn hA hg]
    ring
  rw [e, phaseAverage_sin_sq_add_cos]
  ring

end Flux

/-! ### The gradient form of the effective stress -/

section Gradient

variable (g : CoordinateMetric σ d U)

/-- The quadratic form `∇_j h_{cd} ∇_k h^{cd} − ½ ∇_j h ∇_k h` of a field of matrices. -/
def gradientSquare (h : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) (j k : Fin (d + 1)) : ℝ :=
  tensorPairing g (g.covDerivMatrix h x j) (g.covDerivMatrix h x k) x -
    traceGradient g h x j * traceGradient g h x k / 2

variable {g} {ψ : MinkowskiModel d → ℝ}
  {a : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

theorem tensorPairing_add_smul (c₁ c₂ c₃ c₄ : ℝ)
    (A₁ A₂ B₁ B₂ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (x : MinkowskiModel d) :
    tensorPairing g (c₁ • A₁ + c₂ • A₂) (c₃ • B₁ + c₄ • B₂) x =
      c₁ * c₃ * tensorPairing g A₁ B₁ x + c₁ * c₄ * tensorPairing g A₁ B₂ x +
        c₂ * c₃ * tensorPairing g A₂ B₁ x + c₂ * c₄ * tensorPairing g A₂ B₂ x := by
  unfold tensorPairing
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- The covariant derivative of `h = ε a cos(ψ/ε)`:
`∇_j h = −sin(ψ/ε) k_j a + ε cos(ψ/ε) ∇_j a`, exactly, for `ε ≠ 0`. -/
theorem covDerivMatrix_shortWave (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    {ε : ℝ} (hε : ε ≠ 0) (j : Fin (d + 1)) :
    g.covDerivMatrix (fun z => (ε * Real.cos (ψ z / ε)) • a z) x j =
      (-(Real.sin (ψ x / ε) * gradientCovector ψ x j)) • a x +
        (ε * Real.cos (ψ x / ε)) • g.covDerivMatrix a x j := by
  have hψd : DifferentiableAt ℝ ψ x := differentiableAt_of_contDiffOn hψ hx
  have hF (u : ℝ) : HasDerivAt (fun u => ε * Real.cos (u / ε)) (-Real.sin (u / ε)) u := by
    have h := (((hasDerivAt_id' u).div_const ε).cos).const_mul ε
    have e : ε * (-Real.sin (u / ε) * (1 / ε)) = -Real.sin (u / ε) := by field_simp
    rw [e] at h
    exact h
  have hf : DifferentiableAt ℝ (fun z => ε * Real.cos (ψ z / ε)) x :=
    (hF (ψ x)).differentiableAt.comp x hψd
  have hgc : gradientCovector (fun z => ε * Real.cos (ψ z / ε)) x j =
      -(Real.sin (ψ x / ε) * gradientCovector ψ x j) := by
    rw [gradientCovector_comp (F := fun u => ε * Real.cos (u / ε)) (hF (ψ x)).differentiableAt
      hψd, (hF (ψ x)).deriv]
    ring
  ext p q
  simp only [covDerivMatrix, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [covDerivTwo_smul hf (fun p q => differentiableAt_of_contDiffOn (ha p q) hx), hgc]

/-- **The leading term of `∇h ∇h`**: for `h = ε a cos(ψ/ε)`,
`∇_j h_{cd} ∇_k h^{cd} − ½ ∇_j h ∇_k h − sin²(ψ/ε) (a·a − ½ (tr a)²) k_j k_k → 0` as `ε → 0`. -/
theorem tendsto_gradientSquare_shortWave (hψ : ContDiffOn ℝ ∞ ψ U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) U) {x : MinkowskiModel d} (hx : x ∈ U)
    (j k : Fin (d + 1)) :
    Tendsto (fun ε : ℝ => gradientSquare g (fun z => (ε * Real.cos (ψ z / ε)) • a z) x j k -
      Real.sin (ψ x / ε) ^ 2 * ((tensorPairing g (a x) (a x) x -
        amplitudeTrace g (a x) x ^ 2 / 2) * gradientCovector ψ x j * gradientCovector ψ x k))
      (𝓝[≠] 0) (𝓝 0) := by
  set A := a x
  set κj := gradientCovector ψ x j
  set κk := gradientCovector ψ x k
  set Cj := g.covDerivMatrix a x j
  set Ck := g.covDerivMatrix a x k
  set τ := amplitudeTrace g A x
  -- the trace of a covariant derivative
  have htr (C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (c₁ c₂ : ℝ) :
      ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * (c₁ • A + c₂ • C) i l =
        c₁ * τ + c₂ * ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * C i l := by
    simp only [τ, amplitudeTrace, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have htg (ε : ℝ) (hε : ε ≠ 0) (m : Fin (d + 1)) :
      traceGradient g (fun z => (ε * Real.cos (ψ z / ε)) • a z) x m =
        -(Real.sin (ψ x / ε) * gradientCovector ψ x m) * τ +
          ε * Real.cos (ψ x / ε) * traceGradient g a x m := by
    have h := congrArg (fun M => ∑ i, ∑ l, (g.coefficient x)⁻¹ i l * M i l)
      (covDerivMatrix_shortWave (g := g) hψ ha hx hε m)
    simp only [covDerivMatrix, Matrix.of_apply] at h
    unfold traceGradient
    rw [h, htr]
    rfl
  set P₁ := tensorPairing g A Ck x + tensorPairing g Cj A x
  set P₂ := tensorPairing g Cj Ck x
  set T₁ := κj * traceGradient g a x k + κk * traceGradient g a x j
  set T₂ := traceGradient g a x j * traceGradient g a x k
  have hexp (ε : ℝ) (hε : ε ≠ 0) :
      gradientSquare g (fun z => (ε * Real.cos (ψ z / ε)) • a z) x j k -
        Real.sin (ψ x / ε) ^ 2 * ((tensorPairing g A A x - τ ^ 2 / 2) * κj * κk) =
      ε * (-(Real.sin (ψ x / ε) * Real.cos (ψ x / ε)) * (κj * tensorPairing g A Ck x +
          κk * tensorPairing g Cj A x - τ * T₁ / 2)) +
        ε ^ 2 * (Real.cos (ψ x / ε) ^ 2 * (P₂ - T₂ / 2)) := by
    unfold gradientSquare
    rw [covDerivMatrix_shortWave hψ ha hx hε, covDerivMatrix_shortWave hψ ha hx hε,
      tensorPairing_add_smul, htg ε hε, htg ε hε]
    simp only [T₁, T₂, P₂]
    ring
  set M₁ := κj * tensorPairing g A Ck x + κk * tensorPairing g Cj A x - τ * T₁ / 2
  set M₀ := P₂ - T₂ / 2
  refine squeeze_zero_norm' (a := fun ε : ℝ => |ε| * |M₁| + ε ^ 2 * |M₀|) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hexp ε hε, Real.norm_eq_abs]
    have hs := Real.abs_sin_le_one (ψ x / ε)
    have hc := Real.abs_cos_le_one (ψ x / ε)
    have h1 : |ε * (-(Real.sin (ψ x / ε) * Real.cos (ψ x / ε)) * M₁)| ≤ |ε| * |M₁| := by
      rw [abs_mul, abs_mul, abs_neg, abs_mul]
      have hsc : |Real.sin (ψ x / ε)| * |Real.cos (ψ x / ε)| ≤ 1 := by
        nlinarith [abs_nonneg (Real.sin (ψ x / ε)), abs_nonneg (Real.cos (ψ x / ε))]
      nlinarith [abs_nonneg ε, abs_nonneg M₁, mul_nonneg (abs_nonneg ε) (abs_nonneg M₁),
        mul_nonneg (abs_nonneg (Real.sin (ψ x / ε))) (abs_nonneg (Real.cos (ψ x / ε)))]
    have h2 : |ε ^ 2 * (Real.cos (ψ x / ε) ^ 2 * M₀)| ≤ ε ^ 2 * |M₀| := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, sq_abs]
      have hc2 : |Real.cos (ψ x / ε)| ^ 2 ≤ 1 := by
        nlinarith [abs_nonneg (Real.cos (ψ x / ε))]
      nlinarith [sq_nonneg ε, abs_nonneg M₀, mul_nonneg (sq_nonneg ε) (abs_nonneg M₀),
        sq_nonneg (Real.cos (ψ x / ε))]
    calc |ε * (-(Real.sin (ψ x / ε) * Real.cos (ψ x / ε)) * M₁) +
          ε ^ 2 * (Real.cos (ψ x / ε) ^ 2 * M₀)|
        ≤ |ε * (-(Real.sin (ψ x / ε) * Real.cos (ψ x / ε)) * M₁)| +
            |ε ^ 2 * (Real.cos (ψ x / ε) ^ 2 * M₀)| := abs_add_le _ _
      _ ≤ |ε| * |M₁| + ε ^ 2 * |M₀| := by linarith
  · have hc : Continuous fun ε : ℝ => |ε| * |M₁| + ε ^ 2 * |M₀| := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- **The gradient form of the effective stress** (Isaacson): `t_{jk}` is `1/4κ` times the phase
average of the leading term `sin²θ (a·a − ½ (tr a)²) k_j k_k` of
`∇_j h_{cd} ∇_k h^{cd} − ½ ∇_j h ∇_k h` for `h = ε a cos(ψ/ε)` (`tendsto_gradientSquare_shortWave`);
with `κ = 8π` this is `(1/32π) ⟨∇_j h_{cd} ∇_k h^{cd} − ½ ∇_j h ∇_k h⟩`. -/
theorem effectiveStress_eq_average_gradient (κ : ℝ) (x : MinkowskiModel d) (j k : Fin (d + 1)) :
    effectiveStress g ψ a κ x j k = phaseAverage (fun θ => Real.sin θ ^ 2 *
      ((tensorPairing g (a x) (a x) x - amplitudeTrace g (a x) x ^ 2 / 2) *
        gradientCovector ψ x j * gradientCovector ψ x k)) / (4 * κ) := by
  have e : (fun θ => Real.sin θ ^ 2 *
      ((tensorPairing g (a x) (a x) x - amplitudeTrace g (a x) x ^ 2 / 2) *
        gradientCovector ψ x j * gradientCovector ψ x k)) = fun θ => Real.sin θ ^ 2 *
      ((tensorPairing g (a x) (a x) x - amplitudeTrace g (a x) x ^ 2 / 2) *
        gradientCovector ψ x j * gradientCovector ψ x k) + Real.cos (2 * θ) * 0 := by
    funext θ; ring
  rw [e, phaseAverage_sin_sq_add_cos]
  unfold effectiveStress
  by_cases hκ : κ = 0
  · simp [hκ]
  · field_simp
    ring

end Gradient

/-! ### Instances -/

namespace PlaneWave

open ExactPlaneWave

variable {D : Data}

/-- **The effective stress of the cross wave on a plane wave** of §109:
`t_{jk} = ℓ_j ℓ_k / (4κ a² b²)` with `ℓ = du`, from `a_{cd} a^{cd} = 2/(a² b²)` and `tr a = 0`. -/
theorem effectiveStress_cross {x : MinkowskiModel 3} (hx : x ∈ domain D) (κ : ℝ) (j k : Fin 4) :
    effectiveStress (metric D) retarded (fun _ => crossAmplitude) κ x j k =
      nullCovector j * nullCovector k /
        (4 * κ * D.a (retarded x) ^ 2 * D.b (retarded x) ^ 2) := by
  have ha := (a_pos_of_mem hx).ne'
  have hb := (b_pos_of_mem hx).ne'
  have hP : tensorPairing (metric D) crossAmplitude crossAmplitude x =
      2 / (D.a (retarded x) ^ 2 * D.b (retarded x) ^ 2) := by
    simp only [tensorPairing, coefficient_inv_metric hx, Matrix.diagonal_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp [Fin.sum_univ_four, crossAmplitude, coefficients]
    field_simp
    ring
  have hT : amplitudeTrace (metric D) crossAmplitude x = 0 := by
    simp [amplitudeTrace, coefficient_inv_metric hx, Matrix.diagonal_apply, Fin.sum_univ_four,
      crossAmplitude]
  have hg : gradientCovector retarded x = nullCovector := funext (gradientCovector_retarded x)
  unfold effectiveStress
  rw [hP, hT, hg]
  by_cases hκ : κ = 0
  · simp [hκ]
  · field_simp
    ring

/-- **Conservation on a curved background**: the effective stress of the cross wave is conserved
on every diagonal plane wave of §109 (the rays are null and the amplitude is transported). -/
theorem effectiveStress_cross_conserved (κ : ℝ) {x : MinkowskiModel 3} (hx : x ∈ domain D)
    (k : Fin 4) :
    ∑ j, ∑ l, ((metric D).coefficient x)⁻¹ j l * (metric D).covDerivTwo
      (fun z => Matrix.of fun j k => effectiveStress (metric D) retarded
        (fun _ => crossAmplitude) κ z j k) x l j k = 0 :=
  effectiveStress_conserved (g := metric D) (ψ := retarded) (a := fun _ => crossAmplitude) κ
    contDiffOn_retarded_domain (fun _ _ => contDiffOn_const)
    (fun _ hz => gradientNorm_retarded hz) hx (transportOperator_cross hx) k

/-- **The source of the averaged curvature on a plane wave**: for the cross wave,
`⟨R⁽²⁾⟩_{jk} = −κ (t_{jk} − ½ g_{jk} tr t)`. -/
theorem averagedSecondRicci_cross {κ : ℝ} (hκ : κ ≠ 0) {x : MinkowskiModel 3}
    (hx : x ∈ domain D) (j k : Fin 4) :
    averagedSecondRicci (metric D) retarded (fun _ => crossAmplitude) x j k =
      -κ * (effectiveStress (metric D) retarded (fun _ => crossAmplitude) κ x j k -
        (metric D).coefficient x j k * (∑ p, ∑ q, ((metric D).coefficient x)⁻¹ p q *
          effectiveStress (metric D) retarded (fun _ => crossAmplitude) κ x p q) / 2) :=
  averagedSecondRicci_eq_effectiveStress (g := metric D) (ψ := retarded)
    (a := fun _ => crossAmplitude) hκ hx (fun i j => crossAmplitude_symm i j)
    (isShortWaveGauge_cross_retarded hx) (gradientNorm_retarded hx) j k

end PlaneWave

/-- The unit vector `e_z` of the direction of propagation. -/
def unitZ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 2 1

/-- **The flux of the cross wave in Minkowski space**: for the wave going out along `e_z` with
the cross polarization, `t^{0α} n_α = 1/(4κ)`, half the instantaneous peak flux
`planeFlux e_z a / κ = 1/(2κ)` of §110. -/
theorem effectiveStress_flux_cross (κ : ℝ) (z : MinkowskiModel 3) :
    -∑ α : Fin 3, effectiveStress (minkowski .timeNegative 3 ⊤)
        (fun y => ∑ i, Wave.waveCovector unitZ i * y i)
        (fun _ => traceReverse .timeNegative PlaneWave.crossAmplitude) κ z 0 α.succ * unitZ α =
      1 / (4 * κ) := by
  have hn : ‖unitZ‖ = 1 := by simp [unitZ]
  have hg : ∀ b, PlaneWave.crossAmplitude 0 b =
      -∑ α : Fin 3, unitZ α * PlaneWave.crossAmplitude α.succ b := by
    intro b
    fin_cases b <;> simp [unitZ, PlaneWave.crossAmplitude]
  rw [effectiveStress_flux hn (fun a b => PlaneWave.crossAmplitude_symm a b) hg]
  have h2 : Wave.ttSquare unitZ (fun i j => PlaneWave.crossAmplitude i.succ j.succ) = 2 := by
    simp [Wave.ttSquare, Fin.sum_univ_three, unitZ, PlaneWave.crossAmplitude]
    norm_num
  rw [h2]
  ring

end ProjectAinos.GeneralRelativity.ShortWave
