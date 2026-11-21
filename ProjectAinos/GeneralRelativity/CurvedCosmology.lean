/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.CurvedSpatialHarmonic
public import ProjectAinos.GeneralRelativity.CurvedDustGrowth
public import ProjectAinos.GeneralRelativity.CurvedDustModes
public import ProjectAinos.SpecialFunctions.HyperbolicRadial
public import ProjectAinos.SpecialFunctions.ClassicalPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! # Closed and open dust perturbations from the spatial harmonics

Each solid angular harmonic gives a metric potential, a density contrast and a
covelocity perturbation on the closed or open Einstein dust solution. Both time
solutions extend through the turnaround of the closed universe.
-/

@[expose] public section
noncomputable section
open Set Filter Polynomial Complex
open scoped Real ContDiff Topology
namespace ProjectAinos.GeneralRelativity.CurvedPerturbation
open SmoothGeometry CoordinateMetric FLRW IsotropicRicci CosmologicalModels
open ProjectAinos.SpecialFunctions
open HarmonicPolynomial
local notation "E" => MinkowskiModel 3

private def realPoly (p : ℂ[X]) (s : ℝ) := (p.eval (s : ℂ)).re

private theorem smooth_realPoly (p : ℂ[X]) : ContDiff ℝ ∞ (realPoly p) := by
  have hp : ContDiff ℂ ∞ (fun z : ℂ => p.eval z) := by simpa using p.contDiff_aeval (𝕜 := ℂ) ∞
  exact hp.real_of_complex

private theorem dpoly (p : ℂ[X]) : deriv (realPoly p) = realPoly p.derivative :=
  funext fun s => (p.hasDerivAt (s : ℂ)).real_of_complex.deriv

private abbrev G (l m : ℕ) := ClassicalPolynomial.gegenbauer ((l : ℂ)+1) m

private theorem gegenbauer_radial (l m : ℕ) (s : ℝ) :
    let F := realPoly (G l m)
    (1-s^2)*deriv (deriv F) s-(2*l+3)*s*deriv F s+
      (m : ℝ)*(m+2*l+2)*F s=0 := by
  let p := G l m
  have h := congrArg (Polynomial.eval (s : ℂ))
    (ClassicalPolynomial.gegenbauer_equation ((l : ℂ)+1) m)
  change eval _ ((1-X^2)*p.derivative.derivative-C (2*((l : ℂ)+1)+1)*X*p.derivative+
    C (m*(m+2*((l : ℂ)+1)))*p) = eval _ 0 at h
  simp only [eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_zero,eval_pow,eval_one] at h
  have eq : (((1-s^2 : ℝ) : ℂ))*p.derivative.derivative.eval (s : ℂ)-
      (((2*(l : ℝ)+3)*s : ℝ) : ℂ)*p.derivative.eval (s : ℂ)+
      (((m : ℝ)*(m+2*l+2) : ℝ) : ℂ)*p.eval (s : ℂ)=0 := by
    push_cast; linear_combination h
  have re := congrArg Complex.re eq
  simpa only [realPoly,dpoly,add_re,sub_re,re_ofReal_mul,zero_re] using re

/-- Degree ℓ+m scalar harmonic in the closed stereographic chart. -/
def closedHarmonic {l : ℕ} (p : harmonics 3 l) (m : ℕ) := chartHarmonic p 1
  (fun s : ℝ => ((ClassicalPolynomial.gegenbauer ((l : ℂ)+1) m).eval (s : ℂ)).re)

/-- Scalar standing wave with continuous frequency ξ on the open stereographic chart. -/
def openHarmonic {l : ℕ} (p : harmonics 3 l) (ξ : ℝ) :=
  chartHarmonic p (-1) (Hyperbolic.ambientProfile ξ l)

/-- The closed spatial eigenvalues are n(n+2), for n=ℓ+m. -/
theorem closedHarmonic_equation {l : ℕ} (p : harmonics 3 l) (m : ℕ) (x : E) :
    spatialLaplacian 1 (closedHarmonic p m) x =
      -((l+m : ℕ) : ℝ)*(l+m+2)*closedHarmonic p m x := by
  have hx : psi 1 x ≠ 0 := by unfold psi; positivity
  change spatialLaplacian 1 (chartHarmonic p 1 (realPoly (G l m))) x=_
  rw [chartHarmonic_laplacian p 1 hx (smooth_realPoly _).contDiffAt]
  have h := gegenbauer_radial l m (chartCoordinate 1 x)
  dsimp only at h
  dsimp only [closedHarmonic,chartHarmonic]
  change _ = -((l+m : ℕ) : ℝ)*(l+m+2)*(MvPolynomial.eval _ p.val.val*_*realPoly (G l m) _)
  push_cast
  linear_combination (MvPolynomial.eval (fun j : Fin 3 => x j.succ) p.val.val)*
    (psi 1 x)^(-(l : ℤ))*h

private theorem chartCoordinate_open {x : E} (hx : 0 < psi (-1) x) :
    1 ≤ chartCoordinate (-1) x := by
  have hp : psi (-1) x ≤ 1 := by
    unfold psi
    nlinarith only [sq_nonneg (x 1),sq_nonneg (x 2),sq_nonneg (x 3)]
  have h : 2 ≤ 2/psi (-1) x := (le_div_iff₀ hx).mpr (by linarith)
  unfold chartCoordinate
  linarith

/-- The same chart operator on H³ gives 1+ξ² for every real frequency. -/
theorem openHarmonic_equation {l : ℕ} (p : harmonics 3 l) (ξ : ℝ) {x : E}
    (hx : 0 < psi (-1) x) :
    spatialLaplacian (-1) (openHarmonic p ξ) x = -(1+ξ^2)*openHarmonic p ξ x := by
  have hs := chartCoordinate_open hx
  change spatialLaplacian (-1) (chartHarmonic p (-1) (Hyperbolic.ambientProfile ξ l)) x=_
  rw [chartHarmonic_laplacian p (-1) hx.ne'
    (Hyperbolic.smooth_ambientProfile_at ξ l hs)]
  dsimp only [openHarmonic,chartHarmonic]
  linear_combination (MvPolynomial.eval (fun j : Fin 3 => x j.succ) p.val.val)*
    (psi (-1) x)^(-(l : ℤ))*Hyperbolic.ambient_equation ξ l hs

private theorem dust_mode {D : Data} (hN : D.N=D.a) {κ : ℝ} {ρ : ℝ → ℝ}
    (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0)) (hc : Continuous D.a)
    {x : E} (hx : x ∈ domain D) (hm : κ*ρ (x 0)≠0) (b q : ℝ) (Q : E → ℝ)
    (hQ : ContDiffAt ℝ ∞ Q x) (h₀ : ∀ᶠ y in 𝓝 x, part Q 0 y=0)
    (he : spatialLaplacian D.k Q x = -q*Q x) :
    ∀ φ ∈ ({decay D,growth D b} : Set (ℝ → ℝ)), LinearizedDustAt D κ ρ
      (separated φ Q) (contrast D κ ρ φ q Q) (covelocity D κ ρ φ Q) x := by
  have ht := time_mem hx
  obtain ⟨d,g,_⟩ := dust_amplitudes hN hB hc b ht
  obtain ⟨d',g'⟩ := smooth_amplitudes D hc b
  intro φ hφ
  rcases Set.mem_insert_iff.mp hφ with rfl | rfl
  · exact single_mode hN hB hx hm (d'.contDiffAt (D.isOpen_I.mem_nhds ht)) Q hQ h₀ q he d
  · exact single_mode hN hB hx hm (g'.contDiffAt (D.isOpen_I.mem_nhds ht)) Q hQ h₀ q he g

/-- Both independent modes of the exact closed dust background, with the density
and covelocity fixed by their harmonic on S³. -/
theorem closed_dust_modes {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ) {l : ℕ}
    (p : harmonics 3 l) (m : ℕ) (b : ℝ) {x : E} (hx : x ∈ domain (closedDust A hA)) :
    let D := closedDust A hA
    let ρ := dustDensity κ (6*A) D.a
    let q := ((l+m : ℕ) : ℝ)*(l+m+2)
    let Q := closedHarmonic p m
    ∀ φ ∈ ({decay D,growth D b} : Set (ℝ → ℝ)), LinearizedDustAt D κ ρ
      (separated φ Q) (contrast D κ ρ φ q Q) (covelocity D κ ρ φ Q) x := by
  dsimp only
  apply dust_mode rfl (isEinstein_closedDust hA hκ.ne') _ hx
    (mul_pos hκ (dustDensity_pos hκ (by positivity) (a_pos_of_mem hx))).ne'
  · change ContDiffAt ℝ ∞ (chartHarmonic _ 1 (realPoly (G l m))) _
    exact smooth_chartHarmonic _ _ (psi_pos hx).ne' (smooth_realPoly _).contDiffAt
  · exact chartHarmonic_time _ _ (psi_pos hx).ne' (smooth_realPoly _).contDiffAt
  · change spatialLaplacian 1 (closedHarmonic p m) x=_
    simpa only [neg_mul] using closedHarmonic_equation p m x
  · change Continuous (fun t => A*(1-Real.cos t)); fun_prop

/-- Both temporal solutions and the continuous H³ scalar harmonics solve the
linearized equations on the entire stereographic chart of the exact expanding open dust universe. -/
theorem open_dust_modes {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ) {l : ℕ}
    (p : harmonics 3 l) (ξ b : ℝ) {x : E} (hx : x ∈ domain (openDust A hA)) :
    let D := openDust A hA
    let ρ := dustDensity κ (6*A) D.a
    let Q := openHarmonic p ξ
    ∀ φ ∈ ({decay D,growth D b} : Set (ℝ → ℝ)), LinearizedDustAt D κ ρ
      (separated φ Q) (contrast D κ ρ φ (1+ξ^2) Q) (covelocity D κ ρ φ Q) x := by
  dsimp only
  have hF := Hyperbolic.smooth_ambientProfile_at ξ l (chartCoordinate_open (psi_pos hx))
  apply dust_mode rfl (isEinstein_openDust hA hκ.ne') _ hx
    (mul_pos hκ (dustDensity_pos hκ (by positivity) (a_pos_of_mem hx))).ne'
  · exact smooth_chartHarmonic _ _ (psi_pos hx).ne' hF
  · exact chartHarmonic_time _ _ (psi_pos hx).ne' hF
  · exact openHarmonic_equation p ξ (psi_pos hx)
  · change Continuous (fun t => A*(Real.cosh t-1)); fun_prop

end ProjectAinos.GeneralRelativity.CurvedPerturbation
