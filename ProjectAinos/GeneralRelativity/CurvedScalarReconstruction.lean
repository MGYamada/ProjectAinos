/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.CurvedCosmology
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Tactic

/-!
# Superposition of the curved scalar dust modes

Landau–Lifshitz, §115, for the closed (`k = +1`) and open (`k = −1`) dust universes in the
longitudinal scalar gauge (`CurvedPerturbation`). The linearized equations `LinearizedDustAt`
are, by `linearizedDustAt_iff`, three linear equations in the jets of `(u, δ, V)`; hence:

* `linearizedDustAt_add`, `linearizedDustAt_const_mul`, `linearizedDustAt_sum`:
  **superposition** — finite linear combinations of solutions smooth at a point solve the
  equations at that point.
* `closed_dust_expansion`, `open_dust_expansion`: every **finite** linear combination of the
  scalar modes of `closed_dust_modes` (the harmonics `closedHarmonic p m` of `S³`, eigenvalue
  `n(n+2)`) and of `open_dust_modes` (the harmonics `openHarmonic p ξ` of `H³`, eigenvalue
  `1 + ξ²`), each with either temporal solution, with the corresponding combinations of the
  density contrasts and covelocities, solves the linearized equations on the whole chart.

Not proved here: the expansion of general scalar data in these harmonics with convergence in a
norm controlling two derivatives, and the uniqueness of the coefficients (see the report of
§115); only finite expansions are treated.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.CurvedPerturbation

open SmoothGeometry CoordinateMetric FLRW IsotropicRicci CosmologicalModels
open ProjectAinos.SpecialFunctions

local notation "E" => MinkowskiModel 3

section Linear

variable {u w : E → ℝ} {x : E}

theorem part_add (hu : DifferentiableAt ℝ u x) (hw : DifferentiableAt ℝ w x) (i : Fin 4) :
    part (fun y => u y + w y) i x = part u i x + part w i x := by
  simp only [part]; rw [fderiv_fun_add hu hw]; rfl

theorem part_const_mul (hu : DifferentiableAt ℝ u x) (c : ℝ) (i : Fin 4) :
    part (fun y => c * u y) i x = c * part u i x := by
  simp only [part]; rw [fderiv_const_mul hu]; rfl

theorem secondPartial_add (hu : ContDiffAt ℝ ∞ u x) (hw : ContDiffAt ℝ ∞ w x) (a b : Fin 4) :
    secondPartial (fun y => u y + w y) x a b = secondPartial u x a b + secondPartial w x a b := by
  have hev : (fun z => fderiv ℝ (fun y => u y + w y) z (Pi.single b 1)) =ᶠ[𝓝 x]
      fun z => fderiv ℝ u z (Pi.single b 1) + fderiv ℝ w z (Pi.single b 1) := by
    filter_upwards [eventually_differentiableAt hu, eventually_differentiableAt hw] with z h1 h2
    rw [fderiv_fun_add h1 h2]; rfl
  simp only [secondPartial]
  rw [hev.fderiv_eq, fderiv_fun_add (differentiableAt_partial hu _) (differentiableAt_partial hw _)]
  rfl

theorem secondPartial_const_mul (hu : ContDiffAt ℝ ∞ u x) (c : ℝ) (a b : Fin 4) :
    secondPartial (fun y => c * u y) x a b = c * secondPartial u x a b := by
  have hev : (fun z => fderiv ℝ (fun y => c * u y) z (Pi.single b 1)) =ᶠ[𝓝 x]
      fun z => c * fderiv ℝ u z (Pi.single b 1) := by
    filter_upwards [eventually_differentiableAt hu] with z h1
    rw [fderiv_const_mul h1]; rfl
  simp only [secondPartial]
  rw [hev.fderiv_eq, fderiv_const_mul (differentiableAt_partial hu _)]
  rfl

theorem spatialLaplacian_add (hu : ContDiffAt ℝ ∞ u x) (hw : ContDiffAt ℝ ∞ w x) (k : ℝ) :
    spatialLaplacian k (fun y => u y + w y) x =
      spatialLaplacian k u x + spatialLaplacian k w x := by
  simp only [spatialLaplacian, secondPartial_add hu hw,
    part_add (hu.differentiableAt (by simp)) (hw.differentiableAt (by simp))]
  ring

theorem spatialLaplacian_const_mul (hu : ContDiffAt ℝ ∞ u x) (c k : ℝ) :
    spatialLaplacian k (fun y => c * u y) x = c * spatialLaplacian k u x := by
  simp only [spatialLaplacian, secondPartial_const_mul hu, part_const_mul
    (hu.differentiableAt (by simp))]
  ring

variable {D : Data} (hN : D.N = D.a) {κ : ℝ} {ρ : ℝ → ℝ}
  (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0))
include hN hB

/-- **Superposition** of two solutions of the linearized equations that are smooth at `x`. -/
theorem linearizedDustAt_add (hx : x ∈ domain D) (hu : ContDiffAt ℝ ∞ u x)
    (hw : ContDiffAt ℝ ∞ w x) {δ δ' : E → ℝ} {V V' : E → Fin 4 → ℝ}
    (h₁ : LinearizedDustAt D κ ρ u δ V x) (h₂ : LinearizedDustAt D κ ρ w δ' V' x) :
    LinearizedDustAt D κ ρ (fun y => u y + w y) (fun y => δ y + δ' y)
      (fun y i => V y i + V' y i) x := by
  have e1 := linearizedDustAt_iff hN hB hx hu δ V
  have e2 := linearizedDustAt_iff hN hB hx hw δ' V'
  have e3 := linearizedDustAt_iff hN hB hx (u := fun y => u y + w y) (hu.add hw)
    (fun y => δ y + δ' y)
    (fun y i => V y i + V' y i)
  dsimp only at e1 e2 e3
  rw [e1] at h₁
  rw [e2] at h₂
  rw [e3]
  have hdu := hu.differentiableAt (by simp)
  have hdw := hw.differentiableAt (by simp)
  obtain ⟨a1, a2, a3⟩ := h₁
  obtain ⟨b1, b2, b3⟩ := h₂
  simp only [secondPartial_add hu hw, part_add hdu hdw, spatialLaplacian_add hu hw]
  refine ⟨by linear_combination a1 + b1, by linear_combination a2 + b2, fun i hi => ?_⟩
  linear_combination a3 i hi + b3 i hi

/-- **Superposition**: a multiple of a solution smooth at `x` is a solution. -/
theorem linearizedDustAt_const_mul (hx : x ∈ domain D) (hu : ContDiffAt ℝ ∞ u x) (c : ℝ)
    {δ : E → ℝ} {V : E → Fin 4 → ℝ} (h : LinearizedDustAt D κ ρ u δ V x) :
    LinearizedDustAt D κ ρ (fun y => c * u y) (fun y => c * δ y) (fun y i => c * V y i) x := by
  have e1 := linearizedDustAt_iff hN hB hx hu δ V
  have e3 := linearizedDustAt_iff hN hB hx (u := fun y => c * u y)
    (contDiffAt_const.mul hu) (fun y => c * δ y) (fun y i => c * V y i)
  dsimp only at e1 e3
  rw [e1] at h
  rw [e3]
  have hdu := hu.differentiableAt (by simp)
  obtain ⟨a1, a2, a3⟩ := h
  simp only [secondPartial_const_mul hu, part_const_mul hdu, spatialLaplacian_const_mul hu]
  refine ⟨by linear_combination c * a1, by linear_combination c * a2, fun i hi => ?_⟩
  linear_combination c * a3 i hi

/-- **Finite superposition**: a finite linear combination of solutions smooth at `x` is a
solution at `x`. -/
theorem linearizedDustAt_sum {ι : Type*} (s : Finset ι) (hx : x ∈ domain D) (c : ι → ℝ)
    {U Δ : ι → E → ℝ} {W : ι → E → Fin 4 → ℝ} (hU : ∀ i ∈ s, ContDiffAt ℝ ∞ (U i) x)
    (h : ∀ i ∈ s, LinearizedDustAt D κ ρ (U i) (Δ i) (W i) x) :
    LinearizedDustAt D κ ρ (fun y => ∑ i ∈ s, c i * U i y) (fun y => ∑ i ∈ s, c i * Δ i y)
      (fun y j => ∑ i ∈ s, c i * W i y j) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := linearizedDustAt_const_mul hN hB hx (contDiffAt_const (c := (0 : ℝ))) 0
      (δ := fun _ => 0) (V := fun _ _ => 0)
      (by
        have e := linearizedDustAt_iff hN hB hx (contDiffAt_const (c := (0 : ℝ)))
          (fun _ => 0) (fun _ _ => 0)
        dsimp only at e
        rw [e]
        simp [secondPartial, part, spatialLaplacian])
    simpa using h0
  | insert a s ha ih =>
    have hs : ∀ y, ∑ i ∈ insert a s, c i * U i y = c a * U a y + ∑ i ∈ s, c i * U i y :=
      fun y => Finset.sum_insert ha
    have hsU : ContDiffAt ℝ ∞ (fun y => ∑ i ∈ s, c i * U i y) x :=
      ContDiffAt.sum fun i hi => contDiffAt_const.mul (hU i (Finset.mem_insert_of_mem hi))
    have h1 := linearizedDustAt_const_mul hN hB hx (hU a (Finset.mem_insert_self a s)) (c a)
      (h a (Finset.mem_insert_self a s))
    have h2 := ih (fun i hi => hU i (Finset.mem_insert_of_mem hi))
      (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have h3 := linearizedDustAt_add hN hB hx
      (contDiffAt_const.mul (hU a (Finset.mem_insert_self a s))) hsU h1 h2
    simpa only [Finset.sum_insert ha] using h3

end Linear

/-! ### Finite harmonic expansions on the closed and open dust universes -/

theorem contDiffAt_separated {x : E} {φ : ℝ → ℝ} (hφ : ContDiffAt ℝ ∞ φ (x 0))
    {Q : E → ℝ} (hQ : ContDiffAt ℝ ∞ Q x) : ContDiffAt ℝ ∞ (separated φ Q) x :=
  (hφ.comp x (contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0).contDiffAt).mul hQ

/-- **Finite expansions on the closed dust universe**: for finitely many closed scalar harmonics
`closedHarmonic (p i) (m i)` with eigenvalues `n(n+2)`, `n = ℓᵢ + mᵢ`, each with the decaying or
a growing temporal solution `φᵢ`, and real coefficients `cᵢ`, the combination of the modes with
the combinations of their density contrasts and covelocities solves the linearized Einstein
equations with dust on the whole chart. -/
theorem closed_dust_expansion {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ) {ι : Type*} (s : Finset ι)
    (l : ι → ℕ) (p : ∀ i, HarmonicPolynomial.harmonics 3 (l i)) (m : ι → ℕ) (b : ι → ℝ)
    (φ : ι → ℝ → ℝ) (hφ : ∀ i ∈ s, φ i ∈ ({decay (closedDust A hA),
      growth (closedDust A hA) (b i)} : Set (ℝ → ℝ))) (c : ι → ℝ) {x : E}
    (hx : x ∈ domain (closedDust A hA)) :
    LinearizedDustAt (closedDust A hA) κ (dustDensity κ (6 * A) (closedDust A hA).a)
      (fun y => ∑ i ∈ s, c i * separated (φ i) (closedHarmonic (p i) (m i)) y)
      (fun y => ∑ i ∈ s, c i * contrast (closedDust A hA) κ
        (dustDensity κ (6 * A) (closedDust A hA).a) (φ i)
        (((l i + m i : ℕ) : ℝ) * (l i + m i + 2)) (closedHarmonic (p i) (m i)) y)
      (fun y j => ∑ i ∈ s, c i * covelocity (closedDust A hA) κ
        (dustDensity κ (6 * A) (closedDust A hA).a) (φ i) (closedHarmonic (p i) (m i)) y j) x := by
  have hc : Continuous (closedDust A hA).a := by
    change Continuous (fun t => A * (1 - Real.cos t)); fun_prop
  refine linearizedDustAt_sum rfl (isEinstein_closedDust hA hκ.ne') s hx c (fun i hi => ?_)
    (fun i hi => closed_dust_modes hA hκ (p i) (m i) (b i) hx (φ i) (hφ i hi))
  have ht := time_mem hx
  obtain ⟨d', g'⟩ := smooth_amplitudes (closedDust A hA) hc (b i)
  have hP : ContDiff ℂ ∞ (fun z : ℂ =>
      (ClassicalPolynomial.gegenbauer ((l i : ℂ) + 1) (m i)).eval z) := by
    simpa [Polynomial.coe_aeval_eq_eval] using
      Polynomial.contDiff_aeval (𝕜 := ℂ) (ClassicalPolynomial.gegenbauer ((l i : ℂ) + 1) (m i)) ∞
  have hpoly : ContDiff ℝ ∞ (fun s : ℝ =>
      ((ClassicalPolynomial.gegenbauer ((l i : ℂ) + 1) (m i)).eval (s : ℂ)).re) :=
    Complex.reCLM.contDiff.comp ((hP.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff)
  have hQ : ContDiffAt ℝ ∞ (closedHarmonic (p i) (m i)) x :=
    smooth_chartHarmonic _ _ (psi_pos hx).ne' hpoly.contDiffAt
  rcases Set.mem_insert_iff.mp (hφ i hi) with h | h <;> rw [h]
  · exact contDiffAt_separated (d'.contDiffAt ((closedDust A hA).isOpen_I.mem_nhds ht)) hQ
  · exact contDiffAt_separated
      ((g'.contDiffAt ((closedDust A hA).isOpen_I.mem_nhds ht))) hQ

/-- On the open chart the coordinate `2/ψ − 1` of the hyperboloid is at least `1`. -/
theorem one_le_chartCoordinate {x : E} (hx : 0 < psi (-1) x) : 1 ≤ chartCoordinate (-1) x := by
  have hp : psi (-1) x ≤ 1 := by
    unfold psi
    nlinarith only [sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
  have h : 2 ≤ 2 / psi (-1) x := (le_div_iff₀ hx).mpr (by linarith)
  unfold chartCoordinate
  linarith

/-- **Finite expansions on the open dust universe**: the same for the continuous `H³` scalar
harmonics `openHarmonic (p i) (ξ i)` with eigenvalues `1 + ξᵢ²`. -/
theorem open_dust_expansion {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ) {ι : Type*} (s : Finset ι)
    (l : ι → ℕ) (p : ∀ i, HarmonicPolynomial.harmonics 3 (l i)) (ξ b : ι → ℝ)
    (φ : ι → ℝ → ℝ) (hφ : ∀ i ∈ s, φ i ∈ ({decay (openDust A hA),
      growth (openDust A hA) (b i)} : Set (ℝ → ℝ))) (c : ι → ℝ) {x : E}
    (hx : x ∈ domain (openDust A hA)) :
    LinearizedDustAt (openDust A hA) κ (dustDensity κ (6 * A) (openDust A hA).a)
      (fun y => ∑ i ∈ s, c i * separated (φ i) (openHarmonic (p i) (ξ i)) y)
      (fun y => ∑ i ∈ s, c i * contrast (openDust A hA) κ
        (dustDensity κ (6 * A) (openDust A hA).a) (φ i) (1 + ξ i ^ 2)
        (openHarmonic (p i) (ξ i)) y)
      (fun y j => ∑ i ∈ s, c i * covelocity (openDust A hA) κ
        (dustDensity κ (6 * A) (openDust A hA).a) (φ i) (openHarmonic (p i) (ξ i)) y j) x := by
  have hc : Continuous (openDust A hA).a := by
    change Continuous (fun t => A * (Real.cosh t - 1)); fun_prop
  refine linearizedDustAt_sum rfl (isEinstein_openDust hA hκ.ne') s hx c (fun i hi => ?_)
    (fun i hi => open_dust_modes hA hκ (p i) (ξ i) (b i) hx (φ i) (hφ i hi))
  have ht := time_mem hx
  obtain ⟨d', g'⟩ := smooth_amplitudes (openDust A hA) hc (b i)
  have hQ : ContDiffAt ℝ ∞ (openHarmonic (p i) (ξ i)) x :=
    smooth_chartHarmonic _ _ (psi_pos hx).ne'
      (Hyperbolic.smooth_ambientProfile_at (ξ i) (l i) (one_le_chartCoordinate (psi_pos hx)))
  rcases Set.mem_insert_iff.mp (hφ i hi) with h | h <;> rw [h]
  · exact contDiffAt_separated (d'.contDiffAt ((openDust A hA).isOpen_I.mem_nhds ht)) hQ
  · exact contDiffAt_separated
      ((g'.contDiffAt ((openDust A hA).isOpen_I.mem_nhds ht))) hQ

end ProjectAinos.GeneralRelativity.CurvedPerturbation
