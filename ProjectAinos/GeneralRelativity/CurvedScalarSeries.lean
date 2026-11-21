/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.CurvedScalarReconstruction
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
# Expansions of curved scalar perturbations in separated modes

Landau–Lifshitz, §115, for the closed and open universes in the longitudinal scalar gauge
(`CurvedPerturbation`). For a potential `u` smooth at `x`, `linearizedDustAt_iff` reduces the
linearized Einstein equations with dust to three equations in the jets of `(u, δ, V)`, recorded
here as `ScalarSystemAt` (`linearizedDustAt_iff_scalarSystemAt`): the evolution equation
`u″ + 3Hu′ − 2ku = 0`, the density constraint and the momentum constraints.

* `IsC2Series U f`: **a series converging with two derivatives** on the open set `U`: near every
  point the terms, their first and their second derivatives are bounded by a summable sequence.
  The derivatives of the sum are then the sums of the derivatives (`IsC2Series.part_tsum`,
  `IsC2Series.secondPartial_tsum`, `IsC2Series.hasSum_spatialLaplacian`), by
  `hasFDerivAt_tsum_of_isPreconnected` applied to the terms and to their partial derivatives.
  Finite and finitely supported families of `C²` functions are instances (`IsC2Series.of_finite`,
  `IsC2Series.of_finite_support`).
* `IsModeFamily D φ Q q`: separated modes `φᵢ(t) Qᵢ(x)` with time functions smooth on `I` and
  time-independent spatial eigenfunctions `Δ_k Qᵢ = −qᵢ Qᵢ`.
* `scalarSystemAt_tsum_iff`: **the expansion** `u = Σ φᵢ Qᵢ` with the density contrast
  `δ = Σ contrastᵢ` and the covelocity `V = Σ covelocityᵢ` of the modes **satisfies the scalar
  system at `x` if and only if `Σ (φᵢ″ + 3Hφᵢ′ − 2kφᵢ) Qᵢ(x) = 0`**: the constraints hold term by
  term. Hence `scalarSystemAt_tsum`: if every mode satisfies its evolution equation, the
  expansion solves the system; `linearizedDustAt_tsum`: it solves the linearized Einstein
  equations wherever the sum is smooth.
* `HasUniqueCoefficients S Q`: a uniformly absolutely summable combination `Σ cᵢ Qᵢ` vanishing on
  `S` has vanishing coefficients. `evolution_of_scalarSystemAt`, `scalarSystemAt_slice_iff`:
  **with unique coefficients on a time slice, the expansion solves the system on the slice if and
  only if every mode satisfies its evolution equation at that time**.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.CurvedPerturbation

open SmoothGeometry CoordinateMetric FLRW IsotropicRicci CosmologicalModels

local notation "E" => MinkowskiModel 3

/-! ### The scalar system -/

/-- **The scalar system of the longitudinal gauge** at `x`: the evolution equation of the
potential, the density constraint and the momentum constraints of `linearizedDustAt_iff`. -/
def ScalarSystemAt (D : Data) (κ : ℝ) (ρ : ℝ → ℝ) (u δ : E → ℝ) (V : E → Fin 4 → ℝ) (x : E) :
    Prop :=
  secondPartial u x 0 0 + 3 * hubble D (x 0) * part u 0 x - 2 * D.k * u x = 0 ∧
  κ * ρ (x 0) * D.a (x 0) ^ 2 / 2 * δ x = spatialLaplacian D.k u x -
    3 * hubble D (x 0) * (part u 0 x + hubble D (x 0) * u x) + 3 * D.k * u x ∧
  ∀ i : Fin 4, i ≠ 0 →
    κ * ρ (x 0) * D.a (x 0) * V x i = -2 * (secondPartial u x i 0 + hubble D (x 0) * part u i x)

/-- For a potential smooth at `x` the scalar system is the linearized Einstein–dust system. -/
theorem linearizedDustAt_iff_scalarSystemAt {D : Data} (hN : D.N = D.a) {κ : ℝ} {ρ : ℝ → ℝ}
    (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0)) {x : E}
    (hx : x ∈ domain D) {u : E → ℝ} (hu : ContDiffAt ℝ ∞ u x) (δ : E → ℝ) (V : E → Fin 4 → ℝ) :
    LinearizedDustAt D κ ρ u δ V x ↔ ScalarSystemAt D κ ρ u δ V x :=
  linearizedDustAt_iff hN hB hx hu δ V

/-! ### The jets of a separated mode -/

theorem part_separated {φ : ℝ → ℝ} {Q : E → ℝ} {x : E} (hφ : DifferentiableAt ℝ φ (x 0))
    (hQ : DifferentiableAt ℝ Q x) (i : Fin 4) :
    part (separated φ Q) i x =
      (if i = 0 then deriv φ (x 0) * Q x else 0) + φ (x 0) * part Q i x := by
  change fderiv ℝ (fun z : E => φ (z 0) * Q z) x (Pi.single i 1) = _
  have h := (hasFDerivAt_time hφ.hasDerivAt).mul hQ.hasFDerivAt
  change HasFDerivAt (fun z : E => φ (z 0) * Q z) _ x at h
  rw [h.fderiv]
  by_cases hi : i = 0 <;>
    simp [ContinuousLinearMap.proj_apply, smul_eq_mul, part, hi, eq_comm, mul_comm, add_comm]

/-- **The jets of a separated mode** `φ(t) Q(x)` with `Q` independent of the time. -/
theorem separated_jets {φ : ℝ → ℝ} {Q : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ (x 0)) (hQ : ContDiffAt ℝ ∞ Q x)
    (h₀ : ∀ᶠ y in 𝓝 x, part Q 0 y = 0) :
    part (separated φ Q) 0 x = deriv φ (x 0) * Q x ∧
    secondPartial (separated φ Q) x 0 0 = deriv (deriv φ) (x 0) * Q x ∧
    (∀ i : Fin 4, i ≠ 0 → secondPartial (separated φ Q) x i 0 = deriv φ (x 0) * part Q i x) ∧
    (∀ i : Fin 4, i ≠ 0 → part (separated φ Q) i x = φ (x 0) * part Q i x) ∧
    ∀ k, spatialLaplacian k (separated φ Q) x = φ (x 0) * spatialLaplacian k Q x := by
  have hφ' : ContDiffAt ℝ ∞ (deriv φ) (x 0) := hφ.derivWithin (by simp)
  have hf := hφ.differentiableAt (by simp)
  have hq := hQ.differentiableAt (by simp)
  have hp := (hφ.of_le (m := 1) (by simp)).eventually (by simp)
  have hnear : ∀ᶠ z : E in 𝓝 x, DifferentiableAt ℝ φ (z 0) :=
    ((continuous_apply 0 : Continuous (fun z : E => z 0)).continuousAt.tendsto.eventually hp).mono
      fun _ hz => hz.differentiableAt one_ne_zero
  have ev (i : Fin 4) : part (separated φ Q) i =ᶠ[𝓝 x] (if i = 0 then separated (deriv φ) Q
      else separated φ (part Q i)) := by
    filter_upwards [hnear, eventually_differentiableAt hQ, h₀] with y hy hyQ hy₀
    by_cases hi : i = 0 <;>
      simp [part_separated hy hyQ, hi, hy₀, separated]
  have sec (i j : Fin 4) : secondPartial (separated φ Q) x i j =
      part (if j = 0 then separated (deriv φ) Q else separated φ (part Q j)) i x :=
    congrArg (fun T : E →L[ℝ] ℝ => T (Pi.single i 1)) (ev j).fderiv_eq
  have hs (i : Fin 4) (hi : i ≠ 0) : secondPartial (separated φ Q) x i i =
      φ (x 0) * secondPartial Q x i i := by
    rw [sec]
    simp only [hi, ite_false]
    exact (part_separated hf (differentiableAt_partial hQ (Pi.single i 1)) i).trans (by
      simp only [hi, ite_false, zero_add]; rfl)
  refine ⟨by simpa [separated] using (ev 0).eq_of_nhds, ?_, ?_, ?_, ?_⟩
  · rw [sec]
    simp [part_separated (hφ'.differentiableAt (by simp)) hq, h₀.self_of_nhds]
  · intro i hi
    rw [sec]
    simp [part_separated (hφ'.differentiableAt (by simp)) hq, hi]
  · intro i hi
    rw [part_separated hf hq]
    simp [hi]
  · intro k
    simp [spatialLaplacian, hs, part_separated hf hq]
    ring

/-! ### Series converging with two derivatives -/

variable {ι : Type*}

/-- **A series converging with two derivatives** on `U`: near every point of `U`, on a ball
contained in `U`, the terms are twice differentiable, and the terms, their first and their second
derivatives are bounded by a summable sequence. -/
structure IsC2Series (U : Set E) (f : ι → E → ℝ) : Prop where
  /-- The local summable bounds. -/
  local_bound : ∀ x ∈ U, ∃ ε > 0, ball x ε ⊆ U ∧ ∃ b : ι → ℝ, Summable b ∧
    ∀ i, ∀ y ∈ ball x ε, DifferentiableAt ℝ (f i) y ∧ DifferentiableAt ℝ (fderiv ℝ (f i)) y ∧
      ‖f i y‖ ≤ b i ∧ ‖fderiv ℝ (f i) y‖ ≤ b i ∧ ‖fderiv ℝ (fderiv ℝ (f i)) y‖ ≤ b i

namespace IsC2Series

variable {U : Set E} {f : ι → E → ℝ}

theorem summable (hS : IsC2Series U f) {y : E} (hy : y ∈ U) : Summable fun i => f i y := by
  obtain ⟨ε, hε, -, b, hb, h⟩ := hS.local_bound y hy
  exact hb.of_norm_bounded fun i => (h i y (mem_ball_self hε)).2.2.1

/-- On the ball of a local bound the sum is differentiable with the sum of the derivatives. -/
theorem hasFDerivAt_of_mem {x : E} {ε : ℝ} {b : ι → ℝ} (hb : Summable b)
    (h : ∀ i, ∀ y ∈ ball x ε, DifferentiableAt ℝ (f i) y ∧ DifferentiableAt ℝ (fderiv ℝ (f i)) y ∧
      ‖f i y‖ ≤ b i ∧ ‖fderiv ℝ (f i) y‖ ≤ b i ∧ ‖fderiv ℝ (fderiv ℝ (f i)) y‖ ≤ b i)
    (hε : 0 < ε) {z : E} (hz : z ∈ ball x ε) :
    HasFDerivAt (fun w => ∑' i, f i w) (∑' i, fderiv ℝ (f i) z) z :=
  hasFDerivAt_tsum_of_isPreconnected hb isOpen_ball (convex_ball x ε).isPreconnected
    (fun i y hy => (h i y hy).1.hasFDerivAt) (fun i y hy => (h i y hy).2.2.2.1)
    (mem_ball_self hε) (hb.of_norm_bounded fun i => (h i x (mem_ball_self hε)).2.2.1) hz

theorem summable_fderiv (hS : IsC2Series U f) {y : E} (hy : y ∈ U) :
    Summable fun i => fderiv ℝ (f i) y := by
  obtain ⟨ε, hε, -, b, hb, h⟩ := hS.local_bound y hy
  exact hb.of_norm_bounded fun i => (h i y (mem_ball_self hε)).2.2.2.1

/-- **The derivative of the sum is the sum of the derivatives.** -/
theorem hasFDerivAt (hS : IsC2Series U f) {y : E} (hy : y ∈ U) :
    HasFDerivAt (fun w => ∑' i, f i w) (∑' i, fderiv ℝ (f i) y) y := by
  obtain ⟨ε, hε, -, b, hb, h⟩ := hS.local_bound y hy
  exact hasFDerivAt_of_mem hb h hε (mem_ball_self hε)

theorem fderiv_eventuallyEq (hS : IsC2Series U f) {y : E} (hy : y ∈ U) :
    fderiv ℝ (fun w => ∑' i, f i w) =ᶠ[𝓝 y] fun w => ∑' i, fderiv ℝ (f i) w := by
  obtain ⟨ε, hε, -, b, hb, h⟩ := hS.local_bound y hy
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz
  exact (hasFDerivAt_of_mem hb h hε hz).fderiv

theorem differentiableAt_fderiv (hS : IsC2Series U f) {y : E} (hy : y ∈ U) (i : ι) :
    DifferentiableAt ℝ (fderiv ℝ (f i)) y := by
  obtain ⟨ε, hε, -, b, hb, h⟩ := hS.local_bound y hy
  exact (h i y (mem_ball_self hε)).2.1

theorem secondPartial_eq (hS : IsC2Series U f) {y : E} (hy : y ∈ U) (i : ι) (a c : Fin 4) :
    secondPartial (f i) y a c = fderiv ℝ (fderiv ℝ (f i)) y (Pi.single a 1) (Pi.single c 1) := by
  have h := (ContinuousLinearMap.apply ℝ ℝ (Pi.single c 1 : E)).hasFDerivAt.comp y
    (hS.differentiableAt_fderiv hy i).hasFDerivAt
  simp only [secondPartial]
  rw [show (fun z => fderiv ℝ (f i) z (Pi.single c 1)) =
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single c 1 : E)) ∘ fderiv ℝ (f i) from rfl, h.fderiv]
  rfl

/-- **The partial derivatives of the sum are the sums of the partial derivatives.** -/
theorem part_tsum (hS : IsC2Series U f) {y : E} (hy : y ∈ U) (j : Fin 4) :
    part (fun w => ∑' i, f i w) j y = ∑' i, part (f i) j y := by
  simp only [part]
  rw [(hS.hasFDerivAt hy).fderiv]
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : E)).map_tsum (hS.summable_fderiv hy)

theorem summable_part (hS : IsC2Series U f) {y : E} (hy : y ∈ U) (j : Fin 4) :
    Summable fun i => part (f i) j y :=
  (hS.summable_fderiv hy).mapL (ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : E))

/-- The derivatives of the partial derivatives `z ↦ ∂_c fᵢ(z)` of the terms, and their sum. -/
theorem hasFDerivAt_part_tsum (hS : IsC2Series U f) {y : E} (hy : y ∈ U) (v : E) :
    (Summable fun i => (ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ (f i)) y)) ∧
    HasFDerivAt (fun z => fderiv ℝ (fun w => ∑' i, f i w) z v)
      (∑' i, (ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ (f i)) y)) y := by
  obtain ⟨ε, hε, -, b, hb, h⟩ := hS.local_bound y hy
  let A : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  have hg (i : ι) (z : E) (hz : z ∈ ball y ε) : HasFDerivAt (fun w => fderiv ℝ (f i) w v)
      (A.comp (fderiv ℝ (fderiv ℝ (f i)) z)) z :=
    A.hasFDerivAt.comp z (h i z hz).2.1.hasFDerivAt
  have hg' (i : ι) (z : E) (hz : z ∈ ball y ε) :
      ‖A.comp (fderiv ℝ (fderiv ℝ (f i)) z)‖ ≤ ‖A‖ * b i :=
    (A.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (h i z hz).2.2.2.2 (norm_nonneg _))
  have hg0 : Summable fun i => fderiv ℝ (f i) y v :=
    ((hb.of_norm_bounded fun i => (h i y (mem_ball_self hε)).2.2.2.1).mapL A)
  have hD := hasFDerivAt_tsum_of_isPreconnected (hb.mul_left ‖A‖) isOpen_ball
    (convex_ball y ε).isPreconnected hg hg' (mem_ball_self hε) hg0 (mem_ball_self hε)
  have hev : (fun z => fderiv ℝ (fun w => ∑' i, f i w) z v) =ᶠ[𝓝 y]
      fun z => ∑' i, fderiv ℝ (f i) z v := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz
    rw [(hasFDerivAt_of_mem hb h hε hz).fderiv]
    exact A.map_tsum (hb.of_norm_bounded fun i => (h i z hz).2.2.2.1)
  exact ⟨(hb.mul_left ‖A‖).of_norm_bounded fun i => hg' i y (mem_ball_self hε),
    hD.congr_of_eventuallyEq hev⟩

/-- **The second partial derivatives of the sum are the sums of the second partial
derivatives.** -/
theorem secondPartial_tsum (hS : IsC2Series U f) {y : E} (hy : y ∈ U) (a c : Fin 4) :
    secondPartial (fun w => ∑' i, f i w) y a c = ∑' i, secondPartial (f i) y a c := by
  obtain ⟨hsum, hD⟩ := hS.hasFDerivAt_part_tsum hy (Pi.single c 1)
  simp only [secondPartial]
  rw [hD.fderiv]
  have e := (ContinuousLinearMap.apply ℝ ℝ (Pi.single a 1 : E)).map_tsum hsum
  refine e.trans (tsum_congr fun i => ?_)
  rw [← secondPartial, hS.secondPartial_eq hy i a c]
  rfl

theorem summable_secondPartial (hS : IsC2Series U f) {y : E} (hy : y ∈ U) (a c : Fin 4) :
    Summable fun i => secondPartial (f i) y a c := by
  obtain ⟨hsum, -⟩ := hS.hasFDerivAt_part_tsum hy (Pi.single c 1)
  exact (hsum.mapL (ContinuousLinearMap.apply ℝ ℝ (Pi.single a 1 : E))).congr fun i =>
    (hS.secondPartial_eq hy i a c).symm

/-- **The spatial Laplacian of the sum is the sum of the spatial Laplacians.** -/
theorem hasSum_spatialLaplacian (hS : IsC2Series U f) {y : E} (hy : y ∈ U) (k : ℝ) :
    HasSum (fun i => spatialLaplacian k (f i) y)
      (spatialLaplacian k (fun w => ∑' i, f i w) y) := by
  simp only [spatialLaplacian, hS.secondPartial_tsum hy, hS.part_tsum hy]
  have s (a : Fin 4) := (hS.summable_secondPartial hy a a).hasSum
  have p (a : Fin 4) := (hS.summable_part hy a).hasSum
  exact ((((s 1).add (s 2)).add (s 3)).mul_left _).sub
    (((((p 1).mul_left (y 1)).add ((p 2).mul_left (y 2))).add ((p 3).mul_left (y 3))).mul_left _)
    |>.congr_fun fun i => by ring

/-- **Finite series converge with two derivatives**: a finite family of functions of class `C²`
on an open set is a series of the class. -/
theorem of_finite [Finite ι] (hU : IsOpen U) (hf : ∀ i, ∀ x ∈ U, ContDiffAt ℝ 2 (f i) x) :
    IsC2Series U f where
  local_bound x hx := by
    have hev : ∀ᶠ y in 𝓝 x, y ∈ U ∧ ∀ i, DifferentiableAt ℝ (f i) y ∧
        DifferentiableAt ℝ (fderiv ℝ (f i)) y ∧ ‖f i y‖ < ‖f i x‖ + 1 ∧
        ‖fderiv ℝ (f i) y‖ < ‖fderiv ℝ (f i) x‖ + 1 ∧
        ‖fderiv ℝ (fderiv ℝ (f i)) y‖ < ‖fderiv ℝ (fderiv ℝ (f i)) x‖ + 1 := by
      refine Filter.Eventually.and (hU.mem_nhds hx : ∀ᶠ y in 𝓝 x, y ∈ U)
        (eventually_all.2 fun i => ?_)
      have h2 := hf i x hx
      have h1 : ContDiffAt ℝ 1 (fderiv ℝ (f i)) x := h2.fderiv_right (m := 1) (by norm_num)
      have h0 : ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ (f i))) x :=
        h1.fderiv_right (m := 0) (by norm_num)
      have n2 : ∀ᶠ y in 𝓝 x,
          ‖fderiv ℝ (fderiv ℝ (f i)) y‖ < ‖fderiv ℝ (fderiv ℝ (f i)) x‖ + 1 := by
        filter_upwards [h0.continuousAt.eventually_mem (Metric.ball_mem_nhds _ one_pos)] with y hy
        rw [mem_ball_iff_norm] at hy
        have := norm_le_insert' (fderiv ℝ (fderiv ℝ (f i)) y) (fderiv ℝ (fderiv ℝ (f i)) x)
        linarith
      have n1 : ContinuousAt (fun y => ‖fderiv ℝ (f i) y‖) x := h1.continuousAt.norm
      filter_upwards [h2.eventually (by simp),
        h2.continuousAt.norm.eventually (Iio_mem_nhds (lt_add_one _)),
        n1.eventually (Iio_mem_nhds (lt_add_one _)),
        n2] with y hy c0 c1 c2
      exact ⟨hy.differentiableAt (by norm_num),
        (hy.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num), c0, c1, c2⟩
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
    refine ⟨ε, hε, fun y hy => (hball y hy).1, fun i => ‖f i x‖ + 1 +
      (‖fderiv ℝ (f i) x‖ + 1) + (‖fderiv ℝ (fderiv ℝ (f i)) x‖ + 1),
      Summable.of_finite, fun i y hy => ?_⟩
    obtain ⟨-, h⟩ := hball y hy
    obtain ⟨d0, d1, c0, c1, c2⟩ := h i
    refine ⟨d0, d1, ?_, ?_, ?_⟩ <;> nlinarith [norm_nonneg (f i x), norm_nonneg (fderiv ℝ (f i) x),
      norm_nonneg (fderiv ℝ (fderiv ℝ (f i)) x)]

/-- **Finitely supported series converge with two derivatives**: if all but finitely many terms
vanish and the others are of class `C²` on an open set, the family is a series of the class. -/
theorem of_finite_support (hU : IsOpen U) (s : Finset ι) (h0 : ∀ i ∉ s, f i = 0)
    (hf : ∀ i ∈ s, ∀ x ∈ U, ContDiffAt ℝ 2 (f i) x) : IsC2Series U f where
  local_bound x hx := by
    classical
    obtain ⟨ε, hε, hεU, b, -, hb⟩ := (of_finite (ι := s) (f := fun i => f i) hU
      fun i y hy => hf i i.2 y hy).local_bound x hx
    refine ⟨ε, hε, hεU, fun i => if h : i ∈ s then b ⟨i, h⟩ else 0, ?_, fun i y hy => ?_⟩
    · exact summable_of_ne_finset_zero (s := s) fun i hi => by simp [hi]
    · by_cases h : i ∈ s
      · simpa [h] using hb ⟨i, h⟩ y hy
      · simp only [h, dite_false, h0 i h]
        simp
        exact le_of_eq ContinuousLinearMap.opNorm_zero

end IsC2Series

/-! ### Expansions in separated modes -/

/-- **A family of separated scalar modes** on the domain: time functions smooth on `I` and
time-independent spatial eigenfunctions `Δ_k Qᵢ = −qᵢ Qᵢ` of the chart Laplacian. -/
structure IsModeFamily (D : Data) (φ : ι → ℝ → ℝ) (Q : ι → E → ℝ) (q : ι → ℝ) : Prop where
  /-- The time functions are smooth on `I`. -/
  smooth_time : ∀ i, ContDiffOn ℝ ∞ (φ i) D.I
  /-- The spatial functions are smooth on the domain. -/
  smooth_space : ∀ i, ∀ x ∈ domain D, ContDiffAt ℝ ∞ (Q i) x
  /-- The spatial functions do not depend on the time. -/
  static : ∀ i, ∀ x ∈ domain D, part (Q i) 0 x = 0
  /-- The spatial functions are eigenfunctions of the chart Laplacian. -/
  eigen : ∀ i, ∀ x ∈ domain D, spatialLaplacian D.k (Q i) x = -q i * Q i x

variable {D : Data} {κ : ℝ} {ρ : ℝ → ℝ} {φ : ι → ℝ → ℝ} {Q : ι → E → ℝ} {q : ι → ℝ}

theorem IsModeFamily.jets (hF : IsModeFamily D φ Q q) {x : E} (hx : x ∈ domain D) (i : ι) :
    part (separated (φ i) (Q i)) 0 x = deriv (φ i) (x 0) * Q i x ∧
    secondPartial (separated (φ i) (Q i)) x 0 0 = deriv (deriv (φ i)) (x 0) * Q i x ∧
    (∀ j : Fin 4, j ≠ 0 →
      secondPartial (separated (φ i) (Q i)) x j 0 = deriv (φ i) (x 0) * part (Q i) j x) ∧
    (∀ j : Fin 4, j ≠ 0 → part (separated (φ i) (Q i)) j x = φ i (x 0) * part (Q i) j x) ∧
    spatialLaplacian D.k (separated (φ i) (Q i)) x = -q i * (φ i (x 0) * Q i x) := by
  have ht := time_mem hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := separated_jets
    ((hF.smooth_time i).contDiffAt (D.isOpen_I.mem_nhds ht)) (hF.smooth_space i x hx)
    (eventually_of_mem ((domain D).isOpen.mem_nhds hx) fun y hy => hF.static i y hy)
  refine ⟨h1, h2, h3, h4, ?_⟩
  rw [h5, hF.eigen i x hx]
  ring

/-- The evolution residual `φ″ + 3Hφ′ − 2kφ` of a time function. -/
def evolutionResidual (D : Data) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv φ) t + 3 * hubble D t * deriv φ t - 2 * D.k * φ t

theorem evolution_iff (φ : ℝ → ℝ) (t : ℝ) : Evolution D φ t ↔ evolutionResidual D φ t = 0 :=
  Iff.rfl

/-- **The scalar system of an expansion in separated modes**: with the density contrasts and
covelocities of the modes, the expansion `u = Σ φᵢ Qᵢ` satisfies the scalar system at `x` if and
only if `Σ (φᵢ″ + 3Hφᵢ′ − 2kφᵢ) Qᵢ(x) = 0`. -/
theorem scalarSystemAt_tsum_iff (hF : IsModeFamily D φ Q q)
    (hS : IsC2Series (domain D) fun i => separated (φ i) (Q i)) {x : E} (hx : x ∈ domain D)
    (hm : κ * ρ (x 0) ≠ 0) :
    ScalarSystemAt D κ ρ (fun y => ∑' i, separated (φ i) (Q i) y)
        (fun y => ∑' i, contrast D κ ρ (φ i) (q i) (Q i) y)
        (fun y j => ∑' i, covelocity D κ ρ (φ i) (Q i) y j) x ↔
      ∑' i, evolutionResidual D (φ i) (x 0) * Q i x = 0 := by
  have ha := (a_pos_of_mem hx).ne'
  obtain ⟨hκ, hρ⟩ := mul_ne_zero_iff.mp hm
  -- the sums of the jets
  have s0 : HasSum (fun i => φ i (x 0) * Q i x) (∑' i, separated (φ i) (Q i) x) :=
    (hS.summable hx).hasSum
  have s1 : HasSum (fun i => deriv (φ i) (x 0) * Q i x)
      (part (fun y => ∑' i, separated (φ i) (Q i) y) 0 x) := by
    rw [hS.part_tsum hx]
    exact ((hS.summable_part hx 0).hasSum).congr_fun fun i => ((hF.jets hx i).1).symm
  have s2 : HasSum (fun i => deriv (deriv (φ i)) (x 0) * Q i x)
      (secondPartial (fun y => ∑' i, separated (φ i) (Q i) y) x 0 0) := by
    rw [hS.secondPartial_tsum hx]
    exact ((hS.summable_secondPartial hx 0 0).hasSum).congr_fun fun i =>
      ((hF.jets hx i).2.1).symm
  have sL : HasSum (fun i => -q i * (φ i (x 0) * Q i x))
      (spatialLaplacian D.k (fun y => ∑' i, separated (φ i) (Q i) y) x) :=
    (hS.hasSum_spatialLaplacian hx D.k).congr_fun fun i => ((hF.jets hx i).2.2.2.2).symm
  have sj (j : Fin 4) (hj : j ≠ 0) : HasSum (fun i => deriv (φ i) (x 0) * part (Q i) j x)
      (secondPartial (fun y => ∑' i, separated (φ i) (Q i) y) x j 0) := by
    rw [hS.secondPartial_tsum hx]
    exact ((hS.summable_secondPartial hx j 0).hasSum).congr_fun fun i =>
      ((hF.jets hx i).2.2.1 j hj).symm
  have pj (j : Fin 4) (hj : j ≠ 0) : HasSum (fun i => φ i (x 0) * part (Q i) j x)
      (part (fun y => ∑' i, separated (φ i) (Q i) y) j x) := by
    rw [hS.part_tsum hx]
    exact ((hS.summable_part hx j).hasSum).congr_fun fun i => ((hF.jets hx i).2.2.2.1 j hj).symm
  -- the evolution equation
  have e1 : HasSum (fun i => evolutionResidual D (φ i) (x 0) * Q i x)
      (secondPartial (fun y => ∑' i, separated (φ i) (Q i) y) x 0 0 +
        3 * hubble D (x 0) * part (fun y => ∑' i, separated (φ i) (Q i) y) 0 x -
          2 * D.k * ∑' i, separated (φ i) (Q i) x) :=
    ((s2.add (s1.mul_left (3 * hubble D (x 0)))).sub (s0.mul_left (2 * D.k))).congr_fun fun i => by
      simp only [evolutionResidual]; ring
  -- the density constraint
  have e2 : HasSum (fun i => contrast D κ ρ (φ i) (q i) (Q i) x)
      (2 / (κ * ρ (x 0) * D.a (x 0) ^ 2) *
        (spatialLaplacian D.k (fun y => ∑' i, separated (φ i) (Q i) y) x -
          3 * hubble D (x 0) * (part (fun y => ∑' i, separated (φ i) (Q i) y) 0 x +
            hubble D (x 0) * ∑' i, separated (φ i) (Q i) x) +
          3 * D.k * ∑' i, separated (φ i) (Q i) x)) :=
    (((sL.sub ((s1.add (s0.mul_left (hubble D (x 0)))).mul_left (3 * hubble D (x 0)))).add
      (s0.mul_left (3 * D.k))).mul_left
      (2 / (κ * ρ (x 0) * D.a (x 0) ^ 2))).congr_fun fun i => by
        simp only [contrast]
        field_simp
        ring
  -- the momentum constraints
  have e3 (j : Fin 4) (hj : j ≠ 0) : HasSum (fun i => covelocity D κ ρ (φ i) (Q i) x j)
      (-2 / (κ * ρ (x 0) * D.a (x 0)) *
        (secondPartial (fun y => ∑' i, separated (φ i) (Q i) y) x j 0 +
          hubble D (x 0) * part (fun y => ∑' i, separated (φ i) (Q i) y) j x)) :=
    (((sj j hj).add ((pj j hj).mul_left (hubble D (x 0)))).mul_left
      (-2 / (κ * ρ (x 0) * D.a (x 0)))).congr_fun fun i => by
        simp only [covelocity]
        field_simp
  rw [e1.tsum_eq]
  unfold ScalarSystemAt
  beta_reduce
  refine ⟨fun h => h.1, fun h => ⟨h, ?_, fun j hj => ?_⟩⟩
  · rw [e2.tsum_eq]
    field_simp
  · rw [(e3 j hj).tsum_eq]
    field_simp

/-- **If every mode satisfies its evolution equation, the expansion solves the scalar system.** -/
theorem scalarSystemAt_tsum (hF : IsModeFamily D φ Q q)
    (hS : IsC2Series (domain D) fun i => separated (φ i) (Q i)) {x : E} (hx : x ∈ domain D)
    (hm : κ * ρ (x 0) ≠ 0) (hE : ∀ i, Evolution D (φ i) (x 0)) :
    ScalarSystemAt D κ ρ (fun y => ∑' i, separated (φ i) (Q i) y)
      (fun y => ∑' i, contrast D κ ρ (φ i) (q i) (Q i) y)
      (fun y j => ∑' i, covelocity D κ ρ (φ i) (Q i) y j) x := by
  rw [scalarSystemAt_tsum_iff hF hS hx hm]
  have h : ∀ i, evolutionResidual D (φ i) (x 0) * Q i x = 0 := fun i => by
    rw [show evolutionResidual D (φ i) (x 0) = 0 from hE i, zero_mul]
  simp [h]

/-- **The expansion solves the linearized Einstein equations with dust** wherever its sum is
smooth, if every mode satisfies its evolution equation. -/
theorem linearizedDustAt_tsum (hN : D.N = D.a)
    (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0)) (hF : IsModeFamily D φ Q q)
    (hS : IsC2Series (domain D) fun i => separated (φ i) (Q i)) {x : E} (hx : x ∈ domain D)
    (hm : κ * ρ (x 0) ≠ 0) (hu : ContDiffAt ℝ ∞ (fun y => ∑' i, separated (φ i) (Q i) y) x)
    (hE : ∀ i, Evolution D (φ i) (x 0)) :
    LinearizedDustAt D κ ρ (fun y => ∑' i, separated (φ i) (Q i) y)
      (fun y => ∑' i, contrast D κ ρ (φ i) (q i) (Q i) y)
      (fun y j => ∑' i, covelocity D κ ρ (φ i) (Q i) y j) x :=
  (linearizedDustAt_iff_scalarSystemAt hN hB hx hu _ _).mpr (scalarSystemAt_tsum hF hS hx hm hE)

/-! ### Uniqueness of the coefficients -/

/-- **Unique coefficients on `S`**: a combination `Σ cᵢ Qᵢ` with `|cᵢ Qᵢ| ≤ Mᵢ` on `S` for a
summable `M` that vanishes on `S` has vanishing coefficients. -/
def HasUniqueCoefficients (S : Set E) (Q : ι → E → ℝ) : Prop :=
  ∀ c : ι → ℝ, (∃ M : ι → ℝ, Summable M ∧ ∀ i, ∀ y ∈ S, |c i * Q i y| ≤ M i) →
    (∀ y ∈ S, ∑' i, c i * Q i y = 0) → ∀ i, c i = 0

/-- The time slice `{x ∈ domain | x 0 = t}`. -/
def slice (D : Data) (t : ℝ) : Set E := {x | x ∈ domain D ∧ x 0 = t}

/-- **With unique coefficients on a time slice, an expansion solving the scalar system on the
slice has modes satisfying their evolution equations at that time.** -/
theorem evolution_of_scalarSystemAt (hF : IsModeFamily D φ Q q)
    (hS : IsC2Series (domain D) fun i => separated (φ i) (Q i)) {t : ℝ}
    (hm : κ * ρ t ≠ 0) (hU : HasUniqueCoefficients (slice D t) Q)
    (hM : ∃ M : ι → ℝ, Summable M ∧
      ∀ i, ∀ y ∈ slice D t, |evolutionResidual D (φ i) t * Q i y| ≤ M i)
    (h : ∀ y ∈ slice D t, ScalarSystemAt D κ ρ (fun y => ∑' i, separated (φ i) (Q i) y)
      (fun y => ∑' i, contrast D κ ρ (φ i) (q i) (Q i) y)
      (fun y j => ∑' i, covelocity D κ ρ (φ i) (Q i) y j) y) (i : ι) :
    Evolution D (φ i) t := by
  refine hU (fun i => evolutionResidual D (φ i) t) hM (fun y hy => ?_) i
  have h0 := (scalarSystemAt_tsum_iff hF hS hy.1 (by rw [hy.2]; exact hm)).mp (h y hy)
  rwa [hy.2] at h0

/-- **On a slice with unique coefficients, the expansion solves the scalar system if and only if
every mode satisfies its evolution equation.** -/
theorem scalarSystemAt_slice_iff (hF : IsModeFamily D φ Q q)
    (hS : IsC2Series (domain D) fun i => separated (φ i) (Q i)) {t : ℝ}
    (hm : κ * ρ t ≠ 0) (hU : HasUniqueCoefficients (slice D t) Q)
    (hM : ∃ M : ι → ℝ, Summable M ∧
      ∀ i, ∀ y ∈ slice D t, |evolutionResidual D (φ i) t * Q i y| ≤ M i) :
    (∀ y ∈ slice D t, ScalarSystemAt D κ ρ (fun y => ∑' i, separated (φ i) (Q i) y)
      (fun y => ∑' i, contrast D κ ρ (φ i) (q i) (Q i) y)
      (fun y j => ∑' i, covelocity D κ ρ (φ i) (Q i) y j) y) ↔ ∀ i, Evolution D (φ i) t := by
  refine ⟨fun h => evolution_of_scalarSystemAt hF hS hm hU hM h, fun hE y hy => ?_⟩
  refine scalarSystemAt_tsum hF hS hy.1 (by rw [hy.2]; exact hm) fun i => ?_
  rw [hy.2]; exact hE i

end ProjectAinos.GeneralRelativity.CurvedPerturbation
