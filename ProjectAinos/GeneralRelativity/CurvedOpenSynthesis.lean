/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.CurvedScalarCompleteness
public import ProjectAinos.SpecialFunctions.SineTransformUniqueness
import Mathlib.Tactic

/-!
# Continuous syntheses of open dust perturbations

Landau–Lifshitz, §115, the open universe. The scalar harmonics of `H³` form a continuous family
`openHarmonic p ξ`, `ξ > 0`, so a general perturbation is a synthesis `∫ φ(ξ, t) Q_ξ(x) dμ(ξ)`
rather than a series.

* `IsC2Synthesis U μ f`: **a synthesis converging with two derivatives** on `U`: near every point
  of `U` the integrands, their first and second derivatives are dominated by a `μ`-integrable
  function of the frequency, and they are measurable in the frequency. The derivatives of the
  synthesis are the syntheses of the derivatives (`IsC2Synthesis.part_integral`,
  `IsC2Synthesis.secondPartial_integral`, `IsC2Synthesis.spatialLaplacian_integral`), by
  `hasFDerivAt_integral_of_dominated_of_fderiv_le`.
* `scalarSystemAt_integral_iff`: for a family of separated modes indexed by the frequency, **the
  synthesis with the density contrast and covelocity of the modes satisfies the scalar system at
  `x` if and only if `∫ (φ″ + 3Hφ′ − 2kφ)(ξ, t) Q_ξ(x) dμ(ξ) = 0`**.
* Angular degree `l = 0`: `openZonal ξ = openHarmonic harmonicOne ξ`, the zonal standing wave
  `sin(ξρ)/(ξ sinh ρ)` in the geodesic radius `ρ` (`openZonal_eq_zonalWave` off the time axis).
  `ae_eq_zero_of_integral_openZonal`: **uniqueness of the densities**: an integrable density whose
  synthesis vanishes on a time slice off the time axis vanishes almost everywhere; on the sphere
  of radius `ρ` the synthesis is `(sinh ρ)⁻¹ ∫ c(ξ) sin(ξρ)/ξ dξ`
  (`SineTransform.ae_eq_zero_of_integral_sin_div`).
* `open_zonal_scalarSystemAt_slice_iff`: **a zonal synthesis converging with two derivatives off
  the time axis, with an integrable evolution residual, solves the scalar system on a time slice
  off the axis if and only if almost every mode satisfies its evolution equation at that time.**
* `isC2Synthesis_unitDensity`, `unitDensity_synthesis_hypotheses`: the density `1` on `[1, 2]`
  gives a synthesis satisfying all the hypotheses, with a density that is not almost everywhere
  zero; the bounds come from the joint smoothness of `(ξ, x) ↦ sin(ξρ(x))/(ξ sinh ρ(x))`
  (`contDiffAt_zonalWave_derivs`) on compact sets.

The time axis `x₁ = x₂ = x₃ = 0` is excluded: there the profile is the smooth continuation of the
zonal wave (`HyperbolicZonal`), defined by a choice, without bounds uniform in the frequency.
The angular degrees `l ≥ 1` are not treated here.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory Real
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.CurvedPerturbation

open SmoothGeometry CoordinateMetric FLRW IsotropicRicci CosmologicalModels
open ProjectAinos.SpecialFunctions ProjectAinos.SpecialFunctions.SphericalHarmonics
  ProjectAinos.SpecialFunctions.HarmonicPolynomial

local notation "E" => MinkowskiModel 3

/-! ### Integrals with values -/

/-- `g` is `μ`-integrable with integral `v`. -/
def HasIntegral (μ : Measure ℝ) (g : ℝ → ℝ) (v : ℝ) : Prop :=
  Integrable g μ ∧ ∫ ξ, g ξ ∂μ = v

namespace HasIntegral

variable {μ : Measure ℝ} {g h : ℝ → ℝ} {v w : ℝ}

theorem add (hg : HasIntegral μ g v) (hh : HasIntegral μ h w) :
    HasIntegral μ (fun ξ => g ξ + h ξ) (v + w) :=
  ⟨hg.1.add hh.1, by rw [integral_add hg.1 hh.1, hg.2, hh.2]⟩

theorem sub (hg : HasIntegral μ g v) (hh : HasIntegral μ h w) :
    HasIntegral μ (fun ξ => g ξ - h ξ) (v - w) :=
  ⟨hg.1.sub hh.1, by rw [integral_sub hg.1 hh.1, hg.2, hh.2]⟩

theorem mul_left (hg : HasIntegral μ g v) (c : ℝ) :
    HasIntegral μ (fun ξ => c * g ξ) (c * v) :=
  ⟨hg.1.const_mul c, by rw [integral_const_mul, hg.2]⟩

theorem congr_ae (hg : HasIntegral μ g v) (e : g =ᵐ[μ] h) : HasIntegral μ h v :=
  ⟨hg.1.congr e, by rw [← integral_congr_ae e, hg.2]⟩

theorem congr_fun (hg : HasIntegral μ g v) (e : ∀ ξ, g ξ = h ξ) : HasIntegral μ h v :=
  hg.congr_ae (Eventually.of_forall e)

end HasIntegral

/-! ### Syntheses converging with two derivatives -/

/-- **A synthesis converging with two derivatives** on `U` for the frequency measure `μ`: near
every point of `U`, on a ball contained in `U`, the integrands are measurable in the frequency
with their first and second derivatives, twice differentiable for almost every frequency, and
dominated with their derivatives by a `μ`-integrable function. -/
structure IsC2Synthesis (U : Set E) (μ : Measure ℝ) (f : ℝ → E → ℝ) : Prop where
  /-- The local integrable bounds. -/
  local_bound : ∀ x ∈ U, ∃ ε > 0, ball x ε ⊆ U ∧ ∃ b : ℝ → ℝ, Integrable b μ ∧
    (∀ y ∈ ball x ε, AEStronglyMeasurable (fun ξ => f ξ y) μ ∧
      AEStronglyMeasurable (fun ξ => fderiv ℝ (f ξ) y) μ ∧
      AEStronglyMeasurable (fun ξ => fderiv ℝ (fderiv ℝ (f ξ)) y) μ) ∧
    ∀ᵐ ξ ∂μ, ∀ y ∈ ball x ε, DifferentiableAt ℝ (f ξ) y ∧
      DifferentiableAt ℝ (fderiv ℝ (f ξ)) y ∧ ‖f ξ y‖ ≤ b ξ ∧ ‖fderiv ℝ (f ξ) y‖ ≤ b ξ ∧
        ‖fderiv ℝ (fderiv ℝ (f ξ)) y‖ ≤ b ξ

namespace IsC2Synthesis

variable {U : Set E} {μ : Measure ℝ} {f : ℝ → E → ℝ}

theorem integrable (hS : IsC2Synthesis U μ f) {y : E} (hy : y ∈ U) :
    Integrable (fun ξ => f ξ y) μ := by
  obtain ⟨ε, hε, -, b, hb, hm, h⟩ := hS.local_bound y hy
  exact hb.mono' (hm y (mem_ball_self hε)).1 (h.mono fun ξ hξ => (hξ y (mem_ball_self hε)).2.2.1)

theorem integrable_fderiv (hS : IsC2Synthesis U μ f) {y : E} (hy : y ∈ U) :
    Integrable (fun ξ => fderiv ℝ (f ξ) y) μ := by
  obtain ⟨ε, hε, -, b, hb, hm, h⟩ := hS.local_bound y hy
  exact hb.mono' (hm y (mem_ball_self hε)).2.1
    (h.mono fun ξ hξ => (hξ y (mem_ball_self hε)).2.2.2.1)

/-- **The derivative of the synthesis is the synthesis of the derivatives.** -/
theorem hasFDerivAt (hS : IsC2Synthesis U μ f) {y : E} (hy : y ∈ U) :
    HasFDerivAt (fun w => ∫ ξ, f ξ w ∂μ) (∫ ξ, fderiv ℝ (f ξ) y ∂μ) y := by
  obtain ⟨ε, hε, -, b, hb, hm, h⟩ := hS.local_bound y hy
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun w ξ => f ξ w)
    (F' := fun w ξ => fderiv ℝ (f ξ) w) (bound := b) (ball_mem_nhds y hε)
    (eventually_of_mem (ball_mem_nhds y hε) fun z hz => (hm z hz).1)
    (hS.integrable hy) (hm y (mem_ball_self hε)).2.1
    (h.mono fun ξ hξ z hz => (hξ z hz).2.2.2.1) hb
    (h.mono fun ξ hξ z hz => (hξ z hz).1.hasFDerivAt)

theorem fderiv_eventuallyEq (hS : IsC2Synthesis U μ f) {y : E} (hy : y ∈ U) :
    fderiv ℝ (fun w => ∫ ξ, f ξ w ∂μ) =ᶠ[𝓝 y] fun z => ∫ ξ, fderiv ℝ (f ξ) z ∂μ := by
  obtain ⟨ε, hε, hεU, -⟩ := hS.local_bound y hy
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz
  exact (hS.hasFDerivAt (hεU hz)).fderiv

/-- **The partial derivatives of the synthesis are the syntheses of the partial derivatives.** -/
theorem part_integral (hS : IsC2Synthesis U μ f) {y : E} (hy : y ∈ U) (j : Fin 4) :
    HasIntegral μ (fun ξ => part (f ξ) j y) (part (fun w => ∫ ξ, f ξ w ∂μ) j y) := by
  have hi := (hS.integrable_fderiv hy).apply_continuousLinearMap (Pi.single j 1 : E)
  refine ⟨hi, ?_⟩
  simp only [part]
  rw [(hS.hasFDerivAt hy).fderiv, ContinuousLinearMap.integral_apply (hS.integrable_fderiv hy)]

/-- The derivatives of the partial derivatives of the synthesis. -/
theorem hasFDerivAt_part (hS : IsC2Synthesis U μ f) {y : E} (hy : y ∈ U) (v : E) :
    Integrable (fun ξ => (ContinuousLinearMap.apply ℝ ℝ v).comp
      (fderiv ℝ (fderiv ℝ (f ξ)) y)) μ ∧
    HasFDerivAt (fun z => fderiv ℝ (fun w => ∫ ξ, f ξ w ∂μ) z v)
      (∫ ξ, (ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ (f ξ)) y) ∂μ) y := by
  obtain ⟨ε, hε, hεU, b, hb, hm, h⟩ := hS.local_bound y hy
  set A : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  set C : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) ℝ A
  have hC (T : E →L[ℝ] E →L[ℝ] ℝ) : C T = A.comp T := rfl
  have hmeas : ∀ z ∈ ball y ε, AEStronglyMeasurable (fun ξ => A.comp
      (fderiv ℝ (fderiv ℝ (f ξ)) z)) μ := fun z hz =>
    C.continuous.comp_aestronglyMeasurable (hm z hz).2.2
  have hbd : ∀ᵐ ξ ∂μ, ∀ z ∈ ball y ε, ‖A.comp (fderiv ℝ (fderiv ℝ (f ξ)) z)‖ ≤ ‖A‖ * b ξ :=
    h.mono fun ξ hξ z hz => (A.opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (hξ z hz).2.2.2.2 (norm_nonneg _))
  have hint : Integrable (fun ξ => A.comp (fderiv ℝ (fderiv ℝ (f ξ)) y)) μ :=
    (hb.const_mul ‖A‖).mono' (hmeas y (mem_ball_self hε))
      (hbd.mono fun ξ hξ => hξ y (mem_ball_self hε))
  refine ⟨hint, ?_⟩
  have hD := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z ξ => fderiv ℝ (f ξ) z v) (F' := fun z ξ => A.comp (fderiv ℝ (fderiv ℝ (f ξ)) z))
    (bound := fun ξ => ‖A‖ * b ξ) (ball_mem_nhds y hε)
    (eventually_of_mem (ball_mem_nhds y hε) fun z hz =>
      A.continuous.comp_aestronglyMeasurable (hm z hz).2.1)
    ((hS.integrable_fderiv hy).apply_continuousLinearMap v) (hmeas y (mem_ball_self hε)) hbd
    (hb.const_mul _) (h.mono fun ξ hξ z hz => A.hasFDerivAt.comp z (hξ z hz).2.1.hasFDerivAt)
  have hev : (fun z => fderiv ℝ (fun w => ∫ ξ, f ξ w ∂μ) z v) =ᶠ[𝓝 y]
      fun z => ∫ ξ, fderiv ℝ (f ξ) z v ∂μ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz
    rw [(hS.hasFDerivAt (hεU hz)).fderiv,
      ContinuousLinearMap.integral_apply (hS.integrable_fderiv (hεU hz))]
  exact hD.congr_of_eventuallyEq hev

theorem secondPartial_eq {g : E → ℝ} {y : E} (hg : DifferentiableAt ℝ (fderiv ℝ g) y)
    (a c : Fin 4) :
    secondPartial g y a c = fderiv ℝ (fderiv ℝ g) y (Pi.single a 1) (Pi.single c 1) := by
  have h := (ContinuousLinearMap.apply ℝ ℝ (Pi.single c 1 : E)).hasFDerivAt.comp y hg.hasFDerivAt
  simp only [secondPartial]
  rw [show (fun z => fderiv ℝ g z (Pi.single c 1)) =
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single c 1 : E)) ∘ fderiv ℝ g from rfl, h.fderiv]
  rfl

/-- **The second partial derivatives of the synthesis are the syntheses of the second partial
derivatives.** -/
theorem secondPartial_integral (hS : IsC2Synthesis U μ f) {y : E} (hy : y ∈ U) (a c : Fin 4) :
    HasIntegral μ (fun ξ => secondPartial (f ξ) y a c)
      (secondPartial (fun w => ∫ ξ, f ξ w ∂μ) y a c) := by
  obtain ⟨hint, hD⟩ := hS.hasFDerivAt_part hy (Pi.single c 1)
  obtain ⟨ε, hε, -, b, hb, hm, h⟩ := hS.local_bound y hy
  have hae : (fun ξ => ((ContinuousLinearMap.apply ℝ ℝ (Pi.single c 1 : E)).comp
      (fderiv ℝ (fderiv ℝ (f ξ)) y)) (Pi.single a 1)) =ᵐ[μ]
      fun ξ => secondPartial (f ξ) y a c :=
    h.mono fun ξ hξ => (secondPartial_eq (hξ y (mem_ball_self hε)).2.1 a c).symm
  refine HasIntegral.congr_ae ⟨hint.apply_continuousLinearMap (Pi.single a 1), ?_⟩ hae
  simp only [secondPartial]
  rw [hD.fderiv, ContinuousLinearMap.integral_apply hint]

/-- **The spatial Laplacian of the synthesis is the synthesis of the spatial Laplacians.** -/
theorem spatialLaplacian_integral (hS : IsC2Synthesis U μ f) {y : E} (hy : y ∈ U) (k : ℝ) :
    HasIntegral μ (fun ξ => spatialLaplacian k (f ξ) y)
      (spatialLaplacian k (fun w => ∫ ξ, f ξ w ∂μ) y) := by
  have s (a : Fin 4) := hS.secondPartial_integral hy a a
  have p (a : Fin 4) := hS.part_integral hy a
  exact ((((s 1).add (s 2)).add (s 3)).mul_left _).sub
    (((((p 1).mul_left (y 1)).add ((p 2).mul_left (y 2))).add ((p 3).mul_left (y 3))).mul_left _)
    |>.congr_fun fun ξ => by simp only [spatialLaplacian]

end IsC2Synthesis

/-! ### The scalar system of a synthesis -/

variable {D : Data} {κ : ℝ} {ρ : ℝ → ℝ} {φ : ℝ → ℝ → ℝ} {Q : ℝ → E → ℝ} {q : ℝ → ℝ}
  {μ : Measure ℝ} {U : Set E}

/-- **The scalar system of a synthesis of separated modes**: with the density contrasts and
covelocities of the modes, the synthesis `u = ∫ φ_ξ Q_ξ dμ` satisfies the scalar system at `x` if
and only if `∫ (φ_ξ″ + 3Hφ_ξ′ − 2kφ_ξ) Q_ξ(x) dμ = 0`. -/
theorem scalarSystemAt_integral_iff (hF : IsModeFamily D φ Q q)
    (hS : IsC2Synthesis U μ fun ξ => separated (φ ξ) (Q ξ)) {x : E} (hxU : x ∈ U)
    (hx : x ∈ domain D) (hm : κ * ρ (x 0) ≠ 0) :
    ScalarSystemAt D κ ρ (fun y => ∫ ξ, separated (φ ξ) (Q ξ) y ∂μ)
        (fun y => ∫ ξ, contrast D κ ρ (φ ξ) (q ξ) (Q ξ) y ∂μ)
        (fun y j => ∫ ξ, covelocity D κ ρ (φ ξ) (Q ξ) y j ∂μ) x ↔
      ∫ ξ, evolutionResidual D (φ ξ) (x 0) * Q ξ x ∂μ = 0 := by
  have ha := (a_pos_of_mem hx).ne'
  obtain ⟨hκ, hρ⟩ := mul_ne_zero_iff.mp hm
  set u : E → ℝ := fun y => ∫ ξ, separated (φ ξ) (Q ξ) y ∂μ
  have s0 : HasIntegral μ (fun ξ => φ ξ (x 0) * Q ξ x) (u x) := ⟨hS.integrable hxU, rfl⟩
  have s1 : HasIntegral μ (fun ξ => deriv (φ ξ) (x 0) * Q ξ x) (part u 0 x) :=
    (hS.part_integral hxU 0).congr_fun fun ξ => (hF.jets hx ξ).1
  have s2 : HasIntegral μ (fun ξ => deriv (deriv (φ ξ)) (x 0) * Q ξ x) (secondPartial u x 0 0) :=
    (hS.secondPartial_integral hxU 0 0).congr_fun fun ξ => (hF.jets hx ξ).2.1
  have sL : HasIntegral μ (fun ξ => -q ξ * (φ ξ (x 0) * Q ξ x)) (spatialLaplacian D.k u x) :=
    (hS.spatialLaplacian_integral hxU D.k).congr_fun fun ξ => (hF.jets hx ξ).2.2.2.2
  have sj (j : Fin 4) (hj : j ≠ 0) : HasIntegral μ
      (fun ξ => deriv (φ ξ) (x 0) * part (Q ξ) j x) (secondPartial u x j 0) :=
    (hS.secondPartial_integral hxU j 0).congr_fun fun ξ => (hF.jets hx ξ).2.2.1 j hj
  have pj (j : Fin 4) (hj : j ≠ 0) : HasIntegral μ
      (fun ξ => φ ξ (x 0) * part (Q ξ) j x) (part u j x) :=
    (hS.part_integral hxU j).congr_fun fun ξ => (hF.jets hx ξ).2.2.2.1 j hj
  -- the evolution equation
  have e1 : HasIntegral μ (fun ξ => evolutionResidual D (φ ξ) (x 0) * Q ξ x)
      (secondPartial u x 0 0 + 3 * hubble D (x 0) * part u 0 x - 2 * D.k * u x) :=
    ((s2.add (s1.mul_left (3 * hubble D (x 0)))).sub (s0.mul_left (2 * D.k))).congr_fun
      fun ξ => by simp only [evolutionResidual]; ring
  -- the density constraint
  have e2 : HasIntegral μ (fun ξ => contrast D κ ρ (φ ξ) (q ξ) (Q ξ) x)
      (2 / (κ * ρ (x 0) * D.a (x 0) ^ 2) * (spatialLaplacian D.k u x -
        3 * hubble D (x 0) * (part u 0 x + hubble D (x 0) * u x) + 3 * D.k * u x)) :=
    (((sL.sub ((s1.add (s0.mul_left (hubble D (x 0)))).mul_left (3 * hubble D (x 0)))).add
      (s0.mul_left (3 * D.k))).mul_left (2 / (κ * ρ (x 0) * D.a (x 0) ^ 2))).congr_fun
      fun ξ => by
        simp only [contrast]
        field_simp
        ring
  -- the momentum constraints
  have e3 (j : Fin 4) (hj : j ≠ 0) : HasIntegral μ
      (fun ξ => covelocity D κ ρ (φ ξ) (Q ξ) x j)
      (-2 / (κ * ρ (x 0) * D.a (x 0)) * (secondPartial u x j 0 + hubble D (x 0) * part u j x)) :=
    (((sj j hj).add ((pj j hj).mul_left (hubble D (x 0)))).mul_left
      (-2 / (κ * ρ (x 0) * D.a (x 0)))).congr_fun fun ξ => by
        simp only [covelocity]
        field_simp
  rw [e1.2]
  unfold ScalarSystemAt
  beta_reduce
  refine ⟨fun h => h.1, fun h => ⟨h, ?_, fun j hj => ?_⟩⟩
  · rw [e2.2]
    field_simp
  · rw [(e3 j hj).2]
    field_simp

/-! ### The zonal standing waves of `H³` -/

/-- The constant solid harmonic `1` of degree zero. -/
def harmonicOne : harmonics 3 0 :=
  ⟨⟨1, MvPolynomial.isHomogeneous_one _ _⟩, by
    rw [harmonics, LinearMap.mem_ker, LinearMap.comp_apply]
    exact laplacian_eq_zero_of_degree_le_one (MvPolynomial.isHomogeneous_one _ _) zero_le_one⟩

/-- The zonal standing wave `sin(ξρ)/(ξ sinh ρ)` of frequency `ξ` on the open chart. -/
def openZonal (ξ : ℝ) : E → ℝ := openHarmonic harmonicOne ξ

theorem openZonal_eq (ξ : ℝ) (x : E) :
    openZonal ξ x = Hyperbolic.zonalProfile ξ (chartCoordinate (-1) x) := by
  simp [openZonal, openHarmonic, chartHarmonic, harmonicOne, Hyperbolic.ambientProfile]

/-- The zonal standing waves are a family of separated modes, indexed by the frequency, with
the eigenvalues `1 + ξ²`. -/
theorem isModeFamily_openZonal {A : ℝ} (hA : 0 < A) {φ : ℝ → ℝ → ℝ}
    (hφ : ∀ ξ, ContDiffOn ℝ ∞ (φ ξ) (openDust A hA).I) :
    IsModeFamily (openDust A hA) φ openZonal fun ξ => 1 + ξ ^ 2 :=
  isModeFamily_open hA (fun _ => 0) (fun _ => harmonicOne) id hφ

/-- The points of the open chart off the time axis. -/
def puncturedDomain (D : Data) : Set E := {x | x ∈ domain D ∧ 0 < x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2}

theorem isOpen_puncturedDomain (D : Data) : IsOpen (puncturedDomain D) :=
  (domain D).isOpen.inter (isOpen_lt continuous_const
    (by fun_prop : Continuous fun x : E => x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2))

/-- The time slice off the time axis. -/
def puncturedSlice (D : Data) (t : ℝ) : Set E := {x | x ∈ puncturedDomain D ∧ x 0 = t}

/-- On the sphere of geodesic radius `ρ > 0` of the open chart the ambient co-ordinate is
`cosh ρ`. -/
theorem exists_puncturedSlice_cosh {A : ℝ} (hA : 0 < A) {t : ℝ} (ht : t ∈ (openDust A hA).I)
    {ρ : ℝ} (hρ : 0 < ρ) : ∃ x ∈ puncturedSlice (openDust A hA) t,
      chartCoordinate (-1) x = Real.cosh ρ := by
  set a := ρ / 2
  have hc : 0 < Real.cosh a := Real.cosh_pos a
  have hs : 0 < Real.sinh a := Real.sinh_pos_iff.mpr (by positivity)
  have hcs := Real.cosh_sq_sub_sinh_sq a
  set r := 2 * Real.sinh a / Real.cosh a
  set x : E := ![t, r, 0, 0]
  have hpsi : psi (-1) x = 1 / Real.cosh a ^ 2 := by
    simp only [psi, x, r]
    simp
    field_simp
    linarith
  refine ⟨x, ⟨⟨⟨by simpa [x] using ht, ?_⟩, ?_⟩, by simp [x]⟩, ?_⟩
  · change 0 < psi (-1) x
    rw [hpsi]; positivity
  · simp [x, r]; positivity
  · rw [chartCoordinate, hpsi, show ρ = 2 * a by simp [a]; ring, Real.cosh_two_mul]
    field_simp
    linarith

/-- **Uniqueness of the zonal densities**: an integrable density of zonal standing waves whose
synthesis vanishes on a time slice off the time axis vanishes almost everywhere. -/
theorem ae_eq_zero_of_integral_openZonal {A : ℝ} (hA : 0 < A) {t : ℝ}
    (ht : t ∈ (openDust A hA).I) {c : ℝ → ℝ} (hc : IntegrableOn c (Ioi 0))
    (h : ∀ x ∈ puncturedSlice (openDust A hA) t, ∫ ξ in Ioi 0, c ξ * openZonal ξ x = 0) :
    c =ᵐ[volume.restrict (Ioi 0)] 0 := by
  refine SineTransform.ae_eq_zero_of_integral_sin_div hc fun ρ hρ => ?_
  obtain ⟨x, hx, hxc⟩ := exists_puncturedSlice_cosh hA ht hρ
  have hsh : Real.sinh ρ ≠ 0 := (Real.sinh_pos_iff.mpr hρ).ne'
  have e : ∫ ξ in Ioi 0, c ξ * openZonal ξ x =
      (∫ ξ in Ioi 0, c ξ * (Real.sin (ξ * ρ) / ξ)) / Real.sinh ρ := by
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
    rw [openZonal_eq, hxc, Hyperbolic.zonalProfile_cosh ξ hρ]
    simp only [(show ξ ≠ 0 from ne_of_gt hξ), ↓reduceIte]
    ring
  have := h x hx
  rw [e, div_eq_zero_iff] at this
  exact this.resolve_right hsh

/-- **The scalar system of a zonal synthesis on the open dust universe**: for a synthesis of the
zonal standing waves with densities smooth in time, converging with two derivatives off the time
axis and with an integrable evolution residual, the scalar system holds on a time slice off the
axis if and only if almost every mode satisfies its evolution equation at that time. -/
theorem open_zonal_scalarSystemAt_slice_iff {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ)
    {φ : ℝ → ℝ → ℝ} (hφ : ∀ ξ, ContDiffOn ℝ ∞ (φ ξ) (openDust A hA).I)
    (hS : IsC2Synthesis (puncturedDomain (openDust A hA)) (volume.restrict (Ioi 0))
      fun ξ => separated (φ ξ) (openZonal ξ)) {t : ℝ} (ht : t ∈ (openDust A hA).I)
    (hR : IntegrableOn (fun ξ => evolutionResidual (openDust A hA) (φ ξ) t) (Ioi 0)) :
    (∀ y ∈ puncturedSlice (openDust A hA) t, ScalarSystemAt (openDust A hA) κ
      (dustDensity κ (6 * A) (openDust A hA).a)
      (fun y => ∫ ξ in Ioi 0, separated (φ ξ) (openZonal ξ) y)
      (fun y => ∫ ξ in Ioi 0, contrast (openDust A hA) κ (dustDensity κ (6 * A) (openDust A hA).a)
        (φ ξ) (1 + ξ ^ 2) (openZonal ξ) y)
      (fun y j => ∫ ξ in Ioi 0, covelocity (openDust A hA) κ
        (dustDensity κ (6 * A) (openDust A hA).a) (φ ξ) (openZonal ξ) y j) y) ↔
      ∀ᵐ ξ ∂(volume.restrict (Ioi 0)), Evolution (openDust A hA) (φ ξ) t := by
  have hm : κ * dustDensity κ (6 * A) (openDust A hA).a t ≠ 0 :=
    (mul_pos hκ (dustDensity_pos hκ (by positivity) ((openDust A hA).a_pos t ht))).ne'
  have hiff (y : E) (hy : y ∈ puncturedSlice (openDust A hA) t) := by
    have h := scalarSystemAt_integral_iff (κ := κ) (ρ := dustDensity κ (6 * A) (openDust A hA).a)
      (isModeFamily_openZonal hA hφ) hS hy.1 hy.1.1 (by rw [hy.2]; exact hm)
    rw [hy.2] at h
    exact h
  constructor
  · intro h
    have hz := ae_eq_zero_of_integral_openZonal hA ht hR fun y hy => (hiff y hy).mp (h y hy)
    filter_upwards [hz] with ξ hξ
    exact hξ
  · intro h y hy
    refine (hiff y hy).mpr ?_
    refine (integral_congr_ae ?_).trans (integral_zero ℝ ℝ)
    filter_upwards [h] with ξ hξ
    rw [show evolutionResidual (openDust A hA) (φ ξ) t = 0 from hξ, zero_mul]

/-! ### A zonal synthesis converging with two derivatives -/

/-- The explicit zonal wave `sin(ξρ)/(ξ sinh ρ)`, `ρ = arcosh s(x)`, as a function of `(ξ, x)`. -/
def zonalWave (p : ℝ × E) : ℝ :=
  Real.sin (p.1 * Real.arcosh (chartCoordinate (-1) p.2)) /
    (p.1 * Real.sinh (Real.arcosh (chartCoordinate (-1) p.2)))

theorem psi_lt_one_of_mem {D : Data} {x : E} (hx : x ∈ puncturedDomain D) (hk : D.k = -1) :
    0 < psi (-1) x ∧ psi (-1) x < 1 := by
  have h1 : 0 < psi D.k x := psi_pos hx.1
  rw [hk] at h1
  refine ⟨h1, ?_⟩
  have := hx.2
  simp only [psi]
  linarith

theorem one_lt_chartCoordinate_of_mem {D : Data} {x : E} (hx : x ∈ puncturedDomain D)
    (hk : D.k = -1) : 1 < chartCoordinate (-1) x := by
  obtain ⟨h0, h1⟩ := psi_lt_one_of_mem hx hk
  have : 2 < 2 / psi (-1) x := by rw [lt_div_iff₀ h0]; linarith
  unfold chartCoordinate; linarith

/-- Off the time axis the zonal standing wave is the explicit zonal wave. -/
theorem openZonal_eq_zonalWave {D : Data} (hk : D.k = -1) {ξ : ℝ} (hξ : 0 < ξ) {x : E}
    (hx : x ∈ puncturedDomain D) : openZonal ξ x = zonalWave (ξ, x) := by
  have hs := one_lt_chartCoordinate_of_mem hx hk
  rw [openZonal_eq]
  conv_lhs => rw [← Real.cosh_arcosh hs.le]
  rw [Hyperbolic.zonalProfile_cosh ξ (Real.arcosh_pos hs)]
  simp only [(show ξ ≠ 0 from ne_of_gt hξ), ↓reduceIte, zonalWave]
  rw [div_div]

theorem contDiffAt_zonalWave {D : Data} (hk : D.k = -1) {p : ℝ × E} (hp : 0 < p.1)
    (hx : p.2 ∈ puncturedDomain D) : ContDiffAt ℝ ∞ zonalWave p := by
  have hψ := (psi_lt_one_of_mem hx hk).1
  have hs1 := one_lt_chartCoordinate_of_mem hx hk
  have hs : ContDiffAt ℝ ∞ (fun q : ℝ × E => chartCoordinate (-1) q.2) p :=
    ((contDiffAt_const.div (contDiff_psi (-1)).contDiffAt hψ.ne').sub contDiffAt_const).comp p
      contDiffAt_snd
  have hρ0 := ContDiffAt.comp (g := Real.arcosh) (f := fun q : ℝ × E => chartCoordinate (-1) q.2)
    p (Real.contDiffAt_arcosh (n := ∞) hs1) hs
  have hρ : ContDiffAt ℝ ∞ (fun q : ℝ × E => Real.arcosh (chartCoordinate (-1) q.2)) p := hρ0
  have hsh : 0 < Real.sinh (Real.arcosh (chartCoordinate (-1) p.2)) :=
    Real.sinh_pos_iff.mpr (Real.arcosh_pos hs1)
  exact (Real.contDiff_sin.contDiffAt.comp p (contDiffAt_fst.mul hρ)).div
    (contDiffAt_fst.mul (Real.contDiff_sinh.contDiffAt.comp p hρ)) (by positivity)

/-- The parameter space of the explicit zonal waves: positive frequencies and points off the
time axis. -/
def zonalParam (D : Data) : Set (ℝ × E) := {p | 0 < p.1 ∧ p.2 ∈ puncturedDomain D}

/-- The first two spatial derivatives of the explicit zonal wave are smooth in `(ξ, x)`. -/
theorem contDiffAt_zonalWave_derivs {D : Data} (hk : D.k = -1) {p : ℝ × E}
    (hp : p ∈ zonalParam D) :
    ContDiffAt ℝ ∞ (fun q : ℝ × E => fderiv ℝ (fun z => zonalWave (q.1, z)) q.2) p ∧
    ContDiffAt ℝ ∞ (fun q : ℝ × E =>
      fderiv ℝ (fun w => fderiv ℝ (fun z => zonalWave (q.1, z)) w) q.2) p := by
  have hU : IsOpen (zonalParam D) :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_puncturedDomain D).preimage continuous_snd)
  have hW : ∀ q ∈ zonalParam D, ContDiffAt ℝ ∞ zonalWave q :=
    fun q hq => contDiffAt_zonalWave hk hq.1 hq.2
  have h1 : ∀ q ∈ zonalParam D,
      ContDiffAt ℝ ∞ (fun r : ℝ × E => fderiv ℝ (fun z => zonalWave (r.1, z)) r.2) q := by
    intro q hq
    refine ContDiffAt.fderiv (f := fun (r : ℝ × E) (z : E) => zonalWave (r.1, z))
      (g := Prod.snd) (m := ∞) (n := ∞) ?_ contDiffAt_snd (by simp)
    exact (hW q hq).comp ((q, q.2)) ((contDiffAt_fst.comp _ contDiffAt_fst).prodMk contDiffAt_snd)
  refine ⟨h1 p hp, ?_⟩
  refine ContDiffAt.fderiv (f := fun (r : ℝ × E) (w : E) =>
    fderiv ℝ (fun z => zonalWave (r.1, z)) w) (g := Prod.snd) (m := ∞) (n := ∞) ?_
    contDiffAt_snd (by simp)
  have hmem : (p.1, p.2) ∈ zonalParam D := hp
  have := (h1 _ hmem).comp ((p, p.2))
    ((contDiffAt_fst.comp _ contDiffAt_fst).prodMk contDiffAt_snd)
  exact this

/-- The density `1` on `[1, 2]`. -/
def unitDensity (ξ : ℝ) : ℝ := Set.indicator (Icc 1 2) (fun _ => 1) ξ

theorem unitDensity_of_mem {ξ : ℝ} (h : ξ ∈ Icc (1 : ℝ) 2) : unitDensity ξ = 1 := by
  simp [unitDensity, h]

theorem unitDensity_of_not_mem {ξ : ℝ} (h : ξ ∉ Icc (1 : ℝ) 2) : unitDensity ξ = 0 := by
  simp [unitDensity, h]

theorem measurable_unitDensity : Measurable unitDensity :=
  measurable_const.indicator measurableSet_Icc

theorem integrable_unitDensity : Integrable unitDensity := by
  have : Integrable (Set.indicator (Icc (1 : ℝ) 2) fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc
  exact this

theorem not_unitDensity_ae_eq_zero : ¬ unitDensity =ᵐ[volume.restrict (Ioi 0)] 0 := by
  intro h
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioi] at h
  have h0 : volume (Icc (1 : ℝ) 2) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with ξ hξ hmem
    have := hξ (show (0 : ℝ) < ξ by linarith [hmem.1])
    rw [unitDensity_of_mem hmem] at this
    exact one_ne_zero this
  simp at h0

/-- The jets of the modes of the unit density off the time axis. -/
theorem unitDensity_jets {A : ℝ} (hA : 0 < A) {ξ : ℝ} (hξ : 0 < ξ) {y : E}
    (hy : y ∈ puncturedDomain (openDust A hA)) :
    separated (fun _ => unitDensity ξ) (openZonal ξ) y = unitDensity ξ * zonalWave (ξ, y) ∧
    fderiv ℝ (separated (fun _ => unitDensity ξ) (openZonal ξ)) y =
      unitDensity ξ • fderiv ℝ (fun z => zonalWave (ξ, z)) y ∧
    fderiv ℝ (fderiv ℝ (separated (fun _ => unitDensity ξ) (openZonal ξ))) y =
      unitDensity ξ • fderiv ℝ (fun w => fderiv ℝ (fun z => zonalWave (ξ, z)) w) y ∧
    DifferentiableAt ℝ (separated (fun _ => unitDensity ξ) (openZonal ξ)) y ∧
    DifferentiableAt ℝ (fderiv ℝ (separated (fun _ => unitDensity ξ) (openZonal ξ))) y := by
  have hk : (openDust A hA).k = -1 := rfl
  set U := puncturedDomain (openDust A hA)
  set f := separated (fun _ => unitDensity ξ) (openZonal ξ)
  have hev (z : E) (hz : z ∈ U) : f =ᶠ[𝓝 z] fun w => unitDensity ξ * zonalWave (ξ, w) := by
    filter_upwards [(isOpen_puncturedDomain _).mem_nhds hz] with w hw
    simp only [f, separated, openZonal_eq_zonalWave hk hξ hw]
  have hpair : ContDiff ℝ ∞ fun w : E => ((ξ, w) : ℝ × E) := contDiff_const.prodMk contDiff_id
  have hZ (z : E) (hz : z ∈ U) : ContDiffAt ℝ ∞ (fun w => zonalWave (ξ, w)) z :=
    (contDiffAt_zonalWave hk hξ hz).comp z hpair.contDiffAt
  have hZ1 (z : E) (hz : z ∈ U) :
      ContDiffAt ℝ ∞ (fun w => fderiv ℝ (fun v => zonalWave (ξ, v)) w) z :=
    (contDiffAt_zonalWave_derivs hk (p := (ξ, z)) ⟨hξ, hz⟩).1.comp z hpair.contDiffAt
  have hd1 (z : E) (hz : z ∈ U) :
      fderiv ℝ f z = unitDensity ξ • fderiv ℝ (fun w => zonalWave (ξ, w)) z := by
    rw [(hev z hz).fderiv_eq, fderiv_const_mul ((hZ z hz).differentiableAt (by simp))]
  have hev1 : fderiv ℝ f =ᶠ[𝓝 y]
      fun z => unitDensity ξ • fderiv ℝ (fun w => zonalWave (ξ, w)) z := by
    filter_upwards [(isOpen_puncturedDomain _).mem_nhds hy] with z hz using hd1 z hz
  refine ⟨(hev y hy).eq_of_nhds, hd1 y hy, ?_, ?_, ?_⟩
  · rw [hev1.fderiv_eq, fderiv_fun_const_smul ((hZ1 y hy).differentiableAt (by simp))]
  · exact (((hZ y hy).differentiableAt (by simp)).const_mul _).congr_of_eventuallyEq (hev y hy)
  · have hd : DifferentiableAt ℝ
        (fun z => unitDensity ξ • fderiv ℝ (fun w => zonalWave (ξ, w)) z) y :=
      ((hZ1 y hy).differentiableAt (by simp)).const_smul (unitDensity ξ)
    exact hd.congr_of_eventuallyEq hev1

/-- **A genuinely continuous synthesis converging with two derivatives**: the zonal standing
waves with the density `1` on `[1, 2]` and constant amplitudes. -/
theorem isC2Synthesis_unitDensity {A : ℝ} (hA : 0 < A) :
    IsC2Synthesis (puncturedDomain (openDust A hA)) (volume.restrict (Ioi 0))
      fun ξ => separated (fun _ => unitDensity ξ) (openZonal ξ) := by
  have hk : (openDust A hA).k = -1 := rfl
  set U := puncturedDomain (openDust A hA)
  refine ⟨fun x hx => ?_⟩
  obtain ⟨ε0, hε0, hball⟩ := Metric.isOpen_iff.mp (isOpen_puncturedDomain _) x hx
  set ε := ε0 / 2
  have hε : 0 < ε := by positivity
  have hcl : closedBall x ε ⊆ U := (closedBall_subset_ball (by simp [ε]; linarith)).trans hball
  set K : Set (ℝ × E) := Icc 1 2 ×ˢ closedBall x ε
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall x ε)
  have hKW : K ⊆ zonalParam (openDust A hA) := fun p hp => ⟨by linarith [hp.1.1], hcl hp.2⟩
  have c0 : ContinuousOn (fun p => ‖zonalWave p‖) K := fun p hp =>
    (contDiffAt_zonalWave hk (hKW hp).1 (hKW hp).2).continuousAt.norm.continuousWithinAt
  have c1 : ContinuousOn (fun p : ℝ × E => ‖fderiv ℝ (fun z => zonalWave (p.1, z)) p.2‖) K :=
    fun p hp => (contDiffAt_zonalWave_derivs hk (hKW hp)).1.continuousAt.norm.continuousWithinAt
  have c2 : ContinuousOn (fun p : ℝ × E =>
      ‖fderiv ℝ (fun w => fderiv ℝ (fun z => zonalWave (p.1, z)) w) p.2‖) K :=
    fun p hp => by
      have hc := (contDiffAt_zonalWave_derivs hk (hKW hp)).2.continuousAt
      have hn : Continuous (fun T : E →L[ℝ] E →L[ℝ] ℝ => ‖T‖) := by
        exact @continuous_norm (E →L[ℝ] E →L[ℝ] ℝ) _
      exact (hn.continuousAt.comp hc).continuousWithinAt
  obtain ⟨B0, hB0⟩ := hK.exists_bound_of_continuousOn c0
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn c1
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn c2
  set B := max (max B0 B1) (max B2 0)
  have hB : 0 ≤ B := le_max_of_le_right (le_max_right _ _)
  refine ⟨ε, hε, ball_subset_closedBall.trans hcl, fun ξ => unitDensity ξ * B,
    (integrable_unitDensity.mul_const B).restrict, fun y hy => ?_, ?_⟩
  · have hyU : y ∈ U := hcl (ball_subset_closedBall hy)
    have hpos : ∀ᵐ ξ ∂(volume.restrict (Ioi (0 : ℝ))), 0 < ξ := ae_restrict_mem measurableSet_Ioi
    have hpair : Continuous fun ξ : ℝ => ((ξ, y) : ℝ × E) := by fun_prop
    have hcont (G : ℝ × E → ℝ) (hG : ∀ ξ, 0 < ξ → ContinuousAt G (ξ, y)) :
        ContinuousOn (fun ξ => G (ξ, y)) (Ioi 0) := fun ξ hξ =>
      ((hG ξ hξ).comp (f := fun ξ' : ℝ => ((ξ', y) : ℝ × E))
        hpair.continuousAt).continuousWithinAt
    refine ⟨?_, ?_, ?_⟩
    · refine AEStronglyMeasurable.congr ?_ (hpos.mono fun ξ hξ =>
        (unitDensity_jets hA hξ hyU).1.symm)
      exact measurable_unitDensity.aestronglyMeasurable.mul
        ((hcont zonalWave fun ξ hξ => (contDiffAt_zonalWave hk hξ hyU).continuousAt
          ).aestronglyMeasurable measurableSet_Ioi)
    · refine AEStronglyMeasurable.congr ?_ (hpos.mono fun ξ hξ =>
        (unitDensity_jets hA hξ hyU).2.1.symm)
      have h1 : ContinuousOn (fun ξ => fderiv ℝ (fun z => zonalWave (ξ, z)) y) (Ioi 0) :=
        fun ξ hξ => ((contDiffAt_zonalWave_derivs hk (p := (ξ, y)) ⟨hξ, hyU⟩).1.continuousAt.comp
          (f := fun ξ' : ℝ => ((ξ', y) : ℝ × E)) hpair.continuousAt).continuousWithinAt
      exact measurable_unitDensity.aestronglyMeasurable.smul
        (h1.aestronglyMeasurable measurableSet_Ioi)
    · refine AEStronglyMeasurable.congr ?_ (hpos.mono fun ξ hξ =>
        (unitDensity_jets hA hξ hyU).2.2.1.symm)
      have h2 : ContinuousOn (fun ξ => fderiv ℝ (fun w => fderiv ℝ (fun z => zonalWave (ξ, z)) w) y)
          (Ioi 0) :=
        fun ξ hξ => ((contDiffAt_zonalWave_derivs hk (p := (ξ, y)) ⟨hξ, hyU⟩).2.continuousAt.comp
          (f := fun ξ' : ℝ => ((ξ', y) : ℝ × E)) hpair.continuousAt).continuousWithinAt
      exact measurable_unitDensity.aestronglyMeasurable.smul
        (h2.aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    intro y hy
    have hyU : y ∈ U := hcl (ball_subset_closedBall hy)
    obtain ⟨e0, e1, e2, d0, d1⟩ := unitDensity_jets hA hξ hyU
    have hyK (hm : ξ ∈ Icc (1 : ℝ) 2) : (ξ, y) ∈ K := ⟨hm, ball_subset_closedBall hy⟩
    refine ⟨d0, d1, ?_, ?_, ?_⟩
    · rw [e0]
      by_cases hm : ξ ∈ Icc (1 : ℝ) 2
      · rw [unitDensity_of_mem hm, one_mul, one_mul]
        have := hB0 (ξ, y) (hyK hm)
        rw [Real.norm_eq_abs, abs_norm] at this
        exact this.trans (le_max_of_le_left (le_max_left _ _))
      · rw [unitDensity_of_not_mem hm]; simp
    · rw [e1]
      by_cases hm : ξ ∈ Icc (1 : ℝ) 2
      · rw [unitDensity_of_mem hm, one_smul, one_mul]
        have := hB1 (ξ, y) (hyK hm)
        rw [Real.norm_eq_abs] at this
        exact ((le_abs_self _).trans this).trans (le_max_of_le_left (le_max_right _ _))
      · rw [unitDensity_of_not_mem hm, zero_smul, zero_mul, norm_zero]
    · rw [e2]
      by_cases hm : ξ ∈ Icc (1 : ℝ) 2
      · rw [unitDensity_of_mem hm, one_smul, one_mul]
        have := hB2 (ξ, y) (hyK hm)
        rw [Real.norm_eq_abs] at this
        exact ((le_abs_self _).trans this).trans (le_max_of_le_right (le_max_left _ _))
      · rw [unitDensity_of_not_mem hm]
        have h0 : (0 : ℝ) • fderiv ℝ (fun w => fderiv ℝ (fun z => zonalWave (ξ, z)) w) y = 0 := by
          ext; simp
        rw [h0, zero_mul, ContinuousLinearMap.opNorm_zero]

/-- **The zonal synthesis of the unit density satisfies the hypotheses of
`open_zonal_scalarSystemAt_slice_iff`** with a density that is not almost everywhere zero. -/
theorem unitDensity_synthesis_hypotheses {A : ℝ} (hA : 0 < A) :
    (∀ ξ, ContDiffOn ℝ ∞ (fun _ : ℝ => unitDensity ξ) (openDust A hA).I) ∧
    IsC2Synthesis (puncturedDomain (openDust A hA)) (volume.restrict (Ioi 0))
      (fun ξ => separated (fun _ => unitDensity ξ) (openZonal ξ)) ∧
    (∀ t, IntegrableOn (fun ξ => evolutionResidual (openDust A hA) (fun _ => unitDensity ξ) t)
      (Ioi 0)) ∧
    ¬ unitDensity =ᵐ[volume.restrict (Ioi 0)] 0 := by
  refine ⟨fun ξ => contDiffOn_const, isC2Synthesis_unitDensity hA, fun t => ?_,
    not_unitDensity_ae_eq_zero⟩
  have e : (fun ξ => evolutionResidual (openDust A hA) (fun _ => unitDensity ξ) t) =
      fun ξ => 2 * unitDensity ξ := by
    funext ξ
    simp only [evolutionResidual, deriv_const', deriv_const]
    change 0 + 3 * hubble (openDust A hA) t * 0 - 2 * (-1) * unitDensity ξ = _
    ring
  rw [e]
  exact (integrable_unitDensity.const_mul 2).integrableOn

end ProjectAinos.GeneralRelativity.CurvedPerturbation
