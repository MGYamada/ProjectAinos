/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.SphericalCompleteness
public import ProjectAinos.SmoothGeometry.Euclidean.SphereIntegral
import Mathlib.Tactic

/-!
# Polar co-ordinates and completeness of the harmonics on `S²`

* `integral_eq_integral_Ioi_sphere`: **polar co-ordinates** in `ℝ³` for an integrable function,
  `∫ F = ∫₀^∞ r² (∫_{S²} F(r u) dσ(u)) dr`, from the measure-preserving homeomorphism
  `ℝ³ ∖ {0} ≃ S² × (0, ∞)` and Fubini's theorem.
* `eq_zero_of_integral_mul_restrict`: **completeness of the spherical harmonics in `C(S²)`**: a
  continuous function on `S²` orthogonal to the restrictions of all harmonic homogeneous
  polynomials vanishes. The pairing with a continuous function is continuous for the uniform norm
  and vanishes on the span of the harmonics, which is dense (`continuousSpace_dense`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open ProjectAinos.SpecialFunctions.HarmonicPolynomial

namespace ProjectAinos.SpecialFunctions.SphericalHarmonics

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Polar co-ordinates** in `ℝ³`: `∫ F = ∫₀^∞ r² ∫_{S²} F(r u) dσ(u) dr` for integrable `F`. -/
theorem integral_eq_integral_Ioi_sphere (F : E3 → ℝ) (hF : Integrable F) :
    ∫ x, F x = ∫ r in Ioi (0 : ℝ), r ^ 2 * ∫ u, F (r • (u : E3)) ∂(surfaceMeasure 3) := by
  set μ : Measure E3 := volume
  have h1 : ∫ x, F x ∂μ = ∫ x : ({(0 : E3)}ᶜ : Set E3), F x ∂(μ.comap (↑)) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl fun x ↦ F x,
      restrict_compl_singleton]
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd μ
  set g : sphere (0 : E3) 1 × Ioi (0 : ℝ) → ℝ := fun p => F (p.2.1 • (p.1 : E3))
  have hg : ∀ x : ({(0 : E3)}ᶜ : Set E3), g (homeomorphUnitSphereProd E3 x) = F x := by
    intro x
    have hx0 : (x : E3) ≠ 0 := x.2
    have hx : 0 < ‖(x : E3)‖ := norm_pos_iff.mpr hx0
    simp [g, smul_smul, hx.ne']
  have h2 : ∫ x : ({(0 : E3)}ᶜ : Set E3), F x ∂(μ.comap (↑)) =
      ∫ p, g p ∂((μ.toSphere).prod (Measure.volumeIoiPow (Module.finrank ℝ E3 - 1))) := by
    rw [← hmp.integral_comp (Homeomorph.measurableEmbedding _) g]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hg x).symm)
  have hint :
      Integrable g ((μ.toSphere).prod (Measure.volumeIoiPow (Module.finrank ℝ E3 - 1))) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
    have : Integrable (F ∘ ((↑) : ({(0 : E3)}ᶜ : Set E3) → E3)) (μ.comap (↑)) :=
      (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hF.integrableOn
    exact this.congr (Filter.Eventually.of_forall fun x => (hg x).symm)
  rw [h1, h2, integral_prod_symm g hint]
  simp only [finrank_euclideanSpace, Fintype.card_fin, Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
      ((measurable_subtype_coe.pow_const _).real_toNNReal),
    integral_subtype_comap measurableSet_Ioi
      (fun a => Real.toNNReal (a ^ (3 - 1)) • ∫ u, F (a • (u : E3)) ∂μ.toSphere)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hr) _), smul_eq_mul]

/-- The pairing with a continuous function on `S²` is continuous for the uniform norm. -/
theorem abs_integral_mul_sub_le (f g h : C(UnitSphere 3, ℝ)) :
    |∫ u, f u * g u ∂(surfaceMeasure 3) - ∫ u, f u * h u ∂(surfaceMeasure 3)| ≤
      ‖f‖ * ‖g - h‖ * (surfaceMeasure 3).real univ := by
  have hi (k : C(UnitSphere 3, ℝ)) : Integrable (fun u => f u * k u) (surfaceMeasure 3) :=
    (f * k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub (hi g) (hi h), ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const (C := ‖f‖ * ‖g - h‖)
    (Filter.Eventually.of_forall fun u => ?_)
  have h2 : ‖g u - h u‖ ≤ ‖g - h‖ := by
    have := (g - h).norm_coe_le_norm u
    rwa [ContinuousMap.sub_apply] at this
  rw [← mul_sub, norm_mul]
  exact mul_le_mul (f.norm_coe_le_norm u) h2 (norm_nonneg _) (norm_nonneg _)

/-- **Completeness of the spherical harmonics in `C(S²)`**: a continuous function on the unit
sphere orthogonal to every harmonic homogeneous polynomial vanishes. -/
theorem eq_zero_of_integral_mul_restrict {f : UnitSphere 3 → ℝ} (hf : Continuous f)
    (h : ∀ (l : ℕ) (p : harmonics 3 l),
      ∫ u, f u * restrict 3 l p.val u ∂(surfaceMeasure 3) = 0) : f = 0 := by
  set F : C(UnitSphere 3, ℝ) := ⟨f, hf⟩
  set Φ : C(UnitSphere 3, ℝ) → ℝ := fun g => ∫ u, F u * g u ∂(surfaceMeasure 3)
  have hΦ : Continuous Φ := by
    rw [Metric.continuous_iff]
    intro g ε hε
    set c := ‖F‖ * (surfaceMeasure 3).real univ + 1
    have hc : 0 < c := by positivity
    refine ⟨ε / c, by positivity, fun h' hh => ?_⟩
    rw [Real.dist_eq]
    refine (abs_integral_mul_sub_le F h' g).trans_lt ?_
    rw [dist_eq_norm] at hh
    calc ‖F‖ * ‖h' - g‖ * (surfaceMeasure 3).real univ
        = ‖h' - g‖ * (‖F‖ * (surfaceMeasure 3).real univ) := by ring
      _ ≤ ‖h' - g‖ * c := mul_le_mul_of_nonneg_left (by simp [c]) (norm_nonneg _)
      _ < ε / c * c := mul_lt_mul_of_pos_right hh hc
      _ = ε := div_mul_cancel₀ ε hc.ne'
  have hzero : ∀ g ∈ (⨆ j, continuousSpace 3 j), Φ g = 0 := by
    intro g hg
    refine Submodule.iSup_induction (motive := fun g => Φ g = 0) _ hg (fun j g hg => ?_) ?_
      (fun g g' hg hg' => ?_)
    · obtain ⟨p, hp, rfl⟩ := hg
      exact h j ⟨p, hp⟩
    · simp [Φ]
    · have hi (k : C(UnitSphere 3, ℝ)) : Integrable (fun u => F u * k u) (surfaceMeasure 3) :=
        (F * k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      simp only [Φ, ContinuousMap.add_apply, mul_add] at hg hg' ⊢
      rw [integral_add (hi g) (hi g'), hg, hg', add_zero]
  have hall : ∀ g, Φ g = 0 := by
    intro g
    have hcl : IsClosed {g : C(UnitSphere 3, ℝ) | Φ g = 0} := isClosed_eq hΦ continuous_const
    have hd := continuousSpace_dense (d := 3) (by norm_num)
    have : (↑(⨆ j, continuousSpace 3 j) : Set C(UnitSphere 3, ℝ)) ⊆
        {g : C(UnitSphere 3, ℝ) | Φ g = 0} := fun g hg => hzero g hg
    exact (hcl.closure_subset_iff.mpr this) (hd.closure_eq.symm ▸ mem_univ g)
  have hsq : ∫ u, f u * f u ∂(surfaceMeasure 3) = 0 := hall F
  have hae : (fun u => f u * f u) =ᵐ[surfaceMeasure 3] 0 := by
    refine (integral_eq_zero_iff_of_nonneg (fun u => mul_self_nonneg _) ?_).mp hsq
    exact (hf.mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have := (Continuous.ae_eq_iff_eq (surfaceMeasure 3) (hf.mul hf) continuous_const).mp hae
  funext u
  have h0 : f u * f u = 0 := congrFun this u
  simpa using h0

end ProjectAinos.SpecialFunctions.SphericalHarmonics
