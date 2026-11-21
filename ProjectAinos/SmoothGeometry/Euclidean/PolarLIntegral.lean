/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# Polar co-ordinates for nonnegative functions

`lintegral_eq_lintegral_sphere_Ioi` is the formula of polar co-ordinates for the integral of a
measurable function `F : E → ℝ≥0∞` against an additive Haar measure `μ`:

`∫⁻ x, F x ∂μ = ∫⁻ n, ∫⁻ r in (0, ∞), r^(dim E − 1) F(r n) dr ∂μ.toSphere`.

The function is not assumed to be a product of an angular and a radial factor, in contrast to
`Sphere.integral_polar_mul`. `lintegral_pi_eq_lintegral_sphere_Ioi` is the same formula for
the Lebesgue measure of `Fin n → ℝ`, with the Euclidean unit sphere of `EuclideanSpace ℝ (Fin n)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace ProjectAinos.SmoothGeometry.Sphere

/-- **Polar co-ordinates** for a measurable function with values in `[0, ∞]`:
`∫⁻ F dμ = ∫⁻ (∫⁻_{r > 0} r^(dim E − 1) F(r n) dr) dσ(n)`. -/
theorem lintegral_eq_lintegral_sphere_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {F : E → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂μ = ∫⁻ n, (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * F (r • (n : E))) ∂μ.toSphere := by
  have h1 : ∫⁻ x, F x ∂μ = ∫⁻ x : ({(0 : E)}ᶜ : Set E), F x ∂(μ.comap (↑)) := by
    rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
  have hG : Measurable fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => F (p.2.1 • (p.1 : E)) :=
    hF.comp ((measurable_subtype_coe.comp measurable_snd).smul
      (measurable_subtype_coe.comp measurable_fst))
  have h2 := (Measure.measurePreserving_homeomorphUnitSphereProd μ).lintegral_comp_emb
    (Homeomorph.measurableEmbedding _)
    (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => F (p.2.1 • (p.1 : E)))
  have h3 : ∫⁻ x : ({(0 : E)}ᶜ : Set E), F x ∂(μ.comap (↑)) =
      ∫⁻ x : ({(0 : E)}ᶜ : Set E), (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
        F (p.2.1 • (p.1 : E))) (homeomorphUnitSphereProd E x) ∂(μ.comap (↑)) := by
    refine lintegral_congr fun x => ?_
    have hx0 : (x : E) ≠ 0 := x.2
    have hx : 0 < ‖(x : E)‖ := norm_pos_iff.mpr hx0
    simp [homeomorphUnitSphereProd, smul_smul, hx.ne']
  rw [h1, h3, h2, lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun n => ?_
  show ∫⁻ y : Ioi (0 : ℝ), F (y.1 • (n : E)) ∂(Measure.volumeIoiPow _) = _
  rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _
      ((measurable_subtype_coe.pow_const _).ennreal_ofReal)
      (g := fun y : Ioi (0 : ℝ) => F (y.1 • (n : E)))
      (hF.comp (measurable_subtype_coe.smul_const _))]
  exact lintegral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * F (r • (n : E)))

/-- **Polar co-ordinates** in `Fin n → ℝ` with the Euclidean unit sphere: for a measurable
`F : (Fin n → ℝ) → [0, ∞]`,
`∫⁻ F = ∫⁻ (∫⁻_{r > 0} r^(n − 1) F(r n̂) dr) dσ(n̂)`. -/
theorem lintegral_pi_eq_lintegral_sphere_Ioi {n : ℕ} [NeZero n] {F : (Fin n → ℝ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ e : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ (n - 1)) * F (r • WithLp.ofLp (e : EuclideanSpace ℝ (Fin n))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  have hpres := PiLp.volume_preserving_ofLp (Fin n)
  rw [← hpres.lintegral_comp hF]
  have h := lintegral_eq_lintegral_sphere_Ioi (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (hF.comp hpres.measurable)
  rw [finrank_euclideanSpace_fin] at h
  exact h

end ProjectAinos.SmoothGeometry.Sphere
