/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Uniqueness for the Fourier sine transform of an integrable density

The zonal standing waves of hyperbolic space are `sin(ξρ)/(ξ sinh ρ)`; a synthesis
`∫₀^∞ c(ξ) sin(ξρ)/(ξ sinh ρ) dξ` with an integrable density `c` determines `c`.

* `ae_eq_zero_of_fourier_eq_zero`: **the Fourier transform is injective on `L¹(ℝ)`**: testing
  against `𝓕 (𝓕⁻ g)` for a smooth compactly supported `g` moves the transform to `f`.
* `ae_eq_zero_of_integral_sin_div`: **if `∫₀^∞ c(ξ) sin(ξρ)/ξ dξ = 0` for every `ρ > 0`, then
  `c = 0` almost everywhere on `(0, ∞)`**. Differentiation in `ρ` under the integral sign gives
  the cosine transform `∫₀^∞ c(ξ) cos(ξρ) dξ = 0` for `ρ > 0`, by continuity also at `ρ = 0`,
  and it is the Fourier transform of the even extension of `c`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Real
open scoped FourierTransform Topology ContDiff

namespace ProjectAinos.SpecialFunctions.SineTransform

/-- **The Fourier transform is injective on `L¹(ℝ)`.** -/
theorem ae_eq_zero_of_fourier_eq_zero {f : ℝ → ℂ} (hf : Integrable f) (h : ∀ w, 𝓕 f w = 0) :
    f =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable fun g hg hgc => ?_
  set G : ℝ → ℂ := fun x => (g x : ℂ)
  have hG : ContDiff ℝ ∞ G := Complex.ofRealCLM.contDiff.comp hg
  have hGc : HasCompactSupport G := hgc.comp_left Complex.ofReal_zero
  set S : SchwartzMap ℝ ℂ := hGc.toSchwartzMap hG
  set H : SchwartzMap ℝ ℂ := 𝓕⁻ S
  have hFH (x : ℝ) : 𝓕 (H : ℝ → ℂ) x = G x := by
    rw [← SchwartzMap.fourier_coe]
    simp only [H, FourierInvPair.fourier_fourierInv_eq]
    rfl
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞) (μ := volume)
    (ν := volume) (L := innerₗ ℝ) Real.continuous_fourierChar
    (by simp; fun_prop) H.integrable hf
  have e1 : ∫ x, g x • f x = ∫ x, (𝓕 (H : ℝ → ℂ) x) • f x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show g x • f x = 𝓕 (H : ℝ → ℂ) x • f x
    rw [hFH, Complex.real_smul]
    rfl
  rw [e1]
  change ∫ x, (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (H : ℝ → ℂ) x) • f x = 0
  rw [key]
  have h' : ∀ x, VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) f x = 0 := h
  simp [h']

theorem abs_sin_mul_div_le (ξ ρ : ℝ) (hξ : 0 < ξ) (hρ : 0 ≤ ρ) : |sin (ξ * ρ) / ξ| ≤ ρ := by
  rw [abs_div, abs_of_pos hξ, div_le_iff₀ hξ]
  calc |sin (ξ * ρ)| ≤ |ξ * ρ| := abs_sin_le_abs
    _ = ρ * ξ := by rw [abs_of_nonneg (by positivity)]; ring

/-- **Uniqueness for the sine transform**: an integrable density on `(0, ∞)` with
`∫₀^∞ c(ξ) sin(ξρ)/ξ dξ = 0` for every `ρ > 0` vanishes almost everywhere. -/
theorem ae_eq_zero_of_integral_sin_div {c : ℝ → ℝ} (hc : IntegrableOn c (Ioi 0))
    (h : ∀ ρ : ℝ, 0 < ρ → ∫ ξ in Ioi 0, c ξ * (sin (ξ * ρ) / ξ) = 0) :
    c =ᵐ[volume.restrict (Ioi 0)] 0 := by
  set μ := volume.restrict (Ioi (0 : ℝ))
  have hcm : AEStronglyMeasurable c μ := hc.aestronglyMeasurable
  have hpos : ∀ᵐ ξ ∂μ, 0 < ξ := ae_restrict_mem measurableSet_Ioi
  -- the cosine transform vanishes for `ρ > 0`
  have hcos₀ : ∀ ρ : ℝ, 0 < ρ → ∫ ξ in Ioi 0, c ξ * cos (ξ * ρ) = 0 := by
    intro ρ hρ
    have hmeas (r : ℝ) : AEStronglyMeasurable (fun ξ => c ξ * (sin (ξ * r) / ξ)) μ :=
      hcm.mul (by fun_prop : Measurable fun ξ : ℝ => sin (ξ * r) / ξ).aestronglyMeasurable
    have hint : Integrable (fun ξ => c ξ * (sin (ξ * ρ) / ξ)) μ := by
      refine (hc.abs.const_mul ρ).mono' (hmeas ρ) ?_
      filter_upwards [hpos] with ξ hξ
      rw [Real.norm_eq_abs, abs_mul, mul_comm ρ]
      exact mul_le_mul_of_nonneg_left (abs_sin_mul_div_le ξ ρ hξ hρ.le) (abs_nonneg _)
    have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun r ξ => c ξ * (sin (ξ * r) / ξ)) (F' := fun r ξ => c ξ * cos (ξ * r))
      (x₀ := ρ) (bound := fun ξ => |c ξ|) (Ioi_mem_nhds hρ)
      (Eventually.of_forall fun r => hmeas r) hint (hcm.mul (by fun_prop :
        Continuous fun ξ => cos (ξ * ρ)).aestronglyMeasurable) ?_ hc.abs ?_
    · have hz : (fun r => ∫ ξ in Ioi 0, c ξ * (sin (ξ * r) / ξ)) =ᶠ[𝓝 ρ] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hρ] with r hr using h r hr
      exact hd.2.unique ((hasDerivAt_const ρ (0 : ℝ)).congr_of_eventuallyEq hz)
    · refine Eventually.of_forall fun ξ r _ => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
    · filter_upwards [hpos] with ξ hξ
      intro r _
      have := (((hasDerivAt_id r).const_mul ξ).sin.div_const ξ).const_mul (c ξ)
      refine this.congr_deriv ?_
      simp only [id]
      field_simp
  -- by continuity and parity for every `ρ`
  have hcont : Continuous fun ρ : ℝ => ∫ ξ in Ioi 0, c ξ * cos (ξ * ρ) := by
    refine continuous_of_dominated (bound := fun ξ => |c ξ|) (fun ρ => hcm.mul
      (by fun_prop : Continuous fun ξ => cos (ξ * ρ)).aestronglyMeasurable)
      (fun ρ => Eventually.of_forall fun ξ => ?_) hc.abs (Eventually.of_forall fun ξ => by
        fun_prop)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  have hcos : ∀ ρ : ℝ, ∫ ξ in Ioi 0, c ξ * cos (ξ * ρ) = 0 := by
    have h0 : ∫ ξ in Ioi 0, c ξ * cos (ξ * 0) = 0 := by
      have hcl : IsClosed {ρ : ℝ | ∫ ξ in Ioi 0, c ξ * cos (ξ * ρ) = 0} :=
        isClosed_eq hcont continuous_const
      have hsub : Ioi (0 : ℝ) ⊆ {ρ : ℝ | ∫ ξ in Ioi 0, c ξ * cos (ξ * ρ) = 0} :=
        fun ρ hρ => hcos₀ ρ hρ
      exact hcl.closure_subset_iff.mpr hsub (by rw [closure_Ioi]; exact Set.mem_Ici.mpr le_rfl)
    intro ρ
    rcases lt_trichotomy ρ 0 with hρ | rfl | hρ
    · have := hcos₀ (-ρ) (by linarith)
      simpa only [mul_neg, cos_neg] using this
    · exact h0
    · exact hcos₀ ρ hρ
  -- the even extension has vanishing Fourier transform
  set a : ℝ → ℝ := (Ioi (0 : ℝ)).indicator c
  have ha : Integrable a := (integrable_indicator_iff measurableSet_Ioi).mpr hc
  set f : ℝ → ℂ := fun ξ => ((a ξ + a (-ξ) : ℝ) : ℂ)
  have hf : Integrable f := (ha.add (ha.comp_neg)).ofReal
  have hF : ∀ w, 𝓕 f w = 0 := by
    intro w
    have hint1 : Integrable fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) *
        (a v : ℂ) := by
      refine (ha.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall
        fun v => ?_)
      rw [Complex.norm_exp_ofReal_mul_I]
    have hint2 : Integrable fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) *
        (a (-v) : ℂ) := by
      refine (ha.comp_neg.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall
        fun v => ?_)
      rw [Complex.norm_exp_ofReal_mul_I]
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [f, smul_eq_mul, Complex.ofReal_add, mul_add]
    rw [integral_add hint1 hint2]
    have e2 : ∫ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) * (a (-v) : ℂ) =
        ∫ v : ℝ, Complex.exp (↑(2 * π * v * w) * Complex.I) * (a v : ℂ) := by
      rw [← integral_neg_eq_self]
      congr 1; funext v; simp
    have hint3 : Integrable fun v : ℝ => Complex.exp (↑(2 * π * v * w) * Complex.I) *
        (a v : ℂ) := by
      refine (ha.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall
        fun v => ?_)
      rw [Complex.norm_exp_ofReal_mul_I]
    rw [e2, ← integral_add hint1 hint3]
    have e3 : (fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) * (a v : ℂ) +
        Complex.exp (↑(2 * π * v * w) * Complex.I) * (a v : ℂ)) =
        fun v => ((2 * (a v * cos (v * (2 * π * w))) : ℝ) : ℂ) := by
      funext v
      have := Complex.two_cos (↑(2 * π * v * w))
      push_cast at this ⊢
      have e : (-(2 * ↑π * ↑v * ↑w) * Complex.I : ℂ) = -2 * ↑π * ↑v * ↑w * Complex.I := by ring
      rw [e] at this
      rw [show ((v : ℂ) * (2 * ↑π * ↑w)) = 2 * ↑π * ↑v * ↑w by ring]
      linear_combination (-(a v : ℂ)) * this
    rw [e3, integral_complex_ofReal, integral_const_mul]
    have e4 : ∫ v, a v * cos (v * (2 * π * w)) = ∫ v in Ioi 0, c v * cos (v * (2 * π * w)) := by
      rw [← integral_indicator measurableSet_Ioi]
      congr 1; funext v
      simp only [a, indicator]
      split_ifs <;> simp
    rw [e4, hcos, mul_zero, Complex.ofReal_zero]
  -- conclusion
  have hz := ae_eq_zero_of_fourier_eq_zero hf hF
  have hz' : ∀ᵐ ξ ∂μ, f ξ = 0 := ae_restrict_of_ae hz
  filter_upwards [hz', hpos] with ξ hξ hξ0
  have hneg : a (-ξ) = 0 := by simp [a, show ¬ (0 : ℝ) < -ξ by linarith]
  have hpos' : a ξ = c ξ := by simp [a, hξ0]
  simp only [f, hneg, add_zero, hpos', Complex.ofReal_eq_zero] at hξ
  exact hξ

end ProjectAinos.SpecialFunctions.SineTransform
