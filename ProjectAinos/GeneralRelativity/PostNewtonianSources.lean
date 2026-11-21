/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Potential.NewtonPotential
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Tactic

/-! # The superpotential and the time derivatives of the potentials

Landau–Lifshitz, §106, the potentials of smooth sources in the second approximation, on
`EuclideanSpace ℝ (Fin 3)` with time as a parameter.

* `integral_norm_mul_coordLaplacian`: **the Green identity of the kernel `‖z‖`**,
  `∫ ‖z‖ Δφ = 8π ∫ K φ` for `C²` functions of compact support (`K = 1/4π‖z‖`), from
  `Δ√(‖z‖² + e²) = (2‖z‖² + 3e²)/(‖z‖² + e²)^{3/2}` and dominated convergence as `e → 0⁺`.
* `superPotential` `χ = ‖·‖ ⋆ f`; `superPotential_coordLaplacian`: `χ[Δf] = 8π N[f]`;
  `coordLaplacian_superPotential`: `Δχ = 8π N[f]`, so for `χ = G ∫ ρ(y)‖x − y‖ dy` and
  `U = 4πG N[ρ]` one has `Δχ = 2U`.
* `contDiff_newtonPotential_param`, `hasDerivAt_newtonPotential_time`: for a density `f(t, x)`
  smooth in `(t, x)` and supported in a fixed compact set of space, `N[f(t)](x)` is jointly smooth
  and `∂_t N[f] = N[∂_t f]`; the same for the superpotential (`hasDerivAt_superPotential_time`).
* `hasDerivAt_newtonPotential_continuity`: with the continuity equation `∂_t ρ + ∇ · (ρv) = 0` as
  a hypothesis, `∂_t N[ρ] = −Σ_k ∂_k N[ρ v_k]`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped Topology ContDiff Real Convolution

namespace ProjectAinos.GeneralRelativity.PostNewtonianSources

open SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The Green identity of the kernel `‖z‖` -/

/-- The regularized norm `√(‖z‖² + e²)`. -/
def regNorm (e : ℝ) (z : E3) : ℝ := √(‖z‖ ^ 2 + e ^ 2)

theorem contDiff_regNorm {e : ℝ} (he : e ≠ 0) : ContDiff ℝ ∞ (regNorm e) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hpos : 0 < ‖z‖ ^ 2 + e ^ 2 := by positivity
  exact ((contDiff_norm_sq ℝ).add contDiff_const).contDiffAt.sqrt hpos.ne'

theorem coordLaplacian_regNorm {e : ℝ} (he : e ≠ 0) (z : E3) :
    coordLaplacian (regNorm e) z =
      (2 * ‖z‖ ^ 2 + 3 * e ^ 2) / ((‖z‖ ^ 2 + e ^ 2) * √(‖z‖ ^ 2 + e ^ 2)) := by
  have hpos : 0 < ‖z‖ ^ 2 + e ^ 2 := by positivity
  have hfun : regNorm e = fun y => (fun s => √(s + e ^ 2)) (‖y‖ ^ 2) := rfl
  have hev : ∀ᶠ s in 𝓝 (‖z‖ ^ 2), HasDerivAt (fun s => √(s + e ^ 2))
      ((fun s => (2 * √(s + e ^ 2))⁻¹) s) s := by
    have : ∀ᶠ s in 𝓝 (‖z‖ ^ 2), 0 < s + e ^ 2 :=
      (continuous_id.add continuous_const).continuousAt.eventually (lt_mem_nhds hpos)
    filter_upwards [this] with s hs
    have h := ((hasDerivAt_id s).add_const (e ^ 2)).sqrt hs.ne'
    simpa [div_eq_mul_inv] using h
  have hu : 0 < √(‖z‖ ^ 2 + e ^ 2) := Real.sqrt_pos.mpr hpos
  have hd : HasDerivAt (fun s => (2 * √(s + e ^ 2))⁻¹)
      (-(4 * ((‖z‖ ^ 2 + e ^ 2) * √(‖z‖ ^ 2 + e ^ 2)))⁻¹) (‖z‖ ^ 2) := by
    have h1 := (((hasDerivAt_id (‖z‖ ^ 2)).add_const (e ^ 2)).sqrt hpos.ne').const_mul 2
    have h2 := h1.inv (by simp only [id]; positivity)
    refine h2.congr_deriv ?_
    simp only [id]
    have hs := Real.sq_sqrt hpos.le
    field_simp
    nlinarith [hs]
  rw [hfun, coordLaplacian_comp_normSq hev hd]
  have hs := Real.sq_sqrt hpos.le
  field_simp
  push_cast
  ring

/-- **The Green identity of the kernel `‖z‖`**: `∫ ‖z‖ Δφ = 8π ∫ K φ` for `C²` functions `φ` of
compact support, the integral form of `Δ‖z‖ = 2/‖z‖` without a point mass. -/
theorem integral_norm_mul_coordLaplacian {φ : E3 → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hcφ : HasCompactSupport φ) :
    ∫ z, ‖z‖ * coordLaplacian φ z = 8 * π * ∫ z, newtonKernel z * φ z := by
  have hΔc : Continuous (coordLaplacian φ) := continuous_coordLaplacian hφ
  have hΔs : HasCompactSupport (coordLaplacian φ) := hasCompactSupport_coordLaplacian hcφ
  -- the regularized identities
  have hreg (e : ℝ) (he : e ≠ 0) : ∫ z, regNorm e z * coordLaplacian φ z =
      ∫ z, (2 * ‖z‖ ^ 2 + 3 * e ^ 2) / ((‖z‖ ^ 2 + e ^ 2) * √(‖z‖ ^ 2 + e ^ 2)) * φ z := by
    rw [integral_mul_coordLaplacian ((contDiff_regNorm he).of_le (by simp)) hφ hcφ]
    simp only [coordLaplacian_regNorm he]
  -- the left side tends to `∫ ‖z‖ Δφ`
  have hL : Tendsto (fun e => ∫ z, regNorm e z * coordLaplacian φ z) (𝓝[>] 0)
      (𝓝 (∫ z, ‖z‖ * coordLaplacian φ z)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => regNorm 1 z * |coordLaplacian φ z|) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun e => (((continuous_norm.pow 2).add continuous_const).sqrt.mul
        hΔc).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with e he
      refine Eventually.of_forall fun z => ?_
      unfold regNorm
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (abs_nonneg _)
      nlinarith [he.1, he.2]
    · exact ((((continuous_norm.pow 2).add continuous_const).sqrt.mul
        hΔc.abs).integrable_of_hasCompactSupport (hΔs.abs.mul_left))
    · refine Eventually.of_forall fun z => ?_
      have hc : Continuous fun e : ℝ => regNorm e z * coordLaplacian φ z := by
        unfold regNorm; fun_prop
      have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa [regNorm, Real.sqrt_sq (norm_nonneg z)] using h
  -- the right side tends to `8π ∫ K φ`
  have hR : Tendsto (fun e => ∫ z, (2 * ‖z‖ ^ 2 + 3 * e ^ 2) /
      ((‖z‖ ^ 2 + e ^ 2) * √(‖z‖ ^ 2 + e ^ 2)) * φ z) (𝓝[>] 0)
      (𝓝 (∫ z, 8 * π * (newtonKernel z * φ z))) := by
    have hint : Integrable fun z => 12 * π * (newtonKernel z * |φ z|) := by
      have h := integrable_newtonKernel_mul (ρ := fun y => |φ (-y)|)
        (hcφ.comp_homeomorph (Homeomorph.neg E3)).abs (hφ.continuous.comp continuous_neg).abs 0
      simpa using h.const_mul (12 * π)
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => 12 * π * (newtonKernel z * |φ z|)) ?_ ?_ hint ?_
    · filter_upwards [self_mem_nhdsWithin] with e (he : 0 < e)
      refine Continuous.aestronglyMeasurable ?_
      refine Continuous.mul (Continuous.div (by fun_prop) (by fun_prop) fun z => ?_) hφ.continuous
      have : 0 < ‖z‖ ^ 2 + e ^ 2 := by positivity
      positivity
    · filter_upwards [self_mem_nhdsWithin] with e (he : 0 < e)
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : E3))] with z hz
      · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
        have hu : 0 < ‖z‖ ^ 2 + e ^ 2 := by positivity
        have hsq : ‖z‖ ≤ √(‖z‖ ^ 2 + e ^ 2) :=
          Real.le_sqrt_of_sq_le (by nlinarith)
        have hsu := Real.sq_sqrt hu.le
        have hr : 0 < √(‖z‖ ^ 2 + e ^ 2) := Real.sqrt_pos.mpr hu
        have hF : (2 * ‖z‖ ^ 2 + 3 * e ^ 2) / ((‖z‖ ^ 2 + e ^ 2) * √(‖z‖ ^ 2 + e ^ 2)) ≤
            3 / ‖z‖ := by
          rw [div_le_div_iff₀ (by positivity) hn]
          nlinarith [mul_le_mul_of_nonneg_left hsq hu.le]
        have hF0 : 0 ≤ (2 * ‖z‖ ^ 2 + 3 * e ^ 2) / ((‖z‖ ^ 2 + e ^ 2) * √(‖z‖ ^ 2 + e ^ 2)) := by
          positivity
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hF0]
        calc _ ≤ 3 / ‖z‖ * |φ z| := mul_le_mul_of_nonneg_right hF (abs_nonneg _)
          _ = 12 * π * (newtonKernel z * |φ z|) := by
            rw [newtonKernel]; field_simp; ring
    · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : E3))] with z hz
      have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hc : ContinuousAt (fun e : ℝ => (2 * ‖z‖ ^ 2 + 3 * e ^ 2) /
          ((‖z‖ ^ 2 + e ^ 2) * √(‖z‖ ^ 2 + e ^ 2)) * φ z) 0 := by
        refine ContinuousAt.mul (ContinuousAt.div (by fun_prop) (by fun_prop) ?_)
          continuousAt_const
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
        positivity
      have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      convert h using 2
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
        newtonKernel, Real.sqrt_sq (norm_nonneg z)]
      field_simp
      ring
  have hRL : Tendsto (fun e => ∫ z, regNorm e z * coordLaplacian φ z) (𝓝[>] 0)
      (𝓝 (∫ z, 8 * π * (newtonKernel z * φ z))) :=
    hR.congr' (eventually_nhdsWithin_of_forall fun e (he : 0 < e) => (hreg e he.ne').symm)
  rw [tendsto_nhds_unique hL hRL, integral_const_mul]

/-! ### The superpotential -/

/-- **The superpotential** `χ[f](x) = ∫ ‖y‖ f(x − y) dy`. -/
def superPotential (f : E3 → ℝ) : E3 → ℝ :=
  (fun y : E3 => ‖y‖) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

theorem superPotential_apply (f : E3 → ℝ) (x : E3) :
    superPotential f x = ∫ y, ‖y‖ * f (x - y) := by
  simp [superPotential, convolution_def]

theorem locallyIntegrable_norm : LocallyIntegrable (fun y : E3 => ‖y‖) :=
  continuous_norm.locallyIntegrable

theorem contDiff_superPotential {f : E3 → ℝ} {n : ℕ∞} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (superPotential f) :=
  hc.contDiff_convolution_right _ locallyIntegrable_norm hf

theorem fderiv_superPotential_apply {f : E3 → ℝ} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 1 f) (x v : E3) :
    fderiv ℝ (superPotential f) x v = superPotential (fun y => fderiv ℝ f y v) x := by
  unfold superPotential
  rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    locallyIntegrable_norm hf x).fderiv]
  exact convolution_precompR_apply _ locallyIntegrable_norm (hc.fderiv ℝ)
    (hf.continuous_fderiv (by norm_num)) x v

/-- **The superpotential of a Laplacian**, `χ[Δf] = 8π N[f]` for `C²` functions of compact
support: the Green identity `integral_norm_mul_coordLaplacian` at a translate. -/
theorem superPotential_coordLaplacian {f : E3 → ℝ} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 2 f) (x : E3) :
    superPotential (coordLaplacian f) x = 8 * π * newtonPotential f x := by
  set φ : E3 → ℝ := fun z => f (x + z) with hφd
  have hφ : ContDiff ℝ 2 φ := hf.comp (contDiff_const.add contDiff_id)
  have hcφ : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.addLeft x)
  have hG := integral_norm_mul_coordLaplacian hφ hcφ
  rw [superPotential_apply, newtonPotential_apply,
    ← integral_neg_eq_self (fun y => ‖y‖ * coordLaplacian f (x - y)),
    ← integral_neg_eq_self (fun y => newtonKernel y * f (x - y))]
  simp only [norm_neg, newtonKernel_neg, sub_neg_eq_add]
  rw [← hG]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hφd, coordLaplacian_comp_add_left]

/-- **The Laplacian of the superpotential**, `Δχ[f] = 8π N[f]`: for `χ = G ∫ ρ(y)‖x − y‖ dy` and
`U = 4πG N[ρ]`, `Δχ = 2U`. -/
theorem coordLaplacian_superPotential {f : E3 → ℝ} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 2 f) (x : E3) :
    coordLaplacian (superPotential f) x = 8 * π * newtonPotential f x := by
  have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hpart (v : E3) : (fun y => fderiv ℝ (superPotential f) y v) =
      superPotential (fun y => fderiv ℝ f y v) :=
    funext fun y => fderiv_superPotential_apply hc h1 y v
  have hterm (v : E3) : fderiv ℝ (fun y => fderiv ℝ (superPotential f) y v) x v =
      superPotential (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y v) x := by
    rw [hpart]
    exact fderiv_superPotential_apply (hc.fderiv_apply (𝕜 := ℝ) v)
      ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const) x v
  have hint (v : E3) : Integrable fun y =>
      ‖y‖ * fderiv ℝ (fun z => fderiv ℝ f z v) (x - y) v := by
    have hcont : Continuous fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y v :=
      (((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
        (by norm_num)).clm_apply continuous_const
    have hcs : HasCompactSupport fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y v :=
      (hc.fderiv_apply (𝕜 := ℝ) v).fderiv_apply (𝕜 := ℝ) v
    have h := hcs.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
      locallyIntegrable_norm hcont x
    simp only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] at h
    exact h
  have hΔ : coordLaplacian (superPotential f) x = ∫ y, ‖y‖ * coordLaplacian f (x - y) := by
    simp only [coordLaplacian, hterm, superPotential_apply]
    rw [← integral_finsetSum _ fun i _ => hint _]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Finset.mul_sum]
  rw [hΔ, ← superPotential_apply, superPotential_coordLaplacian hc hf x]

/-! ### Potentials of moving sources -/

/-- The joint smoothness of a convolution with a parameter, for a density supported in a fixed
compact set of space. -/
theorem contDiff_convolution_param {κ : E3 → ℝ} (hκ : LocallyIntegrable κ) {f : ℝ → E3 → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {k : Set E3} (hk : IsCompact k)
    (hfk : ∀ t x, x ∉ k → f t x = 0) :
    ContDiff ℝ ∞ (fun q : ℝ × E3 => (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f q.1) q.2) := by
  have h := contDiffOn_convolution_right_with_param (ContinuousLinearMap.lsmul ℝ ℝ)
    (s := univ) isOpen_univ hk (fun t x _ hx => hfk t x hx) hκ (n := ⊤)
    (by rw [univ_prod_univ]; exact hf.contDiffOn)
  rw [univ_prod_univ] at h
  exact contDiffOn_univ.mp h

/-- The time derivative of a convolution with a parameter falls on the density. -/
theorem hasDerivAt_convolution_time {κ : E3 → ℝ} (hκ : LocallyIntegrable κ) {f : ℝ → E3 → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {k : Set E3} (hk : IsCompact k)
    (hfk : ∀ t x, x ∉ k → f t x = 0) (t : ℝ) (x : E3) :
    HasDerivAt (fun s => (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f s) x)
      ((κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun y => deriv (fun s => f s y) t) x) t := by
  have h := hasFDerivAt_convolution_right_with_param (ContinuousLinearMap.lsmul ℝ ℝ)
    (s := univ) isOpen_univ hk (fun t x _ hx => hfk t x hx) hκ
    (by rw [univ_prod_univ]; exact (hf.of_le (by simp)).contDiffOn) (t, x) (mem_univ t)
  have hl : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : E3)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have h2 := h.comp_hasDerivAt t hl
  refine h2.congr_deriv ?_
  have hd : Continuous fun y => fderiv ℝ ↿f (t, y) :=
    (hf.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)
  have hcs : HasCompactSupport fun y => fderiv ℝ ↿f (t, y) := by
    refine HasCompactSupport.intro hk fun y hy => ?_
    have hev : (↿f : ℝ × E3 → ℝ) =ᶠ[𝓝 (t, y)] fun _ => 0 := by
      have hO : IsOpen ((univ : Set ℝ) ×ˢ kᶜ) := isOpen_univ.prod hk.isClosed.isOpen_compl
      filter_upwards [hO.mem_nhds ⟨mem_univ t, hy⟩] with q hq
      exact hfk q.1 q.2 hq.2
    rw [hev.fderiv_eq]
    simp
  dsimp only
  rw [convolution_precompR_apply _ hκ hcs hd x ((1 : ℝ), (0 : E3))]
  congr 1
  funext y
  have hdy : HasDerivAt (fun s => f s y) (fderiv ℝ ↿f (t, y) (1, 0)) t := by
    have hfd := ((hf.differentiable (by simp)) (t, y)).hasFDerivAt
    have hl' : HasDerivAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : E3)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    exact hfd.comp_hasDerivAt t hl'
  rw [hdy.deriv]

/-- **`∂_t N[f] = N[∂_t f]`** for a density smooth in `(t, x)` and supported in a fixed compact set
of space. -/
theorem hasDerivAt_newtonPotential_time {f : ℝ → E3 → ℝ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    {k : Set E3} (hk : IsCompact k) (hfk : ∀ t x, x ∉ k → f t x = 0) (t : ℝ) (x : E3) :
    HasDerivAt (fun s => newtonPotential (f s) x)
      (newtonPotential (fun y => deriv (fun s => f s y) t) x) t :=
  hasDerivAt_convolution_time locallyIntegrable_newtonKernel hf hk hfk t x

/-- `∂_t χ[f] = χ[∂_t f]` for the superpotential. -/
theorem hasDerivAt_superPotential_time {f : ℝ → E3 → ℝ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    {k : Set E3} (hk : IsCompact k) (hfk : ∀ t x, x ∉ k → f t x = 0) (t : ℝ) (x : E3) :
    HasDerivAt (fun s => superPotential (f s) x)
      (superPotential (fun y => deriv (fun s => f s y) t) x) t :=
  hasDerivAt_convolution_time locallyIntegrable_norm hf hk hfk t x

/-- The Newton potential of a moving source is jointly smooth in `(t, x)`. -/
theorem contDiff_newtonPotential_param {f : ℝ → E3 → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {k : Set E3} (hk : IsCompact k)
    (hfk : ∀ t x, x ∉ k → f t x = 0) :
    ContDiff ℝ ∞ (fun q : ℝ × E3 => newtonPotential (f q.1) q.2) :=
  contDiff_convolution_param locallyIntegrable_newtonKernel hf hk hfk

/-- The superpotential of a moving source is jointly smooth in `(t, x)`. -/
theorem contDiff_superPotential_param {f : ℝ → E3 → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {k : Set E3} (hk : IsCompact k)
    (hfk : ∀ t x, x ∉ k → f t x = 0) :
    ContDiff ℝ ∞ (fun q : ℝ × E3 => superPotential (f q.1) q.2) :=
  contDiff_convolution_param locallyIntegrable_norm hf hk hfk

/-- **The time derivative of the Newtonian potential from the continuity equation**: if
`∂_t ρ = −Σ_k ∂_k (ρ v_k)` (an explicit hypothesis on the data), then
`∂_t N[ρ] = −Σ_k ∂_k N[ρ v_k]`. -/
theorem hasDerivAt_newtonPotential_continuity {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3}
    (hρ : ContDiff ℝ ∞ (Function.uncurry ρ)) (hv : ∀ t, ContDiff ℝ ∞ (v t)) {k : Set E3}
    (hk : IsCompact k) (hρk : ∀ t x, x ∉ k → ρ t x = 0)
    (hcont : ∀ t y, deriv (fun s => ρ s y) t =
      -∑ j, fderiv ℝ (fun z => ρ t z * v t z j) y (EuclideanSpace.single j 1)) (t : ℝ) (x : E3) :
    HasDerivAt (fun s => newtonPotential (ρ s) x)
      (-∑ j, fderiv ℝ (newtonPotential fun z => ρ t z * v t z j) x (EuclideanSpace.single j 1))
      t := by
  have h := hasDerivAt_newtonPotential_time hρ hk hρk t x
  refine h.congr_deriv ?_
  have hρt : ContDiff ℝ ∞ (ρ t) := hρ.comp (contDiff_const.prodMk contDiff_id)
  have hcj (j : Fin 3) : HasCompactSupport fun z => ρ t z * v t z j :=
    (HasCompactSupport.intro hk fun z hz => hρk t z hz).mul_right
  have hdj (j : Fin 3) : ContDiff ℝ 1 fun z => ρ t z * v t z j :=
    (hρt.mul ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ).contDiff.comp (hv t))).of_le (by simp)
  simp only [funext (hcont t), fderiv_newtonPotential_apply (hcj _) (hdj _)]
  have hint (j : Fin 3) : Integrable fun y => newtonKernel y *
      fderiv ℝ (fun z => ρ t z * v t z j) (x - y) (EuclideanSpace.single j 1) :=
    integrable_newtonKernel_mul ((hcj j).fderiv_apply (𝕜 := ℝ) _)
      (((hdj j).continuous_fderiv (by norm_num)).clm_apply continuous_const) x
  rw [newtonPotential_apply]
  simp only [mul_neg, Finset.mul_sum, integral_neg]
  rw [integral_finsetSum _ fun j _ => hint j]
  simp only [newtonPotential_apply]

end ProjectAinos.GeneralRelativity.PostNewtonianSources
