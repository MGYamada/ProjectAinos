/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Fourier.CompactSynthesis
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Tactic

/-!
# Fourier synthesis of weighted integrable amplitudes

The synthesis `synthesis G (t, x) = ∫ e^{2πi⟪ξ, x⟫} G(t, ξ) dξ` of `CompactSynthesis` for
amplitudes without a cutoff in the frequencies.

* `IsWeightedAmplitude I k G`, **weighted amplitudes of order `k`**: for `j < k` the time
  derivative `∂ₜʲG(·, ξ)` is differentiable at every `t ∈ I` for every `ξ`, the derivatives up
  to order `k` are almost everywhere strongly measurable in `ξ`, and locally uniformly in `t ∈ I`
  `(1 + |ξ|)^m |∂ₜʲG(t, ξ)| ≤ g(ξ)` for `j + m ≤ k` with `g` integrable. The class is closed
  under lowering the order (`IsWeightedAmplitude.mono`), the time derivative
  (`IsWeightedAmplitude.timeDeriv`), linear combinations with measurable coefficients of
  polynomial growth (`IsWeightedAmplitude.linComb`, `IsWeightedAmplitude.mul_left`) — among them
  the bounded coefficients of the projections and the symbols `2πi ξ_γ` of the spatial
  derivatives (`IsWeightedAmplitude.partialSymbol`) — and changes off the set of times
  (`IsWeightedAmplitude.congr`). `IsWeightedAmplitude.const`: an amplitude constant in time with
  `(1 + |ξ|)^k G` integrable, for instance a Schwartz function (`integrable_one_add_norm_pow_mul`).
* `IsWeightedAmplitude.hasFDerivAt_synthesis`: for `k ≥ 1` and `I` open, **the synthesis is
  differentiable** on the slab `{z | z 0 ∈ I}`, by dominated differentiation under the integral
  (`hasFDerivAt_integral_of_dominated_of_fderiv_le`) with the explicit derivative
  `integrandDeriv` of `e^{2πi⟪ξ, x⟫} G(t, ξ)`; `IsWeightedAmplitude.fderiv_synthesis_single`:
  the partial derivative `∂_c` of the synthesis is the synthesis of the symbol
  `partialSymbol c G`.
* `ae_eq_zero_of_fourier_eq_zero`: **the Fourier transform is injective on `L¹`**, from the
  self-adjointness of the transform (`integral_fourier_smul_eq`) and the vanishing of a locally
  integrable function that integrates to zero against all test functions;
  `ae_eq_zero_of_synthesis_eq_zero'`: an integrable amplitude whose synthesis vanishes at one
  time vanishes almost everywhere at that time.
* `fourier_synthesis_ae`: **the converse of the inversion**, if the slice of the synthesis of
  an integrable amplitude is integrable, its transform is the amplitude almost everywhere.
* `exists_bound_of_scale_invariant`: a function of `ξ` that is continuous on `ξ ≠ 0` and
  invariant under positive dilations is bounded (by its maximum on the unit sphere);
  `aestronglyMeasurable_of_continuousOn_ne_zero`: it is measurable.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped FourierTransform RealInnerProductSpace ContDiff Topology ComplexConjugate SchwartzMap

namespace ProjectAinos.SmoothGeometry.Fourier

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E" => MinkowskiModel 3

/-! ### Weighted amplitudes -/

/-- **Weighted amplitudes of order `k`** on the set of times `I`: for `j < k` the `j`-th time
derivative `∂ₜʲG(·, ξ)` has the derivative `∂ₜʲ⁺¹G(t, ξ)` at every `t ∈ I`, the derivatives up
to order `k` are almost everywhere strongly measurable in `ξ`, and locally uniformly in `t ∈ I`
`(1 + |ξ|)^m |∂ₜʲG(t, ξ)| ≤ g(ξ)` for `j + m ≤ k`, with `g` integrable. -/
structure IsWeightedAmplitude (I : Set ℝ) (k : ℕ) (G : ℝ → E3 → ℂ) : Prop where
  /-- The time derivatives below the order are derivatives. -/
  hasDerivAt : ∀ j < k, ∀ t ∈ I, ∀ ξ,
    HasDerivAt (fun s => Fourier.timeDeriv^[j] G s ξ) (Fourier.timeDeriv^[j + 1] G t ξ) t
  /-- The time derivatives up to the order are measurable in the frequency. -/
  measurable : ∀ j ≤ k, ∀ t ∈ I, AEStronglyMeasurable (Fourier.timeDeriv^[j] G t)
  /-- The weighted time derivatives are dominated, locally uniformly in time. -/
  bound : ∀ t₀ ∈ I, ∃ g : E3 → ℝ, Integrable g ∧ ∀ᶠ t in 𝓝 t₀, ∀ ξ, ∀ j m : ℕ, j + m ≤ k →
    (1 + ‖ξ‖) ^ m * ‖Fourier.timeDeriv^[j] G t ξ‖ ≤ g ξ

/-- The symbol of `∂_c`: the time derivative for `c = 0` and the multiplication by `2πi ξ_γ`
for `c = γ + 1`. -/
def partialSymbol (c : Fin 4) (G : ℝ → E3 → ℂ) : ℝ → E3 → ℂ :=
  Fin.cases (motive := fun _ => ℝ → E3 → ℂ) (timeDeriv G)
    (fun γ t ξ => 2 * Real.pi * ξ γ * Complex.I * G t ξ) c

@[simp] theorem partialSymbol_zero (G : ℝ → E3 → ℂ) : partialSymbol 0 G = timeDeriv G := rfl

@[simp] theorem partialSymbol_succ (G : ℝ → E3 → ℂ) (γ : Fin 3) :
    partialSymbol γ.succ G = fun t ξ => 2 * Real.pi * ξ γ * Complex.I * G t ξ := rfl

variable {I : Set ℝ} {k : ℕ} {G : ℝ → E3 → ℂ}

/-- The time derivatives depend only on the amplitude at the times of an open set. -/
theorem iterate_timeDeriv_congr (hI : IsOpen I) {G' : ℝ → E3 → ℂ} (h : ∀ t ∈ I, G' t = G t)
    (j : ℕ) : ∀ t ∈ I, Fourier.timeDeriv^[j] G' t = Fourier.timeDeriv^[j] G t := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro t ht
    funext ξ
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hev : (fun s => Fourier.timeDeriv^[j] G' s ξ) =ᶠ[𝓝 t]
        fun s => Fourier.timeDeriv^[j] G s ξ :=
      eventually_of_mem (hI.mem_nhds ht) fun s hs => congrFun (ih s hs) ξ
    simp only [timeDeriv]
    rw [hev.deriv_eq]

/-- The time derivatives of a linear combination with coefficients depending on the frequency. -/
theorem iterate_timeDeriv_linComb (hI : IsOpen I) {ι : Type*} [Fintype ι] (m : ι → E3 → ℂ)
    (G : ι → ℝ → E3 → ℂ) (j : ℕ)
    (hG : ∀ i, ∀ l < j, ∀ t ∈ I, ∀ ξ,
      HasDerivAt (fun s => Fourier.timeDeriv^[l] (G i) s ξ)
        (Fourier.timeDeriv^[l + 1] (G i) t ξ) t) :
    ∀ t ∈ I, ∀ ξ, Fourier.timeDeriv^[j] (fun t ξ => ∑ i, m i ξ * G i t ξ) t ξ =
      ∑ i, m i ξ * Fourier.timeDeriv^[j] (G i) t ξ := by
  induction j with
  | zero => intro t _ ξ; rfl
  | succ j ih =>
    intro t ht ξ
    have ih' := ih fun i l hl => hG i l (by omega)
    rw [Function.iterate_succ_apply']
    have hev : (fun s => Fourier.timeDeriv^[j] (fun t ξ => ∑ i, m i ξ * G i t ξ) s ξ) =ᶠ[𝓝 t]
        fun s => ∑ i, m i ξ * Fourier.timeDeriv^[j] (G i) s ξ :=
      eventually_of_mem (hI.mem_nhds ht) fun s hs => ih' s hs ξ
    have hd : HasDerivAt (fun s => ∑ i, m i ξ * Fourier.timeDeriv^[j] (G i) s ξ)
        (∑ i, m i ξ * Fourier.timeDeriv^[j + 1] (G i) t ξ) t :=
      HasDerivAt.fun_sum fun i _ => (hG i j (by omega) t ht ξ).const_mul (m i ξ)
    show deriv (fun s => Fourier.timeDeriv^[j] (fun t ξ => ∑ i, m i ξ * G i t ξ) s ξ) t = _
    rw [hev.deriv_eq, hd.deriv]

namespace IsWeightedAmplitude

theorem mono (hG : IsWeightedAmplitude I k G) {k' : ℕ} (h : k' ≤ k) :
    IsWeightedAmplitude I k' G where
  hasDerivAt j hj := hG.hasDerivAt j (lt_of_lt_of_le hj h)
  measurable j hj := hG.measurable j (hj.trans h)
  bound t₀ ht₀ := by
    obtain ⟨g, hg, hb⟩ := hG.bound t₀ ht₀
    exact ⟨g, hg, hb.mono fun t ht ξ j m hjm => ht ξ j m (hjm.trans h)⟩

/-- **The time derivative** lowers the order by one. -/
theorem timeDeriv (hG : IsWeightedAmplitude I (k + 1) G) :
    IsWeightedAmplitude I k (Fourier.timeDeriv G) where
  hasDerivAt j hj t ht ξ := hG.hasDerivAt (j + 1) (by omega) t ht ξ
  measurable j hj t ht := hG.measurable (j + 1) (by omega) t ht
  bound t₀ ht₀ := by
    obtain ⟨g, hg, hb⟩ := hG.bound t₀ ht₀
    exact ⟨g, hg, hb.mono fun t ht ξ j m hjm => ht ξ (j + 1) m (by omega)⟩

/-- The class depends only on the amplitude at the times of an open set. -/
theorem congr (hI : IsOpen I) (hG : IsWeightedAmplitude I k G) {G' : ℝ → E3 → ℂ}
    (h : ∀ t ∈ I, G' t = G t) : IsWeightedAmplitude I k G' where
  hasDerivAt j hj t ht ξ := by
    have e := iterate_timeDeriv_congr hI h
    rw [e (j + 1) t ht]
    refine (hG.hasDerivAt j hj t ht ξ).congr_of_eventuallyEq ?_
    exact eventually_of_mem (hI.mem_nhds ht) fun s hs => congrFun (e j s hs) ξ
  measurable j hj t ht := by
    rw [iterate_timeDeriv_congr hI h j t ht]
    exact hG.measurable j hj t ht
  bound t₀ ht₀ := by
    obtain ⟨g, hg, hb⟩ := hG.bound t₀ ht₀
    refine ⟨g, hg, ?_⟩
    filter_upwards [hb, hI.mem_nhds ht₀] with t ht htI ξ j m hjm
    rw [iterate_timeDeriv_congr hI h j t htI]
    exact ht ξ j m hjm

/-- **Linear combinations** with measurable coefficients of polynomial growth of degree `p`
lower the order by `p`. -/
theorem linComb (hI : IsOpen I) {ι : Type*} [Fintype ι] {p : ℕ} {m : ι → E3 → ℂ}
    {G : ι → ℝ → E3 → ℂ} {C : ℝ} (hm : ∀ i, AEStronglyMeasurable (m i))
    (hmb : ∀ i ξ, ‖m i ξ‖ ≤ C * (1 + ‖ξ‖) ^ p) (hG : ∀ i, IsWeightedAmplitude I (k + p) (G i)) :
    IsWeightedAmplitude I k (fun t ξ => ∑ i, m i ξ * G i t ξ) where
  hasDerivAt j hj t ht ξ := by
    have e := iterate_timeDeriv_linComb hI m G (j + 1)
      (fun i l hl => (hG i).hasDerivAt l (by omega))
    have e0 := iterate_timeDeriv_linComb hI m G j (fun i l hl => (hG i).hasDerivAt l (by omega))
    rw [e t ht ξ]
    refine HasDerivAt.congr_of_eventuallyEq
      (f := fun s => ∑ i, m i ξ * Fourier.timeDeriv^[j] (G i) s ξ) ?_ ?_
    · exact HasDerivAt.fun_sum fun i _ => ((hG i).hasDerivAt j (by omega) t ht ξ).const_mul _
    · exact eventually_of_mem (hI.mem_nhds ht) fun s hs => e0 s hs ξ
  measurable j hj t ht := by
    have e0 := iterate_timeDeriv_linComb hI m G j (fun i l hl => (hG i).hasDerivAt l (by omega))
    have h : AEStronglyMeasurable (fun ξ => ∑ i, m i ξ * Fourier.timeDeriv^[j] (G i) t ξ) :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        (hm i).mul ((hG i).measurable j (by omega) t ht)
    exact h.congr (ae_of_all _ fun ξ => (e0 t ht ξ).symm)
  bound t₀ ht₀ := by
    choose g hg hb using fun i => (hG i).bound t₀ ht₀
    refine ⟨fun ξ => ∑ i, |C| * g i ξ,
      integrable_finsetSum _ fun i _ => (hg i).const_mul _, ?_⟩
    filter_upwards [eventually_all.2 hb, hI.mem_nhds ht₀] with t ht htI ξ j l hjl
    rw [iterate_timeDeriv_linComb hI m G j (fun i l' hl' => (hG i).hasDerivAt l' (by omega)) t
      htI ξ]
    calc (1 + ‖ξ‖) ^ l * ‖∑ i, m i ξ * Fourier.timeDeriv^[j] (G i) t ξ‖
        ≤ (1 + ‖ξ‖) ^ l * ∑ i, ‖m i ξ * Fourier.timeDeriv^[j] (G i) t ξ‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = ∑ i, (1 + ‖ξ‖) ^ l * ‖m i ξ * Fourier.timeDeriv^[j] (G i) t ξ‖ := Finset.mul_sum _ _ _
      _ ≤ ∑ i, |C| * g i ξ := Finset.sum_le_sum fun i _ => ?_
    · have h1 := ht i ξ j (l + p) (by omega)
      have hC : ‖m i ξ‖ ≤ |C| * (1 + ‖ξ‖) ^ p :=
        (hmb i ξ).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      calc (1 + ‖ξ‖) ^ l * ‖m i ξ * Fourier.timeDeriv^[j] (G i) t ξ‖
          = ‖m i ξ‖ * ((1 + ‖ξ‖) ^ l * ‖Fourier.timeDeriv^[j] (G i) t ξ‖) := by
            rw [norm_mul]; ring
        _ ≤ (|C| * (1 + ‖ξ‖) ^ p) * ((1 + ‖ξ‖) ^ l * ‖Fourier.timeDeriv^[j] (G i) t ξ‖) :=
            mul_le_mul_of_nonneg_right hC (by positivity)
        _ = |C| * ((1 + ‖ξ‖) ^ (l + p) * ‖Fourier.timeDeriv^[j] (G i) t ξ‖) := by ring
        _ ≤ |C| * g i ξ := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)

/-- **Multiplication** by a measurable function of polynomial growth of degree `p` lowers the
order by `p`. -/
theorem mul_left (hI : IsOpen I) {p : ℕ} {m : E3 → ℂ} {C : ℝ} (hm : AEStronglyMeasurable m)
    (hmb : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖) ^ p) (hG : IsWeightedAmplitude I (k + p) G) :
    IsWeightedAmplitude I k (fun t ξ => m ξ * G t ξ) := by
  have h := linComb (ι := Unit) hI (m := fun _ => m) (G := fun _ => G) (fun _ => hm)
    (fun _ => hmb) (fun _ => hG)
  simpa using h

end IsWeightedAmplitude

theorem continuous_spaceMultiplier (γ : Fin 3) :
    Continuous fun ξ : E3 => (2 * Real.pi * ξ γ * Complex.I : ℂ) :=
  (contDiff_spaceMultiplier γ).continuous

theorem norm_spaceMultiplier_le (γ : Fin 3) (ξ : E3) :
    ‖(2 * Real.pi * ξ γ * Complex.I : ℂ)‖ ≤ 2 * Real.pi * (1 + ‖ξ‖) ^ 1 := by
  have h : |ξ γ| ≤ ‖ξ‖ := by simpa using PiLp.norm_apply_le ξ γ
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, pow_one]
  have e : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hπ]
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) hπ.le

/-- **The symbols of the partial derivatives** lower the order by one. -/
theorem IsWeightedAmplitude.partialSymbol (hI : IsOpen I) (hG : IsWeightedAmplitude I (k + 1) G)
    (c : Fin 4) :
    IsWeightedAmplitude I k (Fourier.partialSymbol c G) := by
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨γ, rfl⟩
  · exact hG.timeDeriv
  · exact hG.mul_left hI (continuous_spaceMultiplier γ).aestronglyMeasurable
      (norm_spaceMultiplier_le γ)

theorem IsWeightedAmplitude.integrable (hG : IsWeightedAmplitude I k G) {t : ℝ} (ht : t ∈ I) :
    Integrable (G t) := by
  obtain ⟨g, hg, hb⟩ := hG.bound t ht
  refine hg.mono' (hG.measurable 0 (Nat.zero_le _) t ht) (ae_of_all _ fun ξ => ?_)
  simpa using hb.self_of_nhds ξ 0 0 (by simp)

/-- The time derivative of the multiple of an amplitude by a function of the frequency. -/
theorem IsWeightedAmplitude.timeDeriv_mul_left (hG : IsWeightedAmplitude I (k + 1) G) {t : ℝ}
    (ht : t ∈ I) (m : E3 → ℂ) (ξ : E3) :
    Fourier.timeDeriv (fun t ξ => m ξ * G t ξ) t ξ = m ξ * Fourier.timeDeriv G t ξ :=
  ((hG.hasDerivAt 0 (by omega) t ht ξ).const_mul (m ξ)).deriv

/-! ### Differentiation of the synthesis -/

theorem continuous_phase (z : E) : Continuous fun ξ : E3 =>
    Complex.exp (↑(2 * Real.pi * ⟪ξ, spatialPoint z⟫) * Complex.I) := by
  fun_prop

theorem norm_synthesisIntegrand (G : ℝ → E3 → ℂ) (z : E) (ξ : E3) :
    ‖synthesisIntegrand G z ξ‖ = ‖G (z 0) ξ‖ := by
  rw [synthesisIntegrand, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem aestronglyMeasurable_synthesisIntegrand {z : E} (h : AEStronglyMeasurable (G (z 0))) :
    AEStronglyMeasurable (synthesisIntegrand G z) :=
  (continuous_phase z).aestronglyMeasurable.mul h

/-- The integrand of the synthesis of an integrable amplitude is integrable. -/
theorem integrable_synthesisIntegrand {z : E} (h : Integrable (G (z 0))) :
    Integrable (synthesisIntegrand G z) :=
  h.norm.mono' (aestronglyMeasurable_synthesisIntegrand h.aestronglyMeasurable)
    (ae_of_all _ fun ξ => (norm_synthesisIntegrand G z ξ).le)

/-- The coordinate `v ↦ v_c` of space-time as a real-linear map into `ℂ`. -/
def coordCLM (c : Fin 4) : E →L[ℝ] ℂ := (ContinuousLinearMap.proj c).smulRight (1 : ℂ)

@[simp] theorem coordCLM_apply (c : Fin 4) (v : E) : coordCLM c v = (v c : ℂ) := by
  simp [coordCLM]

/-- **The derivative of the integrand** `e^{2πi⟪ξ, x⟫} G(t, ξ)` at `z`:
`v ↦ Σ_c e^{2πi⟪ξ, x⟫} (∂_c-symbol of G)(t, ξ) v_c`. -/
def integrandDeriv (G : ℝ → E3 → ℂ) (z : E) (ξ : E3) : E →L[ℝ] ℂ :=
  ∑ c : Fin 4, synthesisIntegrand (partialSymbol c G) z ξ • coordCLM c

theorem integrandDeriv_apply (G : ℝ → E3 → ℂ) (z : E) (ξ : E3) (v : E) :
    integrandDeriv G z ξ v = ∑ c : Fin 4, synthesisIntegrand (partialSymbol c G) z ξ * v c := by
  simp [integrandDeriv, mul_comm]

theorem integrandDeriv_single (G : ℝ → E3 → ℂ) (z : E) (ξ : E3) (c : Fin 4) :
    integrandDeriv G z ξ (Pi.single c 1) = synthesisIntegrand (partialSymbol c G) z ξ := by
  rw [integrandDeriv_apply, Finset.sum_eq_single c (fun b _ hb => by simp [hb])
    (by simp)]
  simp

/-- The integrand is differentiable in the point of space-time when the amplitude is
differentiable in the time. -/
theorem hasFDerivAt_synthesisIntegrand {z : E} {ξ : E3}
    (hG : HasDerivAt (fun s => G s ξ) (timeDeriv G (z 0) ξ) (z 0)) :
    HasFDerivAt (fun w => synthesisIntegrand G w ξ) (integrandDeriv G z ξ) z := by
  set L : E →L[ℝ] ℂ :=
    ((innerSL ℝ ξ).comp spatialPoint).smulRight ((2 * Real.pi : ℂ) * Complex.I) with hL
  have hLw (w : E) : L w = ↑(2 * Real.pi * ⟪ξ, spatialPoint w⟫) * Complex.I := by
    simp only [hL, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, innerSL_apply_apply, Complex.real_smul]
    push_cast; ring
  have h1 : HasFDerivAt (fun w => Complex.exp (L w)) (Complex.exp (L z) • L) z :=
    L.hasFDerivAt.cexp
  have h2 : HasFDerivAt (fun w : E => G (w 0) ξ)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (timeDeriv G (z 0) ξ)).comp
        (ContinuousLinearMap.proj 0)) z := by
    have hp : HasFDerivAt (fun w : E => w 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0) z :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).hasFDerivAt
    have h := HasFDerivAt.comp z hG.hasFDerivAt hp
    exact h
  have e : (fun w => synthesisIntegrand G w ξ) =
      (fun w => Complex.exp (L w)) * fun w : E => G (w 0) ξ := by
    funext w; simp only [synthesisIntegrand, Pi.mul_apply, hLw]
  rw [e]
  refine (h1.mul h2).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  rw [integrandDeriv_apply, Fin.sum_univ_succ]
  simp [synthesisIntegrand, hLw, inner_spatialPoint, Complex.real_smul, Fin.sum_univ_three]
  ring

theorem IsWeightedAmplitude.aestronglyMeasurable_partialSymbol (hG : IsWeightedAmplitude I 1 G)
    {t : ℝ} (ht : t ∈ I) (c : Fin 4) : AEStronglyMeasurable (Fourier.partialSymbol c G t) := by
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨γ, rfl⟩
  · exact hG.measurable 1 le_rfl t ht
  · exact (continuous_spaceMultiplier γ).aestronglyMeasurable.mul (hG.measurable 0 (by omega) t ht)

theorem aestronglyMeasurable_integrandDeriv (hG : IsWeightedAmplitude I 1 G) {z : E}
    (hz : z ∈ slab I) :
    AEStronglyMeasurable (integrandDeriv G z) := by
  have h : AEStronglyMeasurable fun ξ =>
      ∑ c : Fin 4, synthesisIntegrand (partialSymbol c G) z ξ • coordCLM c :=
    Finset.aestronglyMeasurable_fun_sum _ fun c _ =>
      (aestronglyMeasurable_synthesisIntegrand
        (hG.aestronglyMeasurable_partialSymbol hz c)).smul_const _
  exact h.congr (ae_of_all _ fun ξ => by simp [integrandDeriv])

/-- The bound of the derivative of the integrand. -/
theorem norm_integrandDeriv_le {z : E} {ξ : E3} {b : ℝ}
    (hb : ∀ j m : ℕ, j + m ≤ 1 → (1 + ‖ξ‖) ^ m * ‖Fourier.timeDeriv^[j] G (z 0) ξ‖ ≤ b) :
    ‖integrandDeriv G z ξ‖ ≤ (2 * Real.pi + 1) * (∑ c : Fin 4, ‖coordCLM c‖) * b := by
  have hb0 : 0 ≤ b :=
    (by positivity : (0 : ℝ) ≤ (1 + ‖ξ‖) ^ 0 * ‖Fourier.timeDeriv^[0] G (z 0) ξ‖).trans
      (hb 0 0 (by omega))
  have hπ : 0 < Real.pi := Real.pi_pos
  have hc (c : Fin 4) : ‖synthesisIntegrand (partialSymbol c G) z ξ‖ ≤ (2 * Real.pi + 1) * b := by
    rw [norm_synthesisIntegrand]
    rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨γ, rfl⟩
    · have := hb 1 0 (by omega)
      simp only [pow_zero, one_mul, Function.iterate_one] at this
      simp only [partialSymbol_zero]
      nlinarith
    · have h0 := hb 0 1 (by omega)
      simp only [pow_one, Function.iterate_zero, id_eq] at h0
      simp only [partialSymbol_succ]
      rw [norm_mul]
      have hm := norm_spaceMultiplier_le γ ξ
      calc ‖(2 * Real.pi * ξ γ * Complex.I : ℂ)‖ * ‖G (z 0) ξ‖
          ≤ 2 * Real.pi * (1 + ‖ξ‖) ^ 1 * ‖G (z 0) ξ‖ :=
            mul_le_mul_of_nonneg_right hm (norm_nonneg _)
        _ = 2 * Real.pi * ((1 + ‖ξ‖) * ‖G (z 0) ξ‖) := by ring
        _ ≤ 2 * Real.pi * b := mul_le_mul_of_nonneg_left h0 (by positivity)
        _ ≤ (2 * Real.pi + 1) * b := by nlinarith
  calc ‖integrandDeriv G z ξ‖
      ≤ ∑ c : Fin 4, ‖synthesisIntegrand (partialSymbol c G) z ξ • coordCLM c‖ :=
        norm_sum_le _ _
    _ ≤ ∑ c : Fin 4, (2 * Real.pi + 1) * b * ‖coordCLM c‖ := Finset.sum_le_sum fun c _ =>
        (norm_smul_le (synthesisIntegrand (partialSymbol c G) z ξ) (coordCLM c)).trans
          (mul_le_mul_of_nonneg_right (hc c) (norm_nonneg _))
    _ = (2 * Real.pi + 1) * (∑ c : Fin 4, ‖coordCLM c‖) * b := by
        rw [← Finset.mul_sum]; ring

/-- **The synthesis of a weighted amplitude of order one is differentiable** on the slab, with
the integral of the derivatives of the integrand as derivative. -/
theorem IsWeightedAmplitude.hasFDerivAt_synthesis (hI : IsOpen I) (hG : IsWeightedAmplitude I 1 G)
    {z : E} (hz : z ∈ slab I) : HasFDerivAt (synthesis G) (∫ ξ, integrandDeriv G z ξ) z := by
  obtain ⟨g, hg, hb⟩ := hG.bound (z 0) hz
  have hev : ∀ᶠ w in 𝓝 z, w 0 ∈ I ∧ ∀ ξ, ∀ j m : ℕ, j + m ≤ 1 →
      (1 + ‖ξ‖) ^ m * ‖Fourier.timeDeriv^[j] G (w 0) ξ‖ ≤ g ξ :=
    ((continuous_apply 0).tendsto z).eventually
      (Filter.Eventually.and (hI.mem_nhds hz : ∀ᶠ t in 𝓝 (z 0), t ∈ I) hb)
  have e : synthesis G = fun w => ∫ ξ, synthesisIntegrand G w ξ := funext (synthesis_eq G)
  rw [e]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (bound := fun ξ => (2 * Real.pi + 1) * (∑ c : Fin 4, ‖coordCLM c‖) * g ξ) hev
    (hev.mono fun w hw => aestronglyMeasurable_synthesisIntegrand
      (hG.measurable 0 (by omega) _ hw.1))
    (integrable_synthesisIntegrand (hG.integrable hz))
    (aestronglyMeasurable_integrandDeriv hG hz)
    (ae_of_all _ fun ξ w hw => norm_integrandDeriv_le (hw.2 ξ))
    (hg.const_mul _)
    (ae_of_all _ fun ξ w hw => hasFDerivAt_synthesisIntegrand (hG.hasDerivAt 0 (by omega) _ hw.1 ξ))

theorem IsWeightedAmplitude.integrable_integrandDeriv (hG : IsWeightedAmplitude I 1 G) {z : E}
    (hz : z ∈ slab I) : Integrable (integrandDeriv G z) := by
  obtain ⟨g, hg, hb⟩ := hG.bound (z 0) hz
  exact (hg.const_mul ((2 * Real.pi + 1) * (∑ c : Fin 4, ‖coordCLM c‖))).mono'
    (aestronglyMeasurable_integrandDeriv hG hz)
    (ae_of_all _ fun ξ => norm_integrandDeriv_le (hb.self_of_nhds ξ))

theorem IsWeightedAmplitude.differentiableAt_synthesis (hI : IsOpen I)
    (hG : IsWeightedAmplitude I 1 G) {z : E} (hz : z ∈ slab I) :
    DifferentiableAt ℝ (synthesis G) z :=
  (hG.hasFDerivAt_synthesis hI hz).differentiableAt

/-- **The partial derivatives of the synthesis** are the syntheses of the symbols:
`∂ₜ` of the synthesis is the synthesis of `∂ₜG`, and `∂_γ` that of `2πi ξ_γ G`. -/
theorem IsWeightedAmplitude.fderiv_synthesis_single (hI : IsOpen I)
    (hG : IsWeightedAmplitude I 1 G) {z : E} (hz : z ∈ slab I) (c : Fin 4) :
    fderiv ℝ (synthesis G) z (Pi.single c 1) = synthesis (Fourier.partialSymbol c G) z := by
  rw [(hG.hasFDerivAt_synthesis hI hz).fderiv,
    ContinuousLinearMap.integral_apply (hG.integrable_integrandDeriv hz), synthesis_eq]
  exact integral_congr_ae (ae_of_all _ fun ξ => integrandDeriv_single G z ξ c)

/-! ### Real fields -/

theorem IsWeightedAmplitude.isHermitian_timeDeriv (hI : IsOpen I) (hG : IsWeightedAmplitude I 1 G)
    (hH : IsHermitian I G) : IsHermitian I (Fourier.timeDeriv G) := by
  intro t ht ξ
  have hev : (fun s => G s (-ξ)) =ᶠ[𝓝 t] fun s => conj (G s ξ) :=
    eventually_of_mem (hI.mem_nhds ht) fun s hs => hH s hs ξ
  have h0 : HasDerivAt (fun s => G s ξ) (Fourier.timeDeriv G t ξ) t :=
    hG.hasDerivAt 0 (by omega) t ht ξ
  have hc : HasDerivAt (fun s => conj (G s ξ)) (conj (Fourier.timeDeriv G t ξ)) t := by
    simpa only [starRingEnd_apply] using h0.star
  simp only [Fourier.timeDeriv, hev.deriv_eq]
  exact hc.deriv

theorem IsWeightedAmplitude.isHermitian_partialSymbol (hI : IsOpen I)
    (hG : IsWeightedAmplitude I 1 G) (hH : IsHermitian I G) (c : Fin 4) :
    IsHermitian I (Fourier.partialSymbol c G) := by
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨γ, rfl⟩
  · exact hG.isHermitian_timeDeriv hI hH
  · exact hH.space γ

/-! ### Uniqueness and inversion -/

theorem flip_innerₗ : (innerₗ E3).flip = innerₗ E3 :=
  LinearMap.ext₂ fun x y => real_inner_comm x y

theorem flip_neg_innerₗ : (-innerₗ E3).flip = -innerₗ E3 :=
  LinearMap.ext₂ fun x y => by simp [real_inner_comm x y]

/-- The self-adjointness `∫ 𝓕φ · f = ∫ φ · 𝓕f` of the transform, for `φ` and `f` integrable. -/
theorem integral_fourier_smul_eq {φ f : E3 → ℂ} (hφ : Integrable φ) (hf : Integrable f) :
    ∫ ξ, 𝓕 φ ξ * f ξ = ∫ x, φ x * 𝓕 f x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ E3) (μ := volume)
    (ν := volume) Real.continuous_fourierChar continuous_inner hφ hf
  rw [flip_innerₗ] at h
  simp only [smul_eq_mul] at h
  exact h

/-- The self-adjointness of the inverse transform, for `φ` and `f` integrable. -/
theorem integral_fourierInv_smul_eq {φ f : E3 → ℂ} (hφ : Integrable φ) (hf : Integrable f) :
    ∫ ξ, 𝓕⁻ φ ξ * f ξ = ∫ x, φ x * 𝓕⁻ f x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ E3) (μ := volume)
    (ν := volume) Real.continuous_fourierChar (continuous_inner.neg) hφ hf
  rw [flip_neg_innerₗ] at h
  simp only [smul_eq_mul] at h
  exact h

/-- A test function, as a complex Schwartz function. -/
theorem exists_schwartz_eq {g : E3 → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ ψ : 𝓢(E3, ℂ), ∀ x, ψ x = (g x : ℂ) := by
  have hgc' : HasCompactSupport fun x => (g x : ℂ) := hgc.comp_left Complex.ofReal_zero
  have hg' : ContDiff ℝ ∞ fun x => (g x : ℂ) := Complex.ofRealCLM.contDiff.comp hg
  exact ⟨hgc'.toSchwartzMap hg', fun x => rfl⟩

/-- **The Fourier transform is injective on `L¹`**: an integrable function whose transform
vanishes is zero almost everywhere. -/
theorem ae_eq_zero_of_fourier_eq_zero {f : E3 → ℂ} (hf : Integrable f) (h : ∀ w, 𝓕 f w = 0) :
    ∀ᵐ ξ, f ξ = 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable fun g hg hgc => ?_
  obtain ⟨ψ, hψ⟩ := exists_schwartz_eq hg hgc
  have hφ : 𝓕 (⇑(𝓕⁻ ψ : 𝓢(E3, ℂ))) = ⇑ψ := by
    rw [← SchwartzMap.fourier_coe, FourierInvPair.fourier_fourierInv_eq]
  have e : ∫ x, g x • f x = ∫ x, 𝓕 (⇑(𝓕⁻ ψ : 𝓢(E3, ℂ))) x * f x :=
    integral_congr_ae (ae_of_all _ fun x => by beta_reduce; rw [hφ, hψ, Complex.real_smul])
  rw [e, integral_fourier_smul_eq (𝓕⁻ ψ : 𝓢(E3, ℂ)).integrable hf]
  simp [h]

/-- **Uniqueness of the synthesis**: an integrable amplitude whose synthesis vanishes at all
points of one time is zero almost everywhere at that time. -/
theorem ae_eq_zero_of_synthesis_eq_zero' {t : ℝ} (hi : Integrable (G t))
    (h : ∀ x : E3, synthesis G (spacetimePoint t x) = 0) : ∀ᵐ ξ, G t ξ = 0 := by
  refine ae_eq_zero_of_fourier_eq_zero hi fun w => ?_
  rw [show w = -(-w) from (neg_neg w).symm, ← Real.fourierInv_eq_fourier_neg]
  simpa [synthesis] using h (-w)

/-- **The transform of an integrable slice of the synthesis is the amplitude** almost
everywhere. -/
theorem fourier_synthesis_ae {t : ℝ} (hi : Integrable (G t))
    (hu : Integrable fun x : E3 => synthesis G (spacetimePoint t x)) :
    𝓕 (fun x : E3 => synthesis G (spacetimePoint t x)) =ᵐ[volume] G t := by
  have e : (fun x : E3 => synthesis G (spacetimePoint t x)) = 𝓕⁻ (G t) :=
    funext fun x => synthesis_spacetimePoint G t x
  rw [e] at hu ⊢
  have hcont : Continuous (𝓕 (𝓕⁻ (G t))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hu
  refine ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable hi.locallyIntegrable
    fun g hg hgc => ?_
  obtain ⟨ψ, hψ⟩ := exists_schwartz_eq hg hgc
  have h1 : ∫ x, g x • 𝓕 (𝓕⁻ (G t)) x = ∫ x, ψ x * 𝓕 (𝓕⁻ (G t)) x :=
    integral_congr_ae (ae_of_all _ fun x => by beta_reduce; rw [hψ, Complex.real_smul])
  have h2 : ∫ x, g x • G t x = ∫ x, ψ x * G t x :=
    integral_congr_ae (ae_of_all _ fun x => by beta_reduce; rw [hψ, Complex.real_smul])
  have hFψ : Integrable (𝓕 (⇑ψ)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).integrable
  have hψ' : 𝓕⁻ (𝓕 (⇑ψ)) = ⇑ψ := by
    rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourierInv_coe, FourierPair.fourierInv_fourier_eq]
  rw [h1, h2, ← integral_fourier_smul_eq ψ.integrable hu,
    ← integral_fourierInv_smul_eq hFψ hi, hψ']

/-! ### Coefficients and examples -/

/-- **A dilation-invariant function that is continuous away from the origin is bounded**, by
its maximum on the unit sphere and its value at the origin. -/
theorem exists_bound_of_scale_invariant {f : E3 → ℂ} (hf : ContinuousOn f {ξ | ξ ≠ 0})
    (hs : ∀ c : ℝ, 0 < c → ∀ ξ, f (c • ξ) = f ξ) : ∃ C, ∀ ξ, ‖f ξ‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E3) 1).exists_bound_of_continuousOn
    (hf.mono fun ξ hξ h0 => by simp [h0] at hξ)
  refine ⟨max C ‖f 0‖, fun ξ => ?_⟩
  by_cases h0 : ξ = 0
  · rw [h0]; exact le_max_right _ _
  · have hpos : 0 < ‖ξ‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr h0)
    have hmem : ‖ξ‖⁻¹ • ξ ∈ Metric.sphere (0 : E3) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]
    rw [← hs _ hpos ξ]
    exact (hC _ hmem).trans (le_max_left _ _)

/-- A function continuous away from the origin is measurable. -/
theorem aestronglyMeasurable_of_continuousOn_ne_zero {f : E3 → ℂ}
    (hf : ContinuousOn f {ξ | ξ ≠ 0}) : AEStronglyMeasurable f :=
  (measurable_of_continuousOn_compl_singleton 0
    (by rwa [Set.compl_singleton_eq])).aestronglyMeasurable

theorem timeDeriv_const (F : E3 → ℂ) : timeDeriv (fun _ : ℝ => F) = fun _ _ => 0 := by
  funext t ξ; simp [timeDeriv]

theorem iterate_timeDeriv_const (F : E3 → ℂ) (j : ℕ) :
    Fourier.timeDeriv^[j + 1] (fun _ : ℝ => F) = fun _ _ => 0 := by
  induction j with
  | zero => exact timeDeriv_const F
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    exact timeDeriv_const 0

/-- **Amplitudes constant in time**: a measurable `F` with `(1 + |ξ|)^k F` integrable is a
weighted amplitude of order `k`. -/
theorem IsWeightedAmplitude.const {F : E3 → ℂ} (hF : AEStronglyMeasurable F)
    (hFi : Integrable fun ξ => (1 + ‖ξ‖) ^ k * ‖F ξ‖) : IsWeightedAmplitude I k (fun _ => F) where
  hasDerivAt j _ t _ ξ := by
    rw [iterate_timeDeriv_const]
    rcases j with _ | j
    · exact hasDerivAt_const t (F ξ)
    · rw [iterate_timeDeriv_const]; exact hasDerivAt_const t 0
  measurable j _ t _ := by
    rcases j with _ | j
    · exact hF
    · rw [iterate_timeDeriv_const]; exact aestronglyMeasurable_const
  bound _ _ := ⟨_, hFi, Eventually.of_forall fun t ξ j m hjm => by
    rcases j with _ | j
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by simp) (by omega)) (norm_nonneg _)
    · rw [iterate_timeDeriv_const]; simp only [norm_zero, mul_zero]; positivity⟩

/-- The weighted norms of a Schwartz function are integrable. -/
theorem integrable_one_add_norm_pow_mul (f : 𝓢(E3, ℂ)) (k : ℕ) :
    Integrable fun ξ : E3 => (1 + ‖ξ‖) ^ k * ‖f ξ‖ := by
  have h : Integrable fun ξ : E3 =>
      ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (‖ξ‖ ^ m * ‖f ξ‖) :=
    integrable_finsetSum _ fun m _ => (f.integrable_pow_mul volume m).const_mul _
  refine h.congr (ae_of_all _ fun ξ => ?_)
  simp only
  rw [add_comm (1 : ℝ), add_pow, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

end ProjectAinos.SmoothGeometry.Fourier
