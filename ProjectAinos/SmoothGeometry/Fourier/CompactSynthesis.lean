/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Minkowski.Basic
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic

/-!
# Fourier synthesis of time-dependent amplitudes with a fixed compact spectrum

Space-time points are `z = (t, x¹, x², x³) : MinkowskiModel 3`, frequencies are
`ξ : EuclideanSpace ℝ (Fin 3)`, and the Fourier transform has Mathlib's normalization
`𝓕 f(ξ) = ∫ e^{−2πi⟪x, ξ⟫} f(x) dx`. For an amplitude `G(t, ξ)` the **synthesis** is
`synthesis G (t, x) = 𝓕⁻ (G t) x = ∫ e^{2πi⟪ξ, x⟫} G(t, ξ) dξ` (`synthesis_eq`).

* `hasFDerivAt_integral_of_compact`, `fderiv_integral_apply`: differentiation under the
  integral of `p ↦ ∫ Φ(p, ξ) dμ(ξ)` for `Φ` of class `C¹` on `U × V` (`U` open in a proper
  space) that vanishes for `ξ` outside a fixed compact set; the bound comes from compactness.
* `IsCompactAmplitude I K G`: `G` is smooth on `I × ℝ³` and vanishes for `ξ ∉ K`. The class
  is closed under the time derivative `timeDeriv` (`IsCompactAmplitude.timeDeriv`), under
  multiplication by a function of `ξ` smooth on a neighbourhood of `K`
  (`IsCompactAmplitude.mul_left`) and under linear combinations.
* For such amplitudes, on the slab `{z | z 0 ∈ I}` (`I` open, `K` compact): the synthesis is
  smooth (`contDiffOn_synthesis`, from Mathlib's convolution with a parameter), its time
  derivative is the synthesis of `∂ₜG` (`fderiv_synthesis_time`) and its derivative in `x^γ` is
  the synthesis of `2πi ξ_γ G` (`fderiv_synthesis_space`); the synthesis is linear
  (`synthesis_add`, `synthesis_const_mul`, `synthesis_fintype_sum`) and commutes with linear forms
  whose coefficients depend on the time (`synthesis_linearMap`).
* `IsHermitian I G`, `G(t, −ξ) = conj G(t, ξ)`: then the synthesis is real
  (`conj_synthesis`, `ofReal_re_synthesis`); the condition is preserved by `timeDeriv` and by
  multipliers `m` with `m(−ξ) = conj m(ξ)`.
* `eq_zero_of_synthesis_eq_zero`: **uniqueness**, by the Fourier inversion formula; a
  continuous compactly supported amplitude whose synthesis vanishes at one time is zero.
* `fourier_synthesis_slice`: the slices `x ↦ u(t, x)` are Schwartz functions
  (`synthesis_slice_eq_schwartz`) whose transforms are the amplitudes.
* `synthesis_fourier`: **inversion**, the synthesis of the spatial Fourier transforms of a field
  whose slices are continuous and integrable, with integrable transforms, is the field;
  `fourier_neg_of_real`: the transform of a real slice is Hermitian.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped FourierTransform RealInnerProductSpace ContDiff Topology ComplexConjugate SchwartzMap

namespace ProjectAinos.SmoothGeometry.Fourier

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E" => MinkowskiModel 3

/-! ### Differentiation under an integral with a fixed compact support -/

section Parametric

variable {P V F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {μ : Measure V} [IsFiniteMeasureOnCompacts μ]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Φ : P → V → F} {U : Set P} {K : Set V}

omit [ProperSpace P] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace F] in
theorem hasFDerivAt_fderiv_uncurry (hU : IsOpen U) (hΦ : ContDiffOn ℝ 1 ↿Φ (U ×ˢ univ))
    {p : P} (hp : p ∈ U) (ξ : V) :
    HasFDerivAt (fun q => Φ q ξ) ((fderiv ℝ ↿Φ (p, ξ)).comp (ContinuousLinearMap.inl ℝ P V)) p := by
  have hd : DifferentiableAt ℝ ↿Φ (p, ξ) :=
    (hΦ.differentiableOn one_ne_zero).differentiableAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)
  exact hd.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p ξ)

omit [ProperSpace P] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace F] in
theorem fderiv_uncurry_eq_zero (hU : IsOpen U) (hK : IsCompact K)
    (hΦK : ∀ p ∈ U, ∀ ξ ∉ K, Φ p ξ = 0) {p : P} (hp : p ∈ U) {ξ : V} (hξ : ξ ∉ K) :
    fderiv ℝ ↿Φ (p, ξ) = 0 := by
  refine (hasFDerivAt_zero_of_eventually_const (0 : F) ?_).fderiv
  filter_upwards [(hU.prod hK.isClosed.isOpen_compl).mem_nhds ⟨hp, hξ⟩] with q hq
  exact hΦK q.1 hq.1 q.2 hq.2

omit [ProperSpace P] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace F] in
theorem continuous_of_contDiffOn (hΦ : ContDiffOn ℝ 1 ↿Φ (U ×ˢ univ)) {p : P} (hp : p ∈ U) :
    Continuous (Φ p) :=
  hΦ.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    fun _ => ⟨hp, mem_univ _⟩

omit [ProperSpace P] [FiniteDimensional ℝ V] [CompleteSpace F] in
theorem integrable_of_contDiffOn (hK : IsCompact K) (hΦ : ContDiffOn ℝ 1 ↿Φ (U ×ˢ univ))
    (hΦK : ∀ p ∈ U, ∀ ξ ∉ K, Φ p ξ = 0) {p : P} (hp : p ∈ U) : Integrable (Φ p) μ :=
  (continuous_of_contDiffOn hΦ hp).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hK (hΦK p hp))

omit [CompleteSpace F] in
/-- **Differentiation under the integral** for an integrand of class `C¹` on `U × V` that
vanishes outside a fixed compact set of `V`. -/
theorem hasFDerivAt_integral_of_compact (hU : IsOpen U) (hK : IsCompact K)
    (hΦ : ContDiffOn ℝ 1 ↿Φ (U ×ˢ univ)) (hΦK : ∀ p ∈ U, ∀ ξ ∉ K, Φ p ξ = 0) {p₀ : P}
    (hp₀ : p₀ ∈ U) :
    HasFDerivAt (fun p => ∫ ξ, Φ p ξ ∂μ)
      (∫ ξ, (fderiv ℝ ↿Φ (p₀, ξ)).comp (ContinuousLinearMap.inl ℝ P V) ∂μ) p₀ := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU p₀ hp₀
  have hsub : Metric.closedBall p₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεU
  have hcont : ContinuousOn (fun q : P × V =>
      (fderiv ℝ ↿Φ q).comp (ContinuousLinearMap.inl ℝ P V)) (U ×ˢ univ) :=
    (hΦ.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).clm_comp continuousOn_const
  have hcont' (p : P) (hp : p ∈ U) : Continuous fun ξ : V =>
      (fderiv ℝ ↿Φ (p, ξ)).comp (ContinuousLinearMap.inl ℝ P V) :=
    hcont.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hp, mem_univ _⟩
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ (ε / 2)).prod hK).exists_bound_of_continuousOn
    (hcont.mono (prod_mono hsub (subset_univ _)))
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := K.indicator fun _ => C)
    (Metric.closedBall_mem_nhds p₀ (by linarith))
    (eventually_of_mem (hU.mem_nhds hp₀) fun p hp =>
      (continuous_of_contDiffOn hΦ hp).aestronglyMeasurable)
    (integrable_of_contDiffOn hK hΦ hΦK hp₀) (hcont' p₀ hp₀).aestronglyMeasurable
    (Eventually.of_forall fun ξ p hp => ?_)
    ((integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const hK.measure_lt_top.ne))
    (Eventually.of_forall fun ξ p hp => hasFDerivAt_fderiv_uncurry hU hΦ (hsub hp) ξ)
  by_cases hξ : ξ ∈ K
  · rw [indicator_of_mem hξ]
    exact hC (p, ξ) ⟨hp, hξ⟩
  · rw [indicator_of_notMem hξ, fderiv_uncurry_eq_zero hU hK hΦK (hsub hp) hξ]
    simp

omit [CompleteSpace F] in
/-- The directional derivatives of the integral are the integrals of the directional
derivatives. -/
theorem fderiv_integral_apply (hU : IsOpen U) (hK : IsCompact K)
    (hΦ : ContDiffOn ℝ 1 ↿Φ (U ×ˢ univ)) (hΦK : ∀ p ∈ U, ∀ ξ ∉ K, Φ p ξ = 0) {p₀ : P}
    (hp₀ : p₀ ∈ U) (v : P) :
    fderiv ℝ (fun p => ∫ ξ, Φ p ξ ∂μ) p₀ v = ∫ ξ, fderiv ℝ (fun p => Φ p ξ) p₀ v ∂μ := by
  have hcont : Continuous fun ξ : V =>
      (fderiv ℝ ↿Φ (p₀, ξ)).comp (ContinuousLinearMap.inl ℝ P V) :=
    ((hΦ.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).clm_comp
      continuousOn_const).comp_continuous (continuous_const.prodMk continuous_id)
        fun _ => ⟨hp₀, mem_univ _⟩
  have hint : Integrable (fun ξ : V =>
      (fderiv ℝ ↿Φ (p₀, ξ)).comp (ContinuousLinearMap.inl ℝ P V)) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun ξ hξ => by
      simp [fderiv_uncurry_eq_zero hU hK hΦK hp₀ hξ])
  rw [(hasFDerivAt_integral_of_compact hU hK hΦ hΦK hp₀).fderiv,
    ContinuousLinearMap.integral_apply hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [(hasFDerivAt_fderiv_uncurry hU hΦ hp₀ ξ).fderiv]

omit [CompleteSpace F] in
theorem differentiableAt_integral_of_compact (hU : IsOpen U) (hK : IsCompact K)
    (hΦ : ContDiffOn ℝ 1 ↿Φ (U ×ˢ univ)) (hΦK : ∀ p ∈ U, ∀ ξ ∉ K, Φ p ξ = 0) {p₀ : P}
    (hp₀ : p₀ ∈ U) : DifferentiableAt ℝ (fun p => ∫ ξ, Φ p ξ ∂μ) p₀ :=
  (hasFDerivAt_integral_of_compact (μ := μ) hU hK hΦ hΦK hp₀).differentiableAt

end Parametric

/-! ### Points of space-time -/

/-- The spatial point `(x¹, x², x³)` of `z = (t, x¹, x², x³)`. -/
def spatialPoint : E →L[ℝ] E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun γ : Fin 3 => ContinuousLinearMap.proj γ.succ)

@[simp] theorem spatialPoint_apply (z : E) (γ : Fin 3) : spatialPoint z γ = z γ.succ := rfl

/-- The point `(t, x)` of space-time. -/
def spacetimePoint (t : ℝ) (x : E3) : E := Fin.cons t fun γ => x γ

@[simp] theorem spacetimePoint_zero (t : ℝ) (x : E3) : spacetimePoint t x 0 = t := rfl

@[simp] theorem spacetimePoint_succ (t : ℝ) (x : E3) (γ : Fin 3) :
    spacetimePoint t x γ.succ = x γ := rfl

@[simp] theorem spatialPoint_spacetimePoint (t : ℝ) (x : E3) :
    spatialPoint (spacetimePoint t x) = x := by
  ext γ; simp

theorem spacetimePoint_eq (z : E) : spacetimePoint (z 0) (spatialPoint z) = z := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨γ, rfl⟩ <;> simp

/-- `⟪ξ, x⟫ = Σ ξ_γ x^γ`. -/
theorem inner_spatialPoint (ξ : E3) (z : E) :
    ⟪ξ, spatialPoint z⟫ = ∑ γ, ξ γ * z γ.succ := by
  simp [PiLp.inner_apply, mul_comm]

/-! ### The synthesis -/

/-- **The Fourier synthesis** `u(t, x) = ∫ e^{2πi⟪ξ, x⟫} G(t, ξ) dξ`, the inverse Fourier
transform of `G(t, ·)` at `x`. -/
def synthesis (G : ℝ → E3 → ℂ) (z : E) : ℂ := 𝓕⁻ (G (z 0)) (spatialPoint z)

/-- The integrand `e^{2πi⟪ξ, x⟫} G(t, ξ)` of the synthesis. -/
def synthesisIntegrand (G : ℝ → E3 → ℂ) (z : E) (ξ : E3) : ℂ :=
  Complex.exp (↑(2 * Real.pi * ⟪ξ, spatialPoint z⟫) * Complex.I) * G (z 0) ξ

theorem synthesis_eq (G : ℝ → E3 → ℂ) (z : E) :
    synthesis G z = ∫ ξ, synthesisIntegrand G z ξ := by
  rw [synthesis, Real.fourierInv_eq']
  rfl

/-- The time slab `{z | z 0 ∈ I}`. -/
def slab (I : Set ℝ) : Set E := {z | z 0 ∈ I}

theorem isOpen_slab {I : Set ℝ} (hI : IsOpen I) : IsOpen (slab I) :=
  hI.preimage (continuous_apply 0)

/-- **Amplitudes with a fixed compact spectrum**: `G` is smooth on `I × ℝ³` and `G(t, ξ) = 0`
for `t ∈ I` and `ξ ∉ K`. -/
structure IsCompactAmplitude (I : Set ℝ) (K : Set E3) (G : ℝ → E3 → ℂ) : Prop where
  /-- The amplitude is smooth in `(t, ξ)`. -/
  smooth : ContDiffOn ℝ ∞ (uncurry G) (I ×ˢ univ)
  /-- The amplitude vanishes outside `K`. -/
  support : ∀ t ∈ I, ∀ ξ ∉ K, G t ξ = 0

/-- **Hermitian amplitudes**: `G(t, −ξ) = conj G(t, ξ)`, the amplitudes of real fields. -/
def IsHermitian (I : Set ℝ) (G : ℝ → E3 → ℂ) : Prop :=
  ∀ t ∈ I, ∀ ξ, G t (-ξ) = conj (G t ξ)

/-- The time derivative `∂ₜG(t, ξ)`. -/
def timeDeriv (G : ℝ → E3 → ℂ) (t : ℝ) (ξ : E3) : ℂ := deriv (fun s => G s ξ) t

variable {I : Set ℝ} {K : Set E3} {G G₁ G₂ : ℝ → E3 → ℂ}

namespace IsCompactAmplitude

theorem continuous (hG : IsCompactAmplitude I K G) {t : ℝ} (ht : t ∈ I) : Continuous (G t) :=
  hG.smooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    fun _ => ⟨ht, mem_univ _⟩

theorem integrable (hG : IsCompactAmplitude I K G) (hK : IsCompact K) {t : ℝ} (ht : t ∈ I) :
    Integrable (G t) :=
  (hG.continuous ht).integrable_of_hasCompactSupport (HasCompactSupport.intro hK (hG.support t ht))

theorem hasDerivAt (hG : IsCompactAmplitude I K G) (hI : IsOpen I) {t : ℝ} (ht : t ∈ I)
    (ξ : E3) : HasDerivAt (fun s => G s ξ) (timeDeriv G t ξ) t := by
  have hd : DifferentiableAt ℝ (uncurry G) (t, ξ) :=
    (hG.smooth.differentiableOn (by simp)).differentiableAt
      ((hI.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩)
  have h : DifferentiableAt ℝ (uncurry G ∘ fun s : ℝ => (s, ξ)) t :=
    hd.comp t ((differentiableAt_id).prodMk (differentiableAt_const ξ))
  exact h.hasDerivAt

/-- The time derivative of an amplitude of the class is in the class. -/
theorem timeDeriv (hG : IsCompactAmplitude I K G) (hI : IsOpen I) :
    IsCompactAmplitude I K (timeDeriv G) where
  smooth := by
    have hs := hI.prod (isOpen_univ (X := E3))
    have h1 := ((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp hG.smooth).2.clm_apply
      (contDiffOn_const (c := ((1 : ℝ), (0 : E3))))
    refine h1.congr fun q hq => ?_
    obtain ⟨t, ξ⟩ := q
    have hd : HasFDerivAt (uncurry G) (fderiv ℝ (uncurry G) (t, ξ)) (t, ξ) :=
      ((hG.smooth.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hq)).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => (s, ξ)) ((1 : ℝ), (0 : E3)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t ξ)
    exact (hd.comp_hasDerivAt t hl).deriv
  support t ht ξ hξ := by
    have hev : (fun s => G s ξ) =ᶠ[𝓝 t] fun _ => 0 :=
      eventually_of_mem (hI.mem_nhds ht) fun s hs => hG.support s hs ξ hξ
    simp only [ProjectAinos.SmoothGeometry.Fourier.timeDeriv, hev.deriv_eq, deriv_const]

/-- Multiplication by a function of `ξ` that is smooth on a neighbourhood of `K`. -/
theorem mul_left (hG : IsCompactAmplitude I K G) (hK : IsCompact K) {m : E3 → ℂ} {W : Set E3}
    (hW : IsOpen W) (hKW : K ⊆ W) (hm : ContDiffOn ℝ ∞ m W) :
    IsCompactAmplitude I K (fun t ξ => m ξ * G t ξ) where
  smooth := by
    refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
    by_cases hq2 : q.2 ∈ W
    · refine ⟨univ ×ˢ W, isOpen_univ.prod hW, ⟨mem_univ _, hq2⟩, ?_⟩
      have h1 : ContDiffOn ℝ ∞ (fun q : ℝ × E3 => m q.2) ((I ×ˢ univ) ∩ (univ ×ˢ W)) :=
        hm.comp contDiff_snd.contDiffOn fun q hq => hq.2.2
      exact h1.mul (hG.smooth.mono inter_subset_left)
    · refine ⟨univ ×ˢ Kᶜ, isOpen_univ.prod hK.isClosed.isOpen_compl,
        ⟨mem_univ _, fun h => hq2 (hKW h)⟩, ?_⟩
      refine contDiffOn_const (c := (0 : ℂ)).congr fun q hq => ?_
      rw [show q = (q.1, q.2) from rfl, uncurry_apply_pair, hG.support q.1 hq.1.1 q.2 hq.2.2,
        mul_zero]
  support t ht ξ hξ := by simp [hG.support t ht ξ hξ]

theorem mul_smooth (hG : IsCompactAmplitude I K G) {f : ℝ → E3 → ℂ}
    (hf : ContDiffOn ℝ ∞ (uncurry f) (I ×ˢ univ)) :
    IsCompactAmplitude I K (fun t ξ => f t ξ * G t ξ) where
  smooth := hf.mul hG.smooth
  support t ht ξ hξ := by simp [hG.support t ht ξ hξ]

theorem add (hG₁ : IsCompactAmplitude I K G₁) (hG₂ : IsCompactAmplitude I K G₂) :
    IsCompactAmplitude I K (fun t ξ => G₁ t ξ + G₂ t ξ) where
  smooth := hG₁.smooth.add hG₂.smooth
  support t ht ξ hξ := by simp [hG₁.support t ht ξ hξ, hG₂.support t ht ξ hξ]

theorem const_mul (hG : IsCompactAmplitude I K G) (c : ℂ) :
    IsCompactAmplitude I K (fun t ξ => c * G t ξ) where
  smooth := contDiffOn_const.mul hG.smooth
  support t ht ξ hξ := by simp [hG.support t ht ξ hξ]

theorem zero : IsCompactAmplitude I K fun _ _ => 0 where
  smooth := contDiffOn_const
  support _ _ _ _ := rfl

theorem sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → E3 → ℂ}
    (hG : ∀ i ∈ s, IsCompactAmplitude I K (G i)) :
    IsCompactAmplitude I K (fun t ξ => ∑ i ∈ s, G i t ξ) where
  smooth := by
    have h := ContDiffOn.sum (s := s) (t := I ×ˢ univ) (n := ∞) (f := fun i q => uncurry (G i) q)
      fun i hi => (hG i hi).smooth
    refine h.congr fun q _ => ?_
    simp [uncurry]
  support t ht ξ hξ := Finset.sum_eq_zero fun i hi => (hG i hi).support t ht ξ hξ

end IsCompactAmplitude

theorem timeDeriv_mul_left (hG : IsCompactAmplitude I K G) (hI : IsOpen I) {t : ℝ} (ht : t ∈ I)
    (m : E3 → ℂ) (ξ : E3) :
    timeDeriv (fun t ξ => m ξ * G t ξ) t ξ = m ξ * timeDeriv G t ξ :=
  ((hG.hasDerivAt hI ht ξ).const_mul (m ξ)).deriv

/-! #### The integrand -/

theorem contDiff_phase : ContDiff ℝ ∞ fun q : E × E3 =>
    Complex.exp (↑(2 * Real.pi * ⟪q.2, spatialPoint q.1⟫) * Complex.I) := by
  have h : ContDiff ℝ ∞ fun q : E × E3 => ⟪q.2, spatialPoint q.1⟫ :=
    ContDiff.inner ℝ contDiff_snd (spatialPoint.contDiff.comp contDiff_fst)
  exact Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul h)).mul contDiff_const)

theorem IsCompactAmplitude.contDiffOn_integrand (hG : IsCompactAmplitude I K G) :
    ContDiffOn ℝ ∞ ↿(synthesisIntegrand G) (slab I ×ˢ univ) := by
  have h2 : ContDiffOn ℝ ∞ (uncurry G ∘ fun q : E × E3 => (q.1 0, q.2)) (slab I ×ˢ univ) :=
    hG.smooth.comp (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).prodMap
      (ContinuousLinearMap.id ℝ E3)).contDiff.contDiffOn)
      fun q (hq : q ∈ slab I ×ˢ univ) => ⟨hq.1, mem_univ _⟩
  exact contDiff_phase.contDiffOn.mul h2

theorem IsCompactAmplitude.integrand_eq_zero (hG : IsCompactAmplitude I K G) {z : E}
    (hz : z ∈ slab I) {ξ : E3} (hξ : ξ ∉ K) : synthesisIntegrand G z ξ = 0 := by
  simp [synthesisIntegrand, hG.support (z 0) hz ξ hξ]

theorem IsCompactAmplitude.integrable_integrand (hG : IsCompactAmplitude I K G)
    (hK : IsCompact K) {z : E} (hz : z ∈ slab I) : Integrable (synthesisIntegrand G z) :=
  integrable_of_contDiffOn (U := slab I) hK (hG.contDiffOn_integrand.of_le (by simp))
    (fun _ hp _ hξ => hG.integrand_eq_zero hp hξ) hz

/-! #### Smoothness and derivatives -/

/-- **The synthesis is smooth** on the slab. -/
theorem contDiffOn_synthesis (hI : IsOpen I) (hK : IsCompact K) (hG : IsCompactAmplitude I K G) :
    ContDiffOn ℝ ∞ (synthesis G) (slab I) := by
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have h := contDiffOn_convolution_left_with_param_comp (μ := (volume : Measure E3)) L
    (v := fun _ : E => (0 : E3)) contDiffOn_const (f := fun _ : E3 => (1 : ℝ))
    (isOpen_slab hI) hK (fun p x hp hx => hG.integrand_eq_zero hp hx)
    (locallyIntegrable_const 1) hG.contDiffOn_integrand
  refine h.congr fun z _ => ?_
  rw [synthesis_eq, convolution]
  simp [L]

theorem differentiableAt_synthesis (hI : IsOpen I) (hK : IsCompact K)
    (hG : IsCompactAmplitude I K G) {z : E} (hz : z ∈ slab I) :
    DifferentiableAt ℝ (synthesis G) z :=
  ((contDiffOn_synthesis hI hK hG).differentiableOn (by simp)).differentiableAt
    ((isOpen_slab hI).mem_nhds hz)

theorem fderiv_synthesis (hI : IsOpen I) (hK : IsCompact K) (hG : IsCompactAmplitude I K G)
    {z : E} (hz : z ∈ slab I) (v : E) :
    fderiv ℝ (synthesis G) z v = ∫ ξ, fderiv ℝ (fun w => synthesisIntegrand G w ξ) z v := by
  have e : synthesis G = fun w => ∫ ξ, synthesisIntegrand G w ξ := funext (synthesis_eq G)
  rw [e]
  exact fderiv_integral_apply (isOpen_slab hI) hK (hG.contDiffOn_integrand.of_le (by simp))
    (fun _ hp _ hξ => hG.integrand_eq_zero hp hξ) hz v

/-- The directional derivative of the integrand computed along the line `s ↦ z + s v`. -/
theorem fderiv_integrand_eq (hI : IsOpen I) (hG : IsCompactAmplitude I K G) {z : E}
    (hz : z ∈ slab I) (ξ : E3) (v : E) {D : ℂ}
    (hD : HasDerivAt (fun s : ℝ => synthesisIntegrand G (z + s • v) ξ) D 0) :
    fderiv ℝ (fun w => synthesisIntegrand G w ξ) z v = D := by
  have hd : DifferentiableAt ℝ (fun w => synthesisIntegrand G w ξ) z :=
    (hasFDerivAt_fderiv_uncurry (isOpen_slab hI) (hG.contDiffOn_integrand.of_le (by simp))
      hz ξ).differentiableAt
  have hl : HasDerivAt (fun s : ℝ => z + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h2 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact h2.unique hD

theorem fderiv_integrand_time (hI : IsOpen I) (hG : IsCompactAmplitude I K G) {z : E}
    (hz : z ∈ slab I) (ξ : E3) :
    fderiv ℝ (fun w => synthesisIntegrand G w ξ) z (Pi.single 0 1) =
      synthesisIntegrand (timeDeriv G) z ξ := by
  refine fderiv_integrand_eq hI hG hz ξ _ ?_
  have hs (s : ℝ) : spatialPoint (z + s • Pi.single 0 1) = spatialPoint z := by
    ext γ; simp
  have h0 (s : ℝ) : (z + s • (Pi.single 0 1 : E)) 0 = z 0 + s := by simp
  have e : (fun s : ℝ => synthesisIntegrand G (z + s • Pi.single 0 1) ξ) = fun s =>
      Complex.exp (↑(2 * Real.pi * ⟪ξ, spatialPoint z⟫) * Complex.I) * G (z 0 + s) ξ := by
    funext s; simp only [synthesisIntegrand, hs, h0]
  rw [e]
  have h2 : HasDerivAt (fun s => G s ξ) (timeDeriv G (z 0) ξ) (z 0 + 0) := by
    rw [add_zero]; exact hG.hasDerivAt hI hz ξ
  exact (h2.comp_const_add (z 0) 0).const_mul _

theorem fderiv_integrand_space (hI : IsOpen I) (hG : IsCompactAmplitude I K G) {z : E}
    (hz : z ∈ slab I) (ξ : E3) (γ : Fin 3) :
    fderiv ℝ (fun w => synthesisIntegrand G w ξ) z (Pi.single γ.succ 1) =
      synthesisIntegrand (fun t ξ => 2 * Real.pi * ξ γ * Complex.I * G t ξ) z ξ := by
  refine fderiv_integrand_eq hI hG hz ξ _ ?_
  have h0 (s : ℝ) : (z + s • (Pi.single γ.succ 1 : E)) 0 = z 0 := by simp
  have hs (s : ℝ) : ⟪ξ, spatialPoint (z + s • Pi.single γ.succ 1)⟫ =
      ⟪ξ, spatialPoint z⟫ + s * ξ γ := by
    rw [map_add, inner_add_right, map_smul, inner_smul_right]
    congr 1
    rw [inner_spatialPoint]
    simp [Pi.single_apply, Fin.succ_inj]
  simp only [synthesisIntegrand, h0, hs]
  have hlin : HasDerivAt (fun s : ℝ => (↑(2 * Real.pi * (⟪ξ, spatialPoint z⟫ + s * ξ γ)) *
      Complex.I : ℂ)) (↑(2 * Real.pi * ξ γ) * Complex.I) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => 2 * Real.pi * (⟪ξ, spatialPoint z⟫ + s * ξ γ))
        (2 * Real.pi * ξ γ) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (ξ γ)).const_add
        ⟪ξ, spatialPoint z⟫).const_mul (2 * Real.pi)
    exact h1.ofReal_comp.mul_const Complex.I
  have := (hlin.cexp).mul_const (G (z 0) ξ)
  convert this using 1
  simp
  ring

/-- **The time derivative of the synthesis** is the synthesis of `∂ₜG`. -/
theorem fderiv_synthesis_time (hI : IsOpen I) (hK : IsCompact K) (hG : IsCompactAmplitude I K G)
    {z : E} (hz : z ∈ slab I) :
    fderiv ℝ (synthesis G) z (Pi.single 0 1) = synthesis (timeDeriv G) z := by
  rw [fderiv_synthesis hI hK hG hz, synthesis_eq]
  exact integral_congr_ae (Eventually.of_forall fun ξ => fderiv_integrand_time hI hG hz ξ)

/-- **The spatial derivatives of the synthesis**: `∂_γ` is the synthesis of `2πi ξ_γ G`. -/
theorem fderiv_synthesis_space (hI : IsOpen I) (hK : IsCompact K)
    (hG : IsCompactAmplitude I K G) {z : E} (hz : z ∈ slab I) (γ : Fin 3) :
    fderiv ℝ (synthesis G) z (Pi.single γ.succ 1) =
      synthesis (fun t ξ => 2 * Real.pi * ξ γ * Complex.I * G t ξ) z := by
  rw [fderiv_synthesis hI hK hG hz, synthesis_eq]
  exact integral_congr_ae (Eventually.of_forall fun ξ => fderiv_integrand_space hI hG hz ξ γ)

/-- The multiplier `2πi ξ_γ` of the spatial derivatives is smooth. -/
theorem contDiff_spaceMultiplier (γ : Fin 3) :
    ContDiff ℝ ∞ fun ξ : E3 => (2 * Real.pi * ξ γ * Complex.I : ℂ) := by
  have h : ContDiff ℝ ∞ fun ξ : E3 => ξ γ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) γ).contDiff
  exact ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h)).mul contDiff_const)

theorem IsCompactAmplitude.space (hG : IsCompactAmplitude I K G) (hK : IsCompact K)
    (γ : Fin 3) :
    IsCompactAmplitude I K (fun t ξ => 2 * Real.pi * ξ γ * Complex.I * G t ξ) :=
  hG.mul_left hK isOpen_univ (subset_univ K) (contDiff_spaceMultiplier γ).contDiffOn

/-! #### Linearity -/

theorem synthesis_add {z : E} (h₁ : Integrable (synthesisIntegrand G₁ z))
    (h₂ : Integrable (synthesisIntegrand G₂ z)) :
    synthesis (fun t ξ => G₁ t ξ + G₂ t ξ) z = synthesis G₁ z + synthesis G₂ z := by
  simp only [synthesis_eq]
  rw [← integral_add h₁ h₂]
  exact integral_congr_ae (Eventually.of_forall fun ξ => by simp [synthesisIntegrand, mul_add])

theorem synthesis_sub {z : E} (h₁ : Integrable (synthesisIntegrand G₁ z))
    (h₂ : Integrable (synthesisIntegrand G₂ z)) :
    synthesis (fun t ξ => G₁ t ξ - G₂ t ξ) z = synthesis G₁ z - synthesis G₂ z := by
  simp only [synthesis_eq]
  rw [← integral_sub h₁ h₂]
  exact integral_congr_ae (Eventually.of_forall fun ξ => by simp [synthesisIntegrand, mul_sub])

/-- A coefficient that depends on the time alone comes out of the synthesis. -/
theorem synthesis_const_mul (c : ℝ → ℂ) (G : ℝ → E3 → ℂ) (z : E) :
    synthesis (fun t ξ => c t * G t ξ) z = c (z 0) * synthesis G z := by
  simp only [synthesis_eq]
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun ξ => by
    simp only [synthesisIntegrand]; ring)

/-- A finite sum with coefficients that depend on the time comes out of the synthesis. -/
theorem synthesis_fintype_sum {ι : Type*} [Fintype ι] (c : ι → ℝ → ℂ) (G : ι → ℝ → E3 → ℂ)
    {z : E} (h : ∀ i, Integrable (synthesisIntegrand (G i) z)) :
    synthesis (fun t ξ => ∑ i, c i t * G i t ξ) z = ∑ i, c i (z 0) * synthesis (G i) z := by
  simp only [synthesis_eq]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun i _ => (h i).const_mul (c i (z 0))]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [synthesisIntegrand, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The synthesis commutes with a linear form of the amplitudes** whose coefficients depend on
the time: `synthesis (Λ(t) G(t, ξ)) = Λ(t₀) (synthesis G)`. -/
theorem synthesis_linearMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Λ : ℝ → (ι → ℂ) →ₗ[ℂ] ℂ) (G : ι → ℝ → E3 → ℂ) {z : E}
    (h : ∀ i, Integrable (synthesisIntegrand (G i) z)) :
    synthesis (fun t ξ => Λ t fun i => G i t ξ) z = Λ (z 0) fun i => synthesis (G i) z := by
  have e : (fun t ξ => Λ t fun i => G i t ξ) = fun t ξ =>
      ∑ i, Λ t (fun j => if i = j then 1 else 0) * G i t ξ := by
    funext t ξ
    rw [LinearMap.pi_apply_eq_sum_univ]
    exact Finset.sum_congr rfl fun _ _ => by rw [smul_eq_mul, mul_comm]
  rw [e, synthesis_fintype_sum _ _ h, LinearMap.pi_apply_eq_sum_univ]
  exact Finset.sum_congr rfl fun _ _ => by rw [smul_eq_mul, mul_comm]

theorem synthesis_congr {G₁ G₂ : ℝ → E3 → ℂ} {z : E} (h : ∀ ξ, G₁ (z 0) ξ = G₂ (z 0) ξ) :
    synthesis G₁ z = synthesis G₂ z := by
  simp only [synthesis, funext h]

@[simp] theorem synthesis_zero (z : E) : synthesis (fun _ _ => 0) z = 0 := by
  simp [synthesis_eq, synthesisIntegrand]

/-! #### Real fields -/

/-- **The synthesis of a Hermitian amplitude is real.** -/
theorem conj_synthesis {z : E} (h : ∀ ξ, G (z 0) (-ξ) = conj (G (z 0) ξ)) :
    conj (synthesis G z) = synthesis G z := by
  simp only [synthesis_eq]
  rw [← integral_conj, ← integral_neg_eq_self (fun ξ => synthesisIntegrand G z ξ)]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  have hc (a : ℝ) : conj ((a : ℂ) * Complex.I) = ((-a : ℝ) : ℂ) * Complex.I := by
    simp [Complex.conj_ofReal]
  simp only [synthesisIntegrand, map_mul, h, inner_neg_left, ← Complex.exp_conj, hc, mul_neg]

theorem ofReal_re_synthesis {z : E} (h : ∀ ξ, G (z 0) (-ξ) = conj (G (z 0) ξ)) :
    ((synthesis G z).re : ℂ) = synthesis G z := by
  conv_rhs => rw [← Complex.re_add_im (synthesis G z)]
  have him : (synthesis G z).im = 0 := Complex.conj_eq_iff_im.mp (conj_synthesis h)
  rw [him]
  simp

theorem IsHermitian.timeDeriv (hH : IsHermitian I G) (hG : IsCompactAmplitude I K G)
    (hI : IsOpen I) : IsHermitian I (Fourier.timeDeriv G) := by
  intro t ht ξ
  have hev : (fun s => G s (-ξ)) =ᶠ[𝓝 t] fun s => conj (G s ξ) :=
    eventually_of_mem (hI.mem_nhds ht) fun s hs => hH s hs ξ
  have hc : HasDerivAt (fun s => conj (G s ξ)) (conj (Fourier.timeDeriv G t ξ)) t := by
    simpa only [starRingEnd_apply] using (hG.hasDerivAt hI ht ξ).star
  simp only [ProjectAinos.SmoothGeometry.Fourier.timeDeriv, hev.deriv_eq]
  exact hc.deriv

theorem IsHermitian.mul_left (hH : IsHermitian I G) {m : E3 → ℂ}
    (hm : ∀ ξ, m (-ξ) = conj (m ξ)) : IsHermitian I (fun t ξ => m ξ * G t ξ) := by
  intro t ht ξ
  simp [hm, hH t ht ξ]

theorem IsHermitian.space (hH : IsHermitian I G) (γ : Fin 3) :
    IsHermitian I (fun t ξ => 2 * Real.pi * ξ γ * Complex.I * G t ξ) :=
  hH.mul_left fun ξ => by
    simp only [PiLp.neg_apply, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast; ring

theorem IsHermitian.add (h₁ : IsHermitian I G₁) (h₂ : IsHermitian I G₂) :
    IsHermitian I (fun t ξ => G₁ t ξ + G₂ t ξ) := by
  intro t ht ξ; simp [h₁ t ht ξ, h₂ t ht ξ]


/-! #### The slices of the synthesis -/

theorem IsCompactAmplitude.contDiff_slice (hG : IsCompactAmplitude I K G) {t : ℝ} (ht : t ∈ I) :
    ContDiff ℝ ∞ (G t) := by
  rw [← contDiffOn_univ]
  exact hG.smooth.comp ((contDiff_const.prodMk contDiff_id).contDiffOn) fun _ _ =>
    ⟨ht, mem_univ _⟩

theorem IsCompactAmplitude.hasCompactSupport (hG : IsCompactAmplitude I K G) (hK : IsCompact K)
    {t : ℝ} (ht : t ∈ I) : HasCompactSupport (G t) :=
  HasCompactSupport.intro hK (hG.support t ht)

theorem synthesis_spacetimePoint (G : ℝ → E3 → ℂ) (t : ℝ) (x : E3) :
    synthesis G (spacetimePoint t x) = 𝓕⁻ (G t) x := by
  simp [synthesis]

/-- **The slices of the synthesis are Schwartz functions**: the inverse transform of the smooth
compactly supported amplitude. -/
theorem synthesis_slice_eq_schwartz (hG : IsCompactAmplitude I K G) (hK : IsCompact K) {t : ℝ}
    (ht : t ∈ I) :
    (fun x => synthesis G (spacetimePoint t x)) =
      ⇑(𝓕⁻ ((hG.hasCompactSupport hK ht).toSchwartzMap (hG.contDiff_slice ht) : 𝓢(E3, ℂ)) :
        𝓢(E3, ℂ)) := by
  funext x
  rw [synthesis_spacetimePoint, SchwartzMap.fourierInv_coe]
  rfl

theorem continuous_synthesis_slice (hG : IsCompactAmplitude I K G) (hK : IsCompact K) {t : ℝ}
    (ht : t ∈ I) : Continuous fun x => synthesis G (spacetimePoint t x) := by
  rw [synthesis_slice_eq_schwartz hG hK ht]
  exact SchwartzMap.continuous _

theorem integrable_synthesis_slice (hG : IsCompactAmplitude I K G) (hK : IsCompact K) {t : ℝ}
    (ht : t ∈ I) : Integrable fun x => synthesis G (spacetimePoint t x) := by
  rw [synthesis_slice_eq_schwartz hG hK ht]
  exact SchwartzMap.integrable _

/-- **The transform of a slice of the synthesis is the amplitude.** -/
theorem fourier_synthesis_slice (hG : IsCompactAmplitude I K G) (hK : IsCompact K) {t : ℝ}
    (ht : t ∈ I) : 𝓕 (fun x => synthesis G (spacetimePoint t x)) = G t := by
  have e : (fun x => synthesis G (spacetimePoint t x)) = 𝓕⁻ (G t) :=
    funext fun x => synthesis_spacetimePoint G t x
  have hF : Integrable (𝓕 (G t)) := by
    have : 𝓕 (G t) = ⇑(𝓕 ((hG.hasCompactSupport hK ht).toSchwartzMap (hG.contDiff_slice ht) :
        𝓢(E3, ℂ)) : 𝓢(E3, ℂ)) := by
      rw [SchwartzMap.fourier_coe]; rfl
    rw [this]
    exact SchwartzMap.integrable _
  rw [e, Continuous.fourier_fourierInv_eq (hG.continuous ht) (hG.integrable hK ht) hF]

/-! #### Uniqueness and inversion -/

/-- **Uniqueness of the synthesis**: a continuous integrable amplitude whose synthesis vanishes
at all points of one time is zero at that time. -/
theorem eq_zero_of_synthesis_eq_zero {t : ℝ} (hc : Continuous (G t)) (hi : Integrable (G t))
    (h : ∀ x : E3, synthesis G (spacetimePoint t x) = 0) (ξ : E3) : G t ξ = 0 := by
  have h1 : 𝓕⁻ (G t) = 0 := funext fun x => by simpa [synthesis] using h x
  have h2 : 𝓕 (G t) = 0 := funext fun w => by
    rw [show w = -(-w) from (neg_neg w).symm, ← Real.fourierInv_eq_fourier_neg, h1]
    rfl
  have h3 := Continuous.fourierInv_fourier_eq hc hi (by rw [h2]; exact integrable_zero _ _ _)
  rw [← h3, h2]
  simp [Real.fourierInv_eq]

/-- **Fourier inversion**: if the slices `x ↦ f(t, x)` are continuous and integrable and their
Fourier transforms are integrable, the synthesis of the transforms is `f`. -/
theorem synthesis_fourier (f : E → ℂ) {z : E}
    (hc : Continuous fun x : E3 => f (spacetimePoint (z 0) x))
    (hi : Integrable fun x : E3 => f (spacetimePoint (z 0) x))
    (hF : Integrable (𝓕 fun x : E3 => f (spacetimePoint (z 0) x))) :
    synthesis (fun t => 𝓕 fun x : E3 => f (spacetimePoint t x)) z = f z := by
  rw [synthesis, Continuous.fourierInv_fourier_eq hc hi hF]
  exact congrArg f (spacetimePoint_eq z)

/-- **The transform of a real function is Hermitian.** -/
theorem fourier_neg_of_real (f : E3 → ℂ) (hf : ∀ x, conj (f x) = f x) (ξ : E3) :
    𝓕 f (-ξ) = conj (𝓕 f ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Circle.smul_def, smul_eq_mul, map_mul, hf, inner_neg_right, neg_neg]
  congr 1
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]

/-- The real part commutes with the derivatives. -/
theorem fderiv_re {g : E → ℂ} {z : E} (hg : DifferentiableAt ℝ g z) (v : E) :
    fderiv ℝ (fun w => (g w).re) z v = (fderiv ℝ g z v).re := by
  have h := (Complex.reCLM.hasFDerivAt (x := g z)).comp z hg.hasFDerivAt
  rw [show (fun w => (g w).re) = Complex.reCLM ∘ g from rfl, h.fderiv]
  rfl

end ProjectAinos.SmoothGeometry.Fourier
