/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.PerturbationReconstruction
import Mathlib.Tactic

/-!
# A test packet with scalar and tensor components

A wave packet on a flat dust universe (`CosmologicalPerturbation.Reconstruction`): the even
profile `φ(ξ) = b(ξ) + b(−ξ)` of a smooth bump `b` about `ξ₀ = (0, 0, 1)` (`profile`), supported
in the two balls of radius `1/2` about `±ξ₀` (`spectrum`, which avoids `ξ = 0`), and the metric
amplitude
`ĥ(t, ξ) = φ(ξ) (c n n/|n|² + τ(t, ξ) e(ξ))`, `n = 2πξ` (`packetMetric`),
with a scalar component (the longitudinal projector, the spatial co-ordinate mode `λ = μ = c` of
L&L) and a tensor component along the transverse-traceless polarization `e(ξ) = Π_T(n) e₊`
(`polarization`), with no density contrast and no velocity.

* `isFourierData_packet`: the packet is Fourier data for every smooth even `τ`.
* `scalarData_packet`, `vectorData_packet`, `tensorData_packet`: **the decomposition recovers
  the two components**: the scalar part is `φ c nn/|n|²`, the vector part vanishes and the tensor
  part is `φ τ e`.
* `frequencyEq_packet_iff` and `linearizedEinsteinDust_packet_iff`: on a dust background **the
  packet solves the linearized Einstein equations with dust if and only if, at every frequency
  of the support with `e(ξ) ≠ 0`, the tensor amplitude satisfies
  `τ̈ + 3(ȧ/a) τ̇ + (|n|²/a²) τ = 0`**: the scalar component solves its equations by itself.
* `linearizedEinsteinDust_packet_zero`: with `τ = 0` the packet is a nonzero solution.
-/

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology ComplexConjugate

namespace ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Packet

open SmoothGeometry CoordinateMetric FLRW SmoothGeometry.Fourier Reconstruction
open SmoothGeometry.ScalarVectorTensor (Mat3 SymbolEq scalarPart vectorPart tensorPart longVec
  transVec longProj)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The profile -/

/-- The frequency `ξ₀ = (0, 0, 1)`. -/
def ξ₀ : E3 := EuclideanSpace.single 2 1

/-- A smooth bump about `ξ₀`, supported in the ball of radius `1/2`. -/
def bump : ContDiffBump ξ₀ := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The even profile `φ(ξ) = b(ξ) + b(−ξ)`. -/
def profile (ξ : E3) : ℝ := bump ξ + bump (-ξ)

/-- The spectrum: the closed balls of radius `1/2` about `±ξ₀`. -/
def spectrum : Set E3 := Metric.closedBall ξ₀ (1 / 2) ∪ Metric.closedBall (-ξ₀) (1 / 2)

theorem isCompact_spectrum : IsCompact spectrum :=
  (isCompact_closedBall _ _).union (isCompact_closedBall _ _)

theorem norm_ξ₀ : ‖ξ₀‖ = 1 := by simp [ξ₀]

theorem zero_notMem_spectrum : (0 : E3) ∉ spectrum := by
  rintro (h | h) <;> simp [Metric.mem_closedBall, norm_ξ₀] at h <;> norm_num at h

theorem profile_eq_zero {ξ : E3} (hξ : ξ ∉ spectrum) : profile ξ = 0 := by
  have h1 : bump ξ = 0 := by
    have : ξ ∉ Function.support bump := by
      rw [bump.support_eq]
      exact fun h => hξ (Or.inl (Metric.ball_subset_closedBall h))
    simpa using this
  have h2 : bump (-ξ) = 0 := by
    have : -ξ ∉ Function.support bump := by
      rw [bump.support_eq]
      intro h
      apply hξ (Or.inr (Metric.ball_subset_closedBall _))
      rw [Metric.mem_ball, ← dist_neg_neg, neg_neg]
      exact h
    simpa using this
  simp [profile, h1, h2]

theorem profile_neg (ξ : E3) : profile (-ξ) = profile ξ := by
  simp [profile, add_comm]

theorem contDiff_profile : ContDiff ℝ ∞ profile :=
  bump.contDiff.add (bump.contDiff.comp contDiff_neg)

theorem profile_ξ₀_pos : 0 < profile ξ₀ := by
  have h1 : bump ξ₀ = 1 := bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)
  have h2 : 0 ≤ bump (-ξ₀) := bump.nonneg
  simp only [profile, h1]
  linarith

/-! ### The packet -/

/-- The `+` polarization `diag(1, −1, 0)` as a complex matrix. -/
def plusC : Mat3 ℂ := fun α β => (plusPolarization α β : ℂ)

/-- The transverse-traceless polarization `e(ξ) = Π_T(2πξ) e₊` of the frequency `ξ`. -/
def polarization (ξ : E3) : Mat3 ℂ := tensorPart (wave ξ) plusC

/-- **The packet** `ĥ(t, ξ) = φ(ξ) (c nn/|n|² + τ(t, ξ) e(ξ))`. -/
def packetMetric (c : ℝ) (τ : ℝ → E3 → ℝ) : ℝ → E3 → Mat3 ℂ :=
  fun t ξ α β => (profile ξ : ℂ) * (c * longProj (wave ξ) α β + (τ t ξ : ℂ) * polarization ξ α β)

theorem plusC_symm (α β : Fin 3) : plusC α β = plusC β α := by
  simp only [plusC, isTensorPolarization_plus.symm α β]

theorem conj_plusC : (fun α β => conj (plusC α β)) = plusC := by
  funext α β; simp [plusC, Complex.conj_ofReal]

theorem conj_polarization (ξ : E3) (α β : Fin 3) :
    conj (polarization ξ α β) = polarization ξ α β := by
  rw [polarization, ← ScalarVectorTensor.tensorPart_map _ (starRingEnd ℂ) (conj_wave ξ),
    conj_plusC]

theorem conj_longProj (ξ : E3) (α β : Fin 3) :
    conj (longProj (wave ξ) α β) = longProj (wave ξ) α β := by
  simp only [longProj, ScalarVectorTensor.nsq, map_div₀, map_mul, map_sum, map_pow, conj_wave]

theorem longProj_wave_neg (ξ : E3) : longProj (wave (-ξ)) = longProj (wave ξ) := by
  funext α β
  simp only [longProj, wave_neg, ScalarVectorTensor.nsq_neg, Pi.neg_apply, neg_mul_neg]

theorem polarization_neg (ξ : E3) : polarization (-ξ) = polarization ξ := by
  rw [polarization, polarization, wave_neg, ScalarVectorTensor.tensorPart_neg]

variable {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {c : ℝ} {τ : ℝ → E3 → ℝ}

/-- The profile as an amplitude of the class. -/
theorem isCompactAmplitude_profile (I : Set ℝ) :
    IsCompactAmplitude I spectrum fun (_ : ℝ) ξ => (profile ξ : ℂ) where
  smooth := (Complex.ofRealCLM.contDiff.comp (contDiff_profile.comp contDiff_snd)).contDiffOn
  support _ _ _ hξ := by simp [profile_eq_zero hξ]

/-- **The packet is Fourier data** for every smooth even `τ`. -/
theorem isFourierData_packet (hτ : ContDiffOn ℝ ∞ (uncurry τ) (B.I ×ˢ univ))
    (hτe : ∀ t ξ, τ t (-ξ) = τ t ξ) :
    IsFourierData B.I spectrum (packetMetric c τ) (fun _ _ => 0) (fun _ _ _ => 0) where
  metric α β := by
    have hG := isCompactAmplitude_profile B.I
    have hτc : ContDiffOn ℝ ∞ (uncurry fun t ξ => (τ t ξ : ℂ)) (B.I ×ˢ univ) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn hτ
    have h1 := hG.mul_left isCompact_spectrum (m := fun ξ => (c : ℂ) * longProj (wave ξ) α β)
      isOpen_nonzero (subset_nonzero zero_notMem_spectrum)
      (contDiffOn_const.mul (ContDiffOn.div_nsq_wave
        ((contDiff_wave α).mul (contDiff_wave β)).contDiffOn))
    have h2 := (hG.mul_smooth hτc).mul_left isCompact_spectrum
      (m := fun ξ => polarization ξ α β) isOpen_nonzero (subset_nonzero zero_notMem_spectrum)
      (contDiffOn_tensorPart_wave plusC α β)
    have e : amp (packetMetric c τ) α β = fun t ξ =>
        (c : ℂ) * longProj (wave ξ) α β * (profile ξ : ℂ) +
          polarization ξ α β * ((τ t ξ : ℂ) * (profile ξ : ℂ)) := by
      funext t ξ; simp only [amp, packetMetric]; ring
    rw [e]
    exact h1.add h2
  density := IsCompactAmplitude.zero
  velocity _ := IsCompactAmplitude.zero
  symm t ξ α β := by
    simp only [packetMetric, longProj, polarization,
      ScalarVectorTensor.tensorPart_symm _ _ plusC_symm α β]
    ring
  herm_metric α β t _ ξ := by
    simp only [amp, packetMetric, profile_neg, longProj_wave_neg, polarization_neg, hτe, map_mul,
      map_add, Complex.conj_ofReal, conj_longProj, conj_polarization]
  herm_density _ _ _ := by simp
  herm_velocity _ _ _ _ := by simp [vamp]

/-! ### The components -/

theorem packetMetric_eq (t : ℝ) (ξ : E3) :
    packetMetric c τ t ξ = (profile ξ : ℂ) • ((c : ℂ) • longProj (wave ξ) +
      (τ t ξ : ℂ) • polarization ξ) := by
  funext α β; simp [packetMetric]

/-- **The scalar part of the packet** is `φ c nn/|n|²`. -/
theorem scalarData_packet (t : ℝ) {ξ : E3} (hξ : ξ ≠ 0) :
    scalarData (packetMetric c τ) t ξ = ((profile ξ : ℂ) * c) • longProj (wave ξ) := by
  have hn := nsq_wave_ne_zero hξ
  simp only [scalarData, packetMetric_eq, map_smul, map_add, polarization,
    ScalarVectorTensor.scalarPart_longProj hn, ScalarVectorTensor.scalarPart_tensorPart _ hn,
    smul_zero, add_zero, smul_smul]

/-- **The packet has no vector part.** -/
theorem vectorData_packet (t : ℝ) {ξ : E3} (hξ : ξ ≠ 0) :
    vectorData (packetMetric c τ) t ξ = 0 := by
  have hn := nsq_wave_ne_zero hξ
  simp only [vectorData, packetMetric_eq, map_smul, map_add, polarization,
    ScalarVectorTensor.vectorPart_longProj hn, ScalarVectorTensor.vectorPart_tensorPart _ hn,
    smul_zero, add_zero]

/-- **The tensor part of the packet** is `φ τ e`. -/
theorem tensorData_packet (t : ℝ) {ξ : E3} (hξ : ξ ≠ 0) :
    tensorData (packetMetric c τ) t ξ = ((profile ξ : ℂ) * τ t ξ) • polarization ξ := by
  have hn := nsq_wave_ne_zero hξ
  simp only [tensorData, packetMetric_eq, map_smul, map_add, polarization,
    ScalarVectorTensor.tensorPart_longProj hn, ScalarVectorTensor.tensorPart_tensorPart _ hn,
    smul_zero, zero_add, smul_smul]

/-! ### The equations of the packet -/

/-- `|2πξ|²` as a real number. -/
def nsqR (ξ : E3) : ℝ := ∑ γ, (2 * Real.pi * ξ γ) ^ 2

theorem nsq_wave_eq (ξ : E3) : ScalarVectorTensor.nsq (wave ξ) = (nsqR ξ : ℂ) := by
  simp [ScalarVectorTensor.nsq, wave, nsqR]

theorem jet1_packet (hτ : ContDiffOn ℝ ∞ (uncurry τ) (B.I ×ˢ univ)) {t : ℝ} (ht : t ∈ B.I)
    (ξ : E3) :
    jet1 (packetMetric c τ) t ξ =
      ((profile ξ : ℂ) * ((deriv (fun s => τ s ξ) t : ℝ) : ℂ)) • polarization ξ := by
  have hτξ : ContDiffOn ℝ ∞ (fun s => τ s ξ) B.I :=
    hτ.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun s hs => ⟨hs, mem_univ _⟩
  have hd := (hasDerivAt_of_contDiffOn B.isOpen_I hτξ ht).ofReal_comp
  funext α β
  refine (((hd.mul_const (polarization ξ α β)).const_add
    ((c : ℂ) * longProj (wave ξ) α β)).const_mul (profile ξ : ℂ)).deriv.trans ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem jet2_packet (hτ : ContDiffOn ℝ ∞ (uncurry τ) (B.I ×ˢ univ)) {t : ℝ} (ht : t ∈ B.I)
    (ξ : E3) :
    jet2 (packetMetric c τ) t ξ =
      ((profile ξ : ℂ) * ((deriv (deriv fun s => τ s ξ) t : ℝ) : ℂ)) • polarization ξ := by
  have hτξ : ContDiffOn ℝ ∞ (fun s => τ s ξ) B.I :=
    hτ.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun s hs => ⟨hs, mem_univ _⟩
  have hd := (hasDerivAt_of_contDiffOn B.isOpen_I
    (contDiffOn_deriv_of_contDiffOn B.isOpen_I hτξ) ht).ofReal_comp
  funext α β
  have hev : (fun s => timeDeriv (amp (packetMetric c τ) α β) s ξ) =ᶠ[𝓝 t]
      fun s => (profile ξ : ℂ) * (((deriv (fun s => τ s ξ) s : ℝ) : ℂ) * polarization ξ α β) :=
    eventually_of_mem (B.isOpen_I.mem_nhds ht) fun s hs => by
      have := congrFun (congrFun (jet1_packet (c := c) hτ hs ξ) α) β
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul] at this
      show jet1 (packetMetric c τ) s ξ α β = _
      rw [this]; ring
  simp only [jet2, timeDeriv] at hev ⊢
  rw [hev.deriv_eq, ((hd.mul_const (polarization ξ α β)).const_mul (profile ξ : ℂ)).deriv]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The equations of one frequency of the packet**: on a dust background they hold if and only
if `φ(ξ) = 0`, `e(ξ) = 0` or the tensor amplitude satisfies
`τ̈ + 3(ȧ/a) τ̇ + (|n|²/a²) τ = 0`. -/
theorem frequencyEq_packet_iff (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) (hτ : ContDiffOn ℝ ∞ (uncurry τ) (B.I ×ˢ univ))
    (hτe : ∀ t ξ, τ t (-ξ) = τ t ξ) {t : ℝ} (ht : t ∈ B.I) (ξ : E3) :
    FrequencyEq B κ ρ (packetMetric c τ) (fun _ _ => 0) (fun _ _ _ => 0) t ξ ↔
      profile ξ = 0 ∨ polarization ξ = 0 ∨
        deriv (deriv fun s => τ s ξ) t + 3 * (deriv B.a t / B.a t) * deriv (fun s => τ s ξ) t +
          nsqR ξ / B.a t ^ 2 * τ t ξ = 0 := by
  have hD := isFourierData_packet (c := c) hτ hτe
  by_cases hξK : ξ ∈ spectrum
  swap
  · exact ⟨fun _ => Or.inl (profile_eq_zero hξK), fun _ => frequencyEq_of_notMem hD ht hξK⟩
  have hξ : ξ ≠ 0 := fun h => zero_notMem_spectrum (h ▸ hξK)
  have hn := nsq_wave_ne_zero hξ
  have ha := (B.a_pos t ht).ne'
  obtain ⟨e1, e2⟩ := dust_background hB ht
  have hc₁ : (fourierCoeffs B κ ρ t).c₁ = (fourierCoeffs B κ ρ t).src := by
    simp only [fourierCoeffs]
    congr 1
    rw [e1, e2]; ring
  have hS : SymbolEq (fourierCoeffs B κ ρ t) (wave ξ)
      ((profile ξ : ℂ) • (c : ℂ) • longProj (wave ξ)) 0 0 0 0 := by
    refine ⟨by simp [ScalarVectorTensor.resTime], by funext α; simp [ScalarVectorTensor.resMixed],
      ?_⟩
    simp only [ScalarVectorTensor.resSpace, map_smul, ScalarVectorTensor.op_longProj hn, hc₁,
      ScalarVectorTensor.trace_zero, mul_zero, sub_zero, smul_zero, zero_smul, add_zero]
    funext α β
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  have key : (ScalarVectorTensor.nsq (wave ξ) / 2 + (fourierCoeffs B κ ρ t).c₁ -
        (fourierCoeffs B κ ρ t).src) • (profile ξ : ℂ) • (τ t ξ : ℂ) • tensorPart (wave ξ) plusC +
      (fourierCoeffs B κ ρ t).c₂ • ((profile ξ : ℂ) * ((deriv (fun s => τ s ξ) t : ℝ) : ℂ)) •
        tensorPart (wave ξ) plusC +
      (fourierCoeffs B κ ρ t).c₃ •
        ((profile ξ : ℂ) * ((deriv (deriv fun s => τ s ξ) t : ℝ) : ℂ)) •
          tensorPart (wave ξ) plusC =
      ((profile ξ * (B.a t ^ 2 / 2 * (deriv (deriv fun s => τ s ξ) t +
        3 * (deriv B.a t / B.a t) * deriv (fun s => τ s ξ) t + nsqR ξ / B.a t ^ 2 * τ t ξ)) :
          ℝ) : ℂ) • tensorPart (wave ξ) plusC := by
    have ha' : (B.a t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
    rw [hc₁, nsq_wave_eq]
    funext α β
    simp only [fourierCoeffs, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  have h2 : B.a t ^ 2 / 2 ≠ 0 := by positivity
  have hTeq : (ScalarVectorTensor.nsq (wave ξ) / 2 + (fourierCoeffs B κ ρ t).c₁ -
        (fourierCoeffs B κ ρ t).src) • tensorPart (wave ξ) ((profile ξ : ℂ) •
          ((c : ℂ) • longProj (wave ξ) + (τ t ξ : ℂ) • polarization ξ)) +
      (fourierCoeffs B κ ρ t).c₂ • tensorPart (wave ξ)
        (((profile ξ : ℂ) * ((deriv (fun s => τ s ξ) t : ℝ) : ℂ)) • polarization ξ) +
      (fourierCoeffs B κ ρ t).c₃ • tensorPart (wave ξ)
        (((profile ξ : ℂ) * ((deriv (deriv fun s => τ s ξ) t : ℝ) : ℂ)) • polarization ξ) = 0 ↔
      profile ξ = 0 ∨ polarization ξ = 0 ∨
        deriv (deriv fun s => τ s ξ) t + 3 * (deriv B.a t / B.a t) * deriv (fun s => τ s ξ) t +
          nsqR ξ / B.a t ^ 2 * τ t ξ = 0 := by
    simp only [polarization, map_smul, map_add, ScalarVectorTensor.tensorPart_longProj hn,
      ScalarVectorTensor.tensorPart_tensorPart _ hn, smul_zero, zero_add]
    rw [key, smul_eq_zero, Complex.ofReal_eq_zero, mul_eq_zero, mul_eq_zero]
    simp only [h2, false_or]
    tauto
  rw [FrequencyEq, packetMetric_eq, jet1_packet hτ ht, jet2_packet hτ ht,
    ScalarVectorTensor.symbolEq_iff _ _ _ _ _ _ hn,
    ScalarVectorTensor.symbolEq_tensor_iff _ _ _ _ hn, hTeq]
  refine ⟨fun h => h.2.2, fun h => ⟨?_, ?_, h⟩⟩
  · convert hS using 2 <;> simp [polarization, ScalarVectorTensor.scalarPart_longProj hn,
      ScalarVectorTensor.scalarPart_tensorPart _ hn, ← Pi.zero_def]
  · convert ScalarVectorTensor.symbolEq_zero (fourierCoeffs B κ ρ t) (wave ξ) using 2 <;>
      simp [polarization, ScalarVectorTensor.vectorPart_longProj hn,
        ScalarVectorTensor.vectorPart_tensorPart _ hn, ← Pi.zero_def]

/-- **The packet solves the linearized Einstein equations with dust if and only if its tensor
amplitude satisfies `τ̈ + 3(ȧ/a) τ̇ + (|n|²/a²) τ = 0` at every frequency of the support with
`e(ξ) ≠ 0`**; the scalar component solves its equations by itself. -/
theorem linearizedEinsteinDust_packet_iff (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) (hτ : ContDiffOn ℝ ∞ (uncurry τ) (B.I ×ˢ univ))
    (hτe : ∀ t ξ, τ t (-ξ) = τ t ξ) :
    LinearizedEinsteinDust B κ ρ (fieldOf (packetMetric c τ)) (fun _ => 0) (fun _ _ => 0) ↔
      ∀ t ∈ B.I, ∀ ξ, profile ξ ≠ 0 → polarization ξ ≠ 0 →
        deriv (deriv fun s => τ s ξ) t + 3 * (deriv B.a t / B.a t) * deriv (fun s => τ s ξ) t +
          nsqR ξ / B.a t ^ 2 * τ t ξ = 0 := by
  have h := linearizedEinsteinDust_iff_frequencyEq (κ := κ) (ρ := ρ)
    (isFourierData_packet (c := c) hτ hτe) isCompact_spectrum
  rw [scalarOf_zero, vectorOf_zero] at h
  rw [h]
  refine forall₂_congr fun t ht => forall_congr' fun ξ => ?_
  rw [frequencyEq_packet_iff hB hτ hτe ht ξ]
  tauto

/-- **With `τ = 0` the packet is a solution**: the scalar packet `φ c nn/|n|²`. -/
theorem linearizedEinsteinDust_packet_zero (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) :
    LinearizedEinsteinDust B κ ρ (fieldOf (packetMetric c fun _ _ => 0)) (fun _ => 0)
      (fun _ _ => 0) :=
  (linearizedEinsteinDust_packet_iff hB contDiffOn_const (fun _ _ => rfl)).mpr
    fun t _ ξ _ _ => by simp

/-- At the centre `ξ₀` the scalar component of the packet is `φ(ξ₀) c` in the `(3, 3)` entry, so
the packet is nonzero for `c ≠ 0`. -/
theorem packetMetric_ξ₀ (t : ℝ) :
    packetMetric c τ t ξ₀ 2 2 = (profile ξ₀ : ℂ) * (c + (τ t ξ₀ : ℂ) * polarization ξ₀ 2 2) := by
  have hw : wave ξ₀ = ![0, 0, ((2 * Real.pi : ℝ) : ℂ)] := by
    funext γ; fin_cases γ <;> simp [wave, ξ₀]
  have hP : longProj (wave ξ₀) 2 2 = 1 := by
    have hn : ScalarVectorTensor.nsq (wave ξ₀) ≠ 0 :=
      nsq_wave_ne_zero (by rw [← norm_ne_zero_iff, norm_ξ₀]; norm_num)
    rw [ScalarVectorTensor.longProj, ← div_self hn]
    simp [ScalarVectorTensor.nsq, hw, Fin.sum_univ_three, sq]
  simp only [packetMetric, hP, mul_one]

theorem packetMetric_ne_zero (hc : c ≠ 0) (t : ℝ) (hτ0 : τ t ξ₀ = 0) :
    packetMetric c τ t ξ₀ ≠ 0 := by
  intro h
  have := congrFun (congrFun h 2) 2
  rw [packetMetric_ξ₀, hτ0] at this
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Pi.zero_apply, mul_eq_zero,
    Complex.ofReal_eq_zero] at this
  rcases this with h1 | h1
  · exact profile_ξ₀_pos.ne' h1
  · exact hc h1

/-- **The packet has a compact spectrum**, a nontrivial instance of `HasCompactSpectrum`. -/
theorem hasCompactSpectrum_packet (hτ : ContDiffOn ℝ ∞ (uncurry τ) (B.I ×ˢ univ))
    (hτe : ∀ t ξ, τ t (-ξ) = τ t ξ) :
    HasCompactSpectrum B.I spectrum (fieldOf (packetMetric c τ)) (fun _ => 0) (fun _ _ => 0) := by
  have h := ((isFourierData_packet (c := c) hτ hτe).hasCompactSpectrum isCompact_spectrum).1
  rwa [scalarOf_zero, vectorOf_zero] at h

end ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Packet
