/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.PerturbationPacket
public import ProjectAinos.SmoothGeometry.Fourier.WeightedSynthesis
public import ProjectAinos.SmoothGeometry.Tensor.ScalarVectorTensorScaling
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Tactic

/-!
# The reconstruction of a flat perturbation without a cutoff in the frequencies

Landau–Lifshitz, §115, for the flat (`k = 0`) dust universe in the synchronous reference system,
continuing `CosmologicalPerturbation.Reconstruction` without the compact spectrum. A perturbation
`(h_{αβ}, δ, v_α)` is given by its spatial Fourier amplitudes (`IsWeightedData`): the metric
amplitude is a weighted amplitude of order two (`Fourier.IsWeightedAmplitude`: twice
differentiable in `t ∈ I`, measurable in `ξ`, with `(1 + |ξ|)^m |∂ₜʲĥ(t, ξ)| ≤ g(ξ)` for
`j + m ≤ 2` and `g` integrable, locally uniformly in `t`), the density and velocity amplitudes
are of order zero, and all are Hermitian and the metric amplitude symmetric. The fields are the
syntheses `h_{αβ}(t, x) = Re ∫ e^{2πi⟪ξ, x⟫} ĥ_{αβ}(t, ξ) dξ` (`fieldOf`, `scalarOf`, `vectorOf`).

* `IsWeightedData.linearizedEinsteinDust_iff`: **the linearized Einstein equations with dust
  hold if and only if almost every frequency satisfies the mode equations** `FrequencyEq` at
  every time. The derivatives commute with the integral by dominated convergence
  (`Fourier.IsWeightedAmplitude.fderiv_synthesis_single`), and a frequency equation vanishes almost
  everywhere when its synthesis does, by the injectivity of the Fourier transform on `L¹`.
* `IsWeightedData.isWeightedData_scalar`, `…_vector`, `…_tensor`: the scalar, vector and tensor
  parts of the amplitudes are again weighted data. The projections are discontinuous only at
  `ξ = 0`, a null set, and their entries are bounded, being invariant under the dilations of
  `ξ` (`ScalarVectorTensor.scalarPart_smul_left`, `Fourier.exists_bound_of_scale_invariant`).
* `IsWeightedData.linearizedEinsteinDust_iff_split`: **the decomposition**, the perturbation
  solves the equations if and only if its scalar part (with `δ` and the longitudinal velocity),
  its vector part (with the transverse velocity) and its tensor part do;
  `IsWeightedData.fieldOf_eq_add`, `IsWeightedData.vectorOf_eq_add`: it is their sum.
* `HasIntegrableSpectrum`, `HasIntegrableSpectrum.reconstruction`: **the reconstruction** of a
  real perturbation whose slices are continuous and integrable and whose spatial transforms are
  weighted data, by Fourier inversion. `IsWeightedData.fourier_fieldOf_ae`: conversely, the
  transforms of integrable slices of the synthesized fields are the data almost everywhere.
* `hasIntegrableSpectrum_bump`, `fourierBump_zero_ne_zero`, `not_hasCompactSpectrum_bump`:
  **an instance beyond the compact spectrum**, the smooth compactly supported (Schwartz) slices
  of a bump, whose transform does not vanish at `ξ = 0`, so that no compact spectrum avoiding
  the origin contains it.
* `linearizedEinsteinDust_gaugeData`: **a solution beyond the compact spectrum**, the spatial
  co-ordinate mode `ĥ = F(ξ) nn/|n|²` with the Schwartz profile `F` of the bump, which does not
  vanish near `ξ = 0`, where `nn/|n|²` is discontinuous (`gaugeData_ne_zero_near_zero`).
-/

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology ComplexConjugate FourierTransform

namespace ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Reconstruction

open SmoothGeometry CoordinateMetric FLRW SmoothGeometry.Fourier
open SmoothGeometry.ScalarVectorTensor (Mat3 Coeffs SymbolEq resTime resMixed resSpace
  scalarPart vectorPart tensorPart longVec transVec longProj)

local notation "E" => MinkowskiModel 3
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Weighted Fourier data -/

/-- **Weighted Fourier data of a perturbation**: the metric amplitude is a weighted amplitude of
order two, the density and velocity amplitudes of order zero; the metric amplitude is symmetric
and all amplitudes are Hermitian. -/
structure IsWeightedData (I : Set ℝ) (hh : ℝ → E3 → Mat3 ℂ) (dd : ℝ → E3 → ℂ)
    (vv : ℝ → E3 → Fin 3 → ℂ) : Prop where
  /-- The metric amplitude is of order two. -/
  metric : ∀ α β, IsWeightedAmplitude I 2 (amp hh α β)
  /-- The density amplitude is of order zero. -/
  density : IsWeightedAmplitude I 0 dd
  /-- The velocity amplitude is of order zero. -/
  velocity : ∀ α, IsWeightedAmplitude I 0 (vamp vv α)
  /-- The metric amplitude is symmetric. -/
  symm : ∀ t ξ α β, hh t ξ α β = hh t ξ β α
  /-- The metric amplitude is Hermitian. -/
  herm_metric : ∀ α β, IsHermitian I (amp hh α β)
  /-- The density amplitude is Hermitian. -/
  herm_density : IsHermitian I dd
  /-- The velocity amplitude is Hermitian. -/
  herm_velocity : ∀ α, IsHermitian I (vamp vv α)

theorem dsym_eq_partialSymbol (c : Fin 4) (G : ℝ → E3 → ℂ) : dsym c G = partialSymbol c G := rfl

variable {I : Set ℝ} {G : ℝ → E3 → ℂ} {z : E}

theorem isWeightedAmplitude_dsym {k : ℕ} (hI : IsOpen I) (hG : IsWeightedAmplitude I (k + 1) G)
    (c : Fin 4) :
    IsWeightedAmplitude I k (dsym c G) :=
  hG.partialSymbol hI c

/-- **The derivatives of a real synthesized field** of a weighted amplitude of order one are the
syntheses of the symbols. -/
theorem ofReal_fderiv_re_of_isAmplitude (hI : IsOpen I) (hG : IsWeightedAmplitude I 1 G)
    (hH : IsHermitian I G) (hz : z ∈ slab I) (c : Fin 4) :
    ((fderiv ℝ (fun w => (synthesis G w).re) z (Pi.single c 1) : ℝ) : ℂ) =
      synthesis (dsym c G) z := by
  rw [fderiv_re (hG.differentiableAt_synthesis hI hz), hG.fderiv_synthesis_single hI hz c]
  exact ofReal_re_synthesis fun ξ => hG.isHermitian_partialSymbol hI hH c (z 0) hz ξ

variable {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {hh : ℝ → E3 → Mat3 ℂ} {dd : ℝ → E3 → ℂ}
  {vv : ℝ → E3 → Fin 3 → ℂ}

namespace IsWeightedData

theorem ofReal_fieldOf (hD : IsWeightedData B.I hh dd vv) (hz : z ∈ slab B.I) (α β : Fin 3) :
    ((fieldOf hh z α β : ℝ) : ℂ) = synthesis (amp hh α β) z :=
  ofReal_re_synthesis fun ξ => hD.herm_metric α β (z 0) hz ξ

theorem ofReal_scalarOf (hD : IsWeightedData B.I hh dd vv) (hz : z ∈ slab B.I) :
    ((scalarOf dd z : ℝ) : ℂ) = synthesis dd z :=
  ofReal_re_synthesis fun ξ => hD.herm_density (z 0) hz ξ

theorem ofReal_vectorOf (hD : IsWeightedData B.I hh dd vv) (hz : z ∈ slab B.I) (α : Fin 3) :
    ((vectorOf vv z α : ℝ) : ℂ) = synthesis (vamp vv α) z :=
  ofReal_re_synthesis fun ξ => hD.herm_velocity α (z 0) hz ξ

theorem ofReal_dh_fieldOf (hD : IsWeightedData B.I hh dd vv) (hz : z ∈ slab B.I) (c : Fin 4)
    (α β : Fin 3) :
    ((dh (fieldOf hh) c z α β : ℝ) : ℂ) = synthesis (dsym c (amp hh α β)) z :=
  ofReal_fderiv_re_of_isAmplitude B.isOpen_I ((hD.metric α β).mono (by omega))
    (hD.herm_metric α β) hz c

theorem ofReal_ddh_fieldOf (hD : IsWeightedData B.I hh dd vv) (hz : z ∈ slab B.I)
    (c e : Fin 4) (α β : Fin 3) :
    ((ddh (fieldOf hh) c e z α β : ℝ) : ℂ) = synthesis (dsym c (dsym e (amp hh α β))) z := by
  have hev : (fun w => dh (fieldOf hh) e w α β) =ᶠ[𝓝 z]
      fun w => (synthesis (dsym e (amp hh α β)) w).re :=
    eventually_of_mem ((isOpen_slab B.isOpen_I).mem_nhds hz) fun w hw => by
      show dh (fieldOf hh) e w α β = (synthesis (dsym e (amp hh α β)) w).re
      rw [← hD.ofReal_dh_fieldOf hw e α β, Complex.ofReal_re]
  rw [ddh, hev.fderiv_eq]
  exact ofReal_fderiv_re_of_isAmplitude B.isOpen_I
    (isWeightedAmplitude_dsym B.isOpen_I (hD.metric α β) e)
    (((hD.metric α β).mono (by omega)).isHermitian_partialSymbol B.isOpen_I
      (hD.herm_metric α β) e) hz c

theorem isWeightedAmplitude_jetAmp (hD : IsWeightedData B.I hh dd vv) (j : JetIdx) :
    IsWeightedAmplitude B.I 0 (jetAmp hh dd vv j) := by
  cases j with
  | second c e α β =>
    exact isWeightedAmplitude_dsym B.isOpen_I
      (isWeightedAmplitude_dsym B.isOpen_I (hD.metric α β) e) c
  | first c α β =>
    exact isWeightedAmplitude_dsym B.isOpen_I ((hD.metric α β).mono (by omega)) c
  | value α β => exact (hD.metric α β).mono (by omega)
  | density => exact hD.density
  | velocity α => exact hD.velocity α

theorem realJet_eq (hD : IsWeightedData B.I hh dd vv) (hz : z ∈ slab B.I) :
    realJet (fieldOf hh) (scalarOf dd) (vectorOf vv) z =
      fun j => synthesis (jetAmp hh dd vv j) z := by
  funext j
  cases j with
  | second c e α β => exact hD.ofReal_ddh_fieldOf hz c e α β
  | first c α β => exact hD.ofReal_dh_fieldOf hz c α β
  | value α β => exact hD.ofReal_fieldOf hz α β
  | density => exact hD.ofReal_scalarOf hz
  | velocity α => exact hD.ofReal_vectorOf hz α

theorem mixedForm_jetAmp (hD : IsWeightedData B.I hh dd vv) {t : ℝ} (ht : t ∈ B.I) (ξ : E3)
    (α : Fin 3) :
    mixedForm κ ρ t α (fun j => jetAmp hh dd vv j t ξ) =
      resMixed (fourierCoeffs B κ ρ t) (wave ξ) (jet1 hh t ξ) (vv t ξ) α := by
  have h (γ δ ε : Fin 3) : dsym 0 (dsym γ.succ (amp hh δ ε)) t ξ =
      2 * Real.pi * ξ γ * Complex.I * timeDeriv (amp hh δ ε) t ξ := by
    rw [dsym_zero, dsym_succ]
    exact ((hD.metric δ ε).mono (by omega)).timeDeriv_mul_left (k := 0) ht
      (fun ξ => 2 * Real.pi * ξ γ * Complex.I) ξ
  simp only [mixedForm, LinearMap.coe_mk, AddHom.coe_mk, jetAmp]
  simp only [h]
  simp only [dsym_succ, dsym_zero, resMixed, fourierCoeffs,
    ScalarVectorTensor.mix_apply, ScalarVectorTensor.contract, ScalarVectorTensor.trace, jet1, wave,
    vamp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  push_cast
  ring

/-- The synthesis of a form of the jets is the form of the syntheses. -/
theorem synthesis_form (hD : IsWeightedData B.I hh dd vv) (hz : z ∈ slab B.I)
    (Λ : ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ) :
    synthesis (fun t ξ => Λ t fun j => jetAmp hh dd vv j t ξ) z =
      Λ (z 0) (realJet (fieldOf hh) (scalarOf dd) (vectorOf vv) z) := by
  rw [synthesis_linearMap Λ (jetAmp hh dd vv)
    (fun j => integrable_synthesisIntegrand ((hD.isWeightedAmplitude_jetAmp j).integrable hz)),
    hD.realJet_eq hz]

theorem integrable_form (hD : IsWeightedData B.I hh dd vv) {t : ℝ} (ht : t ∈ B.I)
    (Λ : ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ) :
    Integrable fun ξ => Λ t fun j => jetAmp hh dd vv j t ξ := by
  have e : (fun ξ => Λ t fun j => jetAmp hh dd vv j t ξ) = fun ξ =>
      ∑ i, jetAmp hh dd vv i t ξ * Λ t (fun j => if i = j then 1 else 0) := by
    funext ξ
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp only [smul_eq_mul]
  rw [e]
  exact integrable_finsetSum _ fun i _ =>
    ((hD.isWeightedAmplitude_jetAmp i).integrable ht).mul_const _

/-- At a time of `I`, a form of the jets of the amplitudes vanishes for almost every frequency if
and only if its synthesis vanishes at every point of that time. -/
theorem form_eq_zero_iff (hD : IsWeightedData B.I hh dd vv) {t : ℝ} (ht : t ∈ B.I)
    (Λ : ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ) :
    (∀ x : E3, synthesis (fun s ξ => Λ s fun j => jetAmp hh dd vv j s ξ)
        (spacetimePoint t x) = 0) ↔
      ∀ᵐ ξ, Λ t (fun j => jetAmp hh dd vv j t ξ) = 0 := by
  constructor
  · intro h
    exact ae_eq_zero_of_synthesis_eq_zero' (G := fun s ξ => Λ s fun j => jetAmp hh dd vv j s ξ)
      (hD.integrable_form ht Λ) h
  · intro h x
    rw [synthesis_eq]
    refine integral_eq_zero_of_ae (h.mono fun ξ hξ => ?_)
    simp only [synthesisIntegrand, spacetimePoint_zero, Pi.zero_apply]
    rw [hξ, mul_zero]

/-- **The linearized Einstein equations of a perturbation given by weighted Fourier data hold if
and only if, at every time, almost every frequency satisfies the mode equations.** -/
theorem linearizedEinsteinDust_iff (hD : IsWeightedData B.I hh dd vv) :
    LinearizedEinsteinDust B κ ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) ↔
      ∀ t ∈ B.I, ∀ᵐ ξ, FrequencyEq B κ ρ hh dd vv t ξ := by
  have hpt (t : ℝ) (ht : t ∈ B.I) (x : E3) : spacetimePoint t x ∈ slab B.I := ht
  have key (Λ : ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ) (r : E → ℝ)
      (hr : ∀ z ∈ slab B.I, (r z : ℂ) = Λ (z 0)
        (realJet (fieldOf hh) (scalarOf dd) (vectorOf vv) z)) :
      (∀ z ∈ slab B.I, r z = 0) ↔
        ∀ t ∈ B.I, ∀ᵐ ξ, Λ t (fun j => jetAmp hh dd vv j t ξ) = 0 := by
    constructor
    · intro h t ht
      refine (hD.form_eq_zero_iff ht Λ).mp fun x => ?_
      rw [hD.synthesis_form (hpt t ht x), ← hr _ (hpt t ht x), h _ (hpt t ht x),
        Complex.ofReal_zero]
    · intro h z hz
      have h0 := (hD.form_eq_zero_iff hz Λ).mpr (h (z 0) hz) (spatialPoint z)
      rw [spacetimePoint_eq, hD.synthesis_form hz, ← hr z hz] at h0
      exact_mod_cast h0
  have hT := key (timeForm B κ ρ) (fun z => linRicci B (fieldOf hh) z 0 0 -
    κ * linDust B ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) z 0 0)
    fun z _ => residual_time _ _ _ z
  have hM (α : Fin 3) := key (fun t => mixedForm κ ρ t α) (fun z =>
    linRicci B (fieldOf hh) z 0 α.succ -
      κ * linDust B ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) z 0 α.succ)
    fun z _ => (residual_mixed _ _ _ z α).1
  have hM' (α : Fin 3) := key (fun t => mixedForm κ ρ t α) (fun z =>
    linRicci B (fieldOf hh) z α.succ 0 -
      κ * linDust B ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) z α.succ 0)
    fun z _ => (residual_mixed _ _ _ z α).2
  have hS (α β : Fin 3) := key (fun t => spaceForm B κ ρ t α β) (fun z =>
    linRicci B (fieldOf hh) z α.succ β.succ -
      κ * linDust B ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) z α.succ β.succ)
    fun z _ => residual_space _ _ _ z α β
  have hL : LinearizedEinsteinDust B κ ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) ↔
      (∀ z ∈ slab B.I, linRicci B (fieldOf hh) z 0 0 -
          κ * linDust B ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) z 0 0 = 0) ∧
        (∀ α : Fin 3, ∀ z ∈ slab B.I, linRicci B (fieldOf hh) z 0 α.succ -
          κ * linDust B ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) z 0 α.succ = 0) ∧
        (∀ α : Fin 3, ∀ z ∈ slab B.I, linRicci B (fieldOf hh) z α.succ 0 -
          κ * linDust B ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) z α.succ 0 = 0) ∧
        ∀ α β : Fin 3, ∀ z ∈ slab B.I, linRicci B (fieldOf hh) z α.succ β.succ -
          κ * linDust B ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) z α.succ β.succ = 0 := by
    simp only [LinearizedEinsteinDust, ← domain_eq_slab B, SetLike.mem_coe, sub_eq_zero]
    constructor
    · intro h
      exact ⟨fun z hz => h z hz 0 0, fun α z hz => h z hz 0 α.succ,
        fun α z hz => h z hz α.succ 0, fun α β z hz => h z hz α.succ β.succ⟩
    · rintro ⟨h0, h1, h2, h3⟩ z hz i k
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨β, rfl⟩
      · exact h0 z hz
      · exact h1 β z hz
      · exact h2 α z hz
      · exact h3 α β z hz
  rw [hL, hT]
  simp only [hM, hM', hS]
  constructor
  · rintro ⟨h0, h1, -, h3⟩ t ht
    have a1 : ∀ᵐ ξ, ∀ α, mixedForm κ ρ t α (fun j => jetAmp hh dd vv j t ξ) = 0 :=
      ae_all_iff.2 fun α => h1 α t ht
    have a3 : ∀ᵐ ξ, ∀ α β, spaceForm B κ ρ t α β (fun j => jetAmp hh dd vv j t ξ) = 0 :=
      ae_all_iff.2 fun α => ae_all_iff.2 fun β => h3 α β t ht
    filter_upwards [h0 t ht, a1, a3] with ξ e0 e1 e3
    refine ⟨?_, funext fun α => ?_, funext fun α => funext fun β => ?_⟩
    · rw [← timeForm_jetAmp]; exact e0
    · rw [← hD.mixedForm_jetAmp ht]; exact e1 α
    · rw [← spaceForm_jetAmp]; exact e3 α β
  · intro h
    refine ⟨fun t ht => ?_, fun α t ht => ?_, fun α t ht => ?_, fun α β t ht => ?_⟩
    · filter_upwards [h t ht] with ξ hξ
      rw [timeForm_jetAmp]; exact hξ.1
    · filter_upwards [h t ht] with ξ hξ
      rw [hD.mixedForm_jetAmp ht]; exact congrFun hξ.2.1 α
    · filter_upwards [h t ht] with ξ hξ
      rw [hD.mixedForm_jetAmp ht]; exact congrFun hξ.2.1 α
    · filter_upwards [h t ht] with ξ hξ
      rw [spaceForm_jetAmp]; exact congrFun (congrFun hξ.2.2 α) β

end IsWeightedData

/-! ### The projections of weighted data -/

theorem wave_smul (c : ℝ) (ξ : E3) : wave (c • ξ) = (c : ℂ) • wave ξ := by
  funext γ
  simp only [wave, PiLp.smul_apply, smul_eq_mul, Pi.smul_apply]
  push_cast; ring

/-- A linear map of the matrices that depends on the direction of `ξ` alone and is continuous in
`ξ ≠ 0` maps weighted amplitudes of order `k` to weighted amplitudes of order `k`. -/
theorem isWeightedAmplitude_linearMap {k : ℕ} (hI : IsOpen I) (L : E3 → Mat3 ℂ →ₗ[ℂ] Mat3 ℂ)
    (hL : ∀ γ δ α β, ContinuousOn (fun ξ => L ξ (Pi.single γ (Pi.single δ 1)) α β) nonzero)
    (hs : ∀ c : ℝ, 0 < c → ∀ ξ, L (c • ξ) = L ξ) (hG : ∀ γ δ, IsWeightedAmplitude I k (amp hh γ δ))
    (α β : Fin 3) : IsWeightedAmplitude I k (fun t ξ => L ξ (hh t ξ) α β) := by
  let m : Fin 3 × Fin 3 → E3 → ℂ := fun i ξ => L ξ (Pi.single i.1 (Pi.single i.2 1)) α β
  have hb (i : Fin 3 × Fin 3) : ∃ C, ∀ ξ, ‖m i ξ‖ ≤ C :=
    exists_bound_of_scale_invariant (hL i.1 i.2 α β) fun c hc ξ => by simp only [m, hs c hc ξ]
  choose C hC using hb
  have h := IsWeightedAmplitude.linComb (p := 0) (C := ∑ i, |C i|) hI (m := m)
    (G := fun i => amp hh i.1 i.2)
    (fun i => aestronglyMeasurable_of_continuousOn_ne_zero (hL i.1 i.2 α β))
    (fun i ξ => by
      rw [pow_zero, mul_one]
      exact (hC i ξ).trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i))))
    (fun i => hG i.1 i.2)
  have e : (fun t ξ => L ξ (hh t ξ) α β) = fun t ξ =>
      ∑ i : Fin 3 × Fin 3, m i ξ * amp hh i.1 i.2 t ξ := by
    funext t ξ
    rw [ScalarVectorTensor.linearMap_apply_eq_sum, Fintype.sum_prod_type]
    simp only [m, amp, mul_comm]
  rw [e]
  exact h

/-- The same for linear maps of the vectors. -/
theorem isWeightedAmplitude_linearMap_vec {k : ℕ} (hI : IsOpen I)
    (L : E3 → (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))
    (hL : ∀ γ α, ContinuousOn (fun ξ => L ξ (Pi.single γ 1) α) nonzero)
    (hs : ∀ c : ℝ, 0 < c → ∀ ξ, L (c • ξ) = L ξ) (hG : ∀ γ, IsWeightedAmplitude I k (vamp vv γ))
    (α : Fin 3) : IsWeightedAmplitude I k (fun t ξ => L ξ (vv t ξ) α) := by
  let m : Fin 3 → E3 → ℂ := fun γ ξ => L ξ (Pi.single γ 1) α
  have hb (γ : Fin 3) : ∃ C, ∀ ξ, ‖m γ ξ‖ ≤ C :=
    exists_bound_of_scale_invariant (hL γ α) fun c hc ξ => by simp only [m, hs c hc ξ]
  choose C hC using hb
  have h := IsWeightedAmplitude.linComb (p := 0) (C := ∑ i, |C i|) hI (m := m)
    (G := fun γ => vamp vv γ)
    (fun γ => aestronglyMeasurable_of_continuousOn_ne_zero (hL γ α))
    (fun γ ξ => by
      rw [pow_zero, mul_one]
      exact (hC γ ξ).trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ γ))))
    hG
  have e : (fun t ξ => L ξ (vv t ξ) α) = fun t ξ => ∑ γ, m γ ξ * vamp vv γ t ξ := by
    funext t ξ
    rw [ScalarVectorTensor.linearMap_vec_apply_eq_sum]
    simp only [m, vamp, mul_comm]
  rw [e]
  exact h

theorem scalarPart_wave_smul {c : ℝ} (hc : 0 < c) (ξ : E3) :
    scalarPart (wave (c • ξ)) = scalarPart (wave ξ) := by
  rw [wave_smul]
  exact ScalarVectorTensor.scalarPart_smul_left _ (Complex.ofReal_ne_zero.mpr hc.ne')

theorem vectorPart_wave_smul {c : ℝ} (hc : 0 < c) (ξ : E3) :
    vectorPart (wave (c • ξ)) = vectorPart (wave ξ) := by
  rw [wave_smul]
  exact ScalarVectorTensor.vectorPart_smul_left _ (Complex.ofReal_ne_zero.mpr hc.ne')

theorem tensorPart_wave_smul {c : ℝ} (hc : 0 < c) (ξ : E3) :
    tensorPart (wave (c • ξ)) = tensorPart (wave ξ) := by
  rw [wave_smul]
  exact ScalarVectorTensor.tensorPart_smul_left _ (Complex.ofReal_ne_zero.mpr hc.ne')

theorem longVec_wave_smul {c : ℝ} (hc : 0 < c) (ξ : E3) :
    longVec (wave (c • ξ)) = longVec (wave ξ) := by
  rw [wave_smul]
  exact ScalarVectorTensor.longVec_smul_left _ (Complex.ofReal_ne_zero.mpr hc.ne')

theorem transVec_wave_smul {c : ℝ} (hc : 0 < c) (ξ : E3) :
    transVec (wave (c • ξ)) = transVec (wave ξ) := by
  rw [wave_smul]
  exact ScalarVectorTensor.transVec_smul_left _ (Complex.ofReal_ne_zero.mpr hc.ne')

namespace IsWeightedData

/-- **The parts of weighted data are weighted data.** -/
theorem isWeightedData_scalar (hD : IsWeightedData B.I hh dd vv) :
    IsWeightedData B.I (scalarData hh) dd (longData vv) where
  metric α β := isWeightedAmplitude_linearMap B.isOpen_I (fun ξ => scalarPart (wave ξ))
    (fun γ δ α β => (contDiffOn_scalarPart_wave _ α β).continuousOn)
    (fun _ hc ξ => scalarPart_wave_smul hc ξ) hD.metric α β
  density := hD.density
  velocity α := isWeightedAmplitude_linearMap_vec B.isOpen_I (fun ξ => longVec (wave ξ))
    (fun γ α => (contDiffOn_longVec_wave _ α).continuousOn)
    (fun _ hc ξ => longVec_wave_smul hc ξ) hD.velocity α
  symm t ξ α β := ScalarVectorTensor.scalarPart_symm _ _ α β
  herm_metric α β t ht ξ := by
    have e : hh t (-ξ) = fun γ δ => conj (hh t ξ γ δ) :=
      funext fun γ => funext fun δ => hD.herm_metric γ δ t ht ξ
    simp only [amp, scalarData, wave_neg, ScalarVectorTensor.scalarPart_neg, e]
    exact ScalarVectorTensor.scalarPart_map _ (starRingEnd ℂ) (conj_wave ξ) α β
  herm_density := hD.herm_density
  herm_velocity α t ht ξ := by
    have e : vv t (-ξ) = fun γ => conj (vv t ξ γ) :=
      funext fun γ => hD.herm_velocity γ t ht ξ
    simp only [vamp, longData, wave_neg, ScalarVectorTensor.longVec_neg, e]
    exact ScalarVectorTensor.longVec_map _ (starRingEnd ℂ) (conj_wave ξ) α

theorem isWeightedData_vector (hD : IsWeightedData B.I hh dd vv) :
    IsWeightedData B.I (vectorData hh) (fun _ _ => 0) (transData vv) where
  metric α β := isWeightedAmplitude_linearMap B.isOpen_I (fun ξ => vectorPart (wave ξ))
    (fun γ δ α β => (contDiffOn_vectorPart_wave _ α β).continuousOn)
    (fun _ hc ξ => vectorPart_wave_smul hc ξ) hD.metric α β
  density := .const aestronglyMeasurable_const (by simp)
  velocity α := isWeightedAmplitude_linearMap_vec B.isOpen_I (fun ξ => transVec (wave ξ))
    (fun γ α => (contDiffOn_transVec_wave _ α).continuousOn)
    (fun _ hc ξ => transVec_wave_smul hc ξ) hD.velocity α
  symm t ξ α β := ScalarVectorTensor.vectorPart_symm _ _ α β
  herm_metric α β t ht ξ := by
    have e : hh t (-ξ) = fun γ δ => conj (hh t ξ γ δ) :=
      funext fun γ => funext fun δ => hD.herm_metric γ δ t ht ξ
    simp only [amp, vectorData, wave_neg, ScalarVectorTensor.vectorPart_neg, e]
    exact ScalarVectorTensor.vectorPart_map _ (starRingEnd ℂ) (conj_wave ξ) α β
  herm_density _ _ _ := by simp
  herm_velocity α t ht ξ := by
    have e : vv t (-ξ) = fun γ => conj (vv t ξ γ) :=
      funext fun γ => hD.herm_velocity γ t ht ξ
    simp only [vamp, transData, wave_neg, ScalarVectorTensor.transVec_neg, e]
    exact ScalarVectorTensor.transVec_map _ (starRingEnd ℂ) (conj_wave ξ) α

theorem isWeightedData_tensor (hD : IsWeightedData B.I hh dd vv) :
    IsWeightedData B.I (tensorData hh) (fun _ _ => 0) (fun _ _ _ => 0) where
  metric α β := isWeightedAmplitude_linearMap B.isOpen_I (fun ξ => tensorPart (wave ξ))
    (fun γ δ α β => (contDiffOn_tensorPart_wave _ α β).continuousOn)
    (fun _ hc ξ => tensorPart_wave_smul hc ξ) hD.metric α β
  density := .const aestronglyMeasurable_const (by simp)
  velocity _ := .const aestronglyMeasurable_const (by simp)
  symm t ξ α β := ScalarVectorTensor.tensorPart_symm _ _ (hD.symm t ξ) α β
  herm_metric α β t ht ξ := by
    have e : hh t (-ξ) = fun γ δ => conj (hh t ξ γ δ) :=
      funext fun γ => funext fun δ => hD.herm_metric γ δ t ht ξ
    simp only [amp, tensorData, wave_neg, ScalarVectorTensor.tensorPart_neg, e]
    exact ScalarVectorTensor.tensorPart_map _ (starRingEnd ℂ) (conj_wave ξ) α β
  herm_density _ _ _ := by simp
  herm_velocity _ _ _ _ := by simp [vamp]

theorem timeDeriv_linearMap (hD : IsWeightedData B.I hh dd vv) (L : E3 → Mat3 ℂ →ₗ[ℂ] Mat3 ℂ)
    {t : ℝ} (ht : t ∈ B.I) (ξ : E3) (α β : Fin 3) :
    timeDeriv (fun t ξ => L ξ (hh t ξ) α β) t ξ = L ξ (jet1 hh t ξ) α β :=
  (hasDerivAt_linearMap_apply (L ξ) (fun γ δ => (show HasDerivAt (fun s => hh s ξ γ δ)
    (jet1 hh t ξ γ δ) t from (hD.metric γ δ).hasDerivAt 0 (by omega) t ht ξ)) α β).deriv

theorem timeDeriv_timeDeriv_linearMap (hD : IsWeightedData B.I hh dd vv)
    (L : E3 → Mat3 ℂ →ₗ[ℂ] Mat3 ℂ) {t : ℝ} (ht : t ∈ B.I) (ξ : E3) (α β : Fin 3) :
    timeDeriv (timeDeriv fun t ξ => L ξ (hh t ξ) α β) t ξ = L ξ (jet2 hh t ξ) α β := by
  have hev : (fun s => timeDeriv (fun t ξ => L ξ (hh t ξ) α β) s ξ) =ᶠ[𝓝 t]
      fun s => L ξ (jet1 hh s ξ) α β :=
    eventually_of_mem (B.isOpen_I.mem_nhds ht) fun s hs => hD.timeDeriv_linearMap L hs ξ α β
  simp only [timeDeriv] at hev ⊢
  rw [hev.deriv_eq]
  exact (hasDerivAt_linearMap_apply (L ξ) (fun γ δ => (show HasDerivAt (fun s => jet1 hh s ξ γ δ)
    (jet2 hh t ξ γ δ) t from (hD.metric γ δ).hasDerivAt 1 (by omega) t ht ξ)) α β).deriv

theorem jet1_linearMap (hD : IsWeightedData B.I hh dd vv) (L : E3 → Mat3 ℂ →ₗ[ℂ] Mat3 ℂ)
    {t : ℝ} (ht : t ∈ B.I) (ξ : E3) :
    jet1 (fun t ξ => L ξ (hh t ξ)) t ξ = L ξ (jet1 hh t ξ) :=
  funext fun α => funext fun β => hD.timeDeriv_linearMap L ht ξ α β

theorem jet2_linearMap (hD : IsWeightedData B.I hh dd vv) (L : E3 → Mat3 ℂ →ₗ[ℂ] Mat3 ℂ)
    {t : ℝ} (ht : t ∈ B.I) (ξ : E3) :
    jet2 (fun t ξ => L ξ (hh t ξ)) t ξ = L ξ (jet2 hh t ξ) :=
  funext fun α => funext fun β => hD.timeDeriv_timeDeriv_linearMap L ht ξ α β

/-- **The decomposition of the equations of one nonzero frequency** into those of the scalar,
vector and tensor parts. -/
theorem frequencyEq_iff_split (hD : IsWeightedData B.I hh dd vv) {t : ℝ} (ht : t ∈ B.I)
    {ξ : E3} (hξ : ξ ≠ 0) :
    FrequencyEq B κ ρ hh dd vv t ξ ↔
      FrequencyEq B κ ρ (scalarData hh) dd (longData vv) t ξ ∧
      FrequencyEq B κ ρ (vectorData hh) (fun _ _ => 0) (transData vv) t ξ ∧
      FrequencyEq B κ ρ (tensorData hh) (fun _ _ => 0) (fun _ _ _ => 0) t ξ := by
  have s1 : jet1 (scalarData hh) t ξ = scalarPart (wave ξ) (jet1 hh t ξ) :=
    hD.jet1_linearMap (fun ξ => scalarPart (wave ξ)) ht ξ
  have s2 : jet2 (scalarData hh) t ξ = scalarPart (wave ξ) (jet2 hh t ξ) :=
    hD.jet2_linearMap (fun ξ => scalarPart (wave ξ)) ht ξ
  have v1 : jet1 (vectorData hh) t ξ = vectorPart (wave ξ) (jet1 hh t ξ) :=
    hD.jet1_linearMap (fun ξ => vectorPart (wave ξ)) ht ξ
  have v2 : jet2 (vectorData hh) t ξ = vectorPart (wave ξ) (jet2 hh t ξ) :=
    hD.jet2_linearMap (fun ξ => vectorPart (wave ξ)) ht ξ
  have t1 : jet1 (tensorData hh) t ξ = tensorPart (wave ξ) (jet1 hh t ξ) :=
    hD.jet1_linearMap (fun ξ => tensorPart (wave ξ)) ht ξ
  have t2 : jet2 (tensorData hh) t ξ = tensorPart (wave ξ) (jet2 hh t ξ) :=
    hD.jet2_linearMap (fun ξ => tensorPart (wave ξ)) ht ξ
  simp only [FrequencyEq, s1, s2, v1, v2, t1, t2]
  exact ScalarVectorTensor.symbolEq_iff _ _ _ _ _ _ (nsq_wave_ne_zero hξ)

/-- **The scalar–vector–tensor decomposition of the linearized equations** for weighted data: the
perturbation solves the linearized Einstein equations with dust if and only if its scalar part
(with the density contrast and the longitudinal velocity), its vector part (with the transverse
velocity) and its tensor part do. -/
theorem linearizedEinsteinDust_iff_split (hD : IsWeightedData B.I hh dd vv) :
    LinearizedEinsteinDust B κ ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) ↔
      LinearizedEinsteinDust B κ ρ (fieldOf (scalarData hh)) (scalarOf dd)
          (vectorOf (longData vv)) ∧
        LinearizedEinsteinDust B κ ρ (fieldOf (vectorData hh)) (fun _ => 0)
          (vectorOf (transData vv)) ∧
        LinearizedEinsteinDust B κ ρ (fieldOf (tensorData hh)) (fun _ => 0) (fun _ _ => 0) := by
  have hS := hD.isWeightedData_scalar.linearizedEinsteinDust_iff (κ := κ) (ρ := ρ)
  have hV := hD.isWeightedData_vector.linearizedEinsteinDust_iff (κ := κ) (ρ := ρ)
  have hT := hD.isWeightedData_tensor.linearizedEinsteinDust_iff (κ := κ) (ρ := ρ)
  rw [scalarOf_zero] at hV hT
  rw [vectorOf_zero] at hT
  rw [hD.linearizedEinsteinDust_iff, hS, hV, hT]
  have h0 : ∀ᵐ ξ : E3, ξ ≠ 0 := Measure.ae_ne volume 0
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩ <;>
    filter_upwards [h t ht, h0] with ξ hξ hξ0
    · exact ((hD.frequencyEq_iff_split ht hξ0).mp hξ).1
    · exact ((hD.frequencyEq_iff_split ht hξ0).mp hξ).2.1
    · exact ((hD.frequencyEq_iff_split ht hξ0).mp hξ).2.2
  · rintro ⟨h1, h2, h3⟩ t ht
    filter_upwards [h1 t ht, h2 t ht, h3 t ht, h0] with ξ e1 e2 e3 hξ0
    exact (hD.frequencyEq_iff_split ht hξ0).mpr ⟨e1, e2, e3⟩

/-- **The perturbation is the sum of its scalar, vector and tensor parts.** -/
theorem fieldOf_eq_add (hD : IsWeightedData B.I hh dd vv) (hz : z ∈ slab B.I) (α β : Fin 3) :
    fieldOf hh z α β = fieldOf (scalarData hh) z α β + fieldOf (vectorData hh) z α β +
      fieldOf (tensorData hh) z α β := by
  have hS := (hD.isWeightedData_scalar.metric α β).integrable hz
  have hV := (hD.isWeightedData_vector.metric α β).integrable hz
  have hT := (hD.isWeightedData_tensor.metric α β).integrable hz
  have e : amp hh α β = fun t ξ => (amp (scalarData hh) α β t ξ + amp (vectorData hh) α β t ξ) +
      amp (tensorData hh) α β t ξ := by
    funext t ξ
    have := congrFun (congrFun
      (ScalarVectorTensor.scalarPart_add_vectorPart_add_tensorPart (wave ξ) (hh t ξ)) α) β
    simpa only [amp, scalarData, vectorData, tensorData, Pi.add_apply] using this.symm
  simp only [fieldOf]
  rw [e, synthesis_add (integrable_synthesisIntegrand (hS.add hV))
      (integrable_synthesisIntegrand hT),
    synthesis_add (integrable_synthesisIntegrand hS) (integrable_synthesisIntegrand hV)]
  simp only [Complex.add_re]

/-- The velocity is the sum of its longitudinal and transverse parts. -/
theorem vectorOf_eq_add (hD : IsWeightedData B.I hh dd vv) (hz : z ∈ slab B.I) (α : Fin 3) :
    vectorOf vv z α = vectorOf (longData vv) z α + vectorOf (transData vv) z α := by
  have hL := (hD.isWeightedData_scalar.velocity α).integrable hz
  have hT := (hD.isWeightedData_vector.velocity α).integrable hz
  have e : vamp vv α = fun t ξ => vamp (longData vv) α t ξ + vamp (transData vv) α t ξ := by
    funext t ξ
    have := congrFun (ScalarVectorTensor.longVec_add_transVec (wave ξ) (vv t ξ)) α
    simpa only [vamp, longData, transData, Pi.add_apply] using this.symm
  simp only [vectorOf]
  rw [e, synthesis_add (integrable_synthesisIntegrand hL) (integrable_synthesisIntegrand hT)]
  simp only [Complex.add_re]

/-- **Conversely, the transform of an integrable slice of a synthesized field is the data**,
almost everywhere. -/
theorem fourier_fieldOf_ae (hD : IsWeightedData B.I hh dd vv) {t : ℝ} (ht : t ∈ B.I)
    (α β : Fin 3) (hu : Integrable fun x : E3 => fieldOf hh (spacetimePoint t x) α β) :
    𝓕 (fun x : E3 => (fieldOf hh (spacetimePoint t x) α β : ℂ)) =ᵐ[volume]
      fun ξ => hh t ξ α β := by
  have e : (fun x : E3 => (fieldOf hh (spacetimePoint t x) α β : ℂ)) =
      fun x => synthesis (amp hh α β) (spacetimePoint t x) :=
    funext fun x => hD.ofReal_fieldOf (z := spacetimePoint t x) ht α β
  have hu' : Integrable fun x => synthesis (amp hh α β) (spacetimePoint t x) := by
    rw [← e]; exact hu.ofReal
  rw [e]
  exact fourier_synthesis_ae ((hD.metric α β).integrable ht) hu'

end IsWeightedData

/-! ### Reconstruction of a perturbation from its spatial Fourier transforms -/

/-- **A perturbation with an integrable spectrum**: at every time of `I` its spatial slices are
continuous and integrable, the metric perturbation is symmetric, and the spatial Fourier
transforms of the slices are weighted amplitudes, of order two for the metric and zero for the
density and the velocity. -/
structure HasIntegrableSpectrum (I : Set ℝ) (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ)
    (v : E → Fin 3 → ℝ) : Prop where
  /-- The slices of the metric perturbation are continuous. -/
  continuous_metric : ∀ t ∈ I, ∀ α β, Continuous fun x : E3 => h (spacetimePoint t x) α β
  /-- The slices of the metric perturbation are integrable. -/
  integrable_metric : ∀ t ∈ I, ∀ α β, Integrable fun x : E3 => h (spacetimePoint t x) α β
  /-- The slices of the density contrast are continuous. -/
  continuous_density : ∀ t ∈ I, Continuous fun x : E3 => δ (spacetimePoint t x)
  /-- The slices of the density contrast are integrable. -/
  integrable_density : ∀ t ∈ I, Integrable fun x : E3 => δ (spacetimePoint t x)
  /-- The slices of the velocity are continuous. -/
  continuous_velocity : ∀ t ∈ I, ∀ α, Continuous fun x : E3 => v (spacetimePoint t x) α
  /-- The slices of the velocity are integrable. -/
  integrable_velocity : ∀ t ∈ I, ∀ α, Integrable fun x : E3 => v (spacetimePoint t x) α
  /-- The metric perturbation is symmetric. -/
  symm : ∀ z α β, h z α β = h z β α
  /-- The transforms of the metric perturbation are of order two. -/
  metric : ∀ α β, IsWeightedAmplitude I 2 (amp (fourierMetric h) α β)
  /-- The transforms of the density contrast are of order zero. -/
  density : IsWeightedAmplitude I 0 (fourierScalar δ)
  /-- The transforms of the velocity are of order zero. -/
  velocity : ∀ α, IsWeightedAmplitude I 0 (vamp (fourierVector v) α)

variable {h : E → Fin 3 → Fin 3 → ℝ} {δ : E → ℝ} {v : E → Fin 3 → ℝ}

namespace HasIntegrableSpectrum

/-- The transforms of a perturbation with an integrable spectrum are weighted data. -/
theorem isWeightedData (hS : HasIntegrableSpectrum I h δ v) :
    IsWeightedData I (fourierMetric h) (fourierScalar δ) (fourierVector v) where
  metric := hS.metric
  density := hS.density
  velocity := hS.velocity
  symm t ξ α β := by simp only [fourierMetric, hS.symm _ α β]
  herm_metric α β t _ ξ :=
    fourier_neg_of_real _ (fun _ => Complex.conj_ofReal _) ξ
  herm_density t _ ξ := fourier_neg_of_real _ (fun _ => Complex.conj_ofReal _) ξ
  herm_velocity α t _ ξ := fourier_neg_of_real _ (fun _ => Complex.conj_ofReal _) ξ

/-- **Fourier inversion**: a perturbation with an integrable spectrum is the synthesis of its
transforms on the slab. -/
theorem eq_synthesis (hS : HasIntegrableSpectrum I h δ v) (hz : z ∈ slab I) :
    h z = fieldOf (fourierMetric h) z ∧ δ z = scalarOf (fourierScalar δ) z ∧
      v z = vectorOf (fourierVector v) z := by
  refine ⟨funext fun α => funext fun β => ?_, ?_, funext fun α => ?_⟩
  · have e := synthesis_fourier (fun w => (h w α β : ℂ)) (z := z)
      (Complex.continuous_ofReal.comp (hS.continuous_metric (z 0) hz α β))
      (hS.integrable_metric (z 0) hz α β).ofReal ((hS.metric α β).integrable hz)
    simp only [fieldOf]
    rw [show amp (fourierMetric h) α β = fun t => 𝓕 fun x : E3 => (h (spacetimePoint t x) α β : ℂ)
      from rfl, e, Complex.ofReal_re]
  · have e := synthesis_fourier (fun w => (δ w : ℂ)) (z := z)
      (Complex.continuous_ofReal.comp (hS.continuous_density (z 0) hz))
      (hS.integrable_density (z 0) hz).ofReal (hS.density.integrable hz)
    simp only [scalarOf]
    rw [show fourierScalar δ = fun t => 𝓕 fun x : E3 => (δ (spacetimePoint t x) : ℂ) from rfl, e,
      Complex.ofReal_re]
  · have e := synthesis_fourier (fun w => (v w α : ℂ)) (z := z)
      (Complex.continuous_ofReal.comp (hS.continuous_velocity (z 0) hz α))
      (hS.integrable_velocity (z 0) hz α).ofReal ((hS.velocity α).integrable hz)
    simp only [vectorOf]
    rw [show vamp (fourierVector v) α = fun t => 𝓕 fun x : E3 => (v (spacetimePoint t x) α : ℂ)
      from rfl, e, Complex.ofReal_re]

/-- A perturbation with an integrable spectrum solves the linearized equations if and only if at
every time almost every frequency of its transforms satisfies the mode equations. -/
theorem linearizedEinsteinDust_iff (hS : HasIntegrableSpectrum B.I h δ v) :
    LinearizedEinsteinDust B κ ρ h δ v ↔ ∀ t ∈ B.I, ∀ᵐ ξ,
      FrequencyEq B κ ρ (fourierMetric h) (fourierScalar δ) (fourierVector v) t ξ := by
  rw [linearizedEinsteinDust_congr (h' := fieldOf (fourierMetric h))
    (δ' := scalarOf (fourierScalar δ)) (v' := vectorOf (fourierVector v))
    (fun z hz => (hS.eq_synthesis (by rwa [← domain_eq_slab])).1)
    (fun z hz => (hS.eq_synthesis (by rwa [← domain_eq_slab])).2.1)
    (fun z hz => (hS.eq_synthesis (by rwa [← domain_eq_slab])).2.2)]
  exact hS.isWeightedData.linearizedEinsteinDust_iff

/-- **The reconstruction**: a perturbation with an integrable spectrum is the sum of the
syntheses of its scalar, vector and tensor components, and it solves the linearized equations if
and only if each component does. -/
theorem reconstruction (hS : HasIntegrableSpectrum B.I h δ v) :
    (∀ z ∈ domain B.toData, ∀ α β, h z α β = fieldOf (scalarData (fourierMetric h)) z α β +
      fieldOf (vectorData (fourierMetric h)) z α β +
        fieldOf (tensorData (fourierMetric h)) z α β) ∧
    (∀ z ∈ domain B.toData, ∀ α, v z α = vectorOf (longData (fourierVector v)) z α +
      vectorOf (transData (fourierVector v)) z α) ∧
    (LinearizedEinsteinDust B κ ρ h δ v ↔
      LinearizedEinsteinDust B κ ρ (fieldOf (scalarData (fourierMetric h))) δ
          (vectorOf (longData (fourierVector v))) ∧
        LinearizedEinsteinDust B κ ρ (fieldOf (vectorData (fourierMetric h))) (fun _ => 0)
          (vectorOf (transData (fourierVector v))) ∧
        LinearizedEinsteinDust B κ ρ (fieldOf (tensorData (fourierMetric h))) (fun _ => 0)
          (fun _ _ => 0)) := by
  have hD := hS.isWeightedData
  have hz' (z : E) (hz : z ∈ domain B.toData) : z ∈ slab B.I := by rwa [← domain_eq_slab]
  refine ⟨fun z hz α β => ?_, fun z hz α => ?_, ?_⟩
  · rw [(hS.eq_synthesis (hz' z hz)).1]
    exact hD.fieldOf_eq_add (hz' z hz) α β
  · rw [(hS.eq_synthesis (hz' z hz)).2.2]
    exact hD.vectorOf_eq_add (hz' z hz) α
  · rw [linearizedEinsteinDust_congr (h' := fieldOf (fourierMetric h))
      (δ' := scalarOf (fourierScalar δ)) (v' := vectorOf (fourierVector v))
      (fun z hz => (hS.eq_synthesis (hz' z hz)).1)
      (fun z hz => (hS.eq_synthesis (hz' z hz)).2.1)
      (fun z hz => (hS.eq_synthesis (hz' z hz)).2.2),
      hD.linearizedEinsteinDust_iff_split,
      linearizedEinsteinDust_congr (h := fieldOf (scalarData (fourierMetric h)))
        (h' := fieldOf (scalarData (fourierMetric h))) (δ := scalarOf (fourierScalar δ))
        (δ' := δ) (v := vectorOf (longData (fourierVector v)))
        (v' := vectorOf (longData (fourierVector v))) (fun _ _ => rfl)
        (fun z hz => (hS.eq_synthesis (hz' z hz)).2.1.symm) (fun _ _ => rfl)]

end HasIntegrableSpectrum

/-! ### Instances beyond the compact spectrum -/

/-- A smooth bump `φ ≥ 0` on `ℝ³`, equal to `1` on the unit ball and supported in the ball of
radius `2`. -/
def unitBump : ContDiffBump (0 : E3) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump as a complex function. -/
def bumpProfile (x : E3) : ℂ := (unitBump x : ℂ)

theorem contDiff_bumpProfile : ContDiff ℝ ∞ bumpProfile :=
  Complex.ofRealCLM.contDiff.comp unitBump.contDiff

theorem hasCompactSupport_bumpProfile : HasCompactSupport bumpProfile :=
  unitBump.hasCompactSupport.comp_left Complex.ofReal_zero

/-- The bump as a Schwartz function. -/
def bumpSchwartz : SchwartzMap E3 ℂ :=
  hasCompactSupport_bumpProfile.toSchwartzMap contDiff_bumpProfile

/-- The Fourier transform `F = 𝓕φ` of the bump. -/
def fourierBump : E3 → ℂ := 𝓕 bumpProfile

theorem fourierBump_eq : fourierBump = ⇑(𝓕 bumpSchwartz : SchwartzMap E3 ℂ) := by
  rw [SchwartzMap.fourier_coe]; rfl

/-- `F(0) = ∫ φ`. -/
theorem fourierBump_zero : fourierBump 0 = ((∫ x, unitBump x : ℝ) : ℂ) := by
  rw [fourierBump, Real.fourier_eq, ← integral_complex_ofReal]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul, bumpProfile]

/-- **The transform of the bump does not vanish at `ξ = 0`.** -/
theorem fourierBump_zero_ne_zero : fourierBump 0 ≠ 0 := by
  rw [fourierBump_zero, Complex.ofReal_ne_zero]
  exact unitBump.integral_pos.ne'

theorem continuous_fourierBump : Continuous fourierBump := by
  rw [fourierBump_eq]; exact (𝓕 bumpSchwartz : SchwartzMap E3 ℂ).continuous

theorem fourierBump_neg (ξ : E3) : fourierBump (-ξ) = conj (fourierBump ξ) :=
  fourier_neg_of_real _ (fun _ => Complex.conj_ofReal _) ξ

/-- The transform of the bump, constant in time, is a weighted amplitude of every order. -/
theorem isWeightedAmplitude_fourierBump (I : Set ℝ) (k : ℕ) :
    IsWeightedAmplitude I k (fun _ => fourierBump) :=
  IsWeightedAmplitude.const continuous_fourierBump.aestronglyMeasurable
    (by rw [fourierBump_eq]; exact integrable_one_add_norm_pow_mul _ k)

/-- The perturbation `h_{αβ}(t, x) = φ(x)` for all `α, β`. -/
def bumpMetric : E → Fin 3 → Fin 3 → ℝ := fun z _ _ => unitBump (spatialPoint z)

/-- The density contrast `δ(t, x) = φ(x)`. -/
def bumpScalar : E → ℝ := fun z => unitBump (spatialPoint z)

/-- The velocity `v_α(t, x) = φ(x)` for all `α`. -/
def bumpVector : E → Fin 3 → ℝ := fun z _ => unitBump (spatialPoint z)

theorem fourierMetric_bump (t : ℝ) (ξ : E3) (α β : Fin 3) :
    fourierMetric bumpMetric t ξ α β = fourierBump ξ := by
  simp [fourierMetric, bumpMetric, fourierBump]; rfl

theorem fourierScalar_bump (t : ℝ) : fourierScalar bumpScalar t = fourierBump := by
  simp [fourierScalar, bumpScalar, fourierBump]; rfl

theorem fourierVector_bump (t : ℝ) (ξ : E3) (α : Fin 3) :
    fourierVector bumpVector t ξ α = fourierBump ξ := by
  simp [fourierVector, bumpVector, fourierBump]; rfl

/-- **An instance with Schwartz slices**: the bump perturbation has an integrable spectrum. -/
theorem hasIntegrableSpectrum_bump (I : Set ℝ) :
    HasIntegrableSpectrum I bumpMetric bumpScalar bumpVector where
  continuous_metric _ _ _ _ := by simpa [bumpMetric] using unitBump.continuous
  integrable_metric _ _ _ _ := by simpa [bumpMetric] using unitBump.integrable
  continuous_density _ _ := by simpa [bumpScalar] using unitBump.continuous
  integrable_density _ _ := by simpa [bumpScalar] using unitBump.integrable
  continuous_velocity _ _ _ := by simpa [bumpVector] using unitBump.continuous
  integrable_velocity _ _ _ := by simpa [bumpVector] using unitBump.integrable
  symm _ _ _ := rfl
  metric α β := by
    rw [show amp (fourierMetric bumpMetric) α β = fun _ => fourierBump from
      funext fun t => funext fun ξ => fourierMetric_bump t ξ α β]
    exact isWeightedAmplitude_fourierBump I 2
  density := by
    rw [show fourierScalar bumpScalar = fun _ => fourierBump from funext fourierScalar_bump]
    exact isWeightedAmplitude_fourierBump I 0
  velocity α := by
    rw [show vamp (fourierVector bumpVector) α = fun _ => fourierBump from
      funext fun t => funext fun ξ => fourierVector_bump t ξ α]
    exact isWeightedAmplitude_fourierBump I 0

/-- **The bump perturbation is beyond the compact spectra avoiding the origin**: its transform
does not vanish at `ξ = 0`. -/
theorem not_hasCompactSpectrum_bump {t : ℝ} (ht : t ∈ I) {K : Set E3} (h0K : (0 : E3) ∉ K) :
    ¬ HasCompactSpectrum I K bumpMetric bumpScalar bumpVector := fun hS => by
  have h := (hS.metric 0 0).support t ht 0 h0K
  simp only [amp, fourierMetric_bump] at h
  exact fourierBump_zero_ne_zero h

/-! #### A solution: the spatial co-ordinate mode with the profile of the bump -/

/-- The spatial co-ordinate mode `ĥ(t, ξ) = F(ξ) nn/|n|²`, `n = 2πξ`, with the Schwartz
profile `F = 𝓕φ` of the bump, constant in time (the gauge mode `λ = μ = 1` of L&L, §115). -/
def gaugeData : ℝ → E3 → Mat3 ℂ := fun _ ξ => fourierBump ξ • longProj (wave ξ)

theorem longProj_wave_smul {c : ℝ} (hc : 0 < c) (ξ : E3) (α β : Fin 3) :
    longProj (wave (c • ξ)) α β = longProj (wave ξ) α β := by
  simp only [longProj, wave_smul]
  exact ScalarVectorTensor.ratio_smul_left _ (Complex.ofReal_ne_zero.mpr hc.ne') α β

theorem continuousOn_longProj_wave (α β : Fin 3) :
    ContinuousOn (fun ξ : E3 => longProj (wave ξ) α β) nonzero :=
  (ContDiffOn.div_nsq_wave ((contDiff_wave α).mul (contDiff_wave β)).contDiffOn).continuousOn

/-- The co-ordinate mode is weighted data, without a cutoff at `ξ = 0`. -/
theorem isWeightedData_gaugeData (hI : IsOpen I) :
    IsWeightedData I gaugeData (fun _ _ => 0) (fun _ _ _ => 0) where
  metric α β := by
    obtain ⟨C, hC⟩ := exists_bound_of_scale_invariant (continuousOn_longProj_wave α β)
      fun c hc ξ => longProj_wave_smul hc ξ α β
    have h := IsWeightedAmplitude.mul_left (p := 0) (C := C) (k := 2) (I := I)
      hI (m := fun ξ => longProj (wave ξ) α β)
      (aestronglyMeasurable_of_continuousOn_ne_zero (continuousOn_longProj_wave α β))
      (fun ξ => by rw [pow_zero, mul_one]; exact hC ξ) (isWeightedAmplitude_fourierBump I 2)
    convert h using 1
    funext t ξ
    simp only [amp, gaugeData, Pi.smul_apply, smul_eq_mul, mul_comm]
  density := .const aestronglyMeasurable_const (by simp)
  velocity _ := .const aestronglyMeasurable_const (by simp)
  symm t ξ α β := by
    simp only [gaugeData, Pi.smul_apply, smul_eq_mul, longProj, mul_comm (wave ξ α)]
  herm_metric α β t _ ξ := by
    simp only [amp, gaugeData, Pi.smul_apply, smul_eq_mul, Packet.longProj_wave_neg,
      fourierBump_neg, map_mul, Packet.conj_longProj]
  herm_density _ _ _ := by simp
  herm_velocity _ _ _ _ := by simp [vamp]

theorem jet1_gaugeData (t : ℝ) (ξ : E3) : jet1 gaugeData t ξ = 0 := by
  funext α β; simp [jet1, timeDeriv, amp, gaugeData]

theorem jet2_gaugeData (t : ℝ) (ξ : E3) : jet2 gaugeData t ξ = 0 := by
  funext α β; simp [jet2, timeDeriv, amp, gaugeData]

/-- **The co-ordinate mode solves the linearized Einstein equations with dust** on every dust
background, by the frequency criterion for weighted data. -/
theorem linearizedEinsteinDust_gaugeData (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) :
    LinearizedEinsteinDust B κ ρ (fieldOf gaugeData) (fun _ => 0) (fun _ _ => 0) := by
  have h := (isWeightedData_gaugeData (I := B.I) B.isOpen_I).linearizedEinsteinDust_iff
    (κ := κ) (ρ := ρ)
  rw [scalarOf_zero, vectorOf_zero] at h
  refine h.mpr fun t ht => ?_
  filter_upwards [Measure.ae_ne volume 0] with ξ hξ
  have hn := nsq_wave_ne_zero hξ
  obtain ⟨e1, e2⟩ := dust_background hB ht
  have hc₁ : (fourierCoeffs B κ ρ t).c₁ = (fourierCoeffs B κ ρ t).src := by
    simp only [fourierCoeffs]
    congr 1
    rw [e1, e2]; ring
  rw [FrequencyEq, jet1_gaugeData, jet2_gaugeData]
  refine ⟨by simp [ScalarVectorTensor.resTime], by funext α; simp [ScalarVectorTensor.resMixed],
    ?_⟩
  simp only [gaugeData, ScalarVectorTensor.resSpace, map_smul, ScalarVectorTensor.op_longProj hn,
    hc₁, ScalarVectorTensor.trace_zero, mul_zero, sub_zero, smul_zero, zero_smul, add_zero]
  funext α β
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  ring

theorem longProj_wave_ξ₀ : longProj (wave Packet.ξ₀) 2 2 = 1 := by
  have hw : wave Packet.ξ₀ = ![0, 0, ((2 * Real.pi : ℝ) : ℂ)] := by
    funext γ; fin_cases γ <;> simp [wave, Packet.ξ₀]
  have hn : ScalarVectorTensor.nsq (wave Packet.ξ₀) ≠ 0 :=
    nsq_wave_ne_zero (by rw [← norm_ne_zero_iff, Packet.norm_ξ₀]; norm_num)
  rw [ScalarVectorTensor.longProj, ← div_self hn]
  simp [ScalarVectorTensor.nsq, hw, Fin.sum_univ_three, sq]

theorem gaugeData_smul_ξ₀ {s : ℝ} (hs : 0 < s) (t : ℝ) :
    gaugeData t (s • Packet.ξ₀) 2 2 = fourierBump (s • Packet.ξ₀) := by
  simp only [gaugeData, Pi.smul_apply, smul_eq_mul, longProj_wave_smul hs, longProj_wave_ξ₀,
    mul_one]

/-- **The co-ordinate mode does not vanish near `ξ = 0`**, where `nn/|n|²` is discontinuous. -/
theorem exists_gaugeData_ne_zero {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∃ ξ : E3, ‖ξ‖ < ε ∧ gaugeData t ξ ≠ 0 := by
  have hev : ∀ᶠ ξ in 𝓝 (0 : E3), fourierBump ξ ≠ 0 :=
    continuous_fourierBump.continuousAt.eventually_ne fourierBump_zero_ne_zero
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hs : 0 < min ε δ / 2 := by positivity
  have hnorm : ‖(min ε δ / 2) • Packet.ξ₀‖ = min ε δ / 2 := by
    rw [norm_smul, Packet.norm_ξ₀, mul_one, Real.norm_of_nonneg hs.le]
  have h1 : min ε δ / 2 < ε := by
    have := min_le_left ε δ; linarith
  have h2 : min ε δ / 2 < δ := by
    have := min_le_right ε δ; linarith
  refine ⟨(min ε δ / 2) • Packet.ξ₀, by rw [hnorm]; exact h1, fun h => ?_⟩
  have h22 := congrFun (congrFun h 2) 2
  rw [gaugeData_smul_ξ₀ hs] at h22
  exact hball (by rw [dist_zero_right, hnorm]; exact h2) h22

/-- **The co-ordinate mode is not Fourier data with a compact spectrum avoiding the origin**, so
the theorems with a cutoff do not apply to it. -/
theorem not_isFourierData_gaugeData {t : ℝ} (ht : t ∈ I) {K : Set E3} (hK : IsCompact K)
    (h0K : (0 : E3) ∉ K) : ¬ IsFourierData I K gaugeData (fun _ _ => 0) (fun _ _ _ => 0) :=
  fun hD => by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl 0 h0K
    obtain ⟨ξ, hξ, hne⟩ := exists_gaugeData_ne_zero hε t
    have hξK : ξ ∉ K := hball (by rwa [Metric.mem_ball, dist_zero_right])
    exact hne (funext fun α => funext fun β => (hD.metric α β).support t ht ξ hξK)

end ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Reconstruction
