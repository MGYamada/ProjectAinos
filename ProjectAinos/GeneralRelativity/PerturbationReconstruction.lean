/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.CosmologicalPerturbation
public import ProjectAinos.SmoothGeometry.Tensor.ScalarVectorTensor
public import ProjectAinos.SmoothGeometry.Fourier.CompactSynthesis
import Mathlib.Tactic

/-!
# The reconstruction of a flat perturbation from its scalar, vector and tensor modes

Landau–Lifshitz, §115, for the flat (`k = 0`) dust universe in the synchronous reference system
(`CosmologicalPerturbation`). A perturbation `(h_{αβ}, δ, v_α)` is given by its spatial Fourier
amplitudes `ĥ(t, ξ)`, `δ̂(t, ξ)`, `v̂(t, ξ)` (`IsFourierData`): smooth in `(t, ξ)` on `I × ℝ³`,
vanishing for `ξ` outside a fixed compact set `K` (for the projections, `0 ∉ K`: a packet
supported in an annulus), symmetric, and Hermitian, `ĥ(t, −ξ) = conj ĥ(t, ξ)`. The fields are
the syntheses `h_{αβ}(t, x) = Re ∫ e^{2πi⟪ξ, x⟫} ĥ_{αβ}(t, ξ) dξ` (`fieldOf`, `scalarOf`,
`vectorOf`), which are real.

* `linearizedEinsteinDust_iff_frequencyEq`: **the linearized Einstein equations with dust hold
  if and only if every frequency satisfies the mode equations** `FrequencyEq`: the system
  `ScalarVectorTensor.SymbolEq` of `δR_{ik} = κ δS_{ik}` for the wave vector `n = 2πξ`, with
  the jets `ĥ, ∂ₜĥ, ∂ₜ²ĥ`, the density `δ̂` and the velocity `v̂`. The proof differentiates
  under the integral (`Fourier.fderiv_synthesis_time`, `fderiv_synthesis_space`), writes each
  component of the residual as a linear form of the jets (`timeForm`, `mixedForm`, `spaceForm`)
  commuting with the synthesis (`Fourier.synthesis_linearMap`), and uses the uniqueness of the
  Fourier transform (`Fourier.eq_zero_of_synthesis_eq_zero`).
* `frequencyEq_iff_split` and `linearizedEinsteinDust_iff_split`: **the decomposition**. The
  scalar, vector and tensor parts of the amplitudes at each frequency (`scalarData`,
  `vectorData`, `tensorData`, with the longitudinal and transverse velocities `longData`,
  `transData`) are again Fourier data, and the perturbation solves the equations if and only if
  its scalar part (with `δ` and the longitudinal velocity), its vector part (with the transverse
  velocity) and its tensor part (alone) do. `fieldOf_eq_add`: the perturbation is the sum of
  the three parts.
* `isFourierData_of_slices`, `eq_fieldOf_fourier`: **the reconstruction**. A real perturbation
  whose spatial slices are continuous and integrable, with transforms of the class, is the
  synthesis of its transforms, by Fourier inversion; with `linearizedEinsteinDust_congr` all the
  statements apply to it (`reconstruction`).
-/

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory
open scoped ContDiff Topology ComplexConjugate FourierTransform

namespace ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Reconstruction

open SmoothGeometry CoordinateMetric FLRW SmoothGeometry.Fourier
open SmoothGeometry.ScalarVectorTensor (Mat3 Coeffs SymbolEq resTime resMixed resSpace
  scalarPart vectorPart tensorPart longVec transVec)

local notation "E" => MinkowskiModel 3
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Fourier data and their fields -/

/-- The wave vector `n = 2πξ` of the frequency `ξ`, as a complex vector. -/
def wave (ξ : E3) : Fin 3 → ℂ := fun γ => ((2 * Real.pi * ξ γ : ℝ) : ℂ)

/-- The entry `(α, β)` of a matrix amplitude. -/
def amp (hh : ℝ → E3 → Mat3 ℂ) (α β : Fin 3) : ℝ → E3 → ℂ := fun t ξ => hh t ξ α β

/-- The entry `α` of a vector amplitude. -/
def vamp (vv : ℝ → E3 → Fin 3 → ℂ) (α : Fin 3) : ℝ → E3 → ℂ := fun t ξ => vv t ξ α

/-- The metric perturbation `h_{αβ}(t, x) = Re ∫ e^{2πi⟪ξ, x⟫} ĥ_{αβ}(t, ξ) dξ`. -/
def fieldOf (hh : ℝ → E3 → Mat3 ℂ) : E → Fin 3 → Fin 3 → ℝ :=
  fun z α β => (synthesis (amp hh α β) z).re

/-- The density contrast `δ(t, x) = Re ∫ e^{2πi⟪ξ, x⟫} δ̂(t, ξ) dξ`. -/
def scalarOf (dd : ℝ → E3 → ℂ) : E → ℝ := fun z => (synthesis dd z).re

/-- The velocity `v_α(t, x) = Re ∫ e^{2πi⟪ξ, x⟫} v̂_α(t, ξ) dξ`. -/
def vectorOf (vv : ℝ → E3 → Fin 3 → ℂ) : E → Fin 3 → ℝ :=
  fun z α => (synthesis (vamp vv α) z).re

/-- The time derivative `∂ₜĥ(t, ξ)` of the matrix amplitude. -/
def jet1 (hh : ℝ → E3 → Mat3 ℂ) (t : ℝ) (ξ : E3) : Mat3 ℂ :=
  fun α β => timeDeriv (amp hh α β) t ξ

/-- The second time derivative `∂ₜ²ĥ(t, ξ)` of the matrix amplitude. -/
def jet2 (hh : ℝ → E3 → Mat3 ℂ) (t : ℝ) (ξ : E3) : Mat3 ℂ :=
  fun α β => timeDeriv (timeDeriv (amp hh α β)) t ξ

/-- **Fourier data of a perturbation**: the amplitudes are smooth in `(t, ξ)` on `I × ℝ³` and
vanish for `ξ ∉ K`; the metric amplitude is symmetric; all amplitudes are Hermitian. -/
structure IsFourierData (I : Set ℝ) (K : Set E3) (hh : ℝ → E3 → Mat3 ℂ) (dd : ℝ → E3 → ℂ)
    (vv : ℝ → E3 → Fin 3 → ℂ) : Prop where
  /-- The metric amplitude is of the class. -/
  metric : ∀ α β, IsCompactAmplitude I K (amp hh α β)
  /-- The density amplitude is of the class. -/
  density : IsCompactAmplitude I K dd
  /-- The velocity amplitude is of the class. -/
  velocity : ∀ α, IsCompactAmplitude I K (vamp vv α)
  /-- The metric amplitude is symmetric. -/
  symm : ∀ t ξ α β, hh t ξ α β = hh t ξ β α
  /-- The metric amplitude is Hermitian. -/
  herm_metric : ∀ α β, IsHermitian I (amp hh α β)
  /-- The density amplitude is Hermitian. -/
  herm_density : IsHermitian I dd
  /-- The velocity amplitude is Hermitian. -/
  herm_velocity : ∀ α, IsHermitian I (vamp vv α)

/-- The coefficients of the equations of one frequency at the time `t`; the mixed equation has
the factor `i/2` of `∂_α e^{2πi⟪ξ, x⟫} = i n_α e^{2πi⟪ξ, x⟫}`. -/
def fourierCoeffs (B : Background) (κ : ℝ) (ρ : ℝ → ℝ) (t : ℝ) : Coeffs ℂ where
  hub := ((deriv B.a t / B.a t : ℝ) : ℂ)
  dens := ((κ * ρ t : ℝ) : ℂ)
  mixC := Complex.I / 2
  c₁ := ((2 * deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t : ℝ) : ℂ)
  c₂ := ((3 / 2 * (B.a t * deriv B.a t) : ℝ) : ℂ)
  c₃ := ((B.a t ^ 2 / 2 : ℝ) : ℂ)
  c₄ := ((B.a t * deriv B.a t / 2 : ℝ) : ℂ)
  src := ((κ * (ρ t * B.a t ^ 2) / 2 : ℝ) : ℂ)

/-- **The mode equations of the frequency `ξ` at the time `t`**: the equations
`δR_{ik} = κ δS_{ik}` of the wave vector `n = 2πξ` for the jets of the amplitudes. -/
def FrequencyEq (B : Background) (κ : ℝ) (ρ : ℝ → ℝ) (hh : ℝ → E3 → Mat3 ℂ)
    (dd : ℝ → E3 → ℂ) (vv : ℝ → E3 → Fin 3 → ℂ) (t : ℝ) (ξ : E3) : Prop :=
  SymbolEq (fourierCoeffs B κ ρ t) (wave ξ) (hh t ξ) (jet1 hh t ξ) (jet2 hh t ξ) (dd t ξ)
    (vv t ξ)

/-! ### The symbols of the derivatives -/

/-- The symbol of `∂_c`: `∂ₜ` for `c = 0` and the multiplication by `2πi ξ_γ` for
`c = γ + 1`. -/
def dsym (c : Fin 4) (G : ℝ → E3 → ℂ) : ℝ → E3 → ℂ :=
  Fin.cases (motive := fun _ => ℝ → E3 → ℂ) (timeDeriv G)
    (fun γ t ξ => 2 * Real.pi * ξ γ * Complex.I * G t ξ) c

variable {I : Set ℝ} {K : Set E3} {G : ℝ → E3 → ℂ} {z : E}

theorem isCompactAmplitude_dsym (hI : IsOpen I) (hK : IsCompact K)
    (hG : IsCompactAmplitude I K G) (c : Fin 4) : IsCompactAmplitude I K (dsym c G) := by
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨γ, rfl⟩
  · exact hG.timeDeriv hI
  · exact hG.space hK γ

theorem isHermitian_dsym (hI : IsOpen I) (hG : IsCompactAmplitude I K G) (hH : IsHermitian I G)
    (c : Fin 4) : IsHermitian I (dsym c G) := by
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨γ, rfl⟩
  · exact hH.timeDeriv hG hI
  · exact hH.space γ

theorem fderiv_synthesis_dsym (hI : IsOpen I) (hK : IsCompact K) (hG : IsCompactAmplitude I K G)
    (hz : z ∈ slab I) (c : Fin 4) :
    fderiv ℝ (synthesis G) z (Pi.single c 1) = synthesis (dsym c G) z := by
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨γ, rfl⟩
  · exact fderiv_synthesis_time hI hK hG hz
  · exact fderiv_synthesis_space hI hK hG hz γ

/-- **The derivatives of a real synthesized field** are the syntheses of the symbols. -/
theorem ofReal_fderiv_re (hI : IsOpen I) (hK : IsCompact K) (hG : IsCompactAmplitude I K G)
    (hH : IsHermitian I G) (hz : z ∈ slab I) (c : Fin 4) :
    ((fderiv ℝ (fun w => (synthesis G w).re) z (Pi.single c 1) : ℝ) : ℂ) =
      synthesis (dsym c G) z := by
  rw [fderiv_re (differentiableAt_synthesis hI hK hG hz), fderiv_synthesis_dsym hI hK hG hz c]
  exact ofReal_re_synthesis fun ξ => isHermitian_dsym hI hG hH c (z 0) hz ξ

/-- The domain of the flat background is the slab of its times. -/
theorem domain_eq_slab (B : Background) : (domain B.toData : Set E) = slab B.I :=
  Set.ext fun _ => mem_domain_iff

variable {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {hh : ℝ → E3 → Mat3 ℂ} {dd : ℝ → E3 → ℂ}
  {vv : ℝ → E3 → Fin 3 → ℂ}

theorem ofReal_fieldOf (hD : IsFourierData B.I K hh dd vv) (hz : z ∈ slab B.I) (α β : Fin 3) :
    ((fieldOf hh z α β : ℝ) : ℂ) = synthesis (amp hh α β) z :=
  ofReal_re_synthesis fun ξ => hD.herm_metric α β (z 0) hz ξ

theorem ofReal_scalarOf (hD : IsFourierData B.I K hh dd vv) (hz : z ∈ slab B.I) :
    ((scalarOf dd z : ℝ) : ℂ) = synthesis dd z :=
  ofReal_re_synthesis fun ξ => hD.herm_density (z 0) hz ξ

theorem ofReal_vectorOf (hD : IsFourierData B.I K hh dd vv) (hz : z ∈ slab B.I) (α : Fin 3) :
    ((vectorOf vv z α : ℝ) : ℂ) = synthesis (vamp vv α) z :=
  ofReal_re_synthesis fun ξ => hD.herm_velocity α (z 0) hz ξ

theorem ofReal_dh_fieldOf (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K)
    (hz : z ∈ slab B.I) (c : Fin 4) (α β : Fin 3) :
    ((dh (fieldOf hh) c z α β : ℝ) : ℂ) = synthesis (dsym c (amp hh α β)) z :=
  ofReal_fderiv_re B.isOpen_I hK (hD.metric α β) (hD.herm_metric α β) hz c

theorem ofReal_ddh_fieldOf (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K)
    (hz : z ∈ slab B.I) (c e : Fin 4) (α β : Fin 3) :
    ((ddh (fieldOf hh) c e z α β : ℝ) : ℂ) = synthesis (dsym c (dsym e (amp hh α β))) z := by
  have hev : (fun w => dh (fieldOf hh) e w α β) =ᶠ[𝓝 z]
      fun w => (synthesis (dsym e (amp hh α β)) w).re :=
    eventually_of_mem ((isOpen_slab B.isOpen_I).mem_nhds hz) fun w hw => by
      show dh (fieldOf hh) e w α β = (synthesis (dsym e (amp hh α β)) w).re
      rw [← ofReal_dh_fieldOf hD hK hw e α β, Complex.ofReal_re]
  rw [ddh, hev.fderiv_eq]
  exact ofReal_fderiv_re B.isOpen_I hK (isCompactAmplitude_dsym B.isOpen_I hK (hD.metric α β) e)
    (isHermitian_dsym B.isOpen_I (hD.metric α β) (hD.herm_metric α β) e) hz c

/-- The synthesized metric perturbation is a perturbation of the background. -/
theorem isPerturbation_fieldOf (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K) :
    IsPerturbation B (fieldOf hh) where
  smooth α β := by
    rw [domain_eq_slab]
    exact Complex.reCLM.contDiff.comp_contDiffOn
      (contDiffOn_synthesis B.isOpen_I hK (hD.metric α β))
  symm z α β := by
    have e : amp hh α β = amp hh β α := funext fun t => funext fun ξ => hD.symm t ξ α β
    simp only [fieldOf, e]

/-! ### The jets and the residual as linear forms -/

/-- The jets entering the linearized equations: the second and first derivatives and the value
of the metric perturbation, the density contrast and the velocity. -/
inductive JetIdx
  | second (c e : Fin 4) (α β : Fin 3)
  | first (c : Fin 4) (α β : Fin 3)
  | value (α β : Fin 3)
  | density
  | velocity (α : Fin 3)
  deriving DecidableEq, Fintype

/-- The jets of a real perturbation at a point, as complex numbers. -/
def realJet (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) (z : E) :
    JetIdx → ℂ
  | .second c e α β => (ddh h c e z α β : ℂ)
  | .first c α β => (dh h c z α β : ℂ)
  | .value α β => (h z α β : ℂ)
  | .density => (δ z : ℂ)
  | .velocity α => (v z α : ℂ)

/-- The symbols of the jets of Fourier data. -/
def jetAmp (hh : ℝ → E3 → Mat3 ℂ) (dd : ℝ → E3 → ℂ) (vv : ℝ → E3 → Fin 3 → ℂ) :
    JetIdx → ℝ → E3 → ℂ
  | .second c e α β => dsym c (dsym e (amp hh α β))
  | .first c α β => dsym c (amp hh α β)
  | .value α β => amp hh α β
  | .density => dd
  | .velocity α => vamp vv α

theorem isCompactAmplitude_jetAmp (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K)
    (j : JetIdx) : IsCompactAmplitude B.I K (jetAmp hh dd vv j) := by
  cases j with
  | second c e α β =>
    exact isCompactAmplitude_dsym B.isOpen_I hK
      (isCompactAmplitude_dsym B.isOpen_I hK (hD.metric α β) e) c
  | first c α β => exact isCompactAmplitude_dsym B.isOpen_I hK (hD.metric α β) c
  | value α β => exact hD.metric α β
  | density => exact hD.density
  | velocity α => exact hD.velocity α

theorem realJet_eq (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K) (hz : z ∈ slab B.I) :
    realJet (fieldOf hh) (scalarOf dd) (vectorOf vv) z =
      fun j => synthesis (jetAmp hh dd vv j) z := by
  funext j
  cases j with
  | second c e α β => exact ofReal_ddh_fieldOf hD hK hz c e α β
  | first c α β => exact ofReal_dh_fieldOf hD hK hz c α β
  | value α β => exact ofReal_fieldOf hD hz α β
  | density => exact ofReal_scalarOf hD hz
  | velocity α => exact ofReal_vectorOf hD hz α

/-- The residual `δR₀₀ − κ δS₀₀` as a linear form of the jets. -/
def timeForm (B : Background) (κ : ℝ) (ρ : ℝ → ℝ) (t : ℝ) : (JetIdx → ℂ) →ₗ[ℂ] ℂ where
  toFun J := -(∑ γ, J (.second 0 0 γ γ)) / 2 -
    ((deriv B.a t / B.a t : ℝ) : ℂ) * ∑ γ, J (.first 0 γ γ) - ((κ * ρ t : ℝ) : ℂ) * J .density / 2
  map_add' J J' := by simp only [Pi.add_apply, Fin.sum_univ_three]; ring
  map_smul' c J := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Fin.sum_univ_three]; ring

/-- The residual `δR₀α − κ δS₀α` as a linear form of the jets. -/
def mixedForm (κ : ℝ) (ρ : ℝ → ℝ) (t : ℝ) (α : Fin 3) :
    (JetIdx → ℂ) →ₗ[ℂ] ℂ where
  toFun J := (∑ γ, J (.second γ.succ 0 γ α) - ∑ γ, J (.second 0 α.succ γ γ)) / 2 +
    ((κ * ρ t : ℝ) : ℂ) * J (.velocity α)
  map_add' J J' := by simp only [Pi.add_apply, Fin.sum_univ_three]; ring
  map_smul' c J := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Fin.sum_univ_three]; ring

/-- The residual `δR_{αβ} − κ δS_{αβ}` as a linear form of the jets. -/
def spaceForm (B : Background) (κ : ℝ) (ρ : ℝ → ℝ) (t : ℝ) (α β : Fin 3) :
    (JetIdx → ℂ) →ₗ[ℂ] ℂ where
  toFun J := (∑ γ, (J (.second γ.succ α.succ γ β) + J (.second γ.succ β.succ γ α) -
        J (.second γ.succ γ.succ α β)) - ∑ γ, J (.second α.succ β.succ γ γ)) / 2 +
      ((2 * deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t : ℝ) : ℂ) * J (.value α β) +
      ((3 / 2 * (B.a t * deriv B.a t) : ℝ) : ℂ) * J (.first 0 α β) +
      ((B.a t ^ 2 / 2 : ℝ) : ℂ) * J (.second 0 0 α β) +
      (if α = β then ((B.a t * deriv B.a t / 2 : ℝ) : ℂ) * ∑ γ, J (.first 0 γ γ) else 0) -
      ((κ * (ρ t * B.a t ^ 2) / 2 : ℝ) : ℂ) * ((if α = β then J .density else 0) + J (.value α β))
  map_add' J J' := by
    simp only [Pi.add_apply, Fin.sum_univ_three]; split_ifs <;> ring
  map_smul' c J := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Fin.sum_univ_three]
    split_ifs <;> ring

theorem residual_time (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) (z : E) :
    ((linRicci B h z 0 0 - κ * linDust B ρ h δ v z 0 0 : ℝ) : ℂ) =
      timeForm B κ ρ (z 0) (realJet h δ v z) := by
  simp only [linRicci_zero_zero, linRicciTime, linDust_zero_zero, timeForm, LinearMap.coe_mk,
    AddHom.coe_mk, realJet]
  push_cast; ring

theorem residual_mixed (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) (z : E)
    (α : Fin 3) :
    ((linRicci B h z 0 α.succ - κ * linDust B ρ h δ v z 0 α.succ : ℝ) : ℂ) =
      mixedForm κ ρ (z 0) α (realJet h δ v z) ∧
    ((linRicci B h z α.succ 0 - κ * linDust B ρ h δ v z α.succ 0 : ℝ) : ℂ) =
      mixedForm κ ρ (z 0) α (realJet h δ v z) := by
  simp only [linRicci_zero_succ, linRicci_succ_zero, linRicciMixed, linDust_zero_succ,
    linDust_succ_zero, mixedForm, LinearMap.coe_mk, AddHom.coe_mk, realJet]
  push_cast
  constructor <;> ring

theorem residual_space (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ) (v : E → Fin 3 → ℝ) (z : E)
    (α β : Fin 3) :
    ((linRicci B h z α.succ β.succ - κ * linDust B ρ h δ v z α.succ β.succ : ℝ) : ℂ) =
      spaceForm B κ ρ (z 0) α β (realJet h δ v z) := by
  simp only [linRicci_succ_succ, linRicciSpace, linDust_succ_succ, spaceForm, LinearMap.coe_mk,
    AddHom.coe_mk, realJet]
  split_ifs <;> push_cast <;> ring

/-! ### The forms on the amplitudes are the symbols -/

theorem dsym_zero (G : ℝ → E3 → ℂ) : dsym 0 G = timeDeriv G := rfl

theorem dsym_succ (G : ℝ → E3 → ℂ) (γ : Fin 3) :
    dsym γ.succ G = fun t ξ => 2 * Real.pi * ξ γ * Complex.I * G t ξ := rfl

theorem dsym_zero_succ (hI : IsOpen I) (hG : IsCompactAmplitude I K G) {t : ℝ} (ht : t ∈ I)
    (γ : Fin 3) (ξ : E3) :
    dsym 0 (dsym γ.succ G) t ξ = 2 * Real.pi * ξ γ * Complex.I * timeDeriv G t ξ := by
  rw [dsym_zero, dsym_succ]
  exact timeDeriv_mul_left hG hI ht (fun ξ => 2 * Real.pi * ξ γ * Complex.I) ξ

theorem two_pi_I_mul (a b : ℝ) (w : ℂ) :
    2 * (Real.pi : ℂ) * a * Complex.I * (2 * Real.pi * b * Complex.I * w) =
      -(((2 * Real.pi * a : ℝ) : ℂ) * ((2 * Real.pi * b : ℝ) : ℂ) * w) := by
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem timeForm_jetAmp (t : ℝ) (ξ : E3) :
    timeForm B κ ρ t (fun j => jetAmp hh dd vv j t ξ) =
      resTime (fourierCoeffs B κ ρ t) (jet1 hh t ξ) (jet2 hh t ξ) (dd t ξ) := by
  simp only [timeForm, LinearMap.coe_mk, AddHom.coe_mk, jetAmp, resTime, fourierCoeffs,
    ScalarVectorTensor.trace, jet1, jet2, dsym_zero]

theorem mixedForm_jetAmp (hD : IsFourierData B.I K hh dd vv) {t : ℝ} (ht : t ∈ B.I) (ξ : E3)
    (α : Fin 3) :
    mixedForm κ ρ t α (fun j => jetAmp hh dd vv j t ξ) =
      resMixed (fourierCoeffs B κ ρ t) (wave ξ) (jet1 hh t ξ) (vv t ξ) α := by
  simp only [mixedForm, LinearMap.coe_mk, AddHom.coe_mk, jetAmp]
  simp only [dsym_zero_succ B.isOpen_I (hD.metric _ _) ht]
  simp only [dsym_succ, dsym_zero, resMixed, fourierCoeffs,
    ScalarVectorTensor.mix_apply, ScalarVectorTensor.contract, ScalarVectorTensor.trace, jet1, wave,
    vamp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  push_cast
  ring

theorem spaceForm_jetAmp (t : ℝ) (ξ : E3) (α β : Fin 3) :
    spaceForm B κ ρ t α β (fun j => jetAmp hh dd vv j t ξ) =
      resSpace (fourierCoeffs B κ ρ t) (wave ξ) (hh t ξ) (jet1 hh t ξ) (jet2 hh t ξ) (dd t ξ)
        α β := by
  simp only [spaceForm, LinearMap.coe_mk, AddHom.coe_mk, jetAmp, dsym_succ, dsym_zero,
    two_pi_I_mul, resSpace, fourierCoeffs, ScalarVectorTensor.op, ScalarVectorTensor.nsq,
    ScalarVectorTensor.contract, ScalarVectorTensor.trace, ScalarVectorTensor.delta, jet1, jet2,
    wave, amp, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  split_ifs <;> push_cast <;> ring

/-! ### The equations of the frequencies -/

/-- The synthesis of a form of the jets is the form of the syntheses. -/
theorem synthesis_form (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K)
    (hz : z ∈ slab B.I) (Λ : ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ) :
    synthesis (fun t ξ => Λ t fun j => jetAmp hh dd vv j t ξ) z =
      Λ (z 0) (realJet (fieldOf hh) (scalarOf dd) (vectorOf vv) z) := by
  rw [synthesis_linearMap Λ (jetAmp hh dd vv)
    (fun j => (isCompactAmplitude_jetAmp hD hK j).integrable_integrand hK hz),
    realJet_eq hD hK hz]

/-- At a time of `I`, a form of the jets of the amplitudes vanishes for every frequency if and
only if its synthesis vanishes at every point of that time. -/
theorem form_eq_zero_iff (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K) {t : ℝ}
    (ht : t ∈ B.I) (Λ : ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ) :
    (∀ x : E3, synthesis (fun s ξ => Λ s fun j => jetAmp hh dd vv j s ξ)
        (spacetimePoint t x) = 0) ↔
      ∀ ξ, Λ t (fun j => jetAmp hh dd vv j t ξ) = 0 := by
  constructor
  · intro h
    have hc : Continuous fun ξ => Λ t fun j => jetAmp hh dd vv j t ξ :=
      (LinearMap.continuous_of_finiteDimensional (Λ t)).comp
        (continuous_pi fun j => (isCompactAmplitude_jetAmp hD hK j).continuous ht)
    have hi : Integrable fun ξ => Λ t fun j => jetAmp hh dd vv j t ξ :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun ξ hξ => by
        have : (fun j => jetAmp hh dd vv j t ξ) = 0 :=
          funext fun j => (isCompactAmplitude_jetAmp hD hK j).support t ht ξ hξ
        simp [this])
    exact eq_zero_of_synthesis_eq_zero (G := fun s ξ => Λ s fun j => jetAmp hh dd vv j s ξ)
      hc hi h
  · intro h x
    rw [synthesis_congr (G₂ := fun _ _ => 0) fun ξ => h ξ, synthesis_zero]

/-- **The linearized Einstein equations of a perturbation given by Fourier data hold if and only
if every frequency satisfies the mode equations.** -/
theorem linearizedEinsteinDust_iff_frequencyEq (hD : IsFourierData B.I K hh dd vv)
    (hK : IsCompact K) :
    LinearizedEinsteinDust B κ ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) ↔
      ∀ t ∈ B.I, ∀ ξ, FrequencyEq B κ ρ hh dd vv t ξ := by
  have hpt (t : ℝ) (ht : t ∈ B.I) (x : E3) : spacetimePoint t x ∈ slab B.I := ht
  have key (Λ : ℝ → (JetIdx → ℂ) →ₗ[ℂ] ℂ) (r : E → ℝ)
      (hr : ∀ z ∈ slab B.I, (r z : ℂ) = Λ (z 0)
        (realJet (fieldOf hh) (scalarOf dd) (vectorOf vv) z)) :
      (∀ z ∈ slab B.I, r z = 0) ↔
        ∀ t ∈ B.I, ∀ ξ, Λ t (fun j => jetAmp hh dd vv j t ξ) = 0 := by
    constructor
    · intro h t ht
      refine (form_eq_zero_iff hD hK ht Λ).mp fun x => ?_
      rw [synthesis_form hD hK (hpt t ht x), ← hr _ (hpt t ht x), h _ (hpt t ht x),
        Complex.ofReal_zero]
    · intro h z hz
      have h0 := (form_eq_zero_iff hD hK hz Λ).mpr (h (z 0) hz) (spatialPoint z)
      rw [spacetimePoint_eq, synthesis_form hD hK hz, ← hr z hz] at h0
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
  · rintro ⟨h0, h1, -, h3⟩ t ht ξ
    refine ⟨?_, funext fun α => ?_, funext fun α => funext fun β => ?_⟩
    · rw [← timeForm_jetAmp]; exact h0 t ht ξ
    · rw [← mixedForm_jetAmp hD ht]; exact h1 α t ht ξ
    · rw [← spaceForm_jetAmp]; exact h3 α β t ht ξ
  · intro h
    refine ⟨fun t ht ξ => ?_, fun α t ht ξ => ?_, fun α t ht ξ => ?_, fun α β t ht ξ => ?_⟩
    · rw [timeForm_jetAmp]; exact (h t ht ξ).1
    · rw [mixedForm_jetAmp hD ht]; exact congrFun (h t ht ξ).2.1 α
    · rw [mixedForm_jetAmp hD ht]; exact congrFun (h t ht ξ).2.1 α
    · rw [spaceForm_jetAmp]; exact congrFun (congrFun (h t ht ξ).2.2 α) β

/-! ### The scalar, vector and tensor parts of Fourier data -/

/-- The scalar part `Π_S(2πξ) ĥ(t, ξ)` of the metric amplitude. -/
def scalarData (hh : ℝ → E3 → Mat3 ℂ) : ℝ → E3 → Mat3 ℂ :=
  fun t ξ => scalarPart (wave ξ) (hh t ξ)

/-- The vector part `Π_V(2πξ) ĥ(t, ξ)` of the metric amplitude. -/
def vectorData (hh : ℝ → E3 → Mat3 ℂ) : ℝ → E3 → Mat3 ℂ :=
  fun t ξ => vectorPart (wave ξ) (hh t ξ)

/-- The tensor part `Π_T(2πξ) ĥ(t, ξ)` of the metric amplitude. -/
def tensorData (hh : ℝ → E3 → Mat3 ℂ) : ℝ → E3 → Mat3 ℂ :=
  fun t ξ => tensorPart (wave ξ) (hh t ξ)

/-- The longitudinal part `(ξ·v̂/|ξ|²) ξ` of the velocity amplitude. -/
def longData (vv : ℝ → E3 → Fin 3 → ℂ) : ℝ → E3 → Fin 3 → ℂ :=
  fun t ξ => longVec (wave ξ) (vv t ξ)

/-- The transverse part `v̂ − (ξ·v̂/|ξ|²) ξ` of the velocity amplitude. -/
def transData (vv : ℝ → E3 → Fin 3 → ℂ) : ℝ → E3 → Fin 3 → ℂ :=
  fun t ξ => transVec (wave ξ) (vv t ξ)

theorem wave_neg (ξ : E3) : wave (-ξ) = -wave ξ := by
  funext γ; simp [wave]

theorem conj_wave (ξ : E3) (γ : Fin 3) : conj (wave ξ γ) = wave ξ γ := Complex.conj_ofReal _

theorem contDiff_wave (γ : Fin 3) : ContDiff ℝ ∞ fun ξ : E3 => wave ξ γ :=
  Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) γ).contDiff)

theorem nsq_wave_ne_zero {ξ : E3} (hξ : ξ ≠ 0) : ScalarVectorTensor.nsq (wave ξ) ≠ 0 := by
  have e : ScalarVectorTensor.nsq (wave ξ) = ((∑ γ, (2 * Real.pi * ξ γ) ^ 2 : ℝ) : ℂ) := by
    simp [ScalarVectorTensor.nsq, wave]
  rw [e, Complex.ofReal_ne_zero]
  intro h
  apply hξ
  have h' := (Finset.sum_eq_zero_iff_of_nonneg fun γ _ => sq_nonneg (2 * Real.pi * ξ γ)).mp h
  ext γ
  have := h' γ (Finset.mem_univ γ)
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  simpa [hπ] using this

theorem contDiff_nsq_wave : ContDiff ℝ ∞ fun ξ : E3 => ScalarVectorTensor.nsq (wave ξ) :=
  ContDiff.sum fun γ _ => (contDiff_wave γ).pow 2

/-- Division by `|2πξ|²` keeps the smoothness away from `ξ = 0`. -/
theorem ContDiffOn.div_nsq_wave {f : E3 → ℂ} (hf : ContDiffOn ℝ ∞ f {ξ | ξ ≠ 0}) :
    ContDiffOn ℝ ∞ (fun ξ => f ξ / ScalarVectorTensor.nsq (wave ξ)) {ξ | ξ ≠ 0} := by
  have hinv : ContDiffOn ℝ ∞ (fun ξ => (ScalarVectorTensor.nsq (wave ξ))⁻¹) {ξ | ξ ≠ 0} :=
    contDiff_nsq_wave.contDiffOn.inv fun _ hξ => nsq_wave_ne_zero hξ
  exact (hf.mul hinv).congr fun ξ _ => div_eq_mul_inv _ _

/-- The frequencies different from zero. -/
abbrev nonzero : Set E3 := {ξ | ξ ≠ 0}

theorem isOpen_nonzero : IsOpen nonzero := isOpen_ne

section Smooth

variable (M : Mat3 ℂ) (V : Fin 3 → ℂ)

theorem contDiff_contract_wave (β : Fin 3) :
    ContDiff ℝ ∞ fun ξ : E3 => ScalarVectorTensor.contract (wave ξ) M β :=
  ContDiff.sum fun γ _ => (contDiff_wave γ).mul contDiff_const

theorem contDiffOn_longCoeff_wave :
    ContDiffOn ℝ ∞ (fun ξ : E3 => ScalarVectorTensor.longCoeff (wave ξ) M) nonzero :=
  ContDiffOn.div_nsq_wave
    (ContDiff.sum fun β _ => (contDiff_contract_wave M β).mul (contDiff_wave β)).contDiffOn

theorem contDiffOn_shear_wave (β : Fin 3) :
    ContDiffOn ℝ ∞ (fun ξ : E3 => ScalarVectorTensor.shear (wave ξ) M β) nonzero :=
  (contDiff_contract_wave M β).contDiffOn.sub
    ((contDiffOn_longCoeff_wave M).mul (contDiff_wave β).contDiffOn)

theorem contDiffOn_scalarPart_wave (α β : Fin 3) :
    ContDiffOn ℝ ∞ (fun ξ : E3 => scalarPart (wave ξ) M α β) nonzero := by
  simp only [ScalarVectorTensor.scalarPart_apply]
  have hq : ContDiffOn ℝ ∞ (fun ξ : E3 => wave ξ α * wave ξ β / ScalarVectorTensor.nsq (wave ξ))
      nonzero :=
    ContDiffOn.div_nsq_wave ((contDiff_wave α).mul (contDiff_wave β)).contDiffOn
  exact ((contDiffOn_longCoeff_wave M).mul hq).add
    (((contDiffOn_const.sub (contDiffOn_longCoeff_wave M)).div_const 2).mul
      (contDiffOn_const.sub hq))

theorem contDiffOn_vectorPart_wave (α β : Fin 3) :
    ContDiffOn ℝ ∞ (fun ξ : E3 => vectorPart (wave ξ) M α β) nonzero := by
  simp only [ScalarVectorTensor.vectorPart_apply]
  exact ContDiffOn.div_nsq_wave (((contDiff_wave α).contDiffOn.mul (contDiffOn_shear_wave M β)).add
    ((contDiffOn_shear_wave M α).mul (contDiff_wave β).contDiffOn))

theorem contDiffOn_tensorPart_wave (α β : Fin 3) :
    ContDiffOn ℝ ∞ (fun ξ : E3 => tensorPart (wave ξ) M α β) nonzero := by
  simp only [ScalarVectorTensor.tensorPart_apply]
  exact (contDiffOn_const.sub (contDiffOn_scalarPart_wave M α β)).sub
    (contDiffOn_vectorPart_wave M α β)

theorem contDiffOn_longVec_wave (α : Fin 3) :
    ContDiffOn ℝ ∞ (fun ξ : E3 => longVec (wave ξ) V α) nonzero := by
  simp only [ScalarVectorTensor.longVec_apply]
  exact (ContDiffOn.div_nsq_wave
    (ContDiff.sum fun γ _ => (contDiff_wave γ).mul contDiff_const).contDiffOn).mul
      (contDiff_wave α).contDiffOn

theorem contDiffOn_transVec_wave (α : Fin 3) :
    ContDiffOn ℝ ∞ (fun ξ : E3 => transVec (wave ξ) V α) nonzero := by
  simp only [ScalarVectorTensor.transVec_apply]
  exact contDiffOn_const.sub (contDiffOn_longVec_wave V α)

end Smooth

theorem subset_nonzero (h0K : (0 : E3) ∉ K) : K ⊆ nonzero := fun _ hξ h => h0K (h ▸ hξ)

/-- A linear map of the matrices, smooth in `ξ ≠ 0`, maps Fourier data to amplitudes of the
class. -/
theorem isCompactAmplitude_linearMap (hD : IsFourierData I K hh dd vv) (hK : IsCompact K)
    (h0K : (0 : E3) ∉ K) (L : E3 → Mat3 ℂ →ₗ[ℂ] Mat3 ℂ)
    (hL : ∀ γ δ α β, ContDiffOn ℝ ∞ (fun ξ => L ξ (Pi.single γ (Pi.single δ 1)) α β) nonzero)
    (α β : Fin 3) : IsCompactAmplitude I K (fun t ξ => L ξ (hh t ξ) α β) := by
  have e : (fun t ξ => L ξ (hh t ξ) α β) = fun t ξ =>
      ∑ γ, ∑ δ, L ξ (Pi.single γ (Pi.single δ 1)) α β * amp hh γ δ t ξ := by
    funext t ξ
    rw [ScalarVectorTensor.linearMap_apply_eq_sum]
    simp only [amp, mul_comm]
  rw [e]
  exact IsCompactAmplitude.sum _ fun γ _ => IsCompactAmplitude.sum _ fun δ _ =>
    (hD.metric γ δ).mul_left hK isOpen_nonzero (subset_nonzero h0K) (hL γ δ α β)

/-- A linear map of the vectors, smooth in `ξ ≠ 0`, maps Fourier data to amplitudes of the
class. -/
theorem isCompactAmplitude_linearMap_vec (hD : IsFourierData I K hh dd vv) (hK : IsCompact K)
    (h0K : (0 : E3) ∉ K) (L : E3 → (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))
    (hL : ∀ γ α, ContDiffOn ℝ ∞ (fun ξ => L ξ (Pi.single γ 1) α) nonzero) (α : Fin 3) :
    IsCompactAmplitude I K (fun t ξ => L ξ (vv t ξ) α) := by
  have e : (fun t ξ => L ξ (vv t ξ) α) = fun t ξ =>
      ∑ γ, L ξ (Pi.single γ 1) α * vamp vv γ t ξ := by
    funext t ξ
    rw [ScalarVectorTensor.linearMap_vec_apply_eq_sum]
    simp only [vamp, mul_comm]
  rw [e]
  exact IsCompactAmplitude.sum _ fun γ _ =>
    (hD.velocity γ).mul_left hK isOpen_nonzero (subset_nonzero h0K) (hL γ α)

/-- The derivative of a linear map of a matrix-valued function. -/
theorem hasDerivAt_linearMap_apply (L : Mat3 ℂ →ₗ[ℂ] Mat3 ℂ) {M : ℝ → Mat3 ℂ} {M' : Mat3 ℂ}
    {t : ℝ} (h : ∀ α β, HasDerivAt (fun s => M s α β) (M' α β) t) (α β : Fin 3) :
    HasDerivAt (fun s => L (M s) α β) (L M' α β) t := by
  have hM : HasDerivAt M M' t := hasDerivAt_pi.2 fun α => hasDerivAt_pi.2 fun β => h α β
  let Lc : Mat3 ℂ →L[ℝ] Mat3 ℂ := LinearMap.toContinuousLinearMap (L.restrictScalars ℝ)
  have h2 : HasDerivAt (fun s => Lc (M s)) (Lc M') t := Lc.hasFDerivAt.comp_hasDerivAt t hM
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h2 α) β

theorem timeDeriv_linearMap (hD : IsFourierData B.I K hh dd vv) (L : E3 → Mat3 ℂ →ₗ[ℂ] Mat3 ℂ)
    {t : ℝ} (ht : t ∈ B.I) (ξ : E3) (α β : Fin 3) :
    timeDeriv (fun t ξ => L ξ (hh t ξ) α β) t ξ = L ξ (jet1 hh t ξ) α β :=
  (hasDerivAt_linearMap_apply (L ξ) (fun γ δ => (hD.metric γ δ).hasDerivAt B.isOpen_I ht ξ)
    α β).deriv

theorem timeDeriv_timeDeriv_linearMap (hD : IsFourierData B.I K hh dd vv)
    (L : E3 → Mat3 ℂ →ₗ[ℂ] Mat3 ℂ) {t : ℝ} (ht : t ∈ B.I) (ξ : E3) (α β : Fin 3) :
    timeDeriv (timeDeriv fun t ξ => L ξ (hh t ξ) α β) t ξ = L ξ (jet2 hh t ξ) α β := by
  have hev : (fun s => timeDeriv (fun t ξ => L ξ (hh t ξ) α β) s ξ) =ᶠ[𝓝 t]
      fun s => L ξ (jet1 hh s ξ) α β :=
    eventually_of_mem (B.isOpen_I.mem_nhds ht) fun s hs => timeDeriv_linearMap hD L hs ξ α β
  simp only [timeDeriv] at hev ⊢
  rw [hev.deriv_eq]
  exact (hasDerivAt_linearMap_apply (L ξ) (fun γ δ =>
    ((hD.metric γ δ).timeDeriv B.isOpen_I).hasDerivAt B.isOpen_I ht ξ) α β).deriv

/-- **The parts of Fourier data are Fourier data.** -/
theorem isFourierData_scalar (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K)
    (h0K : (0 : E3) ∉ K) : IsFourierData B.I K (scalarData hh) dd (longData vv) where
  metric α β := isCompactAmplitude_linearMap hD hK h0K (fun ξ => scalarPart (wave ξ))
    (fun γ δ α β => contDiffOn_scalarPart_wave _ α β) α β
  density := hD.density
  velocity α := isCompactAmplitude_linearMap_vec hD hK h0K (fun ξ => longVec (wave ξ))
    (fun γ α => contDiffOn_longVec_wave _ α) α
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

theorem isFourierData_vector (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K)
    (h0K : (0 : E3) ∉ K) : IsFourierData B.I K (vectorData hh) (fun _ _ => 0) (transData vv) where
  metric α β := isCompactAmplitude_linearMap hD hK h0K (fun ξ => vectorPart (wave ξ))
    (fun γ δ α β => contDiffOn_vectorPart_wave _ α β) α β
  density := IsCompactAmplitude.zero
  velocity α := isCompactAmplitude_linearMap_vec hD hK h0K (fun ξ => transVec (wave ξ))
    (fun γ α => contDiffOn_transVec_wave _ α) α
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

theorem isFourierData_tensor (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K)
    (h0K : (0 : E3) ∉ K) :
    IsFourierData B.I K (tensorData hh) (fun _ _ => 0) (fun _ _ _ => 0) where
  metric α β := isCompactAmplitude_linearMap hD hK h0K (fun ξ => tensorPart (wave ξ))
    (fun γ δ α β => contDiffOn_tensorPart_wave _ α β) α β
  density := IsCompactAmplitude.zero
  velocity _ := IsCompactAmplitude.zero
  symm t ξ α β := ScalarVectorTensor.tensorPart_symm _ _ (hD.symm t ξ) α β
  herm_metric α β t ht ξ := by
    have e : hh t (-ξ) = fun γ δ => conj (hh t ξ γ δ) :=
      funext fun γ => funext fun δ => hD.herm_metric γ δ t ht ξ
    simp only [amp, tensorData, wave_neg, ScalarVectorTensor.tensorPart_neg, e]
    exact ScalarVectorTensor.tensorPart_map _ (starRingEnd ℂ) (conj_wave ξ) α β
  herm_density _ _ _ := by simp
  herm_velocity _ _ _ _ := by simp [vamp]

/-- Outside the spectrum every frequency satisfies the equations trivially. -/
theorem frequencyEq_of_notMem (hD : IsFourierData B.I K hh dd vv) {t : ℝ} (ht : t ∈ B.I)
    {ξ : E3} (hξ : ξ ∉ K) : FrequencyEq B κ ρ hh dd vv t ξ := by
  have h0 : hh t ξ = 0 := funext fun α => funext fun β => (hD.metric α β).support t ht ξ hξ
  have h1 : jet1 hh t ξ = 0 := funext fun α => funext fun β =>
    ((hD.metric α β).timeDeriv B.isOpen_I).support t ht ξ hξ
  have h2 : jet2 hh t ξ = 0 := funext fun α => funext fun β =>
    (((hD.metric α β).timeDeriv B.isOpen_I).timeDeriv B.isOpen_I).support t ht ξ hξ
  have hd : dd t ξ = 0 := hD.density.support t ht ξ hξ
  have hv : vv t ξ = 0 := funext fun α => (hD.velocity α).support t ht ξ hξ
  rw [FrequencyEq, h0, h1, h2, hd, hv]
  exact ScalarVectorTensor.symbolEq_zero _ _

theorem jet1_linearMap (hD : IsFourierData B.I K hh dd vv) (L : E3 → Mat3 ℂ →ₗ[ℂ] Mat3 ℂ)
    {t : ℝ} (ht : t ∈ B.I) (ξ : E3) :
    jet1 (fun t ξ => L ξ (hh t ξ)) t ξ = L ξ (jet1 hh t ξ) :=
  funext fun α => funext fun β => timeDeriv_linearMap hD L ht ξ α β

theorem jet2_linearMap (hD : IsFourierData B.I K hh dd vv) (L : E3 → Mat3 ℂ →ₗ[ℂ] Mat3 ℂ)
    {t : ℝ} (ht : t ∈ B.I) (ξ : E3) :
    jet2 (fun t ξ => L ξ (hh t ξ)) t ξ = L ξ (jet2 hh t ξ) :=
  funext fun α => funext fun β => timeDeriv_timeDeriv_linearMap hD L ht ξ α β

/-- **The decomposition of the equations of one frequency** into those of the scalar, vector and
tensor parts. -/
theorem frequencyEq_iff_split (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K)
    (h0K : (0 : E3) ∉ K) {t : ℝ} (ht : t ∈ B.I) (ξ : E3) :
    FrequencyEq B κ ρ hh dd vv t ξ ↔
      FrequencyEq B κ ρ (scalarData hh) dd (longData vv) t ξ ∧
      FrequencyEq B κ ρ (vectorData hh) (fun _ _ => 0) (transData vv) t ξ ∧
      FrequencyEq B κ ρ (tensorData hh) (fun _ _ => 0) (fun _ _ _ => 0) t ξ := by
  rcases em (ξ ∈ K) with hξK | hξ
  · have hξ : ξ ≠ 0 := fun h => h0K (h ▸ hξK)
    have s1 : jet1 (scalarData hh) t ξ = scalarPart (wave ξ) (jet1 hh t ξ) :=
      jet1_linearMap hD (fun ξ => scalarPart (wave ξ)) ht ξ
    have s2 : jet2 (scalarData hh) t ξ = scalarPart (wave ξ) (jet2 hh t ξ) :=
      jet2_linearMap hD (fun ξ => scalarPart (wave ξ)) ht ξ
    have v1 : jet1 (vectorData hh) t ξ = vectorPart (wave ξ) (jet1 hh t ξ) :=
      jet1_linearMap hD (fun ξ => vectorPart (wave ξ)) ht ξ
    have v2 : jet2 (vectorData hh) t ξ = vectorPart (wave ξ) (jet2 hh t ξ) :=
      jet2_linearMap hD (fun ξ => vectorPart (wave ξ)) ht ξ
    have t1 : jet1 (tensorData hh) t ξ = tensorPart (wave ξ) (jet1 hh t ξ) :=
      jet1_linearMap hD (fun ξ => tensorPart (wave ξ)) ht ξ
    have t2 : jet2 (tensorData hh) t ξ = tensorPart (wave ξ) (jet2 hh t ξ) :=
      jet2_linearMap hD (fun ξ => tensorPart (wave ξ)) ht ξ
    simp only [FrequencyEq, s1, s2, v1, v2, t1, t2]
    exact ScalarVectorTensor.symbolEq_iff _ _ _ _ _ _ (nsq_wave_ne_zero hξ)
  · exact ⟨fun _ => ⟨frequencyEq_of_notMem (isFourierData_scalar hD hK h0K) ht hξ,
      frequencyEq_of_notMem (isFourierData_vector hD hK h0K) ht hξ,
      frequencyEq_of_notMem (isFourierData_tensor hD hK h0K) ht hξ⟩,
      fun _ => frequencyEq_of_notMem hD ht hξ⟩

@[simp] theorem scalarOf_zero : scalarOf (fun _ _ => 0) = fun _ => 0 := by
  funext z; simp [scalarOf]

@[simp] theorem vectorOf_zero : vectorOf (fun _ _ _ => 0) = fun _ _ => 0 := by
  funext z α
  show (synthesis (fun _ _ => (0 : ℂ)) z).re = 0
  simp

/-- **The scalar–vector–tensor decomposition of the linearized equations**: a perturbation given
by Fourier data supported away from `ξ = 0` solves the linearized Einstein equations with dust if
and only if its scalar part (with the density contrast and the longitudinal velocity), its vector
part (with the transverse velocity) and its tensor part do. -/
theorem linearizedEinsteinDust_iff_split (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K)
    (h0K : (0 : E3) ∉ K) :
    LinearizedEinsteinDust B κ ρ (fieldOf hh) (scalarOf dd) (vectorOf vv) ↔
      LinearizedEinsteinDust B κ ρ (fieldOf (scalarData hh)) (scalarOf dd)
          (vectorOf (longData vv)) ∧
        LinearizedEinsteinDust B κ ρ (fieldOf (vectorData hh)) (fun _ => 0)
          (vectorOf (transData vv)) ∧
        LinearizedEinsteinDust B κ ρ (fieldOf (tensorData hh)) (fun _ => 0) (fun _ _ => 0) := by
  have hS := linearizedEinsteinDust_iff_frequencyEq (κ := κ) (ρ := ρ)
    (isFourierData_scalar hD hK h0K) hK
  have hV := linearizedEinsteinDust_iff_frequencyEq (κ := κ) (ρ := ρ)
    (isFourierData_vector hD hK h0K) hK
  have hT := linearizedEinsteinDust_iff_frequencyEq (κ := κ) (ρ := ρ)
    (isFourierData_tensor hD hK h0K) hK
  rw [scalarOf_zero] at hV hT
  rw [vectorOf_zero] at hT
  rw [linearizedEinsteinDust_iff_frequencyEq hD hK, hS, hV, hT]
  constructor
  · intro h
    exact ⟨fun t ht ξ => ((frequencyEq_iff_split hD hK h0K ht ξ).mp (h t ht ξ)).1,
      fun t ht ξ => ((frequencyEq_iff_split hD hK h0K ht ξ).mp (h t ht ξ)).2.1,
      fun t ht ξ => ((frequencyEq_iff_split hD hK h0K ht ξ).mp (h t ht ξ)).2.2⟩
  · rintro ⟨h1, h2, h3⟩ t ht ξ
    exact (frequencyEq_iff_split hD hK h0K ht ξ).mpr ⟨h1 t ht ξ, h2 t ht ξ, h3 t ht ξ⟩

/-- **The perturbation is the sum of its scalar, vector and tensor parts.** -/
theorem fieldOf_eq_add (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K)
    (h0K : (0 : E3) ∉ K) (hz : z ∈ slab B.I) (α β : Fin 3) :
    fieldOf hh z α β = fieldOf (scalarData hh) z α β + fieldOf (vectorData hh) z α β +
      fieldOf (tensorData hh) z α β := by
  have hS := (isFourierData_scalar hD hK h0K).metric α β
  have hV := (isFourierData_vector hD hK h0K).metric α β
  have hT := (isFourierData_tensor hD hK h0K).metric α β
  have e : amp hh α β = fun t ξ => (amp (scalarData hh) α β t ξ + amp (vectorData hh) α β t ξ) +
      amp (tensorData hh) α β t ξ := by
    funext t ξ
    have := congrFun (congrFun
      (ScalarVectorTensor.scalarPart_add_vectorPart_add_tensorPart (wave ξ) (hh t ξ)) α) β
    simpa only [amp, scalarData, vectorData, tensorData, Pi.add_apply] using this.symm
  simp only [fieldOf]
  rw [e, synthesis_add ((hS.add hV).integrable_integrand hK hz) (hT.integrable_integrand hK hz),
    synthesis_add (hS.integrable_integrand hK hz) (hV.integrable_integrand hK hz)]
  simp only [Complex.add_re]

/-- The velocity is the sum of its longitudinal and transverse parts. -/
theorem vectorOf_eq_add (hD : IsFourierData B.I K hh dd vv) (hK : IsCompact K)
    (h0K : (0 : E3) ∉ K) (hz : z ∈ slab B.I) (α : Fin 3) :
    vectorOf vv z α = vectorOf (longData vv) z α + vectorOf (transData vv) z α := by
  have hL := (isFourierData_scalar hD hK h0K).velocity α
  have hT := (isFourierData_vector hD hK h0K).velocity α
  have e : vamp vv α = fun t ξ => vamp (longData vv) α t ξ + vamp (transData vv) α t ξ := by
    funext t ξ
    have := congrFun (ScalarVectorTensor.longVec_add_transVec (wave ξ) (vv t ξ)) α
    simpa only [vamp, longData, transData, Pi.add_apply] using this.symm
  simp only [vectorOf]
  rw [e, synthesis_add (hL.integrable_integrand hK hz) (hT.integrable_integrand hK hz)]
  simp only [Complex.add_re]

/-! ### Reconstruction of a perturbation from its spatial Fourier transforms -/

/-- The linearized equations only depend on the fields on the domain. -/
theorem linearizedEinsteinDust_congr {h h' : E → Fin 3 → Fin 3 → ℝ} {δ δ' : E → ℝ}
    {v v' : E → Fin 3 → ℝ} (hh : ∀ z ∈ domain B.toData, h z = h' z)
    (hδ : ∀ z ∈ domain B.toData, δ z = δ' z) (hv : ∀ z ∈ domain B.toData, v z = v' z) :
    LinearizedEinsteinDust B κ ρ h δ v ↔ LinearizedEinsteinDust B κ ρ h' δ' v' := by
  have hO := (domain B.toData).isOpen
  have e1 : ∀ z ∈ domain B.toData, ∀ c α β, dh h c z α β = dh h' c z α β := fun z hz c α β => by
    have : (fun w => h w α β) =ᶠ[𝓝 z] fun w => h' w α β :=
      eventually_of_mem (hO.mem_nhds hz) fun w hw => by
        show h w α β = h' w α β
        rw [hh w hw]
    simp only [dh, this.fderiv_eq]
  have e2 : ∀ z ∈ domain B.toData, ∀ c e α β, ddh h c e z α β = ddh h' c e z α β :=
    fun z hz c e α β => by
      have : (fun w => dh h e w α β) =ᶠ[𝓝 z] fun w => dh h' e w α β :=
        eventually_of_mem (hO.mem_nhds hz) fun w hw => e1 w hw e α β
      simp only [ddh, this.fderiv_eq]
  refine forall₂_congr fun z hz => forall₂_congr fun i k => ?_
  have eR : linRicci B h z i k = linRicci B h' z i k := by
    simp only [linRicci, linRicciTime, linRicciMixed, linRicciSpace, e1 z hz, e2 z hz, hh z hz]
  have eD : linDust B ρ h δ v z i k = linDust B ρ h' δ' v' z i k := by
    simp only [linDust, hh z hz, hδ z hz, hv z hz]
  rw [eR, eD]

/-- The spatial Fourier transforms `ĥ(t, ξ)` of the slices of a metric perturbation. -/
def fourierMetric (h : E → Fin 3 → Fin 3 → ℝ) : ℝ → E3 → Mat3 ℂ :=
  fun t ξ α β => 𝓕 (fun x : E3 => (h (spacetimePoint t x) α β : ℂ)) ξ

/-- The spatial Fourier transforms `δ̂(t, ξ)` of the slices of a density contrast. -/
def fourierScalar (δ : E → ℝ) : ℝ → E3 → ℂ :=
  fun t => 𝓕 fun x : E3 => (δ (spacetimePoint t x) : ℂ)

/-- The spatial Fourier transforms `v̂(t, ξ)` of the slices of a velocity. -/
def fourierVector (v : E → Fin 3 → ℝ) : ℝ → E3 → Fin 3 → ℂ :=
  fun t ξ α => 𝓕 (fun x : E3 => (v (spacetimePoint t x) α : ℂ)) ξ

/-- **A perturbation with a compact spectrum**: at every time of `I` its spatial slices are
continuous and integrable, the metric perturbation is symmetric, and the spatial Fourier
transforms of the slices are of the class (smooth in `(t, ξ)`, vanishing for `ξ ∉ K`). -/
structure HasCompactSpectrum (I : Set ℝ) (K : Set E3) (h : E → Fin 3 → Fin 3 → ℝ) (δ : E → ℝ)
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
  /-- The transforms of the metric perturbation are of the class. -/
  metric : ∀ α β, IsCompactAmplitude I K (amp (fourierMetric h) α β)
  /-- The transforms of the density contrast are of the class. -/
  density : IsCompactAmplitude I K (fourierScalar δ)
  /-- The transforms of the velocity are of the class. -/
  velocity : ∀ α, IsCompactAmplitude I K (vamp (fourierVector v) α)

variable {h : E → Fin 3 → Fin 3 → ℝ} {δ : E → ℝ} {v : E → Fin 3 → ℝ}

/-- The transforms of a perturbation with a compact spectrum are Fourier data. -/
theorem HasCompactSpectrum.isFourierData (hS : HasCompactSpectrum I K h δ v) :
    IsFourierData I K (fourierMetric h) (fourierScalar δ) (fourierVector v) where
  metric := hS.metric
  density := hS.density
  velocity := hS.velocity
  symm t ξ α β := by simp only [fourierMetric, hS.symm _ α β]
  herm_metric α β t _ ξ :=
    fourier_neg_of_real _ (fun _ => Complex.conj_ofReal _) ξ
  herm_density t _ ξ := fourier_neg_of_real _ (fun _ => Complex.conj_ofReal _) ξ
  herm_velocity α t _ ξ := fourier_neg_of_real _ (fun _ => Complex.conj_ofReal _) ξ

/-- **Fourier inversion**: a perturbation with a compact spectrum is the synthesis of its
transforms on the slab. -/
theorem HasCompactSpectrum.eq_synthesis (hS : HasCompactSpectrum I K h δ v) (hK : IsCompact K)
    (hz : z ∈ slab I) :
    h z = fieldOf (fourierMetric h) z ∧ δ z = scalarOf (fourierScalar δ) z ∧
      v z = vectorOf (fourierVector v) z := by
  refine ⟨funext fun α => funext fun β => ?_, ?_, funext fun α => ?_⟩
  · have e := synthesis_fourier (fun w => (h w α β : ℂ)) (z := z)
      (Complex.continuous_ofReal.comp (hS.continuous_metric (z 0) hz α β))
      (hS.integrable_metric (z 0) hz α β).ofReal ((hS.metric α β).integrable hK hz)
    simp only [fieldOf]
    rw [show amp (fourierMetric h) α β = fun t => 𝓕 fun x : E3 => (h (spacetimePoint t x) α β : ℂ)
      from rfl, e, Complex.ofReal_re]
  · have e := synthesis_fourier (fun w => (δ w : ℂ)) (z := z)
      (Complex.continuous_ofReal.comp (hS.continuous_density (z 0) hz))
      (hS.integrable_density (z 0) hz).ofReal (hS.density.integrable hK hz)
    simp only [scalarOf]
    rw [show fourierScalar δ = fun t => 𝓕 fun x : E3 => (δ (spacetimePoint t x) : ℂ) from rfl, e,
      Complex.ofReal_re]
  · have e := synthesis_fourier (fun w => (v w α : ℂ)) (z := z)
      (Complex.continuous_ofReal.comp (hS.continuous_velocity (z 0) hz α))
      (hS.integrable_velocity (z 0) hz α).ofReal ((hS.velocity α).integrable hK hz)
    simp only [vectorOf]
    rw [show vamp (fourierVector v) α = fun t => 𝓕 fun x : E3 => (v (spacetimePoint t x) α : ℂ)
      from rfl, e, Complex.ofReal_re]

/-- **The reconstruction**: a perturbation with a compact spectrum solves the linearized
equations if and only if every frequency of its transforms satisfies the mode equations. -/
theorem HasCompactSpectrum.linearizedEinsteinDust_iff (hS : HasCompactSpectrum B.I K h δ v)
    (hK : IsCompact K) :
    LinearizedEinsteinDust B κ ρ h δ v ↔ ∀ t ∈ B.I, ∀ ξ,
      FrequencyEq B κ ρ (fourierMetric h) (fourierScalar δ) (fourierVector v) t ξ := by
  rw [linearizedEinsteinDust_congr (h' := fieldOf (fourierMetric h))
    (δ' := scalarOf (fourierScalar δ)) (v' := vectorOf (fourierVector v))
    (fun z hz => (hS.eq_synthesis hK (by rwa [← domain_eq_slab])).1)
    (fun z hz => (hS.eq_synthesis hK (by rwa [← domain_eq_slab])).2.1)
    (fun z hz => (hS.eq_synthesis hK (by rwa [← domain_eq_slab])).2.2)]
  exact linearizedEinsteinDust_iff_frequencyEq hS.isFourierData hK

/-- **Every solution with a spectrum in a compact set away from `ξ = 0` is the sum of the
syntheses of its scalar, vector and tensor components**, each of which solves the linearized
equations, and conversely. -/
theorem HasCompactSpectrum.reconstruction (hS : HasCompactSpectrum B.I K h δ v)
    (hK : IsCompact K) (h0K : (0 : E3) ∉ K) :
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
  have hD := hS.isFourierData
  have hz' (z : E) (hz : z ∈ domain B.toData) : z ∈ slab B.I := by rwa [← domain_eq_slab]
  refine ⟨fun z hz α β => ?_, fun z hz α => ?_, ?_⟩
  · rw [(hS.eq_synthesis hK (hz' z hz)).1]
    exact fieldOf_eq_add hD hK h0K (hz' z hz) α β
  · rw [(hS.eq_synthesis hK (hz' z hz)).2.2]
    exact vectorOf_eq_add hD hK h0K (hz' z hz) α
  · rw [linearizedEinsteinDust_congr (h' := fieldOf (fourierMetric h))
      (δ' := scalarOf (fourierScalar δ)) (v' := vectorOf (fourierVector v))
      (fun z hz => (hS.eq_synthesis hK (hz' z hz)).1)
      (fun z hz => (hS.eq_synthesis hK (hz' z hz)).2.1)
      (fun z hz => (hS.eq_synthesis hK (hz' z hz)).2.2),
      linearizedEinsteinDust_iff_split hD hK h0K,
      linearizedEinsteinDust_congr (h := fieldOf (scalarData (fourierMetric h)))
        (h' := fieldOf (scalarData (fourierMetric h))) (δ := scalarOf (fourierScalar δ))
        (δ' := δ) (v := vectorOf (longData (fourierVector v)))
        (v' := vectorOf (longData (fourierVector v))) (fun _ _ => rfl)
        (fun z hz => (hS.eq_synthesis hK (hz' z hz)).2.1.symm) (fun _ _ => rfl)]

/-- **Conversely, the synthesis of Fourier data has a compact spectrum**, and its transforms are
the data on `I`. -/
theorem IsFourierData.hasCompactSpectrum (hD : IsFourierData I K hh dd vv) (hK : IsCompact K) :
    HasCompactSpectrum I K (fieldOf hh) (scalarOf dd) (vectorOf vv) ∧
      (∀ t ∈ I, fourierMetric (fieldOf hh) t = hh t ∧ fourierScalar (scalarOf dd) t = dd t ∧
        fourierVector (vectorOf vv) t = vv t) := by
  have sl (G : ℝ → E3 → ℂ) (hG : IsCompactAmplitude I K G) (hH : IsHermitian I G) {t : ℝ}
      (ht : t ∈ I) : (fun x : E3 => (((synthesis G (spacetimePoint t x)).re : ℝ) : ℂ)) =
        fun x => synthesis G (spacetimePoint t x) :=
    funext fun x => ofReal_re_synthesis fun ξ => hH t ht ξ
  have hre (G : ℝ → E3 → ℂ) (hG : IsCompactAmplitude I K G) (hH : IsHermitian I G) {t : ℝ}
      (ht : t ∈ I) : 𝓕 (fun x : E3 => (((synthesis G (spacetimePoint t x)).re : ℝ) : ℂ)) = G t := by
    rw [sl G hG hH ht, fourier_synthesis_slice hG hK ht]
  have hmet : ∀ t ∈ I, fourierMetric (fieldOf hh) t = hh t := fun t ht => funext fun ξ =>
    funext fun α => funext fun β => by
      simp only [fourierMetric, fieldOf]
      rw [hre _ (hD.metric α β) (hD.herm_metric α β) ht]; rfl
  have hden : ∀ t ∈ I, fourierScalar (scalarOf dd) t = dd t := fun t ht => by
    simp only [fourierScalar, scalarOf]
    exact hre _ hD.density hD.herm_density ht
  have hvel : ∀ t ∈ I, fourierVector (vectorOf vv) t = vv t := fun t ht => funext fun ξ =>
    funext fun α => by
      simp only [fourierVector, vectorOf]
      rw [hre _ (hD.velocity α) (hD.herm_velocity α) ht]; rfl
  have congrAmp {G G' : ℝ → E3 → ℂ} (hG : IsCompactAmplitude I K G)
      (e : ∀ t ∈ I, G' t = G t) : IsCompactAmplitude I K G' :=
    ⟨hG.smooth.congr fun q hq => by simp only [uncurry]; rw [e q.1 hq.1],
      fun t ht ξ hξ => by rw [e t ht]; exact hG.support t ht ξ hξ⟩
  refine ⟨⟨fun t ht α β => ?_, fun t ht α β => ?_, fun t ht => ?_, fun t ht => ?_,
    fun t ht α => ?_, fun t ht α => ?_, fun z α β => ?_,
    fun α β => congrAmp (hD.metric α β) fun t ht => by
      funext ξ; exact congrFun (congrFun (congrFun (hmet t ht) ξ) α) β,
    congrAmp hD.density hden,
    fun α => congrAmp (hD.velocity α) fun t ht => by
      funext ξ; exact congrFun (congrFun (hvel t ht) ξ) α⟩,
    fun t ht => ⟨hmet t ht, hden t ht, hvel t ht⟩⟩
  · exact Complex.continuous_re.comp (continuous_synthesis_slice (hD.metric α β) hK ht)
  · exact (integrable_synthesis_slice (hD.metric α β) hK ht).re
  · exact Complex.continuous_re.comp (continuous_synthesis_slice hD.density hK ht)
  · exact (integrable_synthesis_slice hD.density hK ht).re
  · exact Complex.continuous_re.comp (continuous_synthesis_slice (hD.velocity α) hK ht)
  · exact (integrable_synthesis_slice (hD.velocity α) hK ht).re
  · have e : amp hh α β = amp hh β α := funext fun t => funext fun ξ => hD.symm t ξ α β
    simp only [fieldOf, e]

end ProjectAinos.GeneralRelativity.CosmologicalPerturbation.Reconstruction
