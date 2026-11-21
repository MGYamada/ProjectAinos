/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.CosmologicalPerturbation
public import ProjectAinos.SmoothGeometry.Tensor.ScalarVectorTensor
public import ProjectAinos.GeneralRelativity.PerturbationReconstruction
import Mathlib.Tactic

/-!
# The scalar–vector–tensor split of a single plane wave

Landau–Lifshitz, §115, flat dust universe in the synchronous reference system. For a plane wave
`h_{αβ} = F_{αβ}(t) k(n · x)`, `δ = δ̂(t) k(n · x)`, `v_α = V_α(t) k'(n · x)` (`mode`, with
`k'' = −k`), `mode_iff` reduces the linearized Einstein equations with dust to the ordinary
differential equations `ModeEq` of the amplitudes; they are the system
`ScalarVectorTensor.SymbolEq` with the real coefficients `realCoeffs` (`modeEq_iff_symbolEq`).

* `modeEq_iff_split`, `linearizedEinsteinDust_mode_iff_split`: **the equations of a plane wave
  hold if and only if they hold for its scalar part** (with the density contrast and the
  longitudinal velocity), **its vector part** (with the transverse velocity) **and its tensor
  part**, the projections `scalarPart n`, `vectorPart n`, `tensorPart n` of the amplitude
  (`projAmp`) and `longVec n`, `transVec n` of the velocity (`projVel`).
* `mode_scalarPart_eq`: the scalar part of a `cos` wave is the scalar mode `scalarMode n λ μ` of
  `CosmologicalPerturbation` with `λ = (3 nFn/n² − tr F)/2` and `μ = tr F` (`lamOf`, `muOf`), so
  `scalar_sector_iff` reduces it to the equations of `scalarMode_iff`.
* `tensor_sector_iff`: on a dust background the tensor part satisfies
  `T̈ + 3(ȧ/a) Ṫ + (n²/a²) T = 0`, the equation of `tensorMode_iff`, entry by entry.
* `vector_sector_iff`: on a dust background the transverse vector `u = nF − (nFn/n²) n` of the
  amplitude satisfies `ü + 3(ȧ/a) u̇ = 0` and `½ u̇ + κρ V_⊥ = 0`, the equations of
  `vectorMode_iff` (for `F = σ(n ⊗ e + e ⊗ n)`, `u = σ n² e`).
* `frequencyEq_iff_modeEq`, `frequencyEq_iff_planeWaves`: the complex equations
  `Reconstruction.FrequencyEq` of one frequency `ξ` of Fourier data are the equations `ModeEq`
  of the real amplitudes `Re ĥ, Re δ̂, Im v̂` and `Im ĥ, Im δ̂, −Re v̂` with `n = 2πξ`, that is,
  the two real `cos` plane waves of the frequency solve the linearized equations.
-/

@[expose] public section

noncomputable section

open Set Filter Function
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.CosmologicalPerturbation.ModeSplit

open SmoothGeometry CoordinateMetric FLRW
open SmoothGeometry.ScalarVectorTensor (Mat3 Coeffs SymbolEq resTime resMixed resSpace
  scalarPart vectorPart tensorPart longVec transVec shear)

local notation "E" => MinkowskiModel 3

/-- The coefficients of the equations of a real plane wave at the time `t`; the mixed equation
has the factor `½`. -/
def realCoeffs (B : Background) (κ : ℝ) (ρ : ℝ → ℝ) (t : ℝ) : Coeffs ℝ where
  hub := deriv B.a t / B.a t
  dens := κ * ρ t
  mixC := 1 / 2
  c₁ := 2 * deriv B.a t ^ 2 + B.a t * deriv (deriv B.a) t
  c₂ := 3 / 2 * (B.a t * deriv B.a t)
  c₃ := B.a t ^ 2 / 2
  c₄ := B.a t * deriv B.a t / 2
  src := κ * (ρ t * B.a t ^ 2) / 2

/-- **The equations of the amplitudes of a plane wave** at the time `t`, the right-hand side of
`mode_iff`. -/
def ModeEq (B : Background) (κ : ℝ) (ρ : ℝ → ℝ) (F : ℝ → Fin 3 → Fin 3 → ℝ) (n : Fin 3 → ℝ)
    (dc : ℝ → ℝ) (V : ℝ → Fin 3 → ℝ) (t : ℝ) : Prop :=
  modeTime B F t = κ * (ρ t * dc t / 2) ∧ (∀ α, modeMixed F n t α = κ * -(ρ t * V t α)) ∧
    ∀ α β, modeSpace B F n t α β =
      κ * (ρ t * B.a t ^ 2 * ((if α = β then dc t else 0) + F t α β) / 2)

variable {B : Background} {κ : ℝ} {ρ : ℝ → ℝ} {F : ℝ → Fin 3 → Fin 3 → ℝ} {n : Fin 3 → ℝ}

/-- The equations of the amplitudes are the system `SymbolEq` with the real coefficients. -/
theorem modeEq_iff_symbolEq (dc : ℝ → ℝ) (V : ℝ → Fin 3 → ℝ) (t : ℝ) :
    ModeEq B κ ρ F n dc V t ↔
      SymbolEq (realCoeffs B κ ρ t) n (F t) (Fd F t) (Fdd F t) (dc t) (V t) := by
  have e0 : resTime (realCoeffs B κ ρ t) (Fd F t) (Fdd F t) (dc t) =
      modeTime B F t - κ * (ρ t * dc t / 2) := by
    simp only [resTime, realCoeffs, ScalarVectorTensor.trace, modeTime]; ring
  have e1 (α : Fin 3) : resMixed (realCoeffs B κ ρ t) n (Fd F t) (V t) α =
      modeMixed F n t α - κ * -(ρ t * V t α) := by
    simp only [resMixed, realCoeffs, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      ScalarVectorTensor.mix_apply, ScalarVectorTensor.contract, ScalarVectorTensor.trace,
      modeMixed]
    ring
  have e2 (α β : Fin 3) : resSpace (realCoeffs B κ ρ t) n (F t) (Fd F t) (Fdd F t) (dc t) α β =
      modeSpace B F n t α β -
        κ * (ρ t * B.a t ^ 2 * ((if α = β then dc t else 0) + F t α β) / 2) := by
    simp only [resSpace, realCoeffs, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      ScalarVectorTensor.op_apply, ScalarVectorTensor.contract, ScalarVectorTensor.trace,
      ScalarVectorTensor.nsq, ScalarVectorTensor.delta, modeSpace, nsq]
    split_ifs <;> ring
  simp only [ModeEq, SymbolEq, funext_iff, e0, e1, e2, sub_eq_zero, Pi.zero_apply]

/-! ### The projected amplitudes -/

/-- The amplitude `L(F(t))` for a linear map `L` of the matrices. -/
def projAmp (L : Mat3 ℝ →ₗ[ℝ] Mat3 ℝ) (F : ℝ → Fin 3 → Fin 3 → ℝ) : ℝ → Fin 3 → Fin 3 → ℝ :=
  fun t => L (F t)

/-- The velocity amplitude `L(V(t))` for a linear map `L` of the vectors. -/
def projVel (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (V : ℝ → Fin 3 → ℝ) : ℝ → Fin 3 → ℝ :=
  fun t => L (V t)

theorem hasDerivAt_linearMap_apply (L : Mat3 ℝ →ₗ[ℝ] Mat3 ℝ) {M : ℝ → Mat3 ℝ} {M' : Mat3 ℝ}
    {t : ℝ} (h : ∀ α β, HasDerivAt (fun s => M s α β) (M' α β) t) (α β : Fin 3) :
    HasDerivAt (fun s => L (M s) α β) (L M' α β) t := by
  have hM : HasDerivAt M M' t := hasDerivAt_pi.2 fun α => hasDerivAt_pi.2 fun β => h α β
  let Lc : Mat3 ℝ →L[ℝ] Mat3 ℝ := LinearMap.toContinuousLinearMap L
  have h2 : HasDerivAt (fun s => Lc (M s)) (Lc M') t := Lc.hasFDerivAt.comp_hasDerivAt t hM
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h2 α) β

theorem Fd_projAmp (hF : IsAmplitude B F) {t : ℝ} (ht : t ∈ B.I) (L : Mat3 ℝ →ₗ[ℝ] Mat3 ℝ) :
    Fd (projAmp L F) t = L (Fd F t) :=
  funext fun α => funext fun β =>
    (hasDerivAt_linearMap_apply L (fun γ δ => hF.hasDerivAt ht γ δ) α β).deriv

theorem Fdd_projAmp (hF : IsAmplitude B F) {t : ℝ} (ht : t ∈ B.I) (L : Mat3 ℝ →ₗ[ℝ] Mat3 ℝ) :
    Fdd (projAmp L F) t = L (Fdd F t) := by
  funext α β
  have hev : (deriv fun s => projAmp L F s α β) =ᶠ[𝓝 t] fun s => L (Fd F s) α β :=
    eventually_of_mem (B.isOpen_I.mem_nhds ht) fun s hs => by
      have := congrFun (congrFun (Fd_projAmp hF hs L) α) β
      simpa only [Fd] using this
  simp only [Fdd]
  rw [hev.deriv_eq]
  exact (hasDerivAt_linearMap_apply L (fun γ δ => hF.hasDerivAt_Fd ht γ δ) α β).deriv

/-- A linear map of the matrices that preserves the symmetry maps amplitudes to amplitudes. -/
theorem isAmplitude_projAmp (hF : IsAmplitude B F) (L : Mat3 ℝ →ₗ[ℝ] Mat3 ℝ)
    (hL : ∀ t α β, L (F t) α β = L (F t) β α) : IsAmplitude B (projAmp L F) where
  smooth α β := by
    have e : (fun t => projAmp L F t α β) = fun t =>
        ∑ γ, ∑ δ, F t γ δ * L (Pi.single γ (Pi.single δ 1)) α β := by
      funext t; exact ScalarVectorTensor.linearMap_apply_eq_sum L (F t) α β
    rw [e]
    exact ContDiffOn.sum fun γ _ => ContDiffOn.sum fun δ _ => (hF.smooth γ δ).mul contDiffOn_const
  symm t α β := hL t α β

theorem isAmplitude_scalarPart (hF : IsAmplitude B F) :
    IsAmplitude B (projAmp (scalarPart n) F) :=
  isAmplitude_projAmp hF _ fun _ α β => ScalarVectorTensor.scalarPart_symm _ _ α β

theorem isAmplitude_vectorPart (hF : IsAmplitude B F) :
    IsAmplitude B (projAmp (vectorPart n) F) :=
  isAmplitude_projAmp hF _ fun _ α β => ScalarVectorTensor.vectorPart_symm _ _ α β

theorem isAmplitude_tensorPart (hF : IsAmplitude B F) :
    IsAmplitude B (projAmp (tensorPart n) F) :=
  isAmplitude_projAmp hF _ fun t α β => ScalarVectorTensor.tensorPart_symm _ _ (hF.symm t) α β

/-! ### The split -/

/-- **The decomposition of the equations of the amplitudes of a plane wave.** -/
theorem modeEq_iff_split (hF : IsAmplitude B F) (hn : nsq n ≠ 0) (dc : ℝ → ℝ)
    (V : ℝ → Fin 3 → ℝ) :
    (∀ t ∈ B.I, ModeEq B κ ρ F n dc V t) ↔
      (∀ t ∈ B.I, ModeEq B κ ρ (projAmp (scalarPart n) F) n dc (projVel (longVec n) V) t) ∧
      (∀ t ∈ B.I, ModeEq B κ ρ (projAmp (vectorPart n) F) n (fun _ => 0)
        (projVel (transVec n) V) t) ∧
      (∀ t ∈ B.I, ModeEq B κ ρ (projAmp (tensorPart n) F) n (fun _ => 0) (fun _ _ => 0) t) := by
  have hn' : ScalarVectorTensor.nsq n ≠ 0 := hn
  have key (t : ℝ) (ht : t ∈ B.I) := ScalarVectorTensor.symbolEq_iff (realCoeffs B κ ρ t)
    (F t) (Fd F t) (Fdd F t) (dc t) (V t) hn'
  simp only [modeEq_iff_symbolEq]
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩ <;>
      rw [Fd_projAmp hF ht, Fdd_projAmp hF ht]
    · exact ((key t ht).mp (h t ht)).1
    · exact ((key t ht).mp (h t ht)).2.1
    · exact ((key t ht).mp (h t ht)).2.2
  · rintro ⟨h1, h2, h3⟩ t ht
    have a1 := h1 t ht
    have a2 := h2 t ht
    have a3 := h3 t ht
    rw [Fd_projAmp hF ht, Fdd_projAmp hF ht] at a1 a2 a3
    exact (key t ht).mpr ⟨a1, a2, a3⟩

/-- **The scalar–vector–tensor decomposition of a plane wave**: the wave solves the linearized
Einstein equations with dust if and only if its scalar, vector and tensor parts do. -/
theorem linearizedEinsteinDust_mode_iff_split {k k₁ : ℝ → ℝ} (hF : IsAmplitude B F)
    (hk : IsProfile k k₁) (hn : nsq n ≠ 0) (hk0 : ∃ s, k s ≠ 0) (hk1 : ∃ s, k₁ s ≠ 0)
    (dc : ℝ → ℝ) (V : ℝ → Fin 3 → ℝ) :
    LinearizedEinsteinDust B κ ρ (mode F k n) (fun z => dc (z 0) * k (phase n z))
        (fun z α => V (z 0) α * k₁ (phase n z)) ↔
      LinearizedEinsteinDust B κ ρ (mode (projAmp (scalarPart n) F) k n)
          (fun z => dc (z 0) * k (phase n z))
          (fun z α => projVel (longVec n) V (z 0) α * k₁ (phase n z)) ∧
        LinearizedEinsteinDust B κ ρ (mode (projAmp (vectorPart n) F) k n) (fun _ => 0)
          (fun z α => projVel (transVec n) V (z 0) α * k₁ (phase n z)) ∧
        LinearizedEinsteinDust B κ ρ (mode (projAmp (tensorPart n) F) k n) (fun _ => 0)
          (fun _ _ => 0) := by
  have z0 : (fun _ : E => (0 : ℝ)) = fun z => (fun _ : ℝ => (0 : ℝ)) (z 0) * k (phase n z) := by
    funext z; simp
  have z1 : (fun (_ : E) (_ : Fin 3) => (0 : ℝ)) =
      fun z α => (fun (_ : ℝ) (_ : Fin 3) => (0 : ℝ)) (z 0) α * k₁ (phase n z) := by
    funext z α; simp
  rw [z0, z1]
  refine (mode_iff hF hk hn hk0 hk1 dc V).trans ((modeEq_iff_split hF hn dc V).trans ?_)
  exact and_congr (mode_iff (isAmplitude_scalarPart (n := n) hF) hk hn hk0 hk1 dc
    (projVel (longVec n) V)).symm (and_congr (mode_iff (isAmplitude_vectorPart (n := n) hF) hk hn
      hk0 hk1 (fun _ => 0) (projVel (transVec n) V)).symm
    (mode_iff (isAmplitude_tensorPart (n := n) hF) hk hn hk0 hk1 (fun _ => 0)
      (fun _ _ => 0)).symm)

/-! ### The three sectors -/

/-- The parameter `λ = (3 nFn/n² − tr F)/2` of the scalar part. -/
def lamOf (n : Fin 3 → ℝ) (F : ℝ → Fin 3 → Fin 3 → ℝ) (t : ℝ) : ℝ :=
  (3 * ScalarVectorTensor.longCoeff n (F t) - ScalarVectorTensor.trace (F t)) / 2

/-- The parameter `μ = tr F` of the scalar part. -/
def muOf (F : ℝ → Fin 3 → Fin 3 → ℝ) (t : ℝ) : ℝ := ScalarVectorTensor.trace (F t)

theorem projAmp_scalarPart_eq :
    projAmp (scalarPart n) F = scalarAmp n (lamOf n F) (muOf F) := by
  funext t α β
  simp only [projAmp, ScalarVectorTensor.scalarPart_eq, scalarAmp, longitudinal, kron, lamOf,
    muOf, ScalarVectorTensor.delta, ScalarVectorTensor.nsq, nsq]

/-- **The scalar part of a `cos` wave is the scalar mode of L&L.** -/
theorem mode_scalarPart_eq :
    mode (projAmp (scalarPart n) F) Real.cos n = scalarMode n (lamOf n F) (muOf F) := by
  rw [projAmp_scalarPart_eq]; rfl

theorem contDiffOn_lamOf (hF : IsAmplitude B F) : ContDiffOn ℝ ∞ (lamOf n F) B.I := by
  have hs : ContDiffOn ℝ ∞ (fun t => ScalarVectorTensor.longCoeff n (F t)) B.I := by
    unfold ScalarVectorTensor.longCoeff ScalarVectorTensor.sandwich ScalarVectorTensor.contract
    exact (ContDiffOn.sum fun β _ => (ContDiffOn.sum fun γ _ => contDiffOn_const.mul
      (hF.smooth γ β)).mul contDiffOn_const).div_const _
  have htr : ContDiffOn ℝ ∞ (fun t => ScalarVectorTensor.trace (F t)) B.I :=
    ContDiffOn.sum fun γ _ => hF.smooth γ γ
  show ContDiffOn ℝ ∞ (fun t => (3 * ScalarVectorTensor.longCoeff n (F t) -
    ScalarVectorTensor.trace (F t)) / 2) B.I
  exact ((contDiffOn_const.mul hs).sub htr).div_const 2

theorem contDiffOn_muOf (hF : IsAmplitude B F) : ContDiffOn ℝ ∞ (muOf F) B.I := by
  show ContDiffOn ℝ ∞ (fun t => ∑ γ, F t γ γ) B.I
  exact ContDiffOn.sum fun γ _ => hF.smooth γ γ

/-- **The scalar sector reduces to the equations of `scalarMode_iff`**: on a dust background,
for `n ≠ 0`, the scalar part of a `cos` wave with the density contrast `δ̂ cos(n · x)` and the
longitudinal part of the velocity `V(t) (−sin(n · x))` solves the linearized equations if and
only if `λ = lamOf n F`, `μ = muOf F` and `w = −(n · V)/n²` satisfy the four equations of
L&L. -/
theorem scalar_sector_iff (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) (hn : n ≠ 0) (hF : IsAmplitude B F)
    (dc : ℝ → ℝ) (V : ℝ → Fin 3 → ℝ) :
    LinearizedEinsteinDust B κ ρ (mode (projAmp (scalarPart n) F) Real.cos n)
        (fun z => dc (z 0) * Real.cos (phase n z))
        (fun z α => longVec n (V (z 0)) α * -Real.sin (phase n z)) ↔
      ∀ t ∈ B.I,
        deriv (deriv (lamOf n F)) t + 3 * (deriv B.a t / B.a t) * deriv (lamOf n F) t +
            nsq n * (muOf F t - lamOf n F t) / (3 * B.a t ^ 2) = 0 ∧
        deriv (deriv (muOf F)) t + 3 * (deriv B.a t / B.a t) * deriv (muOf F) t +
            nsq n * (muOf F t - lamOf n F t) / (3 * B.a t ^ 2) = 0 ∧
        κ * ρ t * dc t = -(deriv (deriv (muOf F)) t + 2 * (deriv B.a t / B.a t) *
          deriv (muOf F) t) ∧
        deriv (muOf F) t - deriv (lamOf n F) t =
          -(3 * κ * ρ t * (-(ScalarVectorTensor.dot n (V t)) / nsq n)) := by
  have hv : (fun (z : E) α => longVec n (V (z 0)) α * -Real.sin (phase n z)) =
      fun z α => (-(ScalarVectorTensor.dot n (V (z 0))) / nsq n) * n α * Real.sin (phase n z) := by
    funext z α
    simp only [ScalarVectorTensor.longVec_apply, ScalarVectorTensor.nsq, nsq]
    ring
  rw [mode_scalarPart_eq, hv]
  exact scalarMode_iff hB hn (contDiffOn_lamOf (n := n) hF) (contDiffOn_muOf hF) dc
    (fun t => -(ScalarVectorTensor.dot n (V t)) / nsq n)

/-- The background coefficients satisfy `c₁ = κρa²/2` on a dust solution. -/
theorem realCoeffs_c₁ (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) {t : ℝ} (ht : t ∈ B.I) :
    (realCoeffs B κ ρ t).c₁ = (realCoeffs B κ ρ t).src := by
  obtain ⟨e1, e2⟩ := dust_background hB ht
  simp only [realCoeffs]
  rw [e1, e2]; ring

/-- **The tensor sector**: on a dust background the tensor part `T` of the amplitude solves the
equations if and only if `T̈ + 3(ȧ/a) Ṫ + (n²/a²) T = 0` (the equation of `tensorMode_iff`). -/
theorem tensor_sector_iff (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) (hF : IsAmplitude B F) (hn : nsq n ≠ 0) :
    (∀ t ∈ B.I, ModeEq B κ ρ (projAmp (tensorPart n) F) n (fun _ => 0) (fun _ _ => 0) t) ↔
      ∀ t ∈ B.I, ∀ α β, Fdd (projAmp (tensorPart n) F) t α β +
        3 * (deriv B.a t / B.a t) * Fd (projAmp (tensorPart n) F) t α β +
          nsq n / B.a t ^ 2 * projAmp (tensorPart n) F t α β = 0 := by
  have hn' : ScalarVectorTensor.nsq n ≠ 0 := hn
  refine forall₂_congr fun t ht => ?_
  have ha := (B.a_pos t ht).ne'
  rw [modeEq_iff_symbolEq, Fd_projAmp hF ht, Fdd_projAmp hF ht]
  refine (ScalarVectorTensor.symbolEq_tensor_iff (realCoeffs B κ ρ t) (F t) (Fd F t) (Fdd F t)
    hn').trans ?_
  rw [realCoeffs_c₁ hB ht, funext_iff]
  refine forall_congr' fun α => ?_
  rw [funext_iff]
  refine forall_congr' fun β => ?_
  simp only [realCoeffs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, projAmp,
    ScalarVectorTensor.nsq, nsq]
  constructor
  · intro h
    field_simp
    linear_combination 2 * h
  · intro h
    field_simp at h
    linear_combination h / 2

/-- **The vector sector**: on a dust background the vector part solves the equations if and
only if the transverse vector `u = nF − (nFn/n²) n` of the amplitude satisfies
`ü + 3(ȧ/a) u̇ = 0` and `½ u̇ + κρ V_⊥ = 0` (the equations of `vectorMode_iff`). -/
theorem vector_sector_iff (hB : (metric B.toData).IsEinstein κ 0
      (perfectFluidStress B.toData ρ fun _ => 0)) (hF : IsAmplitude B F) (hn : nsq n ≠ 0)
    (V : ℝ → Fin 3 → ℝ) :
    (∀ t ∈ B.I, ModeEq B κ ρ (projAmp (vectorPart n) F) n (fun _ => 0)
        (projVel (transVec n) V) t) ↔
      ∀ t ∈ B.I, (∀ β, shear n (Fdd F t) β + 3 * (deriv B.a t / B.a t) * shear n (Fd F t) β = 0) ∧
        ∀ α, shear n (Fd F t) α / 2 + κ * ρ t * transVec n (V t) α = 0 := by
  have hn' : ScalarVectorTensor.nsq n ≠ 0 := hn
  refine forall₂_congr fun t ht => ?_
  have ha := (B.a_pos t ht).ne'
  rw [modeEq_iff_symbolEq, Fd_projAmp hF ht, Fdd_projAmp hF ht]
  refine (ScalarVectorTensor.symbolEq_vector_iff (realCoeffs B κ ρ t) (F t) (Fd F t) (Fdd F t)
    (V t) hn').trans ?_
  have eV : ((realCoeffs B κ ρ t).c₁ - (realCoeffs B κ ρ t).src) • vectorPart n (F t) +
      (realCoeffs B κ ρ t).c₂ • vectorPart n (Fd F t) +
        (realCoeffs B κ ρ t).c₃ • vectorPart n (Fdd F t) =
      vectorPart n ((realCoeffs B κ ρ t).c₂ • Fd F t + (realCoeffs B κ ρ t).c₃ • Fdd F t) := by
    rw [realCoeffs_c₁ hB ht, sub_self, zero_smul, zero_add, map_add, map_smul, map_smul]
  rw [eV, ScalarVectorTensor.vectorPart_eq_zero_iff _ hn', ScalarVectorTensor.shear_add,
    ScalarVectorTensor.shear_smul, ScalarVectorTensor.shear_smul, and_comm]
  refine and_congr ?_ ?_
  · rw [funext_iff]
    refine forall_congr' fun β => ?_
    simp only [realCoeffs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have e1 : shear n (Fdd F t) β + 3 * (deriv B.a t / B.a t) * shear n (Fd F t) β =
        2 / B.a t ^ 2 * (3 / 2 * (B.a t * deriv B.a t) * shear n (Fd F t) β +
          B.a t ^ 2 / 2 * shear n (Fdd F t) β) := by
      field_simp; ring
    constructor
    · intro h; rw [e1, h, mul_zero]
    · intro h
      have e2 : 3 / 2 * (B.a t * deriv B.a t) * shear n (Fd F t) β +
          B.a t ^ 2 / 2 * shear n (Fdd F t) β = B.a t ^ 2 / 2 * (shear n (Fdd F t) β +
            3 * (deriv B.a t / B.a t) * shear n (Fd F t) β) := by
        field_simp; ring
      rw [e2, h, mul_zero]
  · rw [funext_iff]
    refine forall_congr' fun α => ?_
    simp only [realCoeffs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    constructor <;> intro h <;> linarith

/-! ### The equations of a frequency are those of two real plane waves -/

section Complex

open Reconstruction SmoothGeometry.Fourier

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The real wave vector `2πξ`. -/
def waveR (ξ : E3) : Fin 3 → ℝ := fun γ => 2 * Real.pi * ξ γ

/-- The real part `Re ĥ(t, ξ)` of the amplitude of one frequency. -/
def reAmp (hh : ℝ → E3 → Mat3 ℂ) (ξ : E3) : ℝ → Fin 3 → Fin 3 → ℝ :=
  fun t α β => (hh t ξ α β).re

/-- The imaginary part `Im ĥ(t, ξ)` of the amplitude of one frequency. -/
def imAmp (hh : ℝ → E3 → Mat3 ℂ) (ξ : E3) : ℝ → Fin 3 → Fin 3 → ℝ :=
  fun t α β => (hh t ξ α β).im

variable {K : Set E3} {hh : ℝ → E3 → Mat3 ℂ} {dd : ℝ → E3 → ℂ} {vv : ℝ → E3 → Fin 3 → ℂ}

theorem Fd_reAmp (hD : IsFourierData B.I K hh dd vv) {t : ℝ} (ht : t ∈ B.I) (ξ : E3) :
    (Fd (reAmp hh ξ) t = fun α β => (jet1 hh t ξ α β).re) ∧
      Fd (imAmp hh ξ) t = fun α β => (jet1 hh t ξ α β).im := by
  constructor <;> funext α β
  · exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      ((hD.metric α β).hasDerivAt B.isOpen_I ht ξ)).deriv
  · exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      ((hD.metric α β).hasDerivAt B.isOpen_I ht ξ)).deriv

theorem Fdd_reAmp (hD : IsFourierData B.I K hh dd vv) {t : ℝ} (ht : t ∈ B.I) (ξ : E3) :
    Fdd (reAmp hh ξ) t = (fun α β => (jet2 hh t ξ α β).re) ∧
      Fdd (imAmp hh ξ) t = fun α β => (jet2 hh t ξ α β).im := by
  have hev (α β : Fin 3) : (deriv fun s => reAmp hh ξ s α β) =ᶠ[𝓝 t]
      fun s => (timeDeriv (amp hh α β) s ξ).re :=
    eventually_of_mem (B.isOpen_I.mem_nhds ht) fun s hs =>
      congrFun (congrFun (Fd_reAmp hD hs ξ).1 α) β
  have hev' (α β : Fin 3) : (deriv fun s => imAmp hh ξ s α β) =ᶠ[𝓝 t]
      fun s => (timeDeriv (amp hh α β) s ξ).im :=
    eventually_of_mem (B.isOpen_I.mem_nhds ht) fun s hs =>
      congrFun (congrFun (Fd_reAmp hD hs ξ).2 α) β
  constructor <;> funext α β <;> simp only [Fdd]
  · rw [(hev α β).deriv_eq]
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      (((hD.metric α β).timeDeriv B.isOpen_I).hasDerivAt B.isOpen_I ht ξ)).deriv
  · rw [(hev' α β).deriv_eq]
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      (((hD.metric α β).timeDeriv B.isOpen_I).hasDerivAt B.isOpen_I ht ξ)).deriv

/-- **The complex equations of one frequency are the real equations of its real and imaginary
parts**: with `n = 2πξ`, `FrequencyEq` at the time `t` holds if and only if the amplitudes
`Re ĥ, Re δ̂, Im v̂` and `Im ĥ, Im δ̂, −Re v̂` satisfy the equations `ModeEq` of `mode_iff`. -/
theorem frequencyEq_iff_modeEq (hD : IsFourierData B.I K hh dd vv) {t : ℝ} (ht : t ∈ B.I)
    (ξ : E3) :
    FrequencyEq B κ ρ hh dd vv t ξ ↔
      ModeEq B κ ρ (reAmp hh ξ) (waveR ξ) (fun t => (dd t ξ).re) (fun t α => (vv t ξ α).im) t ∧
      ModeEq B κ ρ (imAmp hh ξ) (waveR ξ) (fun t => (dd t ξ).im) (fun t α => -(vv t ξ α).re)
        t := by
  rw [modeEq_iff_symbolEq, modeEq_iff_symbolEq, (Fd_reAmp hD ht ξ).1, (Fd_reAmp hD ht ξ).2,
    (Fdd_reAmp hD ht ξ).1, (Fdd_reAmp hD ht ξ).2]
  simp only [FrequencyEq, SymbolEq, funext_iff, Pi.zero_apply, Complex.ext_iff,
    Complex.zero_re, Complex.zero_im, ScalarVectorTensor.resTime, ScalarVectorTensor.resMixed,
    ScalarVectorTensor.resSpace, ScalarVectorTensor.mix_apply, ScalarVectorTensor.op_apply,
    ScalarVectorTensor.contract, ScalarVectorTensor.trace, ScalarVectorTensor.nsq,
    ScalarVectorTensor.delta, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    fourierCoeffs, realCoeffs, wave, waveR, reAmp, imAmp, Fin.sum_univ_three, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.inv_re, Complex.inv_im, pow_two,
    Complex.normSq_ofNat, Complex.re_ofNat, Complex.im_ofNat, apply_ite Complex.re,
    apply_ite Complex.im, Complex.one_re, Complex.one_im]
  constructor
  · rintro ⟨⟨h0, h0'⟩, h1, h2⟩
    refine ⟨⟨by linarith, fun α => ?_, fun α β => ?_⟩, ⟨by linarith, fun α => ?_, fun α β => ?_⟩⟩
    · linarith [(h1 α).2]
    · have h := (h2 α β).1
      split_ifs at h ⊢ <;> linarith
    · linarith [(h1 α).1]
    · have h := (h2 α β).2
      split_ifs at h ⊢ <;> linarith
  · rintro ⟨⟨h0, h1, h2⟩, ⟨h0', h1', h2'⟩⟩
    refine ⟨⟨by linarith, by linarith⟩, fun α => ⟨by linarith [h1' α], by linarith [h1 α]⟩,
      fun α β => ⟨?_, ?_⟩⟩
    · have h := h2 α β
      clear h0 h1 h2 h0' h1' h2'
      split_ifs at h ⊢ <;> linear_combination h
    · have h := h2' α β
      clear h0 h1 h2 h0' h1' h2'
      split_ifs at h ⊢ <;> linear_combination h

theorem isAmplitude_reAmp (hD : IsFourierData B.I K hh dd vv) (ξ : E3) :
    IsAmplitude B (reAmp hh ξ) ∧ IsAmplitude B (imAmp hh ξ) := by
  have hs (α β : Fin 3) : ContDiffOn ℝ ∞ (fun t => hh t ξ α β) B.I :=
    (hD.metric α β).smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      fun _ hs => ⟨hs, mem_univ _⟩
  exact ⟨⟨fun α β => Complex.reCLM.contDiff.comp_contDiffOn (hs α β),
      fun t α β => by simp only [reAmp, hD.symm t ξ α β]⟩,
    ⟨fun α β => Complex.imCLM.contDiff.comp_contDiffOn (hs α β),
      fun t α β => by simp only [imAmp, hD.symm t ξ α β]⟩⟩

/-- **Each frequency of the Fourier data satisfies its equations if and only if the two real plane
waves of its real and imaginary parts solve the linearized Einstein equations with dust**
(`mode_iff` with the profile `cos`). -/
theorem frequencyEq_iff_planeWaves (hD : IsFourierData B.I K hh dd vv) {ξ : E3} (hξ : ξ ≠ 0) :
    (∀ t ∈ B.I, FrequencyEq B κ ρ hh dd vv t ξ) ↔
      LinearizedEinsteinDust B κ ρ (mode (reAmp hh ξ) Real.cos (waveR ξ))
          (fun z => (dd (z 0) ξ).re * Real.cos (phase (waveR ξ) z))
          (fun z α => (vv (z 0) ξ α).im * -Real.sin (phase (waveR ξ) z)) ∧
        LinearizedEinsteinDust B κ ρ (mode (imAmp hh ξ) Real.cos (waveR ξ))
          (fun z => (dd (z 0) ξ).im * Real.cos (phase (waveR ξ) z))
          (fun z α => -(vv (z 0) ξ α).re * -Real.sin (phase (waveR ξ) z)) := by
  have hn : nsq (waveR ξ) ≠ 0 := by
    refine nsq_ne_zero fun h => hξ ?_
    ext γ
    have := congrFun h γ
    simp only [waveR, Pi.zero_apply, mul_eq_zero, Real.pi_ne_zero, two_ne_zero,
      false_or] at this
    simpa using this
  rw [mode_iff (isAmplitude_reAmp hD ξ).1 isProfile_cos hn ⟨0, by simp⟩ ⟨Real.pi / 2, by simp⟩
    (fun t => (dd t ξ).re) (fun t α => (vv t ξ α).im),
    mode_iff (isAmplitude_reAmp hD ξ).2 isProfile_cos hn ⟨0, by simp⟩ ⟨Real.pi / 2, by simp⟩
    (fun t => (dd t ξ).im) (fun t α => -(vv t ξ α).re), ← forall₂_and]
  exact forall₂_congr fun t ht => frequencyEq_iff_modeEq hD ht ξ

end Complex

end ProjectAinos.GeneralRelativity.CosmologicalPerturbation.ModeSplit
