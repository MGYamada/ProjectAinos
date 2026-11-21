/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.ChargeCovariance
import Mathlib.Tactic

/-!
# The boosted isotropic metric: a nonzero test of the four-vector law

The metric `η + 2Mρ (dt² + dx²)` of `AsymptoticCharge.lean` (`isotropicMetric`, with `ρ = 1/r`
for `r ≥ 2R₀`) is static, with the energy `P⁰ = 8πM` (`charge_zero_eq_mass`). This file computes
its total density `|g| (G^{ik} + t^{ik})` directly and checks the transformation law of the
charges under a boost.

* `fderiv_comp_space`: the derivatives of a static function `f(space z)`.
* `superpotentialDensity_isotropicMetric_spatial`: for spatial `l, m`,
  `λ^{iklm} = a₁ Q₁ + a₂ Q₂` with `Q₁ = −(1 + P)²`, `Q₂ = 1 − P²`, `P = 2Mρ`, and constant
  coefficients (`isoLam`).
* `totalDensity_isotropicMetric`: `|g| (G^{ik} + t^{ik}) = ½ Σ_{β,γ} ∂_β ∂_γ λ^{ik,β,γ}`, since the
  metric does not depend on the time.
* `totalDensity_isotropicMetric_zero_zero`: **`|g|(G⁰⁰ + t⁰⁰) = −|∇P|²` beyond `2R₀`**, because
  `ρ = 1/r` is harmonic there; `abs_totalDensity_isotropicMetric_le`: **the wedge estimate**,
  `|g| |G^{ik} + t^{ik}| ≤ 180 M²/r⁴` for `r ≥ 3R₀`, at every time.
* `charge_isotropicMetric_succ`: the momentum of the static metric vanishes, `P^α = 0`.
* `boost`, `boost_lorentz`, `boost_inv`: the boost `x⁰ = γ(x'⁰ + βx'¹)`, `x¹ = γ(βx'⁰ + x'¹)`.
* `charge_boost_isotropicMetric`: **the boosted isotropic metric has `P'⁰ = 8πMγ` and
  `P'¹ = −8πMγβ`**, the four-momentum of the mass `M` moving with the velocity `−β`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter TopologicalSpace
open scoped Topology ContDiff Matrix

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry SmoothGeometry.CoordinateMetric SmoothGeometry.Minkowski
  SmoothGeometry.Hyperplane

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Static functions -/

theorem space_single_zero : space (Pi.single 0 1 : MinkowskiModel 3) = 0 := by
  have h := congrArg Prod.snd Wave.timeSpaceEquiv_single_zero
  simpa only [Wave.timeSpaceEquiv_apply] using h

/-- The derivative of a static function `z ↦ f(space z)`. -/
theorem fderiv_comp_space {f : E3 → ℝ} {z : MinkowskiModel 3}
    (hf : DifferentiableAt ℝ f (space z)) (v : MinkowskiModel 3) :
    fderiv ℝ (fun w => f (space w)) z v = fderiv ℝ f (space z) (space v) := by
  have h := hf.hasFDerivAt.comp z space.hasFDerivAt
  rw [show (fun w => f (space w)) = f ∘ space from rfl, h.fderiv]
  rfl

/-! ### The superpotential density of the isotropic metric -/

variable {σ : LorentzConvention} {M R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀}

/-- The potential `P = 2Mρ` of the isotropic metric. -/
def isoPotential (M R₀ : ℝ) (x : E3) : ℝ := 2 * M * isotropicProfile R₀ x

/-- `Q₁ = −(1 + P)²`. -/
def isoQ₁ (M R₀ : ℝ) (x : E3) : ℝ := -(1 + isoPotential M R₀ x) ^ 2

/-- `Q₂ = 1 − P²`. -/
def isoQ₂ (M R₀ : ℝ) (x : E3) : ℝ := 1 - isoPotential M R₀ x ^ 2

/-- The coefficient of `Q₁` in `λ^{ik,β+1,γ+1}`. -/
def isoCoeffOne (i k : Fin 4) (β γ : Fin 3) : ℝ := if i = 0 ∧ k = 0 ∧ β = γ then 1 else 0

/-- The coefficient of `Q₂` in `λ^{ik,β+1,γ+1}`. -/
def isoCoeffTwo (i k : Fin 4) (β γ : Fin 3) : ℝ :=
  (if i = k ∧ i ≠ 0 ∧ β = γ then 1 else 0) - (if i = β.succ ∧ k = γ.succ then 1 else 0)

/-- `λ^{ik,β+1,γ+1} = a₁ Q₁ + a₂ Q₂` for the isotropic metric. -/
def isoLam (M R₀ : ℝ) (i k : Fin 4) (β γ : Fin 3) (x : E3) : ℝ :=
  isoCoeffOne i k β γ * isoQ₁ M R₀ x + isoCoeffTwo i k β γ * isoQ₂ M R₀ x

theorem isotropicCoefficient_ne_zero (σ : LorentzConvention) (hM : 0 ≤ M) (hR : 2 * M < R₀)
    (z : MinkowskiModel 3) (i : Fin 4) : isotropicCoefficient σ M R₀ z i ≠ 0 := by
  obtain ⟨hP0, hP1⟩ := isotropic_bounds hM hR (space z)
  have hs0 : σ.timeSign ≠ 0 := by
    intro h
    have := σ.timeSign_mul_self
    rw [h, mul_zero] at this
    exact zero_ne_one this
  refine Fin.cases ?_ (fun β => ?_) i
  · rw [isotropicCoefficient_zero]
    exact mul_ne_zero hs0 (by linarith)
  · rw [isotropicCoefficient_succ]
    exact mul_ne_zero (neg_ne_zero.mpr hs0) (by linarith)

/-- `|g| g^{ii} g^{ββ} = −(1 + P)²` for `i = 0` and `1 − P²` otherwise. -/
theorem iso_density_inv (σ : LorentzConvention) (hM : 0 ≤ M) (hR : 2 * M < R₀)
    (z : MinkowskiModel 3) (i : Fin 4) (β : Fin 3) :
    |∏ j, isotropicCoefficient σ M R₀ z j| * (isotropicCoefficient σ M R₀ z i)⁻¹ *
        (isotropicCoefficient σ M R₀ z β.succ)⁻¹ =
      if i = 0 then isoQ₁ M R₀ (space z) else isoQ₂ M R₀ (space z) := by
  obtain ⟨hP0, hP1⟩ := isotropic_bounds hM hR (space z)
  have hss : σ.timeSign * σ.timeSign = 1 := σ.timeSign_mul_self
  have hc0 := isotropicCoefficient_zero σ M R₀ z
  have hcs (β : Fin 3) := isotropicCoefficient_succ σ M R₀ z β
  have hprod : ∏ j, isotropicCoefficient σ M R₀ z j =
      -((1 - isoPotential M R₀ (space z)) * (1 + isoPotential M R₀ (space z)) ^ 3) := by
    rw [Fin.prod_univ_four, hc0, show (1 : Fin 4) = Fin.succ 0 from rfl,
      show (2 : Fin 4) = Fin.succ 1 from rfl, show (3 : Fin 4) = Fin.succ 2 from rfl, hcs, hcs,
      hcs]
    unfold isoPotential
    linear_combination (-(1 - 2 * M * isotropicProfile R₀ (space z)) *
      (1 + 2 * M * isotropicProfile R₀ (space z)) ^ 3 * (σ.timeSign * σ.timeSign + 1)) * hss
  have hq : 0 < 1 - isoPotential M R₀ (space z) := by unfold isoPotential; linarith
  have hq' : 0 < 1 + isoPotential M R₀ (space z) := by unfold isoPotential; linarith
  rw [hprod, abs_neg, abs_of_pos (mul_pos hq (pow_pos hq' 3)), hcs]
  have hs2 : σ.timeSign ^ 2 = 1 := by rw [sq]; exact hss
  have hP : isoPotential M R₀ (space z) = 2 * M * isotropicProfile R₀ (space z) := rfl
  refine Fin.cases ?_ (fun α => ?_) i
  · simp only [ite_true, hc0, isoQ₁]
    rw [← hP]
    field_simp
    cases σ <;> simp
  · simp only [Fin.succ_ne_zero, ite_false, hcs, isoQ₂]
    rw [← hP]
    field_simp
    cases σ <;> simp <;> ring

/-- **The superpotential density of the isotropic metric with two spatial indices**:
`λ^{ik,β+1,γ+1} = a₁ Q₁ + a₂ Q₂`. -/
theorem superpotentialDensity_isotropicMetric_spatial (z : MinkowskiModel 3) (i k : Fin 4)
    (β γ : Fin 3) :
    (isotropicMetric σ M R₀ hM hR).superpotentialDensity z i k β.succ γ.succ =
      isoLam M R₀ i k β γ (space z) := by
  have hne := isotropicCoefficient_ne_zero σ hM hR z
  have hA := iso_density_inv σ hM hR z
  set c := isotropicCoefficient σ M R₀ z with hc
  unfold superpotentialDensity
  rw [densityOf, Real.sq_sqrt (abs_nonneg _), coefficient_isotropicMetric,
    inv_diagonal_of_ne_zero hne, Matrix.det_diagonal]
  simp only [Matrix.diagonal_apply, Fin.succ_inj]
  rw [mul_sub]
  have T1 : |∏ j, c j| * ((if i = k then (c i)⁻¹ else 0) * (if β = γ then (c β.succ)⁻¹ else 0)) =
      isoCoeffOne i k β γ * isoQ₁ M R₀ (space z) +
        (if i = k ∧ i ≠ 0 ∧ β = γ then 1 else 0) * isoQ₂ M R₀ (space z) := by
    by_cases hik : i = k
    · subst hik
      by_cases hβγ : β = γ
      · subst hβγ
        simp only [↓reduceIte]
        rw [← mul_assoc, hA]
        by_cases hi : i = 0 <;> simp [isoCoeffOne, hi]
      · simp [isoCoeffOne, hβγ]
    · have h3 : ¬(i = 0 ∧ k = 0 ∧ β = γ) := fun h => hik (h.1.trans h.2.1.symm)
      simp [isoCoeffOne, hik, h3]
  have T2 : |∏ j, c j| * ((if i = β.succ then (c i)⁻¹ else 0) *
      (if k = γ.succ then (c k)⁻¹ else 0)) =
      (if i = β.succ ∧ k = γ.succ then 1 else 0) * isoQ₂ M R₀ (space z) := by
    by_cases hi : i = β.succ
    · by_cases hk : k = γ.succ
      · subst hi hk
        simp only [↓reduceIte]
        rw [← mul_assoc, hA]
        simp [Fin.succ_ne_zero]
      · simp [hk]
    · simp [hi]
  rw [T1, T2, isoLam, isoCoeffTwo]
  ring

/-! ### Derivatives of `Q₁` and `Q₂` -/

theorem hasFDerivAt_isoPotential (hR₀ : 0 < R₀) (y : E3) :
    HasFDerivAt (isoPotential M R₀) ((2 * M) • fderiv ℝ (isotropicProfile R₀) y) y :=
  (((contDiff_isotropicProfile hR₀).differentiable (by simp) y).hasFDerivAt).const_mul (2 * M)

theorem fderiv_isoQ₁ (hR₀ : 0 < R₀) (y u : E3) :
    fderiv ℝ (isoQ₁ M R₀) y u =
      -(2 * (1 + isoPotential M R₀ y) * (2 * M * fderiv ℝ (isotropicProfile R₀) y u)) := by
  have h : HasFDerivAt (fun y => -(1 + isoPotential M R₀ y) ^ 2) _ y :=
    (((hasFDerivAt_isoPotential (M := M) hR₀ y).const_add 1).pow 2).neg
  rw [show isoQ₁ M R₀ = fun y => -(1 + isoPotential M R₀ y) ^ 2 from rfl, h.fderiv]
  simp only [neg_apply, smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one]

theorem fderiv_isoQ₂ (hR₀ : 0 < R₀) (y u : E3) :
    fderiv ℝ (isoQ₂ M R₀) y u =
      -(2 * isoPotential M R₀ y * (2 * M * fderiv ℝ (isotropicProfile R₀) y u)) := by
  have h : HasFDerivAt (fun y => 1 - isoPotential M R₀ y ^ 2) _ y :=
    ((hasFDerivAt_isoPotential (M := M) hR₀ y).pow 2).const_sub 1
  rw [show isoQ₂ M R₀ = fun y => 1 - isoPotential M R₀ y ^ 2 from rfl, h.fderiv]
  simp [smul_eq_mul, nsmul_eq_mul]

theorem differentiableAt_fderiv_profile (hR₀ : 0 < R₀) (x u : E3) :
    DifferentiableAt ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y u) x :=
  (((contDiff_isotropicProfile hR₀).fderiv_right (m := 1) (by simp)).clm_apply
    contDiff_const).differentiable (by simp) x

/-- `∂_v ∂_u Q₁ = −2 (∂_v P ∂_u P + (1 + P) ∂_v ∂_u P)`. -/
theorem fderiv_fderiv_isoQ₁ (hR₀ : 0 < R₀) (x u v : E3) :
    fderiv ℝ (fun y => fderiv ℝ (isoQ₁ M R₀) y u) x v =
      -(2 * (2 * M * fderiv ℝ (isotropicProfile R₀) x v) *
          (2 * M * fderiv ℝ (isotropicProfile R₀) x u) +
        2 * (1 + isoPotential M R₀ x) *
          (2 * M * fderiv ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y u) x v)) := by
  have hf : (fun y => fderiv ℝ (isoQ₁ M R₀) y u) = fun y =>
      -(2 * (1 + isoPotential M R₀ y) * (2 * M * fderiv ℝ (isotropicProfile R₀) y u)) :=
    funext fun y => fderiv_isoQ₁ hR₀ y u
  have h : HasFDerivAt (fun y => -(2 * (1 + isoPotential M R₀ y) *
      (2 * M * fderiv ℝ (isotropicProfile R₀) y u))) _ x :=
    (((((hasFDerivAt_isoPotential (M := M) hR₀ x).const_add 1).const_mul 2).mul
      (((differentiableAt_fderiv_profile hR₀ x u).hasFDerivAt).const_mul (2 * M))).neg)
  rw [hf, h.fderiv]
  simp [smul_eq_mul]
  ring

/-- `∂_v ∂_u Q₂ = −2 (∂_v P ∂_u P + P ∂_v ∂_u P)`. -/
theorem fderiv_fderiv_isoQ₂ (hR₀ : 0 < R₀) (x u v : E3) :
    fderiv ℝ (fun y => fderiv ℝ (isoQ₂ M R₀) y u) x v =
      -(2 * (2 * M * fderiv ℝ (isotropicProfile R₀) x v) *
          (2 * M * fderiv ℝ (isotropicProfile R₀) x u) +
        2 * isoPotential M R₀ x *
          (2 * M * fderiv ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y u) x v)) := by
  have hf : (fun y => fderiv ℝ (isoQ₂ M R₀) y u) = fun y =>
      -(2 * isoPotential M R₀ y * (2 * M * fderiv ℝ (isotropicProfile R₀) y u)) :=
    funext fun y => fderiv_isoQ₂ hR₀ y u
  have h : HasFDerivAt (fun y => -(2 * isoPotential M R₀ y *
      (2 * M * fderiv ℝ (isotropicProfile R₀) y u))) _ x :=
    ((((hasFDerivAt_isoPotential (M := M) hR₀ x).const_mul 2).mul
      (((differentiableAt_fderiv_profile hR₀ x u).hasFDerivAt).const_mul (2 * M))).neg)
  rw [hf, h.fderiv]
  simp [smul_eq_mul]
  ring

theorem contDiff_isoQ₁ (hR₀ : 0 < R₀) : ContDiff ℝ ∞ (isoQ₁ M R₀) :=
  ((contDiff_const.add (contDiff_const.mul (contDiff_isotropicProfile hR₀))).pow 2).neg

theorem contDiff_isoQ₂ (hR₀ : 0 < R₀) : ContDiff ℝ ∞ (isoQ₂ M R₀) :=
  contDiff_const.sub ((contDiff_const.mul (contDiff_isotropicProfile hR₀)).pow 2)

theorem differentiableAt_fderiv_isoQ₁ (hR₀ : 0 < R₀) (x u : E3) :
    DifferentiableAt ℝ (fun y => fderiv ℝ (isoQ₁ M R₀) y u) x :=
  (((contDiff_isoQ₁ hR₀).fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable
    (by simp) x

theorem differentiableAt_fderiv_isoQ₂ (hR₀ : 0 < R₀) (x u : E3) :
    DifferentiableAt ℝ (fun y => fderiv ℝ (isoQ₂ M R₀) y u) x :=
  (((contDiff_isoQ₂ hR₀).fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable
    (by simp) x

theorem fderiv_isoLam (hR₀ : 0 < R₀) (i k : Fin 4) (β γ : Fin 3) (x u : E3) :
    fderiv ℝ (isoLam M R₀ i k β γ) x u = isoCoeffOne i k β γ * fderiv ℝ (isoQ₁ M R₀) x u +
      isoCoeffTwo i k β γ * fderiv ℝ (isoQ₂ M R₀) x u := by
  have h : HasFDerivAt (isoLam M R₀ i k β γ) _ x :=
    ((((contDiff_isoQ₁ hR₀).differentiable (by simp) x).hasFDerivAt).const_mul
      (isoCoeffOne i k β γ)).add
      ((((contDiff_isoQ₂ hR₀).differentiable (by simp) x).hasFDerivAt).const_mul
        (isoCoeffTwo i k β γ))
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-! ### The total density of the isotropic metric -/

theorem coefficient_isotropicMetric_static (z : MinkowskiModel 3) :
    (isotropicMetric σ M R₀ hM hR).coefficient z =
      (isotropicMetric σ M R₀ hM hR).coefficient (vector 0 (space z)) := by
  rw [coefficient_isotropicMetric, coefficient_isotropicMetric]
  congr 1

/-- The superpotential density as a function of space, `x ↦ λ(0, x)`. -/
def isoLamS (σ : LorentzConvention) (M R₀ : ℝ) (hM : 0 ≤ M) (hR : 2 * M < R₀)
    (i k l m : Fin 4) (x : E3) : ℝ :=
  (isotropicMetric σ M R₀ hM hR).superpotentialDensity (vector 0 x) i k l m

theorem superpotentialDensity_isotropicMetric_static (z : MinkowskiModel 3) (i k l m : Fin 4) :
    (isotropicMetric σ M R₀ hM hR).superpotentialDensity z i k l m =
      isoLamS σ M R₀ hM hR i k l m (space z) := by
  unfold isoLamS superpotentialDensity densityOf
  rw [coefficient_isotropicMetric_static z]

theorem contDiff_isoLamS (i k l m : Fin 4) : ContDiff ℝ ∞ (isoLamS σ M R₀ hM hR i k l m) := by
  have h := ((isotropicMetric σ M R₀ hM hR).contDiffOn_superpotentialDensity i k l m)
  rw [TopologicalSpace.Opens.coe_top, contDiffOn_univ] at h
  exact h.comp (contDiff_vector_space 0)

theorem isoLamS_spatial (i k : Fin 4) (β γ : Fin 3) :
    isoLamS σ M R₀ hM hR i k β.succ γ.succ = isoLam M R₀ i k β γ := by
  funext x
  rw [isoLamS, superpotentialDensity_isotropicMetric_spatial, space_vector]

/-- The superpotential as a function of space, `h^{ikl} = Σ_γ ∂_γ λ^{ikl,γ+1}`. -/
def isoHS (σ : LorentzConvention) (M R₀ : ℝ) (hM : 0 ≤ M) (hR : 2 * M < R₀) (i k l : Fin 4)
    (x : E3) : ℝ :=
  ∑ γ : Fin 3, fderiv ℝ (isoLamS σ M R₀ hM hR i k l γ.succ) x (EuclideanSpace.single γ 1)

/-- **The superpotential of the static metric**: `h^{ikl} = Σ_γ ∂_γ λ^{ikl,γ+1}`, since the
derivative along the time axis vanishes. -/
theorem superpotential_isotropicMetric_static (z : MinkowskiModel 3) (i k l : Fin 4) :
    (isotropicMetric σ M R₀ hM hR).superpotential z i k l = isoHS σ M R₀ hM hR i k l (space z) := by
  unfold superpotential isoHS
  rw [Fin.sum_univ_succ]
  have hf (m : Fin 4) : (fun w => (isotropicMetric σ M R₀ hM hR).superpotentialDensity w i k l m) =
      fun w => isoLamS σ M R₀ hM hR i k l m (space w) :=
    funext fun w => superpotentialDensity_isotropicMetric_static w i k l m
  have hd (m : Fin 4) : DifferentiableAt ℝ (isoLamS σ M R₀ hM hR i k l m) (space z) :=
    (contDiff_isoLamS i k l m).differentiable (by simp) _
  simp only [hf, fderiv_comp_space (hd _), space_single_zero, map_zero, zero_add,
    space_single_succ]

theorem contDiff_isoHS (i k l : Fin 4) : ContDiff ℝ ∞ (isoHS σ M R₀ hM hR i k l) :=
  ContDiff.sum fun γ _ => ((contDiff_isoLamS i k l γ.succ).fderiv_right (m := ∞) le_rfl).clm_apply
    contDiff_const

/-- **The total density of the static metric**: `|g| (G^{ik} + t^{ik}) = ½ Σ_β ∂_β h^{ik,β+1}`. -/
theorem totalDensity_isotropicMetric (z : MinkowskiModel 3) (i k : Fin 4) :
    (isotropicMetric σ M R₀ hM hR).totalDensity z i k = (1 / 2) * ∑ β : Fin 3,
      fderiv ℝ (isoHS σ M R₀ hM hR i k β.succ) (space z) (EuclideanSpace.single β 1) := by
  have h := (isotropicMetric σ M R₀ hM hR).sum_fderiv_superpotential
    (TopologicalSpace.Opens.mem_top z) i k
  have hf (l : Fin 4) : (fun w => (isotropicMetric σ M R₀ hM hR).superpotential w i k l) =
      fun w => isoHS σ M R₀ hM hR i k l (space w) :=
    funext fun w => superpotential_isotropicMetric_static w i k l
  have hd (l : Fin 4) : DifferentiableAt ℝ (isoHS σ M R₀ hM hR i k l) (space z) :=
    (contDiff_isoHS i k l).differentiable (by simp) _
  simp only [hf, fderiv_comp_space (hd _), Fin.sum_univ_succ (n := 3), space_single_zero,
    map_zero, zero_add, space_single_succ] at h
  linarith

/-- **The total density in the second derivatives of `Q₁` and `Q₂`**:
`|g| (G^{ik} + t^{ik}) = ½ Σ_{β,γ} (a₁ ∂_β ∂_γ Q₁ + a₂ ∂_β ∂_γ Q₂)`. -/
theorem totalDensity_isotropicMetric_eq (z : MinkowskiModel 3) (i k : Fin 4) :
    (isotropicMetric σ M R₀ hM hR).totalDensity z i k = (1 / 2) * ∑ β : Fin 3, ∑ γ : Fin 3,
      (isoCoeffOne i k β γ * fderiv ℝ (fun y => fderiv ℝ (isoQ₁ M R₀) y
          (EuclideanSpace.single γ 1)) (space z) (EuclideanSpace.single β 1) +
        isoCoeffTwo i k β γ * fderiv ℝ (fun y => fderiv ℝ (isoQ₂ M R₀) y
          (EuclideanSpace.single γ 1)) (space z) (EuclideanSpace.single β 1)) := by
  have hR₀ : 0 < R₀ := by linarith
  rw [totalDensity_isotropicMetric]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  have hf : isoHS σ M R₀ hM hR i k β.succ = fun x => ∑ γ : Fin 3,
      (isoCoeffOne i k β γ * fderiv ℝ (isoQ₁ M R₀) x (EuclideanSpace.single γ 1) +
        isoCoeffTwo i k β γ * fderiv ℝ (isoQ₂ M R₀) x (EuclideanSpace.single γ 1)) := by
    funext x
    unfold isoHS
    simp only [isoLamS_spatial, fderiv_isoLam hR₀]
  have hd (γ : Fin 3) : DifferentiableAt ℝ (fun y =>
      isoCoeffOne i k β γ * fderiv ℝ (isoQ₁ M R₀) y (EuclideanSpace.single γ 1) +
        isoCoeffTwo i k β γ * fderiv ℝ (isoQ₂ M R₀) y (EuclideanSpace.single γ 1)) (space z) :=
    ((differentiableAt_fderiv_isoQ₁ hR₀ _ _).const_mul _).add
      ((differentiableAt_fderiv_isoQ₂ hR₀ _ _).const_mul _)
  rw [hf, fderiv_fun_sum fun γ _ => hd γ, sum_apply]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [fderiv_fun_add ((differentiableAt_fderiv_isoQ₁ hR₀ _ _).const_mul _)
    ((differentiableAt_fderiv_isoQ₂ hR₀ _ _).const_mul _), add_apply,
    fderiv_const_mul (differentiableAt_fderiv_isoQ₁ hR₀ _ _),
    fderiv_const_mul (differentiableAt_fderiv_isoQ₂ hR₀ _ _), smul_apply, smul_apply,
    smul_eq_mul, smul_eq_mul]

/-! ### The total density beyond `2R₀` -/

theorem isoCoeffOne_zero_zero (β γ : Fin 3) : isoCoeffOne 0 0 β γ = if β = γ then 1 else 0 := by
  simp [isoCoeffOne]

theorem isoCoeffTwo_zero_zero (β γ : Fin 3) : isoCoeffTwo 0 0 β γ = 0 := by
  simp [isoCoeffTwo, (Fin.succ_ne_zero β).symm]

theorem isoCoeffOne_eq_zero {i k : Fin 4} (h : ¬(i = 0 ∧ k = 0)) (β γ : Fin 3) :
    isoCoeffOne i k β γ = 0 := by
  have h' : ¬(i = 0 ∧ k = 0 ∧ β = γ) := fun h'' => h ⟨h''.1, h''.2.1⟩
  simp [isoCoeffOne, h']

theorem abs_isoCoeffTwo_le (i k : Fin 4) (β γ : Fin 3) : |isoCoeffTwo i k β γ| ≤ 1 := by
  unfold isoCoeffTwo
  split_ifs <;> norm_num

/-- **The energy density of the isotropic metric beyond `2R₀`**: `|g| (G⁰⁰ + t⁰⁰) = −|∇P|² =
−4M²/r⁴`, since `ρ = 1/r` is harmonic there. -/
theorem totalDensity_isotropicMetric_zero_zero {z : MinkowskiModel 3}
    (hz : 2 * R₀ < ‖space z‖) :
    (isotropicMetric σ M R₀ hM hR).totalDensity z 0 0 = -(4 * M ^ 2 / ‖space z‖ ^ 4) := by
  have hR₀ : 0 < R₀ := by linarith
  have hr : 0 < ‖space z‖ := by linarith
  rw [totalDensity_isotropicMetric_eq]
  simp only [isoCoeffOne_zero_zero, isoCoeffTwo_zero_zero, zero_mul, add_zero, ite_mul, one_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [fderiv_fderiv_isoQ₁ hR₀, fderiv_isotropicProfile hR₀ hz,
    fderiv_fderiv_isotropicProfile hR₀ hz, isoPotential, isotropicProfile_eq hR₀ hz.le,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, mul_one, EuclideanSpace.single,
    PiLp.single_eq_same]
  have hn := EuclideanSpace.real_norm_sq_eq (space z)
  rw [Fin.sum_univ_three] at hn ⊢
  field_simp
  linear_combination (6 * M * ‖space z‖ + 16 * M ^ 2) * hn

theorem abs_inner_single_le (x : E3) (γ : Fin 3) :
    |inner ℝ x (EuclideanSpace.single γ (1 : ℝ))| ≤ ‖x‖ := by
  rw [EuclideanSpace.inner_single_right, conj_trivial, one_mul, ← Real.norm_eq_abs]
  exact PiLp.norm_apply_le x γ

theorem abs_inner_single_single_le (β γ : Fin 3) :
    |inner ℝ (EuclideanSpace.single β (1 : ℝ)) (EuclideanSpace.single γ (1 : ℝ))| ≤ 1 := by
  rw [EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  by_cases h : γ = β
  · subst h
    simp
  · simp [h]

/-- `|∂_γ ρ| ≤ 1/r²` beyond `2R₀`. -/
theorem abs_fderiv_profile_le (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ < ‖x‖) (γ : Fin 3) :
    |fderiv ℝ (isotropicProfile R₀) x (EuclideanSpace.single γ 1)| ≤ 1 / ‖x‖ ^ 2 := by
  have hr : 0 < ‖x‖ := by linarith
  rw [fderiv_isotropicProfile hR₀ hx, abs_neg, abs_div, abs_of_pos (by positivity : 0 < ‖x‖ ^ 3),
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc |inner ℝ x (EuclideanSpace.single γ 1)| * ‖x‖ ^ 2 ≤ ‖x‖ * ‖x‖ ^ 2 := by
        gcongr
        exact abs_inner_single_le x γ
    _ = 1 * ‖x‖ ^ 3 := by ring

/-- `|∂_β ∂_γ ρ| ≤ 4/r³` beyond `2R₀`. -/
theorem abs_fderiv_fderiv_profile_le (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ < ‖x‖) (β γ : Fin 3) :
    |fderiv ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y (EuclideanSpace.single γ 1)) x
      (EuclideanSpace.single β 1)| ≤ 4 / ‖x‖ ^ 3 := by
  have hr : 0 < ‖x‖ := by linarith
  rw [fderiv_fderiv_isotropicProfile hR₀ hx]
  have h1 := abs_inner_single_single_le β γ
  have h2 := abs_inner_single_le x γ
  have h3 := abs_inner_single_le x β
  have hB : |inner ℝ x (EuclideanSpace.single γ (1 : ℝ)) * inner ℝ x (EuclideanSpace.single β 1)|
      ≤ ‖x‖ ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul h2 h3 (abs_nonneg _) (norm_nonneg _)
  calc _ ≤ |-(inner ℝ (EuclideanSpace.single β (1 : ℝ)) (EuclideanSpace.single γ 1) / ‖x‖ ^ 3)| +
        |3 * inner ℝ x (EuclideanSpace.single γ (1 : ℝ)) * inner ℝ x (EuclideanSpace.single β 1) /
          ‖x‖ ^ 5| := abs_add_le _ _
    _ = |inner ℝ (EuclideanSpace.single β (1 : ℝ)) (EuclideanSpace.single γ 1)| / ‖x‖ ^ 3 +
        3 * |inner ℝ x (EuclideanSpace.single γ (1 : ℝ)) * inner ℝ x (EuclideanSpace.single β 1)| /
          ‖x‖ ^ 5 := by
        rw [abs_neg, abs_div, abs_div, mul_assoc, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ ^ 3),
          abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ ^ 5),
          abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    _ ≤ 1 / ‖x‖ ^ 3 + 3 * ‖x‖ ^ 2 / ‖x‖ ^ 5 := by gcongr
    _ = 4 / ‖x‖ ^ 3 := by field_simp; ring

/-- `|∂_β ∂_γ Q₂| ≤ 40 M²/r⁴` beyond `2R₀`. -/
theorem abs_fderiv_fderiv_isoQ₂_le (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ < ‖x‖)
    (β γ : Fin 3) :
    |fderiv ℝ (fun y => fderiv ℝ (isoQ₂ M R₀) y (EuclideanSpace.single γ 1)) x
      (EuclideanSpace.single β 1)| ≤ 40 * M ^ 2 / ‖x‖ ^ 4 := by
  have hr : 0 < ‖x‖ := by linarith
  rw [fderiv_fderiv_isoQ₂ hR₀, isoPotential, isotropicProfile_eq hR₀ hx.le]
  have h1 := abs_fderiv_profile_le hR₀ hx β
  have h2 := abs_fderiv_profile_le hR₀ hx γ
  have h3 := abs_fderiv_fderiv_profile_le hR₀ hx β γ
  set a := fderiv ℝ (isotropicProfile R₀) x (EuclideanSpace.single β 1)
  set b := fderiv ℝ (isotropicProfile R₀) x (EuclideanSpace.single γ 1)
  set c := fderiv ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y (EuclideanSpace.single γ 1)) x
    (EuclideanSpace.single β 1)
  have hab : |a * b| ≤ 1 / ‖x‖ ^ 2 * (1 / ‖x‖ ^ 2) :=
    abs_mul_le_mul_of_le h1 h2
  have hc : |‖x‖⁻¹ * c| ≤ ‖x‖⁻¹ * (4 / ‖x‖ ^ 3) := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hr)]
    exact mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hr).le
  have heq : -(2 * (2 * M * a) * (2 * M * b) + 2 * (2 * M * ‖x‖⁻¹) * (2 * M * c)) =
      -(8 * M ^ 2 * (a * b) + 8 * M ^ 2 * (‖x‖⁻¹ * c)) := by ring
  rw [heq, abs_neg]
  calc _ ≤ |8 * M ^ 2 * (a * b)| + |8 * M ^ 2 * (‖x‖⁻¹ * c)| := abs_add_le _ _
    _ = 8 * M ^ 2 * |a * b| + 8 * M ^ 2 * |‖x‖⁻¹ * c| := by
        rw [abs_mul (8 * M ^ 2) (a * b), abs_mul (8 * M ^ 2) (‖x‖⁻¹ * c),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 * M ^ 2)]
    _ ≤ 8 * M ^ 2 * (1 / ‖x‖ ^ 2 * (1 / ‖x‖ ^ 2)) + 8 * M ^ 2 * (‖x‖⁻¹ * (4 / ‖x‖ ^ 3)) := by
        gcongr
    _ = 40 * M ^ 2 / ‖x‖ ^ 4 := by field_simp; ring

/-- **The wedge estimate for the isotropic metric**: beyond `2R₀`, at every time,
`|g| |G^{ik} + t^{ik}| ≤ 180 M²/r⁴`. -/
theorem abs_totalDensity_isotropicMetric_le {z : MinkowskiModel 3} (hz : 2 * R₀ < ‖space z‖)
    (i k : Fin 4) :
    |(isotropicMetric σ M R₀ hM hR).totalDensity z i k| ≤ 180 * M ^ 2 / ‖space z‖ ^ 4 := by
  have hR₀ : 0 < R₀ := by linarith
  have hr : 0 < ‖space z‖ := by linarith
  by_cases h : i = 0 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := h
    rw [totalDensity_isotropicMetric_zero_zero hz, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * M ^ 2 / ‖space z‖ ^ 4)]
    gcongr
    norm_num
  · rw [totalDensity_isotropicMetric_eq]
    simp only [isoCoeffOne_eq_zero h, zero_mul, zero_add]
    have hterm (β γ : Fin 3) : |isoCoeffTwo i k β γ * fderiv ℝ (fun y => fderiv ℝ (isoQ₂ M R₀) y
        (EuclideanSpace.single γ 1)) (space z) (EuclideanSpace.single β 1)| ≤
        40 * M ^ 2 / ‖space z‖ ^ 4 := by
      calc _ ≤ 1 * (40 * M ^ 2 / ‖space z‖ ^ 4) := abs_mul_le_mul_of_le (abs_isoCoeffTwo_le i k β γ)
            (abs_fderiv_fderiv_isoQ₂_le hR₀ hz β γ)
        _ = _ := one_mul _
    have hs := abs_sum_fin_le fun β => abs_sum_fin_le fun γ => hterm β γ
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc _ ≤ 1 / 2 * (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) * (40 * M ^ 2 / ‖space z‖ ^ 4))) :=
          mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = 180 * M ^ 2 / ‖space z‖ ^ 4 := by push_cast; ring

/-! ### The charges of the isotropic metric -/

theorem isoLam_succ_zero (α β γ : Fin 3) : isoLam M R₀ α.succ 0 β γ = fun _ => 0 := by
  funext x
  simp [isoLam, isoCoeffOne, isoCoeffTwo, Fin.succ_ne_zero, (Fin.succ_ne_zero γ).symm]

/-- **The static metric has no momentum**: `P^α = 0`, since `h^{α0β} = 0`. -/
theorem charge_isotropicMetric_succ (t : ℝ) (α : Fin 3) :
    charge (isotropicMetric σ M R₀ hM hR) t α.succ = 0 := by
  have hzero (R : ℝ) : (isotropicMetric σ M R₀ hM hR).surfaceCharge t R α.succ = 0 := by
    have hf (β : Fin 3) : (isotropicMetric σ M R₀ hM hR).chargeField t α.succ β = fun _ => 0 := by
      funext x
      rw [chargeField, superpotential_isotropicMetric_static, isoHS]
      simp only [isoLamS_spatial, isoLam_succ_zero, fderiv_const_apply, zero_apply,
        Finset.sum_const_zero]
    simp [surfaceCharge, Sphere.flux, hf]
  have h : Tendsto (fun R => (isotropicMetric σ M R₀ hM hR).surfaceCharge t R α.succ) atTop
      (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact h.limUnder_eq

/-! ### The boost -/

/-- The Lorentz factor `γ = 1/√(1 − β²)`. -/
def boostFactor (β : ℝ) : ℝ := (√(1 - β ^ 2))⁻¹

theorem boostFactor_pos {β : ℝ} (hβ : |β| < 1) : 0 < boostFactor β := by
  have h : 0 < 1 - β ^ 2 := by
    have : β ^ 2 < 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg β]
    linarith
  exact inv_pos.mpr (Real.sqrt_pos.mpr h)

theorem boostFactor_sq {β : ℝ} (hβ : |β| < 1) : boostFactor β ^ 2 * (1 - β ^ 2) = 1 := by
  have h : 0 < 1 - β ^ 2 := by
    have : β ^ 2 < 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg β]
    linarith
  rw [boostFactor, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

/-- **The boost** with the velocity `β` along the axis `1`: `x⁰ = γ(x'⁰ + βx'¹)`,
`x¹ = γ(βx'⁰ + x'¹)`. -/
def boost (β : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![boostFactor β, boostFactor β * β, 0, 0; boostFactor β * β, boostFactor β, 0, 0;
    0, 0, 1, 0; 0, 0, 0, 1]

/-- The boost is a Lorentz matrix, `Lᵀ η L = η`. -/
theorem boost_lorentz (σ : LorentzConvention) {β : ℝ} (hβ : |β| < 1) :
    (boost β)ᵀ * minkowskiCoefficient σ * boost β = minkowskiCoefficient σ := by
  have h := boostFactor_sq hβ
  ext i j
  cases σ <;> fin_cases i <;> fin_cases j <;>
    simp [boost, Matrix.mul_apply, Fin.sum_univ_four, lorentzSign, Matrix.diagonal_apply] <;>
    linarith [h]

theorem boost_det_ne_zero (σ : LorentzConvention) {β : ℝ} (hβ : |β| < 1) :
    (boost β).det ≠ 0 :=
  lorentz_det_ne_zero (boost_lorentz σ hβ)

/-- The isotropic metric is Galilean at large distances on every wedge, an instance of
`IsGalileanOnWedge` with a nonzero mass. -/
theorem isGalileanOnWedge_isotropicMetric (c₀ c₁ : ℝ) (v : E3) :
    IsGalileanOnWedge (isotropicMetric σ M R₀ hM hR) c₀ c₁ v (3 * R₀) (8 * M) :=
  isAsymptoticallyGalilean_isotropicMetric.isGalileanOnWedge c₀ c₁ v

/-- The first column of the inverse boost: `(γ, −γβ, 0, 0)`. -/
theorem boost_inv_col (σ : LorentzConvention) {β : ℝ} (hβ : |β| < 1) :
    (boost β)⁻¹ 0 0 = boostFactor β ∧ (boost β)⁻¹ 1 0 = -(boostFactor β * β) ∧
      (boost β)⁻¹ 2 0 = 0 ∧ (boost β)⁻¹ 3 0 = 0 := by
  rw [lorentz_inv (boost_lorentz σ hβ)]
  cases σ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [boost, Matrix.mul_apply, lorentzSign, Matrix.diagonal_apply]

/-- **The boosted isotropic metric** (the nonzero test of the four-vector law): in the
co-ordinates `x = L x'` of the boost with the velocity `β`, `|β| < 1`, the isotropic metric of
mass `M` has the charges `P'⁰ = 8πMγ`, `P'¹ = −8πMγβ`, `P'² = P'³ = 0` on every slice: the
four-momentum `κ M (γ, −γβ, 0, 0)` of the mass moving with the velocity `−β`. The wedge estimate
is `abs_totalDensity_isotropicMetric_le`. -/
theorem charge_boost_isotropicMetric {β : ℝ} (hβ : |β| < 1) (hL : (boost β).det ≠ 0) (t : ℝ) :
    charge ((isotropicMetric σ M R₀ hM hR).linearPullback (boost β) hL) t 0 =
        8 * π * M * boostFactor β ∧
      charge ((isotropicMetric σ M R₀ hM hR).linearPullback (boost β) hL) t 1 =
        -(8 * π * M * boostFactor β * β) ∧
      charge ((isotropicMetric σ M R₀ hM hR).linearPullback (boost β) hL) t 2 = 0 ∧
      charge ((isotropicMetric σ M R₀ hM hR).linearPullback (boost β) hL) t 3 = 0 := by
  have hR₀ : 0 < R₀ := by linarith
  have hlaw (i : Fin 4) : charge ((isotropicMetric σ M R₀ hM hR).linearPullback (boost β) hL) t i =
      (boost β)⁻¹ i 0 * (8 * π * M) := by
    rw [charge_lorentz (isotropicMetric σ M R₀ hM hR) (boost_lorentz σ hβ) hL
      (by simpa [boost] using boostFactor_pos hβ) t 0 (fun _ _ _ => trivial)
      (by positivity : (0 : ℝ) ≤ 180 * M ^ 2) (R₀ := 3 * R₀)
      (fun s _ y hy a k => by
        have hsp : space (wedgePoint 0 (tiltTime (boost β) t) (tiltSlope (boost β)) s y) = y := by
          rw [wedgePoint, space_vector]
        have h := abs_totalDensity_isotropicMetric_le (σ := σ) (hM := hM) (hR := hR)
          (z := wedgePoint 0 (tiltTime (boost β) t) (tiltSlope (boost β)) s y)
          (by rw [hsp]; linarith) a k
        rw [hsp] at h
        exact h) i,
      Fin.sum_univ_succ, charge_zero_eq_mass]
    simp [charge_isotropicMetric_succ]
  obtain ⟨h0, h1, h2, h3⟩ := boost_inv_col σ hβ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlaw, h0]; ring
  · rw [hlaw, h1]; ring
  · rw [hlaw, h2]; ring
  · rw [hlaw, h3]; ring

end ProjectAinos.GeneralRelativity
