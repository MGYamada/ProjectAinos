/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.RadiationReaction
import Mathlib.Tactic

/-!
# The dependence of the electromagnetic mass on the size of the charge

Landau–Lifshitz, *The Classical Theory of Fields*, §75. The profile of radius `a > 0` of a charge
profile `η` is `ηₐ(x) = a⁻³ η(x/a)` (`scaledProfile`), of the same total charge.

* **Scaling**: the kernels of Newton and of Darwin are homogeneous of degree `−1`, so a change of
  variables in the two integrals gives `selfMass_scaledProfile` (`δm(ηₐ) = a⁻¹ δm(η)`) and
  `selfEnergy_scaledProfile` (`U(ηₐ) = a⁻¹ U(η)`), exactly and at fixed charge.
* **Isotropy**: for a profile invariant under the linear isometries of space, the reflections of
  the coordinates make the mass tensor diagonal and their permutations make the diagonal constant,
  so `trace_selfMass` gives `selfMass_isotropic`: `δmᵢₖ = (4/3) U δᵢₖ`, and the isotropic mass
  counterterm `selfMass_scaledProfile_isotropic`: `δmᵢₖ(ηₐ) = (4/3) U(η)/a · δᵢₖ`. The self-energy
  of a nonnegative nonzero charge is positive (`selfEnergy_pos`), so the counterterm diverges as
  `a → 0⁺` (`tendsto_selfMass_scaledProfile_radialBump`).
* **Instances**: the library's normalized bumps form the scaling family,
  `pointBump_eq_scaledProfile` (`pointBump a = (pointBump 1)ₐ`), and `radialBump`, a smooth
  normalized bump that is a function of `‖x‖` (the base of Mathlib's bump functions is chosen
  by choice and is only known to be even, so `pointBump` is not known to be radial). The
  oscillating path of
  `selfForce_expansion_oscillating` with the bump of radius `a`:
  `selfForce_expansion_oscillating_pointBump` (the coefficient of `κ²` is `a⁻¹` times the mass
  tensor of the unit bump) and `selfForce_expansion_oscillating_radial` (the coefficient of `κ²` is
  `−(4/3) U(1)/a · R̈`, that of `κ³` the damping force, independent of `a`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.RadiationReaction

open SmoothGeometry SmoothGeometry.Wave SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The profile of radius `a` -/

/-- The profile of radius `a`: `ηₐ(x) = a⁻³ η(x/a)`. -/
def scaledProfile (a : ℝ) (η : E3 → ℝ) (x : E3) : ℝ := (a ^ 3)⁻¹ * η (a⁻¹ • x)

/-- The profile of radius `a` has the total charge of `η`. -/
theorem integral_scaledProfile {a : ℝ} (ha : 0 < a) (η : E3 → ℝ) :
    ∫ x, scaledProfile a η x = ∫ x, η x := by
  simp only [scaledProfile]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume η ha.le,
    finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity),
    one_mul]

/-- **The change of variables in the double integral**: for a kernel homogeneous of degree `−1`,
`∫∫ ηₐ(x) K(y) ηₐ(x − y) = a⁻¹ ∫∫ η(x) K(y) η(x − y)`. -/
theorem integral_scaledProfile_mul_kernel {a : ℝ} (ha : 0 < a) (η : E3 → ℝ) {K : E3 → ℝ}
    (hK : ∀ y, K (a • y) = a⁻¹ * K y) :
    ∫ x, scaledProfile a η x * ∫ y, K y * scaledProfile a η (x - y) =
      a⁻¹ * ∫ x, η x * ∫ y, K y * η (x - y) := by
  have ha3 : a ^ 3 ≠ 0 := by positivity
  have hin : ∀ x, ∫ y, K y * scaledProfile a η (x - y) =
      a⁻¹ * ∫ y, K y * η (a⁻¹ • x - y) := by
    intro x
    have h1 : (fun y => K y * scaledProfile a η (x - y)) =
        fun y => (fun z => K (a • z) * ((a ^ 3)⁻¹ * η (a⁻¹ • x - z))) (a⁻¹ • y) := by
      funext y
      simp only [scaledProfile, smul_smul, mul_inv_cancel₀ ha.ne', one_smul, smul_sub]
    rw [h1, Measure.integral_comp_inv_smul_of_nonneg volume
      (fun z => K (a • z) * ((a ^ 3)⁻¹ * η (a⁻¹ • x - z))) ha.le, finrank_euclideanSpace_fin,
      smul_eq_mul]
    have h2 : (fun z => K (a • z) * ((a ^ 3)⁻¹ * η (a⁻¹ • x - z))) =
        fun z => (a⁻¹ * (a ^ 3)⁻¹) * (K z * η (a⁻¹ • x - z)) := by
      funext z
      rw [hK]
      ring
    rw [h2, integral_const_mul, ← mul_assoc, ← mul_assoc]
    congr 1
    field_simp
  simp only [hin]
  have h3 : (fun x => scaledProfile a η x * (a⁻¹ * ∫ y, K y * η (a⁻¹ • x - y))) =
      fun x => ((a ^ 3)⁻¹ * a⁻¹) * (fun z => η z * ∫ y, K y * η (z - y)) (a⁻¹ • x) := by
    funext x
    simp only [scaledProfile]
    ring
  rw [h3, integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun z => η z * ∫ y, K y * η (z - y)) ha.le, finrank_euclideanSpace_fin, smul_eq_mul,
    ← mul_assoc]
  congr 1
  field_simp

/-- The Newton kernel is homogeneous of degree `−1`. -/
theorem newtonKernel_smul {a : ℝ} (ha : 0 < a) (y : E3) :
    Potential.newtonKernel (a • y) = a⁻¹ * Potential.newtonKernel y := by
  simp only [Potential.newtonKernel, norm_smul, Real.norm_of_nonneg ha.le]
  rw [show 4 * π * (a * ‖y‖) = a * (4 * π * ‖y‖) by ring, mul_inv]

/-- The kernel of Darwin is homogeneous of degree `−1`. -/
theorem darwinKernel_smul {a : ℝ} (ha : 0 < a) (i k : Fin 3) (y : E3) :
    darwinKernel i k (a • y) = a⁻¹ * darwinKernel i k y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [darwinKernel]
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  simp only [darwinKernel, norm_smul, Real.norm_of_nonneg ha.le, PiLp.smul_apply, smul_eq_mul]
  field_simp

/-- **The electromagnetic mass scales as the inverse radius**: `δm(ηₐ) = a⁻¹ δm(η)`, for every
profile, at fixed charge. -/
theorem selfMass_scaledProfile_apply (e : ℝ) {a : ℝ} (ha : 0 < a) (η : E3 → ℝ) (i k : Fin 3) :
    selfMass e (scaledProfile a η) i k = a⁻¹ * selfMass e η i k := by
  simp only [selfMass]
  rw [integral_scaledProfile_mul_kernel ha η (darwinKernel_smul ha i k)]
  ring

/-- `selfMass e ηₐ = a⁻¹ • selfMass e η` as a tensor. -/
theorem selfMass_scaledProfile (e : ℝ) {a : ℝ} (ha : 0 < a) (η : E3 → ℝ) :
    selfMass e (scaledProfile a η) = a⁻¹ • selfMass e η := by
  funext i k
  simp [selfMass_scaledProfile_apply e ha]

/-- **The self-energy scales as the inverse radius**: `U(ηₐ) = a⁻¹ U(η)`. -/
theorem selfEnergy_scaledProfile (e : ℝ) {a : ℝ} (ha : 0 < a) (η : E3 → ℝ) :
    selfEnergy e (scaledProfile a η) = a⁻¹ * selfEnergy e η := by
  simp only [selfEnergy]
  rw [integral_scaledProfile_mul_kernel ha η (newtonKernel_smul ha)]
  ring

/-! ### Isotropy -/

/-- The exchange of the coordinates `i` and `k`, a linear isometry. -/
def coordSwap (i k : Fin 3) : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i k)

theorem coordSwap_apply (i k l : Fin 3) (y : E3) : coordSwap i k y l = y (Equiv.swap i k l) := by
  simp [coordSwap, Equiv.piCongrLeft']

/-- The reflection `yⱼ ↦ −yⱼ` of the coordinate `j`, a linear isometry. -/
def coordReflection (j : Fin 3) : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrRight 2 fun i =>
    if i = j then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

theorem coordReflection_apply (j l : Fin 3) (y : E3) :
    coordReflection j y l = if l = j then -y l else y l := by
  simp only [coordReflection, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
  split_ifs <;> simp

/-- **A rotation of the variables**: for a profile invariant under a linear isometry `f`,
`∫∫ η(x) K(y) η(x − y) = ∫∫ η(x) K(f y) η(x − y)`. -/
theorem integral_mul_kernel_comp_isometry (f : E3 ≃ₗᵢ[ℝ] E3) {η : E3 → ℝ}
    (hf : ∀ x, η (f x) = η x) (K : E3 → ℝ) :
    ∫ x, η x * ∫ y, K y * η (x - y) = ∫ x, η x * ∫ y, K (f y) * η (x - y) := by
  have hmp := f.measurePreserving
  rw [← hmp.integral_comp' (f := f.toMeasurableEquiv)]
  congr 1
  funext x
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv]
  rw [hf x, ← hmp.integral_comp' (f := f.toMeasurableEquiv)]
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv, ← map_sub, hf]

/-- The reflection of the coordinate `i` reverses the off-diagonal kernel of Darwin. -/
theorem darwinKernel_coordReflection {i k : Fin 3} (hik : i ≠ k) (y : E3) :
    darwinKernel i k (coordReflection i y) = -darwinKernel i k y := by
  simp only [darwinKernel, LinearIsometryEquiv.norm_map, coordReflection_apply, hik, Ne.symm hik,
    ite_true, ite_false]
  ring

/-- The exchange of the coordinates `i` and `k` exchanges the diagonal kernels of Darwin. -/
theorem darwinKernel_coordSwap (i k : Fin 3) (y : E3) :
    darwinKernel i i (coordSwap i k y) = darwinKernel k k y := by
  simp only [darwinKernel, LinearIsometryEquiv.norm_map, coordSwap_apply, Equiv.swap_apply_left,
    ite_true]

/-- For a profile invariant under the reflections of the coordinates the mass tensor is diagonal.
-/
theorem selfMass_eq_zero_of_ne (e : ℝ) {η : E3 → ℝ}
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) {i k : Fin 3} (hik : i ≠ k) :
    selfMass e η i k = 0 := by
  have h := integral_mul_kernel_comp_isometry (coordReflection i) (hrot _) (darwinKernel i k)
  simp only [darwinKernel_coordReflection hik, neg_mul, integral_neg, mul_neg] at h
  have h0 : ∫ x, η x * ∫ y, darwinKernel i k y * η (x - y) = 0 := by linarith
  simp only [selfMass, h0, mul_zero]

/-- For a profile invariant under the permutations of the coordinates the diagonal of the mass
tensor is constant. -/
theorem selfMass_diag_eq (e : ℝ) {η : E3 → ℝ}
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (i k : Fin 3) :
    selfMass e η i i = selfMass e η k k := by
  have h := integral_mul_kernel_comp_isometry (coordSwap i k) (hrot _) (darwinKernel i i)
  simp only [darwinKernel_coordSwap] at h
  simp only [selfMass, h]

/-- **The electromagnetic mass of an isotropic charge** (Landau–Lifshitz §75, the `4/3` of
Abraham and Lorentz): for a continuous compactly supported profile invariant under the linear
isometries of space, `δmᵢₖ = (4/3) U δᵢₖ`. -/
theorem selfMass_isotropic (e : ℝ) {η : E3 → ℝ} (hη : Continuous η) (hc : HasCompactSupport η)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (i k : Fin 3) :
    selfMass e η i k = 4 / 3 * selfEnergy e η * if i = k then 1 else 0 := by
  by_cases hik : i = k
  · subst hik
    have htr := trace_selfMass e hη hc
    simp only [Fin.sum_univ_three, selfMass_diag_eq e hrot 1 0, selfMass_diag_eq e hrot 2 0]
      at htr
    rw [selfMass_diag_eq e hrot i 0]
    simp only [ite_true, mul_one]
    linarith
  · simp only [selfMass_eq_zero_of_ne e hrot hik, hik, ite_false, mul_zero]

/-- A function of `‖x‖` is invariant under the linear isometries of space. -/
theorem comp_isometry_of_radial {g : ℝ → ℝ} (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3) :
    (fun z : E3 => g ‖z‖) (f x) = (fun z : E3 => g ‖z‖) x := by
  simp only [LinearIsometryEquiv.norm_map]

/-- The profile of radius `a` of an invariant profile is invariant. -/
theorem scaledProfile_comp_isometry {η : E3 → ℝ}
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (a : ℝ) (f : E3 ≃ₗᵢ[ℝ] E3)
    (x : E3) : scaledProfile a η (f x) = scaledProfile a η x := by
  simp only [scaledProfile, ← LinearIsometryEquiv.map_smul, hrot]

/-- **The isotropic mass counterterm**: for a continuous compactly supported invariant profile
`η`, the profile of radius `a` has `δmᵢₖ(ηₐ) = (4/3) U(η)/a · δᵢₖ`, which diverges as `a → 0` at
fixed charge. -/
theorem selfMass_scaledProfile_isotropic (e : ℝ) {a : ℝ} (ha : 0 < a) {η : E3 → ℝ}
    (hη : Continuous η) (hc : HasCompactSupport η)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (i k : Fin 3) :
    selfMass e (scaledProfile a η) i k = 4 / 3 * selfEnergy e η / a * if i = k then 1 else 0 := by
  rw [selfMass_scaledProfile_apply e ha, selfMass_isotropic e hη hc hrot]
  ring

/-! ### Properties of the profile of radius `a` -/

theorem contDiff_scaledProfile {η : E3 → ℝ} (hη : ContDiff ℝ ∞ η) (a : ℝ) :
    ContDiff ℝ ∞ (scaledProfile a η) :=
  contDiff_const.mul (hη.comp (contDiff_id.const_smul a⁻¹))

/-- A profile vanishing outside the ball of radius `b` has a profile of radius `a` vanishing
outside the ball of radius `a b`. -/
theorem scaledProfile_eq_zero {η : E3 → ℝ} {a b : ℝ} (ha : 0 < a)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {z : E3} (hz : a * b < ‖z‖) :
    scaledProfile a η z = 0 := by
  simp only [scaledProfile]
  rw [hb _ ?_, mul_zero]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha.le), lt_inv_mul_iff₀ ha]
  exact hz

theorem scaledProfile_neg {η : E3 → ℝ} (hηe : ∀ z, η (-z) = η z) (a : ℝ) (z : E3) :
    scaledProfile a η (-z) = scaledProfile a η z := by
  simp only [scaledProfile, smul_neg, hηe]

theorem hasCompactSupport_scaledProfile {η : E3 → ℝ} (hc : HasCompactSupport η) {a : ℝ}
    (ha : 0 < a) : HasCompactSupport (scaledProfile a η) := by
  obtain ⟨b, hb⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall 0 (a * b)) fun z hz => ?_
  refine scaledProfile_eq_zero ha (b := b) (fun w hw => ?_) (by simpa using hz)
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := hb hmem
  rw [mem_closedBall_zero_iff] at this
  linarith

/-! ### A radial normalized bump -/

/-- The radial bump `exp(−1/(1 − ‖x‖²))` inside the unit ball and `0` outside, unnormalized. -/
def radialBumpShape (x : E3) : ℝ := expNegInvGlue (1 - ‖x‖ ^ 2)

theorem contDiff_radialBumpShape : ContDiff ℝ ∞ radialBumpShape :=
  (expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem radialBumpShape_nonneg (x : E3) : 0 ≤ radialBumpShape x := expNegInvGlue.nonneg _

theorem radialBumpShape_eq_zero {z : E3} (hz : 1 < ‖z‖) : radialBumpShape z = 0 :=
  expNegInvGlue.zero_of_nonpos (by nlinarith)

theorem hasCompactSupport_radialBumpShape : HasCompactSupport radialBumpShape :=
  HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz =>
    radialBumpShape_eq_zero (by simpa using hz)

theorem integral_radialBumpShape_pos : 0 < ∫ z, radialBumpShape z :=
  contDiff_radialBumpShape.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hasCompactSupport_radialBumpShape radialBumpShape_nonneg (x := 0)
    (by simp [radialBumpShape])

/-- **A radial normalized bump**: a smooth nonnegative function of `‖x‖` of mass one, vanishing
outside the unit ball. -/
def radialBump (x : E3) : ℝ := (∫ z, radialBumpShape z)⁻¹ * radialBumpShape x

theorem contDiff_radialBump : ContDiff ℝ ∞ radialBump :=
  contDiff_const.mul contDiff_radialBumpShape

theorem radialBump_nonneg (x : E3) : 0 ≤ radialBump x :=
  mul_nonneg (inv_nonneg.2 integral_radialBumpShape_pos.le) (radialBumpShape_nonneg x)

theorem radialBump_eq_zero {z : E3} (hz : 1 < ‖z‖) : radialBump z = 0 := by
  rw [radialBump, radialBumpShape_eq_zero hz, mul_zero]

theorem hasCompactSupport_radialBump : HasCompactSupport radialBump :=
  hasCompactSupport_radialBumpShape.mul_left

theorem radialBump_comp_isometry (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3) : radialBump (f x) = radialBump x := by
  simp only [radialBump, radialBumpShape, LinearIsometryEquiv.norm_map]

theorem radialBump_neg (z : E3) : radialBump (-z) = radialBump z := by
  simp only [radialBump, radialBumpShape, norm_neg]

theorem integral_radialBump : ∫ z, radialBump z = 1 := by
  simp only [radialBump]
  rw [integral_const_mul]
  exact inv_mul_cancel₀ integral_radialBumpShape_pos.ne'

/-- **The isotropic mass counterterm of the radial bump of radius `a`**:
`δmᵢₖ = (4/3) U(1)/a · δᵢₖ`, with the self-energy `U(1)` of the unit radial bump. -/
theorem selfMass_scaledProfile_radialBump (e : ℝ) {a : ℝ} (ha : 0 < a) (i k : Fin 3) :
    selfMass e (scaledProfile a radialBump) i k =
      4 / 3 * selfEnergy e radialBump / a * if i = k then 1 else 0 :=
  selfMass_scaledProfile_isotropic e ha contDiff_radialBump.continuous hasCompactSupport_radialBump
    radialBump_comp_isometry i k

/-! ### The normalized bumps of the library -/

theorem pointBump_eq_normed {a : ℝ} (ha : 0 < a) :
    pointBump a =
      (⟨a / 2, a, by positivity, by linarith⟩ : ContDiffBump (0 : E3)).normed volume := by
  simp only [pointBump, ha, ↓reduceDIte]

/-- **The normalized bumps of the library form the scaling family**:
`pointBump a = a⁻³ pointBump 1 (·/a)`. -/
theorem pointBump_eq_scaledProfile {a : ℝ} (ha : 0 < a) :
    pointBump a = scaledProfile a (pointBump 1) := by
  set f : ContDiffBump (0 : E3) := ⟨a / 2, a, by positivity, by linarith⟩ with hf
  set g : ContDiffBump (0 : E3) := ⟨1 / 2, 1, by norm_num, by norm_num⟩ with hg
  have hfg : ∀ x, f x = g (a⁻¹ • x) := by
    intro x
    have h1 : a / (a / 2) = 1 / (1 / 2) := by field_simp
    have h2 : (a / 2)⁻¹ = (1 / 2)⁻¹ * a⁻¹ := by field_simp
    simp only [ContDiffBump.apply, hf, hg, sub_zero, smul_smul, h1, h2]
  have hint : ∫ x, f x = a ^ 3 * ∫ x, g x := by
    simp only [hfg]
    rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun x => g x) ha.le,
      finrank_euclideanSpace_fin, smul_eq_mul]
  have hg0 : ∫ x, g x ≠ 0 := (ContDiffBump.integral_pos (f := g) (μ := volume)).ne'
  funext x
  rw [pointBump_eq_normed ha, pointBump_one_eq, scaledProfile, ContDiffBump.normed_def,
    ContDiffBump.normed_def, ← hf, ← hg, hint, hfg]
  field_simp

/-- The mass tensor of the library's bump of radius `a` is `a⁻¹` times that of radius one. -/
theorem selfMass_pointBump (e : ℝ) {a : ℝ} (ha : 0 < a) :
    selfMass e (pointBump a) = a⁻¹ • selfMass e (pointBump 1) := by
  rw [pointBump_eq_scaledProfile ha, selfMass_scaledProfile e ha]

/-- The self-energy of the library's bump of radius `a` is `a⁻¹` times that of radius one. -/
theorem selfEnergy_pointBump (e : ℝ) {a : ℝ} (ha : 0 < a) :
    selfEnergy e (pointBump a) = a⁻¹ * selfEnergy e (pointBump 1) := by
  rw [pointBump_eq_scaledProfile ha, selfEnergy_scaledProfile e ha]

/-! ### The oscillating charge of radius `a` -/

/-- **The self-force of the oscillating bump of radius `a`**: the library's normalized bump of
radius `a` on the oscillating path `R(s) = sin s · e₁` has the self-force
`−a⁻¹ Σₖ δmᵢₖ(1) v̇ₖ + (2/3)(e²/4π) v̈ᵢ + O(κ⁴)`, with the mass tensor `δm(1)` of the bump of
radius one: the coefficient of `κ²` is exactly `a⁻¹` times one independent of `a`, the
coefficient of `κ³` does not depend on `a`, and the constant of the remainder depends on `a`. -/
theorem selfForce_expansion_oscillating_pointBump (e : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ C, ∀ κ, 0 ≤ κ → ∀ (t : ℝ) (i : Fin 3),
      |(∫ x, e * pointBump a (x - oscillatingPath (κ * t)) *
          lorentzDensity (slowScalar κ (rigidCharge e (pointBump a) oscillatingPath))
            (slowVector κ (rigidCurrent e (pointBump a) oscillatingPath))
            (κ • deriv oscillatingPath (κ * t)) i (t, x)) -
        (-(a⁻¹ * (κ ^ 2 * ∑ k, selfMass e (pointBump 1) i k *
            deriv (deriv oscillatingPath) (κ * t) k)) +
          2 / 3 * (e ^ 2 / (4 * π)) * (κ ^ 3 * deriv^[3] oscillatingPath (κ * t) i))| ≤
        C * κ ^ 4 := by
  have hη : ContDiff ℝ ∞ (pointBump a) := by
    rw [pointBump_eq_scaledProfile ha]
    exact contDiff_scaledProfile contDiff_pointBump_one a
  have hb : ∀ z : E3, a < ‖z‖ → pointBump a z = 0 := fun z hz => by
    rw [pointBump_eq_scaledProfile ha]
    exact scaledProfile_eq_zero ha (fun z hz => pointBump_one_eq_zero hz) (by rwa [mul_one])
  have hηe : ∀ z : E3, pointBump a (-z) = pointBump a z := fun z => by
    rw [pointBump_eq_scaledProfile ha]
    exact scaledProfile_neg pointBump_one_neg a z
  have hη1 : ∫ z, pointBump a z = 1 := by
    rw [pointBump_eq_scaledProfile ha, integral_scaledProfile ha, integral_pointBump_one]
  obtain ⟨M, hM⟩ := exists_dampingBounds_of_periodic e hη hb contDiff_oscillatingPath
    norm_oscillatingPath_le (by positivity) periodic_oscillatingPath
  refine ⟨(∫ z, |e * pointBump a z|) * (M * (2 * (1 + a)) ^ 6 / 72 +
    M * (2 * (1 + a)) ^ 4 / 6 + 1 * (M * (2 * (1 + a)) ^ 4)), fun κ hκ t i => ?_⟩
  have H := selfForce_expansion e hη ha.le hb hηe hη1 contDiff_oscillatingPath
    norm_oscillatingPath_le norm_deriv_oscillatingPath_le hM hκ t i
  have key : a⁻¹ * (κ ^ 2 * ∑ k, selfMass e (pointBump 1) i k *
      deriv (deriv oscillatingPath) (κ * t) k) =
      κ ^ 2 * ∑ k, selfMass e (pointBump a) i k * deriv (deriv oscillatingPath) (κ * t) k := by
    simp only [selfMass_pointBump e ha, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [key]
  exact H.trans (le_of_eq (by ring))

/-- **The self-force of the oscillating radial bump of radius `a`**: the radial bump of radius `a`
on the oscillating path has the self-force `−(4/3) U(1)/a · v̇ᵢ + (2/3)(e²/4π) v̈ᵢ + O(κ⁴)` with
`v̇ = κ² R̈(κt)`, `v̈ = κ³ R⃛(κt)` and the self-energy `U(1)` of the unit radial bump: the mass
counterterm is isotropic and proportional to `1/a`, the damping force does not depend on `a`, and
the constant of the remainder depends on `a`. -/
theorem selfForce_expansion_oscillating_radial (e : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ C, ∀ κ, 0 ≤ κ → ∀ (t : ℝ) (i : Fin 3),
      |(∫ x, e * scaledProfile a radialBump (x - oscillatingPath (κ * t)) *
          lorentzDensity
            (slowScalar κ (rigidCharge e (scaledProfile a radialBump) oscillatingPath))
            (slowVector κ (rigidCurrent e (scaledProfile a radialBump) oscillatingPath))
            (κ • deriv oscillatingPath (κ * t)) i (t, x)) -
        (-(4 / 3 * selfEnergy e radialBump / a *
            (κ ^ 2 * deriv (deriv oscillatingPath) (κ * t) i)) +
          2 / 3 * (e ^ 2 / (4 * π)) * (κ ^ 3 * deriv^[3] oscillatingPath (κ * t) i))| ≤
        C * κ ^ 4 := by
  have hη := contDiff_scaledProfile contDiff_radialBump a
  have hb : ∀ z : E3, a < ‖z‖ → scaledProfile a radialBump z = 0 := fun z hz =>
    scaledProfile_eq_zero ha (fun z hz => radialBump_eq_zero hz) (by rwa [mul_one])
  obtain ⟨M, hM⟩ := exists_dampingBounds_of_periodic e hη hb contDiff_oscillatingPath
    norm_oscillatingPath_le (by positivity) periodic_oscillatingPath
  refine ⟨(∫ z, |e * scaledProfile a radialBump z|) * (M * (2 * (1 + a)) ^ 6 / 72 +
    M * (2 * (1 + a)) ^ 4 / 6 + 1 * (M * (2 * (1 + a)) ^ 4)), fun κ hκ t i => ?_⟩
  have H := selfForce_expansion e hη ha.le hb (scaledProfile_neg radialBump_neg a)
    (by rw [integral_scaledProfile ha, integral_radialBump]) contDiff_oscillatingPath
    norm_oscillatingPath_le norm_deriv_oscillatingPath_le hM hκ t i
  have key : 4 / 3 * selfEnergy e radialBump / a *
      (κ ^ 2 * deriv (deriv oscillatingPath) (κ * t) i) =
      κ ^ 2 * ∑ k, selfMass e (scaledProfile a radialBump) i k *
        deriv (deriv oscillatingPath) (κ * t) k := by
    simp only [selfMass_scaledProfile_radialBump e ha, mul_ite, mul_one, mul_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  rw [key]
  exact H.trans (le_of_eq (by ring))

/-! ### The positivity of the self-energy and the divergence of the counterterm -/

/-- **The self-energy of a nonnegative charge is positive**: for a continuous compactly supported
profile `η ≥ 0` with `η(x₀) > 0` and `e ≠ 0`, `U > 0`. -/
theorem selfEnergy_pos {e : ℝ} (he : e ≠ 0) {η : E3 → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) {x₀ : E3} (hx₀ : 0 < η x₀) :
    0 < selfEnergy e η := by
  obtain ⟨b, hb⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set F : ℝ × E3 → ℝ := fun p => η p.2 with hF
  have hFc : Continuous F := hη.comp continuous_snd
  have hFs : SpatialSupport b F := fun p hp => by
    simp only [hF]
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have := hb hmem
    rw [mem_closedBall_zero_iff] at this
    linarith
  have hin : ∀ x : E3, Integrable fun y => Potential.newtonKernel y * η (x - y) := fun x => by
    have := (hFs.kernelSupport Potential.newtonKernel).integrable
      Potential.locallyIntegrable_newtonKernel hFc (0, x)
    simpa [hF, smul_eq_mul] using this
  have hcont : Continuous fun x : E3 => ∫ y, Potential.newtonKernel y * η (x - y) := by
    have := (continuous_kernelIntegral Potential.locallyIntegrable_newtonKernel hFc
      (hFs.kernelSupport Potential.newtonKernel)).comp
      (continuous_const.prodMk continuous_id : Continuous fun x : E3 => ((0 : ℝ), x))
    simpa [Function.comp_def, kernelIntegral, hF, smul_eq_mul] using this
  have hΦ0 : ∀ x : E3, 0 ≤ ∫ y, Potential.newtonKernel y * η (x - y) := fun x =>
    integral_nonneg fun y => mul_nonneg (Potential.newtonKernel_nonneg y) (hη0 _)
  -- the potential at `x₀` is positive: `η(x₀ − y) > 0` near `y = 0`
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hη) x₀ hx₀
  set y₀ : E3 := (r / 2) • EuclideanSpace.single 0 1 with hy₀
  have hny₀ : ‖y₀‖ = r / 2 := by
    rw [hy₀, norm_smul]
    simp [abs_of_pos hr]
  have hsupp : ball y₀ (r / 4) ⊆
      Function.support fun y => Potential.newtonKernel y * η (x₀ - y) := by
    intro y hy
    rw [mem_ball] at hy
    have hy1 : r / 4 ≤ ‖y‖ := by
      have := norm_sub_norm_le y₀ y
      rw [hny₀, ← dist_eq_norm, dist_comm] at this
      linarith
    have hy2 : ‖y‖ < r := by
      have := norm_le_norm_add_norm_sub' y y₀
      rw [hny₀, ← dist_eq_norm] at this
      linarith
    have hN : 0 < Potential.newtonKernel y := by
      rw [Potential.newtonKernel]
      have : 0 < ‖y‖ := by linarith
      positivity
    have hη' : 0 < η (x₀ - y) := hball (by
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
      exact hy2)
    exact (mul_pos hN hη').ne'
  have hΦ : 0 < ∫ y, Potential.newtonKernel y * η (x₀ - y) := by
    rw [integral_pos_iff_support_of_nonneg
      (fun y => mul_nonneg (Potential.newtonKernel_nonneg y) (hη0 _)) (hin x₀)]
    exact (Metric.measure_ball_pos volume y₀ (by positivity)).trans_le (measure_mono hsupp)
  have hout : 0 < ∫ x, η x * ∫ y, Potential.newtonKernel y * η (x - y) :=
    (hη.mul hcont).integral_pos_of_hasCompactSupport_nonneg_nonzero hc.mul_right
      (fun x => mul_nonneg (hη0 x) (hΦ0 x)) (mul_pos hx₀ hΦ).ne'
  have he2 : 0 < e ^ 2 := by positivity
  rw [selfEnergy]
  positivity

theorem selfEnergy_radialBump_pos {e : ℝ} (he : e ≠ 0) : 0 < selfEnergy e radialBump :=
  selfEnergy_pos he contDiff_radialBump.continuous hasCompactSupport_radialBump radialBump_nonneg
    (x₀ := 0) (mul_pos (inv_pos.2 integral_radialBumpShape_pos)
      (by simpa [radialBumpShape] using expNegInvGlue.pos_of_pos one_pos))

/-- **The electromagnetic mass diverges as the size goes to zero**: for `e ≠ 0` the diagonal of
the mass tensor of the radial bump of radius `a` tends to `+∞` as `a → 0⁺`, at fixed charge. -/
theorem tendsto_selfMass_scaledProfile_radialBump {e : ℝ} (he : e ≠ 0) (i : Fin 3) :
    Tendsto (fun a => selfMass e (scaledProfile a radialBump) i i) (𝓝[>] 0) atTop := by
  have hU := selfEnergy_radialBump_pos he
  refine (tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity : 0 < 4 / 3 *
    selfEnergy e radialBump)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  rw [selfMass_scaledProfile_radialBump e ha]
  simp only [ite_true, mul_one]
  ring

end ProjectAinos.Electrodynamics.RadiationReaction
