/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.RadiationReaction.RadiusScaling
import ProjectAinos.Electrodynamics.RadiationReaction.Rectilinear

/-! Public consumers of the size dependence of the electromagnetic mass and of the selection of
the physical solutions of radiation damping (Landau–Lifshitz §§75, 76): the exact `1/a` scaling
of the mass tensor and of the self-energy of a charge of radius `a`, the isotropic mass
counterterm `(4/3) U(1)/a` and its divergence, the self-force of the oscillating bump of radius
`a`, the projection of the equation of Lorentz and Dirac on a rectilinear motion, the selected
proper acceleration with its uniqueness among the solutions bounded in the future, the runaways
and the preacceleration, and the selected world line. Default elaborator options are
intentional: these checks must not rely on the implementation's transparency settings. Every
statement is pinned with its type. -/

noncomputable section

section RadiationSelection

open MeasureTheory Filter Set Metric Real

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.RadiationReaction

open SmoothGeometry SmoothGeometry.Wave SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section RadiusScaling

example (a : ℝ) (η : E3 → ℝ) (x : E3) :
    ℝ :=
  scaledProfile a η x

example (a : ℝ) (η : E3 → ℝ) (x : E3) :
    scaledProfile a η x = (a ^ 3)⁻¹ * η (a⁻¹ • x) :=
  rfl

example {a : ℝ} (ha : 0 < a) (η : E3 → ℝ) :
    ∫ x, scaledProfile a η x = ∫ x, η x :=
  integral_scaledProfile ha η

example {a : ℝ} (ha : 0 < a) (η : E3 → ℝ) {K : E3 → ℝ} (hK : ∀ y, K (a • y) = a⁻¹ * K y) :
    ∫ x, scaledProfile a η x * ∫ y, K y * scaledProfile a η (x - y) =
      a⁻¹ * ∫ x, η x * ∫ y, K y * η (x - y) :=
  integral_scaledProfile_mul_kernel ha η hK

example {a : ℝ} (ha : 0 < a) (y : E3) :
    Potential.newtonKernel (a • y) = a⁻¹ * Potential.newtonKernel y :=
  newtonKernel_smul ha y

example {a : ℝ} (ha : 0 < a) (i k : Fin 3) (y : E3) :
    darwinKernel i k (a • y) = a⁻¹ * darwinKernel i k y :=
  darwinKernel_smul ha i k y

example (e : ℝ) {a : ℝ} (ha : 0 < a) (η : E3 → ℝ) (i k : Fin 3) :
    selfMass e (scaledProfile a η) i k = a⁻¹ * selfMass e η i k :=
  selfMass_scaledProfile_apply e ha η i k

example (e : ℝ) {a : ℝ} (ha : 0 < a) (η : E3 → ℝ) :
    selfMass e (scaledProfile a η) = a⁻¹ • selfMass e η :=
  selfMass_scaledProfile e ha η

example (e : ℝ) {a : ℝ} (ha : 0 < a) (η : E3 → ℝ) :
    selfEnergy e (scaledProfile a η) = a⁻¹ * selfEnergy e η :=
  selfEnergy_scaledProfile e ha η

example (i k : Fin 3) :
    E3 ≃ₗᵢ[ℝ] E3 :=
  coordSwap i k

example (i k l : Fin 3) (y : E3) :
    coordSwap i k y l = y (Equiv.swap i k l) :=
  coordSwap_apply i k l y

example (j : Fin 3) :
    E3 ≃ₗᵢ[ℝ] E3 :=
  coordReflection j

example (j l : Fin 3) (y : E3) :
    coordReflection j y l = if l = j then -y l else y l :=
  coordReflection_apply j l y

example (f : E3 ≃ₗᵢ[ℝ] E3) {η : E3 → ℝ} (hf : ∀ x, η (f x) = η x) (K : E3 → ℝ) :
    ∫ x, η x * ∫ y, K y * η (x - y) = ∫ x, η x * ∫ y, K (f y) * η (x - y) :=
  integral_mul_kernel_comp_isometry f hf K

example {i k : Fin 3} (hik : i ≠ k) (y : E3) :
    darwinKernel i k (coordReflection i y) = -darwinKernel i k y :=
  darwinKernel_coordReflection hik y

example (i k : Fin 3) (y : E3) :
    darwinKernel i i (coordSwap i k y) = darwinKernel k k y :=
  darwinKernel_coordSwap i k y

example (e : ℝ) {η : E3 → ℝ} (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) {i k : Fin 3}
    (hik : i ≠ k) :
    selfMass e η i k = 0 :=
  selfMass_eq_zero_of_ne e hrot hik

example (e : ℝ) {η : E3 → ℝ} (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (i k : Fin 3) :
    selfMass e η i i = selfMass e η k k :=
  selfMass_diag_eq e hrot i k

example (e : ℝ) {η : E3 → ℝ} (hη : Continuous η) (hc : HasCompactSupport η)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (i k : Fin 3) :
    selfMass e η i k = 4 / 3 * selfEnergy e η * if i = k then 1 else 0 :=
  selfMass_isotropic e hη hc hrot i k

example {g : ℝ → ℝ} (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3) :
    (fun z : E3 => g ‖z‖) (f x) = (fun z : E3 => g ‖z‖) x :=
  comp_isometry_of_radial f x

example {η : E3 → ℝ} (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (a : ℝ)
    (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3) :
    scaledProfile a η (f x) = scaledProfile a η x :=
  scaledProfile_comp_isometry hrot a f x

example (e : ℝ) {a : ℝ} (ha : 0 < a) {η : E3 → ℝ} (hη : Continuous η) (hc : HasCompactSupport η)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (i k : Fin 3) :
    selfMass e (scaledProfile a η) i k = 4 / 3 * selfEnergy e η / a * if i = k then 1 else 0 :=
  selfMass_scaledProfile_isotropic e ha hη hc hrot i k

example {η : E3 → ℝ} (hη : ContDiff ℝ ∞ η) (a : ℝ) :
    ContDiff ℝ ∞ (scaledProfile a η) :=
  contDiff_scaledProfile hη a

example {η : E3 → ℝ} {a b : ℝ} (ha : 0 < a) (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {z : E3}
    (hz : a * b < ‖z‖) :
    scaledProfile a η z = 0 :=
  scaledProfile_eq_zero ha hb hz

example {η : E3 → ℝ} (hηe : ∀ z, η (-z) = η z) (a : ℝ) (z : E3) :
    scaledProfile a η (-z) = scaledProfile a η z :=
  scaledProfile_neg hηe a z

example {η : E3 → ℝ} (hc : HasCompactSupport η) {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (scaledProfile a η) :=
  hasCompactSupport_scaledProfile hc ha

example (x : E3) :
    ℝ :=
  radialBumpShape x

example :
    ContDiff ℝ ∞ radialBumpShape :=
  contDiff_radialBumpShape

example (x : E3) :
    0 ≤ radialBumpShape x :=
  radialBumpShape_nonneg x

example {z : E3} (hz : 1 < ‖z‖) :
    radialBumpShape z = 0 :=
  radialBumpShape_eq_zero hz

example :
    HasCompactSupport radialBumpShape :=
  hasCompactSupport_radialBumpShape

example :
    0 < ∫ z, radialBumpShape z :=
  integral_radialBumpShape_pos

example (x : E3) :
    ℝ :=
  radialBump x

example (x : E3) :
    radialBump x = (∫ z, radialBumpShape z)⁻¹ * expNegInvGlue (1 - ‖x‖ ^ 2) :=
  rfl

example :
    ContDiff ℝ ∞ radialBump :=
  contDiff_radialBump

example (x : E3) :
    0 ≤ radialBump x :=
  radialBump_nonneg x

example {z : E3} (hz : 1 < ‖z‖) :
    radialBump z = 0 :=
  radialBump_eq_zero hz

example :
    HasCompactSupport radialBump :=
  hasCompactSupport_radialBump

example (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3) :
    radialBump (f x) = radialBump x :=
  radialBump_comp_isometry f x

example (z : E3) :
    radialBump (-z) = radialBump z :=
  radialBump_neg z

example :
    ∫ z, radialBump z = 1 :=
  integral_radialBump

example (e : ℝ) {a : ℝ} (ha : 0 < a) (i k : Fin 3) :
    selfMass e (scaledProfile a radialBump) i k =
      4 / 3 * selfEnergy e radialBump / a * if i = k then 1 else 0 :=
  selfMass_scaledProfile_radialBump e ha i k

example {a : ℝ} (ha : 0 < a) :
    pointBump a =
      (⟨a / 2, a, by positivity, by linarith⟩ : ContDiffBump (0 : E3)).normed volume :=
  pointBump_eq_normed ha

example {a : ℝ} (ha : 0 < a) :
    pointBump a = scaledProfile a (pointBump 1) :=
  pointBump_eq_scaledProfile ha

example (e : ℝ) {a : ℝ} (ha : 0 < a) :
    selfMass e (pointBump a) = a⁻¹ • selfMass e (pointBump 1) :=
  selfMass_pointBump e ha

example (e : ℝ) {a : ℝ} (ha : 0 < a) :
    selfEnergy e (pointBump a) = a⁻¹ * selfEnergy e (pointBump 1) :=
  selfEnergy_pointBump e ha

example (e : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ C, ∀ κ, 0 ≤ κ → ∀ (t : ℝ) (i : Fin 3),
      |(∫ x, e * pointBump a (x - oscillatingPath (κ * t)) *
          lorentzDensity (slowScalar κ (rigidCharge e (pointBump a) oscillatingPath))
            (slowVector κ (rigidCurrent e (pointBump a) oscillatingPath))
            (κ • deriv oscillatingPath (κ * t)) i (t, x)) -
        (-(a⁻¹ * (κ ^ 2 * ∑ k, selfMass e (pointBump 1) i k *
            deriv (deriv oscillatingPath) (κ * t) k)) +
          2 / 3 * (e ^ 2 / (4 * π)) * (κ ^ 3 * deriv^[3] oscillatingPath (κ * t) i))| ≤
        C * κ ^ 4 :=
  selfForce_expansion_oscillating_pointBump e ha

example (e : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ C, ∀ κ, 0 ≤ κ → ∀ (t : ℝ) (i : Fin 3),
      |(∫ x, e * scaledProfile a radialBump (x - oscillatingPath (κ * t)) *
          lorentzDensity
            (slowScalar κ (rigidCharge e (scaledProfile a radialBump) oscillatingPath))
            (slowVector κ (rigidCurrent e (scaledProfile a radialBump) oscillatingPath))
            (κ • deriv oscillatingPath (κ * t)) i (t, x)) -
        (-(4 / 3 * selfEnergy e radialBump / a *
            (κ ^ 2 * deriv (deriv oscillatingPath) (κ * t) i)) +
          2 / 3 * (e ^ 2 / (4 * π)) * (κ ^ 3 * deriv^[3] oscillatingPath (κ * t) i))| ≤
        C * κ ^ 4 :=
  selfForce_expansion_oscillating_radial e ha

example {e : ℝ} (he : e ≠ 0) {η : E3 → ℝ} (hη : Continuous η) (hc : HasCompactSupport η)
    (hη0 : ∀ x, 0 ≤ η x) {x₀ : E3} (hx₀ : 0 < η x₀) :
    0 < selfEnergy e η :=
  selfEnergy_pos he hη hc hη0 hx₀

example {e : ℝ} (he : e ≠ 0) :
    0 < selfEnergy e radialBump :=
  selfEnergy_radialBump_pos he

example {e : ℝ} (he : e ≠ 0) (i : Fin 3) :
    Tendsto (fun a => selfMass e (scaledProfile a radialBump) i i) (𝓝[>] 0) atTop :=
  tendsto_selfMass_scaledProfile_radialBump he i

end RadiusScaling

section Rectilinear

example (ϑ : ℝ → ℝ) (τ : ℝ) :
    Spacetime :=
  rectilinearVelocity ϑ τ

example (ϑ : ℝ → ℝ) (τ : ℝ) :
    rectilinearVelocity ϑ τ = ![Real.cosh (ϑ τ), Real.sinh (ϑ τ), 0, 0] :=
  rfl

example (ϑ : ℝ → ℝ) (τ : ℝ) :
    Spacetime :=
  rectilinearDirection ϑ τ

example (ϑ : ℝ → ℝ) (τ : ℝ) :
    rectilinearDirection ϑ τ = ![Real.sinh (ϑ τ), Real.cosh (ϑ τ), 0, 0] :=
  rfl

example (ϑ : ℝ → ℝ) (τ : ℝ) :
    minkowskiForm .timeNegative 3 (rectilinearVelocity ϑ τ) (rectilinearVelocity ϑ τ) = -1 :=
  minkowskiForm_rectilinearVelocity ϑ τ

example (ϑ : ℝ → ℝ) (τ : ℝ) :
    minkowskiForm .timeNegative 3 (rectilinearDirection ϑ τ) (rectilinearDirection ϑ τ) = 1 :=
  minkowskiForm_rectilinearDirection ϑ τ

example (ϑ : ℝ → ℝ) (τ : ℝ) :
    minkowskiForm .timeNegative 3 (rectilinearDirection ϑ τ) (rectilinearVelocity ϑ τ) = 0 :=
  minkowskiForm_rectilinearDirection_velocity ϑ τ

example (ϑ : ℝ → ℝ) (τ : ℝ) :
    rectilinearDirection ϑ τ ≠ 0 :=
  rectilinearDirection_ne_zero ϑ τ

example {n : WithTop ℕ∞} {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ n ϑ) :
    ContDiff ℝ n (rectilinearVelocity ϑ) :=
  contDiff_rectilinearVelocity hϑ

example {ϑ : ℝ → ℝ} {ϑ' τ : ℝ} (h : HasDerivAt ϑ ϑ' τ) :
    HasDerivAt (rectilinearVelocity ϑ) (ϑ' • rectilinearDirection ϑ τ) τ :=
  hasDerivAt_rectilinearVelocity h

example {ϑ : ℝ → ℝ} {ϑ' τ : ℝ} (h : HasDerivAt ϑ ϑ' τ) :
    HasDerivAt (rectilinearDirection ϑ) (ϑ' • rectilinearVelocity ϑ τ) τ :=
  hasDerivAt_rectilinearDirection h

example {ϑ : ℝ → ℝ} (hϑ : Differentiable ℝ ϑ) :
    deriv (rectilinearVelocity ϑ) = fun τ => deriv ϑ τ • rectilinearDirection ϑ τ :=
  deriv_rectilinearVelocity hϑ

example {ϑ : ℝ → ℝ} (hϑ : Differentiable ℝ ϑ) (τ : ℝ) :
    minkowskiForm .timeNegative 3 (deriv (rectilinearVelocity ϑ) τ)
      (deriv (rectilinearVelocity ϑ) τ) = deriv ϑ τ ^ 2 :=
  minkowskiForm_deriv_rectilinearVelocity hϑ τ

example {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ) (τ : ℝ) :
    deriv (deriv (rectilinearVelocity ϑ)) τ =
      deriv (deriv ϑ) τ • rectilinearDirection ϑ τ +
        deriv ϑ τ ^ 2 • rectilinearVelocity ϑ τ :=
  deriv_deriv_rectilinearVelocity hϑ τ

example (e : ℝ) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ) (τ : ℝ) :
    lorentzDiracForce e (rectilinearVelocity ϑ) τ =
      (2 / 3 * (e ^ 2 / (4 * π)) * deriv (deriv ϑ) τ) • rectilinearDirection ϑ τ :=
  lorentzDiracForce_rectilinear e hϑ τ

example (m e : ℝ) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ) (τ : ℝ) :
    minkowskiForm .timeNegative 3
        (m • deriv (rectilinearVelocity ϑ) τ - lorentzDiracForce e (rectilinearVelocity ϑ) τ)
        (rectilinearDirection ϑ τ) =
      m * deriv ϑ τ - 2 / 3 * (e ^ 2 / (4 * π)) * deriv (deriv ϑ) τ :=
  minkowskiForm_lorentzDirac_rectilinear m e hϑ τ

example (m e : ℝ) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ) (F : Spacetime) (τ : ℝ) :
    m • deriv (rectilinearVelocity ϑ) τ = F + lorentzDiracForce e (rectilinearVelocity ϑ) τ ↔
      F = (m * deriv ϑ τ - 2 / 3 * (e ^ 2 / (4 * π)) * deriv (deriv ϑ) τ) •
        rectilinearDirection ϑ τ :=
  lorentzDirac_rectilinear_iff m e hϑ F τ

example (m e : ℝ) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ) (f : ℝ → ℝ) (τ : ℝ) :
    m • deriv (rectilinearVelocity ϑ) τ =
        f τ • rectilinearDirection ϑ τ + lorentzDiracForce e (rectilinearVelocity ϑ) τ ↔
      m * deriv ϑ τ = f τ + 2 / 3 * (e ^ 2 / (4 * π)) * deriv (deriv ϑ) τ :=
  lorentzDirac_rectilinear_force_iff m e hϑ f τ

example (m τ₀ : ℝ) (f : ℝ → ℝ) (τ : ℝ) :
    ℝ :=
  selectedAcceleration m τ₀ f τ

example (m τ₀ : ℝ) (f : ℝ → ℝ) (τ : ℝ) :
    selectedAcceleration m τ₀ f τ =
      (m * τ₀)⁻¹ * ∫ s in Ioi τ, Real.exp (-(s - τ) / τ₀) * f s :=
  rfl

example (m τ₀ : ℝ) :
    selectedAcceleration m τ₀ 0 = 0 :=
  selectedAcceleration_zero m τ₀

example {m τ₀ : ℝ} {f : ℝ → ℝ} {T : ℝ} (hT : ∀ s, T < s → f s = 0) {τ : ℝ} (hτ : T ≤ τ) :
    selectedAcceleration m τ₀ f τ = 0 :=
  selectedAcceleration_eq_zero_of_le hT hτ

example {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ T, ∀ s, T < s → f s = 0 :=
  exists_eq_zero_of_lt hfc

example {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) {T : ℝ}
    (hT : ∀ s, T < s → g s = 0) (τ : ℝ) :
    ∫ s in Ioi τ, g s = ∫ s in τ..T, g s :=
  setIntegral_Ioi_eq_intervalIntegral hg hgc hT τ

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {T : ℝ}
    (hT : ∀ s, T < s → f s = 0) (τ : ℝ) :
    selectedAcceleration m τ₀ f τ =
      (m * τ₀)⁻¹ * (Real.exp (τ / τ₀) * ∫ s in τ..T, Real.exp (-s / τ₀) * f s) :=
  selectedAcceleration_eq hf hfc hT τ

example (τ τ₀ : ℝ) :
    Real.exp (τ / τ₀) * Real.exp (-τ / τ₀) = 1 :=
  exp_div_mul_exp_neg_div τ τ₀

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (τ : ℝ) :
    HasDerivAt (selectedAcceleration m τ₀ f)
      (τ₀⁻¹ * selectedAcceleration m τ₀ f τ - (m * τ₀)⁻¹ * f τ) τ :=
  hasDerivAt_selectedAcceleration hf hfc τ

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hm : m ≠ 0) (hτ₀ : τ₀ ≠ 0) (hf : Continuous f)
    (hfc : HasCompactSupport f) (τ : ℝ) :
    m * selectedAcceleration m τ₀ f τ =
      f τ + m * τ₀ * deriv (selectedAcceleration m τ₀ f) τ :=
  selectedAcceleration_solves hm hτ₀ hf hfc τ

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Differentiable ℝ (selectedAcceleration m τ₀ f) :=
  differentiable_selectedAcceleration hf hfc

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ContDiff ℝ ∞ (selectedAcceleration m τ₀ f) :=
  contDiff_selectedAcceleration hf hfc

example {β : ℝ → ℝ} {c : ℝ} (h : ∀ τ, HasDerivAt β (c * β τ) τ) (τ : ℝ) :
    β τ = β 0 * Real.exp (c * τ) :=
  eq_mul_exp_of_hasDerivAt h τ

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hm : m ≠ 0) (hτ₀ : τ₀ ≠ 0) (hf : Continuous f)
    (hfc : HasCompactSupport f) {α : ℝ → ℝ} (hα : Differentiable ℝ α) :
    (∀ τ, m * α τ = f τ + m * τ₀ * deriv α τ) ↔
      ∃ C, ∀ τ, α τ = selectedAcceleration m τ₀ f τ + C * Real.exp (τ / τ₀) :=
  solution_iff hm hτ₀ hf hfc hα

example {τ₀ : ℝ} {C : ℝ} (hC : C ≠ 0) (hτ₀ : 0 < τ₀) :
    Tendsto (fun τ => |C| * Real.exp (τ / τ₀)) atTop atTop :=
  tendsto_abs_mul_exp hC hτ₀

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hm : m ≠ 0) (hτ₀ : 0 < τ₀) (hf : Continuous f)
    (hfc : HasCompactSupport f) {α : ℝ → ℝ} (hα : Differentiable ℝ α)
    (h : ∀ τ, m * α τ = f τ + m * τ₀ * deriv α τ) {M τ₁ : ℝ} (hb : ∀ τ, τ₁ ≤ τ → |α τ| ≤ M) :
    α = selectedAcceleration m τ₀ f :=
  eq_selectedAcceleration_of_bounded hm hτ₀ hf hfc hα h hb

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hm : m ≠ 0) (hτ₀ : 0 < τ₀) (hf : Continuous f)
    (hfc : HasCompactSupport f) {α : ℝ → ℝ} (hα : Differentiable ℝ α)
    (h : ∀ τ, m * α τ = f τ + m * τ₀ * deriv α τ) (hne : α ≠ selectedAcceleration m τ₀ f) :
    Tendsto (fun τ => |α τ|) atTop atTop :=
  tendsto_abs_of_ne_selectedAcceleration hm hτ₀ hf hfc hα h hne

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hm : 0 < m) (hτ₀ : 0 < τ₀) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hf0 : ∀ s, 0 ≤ f s) {s₀ : ℝ} (hs₀ : 0 < f s₀) {τ : ℝ}
    (hτ : τ < s₀) :
    0 < selectedAcceleration m τ₀ f τ :=
  selectedAcceleration_pos hm hτ₀ hf hfc hf0 hs₀ hτ

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hm : 0 < m) (hτ₀ : 0 < τ₀) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hf0 : ∀ s, 0 ≤ f s) {s₀ : ℝ} (hs₀ : 0 < f s₀) {T₁ : ℝ}
    (hT₁ : ∀ s, s < T₁ → f s = 0) {τ : ℝ} (hτ : τ < T₁) :
    f τ = 0 ∧ 0 < selectedAcceleration m τ₀ f τ :=
  selectedAcceleration_preacceleration hm hτ₀ hf hfc hf0 hs₀ hT₁ hτ

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {T₁ : ℝ}
    (hT₁ : ∀ s, s < T₁ → f s = 0) {τ : ℝ} (hτ : τ ≤ T₁) :
    selectedAcceleration m τ₀ f τ =
      Real.exp ((τ - T₁) / τ₀) * selectedAcceleration m τ₀ f T₁ :=
  selectedAcceleration_before hf hfc hT₁ hτ

example (s : ℝ) :
    ℝ :=
  pulse s

example (s : ℝ) :
    pulse s = expNegInvGlue (1 - s ^ 2) :=
  rfl

example :
    ContDiff ℝ ∞ pulse :=
  contDiff_pulse

example (s : ℝ) :
    0 ≤ pulse s :=
  pulse_nonneg s

example {s : ℝ} (hs : 1 < |s|) :
    pulse s = 0 :=
  pulse_eq_zero hs

example :
    HasCompactSupport pulse :=
  hasCompactSupport_pulse

example :
    0 < pulse 0 :=
  pulse_zero_pos

example {s : ℝ} (hs : s < -1) :
    pulse s = 0 :=
  pulse_eq_zero_of_lt hs

example {m τ₀ : ℝ} (hm : 0 < m) (hτ₀ : 0 < τ₀) {τ : ℝ} (hτ : τ < -1) :
    pulse τ = 0 ∧ 0 < selectedAcceleration m τ₀ pulse τ :=
  selectedAcceleration_pulse hm hτ₀ hτ

example (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ)
    (h : ∀ τ, m • deriv (rectilinearVelocity ϑ) τ = lorentzDiracForce e (rectilinearVelocity ϑ) τ)
    {C : ℝ} (hC : ∀ τ, 0 ≤ τ → |deriv ϑ τ| ≤ C) (τ : ℝ) :
    deriv ϑ τ = 0 :=
  rectilinear_free_eq_zero e m he hm hϑ h hC τ

example (e m : ℝ) :
    ℝ :=
  radiationTime e m

example (e m : ℝ) :
    radiationTime e m = 2 / 3 * (e ^ 2 / (4 * π)) / m :=
  rfl

example {e m : ℝ} (he : e ≠ 0) (hm : 0 < m) :
    0 < radiationTime e m :=
  radiationTime_pos he hm

example (e : ℝ) {m : ℝ} (hm : m ≠ 0) :
    m * radiationTime e m = 2 / 3 * (e ^ 2 / (4 * π)) :=
  mul_radiationTime e hm

example (e : ℝ) {m : ℝ} (hm : m ≠ 0) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ) (f : ℝ → ℝ) (τ : ℝ) :
    m • deriv (rectilinearVelocity ϑ) τ =
        f τ • rectilinearDirection ϑ τ + lorentzDiracForce e (rectilinearVelocity ϑ) τ ↔
      m * deriv ϑ τ = f τ + m * radiationTime e m * deriv (deriv ϑ) τ :=
  lorentzDirac_rectilinear_iff_radiationTime e hm hϑ f τ

example (m τ₀ : ℝ) (f : ℝ → ℝ) (ϑ₀ τ : ℝ) :
    ℝ :=
  selectedRapidity m τ₀ f ϑ₀ τ

example (m τ₀ : ℝ) (f : ℝ → ℝ) (ϑ₀ τ : ℝ) :
    selectedRapidity m τ₀ f ϑ₀ τ = ϑ₀ + ∫ σ in (0 : ℝ)..τ, selectedAcceleration m τ₀ f σ :=
  rfl

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (ϑ₀ τ : ℝ) :
    HasDerivAt (selectedRapidity m τ₀ f ϑ₀) (selectedAcceleration m τ₀ f τ) τ :=
  hasDerivAt_selectedRapidity hf hfc ϑ₀ τ

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (ϑ₀ : ℝ) :
    deriv (selectedRapidity m τ₀ f ϑ₀) = selectedAcceleration m τ₀ f :=
  deriv_selectedRapidity hf hfc ϑ₀

example (m τ₀ : ℝ) (f : ℝ → ℝ) (ϑ₀ : ℝ) :
    selectedRapidity m τ₀ f ϑ₀ 0 = ϑ₀ :=
  selectedRapidity_zero m τ₀ f ϑ₀

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (ϑ₀ : ℝ) :
    ContDiff ℝ ∞ (selectedRapidity m τ₀ f ϑ₀) :=
  contDiff_selectedRapidity hf hfc ϑ₀

example {m τ₀ : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (ϑ₀ : ℝ) {T : ℝ}
    (hT : ∀ s, T < s → f s = 0) {τ : ℝ} (hτ : T ≤ τ) :
    deriv (rectilinearVelocity (selectedRapidity m τ₀ f ϑ₀)) τ = 0 :=
  deriv_selectedVelocity_eq_zero_of_le hf hfc ϑ₀ hT hτ

example (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (ϑ₀ τ : ℝ) :
    m • deriv (rectilinearVelocity (selectedRapidity m (radiationTime e m) f ϑ₀)) τ =
      f τ • rectilinearDirection (selectedRapidity m (radiationTime e m) f ϑ₀) τ +
        lorentzDiracForce e (rectilinearVelocity (selectedRapidity m (radiationTime e m) f ϑ₀))
          τ :=
  selected_lorentzDirac e m he hm hf hfc ϑ₀ τ

example (m τ₀ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (ϑ₀ : ℝ) :
    ContDiff ℝ ∞ (rectilinearVelocity (selectedRapidity m τ₀ f ϑ₀)) :=
  contDiff_selectedVelocity m τ₀ hf hfc ϑ₀

example (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ)
    (h : ∀ τ, m • deriv (rectilinearVelocity ϑ) τ =
      f τ • rectilinearDirection ϑ τ + lorentzDiracForce e (rectilinearVelocity ϑ) τ) :
    ∃ C, ∀ τ, deriv ϑ τ =
      selectedAcceleration m (radiationTime e m) f τ + C * Real.exp (τ / radiationTime e m) :=
  rectilinear_lorentzDirac_selection e m he hm hf hfc hϑ h

example (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ)
    (h : ∀ τ, m • deriv (rectilinearVelocity ϑ) τ =
      f τ • rectilinearDirection ϑ τ + lorentzDiracForce e (rectilinearVelocity ϑ) τ)
    {M τ₁ : ℝ} (hb : ∀ τ, τ₁ ≤ τ → |deriv ϑ τ| ≤ M) :
    ϑ = selectedRapidity m (radiationTime e m) f (ϑ 0) :=
  rectilinear_lorentzDirac_eq_selected e m he hm hf hfc hϑ h hb

example (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 2 ϑ)
    (h : ∀ τ, m • deriv (rectilinearVelocity ϑ) τ =
      f τ • rectilinearDirection ϑ τ + lorentzDiracForce e (rectilinearVelocity ϑ) τ)
    (hne : deriv ϑ ≠ selectedAcceleration m (radiationTime e m) f) :
    Tendsto (fun τ => |deriv ϑ τ|) atTop atTop :=
  rectilinear_lorentzDirac_runaway e m he hm hf hfc hϑ h hne

end Rectilinear

end ProjectAinos.Electrodynamics.RadiationReaction

end RadiationSelection
