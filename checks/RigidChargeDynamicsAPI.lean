/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.Electrodynamics.RadiationReaction.EffectiveComparison

/-! Public consumers of the self-consistent motion of a rigid charge in the linear model
(Landau–Lifshitz §75): the theory of linear equations with a distributed delay (estimates,
existence and uniqueness, runaways, the comparison with the reduced equation), the linear
self-force of the retarded field as a convolution of the acceleration over the light time across
the charge, the existence, uniqueness and stability of the motion at a fixed radius, and the
comparison of the motion with the reduced equation of radiation damping. Default elaborator
options are intentional: these checks must not rely on the implementation's transparency
settings. Every statement is pinned with its type. -/

noncomputable section

open MeasureTheory Filter Set Metric Real

open scoped Topology BoundedContinuousFunction

section DistributedDelay

open ProjectAinos.SmoothGeometry.DistributedDelay

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {w τ : Ω → ℝ} {D : ℝ}

example (μ : Measure Ω) (w τ : Ω → ℝ) (D : ℝ) : Prop :=
  DelayData μ w τ D

example (μ : Measure Ω) (w τ : Ω → ℝ) (u : ℝ → E) (t : ℝ) :
    delayOp μ w τ u t = ∫ ω, w ω • u (t - τ ω) ∂μ :=
  rfl

example (μ : Measure Ω) (w τ : Ω → ℝ) (γ : ℝ) :
    weightNorm μ w τ γ = ∫ ω, |w ω| * Real.exp (-(γ * τ ω)) ∂μ :=
  rfl

example (u : ℝ → E) (t : ℝ) :
    doublePrimitive u t = ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, u r :=
  rfl

example (c : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    DelayData (Measure.dirac ()) (fun _ : Unit => c) (fun _ => D) D :=
  delayData_point c hD

example [CompleteSpace E] (c D : ℝ) (u : ℝ → E) (t : ℝ) :
    delayOp (Measure.dirac ()) (fun _ : Unit => c) (fun _ => D) u t = c • u (t - D) :=
  delayOp_point c D u t

example (h : DelayData μ w τ D) : Integrable (fun ω => |w ω|) μ :=
  DelayData.integrable_abs h

example (h : DelayData μ w τ D) {γ : ℝ} (hγ : 0 ≤ γ) :
    Integrable (fun ω => |w ω| * Real.exp (-(γ * τ ω))) μ :=
  DelayData.integrable_mul_exp h hγ

example (μ : Measure Ω) (w τ : Ω → ℝ) (γ : ℝ) : 0 ≤ weightNorm μ w τ γ :=
  DelayData.weightNorm_nonneg μ w τ γ

example (h : DelayData μ w τ D) {γ : ℝ} (hγ : 0 ≤ γ) :
    weightNorm μ w τ γ ≤ ∫ ω, |w ω| ∂μ :=
  DelayData.weightNorm_le h hγ

example (μ : Measure Ω) (w τ : Ω → ℝ) :
    weightNorm μ w τ 0 = ∫ ω, |w ω| ∂μ :=
  DelayData.weightNorm_zero μ w τ

example (h : DelayData μ w τ D) {u : ℝ → E} (hu : Continuous u)
    (t : ℝ) : AEStronglyMeasurable (fun ω => w ω • u (t - τ ω)) μ :=
  DelayData.aestronglyMeasurable_smul h hu t

example (h : DelayData μ w τ D) {u : ℝ → E} {t C : ℝ}
    (hC : ∀ s ∈ Icc (t - D) t, ‖u s‖ ≤ C) (ω : Ω) :
    ‖w ω • u (t - τ ω)‖ ≤ |w ω| * C :=
  DelayData.norm_smul_le h hC ω

example (h : DelayData μ w τ D) {u : ℝ → E} (hu : Continuous u) (t : ℝ) :
    Integrable (fun ω => w ω • u (t - τ ω)) μ :=
  DelayData.integrable_smul h hu t

example (h : DelayData μ w τ D) {u v : ℝ → E} (hu : Continuous u)
    (hv : Continuous v) (t : ℝ) :
    delayOp μ w τ (fun s => u s + v s) t = delayOp μ w τ u t + delayOp μ w τ v t :=
  DelayData.delayOp_add h hu hv t

example (h : DelayData μ w τ D) {u v : ℝ → E} (hu : Continuous u)
    (hv : Continuous v) (t : ℝ) :
    delayOp μ w τ (fun s => u s - v s) t = delayOp μ w τ u t - delayOp μ w τ v t :=
  DelayData.delayOp_sub h hu hv t

example (c : ℝ) (u : ℝ → E) (t : ℝ) :
    delayOp μ w τ (fun s => c • u s) t = c • delayOp μ w τ u t :=
  DelayData.delayOp_smul c u t

example (h : DelayData μ w τ D) {u v : ℝ → E} {t : ℝ}
    (huv : ∀ s ∈ Icc (t - D) t, u s = v s) : delayOp μ w τ u t = delayOp μ w τ v t :=
  DelayData.delayOp_congr h huv

example (h : DelayData μ w τ D) {u : ℝ → E} (hu : Continuous u) :
    Continuous (delayOp μ w τ u) :=
  DelayData.continuous_delayOp h hu

example (h : DelayData μ w τ D) {u : ℝ → E} {T : ℝ}
    (hu : ∀ s ≤ T, u s = 0) {t : ℝ} (ht : t ≤ T) : delayOp μ w τ u t = 0 :=
  DelayData.delayOp_eq_zero_of_le h hu ht

example (h : DelayData μ w τ D) {γ : ℝ} (hγ : 0 ≤ γ) {m₀ : ℝ}
    (hq : weightNorm μ w τ γ < |m₀|) {u : ℝ → E} (hu : Continuous u) {T C H : ℝ}
    (hH : ∀ s ∈ Icc (-D) 0, ‖u s‖ ≤ H)
    (hf : ∀ t ∈ Icc 0 T, ‖m₀ • u t + delayOp μ w τ u t‖ ≤ C * Real.exp (γ * t)) :
    ∀ t ∈ Icc 0 T, ‖u t‖ ≤
      (C + (∫ ω, |w ω| ∂μ) * H) / (|m₀| - weightNorm μ w τ γ) * Real.exp (γ * t) :=
  norm_le_of_delay h hγ hq hu hH hf

example (h : DelayData μ w τ D) {m₀ : ℝ}
    (hq : ∫ ω, |w ω| ∂μ < |m₀|) {u : ℝ → E} {T C B : ℝ} (hB : ∀ s ≤ T, ‖u s‖ ≤ B)
    (hf : ∀ t ≤ T, ‖m₀ • u t + delayOp μ w τ u t‖ ≤ C) :
    ∀ t ≤ T, ‖u t‖ ≤ C / (|m₀| - ∫ ω, |w ω| ∂μ) :=
  norm_le_of_delay_Iic h hq hB hf

example (h : DelayData μ w τ D) (v : ℝ →ᵇ E) (t : ℝ) :
    ‖delayOp μ w τ v t‖ ≤ (∫ ω, |w ω| ∂μ) * ‖v‖ :=
  DelayData.norm_delayOp_le h v t

example [CompleteSpace E] (h : DelayData μ w τ D) {m₀ : ℝ}
    (hq : ∫ ω, |w ω| ∂μ < |m₀|) (f : ℝ →ᵇ E) :
    ∃ u : ℝ →ᵇ E, ∀ t, m₀ • u t + delayOp μ w τ u t = f t :=
  exists_bounded_solution h hq f

example (h : DelayData μ w τ D) {γ : ℝ} (hγ : 0 ≤ γ) :
    DelayData μ (fun ω => w ω * Real.exp (-(γ * τ ω))) τ D :=
  DelayData.weighted h hγ

example (w τ : Ω → ℝ) (γ : ℝ) :
    ∫ ω, |w ω * Real.exp (-(γ * τ ω))| ∂μ = weightNorm μ w τ γ :=
  integral_abs_weighted w τ γ

example (γ : ℝ) (v : ℝ → E) (t : ℝ) :
    delayOp μ w τ (fun s => Real.exp (γ * s) • v s) t =
      Real.exp (γ * t) • delayOp μ (fun ω => w ω * Real.exp (-(γ * τ ω))) τ v t :=
  delayOp_exp_smul γ v t

example [CompleteSpace E] (h : DelayData μ w τ D) {γ : ℝ} (hγ : 0 ≤ γ)
    {m₀ : ℝ} (hq : weightNorm μ w τ γ < |m₀|) {f : ℝ → E} (hf : Continuous f)
    (hf0 : ∀ t ≤ 0, f t = 0) {C : ℝ} (hC : ∀ t, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (γ * t)) :
    ∃ u : ℝ → E, Continuous u ∧ (∀ t ≤ 0, u t = 0) ∧
      (∀ t, m₀ • u t + delayOp μ w τ u t = f t) ∧
      ∀ t, ‖u t‖ ≤ C / (|m₀| - weightNorm μ w τ γ) * Real.exp (γ * t) :=
  exists_solution h hγ hq hf hf0 hC

example (h : DelayData μ w τ D) {γ : ℝ} (hγ : 0 ≤ γ) {m₀ : ℝ}
    (hq : weightNorm μ w τ γ < |m₀|) {u v : ℝ → E} (hu : Continuous u) (hv : Continuous v)
    (h0 : ∀ s ∈ Icc (-D) 0, u s = v s)
    (heq : ∀ t, 0 ≤ t → m₀ • u t + delayOp μ w τ u t = m₀ • v t + delayOp μ w τ v t) :
    ∀ t, 0 ≤ t → u t = v t :=
  eq_of_delay h hγ hq hu hv h0 heq

example (h : DelayData μ w τ D) (hpos : ∀ᵐ ω ∂μ, 0 < τ ω) {m₀ : ℝ}
    (hm₀ : m₀ ≠ 0) (γ₀ : ℝ) : ∃ γ, γ₀ ≤ γ ∧ 0 ≤ γ ∧ weightNorm μ w τ γ < |m₀| :=
  DelayData.exists_weightNorm_lt h hpos hm₀ γ₀

example [CompleteSpace E] (h : DelayData μ w τ D) (hpos : ∀ᵐ ω ∂μ, 0 < τ ω)
    (hw : ∀ ω, 0 ≤ w ω) {m₀ : ℝ} (hm₀ : m₀ < 0) (hm : 0 < m₀ + ∫ ω, w ω ∂μ) :
    ∃ γ, 0 < γ ∧ ∀ (c : E) (t : ℝ),
      m₀ • (Real.exp (γ * t) • c) + delayOp μ w τ (fun s => Real.exp (γ * s) • c) t = 0 :=
  exists_runaway h hpos hw hm₀ hm

example {g : ℝ → E} (hg : Continuous g) (h0 : ∀ t < 0, g t = 0) :
    ∀ t ≤ 0, g t = 0 :=
  eq_zero_of_lt_zero hg h0

example {F : ℝ → E} (hF0 : ∀ t ≤ 0, F t = 0) {t : ℝ} (ht : t < 0) :
    deriv F t = 0 :=
  deriv_eq_zero_of_lt_zero hF0 ht

example {a a' a'' : ℝ → E} (ha : ∀ s, HasDerivAt a (a' s) s)
    (ha' : ∀ s, HasDerivAt a' (a'' s) s) {B : ℝ} (hB : ∀ s, ‖a'' s‖ ≤ B) (t : ℝ) {σ : ℝ}
    (hσ : 0 ≤ σ) : ‖a (t - σ) - a t + σ • a' t‖ ≤ B * σ ^ 2 / 2 :=
  norm_taylor_two_le ha ha' hB t hσ

example (h : DelayData μ w τ D) :
    Integrable (fun ω => w ω * τ ω) μ :=
  DelayData.integrable_mul_delay h

example (h : DelayData μ w τ D) :
    Integrable (fun ω => |w ω| * τ ω ^ 2) μ :=
  DelayData.integrable_mul_delay_sq h

example [CompleteSpace E] (h : DelayData μ w τ D) {m₀ : ℝ}
    (hq : ∫ ω, |w ω| ∂μ < |m₀|) {m M₁ Q₂ : ℝ} (hm : m = m₀ + ∫ ω, w ω ∂μ) (hm0 : m ≠ 0)
    (hM₁ : M₁ = ∫ ω, w ω * τ ω ∂μ) (hQ₂ : Q₂ = ∫ ω, |w ω| * τ ω ^ 2 ∂μ) {F : ℝ → E}
    (hF : ContDiff ℝ 3 F) (hF0 : ∀ t ≤ 0, F t = 0) {B₂ B₃ : ℝ}
    (hB₂ : ∀ t, ‖deriv (deriv F) t‖ ≤ B₂) (hB₃ : ∀ t, ‖deriv (deriv (deriv F)) t‖ ≤ B₃)
    {u : ℝ → E} (hu : Continuous u) (hu0 : ∀ t ≤ 0, u t = 0)
    (hsol : ∀ t, 0 ≤ t → m₀ • u t + delayOp μ w τ u t = F t) (t : ℝ) :
    ‖u t - (m⁻¹ • F t + (M₁ / m ^ 2) • deriv F t)‖ ≤
      ((M₁ / m) ^ 2 * B₂ + Q₂ / 2 * (B₂ / |m| + |M₁| * B₃ / m ^ 2)) /
        (|m₀| - ∫ ω, |w ω| ∂μ) :=
  norm_sub_reduced_le h hq hm hm0 hM₁ hQ₂ hF hF0 hB₂ hB₃ hu hu0 hsol t

section Complete

variable [CompleteSpace E]

example {u : ℝ → E} (hu : Continuous u) :
    Continuous fun s => ∫ r in (0 : ℝ)..s, u r :=
  continuous_primitive_zero hu

example {u : ℝ → E} (hu : Continuous u) (t : ℝ) :
    HasDerivAt (doublePrimitive u) (∫ r in (0 : ℝ)..t, u r) t :=
  hasDerivAt_doublePrimitive hu t

example {u : ℝ → E} (hu : Continuous u) :
    deriv (doublePrimitive u) = fun t => ∫ r in (0 : ℝ)..t, u r :=
  deriv_doublePrimitive hu

example {u : ℝ → E} (hu : Continuous u) (t : ℝ) :
    deriv (deriv (doublePrimitive u)) t = u t :=
  deriv_deriv_doublePrimitive hu t

example {u : ℝ → E} (hu : Continuous u) :
    ContDiff ℝ 2 (doublePrimitive u) :=
  contDiff_doublePrimitive hu

end Complete

example {u : ℝ → E} (hu0 : ∀ t ≤ 0, u t = 0) {s : ℝ} (hs : s ≤ 0) :
    ∫ r in (0 : ℝ)..s, u r = 0 :=
  integral_eq_zero_of_le hu0 hs

example {u : ℝ → E} (hu0 : ∀ t ≤ 0, u t = 0) {t : ℝ}
    (ht : t ≤ 0) : doublePrimitive u t = 0 :=
  doublePrimitive_eq_zero_of_le hu0 ht

example {w τ : Ω → ℝ} {D : ℝ} (h : DelayData μ w τ D)
    {u : ℝ → E} {B : ℝ} (hu : ∀ s, ‖u s‖ ≤ B) (t : ℝ) :
    ‖delayOp μ w τ u t‖ ≤ (∫ ω, |w ω| ∂μ) * B :=
  DelayData.norm_delayOp_le_of_bound h hu t

example {f g : ℝ → E} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (t : ℝ) :
    deriv (deriv fun s => f s + g s) t = deriv (deriv f) t + deriv (deriv g) t :=
  deriv_deriv_add hf hg t

example {g : ℝ → E} (hg : ContDiff ℝ 2 g)
    (hdd : ∀ t, deriv (deriv g) t = 0) (h0 : ∀ t ≤ 0, g t = 0) (t : ℝ) : g t = 0 :=
  eq_zero_of_deriv_deriv_eq_zero hg hdd h0 t

example {f g : ℝ → E} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfg : ∀ t ≤ 0, f t = g t) : ∀ t ≤ 0, deriv (deriv f) t = deriv (deriv g) t :=
  deriv_deriv_eq_of_eq_on_Iic hf hg hfg

example {w τ : Ω → ℝ} {D : ℝ} (h : DelayData μ w τ D) :
    ∫ ω, |w ω| * τ ω ^ 2 ∂μ ≤ D * ∫ ω, |w ω| * τ ω ∂μ :=
  DelayData.integral_abs_mul_sq_le h

example {g : ℝ → E} (hg : ContDiff ℝ 2 g) (h0 : ∀ t ≤ 0, g t = 0)
    {C : ℝ} (hC : ∀ t, ‖deriv (deriv g) t‖ ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    ‖deriv g t‖ ≤ C * t ∧ ‖g t‖ ≤ C * t ^ 2 / 2 :=
  norm_le_of_deriv_deriv_le hg h0 hC ht

example {f : ℝ → E} (hf : Differentiable ℝ f) (c κ : ℝ) :
    deriv (fun t => c • f (κ * t)) = fun t => (c * κ) • deriv f (κ * t) :=
  deriv_smul_comp_mul hf c κ

end DistributedDelay

namespace ProjectAinos.Electrodynamics.RadiationReaction

open scoped ContDiff

open SmoothGeometry SmoothGeometry.Wave SpecialRelativity SmoothGeometry.DistributedDelay

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section RigidChargeDynamics

variable {e : ℝ} {η : E3 → ℝ} {R : ℝ → E3}

example (η : E3 → ℝ) (k : Fin 3) (z : E3) :
    profileDeriv η k z = fderiv ℝ η z (EuclideanSpace.single k 1) :=
  rfl

example (η : E3 → ℝ) (i k : Fin 3) (z : E3) :
    profileDeriv2 η i k z = fderiv ℝ (profileDeriv η k) z (EuclideanSpace.single i 1) :=
  rfl

example (e : ℝ) (η : E3 → ℝ) (p : ℝ × E3) : restCharge e η p = e * η p.2 :=
  rfl

example (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (p : ℝ × E3) :
    linearCharge e η R p = -(e * fderiv ℝ η p.2 (R p.1)) :=
  rfl

example (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (k : Fin 3) (p : ℝ × E3) :
    linearCurrent e η R k p = e * deriv R p.1 k * η p.2 :=
  rfl

example (e : ℝ) (η : E3 → ℝ) (i : Fin 3) :
    restField e η i = electricOf (retardedIntegral (restCharge e η)) (fun _ _ => 0) i :=
  rfl

example (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (i : Fin 3) :
    linearField e η R i = electricOf (retardedIntegral (linearCharge e η R))
      (fun k => retardedIntegral (linearCurrent e η R k)) i :=
  rfl

example (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (t : ℝ) (i : Fin 3) :
    linearSelfForce e η R t i =
      (∫ x, restCharge e η (t, x) * linearField e η R i (t, x)) +
        ∫ x, linearCharge e η R (t, x) * restField e η i (t, x) :=
  rfl

example (e : ℝ) (η : E3 → ℝ) (p : E3 × E3) :
    selfWeight e η p = 2 / 3 * e ^ 2 * (η p.1 * η (p.1 - p.2)) * Potential.newtonKernel p.2 :=
  rfl

example (p : E3 × E3) : selfDelay p = ‖p.2‖ :=
  rfl

example (hη : ContDiff ℝ 2 η) (k : Fin 3) :
    ContDiff ℝ 1 (profileDeriv η k) :=
  contDiff_profileDeriv hη k

example (hη : ContDiff ℝ 2 η) (i k : Fin 3) :
    Continuous (profileDeriv2 η i k) :=
  continuous_profileDeriv2 hη i k

example {G : E3 → ℝ} {b : ℝ} (hG : ∀ z : E3, b < ‖z‖ → G z = 0) {z : E3}
    (hz : b < ‖z‖) : fderiv ℝ G z = 0 :=
  fderiv_eq_zero_of_far hG hz

example {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (k : Fin 3) {z : E3}
    (hz : b < ‖z‖) : profileDeriv η k z = 0 :=
  profileDeriv_eq_zero hb k hz

example {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (i k : Fin 3) {z : E3}
    (hz : b < ‖z‖) : profileDeriv2 η i k z = 0 :=
  profileDeriv2_eq_zero hb i k hz

example (hη : ContDiff ℝ 2 η) (k : Fin 3) (z v : E3) :
    fderiv ℝ (profileDeriv η k) z v = fderiv ℝ (fderiv ℝ η) z v (EuclideanSpace.single k 1) :=
  fderiv_profileDeriv_apply hη k z v

example (hη : ContDiff ℝ 2 η) (i k : Fin 3) (z : E3) :
    profileDeriv2 η i k z = profileDeriv2 η k i z :=
  profileDeriv2_comm hη i k z

example (L : E3 ≃ₗᵢ[ℝ] E3) {φ : E3 → ℝ} {z : E3}
    (hφ : DifferentiableAt ℝ φ (L z)) (v : E3) :
    fderiv ℝ (fun y => φ (L y)) z v = fderiv ℝ φ (L z) (L v) :=
  fderiv_comp_isometry L hφ v

example (L : E3 ≃ₗᵢ[ℝ] E3) (hrot : ∀ x, η (L x) = η x)
    (hη : Differentiable ℝ η) (z u : E3) : fderiv ℝ η z u = fderiv ℝ η (L z) (L u) :=
  fderiv_apply_of_invariant L hrot hη z u

example (L : E3 ≃ₗᵢ[ℝ] E3) (hrot : ∀ x, η (L x) = η x)
    (hη : ContDiff ℝ 2 η) (z u v : E3) :
    fderiv ℝ (fun y => fderiv ℝ η y u) z v =
      fderiv ℝ (fun y => fderiv ℝ η y (L u)) (L z) (L v) :=
  fderiv_fderiv_apply_of_invariant L hrot hη z u v

example (i : Fin 3) :
    coordReflection i (EuclideanSpace.single i 1) = -EuclideanSpace.single i 1 :=
  coordReflection_single_self i

example {i k : Fin 3} (hik : i ≠ k) :
    coordReflection i (EuclideanSpace.single k 1) = EuclideanSpace.single k 1 :=
  coordReflection_single_of_ne hik

example (i k : Fin 3) :
    coordSwap i k (EuclideanSpace.single k 1) = EuclideanSpace.single i 1 :=
  coordSwap_single i k

example {i k : Fin 3} (hik : i ≠ k)
    (hrot : ∀ x, η (coordReflection i x) = η x) (hη : ContDiff ℝ 2 η) (z : E3) :
    profileDeriv2 η i k (coordReflection i z) = -profileDeriv2 η i k z :=
  profileDeriv2_coordReflection hik hrot hη z

example (i k : Fin 3) (hrot : ∀ x, η (coordSwap i k x) = η x)
    (hη : ContDiff ℝ 2 η) (z : E3) :
    profileDeriv2 η i i (coordSwap i k z) = profileDeriv2 η k k z :=
  profileDeriv2_coordSwap i k hrot hη z

example (L : E3 ≃ₗᵢ[ℝ] E3) (hrot : ∀ x, η (L x) = η x)
    {K : E3 → ℝ} (hK : ∀ y, K (L y) = K y) (D : E3 → ℝ) :
    ∫ x, η x * ∫ y, K y * D (x - y) = ∫ x, η x * ∫ y, K y * D (L (x - y)) :=
  integral_mul_kernel_sub_comp L hrot hK D

example
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (hη : ContDiff ℝ 2 η)
    {K : E3 → ℝ} (hK : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (y : E3), K (f y) = K y) {i k : Fin 3}
    (hik : i ≠ k) : ∫ x, η x * ∫ y, K y * profileDeriv2 η i k (x - y) = 0 :=
  integral_mul_profileDeriv2_eq_zero hrot hη hK hik

example
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (hη : ContDiff ℝ 2 η)
    {K : E3 → ℝ} (hK : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (y : E3), K (f y) = K y) (i k : Fin 3) :
    ∫ x, η x * ∫ y, K y * profileDeriv2 η i i (x - y) =
      ∫ x, η x * ∫ y, K y * profileDeriv2 η k k (x - y) :=
  integral_mul_profileDeriv2_diag hrot hη hK i k

example (e : ℝ) (η : E3 → ℝ) :
    rigidCharge e η (fun _ => 0) = restCharge e η :=
  rigidCharge_zero e η

example (hη : Differentiable ℝ η) (R : ℝ → E3) (p : ℝ × E3) :
    HasDerivAt (fun ε : ℝ => rigidCharge e η (fun s => ε • R s) p) (linearCharge e η R p) 0 :=
  hasDerivAt_rigidCharge_smul hη R p

example (hη : Differentiable ℝ η) (hR : Differentiable ℝ R)
    (k : Fin 3) (p : ℝ × E3) :
    HasDerivAt (fun ε : ℝ => rigidCurrent e η (fun s => ε • R s) k p)
      (linearCurrent e η R k p) 0 :=
  hasDerivAt_rigidCurrent_smul hη hR k p

example {b : ℝ} (c : ℝ → ℝ) {G : E3 → ℝ}
    (hG : ∀ z : E3, b < ‖z‖ → G z = 0) : SpatialSupport b (fun p : ℝ × E3 => c p.1 * G p.2) :=
  spatialSupport_slice c hG

example {b : ℝ} {G : E3 → ℝ} (hG : ∀ z : E3, b < ‖z‖ → G z = 0) :
    SpatialSupport b (fun p : ℝ × E3 => G p.2) :=
  spatialSupport_static hG

example {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) :
    SpatialSupport b (restCharge e η) :=
  spatialSupport_restCharge hb

example {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) :
    SpatialSupport b (linearCharge e η R) :=
  spatialSupport_linearCharge hb

example {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (k : Fin 3) :
    SpatialSupport b (linearCurrent e η R k) :=
  spatialSupport_linearCurrent hb k

example {n : ℕ∞} {c : ℝ → ℝ} {G : E3 → ℝ} (hc : ContDiff ℝ n c)
    (hG : ContDiff ℝ n G) : ContDiff ℝ n (fun p : ℝ × E3 => c p.1 * G p.2) :=
  contDiff_mul_slice hc hG

example (hη : ContDiff ℝ 2 η) (hR : ContDiff ℝ 2 R) :
    ContDiff ℝ 1 (linearCharge e η R) :=
  contDiff_linearCharge hη hR

example (hR : ContDiff ℝ 2 R) : ContDiff ℝ 1 (deriv R) :=
  contDiff_deriv_path hR

example (hη : ContDiff ℝ 2 η) (hR : ContDiff ℝ 2 R) (k : Fin 3) :
    ContDiff ℝ 1 (linearCurrent e η R k) :=
  contDiff_linearCurrent hη hR k

example (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) :
    linearCharge e η R = fun p => ∑ k, R p.1 k * (-(e * profileDeriv η k p.2)) :=
  linearCharge_eq_sum e η R

example (hη : ContDiff ℝ 2 η) (e : ℝ) (i k : Fin 3)
    (z : E3) :
    fderiv ℝ (fun z => -(e * profileDeriv η k z)) z (EuclideanSpace.single i 1) =
      -(e * profileDeriv2 η i k z) :=
  fderiv_neg_const_mul_profileDeriv hη e i k z

example (hη : ContDiff ℝ 2 η) (hR : ContDiff ℝ 2 R) (i : Fin 3)
    (p : ℝ × E3) :
    spaceDeriv i (linearCharge e η R) p =
      ∑ k, R p.1 k * (-(e * profileDeriv2 η i k p.2)) :=
  spaceDeriv_linearCharge hη hR i p

example (hη : ContDiff ℝ 2 η) (hR : ContDiff ℝ 2 R) (i : Fin 3) :
    timeDeriv (linearCurrent e η R i) = fun p => e * deriv (deriv R) p.1 i * η p.2 :=
  timeDeriv_linearCurrent hη hR i

example (hη : ContDiff ℝ 2 η) (i : Fin 3) :
    spaceDeriv i (restCharge e η) = fun p => e * profileDeriv η i p.2 :=
  spaceDeriv_restCharge hη i

example (hη : ContDiff ℝ 2 η) (i k : Fin 3) :
    spaceDeriv k (fun p : ℝ × E3 => e * profileDeriv η i p.2) =
      fun p => e * profileDeriv2 η k i p.2 :=
  spaceDeriv_static_profileDeriv hη i k

example (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    retardedIntegral (fun q => -f q) p = -retardedIntegral f p :=
  retardedIntegral_neg' f p

example {b : ℝ} {f g : ℝ × E3 → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfs : SpatialSupport b f) (hgs : SpatialSupport b g) (p : ℝ × E3) :
    retardedIntegral (fun q => f q - g q) p = retardedIntegral f p - retardedIntegral g p :=
  retardedIntegral_sub' hf hg hfs hgs p

example {b : ℝ} {f : Fin 3 → ℝ × E3 → ℝ} (hf : ∀ k, Continuous (f k))
    (hfs : ∀ k, SpatialSupport b (f k)) (p : ℝ × E3) :
    retardedIntegral (fun q => ∑ k, f k q) p = ∑ k, retardedIntegral (f k) p :=
  retardedIntegral_sum' hf hfs p

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hR : ContDiff ℝ 2 R) (i : Fin 3) (p : ℝ × E3) :
    linearField e η R i p =
      ∑ k, retardedIntegral (fun q => R q.1 k * (e * profileDeriv2 η i k q.2)) p -
        retardedIntegral (fun q => deriv (deriv R) q.1 i * (e * η q.2)) p :=
  linearField_eq hη hb hR i p

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (i : Fin 3) (p : ℝ × E3) :
    restField e η i p = -retardedIntegral (fun q => e * profileDeriv η i q.2) p :=
  restField_eq hη hb i p

example (hη : ContDiff ℝ 2 η) (hR : ContDiff ℝ 2 R) (p : ℝ × E3) :
    timeDeriv (linearCharge e η R) p + ∑ k, spaceDeriv k (linearCurrent e η R k) p = 0 :=
  continuity_linear hη hR p

example {G : E3 → ℝ} {b : ℝ} (hG : ∀ z : E3, b < ‖z‖ → G z = 0) :
    HasCompactSupport G :=
  hasCompactSupport_of_far hG

example {G : E3 → ℝ} (hG : Continuous G) {b : ℝ}
    (hGb : ∀ z : E3, b < ‖z‖ → G z = 0) {g : ℝ × E3 → ℝ} (hg : Continuous g) (t : ℝ) :
    Integrable fun x => G x * g (t, x) :=
  integrable_profile_mul hG hGb hg t

example {b : ℝ} {c : ℝ → ℝ} {G : E3 → ℝ} (hc : Continuous c)
    (hG : Continuous G) (hGb : ∀ z : E3, b < ‖z‖ → G z = 0) :
    Continuous (retardedIntegral fun q : ℝ × E3 => c q.1 * G q.2) :=
  continuous_retardedIntegral_slice hc hG hGb

example (hη : ContDiff ℝ 2 η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {Φ : ℝ × E3 → ℝ} (hΦ : ContDiff ℝ 1 Φ) (t : ℝ)
    (k : Fin 3) :
    ∫ x, e * profileDeriv η k x * Φ (t, x) = -∫ x, e * η x * spaceDeriv k Φ (t, x) :=
  integral_profileDeriv_mul hη hb hΦ t k

example (hη : ContDiff ℝ 2 η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hR : ContDiff ℝ 2 R) (t : ℝ) (i : Fin 3) :
    linearSelfForce e η R t i =
      ∑ k, (∫ x, e * η x *
        retardedIntegral (fun q => (R q.1 k - R t k) * (e * profileDeriv2 η i k q.2)) (t, x)) -
      ∫ x, e * η x * retardedIntegral (fun q => deriv (deriv R) q.1 i * (e * η q.2)) (t, x) :=
  linearSelfForce_eq_sum hη hb hR t i

example (hη : ContDiff ℝ 2 η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) {t : ℝ}
    (ht : h t = 0) (x : E3) :
    ∑ j, retardedIntegral (fun q => h q.1 * profileDeriv2 η j j q.2) (t, x) =
      retardedIntegral (fun q => deriv (deriv h) q.1 * η q.2) (t, x) :=
  sum_retardedIntegral_profileDeriv2 hη hb hh ht x

example (e : ℝ) (η : E3 → ℝ) (g : ℝ → ℝ) (G : E3 → ℝ)
    (t : ℝ) :
    ∫ x, e * η x * retardedIntegral (fun q => g q.1 * (e * G q.2)) (t, x) =
      e ^ 2 * ∫ x, η x * ∫ y, g (t - ‖y‖) / (4 * π * ‖y‖) * G (x - y) :=
  integral_mul_retardedIntegral_slice e η g G t

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (hR : ContDiff ℝ 2 R) (t : ℝ)
    (i : Fin 3) :
    linearSelfForce e η R t i =
      -(2 / 3) * ∫ x, e * η x *
        retardedIntegral (fun q => deriv (deriv R) q.1 i * (e * η q.2)) (t, x) :=
  linearSelfForce_eq hη hb hrot hR t i

example : Measurable Potential.newtonKernel :=
  measurable_newtonKernel

example {b : ℝ} (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {p : E3 × E3}
    (hp : selfWeight e η p ≠ 0) : ‖p.2‖ ≤ 2 * b :=
  selfWeight_eq_zero_of_far hb hp

example (hη : Continuous η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) :
    DelayData (volume : Measure (E3 × E3)) (selfWeight e η) selfDelay (2 * b) :=
  selfDelayData hη hb0 hb

example : ∀ᵐ p ∂(volume : Measure (E3 × E3)), 0 < selfDelay p :=
  ae_selfDelay_pos

example (hη0 : ∀ z, 0 ≤ η z) (p : E3 × E3) : 0 ≤ selfWeight e η p :=
  selfWeight_nonneg hη0 p

example (hη : Continuous η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {g : E3 → ℝ} (hg : Continuous g) :
    ∫ p, selfWeight e η p * g p.2 =
      2 / 3 * e ^ 2 * ∫ x, η x * ∫ y, Potential.newtonKernel y * g y * η (x - y) :=
  integral_selfWeight_mul hη hb0 hb hg

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    (hR : ContDiff ℝ 2 R) (t : ℝ) (i : Fin 3) :
    linearSelfForce e η R t i = -∫ p, selfWeight e η p * deriv (deriv R) (t - ‖p.2‖) i :=
  linearSelfForce_eq_integral hη hb0 hb hrot hR t i

example (hR : ContDiff ℝ 2 R) : Continuous (deriv (deriv R)) :=
  continuous_deriv_deriv hR

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    (hR : ContDiff ℝ 2 R) (t : ℝ) (i : Fin 3) :
    linearSelfForce e η R t i =
      -(delayOp volume (selfWeight e η) selfDelay (deriv (deriv R)) t) i :=
  linearSelfForce_eq_delayOp hη hb0 hb hrot hR t i

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {R₁ R₂ : ℝ → E3} (h₁ : ContDiff ℝ 2 R₁) (h₂ : ContDiff ℝ 2 R₂) {t : ℝ}
    (h : ∀ s ∈ Icc (t - 2 * b) t, deriv (deriv R₁) s = deriv (deriv R₂) s) (i : Fin 3) :
    linearSelfForce e η R₁ t i = linearSelfForce e η R₂ t i :=
  linearSelfForce_congr hη hb0 hb hrot h₁ h₂ h i

example (hη : Continuous η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) :
    ∫ p, selfWeight e η p = 4 / 3 * selfEnergy e η :=
  integral_selfWeight hη hb0 hb

example (hη : Continuous η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) :
    ∫ p, selfWeight e η p * selfDelay p = 2 / 3 * (e ^ 2 / (4 * π)) * (∫ z, η z) ^ 2 :=
  integral_selfWeight_mul_delay hη hb0 hb

example (hη : ContDiff ℝ 2 η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    (R₀ V : E3) (t : ℝ) (i : Fin 3) :
    linearSelfForce e η (fun s => R₀ + s • V) t i = 0 :=
  linearSelfForce_inertial hη hb hrot R₀ V t i

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 < b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {R₁ R₂ : ℝ → E3} (h₁ : ContDiff ℝ 2 R₁) (h₂ : ContDiff ℝ 2 R₂) {t : ℝ}
    (h : ∀ s ∈ Icc (t - 2 * b) t, R₁ s = R₂ s) (i : Fin 3) :
    linearSelfForce e η R₁ t i = linearSelfForce e η R₂ t i :=
  linearSelfForce_congr_path hη hb0 hb hrot h₁ h₂ h i

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {R : ℝ → E3} (hR : ContDiff ℝ 2 R) (m₀ : ℝ) (F : ℝ → E3) (t : ℝ) :
    (∀ i, m₀ * deriv (deriv R) t i = F t i + linearSelfForce e η R t i) ↔
      m₀ • deriv (deriv R) t +
        delayOp volume (selfWeight e η) selfDelay (deriv (deriv R)) t = F t :=
  linearMotion_iff hη hb0 hb hrot hR m₀ F t

example (hη : ContDiff ℝ 2 η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    (m₀ : ℝ) (R₀ V : E3) (t : ℝ) (i : Fin 3) :
    m₀ * deriv (deriv fun s : ℝ => R₀ + s • V) t i =
      (fun _ : ℝ => (0 : E3)) t i + linearSelfForce e η (fun s => R₀ + s • V) t i :=
  linearMotion_inertial hη hb hrot m₀ R₀ V t i

example {h u : ℝ → E3} (hh : ContDiff ℝ 2 h)
    (hu : Continuous u) :
    deriv (deriv fun s => h s + doublePrimitive u s) = fun s => deriv (deriv h) s + u s :=
  deriv_deriv_add_doublePrimitive hh hu

example (hη : Continuous η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {m₀ : ℝ} {F h u : ℝ → E3} (hh : ContDiff ℝ 2 h)
    (hu : Continuous u) {t : ℝ}
    (hut : m₀ • u t + delayOp volume (selfWeight e η) selfDelay u t =
      F t - m₀ • deriv (deriv h) t -
        delayOp volume (selfWeight e η) selfDelay (deriv (deriv h)) t) :
    m₀ • deriv (deriv fun s => h s + doublePrimitive u s) t +
      delayOp volume (selfWeight e η) selfDelay
        (deriv (deriv fun s => h s + doublePrimitive u s)) t = F t :=
  delayEq_add_doublePrimitive hη hb0 hb hh hu hut

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {m₀ γ : ℝ} (hγ : 0 ≤ γ) (hq : weightNorm volume (selfWeight e η) selfDelay γ < |m₀|)
    {F : ℝ → E3} (hF : Continuous F) {CF : ℝ}
    (hCF : ∀ t, 0 ≤ t → ‖F t‖ ≤ CF * Real.exp (γ * t)) {h : ℝ → E3} (hh : ContDiff ℝ 2 h)
    {H : ℝ} (hH : ∀ t, ‖deriv (deriv h) t‖ ≤ H)
    (hcompat : ∀ i, m₀ * deriv (deriv h) 0 i = F 0 i + linearSelfForce e η h 0 i) :
    ∃ R : ℝ → E3, ContDiff ℝ 2 R ∧ (∀ t ≤ 0, R t = h t) ∧
      (∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R) t i = F t i + linearSelfForce e η R t i) ∧
      ∀ t, ‖deriv (deriv R) t - deriv (deriv h) t‖ ≤
        (CF + (|m₀| + ∫ p, |selfWeight e η p|) * H) /
          (|m₀| - weightNorm volume (selfWeight e η) selfDelay γ) * Real.exp (γ * t) :=
  exists_linearMotion hη hb0 hb hrot hγ hq hF hCF hh hH hcompat

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {m₀ γ : ℝ} (hγ : 0 ≤ γ) (hq : weightNorm volume (selfWeight e η) selfDelay γ < |m₀|)
    {F R₁ R₂ : ℝ → E3} (h₁ : ContDiff ℝ 2 R₁) (h₂ : ContDiff ℝ 2 R₂)
    (hpast : ∀ t ≤ 0, R₁ t = R₂ t)
    (hm₁ : ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R₁) t i = F t i + linearSelfForce e η R₁ t i)
    (hm₂ : ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R₂) t i = F t i + linearSelfForce e η R₂ t i) :
    R₁ = R₂ :=
  linearMotion_unique hη hb0 hb hrot hγ hq h₁ h₂ hpast hm₁ hm₂

example {g : ℝ → E3} (hg : ∀ s, HasDerivAt g (deriv g s) s)
    (h0 : ∀ s, 0 ≤ s → deriv g s = 0) {t : ℝ} (ht : 0 ≤ t) : g t = g 0 :=
  eq_of_deriv_eq_zero_Ici hg h0 ht

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 < b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {m₀ γ : ℝ} (hγ : 0 ≤ γ) (hq : weightNorm volume (selfWeight e η) selfDelay γ < |m₀|)
    {F R₁ R₂ : ℝ → E3} (h₁ : ContDiff ℝ 2 R₁) (h₂ : ContDiff ℝ 2 R₂)
    (hpast : ∀ t ∈ Icc (-(2 * b)) 0, R₁ t = R₂ t)
    (hm₁ : ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R₁) t i = F t i + linearSelfForce e η R₁ t i)
    (hm₂ : ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R₂) t i = F t i + linearSelfForce e η R₂ t i) :
    ∀ t, 0 ≤ t → R₁ t = R₂ t :=
  linearMotion_unique_of_Icc hη hb0 hb hrot hγ hq h₁ h₂ hpast hm₁ hm₂

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {m₀ γ : ℝ} (hγ : 0 ≤ γ) (hq : weightNorm volume (selfWeight e η) selfDelay γ < |m₀|)
    {F : ℝ → E3} (hF : Continuous F) {CF : ℝ}
    (hCF : ∀ t, 0 ≤ t → ‖F t‖ ≤ CF * Real.exp (γ * t)) {h : ℝ → E3} (hh : ContDiff ℝ 2 h)
    {H : ℝ} (hH : ∀ t, ‖deriv (deriv h) t‖ ≤ H)
    (hcompat : ∀ i, m₀ * deriv (deriv h) 0 i = F 0 i + linearSelfForce e η h 0 i) :
    ∃! R : ℝ → E3, ContDiff ℝ 2 R ∧ (∀ t ≤ 0, R t = h t) ∧
      ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R) t i = F t i + linearSelfForce e η R t i :=
  existsUnique_linearMotion hη hb0 hb hrot hγ hq hF hCF hh hH hcompat

example (hη : ContDiff ℝ 2 η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {m₀ γ : ℝ} (hγ : 0 ≤ γ) (hq : weightNorm volume (selfWeight e η) selfDelay γ < |m₀|)
    {F₁ F₂ R₁ R₂ : ℝ → E3} (h₁ : ContDiff ℝ 2 R₁) (h₂ : ContDiff ℝ 2 R₂)
    (hm₁ : ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R₁) t i = F₁ t i + linearSelfForce e η R₁ t i)
    (hm₂ : ∀ t, 0 ≤ t → ∀ i, m₀ * deriv (deriv R₂) t i = F₂ t i + linearSelfForce e η R₂ t i)
    {T C H : ℝ} (hF : ∀ t ∈ Icc 0 T, ‖F₁ t - F₂ t‖ ≤ C * Real.exp (γ * t))
    (hH : ∀ s ∈ Icc (-(2 * b)) 0, ‖deriv (deriv R₁) s - deriv (deriv R₂) s‖ ≤ H) :
    ∀ t ∈ Icc 0 T, ‖deriv (deriv R₁) t - deriv (deriv R₂) t‖ ≤
      (C + (∫ p, |selfWeight e η p|) * H) /
        (|m₀| - weightNorm volume (selfWeight e η) selfDelay γ) * Real.exp (γ * t) :=
  norm_sub_le_linearMotion hη hb0 hb hrot hγ hq h₁ h₂ hm₁ hm₂ hF hH

example (hη : Continuous η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {m₀ : ℝ} (hm₀ : m₀ ≠ 0) (γ₀ : ℝ) :
    ∃ γ, γ₀ ≤ γ ∧ 0 ≤ γ ∧ weightNorm volume (selfWeight e η) selfDelay γ < |m₀| :=
  exists_rate_selfWeight hη hb0 hb hm₀ γ₀

example (hη : Continuous η) (hη0 : ∀ z, 0 ≤ η z) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) :
    ∫ p, |selfWeight e η p| = 4 / 3 * selfEnergy e η :=
  integral_abs_selfWeight hη hη0 hb0 hb

example (hη : Continuous η) (hη0 : ∀ z, 0 ≤ η z)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {a : ℝ} (ha : 0 < a) :
    ∫ p, |selfWeight e (scaledProfile a η) p| = 4 / 3 * selfEnergy e η / a :=
  integral_abs_selfWeight_scaledProfile hη hη0 hb0 hb ha

example (hη : ContDiff ℝ 2 η) (hη0 : ∀ z, 0 ≤ η z) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) {m₀ : ℝ} (hm₀ : m₀ < 0)
    (hm : 0 < m₀ + 4 / 3 * selfEnergy e η) :
    ∃ γ, 0 < γ ∧ ∀ (c : E3) (t : ℝ) (i : Fin 3),
      m₀ * deriv (deriv fun s => Real.exp (γ * s) • c) t i =
        linearSelfForce e η (fun s => Real.exp (γ * s) • c) t i :=
  exists_runaway_linearMotion hη hη0 hb0 hb hrot hm₀ hm

end RigidChargeDynamics

section EffectiveComparison

variable {e m : ℝ} {η : E3 → ℝ} {F f : ℝ → E3}

example (e m : ℝ) (F : ℝ → E3) (t : ℝ) :
    effectiveAcceleration e m F t =
      m⁻¹ • F t + (2 / 3 * (e ^ 2 / (4 * π)) / m ^ 2) • deriv F t :=
  rfl

example (e m : ℝ) (F : ℝ → E3) (R₀ V : E3) (t : ℝ) :
    effectivePath e m F R₀ V t = R₀ + t • V + doublePrimitive (effectiveAcceleration e m F) t :=
  rfl

example (s : ℝ) : pulseForce s = pulse (s - 2) • EuclideanSpace.single 0 1 :=
  rfl

example (hF : ContDiff ℝ 1 F) :
    Continuous (effectiveAcceleration e m F) :=
  continuous_effectiveAcceleration hF

example (R₀ V : E3) : ContDiff ℝ 2 fun t : ℝ => R₀ + t • V :=
  contDiff_inertial R₀ V

example (R₀ V : E3) : deriv (fun t : ℝ => R₀ + t • V) = fun _ => V :=
  deriv_inertial R₀ V

example (R₀ V : E3) (t : ℝ) :
    deriv (deriv fun t : ℝ => R₀ + t • V) t = 0 :=
  deriv_deriv_inertial R₀ V t

example (hF : ContDiff ℝ 1 F) (R₀ V : E3) :
    ContDiff ℝ 2 (effectivePath e m F R₀ V) :=
  contDiff_effectivePath hF R₀ V

example (hF : ContDiff ℝ 1 F) (R₀ V : E3) (t : ℝ) :
    deriv (deriv (effectivePath e m F R₀ V)) t = effectiveAcceleration e m F t :=
  deriv_deriv_effectivePath hF R₀ V t

example (hm : m ≠ 0) (hF : ContDiff ℝ 1 F) (R₀ V : E3) (t : ℝ) :
    m • deriv (deriv (effectivePath e m F R₀ V)) t =
      F t + (2 / 3 * (e ^ 2 / (4 * π)) / m) • deriv F t :=
  effectivePath_reduced hm hF R₀ V t

example (hF : ContDiff ℝ 1 F) (R₀ V : E3) (t : ℝ) :
    deriv (deriv (effectivePath e m F R₀ V)) t - m⁻¹ • F t =
      (2 / 3 * (e ^ 2 / (4 * π)) / m ^ 2) • deriv F t :=
  deriv_deriv_effectivePath_sub hF R₀ V t

example (hF : ContDiff ℝ 1 F) (hF0 : ∀ t ≤ 0, F t = 0) (R₀ V : E3)
    {t : ℝ} (ht : t ≤ 0) : effectivePath e m F R₀ V t = R₀ + t • V :=
  effectivePath_of_nonpos hF hF0 R₀ V ht

example {n : ℕ∞} (hf : ContDiff ℝ n f) (κ : ℝ) :
    ContDiff ℝ n fun t => κ ^ 2 • f (κ * t) :=
  contDiff_slowForce hf κ

example (hf : ContDiff ℝ 3 f) (κ : ℝ) :
    deriv (fun t => κ ^ 2 • f (κ * t)) = (fun t => κ ^ 3 • deriv f (κ * t)) ∧
      deriv (deriv fun t => κ ^ 2 • f (κ * t)) = (fun t => κ ^ 4 • deriv (deriv f) (κ * t)) ∧
      deriv (deriv (deriv fun t => κ ^ 2 • f (κ * t))) =
        fun t => κ ^ 5 • deriv (deriv (deriv f)) (κ * t) :=
  deriv_slowForce hf κ

example (hη : ContDiff ℝ 2 η) (hη0 : ∀ z, 0 ≤ η z) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (hη1 : ∫ z, η z = 1) {m : ℝ}
    (hreg : 8 / 3 * selfEnergy e η < m) {f : ℝ → E3} (hf : ContDiff ℝ 3 f)
    (hf0 : ∀ s ≤ 0, f s = 0) {B₂ B₃ : ℝ} (hB₂ : ∀ s, ‖deriv (deriv f) s‖ ≤ B₂)
    (hB₃ : ∀ s, ‖deriv (deriv (deriv f)) s‖ ≤ B₃) {κ : ℝ} (hκ : 0 ≤ κ) (R₀ V : E3)
    {R : ℝ → E3} (hR : ContDiff ℝ 2 R) (hpast : ∀ t ≤ 0, R t = R₀ + t • V)
    (hmot : ∀ t, 0 ≤ t → ∀ i, (m - 4 / 3 * selfEnergy e η) * deriv (deriv R) t i =
      (κ ^ 2 • f (κ * t)) i + linearSelfForce e η R t i) (t : ℝ) :
    ‖deriv (deriv R) t -
        deriv (deriv (effectivePath e m (fun s => κ ^ 2 • f (κ * s)) R₀ V)) t‖ ≤
      ((2 / 3 * (e ^ 2 / (4 * π)) / m) ^ 2 * B₂ +
        b * (2 / 3 * (e ^ 2 / (4 * π))) *
          (B₂ / m + κ * (2 / 3 * (e ^ 2 / (4 * π))) * B₃ / m ^ 2)) /
        (m - 8 / 3 * selfEnergy e η) * κ ^ 4 :=
  norm_accel_sub_effective_le hη hη0 hb0 hb hrot hη1 hreg hf hf0 hB₂ hB₃ hκ R₀ V hR hpast hmot t

example (hη : ContDiff ℝ 2 η) (hη0 : ∀ z, 0 ≤ η z) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (hη1 : ∫ z, η z = 1) {m : ℝ}
    (hreg : 8 / 3 * selfEnergy e η < m) {f : ℝ → E3} (hf : ContDiff ℝ 3 f)
    (hf0 : ∀ s ≤ 0, f s = 0) {B₂ B₃ : ℝ} (hB₂ : ∀ s, ‖deriv (deriv f) s‖ ≤ B₂)
    (hB₃ : ∀ s, ‖deriv (deriv (deriv f)) s‖ ≤ B₃) {κ : ℝ} (hκ : 0 ≤ κ) (R₀ V : E3)
    {R : ℝ → E3} (hR : ContDiff ℝ 2 R) (hpast : ∀ t ≤ 0, R t = R₀ + t • V)
    (hmot : ∀ t, 0 ≤ t → ∀ i, (m - 4 / 3 * selfEnergy e η) * deriv (deriv R) t i =
      (κ ^ 2 • f (κ * t)) i + linearSelfForce e η R t i) {t : ℝ} (ht : 0 ≤ t) :
    let X := effectivePath e m (fun s => κ ^ 2 • f (κ * s)) R₀ V
    let C := ((2 / 3 * (e ^ 2 / (4 * π)) / m) ^ 2 * B₂ +
        b * (2 / 3 * (e ^ 2 / (4 * π))) *
          (B₂ / m + κ * (2 / 3 * (e ^ 2 / (4 * π))) * B₃ / m ^ 2)) /
        (m - 8 / 3 * selfEnergy e η)
    ‖deriv (deriv R) t - deriv (deriv X) t‖ ≤ C * κ ^ 4 ∧
      ‖deriv R t - deriv X t‖ ≤ C * κ ^ 4 * t ∧ ‖R t - X t‖ ≤ C * κ ^ 4 * t ^ 2 / 2 :=
  norm_sub_effectivePath_le hη hη0 hb0 hb hrot hη1 hreg hf hf0 hB₂ hB₃ hκ R₀ V hR hpast hmot ht

example (hη : ContDiff ℝ 2 η) (hη0 : ∀ z, 0 ≤ η z) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∀ z : E3, b < ‖z‖ → η z = 0)
    (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x) (hη1 : ∫ z, η z = 1) {m : ℝ}
    (hreg : 8 / 3 * selfEnergy e η < m) {f : ℝ → E3} (hf : ContDiff ℝ 3 f)
    (hf0 : ∀ s ≤ 0, f s = 0) {B₂ B₃ : ℝ} (hB₂ : ∀ s, ‖deriv (deriv f) s‖ ≤ B₂)
    (hB₃ : ∀ s, ‖deriv (deriv (deriv f)) s‖ ≤ B₃) {κ : ℝ} (hκ : 0 < κ) (R₀ V : E3)
    {R : ℝ → E3} (hR : ContDiff ℝ 2 R) (hpast : ∀ t ≤ 0, R t = R₀ + t • V)
    (hmot : ∀ t, 0 ≤ t → ∀ i, (m - 4 / 3 * selfEnergy e η) * deriv (deriv R) t i =
      (κ ^ 2 • f (κ * t)) i + linearSelfForce e η R t i) {T t : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T / κ) :
    let X := effectivePath e m (fun s => κ ^ 2 • f (κ * s)) R₀ V
    let C := ((2 / 3 * (e ^ 2 / (4 * π)) / m) ^ 2 * B₂ +
        b * (2 / 3 * (e ^ 2 / (4 * π))) *
          (B₂ / m + κ * (2 / 3 * (e ^ 2 / (4 * π))) * B₃ / m ^ 2)) /
        (m - 8 / 3 * selfEnergy e η)
    ‖deriv R t - deriv X t‖ ≤ C * T * κ ^ 3 ∧ ‖R t - X t‖ ≤ C * T ^ 2 * κ ^ 2 / 2 ∧
      deriv (deriv X) t - m⁻¹ • (κ ^ 2 • f (κ * t)) =
        (κ ^ 3 * (2 / 3 * (e ^ 2 / (4 * π)) / m ^ 2)) • deriv f (κ * t) :=
  norm_sub_effectivePath_le_slow hη hη0 hb0 hb hrot hη1 hreg hf hf0 hB₂ hB₃ hκ R₀ V hR hpast hmot ht
    htT

example (hη : ContDiff ℝ 2 η) (hη0 : ∀ z, 0 ≤ η z) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    {m : ℝ} (hreg : 8 / 3 * selfEnergy e η < m) {f : ℝ → E3} (hf : Continuous f)
    (hf0 : ∀ s ≤ 0, f s = 0) {B₀ : ℝ} (hB₀ : ∀ s, ‖f s‖ ≤ B₀) (κ : ℝ) (R₀ V : E3) :
    ∃ R : ℝ → E3, ContDiff ℝ 2 R ∧ (∀ t ≤ 0, R t = R₀ + t • V) ∧
      ∀ t, 0 ≤ t → ∀ i, (m - 4 / 3 * selfEnergy e η) * deriv (deriv R) t i =
        (κ ^ 2 • f (κ * t)) i + linearSelfForce e η R t i :=
  exists_slowMotion hη hη0 hb0 hb hrot hreg hf hf0 hB₀ κ R₀ V

example (hη : ContDiff ℝ 2 η) (hη0 : ∀ z, 0 ≤ η z)
    (hb : ∀ z : E3, 1 < ‖z‖ → η z = 0) (hrot : ∀ (f : E3 ≃ₗᵢ[ℝ] E3) (x : E3), η (f x) = η x)
    (hη1 : ∫ z, η z = 1) {a m : ℝ} (ha : 0 < a) (hreg : 8 / 3 * selfEnergy e η / a < m)
    {f : ℝ → E3} (hf : ContDiff ℝ 3 f) (hf0 : ∀ s ≤ 0, f s = 0) {B₂ B₃ : ℝ}
    (hB₂ : ∀ s, ‖deriv (deriv f) s‖ ≤ B₂) (hB₃ : ∀ s, ‖deriv (deriv (deriv f)) s‖ ≤ B₃)
    {κ : ℝ} (hκ : 0 ≤ κ) (R₀ V : E3) {R : ℝ → E3} (hR : ContDiff ℝ 2 R)
    (hpast : ∀ t ≤ 0, R t = R₀ + t • V)
    (hmot : ∀ t, 0 ≤ t → ∀ i, (m - 4 / 3 * selfEnergy e η / a) * deriv (deriv R) t i =
      (κ ^ 2 • f (κ * t)) i + linearSelfForce e (scaledProfile a η) R t i) {t : ℝ}
    (ht : 0 ≤ t) :
    let X := effectivePath e m (fun s => κ ^ 2 • f (κ * s)) R₀ V
    let C := ((2 / 3 * (e ^ 2 / (4 * π)) / m) ^ 2 * B₂ +
        a * (2 / 3 * (e ^ 2 / (4 * π))) *
          (B₂ / m + κ * (2 / 3 * (e ^ 2 / (4 * π))) * B₃ / m ^ 2)) /
        (m - 8 / 3 * selfEnergy e η / a)
    ‖deriv (deriv R) t - deriv (deriv X) t‖ ≤ C * κ ^ 4 ∧
      ‖deriv R t - deriv X t‖ ≤ C * κ ^ 4 * t ∧ ‖R t - X t‖ ≤ C * κ ^ 4 * t ^ 2 / 2 :=
  norm_sub_effectivePath_le_scaledProfile hη hη0 hb hrot hη1 ha hreg hf hf0 hB₂ hB₃ hκ R₀ V hR hpast
    hmot ht

example {g : ℝ → E3} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (k : ℕ) : ∃ B, ∀ s, ‖deriv^[k] g s‖ ≤ B :=
  exists_bound_iterate_deriv hg hc k

example : ContDiff ℝ ∞ pulseForce :=
  contDiff_pulseForce

example {s : ℝ} (hs : s ≤ 0) : pulseForce s = 0 :=
  pulseForce_eq_zero hs

example : HasCompactSupport pulseForce :=
  hasCompactSupport_pulseForce

example (e : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (R₀ V : E3) :
    ∃ (C : ℝ) (R : ℝ → E3), ContDiff ℝ 2 R ∧ (∀ t ≤ 0, R t = R₀ + t • V) ∧
      (∀ t, 0 ≤ t → ∀ i,
        (8 / 3 * selfEnergy e radialBump + 1 - 4 / 3 * selfEnergy e radialBump) *
            deriv (deriv R) t i =
          (κ ^ 2 • pulseForce (κ * t)) i + linearSelfForce e radialBump R t i) ∧
      ∀ t, 0 ≤ t →
        ‖deriv (deriv R) t - deriv (deriv (effectivePath e (8 / 3 * selfEnergy e radialBump + 1)
            (fun s => κ ^ 2 • pulseForce (κ * s)) R₀ V)) t‖ ≤ C * κ ^ 4 ∧
        ‖R t - effectivePath e (8 / 3 * selfEnergy e radialBump + 1)
            (fun s => κ ^ 2 • pulseForce (κ * s)) R₀ V t‖ ≤ C * κ ^ 4 * t ^ 2 / 2 :=
  effectiveComparison_radialBump e hκ R₀ V

example {e : ℝ} (he : e ≠ 0) :
    ∃ γ, 0 < γ ∧ ∀ (c : E3) (t : ℝ) (i : Fin 3),
      -(2 / 3 * selfEnergy e radialBump) * deriv (deriv fun s => Real.exp (γ * s) • c) t i =
        linearSelfForce e radialBump (fun s => Real.exp (γ * s) • c) t i :=
  exists_runaway_radialBump he

end EffectiveComparison

end ProjectAinos.Electrodynamics.RadiationReaction
