/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.RadiationReaction.WorldTube

/-! Public consumers of Dirac's world tube (Landau–Lifshitz §76): the second-order expansions in a
small parameter, the world line in the proper time with its Taylor bounds, the retarded proper
time, the retarded field of Liénard and Wiechert as the curvature of its four-potential, the
stress tensor of a null two-form, the boost to the rest frame, the retarded time and the scaled
lag on the tube, the expansion of the integrand, the flux through the tube with the
electromagnetic mass and the force of Lorentz and Dirac, the balance of four-momentum of the bare
particle, and the uniform and hyperbolic motions. Default elaborator options are intentional:
these checks must not rely on the implementation's transparency settings. Every statement is
pinned with its type. -/

noncomputable section

section WorldTube

open Set Filter MeasureTheory Asymptotics Metric

open scoped Topology

namespace ProjectAinos.Electrodynamics.RadiationReaction.WorldTube

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity SmoothGeometry.Sphere

local notation "η" => minkowskiForm LorentzConvention.timeNegative 3

/-! ### Expansions -/

section Expansion

variable {P : Type*} {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

example (c₀ c₁ c₂ : P → E) (x : ℝ × P) :
    series3 c₀ c₁ c₂ x = c₀ x.2 + x.1 • c₁ x.2 + x.1 ^ 2 • c₂ x.2 :=
  rfl

example {l : Filter (ℝ × P)} {f : ℝ × P → E} {c₀ c₁ c₂ : P → E} (h : HasExp l f c₀ c₁ c₂) :
    (fun x : ℝ × P => c₀ x.2) =O[l] (fun _ => (1 : ℝ)) ∧
      (fun x : ℝ × P => c₁ x.2) =O[l] (fun _ => (1 : ℝ)) ∧
      (fun x : ℝ × P => c₂ x.2) =O[l] (fun _ => (1 : ℝ)) ∧
      (fun x => f x - series3 c₀ c₁ c₂ x) =O[l] (fun x => x.1 ^ 3) :=
  ⟨h.bdd₀, h.bdd₁, h.bdd₂, h.rem⟩

example {l : Filter (ℝ × P)} (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) :
    (fun x : ℝ × P => x.1) =O[l] (fun _ => (1 : ℝ)) :=
  isBigO_fst_one hl

example {l : Filter (ℝ × P)} (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) {m n : ℕ}
    (h : m ≤ n) : (fun x : ℝ × P => x.1 ^ n) =O[l] (fun x => x.1 ^ m) :=
  isBigO_pow_pow hl h

example {l : Filter (ℝ × P)} (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (n : ℕ) :
    (fun x : ℝ × P => x.1 ^ n) =O[l] (fun _ => (1 : ℝ)) :=
  isBigO_pow_one hl n

example {α : Type*} {l' : Filter α} (B : E →L[ℝ] F →L[ℝ] G) {f : α → E} {g : α → F}
    {φ ψ : α → ℝ} (hf : f =O[l'] φ) (hg : g =O[l'] ψ) :
    (fun x => B (f x) (g x)) =O[l'] (fun x => φ x * ψ x) :=
  isBigO_bilin B hf hg

variable {l : Filter (ℝ × P)} {f g : ℝ × P → E} {c₀ c₁ c₂ d₀ d₁ d₂ : P → E}

example (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0))
    (h₀ : (fun x : ℝ × P => c₀ x.2) =O[l] (fun _ => (1 : ℝ)))
    (h₁ : (fun x : ℝ × P => c₁ x.2) =O[l] (fun _ => (1 : ℝ)))
    (h₂ : (fun x : ℝ × P => c₂ x.2) =O[l] (fun _ => (1 : ℝ))) :
    (fun x => series3 c₀ c₁ c₂ x) =O[l] (fun _ => (1 : ℝ)) :=
  HasExp.series_isBigO_one hl h₀ h₁ h₂

example (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (h : HasExp l f c₀ c₁ c₂) :
    f =O[l] (fun _ => (1 : ℝ)) :=
  h.isBigO_one hl

example (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (h : HasExp l f c₀ c₁ c₂) :
    (fun x => f x - c₀ x.2) =O[l] (fun x => x.1) :=
  h.sub_isBigO hl

example (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (h : HasExp l f c₀ c₁ c₂) :
    (fun x => f x - (c₀ x.2 + x.1 • c₁ x.2)) =O[l] (fun x => x.1 ^ 2) :=
  h.sub_isBigO_two hl

example (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (h : HasExp l f c₀ c₁ c₂) :
    Tendsto (fun x => f x - c₀ x.2) l (𝓝 0) :=
  h.tendsto_sub hl

example (h : HasExp l f c₀ c₁ c₂) (hfg : ∀ᶠ x in l, f x = g x) : HasExp l g c₀ c₁ c₂ :=
  h.congr_fun hfg

example (h : HasExp l f c₀ c₁ c₂) (h₀ : ∀ᶠ x in l, c₀ x.2 = d₀ x.2)
    (h₁ : ∀ᶠ x in l, c₁ x.2 = d₁ x.2) (h₂ : ∀ᶠ x in l, c₂ x.2 = d₂ x.2) :
    HasExp l f d₀ d₁ d₂ :=
  h.congr_coeff h₀ h₁ h₂

example (hc : (fun x : ℝ × P => c₀ x.2) =O[l] (fun _ => (1 : ℝ))) :
    HasExp l (fun x => c₀ x.2) c₀ 0 0 :=
  HasExp.const hc

example (h₀ : (fun x : ℝ × P => c₀ x.2) =O[l] (fun _ => (1 : ℝ)))
    (h₁ : (fun x : ℝ × P => c₁ x.2) =O[l] (fun _ => (1 : ℝ)))
    (h₂ : (fun x : ℝ × P => c₂ x.2) =O[l] (fun _ => (1 : ℝ))) :
    HasExp l (series3 c₀ c₁ c₂) c₀ c₁ c₂ :=
  HasExp.series h₀ h₁ h₂

example (hf : HasExp l f c₀ c₁ c₂) (h : (fun x => g x - f x) =O[l] (fun x => x.1 ^ 3)) :
    HasExp l g c₀ c₁ c₂ :=
  hf.of_isBigO_sub h

example (hf : HasExp l f c₀ c₁ c₂) (hg : HasExp l g d₀ d₁ d₂) :
    HasExp l (fun x => f x + g x) (fun p => c₀ p + d₀ p) (fun p => c₁ p + d₁ p)
      (fun p => c₂ p + d₂ p) :=
  hf.add hg

example (hf : HasExp l f c₀ c₁ c₂) :
    HasExp l (fun x => -f x) (fun p => -c₀ p) (fun p => -c₁ p) (fun p => -c₂ p) :=
  hf.neg

example (hf : HasExp l f c₀ c₁ c₂) (hg : HasExp l g d₀ d₁ d₂) :
    HasExp l (fun x => f x - g x) (fun p => c₀ p - d₀ p) (fun p => c₁ p - d₁ p)
      (fun p => c₂ p - d₂ p) :=
  hf.sub hg

example (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (hf : HasExp l f c₀ c₁ c₂) :
    HasExp l (fun x => x.1 • f x) 0 c₀ c₁ :=
  hf.eps_smul hl

example (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (B : E →L[ℝ] F →L[ℝ] G)
    {f : ℝ × P → E} {g : ℝ × P → F} {c₀ c₁ c₂ : P → E} {d₀ d₁ d₂ : P → F}
    (hf : HasExp l f c₀ c₁ c₂) (hg : HasExp l g d₀ d₁ d₂) :
    HasExp l (fun x => B (f x) (g x)) (fun p => B (c₀ p) (d₀ p))
      (fun p => B (c₀ p) (d₁ p) + B (c₁ p) (d₀ p))
      (fun p => B (c₀ p) (d₂ p) + B (c₁ p) (d₁ p) + B (c₂ p) (d₀ p)) :=
  hf.bilin hl B hg

example (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) {f g : ℝ × P → ℝ}
    {c₀ c₁ c₂ d₀ d₁ d₂ : P → ℝ} (hf : HasExp l f c₀ c₁ c₂) (hg : HasExp l g d₀ d₁ d₂) :
    HasExp l (fun x => f x * g x) (fun p => c₀ p * d₀ p) (fun p => c₀ p * d₁ p + c₁ p * d₀ p)
      (fun p => c₀ p * d₂ p + c₁ p * d₁ p + c₂ p * d₀ p) :=
  hf.mul hl hg

example (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) {f : ℝ × P → ℝ} {g : ℝ × P → E}
    {c₀ c₁ c₂ : P → ℝ} {d₀ d₁ d₂ : P → E} (hf : HasExp l f c₀ c₁ c₂)
    (hg : HasExp l g d₀ d₁ d₂) :
    HasExp l (fun x => f x • g x) (fun p => c₀ p • d₀ p)
      (fun p => c₀ p • d₁ p + c₁ p • d₀ p)
      (fun p => c₀ p • d₂ p + c₁ p • d₁ p + c₂ p • d₀ p) :=
  hf.smul hl hg

example (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) {f : ℝ × P → ℝ} {c₁ c₂ : P → ℝ}
    (hf : HasExp l f 1 c₁ c₂) : ∀ᶠ x in l, 1 / 2 ≤ f x :=
  hf.eventually_half_le hl

example (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) {f : ℝ × P → ℝ} {c₁ c₂ : P → ℝ}
    (hf : HasExp l f 1 c₁ c₂) :
    HasExp l (fun x => (f x)⁻¹) 1 (fun p => -c₁ p) (fun p => c₁ p ^ 2 - c₂ p) :=
  hf.inv hl

example {K : Set P} {f : ℝ × P → E} {c₀ c₁ c₂ : P → E}
    (h : HasExp (𝓝[>] (0 : ℝ) ×ˢ 𝓟 K) f c₀ c₁ c₂) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∀ p ∈ K,
      ‖f (ε, p) - (c₀ p + ε • c₁ p + ε ^ 2 • c₂ p)‖ ≤ C * ε ^ 3 :=
  h.exists_bound

end Expansion

/-! ### The Minkowski product and causality -/

example (v w : Spacetime) : η v w = -(v 0 * w 0) + inner ℝ (space v) (space w) :=
  minkowski_eq_time_space v w

example (v w : Spacetime) : η v w = -(v 0 * w 0) + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 :=
  minkowski_coords v w

example (v : Spacetime) (μ : Fin 4) :
    η v (Pi.single μ 1) = lorentzSign .timeNegative μ * v μ :=
  minkowski_single v μ

example (v w : Spacetime) : |η v w| ≤ ‖η‖ * ‖v‖ * ‖w‖ :=
  abs_minkowski_le v w

example {X u : Spacetime} (hX : η X X = 0) (hu : η u u = -1) (hu0 : 0 < u 0) (h : η X u < 0) :
    0 < X 0 :=
  pos_time_of_null_of_neg hX hu hu0 h

example {X u : Spacetime} (hX : η X X = 0) (hX0 : 0 < X 0) (hu : η u u = -1) (hu0 : 0 < u 0) :
    η X u < 0 :=
  minkowski_neg_of_null hX hX0 hu hu0

example {X D : Spacetime} (hX : η X X = 0) (hX0 : 0 < X 0) (hD : ‖space D‖ < D 0) :
    η (X + D) (X + D) < 0 :=
  minkowski_null_add_timelike_neg hX hX0 hD

example (a b : Spacetime) : η (a + b) (a + b) = η a a + 2 * η a b + η b b :=
  minkowski_add_self a b

example {u : Spacetime} (hu : η u u = -1) (hu0 : 0 < u 0) : ‖space u‖ < u 0 :=
  norm_space_lt_of_unit hu hu0

/-! ### World lines in the proper time -/

example (w : ProperWorldline) : ContDiff ℝ 4 w.z := w.contDiff_z

example (w : ProperWorldline) (τ : ℝ) : η (deriv w.z τ) (deriv w.z τ) = -1 := w.unit τ

example (w : ProperWorldline) (τ : ℝ) : 0 < deriv w.z τ 0 := w.future τ

example (w : ProperWorldline) : w.vel = deriv w.z := rfl

example (w : ProperWorldline) : w.acc = deriv w.vel := rfl

example (w : ProperWorldline) : w.jerk = deriv w.acc := rfl

example (w : ProperWorldline) : w.snap = deriv w.jerk := rfl

example (w : ProperWorldline) : ContDiff ℝ 3 w.vel := w.contDiff_vel

example (w : ProperWorldline) : ContDiff ℝ 2 w.acc := w.contDiff_acc

example (w : ProperWorldline) : ContDiff ℝ 1 w.jerk := w.contDiff_jerk

example (w : ProperWorldline) : Continuous w.snap := w.continuous_snap

example (w : ProperWorldline) : Continuous w.jerk := w.continuous_jerk

example (w : ProperWorldline) : Continuous w.acc := w.continuous_acc

example (w : ProperWorldline) : Continuous w.vel := w.continuous_vel

example (w : ProperWorldline) : Continuous w.z := w.continuous_z

example (w : ProperWorldline) (τ : ℝ) : HasDerivAt w.z (w.vel τ) τ := w.hasDerivAt_z τ

example (w : ProperWorldline) (τ : ℝ) : HasDerivAt w.vel (w.acc τ) τ := w.hasDerivAt_vel τ

example (w : ProperWorldline) (τ : ℝ) : HasDerivAt w.acc (w.jerk τ) τ := w.hasDerivAt_acc τ

example (w : ProperWorldline) (τ : ℝ) : HasDerivAt w.jerk (w.snap τ) τ := w.hasDerivAt_jerk τ

example (w : ProperWorldline) (τ : ℝ) : η (w.vel τ) (w.vel τ) = -1 := w.vel_unit τ

example (w : ProperWorldline) (τ : ℝ) : 0 < w.vel τ 0 := w.vel_future τ

example (w : ProperWorldline) (τ : ℝ) : η (w.vel τ) (w.acc τ) = 0 := w.vel_acc τ

example (w : ProperWorldline) (τ : ℝ) : η (w.vel τ) (w.jerk τ) = -η (w.acc τ) (w.acc τ) :=
  w.vel_jerk τ

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E} {s K : ℝ} {n : ℕ}
    (hs : 0 ≤ s) (hK : 0 ≤ K) (hf : ∀ r ∈ Icc 0 s, HasDerivAt f (f' r) r) (h0 : f 0 = 0)
    (hb : ∀ r ∈ Icc 0 s, ‖f' r‖ ≤ K * r ^ n) : ‖f s‖ ≤ K * s ^ (n + 1) :=
  ProperWorldline.norm_le_of_deriv_le hs hK hf h0 hb

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {τ r : ℝ}
    (hf : HasDerivAt f f' (τ - r)) : HasDerivAt (fun r => f (τ - r)) (-f') r :=
  ProperWorldline.hasDerivAt_comp_sub hf

example {w : ProperWorldline} {τ s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (τ - s) τ, ‖w.snap t‖ ≤ M) : ‖w.jerk (τ - s) - w.jerk τ‖ ≤ M * s :=
  ProperWorldline.norm_taylor_jerk hs hM hb

example {w : ProperWorldline} {τ s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (τ - s) τ, ‖w.snap t‖ ≤ M) :
    ‖w.acc (τ - s) - (w.acc τ - s • w.jerk τ)‖ ≤ M * s ^ 2 :=
  ProperWorldline.norm_taylor_acc hs hM hb

example {w : ProperWorldline} {τ s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (τ - s) τ, ‖w.snap t‖ ≤ M) :
    ‖w.vel (τ - s) - (w.vel τ - s • w.acc τ + (s ^ 2 / 2) • w.jerk τ)‖ ≤ M * s ^ 3 :=
  ProperWorldline.norm_taylor_vel hs hM hb

example {w : ProperWorldline} {τ s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (τ - s) τ, ‖w.snap t‖ ≤ M) :
    ‖w.z τ - w.z (τ - s) - (s • w.vel τ - (s ^ 2 / 2) • w.acc τ + (s ^ 3 / 6) • w.jerk τ)‖ ≤
      M * s ^ 4 :=
  ProperWorldline.norm_taylor_z hs hM hb

example {w : ProperWorldline} {τ s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (τ - s) τ, ‖w.acc t‖ ≤ M) : ‖w.vel (τ - s) - w.vel τ‖ ≤ M * s :=
  ProperWorldline.norm_taylor_vel1 hs hM hb

example {w : ProperWorldline} {τ s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (τ - s) τ, ‖w.acc t‖ ≤ M) :
    ‖w.z τ - w.z (τ - s) - s • w.vel τ‖ ≤ M * s ^ 2 :=
  ProperWorldline.norm_taylor_z1 hs hM hb

example (w : ProperWorldline) (t₁ t₂ : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc t₁ t₂, ‖w.vel t‖ ≤ M ∧ ‖w.acc t‖ ≤ M ∧ ‖w.jerk t‖ ≤ M ∧
      ‖w.snap t‖ ≤ M :=
  ProperWorldline.exists_deriv_bound w t₁ t₂

example (w : ProperWorldline) {τ₁ τ₂ : ℝ} (h : τ₁ < τ₂) :
    ‖space (w.z τ₂ - w.z τ₁)‖ < (w.z τ₂ - w.z τ₁) 0 :=
  time_sub_gt_norm w h

/-! ### The retarded proper time -/

example (w : ProperWorldline) (x : Spacetime) (τ : ℝ) :
    w.IsRetarded x τ ↔ η (x - w.z τ) (x - w.z τ) = 0 ∧ w.z τ 0 < x 0 :=
  Iff.rfl

example {w : ProperWorldline} {x : Spacetime} {τ₁ τ₂ : ℝ} (h₁ : w.IsRetarded x τ₁)
    (h₂ : w.IsRetarded x τ₂) : τ₁ = τ₂ :=
  h₁.unique h₂

example (w : ProperWorldline) (x : Spacetime) : ℝ :=
  w.retardedProperTime x

example {w : ProperWorldline} {x : Spacetime} {τ : ℝ} (h : w.IsRetarded x τ) :
    w.retardedProperTime x = τ :=
  ProperWorldline.retardedProperTime_eq h

example {w : ProperWorldline} {x : Spacetime} {τ : ℝ} (h : w.IsRetarded x τ) :
    0 < -η (x - w.z τ) (w.vel τ) :=
  ProperWorldline.retardedDistance_pos h

example {w : ProperWorldline} {x : Spacetime} {τ₀ : ℝ} (h : w.IsRetarded x τ₀) :
    ∀ᶠ y in 𝓝 x, w.IsRetarded y (w.retardedProperTime y) :=
  ProperWorldline.eventually_isRetarded h

example {w : ProperWorldline} {x : Spacetime} {τ₀ : ℝ} (h : w.IsRetarded x τ₀) :
    ContDiffAt ℝ 4 w.retardedProperTime x :=
  ProperWorldline.contDiffAt_retardedProperTime h

example {w : ProperWorldline} {x : Spacetime} {τ₀ : ℝ} (h : w.IsRetarded x τ₀) :
    ContinuousAt w.retardedProperTime x :=
  ProperWorldline.continuousAt_retardedProperTime h

example {w : ProperWorldline} {x : Spacetime} {τ₀ : ℝ} (h : w.IsRetarded x τ₀) :
    HasFDerivAt w.retardedProperTime ((η (x - w.z τ₀) (w.vel τ₀))⁻¹ • η (x - w.z τ₀)) x :=
  ProperWorldline.hasFDerivAt_retardedProperTime h

/-! ### The field of Liénard and Wiechert and its stress tensor -/

example (φ : Spacetime →L[ℝ] ℝ) (v : Spacetime) : oneCovector.symm φ ![v] = φ v :=
  oneCovector_symm_apply_vec φ v

example (R Y : Spacetime) : TwoForm :=
  bivector R Y

example (R Y v w : Spacetime) : bivector R Y ![v, w] = η R v * η Y w - η R w * η Y v :=
  bivector_apply R Y v w

example (R Y v w : Spacetime) :
    covectorPairing ((bivector R Y).curryLeft v) ((bivector R Y).curryLeft w) =
      η (η R v • Y - η Y v • R) (η R w • Y - η Y w • R) :=
  covectorPairing_bivector R Y v w

example (R Y : Spacetime) :
    tensorContraction (bivector R Y) (bivector R Y) = 2 * (η R R * η Y Y - η R Y ^ 2) :=
  tensorContraction_bivector R Y

example {R : Spacetime} (hR : η R R = 0) (Y v w : Spacetime) :
    stressForm (bivector R Y) v w = η R v * η R w * η Y Y -
      η R Y * (η R v * η Y w + η Y v * η R w) + 1 / 2 * η v w * η R Y ^ 2 :=
  stressForm_bivector_of_null hR Y v w

example (F : TwoForm) (N : Spacetime) (μ : Fin 4) :
    stressFlux F N μ = lorentzSign .timeNegative μ * stressForm F (Pi.single μ 1) N :=
  rfl

example {R : Spacetime} (hR : η R R = 0) (Y N : Spacetime) :
    stressFlux (bivector R Y) N = (η R N * η Y Y) • R -
      η R Y • (η Y N • R + η R N • Y) + (1 / 2 * η R Y ^ 2) • N :=
  stressFlux_bivector hR Y N

example (e : ℝ) (R u a : Spacetime) :
    lwVector e R u a = (-(e / (4 * Real.pi))) • (((-η R u) ^ 2)⁻¹ • a +
      ((1 + η R a) / (-η R u) ^ 3) • u) :=
  rfl

example (e : ℝ) (w : ProperWorldline) (x : Spacetime) :
    retardedField e w x = bivector (x - w.z (w.retardedProperTime x))
      (lwVector e (x - w.z (w.retardedProperTime x)) (w.vel (w.retardedProperTime x))
        (w.acc (w.retardedProperTime x))) :=
  rfl

example (e : ℝ) (w : ProperWorldline) : Potential :=
  lwPotential e w

example (e : ℝ) (w : ProperWorldline) {x : Spacetime} {τ₀ : ℝ} (h : w.IsRetarded x τ₀) :
    fieldTensor (lwPotential e w) x = retardedField e w x :=
  fieldTensor_lwPotential e w h

/-! ### The rest frame -/

example (u : Spacetime) (n : Space 3) : Spacetime :=
  restFrame u n

example (u : Spacetime) (n : Space 3) : restFrame u (-n) = -restFrame u n :=
  restFrame_neg u n

example {u : Spacetime} (hu : η u u = -1) (hu0 : 0 < u 0) (n : Space 3) :
    η (restFrame u n) u = 0 :=
  minkowskiForm_restFrame_vel hu hu0 n

example {u : Spacetime} (hu : η u u = -1) (hu0 : 0 < u 0) (n : Space 3) :
    η (restFrame u n) (restFrame u n) = ‖n‖ ^ 2 :=
  minkowskiForm_restFrame_self hu hu0 n

example {u : Spacetime} (hu : η u u = -1) (hu0 : 0 < u 0) (m n : Space 3) :
    η (restFrame u m) (restFrame u n) = inner ℝ m n :=
  minkowskiForm_restFrame hu hu0 m n

example {u : Spacetime} (hu0 : 0 < u 0) (n : Space 3) :
    ContinuousAt (fun p : Spacetime × Space 3 => restFrame p.1 p.2) (u, n) :=
  continuousAt_restFrame hu0 n

/-! ### The retarded field on the tube -/

example (w : ProperWorldline) (τ₁ τ₂ B : ℝ) (p : ℝ × Spacetime) :
    p ∈ tubeParams w τ₁ τ₂ B ↔
      p.1 ∈ Icc τ₁ τ₂ ∧ η p.2 p.2 = 1 ∧ η p.2 (w.vel p.1) = 0 ∧ ‖p.2‖ ≤ B :=
  Iff.rfl

example (w : ProperWorldline) (τ₁ τ₂ B : ℝ) :
    tubeFilter w τ₁ τ₂ B = 𝓝[>] (0 : ℝ) ×ˢ 𝓟 (tubeParams w τ₁ τ₂ B) :=
  rfl

example (w : ProperWorldline) (x : ℝ × (ℝ × Spacetime)) :
    tubeEvent w x = w.z x.2.1 + x.1 • x.2.2 :=
  rfl

example (w : ProperWorldline) (x : ℝ × (ℝ × Spacetime)) :
    lag w x = x.2.1 - w.retardedProperTime (tubeEvent w x) :=
  rfl

example {w : ProperWorldline} {τ₁ τ₂ B : ℝ} :
    ∀ᶠ x in tubeFilter w τ₁ τ₂ B, x.1 / 2 ≤ lag w x ∧ lag w x ≤ 2 * x.1 ∧
      w.IsRetarded (tubeEvent w x) (x.2.1 - lag w x) :=
  eventually_isRetarded_tubeEvent

example (w : ProperWorldline) (p : ℝ × Spacetime) : cα w p = η p.2 (w.acc p.1) := rfl

example (w : ProperWorldline) (p : ℝ × Spacetime) : cβ w p = η p.2 (w.jerk p.1) := rfl

example (w : ProperWorldline) (p : ℝ × Spacetime) : cA w p = η (w.acc p.1) (w.acc p.1) := rfl

example (w : ProperWorldline) (p : ℝ × Spacetime) :
    cσ₂ w p = 3 / 8 * cα w p ^ 2 + cβ w p / 6 - cA w p / 24 :=
  rfl

example (w : ProperWorldline) (x : ℝ × (ℝ × Spacetime)) : scaledLag w x = lag w x / x.1 := rfl

example {w : ProperWorldline} {τ₁ τ₂ B : ℝ} :
    HasExp (tubeFilter w τ₁ τ₂ B) (scaledLag w) (fun _ => (1 : ℝ)) (fun p => -(cα w p / 2))
      (cσ₂ w) :=
  hasExp_scaledLag

example (w : ProperWorldline) (ε τ : ℝ) (N : Spacetime) :
    tubeIntegrandMain w ε τ N = (-(1 / (2 * ε ^ 2))) • N + (1 / (2 * ε)) • w.acc τ +
      ((η (w.acc τ) (w.acc τ) / 2) • N + (2 / 3 * η (w.acc τ) (w.acc τ)) • w.vel τ -
        (3 / 4 * η N (w.acc τ)) • w.acc τ - (2 / 3 : ℝ) • w.jerk τ) :=
  rfl

example (e : ℝ) (w : ProperWorldline) (τ₁ τ₂ B : ℝ) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∀ τ ∈ Icc τ₁ τ₂, ∀ N : Spacetime, η N N = 1 →
      η N (w.vel τ) = 0 → ‖N‖ ≤ B →
      w.IsRetarded (w.z τ + ε • N) (w.retardedProperTime (w.z τ + ε • N)) ∧
      ‖(ε ^ 2 * (1 + ε * η N (w.acc τ))) • stressFlux (retardedField e w (w.z τ + ε • N)) N -
        (e / (4 * Real.pi)) ^ 2 • tubeIntegrandMain w ε τ N‖ ≤ C * ε :=
  tubeIntegrand_expansion e w τ₁ τ₂ B

/-! ### Dirac's tube and its flux -/

example (w : ProperWorldline) (τ : ℝ) (n : Space 3) :
    tubeNormal w τ n = restFrame (w.vel τ) n :=
  rfl

example (e : ℝ) (w : ProperWorldline) (ε τ : ℝ) (n : Space 3) :
    tubeIntegrand e w ε τ n = (ε ^ 2 * (1 + ε * η (tubeNormal w τ n) (w.acc τ))) •
      stressFlux (retardedField e w (w.z τ + ε • tubeNormal w τ n)) (tubeNormal w τ n) :=
  rfl

example (e : ℝ) (w : ProperWorldline) (ε τ₁ τ₂ : ℝ) :
    diracTubeFlux e w ε τ₁ τ₂ =
      ∫ τ in τ₁..τ₂, ∫ n : sphere (0 : Space 3) 1, tubeIntegrand e w ε τ n ∂sphereMeasure :=
  rfl

example (e ε : ℝ) : emMass e ε = e ^ 2 / (8 * Real.pi * ε) := rfl

example (w : ProperWorldline) (τ : ℝ) (n : Space 3) : η (tubeNormal w τ n) (w.vel τ) = 0 :=
  minkowskiForm_tubeNormal_vel w τ n

example (w : ProperWorldline) (τ : ℝ) {n : Space 3} (hn : ‖n‖ = 1) :
    η (tubeNormal w τ n) (tubeNormal w τ n) = 1 :=
  minkowskiForm_tubeNormal_self w τ hn

example (w : ProperWorldline) (τ : ℝ) (n : Space 3) : tubeNormal w τ (-n) = -tubeNormal w τ n :=
  tubeNormal_neg w τ n

example (w : ProperWorldline) : Continuous (fun p : ℝ × Space 3 => tubeNormal w p.1 p.2) :=
  continuous_tubeNormal w

example (w : ProperWorldline) (τ₁ τ₂ : ℝ) :
    ∃ B, ∀ τ ∈ Icc τ₁ τ₂, ∀ n ∈ sphere (0 : Space 3) 1, ‖tubeNormal w τ n‖ ≤ B :=
  exists_bound_tubeNormal w τ₁ τ₂

example (w : ProperWorldline) (τ : ℝ) (n : Space 3) :
    DifferentiableAt ℝ (fun t => tubeNormal w t n) τ :=
  differentiableAt_tubeNormal w τ n

example (w : ProperWorldline) (ε τ : ℝ) {n : Space 3} (hn : ‖n‖ = 1) :
    ∃ V, HasDerivAt (fun t => w.z t + ε • tubeNormal w t n) V τ ∧
      η V (tubeNormal w τ n) = 0 ∧
      -η V (w.vel τ) = 1 + ε * η (tubeNormal w τ n) (w.acc τ) :=
  tube_velocity w ε τ hn

example (e : ℝ) (w : ProperWorldline) (τ₁ τ₂ : ℝ) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∀ τ ∈ Icc τ₁ τ₂, ∀ n ∈ sphere (0 : Space 3) 1,
      w.IsRetarded (w.z τ + ε • tubeNormal w τ n)
        (w.retardedProperTime (w.z τ + ε • tubeNormal w τ n)) ∧
      ‖tubeIntegrand e w ε τ n -
        (e / (4 * Real.pi)) ^ 2 • tubeIntegrandMain w ε τ (tubeNormal w τ n)‖ ≤ C * ε :=
  tubeIntegrand_bound e w τ₁ τ₂

example (e : ℝ) (w : ProperWorldline) {ε τ₁ τ₂ : ℝ}
    (hret : ∀ τ ∈ Icc τ₁ τ₂, ∀ n ∈ sphere (0 : Space 3) 1,
      w.IsRetarded (w.z τ + ε • tubeNormal w τ n)
        (w.retardedProperTime (w.z τ + ε • tubeNormal w τ n))) :
    ContinuousOn (fun p : ℝ × Space 3 => tubeIntegrand e w ε p.1 p.2)
      (Icc τ₁ τ₂ ×ˢ sphere (0 : Space 3) 1) :=
  continuousOn_tubeIntegrand e w hret

example {f : ℝ → Space 3 → Spacetime} {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂)
    (hf : ContinuousOn (fun p : ℝ × Space 3 => f p.1 p.2) (Icc τ₁ τ₂ ×ˢ sphere (0 : Space 3) 1)) :
    IntervalIntegrable (fun τ => ∫ n : sphere (0 : Space 3) 1, f τ n ∂sphereMeasure) volume
      τ₁ τ₂ :=
  intervalIntegrable_integral_sphere h hf

example {f : ℝ → Space 3 → Spacetime} {τ₁ τ₂ τ : ℝ}
    (hf : ContinuousOn (fun p : ℝ × Space 3 => f p.1 p.2) (Icc τ₁ τ₂ ×ˢ sphere (0 : Space 3) 1))
    (hτ : τ ∈ Icc τ₁ τ₂) : Integrable (fun n : sphere (0 : Space 3) 1 => f τ n) sphereMeasure :=
  integrable_sphere_of_continuousOn hf hτ

example (w : ProperWorldline) (ε τ : ℝ) :
    ∫ n : sphere (0 : Space 3) 1, tubeIntegrandMain w ε τ (tubeNormal w τ n) ∂sphereMeasure =
      (4 * Real.pi) • ((1 / (2 * ε)) • w.acc τ +
        (2 / 3 * η (w.acc τ) (w.acc τ)) • w.vel τ - (2 / 3 : ℝ) • w.jerk τ) :=
  integral_tubeIntegrandMain w ε τ

example (e : ℝ) (w : ProperWorldline) (τ : ℝ) :
    lorentzDiracForce e w.vel τ = (2 / 3 * (e ^ 2 / (4 * Real.pi))) •
      (w.jerk τ - η (w.acc τ) (w.acc τ) • w.vel τ) :=
  lorentzDiracForce_vel e w τ

example (e : ℝ) (w : ProperWorldline) : Continuous (lorentzDiracForce e w.vel) :=
  continuous_lorentzDiracForce_vel e w

example (e : ℝ) (w : ProperWorldline) {ε : ℝ} (hε : ε ≠ 0) (τ : ℝ) :
    ∫ n : sphere (0 : Space 3) 1, (e / (4 * Real.pi)) ^ 2 •
      tubeIntegrandMain w ε τ (tubeNormal w τ n) ∂sphereMeasure =
      emMass e ε • w.acc τ - lorentzDiracForce e w.vel τ :=
  integral_tubeIntegrandMain_eq e w hε τ

example (e : ℝ) (w : ProperWorldline) {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀,
      ‖diracTubeFlux e w ε τ₁ τ₂ -
        ∫ τ in τ₁..τ₂, (emMass e ε • w.acc τ - lorentzDiracForce e w.vel τ)‖ ≤ C * ε :=
  diracTubeFlux_expansion e w h

example (e : ℝ) (w : ProperWorldline) {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀,
      ‖diracTubeFlux e w ε τ₁ τ₂ - (emMass e ε • (w.vel τ₂ - w.vel τ₁) -
        (2 / 3 * (e ^ 2 / (4 * Real.pi))) • (w.acc τ₂ - w.acc τ₁) +
          ∫ τ in τ₁..τ₂, radiatedMomentumRate e w.vel τ)‖ ≤ C * ε :=
  diracTubeFlux_expansion_schott e w h

/-! ### The balance of four-momentum -/

example (e : ℝ) (w : ProperWorldline) (m₀ : ℝ → ℝ) (Fext : ℝ → Spacetime) (ε τ₁ τ₂ : ℝ) :
    tubeBalanceDefect e w m₀ Fext ε τ₁ τ₂ =
      m₀ ε • (w.vel τ₂ - w.vel τ₁) - (∫ τ in τ₁..τ₂, Fext τ) + diracTubeFlux e w ε τ₁ τ₂ :=
  rfl

example (e m : ℝ) (w : ProperWorldline) {Fext : ℝ → Spacetime} (hF : Continuous Fext)
    {m₀ : ℝ → ℝ} (hm : ∀ ε, 0 < ε → m₀ ε + emMass e ε = m) {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀,
      ‖tubeBalanceDefect e w m₀ Fext ε τ₁ τ₂ - (m • (w.vel τ₂ - w.vel τ₁) -
        ∫ τ in τ₁..τ₂, (Fext τ + lorentzDiracForce e w.vel τ))‖ ≤ C * ε :=
  tubeBalanceDefect_expansion e m w hF hm h

example (e m : ℝ) (w : ProperWorldline) {Fext : ℝ → Spacetime} (hF : Continuous Fext)
    (h : ∀ τ₁ τ₂, τ₁ ≤ τ₂ → m • (w.vel τ₂ - w.vel τ₁) =
      ∫ τ in τ₁..τ₂, (Fext τ + lorentzDiracForce e w.vel τ)) (τ : ℝ) :
    m • w.acc τ = Fext τ + lorentzDiracForce e w.vel τ :=
  eq_of_integral_eq e m w hF h τ

example (e m : ℝ) (w : ProperWorldline) {Fext : ℝ → Spacetime} (hF : Continuous Fext)
    {m₀ : ℝ → ℝ} (hm : ∀ ε, 0 < ε → m₀ ε + emMass e ε = m)
    (hbal : ∀ τ₁ τ₂, τ₁ ≤ τ₂ →
      Tendsto (fun ε => tubeBalanceDefect e w m₀ Fext ε τ₁ τ₂) (𝓝[>] 0) (𝓝 0))
    (τ : ℝ) : m • w.acc τ = Fext τ + lorentzDiracForce e w.vel τ :=
  lorentzDirac_of_tubeBalance e m w hF hm hbal τ

example (e m : ℝ) (w : ProperWorldline) {Fext : ℝ → Spacetime} (hF : Continuous Fext)
    {m₀ : ℝ → ℝ} (hm : ∀ ε, 0 < ε → m₀ ε + emMass e ε = m) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hbal : ∀ ε ∈ Ioo 0 ε₀, ∀ τ₁ τ₂, τ₁ ≤ τ₂ →
      m₀ ε • (w.vel τ₂ - w.vel τ₁) = (∫ τ in τ₁..τ₂, Fext τ) - diracTubeFlux e w ε τ₁ τ₂)
    (τ : ℝ) : m • w.acc τ = Fext τ + lorentzDiracForce e w.vel τ :=
  lorentzDirac_of_exactTubeBalance e m w hF hm hε₀ hbal τ

example (e m : ℝ) (w : ProperWorldline) {Fext : ℝ → Spacetime} (hF : Continuous Fext)
    {m₀ : ℝ → ℝ} (hm : ∀ ε, 0 < ε → m₀ ε + emMass e ε = m)
    (heq : ∀ τ, m • w.acc τ = Fext τ + lorentzDiracForce e w.vel τ) {τ₁ τ₂ : ℝ}
    (h : τ₁ ≤ τ₂) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ‖tubeBalanceDefect e w m₀ Fext ε τ₁ τ₂‖ ≤ C * ε :=
  tubeBalance_of_lorentzDirac e m w hF hm heq h

example (e m : ℝ) (w : ProperWorldline) {Fext : ℝ → Spacetime} (hF : Continuous Fext)
    {m₀ : ℝ → ℝ} (hm : ∀ ε, 0 < ε → m₀ ε + emMass e ε = m) :
    (∀ τ₁ τ₂, τ₁ ≤ τ₂ →
      Tendsto (fun ε => tubeBalanceDefect e w m₀ Fext ε τ₁ τ₂) (𝓝[>] 0) (𝓝 0)) ↔
      ∀ τ, m • w.acc τ = Fext τ + lorentzDiracForce e w.vel τ :=
  tubeBalance_iff_lorentzDirac e m w hF hm

/-! ### Uniform and hyperbolic motion -/

example (z₀ u₀ : Spacetime) (τ : ℝ) : HasDerivAt (fun τ : ℝ => z₀ + τ • u₀) u₀ τ :=
  hasDerivAt_inertial z₀ u₀ τ

example (z₀ u₀ : Spacetime) (hu : η u₀ u₀ = -1) (hu0 : 0 < u₀ 0) (τ : ℝ) :
    (ProperWorldline.inertial z₀ u₀ hu hu0).z τ = z₀ + τ • u₀ :=
  rfl

example (z₀ u₀ : Spacetime) (hu : η u₀ u₀ = -1) (hu0 : 0 < u₀ 0) :
    (ProperWorldline.inertial z₀ u₀ hu hu0).vel = fun _ => u₀ :=
  ProperWorldline.inertial_vel z₀ u₀ hu hu0

example (z₀ u₀ : Spacetime) (hu : η u₀ u₀ = -1) (hu0 : 0 < u₀ 0) :
    (ProperWorldline.inertial z₀ u₀ hu hu0).acc = fun _ => 0 :=
  ProperWorldline.inertial_acc z₀ u₀ hu hu0

example (e : ℝ) (z₀ u₀ : Spacetime) (hu : η u₀ u₀ = -1) (hu0 : 0 < u₀ 0) {ε : ℝ} (hε : 0 < ε)
    (τ₁ τ₂ : ℝ) : diracTubeFlux e (ProperWorldline.inertial z₀ u₀ hu hu0) ε τ₁ τ₂ = 0 :=
  diracTubeFlux_inertial e z₀ u₀ hu hu0 hε τ₁ τ₂

example (e : ℝ) (z₀ u₀ : Spacetime) (hu : η u₀ u₀ = -1) (hu0 : 0 < u₀ 0) (m₀ : ℝ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (τ₁ τ₂ : ℝ) :
    m₀ ε • ((ProperWorldline.inertial z₀ u₀ hu hu0).vel τ₂ -
      (ProperWorldline.inertial z₀ u₀ hu hu0).vel τ₁) =
      (∫ _ in τ₁..τ₂, (0 : Spacetime)) -
        diracTubeFlux e (ProperWorldline.inertial z₀ u₀ hu hu0) ε τ₁ τ₂ :=
  exactTubeBalance_inertial e z₀ u₀ hu hu0 m₀ hε τ₁ τ₂

example : ContDiff ℝ 4 Examples.hyperbola :=
  contDiff_hyperbola

example : ProperWorldline.hyperbolic.z = Examples.hyperbola :=
  rfl

example : ProperWorldline.hyperbolic.vel = Examples.hyperbolaVelocity :=
  ProperWorldline.hyperbolic_vel

example (e : ℝ) {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀,
      ‖diracTubeFlux e ProperWorldline.hyperbolic ε τ₁ τ₂ - emMass e ε •
        (Examples.hyperbolaVelocity τ₂ - Examples.hyperbolaVelocity τ₁)‖ ≤ C * ε :=
  diracTubeFlux_hyperbolic e h

example {e τ₁ τ₂ : ℝ} (he : e ≠ 0) (h : τ₁ < τ₂) :
    ∫ τ in τ₁..τ₂, radiatedMomentumRate e Examples.hyperbolaVelocity τ ≠ 0 :=
  integral_radiatedMomentumRate_hyperbolic_ne_zero he h

end ProjectAinos.Electrodynamics.RadiationReaction.WorldTube

end WorldTube
