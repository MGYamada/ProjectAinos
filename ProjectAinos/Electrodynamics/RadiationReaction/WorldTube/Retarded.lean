/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.StressTensor
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The retarded field of a point charge in the proper time

A point charge moves on a world line `z(τ)` parametrized by the proper time (`ProperWorldline`:
of class `C⁴`, with the unit future-directed four-velocity `u = ż`, signature `(−+++)`, `c = 1`).
We write `a = u̇` (`ProperWorldline.acc`), `ȧ` (`jerk`) and `ä` (`snap`).

* **Taylor bounds** (`ProperWorldline.norm_taylor_jerk` … `norm_taylor_z`): if `‖ä‖ ≤ M` on
  `[τ − s, τ]`, then `z(τ) − z(τ − s) = s u − s²a/2 + s³ȧ/6 + O(M s⁴)`, and similarly for `u`,
  `a`, `ȧ`, at the time `τ`.
* **Causality**: `pos_time_of_null_of_neg` (a null vector with `X · u < 0` is future-directed),
  `ProperWorldline.time_sub_gt_norm` (the chord `z(τ₂) − z(τ₁)`, `τ₁ < τ₂`, is future-directed
  timelike) and `minkowski_null_add_timelike_neg`.
* **The retarded proper time**: `IsRetarded w x τ` says that `x − z(τ)` is null and
  future-directed; it holds for at most one `τ` (`IsRetarded.unique`), and
  `retardedProperTime w x` is that `τ` (`retardedProperTime_eq`). At every event that has a
  retarded time it is of class `C⁴` (`contDiffAt_retardedProperTime`, by the implicit function
  theorem applied to `(x − z(τ))² = 0`, whose `τ`-derivative `2ρ`, `ρ = −(x − z(τ)) · u(τ)`, is
  positive there, `retardedDistance_pos`), and the nearby events have retarded times
  (`eventually_isRetarded`).
* **The field of Liénard and Wiechert**: `bivector R Y` is the two-form `R ∧ Y`
  (`bivector_apply`), and `retardedField e w x = R ∧ Y` with `R = x − z(τ)` and
  `Y = −(e/4π)(a/ρ² + (1 + R · a) u/ρ³)` (`lwVector`) at the retarded time `τ` of `x`, that is
  `F = −(e/4π)(R ∧ a/ρ² + (1 + R · a) R ∧ u/ρ³)` (Landau–Lifshitz §63 in covariant form). It is
  the curvature of the four-potential `A_μ = (e/4π) u_μ/ρ` of Liénard and Wiechert
  (`fieldTensor_lwPotential` in `WorldTube.Potential`).
* **The stress tensor of a null two-form**: `stressFlux F N` is the vector `T^μ{}_ν N^ν` of the
  stress tensor `stressForm`, with the components `η^{μμ} T(e_μ, N)`, and
  `stressFlux_bivector`: for `R · R = 0`,
  `T(·, N) = (R·N)(Y·Y) R − (R·Y)((Y·N) R + (R·N) Y) + ½ (R·Y)² N`.
* `restFrame u n`: the unit vector of the rest space of `u` with the spatial direction `n`
  (the boost of `(0, n)` to `u`), orthogonal to `u` with `restFrame u n · restFrame u n = |n|²`
  (`minkowskiForm_restFrame_self`, `minkowskiForm_restFrame_vel`) and odd in `n`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.RadiationReaction.WorldTube

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity

local notation "η" => minkowskiForm LorentzConvention.timeNegative 3

/-! ### The Minkowski product -/

/-- `η(v, w) = −v⁰w⁰ + 𝐯 · 𝐰`. -/
theorem minkowski_eq_time_space (v w : Spacetime) :
    η v w = -(v 0 * w 0) + inner ℝ (space v) (space w) := by
  rw [minkowskiForm_convention, ← pair, pair_apply]
  simp only [LorentzConvention.timeSign_timeNegative, time_apply]
  ring

/-- The Minkowski product in co-ordinates. -/
theorem minkowski_coords (v w : Spacetime) :
    η v w = -(v 0 * w 0) + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 := by
  simp [minkowskiForm_apply, Fin.sum_univ_four, lorentzSign]

/-- The Minkowski product with a basis vector is a signed component. -/
theorem minkowski_single (v : Spacetime) (μ : Fin 4) :
    η v (Pi.single μ 1) = lorentzSign .timeNegative μ * v μ := by
  rw [minkowskiForm_apply, Finset.sum_eq_single μ]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ μ) h

/-- The Minkowski product is bounded: `|η(v, w)| ≤ ‖η‖ ‖v‖ ‖w‖`. -/
theorem abs_minkowski_le (v w : Spacetime) : |η v w| ≤ ‖η‖ * ‖v‖ * ‖w‖ := by
  rw [← Real.norm_eq_abs]
  exact (minkowskiForm .timeNegative 3).le_opNorm₂ v w

/-- A null vector whose product with a future unit timelike vector is negative is
future-directed. -/
theorem pos_time_of_null_of_neg {X u : Spacetime} (hX : η X X = 0) (hu : η u u = -1)
    (hu0 : 0 < u 0) (h : η X u < 0) : 0 < X 0 := by
  rw [minkowski_eq_time_space] at hX hu h
  rw [real_inner_self_eq_norm_sq] at hX hu
  by_contra hneg
  have hneg : X 0 ≤ 0 := not_lt.mp hneg
  have hXs : ‖space X‖ = -X 0 := by
    have h1 : ‖space X‖ ^ 2 = (-X 0) ^ 2 := by nlinarith
    exact (pow_left_inj₀ (norm_nonneg _) (by linarith) two_ne_zero).mp h1
  have hus : ‖space u‖ < u 0 := by
    have h1 : ‖space u‖ ^ 2 < u 0 ^ 2 := by nlinarith
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hu0.le two_ne_zero).mp h1
  have hcs := real_inner_le_norm (space X) (space u)
  have hcs' : -(‖space X‖ * ‖space u‖) ≤ inner ℝ (space X) (space u) := by
    have := abs_real_inner_le_norm (space X) (space u)
    rw [abs_le] at this
    linarith [this.1]
  rw [hXs] at hcs'
  nlinarith

/-- A future-directed null vector has a negative product with a future unit timelike vector,
unless it vanishes. -/
theorem minkowski_neg_of_null {X u : Spacetime} (hX : η X X = 0) (hX0 : 0 < X 0)
    (hu : η u u = -1) (hu0 : 0 < u 0) : η X u < 0 := by
  rw [minkowski_eq_time_space] at hX hu ⊢
  rw [real_inner_self_eq_norm_sq] at hX hu
  have hXs : ‖space X‖ = X 0 := by
    have h1 : ‖space X‖ ^ 2 = (X 0) ^ 2 := by nlinarith
    exact (pow_left_inj₀ (norm_nonneg _) hX0.le two_ne_zero).mp h1
  have hus : ‖space u‖ < u 0 := by
    have h1 : ‖space u‖ ^ 2 < u 0 ^ 2 := by nlinarith
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hu0.le two_ne_zero).mp h1
  have hcs := real_inner_le_norm (space X) (space u)
  rw [hXs] at hcs
  nlinarith

/-- A future-directed null vector plus a future-directed timelike vector is timelike. -/
theorem minkowski_null_add_timelike_neg {X D : Spacetime} (hX : η X X = 0) (hX0 : 0 < X 0)
    (hD : ‖space D‖ < D 0) : η (X + D) (X + D) < 0 := by
  have e : η (X + D) (X + D) = η X X + 2 * η X D + η D D := by
    simp only [map_add, add_apply]
    rw [minkowskiForm_symmetric _ D X]
    ring
  rw [e, hX]
  rw [minkowski_eq_time_space] at hX
  rw [minkowski_eq_time_space, minkowski_eq_time_space, real_inner_self_eq_norm_sq]
  rw [real_inner_self_eq_norm_sq] at hX
  have hXs : ‖space X‖ = X 0 := by
    have h1 : ‖space X‖ ^ 2 = (X 0) ^ 2 := by nlinarith
    exact (pow_left_inj₀ (norm_nonneg _) hX0.le two_ne_zero).mp h1
  have hcs := real_inner_le_norm (space X) (space D)
  rw [hXs] at hcs
  have hD0 : 0 ≤ ‖space D‖ := norm_nonneg _
  nlinarith

/-! ### World lines in the proper time -/

/-- A **world line in the proper time**: a curve `z` of class `C⁴` whose tangent `u = ż` is a
future-directed unit timelike vector. -/
structure ProperWorldline where
  /-- The event `z(τ)` at the proper time `τ`. -/
  z : ℝ → Spacetime
  /-- The world line is of class `C⁴`. -/
  contDiff_z : ContDiff ℝ 4 z
  /-- The four-velocity is a unit vector, `u · u = −1`. -/
  unit : ∀ τ, η (deriv z τ) (deriv z τ) = -1
  /-- The four-velocity is future-directed. -/
  future : ∀ τ, 0 < deriv z τ 0

namespace ProperWorldline

variable (w : ProperWorldline)

/-- The four-velocity `u = ż`. -/
def vel : ℝ → Spacetime := deriv w.z

/-- The four-acceleration `a = u̇`. -/
def acc : ℝ → Spacetime := deriv w.vel

/-- The derivative `ȧ` of the four-acceleration. -/
def jerk : ℝ → Spacetime := deriv w.acc

/-- The second derivative `ä` of the four-acceleration. -/
def snap : ℝ → Spacetime := deriv w.jerk

theorem contDiff_vel : ContDiff ℝ 3 w.vel := ContDiff.deriv' (n := 3) w.contDiff_z

theorem contDiff_acc : ContDiff ℝ 2 w.acc := ContDiff.deriv' (n := 2) w.contDiff_vel

theorem contDiff_jerk : ContDiff ℝ 1 w.jerk := ContDiff.deriv' (n := 1) w.contDiff_acc

theorem continuous_snap : Continuous w.snap :=
  (ContDiff.deriv' (n := 0) w.contDiff_jerk).continuous

theorem continuous_jerk : Continuous w.jerk := w.contDiff_jerk.continuous

theorem continuous_acc : Continuous w.acc := w.contDiff_acc.continuous

theorem continuous_vel : Continuous w.vel := w.contDiff_vel.continuous

theorem continuous_z : Continuous w.z := w.contDiff_z.continuous

theorem hasDerivAt_z (τ : ℝ) : HasDerivAt w.z (w.vel τ) τ :=
  ((w.contDiff_z.differentiable (by norm_num)) τ).hasDerivAt

theorem hasDerivAt_vel (τ : ℝ) : HasDerivAt w.vel (w.acc τ) τ :=
  ((w.contDiff_vel.differentiable (by norm_num)) τ).hasDerivAt

theorem hasDerivAt_acc (τ : ℝ) : HasDerivAt w.acc (w.jerk τ) τ :=
  ((w.contDiff_acc.differentiable (by norm_num)) τ).hasDerivAt

theorem hasDerivAt_jerk (τ : ℝ) : HasDerivAt w.jerk (w.snap τ) τ :=
  ((w.contDiff_jerk.differentiable (by norm_num)) τ).hasDerivAt

theorem vel_unit (τ : ℝ) : η (w.vel τ) (w.vel τ) = -1 := w.unit τ

theorem vel_future (τ : ℝ) : 0 < w.vel τ 0 := w.future τ

/-- `u · a = 0`. -/
theorem vel_acc (τ : ℝ) : η (w.vel τ) (w.acc τ) = 0 := by
  have h : HasDerivAt (fun σ => η (w.vel σ) (w.vel σ))
      (η (w.acc τ) (w.vel τ) + η (w.vel τ) (w.acc τ)) τ :=
    ((minkowskiForm .timeNegative 3).hasFDerivAt.comp_hasDerivAt τ (w.hasDerivAt_vel τ)).clm_apply
      (w.hasDerivAt_vel τ)
  have hc : (fun σ => η (w.vel σ) (w.vel σ)) = fun _ => -1 := funext w.vel_unit
  rw [hc] at h
  have := h.unique (hasDerivAt_const τ (-1))
  rw [minkowskiForm_symmetric _ (w.acc τ)] at this
  linarith

/-- `u · ȧ = −a · a`. -/
theorem vel_jerk (τ : ℝ) : η (w.vel τ) (w.jerk τ) = -η (w.acc τ) (w.acc τ) := by
  have h : HasDerivAt (fun σ => η (w.vel σ) (w.acc σ))
      (η (w.acc τ) (w.acc τ) + η (w.vel τ) (w.jerk τ)) τ :=
    ((minkowskiForm .timeNegative 3).hasFDerivAt.comp_hasDerivAt τ (w.hasDerivAt_vel τ)).clm_apply
      (w.hasDerivAt_acc τ)
  have hc : (fun σ => η (w.vel σ) (w.acc σ)) = fun _ => 0 := funext w.vel_acc
  rw [hc] at h
  have := h.unique (hasDerivAt_const τ 0)
  linarith

/-! ### Taylor bounds at a time `τ`, towards the past -/

/-- A function vanishing at `0` whose derivative is at most `K rⁿ` on `[0, s]` is at most
`K sⁿ⁺¹` at `s`. -/
theorem norm_le_of_deriv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {s K : ℝ} {n : ℕ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hf : ∀ r ∈ Icc 0 s, HasDerivAt f (f' r) r) (h0 : f 0 = 0)
    (hb : ∀ r ∈ Icc 0 s, ‖f' r‖ ≤ K * r ^ n) : ‖f s‖ ≤ K * s ^ (n + 1) := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := f') (C := K * s ^ n)
    (fun r hr => (hf r hr).hasDerivWithinAt) (fun r hr => (hb r (Ico_subset_Icc_self hr)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.1 hr.2.le n) hK)) s
    (right_mem_Icc.mpr hs)
  rw [h0, sub_zero, sub_zero] at h
  calc ‖f s‖ ≤ K * s ^ n * s := h
    _ = K * s ^ (n + 1) := by ring

variable {w}

/-- The derivative of `r ↦ f(τ − r)`. -/
theorem hasDerivAt_comp_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {f' : E} {τ r : ℝ} (hf : HasDerivAt f f' (τ - r)) :
    HasDerivAt (fun r => f (τ - r)) (-f') r := by
  have h := hf.scomp r ((hasDerivAt_id' r).const_sub τ)
  simp only [neg_smul, one_smul] at h
  exact h

/-- `ȧ(τ − s) = ȧ(τ) + O(M s)` if `‖ä‖ ≤ M` on `[τ − s, τ]`. -/
theorem norm_taylor_jerk {τ s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (τ - s) τ, ‖w.snap t‖ ≤ M) :
    ‖w.jerk (τ - s) - w.jerk τ‖ ≤ M * s := by
  have h := norm_le_of_deriv_le (f := fun r => w.jerk (τ - r) - w.jerk τ)
    (f' := fun r => -w.snap (τ - r)) (n := 0) hs hM
    (fun r _ => (hasDerivAt_comp_sub (w.hasDerivAt_jerk (τ - r))).sub_const (w.jerk τ))
    (by simp) (fun r hr => by
      rw [norm_neg, pow_zero, mul_one]
      exact hb _ ⟨by linarith [hr.2], by linarith [hr.1]⟩)
  simpa using h

/-- `a(τ − s) = a(τ) − s ȧ(τ) + O(M s²)`. -/
theorem norm_taylor_acc {τ s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (τ - s) τ, ‖w.snap t‖ ≤ M) :
    ‖w.acc (τ - s) - (w.acc τ - s • w.jerk τ)‖ ≤ M * s ^ 2 := by
  have h := norm_le_of_deriv_le (f := fun r => w.acc (τ - r) - (w.acc τ - r • w.jerk τ))
    (f' := fun r => -(w.jerk (τ - r) - w.jerk τ)) (n := 1) hs hM (fun r _ => by
      have h1 := hasDerivAt_comp_sub (w.hasDerivAt_acc (τ - r))
      have h2 : HasDerivAt (fun r => w.acc τ - r • w.jerk τ) (-w.jerk τ) r := by
        simpa using ((hasDerivAt_id' r).smul_const (w.jerk τ)).const_sub (w.acc τ)
      exact (h1.fun_sub h2).congr_deriv (by abel)) (by simp) (fun r hr => by
      rw [norm_neg, pow_one]
      exact norm_taylor_jerk hr.1 hM fun t ht => hb t ⟨by linarith [ht.1, hr.2], ht.2⟩)
  simpa using h

/-- `u(τ − s) = u(τ) − s a(τ) + (s²/2) ȧ(τ) + O(M s³)`. -/
theorem norm_taylor_vel {τ s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (τ - s) τ, ‖w.snap t‖ ≤ M) :
    ‖w.vel (τ - s) - (w.vel τ - s • w.acc τ + (s ^ 2 / 2) • w.jerk τ)‖ ≤ M * s ^ 3 := by
  have h := norm_le_of_deriv_le
    (f := fun r => w.vel (τ - r) - (w.vel τ - r • w.acc τ + (r ^ 2 / 2) • w.jerk τ))
    (f' := fun r => -(w.acc (τ - r) - (w.acc τ - r • w.jerk τ))) (n := 2) hs hM (fun r _ => by
      have h1 := hasDerivAt_comp_sub (w.hasDerivAt_vel (τ - r))
      have h2 : HasDerivAt (fun r => w.vel τ - r • w.acc τ + (r ^ 2 / 2) • w.jerk τ)
          (-w.acc τ + r • w.jerk τ) r := by
        have h3 : HasDerivAt (fun r : ℝ => r ^ 2 / 2) r r := by
          simpa using (hasDerivAt_pow 2 r).div_const 2
        simpa using (((hasDerivAt_id' r).smul_const (w.acc τ)).const_sub (w.vel τ)).fun_add
          (h3.smul_const (w.jerk τ))
      exact (h1.fun_sub h2).congr_deriv (by abel)) (by simp) (fun r hr => by
      rw [norm_neg]
      exact norm_taylor_acc hr.1 hM fun t ht => hb t ⟨by linarith [ht.1, hr.2], ht.2⟩)
  simpa using h

/-- `z(τ) − z(τ − s) = s u(τ) − (s²/2) a(τ) + (s³/6) ȧ(τ) + O(M s⁴)`. -/
theorem norm_taylor_z {τ s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (τ - s) τ, ‖w.snap t‖ ≤ M) :
    ‖w.z τ - w.z (τ - s) - (s • w.vel τ - (s ^ 2 / 2) • w.acc τ + (s ^ 3 / 6) • w.jerk τ)‖ ≤
      M * s ^ 4 := by
  have h := norm_le_of_deriv_le
    (f := fun r => w.z τ - w.z (τ - r) -
      (r • w.vel τ - (r ^ 2 / 2) • w.acc τ + (r ^ 3 / 6) • w.jerk τ))
    (f' := fun r => w.vel (τ - r) - (w.vel τ - r • w.acc τ + (r ^ 2 / 2) • w.jerk τ)) (n := 3)
    hs hM (fun r _ => by
      have h1 := (hasDerivAt_comp_sub (w.hasDerivAt_z (τ - r))).const_sub (w.z τ)
      have h2 : HasDerivAt (fun r => r • w.vel τ - (r ^ 2 / 2) • w.acc τ + (r ^ 3 / 6) • w.jerk τ)
          (w.vel τ - r • w.acc τ + (r ^ 2 / 2) • w.jerk τ) r := by
        have h3 : HasDerivAt (fun r : ℝ => r ^ 2 / 2) r r := by
          simpa using (hasDerivAt_pow 2 r).div_const 2
        have h4 : HasDerivAt (fun r : ℝ => r ^ 3 / 6) (r ^ 2 / 2) r := by
          convert (hasDerivAt_pow 3 r).div_const 6 using 1
          ring
        simpa using (((hasDerivAt_id' r).smul_const (w.vel τ)).fun_sub
          (h3.smul_const (w.acc τ))).fun_add (h4.smul_const (w.jerk τ))
      exact (h1.fun_sub h2).congr_deriv (by abel)) (by simp) (fun r hr =>
      norm_taylor_vel hr.1 hM fun t ht => hb t ⟨by linarith [ht.1, hr.2], ht.2⟩)
  simpa using h

end ProperWorldline

/-! ### Chords and the retarded proper time -/

/-- A future unit timelike vector has `‖𝐮‖ < u⁰`. -/
theorem norm_space_lt_of_unit {u : Spacetime} (hu : η u u = -1) (hu0 : 0 < u 0) :
    ‖space u‖ < u 0 := by
  rw [minkowski_eq_time_space, real_inner_self_eq_norm_sq] at hu
  have h1 : ‖space u‖ ^ 2 < u 0 ^ 2 := by nlinarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hu0.le two_ne_zero).mp h1

/-- **The chord of a world line is future-directed timelike**: for `τ₁ < τ₂`,
`‖𝐳(τ₂) − 𝐳(τ₁)‖ < z⁰(τ₂) − z⁰(τ₁)`. -/
theorem time_sub_gt_norm (w : ProperWorldline) {τ₁ τ₂ : ℝ} (h : τ₁ < τ₂) :
    ‖space (w.z τ₂ - w.z τ₁)‖ < (w.z τ₂ - w.z τ₁) 0 := by
  have hint : ∫ t in τ₁..τ₂, w.vel t = w.z τ₂ - w.z τ₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => w.hasDerivAt_z t)
      (w.continuous_vel.intervalIntegrable _ _)
  have hvi : IntervalIntegrable w.vel MeasureTheory.volume τ₁ τ₂ :=
    w.continuous_vel.intervalIntegrable _ _
  have h0 : (w.z τ₂ - w.z τ₁) 0 = ∫ t in τ₁..τ₂, w.vel t 0 := by
    rw [← hint]
    exact ((ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ).intervalIntegral_comp_comm hvi).symm
  have hs : space (w.z τ₂ - w.z τ₁) = ∫ t in τ₁..τ₂, space (w.vel t) := by
    rw [← hint]
    exact ((space : Spacetime →L[ℝ] Space 3).intervalIntegral_comp_comm hvi).symm
  rw [h0, hs]
  calc ‖∫ t in τ₁..τ₂, space (w.vel t)‖ ≤ ∫ t in τ₁..τ₂, ‖space (w.vel t)‖ :=
        intervalIntegral.norm_integral_le_integral_norm h.le
    _ < ∫ t in τ₁..τ₂, w.vel t 0 := by
        refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt h
          ((space.continuous.comp w.continuous_vel).norm.continuousOn)
          ((continuous_apply 0).comp w.continuous_vel).continuousOn
          (fun t _ => (norm_space_lt_of_unit (w.vel_unit t) (w.vel_future t)).le)
          ⟨τ₁, left_mem_Icc.mpr h.le, norm_space_lt_of_unit (w.vel_unit τ₁) (w.vel_future τ₁)⟩

namespace ProperWorldline

variable (w : ProperWorldline)

/-- `τ` is a **retarded time** of the event `x`: `x − z(τ)` is null and future-directed. -/
def IsRetarded (x : Spacetime) (τ : ℝ) : Prop :=
  η (x - w.z τ) (x - w.z τ) = 0 ∧ w.z τ 0 < x 0

variable {w}

/-- **An event has at most one retarded time**: a later point of the world line would see
`x` along a future timelike chord plus a null vector, which is timelike. -/
theorem IsRetarded.unique {x : Spacetime} {τ₁ τ₂ : ℝ} (h₁ : w.IsRetarded x τ₁)
    (h₂ : w.IsRetarded x τ₂) : τ₁ = τ₂ := by
  have key : ∀ {s t : ℝ}, w.IsRetarded x s → w.IsRetarded x t → s < t → False := by
    intro s t hs ht hst
    have hX0 : 0 < (x - w.z t) 0 := by simpa using sub_pos.mpr ht.2
    have hlt := minkowski_null_add_timelike_neg ht.1 hX0 (time_sub_gt_norm w hst)
    have e : x - w.z t + (w.z t - w.z s) = x - w.z s := by abel
    rw [e, hs.1] at hlt
    exact lt_irrefl 0 hlt
  rcases lt_trichotomy τ₁ τ₂ with h | h | h
  · exact (key h₁ h₂ h).elim
  · exact h
  · exact (key h₂ h₁ h).elim

variable (w) in
open Classical in
/-- **The retarded proper time** of an event: the retarded time when there is one
(`retardedProperTime_eq`), and `0` otherwise. -/
def retardedProperTime (x : Spacetime) : ℝ :=
  if h : ∃ τ, w.IsRetarded x τ then h.choose else 0

/-- The retarded proper time is the retarded time. -/
theorem retardedProperTime_eq {x : Spacetime} {τ : ℝ} (h : w.IsRetarded x τ) :
    w.retardedProperTime x = τ := by
  have hex : ∃ τ, w.IsRetarded x τ := ⟨τ, h⟩
  simp only [retardedProperTime, hex, ↓reduceDIte]
  exact hex.choose_spec.unique h

/-- The retarded distance `ρ = −(x − z(τ)) · u(τ)` is positive at a retarded time. -/
theorem retardedDistance_pos {x : Spacetime} {τ : ℝ} (h : w.IsRetarded x τ) :
    0 < -η (x - w.z τ) (w.vel τ) := by
  have hX0 : 0 < (x - w.z τ) 0 := by simpa using sub_pos.mpr h.2
  linarith [minkowski_neg_of_null h.1 hX0 (w.vel_unit τ) (w.vel_future τ)]

variable (w) in
/-- The equation `(x − z(τ))² = 0` of the retarded time. -/
private def lagEquation (q : Spacetime × ℝ) : ℝ := η (q.1 - w.z q.2) (q.1 - w.z q.2)

private theorem contDiff_lagEquation : ContDiff ℝ 4 w.lagEquation := by
  have h : ContDiff ℝ 4 fun q : Spacetime × ℝ => q.1 - w.z q.2 :=
    contDiff_fst.sub (w.contDiff_z.comp contDiff_snd)
  have hB : ContDiff ℝ 4 (fun p : Spacetime × Spacetime => η p.1 p.2) :=
    (minkowskiForm .timeNegative 3).isBoundedBilinearMap.contDiff
  have h2 := hB.comp (h.prodMk h)
  exact h2

/-- The derivative `−2 (x − z(τ)) · u(τ)` of the equation of the retarded time in `τ`. -/
private theorem hasDerivAt_lagEquation (x : Spacetime) (τ : ℝ) :
    HasDerivAt (fun t => w.lagEquation (x, t)) (-(2 * η (x - w.z τ) (w.vel τ))) τ := by
  have hS : HasDerivAt (fun t => x - w.z t) (-w.vel τ) τ := (w.hasDerivAt_z τ).const_sub x
  have h := ((minkowskiForm .timeNegative 3).hasFDerivAt.comp_hasDerivAt τ hS).clm_apply hS
  have e : η (-w.vel τ) (x - w.z τ) + (η ∘ fun t => x - w.z t) τ (-w.vel τ) =
      -(2 * η (x - w.z τ) (w.vel τ)) := by
    simp only [Function.comp_apply, map_neg, neg_apply]
    rw [minkowskiForm_symmetric _ (w.vel τ)]
    ring
  exact h.congr_deriv e

private theorem isInvertible_of_apply_one_ne_zero {L : ℝ →L[ℝ] ℝ} (h : L 1 ≠ 0) :
    L.IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
  · ext
    change L ((L 1)⁻¹ • (1 : ℝ)) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ h]
  · ext
    change (L 1)⁻¹ • L 1 = (1 : ℝ)
    rw [smul_eq_mul, inv_mul_cancel₀ h]

/-- **The implicit function theorem for the retarded time**: near an event with a retarded time,
there is a function of class `C⁴` that is the retarded time of every nearby event. -/
private theorem exists_contDiffAt_retarded {x : Spacetime} {τ₀ : ℝ} (h : w.IsRetarded x τ₀) :
    ∃ ψ : Spacetime → ℝ, ContDiffAt ℝ 4 ψ x ∧ ∀ᶠ y in 𝓝 x, w.IsRetarded y (ψ y) := by
  set q : Spacetime × ℝ := (x, τ₀) with hq
  have hF : ContDiffAt ℝ 4 w.lagEquation q := w.contDiff_lagEquation.contDiffAt
  have hd : (fderiv ℝ w.lagEquation q ∘L ContinuousLinearMap.inr ℝ Spacetime ℝ) 1 =
      -(2 * η (x - w.z τ₀) (w.vel τ₀)) := by
    have hγ : HasDerivAt (fun t : ℝ => (x, t)) ((0 : Spacetime), (1 : ℝ)) τ₀ :=
      (hasDerivAt_const τ₀ x).prodMk (hasDerivAt_id' τ₀)
    have h1 := (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt τ₀ hγ
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact h1.unique (w.hasDerivAt_lagEquation x τ₀)
  have hinv : (fderiv ℝ w.lagEquation q ∘L ContinuousLinearMap.inr ℝ Spacetime ℝ).IsInvertible := by
    refine isInvertible_of_apply_one_ne_zero ?_
    rw [hd]
    have := retardedDistance_pos h
    intro h0
    linarith
  have hψc := hF.contDiffAt_implicitFunction (by norm_num) hinv
  have hψ := hψc.continuousAt
  have heq := hF.eventually_apply_implicitFunction (by norm_num) hinv
  have hself := hF.implicitFunction_apply_self (by norm_num) hinv
  set ψ := hF.implicitFunction (by norm_num) hinv with hψdef
  have hq0 : w.lagEquation q = 0 := h.1
  have hpos : ∀ᶠ y in 𝓝 x, w.z (ψ y) 0 < y 0 := by
    have hc : ContinuousAt (fun y => y 0 - w.z (ψ y) 0) x :=
      (continuous_apply 0).continuousAt.sub
        ((continuous_apply 0).continuousAt.comp (w.continuous_z.continuousAt.comp hψ))
    have hx : 0 < x 0 - w.z (ψ x) 0 := by
      have : ψ x = τ₀ := hself
      rw [this]
      linarith [h.2]
    filter_upwards [hc.eventually (lt_mem_nhds hx)] with y hy
    linarith
  refine ⟨ψ, hψc, ?_⟩
  filter_upwards [heq, hpos] with y hy hy'
  rw [hq0] at hy
  exact ⟨hy, hy'⟩

/-- Near an event with a retarded time, every event has a retarded time. -/
theorem eventually_isRetarded {x : Spacetime} {τ₀ : ℝ} (h : w.IsRetarded x τ₀) :
    ∀ᶠ y in 𝓝 x, w.IsRetarded y (w.retardedProperTime y) := by
  obtain ⟨ψ, -, hψ⟩ := exists_contDiffAt_retarded h
  filter_upwards [hψ] with y hy
  rw [retardedProperTime_eq hy]
  exact hy

/-- **The retarded proper time is of class `C⁴`** at every event that has a retarded time. -/
theorem contDiffAt_retardedProperTime {x : Spacetime} {τ₀ : ℝ} (h : w.IsRetarded x τ₀) :
    ContDiffAt ℝ 4 w.retardedProperTime x := by
  obtain ⟨ψ, hψc, hψ⟩ := exists_contDiffAt_retarded h
  refine hψc.congr_of_eventuallyEq ?_
  filter_upwards [hψ] with y hy
  exact retardedProperTime_eq hy

/-- **The retarded proper time is continuous** at every event that has a retarded time. -/
theorem continuousAt_retardedProperTime {x : Spacetime} {τ₀ : ℝ} (h : w.IsRetarded x τ₀) :
    ContinuousAt w.retardedProperTime x :=
  (contDiffAt_retardedProperTime h).continuousAt

end ProperWorldline

/-! ### The two-form `R ∧ Y` and its stress tensor -/

/-- A one-form given by a covector evaluates on `![v]` as the covector on `v`. -/
theorem oneCovector_symm_apply_vec (φ : Spacetime →L[ℝ] ℝ) (v : Spacetime) :
    oneCovector.symm φ ![v] = φ v := by
  have h := oneCovector_apply (oneCovector.symm φ) v
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  have hv : (![v] : Fin 1 → Spacetime) = fun _ => v := by
    ext i
    fin_cases i
    rfl
  rw [hv, ← h]

/-- The two-form `R ∧ Y`: `(R ∧ Y)(v, w) = (R · v)(Y · w) − (R · w)(Y · v)`. -/
def bivector (R Y : Spacetime) : TwoForm :=
  DifferentialForm.wedgeLeft (η R) (oneCovector.symm (η Y))

theorem bivector_apply (R Y v w : Spacetime) :
    bivector R Y ![v, w] = η R v * η Y w - η R w * η Y v := by
  have hr1 : Fin.removeNth (1 : Fin 2) ![v, w] = ![v] := by
    ext i
    fin_cases i
    rfl
  simp [bivector, DifferentialForm.wedgeLeft,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ, hr1,
    oneCovector_symm_apply_vec, sub_eq_add_neg]

/-- The pairing of two contractions of `R ∧ Y`. -/
theorem covectorPairing_bivector (R Y v w : Spacetime) :
    covectorPairing ((bivector R Y).curryLeft v) ((bivector R Y).curryLeft w) =
      η (η R v • Y - η Y v • R) (η R w • Y - η Y w • R) := by
  simp only [covectorPairing, oneCovector_curryLeft, bivector_apply, minkowski_single]
  conv_rhs => rw [minkowskiForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs := lorentzSign_sq i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (lorentzSign .timeNegative i * ((η R v * Y i - η Y v * R i) *
    (η R w * Y i - η Y w * R i))) * hs

/-- The invariant `F_{αβ} F^{αβ}` of `R ∧ Y` is `2((R · R)(Y · Y) − (R · Y)²)`. -/
theorem tensorContraction_bivector (R Y : Spacetime) :
    tensorContraction (bivector R Y) (bivector R Y) = 2 * (η R R * η Y Y - η R Y ^ 2) := by
  simp only [tensorContraction, raisedComponent, component, bivector_apply, minkowski_single]
  simp only [minkowski_coords, Fin.sum_univ_four, lorentzSign]
  norm_num
  ring

/-- **The stress tensor of a null two-form** `R ∧ Y`, `R · R = 0`:
`T(v, w) = (R·v)(R·w)(Y·Y) − (R·Y)((R·v)(Y·w) + (Y·v)(R·w)) + ½ (v·w)(R·Y)²`. -/
theorem stressForm_bivector_of_null {R : Spacetime} (hR : η R R = 0) (Y v w : Spacetime) :
    stressForm (bivector R Y) v w = η R v * η R w * η Y Y -
      η R Y * (η R v * η Y w + η Y v * η R w) + 1 / 2 * η v w * η R Y ^ 2 := by
  rw [stressForm, covectorPairing_bivector, tensorContraction_bivector, hR]
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
  rw [minkowskiForm_symmetric _ Y R, hR]
  ring

/-- The four-momentum flux `T^μ{}_ν N^ν` of the stress tensor through a hypersurface with the
normal `N` (indices raised with `(−+++)`). -/
def stressFlux (F : TwoForm) (N : Spacetime) : Spacetime :=
  fun μ => lorentzSign .timeNegative μ * stressForm F (Pi.single μ 1) N

/-- The flux of the stress tensor of a null two-form `R ∧ Y`. -/
theorem stressFlux_bivector {R : Spacetime} (hR : η R R = 0) (Y N : Spacetime) :
    stressFlux (bivector R Y) N = (η R N * η Y Y) • R -
      η R Y • (η Y N • R + η R N • Y) + (1 / 2 * η R Y ^ 2) • N := by
  funext μ
  simp only [stressFlux, stressForm_bivector_of_null hR]
  rw [minkowskiForm_symmetric _ (Pi.single μ 1) N]
  simp only [minkowski_single, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hs := lorentzSign_sq μ
  linear_combination (η R N * η Y Y * R μ - η R Y * (η Y N * R μ + η R N * Y μ) +
    1 / 2 * η R Y ^ 2 * N μ) * hs

/-! ### The field of Liénard and Wiechert -/

/-- The vector `Y = −(e/4π)(a/ρ² + (1 + R · a) u/ρ³)` of the field `R ∧ Y` of a charge with the
separation `R`, the four-velocity `u` and the four-acceleration `a` at the retarded time, where
`ρ = −R · u`. -/
def lwVector (e : ℝ) (R u a : Spacetime) : Spacetime :=
  (-(e / (4 * Real.pi))) • (((-η R u) ^ 2)⁻¹ • a + ((1 + η R a) / (-η R u) ^ 3) • u)

/-- **The retarded field of Liénard and Wiechert** of a charge `e` on the world line `w`, in the
covariant form `F = −(e/4π)(R ∧ a/ρ² + (1 + R · a) R ∧ u/ρ³) = R ∧ Y` (Landau–Lifshitz §63),
evaluated at the retarded proper time of the event. -/
def retardedField (e : ℝ) (w : ProperWorldline) (x : Spacetime) : TwoForm :=
  bivector (x - w.z (w.retardedProperTime x))
    (lwVector e (x - w.z (w.retardedProperTime x)) (w.vel (w.retardedProperTime x))
      (w.acc (w.retardedProperTime x)))

/-! ### The rest frame of a four-velocity -/

/-- The boost of the spatial vector `(0, n)` to the rest frame of `u`:
`(𝐮 · n, n + (𝐮 · n/(1 + u⁰)) 𝐮)`. -/
def restFrame (u : Spacetime) (n : Space 3) : Spacetime :=
  vector (inner ℝ (space u) n) (n + ((1 + u 0)⁻¹ * inner ℝ (space u) n) • space u)

theorem restFrame_neg (u : Spacetime) (n : Space 3) : restFrame u (-n) = -restFrame u n := by
  ext μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp [restFrame, inner_neg_right]
  · simp [restFrame, inner_neg_right]
    ring

/-- The boosted vector is orthogonal to `u`. -/
theorem minkowskiForm_restFrame_vel {u : Spacetime} (hu : η u u = -1) (hu0 : 0 < u 0)
    (n : Space 3) : η (restFrame u n) u = 0 := by
  have hq := hu
  rw [minkowski_eq_time_space, real_inner_self_eq_norm_sq] at hq
  rw [minkowski_eq_time_space, restFrame, vector_zero, space_vector, inner_add_left,
    inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm n]
  have h1 : (1 + u 0) ≠ 0 := by linarith
  have hn : ‖space u‖ ^ 2 = u 0 ^ 2 - 1 := by linarith
  simp only [RCLike.conj_to_real]
  rw [hn]
  field_simp
  ring

/-- The boosted vector has the length of `n`. -/
theorem minkowskiForm_restFrame_self {u : Spacetime} (hu : η u u = -1) (hu0 : 0 < u 0)
    (n : Space 3) : η (restFrame u n) (restFrame u n) = ‖n‖ ^ 2 := by
  have hq := hu
  rw [minkowski_eq_time_space, real_inner_self_eq_norm_sq] at hq
  rw [minkowski_eq_time_space, restFrame, vector_zero, space_vector, real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
    inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm n]
  have h1 : (1 + u 0) ≠ 0 := by linarith
  have hn : ‖space u‖ ^ 2 = u 0 ^ 2 - 1 := by linarith
  simp only [RCLike.conj_to_real]
  rw [hn]
  field_simp
  ring

/-- The boost is continuous in `(u, n)` where `u⁰ > −1`. -/
theorem continuousAt_restFrame {u : Spacetime} (hu0 : 0 < u 0) (n : Space 3) :
    ContinuousAt (fun p : Spacetime × Space 3 => restFrame p.1 p.2) (u, n) := by
  have hc : ContinuousAt (fun p : Spacetime × Space 3 => (1 + p.1 0)⁻¹) (u, n) :=
    (continuousAt_const.add ((continuous_apply 0).comp continuous_fst).continuousAt).inv₀
      (by simp only [Pi.add_apply, Function.comp_apply]; linarith)
  have hi : Continuous (fun p : Spacetime × Space 3 => inner ℝ (space p.1) p.2) :=
    (space.continuous.comp continuous_fst).inner continuous_snd
  have hv : ContinuousAt (fun p : Spacetime × Space 3 =>
      p.2 + ((1 + p.1 0)⁻¹ * inner ℝ (space p.1) p.2) • space p.1) (u, n) :=
    continuous_snd.continuousAt.add ((hc.mul hi.continuousAt).smul
      (space.continuous.comp continuous_fst).continuousAt)
  rw [continuousAt_pi]
  intro μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simpa [restFrame] using hi.continuousAt
  · simp only [restFrame, vector_succ]
    exact (EuclideanSpace.proj i : Space 3 →L[ℝ] ℝ).continuous.continuousAt.comp hv

end ProjectAinos.Electrodynamics.RadiationReaction.WorldTube
