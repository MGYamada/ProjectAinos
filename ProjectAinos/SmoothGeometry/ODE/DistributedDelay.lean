/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Linear equations with a distributed delay

A **delay datum** (`DelayData μ w τ D`) is an integrable weight `w` on a measure space `(Ω, μ)`
and a measurable delay `τ ≥ 0` with `τ ≤ D` where the weight does not vanish. Its operator is

  `(K u)(t) = ∫ w(ω) u(t − τ(ω)) dμ(ω)`  (`delayOp`),

which at the time `t` depends only on `u` on `[t − D, t]` (`DelayData.delayOp_congr`). The
equations studied are `m₀ u(t) + (K u)(t) = f(t)` for a continuous `u : ℝ → E` with values in a
Banach space, with the norms `q = ∫ |w|` and `q_γ = ∫ |w| e^{−γτ}` (`weightNorm`) of the weight.
Instance: the point delay `delayData_point`, `delayOp_point`.

* **Estimates**: `norm_le_of_delay` (on `[0, T]`, `‖u(t)‖ ≤ e^{γt}(C + qH)/(|m₀| − q_γ)` when
  `‖m₀u + Ku‖ ≤ Ce^{γt}` on `[0, T]`, `‖u‖ ≤ H` on `[−D, 0]` and `q_γ < |m₀|`), which gives
  uniqueness (`eq_of_delay`) and Lipschitz dependence on the data on finite intervals, uniformly
  in time for `γ = 0`; `norm_le_of_delay_Iic` on half-lines for bounded `u`.
* **Existence**: `exists_bounded_solution` (a contraction on the bounded continuous functions for
  `q < |m₀|`), and `exists_solution` for every forcing vanishing in the past with the growth
  `e^{γt}` when `q_γ < |m₀|`, through the substitution `u = e^{γt} v` (`DelayData.weighted`,
  `delayOp_exp_smul`). The rate exists for every `m₀ ≠ 0` when `τ > 0` almost everywhere
  (`DelayData.exists_weightNorm_lt`, by dominated convergence).
* **Runaways**: `exists_runaway`: for a nonnegative weight and `−∫ w < m₀ < 0` the characteristic
  function `m₀ + ∫ w e^{−γτ}` has a root `γ > 0`, and `e^{γt} c` solves the free equation.
* **The reduced equation**: `norm_sub_reduced_le`: for `q < |m₀|` and a `C³` forcing `F` vanishing
  in the past, the solution is within
  `((M₁/m)² B₂ + (Q₂/2)(B₂/|m| + |M₁| B₃/m²))/(|m₀| − q)` of
  `F/m + (M₁/m²) F'`, with `m = m₀ + ∫ w`, `M₁ = ∫ w τ`, `Q₂ = ∫ |w| τ²` and bounds `B₂`, `B₃` of
  `F''`, `F'''`; `DelayData.integral_abs_mul_sq_le` (`Q₂ ≤ D ∫ |w| τ`), `norm_taylor_two_le`.
* **Paths**: the double primitive `doublePrimitive u` `t ↦ ∫₀ᵗ ∫₀ˢ u` turns an acceleration into a
  `C²` path; `norm_le_of_deriv_deriv_le` bounds the velocity and the position by the
  acceleration, `eq_zero_of_deriv_deriv_eq_zero`, `deriv_deriv_eq_of_eq_on_Iic`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Real
open scoped Topology BoundedContinuousFunction

namespace ProjectAinos.SmoothGeometry.DistributedDelay

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A delay datum**: an integrable weight `w` and a measurable delay `τ ≥ 0`, with `τ ≤ D`
where the weight does not vanish. -/
structure DelayData (μ : Measure Ω) (w τ : Ω → ℝ) (D : ℝ) : Prop where
  /-- The weight is integrable. -/
  integrable : Integrable w μ
  /-- The delay is measurable. -/
  measurable : Measurable τ
  /-- The delay is nonnegative: the operator is causal. -/
  nonneg : ∀ ω, 0 ≤ τ ω
  /-- The bound of the delay is nonnegative. -/
  bound_nonneg : 0 ≤ D
  /-- The delay is at most `D` where the weight does not vanish: the memory is finite. -/
  le : ∀ ω, w ω ≠ 0 → τ ω ≤ D

/-- The operator `(K u)(t) = ∫ w(ω) u(t − τ(ω)) dμ(ω)` of a distributed delay. -/
def delayOp (μ : Measure Ω) (w τ : Ω → ℝ) (u : ℝ → E) (t : ℝ) : E :=
  ∫ ω, w ω • u (t - τ ω) ∂μ

/-- The weighted norm `q_γ = ∫ |w| e^{−γτ}` of the weight. -/
def weightNorm (μ : Measure Ω) (w τ : Ω → ℝ) (γ : ℝ) : ℝ :=
  ∫ ω, |w ω| * Real.exp (-(γ * τ ω)) ∂μ

/-- **An instance**: a single point delay `c u(t − D)`. -/
theorem delayData_point (c : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    DelayData (Measure.dirac ()) (fun _ : Unit => c) (fun _ => D) D where
  integrable := integrable_const c
  measurable := measurable_const
  nonneg _ := hD
  bound_nonneg := hD
  le _ _ := le_rfl

/-- The operator of the point delay is `c u(t − D)`. -/
theorem delayOp_point [CompleteSpace E] (c D : ℝ) (u : ℝ → E) (t : ℝ) :
    delayOp (Measure.dirac ()) (fun _ : Unit => c) (fun _ => D) u t = c • u (t - D) := by
  simp [delayOp]

namespace DelayData

variable {w τ : Ω → ℝ} {D : ℝ}

theorem integrable_abs (h : DelayData μ w τ D) : Integrable (fun ω => |w ω|) μ :=
  h.integrable.abs

/-- The weight times a bounded measurable factor is integrable. -/
theorem integrable_mul_exp (h : DelayData μ w τ D) {γ : ℝ} (hγ : 0 ≤ γ) :
    Integrable (fun ω => |w ω| * Real.exp (-(γ * τ ω))) μ := by
  refine h.integrable_abs.mono' ?_ (Eventually.of_forall fun ω => ?_)
  · exact h.integrable_abs.aestronglyMeasurable.mul
      (Real.continuous_exp.comp_aestronglyMeasurable
        ((h.measurable.const_mul γ).neg.aestronglyMeasurable))
  · have he : Real.exp (-(γ * τ ω)) ≤ 1 := Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hγ (h.nonneg ω)))
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg _) he

theorem weightNorm_nonneg (μ : Measure Ω) (w τ : Ω → ℝ) (γ : ℝ) : 0 ≤ weightNorm μ w τ γ :=
  integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

/-- The weighted norm is at most the norm `q = ∫ |w|`. -/
theorem weightNorm_le (h : DelayData μ w τ D) {γ : ℝ} (hγ : 0 ≤ γ) :
    weightNorm μ w τ γ ≤ ∫ ω, |w ω| ∂μ := by
  refine integral_mono (h.integrable_mul_exp hγ) h.integrable_abs fun ω => ?_
  have he : Real.exp (-(γ * τ ω)) ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg hγ (h.nonneg ω)))
  exact mul_le_of_le_one_right (abs_nonneg _) he

/-- The weighted norm at the rate `0` is the norm `q = ∫ |w|`. -/
theorem weightNorm_zero (μ : Measure Ω) (w τ : Ω → ℝ) :
    weightNorm μ w τ 0 = ∫ ω, |w ω| ∂μ := by
  simp [weightNorm]

/-- The integrand of the delay operator of a continuous function is strongly measurable. -/
theorem aestronglyMeasurable_smul (h : DelayData μ w τ D) {u : ℝ → E} (hu : Continuous u)
    (t : ℝ) : AEStronglyMeasurable (fun ω => w ω • u (t - τ ω)) μ :=
  h.integrable.aestronglyMeasurable.smul
    (hu.comp_aestronglyMeasurable (measurable_const.sub h.measurable).aestronglyMeasurable)

/-- A pointwise bound of the integrand from a bound of `u` on `[t − D, t]`. -/
theorem norm_smul_le (h : DelayData μ w τ D) {u : ℝ → E} {t C : ℝ}
    (hC : ∀ s ∈ Icc (t - D) t, ‖u s‖ ≤ C) (ω : Ω) :
    ‖w ω • u (t - τ ω)‖ ≤ |w ω| * C := by
  by_cases hw : w ω = 0
  · simp [hw]
  · rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left (hC _ ⟨?_, ?_⟩) (abs_nonneg _)
    · linarith [h.le ω hw]
    · linarith [h.nonneg ω]

/-- **The integrand is integrable** for a continuous function. -/
theorem integrable_smul (h : DelayData μ w τ D) {u : ℝ → E} (hu : Continuous u) (t : ℝ) :
    Integrable (fun ω => w ω • u (t - τ ω)) μ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (t - D) t)
    hu.continuousOn
  exact (h.integrable_abs.mul_const C).mono' (h.aestronglyMeasurable_smul hu t)
    (Eventually.of_forall (h.norm_smul_le hC))

/-- The delay operator is additive on continuous functions. -/
theorem delayOp_add (h : DelayData μ w τ D) {u v : ℝ → E} (hu : Continuous u)
    (hv : Continuous v) (t : ℝ) :
    delayOp μ w τ (fun s => u s + v s) t = delayOp μ w τ u t + delayOp μ w τ v t := by
  simp only [delayOp, smul_add]
  exact integral_add (h.integrable_smul hu t) (h.integrable_smul hv t)

/-- The delay operator is subtractive on continuous functions. -/
theorem delayOp_sub (h : DelayData μ w τ D) {u v : ℝ → E} (hu : Continuous u)
    (hv : Continuous v) (t : ℝ) :
    delayOp μ w τ (fun s => u s - v s) t = delayOp μ w τ u t - delayOp μ w τ v t := by
  simp only [delayOp, smul_sub]
  exact integral_sub (h.integrable_smul hu t) (h.integrable_smul hv t)

/-- The delay operator commutes with scalars. -/
theorem delayOp_smul (c : ℝ) (u : ℝ → E) (t : ℝ) :
    delayOp μ w τ (fun s => c • u s) t = c • delayOp μ w τ u t := by
  simp only [delayOp, smul_comm (w _) c]
  exact integral_smul c _

/-- **Finite memory**: the operator at `t` depends only on `u` on `[t − D, t]`. -/
theorem delayOp_congr (h : DelayData μ w τ D) {u v : ℝ → E} {t : ℝ}
    (huv : ∀ s ∈ Icc (t - D) t, u s = v s) : delayOp μ w τ u t = delayOp μ w τ v t := by
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  by_cases hw : w ω = 0
  · simp [hw]
  · simp only
    rw [huv _ ⟨by linarith [h.le ω hw], by linarith [h.nonneg ω]⟩]

/-- The delay operator of a continuous function is continuous. -/
theorem continuous_delayOp (h : DelayData μ w τ D) {u : ℝ → E} (hu : Continuous u) :
    Continuous (delayOp μ w τ u) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (t₀ - 1 - D) (t₀ + 1)) hu.continuousOn
  refine continuousAt_of_dominated (bound := fun ω => |w ω| * C)
    (Eventually.of_forall fun t => h.aestronglyMeasurable_smul hu t) ?_
    (h.integrable_abs.mul_const C) (Eventually.of_forall fun ω => ?_)
  · filter_upwards [Metric.ball_mem_nhds t₀ one_pos] with t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    refine Eventually.of_forall (h.norm_smul_le fun s hs => hC s ⟨?_, ?_⟩)
    · linarith [hs.1, (abs_lt.mp ht).1]
    · linarith [hs.2, (abs_lt.mp ht).2]
  · exact (continuous_const.smul (hu.comp (continuous_id.sub continuous_const))).continuousAt

/-- The delay operator is zero on functions that vanish in the past. -/
theorem delayOp_eq_zero_of_le (h : DelayData μ w τ D) {u : ℝ → E} {T : ℝ}
    (hu : ∀ s ≤ T, u s = 0) {t : ℝ} (ht : t ≤ T) : delayOp μ w τ u t = 0 := by
  have h0 : (fun ω => w ω • u (t - τ ω)) = fun _ => (0 : E) := by
    funext ω
    rw [hu _ (by linarith [h.nonneg ω]), smul_zero]
  simp only [delayOp, h0, integral_zero]

end DelayData

section Estimates

variable {w τ : Ω → ℝ} {D : ℝ}

/-- **The a priori estimate on a finite interval**: if `q_γ < |m₀|`, `‖u‖ ≤ H` on `[−D, 0]` and
`‖m₀ u(t) + (K u)(t)‖ ≤ C e^{γt}` on `[0, T]`, then `‖u(t)‖ ≤ e^{γt}(C + qH)/(|m₀| − q_γ)` on
`[0, T]`, with `q = ∫ |w|`. The proof evaluates the equation at the maximum of `e^{−γs}‖u(s)‖`
on `[0, T]`. -/
theorem norm_le_of_delay (h : DelayData μ w τ D) {γ : ℝ} (hγ : 0 ≤ γ) {m₀ : ℝ}
    (hq : weightNorm μ w τ γ < |m₀|) {u : ℝ → E} (hu : Continuous u) {T C H : ℝ}
    (hH : ∀ s ∈ Icc (-D) 0, ‖u s‖ ≤ H)
    (hf : ∀ t ∈ Icc 0 T, ‖m₀ • u t + delayOp μ w τ u t‖ ≤ C * Real.exp (γ * t)) :
    ∀ t ∈ Icc 0 T, ‖u t‖ ≤
      (C + (∫ ω, |w ω| ∂μ) * H) / (|m₀| - weightNorm μ w τ γ) * Real.exp (γ * t) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  set q := ∫ ω, |w ω| ∂μ with hqdef
  set qγ := weightNorm μ w τ γ with hqγ
  have hq0 : 0 ≤ q := integral_nonneg fun _ => abs_nonneg _
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0 ⟨by linarith [h.bound_nonneg], le_rfl⟩)
  set g : ℝ → ℝ := fun s => Real.exp (-(γ * s)) * ‖u s‖ with hg
  have hgc : Continuous g :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
      (continuous_norm.comp hu)
  obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
    hgc.continuousOn
  set M := g s₀ with hM
  have hM0 : 0 ≤ M := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  set A := Real.exp (γ * s₀) with hA
  have hApos : 0 < A := Real.exp_pos _
  have hA1 : 1 ≤ A := Real.one_le_exp (mul_nonneg hγ hs₀.1)
  have huM : ∀ s ∈ Icc 0 T, ‖u s‖ ≤ M * Real.exp (γ * s) := by
    intro s hs
    have h1 : g s ≤ M := hmax hs
    have h2 : ‖u s‖ = g s * Real.exp (γ * s) := by
      simp only [hg]
      rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        mul_one]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  -- the pointwise bound of the integrand at `s₀`
  have hpt : ∀ ω, ‖w ω • u (s₀ - τ ω)‖ ≤
      |w ω| * H + M * A * (|w ω| * Real.exp (-(γ * τ ω))) := by
    intro ω
    by_cases hw : w ω = 0
    · simp [hw]
    rw [norm_smul, Real.norm_eq_abs]
    have hb : ‖u (s₀ - τ ω)‖ ≤ H + M * A * Real.exp (-(γ * τ ω)) := by
      by_cases hneg : s₀ - τ ω < 0
      · have := hH (s₀ - τ ω) ⟨by linarith [h.le ω hw, hs₀.1], hneg.le⟩
        have : 0 ≤ M * A * Real.exp (-(γ * τ ω)) := by positivity
        linarith
      · have h3 := huM (s₀ - τ ω) ⟨not_lt.mp hneg, by linarith [h.nonneg ω, hs₀.2]⟩
        have h4 : Real.exp (γ * (s₀ - τ ω)) = A * Real.exp (-(γ * τ ω)) := by
          rw [hA, ← Real.exp_add]
          ring_nf
        rw [h4, ← mul_assoc] at h3
        linarith
    calc |w ω| * ‖u (s₀ - τ ω)‖ ≤ |w ω| * (H + M * A * Real.exp (-(γ * τ ω))) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = |w ω| * H + M * A * (|w ω| * Real.exp (-(γ * τ ω))) := by ring
  have hK : ‖delayOp μ w τ u s₀‖ ≤ q * H + M * A * qγ := by
    have hint : Integrable (fun ω => |w ω| * H + M * A * (|w ω| * Real.exp (-(γ * τ ω)))) μ :=
      (h.integrable_abs.mul_const H).add ((h.integrable_mul_exp hγ).const_mul _)
    refine (norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)).trans (le_of_eq ?_)
    rw [integral_add (h.integrable_abs.mul_const H) ((h.integrable_mul_exp hγ).const_mul _),
      integral_mul_const, integral_const_mul]
    rfl
  have hmain : |m₀| * ‖u s₀‖ ≤ C * A + q * H + M * A * qγ := by
    have h1 : ‖m₀ • u s₀‖ ≤ ‖m₀ • u s₀ + delayOp μ w τ u s₀‖ + ‖delayOp μ w τ u s₀‖ := by
      have := norm_sub_le (m₀ • u s₀ + delayOp μ w τ u s₀) (delayOp μ w τ u s₀)
      rwa [add_sub_cancel_right] at this
    rw [norm_smul, Real.norm_eq_abs] at h1
    linarith [hf s₀ hs₀]
  have hus : ‖u s₀‖ = M * A := by
    simp only [hM, hg, hA]
    rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      mul_one]
  rw [hus] at hmain
  have hqH : q * H ≤ q * H * A := le_mul_of_one_le_right (mul_nonneg hq0 hH0) hA1
  have h5 : (|m₀| * M) * A ≤ (C + q * H + M * qγ) * A := by nlinarith
  have h6 : |m₀| * M ≤ C + q * H + M * qγ := le_of_mul_le_mul_right h5 hApos
  have hden : 0 < |m₀| - qγ := by linarith
  have hMle : M ≤ (C + q * H) / (|m₀| - qγ) := by
    rw [le_div_iff₀ hden]
    linarith
  calc ‖u t‖ ≤ M * Real.exp (γ * t) := huM t ht
    _ ≤ (C + q * H) / (|m₀| - qγ) * Real.exp (γ * t) :=
        mul_le_mul_of_nonneg_right hMle (Real.exp_pos _).le

/-- **The estimate on a half-line** for a bounded function: if `q < |m₀|` and
`‖m₀ u(t) + (K u)(t)‖ ≤ C` for `t ≤ T`, then `‖u(t)‖ ≤ C/(|m₀| − q)` for `t ≤ T`. -/
theorem norm_le_of_delay_Iic (h : DelayData μ w τ D) {m₀ : ℝ}
    (hq : ∫ ω, |w ω| ∂μ < |m₀|) {u : ℝ → E} {T C B : ℝ} (hB : ∀ s ≤ T, ‖u s‖ ≤ B)
    (hf : ∀ t ≤ T, ‖m₀ • u t + delayOp μ w τ u t‖ ≤ C) :
    ∀ t ≤ T, ‖u t‖ ≤ C / (|m₀| - ∫ ω, |w ω| ∂μ) := by
  set q := ∫ ω, |w ω| ∂μ with hqdef
  have hq0 : 0 ≤ q := integral_nonneg fun _ => abs_nonneg _
  have : Nonempty (Iic T) := ⟨⟨T, le_rfl⟩⟩
  have hbdd : BddAbove (range fun s : Iic T => ‖u s‖) :=
    ⟨B, by rintro _ ⟨s, rfl⟩; exact hB s s.2⟩
  set M := ⨆ s : Iic T, ‖u s‖ with hM
  have huM : ∀ s ≤ T, ‖u s‖ ≤ M := fun s hs =>
    le_ciSup hbdd (⟨s, hs⟩ : Iic T)
  have hstep : ∀ t ≤ T, |m₀| * ‖u t‖ ≤ C + q * M := by
    intro t ht
    have hK : ‖delayOp μ w τ u t‖ ≤ q * M := by
      have hpt : ∀ ω, ‖w ω • u (t - τ ω)‖ ≤ |w ω| * M := fun ω => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (huM _ (by linarith [h.nonneg ω])) (abs_nonneg _)
      refine (norm_integral_le_of_norm_le (h.integrable_abs.mul_const M)
        (Eventually.of_forall hpt)).trans (le_of_eq ?_)
      rw [integral_mul_const]
    have h1 : ‖m₀ • u t‖ ≤ ‖m₀ • u t + delayOp μ w τ u t‖ + ‖delayOp μ w τ u t‖ := by
      have := norm_sub_le (m₀ • u t + delayOp μ w τ u t) (delayOp μ w τ u t)
      rwa [add_sub_cancel_right] at this
    rw [norm_smul, Real.norm_eq_abs] at h1
    linarith [hf t ht]
  have hm₀ : 0 < |m₀| := hq0.trans_lt hq
  have hMle : M ≤ (C + q * M) / |m₀| := by
    refine ciSup_le fun s => ?_
    rw [le_div_iff₀ hm₀, mul_comm]
    exact hstep s s.2
  have hden : 0 < |m₀| - q := by linarith
  intro t ht
  refine (huM t ht).trans ?_
  rw [le_div_iff₀ hden]
  rw [le_div_iff₀ hm₀] at hMle
  linarith

end Estimates

section Existence

variable {w τ : Ω → ℝ} {D : ℝ}

/-- The delay operator maps a bounded continuous function to a bounded continuous function, with
`‖K v‖ ≤ q ‖v‖`. -/
theorem DelayData.norm_delayOp_le (h : DelayData μ w τ D) (v : ℝ →ᵇ E) (t : ℝ) :
    ‖delayOp μ w τ v t‖ ≤ (∫ ω, |w ω| ∂μ) * ‖v‖ := by
  have hpt : ∀ ω, ‖w ω • v (t - τ ω)‖ ≤ |w ω| * ‖v‖ := fun ω => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (v.norm_coe_le_norm _) (abs_nonneg _)
  refine (norm_integral_le_of_norm_le (h.integrable_abs.mul_const _)
    (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_mul_const]

/-- **Existence for a small weight**: if `q = ∫ |w| < |m₀|`, then for every bounded continuous
forcing `f` there is a bounded continuous `u` with `m₀ u + K u = f`, the fixed point of the
contraction `v ↦ m₀⁻¹ (f − K v)` of the bounded continuous functions. -/
theorem exists_bounded_solution [CompleteSpace E] (h : DelayData μ w τ D) {m₀ : ℝ}
    (hq : ∫ ω, |w ω| ∂μ < |m₀|) (f : ℝ →ᵇ E) :
    ∃ u : ℝ →ᵇ E, ∀ t, m₀ • u t + delayOp μ w τ u t = f t := by
  set q := ∫ ω, |w ω| ∂μ with hqdef
  have hq0 : 0 ≤ q := integral_nonneg fun _ => abs_nonneg _
  have hm₀ : 0 < |m₀| := hq0.trans_lt hq
  have hm₀' : m₀ ≠ 0 := abs_pos.mp hm₀
  let K : (ℝ →ᵇ E) → (ℝ →ᵇ E) := fun v =>
    BoundedContinuousFunction.ofNormedAddCommGroup (delayOp μ w τ v)
      (h.continuous_delayOp v.continuous) (q * ‖v‖) (h.norm_delayOp_le v)
  have hKapp : ∀ v t, K v t = delayOp μ w τ v t := fun _ _ => rfl
  let Φ : (ℝ →ᵇ E) → (ℝ →ᵇ E) := fun v => m₀⁻¹ • (f - K v)
  have hlip : ∀ v₁ v₂, dist (Φ v₁) (Φ v₂) ≤ (|m₀|⁻¹ * q) * dist v₁ v₂ := by
    intro v₁ v₂
    have hd : Φ v₁ - Φ v₂ = m₀⁻¹ • (K v₂ - K v₁) := by
      simp only [Φ, ← smul_sub]
      congr 1
      abel
    have hK : ‖K v₂ - K v₁‖ ≤ q * ‖v₂ - v₁‖ := by
      refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun t => ?_
      rw [BoundedContinuousFunction.sub_apply, hKapp, hKapp,
        ← h.delayOp_sub v₂.continuous v₁.continuous]
      exact h.norm_delayOp_le (v₂ - v₁) t
    rw [dist_eq_norm, dist_eq_norm, hd, norm_smul, norm_inv, Real.norm_eq_abs, norm_sub_rev v₁]
    calc |m₀|⁻¹ * ‖K v₂ - K v₁‖ ≤ |m₀|⁻¹ * (q * ‖v₂ - v₁‖) :=
          mul_le_mul_of_nonneg_left hK (by positivity)
      _ = |m₀|⁻¹ * q * ‖v₂ - v₁‖ := by ring
  have hc0 : 0 ≤ |m₀|⁻¹ * q := by positivity
  have hc1 : |m₀|⁻¹ * q < 1 := by
    rw [inv_mul_lt_iff₀ hm₀, mul_one]
    exact hq
  have hΦ : ContractingWith (Real.toNNReal (|m₀|⁻¹ * q)) Φ := by
    refine ⟨Real.toNNReal_lt_one.mpr hc1, LipschitzWith.of_dist_le_mul fun v₁ v₂ => ?_⟩
    rw [Real.coe_toNNReal _ hc0]
    exact hlip v₁ v₂
  refine ⟨ContractingWith.fixedPoint Φ hΦ, fun t => ?_⟩
  have hfix : Φ (ContractingWith.fixedPoint Φ hΦ) = ContractingWith.fixedPoint Φ hΦ :=
    ContractingWith.fixedPoint_isFixedPt (f := Φ) hΦ
  set u := ContractingWith.fixedPoint Φ hΦ
  have ht := congrArg (fun v : ℝ →ᵇ E => v t) hfix
  simp only [Φ, BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_sub,
    Pi.sub_apply, hKapp] at ht
  rw [← ht, smul_smul, mul_inv_cancel₀ hm₀', one_smul, sub_add_cancel]

/-- The weight `w e^{−γτ}` of the substitution `u = e^{γt} v`. -/
theorem DelayData.weighted (h : DelayData μ w τ D) {γ : ℝ} (hγ : 0 ≤ γ) :
    DelayData μ (fun ω => w ω * Real.exp (-(γ * τ ω))) τ D where
  integrable := by
    refine h.integrable_abs.mono' ?_ (Eventually.of_forall fun ω => ?_)
    · exact h.integrable.aestronglyMeasurable.mul
        (Real.continuous_exp.comp_aestronglyMeasurable
          ((h.measurable.const_mul γ).neg.aestronglyMeasurable))
    · have he : Real.exp (-(γ * τ ω)) ≤ 1 := Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (mul_nonneg hγ (h.nonneg ω)))
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _) he
  measurable := h.measurable
  nonneg := h.nonneg
  bound_nonneg := h.bound_nonneg
  le ω hw := h.le ω fun h0 => hw (by simp [h0])

theorem integral_abs_weighted (w τ : Ω → ℝ) (γ : ℝ) :
    ∫ ω, |w ω * Real.exp (-(γ * τ ω))| ∂μ = weightNorm μ w τ γ := by
  simp only [weightNorm, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- The operator of `w` on `e^{γt} v` is `e^{γt}` times the operator of `w e^{−γτ}` on `v`. -/
theorem delayOp_exp_smul (γ : ℝ) (v : ℝ → E) (t : ℝ) :
    delayOp μ w τ (fun s => Real.exp (γ * s) • v s) t =
      Real.exp (γ * t) • delayOp μ (fun ω => w ω * Real.exp (-(γ * τ ω))) τ v t := by
  simp only [delayOp, ← integral_smul]
  congr 1
  funext ω
  rw [smul_smul, smul_smul]
  congr 1
  rw [mul_comm (Real.exp (γ * t)), mul_assoc, ← Real.exp_add]
  ring_nf

/-- **Existence and the growth bound**: if `q_γ < |m₀|`, a continuous forcing `f` that vanishes
for `t ≤ 0` and grows at most like `C e^{γt}` has a continuous solution `u` of
`m₀ u + K u = f` that vanishes for `t ≤ 0`, with `‖u(t)‖ ≤ C e^{γt}/(|m₀| − q_γ)`. -/
theorem exists_solution [CompleteSpace E] (h : DelayData μ w τ D) {γ : ℝ} (hγ : 0 ≤ γ)
    {m₀ : ℝ} (hq : weightNorm μ w τ γ < |m₀|) {f : ℝ → E} (hf : Continuous f)
    (hf0 : ∀ t ≤ 0, f t = 0) {C : ℝ} (hC : ∀ t, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (γ * t)) :
    ∃ u : ℝ → E, Continuous u ∧ (∀ t ≤ 0, u t = 0) ∧
      (∀ t, m₀ • u t + delayOp μ w τ u t = f t) ∧
      ∀ t, ‖u t‖ ≤ C / (|m₀| - weightNorm μ w τ γ) * Real.exp (γ * t) := by
  have hγd := h.weighted hγ
  have hq' : ∫ ω, |w ω * Real.exp (-(γ * τ ω))| ∂μ < |m₀| := by
    rwa [integral_abs_weighted]
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0 le_rfl)
    simpa using this
  set g : ℝ → E := fun t => Real.exp (-(γ * t)) • f t with hg
  have hgc : Continuous g :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).smul hf
  have hgb : ∀ t, ‖g t‖ ≤ C := by
    intro t
    rcases le_or_gt t 0 with ht | ht
    · simp [hg, hf0 t ht, hC0]
    · rw [hg, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(γ * t)) * ‖f t‖ ≤ Real.exp (-(γ * t)) * (C * Real.exp (γ * t)) :=
            mul_le_mul_of_nonneg_left (hC t ht.le) (Real.exp_pos _).le
        _ = C := by
            rw [mul_comm C, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
              one_mul]
  obtain ⟨v, hv⟩ := exists_bounded_solution hγd hq'
    (BoundedContinuousFunction.ofNormedAddCommGroup g hgc C hgb)
  have hv' : ∀ t, m₀ • v t + delayOp μ (fun ω => w ω * Real.exp (-(γ * τ ω))) τ v t = g t :=
    hv
  have hden : 0 < |m₀| - weightNorm μ w τ γ := by linarith
  have hvb : ∀ t, ‖v t‖ ≤ C / (|m₀| - weightNorm μ w τ γ) := by
    intro t
    have := norm_le_of_delay_Iic hγd hq' (fun s _ => v.norm_coe_le_norm s)
      (fun s _ => (hv' s).symm ▸ hgb s) t le_rfl
    rwa [integral_abs_weighted] at this
  have hv0 : ∀ t ≤ 0, v t = 0 := by
    intro t ht
    have := norm_le_of_delay_Iic hγd hq' (T := 0) (C := 0) (fun s _ => v.norm_coe_le_norm s)
      (fun s hs => by rw [hv' s]; simp [hg, hf0 s hs]) t ht
    rw [zero_div] at this
    exact norm_le_zero_iff.mp this
  refine ⟨fun t => Real.exp (γ * t) • v t,
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul v.continuous,
    fun t ht => by simp [hv0 t ht], fun t => ?_, fun t => ?_⟩
  · rw [delayOp_exp_smul, smul_comm m₀, ← smul_add, hv' t, hg]
    simp only [smul_smul]
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hvb t) (Real.exp_pos _).le

/-- **Uniqueness**: if `q_γ < |m₀|`, two continuous functions that agree on `[−D, 0]` and have the
same value of `m₀ u + K u` for `t ≥ 0` agree for `t ≥ 0`. -/
theorem eq_of_delay (h : DelayData μ w τ D) {γ : ℝ} (hγ : 0 ≤ γ) {m₀ : ℝ}
    (hq : weightNorm μ w τ γ < |m₀|) {u v : ℝ → E} (hu : Continuous u) (hv : Continuous v)
    (h0 : ∀ s ∈ Icc (-D) 0, u s = v s)
    (heq : ∀ t, 0 ≤ t → m₀ • u t + delayOp μ w τ u t = m₀ • v t + delayOp μ w τ v t) :
    ∀ t, 0 ≤ t → u t = v t := by
  intro t ht
  have hd := norm_le_of_delay h hγ hq (u := fun s => u s - v s) (hu.sub hv) (T := t) (C := 0)
    (H := 0) (fun s hs => by simp [h0 s hs]) (fun s hs => by
      rw [h.delayOp_sub hu hv, smul_sub]
      have := heq s hs.1
      rw [show m₀ • u s - m₀ • v s + (delayOp μ w τ u s - delayOp μ w τ v s) =
        (m₀ • u s + delayOp μ w τ u s) - (m₀ • v s + delayOp μ w τ v s) by abel, this,
        sub_self, norm_zero, zero_mul]) t ⟨ht, le_rfl⟩
  simp only [zero_add, mul_zero, zero_div, zero_mul] at hd
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hd)

/-- **A rate for every bare coefficient**: if the delay is positive almost everywhere, the weighted
norm `q_γ` tends to `0` as `γ → ∞`, so for every `m₀ ≠ 0` there are arbitrarily large rates with
`q_γ < |m₀|`. -/
theorem DelayData.exists_weightNorm_lt (h : DelayData μ w τ D) (hpos : ∀ᵐ ω ∂μ, 0 < τ ω) {m₀ : ℝ}
    (hm₀ : m₀ ≠ 0) (γ₀ : ℝ) : ∃ γ, γ₀ ≤ γ ∧ 0 ≤ γ ∧ weightNorm μ w τ γ < |m₀| := by
  have hlim : Tendsto (weightNorm μ w τ) atTop (𝓝 0) := by
    change Tendsto (fun γ => ∫ ω, |w ω| * Real.exp (-(γ * τ ω)) ∂μ) atTop (𝓝 0)
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
      (F := fun γ ω => |w ω| * Real.exp (-(γ * τ ω))) (f := fun _ => (0 : ℝ))
      (fun ω => |w ω|)
      (Eventually.of_forall fun γ => h.integrable_abs.aestronglyMeasurable.mul
        (Real.continuous_exp.comp_aestronglyMeasurable
          ((h.measurable.const_mul γ).neg.aestronglyMeasurable)))
      ((eventually_ge_atTop 0).mono fun γ hγ => Eventually.of_forall fun ω => by
        have he : Real.exp (-(γ * τ ω)) ≤ 1 := Real.exp_le_one_iff.mpr
          (neg_nonpos.mpr (mul_nonneg hγ (h.nonneg ω)))
        rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_right (abs_nonneg _) he)
      h.integrable_abs
      (hpos.mono fun ω hω => by
        have h1 : Tendsto (fun γ : ℝ => γ * τ ω) atTop atTop :=
          tendsto_id.atTop_mul_const hω
        have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul |w ω|
        simpa [Function.comp_def] using h2)
    simpa using this
  obtain ⟨γ, hγ1, hγ2⟩ := ((hlim.eventually (gt_mem_nhds (abs_pos.mpr hm₀))).and
    (eventually_ge_atTop (max γ₀ 0))).exists
  exact ⟨γ, (le_max_left _ _).trans hγ2, (le_max_right _ _).trans hγ2, hγ1⟩

/-- **Runaway solutions**: for a nonnegative weight with a positive delay almost everywhere and
`−∫ w < m₀ < 0`, the characteristic function `m₀ + ∫ w e^{−γτ}` has a root `γ > 0`, so
`u(t) = e^{γt} c` solves the free equation `m₀ u + K u = 0` and grows exponentially. -/
theorem exists_runaway [CompleteSpace E] (h : DelayData μ w τ D) (hpos : ∀ᵐ ω ∂μ, 0 < τ ω)
    (hw : ∀ ω, 0 ≤ w ω) {m₀ : ℝ} (hm₀ : m₀ < 0) (hm : 0 < m₀ + ∫ ω, w ω ∂μ) :
    ∃ γ, 0 < γ ∧ ∀ (c : E) (t : ℝ),
      m₀ • (Real.exp (γ * t) • c) + delayOp μ w τ (fun s => Real.exp (γ * s) • c) t = 0 := by
  have hwn : ∀ γ, weightNorm μ w τ γ = ∫ ω, w ω * Real.exp (-(γ * τ ω)) ∂μ := fun γ => by
    simp only [weightNorm, abs_of_nonneg (hw _)]
  set χ : ℝ → ℝ := fun γ => m₀ + weightNorm μ w τ γ with hχ
  obtain ⟨Γ, -, hΓ0, hΓ⟩ := h.exists_weightNorm_lt hpos hm₀.ne 0
  have hχΓ : χ Γ < 0 := by
    simp only [hχ]
    rw [abs_of_neg hm₀] at hΓ
    linarith
  have hχ0 : 0 < χ 0 := by
    simp only [hχ, DelayData.weightNorm_zero]
    simpa only [abs_of_nonneg (hw _)] using hm
  have hcont : ContinuousOn χ (Icc 0 Γ) := by
    refine continuousOn_const.add ?_
    refine continuousOn_of_dominated (bound := fun ω => |w ω|)
      (fun γ _ => h.integrable_abs.aestronglyMeasurable.mul
        (Real.continuous_exp.comp_aestronglyMeasurable
          ((h.measurable.const_mul γ).neg.aestronglyMeasurable)))
      (fun γ hγ => Eventually.of_forall fun ω => ?_) h.integrable_abs
      (Eventually.of_forall fun ω => ?_)
    · have he : Real.exp (-(γ * τ ω)) ≤ 1 := Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (mul_nonneg hγ.1 (h.nonneg ω)))
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _) he
    · exact (continuous_const.mul (Real.continuous_exp.comp
        (continuous_id.mul continuous_const).neg)).continuousOn
  obtain ⟨γ, hγ, hγ0⟩ := intermediate_value_Icc' hΓ0 hcont ⟨hχΓ.le, hχ0.le⟩
  have hγpos : 0 < γ := by
    rcases hγ.1.lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq] at hγ0
      linarith
  refine ⟨γ, hγpos, fun c t => ?_⟩
  have hK : delayOp μ w τ (fun s => Real.exp (γ * s) • c) t =
      (weightNorm μ w τ γ) • (Real.exp (γ * t) • c) := by
    rw [delayOp_exp_smul, hwn]
    simp only [delayOp, integral_smul_const]
    rw [smul_comm]
  rw [hK, ← add_smul]
  have : m₀ + weightNorm μ w τ γ = 0 := hγ0
  rw [this, zero_smul]

end Existence

section Reduction

variable {w τ : Ω → ℝ} {D : ℝ}

omit [NormedSpace ℝ E] in
/-- A continuous function that vanishes on `(−∞, 0)` vanishes on `(−∞, 0]`. -/
theorem eq_zero_of_lt_zero {g : ℝ → E} (hg : Continuous g) (h0 : ∀ t < 0, g t = 0) :
    ∀ t ≤ 0, g t = 0 := by
  intro t ht
  have hcl : IsClosed {s : ℝ | g s = 0} := isClosed_eq hg continuous_const
  have hsub : Iio (0 : ℝ) ⊆ {s : ℝ | g s = 0} := fun s hs => h0 s hs
  have := hcl.closure_subset_iff.mpr hsub
  rw [closure_Iio] at this
  exact this ht

/-- The derivative of a function that vanishes on `(−∞, 0]` vanishes on `(−∞, 0)`. -/
theorem deriv_eq_zero_of_lt_zero {F : ℝ → E} (hF0 : ∀ t ≤ 0, F t = 0) {t : ℝ} (ht : t < 0) :
    deriv F t = 0 := by
  have h : F =ᶠ[𝓝 t] fun _ => 0 :=
    Filter.eventually_of_mem (Iio_mem_nhds ht) fun s hs => hF0 s (le_of_lt hs)
  rw [h.deriv_eq, deriv_const]

/-- **The second-order Taylor bound**: `‖a(t − σ) − a(t) + σ a'(t)‖ ≤ B σ²/2` for `σ ≥ 0` when
`‖a''‖ ≤ B`. -/
theorem norm_taylor_two_le {a a' a'' : ℝ → E} (ha : ∀ s, HasDerivAt a (a' s) s)
    (ha' : ∀ s, HasDerivAt a' (a'' s) s) {B : ℝ} (hB : ∀ s, ‖a'' s‖ ≤ B) (t : ℝ) {σ : ℝ}
    (hσ : 0 ≤ σ) : ‖a (t - σ) - a t + σ • a' t‖ ≤ B * σ ^ 2 / 2 := by
  set g : ℝ → E := fun r => a (t - r) - a t + r • a' t with hg
  have hg' : ∀ r, HasDerivAt g (a' t - a' (t - r)) r := by
    intro r
    have h1 : HasDerivAt (fun r => a (t - r)) (-a' (t - r)) r := by
      have := (ha (t - r)).scomp r ((hasDerivAt_const r t).sub (hasDerivAt_id r))
      rw [zero_sub, neg_one_smul] at this
      exact this
    have h2 := ((h1.sub_const (a t)).add ((hasDerivAt_id r).smul_const (a' t)))
    have he : a' t - a' (t - r) = -a' (t - r) + (1 : ℝ) • a' t := by
      rw [one_smul]
      abel
    rw [he]
    exact h2
  have hmv : ∀ r, 0 ≤ r → ‖a' t - a' (t - r)‖ ≤ B * r := by
    intro r hr
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ) (f := a')
      (fun x _ => (ha' x).hasDerivWithinAt) (fun x _ => hB x) convex_univ (mem_univ (t - r))
      (mem_univ t)
    rwa [sub_sub_cancel, Real.norm_of_nonneg hr] at this
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := σ)
    (f := g) (f' := fun r => a' t - a' (t - r)) (B := fun r => B * r ^ 2 / 2)
    (B' := fun r => B * r)
    (fun r _ => (hg' r).continuousAt.continuousWithinAt)
    (fun r _ => (hg' r).hasDerivWithinAt) (by simp [hg])
    (fun r => by
      have := ((hasDerivAt_pow 2 r).const_mul B).div_const 2
      convert this using 1
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring)
    (fun r hr => hmv r hr.1) ⟨hσ, le_rfl⟩
  simpa [hg] using hfence

/-- The weight times the delay is integrable. -/
theorem DelayData.integrable_mul_delay (h : DelayData μ w τ D) :
    Integrable (fun ω => w ω * τ ω) μ := by
  refine (h.integrable_abs.mul_const D).mono'
    (h.integrable.aestronglyMeasurable.mul h.measurable.aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  by_cases hw : w ω = 0
  · simp [hw]
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.nonneg ω)]
    exact mul_le_mul_of_nonneg_left (h.le ω hw) (abs_nonneg _)

/-- The weight times the square of the delay is integrable. -/
theorem DelayData.integrable_mul_delay_sq (h : DelayData μ w τ D) :
    Integrable (fun ω => |w ω| * τ ω ^ 2) μ := by
  refine (h.integrable_abs.mul_const (D ^ 2)).mono'
    (h.integrable_abs.aestronglyMeasurable.mul (h.measurable.pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  by_cases hw : w ω = 0
  · simp [hw]
  · rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (sq_nonneg (τ ω))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h.nonneg ω) (h.le ω hw) 2)
      (abs_nonneg _)

/-- **Comparison with the reduced equation**: if `q = ∫ |w| < |m₀|`, `m = m₀ + ∫ w ≠ 0`, and the
forcing `F` is `C³`, vanishes for `t ≤ 0` and has `‖F''‖ ≤ B₂`, `‖F'''‖ ≤ B₃`, then the solution
`u` of `m₀ u + K u = F` that vanishes in the past stays within
`((M₁/m)² B₂ + (Q₂/2)(B₂/|m| + |M₁| B₃/m²))/(|m₀| − q)` of `F/m + (M₁/m²) F'` at all times, with
the moments `M₁ = ∫ w τ` and `Q₂ = ∫ |w| τ²`. The function `F/m + (M₁/m²) F'` is the
acceleration of the reduced equation `m a = F + (M₁/m) F'`; the residual of the delay equation
along it is `−(M₁/m)² F''` plus the Taylor remainder of order `τ²`. -/
theorem norm_sub_reduced_le [CompleteSpace E] (h : DelayData μ w τ D) {m₀ : ℝ}
    (hq : ∫ ω, |w ω| ∂μ < |m₀|) {m M₁ Q₂ : ℝ} (hm : m = m₀ + ∫ ω, w ω ∂μ) (hm0 : m ≠ 0)
    (hM₁ : M₁ = ∫ ω, w ω * τ ω ∂μ) (hQ₂ : Q₂ = ∫ ω, |w ω| * τ ω ^ 2 ∂μ) {F : ℝ → E}
    (hF : ContDiff ℝ 3 F) (hF0 : ∀ t ≤ 0, F t = 0) {B₂ B₃ : ℝ}
    (hB₂ : ∀ t, ‖deriv (deriv F) t‖ ≤ B₂) (hB₃ : ∀ t, ‖deriv (deriv (deriv F)) t‖ ≤ B₃)
    {u : ℝ → E} (hu : Continuous u) (hu0 : ∀ t ≤ 0, u t = 0)
    (hsol : ∀ t, 0 ≤ t → m₀ • u t + delayOp μ w τ u t = F t) (t : ℝ) :
    ‖u t - (m⁻¹ • F t + (M₁ / m ^ 2) • deriv F t)‖ ≤
      ((M₁ / m) ^ 2 * B₂ + Q₂ / 2 * (B₂ / |m| + |M₁| * B₃ / m ^ 2)) /
        (|m₀| - ∫ ω, |w ω| ∂μ) := by
  set q := ∫ ω, |w ω| ∂μ with hqdef
  have hq0 : 0 ≤ q := integral_nonneg fun _ => abs_nonneg _
  have hden : 0 < |m₀| - q := by linarith
  -- the derivatives of the forcing
  have hF1 : ContDiff ℝ 2 (deriv F) := ((contDiff_succ_iff_deriv (n := 2)).mp hF).2.2
  have hF2 : ContDiff ℝ 1 (deriv (deriv F)) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hF1).2.2
  have dF : ∀ s, HasDerivAt F (deriv F s) s := fun s =>
    ((hF.differentiable (by norm_num)) s).hasDerivAt
  have dF1 : ∀ s, HasDerivAt (deriv F) (deriv (deriv F) s) s := fun s =>
    ((hF1.differentiable (by norm_num)) s).hasDerivAt
  have dF2 : ∀ s, HasDerivAt (deriv (deriv F)) (deriv (deriv (deriv F)) s) s := fun s =>
    ((hF2.differentiable (by norm_num)) s).hasDerivAt
  set c₁ := m⁻¹ with hc₁
  set c₂ := M₁ / m ^ 2 with hc₂
  set a : ℝ → E := fun s => c₁ • F s + c₂ • deriv F s with ha
  set a' : ℝ → E := fun s => c₁ • deriv F s + c₂ • deriv (deriv F) s with ha'
  set a'' : ℝ → E := fun s => c₁ • deriv (deriv F) s + c₂ • deriv (deriv (deriv F)) s
    with ha''
  have da : ∀ s, HasDerivAt a (a' s) s := fun s =>
    ((dF s).const_smul c₁).add ((dF1 s).const_smul c₂)
  have da' : ∀ s, HasDerivAt a' (a'' s) s := fun s =>
    ((dF1 s).const_smul c₁).add ((dF2 s).const_smul c₂)
  have hac : Continuous a := continuous_iff_continuousAt.mpr fun s => (da s).continuousAt
  set Ba := B₂ / |m| + |M₁| * B₃ / m ^ 2 with hBadef
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ 0)
  have hB₃0 : 0 ≤ B₃ := (norm_nonneg _).trans (hB₃ 0)
  have hBa : ∀ s, ‖a'' s‖ ≤ Ba := by
    intro s
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hc₁, hc₂, abs_inv, abs_div,
      abs_of_nonneg (sq_nonneg m)]
    have h1 : |m|⁻¹ * ‖deriv (deriv F) s‖ ≤ B₂ / |m| := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (hB₂ s) (by positivity)
    have h2 : |M₁| / m ^ 2 * ‖deriv (deriv (deriv F)) s‖ ≤ |M₁| * B₃ / m ^ 2 := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left (hB₃ s) (by positivity)
    linarith
  -- the reduced acceleration vanishes in the past
  have hF'0 : ∀ s ≤ 0, deriv F s = 0 :=
    eq_zero_of_lt_zero hF1.continuous fun s hs => deriv_eq_zero_of_lt_zero hF0 hs
  have ha0 : ∀ s ≤ 0, a s = 0 := fun s hs => by simp [ha, hF0 s hs, hF'0 s hs]
  -- the residual of the delay equation along the reduced acceleration
  have hres : ∀ s, ‖m₀ • a s + delayOp μ w τ a s - F s‖ ≤ (M₁ / m) ^ 2 * B₂ + Q₂ / 2 * Ba := by
    intro s
    set ρ : Ω → E := fun ω => a (s - τ ω) - a s + τ ω • a' s with hρ
    have i1 : Integrable (fun ω => w ω • a (s - τ ω)) μ := h.integrable_smul hac s
    have i2 : Integrable (fun ω => w ω • a s) μ := h.integrable.smul_const _
    have i3 : Integrable (fun ω => (w ω * τ ω) • a' s) μ := h.integrable_mul_delay.smul_const _
    have hsplit : ∫ ω, w ω • ρ ω ∂μ =
        delayOp μ w τ a s - (∫ ω, w ω ∂μ) • a s + M₁ • a' s := by
      have he : (fun ω => w ω • ρ ω) =
          fun ω => w ω • a (s - τ ω) - w ω • a s + (w ω * τ ω) • a' s := by
        funext ω
        simp only [hρ, smul_add, smul_sub, smul_smul]
      have hadd := integral_add (μ := μ) (f := fun ω => w ω • a (s - τ ω) - w ω • a s)
        (g := fun ω => (w ω * τ ω) • a' s) (i1.sub i2) i3
      rw [he, hadd, integral_sub i1 i2, integral_smul_const,
        integral_smul_const, hM₁]
      rfl
    have hρb : ‖∫ ω, w ω • ρ ω ∂μ‖ ≤ Q₂ / 2 * Ba := by
      have hpt : ∀ ω, ‖w ω • ρ ω‖ ≤ Ba / 2 * (|w ω| * τ ω ^ 2) := fun ω => by
        rw [norm_smul, Real.norm_eq_abs]
        have := norm_taylor_two_le da da' hBa s (h.nonneg ω)
        calc |w ω| * ‖ρ ω‖ ≤ |w ω| * (Ba * τ ω ^ 2 / 2) :=
              mul_le_mul_of_nonneg_left this (abs_nonneg _)
          _ = Ba / 2 * (|w ω| * τ ω ^ 2) := by ring
      refine (norm_integral_le_of_norm_le (h.integrable_mul_delay_sq.const_mul _)
        (Eventually.of_forall hpt)).trans (le_of_eq ?_)
      rw [integral_const_mul, ← hQ₂]
      ring
    have halg : m₀ • a s + delayOp μ w τ a s - F s =
        -((M₁ / m) ^ 2) • deriv (deriv F) s + ∫ ω, w ω • ρ ω ∂μ := by
      rw [hsplit]
      have e1 : m * c₁ = 1 := by rw [hc₁, mul_inv_cancel₀ hm0]
      have e2 : m * c₂ - M₁ * c₁ = 0 := by
        rw [hc₁, hc₂]
        field_simp
        ring
      have e3 : M₁ * c₂ = (M₁ / m) ^ 2 := by
        rw [hc₂]
        field_simp
      have key : m₀ • a s + (∫ ω, w ω ∂μ) • a s - M₁ • a' s - F s =
          (m * c₁ - 1) • F s + (m * c₂ - M₁ * c₁) • deriv F s -
            (M₁ * c₂) • deriv (deriv F) s := by
        rw [← add_smul, ← hm]
        simp only [ha, ha']
        module
      rw [e1, e2, e3, sub_self, zero_smul, zero_smul, zero_add, zero_sub] at key
      rw [neg_smul, ← key]
      abel
    rw [halg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg _)]
    have := mul_le_mul_of_nonneg_left (hB₂ s) (sq_nonneg (M₁ / m))
    linarith
  -- the error
  set e : ℝ → E := fun s => u s - a s with he
  have hec : Continuous e := hu.sub hac
  have he0 : ∀ s ≤ 0, e s = 0 := fun s hs => by simp [he, hu0 s hs, ha0 s hs]
  have hQ₂0 : 0 ≤ Q₂ := by
    rw [hQ₂]
    exact integral_nonneg fun ω => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hR0 : 0 ≤ (M₁ / m) ^ 2 * B₂ + Q₂ / 2 * Ba := by positivity
  rcases lt_or_ge t 0 with ht | ht
  · rw [show u t - (m⁻¹ • F t + (M₁ / m ^ 2) • deriv F t) = e t from rfl, he0 t ht.le,
      norm_zero]
    positivity
  have hq' : weightNorm μ w τ 0 < |m₀| := by rwa [DelayData.weightNorm_zero]
  have hbound := norm_le_of_delay h le_rfl hq' hec (T := t)
    (C := (M₁ / m) ^ 2 * B₂ + Q₂ / 2 * Ba) (H := 0)
    (fun s hs => by simp [he0 s hs.2]) (fun s hs => by
      rw [h.delayOp_sub hu hac, zero_mul, Real.exp_zero, mul_one]
      have hsol' := hsol s hs.1
      have : m₀ • e s + (delayOp μ w τ u s - delayOp μ w τ a s) =
          -(m₀ • a s + delayOp μ w τ a s - F s) := by
        rw [he]
        simp only [smul_sub]
        rw [← hsol']
        abel
      rw [this, norm_neg]
      exact hres s) t ⟨ht, le_rfl⟩
  rw [DelayData.weightNorm_zero, zero_mul, Real.exp_zero, mul_one, mul_zero, add_zero] at hbound
  exact hbound

/-! ### Accelerations and paths -/

/-- The double primitive `t ↦ ∫₀ᵗ ∫₀ˢ u(r) dr ds`, the path with acceleration `u` that starts
at rest at the origin. -/
def doublePrimitive (u : ℝ → E) (t : ℝ) : E := ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, u r

variable [CompleteSpace E]

theorem continuous_primitive_zero {u : ℝ → E} (hu : Continuous u) :
    Continuous fun s => ∫ r in (0 : ℝ)..s, u r :=
  continuous_iff_continuousAt.mpr fun s =>
    (hu.integral_hasStrictDerivAt 0 s).hasDerivAt.continuousAt

theorem hasDerivAt_doublePrimitive {u : ℝ → E} (hu : Continuous u) (t : ℝ) :
    HasDerivAt (doublePrimitive u) (∫ r in (0 : ℝ)..t, u r) t :=
  ((continuous_primitive_zero hu).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem deriv_doublePrimitive {u : ℝ → E} (hu : Continuous u) :
    deriv (doublePrimitive u) = fun t => ∫ r in (0 : ℝ)..t, u r :=
  funext fun t => (hasDerivAt_doublePrimitive hu t).deriv

/-- The double primitive has the acceleration `u`. -/
theorem deriv_deriv_doublePrimitive {u : ℝ → E} (hu : Continuous u) (t : ℝ) :
    deriv (deriv (doublePrimitive u)) t = u t := by
  rw [deriv_doublePrimitive hu]
  exact hu.deriv_integral u 0 t

/-- The double primitive of a continuous function is `C²`. -/
theorem contDiff_doublePrimitive {u : ℝ → E} (hu : Continuous u) :
    ContDiff ℝ 2 (doublePrimitive u) := by
  refine (contDiff_succ_iff_deriv (n := 1)).mpr
    ⟨fun t => (hasDerivAt_doublePrimitive hu t).differentiableAt, by simp, ?_⟩
  rw [deriv_doublePrimitive hu]
  refine (contDiff_succ_iff_deriv (n := 0)).mpr
    ⟨fun t => (hu.integral_hasStrictDerivAt 0 t).hasDerivAt.differentiableAt, by simp, ?_⟩
  have : deriv (fun t => ∫ r in (0 : ℝ)..t, u r) = u := funext fun t => hu.deriv_integral u 0 t
  rw [this]
  exact contDiff_zero.mpr hu

omit [CompleteSpace E] in
/-- The primitive of a function that vanishes on `(−∞, 0]` vanishes there. -/
theorem integral_eq_zero_of_le {u : ℝ → E} (hu0 : ∀ t ≤ 0, u t = 0) {s : ℝ} (hs : s ≤ 0) :
    ∫ r in (0 : ℝ)..s, u r = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : E)) fun r hr => ?_]
  · simp
  · rw [uIcc_of_ge hs] at hr
    exact hu0 r hr.2

omit [CompleteSpace E] in
/-- The double primitive of a function that vanishes on `(−∞, 0]` vanishes there. -/
theorem doublePrimitive_eq_zero_of_le {u : ℝ → E} (hu0 : ∀ t ≤ 0, u t = 0) {t : ℝ}
    (ht : t ≤ 0) : doublePrimitive u t = 0 :=
  integral_eq_zero_of_le (fun _ hs => integral_eq_zero_of_le hu0 hs) ht

end Reduction

section Paths

/-- A bound of the operator for a bounded function: `‖(K u)(t)‖ ≤ q B` when `‖u‖ ≤ B`. -/
theorem DelayData.norm_delayOp_le_of_bound {w τ : Ω → ℝ} {D : ℝ} (h : DelayData μ w τ D)
    {u : ℝ → E} {B : ℝ} (hu : ∀ s, ‖u s‖ ≤ B) (t : ℝ) :
    ‖delayOp μ w τ u t‖ ≤ (∫ ω, |w ω| ∂μ) * B := by
  have hpt : ∀ ω, ‖w ω • u (t - τ ω)‖ ≤ |w ω| * B := fun ω => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hu _) (abs_nonneg _)
  refine (norm_integral_le_of_norm_le (h.integrable_abs.mul_const _)
    (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_mul_const]

/-- The second derivative of a sum of `C²` functions. -/
theorem deriv_deriv_add {f g : ℝ → E} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (t : ℝ) :
    deriv (deriv fun s => f s + g s) t = deriv (deriv f) t + deriv (deriv g) t := by
  have hf1 : ContDiff ℝ 1 (deriv f) := ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2
  have hg1 : ContDiff ℝ 1 (deriv g) := ((contDiff_succ_iff_deriv (n := 1)).mp hg).2.2
  have h1 : deriv (fun s => f s + g s) = fun s => deriv f s + deriv g s := funext fun s =>
    deriv_add ((hf.differentiable (by norm_num)) s) ((hg.differentiable (by norm_num)) s)
  rw [h1]
  exact deriv_add ((hf1.differentiable one_ne_zero) t) ((hg1.differentiable one_ne_zero) t)

/-- A `C²` function with vanishing second derivative that vanishes on `(−∞, 0]` vanishes. -/
theorem eq_zero_of_deriv_deriv_eq_zero {g : ℝ → E} (hg : ContDiff ℝ 2 g)
    (hdd : ∀ t, deriv (deriv g) t = 0) (h0 : ∀ t ≤ 0, g t = 0) (t : ℝ) : g t = 0 := by
  have hg1 : ContDiff ℝ 1 (deriv g) := ((contDiff_succ_iff_deriv (n := 1)).mp hg).2.2
  have hconst := is_const_of_deriv_eq_zero (hg1.differentiable one_ne_zero) hdd
  have hd0 : deriv g (-1) = 0 := deriv_eq_zero_of_lt_zero h0 (by norm_num)
  have hd : ∀ s, deriv g s = 0 := fun s => (hconst s (-1)).trans hd0
  have hgc := is_const_of_deriv_eq_zero (hg.differentiable (by norm_num)) hd
  exact (hgc t (-1)).trans (h0 (-1) (by norm_num))

/-- Two `C²` functions that agree on `(−∞, 0]` have the same acceleration there. -/
theorem deriv_deriv_eq_of_eq_on_Iic {f g : ℝ → E} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfg : ∀ t ≤ 0, f t = g t) : ∀ t ≤ 0, deriv (deriv f) t = deriv (deriv g) t := by
  have hf2 : Continuous (deriv (deriv f)) :=
    ((contDiff_succ_iff_deriv (n := 0)).mp
      ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2).2.2.continuous
  have hg2 : Continuous (deriv (deriv g)) :=
    ((contDiff_succ_iff_deriv (n := 0)).mp
      ((contDiff_succ_iff_deriv (n := 1)).mp hg).2.2).2.2.continuous
  have h := eq_zero_of_lt_zero (hf2.sub hg2) fun t ht => by
    have hev : f =ᶠ[𝓝 t] g :=
      Filter.eventually_of_mem (Iio_mem_nhds ht) fun s hs => hfg s (le_of_lt hs)
    have hev' : deriv f =ᶠ[𝓝 t] deriv g := hev.deriv
    simp [hev'.deriv_eq]
  exact fun t ht => sub_eq_zero.mp (h t ht)

end Paths

section Bounds

/-- The second moment is at most `D` times the first: `∫ |w| τ² ≤ D ∫ |w| τ`. -/
theorem DelayData.integral_abs_mul_sq_le {w τ : Ω → ℝ} {D : ℝ} (h : DelayData μ w τ D) :
    ∫ ω, |w ω| * τ ω ^ 2 ∂μ ≤ D * ∫ ω, |w ω| * τ ω ∂μ := by
  have hi : Integrable (fun ω => |w ω| * τ ω) μ := by
    refine h.integrable_mul_delay.abs.congr (Eventually.of_forall fun ω => ?_)
    simp only [abs_mul, abs_of_nonneg (h.nonneg ω)]
  rw [← integral_const_mul]
  refine integral_mono h.integrable_mul_delay_sq (hi.const_mul D) fun ω => ?_
  by_cases hw : w ω = 0
  · simp [hw]
  · have h1 := h.le ω hw
    have h2 := h.nonneg ω
    have : |w ω| * τ ω ^ 2 = τ ω * (|w ω| * τ ω) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h1 (mul_nonneg (abs_nonneg _) h2)

/-- **Velocity and position from the acceleration**: a `C²` function that vanishes on `(−∞, 0]`
with `‖g''‖ ≤ C` has `‖g'(t)‖ ≤ C t` and `‖g(t)‖ ≤ C t²/2` for `t ≥ 0`. -/
theorem norm_le_of_deriv_deriv_le {g : ℝ → E} (hg : ContDiff ℝ 2 g) (h0 : ∀ t ≤ 0, g t = 0)
    {C : ℝ} (hC : ∀ t, ‖deriv (deriv g) t‖ ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    ‖deriv g t‖ ≤ C * t ∧ ‖g t‖ ≤ C * t ^ 2 / 2 := by
  have hg1 : ContDiff ℝ 1 (deriv g) := ((contDiff_succ_iff_deriv (n := 1)).mp hg).2.2
  have hdg : ∀ s, HasDerivAt g (deriv g s) s := fun s =>
    ((hg.differentiable (by norm_num)) s).hasDerivAt
  have hdg' : ∀ s, HasDerivAt (deriv g) (deriv (deriv g) s) s := fun s =>
    ((hg1.differentiable one_ne_zero) s).hasDerivAt
  have hd0 : deriv g 0 = 0 :=
    eq_zero_of_lt_zero hg1.continuous (fun s hs => deriv_eq_zero_of_lt_zero h0 hs) 0 le_rfl
  have hv : ∀ s, 0 ≤ s → ‖deriv g s‖ ≤ C * s := by
    intro s hs
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ) (f := deriv g)
      (fun x _ => (hdg' x).hasDerivWithinAt) (fun x _ => hC x) convex_univ (mem_univ 0)
      (mem_univ s)
    rwa [hd0, sub_zero, sub_zero, Real.norm_of_nonneg hs] at this
  refine ⟨hv t ht, ?_⟩
  have hfence := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := t)
    (f := g) (f' := deriv g) (B := fun r => C * r ^ 2 / 2) (B' := fun r => C * r)
    (fun r _ => (hdg r).continuousAt.continuousWithinAt)
    (fun r _ => (hdg r).hasDerivWithinAt) (by simp [h0 0 le_rfl])
    (fun r => by
      have := ((hasDerivAt_pow 2 r).const_mul C).div_const 2
      convert this using 1
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring)
    (fun r hr => hv r hr.1) ⟨ht, le_rfl⟩
  exact hfence

/-- The derivative of a slow function: `d/dt (c f(κt)) = cκ f'(κt)`. -/
theorem deriv_smul_comp_mul {f : ℝ → E} (hf : Differentiable ℝ f) (c κ : ℝ) :
    deriv (fun t => c • f (κ * t)) = fun t => (c * κ) • deriv f (κ * t) := by
  funext t
  have h1 : HasDerivAt (fun t => κ * t) κ t := by
    simpa using (hasDerivAt_id' t).const_mul κ
  have h2 : HasDerivAt (fun t => c • f (κ * t)) (c • κ • deriv f (κ * t)) t :=
    ((hf (κ * t)).hasDerivAt.scomp t h1).const_smul c
  rw [h2.deriv, smul_smul]

end Bounds

end ProjectAinos.SmoothGeometry.DistributedDelay
