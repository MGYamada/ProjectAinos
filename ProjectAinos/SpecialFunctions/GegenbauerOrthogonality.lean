/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.ClassicalPolynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# Orthogonality of the Gegenbauer polynomials in the polar angle

For an integer `l ≥ 0` the real profiles `Fₘ(s) = Re Cₘ^{(l+1)}(s)` (`gegenbauerReal`) are the
radial factors of the scalar harmonics of `S³` (`CurvedPerturbation.closedHarmonic`). In the polar
angle, `s = cos θ`, they are orthogonal for the weight `sin^{2l+2} θ` on `[0, π]`:

* `gegenbauerReal_equation`: Gegenbauer's equation
  `(1 − s²) F″ − (2l + 3) s F′ + m(m + 2l + 2) F = 0` for the real profile, from
  `gegenbauer_equation`.
* `hasDerivAt_angularWronskian`: the Wronskian
  `W(θ) = sin^{2l+3} θ (Fₘ F′ₘ' − F′ₘ Fₘ')(cos θ)` has the derivative
  `(μₘ' − μₘ) sin^{2l+2} θ Fₘ(cos θ) Fₘ'(cos θ)`, `μₘ = m(m + 2l + 2)`; it vanishes at `0` and
  `π`, so there are no singular endpoints.
* `integral_gegenbauerReal_mul_eq_zero`: **orthogonality** for `m ≠ m'`;
  `integral_gegenbauerReal_sq_pos`: the squared norms are positive, since `Fₘ(1) > 0`
  (`gegenbauerReal_one_pos`).
-/

@[expose] public section

noncomputable section

open Polynomial Real Set Filter MeasureTheory intervalIntegral
open scoped Nat Topology ContDiff

namespace ProjectAinos.SpecialFunctions.ClassicalPolynomial

/-- The real Gegenbauer profile `Fₘ(s) = Re Cₘ^{(l+1)}(s)`. -/
def gegenbauerReal (l m : ℕ) (s : ℝ) : ℝ := ((gegenbauer ((l : ℂ) + 1) m).eval (s : ℂ)).re

/-- The real part of a complex polynomial on the real line. -/
def realEval (p : ℂ[X]) (s : ℝ) : ℝ := (p.eval (s : ℂ)).re

theorem hasDerivAt_realEval (p : ℂ[X]) (s : ℝ) :
    HasDerivAt (realEval p) (realEval p.derivative s) s :=
  (p.hasDerivAt (s : ℂ)).real_of_complex

theorem continuous_realEval (p : ℂ[X]) : Continuous (realEval p) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_realEval p s).continuousAt

theorem contDiff_realEval (p : ℂ[X]) : ContDiff ℝ ∞ (realEval p) := by
  have hp : ContDiff ℂ ∞ (fun z : ℂ => p.eval z) := by simpa using p.contDiff_aeval (𝕜 := ℂ) ∞
  exact hp.real_of_complex

theorem contDiff_gegenbauerReal (l m : ℕ) : ContDiff ℝ ∞ (gegenbauerReal l m) :=
  contDiff_realEval _

theorem gegenbauerReal_eq (l m : ℕ) :
    gegenbauerReal l m = realEval (gegenbauer ((l : ℂ) + 1) m) := rfl

/-- **Gegenbauer's equation** for the real profile. -/
theorem gegenbauerReal_equation (l m : ℕ) (s : ℝ) :
    let p := gegenbauer ((l : ℂ) + 1) m
    (1 - s ^ 2) * realEval p.derivative.derivative s - (2 * l + 3) * s * realEval p.derivative s +
      (m : ℝ) * (m + 2 * l + 2) * realEval p s = 0 := by
  intro p
  have h := congrArg (Polynomial.eval (s : ℂ)) (gegenbauer_equation ((l : ℂ) + 1) m)
  change eval _ ((1 - X ^ 2) * p.derivative.derivative - C (2 * ((l : ℂ) + 1) + 1) * X *
    p.derivative + C (m * (m + 2 * ((l : ℂ) + 1))) * p) = eval _ 0 at h
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_zero, eval_pow, eval_one] at h
  have eq : (((1 - s ^ 2 : ℝ) : ℂ)) * p.derivative.derivative.eval (s : ℂ) -
      (((2 * (l : ℝ) + 3) * s : ℝ) : ℂ) * p.derivative.eval (s : ℂ) +
      (((m : ℝ) * (m + 2 * l + 2) : ℝ) : ℂ) * p.eval (s : ℂ) = 0 := by
    push_cast; linear_combination h
  have re := congrArg Complex.re eq
  simpa only [realEval, Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul,
    Complex.zero_re] using re

/-- The eigenvalue `μₘ = m(m + 2l + 2)`. -/
def gegenbauerEigen (l m : ℕ) : ℝ := (m : ℝ) * (m + 2 * l + 2)

theorem gegenbauerEigen_injective (l : ℕ) : Function.Injective (gegenbauerEigen l) := by
  intro m m' h
  simp only [gegenbauerEigen] at h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : (m : ℝ) < m' := by exact_mod_cast hlt
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  · have : (m' : ℝ) < m := by exact_mod_cast hlt
    nlinarith [(Nat.cast_nonneg m' : (0 : ℝ) ≤ m'), (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]

/-- The angular Wronskian `W(θ) = sin^{2l+3} θ (Fₘ F′ₘ' − F′ₘ Fₘ')(cos θ)`. -/
def angularWronskian (l m m' : ℕ) (θ : ℝ) : ℝ :=
  let p := gegenbauer ((l : ℂ) + 1) m
  let p' := gegenbauer ((l : ℂ) + 1) m'
  sin θ ^ (2 * l + 3) * (realEval p (cos θ) * realEval p'.derivative (cos θ) -
    realEval p.derivative (cos θ) * realEval p' (cos θ))

/-- **The derivative of the angular Wronskian.** -/
theorem hasDerivAt_angularWronskian (l m m' : ℕ) (θ : ℝ) :
    HasDerivAt (angularWronskian l m m')
      ((gegenbauerEigen l m' - gegenbauerEigen l m) * sin θ ^ (2 * l + 2) *
        (gegenbauerReal l m (cos θ) * gegenbauerReal l m' (cos θ))) θ := by
  set p := gegenbauer ((l : ℂ) + 1) m
  set p' := gegenbauer ((l : ℂ) + 1) m'
  have hc := hasDerivAt_cos θ
  have d (q : ℂ[X]) : HasDerivAt (fun θ => realEval q (cos θ))
      (realEval q.derivative (cos θ) * -sin θ) θ :=
    (hasDerivAt_realEval q (cos θ)).comp θ hc
  have hs : HasDerivAt (fun θ => sin θ ^ (2 * l + 3))
      ((2 * l + 3 : ℕ) * sin θ ^ (2 * l + 2) * cos θ) θ := by
    have := (hasDerivAt_sin θ).fun_pow (2 * l + 3)
    simpa [Nat.add_sub_cancel] using this
  have hK := ((d p).fun_mul (d p'.derivative)).fun_sub ((d p.derivative).fun_mul (d p'))
  have h := hs.fun_mul hK
  have e1 := gegenbauerReal_equation l m (cos θ)
  have e2 := gegenbauerReal_equation l m' (cos θ)
  dsimp only at e1 e2
  have hsc : sin θ ^ 2 = 1 - cos θ ^ 2 := by rw [sin_sq]
  refine h.congr_deriv ?_
  simp only [gegenbauerEigen, gegenbauerReal_eq]
  push_cast
  linear_combination (-(sin θ ^ (2 * l + 2))) *
    (realEval p (cos θ) * e2 - realEval p' (cos θ) * e1) -
    (sin θ ^ (2 * l + 2)) * (realEval p (cos θ) * realEval p'.derivative.derivative (cos θ) -
      realEval p.derivative.derivative (cos θ) * realEval p' (cos θ)) * hsc

theorem angularWronskian_zero (l m m' : ℕ) : angularWronskian l m m' 0 = 0 := by
  simp [angularWronskian]

theorem angularWronskian_pi (l m m' : ℕ) : angularWronskian l m m' π = 0 := by
  simp [angularWronskian]

theorem continuous_gegenbauerReal (l m : ℕ) : Continuous (gegenbauerReal l m) :=
  continuous_realEval _

/-- **Orthogonality of the Gegenbauer polynomials** in the polar angle. -/
theorem integral_gegenbauerReal_mul_eq_zero (l : ℕ) {m m' : ℕ} (h : m ≠ m') :
    ∫ θ in (0 : ℝ)..π,
      gegenbauerReal l m (cos θ) * gegenbauerReal l m' (cos θ) * sin θ ^ (2 * l + 2) = 0 := by
  have hW := integral_eq_sub_of_hasDerivAt (a := 0) (b := π)
    (fun θ _ => hasDerivAt_angularWronskian l m m' θ)
    ((((continuous_const.mul ((continuous_sin.pow _))).mul
      (((continuous_gegenbauerReal l m).comp continuous_cos).mul
        ((continuous_gegenbauerReal l m').comp continuous_cos)))).intervalIntegrable _ _)
  rw [angularWronskian_zero, angularWronskian_pi, sub_zero] at hW
  have hμ : gegenbauerEigen l m' - gegenbauerEigen l m ≠ 0 :=
    sub_ne_zero.mpr fun e => h (gegenbauerEigen_injective l e).symm
  have e : (fun θ => (gegenbauerEigen l m' - gegenbauerEigen l m) * sin θ ^ (2 * l + 2) *
      (gegenbauerReal l m (cos θ) * gegenbauerReal l m' (cos θ))) = fun θ =>
      (gegenbauerEigen l m' - gegenbauerEigen l m) *
        (gegenbauerReal l m (cos θ) * gegenbauerReal l m' (cos θ) * sin θ ^ (2 * l + 2)) := by
    funext θ; ring
  rw [e, intervalIntegral.integral_const_mul] at hW
  exact (mul_eq_zero.mp hW).resolve_left hμ

/-- The profile at `s = 1`: `Fₘ(1) = (2l + 2)ₘ/m! > 0`. -/
theorem gegenbauerReal_one_pos (l m : ℕ) : 0 < gegenbauerReal l m 1 := by
  have h := gegenbauer_one ((l : ℂ) + 1) m
  have hc : (2 * ((l : ℂ) + 1)) = ((2 * (l + 1) : ℕ) : ℂ) := by push_cast; ring
  rw [hc, ← ascPochhammer_eval_cast] at h
  have hpos : 0 < (ascPochhammer ℕ m).eval (2 * (l + 1)) :=
    ascPochhammer_pos m _ (by positivity)
  simp only [gegenbauerReal, Complex.ofReal_one, h]
  have e : ((((ascPochhammer ℕ m).eval (2 * (l + 1)) : ℕ) : ℂ) / ((m ! : ℕ) : ℂ)) =
      ((((((ascPochhammer ℕ m).eval (2 * (l + 1)) : ℕ) : ℝ) / ((m ! : ℕ) : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
  rw [e, Complex.ofReal_re]
  have : (0 : ℝ) < (((ascPochhammer ℕ m).eval (2 * (l + 1)) : ℕ) : ℝ) := by exact_mod_cast hpos
  positivity

/-- **The squared norms are positive.** -/
theorem integral_gegenbauerReal_sq_pos (l m : ℕ) :
    0 < ∫ θ in (0 : ℝ)..π,
      gegenbauerReal l m (cos θ) * gegenbauerReal l m (cos θ) * sin θ ^ (2 * l + 2) := by
  have hcont : Continuous fun θ => gegenbauerReal l m (cos θ) :=
    (continuous_gegenbauerReal l m).comp continuous_cos
  have hev : ∀ᶠ θ in 𝓝 (0 : ℝ), 0 < gegenbauerReal l m (cos θ) := by
    have h1 : 0 < gegenbauerReal l m (cos 0) := by
      rw [cos_zero]; exact gegenbauerReal_one_pos l m
    exact (hcont.continuousAt (x := 0)).eventually (lt_mem_nhds h1)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set δ' := min δ π with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ pi_pos
  have hint : Continuous fun θ =>
      gegenbauerReal l m (cos θ) * gegenbauerReal l m (cos θ) * sin θ ^ (2 * l + 2) :=
    (hcont.mul hcont).mul (continuous_sin.pow _)
  have hpos : 0 < ∫ θ in (0 : ℝ)..δ',
      gegenbauerReal l m (cos θ) * gegenbauerReal l m (cos θ) * sin θ ^ (2 * l + 2) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hint.intervalIntegrable _ _)
      (fun θ hθ => ?_) hδ'0
    have h1 : 0 < gegenbauerReal l m (cos θ) := hball (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hθ.1]
      exact lt_of_lt_of_le hθ.2 (min_le_left _ _))
    have h2 : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 (lt_of_lt_of_le hθ.2 (min_le_right _ _))
    positivity
  refine hpos.trans_le (intervalIntegral.integral_mono_interval le_rfl hδ'0.le
    (min_le_right _ _) (ae_of_all _ fun θ => ?_) (hint.intervalIntegrable _ _))
  have : 0 ≤ gegenbauerReal l m (cos θ) * gegenbauerReal l m (cos θ) := mul_self_nonneg _
  have h2 : 0 ≤ sin θ ^ (2 * l + 2) := by
    rw [show 2 * l + 2 = 2 * (l + 1) by ring, pow_mul]; positivity
  positivity

end ProjectAinos.SpecialFunctions.ClassicalPolynomial
