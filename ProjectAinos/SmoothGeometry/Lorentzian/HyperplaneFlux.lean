/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorFlux
import Mathlib.Tactic

/-!
# The flux of a conserved current through tilted hyperplanes

Space-time is `MinkowskiModel 3` with the points `vector t y`, `y ∈ ℝ³ = EuclideanSpace ℝ (Fin 3)`.
A current is a family `J k` (`k : Fin 4`) of functions on space-time; it is conserved on an open
set `O` when `Σ_k ∂_k J^k = 0` there.

**Hyperplanes as graphs.** Every hyperplane that is not vertical is the graph
`x⁰ = c + ⟪v, x⟫` over space.

* `graphIntegrand J c v y = J⁰ − Σ_α v_α J^α` at `(c + ⟪v, y⟫, y)`, and `graphFlux J c v` its
  integral over `ℝ³`: the integral of the three-form `ι_J (dx⁰ ∧ dx¹ ∧ dx² ∧ dx³)` over the
  graph, oriented by `dy¹ ∧ dy² ∧ dy³` (`graphIntegrand_eq_det`: the integrand is the determinant
  of `J` and the three tangent vectors `(v_α, e_α)` of the graph). For `v = 0` it is the integral
  of `J⁰` over the slice `x⁰ = c` (`graphFlux_zero`). `graphFluxBall` is the integral over the
  ball `‖y‖ < R` of space, the cut-off at the radius `R`.

**The wedge.** The hyperplanes `x⁰ = (1 − s) c₀ + s (c₁ + ⟪v, x⟫)`, `s ∈ [0, 1]`, interpolate
between the slice `x⁰ = c₀` and the graph `x⁰ = c₁ + ⟪v, x⟫` (`wedgePoint`, `wedgeIntegrand`).

* `hasDerivAt_wedgeIntegrand`, `divergence_wedgeField`: **the derivative of the integrand in `s`
  is minus the spatial divergence** of `V_α = (c₁ − c₀ + ⟪v, y⟫) J^α`, by the conservation of
  `J`.
* `abs_flux_wedgeField_le`: if `|J| ≤ K/‖y‖⁴` on the wedge beyond `R₀`, the flux of `V` through
  the sphere of radius `R` is at most `12π K (|c₁ − c₀| + ‖v‖R)/R²`, the side of the wedge.
* `abs_graphFluxBall_sub_le`: the cut-off fluxes through the two hyperplanes differ by at most
  this side integral, by the divergence theorem on the ball and the mean value theorem in `s`.
* `integral_eq_graphFlux`: **the flux of a conserved current through the tilted hyperplane is its
  integral over the slice**, when the current is `O(r⁻⁴)` uniformly on the wedge.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.Hyperplane

open Minkowski

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Hyperplanes as graphs over space -/

/-- The integrand `J⁰ − Σ_α v_α J^α` of the flux of `J` at the point `(c + ⟪v, y⟫, y)` of the
hyperplane `x⁰ = c + ⟪v, x⟫`. -/
def graphIntegrand (J : Fin 4 → MinkowskiModel 3 → ℝ) (c : ℝ) (v y : E3) : ℝ :=
  J 0 (vector (c + inner ℝ v y) y) - ∑ α, v α * J α.succ (vector (c + inner ℝ v y) y)

/-- **The flux of `J` through the hyperplane `x⁰ = c + ⟪v, x⟫`**, the integral over space of the
three-form `ι_J (dx⁰ ∧ dx¹ ∧ dx² ∧ dx³)` pulled back by the graph map `y ↦ (c + ⟪v, y⟫, y)`. -/
def graphFlux (J : Fin 4 → MinkowskiModel 3 → ℝ) (c : ℝ) (v : E3) : ℝ :=
  ∫ y, graphIntegrand J c v y

/-- The flux through the part `‖y‖ < R` of the hyperplane, the cut-off at the radius `R`. -/
def graphFluxBall (J : Fin 4 → MinkowskiModel 3 → ℝ) (c : ℝ) (v : E3) (R : ℝ) : ℝ :=
  ∫ y in ball (0 : E3) R, graphIntegrand J c v y

theorem graphIntegrand_zero (J : Fin 4 → MinkowskiModel 3 → ℝ) (c : ℝ) (y : E3) :
    graphIntegrand J c 0 y = J 0 (vector c y) := by
  simp [graphIntegrand]

/-- **On a co-ordinate slice the flux is the integral of `J⁰`.** -/
theorem graphFlux_zero (J : Fin 4 → MinkowskiModel 3 → ℝ) (c : ℝ) :
    graphFlux J c 0 = ∫ y, J 0 (vector c y) := by
  simp only [graphFlux, graphIntegrand_zero]

theorem vector_one (t : ℝ) (y : E3) : vector t y 1 = y 0 := rfl
theorem vector_two (t : ℝ) (y : E3) : vector t y 2 = y 1 := rfl
theorem vector_three (t : ℝ) (y : E3) : vector t y 3 = y 2 := rfl

/-- The tangent vector `(v_α, e_α)` of the graph `x⁰ = c + ⟪v, x⟫` along the axis `α`. -/
def graphTangent (v : E3) (α : Fin 3) : MinkowskiModel 3 :=
  vector (v α) (EuclideanSpace.single α 1)

/-- **The integrand is the three-form**: `J⁰ − Σ_α v_α J^α` is the determinant of the matrix with
the columns `J` and the tangent vectors `(v_α, e_α)` of the graph, i.e. the value of
`ι_J (dx⁰ ∧ dx¹ ∧ dx² ∧ dx³)` on the three tangent vectors. -/
theorem graphIntegrand_eq_det (J : Fin 4 → MinkowskiModel 3 → ℝ) (c : ℝ) (v y : E3) :
    graphIntegrand J c v y = (Matrix.of fun i j : Fin 4 =>
      Fin.cases (J i (vector (c + inner ℝ v y) y)) (fun α => graphTangent v α i) j).det := by
  rw [Matrix.det_succ_column_zero]
  simp only [Fin.sum_univ_four, Matrix.of_apply, Fin.cases_zero, graphTangent]
  simp [Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove, Fin.lt_def, graphIntegrand,
    Fin.sum_univ_three, vector_one, vector_two, vector_three]
  ring

/-! ### The family of hyperplanes between a slice and a graph -/

variable (J : Fin 4 → MinkowskiModel 3 → ℝ) (c₀ c₁ : ℝ) (v : E3)

/-- The time `(1 − s) c₀ + s (c₁ + ⟪v, y⟫)` above `y` of the hyperplane `s` of the wedge. -/
def wedgeTime (s : ℝ) (y : E3) : ℝ := (1 - s) * c₀ + s * (c₁ + inner ℝ v y)

/-- The point above `y` of the hyperplane `s` of the wedge. -/
def wedgePoint (s : ℝ) (y : E3) : MinkowskiModel 3 := vector (wedgeTime c₀ c₁ v s y) y

/-- The integrand `J⁰ − s Σ_α v_α J^α` of the flux through the hyperplane `s`. -/
def wedgeIntegrand (s : ℝ) (y : E3) : ℝ :=
  J 0 (wedgePoint c₀ c₁ v s y) - s * ∑ α, v α * J α.succ (wedgePoint c₀ c₁ v s y)

/-- The rate `∂ₛ x⁰ = c₁ − c₀ + ⟪v, y⟫` at which the hyperplanes move. -/
def wedgeSpeed (y : E3) : ℝ := c₁ - c₀ + inner ℝ v y

/-- The field `V_α = (c₁ − c₀ + ⟪v, y⟫) J^α` on space, whose divergence is minus the derivative of
the integrand in `s`. -/
def wedgeField (s : ℝ) (α : Fin 3) (y : E3) : ℝ :=
  wedgeSpeed c₀ c₁ v y * J α.succ (wedgePoint c₀ c₁ v s y)

/-- The derivative of the integrand in `s`. -/
def wedgeDeriv (s : ℝ) (y : E3) : ℝ :=
  wedgeSpeed c₀ c₁ v y * fderiv ℝ (J 0) (wedgePoint c₀ c₁ v s y) (Pi.single 0 1) -
    ∑ α, v α * J α.succ (wedgePoint c₀ c₁ v s y) -
    s * ∑ α, v α * (wedgeSpeed c₀ c₁ v y *
      fderiv ℝ (J α.succ) (wedgePoint c₀ c₁ v s y) (Pi.single 0 1))

theorem wedgePoint_zero (y : E3) : wedgePoint c₀ c₁ v 0 y = vector c₀ y := by
  simp [wedgePoint, wedgeTime]

theorem wedgePoint_one (y : E3) : wedgePoint c₀ c₁ v 1 y = vector (c₁ + inner ℝ v y) y := by
  simp [wedgePoint, wedgeTime]

theorem wedgeIntegrand_zero (y : E3) : wedgeIntegrand J c₀ c₁ v 0 y = J 0 (vector c₀ y) := by
  simp [wedgeIntegrand, wedgePoint_zero]

theorem wedgeIntegrand_one (y : E3) :
    wedgeIntegrand J c₀ c₁ v 1 y = graphIntegrand J c₁ v y := by
  simp [wedgeIntegrand, wedgePoint_one, graphIntegrand]

theorem wedgePoint_eq (s : ℝ) (y : E3) :
    wedgePoint c₀ c₁ v s y = Wave.timeSpaceEquiv.symm (wedgeTime c₀ c₁ v s y, y) := rfl

theorem continuous_wedgePoint :
    Continuous fun p : ℝ × E3 => wedgePoint c₀ c₁ v p.1 p.2 := by
  have h : (fun p : ℝ × E3 => wedgePoint c₀ c₁ v p.1 p.2) = fun p : ℝ × E3 =>
      Wave.timeSpaceEquiv.symm ((1 - p.1) * c₀ + p.1 * (c₁ + inner ℝ v p.2), p.2) := rfl
  rw [h]
  exact Wave.timeSpaceEquiv.symm.continuous.comp (by fun_prop)

theorem contDiff_wedgePoint (s : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun y => wedgePoint c₀ c₁ v s y := by
  have h : (fun y => wedgePoint c₀ c₁ v s y) = fun y : E3 =>
      Wave.timeSpaceEquiv.symm ((1 - s) * c₀ + s * (c₁ + innerSL ℝ v y), y) := rfl
  rw [h]
  exact Wave.timeSpaceEquiv.symm.contDiff.comp
    ((contDiff_const.add (contDiff_const.mul (contDiff_const.add (innerSL ℝ v).contDiff))).prodMk
      contDiff_id)

theorem contDiff_wedgeSpeed {n : WithTop ℕ∞} : ContDiff ℝ n (wedgeSpeed c₀ c₁ v) :=
  contDiff_const.add (innerSL ℝ v).contDiff

/-- The hyperplanes move along the time axis at the rate `wedgeSpeed`. -/
theorem hasDerivAt_wedgePoint (s : ℝ) (y : E3) :
    HasDerivAt (fun s => wedgePoint c₀ c₁ v s y)
      (wedgeSpeed c₀ c₁ v y • (Pi.single 0 1 : MinkowskiModel 3)) s := by
  have ht : HasDerivAt (fun s => wedgeTime c₀ c₁ v s y) (wedgeSpeed c₀ c₁ v y) s := by
    have h := (((hasDerivAt_const s (1 : ℝ)).fun_sub (hasDerivAt_id s)).mul_const c₀).fun_add
      ((hasDerivAt_id s).mul_const (c₁ + inner ℝ v y))
    exact h.congr_deriv (by simp only [wedgeSpeed]; ring)
  exact (hasDerivAt_vector_time (wedgeTime c₀ c₁ v s y) y).scomp s ht

/-- The derivative of the hyperplane `s` over space. -/
theorem hasFDerivAt_wedgePoint_space (s : ℝ) (y : E3) :
    HasFDerivAt (fun y => wedgePoint c₀ c₁ v s y)
      ((Wave.timeSpaceEquiv.symm : ℝ × E3 →L[ℝ] MinkowskiModel 3).comp
        ((s • innerSL ℝ v).prod (ContinuousLinearMap.id ℝ E3))) y := by
  have ht : HasFDerivAt (fun y => wedgeTime c₀ c₁ v s y) (s • innerSL ℝ v) y := by
    exact (((innerSL ℝ v).hasFDerivAt (x := y)).const_add c₁).const_mul s |>.const_add
      ((1 - s) * c₀)
  exact Wave.timeSpaceEquiv.symm.hasFDerivAt.comp y (ht.prodMk (hasFDerivAt_id y))

theorem vector_single (a : ℝ) (α : Fin 3) :
    vector a (EuclideanSpace.single α 1) =
      a • (Pi.single 0 1 : MinkowskiModel 3) + Pi.single α.succ 1 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [vector, (Fin.succ_ne_zero α).symm]
  · simp [vector, Pi.single_apply, Fin.succ_inj, Fin.succ_ne_zero, eq_comm]

/-- The derivative of a function of space-time along the axis `α` of the hyperplane `s`. -/
theorem fderiv_comp_wedgePoint {f : MinkowskiModel 3 → ℝ} {s : ℝ} {y : E3}
    (hf : DifferentiableAt ℝ f (wedgePoint c₀ c₁ v s y)) (α : Fin 3) :
    fderiv ℝ (fun y => f (wedgePoint c₀ c₁ v s y)) y (EuclideanSpace.single α 1) =
      s * v α * fderiv ℝ f (wedgePoint c₀ c₁ v s y) (Pi.single 0 1) +
        fderiv ℝ f (wedgePoint c₀ c₁ v s y) (Pi.single α.succ 1) := by
  have h := hf.hasFDerivAt.comp y (hasFDerivAt_wedgePoint_space c₀ c₁ v s y)
  rw [show (fun y => f (wedgePoint c₀ c₁ v s y)) = f ∘ fun y => wedgePoint c₀ c₁ v s y from rfl,
    h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, Wave.timeSpaceEquiv_symm_apply,
    EuclideanSpace.inner_single_right, smul_eq_mul, one_mul, conj_trivial]
  rw [vector_single, map_add, map_smul, smul_eq_mul]

/-- **The derivative of the integrand in `s`.** -/
theorem hasDerivAt_wedgeIntegrand {s : ℝ} {y : E3}
    (hJ : ∀ k, DifferentiableAt ℝ (J k) (wedgePoint c₀ c₁ v s y)) :
    HasDerivAt (fun s => wedgeIntegrand J c₀ c₁ v s y) (wedgeDeriv J c₀ c₁ v s y) s := by
  have hp := hasDerivAt_wedgePoint c₀ c₁ v s y
  have hk (k : Fin 4) : HasDerivAt (fun s => J k (wedgePoint c₀ c₁ v s y))
      (wedgeSpeed c₀ c₁ v y * fderiv ℝ (J k) (wedgePoint c₀ c₁ v s y) (Pi.single 0 1)) s := by
    have h := (hJ k).hasFDerivAt.comp_hasDerivAt s hp
    rwa [map_smul, smul_eq_mul] at h
  have hsum : HasDerivAt (fun s => ∑ α : Fin 3, v α * J α.succ (wedgePoint c₀ c₁ v s y))
      (∑ α : Fin 3, v α * (wedgeSpeed c₀ c₁ v y *
        fderiv ℝ (J α.succ) (wedgePoint c₀ c₁ v s y) (Pi.single 0 1))) s :=
    HasDerivAt.fun_sum fun α _ => (hk α.succ).const_mul (v α)
  have h := (hk 0).fun_sub ((hasDerivAt_id s).fun_mul hsum)
  exact h.congr_deriv (by simp only [wedgeDeriv, id]; ring)

/-- **The derivative in `s` is minus the divergence of the field `V`**, where `J` is conserved. -/
theorem divergence_wedgeField {s : ℝ} {y : E3}
    (hJ : ∀ k, DifferentiableAt ℝ (J k) (wedgePoint c₀ c₁ v s y))
    (hdiv : ∑ k, fderiv ℝ (J k) (wedgePoint c₀ c₁ v s y) (Pi.single k 1) = 0) :
    Sphere.divergence (wedgeField J c₀ c₁ v s) y = -wedgeDeriv J c₀ c₁ v s y := by
  have hw : HasFDerivAt (wedgeSpeed c₀ c₁ v) (innerSL ℝ v) y :=
    ((innerSL ℝ v).hasFDerivAt (x := y)).const_add (c₁ - c₀)
  have hterm (α : Fin 3) : fderiv ℝ (wedgeField J c₀ c₁ v s α) y (EuclideanSpace.single α 1) =
      wedgeSpeed c₀ c₁ v y * (s * v α * fderiv ℝ (J α.succ) (wedgePoint c₀ c₁ v s y)
        (Pi.single 0 1) + fderiv ℝ (J α.succ) (wedgePoint c₀ c₁ v s y) (Pi.single α.succ 1)) +
      J α.succ (wedgePoint c₀ c₁ v s y) * v α := by
    have hJα : DifferentiableAt ℝ (fun y => J α.succ (wedgePoint c₀ c₁ v s y)) y :=
      (hJ α.succ).comp y (hasFDerivAt_wedgePoint_space c₀ c₁ v s y).differentiableAt
    have h : HasFDerivAt (fun y => wedgeSpeed c₀ c₁ v y * J α.succ (wedgePoint c₀ c₁ v s y)) _ y :=
      hw.mul hJα.hasFDerivAt
    rw [show wedgeField J c₀ c₁ v s α = fun y => wedgeSpeed c₀ c₁ v y *
      J α.succ (wedgePoint c₀ c₁ v s y) from rfl, h.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul,
      innerSL_apply_apply, EuclideanSpace.inner_single_right, one_mul, conj_trivial]
    rw [fderiv_comp_wedgePoint c₀ c₁ v (hJ α.succ)]
  rw [Fin.sum_univ_succ] at hdiv
  simp only [Sphere.divergence, hterm, wedgeDeriv]
  have e1 (α : Fin 3) : wedgeSpeed c₀ c₁ v y * (s * v α * fderiv ℝ (J α.succ)
      (wedgePoint c₀ c₁ v s y) (Pi.single 0 1) + fderiv ℝ (J α.succ) (wedgePoint c₀ c₁ v s y)
        (Pi.single α.succ 1)) + J α.succ (wedgePoint c₀ c₁ v s y) * v α =
      s * (v α * (wedgeSpeed c₀ c₁ v y * fderiv ℝ (J α.succ) (wedgePoint c₀ c₁ v s y)
        (Pi.single 0 1))) + wedgeSpeed c₀ c₁ v y * fderiv ℝ (J α.succ)
          (wedgePoint c₀ c₁ v s y) (Pi.single α.succ 1) +
        v α * J α.succ (wedgePoint c₀ c₁ v s y) := by ring
  simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum]
  linear_combination wedgeSpeed c₀ c₁ v y * hdiv

/-! ### The cut-off fluxes through the hyperplanes of the wedge -/

variable {J c₀ c₁ v} {O : Set (MinkowskiModel 3)}

/-- Where the hyperplanes `s ∈ [0, 1]` lie in an open set, so do the parts over a closed ball of
the hyperplanes `s ∈ [−δ, 1 + δ]` for some `δ > 0`. -/
theorem exists_wedge_nhds (hO : IsOpen O)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ O) (R : ℝ) :
    ∃ δ > 0, ∀ s ∈ Icc (-δ) (1 + δ), ∀ y ∈ closedBall (0 : E3) R,
      wedgePoint c₀ c₁ v s y ∈ O := by
  set Ω : Set (ℝ × E3) := {p | wedgePoint c₀ c₁ v p.1 p.2 ∈ O} with hΩdef
  have hΩ : IsOpen Ω := hO.preimage (continuous_wedgePoint c₀ c₁ v)
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E3) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKΩ : Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E3) R ⊆ Ω := fun p hp => hW p.1 hp.1 p.2
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hΩ hKΩ
  refine ⟨δ / 2, by positivity, fun s hs y hy => ?_⟩
  suffices hsy : ((s, y) : ℝ × E3) ∈ Ω from hsy
  refine hsub ?_
  rw [mem_thickening_iff]
  refine ⟨(max 0 (min s 1), y), ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩, hy⟩, ?_⟩
  rw [Prod.dist_eq, dist_self, Real.dist_eq]
  refine max_lt ?_ hδ
  rcases le_or_gt s 0 with h | h
  · rw [min_eq_left (by linarith), max_eq_left h, sub_zero, abs_of_nonpos h]
    linarith [hs.1]
  · rcases le_or_gt s 1 with h' | h'
    · rw [min_eq_left h', max_eq_right h.le, sub_self, abs_zero]
      exact hδ
    · rw [min_eq_right h'.le, max_eq_right zero_le_one, abs_of_pos (by linarith)]
      linarith [hs.2]

theorem continuousOn_wedgeIntegrand (hJ : ∀ k, ContinuousOn (J k) O) :
    ContinuousOn (fun p : ℝ × E3 => wedgeIntegrand J c₀ c₁ v p.1 p.2)
      {p | wedgePoint c₀ c₁ v p.1 p.2 ∈ O} := by
  have hc := (continuous_wedgePoint c₀ c₁ v).continuousOn (s := {p : ℝ × E3 |
    wedgePoint c₀ c₁ v p.1 p.2 ∈ O})
  have hk (k : Fin 4) : ContinuousOn (fun p : ℝ × E3 => J k (wedgePoint c₀ c₁ v p.1 p.2))
      {p | wedgePoint c₀ c₁ v p.1 p.2 ∈ O} := (hJ k).comp hc fun p hp => hp
  exact (hk 0).sub (continuousOn_fst.mul (continuousOn_finsetSum _ fun α _ =>
    continuousOn_const.mul (hk α.succ)))

theorem continuousOn_wedgeDeriv (hO : IsOpen O) (hJ : ∀ k, ContDiffOn ℝ 1 (J k) O) :
    ContinuousOn (fun p : ℝ × E3 => wedgeDeriv J c₀ c₁ v p.1 p.2)
      {p | wedgePoint c₀ c₁ v p.1 p.2 ∈ O} := by
  have hc := (continuous_wedgePoint c₀ c₁ v).continuousOn (s := {p : ℝ × E3 |
    wedgePoint c₀ c₁ v p.1 p.2 ∈ O})
  have hk (k : Fin 4) : ContinuousOn (fun p : ℝ × E3 => J k (wedgePoint c₀ c₁ v p.1 p.2))
      {p | wedgePoint c₀ c₁ v p.1 p.2 ∈ O} := (hJ k).continuousOn.comp hc fun p hp => hp
  have hd (k : Fin 4) : ContinuousOn (fun p : ℝ × E3 =>
      fderiv ℝ (J k) (wedgePoint c₀ c₁ v p.1 p.2) (Pi.single 0 1))
      {p | wedgePoint c₀ c₁ v p.1 p.2 ∈ O} :=
    (((hJ k).continuousOn_fderiv_of_isOpen hO le_rfl).comp hc fun p hp => hp).clm_apply
      continuousOn_const
  have hw : ContinuousOn (fun p : ℝ × E3 => wedgeSpeed c₀ c₁ v p.2)
      {p | wedgePoint c₀ c₁ v p.1 p.2 ∈ O} :=
    ((contDiff_wedgeSpeed c₀ c₁ v (n := 0)).continuous.comp continuous_snd).continuousOn
  exact ((hw.mul (hd 0)).sub (continuousOn_finsetSum _ fun α _ =>
    continuousOn_const.mul (hk α.succ))).sub (continuousOn_fst.mul
      (continuousOn_finsetSum _ fun α _ => continuousOn_const.mul (hw.mul (hd α.succ))))

/-- The cut-off flux through the hyperplane `s` is differentiable in `s`, with the derivative
`∫_{‖y‖ < R} ∂ₛ(J⁰ − s Σ_α v_α J^α)`. -/
theorem hasDerivAt_integral_ball_wedge (hO : IsOpen O) (hJ : ∀ k, ContDiffOn ℝ 1 (J k) O)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ O) (R : ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => ∫ y in ball (0 : E3) R, wedgeIntegrand J c₀ c₁ v s y)
      (∫ y in ball (0 : E3) R, wedgeDeriv J c₀ c₁ v s y) s := by
  obtain ⟨δ, hδ, hδW⟩ := exists_wedge_nhds hO hW R
  have hK2 : IsCompact (Icc (-δ) (1 + δ) ×ˢ closedBall (0 : E3) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hK2Ω : Icc (-δ) (1 + δ) ×ˢ closedBall (0 : E3) R ⊆
      {p : ℝ × E3 | wedgePoint c₀ c₁ v p.1 p.2 ∈ O} := fun p hp => hδW p.1 hp.1 p.2 hp.2
  obtain ⟨C, hC⟩ := hK2.exists_bound_of_continuousOn
    ((continuousOn_wedgeDeriv (c₀ := c₀) (c₁ := c₁) (v := v) hO hJ).mono hK2Ω)
  have hnear : ∀ s' ∈ ball s δ, s' ∈ Icc (-δ) (1 + δ) := fun s' hs' => by
    rw [mem_ball, Real.dist_eq, abs_lt] at hs'
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hcont (s' : ℝ) (hs' : s' ∈ Icc (-δ) (1 + δ)) :
      ContinuousOn (fun y => wedgeIntegrand J c₀ c₁ v s' y) (closedBall (0 : E3) R) := by
    have hsec : Continuous fun y : E3 => ((s', y) : ℝ × E3) := by fun_prop
    have h := (continuousOn_wedgeIntegrand (c₀ := c₀) (c₁ := c₁) (v := v)
      fun k => (hJ k).continuousOn).comp hsec.continuousOn (fun y hy => hδW s' hs' y hy)
    exact h
  have hcont' : ContinuousOn (fun y => wedgeDeriv J c₀ c₁ v s y) (closedBall (0 : E3) R) := by
    have hsec : Continuous fun y : E3 => ((s, y) : ℝ × E3) := by fun_prop
    have hs' : s ∈ Icc (-δ) (1 + δ) := hnear s (mem_ball_self hδ)
    have h := (continuousOn_wedgeDeriv (c₀ := c₀) (c₁ := c₁) (v := v) hO hJ).comp
      hsec.continuousOn (fun y hy => hδW s hs' y hy)
    exact h
  set μ := volume.restrict (ball (0 : E3) R) with hμ
  have h1 : ∀ᶠ s' in 𝓝 s, AEStronglyMeasurable (fun y => wedgeIntegrand J c₀ c₁ v s' y) μ := by
    filter_upwards [ball_mem_nhds s hδ] with s' hs'
    exact ((hcont s' (hnear s' hs')).mono ball_subset_closedBall).aestronglyMeasurable
      measurableSet_ball
  have h2 : Integrable (fun y => wedgeIntegrand J c₀ c₁ v s y) μ :=
    ((hcont s (hnear s (mem_ball_self hδ))).integrableOn_compact
      (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have h3 : AEStronglyMeasurable (fun y => wedgeDeriv J c₀ c₁ v s y) μ :=
    (hcont'.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  have h4 : ∀ᵐ y ∂μ, ∀ s' ∈ ball s δ, ‖wedgeDeriv J c₀ c₁ v s' y‖ ≤ C :=
    ae_restrict_of_forall_mem measurableSet_ball fun y hy s' hs' =>
      hC (s', y) ⟨hnear s' hs', ball_subset_closedBall hy⟩
  have h5 : Integrable (fun _ : E3 => C) μ := integrableOn_const measure_ball_lt_top.ne
  have h6 : ∀ᵐ y ∂μ, ∀ s' ∈ ball s δ, HasDerivAt (fun s => wedgeIntegrand J c₀ c₁ v s y)
      (wedgeDeriv J c₀ c₁ v s' y) s' := by
    refine ae_restrict_of_forall_mem measurableSet_ball fun y hy s' hs' => ?_
    have hp := hδW s' (hnear s' hs') y (ball_subset_closedBall hy)
    exact hasDerivAt_wedgeIntegrand J c₀ c₁ v fun k =>
      ((hJ k).differentiableOn one_ne_zero _ hp).differentiableAt (hO.mem_nhds hp)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds s hδ) h1 h2 h3 h4 h5
    h6).2

/-- **The derivative of the cut-off flux is minus the flux of `V` through the sphere**, by the
divergence theorem on the ball. -/
theorem integral_ball_wedgeDeriv (hO : IsOpen O) (hJ : ∀ k, ContDiffOn ℝ 1 (J k) O)
    (hdiv : ∀ z ∈ O, ∑ k, fderiv ℝ (J k) z (Pi.single k 1) = 0)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ O) {R : ℝ} (hR : 0 ≤ R) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ y in ball (0 : E3) R, wedgeDeriv J c₀ c₁ v s y =
      -Sphere.flux (wedgeField J c₀ c₁ v s) R := by
  set W : Set E3 := {y | wedgePoint c₀ c₁ v s y ∈ O} with hWdef
  have hWo : IsOpen W := hO.preimage (contDiff_wedgePoint c₀ c₁ v s (n := 0)).continuous
  have hV (α : Fin 3) : ContDiffOn ℝ 1 (wedgeField J c₀ c₁ v s α) W :=
    (contDiff_wedgeSpeed c₀ c₁ v).contDiffOn.mul
      ((hJ α.succ).comp (contDiff_wedgePoint c₀ c₁ v s).contDiffOn fun y hy => hy)
  have h := Sphere.flux_sub_flux hWo hV le_rfl hR (fun x _ _ => hW s hs x)
  rw [Sphere.flux_zero, sub_zero] at h
  rw [h, setIntegral_congr_set (Sphere.shell_zero_ae_eq R), ← integral_neg]
  refine setIntegral_congr_fun measurableSet_ball fun y _ => ?_
  have hp := hW s hs y
  rw [divergence_wedgeField J c₀ c₁ v (fun k =>
    ((hJ k).differentiableOn one_ne_zero _ hp).differentiableAt (hO.mem_nhds hp)) (hdiv _ hp),
    neg_neg]

/-- The cut-off fluxes through the two ends of the wedge differ by at most a bound of the flux
of `V` through the sphere, by the mean value theorem in `s`. -/
theorem abs_integral_ball_wedge_sub_le (hO : IsOpen O) (hJ : ∀ k, ContDiffOn ℝ 1 (J k) O)
    (hdiv : ∀ z ∈ O, ∑ k, fderiv ℝ (J k) z (Pi.single k 1) = 0)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ O) {R B : ℝ} (hR : 0 ≤ R)
    (hB : ∀ s ∈ Icc (0 : ℝ) 1, |Sphere.flux (wedgeField J c₀ c₁ v s) R| ≤ B) :
    |(∫ y in ball (0 : E3) R, wedgeIntegrand J c₀ c₁ v 1 y) -
      ∫ y in ball (0 : E3) R, wedgeIntegrand J c₀ c₁ v 0 y| ≤ B := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s => ∫ y in ball (0 : E3) R, wedgeIntegrand J c₀ c₁ v s y)
    (f' := fun s => ∫ y in ball (0 : E3) R, wedgeDeriv J c₀ c₁ v s y) (C := B)
    (fun s hs => (hasDerivAt_integral_ball_wedge hO hJ hW R hs).hasDerivWithinAt)
    (fun s hs => by
      rw [integral_ball_wedgeDeriv hO hJ hdiv hW hR (Ico_subset_Icc_self hs), norm_neg,
        Real.norm_eq_abs]
      exact hB s (Ico_subset_Icc_self hs)) 1 ⟨zero_le_one, le_rfl⟩
  simpa [Real.norm_eq_abs] using h

/-- **The side of the wedge**: if `|J^k| ≤ K/‖y‖⁴` on the wedge beyond the radius `R₀`, the flux of
`V = (c₁ − c₀ + ⟪v, y⟫) J` through the sphere of radius `R ≥ R₀` is at most
`12π K (|c₁ − c₀| + ‖v‖R)/R²`. -/
theorem abs_flux_wedgeField_le {R₀ K : ℝ}
    (hdecay : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, R₀ ≤ ‖y‖ → ∀ k,
      |J k (wedgePoint c₀ c₁ v s y)| ≤ K / ‖y‖ ^ 4)
    {s R : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hR : 0 < R) (hRR : R₀ ≤ R) :
    |Sphere.flux (wedgeField J c₀ c₁ v s) R| ≤
      12 * π * ((|c₁ - c₀| + ‖v‖ * R) * K) / R ^ 2 := by
  have hpt : ∀ n : sphere (0 : E3) 1, ‖R ^ 2 * ∑ α, wedgeField J c₀ c₁ v s α (R • (n : E3)) *
      (n : E3) α‖ ≤ 3 * ((|c₁ - c₀| + ‖v‖ * R) * K) / R ^ 2 := fun n => by
    have hnorm : ‖R • (n : E3)‖ = R := by
      rw [norm_smul, norm_eq_of_mem_sphere n, mul_one, Real.norm_eq_abs, abs_of_pos hR]
    have hw : |wedgeSpeed c₀ c₁ v (R • (n : E3))| ≤ |c₁ - c₀| + ‖v‖ * R := by
      unfold wedgeSpeed
      calc _ ≤ |c₁ - c₀| + |inner ℝ v (R • (n : E3))| := abs_add_le _ _
        _ ≤ _ := by
          gcongr
          exact (abs_real_inner_le_norm _ _).trans (by rw [hnorm])
    have hterm (α : Fin 3) : |wedgeField J c₀ c₁ v s α (R • (n : E3)) * (n : E3) α| ≤
        (|c₁ - c₀| + ‖v‖ * R) * K / R ^ 4 := by
      have h1 := hdecay s hs (R • (n : E3)) (by rw [hnorm]; exact hRR) α.succ
      rw [hnorm] at h1
      have h2 : |(n : E3) α| ≤ 1 := by
        rw [← Real.norm_eq_abs]
        exact (PiLp.norm_apply_le (n : E3) α).trans (norm_eq_of_mem_sphere n).le
      unfold wedgeField
      calc _ ≤ (|c₁ - c₀| + ‖v‖ * R) * (K / R ^ 4) * 1 :=
            abs_mul_le_mul_of_le (abs_mul_le_mul_of_le hw h1) h2
        _ = _ := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg R)]
    calc R ^ 2 * |∑ α, wedgeField J c₀ c₁ v s α (R • (n : E3)) * (n : E3) α| ≤
        R ^ 2 * (((3 : ℕ) : ℝ) * ((|c₁ - c₀| + ‖v‖ * R) * K / R ^ 4)) :=
          mul_le_mul_of_nonneg_left (abs_sum_fin_le hterm) (sq_nonneg R)
      _ = 3 * ((|c₁ - c₀| + ‖v‖ * R) * K) / R ^ 2 := by
        push_cast
        field_simp
  have h := norm_integral_le_of_norm_le_const (μ := Sphere.sphereMeasure)
    (Eventually.of_forall hpt)
  rw [Sphere.sphereMeasure_real_univ] at h
  rw [Sphere.flux, ← Real.norm_eq_abs]
  calc _ ≤ 3 * ((|c₁ - c₀| + ‖v‖ * R) * K) / R ^ 2 * (4 * π) := h
    _ = 12 * π * ((|c₁ - c₀| + ‖v‖ * R) * K) / R ^ 2 := by ring

/-- **The cut-off fluxes through the slice and through the tilted hyperplane differ by the side of
the wedge**: for a current that is conserved and of class `C¹` on an open set containing the
wedge, with `|J^k| ≤ K/‖y‖⁴` on the wedge beyond `R₀`,
`|∫_{‖y‖<R} (J⁰ − Σ v_α J^α)(c₁ + ⟪v, y⟫, y) dy − ∫_{‖y‖<R} J⁰(c₀, y) dy| ≤
12π K (|c₁ − c₀| + ‖v‖R)/R²` for `R ≥ R₀`. -/
theorem abs_graphFluxBall_sub_le (hO : IsOpen O) (hJ : ∀ k, ContDiffOn ℝ 1 (J k) O)
    (hdiv : ∀ z ∈ O, ∑ k, fderiv ℝ (J k) z (Pi.single k 1) = 0)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ O) {R₀ K : ℝ}
    (hdecay : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, R₀ ≤ ‖y‖ → ∀ k,
      |J k (wedgePoint c₀ c₁ v s y)| ≤ K / ‖y‖ ^ 4)
    {R : ℝ} (hR : 0 < R) (hRR : R₀ ≤ R) :
    |graphFluxBall J c₁ v R - ∫ y in ball (0 : E3) R, J 0 (vector c₀ y)| ≤
      12 * π * ((|c₁ - c₀| + ‖v‖ * R) * K) / R ^ 2 := by
  have h := abs_integral_ball_wedge_sub_le hO hJ hdiv hW hR.le
    (fun s hs => abs_flux_wedgeField_le hdecay hs hR hRR)
  simpa only [wedgeIntegrand_one, wedgeIntegrand_zero, graphFluxBall] using h

/-- The integrals over the balls of an integrable function converge to its integral. -/
theorem tendsto_integral_ball {f : E3 → ℝ} (hf : Integrable f) :
    Tendsto (fun R => ∫ y in ball (0 : E3) R, f y) atTop (𝓝 (∫ y, f y)) := by
  have heq : (fun R => ∫ x, (ball (0 : E3) R).indicator f x) =
      fun R => ∫ y in ball (0 : E3) R, f y :=
    funext fun R => integral_indicator measurableSet_ball
  rw [← heq]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖) ?_ ?_ hf.norm ?_
  · exact Eventually.of_forall fun R => hf.aestronglyMeasurable.indicator measurableSet_ball
  · exact Eventually.of_forall fun R => Eventually.of_forall fun x =>
      norm_indicator_le_norm_self _ _
  · refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ‖x‖] with R hR
    rw [indicator_of_mem (mem_ball_zero_iff.mpr hR)]

/-- **The flux of a conserved current through a tilted hyperplane is its integral over the
slice**: if `J` is conserved and of class `C¹` on an open set that contains the wedge between the
slice `x⁰ = c₀` and the hyperplane `x⁰ = c₁ + ⟪v, x⟫`, and `|J^k| ≤ K/‖y‖⁴` uniformly on the
wedge beyond a radius `R₀`, then `∫ J⁰(c₀, y) dy = ∫ (J⁰ − Σ_α v_α J^α)(c₁ + ⟪v, y⟫, y) dy`. -/
theorem integral_eq_graphFlux (hO : IsOpen O) (hJ : ∀ k, ContDiffOn ℝ 1 (J k) O)
    (hdiv : ∀ z ∈ O, ∑ k, fderiv ℝ (J k) z (Pi.single k 1) = 0)
    (hW : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, wedgePoint c₀ c₁ v s y ∈ O) {R₀ K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y : E3, R₀ ≤ ‖y‖ → ∀ k,
      |J k (wedgePoint c₀ c₁ v s y)| ≤ K / ‖y‖ ^ 4)
    (h₀ : Integrable fun y : E3 => J 0 (vector c₀ y)) (h₁ : Integrable (graphIntegrand J c₁ v)) :
    ∫ y, J 0 (vector c₀ y) = graphFlux J c₁ v := by
  have hD : Tendsto (fun R => graphFluxBall J c₁ v R -
      ∫ y in ball (0 : E3) R, J 0 (vector c₀ y)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun R : ℝ => 12 * π * ((|c₁ - c₀| + ‖v‖) * K) / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop (max R₀ 1)] with R hR
    have hR1 : 1 ≤ R := le_of_max_le_right hR
    have hRpos : 0 < R := by linarith
    rw [Real.norm_eq_abs]
    refine (abs_graphFluxBall_sub_le hO hJ hdiv hW hdecay hRpos (le_of_max_le_left hR)).trans ?_
    rw [div_le_div_iff₀ (by positivity) hRpos]
    have h0 : 0 ≤ (12 * π * K * R) * (|c₁ - c₀| * (R - 1)) :=
      mul_nonneg (by positivity) (mul_nonneg (abs_nonneg _) (by linarith))
    nlinarith [h0]
  have h := tendsto_nhds_unique ((tendsto_integral_ball h₁).sub (tendsto_integral_ball h₀)) hD
  unfold graphFlux
  linarith

end ProjectAinos.SmoothGeometry.Hyperplane
