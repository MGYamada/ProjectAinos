/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Diffraction.GreenField
import Mathlib.Tactic

/-!
# Diffraction: a radiating solution is represented by its values on a plane

For a function `u` of class `C²` on `z > 0` that solves the Helmholtz equation there and satisfies
the radiation condition `IsRadiating k u`, a point `y` with `y_z > 0` and `0 < ε < y_z/2`,
`eq_integral_spacePoint` is the Rayleigh–Sommerfeld representation from the plane `z = ε`:
`u(y) = ∫ u(x, ε) K_k(y − (x, ε)) dx`.

The proof applies the divergence theorem on the half-space `z ≥ ε`
(`integral_divergence_halfSpace`) to Green's field `W = u ∇G − G ∇u` of the Dirichlet Green
function `G = G_k(· − y) − G_k(· − y′)` (`greenField`), multiplied by two smooth radial cutoffs:
`poleCutoff`, which vanishes near the pole, and `farCutoff R`, which vanishes far out (the field
`cutField`). Since `div W = 0`, the divergence is the sum of the two source terms:

* `integral_poleSource`: the source of the cutoff about the pole integrates to `−u(y)`, by the
  divergence theorem on a ball about the pole and the flux of `W` (`fluxC_greenField_eq`);
* `tendsto_integral_farSource`: the source of the cutoff at infinity tends to `0` as `R → ∞`, by
  the far-field bound `norm_sum_mul_greenField_le` on the shell `R ≤ |p| ≤ 2R`;
* `cutField_two_spacePoint`: on the plane `G = 0`, so only `u ∂_z G = u K_k` survives
  (`greenD_spacePoint`, `greenGrad_two_spacePoint`), and `integrable_boundaryIntegrand` with
  dominated convergence takes `R → ∞` in the boundary integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology ContDiff Laplacian InnerProductSpace Real

namespace ProjectAinos.Electrodynamics.Diffraction

open ProjectAinos.SmoothGeometry.Sphere

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Points of space -/

/-- The point at the height `z` depends continuously on the foot and the height. -/
theorem continuous_spacePoint : Continuous fun p : E2 × ℝ => spacePoint p.1 p.2 := by
  unfold spacePoint
  fun_prop

/-- `|x| ≤ |(x, z)|`. -/
theorem norm_le_norm_spacePoint (x : E2) (z : ℝ) : ‖x‖ ≤ ‖spacePoint x z‖ := by
  have h : ‖x‖ ^ 2 ≤ ‖spacePoint x z‖ ^ 2 := by
    rw [norm_sq_spacePoint]
    nlinarith [sq_nonneg z]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-! ### The cutoffs -/

/-- The cutoff `s(|p − y|²/δ² − 1)` about the pole: `0` for `|p − y| ≤ δ`, `1` for
`|p − y| ≥ √2 δ`. -/
def poleCutoff (y : E3) (δ : ℝ) : E3 → ℝ := radialCutoff y (1 / δ ^ 2) (-1)

/-- The cutoff `s(2 − |p|²/R²)` at infinity: `1` for `|p| ≤ R`, `0` for `|p| ≥ √2 R`. -/
def farCutoff (R : ℝ) : E3 → ℝ := radialCutoff 0 (-1 / R ^ 2) 2

theorem poleCutoff_eq_zero {y p : E3} {δ : ℝ} (hδ : 0 < δ) (h : ‖p - y‖ ≤ δ) :
    poleCutoff y δ p = 0 := by
  refine radialCutoff_eq_zero ?_
  have h2 : ‖p - y‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [div_mul_eq_mul_div, one_mul, div_add' _ _ _ (by positivity), div_nonpos_iff]
  right
  constructor <;> nlinarith

theorem poleCutoff_eq_one {y p : E3} {δ : ℝ} (hδ : 0 < δ) (h : 2 * δ ≤ ‖p - y‖) :
    poleCutoff y δ p = 1 := by
  refine radialCutoff_eq_one ?_
  have h2 : (2 * δ) ^ 2 ≤ ‖p - y‖ ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  rw [div_mul_eq_mul_div, one_mul, le_add_neg_iff_add_le, le_div_iff₀ (by positivity)]
  nlinarith

theorem fderiv_poleCutoff_eq_zero {y p : E3} {δ : ℝ} (hδ : 0 < δ)
    (h : ‖p - y‖ < δ ∨ 2 * δ ≤ ‖p - y‖) : fderiv ℝ (poleCutoff y δ) p = 0 := by
  refine fderiv_radialCutoff_eq_zero ?_
  rw [div_mul_eq_mul_div, one_mul]
  rcases h with h | h
  · left
    have h2 : ‖p - y‖ ^ 2 < δ ^ 2 := pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
    rw [add_neg_lt_iff_lt_add, zero_add, div_lt_one (by positivity)]
    exact h2
  · right
    have h2 : (2 * δ) ^ 2 ≤ ‖p - y‖ ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    rw [lt_add_neg_iff_add_lt, lt_div_iff₀ (by positivity)]
    nlinarith

theorem farCutoff_mem_Icc (R : ℝ) (p : E3) : farCutoff R p ∈ Icc 0 1 :=
  radialCutoff_mem_Icc _ _ _ _

theorem farCutoff_eq_one {p : E3} {R : ℝ} (hR : 0 < R) (h : ‖p‖ ≤ R) : farCutoff R p = 1 := by
  refine radialCutoff_eq_one ?_
  have h2 : ‖p‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [sub_zero, div_mul_eq_mul_div, neg_one_mul, neg_div, ← sub_eq_neg_add, le_sub_comm,
    div_le_iff₀ (by positivity)]
  nlinarith

theorem farCutoff_eq_zero {p : E3} {R : ℝ} (hR : 0 < R) (h : 2 * R ≤ ‖p‖) :
    farCutoff R p = 0 := by
  refine radialCutoff_eq_zero ?_
  have h2 : (2 * R) ^ 2 ≤ ‖p‖ ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  rw [sub_zero, div_mul_eq_mul_div, neg_one_mul, neg_div, ← sub_eq_neg_add, sub_nonpos,
    le_div_iff₀ (by positivity)]
  nlinarith

theorem fderiv_farCutoff_eq_zero {p : E3} {R : ℝ} (hR : 0 < R) (h : ‖p‖ < R ∨ 2 * R < ‖p‖) :
    fderiv ℝ (farCutoff R) p = 0 := by
  refine fderiv_radialCutoff_eq_zero ?_
  rw [sub_zero, div_mul_eq_mul_div, neg_one_mul, neg_div, ← sub_eq_neg_add]
  rcases h with h | h
  · right
    have h2 : ‖p‖ ^ 2 < R ^ 2 := pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
    rw [lt_sub_comm, div_lt_iff₀ (by positivity)]
    nlinarith
  · left
    have h2 : (2 * R) ^ 2 < ‖p‖ ^ 2 := pow_lt_pow_left₀ h (by positivity) two_ne_zero
    rw [sub_neg, lt_div_iff₀ (by positivity)]
    nlinarith

/-- The derivative of the cutoff at infinity along `v` is `s′(·)(−2/R²)⟨p, v⟩`. -/
theorem fderiv_farCutoff_apply (R : ℝ) (p v : E3) :
    fderiv ℝ (farCutoff R) p v =
      deriv Real.smoothTransition (-1 / R ^ 2 * ‖p‖ ^ 2 + 2) * (-2 / R ^ 2) * ⟪p, v⟫_ℝ := by
  unfold farCutoff
  rw [fderiv_radialCutoff_apply, sub_zero]
  ring

/-! ### The geometry of the configuration -/

section Geometry

variable {y : E3} {ε : ℝ}

/-- A coordinate of a point of the ball of radius `r` about `y` differs from that of `y` by at
most `r`. -/
theorem apply_two_ge_of_norm_le {x : E3} {r : ℝ} (hx : ‖x‖ ≤ r) : y 2 - r ≤ (y + x) 2 := by
  have := abs_apply_le_norm x 2
  have := neg_abs_le (x 2)
  simp only [PiLp.add_apply]
  linarith

/-- The distance to the pole is at least the difference of the heights. -/
theorem sub_apply_two_le_norm (p : E3) : y 2 - p 2 ≤ ‖p - y‖ := by
  have h := abs_apply_le_norm (p - y) 2
  simp only [PiLp.sub_apply] at h
  have := neg_abs_le (p 2 - y 2)
  linarith

/-- A point above `ε/2` is not the image of the pole, when `2ε < y_z`. -/
theorem ne_imagePoint_of_lt {p : E3} (hεy : 2 * ε < y 2) (hε : 0 < ε) (hp : ε / 2 < p 2) :
    p ≠ imagePoint ε y :=
  ne_imagePoint (by linarith)

end Geometry

/-! ### Green's field cut off about the pole -/

/-- Green's field cut off about the pole, with the radius `δ = y_z/8`. -/
def poleField (k ε : ℝ) (y : E3) (u : E3 → ℂ) (α : Fin 3) (p : E3) : ℂ :=
  (poleCutoff y (y 2 / 8) p : ℂ) * greenField k ε y u α p

/-- The source `Σ_α ∂_α ζ W_α` of the cutoff about the pole. -/
def poleSource (k ε : ℝ) (y : E3) (u : E3 → ℂ) (p : E3) : ℂ :=
  ∑ α, (fderiv ℝ (poleCutoff y (y 2 / 8)) p (EuclideanSpace.single α 1) : ℂ) *
    greenField k ε y u α p

/-- The open half-space `z > ε/2` on which the fields are smooth. -/
def openAbove (ε : ℝ) : Set E3 := {p | ε / 2 < p 2}

theorem isOpen_openAbove (ε : ℝ) : IsOpen (openAbove ε) :=
  isOpen_lt continuous_const (by fun_prop)

section PoleField

variable {k ε : ℝ} {y : E3} {u : E3 → ℂ}

/-- Near the pole the cut-off field vanishes. -/
theorem poleField_eventuallyEq_zero (hy : 0 < y 2) (α : Fin 3) {p : E3}
    (hp : ‖p - y‖ < y 2 / 8) : poleField k ε y u α =ᶠ[𝓝 p] fun _ => 0 := by
  have hδ : 0 < y 2 / 8 := by positivity
  have hopen : IsOpen {q : E3 | ‖q - y‖ < y 2 / 8} :=
    isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
  filter_upwards [hopen.mem_nhds hp] with q hq
  simp [poleField, poleCutoff_eq_zero hδ (le_of_lt hq)]

/-- **The cut-off field is of class `C¹`** on `z > ε/2`. -/
theorem contDiffOn_poleField (hu : ContDiffOn ℝ 2 u upperHalfSpace) (hy : 0 < y 2)
    (hε : 0 < ε) (hεy : 2 * ε < y 2) (α : Fin 3) :
    ContDiffOn ℝ 1 (poleField k ε y u α) (openAbove ε) := by
  intro p hp
  have hp2 : ε / 2 < p 2 := hp
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hpy : ‖p - y‖ < y 2 / 8
  · exact contDiffAt_const.congr_of_eventuallyEq (poleField_eventuallyEq_zero hy α hpy)
  · have h1 : p ≠ y := by
      intro h
      rw [h, sub_self, norm_zero] at hpy
      exact hpy (by positivity)
    have h2 : p ≠ imagePoint ε y := ne_imagePoint_of_lt hεy hε hp2
    have hpH : 0 < p 2 := by linarith
    have hu2 : ContDiffAt ℝ 2 u p := hu.contDiffAt (isOpen_upperHalfSpace.mem_nhds hpH)
    exact contDiffAt_ofReal_mul (contDiff_radialCutoff _ _ _).contDiffAt
      (contDiffAt_greenField k ε α hu2 h1 h2)

/-- The source of the pole cutoff vanishes off the shell `δ ≤ |p − y| < 2δ`. -/
theorem poleSource_eq_zero (hy : 0 < y 2) {p : E3}
    (h : ‖p - y‖ < y 2 / 8 ∨ 2 * (y 2 / 8) ≤ ‖p - y‖) : poleSource k ε y u p = 0 := by
  simp [poleSource, fderiv_poleCutoff_eq_zero (by positivity : (0 : ℝ) < y 2 / 8) h]

/-- **The divergence of the cut-off field is the source of the cutoff**, since Green's field is
free of divergence. -/
theorem divergenceC_poleField (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) (hy : 0 < y 2) (hε : 0 < ε)
    (hεy : 2 * ε < y 2) {p : E3} (hp : p ∈ openAbove ε) :
    divergenceC (poleField k ε y u) p = poleSource k ε y u p := by
  have hp2 : ε / 2 < p 2 := hp
  by_cases hpy : ‖p - y‖ < y 2 / 8
  · rw [poleSource_eq_zero hy (Or.inl hpy)]
    unfold divergenceC
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [(poleField_eventuallyEq_zero hy α hpy).fderiv_eq]
    simp
  · have h1 : p ≠ y := by
      intro h
      rw [h, sub_self, norm_zero] at hpy
      exact hpy (by positivity)
    have h2 : p ≠ imagePoint ε y := ne_imagePoint_of_lt hεy hε hp2
    have hpH : 0 < p 2 := by linarith
    have hu2 : ContDiffAt ℝ 2 u p := hu.contDiffAt (isOpen_upperHalfSpace.mem_nhds hpH)
    have hζ : DifferentiableAt ℝ (poleCutoff y (y 2 / 8)) p :=
      ((contDiff_radialCutoff (n := 1) _ _ _).differentiable (by norm_num)) p
    have hW (α : Fin 3) : DifferentiableAt ℝ (greenField k ε y u α) p :=
      (contDiffAt_greenField k ε α hu2 h1 h2).differentiableAt one_ne_zero
    have hdiv := divergenceC_greenField k ε hu2 (hH p hpH) h1 h2
    unfold divergenceC at hdiv ⊢
    have hpf (α : Fin 3) : poleField k ε y u α =
        fun q => (poleCutoff y (y 2 / 8) q : ℂ) * greenField k ε y u α q := rfl
    simp only [hpf, fderiv_ofReal_mul_apply hζ (hW _), Finset.sum_add_distrib,
      ← Finset.mul_sum, hdiv, mul_zero, zero_add]
    rfl

/-- The cut-off field equals Green's field on the sphere of radius `2δ` about the pole. -/
theorem fluxC_poleField (hy : 0 < y 2) :
    fluxC (poleField k ε y u) y (2 * (y 2 / 8)) = fluxC (greenField k ε y u) y (2 * (y 2 / 8)) := by
  unfold fluxC
  refine integral_congr_ae (Eventually.of_forall fun n => ?_)
  have hn : ‖(n : E3)‖ = 1 := norm_eq_of_mem_sphere n
  have h1 : poleCutoff y (y 2 / 8) (y + (2 * (y 2 / 8)) • (n : E3)) = 1 := by
    refine poleCutoff_eq_one (by positivity) (le_of_eq ?_)
    rw [add_sub_cancel_left, norm_smul, hn, mul_one, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  simp only [poleField, h1, ofReal_one, one_mul]

/-- **The source of the pole cutoff integrates to `−u(y)`**: it is the divergence of the cut-off
field on the ball of radius `2δ` about the pole, whose flux is that of Green's field. -/
theorem integral_poleSource (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) (hy : 0 < y 2) (hε : 0 < ε)
    (hεy : 2 * ε < y 2) :
    ∫ p in {p : E3 | ε ≤ p 2}, poleSource k ε y u p = -u y := by
  set δ := y 2 / 8 with hδdef
  have hδ : 0 < δ := by positivity
  -- the source lives in the ball of radius `2δ` about the pole
  have hout : ∀ p : E3, p ∉ {p : E3 | ε ≤ p 2} → poleSource k ε y u p = 0 := by
    intro p hp
    simp only [mem_ofPred_eq, not_le] at hp
    refine poleSource_eq_zero hy (Or.inr ?_)
    have := sub_apply_two_le_norm (y := y) p
    linarith
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout,
    ← integral_add_left_eq_self (poleSource k ε y u) y]
  have hshell : ∀ x : E3, x ∉ shell 0 (2 * δ) → poleSource k ε y u (y + x) = 0 := by
    intro x hx
    simp only [shell, mem_ofPred_eq, not_and_or, not_lt] at hx
    refine poleSource_eq_zero hy ?_
    rw [add_sub_cancel_left]
    rcases hx with hx | hx
    · left
      have : ‖x‖ = 0 := le_antisymm hx (norm_nonneg _)
      rw [this]
      exact hδ
    · exact Or.inr hx
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hshell]
  have hball : ∀ x : E3, ‖x‖ ≤ 2 * δ → y + x ∈ openAbove ε := fun x hx => by
    have := apply_two_ge_of_norm_le (y := y) hx
    show ε / 2 < (y + x) 2
    linarith
  have hdiv : ∫ x in shell 0 (2 * δ), poleSource k ε y u (y + x) =
      ∫ x in shell 0 (2 * δ), divergenceC (poleField k ε y u) (y + x) := by
    refine setIntegral_congr_fun (measurableSet_shell 0 (2 * δ)) fun x hx => ?_
    exact (divergenceC_poleField hu hH hy hε hεy (hball x hx.2.le)).symm
  have hflux := fluxC_sub_fluxC (isOpen_openAbove ε) (contDiffOn_poleField (k := k) hu hy hε hεy)
    (c := y) le_rfl (by positivity : (0 : ℝ) ≤ 2 * δ) fun x _ hx => hball x hx
  rw [hdiv, ← hflux, fluxC_zero, sub_zero, fluxC_poleField hy]
  refine fluxC_greenField_eq k ε hu hH hy (by linarith) (by positivity) fun x hx => ?_
  have h2 := apply_two_ge_of_norm_le (y := y) hx
  refine ⟨by linarith, ne_imagePoint ?_⟩
  linarith

end PoleField

/-! ### The field cut off about the pole and at infinity -/

/-- Green's field cut off about the pole and outside the ball of radius `√2 R`. -/
def cutField (k ε : ℝ) (y : E3) (u : E3 → ℂ) (R : ℝ) (α : Fin 3) (p : E3) : ℂ :=
  (farCutoff R p : ℂ) * poleField k ε y u α p

/-- The source `Σ_α ∂_α η W_α` of the cutoff at infinity. -/
def farSource (k ε : ℝ) (y : E3) (u : E3 → ℂ) (R : ℝ) (p : E3) : ℂ :=
  ∑ α, (fderiv ℝ (farCutoff R) p (EuclideanSpace.single α 1) : ℂ) * greenField k ε y u α p

/-- The divergence of a field of class `C¹` on an open set is continuous there. -/
theorem continuousOn_divergenceC {V : Fin 3 → E3 → ℂ} {O : Set E3} (hO : IsOpen O)
    (hV : ∀ α, ContDiffOn ℝ 1 (V α) O) : ContinuousOn (divergenceC V) O :=
  continuousOn_finsetSum _ fun α _ =>
    ((hV α).continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const

section CutField

variable {k ε : ℝ} {y : E3} {u : E3 → ℂ}

theorem contDiffOn_cutField (hu : ContDiffOn ℝ 2 u upperHalfSpace) (hy : 0 < y 2)
    (hε : 0 < ε) (hεy : 2 * ε < y 2) (R : ℝ) (α : Fin 3) :
    ContDiffOn ℝ 1 (cutField k ε y u R α) (openAbove ε) := fun _ hp =>
  (contDiffAt_ofReal_mul (contDiff_radialCutoff _ _ _).contDiffAt
    ((contDiffOn_poleField hu hy hε hεy α).contDiffAt
      ((isOpen_openAbove ε).mem_nhds hp))).contDiffWithinAt

theorem cutField_eq_zero {R : ℝ} (hR : 0 < R) (α : Fin 3) {p : E3} (h : 2 * R < ‖p‖) :
    cutField k ε y u R α p = 0 := by
  simp [cutField, farCutoff_eq_zero hR h.le]

theorem farSource_eq_zero {R : ℝ} (hR : 0 < R) {p : E3} (h : ‖p‖ < R ∨ 2 * R < ‖p‖) :
    farSource k ε y u R p = 0 := by
  simp [farSource, fderiv_farCutoff_eq_zero hR h]

/-- **The divergence of the doubly cut-off field** is the sum of the two sources, for
`R > |y| + 2δ`. -/
theorem divergenceC_cutField (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) (hy : 0 < y 2) (hε : 0 < ε)
    (hεy : 2 * ε < y 2) {R : ℝ} (hR : ‖y‖ + 2 * (y 2 / 8) < R) {p : E3}
    (hp : p ∈ openAbove ε) :
    divergenceC (cutField k ε y u R) p = poleSource k ε y u p + farSource k ε y u R p := by
  have hR0 : 0 < R := lt_of_le_of_lt (by positivity) hR
  have hη : DifferentiableAt ℝ (farCutoff R) p :=
    ((contDiff_radialCutoff (n := 1) _ _ _).differentiable (by norm_num)) p
  have hZ (α : Fin 3) : DifferentiableAt ℝ (poleField k ε y u α) p :=
    ((contDiffOn_poleField hu hy hε hεy α).contDiffAt
      ((isOpen_openAbove ε).mem_nhds hp)).differentiableAt one_ne_zero
  have hcf (α : Fin 3) : cutField k ε y u R α =
      fun q => (farCutoff R q : ℂ) * poleField k ε y u α q := rfl
  have hdivZ := divergenceC_poleField hu hH hy hε hεy hp
  unfold divergenceC at hdivZ ⊢
  simp only [hcf, fderiv_ofReal_mul_apply hη (hZ _), Finset.sum_add_distrib, ← Finset.mul_sum,
    hdivZ]
  congr 1
  · by_cases hps : poleSource k ε y u p = 0
    · rw [hps, mul_zero]
    · have hlt : ‖p - y‖ < 2 * (y 2 / 8) := by
        by_contra hcon
        exact hps (poleSource_eq_zero hy (Or.inr (not_lt.mp hcon)))
      have hpR : ‖p‖ ≤ R := by
        have := norm_le_norm_add_norm_sub' p y
        have := norm_sub_rev p y
        linarith [norm_le_insert' p y]
      rw [farCutoff_eq_one hR0 hpR, ofReal_one, one_mul]
  · refine Finset.sum_congr rfl fun α _ => ?_
    by_cases hpR : ‖p‖ < R
    · simp [fderiv_farCutoff_eq_zero hR0 (Or.inl hpR)]
    · have h2 : 2 * (y 2 / 8) ≤ ‖p - y‖ := by
        have := norm_sub_norm_le p y
        linarith [not_lt.mp hpR]
      simp only [poleField, poleCutoff_eq_one (by positivity) h2, ofReal_one, one_mul]

/-- The divergence of the doubly cut-off field is integrable on the half-space `z ≥ ε`. -/
theorem integrableOn_divergenceC_cutField (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hy : 0 < y 2) (hε : 0 < ε) (hεy : 2 * ε < y 2) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (divergenceC (cutField k ε y u R)) {p : E3 | ε ≤ p 2} := by
  refine integrableOn_of_continuousOn_of_eq_zero (isClosed_le continuous_const (by fun_prop))
    (fun p hp => show ε / 2 < p 2 by have : ε ≤ p 2 := hp; linarith)
    (continuousOn_divergenceC (isOpen_openAbove ε) (contDiffOn_cutField hu hy hε hεy R))
    (L := 2 * R) fun p hp => ?_
  unfold divergenceC
  refine Finset.sum_eq_zero fun α _ => ?_
  rw [fderiv_eq_zero_of_lt_norm (fun q hq => cutField_eq_zero hR α hq) hp]
  rfl

/-- The source of the pole cutoff is integrable on the half-space `z ≥ ε`. -/
theorem integrableOn_poleSource (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) (hy : 0 < y 2) (hε : 0 < ε)
    (hεy : 2 * ε < y 2) :
    IntegrableOn (poleSource k ε y u) {p : E3 | ε ≤ p 2} := by
  have hc : ContinuousOn (poleSource k ε y u) (openAbove ε) :=
    (continuousOn_divergenceC (isOpen_openAbove ε) (contDiffOn_poleField hu hy hε hεy)).congr
      fun p hp => (divergenceC_poleField hu hH hy hε hεy hp).symm
  refine integrableOn_of_continuousOn_of_eq_zero (isClosed_le continuous_const (by fun_prop))
    (fun p hp => show ε / 2 < p 2 by have : ε ≤ p 2 := hp; linarith) hc
    (L := ‖y‖ + 2 * (y 2 / 8)) fun p hp => poleSource_eq_zero hy (Or.inr ?_)
  have := norm_sub_norm_le p y
  linarith

/-- The source of the cutoff at infinity is `s′(·)(−2/R²) Σ_α p_α W_α`, so
`|farSource| ≤ S (2/R²) |Σ_α p_α W_α|` for a bound `S` of `|s′|`. -/
theorem norm_farSource_le {R : ℝ} (hR : 0 < R) {S : ℝ}
    (hS : ∀ t, |deriv Real.smoothTransition t| ≤ S) (p : E3) :
    ‖farSource k ε y u R p‖ ≤
      S * (2 / R ^ 2) * ‖∑ α, ((p α : ℝ) : ℂ) * greenField k ε y u α p‖ := by
  set t := -1 / R ^ 2 * ‖p‖ ^ 2 + 2 with ht
  have h : farSource k ε y u R p =
      ((deriv Real.smoothTransition t * (-2 / R ^ 2) : ℝ) : ℂ) *
        ∑ α, ((p α : ℝ) : ℂ) * greenField k ε y u α p := by
    unfold farSource
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [fderiv_farCutoff_apply, EuclideanSpace.inner_single_right, ← ht]
    simp only [conj_trivial, one_mul]
    push_cast
    ring
  have hc : |(-2 / R ^ 2 : ℝ)| = 2 / R ^ 2 := by
    rw [abs_div, abs_neg, abs_two, abs_of_pos (by positivity)]
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, hc]
  gcongr
  exact hS _

/-- The volume of a closed ball of `ℝ³` is `r³` times that of the unit ball. -/
theorem volume_real_closedBall (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure E3).real (closedBall 0 r) =
      r ^ 3 * (volume : Measure E3).real (ball 0 1) := by
  rw [Measure.real, Measure.addHaar_closedBall _ _ hr, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rfl

/-- **The source of the cutoff at infinity integrates to `0` as `R → ∞`**: on the shell
`R ≤ |p| ≤ 2R` it is `O(R⁻²)` times the far-field bound `O(R⁻²) + o(R⁻¹)`, over a volume
`O(R³)`. -/
theorem tendsto_integral_farSource (hrad : IsRadiating k u) (hε : 0 < ε) :
    Tendsto (fun R => ∫ p in {p : E3 | ε ≤ p 2}, farSource k ε y u R p) atTop (𝓝 0) := by
  obtain ⟨S, hS0, hS⟩ := exists_abs_deriv_smoothTransition_le
  obtain ⟨⟨C, R₀, hC⟩, hrad2⟩ := hrad
  set C' := max C 0 with hC'def
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hC' : ∀ p : E3, 0 < p 2 → R₀ ≤ ‖p‖ → ‖p‖ * ‖u p‖ ≤ C' := fun p hp hpR =>
    (hC p hp hpR).trans (le_max_left _ _)
  set a := ‖y‖ + ‖imagePoint ε y‖ with hadef
  set V₁ := (volume : Measure E3).real (ball 0 1) with hV₁def
  have hV₁ : 0 ≤ V₁ := measureReal_nonneg
  set K := 16 * S * V₁ + 1 with hKdef
  have hK : 0 < K := by positivity
  set B := 2 * C' * (|k| * a + 1) with hBdef
  have hB : 0 ≤ B := by positivity
  rw [Metric.tendsto_atTop]
  intro e0 he0
  set e := e0 * π / (4 * K) with hedef
  have he : 0 < e := by positivity
  obtain ⟨R₁, hR₁⟩ := hrad2 e he
  set N := max (max R₀ R₁) (max (2 * a) (max 1 (8 * K * B / (π * e0) + 1))) with hNdef
  refine ⟨N, fun R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) hR)
  have hR0 : 0 < R := by linarith
  have hRR₀ : R₀ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRR₁ : R₁ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hRa : 2 * a ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hRB : 8 * K * B / (π * e0) + 1 ≤ R :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hR
  rw [dist_zero_right]
  set M := S * (2 / R ^ 2) * (B / (π * R ^ 2) + e / (π * R)) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hpt : ∀ p ∈ {p : E3 | ε ≤ p 2}, ‖farSource k ε y u R p‖ ≤ M := by
    intro p hp
    have hp2 : ε ≤ p 2 := hp
    by_cases hpR : ‖p‖ < R ∨ 2 * R < ‖p‖
    · rw [farSource_eq_zero hR0 hpR, norm_zero]
      exact hM0
    · rw [not_or, not_lt, not_lt] at hpR
      obtain ⟨h1, -⟩ := hpR
      have hp0 : 0 < p 2 := by linarith
      have hpn : 0 < ‖p‖ := by linarith
      have hfar := norm_sum_mul_greenField_le (k := k) (ε := ε) (y := y) (u := u) (a := a)
        (C := C') (e := e) (le_add_of_nonneg_right (norm_nonneg _))
        (le_add_of_nonneg_left (norm_nonneg _)) (hRa.trans h1) hpn (hC' p hp0 (hRR₀.trans h1))
        (hR₁ p hp0 (hRR₁.trans h1))
      calc ‖farSource k ε y u R p‖
          ≤ S * (2 / R ^ 2) * ‖∑ α, ((p α : ℝ) : ℂ) * greenField k ε y u α p‖ :=
            norm_farSource_le hR0 hS p
        _ ≤ S * (2 / R ^ 2) * (B / (π * ‖p‖ ^ 2) + e / (π * ‖p‖)) := by
            gcongr
        _ ≤ M := by
            rw [hMdef]
            gcongr
  have hmeas : MeasurableSet {p : E3 | ε ≤ p 2} :=
    measurableSet_le measurable_const (by fun_prop)
  have hzero : ∀ p ∈ {p : E3 | ε ≤ p 2} \ ({p : E3 | ε ≤ p 2} ∩ closedBall 0 (2 * R)),
      farSource k ε y u R p = 0 := by
    intro p hp
    refine farSource_eq_zero hR0 (Or.inr ?_)
    have h := hp.2
    simp only [mem_inter_iff, hp.1, true_and, mem_closedBall, dist_zero_right, not_le] at h
    exact h
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas inter_subset_left hzero]
  have hfin : volume ({p : E3 | ε ≤ p 2} ∩ closedBall 0 (2 * R)) < ⊤ :=
    (measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top
  calc ‖∫ p in {p : E3 | ε ≤ p 2} ∩ closedBall 0 (2 * R), farSource k ε y u R p‖
      ≤ M * (volume : Measure E3).real ({p : E3 | ε ≤ p 2} ∩ closedBall 0 (2 * R)) :=
        norm_setIntegral_le_of_norm_le_const hfin fun p hp => hpt p hp.1
    _ ≤ M * (volume : Measure E3).real (closedBall 0 (2 * R)) := by
        gcongr
        · exact measure_closedBall_lt_top.ne
        · exact inter_subset_right
    _ = 16 * S * V₁ * (B / (π * R) + e / π) := by
        rw [volume_real_closedBall _ (by positivity), hMdef]
        field_simp
        ring
    _ ≤ K * (B / (π * R) + e / π) := by
        gcongr
        linarith
    _ < e0 := by
        have h1 : K * (e / π) = e0 / 4 := by
          rw [hedef]
          field_simp
        have h2 : K * (B / (π * R)) ≤ e0 / 8 := by
          rw [show K * (B / (π * R)) = (K * B / π) / R by field_simp]
          rw [div_le_iff₀ hR0]
          have h3 : 8 * K * B / (π * e0) ≤ R := by linarith
          rw [div_le_iff₀ (by positivity)] at h3
          have : K * B / π = (8 * K * B) / 8 / π := by ring
          rw [this, div_div, div_le_iff₀ (by positivity)]
          nlinarith [Real.pi_pos]
        nlinarith

end CutField

/-! ### The boundary integral -/

/-- **On the plane `z = ε` only `u ∂_z G = u K_k` survives** in the cut-off field. -/
theorem cutField_two_spacePoint {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hy : 0 < y 2)
    (hεy : 2 * ε < y 2) (R : ℝ) (x : E2) :
    cutField k ε y u R 2 (spacePoint x ε) = (farCutoff R (spacePoint x ε) : ℂ) *
      (u (spacePoint x ε) * rayleighKernel k (y - spacePoint x ε)) := by
  have h2 : 2 * (y 2 / 8) ≤ ‖spacePoint x ε - y‖ := by
    have := sub_apply_two_le_norm (y := y) (spacePoint x ε)
    rw [spacePoint_apply_two] at this
    linarith
  simp only [cutField, poleField, poleCutoff_eq_one (by positivity) h2, ofReal_one, one_mul,
    greenField, greenD_spacePoint, greenGrad_two_spacePoint, zero_mul, sub_zero]

/-- The Rayleigh–Sommerfeld kernel from a far point of the plane `z = ε`:
`|K_k(y − (x, ε))| ≤ 2y_z(1 + |k|)/(π(1 + |x|)²)` for `|x| ≥ 2|y| + 2` and `0 ≤ ε ≤ y_z`. -/
theorem norm_rayleighKernel_sub_spacePoint_le (k : ℝ) {y : E3} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hεy : ε ≤ y 2) {x : E2} (hx : 2 * ‖y‖ + 2 ≤ ‖x‖) :
    ‖rayleighKernel k (y - spacePoint x ε)‖ ≤ 2 * y 2 * (1 + |k|) / (π * (1 + ‖x‖) ^ 2) := by
  set q := y - spacePoint x ε with hqdef
  set R := ‖q‖ with hRdef
  have hRx : (1 + ‖x‖) / 2 ≤ R := by
    have h1 := norm_sub_norm_le (spacePoint x ε) y
    have h2 := norm_le_norm_spacePoint x ε
    have h3 : ‖spacePoint x ε - y‖ = R := norm_sub_rev _ _
    linarith
  have hR1 : 1 ≤ R := by
    have := norm_nonneg y
    linarith
  have hR0 : 0 < R := by linarith
  have hq2 : q 2 = y 2 - ε := by simp [hqdef]
  have hK : ‖rayleighKernel k q‖ = (y 2 - ε) * ‖kernelProfile k R‖ := by
    rw [rayleighKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, hq2,
      abs_of_nonneg (by linarith)]
  have hψ := norm_kernelProfile_le k hR0
  have hy2 : 0 ≤ y 2 := le_trans hε0 hεy
  rw [hK]
  calc (y 2 - ε) * ‖kernelProfile k R‖ ≤ y 2 * ((1 + |k| * R) / (2 * π * R ^ 3)) := by
        gcongr
        linarith
    _ ≤ y 2 * ((1 + |k|) / (2 * π * R ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hy2
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h3 : 0 ≤ 2 * π * R ^ 2 := by positivity
        nlinarith [abs_nonneg k]
    _ ≤ y 2 * ((1 + |k|) / (2 * π * ((1 + ‖x‖) / 2) ^ 2)) := by
        gcongr
    _ = 2 * y 2 * (1 + |k|) / (π * (1 + ‖x‖) ^ 2) := by
        field_simp

/-- The function `(1 + |x|)⁻³` is integrable on the plane. -/
theorem integrable_inv_one_add_norm_pow_three :
    Integrable (fun x : E2 => ((1 + ‖x‖) ^ 3)⁻¹) := by
  have h := integrable_one_add_norm (E := E2) (μ := volume) (r := 3)
    (by rw [finrank_euclideanSpace_fin]; norm_num)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

/-- A continuous function on the plane that is `O((1 + |x|)⁻³)` far out is integrable. -/
theorem integrable_of_norm_le_inv_pow_three {f : E2 → ℂ} (hf : Continuous f) {R₂ A : ℝ}
    (hA : ∀ x : E2, R₂ ≤ ‖x‖ → ‖f x‖ ≤ A * ((1 + ‖x‖) ^ 3)⁻¹) : Integrable f := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E2) R₂).exists_bound_of_continuousOn
    hf.continuousOn
  set M' := max M 0 with hM'
  refine Integrable.mono' (integrable_inv_one_add_norm_pow_three.const_mul
    (M' * (1 + |R₂|) ^ 3 + |A|)) hf.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hinv : 0 < ((1 + ‖x‖) ^ 3)⁻¹ := by positivity
  have hM'0 : 0 ≤ M' := le_max_right _ _
  by_cases hx : ‖x‖ ≤ R₂
  · have h1 : ‖f x‖ ≤ M' := (hM x (by simpa using hx)).trans (le_max_left _ _)
    have h2 : 1 ≤ (1 + |R₂|) ^ 3 * ((1 + ‖x‖) ^ 3)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      gcongr
      exact hx.trans (le_abs_self _)
    calc ‖f x‖ ≤ M' * ((1 + |R₂|) ^ 3 * ((1 + ‖x‖) ^ 3)⁻¹) := by nlinarith
      _ ≤ (M' * (1 + |R₂|) ^ 3 + |A|) * ((1 + ‖x‖) ^ 3)⁻¹ := by
          rw [add_mul, mul_assoc]
          have := abs_nonneg A
          nlinarith
  · calc ‖f x‖ ≤ A * ((1 + ‖x‖) ^ 3)⁻¹ := hA x (le_of_lt (not_le.mp hx))
      _ ≤ |A| * ((1 + ‖x‖) ^ 3)⁻¹ := by gcongr; exact le_abs_self A
      _ ≤ (M' * (1 + |R₂|) ^ 3 + |A|) * ((1 + ‖x‖) ^ 3)⁻¹ := by
          gcongr
          have : 0 ≤ M' * (1 + |R₂|) ^ 3 := by positivity
          linarith

/-- The boundary integrand far out: if `|p||u(p)| ≤ C` for `p_z > 0`, `|p| ≥ R₀`, then
`|u(x, ε) K_k(y − (x, ε))| ≤ (4Cy_z(1 + |k|)/π)(1 + |x|)⁻³` far out, for `0 < ε ≤ y_z`. -/
theorem norm_boundaryIntegrand_le {k : ℝ} {u : E3 → ℂ} {C R₀ : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p : E3, 0 < p 2 → R₀ ≤ ‖p‖ → ‖p‖ * ‖u p‖ ≤ C) {y : E3} {ε : ℝ} (hε : 0 < ε)
    (hεy : ε ≤ y 2) {x : E2} (hx : max (max R₀ 1) (2 * ‖y‖ + 2) ≤ ‖x‖) :
    ‖u (spacePoint x ε) * rayleighKernel k (y - spacePoint x ε)‖ ≤
      4 * C * y 2 * (1 + |k|) / π * ((1 + ‖x‖) ^ 3)⁻¹ := by
  have hx0 : R₀ ≤ ‖x‖ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1 : 1 ≤ ‖x‖ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxy : 2 * ‖y‖ + 2 ≤ ‖x‖ := le_trans (le_max_right _ _) hx
  have hsp := norm_le_norm_spacePoint x ε
  have hu : ‖u (spacePoint x ε)‖ ≤ 2 * C / (1 + ‖x‖) := by
    have h := hC (spacePoint x ε) (by rw [spacePoint_apply_two]; exact hε) (hx0.trans hsp)
    rw [le_div_iff₀ (by positivity)]
    have h1 : ‖u (spacePoint x ε)‖ * ‖x‖ ≤ C := by
      calc ‖u (spacePoint x ε)‖ * ‖x‖ ≤ ‖u (spacePoint x ε)‖ * ‖spacePoint x ε‖ := by gcongr
        _ ≤ C := by linarith
    nlinarith [norm_nonneg (u (spacePoint x ε))]
  have hK := norm_rayleighKernel_sub_spacePoint_le k hε.le hεy hxy
  have hy2 : 0 ≤ y 2 := le_trans hε.le hεy
  rw [norm_mul]
  calc ‖u (spacePoint x ε)‖ * ‖rayleighKernel k (y - spacePoint x ε)‖
      ≤ 2 * C / (1 + ‖x‖) * (2 * y 2 * (1 + |k|) / (π * (1 + ‖x‖) ^ 2)) := by gcongr
    _ = 4 * C * y 2 * (1 + |k|) / π * ((1 + ‖x‖) ^ 3)⁻¹ := by
        field_simp
        ring

/-- The boundary integrand on the plane `z = ε` is continuous, for `u` continuous on `z > 0`. -/
theorem continuous_boundaryIntegrand {k : ℝ} {u : E3 → ℂ}
    (hu : ContinuousOn u upperHalfSpace) {y : E3} {ε : ℝ} (hε : 0 < ε) (hεy : ε < y 2) :
    Continuous fun x : E2 => u (spacePoint x ε) * rayleighKernel k (y - spacePoint x ε) := by
  have hsp : Continuous fun x : E2 => spacePoint x ε :=
    continuous_spacePoint.comp (by fun_prop : Continuous fun x : E2 => (x, ε))
  have hcu : Continuous fun x : E2 => u (spacePoint x ε) :=
    hu.comp_continuous hsp fun x => by
      show 0 < (spacePoint x ε) 2
      rw [spacePoint_apply_two]
      exact hε
  have hcK : Continuous fun x : E2 => rayleighKernel k (y - spacePoint x ε) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hq : y - spacePoint x ε ≠ 0 := by
      intro h
      have := congrArg (fun q : E3 => q 2) h
      simp only [PiLp.sub_apply, spacePoint_apply_two, PiLp.zero_apply] at this
      linarith
    exact ContinuousAt.comp (f := fun x : E2 => y - spacePoint x ε)
      (contDiffAt_rayleighKernel k (n := 0) hq).continuousAt
      (continuous_const.sub hsp).continuousAt
  exact hcu.mul hcK

/-- The boundary integrand on the plane `z = ε` is integrable, for a radiating `u`. -/
theorem integrable_boundaryIntegrand {k : ℝ} {u : E3 → ℂ}
    (hu : ContinuousOn u upperHalfSpace) (hrad : IsRadiating k u) {y : E3} {ε : ℝ}
    (hε : 0 < ε) (hεy : ε < y 2) :
    Integrable fun x : E2 => u (spacePoint x ε) * rayleighKernel k (y - spacePoint x ε) := by
  obtain ⟨⟨C, R₀, hC⟩, -⟩ := hrad
  have hC' : ∀ p : E3, 0 < p 2 → R₀ ≤ ‖p‖ → ‖p‖ * ‖u p‖ ≤ max C 0 := fun p hp hpR =>
    (hC p hp hpR).trans (le_max_left _ _)
  exact integrable_of_norm_le_inv_pow_three (continuous_boundaryIntegrand hu hε hεy)
    fun x hx => norm_boundaryIntegrand_le (le_max_right _ _) hC' hε hεy.le hx

/-! ### The representation -/

/-- **The representation of a radiating solution by its values on a plane**: a function of class
`C²` on `z > 0` that solves the Helmholtz equation there and satisfies the radiation condition
is, at a point `y` with `y_z > 0` and for `0 < ε < y_z/2`, the Rayleigh–Sommerfeld integral of its
values on the plane `z = ε`: `u(y) = ∫ u(x, ε) K_k(y − (x, ε)) dx`. -/
theorem eq_integral_spacePoint {k : ℝ} {u : E3 → ℂ} (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) (hrad : IsRadiating k u) {y : E3}
    (hy : 0 < y 2) {ε : ℝ} (hε : 0 < ε) (hεy : 2 * ε < y 2) :
    u y = ∫ x : E2, u (spacePoint x ε) * rayleighKernel k (y - spacePoint x ε) := by
  set g : E2 → ℂ := fun x => u (spacePoint x ε) * rayleighKernel k (y - spacePoint x ε)
    with hgdef
  set s : Set E3 := {p : E3 | ε ≤ p 2} with hsdef
  set R₀ := ‖y‖ + 2 * (y 2 / 8) + 1 with hR₀
  have hR₀pos : 0 < R₀ := by positivity
  have hεy' : ε < y 2 := by linarith
  have hg : Integrable g := integrable_boundaryIntegrand hu.continuousOn hrad hε hεy'
  -- the identity for every large `R`
  have hid : ∀ R, R₀ ≤ R → -u y + ∫ p in s, farSource k ε y u R p =
      -∫ x : E2, (farCutoff R (spacePoint x ε) : ℂ) * g x := by
    intro R hR
    have hR0 : 0 < R := lt_of_lt_of_le hR₀pos hR
    have hRy : ‖y‖ + 2 * (y 2 / 8) < R := by linarith
    have hdivT := integral_divergence_halfSpace (isOpen_openAbove ε)
      (fun p (hp : ε ≤ p 2) => show ε / 2 < p 2 by linarith)
      (contDiffOn_cutField (k := k) hu hy hε hεy R)
      (L := 2 * R) fun α p hp => cutField_eq_zero hR0 α hp
    have hbd : ∀ x : E2, cutField k ε y u R 2 !₂[x 0, x 1, ε] =
        (farCutoff R (spacePoint x ε) : ℂ) * g x := fun x =>
      cutField_two_spacePoint hy hεy R x
    simp only [hbd] at hdivT
    rw [← hdivT]
    have hmeas : MeasurableSet s := measurableSet_le measurable_const (by fun_prop)
    have hpole := integrableOn_poleSource (k := k) hu hH hy hε hεy
    have hdivI := integrableOn_divergenceC_cutField (k := k) hu hy hε hεy hR0
    have heq : ∀ p ∈ s, divergenceC (cutField k ε y u R) p =
        poleSource k ε y u p + farSource k ε y u R p := fun p hp =>
      divergenceC_cutField hu hH hy hε hεy hRy (show ε / 2 < p 2 by
        have : ε ≤ p 2 := hp
        linarith)
    have hfarI : IntegrableOn (farSource k ε y u R) s :=
      (hdivI.sub hpole).congr_fun (fun p hp => by simp only [Pi.sub_apply]; rw [heq p hp]; ring)
        hmeas
    have h1 : ∫ p in s, divergenceC (cutField k ε y u R) p =
        ∫ p in s, (poleSource k ε y u p + farSource k ε y u R p) :=
      setIntegral_congr_fun hmeas heq
    have h2 := integral_add hpole hfarI
    unfold divergenceC at h1
    rw [h1, h2, integral_poleSource hu hH hy hε hεy]
  -- the limit `R → ∞`
  have hT1 : Tendsto (fun R => -u y + ∫ p in s, farSource k ε y u R p) atTop (𝓝 (-u y)) := by
    simpa using (tendsto_const_nhds (x := -u y)).add (tendsto_integral_farSource hrad hε)
  have hT2 : Tendsto (fun R => -∫ x : E2, (farCutoff R (spacePoint x ε) : ℂ) * g x) atTop
      (𝓝 (-∫ x, g x)) := by
    refine Tendsto.neg ?_
    have hcg : Continuous g := continuous_boundaryIntegrand hu.continuousOn hε hεy'
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖g x‖)
      (Eventually.of_forall fun R => ?_) (Eventually.of_forall fun R => ?_) hg.norm ?_
    · exact ((Complex.continuous_ofReal.comp ((contDiff_radialCutoff (n := 0) _ _ _).continuous.comp
        (continuous_spacePoint.comp (by fun_prop : Continuous fun x : E2 => (x, ε))))).mul
        hcg).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (farCutoff_mem_Icc _ _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (farCutoff_mem_Icc _ _).2
    · refine Eventually.of_forall fun x => ?_
      have hev : ∀ᶠ R in atTop, (farCutoff R (spacePoint x ε) : ℂ) * g x = g x := by
        filter_upwards [eventually_ge_atTop (‖spacePoint x ε‖ + 1)] with R hR
        rw [farCutoff_eq_one (by linarith [norm_nonneg (spacePoint x ε)]) (by linarith),
          ofReal_one, one_mul]
      exact tendsto_const_nhds.congr' (hev.mono fun R hR => hR.symm)
  have hT1' : Tendsto (fun R => -u y + ∫ p in s, farSource k ε y u R p) atTop
      (𝓝 (-∫ x, g x)) := hT2.congr' (by
        filter_upwards [eventually_ge_atTop R₀] with R hR
        exact (hid R hR).symm)
  have := tendsto_nhds_unique hT1 hT1'
  exact neg_injective this

end ProjectAinos.Electrodynamics.Diffraction
