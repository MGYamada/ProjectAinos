/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Diffraction.Representation
import Mathlib.Tactic

/-!
# Diffraction: the aperture field is the unique radiating solution

Landau–Lifshitz, *The Classical Theory of Fields*, §59, in the half-space Dirichlet model of
`Aperture.lean`.

* `tendsto_apertureField_nhdsWithin`: **joint continuity up to the plane**, `u(p) → u₀(x)` as
  `p → (x, 0)` within `z > 0`, for continuous aperture data of compact support; with the boundary
  values the field is continuous on the closed half-space (`continuousOn_apertureFieldExt`).
* `eq_integral_spacePoint`: **the representation of a radiating solution by its values on a
  plane**. A function `u` of class `C²` on `z > 0` that solves the Helmholtz equation there and
  satisfies the radiation condition `IsRadiating` has, for `0 < ε < y_z/2`,
  `u(y) = ∫ u(x, ε) K_k(y − (x, ε)) dx` with the Rayleigh–Sommerfeld kernel `K_k`. The proof is
  Green's second identity for `u` and the Dirichlet Green function `G_k(p − y) − G_k(p − y′)` of
  the half-space `z ≥ ε` (`greenField`), by the divergence theorem on that half-space
  (`integral_divergence_halfSpace`) with two smooth cutoffs: the cutoff about the pole gives
  `−u(y)` through the flux on a sphere about the pole (`fluxC_greenField_eq`), the cutoff at
  infinity gives a term that tends to `0` by the radiation conditions of `u` and of the spherical
  waves (`norm_sum_mul_greenField_le`), and on the plane only `u ∂_z G` survives, which is the
  kernel.
* `eq_apertureField`: **a radiating solution with the boundary values `u₀` is the aperture
  field** of `u₀`: let `ε → 0⁺` in the representation, by dominated convergence. The boundary
  values are taken in the sense of limits within `z > 0` (continuity up to the plane); no
  regularity at the plane is assumed, so the plane `z = ε` is used instead of a reflection.
* `IsRadiatingDirichletSolution k u₀ u`: the predicate of the problem;
  `isRadiatingDirichletSolution_apertureField`: the aperture field solves it (existence), and
  `IsRadiatingDirichletSolution.eqOn_apertureField`, `IsRadiatingDirichletSolution.eqOn`:
  **uniqueness**, any two solutions with the same data agree on `z > 0`; `eq_zero_of_isRadiating`
  is the case of zero data. The aperture bump is an instance.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology ContDiff Laplacian InnerProductSpace Real

namespace ProjectAinos.Electrodynamics.Diffraction

open ProjectAinos.SmoothGeometry.Sphere

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Joint continuity of the aperture field up to the plane -/

/-- The foot `(p₁, p₂)` of `p` in the plane. -/
def planeCoord (p : E3) : E2 := !₂[p 0, p 1]

@[simp] theorem planeCoord_apply_zero (p : E3) : planeCoord p 0 = p 0 := by simp [planeCoord]

@[simp] theorem planeCoord_apply_one (p : E3) : planeCoord p 1 = p 1 := by simp [planeCoord]

/-- A point is the point at its height over its foot. -/
theorem spacePoint_planeCoord (p : E3) : spacePoint (planeCoord p) (p 2) = p := by
  ext i
  fin_cases i <;> simp [spacePoint, planeCoord]

/-- The foot of a point of the plane. -/
@[simp] theorem planeCoord_planePoint (x : E2) : planeCoord (planePoint x) = x := by
  ext i
  fin_cases i <;> simp [planeCoord, planePoint]

/-- The foot of a point of space. -/
@[simp] theorem planeCoord_spacePoint (x : E2) (z : ℝ) : planeCoord (spacePoint x z) = x := by
  ext i
  fin_cases i <;> simp [planeCoord, spacePoint]

/-- The point at height `0` is the point of the plane. -/
@[simp] theorem spacePoint_zero (x : E2) : spacePoint x 0 = planePoint x := by
  ext i
  fin_cases i <;> simp [spacePoint, planePoint]

/-- The foot is continuous. -/
theorem continuous_planeCoord : Continuous planeCoord := by
  unfold planeCoord
  fun_prop

/-- The foot is a contraction: `|(p₁, p₂) − x| ≤ |p − (x, 0)|`. -/
theorem norm_planeCoord_sub_le (p : E3) (x : E2) :
    ‖planeCoord p - x‖ ≤ ‖p - planePoint x‖ := by
  have h : ‖planeCoord p - x‖ ^ 2 ≤ ‖p - planePoint x‖ ^ 2 := by
    rw [norm_sq_eq_two, norm_sq_eq_three]
    simp [planeCoord, planePoint]
    positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **Joint continuity of the aperture field up to the plane**: for continuous data of compact
support, `u(p) → u₀(x)` as `p → (x, 0)` within the half-space `z > 0`. -/
theorem tendsto_apertureField_nhdsWithin (k : ℝ) {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) (x : E2) :
    Tendsto (apertureField k u₀) (𝓝[upperHalfSpace] (planePoint x)) (𝓝 (u₀ x)) := by
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  obtain ⟨a₀, ha₀⟩ := hs.isBounded.subset_closedBall 0
  set a := max a₀ 0 with ha_def
  have ha : tsupport u₀ ⊆ closedBall 0 a :=
    ha₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have ha0 : 0 ≤ a := le_max_right _ _
  set ρ : E2 → ℝ := fun v => √(‖v‖ ^ 2 + 1) with hρ
  set H : E3 → E2 → ℂ := fun p v => u₀ (planeCoord p - p 2 • v) *
      (cexp (I * k * (p 2 * ρ v)) * (1 - I * k * (p 2 * ρ v))) * (poissonKernel 1 v : ℂ)
    with hH
  have hρc : Continuous ρ := by
    simp only [hρ]
    fun_prop
  have hHc (v : E2) : Continuous fun p => H p v := by
    simp only [hH]
    have := continuous_planeCoord
    fun_prop
  have hP : Continuous (poissonKernel 1) := by
    rw [show poissonKernel 1 = fun w : E2 => (2 * π)⁻¹ * (√(‖w‖ ^ 2 + 1) ^ 3)⁻¹ from
      funext poissonKernel_one]
    have : ∀ v : E2, √(‖v‖ ^ 2 + 1) ^ 3 ≠ 0 := fun v =>
      pow_ne_zero _ (Real.sqrt_pos.mpr (by positivity)).ne'
    fun_prop (disch := exact this _)
  have hHv (p : E3) : Continuous (H p) := by
    simp only [hH]
    fun_prop
  set bound : E2 → ℝ := fun v => M * (1 + |k| * (‖x‖ + a + 2)) * poissonKernel 1 v with hb
  have hP0 (v : E2) : 0 ≤ poissonKernel 1 v := by
    rw [poissonKernel_one]
    positivity
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM x)
  have hbound : ∀ᶠ p in 𝓝[upperHalfSpace] (planePoint x),
      ∀ᵐ v ∂(volume : Measure E2), ‖H p v‖ ≤ bound v := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (ball_mem_nhds (planePoint x) one_pos)] with p hpH hpb
    refine Eventually.of_forall fun v => ?_
    have hz0 : 0 < p 2 := hpH
    have hpx : ‖p - planePoint x‖ < 1 := by rwa [mem_ball, dist_eq_norm] at hpb
    have hz1 : p 2 < 1 := by
      have := abs_apply_le_norm (p - planePoint x) 2
      simp only [PiLp.sub_apply, planePoint_apply_two, sub_zero] at this
      have := le_abs_self (p 2)
      linarith
    have hfoot : ‖planeCoord p‖ ≤ ‖x‖ + 1 := by
      have h1 := norm_planeCoord_sub_le p x
      have h2 := norm_le_norm_add_norm_sub' (planeCoord p) x
      linarith
    by_cases hv : u₀ (planeCoord p - p 2 • v) = 0
    · simp only [hH, hv, zero_mul, norm_zero, hb]
      have : 0 ≤ 1 + |k| * (‖x‖ + a + 2) := by positivity
      exact mul_nonneg (mul_nonneg hM0 this) (hP0 v)
    · have hxa : ‖planeCoord p - p 2 • v‖ ≤ a := by
        have := ha (subset_tsupport _ hv)
        simpa [dist_eq_norm] using this
      have hzv : p 2 * ‖v‖ ≤ ‖x‖ + a + 1 := by
        have h1 : ‖p 2 • v‖ ≤ ‖planeCoord p‖ + ‖planeCoord p - p 2 • v‖ := by
          calc ‖p 2 • v‖ = ‖planeCoord p - (planeCoord p - p 2 • v)‖ := by rw [sub_sub_cancel]
            _ ≤ ‖planeCoord p‖ + ‖planeCoord p - p 2 • v‖ := norm_sub_le _ _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hz0] at h1
        linarith
      have hρv : ρ v ≤ ‖v‖ + 1 := by
        simp only [hρ]
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [norm_nonneg v]
      have hθ : 0 ≤ p 2 * ρ v := by positivity
      have hθ1 : p 2 * ρ v ≤ ‖x‖ + a + 2 := by
        have : p 2 * ρ v ≤ p 2 * (‖v‖ + 1) := mul_le_mul_of_nonneg_left hρv hz0.le
        nlinarith
      have he : ‖cexp (I * k * (p 2 * ρ v))‖ = 1 := by
        rw [show I * (k : ℂ) * ((p 2 : ℂ) * (ρ v : ℂ)) = I * ((k * (p 2 * ρ v) : ℝ) : ℂ) by
          push_cast; ring]
        exact Complex.norm_exp_I_mul_ofReal _
      have h1 : ‖(1 : ℂ) - I * k * (p 2 * ρ v)‖ ≤ 1 + |k| * (‖x‖ + a + 2) := by
        calc ‖(1 : ℂ) - I * k * (p 2 * ρ v)‖ ≤ ‖(1 : ℂ)‖ + ‖I * k * (p 2 * ρ v)‖ :=
              norm_sub_le _ _
          _ = 1 + |k| * (p 2 * ρ v) := by
            rw [show I * (k : ℂ) * ((p 2 : ℂ) * (ρ v : ℂ)) = I * ((k * (p 2 * ρ v) : ℝ) : ℂ) by
              push_cast; ring]
            rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_mul,
              abs_of_nonneg hθ]
            simp
          _ ≤ 1 + |k| * (‖x‖ + a + 2) := by gcongr
      simp only [hH, hb, norm_mul, he, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hP0 v), one_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hM _) h1 (norm_nonneg _) hM0) (hP0 v)
  have hbi : Integrable bound := integrable_poissonKernel_one.const_mul _
  have hlim : ∀ᵐ v ∂(volume : Measure E2), Tendsto (fun p => H p v)
      (𝓝[upperHalfSpace] (planePoint x)) (𝓝 (u₀ x * (poissonKernel 1 v : ℂ))) := by
    refine Eventually.of_forall fun v => ?_
    have h := ((hHc v).tendsto (planePoint x)).mono_left
      (nhdsWithin_le_nhds (s := upperHalfSpace))
    simpa [hH] using h
  have hT := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall fun p => (hHv p).aestronglyMeasurable) hbound hbi hlim
  have hval : ∫ v : E2, u₀ x * (poissonKernel 1 v : ℂ) = u₀ x := by
    rw [integral_const_mul, integral_complex_ofReal, integral_poissonKernel_one]
    simp
  rw [hval] at hT
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hp
  have h := apertureField_spacePoint_eq k u₀ (planeCoord p) (z := p 2) hp
  rw [spacePoint_planeCoord] at h
  exact h.symm

/-! ### Boundary values in the sense of limits -/

/-- The extension of a function on `z > 0` by the values `g` on the plane. -/
def boundaryExtension (f : E3 → ℂ) (g : E2 → ℂ) (p : E3) : ℂ :=
  if 0 < p 2 then f p else g (planeCoord p)

/-- **A function continuous on `z > 0` with the limits `g` at the plane, extended by `g`, is
continuous on the closed half-space**, for continuous `g`. -/
theorem continuousOn_boundaryExtension {f : E3 → ℂ} {g : E2 → ℂ}
    (hf : ContinuousOn f upperHalfSpace) (hg : Continuous g)
    (hb : ∀ x : E2, Tendsto f (𝓝[upperHalfSpace] (planePoint x)) (𝓝 (g x))) :
    ContinuousOn (boundaryExtension f g) {p : E3 | 0 ≤ p 2} := by
  intro p hp
  rcases (show (0 : ℝ) ≤ p 2 from hp).lt_or_eq with hp0 | hp0
  · have hev : boundaryExtension f g =ᶠ[𝓝 p] f := by
      filter_upwards [isOpen_upperHalfSpace.mem_nhds hp0] with q hq
      simp only [boundaryExtension, show 0 < q 2 from hq, ↓reduceIte]
    have hc : ContinuousAt (boundaryExtension f g) p :=
      ((hf.continuousAt (isOpen_upperHalfSpace.mem_nhds hp0)).congr hev.symm)
    exact hc.continuousWithinAt
  · have hpx : p = planePoint (planeCoord p) := by
      ext i
      fin_cases i <;> simp [planeCoord, planePoint, ← hp0]
    have hval : boundaryExtension f g p = g (planeCoord p) := by
      simp [boundaryExtension, ← hp0]
    have hsplit : {q : E3 | 0 ≤ q 2} = upperHalfSpace ∪ {q : E3 | q 2 = 0} := by
      ext q
      simp only [mem_ofPred_eq, mem_union, upperHalfSpace]
      constructor
      · intro h
        rcases h.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr h.symm
      · rintro (h | h)
        · exact h.le
        · exact h.ge
    show Tendsto _ _ _
    rw [hsplit, nhdsWithin_union, tendsto_sup, hval]
    constructor
    · have h1 := hb (planeCoord p)
      rw [← hpx] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with q hq
      simp only [boundaryExtension, show 0 < q 2 from hq, ↓reduceIte]
    · have h2 : Tendsto (fun q => g (planeCoord q)) (𝓝 p) (𝓝 (g (planeCoord p))) :=
        (hg.comp continuous_planeCoord).tendsto p
      refine (h2.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with q hq
      have hq' : ¬ 0 < q 2 := by
        rw [show q 2 = 0 from hq]
        exact lt_irrefl 0
      simp only [boundaryExtension, hq', ↓reduceIte]

/-- **The aperture field with its boundary values is continuous on the closed half-space**. -/
theorem continuousOn_apertureFieldExt (k : ℝ) {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) :
    ContinuousOn (boundaryExtension (apertureField k u₀) u₀) {p : E3 | 0 ≤ p 2} :=
  continuousOn_boundaryExtension (contDiffOn_apertureField k hc hs).continuousOn hc
    (tendsto_apertureField_nhdsWithin k hc hs)

/-! ### The limit `ε → 0⁺` of the representation -/

/-- The point `(x, ε)` tends to the point `(x, 0)` of the plane within `z > 0` as `ε → 0⁺`. -/
theorem tendsto_spacePoint_nhdsWithin (x : E2) :
    Tendsto (fun ε : ℝ => spacePoint x ε) (𝓝[>] 0) (𝓝[upperHalfSpace] (planePoint x)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Continuous fun ε : ℝ => spacePoint x ε :=
      continuous_spacePoint.comp (by fun_prop : Continuous fun ε : ℝ => (x, ε))
    have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    show 0 < (spacePoint x ε) 2
    rw [spacePoint_apply_two]
    exact hε

/-- `|(x, z)| ≤ |x| + z` for `z ≥ 0`. -/
theorem norm_spacePoint_le (x : E2) {z : ℝ} (hz : 0 ≤ z) : ‖spacePoint x z‖ ≤ ‖x‖ + z := by
  have h : ‖spacePoint x z‖ ^ 2 ≤ (‖x‖ + z) ^ 2 := by
    rw [norm_sq_spacePoint]
    nlinarith [norm_nonneg x]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- **A radiating solution with the boundary values `u₀` is the aperture field of `u₀`**: if `u`
is of class `C²` on `z > 0`, solves the Helmholtz equation there, tends to the continuous data
`u₀` at every point of the plane (within `z > 0`) and satisfies the radiation condition, then
`u(y) = ∫ u₀(x) K_k(y − (x, 0)) dx` on `z > 0`. The representation from the plane `z = ε`
passes to the limit `ε → 0⁺` by dominated convergence, with the bound `O((1 + |x|)⁻³)` from the
radiation condition far out and from the continuity up to the plane near the axis. -/
theorem eq_apertureField {k : ℝ} {u₀ : E2 → ℂ} (hu₀ : Continuous u₀) {u : E3 → ℂ}
    (hu : ContDiffOn ℝ 2 u upperHalfSpace) (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0)
    (hb : ∀ x : E2, Tendsto u (𝓝[upperHalfSpace] (planePoint x)) (𝓝 (u₀ x)))
    (hrad : IsRadiating k u) {y : E3} (hy : 0 < y 2) : u y = apertureField k u₀ y := by
  set g : ℝ → E2 → ℂ := fun ε x => u (spacePoint x ε) * rayleighKernel k (y - spacePoint x ε)
    with hgdef
  obtain ⟨⟨C, R₀, hC⟩, -⟩ := id hrad
  set C' := max C 0 with hC'def
  have hC' : ∀ p : E3, 0 < p 2 → R₀ ≤ ‖p‖ → ‖p‖ * ‖u p‖ ≤ C' := fun p hp hpR =>
    (hC p hp hpR).trans (le_max_left _ _)
  set R₂ := max (max R₀ 1) (2 * ‖y‖ + 2) with hR₂
  have hR₂0 : 0 ≤ R₂ := le_trans zero_le_one (le_trans (le_max_right _ _) (le_max_left _ _))
  -- the bound of `u` near the axis, from the continuity up to the plane
  have hext := continuousOn_boundaryExtension hu.continuousOn hu₀ hb
  have hKc : IsCompact ({p : E3 | 0 ≤ p 2} ∩ closedBall 0 (R₂ + 1)) :=
    (isCompact_closedBall 0 (R₂ + 1)).inter_left (isClosed_le continuous_const (by fun_prop))
  obtain ⟨Mv, hMv⟩ := hKc.exists_bound_of_continuousOn (hext.mono inter_subset_left)
  set Mv' := max Mv 0 with hMv'
  have hMv'0 : 0 ≤ Mv' := le_max_right _ _
  have hnear : ∀ p : E3, 0 < p 2 → ‖p‖ ≤ R₂ + 1 → ‖u p‖ ≤ Mv' := fun p hp hpR => by
    have h := hMv p ⟨hp.le, by simpa using hpR⟩
    simp only [boundaryExtension, hp, ↓reduceIte] at h
    exact h.trans (le_max_left _ _)
  set MK := y 2 * (1 + |k| * (‖y‖ + R₂ + 1)) / (2 * π * (y 2 / 2) ^ 3) with hMK
  have hMK0 : 0 ≤ MK := by positivity
  set A := 4 * C' * y 2 * (1 + |k|) / π with hA
  set Bc := Mv' * MK * (1 + R₂) ^ 3 + A with hBc
  -- the domination
  have hdom : ∀ ε : ℝ, 0 < ε → ε ≤ min 1 (y 2 / 2) → ∀ x : E2,
      ‖g ε x‖ ≤ Bc * ((1 + ‖x‖) ^ 3)⁻¹ := by
    intro ε hε hε1 x
    have hε1' : ε ≤ 1 := le_trans hε1 (min_le_left _ _)
    have hε2 : ε ≤ y 2 / 2 := le_trans hε1 (min_le_right _ _)
    have hA0 : 0 ≤ A := by positivity
    have hinv : 0 < ((1 + ‖x‖) ^ 3)⁻¹ := by positivity
    by_cases hx : R₂ ≤ ‖x‖
    · have h := norm_boundaryIntegrand_le (k := k) (le_max_right C 0) hC' hε
        (by linarith) hx
      calc ‖g ε x‖ ≤ A * ((1 + ‖x‖) ^ 3)⁻¹ := h
        _ ≤ Bc * ((1 + ‖x‖) ^ 3)⁻¹ := by
          gcongr
          have : 0 ≤ Mv' * MK * (1 + R₂) ^ 3 := by positivity
          linarith
    · rw [not_le] at hx
      have hsp : ‖spacePoint x ε‖ ≤ R₂ + 1 := by
        have := norm_spacePoint_le x hε.le
        linarith
      have hu1 : ‖u (spacePoint x ε)‖ ≤ Mv' :=
        hnear _ (by rw [spacePoint_apply_two]; exact hε) hsp
      have hK1 : ‖rayleighKernel k (y - spacePoint x ε)‖ ≤ MK := by
        set q := y - spacePoint x ε with hqdef
        have hq2 : q 2 = y 2 - ε := by simp [hqdef]
        have hRq : y 2 / 2 ≤ ‖q‖ := by
          have := abs_apply_le_norm q 2
          rw [hq2, abs_of_nonneg (by linarith)] at this
          linarith
        have hRq' : ‖q‖ ≤ ‖y‖ + R₂ + 1 := by
          have := norm_sub_le y (spacePoint x ε)
          linarith
        have hR0 : 0 < ‖q‖ := lt_of_lt_of_le (by positivity) hRq
        have hψ := norm_kernelProfile_le k hR0
        rw [rayleighKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, hq2,
          abs_of_nonneg (by linarith), hMK]
        calc (y 2 - ε) * ‖kernelProfile k ‖q‖‖
            ≤ y 2 * ((1 + |k| * ‖q‖) / (2 * π * ‖q‖ ^ 3)) := by
              gcongr
              linarith
          _ ≤ y 2 * ((1 + |k| * (‖y‖ + R₂ + 1)) / (2 * π * (y 2 / 2) ^ 3)) := by
              gcongr
          _ = y 2 * (1 + |k| * (‖y‖ + R₂ + 1)) / (2 * π * (y 2 / 2) ^ 3) := by ring
      have h3 : 1 ≤ (1 + R₂) ^ 3 * ((1 + ‖x‖) ^ 3)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
        gcongr
      calc ‖g ε x‖ = ‖u (spacePoint x ε)‖ * ‖rayleighKernel k (y - spacePoint x ε)‖ :=
            norm_mul _ _
        _ ≤ Mv' * MK := by gcongr
        _ ≤ Mv' * MK * ((1 + R₂) ^ 3 * ((1 + ‖x‖) ^ 3)⁻¹) := by
            have : 0 ≤ Mv' * MK := by positivity
            nlinarith
        _ ≤ Bc * ((1 + ‖x‖) ^ 3)⁻¹ := by
            rw [hBc, add_mul, ← mul_assoc]
            have : 0 ≤ A * ((1 + ‖x‖) ^ 3)⁻¹ := by positivity
            linarith
  have hmin : (0 : ℝ) < min 1 (y 2 / 2) := lt_min one_pos (by positivity)
  have hlim : Tendsto (fun ε => ∫ x, g ε x) (𝓝[>] 0)
      (𝓝 (∫ x, u₀ x * rayleighKernel k (y - planePoint x))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => Bc * ((1 + ‖x‖) ^ 3)⁻¹)
      ?_ ?_ (integrable_inv_one_add_norm_pow_three.const_mul Bc) ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < y 2 by exact hy)] with ε hε
      exact (continuous_boundaryIntegrand hu.continuousOn hε.1 hε.2).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT hmin] with ε hε
      exact Eventually.of_forall (hdom ε hε.1 hε.2)
    · refine Eventually.of_forall fun x => ?_
      have h1 : Tendsto (fun ε => u (spacePoint x ε)) (𝓝[>] 0) (𝓝 (u₀ x)) :=
        (hb x).comp (tendsto_spacePoint_nhdsWithin x)
      have hq : y - planePoint x ≠ 0 := sub_ne_zero.mpr fun h => by
        rw [h, planePoint_apply_two] at hy
        exact lt_irrefl 0 hy
      have hcs : Continuous fun ε : ℝ => y - spacePoint x ε :=
        continuous_const.sub (continuous_spacePoint.comp
          (by fun_prop : Continuous fun ε : ℝ => (x, ε)))
      have h2 : Tendsto (fun ε => rayleighKernel k (y - spacePoint x ε)) (𝓝[>] 0)
          (𝓝 (rayleighKernel k (y - planePoint x))) := by
        have hc := (contDiffAt_rayleighKernel k (n := 0) hq).continuousAt
        have h0 : Tendsto (fun ε : ℝ => y - spacePoint x ε) (𝓝 0) (𝓝 (y - planePoint x)) := by
          simpa using hcs.tendsto 0
        exact (hc.tendsto.comp h0).mono_left nhdsWithin_le_nhds
      exact h1.mul h2
  have hev : (fun ε => ∫ x, g ε x) =ᶠ[𝓝[>] 0] fun _ => u y := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < y 2 / 2 by positivity)] with ε hε
    exact (eq_integral_spacePoint hu hH hrad hy hε.1 (by linarith [hε.2])).symm
  have := tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hlim
  rw [this]
  rfl

/-! ### Existence and uniqueness of the radiating Dirichlet problem -/

/-- **The radiating Dirichlet problem of the half-space** with the data `u₀`: `u` is of class `C²`
on `z > 0` and solves the Helmholtz equation there (classical in the interior), tends to `u₀` at
every point of the plane within `z > 0` (continuous up to the plane with the trace `u₀`) and
satisfies the Sommerfeld radiation condition `IsRadiating`. The values of `u` off `z > 0` play no
role. -/
def IsRadiatingDirichletSolution (k : ℝ) (u₀ : E2 → ℂ) (u : E3 → ℂ) : Prop :=
  ContDiffOn ℝ 2 u upperHalfSpace ∧ (∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) ∧
    (∀ x : E2, Tendsto u (𝓝[upperHalfSpace] (planePoint x)) (𝓝 (u₀ x))) ∧ IsRadiating k u

/-- **Existence**: for `k ≥ 0` and continuous data of compact support the aperture field solves
the radiating Dirichlet problem. -/
theorem isRadiatingDirichletSolution_apertureField {k : ℝ} (hk : 0 ≤ k) {u₀ : E2 → ℂ}
    (hc : Continuous u₀) (hs : HasCompactSupport u₀) :
    IsRadiatingDirichletSolution k u₀ (apertureField k u₀) :=
  ⟨(contDiffOn_apertureField k hc hs).of_le (by simp),
    fun _ hp => helmholtz_apertureField k hc hs hp, tendsto_apertureField_nhdsWithin k hc hs,
    apertureField_isRadiating hk hc hs⟩

/-- **Every solution of the radiating Dirichlet problem is the aperture field** of its data, on
`z > 0`, for continuous data `u₀` and every real `k`. -/
theorem IsRadiatingDirichletSolution.eqOn_apertureField {k : ℝ} {u₀ : E2 → ℂ}
    (hu₀ : Continuous u₀) {u : E3 → ℂ} (h : IsRadiatingDirichletSolution k u₀ u) :
    EqOn u (apertureField k u₀) upperHalfSpace := fun _ hp =>
  eq_apertureField hu₀ h.1 h.2.1 h.2.2.1 h.2.2.2 hp

/-- **Uniqueness**: two solutions of the radiating Dirichlet problem with the same continuous data
agree on `z > 0`. -/
theorem IsRadiatingDirichletSolution.eqOn {k : ℝ} {u₀ : E2 → ℂ} (hu₀ : Continuous u₀)
    {u v : E3 → ℂ} (hu : IsRadiatingDirichletSolution k u₀ u)
    (hv : IsRadiatingDirichletSolution k u₀ v) : EqOn u v upperHalfSpace := fun _ hp =>
  (hu.eqOn_apertureField hu₀ hp).trans (hv.eqOn_apertureField hu₀ hp).symm

/-- **The aperture model is the unique radiating solution with the aperture data as Dirichlet
values**: for `k ≥ 0` and continuous data of compact support, the aperture field solves the
problem and every solution agrees with it on `z > 0`. -/
theorem apertureField_unique {k : ℝ} (hk : 0 ≤ k) {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) :
    IsRadiatingDirichletSolution k u₀ (apertureField k u₀) ∧
      ∀ u : E3 → ℂ, IsRadiatingDirichletSolution k u₀ u →
        EqOn u (apertureField k u₀) upperHalfSpace :=
  ⟨isRadiatingDirichletSolution_apertureField hk hc hs, fun _ h => h.eqOn_apertureField hc⟩

/-- The aperture field of the data `0` vanishes. -/
@[simp] theorem apertureField_zero (k : ℝ) : apertureField k (fun _ => 0) = fun _ => 0 := by
  funext p
  simp [apertureField]

/-- **Uniqueness for zero data**: a solution of the Helmholtz equation of class `C²` on `z > 0`
with the limit `0` at every point of the plane and the radiation condition vanishes on `z > 0`. -/
theorem eq_zero_of_isRadiating {k : ℝ} {u : E3 → ℂ} (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0)
    (hb : ∀ x : E2, Tendsto u (𝓝[upperHalfSpace] (planePoint x)) (𝓝 0))
    (hrad : IsRadiating k u) {p : E3} (hp : 0 < p 2) : u p = 0 := by
  have h := eq_apertureField (u₀ := fun _ => 0) continuous_const hu hH hb hrad hp
  rw [h, apertureField_zero]

/-- The field of the smooth aperture solves the radiating Dirichlet problem with the data
`apertureBump`. -/
theorem isRadiatingDirichletSolution_apertureBump {k : ℝ} (hk : 0 ≤ k) :
    IsRadiatingDirichletSolution k apertureBump (apertureField k apertureBump) :=
  isRadiatingDirichletSolution_apertureField hk continuous_apertureBump
    hasCompactSupport_apertureBump

/-- **Uniqueness for the smooth aperture**: every radiating solution with the boundary values
`apertureBump` is the field of the smooth aperture on `z > 0`. -/
theorem eqOn_apertureField_apertureBump {k : ℝ} {u : E3 → ℂ}
    (h : IsRadiatingDirichletSolution k apertureBump u) :
    EqOn u (apertureField k apertureBump) upperHalfSpace :=
  h.eqOn_apertureField continuous_apertureBump

end ProjectAinos.Electrodynamics.Diffraction
