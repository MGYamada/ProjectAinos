/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.OrthogonalSlicing
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateEinsteinEquation
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-!
# The weak Einstein equations across a hypersurface

Co-ordinates `x = (x⁰, …, x^d)` on an open set of the model, a hypersurface `x^k = 0`, and a metric
given by a coordinate metric `gm` on the side `x^k < 0` and `gp` on the side `x^k ≥ 0`
(`glue k gm.coefficient gp.coefficient`), each smooth up to the hyperplane, continuous across it.
The Einstein tensor of such a metric is a distribution, defined by one integration by parts.

* `weakEinsteinDensity`, `weakEinstein`: for a tensor density `φ^{jl}` with the trace reversal
  `Φ^{jl} = φ^{jl} − ½ g^{jl} g_{mn} φ^{mn}` (`traceRev`), `⟨G, φ⟩ = ∫ (−Γ^i_{jl} ∂_iΦ^{jl} +
  Γ^i_{il} ∂_jΦ^{jl} + (Γ^i_{ia}Γ^a_{jl} − Γ^i_{ja}Γ^a_{il}) Φ^{jl}) d^{d+1}x`, which needs only
  first derivatives of the metric; for a smooth metric it is `∫ G_{jl} φ^{jl}`
  (`weakEinsteinDensity_eq_of_mem`, from `weak_algebra` and `sum_ricciOf_mul_traceRev`).
  `IsTestDensity`, `IsWeakEinstein`: the weak Einstein equations `⟨G, φ⟩ = κ ∫ T_{jl} φ^{jl}` for
  all smooth compactly supported test tensor densities on a collar.
* `integral_divergence_upper`, `integral_divergence_lower`: the divergence theorem on the two
  half-spaces, from Mathlib's divergence theorem on a box; `volume_hyperplane`: the hyperplane is
  a null set.
* `weakFlux_sub_weakFlux`, `jump_algebra`: when the metric is continuous across the hyperplane and
  `∂_k` is its unit normal there (`g_{kμ} = ε δ_{kμ}`, `ε² = 1`), the tangential derivatives are
  continuous and the jump of the flux `V^i = −Γ^i_{jl}Φ^{jl} + Γ^m_{ml}Φ^{il}` is
  `−ε([K_ab] − h_ab[K]) φ^{ab}`, with the second fundamental forms `K` (`secondFundamental k 1`),
  the induced metric `h`, `[K] = h^{ab}[K_ab]` (`inv_succAbove_eq`: `h^{ab}` is the tangential
  block of `g^{-1}`).
* **`weakEinstein_glue`** (Lanczos, Israel): `⟨G, φ⟩ = ∫_{x^k<0} G⁻φ + ∫_{x^k>0} G⁺φ −
  ε ∫ ([K_ab] − h_ab[K]) φ^{ab} dy`: the singular part of the Einstein tensor of the glued metric
  is `−ε([K_ab] − h_ab[K])` times the surface measure. The jumps of `∂_k g_{kμ}` drop out.
  `isWeakEinstein_glue`: if the second fundamental forms agree and each side solves `G = κT`, the
  glued metric solves the weak Einstein equations with no surface layer.
* `contDiffOn_glue_iff`, `contDiffOn_glue_coefficient_iff`: the glued metric is `C¹` on the
  collar exactly when the normal derivatives agree on the hyperplane;
  **`contDiffOn_glue_iff_secondFundamental`**: when moreover `∂_k g_{kμ}` agree (as in Gaussian
  normal co-ordinates), it is `C¹` exactly when the second fundamental forms agree.

The measure is the Lebesgue measure of the co-ordinates, so `φ` is a tensor density; on the
hyperplane, where `g_{kk} = ε`, the measure `dy` of the co-ordinates is the density
`√|h| dy` divided by `√|g|`, so `−ε([K_ab] − h_ab[K]) δ(x^k)` is the invariant surface term.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {d : ℕ}

/-! ### The divergence theorem on a half-space -/

section HalfSpace

/-- A co-ordinate hyperplane `x^k = c` is a null set. -/
theorem volume_hyperplane (k : Fin (d + 1)) (c : ℝ) :
    volume {x : MinkowskiModel d | x k = c} = 0 := by
  have h0 : volume ((LinearMap.ker (LinearMap.proj k : MinkowskiModel d →ₗ[ℝ] ℝ)) :
      Set (MinkowskiModel d)) = 0 := by
    refine Measure.addHaar_submodule volume _ fun h => ?_
    have hm : (Pi.single k 1 : MinkowskiModel d) ∈
        LinearMap.ker (LinearMap.proj k : MinkowskiModel d →ₗ[ℝ] ℝ) := by
      rw [h]
      exact Submodule.mem_top
    simp at hm
  have he : {x : MinkowskiModel d | x k = c} =
      (fun x => x + -Pi.single k c) ⁻¹' ((LinearMap.ker
        (LinearMap.proj k : MinkowskiModel d →ₗ[ℝ] ℝ)) : Set (MinkowskiModel d)) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.proj_apply, Pi.add_apply, Pi.neg_apply, Pi.single_eq_same]
    constructor <;> intro h <;> linarith
  rw [he, measure_preimage_add_right, h0]


/-- A compact set of the model lies in an open cube `|x_j| < L`. -/
theorem exists_abs_lt_of_isCompact {K : Set (MinkowskiModel d)} (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ j, |x j| < L := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨|R| + 1, by positivity, fun x hx j => ?_⟩
  have h1 : ‖x‖ ≤ R := by simpa using hR hx
  have h2 : ‖x j‖ ≤ ‖x‖ := norm_le_pi_norm x j
  rw [Real.norm_eq_abs] at h2
  have := le_abs_self R
  linarith

variable {V : Fin (d + 1) → MinkowskiModel d → ℝ} {O K : Set (MinkowskiModel d)}

/-- A field that vanishes off a compact set has a vanishing derivative off it. -/
theorem fderiv_eq_zero_of_notMem_isCompact {f : MinkowskiModel d → ℝ} (hK : IsCompact K)
    (hf : ∀ x ∉ K, f x = 0) {x : MinkowskiModel d} (hx : x ∉ K) : fderiv ℝ f x = 0 := by
  have h : f =ᶠ[𝓝 x] fun _ => 0 :=
    eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) fun y hy => hf y hy
  rw [h.fderiv_eq]
  simp

/-- A field of class `C¹` on an open set `O` that vanishes off a compact set `K` is
differentiable at the points of `O` and off `K`. -/
theorem differentiableAt_of_mem_or_notMem {f : MinkowskiModel d → ℝ} (hO : IsOpen O)
    (hf : ContDiffOn ℝ 1 f O) (hK : IsCompact K) (hfK : ∀ x ∉ K, f x = 0)
    {x : MinkowskiModel d} (hx : x ∈ O ∨ x ∉ K) : DifferentiableAt ℝ f x := by
  rcases hx with hx | hx
  · exact (hf.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hx)
  · have h : f =ᶠ[𝓝 x] fun _ => 0 :=
      eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) fun y hy => hfK y hy
    exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h

/-- The partial derivatives of such a field are continuous at the points of `O` and off `K`. -/
theorem continuousAt_fderiv_of_mem_or_notMem {f : MinkowskiModel d → ℝ} (hO : IsOpen O)
    (hf : ContDiffOn ℝ 1 f O) (hK : IsCompact K) (hfK : ∀ x ∉ K, f x = 0)
    {x : MinkowskiModel d} (hx : x ∈ O ∨ x ∉ K) (v : MinkowskiModel d) :
    ContinuousAt (fun y => fderiv ℝ f y v) x := by
  rcases hx with hx | hx
  · exact (((hf.continuousOn_fderiv_of_isOpen hO le_rfl).continuousAt
      (hO.mem_nhds hx)).clm_apply continuousAt_const)
  · have h : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x] fun _ => 0 :=
      eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) fun y hy => by
        simp only [fderiv_eq_zero_of_notMem_isCompact hK hfK hy]
        rfl
    exact continuousAt_const.congr h.symm

/-- **The divergence theorem on the half-space** `x^k ≥ 0`: for fields of class `C¹` on an open
set `O` containing the points of a compact set `K` with `x^k ≥ 0`, vanishing off `K`,
`∫_{x^k > 0} ∂_i V^i = −∫ V^k(y₀ = 0)`, the integral over the hyperplane `x^k = 0` in the
co-ordinates `y = (x^j)_{j ≠ k}`. -/
theorem integral_divergence_upper (hO : IsOpen O) (k : Fin (d + 1))
    (hV : ∀ i, ContDiffOn ℝ 1 (V i) O) (hK : IsCompact K) (hVK : ∀ i, ∀ x ∉ K, V i x = 0)
    (hKO : ∀ x ∈ K, 0 ≤ x k → x ∈ O) :
    ∫ x in {x : MinkowskiModel d | 0 < x k}, ∑ i, fderiv ℝ (V i) x (Pi.single i 1) =
      -∫ y : Fin d → ℝ, V k (k.insertNth 0 y) := by
  obtain ⟨L, hL, hKL⟩ := exists_abs_lt_of_isCompact hK
  have hloc {x : MinkowskiModel d} (hx : 0 ≤ x k) : x ∈ O ∨ x ∉ K := by
    by_cases h : x ∈ K
    · exact Or.inl (hKO x h hx)
    · exact Or.inr h
  set a : MinkowskiModel d := Function.update (fun _ => -L) k 0 with ha
  set b : MinkowskiModel d := fun _ => L with hb
  have hak : a k = 0 := by simp [ha]
  have haj {j : Fin (d + 1)} (hj : j ≠ k) : a j = -L := by simp [ha, hj]
  have hle : a ≤ b := by
    intro j
    by_cases hj : j = k
    · subst hj
      rw [hak]
      exact hL.le
    · rw [haj hj]
      simp only [hb]
      linarith
  have hIcc {x : MinkowskiModel d} (hx : x ∈ Icc a b) : 0 ≤ x k := by
    have := hx.1 k
    rwa [hak] at this
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable' a b hle V
    (fun i x => fderiv ℝ (V i) x) ∅ countable_empty
    (fun i x hx => (differentiableAt_of_mem_or_notMem hO (hV i) hK (hVK i)
      (hloc (hIcc hx))).continuousAt.continuousWithinAt)
    (fun x hx i => (differentiableAt_of_mem_or_notMem hO (hV i) hK (hVK i)
      (hloc (by
        have := (hx.1 k (mem_univ k)).1
        rw [hak] at this
        exact this.le))).hasFDerivAt)
    (ContinuousOn.integrableOn_compact isCompact_Icc fun x hx =>
      ContinuousAt.continuousWithinAt (tendsto_finsetSum Finset.univ fun i _ =>
        continuousAt_fderiv_of_mem_or_notMem hO (hV i) hK (hVK i) (hloc (hIcc hx))
          (Pi.single i 1)))
  have hnotK {x : MinkowskiModel d} {j : Fin (d + 1)} (hj : L ≤ |x j|) : x ∉ K :=
    fun hx => absurd (hKL x hx j) (not_lt.mpr hj)
  have hface (i : Fin (d + 1)) (c : ℝ) (hc : L ≤ |c|) :
      ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), V i (i.insertNth c y) = 0 := by
    refine (setIntegral_congr_fun measurableSet_Icc fun y _ => ?_).trans (integral_zero _ _)
    exact hVK i _ (hnotK (j := i) (by rwa [Fin.insertNth_apply_same]))
  rw [Finset.sum_eq_single k] at hdiv
  rotate_left
  · intro i _ hi
    rw [hface i (b i) (by simp [hb, abs_of_pos hL]), haj hi,
      hface i (-L) (by simp [abs_of_pos hL]), sub_zero]
  · simp
  rw [hface k (b k) (by simp [hb, abs_of_pos hL]), zero_sub, hak] at hdiv
  have hfaceK : ∫ y in Icc (a ∘ k.succAbove) (b ∘ k.succAbove), V k (k.insertNth 0 y) =
      ∫ y : Fin d → ℝ, V k (k.insertNth 0 y) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    simp only [mem_Icc, not_and_or, Pi.le_def, not_forall, not_le] at hy
    obtain ⟨j, hj⟩ | ⟨j, hj⟩ := hy
    · refine hVK k _ (hnotK (j := k.succAbove j) ?_)
      rw [Fin.insertNth_apply_succAbove]
      simp only [Function.comp_apply, haj (Fin.succAbove_ne k j)] at hj
      rw [abs_of_neg (by linarith)]
      linarith
    · refine hVK k _ (hnotK (j := k.succAbove j) ?_)
      rw [Fin.insertNth_apply_succAbove]
      simp only [Function.comp_apply, hb] at hj
      rw [abs_of_pos (by linarith)]
      linarith
  rw [hfaceK] at hdiv
  rw [← hdiv]
  set f : MinkowskiModel d → ℝ := fun x => ∑ i, fderiv ℝ (V i) x (Pi.single i 1)
  have hf0 {x : MinkowskiModel d} (hx : x ∉ K) : f x = 0 := by
    simp only [f]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [fderiv_eq_zero_of_notMem_isCompact hK (hVK i) hx]
    rfl
  have hS : MeasurableSet {x : MinkowskiModel d | 0 < x k} :=
    measurableSet_lt measurable_const (measurable_pi_apply k)
  have h1 : ∫ x in {x : MinkowskiModel d | 0 < x k}, f x =
      ∫ x in Icc a b ∩ {x : MinkowskiModel d | 0 < x k}, f x := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS inter_subset_right
      fun x hx => hf0 fun hxK => hx.2 ⟨⟨fun j => ?_, fun j => ?_⟩, hx.1⟩
    · by_cases hj : j = k
      · subst hj
        rw [hak]
        exact (show (0 : ℝ) < x j from hx.1).le
      · rw [haj hj]
        have := hKL x hxK j
        rw [abs_lt] at this
        linarith
    · have := hKL x hxK j
      rw [abs_lt] at this
      simp only [hb]
      linarith
  have h2 : ∫ x in Icc a b ∩ {x : MinkowskiModel d | 0 < x k}, f x = ∫ x in Icc a b, f x := by
    refine setIntegral_congr_set ?_
    refine ae_eq_set.mpr ⟨by rw [sdiff_eq_empty.mpr inter_subset_left, measure_empty],
      measure_mono_null (fun x hx => ?_) (volume_hyperplane k 0)⟩
    have h0 := hIcc hx.1
    have h1 : ¬ 0 < x k := fun h => hx.2 ⟨hx.1, h⟩
    exact le_antisymm (not_lt.mp h1) h0
  rw [h1, h2]

/-- **The divergence theorem on the half-space** `x^k ≤ 0`:
`∫_{x^k < 0} ∂_i V^i = ∫ V^k(y₀ = 0)`. -/
theorem integral_divergence_lower (hO : IsOpen O) (k : Fin (d + 1))
    (hV : ∀ i, ContDiffOn ℝ 1 (V i) O) (hK : IsCompact K) (hVK : ∀ i, ∀ x ∉ K, V i x = 0)
    (hKO : ∀ x ∈ K, x k ≤ 0 → x ∈ O) :
    ∫ x in {x : MinkowskiModel d | x k < 0}, ∑ i, fderiv ℝ (V i) x (Pi.single i 1) =
      ∫ y : Fin d → ℝ, V k (k.insertNth 0 y) := by
  obtain ⟨L, hL, hKL⟩ := exists_abs_lt_of_isCompact hK
  have hloc {x : MinkowskiModel d} (hx : x k ≤ 0) : x ∈ O ∨ x ∉ K := by
    by_cases h : x ∈ K
    · exact Or.inl (hKO x h hx)
    · exact Or.inr h
  set a : MinkowskiModel d := fun _ => -L with ha
  set b : MinkowskiModel d := Function.update (fun _ => L) k 0 with hb
  have hbk : b k = 0 := by simp [hb]
  have hbj {j : Fin (d + 1)} (hj : j ≠ k) : b j = L := by simp [hb, hj]
  have hle : a ≤ b := by
    intro j
    by_cases hj : j = k
    · subst hj
      rw [hbk]
      simp only [ha]
      linarith
    · rw [hbj hj]
      simp only [ha]
      linarith
  have hIcc {x : MinkowskiModel d} (hx : x ∈ Icc a b) : x k ≤ 0 := by
    have := hx.2 k
    rwa [hbk] at this
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable' a b hle V
    (fun i x => fderiv ℝ (V i) x) ∅ countable_empty
    (fun i x hx => (differentiableAt_of_mem_or_notMem hO (hV i) hK (hVK i)
      (hloc (hIcc hx))).continuousAt.continuousWithinAt)
    (fun x hx i => (differentiableAt_of_mem_or_notMem hO (hV i) hK (hVK i)
      (hloc (by
        have := (hx.1 k (mem_univ k)).2
        rw [hbk] at this
        exact this.le))).hasFDerivAt)
    (ContinuousOn.integrableOn_compact isCompact_Icc fun x hx =>
      ContinuousAt.continuousWithinAt (tendsto_finsetSum Finset.univ fun i _ =>
        continuousAt_fderiv_of_mem_or_notMem hO (hV i) hK (hVK i) (hloc (hIcc hx))
          (Pi.single i 1)))
  have hnotK {x : MinkowskiModel d} {j : Fin (d + 1)} (hj : L ≤ |x j|) : x ∉ K :=
    fun hx => absurd (hKL x hx j) (not_lt.mpr hj)
  have hface (i : Fin (d + 1)) (c : ℝ) (hc : L ≤ |c|) :
      ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), V i (i.insertNth c y) = 0 := by
    refine (setIntegral_congr_fun measurableSet_Icc fun y _ => ?_).trans (integral_zero _ _)
    exact hVK i _ (hnotK (j := i) (by rwa [Fin.insertNth_apply_same]))
  rw [Finset.sum_eq_single k] at hdiv
  rotate_left
  · intro i _ hi
    rw [hbj hi, hface i L (by simp [abs_of_pos hL]),
      hface i (a i) (by simp [ha, abs_of_pos hL]), sub_zero]
  · simp
  rw [hface k (a k) (by simp [ha, abs_of_pos hL]), sub_zero, hbk] at hdiv
  have hfaceK : ∫ y in Icc (a ∘ k.succAbove) (b ∘ k.succAbove), V k (k.insertNth 0 y) =
      ∫ y : Fin d → ℝ, V k (k.insertNth 0 y) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    simp only [mem_Icc, not_and_or, Pi.le_def, not_forall, not_le] at hy
    obtain ⟨j, hj⟩ | ⟨j, hj⟩ := hy
    · refine hVK k _ (hnotK (j := k.succAbove j) ?_)
      rw [Fin.insertNth_apply_succAbove]
      simp only [Function.comp_apply, ha] at hj
      rw [abs_of_neg (by linarith)]
      linarith
    · refine hVK k _ (hnotK (j := k.succAbove j) ?_)
      rw [Fin.insertNth_apply_succAbove]
      simp only [Function.comp_apply, hbj (Fin.succAbove_ne k j)] at hj
      rw [abs_of_pos (by linarith)]
      linarith
  rw [hfaceK] at hdiv
  rw [← hdiv]
  set f : MinkowskiModel d → ℝ := fun x => ∑ i, fderiv ℝ (V i) x (Pi.single i 1)
  have hf0 {x : MinkowskiModel d} (hx : x ∉ K) : f x = 0 := by
    simp only [f]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [fderiv_eq_zero_of_notMem_isCompact hK (hVK i) hx]
    rfl
  have hS : MeasurableSet {x : MinkowskiModel d | x k < 0} :=
    measurableSet_lt (measurable_pi_apply k) measurable_const
  have h1 : ∫ x in {x : MinkowskiModel d | x k < 0}, f x =
      ∫ x in Icc a b ∩ {x : MinkowskiModel d | x k < 0}, f x := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS inter_subset_right
      fun x hx => hf0 fun hxK => hx.2 ⟨⟨fun j => ?_, fun j => ?_⟩, hx.1⟩
    · have := hKL x hxK j
      rw [abs_lt] at this
      simp only [ha]
      linarith
    · by_cases hj : j = k
      · subst hj
        rw [hbk]
        exact (show x j < 0 from hx.1).le
      · rw [hbj hj]
        have := hKL x hxK j
        rw [abs_lt] at this
        linarith
  have h2 : ∫ x in Icc a b ∩ {x : MinkowskiModel d | x k < 0}, f x = ∫ x in Icc a b, f x := by
    refine setIntegral_congr_set ?_
    refine ae_eq_set.mpr ⟨by rw [sdiff_eq_empty.mpr inter_subset_left, measure_empty],
      measure_mono_null (fun x hx => ?_) (volume_hyperplane k 0)⟩
    have h0 := hIcc hx.1
    have h1 : ¬ x k < 0 := fun h => hx.2 ⟨hx.1, h⟩
    exact le_antisymm h0 (not_lt.mp h1)
  rw [h1, h2]

end HalfSpace


/-! ### The weak Einstein functional -/

section Weak

/-- The coefficients `Cm` on the side `x^k < 0` and `Cp` on the side `x^k ≥ 0`, glued along the
hyperplane `x^k = 0`. -/
def glue (k : Fin (d + 1)) (Cm Cp : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  if x k < 0 then Cm x else Cp x

/-- The trace reversal `Φ^{jl} = φ^{jl} − ½ C^{jl} C_{mn} φ^{mn}` of a test density `φ` with the
coefficients `C`; `G_{jl} φ^{jl} = R_{jl} Φ^{jl}`. -/
def traceRev (C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  φ x - ((∑ m, ∑ n, C x m n * φ x m n) / 2) • (C x)⁻¹

/-- **The weak form of the Einstein tensor** tested against a tensor density `φ`, at a point: the
Ricci tensor after one integration by parts, paired with the trace reversal `Φ` of `φ`,
`−Γ^i_{jl} ∂_iΦ^{jl} + Γ^i_{il} ∂_jΦ^{jl} + (Γ^i_{ia}Γ^a_{jl} − Γ^i_{ja}Γ^a_{il}) Φ^{jl}`. It needs
only the first derivatives of the coefficients. -/
def weakEinsteinDensity (C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) : ℝ :=
  (∑ i, ∑ j, ∑ l, (-(christoffelOf C x i j l *
      fderiv ℝ (fun y => traceRev C φ y j l) x (Pi.single i 1)) +
    christoffelOf C x i i l * fderiv ℝ (fun y => traceRev C φ y j l) x (Pi.single j 1))) +
  ∑ j, ∑ l, (∑ i, ∑ a, (christoffelOf C x i i a * christoffelOf C x a j l -
    christoffelOf C x i j a * christoffelOf C x a i l)) * traceRev C φ x j l

/-- **The distributional Einstein tensor** `⟨G, φ⟩ = ∫ weakEinsteinDensity C φ` of coefficients
`C` with locally bounded first derivatives, on a tensor density `φ` (Lebesgue measure of the
co-ordinates). -/
def weakEinstein (C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : ℝ :=
  ∫ x, weakEinsteinDensity C φ x

/-- A **test tensor density** on `U`: smooth entries and a compact support in `U`. -/
def IsTestDensity (U : Set (MinkowskiModel d))
    (φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : Prop :=
  (∀ j l, ContDiff ℝ ∞ fun x => φ x j l) ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

/-- **The weak Einstein equations** `G_{jl} = κ T_{jl}` on `U`: for every test tensor density `φ`
on `U`, `⟨G, φ⟩ = κ ∫ T_{jl} φ^{jl}`. -/
def IsWeakEinstein (U : Set (MinkowskiModel d))
    (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (κ : ℝ)
    (T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : Prop :=
  ∀ φ, IsTestDensity U φ → weakEinstein C φ = κ * ∫ x, ∑ j, ∑ l, T x j l * φ x j l

/-- The flux `V^i = −Γ^i_{jl} Φ^{jl} + Γ^m_{ml} Φ^{il}` whose divergence separates the weak form
from the Ricci tensor. -/
def weakFlux (C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (i : Fin (d + 1))
    (x : MinkowskiModel d) : ℝ :=
  -(∑ j, ∑ l, christoffelOf C x i j l * traceRev C φ x j l) +
    ∑ m, ∑ l, christoffelOf C x m m l * traceRev C φ x i l

/-- Reordering a triple sum. -/
theorem sum_rotate {n : ℕ} (X : Fin n → Fin n → Fin n → ℝ) :
    ∑ j, ∑ l, ∑ i, X i j l = ∑ i, ∑ j, ∑ l, X i j l :=
  calc _ = ∑ j, ∑ i, ∑ l, X i j l := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- **The integration by parts identity**, in the values of the symbols `Γ`, their derivatives
`dΓ i j l m = ∂_m Γ^i_{jl}`, the trace reversal `Φ` and its derivatives `dΦ j l m = ∂_m Φ^{jl}`:
the weak form is the divergence of the flux plus `R_{jl} Φ^{jl}`. -/
theorem weak_algebra {n : ℕ} (Γ : Fin n → Fin n → Fin n → ℝ)
    (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ) (Φ : Fin n → Fin n → ℝ)
    (dΦ : Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ l, (-(Γ i j l * dΦ j l i) + Γ i i l * dΦ j l j)) +
      ∑ j, ∑ l, (∑ i, ∑ a, (Γ i i a * Γ a j l - Γ i j a * Γ a i l)) * Φ j l =
    ∑ i, (-(∑ j, ∑ l, (dΓ i j l i * Φ j l + Γ i j l * dΦ j l i)) +
        ∑ m, ∑ l, (dΓ m m l i * Φ i l + Γ m m l * dΦ i l i)) +
      ∑ j, ∑ l, (∑ i, (dΓ i j l i - dΓ i i l j +
        ∑ a, (Γ i i a * Γ a j l - Γ i j a * Γ a i l))) * Φ j l := by
  have h1a : ∑ i, ∑ m, ∑ l, dΓ m m l i * Φ i l = ∑ i, ∑ j, ∑ l, dΓ i i l j * Φ j l :=
    Finset.sum_comm
  have h1b : ∑ i, ∑ m, ∑ l, Γ m m l * dΦ i l i = ∑ i, ∑ j, ∑ l, Γ i i l * dΦ j l j :=
    Finset.sum_comm
  have h2 : ∑ j, ∑ l, (∑ i, (dΓ i j l i - dΓ i i l j +
        ∑ a, (Γ i i a * Γ a j l - Γ i j a * Γ a i l))) * Φ j l =
      ∑ i, ∑ j, ∑ l, (dΓ i j l i * Φ j l - dΓ i i l j * Φ j l) +
        ∑ j, ∑ l, (∑ i, ∑ a, (Γ i i a * Γ a j l - Γ i j a * Γ a i l)) * Φ j l := by
    have e (j l : Fin n) : (∑ i, (dΓ i j l i - dΓ i i l j +
        ∑ a, (Γ i i a * Γ a j l - Γ i j a * Γ a i l))) * Φ j l =
        ∑ i, (dΓ i j l i * Φ j l - dΓ i i l j * Φ j l) +
          (∑ i, ∑ a, (Γ i i a * Γ a j l - Γ i j a * Γ a i l)) * Φ j l := by
      rw [Finset.sum_add_distrib, add_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => e j l]
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_rotate (fun i j l => dΓ i j l i * Φ j l - dΓ i i l j * Φ j l)]
  rw [h2]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [h1a, h1b]
  ring

/-- `R_{jl} Φ^{jl} = G_{jl} φ^{jl}`: the trace reversal moves the trace term of the Einstein
tensor onto the test density. -/
theorem sum_ricciOf_mul_traceRev (C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : MinkowskiModel d) :
    ∑ j, ∑ l, ricciOf C x j l * traceRev C φ x j l =
      ∑ j, ∑ l, einsteinOf C x j l * φ x j l := by
  set t := ∑ m, ∑ n, C x m n * φ x m n with ht
  have e1 (j l : Fin (d + 1)) : ricciOf C x j l * traceRev C φ x j l =
      ricciOf C x j l * φ x j l - t / 2 * (ricciOf C x j l * (C x)⁻¹ j l) := by
    simp only [traceRev, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ← ht]
    ring
  have e2 (j l : Fin (d + 1)) : einsteinOf C x j l * φ x j l =
      ricciOf C x j l * φ x j l - scalarOf C x / 2 * (C x j l * φ x j l) := by
    simp only [einsteinOf]
    ring
  simp only [e1, e2, Finset.sum_sub_distrib, ← Finset.mul_sum, ← ht]
  simp only [scalarOf]
  ring

end Weak


/-! ### The jump at the hyperplane -/

section Jump

variable (k : Fin (d + 1))

/-- **The block inverse**: if the column `k` of an invertible matrix `C` is `ε e_k`, the
tangential block of `C⁻¹` is the inverse of the tangential block of `C`. -/
theorem inv_succAbove_eq {C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (hC : C * C⁻¹ = 1)
    {ε : ℝ} (hcol : ∀ μ, C μ k = if μ = k then ε else 0) (a b : Fin d) :
    (Matrix.of fun a b => C (k.succAbove a) (k.succAbove b))⁻¹ a b =
      C⁻¹ (k.succAbove a) (k.succAbove b) := by
  have h : (Matrix.of fun a b => C (k.succAbove a) (k.succAbove b)) *
      (Matrix.of fun a b => C⁻¹ (k.succAbove a) (k.succAbove b)) = 1 := by
    ext a c
    have hac := congrFun (congrFun hC (k.succAbove a)) (k.succAbove c)
    rw [Matrix.mul_apply, Fin.sum_univ_succAbove _ k, hcol] at hac
    simp only [Fin.succAbove_ne k a, ↓reduceIte, zero_mul, zero_add] at hac
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [hac, Matrix.one_apply, Matrix.one_apply]
    simp
  rw [Matrix.inv_eq_right_inv h]
  rfl

/-- A sum against a row of the form `ε e_k`. -/
theorem sum_row_mul {ε : ℝ} {r : Fin (d + 1) → ℝ} (hr : ∀ μ, r μ = if μ = k then ε else 0)
    (f : Fin (d + 1) → ℝ) : ∑ μ, r μ * f μ = ε * f k := by
  rw [Finset.sum_eq_single k (fun μ _ hμ => by simp [hr, hμ]) (by simp), hr]
  simp

/-- A double sum split at the index `k`. -/
theorem sum_sum_succAbove (f : Fin (d + 1) → Fin (d + 1) → ℝ) :
    ∑ j, ∑ l, f j l = f k k + ∑ b, f k (k.succAbove b) +
      ∑ a, (f (k.succAbove a) k + ∑ b, f (k.succAbove a) (k.succAbove b)) := by
  rw [Fin.sum_univ_succAbove _ k, Fin.sum_univ_succAbove _ k]
  congr 1
  exact Finset.sum_congr rfl fun a _ => Fin.sum_univ_succAbove _ k

/-- **The algebra of the surface term.** At a point of the hyperplane, let the common metric
`C` have the row and the column `k` equal to `ε e_k` (`ε² = 1`), with the inverse `Ci`, and let
`γ = [∂_k C]` be the jump of the normal derivative, the other derivatives being continuous. For
the jumps `ΔΓ^i_{jl} = ½ C^{im} (δ_j^k γ_{lm} + δ_l^k γ_{mj} − δ_m^k γ_{jl})` of the Christoffel
symbols and the trace reversal `Φ` of `φ`, the jump of the flux `ΔΓ^k_{jl} Φ^{jl} − ΔΓ^m_{ml}
Φ^{kl}` is `−ε ([K_ab] − h_ab [K]) φ^{ab}`, with `[K_ab] = γ_ab/2` and `[K] = h^{ab} [K_ab]`. -/
theorem jump_algebra {C Ci γ φ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {ε : ℝ}
    (hε : ε * ε = 1) (hrow : ∀ μ, C k μ = if μ = k then ε else 0)
    (hcol : ∀ μ, C μ k = if μ = k then ε else 0)
    (hirow : ∀ μ, Ci k μ = if μ = k then ε else 0) (hicol : ∀ μ, Ci μ k = if μ = k then ε else 0)
    (hγ : ∀ p q, γ p q = γ q p) :
    ∑ j, ∑ l, (∑ m, Ci k m * (((if j = k then γ l m else 0) + (if l = k then γ m j else 0) -
        (if m = k then γ j l else 0)) / 2)) *
        (φ j l - (∑ m, ∑ n, C m n * φ m n) / 2 * Ci j l) -
      ∑ l, (∑ m, ∑ p, Ci m p * (((if m = k then γ l p else 0) + (if l = k then γ p m else 0) -
        (if p = k then γ m l else 0)) / 2)) *
        (φ k l - (∑ m, ∑ n, C m n * φ m n) / 2 * Ci k l) =
      -ε * ∑ a, ∑ b, (γ (k.succAbove a) (k.succAbove b) / 2 -
        C (k.succAbove a) (k.succAbove b) * ∑ c, ∑ e, Ci (k.succAbove c) (k.succAbove e) *
          (γ (k.succAbove c) (k.succAbove e) / 2)) * φ (k.succAbove a) (k.succAbove b) := by
  set t := ∑ m, ∑ n, C m n * φ m n with ht
  set S := ∑ c, ∑ e, Ci (k.succAbove c) (k.succAbove e) * γ (k.succAbove c) (k.succAbove e)
    with hS
  set H := ∑ a, ∑ b, C (k.succAbove a) (k.succAbove b) * φ (k.succAbove a) (k.succAbove b)
    with hH
  set G := ∑ a, ∑ b, γ (k.succAbove a) (k.succAbove b) * φ (k.succAbove a) (k.succAbove b)
    with hG
  have hne (a : Fin d) : k.succAbove a ≠ k := Fin.succAbove_ne k a
  -- the trace of the density
  have htr : t = ε * φ k k + H := by
    rw [ht, sum_sum_succAbove k]
    simp only [hrow, hcol, hne, ↓reduceIte, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
    rfl
  -- the jumps of the symbols
  have hA (j l : Fin (d + 1)) : ∑ m, Ci k m * (((if j = k then γ l m else 0) +
      (if l = k then γ m j else 0) - (if m = k then γ j l else 0)) / 2) =
      ε * (((if j = k then γ l k else 0) + (if l = k then γ k j else 0) - γ j l) / 2) := by
    rw [sum_row_mul k hirow]
    simp
  have hB (l : Fin (d + 1)) : ∑ m, ∑ p, Ci m p * (((if m = k then γ l p else 0) +
      (if l = k then γ p m else 0) - (if p = k then γ m l else 0)) / 2) =
      if l = k then (ε * γ k k + S) / 2 else 0 := by
    have e (m p : Fin (d + 1)) : Ci m p * (((if m = k then γ l p else 0) +
        (if l = k then γ p m else 0) - (if p = k then γ m l else 0)) / 2) =
        (if m = k then Ci k p * γ l p else 0) / 2 + (if l = k then Ci m p * γ p m else 0) / 2 -
          (if p = k then Ci m k * γ m l else 0) / 2 := by
      split_ifs <;> simp_all <;> ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_ite_irrel,
      Finset.sum_const_zero]
    rw [sum_row_mul k hirow (fun p => γ l p)]
    rw [show ∑ m, Ci m k * γ m l = ε * γ k l from sum_row_mul k hicol (fun m => γ m l)]
    have htrγ : ∑ m, ∑ p, Ci m p * γ p m = ε * γ k k + S := by
      rw [sum_sum_succAbove k]
      simp only [hirow, hicol, hne, ↓reduceIte, zero_mul, Finset.sum_const_zero, add_zero,
        zero_add, hS]
      exact congrArg _ (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by
        rw [hγ])
    split_ifs with hl
    · subst hl
      rw [htrγ]
      ring
    · rw [hγ l k]
      ring
  simp only [hA, hB]
  -- the second sum collapses to `l = k`
  have h2 : ∑ l, (if l = k then (ε * γ k k + S) / 2 else 0) * (φ k l - t / 2 * Ci k l) =
      (ε * γ k k + S) / 2 * (φ k k - t / 2 * ε) := by
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (by simp)]
    simp [hirow]
  rw [h2]
  -- the first sum, split at `k`
  rw [sum_sum_succAbove k]
  have hkk : ε * (((if k = k then γ k k else 0) + (if k = k then γ k k else 0) - γ k k) / 2) *
      (φ k k - t / 2 * Ci k k) = ε / 2 * γ k k * (φ k k - t / 2 * ε) := by
    simp only [↓reduceIte, hirow]
    ring
  have hkb (b : Fin d) : ε * (((if k = k then γ (k.succAbove b) k else 0) +
      (if k.succAbove b = k then γ k k else 0) - γ k (k.succAbove b)) / 2) *
      (φ k (k.succAbove b) - t / 2 * Ci k (k.succAbove b)) = 0 := by
    simp only [↓reduceIte, hne, hγ (k.succAbove b) k]
    ring
  have hak (a : Fin d) : ε * (((if k.succAbove a = k then γ k k else 0) +
      (if k = k then γ k (k.succAbove a) else 0) - γ (k.succAbove a) k) / 2) *
      (φ (k.succAbove a) k - t / 2 * Ci (k.succAbove a) k) = 0 := by
    simp only [↓reduceIte, hne, hγ (k.succAbove a) k]
    ring
  have hab (a b : Fin d) : ε * (((if k.succAbove a = k then γ (k.succAbove b) k else 0) +
      (if k.succAbove b = k then γ k (k.succAbove a) else 0) -
        γ (k.succAbove a) (k.succAbove b)) / 2) *
      (φ (k.succAbove a) (k.succAbove b) - t / 2 * Ci (k.succAbove a) (k.succAbove b)) =
      -(ε / 2) * (γ (k.succAbove a) (k.succAbove b) * φ (k.succAbove a) (k.succAbove b)) +
        ε * t / 4 * (Ci (k.succAbove a) (k.succAbove b) * γ (k.succAbove a) (k.succAbove b)) := by
    simp only [hne, ↓reduceIte]
    ring
  rw [hkk, Finset.sum_congr rfl fun b _ => hkb b, Finset.sum_const_zero, add_zero,
    Finset.sum_congr rfl fun a _ => by
      rw [hak a, zero_add, Finset.sum_congr rfl fun b _ => hab a b]]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← hG, ← hS]
  have hS2 : ∑ c, ∑ e, Ci (k.succAbove c) (k.succAbove e) *
      (γ (k.succAbove c) (k.succAbove e) / 2) = S / 2 := by
    rw [hS, Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hR (s : ℝ) : ∑ a, ∑ b, (γ (k.succAbove a) (k.succAbove b) / 2 -
      C (k.succAbove a) (k.succAbove b) * s) * φ (k.succAbove a) (k.succAbove b) =
      G / 2 - s * H := by
    rw [hG, hH, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hS2, hR (S / 2)]
  rw [htr]
  linear_combination (φ k k * S / 2) * hε

end Jump


/-! ### One smooth side -/

section Side

variable {σ : LorentzConvention} {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)
  {φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}

theorem contDiffOn_traceRev (hφ : ∀ j l, ContDiff ℝ ∞ fun x => φ x j l) (j l : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (fun x => traceRev g.coefficient φ x j l) U := by
  simp only [traceRev, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (hφ j l).contDiffOn.sub (((ContDiffOn.sum fun m _ => ContDiffOn.sum fun n _ =>
    (g.coefficient_contDiffOn m n).mul (hφ m n).contDiffOn).div_const 2).mul
      (g.contDiffOn_coefficient_inv j l))

theorem contDiffOn_weakFlux (hφ : ∀ j l, ContDiff ℝ ∞ fun x => φ x j l) (i : Fin (d + 1)) :
    ContDiffOn ℝ ∞ (weakFlux g.coefficient φ i) U :=
  (ContDiffOn.sum fun j _ => ContDiffOn.sum fun l _ => (g.contDiffOn_christoffelOf i j l).mul
    (g.contDiffOn_traceRev hφ j l)).neg.add (ContDiffOn.sum fun m _ => ContDiffOn.sum
      fun l _ => (g.contDiffOn_christoffelOf m m l).mul (g.contDiffOn_traceRev hφ i l))

/-- **The weak form on a smooth side**: where the coefficients are smooth, the weak density is
the divergence of the flux plus `G_{jl} φ^{jl}`. -/
theorem weakEinsteinDensity_eq_of_mem (hφ : ∀ j l, ContDiff ℝ ∞ fun x => φ x j l)
    {x : MinkowskiModel d} (hx : x ∈ U) :
    weakEinsteinDensity g.coefficient φ x =
      ∑ i, fderiv ℝ (weakFlux g.coefficient φ i) x (Pi.single i 1) +
        ∑ j, ∑ l, einsteinOf g.coefficient x j l * φ x j l := by
  have hU := U.isOpen.mem_nhds hx
  have hΓ (a b c : Fin (d + 1)) : HasFDerivAt (fun y => christoffelOf g.coefficient y a b c)
      (fderiv ℝ (fun y => christoffelOf g.coefficient y a b c) x) x :=
    (((g.contDiffOn_christoffelOf a b c).contDiffAt hU).differentiableAt (by simp)).hasFDerivAt
  have hΦ (a b : Fin (d + 1)) : HasFDerivAt (fun y => traceRev g.coefficient φ y a b)
      (fderiv ℝ (fun y => traceRev g.coefficient φ y a b) x) x :=
    (((g.contDiffOn_traceRev hφ a b).contDiffAt hU).differentiableAt (by simp)).hasFDerivAt
  have hV (i : Fin (d + 1)) : fderiv ℝ (weakFlux g.coefficient φ i) x (Pi.single i 1) =
      -(∑ j, ∑ l, (fderiv ℝ (fun y => christoffelOf g.coefficient y i j l) x (Pi.single i 1) *
          traceRev g.coefficient φ x j l + christoffelOf g.coefficient x i j l *
          fderiv ℝ (fun y => traceRev g.coefficient φ y j l) x (Pi.single i 1))) +
        ∑ m, ∑ l, (fderiv ℝ (fun y => christoffelOf g.coefficient y m m l) x (Pi.single i 1) *
          traceRev g.coefficient φ x i l + christoffelOf g.coefficient x m m l *
          fderiv ℝ (fun y => traceRev g.coefficient φ y i l) x (Pi.single i 1)) := by
    have h := ((HasFDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) fun l _ =>
        (hΓ i j l).fun_mul (hΦ j l)).fun_neg).fun_add
        (HasFDerivAt.fun_sum (u := Finset.univ) fun m _ =>
          HasFDerivAt.fun_sum (u := Finset.univ) fun l _ => (hΓ m m l).fun_mul (hΦ i l))
    rw [show weakFlux g.coefficient φ i = fun y =>
      -(∑ j, ∑ l, christoffelOf g.coefficient y i j l * traceRev g.coefficient φ y j l) +
        ∑ m, ∑ l, christoffelOf g.coefficient y m m l * traceRev g.coefficient φ y i l
      from rfl, h.fderiv]
    simp only [add_apply, neg_apply, FunLike.coe_sum, Finset.sum_apply, smul_apply,
      smul_eq_mul]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    · exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
  rw [show weakEinsteinDensity g.coefficient φ x = _ from weak_algebra
    (fun i j l => christoffelOf g.coefficient x i j l)
    (fun i j l m => fderiv ℝ (fun y => christoffelOf g.coefficient y i j l) x (Pi.single m 1))
    (fun j l => traceRev g.coefficient φ x j l)
    (fun j l m => fderiv ℝ (fun y => traceRev g.coefficient φ y j l) x (Pi.single m 1))]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => (hV i).symm
  · exact sum_ricciOf_mul_traceRev g.coefficient φ x

end Side

/-! ### Off the support of the test density -/

section Off

variable {C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
  {x : MinkowskiModel d}

theorem traceRev_eq_zero {y : MinkowskiModel d} (hy : φ y = 0) : traceRev C φ y = 0 := by
  simp [traceRev, hy]

theorem traceRev_eventuallyEq_zero (hx : x ∉ tsupport φ) (j l : Fin (d + 1)) :
    (fun y => traceRev C φ y j l) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
  rw [traceRev_eq_zero hy]
  rfl

theorem fderiv_traceRev_eq_zero (hx : x ∉ tsupport φ) (j l : Fin (d + 1)) :
    fderiv ℝ (fun y => traceRev C φ y j l) x = 0 := by
  rw [(traceRev_eventuallyEq_zero hx j l).fderiv_eq]
  simp

theorem fderiv_weakFlux_eq_zero (hx : x ∉ tsupport φ) (i : Fin (d + 1)) :
    fderiv ℝ (weakFlux C φ i) x = 0 := by
  have h : weakFlux C φ i =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [weakFlux, traceRev_eq_zero hy]
  rw [h.fderiv_eq]
  simp

theorem weakEinsteinDensity_eq_zero (hx : x ∉ tsupport φ) : weakEinsteinDensity C φ x = 0 := by
  have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp [weakEinsteinDensity, fderiv_traceRev_eq_zero hx, traceRev_eq_zero h0]

theorem weakFlux_eq_zero {y : MinkowskiModel d} (hy : φ y = 0) (i : Fin (d + 1)) :
    weakFlux C φ i y = 0 := by
  simp [weakFlux, traceRev_eq_zero hy]

end Off


/-! ### The jump of the flux at the hyperplane -/

section Boundary

variable (k : Fin (d + 1))

/-- Two functions equal on the hyperplane `x^k = 0` near a point of it have equal derivatives
along the hyperplane. -/
theorem fderiv_eq_of_eqOn_hyperplane {f h : MinkowskiModel d → ℝ} {W : Set (MinkowskiModel d)}
    (hW : IsOpen W) {z : MinkowskiModel d} (hz : z ∈ W) (hzk : z k = 0)
    (hfh : ∀ y ∈ W, y k = 0 → f y = h y) (hf : DifferentiableAt ℝ f z)
    (hh : DifferentiableAt ℝ h z) {j : Fin (d + 1)} (hj : j ≠ k) :
    fderiv ℝ f z (Pi.single j 1) = fderiv ℝ h z (Pi.single j 1) := by
  set ℓ : ℝ → MinkowskiModel d := fun t => z + t • Pi.single j 1 with hℓdef
  have hℓ : HasDerivAt ℓ (Pi.single j 1) 0 := by
    simpa only [one_smul, id] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j 1 : MinkowskiModel d)).const_add z
  have hℓ0 : ℓ 0 = z := by simp [hℓdef]
  have hf' : HasFDerivAt f (fderiv ℝ f z) (ℓ 0) := by
    rw [hℓ0]
    exact hf.hasFDerivAt
  have hh' : HasFDerivAt h (fderiv ℝ h z) (ℓ 0) := by
    rw [hℓ0]
    exact hh.hasFDerivAt
  have h1 := hf'.comp_hasDerivAt (0 : ℝ) hℓ
  have h2 := hh'.comp_hasDerivAt (0 : ℝ) hℓ
  have hev : f ∘ ℓ =ᶠ[𝓝 0] h ∘ ℓ := by
    have hc : ContinuousAt ℓ 0 := hℓ.continuousAt
    filter_upwards [hc.preimage_mem_nhds (by rw [hℓ0]; exact hW.mem_nhds hz)] with t ht
    refine hfh _ ht ?_
    simp [hℓdef, hzk, Ne.symm hj]
  exact h1.unique (h2.congr_of_eventuallyEq hev)

/-- The row `k` of the inverse of a matrix whose row `k` is `ε e_k`, `ε² = 1`. -/
theorem inv_row_eq {C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (hC : C * C⁻¹ = 1) {ε : ℝ}
    (hε : ε * ε = 1) (hrow : ∀ μ, C k μ = if μ = k then ε else 0) (μ : Fin (d + 1)) :
    C⁻¹ k μ = if μ = k then ε else 0 := by
  have h := congrFun (congrFun hC k) μ
  rw [Matrix.mul_apply, sum_row_mul k hrow (fun l => C⁻¹ l μ), Matrix.one_apply] at h
  have h' : C⁻¹ k μ = ε * (if k = μ then 1 else 0) := by
    rw [← h, ← mul_assoc, hε, one_mul]
  rw [h']
  by_cases hμ : μ = k
  · subst hμ
    simp
  · simp [hμ, Ne.symm hμ]

/-- The column `k` of the inverse of a matrix whose column `k` is `ε e_k`, `ε² = 1`. -/
theorem inv_col_eq {C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (hC : C⁻¹ * C = 1) {ε : ℝ}
    (hε : ε * ε = 1) (hcol : ∀ μ, C μ k = if μ = k then ε else 0) (μ : Fin (d + 1)) :
    C⁻¹ μ k = if μ = k then ε else 0 := by
  have h := congrFun (congrFun hC μ) k
  rw [Matrix.mul_apply] at h
  simp_rw [mul_comm (C⁻¹ μ _)] at h
  rw [sum_row_mul k hcol (fun l => C⁻¹ μ l), Matrix.one_apply] at h
  have h' : C⁻¹ μ k = ε * (if μ = k then 1 else 0) := by
    rw [← h, ← mul_assoc, hε, one_mul]
  rw [h']
  by_cases hμ : μ = k
  · subst hμ
    simp
  · simp [hμ]

variable {σ : LorentzConvention} {Um Up : Opens (MinkowskiModel d)}
  (gm : CoordinateMetric σ d Um) (gp : CoordinateMetric σ d Up)

/-- **The jump of the flux across the hyperplane.** Let two coordinate metrics agree on the
hyperplane `x^k = 0` near `z`, with the row `k` of the common coefficients equal to `ε e_k`
(`ε² = 1`: the co-ordinate field `∂_k` is the unit normal there). Then the jump of the flux
`V^k` at `z` is `−ε ([K_ab] − h_ab [K]) φ^{ab}`, with the jump `[K] = K₊ − K₋` of the second
fundamental forms for the normal `∂_k` (`secondFundamental k 1`), the induced metric `h` and
`[K] = h^{ab}[K_ab]`. -/
theorem weakFlux_sub_weakFlux {W : Set (MinkowskiModel d)} (hW : IsOpen W)
    (hWm : W ⊆ Um) (hWp : W ⊆ Up) {ε : ℝ} (hε : ε * ε = 1)
    (hcont : ∀ y ∈ W, y k = 0 → gm.coefficient y = gp.coefficient y)
    (hnormal : ∀ y ∈ W, y k = 0 → ∀ μ, gp.coefficient y k μ = if μ = k then ε else 0)
    (φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) {z : MinkowskiModel d}
    (hz : z ∈ W) (hzk : z k = 0) :
    weakFlux gm.coefficient φ k z - weakFlux gp.coefficient φ k z =
      -ε * ∑ a, ∑ b, ((gp.secondFundamental k 1 z a b - gm.secondFundamental k 1 z a b) -
        gp.inducedMetric k z a b * ∑ c, ∑ e, (gp.inducedMetric k z)⁻¹ c e *
          (gp.secondFundamental k 1 z c e - gm.secondFundamental k 1 z c e)) *
            φ z (k.succAbove a) (k.succAbove b) := by
  have hzm : z ∈ Um := hWm hz
  have hzp : z ∈ Up := hWp hz
  have hC0 : gm.coefficient z = gp.coefficient z := hcont z hz hzk
  have hrow := hnormal z hz hzk
  have hcol (μ : Fin (d + 1)) : gp.coefficient z μ k = if μ = k then ε else 0 := by
    rw [gp.coefficient_symmetric hzp μ k]
    exact hrow μ
  have hinv : gp.coefficient z * (gp.coefficient z)⁻¹ = 1 := gp.coefficient_mul_inv ⟨z, hzp⟩
  have hinv' : (gp.coefficient z)⁻¹ * gp.coefficient z = 1 :=
    Matrix.nonsing_inv_mul _ (gp.coefficient_det_ne_zero ⟨z, hzp⟩).isUnit
  have hirow := inv_row_eq k hinv hε hrow
  have hicol := inv_col_eq k hinv' hε hcol
  -- derivatives of the coefficients
  have hdp (p q : Fin (d + 1)) : DifferentiableAt ℝ (fun y => gp.coefficient y p q) z :=
    ((gp.coefficient_contDiffOn p q).contDiffAt (Up.isOpen.mem_nhds hzp)).differentiableAt
      (by simp)
  have hdm (p q : Fin (d + 1)) : DifferentiableAt ℝ (fun y => gm.coefficient y p q) z :=
    ((gm.coefficient_contDiffOn p q).contDiffAt (Um.isOpen.mem_nhds hzm)).differentiableAt
      (by simp)
  set γ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Matrix.of fun p q =>
    fderiv ℝ (fun y => gp.coefficient y p q) z (Pi.single k 1) -
      fderiv ℝ (fun y => gm.coefficient y p q) z (Pi.single k 1) with hγdef
  have hjump (p q μ : Fin (d + 1)) :
      fderiv ℝ (fun y => gp.coefficient y p q) z (Pi.single μ 1) -
        fderiv ℝ (fun y => gm.coefficient y p q) z (Pi.single μ 1) =
        if μ = k then γ p q else 0 := by
    by_cases hμ : μ = k
    · subst hμ
      simp [hγdef]
    · simp only [hμ, ↓reduceIte]
      rw [fderiv_eq_of_eqOn_hyperplane k hW hz hzk
        (fun y hy hyk => (congrFun (congrFun (hcont y hy hyk) p) q).symm) (hdp p q) (hdm p q) hμ,
        sub_self]
  have hsymm {U' : Opens (MinkowskiModel d)} (g' : CoordinateMetric σ d U') (hz' : z ∈ U')
      (p q : Fin (d + 1)) : fderiv ℝ (fun y => g'.coefficient y p q) z =
        fderiv ℝ (fun y => g'.coefficient y q p) z := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [U'.isOpen.mem_nhds hz'] with y hy using g'.coefficient_symmetric hy p q
  have hγ (p q : Fin (d + 1)) : γ p q = γ q p := by
    simp only [hγdef, Matrix.of_apply, hsymm gp hzp p q, hsymm gm hzm p q]
  -- the jumps of the Christoffel symbols
  have hΓ (i j l : Fin (d + 1)) : christoffelOf gp.coefficient z i j l -
      christoffelOf gm.coefficient z i j l = ∑ m, (gp.coefficient z)⁻¹ i m *
        (((if j = k then γ l m else 0) + (if l = k then γ m j else 0) -
          (if m = k then γ j l else 0)) / 2) := by
    simp only [christoffelOf, hC0, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hjump l m j, ← hjump m j l, ← hjump j l m]
    ring
  have hTR : traceRev gm.coefficient φ z = traceRev gp.coefficient φ z := by
    simp only [traceRev, hC0]
  have hcomm (X : Fin (d + 1) → Fin (d + 1) → ℝ) (Y : Fin (d + 1) → ℝ) :
      ∑ l, (∑ m, X m l) * Y l = ∑ m, ∑ l, X m l * Y l := by
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have key : weakFlux gm.coefficient φ k z - weakFlux gp.coefficient φ k z =
      ∑ j, ∑ l, (christoffelOf gp.coefficient z k j l - christoffelOf gm.coefficient z k j l) *
          traceRev gp.coefficient φ z j l -
        ∑ l, (∑ m, (christoffelOf gp.coefficient z m m l -
          christoffelOf gm.coefficient z m m l)) * traceRev gp.coefficient φ z k l := by
    rw [hcomm]
    simp only [weakFlux, hTR, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [key]
  simp only [hΓ]
  have hTRz (j l : Fin (d + 1)) : traceRev gp.coefficient φ z j l =
      φ z j l - (∑ m, ∑ n, gp.coefficient z m n * φ z m n) / 2 * (gp.coefficient z)⁻¹ j l := by
    simp [traceRev]
  simp only [hTRz]
  rw [jump_algebra k hε hrow hcol hirow hicol hγ]
  -- the second fundamental forms and the induced metric
  have habs : Real.sqrt |gp.coefficient z k k| = 1 := by
    rw [hrow k]
    simp only [↓reduceIte]
    have : |ε| = 1 := by
      have h1 : |ε| * |ε| = 1 := by rw [← abs_mul, hε, abs_one]
      nlinarith [abs_nonneg ε]
    rw [this, Real.sqrt_one]
  have hK (a b : Fin d) : gp.secondFundamental k 1 z a b - gm.secondFundamental k 1 z a b =
      γ (k.succAbove a) (k.succAbove b) / 2 := by
    rw [secondFundamental_apply, secondFundamental_apply, hC0, habs, ← mul_sub]
    simp [hγdef]
    ring
  have hh (a b : Fin d) : gp.inducedMetric k z a b =
      gp.coefficient z (k.succAbove a) (k.succAbove b) := rfl
  have hhinv (c e : Fin d) : (gp.inducedMetric k z)⁻¹ c e =
      (gp.coefficient z)⁻¹ (k.succAbove c) (k.succAbove e) :=
    inv_succAbove_eq k hinv hcol c e
  simp only [hK, hh, hhinv]

end Boundary


/-! ### The surface term -/

section Junction

/-- A function continuous at the points of a closed set `S` in a compact set `K`, and zero on
`S \ K`, is integrable on `S`. -/
theorem integrableOn_of_continuousAt {n : ℕ} {f : (Fin n → ℝ) → ℝ} {S K : Set (Fin n → ℝ)}
    (hS : IsClosed S) (hK : IsCompact K) (hf : ∀ x ∈ S ∩ K, ContinuousAt f x)
    (h0 : ∀ x ∈ S, x ∉ K → f x = 0) : IntegrableOn f S :=
  (ContinuousOn.integrableOn_compact (hK.inter_left hS) fun x hx =>
    (hf x hx).continuousWithinAt).of_forall_sdiff_eq_zero hS.measurableSet
      fun x hx => h0 x hx.1 fun h => hx.2 ⟨hx.1, h⟩

/-- The weak density depends only on the germ of the coefficients. -/
theorem weakEinsteinDensity_congr {C C' φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    {x : MinkowskiModel d} (hC : C =ᶠ[𝓝 x] C') :
    weakEinsteinDensity C φ x = weakEinsteinDensity C' φ x := by
  have hT (j l : Fin (d + 1)) : (fun y => traceRev C φ y j l) =ᶠ[𝓝 x]
      fun y => traceRev C' φ y j l := by
    filter_upwards [hC] with y hy
    simp only [traceRev, hy]
  have hd (j l : Fin (d + 1)) := (hT j l).fderiv_eq (𝕜 := ℝ)
  have hv (j l : Fin (d + 1)) := (hT j l).eq_of_nhds
  simp only [weakEinsteinDensity, christoffelOf_congr hC, hd, hv]

variable (k : Fin (d + 1))

theorem glue_eventuallyEq_left (Cm Cp : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    {x : MinkowskiModel d} (hx : x k < 0) : glue k Cm Cp =ᶠ[𝓝 x] Cm := by
  filter_upwards [(isOpen_lt (continuous_apply k) continuous_const).mem_nhds hx] with y hy
  simp [glue, show y k < 0 from hy]

theorem glue_eventuallyEq_right (Cm Cp : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    {x : MinkowskiModel d} (hx : 0 < x k) : glue k Cm Cp =ᶠ[𝓝 x] Cp := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply k)).mem_nhds hx] with y hy
  simp [glue, not_lt.mpr (show (0 : ℝ) < y k from hy).le]

variable {σ : LorentzConvention} {Um Up : Opens (MinkowskiModel d)}
  (gm : CoordinateMetric σ d Um) (gp : CoordinateMetric σ d Up)

/-- **The distributional Einstein tensor across a hypersurface** (Lanczos, Israel). Let the
metric be `gm` on the side `x^k < 0` and `gp` on the side `x^k ≥ 0` of a collar `U`, each
smooth up to the hyperplane (`U ∩ {x^k ≤ 0} ⊆ Um`, `U ∩ {x^k ≥ 0} ⊆ Up`), continuous across it,
with `∂_k` the unit normal on it (`g_{kμ} = ε δ_{kμ}`, `ε² = 1`). For every test tensor density
`φ` on `U`,
`⟨G, φ⟩ = ∫_{x^k<0} G⁻_{jl} φ^{jl} + ∫_{x^k>0} G⁺_{jl} φ^{jl} − ε ∫ ([K_ab] − h_ab [K]) φ^{ab}`:
the singular part of the Einstein tensor is `−ε([K_ab] − h_ab [K])` times the surface measure
`dy` of the hyperplane, the jump `[K] = K₊ − K₋` of the second fundamental forms for the normal
`∂_k`, with `[K] = h^{ab}[K_ab]`. The jumps of the normal derivatives `∂_k g_{kμ}`, which a
co-ordinate change can remove, do not enter. -/
theorem weakEinstein_glue {U : Set (MinkowskiModel d)} (hU : IsOpen U)
    (hUm : ∀ x ∈ U, x k ≤ 0 → x ∈ Um) (hUp : ∀ x ∈ U, 0 ≤ x k → x ∈ Up)
    {ε : ℝ} (hε : ε * ε = 1)
    (hcont : ∀ y ∈ U, y k = 0 → gm.coefficient y = gp.coefficient y)
    (hnormal : ∀ y ∈ U, y k = 0 → ∀ μ, gp.coefficient y k μ = if μ = k then ε else 0)
    {φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (hφ : IsTestDensity U φ) :
    weakEinstein (glue k gm.coefficient gp.coefficient) φ =
      (∫ x in {x : MinkowskiModel d | x k < 0}, ∑ j, ∑ l,
          einsteinOf gm.coefficient x j l * φ x j l) +
        (∫ x in {x : MinkowskiModel d | 0 < x k}, ∑ j, ∑ l,
          einsteinOf gp.coefficient x j l * φ x j l) -
        ε * ∫ y : Fin d → ℝ, ∑ a, ∑ b,
          ((gp.secondFundamental k 1 (k.insertNth 0 y) a b -
              gm.secondFundamental k 1 (k.insertNth 0 y) a b) -
            gp.inducedMetric k (k.insertNth 0 y) a b * ∑ c, ∑ e,
              (gp.inducedMetric k (k.insertNth 0 y))⁻¹ c e *
                (gp.secondFundamental k 1 (k.insertNth 0 y) c e -
                  gm.secondFundamental k 1 (k.insertNth 0 y) c e)) *
            φ (k.insertNth 0 y) (k.succAbove a) (k.succAbove b) := by
  obtain ⟨hφs, hφc, hφU⟩ := hφ
  set K := tsupport φ with hKdef
  have hK : IsCompact K := hφc
  have hφ0 (x : MinkowskiModel d) (hx : x ∉ K) : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hVm0 (i : Fin (d + 1)) (x : MinkowskiModel d) (hx : x ∉ K) :
      weakFlux gm.coefficient φ i x = 0 := weakFlux_eq_zero (hφ0 x hx) i
  have hVp0 (i : Fin (d + 1)) (x : MinkowskiModel d) (hx : x ∉ K) :
      weakFlux gp.coefficient φ i x = 0 := weakFlux_eq_zero (hφ0 x hx) i
  set Fm : MinkowskiModel d → ℝ :=
    fun x => ∑ i, fderiv ℝ (weakFlux gm.coefficient φ i) x (Pi.single i 1) with hFm
  set Fp : MinkowskiModel d → ℝ :=
    fun x => ∑ i, fderiv ℝ (weakFlux gp.coefficient φ i) x (Pi.single i 1) with hFp
  set Gm : MinkowskiModel d → ℝ :=
    fun x => ∑ j, ∑ l, einsteinOf gm.coefficient x j l * φ x j l with hGm
  set Gp : MinkowskiModel d → ℝ :=
    fun x => ∑ j, ∑ l, einsteinOf gp.coefficient x j l * φ x j l with hGp
  have hFm0 (x : MinkowskiModel d) (hx : x ∉ K) : Fm x = 0 := by
    simp [hFm, fderiv_weakFlux_eq_zero hx]
  have hFp0 (x : MinkowskiModel d) (hx : x ∉ K) : Fp x = 0 := by
    simp [hFp, fderiv_weakFlux_eq_zero hx]
  have hGm0 (x : MinkowskiModel d) (hx : x ∉ K) : Gm x = 0 := by
    simp [hGm, hφ0 x hx]
  have hGp0 (x : MinkowskiModel d) (hx : x ∉ K) : Gp x = 0 := by
    simp [hGp, hφ0 x hx]
  set D := weakEinsteinDensity (glue k gm.coefficient gp.coefficient) φ with hD
  -- the density on the two sides
  have hDm (x : MinkowskiModel d) (hx : x k < 0) : D x = Fm x + Gm x := by
    rw [hD, weakEinsteinDensity_congr (glue_eventuallyEq_left k _ _ hx)]
    by_cases hxK : x ∈ K
    · exact weakEinsteinDensity_eq_of_mem gm hφs (hUm x (hφU hxK) hx.le)
    · rw [weakEinsteinDensity_eq_zero hxK, hFm0 x hxK, hGm0 x hxK, add_zero]
  have hDp (x : MinkowskiModel d) (hx : 0 < x k) : D x = Fp x + Gp x := by
    rw [hD, weakEinsteinDensity_congr (glue_eventuallyEq_right k _ _ hx)]
    by_cases hxK : x ∈ K
    · exact weakEinsteinDensity_eq_of_mem gp hφs (hUp x (hφU hxK) hx.le)
    · rw [weakEinsteinDensity_eq_zero hxK, hFp0 x hxK, hGp0 x hxK, add_zero]
  -- integrability on the closed half-spaces
  have hSm : IsClosed {x : MinkowskiModel d | x k ≤ 0} :=
    isClosed_le (continuous_apply k) continuous_const
  have hSp : IsClosed {x : MinkowskiModel d | 0 ≤ x k} :=
    isClosed_le continuous_const (continuous_apply k)
  have hFm_int : IntegrableOn Fm {x : MinkowskiModel d | x k ≤ 0} :=
    integrableOn_of_continuousAt hSm hK (fun x hx => tendsto_finsetSum Finset.univ fun i _ =>
      continuousAt_fderiv_of_mem_or_notMem Um.isOpen ((contDiffOn_weakFlux gm hφs i).of_le
        (by simp)) hK (hVm0 i) (Or.inl (hUm x (hφU hx.2) hx.1)) (Pi.single i 1))
      fun x _ hx => hFm0 x hx
  have hFp_int : IntegrableOn Fp {x : MinkowskiModel d | 0 ≤ x k} :=
    integrableOn_of_continuousAt hSp hK (fun x hx => tendsto_finsetSum Finset.univ fun i _ =>
      continuousAt_fderiv_of_mem_or_notMem Up.isOpen ((contDiffOn_weakFlux gp hφs i).of_le
        (by simp)) hK (hVp0 i) (Or.inl (hUp x (hφU hx.2) hx.1)) (Pi.single i 1))
      fun x _ hx => hFp0 x hx
  have hGm_int : IntegrableOn Gm {x : MinkowskiModel d | x k ≤ 0} :=
    integrableOn_of_continuousAt hSm hK (fun x hx => tendsto_finsetSum Finset.univ fun j _ =>
      tendsto_finsetSum Finset.univ fun l _ =>
        ((contDiffAt_einsteinOf (g := gm) (hUm x (hφU hx.2) hx.1) j l).continuousAt.mul
          (hφs j l).continuous.continuousAt))
      fun x _ hx => hGm0 x hx
  have hGp_int : IntegrableOn Gp {x : MinkowskiModel d | 0 ≤ x k} :=
    integrableOn_of_continuousAt hSp hK (fun x hx => tendsto_finsetSum Finset.univ fun j _ =>
      tendsto_finsetSum Finset.univ fun l _ =>
        ((contDiffAt_einsteinOf (g := gp) (hUp x (hφU hx.2) hx.1) j l).continuousAt.mul
          (hφs j l).continuous.continuousAt))
      fun x _ hx => hGp0 x hx
  -- the integral of the density
  have hmeasm : MeasurableSet {x : MinkowskiModel d | x k < 0} :=
    measurableSet_lt (measurable_pi_apply k) measurable_const
  have hmeasp : MeasurableSet {x : MinkowskiModel d | 0 < x k} :=
    measurableSet_lt measurable_const (measurable_pi_apply k)
  have hsubm : {x : MinkowskiModel d | x k < 0} ⊆ {x | x k ≤ 0} := fun x hx =>
    show x k ≤ 0 from le_of_lt (show x k < 0 from hx)
  have hsubp : {x : MinkowskiModel d | 0 < x k} ⊆ {x | 0 ≤ x k} := fun x hx =>
    show 0 ≤ x k from le_of_lt (show 0 < x k from hx)
  have hnull : volume {x : MinkowskiModel d | x k = 0} = 0 := volume_hyperplane k 0
  have hDm_int : IntegrableOn D {x : MinkowskiModel d | x k < 0} :=
    ((hFm_int.add hGm_int).mono_set hsubm).congr_fun (fun x hx => (hDm x hx).symm) hmeasm
  have hDp_ae : (fun x => Fp x + Gp x) =ᵐ[volume.restrict {x : MinkowskiModel d | 0 ≤ x k}] D := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hSp.measurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxk
    exact (hDp x (lt_of_le_of_ne hxk (Ne.symm hx))).symm
  have hDp_int : IntegrableOn D {x : MinkowskiModel d | 0 ≤ x k} :=
    (hFp_int.add hGp_int).congr_fun_ae hDp_ae
  have hD_int : Integrable D := by
    rw [← integrableOn_univ]
    have hu : (univ : Set (MinkowskiModel d)) = {x | x k < 0} ∪ {x | 0 ≤ x k} := by
      ext x
      simp [lt_or_ge]
    rw [hu]
    exact hDm_int.union hDp_int
  have hae : {x : MinkowskiModel d | 0 ≤ x k} =ᵐ[volume] {x | 0 < x k} := by
    refine ae_eq_set.mpr ⟨measure_mono_null (fun x hx => ?_) hnull, ?_⟩
    · exact le_antisymm (not_lt.mp hx.2) hx.1
    · rw [sdiff_eq_empty.mpr hsubp, measure_empty]
  have hsplit : weakEinstein (glue k gm.coefficient gp.coefficient) φ =
      (∫ x in {x : MinkowskiModel d | x k < 0}, (Fm x + Gm x)) +
        ∫ x in {x : MinkowskiModel d | 0 < x k}, (Fp x + Gp x) := by
    rw [weakEinstein, ← hD, ← integral_add_compl hmeasm hD_int]
    congr 1
    · exact setIntegral_congr_fun hmeasm fun x hx => hDm x hx
    · have hc : {x : MinkowskiModel d | x k < 0}ᶜ = {x | 0 ≤ x k} := by
        ext x
        simp
      rw [hc, setIntegral_congr_set hae]
      exact setIntegral_congr_fun hmeasp fun x hx => hDp x hx
  rw [hsplit, integral_add (hFm_int.mono_set hsubm) (hGm_int.mono_set hsubm),
    integral_add (hFp_int.mono_set hsubp) (hGp_int.mono_set hsubp)]
  -- the divergence theorem on the two sides
  have hdm : ∫ x in {x : MinkowskiModel d | x k < 0}, Fm x =
      ∫ y : Fin d → ℝ, weakFlux gm.coefficient φ k (k.insertNth 0 y) :=
    integral_divergence_lower Um.isOpen k (fun i => (contDiffOn_weakFlux gm hφs i).of_le
      (by simp)) hK hVm0 fun x hx hxk => hUm x (hφU hx) hxk
  have hdp : ∫ x in {x : MinkowskiModel d | 0 < x k}, Fp x =
      -∫ y : Fin d → ℝ, weakFlux gp.coefficient φ k (k.insertNth 0 y) :=
    integral_divergence_upper Up.isOpen k (fun i => (contDiffOn_weakFlux gp hφs i).of_le
      (by simp)) hK hVp0 fun x hx hxk => hUp x (hφU hx) hxk
  rw [hdm, hdp]
  -- integrability on the hyperplane
  obtain ⟨L, hL, hKL⟩ := exists_abs_lt_of_isCompact hK
  have hι : Continuous fun y : Fin d → ℝ => (k.insertNth (0 : ℝ) y : MinkowskiModel d) :=
    Continuous.finInsertNth (A := fun _ => ℝ) k continuous_const continuous_id
  have hιk (y : Fin d → ℝ) : (k.insertNth (0 : ℝ) y : MinkowskiModel d) k = 0 :=
    Fin.insertNth_apply_same _ _ _
  have hιK {y : Fin d → ℝ} (hy : y ∉ Icc (fun _ => -L) fun _ => L) :
      (k.insertNth (0 : ℝ) y : MinkowskiModel d) ∉ K := by
    intro hyK
    apply hy
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have := hKL _ hyK (k.succAbove j)
      rw [Fin.insertNth_apply_succAbove, abs_lt] at this
      exact this.1.le
    · have := hKL _ hyK (k.succAbove j)
      rw [Fin.insertNth_apply_succAbove, abs_lt] at this
      exact this.2.le
  have hbd {U' : Opens (MinkowskiModel d)} (g' : CoordinateMetric σ d U')
      (hU' : ∀ x ∈ U, x k = 0 → x ∈ U') (hV0 : ∀ x ∉ K, weakFlux g'.coefficient φ k x = 0) :
      Integrable fun y : Fin d → ℝ => weakFlux g'.coefficient φ k (k.insertNth 0 y) := by
    rw [← integrableOn_univ]
    refine integrableOn_of_continuousAt isClosed_univ isCompact_Icc (fun y _ => ?_)
      fun y _ hy => hV0 _ (hιK hy)
    by_cases hyK : (k.insertNth (0 : ℝ) y : MinkowskiModel d) ∈ K
    · have hmem := hU' _ (hφU hyK) (hιk y)
      exact (((contDiffOn_weakFlux g' hφs k).continuousOn.continuousAt
        (U'.isOpen.mem_nhds hmem))).comp hι.continuousAt
    · have h : (fun y : Fin d → ℝ => weakFlux g'.coefficient φ k (k.insertNth 0 y)) =ᶠ[𝓝 y]
          fun _ => 0 := by
        filter_upwards [hι.continuousAt.preimage_mem_nhds
          (hK.isClosed.isOpen_compl.mem_nhds hyK)] with z hz using hV0 _ hz
      exact continuousAt_const.congr h.symm
  have hbm := hbd gm (fun x hx hxk => hUm x hx hxk.le) (hVm0 k)
  have hbp := hbd gp (fun x hx hxk => hUp x hx hxk.ge) (hVp0 k)
  -- the jump of the flux
  have hjump (y : Fin d → ℝ) : weakFlux gm.coefficient φ k (k.insertNth 0 y) -
      weakFlux gp.coefficient φ k (k.insertNth 0 y) =
      -ε * ∑ a, ∑ b, ((gp.secondFundamental k 1 (k.insertNth 0 y) a b -
            gm.secondFundamental k 1 (k.insertNth 0 y) a b) -
          gp.inducedMetric k (k.insertNth 0 y) a b * ∑ c, ∑ e,
            (gp.inducedMetric k (k.insertNth 0 y))⁻¹ c e *
              (gp.secondFundamental k 1 (k.insertNth 0 y) c e -
                gm.secondFundamental k 1 (k.insertNth 0 y) c e)) *
          φ (k.insertNth 0 y) (k.succAbove a) (k.succAbove b) := by
    by_cases hyU : (k.insertNth (0 : ℝ) y : MinkowskiModel d) ∈ U
    · exact weakFlux_sub_weakFlux k gm gp (hU.inter (Um.isOpen.inter Up.isOpen))
        (fun x hx => hx.2.1) (fun x hx => hx.2.2) hε (fun x hx hxk => hcont x hx.1 hxk)
        (fun x hx hxk => hnormal x hx.1 hxk) φ
        ⟨hyU, hUm _ hyU (hιk y).le, hUp _ hyU (hιk y).ge⟩ (hιk y)
    · have hyK : (k.insertNth (0 : ℝ) y : MinkowskiModel d) ∉ K := fun h => hyU (hφU h)
      simp [hVm0 k _ hyK, hVp0 k _ hyK, hφ0 _ hyK]
  have hint : (∫ y : Fin d → ℝ, weakFlux gm.coefficient φ k (k.insertNth 0 y)) -
      ∫ y : Fin d → ℝ, weakFlux gp.coefficient φ k (k.insertNth 0 y) =
      -ε * ∫ y : Fin d → ℝ, ∑ a, ∑ b, ((gp.secondFundamental k 1 (k.insertNth 0 y) a b -
            gm.secondFundamental k 1 (k.insertNth 0 y) a b) -
          gp.inducedMetric k (k.insertNth 0 y) a b * ∑ c, ∑ e,
            (gp.inducedMetric k (k.insertNth 0 y))⁻¹ c e *
              (gp.secondFundamental k 1 (k.insertNth 0 y) c e -
                gm.secondFundamental k 1 (k.insertNth 0 y) c e)) *
          φ (k.insertNth 0 y) (k.succAbove a) (k.succAbove b) := by
    rw [← integral_sub hbm hbp, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hjump)
  linear_combination hint


/-- **No surface layer**: if the second fundamental forms agree on the hyperplane and each side
solves `G = κT` pointwise, with `T` continuous up to the hyperplane, the glued metric solves the
weak Einstein equations on the collar with the glued `T`. -/
theorem isWeakEinstein_glue {U : Set (MinkowskiModel d)} (hU : IsOpen U)
    (hUm : ∀ x ∈ U, x k ≤ 0 → x ∈ Um) (hUp : ∀ x ∈ U, 0 ≤ x k → x ∈ Up)
    {ε : ℝ} (hε : ε * ε = 1)
    (hcont : ∀ y ∈ U, y k = 0 → gm.coefficient y = gp.coefficient y)
    (hnormal : ∀ y ∈ U, y k = 0 → ∀ μ, gp.coefficient y k μ = if μ = k then ε else 0)
    (hK : ∀ y ∈ U, y k = 0 → gp.secondFundamental k 1 y = gm.secondFundamental k 1 y)
    {κ : ℝ} {Tm Tp : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hTm : ∀ j l, ContinuousOn (fun x => Tm x j l) Um)
    (hTp : ∀ j l, ContinuousOn (fun x => Tp x j l) Up)
    (hEm : ∀ x ∈ U, x k < 0 → ∀ j l, einsteinOf gm.coefficient x j l = κ * Tm x j l)
    (hEp : ∀ x ∈ U, 0 < x k → ∀ j l, einsteinOf gp.coefficient x j l = κ * Tp x j l) :
    IsWeakEinstein U (glue k gm.coefficient gp.coefficient) κ (glue k Tm Tp) := by
  intro φ hφ
  have hφ' := hφ
  obtain ⟨hφs, hφc, hφU⟩ := hφ'
  set K := tsupport φ with hKdef
  have hKc : IsCompact K := hφc
  have hφ0 (x : MinkowskiModel d) (hx : x ∉ K) : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  rw [weakEinstein_glue k gm gp hU hUm hUp hε hcont hnormal hφ]
  -- the surface term vanishes
  have hsurf : (∫ y : Fin d → ℝ, ∑ a, ∑ b,
        ((gp.secondFundamental k 1 (k.insertNth 0 y) a b -
            gm.secondFundamental k 1 (k.insertNth 0 y) a b) -
          gp.inducedMetric k (k.insertNth 0 y) a b * ∑ c, ∑ e,
            (gp.inducedMetric k (k.insertNth 0 y))⁻¹ c e *
              (gp.secondFundamental k 1 (k.insertNth 0 y) c e -
                gm.secondFundamental k 1 (k.insertNth 0 y) c e)) *
          φ (k.insertNth 0 y) (k.succAbove a) (k.succAbove b)) = 0 := by
    refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans (integral_zero _ _)
    by_cases hyU : (k.insertNth (0 : ℝ) y : MinkowskiModel d) ∈ U
    · rw [hK _ hyU (Fin.insertNth_apply_same _ _ _)]
      simp
    · have hyK : (k.insertNth (0 : ℝ) y : MinkowskiModel d) ∉ K := fun h => hyU (hφU h)
      simp [hφ0 _ hyK]
  rw [hsurf, mul_zero, sub_zero]
  -- the bulk terms
  have hSm : IsClosed {x : MinkowskiModel d | x k ≤ 0} :=
    isClosed_le (continuous_apply k) continuous_const
  have hSp : IsClosed {x : MinkowskiModel d | 0 ≤ x k} :=
    isClosed_le continuous_const (continuous_apply k)
  have hmeasm : MeasurableSet {x : MinkowskiModel d | x k < 0} :=
    measurableSet_lt (measurable_pi_apply k) measurable_const
  have hmeasp : MeasurableSet {x : MinkowskiModel d | 0 < x k} :=
    measurableSet_lt measurable_const (measurable_pi_apply k)
  have hsubm : {x : MinkowskiModel d | x k < 0} ⊆ {x | x k ≤ 0} := fun x hx =>
    show x k ≤ 0 from le_of_lt (show x k < 0 from hx)
  have hsubp : {x : MinkowskiModel d | 0 < x k} ⊆ {x | 0 ≤ x k} := fun x hx =>
    show 0 ≤ x k from le_of_lt (show 0 < x k from hx)
  have hEm' : ∀ x, x k < 0 → ∑ j, ∑ l, einsteinOf gm.coefficient x j l * φ x j l =
      κ * ∑ j, ∑ l, Tm x j l * φ x j l := by
    intro x hx
    by_cases hxK : x ∈ K
    · simp only [hEm x (hφU hxK) hx, Finset.mul_sum, mul_assoc]
    · simp [hφ0 x hxK]
  have hEp' : ∀ x, 0 < x k → ∑ j, ∑ l, einsteinOf gp.coefficient x j l * φ x j l =
      κ * ∑ j, ∑ l, Tp x j l * φ x j l := by
    intro x hx
    by_cases hxK : x ∈ K
    · simp only [hEp x (hφU hxK) hx, Finset.mul_sum, mul_assoc]
    · simp [hφ0 x hxK]
  rw [setIntegral_congr_fun hmeasm hEm', setIntegral_congr_fun hmeasp hEp', integral_const_mul,
    integral_const_mul, ← mul_add]
  congr 1
  -- the integral of the glued tensor
  have hTm_int : IntegrableOn (fun x => ∑ j, ∑ l, Tm x j l * φ x j l)
      {x : MinkowskiModel d | x k ≤ 0} :=
    integrableOn_of_continuousAt hSm hKc (fun x hx => tendsto_finsetSum Finset.univ fun j _ =>
      tendsto_finsetSum Finset.univ fun l _ =>
        ((hTm j l).continuousAt (Um.isOpen.mem_nhds (hUm x (hφU hx.2) hx.1))).mul
          (hφs j l).continuous.continuousAt)
      fun x _ hx => by simp [hφ0 x hx]
  have hTp_int : IntegrableOn (fun x => ∑ j, ∑ l, Tp x j l * φ x j l)
      {x : MinkowskiModel d | 0 ≤ x k} :=
    integrableOn_of_continuousAt hSp hKc (fun x hx => tendsto_finsetSum Finset.univ fun j _ =>
      tendsto_finsetSum Finset.univ fun l _ =>
        ((hTp j l).continuousAt (Up.isOpen.mem_nhds (hUp x (hφU hx.2) hx.1))).mul
          (hφs j l).continuous.continuousAt)
      fun x _ hx => by simp [hφ0 x hx]
  set f := fun x => ∑ j, ∑ l, glue k Tm Tp x j l * φ x j l with hf
  have hfm : EqOn f (fun x => ∑ j, ∑ l, Tm x j l * φ x j l) {x : MinkowskiModel d | x k < 0} :=
    fun x hx => by simp [hf, glue, show x k < 0 from hx]
  have hfp : EqOn f (fun x => ∑ j, ∑ l, Tp x j l * φ x j l) {x : MinkowskiModel d | 0 ≤ x k} :=
    fun x hx => by simp [hf, glue, not_lt.mpr (show 0 ≤ x k from hx)]
  have hint : Integrable f := by
    rw [← integrableOn_univ]
    have hu : (univ : Set (MinkowskiModel d)) = {x | x k < 0} ∪ {x | 0 ≤ x k} := by
      ext x
      simp [lt_or_ge]
    rw [hu]
    exact ((hTm_int.mono_set hsubm).congr_fun hfm.symm hmeasm).union
      (hTp_int.congr_fun hfp.symm hSp.measurableSet)
  have hnull : volume {x : MinkowskiModel d | x k = 0} = 0 := volume_hyperplane k 0
  have hae : {x : MinkowskiModel d | 0 ≤ x k} =ᵐ[volume] {x | 0 < x k} := by
    refine ae_eq_set.mpr ⟨measure_mono_null (fun x hx => ?_) hnull, ?_⟩
    · exact le_antisymm (not_lt.mp hx.2) hx.1
    · rw [sdiff_eq_empty.mpr hsubp, measure_empty]
  rw [← integral_add_compl hmeasm hint]
  have hc : {x : MinkowskiModel d | x k < 0}ᶜ = {x | 0 ≤ x k} := by
    ext x
    simp
  rw [hc, setIntegral_congr_fun hmeasm hfm, setIntegral_congr_fun hSp.measurableSet hfp,
    setIntegral_congr_set hae]

end Junction


/-! ### Regularity of the glued metric -/

section Regularity

variable (k : Fin (d + 1))

/-- A continuous linear functional on the model is determined by its values on the basis. -/
theorem clm_ext_single {L L' : MinkowskiModel d →L[ℝ] ℝ}
    (h : ∀ j, L (Pi.single j 1) = L' (Pi.single j 1)) : L = L' := by
  ext v
  rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, h]

/-- The closed half-space `x^k ≥ 0` has unique derivatives. -/
theorem uniqueDiffOn_upper : UniqueDiffOn ℝ {x : MinkowskiModel d | 0 ≤ x k} := by
  refine uniqueDiffOn_convex ?_ ⟨Pi.single k 1, ?_⟩
  · intro x hx y hy a b ha hb hab
    change 0 ≤ (a • x + b • y) k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  · refine interior_maximal (t := {x : MinkowskiModel d | 0 < x k}) (fun x hx => le_of_lt
      (show 0 < x k from hx)) (isOpen_lt continuous_const (continuous_apply k)) ?_
    show (0 : ℝ) < (Pi.single k 1 : MinkowskiModel d) k
    simp

/-- The closed half-space `x^k ≤ 0` has unique derivatives. -/
theorem uniqueDiffOn_lower : UniqueDiffOn ℝ {x : MinkowskiModel d | x k ≤ 0} := by
  refine uniqueDiffOn_convex ?_ ⟨-Pi.single k 1, ?_⟩
  · intro x hx y hy a b ha hb hab
    change (a • x + b • y) k ≤ 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
      (mul_nonpos_of_nonneg_of_nonpos hb hy)
  · refine interior_maximal (t := {x : MinkowskiModel d | x k < 0}) (fun x hx => le_of_lt
      (show x k < 0 from hx)) (isOpen_lt (continuous_apply k) continuous_const) ?_
    show (-Pi.single k 1 : MinkowskiModel d) k < 0
    simp

/-- **Gluing two `C¹` functions along a hyperplane.** Let `f` be `C¹` on an open set containing
the points of `U` with `x^k ≥ 0` and `g` on one containing those with `x^k ≤ 0`, equal on the
hyperplane. The glued function is `C¹` on `U` exactly when the normal derivatives `∂_k f` and
`∂_k g` agree on the hyperplane. -/
theorem contDiffOn_glue_iff {f g : MinkowskiModel d → ℝ} {U Of Og : Set (MinkowskiModel d)}
    (hU : IsOpen U) (hOf : IsOpen Of) (hOg : IsOpen Og) (hf : ContDiffOn ℝ 1 f Of)
    (hg : ContDiffOn ℝ 1 g Og) (hUf : ∀ x ∈ U, 0 ≤ x k → x ∈ Of)
    (hUg : ∀ x ∈ U, x k ≤ 0 → x ∈ Og) (hfg : ∀ y ∈ U, y k = 0 → f y = g y) :
    ContDiffOn ℝ 1 (fun x => if x k < 0 then g x else f x) U ↔
      ∀ z ∈ U, z k = 0 → fderiv ℝ f z (Pi.single k 1) = fderiv ℝ g z (Pi.single k 1) := by
  set F : MinkowskiModel d → ℝ := fun x => if x k < 0 then g x else f x with hF
  have hdf {x : MinkowskiModel d} (hx : x ∈ Of) : DifferentiableAt ℝ f x :=
    (hf.differentiableOn one_ne_zero).differentiableAt (hOf.mem_nhds hx)
  have hdg {x : MinkowskiModel d} (hx : x ∈ Og) : DifferentiableAt ℝ g x :=
    (hg.differentiableOn one_ne_zero).differentiableAt (hOg.mem_nhds hx)
  have hFf : EqOn F f {x | 0 ≤ x k} := fun x hx => by
    simp [hF, not_lt.mpr (show 0 ≤ x k from hx)]
  have hFg : EqOn F g ({x : MinkowskiModel d | x k ≤ 0} ∩ U) := fun x hx => by
    rcases (show x k ≤ 0 from hx.1).lt_or_eq with h | h
    · simp [hF, h]
    · simp [hF, h, hfg x hx.2 h]
  -- at a point of the hyperplane the one-sided derivatives are those of `f` and `g`
  have hwf {z : MinkowskiModel d} (hz : z ∈ U) (hzk : 0 ≤ z k) :
      HasFDerivWithinAt F (fderiv ℝ f z) {x | 0 ≤ x k} z :=
    (hdf (hUf z hz hzk)).hasFDerivAt.hasFDerivWithinAt.congr hFf (hFf hzk)
  have hwg {z : MinkowskiModel d} (hz : z ∈ U) (hzk : z k ≤ 0) :
      HasFDerivWithinAt F (fderiv ℝ g z) {x | x k ≤ 0} z :=
    (hasFDerivWithinAt_inter (hU.mem_nhds hz)).mp
      ((hdg (hUg z hz hzk)).hasFDerivAt.hasFDerivWithinAt.congr hFg (hFg ⟨hzk, hz⟩))
  constructor
  · intro hC z hz hzk
    have hD : HasFDerivAt F (fderiv ℝ F z) z :=
      ((hC.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    have e1 := (uniqueDiffOn_upper k z (show 0 ≤ z k from hzk.ge)).eq hD.hasFDerivWithinAt
      (hwf hz hzk.ge)
    have e2 := (uniqueDiffOn_lower k z (show z k ≤ 0 from hzk.le)).eq hD.hasFDerivWithinAt
      (hwg hz hzk.le)
    rw [← e1, ← e2]
  · intro hn
    -- on the hyperplane the two derivatives agree
    have heq {z : MinkowskiModel d} (hz : z ∈ U) (hzk : z k = 0) :
        fderiv ℝ f z = fderiv ℝ g z := by
      refine clm_ext_single fun j => ?_
      by_cases hj : j = k
      · subst hj
        exact hn z hz hzk
      · exact fderiv_eq_of_eqOn_hyperplane k (hU.inter (hOf.inter hOg)) ⟨hz,
          hUf z hz hzk.ge, hUg z hz hzk.le⟩ hzk (fun y hy hyk => hfg y hy.1 hyk)
          (hdf (hUf z hz hzk.ge)) (hdg (hUg z hz hzk.le)) hj
    have hderiv {z : MinkowskiModel d} (hz : z ∈ U) :
        HasFDerivAt F (if z k < 0 then fderiv ℝ g z else fderiv ℝ f z) z := by
      rcases lt_trichotomy (z k) 0 with h | h | h
      · simp only [h, ↓reduceIte]
        refine (hdg (hUg z hz h.le)).hasFDerivAt.congr_of_eventuallyEq ?_
        filter_upwards [(isOpen_lt (continuous_apply k) continuous_const).mem_nhds h] with y hy
        simp [hF, show y k < 0 from hy]
      · simp only [h, lt_irrefl, ↓reduceIte]
        have hu := (hwf hz h.ge).union (heq hz h ▸ hwg hz h.le)
        have hset : {x : MinkowskiModel d | 0 ≤ x k} ∪ {x | x k ≤ 0} = univ := by
          ext x
          simp [le_total]
        rw [hset, hasFDerivWithinAt_univ] at hu
        exact hu
      · simp only [not_lt.mpr h.le, ↓reduceIte]
        refine (hdf (hUf z hz h.le)).hasFDerivAt.congr_of_eventuallyEq ?_
        filter_upwards [(isOpen_lt continuous_const (continuous_apply k)).mem_nhds h] with y hy
        simp [hF, not_lt.mpr (show 0 < y k from hy).le]
    have hfd {z : MinkowskiModel d} (hz : z ∈ U) :
        fderiv ℝ F z = if z k < 0 then fderiv ℝ g z else fderiv ℝ f z := (hderiv hz).fderiv
    have hcf := hf.continuousOn_fderiv_of_isOpen hOf le_rfl
    have hcg := hg.continuousOn_fderiv_of_isOpen hOg le_rfl
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun z hz => (hderiv hz).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    intro z hz
    refine ContinuousAt.continuousWithinAt ?_
    have hup : ContinuousWithinAt (fderiv ℝ F) {x | 0 ≤ x k} z := by
      by_cases hzk : 0 ≤ z k
      · refine (continuousWithinAt_inter (hU.mem_nhds hz)).mp ?_
        refine ((hcf.continuousAt (hOf.mem_nhds (hUf z hz hzk))).continuousWithinAt.congr
          (fun y hy => ?_) ?_)
        · rw [hfd hy.2]
          rcases (show 0 ≤ y k from hy.1).lt_or_eq with h | h
          · simp [not_lt.mpr h.le]
          · simp [← h]
        · rw [hfd hz]
          simp [not_lt.mpr hzk]
      · refine continuousWithinAt_of_notMem_closure ?_
        rw [(isClosed_le continuous_const (continuous_apply k)).closure_eq]
        exact hzk
    have hlow : ContinuousWithinAt (fderiv ℝ F) {x | x k ≤ 0} z := by
      by_cases hzk : z k ≤ 0
      · refine (continuousWithinAt_inter (hU.mem_nhds hz)).mp ?_
        refine ((hcg.continuousAt (hOg.mem_nhds (hUg z hz hzk))).continuousWithinAt.congr
          (fun y hy => ?_) ?_)
        · rw [hfd hy.2]
          rcases (show y k ≤ 0 from hy.1).lt_or_eq with h | h
          · simp [h]
          · simp [h, heq hy.2 h]
        · rw [hfd hz]
          rcases hzk.lt_or_eq with h | h
          · simp [h]
          · simp [h, heq hz h]
      · refine continuousWithinAt_of_notMem_closure ?_
        rw [(isClosed_le (continuous_apply k) continuous_const).closure_eq]
        exact hzk
    have hu := hup.union hlow
    have hset : {x : MinkowskiModel d | 0 ≤ x k} ∪ {x | x k ≤ 0} = univ := by
      ext x
      simp [le_total]
    rwa [hset, continuousWithinAt_univ] at hu

variable {σ : LorentzConvention} {Um Up : Opens (MinkowskiModel d)}
  (gm : CoordinateMetric σ d Um) (gp : CoordinateMetric σ d Up)

/-- **The glued metric is `C¹` exactly when the normal derivatives agree.** -/
theorem contDiffOn_glue_coefficient_iff {U : Set (MinkowskiModel d)} (hU : IsOpen U)
    (hUm : ∀ x ∈ U, x k ≤ 0 → x ∈ Um) (hUp : ∀ x ∈ U, 0 ≤ x k → x ∈ Up)
    (hcont : ∀ y ∈ U, y k = 0 → gm.coefficient y = gp.coefficient y) :
    (∀ p q, ContDiffOn ℝ 1 (fun x => glue k gm.coefficient gp.coefficient x p q) U) ↔
      ∀ z ∈ U, z k = 0 → ∀ p q, fderiv ℝ (fun x => gp.coefficient x p q) z (Pi.single k 1) =
        fderiv ℝ (fun x => gm.coefficient x p q) z (Pi.single k 1) := by
  have h (p q : Fin (d + 1)) := contDiffOn_glue_iff k hU Up.isOpen Um.isOpen
    ((gp.coefficient_contDiffOn p q).of_le (by simp))
    ((gm.coefficient_contDiffOn p q).of_le (by simp)) hUp hUm
    (fun y hy hyk => (congrFun (congrFun (hcont y hy hyk) p) q).symm)
  have hg (p q : Fin (d + 1)) : (fun x => glue k gm.coefficient gp.coefficient x p q) =
      fun x => if x k < 0 then gm.coefficient x p q else gp.coefficient x p q := by
    funext x
    simp only [glue]
    split_ifs <;> rfl
  simp only [hg, h]
  exact ⟨fun H z hz hzk p q => H p q z hz hzk, fun H p q z hz hzk => H z hz hzk p q⟩

/-- **`C¹` exactly when the second fundamental forms agree.** For metrics continuous across the
hyperplane, with `∂_k` the unit normal there (`g_{kμ} = ε δ_{kμ}`, `ε² = 1`) and equal normal
derivatives `∂_k g_{kμ}` of the components along the normal (which a co-ordinate change can
always arrange, as in Gaussian normal co-ordinates where `g_{kμ} = ε δ_{kμ}` near the
hyperplane), the glued metric is `C¹` on the collar if and only if the second fundamental forms
agree on the hyperplane. -/
theorem contDiffOn_glue_iff_secondFundamental {U : Set (MinkowskiModel d)} (hU : IsOpen U)
    (hUm : ∀ x ∈ U, x k ≤ 0 → x ∈ Um) (hUp : ∀ x ∈ U, 0 ≤ x k → x ∈ Up)
    {ε : ℝ} (hε : ε * ε = 1)
    (hcont : ∀ y ∈ U, y k = 0 → gm.coefficient y = gp.coefficient y)
    (hnormal : ∀ y ∈ U, y k = 0 → ∀ μ, gp.coefficient y k μ = if μ = k then ε else 0)
    (hgauge : ∀ z ∈ U, z k = 0 → ∀ μ,
      fderiv ℝ (fun x => gp.coefficient x k μ) z (Pi.single k 1) =
        fderiv ℝ (fun x => gm.coefficient x k μ) z (Pi.single k 1)) :
    (∀ p q, ContDiffOn ℝ 1 (fun x => glue k gm.coefficient gp.coefficient x p q) U) ↔
      ∀ z ∈ U, z k = 0 → gp.secondFundamental k 1 z = gm.secondFundamental k 1 z := by
  rw [contDiffOn_glue_coefficient_iff k gm gp hU hUm hUp hcont]
  have habs {z : MinkowskiModel d} (hz : z ∈ U) (hzk : z k = 0) :
      Real.sqrt |gp.coefficient z k k| = 1 := by
    rw [hnormal z hz hzk k]
    simp only [↓reduceIte]
    have : |ε| = 1 := by
      have h1 : |ε| * |ε| = 1 := by rw [← abs_mul, hε, abs_one]
      nlinarith [abs_nonneg ε]
    rw [this, Real.sqrt_one]
  have hsymm {U' : Opens (MinkowskiModel d)} (g' : CoordinateMetric σ d U')
      {z : MinkowskiModel d} (hz' : z ∈ U') (p q : Fin (d + 1)) :
      fderiv ℝ (fun y => g'.coefficient y p q) z = fderiv ℝ (fun y => g'.coefficient y q p) z := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [U'.isOpen.mem_nhds hz'] with y hy using g'.coefficient_symmetric hy p q
  constructor
  · intro H z hz hzk
    ext a b
    rw [secondFundamental_apply, secondFundamental_apply, hcont z hz hzk, H z hz hzk]
  · intro H z hz hzk p q
    have hzp := hUp z hz hzk.ge
    have hzm := hUm z hz hzk.le
    by_cases hp : p = k
    · subst hp
      exact hgauge z hz hzk q
    · by_cases hq : q = k
      · subst hq
        rw [hsymm gp hzp, hsymm gm hzm]
        exact hgauge z hz hzk p
      · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hp
        obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hq
        have h := congrFun (congrFun (H z hz hzk) a) b
        rw [secondFundamental_apply, secondFundamental_apply, hcont z hz hzk, habs hz hzk] at h
        have h2 : (1 : ℝ) / (2 * 1) ≠ 0 := by norm_num
        exact mul_left_cancel₀ h2 h

end Regularity

end ProjectAinos.SmoothGeometry.CoordinateMetric
