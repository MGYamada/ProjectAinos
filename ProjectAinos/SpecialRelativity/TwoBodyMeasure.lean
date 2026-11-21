/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.TwoBodyFibre
public import ProjectAinos.SpecialRelativity.CrossSection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The invariant measure on the fibre of two outgoing particles

For a regular total momentum `P` with rest mass `M` (`TwoBodyFibre.region`) the measure of the
final states of two particles with the masses `m₃, m₄ ≥ 0` and the total momentum `P` is

`fibreMeasure m₃ m₄ P = (q/M) · (n ↦ fibrePair m₃ m₄ P n)_* σ`,

the image of the surface measure `σ` of the unit sphere of the rest frame, with
`q = √λ(M², m₃², m₄²)/(2M)` (Landau–Lifshitz, *The Classical Theory of Fields*, §12). The
normalization `q/M` is the one of the shell measures `d³p/E` of `FutureShell.measure`:
`lintegral_prod_eq` and `prod_eq_bind` (in `TwoBodyCoarea`) prove that the product of the two
shell measures is the integral of the measures `fibreMeasure m₃ m₄ P` over `d⁴P`.

* `fibreMeasure_univ`: the total mass is `4πq/M`; `fibreMeasure_compl_fibre`: the measure is
  carried by the fibre.
* `fibreMeasure_eq_of_apply`: the measure does not depend on the Lorentz transformation that
  brings the rest frame of `P` to the frame of the co-ordinates. Two such transformations differ
  by a rotation of the rest frame, which preserves `σ` (`Sphere.measurePreserving_sphereMap`).
* `map_fibreMeasure`: **covariance**, `L_* ν_P = ν_{LP}` for every orthochronous `L`.
* `twoBodyCrossSection_covariant`: the cross-section of a reaction with two outgoing particles,
  `(1/4F) ∫_S W dν_{p₁ + p₂}`, is invariant, for a transition weight `W` that is a Lorentz
  scalar. `exists_twoBodyCrossSection_covariant` is an instance with a nonzero boost, a positive
  flux factor and a constant weight. The weight is an input from the interaction.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace ProjectAinos.SpecialRelativity.TwoBodyFibre

open SmoothGeometry SmoothGeometry.Minkowski FutureShell

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {m₃ m₄ : ℝ} {P : MinkowskiModel 3}

/-! ### The measure -/

/-- The measure of the final states of two particles with the total momentum `P`:
`(q/M) · (n ↦ fibrePair m₃ m₄ P n)_* σ`. -/
def fibreMeasure (m₃ m₄ : ℝ) (P : MinkowskiModel 3) : Measure ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
  ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P) •
    Measure.map (fibrePair m₃ m₄ P) Sphere.sphereMeasure

theorem measurable_fibrePair_right (P : MinkowskiModel 3) : Measurable (fibrePair m₃ m₄ P) := by
  have h : Measurable fun n : sphere (0 : E3) 1 => fibrePair m₃ m₄ (P, n).1 (P, n).2 :=
    (measurable_fibrePair (m₃ := m₃) (m₄ := m₄)).comp measurable_prodMk_left
  exact h

/-- The integral against the measure of the fibre is an integral over the sphere. -/
theorem lintegral_fibreMeasure (P : MinkowskiModel 3)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(fibreMeasure m₃ m₄ P) =
      ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P) *
        ∫⁻ n, f (fibrePair m₃ m₄ P n) ∂Sphere.sphereMeasure := by
  rw [fibreMeasure, lintegral_smul_measure, lintegral_map hf (measurable_fibrePair_right P),
    smul_eq_mul]

instance (P : MinkowskiModel 3) : IsFiniteMeasure (fibreMeasure m₃ m₄ P) where
  measure_univ_lt_top := by
    rw [fibreMeasure, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem sphereMeasure_univ : Sphere.sphereMeasure univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [← Sphere.sphereMeasure_real_univ, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The total mass of the measure of the fibre is `4πq/M`. -/
theorem fibreMeasure_univ (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄) :
    fibreMeasure m₃ m₄ P univ =
      ENNReal.ofReal (4 * Real.pi * restMomentum m₃ m₄ (invariantMass P) / invariantMass P) := by
  have hq := restMomentum_pos hm₃ hm₄ (add_lt_invariantMass hm₃ hm₄ hP)
  have hM := invariantMass_pos (futureTimelike_of_mem_region hP)
  rw [fibreMeasure, Measure.smul_apply, Measure.map_apply (measurable_fibrePair_right P)
    MeasurableSet.univ, preimage_univ, sphereMeasure_univ, smul_eq_mul,
    ← ENNReal.ofReal_mul (div_nonneg hq.le hM.le)]
  congr 1
  ring

theorem measurableSet_fibre (P : MinkowskiModel 3) : MeasurableSet (fibre m₃ m₄ P) :=
  (measurableSet_domain.preimage measurable_fst).inter
    ((measurableSet_domain.preimage measurable_snd).inter
      (measurableSet_eq_fun continuous_total.measurable measurable_const))

/-- The measure of the fibre is carried by the fibre. -/
theorem fibreMeasure_compl_fibre (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄) :
    fibreMeasure m₃ m₄ P (fibre m₃ m₄ P)ᶜ = 0 := by
  rw [fibreMeasure, Measure.smul_apply, Measure.map_apply (measurable_fibrePair_right P)
    (measurableSet_fibre P).compl]
  have h : fibrePair m₃ m₄ P ⁻¹' (fibre m₃ m₄ P)ᶜ = ∅ := by
    ext n
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact fibrePair_mem_fibre hm₃ hm₄ hP n
  rw [h, measure_empty, smul_zero]

/-! ### The rotations of the rest frame -/

/-- A rotation of the frame as a linear isometry of `ℝ³`. -/
def rotationIsometry {R : LorentzGroup 3} (hR : R ∈ rotationGroup 3) : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap ∘ₗ spaceLinear R ∘ₗ
        (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
      norm_map' := fun x => by
        have h1 := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (spaceLinear R (WithLp.ofLp x)))
        have h2 := EuclideanSpace.real_norm_sq_eq x
        have h3 := sum_mul_spaceLinear hR (WithLp.ofLp x) (WithLp.ofLp x)
        simp only [← pow_two] at h3
        have hsq : ‖WithLp.toLp 2 (spaceLinear R (WithLp.ofLp x))‖ ^ 2 = ‖x‖ ^ 2 := by
          rw [h1, h2]
          exact h3
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq }
    rfl

theorem sphereVec_sphereMap {R : LorentzGroup 3} (hR : R ∈ rotationGroup 3)
    (n : sphere (0 : E3) 1) :
    sphereVec (Sphere.sphereMap (rotationIsometry hR) n) = spaceLinear R (sphereVec n) := rfl

/-- The measure of the fibre with an arbitrary Lorentz transformation `L` that maps `M e₀` to
`P` in place of `labBoost P`. -/
theorem fibreMeasure_eq_of_apply (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (L : orthochronousLorentzGroup 3) (hL : L.val.val (invariantMass P • timeAxis 3) = P) :
    fibreMeasure m₃ m₄ P =
      ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P) •
        Measure.map (fun n => (action m₃ L (restMomentum m₃ m₄ (invariantMass P) • sphereVec n),
          action m₄ L (-(restMomentum m₃ m₄ (invariantMass P) • sphereVec n))))
          Sphere.sphereMeasure := by
  have hft := futureTimelike_of_mem_region hP
  have hM := invariantMass_pos hft
  set L₀ := labBoost P with hL₀
  set R := L₀⁻¹ * L with hRdef
  have hR : R.val ∈ rotationGroup 3 := by
    change R.val.val (timeAxis 3) = timeAxis 3
    have h1 : R.val.val (invariantMass P • timeAxis 3) = invariantMass P • timeAxis 3 := by
      change L₀.val.val.symm (L.val.val (invariantMass P • timeAxis 3)) = _
      rw [hL, LinearEquiv.symm_apply_eq]
      exact (labBoost_apply_rest hft).symm
    rw [map_smul] at h1
    have h2 := congrArg (fun v : MinkowskiModel 3 => (invariantMass P)⁻¹ • v) h1
    simpa only [smul_smul, inv_mul_cancel₀ hM.ne', one_smul] using h2
  have hRo : (⟨R.val, rotationGroup_le_orthochronous hR⟩ : orthochronousLorentzGroup 3) = R :=
    Subtype.ext rfl
  have hLR : L = L₀ * R := by rw [hRdef, mul_inv_cancel_left]
  set q := restMomentum m₃ m₄ (invariantMass P)
  have hfun : (fun n => (action m₃ L (q • sphereVec n), action m₄ L (-(q • sphereVec n)))) =
      fibrePair m₃ m₄ P ∘ Sphere.sphereMap (rotationIsometry hR) := by
    funext n
    have hd₃ := mem_domain_of_ne_zero m₃ (restVec_ne_zero hm₃ hm₄ hP n)
    have hd₄ := mem_domain_of_ne_zero m₄ (neg_ne_zero.mpr (restVec_ne_zero hm₃ hm₄ hP n))
    rw [Function.comp_apply, fibrePair_eq_action hm₃ hm₄ hP, sphereVec_sphereMap, hLR,
      action_mul _ _ hd₃, action_mul _ _ hd₄, ← hRo, action_rotation_eq m₃ hR,
      action_rotation_eq m₄ hR, map_smul, map_neg, map_smul]
  rw [fibreMeasure, hfun, ← Measure.map_map (measurable_fibrePair_right P)
    (Sphere.sphereMap (rotationIsometry hR)).measurable,
    (Sphere.measurePreserving_sphereMap (rotationIsometry hR)).map_eq]

/-! ### Covariance -/

/-- **Covariance**: an orthochronous Lorentz transformation `L` maps the measure of the fibre over
`P` to the measure of the fibre over `LP`. -/
theorem map_fibreMeasure (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (hP : P ∈ region 3 m₃ m₄)
    (L : orthochronousLorentzGroup 3) :
    Measure.map (Prod.map (action m₃ L) (action m₄ L)) (fibreMeasure m₃ m₄ P) =
      fibreMeasure m₃ m₄ (L.val.val P) := by
  have hft := futureTimelike_of_mem_region hP
  have hLP := lorentz_mem_region L hP
  have hmass := invariantMass_lorentz' L P
  have happ : (L * labBoost P).val.val (invariantMass (L.val.val P) • timeAxis 3) =
      L.val.val P := by
    rw [hmass]
    change L.val.val ((labBoost P).val.val (invariantMass P • timeAxis 3)) = _
    rw [labBoost_apply_rest hft]
  rw [fibreMeasure_eq_of_apply hm₃ hm₄ hLP (L * labBoost P) happ, hmass, fibreMeasure,
    Measure.map_smul, Measure.map_map
      ((continuous_action L).prodMap (continuous_action L)).measurable
      (measurable_fibrePair_right P)]
  congr 2
  funext n
  have hd₃ := mem_domain_of_ne_zero m₃ (restVec_ne_zero hm₃ hm₄ hP n)
  have hd₄ := mem_domain_of_ne_zero m₄ (neg_ne_zero.mpr (restVec_ne_zero hm₃ hm₄ hP n))
  rw [Function.comp_apply, fibrePair_eq_action hm₃ hm₄ hP, Prod.map_apply,
    action_mul _ _ hd₃, action_mul _ _ hd₄]
  exact ((continuous_action L).prodMap (continuous_action L)).measurable.aemeasurable

/-! ### The cross-section -/

theorem action_of_notMem_domain {d : ℕ} {m : ℝ} (L : orthochronousLorentzGroup d)
    {π : Fin d → ℝ} (hπ : π ∉ domain d m) : action m L π = π := by
  have hnn : 0 ≤ m ^ 2 + ∑ i, π i ^ 2 := add_nonneg (sq_nonneg m) (sum_sq_nonneg π)
  have h0 : m ^ 2 + ∑ i, π i ^ 2 = 0 := le_antisymm (not_lt.mp hπ) hnn
  have hm : m ^ 2 = 0 := le_antisymm (by linarith [sum_sq_nonneg π]) (sq_nonneg m)
  have hπ0 : π = 0 := by
    by_contra hne
    have := sum_sq_pos hne
    linarith
  have hpt : point m π = 0 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Real.sqrt (m ^ 2 + ∑ i, π i ^ 2) = 0
      rw [h0, Real.sqrt_zero]
    · change π j = 0
      rw [hπ0, Pi.zero_apply]
  rw [action, hpt, map_zero, hπ0]
  rfl

/-- The inverse transformation undoes the action on every space momentum. -/
theorem action_inv_action' {d : ℕ} {m : ℝ} (L : orthochronousLorentzGroup d)
    (π : Fin d → ℝ) : action m L⁻¹ (action m L π) = π := by
  by_cases hπ : π ∈ domain d m
  · exact action_inv_action L hπ
  · rw [action_of_notMem_domain L hπ, action_of_notMem_domain L⁻¹ hπ]

/-- A Lorentz transformation acts on the chart of a shell by a homeomorphism. -/
def actionHomeomorph {d : ℕ} (m : ℝ) (L : orthochronousLorentzGroup d) :
    (Fin d → ℝ) ≃ₜ (Fin d → ℝ) where
  toFun := action m L
  invFun := action m L⁻¹
  left_inv := action_inv_action' L
  right_inv π := by simpa only [inv_inv] using action_inv_action' L⁻¹ π
  continuous_toFun := continuous_action L
  continuous_invFun := continuous_action L⁻¹

theorem measurableEmbedding_prodMap_action (L : orthochronousLorentzGroup 3) :
    MeasurableEmbedding (Prod.map (action m₃ L) (action m₄ L)) :=
  ((actionHomeomorph m₃ L).prodCongr (actionHomeomorph m₄ L)).measurableEmbedding

/-- The cross-section with the image measure: for a measurable embedding `φ` and a weight with
`W' ∘ φ = W`, `σ[φ_*ν, W'](φ S) = σ[ν, W](S)`. -/
theorem crossSection_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α}
    {φ : α → β} (hφ : MeasurableEmbedding φ) {W : α → ℝ} {W' : β → ℝ}
    (hW : ∀ y, W' (φ y) = W y) (F : ℝ) (S : Set α) :
    crossSection (Measure.map φ ν) W' F (φ '' S) = crossSection ν W F S := by
  rw [crossSection, crossSection, hφ.setIntegral_map, hφ.injective.preimage_image]
  simp only [hW]

/-- The cross-section of a reaction `p₁ + p₂ → p₃ + p₄`, with the measure of the fibre over the
total momentum `p₁ + p₂` as the measure of the final states. -/
def twoBodyCrossSection (m₃ m₄ : ℝ) (W : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ)
    (p₁ p₂ : MinkowskiModel 3) (S : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ))) : ℝ :=
  crossSection (fibreMeasure m₃ m₄ (p₁ + p₂)) W (fluxFactor p₁ p₂) S

/-- **The cross-section is invariant**: for an orthochronous Lorentz transformation `L` and a
transition weight that is a Lorentz scalar, the cross-section of the transformed set of final
states for the transformed incoming momenta is the cross-section of the set. -/
theorem twoBodyCrossSection_covariant (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    {p₁ p₂ : MinkowskiModel 3} (hP : p₁ + p₂ ∈ region 3 m₃ m₄) (L : orthochronousLorentzGroup 3)
    {W W' : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    (hW : ∀ x, W' (Prod.map (action m₃ L) (action m₄ L) x) = W x)
    (S : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ))) :
    twoBodyCrossSection m₃ m₄ W' (L.val.val p₁) (L.val.val p₂)
        (Prod.map (action m₃ L) (action m₄ L) '' S) =
      twoBodyCrossSection m₃ m₄ W p₁ p₂ S := by
  rw [twoBodyCrossSection, twoBodyCrossSection, ← map_add, ← map_fibreMeasure hm₃ hm₄ hP L,
    fluxFactor_lorentz]
  exact crossSection_map (measurableEmbedding_prodMap_action L) hW _ S

/-- The cross-section of all final states for a constant weight `c`:
`(1/4F) · c · 4πq/M`. -/
theorem twoBodyCrossSection_const_univ (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    {p₁ p₂ : MinkowskiModel 3} (hP : p₁ + p₂ ∈ region 3 m₃ m₄) (c : ℝ) :
    twoBodyCrossSection m₃ m₄ (fun _ => c) p₁ p₂ univ =
      (4 * fluxFactor p₁ p₂)⁻¹ * (4 * Real.pi * restMomentum m₃ m₄ (invariantMass (p₁ + p₂)) /
        invariantMass (p₁ + p₂) * c) := by
  have hq := restMomentum_pos hm₃ hm₄ (add_lt_invariantMass hm₃ hm₄ hP)
  have hM := invariantMass_pos (futureTimelike_of_mem_region hP)
  rw [twoBodyCrossSection, crossSection, Measure.restrict_univ, integral_const, smul_eq_mul,
    Measure.real, fibreMeasure_univ hm₃ hm₄ hP, ENNReal.toReal_ofReal (by positivity)]

/-- **An instance**: a target of mass `1` at rest and a projectile of mass `3` and momentum `4`
produce two particles of mass `1`. The total momentum is regular, the flux factor is positive,
the cross-section with the constant weight `1` is positive, and it is invariant under the
nonzero boost with the velocity `1/2` along the first axis. -/
theorem exists_twoBodyCrossSection_covariant :
    ∃ (p₁ p₂ : MinkowskiModel 3) (β : Velocity 3), β ≠ Velocity.zero 3 ∧
      0 < fluxFactor p₁ p₂ ∧ p₁ + p₂ ∈ region 3 1 1 ∧
      0 < twoBodyCrossSection 1 1 (fun _ => 1) p₁ p₂ univ ∧
      twoBodyCrossSection 1 1 (fun _ => 1) ((boost β).val p₁) ((boost β).val p₂)
          (Prod.map (action 1 (boostOrthochronous β)) (action 1 (boostOrthochronous β)) '' univ) =
        twoBodyCrossSection 1 1 (fun _ => 1) p₁ p₂ univ := by
  set p₁ : MinkowskiModel 3 := Fin.cons 1 (0 : Fin 3 → ℝ) with hp₁
  set p₂ : MinkowskiModel 3 := Fin.cons 5 ![4, 0, 0] with hp₂
  set β : Velocity 3 := ⟨EuclideanSpace.single 0 (1 / 2), by
    rw [EuclideanSpace.single, PiLp.norm_single]; norm_num⟩ with hβ
  have hsum : p₁ + p₂ = (Fin.cons 6 ![4, 0, 0] : MinkowskiModel 3) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hp₁, hp₂]
      norm_num
    · simp [hp₁, hp₂]
  have hreg : p₁ + p₂ ∈ region 3 1 1 := by
    rw [hsum]
    refine ⟨by simp, ?_⟩
    rw [FreeParticle.intervalQuadratic_cons, Fin.sum_univ_three]
    norm_num
  have hpair : pair p₁ p₂ = 5 := by
    rw [hp₁, hp₂, pair_cons, Fin.sum_univ_three]
    norm_num
  have hQ₁ : intervalQuadratic p₁ = 1 := by
    rw [hp₁, FreeParticle.intervalQuadratic_cons]
    simp
  have hQ₂ : intervalQuadratic p₂ = 9 := by
    rw [hp₂, FreeParticle.intervalQuadratic_cons, Fin.sum_univ_three]
    norm_num
  have hF : 0 < fluxFactor p₁ p₂ := by
    rw [fluxFactor, hpair, hQ₁, hQ₂]
    exact Real.sqrt_pos.mpr (by norm_num)
  have hone : (0 : ℝ) ≤ 1 := zero_le_one
  have hq := restMomentum_pos hone hone (add_lt_invariantMass hone hone hreg)
  have hM := invariantMass_pos (futureTimelike_of_mem_region hreg)
  refine ⟨p₁, p₂, β, ?_, hF, hreg, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun v : Velocity 3 => (v.val : EuclideanSpace ℝ (Fin 3)) 0) h
    simp [hβ, Velocity.zero] at h1
  · rw [twoBodyCrossSection_const_univ hone hone hreg]
    positivity
  · exact twoBodyCrossSection_covariant hone hone hreg (boostOrthochronous β)
      (fun _ => rfl) univ

end ProjectAinos.SpecialRelativity.TwoBodyFibre
