/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.RadiationReaction
public import ProjectAinos.Electrodynamics.RadiationReaction.WorldTube.FieldExpansion
public import ProjectAinos.Electrodynamics.RadiationReaction.WorldTube.Potential
public import ProjectAinos.SmoothGeometry.Euclidean.SphereIntegral
import Mathlib.Tactic

/-!
# The force of Lorentz and Dirac from Dirac's world tube

Landau–Lifshitz, *The Classical Theory of Fields*, §76, after Dirac (1938), with `c = 1`, the
signature `(−+++)` and the units with `div E = ρ` of `lorentzDiracForce`. A point charge `e`
moves on a world line `z(τ)` of class `C⁴` in the proper time (`ProperWorldline`) and carries
its retarded field of Liénard and Wiechert (`retardedField`), the curvature of the four-potential
`A_μ = (e/4π) u_μ/ρ` at the retarded time (`fieldTensor_lwPotential`).

**Dirac's tube** of radius `ε` is the set of the events `z(τ) + ε N(τ, n)`, where
`N(τ, n) = restFrame (u(τ)) n` (`tubeNormal`) runs over the unit sphere of the rest space of
`u(τ)` as `n` runs over the unit sphere `S²` of `ℝ³`; between the proper times `τ₁ < τ₂` its
caps are the balls of radius `ε` in the rest spaces of `u(τ₁)` and `u(τ₂)`. The outward unit
normal of the side is `N`, and its three-volume element is `ε² (1 + ε N · a) dτ dσ(n)` with the
surface measure `σ` of `S²`: the boost `restFrame u` maps `ℝ³` isometrically onto the rest space
of `u` (`minkowskiForm_restFrame`), so that the tangent vectors `ε restFrame u m`, `m ⊥ n`, of the
sphere are orthogonal to `N` and `u`, and the point of the tube moves with a velocity `V`
orthogonal to `N` whose component along `u` is `1 + ε N · a` (`tube_velocity`). The four-momentum
that flows out of the tube through its side is (`diracTubeFlux`)

  `P(ε) = ∫_{τ₁}^{τ₂} ∫_{S²} ε² (1 + ε N · a) T^μ{}_ν N^ν (z(τ) + εN) dσ dτ`.

* **The expansion of the flux** (`diracTubeFlux_expansion`):
  `P(ε) = ∫_{τ₁}^{τ₂} ((e²/8πε) a − g) dτ + O(ε)`, with the force of Lorentz and Dirac
  `g = lorentzDiracForce e u`; the electromagnetic mass is `e²/(8πε)`, the energy of the field
  of Coulomb outside the radius `ε` (`emMass`). In the form of the Schott balance
  (`diracTubeFlux_expansion_schott`, from `integral_lorentzDirac_eq`):
  `P(ε) = (e²/8πε)[u] − (2/3)(e²/4π)[u̇] + ∫ (2/3)(e²/4π)(u̇ · u̇) u dτ + O(ε)`.
  The angular integrals use only that `N` is odd in `n` (`integral_tubeIntegrandMain`); the
  remainder is uniform by `tubeIntegrand_expansion`.
* **The equation of motion** (`lorentzDirac_of_tubeBalance`): if a bare particle of mass
  `m₀(ε)` on `z` exchanges four-momentum with the field so that the balance
  `m₀(ε)(u(τ₂) − u(τ₁)) = ∫ F_ext dτ − P(ε)` holds up to a defect that tends to `0` as
  `ε → 0`, for all `τ₁ ≤ τ₂`, and the observed mass `m = m₀(ε) + e²/(8πε)` is fixed, then
  `m u̇ = F_ext + g`. The exact balance for all small `ε` is a special case
  (`lorentzDirac_of_exactTubeBalance`; it holds in uniform motion, `exactTubeBalance_inertial`),
  and conversely every solution of the equation of Lorentz
  and Dirac satisfies the balance up to `O(ε)` (`tubeBalance_of_lorentzDirac`), so that the
  hypothesis holds for every world line with `F_ext = m u̇ − g`.
* **Checks**: in uniform motion (`ProperWorldline.inertial`) the retarded field is the boosted
  field of Coulomb and the flux through the tube vanishes exactly for every `ε`
  (`diracTubeFlux_inertial`); in hyperbolic motion (`ProperWorldline.hyperbolic`) the flux is
  the electromagnetic mass term alone up to `O(ε)` (`diracTubeFlux_hyperbolic`), while the
  radiated four-momentum does not vanish (`integral_radiatedMomentumRate_hyperbolic_ne_zero`).

Not proved here: the conservation law `∂_ν T^{μν} = 0` off the world line and the divergence
theorem that would derive the balance for an extended source; the balance is the stated premise
of the bare particle model.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory Asymptotics Metric
open scoped Topology

namespace ProjectAinos.Electrodynamics.RadiationReaction.WorldTube

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity SmoothGeometry.Sphere

local notation "η" => minkowskiForm LorentzConvention.timeNegative 3

/-! ### Dirac's tube and the flux through its side -/

/-- The outward unit normal `N(τ, n)` of Dirac's tube: the unit vector of the rest space of
`u(τ)` with the spatial direction `n`. -/
def tubeNormal (w : ProperWorldline) (τ : ℝ) (n : Space 3) : Spacetime := restFrame (w.vel τ) n

/-- The integrand `ε² (1 + ε N · a) T^μ{}_ν N^ν` of the flux through Dirac's tube at the point
`z(τ) + ε N(τ, n)`. -/
def tubeIntegrand (e : ℝ) (w : ProperWorldline) (ε τ : ℝ) (n : Space 3) : Spacetime :=
  (ε ^ 2 * (1 + ε * η (tubeNormal w τ n) (w.acc τ))) •
    stressFlux (retardedField e w (w.z τ + ε • tubeNormal w τ n)) (tubeNormal w τ n)

/-- **The four-momentum flowing out through the side of Dirac's tube** of radius `ε` between the
proper times `τ₁` and `τ₂`. -/
def diracTubeFlux (e : ℝ) (w : ProperWorldline) (ε τ₁ τ₂ : ℝ) : Spacetime :=
  ∫ τ in τ₁..τ₂, ∫ n : sphere (0 : Space 3) 1, tubeIntegrand e w ε τ n ∂sphereMeasure

/-- The electromagnetic mass `e²/(8πε)` of a charge of radius `ε`. -/
def emMass (e ε : ℝ) : ℝ := e ^ 2 / (8 * Real.pi * ε)

theorem minkowskiForm_tubeNormal_vel (w : ProperWorldline) (τ : ℝ) (n : Space 3) :
    η (tubeNormal w τ n) (w.vel τ) = 0 :=
  minkowskiForm_restFrame_vel (w.vel_unit τ) (w.vel_future τ) n

theorem minkowskiForm_tubeNormal_self (w : ProperWorldline) (τ : ℝ) {n : Space 3}
    (hn : ‖n‖ = 1) : η (tubeNormal w τ n) (tubeNormal w τ n) = 1 := by
  rw [tubeNormal, minkowskiForm_restFrame_self (w.vel_unit τ) (w.vel_future τ), hn, one_pow]

theorem tubeNormal_neg (w : ProperWorldline) (τ : ℝ) (n : Space 3) :
    tubeNormal w τ (-n) = -tubeNormal w τ n :=
  restFrame_neg _ _

theorem continuous_tubeNormal (w : ProperWorldline) :
    Continuous (fun p : ℝ × Space 3 => tubeNormal w p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  have h := continuousAt_restFrame (w.vel_future p.1) p.2
  have hf : ContinuousAt (fun q : ℝ × Space 3 => (w.vel q.1, q.2)) p :=
    ((w.continuous_vel.comp continuous_fst).prodMk continuous_snd).continuousAt
  have h2 := h.comp_of_eq hf rfl
  simp only [Function.comp_def] at h2
  exact h2

/-- The normals over `[τ₁, τ₂]` are bounded. -/
theorem exists_bound_tubeNormal (w : ProperWorldline) (τ₁ τ₂ : ℝ) :
    ∃ B, ∀ τ ∈ Icc τ₁ τ₂, ∀ n ∈ sphere (0 : Space 3) 1, ‖tubeNormal w τ n‖ ≤ B := by
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc.prod (isCompact_sphere (0 : Space 3) 1)) (continuous_tubeNormal w).continuousOn
  exact ⟨B, fun τ hτ n hn => hB (τ, n) ⟨hτ, hn⟩⟩

/-! ### The geometry of the tube -/

/-- The boost of the spatial vectors to the rest frame of `u` is an isometry:
`restFrame u m · restFrame u n = ⟨m, n⟩`. -/
theorem minkowskiForm_restFrame {u : Spacetime} (hu : η u u = -1) (hu0 : 0 < u 0)
    (m n : Space 3) : η (restFrame u m) (restFrame u n) = inner ℝ m n := by
  have hq := hu
  rw [minkowski_eq_time_space, real_inner_self_eq_norm_sq] at hq
  rw [minkowski_eq_time_space, restFrame, restFrame, vector_zero, vector_zero, space_vector,
    space_vector, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
    inner_smul_right, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm m (space u)]
  have h1 : (1 + u 0) ≠ 0 := by linarith
  have hn : ‖space u‖ ^ 2 = u 0 ^ 2 - 1 := by linarith
  simp only [RCLike.conj_to_real]
  rw [hn]
  field_simp
  ring

/-- The normal moves differentiably along the tube. -/
theorem differentiableAt_tubeNormal (w : ProperWorldline) (τ : ℝ) (n : Space 3) :
    DifferentiableAt ℝ (fun t => tubeNormal w t n) τ := by
  have hv : DifferentiableAt ℝ w.vel τ := (w.hasDerivAt_vel τ).differentiableAt
  have hs : DifferentiableAt ℝ (fun t => space (w.vel t)) τ :=
    (space : Spacetime →L[ℝ] Space 3).differentiableAt.comp τ hv
  have hi : DifferentiableAt ℝ (fun t => inner ℝ (space (w.vel t)) n) τ :=
    hs.inner ℝ (differentiableAt_const n)
  have h0 : DifferentiableAt ℝ (fun t => w.vel t 0) τ :=
    (ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ).differentiableAt.comp τ hv
  have hc : DifferentiableAt ℝ (fun t => (1 + w.vel t 0)⁻¹) τ :=
    ((differentiableAt_const 1).add h0).inv (by
      simp only [Pi.add_apply]; linarith [w.vel_future τ])
  have hx : DifferentiableAt ℝ (fun t => n + ((1 + w.vel t 0)⁻¹ * inner ℝ (space (w.vel t)) n) •
      space (w.vel t)) τ := (differentiableAt_const n).add ((hc.mul hi).smul hs)
  rw [differentiableAt_pi]
  intro μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simpa [tubeNormal, restFrame] using hi
  · simp only [tubeNormal, restFrame, vector_succ]
    exact (EuclideanSpace.proj i : Space 3 →L[ℝ] ℝ).differentiableAt.comp τ hx

/-- **The motion of the tube**: the velocity `V = u + ε Ṅ` of the point `z(τ) + ε N(τ, n)` of
Dirac's tube is orthogonal to the normal `N`, and its component along `u` is `1 + ε N · a`;
with the tangent vectors `ε restFrame u m`, `m ⊥ n`, of the sphere, which are orthogonal to `N`
and `u` (`minkowskiForm_restFrame`, `minkowskiForm_restFrame_vel`), `N` is the unit normal of
the side and its three-volume element is `ε² (1 + ε N · a) dτ dσ(n)`. -/
theorem tube_velocity (w : ProperWorldline) (ε τ : ℝ) {n : Space 3} (hn : ‖n‖ = 1) :
    ∃ V, HasDerivAt (fun t => w.z t + ε • tubeNormal w t n) V τ ∧
      η V (tubeNormal w τ n) = 0 ∧
      -η V (w.vel τ) = 1 + ε * η (tubeNormal w τ n) (w.acc τ) := by
  have hN := (differentiableAt_tubeNormal w τ n).hasDerivAt
  set N' := deriv (fun t => tubeNormal w t n) τ
  refine ⟨w.vel τ + ε • N', (w.hasDerivAt_z τ).add (hN.const_smul ε), ?_, ?_⟩
  · have h1 : HasDerivAt (fun t => η (tubeNormal w t n) (tubeNormal w t n))
        (η N' (tubeNormal w τ n) + η (tubeNormal w τ n) N') τ :=
      ((minkowskiForm .timeNegative 3).hasFDerivAt.comp_hasDerivAt τ hN).clm_apply hN
    have hc : (fun t => η (tubeNormal w t n) (tubeNormal w t n)) = fun _ => 1 :=
      funext fun t => minkowskiForm_tubeNormal_self w t hn
    rw [hc] at h1
    have h2 := h1.unique (hasDerivAt_const τ 1)
    rw [minkowskiForm_symmetric _ (tubeNormal w τ n) N'] at h2
    have h3 : η N' (tubeNormal w τ n) = 0 := by linarith
    rw [map_add, add_apply, map_smul, smul_apply, smul_eq_mul, minkowskiForm_symmetric _ (w.vel τ),
      minkowskiForm_tubeNormal_vel, h3]
    ring
  · have h1 : HasDerivAt (fun t => η (tubeNormal w t n) (w.vel t))
        (η N' (w.vel τ) + η (tubeNormal w τ n) (w.acc τ)) τ :=
      ((minkowskiForm .timeNegative 3).hasFDerivAt.comp_hasDerivAt τ hN).clm_apply
        (w.hasDerivAt_vel τ)
    have hc : (fun t => η (tubeNormal w t n) (w.vel t)) = fun _ => 0 :=
      funext fun t => minkowskiForm_tubeNormal_vel w t n
    rw [hc] at h1
    have h2 := h1.unique (hasDerivAt_const τ 0)
    have h3 : η N' (w.vel τ) = -η (tubeNormal w τ n) (w.acc τ) := by linarith
    rw [map_add, add_apply, map_smul, smul_apply, smul_eq_mul, w.vel_unit, h3]
    ring

/-- The uniform expansion of the integrand over `[τ₁, τ₂] × S²`, with the retarded time of every
point of the tube. -/
theorem tubeIntegrand_bound (e : ℝ) (w : ProperWorldline) (τ₁ τ₂ : ℝ) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∀ τ ∈ Icc τ₁ τ₂, ∀ n ∈ sphere (0 : Space 3) 1,
      w.IsRetarded (w.z τ + ε • tubeNormal w τ n)
        (w.retardedProperTime (w.z τ + ε • tubeNormal w τ n)) ∧
      ‖tubeIntegrand e w ε τ n -
        (e / (4 * Real.pi)) ^ 2 • tubeIntegrandMain w ε τ (tubeNormal w τ n)‖ ≤ C * ε := by
  obtain ⟨B, hB⟩ := exists_bound_tubeNormal w τ₁ τ₂
  obtain ⟨C, ε₀, hε₀, h⟩ := tubeIntegrand_expansion e w τ₁ τ₂ B
  refine ⟨C, ε₀, hε₀, fun ε hε τ hτ n hn => ?_⟩
  have hn1 : ‖n‖ = 1 := by simpa using hn
  exact h ε hε τ hτ _ (minkowskiForm_tubeNormal_self w τ hn1) (minkowskiForm_tubeNormal_vel w τ n)
    (hB τ hτ n hn)

/-- **The integrand is continuous** on `[τ₁, τ₂] × S²` when every point of the tube has a
retarded time. -/
theorem continuousOn_tubeIntegrand (e : ℝ) (w : ProperWorldline) {ε τ₁ τ₂ : ℝ}
    (hret : ∀ τ ∈ Icc τ₁ τ₂, ∀ n ∈ sphere (0 : Space 3) 1,
      w.IsRetarded (w.z τ + ε • tubeNormal w τ n)
        (w.retardedProperTime (w.z τ + ε • tubeNormal w τ n))) :
    ContinuousOn (fun p : ℝ × Space 3 => tubeIntegrand e w ε p.1 p.2)
      (Icc τ₁ τ₂ ×ˢ sphere (0 : Space 3) 1) := by
  set X : ℝ × Space 3 → Spacetime := fun p => w.z p.1 + ε • tubeNormal w p.1 p.2 with hX
  have hXc : Continuous X :=
    (w.continuous_z.comp continuous_fst).add ((continuous_tubeNormal w).const_smul ε)
  set T : ℝ × Space 3 → ℝ := fun p => w.retardedProperTime (X p) with hT
  set R : ℝ × Space 3 → Spacetime := fun p => X p - w.z (T p) with hR
  set U : ℝ × Space 3 → Spacetime := fun p => w.vel (T p) with hU
  set Acc : ℝ × Space 3 → Spacetime := fun p => w.acc (T p) with hAcc
  set Y : ℝ × Space 3 → Spacetime := fun p => lwVector e (R p) (U p) (Acc p) with hY
  set N : ℝ × Space 3 → Spacetime := fun p => tubeNormal w p.1 p.2 with hN
  set G : ℝ × Space 3 → Spacetime := fun p =>
    (ε ^ 2 * (1 + ε * η (N p) (w.acc p.1))) • ((η (R p) (N p) * η (Y p) (Y p)) • R p -
      η (R p) (Y p) • (η (Y p) (N p) • R p + η (R p) (N p) • Y p) +
        (1 / 2 * η (R p) (Y p) ^ 2) • N p) with hG
  have heq : EqOn (fun p : ℝ × Space 3 => tubeIntegrand e w ε p.1 p.2) G
      (Icc τ₁ τ₂ ×ˢ sphere (0 : Space 3) 1) := by
    intro p hp
    have hr := hret p.1 hp.1 p.2 hp.2
    simp only [tubeIntegrand, hG, retardedField]
    rw [stressFlux_bivector hr.1]
  refine ContinuousOn.congr ?_ heq
  intro p hp
  have hr := hret p.1 hp.1 p.2 hp.2
  have hTc : ContinuousAt T p :=
    ContinuousAt.comp_of_eq (g := w.retardedProperTime) (f := X)
      (ProperWorldline.continuousAt_retardedProperTime hr) hXc.continuousAt rfl
  have hRc : ContinuousAt R p := hXc.continuousAt.sub (w.continuous_z.continuousAt.comp hTc)
  have hUc : ContinuousAt U p := w.continuous_vel.continuousAt.comp hTc
  have hAc : ContinuousAt Acc p := w.continuous_acc.continuousAt.comp hTc
  have hNc : ContinuousAt N p := (continuous_tubeNormal w).continuousAt
  have hρ : -η (R p) (U p) ≠ 0 := (ProperWorldline.retardedDistance_pos hr).ne'
  have hη : ∀ {f g : ℝ × Space 3 → Spacetime}, ContinuousAt f p → ContinuousAt g p →
      ContinuousAt (fun q => η (f q) (g q)) p := fun hf hg =>
    ((minkowskiForm .timeNegative 3).continuous.continuousAt.comp hf).clm_apply hg
  have hρc : ContinuousAt (fun q => -η (R q) (U q)) p := (hη hRc hUc).neg
  have hYc : ContinuousAt Y p := by
    simp only [hY, lwVector]
    exact ((((hρc.pow 2).inv₀ (pow_ne_zero 2 hρ)).smul hAc).add
      (((continuousAt_const.add (hη hRc hAc)).div (hρc.pow 3) (pow_ne_zero 3 hρ)).smul
        hUc)).const_smul (-(e / (4 * Real.pi)))
  have hGc : ContinuousAt G p := by
    simp only [hG]
    refine (continuousAt_const.mul (continuousAt_const.add (continuousAt_const.mul
      (hη hNc (w.continuous_acc.continuousAt.comp continuous_fst.continuousAt))))).smul ?_
    exact ((((hη hRc hNc).mul (hη hYc hYc)).smul hRc).sub ((hη hRc hYc).smul
      (((hη hYc hNc).smul hRc).add ((hη hRc hNc).smul hYc)))).add
      ((continuousAt_const.mul ((hη hRc hYc).pow 2)).smul hNc)
  exact hGc.continuousWithinAt

/-- A function continuous on `[τ₁, τ₂] × S²` has an interval integrable integral over `S²`. -/
theorem intervalIntegrable_integral_sphere {f : ℝ → Space 3 → Spacetime} {τ₁ τ₂ : ℝ}
    (h : τ₁ ≤ τ₂) (hf : ContinuousOn (fun p : ℝ × Space 3 => f p.1 p.2)
      (Icc τ₁ τ₂ ×ˢ sphere (0 : Space 3) 1)) :
    IntervalIntegrable (fun τ => ∫ n : sphere (0 : Space 3) 1, f τ n ∂sphereMeasure) volume
      τ₁ τ₂ := by
  set g : ℝ × sphere (0 : Space 3) 1 → Spacetime := fun q => f (projIcc τ₁ τ₂ h q.1) q.2 with hg
  have hgc : Continuous g := by
    have hm : Continuous fun q : ℝ × sphere (0 : Space 3) 1 =>
        ((projIcc τ₁ τ₂ h q.1 : ℝ), (q.2 : Space 3)) :=
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd)
    have := hf.comp_continuous hm (fun q => ⟨(projIcc τ₁ τ₂ h q.1).2, q.2.2⟩)
    exact this
  have hc := continuous_parametric_integral_of_continuous (μ := sphereMeasure)
    (f := fun τ (n : sphere (0 : Space 3) 1) => g (τ, n)) hgc isCompact_univ
  simp only [Measure.restrict_univ] at hc
  refine (hc.intervalIntegrable τ₁ τ₂).congr fun τ hτ => ?_
  have hτ' : τ ∈ Icc τ₁ τ₂ := by
    rw [uIoc_of_le h] at hτ
    exact ⟨hτ.1.le, hτ.2⟩
  simp only [hg, projIcc_of_mem h hτ']

/-- A function continuous on `[τ₁, τ₂] × S²` is integrable on `S²` at each `τ ∈ [τ₁, τ₂]`. -/
theorem integrable_sphere_of_continuousOn {f : ℝ → Space 3 → Spacetime} {τ₁ τ₂ τ : ℝ}
    (hf : ContinuousOn (fun p : ℝ × Space 3 => f p.1 p.2) (Icc τ₁ τ₂ ×ˢ sphere (0 : Space 3) 1))
    (hτ : τ ∈ Icc τ₁ τ₂) :
    Integrable (fun n : sphere (0 : Space 3) 1 => f τ n) sphereMeasure := by
  have hc : Continuous fun n : sphere (0 : Space 3) 1 => f τ n := by
    have := hf.comp_continuous (f := fun n : sphere (0 : Space 3) 1 => (τ, (n : Space 3)))
      (continuous_const.prodMk continuous_subtype_val) (fun n => ⟨hτ, n.2⟩)
    exact this
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **The angular integral of the leading terms**: the terms odd in `N` drop out, and
`∫ (−N/(2ε²) + a/(2ε) + (A/2) N + (2/3) A u − (3/4) α a − (2/3) ȧ) dσ
 = 4π (a/(2ε) + (2/3) A u − (2/3) ȧ)`. -/
theorem integral_tubeIntegrandMain (w : ProperWorldline) (ε τ : ℝ) :
    ∫ n : sphere (0 : Space 3) 1, tubeIntegrandMain w ε τ (tubeNormal w τ n) ∂sphereMeasure =
      (4 * Real.pi) • ((1 / (2 * ε)) • w.acc τ +
        (2 / 3 * η (w.acc τ) (w.acc τ)) • w.vel τ - (2 / 3 : ℝ) • w.jerk τ) := by
  set A := η (w.acc τ) (w.acc τ)
  set O : Space 3 → Spacetime := fun m => (A / 2 - 1 / (2 * ε ^ 2)) • tubeNormal w τ m -
    (3 / 4 * η (tubeNormal w τ m) (w.acc τ)) • w.acc τ with hO
  set c : Spacetime := (1 / (2 * ε)) • w.acc τ + (2 / 3 * A) • w.vel τ - (2 / 3 : ℝ) • w.jerk τ
  have hsplit : ∀ n : sphere (0 : Space 3) 1,
      tubeIntegrandMain w ε τ (tubeNormal w τ n) = O n + c := fun n => by
    simp only [tubeIntegrandMain, hO, c, A]
    module
  have hOc : Continuous O := by
    have hN0 := (continuous_tubeNormal w).comp
      ((continuous_const (y := τ)).prodMk (continuous_id (X := Space 3)))
    have hN : Continuous fun m : Space 3 => tubeNormal w τ m := hN0
    have h1 : Continuous fun m : Space 3 => η (tubeNormal w τ m) (w.acc τ) :=
      ((minkowskiForm .timeNegative 3).continuous.comp hN).clm_apply continuous_const
    have h2 : Continuous fun m : Space 3 => (3 / 4 * η (tubeNormal w τ m) (w.acc τ)) • w.acc τ :=
      (continuous_const.mul h1).smul continuous_const
    exact (hN.const_smul (A / 2 - 1 / (2 * ε ^ 2))).sub h2
  have hOi : Integrable (fun n : sphere (0 : Space 3) 1 => O n) sphereMeasure :=
    (hOc.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hodd : ∫ n : sphere (0 : Space 3) 1, O n ∂sphereMeasure = 0 :=
    integral_eq_zero_of_odd (f := O) fun m => by
      simp only [hO, tubeNormal_neg, map_neg, neg_apply, smul_neg]
      module
  simp only [hsplit]
  rw [integral_add hOi (integrable_const c), hodd, integral_const, sphereMeasure_real_univ,
    zero_add]

/-- The force of Lorentz and Dirac along the world line. -/
theorem lorentzDiracForce_vel (e : ℝ) (w : ProperWorldline) (τ : ℝ) :
    lorentzDiracForce e w.vel τ = (2 / 3 * (e ^ 2 / (4 * Real.pi))) •
      (w.jerk τ - η (w.acc τ) (w.acc τ) • w.vel τ) :=
  lorentzDiracForce_eq_of_unit e (w.contDiff_vel.of_le (by norm_num)) w.vel_unit τ

theorem continuous_lorentzDiracForce_vel (e : ℝ) (w : ProperWorldline) :
    Continuous (lorentzDiracForce e w.vel) := by
  have h : lorentzDiracForce e w.vel = fun τ => (2 / 3 * (e ^ 2 / (4 * Real.pi))) •
      (w.jerk τ - η (w.acc τ) (w.acc τ) • w.vel τ) := funext (lorentzDiracForce_vel e w)
  rw [h]
  exact (w.continuous_jerk.sub ((((minkowskiForm .timeNegative 3).continuous.comp
    w.continuous_acc).clm_apply w.continuous_acc).smul w.continuous_vel)).const_smul
      (2 / 3 * (e ^ 2 / (4 * Real.pi)))

/-- The angular integral of the leading terms of the integrand is
`(e²/8πε) a − g` with the force of Lorentz and Dirac `g`. -/
theorem integral_tubeIntegrandMain_eq (e : ℝ) (w : ProperWorldline) {ε : ℝ} (hε : ε ≠ 0)
    (τ : ℝ) :
    ∫ n : sphere (0 : Space 3) 1, (e / (4 * Real.pi)) ^ 2 •
      tubeIntegrandMain w ε τ (tubeNormal w τ n) ∂sphereMeasure =
      emMass e ε • w.acc τ - lorentzDiracForce e w.vel τ := by
  rw [integral_smul, integral_tubeIntegrandMain, lorentzDiracForce_vel, emMass]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  funext μ
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/-! ### The expansion of the flux -/

/-- **The flux through Dirac's tube** (Landau–Lifshitz §76, Dirac 1938): for `τ₁ ≤ τ₂` there
are `C` and `ε₀ > 0` with
`‖P(ε) − ∫_{τ₁}^{τ₂} ((e²/8πε) a − g) dτ‖ ≤ C ε` for `0 < ε < ε₀`, where `g` is the force of
Lorentz and Dirac. -/
theorem diracTubeFlux_expansion (e : ℝ) (w : ProperWorldline) {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀,
      ‖diracTubeFlux e w ε τ₁ τ₂ -
        ∫ τ in τ₁..τ₂, (emMass e ε • w.acc τ - lorentzDiracForce e w.vel τ)‖ ≤ C * ε := by
  obtain ⟨C, ε₀, hε₀, hb⟩ := tubeIntegrand_bound e w τ₁ τ₂
  refine ⟨4 * Real.pi * C * (τ₂ - τ₁), ε₀, hε₀, fun ε hε => ?_⟩
  have hret : ∀ τ ∈ Icc τ₁ τ₂, ∀ n ∈ sphere (0 : Space 3) 1, _ := fun τ hτ n hn =>
    (hb ε hε τ hτ n hn).1
  have hcont := continuousOn_tubeIntegrand e w hret
  have hmc : Continuous fun τ => emMass e ε • w.acc τ - lorentzDiracForce e w.vel τ :=
    (w.continuous_acc.const_smul (emMass e ε)).sub (continuous_lorentzDiracForce_vel e w)
  have hmainc : ContinuousOn (fun p : ℝ × Space 3 =>
      (e / (4 * Real.pi)) ^ 2 • tubeIntegrandMain w ε p.1 (tubeNormal w p.1 p.2))
      (Icc τ₁ τ₂ ×ˢ sphere (0 : Space 3) 1) := by
    have hN := continuous_tubeNormal w
    have hη : Continuous fun p : ℝ × Space 3 => η (tubeNormal w p.1 p.2) (w.acc p.1) :=
      ((minkowskiForm .timeNegative 3).continuous.comp hN).clm_apply
        (w.continuous_acc.comp continuous_fst)
    have hA : Continuous fun p : ℝ × Space 3 => η (w.acc p.1) (w.acc p.1) :=
      ((minkowskiForm .timeNegative 3).continuous.comp (w.continuous_acc.comp
        continuous_fst)).clm_apply (w.continuous_acc.comp continuous_fst)
    have ha := w.continuous_acc.comp (continuous_fst (X := ℝ) (Y := Space 3))
    have hu := w.continuous_vel.comp (continuous_fst (X := ℝ) (Y := Space 3))
    have hj := w.continuous_jerk.comp (continuous_fst (X := ℝ) (Y := Space 3))
    have hc : Continuous fun p : ℝ × Space 3 => tubeIntegrandMain w ε p.1 (tubeNormal w p.1 p.2) :=
      ((hN.const_smul (-(1 / (2 * ε ^ 2)))).add (ha.const_smul (1 / (2 * ε)))).add
        (((((hA.div_const 2).smul hN).add ((continuous_const.mul hA).smul hu)).sub
          ((continuous_const.mul hη).smul ha)).sub (hj.const_smul (2 / 3 : ℝ)))
    exact (hc.const_smul ((e / (4 * Real.pi)) ^ 2)).continuousOn
  have hpt : ∀ τ ∈ Icc τ₁ τ₂, ‖(∫ n : sphere (0 : Space 3) 1, tubeIntegrand e w ε τ n
      ∂sphereMeasure) - (emMass e ε • w.acc τ - lorentzDiracForce e w.vel τ)‖ ≤
        C * ε * (4 * Real.pi) := by
    intro τ hτ
    rw [← integral_tubeIntegrandMain_eq e w hε.1.ne' τ, ← integral_sub
      (integrable_sphere_of_continuousOn hcont hτ)
      (integrable_sphere_of_continuousOn (f := fun τ n => (e / (4 * Real.pi)) ^ 2 •
        tubeIntegrandMain w ε τ (tubeNormal w τ n)) hmainc hτ)]
    have hn := norm_integral_le_of_norm_le_const (μ := sphereMeasure)
      (Eventually.of_forall fun n : sphere (0 : Space 3) 1 => (hb ε hε τ hτ n n.2).2)
    rwa [sphereMeasure_real_univ] at hn
  rw [diracTubeFlux, ← intervalIntegral.integral_sub (intervalIntegrable_integral_sphere h hcont)
    (hmc.intervalIntegrable τ₁ τ₂)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ => hpt τ ?_).trans_eq ?_
  · rw [uIoc_of_le h] at hτ
    exact ⟨hτ.1.le, hτ.2⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- **The flux in the form of the balance of Schott**:
`P(ε) = (e²/8πε)(u(τ₂) − u(τ₁)) − (2/3)(e²/4π)(u̇(τ₂) − u̇(τ₁)) + ∫ (2/3)(e²/4π)(u̇ · u̇) u dτ
 + O(ε)`: the electromagnetic mass, the change of the term of Schott and the radiated
four-momentum. -/
theorem diracTubeFlux_expansion_schott (e : ℝ) (w : ProperWorldline) {τ₁ τ₂ : ℝ}
    (h : τ₁ ≤ τ₂) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀,
      ‖diracTubeFlux e w ε τ₁ τ₂ - (emMass e ε • (w.vel τ₂ - w.vel τ₁) -
        (2 / 3 * (e ^ 2 / (4 * Real.pi))) • (w.acc τ₂ - w.acc τ₁) +
          ∫ τ in τ₁..τ₂, radiatedMomentumRate e w.vel τ)‖ ≤ C * ε := by
  obtain ⟨C, ε₀, hε₀, hb⟩ := diracTubeFlux_expansion e w h
  refine ⟨C, ε₀, hε₀, fun ε hε => ?_⟩
  have hint : ∫ τ in τ₁..τ₂, (emMass e ε • w.acc τ - lorentzDiracForce e w.vel τ) =
      emMass e ε • (w.vel τ₂ - w.vel τ₁) - ((2 / 3 * (e ^ 2 / (4 * Real.pi))) •
        (w.acc τ₂ - w.acc τ₁) - ∫ τ in τ₁..τ₂, radiatedMomentumRate e w.vel τ) := by
    have i1 : IntervalIntegrable (fun τ => emMass e ε • w.acc τ) volume τ₁ τ₂ :=
      (w.continuous_acc.const_smul (emMass e ε)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub i1
      ((continuous_lorentzDiracForce_vel e w).intervalIntegrable _ _),
      intervalIntegral.integral_smul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => w.hasDerivAt_vel t)
        (w.continuous_acc.intervalIntegrable _ _),
      integral_lorentzDirac_eq e (w.contDiff_vel.of_le (by norm_num)) w.vel_unit]
    rfl
  have e2 : emMass e ε • (w.vel τ₂ - w.vel τ₁) - (2 / 3 * (e ^ 2 / (4 * Real.pi))) •
      (w.acc τ₂ - w.acc τ₁) + ∫ τ in τ₁..τ₂, radiatedMomentumRate e w.vel τ =
      ∫ τ in τ₁..τ₂, (emMass e ε • w.acc τ - lorentzDiracForce e w.vel τ) := by
    rw [hint]
    abel
  rw [e2]
  exact hb ε hε

/-! ### The equation of motion from the balance of four-momentum -/

/-- The defect `m₀(ε)(u(τ₂) − u(τ₁)) − ∫ F_ext dτ + P(ε)` of the balance of four-momentum of a
bare particle of mass `m₀(ε)` on the world line with the field outside Dirac's tube. -/
def tubeBalanceDefect (e : ℝ) (w : ProperWorldline) (m₀ : ℝ → ℝ) (Fext : ℝ → Spacetime)
    (ε τ₁ τ₂ : ℝ) : Spacetime :=
  m₀ ε • (w.vel τ₂ - w.vel τ₁) - (∫ τ in τ₁..τ₂, Fext τ) + diracTubeFlux e w ε τ₁ τ₂

/-- With the observed mass `m = m₀(ε) + e²/(8πε)`, the defect of the balance is
`m [u] − ∫ (F_ext + g) dτ` up to `O(ε)`. -/
theorem tubeBalanceDefect_expansion (e m : ℝ) (w : ProperWorldline) {Fext : ℝ → Spacetime}
    (hF : Continuous Fext) {m₀ : ℝ → ℝ} (hm : ∀ ε, 0 < ε → m₀ ε + emMass e ε = m)
    {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀,
      ‖tubeBalanceDefect e w m₀ Fext ε τ₁ τ₂ - (m • (w.vel τ₂ - w.vel τ₁) -
        ∫ τ in τ₁..τ₂, (Fext τ + lorentzDiracForce e w.vel τ))‖ ≤ C * ε := by
  obtain ⟨C, ε₀, hε₀, hb⟩ := diracTubeFlux_expansion e w h
  refine ⟨C, ε₀, hε₀, fun ε hε => ?_⟩
  have i1 : IntervalIntegrable (fun τ => emMass e ε • w.acc τ) volume τ₁ τ₂ :=
    (w.continuous_acc.const_smul (emMass e ε)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (lorentzDiracForce e w.vel) volume τ₁ τ₂ :=
    (continuous_lorentzDiracForce_vel e w).intervalIntegrable τ₁ τ₂
  have hmain : ∫ τ in τ₁..τ₂, (emMass e ε • w.acc τ - lorentzDiracForce e w.vel τ) =
      emMass e ε • (w.vel τ₂ - w.vel τ₁) - ∫ τ in τ₁..τ₂, lorentzDiracForce e w.vel τ := by
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_smul (μ := volume),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => w.hasDerivAt_vel t)
        (w.continuous_acc.intervalIntegrable _ _)]
  have hFl : ∫ τ in τ₁..τ₂, (Fext τ + lorentzDiracForce e w.vel τ) =
      (∫ τ in τ₁..τ₂, Fext τ) + ∫ τ in τ₁..τ₂, lorentzDiracForce e w.vel τ :=
    intervalIntegral.integral_add (hF.intervalIntegrable _ _) i2
  have e1 : tubeBalanceDefect e w m₀ Fext ε τ₁ τ₂ - (m • (w.vel τ₂ - w.vel τ₁) -
      ∫ τ in τ₁..τ₂, (Fext τ + lorentzDiracForce e w.vel τ)) =
      diracTubeFlux e w ε τ₁ τ₂ -
        ∫ τ in τ₁..τ₂, (emMass e ε • w.acc τ - lorentzDiracForce e w.vel τ) := by
    rw [tubeBalanceDefect, hmain, hFl, ← hm ε hε.1, add_smul]
    abel
  rw [e1]
  exact hb ε hε

/-- `m (u(τ₂) − u(τ₁)) = ∫_{τ₁}^{τ₂} (F_ext + g) dτ` for all `τ₁ ≤ τ₂` gives `m u̇ = F_ext + g`. -/
theorem eq_of_integral_eq (e m : ℝ) (w : ProperWorldline) {Fext : ℝ → Spacetime}
    (hF : Continuous Fext)
    (h : ∀ τ₁ τ₂, τ₁ ≤ τ₂ → m • (w.vel τ₂ - w.vel τ₁) =
      ∫ τ in τ₁..τ₂, (Fext τ + lorentzDiracForce e w.vel τ)) (τ : ℝ) :
    m • w.acc τ = Fext τ + lorentzDiracForce e w.vel τ := by
  have hc : Continuous fun τ => Fext τ + lorentzDiracForce e w.vel τ :=
    hF.add (continuous_lorentzDiracForce_vel e w)
  have hd := (hc.integral_hasStrictDerivAt (τ - 1) τ).hasDerivAt
  have hl : HasDerivAt (fun s => m • (w.vel s - w.vel (τ - 1))) (m • w.acc τ) τ := by
    exact ((w.hasDerivAt_vel τ).sub_const (w.vel (τ - 1))).const_smul m
  have hev : (fun s => m • (w.vel s - w.vel (τ - 1))) =ᶠ[𝓝 τ]
      fun s => ∫ x in (τ - 1)..s, (Fext x + lorentzDiracForce e w.vel x) := by
    filter_upwards [lt_mem_nhds (show τ - 1 < τ by linarith)] with s hs
    exact h (τ - 1) s hs.le
  exact hl.unique (hd.congr_of_eventuallyEq hev)

/-- **The equation of Lorentz and Dirac from the balance through Dirac's tube** (Landau–Lifshitz
§76): if the bare particle of mass `m₀(ε)`, with the observed mass `m = m₀(ε) + e²/(8πε)` fixed,
balances its four-momentum with the flux through the side of the tube,
`m₀(ε)(u(τ₂) − u(τ₁)) = ∫ F_ext dτ − P(ε)`, up to a defect that tends to `0` as `ε → 0⁺`, for
all `τ₁ ≤ τ₂`, then `m u̇ = F_ext + g` with the force of Lorentz and Dirac `g`. -/
theorem lorentzDirac_of_tubeBalance (e m : ℝ) (w : ProperWorldline) {Fext : ℝ → Spacetime}
    (hF : Continuous Fext) {m₀ : ℝ → ℝ} (hm : ∀ ε, 0 < ε → m₀ ε + emMass e ε = m)
    (hbal : ∀ τ₁ τ₂, τ₁ ≤ τ₂ →
      Tendsto (fun ε => tubeBalanceDefect e w m₀ Fext ε τ₁ τ₂) (𝓝[>] 0) (𝓝 0))
    (τ : ℝ) : m • w.acc τ = Fext τ + lorentzDiracForce e w.vel τ := by
  refine eq_of_integral_eq e m w hF (fun τ₁ τ₂ h => ?_) τ
  obtain ⟨C, ε₀, hε₀, hb⟩ := tubeBalanceDefect_expansion e m w hF hm h
  set K : Spacetime := m • (w.vel τ₂ - w.vel τ₁) -
    ∫ τ in τ₁..τ₂, (Fext τ + lorentzDiracForce e w.vel τ) with hK
  have hR : Tendsto (fun ε => tubeBalanceDefect e w m₀ Fext ε τ₁ τ₂ - K) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) by
      simpa using (tendsto_nhdsWithin_of_tendsto_nhds (continuous_const.mul continuous_id
        |>.tendsto 0) : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 (C * 0))))
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε using hb ε hε
  have hK0 : Tendsto (fun _ : ℝ => K) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (hbal τ₁ τ₂ h).sub hR
    simpa using this
  have hK' : K = 0 := tendsto_nhds_unique tendsto_const_nhds hK0
  rw [hK, sub_eq_zero] at hK'
  exact hK'

/-- **The exact balance**: if `m₀(ε)(u(τ₂) − u(τ₁)) = ∫ F_ext dτ − P(ε)` for all small `ε > 0` and
all `τ₁ ≤ τ₂`, with `m = m₀(ε) + e²/(8πε)` fixed, then `m u̇ = F_ext + g`. -/
theorem lorentzDirac_of_exactTubeBalance (e m : ℝ) (w : ProperWorldline) {Fext : ℝ → Spacetime}
    (hF : Continuous Fext) {m₀ : ℝ → ℝ} (hm : ∀ ε, 0 < ε → m₀ ε + emMass e ε = m) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀)
    (hbal : ∀ ε ∈ Ioo 0 ε₀, ∀ τ₁ τ₂, τ₁ ≤ τ₂ →
      m₀ ε • (w.vel τ₂ - w.vel τ₁) = (∫ τ in τ₁..τ₂, Fext τ) - diracTubeFlux e w ε τ₁ τ₂)
    (τ : ℝ) : m • w.acc τ = Fext τ + lorentzDiracForce e w.vel τ := by
  refine lorentzDirac_of_tubeBalance e m w hF hm (fun τ₁ τ₂ h => ?_) τ
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  rw [tubeBalanceDefect, hbal ε hε τ₁ τ₂ h]
  abel

/-- **Conversely**, along a solution of the equation of Lorentz and Dirac `m u̇ = F_ext + g` the
balance through Dirac's tube holds up to `O(ε)`; in particular the hypothesis of
`lorentzDirac_of_tubeBalance` holds for every world line with `F_ext = m u̇ − g`. -/
theorem tubeBalance_of_lorentzDirac (e m : ℝ) (w : ProperWorldline) {Fext : ℝ → Spacetime}
    (hF : Continuous Fext) {m₀ : ℝ → ℝ} (hm : ∀ ε, 0 < ε → m₀ ε + emMass e ε = m)
    (heq : ∀ τ, m • w.acc τ = Fext τ + lorentzDiracForce e w.vel τ) {τ₁ τ₂ : ℝ}
    (h : τ₁ ≤ τ₂) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ‖tubeBalanceDefect e w m₀ Fext ε τ₁ τ₂‖ ≤ C * ε := by
  obtain ⟨C, ε₀, hε₀, hb⟩ := tubeBalanceDefect_expansion e m w hF hm h
  refine ⟨C, ε₀, hε₀, fun ε hε => ?_⟩
  have hint : ∫ τ in τ₁..τ₂, (Fext τ + lorentzDiracForce e w.vel τ) =
      m • (w.vel τ₂ - w.vel τ₁) := by
    simp only [← heq]
    rw [intervalIntegral.integral_smul, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => w.hasDerivAt_vel t) (w.continuous_acc.intervalIntegrable _ _)]
  have := hb ε hε
  rwa [hint, sub_self, sub_zero] at this

/-- **The balance through Dirac's tube is equivalent to the equation of Lorentz and Dirac**:
for a continuous external force and a fixed observed mass, the defect of the balance tends to
`0` for all `τ₁ ≤ τ₂` exactly when `m u̇ = F_ext + g`. -/
theorem tubeBalance_iff_lorentzDirac (e m : ℝ) (w : ProperWorldline) {Fext : ℝ → Spacetime}
    (hF : Continuous Fext) {m₀ : ℝ → ℝ} (hm : ∀ ε, 0 < ε → m₀ ε + emMass e ε = m) :
    (∀ τ₁ τ₂, τ₁ ≤ τ₂ →
      Tendsto (fun ε => tubeBalanceDefect e w m₀ Fext ε τ₁ τ₂) (𝓝[>] 0) (𝓝 0)) ↔
      ∀ τ, m • w.acc τ = Fext τ + lorentzDiracForce e w.vel τ := by
  refine ⟨fun hbal => lorentzDirac_of_tubeBalance e m w hF hm hbal, fun heq τ₁ τ₂ h => ?_⟩
  obtain ⟨C, ε₀, hε₀, hb⟩ := tubeBalance_of_lorentzDirac e m w hF hm heq h
  refine squeeze_zero_norm' ?_ (show Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds (continuous_const.mul continuous_id
      |>.tendsto 0) : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 (C * 0))))
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε using hb ε hε

/-! ### Uniform motion -/

theorem hasDerivAt_inertial (z₀ u₀ : Spacetime) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => z₀ + τ • u₀) u₀ τ := by
  simpa using ((hasDerivAt_id τ).smul_const u₀).const_add z₀

/-- The **uniform motion** `z(τ) = z₀ + τ u₀` with a future unit timelike four-velocity `u₀`. -/
def ProperWorldline.inertial (z₀ u₀ : Spacetime) (hu : η u₀ u₀ = -1) (hu0 : 0 < u₀ 0) :
    ProperWorldline where
  z τ := z₀ + τ • u₀
  contDiff_z := contDiff_const.add (contDiff_id.smul contDiff_const)
  unit τ := by rw [(hasDerivAt_inertial z₀ u₀ τ).deriv]; exact hu
  future τ := by rw [(hasDerivAt_inertial z₀ u₀ τ).deriv]; exact hu0

theorem ProperWorldline.inertial_vel (z₀ u₀ : Spacetime) (hu : η u₀ u₀ = -1) (hu0 : 0 < u₀ 0) :
    (ProperWorldline.inertial z₀ u₀ hu hu0).vel = fun _ => u₀ :=
  funext fun τ => (hasDerivAt_inertial z₀ u₀ τ).deriv

theorem ProperWorldline.inertial_acc (z₀ u₀ : Spacetime) (hu : η u₀ u₀ = -1) (hu0 : 0 < u₀ 0) :
    (ProperWorldline.inertial z₀ u₀ hu hu0).acc = fun _ => 0 := by
  funext τ
  simp only [ProperWorldline.acc, ProperWorldline.inertial_vel, deriv_const]

/-- **In uniform motion the flux through Dirac's tube vanishes** for every radius: the retarded
field is the boosted field of Coulomb, whose integrand `−(e/4π)² N/(2ε²)` is odd on the
sphere. -/
theorem diracTubeFlux_inertial (e : ℝ) (z₀ u₀ : Spacetime) (hu : η u₀ u₀ = -1)
    (hu0 : 0 < u₀ 0) {ε : ℝ} (hε : 0 < ε) (τ₁ τ₂ : ℝ) :
    diracTubeFlux e (ProperWorldline.inertial z₀ u₀ hu hu0) ε τ₁ τ₂ = 0 := by
  set w := ProperWorldline.inertial z₀ u₀ hu hu0 with hw
  have hvel : ∀ τ, w.vel τ = u₀ := fun τ => congrFun (ProperWorldline.inertial_vel z₀ u₀ hu hu0) τ
  have hacc : ∀ τ, w.acc τ = 0 := fun τ => congrFun (ProperWorldline.inertial_acc z₀ u₀ hu hu0) τ
  have hpt : ∀ τ (n : sphere (0 : Space 3) 1),
      tubeIntegrand e w ε τ n = (-((e / (4 * Real.pi)) ^ 2 / (2 * ε ^ 2))) • tubeNormal w τ n := by
    intro τ n
    set N := tubeNormal w τ n with hN
    have hNN : η N N = 1 := minkowskiForm_tubeNormal_self w τ (by simp)
    have hNu : η N u₀ = 0 := by rw [← hvel τ]; exact minkowskiForm_tubeNormal_vel w τ n
    have huN : η u₀ N = 0 := by rw [minkowskiForm_symmetric]; exact hNu
    set x := w.z τ + ε • N with hx
    have hX : x - w.z (τ - ε) = ε • (N + u₀) := by
      simp only [hx, hw, ProperWorldline.inertial, smul_add, sub_smul]
      abel
    have hnull : η (x - w.z (τ - ε)) (x - w.z (τ - ε)) = 0 := by
      rw [hX]
      simp only [map_smul, map_add, smul_apply, add_apply, smul_eq_mul, hNN, hNu, huN, hu]
      ring
    have hneg : η (x - w.z (τ - ε)) (w.vel τ) < 0 := by
      rw [hX, hvel]
      simp only [map_smul, map_add, smul_apply, add_apply, smul_eq_mul, hNu, hu]
      linarith
    have hret : w.IsRetarded x (τ - ε) := ⟨hnull, by
      have := pos_time_of_null_of_neg hnull (w.vel_unit τ) (w.vel_future τ) hneg
      simpa using this⟩
    have hτr := ProperWorldline.retardedProperTime_eq hret
    simp only [tubeIntegrand, retardedField]
    rw [← hN, ← hx, hτr, stressFlux_bivector hret.1, hX, hvel, hacc, hacc]
    simp only [lwVector, map_smul, map_add, map_zero, smul_apply, add_apply,
      smul_eq_mul, smul_zero, zero_add, add_zero, mul_zero, hNN, hNu, huN, hu]
    have hε0 : ε ≠ 0 := hε.ne'
    funext μ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hzero : ∀ τ, ∫ n : sphere (0 : Space 3) 1, tubeIntegrand e w ε τ n ∂sphereMeasure = 0 :=
    fun τ => by
      simp only [hpt]
      exact integral_eq_zero_of_odd
        (f := fun m => (-((e / (4 * Real.pi)) ^ 2 / (2 * ε ^ 2))) • tubeNormal w τ m)
        fun m => by rw [tubeNormal_neg, smul_neg]
  simp only [diracTubeFlux, hzero, intervalIntegral.integral_zero]

/-- **An instance of the exact balance**: in uniform motion without an external force, the
balance `m₀(ε)(u(τ₂) − u(τ₁)) = ∫ F_ext dτ − P(ε)` holds for every bare mass and every radius. -/
theorem exactTubeBalance_inertial (e : ℝ) (z₀ u₀ : Spacetime) (hu : η u₀ u₀ = -1)
    (hu0 : 0 < u₀ 0) (m₀ : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (τ₁ τ₂ : ℝ) :
    m₀ ε • ((ProperWorldline.inertial z₀ u₀ hu hu0).vel τ₂ -
      (ProperWorldline.inertial z₀ u₀ hu hu0).vel τ₁) =
      (∫ _ in τ₁..τ₂, (0 : Spacetime)) -
        diracTubeFlux e (ProperWorldline.inertial z₀ u₀ hu hu0) ε τ₁ τ₂ := by
  rw [diracTubeFlux_inertial e z₀ u₀ hu hu0 hε, ProperWorldline.inertial_vel]
  simp

/-! ### Hyperbolic motion -/

theorem contDiff_hyperbola : ContDiff ℝ 4 Examples.hyperbola := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact Real.contDiff_sinh
  · exact Real.contDiff_cosh
  · exact contDiff_const
  · exact contDiff_const

/-- The **hyperbolic motion** `z(τ) = (sinh τ, cosh τ, 0, 0)` of uniform proper acceleration `1`. -/
def ProperWorldline.hyperbolic : ProperWorldline where
  z := Examples.hyperbola
  contDiff_z := contDiff_hyperbola
  unit τ := by rw [Examples.hyperbola_deriv]; exact minkowskiForm_hyperbolaVelocity τ
  future τ := by
    rw [Examples.hyperbola_deriv]
    simpa [Examples.hyperbolaVelocity] using Real.cosh_pos τ

theorem ProperWorldline.hyperbolic_vel :
    ProperWorldline.hyperbolic.vel = Examples.hyperbolaVelocity :=
  funext Examples.hyperbola_deriv

/-- **In hyperbolic motion the finite part of the flux vanishes**: the flux through Dirac's tube
is the electromagnetic mass term `(e²/8πε)(u(τ₂) − u(τ₁))` up to `O(ε)`, since the force of
Lorentz and Dirac vanishes (`lorentzDiracForce_hyperbolaVelocity`). -/
theorem diracTubeFlux_hyperbolic (e : ℝ) {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀,
      ‖diracTubeFlux e ProperWorldline.hyperbolic ε τ₁ τ₂ - emMass e ε •
        (Examples.hyperbolaVelocity τ₂ - Examples.hyperbolaVelocity τ₁)‖ ≤ C * ε := by
  obtain ⟨C, ε₀, hε₀, hb⟩ := diracTubeFlux_expansion e ProperWorldline.hyperbolic h
  refine ⟨C, ε₀, hε₀, fun ε hε => ?_⟩
  have hint : ∫ τ in τ₁..τ₂, (emMass e ε • ProperWorldline.hyperbolic.acc τ -
      lorentzDiracForce e ProperWorldline.hyperbolic.vel τ) =
      emMass e ε • (Examples.hyperbolaVelocity τ₂ - Examples.hyperbolaVelocity τ₁) := by
    simp only [ProperWorldline.hyperbolic_vel, lorentzDiracForce_hyperbolaVelocity, sub_zero]
    rw [intervalIntegral.integral_smul, ← ProperWorldline.hyperbolic_vel,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => ProperWorldline.hyperbolic.hasDerivAt_vel t)
        (ProperWorldline.hyperbolic.continuous_acc.intervalIntegrable _ _)]
  rw [← hint]
  exact hb ε hε

/-- **The radiated four-momentum of hyperbolic motion is not zero**: although the force of
Lorentz and Dirac vanishes, the charge radiates `(2/3)(e²/4π)(z(τ₂) − z(τ₁)) ≠ 0`; in the
balance through the tube it is supplied by the change of the term of Schott. -/
theorem integral_radiatedMomentumRate_hyperbolic_ne_zero {e τ₁ τ₂ : ℝ} (he : e ≠ 0)
    (h : τ₁ < τ₂) :
    ∫ τ in τ₁..τ₂, radiatedMomentumRate e Examples.hyperbolaVelocity τ ≠ 0 := by
  rw [integral_radiatedMomentumRate_hyperbola]
  intro h0
  have h1 := congrFun h0 0
  simp only [Pi.smul_apply, Pi.sub_apply, Examples.hyperbola, Pi.zero_apply, smul_eq_mul] at h1
  have hs : Real.sinh τ₁ < Real.sinh τ₂ := Real.sinh_lt_sinh.mpr h
  have hk : 0 < 2 / 3 * (e ^ 2 / (4 * Real.pi)) := by positivity
  simp at h1
  rcases h1 with h1 | h1
  · exact absurd h1 he
  · linarith

end ProjectAinos.Electrodynamics.RadiationReaction.WorldTube
