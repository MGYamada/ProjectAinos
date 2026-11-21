/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Diffraction.Aperture
public import ProjectAinos.SmoothGeometry.Euclidean.HalfSpaceDivergence
import Mathlib.Tactic

/-!
# Diffraction: the Green field of the half-space above a plane

The tools for the representation of a radiating solution of the Helmholtz equation by its values
on a plane `z = ε` (`Representation.lean`).

* `waveSlope k R = e^{ikR}(ikR − 1)/(4πR³)`: the gradient of the outgoing spherical wave is
  `∇G_k(q) = σ_k(|q|) q` (`fderiv_sphericalWave_apply`); `waveGrad k α q = σ_k(|q|) q_α` and
  `sum_fderiv_waveGrad`: **the Helmholtz equation of the spherical wave** away from its pole,
  `Σ_α ∂_α ∂_α G_k + k² G_k = 0`, from the radial identity `waveSlope_radial`.
* `imagePoint ε y`: the mirror image of `y` in the plane `z = ε`; `greenD k ε y` the Dirichlet
  Green function `G_k(p − y) − G_k(p − y′)` of the half-space `z > ε`, with the gradient
  `greenGrad`. On the plane it vanishes (`greenD_spacePoint`) and its normal derivative is the
  Rayleigh–Sommerfeld kernel (`greenGrad_two_spacePoint`).
* `greenField k ε y u = u ∇G − G ∇u`: `divergenceC_greenField`, **Green's field of two solutions
  of the Helmholtz equation is free of divergence**.
* `tendsto_fluxC_greenField`: the flux of Green's field through the sphere of radius `r` about
  the pole tends to `−u(y)` as `r → 0⁺`, and `fluxC_greenField_eq`: it equals `−u(y)` on every
  sphere about the pole inside the half-space.
* `norm_sum_mul_greenField_le`: the far-field bound `|Σ_α p_α (u ∂_α G − G ∂_α u)| ≤
  2C(|k|a + 1)/(π|p|²) + e/(π|p|)` from the radiation condition of `u` and of the two spherical
  waves (`norm_waveRadial_le`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology ContDiff Laplacian InnerProductSpace Real

namespace ProjectAinos.Electrodynamics.Diffraction

open ProjectAinos.SmoothGeometry.Sphere

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The calculus of the spherical wave -/

/-- The radial slope `σ_k(R) = g_k′(R)/R = e^{ikR}(ikR − 1)/(4πR³)` of the spherical wave
`g_k(R) = e^{ikR}/(4πR)`. -/
def waveSlope (k R : ℝ) : ℂ := cexp (I * k * R) * (I * k * R - 1) / (4 * π * R ^ 3)

/-- The derivative `σ_k′(R) = e^{ikR}(3 − 3ikR − k²R²)/(4πR⁴)` of the slope. -/
def waveSlopeDeriv (k R : ℝ) : ℂ :=
  cexp (I * k * R) * (3 - 3 * I * k * R - k ^ 2 * R ^ 2) / (4 * π * R ^ 4)

/-- The component `∂_α G_k(q) = σ_k(|q|) q_α` of the gradient of the spherical wave. -/
def waveGrad (k : ℝ) (α : Fin 3) (q : E3) : ℂ := waveSlope k ‖q‖ * q α

/-- The radial profile `g_k(R) = e^{ikR}/(4πR)` has the derivative `R σ_k(R)`. -/
theorem hasDerivAt_waveProfile (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt (fun R : ℝ => cexp (I * k * R) / (4 * π * R)) (R * waveSlope k R) R := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : HasDerivAt (fun R : ℝ => (4 * π * (R : ℂ))) (4 * π) R := by
    simpa using (hasDerivAt_id R).ofReal_comp.const_mul (4 * (π : ℂ))
  have h := (hasDerivAt_cexp_I_mul k R).fun_div h1 (by simp [hR', hpi])
  refine h.congr_deriv ?_
  unfold waveSlope
  field_simp

/-- The slope has the derivative `σ_k′`. -/
theorem hasDerivAt_waveSlope (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt (waveSlope k) (waveSlopeDeriv k R) R := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : HasDerivAt (fun R : ℝ => I * k * (R : ℂ) - 1) (I * k) R := by
    simpa using ((hasDerivAt_id R).ofReal_comp.const_mul (I * k)).sub_const 1
  have h2 : HasDerivAt (fun R : ℝ => (4 * π * (R : ℂ) ^ 3))
      (4 * (π : ℂ) * (3 * (R : ℂ) ^ 2)) R := by
    have := ((hasDerivAt_id R).ofReal_comp.pow 3).const_mul (4 * (π : ℂ))
    simpa using this
  have h := ((hasDerivAt_cexp_I_mul k R).fun_mul h1).fun_div h2 (by simp [hR', hpi])
  unfold waveSlope
  refine h.congr_deriv ?_
  unfold waveSlopeDeriv
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- The radial equation of the spherical wave, `3σ_k + Rσ_k′ + k² g_k = 0`: with `σ_k = g_k′/R`
it is `g_k″ + 2g_k′/R + k² g_k = 0`. -/
theorem waveSlope_radial (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    3 * waveSlope k R + R * waveSlopeDeriv k R + k ^ 2 * (cexp (I * k * R) / (4 * π * R)) =
      0 := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold waveSlope waveSlopeDeriv
  field_simp
  ring

/-- The Rayleigh–Sommerfeld profile is `−2` times the slope of the spherical wave. -/
theorem kernelProfile_eq_waveSlope (k R : ℝ) : kernelProfile k R = -2 * waveSlope k R := by
  unfold kernelProfile waveSlope
  ring

/-- The derivative of the spherical wave away from its pole. -/
theorem hasFDerivAt_sphericalWave (k : ℝ) {q : E3} (hq : q ≠ 0) :
    HasFDerivAt (sphericalWave k)
      ((‖q‖⁻¹ • innerSL ℝ q).smulRight (‖q‖ * waveSlope k ‖q‖)) q :=
  hasFDerivAt_comp_norm hq (hasDerivAt_waveProfile k (norm_ne_zero_iff.mpr hq))

/-- **The gradient of the spherical wave**, `DG_k(q)v = σ_k(|q|) ⟨q, v⟩`. -/
theorem fderiv_sphericalWave_apply (k : ℝ) {q : E3} (hq : q ≠ 0) (v : E3) :
    fderiv ℝ (sphericalWave k) q v = waveSlope k ‖q‖ * ⟪q, v⟫_ℝ := by
  have hR : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hq
  rw [(hasFDerivAt_sphericalWave k hq).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
    Complex.real_smul]
  push_cast
  field_simp

/-- The derivative of the gradient component `σ_k(|q|) q_α` away from the pole. -/
theorem hasFDerivAt_waveGrad (k : ℝ) (α : Fin 3) {q : E3} (hq : q ≠ 0) :
    HasFDerivAt (waveGrad k α)
      (waveSlope k ‖q‖ • ofRealCLM.comp (EuclideanSpace.proj α) +
        ((q α : ℝ) : ℂ) • (‖q‖⁻¹ • innerSL ℝ q).smulRight (waveSlopeDeriv k ‖q‖)) q := by
  have hR : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hc : HasFDerivAt (fun y : E3 => ((y α : ℝ) : ℂ))
      (ofRealCLM.comp (EuclideanSpace.proj α)) q :=
    (ofRealCLM.comp (EuclideanSpace.proj α)).hasFDerivAt
  exact (hasFDerivAt_comp_norm hq (hasDerivAt_waveSlope k hR)).mul hc

/-- The derivative of the gradient component along `v`:
`∂_v(σ_k(|q|) q_α) = σ_k′(|q|) ⟨q, v⟩ q_α/|q| + σ_k(|q|) v_α`. -/
theorem fderiv_waveGrad_apply (k : ℝ) (α : Fin 3) {q : E3} (hq : q ≠ 0) (v : E3) :
    fderiv ℝ (waveGrad k α) q v =
      waveSlopeDeriv k ‖q‖ * ⟪q, v⟫_ℝ / ‖q‖ * q α + waveSlope k ‖q‖ * v α := by
  rw [(hasFDerivAt_waveGrad k α hq).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, ofRealCLM_apply, smul_eq_mul,
    Complex.real_smul]
  push_cast
  ring

/-- **The spherical wave solves the Helmholtz equation** away from its pole:
`Σ_α ∂_α(σ_k(|q|) q_α) = −k² G_k(q)`. -/
theorem sum_fderiv_waveGrad (k : ℝ) {q : E3} (hq : q ≠ 0) :
    ∑ α, fderiv ℝ (waveGrad k α) q (EuclideanSpace.single α 1) =
      -(k ^ 2 : ℂ) * sphericalWave k q := by
  have hR : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hR' : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast hR
  have hsum : ((q 0 : ℂ) ^ 2 + (q 1 : ℂ) ^ 2 + (q 2 : ℂ) ^ 2) = (‖q‖ : ℂ) ^ 2 := by
    exact_mod_cast (norm_sq_eq_three q).symm
  have hrad := waveSlope_radial k hR
  simp only [fderiv_waveGrad_apply k _ hq, Fin.sum_univ_three,
    EuclideanSpace.inner_single_right, conj_trivial]
  have hRinv : (‖q‖ : ℂ) * (‖q‖ : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hR'
  simp only [sphericalWave]
  simp
  linear_combination hrad + (waveSlopeDeriv k ‖q‖ / ‖q‖) * hsum +
    (waveSlopeDeriv k ‖q‖ * ‖q‖) * hRinv

/-- The spherical wave is smooth away from its pole. -/
theorem contDiffAt_sphericalWave (k : ℝ) {q : E3} (hq : q ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (sphericalWave k) q := by
  have hR : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hq
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn : ContDiffAt ℝ n (fun y : E3 => ((‖y‖ : ℝ) : ℂ)) q :=
    ofRealCLM.contDiff.contDiffAt.comp q (contDiffAt_norm ℝ hq)
  have he : ContDiffAt ℝ n (fun y : E3 => cexp (I * k * ‖y‖)) q :=
    (contDiffAt_const.mul hn).cexp
  have hd : ContDiffAt ℝ n (fun y : E3 => (4 * π * (‖y‖ : ℂ))⁻¹) q :=
    (contDiffAt_const.mul hn).inv (by simp [hR, hpi])
  refine (he.mul hd).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [sphericalWave, div_eq_mul_inv]

/-- The gradient component of the spherical wave is smooth away from the pole. -/
theorem contDiffAt_waveGrad (k : ℝ) (α : Fin 3) {q : E3} (hq : q ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (waveGrad k α) q := by
  have hR : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hq
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn : ContDiffAt ℝ n (fun y : E3 => ((‖y‖ : ℝ) : ℂ)) q :=
    ofRealCLM.contDiff.contDiffAt.comp q (contDiffAt_norm ℝ hq)
  have hz : ContDiffAt ℝ n (fun y : E3 => ((y α : ℝ) : ℂ)) q :=
    (ofRealCLM.comp (EuclideanSpace.proj α)).contDiff.contDiffAt
  have he : ContDiffAt ℝ n (fun y : E3 => cexp (I * k * ‖y‖)) q :=
    (contDiffAt_const.mul hn).cexp
  have hd : ContDiffAt ℝ n (fun y : E3 => (4 * π * (‖y‖ : ℂ) ^ 3)⁻¹) q :=
    (contDiffAt_const.mul (hn.pow 3)).inv (by simp [hR, hpi])
  have hl : ContDiffAt ℝ n (fun y : E3 => I * k * ((‖y‖ : ℝ) : ℂ) - 1) q :=
    (contDiffAt_const.mul hn).sub contDiffAt_const
  have h := ((he.mul hl).mul hd).mul hz
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [waveGrad, waveSlope, div_eq_mul_inv]

/-- `|G_k(q)| = 1/(4π|q|)`. -/
theorem norm_sphericalWave (k : ℝ) (q : E3) : ‖sphericalWave k q‖ = 1 / (4 * π * ‖q‖) := by
  unfold sphericalWave
  rw [norm_div, norm_cexp_I_mul,
    show (4 * π * (‖q‖ : ℂ)) = ((4 * π * ‖q‖ : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-! ### The Green function of the half-space above a plane -/

/-- The mirror image `(y₁, y₂, 2ε − y₃)` of `y` in the plane `z = ε`. -/
def imagePoint (ε : ℝ) (y : E3) : E3 := !₂[y 0, y 1, 2 * ε - y 2]

/-- **The Dirichlet Green function** `G_k(p − y) − G_k(p − y′)` of the half-space `z > ε`, with
the mirror image `y′` of the pole `y` in the plane `z = ε`. -/
def greenD (k ε : ℝ) (y p : E3) : ℂ :=
  sphericalWave k (p - y) - sphericalWave k (p - imagePoint ε y)

/-- The components `∂_α G_k(p − y) − ∂_α G_k(p − y′)` of the gradient of the Green function. -/
def greenGrad (k ε : ℝ) (y : E3) (α : Fin 3) (p : E3) : ℂ :=
  waveGrad k α (p - y) - waveGrad k α (p - imagePoint ε y)

/-- **Green's field** `u ∂_α G − G ∂_α u` of a function `u` and of the Green function with the
pole `y`. -/
def greenField (k ε : ℝ) (y : E3) (u : E3 → ℂ) (α : Fin 3) (p : E3) : ℂ :=
  u p * greenGrad k ε y α p - greenD k ε y p * fderiv ℝ u p (EuclideanSpace.single α 1)

@[simp] theorem imagePoint_apply_two (ε : ℝ) (y : E3) : imagePoint ε y 2 = 2 * ε - y 2 := by
  simp [imagePoint]

/-- A point of another height than the image is not the image. -/
theorem ne_imagePoint {ε : ℝ} {y p : E3} (h : p 2 ≠ 2 * ε - y 2) : p ≠ imagePoint ε y := by
  rintro rfl
  simp at h

/-- A point of another height than the pole is not the pole. -/
theorem ne_of_apply_two_ne {y p : E3} (h : p 2 ≠ y 2) : p ≠ y := by
  rintro rfl
  exact h rfl

/-- The translated spherical wave has the derivative `σ_k(|p − c|) ⟨p − c, v⟩`. -/
theorem fderiv_sphericalWave_sub_apply (k : ℝ) {c p : E3} (hp : p ≠ c) (v : E3) :
    fderiv ℝ (fun p => sphericalWave k (p - c)) p v = waveSlope k ‖p - c‖ * ⟪p - c, v⟫_ℝ := by
  rw [fderiv_comp_sub, fderiv_sphericalWave_apply k (sub_ne_zero.mpr hp)]

/-- The translated spherical wave is differentiable away from its pole. -/
theorem differentiableAt_sphericalWave_sub (k : ℝ) {c p : E3} (hp : p ≠ c) :
    DifferentiableAt ℝ (fun p => sphericalWave k (p - c)) p :=
  (differentiableAt_comp_sub c).mpr
    ((contDiffAt_sphericalWave k (n := 1) (sub_ne_zero.mpr hp)).differentiableAt one_ne_zero)

/-- The translated gradient component is differentiable away from the pole. -/
theorem differentiableAt_waveGrad_sub (k : ℝ) (α : Fin 3) {c p : E3} (hp : p ≠ c) :
    DifferentiableAt ℝ (fun p => waveGrad k α (p - c)) p :=
  (differentiableAt_comp_sub c).mpr
    ((contDiffAt_waveGrad k α (n := 1) (sub_ne_zero.mpr hp)).differentiableAt one_ne_zero)

/-- The Green function is differentiable away from the pole and its image. -/
theorem differentiableAt_greenD (k ε : ℝ) {y p : E3} (h1 : p ≠ y) (h2 : p ≠ imagePoint ε y) :
    DifferentiableAt ℝ (greenD k ε y) p :=
  (differentiableAt_sphericalWave_sub k h1).sub (differentiableAt_sphericalWave_sub k h2)

/-- The gradient of the Green function is differentiable away from the pole and its image. -/
theorem differentiableAt_greenGrad (k ε : ℝ) (α : Fin 3) {y p : E3} (h1 : p ≠ y)
    (h2 : p ≠ imagePoint ε y) : DifferentiableAt ℝ (greenGrad k ε y α) p :=
  (differentiableAt_waveGrad_sub k α h1).sub (differentiableAt_waveGrad_sub k α h2)

/-- **The gradient of the Green function**: `∂_α (G_k(p − y) − G_k(p − y′)) = greenGrad`. -/
theorem fderiv_greenD_single (k ε : ℝ) {y p : E3} (h1 : p ≠ y) (h2 : p ≠ imagePoint ε y)
    (α : Fin 3) :
    fderiv ℝ (greenD k ε y) p (EuclideanSpace.single α 1) = greenGrad k ε y α p := by
  have hs : greenD k ε y = fun p => sphericalWave k (p - y) -
      sphericalWave k (p - imagePoint ε y) := rfl
  rw [hs, fderiv_fun_sub (differentiableAt_sphericalWave_sub k h1)
    (differentiableAt_sphericalWave_sub k h2)]
  simp only [sub_apply, fderiv_sphericalWave_sub_apply k h1,
    fderiv_sphericalWave_sub_apply k h2, EuclideanSpace.inner_single_right, conj_trivial,
    one_mul, greenGrad, waveGrad]

/-- **The Green function solves the Helmholtz equation** away from the pole and its image:
`Σ_α ∂_α ∂_α G + k² G = 0`. -/
theorem sum_fderiv_greenGrad (k ε : ℝ) {y p : E3} (h1 : p ≠ y) (h2 : p ≠ imagePoint ε y) :
    ∑ α, fderiv ℝ (greenGrad k ε y α) p (EuclideanSpace.single α 1) =
      -(k ^ 2 : ℂ) * greenD k ε y p := by
  have hs (α : Fin 3) : greenGrad k ε y α = fun p => waveGrad k α (p - y) -
      waveGrad k α (p - imagePoint ε y) := rfl
  have hd (α : Fin 3) : fderiv ℝ (greenGrad k ε y α) p (EuclideanSpace.single α 1) =
      fderiv ℝ (waveGrad k α) (p - y) (EuclideanSpace.single α 1) -
        fderiv ℝ (waveGrad k α) (p - imagePoint ε y) (EuclideanSpace.single α 1) := by
    rw [hs, fderiv_fun_sub (differentiableAt_waveGrad_sub k α h1)
      (differentiableAt_waveGrad_sub k α h2), sub_apply, fderiv_comp_sub,
      fderiv_comp_sub]
  simp only [hd, Finset.sum_sub_distrib, sum_fderiv_waveGrad k (sub_ne_zero.mpr h1),
    sum_fderiv_waveGrad k (sub_ne_zero.mpr h2), greenD]
  ring

/-- The Green function is smooth away from the pole and its image. -/
theorem contDiffAt_greenD (k ε : ℝ) {y p : E3} (h1 : p ≠ y) (h2 : p ≠ imagePoint ε y)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (greenD k ε y) p := by
  have hc (c : E3) (hc : p ≠ c) : ContDiffAt ℝ n (fun p => sphericalWave k (p - c)) p :=
    (contDiffAt_sphericalWave k (sub_ne_zero.mpr hc)).comp p
      (contDiffAt_id.sub contDiffAt_const)
  exact (hc y h1).sub (hc _ h2)

/-- The gradient of the Green function is smooth away from the pole and its image. -/
theorem contDiffAt_greenGrad (k ε : ℝ) (α : Fin 3) {y p : E3} (h1 : p ≠ y)
    (h2 : p ≠ imagePoint ε y) {n : WithTop ℕ∞} : ContDiffAt ℝ n (greenGrad k ε y α) p := by
  have hc (c : E3) (hc : p ≠ c) : ContDiffAt ℝ n (fun p => waveGrad k α (p - c)) p :=
    (contDiffAt_waveGrad k α (sub_ne_zero.mpr hc)).comp p
      (contDiffAt_id.sub contDiffAt_const)
  exact (hc y h1).sub (hc _ h2)

/-- Green's field is of class `C¹` where `u` is of class `C²`, away from the pole and its image. -/
theorem contDiffAt_greenField (k ε : ℝ) {y : E3} {u : E3 → ℂ} (α : Fin 3) {p : E3}
    (hu : ContDiffAt ℝ 2 u p) (h1 : p ≠ y) (h2 : p ≠ imagePoint ε y) :
    ContDiffAt ℝ 1 (greenField k ε y u α) p := by
  have hdu : ContDiffAt ℝ 1 (fun q => fderiv ℝ u q (EuclideanSpace.single α 1)) p :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  exact ((hu.of_le (by norm_num)).mul (contDiffAt_greenGrad k ε α h1 h2)).sub
    ((contDiffAt_greenD k ε h1 h2).mul hdu)

/-- **Green's field of two solutions of the Helmholtz equation is free of divergence**:
`div(u ∇G − G ∇u) = u ΔG − G Δu = 0`. -/
theorem divergenceC_greenField (k ε : ℝ) {y : E3} {u : E3 → ℂ} {p : E3}
    (hu : ContDiffAt ℝ 2 u p) (hH : Δ u p + k ^ 2 * u p = 0) (h1 : p ≠ y)
    (h2 : p ≠ imagePoint ε y) : divergenceC (greenField k ε y u) p = 0 := by
  have hud : DifferentiableAt ℝ u p := hu.differentiableAt (by norm_num)
  have hdu (α : Fin 3) : DifferentiableAt ℝ
      (fun q => fderiv ℝ u q (EuclideanSpace.single α 1)) p :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const _)
  have hterm (α : Fin 3) : fderiv ℝ (greenField k ε y u α) p (EuclideanSpace.single α 1) =
      u p * fderiv ℝ (greenGrad k ε y α) p (EuclideanSpace.single α 1) -
        greenD k ε y p * fderiv ℝ (fun q => fderiv ℝ u q (EuclideanSpace.single α 1)) p
          (EuclideanSpace.single α 1) := by
    have h := (hud.hasFDerivAt.mul (differentiableAt_greenGrad k ε α h1 h2).hasFDerivAt).sub
      ((differentiableAt_greenD k ε h1 h2).hasFDerivAt.mul (hdu α).hasFDerivAt)
    have h' : HasFDerivAt (greenField k ε y u α) _ p := h
    rw [h'.fderiv]
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, fderiv_greenD_single k ε h1 h2]
    ring
  have hΔ := laplacian_eq_sum_fderiv hu
  unfold divergenceC
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_fderiv_greenGrad k ε h1 h2]
  rw [← hΔ]
  linear_combination (-greenD k ε y p) * hH

/-- `|(x, ε) − y| = |(x, ε) − y′|`: the points of the plane are equidistant from the pole and its
image. -/
theorem norm_spacePoint_sub_imagePoint (ε : ℝ) (y : E3) (x : E2) :
    ‖spacePoint x ε - imagePoint ε y‖ = ‖spacePoint x ε - y‖ := by
  have h : ‖spacePoint x ε - imagePoint ε y‖ ^ 2 = ‖spacePoint x ε - y‖ ^ 2 := by
    rw [norm_sq_eq_three, norm_sq_eq_three]
    simp [spacePoint, imagePoint]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- **The Green function vanishes on the plane** `z = ε`. -/
theorem greenD_spacePoint (k ε : ℝ) (y : E3) (x : E2) : greenD k ε y (spacePoint x ε) = 0 := by
  unfold greenD sphericalWave
  rw [norm_spacePoint_sub_imagePoint, sub_self]

/-- **The normal derivative of the Green function on the plane** `z = ε` is the
Rayleigh–Sommerfeld kernel: `∂_z G(x, ε) = K_k(y − (x, ε))`. -/
theorem greenGrad_two_spacePoint (k ε : ℝ) (y : E3) (x : E2) :
    greenGrad k ε y 2 (spacePoint x ε) = rayleighKernel k (y - spacePoint x ε) := by
  have hn : ‖y - spacePoint x ε‖ = ‖spacePoint x ε - y‖ := norm_sub_rev _ _
  unfold greenGrad waveGrad rayleighKernel
  rw [norm_spacePoint_sub_imagePoint, hn, kernelProfile_eq_waveSlope]
  simp [spacePoint, imagePoint]
  ring

/-! ### The flux of Green's field through the spheres about the pole -/

/-- The inner product of `ℝ³` in the co-ordinates. -/
theorem inner_eq_three (a b : E3) : ⟪a, b⟫_ℝ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- The derivative along `v` in the partial derivatives, for a complex function. -/
theorem fderiv_apply_eq_sum_single (u : E3 → ℂ) (x v : E3) :
    fderiv ℝ u x v = ∑ α, ((v α : ℝ) : ℂ) * fderiv ℝ u x (EuclideanSpace.single α 1) := by
  conv_lhs => rw [eq_sum_single v]
  simp [map_sum, map_smul, Complex.real_smul]

/-- The slope of the spherical wave is continuous away from `0`. -/
theorem continuousAt_waveSlope (k : ℝ) {R : ℝ} (hR : R ≠ 0) : ContinuousAt (waveSlope k) R :=
  (hasDerivAt_waveSlope k hR).continuousAt

/-- The integrand of the flux of Green's field through the sphere of radius `r` about the pole,
with the singular factors of the spherical wave cancelled; it is continuous up to `r = 0`. -/
def greenFluxIntegrand (k ε : ℝ) (y : E3) (u : E3 → ℂ) (r : ℝ) (n : E3) : ℂ :=
  u (y + r • n) * (cexp (I * k * r) * (I * k * r - 1) / (4 * π) -
      ((r ^ 2 : ℝ) : ℂ) * (waveSlope k ‖y + r • n - imagePoint ε y‖ *
        ⟪y + r • n - imagePoint ε y, n⟫_ℝ)) -
    ((r : ℂ) * cexp (I * k * r) / (4 * π) - ((r ^ 2 : ℝ) : ℂ) *
      sphericalWave k (y + r • n - imagePoint ε y)) * fderiv ℝ u (y + r • n) n

/-- For `r > 0` the flux of Green's field is the integral of `greenFluxIntegrand`. -/
theorem fluxC_greenField_eq_integral (k ε : ℝ) (y : E3) (u : E3 → ℂ) {r : ℝ} (hr : 0 < r) :
    fluxC (greenField k ε y u) y r =
      ∫ n : sphere (0 : E3) 1, greenFluxIntegrand k ε y u r n ∂sphereMeasure := by
  unfold fluxC
  refine integral_congr_ae (Eventually.of_forall fun n => ?_)
  have hn : ‖(n : E3)‖ = 1 := norm_eq_of_mem_sphere n
  have hnorm : ‖y + r • (n : E3) - y‖ = r := by
    rw [add_sub_cancel_left, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hsq : ((n : E3) 0 : ℂ) ^ 2 + ((n : E3) 1 : ℂ) ^ 2 + ((n : E3) 2 : ℂ) ^ 2 = 1 := by
    have h := norm_sq_eq_three (n : E3)
    rw [hn, one_pow] at h
    exact_mod_cast h.symm
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set q : E3 := y + r • (n : E3) - imagePoint ε y with hq
  have hdu := fderiv_apply_eq_sum_single u (y + r • (n : E3)) (n : E3)
  have hin := inner_eq_three q (n : E3)
  simp only [greenFluxIntegrand, greenField, greenGrad, greenD, waveGrad, ← hq, hdu,
    hin, sphericalWave, add_sub_cancel_left, Fin.sum_univ_three, PiLp.smul_apply, smul_eq_mul]
  rw [show ‖r • (n : E3)‖ = r by rw [norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hr]]
  unfold waveSlope
  push_cast
  field_simp
  try simp only [show (r : ℂ) * I * k = I * k * r by ring]
  linear_combination (cexp (I * k * r) * (I * k * r - 1) * u (y + r • (n : E3))) * hsq

/-- The integrand is continuous where the points `y + r n` lie in the half-space `z > 0` and avoid
the image. -/
theorem continuousOn_greenFluxIntegrand (k ε : ℝ) {y : E3} {u : E3 → ℂ}
    (hu : ContDiffOn ℝ 1 u upperHalfSpace) :
    ContinuousOn (Function.uncurry (greenFluxIntegrand k ε y u))
      {x : ℝ × E3 | y + x.1 • x.2 ∈ upperHalfSpace ∧ y + x.1 • x.2 ≠ imagePoint ε y} := by
  have hU := isOpen_upperHalfSpace
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨hx1, hx2⟩ := hx
  have hpt : Continuous fun x : ℝ × E3 => y + x.1 • x.2 := by fun_prop
  have hq0 : y + x.1 • x.2 - imagePoint ε y ≠ 0 := sub_ne_zero.mpr hx2
  have hu' : ContinuousAt (fun x : ℝ × E3 => u (y + x.1 • x.2)) x :=
    ContinuousAt.comp (f := fun x : ℝ × E3 => y + x.1 • x.2)
      (hu.continuousOn.continuousAt (hU.mem_nhds hx1)) hpt.continuousAt
  have hdu : ContinuousAt (fun x : ℝ × E3 => fderiv ℝ u (y + x.1 • x.2) x.2) x := by
    have h1 : ContinuousAt (fun x : ℝ × E3 => fderiv ℝ u (y + x.1 • x.2)) x :=
      ContinuousAt.comp (f := fun x : ℝ × E3 => y + x.1 • x.2)
        ((hu.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hx1))
        hpt.continuousAt
    exact h1.clm_apply continuousAt_snd
  have hq : Continuous fun x : ℝ × E3 => y + x.1 • x.2 - imagePoint ε y := by fun_prop
  have hσ : ContinuousAt (fun x : ℝ × E3 => waveSlope k ‖y + x.1 • x.2 - imagePoint ε y‖) x :=
    ContinuousAt.comp (f := fun x : ℝ × E3 => ‖y + x.1 • x.2 - imagePoint ε y‖)
      (continuousAt_waveSlope k (norm_ne_zero_iff.mpr hq0)) (continuous_norm.comp hq).continuousAt
  have hG : ContinuousAt
      (fun x : ℝ × E3 => sphericalWave k (y + x.1 • x.2 - imagePoint ε y)) x :=
    ContinuousAt.comp (f := fun x : ℝ × E3 => y + x.1 • x.2 - imagePoint ε y)
      (contDiffAt_sphericalWave k (n := 0) hq0).continuousAt hq.continuousAt
  have hin : ContinuousAt
      (fun x : ℝ × E3 => ((⟪y + x.1 • x.2 - imagePoint ε y, x.2⟫_ℝ : ℝ) : ℂ)) x := by
    fun_prop
  have hc1 : ContinuousAt
      (fun x : ℝ × E3 => cexp (I * k * x.1) * (I * k * x.1 - 1) / (4 * π)) x := by fun_prop
  have hc2 : ContinuousAt (fun x : ℝ × E3 => ((x.1 ^ 2 : ℝ) : ℂ)) x := by fun_prop
  have hc3 : ContinuousAt (fun x : ℝ × E3 => (x.1 : ℂ) * cexp (I * k * x.1) / (4 * π)) x := by
    fun_prop
  exact (hu'.mul (hc1.sub (hc2.mul (hσ.mul hin)))).sub ((hc3.sub (hc2.mul hG)).mul hdu)

/-- **The flux of Green's field through small spheres about the pole tends to `−u(y)`**: the
singular part `e^{ikr}(ikr − 1)/(4πr²)` of the normal derivative of the spherical wave, integrated
over the sphere of area `4πr²`, recovers `−u(y)`, and the other terms vanish with `r`. -/
theorem tendsto_fluxC_greenField (k ε : ℝ) {y : E3} {u : E3 → ℂ}
    (hu : ContDiffOn ℝ 1 u upperHalfSpace) (hy : 0 < y 2) (hyε : y 2 ≠ ε) :
    Tendsto (fun r => fluxC (greenField k ε y u) y r) (𝓝[>] 0) (𝓝 (-u y)) := by
  set O : Set (ℝ × E3) :=
    {x : ℝ × E3 | y + x.1 • x.2 ∈ upperHalfSpace ∧ y + x.1 • x.2 ≠ imagePoint ε y} with hOdef
  have hpt : Continuous fun x : ℝ × E3 => y + x.1 • x.2 := by fun_prop
  have hO : IsOpen O :=
    (isOpen_upperHalfSpace.preimage hpt).inter (isOpen_ne_fun hpt continuous_const)
  have hyy : y ≠ imagePoint ε y := ne_imagePoint (by intro h; apply hyε; linarith)
  have hs₀ : ∀ n ∈ sphere (0 : E3) 1, ((0 : ℝ), n) ∈ O := fun n _ => by
    simp only [hOdef, mem_ofPred_eq, zero_smul, add_zero]
    exact ⟨hy, hyy⟩
  have hc := continuousAt_integral_sphere_of_continuousOn hO hs₀
    (continuousOn_greenFluxIntegrand k ε hu)
  have h0 : ∫ n : sphere (0 : E3) 1, greenFluxIntegrand k ε y u 0 n ∂sphereMeasure = -u y := by
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [greenFluxIntegrand, zero_smul, add_zero, ofReal_zero, mul_zero, zero_mul,
      Complex.exp_zero, zero_sub, sub_zero, zero_pow two_ne_zero, zero_div]
    rw [integral_const, sphereMeasure_real_univ, Complex.real_smul]
    push_cast
    field_simp
  have hT : Tendsto (fun r => ∫ n : sphere (0 : E3) 1, greenFluxIntegrand k ε y u r n
      ∂sphereMeasure) (𝓝 0) (𝓝 (-u y)) := h0 ▸ hc
  refine (hT.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (fluxC_greenField_eq_integral k ε y u hr).symm

/-- **The flux of Green's field through every sphere about the pole is `−u(y)`**, when the closed
ball lies in the half-space `z > 0` and avoids the image: the field is free of divergence, so the
flux does not depend on the radius, and it tends to `−u(y)`. -/
theorem fluxC_greenField_eq (k ε : ℝ) {y : E3} {u : E3 → ℂ}
    (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) (hy : 0 < y 2) (hyε : y 2 ≠ ε)
    {R : ℝ} (hR : 0 < R)
    (hball : ∀ x : E3, ‖x‖ ≤ R → 0 < (y + x) 2 ∧ y + x ≠ imagePoint ε y) :
    fluxC (greenField k ε y u) y R = -u y := by
  have hU := isOpen_upperHalfSpace
  set W : Set E3 := {p | 0 < p 2 ∧ p ≠ y ∧ p ≠ imagePoint ε y} with hWdef
  have hW : IsOpen W :=
    (isOpen_upperHalfSpace.inter ((isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_ne_fun continuous_id continuous_const)) : _)
  have hu2 (p : E3) (hp : 0 < p 2) : ContDiffAt ℝ 2 u p :=
    hu.contDiffAt (hU.mem_nhds hp)
  have hV : ∀ α, ContDiffOn ℝ 1 (greenField k ε y u α) W := fun α p hp =>
    (contDiffAt_greenField k ε α (hu2 p hp.1) hp.2.1 hp.2.2).contDiffWithinAt
  have hconst : ∀ r, 0 < r → r ≤ R → fluxC (greenField k ε y u) y r =
      fluxC (greenField k ε y u) y R := by
    intro r hr hrR
    have hsub : ∀ x : E3, r ≤ ‖x‖ → ‖x‖ ≤ R → y + x ∈ W := fun x hx1 hx2 => by
      obtain ⟨h1, h2⟩ := hball x hx2
      refine ⟨h1, ?_, h2⟩
      intro h
      have : x = 0 := by simpa using h
      rw [this, norm_zero] at hx1
      linarith
    have h := fluxC_sub_fluxC hW hV hr.le hrR hsub
    have hzero : ∫ x in shell r R, divergenceC (greenField k ε y u) (y + x) = 0 := by
      refine (setIntegral_congr_fun (measurableSet_shell r R) fun x hx => ?_).trans
        (integral_zero _ _)
      have hxW := hsub x hx.1.le hx.2.le
      exact divergenceC_greenField k ε (hu2 _ hxW.1) (hH _ hxW.1) hxW.2.1 hxW.2.2
    rw [hzero, sub_eq_zero] at h
    exact h.symm
  have hT := tendsto_fluxC_greenField k ε (hu.of_le (by norm_num)) hy hyε
  have hev : (fun r => fluxC (greenField k ε y u) y r) =ᶠ[𝓝[>] 0]
      fun _ => fluxC (greenField k ε y u) y R := by
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    exact hconst r hr.1 hr.2.le
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hT

/-! ### The far field of Green's field -/

/-- A far point is far from `c`: `|p − c| ≥ |p|/2` when `2|c| ≤ |p|`. -/
theorem half_le_norm_sub {c p : E3} (h : 2 * ‖c‖ ≤ ‖p‖) : ‖p‖ / 2 ≤ ‖p - c‖ := by
  have := norm_sub_norm_le p c
  linarith

/-- The translated spherical wave at a far point, `|G_k(p − c)| ≤ 1/(2π|p|)`. -/
theorem norm_sphericalWave_sub_le (k : ℝ) {c p : E3} (h : 2 * ‖c‖ ≤ ‖p‖) (hp : 0 < ‖p‖) :
    ‖sphericalWave k (p - c)‖ ≤ 1 / (2 * π * ‖p‖) := by
  rw [norm_sphericalWave]
  have := half_le_norm_sub h
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [Real.pi_pos]

/-- **The radiation condition of the translated spherical wave**, with an explicit rate:
`|σ_k(|q|)⟨q, p⟩ − ik|p| G_k(q)| ≤ (|k||c| + 1)/(π|p|)` for `q = p − c` and `2|c| ≤ |p|`. -/
theorem norm_waveRadial_le (k : ℝ) {c p : E3} (h : 2 * ‖c‖ ≤ ‖p‖) (hp : 0 < ‖p‖) :
    ‖waveSlope k ‖p - c‖ * ⟪p - c, p⟫_ℝ - I * k * ‖p‖ * sphericalWave k (p - c)‖ ≤
      (|k| * ‖c‖ + 1) / (π * ‖p‖) := by
  set q := p - c with hqdef
  set R := ‖q‖ with hRdef
  set r := ‖p‖ with hrdef
  set d := ⟪q, p⟫_ℝ with hddef
  have hRr : r / 2 ≤ R := half_le_norm_sub h
  have hR0 : 0 < R := by linarith
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hE : waveSlope k R * d - I * k * r * sphericalWave k q =
      sphericalWave k q * (I * k * ((d / R - r : ℝ) : ℂ) - ((d / R ^ 2 : ℝ) : ℂ)) := by
    unfold waveSlope sphericalWave
    rw [← hRdef]
    push_cast
    field_simp
    ring
  have ht : |d / R - r| ≤ 2 * ‖c‖ := by
    have hpq : p = q + c := by rw [hqdef]; abel
    have hd' : d = R ^ 2 + ⟪q, c⟫_ℝ := by
      rw [hddef, hpq, inner_add_right, real_inner_self_eq_norm_sq]
    have h1 : |R - r| ≤ ‖c‖ := by
      have := abs_norm_sub_norm_le q p
      rwa [hqdef, sub_sub_cancel_left, norm_neg] at this
    have h2 : |⟪q, c⟫_ℝ / R| ≤ ‖c‖ := by
      rw [abs_div, abs_of_pos hR0, div_le_iff₀ hR0]
      calc |⟪q, c⟫_ℝ| ≤ R * ‖c‖ := abs_real_inner_le_norm _ _
        _ = ‖c‖ * R := mul_comm _ _
    have he : d / R - r = (R - r) + ⟪q, c⟫_ℝ / R := by
      rw [hd']
      field_simp
      ring
    rw [he]
    calc |(R - r) + ⟪q, c⟫_ℝ / R| ≤ |R - r| + |⟪q, c⟫_ℝ / R| := abs_add_le _ _
      _ ≤ 2 * ‖c‖ := by linarith
  have hdd : |d / R ^ 2| ≤ 2 := by
    have hd : |d| ≤ R * r := abs_real_inner_le_norm q p
    rw [abs_div, abs_of_pos (pow_pos hR0 2), div_le_iff₀ (pow_pos hR0 2)]
    nlinarith
  rw [hE, norm_mul, norm_sphericalWave]
  have hb : ‖I * k * ((d / R - r : ℝ) : ℂ) - ((d / R ^ 2 : ℝ) : ℂ)‖ ≤ 2 * |k| * ‖c‖ + 2 := by
    calc ‖I * k * ((d / R - r : ℝ) : ℂ) - ((d / R ^ 2 : ℝ) : ℂ)‖
        ≤ ‖I * k * ((d / R - r : ℝ) : ℂ)‖ + ‖((d / R ^ 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ = |k| * |d / R - r| + |d / R ^ 2| := by
        rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
      _ ≤ |k| * (2 * ‖c‖) + 2 := by gcongr
      _ = 2 * |k| * ‖c‖ + 2 := by ring
  calc 1 / (4 * π * R) * ‖I * k * ((d / R - r : ℝ) : ℂ) - ((d / R ^ 2 : ℝ) : ℂ)‖
      ≤ 1 / (4 * π * R) * (2 * |k| * ‖c‖ + 2) := by gcongr
    _ = (|k| * ‖c‖ + 1) / (2 * π * R) := by field_simp; ring
    _ ≤ (|k| * ‖c‖ + 1) / (π * r) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [Real.pi_pos]

/-- The sum `Σ_α p_α (u ∂_α G − G ∂_α u)` in terms of the radial derivatives. -/
theorem sum_mul_greenField (k ε : ℝ) (y : E3) (u : E3 → ℂ) (p : E3) :
    ∑ α, ((p α : ℝ) : ℂ) * greenField k ε y u α p =
      u p * (waveSlope k ‖p - y‖ * ⟪p - y, p⟫_ℝ -
        waveSlope k ‖p - imagePoint ε y‖ * ⟪p - imagePoint ε y, p⟫_ℝ) -
      greenD k ε y p * fderiv ℝ u p p := by
  rw [fderiv_apply_eq_sum_single u p p, inner_eq_three, inner_eq_three]
  simp only [greenField, greenGrad, waveGrad, Fin.sum_univ_three, PiLp.sub_apply]
  push_cast
  ring

/-- **The far-field bound of Green's field**: if `|p||u(p)| ≤ C` and
`|p||∂_r u − iku| ≤ e` at `p`, and the pole and its image lie in the ball of radius `a ≤ |p|/2`,
then `|Σ_α p_α (u ∂_α G − G ∂_α u)| ≤ 2C(|k|a + 1)/(π|p|²) + e/(π|p|)`. -/
theorem norm_sum_mul_greenField_le {k ε : ℝ} {y : E3} {u : E3 → ℂ} {p : E3} {a C e : ℝ}
    (ha1 : ‖y‖ ≤ a) (ha2 : ‖imagePoint ε y‖ ≤ a) (hpa : 2 * a ≤ ‖p‖) (hp : 0 < ‖p‖)
    (hC : ‖p‖ * ‖u p‖ ≤ C) (he : ‖p‖ * ‖fderiv ℝ u p (‖p‖⁻¹ • p) - I * k * u p‖ ≤ e) :
    ‖∑ α, ((p α : ℝ) : ℂ) * greenField k ε y u α p‖ ≤
      2 * C * (|k| * a + 1) / (π * ‖p‖ ^ 2) + e / (π * ‖p‖) := by
  set r := ‖p‖ with hrdef
  set y' := imagePoint ε y with hy'
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h1 : 2 * ‖y‖ ≤ r := by linarith
  have h2 : 2 * ‖y'‖ ≤ r := by linarith
  set S1 := waveSlope k ‖p - y‖ * ⟪p - y, p⟫_ℝ - I * k * r * sphericalWave k (p - y)
  set S2 := waveSlope k ‖p - y'‖ * ⟪p - y', p⟫_ℝ - I * k * r * sphericalWave k (p - y')
  set D := fderiv ℝ u p (r⁻¹ • p) - I * k * u p with hD
  have hDu : fderiv ℝ u p p = r * fderiv ℝ u p (r⁻¹ • p) := by
    rw [map_smul, Complex.real_smul, ← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ hp.ne',
      ofReal_one, one_mul]
  have hdecomp : ∑ α, ((p α : ℝ) : ℂ) * greenField k ε y u α p =
      u p * (S1 - S2) - greenD k ε y p * (r * D) := by
    rw [sum_mul_greenField, hDu]
    simp only [greenD, S1, S2, hD, ← hy']
    ring
  have hS1 := norm_waveRadial_le k h1 hp
  have hS2 := norm_waveRadial_le k h2 hp
  have hG : ‖greenD k ε y p‖ ≤ 1 / (π * r) := by
    unfold greenD
    calc ‖sphericalWave k (p - y) - sphericalWave k (p - y')‖
        ≤ ‖sphericalWave k (p - y)‖ + ‖sphericalWave k (p - y')‖ := norm_sub_le _ _
      _ ≤ 1 / (2 * π * r) + 1 / (2 * π * r) :=
        add_le_add (norm_sphericalWave_sub_le k h1 hp) (norm_sphericalWave_sub_le k h2 hp)
      _ = 1 / (π * r) := by field_simp; norm_num
  have hS : ‖S1 - S2‖ ≤ 2 * (|k| * a + 1) / (π * r) := by
    calc ‖S1 - S2‖ ≤ ‖S1‖ + ‖S2‖ := norm_sub_le _ _
      _ ≤ (|k| * ‖y‖ + 1) / (π * r) + (|k| * ‖y'‖ + 1) / (π * r) := add_le_add hS1 hS2
      _ ≤ (|k| * a + 1) / (π * r) + (|k| * a + 1) / (π * r) := by gcongr
      _ = 2 * (|k| * a + 1) / (π * r) := by ring
  have hu : ‖u p‖ ≤ C / r := by rw [le_div_iff₀ hp, mul_comm]; exact hC
  have hrD : ‖(r : ℂ) * D‖ ≤ e := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    exact he
  have hC0 : 0 ≤ C := le_trans (by positivity) hC
  rw [hdecomp]
  calc ‖u p * (S1 - S2) - greenD k ε y p * (r * D)‖
      ≤ ‖u p‖ * ‖S1 - S2‖ + ‖greenD k ε y p‖ * ‖(r : ℂ) * D‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ C / r * (2 * (|k| * a + 1) / (π * r)) + 1 / (π * r) * e := by
        gcongr
    _ = 2 * C * (|k| * a + 1) / (π * r ^ 2) + e / (π * r) := by
        field_simp

end ProjectAinos.Electrodynamics.Diffraction
