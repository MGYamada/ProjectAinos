/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.EinsteinInfeldHoffmann
public import ProjectAinos.GeneralRelativity.NewtonianFieldLimit
public import ProjectAinos.SmoothGeometry.Potential.NewtonPotential
import Mathlib.Tactic

/-! # The potentials of the second approximation

Landau–Lifshitz, §106, the field side of the post-Newtonian potentials `Φ`, `ψ`, `B` of
`PostNewtonianMetricFamily` in the gauge of GR36 (the standard post-Newtonian gauge).

* Smooth sources (a density `ρ` of compact support and a velocity field `v`, both `C²`, at one
  time, on `EuclideanSpace ℝ (Fin 3)`): `newtonianPotential` `Φ = −4πG N[ρ]`,
  `secondPotential` `ψ = −4πG N[ρ((3/2) v² − U)]` with `U = −Φ`, and `vectorNewtonPotential`
  `V_k = 4πG N[ρ v_k]`, all Newton potentials `N` (`SmoothGeometry.Potential.newtonPotential`) of
  sources of compact support; `laplacian_newtonianPotential` `ΔΦ = 4πGρ`,
  `laplacian_secondPotential` `Δψ = 4πGρ((3/2) v² − U)`, `laplacian_vectorNewtonPotential`
  `ΔV_k = −4πGρ v_k`.
* Point masses (the potentials of `EinsteinInfeldHoffmann` seen by the body `a`, at field points
  away from the other bodies): `flatLaplacian_othersPotential` `ΔΦ = 0`,
  `flatLaplacian_othersScalarPotential` `Δψ = 0`, and **the gauge condition of GR36**
  `gauge_othersVectorPotential`: `∇ · B + 3 ∂ₜΦ = 0` along any motion of the bodies. These are the
  vacuum equations of the potentials at the orders `c⁰` and `c⁻²` of `g_tt` and the gauge
  relation between `g_ti` and `g_ij`.

Not in this file: the Einstein equations of the metric family built from these potentials (the
expansion of the coordinate Ricci tensor of the family to the orders `c⁰` and `c⁻²` with a
remainder `O(c⁻⁴)`), the time derivatives of the potentials of moving smooth sources with the
continuity equation, and the part `W` of `B = −(7/2)V − (1/2)W` in this gauge, which is the
gradient of a time derivative of the superpotential `G ∫ ρ(y)‖x − y‖ dy`, not a Newton potential
of a source of compact support.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped Topology Laplacian ContDiff Real

namespace ProjectAinos.GeneralRelativity.PostNewtonianField

open SmoothGeometry.Potential EinsteinInfeldHoffmann NewtonianMetricFamily

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "S" => NewtonianSpace

/-! ### Smooth sources -/

/-- The Newtonian potential `Φ = −4πG N[ρ]` of a density `ρ` (`ΔΦ = 4πGρ`). -/
def newtonianPotential (G : ℝ) (ρ : E3 → ℝ) : E3 → ℝ :=
  newtonPotential (fun y => -(4 * π * G) * ρ y)

/-- The source `ρ ((3/2) v² + Φ)` of the second potential, `U = −Φ`. -/
def secondSource (G : ℝ) (ρ : E3 → ℝ) (v : E3 → E3) : E3 → ℝ := fun y =>
  ρ y * (3 / 2 * ‖v y‖ ^ 2 + newtonianPotential G ρ y)

/-- **The second scalar potential** `ψ = −4πG N[ρ((3/2) v² − U)]` in the gauge of GR36, the
smooth-source form of `othersScalarPotential`. -/
def secondPotential (G : ℝ) (ρ : E3 → ℝ) (v : E3 → E3) : E3 → ℝ :=
  newtonPotential (fun y => -(4 * π * G) * secondSource G ρ v y)

/-- The Newton part `V_k = 4πG N[ρ v_k]` of the vector potential. -/
def vectorNewtonPotential (G : ℝ) (ρ : E3 → ℝ) (v : E3 → E3) (k : Fin 3) : E3 → ℝ :=
  newtonPotential (fun y => 4 * π * G * (ρ y * v y k))

variable {G : ℝ} {ρ : E3 → ℝ} {v : E3 → E3}

theorem hasCompactSupport_const_mul {c : ℝ} {f : E3 → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun y => c * f y) :=
  hf.mul_left

theorem contDiff_newtonianPotential (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) :
    ContDiff ℝ 2 (newtonianPotential G ρ) :=
  contDiff_two_newtonPotential (hasCompactSupport_const_mul hcρ) (contDiff_const.mul hρ)

/-- **Poisson's equation of the Newtonian potential**, `ΔΦ = 4πGρ`. -/
theorem laplacian_newtonianPotential (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (x : E3) : Δ (newtonianPotential G ρ) x = 4 * π * G * ρ x := by
  rw [newtonianPotential, laplacian_newtonPotential (ρ := fun y => -(4 * π * G) * ρ y)
    (hasCompactSupport_const_mul hcρ) (contDiff_const.mul hρ)]
  ring

theorem hasCompactSupport_secondSource (hcρ : HasCompactSupport ρ) :
    HasCompactSupport (secondSource G ρ v) :=
  hcρ.mul_right

theorem contDiff_secondSource (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hv : ContDiff ℝ 2 v) : ContDiff ℝ 2 (secondSource G ρ v) :=
  hρ.mul ((contDiff_const.mul ((contDiff_norm_sq ℝ).comp hv)).add
    (contDiff_newtonianPotential hcρ hρ))

/-- **Poisson's equation of the second potential**, `Δψ = 4πGρ((3/2) v² − U)`, `U = −Φ`. -/
theorem laplacian_secondPotential (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hv : ContDiff ℝ 2 v) (x : E3) :
    Δ (secondPotential G ρ v) x =
      4 * π * G * (ρ x * (3 / 2 * ‖v x‖ ^ 2 - -newtonianPotential G ρ x)) := by
  rw [secondPotential, laplacian_newtonPotential
    (ρ := fun y => -(4 * π * G) * secondSource G ρ v y)
    (hasCompactSupport_const_mul (hasCompactSupport_secondSource hcρ))
    (contDiff_const.mul (contDiff_secondSource hcρ hρ hv)), secondSource]
  ring

/-- **Poisson's equation of the Newton part of the vector potential**, `ΔV_k = −4πGρ v_k`. -/
theorem laplacian_vectorNewtonPotential (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hv : ContDiff ℝ 2 v) (k : Fin 3) (x : E3) :
    Δ (vectorNewtonPotential G ρ v k) x = -(4 * π * G * (ρ x * v x k)) := by
  have hc : HasCompactSupport fun y => 4 * π * G * (ρ y * v y k) :=
    hasCompactSupport_const_mul (hcρ.mul_right (f' := fun y => v y k))
  have hs : ContDiff ℝ 2 fun y => 4 * π * G * (ρ y * v y k) :=
    contDiff_const.mul (hρ.mul ((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).contDiff.comp hv))
  rw [vectorNewtonPotential, laplacian_newtonPotential (ρ := fun y => 4 * π * G * (ρ y * v y k))
    hc hs]

/-! ### Point masses: the vacuum equations off the bodies -/

variable {N : ℕ}

/-- `Σ_α ∂_α (‖z‖₂⁻³ z_α) = 0` for `z ≠ 0`, in the form of the derivatives along the axes. -/
theorem sum_invDist_cube_deriv {z : S} (hz : z ≠ 0) :
    ∑ α : Fin 3, (invDist z ^ 3 - 3 * invDist z ^ 5 * z α ^ 2) = 0 := by
  have h := invDist_sq_mul hz
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e : 3 * invDist z ^ 5 * ∑ α, z α ^ 2 = 3 * invDist z ^ 3 * (invDist z ^ 2 * ∑ α, z α ^ 2) :=
    by ring
  rw [e, h]
  norm_num

/-- The derivative along the axis `e_α` of `‖x − y‖₂⁻³ (x − y)_α`. -/
theorem hasDerivAt_invDist_cube_line {x y : S} (h : x ≠ y) (α : Fin 3) :
    HasDerivAt (fun r : ℝ => invDist (x + r • (Pi.single α 1 : S) - y) ^ 3 *
        (x + r • (Pi.single α 1 : S) - y) α)
      (invDist (x - y) ^ 3 - 3 * invDist (x - y) ^ 5 * (x - y) α ^ 2) 0 := by
  have hl := hasDerivAt_line_sub x (Pi.single α 1 : S) y
  have hz : x + (0 : ℝ) • (Pi.single α 1 : S) - y ≠ 0 := by simpa using sub_ne_zero.mpr h
  have h1 := (hasDerivAt_invDist_comp hl hz).pow 3
  have h2 := hasDerivAt_pi.mp hl α
  have hm := h1.mul h2
  refine hm.congr_deriv ?_
  simp only [zero_smul, add_zero, dot_single, Pi.single_eq_same, Nat.cast_ofNat, Pi.pow_apply]
  ring

/-- The gradient of a sum of inverse distances with constant weights, off the centres. -/
theorem fderiv_weighted_apply (w : Fin N → ℝ) (X : Fin N → S) (s : Finset (Fin N)) {x : S}
    (hx : ∀ b ∈ s, x ≠ X b) (h : S) :
    fderiv ℝ (fun y => ∑ b ∈ s, w b * invDist (y - X b)) x h =
      ∑ b ∈ s, w b * (-(invDist (x - X b) ^ 3) * dot (x - X b) h) := by
  have hd : DifferentiableAt ℝ (fun y => ∑ b ∈ s, w b * invDist (y - X b)) x :=
    DifferentiableAt.fun_sum fun b hb => (DifferentiableAt.comp (g := invDist)
      (f := fun y => y - X b) x (differentiableAt_invDist (sub_ne_zero.mpr (hx b hb)))
      (differentiableAt_id.sub_const _)).const_mul _
  refine fderiv_apply_of_hasDerivAt_line hd ?_
  have hD : HasDerivAt (fun r : ℝ => ∑ b ∈ s, w b * invDist (x + r • h - X b))
      (∑ b ∈ s, w b * (-(invDist (x + (0 : ℝ) • h - X b) ^ 3) *
        dot (x + (0 : ℝ) • h - X b) h)) 0 :=
    HasDerivAt.fun_sum fun b hb => (hasDerivAt_invDist_comp (hasDerivAt_line_sub x h (X b))
      (by simpa using sub_ne_zero.mpr (hx b hb))).const_mul (w b)
  simpa using hD

/-- **A sum of inverse distances with constant weights is harmonic off the centres.** -/
theorem flatLaplacian_weighted (w : Fin N → ℝ) (X : Fin N → S) (s : Finset (Fin N)) {x : S}
    (hx : ∀ b ∈ s, x ≠ X b) :
    flatLaplacian (fun y => ∑ b ∈ s, w b * invDist (y - X b)) x = 0 := by
  have hO : IsOpen {y : S | ∀ b ∈ s, y ≠ X b} := by
    have e : {y : S | ∀ b ∈ s, y ≠ X b} = ⋂ b ∈ s, {y | y ≠ X b} := by
      ext y
      simp
    rw [e]
    exact isOpen_biInter_finset fun b _ => isOpen_ne_fun continuous_id continuous_const
  have hev (α : Fin 3) : (fun y => fderiv ℝ (fun y => ∑ b ∈ s, w b * invDist (y - X b)) y
      (Pi.single α 1)) =ᶠ[𝓝 x] fun y => -∑ b ∈ s, w b * (invDist (y - X b) ^ 3 *
        (y - X b) α) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    rw [fderiv_weighted_apply w X s hy, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [dot_single]; ring
  have hterm (α : Fin 3) : fderiv ℝ (fun y => fderiv ℝ (fun y => ∑ b ∈ s,
      w b * invDist (y - X b)) y (Pi.single α 1)) x (Pi.single α 1) =
      -∑ b ∈ s, w b * (invDist (x - X b) ^ 3 - 3 * invDist (x - X b) ^ 5 * (x - X b) α ^ 2) := by
    rw [(hev α).fderiv_eq]
    have hd : DifferentiableAt ℝ (fun y => -∑ b ∈ s, w b * (invDist (y - X b) ^ 3 *
        (y - X b) α)) x := by
      refine (DifferentiableAt.fun_sum fun b hb => ?_).neg
      have hι : DifferentiableAt ℝ (fun y => invDist (y - X b)) x :=
        DifferentiableAt.comp (g := invDist) (f := fun y => y - X b) x
          (differentiableAt_invDist (sub_ne_zero.mpr (hx b hb))) (differentiableAt_id.sub_const _)
      have hc : DifferentiableAt ℝ (fun y : S => (y - X b) α) x := by fun_prop
      exact (hι.pow 3 |>.mul hc).const_mul _
    refine fderiv_apply_of_hasDerivAt_line hd ?_
    exact (HasDerivAt.fun_sum fun b hb =>
      (hasDerivAt_invDist_cube_line (hx b hb) α).const_mul (w b)).neg
  simp only [flatLaplacian, hterm, Finset.sum_neg_distrib]
  rw [Finset.sum_comm, neg_eq_zero]
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [← Finset.mul_sum, sum_invDist_cube_deriv (sub_ne_zero.mpr (hx b hb)), mul_zero]

/-- **The Newtonian potential of the other bodies is harmonic** off the bodies, `ΔΦ = 0`. -/
theorem flatLaplacian_othersPotential (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N)
    {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) : flatLaplacian (othersPotential G m X a) x = 0 := by
  have h : othersPotential G m X a = fun y => ∑ b ∈ ({a}ᶜ : Finset (Fin N)),
      (-G * m b) * invDist (y - X b) := by
    funext y
    rw [othersPotential, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h]
  exact flatLaplacian_weighted _ X _ fun b hb => hx b (by simpa using hb)

/-- **The second potential is harmonic** off the bodies at each time, `Δψ = 0`. -/
theorem flatLaplacian_othersScalarPotential (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S)
    (a : Fin N) {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) :
    flatLaplacian (othersScalarPotential G m X V a) x = 0 := by
  have h : othersScalarPotential G m X V a = fun y => ∑ b ∈ ({a}ᶜ : Finset (Fin N)),
      (-G * m b * (3 / 2 * ∑ j, V b j ^ 2 - potentialAt G m X b)) * invDist (y - X b) := by
    funext y
    rw [othersScalarPotential, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h]
  exact flatLaplacian_weighted _ X _ fun b hb => hx b (by simpa using hb)

/-- The trace of the derivative of the vector-potential kernel,
`Σ_k ∂_k K_k(z, u) = −6 u · z/‖z‖₂³`. -/
theorem sum_dKernelB_single {z : S} (hz : z ≠ 0) (u : S) :
    ∑ k, dKernelB z u (Pi.single k 1) k = -6 * dot u z * invDist z ^ 3 := by
  have h := invDist_sq_mul hz
  have e : ∑ k, dKernelB z u (Pi.single k 1) k = -6 * dot u z * invDist z ^ 3 +
      3 * dot u z * invDist z ^ 3 * (1 - invDist z ^ 2 * ∑ j, z j ^ 2) := by
    simp only [dKernelB, dot, Fin.sum_univ_three, Pi.single_apply]
    simp
    ring
  rw [e, h]
  ring

/-- **The gauge condition of GR36 for point masses**: along any differentiable motion of the
bodies, at a field point `x` away from the bodies `b ≠ a`, the potentials seen by `a` satisfy
`∇ · B + 3 ∂ₜΦ = 0`, the standard post-Newtonian gauge `∂ⱼ g_tj = (1/2) ∂ₜ g_jj` at order `c⁻²`. -/
theorem gauge_othersVectorPotential (G : ℝ) (m : Fin N → ℝ) {X : ℝ → Fin N → S} {t : ℝ}
    (hX : DifferentiableAt ℝ X t) (a : Fin N) {x : S} (hx : ∀ b, b ≠ a → x ≠ X t b) :
    ∑ k, fderiv ℝ (othersVectorPotential G m (X t) (deriv X t) a) x (Pi.single k 1) k +
      3 * deriv (fun s => othersPotential G m (X s) a x) t = 0 := by
  have hdiv : ∑ k, fderiv ℝ (othersVectorPotential G m (X t) (deriv X t) a) x
      (Pi.single k 1) k = 3 * G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)),
        m b * (dot (deriv X t b) (x - X t b) * invDist (x - X t b) ^ 3) := by
    simp only [fderiv_othersVectorPotential_apply G m (X t) (deriv X t) a hx]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [← Finset.mul_sum]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [sum_dKernelB_single (sub_ne_zero.mpr (hx b (by simpa using hb)))]
    ring
  have hd : HasDerivAt (fun s => othersPotential G m (X s) a x)
      (-G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * (-(invDist (x - X t b) ^ 3) *
        dot (x - X t b) (-deriv X t b))) t := by
    refine (HasDerivAt.fun_sum fun b hb => ?_).const_mul (-G)
    have hb' : b ≠ a := by simpa using hb
    have hz : HasDerivAt (fun s => x - X s b) (-deriv X t b) t := by
      simpa using (hasDerivAt_pi.mp hX.hasDerivAt b).const_sub x
    exact (hasDerivAt_invDist_comp hz (sub_ne_zero.mpr (hx b hb'))).const_mul (m b)
  rw [hdiv, hd.deriv, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [dot_neg_right, dot_comm (x - X t b)]
  ring

end ProjectAinos.GeneralRelativity.PostNewtonianField
