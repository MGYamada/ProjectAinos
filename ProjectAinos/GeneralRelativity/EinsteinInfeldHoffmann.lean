/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.PostNewtonian
public import ProjectAinos.Electrodynamics.DarwinPointCharge
import Mathlib.Tactic

/-! # The Einstein–Infeld–Hoffmann Lagrangian

Landau–Lifshitz, §106, the Lagrangian (106.17) of `N` bodies in the second approximation, in
the physical coordinates of `PostNewtonian` (`x ∈ ℝ³` as `NewtonianSpace`, the Euclidean norm
`‖z‖₂ = √(Σ zⱼ²)` (`euclidNorm`), `ε = c⁻²`) with the gravitational constant `G`. A
configuration is given by positions `X : Fin N → ℝ³`, velocities `V` and masses `m`; the
statements about motions use `C²` paths `X : ℝ → Fin N → ℝ³` with the bodies apart.

* The potentials seen by the body `a`, in the gauge of GR36, each body's own potential omitted:
  `othersPotential` `Φ = −G Σ_{b ≠ a} m_b/r_b`, `othersScalarPotential`
  `ψ = −G Σ_{b ≠ a} (m_b/r_b)((3/2) v_b² − U_b)` with `U_b = G Σ_{c ≠ b} m_c/r_bc`
  (`potentialAt`, which contains the body `a`), and `othersVectorPotential`
  `B = −(G/2) Σ_{b ≠ a} (m_b/r_b)(7 v_b + (v_b · n_b) n_b)` (the kernel `kernelB`).
* `testLagrangian`: the test-body Lagrangian of §106 in given potentials;
  `lagrangian_eq_testLagrangian`: it is `PostNewtonianMetricFamily.lagrangian` for the
  potentials of a family.
* `eihLagrangian`: **the Lagrangian (106.17)** with the velocity-pair term `pairVelocity` and the
  three-mass term, the sums over all indices with `1/r_aa = 0`.
* **Target (i), the term-by-term match.** `eihLagrangian_update`: with the other bodies fixed,
  (106.17) as a function of `(x_a, v_a)` is exactly the test-body Lagrangian of `a` in the
  potentials of the others, minus `(G² m_a²/2c²) Σ_{d ≠ a} m_d (1/r_d(x) − 1/r_d(x_a))²`, plus
  terms independent of `(x_a, v_a)` (`eihRest`, `eihLagrangian_update_sub`). Hence
  `hasFDerivAt_eihLagrangian_update`: the first derivatives in `x_a`, `v_a` at the actual
  configuration coincide with those of the test-body Lagrangian, and
  `eulerLagrange_eihLagrangian_eq_test`: **the Euler–Lagrange residual of (106.17) for the body
  `a` is exactly that of the test-body Lagrangian of `a` in the potentials of the others along
  their motion**. The symmetrization is the factor `1/2` of the pair sums and the three-mass
  term, whose dependence on `x_a` through the `U_b` of the others is matched at `x = x_a` only.
* **Target (v), the Euler–Lagrange equations.** `eulerLagrange_testFamily`: the residual of a test
  body in time-dependent potentials is `m (F − ṗ)`; with the explicit derivatives of the kernels
  (`hasFDerivAt_invDist`, `hasDerivAt_kernelB_comp`, `fderiv_othersPotential_apply`, …),
  `eulerLagrange_eihLagrangian`: the residual of (106.17) for the body `a` in the direction `e_k`
  is `m_a (eihForce − eihMomentumRate)` in the positions, velocities and accelerations.
  `eihAcceleration`: the explicit acceleration `a_N + F − ṗ(a_N)`;
  `eulerLagrange_acceleration_error`: for nonzero masses, mutual distances `≥ δ` and speeds
  `≤ V₀`, a motion satisfying the Euler–Lagrange equations at `t` has the accelerations
  `eihAcceleration` up to `C/c⁴`, uniformly for `c ≥ c₁` (`norm_sub_eihAcceleration_le`, the
  algebraic core: the equations are linear in the accelerations, with the coupling
  `rateLinear` bounded by `abs_rateLinear_le`).
* **Target (ii).** `eihLagrangian_perm`: invariance under relabelling the bodies;
  `newtonAcceleration_perm`.
* **Target (iii).** `eihLagrangian_eq_add`: (106.17) is the Newtonian Lagrangian
  `newtonLagrangian` plus `c⁻²` times `eihCorrectionLagrangian`; `tendsto_eihLagrangian`,
  `eulerLagrange_newtonLagrangian` (Newton's equations), `tendsto_eulerLagrange_eihLagrangian`,
  `tendsto_eihAcceleration`: the limits as `c → ∞`.
* **Target (iv).** `eulerLagrange_testMass`: for the mass `m_a = μ ≠ 0`, the residual of the body
  `a` divided by `μ` is that of a unit test mass in the potentials of the other bodies alone
  (`others_update_config`: with `m_a = 0` they do not depend on `x_a`, `v_a`) plus `μ` times an
  explicit three-mass term; `tendsto_eulerLagrange_testMass`: the limit `μ → 0`;
  `othersScalarPotential_update_mass`: the field felt by a light body.
  `testLagrangian_eq_lagrangian`, `testMass_acceleration_error`: for a post-Newtonian family
  with the potentials of the other bodies, the limit equation is the Euler–Lagrange equation of
  `PostNewtonianMetricFamily.lagrangian 1 c`, so `eulerLagrange_acceleration_error` of
  `PostNewtonian` gives the test-body acceleration.
* Instances: `eihLagrangian_two` (the two-body Lagrangian), `exists_eulerLagrange` (the
  Euler–Lagrange equations hold at any instant along the quadratic motion with the accelerations
  given by a contraction), `exists_eulerLagrange_two` (two unit masses at `±(1, 0, 0)`),
  `exists_family_rest` (a post-Newtonian family with the potentials of a body at rest, for
  `testMass_acceleration_error`).

Not in this file: the field side (the potentials of smooth sources and the Einstein equations to
the stated order), and the convergence of solutions of the Einstein equations for `N` bodies to
the motion of (106.17), which needs the well-posedness of quasilinear hyperbolic systems, absent
from Mathlib.
-/

@[expose] public section
noncomputable section

open ContinuousLinearMap Set Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.EinsteinInfeldHoffmann

open NewtonianMetricFamily

local notation "S" => NewtonianSpace

/-! ### Kernels of a point mass -/

/-- The Euclidean dot product `v · w = Σ vⱼ wⱼ` on `ℝ³`. -/
def dot (v w : S) : ℝ := ∑ j, v j * w j

/-- The Euclidean norm `‖z‖₂ = √(Σ zⱼ²)` on `ℝ³` (the norm of `NewtonianSpace` is the sup norm). -/
def euclidNorm (z : S) : ℝ := √(∑ j, z j ^ 2)

/-- The inverse distance `1/‖z‖₂`; it is `0` at `z = 0` (`0⁻¹ = 0`). -/
def invDist (z : S) : ℝ := (euclidNorm z)⁻¹

/-- The linear form `h ↦ z · h`. -/
def dotL (z : S) : S →L[ℝ] ℝ := ∑ j, z j • (proj j : S →L[ℝ] ℝ)

@[simp] theorem dotL_apply (z h : S) : dotL z h = dot z h := by
  simp [dotL, dot]

theorem dot_comm (v w : S) : dot v w = dot w v := by
  simp only [dot, mul_comm]

theorem dot_neg_right (v w : S) : dot v (-w) = -dot v w := by
  simp [dot]

theorem dot_sub_right (u v w : S) : dot u (v - w) = dot u v - dot u w := by
  simp [dot, mul_sub]

theorem dot_add_left (u v w : S) : dot (u + v) w = dot u w + dot v w := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_zero_left (w : S) : dot 0 w = 0 := by simp [dot]

theorem dot_zero_right (w : S) : dot w 0 = 0 := by simp [dot]

theorem dot_smul_left (r : ℝ) (v w : S) : dot (r • v) w = r * dot v w := by
  simp [dot, Finset.mul_sum, mul_assoc]

theorem dot_smul_right (r : ℝ) (v w : S) : dot v (r • w) = r * dot v w := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sum_sq_neg (z : S) : ∑ j, (-z) j ^ 2 = ∑ j, z j ^ 2 := by simp

theorem euclidNorm_neg (z : S) : euclidNorm (-z) = euclidNorm z := by
  rw [euclidNorm, euclidNorm, sum_sq_neg]

theorem invDist_neg (z : S) : invDist (-z) = invDist z := by
  rw [invDist, invDist, euclidNorm_neg]

theorem invDist_sub_comm (x y : S) : invDist (x - y) = invDist (y - x) := by
  rw [← neg_sub, invDist_neg]

@[simp] theorem invDist_zero : invDist 0 = 0 := by simp [invDist, euclidNorm]

theorem sum_sq_pos {z : S} (hz : z ≠ 0) : 0 < ∑ j, z j ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
  exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi)))
    (Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i))

theorem euclidNorm_pos {z : S} (hz : z ≠ 0) : 0 < euclidNorm z :=
  Real.sqrt_pos.mpr (sum_sq_pos hz)

theorem euclidNorm_nonneg (z : S) : 0 ≤ euclidNorm z := Real.sqrt_nonneg _

theorem invDist_nonneg (z : S) : 0 ≤ invDist z := inv_nonneg.mpr (euclidNorm_nonneg z)

theorem invDist_pos {z : S} (hz : z ≠ 0) : 0 < invDist z := inv_pos.mpr (euclidNorm_pos hz)

theorem euclidNorm_sq (z : S) : euclidNorm z ^ 2 = ∑ j, z j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (z j))

theorem invDist_sq_mul {z : S} (hz : z ≠ 0) : invDist z ^ 2 * ∑ j, z j ^ 2 = 1 := by
  rw [← euclidNorm_sq, invDist, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 (euclidNorm_pos hz).ne')]

theorem abs_component_le_euclidNorm (z : S) (k : Fin 3) : |z k| ≤ euclidNorm z := by
  rw [euclidNorm, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ k))

/-- The components of the unit vector `z/‖z‖₂` are at most `1` (and `0` at `z = 0`). -/
theorem abs_invDist_mul_le (z : S) (k : Fin 3) : |invDist z * z k| ≤ 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [abs_mul, abs_of_nonneg (invDist_nonneg z), invDist, inv_mul_le_iff₀ (euclidNorm_pos hz),
    mul_one]
  exact abs_component_le_euclidNorm z k

theorem invDist_le {z : S} {δ : ℝ} (hδ : 0 < δ) (h : δ ≤ euclidNorm z) : invDist z ≤ δ⁻¹ :=
  inv_anti₀ hδ h

theorem hasFDerivAt_sum_sq (z : S) :
    HasFDerivAt (fun y : S => ∑ j, y j ^ 2) ((2 : ℝ) • dotL z) z := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    ((proj j : S →L[ℝ] ℝ).hasFDerivAt (x := z)).pow 2
  convert h using 1
  · funext y
    simp
  · ext w
    simp [dotL, Finset.mul_sum, mul_assoc]

/-- **The gradient of the inverse distance**, `∇(1/‖z‖₂) = −z/‖z‖₂³`. -/
theorem hasFDerivAt_invDist {z : S} (hz : z ≠ 0) :
    HasFDerivAt invDist (-(invDist z ^ 3) • dotL z) z := by
  have hs := (hasFDerivAt_sum_sq z).sqrt (sum_sq_pos hz).ne'
  have hn : euclidNorm z ≠ 0 := (euclidNorm_pos hz).ne'
  have h : HasFDerivAt (fun y => (euclidNorm y)⁻¹) _ z :=
    (hasDerivAt_inv hn).comp_hasFDerivAt z hs
  refine h.congr_fderiv ?_
  ext w
  simp only [smul_apply, dotL_apply, smul_eq_mul]
  change -(euclidNorm z ^ 2)⁻¹ * ((1 / (2 * euclidNorm z)) * (2 * dot z w)) =
    -(euclidNorm z)⁻¹ ^ 3 * dot z w
  field_simp

/-- The derivative of the inverse distance along a curve. -/
theorem hasDerivAt_invDist_comp {z : ℝ → S} {z' : S} {s : ℝ} (hz : HasDerivAt z z' s)
    (h0 : z s ≠ 0) :
    HasDerivAt (fun r => invDist (z r)) (-(invDist (z s) ^ 3) * dot (z s) z') s := by
  have h := (hasFDerivAt_invDist h0).comp_hasDerivAt s hz
  exact h.congr_deriv (by simp)

/-- The vector-potential kernel `(7u + (u · n) n)/‖z‖₂`, `n = z/‖z‖₂`, of a point mass with the
velocity `u` at the separation `z`; it is `0` at `z = 0`. -/
def kernelB (z u : S) : S := fun k => 7 * u k * invDist z + dot u z * z k * invDist z ^ 3

/-- The derivative of `kernelB · u` at `z` in the direction `h`. -/
def dKernelB (z u h : S) : S := fun k =>
  -7 * u k * invDist z ^ 3 * dot z h + (dot u h * z k + dot u z * h k) * invDist z ^ 3 -
    3 * dot u z * z k * invDist z ^ 5 * dot z h

theorem hasDerivAt_dot_comp {u w : ℝ → S} {u' w' : S} {s : ℝ} (hu : HasDerivAt u u' s)
    (hw : HasDerivAt w w' s) :
    HasDerivAt (fun r => dot (u r) (w r)) (dot u' (w s) + dot (u s) w') s := by
  have h : HasDerivAt (fun r => dot (u r) (w r))
      (∑ j, (u' j * w s j + u s j * w' j)) s :=
    HasDerivAt.fun_sum fun j _ => (hasDerivAt_pi.mp hu j).mul (hasDerivAt_pi.mp hw j)
  refine h.congr_deriv ?_
  simp [dot, Finset.sum_add_distrib]

/-- **The derivative of the vector-potential kernel along a curve** `(z(s), u(s))`. -/
theorem hasDerivAt_kernelB_comp {z u : ℝ → S} {z' u' : S} {s : ℝ} (hz : HasDerivAt z z' s)
    (hu : HasDerivAt u u' s) (h0 : z s ≠ 0) (k : Fin 3) :
    HasDerivAt (fun r => kernelB (z r) (u r) k)
      (dKernelB (z s) (u s) z' k + kernelB (z s) u' k) s := by
  have hι := hasDerivAt_invDist_comp hz h0
  have huz := hasDerivAt_dot_comp hu hz
  have h1 := ((hasDerivAt_pi.mp hu k).const_mul 7).mul hι
  have h2 := (huz.mul (hasDerivAt_pi.mp hz k)).mul (hι.pow 3)
  have h : HasDerivAt (fun r => kernelB (z r) (u r) k) _ s := h1.add h2
  refine h.congr_deriv ?_
  simp only [dKernelB, kernelB, Nat.cast_ofNat, Pi.mul_apply, Pi.pow_apply]
  ring

theorem kernelB_zero_left (u : S) : kernelB 0 u = 0 := by
  funext k
  simp [kernelB]

theorem kernelB_zero_right (z : S) : kernelB z 0 = 0 := by
  funext k
  simp [kernelB, dot_zero_left]

theorem dKernelB_zero_left (u h : S) : dKernelB 0 u h = 0 := by
  funext k
  simp [dKernelB]

/-- The contraction `Σ_k K_k(z, u) w_k = (7 u · w + (u · n)(w · n)) /‖z‖₂`. -/
theorem sum_kernelB_mul (z u w : S) :
    ∑ k, kernelB z u k * w k = 7 * dot u w * invDist z + dot u z * dot w z * invDist z ^ 3 := by
  simp only [kernelB, dot, Fin.sum_univ_three]
  ring

/-! ### The potentials of the bodies -/

variable {N : ℕ}

/-- The Newtonian potential `U_b = G Σ_{c ≠ b} m_c/r_bc` (positive) at the body `b` produced by
the other bodies; the term `c = b` vanishes since `1/r_bb = 0⁻¹ = 0`. -/
def potentialAt (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (b : Fin N) : ℝ :=
  G * ∑ c, m c * invDist (X b - X c)

/-- **The Newtonian potential seen by the body `a`**, `Φ(x) = −G Σ_{b ≠ a} m_b/‖x − x_b‖₂`, with the
body's own potential omitted. -/
def othersPotential (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N) (x : S) : ℝ :=
  -G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * invDist (x - X b)

/-- **The second scalar potential seen by the body `a`**,
`ψ(x) = −G Σ_{b ≠ a} (m_b/‖x − x_b‖₂)((3/2) v_b² − U_b)`, the field of the system of point masses
in the gauge of GR36, with the body's own potential omitted. -/
def othersScalarPotential (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) (x : S) : ℝ :=
  -G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)),
    m b * invDist (x - X b) * (3 / 2 * ∑ j, V b j ^ 2 - potentialAt G m X b)

/-- **The vector potential seen by the body `a`** in the gauge of GR36,
`B(x) = −(G/2) Σ_{b ≠ a} (m_b/r_b)(7 v_b + (v_b · n_b) n_b)`, `r_b n_b = x − x_b`. -/
def othersVectorPotential (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) (x : S) : S :=
  fun k => -(G / 2) * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * kernelB (x - X b) (V b) k

/-! ### The test-body Lagrangian and the Lagrangian (106.17) -/

/-- The test-body Lagrangian of §106 in given static potentials `Φ`, `ψ`, `B` on space:
`−mc² + mv²/2 − mΦ + (m/c²)(v⁴/8 − (3/2)Φv² − Φ²/2 − ψ + B · v)`. With the potentials of a
post-Newtonian family at the time `t` it is `PostNewtonianMetricFamily.lagrangian`
(`lagrangian_eq_testLagrangian`). -/
def testLagrangian (m c : ℝ) (Φ ψ : S → ℝ) (B : S → S) (z : S × S) : ℝ :=
  -m * c ^ 2 + m * ((∑ j, z.2 j ^ 2) / 2 - Φ z.1 +
    epsilon c * ((∑ j, z.2 j ^ 2) ^ 2 / 8 - 3 / 2 * Φ z.1 * ∑ j, z.2 j ^ 2 -
      Φ z.1 ^ 2 / 2 - ψ z.1 + ∑ j, B z.1 j * z.2 j))

/-- The test-body Lagrangian of a post-Newtonian family at the time `t` is `testLagrangian` in its
potentials at `t`. -/
theorem lagrangian_eq_testLagrangian {U : TopologicalSpace.Opens NewtonianCoordinates}
    (f : PostNewtonian.PostNewtonianMetricFamily U) (m c t : ℝ) :
    f.lagrangian m c t = testLagrangian m c (fun x => f.potential (Fin.cons t x))
      (fun x => f.scalarPotential (Fin.cons t x)) (fun x => f.vectorPotential (Fin.cons t x)) :=
  rfl

/-- The velocity factor `3u² − (7/2) u · w − (1/2)(u · n)(w · n)` of the pair terms of (106.17),
`n = z/‖z‖₂`. -/
def pairVelocity (u w z : S) : ℝ :=
  3 * (∑ j, u j ^ 2) - 7 / 2 * dot u w - 1 / 2 * dot u z * dot w z * invDist z ^ 2

/-- **The Lagrangian of Einstein, Infeld and Hoffmann (106.17)** of `N` bodies with the masses
`m`, positions `z.1` and velocities `z.2`:

`L = Σ_a m_a v_a²/2 + Σ_a m_a v_a⁴/(8c²) + Σ_{a ≠ b} G m_a m_b/(2 r_ab)`
`  + Σ_{a ≠ b} (G m_a m_b/(2c² r_ab)) (3v_a² − (7/2) v_a · v_b − (1/2)(v_a · n_ab)(v_b · n_ab))`
`  − Σ_{b ≠ a, d ≠ a} G² m_a m_b m_d/(2c² r_ab r_ad)`,

with `r_ab n_ab = x_a − x_b`. The sums run over all indices: the terms with a repeated index
vanish, since `1/r_aa = 0⁻¹ = 0` (`invDist_zero`), so the sums are those over `a ≠ b` of
(106.17); the three-mass sum is `Σ_a m_a (Σ_{b ≠ a} m_b/r_ab)²` (`sum_three_eq`). -/
def eihLagrangian (G : ℝ) (m : Fin N → ℝ) (c : ℝ) : Mechanics.Lagrangian (Fin N → S) :=
  fun _ z =>
    ∑ a, (m a * (∑ j, z.2 a j ^ 2) / 2 + epsilon c * (m a * (∑ j, z.2 a j ^ 2) ^ 2 / 8)) +
    G / 2 * ∑ a, ∑ b, m a * m b * invDist (z.1 a - z.1 b) +
    epsilon c * (G / 2 * ∑ a, ∑ b, m a * m b * invDist (z.1 a - z.1 b) *
      pairVelocity (z.2 a) (z.2 b) (z.1 a - z.1 b)) -
    epsilon c * (G ^ 2 / 2 * ∑ a, ∑ b, ∑ d,
      m a * m b * m d * invDist (z.1 a - z.1 b) * invDist (z.1 a - z.1 d))

/-- The three-mass sum is `Σ_a m_a (Σ_b m_b/r_ab)²`. -/
theorem sum_three_eq (m : Fin N → ℝ) (X : Fin N → S) :
    ∑ a, ∑ b, ∑ d, m a * m b * m d * invDist (X a - X b) * invDist (X a - X d) =
      ∑ a, m a * (∑ b, m b * invDist (X a - X b)) ^ 2 := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- A double sum with the index `a` split off. -/
private theorem sum_sum_split (F : Fin N → Fin N → ℝ) (a : Fin N) :
    ∑ d, ∑ b, F d b = F a a + ∑ b ∈ ({a}ᶜ : Finset (Fin N)), F a b +
      ∑ d ∈ ({a}ᶜ : Finset (Fin N)), F d a +
      ∑ d ∈ ({a}ᶜ : Finset (Fin N)), ∑ b ∈ ({a}ᶜ : Finset (Fin N)), F d b := by
  rw [Fintype.sum_eq_add_sum_compl a, Fintype.sum_eq_add_sum_compl a (F a),
    Finset.sum_congr rfl fun d _ => Fintype.sum_eq_add_sum_compl a (F d),
    Finset.sum_add_distrib]
  ring

theorem potentialAt_split (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a b : Fin N) :
    potentialAt G m X b = G * (m a * invDist (X b - X a) +
      ∑ c ∈ ({a}ᶜ : Finset (Fin N)), m c * invDist (X b - X c)) := by
  rw [potentialAt, Fintype.sum_eq_add_sum_compl a]

/-- The terms of (106.17) left when the body `a` is moved: the rest energy `m_a c²` of the
test-body Lagrangian, the Lagrangian of the other bodies, and the three-mass terms in which the
body `a` enters only through its actual position. -/
def eihRest (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V : Fin N → S) (a : Fin N) : ℝ :=
  m a * c ^ 2 + ∑ d ∈ ({a}ᶜ : Finset (Fin N)),
      (m d * (∑ j, V d j ^ 2) / 2 + epsilon c * (m d * (∑ j, V d j ^ 2) ^ 2 / 8)) +
    G / 2 * ∑ d ∈ ({a}ᶜ : Finset (Fin N)), ∑ b ∈ ({a}ᶜ : Finset (Fin N)),
      m d * m b * invDist (X d - X b) +
    epsilon c * (G / 2 * ∑ d ∈ ({a}ᶜ : Finset (Fin N)), ∑ b ∈ ({a}ᶜ : Finset (Fin N)),
      m d * m b * invDist (X d - X b) * pairVelocity (V d) (V b) (X d - X b)) -
    epsilon c * (G ^ 2 / 2 * ∑ d ∈ ({a}ᶜ : Finset (Fin N)), m d *
      ((∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * invDist (X d - X b)) ^ 2 -
        m a ^ 2 * invDist (X d - X a) ^ 2))

theorem pairVelocity_neg (u w z : S) : pairVelocity u w (-z) = pairVelocity u w z := by
  simp only [pairVelocity, dot_neg_right, invDist_neg]
  ring

private theorem sum_lin2 {ι : Type} (s : Finset ι) (f g : ι → ℝ) (p q : ℝ) :
    p * ∑ i ∈ s, f i + q * ∑ i ∈ s, g i = ∑ i ∈ s, (p * f i + q * g i) := by
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

private theorem sum_lin3 {ι : Type} (s : Finset ι) (f g h : ι → ℝ) (p q r : ℝ) :
    p * ∑ i ∈ s, f i + q * ∑ i ∈ s, g i + r * ∑ i ∈ s, h i =
      ∑ i ∈ s, (p * f i + q * g i + r * h i) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum]

private theorem sum_lin4 {ι : Type} (s : Finset ι) (f g h k : ι → ℝ) (p q r t : ℝ) :
    p * ∑ i ∈ s, f i + q * ∑ i ∈ s, g i + r * ∑ i ∈ s, h i + t * ∑ i ∈ s, k i =
      ∑ i ∈ s, (p * f i + q * g i + r * h i + t * k i) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]

/-- **The Lagrangian (106.17) seen by one body.** With the other bodies at their positions and
velocities `X`, `V`, the Lagrangian of the system as a function of the position `x` and the
velocity `v` of the body `a` is the test-body Lagrangian of `a` in the potentials `Φ`, `ψ`, `B`
of the others (`othersPotential`, `othersScalarPotential`, `othersVectorPotential`), minus the
three-mass term `(G² m_a²/2c²) Σ_{d ≠ a} m_d (1/r_d(x) − 1/r_d(x_a))²`, which vanishes to second
order at the actual position `x = x_a`, plus terms independent of `(x, v)` (`eihRest`). An exact
identity for every configuration. -/
theorem eihLagrangian_update (G : ℝ) (m : Fin N → ℝ) (c s : ℝ) (X V : Fin N → S) (a : Fin N)
    (x v : S) :
    eihLagrangian G m c s (Function.update X a x, Function.update V a v) =
      testLagrangian (m a) c (othersPotential G m X a) (othersScalarPotential G m X V a)
          (othersVectorPotential G m X V a) (x, v) -
        epsilon c * (G ^ 2 * m a ^ 2 / 2) *
          ∑ d ∈ ({a}ᶜ : Finset (Fin N)), m d * (invDist (X d - x) - invDist (X d - X a)) ^ 2 +
        eihRest G m c X V a := by
  set Y := Function.update X a x with hY
  set W := Function.update V a v with hW
  obtain ⟨C, hC⟩ : ∃ C : Finset (Fin N), C = {a}ᶜ := ⟨_, rfl⟩
  have hYa : Y a = x := by simp [hY]
  have hWa : W a = v := by simp [hW]
  have hne : ∀ d ∈ C, d ≠ a := fun d hd => by simpa [hC] using hd
  have hYd : ∀ d ∈ C, Y d = X d := fun d hd => Function.update_of_ne (hne d hd) _ _
  have hWd : ∀ d ∈ C, W d = V d := fun d hd => Function.update_of_ne (hne d hd) _ _
  set ε := epsilon c with hε
  set vv := ∑ j, v j ^ 2 with hvv
  obtain ⟨t1, ht1⟩ : ∃ t, t = ∑ b ∈ C, m b * invDist (x - X b) := ⟨_, rfl⟩
  obtain ⟨t2, ht2⟩ : ∃ t, t = ∑ b ∈ C, m b * invDist (x - X b) * ∑ j, V b j ^ 2 := ⟨_, rfl⟩
  obtain ⟨t3, ht3⟩ : ∃ t, t = ∑ b ∈ C, m b * invDist (x - X b) * dot v (V b) := ⟨_, rfl⟩
  obtain ⟨t4, ht4⟩ : ∃ t, t = ∑ b ∈ C, m b * invDist (x - X b) ^ 3 * dot v (x - X b) *
      dot (V b) (x - X b) := ⟨_, rfl⟩
  obtain ⟨t5, ht5⟩ : ∃ t, t = ∑ b ∈ C, m b * invDist (x - X b) * invDist (X b - X a) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Fin N → ℝ, R = fun b => ∑ e ∈ C, m e * invDist (X b - X e) := ⟨_, rfl⟩
  obtain ⟨t6, ht6⟩ : ∃ t, t = ∑ b ∈ C, m b * invDist (x - X b) * R b := ⟨_, rfl⟩
  obtain ⟨t8, ht8⟩ : ∃ t, t = ∑ b ∈ C, m b * invDist (x - X b) ^ 2 := ⟨_, rfl⟩
  obtain ⟨t9, ht9⟩ : ∃ t, t = ∑ b ∈ C, m b * invDist (X b - X a) ^ 2 := ⟨_, rfl⟩
  obtain ⟨rr, hrr⟩ : ∃ t, t = ∑ b ∈ C, m b * R b ^ 2 := ⟨_, rfl⟩
  -- the left side
  have hkin : ∑ d, (m d * (∑ j, W d j ^ 2) / 2 + ε * (m d * (∑ j, W d j ^ 2) ^ 2 / 8)) =
      m a * vv / 2 + ε * (m a * vv ^ 2 / 8) +
        ∑ d ∈ C, (m d * (∑ j, V d j ^ 2) / 2 + ε * (m d * (∑ j, V d j ^ 2) ^ 2 / 8)) := by
    rw [Fintype.sum_eq_add_sum_compl a, hWa, ← hC]
    congr 1
    exact Finset.sum_congr rfl fun d hd => by rw [hWd d hd]
  have hnewt : ∑ d, ∑ b, m d * m b * invDist (Y d - Y b) =
      2 * (m a * t1) + ∑ d ∈ C, ∑ b ∈ C, m d * m b * invDist (X d - X b) := by
    rw [sum_sum_split _ a, ← hC]
    simp only [sub_self, invDist_zero, mul_zero, zero_add]
    have h1 : ∑ b ∈ C, m a * m b * invDist (Y a - Y b) = m a * t1 := by
      rw [ht1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b hb => by rw [hYa, hYd b hb]; ring
    have h2 : ∑ d ∈ C, m d * m a * invDist (Y d - Y a) = m a * t1 := by
      rw [ht1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b hb => by rw [hYa, hYd b hb, invDist_sub_comm]; ring
    have h3 : ∑ d ∈ C, ∑ b ∈ C, m d * m b * invDist (Y d - Y b) =
        ∑ d ∈ C, ∑ b ∈ C, m d * m b * invDist (X d - X b) :=
      Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun b hb => by
        rw [hYd d hd, hYd b hb]
    rw [h1, h2, h3]
    ring
  have hvel : ∑ d, ∑ b, m d * m b * invDist (Y d - Y b) *
        pairVelocity (W d) (W b) (Y d - Y b) =
      m a * (3 * vv * t1 + 3 * t2 - 7 * t3 - t4) + ∑ d ∈ C, ∑ b ∈ C,
        m d * m b * invDist (X d - X b) * pairVelocity (V d) (V b) (X d - X b) := by
    rw [sum_sum_split _ a, ← hC]
    simp only [sub_self, invDist_zero, mul_zero, zero_mul, zero_add]
    have h1 : ∑ b ∈ C, m a * m b * invDist (Y a - Y b) * pairVelocity (W a) (W b) (Y a - Y b) +
        ∑ d ∈ C, m d * m a * invDist (Y d - Y a) * pairVelocity (W d) (W a) (Y d - Y a) =
        m a * (3 * vv * t1 + 3 * t2 - 7 * t3 - t4) := by
      have e : m a * (3 * vv * t1 + 3 * t2 - 7 * t3 - t4) =
          (3 * vv * m a) * t1 + (3 * m a) * t2 + (-7 * m a) * t3 + (-m a) * t4 := by ring
      rw [← Finset.sum_add_distrib, e, ht1, ht2, ht3, ht4, sum_lin4]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [hYa, hWa, hYd b hb, hWd b hb, invDist_sub_comm (X b) x, ← neg_sub x (X b),
        pairVelocity_neg]
      simp only [pairVelocity, dot_comm (V b) v, ← hvv]
      ring
    have h3 : ∑ d ∈ C, ∑ b ∈ C, m d * m b * invDist (Y d - Y b) *
        pairVelocity (W d) (W b) (Y d - Y b) = ∑ d ∈ C, ∑ b ∈ C,
          m d * m b * invDist (X d - X b) * pairVelocity (V d) (V b) (X d - X b) :=
      Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun b hb => by
        rw [hYd d hd, hYd b hb, hWd d hd, hWd b hb]
    rw [h3]
    linear_combination h1
  have htrip : ∑ d, ∑ b, ∑ e, m d * m b * m e * invDist (Y d - Y b) * invDist (Y d - Y e) =
      m a * t1 ^ 2 + (m a ^ 2 * t8 + 2 * m a * t6 + rr) := by
    rw [sum_three_eq, Fintype.sum_eq_add_sum_compl a, ← hC]
    have hSa : ∑ b, m b * invDist (Y a - Y b) = t1 := by
      rw [Fintype.sum_eq_add_sum_compl a, sub_self, invDist_zero, mul_zero, zero_add, ← hC, ht1]
      exact Finset.sum_congr rfl fun b hb => by rw [hYa, hYd b hb]
    have hSd : ∀ d ∈ C, ∑ b, m b * invDist (Y d - Y b) = m a * invDist (x - X d) + R d := by
      intro d hd
      rw [Fintype.sum_eq_add_sum_compl a, hYa, hYd d hd, invDist_sub_comm, hR, ← hC]
      congr 1
      exact Finset.sum_congr rfl fun b hb => by rw [hYd b hb]
    have key : ∑ d ∈ C, m d * (∑ b, m b * invDist (Y d - Y b)) ^ 2 =
        m a ^ 2 * t8 + 2 * m a * t6 + rr := by
      have e : m a ^ 2 * t8 + 2 * m a * t6 + rr = m a ^ 2 * t8 + 2 * m a * t6 + 1 * rr := by ring
      rw [e, ht8, ht6, hrr, sum_lin3]
      exact Finset.sum_congr rfl fun d hd => by rw [hSd d hd]; ring
    rw [hSa, key]
  -- the right side
  have hΦ : othersPotential G m X a x = -G * t1 := by rw [othersPotential, ← hC, ht1]
  have hψ : othersScalarPotential G m X V a x = -G * (3 / 2 * t2 - G * m a * t5 - G * t6) := by
    have e : 3 / 2 * t2 - G * m a * t5 - G * t6 =
        3 / 2 * t2 + (-G * m a) * t5 + (-G) * t6 := by ring
    rw [othersScalarPotential, ← hC, e, ht2, ht5, ht6, sum_lin3]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [potentialAt_split G m X a b, hR, ← hC]
    ring
  have hB : ∑ j, othersVectorPotential G m X V a x j * v j = -(G / 2) * (7 * t3 + t4) := by
    have hL : ∑ j, othersVectorPotential G m X V a x j * v j =
        ∑ b ∈ C, -(G / 2) * (m b * ∑ j, kernelB (x - X b) (V b) j * v j) := by
      simp only [othersVectorPotential, ← hC, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => by ring
    have e : -(G / 2) * (7 * t3 + t4) = (-(G / 2) * 7) * t3 + (-(G / 2)) * t4 := by ring
    rw [hL, e, ht3, ht4, sum_lin2]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [sum_kernelB_mul, dot_comm (V b) v]
    ring
  have hQ : ∑ d ∈ C, m d * (invDist (X d - x) - invDist (X d - X a)) ^ 2 = t8 - 2 * t5 + t9 := by
    have e : t8 - 2 * t5 + t9 = 1 * t8 + (-2) * t5 + 1 * t9 := by ring
    rw [e, ht8, ht5, ht9, sum_lin3]
    exact Finset.sum_congr rfl fun d _ => by rw [invDist_sub_comm (X d) x]; ring
  have hrest : ∑ d ∈ C, m d * ((∑ b ∈ C, m b * invDist (X d - X b)) ^ 2 -
      m a ^ 2 * invDist (X d - X a) ^ 2) = rr - m a ^ 2 * t9 := by
    have e : rr - m a ^ 2 * t9 = 1 * rr + (-m a ^ 2) * t9 := by ring
    rw [e, hrr, ht9, sum_lin2]
    exact Finset.sum_congr rfl fun d _ => by rw [hR]; ring
  simp only [eihLagrangian, testLagrangian, eihRest, ← hC]
  rw [hkin, hnewt, hvel, htrip, hΦ, hψ, hB, hQ, hrest, ← hε, ← hvv]
  ring

/-- **The restriction to one body, without the rest.** The difference between the Lagrangian of
the system with the body `a` moved to `(x, v)` and the test-body Lagrangian of `a` in the field of
the others, corrected by the three-mass term, does not depend on `(x, v)`. -/
theorem eihLagrangian_update_sub (G : ℝ) (m : Fin N → ℝ) (c s : ℝ) (X V : Fin N → S)
    (a : Fin N) (x v : S) :
    eihLagrangian G m c s (Function.update X a x, Function.update V a v) -
        testLagrangian (m a) c (othersPotential G m X a) (othersScalarPotential G m X V a)
          (othersVectorPotential G m X V a) (x, v) +
        epsilon c * (G ^ 2 * m a ^ 2 / 2) *
          ∑ d ∈ ({a}ᶜ : Finset (Fin N)), m d * (invDist (X d - x) - invDist (X d - X a)) ^ 2 =
      eihLagrangian G m c s (X, V) -
        testLagrangian (m a) c (othersPotential G m X a) (othersScalarPotential G m X V a)
          (othersVectorPotential G m X V a) (X a, V a) := by
  have h1 := eihLagrangian_update G m c s X V a x v
  have h2 := eihLagrangian_update G m c s X V a (X a) (V a)
  simp only [Function.update_eq_self, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, Finset.sum_const_zero, sub_zero] at h2
  rw [h1, h2]
  ring

/-! ### Smoothness -/

theorem contDiffAt_invDist {z : S} (hz : z ≠ 0) {n : WithTop ℕ∞} : ContDiffAt ℝ n invDist z := by
  have hs : ContDiffAt ℝ n (fun y : S => ∑ j, y j ^ 2) z := by fun_prop
  exact (hs.sqrt (sum_sq_pos hz).ne').inv (euclidNorm_pos hz).ne'

theorem differentiableAt_invDist {z : S} (hz : z ≠ 0) : DifferentiableAt ℝ invDist z :=
  (hasFDerivAt_invDist hz).differentiableAt

/-- The inverse distance of two bodies is smooth in the configuration where they are apart, and
constant (`0`) for a repeated index. -/
theorem contDiffAt_invDist_pair {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (p : Z → Fin N → S) (hp : ContDiff ℝ ∞ p) {z : Z} (a b : Fin N)
    (hab : a ≠ b → p z a ≠ p z b) :
    ContDiffAt ℝ ∞ (fun y => invDist (p y a - p y b)) z := by
  rcases eq_or_ne a b with rfl | h
  · simp only [sub_self, invDist_zero]
    exact contDiffAt_const
  · have hd : ContDiff ℝ ∞ fun y => p y a - p y b :=
      (contDiff_pi.mp hp a).sub (contDiff_pi.mp hp b)
    exact ContDiffAt.comp (g := invDist) (f := fun y => p y a - p y b) z
      (contDiffAt_invDist (sub_ne_zero.mpr (hab h))) hd.contDiffAt

/-- **The Lagrangian (106.17) is smooth on the collision-free configurations.** -/
theorem contDiffAt_eihLagrangian (G : ℝ) (m : Fin N → ℝ) (c s : ℝ)
    {z : (Fin N → S) × (Fin N → S)} (hz : ∀ a b, a ≠ b → z.1 a ≠ z.1 b) :
    ContDiffAt ℝ ∞ (eihLagrangian G m c s) z := by
  have hι : ∀ a b, ContDiffAt ℝ ∞
      (fun y : (Fin N → S) × (Fin N → S) => invDist (y.1 a - y.1 b)) z := fun a b =>
    contDiffAt_invDist_pair (fun y : (Fin N → S) × (Fin N → S) => y.1) contDiff_fst a b
      (hz a b)
  have hv : ∀ a j, ContDiffAt ℝ ∞ (fun y : (Fin N → S) × (Fin N → S) => y.2 a j) z :=
    fun a j => by fun_prop
  have hx : ∀ a j, ContDiffAt ℝ ∞ (fun y : (Fin N → S) × (Fin N → S) => y.1 a j) z :=
    fun a j => by fun_prop
  unfold eihLagrangian pairVelocity dot
  refine (((ContDiffAt.sum fun a _ => ?_).add ?_).add ?_).sub ?_
  · exact (((contDiffAt_const.mul (ContDiffAt.sum fun j _ => (hv a j).pow 2)).div_const _)).add
      (contDiffAt_const.mul ((contDiffAt_const.mul
        ((ContDiffAt.sum fun j _ => (hv a j).pow 2).pow 2)).div_const _))
  · exact contDiffAt_const.mul (ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ =>
      contDiffAt_const.mul (hι a b))
  · refine contDiffAt_const.mul (contDiffAt_const.mul (ContDiffAt.sum fun a _ =>
      ContDiffAt.sum fun b _ => (contDiffAt_const.mul (hι a b)).mul ?_))
    refine ((contDiffAt_const.mul (ContDiffAt.sum fun j _ => (hv a j).pow 2)).sub
      (contDiffAt_const.mul (ContDiffAt.sum fun j _ => (hv a j).mul (hv b j)))).sub ?_
    refine ((contDiffAt_const.mul (ContDiffAt.sum fun j _ => (hv a j).mul
      ((hx a j).sub (hx b j)))).mul (ContDiffAt.sum fun j _ => (hv b j).mul
      ((hx a j).sub (hx b j)))).mul ((hι a b).pow 2)
  · exact contDiffAt_const.mul (contDiffAt_const.mul (ContDiffAt.sum fun a _ =>
      ContDiffAt.sum fun b _ => ContDiffAt.sum fun d _ =>
        (contDiffAt_const.mul (hι a b)).mul (hι a d)))

/-! ### The term-by-term match -/

theorem differentiableAt_othersPotential (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N)
    {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) : DifferentiableAt ℝ (othersPotential G m X a) x := by
  unfold othersPotential
  refine (DifferentiableAt.fun_sum fun b hb => ?_).const_mul _
  have hb' : b ≠ a := by simpa using hb
  exact (DifferentiableAt.comp (g := invDist) (f := fun x => x - X b) x
    (differentiableAt_invDist (sub_ne_zero.mpr (hx b hb')))
    (differentiableAt_id.sub_const _)).const_mul _

theorem differentiableAt_othersScalarPotential (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S)
    (a : Fin N) {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) :
    DifferentiableAt ℝ (othersScalarPotential G m X V a) x := by
  unfold othersScalarPotential
  refine (DifferentiableAt.fun_sum fun b hb => ?_).const_mul _
  have hb' : b ≠ a := by simpa using hb
  exact ((DifferentiableAt.comp (g := invDist) (f := fun x => x - X b) x
    (differentiableAt_invDist (sub_ne_zero.mpr (hx b hb')))
    (differentiableAt_id.sub_const _)).const_mul _).mul_const _

theorem differentiableAt_kernelB_sub {x y : S} (h : x ≠ y) (u : S) (k : Fin 3) :
    DifferentiableAt ℝ (fun x => kernelB (x - y) u k) x := by
  have hι : DifferentiableAt ℝ (fun x => invDist (x - y)) x :=
    DifferentiableAt.comp (g := invDist) (f := fun x => x - y) x
      (differentiableAt_invDist (sub_ne_zero.mpr h)) (differentiableAt_id.sub_const _)
  unfold kernelB dot
  have hc : ∀ j, DifferentiableAt ℝ (fun x : S => (x - y) j) x := fun j => by fun_prop
  exact ((differentiableAt_const _).mul hι).add
    (((DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul (hc j)).mul
      (hc k)).mul (hι.pow 3))

theorem differentiableAt_othersVectorPotential (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S)
    (a : Fin N) {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) :
    DifferentiableAt ℝ (othersVectorPotential G m X V a) x := by
  refine differentiableAt_pi.mpr fun k => ?_
  unfold othersVectorPotential
  refine (DifferentiableAt.fun_sum fun b hb => ?_).const_mul _
  have hb' : b ≠ a := by simpa using hb
  exact (differentiableAt_kernelB_sub (hx b hb') (V b) k).const_mul _

theorem differentiableAt_testLagrangian {m c : ℝ} {Φ ψ : S → ℝ} {B : S → S} {x : S} (v : S)
    (hΦ : DifferentiableAt ℝ Φ x) (hψ : DifferentiableAt ℝ ψ x) (hB : DifferentiableAt ℝ B x) :
    DifferentiableAt ℝ (testLagrangian m c Φ ψ B) (x, v) := by
  have hΦ' : DifferentiableAt ℝ (fun z : S × S => Φ z.1) (x, v) :=
    DifferentiableAt.comp (g := Φ) (f := Prod.fst) (x, v) hΦ differentiableAt_fst
  have hψ' : DifferentiableAt ℝ (fun z : S × S => ψ z.1) (x, v) :=
    DifferentiableAt.comp (g := ψ) (f := Prod.fst) (x, v) hψ differentiableAt_fst
  have hB' : ∀ j, DifferentiableAt ℝ (fun z : S × S => B z.1 j) (x, v) := fun j =>
    DifferentiableAt.comp (g := fun y => B y j) (f := Prod.fst) (x, v)
      (differentiableAt_pi.mp hB j) differentiableAt_fst
  unfold testLagrangian
  fun_prop

/-- A square `(g − g(z₀))²` has the derivative `0` at `z₀`. -/
private theorem hasFDerivAt_sq_sub_self {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {g : Z → ℝ}
    {z₀ : Z} (hg : DifferentiableAt ℝ g z₀) :
    HasFDerivAt (fun z => (g z - g z₀) ^ 2) (0 : Z →L[ℝ] ℝ) z₀ := by
  have h := (hg.hasFDerivAt.sub_const (g z₀)).pow 2
  simpa using h

/-- **The term-by-term match of (106.17) (target (i)).** At a configuration where the body `a`
is apart from the others, the first derivatives of the Lagrangian of the system in the position
and the velocity of `a` are those of the test-body Lagrangian of `a` in the potentials `Φ`, `ψ`,
`B` of the other bodies. -/
theorem hasFDerivAt_eihLagrangian_update (G : ℝ) (m : Fin N → ℝ) (c s : ℝ) (X V : Fin N → S)
    (a : Fin N) (hX : ∀ b, b ≠ a → X a ≠ X b) :
    HasFDerivAt (fun z : S × S => eihLagrangian G m c s
        (Function.update X a z.1, Function.update V a z.2))
      (fderiv ℝ (testLagrangian (m a) c (othersPotential G m X a)
        (othersScalarPotential G m X V a) (othersVectorPotential G m X V a)) (X a, V a))
      (X a, V a) := by
  have hT := differentiableAt_testLagrangian (m := m a) (c := c) (V a)
    (differentiableAt_othersPotential G m X a hX)
    (differentiableAt_othersScalarPotential G m X V a hX)
    (differentiableAt_othersVectorPotential G m X V a hX)
  have hQ : HasFDerivAt (fun z : S × S => epsilon c * (G ^ 2 * m a ^ 2 / 2) *
      ∑ d ∈ ({a}ᶜ : Finset (Fin N)), m d * (invDist (X d - z.1) - invDist (X d - X a)) ^ 2)
      (0 : S × S →L[ℝ] ℝ) (X a, V a) := by
    have h : HasFDerivAt (fun z : S × S => epsilon c * (G ^ 2 * m a ^ 2 / 2) *
        ∑ d ∈ ({a}ᶜ : Finset (Fin N)), m d * (invDist (X d - z.1) - invDist (X d - X a)) ^ 2)
        ((epsilon c * (G ^ 2 * m a ^ 2 / 2)) • ∑ d ∈ ({a}ᶜ : Finset (Fin N)),
          m d • (0 : S × S →L[ℝ] ℝ)) (X a, V a) := by
      refine HasFDerivAt.const_mul (HasFDerivAt.fun_sum fun d hd => ?_) _
      have hd' : d ≠ a := by simpa using hd
      have hg : DifferentiableAt ℝ (fun z : S × S => invDist (X d - z.1)) (X a, V a) :=
        DifferentiableAt.comp (g := invDist) (f := fun z : S × S => X d - z.1) (X a, V a)
          (differentiableAt_invDist (sub_ne_zero.mpr (hX d hd').symm))
          ((differentiableAt_const _).sub differentiableAt_fst)
      exact (hasFDerivAt_sq_sub_self hg).const_mul (m d)
    simpa using h
  have hL : (fun z : S × S => eihLagrangian G m c s
      (Function.update X a z.1, Function.update V a z.2)) = fun z =>
        testLagrangian (m a) c (othersPotential G m X a) (othersScalarPotential G m X V a)
          (othersVectorPotential G m X V a) z -
        epsilon c * (G ^ 2 * m a ^ 2 / 2) *
          ∑ d ∈ ({a}ᶜ : Finset (Fin N)), m d * (invDist (X d - z.1) - invDist (X d - X a)) ^ 2 +
        eihRest G m c X V a := by
    funext z
    exact eihLagrangian_update G m c s X V a z.1 z.2
  rw [hL]
  simpa using (hT.hasFDerivAt.sub hQ).add_const (eihRest G m c X V a)

/-- Two Lagrangians with the same first derivative along a path near `t` have the same
Euler–Lagrange residual at `t`. -/
theorem eulerLagrange_congr_fderiv {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {L₁ L₂ : Mechanics.Lagrangian Q} {x : ℝ → Q} {t : ℝ}
    (h : ∀ᶠ s in 𝓝 t, fderiv ℝ (L₁ s) (x s, deriv x s) = fderiv ℝ (L₂ s) (x s, deriv x s)) :
    Mechanics.eulerLagrange L₁ x t = Mechanics.eulerLagrange L₂ x t := by
  have hm : Mechanics.momentum L₁ x =ᶠ[𝓝 t] Mechanics.momentum L₂ x := by
    filter_upwards [h] with s hs
    rw [Mechanics.momentum, Mechanics.momentum, hs]
  rw [Mechanics.eulerLagrange, Mechanics.eulerLagrange, hm.deriv_eq, Mechanics.force,
    Mechanics.force, h.self_of_nhds]

/-- Pairwise distinct positions stay pairwise distinct near `t` along a continuous path. -/
private theorem eventually_pairwise_ne {X : ℝ → Fin N → S} (hX : Continuous X) {t : ℝ}
    (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) :
    ∀ᶠ s in 𝓝 t, ∀ b d, b ≠ d → X s b ≠ X s d := by
  refine Filter.eventually_all.mpr fun b => Filter.eventually_all.mpr fun d => ?_
  by_cases hbd : b = d
  · exact Eventually.of_forall fun _ h => absurd hbd h
  · have hO : IsOpen {s | X s b ≠ X s d} :=
      isOpen_ne_fun ((continuous_apply b).comp hX) ((continuous_apply d).comp hX)
    filter_upwards [hO.mem_nhds (hsep b d hbd)] with s hs _
    exact hs

/-- **The Euler–Lagrange equations of (106.17) for one body are those of a test body
(target (i)).** Along a `C²` motion of the bodies, apart at the time `t`, the Euler–Lagrange
residual of the Lagrangian of the system in the direction of the body `a` is exactly the
residual of the time-dependent test-body Lagrangian of `a` in the potentials of the others along
their actual motion. -/
theorem eulerLagrange_eihLagrangian_eq_test (G : ℝ) (m : Fin N → ℝ) (c : ℝ)
    {X : ℝ → Fin N → S} (hX : ContDiff ℝ 2 X) {t : ℝ}
    (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N) (w : S) :
    Mechanics.eulerLagrange (eihLagrangian G m c) X t (Pi.single a w) =
      Mechanics.eulerLagrange (fun s => testLagrangian (m a) c (othersPotential G m (X s) a)
          (othersScalarPotential G m (X s) (deriv X s) a)
          (othersVectorPotential G m (X s) (deriv X s) a))
        (fun s => X s a) t w := by
  have hX1 : Differentiable ℝ X := hX.differentiable (by norm_num)
  have hdX : Differentiable ℝ (deriv X) := hX.differentiable_deriv_two
  have hsep' := eventually_pairwise_ne hX.continuous hsep
  have hL : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (eihLagrangian G m c s) (X s, deriv X s) := by
    filter_upwards [hsep'] with s hs
    exact (contDiffAt_eihLagrangian G m c s hs).differentiableAt (by simp)
  have hM : DifferentiableAt ℝ (Mechanics.momentum (eihLagrangian G m c) X) t := by
    have h0 := contDiffAt_eihLagrangian G m c t (z := (X t, deriv X t)) hsep
    have h1 : DifferentiableAt ℝ (fderiv ℝ (eihLagrangian G m c t)) (X t, deriv X t) :=
      (h0.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
    have h2 : DifferentiableAt ℝ (fun s => (X s, deriv X s)) t := (hX1 t).prodMk (hdX t)
    exact (h1.comp t h2).clm_comp (differentiableAt_const _)
  rw [Electrodynamics.eulerLagrange_update (eihLagrangian G m c) X a hL
    (Eventually.of_forall fun s => hX1 s) hM]
  refine congrArg (fun L : S →L[ℝ] ℝ => L w) (eulerLagrange_congr_fderiv (Q := S) ?_)
  filter_upwards [hsep'] with s hs
  have hda : deriv (fun r => X r a) s = deriv X s a :=
    (hasDerivAt_pi.mp (hX1 s).hasDerivAt a).deriv
  rw [hda]
  exact (hasFDerivAt_eihLagrangian_update G m c s (X s) (deriv X s) a
    fun b hb => hs a b (Ne.symm hb)).fderiv

/-! ### The Euler–Lagrange equations of a test body in given potentials -/

/-- The force `∂L/∂x · h` of the test-body Lagrangian per unit mass:
`−∂_hΦ + ε(−(3/2) v² ∂_hΦ − Φ ∂_hΦ − ∂_hψ + Σⱼ ∂_hBⱼ vⱼ)`. -/
def testForce (c : ℝ) (Φ ψ : S → ℝ) (B : S → S) (x v h : S) : ℝ :=
  -fderiv ℝ Φ x h + epsilon c * (-(3 / 2) * (∑ j, v j ^ 2) * fderiv ℝ Φ x h -
    Φ x * fderiv ℝ Φ x h - fderiv ℝ ψ x h + ∑ j, fderiv ℝ B x h j * v j)

/-- The momentum `∂L/∂v` of the test-body Lagrangian per unit mass,
`v + ε(v² v/2 − 3Φ v + B)` with the values `Φ₀ = Φ(x)`, `B₀ = B(x)`. -/
def testMomentum (c Φ₀ : ℝ) (B₀ v : S) (k : Fin 3) : ℝ :=
  v k + epsilon c * ((∑ j, v j ^ 2) * v k / 2 - 3 * Φ₀ * v k + B₀ k)

/-- The rate of the momentum per unit mass along a path with the velocity `v` and the acceleration
`a`, with the value `Φ₀` and the rates `Φ̇`, `Ḃ` of the potentials along the path. -/
def testMomentumRate (c Φ₀ Φd : ℝ) (Bd v a : S) (k : Fin 3) : ℝ :=
  a k + epsilon c * ((∑ j, v j * a j) * v k + (∑ j, v j ^ 2) * a k / 2 - 3 * Φd * v k -
    3 * Φ₀ * a k + Bd k)

theorem fderiv_testLagrangian {m c : ℝ} {Φ ψ : S → ℝ} {B : S → S} {x : S} (v : S)
    (hΦ : DifferentiableAt ℝ Φ x) (hψ : DifferentiableAt ℝ ψ x) (hB : DifferentiableAt ℝ B x)
    (w : S × S) :
    fderiv ℝ (testLagrangian m c Φ ψ B) (x, v) w =
      m * (testForce c Φ ψ B x v w.1 + ∑ k, testMomentum c (Φ x) (B x) v k * w.2 k) := by
  have hΦ' : HasFDerivAt (fun z : S × S => Φ z.1) ((fderiv ℝ Φ x).comp (fst ℝ S S)) (x, v) :=
    hΦ.hasFDerivAt.comp (x, v) hasFDerivAt_fst
  have hψ' : HasFDerivAt (fun z : S × S => ψ z.1) ((fderiv ℝ ψ x).comp (fst ℝ S S)) (x, v) :=
    hψ.hasFDerivAt.comp (x, v) hasFDerivAt_fst
  have hB' (j : Fin 3) : HasFDerivAt (fun z : S × S => B z.1 j)
      (((proj j : S →L[ℝ] ℝ).comp (fderiv ℝ B x)).comp (fst ℝ S S)) (x, v) :=
    HasFDerivAt.comp (g := fun y => B y j) (f := Prod.fst) (x, v)
      ((proj j : S →L[ℝ] ℝ).hasFDerivAt.comp x hB.hasFDerivAt) hasFDerivAt_fst
  have hdΦ := hΦ'.differentiableAt
  have hdψ := hψ'.differentiableAt
  have hdB (j : Fin 3) := (hB' j).differentiableAt
  have hBf (j : Fin 3) := (hB' j).fderiv
  have hs (j : Fin 3) : fderiv ℝ (fun y : S × S => y.2 j) (x, v) =
      (proj j : S →L[ℝ] ℝ).comp (snd ℝ S S) :=
    ((proj j : S →L[ℝ] ℝ).comp (snd ℝ S S)).fderiv
  unfold testLagrangian
  simp only [pow_two, div_eq_mul_inv]
  simp (disch := (intros; fun_prop)) only [fderiv_const_add, fderiv_const_mul, fderiv_fun_add,
    fderiv_fun_sub, fderiv_fun_mul, fderiv_fun_sum, fderiv_const_apply, hΦ'.fderiv, hψ'.fderiv,
    hBf, hs]
  simp only [add_apply, sub_apply, smul_apply, coe_comp, Function.comp_apply, FunLike.coe_sum,
    Finset.sum_apply, smul_eq_mul, proj_apply, coe_snd', coe_fst', zero_apply]
  simp only [testForce, testMomentum, Fin.sum_univ_three]
  ring

theorem momentum_testFamily {m c : ℝ} {Φ ψ : ℝ → S → ℝ} {B : ℝ → S → S} {x : ℝ → S} {s : ℝ}
    (hΦ : DifferentiableAt ℝ (Φ s) (x s)) (hψ : DifferentiableAt ℝ (ψ s) (x s))
    (hB : DifferentiableAt ℝ (B s) (x s)) :
    Mechanics.momentum (fun r => testLagrangian m c (Φ r) (ψ r) (B r)) x s =
      ∑ k, (m * testMomentum c (Φ s (x s)) (B s (x s)) (deriv x s) k) • (proj k : S →L[ℝ] ℝ) := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [Mechanics.momentum, comp_apply, inr_apply, fderiv_testLagrangian _ hΦ hψ hB]
  simp [testForce, Finset.mul_sum, mul_assoc]

/-- **The Euler–Lagrange residual of a test body in time-dependent potentials**, along a `C²`
path, is `m (F − ṗ)` with the force `testForce` and the rate `testMomentumRate`, given the rates
`Φ̇`, `Ḃ` of the potentials along the path. The potentials need to be differentiable only near
the path. -/
theorem eulerLagrange_testFamily {m c : ℝ} {Φ ψ : ℝ → S → ℝ} {B : ℝ → S → S} {x : ℝ → S}
    (hx : ContDiff ℝ 2 x) {t : ℝ}
    (hd : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (Φ s) (x s) ∧ DifferentiableAt ℝ (ψ s) (x s) ∧
      DifferentiableAt ℝ (B s) (x s))
    {Φd : ℝ} {Bd : S} (hΦd : HasDerivAt (fun s => Φ s (x s)) Φd t)
    (hBd : ∀ k, HasDerivAt (fun s => B s (x s) k) (Bd k) t) (k : Fin 3) :
    Mechanics.eulerLagrange (fun s => testLagrangian m c (Φ s) (ψ s) (B s)) x t (Pi.single k 1) =
      m * (testForce c (Φ t) (ψ t) (B t) (x t) (deriv x t) (Pi.single k 1) -
        testMomentumRate c (Φ t (x t)) Φd Bd (deriv x t) (deriv (deriv x) t) k) := by
  obtain ⟨hΦt, hψt, hBt⟩ := hd.self_of_nhds
  have hmom : Mechanics.momentum (fun r => testLagrangian m c (Φ r) (ψ r) (B r)) x =ᶠ[𝓝 t]
      fun s => ∑ k, (m * testMomentum c (Φ s (x s)) (B s (x s)) (deriv x s) k) •
        (proj k : S →L[ℝ] ℝ) := by
    filter_upwards [hd] with s hs
    exact momentum_testFamily hs.1 hs.2.1 hs.2.2
  have hv (j : Fin 3) : HasDerivAt (fun s => deriv x s j) (deriv (deriv x) t j) t :=
    hasDerivAt_pi.mp (hx.differentiable_deriv_two t).hasDerivAt j
  have hP (k : Fin 3) : HasDerivAt (fun s => testMomentum c (Φ s (x s)) (B s (x s)) (deriv x s) k)
      (testMomentumRate c (Φ t (x t)) Φd Bd (deriv x t) (deriv (deriv x) t) k) t := by
    have hsq : HasDerivAt (fun s => ∑ j, deriv x s j ^ 2)
        (∑ j, 2 * deriv x t j * deriv (deriv x) t j) t :=
      HasDerivAt.fun_sum fun j _ => ((hv j).pow 2).congr_deriv (by norm_num)
    have h : HasDerivAt (fun s => testMomentum c (Φ s (x s)) (B s (x s)) (deriv x s) k) _ t :=
      (hv k).add ((((hsq.mul (hv k)).div_const 2).sub ((hΦd.const_mul 3).mul (hv k))).add
        (hBd k) |>.const_mul (epsilon c))
    refine h.congr_deriv ?_
    have e : ∑ j, 2 * deriv x t j * deriv (deriv x) t j =
        2 * ∑ j, deriv x t j * deriv (deriv x) t j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, testMomentumRate]
    ring
  have hD : HasDerivAt (fun s => ∑ k, (m * testMomentum c (Φ s (x s)) (B s (x s))
      (deriv x s) k) • (proj k : S →L[ℝ] ℝ))
      (∑ k, (m * testMomentumRate c (Φ t (x t)) Φd Bd (deriv x t) (deriv (deriv x) t) k) •
        (proj k : S →L[ℝ] ℝ)) t :=
    HasDerivAt.fun_sum fun k _ => ((hP k).const_mul m).smul_const (proj k : S →L[ℝ] ℝ)
  rw [Mechanics.eulerLagrange, sub_apply, Mechanics.force, comp_apply, inl_apply,
    fderiv_testLagrangian _ hΦt hψt hBt, hmom.deriv_eq, hD.deriv]
  simp [Pi.single_apply]
  ring

/-! ### The derivatives of the potentials of point masses -/

/-- A directional derivative read off a line. -/
theorem fderiv_apply_of_hasDerivAt_line {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : S → F} {x h : S} {D : F} (hf : DifferentiableAt ℝ f x)
    (hD : HasDerivAt (fun r : ℝ => f (x + r • h)) D 0) : fderiv ℝ f x h = D := by
  have hl : HasDerivAt (fun r : ℝ => x + r • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
  exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)).unique hD

theorem hasDerivAt_line_sub (x h y : S) :
    HasDerivAt (fun r : ℝ => x + r • h - y) h 0 := by
  simpa using (((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x).sub_const y

theorem fderiv_othersPotential_apply (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N)
    {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) (h : S) :
    fderiv ℝ (othersPotential G m X a) x h =
      G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * invDist (x - X b) ^ 3 * dot (x - X b) h := by
  refine fderiv_apply_of_hasDerivAt_line (differentiableAt_othersPotential G m X a hx) ?_
  have hD : HasDerivAt (fun r : ℝ => othersPotential G m X a (x + r • h))
      (-G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * (-(invDist (x + (0 : ℝ) • h - X b) ^ 3) *
        dot (x + (0 : ℝ) • h - X b) h)) 0 := by
    refine (HasDerivAt.fun_sum fun b hb => ?_).const_mul (-G)
    have hb' : b ≠ a := by simpa using hb
    exact (hasDerivAt_invDist_comp (hasDerivAt_line_sub x h (X b))
      (by simpa using sub_ne_zero.mpr (hx b hb'))).const_mul (m b)
  refine hD.congr_deriv ?_
  simp only [zero_smul, add_zero, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem fderiv_othersScalarPotential_apply (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N)
    {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) (h : S) :
    fderiv ℝ (othersScalarPotential G m X V a) x h =
      G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * (3 / 2 * ∑ j, V b j ^ 2 - potentialAt G m X b) *
        invDist (x - X b) ^ 3 * dot (x - X b) h := by
  refine fderiv_apply_of_hasDerivAt_line (differentiableAt_othersScalarPotential G m X V a hx) ?_
  have hD : HasDerivAt (fun r : ℝ => othersScalarPotential G m X V a (x + r • h))
      (-G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * (-(invDist (x + (0 : ℝ) • h - X b) ^ 3) *
        dot (x + (0 : ℝ) • h - X b) h) * (3 / 2 * ∑ j, V b j ^ 2 - potentialAt G m X b)) 0 := by
    refine (HasDerivAt.fun_sum fun b hb => ?_).const_mul (-G)
    have hb' : b ≠ a := by simpa using hb
    exact ((hasDerivAt_invDist_comp (hasDerivAt_line_sub x h (X b))
      (by simpa using sub_ne_zero.mpr (hx b hb'))).const_mul (m b)).mul_const _
  refine hD.congr_deriv ?_
  simp only [zero_smul, add_zero, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem fderiv_othersVectorPotential_apply (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S)
    (a : Fin N) {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) (h : S) (k : Fin 3) :
    fderiv ℝ (othersVectorPotential G m X V a) x h k =
      -(G / 2) * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * dKernelB (x - X b) (V b) h k := by
  have hD : HasDerivAt (fun r : ℝ => othersVectorPotential G m X V a (x + r • h))
      (fun k => -(G / 2) * ∑ b ∈ ({a}ᶜ : Finset (Fin N)),
        m b * dKernelB (x - X b) (V b) h k) 0 := by
    refine hasDerivAt_pi.mpr fun k => ?_
    have h1 : HasDerivAt (fun r : ℝ => othersVectorPotential G m X V a (x + r • h) k)
        (-(G / 2) * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b *
          (dKernelB (x + (0 : ℝ) • h - X b) (V b) h k + kernelB (x + (0 : ℝ) • h - X b) 0 k))
        0 := by
      refine (HasDerivAt.fun_sum fun b hb => ?_).const_mul (-(G / 2))
      have hb' : b ≠ a := by simpa using hb
      exact (hasDerivAt_kernelB_comp (hasDerivAt_line_sub x h (X b)) (hasDerivAt_const _ (V b))
        (by simpa using sub_ne_zero.mpr (hx b hb')) k).const_mul (m b)
    refine h1.congr_deriv ?_
    simp [kernelB_zero_right]
  rw [fderiv_apply_of_hasDerivAt_line (differentiableAt_othersVectorPotential G m X V a hx) hD]

/-- The rate of the potential of the others at the body `a` along the motion. -/
theorem hasDerivAt_othersPotential_path (G : ℝ) (m : Fin N → ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (a : Fin N) (hsep : ∀ b, b ≠ a → X t a ≠ X t b) :
    HasDerivAt (fun s => othersPotential G m (X s) a (X s a))
      (G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * invDist (X t a - X t b) ^ 3 *
        dot (X t a - X t b) (deriv X t a - deriv X t b)) t := by
  have hX1 := (hX.differentiable (by norm_num) t).hasDerivAt
  have hd (b : Fin N) : HasDerivAt (fun s => X s a - X s b) (deriv X t a - deriv X t b) t :=
    (hasDerivAt_pi.mp hX1 a).sub (hasDerivAt_pi.mp hX1 b)
  have h : HasDerivAt (fun s => othersPotential G m (X s) a (X s a))
      (-G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * (-(invDist (X t a - X t b) ^ 3) *
        dot (X t a - X t b) (deriv X t a - deriv X t b))) t := by
    refine (HasDerivAt.fun_sum fun b hb => ?_).const_mul (-G)
    have hb' : b ≠ a := by simpa using hb
    exact (hasDerivAt_invDist_comp (hd b) (sub_ne_zero.mpr (hsep b hb'))).const_mul (m b)
  refine h.congr_deriv ?_
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The rate of the vector potential of the others at the body `a` along the motion; it contains
the accelerations of the other bodies. -/
theorem hasDerivAt_othersVectorPotential_path (G : ℝ) (m : Fin N → ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (a : Fin N) (hsep : ∀ b, b ≠ a → X t a ≠ X t b) (k : Fin 3) :
    HasDerivAt (fun s => othersVectorPotential G m (X s) (deriv X s) a (X s a) k)
      (-(G / 2) * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b *
        (dKernelB (X t a - X t b) (deriv X t b) (deriv X t a - deriv X t b) k +
          kernelB (X t a - X t b) (deriv (deriv X) t b) k)) t := by
  have hX1 := (hX.differentiable (by norm_num) t).hasDerivAt
  have hX2 := (hX.differentiable_deriv_two t).hasDerivAt
  have hd (b : Fin N) : HasDerivAt (fun s => X s a - X s b) (deriv X t a - deriv X t b) t :=
    (hasDerivAt_pi.mp hX1 a).sub (hasDerivAt_pi.mp hX1 b)
  refine (HasDerivAt.fun_sum fun b hb => ?_).const_mul (-(G / 2))
  have hb' : b ≠ a := by simpa using hb
  exact (hasDerivAt_kernelB_comp (hd b) (hasDerivAt_pi.mp hX2 b)
    (sub_ne_zero.mpr (hsep b hb')) k).const_mul (m b)

/-! ### The explicit Euler–Lagrange equations of (106.17) -/

/-- The Newtonian acceleration `a_N = −G Σ_b m_b (x_a − x_b)/r_ab³` of the body `a`, `−∇Φ` at the
body. -/
def newtonAcceleration (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N) : S := fun k =>
  -G * ∑ b, m b * invDist (X a - X b) ^ 3 * (X a - X b) k

/-- The gradient `∇ψ` at the body `a`. -/
def scalarGradient (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) : S := fun k =>
  G * ∑ b, m b * (3 / 2 * ∑ j, V b j ^ 2 - potentialAt G m X b) * invDist (X a - X b) ^ 3 *
    (X a - X b) k

/-- The gradient `∇(B · v_a)` at the body `a` with its velocity `v_a` held fixed. -/
def vectorGradient (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) : S := fun k =>
  -(G / 2) * ∑ b, m b * ∑ j, dKernelB (X a - X b) (V b) (Pi.single k 1) j * V a j

/-- The rate `dΦ/dt` of the potential at the body `a` along the motion. -/
def potentialRate (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) : ℝ :=
  G * ∑ b, m b * invDist (X a - X b) ^ 3 * dot (X a - X b) (V a - V b)

/-- The vector potential `B` at the body `a`. -/
def vectorPotentialAt (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) : S := fun k =>
  -(G / 2) * ∑ b, m b * kernelB (X a - X b) (V b) k

/-- The rate `dB/dt` of the vector potential at the body `a` along the motion, with the
accelerations `A` of the bodies. -/
def vectorPotentialRate (G : ℝ) (m : Fin N → ℝ) (X V A : Fin N → S) (a : Fin N) : S := fun k =>
  -(G / 2) * ∑ b, m b * (dKernelB (X a - X b) (V b) (V a - V b) k + kernelB (X a - X b) (A b) k)

/-- **The force `∂L/∂x_a` of (106.17) per unit mass**:
`a_N + ε((3/2) v_a² a_N − U_a a_N − ∇ψ + ∇(B · v_a))`. -/
def eihForce (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V : Fin N → S) (a : Fin N) : S := fun k =>
  newtonAcceleration G m X a k + epsilon c * (3 / 2 * (∑ j, V a j ^ 2) *
    newtonAcceleration G m X a k - potentialAt G m X a * newtonAcceleration G m X a k -
    scalarGradient G m X V a k + vectorGradient G m X V a k)

/-- **The rate of the momentum `∂L/∂v_a` of (106.17) per unit mass**, with the accelerations `A`:
`a_a + ε((v_a · a_a) v_a + v_a² a_a/2 − 3 Φ̇ v_a + 3 U_a a_a + Ḃ)`. -/
def eihMomentumRate (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V A : Fin N → S) (a : Fin N) : S :=
  fun k => A a k + epsilon c * ((∑ j, V a j * A a j) * V a k + (∑ j, V a j ^ 2) * A a k / 2 -
    3 * potentialRate G m X V a * V a k + 3 * potentialAt G m X a * A a k +
    vectorPotentialRate G m X V A a k)

private theorem sum_compl_eq_sum {f : Fin N → ℝ} (a : Fin N) (h : f a = 0) :
    ∑ b ∈ ({a}ᶜ : Finset (Fin N)), f b = ∑ b, f b := by
  rw [Fintype.sum_eq_add_sum_compl a f, h, zero_add]

theorem othersPotential_self (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N) :
    othersPotential G m X a (X a) = -potentialAt G m X a := by
  rw [othersPotential, potentialAt, sum_compl_eq_sum a (by simp)]
  ring

theorem dot_single (z : S) (k : Fin 3) : dot z (Pi.single k 1) = z k := by
  simp [dot, Pi.single_apply]

/-- **A test body of the mass `μ` in the potentials of the bodies `b ≠ a`** along their motion,
at the position of the body `a`: its Euler–Lagrange residual is `μ (F_k − ṗ_k)` with the force
`eihForce` and the rate `eihMomentumRate` per unit mass. -/
theorem eulerLagrange_testFamily_others (μ G : ℝ) (m : Fin N → ℝ) (c : ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N)
    (k : Fin 3) :
    Mechanics.eulerLagrange (fun s => testLagrangian μ c (othersPotential G m (X s) a)
          (othersScalarPotential G m (X s) (deriv X s) a)
          (othersVectorPotential G m (X s) (deriv X s) a))
        (fun s => X s a) t (Pi.single k 1) =
      μ * (eihForce G m c (X t) (deriv X t) a k -
        eihMomentumRate G m c (X t) (deriv X t) (deriv (deriv X) t) a k) := by
  have hX1 : Differentiable ℝ X := hX.differentiable (by norm_num)
  have hXa : ContDiff ℝ 2 (fun s => X s a) := contDiff_pi.mp hX a
  have hsepa : ∀ b, b ≠ a → X t a ≠ X t b := fun b hb => hsep a b (Ne.symm hb)
  have hsep' := eventually_pairwise_ne hX.continuous hsep
  have hda : deriv (fun s => X s a) = fun s => deriv X s a :=
    funext fun s => (hasDerivAt_pi.mp (hX1 s).hasDerivAt a).deriv
  have hdda : deriv (fun s => deriv X s a) t = deriv (deriv X) t a :=
    (hasDerivAt_pi.mp (hX.differentiable_deriv_two t).hasDerivAt a).deriv
  have hd : ∀ᶠ s in 𝓝 t,
      DifferentiableAt ℝ (othersPotential G m (X s) a) (X s a) ∧
      DifferentiableAt ℝ (othersScalarPotential G m (X s) (deriv X s) a) (X s a) ∧
      DifferentiableAt ℝ (othersVectorPotential G m (X s) (deriv X s) a) (X s a) := by
    filter_upwards [hsep'] with s hs
    have h' : ∀ b, b ≠ a → X s a ≠ X s b := fun b hb => hs a b (Ne.symm hb)
    exact ⟨differentiableAt_othersPotential G m (X s) a h',
      differentiableAt_othersScalarPotential G m (X s) (deriv X s) a h',
      differentiableAt_othersVectorPotential G m (X s) (deriv X s) a h'⟩
  rw [eulerLagrange_testFamily hXa hd (hasDerivAt_othersPotential_path G m hX a hsepa)
      (hasDerivAt_othersVectorPotential_path G m hX a hsepa) k, hda, hdda]
  beta_reduce
  congr 1
  have hF : testForce c (othersPotential G m (X t) a) (othersScalarPotential G m (X t)
      (deriv X t) a) (othersVectorPotential G m (X t) (deriv X t) a) (X t a) (deriv X t a)
      (Pi.single k 1) = eihForce G m c (X t) (deriv X t) a k := by
    have h1 := fderiv_othersPotential_apply G m (X t) a hsepa (Pi.single k 1)
    have h2 := fderiv_othersScalarPotential_apply G m (X t) (deriv X t) a hsepa (Pi.single k 1)
    have h3 : ∑ j, fderiv ℝ (othersVectorPotential G m (X t) (deriv X t) a) (X t a)
        (Pi.single k 1) j * deriv X t a j = vectorGradient G m (X t) (deriv X t) a k := by
      simp only [fderiv_othersVectorPotential_apply G m (X t) (deriv X t) a hsepa,
        vectorGradient]
      rw [← sum_compl_eq_sum a (by simp [dKernelB_zero_left])]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => by ring
    have hN : fderiv ℝ (othersPotential G m (X t) a) (X t a) (Pi.single k 1) =
        -newtonAcceleration G m (X t) a k := by
      rw [h1, newtonAcceleration, ← sum_compl_eq_sum a (by simp)]
      simp only [dot_single]
      ring
    have hS : fderiv ℝ (othersScalarPotential G m (X t) (deriv X t) a) (X t a) (Pi.single k 1) =
        scalarGradient G m (X t) (deriv X t) a k := by
      rw [h2, scalarGradient, ← sum_compl_eq_sum a (by simp)]
      simp only [dot_single]
    rw [testForce, hN, hS, h3, othersPotential_self, eihForce]
    ring
  have hR : testMomentumRate c (othersPotential G m (X t) a (X t a))
      (G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * invDist (X t a - X t b) ^ 3 *
        dot (X t a - X t b) (deriv X t a - deriv X t b))
      (fun k => -(G / 2) * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b *
        (dKernelB (X t a - X t b) (deriv X t b) (deriv X t a - deriv X t b) k +
          kernelB (X t a - X t b) (deriv (deriv X) t b) k))
      (deriv X t a) (deriv (deriv X) t a) k =
      eihMomentumRate G m c (X t) (deriv X t) (deriv (deriv X) t) a k := by
    simp only [testMomentumRate]
    rw [sum_compl_eq_sum a (by simp), sum_compl_eq_sum a (by simp [dKernelB_zero_left,
      kernelB_zero_left]), othersPotential_self, eihMomentumRate, potentialRate,
      vectorPotentialRate]
    ring
  rw [hF, hR]

/-- **The Euler–Lagrange equations of (106.17), explicitly (target (v)).** Along a `C²` motion,
with the bodies apart at the time `t`, the residual for the body `a` in the direction `e_k` is
`m_a (F_k − ṗ_k)` with the force `eihForce` and the rate `eihMomentumRate` of the momentum per
unit mass at the positions, velocities and accelerations at `t`. -/
theorem eulerLagrange_eihLagrangian (G : ℝ) (m : Fin N → ℝ) (c : ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N)
    (k : Fin 3) :
    Mechanics.eulerLagrange (eihLagrangian G m c) X t (Pi.single a (Pi.single k 1)) =
      m a * (eihForce G m c (X t) (deriv X t) a k -
        eihMomentumRate G m c (X t) (deriv X t) (deriv (deriv X) t) a k) := by
  rw [eulerLagrange_eihLagrangian_eq_test G m c hX hsep a,
    eulerLagrange_testFamily_others (m a) G m c hX hsep a k]

/-! ### The acceleration in the second approximation -/

/-- The correction `(3/2) v_a² a_N − U_a a_N − ∇ψ + ∇(B · v_a)` of the force per unit mass. -/
def forceCorrection (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) : S := fun k =>
  3 / 2 * (∑ j, V a j ^ 2) * newtonAcceleration G m X a k -
    potentialAt G m X a * newtonAcceleration G m X a k - scalarGradient G m X V a k +
    vectorGradient G m X V a k

/-- The part `−3 Φ̇ v_a + Ḃ|_{a = 0}` of the correction of the rate of the momentum that does not
contain the accelerations. -/
def rateZero (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) : S := fun k =>
  -3 * potentialRate G m X V a * V a k -
    (G / 2) * ∑ b, m b * dKernelB (X a - X b) (V b) (V a - V b) k

/-- The part of the correction of the rate of the momentum that is linear in the accelerations
`D`: `(v_a · D_a) v_a + v_a² D_a/2 + 3 U_a D_a − (G/2) Σ_b m_b K(x_a − x_b, D_b)`. -/
def rateLinear (G : ℝ) (m : Fin N → ℝ) (X V D : Fin N → S) (a : Fin N) : S := fun k =>
  (∑ j, V a j * D a j) * V a k + (∑ j, V a j ^ 2) * D a k / 2 +
    3 * potentialAt G m X a * D a k - (G / 2) * ∑ b, m b * kernelB (X a - X b) (D b) k

/-- **The acceleration of the body `a` in the second approximation**: the solution of the
Euler–Lagrange equations `F = ṗ(A)` of (106.17) in which the accelerations in the terms of order
`c⁻²` are the Newtonian ones, `a_N + F − ṗ(a_N)`. Explicitly
`a_N + c⁻²[(3/2) v_a² a_N − U_a a_N − ∇ψ + ∇(B · v_a) − (v_a · a_N) v_a − v_a² a_N/2 + 3 Φ̇ v_a`
`− 3 U_a a_N − Ḃ(a_N)]` with `Φ = −U_a`, `a_N = −∇Φ` and the rates `Φ̇`, `Ḃ` along the motion,
`Ḃ` with the Newtonian accelerations of the other bodies: the combination of the test-body
acceleration `postNewtonianCorrection` (with total rates in place of `∂_t`). -/
def eihAcceleration (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V : Fin N → S) : Fin N → S :=
  fun a k => newtonAcceleration G m X a k + (eihForce G m c X V a k -
    eihMomentumRate G m c X V (fun b => newtonAcceleration G m X b) a k)

theorem eihForce_eq (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V : Fin N → S) (a : Fin N) (k : Fin 3) :
    eihForce G m c X V a k =
      newtonAcceleration G m X a k + epsilon c * forceCorrection G m X V a k := rfl

theorem kernelB_add_right (z u w : S) (k : Fin 3) :
    kernelB z (u + w) k = kernelB z u k + kernelB z w k := by
  simp only [kernelB, dot_add_left, Pi.add_apply]
  ring

theorem eihMomentumRate_eq (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V A : Fin N → S) (a : Fin N)
    (k : Fin 3) :
    eihMomentumRate G m c X V A a k =
      A a k + epsilon c * (rateZero G m X V a k + rateLinear G m X V A a k) := by
  simp only [eihMomentumRate, rateZero, rateLinear, vectorPotentialRate, mul_add,
    Finset.sum_add_distrib]
  ring

theorem kernelB_sub_right (z u w : S) (k : Fin 3) :
    kernelB z (u - w) k = kernelB z u k - kernelB z w k := by
  simp only [kernelB, dot, Pi.sub_apply, Fin.sum_univ_three]
  ring

theorem rateLinear_sub (G : ℝ) (m : Fin N → ℝ) (X V D D' : Fin N → S) (a : Fin N) (k : Fin 3) :
    rateLinear G m X V D a k - rateLinear G m X V D' a k = rateLinear G m X V (D - D') a k := by
  simp only [rateLinear, Pi.sub_apply, kernelB_sub_right, mul_sub, Finset.sum_sub_distrib]
  ring

/-! ### Bounds -/

/-- A real function bounded on a set. -/
private def BoundedOn {α : Type} (T : Set α) (F : α → ℝ) : Prop :=
  ∃ C, 0 ≤ C ∧ ∀ x ∈ T, |F x| ≤ C

section BoundedOn

variable {α : Type} {T : Set α} {F H : α → ℝ}

private theorem BoundedOn.const (a : ℝ) : BoundedOn T (fun _ => a) :=
  ⟨|a|, abs_nonneg a, fun _ _ => le_rfl⟩

private theorem BoundedOn.add (hF : BoundedOn T F) (hH : BoundedOn T H) :
    BoundedOn T (fun x => F x + H x) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hH⟩ := hH
  exact ⟨C + D, by positivity, fun x hx => (abs_add_le _ _).trans (add_le_add (hF x hx) (hH x hx))⟩

private theorem BoundedOn.sub (hF : BoundedOn T F) (hH : BoundedOn T H) :
    BoundedOn T (fun x => F x - H x) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hH⟩ := hH
  exact ⟨C + D, by positivity, fun x hx => (abs_sub _ _).trans (add_le_add (hF x hx) (hH x hx))⟩

private theorem BoundedOn.mul (hF : BoundedOn T F) (hH : BoundedOn T H) :
    BoundedOn T (fun x => F x * H x) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hH⟩ := hH
  refine ⟨C * D, by positivity, fun x hx => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hF x hx) (hH x hx) (abs_nonneg _) hC

private theorem BoundedOn.neg (hF : BoundedOn T F) : BoundedOn T (fun x => -F x) := by
  obtain ⟨C, hC, hF⟩ := hF
  exact ⟨C, hC, fun x hx => by rw [abs_neg]; exact hF x hx⟩

private theorem BoundedOn.div_const (hF : BoundedOn T F) (a : ℝ) :
    BoundedOn T (fun x => F x / a) := by
  simpa only [div_eq_mul_inv] using hF.mul (BoundedOn.const a⁻¹)

private theorem BoundedOn.pow (hF : BoundedOn T F) (n : ℕ) : BoundedOn T (fun x => F x ^ n) := by
  induction n with
  | zero => simpa using BoundedOn.const (T := T) 1
  | succ n ih => simpa only [pow_succ] using ih.mul hF

private theorem BoundedOn.sum {ι : Type} [Fintype ι] {K : ι → α → ℝ}
    (hK : ∀ i, BoundedOn T (K i)) : BoundedOn T (fun x => ∑ i, K i x) := by
  choose C hC hb using hK
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC i, fun x hx => ?_⟩
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hb i x hx)

private theorem BoundedOn.of_le {C : ℝ} (h : ∀ x ∈ T, |F x| ≤ C) : BoundedOn T F :=
  ⟨max C 0, le_max_right _ _, fun x hx => (h x hx).trans (le_max_left _ _)⟩

private theorem BoundedOn.congr (hF : BoundedOn T F) (h : ∀ x, F x = H x) : BoundedOn T H := by
  obtain ⟨C, hC, hF⟩ := hF
  exact ⟨C, hC, fun x hx => by rw [← h x]; exact hF x hx⟩

end BoundedOn

/-- Decompose a bound on a polynomial expression into bounds on its atoms. -/
local macro "bounded_on" : tactic => `(tactic| repeat' first
  | intro _
  | with_reducible apply BoundedOn.const
  | with_reducible apply_assumption
  | with_reducible apply BoundedOn.add
  | with_reducible apply BoundedOn.sub
  | with_reducible apply BoundedOn.mul
  | with_reducible apply BoundedOn.neg
  | with_reducible apply BoundedOn.div_const
  | with_reducible apply BoundedOn.pow
  | with_reducible apply BoundedOn.sum)

/-- The derivative of the kernel in the unit vector `ν = z/‖z‖₂`. -/
theorem dKernelB_eq (z u h : S) (k : Fin 3) :
    dKernelB z u h k = invDist z ^ 2 * (-7 * u k * ∑ j, invDist z * z j * h j +
      (∑ j, u j * h j) * (invDist z * z k) + (∑ j, u j * (invDist z * z j)) * h k -
      3 * (∑ j, u j * (invDist z * z j)) * (invDist z * z k) *
        ∑ j, invDist z * z j * h j) := by
  simp only [dKernelB, dot, Fin.sum_univ_three]
  ring

theorem kernelB_eq (z u : S) (k : Fin 3) :
    kernelB z u k = invDist z * (7 * u k + (∑ j, u j * (invDist z * z j)) * (invDist z * z k)) := by
  simp only [kernelB, dot, Fin.sum_univ_three]
  ring

private theorem BoundedOn.dKernelB {α : Type} {T : Set α} {z u h : α → S}
    (hι : BoundedOn T (fun p => invDist (z p)))
    (hν : ∀ j, BoundedOn T (fun p => invDist (z p) * z p j))
    (hu : ∀ j, BoundedOn T (fun p => u p j)) (hh : ∀ j, BoundedOn T (fun p => h p j))
    (k : Fin 3) : BoundedOn T (fun p => EinsteinInfeldHoffmann.dKernelB (z p) (u p) (h p) k) := by
  refine BoundedOn.congr ?_ fun p => (dKernelB_eq (z p) (u p) (h p) k).symm
  bounded_on

private theorem BoundedOn.kernelB {α : Type} {T : Set α} {z u : α → S}
    (hι : BoundedOn T (fun p => invDist (z p)))
    (hν : ∀ j, BoundedOn T (fun p => invDist (z p) * z p j))
    (hu : ∀ j, BoundedOn T (fun p => u p j)) (k : Fin 3) :
    BoundedOn T (fun p => EinsteinInfeldHoffmann.kernelB (z p) (u p) k) := by
  refine BoundedOn.congr ?_ fun p => (kernelB_eq (z p) (u p) k).symm
  bounded_on

/-- `|K(z, w)_k| ≤ 10 ‖w‖/‖z‖₂` in the sup norm. -/
theorem abs_kernelB_le (z w : S) (k : Fin 3) : |kernelB z w k| ≤ 10 * invDist z * ‖w‖ := by
  rw [kernelB_eq]
  have hι := invDist_nonneg z
  have hw := norm_nonneg w
  have hwj (j : Fin 3) : |w j| ≤ ‖w‖ := spaceComponent_abs_le le_rfl j
  have hs : |∑ j, w j * (invDist z * z j)| ≤ 3 * ‖w‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |w j * (invDist z * z j)| ≤ ∑ _j : Fin 3, ‖w‖ :=
          Finset.sum_le_sum fun j _ => by
            rw [abs_mul]
            exact (mul_le_of_le_one_right (abs_nonneg _) (abs_invDist_mul_le z j)).trans (hwj j)
      _ = 3 * ‖w‖ := by simp
  have hin : |7 * w k + (∑ j, w j * (invDist z * z j)) * (invDist z * z k)| ≤ 10 * ‖w‖ :=
    calc |7 * w k + (∑ j, w j * (invDist z * z j)) * (invDist z * z k)| ≤
          |7 * w k| + |(∑ j, w j * (invDist z * z j)) * (invDist z * z k)| := abs_add_le _ _
      _ ≤ 7 * ‖w‖ + 3 * ‖w‖ := by
          refine add_le_add ?_ ?_
          · rw [abs_mul]
            norm_num
            exact hwj k
          · rw [abs_mul]
            exact (mul_le_of_le_one_right (abs_nonneg _) (abs_invDist_mul_le z k)).trans hs
      _ = 10 * ‖w‖ := by ring
  rw [abs_mul, abs_of_nonneg hι]
  calc invDist z * |7 * w k + (∑ j, w j * (invDist z * z j)) * (invDist z * z k)| ≤
        invDist z * (10 * ‖w‖) := mul_le_mul_of_nonneg_left hin hι
    _ = 10 * invDist z * ‖w‖ := by ring

/-! ### The uniform estimate -/

/-- The configurations with the bodies at mutual distances at least `δ` and speeds at most `V₀`
(the sup norm of `NewtonianSpace`). -/
def separatedSet (N : ℕ) (δ V₀ : ℝ) : Set ((Fin N → S) × (Fin N → S)) :=
  {p | (∀ a b, a ≠ b → δ ≤ euclidNorm (p.1 a - p.1 b)) ∧ ∀ a, ‖p.2 a‖ ≤ V₀}

theorem invDist_le_of_mem {δ V₀ : ℝ} (hδ : 0 < δ) {p : (Fin N → S) × (Fin N → S)}
    (hp : p ∈ separatedSet N δ V₀) (a b : Fin N) : invDist (p.1 a - p.1 b) ≤ δ⁻¹ := by
  rcases eq_or_ne a b with rfl | h
  · simp [hδ.le]
  · exact invDist_le hδ (hp.1 a b h)

theorem abs_potentialAt_le (G : ℝ) (m : Fin N → ℝ) {δ V₀ : ℝ} (hδ : 0 < δ)
    {p : (Fin N → S) × (Fin N → S)} (hp : p ∈ separatedSet N δ V₀) (a : Fin N) :
    |potentialAt G m p.1 a| ≤ |G| * δ⁻¹ * ∑ b, |m b| := by
  rw [potentialAt, abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) (abs_nonneg G)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [abs_mul, abs_of_nonneg (invDist_nonneg _), mul_comm]
  exact mul_le_mul_of_nonneg_right (invDist_le_of_mem hδ hp a b) (abs_nonneg _)

/-- **The linear part of the rate of the momentum is bounded uniformly** on the separated
configurations: `|rateLinear D| ≤ ((9/2)V₀² + 8|G| Σ|m|/δ) ‖D‖`. -/
theorem abs_rateLinear_le (G : ℝ) (m : Fin N → ℝ) {δ V₀ : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V₀)
    {p : (Fin N → S) × (Fin N → S)} (hp : p ∈ separatedSet N δ V₀) (D : Fin N → S) (a : Fin N)
    (k : Fin 3) :
    |rateLinear G m p.1 p.2 D a k| ≤ (9 / 2 * V₀ ^ 2 + 8 * |G| * δ⁻¹ * ∑ b, |m b|) * ‖D‖ := by
  have hD := norm_nonneg D
  have hDa : ‖D a‖ ≤ ‖D‖ := norm_le_pi_norm D a
  have hDb (b : Fin N) (j : Fin 3) : |D b j| ≤ ‖D‖ :=
    (spaceComponent_abs_le le_rfl j).trans (norm_le_pi_norm D b)
  have hVa := hp.2 a
  have hM : 0 ≤ ∑ b, |m b| := Finset.sum_nonneg fun b _ => abs_nonneg _
  have hδ' : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  have e1 : |(∑ j, p.2 a j * D a j) * p.2 a k| ≤ 3 * V₀ ^ 2 * ‖D‖ := by
    rw [abs_mul]
    calc |∑ j, p.2 a j * D a j| * |p.2 a k| ≤ (3 * V₀ * ‖D‖) * V₀ :=
          mul_le_mul ((mixedPairing_abs_le hVa hDa hV)) (spaceComponent_abs_le hVa k)
            (abs_nonneg _) (by positivity)
      _ = 3 * V₀ ^ 2 * ‖D‖ := by ring
  have e2 : |(∑ j, p.2 a j ^ 2) * D a k / 2| ≤ 3 / 2 * V₀ ^ 2 * ‖D‖ := by
    have h0 : 0 ≤ ∑ j, p.2 a j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    rw [abs_div, abs_mul, abs_of_nonneg h0, abs_two]
    calc (∑ j, p.2 a j ^ 2) * |D a k| / 2 ≤ (3 * V₀ ^ 2) * ‖D‖ / 2 :=
          div_le_div_of_nonneg_right (mul_le_mul (spatialSquare_le hVa hV) (hDb a k)
            (abs_nonneg _) (by positivity)) (by norm_num)
      _ = 3 / 2 * V₀ ^ 2 * ‖D‖ := by ring
  have e3 : |3 * potentialAt G m p.1 a * D a k| ≤ 3 * (|G| * δ⁻¹ * ∑ b, |m b|) * ‖D‖ := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (abs_potentialAt_le G m hδ hp a)
      (by norm_num)) (hDb a k) (abs_nonneg _) (by positivity)
  have e4 : |(G / 2) * ∑ b, m b * kernelB (p.1 a - p.1 b) (D b) k| ≤
      5 * |G| * δ⁻¹ * (∑ b, |m b|) * ‖D‖ := by
    rw [abs_mul, abs_div, abs_two]
    have hs : |∑ b, m b * kernelB (p.1 a - p.1 b) (D b) k| ≤ ∑ b, |m b| * (10 * δ⁻¹ * ‖D‖) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ((abs_kernelB_le _ _ k).trans ?_) (abs_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (invDist_le_of_mem hδ hp a b) (by norm_num))
        (norm_le_pi_norm D b) (norm_nonneg _) (by positivity)
    calc |G| / 2 * |∑ b, m b * kernelB (p.1 a - p.1 b) (D b) k| ≤
          |G| / 2 * ∑ b, |m b| * (10 * δ⁻¹ * ‖D‖) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 5 * |G| * δ⁻¹ * (∑ b, |m b|) * ‖D‖ := by rw [← Finset.sum_mul]; ring
  unfold rateLinear
  calc _ ≤ |(∑ j, p.2 a j * D a j) * p.2 a k| + |(∑ j, p.2 a j ^ 2) * D a k / 2| +
        |3 * potentialAt G m p.1 a * D a k| +
        |(G / 2) * ∑ b, m b * kernelB (p.1 a - p.1 b) (D b) k| := by
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 3 * V₀ ^ 2 * ‖D‖ + 3 / 2 * V₀ ^ 2 * ‖D‖ + 3 * (|G| * δ⁻¹ * ∑ b, |m b|) * ‖D‖ +
        5 * |G| * δ⁻¹ * (∑ b, |m b|) * ‖D‖ := by gcongr
    _ = _ := by ring

private theorem boundedOn_atoms {δ V₀ : ℝ} (hδ : 0 < δ) :
    (∀ a b : Fin N, BoundedOn (separatedSet N δ V₀) (fun p => invDist (p.1 a - p.1 b))) ∧
    (∀ (a b : Fin N) (j : Fin 3),
      BoundedOn (separatedSet N δ V₀) (fun p => invDist (p.1 a - p.1 b) * (p.1 a - p.1 b) j)) ∧
    (∀ (a : Fin N) (j : Fin 3), BoundedOn (separatedSet N δ V₀) (fun p => p.2 a j)) := by
  refine ⟨fun a b => BoundedOn.of_le (C := δ⁻¹) fun p hp => ?_, fun a b j =>
    BoundedOn.of_le (C := 1) fun p _ => abs_invDist_mul_le _ j, fun a j =>
    BoundedOn.of_le (C := V₀) fun p hp => spaceComponent_abs_le (hp.2 a) j⟩
  rw [abs_of_nonneg (invDist_nonneg _)]
  exact invDist_le_of_mem hδ hp a b

private theorem boundedOn_corrections (G : ℝ) (m : Fin N → ℝ) {δ V₀ : ℝ} (hδ : 0 < δ) (a : Fin N)
    (k : Fin 3) :
    BoundedOn (separatedSet N δ V₀) (fun p => newtonAcceleration G m p.1 a k) ∧
    BoundedOn (separatedSet N δ V₀) (fun p => forceCorrection G m p.1 p.2 a k) ∧
    BoundedOn (separatedSet N δ V₀) (fun p => rateZero G m p.1 p.2 a k) := by
  obtain ⟨hι, hν, hv⟩ := boundedOn_atoms (N := N) (V₀ := V₀) hδ
  have hU (b : Fin N) : BoundedOn (separatedSet N δ V₀) (fun p => potentialAt G m p.1 b) := by
    unfold potentialAt
    bounded_on
  have hN (a : Fin N) (k : Fin 3) :
      BoundedOn (separatedSet N δ V₀) (fun p => newtonAcceleration G m p.1 a k) := by
    refine BoundedOn.congr (F := fun p => -G * ∑ b, m b * invDist (p.1 a - p.1 b) ^ 2 *
      (invDist (p.1 a - p.1 b) * (p.1 a - p.1 b) k)) ?_ fun p => ?_
    · bounded_on
    · simp only [newtonAcceleration]
      congr 1
      exact Finset.sum_congr rfl fun b _ => by ring
  have hS : BoundedOn (separatedSet N δ V₀) (fun p => scalarGradient G m p.1 p.2 a k) := by
    refine BoundedOn.congr (F := fun p => G * ∑ b, m b * (3 / 2 * ∑ j, p.2 b j ^ 2 -
      potentialAt G m p.1 b) * invDist (p.1 a - p.1 b) ^ 2 *
      (invDist (p.1 a - p.1 b) * (p.1 a - p.1 b) k)) ?_ fun p => ?_
    · bounded_on
    · simp only [scalarGradient]
      congr 1
      exact Finset.sum_congr rfl fun b _ => by ring
  have hsingle (j : Fin 3) : BoundedOn (separatedSet N δ V₀)
      (fun _ => (Pi.single k 1 : S) j) := BoundedOn.const _
  have hW : BoundedOn (separatedSet N δ V₀) (fun p => vectorGradient G m p.1 p.2 a k) := by
    unfold vectorGradient
    refine (BoundedOn.const _).mul (BoundedOn.sum fun b => (BoundedOn.const _).mul
      (BoundedOn.sum fun j => (BoundedOn.dKernelB (hι a b) (hν a b) (hv b) hsingle j).mul
        (hv a j)))
  have hP : BoundedOn (separatedSet N δ V₀) (fun p => potentialRate G m p.1 p.2 a) := by
    refine BoundedOn.congr (F := fun p => G * ∑ b, m b * invDist (p.1 a - p.1 b) ^ 2 *
      ∑ j, (invDist (p.1 a - p.1 b) * (p.1 a - p.1 b) j) * (p.2 a j - p.2 b j)) ?_ fun p => ?_
    · bounded_on
    · simp only [potentialRate, dot, Pi.sub_apply]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hVd (b : Fin N) (j : Fin 3) : BoundedOn (separatedSet N δ V₀)
      (fun p => (p.2 a - p.2 b) j) := (hv a j).sub (hv b j)
  refine ⟨hN a k, ?_, ?_⟩
  · unfold forceCorrection
    exact (((((BoundedOn.const _).mul (BoundedOn.sum fun j => (hv a j).pow 2)).mul
      (hN a k)).sub ((hU a).mul (hN a k))).sub hS).add hW
  · unfold rateZero
    exact (((BoundedOn.const _).mul hP).mul (hv a k)).sub ((BoundedOn.const _).mul
      (BoundedOn.sum fun b => (BoundedOn.const _).mul
        (BoundedOn.dKernelB (hι a b) (hν a b) (hv b) (hVd b) k)))

private theorem norm_le_of_forall {A : Fin N → S} {M : ℝ} (hM : 0 ≤ M) (h : ∀ a k, |A a k| ≤ M) :
    ‖A‖ ≤ M :=
  (pi_norm_le_iff_of_nonneg hM).mpr fun a =>
    (pi_norm_le_iff_of_nonneg hM).mpr fun k => by rw [Real.norm_eq_abs]; exact h a k

private theorem abs_le_norm (A : Fin N → S) (a : Fin N) (k : Fin 3) : |A a k| ≤ ‖A‖ :=
  (spaceComponent_abs_le le_rfl k).trans (norm_le_pi_norm A a)

/-- **The accelerations solving the Euler–Lagrange equations of (106.17) at one instant**, on the
separated configurations: if `F_a = ṗ_a(A)` for all bodies, then `‖A − a_PN‖ ≤ C/c⁴` with one
constant for all `c ≥ c₁` (pointwise in time, an algebraic statement). -/
theorem norm_sub_eihAcceleration_le (G : ℝ) (m : Fin N → ℝ) {δ V₀ : ℝ} (hδ : 0 < δ)
    (hV : 0 ≤ V₀) :
    ∃ C c₁, 0 ≤ C ∧ 1 ≤ c₁ ∧ ∀ c, c₁ ≤ c → ∀ p ∈ separatedSet N δ V₀, ∀ A : Fin N → S,
      (∀ a k, eihForce G m c p.1 p.2 a k = eihMomentumRate G m c p.1 p.2 A a k) →
      ‖A - eihAcceleration G m c p.1 p.2‖ ≤ C / c ^ 4 := by
  have hb := fun a k => boundedOn_corrections (V₀ := V₀) G m hδ a k
  choose CN hCN0 hCN using fun a k => (hb a k).1
  choose CF hCF0 hCF using fun a k => (hb a k).2.1
  choose CR hCR0 hCR using fun a k => (hb a k).2.2
  set KN := ∑ a, ∑ k, CN a k
  set KF := ∑ a, ∑ k, (CF a k + CR a k)
  have hle {f : Fin N → Fin 3 → ℝ} (hf : ∀ a k, 0 ≤ f a k) (a : Fin N) (k : Fin 3) :
      f a k ≤ ∑ a, ∑ k, f a k :=
    (Finset.single_le_sum (fun k _ => hf a k) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun k _ => hf a k) (Finset.mem_univ a))
  have hKN : 0 ≤ KN := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun k _ => hCN0 a k
  have hKF : 0 ≤ KF := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun k _ =>
    add_nonneg (hCF0 a k) (hCR0 a k)
  set CL := 9 / 2 * V₀ ^ 2 + 8 * |G| * δ⁻¹ * ∑ b, |m b|
  have hCL : 0 ≤ CL := by
    have : 0 ≤ ∑ b, |m b| := Finset.sum_nonneg fun b _ => abs_nonneg _
    have : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    positivity
  set K₁ := KF + CL * (2 * (KN + KF))
  refine ⟨CL * K₁, 2 * CL + 1, by positivity, by linarith, ?_⟩
  intro c hc p hp A hEL
  set ε := epsilon c with hε
  have hc1 : 1 ≤ c := by linarith
  have hε0 : 0 ≤ ε := epsilon_nonneg c
  have hε1 : ε ≤ 1 := epsilon_le_one hc1
  have hεL : ε * CL ≤ 1 / 2 := by
    have hc2 : 2 * CL < c ^ 2 := by nlinarith
    rw [hε, epsilon, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    linarith
  set AN : Fin N → S := fun b => newtonAcceleration G m p.1 b
  -- the equation for the accelerations
  have hA (a : Fin N) (k : Fin 3) : A a k - AN a k = ε * (forceCorrection G m p.1 p.2 a k -
      rateZero G m p.1 p.2 a k - rateLinear G m p.1 p.2 A a k) := by
    have h := hEL a k
    rw [eihForce_eq, eihMomentumRate_eq] at h
    simp only [AN]
    linear_combination -h
  have hFR (a : Fin N) (k : Fin 3) :
      |forceCorrection G m p.1 p.2 a k - rateZero G m p.1 p.2 a k| ≤ KF :=
    (abs_sub _ _).trans ((add_le_add (hCF a k p hp) (hCR a k p hp)).trans
      (hle (f := fun a k => CF a k + CR a k) (fun a k => add_nonneg (hCF0 a k) (hCR0 a k)) a k))
  have hAN (a : Fin N) (k : Fin 3) : |AN a k| ≤ KN :=
    (hCN a k p hp).trans (hle hCN0 a k)
  -- a priori bound
  have hAb : ‖A‖ ≤ 2 * (KN + KF) := by
    have h1 : ‖A‖ ≤ KN + KF + ε * CL * ‖A‖ := by
      refine norm_le_of_forall (by positivity) fun a k => ?_
      have hL := abs_rateLinear_le G m hδ hV hp A a k
      calc |A a k| = |AN a k + ε * (forceCorrection G m p.1 p.2 a k - rateZero G m p.1 p.2 a k -
            rateLinear G m p.1 p.2 A a k)| := by rw [← hA a k]; ring_nf
        _ ≤ |AN a k| + ε * (|forceCorrection G m p.1 p.2 a k - rateZero G m p.1 p.2 a k| +
            |rateLinear G m p.1 p.2 A a k|) := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul, abs_of_nonneg hε0]
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) hε0
        _ ≤ KN + ε * (KF + CL * ‖A‖) :=
          add_le_add (hAN a k) (mul_le_mul_of_nonneg_left (add_le_add (hFR a k) hL) hε0)
        _ ≤ KN + KF + ε * CL * ‖A‖ := by nlinarith
    nlinarith [norm_nonneg A]
  -- the deviation from the Newtonian accelerations
  have hD : ‖A - AN‖ ≤ ε * K₁ := by
    refine norm_le_of_forall (by positivity) fun a k => ?_
    rw [Pi.sub_apply, Pi.sub_apply, hA a k, abs_mul, abs_of_nonneg hε0]
    refine mul_le_mul_of_nonneg_left ?_ hε0
    refine (abs_sub _ _).trans (add_le_add (hFR a k) ?_)
    exact (abs_rateLinear_le G m hδ hV hp A a k).trans (mul_le_mul_of_nonneg_left hAb hCL)
  -- the exact identity
  have hc4 : ε ^ 2 = 1 / c ^ 4 := by rw [hε, epsilon, inv_pow, ← pow_mul, one_div]
  refine norm_le_of_forall (by positivity) fun a k => ?_
  have hid : (A - eihAcceleration G m c p.1 p.2) a k =
      -(ε * rateLinear G m p.1 p.2 (A - AN) a k) := by
    have h1 := eihMomentumRate_eq G m c p.1 p.2 A a k
    have h2 := eihMomentumRate_eq G m c p.1 p.2 AN a k
    have h3 := rateLinear_sub G m p.1 p.2 A AN a k
    simp only [Pi.sub_apply, eihAcceleration]
    rw [hEL a k]
    simp only [AN] at h2 h3 ⊢
    linear_combination -h1 + h2 - ε * h3
  rw [hid, abs_neg, abs_mul, abs_of_nonneg hε0]
  calc ε * |rateLinear G m p.1 p.2 (A - AN) a k| ≤ ε * (CL * (ε * K₁)) :=
        mul_le_mul_of_nonneg_left ((abs_rateLinear_le G m hδ hV hp _ a k).trans
          (mul_le_mul_of_nonneg_left hD hCL)) hε0
    _ = CL * K₁ * ε ^ 2 := by ring
    _ = CL * K₁ / c ^ 4 := by rw [hc4]; ring

/-- **The acceleration of the bodies in the second approximation (target (v)).** For bodies of
nonzero masses on a `C²` motion satisfying the Euler–Lagrange equations of (106.17) at the time
`t`, with mutual distances at least `δ` and speeds at most `V₀`, the accelerations are the
explicit `eihAcceleration` up to `C/c⁴`, with one constant for all `c ≥ c₁`. -/
theorem eulerLagrange_acceleration_error (G : ℝ) (m : Fin N → ℝ) (hm : ∀ a, m a ≠ 0)
    {δ V₀ : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V₀) :
    ∃ C c₁, 0 ≤ C ∧ 1 ≤ c₁ ∧ ∀ c, c₁ ≤ c → ∀ X : ℝ → Fin N → S, ContDiff ℝ 2 X → ∀ t,
      (∀ a b, a ≠ b → δ ≤ euclidNorm (X t a - X t b)) → (∀ a, ‖deriv X t a‖ ≤ V₀) →
      Mechanics.eulerLagrange (eihLagrangian G m c) X t = 0 →
      ‖deriv (deriv X) t - eihAcceleration G m c (X t) (deriv X t)‖ ≤ C / c ^ 4 := by
  obtain ⟨C, c₁, hC, hc₁, h⟩ := norm_sub_eihAcceleration_le G m hδ hV (N := N)
  refine ⟨C, c₁, hC, hc₁, fun c hc X hX t hsepδ hVt hEL => ?_⟩
  have hsep : ∀ b d, b ≠ d → X t b ≠ X t d := fun b d hbd heq => by
    have := hsepδ b d hbd
    rw [heq, sub_self, euclidNorm, Finset.sum_eq_zero (fun j _ => by simp), Real.sqrt_zero]
      at this
    linarith
  refine h c hc (X t, deriv X t) ⟨hsepδ, hVt⟩ _ fun a k => ?_
  have h1 := eulerLagrange_eihLagrangian G m c hX hsep a k
  rw [hEL, zero_apply, eq_comm, mul_eq_zero, or_iff_right (hm a), sub_eq_zero] at h1
  exact h1

/-! ### Permutation invariance -/

private theorem sum_perm₂ (σ : Equiv.Perm (Fin N)) (F : Fin N → Fin N → ℝ) :
    ∑ a, ∑ b, F (σ a) (σ b) = ∑ a, ∑ b, F a b :=
  calc ∑ a, ∑ b, F (σ a) (σ b) = ∑ a, ∑ b, F (σ a) b :=
        Finset.sum_congr rfl fun a _ => Equiv.sum_comp σ (fun b => F (σ a) b)
    _ = ∑ a, ∑ b, F a b := Equiv.sum_comp σ (fun a => ∑ b, F a b)

private theorem sum_perm₃ (σ : Equiv.Perm (Fin N)) (F : Fin N → Fin N → Fin N → ℝ) :
    ∑ a, ∑ b, ∑ d, F (σ a) (σ b) (σ d) = ∑ a, ∑ b, ∑ d, F a b d :=
  calc ∑ a, ∑ b, ∑ d, F (σ a) (σ b) (σ d) = ∑ a, ∑ b, ∑ d, F (σ a) (σ b) d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Equiv.sum_comp σ (fun d => F (σ a) (σ b) d)
    _ = ∑ a, ∑ b, ∑ d, F a b d := sum_perm₂ σ (fun a b => ∑ d, F a b d)

/-- **The Lagrangian (106.17) is invariant under a relabelling of the bodies (target (ii)).** -/
theorem eihLagrangian_perm (σ : Equiv.Perm (Fin N)) (G : ℝ) (m : Fin N → ℝ) (c s : ℝ)
    (z : (Fin N → S) × (Fin N → S)) :
    eihLagrangian G (m ∘ σ) c s (z.1 ∘ σ, z.2 ∘ σ) = eihLagrangian G m c s z := by
  simp only [eihLagrangian, Function.comp_apply]
  have h1 := Equiv.sum_comp σ (fun a => m a * (∑ j, z.2 a j ^ 2) / 2 +
    epsilon c * (m a * (∑ j, z.2 a j ^ 2) ^ 2 / 8))
  have h2 := sum_perm₂ σ (fun a b => m a * m b * invDist (z.1 a - z.1 b))
  have h3 := sum_perm₂ σ (fun a b => m a * m b * invDist (z.1 a - z.1 b) *
    pairVelocity (z.2 a) (z.2 b) (z.1 a - z.1 b))
  have h4 := sum_perm₃ σ (fun a b d => m a * m b * m d * invDist (z.1 a - z.1 b) *
    invDist (z.1 a - z.1 d))
  rw [h1, h2, h3, h4]

/-- The Newtonian acceleration is equivariant under a relabelling of the bodies. -/
theorem newtonAcceleration_perm (σ : Equiv.Perm (Fin N)) (G : ℝ) (m : Fin N → ℝ)
    (X : Fin N → S) (a : Fin N) :
    newtonAcceleration G (m ∘ σ) (X ∘ σ) a = newtonAcceleration G m X (σ a) := by
  funext k
  simp only [newtonAcceleration, Function.comp_apply]
  congr 1
  exact Equiv.sum_comp σ (fun b => m b * invDist (X (σ a) - X b) ^ 3 * (X (σ a) - X b) k)

/-! ### The Newtonian limit -/

/-- The Newtonian Lagrangian `Σ_a m_a v_a²/2 + Σ_{a ≠ b} G m_a m_b/(2 r_ab)` of `N` bodies. -/
def newtonLagrangian (G : ℝ) (m : Fin N → ℝ) : Mechanics.Lagrangian (Fin N → S) := fun _ z =>
  ∑ a, m a * (∑ j, z.2 a j ^ 2) / 2 + G / 2 * ∑ a, ∑ b, m a * m b * invDist (z.1 a - z.1 b)

/-- The coefficient of `c⁻²` in (106.17). -/
def eihCorrectionLagrangian (G : ℝ) (m : Fin N → ℝ) : Mechanics.Lagrangian (Fin N → S) :=
  fun _ z => ∑ a, m a * (∑ j, z.2 a j ^ 2) ^ 2 / 8 +
    G / 2 * ∑ a, ∑ b, m a * m b * invDist (z.1 a - z.1 b) *
      pairVelocity (z.2 a) (z.2 b) (z.1 a - z.1 b) -
    G ^ 2 / 2 * ∑ a, ∑ b, ∑ d, m a * m b * m d * invDist (z.1 a - z.1 b) * invDist (z.1 a - z.1 d)

/-- **(106.17) is the Newtonian Lagrangian plus `c⁻²` times its correction.** -/
theorem eihLagrangian_eq_add (G : ℝ) (m : Fin N → ℝ) (c s : ℝ) (z : (Fin N → S) × (Fin N → S)) :
    eihLagrangian G m c s z =
      newtonLagrangian G m s z + epsilon c * eihCorrectionLagrangian G m s z := by
  simp only [eihLagrangian, newtonLagrangian, eihCorrectionLagrangian, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

theorem tendsto_epsilon : Tendsto epsilon atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)

/-- **The Newtonian limit of (106.17) (target (iii))**: as `c → ∞` the Lagrangian tends to the
Newtonian Lagrangian. -/
theorem tendsto_eihLagrangian (G : ℝ) (m : Fin N → ℝ) (s : ℝ) (z : (Fin N → S) × (Fin N → S)) :
    Tendsto (fun c => eihLagrangian G m c s z) atTop (𝓝 (newtonLagrangian G m s z)) := by
  simp only [eihLagrangian_eq_add]
  simpa using tendsto_const_nhds.add (tendsto_epsilon.mul_const (eihCorrectionLagrangian G m s z))

theorem epsilon_zero : epsilon 0 = 0 := by simp [epsilon]

/-- With the convention `0⁻¹ = 0`, `ε(0) = 0` and (106.17) at `c = 0` is the Newtonian
Lagrangian. -/
theorem eihLagrangian_zero (G : ℝ) (m : Fin N → ℝ) :
    eihLagrangian G m 0 = newtonLagrangian G m := by
  funext s z
  rw [eihLagrangian_eq_add, epsilon_zero, zero_mul, add_zero]

/-- **The Euler–Lagrange equations of the Newtonian Lagrangian** are Newton's equations
`m_a ẍ_a = m_a a_N`. -/
theorem eulerLagrange_newtonLagrangian (G : ℝ) (m : Fin N → ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N)
    (k : Fin 3) :
    Mechanics.eulerLagrange (newtonLagrangian G m) X t (Pi.single a (Pi.single k 1)) =
      m a * (newtonAcceleration G m (X t) a k - deriv (deriv X) t a k) := by
  rw [← eihLagrangian_zero, eulerLagrange_eihLagrangian G m 0 hX hsep a k, eihForce_eq,
    eihMomentumRate_eq, epsilon_zero]
  ring

/-- **The Newtonian limit of the Euler–Lagrange equations**: along a fixed `C²` motion with the
bodies apart at `t`, the residual of (106.17) tends to the Newtonian residual as `c → ∞`. -/
theorem tendsto_eulerLagrange_eihLagrangian (G : ℝ) (m : Fin N → ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N)
    (k : Fin 3) :
    Tendsto (fun c => Mechanics.eulerLagrange (eihLagrangian G m c) X t
        (Pi.single a (Pi.single k 1))) atTop
      (𝓝 (Mechanics.eulerLagrange (newtonLagrangian G m) X t (Pi.single a (Pi.single k 1)))) := by
  simp only [eulerLagrange_eihLagrangian G m _ hX hsep a k,
    eulerLagrange_newtonLagrangian G m hX hsep a k, eihForce_eq, eihMomentumRate_eq]
  have h := (tendsto_epsilon.mul_const (m a * (forceCorrection G m (X t) (deriv X t) a k -
    (rateZero G m (X t) (deriv X t) a k +
      rateLinear G m (X t) (deriv X t) (deriv (deriv X) t) a k)))).const_add
    (m a * (newtonAcceleration G m (X t) a k - deriv (deriv X) t a k))
  simp only [zero_mul, add_zero] at h
  refine h.congr fun c => ?_
  ring

/-- **The Newtonian limit of the acceleration**: `a_PN → a_N` as `c → ∞`. -/
theorem tendsto_eihAcceleration (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) :
    Tendsto (fun c => eihAcceleration G m c X V) atTop
      (𝓝 (fun a => newtonAcceleration G m X a)) := by
  refine tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun k => ?_
  simp only [eihAcceleration, eihForce_eq, eihMomentumRate_eq]
  have h := (tendsto_epsilon.mul_const (forceCorrection G m X V a k -
    (rateZero G m X V a k + rateLinear G m X V (fun b => newtonAcceleration G m X b) a k))
    ).const_add (newtonAcceleration G m X a k)
  simp only [zero_mul, add_zero] at h
  refine h.congr fun c => ?_
  ring

/-! ### The test-mass limit -/

private theorem sum_update_mul_eq (m : Fin N → ℝ) (a : Fin N) (μ ν : ℝ) (f : Fin N → ℝ)
    (hf : f a = 0) :
    ∑ b, Function.update m a μ b * f b = ∑ b, Function.update m a ν b * f b := by
  rw [Fintype.sum_eq_add_sum_compl a, Fintype.sum_eq_add_sum_compl a
    (fun b => Function.update m a ν b * f b)]
  simp only [hf, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' : b ≠ a := by simpa using hb
  rw [Function.update_of_ne hb', Function.update_of_ne hb']

private theorem sum_update_mul_eq_self (m : Fin N → ℝ) (a : Fin N) (μ : ℝ) (f : Fin N → ℝ)
    (hf : f a = 0) : ∑ b, Function.update m a μ b * f b = ∑ b, m b * f b := by
  rw [sum_update_mul_eq m a μ (m a) f hf, Function.update_eq_self]

theorem potentialAt_update_self (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N) (μ : ℝ) :
    potentialAt G (Function.update m a μ) X a = potentialAt G m X a := by
  rw [potentialAt, potentialAt, sum_update_mul_eq_self m a μ _ (by simp)]

theorem potentialAt_update_of_ne (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) {a b : Fin N}
    (μ : ℝ) :
    potentialAt G (Function.update m a μ) X b =
      potentialAt G (Function.update m a 0) X b + G * μ * invDist (X b - X a) := by
  simp only [potentialAt]
  rw [Fintype.sum_eq_add_sum_compl a, Fintype.sum_eq_add_sum_compl a
    (fun c => Function.update m a 0 c * invDist (X b - X c))]
  simp only [Function.update_self, zero_mul, zero_add]
  have h : ∑ c ∈ ({a}ᶜ : Finset (Fin N)), Function.update m a μ c * invDist (X b - X c) =
      ∑ c ∈ ({a}ᶜ : Finset (Fin N)), Function.update m a 0 c * invDist (X b - X c) :=
    Finset.sum_congr rfl fun c hc => by
      have hc' : c ≠ a := by simpa using hc
      rw [Function.update_of_ne hc', Function.update_of_ne hc']
  rw [h]
  ring

/-- **The field felt by a light body.** The second potential seen by the body `a` is that of the
other `N − 1` bodies alone plus `m_a G² Σ_{b ≠ a} m_b/(r_b(x) r_ab)`. -/
theorem othersScalarPotential_update_mass (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N)
    (μ : ℝ) (x : S) :
    othersScalarPotential G (Function.update m a μ) X V a x =
      othersScalarPotential G (Function.update m a 0) X V a x + μ * G ^ 2 *
        ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * invDist (x - X b) * invDist (X b - X a) := by
  rw [othersScalarPotential, othersScalarPotential, Finset.mul_sum (s := ({a}ᶜ : Finset (Fin N))),
    Finset.mul_sum (s := ({a}ᶜ : Finset (Fin N))), Finset.mul_sum (s := ({a}ᶜ : Finset (Fin N))),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' : b ≠ a := by simpa using hb
  rw [Function.update_of_ne hb', Function.update_of_ne hb', potentialAt_update_of_ne G m X μ]
  ring

/-- The potentials of the other bodies of a massless body `a` do not depend on its position and
velocity: they are generated by the other `N − 1` bodies. -/
theorem others_update_config (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) (y u : S) :
    othersPotential G (Function.update m a 0) (Function.update X a y) a =
        othersPotential G (Function.update m a 0) X a ∧
      othersScalarPotential G (Function.update m a 0) (Function.update X a y)
          (Function.update V a u) a = othersScalarPotential G (Function.update m a 0) X V a ∧
      othersVectorPotential G (Function.update m a 0) (Function.update X a y)
          (Function.update V a u) a = othersVectorPotential G (Function.update m a 0) X V a := by
  have hX : ∀ b ∈ ({a}ᶜ : Finset (Fin N)), Function.update X a y b = X b := fun b hb =>
    Function.update_of_ne (by simpa using hb) _ _
  have hV : ∀ b ∈ ({a}ᶜ : Finset (Fin N)), Function.update V a u b = V b := fun b hb =>
    Function.update_of_ne (by simpa using hb) _ _
  have hU : ∀ b ∈ ({a}ᶜ : Finset (Fin N)),
      potentialAt G (Function.update m a 0) (Function.update X a y) b =
        potentialAt G (Function.update m a 0) X b := fun b hb => by
    simp only [potentialAt]
    rw [Fintype.sum_eq_add_sum_compl a, Fintype.sum_eq_add_sum_compl a
      (fun c => Function.update m a 0 c * invDist (X b - X c))]
    simp only [Function.update_self, zero_mul, zero_add, hX b hb]
    exact congrArg _ (Finset.sum_congr rfl fun c hc => by rw [hX c hc])
  refine ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => funext fun k => ?_⟩
  · simp only [othersPotential]
    exact congrArg _ (Finset.sum_congr rfl fun b hb => by rw [hX b hb])
  · simp only [othersScalarPotential]
    exact congrArg _ (Finset.sum_congr rfl fun b hb => by rw [hX b hb, hV b hb, hU b hb])
  · simp only [othersVectorPotential]
    exact congrArg _ (Finset.sum_congr rfl fun b hb => by rw [hX b hb, hV b hb])

theorem eihForce_update_mass (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V : Fin N → S) (a : Fin N)
    (μ : ℝ) (k : Fin 3) :
    eihForce G (Function.update m a μ) c X V a k =
      eihForce G (Function.update m a 0) c X V a k + epsilon c * (μ * G ^ 2 *
        ∑ b, m b * invDist (X a - X b) ^ 4 * (X a - X b) k) := by
  have hN : ∀ ν, newtonAcceleration G (Function.update m a ν) X a k =
      newtonAcceleration G m X a k := fun ν => by
    simp only [newtonAcceleration, mul_assoc]
    rw [sum_update_mul_eq_self m a ν _ (by simp)]
  have hW : ∀ ν, vectorGradient G (Function.update m a ν) X V a k = vectorGradient G m X V a k :=
    fun ν => by
      simp only [vectorGradient]
      rw [sum_update_mul_eq_self m a ν _ (by simp [dKernelB_zero_left])]
  have hS : scalarGradient G (Function.update m a μ) X V a k =
      scalarGradient G (Function.update m a 0) X V a k - μ * G ^ 2 *
        ∑ b, m b * invDist (X a - X b) ^ 4 * (X a - X b) k := by
    simp only [scalarGradient]
    have h1 : ∀ ν, ∑ b, Function.update m a ν b * (3 / 2 * ∑ j, V b j ^ 2 -
        potentialAt G (Function.update m a ν) X b) * invDist (X a - X b) ^ 3 * (X a - X b) k =
        ∑ b, m b * ((3 / 2 * ∑ j, V b j ^ 2 - potentialAt G (Function.update m a ν) X b) *
          invDist (X a - X b) ^ 3 * (X a - X b) k) := fun ν => by
      simp only [mul_assoc]
      rw [sum_update_mul_eq_self m a ν _ (by simp)]
    rw [h1, h1, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases eq_or_ne b a with rfl | hb
    · simp
    · rw [potentialAt_update_of_ne G m X μ, invDist_sub_comm (X b)]
      ring
  simp only [eihForce, hN, hW, potentialAt_update_self, hS]
  ring

theorem eihMomentumRate_update_mass (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V A : Fin N → S)
    (a : Fin N) (μ : ℝ) (k : Fin 3) :
    eihMomentumRate G (Function.update m a μ) c X V A a k =
      eihMomentumRate G (Function.update m a 0) c X V A a k := by
  have hP : ∀ ν, potentialRate G (Function.update m a ν) X V a = potentialRate G m X V a :=
    fun ν => by
      simp only [potentialRate, mul_assoc]
      rw [sum_update_mul_eq_self m a ν _ (by simp)]
  have hB : ∀ ν, vectorPotentialRate G (Function.update m a ν) X V A a k =
      vectorPotentialRate G m X V A a k := fun ν => by
    simp only [vectorPotentialRate]
    rw [sum_update_mul_eq_self m a ν _ (by simp [dKernelB_zero_left, kernelB_zero_left])]
  simp only [eihMomentumRate, hP, hB, potentialAt_update_self]

/-- **The test-mass limit (target (iv)), exactly.** For a body `a` of the mass `μ ≠ 0`, the
Euler–Lagrange residual of (106.17) for `a` divided by `μ` is the residual of a unit test mass in
the potentials of the other `N − 1` bodies alone (`others_update_config`) plus `μ` times the
explicit three-mass term `ε G² Σ_b m_b (x_a − x_b)_k / r_ab⁴`. -/
theorem eulerLagrange_testMass (G : ℝ) (m : Fin N → ℝ) (c : ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N) (k : Fin 3)
    {μ : ℝ} (hμ : μ ≠ 0) :
    μ⁻¹ * Mechanics.eulerLagrange (eihLagrangian G (Function.update m a μ) c) X t
        (Pi.single a (Pi.single k 1)) =
      Mechanics.eulerLagrange (fun s => testLagrangian 1 c
          (othersPotential G (Function.update m a 0) (X s) a)
          (othersScalarPotential G (Function.update m a 0) (X s) (deriv X s) a)
          (othersVectorPotential G (Function.update m a 0) (X s) (deriv X s) a))
        (fun s => X s a) t (Pi.single k 1) +
      μ * (epsilon c * G ^ 2 * ∑ b, m b * invDist (X t a - X t b) ^ 4 * (X t a - X t b) k) := by
  rw [eulerLagrange_eihLagrangian _ _ c hX hsep a k, eulerLagrange_testFamily_others 1 G _ c hX
    hsep a k, Function.update_self, eihForce_update_mass, eihMomentumRate_update_mass]
  field_simp
  ring

/-- **The test-mass limit (target (iv))**: as `m_a → 0`, the Euler–Lagrange residual of (106.17)
for the body `a` per unit mass tends to the residual of a test body in the potentials of the
other bodies alone. -/
theorem tendsto_eulerLagrange_testMass (G : ℝ) (m : Fin N → ℝ) (c : ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N)
    (k : Fin 3) :
    Tendsto (fun μ => μ⁻¹ * Mechanics.eulerLagrange (eihLagrangian G (Function.update m a μ) c)
        X t (Pi.single a (Pi.single k 1))) (𝓝[≠] 0)
      (𝓝 (Mechanics.eulerLagrange (fun s => testLagrangian 1 c
          (othersPotential G (Function.update m a 0) (X s) a)
          (othersScalarPotential G (Function.update m a 0) (X s) (deriv X s) a)
          (othersVectorPotential G (Function.update m a 0) (X s) (deriv X s) a))
        (fun s => X s a) t (Pi.single k 1))) := by
  set K := Mechanics.eulerLagrange (fun s => testLagrangian 1 c
      (othersPotential G (Function.update m a 0) (X s) a)
      (othersScalarPotential G (Function.update m a 0) (X s) (deriv X s) a)
      (othersVectorPotential G (Function.update m a 0) (X s) (deriv X s) a))
      (fun s => X s a) t (Pi.single k 1) with hK
  set L := epsilon c * G ^ 2 * ∑ b, m b * invDist (X t a - X t b) ^ 4 * (X t a - X t b) k
  have hc : Continuous (fun μ : ℝ => K + μ * L) := by fun_prop
  have h0 := hc.tendsto 0
  simp only [zero_mul, add_zero] at h0
  exact (h0.mono_left nhdsWithin_le_nhds).congr' (eventually_nhdsWithin_of_forall fun μ hμ =>
    (eulerLagrange_testMass G m c hX hsep a k hμ).symm)

/-- **The test body agrees with the library's test-body Lagrangian.** For a post-Newtonian
family whose potentials are those of the other bodies along their motion, the unit-mass test-body
Lagrangian of the limit is `PostNewtonianMetricFamily.lagrangian 1 c`; so
`PostNewtonianMetricFamily.eulerLagrange_acceleration_error` applies to the limit equation. -/
theorem testLagrangian_eq_lagrangian {U : TopologicalSpace.Opens NewtonianCoordinates}
    (f : PostNewtonian.PostNewtonianMetricFamily U) (μ c : ℝ) (Φ ψ : ℝ → S → ℝ) (B : ℝ → S → S)
    (hΦ : ∀ q, f.potential q = Φ (q 0) (Fin.tail q))
    (hψ : ∀ q, f.scalarPotential q = ψ (q 0) (Fin.tail q))
    (hB : ∀ q, f.vectorPotential q = B (q 0) (Fin.tail q)) :
    (fun s => testLagrangian μ c (Φ s) (ψ s) (B s)) = f.lagrangian μ c := by
  funext s z
  rw [lagrangian_eq_testLagrangian]
  simp only [hΦ, hψ, hB, Fin.cons_zero, Fin.tail_cons]

/-- **Agreement of the test-mass limit with `eulerLagrange_acceleration_error`.** If the
potentials of a post-Newtonian family `f` are those of the bodies `b ≠ a` (with `m_a = 0`) along
their motion `X`, then a path satisfying the limit test-body equation has the acceleration
`f.postNewtonianAcceleration` up to `C/c⁴`. -/
theorem testMass_acceleration_error {U : TopologicalSpace.Opens NewtonianCoordinates}
    (f : PostNewtonian.PostNewtonianMetricFamily U) (G : ℝ) (m : Fin N → ℝ) (X : ℝ → Fin N → S)
    (a : Fin N)
    (hΦ : ∀ q, f.potential q = othersPotential G (Function.update m a 0) (X (q 0)) a (Fin.tail q))
    (hψ : ∀ q, f.scalarPotential q = othersScalarPotential G (Function.update m a 0) (X (q 0))
      (deriv X (q 0)) a (Fin.tail q))
    (hB : ∀ q, f.vectorPotential q = othersVectorPotential G (Function.update m a 0) (X (q 0))
      (deriv X (q 0)) a (Fin.tail q)) {V : ℝ} (hV : 0 ≤ V) :
    ∃ C c₁, 0 ≤ C ∧ 1 ≤ c₁ ∧ ∀ c, c₁ ≤ c → ∀ x : ℝ → S, ContDiff ℝ 2 x → ∀ t,
      (Fin.cons t (x t) : NewtonianCoordinates) ∈ U → ‖deriv x t‖ ≤ V →
      Mechanics.eulerLagrange (fun s => testLagrangian 1 c
          (othersPotential G (Function.update m a 0) (X s) a)
          (othersScalarPotential G (Function.update m a 0) (X s) (deriv X s) a)
          (othersVectorPotential G (Function.update m a 0) (X s) (deriv X s) a)) x t = 0 →
      ‖deriv (deriv x) t - f.postNewtonianAcceleration c (Fin.cons t (x t)) (deriv x t)‖ ≤
        C / c ^ 4 := by
  obtain ⟨C, c₁, hC, hc₁, h⟩ := f.eulerLagrange_acceleration_error hV
  refine ⟨C, c₁, hC, hc₁, fun c hc x hx t ht hv hEL => ?_⟩
  rw [testLagrangian_eq_lagrangian f 1 c _ _ _ hΦ hψ hB] at hEL
  exact h 1 c one_ne_zero hc x hx t ht hv hEL

/-! ### Instances -/

/-- **(106.17) for two bodies**:
`L = m₁v₁²/2 + m₂v₂²/2 + G m₁m₂/r + c⁻²[(m₁v₁⁴ + m₂v₂⁴)/8`
`  + (G m₁m₂/2r)(3v₁² + 3v₂² − 7 v₁ · v₂ − (v₁ · n)(v₂ · n)) − G² m₁m₂(m₁ + m₂)/2r²]`. -/
theorem eihLagrangian_two (G m₁ m₂ c s : ℝ) (x₁ x₂ v₁ v₂ : S) :
    eihLagrangian G ![m₁, m₂] c s (![x₁, x₂], ![v₁, v₂]) =
      m₁ * (∑ j, v₁ j ^ 2) / 2 + m₂ * (∑ j, v₂ j ^ 2) / 2 + G * m₁ * m₂ * invDist (x₁ - x₂) +
        epsilon c * (m₁ * (∑ j, v₁ j ^ 2) ^ 2 / 8 + m₂ * (∑ j, v₂ j ^ 2) ^ 2 / 8 +
          G * m₁ * m₂ * invDist (x₁ - x₂) / 2 * (3 * ∑ j, v₁ j ^ 2 + 3 * ∑ j, v₂ j ^ 2 -
            7 * dot v₁ v₂ - dot v₁ (x₁ - x₂) * dot v₂ (x₁ - x₂) * invDist (x₁ - x₂) ^ 2) -
          G ^ 2 * m₁ * m₂ * (m₁ + m₂) * invDist (x₁ - x₂) ^ 2 / 2) := by
  have h21 : invDist (x₂ - x₁) = invDist (x₁ - x₂) := invDist_sub_comm x₂ x₁
  have hd (v : S) : dot v (x₂ - x₁) = -dot v (x₁ - x₂) := by
    rw [← neg_sub x₁ x₂, dot_neg_right]
  simp only [eihLagrangian, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, invDist_zero, pairVelocity, h21, hd, dot_comm v₂ v₁]
  ring

/-- A collision-free configuration of two bodies: `x₁ = (1, 0, 0)`, `x₂ = (−1, 0, 0)` at the
distance `2`. -/
theorem euclidNorm_two_sep : euclidNorm (![1, 0, 0] - ![-1, 0, 0]) = 2 := by
  have h : ∑ j : Fin 3, (![1, 0, 0] - ![-1, 0, 0] : S) j ^ 2 = 4 := by
    simp [Fin.sum_univ_three]
    norm_num
  rw [euclidNorm, h, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem clm_eq_zero_of_basis (L : (Fin N → S) →L[ℝ] ℝ)
    (h : ∀ a k, L (Pi.single a (Pi.single k 1)) = 0) : L = 0 := by
  have h1 : ∀ (a : Fin N) (k : Fin 3) (r : ℝ), L (Pi.single a (Pi.single k r)) = 0 := by
    intro a k r
    have e : (Pi.single a (Pi.single k r : S) : Fin N → S) = r • Pi.single a (Pi.single k 1) := by
      funext b j
      by_cases hb : b = a
      · subst hb
        by_cases hj : j = k
        · subst hj; simp
        · simp [hj]
      · simp [hb]
    rw [e, map_smul, h, smul_zero]
  have h2 : ∀ (a : Fin N) (x : S), L (Pi.single a x) = 0 := by
    intro a x
    have hM : L.toLinearMap.comp (LinearMap.single ℝ (fun _ : Fin N => S) a) = 0 :=
      LinearMap.pi_ext fun k r => by simp [h1]
    simpa using congrArg (fun F : S →ₗ[ℝ] ℝ => F x) hM
  exact ContinuousLinearMap.coe_injective (LinearMap.pi_ext fun a x => by simp [h2])

/-- **The Euler–Lagrange equations of (106.17) can be satisfied at any instant.** For every
separated configuration `(x, v)` and `c ≥ c₁`, the linear equations `F_a = ṗ_a(A)` for the
accelerations have a solution (a contraction for `c ≥ c₁`), and the quadratic motion through
`(x, v)` with these accelerations satisfies the Euler–Lagrange equations at `t`. -/
theorem exists_eulerLagrange (G : ℝ) (m : Fin N → ℝ) {δ V₀ : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V₀) :
    ∃ c₁, 1 ≤ c₁ ∧ ∀ c, c₁ ≤ c → ∀ p ∈ separatedSet N δ V₀, ∀ t : ℝ,
      ∃ X : ℝ → Fin N → S, ContDiff ℝ ∞ X ∧ X t = p.1 ∧ deriv X t = p.2 ∧
        Mechanics.eulerLagrange (eihLagrangian G m c) X t = 0 := by
  set CL := 9 / 2 * V₀ ^ 2 + 8 * |G| * δ⁻¹ * ∑ b, |m b|
  have hCL : 0 ≤ CL := by
    have : 0 ≤ ∑ b, |m b| := Finset.sum_nonneg fun b _ => abs_nonneg _
    have : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    positivity
  refine ⟨2 * CL + 1, by linarith, fun c hc p hp t => ?_⟩
  set ε := epsilon c with hε
  have hc1 : 1 ≤ c := by linarith
  have hε0 : 0 ≤ ε := epsilon_nonneg c
  have hεL : ε * CL ≤ 1 / 2 := by
    have hc2 : 2 * CL < c ^ 2 := by nlinarith
    rw [hε, epsilon, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    linarith
  -- the contraction
  set T : (Fin N → S) → (Fin N → S) := fun A a k => newtonAcceleration G m p.1 a k +
    ε * (forceCorrection G m p.1 p.2 a k - rateZero G m p.1 p.2 a k -
      rateLinear G m p.1 p.2 A a k) with hT
  have hTd (A B : Fin N → S) : dist (T A) (T B) ≤ (1 / 2 : NNReal) * dist A B := by
    rw [dist_eq_norm, dist_eq_norm]
    refine norm_le_of_forall (by positivity) fun a k => ?_
    have h := rateLinear_sub G m p.1 p.2 A B a k
    have e : (T A - T B) a k = -(ε * rateLinear G m p.1 p.2 (A - B) a k) := by
      simp only [hT, Pi.sub_apply]
      rw [← h]
      ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg hε0]
    calc ε * |rateLinear G m p.1 p.2 (A - B) a k| ≤ ε * (CL * ‖A - B‖) :=
          mul_le_mul_of_nonneg_left (abs_rateLinear_le G m hδ hV hp _ a k) hε0
      _ = (ε * CL) * ‖A - B‖ := by ring
      _ ≤ (1 / 2) * ‖A - B‖ := mul_le_mul_of_nonneg_right hεL (norm_nonneg _)
      _ = _ := by simp
  have hcon : ContractingWith (1 / 2 : NNReal) T :=
    ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul hTd⟩
  set A := ContractingWith.fixedPoint T hcon
  have hA : T A = A := hcon.fixedPoint_isFixedPt
  have hEL (a : Fin N) (k : Fin 3) :
      eihForce G m c p.1 p.2 a k = eihMomentumRate G m c p.1 p.2 A a k := by
    have h := congrFun (congrFun hA a) k
    simp only [hT] at h
    rw [eihForce_eq, eihMomentumRate_eq, ← hε]
    linear_combination h
  -- the quadratic motion
  set X : ℝ → Fin N → S := fun s => p.1 + (s - t) • p.2 + ((s - t) ^ 2 / 2) • A with hXd
  have hX' (s : ℝ) : HasDerivAt X (p.2 + (s - t) • A) s := by
    have h1 : HasDerivAt (fun s : ℝ => (s - t) ^ 2 / 2) (s - t) s := by
      have h := (((hasDerivAt_id' s).sub_const t).pow 2).div_const 2
      convert h using 1
      ring
    have h2 : HasDerivAt (fun s : ℝ => s - t) 1 s := (hasDerivAt_id' s).sub_const t
    have h := ((h2.smul_const p.2).const_add p.1).fun_add (h1.smul_const A)
    exact h.congr_deriv (by simp)
  have hdX : deriv X = fun s => p.2 + (s - t) • A := funext fun s => (hX' s).deriv
  have hddX : deriv (deriv X) t = A := by
    rw [hdX]
    have h := ((hasDerivAt_id' t).sub_const t).smul_const A |>.const_add p.2
    simpa using h.deriv
  have hXt : X t = p.1 := by simp [hXd]
  have hvt : deriv X t = p.2 := by simp [hdX]
  have hXs : ContDiff ℝ ∞ X := by
    simp only [hXd]
    fun_prop
  refine ⟨X, hXs, hXt, hvt, clm_eq_zero_of_basis _ fun a k => ?_⟩
  have hsep : ∀ b d, b ≠ d → X t b ≠ X t d := fun b d hbd heq => by
    have h := hp.1 b d hbd
    rw [← hXt, heq, sub_self, euclidNorm, Finset.sum_eq_zero (fun j _ => by simp),
      Real.sqrt_zero] at h
    linarith
  rw [eulerLagrange_eihLagrangian G m c (hXs.of_le (by simp)) hsep a k, hXt, hvt, hddX,
    hEL a k, sub_self, mul_zero]

/-- **An instance of two bodies (targets (i)–(v))**: two unit masses at `±e₀` with given
velocities bounded by `V₀`; for `c ≥ c₁` a motion through this configuration satisfies the
Euler–Lagrange equations of (106.17) at `t`. -/
theorem exists_eulerLagrange_two (G : ℝ) {V₀ : ℝ} (hV : 0 ≤ V₀) (v₁ v₂ : S) (hv₁ : ‖v₁‖ ≤ V₀)
    (hv₂ : ‖v₂‖ ≤ V₀) :
    ∃ c₁, 1 ≤ c₁ ∧ ∀ c, c₁ ≤ c → ∀ t : ℝ, ∃ X : ℝ → Fin 2 → S, ContDiff ℝ ∞ X ∧
      X t = ![![1, 0, 0], ![-1, 0, 0]] ∧ deriv X t = ![v₁, v₂] ∧
      Mechanics.eulerLagrange (eihLagrangian G ![1, 1] c) X t = 0 := by
  obtain ⟨c₁, hc₁, h⟩ := exists_eulerLagrange (N := 2) G ![1, 1] (δ := 2) (V₀ := V₀)
    (by norm_num) hV
  refine ⟨c₁, hc₁, fun c hc t => h c hc (![![1, 0, 0], ![-1, 0, 0]], ![v₁, v₂]) ?_ t⟩
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · simp only [euclidNorm]
      refine (Real.le_sqrt (by norm_num) (Finset.sum_nonneg fun j _ => sq_nonneg _)).mpr ?_
      simp [Fin.sum_univ_three]
      norm_num
    · simp only [euclidNorm]
      refine (Real.le_sqrt (by norm_num) (Finset.sum_nonneg fun j _ => sq_nonneg _)).mpr ?_
      simp [Fin.sum_univ_three]
      norm_num
    · exact absurd rfl hab
  · fin_cases a
    · simpa using hv₁
    · simpa using hv₂

/-! ### A post-Newtonian family with the potentials of a body at rest -/

/-- A compact buffer inside the open set where a function is `C²` gives an actual bound. -/
theorem exists_coordinateC2Bound_of_contDiffOn {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : NewtonianCoordinates → F} {W K U : Set NewtonianCoordinates}
    (hW : IsOpen W) (hf : ContDiffOn ℝ 2 f W) (hK : IsCompact K) (hKW : K ⊆ W) (hUK : U ⊆ K) :
    ∃ C ≥ (0 : ℝ), CoordinateC2Bound U C f := by
  have h0 : ContinuousOn f K := hf.continuousOn.mono hKW
  have h1 : ContinuousOn (fderiv ℝ f) K :=
    (hf.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hKW
  have hd : ContDiffOn ℝ 1 (fderiv ℝ f) W := hf.fderiv_of_isOpen hW (by norm_num)
  have h2 := (hd.continuousOn_fderiv_of_isOpen hW le_rfl).mono hKW
  obtain ⟨C₀, h₀, hb₀⟩ := (hK.image_of_continuousOn h0).isBounded.exists_pos_norm_le
  obtain ⟨C₁, h₁, hb₁⟩ := (hK.image_of_continuousOn h1).isBounded.exists_pos_norm_le
  obtain ⟨C₂, h₂, hb₂⟩ := (hK.image_of_continuousOn h2).isBounded.exists_pos_norm_le
  refine ⟨C₀ + C₁ + C₂, by positivity, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · exact (hb₀ _ ⟨q, hUK hq, rfl⟩).trans (by linarith)
  · exact (hb₁ _ ⟨q, hUK hq, rfl⟩).trans (by linarith)
  · exact (hb₂ _ ⟨q, hUK hq, rfl⟩).trans (by linarith)

theorem coordinateC2Bound_zero {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set NewtonianCoordinates} {K : ℝ} (hK : 0 ≤ K) :
    CoordinateC2Bound U K (fun _ => (0 : F)) :=
  ⟨fun _ _ => by rw [norm_zero]; exact hK, fun _ _ => by simp [hK], fun q _ => by
    have h : fderiv ℝ (fderiv ℝ fun _ : NewtonianCoordinates => (0 : F)) q = 0 := by simp
    rw [h]
    exact le_of_eq_of_le ContinuousLinearMap.opNorm_zero hK⟩

/-- The point `(t, x) = (0, (1, 0, 0))`. -/
def restPoint : NewtonianCoordinates := Fin.cons 0 ![1, 0, 0]

/-- **An instance for the test-mass limit**: for a body of the mass `M` at rest at the origin and
a massless second body (`m = (M, 0)`, any positions of the second body), there is a
post-Newtonian family on a neighbourhood of `(0, (1, 0, 0))` whose potentials are those of the
other bodies of the body `1` (`Φ = −GM/‖x‖₂`, `ψ = 0`, `B = 0`), so the hypotheses of
`testMass_acceleration_error` are satisfiable. -/
theorem exists_family_rest (G M : ℝ) :
    ∃ (U : TopologicalSpace.Opens NewtonianCoordinates)
      (f : PostNewtonian.PostNewtonianMetricFamily U), restPoint ∈ U ∧
      (∀ q, f.potential q = othersPotential G (Function.update ![M, 0] 1 0)
        ((fun _ => 0 : ℝ → Fin 2 → S) (q 0)) 1 (Fin.tail q)) ∧
      (∀ q, f.scalarPotential q = othersScalarPotential G (Function.update ![M, 0] 1 0)
        ((fun _ => 0 : ℝ → Fin 2 → S) (q 0)) (deriv (fun _ => 0 : ℝ → Fin 2 → S) (q 0)) 1
          (Fin.tail q)) ∧
      (∀ q, f.vectorPotential q = othersVectorPotential G (Function.update ![M, 0] 1 0)
        ((fun _ => 0 : ℝ → Fin 2 → S) (q 0)) (deriv (fun _ => 0 : ℝ → Fin 2 → S) (q 0)) 1
          (Fin.tail q)) := by
  set Φ : NewtonianCoordinates → ℝ := fun q => -G * (M * invDist (Fin.tail q)) with hΦd
  set W : Set NewtonianCoordinates := {q | Fin.tail q ≠ 0} with hW
  have hWo : IsOpen W := isOpen_ne_fun (by fun_prop) continuous_const
  set Kc := Metric.closedBall restPoint (1 / 2)
  have hKW : Kc ⊆ W := by
    intro q hq h0
    have h1 : |q 1 - restPoint 1| ≤ 1 / 2 := by
      have := (norm_le_pi_norm (q - restPoint) 1).trans (mem_closedBall_iff_norm.mp hq)
      simpa [Real.norm_eq_abs] using this
    have hq1 : q 1 = 0 := by simpa [Fin.tail] using congrFun h0 0
    simp [restPoint, hq1] at h1
    norm_num at h1
  have hK : IsCompact Kc := isCompact_closedBall _ _
  set U : TopologicalSpace.Opens NewtonianCoordinates :=
    ⟨Metric.ball restPoint (1 / 2), Metric.isOpen_ball⟩
  have hUK : (U : Set NewtonianCoordinates) ⊆ Kc := Metric.ball_subset_closedBall
  have hUW : (U : Set NewtonianCoordinates) ⊆ W := hUK.trans hKW
  have htail : ContDiff ℝ ∞ (fun q : NewtonianCoordinates => Fin.tail q) := by
    refine contDiff_pi.mpr fun j => ?_
    simp only [Fin.tail]
    fun_prop
  have hΦs : ContDiffOn ℝ ∞ Φ W := fun q hq =>
    (contDiffAt_const.mul (contDiffAt_const.mul (ContDiffAt.comp (g := invDist)
      (f := fun q : NewtonianCoordinates => Fin.tail q) q (contDiffAt_invDist hq)
      htail.contDiffAt))).contDiffWithinAt
  have hT : ContDiffOn ℝ ∞ (fun q => -2 * Φ q ^ 2) W := contDiffOn_const.mul (hΦs.pow 2)
  have hS : ContDiffOn ℝ ∞ (fun q : NewtonianCoordinates =>
      (fun i j : Fin 3 => -2 * Φ q * (if i = j then 1 else 0) : NewtonianSpatialMatrix)) W :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j =>
      (contDiffOn_const.mul hΦs).mul contDiffOn_const
  have h2 {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : NewtonianCoordinates → F}
      (hg : ContDiffOn ℝ ∞ g W) : ContDiffOn ℝ 2 g W := hg.of_le (by simp)
  obtain ⟨K1, hK1, hb1⟩ := exists_coordinateC2Bound_of_contDiffOn hWo (h2 hΦs) hK hKW hUK
  obtain ⟨K2, hK2, hb2⟩ := exists_coordinateC2Bound_of_contDiffOn hWo (h2 hT) hK hKW hUK
  obtain ⟨K3, hK3, hb3⟩ := exists_coordinateC2Bound_of_contDiffOn hWo (h2 hS) hK hKW hUK
  set Kb := K1 + K2 + K3
  have hKb : 0 ≤ Kb := by positivity
  have hmono {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : NewtonianCoordinates → F}
      {L : ℝ} (hg : CoordinateC2Bound U L g) (hL : L ≤ Kb) : CoordinateC2Bound U Kb g :=
    hg.mono (Subset.refl _) hL
  refine ⟨U, {
    potential := Φ
    timeCorrection := fun _ q => -2 * Φ q ^ 2
    mixedCorrection := fun _ _ => 0
    spatialCorrection := fun _ q i j => -2 * Φ q * (if i = j then 1 else 0)
    potential_smooth := hΦs.mono hUW
    time_smooth := fun _ _ => hT.mono hUW
    mixed_smooth := fun _ _ => contDiffOn_const
    spatial_smooth := fun _ _ => hS.mono hUW
    spatial_symmetric := fun _ _ _ _ i j => by simp [eq_comm]
    bound := Kb
    bound_nonneg := hKb
    potential_bound := hmono hb1 (by linarith)
    time_bound := fun _ _ => hmono hb2 (by linarith)
    mixed_bound := fun _ _ => coordinateC2Bound_zero hKb
    spatial_bound := fun _ _ => hmono hb3 (by linarith)
    scalarPotential := fun _ => 0
    vectorPotential := fun _ => 0
    timeRemainder := fun _ _ => 0
    mixedRemainder := fun _ _ => 0
    spatialRemainder := fun _ _ => 0
    time_eq := fun c q => by simp
    mixed_eq := fun c q i => by simp
    spatial_eq := fun c q i j => by simp
    scalar_smooth := contDiffOn_const
    vector_smooth := contDiffOn_const
    timeRemainder_smooth := fun _ _ => contDiffOn_const
    mixedRemainder_smooth := fun _ _ => contDiffOn_const
    spatialRemainder_smooth := fun _ _ => contDiffOn_const
    scalar_bound := coordinateC2Bound_zero hKb
    vector_bound := coordinateC2Bound_zero hKb
    timeRemainder_bound := fun _ _ => coordinateC2Bound_zero hKb
    mixedRemainder_bound := fun _ _ => coordinateC2Bound_zero hKb
    spatialRemainder_bound := fun _ _ => coordinateC2Bound_zero hKb }, ?_, ?_, ?_, ?_⟩
  · show restPoint ∈ Metric.ball restPoint (1 / 2)
    exact Metric.mem_ball_self (by norm_num)
  · have hc : ({1}ᶜ : Finset (Fin 2)) = {0} := by decide
    intro q
    simp [othersPotential, hΦd, hc]
  · have hc : ({1}ᶜ : Finset (Fin 2)) = {0} := by decide
    intro q
    simp [othersScalarPotential, potentialAt, hc]
  · intro q
    funext k
    simp [othersVectorPotential, kernelB_zero_right]

end ProjectAinos.GeneralRelativity.EinsteinInfeldHoffmann











