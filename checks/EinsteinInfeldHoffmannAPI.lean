/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.PostNewtonianField
import ProjectAinos.GeneralRelativity.PostNewtonianRicci
import ProjectAinos.GeneralRelativity.PostNewtonianSources

/-! Public consumers of the Lagrangian of Einstein, Infeld and Hoffmann (Landau–Lifshitz §106,
(106.17)): the kernels of a point mass, the potentials of the other bodies in the gauge of GR36,
the restriction of (106.17) to one body and its term-by-term match with the test-body Lagrangian,
the explicit Euler–Lagrange equations and the acceleration to `O(c⁻⁴)`, the permutation
invariance, the Newtonian and test-mass limits, and the instances; and of the field side: the
potentials of smooth sources as Newton potentials with their Poisson equations, and the vacuum
equations and the gauge condition of the potentials of point masses. Default elaborator options
are intentional: these checks must not rely on the implementation's transparency settings. Every
statement is pinned with its type. -/

noncomputable section

section EinsteinInfeldHoffmann

open ContinuousLinearMap Set Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.EinsteinInfeldHoffmann

open NewtonianMetricFamily

local notation "S" => NewtonianSpace

variable {N : ℕ}

example (v w : S) : ℝ :=
  dot v w

example (z : S) : ℝ :=
  euclidNorm z

example (z : S) : ℝ :=
  invDist z

example (z : S) : S →L[ℝ] ℝ :=
  dotL z

example (z h : S) : dotL z h = dot z h :=
  dotL_apply z h

example (v w : S) : dot v w = dot w v :=
  dot_comm v w

example (v w : S) : dot v (-w) = -dot v w :=
  dot_neg_right v w

example (u v w : S) : dot u (v - w) = dot u v - dot u w :=
  dot_sub_right u v w

example (u v w : S) : dot (u + v) w = dot u w + dot v w :=
  dot_add_left u v w

example (w : S) : dot 0 w = 0 :=
  dot_zero_left w

example (w : S) : dot w 0 = 0 :=
  dot_zero_right w

example (r : ℝ) (v w : S) : dot (r • v) w = r * dot v w :=
  dot_smul_left r v w

example (r : ℝ) (v w : S) : dot v (r • w) = r * dot v w :=
  dot_smul_right r v w

example (z : S) : ∑ j, (-z) j ^ 2 = ∑ j, z j ^ 2 :=
  sum_sq_neg z

example (z : S) : euclidNorm (-z) = euclidNorm z :=
  euclidNorm_neg z

example (z : S) : invDist (-z) = invDist z :=
  invDist_neg z

example (x y : S) : invDist (x - y) = invDist (y - x) :=
  invDist_sub_comm x y

example : invDist 0 = 0 :=
  invDist_zero

example {z : S} (hz : z ≠ 0) : 0 < ∑ j, z j ^ 2 :=
  sum_sq_pos hz

example {z : S} (hz : z ≠ 0) : 0 < euclidNorm z :=
  euclidNorm_pos hz

example (z : S) : 0 ≤ euclidNorm z :=
  euclidNorm_nonneg z

example (z : S) : 0 ≤ invDist z :=
  invDist_nonneg z

example {z : S} (hz : z ≠ 0) : 0 < invDist z :=
  invDist_pos hz

example (z : S) : euclidNorm z ^ 2 = ∑ j, z j ^ 2 :=
  euclidNorm_sq z

example {z : S} (hz : z ≠ 0) : invDist z ^ 2 * ∑ j, z j ^ 2 = 1 :=
  invDist_sq_mul hz

example (z : S) (k : Fin 3) : |z k| ≤ euclidNorm z :=
  abs_component_le_euclidNorm z k

example (z : S) (k : Fin 3) : |invDist z * z k| ≤ 1 :=
  abs_invDist_mul_le z k

example {z : S} {δ : ℝ} (hδ : 0 < δ) (h : δ ≤ euclidNorm z) : invDist z ≤ δ⁻¹ :=
  invDist_le hδ h

example (z : S) :
    HasFDerivAt (fun y : S => ∑ j, y j ^ 2) ((2 : ℝ) • dotL z) z :=
  hasFDerivAt_sum_sq z

example {z : S} (hz : z ≠ 0) :
    HasFDerivAt invDist (-(invDist z ^ 3) • dotL z) z :=
  hasFDerivAt_invDist hz

example {z : ℝ → S} {z' : S} {s : ℝ} (hz : HasDerivAt z z' s)
    (h0 : z s ≠ 0) :
    HasDerivAt (fun r => invDist (z r)) (-(invDist (z s) ^ 3) * dot (z s) z') s :=
  hasDerivAt_invDist_comp hz h0

example (z u : S) : S :=
  kernelB z u

example (z u h : S) : S :=
  dKernelB z u h

example {u w : ℝ → S} {u' w' : S} {s : ℝ} (hu : HasDerivAt u u' s)
    (hw : HasDerivAt w w' s) :
    HasDerivAt (fun r => dot (u r) (w r)) (dot u' (w s) + dot (u s) w') s :=
  hasDerivAt_dot_comp hu hw

example {z u : ℝ → S} {z' u' : S} {s : ℝ} (hz : HasDerivAt z z' s)
    (hu : HasDerivAt u u' s) (h0 : z s ≠ 0) (k : Fin 3) :
    HasDerivAt (fun r => kernelB (z r) (u r) k)
      (dKernelB (z s) (u s) z' k + kernelB (z s) u' k) s :=
  hasDerivAt_kernelB_comp hz hu h0 k

example (u : S) : kernelB 0 u = 0 :=
  kernelB_zero_left u

example (z : S) : kernelB z 0 = 0 :=
  kernelB_zero_right z

example (u h : S) : dKernelB 0 u h = 0 :=
  dKernelB_zero_left u h

example (z u w : S) :
    ∑ k, kernelB z u k * w k = 7 * dot u w * invDist z + dot u z * dot w z * invDist z ^ 3 :=
  sum_kernelB_mul z u w

example (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (b : Fin N) : ℝ :=
  potentialAt G m X b

example (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N) (x : S) : ℝ :=
  othersPotential G m X a x

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) (x : S) : ℝ :=
  othersScalarPotential G m X V a x

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) (x : S) : S :=
  othersVectorPotential G m X V a x

example (m c : ℝ) (Φ ψ : S → ℝ) (B : S → S) (z : S × S) : ℝ :=
  testLagrangian m c Φ ψ B z

example {U : TopologicalSpace.Opens NewtonianCoordinates}
    (f : PostNewtonian.PostNewtonianMetricFamily U) (m c t : ℝ) :
    f.lagrangian m c t = testLagrangian m c (fun x => f.potential (Fin.cons t x))
      (fun x => f.scalarPotential (Fin.cons t x)) (fun x => f.vectorPotential (Fin.cons t x)) :=
  lagrangian_eq_testLagrangian f m c t

example (u w z : S) : ℝ :=
  pairVelocity u w z

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ) : Mechanics.Lagrangian (Fin N → S) :=
  eihLagrangian G m c

example (m : Fin N → ℝ) (X : Fin N → S) :
    ∑ a, ∑ b, ∑ d, m a * m b * m d * invDist (X a - X b) * invDist (X a - X d) =
      ∑ a, m a * (∑ b, m b * invDist (X a - X b)) ^ 2 :=
  sum_three_eq m X

example (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a b : Fin N) :
    potentialAt G m X b = G * (m a * invDist (X b - X a) +
      ∑ c ∈ ({a}ᶜ : Finset (Fin N)), m c * invDist (X b - X c)) :=
  potentialAt_split G m X a b

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V : Fin N → S) (a : Fin N) : ℝ :=
  eihRest G m c X V a

example (u w z : S) : pairVelocity u w (-z) = pairVelocity u w z :=
  pairVelocity_neg u w z

example (G : ℝ) (m : Fin N → ℝ) (c s : ℝ) (X V : Fin N → S) (a : Fin N)
    (x v : S) :
    eihLagrangian G m c s (Function.update X a x, Function.update V a v) =
      testLagrangian (m a) c (othersPotential G m X a) (othersScalarPotential G m X V a)
          (othersVectorPotential G m X V a) (x, v) -
        epsilon c * (G ^ 2 * m a ^ 2 / 2) *
          ∑ d ∈ ({a}ᶜ : Finset (Fin N)), m d * (invDist (X d - x) - invDist (X d - X a)) ^ 2 +
        eihRest G m c X V a :=
  eihLagrangian_update G m c s X V a x v

example (G : ℝ) (m : Fin N → ℝ) (c s : ℝ) (X V : Fin N → S)
    (a : Fin N) (x v : S) :
    eihLagrangian G m c s (Function.update X a x, Function.update V a v) -
        testLagrangian (m a) c (othersPotential G m X a) (othersScalarPotential G m X V a)
          (othersVectorPotential G m X V a) (x, v) +
        epsilon c * (G ^ 2 * m a ^ 2 / 2) *
          ∑ d ∈ ({a}ᶜ : Finset (Fin N)), m d * (invDist (X d - x) - invDist (X d - X a)) ^ 2 =
      eihLagrangian G m c s (X, V) -
        testLagrangian (m a) c (othersPotential G m X a) (othersScalarPotential G m X V a)
          (othersVectorPotential G m X V a) (X a, V a) :=
  eihLagrangian_update_sub G m c s X V a x v

example {z : S} (hz : z ≠ 0) {n : WithTop ℕ∞} : ContDiffAt ℝ n invDist z :=
  contDiffAt_invDist hz

example {z : S} (hz : z ≠ 0) : DifferentiableAt ℝ invDist z :=
  differentiableAt_invDist hz

example {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (p : Z → Fin N → S) (hp : ContDiff ℝ ∞ p) {z : Z} (a b : Fin N)
    (hab : a ≠ b → p z a ≠ p z b) :
    ContDiffAt ℝ ∞ (fun y => invDist (p y a - p y b)) z :=
  contDiffAt_invDist_pair p hp a b hab

example (G : ℝ) (m : Fin N → ℝ) (c s : ℝ)
    {z : (Fin N → S) × (Fin N → S)} (hz : ∀ a b, a ≠ b → z.1 a ≠ z.1 b) :
    ContDiffAt ℝ ∞ (eihLagrangian G m c s) z :=
  contDiffAt_eihLagrangian G m c s hz

example (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N)
    {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) : DifferentiableAt ℝ (othersPotential G m X a) x :=
  differentiableAt_othersPotential G m X a hx

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S)
    (a : Fin N) {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) :
    DifferentiableAt ℝ (othersScalarPotential G m X V a) x :=
  differentiableAt_othersScalarPotential G m X V a hx

example {x y : S} (h : x ≠ y) (u : S) (k : Fin 3) :
    DifferentiableAt ℝ (fun x => kernelB (x - y) u k) x :=
  differentiableAt_kernelB_sub h u k

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S)
    (a : Fin N) {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) :
    DifferentiableAt ℝ (othersVectorPotential G m X V a) x :=
  differentiableAt_othersVectorPotential G m X V a hx

example {m c : ℝ} {Φ ψ : S → ℝ} {B : S → S} {x : S} (v : S)
    (hΦ : DifferentiableAt ℝ Φ x) (hψ : DifferentiableAt ℝ ψ x) (hB : DifferentiableAt ℝ B x) :
    DifferentiableAt ℝ (testLagrangian m c Φ ψ B) (x, v) :=
  differentiableAt_testLagrangian v hΦ hψ hB

example (G : ℝ) (m : Fin N → ℝ) (c s : ℝ) (X V : Fin N → S)
    (a : Fin N) (hX : ∀ b, b ≠ a → X a ≠ X b) :
    HasFDerivAt (fun z : S × S => eihLagrangian G m c s
        (Function.update X a z.1, Function.update V a z.2))
      (fderiv ℝ (testLagrangian (m a) c (othersPotential G m X a)
        (othersScalarPotential G m X V a) (othersVectorPotential G m X V a)) (X a, V a))
      (X a, V a) :=
  hasFDerivAt_eihLagrangian_update G m c s X V a hX

example {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {L₁ L₂ : Mechanics.Lagrangian Q} {x : ℝ → Q} {t : ℝ}
    (h : ∀ᶠ s in 𝓝 t, fderiv ℝ (L₁ s) (x s, deriv x s) = fderiv ℝ (L₂ s) (x s, deriv x s)) :
    Mechanics.eulerLagrange L₁ x t = Mechanics.eulerLagrange L₂ x t :=
  eulerLagrange_congr_fderiv h

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ)
    {X : ℝ → Fin N → S} (hX : ContDiff ℝ 2 X) {t : ℝ}
    (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N) (w : S) :
    Mechanics.eulerLagrange (eihLagrangian G m c) X t (Pi.single a w) =
      Mechanics.eulerLagrange (fun s => testLagrangian (m a) c (othersPotential G m (X s) a)
          (othersScalarPotential G m (X s) (deriv X s) a)
          (othersVectorPotential G m (X s) (deriv X s) a))
        (fun s => X s a) t w :=
  eulerLagrange_eihLagrangian_eq_test G m c hX hsep a w

example (c : ℝ) (Φ ψ : S → ℝ) (B : S → S) (x v h : S) : ℝ :=
  testForce c Φ ψ B x v h

example (c Φ₀ : ℝ) (B₀ v : S) (k : Fin 3) : ℝ :=
  testMomentum c Φ₀ B₀ v k

example (c Φ₀ Φd : ℝ) (Bd v a : S) (k : Fin 3) : ℝ :=
  testMomentumRate c Φ₀ Φd Bd v a k

example {m c : ℝ} {Φ ψ : S → ℝ} {B : S → S} {x : S} (v : S)
    (hΦ : DifferentiableAt ℝ Φ x) (hψ : DifferentiableAt ℝ ψ x) (hB : DifferentiableAt ℝ B x)
    (w : S × S) :
    fderiv ℝ (testLagrangian m c Φ ψ B) (x, v) w =
      m * (testForce c Φ ψ B x v w.1 + ∑ k, testMomentum c (Φ x) (B x) v k * w.2 k) :=
  fderiv_testLagrangian v hΦ hψ hB w

example {m c : ℝ} {Φ ψ : ℝ → S → ℝ} {B : ℝ → S → S} {x : ℝ → S} {s : ℝ}
    (hΦ : DifferentiableAt ℝ (Φ s) (x s)) (hψ : DifferentiableAt ℝ (ψ s) (x s))
    (hB : DifferentiableAt ℝ (B s) (x s)) :
    Mechanics.momentum (fun r => testLagrangian m c (Φ r) (ψ r) (B r)) x s =
      ∑ k, (m * testMomentum c (Φ s (x s)) (B s (x s)) (deriv x s) k) • (proj k : S →L[ℝ] ℝ) :=
  momentum_testFamily hΦ hψ hB

example {m c : ℝ} {Φ ψ : ℝ → S → ℝ} {B : ℝ → S → S} {x : ℝ → S}
    (hx : ContDiff ℝ 2 x) {t : ℝ}
    (hd : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (Φ s) (x s) ∧ DifferentiableAt ℝ (ψ s) (x s) ∧
      DifferentiableAt ℝ (B s) (x s))
    {Φd : ℝ} {Bd : S} (hΦd : HasDerivAt (fun s => Φ s (x s)) Φd t)
    (hBd : ∀ k, HasDerivAt (fun s => B s (x s) k) (Bd k) t) (k : Fin 3) :
    Mechanics.eulerLagrange (fun s => testLagrangian m c (Φ s) (ψ s) (B s)) x t (Pi.single k 1) =
      m * (testForce c (Φ t) (ψ t) (B t) (x t) (deriv x t) (Pi.single k 1) -
        testMomentumRate c (Φ t (x t)) Φd Bd (deriv x t) (deriv (deriv x) t) k) :=
  eulerLagrange_testFamily hx hd hΦd hBd k

example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : S → F} {x h : S} {D : F} (hf : DifferentiableAt ℝ f x)
    (hD : HasDerivAt (fun r : ℝ => f (x + r • h)) D 0) : fderiv ℝ f x h = D :=
  fderiv_apply_of_hasDerivAt_line hf hD

example (x h y : S) :
    HasDerivAt (fun r : ℝ => x + r • h - y) h 0 :=
  hasDerivAt_line_sub x h y

example (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N)
    {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) (h : S) :
    fderiv ℝ (othersPotential G m X a) x h =
      G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * invDist (x - X b) ^ 3 * dot (x - X b) h :=
  fderiv_othersPotential_apply G m X a hx h

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N)
    {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) (h : S) :
    fderiv ℝ (othersScalarPotential G m X V a) x h =
      G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * (3 / 2 * ∑ j, V b j ^ 2 - potentialAt G m X b) *
        invDist (x - X b) ^ 3 * dot (x - X b) h :=
  fderiv_othersScalarPotential_apply G m X V a hx h

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S)
    (a : Fin N) {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) (h : S) (k : Fin 3) :
    fderiv ℝ (othersVectorPotential G m X V a) x h k =
      -(G / 2) * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * dKernelB (x - X b) (V b) h k :=
  fderiv_othersVectorPotential_apply G m X V a hx h k

example (G : ℝ) (m : Fin N → ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (a : Fin N) (hsep : ∀ b, b ≠ a → X t a ≠ X t b) :
    HasDerivAt (fun s => othersPotential G m (X s) a (X s a))
      (G * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * invDist (X t a - X t b) ^ 3 *
        dot (X t a - X t b) (deriv X t a - deriv X t b)) t :=
  hasDerivAt_othersPotential_path G m hX a hsep

example (G : ℝ) (m : Fin N → ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (a : Fin N) (hsep : ∀ b, b ≠ a → X t a ≠ X t b) (k : Fin 3) :
    HasDerivAt (fun s => othersVectorPotential G m (X s) (deriv X s) a (X s a) k)
      (-(G / 2) * ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b *
        (dKernelB (X t a - X t b) (deriv X t b) (deriv X t a - deriv X t b) k +
          kernelB (X t a - X t b) (deriv (deriv X) t b) k)) t :=
  hasDerivAt_othersVectorPotential_path G m hX a hsep k

example (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N) : S :=
  newtonAcceleration G m X a

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) : S :=
  scalarGradient G m X V a

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) : S :=
  vectorGradient G m X V a

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) : ℝ :=
  potentialRate G m X V a

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) : S :=
  vectorPotentialAt G m X V a

example (G : ℝ) (m : Fin N → ℝ) (X V A : Fin N → S) (a : Fin N) : S :=
  vectorPotentialRate G m X V A a

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V : Fin N → S) (a : Fin N) : S :=
  eihForce G m c X V a

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V A : Fin N → S) (a : Fin N) : S :=
  eihMomentumRate G m c X V A a

example (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N) :
    othersPotential G m X a (X a) = -potentialAt G m X a :=
  othersPotential_self G m X a

example (z : S) (k : Fin 3) : dot z (Pi.single k 1) = z k :=
  dot_single z k

example (μ G : ℝ) (m : Fin N → ℝ) (c : ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N)
    (k : Fin 3) :
    Mechanics.eulerLagrange (fun s => testLagrangian μ c (othersPotential G m (X s) a)
          (othersScalarPotential G m (X s) (deriv X s) a)
          (othersVectorPotential G m (X s) (deriv X s) a))
        (fun s => X s a) t (Pi.single k 1) =
      μ * (eihForce G m c (X t) (deriv X t) a k -
        eihMomentumRate G m c (X t) (deriv X t) (deriv (deriv X) t) a k) :=
  eulerLagrange_testFamily_others μ G m c hX hsep a k

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N)
    (k : Fin 3) :
    Mechanics.eulerLagrange (eihLagrangian G m c) X t (Pi.single a (Pi.single k 1)) =
      m a * (eihForce G m c (X t) (deriv X t) a k -
        eihMomentumRate G m c (X t) (deriv X t) (deriv (deriv X) t) a k) :=
  eulerLagrange_eihLagrangian G m c hX hsep a k

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) : S :=
  forceCorrection G m X V a

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) : S :=
  rateZero G m X V a

example (G : ℝ) (m : Fin N → ℝ) (X V D : Fin N → S) (a : Fin N) : S :=
  rateLinear G m X V D a

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V : Fin N → S) : Fin N → S :=
  eihAcceleration G m c X V

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V : Fin N → S) (a : Fin N) (k : Fin 3) :
    eihForce G m c X V a k =
      newtonAcceleration G m X a k + epsilon c * forceCorrection G m X V a k :=
  eihForce_eq G m c X V a k

example (z u w : S) (k : Fin 3) :
    kernelB z (u + w) k = kernelB z u k + kernelB z w k :=
  kernelB_add_right z u w k

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V A : Fin N → S) (a : Fin N)
    (k : Fin 3) :
    eihMomentumRate G m c X V A a k =
      A a k + epsilon c * (rateZero G m X V a k + rateLinear G m X V A a k) :=
  eihMomentumRate_eq G m c X V A a k

example (z u w : S) (k : Fin 3) :
    kernelB z (u - w) k = kernelB z u k - kernelB z w k :=
  kernelB_sub_right z u w k

example (G : ℝ) (m : Fin N → ℝ) (X V D D' : Fin N → S) (a : Fin N) (k : Fin 3) :
    rateLinear G m X V D a k - rateLinear G m X V D' a k = rateLinear G m X V (D - D') a k :=
  rateLinear_sub G m X V D D' a k

example (z u h : S) (k : Fin 3) :
    dKernelB z u h k = invDist z ^ 2 * (-7 * u k * ∑ j, invDist z * z j * h j +
      (∑ j, u j * h j) * (invDist z * z k) + (∑ j, u j * (invDist z * z j)) * h k -
      3 * (∑ j, u j * (invDist z * z j)) * (invDist z * z k) *
        ∑ j, invDist z * z j * h j) :=
  dKernelB_eq z u h k

example (z u : S) (k : Fin 3) :
    kernelB z u k = invDist z * (7 * u k + (∑ j, u j * (invDist z * z j)) * (invDist z * z k)) :=
  kernelB_eq z u k

example (z w : S) (k : Fin 3) : |kernelB z w k| ≤ 10 * invDist z * ‖w‖ :=
  abs_kernelB_le z w k

example (N : ℕ) (δ V₀ : ℝ) : Set ((Fin N → S) × (Fin N → S)) :=
  separatedSet N δ V₀

example {δ V₀ : ℝ} (hδ : 0 < δ) {p : (Fin N → S) × (Fin N → S)}
    (hp : p ∈ separatedSet N δ V₀) (a b : Fin N) : invDist (p.1 a - p.1 b) ≤ δ⁻¹ :=
  invDist_le_of_mem hδ hp a b

example (G : ℝ) (m : Fin N → ℝ) {δ V₀ : ℝ} (hδ : 0 < δ)
    {p : (Fin N → S) × (Fin N → S)} (hp : p ∈ separatedSet N δ V₀) (a : Fin N) :
    |potentialAt G m p.1 a| ≤ |G| * δ⁻¹ * ∑ b, |m b| :=
  abs_potentialAt_le G m hδ hp a

example (G : ℝ) (m : Fin N → ℝ) {δ V₀ : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V₀)
    {p : (Fin N → S) × (Fin N → S)} (hp : p ∈ separatedSet N δ V₀) (D : Fin N → S) (a : Fin N)
    (k : Fin 3) :
    |rateLinear G m p.1 p.2 D a k| ≤ (9 / 2 * V₀ ^ 2 + 8 * |G| * δ⁻¹ * ∑ b, |m b|) * ‖D‖ :=
  abs_rateLinear_le G m hδ hV hp D a k

example (G : ℝ) (m : Fin N → ℝ) {δ V₀ : ℝ} (hδ : 0 < δ)
    (hV : 0 ≤ V₀) :
    ∃ C c₁, 0 ≤ C ∧ 1 ≤ c₁ ∧ ∀ c, c₁ ≤ c → ∀ p ∈ separatedSet N δ V₀, ∀ A : Fin N → S,
      (∀ a k, eihForce G m c p.1 p.2 a k = eihMomentumRate G m c p.1 p.2 A a k) →
      ‖A - eihAcceleration G m c p.1 p.2‖ ≤ C / c ^ 4 :=
  norm_sub_eihAcceleration_le G m hδ hV

example (G : ℝ) (m : Fin N → ℝ) (hm : ∀ a, m a ≠ 0)
    {δ V₀ : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V₀) :
    ∃ C c₁, 0 ≤ C ∧ 1 ≤ c₁ ∧ ∀ c, c₁ ≤ c → ∀ X : ℝ → Fin N → S, ContDiff ℝ 2 X → ∀ t,
      (∀ a b, a ≠ b → δ ≤ euclidNorm (X t a - X t b)) → (∀ a, ‖deriv X t a‖ ≤ V₀) →
      Mechanics.eulerLagrange (eihLagrangian G m c) X t = 0 →
      ‖deriv (deriv X) t - eihAcceleration G m c (X t) (deriv X t)‖ ≤ C / c ^ 4 :=
  eulerLagrange_acceleration_error G m hm hδ hV

example (σ : Equiv.Perm (Fin N)) (G : ℝ) (m : Fin N → ℝ) (c s : ℝ)
    (z : (Fin N → S) × (Fin N → S)) :
    eihLagrangian G (m ∘ σ) c s (z.1 ∘ σ, z.2 ∘ σ) = eihLagrangian G m c s z :=
  eihLagrangian_perm σ G m c s z

example (σ : Equiv.Perm (Fin N)) (G : ℝ) (m : Fin N → ℝ)
    (X : Fin N → S) (a : Fin N) :
    newtonAcceleration G (m ∘ σ) (X ∘ σ) a = newtonAcceleration G m X (σ a) :=
  newtonAcceleration_perm σ G m X a

example (G : ℝ) (m : Fin N → ℝ) : Mechanics.Lagrangian (Fin N → S) :=
  newtonLagrangian G m

example (G : ℝ) (m : Fin N → ℝ) : Mechanics.Lagrangian (Fin N → S) :=
  eihCorrectionLagrangian G m

example (G : ℝ) (m : Fin N → ℝ) (c s : ℝ) (z : (Fin N → S) × (Fin N → S)) :
    eihLagrangian G m c s z =
      newtonLagrangian G m s z + epsilon c * eihCorrectionLagrangian G m s z :=
  eihLagrangian_eq_add G m c s z

example : Tendsto epsilon atTop (𝓝 0) :=
  tendsto_epsilon

example (G : ℝ) (m : Fin N → ℝ) (s : ℝ) (z : (Fin N → S) × (Fin N → S)) :
    Tendsto (fun c => eihLagrangian G m c s z) atTop (𝓝 (newtonLagrangian G m s z)) :=
  tendsto_eihLagrangian G m s z

example : epsilon 0 = 0 :=
  epsilon_zero

example (G : ℝ) (m : Fin N → ℝ) :
    eihLagrangian G m 0 = newtonLagrangian G m :=
  eihLagrangian_zero G m

example (G : ℝ) (m : Fin N → ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N)
    (k : Fin 3) :
    Mechanics.eulerLagrange (newtonLagrangian G m) X t (Pi.single a (Pi.single k 1)) =
      m a * (newtonAcceleration G m (X t) a k - deriv (deriv X) t a k) :=
  eulerLagrange_newtonLagrangian G m hX hsep a k

example (G : ℝ) (m : Fin N → ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N)
    (k : Fin 3) :
    Tendsto (fun c => Mechanics.eulerLagrange (eihLagrangian G m c) X t
        (Pi.single a (Pi.single k 1))) atTop
      (𝓝 (Mechanics.eulerLagrange (newtonLagrangian G m) X t (Pi.single a (Pi.single k 1)))) :=
  tendsto_eulerLagrange_eihLagrangian G m hX hsep a k

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) :
    Tendsto (fun c => eihAcceleration G m c X V) atTop
      (𝓝 (fun a => newtonAcceleration G m X a)) :=
  tendsto_eihAcceleration G m X V

example (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N) (μ : ℝ) :
    potentialAt G (Function.update m a μ) X a = potentialAt G m X a :=
  potentialAt_update_self G m X a μ

example (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) {a b : Fin N}
    (μ : ℝ) :
    potentialAt G (Function.update m a μ) X b =
      potentialAt G (Function.update m a 0) X b + G * μ * invDist (X b - X a) :=
  potentialAt_update_of_ne G m X μ

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N)
    (μ : ℝ) (x : S) :
    othersScalarPotential G (Function.update m a μ) X V a x =
      othersScalarPotential G (Function.update m a 0) X V a x + μ * G ^ 2 *
        ∑ b ∈ ({a}ᶜ : Finset (Fin N)), m b * invDist (x - X b) * invDist (X b - X a) :=
  othersScalarPotential_update_mass G m X V a μ x

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S) (a : Fin N) (y u : S) :
    othersPotential G (Function.update m a 0) (Function.update X a y) a =
        othersPotential G (Function.update m a 0) X a ∧
      othersScalarPotential G (Function.update m a 0) (Function.update X a y)
          (Function.update V a u) a = othersScalarPotential G (Function.update m a 0) X V a ∧
      othersVectorPotential G (Function.update m a 0) (Function.update X a y)
          (Function.update V a u) a = othersVectorPotential G (Function.update m a 0) X V a :=
  others_update_config G m X V a y u

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V : Fin N → S) (a : Fin N)
    (μ : ℝ) (k : Fin 3) :
    eihForce G (Function.update m a μ) c X V a k =
      eihForce G (Function.update m a 0) c X V a k + epsilon c * (μ * G ^ 2 *
        ∑ b, m b * invDist (X a - X b) ^ 4 * (X a - X b) k) :=
  eihForce_update_mass G m c X V a μ k

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ) (X V A : Fin N → S)
    (a : Fin N) (μ : ℝ) (k : Fin 3) :
    eihMomentumRate G (Function.update m a μ) c X V A a k =
      eihMomentumRate G (Function.update m a 0) c X V A a k :=
  eihMomentumRate_update_mass G m c X V A a μ k

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N) (k : Fin 3)
    {μ : ℝ} (hμ : μ ≠ 0) :
    μ⁻¹ * Mechanics.eulerLagrange (eihLagrangian G (Function.update m a μ) c) X t
        (Pi.single a (Pi.single k 1)) =
      Mechanics.eulerLagrange (fun s => testLagrangian 1 c
          (othersPotential G (Function.update m a 0) (X s) a)
          (othersScalarPotential G (Function.update m a 0) (X s) (deriv X s) a)
          (othersVectorPotential G (Function.update m a 0) (X s) (deriv X s) a))
        (fun s => X s a) t (Pi.single k 1) +
      μ * (epsilon c * G ^ 2 * ∑ b, m b * invDist (X t a - X t b) ^ 4 * (X t a - X t b) k) :=
  eulerLagrange_testMass G m c hX hsep a k hμ

example (G : ℝ) (m : Fin N → ℝ) (c : ℝ) {X : ℝ → Fin N → S}
    (hX : ContDiff ℝ 2 X) {t : ℝ} (hsep : ∀ b d, b ≠ d → X t b ≠ X t d) (a : Fin N)
    (k : Fin 3) :
    Tendsto (fun μ => μ⁻¹ * Mechanics.eulerLagrange (eihLagrangian G (Function.update m a μ) c)
        X t (Pi.single a (Pi.single k 1))) (𝓝[≠] 0)
      (𝓝 (Mechanics.eulerLagrange (fun s => testLagrangian 1 c
          (othersPotential G (Function.update m a 0) (X s) a)
          (othersScalarPotential G (Function.update m a 0) (X s) (deriv X s) a)
          (othersVectorPotential G (Function.update m a 0) (X s) (deriv X s) a))
        (fun s => X s a) t (Pi.single k 1))) :=
  tendsto_eulerLagrange_testMass G m c hX hsep a k

example {U : TopologicalSpace.Opens NewtonianCoordinates}
    (f : PostNewtonian.PostNewtonianMetricFamily U) (μ c : ℝ) (Φ ψ : ℝ → S → ℝ) (B : ℝ → S → S)
    (hΦ : ∀ q, f.potential q = Φ (q 0) (Fin.tail q))
    (hψ : ∀ q, f.scalarPotential q = ψ (q 0) (Fin.tail q))
    (hB : ∀ q, f.vectorPotential q = B (q 0) (Fin.tail q)) :
    (fun s => testLagrangian μ c (Φ s) (ψ s) (B s)) = f.lagrangian μ c :=
  testLagrangian_eq_lagrangian f μ c Φ ψ B hΦ hψ hB

example {U : TopologicalSpace.Opens NewtonianCoordinates}
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
        C / c ^ 4 :=
  testMass_acceleration_error f G m X a hΦ hψ hB hV

example (G m₁ m₂ c s : ℝ) (x₁ x₂ v₁ v₂ : S) :
    eihLagrangian G ![m₁, m₂] c s (![x₁, x₂], ![v₁, v₂]) =
      m₁ * (∑ j, v₁ j ^ 2) / 2 + m₂ * (∑ j, v₂ j ^ 2) / 2 + G * m₁ * m₂ * invDist (x₁ - x₂) +
        epsilon c * (m₁ * (∑ j, v₁ j ^ 2) ^ 2 / 8 + m₂ * (∑ j, v₂ j ^ 2) ^ 2 / 8 +
          G * m₁ * m₂ * invDist (x₁ - x₂) / 2 * (3 * ∑ j, v₁ j ^ 2 + 3 * ∑ j, v₂ j ^ 2 -
            7 * dot v₁ v₂ - dot v₁ (x₁ - x₂) * dot v₂ (x₁ - x₂) * invDist (x₁ - x₂) ^ 2) -
          G ^ 2 * m₁ * m₂ * (m₁ + m₂) * invDist (x₁ - x₂) ^ 2 / 2) :=
  eihLagrangian_two G m₁ m₂ c s x₁ x₂ v₁ v₂

example : euclidNorm (![1, 0, 0] - ![-1, 0, 0]) = 2 :=
  euclidNorm_two_sep

example (G : ℝ) (m : Fin N → ℝ) {δ V₀ : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V₀) :
    ∃ c₁, 1 ≤ c₁ ∧ ∀ c, c₁ ≤ c → ∀ p ∈ separatedSet N δ V₀, ∀ t : ℝ,
      ∃ X : ℝ → Fin N → S, ContDiff ℝ ∞ X ∧ X t = p.1 ∧ deriv X t = p.2 ∧
        Mechanics.eulerLagrange (eihLagrangian G m c) X t = 0 :=
  exists_eulerLagrange G m hδ hV

example (G : ℝ) {V₀ : ℝ} (hV : 0 ≤ V₀) (v₁ v₂ : S) (hv₁ : ‖v₁‖ ≤ V₀)
    (hv₂ : ‖v₂‖ ≤ V₀) :
    ∃ c₁, 1 ≤ c₁ ∧ ∀ c, c₁ ≤ c → ∀ t : ℝ, ∃ X : ℝ → Fin 2 → S, ContDiff ℝ ∞ X ∧
      X t = ![![1, 0, 0], ![-1, 0, 0]] ∧ deriv X t = ![v₁, v₂] ∧
      Mechanics.eulerLagrange (eihLagrangian G ![1, 1] c) X t = 0 :=
  exists_eulerLagrange_two G hV v₁ v₂ hv₁ hv₂

example {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : NewtonianCoordinates → F} {W K U : Set NewtonianCoordinates}
    (hW : IsOpen W) (hf : ContDiffOn ℝ 2 f W) (hK : IsCompact K) (hKW : K ⊆ W) (hUK : U ⊆ K) :
    ∃ C ≥ (0 : ℝ), CoordinateC2Bound U C f :=
  exists_coordinateC2Bound_of_contDiffOn hW hf hK hKW hUK

example {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set NewtonianCoordinates} {K : ℝ} (hK : 0 ≤ K) :
    CoordinateC2Bound U K (fun _ => (0 : F)) :=
  coordinateC2Bound_zero hK

example : NewtonianCoordinates :=
  restPoint

example (G M : ℝ) :
    ∃ (U : TopologicalSpace.Opens NewtonianCoordinates)
      (f : PostNewtonian.PostNewtonianMetricFamily U), restPoint ∈ U ∧
      (∀ q, f.potential q = othersPotential G (Function.update ![M, 0] 1 0)
        ((fun _ => 0 : ℝ → Fin 2 → S) (q 0)) 1 (Fin.tail q)) ∧
      (∀ q, f.scalarPotential q = othersScalarPotential G (Function.update ![M, 0] 1 0)
        ((fun _ => 0 : ℝ → Fin 2 → S) (q 0)) (deriv (fun _ => 0 : ℝ → Fin 2 → S) (q 0)) 1
          (Fin.tail q)) ∧
      (∀ q, f.vectorPotential q = othersVectorPotential G (Function.update ![M, 0] 1 0)
        ((fun _ => 0 : ℝ → Fin 2 → S) (q 0)) (deriv (fun _ => 0 : ℝ → Fin 2 → S) (q 0)) 1
          (Fin.tail q)) :=
  exists_family_rest G M

end ProjectAinos.GeneralRelativity.EinsteinInfeldHoffmann

end EinsteinInfeldHoffmann

section PostNewtonianField

open MeasureTheory Filter Set

open scoped Topology Laplacian ContDiff Real

namespace ProjectAinos.GeneralRelativity.PostNewtonianField

open SmoothGeometry.Potential EinsteinInfeldHoffmann NewtonianMetricFamily

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "S" => NewtonianSpace

variable {G : ℝ} {ρ : E3 → ℝ} {v : E3 → E3}

variable {N : ℕ}

example (G : ℝ) (ρ : E3 → ℝ) : E3 → ℝ :=
  newtonianPotential G ρ

example (G : ℝ) (ρ : E3 → ℝ) (v : E3 → E3) : E3 → ℝ :=
  secondSource G ρ v

example (G : ℝ) (ρ : E3 → ℝ) (v : E3 → E3) : E3 → ℝ :=
  secondPotential G ρ v

example (G : ℝ) (ρ : E3 → ℝ) (v : E3 → E3) (k : Fin 3) : E3 → ℝ :=
  vectorNewtonPotential G ρ v k

example {c : ℝ} {f : E3 → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun y => c * f y) :=
  hasCompactSupport_const_mul hf

example (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) :
    ContDiff ℝ 2 (newtonianPotential G ρ) :=
  contDiff_newtonianPotential hcρ hρ

example (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (x : E3) : Δ (newtonianPotential G ρ) x = 4 * π * G * ρ x :=
  laplacian_newtonianPotential hcρ hρ x

example (hcρ : HasCompactSupport ρ) :
    HasCompactSupport (secondSource G ρ v) :=
  hasCompactSupport_secondSource hcρ

example (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hv : ContDiff ℝ 2 v) : ContDiff ℝ 2 (secondSource G ρ v) :=
  contDiff_secondSource hcρ hρ hv

example (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hv : ContDiff ℝ 2 v) (x : E3) :
    Δ (secondPotential G ρ v) x =
      4 * π * G * (ρ x * (3 / 2 * ‖v x‖ ^ 2 - -newtonianPotential G ρ x)) :=
  laplacian_secondPotential hcρ hρ hv x

example (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hv : ContDiff ℝ 2 v) (k : Fin 3) (x : E3) :
    Δ (vectorNewtonPotential G ρ v k) x = -(4 * π * G * (ρ x * v x k)) :=
  laplacian_vectorNewtonPotential hcρ hρ hv k x

example {z : S} (hz : z ≠ 0) :
    ∑ α : Fin 3, (invDist z ^ 3 - 3 * invDist z ^ 5 * z α ^ 2) = 0 :=
  sum_invDist_cube_deriv hz

example {x y : S} (h : x ≠ y) (α : Fin 3) :
    HasDerivAt (fun r : ℝ => invDist (x + r • (Pi.single α 1 : S) - y) ^ 3 *
        (x + r • (Pi.single α 1 : S) - y) α)
      (invDist (x - y) ^ 3 - 3 * invDist (x - y) ^ 5 * (x - y) α ^ 2) 0 :=
  hasDerivAt_invDist_cube_line h α

example (w : Fin N → ℝ) (X : Fin N → S) (s : Finset (Fin N)) {x : S}
    (hx : ∀ b ∈ s, x ≠ X b) (h : S) :
    fderiv ℝ (fun y => ∑ b ∈ s, w b * invDist (y - X b)) x h =
      ∑ b ∈ s, w b * (-(invDist (x - X b) ^ 3) * dot (x - X b) h) :=
  fderiv_weighted_apply w X s hx h

example (w : Fin N → ℝ) (X : Fin N → S) (s : Finset (Fin N)) {x : S}
    (hx : ∀ b ∈ s, x ≠ X b) :
    flatLaplacian (fun y => ∑ b ∈ s, w b * invDist (y - X b)) x = 0 :=
  flatLaplacian_weighted w X s hx

example (G : ℝ) (m : Fin N → ℝ) (X : Fin N → S) (a : Fin N)
    {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) : flatLaplacian (othersPotential G m X a) x = 0 :=
  flatLaplacian_othersPotential G m X a hx

example (G : ℝ) (m : Fin N → ℝ) (X V : Fin N → S)
    (a : Fin N) {x : S} (hx : ∀ b, b ≠ a → x ≠ X b) :
    flatLaplacian (othersScalarPotential G m X V a) x = 0 :=
  flatLaplacian_othersScalarPotential G m X V a hx

example {z : S} (hz : z ≠ 0) (u : S) :
    ∑ k, dKernelB z u (Pi.single k 1) k = -6 * dot u z * invDist z ^ 3 :=
  sum_dKernelB_single hz u

example (G : ℝ) (m : Fin N → ℝ) {X : ℝ → Fin N → S} {t : ℝ}
    (hX : DifferentiableAt ℝ X t) (a : Fin N) {x : S} (hx : ∀ b, b ≠ a → x ≠ X t b) :
    ∑ k, fderiv ℝ (othersVectorPotential G m (X t) (deriv X t) a) x (Pi.single k 1) k +
      3 * deriv (fun s => othersPotential G m (X s) a x) t = 0 :=
  gauge_othersVectorPotential G m hX a hx

end ProjectAinos.GeneralRelativity.PostNewtonianField

end PostNewtonianField

section PostNewtonianRicci

open Set Filter

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.PostNewtonianRicci

open SmoothGeometry SmoothGeometry.CoordinateMetric NewtonianMetricFamily

local notation "E" => NewtonianCoordinates

local notation "S" => NewtonianSpace

variable {d : ℕ} {C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
  {y : MinkowskiModel d} {α : Type} {T : Set α} {ε f g f₀ f₁ g₀ g₁ : α → ℝ}
  {Φ ψ : E → ℝ} {B : E → S} {W : Set E} {K : ℝ} {q : E}

example (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d)
    (m a b : Fin (d + 1)) : ℝ :=
  jet1 C y m a b

example (C : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (y : MinkowskiModel d)
    (m n a b : Fin (d + 1)) : ℝ :=
  jet2 C y m n a b

example (D : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ) (i j l : Fin (d + 1)) : ℝ :=
  lowerJet D i j l

example (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (D : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (k i j : Fin (d + 1)) : ℝ :=
  gamJet M D k i j

example (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (D : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (D₂ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ) (m k i j : Fin (d + 1)) :
    ℝ :=
  dGamJet M D D₂ m k i j

example (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (D : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ)
    (D₂ : Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → Fin (d + 1) → ℝ) (j k : Fin (d + 1)) : ℝ :=
  ricciJet M D D₂ j k

example (z : MinkowskiModel d) (k i j : Fin (d + 1)) :
    christoffelOf C z k i j = gamJet (C z)⁻¹ (jet1 C z) k i j :=
  christoffelOf_eq_gamJet z k i j

example (hC : ∀ a b, DifferentiableAt ℝ (fun z => C z a b) y)
    (hdet : ∀ᶠ z in 𝓝 y, (C z).det ≠ 0) (k l : Fin (d + 1)) :
    DifferentiableAt ℝ (fun z => (C z)⁻¹ k l) y ∧
      fderiv ℝ (fun z => (C z)⁻¹ k l) y = -∑ p, ∑ q, (C y)⁻¹ k p • (C y)⁻¹ q l •
        fderiv ℝ (fun z => C z p q) y :=
  hasFDerivAt_inv_apply hC hdet k l

example (hC : ∀ a b, ContDiffAt ℝ 2 (fun z => C z a b) y)
    (hdet : ∀ᶠ z in 𝓝 y, (C z).det ≠ 0) (j k : Fin (d + 1)) :
    ricciOf C y j k = ricciJet (C y)⁻¹ (jet1 C y) (jet2 C y) j k :=
  ricciOf_eq_ricciJet hC hdet j k

example (g : E → ℝ) (q : E) (m : Fin 4) : ℝ :=
  pd g q m

example (g : E → ℝ) (q : E) (m n : Fin 4) : ℝ :=
  pd2 g q m n

example (g : E → ℝ) (q : E) (m n : Fin 4) : ℝ :=
  sd g q m n

example {g : E → ℝ} {q : E} (hg : ContDiffAt ℝ 2 g q) (m n : Fin 4) :
    pd2 g q m n = fderiv ℝ (fderiv ℝ g) q (Pi.single m 1) (Pi.single n 1) :=
  pd2_eq_fderiv_fderiv hg m n

example {g : E → ℝ} {q : E} (hg : ContDiffAt ℝ 2 g q) (m n : Fin 4) :
    pd2 g q m n = pd2 g q n m :=
  pd2_comm hg m n

example {g : E → ℝ} {q : E} (hg : ContDiffAt ℝ 2 g q) (m n : Fin 4) :
    pd2 g q m n = sd g q m n :=
  pd2_eq_sd hg m n

example (Φ : E → ℝ) (c : ℝ) (q : E) : ℝ :=
  spatialFactor Φ c q

example (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  pnCoefficient Φ ψ B c q

example (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) : ℝ :=
  pnDenom Φ ψ B c q

example (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (i j : Fin 3) : ℝ :=
  pnSpatialInverse Φ ψ B c q i j

example (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  pnInverse Φ ψ B c q

example {Φ ψ : E → ℝ} {B : E → S} {c : ℝ} (hc : c ≠ 0) {q : E}
    (hs : spatialFactor Φ c q ≠ 0) (hD : pnDenom Φ ψ B c q ≠ 0) :
    pnCoefficient Φ ψ B c q * pnInverse Φ ψ B c q = 1 :=
  pnCoefficient_mul_inverse hc hs hD

example (B : E → S) (j : Fin 3) : E → ℝ :=
  comp B j

example (B : E → S) (j : Fin 3) : comp B j = fun z => B z j :=
  comp_eq B j

example (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (m : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  pnJet1 Φ ψ B c q m

example (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (m n : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  pnJet2 Φ ψ B c q m n

example (c : ℝ) (hΦ : DifferentiableAt ℝ Φ q) (hψ : DifferentiableAt ℝ ψ q)
    (hB : ∀ j, DifferentiableAt ℝ (comp B j) q) (m a b : Fin 4) :
    jet1 (d := 3) (pnCoefficient Φ ψ B c) q m a b = pnJet1 Φ ψ B c q m a b :=
  jet1_pnCoefficient c hΦ hψ hB m a b

example (c : ℝ) {W : Set E} (hW : IsOpen W) (hq : q ∈ W)
    (hΦ : ∀ z ∈ W, ContDiffAt ℝ 2 Φ z) (hψ : ∀ z ∈ W, ContDiffAt ℝ 2 ψ z)
    (hB : ∀ z ∈ W, ∀ j, ContDiffAt ℝ 2 (comp B j) z) (m n a b : Fin 4) :
    jet2 (d := 3) (pnCoefficient Φ ψ B c) q m n a b = pnJet2 Φ ψ B c q m n a b :=
  jet2_pnCoefficient c hW hq hΦ hψ hB m n a b

example {α : Type} (T : Set α) (F : α → ℝ) : Prop :=
  BoundedOn T F

example (hf : BoundedOn T f) (hg : BoundedOn T g) :
    BoundedOn T (fun x => f x + g x) :=
  BoundedOn.add' hf hg

example (hf : BoundedOn T f) (hg : BoundedOn T g) :
    BoundedOn T (fun x => f x * g x) :=
  BoundedOn.mul' hf hg

example (hf : BoundedOn T f) : BoundedOn T (fun x => -f x) :=
  BoundedOn.neg' hf

example (a : ℝ) : BoundedOn T (fun _ => a) :=
  BoundedOn.const' a

example {C : ℝ} (h : ∀ x ∈ T, |f x| ≤ C) : BoundedOn T f :=
  BoundedOn.of_le' h

example {ι : Type} [Fintype ι] {K : ι → α → ℝ}
    (hK : ∀ i, BoundedOn T (K i)) : BoundedOn T (fun x => ∑ i, K i x) :=
  BoundedOn.sum' hK

example (h : IsExp T ε f f₀ f₁) : BoundedOn T f :=
  IsExp.bounded h

example (hε : ∀ p ∈ T, 0 ≤ ε p ∧ ε p ≤ 1) (a : ℝ) :
    IsExp T ε (fun _ => a) (fun _ => a) (fun _ => 0) :=
  IsExp.const hε a

example (hε : ∀ p ∈ T, 0 ≤ ε p ∧ ε p ≤ 1) :
    IsExp T ε (fun p => ε p) (fun _ => 0) (fun _ => 1) :=
  IsExp.eps_self hε

example {f₂ : α → ℝ} (hε : ∀ p ∈ T, 0 ≤ ε p ∧ ε p ≤ 1) (h₀ : BoundedOn T f₀)
    (h₁ : BoundedOn T f₁) (h₂ : BoundedOn T f₂)
    (h : ∀ p ∈ T, f p = f₀ p + ε p * f₁ p + ε p ^ 2 * f₂ p) : IsExp T ε f f₀ f₁ :=
  IsExp.of_eq hε h₀ h₁ h₂ h

example (hε : ∀ p ∈ T, 0 ≤ ε p ∧ ε p ≤ 1) (hf : BoundedOn T f) :
    IsExp T ε f f (fun _ => 0) :=
  IsExp.atom hε hf

example (hf : IsExp T ε f f₀ f₁) (hg : IsExp T ε g g₀ g₁) :
    IsExp T ε (fun p => f p + g p) (fun p => f₀ p + g₀ p) (fun p => f₁ p + g₁ p) :=
  IsExp.add hf hg

example (hf : IsExp T ε f f₀ f₁) :
    IsExp T ε (fun p => -f p) (fun p => -f₀ p) (fun p => -f₁ p) :=
  IsExp.neg hf

example (hf : IsExp T ε f f₀ f₁) (hg : IsExp T ε g g₀ g₁) :
    IsExp T ε (fun p => f p - g p) (fun p => f₀ p - g₀ p) (fun p => f₁ p - g₁ p) :=
  IsExp.sub hf hg

example (hf : IsExp T ε f f₀ f₁) (hg : IsExp T ε g g₀ g₁) :
    IsExp T ε (fun p => f p * g p) (fun p => f₀ p * g₀ p)
      (fun p => f₀ p * g₁ p + f₁ p * g₀ p) :=
  IsExp.mul hf hg

example (hf : IsExp T ε f f₀ f₁) :
    IsExp T ε (fun p => f p ^ 2) (fun p => f₀ p * f₀ p)
      (fun p => f₀ p * f₁ p + f₁ p * f₀ p) :=
  IsExp.pow_two hf

example (hf : IsExp T ε f f₀ f₁) :
    IsExp T ε (fun p => f p ^ 3) (fun p => f₀ p * f₀ p * f₀ p)
      (fun p => f₀ p * f₀ p * f₁ p + (f₀ p * f₁ p + f₁ p * f₀ p) * f₀ p) :=
  IsExp.pow_three hf

example (hf : IsExp T ε f f₀ f₁) (a : ℝ) :
    IsExp T ε (fun p => f p / a) (fun p => f₀ p / a) (fun p => f₁ p / a) :=
  IsExp.div_const hf a

example {ι : Type} [Fintype ι] [Nonempty ι] {F F₀ F₁ : ι → α → ℝ}
    (h : ∀ i, IsExp T ε (F i) (F₀ i) (F₁ i)) :
    IsExp T ε (fun p => ∑ i, F i p) (fun p => ∑ i, F₀ i p) (fun p => ∑ i, F₁ i p) :=
  IsExp.sum h

example {f₀' f₁' : α → ℝ} (h : IsExp T ε f f₀ f₁) (h₀ : ∀ p ∈ T, f₀ p = f₀' p)
    (h₁ : ∀ p ∈ T, f₁ p = f₁' p) : IsExp T ε f f₀' f₁' :=
  IsExp.congr h h₀ h₁

example {f' : α → ℝ} (h : IsExp T ε f f₀ f₁) (hf : ∀ p ∈ T, f p = f' p) :
    IsExp T ε f' f₀ f₁ :=
  IsExp.congr_left h hf

example : Matrix (Fin 4) (Fin 4) ℝ :=
  inv0

example (Φ : E → ℝ) (q : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  inv1 Φ q

example (Φ : E → ℝ) (q : E) (m : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  jet10 Φ q m

example (Φ ψ : E → ℝ) (B : E → S) (q : E) (m : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  jet11 Φ ψ B q m

example (Φ : E → ℝ) (q : E) (m n : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  jet20 Φ q m n

example (Φ ψ : E → ℝ) (B : E → S) (q : E) (m n : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  jet21 Φ ψ B q m n

example (W : Set E) (c₁ : ℝ) : Set (ℝ × E) :=
  pnSet W c₁

example :
    PotentialBounds (fun _ => 0) (fun _ => 0) (fun _ => 0) Set.univ 0 :=
  potentialBounds_zero

example (K : ℝ) : ℝ :=
  threshold K

example {c : ℝ} (hK : 0 ≤ K) (hc : threshold K ≤ c) :
    0 ≤ epsilon c ∧ epsilon c ≤ 1 ∧ epsilon c * (K ^ 2 + K + 1) ≤ 1 / 8 :=
  eps_bounds hK hc

example {c : ℝ} {q : E} (hb : PotentialBounds Φ ψ B W K) (hq : q ∈ W)
    (hc : threshold K ≤ c) : 3 / 4 ≤ spatialFactor Φ c q :=
  spatialFactor_ge hb hq hc

example {c : ℝ} {q : E} (hb : PotentialBounds Φ ψ B W K) (hq : q ∈ W)
    (hc : threshold K ≤ c) : 3 / 8 ≤ pnDenom Φ ψ B c q :=
  pnDenom_ge hb hq hc

example (c : ℝ) {q : E} (hΦ : ContDiffAt ℝ 2 Φ q)
    (hψ : ContDiffAt ℝ 2 ψ q) (hB : ∀ j, ContDiffAt ℝ 2 (comp B j) q) (a b : Fin 4) :
    ContDiffAt ℝ 2 (fun z => pnCoefficient Φ ψ B c z a b) q :=
  contDiffAt_pnCoefficient c hΦ hψ hB a b

example {c : ℝ} {q : E} (hb : PotentialBounds Φ ψ B W K) (hq : q ∈ W)
    (hc : threshold K ≤ c) : (pnCoefficient Φ ψ B c q)⁻¹ = pnInverse Φ ψ B c q :=
  pnCoefficient_inv hb hq hc

example (hW : IsOpen W) (hΦ : ∀ z ∈ W, ContDiffAt ℝ 2 Φ z)
    (hψ : ∀ z ∈ W, ContDiffAt ℝ 2 ψ z) (hB : ∀ z ∈ W, ∀ j, ContDiffAt ℝ 2 (comp B j) z)
    (hb : PotentialBounds Φ ψ B W K) {c : ℝ} (hc : threshold K ≤ c) {q : E} (hq : q ∈ W)
    (j k : Fin 4) :
    ricciOf (d := 3) (pnCoefficient Φ ψ B c) q j k =
      ricciJet (pnInverse Φ ψ B c q) (pnJet1 Φ ψ B c q) (pnJet2 Φ ψ B c q) j k :=
  ricciOf_pnCoefficient hW hΦ hψ hB hb hc hq j k

example (hK : 0 ≤ K) : ∀ p ∈ pnSet W (threshold K),
    0 ≤ epsilon p.1 ∧ epsilon p.1 ≤ 1 :=
  pnSet_eps hK

example {g : E → ℝ} (h : ∀ q ∈ W, |g q| ≤ K) :
    BoundedOn (pnSet W (threshold K)) (fun p => g p.2) :=
  boundedOn_of_W h

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => (spatialFactor Φ p.1 p.2)⁻¹) (fun _ => 1) (fun p => 2 * Φ p.2) :=
  exp_sigma hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => (pnDenom Φ ψ B p.1 p.2)⁻¹) (fun _ => 1) (fun _ => 0) :=
  exp_delta hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => epsilon p.1) (fun _ => 0)
      (fun _ => 1) ∧
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => Φ p.2) (fun p => Φ p.2)
      (fun _ => 0) ∧
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => ψ p.2) (fun p => ψ p.2)
      (fun _ => 0) ∧
    (∀ j, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => B p.2 j)
      (fun p => B p.2 j) (fun _ => 0)) ∧
    (∀ m, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => pd Φ p.2 m)
      (fun p => pd Φ p.2 m) (fun _ => 0)) ∧
    (∀ m, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => pd ψ p.2 m)
      (fun p => pd ψ p.2 m) (fun _ => 0)) ∧
    (∀ j m, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => pd (comp B j) p.2 m)
      (fun p => pd (comp B j) p.2 m) (fun _ => 0)) ∧
    (∀ m n, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => sd Φ p.2 m n)
      (fun p => sd Φ p.2 m n) (fun _ => 0)) ∧
    (∀ m n, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1) (fun p => sd ψ p.2 m n)
      (fun p => sd ψ p.2 m n) (fun _ => 0)) ∧
    (∀ j m n, IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => sd (comp B j) p.2 m n) (fun p => sd (comp B j) p.2 m n) (fun _ => 0)) :=
  exp_atoms hb

example (hb : PotentialBounds Φ ψ B W K) (a b : Fin 4) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => pnInverse Φ ψ B p.1 p.2 a b) (fun _ => inv0 a b) (fun p => inv1 Φ p.2 a b) :=
  exp_inverse hb a b

example (hb : PotentialBounds Φ ψ B W K) (m a b : Fin 4) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => pnJet1 Φ ψ B p.1 p.2 m a b) (fun p => jet10 Φ p.2 m a b)
      (fun p => jet11 Φ ψ B p.2 m a b) :=
  exp_jet1 hb m a b

example (hb : PotentialBounds Φ ψ B W K) (m n a b : Fin 4) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => pnJet2 Φ ψ B p.1 p.2 m n a b) (fun p => jet20 Φ p.2 m n a b)
      (fun p => jet21 Φ ψ B p.2 m n a b) :=
  exp_jet2 hb m n a b

example (g : E → ℝ) (q : E) : ℝ :=
  lap g q

example (B : E → S) (q : E) : ℝ :=
  dtDiv B q

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        0 0)
      (fun p => lap Φ p.2)
      (fun p => 4 * Φ p.2 * lap Φ p.2 + lap ψ p.2 + 3 * sd Φ p.2 0 0 + dtDiv B p.2) :=
  exp_ricci_tt hb

example (B : E → S) (q : E) (α : Fin 3) : ℝ :=
  gradDiv B q α

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        0 1)
      (fun _ => 0)
      (fun p => -(lap (comp B 0) p.2 - gradDiv B p.2 0 - 4 * sd Φ p.2 0 1) / 2) :=
  exp_ricci_t0 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        0 2)
      (fun _ => 0)
      (fun p => -(lap (comp B 1) p.2 - gradDiv B p.2 1 - 4 * sd Φ p.2 0 2) / 2) :=
  exp_ricci_t1 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        0 3)
      (fun _ => 0)
      (fun p => -(lap (comp B 2) p.2 - gradDiv B p.2 2 - 4 * sd Φ p.2 0 3) / 2) :=
  exp_ricci_t2 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        1 1)
      (fun _ => 0) (fun p => lap Φ p.2) :=
  exp_ricci_s00 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        1 2)
      (fun _ => 0) (fun _ => 0) :=
  exp_ricci_s01 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        1 3)
      (fun _ => 0) (fun _ => 0) :=
  exp_ricci_s02 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        2 1)
      (fun _ => 0) (fun _ => 0) :=
  exp_ricci_s10 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        2 2)
      (fun _ => 0) (fun p => lap Φ p.2) :=
  exp_ricci_s11 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        2 3)
      (fun _ => 0) (fun _ => 0) :=
  exp_ricci_s12 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        3 1)
      (fun _ => 0) (fun _ => 0) :=
  exp_ricci_s20 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        3 2)
      (fun _ => 0) (fun _ => 0) :=
  exp_ricci_s21 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        3 3)
      (fun _ => 0) (fun p => lap Φ p.2) :=
  exp_ricci_s22 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        1 0)
      (fun _ => 0)
      (fun p => -(lap (comp B 0) p.2 - gradDiv B p.2 0 - 4 * sd Φ p.2 0 1) / 2) :=
  exp_ricci_r0 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        2 0)
      (fun _ => 0)
      (fun p => -(lap (comp B 1) p.2 - gradDiv B p.2 1 - 4 * sd Φ p.2 0 2) / 2) :=
  exp_ricci_r1 hb

example (hb : PotentialBounds Φ ψ B W K) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        3 0)
      (fun _ => 0)
      (fun p => -(lap (comp B 2) p.2 - gradDiv B p.2 2 - 4 * sd Φ p.2 0 3) / 2) :=
  exp_ricci_r2 hb

example (hb : PotentialBounds Φ ψ B W K) (α : Fin 3) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        0 α.succ)
      (fun _ => 0)
      (fun p => -(lap (comp B α) p.2 - gradDiv B p.2 α - 4 * sd Φ p.2 0 α.succ) / 2) :=
  exp_ricci_ti hb α

example (hb : PotentialBounds Φ ψ B W K) (α β : Fin 3) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        α.succ β.succ)
      (fun _ => 0) (fun p => if α = β then lap Φ p.2 else 0) :=
  exp_ricci_ij hb α β

example (hb : PotentialBounds Φ ψ B W K) (α : Fin 3) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        α.succ 0)
      (fun _ => 0)
      (fun p => -(lap (comp B α) p.2 - gradDiv B p.2 α - 4 * sd Φ p.2 0 α.succ) / 2) :=
  exp_ricci_it hb α

example (Φ : E → ℝ) (q : E) (j k : Fin 4) : ℝ :=
  ricciLeading Φ q j k

example (Φ ψ : E → ℝ) (B : E → S) (q : E) (j k : Fin 4) : ℝ :=
  ricciFirst Φ ψ B q j k

example (hb : PotentialBounds Φ ψ B W K) (j k : Fin 4) :
    IsExp (pnSet W (threshold K)) (fun p => epsilon p.1)
      (fun p => ricciJet (pnInverse Φ ψ B p.1 p.2) (pnJet1 Φ ψ B p.1 p.2) (pnJet2 Φ ψ B p.1 p.2)
        j k)
      (fun p => ricciLeading Φ p.2 j k) (fun p => ricciFirst Φ ψ B p.2 j k) :=
  exp_ricci hb j k

example (hW : IsOpen W) (hΦ : ∀ z ∈ W, ContDiffAt ℝ 2 Φ z)
    (hψ : ∀ z ∈ W, ContDiffAt ℝ 2 ψ z) (hB : ∀ z ∈ W, ∀ j, ContDiffAt ℝ 2 (comp B j) z)
    (hb : PotentialBounds Φ ψ B W K) :
    ∃ C, 0 ≤ C ∧ ∀ c, threshold K ≤ c → ∀ q ∈ W, ∀ j k : Fin 4,
      |ricciOf (d := 3) (pnCoefficient Φ ψ B c) q j k -
        (ricciLeading Φ q j k + epsilon c * ricciFirst Φ ψ B q j k)| ≤ C / c ^ 4 :=
  abs_ricciOf_pnCoefficient_sub_le hW hΦ hψ hB hb


end ProjectAinos.GeneralRelativity.PostNewtonianRicci

end PostNewtonianRicci

section PostNewtonianSources

open MeasureTheory Filter Set

open scoped Topology ContDiff Real Convolution

namespace ProjectAinos.GeneralRelativity.PostNewtonianSources

open SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (e : ℝ) (z : E3) : ℝ :=
  regNorm e z

example {e : ℝ} (he : e ≠ 0) : ContDiff ℝ ∞ (regNorm e) :=
  contDiff_regNorm he

example {e : ℝ} (he : e ≠ 0) (z : E3) :
    coordLaplacian (regNorm e) z =
      (2 * ‖z‖ ^ 2 + 3 * e ^ 2) / ((‖z‖ ^ 2 + e ^ 2) * √(‖z‖ ^ 2 + e ^ 2)) :=
  coordLaplacian_regNorm he z

example {φ : E3 → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hcφ : HasCompactSupport φ) :
    ∫ z, ‖z‖ * coordLaplacian φ z = 8 * π * ∫ z, newtonKernel z * φ z :=
  integral_norm_mul_coordLaplacian hφ hcφ

example (f : E3 → ℝ) : E3 → ℝ :=
  superPotential f

example (f : E3 → ℝ) (x : E3) :
    superPotential f x = ∫ y, ‖y‖ * f (x - y) :=
  superPotential_apply f x

example : LocallyIntegrable (fun y : E3 => ‖y‖) :=
  locallyIntegrable_norm

example {f : E3 → ℝ} {n : ℕ∞} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (superPotential f) :=
  contDiff_superPotential hc hf

example {f : E3 → ℝ} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 1 f) (x v : E3) :
    fderiv ℝ (superPotential f) x v = superPotential (fun y => fderiv ℝ f y v) x :=
  fderiv_superPotential_apply hc hf x v

example {f : E3 → ℝ} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 2 f) (x : E3) :
    coordLaplacian (superPotential f) x = 8 * π * newtonPotential f x :=
  coordLaplacian_superPotential hc hf x

example {κ : E3 → ℝ} (hκ : LocallyIntegrable κ) {f : ℝ → E3 → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {k : Set E3} (hk : IsCompact k)
    (hfk : ∀ t x, x ∉ k → f t x = 0) :
    ContDiff ℝ ∞ (fun q : ℝ × E3 => (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f q.1) q.2) :=
  contDiff_convolution_param hκ hf hk hfk

example {κ : E3 → ℝ} (hκ : LocallyIntegrable κ) {f : ℝ → E3 → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {k : Set E3} (hk : IsCompact k)
    (hfk : ∀ t x, x ∉ k → f t x = 0) (t : ℝ) (x : E3) :
    HasDerivAt (fun s => (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f s) x)
      ((κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun y => deriv (fun s => f s y) t) x) t :=
  hasDerivAt_convolution_time hκ hf hk hfk t x

example {f : ℝ → E3 → ℝ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    {k : Set E3} (hk : IsCompact k) (hfk : ∀ t x, x ∉ k → f t x = 0) (t : ℝ) (x : E3) :
    HasDerivAt (fun s => newtonPotential (f s) x)
      (newtonPotential (fun y => deriv (fun s => f s y) t) x) t :=
  hasDerivAt_newtonPotential_time hf hk hfk t x

example {f : ℝ → E3 → ℝ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    {k : Set E3} (hk : IsCompact k) (hfk : ∀ t x, x ∉ k → f t x = 0) (t : ℝ) (x : E3) :
    HasDerivAt (fun s => superPotential (f s) x)
      (superPotential (fun y => deriv (fun s => f s y) t) x) t :=
  hasDerivAt_superPotential_time hf hk hfk t x

example {f : ℝ → E3 → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {k : Set E3} (hk : IsCompact k)
    (hfk : ∀ t x, x ∉ k → f t x = 0) :
    ContDiff ℝ ∞ (fun q : ℝ × E3 => newtonPotential (f q.1) q.2) :=
  contDiff_newtonPotential_param hf hk hfk

example {f : ℝ → E3 → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {k : Set E3} (hk : IsCompact k)
    (hfk : ∀ t x, x ∉ k → f t x = 0) :
    ContDiff ℝ ∞ (fun q : ℝ × E3 => superPotential (f q.1) q.2) :=
  contDiff_superPotential_param hf hk hfk

example {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3}
    (hρ : ContDiff ℝ ∞ (Function.uncurry ρ)) (hv : ∀ t, ContDiff ℝ ∞ (v t)) {k : Set E3}
    (hk : IsCompact k) (hρk : ∀ t x, x ∉ k → ρ t x = 0)
    (hcont : ∀ t y, deriv (fun s => ρ s y) t =
      -∑ j, fderiv ℝ (fun z => ρ t z * v t z j) y (EuclideanSpace.single j 1)) (t : ℝ) (x : E3) :
    HasDerivAt (fun s => newtonPotential (ρ s) x)
      (-∑ j, fderiv ℝ (newtonPotential fun z => ρ t z * v t z j) x (EuclideanSpace.single j 1))
      t :=
  hasDerivAt_newtonPotential_continuity hρ hv hk hρk hcont t x


end ProjectAinos.GeneralRelativity.PostNewtonianSources

end PostNewtonianSources
