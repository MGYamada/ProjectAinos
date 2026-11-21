/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.Diffraction.MaxwellAperture

/-! Public consumers of the uniqueness of the scalar aperture field and of one Maxwell
polarization (Landau–Lifshitz §59): the divergence theorem on a half-space and complex fluxes
through spheres, the Green field of the half-space above a plane, the representation of a
radiating solution by its values on a plane, joint continuity of the aperture field up to the
plane, existence and uniqueness of the radiating Dirichlet problem, and the time-harmonic Maxwell
fields `E = curl(0, 0, u)`, `B = curl E/(ik)` with their radiation and boundary conditions.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

universe u v w

section HalfSpace

open MeasureTheory Set Metric Filter

open scoped Topology ContDiff InnerProductSpace

namespace ProjectAinos.SmoothGeometry.Sphere

local notation "E2" => EuclideanSpace ℝ (Fin 2)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (p : E3) (i : Fin 3) :
    |p i| ≤ ‖p‖ :=
  abs_apply_le_norm p i

example {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {G : E3 → V} {L : ℝ}
    (hG : ∀ p : E3, L < ‖p‖ → G p = 0) {p : E3} (hp : L < ‖p‖) :
    fderiv ℝ G p = 0 :=
  fderiv_eq_zero_of_lt_norm hG hp

example {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : Fin 3 → E3 → V} {O : Set E3}
    (hO : IsOpen O) {ε : ℝ} (hsub : ∀ p : E3, ε ≤ p 2 → p ∈ O) (hF : ∀ α, ContDiffOn ℝ 1 (F α) O)
    {L : ℝ} (hL : ∀ α (p : E3), L < ‖p‖ → F α p = 0) :
    ∫ p in {p : E3 | ε ≤ p 2}, ∑ α, fderiv ℝ (F α) p (EuclideanSpace.single α 1) = -∫ x : E2, F 2
      !₂[x 0, x 1, ε] :=
  integral_divergence_halfSpace hO hsub hF hL

example {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] {G : ℝ → E3 → V} {O : Set (ℝ × E3)}
    (hO : IsOpen O) {s₀ : ℝ} (hs₀ : ∀ n ∈ sphere (0 : E3) 1, (s₀, n) ∈ O)
    (hG : ContinuousOn (Function.uncurry G) O) :
    ContinuousAt (fun s => ∫ n : sphere (0 : E3) 1, G s n ∂sphereMeasure) s₀ :=
  continuousAt_integral_sphere_of_continuousOn hO hs₀ hG

example (V : Fin 3 → E3 → ℂ) (c : E3) (R : ℝ) :
    ℂ :=
  fluxC V c R

example (V : Fin 3 → E3 → ℂ) (x : E3) :
    ℂ :=
  divergenceC V x

example (V : Fin 3 → E3 → ℂ) (c : E3) :
    fluxC V c 0 = 0 :=
  fluxC_zero V c

example (V : Fin 3 → E3 → ℂ) (c : E3) :
    Fin 3 → E3 → ℝ :=
  rePart V c

example (V : Fin 3 → E3 → ℂ) (c : E3) :
    Fin 3 → E3 → ℝ :=
  imPart V c

example {V : Fin 3 → E3 → ℂ} {W : Set E3} (hV : ∀ α, ContinuousOn (V α) W) {c : E3} {R : ℝ}
    (hR : ∀ n ∈ sphere (0 : E3) 1, c + R • n ∈ W) :
    Integrable (fun n : sphere (0 : E3) 1 => ((R ^ 2 : ℝ) : ℂ) * ∑ α, V α (c + R • (n : E3)) *
      (((n : E3) α : ℝ) : ℂ)) sphereMeasure :=
  integrable_fluxC_integrand hV hR

example {V : Fin 3 → E3 → ℂ} {W : Set E3} (hV : ∀ α, ContinuousOn (V α) W) {c : E3} {R : ℝ}
    (hR : ∀ n ∈ sphere (0 : E3) 1, c + R • n ∈ W) :
    (fluxC V c R).re = flux (rePart V c) R :=
  re_fluxC hV hR

example {V : Fin 3 → E3 → ℂ} {W : Set E3} (hV : ∀ α, ContinuousOn (V α) W) {c : E3} {R : ℝ}
    (hR : ∀ n ∈ sphere (0 : E3) 1, c + R • n ∈ W) :
    (fluxC V c R).im = flux (imPart V c) R :=
  im_fluxC hV hR

example {g : E3 → ℂ} {c x : E3} (hg : DifferentiableAt ℝ g (c + x)) (v : E3) :
    fderiv ℝ (fun x => (g (c + x)).re) x v = (fderiv ℝ g (c + x) v).re :=
  fderiv_re_comp_add hg v

example {g : E3 → ℂ} {c x : E3} (hg : DifferentiableAt ℝ g (c + x)) (v : E3) :
    fderiv ℝ (fun x => (g (c + x)).im) x v = (fderiv ℝ g (c + x) v).im :=
  fderiv_im_comp_add hg v

example {V : Fin 3 → E3 → ℂ} {W : Set E3} (hW : IsOpen W) (hV : ∀ α, ContDiffOn ℝ 1 (V α) W)
    {c : E3} {R₁ R₂ : ℝ} (h0 : 0 ≤ R₁) (h12 : R₁ ≤ R₂)
    (hsub : ∀ x : E3, R₁ ≤ ‖x‖ → ‖x‖ ≤ R₂ → c + x ∈ W) :
    fluxC V c R₂ - fluxC V c R₁ = ∫ x in shell R₁ R₂, divergenceC V (c + x) :=
  fluxC_sub_fluxC hW hV h0 h12 hsub

example {t : ℝ} (ht : t < 0 ∨ 1 < t) :
    deriv Real.smoothTransition t = 0 :=
  deriv_smoothTransition_eq_zero ht

example :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t, |deriv Real.smoothTransition t| ≤ S :=
  exists_abs_deriv_smoothTransition_le

example (c : E3) (a b : ℝ) (p : E3) :
    ℝ :=
  radialCutoff c a b p

example (c : E3) (a b : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (radialCutoff c a b) :=
  contDiff_radialCutoff c a b

example (c : E3) (a b : ℝ) (p : E3) :
    HasFDerivAt (radialCutoff c a b) ((deriv Real.smoothTransition (a * ‖p - c‖ ^ 2 + b) * (2 * a))
      • innerSL ℝ (p - c)) p :=
  hasFDerivAt_radialCutoff c a b p

example (c : E3) (a b : ℝ) (p v : E3) :
    fderiv ℝ (radialCutoff c a b) p v = deriv Real.smoothTransition (a * ‖p - c‖ ^ 2 + b) * (2 * a)
      * ⟪p - c, v⟫_ℝ :=
  fderiv_radialCutoff_apply c a b p v

example (c : E3) (a b : ℝ) (p : E3) :
    radialCutoff c a b p ∈ Icc 0 1 :=
  radialCutoff_mem_Icc c a b p

example {c : E3} {a b : ℝ} {p : E3} (h : a * ‖p - c‖ ^ 2 + b ≤ 0) :
    radialCutoff c a b p = 0 :=
  radialCutoff_eq_zero h

example {c : E3} {a b : ℝ} {p : E3} (h : 1 ≤ a * ‖p - c‖ ^ 2 + b) :
    radialCutoff c a b p = 1 :=
  radialCutoff_eq_one h

example {c : E3} {a b : ℝ} {p : E3} (h : a * ‖p - c‖ ^ 2 + b < 0 ∨ 1 < a * ‖p - c‖ ^ 2 + b) :
    fderiv ℝ (radialCutoff c a b) p = 0 :=
  fderiv_radialCutoff_eq_zero h

example {f : E3 → ℝ} {g : E3 → ℂ} {p : E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (v : E3) :
    fderiv ℝ (fun q => (f q : ℂ) * g q) p v = (f p : ℂ) * fderiv ℝ g p v + (fderiv ℝ f p v : ℂ) * g
      p :=
  fderiv_ofReal_mul_apply hf hg v

example {f : E3 → ℝ} {g : E3 → ℂ} {p : E3} {n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f p)
    (hg : ContDiffAt ℝ n g p) :
    ContDiffAt ℝ n (fun q => (f q : ℂ) * g q) p :=
  contDiffAt_ofReal_mul hf hg

example {V : Type w} [NormedAddCommGroup V] {g : E3 → V} {O s : Set E3} (hs : IsClosed s)
    (hsO : s ⊆ O) (hg : ContinuousOn g O) {L : ℝ} (hL : ∀ p : E3, L < ‖p‖ → g p = 0) :
    IntegrableOn g s :=
  integrableOn_of_continuousOn_of_eq_zero hs hsO hg hL

/-! The defining equations of the flux and the divergence. -/

example (V : Fin 3 → E3 → ℂ) (c : E3) (R : ℝ) :
    fluxC V c R = ∫ n : sphere (0 : E3) 1, ((R ^ 2 : ℝ) : ℂ) *
      ∑ α, V α (c + R • (n : E3)) * (((n : E3) α : ℝ) : ℂ) ∂sphereMeasure :=
  rfl

example (V : Fin 3 → E3 → ℂ) (x : E3) :
    divergenceC V x = ∑ α, fderiv ℝ (V α) x (EuclideanSpace.single α 1) :=
  rfl

example (c : E3) (a b : ℝ) (p : E3) :
    radialCutoff c a b p = Real.smoothTransition (a * ‖p - c‖ ^ 2 + b) :=
  rfl

end ProjectAinos.SmoothGeometry.Sphere

end HalfSpace

section Uniqueness

open MeasureTheory Filter Set Metric Complex

open scoped Topology ContDiff Laplacian InnerProductSpace Real

namespace ProjectAinos.Electrodynamics.Diffraction

open ProjectAinos.SmoothGeometry.Sphere

local notation "E2" => EuclideanSpace ℝ (Fin 2)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (k R : ℝ) :
    ℂ :=
  waveSlope k R

example (k R : ℝ) :
    ℂ :=
  waveSlopeDeriv k R

example (k : ℝ) (α : Fin 3) (q : E3) :
    ℂ :=
  waveGrad k α q

example (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt (fun R : ℝ => cexp (I * k * R) / (4 * π * R)) (R * waveSlope k R) R :=
  hasDerivAt_waveProfile k hR

example (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt (waveSlope k) (waveSlopeDeriv k R) R :=
  hasDerivAt_waveSlope k hR

example (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    3 * waveSlope k R + R * waveSlopeDeriv k R + k ^ 2 * (cexp (I * k * R) / (4 * π * R)) = 0 :=
  waveSlope_radial k hR

example (k R : ℝ) :
    kernelProfile k R = -2 * waveSlope k R :=
  kernelProfile_eq_waveSlope k R

example (k : ℝ) {q : E3} (hq : q ≠ 0) :
    HasFDerivAt (sphericalWave k) ((‖q‖⁻¹ • innerSL ℝ q).smulRight (‖q‖ * waveSlope k ‖q‖)) q :=
  hasFDerivAt_sphericalWave k hq

example (k : ℝ) {q : E3} (hq : q ≠ 0) (v : E3) :
    fderiv ℝ (sphericalWave k) q v = waveSlope k ‖q‖ * ⟪q, v⟫_ℝ :=
  fderiv_sphericalWave_apply k hq v

example (k : ℝ) (α : Fin 3) {q : E3} (hq : q ≠ 0) :
    HasFDerivAt (waveGrad k α) (waveSlope k ‖q‖ • ofRealCLM.comp (EuclideanSpace.proj α) + ((q α :
      ℝ) : ℂ) • (‖q‖⁻¹ • innerSL ℝ q).smulRight (waveSlopeDeriv k ‖q‖)) q :=
  hasFDerivAt_waveGrad k α hq

example (k : ℝ) (α : Fin 3) {q : E3} (hq : q ≠ 0) (v : E3) :
    fderiv ℝ (waveGrad k α) q v = waveSlopeDeriv k ‖q‖ * ⟪q, v⟫_ℝ / ‖q‖ * q α + waveSlope k ‖q‖ * v
      α :=
  fderiv_waveGrad_apply k α hq v

example (k : ℝ) {q : E3} (hq : q ≠ 0) :
    ∑ α, fderiv ℝ (waveGrad k α) q (EuclideanSpace.single α 1) = -(k ^ 2 : ℂ) * sphericalWave k q :=
  sum_fderiv_waveGrad k hq

example (k : ℝ) {q : E3} (hq : q ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (sphericalWave k) q :=
  contDiffAt_sphericalWave k hq

example (k : ℝ) (α : Fin 3) {q : E3} (hq : q ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (waveGrad k α) q :=
  contDiffAt_waveGrad k α hq

example (k : ℝ) (q : E3) :
    ‖sphericalWave k q‖ = 1 / (4 * π * ‖q‖) :=
  norm_sphericalWave k q

example (ε : ℝ) (y : E3) :
    E3 :=
  imagePoint ε y

example (k ε : ℝ) (y p : E3) :
    ℂ :=
  greenD k ε y p

example (k ε : ℝ) (y : E3) (α : Fin 3) (p : E3) :
    ℂ :=
  greenGrad k ε y α p

example (k ε : ℝ) (y : E3) (u : E3 → ℂ) (α : Fin 3) (p : E3) :
    ℂ :=
  greenField k ε y u α p

example (ε : ℝ) (y : E3) :
    imagePoint ε y 2 = 2 * ε - y 2 :=
  imagePoint_apply_two ε y

example {ε : ℝ} {y p : E3} (h : p 2 ≠ 2 * ε - y 2) :
    p ≠ imagePoint ε y :=
  ne_imagePoint h

example {y p : E3} (h : p 2 ≠ y 2) :
    p ≠ y :=
  ne_of_apply_two_ne h

example (k : ℝ) {c p : E3} (hp : p ≠ c) (v : E3) :
    fderiv ℝ (fun p => sphericalWave k (p - c)) p v = waveSlope k ‖p - c‖ * ⟪p - c, v⟫_ℝ :=
  fderiv_sphericalWave_sub_apply k hp v

example (k : ℝ) {c p : E3} (hp : p ≠ c) :
    DifferentiableAt ℝ (fun p => sphericalWave k (p - c)) p :=
  differentiableAt_sphericalWave_sub k hp

example (k : ℝ) (α : Fin 3) {c p : E3} (hp : p ≠ c) :
    DifferentiableAt ℝ (fun p => waveGrad k α (p - c)) p :=
  differentiableAt_waveGrad_sub k α hp

example (k ε : ℝ) {y p : E3} (h1 : p ≠ y) (h2 : p ≠ imagePoint ε y) :
    DifferentiableAt ℝ (greenD k ε y) p :=
  differentiableAt_greenD k ε h1 h2

example (k ε : ℝ) (α : Fin 3) {y p : E3} (h1 : p ≠ y) (h2 : p ≠ imagePoint ε y) :
    DifferentiableAt ℝ (greenGrad k ε y α) p :=
  differentiableAt_greenGrad k ε α h1 h2

example (k ε : ℝ) {y p : E3} (h1 : p ≠ y) (h2 : p ≠ imagePoint ε y) (α : Fin 3) :
    fderiv ℝ (greenD k ε y) p (EuclideanSpace.single α 1) = greenGrad k ε y α p :=
  fderiv_greenD_single k ε h1 h2 α

example (k ε : ℝ) {y p : E3} (h1 : p ≠ y) (h2 : p ≠ imagePoint ε y) :
    ∑ α, fderiv ℝ (greenGrad k ε y α) p (EuclideanSpace.single α 1) =
      -(k ^ 2 : ℂ) * greenD k ε y p :=
  sum_fderiv_greenGrad k ε h1 h2

example (k ε : ℝ) {y p : E3} (h1 : p ≠ y) (h2 : p ≠ imagePoint ε y) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (greenD k ε y) p :=
  contDiffAt_greenD k ε h1 h2

example (k ε : ℝ) (α : Fin 3) {y p : E3} (h1 : p ≠ y) (h2 : p ≠ imagePoint ε y) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (greenGrad k ε y α) p :=
  contDiffAt_greenGrad k ε α h1 h2

example (k ε : ℝ) {y : E3} {u : E3 → ℂ} (α : Fin 3) {p : E3} (hu : ContDiffAt ℝ 2 u p) (h1 : p ≠ y)
    (h2 : p ≠ imagePoint ε y) :
    ContDiffAt ℝ 1 (greenField k ε y u α) p :=
  contDiffAt_greenField k ε α hu h1 h2

example (k ε : ℝ) {y : E3} {u : E3 → ℂ} {p : E3} (hu : ContDiffAt ℝ 2 u p)
    (hH : Δ u p + k ^ 2 * u p = 0) (h1 : p ≠ y) (h2 : p ≠ imagePoint ε y) :
    divergenceC (greenField k ε y u) p = 0 :=
  divergenceC_greenField k ε hu hH h1 h2

example (ε : ℝ) (y : E3) (x : E2) :
    ‖spacePoint x ε - imagePoint ε y‖ = ‖spacePoint x ε - y‖ :=
  norm_spacePoint_sub_imagePoint ε y x

example (k ε : ℝ) (y : E3) (x : E2) :
    greenD k ε y (spacePoint x ε) = 0 :=
  greenD_spacePoint k ε y x

example (k ε : ℝ) (y : E3) (x : E2) :
    greenGrad k ε y 2 (spacePoint x ε) = rayleighKernel k (y - spacePoint x ε) :=
  greenGrad_two_spacePoint k ε y x

example (a b : E3) :
    ⟪a, b⟫_ℝ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 :=
  inner_eq_three a b

example (u : E3 → ℂ) (x v : E3) :
    fderiv ℝ u x v = ∑ α, ((v α : ℝ) : ℂ) * fderiv ℝ u x (EuclideanSpace.single α 1) :=
  fderiv_apply_eq_sum_single u x v

example (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    ContinuousAt (waveSlope k) R :=
  continuousAt_waveSlope k hR

example (k ε : ℝ) (y : E3) (u : E3 → ℂ) (r : ℝ) (n : E3) :
    ℂ :=
  greenFluxIntegrand k ε y u r n

example (k ε : ℝ) (y : E3) (u : E3 → ℂ) {r : ℝ} (hr : 0 < r) :
    fluxC (greenField k ε y u) y r = ∫ n : sphere (0 : E3) 1, greenFluxIntegrand k ε y u r n
      ∂sphereMeasure :=
  fluxC_greenField_eq_integral k ε y u hr

example (k ε : ℝ) {y : E3} {u : E3 → ℂ} (hu : ContDiffOn ℝ 1 u upperHalfSpace) :
    ContinuousOn (Function.uncurry (greenFluxIntegrand k ε y u)) {x : ℝ × E3 | y + x.1 • x.2 ∈
      upperHalfSpace ∧ y + x.1 • x.2 ≠ imagePoint ε y} :=
  continuousOn_greenFluxIntegrand k ε hu

example (k ε : ℝ) {y : E3} {u : E3 → ℂ} (hu : ContDiffOn ℝ 1 u upperHalfSpace) (hy : 0 < y 2)
    (hyε : y 2 ≠ ε) :
    Tendsto (fun r => fluxC (greenField k ε y u) y r) (𝓝[>] 0) (𝓝 (-u y)) :=
  tendsto_fluxC_greenField k ε hu hy hyε

example (k ε : ℝ) {y : E3} {u : E3 → ℂ} (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) (hy : 0 < y 2) (hyε : y 2 ≠ ε) {R : ℝ}
    (hR : 0 < R) (hball : ∀ x : E3, ‖x‖ ≤ R → 0 < (y + x) 2 ∧ y + x ≠ imagePoint ε y) :
    fluxC (greenField k ε y u) y R = -u y :=
  fluxC_greenField_eq k ε hu hH hy hyε hR hball

example {c p : E3} (h : 2 * ‖c‖ ≤ ‖p‖) :
    ‖p‖ / 2 ≤ ‖p - c‖ :=
  half_le_norm_sub h

example (k : ℝ) {c p : E3} (h : 2 * ‖c‖ ≤ ‖p‖) (hp : 0 < ‖p‖) :
    ‖sphericalWave k (p - c)‖ ≤ 1 / (2 * π * ‖p‖) :=
  norm_sphericalWave_sub_le k h hp

example (k : ℝ) {c p : E3} (h : 2 * ‖c‖ ≤ ‖p‖) (hp : 0 < ‖p‖) :
    ‖waveSlope k ‖p - c‖ * ⟪p - c, p⟫_ℝ - I * k * ‖p‖ * sphericalWave k (p - c)‖ ≤ (|k| * ‖c‖ + 1) /
      (π * ‖p‖) :=
  norm_waveRadial_le k h hp

example (k ε : ℝ) (y : E3) (u : E3 → ℂ) (p : E3) :
    ∑ α, ((p α : ℝ) : ℂ) * greenField k ε y u α p = u p * (waveSlope k ‖p - y‖ * ⟪p - y, p⟫_ℝ -
      waveSlope k ‖p - imagePoint ε y‖ * ⟪p - imagePoint ε y, p⟫_ℝ) - greenD k ε y p * fderiv ℝ u p
      p :=
  sum_mul_greenField k ε y u p

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} {p : E3} {a C e : ℝ} (ha1 : ‖y‖ ≤ a)
    (ha2 : ‖imagePoint ε y‖ ≤ a) (hpa : 2 * a ≤ ‖p‖) (hp : 0 < ‖p‖) (hC : ‖p‖ * ‖u p‖ ≤ C)
    (he : ‖p‖ * ‖fderiv ℝ u p (‖p‖⁻¹ • p) - I * k * u p‖ ≤ e) :
    ‖∑ α, ((p α : ℝ) : ℂ) * greenField k ε y u α p‖ ≤ 2 * C * (|k| * a + 1) / (π * ‖p‖ ^ 2) + e / (π
      * ‖p‖) :=
  norm_sum_mul_greenField_le ha1 ha2 hpa hp hC he

example :
    Continuous fun p : E2 × ℝ => spacePoint p.1 p.2 :=
  continuous_spacePoint

example (x : E2) (z : ℝ) :
    ‖x‖ ≤ ‖spacePoint x z‖ :=
  norm_le_norm_spacePoint x z

example (y : E3) (δ : ℝ) :
    E3 → ℝ :=
  poleCutoff y δ

example (R : ℝ) :
    E3 → ℝ :=
  farCutoff R

example {y p : E3} {δ : ℝ} (hδ : 0 < δ) (h : ‖p - y‖ ≤ δ) :
    poleCutoff y δ p = 0 :=
  poleCutoff_eq_zero hδ h

example {y p : E3} {δ : ℝ} (hδ : 0 < δ) (h : 2 * δ ≤ ‖p - y‖) :
    poleCutoff y δ p = 1 :=
  poleCutoff_eq_one hδ h

example {y p : E3} {δ : ℝ} (hδ : 0 < δ) (h : ‖p - y‖ < δ ∨ 2 * δ ≤ ‖p - y‖) :
    fderiv ℝ (poleCutoff y δ) p = 0 :=
  fderiv_poleCutoff_eq_zero hδ h

example (R : ℝ) (p : E3) :
    farCutoff R p ∈ Icc 0 1 :=
  farCutoff_mem_Icc R p

example {p : E3} {R : ℝ} (hR : 0 < R) (h : ‖p‖ ≤ R) :
    farCutoff R p = 1 :=
  farCutoff_eq_one hR h

example {p : E3} {R : ℝ} (hR : 0 < R) (h : 2 * R ≤ ‖p‖) :
    farCutoff R p = 0 :=
  farCutoff_eq_zero hR h

example {p : E3} {R : ℝ} (hR : 0 < R) (h : ‖p‖ < R ∨ 2 * R < ‖p‖) :
    fderiv ℝ (farCutoff R) p = 0 :=
  fderiv_farCutoff_eq_zero hR h

example (R : ℝ) (p v : E3) :
    fderiv ℝ (farCutoff R) p v = deriv Real.smoothTransition (-1 / R ^ 2 * ‖p‖ ^ 2 + 2) * (-2 / R ^
      2) * ⟪p, v⟫_ℝ :=
  fderiv_farCutoff_apply R p v

example {y : E3} {x : E3} {r : ℝ} (hx : ‖x‖ ≤ r) :
    y 2 - r ≤ (y + x) 2 :=
  apply_two_ge_of_norm_le hx

example {y : E3} (p : E3) :
    y 2 - p 2 ≤ ‖p - y‖ :=
  sub_apply_two_le_norm p

example {y : E3} {ε : ℝ} {p : E3} (hεy : 2 * ε < y 2) (hε : 0 < ε) (hp : ε / 2 < p 2) :
    p ≠ imagePoint ε y :=
  ne_imagePoint_of_lt hεy hε hp

example (k ε : ℝ) (y : E3) (u : E3 → ℂ) (α : Fin 3) (p : E3) :
    ℂ :=
  poleField k ε y u α p

example (k ε : ℝ) (y : E3) (u : E3 → ℂ) (p : E3) :
    ℂ :=
  poleSource k ε y u p

example (ε : ℝ) :
    Set E3 :=
  openAbove ε

example (ε : ℝ) :
    IsOpen (openAbove ε) :=
  isOpen_openAbove ε

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hy : 0 < y 2) (α : Fin 3) {p : E3}
    (hp : ‖p - y‖ < y 2 / 8) :
    poleField k ε y u α =ᶠ[𝓝 p] fun _ => 0 :=
  poleField_eventuallyEq_zero hy α hp

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hu : ContDiffOn ℝ 2 u upperHalfSpace) (hy : 0 < y 2)
    (hε : 0 < ε) (hεy : 2 * ε < y 2) (α : Fin 3) :
    ContDiffOn ℝ 1 (poleField k ε y u α) (openAbove ε) :=
  contDiffOn_poleField hu hy hε hεy α

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hy : 0 < y 2) {p : E3}
    (h : ‖p - y‖ < y 2 / 8 ∨ 2 * (y 2 / 8) ≤ ‖p - y‖) :
    poleSource k ε y u p = 0 :=
  poleSource_eq_zero hy h

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) (hy : 0 < y 2) (hε : 0 < ε)
    (hεy : 2 * ε < y 2) {p : E3} (hp : p ∈ openAbove ε) :
    divergenceC (poleField k ε y u) p = poleSource k ε y u p :=
  divergenceC_poleField hu hH hy hε hεy hp

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hy : 0 < y 2) :
    fluxC (poleField k ε y u) y (2 * (y 2 / 8)) = fluxC (greenField k ε y u) y (2 * (y 2 / 8)) :=
  fluxC_poleField hy

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) (hy : 0 < y 2) (hε : 0 < ε)
    (hεy : 2 * ε < y 2) :
    ∫ p in {p : E3 | ε ≤ p 2}, poleSource k ε y u p = -u y :=
  integral_poleSource hu hH hy hε hεy

example (k ε : ℝ) (y : E3) (u : E3 → ℂ) (R : ℝ) (α : Fin 3) (p : E3) :
    ℂ :=
  cutField k ε y u R α p

example (k ε : ℝ) (y : E3) (u : E3 → ℂ) (R : ℝ) (p : E3) :
    ℂ :=
  farSource k ε y u R p

example {V : Fin 3 → E3 → ℂ} {O : Set E3} (hO : IsOpen O) (hV : ∀ α, ContDiffOn ℝ 1 (V α) O) :
    ContinuousOn (divergenceC V) O :=
  continuousOn_divergenceC hO hV

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hu : ContDiffOn ℝ 2 u upperHalfSpace) (hy : 0 < y 2)
    (hε : 0 < ε) (hεy : 2 * ε < y 2) (R : ℝ) (α : Fin 3) :
    ContDiffOn ℝ 1 (cutField k ε y u R α) (openAbove ε) :=
  contDiffOn_cutField hu hy hε hεy R α

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} {R : ℝ} (hR : 0 < R) (α : Fin 3) {p : E3}
    (h : 2 * R < ‖p‖) :
    cutField k ε y u R α p = 0 :=
  cutField_eq_zero hR α h

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} {R : ℝ} (hR : 0 < R) {p : E3} (h : ‖p‖ < R ∨ 2 * R < ‖p‖) :
    farSource k ε y u R p = 0 :=
  farSource_eq_zero hR h

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) (hy : 0 < y 2) (hε : 0 < ε)
    (hεy : 2 * ε < y 2) {R : ℝ} (hR : ‖y‖ + 2 * (y 2 / 8) < R) {p : E3} (hp : p ∈ openAbove ε) :
    divergenceC (cutField k ε y u R) p = poleSource k ε y u p + farSource k ε y u R p :=
  divergenceC_cutField hu hH hy hε hεy hR hp

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hu : ContDiffOn ℝ 2 u upperHalfSpace) (hy : 0 < y 2)
    (hε : 0 < ε) (hεy : 2 * ε < y 2) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (divergenceC (cutField k ε y u R)) {p : E3 | ε ≤ p 2} :=
  integrableOn_divergenceC_cutField hu hy hε hεy hR

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) (hy : 0 < y 2) (hε : 0 < ε)
    (hεy : 2 * ε < y 2) :
    IntegrableOn (poleSource k ε y u) {p : E3 | ε ≤ p 2} :=
  integrableOn_poleSource hu hH hy hε hεy

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} {R : ℝ} (hR : 0 < R) {S : ℝ}
    (hS : ∀ t, |deriv Real.smoothTransition t| ≤ S) (p : E3) :
    ‖farSource k ε y u R p‖ ≤ S * (2 / R ^ 2) * ‖∑ α, ((p α : ℝ) : ℂ) * greenField k ε y u α p‖ :=
  norm_farSource_le hR hS p

example (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure E3).real (closedBall 0 r) = r ^ 3 * (volume : Measure E3).real (ball 0 1) :=
  volume_real_closedBall r hr

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hrad : IsRadiating k u) (hε : 0 < ε) :
    Tendsto (fun R => ∫ p in {p : E3 | ε ≤ p 2}, farSource k ε y u R p) atTop (𝓝 0) :=
  tendsto_integral_farSource hrad hε

example {k ε : ℝ} {y : E3} {u : E3 → ℂ} (hy : 0 < y 2) (hεy : 2 * ε < y 2) (R : ℝ) (x : E2) :
    cutField k ε y u R 2 (spacePoint x ε) = (farCutoff R (spacePoint x ε) : ℂ) * (u (spacePoint x ε)
      * rayleighKernel k (y - spacePoint x ε)) :=
  cutField_two_spacePoint hy hεy R x

example (k : ℝ) {y : E3} {ε : ℝ} (hε0 : 0 ≤ ε) (hεy : ε ≤ y 2) {x : E2} (hx : 2 * ‖y‖ + 2 ≤ ‖x‖) :
    ‖rayleighKernel k (y - spacePoint x ε)‖ ≤ 2 * y 2 * (1 + |k|) / (π * (1 + ‖x‖) ^ 2) :=
  norm_rayleighKernel_sub_spacePoint_le k hε0 hεy hx

example :
    Integrable (fun x : E2 => ((1 + ‖x‖) ^ 3)⁻¹) :=
  integrable_inv_one_add_norm_pow_three

example {f : E2 → ℂ} (hf : Continuous f) {R₂ A : ℝ}
    (hA : ∀ x : E2, R₂ ≤ ‖x‖ → ‖f x‖ ≤ A * ((1 + ‖x‖) ^ 3)⁻¹) :
    Integrable f :=
  integrable_of_norm_le_inv_pow_three hf hA

example {k : ℝ} {u : E3 → ℂ} {C R₀ : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p : E3, 0 < p 2 → R₀ ≤ ‖p‖ → ‖p‖ * ‖u p‖ ≤ C) {y : E3} {ε : ℝ} (hε : 0 < ε)
    (hεy : ε ≤ y 2) {x : E2} (hx : max (max R₀ 1) (2 * ‖y‖ + 2) ≤ ‖x‖) :
    ‖u (spacePoint x ε) * rayleighKernel k (y - spacePoint x ε)‖ ≤ 4 * C * y 2 * (1 + |k|) / π * ((1
      + ‖x‖) ^ 3)⁻¹ :=
  norm_boundaryIntegrand_le hC0 hC hε hεy hx

example {k : ℝ} {u : E3 → ℂ} (hu : ContinuousOn u upperHalfSpace) {y : E3} {ε : ℝ} (hε : 0 < ε)
    (hεy : ε < y 2) :
    Continuous fun x : E2 => u (spacePoint x ε) * rayleighKernel k (y - spacePoint x ε) :=
  continuous_boundaryIntegrand hu hε hεy

example {k : ℝ} {u : E3 → ℂ} (hu : ContinuousOn u upperHalfSpace) (hrad : IsRadiating k u) {y : E3}
    {ε : ℝ} (hε : 0 < ε) (hεy : ε < y 2) :
    Integrable fun x : E2 => u (spacePoint x ε) * rayleighKernel k (y - spacePoint x ε) :=
  integrable_boundaryIntegrand hu hrad hε hεy

example {k : ℝ} {u : E3 → ℂ} (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) (hrad : IsRadiating k u) {y : E3}
    (hy : 0 < y 2) {ε : ℝ} (hε : 0 < ε) (hεy : 2 * ε < y 2) :
    u y = ∫ x : E2, u (spacePoint x ε) * rayleighKernel k (y - spacePoint x ε) :=
  eq_integral_spacePoint hu hH hrad hy hε hεy

example (p : E3) :
    E2 :=
  planeCoord p

example (p : E3) :
    planeCoord p 0 = p 0 :=
  planeCoord_apply_zero p

example (p : E3) :
    planeCoord p 1 = p 1 :=
  planeCoord_apply_one p

example (p : E3) :
    spacePoint (planeCoord p) (p 2) = p :=
  spacePoint_planeCoord p

example (x : E2) :
    planeCoord (planePoint x) = x :=
  planeCoord_planePoint x

example (x : E2) (z : ℝ) :
    planeCoord (spacePoint x z) = x :=
  planeCoord_spacePoint x z

example (x : E2) :
    spacePoint x 0 = planePoint x :=
  spacePoint_zero x

example :
    Continuous planeCoord :=
  continuous_planeCoord

example (p : E3) (x : E2) :
    ‖planeCoord p - x‖ ≤ ‖p - planePoint x‖ :=
  norm_planeCoord_sub_le p x

example (k : ℝ) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) (x : E2) :
    Tendsto (apertureField k u₀) (𝓝[upperHalfSpace] (planePoint x)) (𝓝 (u₀ x)) :=
  tendsto_apertureField_nhdsWithin k hc hs x

example (f : E3 → ℂ) (g : E2 → ℂ) (p : E3) :
    ℂ :=
  boundaryExtension f g p

example {f : E3 → ℂ} {g : E2 → ℂ} (hf : ContinuousOn f upperHalfSpace) (hg : Continuous g)
    (hb : ∀ x : E2, Tendsto f (𝓝[upperHalfSpace] (planePoint x)) (𝓝 (g x))) :
    ContinuousOn (boundaryExtension f g) {p : E3 | 0 ≤ p 2} :=
  continuousOn_boundaryExtension hf hg hb

example (k : ℝ) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) :
    ContinuousOn (boundaryExtension (apertureField k u₀) u₀) {p : E3 | 0 ≤ p 2} :=
  continuousOn_apertureFieldExt k hc hs

example (x : E2) :
    Tendsto (fun ε : ℝ => spacePoint x ε) (𝓝[>] 0) (𝓝[upperHalfSpace] (planePoint x)) :=
  tendsto_spacePoint_nhdsWithin x

example (x : E2) {z : ℝ} (hz : 0 ≤ z) :
    ‖spacePoint x z‖ ≤ ‖x‖ + z :=
  norm_spacePoint_le x hz

example {k : ℝ} {u₀ : E2 → ℂ} (hu₀ : Continuous u₀) {u : E3 → ℂ}
    (hu : ContDiffOn ℝ 2 u upperHalfSpace) (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0)
    (hb : ∀ x : E2, Tendsto u (𝓝[upperHalfSpace] (planePoint x)) (𝓝 (u₀ x)))
    (hrad : IsRadiating k u) {y : E3} (hy : 0 < y 2) :
    u y = apertureField k u₀ y :=
  eq_apertureField hu₀ hu hH hb hrad hy

example (k : ℝ) (u₀ : E2 → ℂ) (u : E3 → ℂ) :
    Prop :=
  IsRadiatingDirichletSolution k u₀ u

example {k : ℝ} (hk : 0 ≤ k) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) :
    IsRadiatingDirichletSolution k u₀ (apertureField k u₀) :=
  isRadiatingDirichletSolution_apertureField hk hc hs

example {k : ℝ} {u₀ : E2 → ℂ} (hu₀ : Continuous u₀) {u : E3 → ℂ}
    (h : IsRadiatingDirichletSolution k u₀ u) :
    EqOn u (apertureField k u₀) upperHalfSpace :=
  IsRadiatingDirichletSolution.eqOn_apertureField hu₀ h

example {k : ℝ} {u₀ : E2 → ℂ} (hu₀ : Continuous u₀) {u v : E3 → ℂ}
    (hu : IsRadiatingDirichletSolution k u₀ u) (hv : IsRadiatingDirichletSolution k u₀ v) :
    EqOn u v upperHalfSpace :=
  IsRadiatingDirichletSolution.eqOn hu₀ hu hv

example {k : ℝ} (hk : 0 ≤ k) {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀) :
    IsRadiatingDirichletSolution k u₀ (apertureField k u₀) ∧ ∀ u : E3 → ℂ,
      IsRadiatingDirichletSolution k u₀ u → EqOn u (apertureField k u₀) upperHalfSpace :=
  apertureField_unique hk hc hs

example (k : ℝ) :
    apertureField k (fun _ => 0) = fun _ => 0 :=
  apertureField_zero k

example {k : ℝ} {u : E3 → ℂ} (hu : ContDiffOn ℝ 2 u upperHalfSpace)
    (hH : ∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0)
    (hb : ∀ x : E2, Tendsto u (𝓝[upperHalfSpace] (planePoint x)) (𝓝 0)) (hrad : IsRadiating k u)
    {p : E3} (hp : 0 < p 2) :
    u p = 0 :=
  eq_zero_of_isRadiating hu hH hb hrad hp

example {k : ℝ} (hk : 0 ≤ k) :
    IsRadiatingDirichletSolution k apertureBump (apertureField k apertureBump) :=
  isRadiatingDirichletSolution_apertureBump hk

example {k : ℝ} {u : E3 → ℂ} (h : IsRadiatingDirichletSolution k apertureBump u) :
    EqOn u (apertureField k apertureBump) upperHalfSpace :=
  eqOn_apertureField_apertureBump h

example :
    E2 →L[ℝ] E3 :=
  planePointL

example (y : E2) :
    planePointL y = planePoint y :=
  planePointL_apply y

example (k : ℝ) {u₀ : E2 → ℂ} (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀) {p : E3}
    (hp : 0 < p 2) (w : E2) :
    fderiv ℝ (apertureField k u₀) p (planePoint w) = apertureField k (fun y => fderiv ℝ u₀ y w) p :=
  fderiv_apertureField_planePoint k hd hs hp w

example (i : Fin 2) :
    planePoint (EuclideanSpace.single i 1) = EuclideanSpace.single (Fin.castSucc i) 1 :=
  planePoint_single i

example (i : Fin 3) (f : E3 → ℂ) :
    E3 → ℂ :=
  partialC i f

example (V : Fin 3 → E3 → ℂ) :
    Fin 3 → E3 → ℂ :=
  curlC V

example (k : ℝ) (E B : Fin 3 → E3 → ℂ) (U : Set E3) :
    Prop :=
  IsTimeHarmonicMaxwell k E B U

example (i : Fin 3) :
    partialC i (fun _ => (0 : ℂ)) = fun _ => 0 :=
  partialC_zero i

example (i : Fin 3) (f : E3 → ℂ) :
    partialC i (fun p => -f p) = fun p => -partialC i f p :=
  partialC_neg i f

example (i : Fin 3) {f g : E3 → ℂ} {p : E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) :
    partialC i (fun q => f q - g q) p = partialC i f p - partialC i g p :=
  partialC_sub_apply i hf hg

example (i : Fin 3) (c : ℂ) {f : E3 → ℂ} {p : E3} (hf : DifferentiableAt ℝ f p) :
    partialC i (fun q => c * f q) p = c * partialC i f p :=
  partialC_const_mul_apply i c hf

example (i : Fin 3) {f g : E3 → ℂ} {p : E3} (h : f =ᶠ[𝓝 p] g) :
    partialC i f p = partialC i g p :=
  partialC_congr i h

example (i : Fin 3) {f g : E3 → ℂ} {p : E3} (h : f =ᶠ[𝓝 p] g) :
    partialC i f =ᶠ[𝓝 p] partialC i g :=
  partialC_eventuallyEq i h

example {f : E3 → ℂ} {p : E3} (hf : ContDiffAt ℝ 2 f p) (a b : Fin 3) :
    partialC a (partialC b f) p = partialC b (partialC a f) p :=
  partialC_comm hf a b

example {f : E3 → ℂ} {U : Set E3} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (i : Fin 3) :
    ContDiffOn ℝ ∞ (partialC i f) U :=
  contDiffOn_partialC hU hf i

example (k : ℝ) (u₀ : E2 → ℂ) :
    Fin 3 → E3 → ℂ :=
  apertureE k u₀

example (k : ℝ) (u₀ : E2 → ℂ) :
    Fin 3 → E3 → ℂ :=
  apertureB k u₀

example (k : ℝ) (u₀ : E2 → ℂ) :
    apertureE k u₀ = curlC ![fun _ => 0, fun _ => 0, apertureField k u₀] :=
  apertureE_eq_curlC k u₀

example (k : ℝ) (u₀ : E2 → ℂ) :
    curlC (apertureE k u₀) 0 = partialC 2 (partialC 0 (apertureField k u₀)) :=
  curlC_apertureE_zero k u₀

example (k : ℝ) (u₀ : E2 → ℂ) :
    curlC (apertureE k u₀) 1 = partialC 2 (partialC 1 (apertureField k u₀)) :=
  curlC_apertureE_one k u₀

example (k : ℝ) (u₀ : E2 → ℂ) :
    curlC (apertureE k u₀) 2 = fun p => -partialC 0 (partialC 0 (apertureField k u₀)) p - partialC 1
      (partialC 1 (apertureField k u₀)) p :=
  curlC_apertureE_two k u₀

example (k : ℝ) {u₀ : E2 → ℂ} (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀) (i : Fin 2)
    {p : E3} (hp : 0 < p 2) :
    ∑ j, partialC j (partialC j (partialC (Fin.castSucc i) (apertureField k u₀))) p = -(k ^ 2 : ℂ) *
      partialC (Fin.castSucc i) (apertureField k u₀) p :=
  sum_partialC_tangential k hd hs i hp

example {k : ℝ} (hk : k ≠ 0) {u₀ : E2 → ℂ} (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀) :
    IsTimeHarmonicMaxwell k (apertureE k u₀) (apertureB k u₀) upperHalfSpace :=
  maxwell_aperture hk hd hs

example {k : ℝ} {f g : E3 → ℂ} (hf : IsRadiating k f) (h : EqOn f g upperHalfSpace) :
    IsRadiating k g :=
  IsRadiating.congr hf h

example {k : ℝ} {f : E3 → ℂ} (hf : IsRadiating k f) :
    IsRadiating k fun p => -f p :=
  IsRadiating.neg hf

example (k : ℝ) :
    IsRadiating k fun _ => (0 : ℂ) :=
  isRadiating_zero k

example {u₀ : E2 → ℂ} (hd : ContDiff ℝ 1 u₀) (w : E2) :
    Continuous fun y => fderiv ℝ u₀ y w :=
  continuous_fderiv_apply hd w

example {u₀ : E2 → ℂ} (hs : HasCompactSupport u₀) (w : E2) :
    HasCompactSupport fun y => fderiv ℝ u₀ y w :=
  hasCompactSupport_fderiv_apply hs w

example {u₀ : E2 → ℂ} (k : ℝ) (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀) :
    EqOn (apertureE k u₀ 0) (apertureField k fun y => fderiv ℝ u₀ y (EuclideanSpace.single 1 1))
      upperHalfSpace :=
  apertureE_zero_eqOn k hd hs

example {u₀ : E2 → ℂ} (k : ℝ) (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀) :
    EqOn (apertureE k u₀ 1) (fun p => -apertureField k (fun y => fderiv ℝ u₀ y
      (EuclideanSpace.single 0 1)) p) upperHalfSpace :=
  apertureE_one_eqOn k hd hs

example {u₀ : E2 → ℂ} {k : ℝ} (hk : 0 ≤ k) (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀)
    (α : Fin 3) :
    IsRadiating k (apertureE k u₀ α) :=
  isRadiating_apertureE hk hd hs α

example {u₀ : E2 → ℂ} (k : ℝ) (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀) (x : E2) :
    Tendsto (apertureE k u₀ 0) (𝓝[upperHalfSpace] (planePoint x)) (𝓝 (fderiv ℝ u₀ x
      (EuclideanSpace.single 1 1))) :=
  tendsto_apertureE_zero k hd hs x

example {u₀ : E2 → ℂ} (k : ℝ) (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀) (x : E2) :
    Tendsto (apertureE k u₀ 1) (𝓝[upperHalfSpace] (planePoint x)) (𝓝 (-fderiv ℝ u₀ x
      (EuclideanSpace.single 0 1))) :=
  tendsto_apertureE_one k hd hs x

example {u₀ : E2 → ℂ} (k : ℝ) (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀) {x : E2}
    (hx : x ∉ tsupport u₀) (α : Fin 3) :
    Tendsto (apertureE k u₀ α) (𝓝[upperHalfSpace] (planePoint x)) (𝓝 0) :=
  tendsto_apertureE_screen k hd hs hx α

example {k : ℝ} (hk : k ≠ 0) :
    IsTimeHarmonicMaxwell k (apertureE k apertureBump) (apertureB k apertureBump) upperHalfSpace :=
  maxwell_apertureBump hk

example {k : ℝ} (hk : 0 ≤ k) (α : Fin 3) :
    IsRadiating k (apertureE k apertureBump α) :=
  isRadiating_apertureE_apertureBump hk α

example (k : ℝ) {x : E2} (hx : 1 < ‖x‖) (α : Fin 3) :
    Tendsto (apertureE k apertureBump α) (𝓝[upperHalfSpace] (planePoint x)) (𝓝 0) :=
  tendsto_apertureE_apertureBump_screen k hx α

example :
    ∃ x : E2, fderiv ℝ apertureBump x (EuclideanSpace.single 1 1) ≠ 0 :=
  exists_fderiv_apertureBump_ne_zero

example (k : ℝ) :
    ∃ x : E2, ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (apertureE k apertureBump 0) (𝓝[upperHalfSpace] (planePoint x)) (𝓝 c) :=
  exists_tendsto_apertureE_apertureBump_ne_zero k

/-! The defining equations of the main objects. -/

example (ε : ℝ) (y : E3) : imagePoint ε y = !₂[y 0, y 1, 2 * ε - y 2] :=
  rfl

example (k ε : ℝ) (y p : E3) :
    greenD k ε y p = sphericalWave k (p - y) - sphericalWave k (p - imagePoint ε y) :=
  rfl

example (k ε : ℝ) (y : E3) (u : E3 → ℂ) (α : Fin 3) (p : E3) :
    greenField k ε y u α p =
      u p * greenGrad k ε y α p - greenD k ε y p * fderiv ℝ u p (EuclideanSpace.single α 1) :=
  rfl

example (k : ℝ) (u₀ : E2 → ℂ) (u : E3 → ℂ) :
    IsRadiatingDirichletSolution k u₀ u ↔
      ContDiffOn ℝ 2 u upperHalfSpace ∧ (∀ p : E3, 0 < p 2 → Δ u p + k ^ 2 * u p = 0) ∧
        (∀ x : E2, Tendsto u (𝓝[upperHalfSpace] (planePoint x)) (𝓝 (u₀ x))) ∧
          IsRadiating k u :=
  Iff.rfl

example (i : Fin 3) (f : E3 → ℂ) (p : E3) :
    partialC i f p = fderiv ℝ f p (EuclideanSpace.single i 1) :=
  rfl

example (V : Fin 3 → E3 → ℂ) (p : E3) :
    curlC V 0 p = partialC 1 (V 2) p - partialC 2 (V 1) p ∧
      curlC V 1 p = partialC 2 (V 0) p - partialC 0 (V 2) p ∧
        curlC V 2 p = partialC 0 (V 1) p - partialC 1 (V 0) p :=
  ⟨rfl, rfl, rfl⟩

example (k : ℝ) (E B : Fin 3 → E3 → ℂ) (U : Set E3) :
    IsTimeHarmonicMaxwell k E B U ↔
      ∀ p ∈ U, (∀ α, curlC E α p = I * k * B α p) ∧ (∀ α, curlC B α p = -(I * k) * E α p) ∧
        divergenceC E p = 0 ∧ divergenceC B p = 0 :=
  Iff.rfl

example (k : ℝ) (u₀ : E2 → ℂ) :
    apertureE k u₀ = ![partialC 1 (apertureField k u₀),
      fun p => -partialC 0 (apertureField k u₀) p, fun _ => 0] :=
  rfl

example (k : ℝ) (u₀ : E2 → ℂ) (α : Fin 3) (p : E3) :
    apertureB k u₀ α p = (I * k)⁻¹ * curlC (apertureE k u₀) α p :=
  rfl

end ProjectAinos.Electrodynamics.Diffraction

end Uniqueness
