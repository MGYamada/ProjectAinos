/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Diffraction.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic

/-!
# Diffraction: one Maxwell polarization of the aperture field

For aperture data `u₀` of class `C¹` with compact support and its outgoing scalar field
`u = apertureField k u₀`, the field `E = curl(0, 0, u) = (∂_y u, −∂_x u, 0)` (`apertureE`) and
`B = curl E/(ik)` (`apertureB`) are a time-harmonic solution of Maxwell's equations in vacuum
behind the screen (units `c = ε₀ = μ₀ = 1`, time dependence `e^{−ikt}`): `maxwell_aperture`,
with the predicate `IsTimeHarmonicMaxwell` (`curl E = ikB`, `curl B = −ikE`, `div E = div B = 0`;
with the time dependence `e^{−ikt}` the time derivative is the multiplication by `−ik`, so these
are Faraday's law `curl E = −∂_t B`, the Ampère–Maxwell law `curl B = ∂_t E` and Gauss's laws for
the fields `E e^{−ikt}`, `B e^{−ikt}`).

* `fderiv_apertureField_planePoint`: **tangential derivatives pass to the data**,
  `∂_w u = apertureField k (∂_w u₀)` for `w` in the plane, by integration by parts on the plane;
  so the components of `E` are aperture fields (`apertureE_zero_eqOn`, `apertureE_one_eqOn`).
* `isRadiating_apertureE`: every component of `E` satisfies the radiation condition.
* `tendsto_apertureE_zero`, `tendsto_apertureE_one`: **the boundary condition**: the tangential
  trace of `E` on the plane is `(∂_y u₀, −∂_x u₀)`, determined by the aperture data, and
  `tendsto_apertureE_screen`: it vanishes off the support of `u₀`, the condition `n × E = 0` of a
  perfectly conducting screen.
* The smooth aperture is an instance (`maxwell_apertureBump`), with a nonzero tangential trace
  (`exists_tendsto_apertureE_apertureBump_ne_zero`).

Not proved: the screen problem that determines the aperture trace from an incident field, which
needs traces in `H(curl)` and edge conditions, and the error of the scalar approximation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology ContDiff Laplacian InnerProductSpace Real

namespace ProjectAinos.Electrodynamics.Diffraction

open ProjectAinos.SmoothGeometry.Sphere

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Tangential derivatives of the aperture field -/

/-- The embedding of the plane as a continuous linear map. -/
def planePointL : E2 →L[ℝ] E3 :=
  LinearMap.toContinuousLinearMap
    { toFun := planePoint
      map_add' := fun a b => by ext i; fin_cases i <;> simp [planePoint]
      map_smul' := fun c a => by ext i; fin_cases i <;> simp [planePoint] }

@[simp] theorem planePointL_apply (y : E2) : planePointL y = planePoint y := rfl

/-- **Tangential derivatives pass to the data**: for data of class `C¹` with compact support and
a direction `w` of the plane, `∂_w u = apertureField k (∂_w u₀)` on `z > 0`. The kernel depends on
`p − (y, 0)`, so `∂_w` in `p` is `−∂_w` in `y`, which integration by parts moves onto `u₀`. -/
theorem fderiv_apertureField_planePoint (k : ℝ) {u₀ : E2 → ℂ} (hd : ContDiff ℝ 1 u₀)
    (hs : HasCompactSupport u₀) {p : E3} (hp : 0 < p 2) (w : E2) :
    fderiv ℝ (apertureField k u₀) p (planePoint w) =
      apertureField k (fun y => fderiv ℝ u₀ y w) p := by
  have hc : Continuous u₀ := hd.continuous
  have hK1 : ContDiffOn ℝ 1 (rayleighKernel k) upperHalfSpace := contDiffOn_rayleighKernel k
  have hq (y : E2) : p - planePoint y ≠ 0 := sub_planePoint_ne_zero hp y
  have hg (y : E2) : HasFDerivAt (fun y => rayleighKernel k (p - planePoint y))
      (-(fderiv ℝ (rayleighKernel k) (p - planePoint y)).comp planePointL) y := by
    have hK : DifferentiableAt ℝ (rayleighKernel k) (p - planePoint y) :=
      (contDiffAt_rayleighKernel k (n := 1) (hq y)).differentiableAt one_ne_zero
    have hl : HasFDerivAt (fun y : E2 => p - planePoint y) (-planePointL) y := by
      have := (hasFDerivAt_const p y).fun_sub planePointL.hasFDerivAt
      exact this.congr_fderiv (by simp)
    have h := hK.hasFDerivAt.comp y hl
    rw [ContinuousLinearMap.comp_neg] at h
    exact h
  have hgw (y : E2) : fderiv ℝ (fun y => rayleighKernel k (p - planePoint y)) y w =
      -fderiv ℝ (rayleighKernel k) (p - planePoint y) (planePoint w) := by
    rw [(hg y).fderiv]
    simp
  have hcd : Continuous fun y => fderiv ℝ u₀ y w :=
    (hd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsd : HasCompactSupport fun y => fderiv ℝ u₀ y w :=
    (hs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E2 →L[ℝ] ℂ => L w) (by simp)
  have hKw : ContinuousOn (fun q => fderiv ℝ (rayleighKernel k) q (planePoint w))
      upperHalfSpace :=
    (hK1.continuousOn_fderiv_of_isOpen isOpen_upperHalfSpace le_rfl).clm_apply continuousOn_const
  have hI1 : Integrable fun y => fderiv ℝ u₀ y w * rayleighKernel k (p - planePoint y) := by
    simpa [smul_eq_mul] using integrable_planeIntegrand hcd hsd hK1.continuousOn hp
  have hI2 : Integrable fun y => u₀ y *
      fderiv ℝ (fun y => rayleighKernel k (p - planePoint y)) y w := by
    have := (integrable_planeIntegrand hc hs hKw hp).neg
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp [hgw, smul_eq_mul]
  have hI3 : Integrable fun y => u₀ y * rayleighKernel k (p - planePoint y) := by
    simpa [smul_eq_mul] using integrable_planeIntegrand hc hs hK1.continuousOn hp
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hI1 hI2 hI3
    (fun y _ => (hd.differentiable one_ne_zero) y) (fun y _ => (hg y).differentiableAt)
  rw [apertureField_eq_planeIntegral, fderiv_planeIntegral_apply hc hs hK1 hp]
  unfold planeIntegral
  simp only [hgw, mul_neg, integral_neg, neg_inj] at hibp
  simp only [smul_eq_mul]
  rw [hibp]
  rfl

/-- The axes of the plane are the first two axes of space. -/
@[simp] theorem planePoint_single (i : Fin 2) :
    planePoint (EuclideanSpace.single i 1) = EuclideanSpace.single (Fin.castSucc i) 1 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [planePoint]

/-! ### Complex vector calculus -/

/-- The partial derivative `∂_i f` of a complex function on space. -/
def partialC (i : Fin 3) (f : E3 → ℂ) : E3 → ℂ :=
  fun p => fderiv ℝ f p (EuclideanSpace.single i 1)

/-- The curl of a complex vector field. -/
def curlC (V : Fin 3 → E3 → ℂ) : Fin 3 → E3 → ℂ :=
  ![fun p => partialC 1 (V 2) p - partialC 2 (V 1) p,
    fun p => partialC 2 (V 0) p - partialC 0 (V 2) p,
    fun p => partialC 0 (V 1) p - partialC 1 (V 0) p]

/-- **The time-harmonic Maxwell equations in vacuum** on `U`, in the units `c = ε₀ = μ₀ = 1` and
with the time dependence `e^{−ikt}`: `curl E = ikB`, `curl B = −ikE`, `div E = 0`, `div B = 0`.
The time derivative of `E e^{−ikt}` is `−ik E e^{−ikt}`, so these are Faraday's law
`curl E = −∂_t B`, the Ampère–Maxwell law `curl B = ∂_t E` and Gauss's laws for the fields
`E e^{−ikt}` and `B e^{−ikt}`. -/
def IsTimeHarmonicMaxwell (k : ℝ) (E B : Fin 3 → E3 → ℂ) (U : Set E3) : Prop :=
  ∀ p ∈ U, (∀ α, curlC E α p = I * k * B α p) ∧ (∀ α, curlC B α p = -(I * k) * E α p) ∧
    divergenceC E p = 0 ∧ divergenceC B p = 0

@[simp] theorem partialC_zero (i : Fin 3) : partialC i (fun _ => (0 : ℂ)) = fun _ => 0 := by
  funext p
  simp [partialC]

theorem partialC_neg (i : Fin 3) (f : E3 → ℂ) :
    partialC i (fun p => -f p) = fun p => -partialC i f p := by
  funext p
  simp [partialC, fderiv_fun_neg]

theorem partialC_sub_apply (i : Fin 3) {f g : E3 → ℂ} {p : E3} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) :
    partialC i (fun q => f q - g q) p = partialC i f p - partialC i g p := by
  simp [partialC, fderiv_fun_sub hf hg]

theorem partialC_const_mul_apply (i : Fin 3) (c : ℂ) {f : E3 → ℂ} {p : E3}
    (hf : DifferentiableAt ℝ f p) : partialC i (fun q => c * f q) p = c * partialC i f p := by
  simp [partialC, fderiv_const_mul hf]

/-- The partial derivative depends only on the germ. -/
theorem partialC_congr (i : Fin 3) {f g : E3 → ℂ} {p : E3} (h : f =ᶠ[𝓝 p] g) :
    partialC i f p = partialC i g p := by
  simp [partialC, h.fderiv_eq]

/-- Eventually equal functions have eventually equal partial derivatives. -/
theorem partialC_eventuallyEq (i : Fin 3) {f g : E3 → ℂ} {p : E3} (h : f =ᶠ[𝓝 p] g) :
    partialC i f =ᶠ[𝓝 p] partialC i g :=
  h.fderiv.mono fun q hq => by
    simp only [partialC]
    rw [hq]

/-- **Mixed partial derivatives commute** for a function of class `C²`. -/
theorem partialC_comm {f : E3 → ℂ} {p : E3} (hf : ContDiffAt ℝ 2 f p) (a b : Fin 3) :
    partialC a (partialC b f) p = partialC b (partialC a f) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h (a b : Fin 3) : partialC a (partialC b f) p =
      fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    show fderiv ℝ (fun q => fderiv ℝ f q (EuclideanSpace.single b 1)) p
      (EuclideanSpace.single a 1) = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [h, h]
  exact hf.isSymmSndFDerivAt (by simp) _ _

/-- A partial derivative of a smooth function on an open set is smooth there. -/
theorem contDiffOn_partialC {f : E3 → ℂ} {U : Set E3} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (i : Fin 3) : ContDiffOn ℝ ∞ (partialC i f) U :=
  (hf.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const

/-! ### The fields of one polarization -/

/-- **The electric field** `E = curl(0, 0, u) = (∂_y u, −∂_x u, 0)` of the aperture field. -/
def apertureE (k : ℝ) (u₀ : E2 → ℂ) : Fin 3 → E3 → ℂ :=
  ![partialC 1 (apertureField k u₀), fun p => -partialC 0 (apertureField k u₀) p, fun _ => 0]

/-- **The magnetic field** `B = curl E/(ik)`. -/
def apertureB (k : ℝ) (u₀ : E2 → ℂ) : Fin 3 → E3 → ℂ :=
  fun α p => (I * k)⁻¹ * curlC (apertureE k u₀) α p

/-- The electric field is the curl of the field `(0, 0, u)`. -/
theorem apertureE_eq_curlC (k : ℝ) (u₀ : E2 → ℂ) :
    apertureE k u₀ = curlC ![fun _ => 0, fun _ => 0, apertureField k u₀] := by
  funext α p
  fin_cases α <;> simp [apertureE, curlC]

theorem curlC_apertureE_zero (k : ℝ) (u₀ : E2 → ℂ) :
    curlC (apertureE k u₀) 0 = partialC 2 (partialC 0 (apertureField k u₀)) := by
  funext p
  simp [curlC, apertureE, partialC_neg]

theorem curlC_apertureE_one (k : ℝ) (u₀ : E2 → ℂ) :
    curlC (apertureE k u₀) 1 = partialC 2 (partialC 1 (apertureField k u₀)) := by
  funext p
  simp [curlC, apertureE]

theorem curlC_apertureE_two (k : ℝ) (u₀ : E2 → ℂ) :
    curlC (apertureE k u₀) 2 = fun p => -partialC 0 (partialC 0 (apertureField k u₀)) p -
      partialC 1 (partialC 1 (apertureField k u₀)) p := by
  funext p
  simp [curlC, apertureE, partialC_neg]

/-- **The tangential derivatives solve the Helmholtz equation**: `∂_w u` is the aperture field of
`∂_w u₀`. -/
theorem sum_partialC_tangential (k : ℝ) {u₀ : E2 → ℂ} (hd : ContDiff ℝ 1 u₀)
    (hs : HasCompactSupport u₀) (i : Fin 2) {p : E3} (hp : 0 < p 2) :
    ∑ j, partialC j (partialC j (partialC (Fin.castSucc i) (apertureField k u₀))) p =
      -(k ^ 2 : ℂ) * partialC (Fin.castSucc i) (apertureField k u₀) p := by
  set w : E2 := EuclideanSpace.single i 1
  set d : E2 → ℂ := fun y => fderiv ℝ u₀ y w with hddef
  have hdc : Continuous d := (hd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hds : HasCompactSupport d :=
    (hs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E2 →L[ℝ] ℂ => L w) (by simp)
  have hev : partialC (Fin.castSucc i) (apertureField k u₀) =ᶠ[𝓝 p] apertureField k d := by
    filter_upwards [isOpen_upperHalfSpace.mem_nhds hp] with q hq
    simp only [partialC, ← planePoint_single]
    exact fderiv_apertureField_planePoint k hd hs hq w
  have h2 (j : Fin 3) : partialC j (partialC j (partialC (Fin.castSucc i) (apertureField k u₀))) p
      = partialC j (partialC j (apertureField k d)) p :=
    partialC_congr j (partialC_eventuallyEq j hev)
  have hC : ContDiffAt ℝ 2 (apertureField k d) p :=
    ((contDiffOn_apertureField k hdc hds).contDiffAt
      (isOpen_upperHalfSpace.mem_nhds hp)).of_le (by simp)
  have hΔ := laplacian_eq_sum_fderiv hC
  have hH := helmholtz_apertureField k hdc hds hp
  simp only [h2, hev.eq_of_nhds]
  rw [show ∑ j, partialC j (partialC j (apertureField k d)) p = Δ (apertureField k d) p from
    hΔ.symm]
  linear_combination hH

/-- **One Maxwell polarization of the aperture field**: for data of class `C¹` with compact support
and `k ≠ 0`, the fields `E = curl(0, 0, u)` and `B = curl E/(ik)` solve the time-harmonic Maxwell
equations in vacuum on `z > 0`. `div E = 0` and `div B = 0` are the symmetry of second
derivatives, and `curl B = (∇ div E − ΔE)/(ik) = −ikE` because the components of `E` are aperture
fields of the derivatives of the data and solve the Helmholtz equation. -/
theorem maxwell_aperture {k : ℝ} (hk : k ≠ 0) {u₀ : E2 → ℂ} (hd : ContDiff ℝ 1 u₀)
    (hs : HasCompactSupport u₀) :
    IsTimeHarmonicMaxwell k (apertureE k u₀) (apertureB k u₀) upperHalfSpace := by
  intro p hp
  have hU := isOpen_upperHalfSpace
  set u := apertureField k u₀ with hudef
  have hu : ContDiffOn ℝ ∞ u upperHalfSpace := contDiffOn_apertureField k hd.continuous hs
  have hD (a : Fin 3) : ContDiffOn ℝ ∞ (partialC a u) upperHalfSpace :=
    contDiffOn_partialC hU hu a
  have hDD (a b : Fin 3) : ContDiffOn ℝ ∞ (partialC a (partialC b u)) upperHalfSpace :=
    contDiffOn_partialC hU (hD b) a
  have hat {f : E3 → ℂ} (hf : ContDiffOn ℝ ∞ f upperHalfSpace) : ContDiffAt ℝ ∞ f p :=
    hf.contDiffAt (hU.mem_nhds hp)
  have hdiff {f : E3 → ℂ} (hf : ContDiffOn ℝ ∞ f upperHalfSpace) : DifferentiableAt ℝ f p :=
    (hat hf).differentiableAt (by simp)
  have hc2 {f : E3 → ℂ} (hf : ContDiffOn ℝ ∞ f upperHalfSpace) : ContDiffAt ℝ 2 f p :=
    (hat hf).of_le (by simp)
  have hsym (a b : Fin 3) : partialC a (partialC b u) =ᶠ[𝓝 p] partialC b (partialC a u) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact partialC_comm ((hu.contDiffAt (hU.mem_nhds hq)).of_le (by simp)) a b
  have hcomm (c a b : Fin 3) : partialC c (partialC a (partialC b u)) p =
      partialC c (partialC b (partialC a u)) p := partialC_congr c (hsym a b)
  have hcommD (a b c : Fin 3) : partialC a (partialC b (partialC c u)) p =
      partialC b (partialC a (partialC c u)) p := partialC_comm (hc2 (hD c)) a b
  have hH0 := sum_partialC_tangential k hd hs 0 hp
  have hH1 := sum_partialC_tangential k hd hs 1 hp
  simp only [Fin.sum_univ_three, Fin.castSucc_zero, Fin.castSucc_one] at hH0 hH1
  have hIk : (I * k : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hk)
  set c : ℂ := (I * k)⁻¹ with hcdef
  have hc : c * (k : ℂ) ^ 2 = -(I * k) := by
    rw [hcdef, inv_mul_eq_div, div_eq_iff hIk]
    ring_nf
    rw [I_sq]
    ring
  -- the curl of `E` and the components of `B`
  have hcE0 := curlC_apertureE_zero k u₀
  have hcE1 := curlC_apertureE_one k u₀
  have hcE2 := curlC_apertureE_two k u₀
  rw [← hudef] at hcE0 hcE1 hcE2
  have hdcE2 : DifferentiableAt ℝ (curlC (apertureE k u₀) 2) p := by
    rw [hcE2]
    exact ((hdiff (hDD 0 0)).neg).sub (hdiff (hDD 1 1))
  have hdcE (α : Fin 3) : DifferentiableAt ℝ (curlC (apertureE k u₀) α) p := by
    fin_cases α
    · simp only [Fin.zero_eta, hcE0]
      exact hdiff (hDD 2 0)
    · simp only [Fin.mk_one, hcE1]
      exact hdiff (hDD 2 1)
    · exact hdcE2
  have hpB (a α : Fin 3) : partialC a (apertureB k u₀ α) p =
      c * partialC a (curlC (apertureE k u₀) α) p :=
    partialC_const_mul_apply a c (hdcE α)
  have hpcE2 (a : Fin 3) : partialC a (curlC (apertureE k u₀) 2) p =
      -partialC a (partialC 0 (partialC 0 u)) p - partialC a (partialC 1 (partialC 1 u)) p := by
    rw [hcE2, partialC_sub_apply (f := fun q => -partialC 0 (partialC 0 u) q)
      (g := partialC 1 (partialC 1 u)) a ((hdiff (hDD 0 0)).neg) (hdiff (hDD 1 1)), partialC_neg]
  have hE0 : apertureE k u₀ 0 = partialC 1 u := rfl
  have hE1 : apertureE k u₀ 1 = fun q => -partialC 0 u q := rfl
  have hE2 : apertureE k u₀ 2 = fun _ => 0 := rfl
  refine ⟨fun α => ?_, fun α => ?_, ?_, ?_⟩
  · -- `curl E = ik B`
    show curlC (apertureE k u₀) α p = I * k * ((I * k)⁻¹ * curlC (apertureE k u₀) α p)
    rw [← mul_assoc, mul_inv_cancel₀ hIk, one_mul]
  · -- `curl B = −ik E`
    fin_cases α
    · show partialC 1 (apertureB k u₀ 2) p - partialC 2 (apertureB k u₀ 1) p =
        -(I * k) * apertureE k u₀ 0 p
      rw [hpB, hpB, hpcE2, hcE1, hE0]
      have e1 : partialC 1 (partialC 0 (partialC 0 u)) p =
          partialC 0 (partialC 0 (partialC 1 u)) p := (hcommD 1 0 0).trans (hcomm 0 1 0)
      linear_combination (-c) * e1 + (-c) * hH1 + partialC 1 u p * hc
    · show partialC 2 (apertureB k u₀ 0) p - partialC 0 (apertureB k u₀ 2) p =
        -(I * k) * apertureE k u₀ 1 p
      rw [hpB, hpB, hpcE2, hcE0, hE1]
      have e2 : partialC 0 (partialC 1 (partialC 1 u)) p =
          partialC 1 (partialC 1 (partialC 0 u)) p := (hcommD 0 1 1).trans (hcomm 1 0 1)
      linear_combination c * e2 + c * hH0 - partialC 0 u p * hc
    · show partialC 0 (apertureB k u₀ 1) p - partialC 1 (apertureB k u₀ 0) p =
        -(I * k) * apertureE k u₀ 2 p
      rw [hpB, hpB, hcE1, hcE0, hE2]
      have e3 : partialC 0 (partialC 2 (partialC 1 u)) p =
          partialC 2 (partialC 0 (partialC 1 u)) p := hcommD 0 2 1
      have e4 : partialC 1 (partialC 2 (partialC 0 u)) p =
          partialC 2 (partialC 0 (partialC 1 u)) p := (hcommD 1 2 0).trans (hcomm 2 1 0)
      linear_combination c * e3 - c * e4
  · -- `div E = 0`
    show ∑ α, partialC α (apertureE k u₀ α) p = 0
    rw [Fin.sum_univ_three, hE0, hE1, hE2, partialC_neg, partialC_zero]
    have := partialC_comm (hc2 hu) 0 1
    simp only
    linear_combination this
  · -- `div B = 0`
    show ∑ α, partialC α (apertureB k u₀ α) p = 0
    rw [Fin.sum_univ_three, hpB, hpB, hpB, hpcE2, hcE0, hcE1]
    have e5 := hcommD 0 2 0
    have e6 := hcommD 1 2 1
    linear_combination c * e5 + c * e6

/-! ### The radiation condition and the boundary condition -/

/-- The radiation condition depends only on the values on `z > 0`. -/
theorem IsRadiating.congr {k : ℝ} {f g : E3 → ℂ} (hf : IsRadiating k f)
    (h : EqOn f g upperHalfSpace) : IsRadiating k g := by
  obtain ⟨⟨C, R₀, hC⟩, h2⟩ := hf
  have hd : ∀ p : E3, 0 < p 2 → fderiv ℝ g p = fderiv ℝ f p := fun p hp => by
    have : g =ᶠ[𝓝 p] f := by
      filter_upwards [isOpen_upperHalfSpace.mem_nhds hp] with q hq
      exact (h hq).symm
    exact this.fderiv_eq
  refine ⟨⟨C, R₀, fun p hp hpR => ?_⟩, fun ε hε => ?_⟩
  · rw [← h hp]
    exact hC p hp hpR
  · obtain ⟨R₁, hR₁⟩ := h2 ε hε
    exact ⟨R₁, fun p hp hpR => by rw [hd p hp, ← h hp]; exact hR₁ p hp hpR⟩

/-- The radiation condition is preserved by the change of sign. -/
theorem IsRadiating.neg {k : ℝ} {f : E3 → ℂ} (hf : IsRadiating k f) :
    IsRadiating k fun p => -f p := by
  obtain ⟨⟨C, R₀, hC⟩, h2⟩ := hf
  refine ⟨⟨C, R₀, fun p hp hpR => by simpa using hC p hp hpR⟩, fun ε hε => ?_⟩
  obtain ⟨R₁, hR₁⟩ := h2 ε hε
  refine ⟨R₁, fun p hp hpR => ?_⟩
  rw [fderiv_fun_neg]
  have h := hR₁ p hp hpR
  rwa [show (-fderiv ℝ f p) (‖p‖⁻¹ • p) - I * k * -f p =
      -(fderiv ℝ f p (‖p‖⁻¹ • p) - I * k * f p) by simp only [neg_apply]; ring, norm_neg]

/-- The zero field satisfies the radiation condition. -/
theorem isRadiating_zero (k : ℝ) : IsRadiating k fun _ => (0 : ℂ) :=
  ⟨⟨0, 0, fun p _ _ => by simp⟩, fun ε hε => ⟨0, fun p _ _ => by simpa using hε.le⟩⟩

section Data

variable {u₀ : E2 → ℂ}

/-- A derivative of data of class `C¹` is continuous. -/
theorem continuous_fderiv_apply (hd : ContDiff ℝ 1 u₀) (w : E2) :
    Continuous fun y => fderiv ℝ u₀ y w :=
  (hd.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- A derivative of data of compact support has compact support. -/
theorem hasCompactSupport_fderiv_apply (hs : HasCompactSupport u₀) (w : E2) :
    HasCompactSupport fun y => fderiv ℝ u₀ y w :=
  (hs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E2 →L[ℝ] ℂ => L w) (by simp)

/-- **The first component of `E` is the aperture field of `∂_y u₀`** on `z > 0`. -/
theorem apertureE_zero_eqOn (k : ℝ) (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀) :
    EqOn (apertureE k u₀ 0)
      (apertureField k fun y => fderiv ℝ u₀ y (EuclideanSpace.single 1 1)) upperHalfSpace :=
  fun p hp => by
    show fderiv ℝ (apertureField k u₀) p (EuclideanSpace.single 1 1) = _
    have h := fderiv_apertureField_planePoint k hd hs hp (EuclideanSpace.single 1 1)
    rw [planePoint_single] at h
    exact h

/-- **The second component of `E` is the aperture field of `−∂_x u₀`** on `z > 0`. -/
theorem apertureE_one_eqOn (k : ℝ) (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀) :
    EqOn (apertureE k u₀ 1)
      (fun p => -apertureField k (fun y => fderiv ℝ u₀ y (EuclideanSpace.single 0 1)) p)
      upperHalfSpace :=
  fun p hp => by
    show -fderiv ℝ (apertureField k u₀) p (EuclideanSpace.single 0 1) = _
    have h := fderiv_apertureField_planePoint k hd hs hp (EuclideanSpace.single 0 1)
    simp only [planePoint_single, Fin.castSucc_zero] at h
    simp only [h]

/-- **The electric field satisfies the radiation condition** componentwise, for `k ≥ 0`. -/
theorem isRadiating_apertureE {k : ℝ} (hk : 0 ≤ k) (hd : ContDiff ℝ 1 u₀)
    (hs : HasCompactSupport u₀) (α : Fin 3) : IsRadiating k (apertureE k u₀ α) := by
  fin_cases α
  · exact (apertureField_isRadiating hk (continuous_fderiv_apply hd _)
      (hasCompactSupport_fderiv_apply hs _)).congr (apertureE_zero_eqOn k hd hs).symm
  · exact (apertureField_isRadiating hk (continuous_fderiv_apply hd _)
      (hasCompactSupport_fderiv_apply hs _)).neg.congr (apertureE_one_eqOn k hd hs).symm
  · exact isRadiating_zero k

/-- **The boundary condition, first tangential component**: `E_x(p) → ∂_y u₀(x)` as `p → (x, 0)`
within `z > 0`. -/
theorem tendsto_apertureE_zero (k : ℝ) (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀)
    (x : E2) :
    Tendsto (apertureE k u₀ 0) (𝓝[upperHalfSpace] (planePoint x))
      (𝓝 (fderiv ℝ u₀ x (EuclideanSpace.single 1 1))) := by
  refine (tendsto_apertureField_nhdsWithin k (continuous_fderiv_apply hd _)
    (hasCompactSupport_fderiv_apply hs _) x).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (apertureE_zero_eqOn k hd hs hp).symm

/-- **The boundary condition, second tangential component**: `E_y(p) → −∂_x u₀(x)` as
`p → (x, 0)` within `z > 0`. -/
theorem tendsto_apertureE_one (k : ℝ) (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀)
    (x : E2) :
    Tendsto (apertureE k u₀ 1) (𝓝[upperHalfSpace] (planePoint x))
      (𝓝 (-fderiv ℝ u₀ x (EuclideanSpace.single 0 1))) := by
  refine ((tendsto_apertureField_nhdsWithin k (continuous_fderiv_apply hd _)
    (hasCompactSupport_fderiv_apply hs _) x).neg).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (apertureE_one_eqOn k hd hs hp).symm

/-- **The conducting boundary condition on the screen**: off the support of the aperture data,
`E → 0` at the plane, in particular `n × E = 0` on the screen. -/
theorem tendsto_apertureE_screen (k : ℝ) (hd : ContDiff ℝ 1 u₀) (hs : HasCompactSupport u₀)
    {x : E2} (hx : x ∉ tsupport u₀) (α : Fin 3) :
    Tendsto (apertureE k u₀ α) (𝓝[upperHalfSpace] (planePoint x)) (𝓝 0) := by
  have h0 : fderiv ℝ u₀ x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hx
  fin_cases α
  · simpa [h0] using tendsto_apertureE_zero k hd hs x
  · simpa [h0] using tendsto_apertureE_one k hd hs x
  · exact tendsto_const_nhds

end Data

/-! ### The smooth aperture -/

/-- The fields of the smooth aperture solve the time-harmonic Maxwell equations on `z > 0`. -/
theorem maxwell_apertureBump {k : ℝ} (hk : k ≠ 0) :
    IsTimeHarmonicMaxwell k (apertureE k apertureBump) (apertureB k apertureBump)
      upperHalfSpace :=
  maxwell_aperture hk (contDiff_apertureBump (n := 1)) hasCompactSupport_apertureBump

/-- The electric field of the smooth aperture satisfies the radiation condition. -/
theorem isRadiating_apertureE_apertureBump {k : ℝ} (hk : 0 ≤ k) (α : Fin 3) :
    IsRadiating k (apertureE k apertureBump α) :=
  isRadiating_apertureE hk (contDiff_apertureBump (n := 1)) hasCompactSupport_apertureBump α

/-- The electric field of the smooth aperture vanishes at the screen `|x| > 1`. -/
theorem tendsto_apertureE_apertureBump_screen (k : ℝ) {x : E2} (hx : 1 < ‖x‖) (α : Fin 3) :
    Tendsto (apertureE k apertureBump α) (𝓝[upperHalfSpace] (planePoint x)) (𝓝 0) :=
  tendsto_apertureE_screen k (contDiff_apertureBump (n := 1)) hasCompactSupport_apertureBump
    (fun h => (not_le.mpr hx) (norm_le_one_of_mem_tsupport_apertureBump h)) α

/-- The smooth aperture has a nonvanishing derivative along the second axis somewhere: by the mean
value theorem `s′(c) = 1` for some `c ∈ (0, 1)`, and at `x = (0, √(1 − c))` the derivative is
`−2√(1 − c) s′(c)`. -/
theorem exists_fderiv_apertureBump_ne_zero :
    ∃ x : E2, fderiv ℝ apertureBump x (EuclideanSpace.single 1 1) ≠ 0 := by
  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_slope Real.smoothTransition zero_lt_one
    (Real.smoothTransition.contDiff (n := 0)).continuous.continuousOn
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero).differentiableOn
  rw [Real.smoothTransition.one, Real.smoothTransition.zero, sub_zero, div_one] at hdc
  set t := √(1 - c) with htdef
  have ht : 0 < t := Real.sqrt_pos.mpr (by linarith [hc.2])
  set x : E2 := t • EuclideanSpace.single 1 1 with hxdef
  have hx : ‖x‖ ^ 2 = 1 - c := by
    rw [hxdef, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos ht, htdef, Real.sq_sqrt (by linarith [hc.2])]
  have h1 : HasFDerivAt (fun y : E2 => 1 - ‖y‖ ^ 2) (-(2 • innerSL ℝ x)) x := by
    have := ((hasFDerivAt_id x).norm_sq).const_sub 1
    simpa using this
  have hs : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (1 - ‖x‖ ^ 2))
      (1 - ‖x‖ ^ 2) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have h2 := ofRealCLM.hasFDerivAt.comp x (hs.comp_hasFDerivAt x h1)
  have hb : apertureBump = ⇑ofRealCLM ∘ (Real.smoothTransition ∘ fun y : E2 => 1 - ‖y‖ ^ 2) := by
    funext y
    simp [apertureBump]
  refine ⟨x, ?_⟩
  rw [hb, h2.fderiv]
  have hin : ⟪x, EuclideanSpace.single 1 1⟫_ℝ = t := by
    rw [hxdef, inner_smul_left, EuclideanSpace.inner_single_right]
    simp
  simp only [ContinuousLinearMap.comp_apply, smul_apply, neg_apply, innerSL_apply_apply,
    ofRealCLM_apply, hin, hx, show 1 - (1 - c) = c by ring, hdc, smul_eq_mul, nsmul_eq_mul]
  push_cast
  intro h
  have : (t : ℂ) = 0 := by linear_combination (-1 / 2 : ℂ) * h
  exact ht.ne' (by exact_mod_cast this)

/-- **The electric field of the smooth aperture is not zero**: at some point of the plane its
first component tends to a nonzero value. -/
theorem exists_tendsto_apertureE_apertureBump_ne_zero (k : ℝ) :
    ∃ x : E2, ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (apertureE k apertureBump 0) (𝓝[upperHalfSpace] (planePoint x)) (𝓝 c) := by
  obtain ⟨x, hx⟩ := exists_fderiv_apertureBump_ne_zero
  exact ⟨x, _, hx, tendsto_apertureE_zero k (contDiff_apertureBump (n := 1))
    hasCompactSupport_apertureBump x⟩

end ProjectAinos.Electrodynamics.Diffraction
