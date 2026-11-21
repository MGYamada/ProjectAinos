/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorFlux
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Tactic

/-!
# The divergence theorem on a half-space, and complex fluxes through spheres

Space is `ℝ³ = EuclideanSpace ℝ (Fin 3)`.

* `integral_divergence_halfSpace`: **the divergence theorem on the half-space** `z ≥ ε`, for a
  field of class `C¹` on an open set containing the closed half-space that vanishes outside a
  ball: `∫_{z ≥ ε} div F = −∫_{ℝ²} F_z(x, ε) dx`. It is Mathlib's divergence theorem on a box,
  transported from `Fin 3 → ℝ`; the faces of the box other than `z = ε` lie outside the ball.
* `fluxC V c R = R² ∫ Σ_α V_α(c + R n) n_α dσ(n)` and `divergenceC`: the flux of a complex field
  through the sphere of radius `R` about `c`, and its divergence. `fluxC_sub_fluxC`: **the
  divergence theorem on a shell about `c`**, from `Sphere.flux_sub_flux` applied to the real and
  the imaginary parts.
* `continuousAt_integral_sphere_of_continuousOn`: continuity of a parametric integral over the
  sphere with values in a normed space.
* `radialCutoff c a b p = s(a|p − c|² + b)` with the smooth transition `s`: a smooth radial
  cutoff, with its derivative (`fderiv_radialCutoff_apply`), its values off `[0, 1]`
  (`radialCutoff_eq_zero`, `radialCutoff_eq_one`, `fderiv_radialCutoff_eq_zero`) and the bound of
  `s′` (`exists_abs_deriv_smoothTransition_le`).
* `fderiv_ofReal_mul_apply`, `contDiffAt_ofReal_mul`: products of real and complex functions;
  `integrableOn_of_continuousOn_of_eq_zero`: a function continuous on a neighbourhood of a closed
  set and vanishing outside a ball is integrable on the set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology ContDiff InnerProductSpace

namespace ProjectAinos.SmoothGeometry.Sphere

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The divergence theorem on a half-space -/

section HalfSpace

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A co-ordinate is at most the norm. -/
theorem abs_apply_le_norm (p : E3) (i : Fin 3) : |p i| ≤ ‖p‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le p i

/-- A field that vanishes outside the closed ball of radius `L` has a vanishing derivative
outside it. -/
theorem fderiv_eq_zero_of_lt_norm {G : E3 → V} {L : ℝ} (hG : ∀ p : E3, L < ‖p‖ → G p = 0)
    {p : E3} (hp : L < ‖p‖) : fderiv ℝ G p = 0 := by
  have h : G =ᶠ[𝓝 p] fun _ => (0 : V) := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hp] with q hq
    exact hG q hq
  rw [h.fderiv_eq]
  simp

/-- **The divergence theorem on the half-space** `z ≥ ε`: for a field of class `C¹` on an open
set that contains the closed half-space and vanishes outside the closed ball of radius `L`,
`∫_{z ≥ ε} div F = −∫_{ℝ²} F_z(x₁, x₂, ε) dx`. -/
theorem integral_divergence_halfSpace {F : Fin 3 → E3 → V} {O : Set E3} (hO : IsOpen O)
    {ε : ℝ} (hsub : ∀ p : E3, ε ≤ p 2 → p ∈ O) (hF : ∀ α, ContDiffOn ℝ 1 (F α) O) {L : ℝ}
    (hL : ∀ α (p : E3), L < ‖p‖ → F α p = 0) :
    ∫ p in {p : E3 | ε ≤ p 2}, ∑ α, fderiv ℝ (F α) p (EuclideanSpace.single α 1) =
      -∫ x : E2, F 2 !₂[x 0, x 1, ε] := by
  set e : E3 ≃L[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ with he
  have he_vol : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin 3)
  have he_emb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hsymm (x : Fin 3 → ℝ) (i : Fin 3) : e.symm x i = x i := rfl
  set L' : ℝ := |L| + 1 with hL'
  set Z : ℝ := |ε| + L' with hZ
  have hLL : L < L' := by
    have := le_abs_self L
    linarith
  have hLZ : L < Z := by
    have := abs_nonneg ε
    linarith
  have hL'pos : 0 < L' := by
    have := abs_nonneg L
    linarith
  have hZpos : 0 < Z := by
    have := abs_nonneg ε
    linarith
  set a : Fin 3 → ℝ := ![-L', -L', ε] with ha
  set b : Fin 3 → ℝ := ![L', L', Z] with hb
  have hab : a ≤ b := by
    intro i
    have h1 : -L' ≤ L' := by
      have := abs_nonneg L
      linarith
    have h2 : ε ≤ Z := by
      have := le_abs_self ε
      have := abs_nonneg L
      linarith
    fin_cases i <;> simp [ha, hb, h1, h2]
  -- the norm is large off the box
  have hfar (p : E3) (i : Fin 3) (c : ℝ) (hc : L < |c|) (hpi : p i = c) : L < ‖p‖ := by
    have := abs_apply_le_norm p i
    rw [hpi] at this
    linarith
  have hD0 : ∀ p : E3, L < ‖p‖ →
      ∑ α, fderiv ℝ (F α) p (EuclideanSpace.single α 1) = 0 := fun p hp => by
    simp [fderiv_eq_zero_of_lt_norm (hL _) hp]
  have hIccO : ∀ x ∈ Icc a b, e.symm x ∈ O := fun x hx => hsub _ (by
    rw [hsymm]
    simpa [ha] using hx.1 2)
  set f : Fin 3 → (Fin 3 → ℝ) → V := fun i x => F i (e.symm x) with hf
  set f' : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] V :=
    fun i x => (fderiv ℝ (F i) (e.symm x)).comp (e.symm : (Fin 3 → ℝ) →L[ℝ] E3) with hf'
  have hc (i : Fin 3) : ContinuousOn (f i) (Icc a b) :=
    (hF i).continuousOn.comp e.symm.continuous.continuousOn fun x hx => hIccO x hx
  have hd : ∀ x ∈ (Set.pi univ fun i => Ioo (a i) (b i)) \ (∅ : Set (Fin 3 → ℝ)),
      ∀ i, HasFDerivAt (f i) (f' i x) x := fun x hx i => by
    have hx2 : ε < e.symm x 2 := by
      rw [hsymm]
      simpa [ha] using (hx.1 2 (mem_univ _)).1
    have hO' : e.symm x ∈ O := hsub _ hx2.le
    have hdiff : DifferentiableAt ℝ (F i) (e.symm x) :=
      ((hF i).differentiableOn one_ne_zero _ hO').differentiableAt (hO.mem_nhds hO')
    exact hdiff.hasFDerivAt.comp x e.symm.hasFDerivAt
  have hcD : ContinuousOn (fun x => ∑ i, f' i x (Pi.single i 1)) (Icc a b) := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    have h1 : ContinuousOn (fun x => fderiv ℝ (F i) (e.symm x)) (Icc a b) :=
      ((hF i).continuousOn_fderiv_of_isOpen hO le_rfl).comp e.symm.continuous.continuousOn
        fun x hx => hIccO x hx
    exact h1.clm_apply continuousOn_const
  have hi : IntegrableOn (fun x => ∑ i, f' i x (Pi.single i 1)) (Icc a b) :=
    hcD.integrableOn_compact isCompact_Icc
  have hbox := integral_divergence_of_hasFDerivAt_off_countable' a b hab f f' ∅
    countable_empty hc hd hi
  -- the left side
  have hsingle (i : Fin 3) : e.symm (Pi.single i 1) = EuclideanSpace.single i 1 := by
    ext j
    simp [hsymm, Pi.single_apply, PiLp.single_apply]
  set D : E3 → V := fun p => ∑ α, fderiv ℝ (F α) p (EuclideanSpace.single α 1) with hDdef
  have hlhs : ∫ x in Icc a b, ∑ i, f' i x (Pi.single i 1) = ∫ p in e ⁻¹' Icc a b, D p := by
    rw [← he_vol.setIntegral_preimage_emb he_emb]
    refine setIntegral_congr_fun (measurableSet_Icc.preimage e.continuous.measurable)
      fun p _ => ?_
    simp only [hf', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hsingle,
      hDdef, ContinuousLinearEquiv.symm_apply_apply]
  have hmeas : MeasurableSet {p : E3 | ε ≤ p 2} :=
    measurableSet_le measurable_const (by fun_prop)
  have hset : ∫ p in {p : E3 | ε ≤ p 2}, D p = ∫ p in e ⁻¹' Icc a b, D p := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas (fun p hp => ?_)
      fun p hp => ?_
    · have h := hp.1 2
      simp only [mem_ofPred_eq]
      have : e p 2 = p 2 := rfl
      rw [this] at h
      simpa [ha] using h
    · obtain ⟨hp1, hp2⟩ := hp
      simp only [mem_ofPred_eq] at hp1
      refine hD0 p ?_
      simp only [mem_preimage, mem_Icc, not_and_or, Pi.le_def, not_forall] at hp2
      have he' (i : Fin 3) : e p i = p i := rfl
      rcases hp2 with ⟨i, hi⟩ | ⟨i, hi⟩ <;> simp only [he'] at hi <;> fin_cases i <;>
        simp [ha, hb] at hi
      · exact (hfar p 0 (p 0) (by rw [abs_of_neg (by linarith)]; linarith) rfl)
      · exact (hfar p 1 (p 1) (by rw [abs_of_neg (by linarith)]; linarith) rfl)
      · exact absurd hp1 (not_le.mpr hi)
      · exact (hfar p 0 (p 0) (by rw [abs_of_pos (by linarith)]; linarith) rfl)
      · exact (hfar p 1 (p 1) (by rw [abs_of_pos (by linarith)]; linarith) rfl)
      · exact (hfar p 2 (p 2) (by rw [abs_of_pos (by linarith)]; linarith) rfl)
  -- the faces
  have hzero (i : Fin 3) (c : ℝ) (hc : L < |c|) (x : Fin 2 → ℝ) :
      f i (Fin.insertNth i c x) = 0 := by
    simp only [hf]
    refine hL i _ (hfar _ i c hc ?_)
    rw [hsymm]
    simp
  have hL'abs : L < |L'| := by
    rw [abs_of_pos (by have := abs_nonneg L; linarith)]
    exact hLL
  have hL'abs' : L < |-L'| := by rwa [abs_neg]
  have hZabs : L < |Z| := by
    rw [abs_of_pos (by have := abs_nonneg ε; have := abs_nonneg L; linarith)]
    exact hLZ
  have hface : ∀ i : Fin 3, i ≠ 2 →
      (∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f i (Fin.insertNth i (b i) x)) -
        ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f i (Fin.insertNth i (a i) x) = 0 := by
    intro i hi
    have hai : L < |a i| := by fin_cases i <;> simp_all
    have hbi : L < |b i| := by fin_cases i <;> simp_all
    simp [hzero i _ hai, hzero i _ hbi]
  have htop : ∫ x in Icc (a ∘ (2 : Fin 3).succAbove) (b ∘ (2 : Fin 3).succAbove),
      f 2 (Fin.insertNth 2 (b 2) x) = 0 := by
    have : L < |b 2| := by simpa [hb] using hZabs
    simp [hzero 2 _ this]
  rw [Fin.sum_univ_three, hface 0 (by decide), hface 1 (by decide), htop, zero_add, zero_add,
    zero_sub, hlhs, ← hset] at hbox
  rw [hbox, neg_inj]
  -- the bottom face is the plane
  have ha2 : a 2 = ε := rfl
  rw [ha2]
  set g : (Fin 2 → ℝ) → V := fun x => f 2 (Fin.insertNth 2 ε x) with hg
  have hg0 : ∀ x ∉ Icc (a ∘ (2 : Fin 3).succAbove) (b ∘ (2 : Fin 3).succAbove), g x = 0 := by
    intro x hx
    simp only [mem_Icc, not_and_or, Pi.le_def, not_forall, Function.comp_apply] at hx
    simp only [hg, hf]
    refine hL 2 _ ?_
    rcases hx with ⟨j, hj⟩ | ⟨j, hj⟩ <;> fin_cases j <;>
      simp [ha, hb, Fin.succAbove] at hj
    · exact hfar _ 0 (x 0) (by rw [abs_of_neg (by linarith)]; linarith) (by rw [hsymm]; rfl)
    · exact hfar _ 1 (x 1) (by rw [abs_of_neg (by linarith)]; linarith) (by rw [hsymm]; rfl)
    · exact hfar _ 0 (x 0) (by rw [abs_of_pos (by linarith)]; linarith) (by rw [hsymm]; rfl)
    · exact hfar _ 1 (x 1) (by rw [abs_of_pos (by linarith)]; linarith) (by rw [hsymm]; rfl)
  have hIcc : ∫ x in Icc (a ∘ (2 : Fin 3).succAbove) (b ∘ (2 : Fin 3).succAbove), g x =
      ∫ x, g x := by
    exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ _)
      fun x hx => hg0 x hx.2).symm.trans setIntegral_univ
  rw [hIcc]
  have hmp := PiLp.volume_preserving_ofLp (Fin 2)
  have hemb : MeasurableEmbedding (@WithLp.ofLp 2 (Fin 2 → ℝ)) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.measurableEmbedding
  rw [← hmp.integral_comp hemb g]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hg, hf]
  congr 1
  ext j
  fin_cases j <;> rfl

end HalfSpace

/-! ### Parametric integrals over the sphere with values in a normed space -/

section Parametric

universe v

variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Continuity of a parametric integral over the sphere**, with values in a normed space: if
`G` is continuous on an open set `O ⊇ {s₀} × S²`, then `s ↦ ∫ G(s, n) dσ(n)` is continuous at
`s₀`. -/
theorem continuousAt_integral_sphere_of_continuousOn {G : ℝ → E3 → V} {O : Set (ℝ × E3)}
    (hO : IsOpen O) {s₀ : ℝ} (hs₀ : ∀ n ∈ sphere (0 : E3) 1, (s₀, n) ∈ O)
    (hG : ContinuousOn (Function.uncurry G) O) :
    ContinuousAt (fun s => ∫ n : sphere (0 : E3) 1, G s n ∂sphereMeasure) s₀ := by
  obtain ⟨δ, hδ, hsub⟩ := exists_prod_subset hO hs₀
  have hK : IsCompact (closedBall s₀ δ ×ˢ sphere (0 : E3) 1) :=
    (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKO : closedBall s₀ δ ×ˢ sphere (0 : E3) 1 ⊆ O := fun p hp =>
    hsub p.1 (by simpa [mem_closedBall, Real.dist_eq] using hp.1) p.2 hp.2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hG.mono hKO)
  have hball : ball s₀ δ ∈ 𝓝 s₀ := ball_mem_nhds s₀ hδ
  have hrestr {s : ℝ} (hs : ∀ n ∈ sphere (0 : E3) 1, (s, n) ∈ O) :
      Continuous fun n : sphere (0 : E3) 1 => G s n := by
    have h : Continuous fun n : sphere (0 : E3) 1 => ((s, (n : E3)) : ℝ × E3) := by fun_prop
    exact hG.comp_continuous h fun n => hs n n.2
  refine continuousAt_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const C) ?_
  · filter_upwards [hball] with s hs
    exact (hrestr fun n hn =>
      hsub s (by rw [mem_ball, Real.dist_eq] at hs; exact hs.le) n hn).aestronglyMeasurable
  · filter_upwards [hball] with s hs
    exact Eventually.of_forall fun n => hC (s, n) ⟨ball_subset_closedBall hs, n.2⟩
  · refine Eventually.of_forall fun n => ?_
    have hc : ContinuousAt (Function.uncurry G) (s₀, (n : E3)) :=
      hG.continuousAt (hO.mem_nhds (hs₀ n n.2))
    exact hc.comp (f := fun s : ℝ => ((s, (n : E3)) : ℝ × E3)) (by fun_prop)

end Parametric

/-! ### Complex fluxes through spheres about a point -/

section ComplexFlux

/-- The flux `R² ∫ Σ_α V_α(c + R n) n_α dσ(n)` of a complex vector field through the sphere of
radius `R` about `c`. -/
def fluxC (V : Fin 3 → E3 → ℂ) (c : E3) (R : ℝ) : ℂ :=
  ∫ n : sphere (0 : E3) 1, ((R ^ 2 : ℝ) : ℂ) *
    ∑ α, V α (c + R • (n : E3)) * (((n : E3) α : ℝ) : ℂ) ∂sphereMeasure

/-- The divergence `Σ_α ∂_α V_α` of a complex vector field. -/
def divergenceC (V : Fin 3 → E3 → ℂ) (x : E3) : ℂ :=
  ∑ α, fderiv ℝ (V α) x (EuclideanSpace.single α 1)

/-- The flux through the sphere of radius `0` vanishes. -/
@[simp] theorem fluxC_zero (V : Fin 3 → E3 → ℂ) (c : E3) : fluxC V c 0 = 0 := by
  simp [fluxC]

/-- The real part `x ↦ Re V_α(c + x)` of a complex field, translated to `c`. -/
def rePart (V : Fin 3 → E3 → ℂ) (c : E3) : Fin 3 → E3 → ℝ := fun α x => (V α (c + x)).re

/-- The imaginary part `x ↦ Im V_α(c + x)` of a complex field, translated to `c`. -/
def imPart (V : Fin 3 → E3 → ℂ) (c : E3) : Fin 3 → E3 → ℝ := fun α x => (V α (c + x)).im

/-- The integrand of the flux is integrable when the field is continuous on the sphere. -/
theorem integrable_fluxC_integrand {V : Fin 3 → E3 → ℂ} {W : Set E3}
    (hV : ∀ α, ContinuousOn (V α) W) {c : E3} {R : ℝ}
    (hR : ∀ n ∈ sphere (0 : E3) 1, c + R • n ∈ W) :
    Integrable (fun n : sphere (0 : E3) 1 => ((R ^ 2 : ℝ) : ℂ) *
      ∑ α, V α (c + R • (n : E3)) * (((n : E3) α : ℝ) : ℂ)) sphereMeasure := by
  have hc : Continuous fun n : sphere (0 : E3) 1 => ((R ^ 2 : ℝ) : ℂ) *
      ∑ α, V α (c + R • (n : E3)) * (((n : E3) α : ℝ) : ℂ) := by
    refine continuous_const.mul (continuous_finsetSum _ fun α _ => ?_)
    have h1 : Continuous fun n : sphere (0 : E3) 1 => V α (c + R • (n : E3)) :=
      (hV α).comp_continuous (by fun_prop) fun n => hR n n.2
    exact h1.mul (by fun_prop)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The real part of the flux is the flux of the real part. -/
theorem re_fluxC {V : Fin 3 → E3 → ℂ} {W : Set E3} (hV : ∀ α, ContinuousOn (V α) W) {c : E3}
    {R : ℝ} (hR : ∀ n ∈ sphere (0 : E3) 1, c + R • n ∈ W) :
    (fluxC V c R).re = flux (rePart V c) R := by
  unfold fluxC flux rePart
  rw [← Complex.reCLM_apply, ← (Complex.reCLM : ℂ →L[ℝ] ℝ).integral_comp_comm
    (integrable_fluxC_integrand hV hR)]
  refine integral_congr_ae (Eventually.of_forall fun n => ?_)
  simp only [Complex.reCLM_apply, Complex.re_ofReal_mul, Complex.re_sum, Complex.re_mul_ofReal]

/-- The imaginary part of the flux is the flux of the imaginary part. -/
theorem im_fluxC {V : Fin 3 → E3 → ℂ} {W : Set E3} (hV : ∀ α, ContinuousOn (V α) W) {c : E3}
    {R : ℝ} (hR : ∀ n ∈ sphere (0 : E3) 1, c + R • n ∈ W) :
    (fluxC V c R).im = flux (imPart V c) R := by
  unfold fluxC flux imPart
  rw [← Complex.imCLM_apply, ← (Complex.imCLM : ℂ →L[ℝ] ℝ).integral_comp_comm
    (integrable_fluxC_integrand hV hR)]
  refine integral_congr_ae (Eventually.of_forall fun n => ?_)
  simp only [Complex.imCLM_apply, Complex.im_ofReal_mul, Complex.im_sum, Complex.im_mul_ofReal]

/-- The derivative of the real part of a translated complex function. -/
theorem fderiv_re_comp_add {g : E3 → ℂ} {c x : E3} (hg : DifferentiableAt ℝ g (c + x))
    (v : E3) : fderiv ℝ (fun x => (g (c + x)).re) x v = (fderiv ℝ g (c + x) v).re := by
  have ht : HasFDerivAt (fun x : E3 => c + x) (ContinuousLinearMap.id ℝ E3) x :=
    (hasFDerivAt_id x).const_add c
  have h := (Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp x (hg.hasFDerivAt.comp x ht)
  have hf : (fun x => (g (c + x)).re) = ⇑(Complex.reCLM : ℂ →L[ℝ] ℝ) ∘ (g ∘ fun x => c + x) := by
    funext x
    simp
  rw [hf, h.fderiv]
  simp

/-- The derivative of the imaginary part of a translated complex function. -/
theorem fderiv_im_comp_add {g : E3 → ℂ} {c x : E3} (hg : DifferentiableAt ℝ g (c + x))
    (v : E3) : fderiv ℝ (fun x => (g (c + x)).im) x v = (fderiv ℝ g (c + x) v).im := by
  have ht : HasFDerivAt (fun x : E3 => c + x) (ContinuousLinearMap.id ℝ E3) x :=
    (hasFDerivAt_id x).const_add c
  have h := (Complex.imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp x (hg.hasFDerivAt.comp x ht)
  have hf : (fun x => (g (c + x)).im) = ⇑(Complex.imCLM : ℂ →L[ℝ] ℝ) ∘ (g ∘ fun x => c + x) := by
    funext x
    simp
  rw [hf, h.fderiv]
  simp

/-- **The divergence theorem on a shell about `c`** for a complex field of class `C¹` on an open
set that contains the closed shell `R₁ ≤ |x − c| ≤ R₂`: the difference of the fluxes is the
integral of the divergence over the shell. With `R₁ = 0`, on a ball. -/
theorem fluxC_sub_fluxC {V : Fin 3 → E3 → ℂ} {W : Set E3} (hW : IsOpen W)
    (hV : ∀ α, ContDiffOn ℝ 1 (V α) W) {c : E3} {R₁ R₂ : ℝ} (h0 : 0 ≤ R₁) (h12 : R₁ ≤ R₂)
    (hsub : ∀ x : E3, R₁ ≤ ‖x‖ → ‖x‖ ≤ R₂ → c + x ∈ W) :
    fluxC V c R₂ - fluxC V c R₁ = ∫ x in shell R₁ R₂, divergenceC V (c + x) := by
  set W' : Set E3 := {x | c + x ∈ W} with hW'
  have hW'o : IsOpen W' := hW.preimage (continuous_const.add continuous_id)
  have hmaps : MapsTo (fun x : E3 => c + x) W' W := fun x hx => hx
  have htr : ContDiff ℝ 1 (fun x : E3 => c + x) := contDiff_const.add contDiff_id
  have hre : ∀ α, ContDiffOn ℝ 1 (rePart V c α) W' := fun α =>
    (Complex.reCLM : ℂ →L[ℝ] ℝ).contDiff.comp_contDiffOn ((hV α).comp htr.contDiffOn hmaps)
  have him : ∀ α, ContDiffOn ℝ 1 (imPart V c α) W' := fun α =>
    (Complex.imCLM : ℂ →L[ℝ] ℝ).contDiff.comp_contDiffOn ((hV α).comp htr.contDiffOn hmaps)
  have hfr := flux_sub_flux hW'o hre h0 h12 hsub
  have hfi := flux_sub_flux hW'o him h0 h12 hsub
  have hcont : ∀ α, ContinuousOn (V α) W := fun α => (hV α).continuousOn
  have hsph {R : ℝ} (hR1 : R₁ ≤ R) (hR2 : R ≤ R₂) : ∀ n ∈ sphere (0 : E3) 1, c + R • n ∈ W :=
    fun n hn => hsub _ (by rw [norm_smul, norm_eq_of_mem_sphere ⟨n, hn⟩, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (h0.trans hR1)]; exact hR1)
      (by rw [norm_smul, norm_eq_of_mem_sphere ⟨n, hn⟩, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (h0.trans hR1)]; exact hR2)
  have h1 := hsph le_rfl h12
  have h2 := hsph h12 le_rfl
  -- integrability of the divergence on the shell
  have hdiv : ContinuousOn (fun x => divergenceC V (c + x)) W' := by
    refine continuousOn_finsetSum _ fun α _ => ?_
    exact (((hV α).continuousOn_fderiv_of_isOpen hW le_rfl).comp htr.continuous.continuousOn
      hmaps).clm_apply continuousOn_const
  have hK : IsCompact {x : E3 | R₁ ≤ ‖x‖ ∧ ‖x‖ ≤ R₂} :=
    (isCompact_closedBall (0 : E3) R₂).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      fun x hx => by simpa using hx.2
  have hint : IntegrableOn (fun x => divergenceC V (c + x)) (shell R₁ R₂) :=
    ((hdiv.mono fun x hx => hsub x hx.1 hx.2).integrableOn_compact hK).mono_set
      fun x hx => ⟨hx.1.le, hx.2.le⟩
  have hdr : ∀ x ∈ shell R₁ R₂, divergence (rePart V c) x = (divergenceC V (c + x)).re := by
    intro x hx
    have hxW : c + x ∈ W := hsub x hx.1.le hx.2.le
    unfold divergence divergenceC rePart
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact fderiv_re_comp_add (((hV α).differentiableOn one_ne_zero _ hxW).differentiableAt
      (hW.mem_nhds hxW)) _
  have hdi : ∀ x ∈ shell R₁ R₂, divergence (imPart V c) x = (divergenceC V (c + x)).im := by
    intro x hx
    have hxW : c + x ∈ W := hsub x hx.1.le hx.2.le
    unfold divergence divergenceC imPart
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact fderiv_im_comp_add (((hV α).differentiableOn one_ne_zero _ hxW).differentiableAt
      (hW.mem_nhds hxW)) _
  apply Complex.ext
  · rw [Complex.sub_re, re_fluxC hcont h2, re_fluxC hcont h1, hfr,
      ← Complex.reCLM_apply, ← (Complex.reCLM : ℂ →L[ℝ] ℝ).integral_comp_comm hint]
    exact setIntegral_congr_fun (measurableSet_shell R₁ R₂) fun x hx => by
      simp [hdr x hx]
  · rw [Complex.sub_im, im_fluxC hcont h2, im_fluxC hcont h1, hfi,
      ← Complex.imCLM_apply, ← (Complex.imCLM : ℂ →L[ℝ] ℝ).integral_comp_comm hint]
    exact setIntegral_congr_fun (measurableSet_shell R₁ R₂) fun x hx => by
      simp [hdi x hx]

end ComplexFlux

/-! ### Smooth radial cutoffs -/

section Cutoff

/-- The smooth transition is locally constant, so its derivative vanishes, off `[0, 1]`. -/
theorem deriv_smoothTransition_eq_zero {t : ℝ} (ht : t < 0 ∨ 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  rcases ht with ht | ht
  · have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
    rw [h.deriv_eq, deriv_const]
  · have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
    rw [h.deriv_eq, deriv_const]

/-- The derivative of the smooth transition is bounded. -/
theorem exists_abs_deriv_smoothTransition_le :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t, |deriv Real.smoothTransition t| ≤ S := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨S, hS⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨S, hS0, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · simpa [Real.norm_eq_abs] using hS t ht
  · rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rw [deriv_smoothTransition_eq_zero ht, abs_zero]
    exact hS0

/-- The smooth radial cutoff `s(a|p − c|² + b)`, with the smooth transition `s`. -/
def radialCutoff (c : E3) (a b : ℝ) (p : E3) : ℝ :=
  Real.smoothTransition (a * ‖p - c‖ ^ 2 + b)

/-- The cutoff is smooth. -/
theorem contDiff_radialCutoff (c : E3) (a b : ℝ) {n : ℕ∞} : ContDiff ℝ n (radialCutoff c a b) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)) |>.add
      contDiff_const)

/-- The derivative of the cutoff, `D s(a|p − c|² + b) v = s′(·) 2a ⟨p − c, v⟩`. -/
theorem hasFDerivAt_radialCutoff (c : E3) (a b : ℝ) (p : E3) :
    HasFDerivAt (radialCutoff c a b)
      ((deriv Real.smoothTransition (a * ‖p - c‖ ^ 2 + b) * (2 * a)) •
        innerSL ℝ (p - c)) p := by
  have h1 : HasFDerivAt (fun q : E3 => ‖q - c‖ ^ 2) (2 • innerSL ℝ (p - c)) p := by
    have := ((hasFDerivAt_id p).sub_const c).norm_sq
    simpa using this
  have h2 : HasFDerivAt (fun q : E3 => a * ‖q - c‖ ^ 2 + b) (a • 2 • innerSL ℝ (p - c)) p :=
    (h1.const_mul a).add_const b
  have hs : DifferentiableAt ℝ Real.smoothTransition (a * ‖p - c‖ ^ 2 + b) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) _
  have h := hs.hasDerivAt.comp_hasFDerivAt p h2
  refine h.congr_fderiv ?_
  ext v
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- The derivative of the cutoff along `v`. -/
theorem fderiv_radialCutoff_apply (c : E3) (a b : ℝ) (p v : E3) :
    fderiv ℝ (radialCutoff c a b) p v =
      deriv Real.smoothTransition (a * ‖p - c‖ ^ 2 + b) * (2 * a) * ⟪p - c, v⟫_ℝ := by
  rw [(hasFDerivAt_radialCutoff c a b p).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]

/-- The cutoff takes values in `[0, 1]`. -/
theorem radialCutoff_mem_Icc (c : E3) (a b : ℝ) (p : E3) : radialCutoff c a b p ∈ Icc 0 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The cutoff vanishes where `a|p − c|² + b ≤ 0`. -/
theorem radialCutoff_eq_zero {c : E3} {a b : ℝ} {p : E3} (h : a * ‖p - c‖ ^ 2 + b ≤ 0) :
    radialCutoff c a b p = 0 :=
  Real.smoothTransition.zero_of_nonpos h

/-- The cutoff is `1` where `a|p − c|² + b ≥ 1`. -/
theorem radialCutoff_eq_one {c : E3} {a b : ℝ} {p : E3} (h : 1 ≤ a * ‖p - c‖ ^ 2 + b) :
    radialCutoff c a b p = 1 :=
  Real.smoothTransition.one_of_one_le h

/-- The derivative of the cutoff vanishes where `a|p − c|² + b ∉ [0, 1]`. -/
theorem fderiv_radialCutoff_eq_zero {c : E3} {a b : ℝ} {p : E3}
    (h : a * ‖p - c‖ ^ 2 + b < 0 ∨ 1 < a * ‖p - c‖ ^ 2 + b) :
    fderiv ℝ (radialCutoff c a b) p = 0 := by
  ext v
  rw [fderiv_radialCutoff_apply, deriv_smoothTransition_eq_zero h]
  simp

end Cutoff

/-! ### Products with real functions and integrability of fields of bounded support -/

section Products

/-- The derivative of the product of a real and a complex function along `v`. -/
theorem fderiv_ofReal_mul_apply {f : E3 → ℝ} {g : E3 → ℂ} {p : E3}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (v : E3) :
    fderiv ℝ (fun q => (f q : ℂ) * g q) p v =
      (f p : ℂ) * fderiv ℝ g p v + (fderiv ℝ f p v : ℂ) * g p := by
  have hf' : HasFDerivAt (fun q => (f q : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ f p)) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p hf.hasFDerivAt
  have h : HasFDerivAt (fun q => (f q : ℂ) * g q) _ p := hf'.mul hg.hasFDerivAt
  rw [h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply]
  ring

/-- The product of a real and a complex function of class `Cⁿ` is of class `Cⁿ`. -/
theorem contDiffAt_ofReal_mul {f : E3 → ℝ} {g : E3 → ℂ} {p : E3} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) (hg : ContDiffAt ℝ n g p) :
    ContDiffAt ℝ n (fun q => (f q : ℂ) * g q) p :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp p hf).mul hg

universe w

variable {V : Type w} [NormedAddCommGroup V]

/-- A function continuous on a neighbourhood of a closed set that vanishes outside a ball is
integrable on the closed set. -/
theorem integrableOn_of_continuousOn_of_eq_zero {g : E3 → V} {O s : Set E3} (hs : IsClosed s)
    (hsO : s ⊆ O) (hg : ContinuousOn g O) {L : ℝ} (hL : ∀ p : E3, L < ‖p‖ → g p = 0) :
    IntegrableOn g s := by
  have hK : IsCompact (s ∩ closedBall 0 L) := (isCompact_closedBall 0 L).inter_left hs
  have h1 : IntegrableOn g (s ∩ closedBall 0 L) :=
    (hg.mono (inter_subset_left.trans hsO)).integrableOn_compact hK
  have h2 : IntegrableOn g (s \ closedBall 0 L) := by
    refine (integrableOn_zero (μ := volume) (s := s \ closedBall 0 L)).congr_fun
      (fun p hp => ?_) (hs.measurableSet.diff isClosed_closedBall.measurableSet)
    have : L < ‖p‖ := by
      have := hp.2
      rwa [mem_closedBall, dist_zero_right, not_le] at this
    exact (hL p this).symm
  rw [← inter_union_sdiff s (closedBall 0 L)]
  exact h1.union h2

end Products

end ProjectAinos.SmoothGeometry.Sphere
