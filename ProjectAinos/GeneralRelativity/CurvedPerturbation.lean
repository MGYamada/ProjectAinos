/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.IsotropicRicci
public import ProjectAinos.GeneralRelativity.CosmologicalModels
import Mathlib.Tactic

/-! # Longitudinal scalar perturbations on curved dust backgrounds

The metric has lapse a exp(εU) and spatial scale (a/ψ) exp(−εU).
The equations below differentiate its coordinate Ricci tensor and the trace-reversed
dust source in conformal time.
-/

@[expose] public section
noncomputable section
open Set Filter ContinuousLinearMap
open scoped ContDiff Topology
namespace ProjectAinos.GeneralRelativity.CurvedPerturbation
open SmoothGeometry CoordinateMetric FLRW IsotropicRicci
local notation "E" => MinkowskiModel 3

private def vary (f u : E → ℝ) (e : ℝ) (x : E) := f x+e*u x

private theorem smooth_vary {f u : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hu : ContDiffAt ℝ ∞ u x) (e : ℝ) : ContDiffAt ℝ ∞ (vary f u e) x :=
  hf.add (contDiffAt_const.mul hu)

private theorem pvar {f u : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hu : ContDiffAt ℝ ∞ u x) (e : ℝ) (i : Fin 4) :
    part (vary f u e) i x = part f i x+e*part u i x := by
  have d := hu.differentiableAt (by simp)
  change (fderiv ℝ (fun y => f y+e*u y) x) (Pi.single i 1) = _
  rw [fderiv_fun_add (hf.differentiableAt (by simp)) (d.const_mul e),fderiv_const_mul d]
  rfl

private theorem ppvar {f u : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hu : ContDiffAt ℝ ∞ u x) (e : ℝ) (i j : Fin 4) :
    secondPartial (vary f u e) x i j = secondPartial f x i j+e*secondPartial u x i j := by
  unfold vary
  rw [secondPartial_add hf (contDiffAt_const.mul hu),secondPartial_const_mul hu]

private def lap (u : E → ℝ) (x : E) :=
  secondPartial u x 1 1+secondPartial u x 2 2+secondPartial u x 3 3

private def gradDot (s u : E → ℝ) (x : E) :=
  part s 1 x*part u 1 x+part s 2 x*part u 2 x+part s 3 x*part u 3 x

private def sliceL (f s u : E → ℝ) (x : E) :=
  Real.exp (2*(f x-s x))*(lap u x+gradDot s u x)

private def deltaRicci (f s u : E → ℝ) (x : E) (i j : Fin 4) :=
  let H := part f 0 x
  let Hp := secondPartial s x 0 0
  let U := u x
  let d := part u 0 x
  let dd := secondPartial u x 0 0
  if i=0 then if j=0 then 3*dd+6*H*d+sliceL f s u x
    else 2*(H*part u j x+secondPartial u x j 0)
  else if j=0 then 2*(H*part u i x+secondPartial u x i 0)
  else if i=j then Real.exp (2*(s x-f x))*(-dd-6*H*d-4*(Hp+2*H^2)*U)+
    lap u x+gradDot s u x else 0

private theorem first_variation {f s u : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hs : ContDiffAt ℝ ∞ s x) (hu : ContDiffAt ℝ ∞ u x)
    (hF : ∀ i : Fin 4, i ≠ 0 → part f i x = 0)
    (hL : lap f x = 0) (ht : part s 0 x = part f 0 x) (i j : Fin 4) :
    HasDerivAt (fun e => ricciOf (IsotropicRicci.metric (vary f u e) (vary s u (-e))) x i j)
      (deltaRicci f s u x i j) 0 := by
  simp_rw [ricci_eq (smooth_vary hf hu _) (smooth_vary hs hu _),ricciTable,
    pvar hf hu,pvar hs hu,ppvar hf hu,ppvar hs hu]
  dsimp only [vary,deltaRicci,sliceL,lap,gradDot]
  have h1 := hF 1 (by decide)
  have h2 := hF 2 (by decide)
  have h3 := hF 3 (by decide)
  unfold lap at hL
  split_ifs with hi hj hj hij <;> subst_vars
  all_goals refine DifferentiableAt.hasDerivAt ?_ |>.congr_deriv ?_
  all_goals try fun_prop
  all_goals
    simp (disch := first | assumption | decide | fun_prop)
      [deriv_fun_add,deriv_fun_sub,deriv_fun_mul,deriv_fun_pow,ht,h1,h2,h3,hF,hL]
  all_goals ring

private def loga (D : Data) (x : E) := Real.log (D.a (x 0))
private def logs (D : Data) (x : E) := loga D x-Real.log (psi D.k x)

/-- Conformal Hubble rate a′/a. -/
def hubble (D : Data) (t : ℝ) := deriv D.a t/D.a t

/-- Spatial Laplacian in the unit-curvature stereographic chart. -/
def spatialLaplacian (k : ℝ) (u : E → ℝ) (x : E) : ℝ :=
  (psi k x)^2*(secondPartial u x 1 1+secondPartial u x 2 2+secondPartial u x 3 3)-
    psi k x*(k/2)*(x 1*part u 1 x+x 2*part u 2 x+x 3*part u 3 x)

/-- Perturbed metric in longitudinal gauge. -/
def metricFamily (D : Data) (u : E → ℝ) (e : ℝ) :=
  IsotropicRicci.metric (fun x => Real.log (D.a (x 0))+e*u x)
    (fun x => Real.log (D.a (x 0))-Real.log (psi D.k x)+(-e)*u x)

private theorem geometry {D : Data} {x : E} (hx : x ∈ domain D) :
    ContDiffAt ℝ ∞ (loga D) x ∧ ContDiffAt ℝ ∞ (logs D) x := by
  have h : ContDiffAt ℝ ∞ (loga D) x :=
    ((contDiffOn_time D.contDiffOn_a).contDiffAt ((domain D).isOpen.mem_nhds hx)).log
      (a_pos_of_mem hx).ne'
  exact ⟨h,h.sub ((contDiff_psi D.k).contDiffAt.log (psi_pos hx).ne')⟩

private theorem time_part {f : ℝ → ℝ} {x : E} {d : ℝ} (h : HasDerivAt f d (x 0))
    (i : Fin 4) : part (fun y => f (y 0)) i x = if i=0 then d else 0 := by
  rw [part,(hasFDerivAt_time h).fderiv]
  by_cases hi : i=0 <;> simp [smul_apply,proj_apply,smul_eq_mul,hi,eq_comm]

/-- Derivative of the conformal Hubble rate on the background time interval. -/
theorem hasDerivAt_hubble {D : Data} {t : ℝ} (ht : t ∈ D.I) :
    HasDerivAt (hubble D)
      ((deriv (deriv D.a) t*D.a t-deriv D.a t^2)/D.a t^2) t := by
  have d := hasDerivAt_of_contDiffOn D.isOpen_I D.contDiffOn_a ht
  have d' := hasDerivAt_of_contDiffOn D.isOpen_I
    (contDiffOn_deriv_of_contDiffOn D.isOpen_I D.contDiffOn_a) ht
  change HasDerivAt (deriv D.a / D.a) _ t
  simpa [pow_two] using d'.div d (D.a_pos _ ht).ne'

private theorem parts {D : Data} {x : E} (hx : x ∈ domain D) (i : Fin 4) :
    part (loga D) i x = (if i=0 then hubble D (x 0) else 0) ∧
    part (logs D) i x = (if i=0 then hubble D (x 0) else -(D.k/2*x i/psi D.k x)) := by
  have d := (hasDerivAt_of_contDiffOn D.isOpen_I D.contDiffOn_a (time_mem hx)).log
    (a_pos_of_mem hx).ne'
  have h := time_part d i
  change part (loga D) i x = _ at h
  refine ⟨h,?_⟩
  change (fderiv ℝ (fun z => loga D z-Real.log (psi D.k z)) x) (Pi.single i 1)=_
  rw [fderiv_fun_sub ((geometry hx).1.differentiableAt (by simp))
    ((hasFDerivAt_psi D.k x).log (psi_pos hx).ne').differentiableAt,sub_apply,
    ((hasFDerivAt_psi D.k x).log (psi_pos hx).ne').fderiv]
  change part (loga D) i x - _ = _
  rw [h]
  fin_cases i <;>
    norm_num [Pi.single_apply,proj_apply,smul_apply,add_apply,smul_eq_mul,hubble] <;> ring

private theorem sec_time {D : Data} {x : E} (hx : x ∈ domain D) :
    secondPartial (logs D) x 0 0 = deriv (hubble D) (x 0) ∧ lap (loga D) x=0 := by
  have h : (fun z => part (logs D) 0 z) =ᶠ[𝓝 x] fun z => hubble D (z 0) := by
    filter_upwards [(domain D).isOpen.mem_nhds hx] with z hz using by simpa using (parts hz 0).2
  have zero (i : Fin 4) (hi : i≠0) : secondPartial (loga D) x i i=0 := by
    have eq : (fun z => part (loga D) i z) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(domain D).isOpen.mem_nhds hx] with z hz using by
        simpa [hi] using (parts hz i).1
    change fderiv ℝ (fun z => part (loga D) i z) x (Pi.single i 1)=0
    rw [eq.fderiv_eq]; simp
  refine ⟨?_,by simp [lap,zero]⟩
  change fderiv ℝ (fun z => part (logs D) 0 z) x (Pi.single 0 1)=_
  rw [h.fderiv_eq]
  simpa only [part,ite_true] using
    time_part (hasDerivAt_hubble (D := D) (time_mem hx)).differentiableAt.hasDerivAt 0

private theorem ratio_log {D : Data} {x : E} (hx : x ∈ domain D) :
    Real.exp (2*(loga D x-logs D x)) = psi D.k x^2 ∧
    Real.exp (2*(logs D x-loga D x)) = (psi D.k x^2)⁻¹ := by
  unfold logs
  rw [sub_sub_cancel,show loga D x-Real.log (psi D.k x)-loga D x = -Real.log (psi D.k x) by ring,
    mul_neg,Real.exp_neg,two_mul,Real.exp_add,Real.exp_log (psi_pos hx),pow_two]
  exact ⟨rfl,rfl⟩

/-- At ε = 0 the family is the existing conformal FLRW metric on its chart. -/
theorem metricFamily_zero {D : Data} (hN : D.N=D.a) {x : E} (hx : x ∈ domain D) (u : E → ℝ) :
    metricFamily D u 0 x = (FLRW.metric D).coefficient x := by
  rw [metricFamily,IsotropicRicci.metric,coefficient_metric]
  congr 1
  funext i
  fin_cases i <;> norm_num [coefficients,hN,two_mul,Real.exp_add,Real.exp_sub,
    Real.exp_log (a_pos_of_mem hx),Real.exp_log (psi_pos hx),pow_two] <;> ring

/-- Covariant components of the trace-reversed dust source κρ(uᵢuⱼ+gᵢⱼ/2).
The density contrast is fractional and V is the perturbation of the spatial covelocity. -/
def dustSource (D : Data) (κ : ℝ) (ρ : ℝ → ℝ) (u δ : E → ℝ) (V : E → Fin 4 → ℝ)
    (e : ℝ) (x : E) (i j : Fin 4) :=
  let a := D.a (x 0)
  let v (b : Fin 4) := if b=0 then -a*Real.exp (e*u x) else e*V x b
  κ*ρ (x 0)*(1+e*δ x)*(v i*v j+(metricFamily D u e x i j)/2)

/-- Vanishing derivative of the Einstein–dust residual at a point. -/
def LinearizedDustAt (D : Data) (κ : ℝ) (ρ : ℝ → ℝ) (u δ : E → ℝ) (V : E → Fin 4 → ℝ)
    (x : E) : Prop := ∀ i j, HasDerivAt (fun e =>
      ricciOf (metricFamily D u e) x i j-dustSource D κ ρ u δ V e x i j) 0 0

private theorem coeff_family {D : Data} {x : E} (hx : x ∈ domain D) (u : E → ℝ)
    (e : ℝ) (i j : Fin 4) : metricFamily D u e x i j = if i=j then
      if i=0 then -(D.a (x 0)^2*Real.exp (2*(e*u x)))
      else D.a (x 0)^2/(psi D.k x)^2*Real.exp (-(2*(e*u x))) else 0 := by
  simp only [metricFamily,IsotropicRicci.metric,Matrix.diagonal_apply]
  split_ifs <;> subst_vars <;>
    simp [mul_add,mul_sub,two_mul,Real.exp_add,Real.exp_sub,Real.exp_neg,
      Real.exp_log (a_pos_of_mem hx),Real.exp_log (psi_pos hx),pow_two]

private theorem dust_deriv {D : Data} {x : E} (hx : x ∈ domain D)
    (κ : ℝ) (ρ : ℝ → ℝ) (u δ : E → ℝ) (V : E → Fin 4 → ℝ) (i j : Fin 4) :
    let a := D.a (x 0)
    let m := κ*ρ (x 0)*a^2/2
    HasDerivAt (fun e => dustSource D κ ρ u δ V e x i j)
      (if i=0 then if j=0 then m*(δ x+2*u x) else -κ*ρ (x 0)*a*V x j
       else if j=0 then -κ*ρ (x 0)*a*V x i
       else if i=j then m*(δ x-2*u x)/(psi D.k x)^2 else 0) 0 := by
  dsimp only [dustSource]
  simp_rw [coeff_family hx]
  split_ifs <;> subst_vars <;> try contradiction
  all_goals refine (DifferentiableAt.hasDerivAt ?_).congr_deriv ?_
  all_goals try fun_prop
  all_goals simp (disch := fun_prop) [deriv_fun_mul,deriv_fun_add]
  all_goals ring

/-- The two conformal dust Friedmann equations in the Hubble variable. -/
theorem conformal_dust_eq {D : Data} (hN : D.N=D.a) {κ : ℝ} {ρ : ℝ → ℝ}
    (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0)) {t : ℝ} (ht : t ∈ D.I) :
    κ*ρ t*D.a t^2 = 3*((hubble D t)^2+D.k) ∧
    2*deriv (hubble D) t+(hubble D t)^2+D.k=0 := by
  obtain ⟨h₁,h₂⟩ := (CosmologicalModels.isEinstein_conformal_iff hN κ 0 ρ 0).mp hB t ht
  simp only [Pi.zero_apply,mul_zero,zero_mul,add_zero] at h₁ h₂
  rw [(hasDerivAt_hubble ht).deriv]
  unfold hubble
  constructor
  · field_simp [(D.a_pos t ht).ne']
    linear_combination -3*h₁
  · field_simp [(D.a_pos t ht).ne']
    linear_combination h₂

private theorem slice_eq {D : Data} {x : E} (hx : x ∈ domain D) (u : E → ℝ) :
    sliceL (loga D) (logs D) u x = spatialLaplacian D.k u x := by
  simp only [sliceL,lap,gradDot,spatialLaplacian,(ratio_log hx).1,(parts hx _).2]
  norm_num
  field_simp [(psi_pos hx).ne']
  ring

/-- All sixteen components of the linearized Einstein–dust residual in a conformal FLRW
chart are equivalent to the scalar evolution, density constraint and momentum constraints.
The curvature signs enter through the background Einstein equations and spatial Laplacian. -/
theorem linearizedDustAt_iff {D : Data} (hN : D.N=D.a) {κ : ℝ} {ρ : ℝ → ℝ}
    (hB : (FLRW.metric D).IsEinstein κ 0 (perfectFluidStress D ρ 0)) {x : E} (hx : x ∈ domain D)
    {u : E → ℝ} (hu : ContDiffAt ℝ ∞ u x) (δ : E → ℝ) (V : E → Fin 4 → ℝ) :
    let H := hubble D (x 0)
    let a := D.a (x 0)
    LinearizedDustAt D κ ρ u δ V x ↔
      secondPartial u x 0 0 + 3*H*part u 0 x-2*D.k*u x=0 ∧
      κ*ρ (x 0)*a^2/2*δ x = spatialLaplacian D.k u x-3*H*(part u 0 x+H*u x)+3*D.k*u x ∧
      ∀ i : Fin 4, i≠0 → κ*ρ (x 0)*a*V x i = -2*(secondPartial u x i 0+H*part u i x) := by
  dsimp only
  obtain ⟨fg,sg⟩ := geometry hx
  obtain ⟨hsec,hl⟩ := sec_time hx
  have pt := parts hx
  have p0 := pt 0
  simp only [ite_true] at p0
  have hF (i : Fin 4) (hi : i≠0) : part (loga D) i x=0 := by simpa [hi] using (pt i).1
  have ht := p0.2.trans p0.1.symm
  let H := hubble D (x 0)
  let T := part u 0 x
  let TT := secondPartial u x 0 0
  let M := κ*ρ (x 0)*D.a (x 0)^2/2
  let P := psi D.k x^2
  let L := spatialLaplacian D.k u x
  let h' := deriv (hubble D) (x 0)
  have hp : P≠0 := pow_ne_zero _ (psi_pos hx).ne'
  have eq (i j : Fin 4) :
      HasDerivAt (fun e => ricciOf (metricFamily D u e) x i j-dustSource D κ ρ u δ V e x i j) 0 0 ↔
      (if i=0 then if j=0 then 3*TT+6*H*T+L-M*(δ x+2*u x)
        else 2*(H*part u j x+secondPartial u x j 0)+κ*ρ (x 0)*D.a (x 0)*V x j
       else if j=0 then 2*(H*part u i x+secondPartial u x i 0)+κ*ρ (x 0)*D.a (x 0)*V x i
       else if i=j then (-TT-6*H*T-4*(h'+2*H^2)*u x+L-M*(δ x-2*u x))/P else 0)=0 := by
    have d := (first_variation fg sg hu hF hl ht i j).sub (dust_deriv hx κ ρ u δ V i j)
    change HasDerivAt (fun e => ricciOf (metricFamily D u e) x i j-dustSource D κ ρ u δ V e x i j)
      _ 0 at d
    have hgrad : lap u x+gradDot (logs D) u x = L/P := by
      apply (eq_div_iff hp).mpr
      have h := slice_eq hx u
      rw [sliceL,(ratio_log hx).1] at h
      exact (mul_comm ..).trans h
    have e : deltaRicci (loga D) (logs D) u x i j - (if i=0 then if j=0 then M*(δ x+2*u x)
        else -κ*ρ (x 0)*D.a (x 0)*V x j else if j=0 then -κ*ρ (x 0)*D.a (x 0)*V x i
        else if i=j then M*(δ x-2*u x)/P else 0) =
        (if i=0 then if j=0 then 3*TT+6*H*T+L-M*(δ x+2*u x)
         else 2*(H*part u j x+secondPartial u x j 0)+κ*ρ (x 0)*D.a (x 0)*V x j
         else if j=0 then 2*(H*part u i x+secondPartial u x i 0)+κ*ρ (x 0)*D.a (x 0)*V x i
         else if i=j then (-TT-6*H*T-4*(h'+2*H^2)*u x+L-M*(δ x-2*u x))/P else 0) := by
      simp only [deltaRicci,p0.1,hsec,slice_eq hx,(ratio_log hx).2]
      split_ifs <;> subst_vars <;> dsimp only [H,TT,T,h',L,P] at * <;>
        first | (solve | ring) | (linear_combination hgrad)
    exact ⟨fun h => e.symm.trans (d.unique h),fun h => d.congr_deriv (e.trans h)⟩
  obtain ⟨ha,hb⟩ := conformal_dust_eq hN hB (time_mem hx)
  change _ = 3*(H^2+D.k) at ha
  change 2*h'+H^2+D.k=0 at hb
  have hm : 2*M=3*(H^2+D.k) := by dsimp [M]; linarith
  change (∀ i j, _) ↔ TT+3*H*T-2*D.k*u x=0 ∧
    M*δ x=L-3*H*(T+H*u x)+3*D.k*u x ∧ _
  simp_rw [eq]
  constructor
  · intro h
    have h₀ := h 0 0
    have h₁ := h 1 1
    norm_num [hp] at h₀ h₁
    refine ⟨?_,?_,?_⟩
    · linear_combination (h₀-h₁)/4+u x*(hm/2-hb/2)
    · linear_combination -(h₀+3*h₁)/4+u x*(hm/2-3*hb/2)
    · intro i hi
      have hi' := h i 0
      simp [hi] at hi'
      linarith
  · rintro ⟨he,hd,hv⟩ i j
    split_ifs <;> subst_vars
    all_goals try apply (div_eq_zero_iff.mpr (Or.inl ?_))
    all_goals first | rfl | (solve | linear_combination 3*he-hd-u x*hm) |
      (solve | linear_combination -he-hd+u x*(hm-2*hb)) |
      (solve | linear_combination hv _ (by assumption))

end ProjectAinos.GeneralRelativity.CurvedPerturbation
