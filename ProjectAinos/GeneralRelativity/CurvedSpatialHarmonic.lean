/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.CurvedPerturbation
public import ProjectAinos.SpecialFunctions.HarmonicPolynomial
import Mathlib.Tactic

/-! # The stereographic Laplacian on solid harmonics times radial profiles

For y = 1+k|x|²/4 the ambient quadric coordinate is s = 2/y−1.
Multiplying a solid harmonic of degree ℓ by y⁻ˡ F(s) puts the unit-curvature
Laplacian into Gegenbauer's differential equation with the appropriate curvature sign.
-/

@[expose] public section
noncomputable section
open Set Filter ContinuousLinearMap MvPolynomial
open scoped ContDiff Topology
namespace ProjectAinos.GeneralRelativity.CurvedPerturbation
open SmoothGeometry CoordinateMetric FLRW IsotropicRicci
open ProjectAinos.SpecialFunctions.HarmonicPolynomial
local notation "E" => MinkowskiModel 3
private abbrev P := MvPolynomial (Fin 3) ℝ
private def val (p : P) (x : E) := eval (fun j : Fin 3 => x j.succ) p
private abbrev Xc (i : Fin 4) : E →L[ℝ] ℝ := proj i

private theorem val_C (a : ℝ) : val (C a) = fun _ => a := by ext; simp [val]
private theorem val_add (p q : P) : val (p+q) = fun x => val p x+val q x := by
  ext; simp [val]
private theorem val_X (p : P) (j : Fin 3) : val (p*X j) = fun x => val p x*(Xc j.succ) x := by
  ext; simp [val,Xc]

private theorem smooth_val (p : P) : ContDiff ℝ ∞ (val p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [val_C]; exact contDiff_const
  | add p q hp hq => rw [val_add]; exact hp.add hq
  | mul_X p j hp => rw [val_X]; exact hp.mul (Xc j.succ).contDiff

private theorem dv (p : P) (i : Fin 4) (x : E) :
    part (val p) i x = Fin.cases 0 (fun j => val (pderiv j p) x) i := by
  have d (q : P) := (smooth_val q).differentiable (by simp) x
  induction p using MvPolynomial.induction_on with
  | C a => rw [val_C]; cases i using Fin.cases <;> simp [part,val]
  | add p q hp hq =>
    rw [val_add,part,fderiv_fun_add (d p) (d q),add_apply]
    change part (val p) i x+part (val q) i x=_
    rw [hp,hq]; cases i using Fin.cases <;> simp [val]
  | mul_X p j hp =>
    rw [val_X,part,fderiv_fun_mul (d p) (Xc j.succ).differentiableAt,add_apply,smul_apply,
      smul_apply,(Xc j.succ).hasFDerivAt.fderiv,smul_eq_mul,smul_eq_mul]
    change val p x*(Xc j.succ) (Pi.single i 1)+x j.succ*part (val p) i x=_
    rw [hp]
    cases i using Fin.cases with
    | zero => simp [Xc,Pi.single_apply]
    | succ m =>
      simp [Xc,Pi.single_apply,val,pderiv_X]
      split_ifs <;> simp_all

private theorem ppsi (k : ℝ) (i : Fin 4) (x : E) :
    part (psi k) i x = if i=0 then 0 else k/2*x i := by
  rw [part,fderiv_psi]
  fin_cases i <;> norm_num [dotSpace,Pi.single_apply]

private def profile (p : P) (k : ℝ) (W : ℝ → ℝ) (x : E) := val p x*W (psi k x)

private theorem dprofile (p : P) (k : ℝ) {W : ℝ → ℝ} {x : E}
    (hW : DifferentiableAt ℝ W (psi k x)) (i : Fin 4) :
    part (profile p k W) i x = part (val p) i x*W (psi k x)+
      val p x*deriv W (psi k x)*part (psi k) i x := by
  have h := ((smooth_val p).differentiable (by simp) x).hasFDerivAt.mul
    (hW.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_psi k x))
  change HasFDerivAt (profile p k W) _ x at h
  rw [part,h.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,Function.comp_apply]
  change val p x*(deriv W (psi k x)*_)+W (psi k x)*part (val p) i x=_
  simp only [part,(hasFDerivAt_psi k x).fderiv,smul_apply,add_apply,smul_eq_mul]
  ring

private theorem spatial_profile {l : ℕ} (p : harmonics 3 l) (k : ℝ) {W : ℝ → ℝ} {x : E}
    (hW : ContDiffAt ℝ ∞ W (psi k x)) :
    let y := psi k x
    spatialLaplacian k (profile p.val.val k W) x =
      k*val p.val.val x*(y^2*(y-1)*deriv (deriv W) y+
        y*(((l : ℝ)+1/2)*y+1)*deriv W y-(l : ℝ)*y/2*W y) := by
  let q := p.val.val
  let y := psi k x
  let b := W y
  let d := deriv W y
  let dd := deriv (deriv W) y
  have hd := hW.differentiableAt (by simp)
  have hd' := (hW.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hev := ((contDiff_psi k).continuous.continuousAt (x := x)).tendsto.eventually
    ((hW.of_le (m := 1) (by simp)).eventually (by simp))
  have dp (m : Fin 3) : part (profile q k W) m.succ x =
      val (pderiv m q) x*b+val q x*d*(k/2*x m.succ) := by
    rw [dprofile _ _ hd,dv,ppsi]; simp [b,d,y]
  have ds (m : Fin 3) : secondPartial (profile q k W) x m.succ m.succ =
      val (pderiv m (pderiv m q)) x*b+2*val (pderiv m q) x*d*(k/2*x m.succ)+
        val q x*(dd*(k/2*x m.succ)^2+d*(k/2)) := by
    have eq : part (profile q k W) m.succ =ᶠ[𝓝 x] fun z =>
        profile (pderiv m q) k W z+profile q k (deriv W) z*(k/2*z m.succ) := by
      filter_upwards [hev] with z hz
      rw [dprofile _ _ (hz.differentiableAt one_ne_zero),dv,ppsi]
      simp [profile,mul_assoc]
    have D (r : P) {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f y) :
        DifferentiableAt ℝ (profile r k f) x :=
      ((smooth_val r).differentiable (by simp) x).mul
        (hf.comp x (hasFDerivAt_psi k x).differentiableAt)
    have c : DifferentiableAt ℝ (fun z : E => k/2*z m.succ) x := by fun_prop
    change fderiv ℝ (part (profile q k W) m.succ) x (Pi.single m.succ 1)=_
    rw [eq.fderiv_eq,fderiv_fun_add (D _ hd) (show DifferentiableAt ℝ
      (fun z : E => profile q k (deriv W) z*(k/2*z m.succ)) x from (D _ hd').mul c),
      add_apply,fderiv_fun_mul (D _ hd') c,add_apply,smul_apply,smul_apply,smul_eq_mul,smul_eq_mul]
    have cd : fderiv ℝ (fun z : E => k/2*z m.succ) x (Pi.single m.succ 1) = k/2 := by
      change (fderiv ℝ (fun z => k/2*(Xc m.succ) z) x) (Pi.single m.succ 1)=_
      rw [fderiv_const_mul (Xc m.succ).differentiableAt,(Xc m.succ).hasFDerivAt.fderiv]
      simp [Xc,smul_apply]
    rw [cd]
    change part (profile (pderiv m q) k W) m.succ x+
      (profile q k (deriv W) x*(k/2)+k/2*x m.succ*part (profile q k (deriv W)) m.succ x)=_
    rw [dprofile _ _ hd,dprofile _ _ hd',dv,dv,ppsi]
    simp [b,d,dd,y,profile]
    ring
  have lapQ : ∑ i : Fin 3, val (pderiv i (pderiv i q)) x=0 := by
    have h := congrArg (eval (fun j : Fin 3 => x j.succ)) p.property
    simpa [val,q,laplacian,LinearMap.sum_apply] using h
  have eu : ∑ i : Fin 3, x i.succ*val (pderiv i q) x=(l : ℝ)*val q x := by
    simpa [val,q,nsmul_eq_mul] using congrArg (eval (fun j : Fin 3 => x j.succ))
      p.val.property.sum_X_mul_pderiv
  simp only [Fin.sum_univ_three] at lapQ eu
  have hR : k*(x 1^2+x 2^2+x 3^2)=4*(y-1) := by dsimp [y,psi]; ring
  dsimp only
  change spatialLaplacian k (profile q k W) x = _
  unfold spatialLaplacian
  change y^2*(secondPartial _ x (0 : Fin 3).succ (0 : Fin 3).succ+
    secondPartial _ x (1 : Fin 3).succ (1 : Fin 3).succ+
    secondPartial _ x (2 : Fin 3).succ (2 : Fin 3).succ)-
    y*(k/2)*(x 1*part _ (0 : Fin 3).succ x+x 2*part _ (1 : Fin 3).succ x+
      x 3*part _ (2 : Fin 3).succ x)=_
  rw [ds,ds,ds,dp,dp,dp]
  change _ = k*val q x*(y^2*(y-1)*dd+y*(((l : ℝ)+1/2)*y+1)*d-(l : ℝ)*y/2*b)
  simp only [show (0 : Fin 3).succ=(1 : Fin 4) from rfl,show (1 : Fin 3).succ=(2 : Fin 4) from rfl,
    show (2 : Fin 3).succ=(3 : Fin 4) from rfl] at eu ⊢
  linear_combination y^2*b*lapQ+(y^2*d*k-y*(k/2)*b)*eu+
    (val q x*(y^2*dd*k/4-y*d*k/4))*hR

/-- The zeroth ambient coordinate of the spherical or hyperboloid lift. -/
def chartCoordinate (k : ℝ) (x : E) := 2/psi k x-1

/-- The spatial mode with solid angular harmonic p and radial profile F in the
zeroth ambient coordinate. -/
def chartHarmonic {l : ℕ} (p : harmonics 3 l) (k : ℝ) (F : ℝ → ℝ) (x : E) :=
  eval (fun j : Fin 3 => x j.succ) p.val.val*(psi k x)^(-(l : ℤ))*F (chartCoordinate k x)

private abbrev c (y : ℝ) := 2/y-1
private abbrev wt (l : ℕ) (y : ℝ) := y^(-(l : ℤ))
private def Wt (l : ℕ) (F : ℝ → ℝ) (y : ℝ) := wt l y*F (c y)
private theorem chart_eq {l : ℕ} (p : harmonics 3 l) (k : ℝ) (F : ℝ → ℝ) :
    chartHarmonic p k F = profile p.val.val k (Wt l F) := by
  funext x
  simp [chartHarmonic,profile,Wt,val,c,wt,chartCoordinate,mul_assoc]

private theorem dc {y : ℝ} (hy : y≠0) : HasDerivAt c (-2/y^2) y := by
  apply (((hasDerivAt_const y (2 : ℝ)).div (hasDerivAt_id' y) hy).sub_const 1).congr_deriv
  simp
private theorem dw (l : ℕ) {y : ℝ} (hy : y≠0) :
    HasDerivAt (wt l) (-(l : ℝ)*wt l y/y) y := by
  apply (hasDerivAt_zpow (-(l : ℤ)) y (Or.inl hy)).congr_deriv
  simp [wt,zpow_sub₀ hy,div_eq_mul_inv,mul_assoc]

private def Wt' (l : ℕ) (F : ℝ → ℝ) (y : ℝ) :=
  -(l : ℝ)*wt l y/y*F (c y)-2*wt l y/y^2*deriv F (c y)

private theorem dWt (l : ℕ) {F : ℝ → ℝ} {y : ℝ} (hy : y≠0)
    (hf : DifferentiableAt ℝ F (c y)) : HasDerivAt (Wt l F) (Wt' l F y) y := by
  apply ((dw l hy).mul (hf.hasDerivAt.comp y (dc hy))).congr_deriv
  dsimp [Wt']; ring

private theorem ddWt (l : ℕ) {F : ℝ → ℝ} {y : ℝ} (hy : y≠0) (hf : ContDiffAt ℝ ∞ F (c y)) :
    deriv (deriv (Wt l F)) y=wt l y*((l : ℝ)*(l+1)/y^2*F (c y)+
      4*(l+1)/y^3*deriv F (c y)+4/y^4*deriv (deriv F) (c y)) := by
  have near := (dc hy).continuousAt.tendsto.eventually ((hf.of_le (m := 1) (by simp)).eventually
    (by simp))
  have eq : deriv (Wt l F) =ᶠ[𝓝 y] Wt' l F := by
    filter_upwards [near,isOpen_ne.mem_nhds hy] with t ht ht'
    exact (dWt l ht' (ht.differentiableAt one_ne_zero)).deriv
  have hF := (hf.differentiableAt (by simp)).hasDerivAt.comp y (dc hy)
  have hD := ((hf.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt.comp y
    (dc hy)
  have t₁ := (((dw l hy).const_mul (-(l : ℝ))).div (hasDerivAt_id' y) hy).mul hF
  have t₂ := (((dw l hy).const_mul 2).div ((hasDerivAt_id' y).pow 2) (pow_ne_zero 2 hy)).mul hD
  rw [eq.deriv_eq,(show HasDerivAt (Wt' l F) _ y from t₁.sub t₂).deriv]
  dsimp only [Function.comp_apply,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,Pi.neg_apply]
  field_simp [hy]; ring

private theorem smooth_Wt (l : ℕ) {F : ℝ → ℝ} {y : ℝ} (hy : y≠0) (hf : ContDiffAt ℝ ∞ F (c y)) :
    ContDiffAt ℝ ∞ (Wt l F) y := by
  have hw : ContDiffAt ℝ ∞ (wt l) y := by
    change ContDiffAt ℝ ∞ (fun t : ℝ => t^(-(l : ℤ))) y
    simpa only [zpow_neg,zpow_natCast] using
      (show ContDiffAt ℝ ∞ (fun t : ℝ => (t^l)⁻¹) y from
        (contDiffAt_id.pow l).inv (pow_ne_zero _ hy))
  apply hw.mul
  exact hf.comp _ ((contDiffAt_const.div contDiffAt_id hy).sub contDiffAt_const)

/-- The stereographic chart gives the Gegenbauer radial operator, with the opposite sign
on the open hyperbolic slice. -/
theorem chartHarmonic_laplacian {l : ℕ} (p : harmonics 3 l) (k : ℝ) {F : ℝ → ℝ} {x : E}
    (hx : psi k x ≠ 0) (hf : ContDiffAt ℝ ∞ F (chartCoordinate k x)) :
    let s := chartCoordinate k x
    spatialLaplacian k (chartHarmonic p k F) x =
      k*(eval (fun j : Fin 3 => x j.succ) p.val.val)*(psi k x)^(-(l : ℤ))*
        ((1-s^2)*deriv (deriv F) s-(2*l+3)*s*deriv F s-(l : ℝ)*(l+2)*F s) := by
  rw [chart_eq,spatial_profile p k (smooth_Wt l hx hf)]
  dsimp only
  rw [ddWt l hx hf,(dWt l hx (hf.differentiableAt (by simp))).deriv]
  dsimp only [Wt,Wt',wt,c,val,chartCoordinate]
  field_simp [hx]; ring

/-- Chart harmonics are smooth at regular chart points where the profile is smooth. -/
theorem smooth_chartHarmonic {l : ℕ} (p : harmonics 3 l) (k : ℝ) {F : ℝ → ℝ} {x : E}
    (hx : psi k x ≠ 0) (hf : ContDiffAt ℝ ∞ F (chartCoordinate k x)) :
    ContDiffAt ℝ ∞ (chartHarmonic p k F) x := by
  rw [chart_eq]
  exact (smooth_val _).contDiffAt.mul ((smooth_Wt l hx hf).comp _ (contDiff_psi k).contDiffAt)

/-- Spatial eigenmodes are independent of conformal time. -/
theorem chartHarmonic_time {l : ℕ} (p : harmonics 3 l) (k : ℝ) {F : ℝ → ℝ} {x : E}
    (hx : psi k x ≠ 0) (hf : ContDiffAt ℝ ∞ F (chartCoordinate k x)) :
    ∀ᶠ y in 𝓝 x, part (chartHarmonic p k F) 0 y=0 := by
  rw [chart_eq]
  have near := (contDiff_psi k).continuous.continuousAt (x := x) |>.tendsto.eventually
    (((smooth_Wt l hx hf).of_le (m := 1) (by simp)).eventually (by simp))
  filter_upwards [near] with t ht
  simp [dprofile _ _ (ht.differentiableAt one_ne_zero),dv,ppsi]

end ProjectAinos.GeneralRelativity.CurvedPerturbation
