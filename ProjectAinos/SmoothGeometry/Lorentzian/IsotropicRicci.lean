/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.ChristoffelCertificate
public import ProjectAinos.SmoothGeometry.Lorentzian.DiagonalMetric
public import ProjectAinos.SmoothGeometry.Lorentzian.Linearized
import Mathlib.Tactic

/-! # Ricci tensor with spatially isotropic diagonal coefficients

The lapse exp f and the spatial length scale exp s may depend on all four coordinates.
The table is computed from the coordinate Ricci tensor. This permits scalar perturbations
of either curved FLRW background in longitudinal gauge.
-/

@[expose] public section
noncomputable section
open Set Filter ContinuousLinearMap
open scoped ContDiff Topology
namespace ProjectAinos.SmoothGeometry.IsotropicRicci
open CoordinateMetric
local notation "E" => MinkowskiModel 3

/-- First coordinate derivative. -/
def part (f : E → ℝ) (i : Fin 4) (x : E) := fderiv ℝ f x (Pi.single i 1)

private def entries (f s : E → ℝ) (x : E) (i : Fin 4) :=
  if i=0 then -Real.exp (2*f x) else Real.exp (2*s x)

/-- The metric diag(−exp(2f),exp(2s),exp(2s),exp(2s)). -/
def metric (f s : E → ℝ) (x : E) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun i => if i=0 then -Real.exp (2*f x) else Real.exp (2*s x)

private def table (F S A : Fin 4 → ℝ) (B : ℝ) (k i j : Fin 4) : ℝ :=
  if k=0 then
    if i=0 then F j else if j=0 then F i else if i=j then B else 0
  else if i=0 then
    if j=0 then A k else if k=j then S 0 else 0
  else if j=0 then
    if k=i then S 0 else 0
  else (if k=i then S j else 0)+(if k=j then S i else 0)-(if i=j then S k else 0)

private def ratio (f s : E → ℝ) (x : E) := Real.exp (2*(f x-s x))

private def connection (f s : E → ℝ) (x : E) :=
  table (part f · x) (part s · x) (fun i => ratio f s x*part f i x) (ratio s f x*part s 0 x)

private theorem dscale {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (i : Fin 4) :
    part (fun y => Real.exp (2*f y)) i x = 2*Real.exp (2*f x)*part f i x := by
  have h := (hf.hasFDerivAt.const_mul 2).exp
  rw [part,h.fderiv]
  simp [part,smul_apply,smul_eq_mul]
  ring

private theorem ratio_eq (f s : E → ℝ) (x : E) :
    ratio f s x = Real.exp (2*f x)/Real.exp (2*s x) := by
  rw [ratio,mul_sub,Real.exp_sub]

private theorem gamma_eq {f s : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hs : DifferentiableAt ℝ s x) (k i j : Fin 4) :
    christoffelOf (metric f s) x k i j = connection f s x k i j := by
  have he (n : Fin 4) : entries f s x n ≠ 0 := by
    unfold entries
    split <;> simp [Real.exp_ne_zero]
  change christoffelOf (fun z => Matrix.diagonal (entries f s z)) x k i j = _
  rw [christoffelOf_diagonal _ _ he]
  have hd (m n : Fin 4) : fderiv ℝ (fun z => entries f s z n) x (Pi.single m 1) =
      if n=0 then -2*Real.exp (2*f x)*part f m x else 2*Real.exp (2*s x)*part s m x := by
    by_cases hn : n=0
    · simp only [entries,hn,↓reduceIte,fderiv_fun_neg,neg_apply]
      change -part (fun y => Real.exp (2*f y)) m x = _
      rw [dscale hf]
      ring
    · simp only [entries,hn,↓reduceIte]
      exact dscale hs _
  simp_rw [hd]
  simp only [connection,table,entries,ratio_eq]
  split_ifs <;> subst_vars <;> simp_all <;> field_simp

private theorem dRatio {f s : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hs : DifferentiableAt ℝ s x) (m : Fin 4) :
    part (ratio f s) m x = 2*ratio f s x*(part f m x-part s m x) := by
  change part (fun y => Real.exp (2*((f-s) y))) m x = _
  rw [dscale (hf.sub hs)]
  simp only [ratio,Pi.sub_apply,part,fderiv_sub hf hs,sub_apply]

private theorem conn_part {f s : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hs : ContDiffAt ℝ ∞ s x) (m k i j : Fin 4) :
    part (fun z => connection f s z k i j) m x = table
      (secondPartial f x m) (secondPartial s x m)
      (fun n => ratio f s x*(secondPartial f x m n+
        2*(part f m x-part s m x)*part f n x))
      (ratio s f x*(secondPartial s x m 0+2*(part s m x-part f m x)*part s 0 x)) k i j := by
  have dp {u : E → ℝ} (hu : ContDiffAt ℝ ∞ u x) (n : Fin 4) :=
    (contDiffAt_fderiv_apply hu (Pi.single n 1)).differentiableAt (by simp)
  have Da {u v : E → ℝ} (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x) (n : Fin 4) :
      part (fun z => ratio u v z*part u n z) m x =
        ratio u v x*(secondPartial u x m n+2*(part u m x-part v m x)*part u n x) := by
    have h : DifferentiableAt ℝ (ratio u v) x := by
      unfold ratio
      exact (((hu.differentiableAt (by simp)).sub (hv.differentiableAt (by simp))).const_mul 2).exp
    have hpart : DifferentiableAt ℝ (part u n) x := dp hu n
    rw [part,fderiv_fun_mul h hpart]
    simp only [add_apply,smul_apply,smul_eq_mul]
    change ratio u v x*secondPartial u x m n+part u n x*part (ratio u v) m x=_
    rw [dRatio (hu.differentiableAt (by simp)) (hv.differentiableAt (by simp))]
    ring
  unfold connection table
  split_ifs <;> first | apply Da hf hs | apply Da hs hf | rfl |
    (simp [part,secondPartial,fderiv_fun_add,fderiv_fun_sub,dp hs,add_apply,sub_apply])

/-- Ricci components expressed in the first and second coordinate derivatives
of the two logarithmic scale factors. -/
def ricciTable (f s : E → ℝ) (x : E) (i j : Fin 4) : ℝ :=
  let F := fun a => part f a x
  let S := fun a => part s a x
  let H := secondPartial f x
  let D := secondPartial s x
  let L (d : Fin 4 → Fin 4 → ℝ) := d 1 1+d 2 2+d 3 3
  let p (v w : Fin 4 → ℝ) := v 1*w 1+v 2*w 2+v 3*w 3
  if i=0 then if j=0 then -3*(D 0 0+S 0^2-F 0*S 0)+
    Real.exp (2*(f x-s x))*(L H+p F F+p F S)
    else 2*(S 0*F j-D j 0)
  else if j=0 then 2*(S 0*F i-D i 0)
  else (if i=j then Real.exp (2*(s x-f x))*(D 0 0+3*S 0^2-F 0*S 0)-
    L D-p S S-p S F else 0)-D i j-H i j+S i*S j-F i*F j+S i*F j+S j*F i

/-- The isotropic Ricci formula is the coordinate Ricci tensor of the metric. -/
theorem ricci_eq {f s : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hs : ContDiffAt ℝ ∞ s x) (i j : Fin 4) :
    ricciOf (metric f s) x i j = ricciTable f s x i j := by
  rw [ricciOf_eq_ricciOfChristoffel (G := connection f s) (by
    filter_upwards [eventually_differentiableAt hf,eventually_differentiableAt hs]
      with z h₁ h₂ using gamma_eq h₁ h₂)]
  have hd (m k a b : Fin 4) : fderiv ℝ (fun z => connection f s z k a b) x (Pi.single m 1) =
      _ := conn_part hf hs m k a b
  have hA : Real.exp (2*(s x-f x)) = (Real.exp (2*(f x-s x)))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have symmF := secondPartial_comm (hf.of_le (m := 2) (by simp))
  have symmS := secondPartial_comm (hs.of_le (m := 2) (by simp))
  unfold ricciOfChristoffel
  simp_rw [hd]
  have sum4 (a : Fin 4 → ℝ) := Fin.sum_univ_four a
  simp_rw [sum4]
  fin_cases i <;> fin_cases j <;>
    norm_num [connection,table,ratio,ricciTable,hA]
  all_goals try simp only [symmF 1 0,symmF 2 0,symmF 3 0,symmF 2 1,symmF 3 1,symmF 3 2,
      symmS 1 0,symmS 2 0,symmS 3 0,symmS 2 1,symmS 3 1,symmS 3 2]
  all_goals field_simp; ring

end ProjectAinos.SmoothGeometry.IsotropicRicci
