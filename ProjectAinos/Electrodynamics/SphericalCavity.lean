/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.CavityModes
public import ProjectAinos.SpecialFunctions.SphericalBesselZeros
import Mathlib.Tactic

/-! # A conducting spherical cavity

The vector potential (−y,x,0) cos(kt) F(x²+y²+z²) is smooth throughout the ball.
The radial profile is proportional to j₁(kr)/r. At a positive zero of j₁ the tangential
electric field and normal magnetic field vanish on the entire conducting sphere.
-/

@[expose] public section
noncomputable section
open scoped ContDiff
namespace ProjectAinos.Electrodynamics.CavityModes
open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity
open ProjectAinos.SpecialFunctions.Bessel

private abbrev X (j : Fin 4) := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) j
private def rs (x : Spacetime) := x 1^2+x 2^2+x 3^2
private def mode (a b : ℝ → ℝ) (x : Spacetime) := a (x 0)*b (rs x)

private theorem smooth {a b : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (mode a b) := by unfold mode rs; fun_prop

private theorem dx (j i : Fin 4) (x : Spacetime) :
    partialAt (X j) i x = if i=j then 1 else 0 := by
  rw [partialAt,(X j).hasFDerivAt.fderiv]
  simp [X,Pi.single_apply,eq_comm]

private theorem dm {a b : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (i : Fin 4) (x : Spacetime) : partialAt (mode a b) i x =
    if i=0 then mode (deriv a) b x else 2*x i*mode a (deriv b) x := by
  have dr := (((X 1).hasFDerivAt (x := x)).pow 2).add (((X 2).hasFDerivAt).pow 2)
  have ds := dr.add (((X 3).hasFDerivAt).pow 2)
  change HasFDerivAt rs _ x at ds
  have h := (((ha.differentiable (by simp) _).hasDerivAt).comp_hasFDerivAt x
    (X 0).hasFDerivAt).mul (((hb.differentiable (by simp) _).hasDerivAt).comp_hasFDerivAt x ds)
  change HasFDerivAt (mode a b) _ x at h
  rw [partialAt,h.fderiv]
  fin_cases i <;> norm_num [add_apply,smul_apply,smul_eq_mul,X,Pi.single_apply,
    Function.comp_apply,mode] <;> ring

private def componentMode (a b : ℝ → ℝ) (j : Fin 4) (x : Spacetime) := x j*mode a b x

private theorem dc {a b : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (j i : Fin 4) (x : Spacetime) : partialAt (componentMode a b j) i x =
    (if i=j then mode a b x else 0)+
      if i=0 then componentMode (deriv a) b j x else 2*x i*componentMode a (deriv b) j x := by
  change partialAt (fun t => (X j) t*mode a b t) i x = _
  rw [partialAt_mul (X j).differentiableAt ((smooth ha hb).differentiable (by simp) _),dx,
    dm ha hb]
  split_ifs <;> simp [componentMode,X] <;> ring

private theorem smoothC {a b : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (j : Fin 4) :
    ContDiff ℝ ∞ (componentMode a b j) := (X j).contDiff.mul (smooth ha hb)

private theorem wave {a b : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (j : Fin 4) (hj : j≠0) (x : Spacetime) :
    box (componentMode a b j) x = x j*(-deriv (deriv a) (x 0)*b (rs x)+
      a (x 0)*(4*rs x*deriv (deriv b) (rs x)+10*deriv b (rs x))) := by
  have D {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :=
    (show ContDiff ℝ (∞+1) f by simpa using hf).deriv'
  have ti : partialAt (componentMode a b j) 0 = componentMode (deriv a) b j := by
    funext y
    simp [dc ha hb,Ne.symm hj]
  have sp (i : Fin 4) (hi : i≠0) :
      partialAt (partialAt (componentMode a b j) i) i x =
        (if i=j then 4*x i*mode a (deriv b) x else 0)+
        2*componentMode a (deriv b) j x+4*x i^2*componentMode a (deriv (deriv b)) j x := by
    have h {f : Spacetime → ℝ} (hf : ContDiff ℝ ∞ f) :
        partialAt (fun y => 2*((X i) y*f y)) i x = 2*(f x+x i*partialAt f i x) := by
      rw [partialAt_const_mul (f := fun y => (X i) y*f y) 2
        ((X i).differentiableAt.mul (hf.differentiable (by simp) _)),
        partialAt_mul (X i).differentiableAt (hf.differentiable (by simp) _),dx]
      simp [X,add_comm]
    have hs : partialAt (componentMode a b j) i = fun y =>
        (if i=j then mode a b y else 0)+2*((X i) y*componentMode a (deriv b) j y) := by
      funext y
      simp [dc ha hb,hi,mul_assoc,X]
    rw [hs]
    have hd := (smoothC ha (D hb) j).differentiable (by simp) x
    by_cases h' : i=j
    · subst j
      simp only [↓reduceIte]
      rw [partialAt_add (g := fun y => 2*((X i) y*componentMode a (deriv b) i y))
        ((smooth ha hb).differentiable (by simp) _) (((X i).differentiableAt.mul
        hd).const_mul _),h (smoothC ha (D hb) _),dc ha (D hb),dm ha hb]
      simp [hi,componentMode]
      ring
    · simp only [h',↓reduceIte,zero_add]
      rw [h (smoothC ha (D hb) _),dc ha (D hb)]
      simp [h',hi]
      ring
  rw [box,Fin.sum_univ_three]
  change -partialAt (partialAt _ 0) 0 x+(partialAt (partialAt _ 1) 1 x+
    partialAt (partialAt _ 2) 2 x+partialAt (partialAt _ 3) 3 x)=_
  rw [ti,dc (D ha) hb,sp 1 (by decide),sp 2 (by decide),sp 3 (by decide)]
  fin_cases j <;> norm_num [componentMode,mode,rs] at * <;> ring

private abbrev oscillation (k t : ℝ) := Real.cos (k*t)
private abbrev profile (k : ℝ) := radialProfile (5/2) k
private abbrev C (k : ℝ) (j : Fin 4) := componentMode (oscillation k) (profile k) j

/-- A transverse electric dipole mode on a ball. -/
def sphereMode (k : ℝ) : Potential := potentialOf (fun _ => 0)
  fun x =>
    let b := Real.cos (k*x 0)*radialProfile (5/2) k (x 1^2+x 2^2+x 3^2)
    ![-(x 2*b),x 1*b,0]

private theorem components (k : ℝ) :
    potentialComponent (sphereMode k) 0 = (fun _ => 0) ∧
    potentialComponent (sphereMode k) 1 = (fun x => -C k 2 x) ∧
    potentialComponent (sphereMode k) 2 = C k 1 ∧
    potentialComponent (sphereMode k) 3 = (fun _ => 0) := by
  refine ⟨(potentialComponent_potentialOf_zero ..).trans (by simp),?_,?_,?_⟩
  · exact (potentialComponent_potentialOf_succ _ _ 0).trans rfl
  · exact (potentialComponent_potentialOf_succ _ _ 1).trans rfl
  · exact (potentialComponent_potentialOf_succ _ _ 2).trans rfl

private theorem ha (k : ℝ) : ContDiff ℝ ∞ (oscillation k) := by unfold oscillation; fun_prop
private theorem hb (k : ℝ) : ContDiff ℝ ∞ (profile k) := contDiff_radialProfile ..
private theorem smoothA (k : ℝ) : ContDiff ℝ 2 (sphereMode k) := by
  apply contDiff_potentialOf contDiff_const
  intro i
  fin_cases i
  · exact (smoothC (ha k) (hb k) 2).neg.of_le (show (2 : ℕ∞ω) ≤ ∞ by norm_num)
  · exact (smoothC (ha k) (hb k) 1).of_le (show (2 : ℕ∞ω) ≤ ∞ by norm_num)
  · exact contDiff_const

/-- These vector potentials solve the vacuum Maxwell equations, including at the center. -/
theorem sphereMode_maxwell (k : ℝ) (x : Spacetime) : VacuumMaxwellAt (sphereMode k) x := by
  obtain ⟨c₀,c₁,c₂,c₃⟩ := components k
  have hdiv y : lorenzDivergence (sphereMode k) y=0 := by
    rw [lorenzDivergence,Fin.sum_univ_three]
    change -partialAt (potentialComponent _ 0) 0 y+(partialAt (potentialComponent _ 1) 1 y+
      partialAt (potentialComponent _ 2) 2 y+partialAt (potentialComponent _ 3) 3 y)=0
    rw [c₀,c₁,c₂,c₃,partialAt_neg,partialAt_const,partialAt_const]
    rw [dc (ha k) (hb k),dc (ha k) (hb k)]
    norm_num [componentMode]
    ring
  have w (y : Spacetime) (j : Fin 4) (hj : j≠0) : box (C k j) y=0 := by
    rw [wave (ha k) (hb k) _ hj]
    have h := radialProfile_equation (5/2) k (rs y)
    have dt : deriv (oscillation k) = fun t => -Real.sin (k*t)*k := by
      funext t
      simpa using (((hasDerivAt_id' t).const_mul k).cos.deriv)
    rw [dt]
    have dd := ((((hasDerivAt_id' (y 0)).const_mul k).sin.neg).mul_const k).deriv
    simp only [Pi.neg_apply,mul_one] at dd
    rw [dd]
    linear_combination y j*Real.cos (k*y 0)*h
  have z (y : Spacetime) : box (fun _ => 0) y=0 := by
    have e (i : Fin 4) : partialAt (fun _ => 0) i = fun _ => 0 := funext (partialAt_const 0 i)
    simp [box,e]
  apply (vacuumMaxwellAt_iff_box (smoothA k) hdiv).2 _ x
  intro y i
  fin_cases i
  · exact (congrArg (fun f => box f y) c₀).trans (z y)
  · change box (potentialComponent _ 1) y=0
    rw [c₁,box_neg,w _ _ (by decide),neg_zero]
  · exact (congrArg (fun f => box f y) c₂).trans (w _ _ (by decide))
  · exact (congrArg (fun f => box f y) c₃).trans (z y)

private theorem fields (k : ℝ) (x : Spacetime) :
    let E := electricField (fieldTensor (sphereMode k))
    let B := magneticField (fieldTensor (sphereMode k))
    E 0 x = x 2*mode (deriv (oscillation k)) (profile k) x ∧
    E 1 x = -(x 1*mode (deriv (oscillation k)) (profile k) x) ∧ E 2 x=0 ∧
    x 1*B 0 x+x 2*B 1 x+x 3*B 2 x = 2*x 3*mode (oscillation k) (profile k) x ∧
    B 2 x = 2*mode (oscillation k) (profile k) x+
      2*(x 1^2+x 2^2)*mode (oscillation k) (deriv (profile k)) x := by
  obtain ⟨c₀,c₁,c₂,c₃⟩ := components k
  have hA := (smoothA k).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have he i := electricField_of_coulomb hA (fun y => congrFun c₀ y) i x
  obtain ⟨b₀,b₁,b₂⟩ := magneticField_fieldTensor_apply hA x
  dsimp only
  rw [he,he,he,b₀,b₁,b₂]
  change -partialAt (potentialComponent _ 1) 0 x=_ ∧ -partialAt (potentialComponent _ 2) 0 x=_ ∧
    -partialAt (potentialComponent _ 3) 0 x=_ ∧ _
  simp only [c₁,c₂,c₃,partialAt_const,partialAt_neg,C,dc (ha k) (hb k)]
  norm_num [componentMode]
  constructor <;> ring

/-- On a conducting sphere all electric components and the normal magnetic component
vanish at a dipole eigenfrequency. -/
theorem sphereMode_wall {k R : ℝ} (hk : 0 < k) (hR : 0 < R)
    (hz : sphericalJ 1 ((k*R : ℝ) : ℂ) = 0) (x : Spacetime)
    (hx : x 1^2+x 2^2+x 3^2=R^2) :
    (∀ i, electricField (fieldTensor (sphereMode k)) i x=0) ∧
      ∑ i : Fin 3, x i.succ*magneticField (fieldTensor (sphereMode k)) i x=0 := by
  obtain ⟨e₀,e₁,e₂,hn,_⟩ := fields k x
  have h : profile k (rs x)=0 := by
    change radialProfile (5/2) k (x 1^2+x 2^2+x 3^2)=0
    rw [hx]; exact radialProfile_dipole_zero hk hR hz
  refine ⟨?_,?_⟩
  · intro i
    fin_cases i
    · simpa [mode,h] using e₀
    · simpa [mode,h] using e₁
    · exact e₂
  · simpa [Fin.sum_univ_three,mode,h,add_assoc] using hn

/-- Every positive radius admits arbitrarily high conducting dipole frequencies.
The magnetic field at the center at time zero witnesses a nonzero mode. -/
theorem exists_sphereMode {R : ℝ} (hR : 0 < R) (A : ℝ) :
    ∃ k : ℝ, A < k ∧ 0 < k ∧ sphericalJ 1 ((k*R : ℝ) : ℂ)=0 ∧
      0 < magneticField (fieldTensor (sphereMode k)) 2 0 := by
  obtain ⟨r,hA,hr,hz⟩ := sphericalJ_zeros_unbounded 1 (A*R)
  let k := r/R
  refine ⟨k,(lt_div_iff₀ hR).mpr hA,div_pos hr hR,by simpa [k,hR.ne'] using hz,?_⟩
  have eq := (fields k 0).2.2.2.2
  have h : radialProfile (5/2) k 0 = (Real.Gamma (5/2))⁻¹ := by
    have hΓ : Complex.Gamma (5/2 : ℂ) = (Real.Gamma (5/2) : ℂ) := by
      simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using Complex.Gamma_ofReal (5/2)
    simp [radialProfile,Complex.regularizedHGFun_zero,Complex.regularizedHGFunCoeff,hΓ,
      ← Complex.ofReal_inv]
  simp [mode,rs,oscillation,profile,h] at eq
  rw [eq]
  exact mul_pos (by norm_num) (inv_pos.mpr (Real.Gamma_pos_of_pos (by norm_num)))

end ProjectAinos.Electrodynamics.CavityModes
