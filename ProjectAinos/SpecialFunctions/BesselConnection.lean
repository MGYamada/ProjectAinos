/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.BesselZeros
public import ProjectAinos.SpecialFunctions.Hankel
public import ProjectAinos.SpecialFunctions.BesselRayLimit
public import ProjectAinos.SpecialFunctions.BesselRealAxis
import Mathlib.Tactic

/-! # The real-axis Schläfli formula at nonintegral order

For −1 < a < 0 the Gamma coefficient of the infinite ray fixes the first solution.
The conserved determinant of adjacent-order solutions also fixes the coefficient of the
second solution. The order recurrences extend the identity to every real order.
-/

@[expose] public section
noncomputable section
open Set Filter Complex MeasureTheory
open scoped Real Topology ComplexConjugate
namespace ProjectAinos.SpecialFunctions.Bessel
open Schlaefli

private abbrev J (a x : ℝ) := (besselJ a x).re
private abbrev C (a x : ℝ) := (hankelFirst a x).re

private theorem real_contour (a x : ℝ) :
    C a x = ((arc a x).re - Real.sin (π*a)*realRay (-a) x)/π := by
  have hf : exp (-((a : ℂ)*π)*I) = ↑(Real.cos (-(a*π))) + ↑(Real.sin (-(a*π)))*I := by
    rw [← exp_ofReal_mul_I]
    push_cast
    rfl
  change (hankelFirst a x).re=_
  rw [hankelFirst,hf,← ofReal_realRay,← ofReal_neg,← ofReal_realRay]
  simp only [div_ofReal_re,sub_re,I_mul_re,add_im,ofReal_im,zero_add,im_mul_ofReal,
    mul_I_im,ofReal_re,Real.sin_neg]
  rw [mul_comm π a]
  ring

private theorem arc_real (a x : ℝ) : (arc a x).re =
    ∫ t in 0..π, Real.cos (a*t-x*Real.sin t) := by
  let f (t : ℝ) := exp (((x : ℂ)*Real.sin t-a*t)*I)
  have e := reCLM.intervalIntegral_comp_comm (μ := volume) (a := 0) (b := π) (f := f)
    (Continuous.intervalIntegrable (by unfold f; fun_prop) ..)
  change (∫ t in 0..π, (f t).re) = (∫ t in 0..π, f t).re at e
  change (∫ t in 0..π, f t).re = _
  rw [← e]
  apply intervalIntegral.integral_congr
  intro t _
  change (exp (((x : ℂ)*Real.sin t-a*t)*I)).re=_
  rw [show (x : ℂ)*Real.sin t-a*t = ((x*Real.sin t-a*t : ℝ) : ℂ) by push_cast; rfl,
    exp_ofReal_mul_I_re,← Real.cos_neg,neg_sub]

private theorem arc_zero (a : ℝ) :
    Tendsto (fun u : ℝ => (arc a (2*u : ℝ)).re) (𝓝[>] 0) (𝓝 (arc a 0).re) := by
  have hc := (Complex.continuous_re.continuousAt.comp (hasDerivAt_arc a 0).continuousAt)
  have ht : ContinuousAt (fun u : ℝ => ((2*u : ℝ) : ℂ)) 0 := by fun_prop
  exact hc.tendsto.comp (by simpa using ht.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0)))

/-- Origin coefficient for uᵖ f(2u), using the half-argument normalization of J. -/
private def Scaled (f : ℝ → ℝ) (p c : ℝ) :=
  Tendsto (fun u : ℝ => u^p*f (2*u)) (𝓝[>] 0) (𝓝 c)

private theorem Scaled.raise {f : ℝ → ℝ} {p q c : ℝ} (h : Scaled f p c) (hp : p < q) :
    Scaled f q 0 := by
  have d : 0 < q-p := sub_pos.mpr hp
  have e : Tendsto (fun u : ℝ => u^(q-p)) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.zero_rpow d.ne'] using
      (Real.continuous_rpow_const d.le).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi 0) (a := 0))
  have he := e.mul h
  rw [zero_mul] at he
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [← mul_assoc,← Real.rpow_add hu,sub_add_cancel]

private theorem J_limit (a : ℝ) : Scaled (J a) (-a) (Real.Gamma (a+1))⁻¹ :=
  tendsto_scaled_besselJ a

private theorem C_limit {p : ℝ} (hp : 0 < p) (hq : p < 1) :
    Scaled (C (-p)) p (Real.Gamma (1-p))⁻¹ := by
  have d : Tendsto (fun u : ℝ => u^p) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.zero_rpow hp.ne'] using (Real.continuous_rpow_const hp.le).continuousAt.tendsto
      |>.mono_left (nhdsWithin_le_nhds (s := Ioi 0) (a := 0))
  have h := ((d.mul (arc_zero (-p))).add
    ((tendsto_scaled_ray hp).const_mul (Real.sin (π*p)))).div_const π
  have hg := Real.Gamma_mul_Gamma_one_sub p
  have hs := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hp)
    (show π*p<π by nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hq)])
  have hΓ := Real.Gamma_pos_of_pos (sub_pos.mpr hq)
  simp only [zero_mul,zero_add] at h
  have val : (Real.sin (π*p)*Real.Gamma p)/π = (Real.Gamma (1-p))⁻¹ := by
    have e := (eq_div_iff hs.ne').mp hg
    rw [div_eq_iff Real.pi_ne_zero,inv_mul_eq_div,eq_div_iff hΓ.ne']
    linear_combination e
  rw [val] at h
  apply h.congr'
  filter_upwards with u
  rw [real_contour,neg_neg,mul_neg,Real.sin_neg]
  ring

private theorem C_bounded {a : ℝ} (ha : 0 < a) : ∃ c : ℝ, Scaled (C a) 0 c := by
  have h2 : Tendsto (fun u : ℝ => 2*u) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : ContinuousAt (fun u : ℝ => 2*u) 0 := by fun_prop
      simpa using h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    · filter_upwards [self_mem_nhdsWithin] with u hu using mul_pos zero_lt_two hu
  have h := ((arc_zero a).sub (((tendsto_realRay_zero (neg_lt_zero.mpr ha)).comp h2).const_mul
    (Real.sin (π*a)))).div_const π
  exact ⟨_,h.congr fun u => by simp [real_contour]⟩

/-- First-order Bessel system for the adjacent orders a and a+1 on the positive axis. -/
private def Pair (a : ℝ) (f g : ℝ → ℝ) : Prop := ∀ x : ℝ, 0 < x →
  HasDerivAt f (a/x*f x-g x) x ∧ HasDerivAt g (f x-(a+1)/x*g x) x

private theorem J_rec (a : ℝ) {x : ℝ} (hx : 0 < x) :
    J (a-1) x+J (a+1) x=2*a/x*J a x := by
  have h := congrArg re (recurrence (a : ℂ) x (mem_slitPlane_iff.mpr (Or.inl hx)))
  dsimp only [J]
  push_cast
  have he : (2 : ℂ)*a/x = ((2*a/x : ℝ) : ℂ) := by push_cast; rfl
  simpa only [he,add_re,re_ofReal_mul,zero_re] using h

private theorem J_d (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (J a) (a/x*J a x-J (a+1) x) x := by
  simpa only [J,sub_re,← ofReal_div,re_ofReal_mul,ofReal_add,ofReal_one] using
    (hasDerivAt_besselJ (a : ℂ) x (mem_slitPlane_iff.mpr (Or.inl hx))).real_of_complex

private theorem C_rec (a : ℝ) {x : ℝ} (hx : 0 < x) :
    C (a-1) x+C (a+1) x=2*a/x*C a x := by
  have h := congrArg re (hankelFirst_recurrence (a : ℂ) x hx)
  have he : (x : ℂ)/2 = ((x/2 : ℝ) : ℂ) := by push_cast; rfl
  simp only [he,re_ofReal_mul,add_re] at h
  dsimp only [C]
  push_cast
  field_simp [hx.ne'] at h ⊢
  linear_combination h

private theorem C_d (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (C a) (a/x*C a x-C (a+1) x) x := by
  apply (hasDerivAt_hankelFirst (a : ℂ) x hx).real_of_complex.congr_deriv
  have e := C_rec a hx
  have eq : (C (a-1) x-C (a+1) x)/2=a/x*C a x-C (a+1) x := by linear_combination e/2
  simpa only [C,ofReal_sub,ofReal_add,ofReal_one,sub_re,div_ofNat_re] using eq

private theorem pair_of_rec (f : ℝ → ℝ → ℝ)
    (d : ∀ a : ℝ, ∀ {x : ℝ}, 0 < x → HasDerivAt (f a) (a/x*f a x-f (a+1) x) x)
    (rec : ∀ a : ℝ, ∀ {x : ℝ}, 0 < x → f (a-1) x+f (a+1) x=2*a/x*f a x)
    (a : ℝ) : Pair a (f a) (f (a+1)) := by
  intro x hx
  refine ⟨d a hx,(d (a+1) hx).congr_deriv ?_⟩
  have h := rec (a+1) hx
  rw [add_sub_cancel_right] at h
  linear_combination -h

private theorem pair_reflect (p : ℝ) : Pair (-p) (J p) (fun x => -J (p-1) x) := by
  intro x hx
  constructor
  · apply (J_d p hx).congr_deriv
    linear_combination -(J_rec p hx)
  · apply (J_d (p-1) hx).neg.congr_deriv
    rw [sub_add_cancel]
    ring

private def det (f g h j : ℝ → ℝ) (x : ℝ) := x*(f x*j x-g x*h x)

private theorem det_value {a v : ℝ} {f g h j : ℝ → ℝ} (u : Pair a f g) (w : Pair a h j)
    (hl : Tendsto (fun t : ℝ => det f g h j (2*t)) (𝓝[>] 0) (𝓝 v)) {x : ℝ} (hx : 0 < x) :
    det f g h j x=v := by
  have d (t : ℝ) (ht : 0 < t) : HasDerivAt (det f g h j) 0 t := by
    obtain ⟨df,dg⟩ := u t ht
    obtain ⟨dh,dj⟩ := w t ht
    apply ((hasDerivAt_id' t).mul ((df.mul dj).sub (dg.mul dh))).congr_deriv
    dsimp
    field_simp [ht.ne']
    ring
  have eq (y : ℝ) (hy : 0 < y) := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun t ht => (d t ht).differentiableAt.differentiableWithinAt) (fun t ht => (d t ht).deriv)
    hx hy
  apply tendsto_nhds_unique _ hl
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht using eq (2*t) (mul_pos zero_lt_two ht)

private theorem scaled_product {f g : ℝ → ℝ} {p q b c : ℝ}
    (hf : Scaled f p b) (hg : Scaled g q c) (hp : p+q=1) :
    Tendsto (fun u : ℝ => u*(f (2*u)*g (2*u))) (𝓝[>] 0) (𝓝 (b*c)) := by
  apply (hf.mul hg).congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  change u^p*f (2*u)*(u^q*g (2*u))=_
  rw [show u^p*f (2*u)*(u^q*g (2*u)) = (u^p*u^q)*(f (2*u)*g (2*u)) by ring,
    ← Real.rpow_add hu,hp,Real.rpow_one]

private theorem det_from_scaled {a b c d e p q : ℝ} {f g h j : ℝ → ℝ}
    (u : Pair a f g) (w : Pair a h j)
    (hf : Scaled f p b) (hj : Scaled j (1-p) c)
    (hg : Scaled g (1-q) d) (hh : Scaled h q e) {x : ℝ} (hx : 0 < x) :
    det f g h j x=2*(b*c-d*e) := by
  apply det_value u w _ hx
  have H := ((scaled_product hf hj (by ring)).sub (scaled_product hg hh (by ring))).const_mul 2
  exact H.congr fun t => by dsimp only [det]; ring

private theorem Scaled.sub {f g : ℝ → ℝ} {p b c : ℝ} (hf : Scaled f p b)
    (hg : Scaled g p c) : Scaled (fun x => f x-g x) p (b-c) :=
  (Filter.Tendsto.sub hf hg).congr fun _ => (mul_sub ..).symm

private theorem base_pair {p x : ℝ} (hp : 0 < p) (hq : p < 1) (hx : 0 < x) :
    (C (-p) x=J (-p) x ∧ C (-p+1) x=J (-p+1) x) ∧
      (J (-p) x≠0 ∨ J (-p+1) x≠0) := by
  -- The two reference solutions have orders −p and p. Reflecting the second
  -- gives the pair (Jₚ, −Jₚ₋₁) in the same first-order system.
  let f := J (-p)
  let g := J (-p+1)
  let h := J p
  let j := fun t => -J (p-1) t
  let u := fun t => C (-p) t-f t
  let v := fun t => C (-p+1) t-g t
  let b := (Real.Gamma (1-p))⁻¹
  let c := (Real.Gamma p)⁻¹
  have B : Pair (-p) f g := pair_of_rec J J_d J_rec (-p)
  have T : Pair (-p) h j := pair_reflect p
  have E : Pair (-p) u v := by
    intro t ht
    obtain ⟨d,d'⟩ := pair_of_rec C C_d C_rec (-p) t ht
    obtain ⟨v₁,v₂⟩ := B t ht
    exact ⟨(d.sub v₁).congr_deriv (by dsimp [u,v]; ring),
      (d'.sub v₂).congr_deriv (by dsimp [u,v]; ring)⟩
  have lf : Scaled f p b := by simpa [f,b,sub_eq_neg_add] using J_limit (-p)
  have lg := J_limit (-p+1)
  have lh : Scaled h (-p) _ := J_limit p
  have lj : Scaled j (1-p) (-c) := by
    simpa only [Scaled,j,c,neg_sub,sub_add_cancel,mul_neg] using
      Filter.Tendsto.neg (J_limit (p-1))
  have lu : Scaled u p 0 := by simpa [u,b] using (C_limit hp hq).sub lf
  obtain ⟨z,l⟩ := C_bounded (show 0 < -p+1 by linarith)
  have lv (q : ℝ) (hq' : 0 < q) : Scaled v q 0 := by
    have l' := lg.raise (q := q) (by linarith)
    simpa [v,g] using (l.raise hq').sub l'
  -- The error has zero determinant with each reference solution. Their mutual
  -- determinant is nonzero by the two Gamma coefficients at the origin.
  have A := det_from_scaled E B lu (lg.raise (q := 1-p) (by linarith))
    (lv (1-p) (by linarith)) lf hx
  have D := det_from_scaled E T lu lj (lv (1- -p) (by linarith)) lh hx
  have M := det_from_scaled B T lf lj (lg.raise (q := 1- -p) (by linarith)) lh hx
  have hb : b ≠ 0 := inv_ne_zero (Real.Gamma_pos_of_pos (sub_pos.mpr hq)).ne'
  have hc : c ≠ 0 := inv_ne_zero (Real.Gamma_pos_of_pos hp).ne'
  have hn : f x*j x-g x*h x≠0 := by
    intro eq
    simp [det,eq,hb,hc] at M
  have zero₁ : u x*g x-v x*f x=0 := by
    simpa [det,hx.ne'] using A
  have zero₂ : u x*j x-v x*h x=0 := by
    simpa [det,hx.ne'] using D
  have e₁ : u x=0 := by
    apply (mul_eq_zero.mp (show u x*(f x*j x-g x*h x)=0 by
      linear_combination f x*zero₂-h x*zero₁)).resolve_right hn
  have e₂ : v x=0 := by
    apply (mul_eq_zero.mp (show v x*(f x*j x-g x*h x)=0 by
      linear_combination g x*zero₂-j x*zero₁)).resolve_right hn
  refine ⟨⟨sub_eq_zero.mp e₁,sub_eq_zero.mp e₂⟩,?_⟩
  by_contra! H
  exact hn (by dsimp only [f,g]; rw [H.1,H.2]; ring)

private theorem shifted_pair (a x : ℝ) {u v : ℝ → ℝ}
    (hr : ∀ t : ℝ, u (t-1)+u (t+1)=2*t/x*u t)
    (hs : ∀ t : ℝ, v (t-1)+v (t+1)=2*t/x*v t)
    (h : u a=v a ∧ u (a+1)=v (a+1)) (n : ℤ) :
    u (a+n)=v (a+n) ∧ u (a+n+1)=v (a+n+1) := by
  induction n using Int.inductionOn' (b := 0) with
  | zero => simpa using h
  | succ k _ ih =>
    push_cast
    rw [← add_assoc]
    have e := hr (a+k+1)
    have e' := hs (a+k+1)
    rw [add_sub_cancel_right,ih.1,ih.2] at e
    rw [add_sub_cancel_right] at e'
    exact ⟨ih.2,by linarith⟩
  | pred k _ ih =>
    push_cast
    rw [show a+(k-1)=a+k-1 by ring,sub_add_cancel]
    have e := hr (a+k)
    have e' := hs (a+k)
    rw [ih.1,ih.2] at e
    exact ⟨by linarith,ih.1⟩

private theorem int_connection (n : ℤ) (x : ℝ) : C n x=J n x := by
  rw [real_contour,arc_real,show π*(n : ℝ)=(n : ℝ)*π by ring,Real.sin_int_mul_pi]
  simp [J,integral,div_eq_inv_mul]

private theorem connection_and_nonzero (a : ℝ) {x : ℝ} (hx : 0 < x) :
    C a x=J a x ∧ (J a x≠0 ∨ J (a+1) x≠0) := by
  let n := ⌈a⌉
  by_cases ha : a=(n : ℝ)
  · rw [ha]
    refine ⟨int_connection _ _,?_⟩
    by_contra! H
    have e := ofReal_re_besselJ (n : ℝ) hx
    have e' := ofReal_re_besselJ ((n : ℝ)+1) hx
    rw [show (besselJ ((n : ℝ) : ℂ) x).re=0 from H.1,ofReal_zero] at e
    rw [show (besselJ (((n : ℝ)+1 : ℝ) : ℂ) x).re=0 from H.2,ofReal_zero] at e'
    apply (adjacent_ne_zero n (mem_slitPlane_iff.mpr (Or.inl hx)) (by simpa using e.symm))
    simpa using e'.symm
  · let p := (n : ℝ)-a
    have hp : 0 < p := sub_pos.mpr (lt_of_le_of_ne (Int.le_ceil _) ha)
    have hq : p < 1 := by dsimp [p,n]; linarith [Int.ceil_lt_add_one a]
    obtain ⟨h,hn⟩ := base_pair hp hq hx
    have h₀ : -p+(n : ℝ)=a := by dsimp [p]; ring
    have h' := shifted_pair (-p) x (u := fun b => C b x) (v := fun b => J b x)
      (fun b => C_rec b hx) (fun b => J_rec b hx) h n
    rw [h₀] at h'
    refine ⟨h'.1,?_⟩
    by_contra! H
    have e := shifted_pair a x (u := fun b => J b x) (v := fun _ => 0)
      (fun b => J_rec b hx) (fun b => by ring) H (-n)
    rw [Int.cast_neg,show a+ -(n : ℝ) = -p by dsimp [p]; ring] at e
    exact hn.elim (fun h => h e.1) (fun h => h e.2)

/-- Schläfli's integral for every real order, including the nonintegral ray correction. -/
theorem integral_real_order (a : ℝ) {x : ℝ} (hx : 0 < x) :
    besselJ a x = (((∫ t in 0..π, Real.cos (a*t-x*Real.sin t)) -
      Real.sin (π*a)*realRay (-a) x)/π : ℝ) := by
  rw [← ofReal_re_besselJ a hx]
  change ((J a x : ℝ) : ℂ)=_
  rw [← (connection_and_nonzero a hx).1,real_contour,arc_real]

/-- The outgoing Hankel contour has real part J on the entire positive real axis. -/
theorem hankelFirst_re (a : ℝ) {x : ℝ} (hx : 0 < x) :
    (hankelFirst a x).re=(besselJ a x).re := (connection_and_nonzero a hx).1

/-- A positive zero of J of any real order is simple. -/
theorem deriv_ne_zero_of_real_order_zero (a : ℝ) {x : ℝ} (hx : 0 < x)
    (hj : besselJ a x=0) : deriv (besselJ a) x≠0 := by
  have h := (connection_and_nonzero a hx).2
  rw [(hasDerivAt_besselJ _ _ (mem_slitPlane_iff.mpr (Or.inl hx))).deriv,hj,mul_zero,zero_sub]
  intro e
  have e' := congrArg re (neg_eq_zero.mp e)
  simp only [J,hj,zero_re,ne_self_iff_false,false_or,ofReal_add,ofReal_one] at h
  exact h e'

private theorem reflected_arc (a z : ℂ) : arc (-a) z = exp (a*π*I)*arc a z := by
  let f (t : ℝ) := exp ((z*Real.sin t-a*t)*I)
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π) f π
  rw [sub_self,sub_zero] at h
  have hf (t : ℝ) : exp ((z*Real.sin t-(-a)*t)*I) = exp (a*π*I)*f (π-t) := by
    dsimp [f]
    rw [Real.sin_pi_sub,← exp_add]
    congr 1
    push_cast
    ring
  unfold arc
  simp_rw [hf]
  rw [intervalIntegral.integral_const_mul,h]

/-- Reversing the order multiplies the outgoing contour by exp(iπa). -/
theorem hankelFirst_neg_order (a z : ℂ) : hankelFirst (-a) z = exp (a*π*I)*hankelFirst a z := by
  rw [hankelFirst,hankelFirst,reflected_arc,neg_neg]
  have h := exp_ne_zero (a*π*I)
  rw [show -((-a)*π)*I=a*π*I by ring,show -(a*π)*I = -(a*π*I) by ring,exp_neg]
  field_simp
  ring

/-- The Neumann function is real on the positive real axis for every real order. -/
theorem neumann_real (a : ℝ) {x : ℝ} (hx : 0 < x) : neumann a x = ((hankelFirst a x).im : ℝ) := by
  have h := hankelFirst_re a hx
  rw [neumann,div_eq_iff I_ne_zero,← ofReal_re_besselJ a hx,← h,sub_eq_iff_eq_add]
  rw [add_comm,Complex.re_add_im]

/-- The usual Jₐ and J₋ₐ expression for the Neumann function at nonintegral real order. -/
theorem neumann_nonintegral (a : ℝ) {x : ℝ} (hx : 0 < x) (ha : Real.sin (π*a)≠0) :
    neumann a x = ((Real.cos (π*a)*(besselJ a x).re-(besselJ (-a) x).re)/Real.sin (π*a) : ℝ) := by
  have e := congrArg re (hankelFirst_neg_order a x)
  have he : exp ((a : ℂ)*π*I) = (Real.cos (π*a) : ℂ)+(Real.sin (π*a) : ℂ)*I := by
    rw [← exp_ofReal_mul_I,mul_comm π a,ofReal_mul]
  rw [he] at e
  simp only [mul_re,add_re,add_im,mul_I_im,ofReal_im,ofReal_re,I_re,mul_zero,
    zero_mul,sub_zero,add_zero,zero_add] at e
  rw [← ofReal_neg,hankelFirst_re (-a) hx,hankelFirst_re a hx] at e
  rw [neumann_real a hx,ofReal_inj,eq_div_iff ha]
  push_cast at e ⊢
  linear_combination e

/-- On the positive real axis the incoming and outgoing functions are complex conjugates. -/
theorem hankelSecond_real_axis (a : ℝ) {x : ℝ} (hx : 0 < x) :
    hankelSecond a x = conj (hankelFirst a x) := by
  rw [hankelSecond,← ofReal_re_besselJ a hx,← hankelFirst_re a hx]
  apply Complex.ext <;> simp [Complex.sub_re,Complex.sub_im]
  ring

end ProjectAinos.SpecialFunctions.Bessel
