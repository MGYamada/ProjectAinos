/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.HyperbolicHarmonics
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic

/-! # Continuous spectral synthesis in hyperbolic angular channels

Fourier inversion of an odd radial seed gives a Lebesgue integral of regular standing
waves. A radial raising operator of any fixed order commutes with this inversion:
its finite jet uses only polynomial moments of a Schwartz transform.
-/

@[expose] public section
noncomputable section
open Complex Filter Set MeasureTheory FourierTransform
open scoped Real FourierTransform Topology ContDiff SchwartzMap
namespace ProjectAinos.SpecialFunctions.Hyperbolic

private abbrev Terms := List (ℕ × (ℝ → ℂ))
private def act : Terms → (ℝ → ℂ) → ℝ → ℂ
  | [], _, _ => 0
  | (n,a)::L, f, r => a r*(deriv^[n] f) r + act L f r

private abbrev Cth (r : ℝ) : ℂ := (Real.cosh r : ℂ)/Real.sinh r
private def liftTerms (j : ℕ) : Terms → Terms
  | [] => []
  | (n,a)::L => (n,fun r => deriv a r-(j : ℂ)*Cth r*a r)::(n+1,a)::liftTerms j L

private def operators : ℕ → Terms
  | 0 => [(0, fun _ => 1)]
  | n+1 => liftTerms (n+1) (operators n)

private abbrev Good (L : Terms) := ∀ p ∈ L, ContDiffOn ℝ ∞ p.2 (Ioi 0)
private theorem cotSmooth : ContDiffOn ℝ ∞ Cth (Ioi 0) := by
  have h : ContDiffOn ℝ ∞ (Real.cosh / Real.sinh) (Ioi 0) :=
    Real.contDiff_cosh.contDiffOn.div Real.contDiff_sinh.contDiffOn
      (fun _ ht => (Real.sinh_pos_iff.mpr ht).ne')
  apply (ofRealCLM.contDiff.comp_contDiffOn h).congr
  intro t _
  simp [Cth]

private theorem good_lift {L : Terms} (hL : Good L) (j : ℕ) : Good (liftTerms j L) := by
  induction L with
  | nil => simp [liftTerms]
  | cons p L ih =>
    obtain ⟨n,a⟩ := p
    have ha := hL (n,a) (by simp)
    have hD : ContDiffOn ℝ ∞ (deriv a) (Ioi 0) := ha.deriv_of_isOpen isOpen_Ioi (by simp)
    intro p hp
    simp only [liftTerms,List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact hD.sub ((contDiffOn_const.mul cotSmooth).mul ha)
    · exact ha
    · exact ih (fun p hp => hL p (by simp [hp])) _ hp

private theorem good (l : ℕ) : Good (operators l) := by
  induction l with
  | zero => intro p hp; simp [operators] at hp; subst p; exact contDiffOn_const
  | succ l ih => exact good_lift ih _

private theorem itSmooth {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (k : ℕ) :
    ContDiffOn ℝ ∞ (deriv^[k] g) (Ioi 0) := by
  induction k with
  | zero => exact hg
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

private theorem actSmooth {L : Terms} (hL : Good L) {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) : ContDiffOn ℝ ∞ (act L g) (Ioi 0) := by
  induction L with
  | nil => exact contDiffOn_const
  | cons p L ih =>
    obtain ⟨n,a⟩ := p
    exact ((hL (n,a) (by simp)).mul (itSmooth hg n)).add
      (ih (fun p hp => hL p (by simp [hp])))

private theorem jetRaise (j : ℕ) {L : Terms} (hL : Good L) {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    raise j (act L g) r = act (liftTerms j L) g r := by
  induction L with
  | nil => simp [act,raise,liftTerms]
  | cons p L ih =>
    obtain ⟨n,a⟩ := p
    have ht : Good L := fun p hp => hL p (by simp [hp])
    have hd {f : ℝ → ℂ} (h : ContDiffOn ℝ ∞ f (Ioi 0)) :=
      ((h.contDiffAt (Ioi_mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
    have H : deriv (act ((n,a)::L) g) r = _ :=
      (((hd (hL (n,a) (by simp))).mul (hd (itSmooth hg n))).add (hd (actSmooth ht hg))).deriv
    rw [raise,H]
    simp only [raise,act,liftTerms,Function.iterate_succ_apply'] at ih ⊢
    linear_combination ih ht

private theorem jet {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (l : ℕ) {r : ℝ}
    (hr : 0 < r) : raised g l r = act (operators l) g r := by
  induction l generalizing r with
  | zero => simp [raised,operators,act]
  | succ l ih =>
    have he : raised g l =ᶠ[𝓝 r] act (operators l) g := by
      filter_upwards [Ioi_mem_nhds hr] with t ht using ih ht
    change deriv (raised g l) r-_*_*raised g l r=_
    rw [he.deriv_eq,he.eq_of_nhds]
    exact jetRaise _ (good l) hg hr

private def freq (v : ℝ) : ℂ := 2*π*I*v
private def wave (v t : ℝ) := exp (freq v*t)
private def sd (g : 𝓢(ℝ,ℂ)) : ℕ → 𝓢(ℝ,ℂ)
  | 0 => g
  | n+1 => SchwartzMap.derivCLM ℂ ℂ (sd g n)

private theorem sd_coe (g : 𝓢(ℝ,ℂ)) (n : ℕ) : ⇑(sd g n) = deriv^[n] (g : ℝ → ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',← ih]
    rfl

private theorem transform_sd (g : 𝓢(ℝ,ℂ)) (n : ℕ) (v : ℝ) :
    𝓕 (sd g n) v = freq v^n * 𝓕 g v := by
  induction n with
  | zero => simp [sd]
  | succ n ih =>
    have h := congrFun (Real.fourier_deriv (sd g n).integrable (sd g n).differentiable
      (show Integrable (deriv (sd g n)) from (sd g (n+1)).integrable)) v
    rw [SchwartzMap.fourier_coe,sd_coe,Function.iterate_succ_apply',← sd_coe]
    simp only [SchwartzMap.fourier_coe] at ih
    rw [h,ih,pow_succ]
    simp [freq,smul_eq_mul,SchwartzMap.fourier_coe]
    ring

private theorem wave_deriv (v r : ℝ) :
    HasDerivAt (wave v) (freq v*wave v r) r := by
  convert (((hasDerivAt_id' (r : ℂ)).const_mul (freq v)).cexp.comp_ofReal) using 1
  · rfl
  · simp only [wave,mul_one]
    ring

private theorem wave_jet (v : ℝ) (n : ℕ) :
    deriv^[n] (wave v) = fun r => freq v^n*wave v r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    funext r
    rw [((wave_deriv v r).const_mul _).deriv,pow_succ,mul_assoc]

private theorem norm_wave (v r : ℝ) : ‖wave v r‖ = 1 := by
  simp [wave,freq,norm_exp,mul_re,mul_im]

private theorem term_int (g : 𝓢(ℝ,ℂ)) (k : ℕ) (r : ℝ) :
    Integrable (fun v => (deriv^[k] (wave v)) r*𝓕 g v) := by
  simp_rw [wave_jet]
  have hm : Continuous (fun v => freq v^k*wave v r*𝓕 g v) := by
    unfold wave freq
    fun_prop
  apply ((𝓕 (sd g k)).integrable (μ := volume)).norm.mono' hm.aestronglyMeasurable
  filter_upwards with v
  rw [transform_sd,norm_mul,norm_mul,norm_wave,mul_one,norm_mul]

private theorem inversion (g : 𝓢(ℝ,ℂ)) (n : ℕ) (r : ℝ) :
    (deriv^[n] (g : ℝ → ℂ)) r = ∫ v : ℝ, (deriv^[n] (wave v)) r * 𝓕 g v := by
  have h₀ : 𝓕⁻ (𝓕 (sd g n) : 𝓢(ℝ,ℂ)) = sd g n := fourierInv_fourier_eq _
  have h := congrArg (fun f : 𝓢(ℝ,ℂ) => f r) h₀
  change 𝓕⁻ (𝓕 (sd g n)) r = _ at h
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq'] at h
  rw [← sd_coe,← h]
  apply integral_congr_ae
  filter_upwards with v
  rw [wave_jet,transform_sd]
  simp only [wave,freq,Real.inner_apply,smul_eq_mul]
  push_cast
  ring

private theorem act_inv (L : Terms) (g : 𝓢(ℝ,ℂ)) (r : ℝ) :
    Integrable (fun v => act L (wave v) r * 𝓕 g v) ∧
      act L g r = ∫ v : ℝ, act L (wave v) r*𝓕 g v := by
  induction L with
  | nil => simp [act]
  | cons p L ih =>
    obtain ⟨k,a⟩ := p
    have hi := (term_int g k r).const_mul (a r)
    simp only [act,add_mul,mul_assoc]
    exact ⟨hi.add ih.1,by rw [integral_add hi ih.1,integral_const_mul,← inversion,← ih.2]⟩

private theorem wave_smooth (v : ℝ) : ContDiff ℝ ∞ (wave v) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  unfold wave
  fun_prop

/-- Absolutely convergent continuous Fourier synthesis after any number of angular
raising steps, at every positive geodesic radius. -/
private theorem raised_fourier (l : ℕ) (g : 𝓢(ℝ,ℂ)) {r : ℝ} (hr : 0 < r) :
    Integrable (fun v => raised (wave v) l r*𝓕 g v) ∧
      raised g l r = ∫ v : ℝ, raised (wave v) l r*𝓕 g v := by
  simp_rw [jet (wave_smooth _).contDiffOn l hr,jet (g.smooth ⊤).contDiffOn l hr]
  exact act_inv (operators l) g r

private theorem odd_fourier (g : 𝓢(ℝ,ℂ)) (hg : ∀ t, g (-t) = -g t) (v : ℝ) :
    𝓕 g (-v) = -𝓕 g v := by
  have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ)) (g : ℝ → ℂ) v
  change 𝓕 (fun t : ℝ => g (-t)) v = 𝓕 (g : ℝ → ℂ) (-v) at h
  simp_rw [hg] at h
  rw [SchwartzMap.fourier_coe,← h,Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul,← integral_neg]
  simp

private theorem raised_linear {f g : ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (Ioi 0))
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (a b : ℂ) (l : ℕ) {r : ℝ} (hr : 0 < r) :
    raised (fun t => a*f t+b*g t) l r = a*raised f l r+b*raised g l r := by
  have hS : ContDiffOn ℝ ∞ (fun t => a*f t+b*g t) (Ioi 0) :=
    (contDiffOn_const.mul hf).add (contDiffOn_const.mul hg)
  rw [jet hS l hr,jet hf l hr,jet hg l hr]
  have he (k : ℕ) : Set.EqOn (deriv^[k] (fun t => a*f t+b*g t))
      (fun t => a*(deriv^[k] f) t+b*(deriv^[k] g) t) (Ioi 0) := by
    induction k with
    | zero => intro t _; rfl
    | succ k ih =>
      intro t ht
      have hd {g : ℝ → ℂ} (h : ContDiffOn ℝ ∞ g (Ioi 0)) :=
        (((itSmooth h k).contDiffAt (Ioi_mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
      rw [Function.iterate_succ_apply',(ih.eventuallyEq_of_mem (Ioi_mem_nhds ht)).deriv_eq]
      simp only [Function.iterate_succ_apply']
      exact ((hd hf).const_mul a |>.add ((hd hg).const_mul b)).deriv
  suffices ∀ (L : Terms), act L (fun t => a*f t+b*g t) r = a*act L f r+b*act L g r from this _
  intro L
  induction L with
  | nil => simp [act]
  | cons p L ih =>
    obtain ⟨k,c⟩ := p
    simp only [act,he k hr,ih]
    ring

private theorem sine_smooth (k : ℝ) : ContDiff ℝ ∞ (sineSeed k) := by
  unfold sineSeed
  split
  · exact ofRealCLM.contDiff
  · exact ofRealCLM.contDiff.comp (show ContDiff ℝ ∞ (fun t : ℝ => Real.sin (k*t)/k) by fun_prop)

private theorem standing (v : ℝ) :
    (fun t => wave v t-wave (-v) t) =
      fun t => (2*I*(2*π*v : ℝ))*sineSeed (2*π*v) t := by
  funext t
  let k := 2*π*v
  have hp : wave v t = exp ((k*t : ℝ)*I) := by
    unfold wave freq
    congr 1
    dsimp [k]
    push_cast
    ring
  have hm : wave (-v) t = exp (-((k*t : ℝ) : ℂ)*I) := by
    unfold wave freq
    congr 1
    dsimp [k]
    push_cast
    ring
  rw [hp,hm,exp_mul_I,exp_mul_I,cos_neg,sin_neg,← ofReal_sin]
  change _ = 2*I*(k : ℂ)*sineSeed k t
  by_cases hk : k=0
  · simp [hk]
  · simp only [sineSeed,hk,↓reduceIte,ofReal_div]
    field_simp [ofReal_ne_zero.mpr hk]
    ring

private theorem standing_raised (l : ℕ) (v : ℝ) {r : ℝ} (hr : 0 < r) :
    raised (wave v) l r-raised (wave (-v)) l r =
      (2*I*(2*π*v : ℝ))*raised (sineSeed (2*π*v)) l r := by
  have h₁ := raised_linear (wave_smooth v).contDiffOn (wave_smooth (-v)).contDiffOn 1 (-1) l hr
  have h₂ := raised_linear (sine_smooth (2*π*v)).contDiffOn (sine_smooth (2*π*v)).contDiffOn
    (2*I*(2*π*v : ℝ)) 0 l hr
  simpa only [one_mul,neg_one_mul,← sub_eq_add_neg,zero_mul,add_zero,standing] using h₁.symm.trans
    (by simpa only [one_mul,neg_one_mul,← sub_eq_add_neg,zero_mul,add_zero,standing] using h₂)

private theorem reflected (g : 𝓢(ℝ,ℂ)) (hg : ∀ t, g (-t) = -g t)
    (l : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun v => raised (wave (-v)) l r*𝓕 g v) ∧
      (∫ v : ℝ, raised (wave (-v)) l r*𝓕 g v) = -raised g l r := by
  let f (v : ℝ) := raised (wave v) l r*𝓕 g v
  obtain ⟨hi,he⟩ := raised_fourier l g hr
  have h : (fun v => raised (wave (-v)) l r*𝓕 g v) = fun v => -f (-v) := by
    funext v
    simp [f,odd_fourier g hg]
  rw [h]
  have hh := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hi
  exact ⟨hh.neg,
    by rw [integral_neg,integral_neg_eq_self,he]⟩

/-- Sine-transform synthesis of every odd Schwartz seed in angular degree ℓ.
The spectral measure is Lebesgue measure in v, with eigenvalue −(1+(2πv)²). -/
theorem harmonic_synthesis (l : ℕ) (g : 𝓢(ℝ,ℂ)) (hg : ∀ t, g (-t) = -g t)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun v : ℝ => (I*(2*π*v : ℝ)*𝓕 g v)*harmonic l (2*π*v) r) ∧
      raised g l r/(Real.sinh r : ℂ) =
        ∫ v : ℝ, (I*(2*π*v : ℝ)*𝓕 g v)*harmonic l (2*π*v) r := by
  obtain ⟨hp,hp'⟩ := raised_fourier l g hr
  obtain ⟨hm,hm'⟩ := reflected g hg l hr
  let c := (2*(Real.sinh r : ℂ))⁻¹
  have h : (fun v : ℝ => (I*(2*π*v : ℝ)*𝓕 g v)*harmonic l (2*π*v) r) =
      fun v => c*(raised (wave v) l r*𝓕 g v-raised (wave (-v)) l r*𝓕 g v) := by
    funext v
    rw [← sub_mul,standing_raised l v hr]
    simp [harmonic,hr.ne',c,div_eq_mul_inv]
    ring
  rw [h]
  refine ⟨(hp.sub hm).const_mul c,?_⟩
  rw [integral_const_mul,integral_sub hp hm,← hp',hm']
  dsimp [c]
  ring

private theorem preimage (l : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) {B : ℝ}
    (hB : ∀ s ≥ B, F s = 0) :
    ∃ g : 𝓢(ℝ,ℂ), (∀ t, g (-t) = -g t) ∧ ∀ r : ℝ, 0 < r →
      raised g l r = (Real.sinh r : ℂ)^(l+1)*F (Real.cosh r) := by
  induction l generalizing F with
  | zero =>
    let f (r : ℝ) := (Real.sinh r : ℂ)*F (Real.cosh r)
    have hf : ContDiff ℝ ∞ f := (ofRealCLM.contDiff.comp Real.contDiff_sinh).mul
      (hF.comp Real.contDiff_cosh)
    let R := Real.arcosh (max 1 B)
    have hR : 0 ≤ R := Real.arcosh_nonneg (le_max_left ..)
    have hc : HasCompactSupport f := by
      apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
      intro t ht
      by_contra h
      have h' : R ≤ |t| := by
        contrapose! h
        exact abs_le.mp h.le
      have hb : B ≤ Real.cosh t := (le_max_right 1 B).trans (by
        rw [← Real.cosh_arcosh (le_max_left 1 B)]
        exact Real.cosh_le_cosh.mpr (by change |R| ≤ _; rwa [abs_of_nonneg hR]))
      exact ht (by simp [f,hB _ hb])
    exact ⟨hc.toSchwartzMap hf,fun t => by simp [f],fun r _ => by simp [raised,f]⟩
  | succ l ih =>
    let G (s : ℝ) := ∫ u in B..s, F u
    have hd (s : ℝ) : HasDerivAt G (F s) s := intervalIntegral.integral_hasDerivAt_right
      (hF.continuous.intervalIntegrable ..)
      hF.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hF.continuous.continuousAt
    have hG : ContDiff ℝ ∞ G := contDiff_infty_iff_deriv.mpr
      ⟨fun s => (hd s).differentiableAt, (show deriv G = F from funext fun s => (hd s).deriv) ▸ hF⟩
    have hGB (s : ℝ) (hs : B ≤ s) : G s = 0 := by
      change (∫ u in B..s, F u) = _
      rw [intervalIntegral.integral_congr (g := fun _ => 0) (fun t ht =>
        hB t ((uIcc_of_le hs) ▸ ht).1),intervalIntegral.integral_zero]
    obtain ⟨g,hodd,hg⟩ := ih hG hGB
    refine ⟨g,hodd,fun r hr => ?_⟩
    have he : raised g l =ᶠ[𝓝 r] fun t => (Real.sinh t : ℂ)^(l+1)*G (Real.cosh t) := by
      filter_upwards [Ioi_mem_nhds hr] with t ht using hg t ht
    have h := (((Real.hasDerivAt_sinh r).ofReal_comp.pow (l+1)).mul
      ((hd _).scomp r (Real.hasDerivAt_cosh r))).deriv
    rw [raised,raise,he.deriv_eq,he.eq_of_nhds]
    rw [show deriv (fun t => (Real.sinh t : ℂ)^(l+1)*G (Real.cosh t)) r = _ from h]
    simp only [Nat.cast_succ,Nat.add_one_sub_one,Complex.real_smul,Function.comp_apply,Pi.pow_apply]
    have hn : (Real.sinh r : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hr).ne'
    field_simp
    ring

/-- Every smooth radial test profile sinh(r)ˡ F(cosh r) bounded in support at infinity,
in each spherical-harmonic degree, is an absolutely convergent superposition of the
regular hyperbolic eigenfunctions with a Schwartz Fourier amplitude. -/
theorem expand_channel (l : ℕ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) {B : ℝ}
    (hB : ∀ s ≥ B, F s = 0) :
    ∃ g : 𝓢(ℝ,ℂ), (∀ t, g (-t) = -g t) ∧ ∀ r : ℝ, 0 < r →
      Integrable (fun v : ℝ => (I*(2*π*v : ℝ)*𝓕 g v)*harmonic l (2*π*v) r) ∧
      (Real.sinh r : ℂ)^l*F (Real.cosh r) =
        ∫ v : ℝ, (I*(2*π*v : ℝ)*𝓕 g v)*harmonic l (2*π*v) r := by
  obtain ⟨g,ho,hr⟩ := preimage l hF hB
  refine ⟨g,ho,fun r h => ?_⟩
  obtain ⟨hi,he⟩ := harmonic_synthesis l g ho h
  refine ⟨hi,?_⟩
  rw [← he,hr r h,pow_succ]
  rw [mul_right_comm,mul_div_cancel_right₀ _ (ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr h).ne')]

private def energy (v : ℝ) := 1+(2*π*v)^2
private def residual (E : ℝ) (g : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) := ((1-E : ℝ) : ℂ) • g - sd g 2

private theorem residual_fourier (E : ℝ) (g : 𝓢(ℝ,ℂ)) (v : ℝ) :
    𝓕 (residual E g) v = ((energy v-E : ℝ) : ℂ)*𝓕 g v := by
  rw [residual,← SchwartzMap.fourierTransformCLM_apply ℂ,map_sub,map_smul,
    SchwartzMap.fourierTransformCLM_apply,SchwartzMap.fourierTransformCLM_apply]
  simp only [sub_apply,smul_apply,smul_eq_mul,transform_sd]
  unfold energy freq
  push_cast
  linear_combination -4*(π : ℂ)^2*v^2*𝓕 g v*I_sq

private theorem mass_int (g : 𝓢(ℝ,ℂ)) : Integrable (fun r => ‖g r‖^2) :=
  (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).mp (g.memLp 2 volume)

private theorem packet {E ε : ℝ} (hE : 1 ≤ E) (hε : 0 < ε) :
    ∃ g : 𝓢(ℝ,ℂ), (∀ t, g (-t) = -g t) ∧ 0 < (∫ r, ‖g r‖^2) ∧
      ∀ v : ℝ, ‖(𝓕 (residual E g)) v‖ ≤ ε*‖(𝓕 g) v‖ := by
  let b : ContDiffBump E := ⟨ε/2,ε,half_pos hε,half_lt_self hε⟩
  let F (v : ℝ) : ℂ := (v*b (energy v) : ℝ)
  have hF : ContDiff ℝ ∞ F := ofRealCLM.contDiff.comp
    (contDiff_id.mul (b.contDiff.comp (by unfold energy; fun_prop)))
  let R := √(E+ε)/(2*π)
  have hp : 0 < 2*π := by positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hfc : HasCompactSupport F := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
    intro x hx
    apply abs_le.mp
    by_contra! h
    have H : ε ≤ dist (energy x) E := by
      rw [Real.dist_eq]
      apply le_trans _ (le_abs_self _)
      have h' := (div_lt_iff₀ hp).mp h
      have hs := Real.sq_sqrt (show 0 ≤ E+ε by linarith)
      dsimp [energy]
      nlinarith [sq_abs x,sq_lt_sq' (by linarith [Real.sqrt_nonneg (E+ε)]) h']
    exact hx (by simp [F,b.zero_of_le_dist H])
  let f := hfc.toSchwartzMap hF
  let g : 𝓢(ℝ,ℂ) := 𝓕⁻ f
  have H : 𝓕 g = f := fourier_fourierInv_eq f
  have odd (t : ℝ) : f (-t) = -f t := by
    change F (-t) = -F t
    simp [F,energy]
  have og (t : ℝ) : g (-t) = -g t := by
    change (𝓕⁻ f) (-t) = -(𝓕⁻ f) t
    rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq_fourier_neg,Real.fourierInv_eq_fourier_neg,
      neg_neg]
    simpa only [SchwartzMap.fourier_coe,neg_neg] using (congrArg Neg.neg (odd_fourier f odd t)).symm
  let v := √(E-1+ε/4)/(2*π)
  have hv : 0 < v := div_pos (Real.sqrt_pos.mpr (by linarith)) hp
  have hev : energy v = E+ε/4 := by
    dsimp [energy,v]
    rw [show 2*π*(√(E-1+ε/4)/(2*π)) = √(E-1+ε/4) by field_simp,
      Real.sq_sqrt (by linarith)]
    ring
  have hb : b (energy v) = 1 := b.one_of_mem_closedBall (by
    rw [Metric.mem_closedBall,Real.dist_eq,hev,add_sub_cancel_left,abs_of_pos (by positivity)]
    change ε/4 ≤ ε/2
    linarith)
  refine ⟨g,og,?_,?_⟩
  · rw [← SchwartzMap.integral_norm_sq_fourier g,H]
    apply integral_pos_of_integrable_nonneg_nonzero (x := v)
      (f.continuous.norm.pow _) (mass_int f) (fun _ => sq_nonneg _)
    change ‖F v‖^2 ≠ 0
    simp [F,hb,hv.ne']
  · intro x
    rw [residual_fourier,H,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    change |energy x-E| *‖F x‖ ≤ ε*‖F x‖
    by_cases hx : |energy x-E| ≤ ε
    · exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    · have h₀ : b (energy x)=0 := b.zero_of_le_dist (by
        rw [Real.dist_eq]; exact (lt_of_not_ge hx).le)
      simp [F,h₀]

/-- Weyl's approximate-eigenfunction criterion in the radial channel. The conjugated
Laplacian is 1−d²/dr² on odd seeds and its approximate energies are exactly [1,∞).
Both norms are on the full line, twice the squared spatial radial norms. -/
theorem approximate_iff (E : ℝ) :
    1 ≤ E ↔ ∀ ε : ℝ, 0 < ε → ∃ g : 𝓢(ℝ,ℂ), (∀ t, g (-t) = -g t) ∧
      0 < (∫ r : ℝ, ‖g r‖^2) ∧ (∫ r : ℝ, ‖((1-E : ℝ) : ℂ)*g r-deriv (deriv g) r‖^2) ≤
        ε^2*(∫ r : ℝ, ‖g r‖^2) := by
  have eq (g : 𝓢(ℝ,ℂ)) (r : ℝ) :
      ((1-E : ℝ) : ℂ)*g r-deriv (deriv g) r = residual E g r := rfl
  simp_rw [eq]
  constructor
  · intro hE ε hε
    obtain ⟨g,ho,hm,h⟩ := packet hE hε
    refine ⟨g,ho,hm,?_⟩
    rw [← SchwartzMap.integral_norm_sq_fourier g,
        ← SchwartzMap.integral_norm_sq_fourier (residual E g),
      ← integral_const_mul]
    apply integral_mono (mass_int _) ((mass_int _).const_mul _)
    intro x
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (h x) 2
  · intro h
    by_contra! hE
    obtain ⟨g,_,hm,hh⟩ := h ((1-E)/2) (by linarith)
    have hb : (1-E)^2*(∫ r, ‖g r‖^2) ≤ ∫ r, ‖residual E g r‖^2 := by
      rw [← SchwartzMap.integral_norm_sq_fourier g,
        ← SchwartzMap.integral_norm_sq_fourier (residual E g),
        ← integral_const_mul]
      apply integral_mono ((mass_int _).const_mul _) (mass_int _)
      intro v
      dsimp only
      rw [residual_fourier,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply pow_le_pow_left₀ (by linarith) _ 2
      dsimp [energy]
      nlinarith [sq_nonneg (2*π*v)]
    have ht : ((1-E)/2)^2 < (1-E)^2 := by nlinarith [sq_pos_of_pos (show 0 < 1-E by linarith)]
    exact (not_lt_of_ge (hb.trans hh)) (mul_lt_mul_of_pos_right ht hm)

end ProjectAinos.SpecialFunctions.Hyperbolic
