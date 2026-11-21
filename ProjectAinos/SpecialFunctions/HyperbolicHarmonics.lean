/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import ProjectAinos.SpecialFunctions.SphericalHarmonics
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! # Scalar harmonics on hyperbolic three-space

In geodesic polar coordinates the unit-curvature metric is dr² + sinh² r dΩ².
After multiplication by sinh r, the degree-ℓ radial operator is the half-line
Schrödinger operator with potential 1 + ℓ(ℓ+1)/sinh² r. First-order raising
operators intertwine successive angular degrees.
-/

@[expose] public section
noncomputable section
open Complex Filter Set
open scoped ContDiff Topology
namespace ProjectAinos.SpecialFunctions.Hyperbolic

/-- The radial Laplacian on the coefficient of a degree-ℓ spherical harmonic. -/
def laplacian (l : ℕ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  deriv (deriv f) r+2*(Real.cosh r : ℂ)/Real.sinh r*deriv f r-
    (l : ℂ)*(l+1)/(Real.sinh r : ℂ)^2*f r

/-- The potential in the radial equation after removal of the volume density. -/
def potential (l : ℕ) (r : ℝ) : ℝ := (l : ℝ)*(l+1)/Real.sinh r^2

private abbrev sh (r : ℝ) : ℂ := Real.sinh r
private abbrev ch (r : ℝ) : ℂ := Real.cosh r
private abbrev ct (r : ℝ) := ch r/sh r
private abbrev U (r : ℝ) := (sh r^2)⁻¹

private theorem ds (r : ℝ) : HasDerivAt sh (ch r) r :=
  (Real.hasDerivAt_sinh r).ofReal_comp
private theorem dc (r : ℝ) : HasDerivAt ch (sh r) r :=
  (Real.hasDerivAt_cosh r).ofReal_comp
private theorem ns {r : ℝ} (hr : 0 < r) : sh r ≠ 0 :=
  ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hr).ne'
private theorem hyp (r : ℝ) : ch r^2-sh r^2=1 := by exact_mod_cast Real.cosh_sq_sub_sinh_sq r

private theorem dct {r : ℝ} (hr : 0 < r) : HasDerivAt ct (-U r) r := by
  apply ((dc r).div (ds r) (ns hr)).congr_deriv
  change (sh r*sh r-ch r*ch r)/sh r^2 = -((sh r^2)⁻¹)
  rw [show sh r*sh r-ch r*ch r = -1 by linear_combination -(hyp r)]
  ring

private theorem dU {r : ℝ} (hr : 0 < r) : HasDerivAt U (-2*ct r*U r) r := by
  apply (((ds r).pow 2).inv (pow_ne_zero _ (ns hr))).congr_deriv
  dsimp only [ct,U,Pi.pow_apply]
  have hn := ns hr
  generalize sh r = y at hn ⊢
  field_simp
  ring

/-- Conjugation of the geometric radial operator to its one-dimensional potential. -/
theorem conjugate (l : ℕ) {g : ℝ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    (Real.sinh r : ℂ)*laplacian l (fun t => g t/(Real.sinh t : ℂ)) r =
      deriv (deriv g) r-(1+potential l r : ℝ)*g r := by
  let f (t : ℝ) := g t/sh t
  have hi : ContDiffOn ℝ ∞ (fun t => (Real.sinh t)⁻¹) (Ioi 0) :=
    Real.contDiff_sinh.contDiffOn.inv (fun _ ht => (Real.sinh_pos_iff.mpr ht).ne')
  have hf : ContDiffOn ℝ ∞ f (Ioi 0) := by
    apply (hg.mul (ofRealCLM.contDiff.comp_contDiffOn hi)).congr
    intro t _
    simp [f,sh,div_eq_mul_inv]
  have hd {t : ℝ} (ht : 0 < t) := ((hf.contDiffAt (Ioi_mem_nhds ht)).differentiableAt
    (by simp)).hasDerivAt
  have hf' : ContDiffOn ℝ ∞ (deriv f) (Ioi 0) := hf.deriv_of_isOpen isOpen_Ioi (by simp)
  have hd' := ((hf'.contDiffAt (Ioi_mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  have he {t : ℝ} (ht : 0 < t) : sh t*f t = g t := by
    dsimp only [f]
    rw [mul_comm,div_mul_cancel₀ _ (ns ht)]
  have h (t : ℝ) (ht : 0 < t) : deriv g t = ch t*f t+sh t*deriv f t := by
    have e : g =ᶠ[𝓝 t] fun u => sh u*f u := by
      filter_upwards [Ioi_mem_nhds ht] with u hu using (he hu).symm
    exact e.deriv_eq.trans ((ds t).mul (hd ht)).deriv
  have H : deriv g =ᶠ[𝓝 r] fun t => ch t*f t+sh t*deriv f t := by
    filter_upwards [Ioi_mem_nhds hr] with t ht using h t ht
  have H' : deriv (fun t => ch t*f t+sh t*deriv f t) r = _ :=
    (((dc r).mul (hd hr)).add ((ds r).mul hd')).deriv
  rw [H.deriv_eq,H',← he hr]
  change sh r * (deriv (deriv f) r+2*ch r/sh r*deriv f r-
    (l : ℂ)*(l+1)/sh r^2*f r) = _
  simp only [potential,ofReal_add,ofReal_div,ofReal_pow,ofReal_mul,ofReal_natCast,ofReal_one]
  change sh r*(_+2*ch r/sh r*_-(l : ℂ)*(l+1)/sh r^2*f r) =
    _ - (1+(l : ℂ)*(l+1)/sh r^2)*(sh r*f r)
  have hn := ns hr
  generalize sh r = y at hn ⊢
  field_simp
  ring

/-- The radial differential raising operator at step j. -/
def raise (j : ℕ) (g : ℝ → ℂ) (r : ℝ) :=
  deriv g r-(j : ℂ)*((Real.cosh r : ℂ)/Real.sinh r)*g r

private theorem smooth_ct : ContDiffOn ℝ ∞ ct (Ioi 0) := by
  have h : ContDiffOn ℝ ∞ (Real.cosh / Real.sinh) (Ioi 0) :=
    Real.contDiff_cosh.contDiffOn.div Real.contDiff_sinh.contDiffOn
      (fun _ ht => (Real.sinh_pos_iff.mpr ht).ne')
  apply (ofRealCLM.contDiff.comp_contDiffOn h).congr
  intro t _
  simp [ct,ch,sh]


private theorem smooth_raise {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (j : ℕ) :
    ContDiffOn ℝ ∞ (raise j g) (Ioi 0) :=
  (hg.deriv_of_isOpen isOpen_Ioi (by simp)).sub ((contDiffOn_const.mul smooth_ct).mul hg)

private theorem intertwine {l : ℕ} {g : ℝ → ℂ} {w : ℂ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (he : ∀ r : ℝ, 0 < r → deriv (deriv g) r =
      (((l : ℂ)*(l+1))*U r-w)*g r) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (raise (l+1) g)) r =
      ((((l+1 : ℕ) : ℂ)*(l+1+1))*U r-w)*raise (l+1) g r := by
  let j : ℂ := (l : ℂ)+1
  have h₁ {t : ℝ} (ht : 0 < t) := (hg.contDiffAt (Ioi_mem_nhds ht)).differentiableAt
    (by simp)
  have hD : ContDiffOn ℝ ∞ (deriv g) (Ioi 0) := hg.deriv_of_isOpen isOpen_Ioi (by simp)
  have h₂ {t : ℝ} (ht : 0 < t) := (hD.contDiffAt
    (Ioi_mem_nhds ht)).differentiableAt (by simp)
  have d (t : ℝ) (ht : 0 < t) : deriv (raise (l+1) g) t =
      ((j*j)*U t-w)*g t-j*ct t*deriv g t := by
    change deriv (fun s => deriv g s-((l+1 : ℕ) : ℂ)*ct s*g s) _ = _
    calc
      _ = _ := ((h₂ ht).hasDerivAt.sub (((dct ht).const_mul ((l+1 : ℕ) : ℂ)).mul
        (h₁ ht).hasDerivAt)).deriv
      _ = _ := ?_
    rw [he t ht]
    dsimp only [j]
    push_cast
    ring
  have hd : deriv (raise (l+1) g) =ᶠ[𝓝 r]
      fun t => ((j*j)*U t-w)*g t-j*ct t*deriv g t :=
    by filter_upwards [Ioi_mem_nhds hr] with t ht using d t ht
  rw [hd.deriv_eq]
  calc
    _ = _ := (((((dU hr).const_mul (j*j)).sub_const w).mul (h₁ hr).hasDerivAt).sub
      (((dct hr).const_mul j).mul (h₂ hr).hasDerivAt)).deriv
    _ = _ := ?_
  rw [he r hr,raise]
  dsimp only [j,ct,U]
  push_cast
  ring

/-- Iterate the angular raising operator starting with a one-dimensional wave. -/
def raised (g : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => g
  | n+1 => raise (n+1) (raised g n)

private theorem raised_smooth {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (l : ℕ) :
    ContDiffOn ℝ ∞ (raised g l) (Ioi 0) := by
  induction l with
  | zero => exact hg
  | succ l ih => exact smooth_raise ih _

/-- The ladder carries every free one-dimensional wave to the corresponding angular
channel with the same spectral parameter. -/
theorem raised_equation {g : ℝ → ℂ} {w : ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (he : ∀ r : ℝ, 0 < r → deriv (deriv g) r = -w*g r) (l : ℕ) {r : ℝ} (hr : 0 < r) :
    laplacian l (fun t => raised g l t/(Real.sinh t : ℂ)) r =
      -(1+w)*(raised g l r/(Real.sinh r : ℂ)) := by
  have H (n : ℕ) : ∀ t : ℝ, 0 < t → deriv (deriv (raised g n)) t =
      (((n : ℂ)*(n+1))*U t-w)*raised g n t := by
    induction n with
    | zero => simpa [raised] using he
    | succ n ih =>
      intro t ht
      simpa only [raised,Nat.cast_succ] using intertwine (raised_smooth hg n) ih ht
  have h := conjugate l hr (raised_smooth hg l)
  rw [H l r hr] at h
  apply mul_left_cancel₀ (ns hr)
  rw [show sh r*(-(1+w)*(raised g l r/sh r)) = -(1+w)*raised g l r by
    rw [← mul_assoc,mul_comm (sh r),mul_assoc,mul_comm (sh r),div_mul_cancel₀ _ (ns hr)],h]
  dsimp only [potential,U]
  simp only [ofReal_div,ofReal_pow,ofReal_add,ofReal_mul,ofReal_natCast,ofReal_one]
  ring

/-- The regular sine seed, with the threshold solution r at λ = 0. -/
def sineSeed (k r : ℝ) : ℂ :=
  if k = 0 then (r : ℂ) else (Real.sin (k*r)/k : ℝ)

/-- The regular separated hyperbolic harmonic in angular degree ℓ. -/
def harmonic (l : ℕ) (k r : ℝ) : ℂ :=
  if r=0 then (if l=0 then 1 else 0) else raised (sineSeed k) l r/(Real.sinh r : ℂ)

/-- The eigenvalue is −(1+λ²) in every angular channel. -/
theorem harmonic_equation (l : ℕ) (k : ℝ) {r : ℝ} (hr : 0 < r) :
    laplacian l (harmonic l k) r = -(1+(k : ℂ)^2)*harmonic l k r := by
  have he : harmonic l k =ᶠ[𝓝 r] fun t => raised (sineSeed k) l t/(Real.sinh t : ℂ) := by
    filter_upwards [Ioi_mem_nhds hr] with t ht
    simp [harmonic,(show (0 : ℝ) < t from ht).ne']
  rw [laplacian,he.deriv.deriv_eq,he.deriv_eq,he.eq_of_nhds]
  apply raised_equation _ _ _ hr
  · unfold sineSeed
    split
    · exact ofRealCLM.contDiff.contDiffOn
    · exact (ofRealCLM.contDiff.comp (show ContDiff ℝ ∞ (fun r => Real.sin (k*r)/k) by
        fun_prop)).contDiffOn
  · intro t _
    by_cases h : k = 0
    · subst k
      have d : deriv (sineSeed 0) = fun _ => (1 : ℂ) :=
        funext fun t => by
          rw [show sineSeed 0 = fun y : ℝ => (y : ℂ) from funext fun _ => by simp [sineSeed]]
          exact_mod_cast ((hasDerivAt_id' t).ofReal_comp).deriv
      rw [d]
      simp
    · have d (s : ℝ) : HasDerivAt (sineSeed k) (Real.cos (k*s) : ℂ) s := by
        change HasDerivAt (fun s : ℝ => if k=0 then (s : ℂ) else ↑(Real.sin (k*s)/k)) _ s
        simp only [h,↓reduceIte]
        apply HasDerivAt.ofReal_comp
        apply (((Real.hasDerivAt_sin _).comp s ((hasDerivAt_id' s).const_mul k)).div_const
          k).congr_deriv
        field_simp
      rw [show deriv (sineSeed k) = fun s => (Real.cos (k*s) : ℂ) from funext fun s => (d s).deriv]
      calc
        _ = _ := (((Real.hasDerivAt_cos _).comp t
          ((hasDerivAt_id' t).const_mul k)).ofReal_comp).deriv
        _ = _ := ?_
      simp only [sineSeed,h,↓reduceIte]
      push_cast
      field_simp [ofReal_ne_zero.mpr h]

end ProjectAinos.SpecialFunctions.Hyperbolic
