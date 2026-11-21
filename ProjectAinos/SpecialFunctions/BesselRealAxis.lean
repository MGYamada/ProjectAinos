/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Bessel
import Mathlib.Tactic

/-! # Real orders on the positive Bessel axis -/

@[expose] public section
noncomputable section
open Complex Filter FormalMultilinearSeries
open scoped Topology

namespace ProjectAinos.SpecialFunctions.Bessel

private abbrev F (b : ℂ) := regularizedHGFun 0 {b}

private theorem real_F (b y : ℝ) : ((F b y).re : ℂ) = F b y := by
  let f (n : ℕ) := (y : ℂ)^n*regularizedHGFunCoeff 0 {(b : ℂ)} n
  have hs : HasSum f (F b y) := by
    simpa [f,F,regularizedHGFun,apply_eq_pow_smul_coeff,smul_eq_mul] using
      ((regularizedHGFunSeries 0 {(b : ℂ)}).hasFPowerSeriesOnBall (by simp)).hasSum
        (y := (y : ℂ)) (by simp)
  apply conj_eq_iff_re.mp
  have hconj := (Complex.conjCLE.toContinuousLinearMap.hasSum hs)
  apply HasSum.unique hconj
  apply hs.congr_fun
  intro n
  change starRingEnd ℂ (f n) = f n
  simp [f,regularizedHGFunCoeff,← Gamma_conj]

/-- At positive real argument and real order, the principal first-kind function is real. -/
theorem ofReal_re_besselJ (a : ℝ) {x : ℝ} (hx : 0 < x) :
    ((besselJ a x).re : ℂ) = besselJ a x := by
  have he : besselJ a x = ((x/2)^a : ℝ) * F ((a+1 : ℝ) : ℂ) ((-(x/2)^2 : ℝ) : ℂ) := by
    unfold besselJ
    rw [ofReal_cpow (by positivity : 0 ≤ x/2)]
    push_cast
    rfl
  rw [he,re_ofReal_mul,ofReal_mul,real_F]

/-- Frobenius normalization in the half-argument variable for every real order. -/
theorem tendsto_scaled_besselJ (a : ℝ) :
    Tendsto (fun u : ℝ => u^(-a)*(besselJ a (2*u : ℝ)).re) (𝓝[>] 0)
      (𝓝 (Real.Gamma (a+1))⁻¹) := by
  have h := (analyticAt_regularizedHGFun_zero (b := {((a+1 : ℝ) : ℂ)}) 0).continuousAt
  have hv : ContinuousAt (fun u : ℝ => ((-u^2 : ℝ) : ℂ)) 0 := by fun_prop
  have hc := h.tendsto.comp (show Tendsto (fun u : ℝ => ((-u^2 : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) by
    simpa using hv.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
  have h₀ : F ((a+1 : ℝ) : ℂ) 0 = ((Real.Gamma (a+1))⁻¹ : ℝ) := by
    rw [F,regularizedHGFun_zero]
    simp [regularizedHGFunCoeff,← Gamma_ofReal]
  have hr := (Complex.continuous_re.tendsto _).comp hc
  change Tendsto _ _ (𝓝 (F ((a+1 : ℝ) : ℂ) 0).re) at hr
  rw [h₀,ofReal_re] at hr
  apply hr.congr'
  · filter_upwards [self_mem_nhdsWithin] with u hu
    have hp : 0 < u := hu
    change (F ((a+1 : ℝ) : ℂ) ((-u^2 : ℝ) : ℂ)).re = _
    rw [besselJ,show ((2*u : ℝ) : ℂ)/2 = (u : ℂ) by push_cast; ring,
      ← ofReal_cpow hp.le,re_ofReal_mul,Real.rpow_neg hp.le]
    push_cast
    field_simp [(Real.rpow_pos_of_pos hp a).ne']

end ProjectAinos.SpecialFunctions.Bessel
