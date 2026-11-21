/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.HyperbolicSynthesis
public import ProjectAinos.SpecialFunctions.SphericalBasis
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-! # Completeness of the continuous angular-channel expansion on H³

In the polar coordinate s = cosh r, spatial volume is √(s²−1) ds dΩ on s > 1.
A square-integrable field orthogonal to every regular standing-wave packet in every
spherical harmonic degree vanishes. The proof tests its finitely many angular
coefficients at each degree against arbitrary smooth compactly supported functions
of s, then uses the Hilbert sum on the entire angular sphere.
-/

@[expose] public section
noncomputable section
open Complex Filter Set MeasureTheory FourierTransform
open scoped Real ContDiff Topology FourierTransform SchwartzMap
namespace ProjectAinos.SpecialFunctions.Hyperbolic
open SphericalHarmonics

private abbrev area (s : ℝ) := Real.sqrt (s^2-1)

/-- Hyperbolic radial volume in the coordinate s = cosh r. -/
def radialVolume : Measure ℝ := (volume.restrict (Ioi (1 : ℝ))).withDensity
  (fun s => ENNReal.ofReal (Real.sqrt (s^2-1)))

instance finite_compacts : IsFiniteMeasureOnCompacts radialVolume := by
  constructor
  intro K hK
  have hi : IntegrableOn area K (volume.restrict (Ioi (1 : ℝ))) :=
    (show Continuous area by unfold area; fun_prop).continuousOn.integrableOn_compact hK
  rw [radialVolume,withDensity_apply _ hK.measurableSet]
  simpa only [hasFiniteIntegral_iff_enorm,Real.enorm_eq_ofReal (Real.sqrt_nonneg _)] using
    hi.hasFiniteIntegral

private theorem domain_ae : ∀ᵐ s ∂radialVolume, 1 < s :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

/-- In geodesic radius the same measure has density sinh² r. -/
theorem radialVolume_integral (f : ℝ → ℝ) :
    (∫ s, f s ∂radialVolume) = ∫ r : ℝ in Ioi 0, Real.sinh r^2*f (Real.cosh r) := by
  have him : Real.cosh '' Ioi (0 : ℝ) = Ioi 1 := by
    ext s
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact Real.one_lt_cosh.mpr (show 0 < r from hr).ne'
    · intro hs
      exact ⟨Real.arcosh s,Real.arcosh_pos hs,Real.cosh_arcosh (le_of_lt hs)⟩
  have hinj : InjOn Real.cosh (Ioi (0 : ℝ)) := by
    intro x hx y hy he
    simpa only [Real.arcosh_cosh (le_of_lt hx),Real.arcosh_cosh (le_of_lt hy)]
      using congrArg Real.arcosh he
  rw [radialVolume,integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (by simp),← him, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun r _ => (Real.hasDerivAt_cosh r).hasDerivWithinAt) hinj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have h := Real.sinh_pos_iff.mpr hr
  dsimp only
  rw [abs_of_pos h,ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    show Real.cosh r^2-1=Real.sinh r^2 by linarith [Real.cosh_sq_sub_sinh_sq r],
    Real.sqrt_sq h.le]
  simp [smul_eq_mul,pow_two,mul_assoc]

/-- The Hilbert space of spatial fields in geodesic polar coordinates. -/
abbrev Space := Lp (Lp ℝ 2 (surfaceMeasure 3)) 2 radialVolume

private theorem angular_unique (x : Lp ℝ 2 (surfaceMeasure 3))
    (hx : ∀ n i, inner ℝ (((realBasis n i : l2Space 3 n) : Lp ℝ 2 (surfaceMeasure 3))) x = 0) :
    x=0 := by
  let T := innerSL ℝ x
  have h (n : ℕ) : l2Space 3 n ≤ T.ker := by
    intro y hy
    let w : l2Space 3 n := ⟨y,hy⟩
    have hw := congrArg (fun z : l2Space 3 n => T z.val) ((realBasis n).sum_repr w)
    change T y = 0
    rw [← hw]
    simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower,map_sum,map_smul]
    apply Finset.sum_eq_zero
    intro i _
    have hi : T ((realBasis n i).val) = 0 := by
      change inner ℝ x _ = 0
      rw [real_inner_comm,hx]
    rw [hi,smul_zero]
  have hh := Submodule.topologicalClosure_minimal _ (iSup_le h) T.isClosed_ker
  rw [l2Space_dense (by decide : 0 < 3)] at hh
  have hx' : inner ℝ x x=0 := hh (Submodule.mem_top : x ∈ ⊤)
  exact inner_self_eq_zero.mp hx'

/-- The common orthogonal complement of the continuous spectral packets in all angular
degrees is zero in L²(H³). The packet density is taken in the Fourier variable v. -/
theorem complete (f : Space) (orth : ∀ n (i : Fin (2*n+1)) (g : 𝓢(ℝ,ℂ)),
    (∀ t, g (-t) = -g t) →
    (∫ s, (∫ v : ℝ, (I*(2*π*v : ℝ)*𝓕 g v)*harmonic n (2*π*v) (Real.arcosh s)).re *
      inner ℝ (((realBasis n i : l2Space 3 n) : Lp ℝ 2 (surfaceMeasure 3))) (f s)
      ∂radialVolume) = 0) : f = 0 := by
  let c (n : ℕ) (i : Fin (2*n+1)) (s : ℝ) :=
    inner ℝ (((realBasis n i : l2Space 3 n) : Lp ℝ 2 (surfaceMeasure 3))) (f s)
  have h (n : ℕ) (i : Fin (2*n+1)) : ∀ᵐ s ∂radialVolume, c n i s = 0 := by
    let w (s : ℝ) := area s^n
    have hw : Continuous w := by unfold w area; fun_prop
    have hc : LocallyIntegrable (c n i) radialVolume :=
      ((Lp.memLp f).const_inner ((realBasis n i).val)).locallyIntegrable (by norm_num)
    have hl : LocallyIntegrable (fun s => w s*c n i s) radialVolume := by
      apply locallyIntegrable_iff.mpr
      intro K hK
      obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hw.continuousOn
      exact (hc.integrableOn_isCompact hK).bdd_mul hw.aestronglyMeasurable
        ((ae_restrict_mem hK.measurableSet).mono hC)
    apply (ae_eq_zero_of_integral_contDiff_smul_eq_zero hl ?_).and domain_ae |>.mono
    · intro s hs
      exact (mul_eq_zero.mp hs.1).resolve_left (pow_ne_zero _
        (Real.sqrt_pos.mpr (by nlinarith [hs.2])).ne')
    · intro F hF hK
      obtain ⟨b,hb⟩ := hK.bddAbove
      obtain ⟨g,ho,he⟩ := expand_channel n (ofRealCLM.contDiff.comp hF)
        (B := b+1) (fun s hs => by
          have hnot : s ∉ tsupport F := fun h => by linarith [hb h]
          simp [image_eq_zero_of_notMem_tsupport hnot])
      rw [← orth n i g ho]
      apply integral_congr_ae
      filter_upwards [domain_ae] with s hs
      have hv := (he (Real.arcosh s) (Real.arcosh_pos hs)).2
      rw [← hv,Real.sinh_arcosh hs.le,Real.cosh_arcosh hs.le]
      simp [w,area,c,smul_eq_mul,← ofReal_pow,← ofReal_mul]
      ring
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (h n)),Lp.coeFn_zero (E :=
    Lp ℝ 2 (surfaceMeasure 3)) (p := 2) (μ := radialVolume)] with s hs hz
  rw [hz]
  exact angular_unique _ hs

end ProjectAinos.SpecialFunctions.Hyperbolic
