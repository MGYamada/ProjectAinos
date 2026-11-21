/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.FocalPoints
public import ProjectAinos.GeneralRelativity.EnergyCondition

/-!
# The singularity theorem: focusing and maximizing geodesics give incompleteness

Landau–Lifshitz, §119, with `c = 1` and the signature `(−+++)`, in the form of the theorem of
Hawking. The geometric statement is `CoordinateMetric.length_le_of_focusing`: a time function
`x⁰`, the timelike convergence condition, a slice `Σ = {x⁰ = τ}` with `ν θ ≤ −C < 0`, and the
premise that every point to the `ν`-side of `Σ` is reached from `Σ` by a normal geodesic that
maximizes the proper time, give `L ≤ 3/C` for every `ν`-directed normal geodesic segment from `Σ`.

* `toLorentzMetric_ricci_self`, `ricciOf_timelike_nonneg`: with the Einstein equations, the strong
  energy condition, `κ ≥ 0` and `Λ ≤ 0`, the timelike convergence condition holds in co-ordinates.
* `IsSynchronous.length_le_of_einstein`: **Hawking's theorem for a synchronous metric with matter**:
  on a domain that contains the time lines between `Σ` and its points, every `ν`-directed normal
  geodesic segment from a slice with `ν θ ≤ −C` has length at most `3/C`; the time lines supply the
  maximizers.
* `Kasner.length_le_past`: **the vacuum Kasner metrics are an instance towards the past**: every
  past-directed normal geodesic segment from the slice `t = τ` has length at most `3τ` (the
  comoving geodesic of `KasnerIncompleteness.lean` reaches the curvature singularity after the
  proper time `τ`).
* `Kasner.length_le_reverse_dustKasner`: **the contracting dust model is an instance towards the
  future** with matter: the strong energy condition holds, `θ = −(1/|τ| + 1/(|τ| + t₀))` on the
  slice, and every future-directed normal geodesic segment from it has length at most `3/|θ|`.

The premise on maximizers is what global hyperbolicity with the Cauchy surface `Σ` supplies through
the limit curve theorem; its construction is not part of this file. For the synchronous instances it
is proved: the time lines maximize the proper time among all timelike curves.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry LorentzMetric CoordinateMetric

local notation "E" => MinkowskiModel 3

/-- A bilinear form on the model space is determined by its values on the standard basis. -/
theorem clm2_sum (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    B v w = ∑ j, ∑ k, v j * w k * B (Pi.single j 1) (Pi.single k 1) := by
  have hv : B v = ∑ j, v j • B (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ' v]
    rw [map_sum]
    simp only [map_smul]
  have hw (j : Fin 4) : B (Pi.single j 1) w = ∑ k, w k * B (Pi.single j 1) (Pi.single k 1) := by
    conv_lhs => rw [pi_eq_sum_univ' w]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hv]
  simp only [_root_.sum_apply, smul_apply, smul_eq_mul, hw, Finset.mul_sum, mul_assoc]

/-- The native Ricci tensor of a coordinate metric on a vector is `R_{jk} v^j v^k`. -/
theorem toLorentzMetric_ricci_self {U : Opens E} (g : CoordinateMetric .timeNegative 3 U)
    (y : U) (v : E) :
    g.toLorentzMetric.ricci y v v = ∑ j, ∑ k, ricciOf g.coefficient y j k * v j * v k := by
  have hb (j k : Fin 4) :
      g.toLorentzMetric.ricci y (Pi.single j 1) (Pi.single k 1) = ricciOf g.coefficient y j k := by
    have h := g.toLorentzMetric_ricci_chartField y y j k
    rw [physicalChart_chartField, physicalChart_chartField] at h
    exact h
  refine (clm2_sum (g.toLorentzMetric.ricci y) v v).trans ?_
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  erw [hb]
  ring

/-- **The timelike convergence condition in co-ordinates**: with the Einstein equations, the strong
energy condition, `κ ≥ 0` and `Λ ≤ 0`, `R_{jk} v^j v^k ≥ 0` for every timelike `v`. -/
theorem ricciOf_timelike_nonneg {U : Opens E} {g : CoordinateMetric .timeNegative 3 U}
    {κ Λ : ℝ} {T : Tensor.SmoothBilinear («I» := 𝓘(ℝ, E)) (M := U)}
    (hE : g.toLorentzMetric.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g.toLorentzMetric T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0) :
    ∀ z ∈ U, ∀ v : E, g.form z v v < 0 →
      0 ≤ ∑ j, ∑ k, ricciOf g.coefficient z j k * v j * v k := by
  intro z hz v hv
  have h := SatisfiesEinstein.ricci_timelike_nonneg hE hT hκ hΛ ⟨z, hz⟩ (v := v) hv
  rwa [toLorentzMetric_ricci_self] at h

/-- **Hawking's theorem for a synchronous metric with matter**: with the Einstein equations, the
strong energy condition, `κ ≥ 0` and `Λ ≤ 0`, on a domain that contains the time lines between the
slice `x⁰ = τ` and its points, if `ν θ ≤ −C < 0` on the slice (`ν = 1` towards the future, `ν = −1`
towards the past), every `ν`-directed normal geodesic segment from the slice has length at most
`3/C`. -/
theorem IsSynchronous.length_le_of_einstein {U : Opens E} {g : CoordinateMetric .timeNegative 3 U}
    (hs : g.IsSynchronous) {κ Λ : ℝ} {T : Tensor.SmoothBilinear («I» := 𝓘(ℝ, E)) (M := U)}
    (hE : g.toLorentzMetric.SatisfiesEinstein κ Λ T)
    (hT : StrongEnergyCondition g.toLorentzMetric T) (hκ : 0 ≤ κ) (hΛ : Λ ≤ 0)
    {τ C ν : ℝ} (hν : ν * ν = 1) (hC : 0 < C)
    (hU : ∀ z ∈ U, ∀ t ∈ uIcc τ (z 0), z + (t - z 0) • (Pi.single 0 1 : E) ∈ U)
    (hθ : ∀ z ∈ U, z 0 = τ → ν * g.expansion z ≤ -C)
    {γ : ℝ → E} {L : ℝ} (hL : 0 < L) (hγ : g.IsGeodesicSegment γ L) (hγ0 : γ 0 0 = τ)
    (hn : deriv γ 0 = ν • (Pi.single 0 1 : E)) :
    L ≤ 3 / C := by
  have h := hs.length_le_of_focusing hν hC hU (ricciOf_timelike_nonneg hE hT hκ hΛ) hθ hL hγ hγ0
    hn
  norm_num at h
  exact h

namespace Kasner

/-- **The past-directed time line of a Kasner model is a geodesic segment**: `s ↦ x₀ − s e₀` on
`[0, T]` for `T < x₀⁰`, an instance of `IsGeodesicSegment`. -/
theorem isGeodesicSegment_timeLine_past (p : Fin 3 → ℝ) {x₀ : E} {T : ℝ} (hT : T < x₀ 0) :
    (Kasner.metric (Kasner.kasner p)).IsGeodesicSegment
      (fun s => x₀ + (-1 * s) • (Pi.single 0 1 : E)) T :=
  Kasner.isSynchronous.isGeodesicSegment_timeLine fun s hs => by
    change 0 < (x₀ + (-1 * s) • (Pi.single 0 1 : E)) 0
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    linarith [hs.2]

/-- **The past-directed time line of a Kasner model is a timelike curve**, an instance of
`IsTimelikeCurve`. -/
theorem isTimelikeCurve_timeLine_past (p : Fin 3 → ℝ) {x₀ : E} {T : ℝ} (hT : T < x₀ 0) :
    (Kasner.metric (Kasner.kasner p)).IsTimelikeCurve
      (fun s : ℝ => x₀ + (-1 * s) • (Pi.single 0 1 : E)) T := by
  by_cases hT0 : 0 ≤ T
  · have hγ := isGeodesicSegment_timeLine_past p hT
    have hx₀ : x₀ ∈ Kasner.domain (Kasner.kasner p) := by
      change 0 < x₀ 0
      linarith
    have h0 : (fun s : ℝ => x₀ + (-1 * s) • (Pi.single 0 1 : E)) 0 = x₀ := by simp
    have hn : deriv (fun s : ℝ => x₀ + (-1 * s) • (Pi.single 0 1 : E)) 0 =
        (-1 : ℝ) • (Kasner.metric (Kasner.kasner p)).sliceNormal
          ((fun s : ℝ => x₀ + (-1 * s) • (Pi.single 0 1 : E)) 0) := by
      rw [h0, Kasner.isSynchronous.sliceNormal_eq hx₀, (hγ.hasDerivAt 0).deriv]
      have h := (((hasDerivAt_id' (0 : ℝ)).const_mul (-1 : ℝ)).smul_const
        (Pi.single 0 1 : E)).const_add x₀
      rw [mul_one] at h
      exact h.deriv
    have hq := Kasner.isSynchronous.coefficient_inv_zero_zero (hγ.mem 0 ⟨le_rfl, hT0⟩)
    have huu := hγ.form_deriv_self hT0 (by norm_num) hn (by rw [hq]; norm_num)
    exact ⟨hγ.mem, fun s _ => (hγ.hasDerivAt s).differentiableAt,
      hγ.continuous_deriv.continuousOn, fun s hs => by rw [huu s hs]; norm_num⟩
  · push Not at hT0
    have he : Icc (0 : ℝ) T = ∅ := Icc_eq_empty (by linarith)
    exact ⟨by simp [he], by simp [he], by simp [he], by simp [he]⟩

/-- A domain `t ∈ I` with `I` an interval contains the time lines between a slice `t = τ`, `τ ∈ I`,
and each of its points. -/
theorem domain_timeLine {D : Kasner.Data} (hI : (D.I).OrdConnected) {τ : ℝ} (hτ : τ ∈ D.I) :
    ∀ z ∈ Kasner.domain D, ∀ t ∈ uIcc τ (z 0), z + (t - z 0) • (Pi.single 0 1 : E) ∈
      Kasner.domain D := by
  intro z hz t ht
  have h : (z + (t - z 0) • (Pi.single 0 1 : E)) 0 = t := by simp
  change (z + (t - z 0) • (Pi.single 0 1 : E)) 0 ∈ D.I
  rw [h]
  exact hI.uIcc_subset hτ (Kasner.time_mem hz) ht

/-- **The vacuum Kasner metrics are an instance of focusing incompleteness towards the past**:
for Kasner exponents (`Σp = Σp² = 1`) and `τ > 0`, every past-directed normal geodesic segment
from the slice `t = τ` has length at most `3τ`. The slice has `θ = 1/τ`, the Ricci tensor
vanishes, and the time lines maximize the proper time. -/
theorem length_le_past {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1) {τ : ℝ}
    (hτ : 0 < τ) {γ : ℝ → E} {L : ℝ} (hL : 0 < L)
    (hγ : (Kasner.metric (Kasner.kasner p)).IsGeodesicSegment γ L) (hγ0 : γ 0 0 = τ)
    (hn : deriv γ 0 = -(Pi.single 0 1 : E)) :
    L ≤ 3 * τ := by
  have hU := domain_timeLine (D := Kasner.kasner p) (by simpa using ordConnected_Ioi)
    (show τ ∈ (Kasner.kasner p).I from hτ)
  have hRic : ∀ z ∈ Kasner.domain (Kasner.kasner p), ∀ v : E,
      (Kasner.metric (Kasner.kasner p)).form z v v < 0 →
      0 ≤ ∑ j, ∑ k, ricciOf (Kasner.metric (Kasner.kasner p)).coefficient z j k * v j * v k := by
    intro z hz v _
    have h0 := (Kasner.ricciOf_kasner_eq_zero_iff p).mpr (Or.inl ⟨h1, h2⟩) z hz
    simp [h0]
  have hθ : ∀ z ∈ Kasner.domain (Kasner.kasner p), z 0 = τ →
      -1 * (Kasner.metric (Kasner.kasner p)).expansion z ≤ -(1 / τ) := by
    intro z hz hz0
    rw [expansion_metric hz, Kasner.expansion, hz0]
    simp only [Kasner.hubble_kasner p _ hτ]
    rw [← Finset.sum_div, h1]
    linarith
  have h := Kasner.isSynchronous.length_le_of_focusing (by norm_num) (by positivity) hU hRic hθ
    hL hγ hγ0 (by rw [neg_one_smul]; exact hn)
  have h3 : ((3 : ℕ) : ℝ) / (1 / τ) = 3 * τ := by
    field_simp
    norm_num
  rwa [h3] at h

/-- **The contracting dust model is an instance of focusing incompleteness towards the future**:
the time reversal of the dust model of `Kasner.dustKasner`, on `t < 0` with `κ = 1`, satisfies the
Einstein equations with `Λ = 0` and the strong energy condition, and every future-directed normal
geodesic segment from the slice `t = τ < 0` has length at most `3/C` with
`C = 1/|τ| + 1/(|τ| + t₀) = −θ`. -/
theorem length_le_reverse_dustKasner {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1)
    (h2 : ∑ α, p α ^ 2 = 1) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {τ : ℝ} (hτ : τ < 0) {γ : ℝ → E} {L : ℝ}
    (hL : 0 < L)
    (hγ : (Kasner.metric (Kasner.dustKasner p t₀ ht₀).reverse).IsGeodesicSegment γ L)
    (hγ0 : γ 0 0 = τ) (hn : deriv γ 0 = (Pi.single 0 1 : E)) :
    L ≤ 3 / (1 / -τ + 1 / (-τ + t₀)) := by
  set ρ : ℝ → ℝ := fun t => Kasner.dustDensity 1 t₀ (-t) with hρ
  set q : ℝ → ℝ := fun t => (0 : ℝ → ℝ) (-t) with hq
  have hρs : ContDiffOn ℝ ∞ ρ (Kasner.dustKasner p t₀ ht₀).reverse.I :=
    (contDiffOn_dustDensity one_ne_zero ht₀).comp contDiff_neg.contDiffOn fun _ ht' => ht'
  have hT := contDiffOn_perfectFluidStress (D := (Kasner.dustKasner p t₀ ht₀).reverse) hρs
    (contDiffOn_const (c := (0 : ℝ)))
  have hE := (satisfiesEinstein_bilinearOf_iff hT 1 0).mpr
    (isEinstein_reverse (Kasner.isEinstein_dustKasner ht₀ h1 h2 one_ne_zero))
  have hS := strongEnergyCondition_perfectFluidStress (D := (Kasner.dustKasner p t₀ ht₀).reverse)
    ρ q hT
    (fun t ht' => by simpa [hρ, hq] using (Kasner.dustDensity_pos one_pos ht₀ ht').le)
    (fun t ht' => by simpa [hρ, hq] using (Kasner.dustDensity_pos one_pos ht₀ ht').le)
  have hτI : τ ∈ (Kasner.dustKasner p t₀ ht₀).reverse.I := by
    change 0 < -τ
    linarith
  have hord : ((Kasner.dustKasner p t₀ ht₀).reverse.I).OrdConnected := by
    change (Neg.neg ⁻¹' Ioi (0 : ℝ)).OrdConnected
    rw [show Neg.neg ⁻¹' Ioi (0 : ℝ) = Iio 0 by ext t; simp]
    exact ordConnected_Iio
  have hU := domain_timeLine hord hτI
  have hθ : ∀ z ∈ Kasner.domain (Kasner.dustKasner p t₀ ht₀).reverse, z 0 = τ →
      1 * (Kasner.metric (Kasner.dustKasner p t₀ ht₀).reverse).expansion z ≤
        -(1 / -τ + 1 / (-τ + t₀)) := by
    intro z hz hz0
    rw [(reverse_dustKasner_exists_notMem h1 h2 ht₀ hz).1, hz0, one_mul]
  have hC : 0 < 1 / -τ + 1 / (-τ + t₀) := by
    have : 0 < -τ := by linarith
    have : 0 < -τ + t₀ := by linarith
    positivity
  exact IsSynchronous.length_le_of_einstein Kasner.isSynchronous hE hS zero_le_one le_rfl
    (by norm_num) hC hU hθ hL hγ hγ0 (by rw [one_smul]; exact hn)

end Kasner

end ProjectAinos.GeneralRelativity
