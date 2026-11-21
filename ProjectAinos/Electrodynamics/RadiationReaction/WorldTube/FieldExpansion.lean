/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.RadiationReaction.WorldTube.Expansion
public import ProjectAinos.Electrodynamics.RadiationReaction.WorldTube.Retarded
import Mathlib.Tactic

/-!
# The retarded field on Dirac's world tube

For a world line `z(τ)` in the proper time (`ProperWorldline`), a proper time `τ` and a unit
vector `N` orthogonal to `u(τ)`, the event `z(τ) + ε N` lies on Dirac's tube of radius `ε`
(`tubeEvent`). Uniformly for `τ ∈ [τ₁, τ₂]` and `N` in a bounded set (`tubeParams`), along
`ε → 0⁺` (`tubeFilter`):

* **The retarded time** (`eventually_isRetarded_tubeEvent`): for small `ε` the event has the
  retarded time `τ − s` with `ε/2 ≤ s ≤ 2ε` (`lag`), found by the intermediate value theorem,
  and `σ = s/ε = 1 − εα/2 + ε²(3α²/8 + β/6 − A/24) + O(ε³)` with `α = N · a`, `β = N · ȧ`,
  `A = a · a` (`hasExp_scaledLag`), from the null condition and a factorization of its
  difference at two roots.
* **The field**: with the separation `R = ε R̂`, the retarded four-velocity `u'` and
  four-acceleration `a'`, and `ρ = ε ρ̂`, the field is `R ∧ Y` with `Y = −(e/4π) ε⁻³ Ŷ`, and the
  flux of the stress tensor through the tube is exactly `T(·, N) = (e/4π)² ε⁻⁴ Ŵ(R̂, Ŷ)` with
  `Ŵ = (R̂·N)(Ŷ·Ŷ) R̂ − (R̂·Ŷ)((Ŷ·N) R̂ + (R̂·N) Ŷ) + ½ (R̂·Ŷ)² N`. The scaled quantities `R̂`,
  `u'`, `ε a'`, `ρ̂`, `ρ̂⁻¹`, `ρ̂⁻²`, `ρ̂⁻³`, `Ŷ` and `Ŵ` are expanded to `O(ε³)` in turn with the
  calculus of `HasExp`, from the expansion of `σ` and the Taylor bounds of the world line at
  `τ − s`; the coefficients are simplified with the Gram relations `u · u = −1`, `u · a = 0`,
  `u · ȧ = −a · a`, `N · N = 1`, `N · u = 0`.
* **The expansion of the integrand of Dirac's tube** (`tubeIntegrand_expansion`): for small
  `ε > 0`, uniformly,
  `ε² (1 + ε α) T(·, N) = (e/4π)² (−N/(2ε²) + a/(2ε) + (A/2) N + (2/3) A u − (3/4) α a
  − (2/3) ȧ) + O(ε)` (`tubeIntegrandMain`), and every point of the tube has a retarded time.
-/

@[expose] public section

noncomputable section

open Set Filter Asymptotics
open scoped Topology

namespace ProjectAinos.Electrodynamics.RadiationReaction.WorldTube

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity

local notation "η" => minkowskiForm LorentzConvention.timeNegative 3

/-! ### First-order Taylor bounds -/

namespace ProperWorldline

variable {w : ProperWorldline}

/-- `u(τ − s) = u(τ) + O(M s)` if `‖a‖ ≤ M` on `[τ − s, τ]`. -/
theorem norm_taylor_vel1 {τ s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (τ - s) τ, ‖w.acc t‖ ≤ M) :
    ‖w.vel (τ - s) - w.vel τ‖ ≤ M * s := by
  have h := norm_le_of_deriv_le (f := fun r => w.vel (τ - r) - w.vel τ)
    (f' := fun r => -w.acc (τ - r)) (n := 0) hs hM
    (fun r _ => (hasDerivAt_comp_sub (w.hasDerivAt_vel (τ - r))).sub_const (w.vel τ))
    (by simp) (fun r hr => by
      rw [norm_neg, pow_zero, mul_one]
      exact hb _ ⟨by linarith [hr.2], by linarith [hr.1]⟩)
  simpa using h

/-- `z(τ) − z(τ − s) = s u(τ) + O(M s²)` if `‖a‖ ≤ M` on `[τ − s, τ]`. -/
theorem norm_taylor_z1 {τ s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (τ - s) τ, ‖w.acc t‖ ≤ M) :
    ‖w.z τ - w.z (τ - s) - s • w.vel τ‖ ≤ M * s ^ 2 := by
  have h := norm_le_of_deriv_le (f := fun r => w.z τ - w.z (τ - r) - r • w.vel τ)
    (f' := fun r => w.vel (τ - r) - w.vel τ) (n := 1) hs hM (fun r _ => by
      have h1 := (hasDerivAt_comp_sub (w.hasDerivAt_z (τ - r))).const_sub (w.z τ)
      have h2 : HasDerivAt (fun r : ℝ => r • w.vel τ) (w.vel τ) r := by
        simpa using (hasDerivAt_id' r).smul_const (w.vel τ)
      exact (h1.fun_sub h2).congr_deriv (by abel)) (by simp) (fun r hr => by
      rw [pow_one]
      exact norm_taylor_vel1 hr.1 hM fun t ht => hb t ⟨by linarith [ht.1, hr.2], ht.2⟩)
  simpa using h

/-- The derivatives of the world line up to the fourth are bounded on a compact interval. -/
theorem exists_deriv_bound (w : ProperWorldline) (t₁ t₂ : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc t₁ t₂, ‖w.vel t‖ ≤ M ∧ ‖w.acc t‖ ≤ M ∧ ‖w.jerk t‖ ≤ M ∧
      ‖w.snap t‖ ≤ M := by
  obtain ⟨M₁, h₁⟩ := isCompact_Icc.exists_bound_of_continuousOn w.continuous_vel.continuousOn
    (s := Icc t₁ t₂)
  obtain ⟨M₂, h₂⟩ := isCompact_Icc.exists_bound_of_continuousOn w.continuous_acc.continuousOn
    (s := Icc t₁ t₂)
  obtain ⟨M₃, h₃⟩ := isCompact_Icc.exists_bound_of_continuousOn w.continuous_jerk.continuousOn
    (s := Icc t₁ t₂)
  obtain ⟨M₄, h₄⟩ := isCompact_Icc.exists_bound_of_continuousOn w.continuous_snap.continuousOn
    (s := Icc t₁ t₂)
  refine ⟨max (max M₁ M₂) (max (max M₃ M₄) 0), by positivity, fun t ht => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (h₁ t ht).trans (by simp)
  · exact (h₂ t ht).trans (by simp)
  · exact (h₃ t ht).trans (by simp)
  · exact (h₄ t ht).trans (by simp)

end ProperWorldline

/-! ### The parameters of the tube -/

/-- `η(a + b, a + b) = η(a, a) + 2 η(a, b) + η(b, b)`. -/
theorem minkowski_add_self (a b : Spacetime) : η (a + b) (a + b) = η a a + 2 * η a b + η b b := by
  simp only [map_add, add_apply]
  rw [minkowskiForm_symmetric _ b a]
  ring

variable (w : ProperWorldline) (τ₁ τ₂ B : ℝ)

/-- The parameters `(τ, N)` of Dirac's tube between `τ₁` and `τ₂`: `τ ∈ [τ₁, τ₂]` and a unit
vector `N` orthogonal to `u(τ)`, with `‖N‖ ≤ B`. -/
def tubeParams : Set (ℝ × Spacetime) :=
  {p | p.1 ∈ Icc τ₁ τ₂ ∧ η p.2 p.2 = 1 ∧ η p.2 (w.vel p.1) = 0 ∧ ‖p.2‖ ≤ B}

/-- The filter `ε → 0⁺`, uniformly in the parameters of the tube. -/
abbrev tubeFilter : Filter (ℝ × (ℝ × Spacetime)) := 𝓝[>] (0 : ℝ) ×ˢ 𝓟 (tubeParams w τ₁ τ₂ B)

/-- The event `z(τ) + ε N` on Dirac's tube, at `x = (ε, (τ, N))`. -/
def tubeEvent (x : ℝ × (ℝ × Spacetime)) : Spacetime := w.z x.2.1 + x.1 • x.2.2

/-- The retarded lag `s = τ − τ_ret` of the event `z(τ) + ε N`. -/
def lag (x : ℝ × (ℝ × Spacetime)) : ℝ := x.2.1 - w.retardedProperTime (tubeEvent w x)

variable {w τ₁ τ₂ B}

private theorem tendsto_fst_tubeFilter :
    Tendsto (fun x : ℝ × (ℝ × Spacetime) => x.1) (tubeFilter w τ₁ τ₂ B) (𝓝 0) :=
  tendsto_fst.mono_right nhdsWithin_le_nhds

private theorem eventually_tubeFilter {q : ℝ → Prop} (hq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), q ε) :
    ∀ᶠ x in tubeFilter w τ₁ τ₂ B, q x.1 ∧ x.2 ∈ tubeParams w τ₁ τ₂ B := by
  rw [eventually_prod_principal_iff]
  filter_upwards [hq] with ε hε p hp using ⟨hε, hp⟩

private theorem eventually_mem_tubeParams :
    ∀ᶠ x in tubeFilter w τ₁ τ₂ B, x.2 ∈ tubeParams w τ₁ τ₂ B :=
  (eventually_tubeFilter (q := fun _ => True) (Eventually.of_forall fun _ => trivial)).mono
    fun _ h => h.2

private theorem eventually_fst_mem_Ioo {ε₀ : ℝ} (h : 0 < ε₀) :
    ∀ᶠ x in tubeFilter w τ₁ τ₂ B, x.1 ∈ Ioo 0 ε₀ ∧ x.2 ∈ tubeParams w τ₁ τ₂ B :=
  eventually_tubeFilter (Ioo_mem_nhdsGT h)

/-- A function of the parameters bounded on the tube is bounded along the filter. -/
private theorem isBigO_one_of_bound {E : Type*} [NormedAddCommGroup E] {c : ℝ × Spacetime → E}
    {C : ℝ}
    (h : ∀ p ∈ tubeParams w τ₁ τ₂ B, ‖c p‖ ≤ C) :
    (fun x : ℝ × (ℝ × Spacetime) => c x.2) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) :=
  IsBigO.of_bound C (eventually_mem_tubeParams.mono fun x hx => by simpa using h x.2 hx)

/-! ### The retarded time of an event of the tube -/

/-- The constant of the null condition on the tube. -/
private def nullConst (M B : ℝ) : ℝ := ‖η‖ * (8 * M * (|B| + 2 * M) + 16 * M ^ 2) + 1

private theorem nullConst_pos {M B : ℝ} (hM : 0 ≤ M) : 0 < nullConst M B := by
  unfold nullConst
  positivity

/-- **The null condition near the world line**: for `r ∈ [ε/2, 2ε]`, `ε ≤ 1/2`, the square of
`ε N + z(τ) − z(τ − r)` is `ε² − r² + O(ε³)`, and its product with `u(τ)` is
`−r + O(r²)`. -/
private theorem tube_null_bound {w : ProperWorldline} {τ ε r M B : ℝ} {N : Spacetime} (hM0 : 0 ≤ M)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hr : r ∈ Icc (ε / 2) (2 * ε))
    (hacc : ∀ t ∈ Icc (τ - r) τ, ‖w.acc t‖ ≤ M) (hu : ‖w.vel τ‖ ≤ M) (hNN : η N N = 1)
    (hNu : η N (w.vel τ) = 0) (hNB : ‖N‖ ≤ B) :
    |η (ε • N + (w.z τ - w.z (τ - r))) (ε • N + (w.z τ - w.z (τ - r))) - (ε ^ 2 - r ^ 2)| ≤
      nullConst M B * ε ^ 3 ∧
    η (ε • N + (w.z τ - w.z (τ - r))) (w.vel τ) ≤ -r + ‖η‖ * M ^ 2 * r ^ 2 := by
  have hr0 : 0 ≤ r := by linarith [hr.1]
  set E := w.z τ - w.z (τ - r) - r • w.vel τ with hE
  have hEb : ‖E‖ ≤ M * r ^ 2 := ProperWorldline.norm_taylor_z1 hr0 hM0 hacc
  have hsplit : ε • N + (w.z τ - w.z (τ - r)) = (ε • N + r • w.vel τ) + E := by
    rw [hE]; abel
  have hH1 : η (ε • N + (w.z τ - w.z (τ - r))) (ε • N + (w.z τ - w.z (τ - r))) =
      ε ^ 2 - r ^ 2 + (2 * η (ε • N + r • w.vel τ) E + η E E) := by
    rw [hsplit, minkowski_add_self, minkowski_add_self]
    simp only [map_smul, smul_apply, smul_eq_mul, hNN, w.vel_unit, hNu]
    ring
  have hA : ‖ε • N + r • w.vel τ‖ ≤ ε * (|B| + 2 * M) := by
    calc ‖ε • N + r • w.vel τ‖ ≤ ε * ‖N‖ + r * ‖w.vel τ‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hε.le, Real.norm_of_nonneg hr0]
      _ ≤ ε * |B| + 2 * ε * M := by
          gcongr
          · exact hNB.trans (le_abs_self B)
          · exact hr.2
      _ = ε * (|B| + 2 * M) := by ring
  have hr2 : r ^ 2 ≤ 4 * ε ^ 2 := by nlinarith [hr.2]
  have hEb' : ‖E‖ ≤ M * (4 * ε ^ 2) := hEb.trans (by gcongr)
  have h1 : |2 * η (ε • N + r • w.vel τ) E| ≤ 2 * (‖η‖ * (ε * (|B| + 2 * M)) *
      (M * (4 * ε ^ 2))) := by
    rw [abs_mul, abs_two]
    gcongr
    exact (abs_minkowski_le _ _).trans (by gcongr)
  have h2 : |η E E| ≤ ‖η‖ * (M * (4 * ε ^ 2)) * (M * (4 * ε ^ 2)) :=
    (abs_minkowski_le _ _).trans (by gcongr)
  refine ⟨?_, ?_⟩
  · rw [hH1, add_sub_cancel_left]
    refine (abs_add_le _ _).trans ?_
    have hε3 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one hε.le (by linarith) (by norm_num)
    have hη := norm_nonneg η
    calc |2 * η (ε • N + r • w.vel τ) E| + |η E E| ≤
          2 * (‖η‖ * (ε * (|B| + 2 * M)) * (M * (4 * ε ^ 2))) +
            ‖η‖ * (M * (4 * ε ^ 2)) * (M * (4 * ε ^ 2)) := add_le_add h1 h2
      _ = ‖η‖ * (8 * M * (|B| + 2 * M)) * ε ^ 3 + ‖η‖ * (16 * M ^ 2) * ε ^ 4 := by ring
      _ ≤ ‖η‖ * (8 * M * (|B| + 2 * M)) * ε ^ 3 + ‖η‖ * (16 * M ^ 2) * ε ^ 3 := by gcongr
      _ ≤ nullConst M B * ε ^ 3 := by
          rw [nullConst]
          nlinarith [pow_pos hε 3]
  · rw [hsplit, map_add, add_apply]
    have hu' : η (ε • N + r • w.vel τ) (w.vel τ) = -r := by
      simp [map_smul, hNu, w.vel_unit]
    rw [hu']
    have h3 : |η E (w.vel τ)| ≤ ‖η‖ * (M * r ^ 2) * M :=
      (abs_minkowski_le _ _).trans (by gcongr)
    have := (abs_le.mp h3).2
    nlinarith

/-- **The retarded time of the tube**: for small `ε`, the event `z(τ) + ε N` has the retarded
time `τ − s` with `ε/2 ≤ s ≤ 2ε`. -/
theorem eventually_isRetarded_tubeEvent :
    ∀ᶠ x in tubeFilter w τ₁ τ₂ B, x.1 / 2 ≤ lag w x ∧ lag w x ≤ 2 * x.1 ∧
      w.IsRetarded (tubeEvent w x) (x.2.1 - lag w x) := by
  obtain ⟨M, hM0, hM⟩ := w.exists_deriv_bound (τ₁ - 1) τ₂
  have hC := nullConst_pos (B := B) hM0
  set K : ℝ := 2 * nullConst M B + 2 * ‖η‖ * M ^ 2 + 1 with hK
  have hKpos : 0 < K := by positivity
  have hε₀pos : 0 < min (1 / 2) (1 / K) := lt_min (by norm_num) (by positivity)
  filter_upwards [eventually_fst_mem_Ioo hε₀pos] with x hx
  obtain ⟨⟨hε, hεlt⟩, ⟨hτ, hNN, hNu, hNB⟩⟩ := hx
  have hε1 : x.1 ≤ 1 / 2 := (lt_of_lt_of_le hεlt (min_le_left _ _)).le
  have hεK : x.1 * K < 1 := by
    have h := lt_of_lt_of_le hεlt (min_le_right _ _)
    rwa [lt_div_iff₀ hKpos] at h
  have hu : ‖w.vel x.2.1‖ ≤ M := (hM x.2.1 ⟨by linarith [hτ.1], hτ.2⟩).1
  have hb : ∀ r ∈ Icc (x.1 / 2) (2 * x.1), _ := fun r hr =>
    tube_null_bound (w := w) (N := x.2.2) hM0 hε hε1 hr (fun t ht =>
      (hM t ⟨by linarith [ht.1, hr.2, hτ.1], by linarith [ht.2, hτ.2]⟩).2.1) hu hNN hNu hNB
  set H : ℝ → ℝ := fun r => η (x.1 • x.2.2 + (w.z x.2.1 - w.z (x.2.1 - r)))
    (x.1 • x.2.2 + (w.z x.2.1 - w.z (x.2.1 - r))) with hH
  have hcont : ContinuousOn H (Icc (x.1 / 2) (2 * x.1)) := by
    have hc : Continuous fun r => x.1 • x.2.2 + (w.z x.2.1 - w.z (x.2.1 - r)) :=
      continuous_const.add (continuous_const.sub (w.continuous_z.comp
        (continuous_const.sub continuous_id)))
    have h7 := ((minkowskiForm .timeNegative 3).continuous.comp hc).clm_apply hc
    exact h7.continuousOn
  have hCε : nullConst M B * x.1 ≤ 1 / 2 := by
    have h1 : 0 ≤ x.1 * (2 * ‖η‖ * M ^ 2 + 1) := by positivity
    rw [hK] at hεK
    nlinarith
  have hC3 : nullConst M B * x.1 ^ 3 ≤ x.1 ^ 2 / 2 := by
    have h1 : nullConst M B * x.1 ^ 3 = (nullConst M B * x.1) * x.1 ^ 2 := by ring
    rw [h1]
    nlinarith [pow_pos hε 2]
  have hlo : H (2 * x.1) ≤ 0 := by
    have h := (abs_le.mp (hb (2 * x.1) ⟨by linarith, le_rfl⟩).1).2
    simp only [hH]
    nlinarith [pow_pos hε 2]
  have hhi : 0 ≤ H (x.1 / 2) := by
    have h := (abs_le.mp (hb (x.1 / 2) ⟨le_rfl, by linarith⟩).1).1
    simp only [hH]
    nlinarith [pow_pos hε 2]
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' (by linarith) hcont ⟨hlo, hhi⟩
  have hX : tubeEvent w x - w.z (x.2.1 - r) = x.1 • x.2.2 + (w.z x.2.1 - w.z (x.2.1 - r)) := by
    simp only [tubeEvent]
    abel
  have hneg : η (tubeEvent w x - w.z (x.2.1 - r)) (w.vel x.2.1) < 0 := by
    rw [hX]
    have h := (hb r hr).2
    have hr' : 0 < r := by linarith [hr.1]
    have : ‖η‖ * M ^ 2 * r < 1 := by nlinarith [hr.2, norm_nonneg η, sq_nonneg M]
    nlinarith
  have hnull : η (tubeEvent w x - w.z (x.2.1 - r)) (tubeEvent w x - w.z (x.2.1 - r)) = 0 := by
    rw [hX]
    exact hr0
  have hret : w.IsRetarded (tubeEvent w x) (x.2.1 - r) := by
    refine ⟨hnull, ?_⟩
    have h0 := pos_time_of_null_of_neg hnull (w.vel_unit x.2.1) (w.vel_future x.2.1) hneg
    simpa using h0
  have hlag : lag w x = r := by
    simp only [lag, ProperWorldline.retardedProperTime_eq hret]
    ring
  rw [hlag]
  exact ⟨hr.1, hr.2, hret⟩

/-! ### Bounds along the tube -/

/-- A constant is bounded. -/
private theorem bdd_const {α : Type*} {l : Filter α} (c : ℝ) :
    (fun _ : α => c) =O[l] (fun _ => (1 : ℝ)) :=
  isBigO_const_const c one_ne_zero l

/-- A product of bounded functions is bounded. -/
private theorem bdd_mul {α : Type*} {l : Filter α} {f g : α → ℝ} (hf : f =O[l] (fun _ => (1 : ℝ)))
    (hg : g =O[l] (fun _ => (1 : ℝ))) : (fun x => f x * g x) =O[l] (fun _ => (1 : ℝ)) := by
  simpa using hf.mul hg

variable (w) in
/-- `α = N · a(τ)`. -/
def cα (p : ℝ × Spacetime) : ℝ := η p.2 (w.acc p.1)

variable (w) in
/-- `β = N · ȧ(τ)`. -/
def cβ (p : ℝ × Spacetime) : ℝ := η p.2 (w.jerk p.1)

variable (w) in
/-- `A = a(τ) · a(τ)`. -/
def cA (p : ℝ × Spacetime) : ℝ := η (w.acc p.1) (w.acc p.1)

variable (w) in
/-- The second coefficient `3α²/8 + β/6 − A/24` of the scaled retarded lag. -/
def cσ₂ (p : ℝ × Spacetime) : ℝ := 3 / 8 * cα w p ^ 2 + cβ w p / 6 - cA w p / 24

variable (w) in
/-- The scaled retarded lag `σ = s/ε`. -/
def scaledLag (x : ℝ × (ℝ × Spacetime)) : ℝ := lag w x / x.1

private theorem isBigO_vel :
    (fun x : ℝ × (ℝ × Spacetime) => w.vel x.2.1) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
  obtain ⟨M, -, hM⟩ := w.exists_deriv_bound τ₁ τ₂
  exact isBigO_one_of_bound (c := fun p => w.vel p.1) fun p hp => (hM p.1 hp.1).1

private theorem isBigO_acc :
    (fun x : ℝ × (ℝ × Spacetime) => w.acc x.2.1) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
  obtain ⟨M, -, hM⟩ := w.exists_deriv_bound τ₁ τ₂
  exact isBigO_one_of_bound (c := fun p => w.acc p.1) fun p hp => (hM p.1 hp.1).2.1

private theorem isBigO_jerk :
    (fun x : ℝ × (ℝ × Spacetime) => w.jerk x.2.1) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
  obtain ⟨M, -, hM⟩ := w.exists_deriv_bound τ₁ τ₂
  exact isBigO_one_of_bound (c := fun p => w.jerk p.1) fun p hp => (hM p.1 hp.1).2.2.1

private theorem isBigO_normal :
    (fun x : ℝ × (ℝ × Spacetime) => x.2.2) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) :=
  isBigO_one_of_bound (c := fun p => p.2) fun _ hp => hp.2.2.2

private theorem isBigO_minkowski {f g : ℝ × (ℝ × Spacetime) → Spacetime}
    (hf : f =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)))
    (hg : g =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ))) :
    (fun x => η (f x) (g x)) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
  simpa using isBigO_bilin (minkowskiForm .timeNegative 3) hf hg

private theorem isBigO_cα :
    (fun x : ℝ × (ℝ × Spacetime) => cα w x.2) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) :=
  isBigO_minkowski isBigO_normal isBigO_acc

private theorem isBigO_cβ :
    (fun x : ℝ × (ℝ × Spacetime) => cβ w x.2) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) :=
  isBigO_minkowski isBigO_normal isBigO_jerk

private theorem isBigO_cA :
    (fun x : ℝ × (ℝ × Spacetime) => cA w x.2) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) :=
  isBigO_minkowski isBigO_acc isBigO_acc

private theorem isBigO_cσ₂ :
    (fun x : ℝ × (ℝ × Spacetime) => cσ₂ w x.2) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
  have h1 : (fun x : ℝ × (ℝ × Spacetime) => 3 / 8 * cα w x.2 ^ 2) =O[tubeFilter w τ₁ τ₂ B]
      (fun _ => (1 : ℝ)) := by
    simpa [sq] using ((isBigO_cα (w := w)).mul isBigO_cα).const_mul_left (3 / 8 : ℝ)
  have h2 : (fun x : ℝ × (ℝ × Spacetime) => cβ w x.2 / 6) =O[tubeFilter w τ₁ τ₂ B]
      (fun _ => (1 : ℝ)) := by
    simpa [div_eq_mul_inv, mul_comm] using (isBigO_cβ (w := w)).const_mul_left (1 / 6 : ℝ)
  have h3 : (fun x : ℝ × (ℝ × Spacetime) => cA w x.2 / 24) =O[tubeFilter w τ₁ τ₂ B]
      (fun _ => (1 : ℝ)) := by
    simpa [div_eq_mul_inv, mul_comm] using (isBigO_cA (w := w)).const_mul_left (1 / 24 : ℝ)
  exact (h1.add h2).sub h3

/-- `σ ∈ [1/2, 2]` eventually. -/
private theorem eventually_scaledLag_mem :
    ∀ᶠ x in tubeFilter w τ₁ τ₂ B, scaledLag w x ∈ Icc (1 / 2) 2 := by
  filter_upwards [eventually_isRetarded_tubeEvent, eventually_fst_mem_Ioo one_pos]
    with x hx hε
  have hε0 := hε.1.1
  refine ⟨?_, ?_⟩
  · rw [scaledLag, le_div_iff₀ hε0]; linarith [hx.1]
  · rw [scaledLag, div_le_iff₀ hε0]; linarith [hx.2.1]

private theorem isBigO_scaledLag :
    (fun x => scaledLag w x) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) :=
  IsBigO.of_bound 2 (eventually_scaledLag_mem.mono fun x hx => by
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [hx.1]), norm_one, mul_one]
    exact hx.2)

/-- The lag is `ε σ`. -/
private theorem eventually_lag_eq :
    ∀ᶠ x in tubeFilter w τ₁ τ₂ B, lag w x = x.1 * scaledLag w x := by
  filter_upwards [eventually_fst_mem_Ioo one_pos] with x hx
  rw [scaledLag, mul_div_cancel₀ _ hx.1.1.ne']

/-- **The Taylor bounds at the retarded time**: eventually the remainders of `z`, `u`, `a` at
`τ − s` are at most `16 M ε⁴`, `8 M ε³`, `4 M ε²`. -/
private theorem eventually_taylor :
    ∃ M, 0 ≤ M ∧ ∀ᶠ x in tubeFilter w τ₁ τ₂ B,
      ‖w.z x.2.1 - w.z (x.2.1 - lag w x) - (lag w x • w.vel x.2.1 -
        (lag w x ^ 2 / 2) • w.acc x.2.1 + (lag w x ^ 3 / 6) • w.jerk x.2.1)‖ ≤
          M * 16 * x.1 ^ 4 ∧
      ‖w.vel (x.2.1 - lag w x) - (w.vel x.2.1 - lag w x • w.acc x.2.1 +
        (lag w x ^ 2 / 2) • w.jerk x.2.1)‖ ≤ M * 8 * x.1 ^ 3 ∧
      ‖w.acc (x.2.1 - lag w x) - (w.acc x.2.1 - lag w x • w.jerk x.2.1)‖ ≤ M * 4 * x.1 ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := w.exists_deriv_bound (τ₁ - 1) τ₂
  refine ⟨M, hM0, ?_⟩
  filter_upwards [eventually_isRetarded_tubeEvent, eventually_fst_mem_Ioo (by norm_num :
    (0 : ℝ) < 1 / 2)] with x hx hε
  obtain ⟨⟨hε0, hε1⟩, ⟨hτ, -⟩⟩ := hε
  have hs0 : 0 ≤ lag w x := by linarith [hx.1]
  have hs1 : lag w x ≤ 2 * x.1 := hx.2.1
  have hb : ∀ t ∈ Icc (x.2.1 - lag w x) x.2.1, ‖w.snap t‖ ≤ M := fun t ht =>
    (hM t ⟨by linarith [ht.1, hτ.1], by linarith [ht.2, hτ.2]⟩).2.2.2
  refine ⟨(ProperWorldline.norm_taylor_z hs0 hM0 hb).trans ?_,
    (ProperWorldline.norm_taylor_vel hs0 hM0 hb).trans ?_,
    (ProperWorldline.norm_taylor_acc hs0 hM0 hb).trans ?_⟩
  · have : lag w x ^ 4 ≤ (2 * x.1) ^ 4 := pow_le_pow_left₀ hs0 hs1 4
    nlinarith
  · have : lag w x ^ 3 ≤ (2 * x.1) ^ 3 := pow_le_pow_left₀ hs0 hs1 3
    nlinarith
  · have : lag w x ^ 2 ≤ (2 * x.1) ^ 2 := pow_le_pow_left₀ hs0 hs1 2
    nlinarith

/-! ### The scaled retarded lag -/

variable (w) in
/-- The scaled chord `D̂ = (z(τ) − z(τ − s))/ε`. -/
private def Dhat (x : ℝ × (ℝ × Spacetime)) : Spacetime :=
  x.1⁻¹ • (w.z x.2.1 - w.z (x.2.1 - lag w x))

variable (w) in
/-- The Taylor polynomial `σ u − (ε σ²/2) a + (ε² σ³/6) ȧ` of the scaled chord. -/
private def Dhat0 (x : ℝ × (ℝ × Spacetime)) : Spacetime :=
  scaledLag w x • w.vel x.2.1 - (x.1 * scaledLag w x ^ 2 / 2) • w.acc x.2.1 +
    (x.1 ^ 2 * scaledLag w x ^ 3 / 6) • w.jerk x.2.1

private theorem isBigO_Dhat_sub :
    (fun x => Dhat w x - Dhat0 w x) =O[tubeFilter w τ₁ τ₂ B] (fun x => x.1 ^ 3) := by
  obtain ⟨M, hM0, hM⟩ := eventually_taylor (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  refine IsBigO.of_bound (16 * M) ?_
  filter_upwards [hM, eventually_fst_mem_Ioo one_pos] with x hx hε
  have hε0 : x.1 ≠ 0 := hε.1.1.ne'
  have c1 : scaledLag w x = x.1⁻¹ * lag w x := by rw [scaledLag, div_eq_inv_mul]
  have c2 : x.1 * scaledLag w x ^ 2 / 2 = x.1⁻¹ * (lag w x ^ 2 / 2) := by
    rw [scaledLag]; field_simp
  have c3 : x.1 ^ 2 * scaledLag w x ^ 3 / 6 = x.1⁻¹ * (lag w x ^ 3 / 6) := by
    rw [scaledLag]; field_simp
  have e : Dhat w x - Dhat0 w x = x.1⁻¹ • (w.z x.2.1 - w.z (x.2.1 - lag w x) -
      (lag w x • w.vel x.2.1 - (lag w x ^ 2 / 2) • w.acc x.2.1 +
        (lag w x ^ 3 / 6) • w.jerk x.2.1)) := by
    rw [Dhat, Dhat0, c2, c3, c1]
    simp only [smul_sub, smul_add, smul_smul]
  rw [e, norm_smul, norm_inv, Real.norm_of_nonneg hε.1.1.le, Real.norm_eq_abs,
    abs_of_pos (pow_pos hε.1.1 3)]
  refine (mul_le_mul_of_nonneg_left hx.1 (inv_nonneg.mpr hε.1.1.le)).trans_eq ?_
  field_simp

private theorem isBigO_Dhat0 :
    (fun x => Dhat0 w x) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
  have h1 := isBigO_pow_one (tendsto_fst_tubeFilter (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B))
  have hσ := isBigO_scaledLag (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have a1 : (fun x : ℝ × (ℝ × Spacetime) => scaledLag w x • w.vel x.2.1) =O[tubeFilter w τ₁ τ₂ B]
      (fun _ => (1 : ℝ)) := by simpa using hσ.smul isBigO_vel
  have a2 : (fun x : ℝ × (ℝ × Spacetime) => (x.1 * scaledLag w x ^ 2 / 2) • w.acc x.2.1) =O[
      tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
    have : (fun x : ℝ × (ℝ × Spacetime) => x.1 * scaledLag w x ^ 2 / 2) =O[tubeFilter w τ₁ τ₂ B]
        (fun _ => (1 : ℝ)) := by
      simpa [div_eq_mul_inv, sq, mul_assoc] using
        ((((h1 1).mul (hσ.mul hσ)).mul (isBigO_const_const (1 / 2 : ℝ) one_ne_zero _)))
    simpa using this.smul isBigO_acc
  have a3 : (fun x : ℝ × (ℝ × Spacetime) => (x.1 ^ 2 * scaledLag w x ^ 3 / 6) • w.jerk x.2.1) =O[
      tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
    have : (fun x : ℝ × (ℝ × Spacetime) => x.1 ^ 2 * scaledLag w x ^ 3 / 6) =O[
        tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
      simpa [div_eq_mul_inv, pow_succ, mul_assoc] using
        ((((h1 2).mul ((hσ.mul hσ).mul hσ)).mul (isBigO_const_const (1 / 6 : ℝ) one_ne_zero _)))
    simpa using this.smul isBigO_jerk
  exact (a1.sub a2).add a3

/-- **The null condition** in the scaled form: `(N + D̂)² = 0`. -/
private theorem eventually_null_Dhat :
    ∀ᶠ x in tubeFilter w τ₁ τ₂ B, η (x.2.2 + Dhat w x) (x.2.2 + Dhat w x) = 0 := by
  filter_upwards [eventually_isRetarded_tubeEvent, eventually_fst_mem_Ioo one_pos] with x hx hε
  have hε0 : x.1 ≠ 0 := hε.1.1.ne'
  have e : tubeEvent w x - w.z (x.2.1 - lag w x) = x.1 • (x.2.2 + Dhat w x) := by
    rw [tubeEvent, Dhat, smul_add, smul_smul, mul_inv_cancel₀ hε0, one_smul]
    abel
  have h := hx.2.2.1
  rw [e] at h
  simp only [map_smul, smul_apply, smul_eq_mul] at h
  have h2 : x.1 * x.1 ≠ 0 := mul_ne_zero hε0 hε0
  have := mul_eq_zero.mp (show x.1 * x.1 * η (x.2.2 + Dhat w x) (x.2.2 + Dhat w x) = 0 by
    rw [mul_assoc]; exact h)
  exact this.resolve_left h2

variable (w) in
/-- The polynomial `f(σ) = 1 − σ²(1 + εα) + ε²(σ³β/3 − σ⁴A/12)` of the null condition. -/
private def nullPoly (x : ℝ × (ℝ × Spacetime)) (σ : ℝ) : ℝ :=
  1 - σ ^ 2 * (1 + x.1 * cα w x.2) + x.1 ^ 2 * (σ ^ 3 * cβ w x.2 / 3 - σ ^ 4 * cA w x.2 / 12)

/-- The square of `N + D̂₀` in terms of `f(σ)`. -/
private theorem minkowski_Dhat0 {x : ℝ × (ℝ × Spacetime)} (hx : x.2 ∈ tubeParams w τ₁ τ₂ B) :
    η (x.2.2 + Dhat0 w x) (x.2.2 + Dhat0 w x) = nullPoly w x (scaledLag w x) -
      x.1 ^ 3 * scaledLag w x ^ 5 * η (w.acc x.2.1) (w.jerk x.2.1) / 6 +
      x.1 ^ 4 * scaledLag w x ^ 6 * η (w.jerk x.2.1) (w.jerk x.2.1) / 36 := by
  obtain ⟨-, hNN, hNu, -⟩ := hx
  have huN : η (w.vel x.2.1) x.2.2 = 0 := by rw [minkowskiForm_symmetric]; exact hNu
  have hua := w.vel_acc x.2.1
  have hau : η (w.acc x.2.1) (w.vel x.2.1) = 0 := by rw [minkowskiForm_symmetric]; exact hua
  have hub := w.vel_jerk x.2.1
  have hbu : η (w.jerk x.2.1) (w.vel x.2.1) = -η (w.acc x.2.1) (w.acc x.2.1) := by
    rw [minkowskiForm_symmetric]; exact hub
  have haN : η (w.acc x.2.1) x.2.2 = cα w x.2 := by rw [minkowskiForm_symmetric]; rfl
  have hbN : η (w.jerk x.2.1) x.2.2 = cβ w x.2 := by rw [minkowskiForm_symmetric]; rfl
  have hba : η (w.jerk x.2.1) (w.acc x.2.1) = η (w.acc x.2.1) (w.jerk x.2.1) :=
    minkowskiForm_symmetric _ _ _
  have hNa : η x.2.2 (w.acc x.2.1) = cα w x.2 := rfl
  have hNb : η x.2.2 (w.jerk x.2.1) = cβ w x.2 := rfl
  simp only [Dhat0, nullPoly, map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply,
    smul_eq_mul, hNN, hNu, huN, hua, hau, hub, hbu, haN, hbN, hba, hNa, hNb, w.vel_unit]
  unfold cA
  ring

/-- **The null condition up to `O(ε³)`**: `f(σ) = O(ε³)`. -/
private theorem isBigO_nullPoly :
    (fun x => nullPoly w x (scaledLag w x)) =O[tubeFilter w τ₁ τ₂ B] (fun x => x.1 ^ 3) := by
  have hl := tendsto_fst_tubeFilter (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  set r := fun x => Dhat w x - Dhat0 w x with hr
  have hrO : r =O[tubeFilter w τ₁ τ₂ B] (fun x => x.1 ^ 3) := isBigO_Dhat_sub
  have hX : (fun x => x.2.2 + Dhat w x) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
    have : (fun x => x.2.2 + Dhat w x) = fun x => x.2.2 + Dhat0 w x + r x := by
      funext x; simp only [hr]; abel
    rw [this]
    exact (isBigO_normal.add isBigO_Dhat0).add (hrO.trans (isBigO_pow_one hl 3))
  have e : ∀ᶠ x in tubeFilter w τ₁ τ₂ B, nullPoly w x (scaledLag w x) =
      -(2 * η (x.2.2 + Dhat w x) (r x)) + η (r x) (r x) +
        x.1 ^ 3 * scaledLag w x ^ 5 * η (w.acc x.2.1) (w.jerk x.2.1) / 6 -
        x.1 ^ 4 * scaledLag w x ^ 6 * η (w.jerk x.2.1) (w.jerk x.2.1) / 36 := by
    filter_upwards [eventually_null_Dhat, eventually_mem_tubeParams] with x h0 hx
    have h1 := minkowski_Dhat0 hx
    have hsplit : x.2.2 + Dhat0 w x = (x.2.2 + Dhat w x) - r x := by simp only [hr]; abel
    rw [hsplit] at h1
    simp only [map_sub, sub_apply, h0] at h1
    rw [minkowskiForm_symmetric _ (r x) (x.2.2 + Dhat w x)] at h1
    linarith
  refine IsBigO.congr' ?_ (e.mono fun x hx => hx.symm) EventuallyEq.rfl
  have hσ := isBigO_scaledLag (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hab := isBigO_minkowski (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B) isBigO_acc isBigO_jerk
  have hbb := isBigO_minkowski (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B) isBigO_jerk isBigO_jerk
  have t1 : (fun x => -(2 * η (x.2.2 + Dhat w x) (r x))) =O[tubeFilter w τ₁ τ₂ B]
      (fun x => x.1 ^ 3) := by
    simpa using ((isBigO_bilin (minkowskiForm .timeNegative 3) hX hrO).const_mul_left 2).neg_left
  have t2 : (fun x => η (r x) (r x)) =O[tubeFilter w τ₁ τ₂ B] (fun x => x.1 ^ 3) := by
    simpa using isBigO_bilin (minkowskiForm .timeNegative 3) hrO (hrO.trans (isBigO_pow_one hl 3))
  have t3 : (fun x => x.1 ^ 3 * scaledLag w x ^ 5 * η (w.acc x.2.1) (w.jerk x.2.1) / 6) =O[
      tubeFilter w τ₁ τ₂ B] (fun x => x.1 ^ 3) := by
    have h5 : (fun x => scaledLag w x ^ 5) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
      simpa using hσ.pow 5
    simpa [div_eq_mul_inv, mul_assoc] using
      ((isBigO_refl (fun x : ℝ × (ℝ × Spacetime) => x.1 ^ 3) _).mul (h5.mul (hab.mul
        (isBigO_const_const (1 / 6 : ℝ) one_ne_zero _))))
  have t4 : (fun x => x.1 ^ 4 * scaledLag w x ^ 6 * η (w.jerk x.2.1) (w.jerk x.2.1) / 36) =O[
      tubeFilter w τ₁ τ₂ B] (fun x => x.1 ^ 3) := by
    have h6 : (fun x => scaledLag w x ^ 6) =O[tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
      simpa using hσ.pow 6
    simpa [div_eq_mul_inv, mul_assoc] using
      ((isBigO_pow_pow hl (m := 3) (n := 4) (by norm_num)).mul (h6.mul (hbb.mul
        (isBigO_const_const (1 / 36 : ℝ) one_ne_zero _))))
  exact ((t1.add t2).add t3).sub t4

variable (w) in
/-- The approximate scaled lag `σ* = 1 − εα/2 + ε²(3α²/8 + β/6 − A/24)`. -/
private def sigmaStar (x : ℝ × (ℝ × Spacetime)) : ℝ :=
  series3 (fun _ => (1 : ℝ)) (fun p => -(cα w p / 2)) (cσ₂ w) x

private theorem hasExp_sigmaStar :
    HasExp (tubeFilter w τ₁ τ₂ B) (sigmaStar w) (fun _ => (1 : ℝ)) (fun p => -(cα w p / 2))
      (cσ₂ w) := by
  unfold sigmaStar
  refine HasExp.series (c₀ := fun _ => (1 : ℝ)) (bdd_const 1) ?_ isBigO_cσ₂
  simpa [div_eq_mul_inv, mul_comm] using
    ((isBigO_cα (w := w)).const_mul_left (1 / 2 : ℝ)).neg_left

/-- **`σ*` solves the null condition to `O(ε³)`**. -/
private theorem isBigO_nullPoly_sigmaStar :
    (fun x => nullPoly w x (sigmaStar w x)) =O[tubeFilter w τ₁ τ₂ B] (fun x => x.1 ^ 3) := by
  have hl := tendsto_fst_tubeFilter (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hS := hasExp_sigmaStar (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have h1 : HasExp (tubeFilter w τ₁ τ₂ B) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) 0 0 :=
    HasExp.const (c₀ := fun _ => (1 : ℝ)) (bdd_const 1)
  have hα := HasExp.const (l := tubeFilter w τ₁ τ₂ B) (isBigO_cα (w := w))
  have hβ := HasExp.const (l := tubeFilter w τ₁ τ₂ B) (isBigO_cβ (w := w))
  have hA := HasExp.const (l := tubeFilter w τ₁ τ₂ B) (isBigO_cA (w := w))
  have hεα := h1.add (hα.eps_smul hl)
  have hS2 := hS.mul hl hS
  have hS3 := hS2.mul hl hS
  have hS4 := hS2.mul hl hS2
  have hc3 : HasExp (tubeFilter w τ₁ τ₂ B) (fun _ => (1 / 3 : ℝ)) (fun _ => (1 / 3 : ℝ)) 0 0 :=
    HasExp.const (c₀ := fun _ => (1 / 3 : ℝ)) (bdd_const _)
  have hc12 : HasExp (tubeFilter w τ₁ τ₂ B) (fun _ => (1 / 12 : ℝ)) (fun _ => (1 / 12 : ℝ)) 0 0 :=
    HasExp.const (c₀ := fun _ => (1 / 12 : ℝ)) (bdd_const _)
  have hin := ((hS3.mul hl hβ).mul hl hc3).sub ((hS4.mul hl hA).mul hl hc12)
  have htot := (h1.sub (hS2.mul hl hεα)).add ((hin.eps_smul hl).eps_smul hl)
  have h0 := htot.congr_coeff (d₀ := 0) (d₁ := 0) (d₂ := 0)
    (Eventually.of_forall fun x => by simp)
    (Eventually.of_forall fun x => by simp)
    (Eventually.of_forall fun x => by simp [cσ₂]; ring)
  have h0' := h0.congr_fun (g := fun x => nullPoly w x (sigmaStar w x))
    (Eventually.of_forall fun x => by simp only [nullPoly, smul_eq_mul]; ring)
  simpa [series3] using h0'.rem

variable (w) in
/-- The factor `q` of `f(σ) − f(σ*) = (σ − σ*) q`. -/
private def nullFactor (x : ℝ × (ℝ × Spacetime)) (σ t : ℝ) : ℝ :=
  -(σ + t) * (1 + x.1 * cα w x.2) + x.1 ^ 2 * (cβ w x.2 * (σ ^ 2 + σ * t + t ^ 2) / 3 -
    cA w x.2 * (σ + t) * (σ ^ 2 + t ^ 2) / 12)

private theorem nullPoly_sub (x : ℝ × (ℝ × Spacetime)) (σ t : ℝ) :
    nullPoly w x σ - nullPoly w x t = (σ - t) * nullFactor w x σ t := by
  simp only [nullPoly, nullFactor]
  ring

/-- Eventually `−q ≥ 1/2`. -/
private theorem eventually_nullFactor :
    ∀ᶠ x in tubeFilter w τ₁ τ₂ B, 1 / 2 ≤ -nullFactor w x (scaledLag w x) (sigmaStar w x) := by
  have hl := tendsto_fst_tubeFilter (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hS := hasExp_sigmaStar (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hσ := isBigO_scaledLag (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hSb := hS.isBigO_one hl
  -- `σ* → 1`
  have t1 := (hS.tendsto_sub hl).eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num :
    (0 : ℝ) < 1 / 2))
  -- `ε α → 0`
  have t2 : Tendsto (fun x : ℝ × (ℝ × Spacetime) => x.1 * cα w x.2) (tubeFilter w τ₁ τ₂ B)
      (𝓝 0) := by
    simpa using ((isBigO_refl (fun x : ℝ × (ℝ × Spacetime) => x.1) _).mul
      (isBigO_cα (w := w))).trans_tendsto (by simpa using hl)
  have t2' := t2.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4))
  -- `ε² Z → 0`
  have hZ : (fun x => cβ w x.2 * (scaledLag w x ^ 2 + scaledLag w x * sigmaStar w x +
      sigmaStar w x ^ 2) / 3 - cA w x.2 * (scaledLag w x + sigmaStar w x) *
        (scaledLag w x ^ 2 + sigmaStar w x ^ 2) / 12) =O[tubeFilter w τ₁ τ₂ B]
          (fun _ => (1 : ℝ)) := by
    have q1 := ((bdd_mul hσ hσ).add (bdd_mul hσ hSb)).add (bdd_mul hSb hSb)
    have q2 := bdd_mul (hσ.add hSb) ((bdd_mul hσ hσ).add (bdd_mul hSb hSb))
    have r1 := bdd_mul (bdd_mul (isBigO_cβ (w := w)) q1) (bdd_const (1 / 3 : ℝ))
    have r2 := bdd_mul (bdd_mul (bdd_mul (isBigO_cA (w := w)) (hσ.add hSb))
      ((bdd_mul hσ hσ).add (bdd_mul hSb hSb))) (bdd_const (1 / 12 : ℝ))
    refine (r1.sub r2).congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
    simp only [div_eq_mul_inv, sq]
    ring
  have t3 : Tendsto (fun x => x.1 ^ 2 * (cβ w x.2 * (scaledLag w x ^ 2 + scaledLag w x *
      sigmaStar w x + sigmaStar w x ^ 2) / 3 - cA w x.2 * (scaledLag w x + sigmaStar w x) *
        (scaledLag w x ^ 2 + sigmaStar w x ^ 2) / 12)) (tubeFilter w τ₁ τ₂ B) (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ × (ℝ × Spacetime) => x.1 ^ 2) (tubeFilter w τ₁ τ₂ B) (𝓝 0) := by
      simpa using hl.pow 2
    simpa using ((isBigO_refl (fun x : ℝ × (ℝ × Spacetime) => x.1 ^ 2) _).mul hZ).trans_tendsto
      (by simpa using h2)
  have t3' := t3.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [t1, t2', t3', eventually_scaledLag_mem] with x h1 h2 h3 h4
  simp only [dist_zero_right, Real.norm_eq_abs] at h1 h2 h3
  rw [abs_lt] at h1 h2 h3
  simp only [nullFactor]
  have hsum : 1 ≤ scaledLag w x + sigmaStar w x := by linarith [h4.1, h1.1]
  have hfac : 3 / 4 ≤ 1 + x.1 * cα w x.2 := by linarith [h2.1]
  have hprod : 3 / 4 ≤ (scaledLag w x + sigmaStar w x) * (1 + x.1 * cα w x.2) := by
    nlinarith
  nlinarith [h3.2]

/-- **The expansion of the scaled retarded lag**:
`σ = 1 − εα/2 + ε²(3α²/8 + β/6 − A/24) + O(ε³)`. -/
theorem hasExp_scaledLag :
    HasExp (tubeFilter w τ₁ τ₂ B) (scaledLag w) (fun _ => (1 : ℝ)) (fun p => -(cα w p / 2))
      (cσ₂ w) := by
  have hS := hasExp_sigmaStar (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  refine ⟨hS.bdd₀, hS.bdd₁, hS.bdd₂, ?_⟩
  have hd : (fun x => nullPoly w x (scaledLag w x) - nullPoly w x (sigmaStar w x)) =O[
      tubeFilter w τ₁ τ₂ B] (fun x => x.1 ^ 3) := isBigO_nullPoly.sub isBigO_nullPoly_sigmaStar
  have hinv : (fun x => (-nullFactor w x (scaledLag w x) (sigmaStar w x))⁻¹) =O[
      tubeFilter w τ₁ τ₂ B] (fun _ => (1 : ℝ)) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_nullFactor] with x hx
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith), norm_one, mul_one,
      inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have e : ∀ᶠ x in tubeFilter w τ₁ τ₂ B, scaledLag w x - series3 (fun _ => (1 : ℝ))
      (fun p => -(cα w p / 2)) (cσ₂ w) x =
      -((nullPoly w x (scaledLag w x) - nullPoly w x (sigmaStar w x)) *
        (-nullFactor w x (scaledLag w x) (sigmaStar w x))⁻¹) := by
    filter_upwards [eventually_nullFactor] with x hx
    have hq : nullFactor w x (scaledLag w x) (sigmaStar w x) ≠ 0 := by
      intro h0; rw [h0] at hx; norm_num at hx
    rw [nullPoly_sub, ← sigmaStar]
    field_simp
  refine IsBigO.congr' ?_ (e.mono fun x hx => hx.symm) EventuallyEq.rfl
  simpa using (hd.mul hinv).neg_left

/-! ### The scaled separation, four-velocity and four-acceleration at the retarded time -/

/-- The Gram relations on the tube. -/
private theorem tube_gram {p : ℝ × Spacetime} (hp : p ∈ tubeParams w τ₁ τ₂ B) :
    η p.2 p.2 = 1 ∧ η p.2 (w.vel p.1) = 0 ∧ η (w.vel p.1) p.2 = 0 ∧
      η (w.vel p.1) (w.vel p.1) = -1 ∧ η (w.vel p.1) (w.acc p.1) = 0 ∧
      η (w.acc p.1) (w.vel p.1) = 0 ∧
      η (w.vel p.1) (w.jerk p.1) = -η (w.acc p.1) (w.acc p.1) ∧
      η (w.jerk p.1) (w.vel p.1) = -η (w.acc p.1) (w.acc p.1) ∧
      η (w.acc p.1) p.2 = η p.2 (w.acc p.1) ∧ η (w.jerk p.1) p.2 = η p.2 (w.jerk p.1) ∧
      η (w.jerk p.1) (w.acc p.1) = η (w.acc p.1) (w.jerk p.1) := by
  obtain ⟨-, hNN, hNu, -⟩ := hp
  refine ⟨hNN, hNu, by rw [minkowskiForm_symmetric]; exact hNu, w.vel_unit _, w.vel_acc _,
    by rw [minkowskiForm_symmetric]; exact w.vel_acc _, w.vel_jerk _,
    by rw [minkowskiForm_symmetric]; exact w.vel_jerk _, minkowskiForm_symmetric _ _ _,
    minkowskiForm_symmetric _ _ _, minkowskiForm_symmetric _ _ _⟩

/-- Simplification of the Minkowski products of the coefficients of the expansions with the Gram
relations of the context. -/
local macro "tube_simp" : tactic => `(tactic| simp only [map_add, map_sub, map_neg, map_smul,
  map_zero,
  add_apply, sub_apply, neg_apply, smul_apply, zero_apply, smul_eq_mul, Pi.add_apply,
  Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply, Pi.one_apply, zero_smul, smul_zero,
  zero_add, add_zero, mul_zero, zero_mul, one_smul, one_mul, mul_one, neg_neg, neg_zero, sub_zero,
  zero_sub, cα, cβ, cA, cσ₂, *])

/-- An equality of coefficients on the tube, after the simplification by the Gram relations. -/
local macro "tube_coeff" : tactic => `(tactic| (
  filter_upwards [eventually_mem_tubeParams] with x hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := tube_gram hx
  tube_simp))

variable (w) in
/-- The scaled separation `R̂ = R/ε = N + D̂` at the retarded time. -/
private def Rhat (x : ℝ × (ℝ × Spacetime)) : Spacetime := x.2.2 + Dhat w x

variable (w) in
/-- The four-velocity `u' = u(τ − s)` at the retarded time. -/
private def uRet (x : ℝ × (ℝ × Spacetime)) : Spacetime := w.vel (x.2.1 - lag w x)

variable (w) in
/-- The scaled four-acceleration `ε a' = ε a(τ − s)` at the retarded time. -/
private def epsAcc (x : ℝ × (ℝ × Spacetime)) : Spacetime := x.1 • w.acc (x.2.1 - lag w x)

private theorem hasExp_vel : HasExp (tubeFilter w τ₁ τ₂ B) (fun x => w.vel x.2.1)
    (fun p => w.vel p.1) 0 0 := HasExp.const (c₀ := fun p : ℝ × Spacetime => w.vel p.1) isBigO_vel

private theorem hasExp_acc : HasExp (tubeFilter w τ₁ τ₂ B) (fun x => w.acc x.2.1)
    (fun p => w.acc p.1) 0 0 := HasExp.const (c₀ := fun p : ℝ × Spacetime => w.acc p.1) isBigO_acc

private theorem hasExp_jerk : HasExp (tubeFilter w τ₁ τ₂ B) (fun x => w.jerk x.2.1)
    (fun p => w.jerk p.1) 0 0 :=
  HasExp.const (c₀ := fun p : ℝ × Spacetime => w.jerk p.1) isBigO_jerk

private theorem hasExp_normal : HasExp (tubeFilter w τ₁ τ₂ B) (fun x => x.2.2) (fun p => p.2) 0 0 :=
  HasExp.const (c₀ := fun p : ℝ × Spacetime => p.2) isBigO_normal

private theorem hasExp_realConst (c : ℝ) :
    HasExp (tubeFilter w τ₁ τ₂ B) (fun _ => c) (fun _ => c) 0 0 :=
  HasExp.const (c₀ := fun _ => c) (bdd_const c)

/-- **The expansion of the scaled separation**:
`R̂ = (N + u) − ε(α u + a)/2 + ε²(σ₂ u + α a/2 + ȧ/6) + O(ε³)`. -/
private theorem hasExp_Rhat : HasExp (tubeFilter w τ₁ τ₂ B) (Rhat w) (fun p => p.2 + w.vel p.1)
    (fun p => -(cα w p / 2) • w.vel p.1 - (1 / 2 : ℝ) • w.acc p.1)
    (fun p => cσ₂ w p • w.vel p.1 + (cα w p / 2) • w.acc p.1 + (1 / 6 : ℝ) • w.jerk p.1) := by
  have hl := tendsto_fst_tubeFilter (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hσ := hasExp_scaledLag (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hσ2 := hσ.mul hl hσ
  have hσ3 := hσ2.mul hl hσ
  have t1 := hσ.smul hl hasExp_vel
  have t2 := (((hσ2.mul hl (hasExp_realConst (1 / 2))).eps_smul hl).smul hl hasExp_acc)
  have t3 := ((((hσ3.mul hl (hasExp_realConst (1 / 6))).eps_smul hl).eps_smul hl).smul hl
    hasExp_jerk)
  have hD0 := (hasExp_normal.add ((t1.sub t2).add t3)).congr_fun (g := fun x => x.2.2 + Dhat0 w x)
    (Eventually.of_forall fun x => by
      simp only [Dhat0, smul_eq_mul]
      congr 2
      · congr 2; ring
      · congr 1; ring)
  have h := hD0.of_isBigO_sub (g := Rhat w) (by
    have : (fun x => Rhat w x - (x.2.2 + Dhat0 w x)) = fun x => Dhat w x - Dhat0 w x := by
      funext x; simp only [Rhat]; abel
    rw [this]
    exact isBigO_Dhat_sub)
  refine h.congr_coeff ?_ ?_ ?_
  · exact Eventually.of_forall fun x => by simp
  · exact Eventually.of_forall fun x => by simp
  · exact Eventually.of_forall fun x => by simp; module

private theorem hasExp_epsLag : HasExp (tubeFilter w τ₁ τ₂ B) (fun x => x.1 • scaledLag w x) 0
    (fun _ => (1 : ℝ)) (fun p => -(cα w p / 2)) :=
  hasExp_scaledLag.eps_smul tendsto_fst_tubeFilter

/-- **The four-velocity at the retarded time**: `u' = u − ε a + ε²(α a + ȧ)/2 + O(ε³)`. -/
private theorem hasExp_uRet : HasExp (tubeFilter w τ₁ τ₂ B) (uRet w) (fun p => w.vel p.1)
    (fun p => -w.acc p.1) (fun p => (cα w p / 2) • w.acc p.1 + (1 / 2 : ℝ) • w.jerk p.1) := by
  have hl := tendsto_fst_tubeFilter (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hs := hasExp_epsLag (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hs2 := hs.mul hl hs
  have t2 := hs.smul hl hasExp_acc
  have t3 := (hs2.mul hl (hasExp_realConst (1 / 2))).smul hl hasExp_jerk
  have hP := (hasExp_vel.sub t2).add t3
  obtain ⟨M, -, hM⟩ := eventually_taylor (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have h := hP.of_isBigO_sub (g := uRet w) (by
    refine IsBigO.of_bound (8 * M) ?_
    filter_upwards [hM, eventually_lag_eq, eventually_fst_mem_Ioo one_pos] with x hx hlag hε
    rw [Real.norm_eq_abs, abs_pow]
    have e : uRet w x - (w.vel x.2.1 - (x.1 • scaledLag w x) • w.acc x.2.1 +
        ((x.1 • scaledLag w x) * (x.1 • scaledLag w x) * (1 / 2)) • w.jerk x.2.1) =
        w.vel (x.2.1 - lag w x) - (w.vel x.2.1 - lag w x • w.acc x.2.1 +
          (lag w x ^ 2 / 2) • w.jerk x.2.1) := by
      rw [uRet, hlag, smul_eq_mul]
      congr 3
      ring
    rw [e]
    refine hx.2.1.trans (le_of_eq ?_)
    rw [abs_of_nonneg hε.1.1.le]
    ring)
  refine h.congr_coeff ?_ ?_ ?_
  · exact Eventually.of_forall fun x => by simp
  · exact Eventually.of_forall fun x => by simp
  · exact Eventually.of_forall fun x => by simp

/-- **The scaled four-acceleration at the retarded time**: `ε a' = ε a − ε² ȧ + O(ε³)`. -/
private theorem hasExp_epsAcc : HasExp (tubeFilter w τ₁ τ₂ B) (epsAcc w) 0 (fun p => w.acc p.1)
    (fun p => -w.jerk p.1) := by
  have hl := tendsto_fst_tubeFilter (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hs := hasExp_epsLag (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hP := (hasExp_acc.sub (hs.smul hl hasExp_jerk)).eps_smul hl
  obtain ⟨M, -, hM⟩ := eventually_taylor (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have h := hP.of_isBigO_sub (g := epsAcc w) (by
    refine IsBigO.of_bound (4 * M) ?_
    filter_upwards [hM, eventually_lag_eq, eventually_fst_mem_Ioo one_pos] with x hx hlag hε
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hε.1.1.le]
    have e : epsAcc w x - x.1 • (w.acc x.2.1 - (x.1 • scaledLag w x) • w.jerk x.2.1) =
        x.1 • (w.acc (x.2.1 - lag w x) - (w.acc x.2.1 - lag w x • w.jerk x.2.1)) := by
      simp only [epsAcc, hlag, smul_eq_mul, smul_sub]
    rw [e, norm_smul, Real.norm_of_nonneg hε.1.1.le]
    calc x.1 * ‖w.acc (x.2.1 - lag w x) - (w.acc x.2.1 - lag w x • w.jerk x.2.1)‖ ≤
          x.1 * (M * 4 * x.1 ^ 2) := mul_le_mul_of_nonneg_left hx.2.2 hε.1.1.le
      _ = 4 * M * x.1 ^ 3 := by ring)
  refine h.congr_coeff ?_ ?_ ?_
  · exact Eventually.of_forall fun x => by simp
  · exact Eventually.of_forall fun x => by simp
  · exact Eventually.of_forall fun x => by simp

variable (w) in
/-- The scaled retarded distance `ρ̂ = ρ/ε = −R̂ · u'`. -/
private def rhoHat (x : ℝ × (ℝ × Spacetime)) : ℝ := -η (Rhat w x) (uRet w x)

variable (w) in
/-- The second coefficient `A/8 − α²/8 − β/3` of the scaled retarded distance. -/
private def cρ₂ (p : ℝ × Spacetime) : ℝ := cA w p / 8 - cα w p ^ 2 / 8 - cβ w p / 3

/-- **The scaled retarded distance**: `ρ̂ = 1 + εα/2 + ε²(A/8 − α²/8 − β/3) + O(ε³)`. -/
private theorem hasExp_rhoHat : HasExp (tubeFilter w τ₁ τ₂ B) (rhoHat w) 1 (fun p => cα w p / 2)
    (cρ₂ w) := by
  have hl := tendsto_fst_tubeFilter (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have h := (hasExp_Rhat.bilin hl (minkowskiForm .timeNegative 3) hasExp_uRet).neg
  refine (h.congr_fun (g := rhoHat w) (Eventually.of_forall fun x => rfl)).congr_coeff ?_ ?_ ?_
  · tube_coeff
  · tube_coeff; ring
  · simp only [cρ₂]; tube_coeff; ring

/-- **The inverse of the scaled retarded distance**:
`ρ̂⁻¹ = 1 − εα/2 + ε²(3α²/8 + β/3 − A/8) + O(ε³)`. -/
private theorem hasExp_rhoInv : HasExp (tubeFilter w τ₁ τ₂ B) (fun x => (rhoHat w x)⁻¹) 1
    (fun p => -(cα w p / 2)) (fun p => 3 / 8 * cα w p ^ 2 + cβ w p / 3 - cA w p / 8) := by
  refine (hasExp_rhoHat.inv tendsto_fst_tubeFilter).congr_coeff ?_ ?_ ?_
  · exact Eventually.of_forall fun x => rfl
  · exact Eventually.of_forall fun x => rfl
  · exact Eventually.of_forall fun x => by simp only [cρ₂]; ring

/-- `ρ̂⁻² = 1 − εα + ε²(α² + 2β/3 − A/4) + O(ε³)`. -/
private theorem hasExp_rhoInv2 : HasExp (tubeFilter w τ₁ τ₂ B) (fun x => (rhoHat w x ^ 2)⁻¹) 1
    (fun p => -cα w p) (fun p => cα w p ^ 2 + 2 / 3 * cβ w p - cA w p / 4) := by
  have h := hasExp_rhoInv (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  refine ((h.mul tendsto_fst_tubeFilter h).congr_fun (Eventually.of_forall fun x => by
    rw [sq, mul_inv])).congr_coeff ?_ ?_ ?_
  · exact Eventually.of_forall fun x => by simp
  · exact Eventually.of_forall fun x => by simp only [Pi.one_apply]; ring
  · exact Eventually.of_forall fun x => by simp only [Pi.one_apply]; ring

/-- `ρ̂⁻³ = 1 − 3εα/2 + ε²(15α²/8 + β − 3A/8) + O(ε³)`. -/
private theorem hasExp_rhoInv3 : HasExp (tubeFilter w τ₁ τ₂ B) (fun x => (rhoHat w x ^ 3)⁻¹) 1
    (fun p => -(3 / 2 * cα w p)) (fun p => 15 / 8 * cα w p ^ 2 + cβ w p - 3 / 8 * cA w p) := by
  have h := hasExp_rhoInv (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have h2 := hasExp_rhoInv2 (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  refine ((h2.mul tendsto_fst_tubeFilter h).congr_fun (Eventually.of_forall fun x => by
    ring)).congr_coeff ?_ ?_ ?_
  · exact Eventually.of_forall fun x => by simp
  · exact Eventually.of_forall fun x => by simp only [Pi.one_apply]; ring
  · exact Eventually.of_forall fun x => by simp only [Pi.one_apply]; ring

/-- `R̂ · (ε a') = εα + ε²(A/2 − β) + O(ε³)`. -/
private theorem hasExp_Rhat_epsAcc : HasExp (tubeFilter w τ₁ τ₂ B)
    (fun x => η (Rhat w x) (epsAcc w x)) 0 (fun p => cα w p)
    (fun p => cA w p / 2 - cβ w p) := by
  refine (hasExp_Rhat.bilin tendsto_fst_tubeFilter (minkowskiForm .timeNegative 3)
    hasExp_epsAcc).congr_coeff ?_ ?_ ?_
  · tube_coeff
  · tube_coeff
  · tube_coeff; ring

variable (w) in
/-- The scaled vector `Ŷ = (ρ̂²)⁻¹ ε a' + (1 + R̂ · ε a') (ρ̂³)⁻¹ u'` of the field, with
`Y = −(e/4π) ε⁻³ Ŷ`. -/
private def Yhat (x : ℝ × (ℝ × Spacetime)) : Spacetime :=
  (rhoHat w x ^ 2)⁻¹ • epsAcc w x +
    ((1 + η (Rhat w x) (epsAcc w x)) * (rhoHat w x ^ 3)⁻¹) • uRet w x

/-- **The scaled vector of the field**: `Ŷ = u − εα u/2 + ε²((A + 3α²)/8 u − ȧ/2) + O(ε³)`. -/
private theorem hasExp_Yhat : HasExp (tubeFilter w τ₁ τ₂ B) (Yhat w) (fun p => w.vel p.1)
    (fun p => -(cα w p / 2) • w.vel p.1)
    (fun p => ((cA w p + 3 * cα w p ^ 2) / 8) • w.vel p.1 - (1 / 2 : ℝ) • w.jerk p.1) := by
  have hl := tendsto_fst_tubeFilter (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hc := ((hasExp_realConst (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B) 1).add
    hasExp_Rhat_epsAcc).mul hl hasExp_rhoInv3
  have h := (hasExp_rhoInv2.smul hl hasExp_epsAcc).add (hc.smul hl hasExp_uRet)
  refine (h.congr_fun (g := Yhat w) (Eventually.of_forall fun x => rfl)).congr_coeff ?_ ?_ ?_
  · tube_coeff
  · tube_coeff; module
  · tube_coeff; module

/-- `R̂ · N = 1 − εα/2 + ε²(α²/2 + β/6) + O(ε³)`. -/
private theorem hasExp_Rhat_normal : HasExp (tubeFilter w τ₁ τ₂ B) (fun x => η (Rhat w x) x.2.2)
    (fun _ => (1 : ℝ)) (fun p => -(cα w p / 2)) (fun p => cα w p ^ 2 / 2 + cβ w p / 6) := by
  refine (hasExp_Rhat.bilin tendsto_fst_tubeFilter (minkowskiForm .timeNegative 3)
    hasExp_normal).congr_coeff ?_ ?_ ?_
  · tube_coeff
  · tube_coeff; ring
  · tube_coeff; ring

/-- `Ŷ · Ŷ = −1 + εα + ε²(3A/4 − α²) + O(ε³)`. -/
private theorem hasExp_Yhat_self : HasExp (tubeFilter w τ₁ τ₂ B) (fun x => η (Yhat w x) (Yhat w x))
    (fun _ => (-1 : ℝ)) (fun p => cα w p) (fun p => 3 / 4 * cA w p - cα w p ^ 2) := by
  refine (hasExp_Yhat.bilin tendsto_fst_tubeFilter (minkowskiForm .timeNegative 3)
    hasExp_Yhat).congr_coeff ?_ ?_ ?_
  · tube_coeff
  · tube_coeff; ring
  · tube_coeff; ring

/-- `R̂ · Ŷ = −1 + εα + ε²(A/4 − α² − 2β/3) + O(ε³)`. -/
private theorem hasExp_Rhat_Yhat : HasExp (tubeFilter w τ₁ τ₂ B) (fun x => η (Rhat w x) (Yhat w x))
    (fun _ => (-1 : ℝ)) (fun p => cα w p) (fun p => cA w p / 4 - cα w p ^ 2 - 2 / 3 * cβ w p) := by
  refine (hasExp_Rhat.bilin tendsto_fst_tubeFilter (minkowskiForm .timeNegative 3)
    hasExp_Yhat).congr_coeff ?_ ?_ ?_
  · tube_coeff
  · tube_coeff; ring
  · tube_coeff; ring

/-- `Ŷ · N = −ε² β/2 + O(ε³)`. -/
private theorem hasExp_Yhat_normal : HasExp (tubeFilter w τ₁ τ₂ B) (fun x => η (Yhat w x) x.2.2)
    0 0 (fun p => -(cβ w p / 2)) := by
  refine (hasExp_Yhat.bilin tendsto_fst_tubeFilter (minkowskiForm .timeNegative 3)
    hasExp_normal).congr_coeff ?_ ?_ ?_
  · tube_coeff
  · tube_coeff
  · tube_coeff; ring

variable (w) in
/-- The scaled flux `Ŵ = (R̂·N)(Ŷ·Ŷ) R̂ − (R̂·Ŷ)((Ŷ·N) R̂ + (R̂·N) Ŷ) + ½ (R̂·Ŷ)² N` of the stress
tensor, with `T(·, N) = (e/4π)² ε⁻⁴ Ŵ`. -/
private def What (x : ℝ × (ℝ × Spacetime)) : Spacetime :=
  (η (Rhat w x) x.2.2 * η (Yhat w x) (Yhat w x)) • Rhat w x -
    η (Rhat w x) (Yhat w x) • (η (Yhat w x) x.2.2 • Rhat w x + η (Rhat w x) x.2.2 • Yhat w x) +
      (1 / 2 * η (Rhat w x) (Yhat w x) ^ 2) • x.2.2

/-- **The scaled flux**:
`Ŵ = −N/2 + ε(α N + a)/2 + ε²((A − α²)/2 N + (2/3) A u − (5/4) α a − (2/3) ȧ) + O(ε³)`. -/
private theorem hasExp_What : HasExp (tubeFilter w τ₁ τ₂ B) (What w) (fun p => -(1 / 2 : ℝ) • p.2)
    (fun p => (cα w p / 2) • p.2 + (1 / 2 : ℝ) • w.acc p.1)
    (fun p => ((cA w p - cα w p ^ 2) / 2) • p.2 + (2 / 3 * cA w p) • w.vel p.1 -
      (5 / 4 * cα w p) • w.acc p.1 - (2 / 3 : ℝ) • w.jerk p.1) := by
  have hl := tendsto_fst_tubeFilter (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hRN := hasExp_Rhat_normal (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hRY := hasExp_Rhat_Yhat (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have t1 := (hRN.mul hl hasExp_Yhat_self).smul hl hasExp_Rhat
  have t2 := hRY.smul hl ((hasExp_Yhat_normal.smul hl hasExp_Rhat).add (hRN.smul hl hasExp_Yhat))
  have t3 := (((hasExp_realConst (1 / 2)).mul hl (hRY.mul hl hRY))).smul hl hasExp_normal
  have h := (t1.sub t2).add t3
  refine (h.congr_fun (g := What w) (Eventually.of_forall fun x => by
    simp only [What, sq])).congr_coeff ?_ ?_ ?_
  · exact Eventually.of_forall fun x => by simp only [Pi.zero_apply]; module
  · exact Eventually.of_forall fun x => by simp only [Pi.zero_apply]; module
  · exact Eventually.of_forall fun x => by simp only [Pi.zero_apply, cσ₂]; module

variable (w) in
/-- The scaled integrand `(1 + εα) Ŵ` of the flux through Dirac's tube. -/
private def tubeIntegrandHat (x : ℝ × (ℝ × Spacetime)) : Spacetime :=
  (1 + x.1 * cα w x.2) • What w x

/-- **The expansion of the integrand of Dirac's tube**:
`(1 + εα) Ŵ = −N/2 + ε a/2 + ε²((A/2) N + (2/3) A u − (3/4) α a − (2/3) ȧ) + O(ε³)`. -/
private theorem hasExp_tubeIntegrandHat : HasExp (tubeFilter w τ₁ τ₂ B) (tubeIntegrandHat w)
    (fun p => -(1 / 2 : ℝ) • p.2) (fun p => (1 / 2 : ℝ) • w.acc p.1)
    (fun p => (cA w p / 2) • p.2 + (2 / 3 * cA w p) • w.vel p.1 -
      (3 / 4 * cα w p) • w.acc p.1 - (2 / 3 : ℝ) • w.jerk p.1) := by
  have hl := tendsto_fst_tubeFilter (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  have hα := HasExp.const (l := tubeFilter w τ₁ τ₂ B) (isBigO_cα (w := w))
  have h := ((hasExp_realConst 1).add (hα.eps_smul hl)).smul hl hasExp_What
  refine (h.congr_fun (g := tubeIntegrandHat w) (Eventually.of_forall fun x => by
    simp only [tubeIntegrandHat, smul_eq_mul])).congr_coeff ?_ ?_ ?_
  · exact Eventually.of_forall fun x => by simp
  · exact Eventually.of_forall fun x => by simp only [Pi.zero_apply]; module
  · exact Eventually.of_forall fun x => by simp only [Pi.zero_apply]; module

/-! ### The flux of the stress tensor of the retarded field through the tube -/

/-- The retarded proper time of an event of the tube is `τ − s`. -/
private theorem retardedProperTime_tubeEvent (x : ℝ × (ℝ × Spacetime)) :
    w.retardedProperTime (tubeEvent w x) = x.2.1 - lag w x := by
  simp only [lag]
  ring

/-- **The exact flux** at the event `z(τ) + εN` of the tube:
`T(·, N) = (e/4π)² ε⁻⁴ Ŵ` for the retarded field. -/
private theorem stressFlux_tubeEvent (e : ℝ) {x : ℝ × (ℝ × Spacetime)} (hε : x.1 ≠ 0)
    (hret : w.IsRetarded (tubeEvent w x) (x.2.1 - lag w x)) :
    stressFlux (retardedField e w (tubeEvent w x)) x.2.2 =
      ((e / (4 * Real.pi)) ^ 2 * (x.1 ^ 4)⁻¹) • What w x := by
  set R := tubeEvent w x - w.z (x.2.1 - lag w x) with hR
  have hRe : R = x.1 • Rhat w x := by
    rw [hR, Rhat, Dhat, tubeEvent, smul_add, smul_smul, mul_inv_cancel₀ hε, one_smul]
    abel
  have hRR : η R R = 0 := hret.1
  have hea : x.1 • w.acc (x.2.1 - lag w x) = epsAcc w x := rfl
  have hY : lwVector e R (w.vel (x.2.1 - lag w x)) (w.acc (x.2.1 - lag w x)) =
      (-(e / (4 * Real.pi)) * (x.1 ^ 3)⁻¹) • Yhat w x := by
    have hρ : -η R (w.vel (x.2.1 - lag w x)) = x.1 * rhoHat w x := by
      rw [hRe, map_smul, smul_apply, smul_eq_mul, rhoHat, uRet]
      ring
    have hRa : η R (w.acc (x.2.1 - lag w x)) = η (Rhat w x) (epsAcc w x) := by
      rw [hRe, ← hea, map_smul, smul_apply, smul_eq_mul, map_smul, smul_eq_mul]
    have s1 : ((x.1 * rhoHat w x) ^ 2)⁻¹ = (x.1 ^ 3)⁻¹ * ((rhoHat w x ^ 2)⁻¹ * x.1) := by
      rw [mul_pow, mul_inv]
      field_simp
    have s2 : (1 + η (Rhat w x) (epsAcc w x)) / (x.1 * rhoHat w x) ^ 3 =
        (x.1 ^ 3)⁻¹ * ((1 + η (Rhat w x) (epsAcc w x)) * (rhoHat w x ^ 3)⁻¹) := by
      rw [mul_pow, div_eq_mul_inv, mul_inv]
      ring
    rw [lwVector, hρ, hRa, s1, s2, Yhat, ← hea, uRet]
    simp only [smul_add, smul_smul]
    module
  rw [retardedField, retardedProperTime_tubeEvent, ← hR, hY, stressFlux_bivector hRR, hRe]
  simp only [map_smul, smul_apply, smul_eq_mul, What]
  have h4 : (x.1 ^ 4)⁻¹ = (x.1 ^ 3)⁻¹ * (x.1 ^ 3)⁻¹ * x.1 * x.1 := by
    field_simp
  rw [h4]
  module

/-- The integrand of Dirac's tube at `z(τ) + εN` is `(e/4π)² ε⁻² (1 + εα) Ŵ`. -/
private theorem tubeIntegrand_eq (e : ℝ) {x : ℝ × (ℝ × Spacetime)} (hε : x.1 ≠ 0)
    (hret : w.IsRetarded (tubeEvent w x) (x.2.1 - lag w x)) :
    (x.1 ^ 2 * (1 + x.1 * cα w x.2)) • stressFlux (retardedField e w (tubeEvent w x)) x.2.2 =
      ((e / (4 * Real.pi)) ^ 2 * (x.1 ^ 2)⁻¹) • tubeIntegrandHat w x := by
  rw [stressFlux_tubeEvent e hε hret, tubeIntegrandHat, smul_smul, smul_smul]
  congr 1
  field_simp

/-- The leading terms `−N/(2ε²) + a/(2ε) + (A/2) N + (2/3) A u − (3/4) α a − (2/3) ȧ` of the
integrand of Dirac's tube, divided by `(e/4π)²`. -/
def tubeIntegrandMain (w : ProperWorldline) (ε τ : ℝ) (N : Spacetime) : Spacetime :=
  (-(1 / (2 * ε ^ 2))) • N + (1 / (2 * ε)) • w.acc τ +
    ((η (w.acc τ) (w.acc τ) / 2) • N + (2 / 3 * η (w.acc τ) (w.acc τ)) • w.vel τ -
      (3 / 4 * η N (w.acc τ)) • w.acc τ - (2 / 3 : ℝ) • w.jerk τ)

/-- **The expansion of the integrand of Dirac's tube**: uniformly for `τ ∈ [τ₁, τ₂]` and unit
vectors `N ⊥ u(τ)` with `‖N‖ ≤ B`, for small `ε > 0`,
`ε²(1 + ε N · a) T(·, N)(z(τ) + εN) = (e/4π)² (−N/(2ε²) + a/(2ε) + (A/2) N + (2/3) A u
 − (3/4) α a − (2/3) ȧ) + O(ε)` for the retarded field of Liénard and Wiechert. -/
theorem tubeIntegrand_expansion (e : ℝ) (w : ProperWorldline) (τ₁ τ₂ B : ℝ) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∀ τ ∈ Icc τ₁ τ₂, ∀ N : Spacetime, η N N = 1 →
      η N (w.vel τ) = 0 → ‖N‖ ≤ B →
      w.IsRetarded (w.z τ + ε • N) (w.retardedProperTime (w.z τ + ε • N)) ∧
      ‖(ε ^ 2 * (1 + ε * η N (w.acc τ))) • stressFlux (retardedField e w (w.z τ + ε • N)) N -
        (e / (4 * Real.pi)) ^ 2 • tubeIntegrandMain w ε τ N‖ ≤ C * ε := by
  obtain ⟨C, ε₁, hε₁, hC⟩ := (hasExp_tubeIntegrandHat (w := w) (τ₁ := τ₁) (τ₂ := τ₂)
    (B := B)).exists_bound
  have hev := eventually_isRetarded_tubeEvent (w := w) (τ₁ := τ₁) (τ₂ := τ₂) (B := B)
  rw [eventually_prod_principal_iff, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    at hev
  obtain ⟨ε₂, hε₂, hev⟩ := hev
  refine ⟨(e / (4 * Real.pi)) ^ 2 * C, min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε τ hτ N hNN hNu hNB =>
    ?_⟩
  have hp : (τ, N) ∈ tubeParams w τ₁ τ₂ B := ⟨hτ, hNN, hNu, hNB⟩
  have hε0 : 0 < ε := hε.1
  have hdist : dist ε 0 < ε₂ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
    exact lt_of_lt_of_le hε.2 (min_le_right _ _)
  have hret := (hev (y := ε) hdist hε0 (τ, N) hp).2.2
  set x : ℝ × (ℝ × Spacetime) := (ε, (τ, N)) with hx
  have hte : tubeEvent w x = w.z τ + ε • N := rfl
  refine ⟨?_, ?_⟩
  · rw [← hte, retardedProperTime_tubeEvent]
    exact hret
  have h1 := tubeIntegrand_eq (w := w) e (x := x) hε0.ne' hret
  rw [hte] at h1
  have hb := hC ε ⟨hε0, lt_of_lt_of_le hε.2 (min_le_left _ _)⟩ (τ, N) hp
  change ‖(ε ^ 2 * (1 + ε * cα w (τ, N))) • stressFlux (retardedField e w (w.z τ + ε • N)) N -
    (e / (4 * Real.pi)) ^ 2 • tubeIntegrandMain w ε τ N‖ ≤ _
  rw [h1]
  have e2 : ((e / (4 * Real.pi)) ^ 2 * (ε ^ 2)⁻¹) • tubeIntegrandHat w x -
      (e / (4 * Real.pi)) ^ 2 • tubeIntegrandMain w ε τ N =
      ((e / (4 * Real.pi)) ^ 2 * (ε ^ 2)⁻¹) • (tubeIntegrandHat w (ε, (τ, N)) -
        ((-(1 / 2 : ℝ)) • N + ε • ((1 / 2 : ℝ) • w.acc τ) + ε ^ 2 •
          ((cA w (τ, N) / 2) • N + (2 / 3 * cA w (τ, N)) • w.vel τ -
            (3 / 4 * cα w (τ, N)) • w.acc τ - (2 / 3 : ℝ) • w.jerk τ))) := by
    have hε1 : ε ≠ 0 := hε0.ne'
    funext μ
    simp only [tubeIntegrandMain, cA, cα, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    field_simp
    ring
  rw [e2, norm_smul, Real.norm_of_nonneg (by positivity)]
  refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_
  field_simp

end ProjectAinos.Electrodynamics.RadiationReaction.WorldTube
