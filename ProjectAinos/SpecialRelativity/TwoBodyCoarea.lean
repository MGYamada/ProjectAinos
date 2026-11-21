/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.TwoBodyMeasure
public import ProjectAinos.SmoothGeometry.Euclidean.PolarLIntegral
public import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The product of two shell measures as an integral over the total momentum

For two particles with the masses `m₃, m₄ ≥ 0` and the shell measures `μᵢ = d³πᵢ/Eᵢ`
(`FutureShell.measure`), `lintegral_regular_eq` is the integration formula

`∫∫_{regular} f dμ₃ dμ₄ = ∫_{region} (∫ f dν_P) d⁴P`

for every measurable `f ≥ 0`, with the measures `ν_P = fibreMeasure m₃ m₄ P` of the fibres and
the Lebesgue measure `d⁴P` on the regular total momenta (Landau–Lifshitz, *The Classical Theory of
Fields*, §12). It identifies `ν_P` as the product measure constrained to the total momentum `P`,
with the normalization `q/M`. As measures, the product restricted to the regular pairs is the
integral of the measurable family `P ↦ ν_P` (`restrict_regular_eq_bind`). The pairs that are not
regular form a null set (`prod_regular_compl`): for them the first space momentum lies on the
line of the total space momentum (`mem_span_of_notMem_regular`), by the equality case of the
reverse Cauchy–Schwarz inequality. So the formula holds for the whole product measure
(`lintegral_prod_eq`), and `prod_eq_bind` is the disintegration
`μ₃ ⊗ μ₄ = ∫ ν_P d⁴P` over the regular total momenta.

The proof changes the variables in four steps.

1. The total space momentum `K = π₃ + π₄` replaces `π₄` (`measurePreserving_prod_sub`).
2. For a fixed `K`, the rest momentum `k` of the first particle replaces `π₃`:
   `π₃ = labFirst m₃ m₄ K k = k + c(k) K`. The derivative is the identity plus a map of rank one
   (`hasFDerivAt_labFirst`), with the Jacobian `(P⁰E₃ + ⟨K, k⟩)(P⁰E₄ − ⟨K, k⟩)/(M P⁰ E₃ E₄)`
   (`det_labDeriv`), where `Eᵢ` are the energies in the rest frame and `M = E₃ + E₄`. The map is
   injective on `k ≠ 0` with the image of the regular pairs (`injOn_labFirst`,
   `image_labFirst`), and the densities `1/E` of the two shells turn the Jacobian into
   `M/(P⁰E₃E₄)` (`jacobian_mul_density`).
3. Polar co-ordinates `k = r n` (`Sphere.lintegral_pi_eq_lintegral_sphere_Ioi`).
4. The radial substitution `P⁰ = √(M(r)² + |K|²)` with `M(r) = √(m₃² + r²) + √(m₄² + r²)`, of
   derivative `r M²/(P⁰E₃E₄)` (`hasDerivAt_radialEnergy`); then `r²M/(P⁰E₃E₄) dr = (q/M) dP⁰`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace ProjectAinos.SpecialRelativity.TwoBodyFibre

open SmoothGeometry SmoothGeometry.Minkowski FutureShell FreeParticle

variable {d : ℕ} {m₃ m₄ : ℝ}

/-! ### The derivative of the boost in the rest momentum -/

/-- The gradient of the coefficient `c(k)` in `labFirst K k = k + c(k) K`:
`K/(M(M + P⁰)) + ((E₄ − E₃ − ⟨K, k⟩/P⁰)/(M E₃ E₄)) k`. -/
def labGrad (m₃ m₄ : ℝ) (K k : Fin d → ℝ) : Fin d → ℝ :=
  (pairMass m₃ m₄ k * (pairMass m₃ m₄ k + Real.sqrt (pairMass m₃ m₄ k ^ 2 + ∑ i, K i ^ 2)))⁻¹ •
      K +
    ((energy m₄ k - energy m₃ k - (∑ i, K i * k i) /
        Real.sqrt (pairMass m₃ m₄ k ^ 2 + ∑ i, K i ^ 2)) /
      (pairMass m₃ m₄ k * energy m₃ k * energy m₄ k)) • k

/-- The derivative of `k ↦ labFirst m₃ m₄ K k`: the identity plus a map of rank one. -/
def labDeriv (m₃ m₄ : ℝ) (K k : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.id ℝ (Fin d → ℝ) + (dotCovector (labGrad m₃ m₄ K k)).smulRight K

theorem hasFDerivAt_inv_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {f' : E →L[ℝ] ℝ} {x : E} (hf : HasFDerivAt f f' x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => (f y)⁻¹) (-(f x ^ 2)⁻¹ • f') x :=
  (hasDerivAt_inv hx).comp_hasFDerivAt x hf

theorem dotCovector_smul_add_smul (a b : ℝ) (K k w : Fin d → ℝ) :
    dotCovector (a • K + b • k) w = a * ∑ i, K i * w i + b * ∑ i, k i * w i := by
  rw [dotCovector_apply, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The derivative of the space momentum of the first particle in the rest momentum. -/
theorem hasFDerivAt_labFirst (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    HasFDerivAt (labFirst m₃ m₄ K) (labDeriv m₃ m₄ K k) k := by
  have he₃p := energy_pos_of_ne_zero m₃ hk
  have he₄p := energy_pos_of_ne_zero m₄ hk
  have hMp : 0 < energy m₃ k + energy m₄ k := add_pos he₃p he₄p
  have hs := sum_sq_nonneg K
  have hSp : 0 < (energy m₃ k + energy m₄ k) ^ 2 + ∑ i, K i ^ 2 := by positivity
  have hTp : 0 < Real.sqrt ((energy m₃ k + energy m₄ k) ^ 2 + ∑ i, K i ^ 2) :=
    Real.sqrt_pos.mpr hSp
  have he₃ := hasFDerivAt_energy (mem_domain_of_ne_zero m₃ hk)
  have he₄ := hasFDerivAt_energy (mem_domain_of_ne_zero m₄ hk)
  have hM := he₃.fun_add he₄
  have hA : HasFDerivAt (fun k : Fin d → ℝ => ∑ i, K i * k i) (dotCovector K) k := by
    have h : (fun k : Fin d → ℝ => ∑ i, K i * k i) = ⇑(dotCovector K) :=
      funext fun w => (dotCovector_apply K w).symm
    rw [h]
    exact (dotCovector K).hasFDerivAt
  have hS := (hM.pow 2).add_const (∑ i, K i ^ 2)
  have hT := hS.sqrt hSp.ne'
  have hD := hM.fun_mul (hM.fun_add hT)
  have hDi := hasFDerivAt_inv_comp hD (mul_pos hMp (add_pos hMp hTp)).ne'
  have hMi := hasFDerivAt_inv_comp hM hMp.ne'
  have hc := (hA.fun_mul hDi).fun_add (he₃.fun_mul hMi)
  have hc' := hc.congr_fderiv (g' := dotCovector (labGrad m₃ m₄ K k)) (by
    ext w
    rw [labGrad, dotCovector_smul_add_smul]
    simp only [add_apply, smul_apply, smul_eq_mul, dotCovector_apply, pairMass,
      nsmul_eq_mul, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    generalize ∑ i, K i * w i = C
    generalize ∑ i, k i * w i = B
    generalize ∑ i, K i * k i = A
    field_simp
    ring)
  have hχ := (hasFDerivAt_id k).fun_add (hc'.smul_const K)
  have hfun : labFirst m₃ m₄ K = fun k => id k + ((∑ i, K i * k i) *
      ((energy m₃ k + energy m₄ k) * ((energy m₃ k + energy m₄ k) +
        Real.sqrt ((energy m₃ k + energy m₄ k) ^ 2 + ∑ i, K i ^ 2)))⁻¹ +
      energy m₃ k * (energy m₃ k + energy m₄ k)⁻¹) • K := by
    funext k
    rw [labFirst_eq, div_eq_mul_inv, div_eq_mul_inv]
    rfl
  rw [hfun]
  exact hχ

/-! ### The Jacobian -/

theorem time_totalOf_sq (K k : Fin d → ℝ) :
    time (totalOf m₃ m₄ K k) ^ 2 = pairMass m₃ m₄ k ^ 2 + ∑ i, K i ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sum_sq_nonneg K))

theorem time_totalOf_pos (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    0 < time (totalOf m₃ m₄ K k) := by
  have h1 := pairMass_pos (m₃ := m₃) (m₄ := m₄) hk
  have h2 := sum_sq_nonneg K
  exact Real.sqrt_pos.mpr (by positivity)

/-- `|⟨K, k⟩| < P⁰ E(k)` for `k ≠ 0`. -/
theorem abs_dot_lt (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) (m : ℝ) :
    |∑ i, K i * k i| < time (totalOf m₃ m₄ K k) * energy m k := by
  have hcs := sq_sum_mul_le K k
  have hρ := sum_sq_pos hk
  have hT := time_totalOf_sq (m₃ := m₃) (m₄ := m₄) K k
  have hTp := time_totalOf_pos (m₃ := m₃) (m₄ := m₄) K hk
  have hM := pairMass_pos (m₃ := m₃) (m₄ := m₄) hk
  have hE := energy_sq' m k
  have hEp := energy_pos_of_ne_zero m hk
  have hs := sum_sq_nonneg K
  refine abs_lt_of_sq_lt_sq ?_ (by positivity)
  have h1 : (∑ i, K i ^ 2) * ∑ i, k i ^ 2 < time (totalOf m₃ m₄ K k) ^ 2 * ∑ i, k i ^ 2 := by
    have : ∑ i, K i ^ 2 < time (totalOf m₃ m₄ K k) ^ 2 := by nlinarith
    exact mul_lt_mul_of_pos_right this hρ
  have h2 : time (totalOf m₃ m₄ K k) ^ 2 * ∑ i, k i ^ 2 ≤
      time (totalOf m₃ m₄ K k) ^ 2 * energy m k ^ 2 := by
    have : ∑ i, k i ^ 2 ≤ energy m k ^ 2 := by nlinarith [sq_nonneg m]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  nlinarith

/-- The energy of the first particle in the frame of the co-ordinates:
`(P⁰E₃ + ⟨K, k⟩)/M`. -/
theorem energy_labFirst (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    energy m₃ (labFirst m₃ m₄ K k) =
      (time (totalOf m₃ m₄ K k) * energy m₃ k + ∑ i, K i * k i) / pairMass m₃ m₄ k := by
  have hM := pairMass_pos (m₃ := m₃) (m₄ := m₄) hk
  have hpos := abs_dot_lt (m₃ := m₃) (m₄ := m₄) K hk m₃
  have h := energy_labSpace (P := totalOf m₃ m₄ K k) (m := m₃) (E := energy m₃ k) (k := k)
    (by rw [invariantMass_totalOf]; exact hM) (time_totalOf_pos K hk)
    (by rw [invariantMass_totalOf, time_totalOf_sq]; rfl) (energy_sq' m₃ k)
    (by rw [spaceMomentum_totalOf]; linarith [neg_abs_le (∑ i, K i * k i)])
  rw [invariantMass_totalOf, spaceMomentum_totalOf] at h
  exact h

/-- The energy of the second particle in the frame of the co-ordinates:
`(P⁰E₄ − ⟨K, k⟩)/M`. -/
theorem energy_sub_labFirst (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    energy m₄ (K - labFirst m₃ m₄ K k) =
      (time (totalOf m₃ m₄ K k) * energy m₄ k - ∑ i, K i * k i) / pairMass m₃ m₄ k := by
  have hM := pairMass_pos (m₃ := m₃) (m₄ := m₄) hk
  have hpos := abs_dot_lt (m₃ := m₃) (m₄ := m₄) K hk m₄
  have hneg : ∑ i, K i * (-k) i = -∑ i, K i * k i := by
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  have h := energy_labSpace (P := totalOf m₃ m₄ K k) (m := m₄) (E := energy m₄ k) (k := -k)
    (by rw [invariantMass_totalOf]; exact hM) (time_totalOf_pos K hk)
    (by rw [invariantMass_totalOf, time_totalOf_sq]; rfl)
    (by rw [sum_neg_sq]; exact energy_sq' m₄ k)
    (by rw [spaceMomentum_totalOf, hneg]; linarith [le_abs_self (∑ i, K i * k i)])
  rw [invariantMass_totalOf, spaceMomentum_totalOf, hneg, ← sub_eq_add_neg] at h
  rw [sub_labFirst K hM]
  exact h

/-- **The Jacobian** of `k ↦ labFirst K k`:
`(P⁰E₃ + ⟨K, k⟩)(P⁰E₄ − ⟨K, k⟩)/(M P⁰ E₃ E₄)`. -/
theorem det_labDeriv (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    (labDeriv m₃ m₄ K k).det =
      (time (totalOf m₃ m₄ K k) * energy m₃ k + ∑ i, K i * k i) *
        (time (totalOf m₃ m₄ K k) * energy m₄ k - ∑ i, K i * k i) /
      (pairMass m₃ m₄ k * time (totalOf m₃ m₄ K k) * energy m₃ k * energy m₄ k) := by
  have he₃ := energy_pos_of_ne_zero m₃ hk
  have he₄ := energy_pos_of_ne_zero m₄ hk
  have hT2 := time_totalOf_sq (m₃ := m₃) (m₄ := m₄) K k
  have hTp := time_totalOf_pos (m₃ := m₃) (m₄ := m₄) K hk
  rw [labDeriv, det_id_add_smulRight]
  have hsum : ∑ i, labGrad m₃ m₄ K k i * K i = dotCovector (labGrad m₃ m₄ K k) K :=
    (dotCovector_apply _ _).symm
  rw [hsum, labGrad, dotCovector_smul_add_smul]
  have hKK : ∑ i, K i * K i = ∑ i, K i ^ 2 := Finset.sum_congr rfl fun i _ => (sq (K i)).symm
  have hkK : ∑ i, k i * K i = ∑ i, K i * k i := Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hKK, hkK]
  change 1 + ((pairMass m₃ m₄ k * (pairMass m₃ m₄ k + time (totalOf m₃ m₄ K k)))⁻¹ * _ +
    (energy m₄ k - energy m₃ k - _ / time (totalOf m₃ m₄ K k)) /
      (pairMass m₃ m₄ k * energy m₃ k * energy m₄ k) * _) = _
  generalize time (totalOf m₃ m₄ K k) = T at *
  generalize ∑ i, K i * k i = A at *
  generalize ∑ i, K i ^ 2 = s at *
  have hs : s = T ^ 2 - pairMass m₃ m₄ k ^ 2 := by linarith
  subst hs
  rw [pairMass] at *
  field_simp
  ring

/-- The Jacobian and the densities `1/E` of the two shells give the weight `M/(P⁰E₃E₄)`. -/
theorem jacobian_mul_density (K : Fin d → ℝ) {k : Fin d → ℝ} (hk : k ≠ 0) :
    ENNReal.ofReal |(labDeriv m₃ m₄ K k).det| *
        (ENNReal.ofReal (energy m₃ (labFirst m₃ m₄ K k))⁻¹ *
          ENNReal.ofReal (energy m₄ (K - labFirst m₃ m₄ K k))⁻¹) =
      ENNReal.ofReal (pairMass m₃ m₄ k /
        (time (totalOf m₃ m₄ K k) * energy m₃ k * energy m₄ k)) := by
  have he₃ := energy_pos_of_ne_zero m₃ hk
  have he₄ := energy_pos_of_ne_zero m₄ hk
  have hM := pairMass_pos (m₃ := m₃) (m₄ := m₄) hk
  have hTp := time_totalOf_pos (m₃ := m₃) (m₄ := m₄) K hk
  have h₃ := abs_dot_lt (m₃ := m₃) (m₄ := m₄) K hk m₃
  have h₄ := abs_dot_lt (m₃ := m₃) (m₄ := m₄) K hk m₄
  have hX : 0 < time (totalOf m₃ m₄ K k) * energy m₃ k + ∑ i, K i * k i := by
    linarith [neg_abs_le (∑ i, K i * k i)]
  have hY : 0 < time (totalOf m₃ m₄ K k) * energy m₄ k - ∑ i, K i * k i := by
    linarith [le_abs_self (∑ i, K i * k i)]
  rw [det_labDeriv K hk, energy_labFirst K hk, energy_sub_labFirst K hk,
    abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-! ### Injectivity and image -/

/-- The change of variables `k ↦ labFirst K k` is injective on `k ≠ 0`. -/
theorem injOn_labFirst (K : Fin d → ℝ) : InjOn (labFirst m₃ m₄ K) {k | k ≠ 0} := by
  intro k hk k' hk' h
  have h1 := total_labFirst (m₃ := m₃) (m₄ := m₄) K hk
  have h2 := total_labFirst (m₃ := m₃) (m₄ := m₄) K hk'
  rw [h] at h1
  have hP : totalOf m₃ m₄ K k = totalOf m₃ m₄ K k' := h1.symm.trans h2
  rw [labFirst_eq_action K (pairMass_pos hk), labFirst_eq_action K (pairMass_pos hk'), hP] at h
  have h3 := congrArg (action m₃ (labBoost (totalOf m₃ m₄ K k'))⁻¹) h
  rwa [action_inv_action _ (mem_domain_of_ne_zero m₃ hk),
    action_inv_action _ (mem_domain_of_ne_zero m₃ hk')] at h3

/-- The space momenta `π₃` of the regular pairs with the total space momentum `K`. -/
def regSlice (d : ℕ) (m₃ m₄ : ℝ) (K : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {π | (π, K - π) ∈ regular d m₃ m₄}

theorem measurableSet_regSlice (K : Fin d → ℝ) : MeasurableSet (regSlice d m₃ m₄ K) :=
  measurableSet_regular.preimage (measurable_id.prodMk (measurable_const.sub measurable_id))

theorem spaceMomentum_total (x : (Fin d → ℝ) × (Fin d → ℝ)) :
    spaceMomentum (total m₃ m₄ x) = x.1 + x.2 := by
  funext i
  simp [spaceMomentum, total, point]

theorem pairMass_zero (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) : pairMass m₃ m₄ (0 : Fin d → ℝ) = m₃ + m₄ := by
  simp [pairMass, energy, Real.sqrt_sq hm₃, Real.sqrt_sq hm₄]

/-- The image of `k ≠ 0` under `labFirst K` is the slice of the regular pairs. -/
theorem image_labFirst (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (K : Fin d → ℝ) :
    labFirst m₃ m₄ K '' {k | k ≠ 0} = regSlice d m₃ m₄ K := by
  ext π
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨labFirst_mem_domain K hk, sub_labFirst_mem_domain K hk, ?_⟩
    rw [total_labFirst K hk]
    exact totalOf_mem_region hm₃ hm₄ K hk
  · intro hπ
    set P := total m₃ m₄ (π, K - π) with hPdef
    have hPr : P ∈ region d m₃ m₄ := hπ.2.2
    have hft := futureTimelike_of_mem_region hPr
    have hx : (π, K - π) ∈ fibre m₃ m₄ P := ⟨hπ.1, hπ.2.1, rfl⟩
    obtain ⟨-, hM⟩ := rest_of_mem_fibre hft hx
    have hK : spaceMomentum P = K := by
      rw [hPdef, spaceMomentum_total]
      exact add_sub_cancel π K
    have htot : totalOf m₃ m₄ K (action m₃ (labBoost P)⁻¹ π) = P := by
      rw [totalOf, hM, ← hK, ← time_sq_of_mem_region hPr, Real.sqrt_sq hPr.1.le]
      exact cons_time_spaceMomentum _
    have hk0 : action m₃ (labBoost P)⁻¹ π ≠ 0 := by
      intro h0
      have hlt := add_lt_invariantMass hm₃ hm₄ hPr
      rw [← hM, h0, pairMass_zero hm₃ hm₄] at hlt
      exact lt_irrefl _ hlt
    refine ⟨_, hk0, ?_⟩
    rw [labFirst_eq_action K (pairMass_pos hk0), htot]
    exact action_action_inv _ hπ.1

/-! ### The change of variables at a fixed total space momentum -/

/-- The product `1/(E₃E₄)` of the densities of the two shells. -/
def pairDensity (m₃ m₄ : ℝ) (x : (Fin d → ℝ) × (Fin d → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (energy m₃ x.1)⁻¹ * ENNReal.ofReal (energy m₄ x.2)⁻¹

/-- The weight `M/(P⁰E₃E₄)` of the rest momentum `k` at the total space momentum `K`. -/
def restWeight (m₃ m₄ : ℝ) (K k : Fin d → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (pairMass m₃ m₄ k / (time (totalOf m₃ m₄ K k) * energy m₃ k * energy m₄ k))

theorem measurable_pairDensity : Measurable (pairDensity (d := d) m₃ m₄) :=
  (measurable_density.comp measurable_fst).mul (measurable_density.comp measurable_snd)

theorem continuous_time_totalOf (K : Fin d → ℝ) :
    Continuous fun k : Fin d → ℝ => time (totalOf m₃ m₄ K k) :=
  Real.continuous_sqrt.comp ((continuous_pairMass.pow 2).add continuous_const)

theorem measurable_restWeight (K : Fin d → ℝ) : Measurable (restWeight (d := d) m₃ m₄ K) :=
  ENNReal.measurable_ofReal.comp (continuous_pairMass.measurable.div
    (((continuous_time_totalOf K).mul continuous_energy).mul continuous_energy).measurable)

/-- **The change of variables `π₃ = labFirst K k`** at a fixed total space momentum `K`:
`∫ 1_reg f(π₃, K − π₃) dπ₃/(E₃E₄) = ∫ f(π₃(k), K − π₃(k)) M/(P⁰E₃E₄) d³k`. -/
theorem lintegral_slice (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (K : Fin 3 → ℝ)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} :
    ∫⁻ π, (regular 3 m₃ m₄).indicator (fun x => f x * pairDensity m₃ m₄ x) (π, K - π) =
      ∫⁻ k, restWeight m₃ m₄ K k * f (labFirst m₃ m₄ K k, K - labFirst m₃ m₄ K k) := by
  have h1 : (fun π => (regular 3 m₃ m₄).indicator (fun x => f x * pairDensity m₃ m₄ x)
      (π, K - π)) = (regSlice 3 m₃ m₄ K).indicator
        (fun π => f (π, K - π) * pairDensity m₃ m₄ (π, K - π)) := by
    funext π
    by_cases h : π ∈ regSlice 3 m₃ m₄ K
    · rw [indicator_of_mem h, indicator_of_mem (show (π, K - π) ∈ regular 3 m₃ m₄ from h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (show (π, K - π) ∉ regular 3 m₃ m₄ from h)]
  have hU : MeasurableSet {k : Fin 3 → ℝ | k ≠ 0} := (measurableSet_singleton 0).compl
  rw [h1, lintegral_indicator (measurableSet_regSlice K), ← image_labFirst hm₃ hm₄ K,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU
      (fun k hk => (hasFDerivAt_labFirst K hk).hasFDerivWithinAt) (injOn_labFirst K)]
  have h2 : ∫⁻ k, restWeight m₃ m₄ K k * f (labFirst m₃ m₄ K k, K - labFirst m₃ m₄ K k) =
      ∫⁻ k in {k : Fin 3 → ℝ | k ≠ 0},
        restWeight m₃ m₄ K k * f (labFirst m₃ m₄ K k, K - labFirst m₃ m₄ K k) := by
    rw [show {k : Fin 3 → ℝ | k ≠ 0} = {0}ᶜ from rfl, restrict_compl_singleton]
  rw [h2]
  refine setLIntegral_congr_fun hU fun k hk => ?_
  have h3 := jacobian_mul_density (m₃ := m₃) (m₄ := m₄) K hk
  simp only [pairDensity]
  rw [restWeight, ← h3]
  ring

/-! ### The radial substitution -/

/-- The rest mass `√(m₃² + r²) + √(m₄² + r²)` of the pair with the rest momenta of length `r`. -/
def radialMass (m₃ m₄ r : ℝ) : ℝ := Real.sqrt (m₃ ^ 2 + r ^ 2) + Real.sqrt (m₄ ^ 2 + r ^ 2)

/-- The total energy `√(M(r)² + s)` at the total space momentum with `|K|² = s`. -/
def radialEnergy (m₃ m₄ s r : ℝ) : ℝ := Real.sqrt (radialMass m₃ m₄ r ^ 2 + s)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem energy_smul_sphereVec (m r : ℝ) (n : sphere (0 : E3) 1) :
    energy m (r • sphereVec n) = Real.sqrt (m ^ 2 + r ^ 2) := by
  rw [energy, sum_smul_sq, sum_sphereVec_sq, mul_one]

theorem pairMass_smul_sphereVec (r : ℝ) (n : sphere (0 : E3) 1) :
    pairMass m₃ m₄ (r • sphereVec n) = radialMass m₃ m₄ r := by
  rw [pairMass, energy_smul_sphereVec, energy_smul_sphereVec, radialMass]

theorem totalOf_smul_sphereVec (K : Fin 3 → ℝ) (r : ℝ) (n : sphere (0 : E3) 1) :
    totalOf m₃ m₄ K (r • sphereVec n) =
      (Fin.cons (radialEnergy m₃ m₄ (∑ i, K i ^ 2) r) K : MinkowskiModel 3) := by
  rw [totalOf, pairMass_smul_sphereVec, radialEnergy]

theorem hasDerivAt_sqrt_sq_add (m : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r : ℝ => Real.sqrt (m ^ 2 + r ^ 2)) (r / Real.sqrt (m ^ 2 + r ^ 2)) r := by
  have hpos : 0 < m ^ 2 + r ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => m ^ 2 + r ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).const_add (m ^ 2)
  refine (h1.sqrt hpos.ne').congr_deriv ?_
  have hs := Real.sqrt_pos.mpr hpos
  field_simp

/-- The derivative of the rest mass `M(r) = √(m₃² + r²) + √(m₄² + r²)` in the length `r` of the
rest momentum: `r M/(E₃E₄)`. -/
theorem hasDerivAt_radialMass {r : ℝ} (hr : 0 < r) :
    HasDerivAt (radialMass m₃ m₄)
      (r * radialMass m₃ m₄ r / (Real.sqrt (m₃ ^ 2 + r ^ 2) * Real.sqrt (m₄ ^ 2 + r ^ 2))) r := by
  have he₃ : 0 < Real.sqrt (m₃ ^ 2 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have he₄ : 0 < Real.sqrt (m₄ ^ 2 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h : HasDerivAt (radialMass m₃ m₄)
      (r / Real.sqrt (m₃ ^ 2 + r ^ 2) + r / Real.sqrt (m₄ ^ 2 + r ^ 2)) r :=
    (hasDerivAt_sqrt_sq_add m₃ hr).add (hasDerivAt_sqrt_sq_add m₄ hr)
  refine h.congr_deriv ?_
  rw [radialMass]
  field_simp
  ring

/-- The derivative of the total energy in the rest momentum: `r M²/(P⁰E₃E₄)`. -/
theorem hasDerivAt_radialEnergy {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) :
    HasDerivAt (radialEnergy m₃ m₄ s)
      (r * radialMass m₃ m₄ r ^ 2 / (radialEnergy m₃ m₄ s r * Real.sqrt (m₃ ^ 2 + r ^ 2) *
        Real.sqrt (m₄ ^ 2 + r ^ 2))) r := by
  have he₃ : 0 < Real.sqrt (m₃ ^ 2 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have he₄ : 0 < Real.sqrt (m₄ ^ 2 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hM : 0 < radialMass m₃ m₄ r := add_pos he₃ he₄
  have hS : 0 < radialMass m₃ m₄ r ^ 2 + s := by positivity
  have hT : 0 < radialEnergy m₃ m₄ s r := Real.sqrt_pos.mpr hS
  have hMd : HasDerivAt (fun r => radialMass m₃ m₄ r)
      (r / Real.sqrt (m₃ ^ 2 + r ^ 2) + r / Real.sqrt (m₄ ^ 2 + r ^ 2)) r :=
    (hasDerivAt_sqrt_sq_add m₃ hr).add (hasDerivAt_sqrt_sq_add m₄ hr)
  have h3 : HasDerivAt (radialEnergy m₃ m₄ s) _ r := ((hMd.pow 2).add_const s).sqrt hS.ne'
  refine h3.congr_deriv ?_
  have hTdef : Real.sqrt (((fun r => radialMass m₃ m₄ r) ^ 2) r + s) =
      radialEnergy m₃ m₄ s r := rfl
  rw [hTdef]
  norm_num
  rw [radialMass] at *
  field_simp
  ring

theorem sqrt_sq_add_lt {m a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Real.sqrt (m ^ 2 + a ^ 2) < Real.sqrt (m ^ 2 + b ^ 2) :=
  Real.sqrt_lt_sqrt (by positivity) (by nlinarith)

theorem strictMonoOn_radialEnergy {s : ℝ} (hs : 0 ≤ s) :
    StrictMonoOn (radialEnergy m₃ m₄ s) (Ioi 0) := by
  intro a ha b hb hab
  have hM : radialMass m₃ m₄ a < radialMass m₃ m₄ b :=
    add_lt_add (sqrt_sq_add_lt (le_of_lt ha) hab) (sqrt_sq_add_lt (le_of_lt ha) hab)
  have h0 : 0 ≤ radialMass m₃ m₄ a := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : radialMass m₃ m₄ a ^ 2 < radialMass m₃ m₄ b ^ 2 := pow_lt_pow_left₀ hM h0 two_ne_zero
  exact Real.sqrt_lt_sqrt (by positivity) (by linarith)

/-- The total energies of the pairs with rest momenta `r > 0` are the energies above
`√((m₃ + m₄)² + s)`. -/
theorem image_radialEnergy (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) {s : ℝ} (hs : 0 ≤ s) :
    radialEnergy m₃ m₄ s '' Ioi 0 = Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + s)) := by
  ext t
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hlt := add_lt_sqrt_add_sqrt hm₃ hm₄ (show 0 < r from hr)
    have h0 : 0 ≤ m₃ + m₄ := add_nonneg hm₃ hm₄
    exact Real.sqrt_lt_sqrt (by positivity) (by
      have : (m₃ + m₄) ^ 2 < radialMass m₃ m₄ r ^ 2 := pow_lt_pow_left₀ hlt h0 two_ne_zero
      linarith)
  · intro ht
    have ht' : Real.sqrt ((m₃ + m₄) ^ 2 + s) < t := ht
    have h0 : 0 ≤ Real.sqrt ((m₃ + m₄) ^ 2 + s) := Real.sqrt_nonneg _
    have htpos : 0 < t := lt_of_le_of_lt h0 ht'
    have ht2 : (m₃ + m₄) ^ 2 + s < t ^ 2 := by
      have := (Real.sqrt_lt' htpos).mp ht'
      linarith
    have hM : m₃ + m₄ < Real.sqrt (t ^ 2 - s) :=
      (Real.lt_sqrt (add_nonneg hm₃ hm₄)).mpr (by linarith)
    refine ⟨restMomentum m₃ m₄ (Real.sqrt (t ^ 2 - s)), restMomentum_pos hm₃ hm₄ hM, ?_⟩
    rw [radialEnergy, radialMass, sqrt_add_sqrt_restMomentum hm₃ hm₄ hM,
      Real.sq_sqrt (by nlinarith [sq_nonneg (m₃ + m₄)]), sub_add_cancel, Real.sqrt_sq htpos.le]

/-- **The radial substitution** `P⁰ = √(M(r)² + |K|²)` in the integral over the length `r` of
the rest momentum: `r² M/(P⁰E₃E₄) dr = (q/M) dP⁰`. -/
theorem lintegral_radial (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (K : Fin 3 → ℝ) (n : sphere (0 : E3) 1)
    (f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * (restWeight m₃ m₄ K (r • sphereVec n) *
        f (labFirst m₃ m₄ K (r • sphereVec n), K - labFirst m₃ m₄ K (r • sphereVec n))) =
      ∫⁻ t in Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + ∑ i, K i ^ 2)),
        ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass (Fin.cons t K : MinkowskiModel 3)) /
          invariantMass (Fin.cons t K : MinkowskiModel 3)) *
          f (fibrePair m₃ m₄ (Fin.cons t K) n) := by
  have hs := sum_sq_nonneg K
  rw [← image_radialEnergy hm₃ hm₄ hs, lintegral_image_eq_lintegral_abs_deriv_mul
    measurableSet_Ioi (fun r hr => (hasDerivAt_radialEnergy (m₃ := m₃) (m₄ := m₄) hs
      hr).hasDerivWithinAt) (strictMonoOn_radialEnergy hs).injOn]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : 0 < r := hr
  have he₃ : 0 < Real.sqrt (m₃ ^ 2 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have he₄ : 0 < Real.sqrt (m₄ ^ 2 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hM : 0 < radialMass m₃ m₄ r := add_pos he₃ he₄
  have hT : 0 < radialEnergy m₃ m₄ (∑ i, K i ^ 2) r := Real.sqrt_pos.mpr (by positivity)
  have hq : restMomentum m₃ m₄ (radialMass m₃ m₄ r) = r :=
    restMomentum_sqrt_add_sqrt hr'.le
  rw [← totalOf_smul_sphereVec K r n, invariantMass_totalOf, pairMass_smul_sphereVec, hq]
  have hfp : fibrePair m₃ m₄ (totalOf m₃ m₄ K (r • sphereVec n)) n =
      (labFirst m₃ m₄ K (r • sphereVec n), K - labFirst m₃ m₄ K (r • sphereVec n)) := by
    rw [fibrePair, spaceMomentum_totalOf, invariantMass_totalOf, pairMass_smul_sphereVec, hq]
  rw [hfp, restWeight, pairMass_smul_sphereVec, totalOf_smul_sphereVec, energy_smul_sphereVec,
    energy_smul_sphereVec, ← mul_assoc, ← mul_assoc]
  congr 1
  change ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (radialMass m₃ m₄ r /
    (radialEnergy m₃ m₄ (∑ i, K i ^ 2) r * Real.sqrt (m₃ ^ 2 + r ^ 2) *
      Real.sqrt (m₄ ^ 2 + r ^ 2))) = _
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (abs_nonneg _),
    abs_of_pos (by positivity)]
  congr 1
  field_simp

/-! ### The integration formula -/

theorem measurable_cons :
    Measurable fun z : ℝ × (Fin d → ℝ) => (Fin.cons z.1 z.2 : MinkowskiModel d) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using measurable_fst
  · change Measurable fun z : ℝ × (Fin d → ℝ) => z.2 j
    exact (measurable_pi_apply j).comp measurable_snd

/-- The Lebesgue measure of the momenta in the time and the space co-ordinates:
`∫ F d⁴P = ∫ (∫ F(t, K) dt) d³K`. -/
theorem lintegral_minkowski {F : MinkowskiModel d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ P, F P = ∫⁻ K : Fin d → ℝ, ∫⁻ t : ℝ, F (Fin.cons t K) := by
  have hmp :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (d + 1) => (volume : Measure ℝ)) 0).symm
  have h1 := hmp.lintegral_comp hF
  have hpt : ∀ a : ℝ × (Fin d → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm a =
        (Fin.cons a.1 a.2 : MinkowskiModel d) := fun a => by
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  simp only [hpt] at h1
  have hc : Measurable fun z : ℝ × (Fin d → ℝ) => F (Fin.cons z.1 z.2) := hF.comp measurable_cons
  rw [volume_pi, ← h1, lintegral_prod _ hc.aemeasurable]
  exact lintegral_lintegral_swap hc.aemeasurable

/-- The total momentum `(t, K)` is regular if and only if `t > √((m₃ + m₄)² + |K|²)`. -/
theorem cons_mem_region_iff (t : ℝ) (K : Fin 3 → ℝ) :
    (Fin.cons t K : MinkowskiModel 3) ∈ region 3 m₃ m₄ ↔
      t ∈ Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + ∑ i, K i ^ 2)) := by
  change 0 < t ∧ (m₃ + m₄) ^ 2 < intervalQuadratic (Fin.cons t K : MinkowskiModel 3) ↔
    Real.sqrt ((m₃ + m₄) ^ 2 + ∑ i, K i ^ 2) < t
  rw [intervalQuadratic_cons]
  constructor
  · rintro ⟨ht, hQ⟩
    exact (Real.sqrt_lt' ht).mpr (by linarith)
  · intro ht
    have htpos : 0 < t := lt_of_le_of_lt (Real.sqrt_nonneg _) ht
    have h := (Real.sqrt_lt' htpos).mp ht
    exact ⟨htpos, by linarith⟩

theorem measurable_labFirst_right (K : Fin d → ℝ) : Measurable (labFirst m₃ m₄ K) := by
  have h : Measurable fun k : Fin d → ℝ => labFirst m₃ m₄ (K, k).1 (K, k).2 :=
    (measurable_labFirst (m₃ := m₃) (m₄ := m₄)).comp measurable_prodMk_left
  exact h

theorem measurable_fibreWeight :
    Measurable fun P : MinkowskiModel 3 =>
      ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P) :=
  ENNReal.measurable_ofReal.comp ((measurable_restMomentum.comp
    continuous_invariantMass.measurable).div continuous_invariantMass.measurable)

/-- The integrand on the right side of the integration formula, in the co-ordinates `(t, K)` of
the total momentum and the direction `n` in its rest frame. -/
def fibreIntegrand (m₃ m₄ : ℝ) (f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞) (K : Fin 3 → ℝ)
    (n : sphere (0 : E3) 1) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass (Fin.cons t K : MinkowskiModel 3)) /
    invariantMass (Fin.cons t K : MinkowskiModel 3)) * f (fibrePair m₃ m₄ (Fin.cons t K) n)

theorem measurable_fibreIntegrand {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f)
    (K : Fin 3 → ℝ) :
    Measurable fun z : ℝ × sphere (0 : E3) 1 => fibreIntegrand m₃ m₄ f K z.2 z.1 := by
  have hconsK : Measurable fun t : ℝ => (Fin.cons t K : MinkowskiModel 3) :=
    measurable_cons.comp (measurable_id.prodMk measurable_const)
  have hc1 : Measurable fun z : ℝ × sphere (0 : E3) 1 => (Fin.cons z.1 K : MinkowskiModel 3) :=
    hconsK.comp measurable_fst
  have hw1 := (measurable_fibreWeight (m₃ := m₃) (m₄ := m₄)).comp hc1
  have hp1 : Measurable fun z : ℝ × sphere (0 : E3) 1 =>
      ((Fin.cons z.1 K : MinkowskiModel 3), z.2) := hc1.prodMk measurable_snd
  have hf1 := (hf.comp (measurable_fibrePair (m₃ := m₃) (m₄ := m₄))).comp hp1
  exact hw1.mul hf1

/-- The product of the shell measures has the density `1/(E₃E₄)`. -/
theorem setLIntegral_prod_measure (f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in regular 3 m₃ m₄, f x ∂((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)) =
      ∫⁻ x, (regular 3 m₃ m₄).indicator (fun x => f x * pairDensity m₃ m₄ x) x := by
  have hd₃ := (measurable_density (d := 3) (m := m₃)).indicator (measurableSet_domain (m := m₃))
  have hd₄ := (measurable_density (d := 3) (m := m₄)).indicator (measurableSet_domain (m := m₄))
  have hρ : Measurable fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (domain 3 m₃).indicator (fun π => ENNReal.ofReal (energy m₃ π)⁻¹) z.1 *
        (domain 3 m₄).indicator (fun π => ENNReal.ofReal (energy m₄ π)⁻¹) z.2 :=
    (hd₃.comp measurable_fst).mul (hd₄.comp measurable_snd)
  rw [FutureShell.measure, FutureShell.measure, ← withDensity_indicator measurableSet_domain,
    ← withDensity_indicator measurableSet_domain, prod_withDensity hd₃ hd₄,
    setLIntegral_withDensity_eq_setLIntegral_mul _ hρ hf measurableSet_regular,
    ← lintegral_indicator measurableSet_regular]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ regular 3 m₃ m₄
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    simp only [Pi.mul_apply, pairDensity, indicator_of_mem hx.1, indicator_of_mem hx.2.1]
    ring
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

/-- The total space momentum `K = π₃ + π₄` replaces `π₄`. -/
theorem lintegral_prod_sub {G : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x = ∫⁻ K, ∫⁻ π, G (π, K - π) := by
  have hmp := measurePreserving_prod_sub (volume : Measure (Fin 3 → ℝ))
    (volume : Measure (Fin 3 → ℝ))
  have hc : Measurable fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) => G (z.1, z.2 - z.1) :=
    hG.comp hmp.measurable
  rw [show (∫⁻ x, G x) = ∫⁻ x, G x ∂((volume : Measure (Fin 3 → ℝ)).prod volume) from rfl,
    ← hmp.lintegral_comp hG, lintegral_prod _ hc.aemeasurable]
  exact lintegral_lintegral_swap hc.aemeasurable

/-- At a fixed total space momentum `K`: the rest momentum, polar co-ordinates and the radial
substitution. -/
theorem lintegral_slice_eq (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (K : Fin 3 → ℝ)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ π, (regular 3 m₃ m₄).indicator (fun x => f x * pairDensity m₃ m₄ x) (π, K - π) =
      ∫⁻ n, (∫⁻ t in Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + ∑ i, K i ^ 2)),
        fibreIntegrand m₃ m₄ f K n t) ∂Sphere.sphereMeasure := by
  rw [lintegral_slice hm₃ hm₄ K]
  have hl := measurable_labFirst_right (m₃ := m₃) (m₄ := m₄) K
  have hw : Measurable fun k =>
      restWeight m₃ m₄ K k * f (labFirst m₃ m₄ K k, K - labFirst m₃ m₄ K k) :=
    (measurable_restWeight K).mul (hf.comp (hl.prodMk (measurable_const.sub hl)))
  rw [Sphere.lintegral_pi_eq_lintegral_sphere_Ioi hw]
  refine lintegral_congr fun n => ?_
  exact lintegral_radial hm₃ hm₄ K n f

/-- At a fixed space momentum `K`, the integral over the regular total momenta `(t, K)`. -/
theorem lintegral_region_slice {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f)
    (K : Fin 3 → ℝ) :
    ∫⁻ t, (region 3 m₃ m₄).indicator (fun P : MinkowskiModel 3 =>
        ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P) *
          ∫⁻ n, f (fibrePair m₃ m₄ P n) ∂Sphere.sphereMeasure) (Fin.cons t K) =
      ∫⁻ n, (∫⁻ t in Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + ∑ i, K i ^ 2)),
        fibreIntegrand m₃ m₄ f K n t) ∂Sphere.sphereMeasure := by
  have h1 : ∀ t : ℝ, (region 3 m₃ m₄).indicator (fun P : MinkowskiModel 3 =>
      ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P) *
        ∫⁻ n, f (fibrePair m₃ m₄ P n) ∂Sphere.sphereMeasure) (Fin.cons t K) =
      (Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + ∑ i, K i ^ 2))).indicator
        (fun t : ℝ => ∫⁻ n, fibreIntegrand m₃ m₄ f K n t ∂Sphere.sphereMeasure) t := by
    intro t
    have h2 : ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass
        (Fin.cons t K : MinkowskiModel 3)) / invariantMass (Fin.cons t K : MinkowskiModel 3)) *
          ∫⁻ n, f (fibrePair m₃ m₄ (Fin.cons t K) n) ∂Sphere.sphereMeasure =
        ∫⁻ n, fibreIntegrand m₃ m₄ f K n t ∂Sphere.sphereMeasure :=
      (lintegral_const_mul _ (hf.comp (measurable_fibrePair_right _))).symm
    by_cases ht : (Fin.cons t K : MinkowskiModel 3) ∈ region 3 m₃ m₄
    · rw [indicator_of_mem ht, indicator_of_mem ((cons_mem_region_iff t K).mp ht)]
      exact h2
    · rw [indicator_of_notMem ht,
        indicator_of_notMem (fun h => ht ((cons_mem_region_iff t K).mpr h))]
  rw [lintegral_congr h1, lintegral_indicator measurableSet_Ioi]
  exact lintegral_lintegral_swap (measurable_fibreIntegrand hf K).aemeasurable

/-- The right side of the integration formula in the co-ordinates `(t, K, n)`. -/
theorem setLIntegral_region_eq {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ P in region 3 m₃ m₄, ∫⁻ x, f x ∂(fibreMeasure m₃ m₄ P) =
      ∫⁻ K : Fin 3 → ℝ, ∫⁻ n, (∫⁻ t in Ioi (Real.sqrt ((m₃ + m₄) ^ 2 + ∑ i, K i ^ 2)),
        fibreIntegrand m₃ m₄ f K n t) ∂Sphere.sphereMeasure := by
  have hint : Measurable fun P : MinkowskiModel 3 =>
      ∫⁻ n, f (fibrePair m₃ m₄ P n) ∂Sphere.sphereMeasure :=
    (hf.comp measurable_fibrePair).lintegral_prod_right'
  have hH : Measurable fun P : MinkowskiModel 3 =>
      ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P) *
        ∫⁻ n, f (fibrePair m₃ m₄ P n) ∂Sphere.sphereMeasure :=
    (measurable_fibreWeight (m₃ := m₃) (m₄ := m₄)).mul hint
  rw [setLIntegral_congr_fun measurableSet_region (fun P _ => lintegral_fibreMeasure P hf),
    ← lintegral_indicator measurableSet_region,
    lintegral_minkowski (hH.indicator measurableSet_region)]
  exact lintegral_congr fun K => lintegral_region_slice hf K

/-- **The integration formula of two outgoing particles.** For a measurable `f ≥ 0` on the pairs
of space momenta, the integral over the regular pairs against the product of the two shell
measures `d³π₃/E₃ d³π₄/E₄` is the integral over the regular total momenta `P`, against the
Lebesgue measure `d⁴P`, of the integral of `f` against the measure `fibreMeasure m₃ m₄ P` of the
fibre over `P`. -/
theorem lintegral_regular_eq (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in regular 3 m₃ m₄, f x ∂((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)) =
      ∫⁻ P in region 3 m₃ m₄, ∫⁻ x, f x ∂(fibreMeasure m₃ m₄ P) := by
  have hG : Measurable ((regular 3 m₃ m₄).indicator fun x => f x * pairDensity m₃ m₄ x) :=
    (hf.mul measurable_pairDensity).indicator measurableSet_regular
  rw [setLIntegral_prod_measure f hf, lintegral_prod_sub hG, setLIntegral_region_eq hf]
  exact lintegral_congr fun K => lintegral_slice_eq hm₃ hm₄ K hf

/-- The integration formula for a function that vanishes outside the regular pairs. -/
theorem lintegral_eq_of_support (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f)
    (hsupp : ∀ x ∉ regular 3 m₃ m₄, f x = 0) :
    ∫⁻ x, f x ∂((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)) =
      ∫⁻ P in region 3 m₃ m₄, ∫⁻ x, f x ∂(fibreMeasure m₃ m₄ P) := by
  rw [← lintegral_regular_eq hm₃ hm₄ hf, ← lintegral_indicator measurableSet_regular]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ regular 3 m₃ m₄
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, hsupp x hx]

/-- The measures of the fibres form a measurable family. -/
theorem measurable_fibreMeasure : Measurable (fibreMeasure m₃ m₄) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have hS1 : Measurable (S.indicator (1 : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞)) :=
    measurable_one.indicator hS
  have h : ∀ P : MinkowskiModel 3, fibreMeasure m₃ m₄ P S =
      ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P) *
        ∫⁻ n, S.indicator 1 (fibrePair m₃ m₄ P n) ∂Sphere.sphereMeasure := fun P => by
    rw [← lintegral_indicator_one hS, lintegral_fibreMeasure P hS1]
  simp_rw [h]
  exact (measurable_fibreWeight (m₃ := m₃) (m₄ := m₄)).mul
    ((hS1.comp (measurable_fibrePair (m₃ := m₃) (m₄ := m₄))).lintegral_prod_right')

/-- **The disintegration**: the product of the shell measures, restricted to the regular pairs,
is the integral of the measures of the fibres over the Lebesgue measure of the regular total
momenta. -/
theorem restrict_regular_eq_bind (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) :
    ((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)).restrict (regular 3 m₃ m₄) =
      (volume.restrict (region 3 m₃ m₄)).bind (fibreMeasure m₃ m₄) := by
  ext S hS
  have hS1 : Measurable (S.indicator (1 : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞)) :=
    measurable_one.indicator hS
  rw [Measure.bind_apply hS measurable_fibreMeasure.aemeasurable, ← lintegral_indicator_one hS,
    lintegral_regular_eq hm₃ hm₄ hS1]
  exact setLIntegral_congr_fun measurableSet_region fun P _ => lintegral_indicator_one hS

/-! ### The pairs that are not regular -/

/-- A null vector orthogonal to a timelike vector is zero. -/
theorem eq_zero_of_pair_eq_zero {U W : MinkowskiModel d} (hU : 0 < intervalQuadratic U)
    (hW : pair U W = 0) (hQ : intervalQuadratic W = 0) : W = 0 := by
  by_contra h
  have := intervalQuadratic_neg_of_pair_eq_zero hU hW h
  linarith

theorem intervalQuadratic_smul_sub_smul (a b : ℝ) (p q : MinkowskiModel d) :
    intervalQuadratic (a • p - b • q) =
      a ^ 2 * intervalQuadratic p - 2 * a * b * pair p q + b ^ 2 * intervalQuadratic q := by
  simp only [intervalQuadratic_apply, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
  rw [Minkowski.pair_comm q p]
  ring

/-- **The pairs that are not regular.** If two momenta on the shells have a total momentum that
is not regular, the first space momentum is on the line of the total space momentum: the two
particles have the same velocity, or both are massless and their momenta are parallel. -/
theorem mem_span_of_notMem_regular (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    {x : (Fin d → ℝ) × (Fin d → ℝ)} (h₃ : x.1 ∈ domain d m₃) (h₄ : x.2 ∈ domain d m₄)
    (hx : x ∉ regular d m₃ m₄) : x.1 ∈ Submodule.span ℝ {x.1 + x.2} := by
  have hp₃ := point_mem h₃
  have hp₄ := point_mem h₄
  have hfc₃ := futureCausal_of_mem hp₃
  have hfc₄ := futureCausal_of_mem hp₄
  have htime : 0 < time (total m₃ m₄ x) := by
    rw [total, map_add]
    exact add_pos hp₃.2 hp₄.2
  have hQle : intervalQuadratic (total m₃ m₄ x) ≤ (m₃ + m₄) ^ 2 := by
    by_contra h
    exact hx ⟨h₃, h₄, htime, lt_of_not_ge h⟩
  have hcs := sqrt_mul_sqrt_le_pair hfc₃ hfc₄
  rw [hp₃.1, hp₄.1, Real.sqrt_sq hm₃, Real.sqrt_sq hm₄] at hcs
  have hadd := intervalQuadratic_add (point m₃ x.1) (point m₄ x.2)
  rw [hp₃.1, hp₄.1] at hadd
  have hpair : pair (point m₃ x.1) (point m₄ x.2) = m₃ * m₄ := by
    rw [total] at hQle
    nlinarith
  have hcoord : ∀ (a b : ℝ), a • point m₃ x.1 - b • point m₄ x.2 = 0 →
      ∀ i, a * x.1 i - b * x.2 i = 0 := by
    intro a b h i
    have := congrFun h i.succ
    simpa [point] using this
  rw [Submodule.mem_span_singleton]
  rcases eq_or_lt_of_le (add_nonneg hm₃ hm₄) with h0 | hpos
  · -- two massless particles: their momenta are parallel
    have hm₃0 : m₃ = 0 := by linarith
    have hm₄0 : m₄ = 0 := by linarith
    have hne : point m₃ x.1 ≠ 0 := fun h => zero_notMem_shell (h ▸ hp₃)
    obtain ⟨c, hc, hpc⟩ := exists_smul_of_pair_eq_zero hfc₃ hfc₄ hne
      (by rw [hp₃.1, hm₃0]; ring) (by rw [hp₄.1, hm₄0]; ring) (by rw [hpair, hm₃0, zero_mul])
    have hW : c • point m₃ x.1 - (1 : ℝ) • point m₄ x.2 = 0 := by rw [hpc, one_smul, sub_self]
    have hc' := hcoord c 1 hW
    refine ⟨(1 + c)⁻¹, ?_⟩
    have h1c : 1 + c ≠ 0 := by linarith
    funext i
    have := hc' i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    linarith
  · -- a massive particle: the two particles have the same velocity
    have hW : m₄ • point m₃ x.1 - m₃ • point m₄ x.2 = 0 := by
      have hQW : intervalQuadratic (m₄ • point m₃ x.1 - m₃ • point m₄ x.2) = 0 := by
        rw [intervalQuadratic_smul_sub_smul, hp₃.1, hp₄.1, hpair]
        ring
      rcases eq_or_lt_of_le hm₄ with h4 | h4
      · refine eq_zero_of_pair_eq_zero (U := point m₃ x.1) ?_ ?_ hQW
        · rw [hp₃.1]
          have : 0 < m₃ := by linarith
          positivity
        · have hq3 : pair (point m₃ x.1) (point m₃ x.1) = m₃ ^ 2 := hp₃.1
          simp only [map_sub, map_smul, smul_eq_mul]
          rw [hq3, hpair, ← h4]
          ring
      · refine eq_zero_of_pair_eq_zero (U := point m₄ x.2) ?_ ?_ hQW
        · rw [hp₄.1]
          positivity
        · have hq4 : pair (point m₄ x.2) (point m₄ x.2) = m₄ ^ 2 := hp₄.1
          simp only [map_sub, map_smul, smul_eq_mul]
          rw [Minkowski.pair_comm (point m₄ x.2) (point m₃ x.1), hpair, hq4]
          ring
    have hc' := hcoord m₄ m₃ hW
    refine ⟨m₃ / (m₃ + m₄), ?_⟩
    funext i
    have := hc' i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    linarith

theorem span_singleton_ne_top (K : Fin 3 → ℝ) : Submodule.span ℝ {K} ≠ ⊤ := by
  intro htop
  have h := finrank_span_le_card (R := ℝ) ({K} : Set (Fin 3 → ℝ))
  rw [htop, finrank_top, Module.finrank_fin_fun] at h
  simp at h

/-- The slice of the pairs that are not regular, at a fixed total space momentum, is a null
set. -/
theorem volume_irregular_slice (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (K : Fin 3 → ℝ) :
    volume {π : Fin 3 → ℝ | π ∈ domain 3 m₃ ∧ K - π ∈ domain 3 m₄ ∧
      (π, K - π) ∉ regular 3 m₃ m₄} = 0 := by
  refine measure_mono_null (fun π hπ => ?_)
    (Measure.addHaar_submodule volume _ (span_singleton_ne_top K))
  have h := mem_span_of_notMem_regular hm₃ hm₄ (x := (π, K - π)) hπ.1 hπ.2.1 hπ.2.2
  simpa using h

/-- **The pairs that are not regular form a null set** for the product of the shell
measures. -/
theorem prod_regular_compl (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) :
    ((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)) (regular 3 m₃ m₄)ᶜ = 0 := by
  have hd₃ := (measurable_density (d := 3) (m := m₃)).indicator (measurableSet_domain (m := m₃))
  have hd₄ := (measurable_density (d := 3) (m := m₄)).indicator (measurableSet_domain (m := m₄))
  have hρ : Measurable fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (domain 3 m₃).indicator (fun π => ENNReal.ofReal (energy m₃ π)⁻¹) z.1 *
        (domain 3 m₄).indicator (fun π => ENNReal.ofReal (energy m₄ π)⁻¹) z.2 :=
    (hd₃.comp measurable_fst).mul (hd₄.comp measurable_snd)
  rw [FutureShell.measure, FutureShell.measure, ← withDensity_indicator measurableSet_domain,
    ← withDensity_indicator measurableSet_domain, prod_withDensity hd₃ hd₄,
    withDensity_apply _ measurableSet_regular.compl,
    ← lintegral_indicator measurableSet_regular.compl]
  rw [show (∫⁻ x, (regular 3 m₃ m₄)ᶜ.indicator (fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (domain 3 m₃).indicator (fun π => ENNReal.ofReal (energy m₃ π)⁻¹) z.1 *
        (domain 3 m₄).indicator (fun π => ENNReal.ofReal (energy m₄ π)⁻¹) z.2) x
          ∂((volume : Measure (Fin 3 → ℝ)).prod volume)) =
      ∫⁻ x, (regular 3 m₃ m₄)ᶜ.indicator (fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (domain 3 m₃).indicator (fun π => ENNReal.ofReal (energy m₃ π)⁻¹) z.1 *
        (domain 3 m₄).indicator (fun π => ENNReal.ofReal (energy m₄ π)⁻¹) z.2) x from rfl,
    lintegral_prod_sub (hρ.indicator measurableSet_regular.compl)]
  refine (lintegral_congr fun K => ?_).trans lintegral_zero
  set I := {π : Fin 3 → ℝ | π ∈ domain 3 m₃ ∧ K - π ∈ domain 3 m₄ ∧
    (π, K - π) ∉ regular 3 m₃ m₄} with hI
  have hsub : Measurable fun π : Fin 3 → ℝ => K - π := measurable_const.sub measurable_id
  have hImeas : MeasurableSet I :=
    (measurableSet_domain (d := 3) (m := m₃)).inter
      (((measurableSet_domain (d := 3) (m := m₄)).preimage hsub).inter
        ((measurableSet_regular (d := 3) (m₃ := m₃) (m₄ := m₄)).compl.preimage
          (measurable_id.prodMk hsub)))
  have h1 : ∀ π : Fin 3 → ℝ, (regular 3 m₃ m₄)ᶜ.indicator (fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (domain 3 m₃).indicator (fun π => ENNReal.ofReal (energy m₃ π)⁻¹) z.1 *
        (domain 3 m₄).indicator (fun π => ENNReal.ofReal (energy m₄ π)⁻¹) z.2) (π, K - π) =
      I.indicator (fun π => ENNReal.ofReal (energy m₃ π)⁻¹ *
        ENNReal.ofReal (energy m₄ (K - π))⁻¹) π := by
    intro π
    by_cases hπ : π ∈ I
    · rw [indicator_of_mem (show (π, K - π) ∈ (regular 3 m₃ m₄)ᶜ from hπ.2.2), indicator_of_mem hπ]
      simp only [indicator_of_mem hπ.1, indicator_of_mem hπ.2.1]
    · rw [indicator_of_notMem hπ]
      by_cases hr : (π, K - π) ∈ regular 3 m₃ m₄
      · rw [indicator_of_notMem (show (π, K - π) ∉ (regular 3 m₃ m₄)ᶜ from fun h => h hr)]
      · rw [indicator_of_mem (show (π, K - π) ∈ (regular 3 m₃ m₄)ᶜ from hr)]
        by_cases h3 : π ∈ domain 3 m₃
        · have h4 : K - π ∉ domain 3 m₄ := fun h4 => hπ ⟨h3, h4, hr⟩
          simp only [indicator_of_notMem h4, mul_zero]
        · simp only [indicator_of_notMem h3, zero_mul]
  rw [lintegral_congr h1, lintegral_indicator hImeas]
  exact setLIntegral_measure_zero _ _ (volume_irregular_slice hm₃ hm₄ K)

/-- **The integration formula** for the whole product of the two shell measures. -/
theorem lintegral_prod_eq (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)) =
      ∫⁻ P in region 3 m₃ m₄, ∫⁻ x, f x ∂(fibreMeasure m₃ m₄ P) := by
  have hae : ∀ᵐ x ∂((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)),
      x ∈ regular 3 m₃ m₄ := ae_iff.mpr (prod_regular_compl hm₃ hm₄)
  rw [← lintegral_regular_eq hm₃ hm₄ hf, Measure.restrict_eq_self_of_ae_mem hae]

/-- **The disintegration** of the product of the two shell measures over the total momentum. -/
theorem prod_eq_bind (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) :
    (FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄) =
      (volume.restrict (region 3 m₃ m₄)).bind (fibreMeasure m₃ m₄) := by
  have hae : ∀ᵐ x ∂((FutureShell.measure 3 m₃).prod (FutureShell.measure 3 m₄)),
      x ∈ regular 3 m₃ m₄ := ae_iff.mpr (prod_regular_compl hm₃ hm₄)
  rw [← restrict_regular_eq_bind hm₃ hm₄, Measure.restrict_eq_self_of_ae_mem hae]

end ProjectAinos.SpecialRelativity.TwoBodyFibre
