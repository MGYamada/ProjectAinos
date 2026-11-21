/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.MassFoliation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The measure of the final states of several particles at a fixed total momentum

For `k + 2` outgoing particles with the masses `m 0, …, m (k+1) ≥ 0` the space momenta form the
nested product `Config k` (`Config 0` = pairs, `Config (k+1) = Config k × ℝ³`), with the product
`shellProd m k` of the shell measures `d³π/E`. The measure of the final states at the total
momentum `P` is `manyMeasure m k P` (Landau–Lifshitz, *The Classical Theory of Fields*, §12).
It is defined by peeling off the last particle: for `k + 1`, the first `k + 2` particles have an
intermediate total momentum `Q` of rest mass `M` with `Σ_{i ≤ k+1} m i < M < M_P − m (k+2)`, and

`ν^{(k+1)}_P = ∫ M dM ∫ ν^{(k)}_Q ⊗ δ_{π} dν^{(2)}_{M, m(k+2), P}(Q, π)`

with the two-body measure `fibreMeasure M (m (k+2)) P` of the pair `(Q, p_{k+3})`
(`lintegral_manyMeasure_succ`). For `k = 0` it is `fibreMeasure (m 0) (m 1) P`
(`manyMeasure_zero`). The measure is the image of an explicit density on a fixed parameter space
`Param k` of intermediate masses and directions (`weight`, `phase`, `base`), so the family is
measurable in the total momentum, also inside the integrals of the induction
(`measurable_lintegral_manyMeasure`, `measurable_manyMeasure`).

* `lintegral_shellProd`: **the integration formula**
  `∫ f d(μ₀ ⊗ ⋯ ⊗ μ_{k+1}) = ∫_{M_P > Σ m} (∫ f dν^{(k)}_P) d⁴P` for every measurable `f ≥ 0`,
  by induction from `lintegral_prod_eq` and the foliation `d⁴Q = M dM d³K/E_M`
  (`lintegral_massRegion`). The formula holds for the whole product measure, since the pairs that
  are not regular are a null set in the two-body case (`prod_regular_compl`).
  `shellProd_eq_bind` is the disintegration `μ₀ ⊗ ⋯ ⊗ μ_{k+1} = ∫ ν^{(k)}_P d⁴P`.
* `map_manyMeasure`: **covariance**, `L_* ν^{(k)}_P = ν^{(k)}_{LP}` for orthochronous `L`.
* `manyMeasure_totalMomentum_ne`: **the support**, `ν^{(k)}_P` is carried by the configurations
  of total momentum `P`; `manyMeasure_univ_le`: the total mass is at most `(2π)^{k+1} M_P^{2k}`.
* `manyCrossSection_covariant`: the cross-section `(1/4F) ∫_S W dν^{(k)}_{p₁+p₂}` is invariant
  for a weight that is a Lorentz scalar.
* `manyMeasure_one_pos`, `exists_manyCrossSection_pos`: instances with three particles of
  mass `1` at rest mass `4`, with a positive measure and a positive cross-section.

Only one grouping is used, the one that peels off the last particle; the comparison of different
groupings is not stated.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace ProjectAinos.SpecialRelativity.ManyBody

open SmoothGeometry SmoothGeometry.Minkowski FutureShell TwoBodyFibre

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Measurability in the mass of the first particle -/

theorem continuous_energy_mass' {d : ℕ} :
    Continuous fun z : ℝ × (Fin d → ℝ) => energy z.1 z.2 :=
  Real.continuous_sqrt.comp ((continuous_fst.pow 2).add (continuous_sum_sq.comp continuous_snd))

theorem measurable_labFirst_mass (m₄ : ℝ) :
    Measurable fun z : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => labFirst z.1 m₄ z.2.1 z.2.2 := by
  simp only [labFirst_eq]
  have he₃ : Measurable fun z : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => energy z.1 z.2.2 :=
    (continuous_energy_mass'.comp (continuous_fst.prodMk
      (continuous_snd.comp continuous_snd))).measurable
  have he₄ : Measurable fun z : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => energy m₄ z.2.2 :=
    (continuous_energy.comp (continuous_snd.comp continuous_snd)).measurable
  have hM : Measurable fun z : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => pairMass z.1 m₄ z.2.2 := by
    have h := he₃.add he₄
    exact h
  have hs : Measurable fun z : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => ∑ i, z.2.1 i ^ 2 :=
    (continuous_sum_sq.comp (continuous_fst.comp continuous_snd)).measurable
  have hT : Measurable fun z : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      Real.sqrt (pairMass z.1 m₄ z.2.2 ^ 2 + ∑ i, z.2.1 i ^ 2) :=
    Real.continuous_sqrt.measurable.comp ((hM.pow_const 2).add hs)
  have hA : Measurable fun z : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => ∑ i, z.2.1 i * z.2.2 i :=
    (continuous_dot.comp continuous_snd).measurable
  have hk : Measurable fun z : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => z.2.2 :=
    measurable_snd.comp measurable_snd
  have hK : Measurable fun z : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => z.2.1 :=
    measurable_fst.comp measurable_snd
  exact hk.add (((hA.div (hM.mul (hM.add hT))).add (he₃.div hM)).smul hK)

theorem measurable_restMomentum_mass (m₄ : ℝ) :
    Measurable fun z : ℝ × ℝ => restMomentum z.1 m₄ z.2 := by
  have h : Continuous fun z : ℝ × ℝ => Real.sqrt (kallen (z.2 ^ 2) (z.1 ^ 2) (m₄ ^ 2)) := by
    unfold kallen
    fun_prop
  exact h.measurable.div (measurable_const.mul measurable_snd)

theorem measurable_fibrePair_mass (m₄ : ℝ) :
    Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 =>
      fibrePair z.1.1 m₄ z.1.2 z.2 := by
  have hM : Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 => z.1.1 :=
    measurable_fst.comp measurable_fst
  have hP : Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 => z.1.2 :=
    measurable_snd.comp measurable_fst
  have hK0 := contDiff_spaceMomentum.continuous.measurable.comp hP
  have hK : Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 =>
      spaceMomentum z.1.2 := hK0
  have hI0 := continuous_invariantMass.measurable.comp hP
  have hI : Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 =>
      invariantMass z.1.2 := hI0
  have hq0 := (measurable_restMomentum_mass m₄).comp (hM.prodMk hI)
  have hq : Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 =>
      restMomentum z.1.1 m₄ (invariantMass z.1.2) := hq0
  have hn : Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 => z.2 :=
    measurable_snd
  have hv0 := continuous_sphereVec.measurable.comp hn
  have hv : Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 => sphereVec z.2 := hv0
  have hk : Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 =>
      restMomentum z.1.1 m₄ (invariantMass z.1.2) • sphereVec z.2 := hq.smul hv
  have h10 := (measurable_labFirst_mass m₄).comp (hM.prodMk (hK.prodMk hk))
  have h1 : Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 =>
      labFirst z.1.1 m₄ (spaceMomentum z.1.2)
        (restMomentum z.1.1 m₄ (invariantMass z.1.2) • sphereVec z.2) := h10
  have h2 : Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 =>
      (labFirst z.1.1 m₄ (spaceMomentum z.1.2)
          (restMomentum z.1.1 m₄ (invariantMass z.1.2) • sphereVec z.2),
        spaceMomentum z.1.2 - labFirst z.1.1 m₄ (spaceMomentum z.1.2)
          (restMomentum z.1.1 m₄ (invariantMass z.1.2) • sphereVec z.2)) :=
    h1.prodMk (hK.sub h1)
  exact h2

/-- The density `q/M` of the two-body measure of the fibre. -/
def fibreWeight (m₃ m₄ : ℝ) (P : MinkowskiModel 3) : ℝ≥0∞ :=
  ENNReal.ofReal (restMomentum m₃ m₄ (invariantMass P) / invariantMass P)

theorem measurable_fibreWeight_mass (m₄ : ℝ) :
    Measurable fun z : ℝ × MinkowskiModel 3 => fibreWeight z.1 m₄ z.2 := by
  have hs : Measurable fun z : ℝ × MinkowskiModel 3 => z.2 := measurable_snd
  have hI0 := continuous_invariantMass.measurable.comp hs
  have hI : Measurable fun z : ℝ × MinkowskiModel 3 => invariantMass z.2 := hI0
  have hq0 := (measurable_restMomentum_mass m₄).comp (measurable_fst.prodMk hI)
  have hq : Measurable fun z : ℝ × MinkowskiModel 3 => restMomentum z.1 m₄ (invariantMass z.2) :=
    hq0
  have h0 := ENNReal.measurable_ofReal.comp (hq.div hI)
  exact h0

theorem lintegral_fibreMeasure' {m₃ m₄ : ℝ} (P : MinkowskiModel 3)
    {f : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(fibreMeasure m₃ m₄ P) =
      fibreWeight m₃ m₄ P * ∫⁻ n, f (fibrePair m₃ m₄ P n) ∂Sphere.sphereMeasure :=
  lintegral_fibreMeasure P hf

/-- The total momentum `Q` of the first particles in the pair `(Q, p)` of the two-body fibre over
`P` with the masses `M`, `m'` and the direction `n`. -/
def interMomentum (M m' : ℝ) (P : MinkowskiModel 3) (n : sphere (0 : E3) 1) :
    MinkowskiModel 3 :=
  point M (fibrePair M m' P n).1

theorem measurable_interMomentum (m' : ℝ) :
    Measurable fun z : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 =>
      interMomentum z.1.1 m' z.1.2 z.2 := by
  have h0 := measurable_point_mass.comp ((measurable_fst.comp measurable_fst).prodMk
    (measurable_fibrePair_mass m').fst)
  exact h0

/-! ### Configurations and parameters -/

/-- The space momenta of `k + 2` particles as nested pairs. -/
def Config : ℕ → Type
  | 0 => (Fin 3 → ℝ) × (Fin 3 → ℝ)
  | k + 1 => Config k × (Fin 3 → ℝ)

instance Config.instMeasurableSpace : (k : ℕ) → MeasurableSpace (Config k)
  | 0 => (inferInstance : MeasurableSpace ((Fin 3 → ℝ) × (Fin 3 → ℝ)))
  | k + 1 => @Prod.instMeasurableSpace (Config k) (Fin 3 → ℝ) (Config.instMeasurableSpace k) _

/-- The parameters of the sequential decay into `k + 2` particles: for each step after the
first, the rest mass of the first particles and a direction, and a direction for the first
pair. -/
def Param : ℕ → Type
  | 0 => sphere (0 : E3) 1
  | k + 1 => (ℝ × sphere (0 : E3) 1) × Param k

instance Param.instMeasurableSpace : (k : ℕ) → MeasurableSpace (Param k)
  | 0 => (inferInstance : MeasurableSpace (sphere (0 : E3) 1))
  | k + 1 => @Prod.instMeasurableSpace (ℝ × sphere (0 : E3) 1) (Param k) _
      (Param.instMeasurableSpace k)

variable (m : ℕ → ℝ)

/-- The sum `Σ_{i ≤ k+1} m i` of the masses of the first `k + 2` particles. -/
def massSum (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 2), m i

/-- The product of the shell measures of the first `k + 2` particles. -/
def shellProd : (k : ℕ) → Measure (Config k)
  | 0 => (FutureShell.measure 3 (m 0)).prod (FutureShell.measure 3 (m 1))
  | k + 1 => (shellProd k).prod (FutureShell.measure 3 (m (k + 2)))

/-- The reference measure on the parameters: the Lebesgue measure of the masses and the surface
measure of the directions. -/
def base : (k : ℕ) → Measure (Param k)
  | 0 => Sphere.sphereMeasure
  | k + 1 => ((volume : Measure ℝ).prod Sphere.sphereMeasure).prod (base k)

/-- The factor `M` of the intermediate mass `M` of the first particles, on the window
`S < M < M_P − m'` of the masses. -/
def window (S m' : ℝ) (P : MinkowskiModel 3) (M : ℝ) : ℝ≥0∞ :=
  {z : MinkowskiModel 3 × ℝ | S < z.2 ∧ z.2 < invariantMass z.1 - m'}.indicator
    (fun z => ENNReal.ofReal z.2) (P, M)

/-- The density of the measure of the final states on the parameters. -/
def weight : (k : ℕ) → MinkowskiModel 3 → Param k → ℝ≥0∞
  | 0 => fun P _ => fibreWeight (m 0) (m 1) P
  | k + 1 => fun P (z : (ℝ × sphere (0 : E3) 1) × Param k) =>
      window (massSum m k) (m (k + 2)) P z.1.1 * fibreWeight z.1.1 (m (k + 2)) P *
        weight k (interMomentum z.1.1 (m (k + 2)) P z.1.2) z.2

/-- The space momenta of the particles for the parameters. -/
def phase : (k : ℕ) → MinkowskiModel 3 → Param k → Config k
  | 0 => fun P n => fibrePair (m 0) (m 1) P n
  | k + 1 => fun P (z : (ℝ × sphere (0 : E3) 1) × Param k) =>
      ((phase k (interMomentum z.1.1 (m (k + 2)) P z.1.2) z.2,
        (fibrePair z.1.1 (m (k + 2)) P z.1.2).2) : Config k × (Fin 3 → ℝ))

/-- **The measure of the final states of `k + 2` particles at the total momentum `P`.** -/
def manyMeasure (k : ℕ) (P : MinkowskiModel 3) : Measure (Config k) :=
  Measure.map (phase m k P) ((base k).withDensity (weight m k P))

instance shellProd.instSFinite : (k : ℕ) → SFinite (shellProd m k)
  | 0 => by
    change SFinite ((FutureShell.measure 3 (m 0)).prod (FutureShell.measure 3 (m 1)))
    infer_instance
  | k + 1 => by
    have := shellProd.instSFinite k
    change SFinite ((shellProd m k).prod (FutureShell.measure 3 (m (k + 2))))
    infer_instance

instance base.instSFinite : (k : ℕ) → SFinite (base k)
  | 0 => by
    change SFinite Sphere.sphereMeasure
    infer_instance
  | k + 1 => by
    have := base.instSFinite k
    change SFinite (((volume : Measure ℝ).prod Sphere.sphereMeasure).prod (base k))
    infer_instance

/-! ### Measurability and the integrals -/

theorem massSum_zero : massSum m 0 = m 0 + m 1 := by
  simp [massSum, Finset.sum_range_succ]

theorem massSum_succ (k : ℕ) : massSum m (k + 1) = massSum m k + m (k + 2) :=
  Finset.sum_range_succ _ _

theorem massSum_nonneg (hm : ∀ i, 0 ≤ m i) (k : ℕ) : 0 ≤ massSum m k :=
  Finset.sum_nonneg fun i _ => hm i

theorem measurable_window (S m' : ℝ) :
    Measurable fun z : MinkowskiModel 3 × ℝ => window S m' z.1 z.2 := by
  have hI0 := continuous_invariantMass.measurable.comp
    (measurable_fst : Measurable fun z : MinkowskiModel 3 × ℝ => z.1)
  have hI : Measurable fun z : MinkowskiModel 3 × ℝ => invariantMass z.1 - m' :=
    hI0.sub_const m'
  have hset : MeasurableSet {z : MinkowskiModel 3 × ℝ | S < z.2 ∧ z.2 < invariantMass z.1 - m'} :=
    (measurableSet_lt measurable_const measurable_snd).inter (measurableSet_lt measurable_snd hI)
  have h := (ENNReal.measurable_ofReal.comp
    (measurable_snd : Measurable fun z : MinkowskiModel 3 × ℝ => z.2)).indicator hset
  exact h

theorem window_of_mem {S m' M : ℝ} {P : MinkowskiModel 3} (h : S < M ∧ M < invariantMass P - m') :
    window S m' P M = ENNReal.ofReal M := by
  rw [window, indicator_of_mem (show (P, M) ∈ {z : MinkowskiModel 3 × ℝ |
    S < z.2 ∧ z.2 < invariantMass z.1 - m'} from h)]

theorem window_of_notMem {S m' M : ℝ} {P : MinkowskiModel 3}
    (h : ¬(S < M ∧ M < invariantMass P - m')) : window S m' P M = 0 := by
  rw [window, indicator_of_notMem (show (P, M) ∉ {z : MinkowskiModel 3 × ℝ |
    S < z.2 ∧ z.2 < invariantMass z.1 - m'} from h)]

/-- The density is measurable in the total momentum and the parameters. -/
theorem measurable_weight :
    ∀ k : ℕ, Measurable fun z : MinkowskiModel 3 × Param k => weight m k z.1 z.2
  | 0 => by
    have h0 := (measurable_fibreWeight_mass (m 1)).comp
      ((measurable_const : Measurable fun _ : MinkowskiModel 3 × Param 0 => m 0).prodMk
        (measurable_fst : Measurable fun z : MinkowskiModel 3 × Param 0 => z.1))
    exact h0
  | k + 1 => by
    have ih := measurable_weight k
    change Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
      window (massSum m k) (m (k + 2)) z.1 z.2.1.1 * fibreWeight z.2.1.1 (m (k + 2)) z.1 *
        weight m k (interMomentum z.2.1.1 (m (k + 2)) z.1 z.2.1.2) z.2.2
    have hP : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        z.1 := measurable_fst
    have hM : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        z.2.1.1 := measurable_fst.comp (measurable_fst.comp measurable_snd)
    have hn : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        z.2.1.2 := measurable_snd.comp (measurable_fst.comp measurable_snd)
    have hθ : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        z.2.2 := measurable_snd.comp measurable_snd
    have h10 := (measurable_window (massSum m k) (m (k + 2))).comp (hP.prodMk hM)
    have h1 : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        window (massSum m k) (m (k + 2)) z.1 z.2.1.1 := h10
    have h20 := (measurable_fibreWeight_mass (m (k + 2))).comp (hM.prodMk hP)
    have h2 : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        fibreWeight z.2.1.1 (m (k + 2)) z.1 := h20
    have hQ0 := (measurable_interMomentum (m (k + 2))).comp ((hM.prodMk hP).prodMk hn)
    have hQ : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        interMomentum z.2.1.1 (m (k + 2)) z.1 z.2.1.2 := hQ0
    have h30 := ih.comp (hQ.prodMk hθ)
    have h3 : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        weight m k (interMomentum z.2.1.1 (m (k + 2)) z.1 z.2.1.2) z.2.2 := h30
    have h := (h1.mul h2).mul h3
    exact h

/-- The space momenta are measurable in the total momentum and the parameters. -/
theorem measurable_phase :
    ∀ k : ℕ, Measurable fun z : MinkowskiModel 3 × Param k => phase m k z.1 z.2
  | 0 => by
    have h0 := measurable_fibrePair (m₃ := m 0) (m₄ := m 1)
    exact h0
  | k + 1 => by
    have ih := measurable_phase k
    change Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
      ((phase m k (interMomentum z.2.1.1 (m (k + 2)) z.1 z.2.1.2) z.2.2,
        (fibrePair z.2.1.1 (m (k + 2)) z.1 z.2.1.2).2) : Config k × (Fin 3 → ℝ))
    have hP : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        z.1 := measurable_fst
    have hM : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        z.2.1.1 := measurable_fst.comp (measurable_fst.comp measurable_snd)
    have hn : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        z.2.1.2 := measurable_snd.comp (measurable_fst.comp measurable_snd)
    have hθ : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        z.2.2 := measurable_snd.comp measurable_snd
    have hQ0 := (measurable_interMomentum (m (k + 2))).comp ((hM.prodMk hP).prodMk hn)
    have hQ : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        interMomentum z.2.1.1 (m (k + 2)) z.1 z.2.1.2 := hQ0
    have h10 := ih.comp (hQ.prodMk hθ)
    have h1 : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        phase m k (interMomentum z.2.1.1 (m (k + 2)) z.1 z.2.1.2) z.2.2 := h10
    have h20 := (measurable_fibrePair_mass (m (k + 2))).comp ((hM.prodMk hP).prodMk hn)
    have h2 : Measurable fun z : MinkowskiModel 3 × ((ℝ × sphere (0 : E3) 1) × Param k) =>
        (fibrePair z.2.1.1 (m (k + 2)) z.1 z.2.1.2).2 := h20.snd
    have h := h1.prodMk h2
    exact h

theorem measurable_weight_right (k : ℕ) (P : MinkowskiModel 3) : Measurable (weight m k P) := by
  have h := (measurable_weight m k).comp
    (measurable_prodMk_left : Measurable fun θ : Param k => (P, θ))
  exact h

theorem measurable_phase_right (k : ℕ) (P : MinkowskiModel 3) : Measurable (phase m k P) := by
  have h := (measurable_phase m k).comp
    (measurable_prodMk_left : Measurable fun θ : Param k => (P, θ))
  exact h

/-- The integral against the measure of the final states is an integral over the
parameters. -/
theorem lintegral_manyMeasure (k : ℕ) (P : MinkowskiModel 3) {f : Config k → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂(manyMeasure m k P) = ∫⁻ θ, weight m k P θ * f (phase m k P θ) ∂(base k) := by
  rw [manyMeasure, lintegral_map hf (measurable_phase_right m k P)]
  exact lintegral_withDensity_eq_lintegral_mul _ (measurable_weight_right m k P)
    (hf.comp (measurable_phase_right m k P))

/-- **Measurability of the family**: the integral of a jointly measurable function against
`manyMeasure m k (g a)` is measurable in `a`. -/
theorem measurable_lintegral_manyMeasure (k : ℕ) {α : Type*} [MeasurableSpace α]
    {F : α × Config k → ℝ≥0∞} (hF : Measurable F) {g : α → MinkowskiModel 3}
    (hg : Measurable g) :
    Measurable fun a => ∫⁻ x, F (a, x) ∂(manyMeasure m k (g a)) := by
  have h1 : (fun a => ∫⁻ x, F (a, x) ∂(manyMeasure m k (g a))) =
      fun a => ∫⁻ θ, weight m k (g a) θ * F (a, phase m k (g a) θ) ∂(base k) := by
    funext a
    exact lintegral_manyMeasure m k (g a)
      (hF.comp (measurable_prodMk_left : Measurable fun x : Config k => (a, x)))
  rw [h1]
  have hga : Measurable fun z : α × Param k => (g z.1, z.2) :=
    (hg.comp measurable_fst).prodMk measurable_snd
  have hw0 := (measurable_weight m k).comp hga
  have hw : Measurable fun z : α × Param k => weight m k (g z.1) z.2 := hw0
  have hp0 := (measurable_phase m k).comp hga
  have hp : Measurable fun z : α × Param k => phase m k (g z.1) z.2 := hp0
  have hF0 := hF.comp (measurable_fst.prodMk hp)
  have hF1 : Measurable fun z : α × Param k => F (z.1, phase m k (g z.1) z.2) := hF0
  have h := hw.mul hF1
  exact h.lintegral_prod_right'

/-- For two particles, the measure is the two-body measure of the fibre. -/
theorem manyMeasure_zero (P : MinkowskiModel 3) :
    manyMeasure m 0 P = fibreMeasure (m 0) (m 1) P := by
  change Measure.map (fibrePair (m 0) (m 1) P)
      (Sphere.sphereMeasure.withDensity fun _ => fibreWeight (m 0) (m 1) P) = _
  rw [withDensity_const, Measure.map_smul]
  · rfl
  · exact (measurable_fibrePair_right (m₃ := m 0) (m₄ := m 1) P).aemeasurable

theorem measurable_fibrePair_mass_right (m' : ℝ) (P : MinkowskiModel 3) :
    Measurable fun a : ℝ × sphere (0 : E3) 1 => fibrePair a.1 m' P a.2 := by
  have h0 := (measurable_fibrePair_mass m').comp
    (((measurable_fst : Measurable fun a : ℝ × sphere (0 : E3) 1 => a.1).prodMk
      (measurable_const : Measurable fun _ : ℝ × sphere (0 : E3) 1 => P)).prodMk
        (measurable_snd : Measurable fun a : ℝ × sphere (0 : E3) 1 => a.2))
  exact h0

theorem measurable_interMomentum_right (m' : ℝ) (P : MinkowskiModel 3) :
    Measurable fun a : ℝ × sphere (0 : E3) 1 => interMomentum a.1 m' P a.2 := by
  have h0 := (measurable_interMomentum m').comp
    (((measurable_fst : Measurable fun a : ℝ × sphere (0 : E3) 1 => a.1).prodMk
      (measurable_const : Measurable fun _ : ℝ × sphere (0 : E3) 1 => P)).prodMk
        (measurable_snd : Measurable fun a : ℝ × sphere (0 : E3) 1 => a.2))
  exact h0

/-- The inner integral of the step: the integral of `f` against the measure of the first
particles at the total momentum `point M y.1`, with the last particle at `y.2`. -/
theorem measurable_lintegral_point (k : ℕ) {f : Config (k + 1) → ℝ≥0∞} (hf : Measurable f)
    (M : ℝ) :
    Measurable fun y : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ∫⁻ x, f ((x, y.2) : Config k × (Fin 3 → ℝ)) ∂(manyMeasure m k (point M y.1)) := by
  have hF0 := hf.comp ((measurable_snd : Measurable fun z : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) ×
    Config k => z.2).prodMk (measurable_snd.comp measurable_fst))
  have hF : Measurable fun z : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × Config k =>
      f ((z.2, z.1.2) : Config k × (Fin 3 → ℝ)) := hF0
  have hg0 := measurable_point_mass.comp ((measurable_const : Measurable fun _ :
    (Fin 3 → ℝ) × (Fin 3 → ℝ) => M).prodMk measurable_fst)
  have hg : Measurable fun y : (Fin 3 → ℝ) × (Fin 3 → ℝ) => point M y.1 := hg0
  exact measurable_lintegral_manyMeasure m k hF hg

/-- **Peeling off the last particle**: `ν^{(k+1)}_P` is the integral over the intermediate mass
`M` (with the factor `M` on the window `Σ m < M < M_P − m (k+2)`) of the two-body measure of
`(Q, p)` with the measures `ν^{(k)}_Q` of the first particles. -/
theorem lintegral_manyMeasure_succ (k : ℕ) (P : MinkowskiModel 3)
    {f : Config (k + 1) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(manyMeasure m (k + 1) P) =
      ∫⁻ M, window (massSum m k) (m (k + 2)) P M *
        ∫⁻ y, (∫⁻ x, f ((x, y.2) : Config k × (Fin 3 → ℝ)) ∂(manyMeasure m k (point M y.1)))
          ∂(fibreMeasure M (m (k + 2)) P) := by
  rw [lintegral_manyMeasure m (k + 1) P hf]
  have hint0 := (measurable_weight_right m (k + 1) P).mul
    (hf.comp (measurable_phase_right m (k + 1) P))
  have hint : Measurable fun z : (ℝ × sphere (0 : E3) 1) × Param k =>
      weight m (k + 1) P z * f (phase m (k + 1) P z) := hint0
  change ∫⁻ z : (ℝ × sphere (0 : E3) 1) × Param k,
      weight m (k + 1) P z * f (phase m (k + 1) P z) ∂(((volume : Measure ℝ).prod
        Sphere.sphereMeasure).prod (base k)) = _
  rw [lintegral_prod _ hint.aemeasurable]
  have h1 : ∀ a : ℝ × sphere (0 : E3) 1,
      ∫⁻ θ, weight m (k + 1) P (a, θ) * f (phase m (k + 1) P (a, θ)) ∂(base k) =
        window (massSum m k) (m (k + 2)) P a.1 * fibreWeight a.1 (m (k + 2)) P *
          ∫⁻ x, f ((x, (fibrePair a.1 (m (k + 2)) P a.2).2) : Config k × (Fin 3 → ℝ))
            ∂(manyMeasure m k (interMomentum a.1 (m (k + 2)) P a.2)) := by
    intro a
    have hfa : Measurable fun x : Config k =>
        f ((x, (fibrePair a.1 (m (k + 2)) P a.2).2) : Config k × (Fin 3 → ℝ)) := by
      have h0 := hf.comp (measurable_prodMk_right : Measurable fun x : Config k =>
        ((x, (fibrePair a.1 (m (k + 2)) P a.2).2) : Config k × (Fin 3 → ℝ)))
      exact h0
    have hm1 : Measurable fun θ : Param k =>
        weight m k (interMomentum a.1 (m (k + 2)) P a.2) θ *
          f ((phase m k (interMomentum a.1 (m (k + 2)) P a.2) θ,
            (fibrePair a.1 (m (k + 2)) P a.2).2) : Config k × (Fin 3 → ℝ)) := by
      have h0 := (measurable_weight_right m k (interMomentum a.1 (m (k + 2)) P a.2)).mul
        (hfa.comp (measurable_phase_right m k (interMomentum a.1 (m (k + 2)) P a.2)))
      exact h0
    rw [lintegral_manyMeasure m k _ hfa, ← lintegral_const_mul _ hm1]
    refine lintegral_congr fun θ => ?_
    change window (massSum m k) (m (k + 2)) P a.1 * fibreWeight a.1 (m (k + 2)) P *
        weight m k (interMomentum a.1 (m (k + 2)) P a.2) θ *
          f ((phase m k (interMomentum a.1 (m (k + 2)) P a.2) θ,
            (fibrePair a.1 (m (k + 2)) P a.2).2) : Config k × (Fin 3 → ℝ)) = _
    ring
  rw [lintegral_congr h1]
  have hI : Measurable fun a : ℝ × sphere (0 : E3) 1 =>
      ∫⁻ x, f ((x, (fibrePair a.1 (m (k + 2)) P a.2).2) : Config k × (Fin 3 → ℝ))
        ∂(manyMeasure m k (interMomentum a.1 (m (k + 2)) P a.2)) := by
    have hp := measurable_fibrePair_mass_right (m (k + 2)) P
    have hF0 := hf.comp ((measurable_snd : Measurable fun z : (ℝ × sphere (0 : E3) 1) ×
      Config k => z.2).prodMk (hp.snd.comp measurable_fst))
    have hF : Measurable fun z : (ℝ × sphere (0 : E3) 1) × Config k =>
        f ((z.2, (fibrePair z.1.1 (m (k + 2)) P z.1.2).2) : Config k × (Fin 3 → ℝ)) := hF0
    exact measurable_lintegral_manyMeasure m k hF (measurable_interMomentum_right _ P)
  have hw0 := (measurable_window (massSum m k) (m (k + 2))).comp
    ((measurable_const : Measurable fun _ : ℝ × sphere (0 : E3) 1 => P).prodMk measurable_fst)
  have hw : Measurable fun a : ℝ × sphere (0 : E3) 1 =>
      window (massSum m k) (m (k + 2)) P a.1 := hw0
  have hq0 := (measurable_fibreWeight_mass (m (k + 2))).comp
    ((measurable_fst : Measurable fun a : ℝ × sphere (0 : E3) 1 => a.1).prodMk
      (measurable_const : Measurable fun _ : ℝ × sphere (0 : E3) 1 => P))
  have hq : Measurable fun a : ℝ × sphere (0 : E3) 1 => fibreWeight a.1 (m (k + 2)) P := hq0
  have hW : Measurable fun a : ℝ × sphere (0 : E3) 1 =>
      window (massSum m k) (m (k + 2)) P a.1 * fibreWeight a.1 (m (k + 2)) P *
        ∫⁻ x, f ((x, (fibrePair a.1 (m (k + 2)) P a.2).2) : Config k × (Fin 3 → ℝ))
          ∂(manyMeasure m k (interMomentum a.1 (m (k + 2)) P a.2)) := by
    have h0 := (hw.mul hq).mul hI
    exact h0
  rw [lintegral_prod _ hW.aemeasurable]
  refine lintegral_congr fun M => ?_
  dsimp only
  have hIM : Measurable fun n : sphere (0 : E3) 1 =>
      ∫⁻ x, f ((x, (fibrePair M (m (k + 2)) P n).2) : Config k × (Fin 3 → ℝ))
        ∂(manyMeasure m k (interMomentum M (m (k + 2)) P n)) := by
    have h0 := hI.comp (measurable_prodMk_left : Measurable fun n : sphere (0 : E3) 1 => (M, n))
    exact h0
  rw [lintegral_const_mul _ hIM, lintegral_fibreMeasure' P (measurable_lintegral_point m k hf M),
    mul_assoc]
  rfl

/-! ### The integration formula -/

/-- The foliation `d⁴Q = M dM d³K/E_M` paired with the shell measure of the last particle. -/
theorem lintegral_shell_foliation {S : ℝ} (hS : 0 ≤ S) (m' : ℝ)
    {H : (Fin 3 → ℝ) × MinkowskiModel 3 → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ π, (∫⁻ Q in massRegion S, H (π, Q)) ∂(FutureShell.measure 3 m') =
      ∫⁻ M in Ioi S, ENNReal.ofReal M *
        ∫⁻ y, H (y.2, point M y.1)
          ∂((FutureShell.measure 3 M).prod (FutureShell.measure 3 m')) := by
  have h1 : ∀ π : Fin 3 → ℝ, ∫⁻ Q in massRegion S, H (π, Q) =
      ∫⁻ M in Ioi S, ∫⁻ K, ENNReal.ofReal (M / energy M K) * H (π, point M K) := fun π =>
    lintegral_massRegion hS (hH.comp (measurable_prodMk_left :
      Measurable fun Q : MinkowskiModel 3 => (π, Q)))
  rw [lintegral_congr h1]
  have hE : Measurable fun z : ((Fin 3 → ℝ) × ℝ) × (Fin 3 → ℝ) => energy z.1.2 z.2 := by
    have h0 := continuous_energy_mass.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd :
        Measurable fun z : ((Fin 3 → ℝ) × ℝ) × (Fin 3 → ℝ) => (z.1.2, z.2))
    exact h0
  have hpt : Measurable fun z : ((Fin 3 → ℝ) × ℝ) × (Fin 3 → ℝ) => point z.1.2 z.2 := by
    have h0 := measurable_point_mass.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd :
        Measurable fun z : ((Fin 3 → ℝ) × ℝ) × (Fin 3 → ℝ) => (z.1.2, z.2))
    exact h0
  have hHz : Measurable fun z : ((Fin 3 → ℝ) × ℝ) × (Fin 3 → ℝ) =>
      H (z.1.1, point z.1.2 z.2) := by
    have h0 := hH.comp ((measurable_fst.comp measurable_fst).prodMk hpt)
    exact h0
  have hfull : Measurable fun z : ((Fin 3 → ℝ) × ℝ) × (Fin 3 → ℝ) =>
      ENNReal.ofReal (z.1.2 / energy z.1.2 z.2) * H (z.1.1, point z.1.2 z.2) := by
    have h0 := (ENNReal.measurable_ofReal.comp
      ((measurable_snd.comp measurable_fst).div hE)).mul hHz
    exact h0
  rw [lintegral_lintegral_swap hfull.lintegral_prod_right'.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun M hM => ?_
  have hM' : 0 < M := lt_of_le_of_lt hS hM
  have hK2 : Measurable fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) => H (z.2, point M z.1) := by
    have h0 := hH.comp (measurable_snd.prodMk (continuous_point.measurable.comp measurable_fst) :
      Measurable fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (z.2, point M z.1))
    exact h0
  have hK3 : Measurable fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ENNReal.ofReal (M / energy M z.1) * H (z.2, point M z.1) := by
    have he0 := (continuous_energy (d := 3) (m := M)).measurable.comp
      (measurable_fst : Measurable fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) => z.1)
    have he : Measurable fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) => energy M z.1 := he0
    have hd : Measurable fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) => M / energy M z.1 :=
      (measurable_const : Measurable fun _ : (Fin 3 → ℝ) × (Fin 3 → ℝ) => M).div he
    have h0 := (ENNReal.measurable_ofReal.comp hd).mul hK2
    exact h0
  have hinner : Measurable fun K : Fin 3 → ℝ =>
      ∫⁻ π, H (π, point M K) ∂(FutureShell.measure 3 m') := hK2.lintegral_prod_right'
  have hμ : FutureShell.measure 3 M =
      (volume : Measure (Fin 3 → ℝ)).withDensity fun π => ENNReal.ofReal (energy M π)⁻¹ := by
    rw [FutureShell.measure, domain_eq_univ hM'.ne', Measure.restrict_univ]
  rw [lintegral_prod _ hK2.aemeasurable, hμ,
    lintegral_withDensity_eq_lintegral_mul _ measurable_density hinner,
    ← lintegral_const_mul _ (measurable_density.mul hinner)]
  have hswap := lintegral_lintegral_swap (μ := FutureShell.measure 3 m')
    (ν := (volume : Measure (Fin 3 → ℝ)))
    (f := fun π K => ENNReal.ofReal (M / energy M K) * H (π, point M K))
    (by
      have h0 := hK3.comp (measurable_snd.prodMk measurable_fst :
        Measurable fun z : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (z.2, z.1))
      exact h0.aemeasurable)
  rw [hswap]
  refine lintegral_congr fun K => ?_
  have hHK : Measurable fun π : Fin 3 → ℝ => H (π, point M K) :=
    hH.comp (measurable_prodMk_right : Measurable fun π : Fin 3 → ℝ => (π, point M K))
  simp only [Pi.mul_apply]
  rw [lintegral_const_mul _ hHK, ← mul_assoc, ← ENNReal.ofReal_mul hM'.le, div_eq_mul_inv]

/-- A total momentum that is regular for the masses `M > S` and `m'` is in the region of
`S + m'`. -/
theorem mem_massRegion_of_mem_region {S m' M : ℝ} (hS : 0 ≤ S) (hm' : 0 ≤ m') (hM : S < M)
    {P : MinkowskiModel 3} (hP : P ∈ region 3 M m') : P ∈ massRegion (S + m') := by
  refine ⟨hP.1, ?_⟩
  have h1 : (S + m') ^ 2 < (M + m') ^ 2 := by nlinarith
  exact lt_trans h1 hP.2

/-- For a total momentum of positive energy, the regularity for `M` and `m'` is the window
`M < M_P − m'`. -/
theorem mem_region_iff {S m' M : ℝ} (hS : 0 ≤ S) (hm' : 0 ≤ m') (hM : S < M)
    {P : MinkowskiModel 3} (hP : 0 < time P) : P ∈ region 3 M m' ↔ M < invariantMass P - m' := by
  have h0 : 0 ≤ M + m' := by linarith
  constructor
  · intro h
    have := (Real.lt_sqrt h0).mpr h.2
    change M + m' < invariantMass P at this
    linarith
  · intro h
    refine ⟨hP, (Real.lt_sqrt h0).mp ?_⟩
    change M + m' < invariantMass P
    linarith

/-- The exchange of the intermediate mass and the total momentum. -/
theorem lintegral_mass_region_swap {S m' : ℝ} (hS : 0 ≤ S) (hm' : 0 ≤ m')
    {J : ℝ × MinkowskiModel 3 → ℝ≥0∞} (hJ : Measurable J) :
    ∫⁻ M in Ioi S, ENNReal.ofReal M * ∫⁻ P in region 3 M m', J (M, P) =
      ∫⁻ P in massRegion (S + m'), ∫⁻ M, window S m' P M * J (M, P) := by
  set A := {z : ℝ × MinkowskiModel 3 | S < z.1 ∧ z.2 ∈ region 3 z.1 m'} with hA
  have hAm : MeasurableSet A := by
    have hI : Measurable fun z : ℝ × MinkowskiModel 3 => intervalQuadratic z.2 := by
      have h0 := (pair.continuous₂.comp (continuous_id.prodMk continuous_id)).measurable.comp
        (measurable_snd : Measurable fun z : ℝ × MinkowskiModel 3 => z.2)
      exact h0
    have ht : Measurable fun z : ℝ × MinkowskiModel 3 => time z.2 := by
      have h0 := time.continuous.measurable.comp
        (measurable_snd : Measurable fun z : ℝ × MinkowskiModel 3 => z.2)
      exact h0
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const ht).inter
        (measurableSet_lt ((measurable_fst.add_const m').pow_const 2) hI))
  set F : ℝ × MinkowskiModel 3 → ℝ≥0∞ := A.indicator fun z => ENNReal.ofReal z.1 * J z with hF
  have hFm : Measurable F :=
    ((ENNReal.measurable_ofReal.comp measurable_fst).mul hJ).indicator hAm
  have hL : ∀ M : ℝ, (Ioi S).indicator (fun M => ENNReal.ofReal M *
      ∫⁻ P in region 3 M m', J (M, P)) M = ∫⁻ P, F (M, P) := by
    intro M
    by_cases hM : M ∈ Ioi S
    · rw [indicator_of_mem hM, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_indicator measurableSet_region]
      refine lintegral_congr fun P => ?_
      by_cases hP : P ∈ region 3 M m'
      · rw [indicator_of_mem hP, hF, indicator_of_mem (show (M, P) ∈ A from ⟨hM, hP⟩)]
      · rw [indicator_of_notMem hP, hF, indicator_of_notMem (fun h : (M, P) ∈ A => hP h.2)]
    · rw [indicator_of_notMem hM]
      symm
      refine (lintegral_congr fun P => ?_).trans lintegral_zero
      rw [hF, indicator_of_notMem (fun h : (M, P) ∈ A => hM h.1)]
  have hR : ∀ P : MinkowskiModel 3, (massRegion (S + m')).indicator
      (fun P => ∫⁻ M, window S m' P M * J (M, P)) P = ∫⁻ M, F (M, P) := by
    intro P
    by_cases hP : P ∈ massRegion (S + m')
    · rw [indicator_of_mem hP]
      refine lintegral_congr fun M => ?_
      by_cases hw : S < M ∧ M < invariantMass P - m'
      · rw [window_of_mem hw, hF,
          indicator_of_mem (show (M, P) ∈ A from
            ⟨hw.1, (mem_region_iff hS hm' hw.1 hP.1).mpr hw.2⟩)]
      · rw [window_of_notMem hw, zero_mul, hF, indicator_of_notMem]
        intro h
        exact hw ⟨h.1, (mem_region_iff hS hm' h.1 hP.1).mp h.2⟩
    · rw [indicator_of_notMem hP]
      symm
      refine (lintegral_congr fun M => ?_).trans lintegral_zero
      rw [hF, indicator_of_notMem (fun h : (M, P) ∈ A =>
        hP (mem_massRegion_of_mem_region hS hm' h.1 h.2))]
  rw [← lintegral_indicator measurableSet_Ioi, lintegral_congr hL,
    ← lintegral_indicator (measurableSet_massRegion _), lintegral_congr hR]
  exact lintegral_lintegral_swap hFm.aemeasurable

/-- The integral against the two-body measure of the fibre is measurable in the first mass and
the total momentum. -/
theorem measurable_lintegral_fibreMeasure (m' : ℝ)
    {G : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) → ℝ≥0∞} (hG : Measurable G) :
    Measurable fun z : ℝ × MinkowskiModel 3 => ∫⁻ y, G (z.1, y) ∂(fibreMeasure z.1 m' z.2) := by
  have h1 : (fun z : ℝ × MinkowskiModel 3 => ∫⁻ y, G (z.1, y) ∂(fibreMeasure z.1 m' z.2)) =
      fun z => fibreWeight z.1 m' z.2 *
        ∫⁻ n, G (z.1, fibrePair z.1 m' z.2 n) ∂Sphere.sphereMeasure := by
    funext z
    exact lintegral_fibreMeasure' z.2
      (hG.comp (measurable_prodMk_left : Measurable fun y => (z.1, y)))
  rw [h1]
  have h2 : Measurable fun w : (ℝ × MinkowskiModel 3) × sphere (0 : E3) 1 =>
      G (w.1.1, fibrePair w.1.1 m' w.1.2 w.2) := by
    have h0 := hG.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fibrePair_mass m'))
    exact h0
  exact (measurable_fibreWeight_mass m').mul h2.lintegral_prod_right'

/-- **The integration formula for `k + 2` particles**: for every measurable `f ≥ 0`,
`∫ f d(μ₀ ⊗ ⋯ ⊗ μ_{k+1}) = ∫_{M_P > Σ m} (∫ f dν^{(k)}_P) d⁴P`. -/
theorem lintegral_shellProd (hm : ∀ i, 0 ≤ m i) :
    ∀ (k : ℕ) {f : Config k → ℝ≥0∞}, Measurable f →
      ∫⁻ x, f x ∂(shellProd m k) =
        ∫⁻ P in massRegion (massSum m k), ∫⁻ x, f x ∂(manyMeasure m k P)
  | 0, f, hf => by
    change ∫⁻ x, f x ∂((FutureShell.measure 3 (m 0)).prod (FutureShell.measure 3 (m 1))) = _
    rw [massSum_zero, ← region_eq_massRegion]
    simp_rw [manyMeasure_zero]
    exact lintegral_prod_eq (hm 0) (hm 1) hf
  | k + 1, f, hf => by
    have hS := massSum_nonneg m hm k
    have hm' := hm (k + 2)
    change ∫⁻ z, f z ∂((shellProd m k).prod (FutureShell.measure 3 (m (k + 2)))) = _
    have hf' : Measurable (Function.uncurry fun (x : Config k) (y : Fin 3 → ℝ) =>
        f ((x, y) : Config k × (Fin 3 → ℝ))) := hf
    rw [lintegral_prod _ hf.aemeasurable, lintegral_lintegral_swap hf'.aemeasurable]
    set H : (Fin 3 → ℝ) × MinkowskiModel 3 → ℝ≥0∞ := fun z =>
      ∫⁻ x, f ((x, z.1) : Config k × (Fin 3 → ℝ)) ∂(manyMeasure m k z.2) with hHdef
    have hH : Measurable H := by
      have hF0 := hf.comp ((measurable_snd : Measurable fun z : ((Fin 3 → ℝ) ×
        MinkowskiModel 3) × Config k => z.2).prodMk (measurable_fst.comp measurable_fst))
      have hF : Measurable fun z : ((Fin 3 → ℝ) × MinkowskiModel 3) × Config k =>
          f ((z.2, z.1.1) : Config k × (Fin 3 → ℝ)) := hF0
      exact measurable_lintegral_manyMeasure m k hF measurable_snd
    have h1 : ∀ π : Fin 3 → ℝ, ∫⁻ x, f ((x, π) : Config k × (Fin 3 → ℝ)) ∂(shellProd m k) =
        ∫⁻ Q in massRegion (massSum m k), H (π, Q) := fun π =>
      lintegral_shellProd hm k (hf.comp (measurable_prodMk_right :
        Measurable fun x : Config k => ((x, π) : Config k × (Fin 3 → ℝ))))
    rw [lintegral_congr h1, lintegral_shell_foliation hS (m (k + 2)) hH]
    have hG : ∀ M : ℝ, Measurable fun y : (Fin 3 → ℝ) × (Fin 3 → ℝ) => H (y.2, point M y.1) :=
      fun M => measurable_lintegral_point m k hf M
    rw [setLIntegral_congr_fun measurableSet_Ioi fun M hM => by
      rw [lintegral_prod_eq (lt_of_le_of_lt hS hM).le hm' (hG M)]]
    have hJ : Measurable fun z : ℝ × MinkowskiModel 3 =>
        ∫⁻ y, H (y.2, point z.1 y.1) ∂(fibreMeasure z.1 (m (k + 2)) z.2) := by
      have hG2 : Measurable fun w : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
          H (w.2.2, point w.1 w.2.1) := by
        have h0 := hH.comp ((measurable_snd.comp measurable_snd).prodMk
          (measurable_point_mass.comp (measurable_fst.prodMk
            (measurable_fst.comp measurable_snd))))
        exact h0
      exact measurable_lintegral_fibreMeasure (m (k + 2)) hG2
    rw [lintegral_mass_region_swap hS hm' hJ, massSum_succ]
    refine setLIntegral_congr_fun (measurableSet_massRegion _) fun P _ => ?_
    rw [lintegral_manyMeasure_succ m k P hf]

/-- The measures of the final states form a measurable family in the total momentum. -/
theorem measurable_manyMeasure (k : ℕ) : Measurable (manyMeasure m k) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have hS1 : Measurable (S.indicator (1 : Config k → ℝ≥0∞)) := measurable_one.indicator hS
  have hF : Measurable fun z : MinkowskiModel 3 × Config k =>
      S.indicator (1 : Config k → ℝ≥0∞) z.2 := by
    have h0 := hS1.comp (measurable_snd : Measurable fun z : MinkowskiModel 3 × Config k => z.2)
    exact h0
  have h := measurable_lintegral_manyMeasure m k hF measurable_id
  have h1 : (fun P : MinkowskiModel 3 => manyMeasure m k P S) =
      fun P => ∫⁻ x, S.indicator (1 : Config k → ℝ≥0∞) x ∂(manyMeasure m k (id P)) := by
    funext P
    exact (lintegral_indicator_one hS).symm
  rw [h1]
  exact h

/-- **The disintegration** of the product of the shell measures of `k + 2` particles over the
total momentum. -/
theorem shellProd_eq_bind (hm : ∀ i, 0 ≤ m i) (k : ℕ) :
    shellProd m k = (volume.restrict (massRegion (massSum m k))).bind (manyMeasure m k) := by
  ext S hS
  have hS1 : Measurable (S.indicator (1 : Config k → ℝ≥0∞)) := measurable_one.indicator hS
  rw [Measure.bind_apply hS (measurable_manyMeasure m k).aemeasurable,
    ← lintegral_indicator_one hS, lintegral_shellProd m hm k hS1]
  exact setLIntegral_congr_fun (measurableSet_massRegion _) fun P _ =>
    lintegral_indicator_one hS

/-! ### Covariance -/

/-- An orthochronous Lorentz transformation acting on the space momenta of all particles. -/
def act (L : orthochronousLorentzGroup 3) : (k : ℕ) → Config k → Config k
  | 0 => Prod.map (action (m 0) L) (action (m 1) L)
  | k + 1 => Prod.map (act L k) (action (m (k + 2)) L)

theorem measurable_act (L : orthochronousLorentzGroup 3) : ∀ k : ℕ, Measurable (act m L k)
  | 0 => ((continuous_action L).prodMap (continuous_action L)).measurable
  | k + 1 => (measurable_act L k).prodMap (continuous_action L).measurable

theorem window_lorentz (S m' : ℝ) (L : orthochronousLorentzGroup 3) (P : MinkowskiModel 3)
    (M : ℝ) : window S m' (L.val.val P) M = window S m' P M := by
  by_cases h : S < M ∧ M < invariantMass P - m'
  · rw [window_of_mem h, window_of_mem (by rw [invariantMass_lorentz']; exact h)]
  · rw [window_of_notMem h, window_of_notMem (by rw [invariantMass_lorentz']; exact h)]

/-- Covariance at the level of integrals. -/
theorem lintegral_comp_act (hm : ∀ i, 0 ≤ m i) (L : orthochronousLorentzGroup 3) :
    ∀ (k : ℕ) {P : MinkowskiModel 3}, P ∈ massRegion (massSum m k) →
      ∀ {f : Config k → ℝ≥0∞}, Measurable f →
        ∫⁻ x, f (act m L k x) ∂(manyMeasure m k P) =
          ∫⁻ x, f x ∂(manyMeasure m k (L.val.val P))
  | 0, P, hP, f, hf => by
    have hP' : P ∈ region 3 (m 0) (m 1) := by
      rw [region_eq_massRegion, ← massSum_zero]
      exact hP
    rw [manyMeasure_zero, manyMeasure_zero, ← map_fibreMeasure (hm 0) (hm 1) hP' L]
    exact (lintegral_map hf (measurable_act m L 0)).symm
  | k + 1, P, hP, f, hf => by
    have hS := massSum_nonneg m hm k
    have hm' := hm (k + 2)
    have hfa : Measurable fun x : Config (k + 1) => f (act m L (k + 1) x) :=
      hf.comp (measurable_act m L (k + 1))
    rw [lintegral_manyMeasure_succ m k P hfa, lintegral_manyMeasure_succ m k (L.val.val P) hf]
    refine lintegral_congr fun M => ?_
    rw [window_lorentz]
    by_cases hw : massSum m k < M ∧ M < invariantMass P - m (k + 2)
    · congr 1
      have hM : 0 < M := lt_of_le_of_lt hS hw.1
      have hPt : 0 < time P := by
        have h := hP.1
        exact h
      have hPr : P ∈ region 3 M (m (k + 2)) := (mem_region_iff hS hm' hw.1 hPt).mpr hw.2
      have hφ : Measurable (Prod.map (action M L) (action (m (k + 2)) L)) :=
        ((continuous_action L).prodMap (continuous_action L)).measurable
      rw [← map_fibreMeasure hM.le hm' hPr L,
        lintegral_map (measurable_lintegral_point m k hf M) hφ]
      refine lintegral_congr fun y => ?_
      have hQ : point M y.1 ∈ massRegion (massSum m k) := point_mem_massRegion hS hw.1 y.1
      have hdom : y.1 ∈ domain 3 M := by
        rw [domain_eq_univ hM.ne']
        exact mem_univ _
      have hpt : point M (action M L y.1) = L.val.val (point M y.1) := point_action L hdom
      have hfy : Measurable fun x : Config k =>
          f ((x, action (m (k + 2)) L y.2) : Config k × (Fin 3 → ℝ)) := by
        have h0 := hf.comp (measurable_prodMk_right : Measurable fun x : Config k =>
          ((x, action (m (k + 2)) L y.2) : Config k × (Fin 3 → ℝ)))
        exact h0
      change ∫⁻ x, f ((act m L k x, action (m (k + 2)) L y.2) : Config k × (Fin 3 → ℝ))
          ∂(manyMeasure m k (point M y.1)) =
        ∫⁻ x, f ((x, action (m (k + 2)) L y.2) : Config k × (Fin 3 → ℝ))
          ∂(manyMeasure m k (point M (action M L y.1)))
      rw [hpt]
      exact lintegral_comp_act hm L k hQ hfy
    · rw [window_of_notMem hw, zero_mul, zero_mul]

/-- **Covariance**: an orthochronous Lorentz transformation maps the measure of the final states
at `P` to the measure of the final states at `LP`. -/
theorem map_manyMeasure (hm : ∀ i, 0 ≤ m i) (k : ℕ) {P : MinkowskiModel 3}
    (hP : P ∈ massRegion (massSum m k)) (L : orthochronousLorentzGroup 3) :
    Measure.map (act m L k) (manyMeasure m k P) = manyMeasure m k (L.val.val P) := by
  ext S hS
  have hS1 : Measurable (S.indicator (1 : Config k → ℝ≥0∞)) := measurable_one.indicator hS
  rw [Measure.map_apply (measurable_act m L k) hS,
    ← lintegral_indicator_one (hS.preimage (measurable_act m L k)), ← lintegral_indicator_one hS,
    ← lintegral_comp_act m hm L k hP hS1]
  rfl

/-! ### An instance with three particles -/

theorem invariantMass_rest : invariantMass (Fin.cons 4 0 : MinkowskiModel 3) = 4 := by
  rw [invariantMass, properSpeed, FreeParticle.intervalQuadratic_cons]
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, sub_zero]
  rw [show (4 : ℝ) ^ 2 = 4 ^ 2 from rfl, Real.sqrt_sq (by norm_num)]

/-- **An instance**: three particles of mass `1` at the total momentum `(4, 0)`, which is in the
region `M_P > 3`, have a nonzero measure of the final states. -/
theorem manyMeasure_one_pos :
    (Fin.cons 4 0 : MinkowskiModel 3) ∈ massRegion (massSum (fun _ => 1) 1) ∧
      0 < manyMeasure (fun _ => 1) 1 (Fin.cons 4 0) univ := by
  set m₁ : ℕ → ℝ := fun _ => 1 with hm₁
  set P : MinkowskiModel 3 := Fin.cons 4 0 with hPdef
  have hsum0 : massSum m₁ 0 = 2 := by
    rw [massSum_zero]
    norm_num [hm₁]
  have hsum1 : massSum m₁ 1 = 3 := by
    rw [massSum_succ, hsum0]
    norm_num [hm₁]
  have hMP : invariantMass P = 4 := invariantMass_rest
  have htime : 0 < time P := by
    rw [hPdef]
    norm_num
  have hQP : intervalQuadratic P = 16 := by
    rw [hPdef, FreeParticle.intervalQuadratic_cons]
    norm_num
  refine ⟨⟨htime, by rw [hsum1, hQP]; norm_num⟩, ?_⟩
  have h1 : Measurable (fun _ : Config 1 => (1 : ℝ≥0∞)) := measurable_const
  rw [← lintegral_one, lintegral_manyMeasure_succ m₁ 0 P h1]
  -- the inner integrals as a function of the intermediate mass
  have hG : Measurable fun w : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      ∫⁻ _x : Config 0, (1 : ℝ≥0∞) ∂(manyMeasure m₁ 0 (point w.1 w.2.1)) := by
    have hg0 := measurable_point_mass.comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd) : Measurable fun w : ℝ × ((Fin 3 → ℝ) ×
        (Fin 3 → ℝ)) => (w.1, w.2.1))
    have hg : Measurable fun w : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => point w.1 w.2.1 := hg0
    exact measurable_lintegral_manyMeasure m₁ 0
      (measurable_const : Measurable fun _ : (ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ))) × Config 0 =>
        (1 : ℝ≥0∞)) hg
  have hJ0 := (measurable_lintegral_fibreMeasure (m₁ (0 + 2)) hG).comp
    (measurable_id.prodMk measurable_const : Measurable fun M : ℝ => (M, P))
  have hJ : Measurable fun M : ℝ => ∫⁻ y, (∫⁻ _x : Config 0, (1 : ℝ≥0∞)
      ∂(manyMeasure m₁ 0 (point M y.1))) ∂(fibreMeasure M (m₁ (0 + 2)) P) := hJ0
  have hw0 := (measurable_window (massSum m₁ 0) (m₁ (0 + 2))).comp
    ((measurable_const : Measurable fun _ : ℝ => P).prodMk measurable_id)
  have hw : Measurable fun M : ℝ => window (massSum m₁ 0) (m₁ (0 + 2)) P M := hw0
  have hg : Measurable fun M : ℝ => window (massSum m₁ 0) (m₁ (0 + 2)) P M *
      ∫⁻ y, (∫⁻ _x : Config 0, (1 : ℝ≥0∞) ∂(manyMeasure m₁ 0 (point M y.1)))
        ∂(fibreMeasure M (m₁ (0 + 2)) P) := by
    have h0 := hw.mul hJ
    exact h0
  rw [lintegral_pos_iff_support hg]
  have hsub : Ioo (2 : ℝ) 3 ⊆ Function.support (fun M : ℝ =>
      window (massSum m₁ 0) (m₁ (0 + 2)) P M * ∫⁻ y, (∫⁻ _x : Config 0, (1 : ℝ≥0∞)
        ∂(manyMeasure m₁ 0 (point M y.1))) ∂(fibreMeasure M (m₁ (0 + 2)) P)) := by
    intro M hM
    have hM2 : (2 : ℝ) < M := hM.1
    have hM3 : M < 3 := hM.2
    have hMpos : 0 < M := by linarith
    have hm2 : m₁ (0 + 2) = 1 := rfl
    have hwin : window (massSum m₁ 0) (m₁ (0 + 2)) P M = ENNReal.ofReal M :=
      window_of_mem ⟨by rw [hsum0]; exact hM2, by rw [hMP, hm2]; linarith⟩
    have hinner : ∀ y : (Fin 3 → ℝ) × (Fin 3 → ℝ),
        ∫⁻ _x : Config 0, (1 : ℝ≥0∞) ∂(manyMeasure m₁ 0 (point M y.1)) =
          ENNReal.ofReal (4 * Real.pi * restMomentum 1 1 M / M) := by
      intro y
      have hreg : point M y.1 ∈ region 3 (m₁ 0) (m₁ 1) := by
        rw [region_eq_massRegion, ← massSum_zero]
        exact point_mem_massRegion (by rw [hsum0]; norm_num) (by rw [hsum0]; exact hM2) y.1
      have h3 := fibreMeasure_univ (m₃ := m₁ 0) (m₄ := m₁ 1) (by norm_num [hm₁])
        (by norm_num [hm₁]) hreg
      rw [invariantMass_point hMpos] at h3
      rw [lintegral_one]
      exact (congrArg (fun μ : Measure (Config 0) => μ univ)
        (manyMeasure_zero m₁ (point M y.1))).trans h3
    have hPr : P ∈ region 3 M (m₁ (0 + 2)) := by
      refine ⟨htime, ?_⟩
      rw [hQP, hm2]
      nlinarith
    rw [Function.mem_support, hwin, lintegral_congr hinner, lintegral_const,
      fibreMeasure_univ hMpos.le (by norm_num [hm₁]) hPr, hMP]
    have hq1 : 0 < restMomentum 1 1 M := restMomentum_pos (by norm_num) (by norm_num)
      (by linarith)
    have hq2 : 0 < restMomentum M (m₁ (0 + 2)) 4 := restMomentum_pos hMpos.le
      (by norm_num [hm₁]) (by rw [hm2]; linarith)
    refine mul_ne_zero (ENNReal.ofReal_pos.mpr hMpos).ne' (mul_ne_zero ?_ ?_)
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  calc (0 : ℝ≥0∞) < volume (Ioo (2 : ℝ) 3) := by
        rw [Real.volume_Ioo]
        norm_num
    _ ≤ _ := measure_mono hsub

/-! ### The support of the measure -/

/-- The total momentum `Σ pᵢ` of the particles, with the momenta on the shells. -/
def totalMomentum : (k : ℕ) → Config k → MinkowskiModel 3
  | 0 => fun x => total (m 0) (m 1) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ))
  | k + 1 => fun x => totalMomentum k (x : Config k × (Fin 3 → ℝ)).1 +
      point (m (k + 2)) (x : Config k × (Fin 3 → ℝ)).2

theorem measurable_totalMomentum : ∀ k : ℕ, Measurable (totalMomentum m k)
  | 0 => by
    have h := continuous_total (d := 3) (m₃ := m 0) (m₄ := m 1)
    exact h.measurable
  | k + 1 => by
    have h1 := (measurable_totalMomentum k).comp
      (measurable_fst : Measurable fun x : Config k × (Fin 3 → ℝ) => x.1)
    have h2 := (continuous_point (d := 3) (m := m (k + 2))).measurable.comp
      (measurable_snd : Measurable fun x : Config k × (Fin 3 → ℝ) => x.2)
    have h := h1.add h2
    exact h

/-- **The support**: the measure of the final states at a regular `P` is carried by the
configurations with the total momentum `P`. -/
theorem manyMeasure_totalMomentum_ne (hm : ∀ i, 0 ≤ m i) :
    ∀ (k : ℕ) {P : MinkowskiModel 3}, P ∈ massRegion (massSum m k) →
      manyMeasure m k P {x | totalMomentum m k x ≠ P} = 0
  | 0, P, hP => by
    have hP' : P ∈ region 3 (m 0) (m 1) := by
      rw [region_eq_massRegion, ← massSum_zero]
      exact hP
    have h0 : manyMeasure m 0 P (fibre (m 0) (m 1) P)ᶜ = 0 :=
      (congrArg (fun μ : Measure (Config 0) => μ (fibre (m 0) (m 1) P)ᶜ)
        (manyMeasure_zero m P)).trans (fibreMeasure_compl_fibre (hm 0) (hm 1) hP')
    refine measure_mono_null (fun x hx => ?_) h0
    intro hfib
    exact hx hfib.2.2
  | k + 1, P, hP => by
    have hS := massSum_nonneg m hm k
    have hm' := hm (k + 2)
    have hmeas : MeasurableSet {x : Config (k + 1) | totalMomentum m (k + 1) x ≠ P} :=
      (measurableSet_eq_fun (measurable_totalMomentum m (k + 1)) measurable_const).compl
    have h1 : Measurable ({x : Config (k + 1) | totalMomentum m (k + 1) x ≠ P}.indicator
      (1 : Config (k + 1) → ℝ≥0∞)) := measurable_one.indicator hmeas
    rw [← lintegral_indicator_one hmeas, lintegral_manyMeasure_succ m k P h1]
    refine (lintegral_congr fun M => ?_).trans lintegral_zero
    by_cases hw : massSum m k < M ∧ M < invariantMass P - m (k + 2)
    · have hM : 0 < M := lt_of_le_of_lt hS hw.1
      have hPr : P ∈ region 3 M (m (k + 2)) := (mem_region_iff hS hm' hw.1 hP.1).mpr hw.2
      have hfib : ∀ᵐ y ∂(fibreMeasure M (m (k + 2)) P), y ∈ fibre M (m (k + 2)) P :=
        ae_iff.mpr (fibreMeasure_compl_fibre hM.le hm' hPr)
      have hzero : ∫⁻ y, (∫⁻ x, {x : Config (k + 1) | totalMomentum m (k + 1) x ≠ P}.indicator 1
          ((x, y.2) : Config k × (Fin 3 → ℝ)) ∂(manyMeasure m k (point M y.1)))
            ∂(fibreMeasure M (m (k + 2)) P) = 0 := by
        refine (lintegral_congr_ae (hfib.mono fun y hy => ?_)).trans lintegral_zero
        have hQ := point_mem_massRegion hS hw.1 y.1
        have hIH : ∀ᵐ x ∂(manyMeasure m k (point M y.1)),
            ¬(totalMomentum m k x ≠ point M y.1) :=
          ae_iff.mpr (by simpa using manyMeasure_totalMomentum_ne hm k hQ)
        refine (lintegral_congr_ae (hIH.mono fun x hx => ?_)).trans lintegral_zero
        have hnot : ((x, y.2) : Config k × (Fin 3 → ℝ)) ∉
            {x : Config (k + 1) | totalMomentum m (k + 1) x ≠ P} := by
          intro h
          apply h
          change totalMomentum m k x + point (m (k + 2)) y.2 = P
          rw [not_not.mp hx]
          exact hy.2.2
        exact indicator_of_notMem hnot _
      rw [hzero, mul_zero]
    · rw [window_of_notMem hw, zero_mul]

/-- The support, as an almost-everywhere statement. -/
theorem ae_totalMomentum_eq (hm : ∀ i, 0 ≤ m i) (k : ℕ) {P : MinkowskiModel 3}
    (hP : P ∈ massRegion (massSum m k)) :
    ∀ᵐ x ∂(manyMeasure m k P), totalMomentum m k x = P := by
  have h := manyMeasure_totalMomentum_ne m hm k hP
  exact ae_iff.mpr (by simpa using h)

/-! ### The total mass -/

theorem restMomentum_le_half {m₃ m₄ M : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) (h : m₃ + m₄ < M) :
    restMomentum m₃ m₄ M ≤ M / 2 := by
  have hM : 0 < M := by linarith
  have hq := restMomentum_pos hm₃ hm₄ h
  have hsq := restMomentum_sq hm₃ hm₄ h
  have hk : kallen (M ^ 2) (m₃ ^ 2) (m₄ ^ 2) ≤ M ^ 4 := by
    rw [kallen_sq]
    have h1 : 0 ≤ M ^ 2 - (m₃ + m₄) ^ 2 := by nlinarith
    have h2 : 0 ≤ M ^ 2 - (m₃ - m₄) ^ 2 := by nlinarith
    have h3 : M ^ 2 - (m₃ + m₄) ^ 2 ≤ M ^ 2 := by nlinarith
    have h4 : M ^ 2 - (m₃ - m₄) ^ 2 ≤ M ^ 2 := by nlinarith
    calc (M ^ 2 - (m₃ + m₄) ^ 2) * (M ^ 2 - (m₃ - m₄) ^ 2) ≤ M ^ 2 * M ^ 2 :=
          mul_le_mul h3 h4 h2 (sq_nonneg M)
      _ = M ^ 4 := by ring
  have hq2 : restMomentum m₃ m₄ M ^ 2 ≤ (M / 2) ^ 2 := by
    rw [hsq, div_pow]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  exact (pow_le_pow_iff_left₀ hq.le (by positivity) two_ne_zero).mp hq2

/-- The total mass `4πq/M` of a two-body measure is at most `2π`. -/
theorem fibreMeasure_univ_le {m₃ m₄ : ℝ} (hm₃ : 0 ≤ m₃) (hm₄ : 0 ≤ m₄) {P : MinkowskiModel 3}
    (hP : P ∈ region 3 m₃ m₄) : fibreMeasure m₃ m₄ P univ ≤ ENNReal.ofReal (2 * Real.pi) := by
  have hM := invariantMass_pos (futureTimelike_of_mem_region hP)
  have hq := restMomentum_le_half hm₃ hm₄ (add_lt_invariantMass hm₃ hm₄ hP)
  rw [fibreMeasure_univ hm₃ hm₄ hP]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ hM]
  nlinarith [Real.pi_pos]

/-- **The total mass is finite**: `ν^{(k)}_P(univ) ≤ (2π)^{k+1} M_P^{2k}` for a regular `P`. -/
theorem manyMeasure_univ_le (hm : ∀ i, 0 ≤ m i) :
    ∀ (k : ℕ) {P : MinkowskiModel 3}, P ∈ massRegion (massSum m k) →
      manyMeasure m k P univ ≤
        ENNReal.ofReal ((2 * Real.pi) ^ (k + 1) * invariantMass P ^ (2 * k))
  | 0, P, hP => by
    have hP' : P ∈ region 3 (m 0) (m 1) := by
      rw [region_eq_massRegion, ← massSum_zero]
      exact hP
    have h := fibreMeasure_univ_le (hm 0) (hm 1) hP'
    have h0 : manyMeasure m 0 P univ = fibreMeasure (m 0) (m 1) P univ :=
      congrArg (fun μ : Measure (Config 0) => μ univ) (manyMeasure_zero m P)
    rw [h0]
    simpa using h
  | k + 1, P, hP => by
    have hS := massSum_nonneg m hm k
    have hm' := hm (k + 2)
    have hMP : 0 ≤ invariantMass P := invariantMass_nonneg P
    set C : ℝ := (2 * Real.pi) ^ (k + 2) * invariantMass P ^ (2 * k + 1) with hC
    have h1 : Measurable (fun _ : Config (k + 1) => (1 : ℝ≥0∞)) := measurable_const
    rw [← lintegral_one, lintegral_manyMeasure_succ m k P h1]
    have hbound : ∀ M : ℝ, window (massSum m k) (m (k + 2)) P M *
        ∫⁻ y, (∫⁻ _x : Config k, (1 : ℝ≥0∞) ∂(manyMeasure m k (point M y.1)))
          ∂(fibreMeasure M (m (k + 2)) P) ≤
        (Ioo (massSum m k) (invariantMass P - m (k + 2))).indicator
          (fun _ => ENNReal.ofReal C) M := by
      intro M
      by_cases hw : massSum m k < M ∧ M < invariantMass P - m (k + 2)
      · have hM : 0 < M := lt_of_le_of_lt hS hw.1
        have hMle : M ≤ invariantMass P := by linarith [hw.2]
        have hPr : P ∈ region 3 M (m (k + 2)) := (mem_region_iff hS hm' hw.1 hP.1).mpr hw.2
        rw [window_of_mem hw, indicator_of_mem (show M ∈ Ioo (massSum m k)
          (invariantMass P - m (k + 2)) from hw)]
        have hin : ∀ y : (Fin 3 → ℝ) × (Fin 3 → ℝ),
            ∫⁻ _x : Config k, (1 : ℝ≥0∞) ∂(manyMeasure m k (point M y.1)) ≤
              ENNReal.ofReal ((2 * Real.pi) ^ (k + 1) * M ^ (2 * k)) := by
          intro y
          rw [lintegral_one]
          have := manyMeasure_univ_le hm k (point_mem_massRegion hS hw.1 y.1)
          rwa [invariantMass_point hM] at this
        calc ENNReal.ofReal M * ∫⁻ y, (∫⁻ _x : Config k, (1 : ℝ≥0∞)
              ∂(manyMeasure m k (point M y.1))) ∂(fibreMeasure M (m (k + 2)) P)
            ≤ ENNReal.ofReal M * (ENNReal.ofReal ((2 * Real.pi) ^ (k + 1) * M ^ (2 * k)) *
                ENNReal.ofReal (2 * Real.pi)) := by
              gcongr
              calc ∫⁻ y, (∫⁻ _x : Config k, (1 : ℝ≥0∞) ∂(manyMeasure m k (point M y.1)))
                    ∂(fibreMeasure M (m (k + 2)) P)
                  ≤ ∫⁻ _y, ENNReal.ofReal ((2 * Real.pi) ^ (k + 1) * M ^ (2 * k))
                    ∂(fibreMeasure M (m (k + 2)) P) := lintegral_mono hin
                _ = ENNReal.ofReal ((2 * Real.pi) ^ (k + 1) * M ^ (2 * k)) *
                    fibreMeasure M (m (k + 2)) P univ := lintegral_const _
                _ ≤ _ := by
                  gcongr
                  exact fibreMeasure_univ_le hM.le hm' hPr
          _ ≤ ENNReal.ofReal C := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hM.le]
              refine ENNReal.ofReal_le_ofReal ?_
              rw [hC]
              have hpow : M ^ (2 * k + 1) ≤ invariantMass P ^ (2 * k + 1) :=
                pow_le_pow_left₀ hM.le hMle _
              have hpi : 0 ≤ (2 * Real.pi) ^ (k + 2) := by positivity
              calc M * ((2 * Real.pi) ^ (k + 1) * M ^ (2 * k) * (2 * Real.pi))
                  = (2 * Real.pi) ^ (k + 2) * M ^ (2 * k + 1) := by ring
                _ ≤ (2 * Real.pi) ^ (k + 2) * invariantMass P ^ (2 * k + 1) :=
                    mul_le_mul_of_nonneg_left hpow hpi
      · rw [window_of_notMem hw, zero_mul]
        exact bot_le
    calc ∫⁻ M, window (massSum m k) (m (k + 2)) P M *
          ∫⁻ y, (∫⁻ _x : Config k, (1 : ℝ≥0∞) ∂(manyMeasure m k (point M y.1)))
            ∂(fibreMeasure M (m (k + 2)) P)
        ≤ ∫⁻ M, (Ioo (massSum m k) (invariantMass P - m (k + 2))).indicator
            (fun _ => ENNReal.ofReal C) M := lintegral_mono hbound
      _ = ENNReal.ofReal C * volume (Ioo (massSum m k) (invariantMass P - m (k + 2))) :=
          lintegral_indicator_const measurableSet_Ioo _
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (invariantMass P) := by
          gcongr
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal ((2 * Real.pi) ^ (k + 1 + 1) * invariantMass P ^ (2 * (k + 1))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hC]
          ring

theorem manyMeasure_univ_lt_top (hm : ∀ i, 0 ≤ m i) (k : ℕ) {P : MinkowskiModel 3}
    (hP : P ∈ massRegion (massSum m k)) : manyMeasure m k P univ < ∞ :=
  lt_of_le_of_lt (manyMeasure_univ_le m hm k hP) ENNReal.ofReal_lt_top

/-! ### The cross-section of `k + 2` outgoing particles -/

theorem act_inv_act (L : orthochronousLorentzGroup 3) :
    ∀ (k : ℕ) (x : Config k), act m L⁻¹ k (act m L k x) = x
  | 0, x => by
    change Prod.map (action (m 0) L⁻¹) (action (m 1) L⁻¹)
      (Prod.map (action (m 0) L) (action (m 1) L) (x : (Fin 3 → ℝ) × (Fin 3 → ℝ))) = x
    exact Prod.ext (action_inv_action' L _) (action_inv_action' L _)
  | k + 1, x => by
    change Prod.map (act m L⁻¹ k) (action (m (k + 2)) L⁻¹)
      (Prod.map (act m L k) (action (m (k + 2)) L) (x : Config k × (Fin 3 → ℝ))) = x
    exact Prod.ext (act_inv_act L k _) (action_inv_action' L _)

/-- A Lorentz transformation acts on the configurations by a measurable equivalence. -/
def actEquiv (L : orthochronousLorentzGroup 3) (k : ℕ) : Config k ≃ᵐ Config k where
  toFun := act m L k
  invFun := act m L⁻¹ k
  left_inv := act_inv_act m L k
  right_inv x := by simpa only [inv_inv] using act_inv_act m L⁻¹ k x
  measurable_toFun := measurable_act m L k
  measurable_invFun := measurable_act m L⁻¹ k

/-- The cross-section of a reaction `p₁ + p₂ → k + 2` particles: `(1/4F) ∫_S W dν_{p₁+p₂}`. -/
def manyCrossSection (k : ℕ) (W : Config k → ℝ) (p₁ p₂ : MinkowskiModel 3)
    (S : Set (Config k)) : ℝ :=
  crossSection (manyMeasure m k (p₁ + p₂)) W (fluxFactor p₁ p₂) S

/-- **The cross-section of `k + 2` outgoing particles is invariant** for a transition weight
that is a Lorentz scalar. -/
theorem manyCrossSection_covariant (hm : ∀ i, 0 ≤ m i) (k : ℕ) {p₁ p₂ : MinkowskiModel 3}
    (hP : p₁ + p₂ ∈ massRegion (massSum m k)) (L : orthochronousLorentzGroup 3)
    {W W' : Config k → ℝ} (hW : ∀ x, W' (act m L k x) = W x) (S : Set (Config k)) :
    manyCrossSection m k W' (L.val.val p₁) (L.val.val p₂) (act m L k '' S) =
      manyCrossSection m k W p₁ p₂ S := by
  rw [manyCrossSection, manyCrossSection, ← map_add, ← map_manyMeasure m hm k hP L,
    fluxFactor_lorentz]
  exact crossSection_map (actEquiv m L k).measurableEmbedding hW _ S

/-- **An instance with three outgoing particles**: two incoming particles of mass `√3` with
the momenta `(2, ±1, 0, 0)` and three outgoing particles of mass `1`. The flux factor is `4`,
the cross-section with the constant weight `1` is positive, and it is invariant under every
orthochronous Lorentz transformation. -/
theorem exists_manyCrossSection_pos :
    ∃ p₁ p₂ : MinkowskiModel 3, 0 < fluxFactor p₁ p₂ ∧
      p₁ + p₂ ∈ massRegion (massSum (fun _ => 1) 1) ∧
      0 < manyCrossSection (fun _ => 1) 1 (fun _ => 1) p₁ p₂ univ ∧
      ∀ L : orthochronousLorentzGroup 3,
        manyCrossSection (fun _ => 1) 1 (fun _ => 1) (L.val.val p₁) (L.val.val p₂)
            (act (fun _ => 1) L 1 '' univ) =
          manyCrossSection (fun _ => 1) 1 (fun _ => 1) p₁ p₂ univ := by
  set p₁ : MinkowskiModel 3 := Fin.cons 2 ![1, 0, 0] with hp₁
  set p₂ : MinkowskiModel 3 := Fin.cons 2 ![-1, 0, 0] with hp₂
  have hsum : p₁ + p₂ = (Fin.cons 4 0 : MinkowskiModel 3) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hp₁, hp₂]
      norm_num
    · simp only [Pi.add_apply, Fin.cons_succ, hp₁, hp₂, Pi.zero_apply]
      fin_cases j <;> simp
  have hpair : pair p₁ p₂ = 5 := by
    rw [hp₁, hp₂, pair_cons, Fin.sum_univ_three]
    norm_num
  have hQ₁ : intervalQuadratic p₁ = 3 := by
    rw [hp₁, FreeParticle.intervalQuadratic_cons, Fin.sum_univ_three]
    norm_num
  have hQ₂ : intervalQuadratic p₂ = 3 := by
    rw [hp₂, FreeParticle.intervalQuadratic_cons, Fin.sum_univ_three]
    norm_num
  have hF : fluxFactor p₁ p₂ = 4 := by
    rw [fluxFactor, hpair, hQ₁, hQ₂, show (5 : ℝ) ^ 2 - 3 * 3 = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  obtain ⟨hreg, hpos⟩ := manyMeasure_one_pos
  have hm₁ : ∀ i : ℕ, 0 ≤ (fun _ : ℕ => (1 : ℝ)) i := fun _ => zero_le_one
  have hfin := manyMeasure_univ_lt_top (fun _ => 1) hm₁ 1 hreg
  refine ⟨p₁, p₂, by rw [hF]; norm_num, by rw [hsum]; exact hreg, ?_, fun L =>
    manyCrossSection_covariant (fun _ => 1) hm₁ 1 (by rw [hsum]; exact hreg) L
      (fun _ => rfl) univ⟩
  rw [manyCrossSection, crossSection, hF, hsum, Measure.restrict_univ, integral_const,
    smul_eq_mul, mul_one, Measure.real]
  exact mul_pos (by norm_num) (ENNReal.toReal_pos hpos.ne' hfin.ne)

end ProjectAinos.SpecialRelativity.ManyBody
