/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.Kasner
public import ProjectAinos.GeneralRelativity.ProperTime
public import ProjectAinos.SmoothGeometry.Lorentzian.Kretschmann
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateGeodesic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Kasner singularity is a curvature singularity at finite proper time

Landau–Lifshitz, §§117, 119, with `c = 1` and the signature `(−+++)`. For a vacuum Kasner metric
`−dt² + Σ_α t^{2p_α} (dx^α)²` on `t > 0` (`Σp = Σp² = 1`):

* `curvatureOf_christoffel_eq`: the full table `riemann` of the curvature components of the flat
  anisotropic model; `kretschmann_metric`: **its Kretschmann scalar**
  `R_{abcd} R^{abcd} = 4 Σ_α (ä_α/a_α)² + 4 Σ_{α<β} H_α² H_β²`; `kretschmann_kasner`: for a vacuum
  Kasner metric `R_{abcd} R^{abcd} = −16 p₁p₂p₃/t⁴`, and `kasner_prod_neg`: `p₁p₂p₃ < 0` unless `p`
  is a permutation of `(1, 0, 0)`.
* `comovingPast`, `isGeodesicOn_comovingPast`, `curveVelocity_comovingPast`,
  `form_curveVelocity_comovingPast`, `properTime_comovingPast`: **the comoving past-directed unit
  timelike geodesic** `s ↦ x₀ − s e₀` from any point `x₀` reaches every slice `t > 0` after the
  proper time `x₀⁰ − t`, so its total proper time towards the past is `x₀⁰`, finite.
* `eventually_comovingPast_notMem`, `not_tendsto_comovingPast`: **it is inextendible in the
  space-time**: it leaves every compact subset and has no limit as its proper time tends to `x₀⁰`.
* `tendsto_kretschmann_comovingPast`: **the curvature diverges** along it, `R_{abcd}R^{abcd} → +∞`.
* `not_continuousAt_of_eq_kretschmann`: no function continuous at the co-ordinate limit point
  `(0, x₀¹, x₀², x₀³)` agrees with the Kretschmann scalar on `t > 0` near it;
  `not_tendsto_of_isometry`: **for every Lorentz manifold `N` and every smooth map of the Kasner
  space-time into `N` that preserves the metric, the image of the geodesic has no limit in `N`**:
  the Kretschmann scalar is invariant and continuous (`Kretschmann.lean`). So there is no `C^∞`
  extension of the space-time through the end of the geodesic, and none in which the curvature
  invariant is continuous at an end point.
* `riemann_kasner_flat`, `kretschmann_kasner_flat`, `exists_isometry_tendsto_flat`: the contrast:
  **the flat Kasner metric** `−dt² + t²(dx¹)² + (dx²)² + (dx³)²` (exponents `(1, 0, 0)`) has zero
  curvature, and the Milne map `(t cosh x¹, t sinh x¹, x², x³)` embeds it isometrically in
  Minkowski space, where the comoving line has an end point: its singularity at `t = 0` is one of
  the co-ordinates.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace Filter
open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity.Kasner

open SmoothGeometry CoordinateMetric LorentzMetric

local notation "E" => MinkowskiModel 3
local notation "I" => 𝓘(ℝ, MinkowskiModel 3)

variable {D : Data} {x : E}

/-! ### The curvature tensor of the anisotropic metric -/

variable (D) in
/-- `R^α_{0α0} = ä_α/a_α`, the relative acceleration of the axis `α`. -/
def curvTime (α : Fin 3) (x : E) : ℝ := accel D α (x 0)

variable (D) in
/-- `R^0_{α0α} = a_α ä_α`. -/
def curvSpace (α : Fin 3) (x : E) : ℝ := D.a α (x 0) * deriv (deriv (D.a α)) (x 0)

variable (D) in
/-- `R^α_{αββ} = H_α a_β ȧ_β` for `α ≠ β`. -/
def curvMixed (α β : Fin 3) (x : E) : ℝ := hubble D α (x 0) * gammaSpatial D β x

variable (D) in
/-- **The table of the curvature components** `R^l_{kij} = (R(∂_i, ∂_j)∂_k)^l` of the anisotropic
metric, indexed `riemann D x l i j k`: the nonzero components are
`R^α_{0α0} = −R^α_{00α} = ä_α/a_α`, `R^0_{α0α} = −R^0_{αα0} = a_α ä_α` and, for `α ≠ β`,
`R^α_{βαβ} = −R^α_{ββα} = H_α a_β ȧ_β`, up to the antisymmetry in the last pair. -/
def riemann (x : E) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![
    ![
      ![![0, 0, 0, 0],
        ![0, curvSpace D 0 x, 0, 0],
        ![0, 0, curvSpace D 1 x, 0],
        ![0, 0, 0, curvSpace D 2 x]],
      ![![0, -curvSpace D 0 x, 0, 0],
        ![0, 0, 0, 0],
        ![0, 0, 0, 0],
        ![0, 0, 0, 0]],
      ![![0, 0, -curvSpace D 1 x, 0],
        ![0, 0, 0, 0],
        ![0, 0, 0, 0],
        ![0, 0, 0, 0]],
      ![![0, 0, 0, -curvSpace D 2 x],
        ![0, 0, 0, 0],
        ![0, 0, 0, 0],
        ![0, 0, 0, 0]]],
    ![
      ![![0, 0, 0, 0],
        ![curvTime D 0 x, 0, 0, 0],
        ![0, 0, 0, 0],
        ![0, 0, 0, 0]],
      ![![-curvTime D 0 x, 0, 0, 0],
        ![0, 0, 0, 0],
        ![0, 0, curvMixed D 0 1 x, 0],
        ![0, 0, 0, curvMixed D 0 2 x]],
      ![![0, 0, 0, 0],
        ![0, 0, -curvMixed D 0 1 x, 0],
        ![0, 0, 0, 0],
        ![0, 0, 0, 0]],
      ![![0, 0, 0, 0],
        ![0, 0, 0, -curvMixed D 0 2 x],
        ![0, 0, 0, 0],
        ![0, 0, 0, 0]]],
    ![
      ![![0, 0, 0, 0],
        ![0, 0, 0, 0],
        ![curvTime D 1 x, 0, 0, 0],
        ![0, 0, 0, 0]],
      ![![0, 0, 0, 0],
        ![0, 0, 0, 0],
        ![0, -curvMixed D 1 0 x, 0, 0],
        ![0, 0, 0, 0]],
      ![![-curvTime D 1 x, 0, 0, 0],
        ![0, curvMixed D 1 0 x, 0, 0],
        ![0, 0, 0, 0],
        ![0, 0, 0, curvMixed D 1 2 x]],
      ![![0, 0, 0, 0],
        ![0, 0, 0, 0],
        ![0, 0, 0, -curvMixed D 1 2 x],
        ![0, 0, 0, 0]]],
    ![
      ![![0, 0, 0, 0],
        ![0, 0, 0, 0],
        ![0, 0, 0, 0],
        ![curvTime D 2 x, 0, 0, 0]],
      ![![0, 0, 0, 0],
        ![0, 0, 0, 0],
        ![0, 0, 0, 0],
        ![0, -curvMixed D 2 0 x, 0, 0]],
      ![![0, 0, 0, 0],
        ![0, 0, 0, 0],
        ![0, 0, 0, 0],
        ![0, 0, -curvMixed D 2 1 x, 0]],
      ![![-curvTime D 2 x, 0, 0, 0],
        ![0, curvMixed D 2 0 x, 0, 0],
        ![0, 0, curvMixed D 2 1 x, 0],
        ![0, 0, 0, 0]]]]

/-- **The curvature components of the anisotropic metric** are the table `riemann`. -/
theorem curvatureOf_christoffel_eq (hx : x ∈ domain D) (l i j k : Fin 4) :
    curvatureOf (christoffel D) x l i j k = riemann D x l i j k := by
  have h0 := (a_pos_of_mem hx 0).ne'
  have h1 := (a_pos_of_mem hx 1).ne'
  have h2 := (a_pos_of_mem hx 2).ne'
  fin_cases l <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
  · simp only [curvatureOf, SphericalAnsatz.sum_four, christoffel, riemann, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    simp only [fderiv_gammaSpatial hx, fderiv_gammaExpansion hx, fderiv_const_apply, zero_apply]
    simp [gammaSpatial, gammaExpansion, curvTime, curvSpace, curvMixed, hubble, accel]
    try field_simp
    try ring

variable (D) in
/-- **The Kretschmann scalar of the anisotropic metric**,
`R_{abcd} R^{abcd} = 4 Σ_α (ä_α/a_α)² + 4 (H₁²H₂² + H₁²H₃² + H₂²H₃²)`. -/
def kretschmannScalar (t : ℝ) : ℝ :=
  4 * ∑ α, accel D α t ^ 2 + 4 * (hubble D 0 t ^ 2 * hubble D 1 t ^ 2 +
    hubble D 0 t ^ 2 * hubble D 2 t ^ 2 + hubble D 1 t ^ 2 * hubble D 2 t ^ 2)

/-- **The Kretschmann scalar of the anisotropic metric** at a point of the domain is
`4 Σ_α (ä_α/a_α)² + 4 Σ_{α<β} H_α² H_β²` (`kretschmannScalar`). -/
theorem kretschmann_metric (y : domain D) :
    (metric D).toLorentzMetric.kretschmann y = kretschmannScalar D ((y : E) 0) := by
  have hy := y.2
  have h0 := (a_pos_of_mem hy 0).ne'
  have h1 := (a_pos_of_mem hy 1).ne'
  have h2 := (a_pos_of_mem hy 2).ne'
  rw [toLorentzMetric_kretschmann_of_table (metric D) y (eventually_christoffelOf_eq y.2),
    coefficient_metric_inv y.2]
  have hR : curvatureOf (christoffel D) (y : E) = riemann D y := by
    funext l i j k
    exact curvatureOf_christoffel_eq y.2 l i j k
  rw [hR]
  simp only [kretschmannContraction, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [SphericalAnsatz.sum_four, riemann, Fin.isValue, Matrix.cons_val]
  simp [curvTime, curvSpace, curvMixed, accel, hubble, gammaSpatial, kretschmannScalar,
    coefficients, Fin.sum_univ_three]
  field_simp
  ring

/-! ### The Kasner metrics -/

/-- **The Kretschmann scalar of a Kasner metric**:
`R_{abcd} R^{abcd} = (4 Σ_α p_α² (p_α − 1)² + 4 Σ_{α<β} p_α² p_β²)/t⁴`. -/
theorem kretschmannScalar_kasner (p : Fin 3 → ℝ) {t : ℝ} (ht : 0 < t) :
    kretschmannScalar (kasner p) t =
      (4 * ∑ α, p α ^ 2 * (p α - 1) ^ 2 +
        4 * (p 0 ^ 2 * p 1 ^ 2 + p 0 ^ 2 * p 2 ^ 2 + p 1 ^ 2 * p 2 ^ 2)) / t ^ 4 := by
  have ht' := ht.ne'
  simp only [kretschmannScalar, accel_kasner p _ ht, hubble_kasner p _ ht, Fin.sum_univ_three]
  field_simp

/-- **The Kretschmann scalar of a vacuum Kasner metric** is `−16 p₁p₂p₃/t⁴`. -/
theorem kretschmannScalar_kasner_of_vacuum {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1)
    (h2 : ∑ α, p α ^ 2 = 1) {t : ℝ} (ht : 0 < t) :
    kretschmannScalar (kasner p) t = -16 * (p 0 * p 1 * p 2) / t ^ 4 := by
  rw [kretschmannScalar_kasner p ht]
  rw [Fin.sum_univ_three] at h1 h2
  congr 1
  rw [Fin.sum_univ_three]
  linear_combination
    (-2 * p 0 ^ 3 - 4 * p 0 ^ 2 * p 1 + 2 * p 0 ^ 2 * p 2 - 4 * p 0 ^ 2 - 4 * p 0 * p 1 ^ 2 +
      2 * p 0 * p 1 * p 2 + 6 * p 0 * p 1 - 4 * p 0 * p 2 ^ 2 + 6 * p 0 * p 2 + 6 * p 0 -
      2 * p 1 ^ 3 + 2 * p 1 ^ 2 * p 2 - 4 * p 1 ^ 2 - 4 * p 1 * p 2 ^ 2 + 6 * p 1 * p 2 +
      6 * p 1 + 4 * p 2 ^ 3 - 4 * p 2 ^ 2) * h1 +
    (6 * p 0 ^ 2 + 6 * p 0 * p 1 - 6 * p 0 + 6 * p 1 ^ 2 - 6 * p 1) * h2

/-- **The product of the exponents of a curved vacuum Kasner metric is negative**: if
`Σp = Σp² = 1` and `p` is not a permutation of `(1, 0, 0)`, then `p₁p₂p₃ < 0`. With
`p₁p₂ + p₁p₃ + p₂p₃ = 0`, `p₁p₂p₃ = −p₃²(1 − p₃)`, and `0 < |p₃| < 1`. -/
theorem kasner_prod_neg {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hp : p ≠ ![1, 0, 0] ∧ p ≠ ![0, 1, 0] ∧ p ≠ ![0, 0, 1]) : p 0 * p 1 * p 2 < 0 := by
  have hpairs := kasner_pairs h1 h2
  obtain ⟨hc0, hc1⟩ := kasner_exponent_ne h1 h2 hp 2
  rw [Fin.sum_univ_three] at h1 h2
  have hprod : p 0 * p 1 * p 2 = -(p 2 ^ 2 * (1 - p 2)) := by
    have : p 0 * p 1 = -(p 2 * (p 0 + p 1)) := by linarith
    rw [this, show p 0 + p 1 = 1 - p 2 by linarith]
    ring
  have hle : p 2 ≤ 1 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
  have hlt : 0 < 1 - p 2 := sub_pos.mpr (lt_of_le_of_ne hle hc1)
  have hsq : 0 < p 2 ^ 2 := by positivity
  rw [hprod]
  nlinarith [mul_pos hsq hlt]

/-- **The Kretschmann scalar of a curved vacuum Kasner metric is positive and diverges as
`t → 0`**: `R_{abcd} R^{abcd} = 16 |p₁p₂p₃|/t⁴` at every point of the domain. -/
theorem kretschmann_kasner {p : Fin 3 → ℝ} (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (y : domain (kasner p)) :
    (metric (kasner p)).toLorentzMetric.kretschmann y = -16 * (p 0 * p 1 * p 2) / (y : E) 0 ^ 4 :=
  (kretschmann_metric y).trans (kretschmannScalar_kasner_of_vacuum h1 h2 (time_pos_kasner y.2))

/-! ### Flat Kasner space -/

/-- **The flat Kasner metric** `−dt² + t² (dx¹)² + (dx²)² + (dx³)²` (the exponents `(1, 0, 0)`, a
wedge of Minkowski space in Milne co-ordinates) **has zero curvature**: every curvature component
vanishes, and so does its Kretschmann scalar. -/
theorem riemann_kasner_flat (y : domain (kasner ![1, 0, 0])) (l i j k : Fin 4) :
    (metric (kasner ![1, 0, 0])).toLorentzMetric.chartCurvature (physicalChart y) y l i j k =
      0 := by
  have ht := time_pos_kasner y.2
  rw [toLorentzMetric_chartCurvature_eq_curvatureOf _ y y (eventually_christoffelOf_eq y.2),
    curvatureOf_christoffel_eq y.2]
  have hT (α : Fin 3) : curvTime (kasner ![1, 0, 0]) α y = 0 := by
    rw [curvTime, accel_kasner _ α ht]
    fin_cases α <;> simp
  have hS (α : Fin 3) : curvSpace (kasner ![1, 0, 0]) α y = 0 := by
    have ha := (a_pos_of_mem y.2 α).ne'
    have h := hT α
    rw [curvTime, accel, div_eq_zero_iff, or_iff_left ha] at h
    rw [curvSpace, h, mul_zero]
  have hM (α β : Fin 3) (hαβ : α ≠ β) : curvMixed (kasner ![1, 0, 0]) α β y = 0 := by
    rw [curvMixed, gammaSpatial, hubble_kasner _ α ht, (hasDerivAt_kasner _ β ht).deriv]
    fin_cases α <;> fin_cases β <;> simp_all
  fin_cases l <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [riemann, hT, hS, hM]

/-- The Kretschmann scalar of the flat Kasner metric vanishes. -/
theorem kretschmann_kasner_flat (y : domain (kasner ![1, 0, 0])) :
    (metric (kasner ![1, 0, 0])).toLorentzMetric.kretschmann y = 0 := by
  rw [kretschmann_chart _ (physicalChart_mem y) (by simp), kretschmannContraction]
  simp [riemann_kasner_flat]

/-! ### The comoving past-directed geodesic -/

/-- A point lies in the domain of a Kasner metric exactly when its time is positive. -/
theorem mem_domain_kasner {p : Fin 3 → ℝ} {z : E} : z ∈ domain (kasner p) ↔ 0 < z 0 := Iff.rfl

/-- The point `x₀ − s e₀` of the time line through `x₀`, at the proper time `s` towards the
past. -/
def comovingPoint (x₀ : E) (s : ℝ) : E := x₀ - s • Pi.single 0 1

@[simp] theorem comovingPoint_zero (x₀ : E) (s : ℝ) : comovingPoint x₀ s 0 = x₀ 0 - s := by
  simp [comovingPoint]

theorem hasDerivAt_comovingPoint (x₀ : E) (s : ℝ) :
    HasDerivAt (comovingPoint x₀) (-(Pi.single 0 1 : E)) s := by
  have h := ((hasDerivAt_id s).smul_const (Pi.single 0 1 : E)).const_sub x₀
  simp only [id, one_smul] at h
  exact h

variable {p : Fin 3 → ℝ} {x₀ : domain (kasner p)} {s : ℝ}

variable (p x₀) in
/-- **The comoving past-directed time line** of a Kasner model from a point `x₀` of the spacetime:
`s ↦ x₀ − s e₀` for `s < t₀ = x₀⁰`, along which the time `t₀ − s` decreases to `0`. Outside this
parameter interval it is `x₀`, a value that no statement uses. -/
def comovingPast (s : ℝ) : domain (kasner p) :=
  if hs : s < (x₀ : E) 0 then
    ⟨comovingPoint x₀ s, by rw [mem_domain_kasner, comovingPoint_zero]; linarith⟩
  else x₀

theorem comovingPast_val (hs : s < (x₀ : E) 0) :
    (comovingPast p x₀ s : E) = comovingPoint x₀ s := by
  simp [comovingPast, hs]

theorem comovingPast_eventuallyEq (hs : s < (x₀ : E) 0) :
    (fun s => (comovingPast p x₀ s : E)) =ᶠ[𝓝 s] comovingPoint x₀ :=
  eventually_of_mem (isOpen_Iio.mem_nhds hs) fun _ h => comovingPast_val h

/-- **The velocity of the comoving line is `−e₀`**: it is past-directed, its time decreases at
the unit rate. -/
theorem curveVelocity_comovingPast (hs : s < (x₀ : E) 0) :
    (curveVelocity (comovingPast p x₀) s : E) = -Pi.single 0 1 := by
  have hd : DifferentiableAt ℝ (fun s => (comovingPast p x₀ s : E)) s :=
    (hasDerivAt_comovingPoint (x₀ : E) s).differentiableAt.congr_of_eventuallyEq
      (comovingPast_eventuallyEq hs)
  rw [curveVelocity_val (mdifferentiableAt_iff_differentiableAt_val.mpr hd),
    (comovingPast_eventuallyEq hs).deriv_eq, (hasDerivAt_comovingPoint (x₀ : E) s).deriv]

/-- **The velocity is a unit timelike vector**: `g(γ̇, γ̇) = −1`. -/
theorem form_curveVelocity_comovingPast (hs : s < (x₀ : E) 0) :
    (metric (kasner p)).toLorentzMetric.form (comovingPast p x₀ s)
      (curveVelocity (comovingPast p x₀) s) (curveVelocity (comovingPast p x₀) s) = -1 := by
  rw [toLorentzMetric_form, curveVelocity_comovingPast hs]
  simp only [map_neg, neg_apply, neg_neg]
  have h := coefficient_metric (D := kasner p) (comovingPast p x₀ s)
  have h00 := congrFun (congrFun h 0) 0
  simpa [coefficient, coefficients] using h00

/-- **The comoving line is a geodesic** on the parameter interval `s < t₀`. -/
theorem isGeodesicOn_comovingPast :
    (metric (kasner p)).toLorentzMetric.IsGeodesicOn (Iio ((x₀ : E) 0)) (comovingPast p x₀) := by
  have hc : ContDiffOn ℝ 2 (fun s => (comovingPast p x₀ s : E)) (Iio ((x₀ : E) 0)) := by
    intro s hs
    have h : ContDiff ℝ 2 (comovingPoint (x₀ : E)) := by
      unfold comovingPoint
      fun_prop
    exact (h.contDiffAt.congr_of_eventuallyEq (comovingPast_eventuallyEq hs)).contDiffWithinAt
  rw [(metric (kasner p)).isGeodesicOn_iff isOpen_Iio hc]
  intro s hs k
  have hderiv : deriv (fun s => (comovingPast p x₀ s : E)) =ᶠ[𝓝 s] fun _ => -Pi.single 0 1 := by
    filter_upwards [isOpen_Iio.mem_nhds hs] with r hr
    rw [(comovingPast_eventuallyEq hr).deriv_eq, (hasDerivAt_comovingPoint (x₀ : E) r).deriv]
  rw [hderiv.deriv_eq, deriv_const, hderiv.self_of_nhds]
  have hz := (isSynchronous (D := kasner p)).christoffel_zero_zero (comovingPast p x₀ s).2 k
  simp [Pi.single_apply, hz]

/-- **The proper time along the comoving line is its parameter**: from `x₀` to the slice
`t = t₀ − s` it is `s`, so the line reaches every time `t > 0` and its total proper time towards the
past is `t₀`, finite. -/
theorem properTime_comovingPast (hs0 : 0 ≤ s) (hs : s < (x₀ : E) 0) :
    properTime (metric (kasner p)).toLorentzMetric (comovingPast p x₀) 0 s = s := by
  unfold properTime
  have h : ∀ t ∈ uIcc 0 s,
      speedAlong (metric (kasner p)).toLorentzMetric (comovingPast p x₀) t = 1 := by
    intro t ht
    rw [uIcc_of_le hs0] at ht
    rw [speedAlong, properSpeed, form_curveVelocity_comovingPast (by linarith [ht.2])]
    norm_num
  rw [intervalIntegral.integral_congr h]
  simp

/-- **The comoving line leaves every compact subset of the spacetime** as its proper time tends to
`t₀`: it has no endpoint in the spacetime. -/
theorem eventually_comovingPast_notMem {K : Set (domain (kasner p))} (hK : IsCompact K) :
    ∀ᶠ s in 𝓝[<] ((x₀ : E) 0), comovingPast p x₀ s ∉ K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact Eventually.of_forall fun _ h => h
  have hcont : Continuous fun y : domain (kasner p) => (y : E) 0 :=
    (continuous_apply 0).comp continuous_subtype_val
  obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  have hm : 0 < (y₀ : E) 0 := y₀.2
  filter_upwards [Ioo_mem_nhdsLT (show (x₀ : E) 0 - (y₀ : E) 0 < (x₀ : E) 0 by linarith)]
    with s hs hsK
  have h1 : (y₀ : E) 0 ≤ (comovingPast p x₀ s : E) 0 := hmin hsK
  rw [comovingPast_val hs.2, comovingPoint_zero] at h1
  linarith [hs.1]

/-- **The comoving line has no limit in the spacetime** as its proper time tends to `t₀`. -/
theorem not_tendsto_comovingPast (q : domain (kasner p)) :
    ¬ Tendsto (comovingPast p x₀) (𝓝[<] ((x₀ : E) 0)) (𝓝 q) := by
  intro h
  have h1 : Tendsto (fun s => (comovingPast p x₀ s : E) 0) (𝓝[<] ((x₀ : E) 0))
      (𝓝 ((q : E) 0)) :=
    ((continuous_apply 0).comp continuous_subtype_val).continuousAt.tendsto.comp h
  have h2 : Tendsto (fun s => (comovingPast p x₀ s : E) 0) (𝓝[<] ((x₀ : E) 0)) (𝓝 0) := by
    have h3 : Tendsto (fun s => (x₀ : E) 0 - s) (𝓝[<] ((x₀ : E) 0)) (𝓝 0) := by
      have h4 : Tendsto (fun s : ℝ => (x₀ : E) 0 - s) (𝓝 ((x₀ : E) 0))
          (𝓝 ((x₀ : E) 0 - (x₀ : E) 0)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at h4
      exact h4.mono_left nhdsWithin_le_nhds
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [comovingPast_val hs, comovingPoint_zero]
  have h5 := tendsto_nhds_unique h1 h2
  have h6 : 0 < (q : E) 0 := q.2
  linarith

/-- The co-ordinates of the comoving line tend to `x₀ − t₀ e₀ = (0, x₀¹, x₀², x₀³)`, a point of
the boundary `t = 0` of the domain in the co-ordinate space. -/
theorem tendsto_comovingPast_val :
    Tendsto (fun s => (comovingPast p x₀ s : E)) (𝓝[<] ((x₀ : E) 0))
      (𝓝 (comovingPoint x₀ ((x₀ : E) 0))) := by
  have h : Tendsto (comovingPoint (x₀ : E)) (𝓝[<] ((x₀ : E) 0))
      (𝓝 (comovingPoint x₀ ((x₀ : E) 0))) :=
    (hasDerivAt_comovingPoint (x₀ : E) _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (comovingPast_val hs).symm

/-! ### The curvature diverges along the comoving line -/

/-- **The Kretschmann scalar along the comoving line** is `−16 p₁p₂p₃/(t₀ − s)⁴`. -/
theorem kretschmann_comovingPast (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hs : s < (x₀ : E) 0) :
    (metric (kasner p)).toLorentzMetric.kretschmann (comovingPast p x₀ s) =
      -16 * (p 0 * p 1 * p 2) / ((x₀ : E) 0 - s) ^ 4 := by
  rw [kretschmann_kasner h1 h2, comovingPast_val hs, comovingPoint_zero]

/-- **The curvature diverges at the end of the comoving line** of a curved vacuum Kasner metric:
`R_{abcd} R^{abcd} → +∞` as the proper time tends to `t₀`. -/
theorem tendsto_kretschmann_comovingPast (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hp : p ≠ ![1, 0, 0] ∧ p ≠ ![0, 1, 0] ∧ p ≠ ![0, 0, 1]) :
    Tendsto (fun s => (metric (kasner p)).toLorentzMetric.kretschmann (comovingPast p x₀ s))
      (𝓝[<] ((x₀ : E) 0)) atTop := by
  set t₀ := (x₀ : E) 0
  have hc : 0 < -16 * (p 0 * p 1 * p 2) := by nlinarith [kasner_prod_neg h1 h2 hp]
  have hpow : Tendsto (fun s => (t₀ - s) ^ 4) (𝓝[<] t₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h3 : Tendsto (fun s : ℝ => (t₀ - s) ^ 4) (𝓝 t₀) (𝓝 ((t₀ - t₀) ^ 4)) :=
        (tendsto_const_nhds.sub tendsto_id).pow 4
      rw [sub_self, zero_pow (by norm_num)] at h3
      exact h3.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact pow_pos (sub_pos.mpr hs) 4
  have hlim := (tendsto_inv_nhdsGT_zero.comp hpow).const_mul_atTop hc
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [kretschmann_comovingPast h1 h2 hs, Function.comp_apply, div_eq_mul_inv]

/-- **No extension of the curvature invariant**: no function on the co-ordinate space that is
continuous at the limit point `(0, x₀¹, x₀², x₀³)` of the comoving line agrees with the
Kretschmann scalar on the part `t > 0` of a neighbourhood of that point: the metric has no
extension to a neighbourhood of the limit point with a continuous curvature invariant. (For a
`C²` metric there agreeing with the Kasner metric where `t > 0`, its Kretschmann scalar would be
such a function; the invariant statement, for every extension, is `not_tendsto_of_isometry`.) -/
theorem not_continuousAt_of_eq_kretschmann (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hp : p ≠ ![1, 0, 0] ∧ p ≠ ![0, 1, 0] ∧ p ≠ ![0, 0, 1]) (F : E → ℝ)
    (hF : ∀ᶠ z in 𝓝 (comovingPoint x₀ ((x₀ : E) 0)), ∀ hz : z ∈ domain (kasner p),
      F z = (metric (kasner p)).toLorentzMetric.kretschmann ⟨z, hz⟩) :
    ¬ ContinuousAt F (comovingPoint x₀ ((x₀ : E) 0)) := by
  intro hcont
  have hlim := hcont.tendsto.comp (tendsto_comovingPast_val (p := p) (x₀ := x₀))
  have hK := tendsto_kretschmann_comovingPast (x₀ := x₀) h1 h2 hp
  refine not_tendsto_nhds_of_tendsto_atTop hK (F (comovingPoint x₀ ((x₀ : E) 0))) ?_
  refine hlim.congr' ?_
  filter_upwards [tendsto_comovingPast_val.eventually hF] with s hs
  exact hs (comovingPast p x₀ s).2

/-- **The comoving line has no endpoint in any extension of the spacetime**: for every Lorentz
manifold `N` and every smooth map `f` from the curved vacuum Kasner spacetime into `N` whose
differential preserves the metric (an isometric immersion, in particular an embedding of the
spacetime as an open subset of a larger one), the image of the comoving line has no limit in `N`
as its proper time tends to `t₀`. The Kretschmann scalar of `N` is continuous, it agrees with that
of the Kasner metric along the image, and the latter diverges. -/
theorem not_tendsto_of_isometry (h1 : ∑ α, p α = 1) (h2 : ∑ α, p α ^ 2 = 1)
    (hp : p ≠ ![1, 0, 0] ∧ p ≠ ![0, 1, 0] ∧ p ≠ ![0, 0, 1]) {N : Type} [TopologicalSpace N]
    [ChartedSpace E N] [IsManifold I ∞ N] (h : LorentzMetric .timeNegative 3 N)
    {f : domain (kasner p) → N} (hf : ContMDiff I I ∞ f)
    (hmetric : ∀ y v w, (metric (kasner p)).toLorentzMetric.form y v w =
      h.form (f y) (mfderiv I I f y v) (mfderiv I I f y w)) (q : N) :
    ¬ Tendsto (fun s => f (comovingPast p x₀ s)) (𝓝[<] ((x₀ : E) 0)) (𝓝 q) := by
  intro hq
  have hK := (h.kretschmann_continuousAt q).tendsto.comp hq
  have hinf := tendsto_kretschmann_comovingPast (x₀ := x₀) h1 h2 hp
  refine not_tendsto_nhds_of_tendsto_atTop hinf (h.kretschmann q) ?_
  refine hK.congr fun s => ?_
  exact ((metric (kasner p)).toLorentzMetric.kretschmann_isometry h hf hmetric _).symm

/-! ### The flat Kasner metric extends: Milne co-ordinates -/

/-- **The Milne map** `(t, x¹, x², x³) ↦ (t cosh x¹, t sinh x¹, x², x³)`. -/
def milne (z : E) : E := ![z 0 * Real.cosh (z 1), z 0 * Real.sinh (z 1), z 2, z 3]

theorem contDiff_milne : ContDiff ℝ ∞ milne := by
  refine contDiff_pi.mpr fun i => ?_
  fin_cases i <;> simp only [milne] <;> simp <;> fun_prop

theorem fderiv_milne_apply (z v : E) :
    fderiv ℝ milne z v = ![Real.cosh (z 1) * v 0 + z 0 * Real.sinh (z 1) * v 1,
      Real.sinh (z 1) * v 0 + z 0 * Real.cosh (z 1) * v 1, v 2, v 3] := by
  have hd : HasFDerivAt milne (fderiv ℝ milne z) z :=
    (contDiff_milne.differentiable (by simp) z).hasFDerivAt
  have hc := hasFDerivAt_pi'.mp hd
  have hp (i : Fin 4) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i).hasFDerivAt (x := z)
  funext i
  have h1 := hc i
  fin_cases i
  · have h2 := (hp 0).mul ((Real.hasDerivAt_cosh (z 1)).comp_hasFDerivAt z (hp 1))
    have h3 := congrArg (fun L : E →L[ℝ] ℝ => L v) (h1.unique h2)
    simp at h3
    simp [h3]
    ring
  · have h2 := (hp 0).mul ((Real.hasDerivAt_sinh (z 1)).comp_hasFDerivAt z (hp 1))
    have h3 := congrArg (fun L : E →L[ℝ] ℝ => L v) (h1.unique h2)
    simp at h3
    simp [h3]
    ring
  · have h3 := congrArg (fun L : E →L[ℝ] ℝ => L v) (h1.unique (hp 2))
    simp at h3
    simp [h3]
  · have h3 := congrArg (fun L : E →L[ℝ] ℝ => L v) (h1.unique (hp 3))
    simp at h3
    simp [h3]

/-- The Milne map on the flat Kasner space-time. -/
def milneEmbedding (y : domain (kasner ![1, 0, 0])) : E := milne y

theorem contMDiff_milneEmbedding : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ milneEmbedding :=
  contDiff_milne.contMDiff.comp contMDiff_subtype_val

theorem mfderiv_milneEmbedding (y : domain (kasner ![1, 0, 0])) (v : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) milneEmbedding y v = fderiv ℝ milne y v := by
  have h1 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) milne (y : E) :=
    (contDiff_milne.contMDiff (y : E)).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (Subtype.val : domain (kasner ![1, 0, 0]) → E) y :=
    ((contMDiff_subtype_val (n := ∞)) y).mdifferentiableAt (by simp)
  have h := mfderiv_comp y h1 h2
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (milne ∘ Subtype.val) y v = _
  rw [h]
  erw [ContinuousLinearMap.comp_apply, Manifold.mfderiv_subtype_val_apply, mfderiv_eq_fderiv]
  rfl

/-- **The Milne map preserves the metric**: the flat Kasner metric is the pullback of the
Minkowski metric, `−dT² + dX² = −dt² + t² (dx¹)²` for `T = t cosh x¹`, `X = t sinh x¹`. -/
theorem form_milneEmbedding (y : domain (kasner ![1, 0, 0])) (v w : E) :
    (metric (kasner ![1, 0, 0])).toLorentzMetric.form y v w =
      (minkowskiMetric .timeNegative 3).form (milneEmbedding y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) milneEmbedding y v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) milneEmbedding y w) := by
  rw [mfderiv_milneEmbedding, mfderiv_milneEmbedding, fderiv_milne_apply, fderiv_milne_apply]
  change (metric (kasner ![1, 0, 0])).form y v w = minkowskiForm .timeNegative 3 _ _
  rw [form_apply, coefficient_metric, minkowskiForm_apply]
  simp [Fin.sum_univ_succ, Matrix.diagonal_apply, coefficients, lorentzSign, kasner_a,
    Real.rpow_one, Real.rpow_zero]
  have hc := Real.cosh_sq_sub_sinh_sq ((y : E) 1)
  linear_combination (v 0 * w 0 - (y : E) 0 ^ 2 * (v 1 * w 1)) * hc

/-- **The comoving line of the flat Kasner metric has an end point in an extension**: the Milne
map is a smooth metric-preserving map of the flat Kasner space-time into Minkowski space, and the
image of the comoving line tends to `(0, 0, x₀², x₀³)` as its proper time tends to `x₀⁰`. So the
conclusion of `not_tendsto_of_isometry` fails for the flat exponents `(1, 0, 0)`: the end of the
geodesic is a singularity of the co-ordinates only. -/
theorem exists_isometry_tendsto_flat (x₀ : domain (kasner ![1, 0, 0])) :
    ∃ f : domain (kasner ![1, 0, 0]) → E, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f ∧
      (∀ y v w, (metric (kasner ![1, 0, 0])).toLorentzMetric.form y v w =
        (minkowskiMetric .timeNegative 3).form (f y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f y v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f y w)) ∧
      ∃ q : E, Tendsto (fun s => f (comovingPast ![1, 0, 0] x₀ s))
        (𝓝[<] ((x₀ : E) 0)) (𝓝 q) :=
  ⟨milneEmbedding, contMDiff_milneEmbedding, form_milneEmbedding,
    milne (comovingPoint x₀ ((x₀ : E) 0)),
    (contDiff_milne.continuous.tendsto _).comp tendsto_comovingPast_val⟩

end ProjectAinos.GeneralRelativity.Kasner
