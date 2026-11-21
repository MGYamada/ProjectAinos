/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.ProperTimeVariation
public import ProjectAinos.SmoothGeometry.Lorentzian.Focusing
public import ProjectAinos.SmoothGeometry.ODE.Propagator
public import ProjectAinos.SmoothGeometry.ODE.SecondDerivativeTest

/-!
# Maximizing normal geodesics are short, and focusing gives incompleteness

Landau–Lifshitz, §119, in the form of the singularity theorem of Hawking, for a metric given by
coefficients on an open set `U` of the model space and the slices `Σ = {x⁰ = τ}`.

* `IsGeodesicSegment`, `IsTimelikeCurve`, `curveProperTime`: geodesic segments on `[0, L]` (the
  coordinate geodesic equation `γ'' = −Γ(γ', γ')`), the timelike `C¹` curves on `[0, T]` that
  compete for the proper time, and their proper time `∫ √(−g(ċ, ċ))`.
* `sliceNormal`, `sliceSecondForm`, `sliceExpansion`: the future unit normal
  `n = −(−g^{00})^{−1/2} g^{k0} ∂_k` of the slices where `g^{00} < 0`, their second fundamental form
  `K(X, Y) = −g(Γ(X, Y), n)` and their expansion `θ = h^{αβ} K_{αβ}`; the slice is spacelike
  (`spatialCoefficient_posDef`) and has an orthonormal frame with `Σ_i K(F_i, F_i) = θ`
  (`exists_orthonormal_slice`).
* `parallelField`, `form_eq_of_parallel`: parallel transport along a geodesic segment, by the
  propagator of the linear equation `E' = −Γ(γ', E)`, preserves the metric.
* `varSpeed₂_zero`: **the second variation** of the squared speed `φ = −g(ċ_ε, ċ_ε)` of the
  variation `c_ε = γ + ε W`: `∂²_ε φ(0) = −2 (F' + g(D W, D W) + g(R(W, γ')W, γ'))`, with the
  boundary term `F = g(Γ(W, W), γ')` (`hasDerivAt_boundaryTerm`); `sum_curv_frame`:
  `Σ_i g(R(E_i, u)E_i, u) = −Ric(u, u)` over an orthonormal frame.
* `length_le_of_maximizing`: **a normal geodesic that maximizes the proper time from `Σ` is
  short**: under `Ric(γ', γ') ≥ 0` and `ν θ ≤ −C < 0`, its length is at most `d/C` (it has no focal
  point before its end, and focusing would give one within `d/C`). Otherwise the second
  variation along `(1 − s/L) E_i` for a parallel orthonormal frame of `Σ` is positive for some
  `i`, and the analytic step `SecondDerivativeTest.exists_lt_integral_sqrt` gives a longer
  timelike curve.
* `length_le_of_focusing`: **focusing incompleteness**: if `x⁰` is a time function, the timelike
  convergence condition holds, `ν θ ≤ −C` on `Σ`, and every point to the `ν`-side of `Σ` is
  reached from `Σ` by a maximizing normal geodesic (what global hyperbolicity supplies by limit
  curves, taken here as a premise), then **every `ν`-directed normal geodesic from `Σ` has length
  at most `d/C`**.
* `IsSynchronous.curveProperTime_le`, `IsSynchronous.length_le_of_focusing`: in a synchronous metric
  the time lines maximize the proper time (`−g(v, v) ≤ (v⁰)²`), so the maximizing premise holds on
  every domain that contains the time lines between `Σ` and its points.

Focusing alone is the divergence of `θ` along time lines that stay in a synchronous chart
(`Focusing.lean`); leaving a synchronous chart is not a caustic. The theorem here concludes the
incompleteness of the space-time `U` itself, for geodesics that need not stay in any synchronous
chart: the comparison is with all timelike curves.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace ContinuousLinearMap MeasureTheory
open scoped Manifold ContDiff Topology MatrixOrder Matrix

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {d : ℕ} {U : Opens (MinkowskiModel d)} (g : CoordinateMetric .timeNegative d U)

local notation "E" => MinkowskiModel d

/-! ### Curves, proper time and the slices `x⁰ = τ` -/

/-- **A geodesic segment** on `[0, L]`: a `C²` curve with values in `U` on `[0, L]` whose
coordinates satisfy the geodesic equation `γ'' = −Γ(γ', γ')` there. -/
structure IsGeodesicSegment (γ : ℝ → E) (L : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 γ
  mem : ∀ s ∈ Icc 0 L, γ s ∈ U
  geodesic : ∀ s ∈ Icc 0 L, deriv (deriv γ) s = -g.chr (γ s) (deriv γ s) (deriv γ s)

/-- **A timelike curve** on `[0, T]`: a curve with values in `U`, differentiable at every point of
`[0, T]` with a continuous derivative there, and a timelike velocity. -/
structure IsTimelikeCurve (c : ℝ → E) (T : ℝ) : Prop where
  mem : ∀ s ∈ Icc 0 T, c s ∈ U
  differentiableAt : ∀ s ∈ Icc 0 T, DifferentiableAt ℝ c s
  continuousOn_deriv : ContinuousOn (deriv c) (Icc 0 T)
  timelike : ∀ s ∈ Icc 0 T, g.form (c s) (deriv c s) (deriv c s) < 0

/-- **The proper time** `∫₀ᵀ √(−g(ċ, ċ)) ds` of a curve on `[0, T]`. -/
def curveProperTime (c : ℝ → E) (T : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..T, Real.sqrt (-g.form (c s) (deriv c s) (deriv c s))

/-- **The future unit normal** of the slice `x⁰ = const` through `z`,
`n = −(−g^{00})^{−1/2} g^{k0} ∂_k`, the unit vector of the gradient of `x⁰`. -/
def sliceNormal (z : E) : E :=
  fun k => -(Real.sqrt (-(g.coefficient z)⁻¹ 0 0))⁻¹ * (g.coefficient z)⁻¹ k 0

/-- **The second fundamental form** `K(X, Y) = −g(Γ(X, Y), n)` of the slice `x⁰ = const` on
tangent vectors `X, Y` with `X⁰ = Y⁰ = 0`. -/
def sliceSecondForm (z X Y : E) : ℝ := -g.form z (g.chr z X Y) (g.sliceNormal z)

/-- **The expansion** `θ = h^{αβ} K_{αβ}` of the slice `x⁰ = const` through `z`, the trace of its
second fundamental form with the inverse of its induced metric `h_{αβ} = g_{αβ}`
(`spatialCoefficient`): the mean curvature, the expansion of the normal geodesics. -/
def sliceExpansion (z : E) : ℝ :=
  ∑ α, ∑ β, (g.spatialCoefficient z)⁻¹ α β *
    g.sliceSecondForm z (Pi.single α.succ 1) (Pi.single β.succ 1)

/-! ### The unit normal -/

variable {g}

theorem coefficient_inv_mul {z : E} (hz : z ∈ U) : (g.coefficient z)⁻¹ * g.coefficient z = 1 :=
  mul_eq_one_comm.mp (g.coefficient_mul_inv ⟨z, hz⟩)

/-- `g(n, X) = −X⁰/√(−g^{00})`: the normal is orthogonal to the slice and points to increasing
`x⁰`. -/
theorem form_sliceNormal {z : E} (hz : z ∈ U) (X : E) :
    g.form z (g.sliceNormal z) X = -(Real.sqrt (-(g.coefficient z)⁻¹ 0 0))⁻¹ * X 0 := by
  have hinv := coefficient_inv_mul (g := g) hz
  set c := -(Real.sqrt (-(g.coefficient z)⁻¹ 0 0))⁻¹ with hc
  have h (j : Fin (d + 1)) : ∑ i, g.coefficient z i j * (g.coefficient z)⁻¹ i 0 =
      if 0 = j then 1 else 0 := by
    have h1 := congrFun (congrFun hinv 0) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [g.coefficient_inv_symmetric hz i 0]
    ring
  rw [g.form_apply, Finset.sum_comm]
  calc ∑ j, ∑ i, g.coefficient z i j * g.sliceNormal z i * X j
      = ∑ j, c * X j * ∑ i, g.coefficient z i j * (g.coefficient z)⁻¹ i 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [sliceNormal, hc]
        ring
    _ = c * X 0 := by
        simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem sliceNormal_zero {z : E} (hq : (g.coefficient z)⁻¹ 0 0 < 0) :
    g.sliceNormal z 0 = Real.sqrt (-(g.coefficient z)⁻¹ 0 0) := by
  have hq' : 0 < -(g.coefficient z)⁻¹ 0 0 := by linarith
  have hs := Real.sqrt_pos.mpr hq'
  simp only [sliceNormal]
  have h := Real.mul_self_sqrt hq'.le
  field_simp
  linarith

/-- **The normal is a unit timelike vector**: `g(n, n) = −1`. -/
theorem form_sliceNormal_self {z : E} (hz : z ∈ U) (hq : (g.coefficient z)⁻¹ 0 0 < 0) :
    g.form z (g.sliceNormal z) (g.sliceNormal z) = -1 := by
  rw [form_sliceNormal hz, sliceNormal_zero hq]
  have hs := Real.sqrt_pos.mpr (show 0 < -(g.coefficient z)⁻¹ 0 0 by linarith)
  field_simp

/-- The vector `(0, ξ)` of the slice with spatial components `ξ`. -/
def sliceVector (ξ : Fin d → ℝ) : E := Fin.cons 0 ξ

@[simp] theorem sliceVector_zero (ξ : Fin d → ℝ) : sliceVector ξ 0 = 0 := rfl

@[simp] theorem sliceVector_succ (ξ : Fin d → ℝ) (α : Fin d) : sliceVector ξ α.succ = ξ α := rfl

theorem form_sliceVector (z : E) (ξ η : Fin d → ℝ) :
    g.form z (sliceVector ξ) (sliceVector η) =
      ∑ α, ∑ β, g.spatialCoefficient z α β * ξ α * η β := by
  rw [g.form_apply, Fin.sum_univ_succ]
  simp only [sliceVector_zero, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
    Fin.sum_univ_succ (f := fun j => _ * _ * sliceVector η j), sliceVector_succ]
  rfl

/-- **The slice is spacelike** where `g^{00} < 0`: its induced metric is positive definite. -/
theorem spatialCoefficient_posDef {z : E} (hz : z ∈ U) (hq : (g.coefficient z)⁻¹ 0 0 < 0) :
    (g.spatialCoefficient z).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun ξ hξ => ?_
  · ext α β
    simp [spatialCoefficient, Matrix.conjTranspose_apply, g.coefficient_symmetric hz]
  · obtain ⟨e, he⟩ := g.signature z hz
    have hu : g.form z (g.sliceNormal z) (g.sliceNormal z) < 0 := by
      rw [form_sliceNormal_self hz hq]
      norm_num
    have hv : g.form z (g.sliceNormal z) (sliceVector ξ) = 0 := by
      rw [form_sliceNormal hz, sliceVector_zero, mul_zero]
    have hv0 : sliceVector ξ ≠ 0 := by
      intro h
      apply hξ
      funext α
      have := congrFun h α.succ
      simpa using this
    have h := Minkowski.pos_of_orthogonal he hu hv hv0
    rw [form_sliceVector] at h
    convert h using 1
    simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    ring

theorem sliceVector_eq_sum (ξ : Fin d → ℝ) :
    sliceVector ξ = ∑ α, ξ α • (Pi.single α.succ 1 : E) := by
  funext k
  refine Fin.cases ?_ (fun β => ?_) k
  · simp [Fin.succ_ne_zero]
  · simp [Pi.single_apply, Fin.succ_inj]

/-- The second fundamental form is bilinear. -/
theorem sliceSecondForm_sliceVector (z : E) (ξ η : Fin d → ℝ) :
    g.sliceSecondForm z (sliceVector ξ) (sliceVector η) =
      ∑ α, ∑ β, ξ α * η β * g.sliceSecondForm z (Pi.single α.succ 1) (Pi.single β.succ 1) := by
  simp only [sliceSecondForm, sliceVector_eq_sum, map_sum, map_smul,
    _root_.sum_apply, smul_apply, smul_eq_mul, Finset.sum_neg_distrib, mul_neg,
    Finset.mul_sum]
  rw [neg_inj, Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

/-- **An orthonormal basis of the slice**: at a point where `g^{00} < 0` there are vectors
`F i = (0, ξ_i)` with `g(F i, F j) = δ_{ij}`, and the trace of the second fundamental form over
them is the expansion `θ`. -/
theorem exists_orthonormal_slice {z : E} (hz : z ∈ U) (hq : (g.coefficient z)⁻¹ 0 0 < 0) :
    ∃ F : Fin d → E, (∀ i, F i 0 = 0) ∧
      (∀ i j, g.form z (F i) (F j) = if i = j then 1 else 0) ∧
      ∑ i, g.sliceSecondForm z (F i) (F i) = g.sliceExpansion z := by
  have hpos := spatialCoefficient_posDef hz hq
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos.inv.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at hB
  have hdet : IsUnit (g.spatialCoefficient z).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit
  have h1 : Bᵀ * (B * g.spatialCoefficient z) = 1 := by
    rw [← Matrix.mul_assoc, ← hB]
    exact Matrix.nonsing_inv_mul _ hdet
  have h2 : B * g.spatialCoefficient z * Bᵀ = 1 := mul_eq_one_comm.mp h1
  refine ⟨fun i => sliceVector fun α => B i α, fun i => rfl, fun i j => ?_, ?_⟩
  · rw [form_sliceVector]
    have h3 := congrFun (congrFun h2 i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h3
    rw [← h3, Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  · simp only [sliceSecondForm_sliceVector, sliceExpansion, hB, Matrix.mul_apply,
      Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm]

/-! ### The trace in an orthonormal basis -/

/-- **The trace in an orthonormal basis**: for vectors `f_a` with `g(f_a, f_b) = η_a δ_{ab}` and
`η_a² = 1`, the trace of a linear map is `Σ_a η_a g(A f_a, f_a)`. -/
theorem trace_eq_sum_orthonormal {z : E} (hz : z ∈ U) (A : E →L[ℝ] E) (f : Fin (d + 1) → E)
    (η : Fin (d + 1) → ℝ) (hη : ∀ a, η a * η a = 1)
    (horth : ∀ a b, g.form z (f a) (f b) = if a = b then η a else 0) :
    ∑ l, A (Pi.single l 1) l = ∑ a, η a * g.form z (A (f a)) (f a) := by
  let C := g.coefficient z
  let P : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Matrix.of fun i a => f a i
  let N : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Matrix.diagonal η
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := Matrix.of fun l i => A (Pi.single i 1) l
  have hM (v : E) (l : Fin (d + 1)) : A v l = ∑ i, M l i * v i := by
    conv_lhs => rw [pi_eq_sum_univ' v]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M,
      Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hgram : Pᵀ * C * P = N := by
    ext a b
    have h := horth a b
    rw [g.form_apply] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, P, N, Matrix.of_apply,
      Matrix.diagonal_apply, C, Finset.sum_mul]
    rw [← h, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hNN : N * N = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext hη)
  have h1 : Pᵀ * C * (P * N) = 1 := by rw [← Matrix.mul_assoc, hgram, hNN]
  have h2 : P * N * (Pᵀ * C) = 1 := by
    have h1' : Pᵀ * C * (P * N) = 1 := h1
    exact mul_eq_one_comm.mp h1'
  have htr : ∑ l, A (Pi.single l 1) l = M.trace := by
    simp only [Matrix.trace, Matrix.diag, M, Matrix.of_apply]
  rw [htr]
  calc M.trace = (M * (P * N) * (Pᵀ * C)).trace := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    _ = (Pᵀ * C * M * (P * N)).trace := by rw [Matrix.trace_mul_cycle]
    _ = ∑ a, (Pᵀ * C * M * P) a a * η a := by
        rw [← Matrix.mul_assoc, Matrix.trace]
        simp only [Matrix.diag, N, Matrix.mul_diagonal]
    _ = ∑ a, η a * g.form z (A (f a)) (f a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_comm, g.form_comm hz, g.form_apply]
        congr 1
        simp only [Matrix.mul_apply, Matrix.transpose_apply, P, Matrix.of_apply, C, hM,
          Finset.mul_sum, Finset.sum_mul]
        conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
        conv_lhs => rw [Finset.sum_comm]
        conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun j _ => ?_
        ring

/-! ### Parallel transport along a geodesic segment -/

variable {γ : ℝ → MinkowskiModel d} {L : ℝ}

theorem IsGeodesicSegment.hasDerivAt (hγ : g.IsGeodesicSegment γ L) (s : ℝ) :
    HasDerivAt γ (deriv γ s) s :=
  (hγ.contDiff.differentiable (by norm_num) s).hasDerivAt

theorem IsGeodesicSegment.contDiff_deriv (hγ : g.IsGeodesicSegment γ L) :
    ContDiff ℝ 1 (deriv γ) :=
  (contDiff_succ_iff_deriv.mp hγ.contDiff).2.2

theorem IsGeodesicSegment.hasDerivAt_deriv (hγ : g.IsGeodesicSegment γ L) (s : ℝ) :
    HasDerivAt (deriv γ) (deriv (deriv γ) s) s :=
  (hγ.contDiff_deriv.differentiable one_ne_zero s).hasDerivAt

theorem IsGeodesicSegment.continuous_deriv (hγ : g.IsGeodesicSegment γ L) :
    Continuous (deriv γ) :=
  hγ.contDiff_deriv.continuous

/-- The coefficient `s ↦ −Γ(γ(s))(γ'(s), ·)` of parallel transport along `γ`, evaluated at the
nearest point of `[0, L]`. -/
def transportCoeff (γ : ℝ → E) (L : ℝ) (hL : 0 ≤ L) (s : ℝ) : E →L[ℝ] E :=
  -g.chr (γ (projIcc 0 L hL s)) (deriv γ (projIcc 0 L hL s))

theorem continuous_transportCoeff (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) :
    Continuous (g.transportCoeff γ L hL) := by
  have hc : ContinuousOn (fun s => g.chr (γ s) (deriv γ s)) (Icc 0 L) := by
    have h1 : ContinuousOn (fun s => g.chr (γ s)) (Icc 0 L) :=
      g.contDiffOn_chr.continuousOn.comp hγ.contDiff.continuous.continuousOn
        fun s hs => hγ.mem s hs
    exact h1.clm_apply hγ.continuous_deriv.continuousOn
  exact (hc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    fun s => (projIcc 0 L hL s).2).neg

theorem transportCoeff_of_mem (hL : 0 ≤ L) {s : ℝ} (hs : s ∈ Icc 0 L) :
    g.transportCoeff γ L hL s = -g.chr (γ s) (deriv γ s) := by
  simp [transportCoeff, projIcc_of_mem hL hs]

variable (g) in
/-- The transport coefficient as a continuous curve of endomorphisms. -/
def transportCurve (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) : C(ℝ, E →L[ℝ] E) :=
  ⟨g.transportCoeff γ L hL, g.continuous_transportCoeff hγ hL⟩

variable (g) in
/-- **The parallel transport** of a vector `v` at `γ(0)` along the segment. -/
def parallelField (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) (v : E) (s : ℝ) : E :=
  LinearODE.propagator (g.transportCurve hγ hL) s 0 v

theorem hasDerivAt_parallelField (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) (v : E) (s : ℝ) :
    HasDerivAt (g.parallelField hγ hL v)
      (g.transportCoeff γ L hL s (g.parallelField hγ hL v s)) s :=
  LinearODE.hasDerivAt_propagator_apply _ s 0 v

@[simp] theorem parallelField_zero (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) (v : E) :
    g.parallelField hγ hL v 0 = v := by
  simp [parallelField]

theorem continuous_parallelField (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L) (v : E) :
    Continuous (g.parallelField hγ hL v) :=
  continuous_iff_continuousAt.mpr fun s => (g.hasDerivAt_parallelField hγ hL v s).continuousAt

/-- **Parallel transport preserves the metric**: for fields `V`, `W` along the segment with
`V' = −Γ(γ', V)` and `W' = −Γ(γ', W)` on `[0, L]`, `g(V, W)` is constant there. The velocity of the
geodesic is such a field. -/
theorem form_eq_of_parallel (hγ : g.IsGeodesicSegment γ L) {V W V' W' : ℝ → E}
    (hV : ∀ s ∈ Icc 0 L, HasDerivAt V (V' s) s) (hW : ∀ s ∈ Icc 0 L, HasDerivAt W (W' s) s)
    (hV' : ∀ s ∈ Icc 0 L, V' s = -g.chr (γ s) (deriv γ s) (V s))
    (hW' : ∀ s ∈ Icc 0 L, W' s = -g.chr (γ s) (deriv γ s) (W s)) :
    ∀ s ∈ Icc 0 L, g.form (γ s) (V s) (W s) = g.form (γ 0) (V 0) (W 0) := by
  have hd (s : ℝ) (hs : s ∈ Icc 0 L) : HasDerivAt (fun s => g.form (γ s) (V s) (W s)) 0 s := by
    have h := g.hasDerivAt_form_along (hγ.mem s hs) (hγ.hasDerivAt s) (hV s hs) (hW s hs)
    rw [hV' s hs, hW' s hs] at h
    simpa using h
  exact constant_of_has_deriv_right_zero (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt

/-! ### The second variation of the squared speed -/

variable (g) in
/-- The squared speed `φ(ε) = −g(u + εw', u + εw')` at `x + εw` of a varied curve `γ + εW` at one
parameter, with `x = γ(s)`, `u = γ'(s)`, `w = W(s)` and `w' = W'(s)`. -/
def varSpeed (x u w w' : E) (ε : ℝ) : ℝ := -g.form (x + ε • w) (u + ε • w') (u + ε • w')

variable (g) in
/-- Its first derivative in `ε`, `−2 g(w' + Γ(w, u + εw'), u + εw')`. -/
def varSpeed₁ (x u w w' : E) (ε : ℝ) : ℝ :=
  -2 * g.form (x + ε • w) (w' + g.chr (x + ε • w) w (u + ε • w')) (u + ε • w')

variable (g) in
/-- The expression of the second derivative at a point `y` with velocity `v`. -/
def varSpeed₂Expr (y v w w' : E) : ℝ :=
  -2 * (g.form y (g.chr y w (w' + g.chr y w v) + (fderiv ℝ g.chr y w w v + g.chr y w w')) v +
    g.form y (w' + g.chr y w v) (w' + g.chr y w v))

variable (g) in
/-- Its second derivative in `ε`. -/
def varSpeed₂ (x u w w' : E) (ε : ℝ) : ℝ := g.varSpeed₂Expr (x + ε • w) (u + ε • w') w w'

theorem hasDerivAt_line (x w : E) (ε : ℝ) : HasDerivAt (fun e : ℝ => x + e • w) w ε := by
  have h := ((hasDerivAt_id' ε).smul_const w).const_add x
  rwa [one_smul] at h

theorem hasDerivAt_varSpeed {x u w w' : E} {ε : ℝ} (hx : x + ε • w ∈ U) :
    HasDerivAt (g.varSpeed x u w w') (g.varSpeed₁ x u w w' ε) ε := by
  have h := g.hasDerivAt_form_along hx (hasDerivAt_line x w ε) (hasDerivAt_line u w' ε)
    (hasDerivAt_line u w' ε)
  refine h.neg.congr_deriv ?_
  rw [varSpeed₁, g.form_comm hx (u + ε • w'), add_comm (g.chr _ _ _) w']
  ring

theorem hasDerivAt_varSpeed₁ {x u w w' : E} {ε : ℝ} (hx : x + ε • w ∈ U) :
    HasDerivAt (g.varSpeed₁ x u w w') (g.varSpeed₂ x u w w' ε) ε := by
  have hP := (g.hasDerivAt_chr_along hx (hasDerivAt_line x w ε) (hasDerivAt_const ε w)
    (hasDerivAt_line u w' ε)).const_add w'
  have h := g.hasDerivAt_form_along hx (hasDerivAt_line x w ε) hP (hasDerivAt_line u w' ε)
  refine (h.const_mul (-2)).congr_deriv ?_
  rw [varSpeed₂, varSpeed₂Expr, map_zero, zero_apply, add_zero, add_comm (g.chr _ _ _) w']

/-- **The second variation at `ε = 0`**: with `P = w' + Γ(u, w)`,
`φ''(0) = −2 (F' + g(P, P) + g(R(w, u)w, u))`, where
`F' = g(Γ(u, Γ(w, w)) + (∂_u Γ)(w, w) + Γ(w', w) + Γ(w, w'), u)` is the derivative of the boundary
term `F = g(Γ(W, W), γ')` along a geodesic. -/
theorem varSpeed₂_zero {x : E} (hx : x ∈ U) (u w w' : E) :
    g.varSpeed₂ x u w w' 0 =
      -2 * (g.form x (g.chr x u (g.chr x w w) +
          (fderiv ℝ g.chr x u w w + g.chr x w' w + g.chr x w w')) u +
        g.form x (w' + g.chr x u w) (w' + g.chr x u w) + g.form x (g.curv x w u w) u) := by
  simp only [varSpeed₂, varSpeed₂Expr, zero_smul, add_zero, curv]
  rw [g.chr_symm hx w' w, g.chr_symm hx u w, g.fderiv_chr_symm hx w u w]
  simp only [map_add, map_sub, add_apply, sub_apply]
  ring

/-! ### Continuity and a tube around the segment -/

theorem continuousOn_form_apply {T : Type} [TopologicalSpace T] {S : Set T} {y a b : T → E}
    (hy : ContinuousOn y S) (hyU : MapsTo y S U) (ha : ContinuousOn a S) (hb : ContinuousOn b S) :
    ContinuousOn (fun t => g.form (y t) (a t) (b t)) S :=
  ((g.smooth.continuousOn.comp hy hyU).clm_apply ha).clm_apply hb

theorem continuousOn_chr_apply {T : Type} [TopologicalSpace T] {S : Set T} {y a b : T → E}
    (hy : ContinuousOn y S) (hyU : MapsTo y S U) (ha : ContinuousOn a S) (hb : ContinuousOn b S) :
    ContinuousOn (fun t => g.chr (y t) (a t) (b t)) S :=
  ((g.contDiffOn_chr.continuousOn.comp hy hyU).clm_apply ha).clm_apply hb

theorem continuousOn_fderiv_chr_apply {T : Type} [TopologicalSpace T] {S : Set T}
    {y v a b : T → E} (hy : ContinuousOn y S) (hyU : MapsTo y S U) (hv : ContinuousOn v S)
    (ha : ContinuousOn a S) (hb : ContinuousOn b S) :
    ContinuousOn (fun t => fderiv ℝ g.chr (y t) (v t) (a t) (b t)) S := by
  have h1 := g.contDiffOn_chr.continuousOn_fderiv_of_isOpen U.isOpen (by simp)
  have h2 := h1.comp hy hyU
  exact ((h2.clm_apply hv).clm_apply ha).clm_apply hb

theorem continuousOn_varSpeed₂Expr {T : Type} [TopologicalSpace T] {S : Set T}
    {y v w w' : T → E} (hy : ContinuousOn y S) (hyU : MapsTo y S U) (hv : ContinuousOn v S)
    (hw : ContinuousOn w S) (hw' : ContinuousOn w' S) :
    ContinuousOn (fun t => g.varSpeed₂Expr (y t) (v t) (w t) (w' t)) S := by
  have hP : ContinuousOn (fun t => w' t + g.chr (y t) (w t) (v t)) S :=
    hw'.add (continuousOn_chr_apply (g := g) hy hyU hw hv)
  have hQ : ContinuousOn (fun t => g.chr (y t) (w t) (w' t + g.chr (y t) (w t) (v t)) +
      (fderiv ℝ g.chr (y t) (w t) (w t) (v t) + g.chr (y t) (w t) (w' t))) S :=
    (continuousOn_chr_apply (g := g) hy hyU hw hP).add
      ((continuousOn_fderiv_chr_apply (g := g) hy hyU hw hw hv).add
        (continuousOn_chr_apply (g := g) hy hyU hw hw'))
  have h := ((continuousOn_form_apply (g := g) hy hyU hQ hv).add
    (continuousOn_form_apply (g := g) hy hyU hP hP)).const_smul (-2 : ℝ)
  refine h.congr fun t _ => ?_
  simp only [varSpeed₂Expr, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

/-- **A tube around the segment**: there is `ε₀ > 0` such that `γ(s) + ε w ∈ U` for all
`s ∈ [0, L]`, `ε ∈ [0, ε₀]` and `‖w‖ ≤ M`. -/
theorem exists_tube {γ : ℝ → E} {L M : ℝ} (hγ : ContinuousOn γ (Icc 0 L))
    (hU : MapsTo γ (Icc 0 L) U) (hM : 0 ≤ M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Icc 0 ε₀, ∀ s ∈ Icc 0 L, ∀ w : E, ‖w‖ ≤ M → γ s + ε • w ∈ U := by
  have hK : IsCompact (γ '' Icc 0 L) := isCompact_Icc.image_of_continuousOn hγ
  obtain ⟨r, hr, hsub⟩ := hK.exists_thickening_subset_open U.isOpen
    (by rintro _ ⟨s, hs, rfl⟩; exact hU hs)
  refine ⟨r / (2 * (M + 1)), by positivity, fun ε hε s hs w hw => hsub ?_⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨γ s, ⟨s, hs, rfl⟩, ?_⟩
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε.1]
  have h1 : ε * ‖w‖ ≤ r / (2 * (M + 1)) * M :=
    mul_le_mul hε.2 hw (norm_nonneg w) (by positivity)
  have h2 : r / (2 * (M + 1)) * M < r := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ### The boundary term and the curvature term -/

/-- **The boundary term** `F = g(Γ(W, W), γ')` along a geodesic has the derivative
`g(Γ(γ', Γ(W, W)) + (∂_{γ'} Γ)(W, W) + Γ(W', W) + Γ(W, W'), γ')`. -/
theorem hasDerivAt_boundaryTerm (hγ : g.IsGeodesicSegment γ L) {W W' : ℝ → E} {s : ℝ}
    (hs : s ∈ Icc 0 L) (hW : HasDerivAt W (W' s) s) :
    HasDerivAt (fun s => g.form (γ s) (g.chr (γ s) (W s) (W s)) (deriv γ s))
      (g.form (γ s) (g.chr (γ s) (deriv γ s) (g.chr (γ s) (W s) (W s)) +
        (fderiv ℝ g.chr (γ s) (deriv γ s) (W s) (W s) + g.chr (γ s) (W' s) (W s) +
          g.chr (γ s) (W s) (W' s))) (deriv γ s)) s := by
  have hX := g.hasDerivAt_chr_along (hγ.mem s hs) (hγ.hasDerivAt s) hW hW
  have h := g.hasDerivAt_form_along (hγ.mem s hs) (hγ.hasDerivAt s) hX (hγ.hasDerivAt_deriv s)
  refine h.congr_deriv ?_
  rw [hγ.geodesic s hs, add_neg_cancel, map_zero, add_zero]

theorem curv_smul_smul (x a b : E) (c : ℝ) :
    g.curv x (c • a) b (c • a) = (c * c) • g.curv x a b a := by
  simp only [curv, map_smul, smul_apply, smul_sub, smul_add, smul_smul]

/-- **The curvature term summed over an orthonormal frame is minus the Ricci curvature**: for a
unit timelike `u` and an orthonormal frame `E_i` of its orthogonal complement,
`Σ_i g(R(E_i, u)E_i, u) = −Ric(u, u)`. -/
theorem sum_curv_frame {x : E} (hx : x ∈ U) (u : E) (Ef : Fin d → E)
    (huu : g.form x u u = -1) (hEu : ∀ i, g.form x (Ef i) u = 0)
    (hEE : ∀ i j, g.form x (Ef i) (Ef j) = if i = j then 1 else 0) :
    ∑ i, g.form x (g.curv x (Ef i) u (Ef i)) u =
      -∑ j, ∑ k, ricciOf g.coefficient x j k * u j * u k := by
  let A : E →L[ℝ] E := ((fderiv ℝ g.chr x).flip u).flip u - (fderiv ℝ g.chr x u).flip u +
    (g.chr x).flip (g.chr x u u) - (g.chr x u).comp ((g.chr x).flip u)
  have hA (X : E) : A X = g.curv x X u u := by
    simp only [A, curv, add_apply, sub_apply, flip_apply, comp_apply]
  let fr : Fin (d + 1) → E := Fin.cons u Ef
  let η : Fin (d + 1) → ℝ := Fin.cons (-1) fun _ => 1
  have horth (a b : Fin (d + 1)) :
      g.form x (fr a) (fr b) = if a = b then η a else 0 := by
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · simp [fr, η, huu]
    · simp [fr, η, g.form_comm hx u, hEu, (Fin.succ_ne_zero j).symm]
    · simp [fr, η, hEu, Fin.succ_ne_zero]
    · simp [fr, η, hEE, Fin.succ_inj]
  have hη (a : Fin (d + 1)) : η a * η a = 1 := by
    refine Fin.cases ?_ (fun i => ?_) a <;> simp [η]
  have htr := trace_eq_sum_orthonormal hx A fr η hη horth
  have hric := g.ricciOf_eq_sum_curv hx u
  simp only [← hA] at hric
  rw [hric, htr, Fin.sum_univ_succ]
  simp only [fr, η, Fin.cons_zero, Fin.cons_succ, hA, curv_self, map_zero, zero_apply, mul_zero,
    zero_add, one_mul]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g.curv_pair_swap hx]

/-! ### Maximizing normal geodesics are short -/

/-- **A maximizing normal geodesic is short** (it has no focal point of the slice before its end,
and focusing would produce one within `d/C`; focal points are not defined here, the second variation
is used directly). Let `γ`
be a geodesic segment on `[0, L]` that starts on the slice `x⁰ = τ` with the velocity `ν n`,
`ν = ±1`, where `n` is the unit normal of the slice (the slice is spacelike there:
`g^{00} < 0`). Assume the timelike convergence `Ric(γ', γ') ≥ 0` along `γ` and
`ν θ ≤ −C < 0` for the expansion `θ` of the slice at `γ(0)`. If `γ` maximizes the proper time
among the timelike curves from the slice to `γ(L)`, then `L ≤ d/C`.

If `L > d/C`, the second variation of the proper time along the fields `(1 − s/L) E_i`, for a
parallel orthonormal frame `E_i` of the slice transported along `γ`, sums to
`2(−ν θ − d/L + ∫ (1 − s/L)² Ric(γ', γ')) > 0`, so one of the curves `γ + ε (1 − s/L) E_i` is
timelike and longer. -/
theorem length_le_of_maximizing {τ C L ν : ℝ} (hν : ν * ν = 1) (hC : 0 < C) (hL : 0 < L)
    {γ : ℝ → E} (hγ : g.IsGeodesicSegment γ L) (hγ0 : γ 0 0 = τ)
    (hn : deriv γ 0 = ν • g.sliceNormal (γ 0)) (hq : (g.coefficient (γ 0))⁻¹ 0 0 < 0)
    (hRic : ∀ s ∈ Icc 0 L,
      0 ≤ ∑ j, ∑ k, ricciOf g.coefficient (γ s) j k * deriv γ s j * deriv γ s k)
    (hθ : ν * g.sliceExpansion (γ 0) ≤ -C)
    (hmax : ∀ (c : ℝ → E) (T : ℝ), g.IsTimelikeCurve c T → c 0 0 = τ → c T = γ L →
      g.curveProperTime c T ≤ L) :
    L ≤ d / C := by
  by_contra hlt'
  have hlt : d / C < L := not_le.mp hlt'
  have hL0 := hL.le
  have hmem0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL0⟩
  have hmemL : L ∈ Icc 0 L := ⟨hL0, le_rfl⟩
  have hx0 : γ 0 ∈ U := hγ.mem 0 hmem0
  obtain ⟨F, hF0, hFF, hFθ⟩ := exists_orthonormal_slice hx0 hq
  -- the parallel frame
  set Ef : Fin d → ℝ → E := fun i => g.parallelField hγ hL0 (F i) with hEf
  have hEd (i : Fin d) (s : ℝ) :
      HasDerivAt (Ef i) (g.transportCoeff γ L hL0 s (Ef i s)) s :=
    g.hasDerivAt_parallelField hγ hL0 (F i) s
  have hEd' (i : Fin d) (s : ℝ) (hs : s ∈ Icc 0 L) :
      g.transportCoeff γ L hL0 s (Ef i s) = -g.chr (γ s) (deriv γ s) (Ef i s) := by
    rw [transportCoeff_of_mem hL0 hs, neg_apply]
  have hEE (i j : Fin d) (s : ℝ) (hs : s ∈ Icc 0 L) :
      g.form (γ s) (Ef i s) (Ef j s) = if i = j then 1 else 0 := by
    rw [form_eq_of_parallel hγ (fun s _ => hEd i s) (fun s _ => hEd j s)
      (fun s hs => hEd' i s hs) (fun s hs => hEd' j s hs) s hs]
    simp only [hEf, parallelField_zero, hFF]
  have hEu (i : Fin d) (s : ℝ) (hs : s ∈ Icc 0 L) : g.form (γ s) (Ef i s) (deriv γ s) = 0 := by
    rw [form_eq_of_parallel hγ (fun s _ => hEd i s) (fun s _ => hγ.hasDerivAt_deriv s)
      (fun s hs => hEd' i s hs) (fun s hs => hγ.geodesic s hs) s hs]
    simp only [hEf, parallelField_zero, hn, map_smul, smul_eq_mul]
    rw [g.form_comm hx0, form_sliceNormal hx0, hF0, mul_zero, mul_zero]
  have huu (s : ℝ) (hs : s ∈ Icc 0 L) : g.form (γ s) (deriv γ s) (deriv γ s) = -1 := by
    rw [form_eq_of_parallel hγ (fun s _ => hγ.hasDerivAt_deriv s)
      (fun s _ => hγ.hasDerivAt_deriv s) (fun s hs => hγ.geodesic s hs)
      (fun s hs => hγ.geodesic s hs) s hs, hn]
    simp only [map_smul, smul_apply, smul_eq_mul, form_sliceNormal_self hx0 hq]
    linear_combination -hν
  -- the test fields `W_i = (1 − s/L) E_i`
  set f : ℝ → ℝ := fun s => 1 - s / L with hf
  have hfd (s : ℝ) : HasDerivAt f (-1 / L) s := by
    have h := ((hasDerivAt_id' s).div_const L).const_sub 1
    rw [neg_div]
    exact h
  have hfc : Continuous f := continuous_const.sub (continuous_id.div_const L)
  set W : Fin d → ℝ → E := fun i s => f s • Ef i s with hW
  set W' : Fin d → ℝ → E := fun i s =>
    (-1 / L) • Ef i s + f s • g.transportCoeff γ L hL0 s (Ef i s) with hW'
  have hEc (i : Fin d) : Continuous (Ef i) := g.continuous_parallelField hγ hL0 (F i)
  have hWd (i : Fin d) (s : ℝ) : HasDerivAt (W i) (W' i s) s := by
    have h := (hfd s).smul (hEd i s)
    refine h.congr_deriv ?_
    rw [add_comm]
  have hWc (i : Fin d) : Continuous (W i) := hfc.smul (hEc i)
  have hW'c (i : Fin d) : Continuous (W' i) := by
    have h1 : Continuous fun s => (-1 / L) • Ef i s := by
      have h := (hEc i).const_smul (-1 / L : ℝ)
      exact h
    have h2 : Continuous fun s => f s • g.transportCoeff γ L hL0 s (Ef i s) :=
      hfc.smul ((g.continuous_transportCoeff hγ hL0).clm_apply (hEc i))
    exact h1.add h2
  have hP (i : Fin d) (s : ℝ) (hs : s ∈ Icc 0 L) :
      W' i s + g.chr (γ s) (deriv γ s) (W i s) = (-1 / L) • Ef i s := by
    simp only [hW', hW, hEd' i s hs, map_smul, smul_neg]
    abel
  have hP' (i : Fin d) (s : ℝ) (hs : s ∈ Icc 0 L) :
      W' i s + g.chr (γ s) (W i s) (deriv γ s) = (-1 / L) • Ef i s := by
    rw [g.chr_symm (hγ.mem s hs), hP i s hs]
  -- a tube around the segment
  have hγc : Continuous γ := hγ.contDiff.continuous
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun s => ∑ i, ‖W i s‖) (s := Icc (0 : ℝ) L)
    (continuous_finsetSum _ fun i _ => (hWc i).norm).continuousOn
  have hWM (i : Fin d) (s : ℝ) (hs : s ∈ Icc 0 L) : ‖W i s‖ ≤ max M₀ 0 := by
    have h1 : ‖W i s‖ ≤ ∑ j, ‖W j s‖ :=
      Finset.single_le_sum (f := fun j => ‖W j s‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    have h2 := hM₀ s hs
    rw [Real.norm_eq_abs] at h2
    exact h1.trans ((le_abs_self _).trans (h2.trans (le_max_left _ _)))
  obtain ⟨ε₀, hε₀, htube⟩ := exists_tube hγc.continuousOn (fun s hs => hγ.mem s hs)
    (le_max_right M₀ 0)
  have hU (i : Fin d) (ε s : ℝ) (hε : ε ∈ Icc 0 ε₀) (hs : s ∈ Icc 0 L) :
      γ s + ε • W i s ∈ U := htube ε hε s hs _ (hWM i s hs)
  have hγd : Continuous (deriv γ) := hγ.continuous_deriv
  -- the hypotheses of the second derivative test for each field
  have h1 (i : Fin d) : ∀ s ∈ Icc 0 L, ∀ ε ∈ Icc 0 ε₀, HasDerivAt
      (fun e => g.varSpeed (γ s) (deriv γ s) (W i s) (W' i s) e)
      (g.varSpeed₁ (γ s) (deriv γ s) (W i s) (W' i s) ε) ε :=
    fun s hs ε hε => g.hasDerivAt_varSpeed (hU i ε s hε hs)
  have h2 (i : Fin d) : ∀ s ∈ Icc 0 L, ∀ ε ∈ Icc 0 ε₀, HasDerivAt
      (fun e => g.varSpeed₁ (γ s) (deriv γ s) (W i s) (W' i s) e)
      (g.varSpeed₂ (γ s) (deriv γ s) (W i s) (W' i s) ε) ε :=
    fun s hs ε hε => g.hasDerivAt_varSpeed₁ (hU i ε s hε hs)
  have h3 (i : Fin d) : ContinuousOn
      (fun q : ℝ × ℝ => g.varSpeed₂ (γ q.2) (deriv γ q.2) (W i q.2) (W' i q.2) q.1)
      (Icc 0 ε₀ ×ˢ Icc 0 L) := by
    have hy : Continuous fun q : ℝ × ℝ => γ q.2 + q.1 • W i q.2 :=
      (hγc.comp continuous_snd).add (continuous_fst.smul ((hWc i).comp continuous_snd))
    have hv : Continuous fun q : ℝ × ℝ => deriv γ q.2 + q.1 • W' i q.2 :=
      (hγd.comp continuous_snd).add (continuous_fst.smul ((hW'c i).comp continuous_snd))
    exact continuousOn_varSpeed₂Expr (g := g) hy.continuousOn
      (fun q hq => hU i q.1 q.2 hq.1 hq.2) hv.continuousOn
      ((hWc i).comp continuous_snd).continuousOn ((hW'c i).comp continuous_snd).continuousOn
  have h4 (i : Fin d) : ∀ ε ∈ Icc 0 ε₀,
      ContinuousOn (fun s => g.varSpeed (γ s) (deriv γ s) (W i s) (W' i s) ε) (Icc 0 L) := by
    intro ε hε
    have hy : Continuous fun s => γ s + ε • W i s := hγc.add ((hWc i).const_smul ε)
    have hv : Continuous fun s => deriv γ s + ε • W' i s := hγd.add ((hW'c i).const_smul ε)
    exact (continuousOn_form_apply (g := g) hy.continuousOn (fun s hs => hU i ε s hε hs)
      hv.continuousOn hv.continuousOn).neg
  have h5 (i : Fin d) : ∀ s ∈ Icc 0 L,
      g.varSpeed (γ s) (deriv γ s) (W i s) (W' i s) 0 = 1 ∧
        g.varSpeed₁ (γ s) (deriv γ s) (W i s) (W' i s) 0 = 0 := by
    intro s hs
    refine ⟨?_, ?_⟩
    · simp only [varSpeed, zero_smul, add_zero, huu s hs, neg_neg]
    · simp only [varSpeed₁, zero_smul, add_zero, hP' i s hs, map_smul, smul_apply, smul_eq_mul,
        hEu i s hs, mul_zero]
  -- the boundary term
  set Fb : Fin d → ℝ → ℝ := fun i s =>
    g.form (γ s) (g.chr (γ s) (W i s) (W i s)) (deriv γ s) with hFb
  set Fd : Fin d → ℝ → ℝ := fun i s =>
    g.form (γ s) (g.chr (γ s) (deriv γ s) (g.chr (γ s) (W i s) (W i s)) +
      (fderiv ℝ g.chr (γ s) (deriv γ s) (W i s) (W i s) + g.chr (γ s) (W' i s) (W i s) +
        g.chr (γ s) (W i s) (W' i s))) (deriv γ s) with hFd
  have hFbd (i : Fin d) (s : ℝ) (hs : s ∈ Icc 0 L) : HasDerivAt (Fb i) (Fd i s) s :=
    g.hasDerivAt_boundaryTerm hγ hs (hWd i s)
  have hFdc (i : Fin d) : ContinuousOn (Fd i) (Icc 0 L) := by
    have hy := hγc.continuousOn (s := Icc 0 L)
    have hyU : MapsTo γ (Icc 0 L) U := fun s hs => hγ.mem s hs
    have hu := hγd.continuousOn (s := Icc 0 L)
    have hw := (hWc i).continuousOn (s := Icc 0 L)
    have hw' := (hW'c i).continuousOn (s := Icc 0 L)
    exact continuousOn_form_apply (g := g) hy hyU
      ((continuousOn_chr_apply (g := g) hy hyU hu
        (continuousOn_chr_apply (g := g) hy hyU hw hw)).add
        (((continuousOn_fderiv_chr_apply (g := g) hy hyU hu hw hw).add
          (continuousOn_chr_apply (g := g) hy hyU hw' hw)).add
            (continuousOn_chr_apply (g := g) hy hyU hw hw'))) hu
  -- the second variation at `ε = 0`
  have hφ₂ (i : Fin d) (s : ℝ) (hs : s ∈ Icc 0 L) :
      g.varSpeed₂ (γ s) (deriv γ s) (W i s) (W' i s) 0 = -2 * (Fd i s + 1 / L ^ 2 +
        f s ^ 2 * g.form (γ s) (g.curv (γ s) (Ef i s) (deriv γ s) (Ef i s)) (deriv γ s)) := by
    rw [g.varSpeed₂_zero (hγ.mem s hs), hP i s hs]
    have hc : g.curv (γ s) (W i s) (deriv γ s) (W i s) =
        (f s * f s) • g.curv (γ s) (Ef i s) (deriv γ s) (Ef i s) :=
      g.curv_smul_smul (γ s) (Ef i s) (deriv γ s) (f s)
    rw [hc]
    simp only [map_smul, smul_apply, smul_eq_mul, hEE i i s hs, ite_true, hFd]
    field_simp
  have hsumφ (s : ℝ) (hs : s ∈ Icc 0 L) :
      ∑ i, g.varSpeed₂ (γ s) (deriv γ s) (W i s) (W' i s) 0 =
        -2 * (∑ i, Fd i s + d / L ^ 2) + 2 * f s ^ 2 *
          ∑ j, ∑ k, ricciOf g.coefficient (γ s) j k * deriv γ s j * deriv γ s k := by
    have hR := g.sum_curv_frame (hγ.mem s hs) (deriv γ s) (fun i => Ef i s) (huu s hs)
      (fun i => hEu i s hs) (fun i j => hEE i j s hs)
    simp only [hφ₂ _ s hs, Finset.sum_add_distrib, ← Finset.mul_sum] at hR ⊢
    rw [hR, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hge (s : ℝ) (hs : s ∈ Icc 0 L) :
      -2 * (∑ i, Fd i s + d / L ^ 2) ≤
        ∑ i, g.varSpeed₂ (γ s) (deriv γ s) (W i s) (W' i s) 0 := by
    rw [hsumφ s hs]
    nlinarith [hRic s hs, sq_nonneg (f s)]
  -- integration
  have hint₂ (i : Fin d) : IntervalIntegrable
      (fun s => g.varSpeed₂ (γ s) (deriv γ s) (W i s) (W' i s) 0) volume 0 L := by
    have hmaps : MapsTo (fun s : ℝ => ((0 : ℝ), s)) (Icc 0 L) (Icc 0 ε₀ ×ˢ Icc 0 L) :=
      fun s hs => ⟨⟨le_rfl, hε₀.le⟩, hs⟩
    have hc := (h3 i).comp (continuousOn_const.prodMk continuousOn_id) hmaps
    exact (hc.mono (by rw [uIcc_of_le hL0])).intervalIntegrable
  have hintFd (i : Fin d) : IntervalIntegrable (Fd i) volume 0 L :=
    ((hFdc i).mono (by rw [uIcc_of_le hL0])).intervalIntegrable
  have hintsum : IntervalIntegrable (fun s => ∑ i, Fd i s) volume 0 L := by
    have h := IntervalIntegrable.sum Finset.univ fun i _ => hintFd i
    convert h using 1
    funext s
    simp only [Finset.sum_apply]
  have hintsum₂ : IntervalIntegrable
      (fun s => ∑ i, g.varSpeed₂ (γ s) (deriv γ s) (W i s) (W' i s) 0) volume 0 L := by
    have h := IntervalIntegrable.sum Finset.univ fun i _ => hint₂ i
    convert h using 1
    funext s
    simp only [Finset.sum_apply]
  have hmono := intervalIntegral.integral_mono_on hL0
    ((hintsum.add intervalIntegrable_const).const_mul (-2)) hintsum₂ hge
  have hFTC : ∫ s in (0 : ℝ)..L, ∑ i, Fd i s = ∑ i, Fb i L - ∑ i, Fb i 0 := by
    rw [intervalIntegral.integral_finsetSum fun i _ => hintFd i, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hFbd i s (by rwa [uIcc_of_le hL0] at hs)) (hintFd i)
  have hFbL : ∑ i, Fb i L = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [hFb, hW, hf, div_self hL.ne', sub_self, zero_smul, map_zero, zero_apply]
  have hFb0 : ∑ i, Fb i 0 = -ν * g.sliceExpansion (γ 0) := by
    rw [← hFθ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hFb, hW, hf, zero_div, sub_zero, one_smul, hEf, parallelField_zero, hn, map_smul,
      smul_eq_mul, sliceSecondForm]
    ring
  have hlow : ∫ s in (0 : ℝ)..L, -2 * (∑ i, Fd i s + d / L ^ 2) =
      -2 * ν * g.sliceExpansion (γ 0) - 2 * (d / L) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hintsum
      intervalIntegrable_const, hFTC, hFbL, hFb0, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    field_simp
    ring
  have hdL : (d : ℝ) / L < C := by
    rw [div_lt_iff₀ hL]
    rw [div_lt_iff₀ hC] at hlt
    linarith
  have hsum_pos : 0 < ∑ i, ∫ s in (0 : ℝ)..L,
      g.varSpeed₂ (γ s) (deriv γ s) (W i s) (W' i s) 0 := by
    rw [← intervalIntegral.integral_finsetSum fun i _ => hint₂ i]
    rw [hlow] at hmono
    nlinarith
  have hlt0 : ∑ _i : Fin d, (0 : ℝ) < ∑ i, ∫ s in (0 : ℝ)..L,
      g.varSpeed₂ (γ s) (deriv γ s) (W i s) (W' i s) 0 := by
    rw [Finset.sum_const_zero]
    exact hsum_pos
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt hlt0
  -- a longer timelike curve
  obtain ⟨ε, hε, hpos, hlong⟩ := SecondDerivativeTest.exists_lt_integral_sqrt hL hε₀ (h1 i) (h2 i)
    (h3 i) (h4 i) (h5 i) hi
  have hεI : ε ∈ Icc 0 ε₀ := ⟨hε.1.le, hε.2⟩
  set c : ℝ → E := fun s => γ s + ε • W i s with hc
  have hcd (s : ℝ) : HasDerivAt c (deriv γ s + ε • W' i s) s :=
    (hγ.hasDerivAt s).add ((hWd i s).const_smul ε)
  have hderc : deriv c = fun s => deriv γ s + ε • W' i s := funext fun s => (hcd s).deriv
  have hcT : g.IsTimelikeCurve c L := by
    refine ⟨fun s hs => hU i ε s hεI hs, fun s _ => (hcd s).differentiableAt, ?_, fun s hs => ?_⟩
    · rw [hderc]
      exact (hγd.add ((hW'c i).const_smul ε)).continuousOn
    · rw [hderc]
      have h := hpos s hs
      simp only [varSpeed] at h
      linarith
  have hc0 : c 0 0 = τ := by
    simp only [hc, hW, hf, hEf, parallelField_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hF0, mul_zero, add_zero, hγ0]
  have hcL : c L = γ L := by
    simp only [hc, hW, hf, div_self hL.ne', sub_self, zero_smul, smul_zero, add_zero]
  have hle := hmax c L hcT hc0 hcL
  have heq : g.curveProperTime c L = ∫ s in (0 : ℝ)..L,
      Real.sqrt (g.varSpeed (γ s) (deriv γ s) (W i s) (W' i s) ε) := by
    unfold curveProperTime
    rw [hderc]
    rfl
  linarith

/-! ### Focusing incompleteness -/

/-- A normal geodesic segment has unit timelike velocity: `g(γ', γ') = −1` on `[0, L]`. -/
theorem IsGeodesicSegment.form_deriv_self (hγ : g.IsGeodesicSegment γ L) (hL : 0 ≤ L)
    {ν : ℝ} (hν : ν * ν = 1) (hn : deriv γ 0 = ν • g.sliceNormal (γ 0))
    (hq : (g.coefficient (γ 0))⁻¹ 0 0 < 0) :
    ∀ s ∈ Icc 0 L, g.form (γ s) (deriv γ s) (deriv γ s) = -1 := by
  intro s hs
  have hx0 : γ 0 ∈ U := hγ.mem 0 ⟨le_rfl, hL⟩
  rw [form_eq_of_parallel hγ (fun s _ => hγ.hasDerivAt_deriv s)
    (fun s _ => hγ.hasDerivAt_deriv s) (fun s hs => hγ.geodesic s hs)
    (fun s hs => hγ.geodesic s hs) s hs, hn]
  simp only [map_smul, smul_apply, smul_eq_mul, form_sliceNormal_self hx0 hq]
  linear_combination -hν

/-- **A timelike vector is transverse to the slices** where `x⁰` is a time function
(`g^{00} < 0`): its time component does not vanish. -/
theorem zero_ne_of_timelike {z : E} (hz : z ∈ U) (hq : (g.coefficient z)⁻¹ 0 0 < 0) {v : E}
    (hv : g.form z v v < 0) : v 0 ≠ 0 := by
  intro h0
  obtain ⟨e, he⟩ := g.signature z hz
  have hu : g.form z (g.sliceNormal z) (g.sliceNormal z) < 0 := by
    rw [form_sliceNormal_self hz hq]
    norm_num
  have horth : g.form z (g.sliceNormal z) v = 0 := by
    rw [form_sliceNormal hz, h0, mul_zero]
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  have h := Minkowski.pos_of_orthogonal he hu horth hv0
  linarith

/-- The proper time of a unit-speed curve is its parameter length. -/
theorem curveProperTime_eq_of_unit {c : ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hc : ∀ s ∈ Icc 0 T, g.form (c s) (deriv c s) (deriv c s) = -1) :
    g.curveProperTime c T = T := by
  unfold curveProperTime
  have h : ∀ s ∈ uIcc 0 T, Real.sqrt (-g.form (c s) (deriv c s) (deriv c s)) = 1 := by
    intro s hs
    rw [uIcc_of_le hT] at hs
    rw [hc s hs, neg_neg, Real.sqrt_one]
  rw [intervalIntegral.integral_congr h]
  simp

/-- **The time function increases along a normal geodesic**: if `x⁰` is a time function along the
segment and the segment starts with the velocity `ν n`, then `ν x⁰` increases along it. -/
theorem IsGeodesicSegment.time_lt (hγ : g.IsGeodesicSegment γ L) (hL : 0 < L) {ν : ℝ}
    (hν : ν * ν = 1) (hn : deriv γ 0 = ν • g.sliceNormal (γ 0))
    (htime : ∀ s ∈ Icc 0 L, (g.coefficient (γ s))⁻¹ 0 0 < 0) :
    0 < ν * (γ L 0 - γ 0 0) := by
  have hmem0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have huu := hγ.form_deriv_self hL.le hν hn (htime 0 hmem0)
  set φ : ℝ → ℝ := fun s => ν * deriv γ s 0 with hφ
  have hφc : Continuous φ := continuous_const.mul ((continuous_apply 0).comp hγ.continuous_deriv)
  have hφ0 : 0 < φ 0 := by
    simp only [hφ, hn, Pi.smul_apply, smul_eq_mul, sliceNormal_zero (htime 0 hmem0)]
    rw [← mul_assoc, hν, one_mul]
    exact Real.sqrt_pos.mpr (by linarith [htime 0 hmem0])
  have hφne (s : ℝ) (hs : s ∈ Icc 0 L) : φ s ≠ 0 := by
    have h := g.zero_ne_of_timelike (hγ.mem s hs) (htime s hs)
      (by rw [huu s hs]; norm_num : g.form (γ s) (deriv γ s) (deriv γ s) < 0)
    have hν0 : ν ≠ 0 := by
      rintro rfl
      simp at hν
    exact mul_ne_zero hν0 h
  have hφpos (s : ℝ) (hs : s ∈ Icc 0 L) : 0 < φ s := by
    by_contra hle
    push Not at hle
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hs.1 hφc.continuousOn ⟨hle, hφ0.le⟩
    exact hφne r ⟨hr.1, hr.2.trans hs.2⟩ hr0
  have hd (s : ℝ) : HasDerivAt (fun s => ν * γ s 0) (φ s) s := by
    have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ)
      0).hasFDerivAt.comp_hasDerivAt s (hγ.hasDerivAt s)).const_mul ν
    exact h
  have hmono : StrictMonoOn (fun s => ν * γ s 0) (Icc 0 L) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 L)
      (fun s _ => (hd s).continuousAt.continuousWithinAt) fun s hs => ?_
    rw [interior_Icc] at hs
    rw [(hd s).deriv]
    exact hφpos s (Ioo_subset_Icc_self hs)
  have h := hmono hmem0 ⟨hL.le, le_rfl⟩ hL
  simp only at h
  nlinarith

/-- **Focusing incompleteness** (the singularity theorem of Hawking, with the maximizing property
as a premise). Let `x⁰` be a time function on `U` (`g^{00} < 0`), let the timelike convergence
condition `Ric(v, v) ≥ 0` hold for every timelike `v`, and let the slice `Σ = {x⁰ = τ}` have
`ν θ ≤ −C < 0` everywhere (`ν = 1`: contracting towards the future; `ν = −1`: expanding, towards
the past). Assume that every point `p` of `U` to the `ν`-side of `Σ` is joined to `Σ` by a
`ν`-directed normal geodesic segment that maximizes the proper time among the timelike curves from
`Σ` to `p` — the property that global hyperbolicity with the Cauchy surface `Σ` supplies through
limit curves. Then **every `ν`-directed normal geodesic segment from `Σ` has proper length at most
`d/C`**: no such geodesic can be extended beyond the proper time `d/C`, so the space-time is
timelike geodesically incomplete in that direction. -/
theorem length_le_of_focusing {τ C ν : ℝ} (hν : ν * ν = 1) (hC : 0 < C)
    (htime : ∀ z ∈ U, (g.coefficient z)⁻¹ 0 0 < 0)
    (hRic : ∀ z ∈ U, ∀ v : E, g.form z v v < 0 →
      0 ≤ ∑ j, ∑ k, ricciOf g.coefficient z j k * v j * v k)
    (hθ : ∀ z ∈ U, z 0 = τ → ν * g.sliceExpansion z ≤ -C)
    (hmax : ∀ p ∈ U, 0 < ν * (p 0 - τ) → ∃ (σ : ℝ → E) (ℓ : ℝ), 0 < ℓ ∧
      g.IsGeodesicSegment σ ℓ ∧ σ 0 0 = τ ∧ deriv σ 0 = ν • g.sliceNormal (σ 0) ∧ σ ℓ = p ∧
      ∀ (c : ℝ → E) (T : ℝ), g.IsTimelikeCurve c T → c 0 0 = τ → c T = p →
        g.curveProperTime c T ≤ ℓ)
    {γ : ℝ → E} {L : ℝ} (hL : 0 < L) (hγ : g.IsGeodesicSegment γ L) (hγ0 : γ 0 0 = τ)
    (hn : deriv γ 0 = ν • g.sliceNormal (γ 0)) :
    L ≤ d / C := by
  have hmem0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have hmemL : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
  have huu := hγ.form_deriv_self hL.le hν hn (htime _ (hγ.mem 0 hmem0))
  have hpos := hγ.time_lt hL hν hn fun s hs => htime _ (hγ.mem s hs)
  rw [hγ0] at hpos
  obtain ⟨σ, ℓ, hℓ, hσ, hσ0, hσn, hσℓ, hσmax⟩ := hmax (γ L) (hγ.mem L hmemL) hpos
  -- `γ` is a timelike curve from the slice to `γ(L)` of proper time `L`
  have hγT : g.IsTimelikeCurve γ L :=
    ⟨fun s hs => hγ.mem s hs, fun s _ => (hγ.hasDerivAt s).differentiableAt,
      hγ.continuous_deriv.continuousOn, fun s hs => by rw [huu s hs]; norm_num⟩
  have hLℓ : L ≤ ℓ := by
    have h := hσmax γ L hγT hγ0 rfl
    rwa [curveProperTime_eq_of_unit hL.le huu] at h
  -- the maximizer is short
  have hσ0' : (0 : ℝ) ∈ Icc 0 ℓ := ⟨le_rfl, hℓ.le⟩
  have hσuu := hσ.form_deriv_self hℓ.le hν hσn (htime _ (hσ.mem 0 hσ0'))
  have hℓC := g.length_le_of_maximizing hν hC hℓ hσ hσ0 hσn (htime _ (hσ.mem 0 hσ0'))
    (fun s hs => hRic _ (hσ.mem s hs) _ (by rw [hσuu s hs]; norm_num))
    (hθ _ (hσ.mem 0 hσ0') hσ0) (fun c T hc hc0 hcT => hσmax c T hc hc0 (hcT.trans hσℓ))
  linarith

/-! ### Synchronous metrics: the time lines maximize -/

namespace IsSynchronous

variable (hs : g.IsSynchronous) {z : MinkowskiModel d}
include hs

theorem coefficient_inv_zero_zero (hz : z ∈ U) : (g.coefficient z)⁻¹ 0 0 = -1 := by
  simpa using hs.inv_zero hz 0

/-- The unit normal of the slices of a synchronous metric is `e₀`. -/
theorem sliceNormal_eq (hz : z ∈ U) : g.sliceNormal z = Pi.single 0 1 := by
  funext k
  simp only [sliceNormal, hs.coefficient_inv_zero_zero hz, neg_neg, Real.sqrt_one, inv_one,
    hs.inv_zero_right hz, Pi.single_apply]
  split_ifs <;> simp

/-- The second fundamental form of the slices of a synchronous metric is `½ ∂_t γ_{αβ}`. -/
theorem sliceSecondForm_eq (hz : z ∈ U) (α β : Fin d) :
    g.sliceSecondForm z (Pi.single α.succ 1) (Pi.single β.succ 1) = g.metricRate z α β / 2 := by
  rw [sliceSecondForm, hs.sliceNormal_eq hz, form_single_right', chr_single, Fin.sum_univ_succ,
    hs.coefficient_zero_right hz 0]
  simp only [ite_true, Fin.succ_ne_zero, ite_false, hs.coefficient_zero_right hz, zero_mul,
    Finset.sum_const_zero, add_zero, neg_one_mul, neg_neg, hs.christoffel_zero_succ_succ hz]

/-- **The expansion of the slices of a synchronous metric is the expansion of its time lines**,
`θ = ½ κ^α_α`. -/
theorem sliceExpansion_eq (hz : z ∈ U) : g.sliceExpansion z = g.expansion z := by
  rw [sliceExpansion, expansion, Finset.sum_div]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [extrinsicRate, Finset.sum_div]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [hs.sliceSecondForm_eq hz, hs.inv_spatialCoefficient hz, Matrix.of_apply, metricRate]
  ring

/-- **The proper-time rate is at most the rate of the time**: `−g(v, v) ≤ (v⁰)²` in a synchronous
metric. -/
theorem neg_form_le (hz : z ∈ U) (v : E) : -g.form z v v ≤ v 0 ^ 2 := by
  have hpos := hs.spatialCoefficient_posDef hz
  have hsp : 0 ≤ g.form z (sliceVector fun α => v α.succ) (sliceVector fun α => v α.succ) := by
    rw [form_sliceVector]
    have h := hpos.posSemidef.dotProduct_mulVec_nonneg (fun α => v α.succ)
    simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at h
    convert h using 1
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    ring
  have hv : v = v 0 • (Pi.single 0 1 : E) + sliceVector fun α => v α.succ := by
    funext k
    refine Fin.cases ?_ (fun α => ?_) k
    · simp
    · simp [Fin.succ_ne_zero]
  have h0 (w : E) (hw : w 0 = 0) : g.form z (Pi.single 0 1) w = 0 := by
    rw [g.form_comm hz, form_single_right', Fin.sum_univ_succ, hs.coefficient_zero_right hz 0,
      hw, mul_zero, zero_add]
    exact Finset.sum_eq_zero fun α _ => by
      simp [hs.coefficient_zero_right hz, Fin.succ_ne_zero]
  have h00 : g.form z (Pi.single 0 1) (Pi.single 0 1) = -1 := (hs z hz).1
  set X : E := sliceVector fun α => v α.succ
  have hX : X 0 = 0 := rfl
  have hform : g.form z v v = -(v 0) ^ 2 + g.form z X X := by
    conv_lhs => rw [hv]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, h00, h0 X hX,
      g.form_comm hz X (Pi.single 0 1)]
    ring
  rw [hform]
  linarith

omit hs in
/-- A continuous function on `[a, b]` without zeros keeps the sign it has at `a`. -/
theorem pos_of_ne_zero {φ : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn φ (Icc a b))
    (hne : ∀ s ∈ Icc a b, φ s ≠ 0) (ha : 0 < φ a) : ∀ s ∈ Icc a b, 0 < φ s := by
  intro s hs
  by_contra hle
  push Not at hle
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hs.1 (hc.mono (Icc_subset_Icc le_rfl hs.2))
    ⟨hle, ha.le⟩
  exact hne r ⟨hr.1, hr.2.trans hs.2⟩ hr0

/-- **The time lines of a synchronous metric maximize the proper time**: every timelike curve on
`[0, T]` has proper time at most `|Δx⁰|`, the proper time of the time line between the slices of
its end points. -/
theorem curveProperTime_le {c : ℝ → E} {T : ℝ} (hT : 0 ≤ T) (hc : g.IsTimelikeCurve c T) :
    g.curveProperTime c T ≤ |c T 0 - c 0 0| := by
  set h : ℝ → ℝ := fun s => deriv c s 0 with hh
  have hhc : ContinuousOn h (Icc 0 T) :=
    ((continuous_apply 0).comp_continuousOn hc.continuousOn_deriv)
  have hcc : ContinuousOn c (Icc 0 T) :=
    fun s hs => (hc.differentiableAt s hs).continuousAt.continuousWithinAt
  have hle (s : ℝ) (hs' : s ∈ Icc 0 T) :
      Real.sqrt (-g.form (c s) (deriv c s) (deriv c s)) ≤ |h s| := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (hs.neg_form_le (hc.mem s hs') _)
  have hne (s : ℝ) (hs' : s ∈ Icc 0 T) : h s ≠ 0 := by
    intro h0
    have h1 := hs.neg_form_le (hc.mem s hs') (deriv c s)
    have h2 := hc.timelike s hs'
    simp only [hh] at h0
    rw [h0] at h1
    linarith
  have hd (s : ℝ) (hs' : s ∈ Icc 0 T) : HasDerivAt (fun s => c s 0) (h s) s :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ)
      0).hasFDerivAt.comp_hasDerivAt s (hc.differentiableAt s hs').hasDerivAt
  have hint : IntervalIntegrable h volume 0 T :=
    (hhc.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  have hFTC : ∫ s in (0 : ℝ)..T, h s = c T 0 - c 0 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs' => hd s (by rwa [uIcc_of_le hT] at hs')) hint
  have hmono := intervalIntegral.integral_mono_on hT
    ((continuousOn_form_apply (g := g) hcc hc.mem hc.continuousOn_deriv
      hc.continuousOn_deriv).neg.sqrt.mono (by rw [uIcc_of_le hT])).intervalIntegrable
    (hint.abs) hle
  unfold curveProperTime
  refine hmono.trans (le_of_eq ?_)
  have hmem0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  rcases lt_or_gt_of_ne (hne 0 hmem0) with hneg | hpos
  · have hall := pos_of_ne_zero (φ := fun s => -h s) hhc.neg (fun s hs' => neg_ne_zero.mpr
      (hne s hs')) (by simpa using hneg)
    have habs : ∀ s ∈ uIcc 0 T, |h s| = -h s := fun s hs' =>
      abs_of_neg (by have := hall s (by rwa [uIcc_of_le hT] at hs'); simp at this; linarith)
    rw [intervalIntegral.integral_congr habs, intervalIntegral.integral_neg, hFTC, abs_of_nonpos]
    have h1 := intervalIntegral.integral_nonneg (μ := volume) hT (fun s hs' => (hall s hs').le)
    simp only [intervalIntegral.integral_neg, hFTC] at h1
    linarith
  · have hall := pos_of_ne_zero hhc hne hpos
    have habs : ∀ s ∈ uIcc 0 T, |h s| = h s := fun s hs' =>
      abs_of_pos (hall s (by rwa [uIcc_of_le hT] at hs'))
    rw [intervalIntegral.integral_congr habs, hFTC, abs_of_nonneg]
    have h1 := intervalIntegral.integral_nonneg (μ := volume) hT (fun s hs' => (hall s hs').le)
    rw [hFTC] at h1
    exact h1

/-- **The time lines of a synchronous metric are geodesic segments.** -/
theorem isGeodesicSegment_timeLine {x₀ : E} {ν L : ℝ}
    (hmem : ∀ s ∈ Icc 0 L, x₀ + (ν * s) • (Pi.single 0 1 : E) ∈ U) :
    g.IsGeodesicSegment (fun s => x₀ + (ν * s) • (Pi.single 0 1 : E)) L := by
  have hd (s : ℝ) : HasDerivAt (fun s => x₀ + (ν * s) • (Pi.single 0 1 : E))
      (ν • (Pi.single 0 1 : E)) s := by
    have h := (((hasDerivAt_id' s).const_mul ν).smul_const (Pi.single 0 1 : E)).const_add x₀
    rwa [mul_one] at h
  have hderiv : deriv (fun s => x₀ + (ν * s) • (Pi.single 0 1 : E)) =
      fun _ => ν • (Pi.single 0 1 : E) := funext fun s => (hd s).deriv
  refine ⟨by fun_prop, hmem, fun s hs' => ?_⟩
  have h0 : g.chr (x₀ + (ν * s) • Pi.single 0 1) (Pi.single 0 1) (Pi.single 0 1) = 0 := by
    rw [chr_single]
    exact funext fun l => hs.christoffel_zero_zero (hmem s hs') l
  rw [hderiv, deriv_const]
  simp only [map_smul, smul_apply, h0, smul_zero, neg_zero]

/-- **Focusing incompleteness in a synchronous metric**: on a domain that contains the time lines
between the slice `x⁰ = τ` and each of its points, with the timelike convergence condition and
`ν θ ≤ −C < 0` on the slice, every `ν`-directed normal geodesic segment from the slice has length
at most `d/C`. The maximizing premise of `length_le_of_focusing` holds: the time lines maximize the
proper time (`curveProperTime_le`). -/
theorem length_le_of_focusing {τ C ν : ℝ} (hν : ν * ν = 1) (hC : 0 < C)
    (hU : ∀ z ∈ U, ∀ t ∈ uIcc τ (z 0), z + (t - z 0) • (Pi.single 0 1 : E) ∈ U)
    (hRic : ∀ z ∈ U, ∀ v : E, g.form z v v < 0 →
      0 ≤ ∑ j, ∑ k, ricciOf g.coefficient z j k * v j * v k)
    (hθ : ∀ z ∈ U, z 0 = τ → ν * g.expansion z ≤ -C)
    {γ : ℝ → E} {L : ℝ} (hL : 0 < L) (hγ : g.IsGeodesicSegment γ L) (hγ0 : γ 0 0 = τ)
    (hn : deriv γ 0 = ν • (Pi.single 0 1 : E)) :
    L ≤ d / C := by
  have hγU : γ 0 ∈ U := hγ.mem 0 ⟨le_rfl, hL.le⟩
  have htime : ∀ z ∈ U, (g.coefficient z)⁻¹ 0 0 < 0 := fun z hz => by
    rw [hs.coefficient_inv_zero_zero hz]
    norm_num
  have hθ' : ∀ z ∈ U, z 0 = τ → ν * g.sliceExpansion z ≤ -C := fun z hz hz0 => by
    rw [hs.sliceExpansion_eq hz]
    exact hθ z hz hz0
  have hn' : deriv γ 0 = ν • g.sliceNormal (γ 0) := by
    rw [hs.sliceNormal_eq hγU]
    exact hn
  refine g.length_le_of_focusing hν hC htime hRic hθ' ?_ hL hγ hγ0 hn'
  intro p hp hpν
  have hν1 : |ν| = 1 := by
    have h : |ν| * |ν| = 1 := by rw [← abs_mul, hν, abs_one]
    nlinarith [abs_nonneg ν]
  set ℓ := ν * (p 0 - τ) with hℓ
  set σ : ℝ → E := fun s => (p + (τ - p 0) • (Pi.single 0 1 : E)) + (ν * s) • Pi.single 0 1
    with hσ
  have hσt (s : ℝ) : σ s = p + (τ - p 0 + ν * s) • (Pi.single 0 1 : E) := by
    simp only [hσ, add_smul, add_assoc]
  have hσmem : ∀ s ∈ Icc 0 ℓ, σ s ∈ U := by
    intro s hs'
    rw [hσt]
    have h := hU p hp (τ + ν * s) ?_
    · convert h using 3
      ring
    · rw [mem_uIcc]
      have hνs : ν * (ν * s) = s := by rw [← mul_assoc, hν, one_mul]
      rcases le_or_gt 0 ν with hν0 | hν0
      · have hν' : ν = 1 := by nlinarith
        subst hν'
        left
        constructor <;> nlinarith [hs'.1, hs'.2]
      · have hν' : ν = -1 := by nlinarith
        subst hν'
        right
        constructor <;> nlinarith [hs'.1, hs'.2]
  have hσseg := hs.isGeodesicSegment_timeLine hσmem
  refine ⟨σ, ℓ, hpν, hσseg, ?_, ?_, ?_, fun c T hcT hc0 hcp => ?_⟩
  · simp [hσ]
  · rw [hs.sliceNormal_eq (hσseg.mem 0 ⟨le_rfl, hpν.le⟩)]
    exact (hσseg.hasDerivAt 0).deriv.trans (by
      have h := (((hasDerivAt_id' (0 : ℝ)).const_mul ν).smul_const (Pi.single 0 1 : E)).const_add
        (p + (τ - p 0) • (Pi.single 0 1 : E))
      rw [mul_one] at h
      exact h.deriv)
  · rw [hσt, hℓ, ← mul_assoc, hν, one_mul]
    simp
  · rcases lt_or_ge T 0 with hT | hT
    · have h1 : g.curveProperTime c T ≤ 0 := by
        unfold curveProperTime
        rw [intervalIntegral.integral_symm, neg_nonpos]
        exact intervalIntegral.integral_nonneg hT.le fun s _ => Real.sqrt_nonneg _
      linarith
    have h := hs.curveProperTime_le hT hcT
    rw [hcp, hc0] at h
    refine h.trans (le_of_eq ?_)
    rw [hℓ, abs_eq_abs.mpr (Or.inl rfl)]
    rw [show |p 0 - τ| = |ν| * |p 0 - τ| by rw [hν1, one_mul], ← abs_mul]
    exact abs_of_pos hpν

end IsSynchronous

end ProjectAinos.SmoothGeometry.CoordinateMetric
