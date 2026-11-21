/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.CollapseHorizon

/-! Public consumers of the Einstein equations across the boundary of a collapsing body and of its
event horizon (Landau–Lifshitz §102): the Einstein tensor of a coordinate metric under a change of
co-ordinates and the pullback metric; the distributional Einstein tensor of a metric glued along a
hyperplane, its surface term `−ε([K_ab] − h_ab[K])`, the weak Einstein equations and the `C¹`
criterion; the adapted chart of the Oppenheimer–Snyder junction, the glued metric, its weak
Einstein equations and a genuine surface layer; the spacetime of the collapse in the chart of
Painlevé and Gullstrand, its future causal curves, the generator of the horizon, non-escape below
it, escape above it, and the event horizon as the boundary of the causal past of future null
infinity. Default elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology Real InnerProductSpace Manifold
open ProjectAinos.SmoothGeometry ProjectAinos.SmoothGeometry.CoordinateMetric
  ProjectAinos.GeneralRelativity ProjectAinos.GeneralRelativity.Collapse
  ProjectAinos.GeneralRelativity.CollapseJunction ProjectAinos.GeneralRelativity.CollapseHorizon

example :
    {d : ℕ} →
      {U V : Opens (MinkowskiModel d)} →
        (F : MinkowskiModel d → MinkowskiModel d) → MapsTo F ↑U ↑V → ↥U → ↥V :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.restrictMap

example :
    ∀ {d : ℕ} {U V : Opens (MinkowskiModel d)} {F : MinkowskiModel d → MinkowskiModel d},
      ContDiffOn ℝ ∞ F ↑U →
        ∀ (hm : MapsTo F ↑U ↑V),
          ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ (restrictMap F hm) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.contMDiff_restrictMap

example :
    ∀ {d : ℕ} {U V : Opens (MinkowskiModel d)} {F : MinkowskiModel d → MinkowskiModel d},
      ContDiffOn ℝ ∞ F ↑U →
        ∀ (hm : MapsTo F ↑U ↑V) (z : ↥U) (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) z),
          (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (restrictMap F hm) z) v =
            (fderiv ℝ F ↑z) v :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.mfderiv_restrictMap

example :
    ∀ {d : ℕ} (B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ) (v w : MinkowskiModel d),
      (B v) w =
        ∑ a : Fin (d + 1), ∑ b : Fin (d + 1), (B (Pi.single a 1)) (Pi.single b 1) * v a * w b :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.bilinear_eq_sum

example :
    ∀ {σ : LorentzConvention} {d : ℕ} {U V : Opens (MinkowskiModel d)}
      (g : CoordinateMetric σ d V) (g' : CoordinateMetric σ d U)
      {F : MinkowskiModel d → MinkowskiModel d},
      (∀ x ∈ U,
          ∀ (v w : MinkowskiModel d),
            ((g'.form x) v) w = ((g.form (F x)) ((fderiv ℝ F x) v)) ((fderiv ℝ F x) w)) →
        ∀ {x : MinkowskiModel d},
          x ∈ U →
            ∀ (i k : Fin (d + 1)),
              g'.coefficient x i k =
                ∑ a : Fin (d + 1),
                  ∑ b : Fin (d + 1),
                    g.coefficient (F x) a b * (fderiv ℝ F x) (Pi.single i 1) a *
                      (fderiv ℝ F x) (Pi.single k 1) b :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.coefficient_pullback

example :
    ∀ {σ : LorentzConvention} {d : ℕ} {U V : Opens (MinkowskiModel d)}
      (g : CoordinateMetric σ d V) (g' : CoordinateMetric σ d U)
      {F : MinkowskiModel d → MinkowskiModel d},
      ContDiffOn ℝ ∞ F ↑U →
        MapsTo F ↑U ↑V →
          (∀ x ∈ U,
              ∀ (v w : MinkowskiModel d),
                ((g'.form x) v) w = ((g.form (F x)) ((fderiv ℝ F x) v)) ((fderiv ℝ F x) w)) →
            ∀ {x : MinkowskiModel d},
              x ∈ U →
                ∀ (i k : Fin (d + 1)),
                  einsteinOf g'.coefficient x i k =
                    ∑ a : Fin (d + 1),
                      ∑ b : Fin (d + 1),
                        einsteinOf g.coefficient (F x) a b * (fderiv ℝ F x) (Pi.single i 1) a *
                          (fderiv ℝ F x) (Pi.single k 1) b :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.einsteinOf_pullback

example :
    {d : ℕ} →
      (MinkowskiModel d → MinkowskiModel d) →
        (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) →
          MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.pullbackTensor

example :
    ∀ {σ : LorentzConvention} {d : ℕ} {U V : Opens (MinkowskiModel d)}
      (g : CoordinateMetric σ d V) (g' : CoordinateMetric σ d U)
      {F : MinkowskiModel d → MinkowskiModel d} {κ Λ : ℝ}
      {T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ},
      g.IsEinstein κ Λ T →
        ContDiffOn ℝ ∞ F ↑U →
          MapsTo F ↑U ↑V →
            (∀ x ∈ U,
                ∀ (v w : MinkowskiModel d),
                  ((g'.form x) v) w = ((g.form (F x)) ((fderiv ℝ F x) v)) ((fderiv ℝ F x) w)) →
              g'.IsEinstein κ Λ (pullbackTensor F T) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.IsEinstein.pullback

example :
    {σ : LorentzConvention} →
      {d : ℕ} →
        {U V : Opens (MinkowskiModel d)} →
          CoordinateMetric σ d V →
            (F : MinkowskiModel d → MinkowskiModel d) →
              ContDiffOn ℝ ∞ F ↑U →
                MapsTo F ↑U ↑V → (∀ x ∈ U, (fderiv ℝ F x).IsInvertible) → CoordinateMetric σ d U :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.pullback

example :
    ∀ {σ : LorentzConvention} {d : ℕ} {U V : Opens (MinkowskiModel d)}
      (g : CoordinateMetric σ d V) {F : MinkowskiModel d → MinkowskiModel d}
      (hF : ContDiffOn ℝ ∞ F ↑U) (hm : MapsTo F ↑U ↑V)
      (hinv : ∀ x ∈ U, (fderiv ℝ F x).IsInvertible) (x v w : MinkowskiModel d),
      (((g.pullback F hF hm hinv).form x) v) w =
        ((g.form (F x)) ((fderiv ℝ F x) v)) ((fderiv ℝ F x) w) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.pullback_form_apply

example :
    ∀ {σ : LorentzConvention} {d : ℕ} {U V : Opens (MinkowskiModel d)}
      (g : CoordinateMetric σ d V) {F : MinkowskiModel d → MinkowskiModel d}
      (hF : ContDiffOn ℝ ∞ F ↑U) (hm : MapsTo F ↑U ↑V)
      (hinv : ∀ x ∈ U, (fderiv ℝ F x).IsInvertible) {κ Λ : ℝ}
      {T : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ},
      g.IsEinstein κ Λ T → (g.pullback F hF hm hinv).IsEinstein κ Λ (pullbackTensor F T) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.IsEinstein.pullback_metric

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) (c : ℝ), volume {x : MinkowskiModel d | x k = c} = 0 :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.volume_hyperplane

example :
    ∀ {d : ℕ} {K : Set (MinkowskiModel d)},
      IsCompact K → ∃ (L : ℝ), 0 < L ∧ ∀ x ∈ K, ∀ (j : Fin (d + 1)), |x j| < L :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.exists_abs_lt_of_isCompact

example :
    ∀ {d : ℕ} {K : Set (MinkowskiModel d)} {f : MinkowskiModel d → ℝ},
      IsCompact K → (∀ x ∉ K, f x = 0) → ∀ {x : MinkowskiModel d}, x ∉ K → fderiv ℝ f x = 0 :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.fderiv_eq_zero_of_notMem_isCompact

example :
    ∀ {d : ℕ} {O K : Set (MinkowskiModel d)} {f : MinkowskiModel d → ℝ},
      IsOpen O →
        ContDiffOn ℝ 1 f O →
          IsCompact K →
            (∀ x ∉ K, f x = 0) →
              ∀ {x : MinkowskiModel d}, x ∈ O ∨ x ∉ K → DifferentiableAt ℝ f x :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.differentiableAt_of_mem_or_notMem

example :
    ∀ {d : ℕ} {O K : Set (MinkowskiModel d)} {f : MinkowskiModel d → ℝ},
      IsOpen O →
        ContDiffOn ℝ 1 f O →
          IsCompact K →
            (∀ x ∉ K, f x = 0) →
              ∀ {x : MinkowskiModel d},
                x ∈ O ∨ x ∉ K →
                  ∀ (v : MinkowskiModel d),
                    ContinuousAt (fun (y : MinkowskiModel d) => (fderiv ℝ f y) v) x :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.continuousAt_fderiv_of_mem_or_notMem

example :
    ∀ {d : ℕ} {V : Fin (d + 1) → MinkowskiModel d → ℝ} {O K : Set (MinkowskiModel d)},
      IsOpen O →
        ∀ (k : Fin (d + 1)),
          (∀ (i : Fin (d + 1)), ContDiffOn ℝ 1 (V i) O) →
            IsCompact K →
              (∀ (i : Fin (d + 1)), ∀ x ∉ K, V i x = 0) →
                (∀ x ∈ K, 0 ≤ x k → x ∈ O) →
                  ∫ (x : MinkowskiModel d) in {x : MinkowskiModel d | 0 < x k},
                      ∑ i : Fin (d + 1), (fderiv ℝ (V i) x) (Pi.single i 1) =
                    -∫ (y : Fin d → ℝ), V k (k.insertNth 0 y) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.integral_divergence_upper

example :
    ∀ {d : ℕ} {V : Fin (d + 1) → MinkowskiModel d → ℝ} {O K : Set (MinkowskiModel d)},
      IsOpen O →
        ∀ (k : Fin (d + 1)),
          (∀ (i : Fin (d + 1)), ContDiffOn ℝ 1 (V i) O) →
            IsCompact K →
              (∀ (i : Fin (d + 1)), ∀ x ∉ K, V i x = 0) →
                (∀ x ∈ K, x k ≤ 0 → x ∈ O) →
                  ∫ (x : MinkowskiModel d) in {x : MinkowskiModel d | x k < 0},
                      ∑ i : Fin (d + 1), (fderiv ℝ (V i) x) (Pi.single i 1) =
                    ∫ (y : Fin d → ℝ), V k (k.insertNth 0 y) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.integral_divergence_lower

example :
    {d : ℕ} →
      Fin (d + 1) →
        (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) →
          (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) →
            MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.glue

example :
    {d : ℕ} →
      (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) →
        (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) →
          MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.traceReverse

example :
    {d : ℕ} →
      (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) →
        (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) → MinkowskiModel d → ℝ :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.weakEinsteinDensity

example :
    {d : ℕ} →
      (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) →
        (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) → ℝ :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.weakEinstein

example :
    {d : ℕ} →
      Set (MinkowskiModel d) → (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) → Prop :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.IsTestDensity

example :
    {d : ℕ} →
      Set (MinkowskiModel d) →
        (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) →
          ℝ → (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) → Prop :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.IsWeakEinstein

example :
    {d : ℕ} →
      (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) →
        (MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) →
          Fin (d + 1) → MinkowskiModel d → ℝ :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.weakFlux

example :
    ∀ {n : ℕ} (X : Fin n → Fin n → Fin n → ℝ),
      ∑ j : Fin n, ∑ l : Fin n, ∑ i : Fin n, X i j l =
        ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, X i j l :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.sum_rotate

example :
    ∀ {n : ℕ} (Γ : Fin n → Fin n → Fin n → ℝ) (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ)
      (Φ : Fin n → Fin n → ℝ) (dΦ : Fin n → Fin n → Fin n → ℝ),
      ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, (-(Γ i j l * dΦ j l i) + Γ i i l * dΦ j l j) +
          ∑ j : Fin n,
            ∑ l : Fin n,
              (∑ i : Fin n, ∑ a : Fin n, (Γ i i a * Γ a j l - Γ i j a * Γ a i l)) * Φ j l =
        ∑ i : Fin n,
            (-∑ j : Fin n, ∑ l : Fin n, (dΓ i j l i * Φ j l + Γ i j l * dΦ j l i) +
              ∑ m : Fin n, ∑ l : Fin n, (dΓ m m l i * Φ i l + Γ m m l * dΦ i l i)) +
          ∑ j : Fin n,
            ∑ l : Fin n,
              (∑ i : Fin n,
                  (dΓ i j l i - dΓ i i l j +
                    ∑ a : Fin n, (Γ i i a * Γ a j l - Γ i j a * Γ a i l))) *
                Φ j l :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.weak_algebra

example :
    ∀ {d : ℕ} (C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      (x : MinkowskiModel d),
      ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), ricciOf C x j l * traceReverse C φ x j l =
        ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), einsteinOf C x j l * φ x j l :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.sum_ricciOf_mul_traceReverse

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) {C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ},
      C * C⁻¹ = 1 →
        ∀ {ε : ℝ},
          (∀ (μ : Fin (d + 1)), C μ k = if μ = k then ε else 0) →
            ∀ (a b : Fin d),
              (Matrix.of fun (a b : Fin d) => C (k.succAbove a) (k.succAbove b))⁻¹ a b =
                C⁻¹ (k.succAbove a) (k.succAbove b) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.inv_succAbove_eq

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) {ε : ℝ} {r : Fin (d + 1) → ℝ},
      (∀ (μ : Fin (d + 1)), r μ = if μ = k then ε else 0) →
        ∀ (f : Fin (d + 1) → ℝ), ∑ μ : Fin (d + 1), r μ * f μ = ε * f k :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.sum_row_mul

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) (f : Fin (d + 1) → Fin (d + 1) → ℝ),
      ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), f j l =
        f k k + ∑ b : Fin d, f k (k.succAbove b) +
          ∑ a : Fin d, (f (k.succAbove a) k + ∑ b : Fin d, f (k.succAbove a) (k.succAbove b)) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.sum_sum_succAbove

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) {C Ci γ φ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} {ε : ℝ},
      ε * ε = 1 →
        (∀ (μ : Fin (d + 1)), C k μ = if μ = k then ε else 0) →
          (∀ (μ : Fin (d + 1)), C μ k = if μ = k then ε else 0) →
            (∀ (μ : Fin (d + 1)), Ci k μ = if μ = k then ε else 0) →
              (∀ (μ : Fin (d + 1)), Ci μ k = if μ = k then ε else 0) →
                (∀ (p q : Fin (d + 1)), γ p q = γ q p) →
                  ∑ j : Fin (d + 1),
                        ∑ l : Fin (d + 1),
                          (∑ m : Fin (d + 1),
                              Ci k m *
                                ((((if j = k then γ l m else 0) + if l = k then γ m j else 0) -
                                    if m = k then γ j l else 0) /
                                  2)) *
                            (φ j l -
                              (∑ m : Fin (d + 1), ∑ n : Fin (d + 1), C m n * φ m n) / 2 *
                                Ci j l) -
                      ∑ l : Fin (d + 1),
                        (∑ m : Fin (d + 1),
                            ∑ p : Fin (d + 1),
                              Ci m p *
                                ((((if m = k then γ l p else 0) + if l = k then γ p m else 0) -
                                    if p = k then γ m l else 0) /
                                  2)) *
                          (φ k l -
                            (∑ m : Fin (d + 1), ∑ n : Fin (d + 1), C m n * φ m n) / 2 *
                              Ci k l) =
                    -ε *
                      ∑ a : Fin d,
                        ∑ b : Fin d,
                          (γ (k.succAbove a) (k.succAbove b) / 2 -
                              C (k.succAbove a) (k.succAbove b) *
                                ∑ c : Fin d,
                                  ∑ e : Fin d,
                                    Ci (k.succAbove c) (k.succAbove e) *
                                      (γ (k.succAbove c) (k.succAbove e) / 2)) *
                            φ (k.succAbove a) (k.succAbove b) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.jump_algebra

example :
    ∀ {d : ℕ} {σ : LorentzConvention} {U : Opens (MinkowskiModel d)}
      (g : CoordinateMetric σ d U)
      {φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ},
      (∀ (j l : Fin (d + 1)), ContDiff ℝ ∞ fun (x : MinkowskiModel d) => φ x j l) →
        ∀ (j l : Fin (d + 1)),
          ContDiffOn ℝ ∞ (fun (x : MinkowskiModel d) => traceReverse g.coefficient φ x j l) ↑U :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.contDiffOn_traceReverse

example :
    ∀ {d : ℕ} {σ : LorentzConvention} {U : Opens (MinkowskiModel d)}
      (g : CoordinateMetric σ d U)
      {φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ},
      (∀ (j l : Fin (d + 1)), ContDiff ℝ ∞ fun (x : MinkowskiModel d) => φ x j l) →
        ∀ (i : Fin (d + 1)), ContDiffOn ℝ ∞ (weakFlux g.coefficient φ i) ↑U :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.contDiffOn_weakFlux

example :
    ∀ {d : ℕ} {σ : LorentzConvention} {U : Opens (MinkowskiModel d)}
      (g : CoordinateMetric σ d U)
      {φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ},
      (∀ (j l : Fin (d + 1)), ContDiff ℝ ∞ fun (x : MinkowskiModel d) => φ x j l) →
        ∀ {x : MinkowskiModel d},
          x ∈ U →
            weakEinsteinDensity g.coefficient φ x =
              ∑ i : Fin (d + 1), (fderiv ℝ (weakFlux g.coefficient φ i) x) (Pi.single i 1) +
                ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), einsteinOf g.coefficient x j l * φ x j l :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.weakEinsteinDensity_eq_of_mem

example :
    ∀ {d : ℕ} {C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
      {y : MinkowskiModel d}, φ y = 0 → traceReverse C φ y = 0 :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.traceReverse_eq_zero

example :
    ∀ {d : ℕ} {C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
      {x : MinkowskiModel d},
      x ∉ tsupport φ →
        ∀ (j l : Fin (d + 1)),
          (fun (y : MinkowskiModel d) => traceReverse C φ y j l) =ᶠ[𝓝 x]
            fun (_ : MinkowskiModel d) => 0 :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.traceReverse_eventuallyEq_zero

example :
    ∀ {d : ℕ} {C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
      {x : MinkowskiModel d},
      x ∉ tsupport φ →
        ∀ (j l : Fin (d + 1)),
          fderiv ℝ (fun (y : MinkowskiModel d) => traceReverse C φ y j l) x = 0 :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.fderiv_traceReverse_eq_zero

example :
    ∀ {d : ℕ} {C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
      {x : MinkowskiModel d},
      x ∉ tsupport φ → ∀ (i : Fin (d + 1)), fderiv ℝ (weakFlux C φ i) x = 0 :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.fderiv_weakFlux_eq_zero

example :
    ∀ {d : ℕ} {C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
      {x : MinkowskiModel d}, x ∉ tsupport φ → weakEinsteinDensity C φ x = 0 :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.weakEinsteinDensity_eq_zero

example :
    ∀ {d : ℕ} {C φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
      {y : MinkowskiModel d}, φ y = 0 → ∀ (i : Fin (d + 1)), weakFlux C φ i y = 0 :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.weakFlux_eq_zero

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) {f h : MinkowskiModel d → ℝ} {W : Set (MinkowskiModel d)},
      IsOpen W →
        ∀ {z : MinkowskiModel d},
          z ∈ W →
            z k = 0 →
              (∀ y ∈ W, y k = 0 → f y = h y) →
                DifferentiableAt ℝ f z →
                  DifferentiableAt ℝ h z →
                    ∀ {j : Fin (d + 1)},
                      j ≠ k → (fderiv ℝ f z) (Pi.single j 1) = (fderiv ℝ h z) (Pi.single j 1) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.fderiv_eq_of_eqOn_hyperplane

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) {C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ},
      C * C⁻¹ = 1 →
        ∀ {ε : ℝ},
          ε * ε = 1 →
            (∀ (μ : Fin (d + 1)), C k μ = if μ = k then ε else 0) →
              ∀ (μ : Fin (d + 1)), C⁻¹ k μ = if μ = k then ε else 0 :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.inv_row_eq

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) {C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ},
      C⁻¹ * C = 1 →
        ∀ {ε : ℝ},
          ε * ε = 1 →
            (∀ (μ : Fin (d + 1)), C μ k = if μ = k then ε else 0) →
              ∀ (μ : Fin (d + 1)), C⁻¹ μ k = if μ = k then ε else 0 :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.inv_col_eq

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) {σ : LorentzConvention} {Um Up : Opens (MinkowskiModel d)}
      (gm : CoordinateMetric σ d Um) (gp : CoordinateMetric σ d Up)
      {W : Set (MinkowskiModel d)},
      IsOpen W →
        W ⊆ ↑Um →
          W ⊆ ↑Up →
            ∀ {ε : ℝ},
              ε * ε = 1 →
                (∀ y ∈ W, y k = 0 → gm.coefficient y = gp.coefficient y) →
                  (∀ y ∈ W,
                      y k = 0 →
                        ∀ (μ : Fin (d + 1)), gp.coefficient y k μ = if μ = k then ε else 0) →
                    ∀ (φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
                      {z : MinkowskiModel d},
                      z ∈ W →
                        z k = 0 →
                          weakFlux gm.coefficient φ k z - weakFlux gp.coefficient φ k z =
                            -ε *
                              ∑ a : Fin d,
                                ∑ b : Fin d,
                                  (gp.secondFundamental k 1 z a b -
                                        gm.secondFundamental k 1 z a b -
                                      gp.inducedMetric k z a b *
                                        ∑ c : Fin d,
                                          ∑ e : Fin d,
                                            (gp.inducedMetric k z)⁻¹ c e *
                                              (gp.secondFundamental k 1 z c e -
                                                gm.secondFundamental k 1 z c e)) *
                                    φ z (k.succAbove a) (k.succAbove b) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.weakFlux_sub_weakFlux

example :
    ∀ {n : ℕ} {f : (Fin n → ℝ) → ℝ} {S K : Set (Fin n → ℝ)},
      IsClosed S →
        IsCompact K →
          (∀ x ∈ S ∩ K, ContinuousAt f x) → (∀ x ∈ S, x ∉ K → f x = 0) → IntegrableOn f S volume :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.integrableOn_of_continuousAt

example :
    ∀ {d : ℕ} {C C' φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
      {x : MinkowskiModel d},
      C =ᶠ[𝓝 x] C' → weakEinsteinDensity C φ x = weakEinsteinDensity C' φ x :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.weakEinsteinDensity_congr

example :
    ∀ {d : ℕ} (k : Fin (d + 1))
      (Cm Cp : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) {x : MinkowskiModel d},
      x k < 0 → glue k Cm Cp =ᶠ[𝓝 x] Cm :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.glue_eventuallyEq_left

example :
    ∀ {d : ℕ} (k : Fin (d + 1))
      (Cm Cp : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) {x : MinkowskiModel d},
      0 < x k → glue k Cm Cp =ᶠ[𝓝 x] Cp :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.glue_eventuallyEq_right

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) {σ : LorentzConvention} {Um Up : Opens (MinkowskiModel d)}
      (gm : CoordinateMetric σ d Um) (gp : CoordinateMetric σ d Up)
      {U : Set (MinkowskiModel d)},
      IsOpen U →
        (∀ x ∈ U, x k ≤ 0 → x ∈ Um) →
          (∀ x ∈ U, 0 ≤ x k → x ∈ Up) →
            ∀ {ε : ℝ},
              ε * ε = 1 →
                (∀ y ∈ U, y k = 0 → gm.coefficient y = gp.coefficient y) →
                  (∀ y ∈ U,
                      y k = 0 →
                        ∀ (μ : Fin (d + 1)), gp.coefficient y k μ = if μ = k then ε else 0) →
                    ∀ {φ : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ},
                      IsTestDensity U φ →
                        weakEinstein (glue k gm.coefficient gp.coefficient) φ =
                          ((∫ (x : MinkowskiModel d) in {x : MinkowskiModel d | x k < 0},
                                ∑ j : Fin (d + 1),
                                  ∑ l : Fin (d + 1),
                                    einsteinOf gm.coefficient x j l * φ x j l) +
                              ∫ (x : MinkowskiModel d) in {x : MinkowskiModel d | 0 < x k},
                                ∑ j : Fin (d + 1),
                                  ∑ l : Fin (d + 1),
                                    einsteinOf gp.coefficient x j l * φ x j l) -
                            ε *
                              ∫ (y : Fin d → ℝ),
                                ∑ a : Fin d,
                                  ∑ b : Fin d,
                                    (gp.secondFundamental k 1 (k.insertNth 0 y) a b -
                                          gm.secondFundamental k 1 (k.insertNth 0 y) a b -
                                        gp.inducedMetric k (k.insertNth 0 y) a b *
                                          ∑ c : Fin d,
                                            ∑ e : Fin d,
                                              (gp.inducedMetric k (k.insertNth 0 y))⁻¹ c e *
                                                (gp.secondFundamental k 1 (k.insertNth 0 y) c
                                                    e -
                                                  gm.secondFundamental k 1 (k.insertNth 0 y) c
                                                    e)) *
                                      φ (k.insertNth 0 y) (k.succAbove a) (k.succAbove b) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.weakEinstein_glue

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) {σ : LorentzConvention} {Um Up : Opens (MinkowskiModel d)}
      (gm : CoordinateMetric σ d Um) (gp : CoordinateMetric σ d Up)
      {U : Set (MinkowskiModel d)},
      IsOpen U →
        (∀ x ∈ U, x k ≤ 0 → x ∈ Um) →
          (∀ x ∈ U, 0 ≤ x k → x ∈ Up) →
            ∀ {ε : ℝ},
              ε * ε = 1 →
                (∀ y ∈ U, y k = 0 → gm.coefficient y = gp.coefficient y) →
                  (∀ y ∈ U,
                      y k = 0 →
                        ∀ (μ : Fin (d + 1)), gp.coefficient y k μ = if μ = k then ε else 0) →
                    (∀ y ∈ U,
                        y k = 0 → gp.secondFundamental k 1 y = gm.secondFundamental k 1 y) →
                      ∀ {κ : ℝ}
                        {Tm Tp : MinkowskiModel d → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ},
                        (∀ (j l : Fin (d + 1)),
                            ContinuousOn (fun (x : MinkowskiModel d) => Tm x j l) ↑Um) →
                          (∀ (j l : Fin (d + 1)),
                              ContinuousOn (fun (x : MinkowskiModel d) => Tp x j l) ↑Up) →
                            (∀ x ∈ U,
                                x k < 0 →
                                  ∀ (j l : Fin (d + 1)),
                                    einsteinOf gm.coefficient x j l = κ * Tm x j l) →
                              (∀ x ∈ U,
                                  0 < x k →
                                    ∀ (j l : Fin (d + 1)),
                                      einsteinOf gp.coefficient x j l = κ * Tp x j l) →
                                IsWeakEinstein U (glue k gm.coefficient gp.coefficient) κ
                                  (glue k Tm Tp) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.isWeakEinstein_glue

example :
    ∀ {d : ℕ} {L L' : MinkowskiModel d →L[ℝ] ℝ},
      (∀ (j : Fin (d + 1)), L (Pi.single j 1) = L' (Pi.single j 1)) → L = L' :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.clm_ext_single

example :
    ∀ {d : ℕ} (k : Fin (d + 1)), UniqueDiffOn ℝ {x : MinkowskiModel d | 0 ≤ x k} :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.uniqueDiffOn_upper

example :
    ∀ {d : ℕ} (k : Fin (d + 1)), UniqueDiffOn ℝ {x : MinkowskiModel d | x k ≤ 0} :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.uniqueDiffOn_lower

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) {f g : MinkowskiModel d → ℝ} {U Of Og : Set (MinkowskiModel d)},
      IsOpen U →
        IsOpen Of →
          IsOpen Og →
            ContDiffOn ℝ 1 f Of →
              ContDiffOn ℝ 1 g Og →
                (∀ x ∈ U, 0 ≤ x k → x ∈ Of) →
                  (∀ x ∈ U, x k ≤ 0 → x ∈ Og) →
                    (∀ y ∈ U, y k = 0 → f y = g y) →
                      (ContDiffOn ℝ 1
                          (fun (x : MinkowskiModel d) => if x k < 0 then g x else f x) U ↔
                        ∀ z ∈ U,
                          z k = 0 →
                            (fderiv ℝ f z) (Pi.single k 1) = (fderiv ℝ g z) (Pi.single k 1)) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.contDiffOn_glue_iff

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) {σ : LorentzConvention} {Um Up : Opens (MinkowskiModel d)}
      (gm : CoordinateMetric σ d Um) (gp : CoordinateMetric σ d Up)
      {U : Set (MinkowskiModel d)},
      IsOpen U →
        (∀ x ∈ U, x k ≤ 0 → x ∈ Um) →
          (∀ x ∈ U, 0 ≤ x k → x ∈ Up) →
            (∀ y ∈ U, y k = 0 → gm.coefficient y = gp.coefficient y) →
              ((∀ (p q : Fin (d + 1)),
                  ContDiffOn ℝ 1
                    (fun (x : MinkowskiModel d) => glue k gm.coefficient gp.coefficient x p q)
                    U) ↔
                ∀ z ∈ U,
                  z k = 0 →
                    ∀ (p q : Fin (d + 1)),
                      (fderiv ℝ (fun (x : MinkowskiModel d) => gp.coefficient x p q) z)
                          (Pi.single k 1) =
                        (fderiv ℝ (fun (x : MinkowskiModel d) => gm.coefficient x p q) z)
                          (Pi.single k 1)) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.contDiffOn_glue_coefficient_iff

example :
    ∀ {d : ℕ} (k : Fin (d + 1)) {σ : LorentzConvention} {Um Up : Opens (MinkowskiModel d)}
      (gm : CoordinateMetric σ d Um) (gp : CoordinateMetric σ d Up)
      {U : Set (MinkowskiModel d)},
      IsOpen U →
        (∀ x ∈ U, x k ≤ 0 → x ∈ Um) →
          (∀ x ∈ U, 0 ≤ x k → x ∈ Up) →
            ∀ {ε : ℝ},
              ε * ε = 1 →
                (∀ y ∈ U, y k = 0 → gm.coefficient y = gp.coefficient y) →
                  (∀ y ∈ U,
                      y k = 0 →
                        ∀ (μ : Fin (d + 1)), gp.coefficient y k μ = if μ = k then ε else 0) →
                    (∀ z ∈ U,
                        z k = 0 →
                          ∀ (μ : Fin (d + 1)),
                            (fderiv ℝ (fun (x : MinkowskiModel d) => gp.coefficient x k μ) z)
                                (Pi.single k 1) =
                              (fderiv ℝ (fun (x : MinkowskiModel d) => gm.coefficient x k μ) z)
                                (Pi.single k 1)) →
                      ((∀ (p q : Fin (d + 1)),
                          ContDiffOn ℝ 1
                            (fun (x : MinkowskiModel d) =>
                              glue k gm.coefficient gp.coefficient x p q)
                            U) ↔
                        ∀ z ∈ U,
                          z k = 0 → gp.secondFundamental k 1 z = gm.secondFundamental k 1 z) :=
  @ProjectAinos.SmoothGeometry.CoordinateMetric.contDiffOn_glue_iff_secondFundamental

example :
    ℝ → ℝ → MinkowskiModel 3 → Matrix (Fin 4) (Fin 4) ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.comovingDust

example :
    ContDiff ℝ ∞ toCartesian :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.contDiff_toCartesian

example :
    ∀ {τc κ : ℝ} (hτc : 0 < τc),
      κ ≠ 0 → (dustInterior hτc).metric.IsEinstein κ 0 (comovingDust κ τc) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.isEinstein_dustInterior

example :
    ∀ (M : ℝ) (x : MinkowskiModel 3),
      Tolman.lemaitreRadius (2 * M) (x 0) (x 1) = lemaitreRadius M x :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.tolman_lemaitreRadius

example :
    ∀ {M κ : ℝ} (hM : 0 < M), κ ≠ 0 → (lemaitre hM).metric.IsEinstein κ 0 0 :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.isEinstein_lemaitre

example :
    ℝ → ℝ → ℝ → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.boundaryRadius

example :
    ℝ → ℝ → ℝ → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.boundaryRate

example :
    ∀ {τc χb : ℝ}, 0 < τc → 0 < χb → ∀ {T : ℝ}, T < τc → 0 < boundaryRadius τc χb T :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.boundaryRadius_pos

example :
    ∀ {τc χb : ℝ},
      0 < τc → ∀ {T : ℝ}, T < τc → HasDerivAt (boundaryRadius τc χb) (boundaryRate τc χb T) T :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.hasDerivAt_boundaryRadius

example :
    ∀ {τc χb : ℝ}, 0 < τc → ContDiffOn ℝ ∞ (boundaryRadius τc χb) (Iio τc) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.contDiffOn_boundaryRadius

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {T : ℝ}, T < τc → √(2 * M / boundaryRadius τc χb T) = -boundaryRate τc χb T :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.sqrt_two_mul_div_boundaryRadius

example :
    ℝ → MinkowskiModel 3 → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.interiorTime

example :
    ℝ → ℝ → MinkowskiModel 3 → MinkowskiModel 3 :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.interiorMap

example :
    ℝ → ℝ → ℝ → MinkowskiModel 3 → MinkowskiModel 3 :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.exteriorMap

example :
    ∀ (τc : ℝ), Continuous (dustScale τc) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.continuous_dustScale

example :
    ∀ (τc χb : ℝ), Continuous (boundaryRadius τc χb) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.continuous_boundaryRadius

example :
    ∀ {O : Set (MinkowskiModel 3)},
      IsOpen O → ∀ {f : MinkowskiModel 3 → ℝ}, ContinuousOn f O → IsOpen (O ∩ f ⁻¹' Ioi 0) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.isOpen_pos

example :
    IsOpen {x : MinkowskiModel 3 | 0 < x 2 ∧ x 2 < π} :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.isOpen_angle

example :
    ∀ (τc : ℝ), IsOpen {x : MinkowskiModel 3 | x 0 < τc} :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.isOpen_lt_crunch

example :
    ∀ (τc : ℝ), ContinuousOn (interiorTime τc) {x : MinkowskiModel 3 | x 0 < τc} :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.continuousOn_interiorTime

example :
    {τc : ℝ} → 0 < τc → ℝ → Opens (MinkowskiModel 3) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.interiorDomain

example :
    ℝ → ℝ → Opens (MinkowskiModel 3) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.exteriorDomain

example :
    {τc : ℝ} → 0 < τc → ℝ → Opens (MinkowskiModel 3) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.collar

example :
    ∀ {τc χb : ℝ} (hτc : 0 < τc),
      0 < χb →
        ∀ {x : MinkowskiModel 3}, x 0 < τc → x 1 = 0 → 0 < x 2 → x 2 < π → x ∈ collar hτc χb :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.mem_collar_of_boundary

example :
    ℝ → MinkowskiModel 3 → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.timeRateT

example :
    ℝ → MinkowskiModel 3 → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.timeRateN

example :
    ℝ → MinkowskiModel 3 → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.hubble

example :
    ℝ → MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.interiorDeriv

example :
    ∀ (τc : ℝ) (x v : MinkowskiModel 3),
      (interiorDeriv τc x) v =
        ![timeRateT τc x * v 0 + timeRateN τc x * v 1,
          (-(x 1 * hubble τc x * timeRateT τc x) * v 0 +
              (1 - x 1 * hubble τc x * timeRateN τc x) * v 1) /
            dustScale τc (interiorTime τc x),
          v 2, v 3] :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.interiorDeriv_apply

example :
    ∀ {τc : ℝ} {x : MinkowskiModel 3},
      x 0 < τc →
        HasFDerivAt (interiorTime τc)
          (timeRateT τc x • (ContinuousLinearMap.proj 0 : MinkowskiModel 3 →L[ℝ] ℝ) +
            timeRateN τc x • (ContinuousLinearMap.proj 1 : MinkowskiModel 3 →L[ℝ] ℝ))
          x :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.hasFDerivAt_interiorTime

example :
    ∀ {τc χb : ℝ} (hτc : 0 < τc) {x : MinkowskiModel 3},
      x ∈ interiorDomain hτc χb → HasFDerivAt (interiorMap τc χb) (interiorDeriv τc x) x :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.hasFDerivAt_interiorMap

example :
    ℝ → ℝ → MinkowskiModel 3 → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.exteriorRadius

example :
    ℝ → ℝ → ℝ → MinkowskiModel 3 → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.exteriorScale

example :
    ℝ → ℝ → ℝ → MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.exteriorDeriv

example :
    ∀ (M τc χb : ℝ) (x v : MinkowskiModel 3),
      (exteriorDeriv M τc χb x) v =
        ![v 0,
          (1 + exteriorScale M τc χb x * boundaryRate τc χb (x 0)) * v 0 +
            exteriorScale M τc χb x * v 1,
          v 2, v 3] :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.exteriorDeriv_apply

example :
    ∀ {M τc χb : ℝ},
      0 < M → ∀ {x : MinkowskiModel 3}, x ∈ exteriorDomain τc χb → 0 < exteriorScale M τc χb x :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.exteriorScale_pos

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        ∀ {x : MinkowskiModel 3},
          x ∈ exteriorDomain τc χb →
            exteriorScale M τc χb x ^ 2 = exteriorRadius τc χb x / (2 * M) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.exteriorScale_sq

example :
    ∀ {τc χb : ℝ},
      0 < τc →
        ∀ {x : MinkowskiModel 3},
          x 0 < τc →
            HasFDerivAt (exteriorRadius τc χb)
              ((ContinuousLinearMap.proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) +
                boundaryRate τc χb (x 0) • (ContinuousLinearMap.proj 0 : MinkowskiModel 3 →L[ℝ] ℝ))
              x :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.hasFDerivAt_exteriorRadius

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          ∀ {x : MinkowskiModel 3},
            x ∈ exteriorDomain τc χb →
              HasFDerivAt (exteriorMap M τc χb) (exteriorDeriv M τc χb x) x :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.hasFDerivAt_exteriorMap

example :
    ∀ (τc : ℝ), ContDiffOn ℝ ∞ (interiorTime τc) {x : MinkowskiModel 3 | x 0 < τc} :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.contDiffOn_interiorTime

example :
    ∀ {τc : ℝ} (hτc : 0 < τc) (χb : ℝ),
      ContDiffOn ℝ ∞ (interiorMap τc χb) ↑(interiorDomain hτc χb) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.contDiffOn_interiorMap

example :
    ∀ {M τc : ℝ},
      0 < M → 0 < τc → ∀ (χb : ℝ), ContDiffOn ℝ ∞ (exteriorMap M τc χb) ↑(exteriorDomain τc χb) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.contDiffOn_exteriorMap

example :
    ∀ {τc : ℝ} (hτc : 0 < τc) (χb : ℝ),
      MapsTo (interiorMap τc χb) ↑(interiorDomain hτc χb) ↑(dustInterior hτc).domain :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.mapsTo_interiorMap

example :
    ∀ {M τc : ℝ} (hM : 0 < M) (χb : ℝ),
      MapsTo (exteriorMap M τc χb) ↑(exteriorDomain τc χb) ↑(lemaitre hM).domain :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.mapsTo_exteriorMap

example :
    ∀ {L : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3}, Function.Injective ⇑L → L.IsInvertible :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.isInvertible_of_injective

example :
    ∀ {τc χb : ℝ} (hτc : 0 < τc) {x : MinkowskiModel 3},
      x ∈ interiorDomain hτc χb → (interiorDeriv τc x).IsInvertible :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.isInvertible_interiorDeriv

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        ∀ {x : MinkowskiModel 3},
          x ∈ exteriorDomain τc χb → (exteriorDeriv M τc χb x).IsInvertible :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.isInvertible_exteriorDeriv

example :
    {τc : ℝ} →
      (hτc : 0 < τc) →
        (χb : ℝ) → CoordinateMetric LorentzConvention.timeNegative 3 (interiorDomain hτc χb) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.interiorMetric

example :
    {M τc : ℝ} →
      0 < M →
        0 < τc →
          (χb : ℝ) → CoordinateMetric LorentzConvention.timeNegative 3 (exteriorDomain τc χb) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.exteriorMetric

example :
    ℝ → ℝ → MinkowskiModel 3 → Matrix (Fin 4) (Fin 4) ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.interiorCoeff

example :
    ∀ {τc χb : ℝ} (hτc : 0 < τc) {x : MinkowskiModel 3},
      x ∈ interiorDomain hτc χb → (interiorMetric hτc χb).coefficient x = interiorCoeff τc χb x :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.coefficient_interiorMetric

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        ∀ {x : MinkowskiModel 3},
          x ∈ exteriorDomain τc χb →
            lemaitreRadius M (exteriorMap M τc χb x) = exteriorRadius τc χb x :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.lemaitreRadius_exteriorMap

example :
    ℝ → ℝ → ℝ → MinkowskiModel 3 → Matrix (Fin 4) (Fin 4) ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.exteriorCoeff

example :
    ∀ {M τc χb : ℝ} (hM : 0 < M) (hτc : 0 < τc) {x : MinkowskiModel 3},
      x ∈ exteriorDomain τc χb →
        (exteriorMetric hM hτc χb).coefficient x = exteriorCoeff M τc χb x :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.coefficient_exteriorMetric

example :
    ∀ {U : Opens (MinkowskiModel 3)} (g : CoordinateMetric LorentzConvention.timeNegative 3 U)
      {C : MinkowskiModel 3 → Matrix (Fin 4) (Fin 4) ℝ},
      (∀ x ∈ U, g.coefficient x = C x) →
        ∀ {z : MinkowskiModel 3},
          z ∈ U →
            ∀ {p q : Fin 4} {c : ℝ},
              HasDerivAt (fun (s : ℝ) => C (Function.update z 1 s) p q) c (z 1) →
                (fderiv ℝ (fun (y : MinkowskiModel 3) => g.coefficient y p q) z)
                    (Pi.single 1 1) =
                  c :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.fderiv_normal_eq

example :
    ℝ → ℝ → ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.normalDeriv

example :
    ∀ (c : ℝ), HasDerivAt (fun (s : ℝ) => s ^ 2 / c) 0 0 :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.hasDerivAt_sq_div

example :
    ∀ {τc χb : ℝ} (hτc : 0 < τc) {z : MinkowskiModel 3},
      z ∈ interiorDomain hτc χb →
        z 1 = 0 →
          ∀ (p q : Fin 4),
            (fderiv ℝ (fun (y : MinkowskiModel 3) => (interiorMetric hτc χb).coefficient y p q)
                  z)
                (Pi.single 1 1) =
              normalDeriv τc χb (z 0) (z 2) p q :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.fderiv_interiorMetric

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {T : ℝ},
                T < τc → (√(boundaryRadius τc χb T / (2 * M)))⁻¹ = -boundaryRate τc χb T :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.inv_exteriorScale_boundary

example :
    ∀ {M τc χb : ℝ} (hM : 0 < M) (hτc : 0 < τc),
      0 < χb →
        9 * M * τc ^ 2 = 2 * χb ^ 3 →
          ∀ {z : MinkowskiModel 3},
            z ∈ exteriorDomain τc χb →
              z 1 = 0 →
                ∀ (p q : Fin 4),
                  (fderiv ℝ
                        (fun (y : MinkowskiModel 3) =>
                          (exteriorMetric hM hτc χb).coefficient y p q)
                        z)
                      (Pi.single 1 1) =
                    normalDeriv τc χb (z 0) (z 2) p q :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.fderiv_exteriorMetric

example :
    ℝ → ℝ → ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.boundaryCoeff

example :
    ∀ {τc χb : ℝ} (hτc : 0 < τc) {z : MinkowskiModel 3},
      z ∈ interiorDomain hτc χb →
        z 1 = 0 → (interiorMetric hτc χb).coefficient z = boundaryCoeff τc χb (z 0) (z 2) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.coefficient_interiorMetric_boundary

example :
    ∀ {M τc χb : ℝ} (hM : 0 < M) (hτc : 0 < τc),
      0 < χb →
        9 * M * τc ^ 2 = 2 * χb ^ 3 →
          ∀ {z : MinkowskiModel 3},
            z ∈ exteriorDomain τc χb →
              z 1 = 0 →
                (exteriorMetric hM hτc χb).coefficient z = boundaryCoeff τc χb (z 0) (z 2) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.coefficient_exteriorMetric_boundary

example :
    ∀ {τc χb : ℝ} (hτc : 0 < τc), collar hτc χb ≤ interiorDomain hτc χb :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.collar_le_interior

example :
    ∀ {τc χb : ℝ} (hτc : 0 < τc), collar hτc χb ≤ exteriorDomain τc χb :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.collar_le_exterior

example :
    ∀ {M τc χb : ℝ} (hM : 0 < M) (hτc : 0 < τc),
      0 < χb →
        9 * M * τc ^ 2 = 2 * χb ^ 3 →
          ∀ {y : MinkowskiModel 3},
            y ∈ collar hτc χb →
              y 1 = 0 →
                (interiorMetric hτc χb).coefficient y = (exteriorMetric hM hτc χb).coefficient y :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.coefficient_eq_on_boundary

example :
    ∀ {M τc χb : ℝ} (hM : 0 < M) (hτc : 0 < τc),
      0 < χb →
        9 * M * τc ^ 2 = 2 * χb ^ 3 →
          ∀ {y : MinkowskiModel 3},
            y ∈ collar hτc χb →
              y 1 = 0 →
                ∀ (μ : Fin 4),
                  (exteriorMetric hM hτc χb).coefficient y 1 μ = if μ = 1 then 1 else 0 :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.coefficient_normal_on_boundary

example :
    ∀ {M τc χb : ℝ} (hM : 0 < M) (hτc : 0 < τc),
      0 < χb →
        9 * M * τc ^ 2 = 2 * χb ^ 3 →
          ∀ {z : MinkowskiModel 3},
            z ∈ collar hτc χb →
              z 1 = 0 →
                ∀ (p q : Fin 4),
                  (fderiv ℝ
                        (fun (x : MinkowskiModel 3) =>
                          (exteriorMetric hM hτc χb).coefficient x p q)
                        z)
                      (Pi.single 1 1) =
                    (fderiv ℝ
                        (fun (x : MinkowskiModel 3) =>
                          (interiorMetric hτc χb).coefficient x p q)
                        z)
                      (Pi.single 1 1) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.fderiv_eq_on_boundary

example :
    ∀ {τc χb : ℝ} {z : MinkowskiModel 3}, z 1 = 0 → interiorMap τc χb z = ![z 0, χb, z 2, z 3] :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.interiorMap_boundary

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {z : MinkowskiModel 3},
                z ∈ exteriorDomain τc χb →
                  z 1 = 0 → exteriorMap M τc χb z = ![z 0, τc, z 2, z 3] :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.exteriorMap_boundary

example :
    ∀ {M τc χb : ℝ} (hM : 0 < M) (hτc : 0 < τc),
      0 < χb →
        9 * M * τc ^ 2 = 2 * χb ^ 3 →
          ∀ {z : MinkowskiModel 3},
            z ∈ collar hτc χb →
              z 1 = 0 →
                (exteriorMetric hM hτc χb).secondFundamental 1 1 z =
                    (lemaitre hM).metric.secondFundamental 1 1 ![z 0, τc, z 2, z 3] ∧
                  (interiorMetric hτc χb).secondFundamental 1 1 z =
                      (dustInterior hτc).metric.secondFundamental 1 1 ![z 0, χb, z 2, z 3] ∧
                    (exteriorMetric hM hτc χb).secondFundamental 1 1 z =
                        (interiorMetric hτc χb).secondFundamental 1 1 z ∧
                      (exteriorMetric hM hτc χb).inducedMetric 1 z =
                          (lemaitre hM).metric.inducedMetric 1 ![z 0, τc, z 2, z 3] ∧
                        (interiorMetric hτc χb).inducedMetric 1 z =
                          (dustInterior hτc).metric.inducedMetric 1 ![z 0, χb, z 2, z 3] :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.junction_adapted

example :
    ℝ → ℝ → MinkowskiModel 3 → Matrix (Fin 4) (Fin 4) ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.chartDust

example :
    ∀ {τc χb κ : ℝ} (hτc : 0 < τc) {x : MinkowskiModel 3},
      x ∈ interiorDomain hτc χb →
        pullbackTensor (interiorMap τc χb) (comovingDust κ τc) x = chartDust κ τc x :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.pullbackTensor_comovingDust

example :
    ∀ {τc χb κ : ℝ} (hτc : 0 < τc),
      κ ≠ 0 → (interiorMetric hτc χb).IsEinstein κ 0 (chartDust κ τc) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.isEinstein_interiorMetric

example :
    ∀ {M τc χb κ : ℝ} (hM : 0 < M) (hτc : 0 < τc),
      κ ≠ 0 → (exteriorMetric hM hτc χb).IsEinstein κ 0 0 :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.isEinstein_exteriorMetric

example :
    ∀ {τc χb : ℝ} (hτc : 0 < τc) (κ : ℝ) (i k : Fin 4),
      ContinuousOn (fun (x : MinkowskiModel 3) => chartDust κ τc x i k) ↑(interiorDomain hτc χb) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.continuousOn_chartDust

example :
    ∀ {M τc χb : ℝ} (hM : 0 < M) (hτc : 0 < τc),
      0 < χb →
        9 * M * τc ^ 2 = 2 * χb ^ 3 →
          ∀ (p q : Fin 4),
            ContDiffOn ℝ 1
              (fun (x : MinkowskiModel 3) =>
                glue 1 (interiorMetric hτc χb).coefficient
                  (exteriorMetric hM hτc χb).coefficient x p q)
              ↑(collar hτc χb) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.contDiffOn_glue

example :
    ∀ {M τc χb : ℝ} (hM : 0 < M) (hτc : 0 < τc),
      0 < χb →
        9 * M * τc ^ 2 = 2 * χb ^ 3 →
          ((∀ (p q : Fin (3 + 1)),
              ContDiffOn ℝ 1
                (fun (x : MinkowskiModel 3) =>
                  glue 1 (interiorMetric hτc χb).coefficient
                    (exteriorMetric hM hτc χb).coefficient x p q)
                ↑(collar hτc χb)) ↔
            ∀ z ∈ collar hτc χb,
              z 1 = 0 →
                (exteriorMetric hM hτc χb).secondFundamental 1 1 z =
                  (interiorMetric hτc χb).secondFundamental 1 1 z) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.contDiffOn_glue_iff_junction

example :
    ∀ {M τc χb κ : ℝ} (hM : 0 < M) (hτc : 0 < τc),
      0 < χb →
        9 * M * τc ^ 2 = 2 * χb ^ 3 →
          κ ≠ 0 →
            IsWeakEinstein (↑(collar hτc χb))
              (glue 1 (interiorMetric hτc χb).coefficient
                (exteriorMetric hM hτc χb).coefficient)
              κ (glue 1 (chartDust κ τc) 0) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.isWeakEinstein_oppenheimerSnyder

example :
    ℝ → ℝ → Opens (MinkowskiModel 3) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.shellDomain

example :
    ℝ → ℝ → MinkowskiModel 3 → Fin 4 → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.shellCoeffs

example :
    (R₀ s : ℝ) → CoordinateMetric LorentzConvention.timeNegative 3 (shellDomain R₀ s) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.shellMetric

example :
    ℝ → ℝ → Opens (MinkowskiModel 3) :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.shellCollar

example :
    ∀ {R₀ t : ℝ} {y : MinkowskiModel 3},
      y 1 = 0 →
        (shellMetric R₀ t).secondFundamental 1 1 y =
          Matrix.diagonal ![0, t * R₀, t * R₀ * Real.sin (y 2) ^ 2] :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.secondFundamental_shellMetric

example :
    ∀ {R₀ t : ℝ} {y : MinkowskiModel 3},
      y 1 = 0 →
        (shellMetric R₀ t).inducedMetric 1 y =
          Matrix.diagonal ![-1, R₀ ^ 2, R₀ ^ 2 * Real.sin (y 2) ^ 2] :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.inducedMetric_shellMetric

example :
    ∀ {R₀ s : ℝ},
      0 < R₀ →
        ∀ {y : MinkowskiModel 3},
          y ∈ shellCollar R₀ s →
            y 1 = 0 →
              (shellMetric R₀ s).secondFundamental 1 1 y 0 0 -
                    (shellMetric R₀ 1).secondFundamental 1 1 y 0 0 -
                  (shellMetric R₀ s).inducedMetric 1 y 0 0 *
                    ∑ c : Fin 3,
                      ∑ e : Fin 3,
                        ((shellMetric R₀ s).inducedMetric 1 y)⁻¹ c e *
                          ((shellMetric R₀ s).secondFundamental 1 1 y c e -
                            (shellMetric R₀ 1).secondFundamental 1 1 y c e) =
                2 * (s - 1) / R₀ :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.shell_surface_density

example :
    ∀ {R₀ s : ℝ},
      0 < R₀ →
        s ≠ 1 →
          ∃ (φ : MinkowskiModel 3 → Matrix (Fin 4) (Fin 4) ℝ),
            IsTestDensity (↑(shellCollar R₀ s)) φ ∧
              weakEinstein
                  (glue 1 (shellMetric R₀ 1).coefficient (shellMetric R₀ s).coefficient) φ ≠
                (∫ (x : MinkowskiModel 3) in {x : MinkowskiModel 3 | x 1 < 0},
                    ∑ j : Fin (3 + 1),
                      ∑ l : Fin (3 + 1),
                        einsteinOf (shellMetric R₀ 1).coefficient x j l * φ x j l) +
                  ∫ (x : MinkowskiModel 3) in {x : MinkowskiModel 3 | 0 < x 1},
                    ∑ j : Fin (3 + 1),
                      ∑ l : Fin (3 + 1),
                        einsteinOf (shellMetric R₀ s).coefficient x j l * φ x j l :=
  @ProjectAinos.GeneralRelativity.CollapseJunction.exists_surface_layer

example :
    ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.infallSpeed

example :
    ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.infallRate

example :
    ℝ → ℝ → ℝ → ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.shift

example :
    ℝ →
      ℝ →
        ℝ →
          ℝ × EuclideanSpace ℝ (Fin 3) →
            ℝ × EuclideanSpace ℝ (Fin 3) → ℝ × EuclideanSpace ℝ (Fin 3) → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.osForm

example :
    ℝ → Set (ℝ × EuclideanSpace ℝ (Fin 3)) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.spacetime

example :
    ℝ → ℝ → ℝ → ℝ × EuclideanSpace ℝ (Fin 3) → ℝ × EuclideanSpace ℝ (Fin 3) → Prop :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.IsFutureCausal

example :
    ℝ → ℝ → ℝ → ℝ → (ℝ → EuclideanSpace ℝ (Fin 3)) → Prop :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.IsFutureCausalCurve

example :
    ℝ → ℝ → ℝ → Set (ℝ × EuclideanSpace ℝ (Fin 3)) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.causalPastScri

example :
    ℝ → ℝ → ℝ → Set (ℝ × EuclideanSpace ℝ (Fin 3)) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.eventHorizon

example :
    ℝ → ℝ → ℝ → ℝ → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.horizonRadius

example :
    ∀ {M τc χb : ℝ} (p : ℝ × EuclideanSpace ℝ (Fin 3)) (v : EuclideanSpace ℝ (Fin 3)),
      osForm M τc χb p (1, v) (1, v) = -1 + ‖v + shift M τc χb p.1 p.2‖ ^ 2 :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.osForm_self

example :
    ∀ {M τc χb : ℝ} (p : ℝ × EuclideanSpace ℝ (Fin 3)) (v : EuclideanSpace ℝ (Fin 3)),
      IsFutureCausal M τc χb p (1, v) ↔ ‖v + shift M τc χb p.1 p.2‖ ≤ 1 :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.isFutureCausal_iff

example :
    ∀ {M τc χb : ℝ},
      0 < τc →
        9 * M * τc ^ 2 = 2 * χb ^ 3 →
          ∀ {τ : ℝ}, τ < τc → boundaryRadius τc χb τ ^ 3 = 9 / 2 * M * (τc - τ) ^ 2 :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.boundaryRadius_cube

example :
    ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → (a ≤ b ↔ a ^ 3 ≤ b ^ 3) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.le_iff_cube_le

example :
    ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → (a < b ↔ a ^ 3 < b ^ 3) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.lt_iff_cube_lt

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {τ : ℝ},
                τ < τc →
                  2 / 3 * boundaryRadius τc χb τ / (τc - τ) = √(2 * M / boundaryRadius τc χb τ) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.dust_speed_boundary

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {τ : ℝ}, τ < τc → (boundaryRadius τc χb τ ≤ 2 * M ↔ τc - 4 * M / 3 ≤ τ) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.boundaryRadius_le_iff

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {τ : ℝ}, τ < τc - 4 * M / 3 → 2 * M < boundaryRadius τc χb τ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.two_mul_lt_boundaryRadius

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb → 9 * M * τc ^ 2 = 2 * χb ^ 3 → boundaryRadius τc χb (τc - 4 * M / 3) = 2 * M :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.boundaryRadius_horizonTime

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {τ : ℝ},
                τ ≤ τc - 4 * M / 3 →
                  3 * (boundaryRadius τc χb τ - (τc - τ)) ≤ boundaryRadius τc χb τ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.horizonRadius_le_boundaryRadius

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb → 9 * M * τc ^ 2 = 2 * χb ^ 3 → ∀ (τ : ℝ), horizonRadius M τc χb τ ≤ 2 * M :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.horizonRadius_le

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {τ : ℝ}, τc - 4 * M / 3 ≤ τ → horizonRadius M τc χb τ = 2 * M :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.horizonRadius_of_le

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {τ : ℝ}, τc - 4 * M / 3 ≤ τ → infallSpeed M τc χb τ (2 * M) = 1 :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.infallSpeed_two_mul

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ (τ : ℝ),
                HasDerivWithinAt (horizonRadius M τc χb)
                  (1 - infallSpeed M τc χb τ (horizonRadius M τc χb τ)) (Ici τ) τ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.hasDerivWithinAt_horizonRadius

example :
    ∀ {M τc χb : ℝ} (τ r : ℝ), infallRate M τc χb τ r * r = infallSpeed M τc χb τ r :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.infallRate_mul

example :
    ∀ {M τc χb : ℝ} (τ : ℝ) (x : EuclideanSpace ℝ (Fin 3)),
      ⟪x, shift M τc χb τ x⟫_ℝ = infallSpeed M τc χb τ ‖x‖ * ‖x‖ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.inner_shift

example :
    ∀ {M τc χb : ℝ} (τ : ℝ), infallSpeed M τc χb τ 0 = 0 :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.infallSpeed_zero

example :
    ∀ {M τc χb : ℝ} {x : ℝ → EuclideanSpace ℝ (Fin 3)} {τ : ℝ} {v : EuclideanSpace ℝ (Fin 3)},
      HasDerivWithinAt x v (Ici τ) τ →
        ‖v + shift M τc χb τ (x τ)‖ ≤ 1 →
          ∀ {r₁ : ℝ},
            1 - infallSpeed M τc χb τ ‖x τ‖ < r₁ →
              ∀ᶠ (z : ℝ) in 𝓝[>] τ, (z - τ)⁻¹ * (‖x z‖ - ‖x τ‖) < r₁ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.eventually_slope_norm_lt

example :
    ∀ {M : ℝ},
      0 < M → ∀ {a r : ℝ}, 2 * M ≤ a → a ≤ r → √(2 * M / a) - √(2 * M / r) ≤ (r - a) / (4 * M) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.sqrt_sub_sqrt_le

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {τ r : ℝ},
                horizonRadius M τc χb τ ≤ r →
                  infallSpeed M τc χb τ (horizonRadius M τc χb τ) - infallSpeed M τc χb τ r ≤
                    (r - horizonRadius M τc χb τ) / (4 * M) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.infallSpeed_sub_le

example :
    ∀ {M τc χb : ℝ},
      0 < M → 0 < τc → 0 < χb → 9 * M * τc ^ 2 = 2 * χb ^ 3 → Continuous (horizonRadius M τc χb) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.continuous_horizonRadius

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {x : ℝ → EuclideanSpace ℝ (Fin 3)} {τ₀ τ : ℝ},
                τ₀ ≤ τ →
                  ContinuousOn x (Icc τ₀ τ) →
                    (∀ t ∈ Ico τ₀ τ,
                        ∃ (v : EuclideanSpace ℝ (Fin 3)),
                          HasDerivWithinAt x v (Ici t) t ∧
                            IsFutureCausal M τc χb (t, x t) (1, v)) →
                      ‖x τ₀‖ ≤ horizonRadius M τc χb τ₀ → ‖x τ‖ ≤ horizonRadius M τc χb τ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.norm_le_horizonRadius_of_arc

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {x : ℝ → EuclideanSpace ℝ (Fin 3)} {τ₀ : ℝ},
                IsFutureCausalCurve M τc χb τ₀ x →
                  ‖x τ₀‖ ≤ horizonRadius M τc χb τ₀ →
                    ∀ {τ : ℝ}, τ₀ ≤ τ → ‖x τ‖ ≤ horizonRadius M τc χb τ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.norm_le_horizonRadius

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {p : ℝ × EuclideanSpace ℝ (Fin 3)},
                ‖p.2‖ ≤ horizonRadius M τc χb p.1 → p ∉ causalPastScri M τc χb :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.notMem_causalPastScri

example :
    ∀ {M τc χb τ ρ : ℝ},
      0 ≤ ρ →
        ∀ {u : EuclideanSpace ℝ (Fin 3)},
          ‖u‖ = 1 → shift M τc χb τ (ρ • u) = infallSpeed M τc χb τ ρ • u :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.shift_smul

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {τ τ' : ℝ}, τ ≤ τ' → τ' < τc → boundaryRadius τc χb τ' ≤ boundaryRadius τc χb τ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.boundaryRadius_anti

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {τ r : ℝ},
                τc ≤ τ ∨ boundaryRadius τc χb τ ≤ r → infallSpeed M τc χb τ r = √(2 * M / r) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.infallSpeed_eq_sqrt

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {τ₁ R₁ : ℝ} {u : EuclideanSpace ℝ (Fin 3)},
                ‖u‖ = 1 →
                  2 * M < R₁ →
                    (τ₁ < τc → boundaryRadius τc χb τ₁ ≤ R₁) →
                      ∀ {τ : ℝ},
                        τ₁ ≤ τ →
                          have δ := (1 - √(2 * M / R₁)) / 2;
                          (τ, (R₁ + δ * (τ - τ₁)) • u) ∈ spacetime τc ∧
                            HasDerivAt (fun (t : ℝ) => (R₁ + δ * (t - τ₁)) • u) (δ • u) τ ∧
                              ‖δ • u + shift M τc χb τ ((R₁ + δ * (τ - τ₁)) • u)‖ ≤ 1 ∧
                                ‖(R₁ + δ * (τ - τ₁)) • u‖ = R₁ + δ * (τ - τ₁) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.exterior_escape

example :
    ∀ {M τc χb : ℝ},
      0 < τc →
        0 < χb →
          9 * M * τc ^ 2 = 2 * χb ^ 3 →
            ∀ {c τ : ℝ},
              0 ≤ c →
                τ < τc → (c * boundaryRadius τc χb τ ≤ 3 * (τc - τ) ↔ c ^ 3 * M / 6 ≤ τc - τ) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.mul_boundaryRadius_le_iff

example :
    ∀ {M τc χb : ℝ},
      0 < τc →
        0 < χb →
          9 * M * τc ^ 2 = 2 * χb ^ 3 →
            ∀ {c τ : ℝ},
              0 ≤ c →
                τ < τc → (3 * (τc - τ) ≤ c * boundaryRadius τc χb τ ↔ τc - τ ≤ c ^ 3 * M / 6) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.le_mul_boundaryRadius_iff

example :
    ℝ → ℝ → ℝ → ℝ → ℝ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.dustRay

example :
    ∀ {τc χb : ℝ},
      0 < τc →
        ∀ (lam : ℝ) {τ : ℝ},
          τ < τc → HasDerivAt (dustRay τc χb lam) (lam * boundaryRate τc χb τ + 3) τ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.hasDerivAt_dustRay

example :
    ∀ {τc χb : ℝ} (lam : ℝ) {τ : ℝ},
      τ < τc → lam * boundaryRate τc χb τ + 3 + 2 / 3 * dustRay τc χb lam τ / (τc - τ) = 1 :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.dustRay_null

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {τp ρp : ℝ},
                τp < τc - 4 * M / 3 →
                  0 ≤ ρp →
                    ρp ≤ boundaryRadius τc χb τp →
                      3 * (boundaryRadius τc χb τp - (τc - τp)) < ρp →
                        have lam := (ρp + 3 * (τc - τp)) / boundaryRadius τc χb τp;
                        have τe := τc - (lam - 1) ^ 3 * M / 6;
                        dustRay τc χb lam τp = ρp ∧
                          3 < lam ∧
                            τp ≤ τe ∧
                              τe < τc - 4 * M / 3 ∧
                                dustRay τc χb lam τe = boundaryRadius τc χb τe ∧
                                  2 * M < boundaryRadius τc χb τe ∧
                                    ∀ (τ : ℝ),
                                      τp ≤ τ →
                                        τ ≤ τe →
                                          0 ≤ dustRay τc χb lam τ ∧
                                            dustRay τc χb lam τ ≤ boundaryRadius τc χb τ :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.dustRay_exit

example :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.direction

example :
    ∀ (x : EuclideanSpace ℝ (Fin 3)), ‖direction x‖ = 1 :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.norm_direction

example :
    ∀ (x : EuclideanSpace ℝ (Fin 3)), ‖x‖ • direction x = x :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.norm_smul_direction

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {p : ℝ × EuclideanSpace ℝ (Fin 3)},
                p ∈ spacetime τc →
                  horizonRadius M τc χb p.1 < ‖p.2‖ → p ∈ causalPastScri M τc χb :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.mem_causalPastScri

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              causalPastScri M τc χb =
                {p : ℝ × EuclideanSpace ℝ (Fin 3) | horizonRadius M τc χb p.1 < ‖p.2‖} :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.causalPastScri_eq

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              eventHorizon M τc χb =
                {p : ℝ × EuclideanSpace ℝ (Fin 3) | ‖p.2‖ = horizonRadius M τc χb p.1} :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.eventHorizon_eq

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {u : EuclideanSpace ℝ (Fin 3)},
                ‖u‖ = 1 →
                  (∀ (τ : ℝ),
                      0 ≤ horizonRadius M τc χb τ →
                        osForm M τc χb (τ, horizonRadius M τc χb τ • u)
                            (1, (1 - infallSpeed M τc χb τ (horizonRadius M τc χb τ)) • u)
                            (1, (1 - infallSpeed M τc χb τ (horizonRadius M τc χb τ)) • u) =
                          0) ∧
                    horizonRadius M τc χb (τc - 4 * M / 3) = 2 * M ∧
                      boundaryRadius τc χb (τc - 4 * M / 3) = 2 * M ∧
                        horizonRadius M τc χb (τc - 9 * M / 2) = 0 :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.horizon_generator

example :
    ∀ {M τc χb : ℝ},
      0 < M →
        0 < τc →
          0 < χb →
            9 * M * τc ^ 2 = 2 * χb ^ 3 →
              ∀ {u : EuclideanSpace ℝ (Fin 3)},
                ‖u‖ = 1 →
                  IsFutureCausalCurve M τc χb (τc - 4 * M / 3) fun (_ : ℝ) => (2 * M) • u :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.isFutureCausalCurve_horizon

example :
    ℝ → ℝ → EuclideanSpace ℝ (Fin 3) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.sphDir

example :
    ℝ → ℝ → EuclideanSpace ℝ (Fin 3) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.sphDirθ

example :
    ℝ → ℝ → EuclideanSpace ℝ (Fin 3) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.sphDirφ

example :
    ∀ (θ φ : ℝ),
      ⟪sphDir θ φ, sphDir θ φ⟫_ℝ = 1 ∧
        ⟪sphDir θ φ, sphDirθ θ φ⟫_ℝ = 0 ∧
          ⟪sphDir θ φ, sphDirφ θ φ⟫_ℝ = 0 ∧
            ⟪sphDirθ θ φ, sphDirθ θ φ⟫_ℝ = 1 ∧
              ⟪sphDirθ θ φ, sphDirφ θ φ⟫_ℝ = 0 ∧ ⟪sphDirφ θ φ, sphDirφ θ φ⟫_ℝ = Real.sin θ ^ 2 :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.inner_sphDir

example :
    ∀ (θ φ : ℝ), ‖sphDir θ φ‖ = 1 :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.norm_sphDir

example :
    ∀ (x : MinkowskiModel 3),
      HasFDerivAt (fun (y : MinkowskiModel 3) => sphDir (y 2) (y 3))
        (((ContinuousLinearMap.proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)).smulRight (sphDirθ (x 2) (x 3)) +
          ((ContinuousLinearMap.proj 3 : MinkowskiModel 3 →L[ℝ] ℝ)).smulRight (sphDirφ (x 2) (x 3)))
        x :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.hasFDerivAt_sphDir

example :
    (MinkowskiModel 3 → ℝ) → MinkowskiModel 3 → ℝ × EuclideanSpace ℝ (Fin 3) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.sphChart

example :
    ∀ {ρ : MinkowskiModel 3 → ℝ} {ρ' : MinkowskiModel 3 →L[ℝ] ℝ} {x : MinkowskiModel 3},
      HasFDerivAt ρ ρ' x →
        HasFDerivAt (sphChart ρ)
          (((ContinuousLinearMap.proj 0 : MinkowskiModel 3 →L[ℝ] ℝ)).prod
            (ρ x •
                (((ContinuousLinearMap.proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)).smulRight
                    (sphDirθ (x 2) (x 3)) +
                  ((ContinuousLinearMap.proj 3 : MinkowskiModel 3 →L[ℝ] ℝ)).smulRight
                    (sphDirφ (x 2) (x 3))) +
              ρ'.smulRight (sphDir (x 2) (x 3))))
          x :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.hasFDerivAt_sphChart

example :
    ∀ {M τc χb : ℝ} {ρ : MinkowskiModel 3 → ℝ} {ρ' : MinkowskiModel 3 →L[ℝ] ℝ}
      {x : MinkowskiModel 3},
      HasFDerivAt ρ ρ' x →
        0 ≤ ρ x →
          ∀ (v w : MinkowskiModel 3),
            osForm M τc χb (sphChart ρ x) ((fderiv ℝ (sphChart ρ) x) v)
                ((fderiv ℝ (sphChart ρ) x) w) =
              -(v 0 * w 0) +
                  (ρ' v + infallSpeed M τc χb (x 0) (ρ x) * v 0) *
                    (ρ' w + infallSpeed M τc χb (x 0) (ρ x) * w 0) +
                ρ x ^ 2 * (v 2 * w 2 + Real.sin (x 2) ^ 2 * (v 3 * w 3)) :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.osForm_sphChart

example :
    ∀ {M τc χb : ℝ} (hτc : 0 < τc) {x : MinkowskiModel 3},
      x ∈ dustDomain τc →
        x 1 ≤ χb →
          ∀ (v w : MinkowskiModel 3),
            osForm M τc χb (sphChart (fun (y : MinkowskiModel 3) => dustScale τc (y 0) * y 1) x)
                ((fderiv ℝ (sphChart fun (y : MinkowskiModel 3) => dustScale τc (y 0) * y 1) x)
                  v)
                ((fderiv ℝ (sphChart fun (y : MinkowskiModel 3) => dustScale τc (y 0) * y 1) x)
                  w) =
              (((dustInterior hτc).metric.form x) v) w :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.form_dust

example :
    ∀ {M τc χb : ℝ} (hM : 0 < M),
      0 < τc →
        0 < χb →
          9 * M * τc ^ 2 = 2 * χb ^ 3 →
            ∀ {x : MinkowskiModel 3},
              x ∈ lemaitreDomain →
                τc ≤ x 1 →
                  ∀ (v w : MinkowskiModel 3),
                    osForm M τc χb (sphChart (lemaitreRadius M) x)
                        ((fderiv ℝ (sphChart (lemaitreRadius M)) x) v)
                        ((fderiv ℝ (sphChart (lemaitreRadius M)) x) w) =
                      (((lemaitre hM).metric.form x) v) w :=
  @ProjectAinos.GeneralRelativity.CollapseHorizon.form_lemaitre
