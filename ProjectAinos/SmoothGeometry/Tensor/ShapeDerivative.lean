/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Tensor.Regularity
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-! # Covariant differentiation of every tensor shape

A connection on a smooth bundle is a covariant derivative of mathlib on its actual fibres
(`SmoothBundle.Connection`). Connections on two bundles `A` and `B` induce one on the hom bundle
`Hom(A, B)` of mathlib (`SmoothBundle.homConnection`):

`(∇_u L)(w x) = ∇_u (L w) − L (∇_u w)`.

The right side is tensorial in the section `w` when `L` is differentiable at `x`, so it descends
by `TensorialAt.mkHom₂` to a continuous bilinear map of the direction and the fibre vector. On
sections not differentiable at `x` the value is `0`; a covariant derivative of mathlib is
constrained only on differentiable sections. The additivity and the Leibniz rule
`∇(f L) = f ∇L + df ⊗ L` are proved, so the result is a covariant derivative of mathlib.

* `Shape.connection cov s`: by recursion on the shape, the directional derivative on scalars,
  the tangent connection `cov` on vectors and the induced connection on hom shapes. This covers
  covectors (`Shape.cotangent`), the covariant, contravariant and mixed tensors of
  `Shape.covariant` and `Shape.mixed`, and every other shape.
* `Shape.connection_hom_apply`, `Shape.connection_apply_section`: the Leibniz correction on any
  local differentiable extension, and its independence of the extension
  (`Shape.connection_hom_correction_eq`); `Shape.connection_add`, `Shape.connection_smul`,
  `Shape.connection_const_smul`, `Shape.connection_congr`.
* `SmoothBundle.Connection.IsLocallyRegular`: a connection takes sections `C^(n+1)` at a point
  to sections `C^n` there. It holds on scalars and passes to hom bundles, so a locally regular
  tangent connection gives a locally regular connection on every shape
  (`Shape.connection_isLocallyRegular`), and the derivative of a smooth tensor is a smooth tensor
  of shape `hom tangent s` (`Shape.covariantDerivative`), with smooth coefficients in every
  bundle chart (`Shape.coefficients_covariantDerivative_contMDiffOn`).
-/

@[expose] public section
noncomputable section
open Bundle FiberBundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.Tensor

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "TM" => TangentSpace I (M := M)

namespace SmoothBundle

/-- A connection on a smooth bundle: a covariant derivative of mathlib on its actual fibres. -/
abbrev Connection (A : SmoothBundle I (M := M)) : Type :=
  CovariantDerivative I A.Model A.Fiber

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- A section of the scalar bundle is differentiable precisely when it is as a function. -/
theorem mdifferentiableAt_scalar_iff {f : ∀ x, (scalar I (M := M)).Fiber x} {x : M} :
    MDifferentiableAt I (I.prod 𝓘(ℝ)) (fun y => TotalSpace.mk' ℝ y (f y)) x ↔
      MDifferentiableAt I 𝓘(ℝ) (fun y => (f y : ℝ)) x := by
  rw [mdifferentiableAt_section]
  rfl

/-- The directional derivative is the connection on scalars. -/
def scalarConnection : Connection (scalar I (M := M)) where
  toFun f x := mvfderiv I (fun y => (f y : ℝ)) x
  isCovariantDerivativeOnUniv := {
    add := fun hf hg _ => by
      exact mvfderiv_add (mdifferentiableAt_scalar_iff.mp hf)
        (mdifferentiableAt_scalar_iff.mp hg)
    leibniz := fun hf hg _ => by
      exact mvfderiv_smul hg (mdifferentiableAt_scalar_iff.mp hf) }

variable {A B : SmoothBundle I (M := M)}

/-- The Leibniz correction `∇_U (L w) − L (∇_U w)` of a hom section `L`, on a direction field
`U` and a section `w` of its domain. -/
def homDerivativeAux (cA : Connection A) (cB : Connection B)
    (L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x) (x : M) (U : ∀ x, TM x) (w : ∀ x, A.Fiber x) :
    B.Fiber x :=
  cB (fun y => L y (w y)) x (U x) - L x (cA w x (U x))

omit [FiniteDimensional ℝ E] in
/-- The Leibniz correction is tensorial in the direction field. -/
theorem homDerivativeAux_tensorial_direction (cA : Connection A) (cB : Connection B)
    (L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x) (x : M) (w : ∀ x, A.Fiber x) :
    TensorialAt I E (fun U => homDerivativeAux cA cB L x U w) x where
  smul {f U} _ _ := by
    simp [homDerivativeAux, smul_sub]
  add {U U'} _ _ := by
    simp only [homDerivativeAux, Pi.add_apply, map_add]
    abel

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The Leibniz correction of a hom section differentiable at `x` is tensorial in the section
of its domain. -/
theorem homDerivativeAux_tensorial_section (cA : Connection A) (cB : Connection B)
    {L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x} {x : M}
    (hL : MDifferentiableAt I (I.prod 𝓘(ℝ, A.Model →L[ℝ] B.Model))
      (fun y => TotalSpace.mk' (A.Model →L[ℝ] B.Model) y (L y)) x) (U : ∀ x, TM x) :
    TensorialAt I A.Model (fun w => homDerivativeAux cA cB L x U w) x where
  smul {f w} hf hw := by
    have hfun : (fun y => L y ((f • w) y)) = f • fun y => L y (w y) := by
      funext y
      simp
    simp only [homDerivativeAux, hfun]
    rw [cB.isCovariantDerivativeOnUniv.leibniz (hL.clm_bundle_apply hw) hf,
      cA.isCovariantDerivativeOnUniv.leibniz hw hf]
    simp only [add_apply, smul_apply, smulRight_apply, map_add, map_smul]
    module
  add {w w'} hw hw' := by
    have hfun : (fun y => L y ((w + w') y)) =
        (fun y => L y (w y)) + fun y => L y (w' y) := by
      funext y
      simp
    simp only [homDerivativeAux, hfun]
    rw [cB.isCovariantDerivativeOnUniv.add (hL.clm_bundle_apply hw) (hL.clm_bundle_apply hw'),
      cA.isCovariantDerivativeOnUniv.add hw hw']
    simp only [add_apply, map_add]
    abel

open Classical in
/-- The induced derivative of a hom section, `(∇_u L) w = ∇_u (L w) − L (∇_u w)`, on
sections differentiable at the point, and zero elsewhere. -/
def homConnectionFun (cA : Connection A) (cB : Connection B)
    (L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x) (x : M) :
    TM x →L[ℝ] A.Fiber x →L[ℝ] B.Fiber x :=
  if hL : MDifferentiableAt I (I.prod 𝓘(ℝ, A.Model →L[ℝ] B.Model))
      (fun y => TotalSpace.mk' (A.Model →L[ℝ] B.Model) y (L y)) x then
    TensorialAt.mkHom₂ (fun U w => homDerivativeAux cA cB L x U w) x
      (fun w _ => homDerivativeAux_tensorial_direction cA cB L x w)
      (fun U _ => homDerivativeAux_tensorial_section cA cB hL U)
  else 0

/-- On a hom section differentiable at `x`, the induced derivative is the Leibniz correction on
every section of the domain differentiable at `x`. -/
theorem homConnectionFun_apply (cA : Connection A) (cB : Connection B)
    {L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x} {x : M}
    (hL : MDifferentiableAt I (I.prod 𝓘(ℝ, A.Model →L[ℝ] B.Model))
      (fun y => TotalSpace.mk' (A.Model →L[ℝ] B.Model) y (L y)) x)
    {w : ∀ x, A.Fiber x}
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, A.Model))
      (fun y => TotalSpace.mk' A.Model y (w y)) x) (u : TM x) :
    homConnectionFun cA cB L x u (w x) = cB (fun y => L y (w y)) x u - L x (cA w x u) := by
  simp only [homConnectionFun, hL, ↓reduceDIte]
  have h := TensorialAt.mkHom₂_apply (fun w _ => homDerivativeAux_tensorial_direction cA cB L x w)
    (fun U _ => homDerivativeAux_tensorial_section cA cB hL U)
    (mdifferentiableAt_extend I E u) hw
  rw [extend_apply_self] at h
  rw [h, homDerivativeAux, extend_apply_self]

/-- The connection induced on a hom bundle: `(∇_u L) w = ∇_u (L w) − L (∇_u w)`. -/
def homConnection (cA : Connection A) (cB : Connection B) : Connection (hom I A B) where
  toFun := homConnectionFun cA cB
  isCovariantDerivativeOnUniv := {
    add := fun {L L'} {x} hL hL' _ => by
      have hLL' := mdifferentiableAt_add_section hL hL'
      ext u w
      simp only [homConnectionFun, hL, hL', hLL', ↓reduceDIte, add_apply,
        TensorialAt.mkHom₂_apply_eq_extend, homDerivativeAux]
      have hW := mdifferentiableAt_extend I A.Model w
      have hfun : (fun y => (L + L') y (extend A.Model w y)) =
          (fun y => L y (extend A.Model w y)) + fun y => L' y (extend A.Model w y) := by
        funext y
        simp
      rw [hfun, cB.isCovariantDerivativeOnUniv.add (hL.clm_bundle_apply hW)
        (hL'.clm_bundle_apply hW)]
      simp only [add_apply, Pi.add_apply]
      abel
    leibniz := fun {L g} {x} hL hg _ => by
      have hgL := hg.smul_section hL
      ext u w
      simp only [homConnectionFun, hL, hgL, ↓reduceDIte, add_apply, smul_apply,
        smulRight_apply, TensorialAt.mkHom₂_apply_eq_extend, homDerivativeAux]
      have hW := mdifferentiableAt_extend I A.Model w
      have hfun : (fun y => (g • L) y (extend A.Model w y)) =
          g • fun y => L y (extend A.Model w y) := by
        funext y
        simp
      rw [hfun, cB.isCovariantDerivativeOnUniv.leibniz (hL.clm_bundle_apply hW) hg]
      simp only [add_apply, smul_apply, smulRight_apply, Pi.smul_apply', extend_apply_self]
      module }

/-- The induced connection is the Leibniz correction on every local differentiable extension. -/
theorem homConnection_apply (cA : Connection A) (cB : Connection B)
    {L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x} {x : M}
    (hL : MDifferentiableAt I (I.prod 𝓘(ℝ, A.Model →L[ℝ] B.Model))
      (fun y => TotalSpace.mk' (A.Model →L[ℝ] B.Model) y (L y)) x)
    {w : ∀ x, A.Fiber x}
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, A.Model))
      (fun y => TotalSpace.mk' A.Model y (w y)) x) (u : TM x) :
    homConnection cA cB L x u (w x) = cB (fun y => L y (w y)) x u - L x (cA w x u) :=
  homConnectionFun_apply cA cB hL hw u

/-! ### Regularity -/

/-- A connection is locally regular when it maps sections that are `C^(n+1)` at a point to
sections of `Hom(TM, A)` that are `C^n` at that point, for every `n`, including `n = ∞`. -/
def Connection.IsLocallyRegular {A : SmoothBundle I (M := M)} (c : Connection A) : Prop :=
  ∀ (n : ℕ∞) {σ : ∀ x, A.Fiber x} {x : M},
    ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) (n + 1)
      (fun y => TotalSpace.mk' A.Model y (σ y)) x →
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] A.Model)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] A.Model) y (c σ y)) x

omit [FiniteDimensional ℝ E] in
/-- A locally regular connection is of class `C^n` in the sense of mathlib, for every `n`. -/
theorem Connection.IsLocallyRegular.contMDiffCovariantDerivative {A : SmoothBundle I (M := M)}
    {c : Connection A} (hc : c.IsLocallyRegular) (n : ℕ∞) :
    CovariantDerivative.ContMDiffCovariantDerivative c n where
  contMDiff := ⟨by
    intro σ hσ
    rw [contMDiffOn_univ] at hσ ⊢
    intro x
    exact hc n (hσ x)⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- A section of the scalar bundle is `C^n` precisely when it is as a function. -/
theorem contMDiffAt_scalar_iff {n : ℕ∞ω} {f : ∀ x, (scalar I (M := M)).Fiber x} {x : M} :
    ContMDiffAt I (I.prod 𝓘(ℝ)) n (fun y => TotalSpace.mk' ℝ y (f y)) x ↔
      ContMDiffAt I 𝓘(ℝ) n (fun y => (f y : ℝ)) x := by
  rw [contMDiffAt_section]
  rfl

omit [FiniteDimensional ℝ E] in
/-- A directional derivative of a `C^(n+1)` function along a `C^n` field is `C^n`. -/
theorem contMDiffAt_mvfderiv_apply {n : ℕ∞} {f : M → ℝ} {X : ∀ x, TM x} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) (n + 1) f x)
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (fun y => TotalSpace.mk' E y (X y)) x) :
    ContMDiffAt I 𝓘(ℝ) n (fun y => mvfderiv I f y (X y)) x := by
  have hd := hf.mfderiv_const (m := n) le_rfl
  have hc : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) n
      (fun y => inCoordinates E (TangentSpace I) ℝ
        (TangentSpace 𝓘(ℝ)) x y (f x) (f y) (mfderiv I 𝓘(ℝ) f y)) x := by
    convert! hd using 1
  have ha := hc.clm_apply_of_inCoordinates hX (hf.of_le (self_le_add_right _ _))
  rw [contMDiffAt_totalSpace] at ha
  have h2 := ha.2
  simp at h2
  exact h2

/-- The directional derivative loses one derivative. -/
theorem scalarConnection_isLocallyRegular :
    (scalarConnection (I := I) (M := M)).IsLocallyRegular := by
  intro n f x hf
  apply contMDiffAt_of_apply (tangent I) (scalar I)
  intro X hX
  apply contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_id, ?_⟩
  exact contMDiffAt_mvfderiv_apply (contMDiffAt_scalar_iff.mp hf) (hX.of_le (by simp))

omit [FiniteDimensional ℝ E] in
private theorem eventually_mdifferentiableAt_of_contMDiffAt (B : SmoothBundle I (M := M))
    {n : ℕ∞} {σ : ∀ x, B.Fiber x} {x : M}
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) (n + 1)
      (fun y => TotalSpace.mk' B.Model y (σ y)) x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I (I.prod 𝓘(ℝ, B.Model))
      (fun y => TotalSpace.mk' B.Model y (σ y)) y := by
  have h₁ := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hσ.of_le (by simp))
  exact h₁.mono fun _ hy => hy.mdifferentiableAt (by norm_num)

/-- The induced connection on a hom bundle is locally regular when both connections are. -/
theorem homConnection_isLocallyRegular {cA : Connection A} {cB : Connection B}
    (hA : cA.IsLocallyRegular) (hB : cB.IsLocallyRegular) :
    (homConnection cA cB).IsLocallyRegular := by
  intro n L x hL
  apply contMDiffAt_of_apply (tangent I) (hom I A B)
  intro X hX
  apply contMDiffAt_of_apply A B
  intro W hW
  have hW₁ : ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) (n + 1)
      (fun y => TotalSpace.mk' A.Model y (W y)) x := hW.of_le (by simp)
  have hXn : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (fun y => TotalSpace.mk' E y (X y)) x :=
    hX.of_le (by simp)
  have hLW : ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) (n + 1)
      (fun y => TotalSpace.mk' B.Model y (L y (W y))) x := hL.clm_bundle_apply hW₁
  have h₁ := (hB n hLW).clm_bundle_apply hXn
  have h₂ := (hL.of_le (self_le_add_right _ _)).clm_bundle_apply
    ((hA n hW₁).clm_bundle_apply hXn)
  apply (h₁.sub_section h₂).congr_of_eventuallyEq
  filter_upwards [eventually_mdifferentiableAt_of_contMDiffAt (hom I A B) hL,
    eventually_mdifferentiableAt_of_contMDiffAt A hW₁] with y hyL hyW
  rw [homConnection_apply cA cB hyL hyW]
  rfl

end SmoothBundle

namespace Shape

variable (cov : CovariantDerivative I E (TangentSpace I (M := M)))

/-- The covariant derivative on each tensor shape induced by a connection on the tangent bundle:
the directional derivative on scalars, the connection on vectors, and the Leibniz correction on
hom shapes. -/
def connection : (s : Shape) → (s.bundle I (M := M)).Connection
  | .scalar => SmoothBundle.scalarConnection
  | .tangent => cov
  | .hom a b => SmoothBundle.homConnection (connection a) (connection b)

@[simp] theorem connection_scalar :
    Shape.scalar.connection cov = SmoothBundle.scalarConnection := rfl

@[simp] theorem connection_tangent : Shape.tangent.connection cov = cov := rfl

theorem connection_hom (a b : Shape) :
    (Shape.hom a b).connection cov =
      SmoothBundle.homConnection (a.connection cov) (b.connection cov) := rfl

/-- On scalars the derivative is the directional derivative. -/
theorem connection_scalar_apply (f : M → ℝ) (x : M) :
    Shape.scalar.connection cov f x = mvfderiv I f x := rfl

/-- On a hom shape the derivative is the Leibniz correction, `(∇_u L)(w x) =
∇_u (L w) − L (∇_u w)`, for every section `w` differentiable at `x`: its value does not depend
on the local extension `w` of the vector `w x`. -/
theorem connection_hom_apply (a b : Shape)
    {L : ∀ x, (a.bundle I (M := M)).Fiber x →L[ℝ] (b.bundle I (M := M)).Fiber x} {x : M}
    (hL : MDifferentiableAt I
      (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model →L[ℝ] (b.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' ((a.bundle I (M := M)).Model →L[ℝ] (b.bundle I (M := M)).Model)
        y (L y)) x)
    {w : ∀ x, (a.bundle I (M := M)).Fiber x}
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (a.bundle I (M := M)).Model y (w y)) x) (u : TM x) :
    (Shape.hom a b).connection cov L x u (w x) =
      b.connection cov (fun y => L y (w y)) x u - L x (a.connection cov w x u) :=
  SmoothBundle.homConnection_apply _ _ hL hw u

/-- The Leibniz rule for evaluation: `∇_u (L w) = (∇_u L) w + L (∇_u w)`. -/
theorem connection_apply_section (a b : Shape)
    {L : ∀ x, (a.bundle I (M := M)).Fiber x →L[ℝ] (b.bundle I (M := M)).Fiber x} {x : M}
    (hL : MDifferentiableAt I
      (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model →L[ℝ] (b.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' ((a.bundle I (M := M)).Model →L[ℝ] (b.bundle I (M := M)).Model)
        y (L y)) x)
    {w : ∀ x, (a.bundle I (M := M)).Fiber x}
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (a.bundle I (M := M)).Model y (w y)) x) (u : TM x) :
    b.connection cov (fun y => L y (w y)) x u =
      (Shape.hom a b).connection cov L x u (w x) + L x (a.connection cov w x u) := by
  rw [connection_hom_apply cov a b hL hw u, sub_add_cancel]

/-- The Leibniz correction depends on the section `w` only through its value at the point. -/
theorem connection_hom_correction_eq (a b : Shape)
    {L : ∀ x, (a.bundle I (M := M)).Fiber x →L[ℝ] (b.bundle I (M := M)).Fiber x} {x : M}
    (hL : MDifferentiableAt I
      (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model →L[ℝ] (b.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' ((a.bundle I (M := M)).Model →L[ℝ] (b.bundle I (M := M)).Model)
        y (L y)) x)
    {w w' : ∀ x, (a.bundle I (M := M)).Fiber x}
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (a.bundle I (M := M)).Model y (w y)) x)
    (hw' : MDifferentiableAt I (I.prod 𝓘(ℝ, (a.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (a.bundle I (M := M)).Model y (w' y)) x)
    (hww' : w x = w' x) (u : TM x) :
    b.connection cov (fun y => L y (w y)) x u - L x (a.connection cov w x u) =
      b.connection cov (fun y => L y (w' y)) x u - L x (a.connection cov w' x u) := by
  rw [← connection_hom_apply cov a b hL hw u, ← connection_hom_apply cov a b hL hw' u, hww']

/-- Additivity on sections differentiable at the point. -/
theorem connection_add (s : Shape) {T T' : ∀ x, (s.bundle I (M := M)).Fiber x} {x : M}
    (hT : MDifferentiableAt I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T y)) x)
    (hT' : MDifferentiableAt I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T' y)) x) :
    s.connection cov (T + T') x = s.connection cov T x + s.connection cov T' x :=
  (s.connection cov).isCovariantDerivativeOnUniv.add hT hT'

/-- The Leibniz rule for a scalar multiple, `∇(f T) = f ∇T + df ⊗ T`. -/
theorem connection_smul (s : Shape) {f : M → ℝ} {T : ∀ x, (s.bundle I (M := M)).Fiber x}
    {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hT : MDifferentiableAt I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T y)) x) :
    s.connection cov (f • T) x =
      f x • s.connection cov T x + (mvfderiv I f x).smulRight (T x) :=
  (s.connection cov).isCovariantDerivativeOnUniv.leibniz hT hf

/-- Linearity over constants. -/
theorem connection_const_smul (s : Shape) (c : ℝ) {T : ∀ x, (s.bundle I (M := M)).Fiber x}
    {x : M} (hT : MDifferentiableAt I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T y)) x) :
    s.connection cov (c • T) x = c • s.connection cov T x :=
  (s.connection cov).isCovariantDerivativeOnUniv.smul_const c hT

/-- The derivative at a point depends only on the germ of the section. -/
theorem connection_congr (s : Shape) {T T' : ∀ x, (s.bundle I (M := M)).Fiber x} {x : M}
    (hT : MDifferentiableAt I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T y)) x)
    (hT' : MDifferentiableAt I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model))
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T' y)) x)
    (hTT' : ∀ᶠ y in 𝓝 x, T y = T' y) :
    s.connection cov T x = s.connection cov T' x :=
  (s.connection cov).isCovariantDerivativeOnUniv.congr_of_eventuallyEq hT hT' Filter.univ_mem
    hTT'

variable {cov}

/-- A locally regular tangent connection induces a locally regular connection on every shape. -/
theorem connection_isLocallyRegular (hcov : SmoothBundle.Connection.IsLocallyRegular
      (A := SmoothBundle.tangent I (M := M)) cov) :
    ∀ s : Shape, (s.connection cov).IsLocallyRegular
  | .scalar => SmoothBundle.scalarConnection_isLocallyRegular
  | .tangent => hcov
  | .hom a b => SmoothBundle.homConnection_isLocallyRegular
      (connection_isLocallyRegular hcov a) (connection_isLocallyRegular hcov b)

/-- The derivative of a smooth tensor of any shape is a smooth section of `Hom(TM, ·)`. -/
theorem contMDiff_connection (hcov : SmoothBundle.Connection.IsLocallyRegular
      (A := SmoothBundle.tangent I (M := M)) cov) (s : Shape)
    {T : ∀ x, (s.bundle I (M := M)).Fiber x}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, (s.bundle I (M := M)).Model)) ∞
      (fun y => TotalSpace.mk' (s.bundle I (M := M)).Model y (T y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (s.bundle I (M := M)).Model)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] (s.bundle I (M := M)).Model) y
        (s.connection cov T y)) := fun x =>
  connection_isLocallyRegular hcov s ⊤ (by simpa using hT x)

/-- The covariant derivative of a smooth tensor of shape `s`, as a smooth tensor of shape
`hom tangent s`; the direction is its first argument. -/
def covariantDerivative (hcov : SmoothBundle.Connection.IsLocallyRegular
      (A := SmoothBundle.tangent I (M := M)) cov) (s : Shape)
    (T : (s.bundle I (M := M)).Section I) : ((Shape.hom .tangent s).bundle I (M := M)).Section I :=
  ⟨s.connection cov T, contMDiff_connection hcov s T.contMDiff⟩

/-- In every bundle chart of `Hom(TM, ·)`, the coefficients of the derivative of a smooth tensor
are smooth on the base set of the chart. -/
theorem coefficients_covariantDerivative_contMDiffOn
    (hcov : SmoothBundle.Connection.IsLocallyRegular (A := SmoothBundle.tangent I (M := M)) cov)
    (s : Shape) (T : (s.bundle I (M := M)).Section I)
    (e : Trivialization ((Shape.hom .tangent s).bundle I (M := M)).Model
      (TotalSpace.proj : TotalSpace _ ((Shape.hom .tangent s).bundle I (M := M)).Fiber → M))
    [MemTrivializationAtlas e] :
    ContMDiffOn I 𝓘(ℝ, ((Shape.hom .tangent s).bundle I (M := M)).Model) ∞
      (SmoothBundle.coefficients I _ e (covariantDerivative hcov s T)) e.baseSet :=
  SmoothBundle.coefficients_contMDiffOn I _ e _

@[simp] theorem covariantDerivative_apply (hcov : SmoothBundle.Connection.IsLocallyRegular
      (A := SmoothBundle.tangent I (M := M)) cov) (s : Shape)
    (T : (s.bundle I (M := M)).Section I) (x : M) :
    covariantDerivative hcov s T x = s.connection cov T x := rfl

end Shape
end ProjectAinos.SmoothGeometry.Tensor
