/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Tensor.ShapeDerivative
public import ProjectAinos.SmoothGeometry.Tensor.TrilinearDerivative

/-! # The shape connection recovers the bilinear and trilinear derivatives

Evaluated on vectors, the connection of `Tensor.Shape.connection` on the shape of a covariant
two-tensor is `Tensor.bilinearCovariantDerivative`, and on the shape of a tangent-valued
trilinear tensor it is `Tensor.trilinearCovariantDerivative`. The direction is the first
argument of the shape connection and the last argument of the earlier derivatives.
-/

@[expose] public section
noncomputable section
open Bundle FiberBundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.Tensor.Shape

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (TangentSpace I (M := M)))

local notation "TM" => TangentSpace I (M := M)

/-- On a smooth covariant two-tensor the shape connection is the bilinear covariant derivative:
`(∇_u B)(v, w) = u(B(v, w)) − B(∇_u v, w) − B(v, ∇_u w)`. -/
theorem connection_covariant_two_apply (B : SmoothBilinear (I := I) (M := M)) (x : M)
    (u v w : TM x) :
    (Shape.covariant 2).connection cov (fun y => B y) x u v w =
      bilinearCovariantDerivative cov B x v w u := by
  have hB : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (B y)) x :=
    (B.contMDiff x).mdifferentiableAt (by simp)
  have hV := mdifferentiableAt_extend I E v
  have hW := mdifferentiableAt_extend I E w
  have hBV := hB.clm_bundle_apply hV
  have h₁ := connection_hom_apply cov .tangent (.hom .tangent .scalar)
    (L := fun y => B y) hB hV u
  have h₂ := connection_hom_apply cov .tangent .scalar
    (L := fun y => B y (extend E v y)) hBV hW u
  have h₃ := bilinearCovariantDerivative_apply cov B hV hW u
  simp only [extend_apply_self] at h₁ h₂ h₃
  rw [h₁, sub_apply, h₂, h₃]
  simp only [connection_scalar_apply, connection_tangent]
  abel

/-- On a smooth tangent-valued trilinear tensor the shape connection is the trilinear covariant
derivative: `(∇_u R)(v, w)z = ∇_u (R(v, w)z) − R(∇_u v, w)z − R(v, ∇_u w)z − R(v, w)∇_u z`. -/
theorem connection_trilinear_apply {R : ∀ x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x}
    (hR : IsSmoothTrilinear R) (x : M) (u v w z : TM x) :
    (Shape.hom .tangent (.hom .tangent (.hom .tangent .tangent))).connection cov R x u v w z =
      trilinearCovariantDerivative cov R hR x v w z u := by
  have hR' := (hR x).mdifferentiableAt (by simp)
  have hV := mdifferentiableAt_extend I E v
  have hW := mdifferentiableAt_extend I E w
  have hZ := mdifferentiableAt_extend I E z
  have h₁ := connection_hom_apply cov .tangent (.hom .tangent (.hom .tangent .tangent))
    (L := R) hR' hV u
  have h₂ := connection_hom_apply cov .tangent (.hom .tangent .tangent)
    (L := fun y => R y (extend E v y)) (hR'.clm_bundle_apply hV) hW u
  have h₃ := connection_hom_apply cov .tangent .tangent
    (L := fun y => R y (extend E v y) (extend E w y))
    ((hR'.clm_bundle_apply hV).clm_bundle_apply hW) hZ u
  have h₄ := trilinearCovariantDerivative_apply cov hR (contMDiffAt_extend I E v)
    (contMDiffAt_extend I E w) (contMDiffAt_extend I E z) u
  simp only [extend_apply_self] at h₁ h₂ h₃ h₄
  rw [h₁, sub_apply, h₂, sub_apply, sub_apply, h₃, h₄]
  simp only [connection_tangent]
  abel

end ProjectAinos.SmoothGeometry.Tensor.Shape
