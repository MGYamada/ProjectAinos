/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.ShapeDerivative
public import ProjectAinos.SmoothGeometry.Lorentzian.ExponentialConformalExample

/-! # The shape connection on a curved conformally flat metric

For the metric `g = e^{2z}(−dt² + dx² + dy² + dz²)` of `ExponentialConformalExample`:

* `metric_shapeConnection_form`: `∇g = 0`, although the components of `g` are not constant
  (`metric_mvfderiv_form_chartField`: `∂_u g(∂_v, ∂_w) = 2 u₃ e^{2z} η(v, w)`).
* `metric_shapeConnection_dz`: the coordinate covector `dz` has constant components and the
  covariant derivative `(∇_i dz)_k = η_{ik} − 2 δ_{i3} δ_{k3}`, which is the Christoffel term with
  its sign; `metric_shapeConnection_dz_ne_zero`: `(∇_t dz)_t = −1`.
-/

@[expose] public section

noncomputable section

open Bundle ContinuousLinearMap TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.ExponentialConformalExample

open LorentzMetric CoordinateMetric

local notation "E" => MinkowskiModel 3
local notation "η" => minkowskiForm LorentzConvention.timeNegative 3

/-- Metric compatibility on the curved metric. -/
theorem metric_shapeConnection_form :
    (Tensor.Shape.covariant 2).connection metric.toLorentzMetric.leviCivita
      (fun y => metric.toLorentzMetric.form y) = 0 :=
  metric.toLorentzMetric.shapeConnection_form

/-- The components of the metric vary: `∂_u g(∂_v, ∂_w) = 2 u₃ e^{2z} η(v, w)`. -/
theorem metric_mvfderiv_form_chartField (x y : (⊤ : Opens E)) (u v w : E) :
    mvfderiv 𝓘(ℝ, E) (fun z => metric.toLorentzMetric.form z (chartField (physicalChart x) v z)
        (chartField (physicalChart x) w z)) y (chartField (physicalChart x) u y) =
      2 * u 3 * Real.exp (2 * (y : E) 3) * η v w := by
  have hfun : (fun z => metric.toLorentzMetric.form z (chartField (physicalChart x) v z)
      (chartField (physicalChart x) w z)) =
      fun z : (⊤ : Opens E) => Real.exp (2 * (z : E) 3) * η v w :=
    funext fun z => metric_form_chartField x z v w
  have hcd : ContDiff ℝ ∞ (fun q : E => Real.exp (2 * q 3) * η v w) := by fun_prop
  have hG : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
      (fun z : (⊤ : Opens E) => Real.exp (2 * (z : E) 3) * η v w) y :=
    ((hcd.contMDiff.comp (contMDiff_subtype_val (U := (⊤ : Opens E)))) y).mdifferentiableAt
      (by simp)
  have hd : HasFDerivAt (fun q : E => Real.exp (2 * q 3) * η v w)
      ((2 * Real.exp (2 * (y : E) 3) * η v w) • (proj 3 : E →L[ℝ] ℝ)) (y : E) := by
    have hp := (proj 3 : E →L[ℝ] ℝ).hasFDerivAt (x := (y : E))
    convert! ((hp.const_mul 2).exp).mul_const (η v w) using 1
    ext u
    simp
    ring
  have hcomp : (fun z : (⊤ : Opens E) => Real.exp (2 * (z : E) 3) * η v w) ∘
      (physicalChart x).symm = fun q : E => Real.exp (2 * q 3) * η v w := by
    funext q
    simp only [Function.comp]
    rw [← physicalChart_apply x ((physicalChart x).symm q),
      (physicalChart x).right_inv (by simp)]
  rw [hfun, mvfderiv_chartField (physicalChart_mem x) (by simp) hG, hcomp, physicalChart_apply,
    hd.fderiv]
  simp only [smul_apply, proj_apply, smul_eq_mul]
  ring

/-- The chart Christoffel symbols are the components of the constant map `Γ`. -/
theorem metric_chartChristoffel (x y : (⊤ : Opens E)) (j i k : Fin 4) :
    metric.toLorentzMetric.chartChristoffel (physicalChart x) y j i k =
      connection (Pi.single i 1) (Pi.single k 1) j := by
  rw [chartChristoffel, metric_leviCivita x y,
    chartTangentMap_field (physicalChart_mem x) (by simp)]

/-- The covariant derivative of `dz`: `(∇_i dz)_k = η_{ik} − 2 δ_{i3} δ_{k3}`. -/
theorem metric_shapeConnection_dz (x y : (⊤ : Opens E)) (i k : Fin 4) :
    Tensor.Shape.cotangent.connection metric.toLorentzMetric.leviCivita
        (fun z => chartCovector (physicalChart x) z 3) y
        (chartField (physicalChart x) (Pi.single i 1) y)
        (chartField (physicalChart x) (Pi.single k 1) y) =
      η (Pi.single i 1) (Pi.single k 1) -
        2 * (Pi.single i 1 : E) 3 * (Pi.single k 1 : E) 3 := by
  rw [metric.toLorentzMetric.shapeConnection_chartCovector_apply (physicalChart_mem x)
    (by simp) i 3 k, metric_chartChristoffel]
  simp only [connection, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_eq_same, mul_one]
  ring

/-- `dz` is not parallel: `(∇_t dz)_t = −1`. -/
theorem metric_shapeConnection_dz_ne_zero (x y : (⊤ : Opens E)) :
    Tensor.Shape.cotangent.connection metric.toLorentzMetric.leviCivita
        (fun z => chartCovector (physicalChart x) z 3) y
        (chartField (physicalChart x) (Pi.single 0 1) y)
        (chartField (physicalChart x) (Pi.single 0 1) y) = -1 := by
  rw [metric_shapeConnection_dz]
  simp [minkowskiForm_apply, lorentzSign, LorentzConvention.timeSign,
    Pi.single_apply]

end ProjectAinos.SmoothGeometry.ExponentialConformalExample
