/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.PostNewtonianRicci
public import ProjectAinos.GeneralRelativity.PostNewtonianSources
import Mathlib.Tactic

/-! # The post-Newtonian metric of smooth dust

Landau–Lifshitz, §106, the field equations of the second approximation for extended bodies: the
metric of the second approximation built from smooth dust solves the Einstein equations up to
`O(c⁻⁴)`, in the coordinates `(t, x)` of `NewtonianCoordinates` with `ε = c⁻²`.

* Potentials of sources on space-time `ℝ × ℝ³`: `pot κ f`, `P[κ, f](t, x) = (κ ⋆ f(t, ·))(x)`,
  for the Newton kernel `K` and the kernel `‖·‖` of the superpotential. For a smooth source
  supported in `ℝ × k` with `k` compact (`IsSource`), `fderiv_pot_apply`: **the derivative along
  any direction `w` of space-time falls on the source**, `D_w P[κ, f] = P[κ, D_w f]` (`dir`);
  `pot_newtonKernel_lapS`: `P[K, Δf] = −f`; `pot_norm_lapS`: `P[‖·‖, Δf] = 8π P[K, f]`;
  `dir_comm`: the derivatives of a smooth source commute.
* `spacetimeMap`: `q ↦ (t, x)`; `pd_comp_spacetimeMap`, `pd2_comp_spacetimeMap`,
  `lap_comp_spacetimeMap`: the partial derivatives of a pulled-back function.
* `SmoothDust`: a proper density `ρ̃` and a velocity `v`, smooth in `(t, x)`, the density supported
  in a compact set, with the continuity equation `∂_t ρ̃ + ∇ · (ρ̃ v) = 0` as a hypothesis. Its
  potentials in the gauge of GR36: `dustNewtonian` `Φ = −4πG N[ρ̃]`, `dustSecond`
  `ψ = −8πG N[ρ̃(v² + U)]` (`U = −Φ`), `dustVector` `B_α = −16πG N[ρ̃ v_α] − (G/2) χ[∂_α ∂_t ρ̃]`
  (`N` the Newton potential, `χ` the superpotential), on `NewtonianCoordinates` `dustPhi`,
  `dustPsi`, `dustB`, and the metric `dustMetric` (`pnCoefficient` of the potentials).
* The field equations of the potentials: `SmoothDust.lap_dustPhi` `ΔΦ = 4πGρ̃`;
  `SmoothDust.gauge` **the gauge condition `3∂_tΦ + ∇ · B = 0`** and `SmoothDust.gauge_rate`;
  `SmoothDust.vector_eq` `ΔB_α − ∂_α ∇ · B − 4∂_t∂_αΦ = 16πGρ̃ v_α`; `SmoothDust.scalar_eq`
  `4ΦΔΦ + Δψ = 8πGρ̃(v² + Φ)`. Hence `SmoothDust.abs_ricciOf_dustMetric_sub_le`: with the
  expansion `abs_ricciOf_pnCoefficient_sub_le` of `PostNewtonianRicci` and the bounds
  `exists_potentialBounds`, `|R_jk − S_jk| ≤ C/c⁴` on bounded sets with `dustRicci`
  `S_tt = 4πGρ̃(1 + 2(v² + Φ)/c²)`, `S_tα = −8πGρ̃ v_α/c²`, `S_αβ = 4πGρ̃ δ_αβ/c²`.
* The matter side: `fourVelocity` `u = γ(1, v)` with `g(u, u) = −c²` (`fourVelocity_norm`),
  `dustStress` `T_ab = ρ̃ u_a u_b`, `trace_dustStress` `g^{ab}T_ab = −ρ̃c²`,
  `traceReversedSource` `κ(T − ½ g tr T)` with `κ = 8πG/c⁴`, and `dustSource` for the metric of
  the dust. `isExp_inv_one_add`: the expansion of `γ² = (γ⁻²)⁻¹` (`normFactor`);
  `exp_dustSource`, `SmoothDust.abs_dustSource_sub_le`: `|κ(T − ½ g T)_jk − S_jk| ≤ C/c⁴`.
* **`SmoothDust.abs_ricciOf_sub_dustSource_le`: the metric of smooth dust solves the Einstein
  equations `R_jk = κ(T_jk − ½ g_jk T)` up to `C/c⁴`**, uniformly on bounded sets of `(t, x)`
  for `c ≥ c₁`.
* Instance: `smoothDust_bump` (a static smooth bump at rest), `exists_smoothDust`.

Not in this file: the next order of the field equations, where the Euler equation of the dust
enters (at the order stated here only the continuity equation is used); the relativistic
continuity equation `∂_μ(√−g ρ̃ u^μ) = 0` in place of the Newtonian one (the difference is
`O(c⁻²)` and changes the estimate only at `O(c⁻⁴)`); and solutions of the Einstein–Euler system
itself, which need its well-posedness, absent from Mathlib.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped Topology ContDiff Real Convolution

namespace ProjectAinos.GeneralRelativity.PostNewtonianDust

open SmoothGeometry.Potential SmoothGeometry.CoordinateMetric PostNewtonianSources
  PostNewtonianRicci NewtonianMetricFamily

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "E" => NewtonianCoordinates

local notation "S" => NewtonianSpace

/-! ### Potentials of sources on space-time -/

section Potentials

/-- A function on space-time `ℝ × ℝ³` that vanishes outside `ℝ × k`. -/
def SupportedIn (k : Set E3) (f : ℝ × E3 → ℝ) : Prop := ∀ t y, y ∉ k → f (t, y) = 0

/-- The potential `P[κ, f](t, x) = (κ ⋆ f(t, ·))(x) = ∫ κ(y) f(t, x − y) dy` of a source on
space-time. -/
def pot (κ : E3 → ℝ) (f : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ :=
  (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun y => f (p.1, y)) p.2

/-- The derivative `D_w f` of a function on space-time along a direction `w`. -/
def dir (w : ℝ × E3) (f : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ := fderiv ℝ f p w

/-- The time direction `(1, 0)`. -/
def eT : ℝ × E3 := (1, 0)

/-- The spatial direction `(0, e_α)`. -/
def eS (α : Fin 3) : ℝ × E3 := (0, EuclideanSpace.single α 1)

/-- The spatial Laplacian `Σ_α D_α D_α f` of a function on space-time. -/
def lapS (f : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ := ∑ α, dir (eS α) (dir (eS α) f) p

variable {κ : E3 → ℝ} {f g : ℝ × E3 → ℝ} {k : Set E3}

theorem pot_apply (κ : E3 → ℝ) (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    pot κ f p = ∫ y, κ y * f (p.1, p.2 - y) := by
  simp [pot, convolution_def]

theorem pot_newtonKernel (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    pot newtonKernel f p = newtonPotential (fun y => f (p.1, y)) p.2 := rfl

theorem pot_norm (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    pot (fun y => ‖y‖) f p = superPotential (fun y => f (p.1, y)) p.2 := rfl

theorem SupportedIn.dir (hk : IsCompact k) (hf : SupportedIn k f) (w : ℝ × E3) :
    SupportedIn k (dir w f) := by
  intro t y hy
  have hev : f =ᶠ[𝓝 (t, y)] fun _ => 0 := by
    have hO : IsOpen ((univ : Set ℝ) ×ˢ kᶜ) := isOpen_univ.prod hk.isClosed.isOpen_compl
    filter_upwards [hO.mem_nhds ⟨mem_univ t, hy⟩] with q hq
    exact hf q.1 q.2 hq.2
  simp [PostNewtonianDust.dir, hev.fderiv_eq]

theorem SupportedIn.add (hf : SupportedIn k f) (hg : SupportedIn k g) :
    SupportedIn k (fun p => f p + g p) := fun t y hy => by simp [hf t y hy, hg t y hy]

theorem SupportedIn.mul_left (hf : SupportedIn k f) (a : ℝ × E3 → ℝ) :
    SupportedIn k (fun p => a p * f p) := fun t y hy => by simp [hf t y hy]

theorem SupportedIn.mul_right (hf : SupportedIn k f) (a : ℝ × E3 → ℝ) :
    SupportedIn k (fun p => f p * a p) := fun t y hy => by simp [hf t y hy]

theorem SupportedIn.hasCompactSupport (hk : IsCompact k) (hf : SupportedIn k f) (t : ℝ) :
    HasCompactSupport fun y => f (t, y) :=
  HasCompactSupport.intro hk fun y hy => hf t y hy

theorem contDiff_dir (hf : ContDiff ℝ ∞ f) (w : ℝ × E3) : ContDiff ℝ ∞ (dir w f) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

theorem contDiff_slice (hf : ContDiff ℝ ∞ f) (t : ℝ) : ContDiff ℝ ∞ fun y : E3 => f (t, y) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

theorem integrable_pot (hκ : LocallyIntegrable κ) (hf : Continuous f) (hk : IsCompact k)
    (hfk : SupportedIn k f) (p : ℝ × E3) : Integrable fun y => κ y * f (p.1, p.2 - y) := by
  have h := (hfk.hasCompactSupport hk p.1).convolutionExists_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hκ (hf.comp (continuous_const.prodMk continuous_id)) p.2
  simp only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] at h
  exact h

theorem pot_add (hκ : LocallyIntegrable κ) (hf : Continuous f) (hg : Continuous g)
    (hk : IsCompact k) (hfk : SupportedIn k f) (hgk : SupportedIn k g) (p : ℝ × E3) :
    pot κ (fun q => f q + g q) p = pot κ f p + pot κ g p := by
  simp only [pot_apply, mul_add]
  exact integral_add (integrable_pot hκ hf hk hfk p) (integrable_pot hκ hg hk hgk p)

theorem pot_const_mul (a : ℝ) (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    pot κ (fun q => a * f q) p = a * pot κ f p := by
  simp only [pot_apply, mul_left_comm _ a]
  exact integral_const_mul a _

theorem pot_sum {ι : Type} (s : Finset ι) {F : ι → ℝ × E3 → ℝ} (hκ : LocallyIntegrable κ)
    (hF : ∀ i, Continuous (F i)) (hk : IsCompact k) (hFk : ∀ i, SupportedIn k (F i))
    (p : ℝ × E3) : pot κ (fun q => ∑ i ∈ s, F i q) p = ∑ i ∈ s, pot κ (F i) p := by
  simp only [pot_apply, Finset.mul_sum]
  exact integral_finsetSum s fun i _ => integrable_pot hκ (hF i) hk (hFk i) p

theorem pot_congr {f g : ℝ × E3 → ℝ} (h : ∀ q, f q = g q) (p : ℝ × E3) : pot κ f p = pot κ g p := by
  rw [funext h]

/-- **The derivative of a potential falls on the source**: `D_w P[κ, f] = P[κ, D_w f]`, for a
smooth source supported in `ℝ × k` with `k` compact and a locally integrable kernel. -/
theorem fderiv_pot_apply (hκ : LocallyIntegrable κ) (hf : ContDiff ℝ ∞ f) (hk : IsCompact k)
    (hfk : SupportedIn k f) (p w : ℝ × E3) : fderiv ℝ (pot κ f) p w = pot κ (dir w f) p := by
  have h := hasFDerivAt_convolution_right_with_param (ContinuousLinearMap.lsmul ℝ ℝ)
    (g := fun t y => f (t, y)) (s := univ) isOpen_univ hk (fun t x _ hx => hfk t x hx) hκ
    (by rw [univ_prod_univ]; exact (hf.of_le (by simp)).contDiffOn) p (mem_univ _)
  have h' : HasFDerivAt (pot κ f) _ p := h
  rw [h'.fderiv]
  have hd : Continuous fun y => fderiv ℝ f (p.1, y) :=
    (hf.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)
  have hcs : HasCompactSupport fun y => fderiv ℝ f (p.1, y) := by
    refine HasCompactSupport.intro hk fun y hy => ?_
    have hev : f =ᶠ[𝓝 (p.1, y)] fun _ => 0 := by
      have hO : IsOpen ((univ : Set ℝ) ×ˢ kᶜ) := isOpen_univ.prod hk.isClosed.isOpen_compl
      filter_upwards [hO.mem_nhds ⟨mem_univ _, hy⟩] with q hq
      exact hfk q.1 q.2 hq.2
    rw [hev.fderiv_eq]
    simp
  exact convolution_precompR_apply _ hκ hcs hd p.2 w

theorem contDiff_pot (hκ : LocallyIntegrable κ) (hf : ContDiff ℝ ∞ f) (hk : IsCompact k)
    (hfk : SupportedIn k f) : ContDiff ℝ ∞ (pot κ f) :=
  contDiff_convolution_param (f := fun t y => f (t, y)) hκ hf hk hfk

theorem dir_slice (hf : Differentiable ℝ f) (t : ℝ) (y w : E3) :
    dir (0, w) f (t, y) = fderiv ℝ (fun z => f (t, z)) y w := by
  have h : HasFDerivAt (fun z => f (t, z))
      ((fderiv ℝ f (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E3)) y :=
    (hf (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
  rw [h.fderiv]
  simp [PostNewtonianDust.dir]

theorem dir_time (hf : Differentiable ℝ f) (t : ℝ) (y : E3) :
    dir eT f (t, y) = deriv (fun s => f (s, y)) t := by
  have hl : HasDerivAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : E3)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have h : HasDerivAt (fun s => f (s, y)) (fderiv ℝ f (t, y) (1, 0)) t :=
    (hf (t, y)).hasFDerivAt.comp_hasDerivAt t hl
  rw [h.deriv]
  rfl

/-- The spatial Laplacian of a smooth source is the Laplacian of its time slices. -/
theorem lapS_eq (hf : ContDiff ℝ ∞ f) (t : ℝ) (y : E3) :
    lapS f (t, y) = coordLaplacian (fun z => f (t, z)) y := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  unfold lapS coordLaplacian
  refine Finset.sum_congr rfl fun α _ => ?_
  have h1 (z : E3) : dir (eS α) f (t, z) =
      fderiv ℝ (fun z => f (t, z)) z (EuclideanSpace.single α 1) := dir_slice hd t z _
  rw [show eS α = (0, EuclideanSpace.single α 1) from rfl,
    dir_slice ((contDiff_dir hf _).differentiable (by simp)) t y, ← show eS α =
      (0, EuclideanSpace.single α 1) from rfl]
  simp only [h1]

/-- **Poisson's equation for the potentials**: `P[K, Δf] = −f` for the Newton kernel `K`. -/
theorem pot_newtonKernel_lapS (hf : ContDiff ℝ ∞ f) (hk : IsCompact k) (hfk : SupportedIn k f)
    (p : ℝ × E3) : pot newtonKernel (lapS f) p = -f p := by
  have hs : ContDiff ℝ 2 fun y => f (p.1, y) := (contDiff_slice hf p.1).of_le (by simp)
  have hc := hfk.hasCompactSupport hk p.1
  rw [pot_newtonKernel]
  have he : (fun y => lapS f (p.1, y)) = coordLaplacian fun z => f (p.1, z) :=
    funext fun y => lapS_eq hf p.1 y
  rw [he, ← coordLaplacian_newtonPotential hc hs,
    coordLaplacian_eq_laplacian (contDiff_two_newtonPotential hc hs).contDiffAt,
    laplacian_newtonPotential hc hs]

/-- `P[‖·‖, Δf] = 8π P[K, f]`, the superpotential of a Laplacian. -/
theorem pot_norm_lapS (hf : ContDiff ℝ ∞ f) (hk : IsCompact k) (hfk : SupportedIn k f)
    (p : ℝ × E3) : pot (fun y => ‖y‖) (lapS f) p = 8 * π * pot newtonKernel f p := by
  have hs : ContDiff ℝ 2 fun y => f (p.1, y) := (contDiff_slice hf p.1).of_le (by simp)
  have hc := hfk.hasCompactSupport hk p.1
  rw [pot_norm, pot_newtonKernel]
  have he : (fun y => lapS f (p.1, y)) = coordLaplacian fun z => f (p.1, z) :=
    funext fun y => lapS_eq hf p.1 y
  rw [he, superPotential_coordLaplacian hc hs]

end Potentials

/-! ### The algebra of sources and their derivatives -/

section Algebra

variable {κ : E3 → ℝ} {f g : ℝ × E3 → ℝ} {k : Set E3}

/-- A smooth source on space-time supported in `ℝ × k`. -/
def IsSource (k : Set E3) (f : ℝ × E3 → ℝ) : Prop := ContDiff ℝ ∞ f ∧ SupportedIn k f

theorem isSource_zero (k : Set E3) : IsSource k fun _ => 0 :=
  ⟨contDiff_const, fun _ _ _ => rfl⟩

theorem IsSource.dir (hk : IsCompact k) (hf : IsSource k f) (w : ℝ × E3) :
    IsSource k (dir w f) :=
  ⟨contDiff_dir hf.1 w, hf.2.dir hk w⟩

theorem IsSource.add (hf : IsSource k f) (hg : IsSource k g) :
    IsSource k fun p => f p + g p :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem IsSource.mul_left {a : ℝ × E3 → ℝ} (ha : ContDiff ℝ ∞ a) (hf : IsSource k f) :
    IsSource k fun p => a p * f p :=
  ⟨ha.mul hf.1, hf.2.mul_left a⟩

theorem IsSource.mul_right' {a : ℝ × E3 → ℝ} (hf : IsSource k f) (ha : ContDiff ℝ ∞ a) :
    IsSource k fun p => f p * a p :=
  ⟨hf.1.mul ha, hf.2.mul_right a⟩

theorem IsSource.const_mul (a : ℝ) (hf : IsSource k f) : IsSource k fun p => a * f p :=
  hf.mul_left (a := fun _ => a) contDiff_const

theorem IsSource.sum {ι : Type} (s : Finset ι) {F : ι → ℝ × E3 → ℝ}
    (hF : ∀ i, IsSource k (F i)) : IsSource k fun p => ∑ i ∈ s, F i p :=
  ⟨ContDiff.sum fun i _ => (hF i).1, fun t y hy => Finset.sum_eq_zero fun i _ => (hF i).2 t y hy⟩

theorem IsSource.lapS (hk : IsCompact k) (hf : IsSource k f) : IsSource k (lapS f) :=
  IsSource.sum _ fun _ => (hf.dir hk _).dir hk _

theorem dir_add (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (w : ℝ × E3) :
    dir w (fun p => f p + g p) = fun p => dir w f p + dir w g p := by
  funext p
  simp [PostNewtonianDust.dir, fderiv_fun_add (hf p) (hg p)]

theorem dir_const_mul (a : ℝ) (hf : Differentiable ℝ f) (w : ℝ × E3) :
    dir w (fun p => a * f p) = fun p => a * dir w f p := by
  funext p
  simp [PostNewtonianDust.dir, fderiv_const_mul (hf p) a]

theorem dir_sum {ι : Type} (s : Finset ι) {F : ι → ℝ × E3 → ℝ}
    (hF : ∀ i, Differentiable ℝ (F i)) (w : ℝ × E3) :
    dir w (fun p => ∑ i ∈ s, F i p) = fun p => ∑ i ∈ s, dir w (F i) p := by
  funext p
  simp [PostNewtonianDust.dir, fderiv_fun_sum fun i _ => hF i p]

theorem dir_dir_eq (hf : ContDiff ℝ ∞ f) (a b p : ℝ × E3) :
    dir a (dir b f) p = fderiv ℝ (fderiv ℝ f) p a b := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp)) p
  show fderiv ℝ (fun y => fderiv ℝ f y b) p a = _
  rw [fderiv_clm_apply hd (differentiableAt_const b)]
  simp

/-- **The derivatives of a smooth source commute**: `D_a D_b f = D_b D_a f`. -/
theorem dir_comm (hf : ContDiff ℝ ∞ f) (a b : ℝ × E3) : dir a (dir b f) = dir b (dir a f) := by
  funext p
  rw [dir_dir_eq hf, dir_dir_eq hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) a b

theorem dir_lapS (hf : ContDiff ℝ ∞ f) (w : ℝ × E3) : dir w (lapS f) = lapS (dir w f) := by
  unfold lapS
  rw [dir_sum _ fun α => (contDiff_dir (contDiff_dir hf _) _).differentiable (by simp)]
  funext p
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [dir_comm (contDiff_dir hf _), dir_comm hf w (eS α)]

theorem dir_pot (hκ : LocallyIntegrable κ) (hk : IsCompact k) (hf : IsSource k f)
    (w : ℝ × E3) : dir w (pot κ f) = pot κ (dir w f) :=
  funext fun p => fderiv_pot_apply hκ hf.1 hk hf.2 p w

theorem lapS_pot (hκ : LocallyIntegrable κ) (hk : IsCompact k) (hf : IsSource k f) :
    lapS (pot κ f) = pot κ (lapS f) := by
  funext p
  unfold lapS
  simp only [dir_pot hκ hk hf, dir_pot hκ hk (hf.dir hk _)]
  exact (pot_sum _ hκ (fun α => (((hf.dir hk _).dir hk _).1).continuous) hk
    (fun α => ((hf.dir hk _).dir hk _).2) p).symm

end Algebra

/-! ### The coordinates `(t, x)` of `NewtonianCoordinates` -/

section Pullback

/-- The point `x ∈ ℝ³` of `q = (t, x)`. -/
def spatialPoint (q : E) : E3 := WithLp.toLp 2 (Fin.tail q)

/-- The linear map `q ↦ (t, x)` from `NewtonianCoordinates` to space-time `ℝ × ℝ³`. -/
def spacetimeMap : E →L[ℝ] ℝ × E3 :=
  (ContinuousLinearMap.proj 0).prod ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i : Fin 3 => ContinuousLinearMap.proj i.succ)

theorem spacetimeMap_apply (q : E) : spacetimeMap q = (q 0, spatialPoint q) := rfl

theorem spacetimeMap_single_zero : spacetimeMap (Pi.single 0 1) = eT := by
  rw [spacetimeMap_apply, eT]
  refine Prod.ext (by simp) ?_
  ext i
  simp [spatialPoint, Fin.tail, Fin.succ_ne_zero]

theorem spacetimeMap_single_succ (α : Fin 3) : spacetimeMap (Pi.single α.succ 1) = eS α := by
  rw [spacetimeMap_apply, eS]
  refine Prod.ext (by simp [Fin.succ_ne_zero]) ?_
  ext i
  simp [spatialPoint, Fin.tail, Pi.single_apply]

theorem pd_comp_spacetimeMap {F : ℝ × E3 → ℝ} (hF : Differentiable ℝ F) (q : E) (m : Fin 4) :
    pd (F ∘ spacetimeMap) q m = dir (spacetimeMap (Pi.single m 1)) F (spacetimeMap q) := by
  have h : HasFDerivAt (F ∘ spacetimeMap) ((fderiv ℝ F (spacetimeMap q)).comp spacetimeMap) q :=
    (hF _).hasFDerivAt.comp q spacetimeMap.hasFDerivAt
  simp [pd, h.fderiv, PostNewtonianDust.dir]

theorem pd2_comp_spacetimeMap {F : ℝ × E3 → ℝ} (hF : ContDiff ℝ ∞ F) (q : E) (m n : Fin 4) :
    pd2 (F ∘ spacetimeMap) q m n = dir (spacetimeMap (Pi.single m 1))
      (dir (spacetimeMap (Pi.single n 1)) F) (spacetimeMap q) := by
  have hd := hF.differentiable (by simp)
  have he : (fun z => fderiv ℝ (F ∘ spacetimeMap) z (Pi.single n 1)) =
      dir (spacetimeMap (Pi.single n 1)) F ∘ spacetimeMap :=
    funext fun z => pd_comp_spacetimeMap hd z n
  unfold pd2
  rw [he]
  exact pd_comp_spacetimeMap ((contDiff_dir hF _).differentiable (by simp)) q m

theorem contDiff_comp_spacetimeMap {F : ℝ × E3 → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (F ∘ spacetimeMap) :=
  hF.comp spacetimeMap.contDiff

theorem sd_comp_spacetimeMap {F : ℝ × E3 → ℝ} (hF : ContDiff ℝ ∞ F) (q : E) (m n : Fin 4) :
    sd (F ∘ spacetimeMap) q m n = dir (spacetimeMap (Pi.single m 1))
      (dir (spacetimeMap (Pi.single n 1)) F) (spacetimeMap q) := by
  rw [← pd2_eq_sd ((contDiff_comp_spacetimeMap hF).contDiffAt.of_le (by simp)),
    pd2_comp_spacetimeMap hF]

/-- The flat Laplacian of a pulled-back function is the spatial Laplacian. -/
theorem lap_comp_spacetimeMap {F : ℝ × E3 → ℝ} (hF : ContDiff ℝ ∞ F) (q : E) :
    lap (F ∘ spacetimeMap) q = lapS F (spacetimeMap q) := by
  simp only [lap, lapS, Fin.sum_univ_three]
  rw [sd_comp_spacetimeMap hF, sd_comp_spacetimeMap hF, sd_comp_spacetimeMap hF]
  rw [show (1 : Fin 4) = (0 : Fin 3).succ from rfl, show (2 : Fin 4) = (1 : Fin 3).succ from rfl,
    show (3 : Fin 4) = (2 : Fin 3).succ from rfl, spacetimeMap_single_succ,
    spacetimeMap_single_succ, spacetimeMap_single_succ]

end Pullback

theorem lapS_add {f g : ℝ × E3 → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    lapS (fun p => f p + g p) = fun p => lapS f p + lapS g p := by
  have hd {h : ℝ × E3 → ℝ} (hh : ContDiff ℝ ∞ h) : Differentiable ℝ h := hh.differentiable (by simp)
  funext p
  unfold lapS
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [dir_add (hd hf) (hd hg), dir_add (hd (contDiff_dir hf _)) (hd (contDiff_dir hg _))]

/-! ### Smooth dust and its potentials -/

section Dust

/-- **Smooth dust**: a proper density `ρ̃` and a velocity field `v`, both smooth in `(t, x)`, the
density supported in the compact set `k` of space at all times, and the continuity equation
`∂_t ρ̃ + ∇ · (ρ̃ v) = 0` as an explicit hypothesis on the data. -/
structure SmoothDust (k : Set E3) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) : Prop where
  density_smooth : ContDiff ℝ ∞ (Function.uncurry ρ)
  velocity_smooth : ContDiff ℝ ∞ (Function.uncurry v)
  isCompact : IsCompact k
  support : ∀ t y, y ∉ k → ρ t y = 0
  continuity : ∀ t y, deriv (fun s => ρ s y) t +
    ∑ j, fderiv ℝ (fun z => ρ t z * v t z j) y (EuclideanSpace.single j 1) = 0

/-- The Newtonian potential `Φ = −4πG N[ρ̃]` of the dust at the time `t`, so `ΔΦ = 4πGρ̃`. -/
def dustNewtonian (G : ℝ) (ρ : ℝ → E3 → ℝ) (t : ℝ) : E3 → ℝ :=
  newtonPotential fun y => -(4 * π * G) * ρ t y

/-- The second potential `ψ = −8πG N[ρ̃(v² + U)]` with `U = −Φ`, so `Δψ = 8πGρ̃(v² + U)`. -/
def dustSecond (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (t : ℝ) : E3 → ℝ :=
  newtonPotential fun y => -(8 * π * G) * (ρ t y * (‖v t y‖ ^ 2 - dustNewtonian G ρ t y))

/-- The vector potential in the gauge of GR36, `B_α = −16πG N[ρ̃ v_α] − (G/2) χ[∂_α ∂_t ρ̃]`
(`N` the Newton potential, `χ` the superpotential); with `V_α = G ∫ ρ̃ v_α/r` and
`X = G ∫ ρ̃ r`, `B_α = −4V_α − (1/2) ∂_t ∂_α X`. -/
def dustVector (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (t : ℝ) (α : Fin 3) (x : E3) : ℝ :=
  newtonPotential (fun y => -(16 * π * G) * (ρ t y * v t y α)) x +
    superPotential (fun y => -(G / 2) *
      fderiv ℝ (fun z => deriv (fun s => ρ s z) t) y (EuclideanSpace.single α 1)) x

/-- The Newtonian potential on `NewtonianCoordinates`. -/
def dustPhi (G : ℝ) (ρ : ℝ → E3 → ℝ) (q : E) : ℝ := dustNewtonian G ρ (q 0) (spatialPoint q)

/-- The second potential on `NewtonianCoordinates`. -/
def dustPsi (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (q : E) : ℝ :=
  dustSecond G ρ v (q 0) (spatialPoint q)

/-- The vector potential on `NewtonianCoordinates`. -/
def dustB (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (q : E) : S := fun α =>
  dustVector G ρ v (q 0) α (spatialPoint q)

/-- **The post-Newtonian metric of the dust**: `pnCoefficient` of the potentials `Φ`, `ψ`, `B`. -/
def dustMetric (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (c : ℝ) (q : E) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  pnCoefficient (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) c q

/-- The source `−4πG ρ̃` of `Φ` on space-time. -/
def srcPhi (G : ℝ) (ρ : ℝ → E3 → ℝ) (p : ℝ × E3) : ℝ := -(4 * π * G) * ρ p.1 p.2

/-- The source of `ψ` on space-time. -/
def srcPsi (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (p : ℝ × E3) : ℝ :=
  -(8 * π * G) * (ρ p.1 p.2 * (‖v p.1 p.2‖ ^ 2 - dustNewtonian G ρ p.1 p.2))

/-- The source `−16πG ρ̃ v_α` of the Newton part of `B_α`. -/
def srcA (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (α : Fin 3) (p : ℝ × E3) : ℝ :=
  -(16 * π * G) * (ρ p.1 p.2 * v p.1 p.2 α)

/-- The source `−(G/2) ∂_α ∂_t ρ̃` of the superpotential part of `B_α`. -/
def srcW (G : ℝ) (ρ : ℝ → E3 → ℝ) (α : Fin 3) (p : ℝ × E3) : ℝ :=
  -(G / 2) * fderiv ℝ (fun z => deriv (fun s => ρ s z) p.1) p.2 (EuclideanSpace.single α 1)

/-- The vector potential on space-time. -/
def potB (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (α : Fin 3) (p : ℝ × E3) : ℝ :=
  pot newtonKernel (srcA G ρ v α) p + pot (fun y => ‖y‖) (srcW G ρ α) p

variable {G : ℝ} {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3} {k : Set E3}

theorem dustNewtonian_eq (p : ℝ × E3) :
    dustNewtonian G ρ p.1 p.2 = pot newtonKernel (srcPhi G ρ) p := rfl

theorem dustPhi_eq : dustPhi G ρ = pot newtonKernel (srcPhi G ρ) ∘ spacetimeMap := rfl

theorem dustPsi_eq : dustPsi G ρ v = pot newtonKernel (srcPsi G ρ v) ∘ spacetimeMap := rfl

theorem comp_dustB (α : Fin 3) : comp (dustB G ρ v) α = potB G ρ v α ∘ spacetimeMap := rfl

theorem srcPhi_eq : srcPhi G ρ = fun p => -(4 * π * G) * Function.uncurry ρ p := rfl

theorem srcPsi_eq : srcPsi G ρ v = fun p => -(8 * π * G) * (Function.uncurry ρ p *
    (‖Function.uncurry v p‖ ^ 2 - pot newtonKernel (srcPhi G ρ) p)) := rfl

theorem SmoothDust.isSource (h : SmoothDust k ρ v) : IsSource k (Function.uncurry ρ) :=
  ⟨h.density_smooth, fun t y hy => h.support t y hy⟩

theorem SmoothDust.isSource_srcPhi (h : SmoothDust k ρ v) : IsSource k (srcPhi G ρ) := by
  rw [srcPhi_eq]
  exact h.isSource.const_mul _

theorem SmoothDust.contDiff_velocity (h : SmoothDust k ρ v) (α : Fin 3) :
    ContDiff ℝ ∞ fun p : ℝ × E3 => v p.1 p.2 α :=
  (EuclideanSpace.proj α : E3 →L[ℝ] ℝ).contDiff.comp h.velocity_smooth

theorem SmoothDust.isSource_srcA (h : SmoothDust k ρ v) (α : Fin 3) :
    IsSource k (srcA G ρ v α) := by
  have h1 : IsSource k fun p : ℝ × E3 => Function.uncurry ρ p * v p.1 p.2 α :=
    ⟨h.density_smooth.mul (h.contDiff_velocity α), h.isSource.2.mul_right _⟩
  exact h1.const_mul _

theorem SmoothDust.isSource_srcPsi (h : SmoothDust k ρ v) : IsSource k (srcPsi G ρ v) := by
  have hΦ := h.isSource_srcPhi (G := G)
  have hP : ContDiff ℝ ∞ (pot newtonKernel (srcPhi G ρ)) :=
    contDiff_pot locallyIntegrable_newtonKernel hΦ.1 h.isCompact hΦ.2
  have hv2 : ContDiff ℝ ∞ fun p : ℝ × E3 => ‖Function.uncurry v p‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp h.velocity_smooth
  rw [srcPsi_eq]
  exact (h.isSource.mul_right' (hv2.sub hP)).const_mul _

/-- The source of the superpotential part is `−(G/2) D_α D_t ρ̃`. -/
theorem SmoothDust.srcW_eq (h : SmoothDust k ρ v) (α : Fin 3) :
    srcW G ρ α = fun p => -(G / 2) * dir (eS α) (dir eT (Function.uncurry ρ)) p := by
  have hd := h.density_smooth.differentiable (by simp)
  have hd' := (contDiff_dir h.density_smooth eT).differentiable (by simp)
  funext p
  have he : (fun z => deriv (fun s => ρ s z) p.1) = fun z => dir eT (Function.uncurry ρ) (p.1, z) :=
    funext fun z => (dir_time hd p.1 z).symm
  rw [srcW, he, show eS α = (0, EuclideanSpace.single α 1) from rfl, dir_slice hd']

theorem SmoothDust.isSource_srcW (h : SmoothDust k ρ v) (α : Fin 3) :
    IsSource k (srcW G ρ α) := by
  rw [h.srcW_eq]
  exact ((h.isSource.dir h.isCompact _).dir h.isCompact _).const_mul _

/-- The continuity equation on space-time: `Σ_α D_α(−16πG ρ̃ v_α) = 16πG D_t ρ̃`. -/
theorem SmoothDust.sum_dir_srcA (h : SmoothDust k ρ v) (p : ℝ × E3) :
    ∑ α, dir (eS α) (srcA G ρ v α) p = 16 * π * G * dir eT (Function.uncurry ρ) p := by
  obtain ⟨t, y⟩ := p
  have hd := h.density_smooth.differentiable (by simp)
  have hj (α : Fin 3) : Differentiable ℝ fun p : ℝ × E3 => Function.uncurry ρ p * v p.1 p.2 α :=
    (h.density_smooth.mul (h.contDiff_velocity α)).differentiable (by simp)
  have hc := h.continuity t y
  have h1 (α : Fin 3) : dir (eS α) (srcA G ρ v α) (t, y) = -(16 * π * G) *
      fderiv ℝ (fun z => ρ t z * v t z α) y (EuclideanSpace.single α 1) := by
    have e : dir (eS α) (srcA G ρ v α) = fun p => -(16 * π * G) *
        dir (eS α) (fun p : ℝ × E3 => Function.uncurry ρ p * v p.1 p.2 α) p :=
      dir_const_mul (-(16 * π * G)) (hj α) (eS α)
    rw [e, show eS α = (0, EuclideanSpace.single α 1) from rfl]
    beta_reduce
    rw [dir_slice (hj α)]
    rfl
  rw [Finset.sum_congr rfl fun α _ => h1 α, ← Finset.mul_sum, dir_time hd]
  simp only [Function.uncurry_apply_pair]
  linear_combination (-(16 * π * G)) * hc

end Dust

/-! ### The field equations of the potentials -/

section Identities

variable {G : ℝ} {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3} {k : Set E3}

theorem SmoothDust.contDiff_potPhi (h : SmoothDust k ρ v) :
    ContDiff ℝ ∞ (pot newtonKernel (srcPhi G ρ)) :=
  contDiff_pot locallyIntegrable_newtonKernel h.isSource_srcPhi.1 h.isCompact h.isSource_srcPhi.2

theorem SmoothDust.contDiff_potPsi (h : SmoothDust k ρ v) :
    ContDiff ℝ ∞ (pot newtonKernel (srcPsi G ρ v)) :=
  contDiff_pot locallyIntegrable_newtonKernel h.isSource_srcPsi.1 h.isCompact h.isSource_srcPsi.2

theorem SmoothDust.contDiff_potB (h : SmoothDust k ρ v) (α : Fin 3) :
    ContDiff ℝ ∞ (potB G ρ v α) :=
  (contDiff_pot locallyIntegrable_newtonKernel (h.isSource_srcA α).1 h.isCompact
    (h.isSource_srcA α).2).add
    (contDiff_pot locallyIntegrable_norm (h.isSource_srcW α).1 h.isCompact (h.isSource_srcW α).2)

theorem SmoothDust.contDiff_dustPhi (h : SmoothDust k ρ v) : ContDiff ℝ ∞ (dustPhi G ρ) :=
  contDiff_comp_spacetimeMap h.contDiff_potPhi

theorem SmoothDust.contDiff_dustPsi (h : SmoothDust k ρ v) : ContDiff ℝ ∞ (dustPsi G ρ v) :=
  contDiff_comp_spacetimeMap h.contDiff_potPsi

theorem SmoothDust.contDiff_dustB (h : SmoothDust k ρ v) (α : Fin 3) :
    ContDiff ℝ ∞ (comp (dustB G ρ v) α) :=
  contDiff_comp_spacetimeMap (h.contDiff_potB α)

/-- **Poisson's equation of the Newtonian potential**, `ΔΦ = 4πGρ̃`. -/
theorem SmoothDust.lap_dustPhi (h : SmoothDust k ρ v) (q : E) :
    lap (dustPhi G ρ) q = 4 * π * G * ρ (q 0) (spatialPoint q) := by
  have hs := h.isSource_srcPhi (G := G)
  rw [dustPhi_eq, lap_comp_spacetimeMap h.contDiff_potPhi,
    lapS_pot locallyIntegrable_newtonKernel h.isCompact hs,
    pot_newtonKernel_lapS hs.1 h.isCompact hs.2, spacetimeMap_apply, srcPhi]
  ring

/-- The equation of the second potential, `Δψ = 8πGρ̃(v² − Φ)`. -/
theorem SmoothDust.lap_dustPsi (h : SmoothDust k ρ v) (q : E) :
    lap (dustPsi G ρ v) q = 8 * π * G * (ρ (q 0) (spatialPoint q) *
      (‖v (q 0) (spatialPoint q)‖ ^ 2 - dustPhi G ρ q)) := by
  have hs := h.isSource_srcPsi (G := G)
  rw [dustPsi_eq, lap_comp_spacetimeMap h.contDiff_potPsi,
    lapS_pot locallyIntegrable_newtonKernel h.isCompact hs,
    pot_newtonKernel_lapS hs.1 h.isCompact hs.2, spacetimeMap_apply, srcPsi]
  simp only [dustPhi]
  ring

/-- **The gauge condition of GR36 for smooth dust**: `3 ∂_t Φ + ∇ · B = 0`, from the continuity
equation and `χ[Δf] = 8π N[f]`. -/
theorem SmoothDust.gauge (h : SmoothDust k ρ v) (q : E) :
    3 * pd (dustPhi G ρ) q 0 + ∑ α, pd (comp (dustB G ρ v) α) q α.succ = 0 := by
  have hk := h.isCompact
  have hK := locallyIntegrable_newtonKernel
  have hN := locallyIntegrable_norm
  have hρ := h.isSource
  have hρd : Differentiable ℝ (Function.uncurry ρ) := hρ.1.differentiable (by simp)
  have hΦs := h.isSource_srcPhi (G := G)
  have hAs := fun α => h.isSource_srcA (G := G) α
  have hWs := fun α => h.isSource_srcW (G := G) α
  set p := spacetimeMap q
  have h1 : pd (dustPhi G ρ) q 0 =
      -(4 * π * G) * pot newtonKernel (dir eT (Function.uncurry ρ)) p := by
    rw [dustPhi_eq, pd_comp_spacetimeMap (h.contDiff_potPhi.differentiable (by simp)),
      spacetimeMap_single_zero, dir_pot hK hk hΦs, srcPhi_eq, dir_const_mul _ hρd, pot_const_mul]
  have h2 (α : Fin 3) : pd (comp (dustB G ρ v) α) q α.succ =
      pot newtonKernel (dir (eS α) (srcA G ρ v α)) p +
        pot (fun y => ‖y‖) (dir (eS α) (srcW G ρ α)) p := by
    rw [comp_dustB, pd_comp_spacetimeMap ((h.contDiff_potB α).differentiable (by simp)),
      spacetimeMap_single_succ]
    unfold potB
    rw [dir_add ((contDiff_pot hK (hAs α).1 hk (hAs α).2).differentiable (by simp))
      ((contDiff_pot hN (hWs α).1 hk (hWs α).2).differentiable (by simp)),
      dir_pot hK hk (hAs α), dir_pot hN hk (hWs α)]
  have h3 : ∑ α, pot newtonKernel (dir (eS α) (srcA G ρ v α)) p =
      16 * π * G * pot newtonKernel (dir eT (Function.uncurry ρ)) p := by
    rw [← pot_sum _ hK (fun α => ((hAs α).dir hk _).1.continuous) hk
      (fun α => ((hAs α).dir hk _).2) p, pot_congr h.sum_dir_srcA p, pot_const_mul]
  have h4 : ∑ α, pot (fun y => ‖y‖) (dir (eS α) (srcW G ρ α)) p =
      -(G / 2) * (8 * π * pot newtonKernel (dir eT (Function.uncurry ρ)) p) := by
    have hd2 := hρ.dir hk eT
    have e (p' : ℝ × E3) : ∑ α, dir (eS α) (srcW G ρ α) p' =
        -(G / 2) * lapS (dir eT (Function.uncurry ρ)) p' := by
      simp only [h.srcW_eq]
      unfold lapS
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [dir_const_mul _ ((hd2.dir hk _).1.differentiable (by simp))]
    rw [← pot_sum _ hN (fun α => ((hWs α).dir hk _).1.continuous) hk
      (fun α => ((hWs α).dir hk _).2) p, pot_congr e p, pot_const_mul,
      pot_norm_lapS hd2.1 hk hd2.2]
  rw [h1, Finset.sum_congr rfl fun α _ => h2 α, Finset.sum_add_distrib, h3, h4]
  ring

theorem differentiableAt_pd {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (n : Fin 4) (q : E) :
    DifferentiableAt ℝ (fun z => pd g z n) q :=
  (((contDiff_infty_iff_fderiv.mp hg).2.clm_apply contDiff_const).differentiable (by simp)) q

theorem pd2_eq_fderiv_pd (g : E → ℝ) (q : E) (m n : Fin 4) :
    pd2 g q m n = fderiv ℝ (fun z => pd g z n) q (Pi.single m 1) := rfl

theorem SmoothDust.fderiv_gauge (h : SmoothDust k ρ v) (q : E) (m : Fin 4) :
    3 * pd2 (dustPhi G ρ) q m 0 + ∑ α, pd2 (comp (dustB G ρ v) α) q m α.succ = 0 := by
  have hz : (fun z => 3 * pd (dustPhi G ρ) z 0 + ∑ α, pd (comp (dustB G ρ v) α) z α.succ) =
      fun _ => 0 := funext h.gauge
  have hΦ := differentiableAt_pd (h.contDiff_dustPhi (G := G)) 0 q
  have hB (α : Fin 3) := differentiableAt_pd (h.contDiff_dustB (G := G) α) α.succ q
  have key := congrArg (fun F => fderiv ℝ F q (Pi.single m 1)) hz
  rw [fderiv_fun_add (hΦ.const_mul 3) (DifferentiableAt.fun_sum fun α _ => hB α),
    fderiv_const_mul hΦ, fderiv_fun_sum fun α _ => hB α] at key
  simpa [pd2_eq_fderiv_pd] using key

/-- **The time derivative of the gauge condition**, `∂_t(3∂_tΦ + ∇ · B) = 0`. -/
theorem SmoothDust.gauge_rate (h : SmoothDust k ρ v) (q : E) :
    3 * sd (dustPhi G ρ) q 0 0 + dtDiv (dustB G ρ v) q = 0 := by
  have h0 := h.fderiv_gauge (G := G) q 0
  simp only [Fin.sum_univ_three] at h0
  simp only [sd, dtDiv]
  simpa using h0

/-- The gradient of the divergence from the gauge, `∂_α ∇ · B = −3 ∂_α ∂_t Φ`. -/
theorem SmoothDust.gradDiv_eq (h : SmoothDust k ρ v) (q : E) (α : Fin 3) :
    gradDiv (dustB G ρ v) q α = -3 * pd2 (dustPhi G ρ) q α.succ 0 := by
  have h0 := h.fderiv_gauge (G := G) q α.succ
  have hs (β : Fin 3) (m n : Fin 4) := pd2_eq_sd
    ((h.contDiff_dustB (G := G) β).contDiffAt (x := q).of_le (by simp)) m n
  simp only [Fin.sum_univ_three] at h0
  rw [gradDiv, ← hs, ← hs, ← hs]
  have e3 : Fin.succ (2 : Fin 3) = (3 : Fin 4) := rfl
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, e3] at h0 ⊢
  linarith

/-- The Newton potential of `∂_α ∂_t ρ̃`. -/
def mixedRate (ρ : ℝ → E3 → ℝ) (α : Fin 3) (p : ℝ × E3) : ℝ :=
  pot newtonKernel (dir (eS α) (dir eT (Function.uncurry ρ))) p

theorem SmoothDust.pd2_dustPhi (h : SmoothDust k ρ v) (q : E) (α : Fin 3) :
    pd2 (dustPhi G ρ) q α.succ 0 = -(4 * π * G) * mixedRate ρ α (spacetimeMap q) := by
  have hk := h.isCompact
  have hK := locallyIntegrable_newtonKernel
  have hρ := h.isSource
  have hΦs := h.isSource_srcPhi (G := G)
  rw [dustPhi_eq, pd2_comp_spacetimeMap h.contDiff_potPhi, spacetimeMap_single_zero,
    spacetimeMap_single_succ, dir_pot hK hk hΦs, dir_pot hK hk (hΦs.dir hk _), srcPhi_eq,
    dir_const_mul _ (hρ.1.differentiable (by simp)),
    dir_const_mul _ ((hρ.dir hk _).1.differentiable (by simp)), pot_const_mul, mixedRate]

theorem SmoothDust.lap_dustB (h : SmoothDust k ρ v) (q : E) (α : Fin 3) :
    lap (comp (dustB G ρ v) α) q = 16 * π * G * (ρ (q 0) (spatialPoint q) *
      v (q 0) (spatialPoint q) α) - 4 * π * G * mixedRate ρ α (spacetimeMap q) := by
  have hk := h.isCompact
  have hK := locallyIntegrable_newtonKernel
  have hN := locallyIntegrable_norm
  have hAs := h.isSource_srcA (G := G) α
  have hWs := h.isSource_srcW (G := G) α
  have hρ := h.isSource
  rw [comp_dustB, lap_comp_spacetimeMap (h.contDiff_potB α)]
  unfold potB
  rw [lapS_add (contDiff_pot hK hAs.1 hk hAs.2) (contDiff_pot hN hWs.1 hk hWs.2)]
  simp only
  rw [lapS_pot hK hk hAs, lapS_pot hN hk hWs, pot_newtonKernel_lapS hAs.1 hk hAs.2,
    pot_norm_lapS hWs.1 hk hWs.2, h.srcW_eq, pot_const_mul, mixedRate, srcA,
    spacetimeMap_apply]
  ring

/-- **The equation of the vector potential**, `ΔB_α − ∂_α ∇ · B − 4 ∂_t ∂_α Φ = 16πG ρ̃ v_α`. -/
theorem SmoothDust.vector_eq (h : SmoothDust k ρ v) (q : E) (α : Fin 3) :
    lap (comp (dustB G ρ v) α) q - gradDiv (dustB G ρ v) q α - 4 * sd (dustPhi G ρ) q 0 α.succ =
      16 * π * G * (ρ (q 0) (spatialPoint q) * v (q 0) (spatialPoint q) α) := by
  have hsd : sd (dustPhi G ρ) q 0 α.succ = pd2 (dustPhi G ρ) q α.succ 0 := by
    rw [← pd2_eq_sd (h.contDiff_dustPhi.contDiffAt.of_le (by simp)),
      pd2_comm (h.contDiff_dustPhi.contDiffAt.of_le (by simp))]
  rw [h.lap_dustB, h.gradDiv_eq, hsd, h.pd2_dustPhi]
  ring

/-- **The equation of the second potential with the Newtonian part**,
`4ΦΔΦ + Δψ = 8πGρ̃(v² + Φ)`. -/
theorem SmoothDust.scalar_eq (h : SmoothDust k ρ v) (q : E) :
    4 * dustPhi G ρ q * lap (dustPhi G ρ) q + lap (dustPsi G ρ v) q =
      8 * π * G * (ρ (q 0) (spatialPoint q) *
        (‖v (q 0) (spatialPoint q)‖ ^ 2 + dustPhi G ρ q)) := by
  rw [h.lap_dustPhi, h.lap_dustPsi]
  ring

end Identities

/-! ### Bounds of the potentials on bounded sets -/

section Bounds

theorem potentialBounds_mono {Φ ψ : E → ℝ} {B : E → S} {W : Set E} {K K' : ℝ}
    (hb : PotentialBounds Φ ψ B W K) (hK : K ≤ K') : PotentialBounds Φ ψ B W K' := by
  refine ⟨hb.nonneg.trans hK, fun q hq => ?_, fun q hq m => ?_, fun q hq m n => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hb.value q hq
    exact ⟨h1.trans hK, h2.trans hK, fun j => (h3 j).trans hK⟩
  · obtain ⟨h1, h2, h3⟩ := hb.first q hq m
    exact ⟨h1.trans hK, h2.trans hK, fun j => (h3 j).trans hK⟩
  · obtain ⟨h1, h2, h3⟩ := hb.second q hq m n
    exact ⟨h1.trans hK, h2.trans hK, fun j => (h3 j).trans hK⟩

/-- The value, the partial derivatives and the second partial derivatives of a `C²` function
are bounded by its `CoordinateC2Bound`. -/
theorem abs_le_of_coordinateC2Bound {g : E → ℝ} (hg : ContDiff ℝ 2 g) {W : Set E} {K : ℝ}
    (hb : CoordinateC2Bound W K g) {q : E} (hq : q ∈ W) :
    |g q| ≤ K ∧ (∀ m, |pd g q m| ≤ K) ∧ ∀ m n, |sd g q m n| ≤ K := by
  have he (m : Fin 4) : ‖(Pi.single m 1 : E)‖ = 1 := by
    rw [Pi.norm_single]
    simp
  refine ⟨by simpa [Real.norm_eq_abs] using hb.value q hq, fun m => ?_, fun m n => ?_⟩
  · have h1 := (fderiv ℝ g q).le_opNorm (Pi.single m 1)
    rw [he, mul_one, Real.norm_eq_abs] at h1
    exact h1.trans (hb.first q hq)
  · have h2 (a b : Fin 4) : |pd2 g q a b| ≤ K := by
      rw [pd2_eq_fderiv_fderiv hg.contDiffAt]
      have h1 := (fderiv ℝ (fderiv ℝ g) q).le_opNorm₂ (Pi.single a 1) (Pi.single b 1)
      rw [he, he, mul_one, mul_one, Real.norm_eq_abs] at h1
      exact h1.trans (hb.second q hq)
    unfold sd
    split_ifs
    · exact h2 _ _
    · exact h2 _ _

/-- **Bounds of `C²` potentials on a bounded set**: `PotentialBounds` holds for some `K`. -/
theorem exists_potentialBounds {Φ ψ : E → ℝ} {B : E → S} (hΦ : ContDiff ℝ 2 Φ)
    (hψ : ContDiff ℝ 2 ψ) (hB : ∀ j, ContDiff ℝ 2 (comp B j)) {W : Set E}
    (hW : Bornology.IsBounded W) : ∃ K, PotentialBounds Φ ψ B W K := by
  have hc := hW.isCompact_closure
  obtain ⟨K₁, hK₁, b₁⟩ := exists_coordinateC2Bound hΦ hc subset_closure
  obtain ⟨K₂, hK₂, b₂⟩ := exists_coordinateC2Bound hψ hc subset_closure
  choose K₃ hK₃ b₃ using fun j => exists_coordinateC2Bound (hB j) hc subset_closure
  have hs : 0 ≤ ∑ j, K₃ j := Finset.sum_nonneg fun j _ => hK₃ j
  have h3 (j : Fin 3) : K₃ j ≤ ∑ j, K₃ j :=
    Finset.single_le_sum (fun j _ => hK₃ j) (Finset.mem_univ j)
  refine ⟨K₁ + K₂ + ∑ j, K₃ j, by positivity, fun q hq => ?_, fun q hq m => ?_,
    fun q hq m n => ?_⟩
  · have a₁ := (abs_le_of_coordinateC2Bound hΦ b₁ hq).1
    have a₂ := (abs_le_of_coordinateC2Bound hψ b₂ hq).1
    have a₃ (j : Fin 3) : |B q j| ≤ K₃ j := (abs_le_of_coordinateC2Bound (hB j) (b₃ j) hq).1
    exact ⟨by linarith, by linarith, fun j => by linarith [a₃ j, h3 j]⟩
  · have a₁ := (abs_le_of_coordinateC2Bound hΦ b₁ hq).2.1 m
    have a₂ := (abs_le_of_coordinateC2Bound hψ b₂ hq).2.1 m
    have a₃ (j : Fin 3) := (abs_le_of_coordinateC2Bound (hB j) (b₃ j) hq).2.1 m
    exact ⟨by linarith, by linarith, fun j => by linarith [a₃ j, h3 j]⟩
  · have a₁ := (abs_le_of_coordinateC2Bound hΦ b₁ hq).2.2 m n
    have a₂ := (abs_le_of_coordinateC2Bound hψ b₂ hq).2.2 m n
    have a₃ (j : Fin 3) := (abs_le_of_coordinateC2Bound (hB j) (b₃ j) hq).2.2 m n
    exact ⟨by linarith, by linarith, fun j => by linarith [a₃ j, h3 j]⟩

end Bounds

/-! ### The Ricci tensor of the metric of smooth dust -/

section Ricci

variable {G : ℝ} {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3} {k : Set E3}

/-- The leading part `4πGρ̃` (time-time) of the source of the Ricci tensor of dust. -/
def dustLeading (G : ℝ) (ρ : ℝ → E3 → ℝ) (q : E) (j l : Fin 4) : ℝ :=
  if j = 0 ∧ l = 0 then 4 * π * G * ρ (q 0) (spatialPoint q) else 0

/-- The part of order `c⁻²` of the source of the Ricci tensor of dust: `8πGρ̃(v² + Φ)`
(time-time), `−8πGρ̃ v_α` (time-space) and `4πGρ̃ δ_αβ` (space-space). -/
def dustFirst (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (q : E) (j l : Fin 4) : ℝ :=
  Fin.cases (Fin.cases (8 * π * G * (ρ (q 0) (spatialPoint q) *
        (‖v (q 0) (spatialPoint q)‖ ^ 2 + dustPhi G ρ q)))
      (fun β => -(8 * π * G) * (ρ (q 0) (spatialPoint q) * v (q 0) (spatialPoint q) β)) l)
    (fun α => Fin.cases (-(8 * π * G) * (ρ (q 0) (spatialPoint q) * v (q 0) (spatialPoint q) α))
      (fun β => if α = β then 4 * π * G * ρ (q 0) (spatialPoint q) else 0) l) j

/-- **The source of the Ricci tensor of dust to the order `c⁻²`** in the coordinates `(t, x)`:
`S_tt = 4πGρ̃(1 + 2(v² + Φ)/c²)`, `S_tα = S_αt = −8πGρ̃ v_α/c²`, `S_αβ = 4πGρ̃ δ_αβ/c²`. -/
def dustRicci (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (c : ℝ) (q : E) (j l : Fin 4) : ℝ :=
  dustLeading G ρ q j l + epsilon c * dustFirst G ρ v q j l

theorem SmoothDust.ricciLeading_eq (h : SmoothDust k ρ v) (q : E) (j l : Fin 4) :
    ricciLeading (dustPhi G ρ) q j l = dustLeading G ρ q j l := by
  simp only [ricciLeading, dustLeading, h.lap_dustPhi]

theorem SmoothDust.ricciFirst_eq (h : SmoothDust k ρ v) (q : E) (j l : Fin 4) :
    ricciFirst (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) q j l = dustFirst G ρ v q j l := by
  refine Fin.cases ?_ (fun α => ?_) j <;> refine Fin.cases ?_ (fun β => ?_) l
  · simp only [ricciFirst, dustFirst, Fin.cases_zero]
    linear_combination h.scalar_eq (G := G) q + h.gauge_rate (G := G) q
  · simp only [ricciFirst, dustFirst, Fin.cases_zero, Fin.cases_succ]
    rw [h.vector_eq]
    ring
  · simp only [ricciFirst, dustFirst, Fin.cases_zero, Fin.cases_succ]
    rw [h.vector_eq]
    ring
  · simp only [ricciFirst, dustFirst, Fin.cases_succ, h.lap_dustPhi]

theorem SmoothDust.exists_potentialBounds (h : SmoothDust k ρ v) {W : Set E}
    (hW : Bornology.IsBounded W) :
    ∃ K, PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K :=
  PostNewtonianDust.exists_potentialBounds (h.contDiff_dustPhi.of_le (by simp))
    (h.contDiff_dustPsi.of_le (by simp)) (fun j => (h.contDiff_dustB j).of_le (by simp)) hW

/-- **The Ricci tensor of the post-Newtonian metric of smooth dust to the order `c⁻²`**: on a
bounded set of `(t, x)`, `|R_jk − S_jk| ≤ C/c⁴` for `c ≥ c₁`, with the source `dustRicci`
`S_tt = 4πGρ̃(1 + 2(v² + Φ)/c²)`, `S_tα = −8πGρ̃ v_α/c²`, `S_αβ = 4πGρ̃ δ_αβ/c²`. -/
theorem SmoothDust.abs_ricciOf_dustMetric_sub_le (h : SmoothDust k ρ v) {W : Set E}
    (hW : Bornology.IsBounded W) :
    ∃ c₁ C, ∀ c, c₁ ≤ c → ∀ q ∈ W, ∀ j l : Fin 4,
      |ricciOf (d := 3) (dustMetric G ρ v c) q j l - dustRicci G ρ v c q j l| ≤ C / c ^ 4 := by
  obtain ⟨R, hR⟩ := hW.subset_ball (0 : E)
  obtain ⟨K, hb⟩ :=
    h.exists_potentialBounds (G := G) (Metric.isBounded_ball (x := (0 : E)) (r := R))
  obtain ⟨C, -, hest⟩ := abs_ricciOf_pnCoefficient_sub_le Metric.isOpen_ball
    (fun z _ => h.contDiff_dustPhi.contDiffAt.of_le (by simp))
    (fun z _ => h.contDiff_dustPsi.contDiffAt.of_le (by simp))
    (fun z _ j => (h.contDiff_dustB j).contDiffAt.of_le (by simp)) hb
  refine ⟨threshold K, C, fun c hc q hq j l => ?_⟩
  have h1 := hest c hc q (hR hq) j l
  rw [h.ricciLeading_eq, h.ricciFirst_eq] at h1
  exact h1

end Ricci

/-! ### The stress tensor of dust -/

section Matter

open Matrix

/-- The direction `(1, v)` of a world line in the coordinates `(t, x)`. -/
def flowVector (w : S) : Fin 4 → ℝ := Fin.cons 1 w

/-- The four-velocity `u = γ(1, v)` normalized by `g(u, u) = −c²`: `γ⁻² = −g((1, v), (1, v))/c²`
(`fourVelocity_norm`). -/
def fourVelocity (g : Matrix (Fin 4) (Fin 4) ℝ) (c : ℝ) (w : S) : Fin 4 → ℝ :=
  (√(-(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2))⁻¹ • flowVector w

/-- The stress tensor of dust of proper density `ρ̃` with lowered indices, `T_ab = ρ̃ u_a u_b`,
`u_a = g_ab u^b`. -/
def dustStress (g : Matrix (Fin 4) (Fin 4) ℝ) (c ρ : ℝ) (w : S) (a b : Fin 4) : ℝ :=
  ρ * (g *ᵥ fourVelocity g c w) a * (g *ᵥ fourVelocity g c w) b

/-- **The trace-reversed source** `κ(T_ab − ½ g_ab g^{cd} T_cd)` with `κ = 8πG/c⁴`: the Einstein
equations `G_ab = κ T_ab` are `R_ab = κ(T_ab − ½ g_ab T)`. -/
def traceReversedSource (G c : ℝ) (g : Matrix (Fin 4) (Fin 4) ℝ) (T : Fin 4 → Fin 4 → ℝ)
    (a b : Fin 4) : ℝ :=
  8 * π * G / c ^ 4 * (T a b - 1 / 2 * g a b * ∑ l, ∑ m, g⁻¹ l m * T l m)

/-- The velocity `v(t, x)` of the dust at `q = (t, x)`. -/
def dustVelocity (v : ℝ → E3 → E3) (q : E) : S := fun α => v (q 0) (spatialPoint q) α

/-- **The source of the Einstein equations of the dust**: `κ(T − ½ g tr T)` for the stress
`T = ρ̃ u ⊗ u` of the proper density `ρ̃` and the four-velocity `u = γ(1, v)` in the metric
`dustMetric`. -/
def dustSource (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (c : ℝ) (q : E) (a b : Fin 4) : ℝ :=
  traceReversedSource G c (dustMetric G ρ v c q)
    (dustStress (dustMetric G ρ v c q) c (ρ (q 0) (spatialPoint q)) (dustVelocity v q)) a b

variable {g : Matrix (Fin 4) (Fin 4) ℝ} {G c ρ₀ : ℝ} {w : S}

theorem ne_zero_of_normSq_pos (hN : 0 < -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2) : c ≠ 0 := by
  rintro rfl
  simp at hN

/-- **The normalization of the four-velocity**, `g(u, u) = −c²`. -/
theorem fourVelocity_norm (hN : 0 < -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2) :
    fourVelocity g c w ⬝ᵥ g *ᵥ fourVelocity g c w = -c ^ 2 := by
  have hc := ne_zero_of_normSq_pos hN
  set N := -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2 with hNd
  have hγ : ((√N)⁻¹) ^ 2 = N⁻¹ := by rw [inv_pow, Real.sq_sqrt hN.le]
  have he : flowVector w ⬝ᵥ g *ᵥ flowVector w = -(c ^ 2 * N) := by
    rw [hNd]
    field_simp
  have hu : fourVelocity g c w = (√N)⁻¹ • flowVector w := rfl
  rw [hu, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, ← sq, hγ, he]
  field_simp

theorem dustStress_eq (hN : 0 < -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2) (a b : Fin 4) :
    dustStress g c ρ₀ w a b = ρ₀ * (-(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2)⁻¹ *
      (g *ᵥ flowVector w) a * (g *ᵥ flowVector w) b := by
  set N := -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2 with hNd
  have hγ : ((√N)⁻¹) ^ 2 = N⁻¹ := by rw [inv_pow, Real.sq_sqrt hN.le]
  simp only [dustStress, fourVelocity, ← hNd, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  rw [← hγ]
  ring

/-- **The trace of the stress of dust**, `g^{ab} T_ab = −ρ̃c²`. -/
theorem trace_dustStress (hg : g.det ≠ 0)
    (hN : 0 < -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2) :
    ∑ l, ∑ m, g⁻¹ l m * dustStress g c ρ₀ w l m = -(ρ₀ * c ^ 2) := by
  have hc := ne_zero_of_normSq_pos hN
  set N := -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2 with hNd
  set Y := g *ᵥ flowVector w with hY
  simp only [dustStress_eq hN, ← hNd, ← hY]
  have h1 : ∑ l, ∑ m, g⁻¹ l m * (ρ₀ * N⁻¹ * Y l * Y m) = ρ₀ * N⁻¹ * (Y ⬝ᵥ (g⁻¹ *ᵥ Y)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  have h2 : g⁻¹ *ᵥ Y = flowVector w := by
    rw [hY, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg),
      Matrix.one_mulVec]
  have h3 : Y ⬝ᵥ flowVector w = -(c ^ 2 * N) := by
    rw [hY, dotProduct_comm, hNd]
    field_simp
    ring
  rw [h1, h2, h3]
  field_simp

/-- The trace-reversed source of dust: `κρ̃(γ²(g e)_a (g e)_b + (c²/2) g_ab)`, `e = (1, v)`. -/
theorem traceReversedSource_dustStress (hg : g.det ≠ 0)
    (hN : 0 < -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2) (a b : Fin 4) :
    traceReversedSource G c g (dustStress g c ρ₀ w) a b = 8 * π * G / c ^ 4 * (ρ₀ *
      ((-(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2)⁻¹ * (g *ᵥ flowVector w) a *
        (g *ᵥ flowVector w) b + c ^ 2 / 2 * g a b)) := by
  rw [traceReversedSource, trace_dustStress hg hN, dustStress_eq hN]
  ring

end Matter

/-! ### The expansion of the source of dust -/

section MatterExpansion

open Matrix

/-- Decompose an expansion of a polynomial expression into expansions of its atoms. -/
local macro "exp_on" : tactic => `(tactic| repeat' first
  | intro _
  | with_reducible apply_assumption
  | with_reducible apply IsExp.const
  | with_reducible apply IsExp.add
  | with_reducible apply IsExp.sub
  | with_reducible apply IsExp.mul
  | with_reducible apply IsExp.neg
  | with_reducible apply IsExp.pow_two
  | with_reducible apply IsExp.pow_three
  | with_reducible apply IsExp.div_const
  | with_reducible apply IsExp.sum)

theorem one_half_le_of_bounds {e n₁ n₂ M : ℝ} (he : 0 ≤ e ∧ e ≤ 1) (h₁ : |n₁| ≤ M)
    (h₂ : |n₂| ≤ M) (hM : e * M ≤ 1 / 4) : 1 / 2 ≤ 1 + e * n₁ + e ^ 2 * n₂ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans h₁
  have he2 : e ^ 2 ≤ e := by nlinarith
  have a1 : |e * n₁| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_nonneg he.1]
    nlinarith [mul_le_mul_of_nonneg_left h₁ he.1]
  have a2 : |e ^ 2 * n₂| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg e)]
    nlinarith [mul_le_mul_of_nonneg_left h₂ (sq_nonneg e), abs_nonneg n₂,
      mul_le_mul_of_nonneg_right he2 hM0]
  linarith [neg_abs_le (e * n₁), neg_abs_le (e ^ 2 * n₂)]

/-- **The expansion of an inverse** `(1 + εn₁ + ε²n₂)⁻¹ = 1 − εn₁ + O(ε²)` for bounded `n₁`,
`n₂` and `εM ≤ 1/4`. -/
theorem isExp_inv_one_add {α : Type} {T : Set α} {ε n₁ n₂ : α → ℝ} {M : ℝ}
    (hε : ∀ p ∈ T, 0 ≤ ε p ∧ ε p ≤ 1) (h₁ : ∀ p ∈ T, |n₁ p| ≤ M) (h₂ : ∀ p ∈ T, |n₂ p| ≤ M)
    (hM : ∀ p ∈ T, ε p * M ≤ 1 / 4) :
    IsExp T ε (fun p => (1 + ε p * n₁ p + ε p ^ 2 * n₂ p)⁻¹) (fun _ => 1) (fun p => -n₁ p) := by
  have hN (p : α) (hp : p ∈ T) := one_half_le_of_bounds (hε p hp) (h₁ p hp) (h₂ p hp) (hM p hp)
  have hinv : BoundedOn T (fun p => (1 + ε p * n₁ p + ε p ^ 2 * n₂ p)⁻¹) :=
    BoundedOn.of_le' (C := 2) fun p hp => by
      have := hN p hp
      rw [abs_of_pos (inv_pos.mpr (by linarith)), inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
  have hn₁ : BoundedOn T n₁ := BoundedOn.of_le' h₁
  have hn₂ : BoundedOn T n₂ := BoundedOn.of_le' h₂
  have hε' : BoundedOn T ε := BoundedOn.of_le' (C := 1) fun p hp => by
    rw [abs_of_nonneg (hε p hp).1]
    exact (hε p hp).2
  refine IsExp.of_eq (f₂ := fun p => (n₁ p * n₁ p - n₂ p + ε p * n₁ p * n₂ p) *
    (1 + ε p * n₁ p + ε p ^ 2 * n₂ p)⁻¹) hε (BoundedOn.const' 1) hn₁.neg' ?_ fun p hp => ?_
  · obtain ⟨C, hC, hb⟩ := (((hn₁.mul' hn₁).add' hn₂.neg').add' ((hε'.mul' hn₁).mul' hn₂)).mul' hinv
    exact ⟨C, hC, fun p hp => by
      have := hb p hp
      simp only at this ⊢
      rwa [sub_eq_add_neg]⟩
  · have hD : 1 + ε p * n₁ p + ε p ^ 2 * n₂ p ≠ 0 := by linarith [hN p hp]
    field_simp
    ring

theorem pnCoefficient_zero_zero (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) :
    pnCoefficient Φ ψ B c q 0 0 = -c ^ 2 - 2 * Φ q - 2 * epsilon c * (Φ q ^ 2 + ψ q) := rfl

theorem pnCoefficient_zero_succ (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (α : Fin 3) :
    pnCoefficient Φ ψ B c q 0 α.succ = epsilon c * B q α := by
  fin_cases α <;> rfl

theorem pnCoefficient_succ_zero (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (α : Fin 3) :
    pnCoefficient Φ ψ B c q α.succ 0 = epsilon c * B q α := by
  fin_cases α <;> rfl

theorem pnCoefficient_succ_succ (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (α β : Fin 3) :
    pnCoefficient Φ ψ B c q α.succ β.succ = if α = β then spatialFactor Φ c q else 0 := by
  fin_cases α <;> fin_cases β <;> rfl

theorem flowVector_dotProduct (w : S) (Y : Fin 4 → ℝ) :
    flowVector w ⬝ᵥ Y = Y 0 + ∑ β, w β * Y β.succ := by
  rw [dotProduct, Fin.sum_univ_succ]
  simp [flowVector]

theorem pnCoefficient_mulVec_zero (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (w : S) :
    (pnCoefficient Φ ψ B c q *ᵥ flowVector w) 0 =
      -c ^ 2 - 2 * Φ q - 2 * epsilon c * (Φ q ^ 2 + ψ q) + epsilon c * ∑ β, B q β * w β := by
  rw [mulVec, dotProduct, Fin.sum_univ_succ]
  simp only [flowVector, Fin.cons_zero, Fin.cons_succ, pnCoefficient_zero_zero,
    pnCoefficient_zero_succ, Finset.mul_sum]
  ring_nf

theorem pnCoefficient_mulVec_succ (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (w : S)
    (α : Fin 3) : (pnCoefficient Φ ψ B c q *ᵥ flowVector w) α.succ =
      epsilon c * B q α + spatialFactor Φ c q * w α := by
  rw [mulVec, dotProduct, Fin.sum_univ_succ]
  simp [flowVector, pnCoefficient_succ_zero, pnCoefficient_succ_succ]

variable {G : ℝ} {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3} {W : Set E} {K c : ℝ}

/-- The factor `γ⁻² = −g((1, v), (1, v))/c²` of the four-velocity of the dust. -/
def normFactor (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (c : ℝ) (q : E) : ℝ :=
  -(flowVector (dustVelocity v q) ⬝ᵥ dustMetric G ρ v c q *ᵥ flowVector (dustVelocity v q)) /
    c ^ 2

theorem normFactor_eq (hc : c ≠ 0) (q : E) :
    normFactor G ρ v c q = 1 + epsilon c * (2 * dustPhi G ρ q - ∑ β, dustVelocity v q β ^ 2) +
      epsilon c ^ 2 * (2 * (dustPhi G ρ q ^ 2 + dustPsi G ρ v q) -
        2 * ∑ β, dustB G ρ v q β * dustVelocity v q β +
          2 * dustPhi G ρ q * ∑ β, dustVelocity v q β ^ 2) := by
  rw [normFactor, dustMetric, flowVector_dotProduct, pnCoefficient_mulVec_zero]
  simp only [pnCoefficient_mulVec_succ, spatialFactor]
  have e : ∑ β, dustVelocity v q β * (epsilon c * dustB G ρ v q β +
      (1 - 2 * epsilon c * dustPhi G ρ q) * dustVelocity v q β) =
      epsilon c * ∑ β, dustB G ρ v q β * dustVelocity v q β +
        (1 - 2 * epsilon c * dustPhi G ρ q) * ∑ β, dustVelocity v q β ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  rw [e]
  simp only [epsilon]
  field_simp
  ring

/-- The bound `M = 2K + 3K² + 2(K² + K) + 6K² + 6K³` of the coefficients of `γ⁻²`. -/
def normBound (K : ℝ) : ℝ := 2 * K + 3 * K ^ 2 + (2 * (K ^ 2 + K) + 6 * K ^ 2 + 6 * K ^ 3)

/-- The threshold `c₂ = c₁ + 4M + 1` of the expansion of the source of dust. -/
def dustThreshold (K : ℝ) : ℝ := threshold K + 4 * normBound K + 1

theorem dustThreshold_spec (hK : 0 ≤ K) (hc : dustThreshold K ≤ c) :
    threshold K ≤ c ∧ 0 ≤ epsilon c ∧ epsilon c ≤ 1 ∧ epsilon c * normBound K ≤ 1 / 4 := by
  have hM : 0 ≤ normBound K := by unfold normBound; positivity
  have ht : 9 ≤ threshold K := by unfold threshold; nlinarith
  have h1 : threshold K ≤ c := by unfold dustThreshold at hc; linarith
  have hc1 : 1 ≤ c := by linarith
  refine ⟨h1, epsilon_nonneg c, epsilon_le_one hc1, ?_⟩
  have hc2 : 4 * normBound K + 1 ≤ c ^ 2 := by unfold dustThreshold at hc; nlinarith
  rw [epsilon, inv_mul_le_iff₀ (by positivity)]
  nlinarith

theorem abs_sum_sq_le {w : Fin 3 → ℝ} (hw : ∀ β, |w β| ≤ K) : |∑ β, w β ^ 2| ≤ 3 * K ^ 2 := by
  have h (β : Fin 3) : w β ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hw β) 2
  rw [abs_of_nonneg (Finset.sum_nonneg fun β _ => sq_nonneg _), Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem abs_sum_mul_le {b w : Fin 3 → ℝ} (hb : ∀ β, |b β| ≤ K) (hw : ∀ β, |w β| ≤ K) :
    |∑ β, b β * w β| ≤ 3 * K ^ 2 := by
  have h (β : Fin 3) : |b β * w β| ≤ K ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul (hb β) (hw β) (abs_nonneg _) ((abs_nonneg _).trans (hb β))
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

/-- The source of dust as a rational function of `γ⁻²` and the coefficients. -/
theorem dustSource_eq (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    {q : E} (hq : q ∈ W) (hc : threshold K ≤ c) (hN : 0 < normFactor G ρ v c q) (a b : Fin 4) :
    dustSource G ρ v c q a b = 8 * π * G / c ^ 4 * (ρ (q 0) (spatialPoint q) *
      ((normFactor G ρ v c q)⁻¹ * (dustMetric G ρ v c q *ᵥ flowVector (dustVelocity v q)) a *
        (dustMetric G ρ v c q *ᵥ flowVector (dustVelocity v q)) b +
          c ^ 2 / 2 * dustMetric G ρ v c q a b)) := by
  have hc0 : c ≠ 0 := by unfold threshold at hc; nlinarith [hb.nonneg]
  have hdet : (dustMetric G ρ v c q).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (pnCoefficient_mul_inverse hc0
      (by linarith [spatialFactor_ge hb hq hc]) (by linarith [pnDenom_ge hb hq hc]))
  exact traceReversedSource_dustStress hdet hN a b

/-- The atoms of the expansion of the source of dust on `pnSet W (dustThreshold K)`: `ε`, the
potentials, the density, the velocity, `B · v`, and the factor `γ² = (γ⁻²)⁻¹ = 1 + ε(v² − 2Φ) +
O(ε²)`. -/
theorem dust_atoms (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) :
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1) (fun p => epsilon p.1)
      (fun _ => 0) (fun _ => 1) ∧
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1) (fun p => dustPhi G ρ p.2)
      (fun p => dustPhi G ρ p.2) (fun _ => 0) ∧
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1) (fun p => dustPsi G ρ v p.2)
      (fun p => dustPsi G ρ v p.2) (fun _ => 0) ∧
    (∀ β, IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1) (fun p => dustB G ρ v p.2 β)
      (fun p => dustB G ρ v p.2 β) (fun _ => 0)) ∧
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => ρ (p.2 0) (spatialPoint p.2)) (fun p => ρ (p.2 0) (spatialPoint p.2))
      (fun _ => 0) ∧
    (∀ β, IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => dustVelocity v p.2 β) (fun p => dustVelocity v p.2 β) (fun _ => 0)) ∧
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => ∑ β, dustB G ρ v p.2 β * dustVelocity v p.2 β)
      (fun p => ∑ β, dustB G ρ v p.2 β * dustVelocity v p.2 β) (fun _ => 0) ∧
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => (normFactor G ρ v p.1 p.2)⁻¹) (fun _ => 1)
      (fun p => -(2 * dustPhi G ρ p.2 - ∑ β, dustVelocity v p.2 β ^ 2)) ∧
    ∀ p ∈ pnSet W (dustThreshold K), 0 < normFactor G ρ v p.1 p.2 := by
  set T := pnSet W (dustThreshold K)
  have hK := hb.nonneg
  have hT (p : ℝ × E) (hp : p ∈ T) := dustThreshold_spec hK hp.1
  have hε : ∀ p ∈ T, 0 ≤ epsilon p.1 ∧ epsilon p.1 ≤ 1 :=
    fun p hp => ⟨(hT p hp).2.1, (hT p hp).2.2.1⟩
  have hbd {g : E → ℝ} (hg : ∀ q ∈ W, |g q| ≤ K) : BoundedOn T (fun p => g p.2) :=
    BoundedOn.of_le' fun p hp => hg p.2 hp.2
  have hbw (q : E) (hq : q ∈ W) : |∑ β, dustB G ρ v q β * dustVelocity v q β| ≤ 3 * K ^ 2 :=
    abs_sum_mul_le (fun β => (hb.value q hq).2.2 β) (hw q hq)
  have hww (q : E) (hq : q ∈ W) : |∑ β, dustVelocity v q β ^ 2| ≤ 3 * K ^ 2 :=
    abs_sum_sq_le (hw q hq)
  have hn₁ (p : ℝ × E) (hp : p ∈ T) :
      |2 * dustPhi G ρ p.2 - ∑ β, dustVelocity v p.2 β ^ 2| ≤ normBound K := by
    obtain ⟨a1, a2⟩ := abs_le.mp (hb.value p.2 hp.2).1
    obtain ⟨b1, b2⟩ := abs_le.mp (hww p.2 hp.2)
    have hM : 0 ≤ 2 * (K ^ 2 + K) + 6 * K ^ 2 + 6 * K ^ 3 := by positivity
    rw [abs_le]
    unfold normBound
    constructor <;> linarith
  have hn₂ (p : ℝ × E) (hp : p ∈ T) :
      |2 * (dustPhi G ρ p.2 ^ 2 + dustPsi G ρ v p.2) -
        2 * ∑ β, dustB G ρ v p.2 β * dustVelocity v p.2 β +
          2 * dustPhi G ρ p.2 * ∑ β, dustVelocity v p.2 β ^ 2| ≤ normBound K := by
    have h1 := (hb.value p.2 hp.2).1
    obtain ⟨a1, a2⟩ := abs_le.mp (hb.value p.2 hp.2).2.1
    obtain ⟨b1, b2⟩ := abs_le.mp (hbw p.2 hp.2)
    have hΦ2 : dustPhi G ρ p.2 ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hΦw : |dustPhi G ρ p.2 * ∑ β, dustVelocity v p.2 β ^ 2| ≤ K * (3 * K ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul h1 (hww p.2 hp.2) (abs_nonneg _) hK
    obtain ⟨c1, c2⟩ := abs_le.mp hΦw
    have hs := sq_nonneg (dustPhi G ρ p.2)
    have hK2 := sq_nonneg K
    rw [abs_le]
    unfold normBound
    constructor <;> nlinarith
  have hN (p : ℝ × E) (hp : p ∈ T) : normFactor G ρ v p.1 p.2 =
      1 + epsilon p.1 * (2 * dustPhi G ρ p.2 - ∑ β, dustVelocity v p.2 β ^ 2) +
        epsilon p.1 ^ 2 * (2 * (dustPhi G ρ p.2 ^ 2 + dustPsi G ρ v p.2) -
          2 * ∑ β, dustB G ρ v p.2 β * dustVelocity v p.2 β +
            2 * dustPhi G ρ p.2 * ∑ β, dustVelocity v p.2 β ^ 2) := by
    have h9 : 9 ≤ p.1 := by have := (hT p hp).1; unfold threshold at this; nlinarith
    exact normFactor_eq (by linarith) p.2
  refine ⟨IsExp.eps_self hε, IsExp.atom hε (hbd fun q hq => (hb.value q hq).1),
    IsExp.atom hε (hbd fun q hq => (hb.value q hq).2.1),
    fun β => IsExp.atom hε (hbd (g := fun q => dustB G ρ v q β) fun q hq =>
      (hb.value q hq).2.2 β),
    IsExp.atom hε (hbd (g := fun q => ρ (q 0) (spatialPoint q)) hρ),
    fun β => IsExp.atom hε (hbd (g := fun q => dustVelocity v q β) fun q hq => hw q hq β),
    IsExp.atom hε (BoundedOn.of_le' fun p hp => hbw p.2 hp.2), ?_, fun p hp => ?_⟩
  · exact (isExp_inv_one_add hε hn₁ hn₂ fun p hp => (hT p hp).2.2.2).congr_left fun p hp => by
      rw [hN p hp]
  · rw [hN p hp]
    linarith [one_half_le_of_bounds (hε p hp) (hn₁ p hp) (hn₂ p hp) (hT p hp).2.2.2]

theorem dustSource_eq_of_mem
    (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) {p : ℝ × E}
    (hp : p ∈ pnSet W (dustThreshold K)) (a b : Fin 4) :
    p.1 ≠ 0 ∧ dustSource G ρ v p.1 p.2 a b = 8 * π * G / p.1 ^ 4 *
      (ρ (p.2 0) (spatialPoint p.2) * ((normFactor G ρ v p.1 p.2)⁻¹ *
        (dustMetric G ρ v p.1 p.2 *ᵥ flowVector (dustVelocity v p.2)) a *
        (dustMetric G ρ v p.1 p.2 *ᵥ flowVector (dustVelocity v p.2)) b +
          p.1 ^ 2 / 2 * dustMetric G ρ v p.1 p.2 a b)) := by
  have hT := dustThreshold_spec hb.nonneg hp.1
  have hc0 : p.1 ≠ 0 := by
    have := hT.1
    unfold threshold at this
    nlinarith [hb.nonneg]
  exact ⟨hc0, dustSource_eq hb hp.2 hT.1 ((dust_atoms hb hρ hw).2.2.2.2.2.2.2.2 p hp) a b⟩

theorem exp_dustSource_tt
    (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) :
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => dustSource G ρ v p.1 p.2 0 0) (fun p => dustLeading G ρ p.2 0 0)
      (fun p => dustFirst G ρ v p.2 0 0) := by
  obtain ⟨aε, aΦ, aψ, -, aρ, -, abw, aN, -⟩ := dust_atoms hb hρ hw
  have hε := aε.eps
  refine IsExp.congr_left (f := fun p => 8 * π * G * (ρ (p.2 0) (spatialPoint p.2) *
    ((normFactor G ρ v p.1 p.2)⁻¹ * (1 + 2 * epsilon p.1 * dustPhi G ρ p.2 +
      2 * epsilon p.1 ^ 2 * (dustPhi G ρ p.2 ^ 2 + dustPsi G ρ v p.2) -
        epsilon p.1 ^ 2 * ∑ β, dustB G ρ v p.2 β * dustVelocity v p.2 β) ^ 2 -
      (1 + 2 * epsilon p.1 * dustPhi G ρ p.2 +
        2 * epsilon p.1 ^ 2 * (dustPhi G ρ p.2 ^ 2 + dustPsi G ρ v p.2)) / 2))) ?_
    fun p hp => ?_
  · apply IsExp.congr
    focus
      exp_on
    all_goals intro p _
    all_goals simp only [dustLeading, dustFirst, Fin.cases_zero, and_self, ↓reduceIte,
      EuclideanSpace.real_norm_sq_eq, dustVelocity]
    all_goals ring
  · obtain ⟨h0, hs⟩ := dustSource_eq_of_mem hb hρ hw hp 0 0
    rw [hs, dustMetric, pnCoefficient_mulVec_zero, pnCoefficient_zero_zero]
    set Ni := (normFactor G ρ v p.1 p.2)⁻¹
    simp only [epsilon]
    field_simp
    ring

theorem exp_dustSource_ts
    (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) (β : Fin 3) :
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => dustSource G ρ v p.1 p.2 0 β.succ) (fun p => dustLeading G ρ p.2 0 β.succ)
      (fun p => dustFirst G ρ v p.2 0 β.succ) := by
  obtain ⟨aε, aΦ, aψ, aB, aρ, aw, abw, aN, -⟩ := dust_atoms hb hρ hw
  have hε := aε.eps
  have aBβ := aB β
  have awβ := aw β
  refine IsExp.congr_left (f := fun p => 8 * π * G * (ρ (p.2 0) (spatialPoint p.2) *
    (-(epsilon p.1 * ((normFactor G ρ v p.1 p.2)⁻¹ * (1 + 2 * epsilon p.1 * dustPhi G ρ p.2 +
      2 * epsilon p.1 ^ 2 * (dustPhi G ρ p.2 ^ 2 + dustPsi G ρ v p.2) -
        epsilon p.1 ^ 2 * ∑ β, dustB G ρ v p.2 β * dustVelocity v p.2 β) *
      (epsilon p.1 * dustB G ρ v p.2 β +
        (1 - 2 * epsilon p.1 * dustPhi G ρ p.2) * dustVelocity v p.2 β))) +
      epsilon p.1 ^ 2 * dustB G ρ v p.2 β / 2))) ?_ fun p hp => ?_
  · apply IsExp.congr
    focus
      exp_on
    all_goals intro p _
    all_goals simp [dustLeading, dustFirst, dustVelocity, Fin.succ_ne_zero]
  · obtain ⟨h0, hs⟩ := dustSource_eq_of_mem hb hρ hw hp 0 β.succ
    rw [hs, dustMetric, pnCoefficient_mulVec_zero, pnCoefficient_mulVec_succ,
      pnCoefficient_zero_succ, spatialFactor]
    set Ni := (normFactor G ρ v p.1 p.2)⁻¹
    simp only [epsilon]
    field_simp
    ring

theorem exp_dustSource_st
    (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) (α : Fin 3) :
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => dustSource G ρ v p.1 p.2 α.succ 0) (fun p => dustLeading G ρ p.2 α.succ 0)
      (fun p => dustFirst G ρ v p.2 α.succ 0) := by
  obtain ⟨aε, aΦ, aψ, aB, aρ, aw, abw, aN, -⟩ := dust_atoms hb hρ hw
  have hε := aε.eps
  have aBα := aB α
  have awα := aw α
  refine IsExp.congr_left (f := fun p => 8 * π * G * (ρ (p.2 0) (spatialPoint p.2) *
    (-(epsilon p.1 * ((normFactor G ρ v p.1 p.2)⁻¹ *
      (epsilon p.1 * dustB G ρ v p.2 α +
        (1 - 2 * epsilon p.1 * dustPhi G ρ p.2) * dustVelocity v p.2 α) *
      (1 + 2 * epsilon p.1 * dustPhi G ρ p.2 +
        2 * epsilon p.1 ^ 2 * (dustPhi G ρ p.2 ^ 2 + dustPsi G ρ v p.2) -
          epsilon p.1 ^ 2 * ∑ β, dustB G ρ v p.2 β * dustVelocity v p.2 β))) +
      epsilon p.1 ^ 2 * dustB G ρ v p.2 α / 2))) ?_ fun p hp => ?_
  · apply IsExp.congr
    focus
      exp_on
    all_goals intro p _
    all_goals simp [dustLeading, dustFirst, dustVelocity, Fin.succ_ne_zero]
  · obtain ⟨h0, hs⟩ := dustSource_eq_of_mem hb hρ hw hp α.succ 0
    rw [hs, dustMetric, pnCoefficient_mulVec_zero, pnCoefficient_mulVec_succ,
      pnCoefficient_succ_zero, spatialFactor]
    set Ni := (normFactor G ρ v p.1 p.2)⁻¹
    simp only [epsilon]
    field_simp
    ring

theorem exp_dustSource_ss
    (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) (α β : Fin 3) :
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => dustSource G ρ v p.1 p.2 α.succ β.succ)
      (fun p => dustLeading G ρ p.2 α.succ β.succ)
      (fun p => dustFirst G ρ v p.2 α.succ β.succ) := by
  obtain ⟨aε, aΦ, aψ, aB, aρ, aw, abw, aN, -⟩ := dust_atoms hb hρ hw
  have hε := aε.eps
  have aBα := aB α
  have awα := aw α
  have aBβ := aB β
  have awβ := aw β
  refine IsExp.congr_left (f := fun p => 8 * π * G * (ρ (p.2 0) (spatialPoint p.2) *
    (epsilon p.1 ^ 2 * ((normFactor G ρ v p.1 p.2)⁻¹ *
      (epsilon p.1 * dustB G ρ v p.2 α +
        (1 - 2 * epsilon p.1 * dustPhi G ρ p.2) * dustVelocity v p.2 α) *
      (epsilon p.1 * dustB G ρ v p.2 β +
        (1 - 2 * epsilon p.1 * dustPhi G ρ p.2) * dustVelocity v p.2 β)) +
      epsilon p.1 * ((if α = β then 1 else 0) * (1 - 2 * epsilon p.1 * dustPhi G ρ p.2)) /
        2))) ?_ fun p hp => ?_
  · apply IsExp.congr
    focus
      exp_on
    all_goals intro p _
    all_goals simp only [dustLeading, dustFirst, Fin.cases_succ, Fin.succ_ne_zero,
      false_and, ↓reduceIte]
    all_goals split_ifs <;> ring
  · obtain ⟨h0, hs⟩ := dustSource_eq_of_mem hb hρ hw hp α.succ β.succ
    rw [hs, dustMetric, pnCoefficient_mulVec_succ, pnCoefficient_mulVec_succ,
      pnCoefficient_succ_succ, spatialFactor]
    set Ni := (normFactor G ρ v p.1 p.2)⁻¹
    simp only [epsilon]
    split_ifs
    · field_simp
    · field_simp
      ring

/-- **The expansion of the source of dust**: on `W` with the bounds `K` of the potentials, the
density and the velocity, every component of `κ(T − ½ g tr T)` is `S⁽⁰⁾ + c⁻²S⁽¹⁾ + O(c⁻⁴)`
uniformly for `c ≥ c₂ = dustThreshold K`, with `S⁽⁰⁾ = dustLeading` and `S⁽¹⁾ = dustFirst`. -/
theorem exp_dustSource (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) (j l : Fin 4) :
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => dustSource G ρ v p.1 p.2 j l) (fun p => dustLeading G ρ p.2 j l)
      (fun p => dustFirst G ρ v p.2 j l) := by
  refine Fin.cases ?_ (fun α => ?_) j <;> refine Fin.cases ?_ (fun β => ?_) l
  · exact exp_dustSource_tt hb hρ hw
  · exact exp_dustSource_ts hb hρ hw β
  · exact exp_dustSource_st hb hρ hw α
  · exact exp_dustSource_ss hb hρ hw α β

end MatterExpansion

/-! ### The Einstein equations of smooth dust to the order `c⁻²` -/

section Main

variable {G : ℝ} {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3} {k : Set E3} {W : Set E}

theorem exists_abs_le_on {f : E → ℝ} (hf : Continuous f) (hW : Bornology.IsBounded W) :
    ∃ C, ∀ q ∈ W, |f q| ≤ C := by
  obtain ⟨C, hC⟩ := hW.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun q hq => by simpa [Real.norm_eq_abs] using hC q (subset_closure hq)⟩

/-- On a bounded set, the potentials, the density and the velocity of smooth dust have a common
bound. -/
theorem SmoothDust.exists_bounds (h : SmoothDust k ρ v) (hW : Bornology.IsBounded W) :
    ∃ K, PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K ∧
      (∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K) ∧ ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K := by
  obtain ⟨K₀, hb₀⟩ := h.exists_potentialBounds (G := G) hW
  obtain ⟨K₁, h₁⟩ := exists_abs_le_on (f := fun q => ρ (q 0) (spatialPoint q))
    (h.density_smooth.continuous.comp spacetimeMap.continuous) hW
  choose K₂ h₂ using fun β => exists_abs_le_on (f := fun q => dustVelocity v q β)
    ((h.contDiff_velocity β).continuous.comp spacetimeMap.continuous) hW
  have hs : 0 ≤ ∑ β, |K₂ β| := Finset.sum_nonneg fun β _ => abs_nonneg _
  have hs' (β : Fin 3) : |K₂ β| ≤ ∑ β, |K₂ β| :=
    Finset.single_le_sum (fun β _ => abs_nonneg (K₂ β)) (Finset.mem_univ β)
  have hK₀ := hb₀.nonneg
  refine ⟨K₀ + |K₁| + ∑ β, |K₂ β|, potentialBounds_mono hb₀ (by linarith [abs_nonneg K₁]),
    fun q hq => ?_, fun q hq β => ?_⟩
  · linarith [h₁ q hq, le_abs_self K₁]
  · linarith [h₂ β q hq, le_abs_self (K₂ β), hs' β, abs_nonneg K₁]

/-- **The source of dust to the order `c⁻²`**: on a bounded set of `(t, x)`,
`|κ(T − ½ g tr T)_jk − S_jk| ≤ C/c⁴` for `c ≥ c₁`, with `S = dustRicci`. -/
theorem SmoothDust.abs_dustSource_sub_le (h : SmoothDust k ρ v) (hW : Bornology.IsBounded W) :
    ∃ c₁ C, ∀ c, c₁ ≤ c → ∀ q ∈ W, ∀ j l : Fin 4,
      |dustSource G ρ v c q j l - dustRicci G ρ v c q j l| ≤ C / c ^ 4 := by
  obtain ⟨K, hb, hρ, hw⟩ := h.exists_bounds (G := G) hW
  choose C hC0 hC using fun j l => (exp_dustSource hb hρ hw j l).rem
  refine ⟨dustThreshold K, ∑ j, ∑ l, C j l, fun c hc q hq j l => ?_⟩
  have h1 := hC j l (c, q) ⟨hc, hq⟩
  have hc0 : 0 < c := by
    have := (dustThreshold_spec hb.nonneg hc).1
    unfold threshold at this
    nlinarith [hb.nonneg]
  have hc4 : epsilon c ^ 2 = 1 / c ^ 4 := by rw [epsilon, inv_pow, ← pow_mul, one_div]
  simp only at h1
  rw [hc4, mul_one_div] at h1
  have hle : C j l ≤ ∑ j, ∑ l, C j l :=
    (Finset.single_le_sum (fun l _ => hC0 j l) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun l _ => hC0 j l)
        (Finset.mem_univ j))
  exact h1.trans (div_le_div_of_nonneg_right hle (by positivity))

/-- **The post-Newtonian metric of smooth dust solves the Einstein equations up to `O(c⁻⁴)`**
(Landau–Lifshitz §106, the field equations of the second approximation). For smooth dust
(`SmoothDust`: a proper density `ρ̃` and a velocity `v` smooth in `(t, x)`, the density supported
in a fixed compact set of space, and the continuity equation `∂_t ρ̃ + ∇ · (ρ̃ v) = 0`), the
metric `dustMetric` (`g_tt = −c² − 2Φ − 2(Φ² + ψ)/c²`, `g_tα = B_α/c²`, `g_αβ = (1 − 2Φ/c²)δ_αβ`)
of the potentials `Φ = −4πG N[ρ̃]`, `ψ = −8πG N[ρ̃(v² + U)]` (`U = −Φ`) and
`B_α = −16πG N[ρ̃ v_α] − (G/2) χ[∂_α ∂_t ρ̃]` (the gauge of GR36, `3∂_tΦ + ∇ · B = 0`) satisfies
`|R_jk − κ(T_jk − ½ g_jk T)| ≤ C/c⁴` on every bounded set of `(t, x)` for `c ≥ c₁`.

Conventions: coordinates `(t, x)` with time first (`NewtonianCoordinates`); signature `(−+++)`;
the coordinate Ricci tensor `ricciOf`; `κ = 8πG/c⁴`; the stress of dust `T_ab = ρ̃ u_a u_b` with
`u = γ(1, v)`, `g(u, u) = −c²` (`dustSource`). The density is the proper (rest-frame) density
`ρ̃`, hence the source `ρ̃(v² + U)` of `ψ`; the source `ρ((3/2)v² − U)` of
`PostNewtonianField.secondPotential` belongs to the conserved density
`ρ* = ρ̃(1 + (v²/2 + 3U)/c²) + O(c⁻⁴)` (`√−g ρ̃ u⁰` in `x⁰ = ct`). The trace-reversed form
`R = κ(T − ½ g T)` is the form of the Einstein equations whose components have the orders
`R_tt = O(1)`, `R_tα = R_αβ = O(c⁻²)` in these coordinates; in `x⁰ = ct` the errors are
`O(c⁻⁶)`, `O(c⁻⁵)` and `O(c⁻⁴)`, the accuracy of the second approximation. -/
theorem SmoothDust.abs_ricciOf_sub_dustSource_le (h : SmoothDust k ρ v)
    (hW : Bornology.IsBounded W) :
    ∃ c₁ C, ∀ c, c₁ ≤ c → ∀ q ∈ W, ∀ j l : Fin 4,
      |ricciOf (d := 3) (dustMetric G ρ v c) q j l - dustSource G ρ v c q j l| ≤ C / c ^ 4 := by
  obtain ⟨c₁, C₁, h₁⟩ := h.abs_ricciOf_dustMetric_sub_le (G := G) hW
  obtain ⟨c₂, C₂, h₂⟩ := h.abs_dustSource_sub_le (G := G) hW
  refine ⟨max c₁ c₂, C₁ + C₂, fun c hc q hq j l => ?_⟩
  have a := h₁ c (le_of_max_le_left hc) q hq j l
  have b := h₂ c (le_of_max_le_right hc) q hq j l
  calc |ricciOf (d := 3) (dustMetric G ρ v c) q j l - dustSource G ρ v c q j l| =
      |(ricciOf (d := 3) (dustMetric G ρ v c) q j l - dustRicci G ρ v c q j l) -
        (dustSource G ρ v c q j l - dustRicci G ρ v c q j l)| := by ring_nf
    _ ≤ |ricciOf (d := 3) (dustMetric G ρ v c) q j l - dustRicci G ρ v c q j l| +
        |dustSource G ρ v c q j l - dustRicci G ρ v c q j l| := abs_sub _ _
    _ ≤ C₁ / c ^ 4 + C₂ / c ^ 4 := add_le_add a b
    _ = (C₁ + C₂) / c ^ 4 := by ring

end Main

/-! ### An instance -/

section Instance

/-- A smooth bump of radii `1` and `2` at the origin. -/
def dustBump : ContDiffBump (0 : E3) := ⟨1, 2, one_pos, one_lt_two⟩

/-- **An instance of smooth dust**: the static bump `ρ̃ = dustBump` at rest (`v = 0`), supported
in the closed ball of radius `2`; the continuity equation holds since `ρ̃` does not depend on
time and `ρ̃ v = 0`. -/
theorem smoothDust_bump :
    SmoothDust (Metric.closedBall 0 2) (fun _ y => dustBump y) (fun _ _ => 0) := by
  refine ⟨?_, contDiff_const, isCompact_closedBall 0 2, fun t y hy => ?_, fun t y => ?_⟩
  · exact dustBump.contDiff.comp contDiff_snd
  · refine dustBump.zero_of_le_dist ?_
    rw [Metric.mem_closedBall, not_le] at hy
    exact hy.le
  · simp

theorem dustBump_zero : dustBump (0 : E3) = 1 :=
  dustBump.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)

/-- **The hypotheses are satisfiable**: there is smooth dust with a nonzero density, and for it
the conclusion of `SmoothDust.abs_ricciOf_sub_dustSource_le` holds on the unit ball. -/
theorem exists_smoothDust (G : ℝ) :
    ∃ (k : Set E3) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3), SmoothDust k ρ v ∧ ρ 0 0 = 1 ∧
      ∃ c₁ C, ∀ c, c₁ ≤ c → ∀ q ∈ Metric.ball (0 : E) 1, ∀ j l : Fin 4,
        |ricciOf (d := 3) (dustMetric G ρ v c) q j l - dustSource G ρ v c q j l| ≤ C / c ^ 4 :=
  ⟨_, _, _, smoothDust_bump, dustBump_zero,
    smoothDust_bump.abs_ricciOf_sub_dustSource_le Metric.isBounded_ball⟩

end Instance

end ProjectAinos.GeneralRelativity.PostNewtonianDust
