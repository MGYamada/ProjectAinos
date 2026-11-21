/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.PostNewtonianDust

/-! Public consumers of the post-Newtonian metric of smooth dust (Landau–Lifshitz §106, the field
equations of the second approximation): the potentials of sources on space-time and their
derivatives, the coordinates `(t, x)`, smooth dust with its potentials in the gauge of GR36 and
their field equations, the Ricci tensor of the metric to the order `c⁻²`, the stress of dust and its
trace-reversed source, their expansion, the Einstein equations up to `O(c⁻⁴)`, and the instance;
and the superpotential of a Laplacian. Default elaborator options are intentional: these checks
must not rely on the implementation's transparency settings. Every statement is pinned with its
type. -/

noncomputable section

section PostNewtonianSources

open MeasureTheory

open scoped Real

namespace ProjectAinos.GeneralRelativity.PostNewtonianSources

open SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {f : E3 → ℝ} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 2 f) (x : E3) :
    superPotential (coordLaplacian f) x = 8 * π * newtonPotential f x :=
  superPotential_coordLaplacian hc hf x

end ProjectAinos.GeneralRelativity.PostNewtonianSources

end PostNewtonianSources

section PostNewtonianDust

open MeasureTheory Filter Set

open scoped Topology ContDiff Real Convolution

namespace ProjectAinos.GeneralRelativity.PostNewtonianDust

open SmoothGeometry.Potential SmoothGeometry.CoordinateMetric PostNewtonianSources
  PostNewtonianRicci NewtonianMetricFamily

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "E" => NewtonianCoordinates

local notation "S" => NewtonianSpace

section Potentials

example (k : Set E3) (f : ℝ × E3 → ℝ) : Prop :=
  SupportedIn k f

example (κ : E3 → ℝ) (f : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ :=
  pot κ f p

example (w : ℝ × E3) (f : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ :=
  dir w f p

example : ℝ × E3 :=
  eT

example (α : Fin 3) : ℝ × E3 :=
  eS α

example (f : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ :=
  lapS f p

variable {κ : E3 → ℝ} {f g : ℝ × E3 → ℝ} {k : Set E3}

example (κ : E3 → ℝ) (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    pot κ f p = ∫ y, κ y * f (p.1, p.2 - y) :=
  pot_apply κ f p

example (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    pot newtonKernel f p = newtonPotential (fun y => f (p.1, y)) p.2 :=
  pot_newtonKernel f p

example (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    pot (fun y => ‖y‖) f p = superPotential (fun y => f (p.1, y)) p.2 :=
  pot_norm f p

example (hk : IsCompact k) (hf : SupportedIn k f) (w : ℝ × E3) :
    SupportedIn k (dir w f) :=
  SupportedIn.dir hk hf w

example (hf : SupportedIn k f) (hg : SupportedIn k g) :
    SupportedIn k (fun p => f p + g p) :=
  SupportedIn.add hf hg

example (hf : SupportedIn k f) (a : ℝ × E3 → ℝ) :
    SupportedIn k (fun p => a p * f p) :=
  SupportedIn.mul_left hf a

example (hf : SupportedIn k f) (a : ℝ × E3 → ℝ) :
    SupportedIn k (fun p => f p * a p) :=
  SupportedIn.mul_right hf a

example (hk : IsCompact k) (hf : SupportedIn k f) (t : ℝ) :
    HasCompactSupport fun y => f (t, y) :=
  SupportedIn.hasCompactSupport hk hf t

example (hf : ContDiff ℝ ∞ f) (w : ℝ × E3) : ContDiff ℝ ∞ (dir w f) :=
  contDiff_dir hf w

example (hf : ContDiff ℝ ∞ f) (t : ℝ) : ContDiff ℝ ∞ fun y : E3 => f (t, y) :=
  contDiff_slice hf t

example (hκ : LocallyIntegrable κ) (hf : Continuous f) (hk : IsCompact k)
    (hfk : SupportedIn k f) (p : ℝ × E3) : Integrable fun y => κ y * f (p.1, p.2 - y) :=
  integrable_pot hκ hf hk hfk p

example (hκ : LocallyIntegrable κ) (hf : Continuous f) (hg : Continuous g)
    (hk : IsCompact k) (hfk : SupportedIn k f) (hgk : SupportedIn k g) (p : ℝ × E3) :
    pot κ (fun q => f q + g q) p = pot κ f p + pot κ g p :=
  pot_add hκ hf hg hk hfk hgk p

example (a : ℝ) (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    pot κ (fun q => a * f q) p = a * pot κ f p :=
  pot_const_mul a f p

example {ι : Type} (s : Finset ι) {F : ι → ℝ × E3 → ℝ} (hκ : LocallyIntegrable κ)
    (hF : ∀ i, Continuous (F i)) (hk : IsCompact k) (hFk : ∀ i, SupportedIn k (F i))
    (p : ℝ × E3) : pot κ (fun q => ∑ i ∈ s, F i q) p = ∑ i ∈ s, pot κ (F i) p :=
  pot_sum s hκ hF hk hFk p

example {f g : ℝ × E3 → ℝ} (h : ∀ q, f q = g q) (p : ℝ × E3) : pot κ f p = pot κ g p :=
  pot_congr h p

example (hκ : LocallyIntegrable κ) (hf : ContDiff ℝ ∞ f) (hk : IsCompact k)
    (hfk : SupportedIn k f) (p w : ℝ × E3) : fderiv ℝ (pot κ f) p w = pot κ (dir w f) p :=
  fderiv_pot_apply hκ hf hk hfk p w

example (hκ : LocallyIntegrable κ) (hf : ContDiff ℝ ∞ f) (hk : IsCompact k)
    (hfk : SupportedIn k f) : ContDiff ℝ ∞ (pot κ f) :=
  contDiff_pot hκ hf hk hfk

example (hf : Differentiable ℝ f) (t : ℝ) (y w : E3) :
    dir (0, w) f (t, y) = fderiv ℝ (fun z => f (t, z)) y w :=
  dir_slice hf t y w

example (hf : Differentiable ℝ f) (t : ℝ) (y : E3) :
    dir eT f (t, y) = deriv (fun s => f (s, y)) t :=
  dir_time hf t y

example (hf : ContDiff ℝ ∞ f) (t : ℝ) (y : E3) :
    lapS f (t, y) = coordLaplacian (fun z => f (t, z)) y :=
  lapS_eq hf t y

example (hf : ContDiff ℝ ∞ f) (hk : IsCompact k) (hfk : SupportedIn k f)
    (p : ℝ × E3) : pot newtonKernel (lapS f) p = -f p :=
  pot_newtonKernel_lapS hf hk hfk p

example (hf : ContDiff ℝ ∞ f) (hk : IsCompact k) (hfk : SupportedIn k f)
    (p : ℝ × E3) : pot (fun y => ‖y‖) (lapS f) p = 8 * π * pot newtonKernel f p :=
  pot_norm_lapS hf hk hfk p

end Potentials

section Algebra

variable {κ : E3 → ℝ} {f g : ℝ × E3 → ℝ} {k : Set E3}

example (k : Set E3) (f : ℝ × E3 → ℝ) : Prop :=
  IsSource k f

example (k : Set E3) : IsSource k fun _ => 0 :=
  isSource_zero k

example (hk : IsCompact k) (hf : IsSource k f) (w : ℝ × E3) :
    IsSource k (dir w f) :=
  IsSource.dir hk hf w

example (hf : IsSource k f) (hg : IsSource k g) :
    IsSource k fun p => f p + g p :=
  IsSource.add hf hg

example {a : ℝ × E3 → ℝ} (ha : ContDiff ℝ ∞ a) (hf : IsSource k f) :
    IsSource k fun p => a p * f p :=
  IsSource.mul_left ha hf

example {a : ℝ × E3 → ℝ} (hf : IsSource k f) (ha : ContDiff ℝ ∞ a) :
    IsSource k fun p => f p * a p :=
  IsSource.mul_right' hf ha

example (a : ℝ) (hf : IsSource k f) : IsSource k fun p => a * f p :=
  IsSource.const_mul a hf

example {ι : Type} (s : Finset ι) {F : ι → ℝ × E3 → ℝ}
    (hF : ∀ i, IsSource k (F i)) : IsSource k fun p => ∑ i ∈ s, F i p :=
  IsSource.sum s hF

example (hk : IsCompact k) (hf : IsSource k f) : IsSource k (lapS f) :=
  IsSource.lapS hk hf

example (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (w : ℝ × E3) :
    dir w (fun p => f p + g p) = fun p => dir w f p + dir w g p :=
  dir_add hf hg w

example (a : ℝ) (hf : Differentiable ℝ f) (w : ℝ × E3) :
    dir w (fun p => a * f p) = fun p => a * dir w f p :=
  dir_const_mul a hf w

example {ι : Type} (s : Finset ι) {F : ι → ℝ × E3 → ℝ}
    (hF : ∀ i, Differentiable ℝ (F i)) (w : ℝ × E3) :
    dir w (fun p => ∑ i ∈ s, F i p) = fun p => ∑ i ∈ s, dir w (F i) p :=
  dir_sum s hF w

example (hf : ContDiff ℝ ∞ f) (a b p : ℝ × E3) :
    dir a (dir b f) p = fderiv ℝ (fderiv ℝ f) p a b :=
  dir_dir_eq hf a b p

example (hf : ContDiff ℝ ∞ f) (a b : ℝ × E3) : dir a (dir b f) = dir b (dir a f) :=
  dir_comm hf a b

example (hf : ContDiff ℝ ∞ f) (w : ℝ × E3) : dir w (lapS f) = lapS (dir w f) :=
  dir_lapS hf w

example (hκ : LocallyIntegrable κ) (hk : IsCompact k) (hf : IsSource k f)
    (w : ℝ × E3) : dir w (pot κ f) = pot κ (dir w f) :=
  dir_pot hκ hk hf w

example (hκ : LocallyIntegrable κ) (hk : IsCompact k) (hf : IsSource k f) :
    lapS (pot κ f) = pot κ (lapS f) :=
  lapS_pot hκ hk hf

end Algebra

section Pullback

example (q : E) : E3 :=
  spatialPoint q

example : E →L[ℝ] ℝ × E3 :=
  spacetimeMap

example (q : E) : spacetimeMap q = (q 0, spatialPoint q) :=
  spacetimeMap_apply q

example : spacetimeMap (Pi.single 0 1) = eT :=
  spacetimeMap_single_zero

example (α : Fin 3) : spacetimeMap (Pi.single α.succ 1) = eS α :=
  spacetimeMap_single_succ α

example {F : ℝ × E3 → ℝ} (hF : Differentiable ℝ F) (q : E) (m : Fin 4) :
    pd (F ∘ spacetimeMap) q m = dir (spacetimeMap (Pi.single m 1)) F (spacetimeMap q) :=
  pd_comp_spacetimeMap hF q m

example {F : ℝ × E3 → ℝ} (hF : ContDiff ℝ ∞ F) (q : E) (m n : Fin 4) :
    pd2 (F ∘ spacetimeMap) q m n = dir (spacetimeMap (Pi.single m 1))
      (dir (spacetimeMap (Pi.single n 1)) F) (spacetimeMap q) :=
  pd2_comp_spacetimeMap hF q m n

example {F : ℝ × E3 → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (F ∘ spacetimeMap) :=
  contDiff_comp_spacetimeMap hF

example {F : ℝ × E3 → ℝ} (hF : ContDiff ℝ ∞ F) (q : E) (m n : Fin 4) :
    sd (F ∘ spacetimeMap) q m n = dir (spacetimeMap (Pi.single m 1))
      (dir (spacetimeMap (Pi.single n 1)) F) (spacetimeMap q) :=
  sd_comp_spacetimeMap hF q m n

example {F : ℝ × E3 → ℝ} (hF : ContDiff ℝ ∞ F) (q : E) :
    lap (F ∘ spacetimeMap) q = lapS F (spacetimeMap q) :=
  lap_comp_spacetimeMap hF q

end Pullback

example {f g : ℝ × E3 → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    lapS (fun p => f p + g p) = fun p => lapS f p + lapS g p :=
  lapS_add hf hg

section Dust

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (t : ℝ) : E3 → ℝ :=
  dustNewtonian G ρ t

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (t : ℝ) : E3 → ℝ :=
  dustSecond G ρ v t

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (t : ℝ) (α : Fin 3) (x : E3) : ℝ :=
  dustVector G ρ v t α x

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (q : E) : ℝ :=
  dustPhi G ρ q

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (q : E) : ℝ :=
  dustPsi G ρ v q

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (q : E) : S :=
  dustB G ρ v q

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (c : ℝ) (q : E) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  dustMetric G ρ v c q

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (p : ℝ × E3) : ℝ :=
  srcPhi G ρ p

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (p : ℝ × E3) : ℝ :=
  srcPsi G ρ v p

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (α : Fin 3) (p : ℝ × E3) : ℝ :=
  srcA G ρ v α p

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (α : Fin 3) (p : ℝ × E3) : ℝ :=
  srcW G ρ α p

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (α : Fin 3) (p : ℝ × E3) : ℝ :=
  potB G ρ v α p

variable {G : ℝ} {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3} {k : Set E3}

example (p : ℝ × E3) :
    dustNewtonian G ρ p.1 p.2 = pot newtonKernel (srcPhi G ρ) p :=
  dustNewtonian_eq p

example : dustPhi G ρ = pot newtonKernel (srcPhi G ρ) ∘ spacetimeMap :=
  dustPhi_eq

example : dustPsi G ρ v = pot newtonKernel (srcPsi G ρ v) ∘ spacetimeMap :=
  dustPsi_eq

example (α : Fin 3) : comp (dustB G ρ v) α = potB G ρ v α ∘ spacetimeMap :=
  comp_dustB α

example : srcPhi G ρ = fun p => -(4 * π * G) * Function.uncurry ρ p :=
  srcPhi_eq

example : srcPsi G ρ v = fun p => -(8 * π * G) * (Function.uncurry ρ p *
    (‖Function.uncurry v p‖ ^ 2 - pot newtonKernel (srcPhi G ρ) p)) :=
  srcPsi_eq

example (h : SmoothDust k ρ v) : IsSource k (Function.uncurry ρ) :=
  SmoothDust.isSource h

example (h : SmoothDust k ρ v) : IsSource k (srcPhi G ρ) :=
  SmoothDust.isSource_srcPhi h

example (h : SmoothDust k ρ v) (α : Fin 3) :
    ContDiff ℝ ∞ fun p : ℝ × E3 => v p.1 p.2 α :=
  SmoothDust.contDiff_velocity h α

example (h : SmoothDust k ρ v) (α : Fin 3) :
    IsSource k (srcA G ρ v α) :=
  SmoothDust.isSource_srcA h α

example (h : SmoothDust k ρ v) : IsSource k (srcPsi G ρ v) :=
  SmoothDust.isSource_srcPsi h

example (h : SmoothDust k ρ v) (α : Fin 3) :
    srcW G ρ α = fun p => -(G / 2) * dir (eS α) (dir eT (Function.uncurry ρ)) p :=
  SmoothDust.srcW_eq h α

example (h : SmoothDust k ρ v) (α : Fin 3) :
    IsSource k (srcW G ρ α) :=
  SmoothDust.isSource_srcW h α

example (h : SmoothDust k ρ v) (p : ℝ × E3) :
    ∑ α, dir (eS α) (srcA G ρ v α) p = 16 * π * G * dir eT (Function.uncurry ρ) p :=
  SmoothDust.sum_dir_srcA h p

end Dust

section Identities

variable {G : ℝ} {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3} {k : Set E3}

example (h : SmoothDust k ρ v) :
    ContDiff ℝ ∞ (pot newtonKernel (srcPhi G ρ)) :=
  SmoothDust.contDiff_potPhi h

example (h : SmoothDust k ρ v) :
    ContDiff ℝ ∞ (pot newtonKernel (srcPsi G ρ v)) :=
  SmoothDust.contDiff_potPsi h

example (h : SmoothDust k ρ v) (α : Fin 3) :
    ContDiff ℝ ∞ (potB G ρ v α) :=
  SmoothDust.contDiff_potB h α

example (h : SmoothDust k ρ v) : ContDiff ℝ ∞ (dustPhi G ρ) :=
  SmoothDust.contDiff_dustPhi h

example (h : SmoothDust k ρ v) : ContDiff ℝ ∞ (dustPsi G ρ v) :=
  SmoothDust.contDiff_dustPsi h

example (h : SmoothDust k ρ v) (α : Fin 3) :
    ContDiff ℝ ∞ (comp (dustB G ρ v) α) :=
  SmoothDust.contDiff_dustB h α

example (h : SmoothDust k ρ v) (q : E) :
    lap (dustPhi G ρ) q = 4 * π * G * ρ (q 0) (spatialPoint q) :=
  SmoothDust.lap_dustPhi h q

example (h : SmoothDust k ρ v) (q : E) :
    lap (dustPsi G ρ v) q = 8 * π * G * (ρ (q 0) (spatialPoint q) *
      (‖v (q 0) (spatialPoint q)‖ ^ 2 - dustPhi G ρ q)) :=
  SmoothDust.lap_dustPsi h q

example (h : SmoothDust k ρ v) (q : E) :
    3 * pd (dustPhi G ρ) q 0 + ∑ α, pd (comp (dustB G ρ v) α) q α.succ = 0 :=
  SmoothDust.gauge h q

example {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (n : Fin 4) (q : E) :
    DifferentiableAt ℝ (fun z => pd g z n) q :=
  differentiableAt_pd hg n q

example (g : E → ℝ) (q : E) (m n : Fin 4) :
    pd2 g q m n = fderiv ℝ (fun z => pd g z n) q (Pi.single m 1) :=
  pd2_eq_fderiv_pd g q m n

example (h : SmoothDust k ρ v) (q : E) (m : Fin 4) :
    3 * pd2 (dustPhi G ρ) q m 0 + ∑ α, pd2 (comp (dustB G ρ v) α) q m α.succ = 0 :=
  SmoothDust.fderiv_gauge h q m

example (h : SmoothDust k ρ v) (q : E) :
    3 * sd (dustPhi G ρ) q 0 0 + dtDiv (dustB G ρ v) q = 0 :=
  SmoothDust.gauge_rate h q

example (h : SmoothDust k ρ v) (q : E) (α : Fin 3) :
    gradDiv (dustB G ρ v) q α = -3 * pd2 (dustPhi G ρ) q α.succ 0 :=
  SmoothDust.gradDiv_eq h q α

example (ρ : ℝ → E3 → ℝ) (α : Fin 3) (p : ℝ × E3) : ℝ :=
  mixedRate ρ α p

example (h : SmoothDust k ρ v) (q : E) (α : Fin 3) :
    pd2 (dustPhi G ρ) q α.succ 0 = -(4 * π * G) * mixedRate ρ α (spacetimeMap q) :=
  SmoothDust.pd2_dustPhi h q α

example (h : SmoothDust k ρ v) (q : E) (α : Fin 3) :
    lap (comp (dustB G ρ v) α) q = 16 * π * G * (ρ (q 0) (spatialPoint q) *
      v (q 0) (spatialPoint q) α) - 4 * π * G * mixedRate ρ α (spacetimeMap q) :=
  SmoothDust.lap_dustB h q α

example (h : SmoothDust k ρ v) (q : E) (α : Fin 3) :
    lap (comp (dustB G ρ v) α) q - gradDiv (dustB G ρ v) q α - 4 * sd (dustPhi G ρ) q 0 α.succ =
      16 * π * G * (ρ (q 0) (spatialPoint q) * v (q 0) (spatialPoint q) α) :=
  SmoothDust.vector_eq h q α

example (h : SmoothDust k ρ v) (q : E) :
    4 * dustPhi G ρ q * lap (dustPhi G ρ) q + lap (dustPsi G ρ v) q =
      8 * π * G * (ρ (q 0) (spatialPoint q) *
        (‖v (q 0) (spatialPoint q)‖ ^ 2 + dustPhi G ρ q)) :=
  SmoothDust.scalar_eq h q

end Identities

section Bounds

example {Φ ψ : E → ℝ} {B : E → S} {W : Set E} {K K' : ℝ}
    (hb : PotentialBounds Φ ψ B W K) (hK : K ≤ K') : PotentialBounds Φ ψ B W K' :=
  potentialBounds_mono hb hK

example {g : E → ℝ} (hg : ContDiff ℝ 2 g) {W : Set E} {K : ℝ}
    (hb : CoordinateC2Bound W K g) {q : E} (hq : q ∈ W) :
    |g q| ≤ K ∧ (∀ m, |pd g q m| ≤ K) ∧ ∀ m n, |sd g q m n| ≤ K :=
  abs_le_of_coordinateC2Bound hg hb hq

example {Φ ψ : E → ℝ} {B : E → S} (hΦ : ContDiff ℝ 2 Φ)
    (hψ : ContDiff ℝ 2 ψ) (hB : ∀ j, ContDiff ℝ 2 (comp B j)) {W : Set E}
    (hW : Bornology.IsBounded W) : ∃ K, PotentialBounds Φ ψ B W K :=
  exists_potentialBounds hΦ hψ hB hW

end Bounds

section Ricci

variable {G : ℝ} {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3} {k : Set E3}

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (q : E) (j l : Fin 4) : ℝ :=
  dustLeading G ρ q j l

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (q : E) (j l : Fin 4) : ℝ :=
  dustFirst G ρ v q j l

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (c : ℝ) (q : E) (j l : Fin 4) : ℝ :=
  dustRicci G ρ v c q j l

example (h : SmoothDust k ρ v) (q : E) (j l : Fin 4) :
    ricciLeading (dustPhi G ρ) q j l = dustLeading G ρ q j l :=
  SmoothDust.ricciLeading_eq h q j l

example (h : SmoothDust k ρ v) (q : E) (j l : Fin 4) :
    ricciFirst (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) q j l = dustFirst G ρ v q j l :=
  SmoothDust.ricciFirst_eq h q j l

example (h : SmoothDust k ρ v) {W : Set E}
    (hW : Bornology.IsBounded W) :
    ∃ K, PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K :=
  SmoothDust.exists_potentialBounds h hW

example (h : SmoothDust k ρ v) {W : Set E}
    (hW : Bornology.IsBounded W) :
    ∃ c₁ C, ∀ c, c₁ ≤ c → ∀ q ∈ W, ∀ j l : Fin 4,
      |ricciOf (d := 3) (dustMetric G ρ v c) q j l - dustRicci G ρ v c q j l| ≤ C / c ^ 4 :=
  SmoothDust.abs_ricciOf_dustMetric_sub_le h hW

end Ricci

section Matter

open Matrix

example (w : S) : Fin 4 → ℝ :=
  flowVector w

example (g : Matrix (Fin 4) (Fin 4) ℝ) (c : ℝ) (w : S) : Fin 4 → ℝ :=
  fourVelocity g c w

example (g : Matrix (Fin 4) (Fin 4) ℝ) (c ρ : ℝ) (w : S) (a b : Fin 4) : ℝ :=
  dustStress g c ρ w a b

example (G c : ℝ) (g : Matrix (Fin 4) (Fin 4) ℝ) (T : Fin 4 → Fin 4 → ℝ)
    (a b : Fin 4) : ℝ :=
  traceReversedSource G c g T a b

example (v : ℝ → E3 → E3) (q : E) : S :=
  dustVelocity v q

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (c : ℝ) (q : E) (a b : Fin 4) : ℝ :=
  dustSource G ρ v c q a b

variable {g : Matrix (Fin 4) (Fin 4) ℝ} {G c ρ₀ : ℝ} {w : S}

example (hN : 0 < -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2) : c ≠ 0 :=
  ne_zero_of_normSq_pos hN

example (hN : 0 < -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2) :
    fourVelocity g c w ⬝ᵥ g *ᵥ fourVelocity g c w = -c ^ 2 :=
  fourVelocity_norm hN

example (hN : 0 < -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2) (a b : Fin 4) :
    dustStress g c ρ₀ w a b = ρ₀ * (-(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2)⁻¹ *
      (g *ᵥ flowVector w) a * (g *ᵥ flowVector w) b :=
  dustStress_eq hN a b

example (hg : g.det ≠ 0)
    (hN : 0 < -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2) :
    ∑ l, ∑ m, g⁻¹ l m * dustStress g c ρ₀ w l m = -(ρ₀ * c ^ 2) :=
  trace_dustStress hg hN

example (hg : g.det ≠ 0)
    (hN : 0 < -(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2) (a b : Fin 4) :
    traceReversedSource G c g (dustStress g c ρ₀ w) a b = 8 * π * G / c ^ 4 * (ρ₀ *
      ((-(flowVector w ⬝ᵥ g *ᵥ flowVector w) / c ^ 2)⁻¹ * (g *ᵥ flowVector w) a *
        (g *ᵥ flowVector w) b + c ^ 2 / 2 * g a b)) :=
  traceReversedSource_dustStress hg hN a b

end Matter

section MatterExpansion

open Matrix

example {e n₁ n₂ M : ℝ} (he : 0 ≤ e ∧ e ≤ 1) (h₁ : |n₁| ≤ M)
    (h₂ : |n₂| ≤ M) (hM : e * M ≤ 1 / 4) : 1 / 2 ≤ 1 + e * n₁ + e ^ 2 * n₂ :=
  one_half_le_of_bounds he h₁ h₂ hM

example {α : Type} {T : Set α} {ε n₁ n₂ : α → ℝ} {M : ℝ}
    (hε : ∀ p ∈ T, 0 ≤ ε p ∧ ε p ≤ 1) (h₁ : ∀ p ∈ T, |n₁ p| ≤ M) (h₂ : ∀ p ∈ T, |n₂ p| ≤ M)
    (hM : ∀ p ∈ T, ε p * M ≤ 1 / 4) :
    IsExp T ε (fun p => (1 + ε p * n₁ p + ε p ^ 2 * n₂ p)⁻¹) (fun _ => 1) (fun p => -n₁ p) :=
  isExp_inv_one_add hε h₁ h₂ hM

example (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) :
    pnCoefficient Φ ψ B c q 0 0 = -c ^ 2 - 2 * Φ q - 2 * epsilon c * (Φ q ^ 2 + ψ q) :=
  pnCoefficient_zero_zero Φ ψ B c q

example (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (α : Fin 3) :
    pnCoefficient Φ ψ B c q 0 α.succ = epsilon c * B q α :=
  pnCoefficient_zero_succ Φ ψ B c q α

example (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (α : Fin 3) :
    pnCoefficient Φ ψ B c q α.succ 0 = epsilon c * B q α :=
  pnCoefficient_succ_zero Φ ψ B c q α

example (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (α β : Fin 3) :
    pnCoefficient Φ ψ B c q α.succ β.succ = if α = β then spatialFactor Φ c q else 0 :=
  pnCoefficient_succ_succ Φ ψ B c q α β

example (w : S) (Y : Fin 4 → ℝ) :
    flowVector w ⬝ᵥ Y = Y 0 + ∑ β, w β * Y β.succ :=
  flowVector_dotProduct w Y

example (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (w : S) :
    (pnCoefficient Φ ψ B c q *ᵥ flowVector w) 0 =
      -c ^ 2 - 2 * Φ q - 2 * epsilon c * (Φ q ^ 2 + ψ q) + epsilon c * ∑ β, B q β * w β :=
  pnCoefficient_mulVec_zero Φ ψ B c q w

example (Φ ψ : E → ℝ) (B : E → S) (c : ℝ) (q : E) (w : S)
    (α : Fin 3) : (pnCoefficient Φ ψ B c q *ᵥ flowVector w) α.succ =
      epsilon c * B q α + spatialFactor Φ c q * w α :=
  pnCoefficient_mulVec_succ Φ ψ B c q w α

variable {G : ℝ} {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3} {W : Set E} {K c : ℝ}

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (c : ℝ) (q : E) : ℝ :=
  normFactor G ρ v c q

example (hc : c ≠ 0) (q : E) :
    normFactor G ρ v c q = 1 + epsilon c * (2 * dustPhi G ρ q - ∑ β, dustVelocity v q β ^ 2) +
      epsilon c ^ 2 * (2 * (dustPhi G ρ q ^ 2 + dustPsi G ρ v q) -
        2 * ∑ β, dustB G ρ v q β * dustVelocity v q β +
          2 * dustPhi G ρ q * ∑ β, dustVelocity v q β ^ 2) :=
  normFactor_eq hc q

example (K : ℝ) : ℝ :=
  normBound K

example (K : ℝ) : ℝ :=
  dustThreshold K

example (hK : 0 ≤ K) (hc : dustThreshold K ≤ c) :
    threshold K ≤ c ∧ 0 ≤ epsilon c ∧ epsilon c ≤ 1 ∧ epsilon c * normBound K ≤ 1 / 4 :=
  dustThreshold_spec hK hc

example {w : Fin 3 → ℝ} (hw : ∀ β, |w β| ≤ K) : |∑ β, w β ^ 2| ≤ 3 * K ^ 2 :=
  abs_sum_sq_le hw

example {b w : Fin 3 → ℝ} (hb : ∀ β, |b β| ≤ K) (hw : ∀ β, |w β| ≤ K) :
    |∑ β, b β * w β| ≤ 3 * K ^ 2 :=
  abs_sum_mul_le hb hw

example (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    {q : E} (hq : q ∈ W) (hc : threshold K ≤ c) (hN : 0 < normFactor G ρ v c q) (a b : Fin 4) :
    dustSource G ρ v c q a b = 8 * π * G / c ^ 4 * (ρ (q 0) (spatialPoint q) *
      ((normFactor G ρ v c q)⁻¹ * (dustMetric G ρ v c q *ᵥ flowVector (dustVelocity v q)) a *
        (dustMetric G ρ v c q *ᵥ flowVector (dustVelocity v q)) b +
          c ^ 2 / 2 * dustMetric G ρ v c q a b)) :=
  dustSource_eq hb hq hc hN a b

example (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
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
    ∀ p ∈ pnSet W (dustThreshold K), 0 < normFactor G ρ v p.1 p.2 :=
  dust_atoms hb hρ hw

example
    (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) {p : ℝ × E}
    (hp : p ∈ pnSet W (dustThreshold K)) (a b : Fin 4) :
    p.1 ≠ 0 ∧ dustSource G ρ v p.1 p.2 a b = 8 * π * G / p.1 ^ 4 *
      (ρ (p.2 0) (spatialPoint p.2) * ((normFactor G ρ v p.1 p.2)⁻¹ *
        (dustMetric G ρ v p.1 p.2 *ᵥ flowVector (dustVelocity v p.2)) a *
        (dustMetric G ρ v p.1 p.2 *ᵥ flowVector (dustVelocity v p.2)) b +
          p.1 ^ 2 / 2 * dustMetric G ρ v p.1 p.2 a b)) :=
  dustSource_eq_of_mem hb hρ hw hp a b

example
    (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) :
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => dustSource G ρ v p.1 p.2 0 0) (fun p => dustLeading G ρ p.2 0 0)
      (fun p => dustFirst G ρ v p.2 0 0) :=
  exp_dustSource_tt hb hρ hw

example
    (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) (β : Fin 3) :
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => dustSource G ρ v p.1 p.2 0 β.succ) (fun p => dustLeading G ρ p.2 0 β.succ)
      (fun p => dustFirst G ρ v p.2 0 β.succ) :=
  exp_dustSource_ts hb hρ hw β

example
    (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) (α : Fin 3) :
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => dustSource G ρ v p.1 p.2 α.succ 0) (fun p => dustLeading G ρ p.2 α.succ 0)
      (fun p => dustFirst G ρ v p.2 α.succ 0) :=
  exp_dustSource_st hb hρ hw α

example
    (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) (α β : Fin 3) :
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => dustSource G ρ v p.1 p.2 α.succ β.succ)
      (fun p => dustLeading G ρ p.2 α.succ β.succ)
      (fun p => dustFirst G ρ v p.2 α.succ β.succ) :=
  exp_dustSource_ss hb hρ hw α β

example (hb : PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K)
    (hρ : ∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K)
    (hw : ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K) (j l : Fin 4) :
    IsExp (pnSet W (dustThreshold K)) (fun p => epsilon p.1)
      (fun p => dustSource G ρ v p.1 p.2 j l) (fun p => dustLeading G ρ p.2 j l)
      (fun p => dustFirst G ρ v p.2 j l) :=
  exp_dustSource hb hρ hw j l

end MatterExpansion

section Main

variable {G : ℝ} {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3} {k : Set E3} {W : Set E}

example {f : E → ℝ} (hf : Continuous f) (hW : Bornology.IsBounded W) :
    ∃ C, ∀ q ∈ W, |f q| ≤ C :=
  exists_abs_le_on hf hW

example (h : SmoothDust k ρ v) (hW : Bornology.IsBounded W) :
    ∃ K, PotentialBounds (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) W K ∧
      (∀ q ∈ W, |ρ (q 0) (spatialPoint q)| ≤ K) ∧ ∀ q ∈ W, ∀ β, |dustVelocity v q β| ≤ K :=
  SmoothDust.exists_bounds h hW

example (h : SmoothDust k ρ v) (hW : Bornology.IsBounded W) :
    ∃ c₁ C, ∀ c, c₁ ≤ c → ∀ q ∈ W, ∀ j l : Fin 4,
      |dustSource G ρ v c q j l - dustRicci G ρ v c q j l| ≤ C / c ^ 4 :=
  SmoothDust.abs_dustSource_sub_le h hW

example (h : SmoothDust k ρ v)
    (hW : Bornology.IsBounded W) :
    ∃ c₁ C, ∀ c, c₁ ≤ c → ∀ q ∈ W, ∀ j l : Fin 4,
      |ricciOf (d := 3) (dustMetric G ρ v c) q j l - dustSource G ρ v c q j l| ≤ C / c ^ 4 :=
  SmoothDust.abs_ricciOf_sub_dustSource_le h hW

end Main

section Instance

example : ContDiffBump (0 : E3) :=
  dustBump

example :
    SmoothDust (Metric.closedBall 0 2) (fun _ y => dustBump y) (fun _ _ => 0) :=
  smoothDust_bump

example : dustBump (0 : E3) = 1 :=
  dustBump_zero

example (G : ℝ) :
    ∃ (k : Set E3) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3), SmoothDust k ρ v ∧ ρ 0 0 = 1 ∧
      ∃ c₁ C, ∀ c, c₁ ≤ c → ∀ q ∈ Metric.ball (0 : E) 1, ∀ j l : Fin 4,
        |ricciOf (d := 3) (dustMetric G ρ v c) q j l - dustSource G ρ v c q j l| ≤ C / c ^ 4 :=
  exists_smoothDust G

end Instance


section Structure

variable {k : Set E3} {ρ : ℝ → E3 → ℝ} {v : ℝ → E3 → E3}

example (k : Set E3) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) : Prop :=
  SmoothDust k ρ v

example (h : SmoothDust k ρ v) : ContDiff ℝ ∞ (Function.uncurry ρ) :=
  h.density_smooth

example (h : SmoothDust k ρ v) : ContDiff ℝ ∞ (Function.uncurry v) :=
  h.velocity_smooth

example (h : SmoothDust k ρ v) : IsCompact k :=
  h.isCompact

example (h : SmoothDust k ρ v) : ∀ t y, y ∉ k → ρ t y = 0 :=
  h.support

example (h : SmoothDust k ρ v) : ∀ t y, deriv (fun s => ρ s y) t +
    ∑ j, fderiv ℝ (fun z => ρ t z * v t z j) y (EuclideanSpace.single j 1) = 0 :=
  h.continuity

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (t : ℝ) :
    dustNewtonian G ρ t = newtonPotential fun y => -(4 * π * G) * ρ t y :=
  rfl

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (t : ℝ) :
    dustSecond G ρ v t = newtonPotential fun y =>
      -(8 * π * G) * (ρ t y * (‖v t y‖ ^ 2 - dustNewtonian G ρ t y)) :=
  rfl

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (t : ℝ) (α : Fin 3) (x : E3) :
    dustVector G ρ v t α x = newtonPotential (fun y => -(16 * π * G) * (ρ t y * v t y α)) x +
      superPotential (fun y => -(G / 2) *
        fderiv ℝ (fun z => deriv (fun s => ρ s z) t) y (EuclideanSpace.single α 1)) x :=
  rfl

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (c : ℝ) (q : E) :
    dustMetric G ρ v c q = pnCoefficient (dustPhi G ρ) (dustPsi G ρ v) (dustB G ρ v) c q :=
  rfl

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (c : ℝ) (q : E) (j l : Fin 4) :
    dustRicci G ρ v c q j l = dustLeading G ρ q j l + epsilon c * dustFirst G ρ v q j l :=
  rfl

example (G : ℝ) (ρ : ℝ → E3 → ℝ) (v : ℝ → E3 → E3) (c : ℝ) (q : E) (a b : Fin 4) :
    dustSource G ρ v c q a b = traceReversedSource G c (dustMetric G ρ v c q)
      (dustStress (dustMetric G ρ v c q) c (ρ (q 0) (spatialPoint q)) (dustVelocity v q)) a b :=
  rfl

example (G c : ℝ) (g : Matrix (Fin 4) (Fin 4) ℝ) (T : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    traceReversedSource G c g T a b =
      8 * π * G / c ^ 4 * (T a b - 1 / 2 * g a b * ∑ l, ∑ m, g⁻¹ l m * T l m) :=
  rfl

end Structure

end ProjectAinos.GeneralRelativity.PostNewtonianDust

end PostNewtonianDust
