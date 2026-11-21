/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Second-order expansions in a small parameter, uniformly in a parameter

A function `f(ε, p)` along a filter `l` on `ℝ × P` on which `ε → 0` has the expansion
`c₀(p) + ε c₁(p) + ε² c₂(p)` (`HasExp l f c₀ c₁ c₂`) when the coefficients are bounded along `l`
and `f − (c₀ + ε c₁ + ε² c₂) = O(ε³)`. For `l = 𝓝[>] 0 ×ˢ 𝓟 K` this is an expansion uniform
in `p ∈ K` (`HasExp.exists_bound`). Expansions add (`HasExp.add`, `HasExp.sub`, `HasExp.neg`), are
multiplied by `ε` (`HasExp.eps_smul`), are unchanged by an `O(ε³)` change of the function
(`HasExp.of_isBigO_sub`), compose with continuous bilinear maps
(`HasExp.bilin`, with the truncated Cauchy product of the coefficients), in particular products
(`HasExp.mul`) and scalar multiples (`HasExp.smul`), and invert when the leading coefficient
is `1` (`HasExp.inv`). The coefficients may be replaced by equal ones (`HasExp.congr_coeff`).

These are the tools of the expansion of the field of a point charge on Dirac's world tube
(`Electrodynamics.RadiationReaction.WorldTube`).
-/

@[expose] public section

noncomputable section

open Filter Asymptotics Set
open scoped Topology

namespace ProjectAinos.Electrodynamics.RadiationReaction.WorldTube

variable {P : Type*} {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The truncated series `c₀(p) + ε c₁(p) + ε² c₂(p)` at `x = (ε, p)`. -/
def series3 (c₀ c₁ c₂ : P → E) (x : ℝ × P) : E := c₀ x.2 + x.1 • c₁ x.2 + x.1 ^ 2 • c₂ x.2

/-- `f` has along `l` the expansion `c₀ + ε c₁ + ε² c₂` with bounded coefficients and a remainder
`O(ε³)`. -/
structure HasExp (l : Filter (ℝ × P)) (f : ℝ × P → E) (c₀ c₁ c₂ : P → E) : Prop where
  bdd₀ : (fun x : ℝ × P => c₀ x.2) =O[l] (fun _ => (1 : ℝ))
  bdd₁ : (fun x : ℝ × P => c₁ x.2) =O[l] (fun _ => (1 : ℝ))
  bdd₂ : (fun x : ℝ × P => c₂ x.2) =O[l] (fun _ => (1 : ℝ))
  rem : (fun x => f x - series3 c₀ c₁ c₂ x) =O[l] (fun x => x.1 ^ 3)

variable {l : Filter (ℝ × P)}

/-- Along a filter on which `ε → 0`, `ε` is bounded. -/
theorem isBigO_fst_one (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) :
    (fun x : ℝ × P => x.1) =O[l] (fun _ => (1 : ℝ)) :=
  hl.isBigO_one ℝ

/-- Along a filter on which `ε → 0`, `εⁿ = O(εᵐ)` for `m ≤ n`. -/
theorem isBigO_pow_pow (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) {m n : ℕ} (h : m ≤ n) :
    (fun x : ℝ × P => x.1 ^ n) =O[l] (fun x => x.1 ^ m) := by
  have e : (fun x : ℝ × P => x.1 ^ n) = fun x => x.1 ^ m * x.1 ^ (n - m) := by
    funext x
    rw [← pow_add, Nat.add_sub_cancel' h]
  rw [e]
  have h1 : (fun x : ℝ × P => x.1 ^ (n - m)) =O[l] (fun _ => (1 : ℝ)) :=
    ((isBigO_fst_one hl).pow (n - m)).trans (by simp [isBigO_refl])
  simpa using (isBigO_refl (fun x : ℝ × P => x.1 ^ m) l).mul h1

/-- Along a filter on which `ε → 0`, `εⁿ` is bounded. -/
theorem isBigO_pow_one (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (n : ℕ) :
    (fun x : ℝ × P => x.1 ^ n) =O[l] (fun _ => (1 : ℝ)) := by
  simpa using isBigO_pow_pow hl (m := 0) (n := n) (Nat.zero_le n)

/-- The image of two functions under a continuous bilinear map is bounded by the product of
their bounds. -/
theorem isBigO_bilin {α : Type*} {l' : Filter α} (B : E →L[ℝ] F →L[ℝ] G) {f : α → E} {g : α → F}
    {φ ψ : α → ℝ} (hf : f =O[l'] φ) (hg : g =O[l'] ψ) :
    (fun x => B (f x) (g x)) =O[l'] (fun x => φ x * ψ x) := by
  have h1 : (fun x => B (f x) (g x)) =O[l'] (fun x => ‖f x‖ * ‖g x‖) := by
    refine IsBigO.of_bound ‖B‖ (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc]
    exact B.le_opNorm₂ (f x) (g x)
  exact h1.trans (hf.norm_left.mul hg.norm_left)

namespace HasExp

variable {f g : ℝ × P → E} {c₀ c₁ c₂ d₀ d₁ d₂ : P → E}

/-- A truncated series with bounded coefficients is bounded. -/
theorem series_isBigO_one (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0))
    (h₀ : (fun x : ℝ × P => c₀ x.2) =O[l] (fun _ => (1 : ℝ)))
    (h₁ : (fun x : ℝ × P => c₁ x.2) =O[l] (fun _ => (1 : ℝ)))
    (h₂ : (fun x : ℝ × P => c₂ x.2) =O[l] (fun _ => (1 : ℝ))) :
    (fun x => series3 c₀ c₁ c₂ x) =O[l] (fun _ => (1 : ℝ)) := by
  have a1 : (fun x : ℝ × P => x.1 • c₁ x.2) =O[l] (fun _ => (1 : ℝ)) := by
    simpa using (isBigO_fst_one hl).smul h₁
  have a2 : (fun x : ℝ × P => x.1 ^ 2 • c₂ x.2) =O[l] (fun _ => (1 : ℝ)) := by
    simpa using (isBigO_pow_one hl 2).smul h₂
  exact (h₀.add a1).add a2

/-- A function with an expansion is bounded. -/
theorem isBigO_one (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (h : HasExp l f c₀ c₁ c₂) :
    f =O[l] (fun _ => (1 : ℝ)) := by
  have hs := series_isBigO_one hl h.bdd₀ h.bdd₁ h.bdd₂
  have hr : (fun x => f x - series3 c₀ c₁ c₂ x) =O[l] (fun _ => (1 : ℝ)) :=
    h.rem.trans (isBigO_pow_one hl 3)
  simpa using hr.add hs

/-- The leading term: `f − c₀ = O(ε)`. -/
theorem sub_isBigO (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (h : HasExp l f c₀ c₁ c₂) :
    (fun x => f x - c₀ x.2) =O[l] (fun x => x.1) := by
  have e : (fun x => f x - c₀ x.2) = fun x => (f x - series3 c₀ c₁ c₂ x) +
      (x.1 • c₁ x.2 + x.1 ^ 2 • c₂ x.2) := by
    funext x
    simp only [series3]
    abel
  rw [e]
  have h3 : (fun x : ℝ × P => x.1 ^ 3) =O[l] (fun x => x.1) := by
    simpa using isBigO_pow_pow hl (m := 1) (n := 3) (by norm_num)
  have a1 : (fun x : ℝ × P => x.1 • c₁ x.2) =O[l] (fun x => x.1) := by
    simpa using (isBigO_refl (fun x : ℝ × P => x.1) l).smul h.bdd₁
  have a2 : (fun x : ℝ × P => x.1 ^ 2 • c₂ x.2) =O[l] (fun x => x.1) := by
    have h2 : (fun x : ℝ × P => x.1 ^ 2) =O[l] (fun x => x.1) := by
      simpa using isBigO_pow_pow hl (m := 1) (n := 2) (by norm_num)
    simpa using h2.smul h.bdd₂
  exact (h.rem.trans h3).add (a1.add a2)

/-- The first two terms: `f − c₀ − ε c₁ = O(ε²)`. -/
theorem sub_isBigO_two (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (h : HasExp l f c₀ c₁ c₂) :
    (fun x => f x - (c₀ x.2 + x.1 • c₁ x.2)) =O[l] (fun x => x.1 ^ 2) := by
  have e : (fun x => f x - (c₀ x.2 + x.1 • c₁ x.2)) = fun x => (f x - series3 c₀ c₁ c₂ x) +
      x.1 ^ 2 • c₂ x.2 := by
    funext x
    simp only [series3]
    abel
  rw [e]
  have h3 : (fun x : ℝ × P => x.1 ^ 3) =O[l] (fun x => x.1 ^ 2) :=
    isBigO_pow_pow hl (by norm_num)
  have a2 : (fun x : ℝ × P => x.1 ^ 2 • c₂ x.2) =O[l] (fun x => x.1 ^ 2) := by
    simpa using (isBigO_refl (fun x : ℝ × P => x.1 ^ 2) l).smul h.bdd₂
  exact (h.rem.trans h3).add a2

/-- The leading coefficient is the limit: `f − c₀ → 0`. -/
theorem tendsto_sub (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (h : HasExp l f c₀ c₁ c₂) :
    Tendsto (fun x => f x - c₀ x.2) l (𝓝 0) :=
  (h.sub_isBigO hl).trans_tendsto hl

/-- Replacing the function by one equal to it eventually. -/
theorem congr_fun (h : HasExp l f c₀ c₁ c₂) (hfg : ∀ᶠ x in l, f x = g x) :
    HasExp l g c₀ c₁ c₂ where
  bdd₀ := h.bdd₀
  bdd₁ := h.bdd₁
  bdd₂ := h.bdd₂
  rem := h.rem.congr' (hfg.mono fun x hx => by simp only [hx]) EventuallyEq.rfl

/-- Replacing the coefficients by ones equal to them eventually. -/
theorem congr_coeff (h : HasExp l f c₀ c₁ c₂) (h₀ : ∀ᶠ x in l, c₀ x.2 = d₀ x.2)
    (h₁ : ∀ᶠ x in l, c₁ x.2 = d₁ x.2) (h₂ : ∀ᶠ x in l, c₂ x.2 = d₂ x.2) :
    HasExp l f d₀ d₁ d₂ where
  bdd₀ := h.bdd₀.congr' h₀ EventuallyEq.rfl
  bdd₁ := h.bdd₁.congr' h₁ EventuallyEq.rfl
  bdd₂ := h.bdd₂.congr' h₂ EventuallyEq.rfl
  rem := h.rem.congr' (by
    filter_upwards [h₀, h₁, h₂] with x a b c
    simp only [series3, a, b, c]) EventuallyEq.rfl

/-- A function of the parameter alone that is bounded is its own expansion. -/
theorem const (hc : (fun x : ℝ × P => c₀ x.2) =O[l] (fun _ => (1 : ℝ))) :
    HasExp l (fun x => c₀ x.2) c₀ 0 0 where
  bdd₀ := hc
  bdd₁ := IsBigO.of_bound 0 (Eventually.of_forall fun x => by simp)
  bdd₂ := IsBigO.of_bound 0 (Eventually.of_forall fun x => by simp)
  rem := IsBigO.of_bound 0 (Eventually.of_forall fun x => by simp [series3])

/-- A truncated series with bounded coefficients is its own expansion. -/
theorem series (h₀ : (fun x : ℝ × P => c₀ x.2) =O[l] (fun _ => (1 : ℝ)))
    (h₁ : (fun x : ℝ × P => c₁ x.2) =O[l] (fun _ => (1 : ℝ)))
    (h₂ : (fun x : ℝ × P => c₂ x.2) =O[l] (fun _ => (1 : ℝ))) :
    HasExp l (series3 c₀ c₁ c₂) c₀ c₁ c₂ where
  bdd₀ := h₀
  bdd₁ := h₁
  bdd₂ := h₂
  rem := IsBigO.of_bound 0 (Eventually.of_forall fun x => by simp)

/-- A function within `O(ε³)` of one with an expansion has the same expansion. -/
theorem of_isBigO_sub (hf : HasExp l f c₀ c₁ c₂)
    (h : (fun x => g x - f x) =O[l] (fun x => x.1 ^ 3)) : HasExp l g c₀ c₁ c₂ where
  bdd₀ := hf.bdd₀
  bdd₁ := hf.bdd₁
  bdd₂ := hf.bdd₂
  rem := by
    have e : (fun x => g x - series3 c₀ c₁ c₂ x) =
        fun x => (g x - f x) + (f x - series3 c₀ c₁ c₂ x) := by
      funext x; abel
    rw [e]
    exact h.add hf.rem

/-- The sum of two expansions. -/
theorem add (hf : HasExp l f c₀ c₁ c₂) (hg : HasExp l g d₀ d₁ d₂) :
    HasExp l (fun x => f x + g x) (fun p => c₀ p + d₀ p) (fun p => c₁ p + d₁ p)
      (fun p => c₂ p + d₂ p) where
  bdd₀ := hf.bdd₀.add hg.bdd₀
  bdd₁ := hf.bdd₁.add hg.bdd₁
  bdd₂ := hf.bdd₂.add hg.bdd₂
  rem := by
    have e : (fun x => f x + g x - series3 (fun p => c₀ p + d₀ p) (fun p => c₁ p + d₁ p)
        (fun p => c₂ p + d₂ p) x) =
        fun x => (f x - series3 c₀ c₁ c₂ x) + (g x - series3 d₀ d₁ d₂ x) := by
      funext x
      simp only [series3, smul_add]
      abel
    rw [e]
    exact hf.rem.add hg.rem

/-- The negative of an expansion. -/
theorem neg (hf : HasExp l f c₀ c₁ c₂) :
    HasExp l (fun x => -f x) (fun p => -c₀ p) (fun p => -c₁ p) (fun p => -c₂ p) where
  bdd₀ := hf.bdd₀.neg_left
  bdd₁ := hf.bdd₁.neg_left
  bdd₂ := hf.bdd₂.neg_left
  rem := by
    have e : (fun x => -f x - series3 (fun p => -c₀ p) (fun p => -c₁ p) (fun p => -c₂ p) x) =
        fun x => -(f x - series3 c₀ c₁ c₂ x) := by
      funext x
      simp only [series3, smul_neg]
      abel
    rw [e]
    exact hf.rem.neg_left

/-- The difference of two expansions. -/
theorem sub (hf : HasExp l f c₀ c₁ c₂) (hg : HasExp l g d₀ d₁ d₂) :
    HasExp l (fun x => f x - g x) (fun p => c₀ p - d₀ p) (fun p => c₁ p - d₁ p)
      (fun p => c₂ p - d₂ p) := by
  have h := hf.add hg.neg
  simp only [← sub_eq_add_neg] at h
  exact h

/-- Multiplication by `ε` shifts the coefficients. -/
theorem eps_smul (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (hf : HasExp l f c₀ c₁ c₂) :
    HasExp l (fun x => x.1 • f x) 0 c₀ c₁ where
  bdd₀ := IsBigO.of_bound 0 (Eventually.of_forall fun x => by simp)
  bdd₁ := hf.bdd₀
  bdd₂ := hf.bdd₁
  rem := by
    have e : (fun x => x.1 • f x - series3 0 c₀ c₁ x) =
        fun x => x.1 • (f x - series3 c₀ c₁ c₂ x) + x.1 ^ 3 • c₂ x.2 := by
      funext x
      simp only [series3, Pi.zero_apply, zero_add, smul_sub, smul_add, smul_smul]
      ring_nf
      abel
    rw [e]
    have a1 : (fun x : ℝ × P => x.1 • (f x - series3 c₀ c₁ c₂ x)) =O[l] (fun x => x.1 ^ 3) := by
      simpa using (isBigO_fst_one hl).smul hf.rem
    have a2 : (fun x : ℝ × P => x.1 ^ 3 • c₂ x.2) =O[l] (fun x => x.1 ^ 3) := by
      simpa using (isBigO_refl (fun x : ℝ × P => x.1 ^ 3) l).smul hf.bdd₂
    exact a1.add a2

/-- **The image under a continuous bilinear map** has the truncated Cauchy product of the
coefficients. -/
theorem bilin (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) (B : E →L[ℝ] F →L[ℝ] G)
    {f : ℝ × P → E} {g : ℝ × P → F} {c₀ c₁ c₂ : P → E} {d₀ d₁ d₂ : P → F}
    (hf : HasExp l f c₀ c₁ c₂) (hg : HasExp l g d₀ d₁ d₂) :
    HasExp l (fun x => B (f x) (g x)) (fun p => B (c₀ p) (d₀ p))
      (fun p => B (c₀ p) (d₁ p) + B (c₁ p) (d₀ p))
      (fun p => B (c₀ p) (d₂ p) + B (c₁ p) (d₁ p) + B (c₂ p) (d₀ p)) where
  bdd₀ := by simpa using isBigO_bilin B hf.bdd₀ hg.bdd₀
  bdd₁ := by simpa using (isBigO_bilin B hf.bdd₀ hg.bdd₁).add (isBigO_bilin B hf.bdd₁ hg.bdd₀)
  bdd₂ := by
    simpa using ((isBigO_bilin B hf.bdd₀ hg.bdd₂).add (isBigO_bilin B hf.bdd₁ hg.bdd₁)).add
      (isBigO_bilin B hf.bdd₂ hg.bdd₀)
  rem := by
    set Sf := series3 c₀ c₁ c₂ with hSf
    set Sg := series3 d₀ d₁ d₂ with hSg
    have e : (fun x => B (f x) (g x) - series3 (fun p => B (c₀ p) (d₀ p))
        (fun p => B (c₀ p) (d₁ p) + B (c₁ p) (d₀ p))
        (fun p => B (c₀ p) (d₂ p) + B (c₁ p) (d₁ p) + B (c₂ p) (d₀ p)) x) =
        fun x => B (f x - Sf x) (g x) + B (Sf x) (g x - Sg x) +
          (x.1 ^ 3 • (B (c₁ x.2) (d₂ x.2) + B (c₂ x.2) (d₁ x.2)) +
            x.1 ^ 4 • B (c₂ x.2) (d₂ x.2)) := by
      funext x
      simp only [hSf, hSg, series3, map_add, map_sub, map_smul, FunLike.coe_add,
        FunLike.coe_sub, FunLike.coe_smul, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_add, smul_smul]
      module
    rw [e]
    have hgb := hg.isBigO_one hl
    have hSfb := series_isBigO_one hl hf.bdd₀ hf.bdd₁ hf.bdd₂
    have a1 : (fun x => B (f x - Sf x) (g x)) =O[l] (fun x => x.1 ^ 3) := by
      simpa using isBigO_bilin B hf.rem hgb
    have a2 : (fun x => B (Sf x) (g x - Sg x)) =O[l] (fun x => x.1 ^ 3) := by
      simpa using isBigO_bilin B hSfb hg.rem
    have a3 : (fun x : ℝ × P => x.1 ^ 3 • (B (c₁ x.2) (d₂ x.2) + B (c₂ x.2) (d₁ x.2))) =O[l]
        (fun x => x.1 ^ 3) := by
      simpa using (isBigO_refl (fun x : ℝ × P => x.1 ^ 3) l).smul
        ((isBigO_bilin B hf.bdd₁ hg.bdd₂).add (isBigO_bilin B hf.bdd₂ hg.bdd₁))
    have a4 : (fun x : ℝ × P => x.1 ^ 4 • B (c₂ x.2) (d₂ x.2)) =O[l] (fun x => x.1 ^ 3) := by
      simpa using (isBigO_pow_pow hl (m := 3) (n := 4) (by norm_num)).smul
        (isBigO_bilin B hf.bdd₂ hg.bdd₂)
    exact (a1.add a2).add (a3.add a4)

/-- **The product of two expansions** of real functions. -/
theorem mul (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) {f g : ℝ × P → ℝ}
    {c₀ c₁ c₂ d₀ d₁ d₂ : P → ℝ} (hf : HasExp l f c₀ c₁ c₂) (hg : HasExp l g d₀ d₁ d₂) :
    HasExp l (fun x => f x * g x) (fun p => c₀ p * d₀ p) (fun p => c₀ p * d₁ p + c₁ p * d₀ p)
      (fun p => c₀ p * d₂ p + c₁ p * d₁ p + c₂ p * d₀ p) := by
  simpa using hf.bilin hl (ContinuousLinearMap.mul ℝ ℝ) hg

/-- **A scalar multiple**: the expansion of `f • g` for a real `f`. -/
theorem smul (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) {f : ℝ × P → ℝ} {g : ℝ × P → E}
    {c₀ c₁ c₂ : P → ℝ} {d₀ d₁ d₂ : P → E} (hf : HasExp l f c₀ c₁ c₂)
    (hg : HasExp l g d₀ d₁ d₂) :
    HasExp l (fun x => f x • g x) (fun p => c₀ p • d₀ p)
      (fun p => c₀ p • d₁ p + c₁ p • d₀ p)
      (fun p => c₀ p • d₂ p + c₁ p • d₁ p + c₂ p • d₀ p) := by
  simpa using hf.bilin hl (ContinuousLinearMap.lsmul ℝ ℝ) hg

/-- Eventually a function with the leading coefficient `1` is at least `1/2`. -/
theorem eventually_half_le (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) {f : ℝ × P → ℝ}
    {c₁ c₂ : P → ℝ} (hf : HasExp l f 1 c₁ c₂) : ∀ᶠ x in l, 1 / 2 ≤ f x := by
  have h := (hf.tendsto_sub hl).eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num :
    (0 : ℝ) < 1 / 2))
  filter_upwards [h] with x hx
  rw [dist_zero_right, Real.norm_eq_abs, Pi.one_apply] at hx
  have := neg_abs_le (f x - 1)
  linarith

/-- **The inverse** of an expansion with the leading coefficient `1`. -/
theorem inv (hl : Tendsto (fun x : ℝ × P => x.1) l (𝓝 0)) {f : ℝ × P → ℝ} {c₁ c₂ : P → ℝ}
    (hf : HasExp l f 1 c₁ c₂) :
    HasExp l (fun x => (f x)⁻¹) 1 (fun p => -c₁ p) (fun p => c₁ p ^ 2 - c₂ p) := by
  have hb₁ : (fun x : ℝ × P => -c₁ x.2) =O[l] (fun _ => (1 : ℝ)) := hf.bdd₁.neg_left
  have hb₂ : (fun x : ℝ × P => c₁ x.2 ^ 2 - c₂ x.2) =O[l] (fun _ => (1 : ℝ)) := by
    have h11 : (fun x : ℝ × P => c₁ x.2 ^ 2) =O[l] (fun _ => (1 : ℝ)) := by
      simpa [sq] using hf.bdd₁.mul hf.bdd₁
    exact h11.sub hf.bdd₂
  have hQ := HasExp.series (l := l) (c₀ := 1) (c₁ := fun p => -c₁ p)
    (c₂ := fun p => c₁ p ^ 2 - c₂ p) hf.bdd₀ hb₁ hb₂
  have hfQ := (hf.mul hl hQ).congr_coeff (d₀ := 1) (d₁ := 0) (d₂ := 0)
    (Eventually.of_forall fun x => by simp) (Eventually.of_forall fun x => by simp)
    (Eventually.of_forall fun x => by simp; ring)
  have hr : (fun x => f x * series3 1 (fun p => -c₁ p) (fun p => c₁ p ^ 2 - c₂ p) x - 1) =O[l]
      (fun x => x.1 ^ 3) := by
    simpa [series3] using hfQ.rem
  have hinvb : (fun x => (f x)⁻¹) =O[l] (fun _ => (1 : ℝ)) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [hf.eventually_half_le hl] with x hx
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith), norm_one, mul_one]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  refine ⟨hf.bdd₀, hb₁, hb₂, ?_⟩
  have e : ∀ᶠ x in l, (f x)⁻¹ - series3 1 (fun p => -c₁ p) (fun p => c₁ p ^ 2 - c₂ p) x =
      -((f x * series3 1 (fun p => -c₁ p) (fun p => c₁ p ^ 2 - c₂ p) x - 1) * (f x)⁻¹) := by
    filter_upwards [hf.eventually_half_le hl] with x hx
    have hx0 : f x ≠ 0 := by linarith
    field_simp
    ring
  refine IsBigO.congr' ?_ (e.mono fun x hx => hx.symm) EventuallyEq.rfl
  simpa using (hr.mul hinvb).neg_left

/-- **The uniform bound**: along `𝓝[>] 0 ×ˢ 𝓟 K`, the remainder is at most `C ε³` for all small
`ε > 0` and all `p ∈ K`. -/
theorem exists_bound {K : Set P} {f : ℝ × P → E} {c₀ c₁ c₂ : P → E}
    (h : HasExp (𝓝[>] (0 : ℝ) ×ˢ 𝓟 K) f c₀ c₁ c₂) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∀ p ∈ K,
      ‖f (ε, p) - (c₀ p + ε • c₁ p + ε ^ 2 • c₂ p)‖ ≤ C * ε ^ 3 := by
  obtain ⟨C, hC⟩ := h.rem.bound
  rw [eventually_prod_principal_iff, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hC
  obtain ⟨ε₀, hε₀, hb⟩ := hC
  refine ⟨C, ε₀, hε₀, fun ε hε p hp => ?_⟩
  have h1 := hb (y := ε) (by rw [Real.dist_eq, sub_zero, abs_of_pos hε.1]; exact hε.2) hε.1 p hp
  rw [Real.norm_eq_abs, abs_of_pos (pow_pos hε.1 3)] at h1
  simpa [series3] using h1

end HasExp

end ProjectAinos.Electrodynamics.RadiationReaction.WorldTube
