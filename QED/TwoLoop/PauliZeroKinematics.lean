/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroCovariance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Pauli component of the order-`e⁵` vertex limit depends on the pair only through `q²`

Part of obligation O2-22 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4), the reduction "by O2-20,
`F̂₂` depends on the pair only through `q²`". For two on-shell positive-energy pairs `(p', p)` and
`(k', k)` with the same `q²` (equivalently the same `p'·p`), the Pauli projections of the
`ε → 0⁺` limits of the order-`e⁵` vertex agree (`formFactorProj₂_eq_of_dot_eq`), and so do the
Pauli components of their form-factor pairs (`snd_eq_of_isFormFactorPair_of_dot_eq`).

## Proof

The second pair is reached from the first by at most two reflections in spacelike vectors, each
of which has the spinor lift `(a̸Γ, a̸Γ/(a·a))` (`QED.TwoLoop.ReflCovariance.isSpinLift_reflect`)
and keeps positive energies; the Pauli projector is invariant under each
(`QED.TwoLoop.PauliZero.formFactorProj₂_vertexLimit_map`).

* `R₁`, the reflection in `a₁ = p - k` (skipped if `p = k`), maps `p` to `k` and `p'` to some
  `p''`. Since `a₁ ⊥ p + k` and `p + k` is timelike, `a₁` is spacelike
  (`dot_self_pos_of_dot_eq_zero`). `p''` has positive energy because `p''·k = p'·p < 0`
  (`pos_of_dot_neg`).
* `R₂`, the reflection in `a₂ = p'' - k'` (skipped if `p'' = k'`), fixes `k` (as
  `a₂·k = p'·p - k'·k = 0`) and maps `p''` to `k'`; `a₂ ⊥ k` makes it spacelike.

The timelike inequalities are proved from the Lagrange identity in the three spatial components.
-/

@[expose] public section

open Complex Matrix Filter Topology

namespace QED.TwoLoop.PauliZero

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.ReflCovariance

/-! ### Timelike vectors -/

/-- The Lagrange identity bound `(x⃗·y⃗)² ≤ |x⃗|² |y⃗|²` in the spatial components. -/
theorem spatial_cauchySchwarz (x y : Fin 4 → ℝ) :
    (x 1 * y 1 + x 2 * y 2 + x 3 * y 3) ^ 2 ≤
      (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) * (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) := by
  nlinarith [sq_nonneg (x 1 * y 2 - x 2 * y 1), sq_nonneg (x 1 * y 3 - x 3 * y 1),
    sq_nonneg (x 2 * y 3 - x 3 * y 2)]

/-- Two future timelike vectors have negative product. -/
theorem dot_neg_of_timelike {x y : Fin 4 → ℝ} (hx : Minkowski.dot x x < 0)
    (hy : Minkowski.dot y y < 0) (hx0 : 0 < x 0) (hy0 : 0 < y 0) : Minkowski.dot x y < 0 := by
  rw [Minkowski.dot_eq] at hx hy ⊢
  have hcs := spatial_cauchySchwarz x y
  set s := x 1 * y 1 + x 2 * y 2 + x 3 * y 3
  set a := x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2
  set b := y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have ha' : a < x 0 ^ 2 := by simp only [a]; nlinarith
  have hb' : b < y 0 ^ 2 := by simp only [b]; nlinarith
  have hab : a * b < (x 0 * y 0) ^ 2 := by
    rw [mul_pow]
    calc a * b ≤ a * y 0 ^ 2 := mul_le_mul_of_nonneg_left hb'.le ha
      _ < x 0 ^ 2 * y 0 ^ 2 := mul_lt_mul_of_pos_right ha' (by positivity)
  have hxy : 0 < x 0 * y 0 := mul_pos hx0 hy0
  have hs : s < x 0 * y 0 := by
    by_contra! hc
    nlinarith
  have e : -(x 0 * y 0) + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 = s - x 0 * y 0 := by
    simp only [s]; ring
  rw [e]
  linarith

/-- A timelike vector with negative product against a future timelike vector is future. -/
theorem pos_of_dot_neg {x y : Fin 4 → ℝ} (hx : Minkowski.dot x x < 0)
    (hy : Minkowski.dot y y < 0) (hy0 : 0 < y 0) (hxy : Minkowski.dot x y < 0) : 0 < x 0 := by
  by_contra! hc
  rcases hc.lt_or_eq with hlt | heq
  · have hnx : Minkowski.dot (-x) (-x) < 0 := by
      rw [Minkowski.dot_eq] at hx ⊢
      simp only [Pi.neg_apply]
      linarith
    have := dot_neg_of_timelike hnx hy (by simp only [Pi.neg_apply]; linarith) hy0
    rw [Minkowski.dot_eq] at this hxy
    simp only [Pi.neg_apply] at this
    linarith
  · rw [Minkowski.dot_eq, heq] at hx
    nlinarith [sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]

/-- A nonzero vector orthogonal to a timelike vector is spacelike. -/
theorem dot_self_pos_of_dot_eq_zero {w k : Fin 4 → ℝ} (hk : Minkowski.dot k k < 0)
    (hwk : Minkowski.dot w k = 0) (hw : w ≠ 0) : 0 < Minkowski.dot w w := by
  rw [Minkowski.dot_eq] at hk hwk ⊢
  have hcs := spatial_cauchySchwarz w k
  set s := w 1 * k 1 + w 2 * k 2 + w 3 * k 3 with hs
  set a := w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 with ha
  set b := k 1 ^ 2 + k 2 ^ 2 + k 3 ^ 2 with hb
  have hb' : b < k 0 ^ 2 := by simp only [b]; nlinarith
  have hs0 : s = w 0 * k 0 := by simp only [s]; linarith
  have ha0 : 0 < a := by
    rcases (show (0 : ℝ) ≤ a by positivity).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 : w 1 = 0 := by nlinarith [sq_nonneg (w 1), sq_nonneg (w 2), sq_nonneg (w 3)]
      have h2 : w 2 = 0 := by nlinarith [sq_nonneg (w 1), sq_nonneg (w 2), sq_nonneg (w 3)]
      have h3 : w 3 = 0 := by nlinarith [sq_nonneg (w 1), sq_nonneg (w 2), sq_nonneg (w 3)]
      have hk0 : k 0 ≠ 0 := by
        intro h0
        rw [h0] at hb'
        nlinarith [sq_nonneg (k 1), sq_nonneg (k 2), sq_nonneg (k 3)]
      have hs' : s = 0 := by simp only [s, h1, h2, h3]; ring
      have h0 : w 0 = 0 := by
        rw [hs'] at hs0
        rcases mul_eq_zero.mp hs0.symm with h | h
        · exact h
        · exact absurd h hk0
      apply hw
      funext i
      fin_cases i <;> simp [h0, h1, h2, h3]
  -- `(w·w) k₀² = a k₀² - s² ≥ a (k₀² - b) > 0`
  have key : (-(w 0 * w 0) + w 1 * w 1 + w 2 * w 2 + w 3 * w 3) * k 0 ^ 2 > 0 := by
    have e : (-(w 0 * w 0) + w 1 * w 1 + w 2 * w 2 + w 3 * w 3) * k 0 ^ 2 =
        a * k 0 ^ 2 - s ^ 2 := by
      rw [hs0]; simp only [a]; ring
    rw [e]
    have : a * b < a * k 0 ^ 2 := mul_lt_mul_of_pos_left hb' ha0
    linarith
  have hk2 : 0 < k 0 ^ 2 := lt_of_le_of_lt (by positivity) hb'
  by_contra! hc
  nlinarith

/-! ### Reflections between on-shell vectors -/

/-- The reflection in `a = u - v` maps `u` to `v` when `u·u = v·v`. -/
theorem reflect_sub_self {u v : Fin 4 → ℝ} (huv : Minkowski.dot u u = Minkowski.dot v v)
    (ha : Minkowski.dot (u - v) (u - v) ≠ 0) : reflect (u - v) u = v := by
  have h1 : Minkowski.dot (u - v) (u - v) = 2 * Minkowski.dot (u - v) u := by
    simp only [Minkowski.dot_eq, Pi.sub_apply] at huv ⊢
    linear_combination (-1 : ℝ) * huv
  have h2 : 2 * Minkowski.dot (u - v) u / Minkowski.dot (u - v) (u - v) = 1 := by
    rw [h1] at ha ⊢
    exact div_self ha
  unfold reflect
  rw [h2, one_smul, sub_sub_cancel]

/-- The reflection in `a` fixes vectors orthogonal to `a`. -/
theorem reflect_of_dot_eq_zero {a u : Fin 4 → ℝ} (hau : Minkowski.dot a u = 0) :
    reflect a u = u := by
  unfold reflect
  rw [hau, mul_zero, zero_div, zero_smul, sub_zero]

/-! ### One reflection step -/

section Step

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁)
  (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
  (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
include hm hmγ hΛ hM₁ hM₂ hc₁ hc₂

/-- **One reflection step.** If the reflection `R_a` (`a·a ≠ 0`) maps the on-shell
positive-energy pair `(p', p)` with `q² ≥ 0` to the positive-energy pair `(r', r)`, the Pauli
projections of the vertex limits at the two pairs agree. -/
theorem formFactorProj₂_eq_of_reflect {a p' p r' r : Fin 4 → ℝ}
    (ha : Minkowski.dot a a ≠ 0) (hr : reflect a p = r) (hr' : reflect a p' = r')
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hr0 : 0 < r 0) (hr0' : 0 < r' 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsVertexOrderFiveLimit P p' p V) (hW : IsVertexOrderFiveLimit P r' r W) (e : ℝ) :
    QED.OneLoop.formFactorProj₂ e P.m r' r W = QED.OneLoop.formFactorProj₂ e P.m p' p V := by
  have hLp : reflectMatrix a *ᵥ p = r := by rw [reflectMatrix_mulVec, hr]
  have hLp' : reflectMatrix a *ᵥ p' = r' := by rw [reflectMatrix_mulVec, hr']
  rw [← hLp, ← hLp'] at hW ⊢
  exact formFactorProj₂_vertexLimit_map P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ (isSpinLift_reflect ha) hp
    hp' hp0 hp0' (hLp ▸ hr0) (hLp' ▸ hr0') hq hV hW e

end Step

/-! ### Two pairs with the same `q²` -/

/-- On shell, `q² = -2m² - 2 p'·p`. -/
theorem dot_sub_eq_of_onShell {m : ℝ} {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) :
    Minkowski.dot (p' - p) (p' - p) = -2 * m ^ 2 - 2 * Minkowski.dot p' p := by
  have e : Minkowski.dot (p' - p) (p' - p) =
      Minkowski.dot p' p' - 2 * Minkowski.dot p' p + Minkowski.dot p p := by
    simp only [Minkowski.dot_eq, Pi.sub_apply]; ring
  rw [e, hp', hp]; ring

/-- **The Pauli projection of the vertex limit depends on the pair only through `p'·p`.** For
`m, m_γ, Λ > 0`, `M₁, M₂ ≥ m` with the Pauli–Villars conditions, any counterterms, two on-shell
positive-energy pairs `(p', p)`, `(k', k)` with `k'·k = p'·p` and `q² ≥ 0`, and the `ε → 0⁺`
limits `V`, `W₁` of the order-`e⁵` vertex at them: `P₂(k', k; W₁) = P₂(p', p; V)`. -/
theorem formFactorProj₂_eq_of_dot_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p k' k : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hpt : Minkowski.dot k k = -P.m ^ 2)
    (hpt' : Minkowski.dot k' k' = -P.m ^ 2) (hpt0 : 0 < k 0) (hpt0' : 0 < k' 0)
    (hdot : Minkowski.dot k' k = Minkowski.dot p' p)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {V W₁ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsVertexOrderFiveLimit P p' p V) (hW₁ : IsVertexOrderFiveLimit P k' k W₁) (e : ℝ) :
    QED.OneLoop.formFactorProj₂ e P.m k' k W₁ = QED.OneLoop.formFactorProj₂ e P.m p' p V := by
  have hm2 : Minkowski.dot p p < 0 := by rw [hp]; nlinarith
  have hmt2 : Minkowski.dot k k < 0 := by rw [hpt]; nlinarith
  have hm2' : Minkowski.dot p' p' < 0 := by rw [hp']; nlinarith
  -- Step 1: move `p` to `k`.
  obtain ⟨p'', hp'', hp0'', hdot'', hstep₁⟩ : ∃ p'' : Fin 4 → ℝ,
      Minkowski.dot p'' p'' = -P.m ^ 2 ∧ 0 < p'' 0 ∧ Minkowski.dot p'' k = Minkowski.dot p' p ∧
      ∀ W, IsVertexOrderFiveLimit P p'' k W →
        QED.OneLoop.formFactorProj₂ e P.m p'' k W = QED.OneLoop.formFactorProj₂ e P.m p' p V := by
    by_cases hpp : p = k
    · subst hpp
      exact ⟨p', hp', hp0', rfl, fun W hW => by
        rw [VertexLimit.isVertexOrderFiveLimit_unique hW hV]⟩
    · set a := p - k with ha_def
      have hk : Minkowski.dot (p + k) (p + k) < 0 := by
        have e1 : Minkowski.dot (p + k) (p + k) =
            Minkowski.dot p p + 2 * Minkowski.dot p k + Minkowski.dot k k := by
          simp only [Minkowski.dot_eq, Pi.add_apply]; ring
        rw [e1]
        have := dot_neg_of_timelike hm2 hmt2 hp0 hpt0
        linarith
      have hak : Minkowski.dot a (p + k) = 0 := by
        have e1 : Minkowski.dot a (p + k) = Minkowski.dot p p - Minkowski.dot k k := by
          simp only [a, Minkowski.dot_eq, Pi.add_apply, Pi.sub_apply]; ring
        rw [e1, hp, hpt, sub_self]
      have ha0 : a ≠ 0 := fun h => hpp (sub_eq_zero.mp h)
      have haa : 0 < Minkowski.dot a a := dot_self_pos_of_dot_eq_zero hk hak ha0
      have hr : reflect a p = k := reflect_sub_self (by rw [hp, hpt]) haa.ne'
      set p'' := reflect a p' with hp''_def
      have hp''2 : Minkowski.dot p'' p'' = -P.m ^ 2 := by rw [dot_reflect haa.ne', hp']
      have hd : Minkowski.dot p'' k = Minkowski.dot p' p := by
        rw [← hr, dot_reflect haa.ne']
      have hp''0 : 0 < p'' 0 := by
        refine pos_of_dot_neg (by rw [hp''2]; nlinarith) hmt2 hpt0 ?_
        rw [hd]
        exact dot_neg_of_timelike hm2' hm2 hp0' hp0
      exact ⟨p'', hp''2, hp''0, hd, fun W hW =>
        formFactorProj₂_eq_of_reflect P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ haa.ne' hr rfl hp hp' hp0
          hp0' hpt0 hp''0 hq hV hW e⟩
  -- Step 2: move `p''` to `k'`, fixing `k`.
  have hk'' : 0 ≤ Minkowski.dot (p'' - k) (p'' - k) := by
    rw [dot_sub_eq_of_onShell hp'' hpt, hdot'', ← dot_sub_eq_of_onShell hp' hp]
    exact hq
  obtain ⟨W, hW⟩ := VertexLimit.exists_isVertexOrderFiveLimit P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hpt
    hp'' hpt0 hp0'' hk''
  rw [← hstep₁ W hW]
  by_cases hpp : p'' = k'
  · subst hpp
    rw [VertexLimit.isVertexOrderFiveLimit_unique hW₁ hW]
  · set a := p'' - k' with ha_def
    have hak : Minkowski.dot a k = 0 := by
      have e1 : Minkowski.dot a k = Minkowski.dot p'' k - Minkowski.dot k' k := by
        simp only [a, Minkowski.dot_eq, Pi.sub_apply]; ring
      rw [e1, hdot'', hdot, sub_self]
    have ha0 : a ≠ 0 := fun h => hpp (sub_eq_zero.mp h)
    have haa : 0 < Minkowski.dot a a := dot_self_pos_of_dot_eq_zero hmt2 hak ha0
    exact formFactorProj₂_eq_of_reflect P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ haa.ne'
      (reflect_of_dot_eq_zero hak) (reflect_sub_self (by rw [hp'', hpt']) haa.ne') hpt hp''
      hpt0 hp0'' hpt0 hpt0' hk'' hW hW₁ e

/-- **The same with `q²`**: pairs with equal `q²` have equal Pauli projections. -/
theorem formFactorProj₂_eq_of_dot_sub_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p' p k' k : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0)
    (hp0' : 0 < p' 0) (hpt : Minkowski.dot k k = -P.m ^ 2)
    (hpt' : Minkowski.dot k' k' = -P.m ^ 2) (hpt0 : 0 < k 0) (hpt0' : 0 < k' 0)
    (hqq : Minkowski.dot (k' - k) (k' - k) = Minkowski.dot (p' - p) (p' - p))
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) {V W₁ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsVertexOrderFiveLimit P p' p V) (hW₁ : IsVertexOrderFiveLimit P k' k W₁) (e : ℝ) :
    QED.OneLoop.formFactorProj₂ e P.m k' k W₁ = QED.OneLoop.formFactorProj₂ e P.m p' p V := by
  refine formFactorProj₂_eq_of_dot_eq P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0' hpt hpt' hpt0
    hpt0' ?_ hq hV hW₁ e
  rw [dot_sub_eq_of_onShell hpt' hpt, dot_sub_eq_of_onShell hp' hp] at hqq
  linarith

/-- **The Pauli component of the form-factor pairs depends on the pair only through `q²`.** For
`e ≠ 0` and the hypotheses of `formFactorProj₂_eq_of_dot_sub_eq` with `q² > 0`, form-factor pairs
`F` of `V` at `(p', p)` and `G` of `W₁` at `(k', k)` have `G₂ = F₂`. -/
theorem snd_eq_of_isFormFactorPair_of_dot_sub_eq (P : Params) (he : P.e ≠ 0) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {p' p k' k : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp0 : 0 < p 0) (hp0' : 0 < p' 0)
    (hpt : Minkowski.dot k k = -P.m ^ 2) (hpt' : Minkowski.dot k' k' = -P.m ^ 2)
    (hpt0 : 0 < k 0) (hpt0' : 0 < k' 0)
    (hqq : Minkowski.dot (k' - k) (k' - k) = Minkowski.dot (p' - p) (p' - p))
    (hq : 0 < Minkowski.dot (p' - p) (p' - p)) {V W₁ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hV : IsVertexOrderFiveLimit P p' p V) (hW₁ : IsVertexOrderFiveLimit P k' k W₁)
    {F G : ℂ × ℂ} (hF : QED.OneLoop.IsFormFactorPair P.e P.m p' p V F)
    (hG : QED.OneLoop.IsFormFactorPair P.e P.m k' k W₁ G) : G.2 = F.2 := by
  rw [QED.OneLoop.eq_formFactorProj_of_isFormFactorPair he hm.ne' hpt' hpt (hqq ▸ hq) hG,
    QED.OneLoop.eq_formFactorProj_of_isFormFactorPair he hm.ne' hp' hp hq hF]
  exact formFactorProj₂_eq_of_dot_sub_eq P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hp hp' hp0 hp0' hpt hpt' hpt0
    hpt0' hqq hq.le hV hW₁ P.e

end QED.TwoLoop.PauliZero

end
