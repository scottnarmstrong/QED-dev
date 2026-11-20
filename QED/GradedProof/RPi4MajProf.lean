/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajGrow

/-!
# (R-Π₄) step L10: global bounds on a profile from its halving identity

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. A profile `g`
of the scaling form of the decoupling (step L9), recorded at the configuration `x = 4`, obeys
`2(g(s) - g(s/2)) - (g(s/2) - g(s/4)) = v(s)` (`decR g 4 s = v s`). Model-free:

* `maj_profile_bounds`: if `g(0) = 0`, `g` is `L`-Lipschitz on `[-δ, δ]`, and the source `v` is
  bounded by `A ω(s)` and on the scale of `s` by `A ω(s) (1 - r)/r` (`ω` monotone, `≥ 1`), then
  `‖g(s)‖ ≤ K ω(s) w(s)` and `‖g(s) - g(rs)‖ ≤ K ω(s) w(s) (1 - r)/r`, `K = Lδ + C_δ A`:
  halving (`maj_norm_le_of_halving`) then telescoping (`maj_norm_le_of_telescope`), applied to
  `g` and to `s ↦ g(s) - g(rs)`;
* `maj_le_min_form`: a bound `q ≤ Φ₀ w(τ) X` together with `q ≤ L τ X` for `τ ≤ δ` gives
  `q ≤ (L + Φ₀ + Φ₀/δ) min(τ, 1) w(τ) X`.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

section Profile

variable {g v : ℝ → ℂ} {ω : ℝ → ℝ} {δ L A : ℝ}

/-- The increments of a profile `L`-Lipschitz on `[-δ, δ]` are `O(s)` there. -/
theorem maj_norm_incr_le (hgL : ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖g t - g t'‖ ≤ L * |t - t'|)
    (hL : 0 ≤ L) {s : ℝ} (hs : 0 ≤ s) (hsδ : s ≤ δ) : ‖g s - g (s / 2)‖ ≤ L * s := by
  have h1 : |s| ≤ δ := by rw [abs_of_nonneg hs]; exact hsδ
  have h2 : |s / 2| ≤ δ := by rw [abs_of_nonneg (by positivity)]; linarith
  refine (hgL _ _ h1 h2).trans ?_
  rw [show s - s / 2 = s / 2 by ring, abs_of_nonneg (by positivity)]
  nlinarith

variable (hδ : 0 < δ) (hL : 0 ≤ L) (hg0 : g 0 = 0)
  (hgL : ∀ t t' : ℝ, |t| ≤ δ → |t'| ≤ δ → ‖g t - g t'‖ ≤ L * |t - t'|)
  (hgv : ∀ s, 0 ≤ s → 2 * (g s - g (s / 2)) - (g (s / 2) - g (s / 2 / 2)) = v s)
  (hω : ∀ s t, 0 ≤ s → s ≤ t → ω s ≤ ω t) (hω1 : ∀ s, 0 ≤ s → 1 ≤ ω s) (hA : 0 ≤ A)
  (hv : ∀ s, 0 ≤ s → ‖v s‖ ≤ A * ω s)
  (hvr : ∀ s r, 0 ≤ s → 0 < r → r ≤ 1 → ‖v s - v (r * s)‖ ≤ A * ω s * ((1 - r) / r))

include hδ hL hg0 hgL hgv hω hω1 hA hv in
/-- **Growth of a profile** from its halving identity: `‖g(s)‖ ≤ (Lδ + C_δ A) ω(s) w(s)`. -/
theorem maj_profile_norm_le {s : ℝ} (hs : 0 ≤ s) :
    ‖g s‖ ≤ (L * δ + majC δ * A) * ω s * majW s := by
  have ha : ∀ s, 0 ≤ s → ‖g s - g (s / 2)‖ ≤ A * ω s := fun s hs =>
    maj_norm_le_of_halving (u := fun s => g s - g (s / 2)) (K := L) hδ hgv hv
      (fun s t hs hst => mul_le_mul_of_nonneg_left (hω s t hs hst) hA)
      (fun s hs hsδ => maj_norm_incr_le hgL hL hs hsδ) hs
  have h := maj_norm_le_of_telescope (u := g) (a := fun s => g s - g (s / 2)) (K₀ := L * δ) hδ
    (fun s _ => rfl) ha (fun s t hs hst => mul_le_mul_of_nonneg_left (hω s t hs hst) hA)
    (fun s hs hsδ => by
      have h1 : |s| ≤ δ := by rw [abs_of_nonneg hs]; exact hsδ
      have := hgL s 0 h1 (by simpa using hδ.le)
      rw [hg0, sub_zero, sub_zero, abs_of_nonneg hs] at this
      nlinarith) hs
  have hw := maj_one_le_majW hs
  have hω' := hω1 s hs
  have hC := majC_nonneg hδ
  have h1 : L * δ ≤ L * δ * (ω s * majW s) := by
    have : 1 ≤ ω s * majW s := by nlinarith
    nlinarith [mul_nonneg hL hδ.le]
  calc ‖g s‖ ≤ L * δ + majC δ * majW s * (A * ω s) := h
    _ ≤ L * δ * (ω s * majW s) + majC δ * majW s * (A * ω s) := by linarith
    _ = _ := by ring

include hδ hL hgL hgv hω hω1 hA hvr in
/-- **Scale-Lipschitz growth of a profile**: `‖g(s) - g(rs)‖ ≤ (Lδ + C_δ A) ω(s) w(s) (1-r)/r`
for `0 < r ≤ 1`. -/
theorem maj_profile_norm_sub_le {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖g s - g (r * s)‖ ≤ (L * δ + majC δ * A) * ω s * majW s * ((1 - r) / r) := by
  have hq : 0 ≤ (1 - r) / r := div_nonneg (by linarith) hr.le
  have hmono : ∀ s t, 0 ≤ s → s ≤ t → A * ω s * ((1 - r) / r) ≤ A * ω t * ((1 - r) / r) :=
    fun s t hs hst => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hω s t hs hst) hA)
      hq
  have hrs : ∀ s, r * (s / 2) = r * s / 2 := fun s => by ring
  -- halving for the increments at ratio `r`
  have ha : ∀ s, 0 ≤ s → ‖(g s - g (s / 2)) - (g (r * s) - g (r * s / 2))‖ ≤
      A * ω s * ((1 - r) / r) := fun s hs =>
    maj_norm_le_of_halving (u := fun s => (g s - g (s / 2)) - (g (r * s) - g (r * s / 2)))
      (v := fun s => v s - v (r * s)) (K := 2 * L) hδ
      (fun s hs => by
        have h1 := hgv s hs
        have h2 := hgv (r * s) (by positivity)
        rw [← h1, ← h2, hrs]
        ring_nf)
      (fun s hs => hvr s r hs hr hr1) hmono
      (fun s hs hsδ => by
        have hrs0 : 0 ≤ r * s := by positivity
        have hrsδ : r * s ≤ δ := by nlinarith
        have h1 := maj_norm_incr_le hgL hL hs hsδ
        have h2 := maj_norm_incr_le hgL hL hrs0 hrsδ
        calc _ ≤ ‖g s - g (s / 2)‖ + ‖g (r * s) - g (r * s / 2)‖ := norm_sub_le _ _
          _ ≤ L * s + L * (r * s) := add_le_add h1 h2
          _ ≤ 2 * L * s := by nlinarith [mul_nonneg hL hs]) hs
  have h := maj_norm_le_of_telescope (u := fun s => g s - g (r * s))
    (a := fun s => (g s - g (s / 2)) - (g (r * s) - g (r * s / 2)))
    (K₀ := L * δ * ((1 - r) / r)) hδ
    (fun s _ => by simp only [hrs]; ring) ha hmono
    (fun s hs hsδ => by
      have h1 : |s| ≤ δ := by rw [abs_of_nonneg hs]; exact hsδ
      have h2 : |r * s| ≤ δ := by rw [abs_of_nonneg (by positivity)]; nlinarith
      refine (hgL _ _ h1 h2).trans ?_
      rw [show s - r * s = (1 - r) * s by ring, abs_of_nonneg (by nlinarith)]
      have : (1 - r) ≤ (1 - r) / r := by
        rw [le_div_iff₀ hr]
        nlinarith
      calc L * ((1 - r) * s) ≤ L * ((1 - r) * δ) := by gcongr
        _ ≤ L * (((1 - r) / r) * δ) := by gcongr
        _ = _ := by ring) hs
  have hw := maj_one_le_majW hs
  have hω' := hω1 s hs
  have hC := majC_nonneg hδ
  have h1 : L * δ * ((1 - r) / r) ≤ L * δ * ((1 - r) / r) * (ω s * majW s) := by
    have : 1 ≤ ω s * majW s := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hL hδ.le) hq]
  calc ‖g s - g (r * s)‖ ≤ L * δ * ((1 - r) / r) + majC δ * majW s * (A * ω s * ((1 - r) / r)) :=
        h
    _ ≤ L * δ * ((1 - r) / r) * (ω s * majW s) +
        majC δ * majW s * (A * ω s * ((1 - r) / r)) := by linarith
    _ = _ := by ring

end Profile

/-- **The `min(τ, 1)` form**: `q ≤ Φ₀ w(τ) X` and `q ≤ L τ X` for `τ ≤ δ` give
`q ≤ (L + Φ₀ + Φ₀/δ) min(τ, 1) w(τ) X`. -/
theorem maj_le_min_form {q τ Φ₀ L δ X : ℝ} (hτ : 0 ≤ τ) (hδ : 0 < δ) (hL : 0 ≤ L) (hΦ : 0 ≤ Φ₀)
    (hX : 0 ≤ X) (h1 : q ≤ Φ₀ * majW τ * X) (h2 : τ ≤ δ → q ≤ L * τ * X) :
    q ≤ (L + Φ₀ + Φ₀ / δ) * min τ 1 * majW τ * X := by
  have hw := maj_one_le_majW hτ
  have hΦδ : 0 ≤ Φ₀ / δ := div_nonneg hΦ hδ.le
  rcases le_or_gt 1 τ with h | h
  · rw [min_eq_right h]
    have : Φ₀ * majW τ * X ≤ (L + Φ₀ + Φ₀ / δ) * 1 * majW τ * X := by
      have := mul_nonneg (mul_nonneg (add_nonneg hL hΦδ) (by linarith : (0 : ℝ) ≤ majW τ)) hX
      nlinarith
    linarith
  · rw [min_eq_left h.le]
    rcases le_or_gt τ δ with hτδ | hτδ
    · have h3 := h2 hτδ
      have : L * τ * X ≤ (L + Φ₀ + Φ₀ / δ) * τ * majW τ * X := by
        have e1 : 0 ≤ (Φ₀ + Φ₀ / δ) * τ * majW τ * X := by positivity
        have e2 : L * τ * X ≤ L * τ * majW τ * X := by
          have := mul_nonneg (mul_nonneg hL hτ) hX
          nlinarith
        nlinarith
      linarith
    · have hq : 1 ≤ τ / δ := by rw [le_div_iff₀ hδ]; linarith
      have e : Φ₀ * majW τ * X ≤ Φ₀ / δ * τ * majW τ * X := by
        have : Φ₀ / δ * τ = Φ₀ * (τ / δ) := by ring
        rw [this]
        have := mul_nonneg (mul_nonneg hΦ (by linarith : (0 : ℝ) ≤ majW τ)) hX
        nlinarith
      have e1 : 0 ≤ (L + Φ₀) * τ * majW τ * X := by positivity
      nlinarith

end QED.GradedProof.RPi4

end
