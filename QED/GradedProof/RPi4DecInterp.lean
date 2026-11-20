/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Dyadic

/-!
# (R-Π₄) step L9: Lipschitz bounds from a sup bound and a second-difference bound

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (Lipschitz bounds
near `s = 0`). An interpolation inequality: a function `f` with `‖f‖ ≤ A` on `[-2δ, 2δ]` and
second differences `‖f(s + 2h) - 2 f(s + h) + f(s)‖ ≤ B h²` is Lipschitz on `[-δ, δ]` with
constant `4A/ρ + Bρ` for every `0 < ρ ≤ δ` (so `≈ √(AB)` when `A` is small). With `A` decaying in
the photon pair and `B` bounded, this turns value bounds at comparable photon pairs into
decaying Lipschitz bounds, with no rate for the `s`-derivative.

* `dec_norm_step_sub_le`, `dec_norm_tele_sub_le`: telescoping along an arithmetic progression;
* **`dec_norm_sub_le_of_twoDiff`**: the interpolation inequality;
* `dec_inv_rpow_le`: `1 / min δ x ≤ 1 / δ + 1 / x`;
* **`dec_norm_le_of_comparable_heavy`**: the dyadic lemma for heavy pairs (`b ≥ 1`, bound
  `C b⁻ᵖ` at comparable pairs), by inversion from
  `QED.GradedProof.RPi4.norm_le_of_comparable_rpow`.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

section Interp

variable {f : ℝ → ℂ} {s d B : ℝ} {n : ℕ}

/-- The steps along `s + k d` deviate from the first step by at most `k B d²`. -/
theorem dec_norm_step_sub_le
    (h2 : ∀ k : ℕ, k + 2 ≤ n → ‖f (s + ((k : ℝ) + 2) * d) - 2 * f (s + ((k : ℝ) + 1) * d) +
      f (s + (k : ℝ) * d)‖ ≤ B * d ^ 2) :
    ∀ m : ℕ, m + 1 ≤ n → ‖f (s + ((m : ℝ) + 1) * d) - f (s + (m : ℝ) * d) -
      (f (s + d) - f s)‖ ≤ (m : ℝ) * B * d ^ 2 := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h := h2 m (by omega)
    have e : f (s + (((m + 1 : ℕ) : ℝ) + 1) * d) - f (s + ((m + 1 : ℕ) : ℝ) * d) -
        (f (s + d) - f s) = (f (s + ((m : ℝ) + 1) * d) - f (s + (m : ℝ) * d) -
        (f (s + d) - f s)) + (f (s + ((m : ℝ) + 2) * d) - 2 * f (s + ((m : ℝ) + 1) * d) +
        f (s + (m : ℝ) * d)) := by
      push_cast
      ring_nf
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := ih (by omega)
    push_cast
    linarith

/-- **Telescoping**: `‖f(s + m d) - f(s) - m (f(s + d) - f(s))‖ ≤ (m (m - 1)/2) B d²`. -/
theorem dec_norm_tele_sub_le
    (h2 : ∀ k : ℕ, k + 2 ≤ n → ‖f (s + ((k : ℝ) + 2) * d) - 2 * f (s + ((k : ℝ) + 1) * d) +
      f (s + (k : ℝ) * d)‖ ≤ B * d ^ 2) :
    ∀ m : ℕ, m ≤ n → ‖f (s + (m : ℝ) * d) - f s - (m : ℂ) * (f (s + d) - f s)‖ ≤
      (m : ℝ) * ((m : ℝ) - 1) / 2 * B * d ^ 2 := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hs := dec_norm_step_sub_le h2 m hm
    have e : f (s + ((m + 1 : ℕ) : ℝ) * d) - f s - ((m + 1 : ℕ) : ℂ) * (f (s + d) - f s) =
        (f (s + (m : ℝ) * d) - f s - (m : ℂ) * (f (s + d) - f s)) +
        (f (s + ((m : ℝ) + 1) * d) - f (s + (m : ℝ) * d) - (f (s + d) - f s)) := by
      push_cast
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := ih (by omega)
    push_cast
    nlinarith

/-- **The interpolation inequality.** If `‖f‖ ≤ A` on `[-2δ, 2δ]` and the second differences of
`f` there are at most `B h²`, then `‖f s' - f s‖ ≤ (4A/ρ + Bρ) |s' - s|` on `[-δ, δ]`, for every
`0 < ρ ≤ δ`. -/
theorem dec_norm_sub_le_of_twoDiff {δ A ρ : ℝ} (hρ : 0 < ρ) (hρδ : ρ ≤ δ) (hB : 0 ≤ B)
    (hA : ∀ r : ℝ, |r| ≤ 2 * δ → ‖f r‖ ≤ A)
    (h2 : ∀ r h : ℝ, |r| ≤ 2 * δ → |r + 2 * h| ≤ 2 * δ →
      ‖f (r + 2 * h) - 2 * f (r + h) + f r‖ ≤ B * h ^ 2)
    {s s' : ℝ} (hs : |s| ≤ δ) (hs' : |s'| ≤ δ) :
    ‖f s' - f s‖ ≤ (4 * A / ρ + B * ρ) * |s' - s| := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (by rw [abs_zero]; linarith [hρ.trans_le hρδ]))
  set d := s' - s with hd
  have hs's : s' = s + d := by rw [hd]; ring
  have hfs : ‖f s‖ ≤ A := hA s (by linarith [hρ.trans_le hρδ])
  have hfs' : ‖f s'‖ ≤ A := hA s' (by linarith [hρ.trans_le hρδ])
  have h2A : ‖f s' - f s‖ ≤ 2 * A := (norm_sub_le _ _).trans (by linarith)
  have hBρ : 0 ≤ B * ρ := mul_nonneg hB hρ.le
  rcases lt_or_ge ρ |d| with hlt | hle
  · -- a long step: the sup bound suffices
    refine h2A.trans ?_
    have h1 : 2 * A ≤ 4 * A / ρ * |d| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hρ]
      nlinarith
    nlinarith [abs_nonneg d]
  -- a short step: telescope over `m = ⌊ρ/|d|⌋` steps
  rcases eq_or_lt_of_le (abs_nonneg d) with h0 | hd0
  · have : d = 0 := abs_eq_zero.1 h0.symm
    rw [hs's, this, add_zero, sub_self, norm_zero]
    exact mul_nonneg (add_nonneg (by positivity) hBρ) (abs_nonneg _)
  set x : ℝ := ρ / |d|
  have hx1 : 1 ≤ x := by rw [le_div_iff₀ hd0]; linarith
  set m : ℕ := ⌊x⌋₊
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.one_le_floor_iff x).2 hx1
  have hmx : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxm : x < m + 1 := Nat.lt_floor_add_one x
  have hmd : (m : ℝ) * |d| ≤ ρ := by
    have := mul_le_mul_of_nonneg_right hmx hd0.le
    rwa [div_mul_cancel₀ _ hd0.ne'] at this
  have hρmd : ρ ≤ 2 * (m : ℝ) * |d| := by
    have h := mul_le_mul_of_nonneg_right (by linarith : x ≤ 2 * m) hd0.le
    rwa [div_mul_cancel₀ _ hd0.ne'] at h
  -- the points `s + k d`, `k ≤ m`, stay in `[-2δ, 2δ]`
  have hpt : ∀ k : ℝ, 0 ≤ k → k ≤ m → |s + k * d| ≤ 2 * δ := fun k hk0 hkm => by
    have : |k * d| ≤ ρ := by
      rw [abs_mul, abs_of_nonneg hk0]
      exact (mul_le_mul_of_nonneg_right hkm hd0.le).trans hmd
    have := abs_add_le s (k * d)
    linarith
  have htele := dec_norm_tele_sub_le (f := f) (s := s) (d := d) (B := B) (n := m)
    (fun k hk => by
      have hk' : ((k : ℝ) + 2) ≤ m := by exact_mod_cast hk
      have e1 : s + ((k : ℝ) + 2) * d = s + (k : ℝ) * d + 2 * d := by ring
      have e2 : s + ((k : ℝ) + 1) * d = s + (k : ℝ) * d + d := by ring
      rw [e1, e2]
      exact h2 _ d (hpt k (Nat.cast_nonneg k) (by linarith))
        (by rw [← e1]; exact hpt _ (by positivity) hk'))
    m le_rfl
  rw [← hs's] at htele
  have hfm : ‖f (s + (m : ℝ) * d)‖ ≤ A := hA _ (hpt m (Nat.cast_nonneg m) le_rfl)
  -- `m ‖D‖ ≤ 2A + (m²/2) B d²`
  have hmD : (m : ℝ) * ‖f s' - f s‖ ≤ 2 * A + (m : ℝ) * ((m : ℝ) - 1) / 2 * B * d ^ 2 := by
    have e : (m : ℂ) * (f s' - f s) = (f (s + (m : ℝ) * d) - f s) -
        (f (s + (m : ℝ) * d) - f s - (m : ℂ) * (f s' - f s)) := by ring
    have hn : ‖(m : ℂ) * (f s' - f s)‖ = (m : ℝ) * ‖f s' - f s‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [← hn, e]
    refine (norm_sub_le _ _).trans ?_
    have := norm_sub_le (f (s + (m : ℝ) * d)) (f s)
    linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hd2 : d ^ 2 = |d| * |d| := by rw [← sq_abs, sq]
  -- divide by `m`
  have key : ‖f s' - f s‖ ≤ 2 * A / m + ((m : ℝ) * |d|) * B * |d| / 2 := by
    rw [div_add_div _ _ hm0.ne' (two_ne_zero), le_div_iff₀ (by positivity)]
    rw [hd2] at hmD
    nlinarith [norm_nonneg (f s' - f s), mul_nonneg hB (mul_nonneg hd0.le hd0.le)]
  refine key.trans ?_
  have t1 : 2 * A / m ≤ 4 * A / ρ * |d| := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hm0 hρ]
    nlinarith
  have t2 : ((m : ℝ) * |d|) * B * |d| / 2 ≤ B * ρ * |d| := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmd hB) hd0.le
    nlinarith [mul_nonneg hBρ hd0.le]
  linarith

end Interp

/-- `1 / min δ x ≤ 1 / δ + 1 / x` for positive `δ`, `x`. -/
theorem dec_inv_min_le {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) :
    1 / min δ x ≤ 1 / δ + 1 / x := by
  rcases min_cases δ x with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · have : 0 ≤ 1 / x := by positivity
    linarith
  · have : 0 ≤ 1 / δ := by positivity
    linarith

/-- **The dyadic lemma for heavy pairs**: additivity for `1 ≤ a ≤ b ≤ d` and `‖Q a b‖ ≤ C a⁻ᵖ`
at comparable pairs `1 ≤ a ≤ b ≤ 2a` give `‖Q a b‖ ≤ C / (1 - 2⁻ᵖ)` for all `1 ≤ a ≤ b`. -/
theorem dec_norm_le_of_comparable_heavy {Q : ℝ → ℝ → ℂ} {C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p)
    (hadd : ∀ a b d, 1 ≤ a → a ≤ b → b ≤ d → Q a d = Q a b + Q b d)
    (hcomp : ∀ a b, 1 ≤ a → a ≤ b → b ≤ 2 * a → ‖Q a b‖ ≤ C * a ^ (-p)) :
    ∀ a b, 1 ≤ a → a ≤ b → ‖Q a b‖ ≤ C / (1 - (2 : ℝ) ^ (-p)) := by
  have hρ1 : (2 : ℝ) ^ (-p) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h := norm_le_of_comparable_rpow (Q := fun a b => Q b⁻¹ a⁻¹) (r₀ := 1) hC hp
    (fun a b d ha hab hbd hd1 => by
      have hb : 0 < b := ha.trans_le hab
      have hd : 0 < d := hb.trans_le hbd
      exact hadd d⁻¹ b⁻¹ a⁻¹ (one_le_inv₀ hd |>.2 hd1) (inv_anti₀ hb hbd)
        (inv_anti₀ ha hab) |>.trans (add_comm _ _))
    (fun a b ha hab hb2 hb1 => by
      have hb : 0 < b := ha.trans_le hab
      refine (hcomp b⁻¹ a⁻¹ ((one_le_inv₀ hb).2 hb1) (inv_anti₀ ha hab) ?_).trans ?_
      · rw [show (2 : ℝ) * b⁻¹ = (b / 2)⁻¹ by field_simp]
        exact inv_anti₀ (by positivity) (by linarith)
      · rw [Real.inv_rpow hb.le, Real.rpow_neg hb.le, inv_inv])
  intro a b ha hab
  have ha0 : 0 < a := one_pos.trans_le ha
  have hb0 : 0 < b := ha0.trans_le hab
  have h' := h b⁻¹ a⁻¹ (inv_pos.2 hb0) (inv_anti₀ ha0 hab) (inv_le_one_of_one_le₀ ha)
  simp only [inv_inv] at h'
  refine h'.trans ?_
  have hd : 0 < 1 - (2 : ℝ) ^ (-p) := by linarith
  rw [div_le_div_iff_of_pos_right hd]
  have : a⁻¹ ^ p ≤ 1 := Real.rpow_le_one (inv_nonneg.2 ha0.le) (inv_le_one_of_one_le₀ ha) hp.le
  nlinarith

end QED.GradedProof.RPi4

end
