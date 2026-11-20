/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCAh

/-!
# Set (c), Stage K, closed forms: the `v = 0` value of `Â` in letters

Helper level (no frozen statement). Step 4 of the `ρ_oC` route (Stage K notes, Session 30+).
The `X`-independent part of the remainder `φ_X` (`formOCPhi`) is
`f(a, x) = Â(a, x, 0) + x²/4 (1 - log D₀)` (**`formOCf`**). With
`D₀ (1 - x) = (1 - a x)(1 - x + a x)` (**`formOCD0_eq_mul`**),
`β_c = -x⁴/(4 (1 - a x)(1 - x + a x))` (**`formOCbeta_eq`**) and
`λ(a, x, 0) = a (1 - x)²/(x (1 - a x)(1 - x + a x))` (**`formOClam_zero`**),
**`formOCAhR_zero`**: `Â(a, x, 0) = R₀(a, x, 0) - β_c log λ(a, x, 0)`, where `R₀(a, x, 0)` is the
rational function **`formOCfR`**; **`formOCf_eq`** writes `f` in the letters
`a, x, 1 - x, 1 - a x, 1 - x + a x` (scratch `stageK/foc4/p1.py`).
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- `R₀(a, x, 0)`, the rational part of `Â` at `v = 0`. -/
noncomputable def formOCfR (a x : ℝ) : ℝ :=
  -x ^ 2 * (2 * a ^ 2 * x ^ 3 - 2 * a ^ 2 * x ^ 2 - 4 * a * x ^ 3 + 4 * a * x ^ 2 + 4 * a * x +
    5 * x ^ 2 - 8 * x + 6) / (8 * (a * x - 1) * (a * x - x + 1))

/-- **The `X`-independent part of `φ_X`**: `f = Â(a, x, 0) + x²/4 (1 - log D₀)`. -/
noncomputable def formOCf (a x : ℝ) : ℝ :=
  formOCAhR a x 0 + x ^ 2 / 4 * (1 - log (formOCD0 a x))

section

variable {a x : ℝ}

theorem formOCD0_eq_mul (hx : x ≠ 1) :
    formOCD0 a x * (1 - x) = (1 - a * x) * (1 - x + a * x) := by
  have h : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  unfold formOCD0 setCKQ
  field_simp
  ring

theorem formOCbeta_eq (hx : x ≠ 1) :
    formOCbeta a x = -x ^ 4 / (4 * ((1 - a * x) * (1 - x + a * x))) := by
  rw [← formOCD0_eq_mul hx, formOCbeta,
    show 4 * (formOCD0 a x * (1 - x)) = -(4 * formOCD0 a x * (x - 1)) by ring, div_neg,
    neg_div, neg_neg]

theorem formOClam_zero (hx : x ∈ Ioo (0 : ℝ) 1) :
    formOClam a x 0 = a * (1 - x) ^ 2 / (x * ((1 - a * x) * (1 - x + a * x))) := by
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h0 : x ≠ 0 := hx.1.ne'
  unfold formOClam formOCE setCKQ
  rw [show x + a * (x ^ 2 / (1 - x) + 0) = x * (1 - x + a * x) / (1 - x) by
    field_simp; ring]
  rw [mul_div_assoc', div_div_eq_mul_div]
  congr 1 <;> ring

theorem formOCAhR_zero (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    formOCAhR a x 0 = formOCfR a x - formOCbeta a x * log (formOClam a x 0) := by
  have hD0 : formOCD0 a x ≠ 0 := (formOCD0_pos ha hx).ne'
  have hx1 : x - 1 ≠ 0 := by linarith [hx.2]
  have h1x : 1 - x ≠ 0 := by linarith [hx.2]
  have hL : a * x - 1 ≠ 0 := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have hM : a * x - x + 1 ≠ 0 := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have hD : formOCD a x 0 = formOCD0 a x := by simp [formOCD, formOCD0]
  have hYc : formOCYc a x 0 = 0 := by simp [formOCYc]
  have hN : x * formOCN1x a x 0 = formOCbeta a x := by
    rw [formOCN1x, formOC_simp_rat3, hD, formOCbeta]
    simp only [formOCN1xN, Matrix.cons_val_zero]
    field_simp
    ring
  have hR : formOCR0 a x 0 = formOCfR a x := by
    rw [formOCR0, formOC_simp_rat3, hD]
    simp only [formOCR0N, Matrix.cons_val_zero]
    have e : formOCD0 a x = (1 - a * x) * (1 - x + a * x) / (1 - x) := by
      rw [← formOCD0_eq_mul (by linarith [hx.2])]
      field_simp
    have hL' : 1 - a * x ≠ 0 := by nlinarith [ha.1, ha.2, hx.1, hx.2]
    have hM' : 1 - x + a * x ≠ 0 := by nlinarith [ha.1, ha.2, hx.1, hx.2]
    rw [e]
    unfold formOCfR setCKQ
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    ring
  unfold formOCAhR
  rw [hYc, hR, ← hN]
  simp

/-- **`f` in letters.** -/
theorem formOCf_eq (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    formOCf a x = formOCfR a x + x ^ 2 / 4 -
      formOCbeta a x * (log a + 2 * log (1 - x) - log x - log (1 - a * x) -
        log (1 - x + a * x)) -
      x ^ 2 / 4 * (log (1 - a * x) + log (1 - x + a * x) - log (1 - x)) := by
  have h1x : 0 < 1 - x := by linarith [hx.2]
  have hL : 0 < 1 - a * x := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have hM : 0 < 1 - x + a * x := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have hlam : log (formOClam a x 0) =
      log a + 2 * log (1 - x) - log x - log (1 - a * x) - log (1 - x + a * x) := by
    have hp : (1 - a * x) * (1 - x + a * x) ≠ 0 := (mul_pos hL hM).ne'
    rw [formOClam_zero hx, log_div (mul_ne_zero ha.1.ne' (pow_ne_zero 2 h1x.ne'))
      (mul_ne_zero hx.1.ne' hp), log_mul ha.1.ne' (pow_ne_zero 2 h1x.ne'), log_pow,
      log_mul hx.1.ne' hp, log_mul hL.ne' hM.ne']
    push_cast
    ring
  have hD0 : log (formOCD0 a x) = log (1 - a * x) + log (1 - x + a * x) - log (1 - x) := by
    have e : formOCD0 a x = (1 - a * x) * (1 - x + a * x) / (1 - x) := by
      rw [← formOCD0_eq_mul (by linarith [hx.2])]
      field_simp
    rw [e, log_div (by positivity) h1x.ne', log_mul hL.ne' hM.ne']
  rw [formOCf, formOCAhR_zero ha hx, hlam, hD0]
  ring

end

end QED.ChainProof.SetCK

end
