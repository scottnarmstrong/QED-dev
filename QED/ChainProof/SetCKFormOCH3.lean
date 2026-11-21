/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCH2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp

/-!
# Set (c), Stage K, closed forms: `G` and `𝒢` regularized at `a = 0`

Helper level (no frozen statement). Item 5 of the `ρ_oC` route (Stage K notes). The closed forms
`G = formOCG` and `𝒢 = formOCH` have spurious poles at `a = 0` (`a⁻³ log(1 - aX)`, `a⁻²`,
`a⁻¹`) that cancel. With `φ(a) = (log(1 - aX) + aX + (aX)²/2 + (aX)³/3)/a³`
(**`formOCHphi`**, `|φ| ≤ 2|a|` for `|a| ≤ 1/2` by the logarithm series,
**`formOCHphi_abs_le`**), both are rewritten without poles:

* **`formOCH_eq_r`**: `𝒢 = formOCHr` for `a ≠ 0`, where `formOCHr` uses `a log a` and `φ`;
* **`formOCG_eq_r`**: `G = formOCGr0 + c_A log a` for `a ≠ 0`.

For `X ∈ (0, 1)` both regular forms are continuous in `a` at every `a₀ ∈ [0, 1]`
(**`continuousAt_formOCHr`**, **`continuousAt_formOCGr0`**).
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.ChainProof.SetCK

/-- `φ(a) = (log(1 - aX) + aX + (aX)²/2 + (aX)³/3)/a³`, the logarithm series remainder. -/
noncomputable def formOCHphi (a X : ℝ) : ℝ :=
  (log (1 - a * X) + a * X + (a * X) ^ 2 / 2 + (a * X) ^ 3 / 3) / a ^ 3

/-- `a³` times the principal part at `a = 0` of the `log (1 - a X)` coefficient of `𝒢`. -/
noncomputable def formOCHhS (a X : ℝ) : ℝ :=
  formOCHq
    (0)
    (-X*(X - 2)/(6*(X - 1)^2))
    (7*X*(X - 2)/(12*(X - 1)^2))
    (0)
    (0)
    a

/-- The regular part of the `log (1 - a X)` coefficient of `𝒢`. -/
noncomputable def formOCHhcR (a X : ℝ) : ℝ :=
  formOCHq
    (-X*(2*X^6 - 20*X^5 + 70*X^4 - 114*X^3 + 83*X^2 - 15*X - 10)/(12*(X - 2)*(X - 1)^3))
    (X^2*(X^5 - 12*X^4 + 37*X^3 - 46*X^2 + 20*X - 4)/(12*(X - 2)*(X - 1)^3))
    (-X^3/4)
    (0)
    (0)
    a / (1 - X + a * X)

/-- The regularized rational part of `𝒢` (a polynomial in `a`). -/
noncomputable def formOCHhRat (a X : ℝ) : ℝ :=
  formOCHq
    (X^2*(X - 7)*(X - 2)/(12*(X - 1)^2))
    (X^2*(2*X^4 + 9*X^3 - 41*X^2 + 54*X - 30)/(36*(X - 1)^3))
    (-X^4*(X - 2)*(7*X - 10)/(36*(X - 1)^3))
    (0)
    (0)
    a

/-- `a³` times the principal part at `a = 0` of the `log (1 - a X)` coefficient of `G`. -/
noncomputable def formOCGgS (a X : ℝ) : ℝ :=
  formOCHq
    (X*(X - 2)/(3*(X - 1)^2))
    (-7*X*(X - 2)/(12*(X - 1)^2))
    (-X*(X - 2)*(2*X^4 - 3*X^3 + 2*X^2 + 2*X - 1)/(6*(X - 1)^4))
    (0)
    (0)
    a

/-- The regular part of the `log (1 - a X)` coefficient of `G`. -/
noncomputable def formOCGgcR (a X : ℝ) : ℝ :=
  formOCHq
    (-X^2*(3*X^5 - 9*X^4 + 5*X^3 + 5*X^2 - 9*X - 3)/(12*(X - 1)^3))
    (X^3*(5*X^5 - 22*X^4 + 38*X^3 - 32*X^2 + 10*X - 1)/(6*(X - 1)^4))
    (-X^4/4)
    (0)
    (0)
    a / (1 - X + a * X) ^ 2

/-- The regularized rational part of `G`. -/
noncomputable def formOCGgRat (a X : ℝ) : ℝ :=
  formOCHq
    (X^2*(4*X^5 - 64*X^4 + 221*X^3 - 299*X^2 + 198*X - 36)/(36*(X - 1)^3))
    (X^3*(X - 2)*(2*X^5 + 25*X^4 - 46*X^3 + 36*X^2 + 4*X - 9)/(36*(X - 1)^4))
    (X^4*(X - 2)*(X^5 - 13*X^3 + 25*X^2 - 24*X + 8)/(18*(X - 1)^4))
    (X^5*(X - 2)*(4*X^5 - 12*X^4 + 6*X^3 + 3*X^2 - 6*X + 3)/(36*(X - 1)^4))
    (-X^6*(X - 2)*(2*X^4 - 3*X^3 + 2*X^2 + 2*X - 1)/(18*(X - 1)^4))
    a / ((1 - a * X) * (1 - X + a * X))

/-- The `log a` coefficient of `𝒢`, divided by `a`. -/
noncomputable def formOCHhl (a X : ℝ) : ℝ :=
  formOCHq
    (-X^2*(4*X^5 - 21*X^4 + 42*X^3 - 39*X^2 + 22*X - 4)/(12*(X - 1)^4))
    (-X^3*(X - 2)*(2*X - 1)^2/(6*(X - 1)^4))
    (X^4*(X - 2)*(2*X^2 - 3*X + 2)/(12*(X - 1)^4))
    (X^6*(X - 2)/(12*(X - 1)^4))
    (0)
    a / (1 - a * X)

/-- **`𝒢` without poles at `a = 0`.** -/
noncomputable def formOCHr (a X : ℝ) : ℝ :=
  formOCHhRat a X + formOCHhl a X * (a * log a) +
    formOCHK X * (a * log a) * (a ^ 2 * formOCHphi a X - X - a * X ^ 2 / 2 - a ^ 2 * X ^ 3 / 3) +
    formOCHhS a X * formOCHphi a X + formOCHhcR a X * log (1 - a * X) +
    formOCHK X * log X * log (1 - a * X) + formOCHcM a X * log (1 - X + a * X) +
    formOCHcx a X * log X + a * X ^ 2 / 4 * log (1 - X) + formOCHcT a X * log (2 - X) +
    formOCHK X * (2 * Li₂ (a * X) - Li₂ ((1 - X + a * X) / (2 - X)) +
      Li₂ ((1 - a * X) / (2 - X)))

/-- **`G` without poles at `a = 0`**, except for the `log a` term. -/
noncomputable def formOCGr0 (a X : ℝ) : ℝ :=
  formOCGgRat a X + formOCGcA a X * log X + X ^ 2 / 4 * log (1 - X) +
    formOCGc2X a X * log (2 - X) + formOCGgcR a X * log (1 - a * X) +
    formOCGgS a X * formOCHphi a X + formOCGcbX a X * log (1 - X + a * X)

section

variable {a X : ℝ}

/-- The logarithm series bound: `|φ(a)| ≤ 2|a|` for `|a| ≤ 1/2`, `|X| ≤ 1`. -/
theorem formOCHphi_abs_le (ha : |a| ≤ 1 / 2) (hX : |X| ≤ 1) : |formOCHphi a X| ≤ 2 * |a| := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp [formOCHphi]
  have hu : |a * X| ≤ 1 / 2 := by
    rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg X]
  have h := Real.abs_log_sub_add_sum_range_le (show |a * X| < 1 by linarith) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have e : formOCHphi a X =
      (a * X + (a * X) ^ 2 / 2 + (a * X) ^ 3 / 3 + log (1 - a * X)) / a ^ 3 := by
    unfold formOCHphi; ring
  have hpos : 0 < |a| := abs_pos.2 ha0
  have hX4 : |X| ^ 4 ≤ 1 := pow_le_one₀ (abs_nonneg X) hX
  rw [abs_mul] at hu
  have hb : (|a| * |X|) ^ 4 / (1 - |a| * |X|) ≤ 2 * |a| ^ 4 := by
    rw [div_le_iff₀ (by linarith), mul_pow]
    have : 0 ≤ |a| ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hX4 this, mul_nonneg (abs_nonneg a) (abs_nonneg X)]
  rw [e, abs_div, abs_pow, div_le_iff₀ (by positivity)]
  have h' : |a * X + (a * X) ^ 2 / 2 + (a * X) ^ 3 / 3 + log (1 - a * X)| ≤ 2 * |a| ^ 4 := by
    refine le_trans (le_of_eq_of_le ?_ h) hb
    ring_nf
  calc _ ≤ 2 * |a| ^ 4 := h'
    _ = 2 * |a| * |a| ^ 3 := by ring

theorem tendsto_formOCHphi_zero (hX : |X| ≤ 1) :
    Tendsto (fun b => formOCHphi b X) (𝓝 0) (𝓝 0) := by
  have h2 : Tendsto (fun b : ℝ => 2 * |b|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul 2
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with b hb
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hb
  rw [Real.norm_eq_abs]
  exact formOCHphi_abs_le hb hX

theorem continuousAt_formOCHphi (hX : X ∈ Ioo (0 : ℝ) 1) {a₀ : ℝ} (ha : a₀ ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun b => formOCHphi b X) a₀ := by
  obtain ⟨hX0, hX1⟩ := hX
  rcases eq_or_lt_of_le ha.1 with h | h
  · subst h
    have h0 : formOCHphi 0 X = 0 := by simp [formOCHphi]
    rw [ContinuousAt, h0]
    exact tendsto_formOCHphi_zero (by rw [abs_le]; constructor <;> linarith)
  · have hL : 1 - a₀ * X ≠ 0 := by nlinarith [ha.2]
    unfold formOCHphi
    exact ContinuousAt.div (by fun_prop (disch := exact hL)) (by fun_prop) (by positivity)

/-- **`𝒢` in regular form.** -/
theorem formOCH_eq_r (ha : a ≠ 0) (hX1 : X - 1 ≠ 0) (hX2 : X - 2 ≠ 0)
    (hM : 1 - X + a * X ≠ 0) : formOCH a X = formOCHr a X := by
  simp only [formOCH, formOCHr, formOCHphi, formOCHc0, formOCHcl, formOCHcL, formOCHhRat,
    formOCHhl, formOCHhS, formOCHhcR, formOCHq]
  generalize log a = la
  generalize log (1 - a * X) = lL
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hXg : X - 1 = Xm at *
  generalize hTg : X - 2 = Xt at *
  field_simp
  subst hMg hXg hTg
  ring

/-- **`G` in regular form.** -/
theorem formOCG_eq_r (ha : a ≠ 0) (hX1 : X - 1 ≠ 0) (hX2 : X - 2 ≠ 0) (hL : 1 - a * X ≠ 0)
    (hM : 1 - X + a * X ≠ 0) :
    formOCG a X = formOCGr0 a X + formOCGcA a X * log a := by
  simp only [formOCG, formOCGr0, formOCHphi, formOCGcRat, formOCGcaX, formOCGgRat, formOCGgS,
    formOCGgcR, formOCHq]
  have hO : 1 - X ≠ 0 := fun h => hX1 (by linarith)
  generalize log (1 - a * X) = lL
  generalize hLg : 1 - a * X = Lg at *
  generalize hMg : 1 - X + a * X = Mg at *
  generalize hXg : X - 1 = Xm at *
  generalize hTg : X - 2 = Xt at *
  generalize hOg : 1 - X = Og at *
  field_simp
  subst hLg hMg hXg hTg hOg
  ring

/-- Continuity of a quartic over a denominator. -/
theorem formOCH_continuousAt_q {c₀ c₁ c₂ c₃ c₄ a₀ : ℝ} {D : ℝ → ℝ} (hD : ContinuousAt D a₀)
    (h : D a₀ ≠ 0) : ContinuousAt (fun b => formOCHq c₀ c₁ c₂ c₃ c₄ b / D b) a₀ :=
  ContinuousAt.div (by unfold formOCHq; fun_prop) hD h

theorem formOCH_continuousAt_Li₂ {g : ℝ → ℝ} {a₀ : ℝ} (hg : ContinuousAt g a₀) (h0 : 0 ≤ g a₀)
    (h1 : g a₀ < 1) : ContinuousAt (fun b => Li₂ (g b)) a₀ :=
  (continuousOn_Li₂.continuousAt (Icc_mem_nhds (by linarith) h1)).comp hg

/-- **Continuity of `𝒢`** (regular form) in `a` on `[0, 1]`. -/
theorem continuousAt_formOCHr (hX : X ∈ Ioo (0 : ℝ) 1) {a₀ : ℝ} (ha : a₀ ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun b => formOCHr b X) a₀ := by
  have hφ := continuousAt_formOCHphi hX ha
  obtain ⟨hX0, hX1⟩ := hX
  obtain ⟨ha0, ha1⟩ := ha
  have hL : 0 < 1 - a₀ * X := by nlinarith
  have hM : 0 < 1 - X + a₀ * X := by nlinarith
  have h2 : 0 < 2 - X := by linarith
  have cL : ContinuousAt (fun b : ℝ => 1 - b * X) a₀ := by fun_prop
  have cM : ContinuousAt (fun b : ℝ => 1 - X + b * X) a₀ := by fun_prop
  have c1 : ContinuousAt (fun b => formOCHhRat b X) a₀ := by
    unfold formOCHhRat formOCHq; fun_prop
  have c2 : ContinuousAt (fun b => formOCHhl b X) a₀ := formOCH_continuousAt_q cL hL.ne'
  have c3 : ContinuousAt (fun b => formOCHhS b X) a₀ := by
    unfold formOCHhS formOCHq; fun_prop
  have c4 : ContinuousAt (fun b => formOCHhcR b X) a₀ := formOCH_continuousAt_q cM hM.ne'
  have c5 : ContinuousAt (fun b => formOCHcM b X) a₀ := formOCH_continuousAt_q cL hL.ne'
  have c6 : ContinuousAt (fun b => formOCHcx b X) a₀ := formOCH_continuousAt_q cL hL.ne'
  have c7 : ContinuousAt (fun b => formOCHcT b X) a₀ :=
    formOCH_continuousAt_q (cL.mul cM) (mul_ne_zero hL.ne' hM.ne')
  have cal : ContinuousAt (fun b : ℝ => b * log b) a₀ := continuous_mul_log.continuousAt
  have lL : ContinuousAt (fun b : ℝ => log (1 - b * X)) a₀ := cL.log hL.ne'
  have lM : ContinuousAt (fun b : ℝ => log (1 - X + b * X)) a₀ := cM.log hM.ne'
  have i1 : ContinuousAt (fun b => Li₂ (b * X)) a₀ :=
    formOCH_continuousAt_Li₂ (by fun_prop) (by positivity) (by nlinarith)
  have i2 : ContinuousAt (fun b => Li₂ ((1 - X + b * X) / (2 - X))) a₀ :=
    formOCH_continuousAt_Li₂ (cM.div_const _) (by positivity)
      (by rw [div_lt_one h2]; nlinarith)
  have i3 : ContinuousAt (fun b => Li₂ ((1 - b * X) / (2 - X))) a₀ :=
    formOCH_continuousAt_Li₂ (cL.div_const _) (by positivity)
      (by rw [div_lt_one h2]; nlinarith)
  have cp : ContinuousAt (fun b : ℝ => b ^ 2 * formOCHphi b X - X - b * X ^ 2 / 2 -
      b ^ 2 * X ^ 3 / 3) a₀ := by
    have : ContinuousAt (fun b : ℝ => b ^ 2) a₀ := by fun_prop
    exact (((this.mul hφ).sub continuousAt_const).sub (by fun_prop)).sub (by fun_prop)
  have cco : ContinuousAt (fun b : ℝ => b * X ^ 2 / 4 * log (1 - X)) a₀ := by fun_prop
  exact (((((((((c1.add (c2.mul cal)).add ((continuousAt_const.mul cal).mul cp)).add
    (c3.mul hφ)).add (c4.mul lL)).add (continuousAt_const.mul lL)).add (c5.mul lM)).add
    (c6.mul continuousAt_const)).add cco).add (c7.mul continuousAt_const)).add
    (continuousAt_const.mul (((continuousAt_const.mul i1).sub i2).add i3))

/-- **Continuity of the regular part of `G`** in `a` on `[0, 1]`. -/
theorem continuousAt_formOCGr0 (hX : X ∈ Ioo (0 : ℝ) 1) {a₀ : ℝ} (ha : a₀ ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun b => formOCGr0 b X) a₀ := by
  have hφ := continuousAt_formOCHphi hX ha
  obtain ⟨hX0, hX1⟩ := hX
  obtain ⟨ha0, ha1⟩ := ha
  have hL : 0 < 1 - a₀ * X := by nlinarith
  have hM : 0 < 1 - X + a₀ * X := by nlinarith
  have hO : 0 < 1 - X := by linarith
  have cL : ContinuousAt (fun b : ℝ => 1 - b * X) a₀ := by fun_prop
  have cM : ContinuousAt (fun b : ℝ => 1 - X + b * X) a₀ := by fun_prop
  have c1 : ContinuousAt (fun b => formOCGgRat b X) a₀ :=
    formOCH_continuousAt_q (cL.mul cM) (mul_ne_zero hL.ne' hM.ne')
  have c2 : ContinuousAt (fun b => formOCGcA b X) a₀ := by
    unfold formOCGcA
    exact ContinuousAt.div (by fun_prop) (by fun_prop)
      (mul_ne_zero (pow_ne_zero _ hO.ne') (pow_ne_zero _ hL.ne'))
  have c3 : ContinuousAt (fun b => formOCGc2X b X) a₀ := by
    unfold formOCGc2X
    exact ContinuousAt.div (by fun_prop) (by fun_prop)
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hO.ne') (pow_ne_zero _ hL.ne'))
        (pow_ne_zero _ hM.ne'))
  have c4 : ContinuousAt (fun b => formOCGgcR b X) a₀ :=
    formOCH_continuousAt_q (cM.pow 2) (pow_ne_zero _ hM.ne')
  have c5 : ContinuousAt (fun b => formOCGgS b X) a₀ := by
    unfold formOCGgS formOCHq; fun_prop
  have c6 : ContinuousAt (fun b => formOCGcbX b X) a₀ := by
    unfold formOCGcbX
    exact ContinuousAt.div (by fun_prop) (by fun_prop)
      (mul_ne_zero (pow_ne_zero _ hO.ne') (pow_ne_zero _ hL.ne'))
  exact (((((c1.add (c2.mul continuousAt_const)).add continuousAt_const).add
    (c3.mul continuousAt_const)).add (c4.mul (cL.log hL.ne'))).add (c5.mul hφ)).add
    (c6.mul (cM.log hM.ne'))

/-- Continuity of the `log a` coefficient `c_A` of `G` in `a` on `[0, 1]`. -/
theorem continuousAt_formOCGcA (hX : X ∈ Ioo (0 : ℝ) 1) {a₀ : ℝ} (ha : a₀ ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun b => formOCGcA b X) a₀ := by
  have hL : 0 < 1 - a₀ * X := by nlinarith [hX.1, hX.2, ha.1, ha.2]
  have hO : 0 < 1 - X := by linarith [hX.2]
  unfold formOCGcA
  exact ContinuousAt.div (by fun_prop) (by fun_prop)
    (mul_ne_zero (pow_ne_zero _ hO.ne') (pow_ne_zero _ hL.ne'))

end

end QED.ChainProof.SetCK

end
