/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWAsmDef
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Set (a), stage D: the elementary `ρ`-integral of the `VB` node density

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. On each
piece cut out of `ρ ∈ (0, 1)` by the sign conditions of `ksWnB`, the node density has the shape
`p₀ + p₁ρ + q ρ log ρ + m ρ log(1-ρ) + e/ρ + f/(1-ρ)`, whose primitive `ksWVF` is elementary.

With `A = ksDA 1 (-T) w`, `B = ksDA 1 (-T) β`, `Y = ksDYmax β w` and the cut
`r⋆ = A/(A - YB)` of `D = (1-ρ)A + ρYB`, the `ρ`-integral of `ksWnB` over `(0, 1)` is a sum of
values of `ksWVF` in each of the four sign cases.

Main results:

* `ksWV_integral_gen`: the integral of the shape over `[a, c] ⊆ [0, 1]`
  (with `e = 0` if `a = 0` and `f = 0` if `c = 1`);
* **`ksWV_integral_neg_neg`** (`A, B < 0`), **`ksWV_integral_neg_pos`** (`A < 0 < B`),
  **`ksWV_integral_pos_neg`** (`B < 0 < A`), **`ksWV_integral_pos_pos`** (`A, B > 0`: zero).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

/-- The integrand shape of the `VB` density in `ρ`. -/
noncomputable def ksWVg (p₀ p₁ q m e f r : ℝ) : ℝ :=
  p₀ + p₁ * r + q * (r * log r) + m * (r * log (1 - r)) + e / r + f / (1 - r)

/-- The primitive of `ksWVg`. -/
noncomputable def ksWVF (p₀ p₁ q m e f r : ℝ) : ℝ :=
  p₀ * r + p₁ * r ^ 2 / 2 + q * (r / 2 * (r * log r) - r ^ 2 / 4) +
    m * (-((1 + r) / 2) * ((1 - r) * log (1 - r)) - r / 2 - r ^ 2 / 4) + e * log r -
    f * log (1 - r)

theorem ksWV_continuous_mulLog_one : Continuous fun y : ℝ => (1 - y) * log (1 - y) :=
  continuous_mul_log.comp (continuous_const.sub continuous_id)

theorem ksWV_hasDerivAt_ksWVF (p₀ p₁ q m e f : ℝ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (ksWVF p₀ p₁ q m e f) (ksWVg p₀ p₁ q m e f r) r := by
  have hr0 : r ≠ 0 := hr.1.ne'
  have hr1 : 1 - r ≠ 0 := by linarith [hr.2]
  have hl := hasDerivAt_log hr0
  have hl1 : HasDerivAt (fun y => log (1 - y)) (-1 / (1 - r)) r := by
    have := (hasDerivAt_log hr1).comp r ((hasDerivAt_id r).const_sub 1)
    refine this.congr_deriv ?_
    field_simp
  have hm : HasDerivAt (fun y => y * log y) (log r + 1) r := by
    have h := (hasDerivAt_id r).mul hl
    simp only [id, one_mul] at h
    refine h.congr_deriv ?_
    field_simp
  have hm1 : HasDerivAt (fun y => (1 - y) * log (1 - y)) (-log (1 - r) - 1) r := by
    have h := ((hasDerivAt_id r).const_sub 1).mul hl1
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have h1 := (hasDerivAt_id r).const_mul p₀
  have h2 := ((hasDerivAt_pow 2 r).const_mul p₁).div_const 2
  have h3 := ((((hasDerivAt_id r).div_const 2).mul hm).sub
    ((hasDerivAt_pow 2 r).div_const 4)).const_mul q
  have h4 := (((((hasDerivAt_id r).const_add 1).div_const 2).neg.mul hm1).sub
    ((hasDerivAt_id r).div_const 2)).sub ((hasDerivAt_pow 2 r).div_const 4)
  have h5 := hl.const_mul e
  have h6 := hl1.const_mul f
  refine (((((h1.add h2).add h3).add (h4.const_mul m)).add h5).sub h6).congr_deriv ?_
  simp only [ksWVg, id, Pi.neg_apply]
  push_cast
  field_simp
  ring

theorem ksWV_intervalIntegrable_ksWVg (p₀ p₁ q m e f : ℝ) {a c : ℝ} (hac : a ≤ c)
    (hA : 0 < a ∨ e = 0) (hC : c < 1 ∨ f = 0) :
    IntervalIntegrable (ksWVg p₀ p₁ q m e f) volume a c := by
  have hlog1 : IntervalIntegrable (fun r : ℝ => log (1 - r)) volume a c := by
    have h := (intervalIntegrable_log' (a := 1 - a) (b := 1 - c)).comp_sub_left 1
    simp only [sub_sub_cancel] at h
    exact h
  have i1 : IntervalIntegrable (fun r : ℝ => p₀ + p₁ * r + q * (r * log r)) volume a c := by
    have := continuous_mul_log
    exact Continuous.intervalIntegrable (by fun_prop) _ _
  have i2 : IntervalIntegrable (fun r : ℝ => m * (r * log (1 - r))) volume a c :=
    (hlog1.continuousOn_mul (g := fun r => r) continuousOn_id).const_mul m
  have i3 : IntervalIntegrable (fun r : ℝ => e / r) volume a c := by
    rcases hA with ha' | rfl
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hac]
      exact continuousOn_const.div continuousOn_id fun x hx => (ha'.trans_le hx.1).ne'
    · simp only [zero_div]; exact intervalIntegrable_const
  have i4 : IntervalIntegrable (fun r : ℝ => f / (1 - r)) volume a c := by
    rcases hC with hc' | rfl
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hac]
      exact continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun x hx => by
        linarith [hx.2]
    · simp only [zero_div]; exact intervalIntegrable_const
  refine ((((i1.add i2).add i3).add i4).congr fun r _ => ?_)
  simp only [ksWVg]

/-- **The elementary `ρ`-integral**: `∫_a^c ksWVg = ksWVF c - ksWVF a` for `0 ≤ a ≤ c ≤ 1`,
`e = 0` if `a = 0`, `f = 0` if `c = 1`. -/
theorem ksWV_integral_gen (p₀ p₁ q m e f : ℝ) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c)
    (hc : c ≤ 1) (hA : 0 < a ∨ e = 0) (hC : c < 1 ∨ f = 0) :
    ∫ r in a..c, ksWVg p₀ p₁ q m e f r = ksWVF p₀ p₁ q m e f c - ksWVF p₀ p₁ q m e f a := by
  have hcont : ContinuousOn (ksWVF p₀ p₁ q m e f) (Icc a c) := by
    have h0 : ContinuousOn (fun r : ℝ => p₀ * r + p₁ * r ^ 2 / 2 + q * (r / 2 * (r * log r) -
        r ^ 2 / 4) + m * (-((1 + r) / 2) * ((1 - r) * log (1 - r)) - r / 2 - r ^ 2 / 4))
        (Icc a c) := by
      have := continuous_mul_log
      have := ksWV_continuous_mulLog_one
      exact Continuous.continuousOn (by fun_prop)
    have h1 : ContinuousOn (fun r : ℝ => e * log r) (Icc a c) := by
      rcases hA with ha' | rfl
      · exact (continuousOn_log.mono fun x hx => (ha'.trans_le hx.1).ne').const_smul e
      · simp only [zero_mul]; exact continuousOn_const
    have h2 : ContinuousOn (fun r : ℝ => f * log (1 - r)) (Icc a c) := by
      rcases hC with hc' | rfl
      · refine ContinuousOn.mul continuousOn_const ?_
        exact (continuousOn_log.comp (continuousOn_const.sub continuousOn_id)
          fun x hx => by simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.2])
      · simp only [zero_mul]; exact continuousOn_const
    exact (h0.add h1).sub h2
  rw [integral_eq_sub_of_hasDerivAt_of_le hac hcont
    (fun r hr => ksWV_hasDerivAt_ksWVF p₀ p₁ q m e f ⟨ha.trans_lt hr.1, hr.2.trans_le hc⟩)
    (ksWV_intervalIntegrable_ksWVg p₀ p₁ q m e f hac hA hC)]

/-- A function equal to `ksWVg` on `(a, c)` has the elementary integral. -/
theorem ksWV_piece {f : ℝ → ℝ} (p₀ p₁ q m e g : ℝ) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c)
    (hc : c ≤ 1) (hA : 0 < a ∨ e = 0) (hC : c < 1 ∨ g = 0)
    (h : EqOn (ksWVg p₀ p₁ q m e g) f (Ioo a c)) :
    IntervalIntegrable f volume a c ∧
      ∫ r in a..c, f r = ksWVF p₀ p₁ q m e g c - ksWVF p₀ p₁ q m e g a := by
  refine ⟨(ksWV_intervalIntegrable_ksWVg p₀ p₁ q m e g hac hA hC).congr_uIoo
    (uIoo_of_le hac ▸ h), ?_⟩
  rw [← integral_congr_Ioo_of_le hac h]
  exact ksWV_integral_gen p₀ p₁ q m e g ha hac hc hA hC

/-! ### The polynomial parts of the density -/

/-- `ksUG0 1 s ρ β w = g₀ + g₁ρ + g₂ρ²` with `A = ksDA 1 s w`. -/
theorem ksWV_ksUG0_eq (s ρ β w : ℝ) :
    ksUG0 1 s ρ β w = 16 * (ksDA 1 s w - 2 * w ^ 2 + 2 * w - 1) +
      16 * (-ksDA 1 s w - 2 * β * w + β + 2 * w ^ 2 - w) * ρ +
      16 * (-ksDA 1 s w * β ^ 2 + ksDA 1 s w * β + (β - w) ^ 2) * ρ ^ 2 := by
  simp only [ksUG0, ksUGc, ksDEc, ksDHc, ksDcv, ksDc0, ksUPtB, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.val_zero, Nat.cast_zero]
  ring

/-- `ksUq ρ β w = q₀ + q₁ρ`. -/
theorem ksWV_ksUq_eq (ρ β w : ℝ) :
    ksUq ρ β w = (32 * β - 32 * β ^ 2 - 32) + 32 * β * (1 - β) * ρ := by
  unfold ksUq
  ring

/-! ### Case `A_w < 0`, `A_β < 0` -/

/-- **The `ρ`-integral when both node denominators are negative.** -/
theorem ksWV_integral_neg_neg {β w T : ℝ} (hA : ksDA 1 (-T) w < 0) (hB : ksDA 1 (-T) β < 0)
    (hY : 0 < ksDYmax β w) :
    ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ β w T =
      ksWVF (-(32 * β - 32 * β ^ 2 - 32) * ksDYmax β w / 2 +
          ksUf0 β w * log (-ksDA 1 (-T) β))
        (-(32 * β * (1 - β)) * ksDYmax β w / 2 - ksUcB w * log (ksDYmax β w) +
          ksUcB w * log (-ksDA 1 (-T) w)) (ksUcB w) 0 0 0 1 := by
  have hpt : ∀ ρ ∈ Ioo (0 : ℝ) 1, ksWnB ρ β w T =
      ksWVg (-(32 * β - 32 * β ^ 2 - 32) * ksDYmax β w / 2 +
          ksUf0 β w * log (-ksDA 1 (-T) β))
        (-(32 * β * (1 - β)) * ksDYmax β w / 2 - ksUcB w * log (ksDYmax β w) +
          ksUcB w * log (-ksDA 1 (-T) w)) (ksUcB w) 0 0 0 ρ := by
    intro ρ hρ
    obtain ⟨h0, h1⟩ := hρ
    have hD : (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β < 0 := by
      have : 0 < 1 - ρ := by linarith
      nlinarith [mul_pos this (neg_pos.2 hA), mul_pos (mul_pos h0 hY) (neg_pos.2 hB)]
    have hz : ¬ (ρ * ksDYmax β w * ksDA 1 (-T) β / ((1 - ρ) * ksDA 1 (-T) w) < -1) := by
      have : 0 < ρ * ksDYmax β w * ksDA 1 (-T) β / ((1 - ρ) * ksDA 1 (-T) w) :=
        div_pos_of_neg_of_neg (by nlinarith [mul_pos h0 hY])
          (mul_neg_of_pos_of_neg (by linarith) hA)
      linarith
    simp only [ksWnB, hD, hA, hB, hz, ↓reduceIte, log_div hY.ne' h0.ne', ksWV_ksUq_eq, ksWVg]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    ksWV_integral_gen _ _ _ _ _ _ le_rfl zero_le_one le_rfl (Or.inr rfl) (Or.inr rfl)]
  simp only [ksWVF, log_zero, log_one, sub_zero, sub_self]
  ring

/-! ### Mixed signs -/

/-- The cut `r⋆ = A/(A - Y B)` of `(0, 1)` where `D = (1-ρ)A + ρYB` changes sign. -/
noncomputable def ksWVrs (A B Y : ℝ) : ℝ := A / (A - Y * B)

theorem ksWV_rs_mem {A B Y : ℝ} (hY : 0 < Y) (hAB : A * B < 0) :
    ksWVrs A B Y ∈ Ioo (0 : ℝ) 1 := by
  unfold ksWVrs
  rcases lt_or_gt_of_ne (show A ≠ 0 by rintro rfl; simp at hAB) with hA | hA
  · have hB : 0 < B := by nlinarith
    have hd : A - Y * B < 0 := by nlinarith [mul_pos hY hB]
    exact ⟨div_pos_of_neg_of_neg hA hd, (div_lt_one_of_neg hd).2 (by nlinarith [mul_pos hY hB])⟩
  · have hB : B < 0 := by nlinarith
    have hd : 0 < A - Y * B := by nlinarith [mul_pos hY (neg_pos.2 hB)]
    exact ⟨div_pos hA hd, (div_lt_one hd).2 (by nlinarith [mul_pos hY (neg_pos.2 hB)])⟩

/-- `-z = ρK/(1-ρ)`, `K = YB/(-A)`, and its logarithm. -/
theorem ksWV_log_negz {A B Y ρ : ℝ} (hK : 0 < Y * B / -A) (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    log (-(ρ * Y * B / ((1 - ρ) * A))) = log ρ + log (Y * B / -A) - log (1 - ρ) := by
  obtain ⟨h0, h1⟩ := hρ
  have hA : A ≠ 0 := by rintro rfl; simp at hK
  have h1' : (0 : ℝ) < 1 - ρ := by linarith
  rw [show -(ρ * Y * B / ((1 - ρ) * A)) = ρ * (Y * B / -A) / (1 - ρ) by
    field_simp, log_div (mul_pos h0 hK).ne' h1'.ne', log_mul h0.ne' hK.ne']

/-- **The `ρ`-integral for `A_w < 0 < A_β`.** -/
theorem ksWV_integral_neg_pos {β w T : ℝ} (hT : 0 < T) (hA : ksDA 1 (-T) w < 0)
    (hB : 0 < ksDA 1 (-T) β) (hY : 0 < ksDYmax β w) :
    ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ β w T =
      (ksWVF (-(32 * β - 32 * β ^ 2 - 32) * ksDYmax β w / 2)
          (-(32 * β * (1 - β)) * ksDYmax β w / 2 - ksUcB w * log (ksDYmax β w) +
            ksUcB w * log (-ksDA 1 (-T) w)) (ksUcB w) 0 0 (-ksUf0 β w)
          (ksWVrs (ksDA 1 (-T) w) (ksDA 1 (-T) β) (ksDYmax β w)) -
        ksWVF (-(32 * β - 32 * β ^ 2 - 32) * ksDYmax β w / 2)
          (-(32 * β * (1 - β)) * ksDYmax β w / 2 - ksUcB w * log (ksDYmax β w) +
            ksUcB w * log (-ksDA 1 (-T) w)) (ksUcB w) 0 0 (-ksUf0 β w) 0) +
      (ksWVF (-(16 * (-ksDA 1 (-T) w - 2 * β * w + β + 2 * w ^ 2 - w)) / ksDA 1 (-T) β)
          (-(16 * (-ksDA 1 (-T) w * β ^ 2 + ksDA 1 (-T) w * β + (β - w) ^ 2)) / ksDA 1 (-T) β -
            ksUcB w * log (ksDYmax β w) + ksUcB w * log (-ksDA 1 (-T) w) +
            ksUcB w * log (ksDYmax β w * ksDA 1 (-T) β / -ksDA 1 (-T) w))
          (2 * ksUcB w) (-ksUcB w)
          (-(16 * (ksDA 1 (-T) w - 2 * w ^ 2 + 2 * w - 1)) / ksDA 1 (-T) β) 0 1 -
        ksWVF (-(16 * (-ksDA 1 (-T) w - 2 * β * w + β + 2 * w ^ 2 - w)) / ksDA 1 (-T) β)
          (-(16 * (-ksDA 1 (-T) w * β ^ 2 + ksDA 1 (-T) w * β + (β - w) ^ 2)) / ksDA 1 (-T) β -
            ksUcB w * log (ksDYmax β w) + ksUcB w * log (-ksDA 1 (-T) w) +
            ksUcB w * log (ksDYmax β w * ksDA 1 (-T) β / -ksDA 1 (-T) w))
          (2 * ksUcB w) (-ksUcB w)
          (-(16 * (ksDA 1 (-T) w - 2 * w ^ 2 + 2 * w - 1)) / ksDA 1 (-T) β) 0
          (ksWVrs (ksDA 1 (-T) w) (ksDA 1 (-T) β) (ksDYmax β w))) := by
  have hrs := ksWV_rs_mem hY (mul_neg_of_neg_of_pos hA hB)
  have hd : ksDA 1 (-T) w - ksDYmax β w * ksDA 1 (-T) β < 0 := by
    nlinarith [mul_pos hY hB]
  have hK : 0 < ksDYmax β w * ksDA 1 (-T) β / -ksDA 1 (-T) w :=
    div_pos (mul_pos hY hB) (neg_pos.2 hA)
  have heps : ¬ (w * (1 - w) < β * (1 - β)) := by
    intro h
    simp only [ksDA] at hA hB
    nlinarith [mul_lt_mul_of_pos_right h hT]
  -- `D < 0` exactly below the cut
  have hDiff : ∀ ρ, (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β =
      (ksDA 1 (-T) w - ksDYmax β w * ksDA 1 (-T) β) *
        (ksWVrs (ksDA 1 (-T) w) (ksDA 1 (-T) β) (ksDYmax β w) - ρ) := by
    intro ρ; unfold ksWVrs; have := hd.ne; field_simp; ring
  have hzD : ∀ ρ, ρ < 1 → (ρ * ksDYmax β w * ksDA 1 (-T) β / ((1 - ρ) * ksDA 1 (-T) w) < -1 ↔
      0 < (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β) := by
    intro ρ h1
    have hn : (1 - ρ) * ksDA 1 (-T) w < 0 := mul_neg_of_pos_of_neg (by linarith) hA
    rw [div_lt_iff_of_neg hn]
    constructor <;> intro h <;> linarith
  have e1 : EqOn (ksWVg (-(32 * β - 32 * β ^ 2 - 32) * ksDYmax β w / 2)
      (-(32 * β * (1 - β)) * ksDYmax β w / 2 - ksUcB w * log (ksDYmax β w) +
        ksUcB w * log (-ksDA 1 (-T) w)) (ksUcB w) 0 0 (-ksUf0 β w)) (fun ρ => ksWnB ρ β w T)
      (Ioo 0 (ksWVrs (ksDA 1 (-T) w) (ksDA 1 (-T) β) (ksDYmax β w))) := by
    intro ρ hρ
    have h1 : ρ < 1 := hρ.2.trans hrs.2
    have hD : (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β < 0 := by
      rw [hDiff]; exact mul_neg_of_neg_of_pos hd (by linarith [hρ.2])
    have hz := mt (hzD ρ h1).1 (not_lt.2 hD.le)
    have hB' : ¬ ksDA 1 (-T) β < 0 := not_lt.2 hB.le
    have h1' : (1 : ℝ) - ρ ≠ 0 := by linarith
    simp only [ksWnB, hD, hA, hB', hz, ↓reduceIte, log_div hY.ne' hρ.1.ne', ksWV_ksUq_eq, ksWVg]
    field_simp
    ring
  have e2 : EqOn (ksWVg (-(16 * (-ksDA 1 (-T) w - 2 * β * w + β + 2 * w ^ 2 - w)) /
        ksDA 1 (-T) β)
      (-(16 * (-ksDA 1 (-T) w * β ^ 2 + ksDA 1 (-T) w * β + (β - w) ^ 2)) / ksDA 1 (-T) β -
        ksUcB w * log (ksDYmax β w) + ksUcB w * log (-ksDA 1 (-T) w) +
        ksUcB w * log (ksDYmax β w * ksDA 1 (-T) β / -ksDA 1 (-T) w))
      (2 * ksUcB w) (-ksUcB w)
      (-(16 * (ksDA 1 (-T) w - 2 * w ^ 2 + 2 * w - 1)) / ksDA 1 (-T) β) 0)
      (fun ρ => ksWnB ρ β w T) (Ioo (ksWVrs (ksDA 1 (-T) w) (ksDA 1 (-T) β) (ksDYmax β w)) 1) := by
    intro ρ hρ
    have hρ' : ρ ∈ Ioo (0 : ℝ) 1 := ⟨hrs.1.trans hρ.1, hρ.2⟩
    have hD : 0 < (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β := by
      rw [hDiff]; exact mul_pos_of_neg_of_neg hd (by linarith [hρ.1])
    have hz := (hzD ρ hρ.2).2 hD
    have hD' : ¬ ((1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β < 0) :=
      not_lt.2 hD.le
    have hB' : ¬ ksDA 1 (-T) β < 0 := not_lt.2 hB.le
    have h1' : (1 : ℝ) - ρ ≠ 0 := by linarith [hρ.2]
    simp only [ksWnB, hD', hA, hB', hz, heps, ↓reduceIte, log_div hY.ne' hρ'.1.ne',
      ksWV_log_negz hK hρ', ksWV_ksUG0_eq, ksWVg]
    have hρ0 : ρ ≠ 0 := hρ'.1.ne'
    have hB0 : ksDA 1 (-T) β ≠ 0 := hB.ne'
    field_simp
    ring
  obtain ⟨i1, v1⟩ := ksWV_piece _ _ _ _ _ _ le_rfl hrs.1.le hrs.2.le (Or.inr rfl)
    (Or.inl hrs.2) e1
  obtain ⟨i2, v2⟩ := ksWV_piece _ _ _ _ _ _ hrs.1.le hrs.2.le le_rfl (Or.inl hrs.1)
    (Or.inr rfl) e2
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← integral_add_adjacent_intervals i1 i2, v1, v2]

/-- **The `ρ`-integral for `A_β < 0 < A_w`.** -/
theorem ksWV_integral_pos_neg {β w T : ℝ} (hT : 0 < T) (hA : 0 < ksDA 1 (-T) w)
    (hB : ksDA 1 (-T) β < 0) (hY : 0 < ksDYmax β w) :
    ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ β w T =
      (ksWVF (ksUf0 β w * log (-ksDA 1 (-T) β)) 0 0 0 0 (ksUf0 β w)
          (ksWVrs (ksDA 1 (-T) w) (ksDA 1 (-T) β) (ksDYmax β w)) -
        ksWVF (ksUf0 β w * log (-ksDA 1 (-T) β)) 0 0 0 0 (ksUf0 β w) 0) +
      (ksWVF ((16 * (-ksDA 1 (-T) w - 2 * β * w + β + 2 * w ^ 2 - w)) / ksDA 1 (-T) β -
            (32 * β - 32 * β ^ 2 - 32) * ksDYmax β w / 2 + ksUf0 β w * log (-ksDA 1 (-T) β))
          ((16 * (-ksDA 1 (-T) w * β ^ 2 + ksDA 1 (-T) w * β + (β - w) ^ 2)) / ksDA 1 (-T) β -
            32 * β * (1 - β) * ksDYmax β w / 2 -
            ksUcB w * log (ksDYmax β w * ksDA 1 (-T) β / -ksDA 1 (-T) w))
          (-ksUcB w) (ksUcB w)
          ((16 * (ksDA 1 (-T) w - 2 * w ^ 2 + 2 * w - 1)) / ksDA 1 (-T) β) 0 1 -
        ksWVF ((16 * (-ksDA 1 (-T) w - 2 * β * w + β + 2 * w ^ 2 - w)) / ksDA 1 (-T) β -
            (32 * β - 32 * β ^ 2 - 32) * ksDYmax β w / 2 + ksUf0 β w * log (-ksDA 1 (-T) β))
          ((16 * (-ksDA 1 (-T) w * β ^ 2 + ksDA 1 (-T) w * β + (β - w) ^ 2)) / ksDA 1 (-T) β -
            32 * β * (1 - β) * ksDYmax β w / 2 -
            ksUcB w * log (ksDYmax β w * ksDA 1 (-T) β / -ksDA 1 (-T) w))
          (-ksUcB w) (ksUcB w)
          ((16 * (ksDA 1 (-T) w - 2 * w ^ 2 + 2 * w - 1)) / ksDA 1 (-T) β) 0
          (ksWVrs (ksDA 1 (-T) w) (ksDA 1 (-T) β) (ksDYmax β w))) := by
  have hrs := ksWV_rs_mem hY (mul_neg_of_pos_of_neg hA hB)
  have hd : 0 < ksDA 1 (-T) w - ksDYmax β w * ksDA 1 (-T) β := by
    nlinarith [mul_pos hY (neg_pos.2 hB)]
  have hK : 0 < ksDYmax β w * ksDA 1 (-T) β / -ksDA 1 (-T) w :=
    div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hY hB) (neg_neg_of_pos hA)
  have heps : w * (1 - w) < β * (1 - β) := by
    simp only [ksDA] at hA hB
    by_contra h
    nlinarith [mul_le_mul_of_nonneg_right (not_lt.1 h) hT.le]
  have hDiff : ∀ ρ, (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β =
      (ksDA 1 (-T) w - ksDYmax β w * ksDA 1 (-T) β) *
        ((ksWVrs (ksDA 1 (-T) w) (ksDA 1 (-T) β) (ksDYmax β w)) - ρ) := by
    intro ρ; unfold ksWVrs; have := hd.ne'; field_simp; ring
  have hzD : ∀ ρ, ρ < 1 → (ρ * ksDYmax β w * ksDA 1 (-T) β / ((1 - ρ) * ksDA 1 (-T) w) < -1 ↔
      (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β < 0) := by
    intro ρ h1
    have hn : 0 < (1 - ρ) * ksDA 1 (-T) w := mul_pos (by linarith) hA
    rw [div_lt_iff₀ hn]
    constructor <;> intro h <;> linarith
  have hA' : ¬ ksDA 1 (-T) w < 0 := not_lt.2 hA.le
  have e1 : EqOn (ksWVg (ksUf0 β w * log (-ksDA 1 (-T) β)) 0 0 0 0 (ksUf0 β w))
      (fun ρ => ksWnB ρ β w T) (Ioo 0 (ksWVrs (ksDA 1 (-T) w) (ksDA 1 (-T) β) (ksDYmax β w))) := by
    intro ρ hρ
    have h1 : ρ < 1 := hρ.2.trans hrs.2
    have hD : 0 < (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β := by
      rw [hDiff]; exact mul_pos hd (by linarith [hρ.2])
    have hD' : ¬ ((1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β < 0) :=
      not_lt.2 hD.le
    have hz := mt (hzD ρ h1).1 hD'
    have h1' : (1 : ℝ) - ρ ≠ 0 := by linarith
    simp only [ksWnB, hD', hA', hB, hz, ↓reduceIte, ksWVg]
    field_simp
    ring
  have e2 : EqOn (ksWVg ((16 * (-ksDA 1 (-T) w - 2 * β * w + β + 2 * w ^ 2 - w)) / ksDA 1 (-T) β -
            (32 * β - 32 * β ^ 2 - 32) * ksDYmax β w / 2 + ksUf0 β w * log (-ksDA 1 (-T) β))
          ((16 * (-ksDA 1 (-T) w * β ^ 2 + ksDA 1 (-T) w * β + (β - w) ^ 2)) / ksDA 1 (-T) β -
            32 * β * (1 - β) * ksDYmax β w / 2 -
            ksUcB w * log (ksDYmax β w * ksDA 1 (-T) β / -ksDA 1 (-T) w))
          (-ksUcB w) (ksUcB w)
          ((16 * (ksDA 1 (-T) w - 2 * w ^ 2 + 2 * w - 1)) / ksDA 1 (-T) β) 0)
      (fun ρ => ksWnB ρ β w T) (Ioo (ksWVrs (ksDA 1 (-T) w) (ksDA 1 (-T) β) (ksDYmax β w)) 1) := by
    intro ρ hρ
    have hρ' : ρ ∈ Ioo (0 : ℝ) 1 := ⟨hrs.1.trans hρ.1, hρ.2⟩
    have hD : (1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β < 0 := by
      rw [hDiff]; exact mul_neg_of_pos_of_neg hd (by linarith [hρ.1])
    have hz := (hzD ρ hρ.2).2 hD
    have h1' : (1 : ℝ) - ρ ≠ 0 := by linarith [hρ.2]
    simp only [ksWnB, hD, hA', hB, hz, heps, ↓reduceIte, ksWV_log_negz hK hρ', ksWV_ksUG0_eq,
      ksWV_ksUq_eq, ksWVg]
    have hρ0 : ρ ≠ 0 := hρ'.1.ne'
    have hB0 : ksDA 1 (-T) β ≠ 0 := hB.ne
    field_simp
    ring
  obtain ⟨i1, v1⟩ := ksWV_piece _ _ _ _ _ _ le_rfl hrs.1.le hrs.2.le (Or.inr rfl)
    (Or.inl hrs.2) e1
  obtain ⟨i2, v2⟩ := ksWV_piece _ _ _ _ _ _ hrs.1.le hrs.2.le le_rfl (Or.inl hrs.1)
    (Or.inr rfl) e2
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← integral_add_adjacent_intervals i1 i2, v1, v2]

/-- **The `ρ`-integral vanishes when both node denominators are positive.** -/
theorem ksWV_integral_pos_pos {β w T : ℝ} (hA : 0 < ksDA 1 (-T) w) (hB : 0 < ksDA 1 (-T) β)
    (hY : 0 < ksDYmax β w) : ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ β w T = 0 := by
  have hpt : ∀ ρ ∈ Ioo (0 : ℝ) 1, ksWnB ρ β w T = 0 := by
    intro ρ hρ
    obtain ⟨h0, h1⟩ := hρ
    have hD : ¬ ((1 - ρ) * ksDA 1 (-T) w + ρ * ksDYmax β w * ksDA 1 (-T) β < 0) := by
      have : 0 < 1 - ρ := by linarith
      nlinarith [mul_pos this hA, mul_pos (mul_pos h0 hY) hB]
    have hz : ¬ (ρ * ksDYmax β w * ksDA 1 (-T) β / ((1 - ρ) * ksDA 1 (-T) w) < -1) := by
      have : 0 < ρ * ksDYmax β w * ksDA 1 (-T) β / ((1 - ρ) * ksDA 1 (-T) w) :=
        div_pos (mul_pos (mul_pos h0 hY) hB) (mul_pos (by linarith) hA)
      linarith
    simp only [ksWnB, hD, not_lt.2 hA.le, not_lt.2 hB.le, hz, ↓reduceIte]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_zero]

end QED.ChainProof.SetAKS

end
