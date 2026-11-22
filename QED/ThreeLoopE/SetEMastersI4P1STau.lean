/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetEMastersI4P1SL

/-!
# Set (e), master I₄: the scaling `t = λ τ`

After `t = λ τ` with `λ = a + b = 1 - c` and `k = b + c = 1 - a`, every `λ` in the
`l`-integral `QED.ThreeLoopE.i4SB` of `QED.ThreeLoopE.SetEMastersI4P1SL` cancels except in

  `A = log (c + τ) + 4 + 3 λ (log λ - log (1 + τ)) / (c + τ)`   (`QED.ThreeLoopE.i4TAt`),

and `λ · i4SB (λ τ)` is the bracket `QED.ThreeLoopE.i4TBr a c τ`
(`QED.ThreeLoopE.i4TBr_eq`): with `N = c + k τ` and `δ = a - c - k τ`,

* it vanishes for `k (a + c) τ + c² ≤ 0` (that is `τ ≤ τ₀ = -c² / (k (a + c))`);
* otherwise it is `(Up - Lo) / ((1 + τ)(c + τ))`, where
  `Up = -(A + log k + 2 log a + 2 - log δ) δ / (k a N) - log (N / (k a)) / (k N)` for `δ > 0`
  and `Up = log k / (k N)` for `δ ≤ 0`, and
  `Lo = -(A + 2 log c + 2 - log (-τ)) / (k c) - (log (-τ) - log c) / (k N)` for `τ < 0`
  and `Lo = -(A + log N + 2) / (k N)` for `τ ≥ 0`.

Hence `P'(0) = ∫_{(a, b)} ∫_τ i4TBr a (1 - a - b) τ` (`QED.ThreeLoopE.i4P1_Br`).

## Main definitions

* `QED.ThreeLoopE.i4TDel`, `QED.ThreeLoopE.i4TNt`, `QED.ThreeLoopE.i4TAt`,
  `QED.ThreeLoopE.i4TUp`, `QED.ThreeLoopE.i4TLo`, `QED.ThreeLoopE.i4TBr`.

## Main results

* `QED.ThreeLoopE.i4TBr_eq`, `QED.ThreeLoopE.i4P1_Br`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real

namespace QED.ThreeLoopE

/-- `δ = a - c - k τ`, `k = 1 - a`. -/
def i4TDel (a c τ : ℝ) : ℝ := a - c - (1 - a) * τ

/-- `N = c + k τ`. -/
def i4TNt (a c τ : ℝ) : ℝ := c + (1 - a) * τ

/-- `A = log (c + τ) + 4 + 3 λ (log λ - log (1 + τ)) / (c + τ)`, `λ = 1 - c`. -/
noncomputable def i4TAt (c τ : ℝ) : ℝ :=
  log (c + τ) + 4 + 3 * (1 - c) * (log (1 - c) - log (1 + τ)) / (c + τ)

/-- The upper-end value. -/
noncomputable def i4TUp (a c τ : ℝ) : ℝ :=
  if 0 < i4TDel a c τ then
    -((i4TAt c τ + log (1 - a) + 2 * log a + 2 - log (i4TDel a c τ)) * i4TDel a c τ /
        ((1 - a) * a * i4TNt a c τ)) -
      log (i4TNt a c τ / ((1 - a) * a)) / ((1 - a) * i4TNt a c τ)
  else log (1 - a) / ((1 - a) * i4TNt a c τ)

/-- The lower-end value. -/
noncomputable def i4TLo (a c τ : ℝ) : ℝ :=
  if τ < 0 then
    -((i4TAt c τ + 2 * log c + 2 - log (-τ)) / ((1 - a) * c)) -
      (log (-τ) - log c) / ((1 - a) * i4TNt a c τ)
  else -((i4TAt c τ + log (i4TNt a c τ) + 2) / ((1 - a) * i4TNt a c τ))

/-- The bracket: `λ · i4SB (λ τ)`. -/
noncomputable def i4TBr (a c τ : ℝ) : ℝ :=
  if (1 - a) * (a + c) * τ + c ^ 2 ≤ 0 then 0 else
    (i4TUp a c τ - i4TLo a c τ) / ((1 + τ) * (c + τ))

/-- **The scaled bracket**: `λ · i4SB (λ τ) = i4TBr a c τ`. -/
theorem i4TBr_eq {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1)
    (τ : ℝ) : (a + b) * i4SB a b c ((a + b) * τ) = i4TBr a c τ := by
  have hlam : a + b = 1 - c := by linarith
  have hk : b + c = 1 - a := by linarith
  have hL : 0 < 1 - c := by linarith
  have hK : 0 < 1 - a := by linarith
  have eβ : i4SBe a b c ((a + b) * τ) = (1 - c) ^ 2 * ((1 - a) * (a + c) * τ + c ^ 2) := by
    unfold i4SBe; rw [hlam, hk]; ring
  have eα : i4SAl a b c ((a + b) * τ) = (1 - a) * (1 - c) * i4TDel a c τ := by
    unfold i4SAl i4TDel; rw [hlam, hk]; ring
  have eNt : i4SNt a b c ((a + b) * τ) = (1 - c) * i4TNt a c τ := by
    unfold i4SNt i4TNt; rw [hlam, hk]; ring
  unfold i4TBr i4SB
  by_cases hβ : (1 - a) * (a + c) * τ + c ^ 2 ≤ 0
  · have : i4SBe a b c ((a + b) * τ) ≤ 0 := by
      rw [eβ]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hβ
    simp [this, hβ]
  push Not at hβ
  have hβ' : 0 < i4SBe a b c ((a + b) * τ) := by rw [eβ]; positivity
  have hNt : 0 < i4TNt a c τ := by
    have := i4SNt_pos ha hb hc hβ'
    rw [eNt] at this
    exact pos_of_mul_pos_right this hL.le
  have hcτ : 0 < c + τ := by
    by_contra h
    push Not at h
    have e : (1 - a) * (a + c) - c = a * b := by
      have : b = 1 - a - c := by linarith
      rw [this]; ring
    nlinarith [mul_pos ha hb, mul_pos (mul_pos ha hb) hc]
  have h1τ : 0 < 1 + τ := by linarith
  have eP : i4SP a b c ((a + b) * τ) = 1 / ((1 + τ) * (c + τ)) := by
    unfold i4SP; rw [hlam]; field_simp
  have eC : i4SC a b c ((a + b) * τ) = i4TAt c τ - log (1 - c) := by
    unfold i4SC i4TAt; rw [hlam]
    rw [show (1 - c) * c + (1 - c) * τ = (1 - c) * (c + τ) by ring,
      show (1 - c) ^ 2 / (1 - c + (1 - c) * τ) = (1 - c) / (1 + τ) by field_simp,
      log_mul hL.ne' hcτ.ne', log_div hL.ne' h1τ.ne']
    field_simp; ring
  have eNt' : i4SN a b c ((a + b) * τ) = (1 - c) * i4TNt a c τ := by
    unfold i4SN i4TNt; rw [hlam, hk]; ring
  simp only [hβ'.not_ge, ↓reduceIte, not_le.2 hβ]
  rw [eα]
  -- the lower end
  have hLo : (a + b) * i4SLF a b c ((a + b) * τ) (max 0 ((a + b) * τ)) =
      i4TLo a c τ / ((1 + τ) * (c + τ)) := by
    unfold i4TLo
    by_cases hτ : τ < 0
    · have hm : max 0 ((a + b) * τ) = 0 :=
        max_eq_left (by rw [hlam]; exact mul_nonpos_of_nonneg_of_nonpos hL.le hτ.le)
      have eN0 : i4SN a b c 0 = (1 - c) * c := by unfold i4SN; rw [hlam]; ring
      have hlog : log (0 - (a + b) * τ) = log (1 - c) + log (-τ) := by
        rw [hlam, show 0 - (1 - c) * τ = (1 - c) * (-τ) by ring,
          log_mul hL.ne' (by linarith)]
      simp only [hm, hτ, ↓reduceIte]
      unfold i4SLF
      rw [hlog, eP, eC, eNt, eN0, log_mul hL.ne' hc.ne', hk, hlam]
      field_simp
      unfold i4TNt
      ring
    · push Not at hτ
      have hm : max 0 ((a + b) * τ) = (a + b) * τ := max_eq_right (by positivity)
      simp only [hm, not_lt.2 hτ, ↓reduceIte]
      unfold i4SLF
      rw [sub_self, zero_mul, eP, eC, eNt, eNt', log_mul hL.ne' hNt.ne', hk, hlam]
      field_simp
      unfold i4TNt
      ring
  rw [mul_sub, hLo, sub_div]
  congr 1
  -- the upper end
  unfold i4TUp
  by_cases hδ : 0 < i4TDel a c τ
  · have hα : 0 < (1 - a) * (1 - c) * i4TDel a c τ := by positivity
    simp only [hα, hδ, ↓reduceIte]
    have eN : i4SN a b c (i4SBe a b c ((a + b) * τ) / ((1 - a) * (1 - c) * i4TDel a c τ)) =
        (1 - c) * a * i4TNt a c τ / i4TDel a c τ := by
      rw [eβ]; unfold i4SN i4TNt i4TDel at *; rw [hlam, hk]
      have : b = 1 - a - c := by linarith
      field_simp; ring
    have ex : i4SBe a b c ((a + b) * τ) / ((1 - a) * (1 - c) * i4TDel a c τ) - (a + b) * τ =
        (1 - c) * i4TNt a c τ ^ 2 / ((1 - a) * i4TDel a c τ) := by
      rw [eβ, hlam]; unfold i4TNt i4TDel at *
      field_simp; ring
    unfold i4SLF
    rw [ex, eN, eP, eC, eNt, hk,
      log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_div (by positivity) (by positivity),
      log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_pow, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
    push_cast
    simp only [hlam]
    generalize log (i4TNt a c τ) = L₁
    generalize log (i4TDel a c τ) = L₂
    generalize log (1 - a) = L₃
    generalize log (1 - c) = L₄
    generalize log a = L₅
    generalize i4TAt c τ = A
    field_simp
    unfold i4TNt i4TDel
    ring
  · have hα : ¬ 0 < (1 - a) * (1 - c) * i4TDel a c τ := by
      push Not at hδ ⊢
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hδ
    simp only [hα, hδ, ↓reduceIte]
    rw [eP, eNt, hk]
    field_simp
    rw [hlam]
    ring

/-- **`P'(0)` as a triple integral of the bracket.** -/
theorem i4P1_Br :
    (∀ᵐ q ∂(volume.restrict i4STri), Integrable (i4TBr q.1 (1 - q.1 - q.2))) ∧
      IntegrableOn (fun q : ℝ × ℝ => ∫ τ, i4TBr q.1 (1 - q.1 - q.2) τ) i4STri ∧
      iteratedDeriv 1 i4PInt 0 =
        ((∫ q in i4STri, ∫ τ, i4TBr q.1 (1 - q.1 - q.2) τ : ℝ) : ℂ) := by
  obtain ⟨hae, hI, hE⟩ := i4P1_B
  have key : ∀ᵐ q ∂(volume.restrict i4STri), Integrable (i4TBr q.1 (1 - q.1 - q.2)) ∧
      ∫ t, i4SB q.1 q.2 (1 - q.1 - q.2) t = ∫ τ, i4TBr q.1 (1 - q.1 - q.2) τ := by
    filter_upwards [hae, ae_restrict_mem measurableSet_i4STri] with q hq hT
    obtain ⟨h1, h2, h3⟩ := hT
    have hc : 0 < 1 - q.1 - q.2 := by linarith
    have habc : q.1 + q.2 + (1 - q.1 - q.2) = 1 := by ring
    have hlam : 0 < q.1 + q.2 := by positivity
    have e : i4TBr q.1 (1 - q.1 - q.2) =
        fun τ => (q.1 + q.2) * i4SB q.1 q.2 (1 - q.1 - q.2) ((q.1 + q.2) * τ) :=
      funext fun τ => (i4TBr_eq h1 h2 hc habc τ).symm
    rw [e]
    refine ⟨(hq.comp_mul_left' hlam.ne').const_mul _, ?_⟩
    rw [integral_const_mul, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.2 hlam),
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]
  refine ⟨key.mono fun q hq => hq.1, hI.congr_fun_ae (key.mono fun q hq => hq.2), ?_⟩
  rw [hE, integral_congr_ae (key.mono fun q hq => hq.2)]

end QED.ThreeLoopE

end
