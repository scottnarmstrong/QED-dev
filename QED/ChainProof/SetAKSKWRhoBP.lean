/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Set (a), stage D: integrals of polynomials times logarithms

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. After the
`ρ`-integral, the `VB` node density is, on each piece of the `w`-interval, a polynomial in `w`
plus polynomials times logarithms `log (w - a)` (with `Real.log`, i.e. `log |w - a|`). This file
integrates such functions over an arbitrary interval, with no condition on the position of `a`:
`w ↦ w ^ j log (w - a)` has the continuous primitive `ksWPH j a`.

Main results:

* **`ksWP_integral_pow_log`**: `∫_l^u w^j log (w - a) dw = ksWPH j a u - ksWPH j a l`;
* **`ksWP_integral_ksWPe`**: the integral of a finite combination `ksWPe L P` of such terms and
  monomials is `ksWPv L P l u`;
* `ksWP_integral_ksWPq`: the integral of `c₁/(w - p) + c₂/(w - p)²` off the pole;
* `ksWP_piece`: the same for a function agreeing with `ksWPe L P` on `(l, u)`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

/-- `S_j(a, w) = Σ_{m ≤ j} w^m a^(j-m)`, so that `S_j(a, w) (w - a) = w^(j+1) - a^(j+1)`. -/
noncomputable def ksWPs (j : ℕ) (a w : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (j + 1), w ^ m * a ^ (j - m)

/-- A primitive of `S_j(a, ·)`. -/
noncomputable def ksWPr (j : ℕ) (a w : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (j + 1), w ^ (m + 1) / (m + 1) * a ^ (j - m)

/-- The continuous primitive of `w ↦ w ^ j log (w - a)`. -/
noncomputable def ksWPH (j : ℕ) (a w : ℝ) : ℝ :=
  (ksWPs j a w * ((w - a) * log (w - a)) - ksWPr j a w) / (j + 1)

theorem ksWP_ksWPs_mul (j : ℕ) (a w : ℝ) : ksWPs j a w * (w - a) = w ^ (j + 1) - a ^ (j + 1) := by
  unfold ksWPs
  rw [← geom_sum₂_mul]
  simp only [Nat.add_sub_cancel]

theorem ksWP_continuous_ksWPH (j : ℕ) (a : ℝ) : Continuous (ksWPH j a) := by
  have h1 : Continuous fun w : ℝ => (w - a) * log (w - a) :=
    continuous_mul_log.comp (continuous_id.sub continuous_const)
  unfold ksWPH ksWPs ksWPr
  fun_prop

theorem ksWP_hasDerivAt_ksWPr (j : ℕ) (a w : ℝ) : HasDerivAt (ksWPr j a) (ksWPs j a w) w := by
  unfold ksWPr ksWPs
  have : ∀ m ∈ Finset.range (j + 1), HasDerivAt (fun w : ℝ => w ^ (m + 1) / (m + 1) * a ^ (j - m))
      (w ^ m * a ^ (j - m)) w := by
    intro m _
    have h := ((hasDerivAt_pow (m + 1) w).div_const ((m : ℝ) + 1)).mul_const (a ^ (j - m))
    refine h.congr_deriv ?_
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
  have h := HasDerivAt.fun_sum this
  simpa using h

theorem ksWP_hasDerivAt_ksWPH (j : ℕ) {a w : ℝ} (hw : w ≠ a) :
    HasDerivAt (ksWPH j a) (w ^ j * log (w - a)) w := by
  have hwa : w - a ≠ 0 := sub_ne_zero.2 hw
  have e : ksWPH j a = fun x => ((x ^ (j + 1) - a ^ (j + 1)) * log (x - a) - ksWPr j a x) /
      (j + 1) := by
    funext x
    unfold ksWPH
    rw [← ksWP_ksWPs_mul, mul_assoc]
  rw [e]
  have hl : HasDerivAt (fun x => log (x - a)) (1 / (w - a)) w := by
    have := ((hasDerivAt_id w).sub_const a).log hwa
    simpa using this
  have h := ((((hasDerivAt_pow (j + 1) w).sub_const (a ^ (j + 1))).mul hl).sub
    (ksWP_hasDerivAt_ksWPr j a w)).div_const ((j : ℝ) + 1)
  refine h.congr_deriv ?_
  have hS := ksWP_ksWPs_mul j a w
  have : (j : ℝ) + 1 ≠ 0 := by positivity
  rw [← hS]
  push_cast
  field_simp
  ring

theorem ksWP_intervalIntegrable_pow_log (j : ℕ) (a l u : ℝ) :
    IntervalIntegrable (fun w => w ^ j * log (w - a)) volume l u := by
  have h := (intervalIntegrable_log' (a := l - a) (b := u - a)).comp_sub_right a
  simp only [sub_add_cancel] at h
  have := h.continuousOn_mul (g := fun w : ℝ => w ^ j) (continuous_pow j).continuousOn
  simpa only [mul_comm] using this

/-- **The integral of `w^j log (w - a)`** over any interval. -/
theorem ksWP_integral_pow_log (j : ℕ) (a l u : ℝ) :
    ∫ w in l..u, w ^ j * log (w - a) = ksWPH j a u - ksWPH j a l :=
  integral_eq_of_hasDerivAt_off_countable (ksWPH j a) (fun w => w ^ j * log (w - a))
    (countable_singleton a) (ksWP_continuous_ksWPH j a).continuousOn
    (fun _ hw => ksWP_hasDerivAt_ksWPH j hw.2) (ksWP_intervalIntegrable_pow_log j a l u)

/-- A finite combination of terms `c w^j log (w - a)` (list `L` of `(c, j, a)`) and monomials
`c w^j` (list `P` of `(c, j)`). -/
noncomputable def ksWPe (L : List (ℝ × ℕ × ℝ)) (P : List (ℝ × ℕ)) (w : ℝ) : ℝ :=
  (L.map fun t => t.1 * (w ^ t.2.1 * log (w - t.2.2))).sum + (P.map fun t => t.1 * w ^ t.2).sum

/-- The integral of `ksWPe L P` over `[l, u]`. -/
noncomputable def ksWPv (L : List (ℝ × ℕ × ℝ)) (P : List (ℝ × ℕ)) (l u : ℝ) : ℝ :=
  (L.map fun t => t.1 * (ksWPH t.2.1 t.2.2 u - ksWPH t.2.1 t.2.2 l)).sum +
    (P.map fun t => t.1 * ((u ^ (t.2 + 1) - l ^ (t.2 + 1)) / (t.2 + 1))).sum

theorem ksWP_log_part (L : List (ℝ × ℕ × ℝ)) (l u : ℝ) :
    IntervalIntegrable (fun w => (L.map fun t => t.1 * (w ^ t.2.1 * log (w - t.2.2))).sum)
        volume l u ∧
      ∫ w in l..u, (L.map fun t => t.1 * (w ^ t.2.1 * log (w - t.2.2))).sum =
        (L.map fun t => t.1 * (ksWPH t.2.1 t.2.2 u - ksWPH t.2.1 t.2.2 l)).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    obtain ⟨c, j, a⟩ := t
    have i1 := (ksWP_intervalIntegrable_pow_log j a l u).const_mul c
    simp only [List.map_cons, List.sum_cons]
    refine ⟨i1.add ih.1, ?_⟩
    rw [integral_add i1 ih.1, intervalIntegral.integral_const_mul, ksWP_integral_pow_log, ih.2]

theorem ksWP_pow_part (P : List (ℝ × ℕ)) (l u : ℝ) :
    IntervalIntegrable (fun w => (P.map fun t => t.1 * w ^ t.2).sum) volume l u ∧
      ∫ w in l..u, (P.map fun t => t.1 * w ^ t.2).sum =
        (P.map fun t => t.1 * ((u ^ (t.2 + 1) - l ^ (t.2 + 1)) / (t.2 + 1))).sum := by
  induction P with
  | nil => simp
  | cons t P ih =>
    obtain ⟨c, j⟩ := t
    have i1 : IntervalIntegrable (fun w : ℝ => c * w ^ j) volume l u :=
      (continuous_const.mul (continuous_pow j)).intervalIntegrable _ _
    simp only [List.map_cons, List.sum_cons]
    refine ⟨i1.add ih.1, ?_⟩
    rw [integral_add i1 ih.1, intervalIntegral.integral_const_mul, integral_pow, ih.2]

theorem ksWP_intervalIntegrable_ksWPe (L : List (ℝ × ℕ × ℝ)) (P : List (ℝ × ℕ)) (l u : ℝ) :
    IntervalIntegrable (ksWPe L P) volume l u :=
  (ksWP_log_part L l u).1.add (ksWP_pow_part P l u).1

/-- **The integral of a polynomial-logarithmic combination.** -/
theorem ksWP_integral_ksWPe (L : List (ℝ × ℕ × ℝ)) (P : List (ℝ × ℕ)) (l u : ℝ) :
    ∫ w in l..u, ksWPe L P w = ksWPv L P l u := by
  unfold ksWPe ksWPv
  rw [integral_add (ksWP_log_part L l u).1 (ksWP_pow_part P l u).1, (ksWP_log_part L l u).2,
    (ksWP_pow_part P l u).2]

/-- A simple and a double pole at `p`: `c₁/(w - p) + c₂/(w - p)²`. -/
noncomputable def ksWPq (p c₁ c₂ w : ℝ) : ℝ := c₁ / (w - p) + c₂ / (w - p) ^ 2

/-- The primitive of `ksWPq p c₁ c₂` off `p`. -/
noncomputable def ksWPQ (p c₁ c₂ w : ℝ) : ℝ := c₁ * log (w - p) - c₂ / (w - p)

/-- **The integral of the pole terms** over an interval not containing the pole. -/
theorem ksWP_integral_ksWPq (p c₁ c₂ : ℝ) {l u : ℝ} (hp : p ∉ uIcc l u) :
    IntervalIntegrable (ksWPq p c₁ c₂) volume l u ∧
      ∫ w in l..u, ksWPq p c₁ c₂ w = ksWPQ p c₁ c₂ u - ksWPQ p c₁ c₂ l := by
  have hne : ∀ w ∈ uIcc l u, w - p ≠ 0 := fun w hw h => hp (sub_eq_zero.1 h ▸ hw)
  have hc : ContinuousOn (ksWPq p c₁ c₂) (uIcc l u) := by
    unfold ksWPq
    exact (continuousOn_const.div (continuousOn_id.sub continuousOn_const) hne).add
      (continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow 2)
        fun w hw => pow_ne_zero 2 (hne w hw))
  refine ⟨hc.intervalIntegrable, integral_eq_sub_of_hasDerivAt (fun w hw => ?_)
    hc.intervalIntegrable⟩
  have h0 := hne w hw
  have h1 := (((hasDerivAt_id w).sub_const p).log h0).const_mul c₁
  have h2 := (((hasDerivAt_id w).sub_const p).inv h0).const_mul c₂
  refine (h1.sub (h2.congr_deriv rfl)).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · simp only [ksWPq, id]
    field_simp
    ring
  · exact Filter.Eventually.of_forall fun x => by simp [ksWPQ, div_eq_mul_inv]

/-- A function equal to `ksWPe L P` on `(l, u)` has the integral `ksWPv L P l u`. -/
theorem ksWP_piece {f : ℝ → ℝ} (L : List (ℝ × ℕ × ℝ)) (P : List (ℝ × ℕ)) {l u : ℝ}
    (hlu : l ≤ u) (h : EqOn (ksWPe L P) f (Ioo l u)) :
    IntervalIntegrable f volume l u ∧ ∫ w in l..u, f w = ksWPv L P l u := by
  refine ⟨(ksWP_intervalIntegrable_ksWPe L P l u).congr_uIoo (uIoo_of_le hlu ▸ h), ?_⟩
  rw [← integral_congr_Ioo_of_le hlu h, ksWP_integral_ksWPe]

/-- A function equal to `ksWPe L P + ksWPq p c₁ c₂` on `(l, u)`, `p ∉ [l, u]`. -/
theorem ksWP_piece_q {f : ℝ → ℝ} (L : List (ℝ × ℕ × ℝ)) (P : List (ℝ × ℕ)) (p c₁ c₂ : ℝ)
    {l u : ℝ} (hlu : l ≤ u) (hp : p ∉ uIcc l u)
    (h : EqOn (fun w => ksWPe L P w + ksWPq p c₁ c₂ w) f (Ioo l u)) :
    IntervalIntegrable f volume l u ∧
      ∫ w in l..u, f w = ksWPv L P l u + (ksWPQ p c₁ c₂ u - ksWPQ p c₁ c₂ l) := by
  obtain ⟨iq, vq⟩ := ksWP_integral_ksWPq p c₁ c₂ hp
  have ie := ksWP_intervalIntegrable_ksWPe L P l u
  refine ⟨(ie.add iq).congr_uIoo (uIoo_of_le hlu ▸ h), ?_⟩
  rw [← integral_congr_Ioo_of_le hlu h, integral_add ie iq, ksWP_integral_ksWPe, vq]

/-- A function vanishing on `(l, u)` has integral zero there. -/
theorem ksWP_piece_zero {f : ℝ → ℝ} {l u : ℝ} (hlu : l ≤ u) (h : EqOn (fun _ => 0) f (Ioo l u)) :
    IntervalIntegrable f volume l u ∧ ∫ w in l..u, f w = 0 := by
  refine ⟨intervalIntegrable_const.congr_uIoo (uIoo_of_le hlu ▸ h), ?_⟩
  rw [← integral_congr_Ioo_of_le hlu h, intervalIntegral.integral_zero]

end QED.ChainProof.SetAKS

end
