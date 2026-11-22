/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Set (d), master `I₁₅`: finite sums of harmonic polylogarithms with polynomial coefficients

The outer integrals of the third Taylor coefficient of `K` are integrals over `(0, 1)` of
`HPL` combinations `Σ qₜ(u) H(wₜ; u)`, where each `qₜ(u) = a/u + b + c u + d u²`. This file
packages such sums as lists of coefficient-word pairs and proves, once and for all,

* the derivative `d/du Σ qₜ H(wₜ) = Σ (qₜ' H(wₜ) + qₜ H'(wₜ))` on `(0, 1)`;
* the limit `0` at `0⁺` when each term is a non-all-zero word or has `a = b = 0`;
* the limit `Σ qₜ(1) H(wₜ; 1)` at `1⁻` when every word starting with `1` has `qₜ(1) = 0`.

## Main definitions

* `QED.ThreeLoopD.i15T3q`: the coefficient `a/u + b + c u + d u²`.
* `QED.ThreeLoopD.i15T3Sum`: the sum `Σ qₜ(u) H(wₜ; u)` over a list.
* `QED.ThreeLoopD.i15T3SumD`: its derivative.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i15T3Sum`, `QED.ThreeLoopD.tendsto_i15T3Sum_zero`,
  `QED.ThreeLoopD.tendsto_i15T3Sum_one`.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog.HPL

namespace QED.ThreeLoopD

/-- The coefficient `a/u + b + c u + d u²` of a term, `t = (a, b, c, d)`. -/
noncomputable def i15T3q (t : ℝ × ℝ × ℝ × ℝ) (u : ℝ) : ℝ :=
  t.1 / u + t.2.1 + t.2.2.1 * u + t.2.2.2 * u ^ 2

/-- Its derivative `-a/u² + c + 2 d u`. -/
noncomputable def i15T3q' (t : ℝ × ℝ × ℝ × ℝ) (u : ℝ) : ℝ :=
  -(t.1 / u ^ 2) + t.2.2.1 + 2 * t.2.2.2 * u

/-- The derivative of `H(w)`: `0` for the empty word, `f a · H(w')` for `w = a · w'`. -/
noncomputable def i15T3hd : List Letter → ℝ → ℝ
  | [], _ => 0
  | a :: w, u => a.kernel u * hpl w u

/-- The sum `Σ qₜ(u) H(wₜ; u)`. -/
noncomputable def i15T3Sum (L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter)) (u : ℝ) : ℝ :=
  (L.map fun t => i15T3q t.1 u * hpl t.2 u).sum

/-- Its derivative `Σ (qₜ' H(wₜ) + qₜ H'(wₜ))`. -/
noncomputable def i15T3SumD (L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter)) (u : ℝ) : ℝ :=
  (L.map fun t => i15T3q' t.1 u * hpl t.2 u + i15T3q t.1 u * i15T3hd t.2 u).sum

@[simp] theorem i15T3Sum_nil (u : ℝ) : i15T3Sum [] u = 0 := rfl

@[simp] theorem i15T3Sum_cons (t : (ℝ × ℝ × ℝ × ℝ) × List Letter)
    (L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter)) (u : ℝ) :
    i15T3Sum (t :: L) u = i15T3q t.1 u * hpl t.2 u + i15T3Sum L u := by
  simp [i15T3Sum]

@[simp] theorem i15T3SumD_nil (u : ℝ) : i15T3SumD [] u = 0 := rfl

@[simp] theorem i15T3SumD_cons (t : (ℝ × ℝ × ℝ × ℝ) × List Letter)
    (L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter)) (u : ℝ) :
    i15T3SumD (t :: L) u =
      i15T3q' t.1 u * hpl t.2 u + i15T3q t.1 u * i15T3hd t.2 u + i15T3SumD L u := by
  simp [i15T3SumD]

theorem hasDerivAt_i15T3q (t : ℝ × ℝ × ℝ × ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (i15T3q t) (i15T3q' t u) u := by
  have h := (((hasDerivAt_inv hu).const_mul t.1).add_const t.2.1).add
    (((hasDerivAt_id' u).const_mul t.2.2.1).add ((hasDerivAt_pow 2 u).const_mul t.2.2.2))
  have e : i15T3q t = fun y => t.1 * y⁻¹ + t.2.1 + (t.2.2.1 * y + t.2.2.2 * y ^ 2) :=
    funext fun y => by simp only [i15T3q]; ring
  rw [e]
  exact h.congr_deriv (by simp only [i15T3q']; field_simp; ring)

theorem hasDerivAt_hpl_i15T3hd (w : List Letter) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (hpl w) (i15T3hd w u) u := by
  cases w with
  | nil =>
    rw [show hpl [] = fun _ => 1 from funext hpl_nil]
    exact hasDerivAt_const u (1 : ℝ)
  | cons a w => exact hasDerivAt_hpl_cons a w hu

theorem hasDerivAt_i15T3Sum (L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter)) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivAt (i15T3Sum L) (i15T3SumD L u) u := by
  induction L with
  | nil =>
    rw [show i15T3Sum [] = fun _ => 0 from funext fun _ => rfl]
    exact hasDerivAt_const u (0 : ℝ)
  | cons t L ih =>
    have h := (HasDerivAt.mul (hasDerivAt_i15T3q t.1 hu.1.ne')
      (hasDerivAt_hpl_i15T3hd t.2 hu)).add ih
    rw [show i15T3Sum (t :: L) = fun u => i15T3q t.1 u * hpl t.2 u + i15T3Sum L u from
      funext fun u => i15T3Sum_cons t L u]
    exact h.congr_deriv (by simp)

/-! ### Limits -/

/-- `u H(w; u) → 0` as `u → 0⁺`, for every word. -/
theorem tendsto_mul_hpl_zero (w : List Letter) :
    Tendsto (fun u => u * hpl w u) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, -, h⟩ := abs_hpl_le_rpow_neg w (δ := 1 / 2) (by norm_num) (b := 1 / 2)
    (by norm_num)
  refine tendsto_zero_of_abs_le_rpow (C := C) (r := 1 / 2) (b := 1 / 2) (by norm_num)
    (by norm_num) fun t ht => ?_
  have ht0 := ht.1
  rw [abs_mul, abs_of_pos ht0]
  calc t * |hpl w t| ≤ t * (C * t ^ (-(1 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left (h t ht) ht0.le
    _ = C * (t ^ (1 : ℝ) * t ^ (-(1 / 2) : ℝ)) := by rw [rpow_one]; ring
    _ = C * t ^ (1 / 2 : ℝ) := by rw [← rpow_add ht0]; norm_num

/-- `(1 - u) H(w; u) → 0` as `u → 1⁻`, for every word. -/
theorem tendsto_one_sub_mul_hpl_one (w : List Letter) :
    Tendsto (fun u => (1 - u) * hpl w u) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨C, -, h⟩ := abs_hpl_le_one_sub_rpow w (ε := 1 / 2) (by norm_num)
  have hC : Tendsto (fun u : ℝ => C * (1 - u) ^ (1 / 2 : ℝ)) (𝓝[<] 1) (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => 1 - u) (𝓝[<] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 (1 - 1)) :=
          (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with u (hu : u < 1)
        exact sub_pos.2 hu
    simpa using ((tendsto_rpow_nhdsGT_zero (r := 1 / 2) (by norm_num)).comp h1).const_mul C
  refine squeeze_zero_norm' ?_ hC
  filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with t ht
  have h1t : 0 < 1 - t := by linarith [ht.2]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos h1t]
  calc (1 - t) * |hpl w t| ≤ (1 - t) * (C * (1 - t) ^ (-(1 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left (h t ⟨ht.1.le, ht.2⟩) h1t.le
    _ = C * ((1 - t) ^ (1 : ℝ) * (1 - t) ^ (-(1 / 2) : ℝ)) := by rw [rpow_one]; ring
    _ = C * (1 - t) ^ (1 / 2 : ℝ) := by rw [← rpow_add h1t]; norm_num

theorem tendsto_i15T3q_mul_hpl_zero {t : ℝ × ℝ × ℝ × ℝ} {w : List Letter} (ha : t.1 = 0)
    (h : ¬AllZero w ∨ t.2.1 = 0) :
    Tendsto (fun u => i15T3q t u * hpl w u) (𝓝[>] 0) (𝓝 0) := by
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hm := tendsto_mul_hpl_zero w
  have e : ∀ u, i15T3q t u * hpl w u =
      t.2.1 * hpl w u + (t.2.2.1 + t.2.2.2 * u) * (u * hpl w u) := by
    intro u; simp only [i15T3q, ha, zero_div, zero_add]; ring
  simp only [e]
  have h2 : Tendsto (fun u => (t.2.2.1 + t.2.2.2 * u) * (u * hpl w u)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.add (hx0.const_mul t.2.2.2)).mul hm
  rcases h with hw | hb
  · simpa using ((tendsto_hpl_zero hw).const_mul t.2.1).add h2
  · simpa [hb] using h2

theorem tendsto_i15T3Sum_zero {L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter)}
    (h : ∀ t ∈ L, t.1.1 = 0 ∧ (¬AllZero t.2 ∨ t.1.2.1 = 0)) :
    Tendsto (i15T3Sum L) (𝓝[>] 0) (𝓝 0) := by
  induction L with
  | nil =>
    rw [show i15T3Sum [] = fun _ => 0 from funext fun _ => rfl]
    exact tendsto_const_nhds
  | cons t L ih =>
    have h1 := h t List.mem_cons_self
    have h2 := ih fun s hs => h s (List.mem_cons_of_mem t hs)
    have := (tendsto_i15T3q_mul_hpl_zero h1.1 h1.2).add h2
    rw [show i15T3Sum (t :: L) = fun u => i15T3q t.1 u * hpl t.2 u + i15T3Sum L u from
      funext fun u => i15T3Sum_cons t L u]
    simpa using this

theorem tendsto_i15T3q_mul_hpl_one (t : ℝ × ℝ × ℝ × ℝ) (w : List Letter)
    (h : w.head? = some Letter.one → i15T3q t 1 = 0) :
    Tendsto (fun u => i15T3q t u * hpl w u) (𝓝[<] 1) (𝓝 (i15T3q t 1 * hpl w 1)) := by
  have hq : ContinuousAt (i15T3q t) 1 := (hasDerivAt_i15T3q t one_ne_zero).continuousAt
  have hq' : Tendsto (i15T3q t) (𝓝[<] 1) (𝓝 (i15T3q t 1)) :=
    hq.tendsto.mono_left nhdsWithin_le_nhds
  cases w with
  | nil => simpa using hq'
  | cons a w =>
    by_cases ha : a = Letter.one
    · subst ha
      have h0 := h rfl
      rw [h0, zero_mul]
      have e : ∀ u, u ≠ 0 → i15T3q t u * hpl (Letter.one :: w) u =
          -((t.2.2.2 * u + t.2.2.1 + t.2.2.2 - t.1 / u) *
            ((1 - u) * hpl (Letter.one :: w) u)) := by
        intro u hu
        have h0' : t.1 + t.2.1 + t.2.2.1 + t.2.2.2 = 0 := by
          simpa [i15T3q] using h0
        have : t.2.1 = -(t.1 + t.2.2.1 + t.2.2.2) := by linarith
        simp only [i15T3q, this]
        field_simp
        ring
      have hc : Tendsto (fun u : ℝ => t.2.2.2 * u + t.2.2.1 + t.2.2.2 - t.1 / u) (𝓝[<] 1)
          (𝓝 (t.2.2.2 * 1 + t.2.2.1 + t.2.2.2 - t.1 / 1)) := by
        have : ContinuousAt (fun u : ℝ => t.2.2.2 * u + t.2.2.1 + t.2.2.2 - t.1 / u) 1 := by
          fun_prop (disch := norm_num)
        exact this.tendsto.mono_left nhdsWithin_le_nhds
      have hl := (hc.mul (tendsto_one_sub_mul_hpl_one (Letter.one :: w))).neg
      rw [mul_zero, neg_zero] at hl
      refine hl.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with u hu
      exact (e u hu.1.ne').symm
    · exact hq'.mul (tendsto_hpl_one ha w)

theorem tendsto_i15T3Sum_one {L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter)}
    (h : ∀ t ∈ L, t.2.head? = some Letter.one → i15T3q t.1 1 = 0) :
    Tendsto (i15T3Sum L) (𝓝[<] 1) (𝓝 ((L.map fun t => i15T3q t.1 1 * hpl t.2 1).sum)) := by
  induction L with
  | nil =>
    rw [show i15T3Sum [] = fun _ => 0 from funext fun _ => rfl]
    exact tendsto_const_nhds
  | cons t L ih =>
    have h1 := h t List.mem_cons_self
    have h2 := ih fun s hs => h s (List.mem_cons_of_mem t hs)
    have := (tendsto_i15T3q_mul_hpl_one t.1 t.2 h1).add h2
    rw [show i15T3Sum (t :: L) = fun u => i15T3q t.1 u * hpl t.2 u + i15T3Sum L u from
      funext fun u => i15T3Sum_cons t L u]
    exact this

end QED.ThreeLoopD
