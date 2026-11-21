/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLShuffle
public import QED.Polylog.LiN
public import QED.Polylog.Zeta5
import QED.Polylog.AlphabetPM
import QED.Polylog.ExtraIntegrals
import QED.Polylog.LiCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Harmonic polylogarithms of weight at most three in closed form

Closed forms on `(0, 1)` of the harmonic polylogarithms `QED.Polylog.HPL.hpl` of weight `1`
and `2` (all `3 + 9` words) in terms of `log` and the dilogarithm `Li 2`, and of the weight-3
words over `{0, 1}` and over `{0, -1}` (`8 + 7` words) in terms of `log`, `Li 2`, `Li 3` and
`ζ(3) = zeta3`. Words are written with `0`, `1`, `-1` for `Letter.zero`, `Letter.one`,
`Letter.negOne`.

Each Lyndon word is identified by the uniqueness theorem
`QED.Polylog.HPL.eq_hpl_cons_of_hasDerivAt` (matching derivative, limit `0` at `0⁺`); the
remaining words follow from the shuffle product `QED.Polylog.HPL.hpl_mul_hpl`.

## Main results

* weight 1: `H(0) = log x`, `H(1) = -log (1 - x)`, `H(-1) = log (1 + x)`;
* weight 2: `H(0, 1) = Li 2 x`, `H(0, -1) = -Li 2 (-x)`,
  `H(1, -1) = Li 2 ((1 - x)/2) - Li 2 (1/2) - log 2 log (1 - x)`,
  `H(-1, 1) = Li 2 ((1 + x)/2) - Li 2 (1/2) - log 2 log (1 + x)`, and the shuffle consequences;
* weight 3: `H(0, 0, 1) = Li 3 x`, `H(0, 0, -1) = -Li 3 (-x)`,
  `H(0, 1, 1) = ζ(3) - Li 3 (1 - x) + log (1 - x) Li 2 (1 - x) + log x log² (1 - x) / 2`,
  `H(0, -1, -1) = ζ(3) - Li 3 (1/(1 + x)) - log (1 + x) Li 2 (1/(1 + x)) - log³ (1 + x)/3
  + log x log² (1 + x) / 2`, and the shuffle consequences.
-/

public section

open Real Set Filter Topology

namespace QED.Polylog.HPL

open Letter

/-! ### Limits at `0⁺` -/

/-- A function continuous at `0` with value `c` tends to `c` at `0⁺`. -/
theorem tendsto_nhdsGT_of_continuousAt {F : ℝ → ℝ} {c : ℝ} (hF : ContinuousAt F 0)
    (h : F 0 = c) : Tendsto F (𝓝[>] 0) (𝓝 c) := by
  rw [← h]
  exact hF.tendsto.mono_left nhdsWithin_le_nhds

/-- `Li k (g x) → Li k (g 0)` at `0⁺` for `g` continuous at `0` with `g 0 ∈ [-1, 1]` and `g`
eventually in `[-1, 1]` at `0⁺`. -/
theorem tendsto_Li_comp_zero {k : ℕ} (hk : 2 ≤ k) {g : ℝ → ℝ} (hg : ContinuousAt g 0)
    (hg0 : g 0 ∈ Icc (-1 : ℝ) 1) (hgs : ∀ x ∈ Ioo (0 : ℝ) 1, g x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun x => Li k (g x)) (𝓝[>] 0) (𝓝 (Li k (g 0))) :=
  tendsto_Li_comp hk hg0 (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with x hx using hgs x hx)

/-- `log x log (1 + x) → 0` at `0⁺`. -/
theorem tendsto_log_mul_log_one_add_zero :
    Tendsto (fun x => log x * log (1 + x)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_mul_log_zero.mul tendsto_log_one_add_div_zero
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  field_simp

/-! ### Weight one -/

/-- The closed form of `H(0; x)`. -/
theorem hpl_zero (x : ℝ) : hpl [zero] x = log x := by
  simp [hpl_of_allZero (w := [zero]) (by simp)]

/-- The closed form of `H(1; x)` on `(0, 1)`. -/
theorem hpl_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : hpl [one] x = -log (1 - x) := by
  refine eq_hpl_cons_of_hasDerivAt (a := one) (w := []) (by simp)
    (F := fun y => -log (1 - y)) (fun y hy => ?_)
    (tendsto_nhdsGT_of_continuousAt (c := 0) (by fun_prop (disch := norm_num)) (by simp)) x hx
  have h1 : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
  refine (((hasDerivAt_id y).const_sub 1).log h1).neg.congr_deriv ?_
  simp only [kernel_one, hpl_nil, id]
  field_simp

/-- The closed form of `H(-1; x)` on `(0, 1)`. -/
theorem hpl_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : hpl [negOne] x = log (1 + x) := by
  refine eq_hpl_cons_of_hasDerivAt (a := negOne) (w := []) (by simp)
    (F := fun y => log (1 + y)) (fun y hy => ?_)
    (tendsto_nhdsGT_of_continuousAt (c := 0) (by fun_prop (disch := norm_num)) (by simp)) x hx
  have h1 : (1 : ℝ) + y ≠ 0 := by linarith [hy.1]
  refine (((hasDerivAt_id y).const_add 1).log h1).congr_deriv ?_
  simp only [kernel_negOne, hpl_nil, id]
  field_simp

/-! ### Weight two -/

/-- The closed form of `H(0, 0; x)`. -/
theorem hpl_zero_zero (x : ℝ) : hpl [zero, zero] x = log x ^ 2 / 2 := by
  simp [hpl_of_allZero (w := [zero, zero]) (by simp)]

/-- The closed form of `H(0, 1; x)` on `(0, 1)`. -/
theorem hpl_zero_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : hpl [zero, one] x = Li 2 x := by
  refine eq_hpl_cons_of_hasDerivAt (a := zero) (w := [one]) (by simp) (F := Li 2) (fun y hy => ?_)
    (by simpa using (tendsto_Li_comp_zero (g := id) le_rfl continuousAt_id (by simp)
      fun y hy => ⟨by show (-1 : ℝ) ≤ y; linarith [hy.1], hy.2.le⟩)) x hx
  have hy1 : |y| < 1 := abs_lt.2 ⟨by linarith [hy.1], hy.2⟩
  refine (hasDerivAt_Li (k := 2) (by norm_num) hy1 hy.1.ne').congr_deriv ?_
  rw [kernel_zero, hpl_one hy, show 2 - 1 = 1 from rfl, Li_one hy1]
  field_simp

/-- The closed form of `H(0, -1; x)` on `(0, 1)`. -/
theorem hpl_zero_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne] x = -Li 2 (-x) := by
  refine eq_hpl_cons_of_hasDerivAt (a := zero) (w := [negOne]) (by simp)
    (F := fun y => -Li 2 (-y)) (fun y hy => ?_)
    (by simpa using (tendsto_Li_comp_zero (g := fun y => -y) le_rfl continuousAt_neg (by simp)
      fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩).neg) x hx
  obtain ⟨hf, h1, h0, -, -, -⟩ := PM.data_neg hy.1 hy.2
  refine (hasDerivAt_Li_two_comp hf h1 h0).neg.congr_deriv ?_
  rw [kernel_zero, hpl_negOne hy, sub_neg_eq_add]
  field_simp

/-- The closed form of `H(1, 1; x)` on `(0, 1)`. -/
theorem hpl_one_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : hpl [one, one] x = log (1 - x) ^ 2 / 2 := by
  have h := hpl_mul_hpl [one] [one] hx
  simp [shuffle, shuffleAux, hpl_one hx] at h
  linarith

/-- The closed form of `H(-1, -1; x)` on `(0, 1)`. -/
theorem hpl_negOne_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, negOne] x = log (1 + x) ^ 2 / 2 := by
  have h := hpl_mul_hpl [negOne] [negOne] hx
  simp [shuffle, shuffleAux, hpl_negOne hx] at h
  linarith

/-- The closed form of `H(1, 0; x)` on `(0, 1)`. -/
theorem hpl_one_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero] x = -log x * log (1 - x) - Li 2 x := by
  have h := hpl_mul_hpl [one] [zero] hx
  simp [shuffle, shuffleAux, hpl_one hx, hpl_zero, hpl_zero_one hx] at h
  linarith

/-- The closed form of `H(-1, 0; x)` on `(0, 1)`. -/
theorem hpl_negOne_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, zero] x = log x * log (1 + x) + Li 2 (-x) := by
  have h := hpl_mul_hpl [negOne] [zero] hx
  simp [shuffle, shuffleAux, hpl_negOne hx, hpl_zero, hpl_zero_negOne hx] at h
  linarith

/-- The closed form of `H(1, -1; x)` on `(0, 1)`. -/
theorem hpl_one_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, negOne] x = Li 2 ((1 - x) / 2) - Li 2 (1 / 2) - log 2 * log (1 - x) := by
  refine eq_hpl_cons_of_hasDerivAt (a := one) (w := [negOne]) (by simp)
    (F := fun y => Li 2 ((1 - y) / 2) - Li 2 (1 / 2) - log 2 * log (1 - y)) (fun y hy => ?_)
    ?_ x hx
  · obtain ⟨hf, h1, h0, hd, -, hl1⟩ := PM.data_halfOneSub hy.1 hy.2
    have hL := hasDerivAt_Li_two_of hf h1 h0 hd hl1
    have h1y : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
    have hlog := ((hasDerivAt_id y).const_sub 1).log h1y
    refine ((hL.sub_const _).sub (hlog.const_mul (log 2))).congr_deriv ?_
    rw [kernel_one, hpl_negOne hy]
    simp only [id]
    field_simp
    ring
  · have h := ((tendsto_Li_comp_zero (g := fun y => (1 - y) / 2) le_rfl (by fun_prop)
      (by norm_num) fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩).sub_const
      (Li 2 (1 / 2))).sub ((tendsto_nhdsGT_of_continuousAt (F := fun y => log (1 - y))
      (c := 0) (by fun_prop (disch := norm_num)) (by simp)).const_mul (log 2))
    simpa using h

/-- The closed form of `H(-1, 1; x)` on `(0, 1)`. -/
theorem hpl_negOne_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, one] x = Li 2 ((1 + x) / 2) - Li 2 (1 / 2) - log 2 * log (1 + x) := by
  refine eq_hpl_cons_of_hasDerivAt (a := negOne) (w := [one]) (by simp)
    (F := fun y => Li 2 ((1 + y) / 2) - Li 2 (1 / 2) - log 2 * log (1 + y)) (fun y hy => ?_)
    ?_ x hx
  · obtain ⟨hf, h1, h0, hd, -, hl1⟩ := PM.data_halfOneAdd hy.1 hy.2
    have hL := hasDerivAt_Li_two_of hf h1 h0 hd hl1
    have h1y : (1 : ℝ) + y ≠ 0 := by linarith [hy.1]
    have hlog := ((hasDerivAt_id y).const_add 1).log h1y
    refine ((hL.sub_const _).sub (hlog.const_mul (log 2))).congr_deriv ?_
    rw [kernel_negOne, hpl_one hy]
    simp only [id]
    field_simp
    ring
  · have h := ((tendsto_Li_comp_zero (g := fun y => (1 + y) / 2) le_rfl (by fun_prop)
      (by norm_num) fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩).sub_const
      (Li 2 (1 / 2))).sub ((tendsto_nhdsGT_of_continuousAt (F := fun y => log (1 + y))
      (c := 0) (by fun_prop (disch := norm_num)) (by simp)).const_mul (log 2))
    simpa using h

/-! ### Weight three over `{0, 1}` -/

/-- The closed form of `H(0, 0, 0; x)`. -/
theorem hpl_zero_zero_zero (x : ℝ) : hpl [zero, zero, zero] x = log x ^ 3 / 6 := by
  simp [hpl_of_allZero (w := [zero, zero, zero]) (by simp), Nat.factorial]

/-- The closed form of `H(0, 0, 1; x)` on `(0, 1)`. -/
theorem hpl_zero_zero_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, zero, one] x = Li 3 x := by
  refine eq_hpl_cons_of_hasDerivAt (a := zero) (w := [zero, one]) (by simp)
    (F := Li 3) (fun y hy => ?_)
    (by simpa using (tendsto_Li_comp_zero (k := 3) (g := id) (by norm_num) continuousAt_id
      (by simp) fun y hy => ⟨by show (-1 : ℝ) ≤ y; linarith [hy.1], hy.2.le⟩)) x hx
  have hy1 : |y| < 1 := abs_lt.2 ⟨by linarith [hy.1], hy.2⟩
  refine (hasDerivAt_Li (k := 3) (by norm_num) hy1 hy.1.ne').congr_deriv ?_
  rw [kernel_zero, hpl_zero_one hy, show 3 - 1 = 2 from rfl]
  field_simp

/-- `H(0, 1, 1; x) = S₁,₂(x)`, through `Li 3 (1 - x)`. -/
theorem hpl_zero_one_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, one] x = zeta3 - Li 3 (1 - x) + log (1 - x) * Li 2 (1 - x) +
      log x * log (1 - x) ^ 2 / 2 := by
  refine eq_hpl_cons_of_hasDerivAt (a := zero) (w := [one, one]) (by simp)
    (F := fun y => zeta3 - Li 3 (1 - y) + log (1 - y) * Li 2 (1 - y) +
      log y * log (1 - y) ^ 2 / 2) (fun y hy => ?_) ?_ x hx
  · obtain ⟨hf, h1, h0, hd, -, hl1⟩ := PM.data_oneSub hy.1 hy.2
    have h3 := hasDerivAt_Li_three_of hf h1 h0 hd rfl
    have h2 := hasDerivAt_Li_two_of hf h1 h0 hd hl1
    have hl := hf.log h0
    have hlx := hasDerivAt_log hy.1.ne'
    refine ((((hasDerivAt_const y zeta3).sub h3).add (hl.mul h2)).add
      ((hlx.mul (hl.pow 2)).div_const 2)).congr_deriv ?_
    rw [kernel_zero, hpl_one_one hy]
    simp only [Pi.pow_apply]
    have h1y : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
    have hy0 : y ≠ 0 := hy.1.ne'
    field_simp
    ring
  · have hmem : ∀ y ∈ Ioo (0 : ℝ) 1, 1 - y ∈ Icc (-1 : ℝ) 1 :=
      fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have t3 := tendsto_Li_comp_zero (k := 3) (g := fun y => 1 - y) (by norm_num) (by fun_prop)
      (by norm_num) hmem
    have t2 := tendsto_Li_comp_zero (k := 2) (g := fun y => 1 - y) le_rfl (by fun_prop)
      (by norm_num) hmem
    have tl := tendsto_nhdsGT_of_continuousAt (F := fun y => log (1 - y))
      (c := 0) (by fun_prop (disch := norm_num)) (by simp)
    have h := (((tendsto_const_nhds (x := zeta3)).sub t3).add (tl.mul t2)).add
      ((tendsto_log_mul_log_one_sub_zero.mul tl).div_const 2)
    simp only [sub_zero, Li_three_one, sub_self, zero_mul, zero_div, add_zero] at h
    refine h.congr' (Eventually.of_forall fun y => ?_)
    ring

/-- The closed form of `H(0, 1, 0; x)` on `(0, 1)`. -/
theorem hpl_zero_one_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, one, zero] x = log x * Li 2 x - 2 * Li 3 x := by
  have h := hpl_mul_hpl [zero] [zero, one] hx
  simp [shuffle, shuffleAux, hpl_zero, hpl_zero_one hx, hpl_zero_zero_one hx] at h
  linarith

/-- The closed form of `H(1, 0, 0; x)` on `(0, 1)`. -/
theorem hpl_one_zero_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero, zero] x = -log x ^ 2 * log (1 - x) / 2 - log x * Li 2 x + Li 3 x := by
  have h := hpl_mul_hpl [zero, zero] [one] hx
  simp [shuffle, shuffleAux, hpl_zero_zero, hpl_one hx, hpl_zero_zero_one hx,
    hpl_zero_one_zero hx] at h
  linarith

/-- The closed form of `H(1, 0, 1; x)` on `(0, 1)`. -/
theorem hpl_one_zero_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, zero, one] x = -log (1 - x) * Li 2 x - 2 * hpl [zero, one, one] x := by
  have h := hpl_mul_hpl [one] [zero, one] hx
  simp [shuffle, shuffleAux, hpl_one hx, hpl_zero_one hx] at h
  linarith

/-- The closed form of `H(1, 1, 0; x)` on `(0, 1)`. -/
theorem hpl_one_one_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, zero] x = log x * log (1 - x) ^ 2 / 2 + log (1 - x) * Li 2 x +
      hpl [zero, one, one] x := by
  have h := hpl_mul_hpl [zero] [one, one] hx
  simp [shuffle, shuffleAux, hpl_zero, hpl_one_one hx, hpl_one_zero_one hx] at h
  linarith

/-- The closed form of `H(1, 1, 1; x)` on `(0, 1)`. -/
theorem hpl_one_one_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [one, one, one] x = -log (1 - x) ^ 3 / 6 := by
  have h := hpl_mul_hpl [one] [one, one] hx
  simp [shuffle, shuffleAux, hpl_one hx, hpl_one_one hx] at h
  linarith

/-! ### Weight three over `{0, -1}` -/

/-- The closed form of `H(0, 0, -1; x)` on `(0, 1)`. -/
theorem hpl_zero_zero_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, zero, negOne] x = -Li 3 (-x) := by
  refine eq_hpl_cons_of_hasDerivAt (a := zero) (w := [zero, negOne]) (by simp)
    (F := fun y => -Li 3 (-y)) (fun y hy => ?_)
    (by simpa using (tendsto_Li_comp_zero (k := 3) (g := fun y => -y) (by norm_num)
      continuousAt_neg (by simp) fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩).neg)
    x hx
  obtain ⟨hf, h1, h0, hd, -, -⟩ := PM.data_neg hy.1 hy.2
  refine (hasDerivAt_Li_three_of hf h1 h0 hd rfl).neg.congr_deriv ?_
  rw [kernel_zero, hpl_zero_negOne hy]
  field_simp

/-- `H(0, -1, -1; x) = S₁,₂(-x)`, through `Li 3 (1 / (1 + x))`. -/
theorem hpl_zero_negOne_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne, negOne] x = zeta3 - Li 3 (1 / (1 + x)) -
      log (1 + x) * Li 2 (1 / (1 + x)) - log (1 + x) ^ 3 / 3 +
      log x * log (1 + x) ^ 2 / 2 := by
  refine eq_hpl_cons_of_hasDerivAt (a := zero) (w := [negOne, negOne]) (by simp)
    (F := fun y => zeta3 - Li 3 (1 / (1 + y)) - log (1 + y) * Li 2 (1 / (1 + y)) -
      log (1 + y) ^ 3 / 3 + log y * log (1 + y) ^ 2 / 2) (fun y hy => ?_) ?_ x hx
  · obtain ⟨hf, h1, h0, hd, -, hl1⟩ := PM.data_invOneAdd hy.1 hy.2
    have h3 := hasDerivAt_Li_three_of hf h1 h0 hd rfl
    have h2 := hasDerivAt_Li_two_of hf h1 h0 hd hl1
    have h1y : (1 : ℝ) + y ≠ 0 := by linarith [hy.1]
    have hl := ((hasDerivAt_id y).const_add 1).log h1y
    have hlx := hasDerivAt_log hy.1.ne'
    refine (((((hasDerivAt_const y zeta3).sub h3).sub (hl.mul h2)).sub
      ((hl.pow 3).div_const 3)).add ((hlx.mul (hl.pow 2)).div_const 2)).congr_deriv ?_
    rw [kernel_zero, hpl_negOne_negOne hy]
    simp only [id, Pi.pow_apply]
    have hy0 : y ≠ 0 := hy.1.ne'
    field_simp
    ring
  · have hmem : ∀ y ∈ Ioo (0 : ℝ) 1, 1 / (1 + y) ∈ Icc (-1 : ℝ) 1 := fun y hy =>
      ⟨by have : 0 < 1 / (1 + y) := by have := hy.1; positivity
          linarith,
        by rw [div_le_one (by linarith [hy.1])]; linarith [hy.1]⟩
    have hc : ContinuousAt (fun y : ℝ => 1 / (1 + y)) 0 := by fun_prop (disch := norm_num)
    have t3 := tendsto_Li_comp_zero (k := 3) (g := fun y => 1 / (1 + y)) (by norm_num) hc
      (by norm_num) hmem
    have t2 := tendsto_Li_comp_zero (k := 2) (g := fun y => 1 / (1 + y)) le_rfl hc
      (by norm_num) hmem
    have tl := tendsto_nhdsGT_of_continuousAt (F := fun y => log (1 + y))
      (c := 0) (by fun_prop (disch := norm_num)) (by simp)
    have h := (((((tendsto_const_nhds (x := zeta3)).sub t3).sub (tl.mul t2)).sub
      ((tl.pow 3).div_const 3)).add ((tendsto_log_mul_log_one_add_zero.mul tl).div_const 2))
    simp only [add_zero, div_one, Li_three_one, sub_self, zero_mul, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] at h
    refine h.congr' (Eventually.of_forall fun y => ?_)
    ring

/-- The closed form of `H(0, -1, 0; x)` on `(0, 1)`. -/
theorem hpl_zero_negOne_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne, zero] x = -log x * Li 2 (-x) + 2 * Li 3 (-x) := by
  have h := hpl_mul_hpl [zero] [zero, negOne] hx
  simp [shuffle, shuffleAux, hpl_zero, hpl_zero_negOne hx, hpl_zero_zero_negOne hx] at h
  linarith

/-- The closed form of `H(-1, 0, 0; x)` on `(0, 1)`. -/
theorem hpl_negOne_zero_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, zero, zero] x =
      log x ^ 2 * log (1 + x) / 2 + log x * Li 2 (-x) - Li 3 (-x) := by
  have h := hpl_mul_hpl [zero, zero] [negOne] hx
  simp [shuffle, shuffleAux, hpl_zero_zero, hpl_negOne hx, hpl_zero_zero_negOne hx,
    hpl_zero_negOne_zero hx] at h
  linarith

/-- The closed form of `H(-1, 0, -1; x)` on `(0, 1)`. -/
theorem hpl_negOne_zero_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, zero, negOne] x =
      -log (1 + x) * Li 2 (-x) - 2 * hpl [zero, negOne, negOne] x := by
  have h := hpl_mul_hpl [negOne] [zero, negOne] hx
  simp [shuffle, shuffleAux, hpl_negOne hx, hpl_zero_negOne hx] at h
  linarith

/-- The closed form of `H(-1, -1, 0; x)` on `(0, 1)`. -/
theorem hpl_negOne_negOne_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, negOne, zero] x = log x * log (1 + x) ^ 2 / 2 + log (1 + x) * Li 2 (-x) +
      hpl [zero, negOne, negOne] x := by
  have h := hpl_mul_hpl [zero] [negOne, negOne] hx
  simp [shuffle, shuffleAux, hpl_zero, hpl_negOne_negOne hx, hpl_negOne_zero_negOne hx] at h
  linarith

/-- The closed form of `H(-1, -1, -1; x)` on `(0, 1)`. -/
theorem hpl_negOne_negOne_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [negOne, negOne, negOne] x = log (1 + x) ^ 3 / 6 := by
  have h := hpl_mul_hpl [negOne] [negOne, negOne] hx
  simp [shuffle, shuffleAux, hpl_negOne hx, hpl_negOne_negOne hx] at h
  linarith

end QED.Polylog.HPL
