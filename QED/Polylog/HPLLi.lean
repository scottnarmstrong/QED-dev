/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLValues
import QED.Polylog.LiCalculus

/-!
# The classical polylogarithms as harmonic polylogarithms

For every `k ≥ 0`, the words `0ᵏ · 1` and `0ᵏ · (-1)` give the classical polylogarithms:
`H(0ᵏ, 1; x) = Li_{k+1}(x)` and `H(0ᵏ, -1; x) = -Li_{k+1}(-x)` on `(0, 1)`. Both are proved by
induction on `k` with the uniqueness theorem `QED.Polylog.HPL.eq_hpl_cons_of_hasDerivAt`. At
`x = 1` this gives `H(0ᵏ, 1; 1) = Li_{k+1}(1) = ζ(k + 1)` and `H(0ᵏ, -1; 1) = -Li_{k+1}(-1)`
for `k ≥ 1`.

## Main results

* `QED.Polylog.HPL.hpl_replicate_zero_one`: `H(0ᵏ, 1; x) = Li (k + 1) x`.
* `QED.Polylog.HPL.hpl_replicate_zero_negOne`: `H(0ᵏ, -1; x) = -Li (k + 1) (-x)`.
* `QED.Polylog.HPL.hpl_replicate_zero_one_at_one`,
  `QED.Polylog.HPL.hpl_replicate_zero_negOne_at_one`: the values at `1`.
-/

public section

open Real Set Filter Topology

namespace QED.Polylog.HPL

open Letter

/-- `H(0ᵏ, 1; x) = Li_{k+1}(x)` on `(0, 1)`. -/
theorem hpl_replicate_zero_one (k : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl (List.replicate k zero ++ [one]) x = Li (k + 1) x := by
  induction k generalizing x with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, zero_add]
    rw [hpl_one hx, Li_one (abs_lt.2 ⟨by linarith [hx.1], hx.2⟩)]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    refine eq_hpl_cons_of_hasDerivAt (by simp [AllZero]) (F := Li (k + 2)) (fun y hy => ?_)
      (by simpa using (tendsto_Li_comp_zero (k := k + 2) (g := id) (by omega) continuousAt_id
        (by simp) fun y hy => ⟨by show (-1 : ℝ) ≤ y; linarith [hy.1], hy.2.le⟩)) x hx
    have hy1 : |y| < 1 := abs_lt.2 ⟨by linarith [hy.1], hy.2⟩
    refine (hasDerivAt_Li (k := k + 2) (by omega) hy1 hy.1.ne').congr_deriv ?_
    rw [kernel_zero, ih hy, show k + 2 - 1 = k + 1 from rfl]
    field_simp

/-- `H(0ᵏ, -1; x) = -Li_{k+1}(-x)` on `(0, 1)`. -/
theorem hpl_replicate_zero_negOne (k : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl (List.replicate k zero ++ [negOne]) x = -Li (k + 1) (-x) := by
  induction k generalizing x with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, zero_add]
    rw [hpl_negOne hx, Li_one (abs_lt.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩)]
    simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    refine eq_hpl_cons_of_hasDerivAt (by simp [AllZero]) (F := fun y => -Li (k + 2) (-y))
      (fun y hy => ?_)
      (by simpa using (tendsto_Li_comp_zero (k := k + 2) (g := fun y => -y) (by omega)
        continuousAt_neg (by simp)
        fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩).neg) x hx
    have hy1 : |-y| < 1 := by rw [abs_neg]; exact abs_lt.2 ⟨by linarith [hy.1], hy.2⟩
    have hy0 : -y ≠ 0 := neg_ne_zero.2 hy.1.ne'
    refine (hasDerivAt_Li_comp (k := k + 2) (by omega) (hasDerivAt_id y).neg hy1
      hy0).neg.congr_deriv ?_
    rw [kernel_zero, ih hy, show k + 2 - 1 = k + 1 from rfl]
    have : y ≠ 0 := hy.1.ne'
    simp only [Pi.neg_apply, id]
    field_simp

/-- `H(0ᵏ, 1; 1) = Li_{k+1}(1) = ζ(k + 1)` for `k ≥ 1`. -/
theorem hpl_replicate_zero_one_at_one {k : ℕ} (hk : 1 ≤ k) :
    hpl (List.replicate k zero ++ [one]) 1 = Li (k + 1) 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [List.replicate_succ, List.cons_append]
  exact hpl_one_eq_of_tendsto (by simp) (fun x hx => by
    rw [← List.cons_append, ← List.replicate_succ]; exact hpl_replicate_zero_one _ hx)
    (tendsto_Li_one_left (by omega))

/-- `H(0ᵏ, -1; 1) = -Li_{k+1}(-1)` for `k ≥ 1`. -/
theorem hpl_replicate_zero_negOne_at_one {k : ℕ} (hk : 1 ≤ k) :
    hpl (List.replicate k zero ++ [negOne]) 1 = -Li (k + 1) (-1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [List.replicate_succ, List.cons_append]
  exact hpl_one_eq_of_tendsto (by simp) (fun x hx => by
    rw [← List.cons_append, ← List.replicate_succ]; exact hpl_replicate_zero_negOne _ hx)
    (tendsto_Li_neg_one_left (by omega)).neg

end QED.Polylog.HPL
