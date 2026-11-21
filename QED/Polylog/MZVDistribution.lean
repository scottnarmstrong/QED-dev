/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.MZVHPL

/-!
# The distribution relation of alternating multiple zeta values

Summing over all sign patterns kills the odd summation indices:
`∑_{σ ∈ {±1}ᵏ} ζ(s₁, …, s_k; σ) = 2^{k - (s₁ + ⋯ + s_k)} ζ(s₁, …, s_k)` for `s₁ ≥ 2`,
`sⱼ ≥ 1`. It holds exactly at every truncation (`∑_σ Z_M(s; σ) = 2^{k-|s|} Z_{⌈M/2⌉}(s)`),
since `∏ⱼ (1 + (-1)^{nⱼ}) = 2ᵏ [all nⱼ even]` and `(2m)^{-s} = 2^{-s} m^{-s}`.

## Main definitions

* `QED.Polylog.MZV.signedLists`: all sign patterns over an exponent list.
* `QED.Polylog.MZV.unsignedList`: the exponent list with all signs `+1`.

## Main results

* `QED.Polylog.MZV.sum_signedLists_nestedSum`: the truncated distribution relation.
* `QED.Polylog.MZV.sum_signedLists_mzv`: the distribution relation.
* `QED.Polylog.MZV.sum_signedLists_hpl_one`: the same in HPL words.
-/

@[expose] public section

open Real Filter Topology Finset

namespace QED.Polylog.MZV

open QED.Polylog.HPL QED.Polylog.HPL.Letter

/-- All sign patterns over an exponent list. -/
def signedLists : List ℕ → List (List (ℕ × ℤ))
  | [] => [[]]
  | s :: t => (signedLists t).map ((s, 1) :: ·) ++ (signedLists t).map ((s, -1) :: ·)

/-- The exponent list with all signs `+1`. -/
def unsignedList (s : List ℕ) : List (ℕ × ℤ) := s.map fun a => (a, 1)

theorem sum_map_sum_range {β : Type*} (L : List β) (g : β → ℕ → ℝ) (M : ℕ) :
    (L.map fun l => ∑ n ∈ range M, g l n).sum = ∑ n ∈ range M, (L.map fun l => g l n).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, sum_add_distrib]

/-- Splitting a sum over `n < M` into even and odd `n`. -/
theorem sum_range_even_odd (g : ℕ → ℝ) : ∀ M : ℕ,
    ∑ n ∈ range M, g n = ∑ m ∈ range ((M + 1) / 2), g (2 * m) + ∑ m ∈ range (M / 2), g (2 * m + 1)
  | 0 => by simp
  | 1 => by simp
  | M + 2 => by
    rw [sum_range_succ, sum_range_succ, sum_range_even_odd g M,
      show (M + 2 + 1) / 2 = (M + 1) / 2 + 1 by omega, show (M + 2) / 2 = M / 2 + 1 by omega,
      sum_range_succ, sum_range_succ]
    rcases Nat.even_or_odd M with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [show (M + 1) / 2 = k by omega, show M / 2 = k by omega, show 2 * k = M by omega]
      ring
    · rw [show (M + 1) / 2 = k + 1 by omega, show M / 2 = k by omega,
        show 2 * (k + 1) = M + 1 by omega, show 2 * k + 1 = M by omega]
      ring

/-- **The truncated distribution relation**:
`∑_σ Z_M(s; σ) = 2^{k} / 2^{|s|} Z_{⌈M/2⌉}(s)`. -/
theorem sum_signedLists_nestedSum : ∀ (s : List ℕ) (M : ℕ),
    ((signedLists s).map fun l => nestedSum mzvTerm l M).sum =
      2 ^ s.length / 2 ^ s.sum * nestedSum mzvTerm (unsignedList s) ((M + 1) / 2)
  | [], M => by simp [signedLists, unsignedList]
  | a :: t, M => by
    simp only [signedLists, List.map_append, List.map_map, Function.comp_def, List.sum_append,
      nestedSum_cons, sum_map_sum_range, ← sum_add_distrib, List.sum_map_mul_left,
      sum_signedLists_nestedSum t, ← add_mul]
    rw [sum_range_even_odd]
    have hodd : ∀ m : ℕ, mzvTerm (a, 1) (2 * m + 1) + mzvTerm (a, -1) (2 * m + 1) = 0 :=
      fun m => by
        simp only [mzvTerm, Int.cast_one, one_pow, Int.cast_neg, pow_succ, pow_mul, one_mul]
        ring
    simp only [hodd, zero_mul, sum_const_zero, add_zero, unsignedList, List.map_cons,
      nestedSum_cons, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [show (2 * m + 1) / 2 = m by omega]
    simp only [mzvTerm, Int.cast_one, one_pow, Int.cast_neg]
    rw [show ((-1 : ℝ)) ^ (2 * m) = 1 by rw [pow_mul]; norm_num]
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_pow, List.length_cons, List.sum_cons, pow_succ,
      pow_add]
    field_simp
    ring

theorem mem_signedLists : ∀ {s : List ℕ} {l : List (ℕ × ℤ)}, l ∈ signedLists s →
    l.map Prod.fst = s ∧ ∀ x ∈ l, x.2 = 1 ∨ x.2 = -1
  | [], l, hl => by simp_all [signedLists]
  | a :: t, l, hl => by
    simp only [signedLists, List.mem_append, List.mem_map] at hl
    rcases hl with ⟨l', hl', rfl⟩ | ⟨l', hl', rfl⟩ <;>
    · obtain ⟨h1, h2⟩ := mem_signedLists hl'
      refine ⟨by simp [h1], fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · exact h2 x hx

theorem valid_of_mem_signedLists {s : List ℕ} (hs : ∀ a ∈ s, 1 ≤ a) {l : List (ℕ × ℤ)}
    (hl : l ∈ signedLists s) : Valid l := by
  obtain ⟨h1, h2⟩ := mem_signedLists hl
  intro x hx
  exact ⟨hs x.1 (h1 ▸ List.mem_map_of_mem hx), h2 x hx⟩

theorem conv_of_mem_signedLists {a : ℕ} (ha : 2 ≤ a) {t : List ℕ} {l : List (ℕ × ℤ)}
    (hl : l ∈ signedLists (a :: t)) : Conv l := by
  simp only [signedLists, List.mem_append, List.mem_map] at hl
  rcases hl with ⟨l', -, rfl⟩ | ⟨l', -, rfl⟩ <;>
  · refine ⟨List.cons_ne_nil _ _, ?_⟩
    simp only [List.head?_cons, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
    omega

theorem valid_unsignedList {s : List ℕ} (hs : ∀ a ∈ s, 1 ≤ a) : Valid (unsignedList s) := by
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
  exact ⟨hs b hb, Or.inl rfl⟩

theorem conv_unsignedList {a : ℕ} (ha : 2 ≤ a) (t : List ℕ) : Conv (unsignedList (a :: t)) := by
  refine ⟨by simp [unsignedList], ?_⟩
  simp only [unsignedList, List.map_cons, List.head?_cons, ne_eq, Option.some.injEq,
    Prod.mk.injEq, not_and]
  omega

/-- **The distribution relation**: for `s₁ ≥ 2` and `sⱼ ≥ 1`,
`∑_{σ} ζ(s; σ) = 2^{k} / 2^{|s|} ζ(s)`. -/
theorem sum_signedLists_mzv {a : ℕ} (ha : 2 ≤ a) {t : List ℕ} (ht : ∀ b ∈ t, 1 ≤ b) :
    ((signedLists (a :: t)).map mzv).sum =
      2 ^ (a :: t).length / 2 ^ (a :: t).sum * mzv (unsignedList (a :: t)) := by
  have hs : ∀ b ∈ a :: t, 1 ≤ b := fun b hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · omega
    · exact ht b hb
  have h2 : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => by omega⟩
  have h1 : Tendsto (fun N => ((signedLists (a :: t)).map fun l => nestedSum mzvTerm l (2 * N)).sum)
      atTop (𝓝 ((signedLists (a :: t)).map mzv).sum) :=
    tendsto_list_sum _ fun l hl => (tendsto_nestedSum_mzv (valid_of_mem_signedLists hs hl)
      (conv_of_mem_signedLists ha hl)).comp h2
  have h3 := (tendsto_nestedSum_mzv (valid_unsignedList hs) (conv_unsignedList ha t)).const_mul
    ((2 : ℝ) ^ (a :: t).length / 2 ^ (a :: t).sum)
  refine tendsto_nhds_unique h1 (h3.congr fun N => ?_)
  rw [sum_signedLists_nestedSum, show (2 * N + 1) / 2 = N by omega]

/-- The distribution relation in HPL words. -/
theorem sum_signedLists_hpl_one {a : ℕ} (ha : 2 ≤ a) {t : List ℕ} (ht : ∀ b ∈ t, 1 ≤ b) :
    ((signedLists (a :: t)).map fun l => (wordSign (decode 1 l) : ℝ) * hpl (decode 1 l) 1).sum =
      2 ^ (a :: t).length / 2 ^ (a :: t).sum *
        ((wordSign (decode 1 (unsignedList (a :: t))) : ℝ) *
          hpl (decode 1 (unsignedList (a :: t))) 1) := by
  have hs : ∀ b ∈ a :: t, 1 ≤ b := fun b hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · omega
    · exact ht b hb
  rw [← mzv_eq_hpl_one (valid_unsignedList hs) (conv_unsignedList ha t),
    ← sum_signedLists_mzv ha ht]
  exact congrArg List.sum (List.map_congr_left fun l hl =>
    (mzv_eq_hpl_one (valid_of_mem_signedLists hs hl) (conv_of_mem_signedLists ha hl)).symm)

end QED.Polylog.MZV
