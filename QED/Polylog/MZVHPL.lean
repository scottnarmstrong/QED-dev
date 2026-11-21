/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLRegular
public import QED.Polylog.HPLSeries
public import QED.Polylog.MZVStuffle

/-!
# Alternating multiple zeta values and the double shuffle relations

An alternating multiple zeta value is indexed by a list `((s₁, σ₁), …, (s_k, σ_k))` of
pairs with `sⱼ ≥ 1`, `σⱼ = ±1`:
`ζ(s₁, …, s_k; σ₁, …, σ_k) = lim_N ∑_{N > n₁ > ⋯ > n_k ≥ 1} ∏ⱼ σⱼ^{nⱼ} / nⱼ^{sⱼ}`,
convergent when `(s₁, σ₁) ≠ (1, 1)`. Here it is `QED.Polylog.MZV.mzv`, the limit of the
truncated nested sums `QED.Polylog.MZV.nestedSum mzvTerm` with `mzvTerm (s, σ) n = σⁿ / nˢ`.

Values of harmonic polylogarithms at `1` are such values: if `w = 0^{s₁-1} a₁ ⋯ 0^{s_k-1} a_k`
(letters `aⱼ = ±1`) then `∑_{n<N} c_w(n) = (∏ⱼ aⱼ) Z_N(encode 1 0 w)` where `encode` records
the exponents `sⱼ` and the signs `σⱼ = aⱼ₋₁ aⱼ` (`a₀ = 1`); so
`H(w; 1) = (∏ⱼ aⱼ) ζ(encode 1 0 w)` for `a₁ ≠ 1`. The inverse is `decode 1`.

The two products are:

* the **stuffle** `QED.Polylog.MZV.mzv_mul_mzv`: `ζ(u) ζ(v) = ∑_{w ∈ u ∗ v} ζ(w)`, the limit of
  the exact identity `QED.Polylog.MZV.nestedSum_mul_nestedSum` of truncated sums;
* the **shuffle** `QED.Polylog.HPL.hpl_one_mul_hpl_one`: `H(u; 1) H(v; 1) = ∑_{w ∈ u ⧢ v} H(w; 1)`
  for words not starting with `1`, the limit at `1⁻` of `QED.Polylog.HPL.hpl_mul_hpl`.

Comparing them gives the (convergent) double shuffle relations; see
`QED.Polylog.MZV.hpl_one_mul_hpl_one_stuffle` for the stuffle written in HPL words.

## Main definitions

* `QED.Polylog.MZV.mzvTerm`, `QED.Polylog.MZV.mzvOp`: the weights `σⁿ / nˢ` and their product.
* `QED.Polylog.MZV.mzv`: the alternating multiple zeta values.
* `QED.Polylog.MZV.encode`, `QED.Polylog.MZV.decode`, `QED.Polylog.MZV.wordSign`: the
  dictionary between HPL words and index lists.

## Main results

* `QED.Polylog.MZV.sum_coef_eq_nestedSum`: `∑_{n<N} c_w(n) = (±1) Z_N(encode 1 0 w)`.
* `QED.Polylog.MZV.hpl_one_eq_mzv`, `QED.Polylog.MZV.mzv_eq_hpl_one`: the dictionary at `1`.
* `QED.Polylog.MZV.mzv_mul_mzv`: the stuffle product of convergent alternating MZVs.
* `QED.Polylog.HPL.hpl_one_mul_hpl_one`: the shuffle product at `1`.
* `QED.Polylog.MZV.hpl_one_mul_hpl_one_stuffle`: the stuffle product in HPL words.
-/

@[expose] public section

open Real Set Filter Topology Finset

namespace QED.Polylog.HPL

open Letter

/-! ### The shuffle product at `1` -/

theorem head_ne_one_of_mem_shuffle : ∀ {u v w : List Letter}, w ∈ shuffle u v →
    u.head? ≠ some one → v.head? ≠ some one → w.head? ≠ some one
  | [], v, w, hw, _, hv => by
    simp only [shuffle_nil_left, List.mem_singleton] at hw
    rwa [hw]
  | a :: u, [], w, hw, hu, _ => by
    simp only [shuffle_nil_right, List.mem_singleton] at hw
    rwa [hw]
  | a :: u, b :: v, w, hw, hu, hv => by
    rw [shuffle_cons_cons] at hw
    simp only [List.mem_append, List.mem_map] at hw
    rcases hw with ⟨w', -, rfl⟩ | ⟨w', -, rfl⟩
    · simpa using hu
    · simpa using hv

/-- **The shuffle product at `1`.** For words not starting with `1`,
`H(u; 1) H(v; 1) = ∑_{w ∈ u ⧢ v} H(w; 1)`. -/
theorem hpl_one_mul_hpl_one {u v : List Letter} (hu : u.head? ≠ some one)
    (hv : v.head? ≠ some one) :
    hpl u 1 * hpl v 1 = ((shuffle u v).map fun w => hpl w 1).sum := by
  have h1 := (tendsto_hpl_of_head_ne_one hu).mul (tendsto_hpl_of_head_ne_one hv)
  have h2 : Tendsto (fun x => ((shuffle u v).map fun w => hpl w x).sum) (𝓝[<] 1)
      (𝓝 ((shuffle u v).map fun w => hpl w 1).sum) :=
    tendsto_list_sum _ fun w hw => tendsto_hpl_of_head_ne_one (head_ne_one_of_mem_shuffle hw hu hv)
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with x hx
  exact (hpl_mul_hpl u v hx).symm

end QED.Polylog.HPL

namespace QED.Polylog.MZV

open QED.Polylog.HPL QED.Polylog.HPL.Letter

/-! ### Alternating multiple zeta values -/

/-- The weight `σⁿ / nˢ` of the index `(s, σ)`. -/
noncomputable def mzvTerm (x : ℕ × ℤ) (n : ℕ) : ℝ := (x.2 : ℝ) ^ n / (n : ℝ) ^ x.1

/-- The product of indices, `(s, σ) ⋄ (t, τ) = (s + t, σ τ)`. -/
def mzvOp (x y : ℕ × ℤ) : ℕ × ℤ := (x.1 + y.1, x.2 * y.2)

theorem mzvTerm_mzvOp (x y : ℕ × ℤ) (n : ℕ) :
    mzvTerm (mzvOp x y) n = mzvTerm x n * mzvTerm y n := by
  simp only [mzvTerm, mzvOp, Int.cast_mul, mul_pow, pow_add]
  rw [div_mul_div_comm]

/-- The truncated stuffle product of the alternating nested sums. -/
theorem nestedSum_mzvTerm_mul (u v : List (ℕ × ℤ)) (N : ℕ) :
    nestedSum mzvTerm u N * nestedSum mzvTerm v N =
      ((stuffle mzvOp u v).map fun w => nestedSum mzvTerm w N).sum :=
  nestedSum_mul_nestedSum mzvOp mzvTerm mzvTerm_mzvOp N u v

/-- The alternating multiple zeta value `ζ(l) = lim_N Z_N(l)` (meaningful when the limit
exists, e.g. for `QED.Polylog.MZV.Valid` lists with `QED.Polylog.MZV.Conv`). -/
noncomputable def mzv (l : List (ℕ × ℤ)) : ℝ := limUnder atTop (nestedSum mzvTerm l)

/-- Every index has `s ≥ 1` and `σ = ±1`. -/
def Valid (l : List (ℕ × ℤ)) : Prop := ∀ x ∈ l, 1 ≤ x.1 ∧ (x.2 = 1 ∨ x.2 = -1)

instance (l : List (ℕ × ℤ)) : Decidable (Valid l) :=
  inferInstanceAs (Decidable (∀ x ∈ l, 1 ≤ x.1 ∧ (x.2 = 1 ∨ x.2 = -1)))

/-- The convergence condition: nonempty, with first index not `(1, 1)`. -/
def Conv (l : List (ℕ × ℤ)) : Prop := l ≠ [] ∧ l.head? ≠ some (1, 1)

instance (l : List (ℕ × ℤ)) : Decidable (Conv l) :=
  inferInstanceAs (Decidable (l ≠ [] ∧ l.head? ≠ some (1, 1)))

/-! ### The dictionary with HPL words -/

/-- The index list of a word: `encode τ k w` reads `w` after `k` pending zeros, with
previous nonzero letter `τ`. -/
def encode : ℤ → ℕ → List Letter → List (ℕ × ℤ)
  | _, _, [] => []
  | τ, k, zero :: w => encode τ (k + 1) w
  | τ, k, one :: w => (k + 1, τ) :: encode 1 0 w
  | τ, k, negOne :: w => (k + 1, -τ) :: encode (-1) 0 w

/-- The product of the nonzero letters of a word. -/
def wordSign : List Letter → ℤ
  | [] => 1
  | zero :: w => wordSign w
  | one :: w => wordSign w
  | negOne :: w => -wordSign w

/-- The letter `1` for the sign `1`, and `-1` otherwise. -/
def letterOfSign (σ : ℤ) : Letter := if σ = 1 then one else negOne

/-- The word of an index list, the inverse of `encode τ 0` on valid lists. -/
def decode : ℤ → List (ℕ × ℤ) → List Letter
  | _, [] => []
  | τ, x :: l => List.replicate (x.1 - 1) zero ++ letterOfSign (x.2 * τ) :: decode (x.2 * τ) l

theorem wordSign_mul_self : ∀ w : List Letter, wordSign w * wordSign w = 1
  | [] => rfl
  | zero :: w => wordSign_mul_self w
  | one :: w => wordSign_mul_self w
  | negOne :: w => by simpa [wordSign] using wordSign_mul_self w

theorem wordSign_cast_mul_self (w : List Letter) : (wordSign w : ℝ) * wordSign w = 1 := by
  exact_mod_cast wordSign_mul_self w

/-- **Nested sums of HPL coefficients.** For a word with no trailing zero,
`∑_{n<N} τⁿ c_w(n) / nᵏ = (∏ nonzero letters) Z_N(encode τ k w)` (for the empty word, with
`k = 0` and `N > 0`). -/
theorem sum_coef_eq_nestedSum : ∀ (w : List Letter) (τ : ℤ) (k N : ℕ),
    w.getLast? ≠ some zero → (w = [] → k = 0 ∧ 0 < N) →
    ∑ n ∈ range N, (τ : ℝ) ^ n * coef w n / (n : ℝ) ^ k =
      wordSign w * nestedSum mzvTerm (encode τ k w) N
  | [], τ, k, N, _, h0 => by
    obtain ⟨rfl, hN⟩ := h0 rfl
    simp [coef_nil, encode, wordSign, hN]
  | zero :: w, τ, k, N, hw, _ => by
    have hne : w ≠ [] := by rintro rfl; simp at hw
    have ih := sum_coef_eq_nestedSum w τ (k + 1) N (getLast?_ne_of_cons hw)
      (fun h => absurd h hne)
    simp only [encode, wordSign, ← ih, coef_zero_cons]
    refine sum_congr rfl fun n _ => ?_
    rw [pow_succ]
    ring
  | one :: w, τ, k, N, hw, _ => by
    simp only [encode, wordSign, nestedSum_cons, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [coef, mzvTerm]
    have ih := sum_coef_eq_nestedSum w 1 0 n (getLast?_ne_of_cons hw) (fun _ => ⟨rfl, hn⟩)
    simp only [Int.cast_one, one_pow, one_mul, pow_zero, div_one] at ih
    rw [show coef (one :: w) n = twistSum 1 (coef w) n / n from rfl, twistSum_eq_sum]
    simp only [one_pow, one_mul, ih, mzvTerm, pow_succ]
    ring
  | negOne :: w, τ, k, N, hw, _ => by
    simp only [encode, wordSign, nestedSum_cons, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [coef, mzvTerm]
    have ih := sum_coef_eq_nestedSum w (-1) 0 n (getLast?_ne_of_cons hw) (fun _ => ⟨rfl, hn⟩)
    simp only [Int.cast_neg, Int.cast_one, pow_zero, div_one] at ih
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hsum : twistSum (-1) (coef w) (n + 1) =
        (-1) ^ n * ∑ m ∈ range (n + 1), (-1 : ℝ) ^ m * coef w m := by
      rw [twistSum_eq_sum, mul_sum]
      refine sum_congr rfl fun m hm => ?_
      rw [Finset.mem_range] at hm
      have e : n = (n - m) + m := by omega
      rw [Nat.add_sub_cancel, e, pow_add, Nat.add_sub_cancel, mul_assoc, ← mul_assoc
        ((-1 : ℝ) ^ m), ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [show coef (negOne :: w) (n + 1) = twistSum (-1) (coef w) (n + 1) / ((n + 1 : ℕ) : ℝ)
      from rfl, hsum, ih]
    simp only [mzvTerm, Int.cast_neg, neg_pow (τ : ℝ), pow_succ]
    ring

/-- `∑_{n<N} c_w(n) = (∏ nonzero letters) Z_N(encode 1 0 w)` for a nonempty word with no
trailing zero. -/
theorem sum_coef_eq_nestedSum_one {w : List Letter} (hne : w ≠ [])
    (hw : w.getLast? ≠ some zero) (N : ℕ) :
    ∑ n ∈ range N, coef w n = wordSign w * nestedSum mzvTerm (encode 1 0 w) N := by
  have := sum_coef_eq_nestedSum w 1 0 N hw (fun h => absurd h hne)
  simpa using this

/-- For a word not starting with `1` and with no trailing zero, the nested sums of its index
list converge to `(∏ nonzero letters) H(w; 1)`. -/
theorem tendsto_nestedSum_encode {a : Letter} (ha : a ≠ one) {w : List Letter}
    (hw : (a :: w).getLast? ≠ some zero) :
    Tendsto (nestedSum mzvTerm (encode 1 0 (a :: w))) atTop
      (𝓝 (wordSign (a :: w) * hpl (a :: w) 1)) := by
  have h := (tendsto_sum_coef_hpl_one ha hw).const_mul (wordSign (a :: w) : ℝ)
  refine h.congr fun N => ?_
  rw [sum_coef_eq_nestedSum_one (List.cons_ne_nil _ _) hw, ← mul_assoc,
    wordSign_cast_mul_self, one_mul]

/-- **HPL values at `1` are alternating MZVs**: `H(w; 1) = (∏ nonzero letters) ζ(encode 1 0 w)`
for `w` not starting with `1` and with no trailing zero. -/
theorem hpl_one_eq_mzv {a : Letter} (ha : a ≠ one) {w : List Letter}
    (hw : (a :: w).getLast? ≠ some zero) :
    hpl (a :: w) 1 = wordSign (a :: w) * mzv (encode 1 0 (a :: w)) := by
  rw [mzv, (tendsto_nestedSum_encode ha hw).limUnder_eq, ← mul_assoc, wordSign_cast_mul_self,
    one_mul]

/-! ### Decoding -/

theorem encode_replicate_append (τ : ℤ) (k : ℕ) (w : List Letter) :
    ∀ j, encode τ k (List.replicate j zero ++ w) = encode τ (k + j) w
  | 0 => rfl
  | j + 1 => by
    rw [List.replicate_succ, List.cons_append, encode, encode_replicate_append τ (k + 1) w j]
    congr 1
    omega

theorem encode_decode : ∀ (l : List (ℕ × ℤ)) (τ : ℤ), (τ = 1 ∨ τ = -1) → Valid l →
    encode τ 0 (decode τ l) = l
  | [], _, _, _ => rfl
  | x :: l, τ, hτ, hl => by
    obtain ⟨hs, hσ⟩ := hl x List.mem_cons_self
    have hl' : Valid l := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    obtain ⟨s, σ⟩ := x
    simp only at hs hσ
    rw [decode, encode_replicate_append, zero_add]
    have hs' : s - 1 + 1 = s := by omega
    have ih1 := encode_decode l 1 (Or.inl rfl) hl'
    have ih2 := encode_decode l (-1) (Or.inr rfl) hl'
    rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;>
      simp [letterOfSign, encode, hs', ih1, ih2]

theorem decode_ne_nil {τ : ℤ} {l : List (ℕ × ℤ)} (hl : l ≠ []) : decode τ l ≠ [] := by
  obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp [decode]

theorem letterOfSign_ne_zero (σ : ℤ) : letterOfSign σ ≠ zero := by
  unfold letterOfSign; split_ifs <;> simp

theorem getLast?_decode : ∀ (τ : ℤ) (l : List (ℕ × ℤ)), (decode τ l).getLast? ≠ some zero
  | _, [] => by simp [decode]
  | τ, x :: l => by
    rw [decode, List.getLast?_append, List.getLast?_cons]
    by_cases hl : l = []
    · subst hl
      simpa [decode] using letterOfSign_ne_zero _
    · have h := getLast?_decode (x.2 * τ) l
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1
        (mt List.getLast?_eq_none_iff.1 (decode_ne_nil hl))
      rw [hy] at h ⊢
      simpa using h

theorem head_decode_ne_one {l : List (ℕ × ℤ)} (hv : Valid l) (hc : Conv l) :
    (decode 1 l).head? ≠ some one := by
  obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil hc.1
  obtain ⟨s, σ⟩ := x
  obtain ⟨hs, hσ⟩ := hv (s, σ) List.mem_cons_self
  have hc2 := hc.2
  simp only [List.head?_cons, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and] at hc2 hs hσ
  rw [decode]
  rcases Nat.lt_or_ge 1 s with h | h
  · obtain ⟨j, hj⟩ : ∃ j, s - 1 = j + 1 := ⟨s - 2, by omega⟩
    simp [hj, List.replicate_succ]
  · have hs1 : s = 1 := by omega
    subst hs1
    rcases hσ with rfl | rfl
    · exact absurd rfl (hc2 rfl)
    · simp [letterOfSign]

/-- **Convergent alternating MZVs are HPL values at `1`.** -/
theorem mzv_eq_hpl_one {l : List (ℕ × ℤ)} (hv : Valid l) (hc : Conv l) :
    mzv l = wordSign (decode 1 l) * hpl (decode 1 l) 1 := by
  have hne := decode_ne_nil (τ := 1) hc.1
  obtain ⟨a, w, hw⟩ := List.exists_cons_of_ne_nil hne
  have ha : a ≠ one := by
    intro h
    have := head_decode_ne_one hv hc
    rw [hw, h] at this
    exact this rfl
  have hlast : (a :: w).getLast? ≠ some zero := hw ▸ getLast?_decode 1 l
  rw [hw, hpl_one_eq_mzv ha hlast, ← mul_assoc, wordSign_cast_mul_self, one_mul, ← hw,
    encode_decode l 1 (Or.inl rfl) hv]

/-- The nested sums of a convergent valid list converge to its MZV. -/
theorem tendsto_nestedSum_mzv {l : List (ℕ × ℤ)} (hv : Valid l) (hc : Conv l) :
    Tendsto (nestedSum mzvTerm l) atTop (𝓝 (mzv l)) := by
  have hne := decode_ne_nil (τ := 1) hc.1
  obtain ⟨a, w, hw⟩ := List.exists_cons_of_ne_nil hne
  have ha : a ≠ one := by
    intro h
    have := head_decode_ne_one hv hc
    rw [hw, h] at this
    exact this rfl
  have hlast : (a :: w).getLast? ≠ some zero := hw ▸ getLast?_decode 1 l
  have h := tendsto_nestedSum_encode ha hlast
  rw [← hw, encode_decode l 1 (Or.inl rfl) hv] at h
  rwa [mzv, h.limUnder_eq]

/-! ### The stuffle product of alternating MZVs -/

theorem valid_of_mem_stuffle {u v w : List (ℕ × ℤ)} (hu : Valid u) (hv : Valid v)
    (hw : w ∈ stuffle mzvOp u v) : Valid w := by
  intro x hx
  rcases mem_of_mem_mem_stuffle mzvOp hw x hx with h | h | ⟨a, ha, b, hb, rfl⟩
  · exact hu x h
  · exact hv x h
  · obtain ⟨ha1, ha2⟩ := hu a ha
    obtain ⟨hb1, hb2⟩ := hv b hb
    refine ⟨by simp only [mzvOp]; omega, ?_⟩
    simp only [mzvOp]
    rcases ha2 with h1 | h1 <;> rcases hb2 with h2 | h2 <;> simp [h1, h2]

theorem conv_of_mem_stuffle {u v w : List (ℕ × ℤ)} (hu : Valid u) (hv : Valid v)
    (hcu : Conv u) (hcv : Conv v) (hw : w ∈ stuffle mzvOp u v) : Conv w := by
  obtain ⟨a, u, rfl⟩ := List.exists_cons_of_ne_nil hcu.1
  obtain ⟨b, v, rfl⟩ := List.exists_cons_of_ne_nil hcv.1
  obtain ⟨c, w', rfl, hc⟩ := head_of_mem_stuffle_cons_cons mzvOp hw
  refine ⟨List.cons_ne_nil _ _, ?_⟩
  rcases hc with rfl | rfl | rfl
  · exact hcu.2
  · exact hcv.2
  · have h1 := (hu a List.mem_cons_self).1
    have h2 := (hv b List.mem_cons_self).1
    simp only [List.head?_cons, ne_eq, Option.some.injEq, mzvOp, Prod.mk.injEq, not_and]
    intro h
    omega

/-- **The stuffle product of alternating multiple zeta values**: for convergent valid index
lists, `ζ(u) ζ(v) = ∑_{w ∈ u ∗ v} ζ(w)`. -/
theorem mzv_mul_mzv {u v : List (ℕ × ℤ)} (hu : Valid u) (hv : Valid v) (hcu : Conv u)
    (hcv : Conv v) :
    mzv u * mzv v = ((stuffle mzvOp u v).map mzv).sum := by
  have h1 := (tendsto_nestedSum_mzv hu hcu).mul (tendsto_nestedSum_mzv hv hcv)
  have h2 : Tendsto (fun N => ((stuffle mzvOp u v).map fun w => nestedSum mzvTerm w N).sum)
      atTop (𝓝 ((stuffle mzvOp u v).map mzv).sum) :=
    tendsto_list_sum _ fun w hw => tendsto_nestedSum_mzv (valid_of_mem_stuffle hu hv hw)
      (conv_of_mem_stuffle hu hv hcu hcv hw)
  exact tendsto_nhds_unique h1 (h2.congr fun N => (nestedSum_mzvTerm_mul u v N).symm)

theorem valid_encode : ∀ (τ : ℤ) (k : ℕ) (w : List Letter), (τ = 1 ∨ τ = -1) →
    Valid (encode τ k w)
  | _, _, [], _ => by simp [Valid, encode]
  | τ, k, zero :: w, hτ => valid_encode τ (k + 1) w hτ
  | τ, k, one :: w, hτ => by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨by simp, hτ⟩
    · exact valid_encode 1 0 w (Or.inl rfl) x hx
  | τ, k, negOne :: w, hτ => by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨by simp, ?_⟩
      rcases hτ with rfl | rfl <;> simp
    · exact valid_encode (-1) 0 w (Or.inr rfl) x hx

theorem head_encode : ∀ (τ : ℤ) (k : ℕ) (w : List Letter), ∀ x ∈ (encode τ k w).head?,
    k + 1 ≤ x.1
  | _, _, [] => by simp [encode]
  | τ, k, zero :: w => fun x hx => by
    have := head_encode τ (k + 1) w x hx
    omega
  | τ, k, one :: w => by simp [encode]
  | τ, k, negOne :: w => by simp [encode]

theorem encode_ne_nil : ∀ (τ : ℤ) (k : ℕ) {w : List Letter}, ¬AllZero w → encode τ k w ≠ []
  | _, _, [], h => absurd (fun _ h => by simp at h) h
  | τ, k, zero :: w, h => encode_ne_nil τ (k + 1) fun hw => h fun b hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · rfl
      · exact hw b hb
  | τ, k, one :: w, _ => by simp [encode]
  | τ, k, negOne :: w, _ => by simp [encode]

theorem conv_encode {a : Letter} (ha : a ≠ one) {w : List Letter}
    (hw : (a :: w).getLast? ≠ some zero) : Conv (encode 1 0 (a :: w)) := by
  refine ⟨encode_ne_nil 1 0 (not_allZero_of_getLast? (List.cons_ne_nil _ _) hw), ?_⟩
  intro h
  cases a with
  | one => exact ha rfl
  | negOne => simp [encode] at h
  | zero =>
    have := head_encode 1 1 w (1, 1) (by simpa [encode] using h)
    simp at this

/-- **The stuffle product in HPL words**: for words `u`, `v` not starting with `1` and with no
trailing zero, `H(u; 1) H(v; 1)` is the sum over the stuffles `l` of their index lists of
`± H(decode 1 l; 1)`. -/
theorem hpl_one_mul_hpl_one_stuffle {a b : Letter} (ha : a ≠ one) (hb : b ≠ one)
    {u v : List Letter} (hu : (a :: u).getLast? ≠ some zero)
    (hv : (b :: v).getLast? ≠ some zero) :
    hpl (a :: u) 1 * hpl (b :: v) 1 =
      ((stuffle mzvOp (encode 1 0 (a :: u)) (encode 1 0 (b :: v))).map fun l =>
        ((wordSign (a :: u) * wordSign (b :: v) * wordSign (decode 1 l) : ℤ) : ℝ) *
          hpl (decode 1 l) 1).sum := by
  have Vu := valid_encode 1 0 (a :: u) (Or.inl rfl)
  have Vv := valid_encode 1 0 (b :: v) (Or.inl rfl)
  rw [hpl_one_eq_mzv ha hu, hpl_one_eq_mzv hb hv,
    show ∀ p q r s : ℝ, p * q * (r * s) = p * r * (q * s) from fun _ _ _ _ => by ring,
    mzv_mul_mzv Vu Vv (conv_encode ha hu) (conv_encode hb hv), ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
  rw [mzv_eq_hpl_one (valid_of_mem_stuffle Vu Vv hl)
    (conv_of_mem_stuffle Vu Vv (conv_encode ha hu) (conv_encode hb hv) hl)]
  push_cast
  ring

end QED.Polylog.MZV
