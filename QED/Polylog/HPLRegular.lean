/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLShuffle
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Shuffle regularization of harmonic polylogarithms at `1`

A harmonic polylogarithm whose word starts with `1` diverges logarithmically at `x = 1`. By the
shuffle product, every word is a polynomial in `H(1; x) = -log (1 - x)` whose coefficients are
rational combinations of harmonic polylogarithms of words not starting with `1`:

`H(1ᵏ · v; x) = ∑ c · H(1; x)ʲ · H(u; x)`, the sum over the triples `(c, j, u)` of
`QED.Polylog.HPL.regExpand k v`, each `u` not starting with `1` when `v` does not.

The expansion comes from the shuffle of the one-letter word `1` with `1ᵏ · v`:
`H(1) H(1ᵏ · v) = (k + 1) H(1ᵏ⁺¹ · v) + ∑_{u} H(1ᵏ · u)`, `u` running over the insertions of `1`
into `v` after its first letter (`QED.Polylog.HPL.insertOne`).

The shuffle-regularized value `QED.Polylog.HPL.hplReg w` sets `H(1; 1) = 0` in this expansion; it
equals `H(w; 1)` when `w` does not start with `1`, and it is the limit at `1⁻` of the
coefficient of `H(1; x)⁰`.

## Main definitions

* `QED.Polylog.HPL.insertOne`: the insertions of `1` into a word after its first letter.
* `QED.Polylog.HPL.regExpand`: the expansion of `H(1ᵏ · v)` in powers of `H(1)`.
* `QED.Polylog.HPL.splitOnes`: a word as `1ᵏ · v` with `v` not starting with `1`.
* `QED.Polylog.HPL.hplReg`: the shuffle-regularized value at `1`.

## Main results

* `QED.Polylog.HPL.hpl_replicate_one_append_eq`: the expansion of `H(1ᵏ · v; x)` on `(0, 1)`.
* `QED.Polylog.HPL.hpl_eq_regExpand`: the expansion of `H(w; x)` for every word.
* `QED.Polylog.HPL.head_ne_one_of_mem_regExpand`: the coefficient words do not start with `1`.
* `QED.Polylog.HPL.hplReg_eq_hpl_one`: `hplReg w = H(w; 1)` when `w` does not start with `1`.
* `QED.Polylog.HPL.tendsto_regConst_hplReg`: the `H(1)⁰` coefficient tends to `hplReg w`.
-/

@[expose] public section

open Real Set Filter Topology

namespace QED.Polylog.HPL

open Letter

/-- The insertions of the letter `1` into a word after its first letter (none for `[]`). -/
def insertOne : List Letter → List (List Letter)
  | [] => []
  | b :: v => (shuffle [one] v).map (b :: ·)

/-- The expansion of `H(1ᵏ · v)` as a list of triples `(c, j, u)` standing for
`c · H(1)ʲ · H(u)`. -/
def regExpand : ℕ → List Letter → List (ℚ × ℕ × List Letter)
  | 0, v => [(1, 0, v)]
  | k + 1, v =>
    (regExpand k v).map (fun t : ℚ × ℕ × List Letter => (t.1 / ((k : ℚ) + 1), t.2.1 + 1, t.2.2))
      ++ ((insertOne v).flatMap (regExpand k)).map
        (fun t : ℚ × ℕ × List Letter => (-t.1 / ((k : ℚ) + 1), t.2.1, t.2.2))

/-- The value of an expansion with `H(1)` replaced by `h` and `H(u)` by `F u`. -/
noncomputable def evalExp (h : ℝ) (F : List Letter → ℝ) (L : List (ℚ × ℕ × List Letter)) : ℝ :=
  (L.map fun t => (t.1 : ℝ) * h ^ t.2.1 * F t.2.2).sum

theorem evalExp_append (h : ℝ) (F : List Letter → ℝ) (L M : List (ℚ × ℕ × List Letter)) :
    evalExp h F (L ++ M) = evalExp h F L + evalExp h F M := by
  simp [evalExp]

/-- The shuffle of `1` with `1ᵏ · v`. -/
theorem sum_shuffle_one_replicate (f : List Letter → ℝ) (k : ℕ) (v : List Letter) :
    ((shuffle [one] (List.replicate k one ++ v)).map f).sum =
      (k + 1) * f (List.replicate (k + 1) one ++ v) +
        ((insertOne v).map fun u => f (List.replicate k one ++ u)).sum := by
  induction k generalizing f with
  | zero =>
    cases v with
    | nil => simp [insertOne]
    | cons b v =>
      simp only [List.replicate_zero, List.nil_append, shuffle_cons_cons, shuffle_nil_left,
        List.map_cons, List.map_nil, List.map_append, List.sum_append, List.sum_cons,
        List.sum_nil, insertOne, List.map_map]
      simp only [List.replicate_succ, List.replicate_zero, List.singleton_append, Nat.cast_zero]
      ring
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, shuffle_cons_cons, shuffle_nil_left,
      List.map_append, List.sum_append, List.map_map, List.map_map, ih (f ∘ (one :: ·))]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_def,
      List.replicate_succ, List.cons_append]
    push_cast
    ring

/-- The words of `insertOne v` start with the first letter of `v`. -/
theorem head_of_mem_insertOne {v u : List Letter} (hu : u ∈ insertOne v) :
    u.head? = v.head? := by
  cases v with
  | nil => simp [insertOne] at hu
  | cons b v =>
    simp only [insertOne, List.mem_map] at hu
    obtain ⟨u', -, rfl⟩ := hu
    rfl

/-- The coefficient words of `regExpand k v` do not start with `1` when `v` does not. -/
theorem head_ne_one_of_mem_regExpand {k : ℕ} {v : List Letter} (hv : v.head? ≠ some one)
    {t : ℚ × ℕ × List Letter} (ht : t ∈ regExpand k v) : t.2.2.head? ≠ some one := by
  induction k generalizing v t with
  | zero =>
    simp only [regExpand, List.mem_singleton] at ht
    subst ht
    exact hv
  | succ k ih =>
    simp only [regExpand, List.mem_append, List.mem_map, List.mem_flatMap] at ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨s, ⟨u, hu, hs⟩, rfl⟩
    · exact ih (t := s) hv hs
    · exact ih (t := s) (by rwa [head_of_mem_insertOne hu]) hs

/-- **Shuffle regularization.** For `v` not starting with `1` (or any `v`) and `0 < x < 1`,
`H(1ᵏ · v; x) = ∑_{(c, j, u)} c · H(1; x)ʲ · H(u; x)` over `regExpand k v`. -/
theorem hpl_replicate_one_append_eq (k : ℕ) (v : List Letter) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl (List.replicate k one ++ v) x = evalExp (hpl [one] x) (hpl · x) (regExpand k v) := by
  induction k generalizing v with
  | zero => simp [regExpand, evalExp]
  | succ k ih =>
    have hsh := hpl_mul_hpl [one] (List.replicate k one ++ v) hx
    rw [sum_shuffle_one_replicate (hpl · x)] at hsh
    have hk : (0 : ℝ) < k + 1 := by positivity
    have hH : hpl (List.replicate (k + 1) one ++ v) x =
        (hpl [one] x * hpl (List.replicate k one ++ v) x -
          ((insertOne v).map fun u => hpl (List.replicate k one ++ u) x).sum) / (k + 1) := by
      rw [eq_div_iff hk.ne']
      linarith
    rw [hH, ih v, regExpand, evalExp_append]
    simp only [List.map_congr_left (fun u _ => ih u)]
    simp only [evalExp, List.map_map, List.flatMap, List.map_flatten, List.sum_flatten,
      Function.comp_def]
    push_cast
    have e1 : ∀ L : List (ℚ × ℕ × List Letter),
        (L.map fun t => (t.1 : ℝ) / (k + 1) * hpl [one] x ^ (t.2.1 + 1) * hpl t.2.2 x).sum =
          hpl [one] x / (k + 1) *
            (L.map fun t => (t.1 : ℝ) * hpl [one] x ^ t.2.1 * hpl t.2.2 x).sum := by
      intro L
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      ring
    have e2 : ∀ L : List (ℚ × ℕ × List Letter),
        (L.map fun t => -(t.1 : ℝ) / (k + 1) * hpl [one] x ^ t.2.1 * hpl t.2.2 x).sum =
          -1 / (k + 1) * (L.map fun t => (t.1 : ℝ) * hpl [one] x ^ t.2.1 * hpl t.2.2 x).sum := by
      intro L
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      ring
    simp only [e1, e2, List.sum_map_mul_left]
    field_simp
    ring

/-- A word as `1ᵏ · v` with `v` not starting with `1`. -/
def splitOnes : List Letter → ℕ × List Letter
  | one :: w => ((splitOnes w).1 + 1, (splitOnes w).2)
  | w => (0, w)

theorem splitOnes_spec : ∀ w : List Letter,
    List.replicate (splitOnes w).1 one ++ (splitOnes w).2 = w ∧ (splitOnes w).2.head? ≠ some one
  | [] => by simp [splitOnes]
  | zero :: w => by simp [splitOnes]
  | negOne :: w => by simp [splitOnes]
  | one :: w => by
    obtain ⟨h1, h2⟩ := splitOnes_spec w
    refine ⟨?_, h2⟩
    simp only [splitOnes, List.replicate_succ, List.cons_append, h1]

theorem splitOnes_of_head_ne_one {w : List Letter} (hw : w.head? ≠ some one) :
    splitOnes w = (0, w) := by
  match w, hw with
  | [], _ => rfl
  | zero :: w, _ => rfl
  | negOne :: w, _ => rfl
  | one :: w, hw => simp at hw

/-- The expansion of `H(w)` in powers of `H(1)`. -/
def regExpandWord (w : List Letter) : List (ℚ × ℕ × List Letter) :=
  regExpand (splitOnes w).1 (splitOnes w).2

/-- Every harmonic polylogarithm is a polynomial in `H(1; x)` with coefficients harmonic
polylogarithms of words not starting with `1`. -/
theorem hpl_eq_regExpand (w : List Letter) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl w x = evalExp (hpl [one] x) (hpl · x) (regExpandWord w) := by
  conv_lhs => rw [← (splitOnes_spec w).1]
  exact hpl_replicate_one_append_eq _ _ hx

theorem head_ne_one_of_mem_regExpandWord (w : List Letter) {t : ℚ × ℕ × List Letter}
    (ht : t ∈ regExpandWord w) : t.2.2.head? ≠ some one :=
  head_ne_one_of_mem_regExpand (splitOnes_spec w).2 ht

/-- The shuffle-regularized value of `H(w)` at `1`: the expansion of `H(w)` in powers of
`H(1)` evaluated at `H(1) = 0` and `H(u) = H(u; 1)`. -/
noncomputable def hplReg (w : List Letter) : ℝ := evalExp 0 (hpl · 1) (regExpandWord w)

/-- The regularized value is the ordinary one for words not starting with `1`. -/
theorem hplReg_eq_hpl_one {w : List Letter} (hw : w.head? ≠ some one) :
    hplReg w = hpl w 1 := by
  simp [hplReg, regExpandWord, splitOnes_of_head_ne_one hw, regExpand, evalExp]

/-- The constant term of the expansion, a function of `x`. -/
noncomputable def regConst (w : List Letter) (x : ℝ) : ℝ := evalExp 0 (hpl · x) (regExpandWord w)

/-- `H(u; x) → H(u; 1)` as `x → 1⁻` for a word not starting with `1`. -/
theorem tendsto_hpl_of_head_ne_one {u : List Letter} (hu : u.head? ≠ some one) :
    Tendsto (hpl u) (𝓝[<] 1) (𝓝 (hpl u 1)) := by
  cases u with
  | nil =>
    rw [show hpl [] = fun _ => (1 : ℝ) from funext hpl_nil]
    exact tendsto_const_nhds
  | cons a u => exact tendsto_hpl_one (by simpa using hu) u

/-- The constant term of the expansion of `H(w; x)` tends to the regularized value. -/
theorem tendsto_regConst_hplReg (w : List Letter) :
    Tendsto (regConst w) (𝓝[<] 1) (𝓝 (hplReg w)) := by
  unfold regConst hplReg evalExp
  exact tendsto_list_sum _ fun t ht =>
    ((tendsto_hpl_of_head_ne_one (head_ne_one_of_mem_regExpandWord w ht)).const_mul _)

end QED.Polylog.HPL
