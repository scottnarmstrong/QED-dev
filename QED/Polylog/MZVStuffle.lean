/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.LinearCombination

/-!
# The stuffle (quasi-shuffle) product of nested sums

For an alphabet `α`, a weight `f : α → ℕ → ℝ` and a word `w = (a₁, …, a_k)`, the truncated
nested sum is
`Z_N(a₁, …, a_k) = ∑_{N > n₁ > n₂ > ⋯ > n_k ≥ 0} f a₁ n₁ ⋯ f a_k n_k`,
defined by `Z_N([]) = 1` and `Z_N(a · w) = ∑_{n < N} f a n · Z_n(w)`. When the alphabet carries
an operation `⋄` with `f (a ⋄ b) n = f a n · f b n`, these sums multiply by the quasi-shuffle
(stuffle) product, *exactly* for every truncation `N`:
`Z_N(u) Z_N(v) = ∑_{w ∈ u ∗ v} Z_N(w)`,
where `(a · u) ∗ (b · v) = a · (u ∗ (b · v)) + b · ((a · u) ∗ v) + (a ⋄ b) · (u ∗ v)`.

For the multiple zeta values `f (s, σ) n = σⁿ / nˢ` and `(s, σ) ⋄ (t, τ) = (s + t, σ τ)`; then
`Z_N` are the partial sums of the (alternating) multiple zeta values and the identity is the
stuffle half of the double shuffle relations (see `QED.Polylog.MZVHPL`).

## Main definitions

* `QED.Polylog.MZV.stuffle`: the quasi-shuffles of two words, with multiplicity.
* `QED.Polylog.MZV.nestedSum`: the truncated nested sums `Z_N(w)`.

## Main results

* `QED.Polylog.MZV.nestedSum_mul_nestedSum`: the stuffle product of truncated nested sums.
-/

@[expose] public section

open Finset

namespace QED.Polylog.MZV

variable {α : Type*}

/-! ### The quasi-shuffle product -/

/-- Auxiliary for `stuffle`: given `a`, `u` and the function `stuffle op u`, the stuffles of
`a :: u` with a word, by recursion on that word. -/
def stuffleAux (op : α → α → α) (a : α) (u : List α) (su : List α → List (List α)) :
    List α → List (List α)
  | [] => [a :: u]
  | b :: v => (su (b :: v)).map (a :: ·) ++ (stuffleAux op a u su v).map (b :: ·) ++
      (su v).map (op a b :: ·)

/-- The quasi-shuffles (stuffles) of two words, as a list of words counted with multiplicity:
`[] ∗ v = [v]`, `u ∗ [] = [u]` and
`(a · u) ∗ (b · v) = a · (u ∗ (b · v)) + b · ((a · u) ∗ v) + (a ⋄ b) · (u ∗ v)`. -/
def stuffle (op : α → α → α) : List α → List α → List (List α)
  | [], v => [v]
  | a :: u, v => stuffleAux op a u (stuffle op u) v

variable (op : α → α → α)

@[simp] theorem stuffle_nil_left (v : List α) : stuffle op [] v = [v] := rfl

@[simp] theorem stuffle_nil_right (u : List α) : stuffle op u [] = [u] := by
  cases u <;> rfl

theorem stuffle_cons_cons (a b : α) (u v : List α) :
    stuffle op (a :: u) (b :: v) =
      (stuffle op u (b :: v)).map (a :: ·) ++ (stuffle op (a :: u) v).map (b :: ·) ++
        (stuffle op u v).map (op a b :: ·) := rfl

/-- The stuffles of two nonempty words start with the first letter of one of them, or with
their `⋄`-product. -/
theorem head_of_mem_stuffle_cons_cons {a b : α} {u v w : List α}
    (hw : w ∈ stuffle op (a :: u) (b :: v)) :
    ∃ c w', w = c :: w' ∧ (c = a ∨ c = b ∨ c = op a b) := by
  rw [stuffle_cons_cons] at hw
  simp only [List.mem_append, List.mem_map] at hw
  rcases hw with (⟨w', -, rfl⟩ | ⟨w', -, rfl⟩) | ⟨w', -, rfl⟩
  · exact ⟨a, w', rfl, Or.inl rfl⟩
  · exact ⟨b, w', rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨op a b, w', rfl, Or.inr (Or.inr rfl)⟩

/-- Every letter of a stuffle of `u` and `v` is a letter of `u`, a letter of `v`, or the
`⋄`-product of one of each. -/
theorem mem_of_mem_mem_stuffle : ∀ {u v w : List α}, w ∈ stuffle op u v → ∀ x ∈ w,
    x ∈ u ∨ x ∈ v ∨ ∃ a ∈ u, ∃ b ∈ v, x = op a b
  | [], v, w, hw, x, hx => by
    simp only [stuffle_nil_left, List.mem_singleton] at hw
    subst hw
    exact Or.inr (Or.inl hx)
  | a :: u, [], w, hw, x, hx => by
    simp only [stuffle_nil_right, List.mem_singleton] at hw
    subst hw
    exact Or.inl hx
  | a :: u, b :: v, w, hw, x, hx => by
    rw [stuffle_cons_cons] at hw
    simp only [List.mem_append, List.mem_map] at hw
    rcases hw with (⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩) | ⟨w', hw', rfl⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl List.mem_cons_self
      rcases mem_of_mem_mem_stuffle hw' x hx with h | h | ⟨a', ha', b', hb', rfl⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨a', List.mem_cons_of_mem _ ha', b', hb', rfl⟩)
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inr (Or.inl List.mem_cons_self)
      rcases mem_of_mem_mem_stuffle hw' x hx with h | h | ⟨a', ha', b', hb', rfl⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
      · exact Or.inr (Or.inr ⟨a', ha', b', List.mem_cons_of_mem _ hb', rfl⟩)
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inr (Or.inr ⟨a, List.mem_cons_self, b, List.mem_cons_self, rfl⟩)
      rcases mem_of_mem_mem_stuffle hw' x hx with h | h | ⟨a', ha', b', hb', rfl⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
      · exact Or.inr (Or.inr ⟨a', List.mem_cons_of_mem _ ha', b', List.mem_cons_of_mem _ hb',
          rfl⟩)

/-! ### Truncated nested sums -/

/-- The truncated nested sums `Z_N(a₁, …, a_k) = ∑_{N > n₁ > ⋯ > n_k ≥ 0} ∏ⱼ f aⱼ nⱼ`:
`Z_N([]) = 1` and `Z_N(a · w) = ∑_{n < N} f a n · Z_n(w)`. -/
noncomputable def nestedSum (f : α → ℕ → ℝ) : List α → ℕ → ℝ
  | [], _ => 1
  | a :: w, N => ∑ n ∈ range N, f a n * nestedSum f w n

variable (f : α → ℕ → ℝ)

@[simp] theorem nestedSum_nil (N : ℕ) : nestedSum f [] N = 1 := rfl

theorem nestedSum_cons (a : α) (w : List α) (N : ℕ) :
    nestedSum f (a :: w) N = ∑ n ∈ range N, f a n * nestedSum f w n := rfl

@[simp] theorem nestedSum_cons_zero (a : α) (w : List α) : nestedSum f (a :: w) 0 = 0 := by
  simp [nestedSum_cons]

theorem nestedSum_cons_succ (a : α) (w : List α) (N : ℕ) :
    nestedSum f (a :: w) (N + 1) = nestedSum f (a :: w) N + f a N * nestedSum f w N := by
  simp [nestedSum_cons, sum_range_succ]

/-- Prepending a letter to a list of words, at truncation `N + 1`. -/
theorem sum_map_cons_nestedSum_succ (a : α) (L : List (List α)) (N : ℕ) :
    (L.map fun w => nestedSum f (a :: w) (N + 1)) =
      L.map fun w => nestedSum f (a :: w) N + f a N * nestedSum f w N := by
  simp only [nestedSum_cons_succ]

/-- **The stuffle product of truncated nested sums.** If `f (a ⋄ b) n = f a n · f b n`, then
`Z_N(u) Z_N(v) = ∑_{w ∈ u ∗ v} Z_N(w)` for every truncation `N`. -/
theorem nestedSum_mul_nestedSum (hf : ∀ a b n, f (op a b) n = f a n * f b n) (N : ℕ) :
    ∀ u v : List α, nestedSum f u N * nestedSum f v N =
      ((stuffle op u v).map fun w => nestedSum f w N).sum := by
  induction N with
  | zero =>
    intro u v
    match u, v with
    | [], v => simp
    | a :: u, [] => simp
    | a :: u, b :: v =>
      rw [stuffle_cons_cons]
      simp [Function.comp_def]
  | succ N ih =>
    intro u v
    match u, v with
    | [], v => simp
    | a :: u, [] => simp
    | a :: u, b :: v =>
      rw [stuffle_cons_cons]
      simp only [List.map_append, List.map_map, Function.comp_def, List.sum_append,
        nestedSum_cons_succ, List.sum_map_add, List.sum_map_mul_left, ← ih, hf]
      have h := ih (a :: u) (b :: v)
      rw [stuffle_cons_cons] at h
      simp only [List.map_append, List.map_map, Function.comp_def, List.sum_append] at h
      linear_combination h

end QED.Polylog.MZV
