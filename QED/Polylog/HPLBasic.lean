/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Harmonic polylogarithms with alphabet `{0, 1, -1}`: the definition

The harmonic polylogarithms (HPLs) of Remiddi and Vermaseren, for words over the alphabet
`{0, 1, -1}` and real arguments. Each letter `a` carries the kernel `f a`:
`f 0 t = 1 / t`, `f 1 t = 1 / (1 - t)`, `f (-1) t = 1 / (1 + t)`. For a word `w` (a list of
letters, the leftmost letter being the outermost integration) the HPL `H(w; x)` is defined by
the recursion

* `H([]; x) = 1`;
* `H(0ⁿ; x) = logⁿ x / n!` (the trailing-zero convention, for the all-zero word of length `n`);
* `H(a · w; x) = ∫₀ˣ f a t · H(w; t) dt` when `a · w` is not all zeros.

The integral in the last case converges for `0 ≤ x < 1`: the integrand has at worst a power of
`log t` singularity at `0` (proved in `QED.Polylog.HPLCalculus`). The recursion is structural on
the word, and the case split is on the word only, so for a fixed word `hpl w` is either an
explicit power of `log` or the primitive `x ↦ ∫₀ˣ g` of a fixed function `g`.

The natural domain is `0 < x < 1`. At `x = 1` the definition gives `H(a · w; 1) = ∫₀¹ f a · H(w)`
(a Lebesgue integral): when `a ≠ 1` the integrand is integrable and this is the limit of
`H(a · w; x)` as `x → 1⁻` (`QED.Polylog.HPL.tendsto_hpl_one`); when `a = 1` the integral
diverges and `H(1 · w; 1)` is a junk value, not to be used.

This file also defines the shuffle product of words, `QED.Polylog.HPL.shuffle u v`, as a list
of words counted with multiplicity, and proves that each shuffle is a permutation of `u ++ v`.

## Main definitions

* `QED.Polylog.HPL.Letter`: the alphabet `{0, 1, -1}`, with constructors `zero`, `one`,
  `negOne`.
* `QED.Polylog.HPL.Letter.kernel`: the kernel `f a`.
* `QED.Polylog.HPL.AllZero`: a word all of whose letters are `0`.
* `QED.Polylog.HPL.hpl`: the harmonic polylogarithm `H(w; x)`.
* `QED.Polylog.HPL.shuffle`: the shuffles of two words.

## Main results

* `QED.Polylog.HPL.hpl_of_allZero`: `H(0ⁿ; x) = logⁿ x / n!`.
* `QED.Polylog.HPL.hpl_cons_of_not_allZero`: the integral recursion.
* `QED.Polylog.HPL.perm_of_mem_shuffle`: every shuffle of `u` and `v` is a permutation of
  `u ++ v`.
-/

@[expose] public section

open Real

namespace QED.Polylog.HPL

/-- The letters `0`, `1`, `-1` of the HPL alphabet. -/
inductive Letter where
  /-- The letter `0`, with kernel `1 / t`. -/
  | zero
  /-- The letter `1`, with kernel `1 / (1 - t)`. -/
  | one
  /-- The letter `-1`, with kernel `1 / (1 + t)`. -/
  | negOne
  deriving DecidableEq, Repr

namespace Letter

/-- The kernel `f a` of a letter: `f 0 t = 1 / t`, `f 1 t = 1 / (1 - t)`,
`f (-1) t = 1 / (1 + t)`. -/
noncomputable def kernel : Letter → ℝ → ℝ
  | zero, t => t⁻¹
  | one, t => (1 - t)⁻¹
  | negOne, t => (1 + t)⁻¹

/-- The kernel of `0`. -/
@[simp] theorem kernel_zero (t : ℝ) : zero.kernel t = t⁻¹ := rfl

/-- The kernel of `1`. -/
@[simp] theorem kernel_one (t : ℝ) : one.kernel t = (1 - t)⁻¹ := rfl

/-- The kernel of `-1`. -/
@[simp] theorem kernel_negOne (t : ℝ) : negOne.kernel t = (1 + t)⁻¹ := rfl

end Letter

/-- A word all of whose letters are `0`. -/
def AllZero (w : List Letter) : Prop := ∀ a ∈ w, a = Letter.zero

instance (w : List Letter) : Decidable (AllZero w) :=
  inferInstanceAs (Decidable (∀ a ∈ w, a = Letter.zero))

@[simp] theorem allZero_nil : AllZero [] := by simp [AllZero]

@[simp] theorem allZero_cons {a : Letter} {w : List Letter} :
    AllZero (a :: w) ↔ a = Letter.zero ∧ AllZero w := by
  simp [AllZero]

theorem allZero_append {u v : List Letter} : AllZero (u ++ v) ↔ AllZero u ∧ AllZero v := by
  simp only [AllZero, List.mem_append]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  · rintro ⟨hu, hv⟩ a (ha | ha)
    · exact hu a ha
    · exact hv a ha

theorem AllZero.of_perm {u v : List Letter} (h : u.Perm v) (hu : AllZero u) : AllZero v :=
  fun a ha => hu a (h.mem_iff.2 ha)

/-- The harmonic polylogarithm `H(w; x)` for a word `w` over `{0, 1, -1}`:
`H([]; x) = 1`, `H(0ⁿ; x) = logⁿ x / n!`, and otherwise
`H(a · w; x) = ∫₀ˣ f a t · H(w; t) dt`. -/
noncomputable def hpl : List Letter → ℝ → ℝ
  | [], _ => 1
  | a :: w, x =>
    if AllZero (a :: w) then log x ^ (w.length + 1) / ((w.length + 1).factorial : ℝ)
    else ∫ t in (0 : ℝ)..x, a.kernel t * hpl w t

@[simp] theorem hpl_nil (x : ℝ) : hpl [] x = 1 := rfl

/-- The trailing-zero convention: `H(0ⁿ; x) = logⁿ x / n!`. -/
theorem hpl_of_allZero {w : List Letter} (h : AllZero w) (x : ℝ) :
    hpl w x = log x ^ w.length / (w.length.factorial : ℝ) := by
  cases w with
  | nil => simp
  | cons a w => simp only [hpl, h, ↓reduceIte, List.length_cons]

/-- The integral recursion `H(a · w; x) = ∫₀ˣ f a t · H(w; t) dt` for a word that is not all
zeros. -/
theorem hpl_cons_of_not_allZero {a : Letter} {w : List Letter} (h : ¬AllZero (a :: w)) :
    hpl (a :: w) = fun x => ∫ t in (0 : ℝ)..x, a.kernel t * hpl w t := by
  funext x
  simp only [hpl, h, ↓reduceIte]

/-- The integral recursion for a word whose first letter is not `0`. -/
theorem hpl_cons_of_ne_zero {a : Letter} (ha : a ≠ Letter.zero) (w : List Letter) :
    hpl (a :: w) = fun x => ∫ t in (0 : ℝ)..x, a.kernel t * hpl w t :=
  hpl_cons_of_not_allZero (by simp [ha])

/-- `H(w; 0) = 0` for a nonempty word. -/
theorem hpl_at_zero {w : List Letter} (hw : w ≠ []) : hpl w 0 = 0 := by
  obtain ⟨a, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  by_cases h : AllZero (a :: w)
  · simp [hpl_of_allZero h]
  · simp [hpl_cons_of_not_allZero h]

/-! ### Shuffles -/

section Shuffle

variable {α : Type*}

/-- Auxiliary for `shuffle`: given `a`, `u` and the function `shuffle u`, the shuffles of
`a :: u` with a word, by recursion on that word. -/
def shuffleAux (a : α) (u : List α) (su : List α → List (List α)) : List α → List (List α)
  | [] => [a :: u]
  | b :: v => (su (b :: v)).map (a :: ·) ++ (shuffleAux a u su v).map (b :: ·)

/-- The shuffles of two words, as a list of words counted with multiplicity:
`[] ⧢ v = [v]`, `u ⧢ [] = [u]` and
`(a :: u) ⧢ (b :: v) = a · (u ⧢ (b :: v)) + b · ((a :: u) ⧢ v)`. -/
def shuffle : List α → List α → List (List α)
  | [], v => [v]
  | a :: u, v => shuffleAux a u (shuffle u) v

@[simp] theorem shuffle_nil_left (v : List α) : shuffle [] v = [v] := rfl

@[simp] theorem shuffle_nil_right (u : List α) : shuffle u [] = [u] := by
  cases u <;> rfl

theorem shuffle_cons_cons (a b : α) (u v : List α) :
    shuffle (a :: u) (b :: v) =
      (shuffle u (b :: v)).map (a :: ·) ++ (shuffle (a :: u) v).map (b :: ·) := rfl

/-- Every shuffle of `u` and `v` is a permutation of `u ++ v`. -/
theorem perm_of_mem_shuffle : ∀ {u v w : List α}, w ∈ shuffle u v → w.Perm (u ++ v)
  | [], v, w, h => by
    rw [shuffle_nil_left, List.mem_singleton] at h
    simp [h]
  | a :: u, [], w, h => by
    rw [shuffle_nil_right, List.mem_singleton] at h
    simp [h]
  | a :: u, b :: v, w, h => by
    rw [shuffle_cons_cons, List.mem_append, List.mem_map, List.mem_map] at h
    rcases h with ⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩
    · exact (perm_of_mem_shuffle hw').cons a
    · exact ((perm_of_mem_shuffle hw').cons b).trans List.perm_middle.symm
termination_by u v => u.length + v.length

/-- Every shuffle of `u` and `v` has length `u.length + v.length`. -/
theorem length_of_mem_shuffle {u v w : List α} (h : w ∈ shuffle u v) :
    w.length = u.length + v.length := by
  rw [(perm_of_mem_shuffle h).length_eq, List.length_append]

end Shuffle

/-- A shuffle of two words is all zeros exactly when both words are. -/
theorem allZero_of_mem_shuffle_iff {u v w : List Letter} (h : w ∈ shuffle u v) :
    AllZero w ↔ AllZero u ∧ AllZero v := by
  rw [← allZero_append]
  exact ⟨fun hw => hw.of_perm (perm_of_mem_shuffle h),
    fun huv => huv.of_perm (perm_of_mem_shuffle h).symm⟩

end QED.Polylog.HPL
