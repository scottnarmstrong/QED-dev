/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Kernel-checked linear combinations with coefficients in `ℤ[d]` (IBP certificates, layer L2)

Integration-by-parts reductions are produced by untrusted programs and checked in Lean as
certificates whose arithmetic is carried out by the kernel (`decide +kernel`), in the style of
the interval checker `QED.Numerics.Interval` (decision D-34, author choice P2). This module holds
the computable data structures and the abstract checker.

* A polynomial in `ℤ[d]` is a list of integer coefficients, constant term first
  (`QED.Algebra.IBPCert.Poly`). Rational functions in `ℚ(d)` are represented by numerators over
  one common denominator: a certificate clears all denominators at once.
* A linear combination of symbolic integrals is a list of pairs `(label, coefficient)`, the
  label an index vector `ν ∈ ℤᴺ` written as a list (`QED.Algebra.IBPCert.LinComb`). The checker
  keeps combinations sorted by label and merges them; the order only matters for completeness,
  soundness only needs that labels compared equal are equal.
* `QED.Algebra.IBPCert.checkCombo` checks that `Σ cₖ Rₖ - q · [T] + Σ nⱼ [Mⱼ]` vanishes term by
  term, except for terms whose label a given predicate declares zero, and that `q ≠ 0` as a
  polynomial.

Everything is evaluated in an arbitrary field `K` at a point `d : K`, against an arbitrary
family `J : List ℤ → K` of values attached to the labels.

## Main statements

* `QED.Algebra.IBPCert.LinComb.eval_add`, `eval_sumTree`: merging is evaluation-additive.
* `QED.Algebra.IBPCert.checkCombo_sound`: if the check passes, every relation `Rₖ` evaluates to
  `0`, the declared-zero labels evaluate to `0`, and `q(d) ≠ 0`, then
  `J T = Σ (nⱼ(d) / q(d)) · J Mⱼ`.
* `QED.Algebra.IBPCert.Poly.exists_finset_eval_ne_zero`: in characteristic `0`, a polynomial
  the checker accepts as nonzero vanishes only on a finite set.
-/

@[expose] public section

namespace QED.Algebra.IBPCert

/-! ### Integer and label comparisons that reduce well in the kernel -/

/-- Three-way comparison of natural numbers through `Nat.blt` and `Nat.beq` (GMP-accelerated in
the kernel). -/
def natCmp (a b : ℕ) : Ordering :=
  bif Nat.blt a b then .lt else bif Nat.beq a b then .eq else .gt

theorem eq_of_natCmp_eq {a b : ℕ} (h : natCmp a b = .eq) : a = b := by
  unfold natCmp at h
  cases h1 : Nat.blt a b <;> cases h2 : Nat.beq a b <;> simp_all

/-- Three-way comparison of integers by constructors and `natCmp`. -/
def intCmp : ℤ → ℤ → Ordering
  | .ofNat a, .ofNat b => natCmp a b
  | .ofNat _, .negSucc _ => .gt
  | .negSucc _, .ofNat _ => .lt
  | .negSucc a, .negSucc b => natCmp b a

theorem eq_of_intCmp_eq {a b : ℤ} (h : intCmp a b = .eq) : a = b := by
  cases a <;> cases b <;> simp only [intCmp, reduceCtorEq] at h
  · rw [eq_of_natCmp_eq h]
  · rw [eq_of_natCmp_eq h]

/-- `a = 0` for an integer, decided by constructors and `Nat.beq`. -/
def intIsZero : ℤ → Bool
  | .ofNat a => Nat.beq a 0
  | .negSucc _ => false

theorem eq_zero_of_intIsZero {a : ℤ} (h : intIsZero a = true) : a = 0 := by
  cases a with
  | ofNat a => simp only [intIsZero] at h; simp [Nat.eq_of_beq_eq_true h]
  | negSucc a => simp [intIsZero] at h

/-- `a ≤ 0` for an integer, decided by constructors and `Nat.beq`. -/
def intNonpos : ℤ → Bool
  | .ofNat a => Nat.beq a 0
  | .negSucc _ => true

theorem nonpos_of_intNonpos {a : ℤ} (h : intNonpos a = true) : a ≤ 0 := by
  cases a with
  | ofNat a => simp only [intNonpos] at h; simp [Nat.eq_of_beq_eq_true h]
  | negSucc a => exact (Int.negSucc_lt_zero a).le

/-- Lexicographic comparison of labels (integer lists). -/
def labelCmp : List ℤ → List ℤ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: l, b :: m =>
    match intCmp a b with
    | .eq => labelCmp l m
    | o => o

theorem eq_of_labelCmp_eq : ∀ {l m : List ℤ}, labelCmp l m = .eq → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [labelCmp] at h
  | _ :: _, [], h => by simp [labelCmp] at h
  | a :: l, b :: m, h => by
    unfold labelCmp at h
    cases hab : intCmp a b <;> rw [hab] at h <;> try simp at h
    rw [eq_of_intCmp_eq hab, eq_of_labelCmp_eq h]

/-! ### Polynomials in `ℤ[d]` -/

/-- A polynomial in `ℤ[d]`, as its list of coefficients, constant term first. Trailing zeros
are allowed. -/
abbrev Poly := List ℤ

namespace Poly

theorem int_add_eq (a b : ℤ) : Int.add a b = a + b := rfl

theorem int_mul_eq (a b : ℤ) : Int.mul a b = a * b := rfl

/-- Sum of polynomials. -/
def add : Poly → Poly → Poly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => Int.add a b :: add p q

/-- Product by an integer. -/
def smul (c : ℤ) : Poly → Poly
  | [] => []
  | a :: p => Int.mul c a :: smul c p

/-- Product of polynomials. -/
def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)

/-- Negation. -/
def neg (p : Poly) : Poly := smul (-1) p

/-- Whether every coefficient vanishes. -/
def isZero : Poly → Bool
  | [] => true
  | a :: p => intIsZero a && isZero p

/-- Evaluation at `d` in a ring, by Horner's rule. -/
def eval {K : Type*} [Ring K] (d : K) : Poly → K
  | [] => 0
  | a :: p => (a : K) + d * eval d p

variable {K : Type*} [CommRing K] (d : K)

@[simp] theorem eval_nil : eval d ([] : Poly) = 0 := rfl

@[simp] theorem eval_cons (a : ℤ) (p : Poly) : eval d (a :: p) = (a : K) + d * eval d p := rfl

theorem eval_add : ∀ p q : Poly, eval d (add p q) = eval d p + eval d q
  | [], q => by simp [add]
  | a :: p, [] => by simp [add]
  | a :: p, b :: q => by simp only [add, eval_cons, eval_add p q, int_add_eq]; push_cast; ring

theorem eval_smul (c : ℤ) : ∀ p : Poly, eval d (smul c p) = c * eval d p
  | [] => by simp [smul]
  | a :: p => by simp only [smul, eval_cons, eval_smul c p, int_mul_eq]; push_cast; ring

theorem eval_mul : ∀ p q : Poly, eval d (mul p q) = eval d p * eval d q
  | [], q => by simp [mul]
  | a :: p, q => by
    simp only [mul, eval_add, eval_smul, eval_cons, eval_mul p q]; push_cast; ring

theorem eval_neg (p : Poly) : eval d (neg p) = -eval d p := by
  simp [neg, eval_smul]

theorem eval_eq_zero_of_isZero : ∀ {p : Poly}, isZero p = true → eval d p = 0
  | [], _ => rfl
  | a :: p, h => by
    simp only [isZero, Bool.and_eq_true] at h
    simp [eq_zero_of_intIsZero h.1, eval_eq_zero_of_isZero h.2]

/-! #### Nonzero polynomials have finitely many roots -/

/-- The polynomial in `K[X]` with the given integer coefficients. -/
noncomputable def toPolynomial {K : Type*} [CommRing K] : Poly → Polynomial K
  | [] => 0
  | a :: p => Polynomial.C (a : K) + Polynomial.X * toPolynomial p

theorem eval_toPolynomial : ∀ p : Poly, (toPolynomial p).eval d = eval d p
  | [] => by simp [toPolynomial]
  | a :: p => by simp [toPolynomial, eval_toPolynomial p]

theorem toPolynomial_ne_zero {K : Type*} [Field K] [CharZero K] :
    ∀ {p : Poly}, isZero p = false → (toPolynomial p : Polynomial K) ≠ 0
  | [], h => by simp [isZero] at h
  | a :: p, h => by
    intro h0
    have hc0 : ((toPolynomial (a :: p) : Polynomial K)).coeff 0 = (a : K) := by
      simp [toPolynomial]
    have hX : ∀ n, ((toPolynomial (a :: p) : Polynomial K)).coeff (n + 1) =
        (toPolynomial p : Polynomial K).coeff n := by
      intro n
      rw [toPolynomial, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul]
      simp
    have ha : a = 0 := by
      have := hc0; rw [h0, Polynomial.coeff_zero] at this; exact_mod_cast this.symm
    have hp : (toPolynomial p : Polynomial K) = 0 := by
      ext n; rw [← hX n, h0, Polynomial.coeff_zero, Polynomial.coeff_zero]
    have hz : isZero p = false := by
      simpa [isZero, ha, intIsZero] using h
    exact toPolynomial_ne_zero hz hp

/-- A polynomial that the checker accepts as nonzero vanishes only on a finite set of points of
a field of characteristic `0`. -/
theorem exists_finset_eval_ne_zero {K : Type*} [Field K] [CharZero K] {p : Poly}
    (h : isZero p = false) : ∃ s : Finset K, ∀ d ∉ s, eval d p ≠ 0 := by
  classical
  refine ⟨(toPolynomial p : Polynomial K).roots.toFinset, fun d hd h0 => hd ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (toPolynomial_ne_zero h),
    Polynomial.IsRoot.def, eval_toPolynomial, h0]

end Poly

/-! ### Linear combinations of labelled integrals -/

/-- A linear combination `Σ pᵢ(d) · [νᵢ]` of symbolic integrals with labels `νᵢ` (integer
lists) and polynomial coefficients. -/
abbrev LinComb := List (List ℤ × Poly)

namespace LinComb

variable {K : Type*} [CommRing K] (J : List ℤ → K) (d : K)

/-- Evaluation: `Σ pᵢ(d) · J νᵢ`. -/
def eval : LinComb → K
  | [] => 0
  | t :: ts => Poly.eval d t.2 * J t.1 + eval ts

@[simp] theorem eval_nil : eval J d [] = 0 := rfl

@[simp] theorem eval_cons (t : List ℤ × Poly) (ts : LinComb) :
    eval J d (t :: ts) = Poly.eval d t.2 * J t.1 + eval J d ts := rfl

/-- Merge step: insert the sorted list `t :: ts` into a sorted list, given the merge `rec` of
`ts` with anything. Terms with equal labels are combined, and dropped if they cancel. -/
def addCons (t : List ℤ × Poly) (ts : LinComb) (rec : LinComb → LinComb) : LinComb → LinComb
  | [] => t :: ts
  | u :: us =>
    match labelCmp t.1 u.1 with
    | .lt => t :: rec (u :: us)
    | .gt => u :: addCons t ts rec us
    | .eq =>
      let p := Poly.add t.2 u.2
      bif Poly.isZero p then rec us else (t.1, p) :: rec us

/-- Merge of two combinations sorted by label (structural recursion on both lists). -/
def add : LinComb → LinComb → LinComb
  | [], m => m
  | t :: ts, m => addCons t ts (add ts) m

theorem eval_addCons (t : List ℤ × Poly) (ts : LinComb) (rec : LinComb → LinComb)
    (hrec : ∀ m, eval J d (rec m) = eval J d ts + eval J d m) :
    ∀ m, eval J d (addCons t ts rec m) = eval J d (t :: ts) + eval J d m
  | [] => by simp [addCons]
  | u :: us => by
    unfold addCons
    cases h : labelCmp t.1 u.1
    · simp only [eval_cons, hrec]; ring
    · have hl := eq_of_labelCmp_eq h
      cases hz : Poly.isZero (Poly.add t.2 u.2)
      · simp only [hz, Bool.cond_false, eval_cons, hrec, Poly.eval_add, hl]; ring
      · have h0 := Poly.eval_eq_zero_of_isZero d hz
        rw [Poly.eval_add] at h0
        simp only [hz, Bool.cond_true, hrec, eval_cons, hl]
        linear_combination (-J u.1) * h0
    · simp only [eval_cons, eval_addCons t ts rec hrec us]; ring

theorem eval_add : ∀ l m : LinComb, eval J d (add l m) = eval J d l + eval J d m
  | [], m => by simp [add]
  | t :: ts, m => eval_addCons J d t ts (add ts) (eval_add ts) m

/-- Product of every coefficient by a polynomial. -/
def smul (p : Poly) (l : LinComb) : LinComb := l.map fun t => (t.1, Poly.mul p t.2)

theorem eval_smul (p : Poly) : ∀ l : LinComb, eval J d (smul p l) = Poly.eval d p * eval J d l
  | [] => by simp [smul]
  | t :: ts => by
    have := eval_smul p ts
    simp only [smul, List.map_cons, eval_cons, Poly.eval_mul] at this ⊢
    rw [this]; ring

/-- The sorted combination of a list of terms, inserting one term at a time and skipping
vanishing coefficients. -/
def ofTerms : List (List ℤ × Poly) → LinComb
  | [] => []
  | t :: ts => bif Poly.isZero t.2 then ofTerms ts else add [t] (ofTerms ts)

theorem eval_ofTerms : ∀ ts : List (List ℤ × Poly), eval J d (ofTerms ts) = eval J d ts
  | [] => rfl
  | t :: ts => by
    unfold ofTerms
    cases hz : Poly.isZero t.2
    · simp [eval_add, eval_ofTerms ts]
    · simp [eval_ofTerms ts, Poly.eval_eq_zero_of_isZero d hz]

/-- One round of pairwise merging. -/
def pairs : List LinComb → List LinComb
  | [] => []
  | [l] => [l]
  | l :: m :: rest => add l m :: pairs rest

/-- Balanced merging of a list of combinations: `fuel` rounds of pairwise merging, then a
right fold. -/
def sumTree : ℕ → List LinComb → LinComb
  | 0, ls => ls.foldr add []
  | k + 1, ls =>
    match ls with
    | [] => []
    | [l] => l
    | l :: m :: rest => sumTree k (pairs (l :: m :: rest))

theorem sum_pairs : ∀ ls : List LinComb,
    ((pairs ls).map (eval J d)).sum = (ls.map (eval J d)).sum
  | [] => rfl
  | [_] => rfl
  | l :: m :: rest => by
    simp only [pairs, List.map_cons, List.sum_cons, eval_add, sum_pairs rest]; ring

theorem eval_foldr_add : ∀ ls : List LinComb,
    eval J d (ls.foldr add []) = (ls.map (eval J d)).sum
  | [] => rfl
  | l :: ls => by simp [eval_add, eval_foldr_add ls]

theorem eval_sumTree : ∀ (k : ℕ) (ls : List LinComb),
    eval J d (sumTree k ls) = (ls.map (eval J d)).sum
  | 0, ls => eval_foldr_add J d ls
  | _ + 1, [] => by simp [sumTree]
  | _ + 1, [l] => by simp [sumTree]
  | k + 1, l :: m :: rest => by
    rw [sumTree, eval_sumTree k, sum_pairs]

/-- Whether every term either has a vanishing coefficient or a label declared zero by `z`. -/
def vanishes (z : List ℤ → Bool) (l : LinComb) : Bool :=
  l.all fun t => z t.1 || Poly.isZero t.2

theorem eval_eq_zero_of_vanishes {z : List ℤ → Bool} (hz : ∀ ν, z ν = true → J ν = 0) :
    ∀ {l : LinComb}, vanishes z l = true → eval J d l = 0
  | [], _ => rfl
  | t :: ts, h => by
    simp only [vanishes, List.all_cons, Bool.and_eq_true, Bool.or_eq_true] at h
    rw [eval_cons, eval_eq_zero_of_vanishes hz (l := ts) h.2]
    rcases h.1 with h1 | h1
    · simp [hz _ h1]
    · simp [Poly.eval_eq_zero_of_isZero d h1]

end LinComb

/-! ### The abstract checker -/

/-- The combination `Σ cₖ Rₖ - q · [T] + Σ nⱼ [Mⱼ]` that a certificate claims to vanish, for
relations `Rₖ` with multipliers `cₖ`, target `T`, common denominator `q` and master
numerators `nⱼ`. -/
def combo (rels : List (LinComb × Poly)) (target : List ℤ) (den : Poly)
    (masters : List (List ℤ × Poly)) : LinComb :=
  LinComb.sumTree 64
    (LinComb.ofTerms ((target, Poly.neg den) :: masters) ::
      rels.map fun r => LinComb.smul r.2 r.1)

/-- The abstract certificate check: the denominator is a nonzero polynomial and the combination
`combo` vanishes, up to labels declared zero by `z`. -/
def checkCombo (z : List ℤ → Bool) (rels : List (LinComb × Poly)) (target : List ℤ)
    (den : Poly) (masters : List (List ℤ × Poly)) : Bool :=
  !Poly.isZero den && LinComb.vanishes z (combo rels target den masters)

theorem isZero_den_of_checkCombo {z : List ℤ → Bool} {rels : List (LinComb × Poly)}
    {target : List ℤ} {den : Poly} {masters : List (List ℤ × Poly)}
    (h : checkCombo z rels target den masters = true) : Poly.isZero den = false := by
  simp only [checkCombo, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1

/-- Soundness of the abstract checker. If `checkCombo` accepts, every relation evaluates to
`0`, every label declared zero evaluates to `0`, and `q(d) ≠ 0`, then
`J T = Σ (nⱼ(d) / q(d)) · J Mⱼ`. -/
theorem checkCombo_sound {K : Type*} [Field K] (J : List ℤ → K) (d : K)
    {z : List ℤ → Bool} {rels : List (LinComb × Poly)} {target : List ℤ} {den : Poly}
    {masters : List (List ℤ × Poly)} (h : checkCombo z rels target den masters = true)
    (hrels : ∀ r ∈ rels, LinComb.eval J d r.1 = 0) (hz : ∀ ν, z ν = true → J ν = 0)
    (hden : Poly.eval d den ≠ 0) :
    J target = (masters.map fun m => Poly.eval d m.2 / Poly.eval d den * J m.1).sum := by
  simp only [checkCombo, Bool.and_eq_true] at h
  have h0 := LinComb.eval_eq_zero_of_vanishes J d hz h.2
  rw [combo, LinComb.eval_sumTree, List.map_cons, List.sum_cons, LinComb.eval_ofTerms,
    LinComb.eval_cons, Poly.eval_neg] at h0
  have hr : ((rels.map fun r => LinComb.smul r.2 r.1).map (LinComb.eval J d)).sum = 0 := by
    rw [List.map_map]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    simp [LinComb.eval_smul, hrels r hr]
  have hm : ∀ ms : List (List ℤ × Poly), LinComb.eval J d ms =
      Poly.eval d den * (ms.map fun m => Poly.eval d m.2 / Poly.eval d den * J m.1).sum := by
    intro ms
    induction ms with
    | nil => simp
    | cons m ms ih => simp only [LinComb.eval_cons, ih, List.map_cons, List.sum_cons];
                      field_simp
  rw [hr, hm] at h0
  apply mul_left_cancel₀ hden
  linear_combination -h0

end QED.Algebra.IBPCert
