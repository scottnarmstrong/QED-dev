/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.IBPCertSym
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Symmetry terms and relabellings for the set (e) certificates

The label-split certificates of set (e) reduce a target to a master list `Ms` of the checker
that holds the Kira masters and, for each symmetry entry `(σ, ν, ζ)`, the two terms `(ν, ζ)` and
`(permLabel σ ν, -ζ)`. Under the relabelling hypothesis `I(permLabel σ ν) = I(ν)` the two terms
cancel, so a reduction to `Ms` is a reduction to the masters.

## Main statements

* `QED.ThreeLoopE.SetECert.symTerms`: the terms of a list of symmetry entries.
* `QED.ThreeLoopE.SetECert.masters_of_comb`: if `Ms - (masters + symTerms S)` normalizes to the
  empty combination, then under the symmetry hypotheses the combinations `Σ (n / q) I` over `Ms`
  and over the masters agree.
* `QED.ThreeLoopE.SetECert.masters_of_comb_rel`: the same with further relations `r` (numerator
  symmetries) entering with multipliers `ζ` as the terms `relTerms`, under `eval r = 0`.
* `QED.ThreeLoopE.SetECert.sum_relabel`: a combination of the integrals `I(ν)` equals the
  relabelled combination of the integrals `J(permLabel σ ν)` when `I(ν) = J(permLabel σ ν)` on
  its labels (for families related by a change of loop momenta mapping every line to a line).
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert

/-- The terms of symmetry entries `(σ, ν, ζ)`: `(ν, ζ)` and `(permLabel σ ν, -ζ)`. -/
def symTerms (S : List (List ℕ × List ℤ × Poly)) : List (List ℤ × Poly) :=
  S.flatMap fun e => [(e.2.1, e.2.2), (permLabel e.1 e.2.1, Poly.neg e.2.2)]

theorem lc_eval_append {K : Type*} [Field K] (J : List ℤ → K) (d : K) :
    ∀ l m : LinComb, LinComb.eval J d (l ++ m) = LinComb.eval J d l + LinComb.eval J d m
  | [], m => by simp
  | t :: l, m => by
    rw [List.cons_append, LinComb.eval_cons, LinComb.eval_cons, lc_eval_append J d l m]; ring

theorem sum_div_eq_eval {K : Type*} [Field K] (n : ℕ) (I : (Fin n → ℤ) → K → K) (d c : K) :
    ∀ l : List (List ℤ × Poly),
      (l.map fun m => Poly.eval d m.2 / c * I (toVec n m.1) d).sum =
        LinComb.eval (fun l => I (toVec n l) d) d l / c
  | [] => by simp
  | t :: l => by
    simp only [List.map_cons, List.sum_cons, LinComb.eval_cons, sum_div_eq_eval n I d c l]; ring

theorem eval_symTerms {K : Type*} [Field K] (F : Family) (I : (Fin F.nProp → ℤ) → K → K)
    (d : K) : ∀ S : List (List ℕ × List ℤ × Poly), (∀ e ∈ S, F.SymHoldsAt I d e.1 e.2.1) →
      LinComb.eval (fun l => I (toVec F.nProp l) d) d (symTerms S) = 0
  | [], _ => rfl
  | e :: S, h => by
    have h1 : F.SymHoldsAt I d e.1 e.2.1 := h e List.mem_cons_self
    have h2 := eval_symTerms F I d S fun e' he' => h e' (List.mem_cons_of_mem _ he')
    unfold Family.SymHoldsAt at h1
    simp only [symTerms, List.flatMap_cons] at h2 ⊢
    rw [lc_eval_append, h2]
    simp only [LinComb.eval_cons, LinComb.eval_nil, Poly.eval_neg, h1]
    ring

/-- A reduction to the checker's master list `Ms` is a reduction to the masters when
`Ms - (masters + symTerms S)` normalizes to the empty combination and the symmetry entries of
`S` hold. -/
theorem masters_of_comb {K : Type*} [Field K] (F : Family) (I : (Fin F.nProp → ℤ) → K → K)
    (d : K) (den : Poly) (Ms Mas : List (List ℤ × Poly)) (S : List (List ℕ × List ℤ × Poly))
    (hc : LinComb.ofTerms (Ms ++ LinComb.smul [-1] (Mas ++ symTerms S)) = [])
    (hs : ∀ e ∈ S, F.SymHoldsAt I d e.1 e.2.1) :
    (Ms.map fun m => Poly.eval d m.2 / Poly.eval d den * I (toVec F.nProp m.1) d).sum =
      (Mas.map fun m => Poly.eval d m.2 / Poly.eval d den * I (toVec F.nProp m.1) d).sum := by
  have h := congrArg (LinComb.eval (fun l => I (toVec F.nProp l) d) d) hc
  rw [LinComb.eval_ofTerms, lc_eval_append, LinComb.eval_smul, lc_eval_append,
    eval_symTerms F I d S hs] at h
  simp only [LinComb.eval_nil, Poly.eval_cons, Poly.eval_nil] at h
  rw [sum_div_eq_eval, sum_div_eq_eval]
  congr 1
  push_cast at h
  linear_combination h

/-- The terms of relations with multipliers `(r, ζ)`: the terms of `ζ r`. -/
def relTerms (R : List (LinComb × Poly)) : List (List ℤ × Poly) :=
  R.flatMap fun e => LinComb.smul e.2 e.1

theorem eval_relTerms {K : Type*} [Field K] (J : List ℤ → K) (d : K) :
    ∀ R : List (LinComb × Poly), (∀ e ∈ R, LinComb.eval J d e.1 = 0) →
      LinComb.eval J d (relTerms R) = 0
  | [], _ => rfl
  | e :: R, h => by
    have h2 := eval_relTerms J d R fun e' he' => h e' (List.mem_cons_of_mem _ he')
    simp only [relTerms, List.flatMap_cons] at h2 ⊢
    rw [lc_eval_append, h2, LinComb.eval_smul, h e List.mem_cons_self]
    ring

/-- `masters_of_comb` with further relations `R` (each `(r, ζ)` with `eval r = 0`). -/
theorem masters_of_comb_rel {K : Type*} [Field K] (F : Family) (I : (Fin F.nProp → ℤ) → K → K)
    (d : K) (den : Poly) (Ms Mas : List (List ℤ × Poly)) (S : List (List ℕ × List ℤ × Poly))
    (R : List (LinComb × Poly))
    (hc : LinComb.ofTerms (Ms ++ LinComb.smul [-1] (Mas ++ symTerms S ++ relTerms R)) = [])
    (hs : ∀ e ∈ S, F.SymHoldsAt I d e.1 e.2.1)
    (hn : ∀ e ∈ R, LinComb.eval (fun l => I (toVec F.nProp l) d) d e.1 = 0) :
    (Ms.map fun m => Poly.eval d m.2 / Poly.eval d den * I (toVec F.nProp m.1) d).sum =
      (Mas.map fun m => Poly.eval d m.2 / Poly.eval d den * I (toVec F.nProp m.1) d).sum := by
  have h := congrArg (LinComb.eval (fun l => I (toVec F.nProp l) d) d) hc
  rw [LinComb.eval_ofTerms, lc_eval_append, LinComb.eval_smul, lc_eval_append, lc_eval_append,
    eval_symTerms F I d S hs, eval_relTerms _ d R hn] at h
  simp only [LinComb.eval_nil, Poly.eval_cons, Poly.eval_nil] at h
  rw [sum_div_eq_eval, sum_div_eq_eval]
  congr 1
  push_cast at h
  linear_combination h

/-- Relabelling a combination: if `I(ν) = J(permLabel σ ν)` on the labels of `T`, the
combination `Σ f(t) I(ν)` equals the combination of `J` over the relabelled list. -/
theorem sum_relabel {K : Type*} [Field K] (n m : ℕ) (σ : List ℕ) (I : (Fin n → ℤ) → K → K)
    (J : (Fin m → ℤ) → K → K) (d : K) (f : Poly → K) :
    ∀ T : List (List ℤ × Poly),
      (∀ t ∈ T, I (toVec n t.1) d = J (toVec m (permLabel σ t.1)) d) →
      (T.map fun t => f t.2 * I (toVec n t.1) d).sum =
        ((T.map fun t => (permLabel σ t.1, t.2)).map fun t => f t.2 * J (toVec m t.1) d).sum
  | [], _ => rfl
  | t :: T, h => by
    simp only [List.map_cons, List.sum_cons]
    rw [h t List.mem_cons_self,
      sum_relabel n m σ I J d f T fun t' ht' => h t' (List.mem_cons_of_mem _ ht')]

end QED.ThreeLoopE.SetECert
