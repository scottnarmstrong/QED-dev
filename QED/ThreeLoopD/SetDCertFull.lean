/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDCertFullChecks
public import QED.ThreeLoopD.SetDCertFullPart0
public import QED.ThreeLoopD.SetDCertFullPart1
public import QED.ThreeLoopD.SetDCertFullPart2
public import QED.ThreeLoopD.SetDCertFullPart3
public import QED.ThreeLoopD.SetDCertFullPart4
public import QED.ThreeLoopD.SetDCertFullPart5
public import QED.ThreeLoopD.SetDCertFullPart6
public import QED.ThreeLoopD.SetDCertFullPart7
public import QED.ThreeLoopD.SetDCertFullPart8
public import QED.ThreeLoopD.SetDCertFullPart9
public import QED.ThreeLoopD.SetDCertFullPart10
public import QED.ThreeLoopD.SetDCertFullPart11
public import QED.ThreeLoopD.SetDCertFullPart12
public import QED.ThreeLoopD.SetDCertFullPart13
public import QED.ThreeLoopD.SetDCertFullPart14
public import QED.ThreeLoopD.SetDCertFullPart15
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The full IBP reduction of set (d)

The label-split certificate of `QED.Algebra.IBPCertSector` reduces the projected set (d)
combination `QED.ThreeLoopD.SetDCertFull.sdTarget` of `QED.ThreeLoopD.SetDCert.lbl` integrals to
the eleven Laporta–Remiddi masters `QED.ThreeLoopD.SetDCertFull.sdMasters`, with the IBP
relations, the scaleless sectors and the relabelling symmetries `I(permLabel σ ν) = I(ν)` of the
entries of `QED.ThreeLoopD.SetDCertFull.sdSyms` (one per IBP master in a copy of a sector, or
second master of a sector). The checker reduces to a master list `sdMs` holding the masters and
the terms of the symmetry entries; these cancel in pairs under the symmetry hypotheses.

## Main statements

* `QED.ThreeLoopD.SetDCertFull.setD_reduction_at`: at `d` with `q(d) ≠ 0`, for every family of
  values satisfying the IBP relations, the scaleless sectors of `lbl` and the symmetry entries,
  the target combination equals the certified combination of the masters.
* `QED.ThreeLoopD.SetDCertFull.setD_reduction`: the same off a finite set of `d`.
-/

@[expose] public section

namespace QED.ThreeLoopD.SetDCertFull

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Sector QED.ThreeLoopD.SetDCert

theorem sd_parts : ∀ p < 16, partOk sdCtx sdDen (rGetL (chunks sdTargetL sdTarget) p)
    (rGetL (chunks sdMsL sdMs) p) sdBlocks p = true := fun p hp =>
  match p, hp with
  | 0, _ => sdPart0
  | 1, _ => sdPart1
  | 2, _ => sdPart2
  | 3, _ => sdPart3
  | 4, _ => sdPart4
  | 5, _ => sdPart5
  | 6, _ => sdPart6
  | 7, _ => sdPart7
  | 8, _ => sdPart8
  | 9, _ => sdPart9
  | 10, _ => sdPart10
  | 11, _ => sdPart11
  | 12, _ => sdPart12
  | 13, _ => sdPart13
  | 14, _ => sdPart14
  | 15, _ => sdPart15
  | _ + 16, h => absurd h (by omega)

theorem eval_append {K : Type*} [Field K] (J : List ℤ → K) (d : K) :
    ∀ l m : LinComb, LinComb.eval J d (l ++ m) = LinComb.eval J d l + LinComb.eval J d m
  | [], m => by simp
  | t :: l, m => by
    rw [List.cons_append, LinComb.eval_cons, LinComb.eval_cons, eval_append J d l m]; ring

theorem sum_div_eq {K : Type*} [Field K] (I : (Fin lbl.nProp → ℤ) → K → K) (d c : K) :
    ∀ l : List (List ℤ × Poly),
      (l.map fun m => Poly.eval d m.2 / c * I (toVec lbl.nProp m.1) d).sum =
        LinComb.eval (fun l => I (toVec lbl.nProp l) d) d l / c
  | [] => by simp
  | t :: l => by
    simp only [List.map_cons, List.sum_cons, LinComb.eval_cons, sum_div_eq I d c l]; ring

theorem eval_symTerms {K : Type*} [Field K] (I : (Fin lbl.nProp → ℤ) → K → K) (d : K) :
    ∀ S : List (List ℕ × List ℤ × Poly), (∀ e ∈ S, lbl.SymHoldsAt I d e.1 e.2.1) →
      LinComb.eval (fun l => I (toVec lbl.nProp l) d) d (symTerms S) = 0
  | [], _ => rfl
  | e :: S, h => by
    have h1 : lbl.SymHoldsAt I d e.1 e.2.1 := h e List.mem_cons_self
    have h2 := eval_symTerms I d S fun e' he' => h e' (List.mem_cons_of_mem _ he')
    unfold Family.SymHoldsAt at h1
    simp only [symTerms, List.flatMap_cons] at h2 ⊢
    rw [eval_append, h2]
    simp only [LinComb.eval_cons, LinComb.eval_nil, Poly.eval_neg, h1]
    ring

/-- **The full set (d) reduction at a point.** At `d` with `q(d) ≠ 0`, for every family of
values `I` satisfying the IBP relations, the scaleless sectors of `lbl` and the relabelling
symmetries of `sdSyms` at `d`, the target combination `Σ tₗ(d) I(l)` equals
`Σ (nⱼ(d) / q(d)) I(Mⱼ)` over the eleven masters. -/
theorem setD_reduction_at {K : Type*} [Field K] (I : (Fin lbl.nProp → ℤ) → K → K) (d : K)
    (hI : lbl.IBPHolds I d) (hz : lbl.ZeroSectors I d)
    (hs : ∀ e ∈ sdSyms, lbl.SymHoldsAt I d e.1 e.2.1) (hq : Poly.eval d sdDen ≠ 0) :
    (sdTarget.map fun t => Poly.eval d t.2 * I (toVec lbl.nProp t.1) d).sum =
      (sdMasters.map fun m =>
        Poly.eval d m.2 / Poly.eval d sdDen * I (toVec lbl.nProp m.1) d).sum := by
  have h := gcert_reduction (P := 16) (den := sdDen) (T := sdTarget) (Ms := sdMs)
    (tl := sdTargetL) (ml := sdMsL) sdMT_ok sdFac_ok sdZS_eq sdBlocks_ok sdClaim_range
    sdTargetL_lt sdMsL_lt sdBound sd_parts I d hI hz hq
  have hc := congrArg (LinComb.eval (fun l => I (toVec lbl.nProp l) d) d) sdMs_comb
  rw [LinComb.eval_ofTerms, eval_append, LinComb.eval_smul, eval_append,
    eval_symTerms I d sdSyms hs] at hc
  simp only [LinComb.eval_nil, Poly.eval_cons, Poly.eval_nil] at hc
  rw [h, sum_div_eq, sum_div_eq]
  congr 1
  push_cast at hc
  linear_combination hc

/-- **The full set (d) reduction.** Off a finite set of dimensions `d`, `q(d) ≠ 0` and, for
every family of values `I` satisfying the IBP relations, the scaleless sectors of `lbl` and the
relabelling symmetries of `sdSyms` at `d`, the target combination equals the certified
combination of the eleven masters. -/
theorem setD_reduction {K : Type*} [Field K] [CharZero K] :
    ∃ s : Finset K, ∀ d ∉ s, Poly.eval d sdDen ≠ 0 ∧
      ∀ I : (Fin lbl.nProp → ℤ) → K → K, lbl.IBPHolds I d → lbl.ZeroSectors I d →
        (∀ e ∈ sdSyms, lbl.SymHoldsAt I d e.1 e.2.1) →
        (sdTarget.map fun t => Poly.eval d t.2 * I (toVec lbl.nProp t.1) d).sum =
          (sdMasters.map fun m =>
            Poly.eval d m.2 / Poly.eval d sdDen * I (toVec lbl.nProp m.1) d).sum := by
  obtain ⟨s, hs⟩ := Poly.exists_finset_eval_ne_zero (K := K) sdDen_ne_zero
  exact ⟨s, fun d hd => ⟨hs d hd, fun I hI hz hsym =>
    setD_reduction_at I d hI hz hsym (hs d hd)⟩⟩

end QED.ThreeLoopD.SetDCertFull
