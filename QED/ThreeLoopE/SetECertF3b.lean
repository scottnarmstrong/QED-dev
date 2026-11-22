/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3bFamily
public import QED.Algebra.IBPCertSectorSound
public import QED.ThreeLoopE.SetECertSymTerms
public import QED.ThreeLoopE.SetECertF3bData9
public import QED.ThreeLoopE.SetECertF3bPart0
public import QED.ThreeLoopE.SetECertF3bPart1
public import QED.ThreeLoopE.SetECertF3bPart2
public import QED.ThreeLoopE.SetECertF3bPart3
public import QED.ThreeLoopE.SetECertF3bPart4
public import QED.ThreeLoopE.SetECertF3bPart5
public import QED.ThreeLoopE.SetECertF3bPart6
public import QED.ThreeLoopE.SetECertF3bPart7

/-!
# The `f3b` reduction of set (e)

The label-split certificate of `QED.Algebra.IBPCertSector` reduces the projected combination `Y - (d
- 1)² T₁` of the set (e) vertex diagrams of self-energy topology `f3b`
(`QED.ThreeLoopE.SetECert.f3bTarget`, integrals in scaleless sectors dropped) to the Kira masters
`QED.ThreeLoopE.SetECert.f3bMasters` of the family `QED.ThreeLoopE.SetECert.f3b`, with the IBP
relations, the scaleless sectors and the relabelling symmetries `I(permLabel σ ν) = I(ν)` of the
entries of `QED.ThreeLoopE.SetECert.f3bSyms`. The checker reduces to a master list `f3bMs` that
holds the masters and the terms of the symmetry entries (`f3bMs_comb`).

## Main statements

* `QED.ThreeLoopE.SetECert.f3b_reduction_of_den`: at every `d` with `q(d) ≠ 0`, for every family of
  values satisfying the hypotheses at `d`, the target combination equals the certified combination
  of the masters.
* `QED.ThreeLoopE.SetECert.f3b_reduction`: the same off a finite set of `d`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Sector

theorem f3bMT_ok : mtOk f3b f3bCtx 122 22 = true := by decide +kernel

theorem f3bFac_ok : facOk f3bCtx f3bFac f3bQE f3bNF = true := by decide +kernel

theorem f3bZS_eq :
    f3bZS = f3b.zeroSectors.map fun S => S.map fun a => (a, f3bCtx.B ^ a) := by
  decide +kernel

theorem f3bBlocks_ok :
    f3bBlocks.all (GBlock.ok f3bCtx 3 4 9 8 f3bQE f3bYb f3bNF f3bZS) = true := by
  simp only [f3bBlocks, rApp_eq, List.all_append, f3bB0_ok, f3bB1_ok, f3bB2_ok, f3bB3_ok, f3bB4_ok,
    f3bB5_ok, f3bB6_ok, f3bB7_ok, Bool.and_self]

theorem f3bClaim_range :
    (f3bTarget ++ f3bMs).all (fun t => inRange 9 3 9 t.1) = true := by
  decide +kernel

theorem f3bBound :
    (f3bBlocks.map fun b => b.seeds.length).sum * (22 * (f3bYb * 122)) +
      Poly.norm1 f3bDen * (f3bTarget.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum +
      (f3bMs.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum < f3bCtx.x0 := by
  decide +kernel

theorem f3bTargetL_lt : f3bTargetL.length < 8 := by decide +kernel

theorem f3bMsL_lt : f3bMsL.length < 8 := by decide +kernel

theorem f3bDen_ne_zero : Poly.isZero f3bDen = false := by decide +kernel

/-- The master list of the checker is the Kira masters plus the symmetry terms. -/
theorem f3bMs_comb :
    LinComb.ofTerms (f3bMs ++ LinComb.smul [-1] (f3bMasters ++ symTerms f3bSyms)) =
      [] := by
  decide +kernel

theorem f3b_parts : ∀ p < 8,
    partOk f3bCtx f3bDen (rGetL (chunks f3bTargetL f3bTarget) p)
      (rGetL (chunks f3bMsL f3bMs) p) f3bBlocks p = true := fun p hp =>
  match p, hp with
  | 0, _ => f3bPart0
  | 1, _ => f3bPart1
  | 2, _ => f3bPart2
  | 3, _ => f3bPart3
  | 4, _ => f3bPart4
  | 5, _ => f3bPart5
  | 6, _ => f3bPart6
  | 7, _ => f3bPart7
  | _ + 8, h => absurd h (by omega)

/-- The `f3b` reduction at every dimension `d` where the common denominator `q(d)` is nonzero: for
every family of values `I` satisfying the IBP relations, the scaleless sectors and the relabelling
symmetries of `f3bSyms` of `f3b` at `d`, the target combination `Σ tₗ(d) I(l)` equals `Σ (nⱼ(d) /
q(d)) I(Mⱼ)` over the Kira masters. -/
theorem f3b_reduction_of_den {K : Type*} [Field K] [CharZero K] (d : K)
    (hd : Poly.eval d f3bDen ≠ 0) (I : (Fin f3b.nProp → ℤ) → K → K)
    (hI : f3b.IBPHolds I d) (hz : f3b.ZeroSectors I d)
    (hs : ∀ e ∈ f3bSyms, f3b.SymHoldsAt I d e.1 e.2.1) :
    (f3bTarget.map fun t => Poly.eval d t.2 * I (toVec f3b.nProp t.1) d).sum =
      (f3bMasters.map fun m =>
        Poly.eval d m.2 / Poly.eval d f3bDen * I (toVec f3b.nProp m.1) d).sum := by
  have h := gcert_reduction (P := 8) (den := f3bDen) (T := f3bTarget) (Ms := f3bMs)
    (tl := f3bTargetL) (ml := f3bMsL) f3bMT_ok f3bFac_ok f3bZS_eq f3bBlocks_ok f3bClaim_range
    f3bTargetL_lt f3bMsL_lt f3bBound f3b_parts I d hI hz hd
  rw [h]
  exact masters_of_comb f3b I d f3bDen f3bMs f3bMasters f3bSyms f3bMs_comb hs

/-- **The `f3b` reduction.** Off a finite set of dimensions `d`, `q(d) ≠ 0` and, for every family of
values `I` satisfying the IBP relations, the scaleless sectors and the relabelling symmetries of
`f3bSyms` of `f3b` at `d`, the target combination equals the certified combination of the Kira
masters. -/
theorem f3b_reduction {K : Type*} [Field K] [CharZero K] :
    ∃ s : Finset K, ∀ d ∉ s, Poly.eval d f3bDen ≠ 0 ∧
      ∀ I : (Fin f3b.nProp → ℤ) → K → K, f3b.IBPHolds I d → f3b.ZeroSectors I d →
      (∀ e ∈ f3bSyms, f3b.SymHoldsAt I d e.1 e.2.1) →
        (f3bTarget.map fun t => Poly.eval d t.2 * I (toVec f3b.nProp t.1) d).sum =
          (f3bMasters.map fun m =>
            Poly.eval d m.2 / Poly.eval d f3bDen * I (toVec f3b.nProp m.1) d).sum := by
  obtain ⟨s, hs⟩ := Poly.exists_finset_eval_ne_zero (K := K) f3bDen_ne_zero
  exact ⟨s, fun d hd => ⟨hs d hd, fun I hI hz hsym =>
    f3b_reduction_of_den d (hs d hd) I hI hz hsym⟩⟩

end QED.ThreeLoopE.SetECert
