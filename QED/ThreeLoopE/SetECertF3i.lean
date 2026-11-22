/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3iFamily
public import QED.Algebra.IBPCertSectorSound
public import QED.ThreeLoopE.SetECertSymTerms
public import QED.ThreeLoopE.SetECertF3iData23
public import QED.ThreeLoopE.SetECertF3iPart0
public import QED.ThreeLoopE.SetECertF3iPart1
public import QED.ThreeLoopE.SetECertF3iPart2
public import QED.ThreeLoopE.SetECertF3iPart3
public import QED.ThreeLoopE.SetECertF3iPart4
public import QED.ThreeLoopE.SetECertF3iPart5
public import QED.ThreeLoopE.SetECertF3iPart6
public import QED.ThreeLoopE.SetECertF3iPart7
public import QED.ThreeLoopE.SetECertF3iPart8
public import QED.ThreeLoopE.SetECertF3iPart9
public import QED.ThreeLoopE.SetECertF3iPart10
public import QED.ThreeLoopE.SetECertF3iPart11
public import QED.ThreeLoopE.SetECertF3iPart12
public import QED.ThreeLoopE.SetECertF3iPart13
public import QED.ThreeLoopE.SetECertF3iPart14
public import QED.ThreeLoopE.SetECertF3iPart15

/-!
# The `f3i` reduction of set (e)

The label-split certificate of `QED.Algebra.IBPCertSector` reduces the projected combination `Y - (d
- 1)² T₁` of the set (e) vertex diagrams of self-energy topology `f3i`
(`QED.ThreeLoopE.SetECert.f3iTarget`, integrals in scaleless sectors dropped) to the Kira masters
`QED.ThreeLoopE.SetECert.f3iMasters` of the family `QED.ThreeLoopE.SetECert.f3i`, with the IBP
relations, the scaleless sectors and the relabelling symmetries `I(permLabel σ ν) = I(ν)` of the
entries of `QED.ThreeLoopE.SetECert.f3iSyms`. The checker reduces to a master list `f3iMs` that
holds the masters and the terms of the symmetry entries (`f3iMs_comb`).

## Main statements

* `QED.ThreeLoopE.SetECert.f3i_reduction_of_den`: at every `d` with `q(d) ≠ 0`, for every family of
  values satisfying the hypotheses at `d`, the target combination equals the certified combination
  of the masters.
* `QED.ThreeLoopE.SetECert.f3i_reduction`: the same off a finite set of `d`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Sector

theorem f3iMT_ok : mtOk f3i f3iCtx 132 32 = true := by decide +kernel

theorem f3iFac_ok : facOk f3iCtx f3iFac f3iQE f3iNF = true := by decide +kernel

theorem f3iZS_eq :
    f3iZS = f3i.zeroSectors.map fun S => S.map fun a => (a, f3iCtx.B ^ a) := by
  decide +kernel

theorem f3iBlocks_ok :
    f3iBlocks.all (GBlock.ok f3iCtx 3 4 9 16 f3iQE f3iYb f3iNF f3iZS) = true := by
  simp only [f3iBlocks, rApp_eq, List.all_append, f3iB0_ok, f3iB1_ok, f3iB2_ok, f3iB3_ok, f3iB4_ok,
    f3iB5_ok, f3iB6_ok, f3iB7_ok, f3iB8_ok, f3iB9_ok, f3iB10_ok, f3iB11_ok, f3iB12_ok, f3iB13_ok,
    f3iB14_ok, f3iB15_ok, f3iB16_ok, f3iB17_ok, f3iB18_ok, f3iB19_ok, f3iB20_ok, Bool.and_self]

theorem f3iClaim_range :
    (f3iTarget ++ f3iMs).all (fun t => inRange 8 3 9 t.1) = true := by
  decide +kernel

theorem f3iBound :
    (f3iBlocks.map fun b => b.seeds.length).sum * (32 * (f3iYb * 132)) +
      Poly.norm1 f3iDen * (f3iTarget.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum +
      (f3iMs.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum < f3iCtx.x0 := by
  decide +kernel

theorem f3iTargetL_lt : f3iTargetL.length < 16 := by decide +kernel

theorem f3iMsL_lt : f3iMsL.length < 16 := by decide +kernel

theorem f3iDen_ne_zero : Poly.isZero f3iDen = false := by decide +kernel

/-- The master list of the checker is the Kira masters plus the symmetry terms. -/
theorem f3iMs_comb :
    LinComb.ofTerms (f3iMs ++ LinComb.smul [-1] (f3iMasters ++ symTerms f3iSyms)) =
      [] := by
  decide +kernel

theorem f3i_parts : ∀ p < 16,
    partOk f3iCtx f3iDen (rGetL (chunks f3iTargetL f3iTarget) p)
      (rGetL (chunks f3iMsL f3iMs) p) f3iBlocks p = true := fun p hp =>
  match p, hp with
  | 0, _ => f3iPart0
  | 1, _ => f3iPart1
  | 2, _ => f3iPart2
  | 3, _ => f3iPart3
  | 4, _ => f3iPart4
  | 5, _ => f3iPart5
  | 6, _ => f3iPart6
  | 7, _ => f3iPart7
  | 8, _ => f3iPart8
  | 9, _ => f3iPart9
  | 10, _ => f3iPart10
  | 11, _ => f3iPart11
  | 12, _ => f3iPart12
  | 13, _ => f3iPart13
  | 14, _ => f3iPart14
  | 15, _ => f3iPart15
  | _ + 16, h => absurd h (by omega)

/-- The `f3i` reduction at every dimension `d` where the common denominator `q(d)` is nonzero: for
every family of values `I` satisfying the IBP relations, the scaleless sectors and the relabelling
symmetries of `f3iSyms` of `f3i` at `d`, the target combination `Σ tₗ(d) I(l)` equals `Σ (nⱼ(d) /
q(d)) I(Mⱼ)` over the Kira masters. -/
theorem f3i_reduction_of_den {K : Type*} [Field K] [CharZero K] (d : K)
    (hd : Poly.eval d f3iDen ≠ 0) (I : (Fin f3i.nProp → ℤ) → K → K)
    (hI : f3i.IBPHolds I d) (hz : f3i.ZeroSectors I d)
    (hs : ∀ e ∈ f3iSyms, f3i.SymHoldsAt I d e.1 e.2.1) :
    (f3iTarget.map fun t => Poly.eval d t.2 * I (toVec f3i.nProp t.1) d).sum =
      (f3iMasters.map fun m =>
        Poly.eval d m.2 / Poly.eval d f3iDen * I (toVec f3i.nProp m.1) d).sum := by
  have h := gcert_reduction (P := 16) (den := f3iDen) (T := f3iTarget) (Ms := f3iMs)
    (tl := f3iTargetL) (ml := f3iMsL) f3iMT_ok f3iFac_ok f3iZS_eq f3iBlocks_ok f3iClaim_range
    f3iTargetL_lt f3iMsL_lt f3iBound f3i_parts I d hI hz hd
  rw [h]
  exact masters_of_comb f3i I d f3iDen f3iMs f3iMasters f3iSyms f3iMs_comb hs

/-- **The `f3i` reduction.** Off a finite set of dimensions `d`, `q(d) ≠ 0` and, for every family of
values `I` satisfying the IBP relations, the scaleless sectors and the relabelling symmetries of
`f3iSyms` of `f3i` at `d`, the target combination equals the certified combination of the Kira
masters. -/
theorem f3i_reduction {K : Type*} [Field K] [CharZero K] :
    ∃ s : Finset K, ∀ d ∉ s, Poly.eval d f3iDen ≠ 0 ∧
      ∀ I : (Fin f3i.nProp → ℤ) → K → K, f3i.IBPHolds I d → f3i.ZeroSectors I d →
      (∀ e ∈ f3iSyms, f3i.SymHoldsAt I d e.1 e.2.1) →
        (f3iTarget.map fun t => Poly.eval d t.2 * I (toVec f3i.nProp t.1) d).sum =
          (f3iMasters.map fun m =>
            Poly.eval d m.2 / Poly.eval d f3iDen * I (toVec f3i.nProp m.1) d).sum := by
  obtain ⟨s, hs⟩ := Poly.exists_finset_eval_ne_zero (K := K) f3iDen_ne_zero
  exact ⟨s, fun d hd => ⟨hs d hd, fun I hI hz hsym =>
    f3i_reduction_of_den d (hs d hd) I hI hz hsym⟩⟩

end QED.ThreeLoopE.SetECert
