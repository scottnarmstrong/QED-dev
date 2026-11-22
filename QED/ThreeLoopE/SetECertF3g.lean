/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3gFamily
public import QED.Algebra.IBPCertSectorSound
public import QED.ThreeLoopE.SetECertSymTerms
public import QED.ThreeLoopE.SetECertF3gData6
public import QED.ThreeLoopE.SetECertF3gPart0
public import QED.ThreeLoopE.SetECertF3gPart1
public import QED.ThreeLoopE.SetECertF3gPart2
public import QED.ThreeLoopE.SetECertF3gPart3
public import QED.ThreeLoopE.SetECertF3gPart4
public import QED.ThreeLoopE.SetECertF3gPart5
public import QED.ThreeLoopE.SetECertF3gPart6
public import QED.ThreeLoopE.SetECertF3gPart7

/-!
# The `f3g` reduction of set (e)

The label-split certificate of `QED.Algebra.IBPCertSector` reduces the projected combination `Y - (d
- 1)² T₁` of the set (e) vertex diagrams of self-energy topology `f3g`
(`QED.ThreeLoopE.SetECert.f3gTarget`, integrals in scaleless sectors dropped) to the Kira masters
`QED.ThreeLoopE.SetECert.f3gMasters` of the family `QED.ThreeLoopE.SetECert.f3g`, with the IBP
relations, the scaleless sectors and the relabelling symmetries `I(permLabel σ ν) = I(ν)` of the
entries of `QED.ThreeLoopE.SetECert.f3gSyms`. The checker reduces to a master list `f3gMs` that
holds the masters and the terms of the symmetry entries (`f3gMs_comb`). Further hypotheses: the
numerator-symmetry relations `r` of `QED.ThreeLoopE.SetECert.f3gRels` (`Σ c [l] = 0`, integer
coefficients, scaleless-sector terms dropped). Each comes from a change of loop momenta `k ↦ A k + b
p`, `p ↦ s p` mapping the denominators of the integral `ν` to denominators and its numerators to
linear combinations of denominators (checked offline as a pointwise identity of integrands,
`symn.py`); they enter with multipliers `ζ`.

## Main statements

* `QED.ThreeLoopE.SetECert.f3g_reduction_of_den`: at every `d` with `q(d) ≠ 0`, for every family of
  values satisfying the hypotheses at `d`, the target combination equals the certified combination
  of the masters.
* `QED.ThreeLoopE.SetECert.f3g_reduction`: the same off a finite set of `d`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Sector

theorem f3gMT_ok : mtOk f3g f3gCtx 122 30 = true := by decide +kernel

theorem f3gFac_ok : facOk f3gCtx f3gFac f3gQE f3gNF = true := by decide +kernel

theorem f3gZS_eq :
    f3gZS = f3g.zeroSectors.map fun S => S.map fun a => (a, f3gCtx.B ^ a) := by
  decide +kernel

theorem f3gBlocks_ok :
    f3gBlocks.all (GBlock.ok f3gCtx 3 4 9 8 f3gQE f3gYb f3gNF f3gZS) = true := by
  simp only [f3gBlocks, rApp_eq, List.all_append, f3gB0_ok, f3gB1_ok, f3gB2_ok, f3gB3_ok, f3gB4_ok,
    Bool.and_self]

theorem f3gClaim_range :
    (f3gTarget ++ f3gMs).all (fun t => inRange 9 3 9 t.1) = true := by
  decide +kernel

theorem f3gBound :
    (f3gBlocks.map fun b => b.seeds.length).sum * (30 * (f3gYb * 122)) +
      Poly.norm1 f3gDen * (f3gTarget.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum +
      (f3gMs.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum < f3gCtx.x0 := by
  decide +kernel

theorem f3gTargetL_lt : f3gTargetL.length < 8 := by decide +kernel

theorem f3gMsL_lt : f3gMsL.length < 8 := by decide +kernel

theorem f3gDen_ne_zero : Poly.isZero f3gDen = false := by decide +kernel

/-- The master list of the checker is the Kira masters plus the symmetry terms. -/
theorem f3gMs_comb :
    LinComb.ofTerms (f3gMs ++ LinComb.smul [-1] (f3gMasters ++ symTerms f3gSyms ++
      relTerms f3gRels)) =
      [] := by
  decide +kernel

theorem f3g_parts : ∀ p < 8,
    partOk f3gCtx f3gDen (rGetL (chunks f3gTargetL f3gTarget) p)
      (rGetL (chunks f3gMsL f3gMs) p) f3gBlocks p = true := fun p hp =>
  match p, hp with
  | 0, _ => f3gPart0
  | 1, _ => f3gPart1
  | 2, _ => f3gPart2
  | 3, _ => f3gPart3
  | 4, _ => f3gPart4
  | 5, _ => f3gPart5
  | 6, _ => f3gPart6
  | 7, _ => f3gPart7
  | _ + 8, h => absurd h (by omega)

/-- The `f3g` reduction at every dimension `d` where the common denominator `q(d)` is nonzero: for
every family of values `I` satisfying the IBP relations, the scaleless sectors and the relabelling
symmetries of `f3gSyms` of `f3g` at `d`, the target combination `Σ tₗ(d) I(l)` equals `Σ (nⱼ(d) /
q(d)) I(Mⱼ)` over the Kira masters. -/
theorem f3g_reduction_of_den {K : Type*} [Field K] [CharZero K] (d : K)
    (hd : Poly.eval d f3gDen ≠ 0) (I : (Fin f3g.nProp → ℤ) → K → K)
    (hI : f3g.IBPHolds I d) (hz : f3g.ZeroSectors I d)
    (hs : ∀ e ∈ f3gSyms, f3g.SymHoldsAt I d e.1 e.2.1)
    (hn : ∀ e ∈ f3gRels,
      LinComb.eval (fun l => I (toVec f3g.nProp l) d) d e.1 = 0) :
    (f3gTarget.map fun t => Poly.eval d t.2 * I (toVec f3g.nProp t.1) d).sum =
      (f3gMasters.map fun m =>
        Poly.eval d m.2 / Poly.eval d f3gDen * I (toVec f3g.nProp m.1) d).sum := by
  have h := gcert_reduction (P := 8) (den := f3gDen) (T := f3gTarget) (Ms := f3gMs)
    (tl := f3gTargetL) (ml := f3gMsL) f3gMT_ok f3gFac_ok f3gZS_eq f3gBlocks_ok f3gClaim_range
    f3gTargetL_lt f3gMsL_lt f3gBound f3g_parts I d hI hz hd
  rw [h]
  exact masters_of_comb_rel f3g I d f3gDen f3gMs f3gMasters f3gSyms f3gRels f3gMs_comb hs hn

/-- **The `f3g` reduction.** Off a finite set of dimensions `d`, `q(d) ≠ 0` and, for every family of
values `I` satisfying the IBP relations, the scaleless sectors and the relabelling symmetries of
`f3gSyms` of `f3g` at `d`, the target combination equals the certified combination of the Kira
masters. -/
theorem f3g_reduction {K : Type*} [Field K] [CharZero K] :
    ∃ s : Finset K, ∀ d ∉ s, Poly.eval d f3gDen ≠ 0 ∧
      ∀ I : (Fin f3g.nProp → ℤ) → K → K, f3g.IBPHolds I d → f3g.ZeroSectors I d →
      (∀ e ∈ f3gSyms, f3g.SymHoldsAt I d e.1 e.2.1) →
      (∀ e ∈ f3gRels,
        LinComb.eval (fun l => I (toVec f3g.nProp l) d) d e.1 = 0) →
        (f3gTarget.map fun t => Poly.eval d t.2 * I (toVec f3g.nProp t.1) d).sum =
          (f3gMasters.map fun m =>
            Poly.eval d m.2 / Poly.eval d f3gDen * I (toVec f3g.nProp m.1) d).sum := by
  obtain ⟨s, hs⟩ := Poly.exists_finset_eval_ne_zero (K := K) f3gDen_ne_zero
  exact ⟨s, fun d hd => ⟨hs d hd, fun I hI hz hsym hrel =>
    f3g_reduction_of_den d (hs d hd) I hI hz hsym hrel⟩⟩

end QED.ThreeLoopE.SetECert
