/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3hFamily
public import QED.Algebra.IBPCertSectorSound
public import QED.ThreeLoopE.SetECertSymTerms
public import QED.ThreeLoopE.SetECertF3hData2
public import QED.ThreeLoopE.SetECertF3hPart0
public import QED.ThreeLoopE.SetECertF3hPart1
public import QED.ThreeLoopE.SetECertF3hPart2
public import QED.ThreeLoopE.SetECertF3hPart3

/-!
# The `f3h` reduction of set (e)

The label-split certificate of `QED.Algebra.IBPCertSector` reduces the projected combination `Y - (d
- 1)² T₁` of the set (e) vertex diagrams of self-energy topology `f3h`
(`QED.ThreeLoopE.SetECert.f3hTarget`, integrals in scaleless sectors dropped) to the Kira masters
`QED.ThreeLoopE.SetECert.f3hMasters` of the family `QED.ThreeLoopE.SetECert.f3h`, with the IBP
relations, the scaleless sectors and the relabelling symmetries `I(permLabel σ ν) = I(ν)` of the
entries of `QED.ThreeLoopE.SetECert.f3hSyms`. The checker reduces to a master list `f3hMs` that
holds the masters and the terms of the symmetry entries (`f3hMs_comb`).

## Main statements

* `QED.ThreeLoopE.SetECert.f3h_reduction_of_den`: at every `d` with `q(d) ≠ 0`, for every family of
  values satisfying the hypotheses at `d`, the target combination equals the certified combination
  of the masters.
* `QED.ThreeLoopE.SetECert.f3h_reduction`: the same off a finite set of `d`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Sector

theorem f3hMT_ok : mtOk f3h f3hCtx 144 25 = true := by decide +kernel

theorem f3hFac_ok : facOk f3hCtx f3hFac f3hQE f3hNF = true := by decide +kernel

theorem f3hZS_eq :
    f3hZS = f3h.zeroSectors.map fun S => S.map fun a => (a, f3hCtx.B ^ a) := by
  decide +kernel

theorem f3hBlocks_ok :
    f3hBlocks.all (GBlock.ok f3hCtx 3 4 9 4 f3hQE f3hYb f3hNF f3hZS) = true := by
  simp only [f3hBlocks, rApp_eq, List.all_append, f3hB0_ok, f3hB1_ok, Bool.and_self]

theorem f3hClaim_range :
    (f3hTarget ++ f3hMs).all (fun t => inRange 9 3 9 t.1) = true := by
  decide +kernel

theorem f3hBound :
    (f3hBlocks.map fun b => b.seeds.length).sum * (25 * (f3hYb * 144)) +
      Poly.norm1 f3hDen * (f3hTarget.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum +
      (f3hMs.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum < f3hCtx.x0 := by
  decide +kernel

theorem f3hTargetL_lt : f3hTargetL.length < 4 := by decide +kernel

theorem f3hMsL_lt : f3hMsL.length < 4 := by decide +kernel

theorem f3hDen_ne_zero : Poly.isZero f3hDen = false := by decide +kernel

/-- The master list of the checker is the Kira masters plus the symmetry terms. -/
theorem f3hMs_comb :
    LinComb.ofTerms (f3hMs ++ LinComb.smul [-1] (f3hMasters ++ symTerms f3hSyms)) =
      [] := by
  decide +kernel

theorem f3h_parts : ∀ p < 4,
    partOk f3hCtx f3hDen (rGetL (chunks f3hTargetL f3hTarget) p)
      (rGetL (chunks f3hMsL f3hMs) p) f3hBlocks p = true := fun p hp =>
  match p, hp with
  | 0, _ => f3hPart0
  | 1, _ => f3hPart1
  | 2, _ => f3hPart2
  | 3, _ => f3hPart3
  | _ + 4, h => absurd h (by omega)

/-- The `f3h` reduction at every dimension `d` where the common denominator `q(d)` is nonzero: for
every family of values `I` satisfying the IBP relations, the scaleless sectors and the relabelling
symmetries of `f3hSyms` of `f3h` at `d`, the target combination `Σ tₗ(d) I(l)` equals `Σ (nⱼ(d) /
q(d)) I(Mⱼ)` over the Kira masters. -/
theorem f3h_reduction_of_den {K : Type*} [Field K] [CharZero K] (d : K)
    (hd : Poly.eval d f3hDen ≠ 0) (I : (Fin f3h.nProp → ℤ) → K → K)
    (hI : f3h.IBPHolds I d) (hz : f3h.ZeroSectors I d)
    (hs : ∀ e ∈ f3hSyms, f3h.SymHoldsAt I d e.1 e.2.1) :
    (f3hTarget.map fun t => Poly.eval d t.2 * I (toVec f3h.nProp t.1) d).sum =
      (f3hMasters.map fun m =>
        Poly.eval d m.2 / Poly.eval d f3hDen * I (toVec f3h.nProp m.1) d).sum := by
  have h := gcert_reduction (P := 4) (den := f3hDen) (T := f3hTarget) (Ms := f3hMs)
    (tl := f3hTargetL) (ml := f3hMsL) f3hMT_ok f3hFac_ok f3hZS_eq f3hBlocks_ok f3hClaim_range
    f3hTargetL_lt f3hMsL_lt f3hBound f3h_parts I d hI hz hd
  rw [h]
  exact masters_of_comb f3h I d f3hDen f3hMs f3hMasters f3hSyms f3hMs_comb hs

/-- **The `f3h` reduction.** Off a finite set of dimensions `d`, `q(d) ≠ 0` and, for every family of
values `I` satisfying the IBP relations, the scaleless sectors and the relabelling symmetries of
`f3hSyms` of `f3h` at `d`, the target combination equals the certified combination of the Kira
masters. -/
theorem f3h_reduction {K : Type*} [Field K] [CharZero K] :
    ∃ s : Finset K, ∀ d ∉ s, Poly.eval d f3hDen ≠ 0 ∧
      ∀ I : (Fin f3h.nProp → ℤ) → K → K, f3h.IBPHolds I d → f3h.ZeroSectors I d →
      (∀ e ∈ f3hSyms, f3h.SymHoldsAt I d e.1 e.2.1) →
        (f3hTarget.map fun t => Poly.eval d t.2 * I (toVec f3h.nProp t.1) d).sum =
          (f3hMasters.map fun m =>
            Poly.eval d m.2 / Poly.eval d f3hDen * I (toVec f3h.nProp m.1) d).sum := by
  obtain ⟨s, hs⟩ := Poly.exists_finset_eval_ne_zero (K := K) f3hDen_ne_zero
  exact ⟨s, fun d hd => ⟨hs d hd, fun I hI hz hsym =>
    f3h_reduction_of_den d (hs d hd) I hI hz hsym⟩⟩

end QED.ThreeLoopE.SetECert
