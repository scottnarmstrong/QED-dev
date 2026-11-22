/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3dFamily
public import QED.Algebra.IBPCertSectorSound
public import QED.ThreeLoopE.SetECertSymTerms
public import QED.ThreeLoopE.SetECertF3dData59
public import QED.ThreeLoopE.SetECertF3dPart0
public import QED.ThreeLoopE.SetECertF3dPart1
public import QED.ThreeLoopE.SetECertF3dPart2
public import QED.ThreeLoopE.SetECertF3dPart3
public import QED.ThreeLoopE.SetECertF3dPart4
public import QED.ThreeLoopE.SetECertF3dPart5
public import QED.ThreeLoopE.SetECertF3dPart6
public import QED.ThreeLoopE.SetECertF3dPart7
public import QED.ThreeLoopE.SetECertF3dPart8
public import QED.ThreeLoopE.SetECertF3dPart9
public import QED.ThreeLoopE.SetECertF3dPart10
public import QED.ThreeLoopE.SetECertF3dPart11
public import QED.ThreeLoopE.SetECertF3dPart12
public import QED.ThreeLoopE.SetECertF3dPart13
public import QED.ThreeLoopE.SetECertF3dPart14
public import QED.ThreeLoopE.SetECertF3dPart15
public import QED.ThreeLoopE.SetECertF3dPart16
public import QED.ThreeLoopE.SetECertF3dPart17
public import QED.ThreeLoopE.SetECertF3dPart18
public import QED.ThreeLoopE.SetECertF3dPart19
public import QED.ThreeLoopE.SetECertF3dPart20
public import QED.ThreeLoopE.SetECertF3dPart21
public import QED.ThreeLoopE.SetECertF3dPart22
public import QED.ThreeLoopE.SetECertF3dPart23
public import QED.ThreeLoopE.SetECertF3dPart24
public import QED.ThreeLoopE.SetECertF3dPart25
public import QED.ThreeLoopE.SetECertF3dPart26
public import QED.ThreeLoopE.SetECertF3dPart27
public import QED.ThreeLoopE.SetECertF3dPart28
public import QED.ThreeLoopE.SetECertF3dPart29
public import QED.ThreeLoopE.SetECertF3dPart30
public import QED.ThreeLoopE.SetECertF3dPart31

/-!
# The `f3d` reduction of set (e)

The label-split certificate of `QED.Algebra.IBPCertSector` reduces the projected combination `Y - (d
- 1)² T₁` of the set (e) vertex diagrams of self-energy topology `f3d`
(`QED.ThreeLoopE.SetECert.f3dTarget`, integrals in scaleless sectors dropped) to the Kira masters
`QED.ThreeLoopE.SetECert.f3dMasters` of the family `QED.ThreeLoopE.SetECert.f3d`, with the IBP
relations, the scaleless sectors and the relabelling symmetries `I(permLabel σ ν) = I(ν)` of the
entries of `QED.ThreeLoopE.SetECert.f3dSyms`. The checker reduces to a master list `f3dMs` that
holds the masters and the terms of the symmetry entries (`f3dMs_comb`).

## Main statements

* `QED.ThreeLoopE.SetECert.f3d_reduction_of_den`: at every `d` with `q(d) ≠ 0`, for every family of
  values satisfying the hypotheses at `d`, the target combination equals the certified combination
  of the masters.
* `QED.ThreeLoopE.SetECert.f3d_reduction`: the same off a finite set of `d`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Sector

theorem f3dMT_ok : mtOk f3d f3dCtx 132 25 = true := by decide +kernel

theorem f3dFac_ok : facOk f3dCtx f3dFac f3dQE f3dNF = true := by decide +kernel

theorem f3dZS_eq :
    f3dZS = f3d.zeroSectors.map fun S => S.map fun a => (a, f3dCtx.B ^ a) := by
  decide +kernel

theorem f3dBlocks_ok :
    f3dBlocks.all (GBlock.ok f3dCtx 3 4 9 32 f3dQE f3dYb f3dNF f3dZS) = true := by
  simp only [f3dBlocks, rApp_eq, List.all_append, f3dB0_ok, f3dB1_ok, f3dB2_ok, f3dB3_ok, f3dB4_ok,
    f3dB5_ok, f3dB6_ok, f3dB7_ok, f3dB8_ok, f3dB9_ok, f3dB10_ok, f3dB11_ok, f3dB12_ok, f3dB13_ok,
    f3dB14_ok, f3dB15_ok, f3dB16_ok, f3dB17_ok, f3dB18_ok, f3dB19_ok, f3dB20_ok, f3dB21_ok,
    f3dB22_ok, f3dB23_ok, f3dB24_ok, f3dB25_ok, f3dB26_ok, f3dB27_ok, f3dB28_ok, f3dB29_ok,
    f3dB30_ok, f3dB31_ok, f3dB32_ok, f3dB33_ok, f3dB34_ok, f3dB35_ok, f3dB36_ok, f3dB37_ok,
    f3dB38_ok, f3dB39_ok, f3dB40_ok, f3dB41_ok, f3dB42_ok, f3dB43_ok, f3dB44_ok, f3dB45_ok,
    f3dB46_ok, f3dB47_ok, f3dB48_ok, f3dB49_ok, f3dB50_ok, f3dB51_ok, f3dB52_ok, f3dB53_ok,
    f3dB54_ok, Bool.and_self]

theorem f3dClaim_range :
    (f3dTarget ++ f3dMs).all (fun t => inRange 8 3 9 t.1) = true := by
  decide +kernel

theorem f3dBound :
    (f3dBlocks.map fun b => b.seeds.length).sum * (25 * (f3dYb * 132)) +
      Poly.norm1 f3dDen * (f3dTarget.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum +
      (f3dMs.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum < f3dCtx.x0 := by
  decide +kernel

theorem f3dTargetL_lt : f3dTargetL.length < 32 := by decide +kernel

theorem f3dMsL_lt : f3dMsL.length < 32 := by decide +kernel

theorem f3dDen_ne_zero : Poly.isZero f3dDen = false := by decide +kernel

/-- The master list of the checker is the Kira masters plus the symmetry terms. -/
theorem f3dMs_comb :
    LinComb.ofTerms (f3dMs ++ LinComb.smul [-1] (f3dMasters ++ symTerms f3dSyms)) =
      [] := by
  decide +kernel

theorem f3d_parts : ∀ p < 32,
    partOk f3dCtx f3dDen (rGetL (chunks f3dTargetL f3dTarget) p)
      (rGetL (chunks f3dMsL f3dMs) p) f3dBlocks p = true := fun p hp =>
  match p, hp with
  | 0, _ => f3dPart0
  | 1, _ => f3dPart1
  | 2, _ => f3dPart2
  | 3, _ => f3dPart3
  | 4, _ => f3dPart4
  | 5, _ => f3dPart5
  | 6, _ => f3dPart6
  | 7, _ => f3dPart7
  | 8, _ => f3dPart8
  | 9, _ => f3dPart9
  | 10, _ => f3dPart10
  | 11, _ => f3dPart11
  | 12, _ => f3dPart12
  | 13, _ => f3dPart13
  | 14, _ => f3dPart14
  | 15, _ => f3dPart15
  | 16, _ => f3dPart16
  | 17, _ => f3dPart17
  | 18, _ => f3dPart18
  | 19, _ => f3dPart19
  | 20, _ => f3dPart20
  | 21, _ => f3dPart21
  | 22, _ => f3dPart22
  | 23, _ => f3dPart23
  | 24, _ => f3dPart24
  | 25, _ => f3dPart25
  | 26, _ => f3dPart26
  | 27, _ => f3dPart27
  | 28, _ => f3dPart28
  | 29, _ => f3dPart29
  | 30, _ => f3dPart30
  | 31, _ => f3dPart31
  | _ + 32, h => absurd h (by omega)

/-- The `f3d` reduction at every dimension `d` where the common denominator `q(d)` is nonzero: for
every family of values `I` satisfying the IBP relations, the scaleless sectors and the relabelling
symmetries of `f3dSyms` of `f3d` at `d`, the target combination `Σ tₗ(d) I(l)` equals `Σ (nⱼ(d) /
q(d)) I(Mⱼ)` over the Kira masters. -/
theorem f3d_reduction_of_den {K : Type*} [Field K] [CharZero K] (d : K)
    (hd : Poly.eval d f3dDen ≠ 0) (I : (Fin f3d.nProp → ℤ) → K → K)
    (hI : f3d.IBPHolds I d) (hz : f3d.ZeroSectors I d)
    (hs : ∀ e ∈ f3dSyms, f3d.SymHoldsAt I d e.1 e.2.1) :
    (f3dTarget.map fun t => Poly.eval d t.2 * I (toVec f3d.nProp t.1) d).sum =
      (f3dMasters.map fun m =>
        Poly.eval d m.2 / Poly.eval d f3dDen * I (toVec f3d.nProp m.1) d).sum := by
  have h := gcert_reduction (P := 32) (den := f3dDen) (T := f3dTarget) (Ms := f3dMs)
    (tl := f3dTargetL) (ml := f3dMsL) f3dMT_ok f3dFac_ok f3dZS_eq f3dBlocks_ok f3dClaim_range
    f3dTargetL_lt f3dMsL_lt f3dBound f3d_parts I d hI hz hd
  rw [h]
  exact masters_of_comb f3d I d f3dDen f3dMs f3dMasters f3dSyms f3dMs_comb hs

/-- **The `f3d` reduction.** Off a finite set of dimensions `d`, `q(d) ≠ 0` and, for every family of
values `I` satisfying the IBP relations, the scaleless sectors and the relabelling symmetries of
`f3dSyms` of `f3d` at `d`, the target combination equals the certified combination of the Kira
masters. -/
theorem f3d_reduction {K : Type*} [Field K] [CharZero K] :
    ∃ s : Finset K, ∀ d ∉ s, Poly.eval d f3dDen ≠ 0 ∧
      ∀ I : (Fin f3d.nProp → ℤ) → K → K, f3d.IBPHolds I d → f3d.ZeroSectors I d →
      (∀ e ∈ f3dSyms, f3d.SymHoldsAt I d e.1 e.2.1) →
        (f3dTarget.map fun t => Poly.eval d t.2 * I (toVec f3d.nProp t.1) d).sum =
          (f3dMasters.map fun m =>
            Poly.eval d m.2 / Poly.eval d f3dDen * I (toVec f3d.nProp m.1) d).sum := by
  obtain ⟨s, hs⟩ := Poly.exists_finset_eval_ne_zero (K := K) f3dDen_ne_zero
  exact ⟨s, fun d hd => ⟨hs d hd, fun I hI hz hsym =>
    f3d_reduction_of_den d (hs d hd) I hI hz hsym⟩⟩

end QED.ThreeLoopE.SetECert
