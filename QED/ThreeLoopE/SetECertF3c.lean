/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3cFamily
public import QED.ThreeLoopE.SetECertF3cAll
public import QED.ThreeLoopE.SetECertF3cPart0
public import QED.ThreeLoopE.SetECertF3cPart1
public import QED.ThreeLoopE.SetECertF3cPart2
public import QED.ThreeLoopE.SetECertF3cPart3
public import QED.ThreeLoopE.SetECertF3cPart4
public import QED.ThreeLoopE.SetECertF3cPart5
public import QED.ThreeLoopE.SetECertF3cPart6
public import QED.ThreeLoopE.SetECertF3cPart7
public import QED.ThreeLoopE.SetECertF3cPart8
public import QED.ThreeLoopE.SetECertF3cPart9
public import QED.ThreeLoopE.SetECertF3cPart10
public import QED.ThreeLoopE.SetECertF3cPart11
public import QED.ThreeLoopE.SetECertF3cPart12
public import QED.ThreeLoopE.SetECertF3cPart13
public import QED.ThreeLoopE.SetECertF3cPart14
public import QED.ThreeLoopE.SetECertF3cPart15
public import QED.ThreeLoopE.SetECertF3cPart16
public import QED.ThreeLoopE.SetECertF3cPart17
public import QED.ThreeLoopE.SetECertF3cPart18
public import QED.ThreeLoopE.SetECertF3cPart19
public import QED.ThreeLoopE.SetECertF3cPart20
public import QED.ThreeLoopE.SetECertF3cPart21
public import QED.ThreeLoopE.SetECertF3cPart22
public import QED.ThreeLoopE.SetECertF3cPart23
public import QED.ThreeLoopE.SetECertF3cPart24
public import QED.ThreeLoopE.SetECertF3cPart25
public import QED.ThreeLoopE.SetECertF3cPart26
public import QED.ThreeLoopE.SetECertF3cPart27
public import QED.ThreeLoopE.SetECertF3cPart28
public import QED.ThreeLoopE.SetECertF3cPart29
public import QED.ThreeLoopE.SetECertF3cPart30
public import QED.ThreeLoopE.SetECertF3cPart31

/-!
# The `f3c` reduction of set (e)

The label-split certificate of `QED.Algebra.IBPCertSector` reduces the projected combination
`Y - (d - 1)² T₁` of the set (e) vertex diagrams of self-energy topology `f3c` (the triple
cross, `QED.ThreeLoopE.SetECert.f3cTarget`) to the IBP masters
`QED.ThreeLoopE.SetECert.f3cMasters` (the integrals left by the elimination without symmetry
relations, one or more per sector copy).

## Main statements

* `QED.ThreeLoopE.SetECert.f3c_reduction`: off a finite set of `d`, for every family of values
  satisfying all IBP relations and the scaleless sectors of `f3c` at `d`, the target combination
  equals the certified combination of the masters.
* `QED.ThreeLoopE.SetECert.f3c_reduction_of_den`: the same at every `d` with `q(d) ≠ 0`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Sector

theorem f3c_parts : ∀ p < 32, partOk f3cCtx f3cDen (rGetL (chunks f3cTargetL f3cTarget) p)
    (rGetL (chunks f3cMastersL f3cMasters) p) f3cBlocks p = true := fun p hp =>
  match p, hp with
  | 0, _ => f3cPart0
  | 1, _ => f3cPart1
  | 2, _ => f3cPart2
  | 3, _ => f3cPart3
  | 4, _ => f3cPart4
  | 5, _ => f3cPart5
  | 6, _ => f3cPart6
  | 7, _ => f3cPart7
  | 8, _ => f3cPart8
  | 9, _ => f3cPart9
  | 10, _ => f3cPart10
  | 11, _ => f3cPart11
  | 12, _ => f3cPart12
  | 13, _ => f3cPart13
  | 14, _ => f3cPart14
  | 15, _ => f3cPart15
  | 16, _ => f3cPart16
  | 17, _ => f3cPart17
  | 18, _ => f3cPart18
  | 19, _ => f3cPart19
  | 20, _ => f3cPart20
  | 21, _ => f3cPart21
  | 22, _ => f3cPart22
  | 23, _ => f3cPart23
  | 24, _ => f3cPart24
  | 25, _ => f3cPart25
  | 26, _ => f3cPart26
  | 27, _ => f3cPart27
  | 28, _ => f3cPart28
  | 29, _ => f3cPart29
  | 30, _ => f3cPart30
  | 31, _ => f3cPart31
  | _ + 32, h => absurd h (by omega)

theorem f3cBlocks_ok :
    f3cBlocks.all (GBlock.ok f3cCtx 3 4 9 32 f3cQE f3cYb f3cNF f3cZS) = true := by
  simp only [f3cBlocks, rApp_eq, List.all_append, f3cB0_ok, f3cB1_ok, f3cB2_ok, f3cB3_ok, f3cB4_ok,
    f3cB5_ok, f3cB6_ok, f3cB7_ok, f3cB8_ok, f3cB9_ok, f3cB10_ok, f3cB11_ok, f3cB12_ok, f3cB13_ok,
    f3cB14_ok, f3cB15_ok, f3cB16_ok, f3cB17_ok, f3cB18_ok, f3cB19_ok, f3cB20_ok, f3cB21_ok,
    f3cB22_ok, f3cB23_ok, f3cB24_ok, f3cB25_ok, f3cB26_ok, f3cB27_ok, f3cB28_ok, f3cB29_ok,
    f3cB30_ok, f3cB31_ok, f3cB32_ok, f3cB33_ok, f3cB34_ok, f3cB35_ok, f3cB36_ok, f3cB37_ok,
    f3cB38_ok, f3cB39_ok, f3cB40_ok, f3cB41_ok, f3cB42_ok, f3cB43_ok, f3cB44_ok, f3cB45_ok,
    f3cB46_ok, f3cB47_ok, f3cB48_ok, f3cB49_ok, f3cB50_ok, f3cB51_ok, f3cB52_ok, f3cB53_ok,
    f3cB54_ok, f3cB55_ok, f3cB56_ok, f3cB57_ok, f3cB58_ok, f3cB59_ok, f3cB60_ok, f3cB61_ok,
    f3cB62_ok, f3cB63_ok, f3cB64_ok, Bool.and_self]

theorem f3cClaim_range :
    (f3cTarget ++ f3cMasters).all (fun t => inRange 10 4 9 t.1) = true := by
  decide +kernel

theorem f3cBound : (f3cBlocks.map fun b => b.seeds.length).sum * (37 * (f3cYb * 142)) +
    Poly.norm1 f3cDen * (f3cTarget.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum +
      (f3cMasters.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum < f3cCtx.x0 := by
  decide +kernel

theorem f3cTargetL_lt : f3cTargetL.length < 32 := by decide +kernel

theorem f3cMastersL_lt : f3cMastersL.length < 32 := by decide +kernel

theorem f3cDen_ne_zero : Poly.isZero f3cDen = false := by decide +kernel

/-- The `f3c` reduction at every dimension `d` where the common denominator `q(d)` is
nonzero. -/
theorem f3c_reduction_of_den {K : Type*} [Field K] [CharZero K] (d : K)
    (hd : Poly.eval d f3cDen ≠ 0) (I : (Fin f3c.nProp → ℤ) → K → K)
    (hI : f3c.IBPHolds I d) (hz : f3c.ZeroSectors I d) :
    (f3cTarget.map fun t => Poly.eval d t.2 * I (toVec f3c.nProp t.1) d).sum =
      (f3cMasters.map fun m =>
        Poly.eval d m.2 / Poly.eval d f3cDen * I (toVec f3c.nProp m.1) d).sum :=
  gcert_reduction (P := 32) (den := f3cDen) (T := f3cTarget) (Ms := f3cMasters)
    (tl := f3cTargetL) (ml := f3cMastersL) f3cMT_ok f3cFac_ok
    f3cZS_eq f3cBlocks_ok f3cClaim_range f3cTargetL_lt f3cMastersL_lt
    f3cBound f3c_parts I d hI hz hd

/-- **The `f3c` reduction.** Off a finite set of dimensions `d`, for every family of values `I`
satisfying the IBP relations and the scaleless sectors of `f3c` at `d`, the projected
combination `Σ tₗ(d) I(l)` of the `f3c` diagrams equals `Σ (nⱼ(d) / q(d)) I(Mⱼ)` over the
masters. -/
theorem f3c_reduction {K : Type*} [Field K] [CharZero K] :
    ∃ s : Finset K, ∀ d ∉ s, Poly.eval d f3cDen ≠ 0 ∧
      ∀ I : (Fin f3c.nProp → ℤ) → K → K, f3c.IBPHolds I d → f3c.ZeroSectors I d →
        (f3cTarget.map fun t => Poly.eval d t.2 * I (toVec f3c.nProp t.1) d).sum =
          (f3cMasters.map fun m =>
            Poly.eval d m.2 / Poly.eval d f3cDen * I (toVec f3c.nProp m.1) d).sum := by
  obtain ⟨s, hs⟩ := Poly.exists_finset_eval_ne_zero (K := K) f3cDen_ne_zero
  exact ⟨s, fun d hd => ⟨hs d hd, fun I hI hz => f3c_reduction_of_den d (hs d hd) I hI hz⟩⟩

end QED.ThreeLoopE.SetECert
