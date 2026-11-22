/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3cFamily
public import QED.ThreeLoopE.SetEBridgeXAll
public import QED.ThreeLoopE.SetEBridgeXPart0

/-!
# The `f3c` reduction of the sector-92 numerators

The label-split certificate of `QED.Algebra.IBPCertSector` reduces the sector-92 numerators
(`QED.ThreeLoopE.SetECert.f3cXTarget`) in the family `QED.ThreeLoopE.SetECert.f3c` to the IBP
masters `QED.ThreeLoopE.SetECert.f3cXMasters` (a subset of the masters of the `f3c` reduction,
`QED.ThreeLoopE.SetECert.f3cMasters`).

## Main statements

* `QED.ThreeLoopE.SetECert.f3cX_reduction_of_den`: at every `d` with `q(d) ≠ 0`, for every
  family of values satisfying all IBP relations and the scaleless sectors of `f3c` at `d`, the
  target combination equals the certified combination of the masters.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Sector

theorem f3cXMT_ok : mtOk f3c f3cXCtx 142 37 = true := by decide +kernel

theorem f3cXFac_ok : facOk f3cXCtx f3cXFac f3cXQE f3cXNF = true := by decide +kernel

theorem f3cXZS_eq :
    f3cXZS = f3c.zeroSectors.map fun S => S.map fun a => (a, f3cXCtx.B ^ a) := by
  decide +kernel

theorem f3cX_parts : ∀ p < 1, partOk f3cXCtx f3cXDen
    (rGetL (chunks f3cXTargetL f3cXTarget) p)
    (rGetL (chunks f3cXMastersL f3cXMasters) p) f3cXBlocks p = true := fun p hp =>
  match p, hp with
  | 0, _ => f3cXPart0
  | _ + 1, h => absurd h (by omega)

theorem f3cXBlocks_ok :
    f3cXBlocks.all (GBlock.ok f3cXCtx 3 4 9 1 f3cXQE f3cXYb f3cXNF f3cXZS) = true :=
  f3cXB0_ok

theorem f3cXClaim_range :
    (f3cXTarget ++ f3cXMasters).all (fun t => inRange 10 4 9 t.1) = true := by
  decide +kernel

theorem f3cXBound : (f3cXBlocks.map fun b => b.seeds.length).sum * (37 * (f3cXYb * 142)) +
    Poly.norm1 f3cXDen * (f3cXTarget.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum +
      (f3cXMasters.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum < f3cXCtx.x0 := by
  decide +kernel

theorem f3cXTargetL_lt : f3cXTargetL.length < 1 := by decide +kernel

theorem f3cXMastersL_lt : f3cXMastersL.length < 1 := by decide +kernel

theorem f3cXDen_ne_zero : Poly.isZero f3cXDen = false := by decide +kernel

/-- **The reduction of the sector-92 numerators.** At every dimension `d` where the common
denominator `q(d)` is nonzero, for every family of values `I` satisfying the IBP relations and
the scaleless sectors of `f3c` at `d`. -/
theorem f3cX_reduction_of_den {K : Type*} [Field K] [CharZero K] (d : K)
    (hd : Poly.eval d f3cXDen ≠ 0) (I : (Fin f3c.nProp → ℤ) → K → K)
    (hI : f3c.IBPHolds I d) (hz : f3c.ZeroSectors I d) :
    (f3cXTarget.map fun t => Poly.eval d t.2 * I (toVec f3c.nProp t.1) d).sum =
      (f3cXMasters.map fun m =>
        Poly.eval d m.2 / Poly.eval d f3cXDen * I (toVec f3c.nProp m.1) d).sum :=
  gcert_reduction (P := 1) (den := f3cXDen) (T := f3cXTarget) (Ms := f3cXMasters)
    (tl := f3cXTargetL) (ml := f3cXMastersL) f3cXMT_ok f3cXFac_ok
    f3cXZS_eq f3cXBlocks_ok f3cXClaim_range f3cXTargetL_lt f3cXMastersL_lt
    f3cXBound f3cX_parts I d hI hz hd

end QED.ThreeLoopE.SetECert
