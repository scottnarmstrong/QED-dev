/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3cFamily
public import QED.ThreeLoopE.SetEBridgeI1All
public import QED.ThreeLoopE.SetEBridgeI1Part0
public import QED.ThreeLoopE.SetEBridgeI1Part8
public import QED.ThreeLoopE.SetEBridgeI1Part16
public import QED.ThreeLoopE.SetEBridgeI1Part24

/-!
# The `f3c` reduction of the numerator integral `2 I₁`

The label-split certificate of `QED.Algebra.IBPCertSector` reduces the numerator integral `2 I₁`
(`QED.ThreeLoopE.SetECert.f3cI1Target`) in the family `QED.ThreeLoopE.SetECert.f3c` to the IBP
masters `QED.ThreeLoopE.SetECert.f3cI1Masters` (the masters of the `f3c` reduction,
`QED.ThreeLoopE.SetECert.f3cMasters`).

## Main statements

* `QED.ThreeLoopE.SetECert.f3cI1_reduction_of_den`: at every `d` with `q(d) ≠ 0`, for every
  family of values satisfying all IBP relations and the scaleless sectors of `f3c` at `d`, the
  target combination equals the certified combination of the masters.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Sector

theorem f3cI1MT_ok : mtOk f3c f3cI1Ctx 142 37 = true := by decide +kernel

theorem f3cI1Fac_ok : facOk f3cI1Ctx f3cI1Fac f3cI1QE f3cI1NF = true := by decide +kernel

theorem f3cI1ZS_eq :
    f3cI1ZS = f3c.zeroSectors.map fun S => S.map fun a => (a, f3cI1Ctx.B ^ a) := by
  decide +kernel

theorem f3cI1_parts : ∀ p < 32, partOk f3cI1Ctx f3cI1Den
    (rGetL (chunks f3cI1TargetL f3cI1Target) p)
    (rGetL (chunks f3cI1MastersL f3cI1Masters) p) f3cI1Blocks p = true := fun p hp =>
  match p, hp with
  | 0, _ => f3cI1Part0
  | 1, _ => f3cI1Part1
  | 2, _ => f3cI1Part2
  | 3, _ => f3cI1Part3
  | 4, _ => f3cI1Part4
  | 5, _ => f3cI1Part5
  | 6, _ => f3cI1Part6
  | 7, _ => f3cI1Part7
  | 8, _ => f3cI1Part8
  | 9, _ => f3cI1Part9
  | 10, _ => f3cI1Part10
  | 11, _ => f3cI1Part11
  | 12, _ => f3cI1Part12
  | 13, _ => f3cI1Part13
  | 14, _ => f3cI1Part14
  | 15, _ => f3cI1Part15
  | 16, _ => f3cI1Part16
  | 17, _ => f3cI1Part17
  | 18, _ => f3cI1Part18
  | 19, _ => f3cI1Part19
  | 20, _ => f3cI1Part20
  | 21, _ => f3cI1Part21
  | 22, _ => f3cI1Part22
  | 23, _ => f3cI1Part23
  | 24, _ => f3cI1Part24
  | 25, _ => f3cI1Part25
  | 26, _ => f3cI1Part26
  | 27, _ => f3cI1Part27
  | 28, _ => f3cI1Part28
  | 29, _ => f3cI1Part29
  | 30, _ => f3cI1Part30
  | 31, _ => f3cI1Part31
  | _ + 32, h => absurd h (by omega)

theorem f3cI1Blocks_ok :
    f3cI1Blocks.all (GBlock.ok f3cI1Ctx 3 4 9 32 f3cI1QE f3cI1Yb f3cI1NF f3cI1ZS) = true :=
  by
    simp only [f3cI1Blocks, rApp_eq, List.all_append, f3cI1B0_ok, f3cI1B1_ok, f3cI1B2_ok,
    f3cI1B3_ok, f3cI1B4_ok, f3cI1B5_ok, f3cI1B6_ok, f3cI1B7_ok, f3cI1B8_ok, f3cI1B9_ok, f3cI1B10_ok,
    Bool.and_self]

theorem f3cI1Claim_range :
    (f3cI1Target ++ f3cI1Masters).all (fun t => inRange 10 4 9 t.1) = true := by
  decide +kernel

theorem f3cI1Bound : (f3cI1Blocks.map fun b => b.seeds.length).sum * (37 * (f3cI1Yb * 142)) +
    Poly.norm1 f3cI1Den * (f3cI1Target.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum +
      (f3cI1Masters.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum < f3cI1Ctx.x0 := by
  decide +kernel

theorem f3cI1TargetL_lt : f3cI1TargetL.length < 32 := by decide +kernel

theorem f3cI1MastersL_lt : f3cI1MastersL.length < 32 := by decide +kernel

theorem f3cI1Den_ne_zero : Poly.isZero f3cI1Den = false := by decide +kernel

/-- **The reduction of the numerator integral `2 I₁`.** At every dimension `d` where the common
denominator `q(d)` is nonzero, for every family of values `I` satisfying the IBP relations and
the scaleless sectors of `f3c` at `d`. -/
theorem f3cI1_reduction_of_den {K : Type*} [Field K] [CharZero K] (d : K)
    (hd : Poly.eval d f3cI1Den ≠ 0) (I : (Fin f3c.nProp → ℤ) → K → K)
    (hI : f3c.IBPHolds I d) (hz : f3c.ZeroSectors I d) :
    (f3cI1Target.map fun t => Poly.eval d t.2 * I (toVec f3c.nProp t.1) d).sum =
      (f3cI1Masters.map fun m =>
        Poly.eval d m.2 / Poly.eval d f3cI1Den * I (toVec f3c.nProp m.1) d).sum :=
  gcert_reduction (P := 32) (den := f3cI1Den) (T := f3cI1Target) (Ms := f3cI1Masters)
    (tl := f3cI1TargetL) (ml := f3cI1MastersL) f3cI1MT_ok f3cI1Fac_ok
    f3cI1ZS_eq f3cI1Blocks_ok f3cI1Claim_range f3cI1TargetL_lt f3cI1MastersL_lt
    f3cI1Bound f3cI1_parts I d hI hz hd

end QED.ThreeLoopE.SetECert
