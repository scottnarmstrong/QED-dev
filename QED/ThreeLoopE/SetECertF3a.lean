/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3aFamily
public import QED.Algebra.IBPCertSectorSound
public import QED.ThreeLoopE.SetECertSymTerms
public import QED.ThreeLoopE.SetECertF3aData26
public import QED.ThreeLoopE.SetECertF3aPart0
public import QED.ThreeLoopE.SetECertF3aPart1
public import QED.ThreeLoopE.SetECertF3aPart2
public import QED.ThreeLoopE.SetECertF3aPart3
public import QED.ThreeLoopE.SetECertF3aPart4
public import QED.ThreeLoopE.SetECertF3aPart5
public import QED.ThreeLoopE.SetECertF3aPart6
public import QED.ThreeLoopE.SetECertF3aPart7
public import QED.ThreeLoopE.SetECertF3aPart8
public import QED.ThreeLoopE.SetECertF3aPart9
public import QED.ThreeLoopE.SetECertF3aPart10
public import QED.ThreeLoopE.SetECertF3aPart11
public import QED.ThreeLoopE.SetECertF3aPart12
public import QED.ThreeLoopE.SetECertF3aPart13
public import QED.ThreeLoopE.SetECertF3aPart14
public import QED.ThreeLoopE.SetECertF3aPart15
public import QED.ThreeLoopE.SetECertF3aPart16
public import QED.ThreeLoopE.SetECertF3aPart17
public import QED.ThreeLoopE.SetECertF3aPart18
public import QED.ThreeLoopE.SetECertF3aPart19
public import QED.ThreeLoopE.SetECertF3aPart20
public import QED.ThreeLoopE.SetECertF3aPart21
public import QED.ThreeLoopE.SetECertF3aPart22
public import QED.ThreeLoopE.SetECertF3aPart23
public import QED.ThreeLoopE.SetECertF3aPart24
public import QED.ThreeLoopE.SetECertF3aPart25
public import QED.ThreeLoopE.SetECertF3aPart26
public import QED.ThreeLoopE.SetECertF3aPart27
public import QED.ThreeLoopE.SetECertF3aPart28
public import QED.ThreeLoopE.SetECertF3aPart29
public import QED.ThreeLoopE.SetECertF3aPart30
public import QED.ThreeLoopE.SetECertF3aPart31

/-!
# The `f3a` reduction of set (e)

The label-split certificate of `QED.Algebra.IBPCertSector` reduces the projected combination `Y - (d
- 1)² T₁` of the set (e) vertex diagrams of self-energy topology `f3a`
(`QED.ThreeLoopE.SetECert.f3aTarget`, integrals in scaleless sectors dropped) to the Kira masters
`QED.ThreeLoopE.SetECert.f3aMasters` of the family `QED.ThreeLoopE.SetECert.f3a`, with the IBP
relations, the scaleless sectors and the relabelling symmetries `I(permLabel σ ν) = I(ν)` of the
entries of `QED.ThreeLoopE.SetECert.f3aSyms`. The checker reduces to a master list `f3aMs` that
holds the masters and the terms of the symmetry entries (`f3aMs_comb`). Further hypotheses: the
numerator-symmetry relations `r` of `QED.ThreeLoopE.SetECert.f3aRels` (`Σ c [l] = 0`, integer
coefficients, scaleless-sector terms dropped). Each comes from a change of loop momenta `k ↦ A k + b
p`, `p ↦ s p` mapping the denominators of the integral `ν` to denominators and its numerators to
linear combinations of denominators (checked offline as a pointwise identity of integrands,
`symn.py`); they enter with multipliers `ζ`.

## Main statements

* `QED.ThreeLoopE.SetECert.f3a_reduction_of_den`: at every `d` with `q(d) ≠ 0`, for every family of
  values satisfying the hypotheses at `d`, the target combination equals the certified combination
  of the masters.
* `QED.ThreeLoopE.SetECert.f3a_reduction`: the same off a finite set of `d`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert QED.Algebra.IBPCert.Sector

theorem f3aMT_ok : mtOk f3a f3aCtx 132 16 = true := by decide +kernel

theorem f3aFac_ok : facOk f3aCtx f3aFac f3aQE f3aNF = true := by decide +kernel

theorem f3aZS_eq :
    f3aZS = f3a.zeroSectors.map fun S => S.map fun a => (a, f3aCtx.B ^ a) := by
  decide +kernel

theorem f3aBlocks_ok :
    f3aBlocks.all (GBlock.ok f3aCtx 3 4 9 32 f3aQE f3aYb f3aNF f3aZS) = true := by
  simp only [f3aBlocks, rApp_eq, List.all_append, f3aB0_ok, f3aB1_ok, f3aB2_ok, f3aB3_ok, f3aB4_ok,
    f3aB5_ok, f3aB6_ok, f3aB7_ok, f3aB8_ok, f3aB9_ok, f3aB10_ok, f3aB11_ok, f3aB12_ok, f3aB13_ok,
    f3aB14_ok, f3aB15_ok, Bool.and_self]

theorem f3aClaim_range :
    (f3aTarget ++ f3aMs).all (fun t => inRange 9 4 9 t.1) = true := by
  decide +kernel

theorem f3aBound :
    (f3aBlocks.map fun b => b.seeds.length).sum * (16 * (f3aYb * 132)) +
      Poly.norm1 f3aDen * (f3aTarget.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum +
      (f3aMs.map fun t : List ℤ × Poly => Poly.norm1 t.2).sum < f3aCtx.x0 := by
  decide +kernel

theorem f3aTargetL_lt : f3aTargetL.length < 32 := by decide +kernel

theorem f3aMsL_lt : f3aMsL.length < 32 := by decide +kernel

theorem f3aDen_ne_zero : Poly.isZero f3aDen = false := by decide +kernel

/-- The master list of the checker is the Kira masters plus the symmetry terms. -/
theorem f3aMs_comb :
    LinComb.ofTerms (f3aMs ++ LinComb.smul [-1] (f3aMasters ++ symTerms f3aSyms ++
      relTerms f3aRels)) =
      [] := by
  decide +kernel

theorem f3a_parts : ∀ p < 32,
    partOk f3aCtx f3aDen (rGetL (chunks f3aTargetL f3aTarget) p)
      (rGetL (chunks f3aMsL f3aMs) p) f3aBlocks p = true := fun p hp =>
  match p, hp with
  | 0, _ => f3aPart0
  | 1, _ => f3aPart1
  | 2, _ => f3aPart2
  | 3, _ => f3aPart3
  | 4, _ => f3aPart4
  | 5, _ => f3aPart5
  | 6, _ => f3aPart6
  | 7, _ => f3aPart7
  | 8, _ => f3aPart8
  | 9, _ => f3aPart9
  | 10, _ => f3aPart10
  | 11, _ => f3aPart11
  | 12, _ => f3aPart12
  | 13, _ => f3aPart13
  | 14, _ => f3aPart14
  | 15, _ => f3aPart15
  | 16, _ => f3aPart16
  | 17, _ => f3aPart17
  | 18, _ => f3aPart18
  | 19, _ => f3aPart19
  | 20, _ => f3aPart20
  | 21, _ => f3aPart21
  | 22, _ => f3aPart22
  | 23, _ => f3aPart23
  | 24, _ => f3aPart24
  | 25, _ => f3aPart25
  | 26, _ => f3aPart26
  | 27, _ => f3aPart27
  | 28, _ => f3aPart28
  | 29, _ => f3aPart29
  | 30, _ => f3aPart30
  | 31, _ => f3aPart31
  | _ + 32, h => absurd h (by omega)

/-- The `f3a` reduction at every dimension `d` where the common denominator `q(d)` is nonzero: for
every family of values `I` satisfying the IBP relations, the scaleless sectors and the relabelling
symmetries of `f3aSyms` of `f3a` at `d`, the target combination `Σ tₗ(d) I(l)` equals `Σ (nⱼ(d) /
q(d)) I(Mⱼ)` over the Kira masters. -/
theorem f3a_reduction_of_den {K : Type*} [Field K] [CharZero K] (d : K)
    (hd : Poly.eval d f3aDen ≠ 0) (I : (Fin f3a.nProp → ℤ) → K → K)
    (hI : f3a.IBPHolds I d) (hz : f3a.ZeroSectors I d)
    (hs : ∀ e ∈ f3aSyms, f3a.SymHoldsAt I d e.1 e.2.1)
    (hn : ∀ e ∈ f3aRels,
      LinComb.eval (fun l => I (toVec f3a.nProp l) d) d e.1 = 0) :
    (f3aTarget.map fun t => Poly.eval d t.2 * I (toVec f3a.nProp t.1) d).sum =
      (f3aMasters.map fun m =>
        Poly.eval d m.2 / Poly.eval d f3aDen * I (toVec f3a.nProp m.1) d).sum := by
  have h := gcert_reduction (P := 32) (den := f3aDen) (T := f3aTarget) (Ms := f3aMs)
    (tl := f3aTargetL) (ml := f3aMsL) f3aMT_ok f3aFac_ok f3aZS_eq f3aBlocks_ok f3aClaim_range
    f3aTargetL_lt f3aMsL_lt f3aBound f3a_parts I d hI hz hd
  rw [h]
  exact masters_of_comb_rel f3a I d f3aDen f3aMs f3aMasters f3aSyms f3aRels f3aMs_comb hs hn

/-- **The `f3a` reduction.** Off a finite set of dimensions `d`, `q(d) ≠ 0` and, for every family of
values `I` satisfying the IBP relations, the scaleless sectors and the relabelling symmetries of
`f3aSyms` of `f3a` at `d`, the target combination equals the certified combination of the Kira
masters. -/
theorem f3a_reduction {K : Type*} [Field K] [CharZero K] :
    ∃ s : Finset K, ∀ d ∉ s, Poly.eval d f3aDen ≠ 0 ∧
      ∀ I : (Fin f3a.nProp → ℤ) → K → K, f3a.IBPHolds I d → f3a.ZeroSectors I d →
      (∀ e ∈ f3aSyms, f3a.SymHoldsAt I d e.1 e.2.1) →
      (∀ e ∈ f3aRels,
        LinComb.eval (fun l => I (toVec f3a.nProp l) d) d e.1 = 0) →
        (f3aTarget.map fun t => Poly.eval d t.2 * I (toVec f3a.nProp t.1) d).sum =
          (f3aMasters.map fun m =>
            Poly.eval d m.2 / Poly.eval d f3aDen * I (toVec f3a.nProp m.1) d).sum := by
  obtain ⟨s, hs⟩ := Poly.exists_finset_eval_ne_zero (K := K) f3aDen_ne_zero
  exact ⟨s, fun d hd => ⟨hs d hd, fun I hI hz hsym hrel =>
    f3a_reduction_of_den d (hs d hd) I hI hz hsym hrel⟩⟩

end QED.ThreeLoopE.SetECert
