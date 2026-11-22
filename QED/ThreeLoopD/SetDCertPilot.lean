/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDCertPilotChain

/-!
# Reduction of the set (d) integral `[1, 1, 1, 1, 1, 1, 1, 0, 0]`: the reduction

The last step of the chain, rewritten as the reduction of the target.
-/

@[expose] public section

namespace QED.ThreeLoopD.SetDCertPilot

open QED.Algebra.IBPCert QED.ThreeLoopD.SetDCert

/-- The common denominator of the reduction (generated). -/
def den : Poly := [116121600, -264130560, 261017088, -146380288, 50957824, -11276800, 1549312,
    -120832, 4096]

def masters_0 : List (List ℤ × Poly) := [([0, 1, 1, 1, 1, 1, 1, 0, 0], [-32256000, 75878400,
    -77653760, 45156224, -16318592, 3752576, -536192, 43520, -1536]), ([0, 1, 1, 1, 0, 1, 1, 0,
    0], [-7257600, 17919360, -19260288, 11768064, -4469504, 1080192, -162176, 13824, -512]), ([0,
    1, 0, 0, 1, 1, 1, 0, 0], [37658880, -110076576, 141992920, -106064272, 50547856, -15935872,
    3322840, -441808, 33984, -1152]), ([1, 1, 0, 0, 1, 0, 1, 0, 0], [-10368000, 30211200,
    -38755680, 28728832, -13561800, 4227832, -870360, 114088, -8640, 288]), ([-1, 1, 0, 0, 1, 1,
    1, 0, 0], [11612160, -35154432, 46771200, -35897760, 17519040, -5638536, 1197000, -161640,
    12600, -432]), ([0, 0, 0, 0, 1, 1, 1, 0, 0], [13440, -531808, 1415664, -1672168, 1122140,
    -466000, 122456, -19872, 1820, -72]), ([0, 1, 1, 1, 0, 1, 0, 0, 0], [-1497600, 4042560,
    -4729808, 3132680, -1284488, 333800, -53672, 4880, -192]), ([0, 1, 1, 1, 0, 0, 1, 0, 0],
    [-1497600, 4042560, -4729808, 3132680, -1284488, 333800, -53672, 4880, -192]), ([0, 1, 1, 0,
    0, 1, 1, 0, 0], [-1267200, 3376320, -3896176, 2543400, -1027216, 262800, -41584, 3720, -144]),
    ([0, 0, 0, 1, 1, 1, 1, 0, 0], [-3225600, 8636160, -10017728, 6575584, -2671136, 687520,
    -109472, 9856, -384]), ([1, 1, 0, 0, 1, 1, 0, 0, 0], [-10368000, 30211200, -38755680,
    28728832, -13561800, 4227832, -870360, 114088, -8640, 288]), ([0, 0, 0, 1, 1, 1, 0, 0, 0],
    [-537600, 1596160, -2045568, 1476928, -656672, 184000, -31712, 3072, -128]), ([0, 0, 0, 1, 1,
    0, 1, 0, 0], [-537600, 1596160, -2045568, 1476928, -656672, 184000, -31712, 3072, -128])]

/-- The masters and their numerators (generated). -/
def masters : List (List ℤ × Poly) :=
  masters_0
theorem claim_last :
    step2.claim = ([1, 1, 1, 1, 1, 1, 1, 0, 0], den) :: masters.map fun m => (m.1,
        Poly.neg m.2) := by
  decide +kernel

/-- **The reduction.** Under the chain hypotheses at `d` and `den(d) ≠ 0`, the target is the
certified combination of the masters. -/
theorem reduction {K : Type*} [Field K] (I : (Fin lbl.nProp → ℤ) → K → K) (d : K)
    (h : ChainHyp I d) (hq : Poly.eval d den ≠ 0) :
    I (toVec lbl.nProp [1, 1, 1, 1, 1, 1, 1, 0, 0]) d =
      (masters.map fun m => Poly.eval d m.2 / Poly.eval d den *
        I (toVec lbl.nProp m.1) d).sum := by
  have hK := holds2 I d h
  rw [claim_last] at hK
  exact Step.reduction (fun l => I (toVec lbl.nProp l) d) d _ _ _ hK hq

theorem den_ne_zero : Poly.isZero den = false := by decide +kernel

/-- The exceptional set `{den = 0}` is finite. -/
theorem exists_finset_reduction {K : Type*} [Field K] [CharZero K] :
    ∃ s : Finset K, ∀ d ∉ s, ∀ I : (Fin lbl.nProp → ℤ) → K → K, ChainHyp I d →
      I (toVec lbl.nProp [1, 1, 1, 1, 1, 1, 1, 0, 0]) d =
        (masters.map fun m => Poly.eval d m.2 / Poly.eval d den *
          I (toVec lbl.nProp m.1) d).sum := by
  obtain ⟨s, hs⟩ := Poly.exists_finset_eval_ne_zero (K := K) den_ne_zero
  exact ⟨s, fun d hd I h => reduction I d h (hs d hd)⟩

end QED.ThreeLoopD.SetDCertPilot
