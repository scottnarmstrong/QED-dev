/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopZero
public import QED.ThreeLoopD.SetDCertPilot

/-!
# The set (d) pilot reduction for the face values `val3`

The pilot certificate `QED.ThreeLoopD.SetDCertPilot` reduces the set (d) integral
`[1, 1, 1, 1, 1, 1, 1, 0, 0]` to masters under the chain hypotheses
`QED.ThreeLoopD.SetDCertPilot.ChainHyp`: the IBP relations at the seeds of its three steps and
the vanishing of its declared zero labels. Every seed and every zero label of the chain has
`ν₇, ν₈ ≤ 0`, and every zero label lies in a declared scaleless sector (`pilotOk`, checked by
the kernel), so for `d ∉ ℚ` both hypotheses hold for `QED.DimReg.ThreeLoop.val3`
(`QED.DimReg.ThreeLoop.ibpHoldsAt_val3`, `QED.DimReg.ThreeLoop.val3_zero_of_zeroPred`).

## Main statements

* `chainHyp_val3`: the chain hypotheses for `val3` at every `d ∉ ℚ`;
* `val3_pilot_reduction`: off a finite set of `d ∉ ℚ`, `val3` at the target is the certified
  combination of `val3` at the masters (all of which, like the target, have `ν₇ = ν₈ = 0`:
  `masters_face`).
-/

@[expose] public section

open QED.Algebra.IBPCert QED.ThreeLoopD.SetDCert QED.ThreeLoopD.SetDCertPilot
open QED.DimReg.TwoLoopSESector (Irr)

namespace QED.DimReg.ThreeLoop

/-- The seeds of the pilot chain have `i < 3`, `j < 4` and `ν₇, ν₈ ≤ 0`; its zero labels lie in
declared scaleless sectors and have `ν₇, ν₈ ≤ 0`. -/
def pilotOk : Bool :=
  steps.all fun c =>
    c.seeds.all (fun s => ((Nat.blt s.i 3 && Nat.blt s.j 4) && intNonpos (s.nu.getD 7 0)) &&
      intNonpos (s.nu.getD 8 0)) &&
    c.zeros.all fun l => (lbl.zeroPred l && intNonpos (l.getD 7 0)) && intNonpos (l.getD 8 0)

theorem pilotOk_eq : pilotOk = true := by decide +kernel

/-- The masters of the pilot reduction have `ν₇ = ν₈ = 0`. -/
theorem masters_face :
    masters.all (fun m => m.1.getD 7 0 == 0 && m.1.getD 8 0 == 0) = true := by
  decide +kernel

/-- **The chain hypotheses of the pilot reduction hold for `val3`** at every `d ∉ ℚ`. -/
theorem chainHyp_val3 {d : ℂ} (hd : Irr d) : ChainHyp val3 d := by
  intro c hc
  have h := List.all_eq_true.1 pilotOk_eq c hc
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hs, hz⟩ := h
  refine ⟨fun s hs' => ?_, fun l hl => ?_⟩
  · obtain ⟨⟨⟨hi, hj⟩, h7⟩, h8⟩ := hs s hs'
    exact ibpHoldsAt_val3 hd (Nat.blt_eq ▸ hi) (Nat.blt_eq ▸ hj) _ (nonpos_of_intNonpos h7)
      (nonpos_of_intNonpos h8)
  · obtain ⟨⟨hzp, h7⟩, h8⟩ := hz l hl
    exact val3_zero_of_zeroPred hd hzp (nonpos_of_intNonpos h7) (nonpos_of_intNonpos h8)

/-- **The set (d) pilot reduction for the face values.** Off a finite set of dimensions
`d ∉ ℚ`, `val3 [1, 1, 1, 1, 1, 1, 1, 0, 0] d` is the certified combination of the values `val3`
at the masters of `QED.ThreeLoopD.SetDCertPilot.masters`. -/
theorem val3_pilot_reduction : ∃ s : Finset ℂ, ∀ d, Irr d → d ∉ s →
    val3 (toVec 9 [1, 1, 1, 1, 1, 1, 1, 0, 0]) d =
      (masters.map fun m => Poly.eval d m.2 / Poly.eval d den * val3 (toVec 9 m.1) d).sum := by
  obtain ⟨s, hs⟩ := exists_finset_reduction (K := ℂ)
  exact ⟨s, fun d hd hds => hs d hds val3 (chainHyp_val3 hd)⟩

end QED.DimReg.ThreeLoop
