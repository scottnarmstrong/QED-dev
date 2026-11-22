/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDCertPilotData2

/-!
# Reduction of the set (d) integral `[1, 1, 1, 1, 1, 1, 1, 0, 0]`: kernel checks

Each step is checked by `decide +kernel` and turned into its relation by
`QED.Algebra.IBPCert.KStep.sound'`; the reduction itself is stated in the next module.
-/

@[expose] public section

namespace QED.ThreeLoopD.SetDCertPilot

open QED.Algebra.IBPCert QED.ThreeLoopD.SetDCert

/-- All steps of the chain. -/
def steps : List KStep :=
  [step0, step1, step2]

/-- The hypotheses of the chain at `d`: the IBP relations at every seed and the vanishing of
every declared zero label. -/
def ChainHyp {K : Type*} [Field K] (I : (Fin lbl.nProp → ℤ) → K → K) (d : K) : Prop :=
  ∀ c ∈ steps, (∀ s ∈ c.seeds, lbl.IBPHoldsAt I d s.i s.j (toVec lbl.nProp s.nu)) ∧
    ∀ l ∈ c.zeros, I (toVec lbl.nProp l) d = 0

theorem check0 : step0.check lbl 8 3 = true := by decide +kernel

theorem holds0 {K : Type*} [Field K] (I : (Fin lbl.nProp → ℤ) → K → K) (d : K)
    (h : ChainHyp I d) :
    LinComb.eval (fun l => I (toVec lbl.nProp l) d) d step0.claim = 0 :=
  have hk := h step0 (List.mem_cons_self)
  KStep.sound' check0 I d hk.1 hk.2 trivial

theorem check1 : step1.check lbl 8 3 = true := by decide +kernel

theorem holds1 {K : Type*} [Field K] (I : (Fin lbl.nProp → ℤ) → K → K) (d : K)
    (h : ChainHyp I d) :
    LinComb.eval (fun l => I (toVec lbl.nProp l) d) d step1.claim = 0 :=
  have hk := h step1 (List.mem_cons_of_mem _ (List.mem_cons_self))
  KStep.sound' check1 I d hk.1 hk.2 ⟨holds0 I d h, trivial⟩

theorem check2 : step2.check lbl 8 3 = true := by decide +kernel

theorem holds2 {K : Type*} [Field K] (I : (Fin lbl.nProp → ℤ) → K → K) (d : K)
    (h : ChainHyp I d) :
    LinComb.eval (fun l => I (toVec lbl.nProp l) d) d step2.claim = 0 :=
  have hk := h step2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  KStep.sound' check2 I d hk.1 hk.2 ⟨holds1 I d h, trivial⟩

end QED.ThreeLoopD.SetDCertPilot
