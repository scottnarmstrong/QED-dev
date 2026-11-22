/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3jData15

/-!
# The `f3j` reduction of set (e): kernel checks

Each step of the generated chain is checked by `decide +kernel` and turned into its relation by
`QED.Algebra.IBPCert.KStep.sound'`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert

/-- All steps of the chain. -/
def f3jSteps : List KStep :=
  [f3jStep0, f3jStep1, f3jStep2, f3jStep3]

/-- The hypotheses of the chain at `d`: the IBP relations at every seed and the vanishing of
every declared zero label. -/
def F3jChainHyp {K : Type*} [Field K] (I : (Fin f3j.nProp → ℤ) → K → K) (d : K) : Prop :=
  ∀ c ∈ f3jSteps, (∀ s ∈ c.seeds, f3j.IBPHoldsAt I d s.i s.j (toVec f3j.nProp s.nu)) ∧
    ∀ l ∈ c.zeros, I (toVec f3j.nProp l) d = 0

theorem f3jCheck0 : f3jStep0.check f3j 9 3 = true := by decide +kernel

theorem f3jHolds0 {K : Type*} [Field K] (I : (Fin f3j.nProp → ℤ) → K → K) (d : K)
    (h : F3jChainHyp I d) :
    LinComb.eval (fun l => I (toVec f3j.nProp l) d) d f3jStep0.claim = 0 :=
  have hk := h f3jStep0
      (.head _)
  KStep.sound' f3jCheck0 I d hk.1 hk.2 trivial

theorem f3jCheck1 : f3jStep1.check f3j 9 3 = true := by decide +kernel

theorem f3jHolds1 {K : Type*} [Field K] (I : (Fin f3j.nProp → ℤ) → K → K) (d : K)
    (h : F3jChainHyp I d) :
    LinComb.eval (fun l => I (toVec f3j.nProp l) d) d f3jStep1.claim = 0 :=
  have hk := h f3jStep1
      (.tail _ <| .head _)
  KStep.sound' f3jCheck1 I d hk.1 hk.2 ⟨f3jHolds0 I d h, trivial⟩

theorem f3jCheck2 : f3jStep2.check f3j 9 3 = true := by decide +kernel

theorem f3jHolds2 {K : Type*} [Field K] (I : (Fin f3j.nProp → ℤ) → K → K) (d : K)
    (h : F3jChainHyp I d) :
    LinComb.eval (fun l => I (toVec f3j.nProp l) d) d f3jStep2.claim = 0 :=
  have hk := h f3jStep2
      (.tail _ <| .tail _ <| .head _)
  KStep.sound' f3jCheck2 I d hk.1 hk.2 ⟨f3jHolds1 I d h, trivial⟩

theorem f3jCheck3 : f3jStep3.check f3j 9 3 = true := by decide +kernel

theorem f3jHolds3 {K : Type*} [Field K] (I : (Fin f3j.nProp → ℤ) → K → K) (d : K)
    (h : F3jChainHyp I d) :
    LinComb.eval (fun l => I (toVec f3j.nProp l) d) d f3jStep3.claim = 0 :=
  have hk := h f3jStep3
      (.tail _ <| .tail _ <| .tail _ <| .head _)
  KStep.sound' f3jCheck3 I d hk.1 hk.2 ⟨f3jHolds2 I d h, trivial⟩

theorem f3jSteps_check : ∀ c ∈ f3jSteps, c.check f3j 9 3 = true := by
  intro c hc
  simp only [f3jSteps, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact f3jCheck0
  · exact f3jCheck1
  · exact f3jCheck2
  · exact f3jCheck3

end QED.ThreeLoopE.SetECert
