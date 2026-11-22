/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3jChain

/-!
# The `f3j` reduction of set (e)

The generated chain `QED.ThreeLoopE.SetECert.f3jSteps`, checked step by step by the single-point
checker `QED.Algebra.IBPCert.KStep`, reduces the projected combination `Y - (d - 1)² T₁` of the
set (e) vertex diagrams of self-energy topology `f3j` (`QED.ThreeLoopE.SetECert.f3jTarget`) to
the four masters `QED.ThreeLoopE.SetECert.f3jMasters`: `[1,1,1,0,0,1,0,0,0]`,
`[0,1,1,1,0,1,0,0,0]`, `[1,1,0,0,1,1,0,0,0]` and `[0,0,0,1,1,1,0,0,0]` (in the labelling of
Laporta-Remiddi: `I₁₇`, `I₁₄`, `I₁₆`, `I₁₈` up to normalization and sign). The last step's claim
is `q · Σ tₗ [l] - Σ nⱼ [Mⱼ]` by definition, so the reduction is
`QED.Algebra.IBPCert.Step.reduction_combo`.

## Main statements

* `QED.ThreeLoopE.SetECert.f3j_reduction_of_chainHyp`: under the IBP relations at the seeds of
  the chain and the vanishing of its zero labels at `d`, and `q(d) ≠ 0`, the target combination
  equals the certified combination of the masters.
* `QED.ThreeLoopE.SetECert.f3j_reduction`: the same off a finite set of `d`, for every family of
  values satisfying all IBP relations and the scaleless sectors of `f3j` at `d`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert

/-- **The `f3j` reduction under the local hypotheses of the chain.** -/
theorem f3j_reduction_of_chainHyp {K : Type*} [Field K] (I : (Fin f3j.nProp → ℤ) → K → K)
    (d : K) (h : F3jChainHyp I d) (hq : Poly.eval d f3jDen ≠ 0) :
    (f3jTarget.map fun t => Poly.eval d t.2 * I (toVec f3j.nProp t.1) d).sum =
      (f3jMasters.map fun m =>
        Poly.eval d m.2 / Poly.eval d f3jDen * I (toVec f3j.nProp m.1) d).sum :=
  Step.reduction_combo (fun l => I (toVec f3j.nProp l) d) d _ _ _ (f3jHolds3 I d h) hq

/-- A checked step has admissible seeds and zero labels in the zero sectors. -/
theorem kStep_ok_of_check {F : Family} {B o : ℕ} {c : KStep} (h : c.check F B o = true) :
    (∀ s ∈ c.seeds, s.ok F = true) ∧ ∀ l ∈ c.zeros, F.zeroPred l = true := by
  simp only [KStep.check, KStep.admissible, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.2, fun l hl => (h.1.1.2 l hl).2⟩

/-- The global hypotheses (all IBP relations and the scaleless sectors) give those of the
chain. -/
theorem f3jChainHyp_of_global {K : Type*} [Field K] {I : (Fin f3j.nProp → ℤ) → K → K} {d : K}
    (hI : f3j.IBPHolds I d) (hz : f3j.ZeroSectors I d) : F3jChainHyp I d := by
  intro c hc
  obtain ⟨hs, hl⟩ := kStep_ok_of_check (f3jSteps_check c hc)
  refine ⟨fun s hs' => ?_, fun l hl' => hz.at (hl l hl')⟩
  have := hs s hs'
  simp only [Seed.ok, Bool.and_eq_true, Nat.blt_eq] at this
  exact hI.at this.1.1 this.1.2 _

theorem f3jDen_ne_zero : Poly.isZero f3jDen = false := by decide +kernel

/-- **The `f3j` reduction.** Off a finite set of dimensions `d`, for every family of values `I`
satisfying the IBP relations and the scaleless sectors of `f3j` at `d`, the projected
combination `Σ tₗ(d) I(l)` of the `f3j` diagrams equals `Σ (nⱼ(d) / q(d)) I(Mⱼ)` over the four
masters. -/
theorem f3j_reduction {K : Type*} [Field K] [CharZero K] :
    ∃ s : Finset K, ∀ d ∉ s, Poly.eval d f3jDen ≠ 0 ∧
      ∀ I : (Fin f3j.nProp → ℤ) → K → K, f3j.IBPHolds I d → f3j.ZeroSectors I d →
        (f3jTarget.map fun t => Poly.eval d t.2 * I (toVec f3j.nProp t.1) d).sum =
          (f3jMasters.map fun m =>
            Poly.eval d m.2 / Poly.eval d f3jDen * I (toVec f3j.nProp m.1) d).sum := by
  obtain ⟨s, hs⟩ := Poly.exists_finset_eval_ne_zero (K := K) f3jDen_ne_zero
  exact ⟨s, fun d hd => ⟨hs d hd, fun I hI hz =>
    f3j_reduction_of_chainHyp I d (f3jChainHyp_of_global hI hz) (hs d hd)⟩⟩

end QED.ThreeLoopE.SetECert
