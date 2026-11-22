/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3j
public import QED.ThreeLoopE.SetEBridgeSym

/-!
# Set (e), family `f3j`: the reduction in the Laporta-Remiddi basis

The four masters of the `f3j` reduction (`QED.ThreeLoopE.SetECert.f3j_reduction`) are corner
integrals of the family `f3j` that a change of loop momenta `k ↦ A k + b p` carries onto LR
masters, written as corner vectors of the family `f3c` (`QED.ThreeLoopE.SetEBridgeSym`):

* `[1,1,1,0,0,1,0,0,0] ↦ I₁₇` (the identity map: the lines `k₁, k₂, k₃, p - k₁ - k₂ - k₃` are
  common to both families);
* `[0,1,1,1,0,1,0,0,0] ↦ I₁₄`: `k₁ ↦ -k₁ - k₂ - k₃ + 2p`, `k₂ ↦ k₁`, `k₃ ↦ k₂`;
* `[1,1,0,0,1,1,0,0,0] ↦ I₁₆`: `k₁ ↦ k₂`, `k₂ ↦ k₃`, `k₃ ↦ k₁`;
* `[0,0,0,1,1,1,0,0,0] ↦ I₁₈`: `k₁ ↦ k₁`, `k₂ ↦ -k₁ + k₂ + k₃`, `k₃ ↦ -k₂`.

These identities relate integrals of two different families, so they are stated as a hypothesis
`QED.ThreeLoopE.SetECert.f3jCrossHold` on the two families of values. Under it, the `f3j` part of
set (e) is a combination of the LR masters of `f3c`, with the coefficients of the survey (the
four coefficients agree exactly with the survey's `f3j` coefficients of `Y - (d - 1)² T₁`,
offline check).

## Main statements

* `QED.ThreeLoopE.SetECert.f3j_bridge_of_den`: at every `d` with `q(d) ≠ 0`, the projected
  combination of the `f3j` diagrams equals `Σⱼ (nⱼ(d) / q(d)) J(LRⱼ)`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert

/-- The LR master, as a corner vector of `f3c`, of each master of the `f3j` reduction. -/
def f3jToLR : List (List ℤ × List ℤ) :=
  [([1, 1, 1, 0, 0, 1, 0, 0, 0], f3cLRI17), ([0, 1, 1, 1, 0, 1, 0, 0, 0], f3cLRI14),
    ([1, 1, 0, 0, 1, 1, 0, 0, 0], f3cLRI16), ([0, 0, 0, 1, 1, 1, 0, 0, 0], f3cLRI18)]

/-- The cross-family relabellings: the value of each `f3j` master is that of its LR master in
`f3c`. -/
def f3jCrossHold {K : Type*} [Field K] (I : (Fin f3j.nProp → ℤ) → K → K)
    (J : (Fin f3c.nProp → ℤ) → K → K) (d : K) : Prop :=
  ∀ p ∈ f3jToLR, I (toVec f3j.nProp p.1) d = J (toVec f3c.nProp p.2) d

/-- The `f3j` coefficients on the LR masters of `f3c` (numerators over `f3jDen`). -/
noncomputable def f3jBridgeLR : List (List ℤ × Poly) :=
  f3jMasters.map fun m => ((f3jToLR.lookup m.1).getD m.1, m.2)

theorem f3jToLR_mem : ∀ m ∈ f3jMasters, (m.1, (f3jToLR.lookup m.1).getD m.1) ∈ f3jToLR := by
  decide +kernel

/-- **The `f3j` reduction in the Laporta-Remiddi basis.** If `q(d) ≠ 0`, `I` satisfies the IBP
relations and the scaleless sectors of `f3j` at `d`, and the values `J` of `f3c` satisfy the
cross-family relabellings, then the projected combination of the `f3j` diagrams equals
`Σⱼ (nⱼ(d) / q(d)) J(LRⱼ)` over `I₁₇, I₁₄, I₁₆, I₁₈`. -/
theorem f3j_bridge_of_den {K : Type*} [Field K] (d : K) (hq : Poly.eval d f3jDen ≠ 0)
    (I : (Fin f3j.nProp → ℤ) → K → K) (J : (Fin f3c.nProp → ℤ) → K → K)
    (hI : f3j.IBPHolds I d) (hz : f3j.ZeroSectors I d) (hx : f3jCrossHold I J d) :
    (f3jTarget.map fun t => Poly.eval d t.2 * I (toVec f3j.nProp t.1) d).sum =
      (f3jBridgeLR.map fun m =>
        Poly.eval d m.2 / Poly.eval d f3jDen * J (toVec f3c.nProp m.1) d).sum := by
  rw [f3j_reduction_of_chainHyp I d (f3jChainHyp_of_global hI hz) hq, f3jBridgeLR, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun m hm => ?_)
  simp only [Function.comp_apply]
  rw [hx _ (f3jToLR_mem m hm)]

end QED.ThreeLoopE.SetECert
