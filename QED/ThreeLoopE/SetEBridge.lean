/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopE.SetECertF3c
public import QED.ThreeLoopE.SetEBridgeI1
public import QED.ThreeLoopE.SetEBridgeX
public import QED.ThreeLoopE.SetEBridgeData1
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Set (e), family `f3c`: the reduction in the Laporta-Remiddi basis

`QED.ThreeLoopE.SetECert.f3c_reduction_of_den` reduces the projected combination
`Y - (d - 1)² T₁` of the `f3c` diagrams to the 46 IBP masters `f3cMasters`. This file changes
the basis to the seventeen masters of Laporta-Remiddi that set (e)'s assembly uses
(`QED.ThreeLoopE.SetEMasters`): the corner integrals `f3cLRI2, …, f3cLRI18` and the numerator
master `f3cLRI1` of `QED.ThreeLoopE.SetEBridgeSym`, all in the family `f3c`. It uses

* the reduction of `2 I₁` to the same masters (`QED.ThreeLoopE.SetECert.f3cI1_reduction_of_den`):
  this is the relation `J₀ = 2(d - 4)/(3d - 13) I₁ + (lower masters)` for Kira's scalar triple
  cross `J₀ = [1,1,1,1,1,1,1,1,0]`, used to eliminate `J₀`;
* the reduction of two sector-92 numerator integrals (`f3cX_reduction_of_den`) and the symmetry
  relation of the numerator master `[-1,0,1,1,1,0,1,0,0]` (`f3cSymNHolds`);
* the 28 corner symmetries `f3cSymsHold`, which identify the remaining masters with LR's.

The combination of these relations is checked exactly, as an identity of linear combinations
with coefficients in `ℤ[d]` (`QED.ThreeLoopE.SetECert.bridgeCheck`, by `decide +kernel`).

## Main statements

* `QED.ThreeLoopE.SetECert.f3c_bridge_of_den`: at every `d` with `Q(d) ≠ 0`
  (`Q = f3cBridgeQ`, explicit), for every family of values `I` satisfying the IBP relations,
  the scaleless sectors and the symmetry relations of `f3c` at `d`,
  `Σ tₗ(d) I(l) = Σⱼ (nⱼ(d) / (q α)(d)) I(LRⱼ) + (n₁(d) / (q α)(d)) I₁`.
* `QED.ThreeLoopE.SetECert.f3c_bridge`: the same off a finite set of `d`.

The coefficients `nⱼ / (q α)` are the `f3c` part of the survey's set (e) coefficients (before
the factor `1 / (512 (d - 1)(d - 2))` of `F₂` and `a⁽³⁾`, and before the sum over families and
counterterms): they agree exactly with the survey's `f3c` coefficients of `Y - (d - 1)² T₁`
mapped to the LR basis (offline check, `setecert/bridge/bridge.py`). The common denominator is
`q α` with `α = 3d - 13`.
-/

@[expose] public section

namespace QED.ThreeLoopE.SetECert

open QED.Algebra.IBPCert

/-! ### An exact check of linear relations -/

/-- The exact check that `L = Σₖ mₖ Rₖ` as linear combinations with coefficients in `ℤ[d]`:
the merged sum `-L + Σₖ mₖ Rₖ` has no nonzero coefficient. -/
def bridgeCheck (L : LinComb) (rels : List (LinComb × Poly)) : Bool :=
  LinComb.vanishes (fun _ => false) (LinComb.sumTree 64 (LinComb.ofTerms (LinComb.smul [-1] L) ::
    rels.map fun r => LinComb.ofTerms (LinComb.smul r.2 r.1)))

theorem eval_eq_zero_of_bridgeCheck {K : Type*} [Field K] (J : List ℤ → K) (d : K)
    {L : LinComb} {rels : List (LinComb × Poly)} (h : bridgeCheck L rels = true)
    (hr : ∀ r ∈ rels, LinComb.eval J d r.1 = 0) : LinComb.eval J d L = 0 := by
  have h0 := LinComb.eval_eq_zero_of_vanishes J d (z := fun _ => false) (by simp) h
  rw [LinComb.eval_sumTree, List.map_cons, List.sum_cons, LinComb.eval_ofTerms,
    LinComb.eval_smul] at h0
  have hs : ((rels.map fun r => LinComb.ofTerms (LinComb.smul r.2 r.1)).map
      (LinComb.eval J d)).sum = 0 := by
    rw [List.map_map]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
    simp [LinComb.eval_ofTerms, LinComb.eval_smul, hr r hr']
  have hm : Poly.eval d [-1] = -1 := by simp [Poly.eval]
  rw [hs, add_zero, hm, neg_one_mul, neg_eq_zero] at h0
  exact h0

theorem sum_map_div_mul {K : Type*} [Field K] (J : List ℤ → K) (d c : K) :
    ∀ ms : LinComb, (ms.map fun m => Poly.eval d m.2 / c * J m.1).sum =
      LinComb.eval J d ms / c
  | [] => by simp
  | m :: ms => by
    rw [List.map_cons, List.sum_cons, sum_map_div_mul J d c ms, LinComb.eval_cons]
    ring

/-- A reduction `Σ tₗ J(l) = Σ (nⱼ / q) J(Mⱼ)` as a vanishing linear combination. -/
theorem eval_combo_of_reduction {K : Type*} [Field K] (J : List ℤ → K) (d : K) (q : Poly)
    (ts ms : LinComb) (hq : Poly.eval d q ≠ 0)
    (h : (ts.map fun t => Poly.eval d t.2 * J t.1).sum =
      (ms.map fun m => Poly.eval d m.2 / Poly.eval d q * J m.1).sum) :
    LinComb.eval J d (LinComb.smul q ts ++ ms.map fun m => (m.1, Poly.neg m.2)) = 0 := by
  have hneg : ∀ L : LinComb,
      LinComb.eval J d (L.map fun m => (m.1, Poly.neg m.2)) = -LinComb.eval J d L := by
    intro L
    induction L with
    | nil => simp
    | cons m L ih => simp only [List.map_cons, LinComb.eval_cons, ih, Poly.eval_neg]; ring
  rw [LinComb.eval_eq_sum, List.map_append, List.sum_append, ← LinComb.eval_eq_sum,
    ← LinComb.eval_eq_sum, hneg, LinComb.eval_smul, LinComb.eval_eq_sum J d ts, h,
    sum_map_div_mul]
  field_simp
  ring

/-! ### The basis change -/

/-- The numerator symmetry with its scaleless terms dropped:
`2 [-1,0,1,1,1,0,1,0,0] - [0,0,0,1,1,0,1,0,0] + [0,0,1,1,1,0,1,-1,0] - [0,0,1,1,1,0,1,0,-1]`. -/
def f3cRelN : LinComb :=
  [([-1, 0, 1, 1, 1, 0, 1, 0, 0], [2]), ([0, 0, 0, 1, 1, 0, 1, 0, 0], [-1]),
    ([0, 0, 1, 1, 1, 0, 1, -1, 0], [1]), ([0, 0, 1, 1, 1, 0, 1, 0, -1], [-1])]

/-- The relations of the basis change with their multipliers: the `I₁` and sector-92
reductions, the numerator symmetry and the corner symmetries. -/
noncomputable def f3cBridgeRels : List (LinComb × Poly) :=
  (LinComb.smul f3cI1Den f3cI1Target ++ f3cI1Masters.map fun m => (m.1, Poly.neg m.2),
      f3cBridgeMuI1) ::
    (LinComb.smul f3cXDen f3cXTarget ++ f3cXMasters.map fun m => (m.1, Poly.neg m.2),
      f3cBridgeMuX) ::
    (f3cRelN, f3cBridgeMuN) ::
    (f3cSyms.zip f3cBridgeMuS).map fun p => (symRel p.1.1 p.1.2, p.2)

/-- The claimed identity: `α Σ nₘ [Mₘ] - Σⱼ nⱼ [LRⱼ] - (n₁ / 2) · [2 I₁]`. -/
noncomputable def f3cBridgeClaim : LinComb :=
  LinComb.smul f3cBridgeAlpha f3cMasters ++ (f3cBridgeLR.map fun m => (m.1, Poly.neg m.2)) ++
    LinComb.smul (Poly.neg f3cBridgeY) f3cI1Target

theorem f3cBridge_check : bridgeCheck f3cBridgeClaim f3cBridgeRels = true := by
  decide +kernel

theorem f3cBridgeI1_eq : Poly.smul 2 f3cBridgeY = f3cBridgeI1 := by decide +kernel

/-- The common denominator `q α` of the LR coefficients. -/
noncomputable def f3cBridgeDen : Poly := Poly.mul f3cDen f3cBridgeAlpha

/-- The polynomial whose nonvanishing at `d` the basis change needs: `q α q₁ qₓ`. -/
noncomputable def f3cBridgeQ : Poly := Poly.mul f3cBridgeDen (Poly.mul f3cI1Den f3cXDen)

theorem f3cBridgeQ_ne_zero : Poly.isZero f3cBridgeQ = false := by decide +kernel

theorem f3cI1Target_eval {K : Type*} [Field K] [CharZero K] (I : (Fin f3c.nProp → ℤ) → K → K)
    (d : K) :
    LinComb.eval (fun l => I (toVec f3c.nProp l) d) d f3cI1Target = 2 * f3cLRI1 I d := by
  simp only [f3cI1Target, f3cI1Target_0, f3cLRI1, LinComb.eval, Poly.eval]
  push_cast
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  field_simp
  ring

theorem f3cRelN_eval {K : Type*} [Field K] {I : (Fin f3c.nProp → ℤ) → K → K} {d : K}
    (hz : f3c.ZeroSectors I d) (hn : f3cSymNHolds I d) :
    LinComb.eval (fun l => I (toVec f3c.nProp l) d) d f3cRelN = 0 := by
  have z1 := hz.at (l := [0, 0, 1, 0, 1, 0, 1, 0, 0]) (by decide +kernel)
  have z2 := hz.at (l := [0, 0, 1, 1, 0, 0, 1, 0, 0]) (by decide +kernel)
  have z3 := hz.at (l := [0, 0, 1, 1, 1, 0, 0, 0, 0]) (by decide +kernel)
  unfold f3cSymNHolds at hn
  simp only [f3cRelN, LinComb.eval, Poly.eval]
  push_cast
  linear_combination hn + z1 - z2 + z3

/-- **The `f3c` reduction in the Laporta-Remiddi basis, at a given `d`.** If `Q(d) ≠ 0`
(`Q = f3cBridgeQ = q α q₁ qₓ`), then for every family of values `I` satisfying the IBP
relations, the scaleless sectors and the symmetry relations of `f3c` at `d`, the projected
combination `Σ tₗ(d) I(l)` of the `f3c` diagrams equals
`Σⱼ (nⱼ(d) / (q α)(d)) I(LRⱼ) + (n₁(d) / (q α)(d)) I₁` over the LR masters `I₂, …, I₁₈`
(`f3cBridgeLR`) and `I₁` (`f3cLRI1`). -/
theorem f3c_bridge_of_den {K : Type*} [Field K] [CharZero K] (d : K)
    (hd : Poly.eval d f3cBridgeQ ≠ 0) (I : (Fin f3c.nProp → ℤ) → K → K)
    (hI : f3c.IBPHolds I d) (hz : f3c.ZeroSectors I d) (hs : f3cSymsHold I d)
    (hn : f3cSymNHolds I d) :
    (f3cTarget.map fun t => Poly.eval d t.2 * I (toVec f3c.nProp t.1) d).sum =
      (f3cBridgeLR.map fun m =>
        Poly.eval d m.2 / Poly.eval d f3cBridgeDen * I (toVec f3c.nProp m.1) d).sum +
        Poly.eval d f3cBridgeI1 / Poly.eval d f3cBridgeDen * f3cLRI1 I d := by
  set J : List ℤ → K := fun l => I (toVec f3c.nProp l) d with hJ
  simp only [f3cBridgeQ, f3cBridgeDen, Poly.eval_mul, mul_ne_zero_iff] at hd
  obtain ⟨⟨hq, ha⟩, hq1, hqx⟩ := hd
  have hr : ∀ r ∈ f3cBridgeRels, LinComb.eval J d r.1 = 0 := by
    intro r hr
    simp only [f3cBridgeRels, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | rfl | rfl | ⟨⟨⟨σ, ν⟩, μ⟩, hp, rfl⟩
    · exact eval_combo_of_reduction J d _ _ _ hq1 (f3cI1_reduction_of_den d hq1 I hI hz)
    · exact eval_combo_of_reduction J d _ _ _ hqx (f3cX_reduction_of_den d hqx I hI hz)
    · exact f3cRelN_eval hz hn
    · exact symRel_eval (hs _ (List.of_mem_zip hp).1)
  have hc := eval_eq_zero_of_bridgeCheck J d f3cBridge_check hr
  rw [f3cBridgeClaim, LinComb.eval_eq_sum, List.map_append, List.map_append, List.sum_append,
    List.sum_append, ← LinComb.eval_eq_sum, ← LinComb.eval_eq_sum, ← LinComb.eval_eq_sum,
    LinComb.eval_smul, LinComb.eval_smul, f3cI1Target_eval, Poly.eval_neg] at hc
  have hneg : ∀ L : LinComb,
      LinComb.eval J d (L.map fun m => (m.1, Poly.neg m.2)) = -LinComb.eval J d L := by
    intro L
    induction L with
    | nil => simp
    | cons m L ih => simp only [List.map_cons, LinComb.eval_cons, ih, Poly.eval_neg]; ring
  rw [hneg] at hc
  have e1 : (f3cMasters.map fun m =>
      Poly.eval d m.2 / Poly.eval d f3cDen * I (toVec f3c.nProp m.1) d).sum =
      LinComb.eval J d f3cMasters / Poly.eval d f3cDen := sum_map_div_mul J d _ _
  have e2 : (f3cBridgeLR.map fun m =>
      Poly.eval d m.2 / Poly.eval d f3cBridgeDen * I (toVec f3c.nProp m.1) d).sum =
      LinComb.eval J d f3cBridgeLR / Poly.eval d f3cBridgeDen := sum_map_div_mul J d _ _
  rw [f3c_reduction_of_den d hq I hI hz, e1, e2, ← f3cBridgeI1_eq, Poly.eval_smul,
    f3cBridgeDen, Poly.eval_mul]
  field_simp
  linear_combination hc

/-- **The `f3c` reduction in the Laporta-Remiddi basis.** Off a finite set of dimensions `d`,
for every family of values `I` satisfying the IBP relations, the scaleless sectors and the
symmetry relations of `f3c` at `d`, the projected combination of the `f3c` diagrams equals
`Σⱼ (nⱼ(d) / (q α)(d)) I(LRⱼ) + (n₁(d) / (q α)(d)) I₁`. -/
theorem f3c_bridge {K : Type*} [Field K] [CharZero K] :
    ∃ s : Finset K, ∀ d ∉ s, Poly.eval d f3cBridgeQ ≠ 0 ∧
      ∀ I : (Fin f3c.nProp → ℤ) → K → K, f3c.IBPHolds I d → f3c.ZeroSectors I d →
        f3cSymsHold I d → f3cSymNHolds I d →
        (f3cTarget.map fun t => Poly.eval d t.2 * I (toVec f3c.nProp t.1) d).sum =
          (f3cBridgeLR.map fun m =>
            Poly.eval d m.2 / Poly.eval d f3cBridgeDen * I (toVec f3c.nProp m.1) d).sum +
            Poly.eval d f3cBridgeI1 / Poly.eval d f3cBridgeDen * f3cLRI1 I d := by
  obtain ⟨s, hs⟩ := Poly.exists_finset_eval_ne_zero (K := K) f3cBridgeQ_ne_zero
  exact ⟨s, fun d hd => ⟨hs d hd, fun I hI hz hy hn =>
    f3c_bridge_of_den d (hs d hd) I hI hz hy hn⟩⟩

end QED.ThreeLoopE.SetECert
