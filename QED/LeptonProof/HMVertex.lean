/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.LeptonProof.HMSplit

/-!
# The multi-lepton order-`e⁵` vertex through T1's vertices

Helper level, Phase 5 Stage 0 (decision D-50). The order-exactly-`5` part of the flavoured 1PI
function (F₈) is a fixed linear functional `orderFiveSum` of the contraction values (the sum over
the vertex sequences of total order `5` and their 1PI contractions, with `1/N!` and the fermionic
signs), for every flavour data (`onePIFunction₂_five_sub_four_eq`). With the contraction split
of `QED/LeptonProof/HMSplit.lean` this gives, at every `ε > 0`:

* `vertexOrderFive_leptonFlavors_eq`: **the multi-lepton vertex (F₉) is T1's vertex (HV₁) at
  `P` plus `∑_ℓ ∑_j w_{ℓ j}` times T1's vertex at the auxiliary parameter sets of lepton `ℓ`.**
-/

@[expose] public section

open Complex Finset
open QED.WickModel (Params Contraction IsOnePI fermionSign)

namespace QED.Lepton.Proof.HM

open scoped Classical

/-- A function of the contractions with one external fermion pair and one external photon. -/
abbrev ContrFun : Type := (N : ℕ) → (κ : Fin N → Wick.VertexKind) → Contraction 1 1 κ → ℂ

/-- **The order-`e⁵` functional**: the sum over the vertex sequences of total order exactly `5`
and their 1PI contractions, with `1/N!` and the fermionic signs. -/
noncomputable def orderFiveSum (v : ContrFun) : ℂ :=
  ∑ N ∈ range 6, (N.factorial : ℂ)⁻¹ *
    ∑ κ ∈ (univ : Finset (Fin N → Wick.VertexKind)).filter (fun κ => ∑ t, (κ t).order = 5),
      ∑ C ∈ (univ : Finset (Contraction 1 1 κ)).filter IsOnePI,
        ((fermionSign C : ℤ) : ℂ) * v N κ C

theorem orderFiveSum_congr {v v' : ContrFun}
    (h : ∀ N (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order = 5 → ∀ C : Contraction 1 1 κ,
      IsOnePI C → v N κ C = v' N κ C) :
    orderFiveSum v = orderFiveSum v' := by
  unfold orderFiveSum
  refine sum_congr rfl fun N _ => congrArg _ (sum_congr rfl fun κ hκ => sum_congr rfl
    fun C hC => ?_)
  rw [h N κ (mem_filter.mp hκ).2 C (mem_filter.mp hC).2]

theorem orderFiveSum_add (v v' : ContrFun) :
    orderFiveSum (fun N κ C => v N κ C + v' N κ C) = orderFiveSum v + orderFiveSum v' := by
  unfold orderFiveSum
  simp only [mul_add, sum_add_distrib]

theorem orderFiveSum_const_mul (c : ℂ) (v : ContrFun) :
    orderFiveSum (fun N κ C => c * v N κ C) = c * orderFiveSum v := by
  unfold orderFiveSum
  simp only [mul_sum]
  refine sum_congr rfl fun N _ => sum_congr rfl fun κ _ => sum_congr rfl fun C _ => ?_
  ring

theorem orderFiveSum_zero : orderFiveSum (fun _ _ _ => 0) = 0 := by
  simp [orderFiveSum]

theorem orderFiveSum_sum {ι : Type*} (s : Finset ι) (v : ι → ContrFun) :
    orderFiveSum (fun N κ C => ∑ i ∈ s, v i N κ C) = ∑ i ∈ s, orderFiveSum (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using orderFiveSum_zero
  | insert a s ha ih =>
    simp only [sum_insert ha]
    rw [orderFiveSum_add (v a) (fun N κ C => ∑ i ∈ s, v i N κ C), ih]

/-- **The order-exactly-`5` part of (F₈) is `orderFiveSum` of the values**, for every flavour
data. -/
theorem onePIFunction₂_five_sub_four_eq (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    onePIFunction₂ P Φ 1 1 5 pOut pIn kIn αOut βIn μ -
        onePIFunction₂ P Φ 1 1 4 pOut pIn kIn αOut βIn μ =
      orderFiveSum fun _ _ C => contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ := by
  unfold onePIFunction₂ orderFiveSum
  simp only [QED.TwoLoop.Enumeration.sum_filter_le_five, mul_add, sum_add_distrib]
  rw [sum_range_succ _ 5, sum_range_succ (fun N => (N.factorial : ℂ)⁻¹ * ∑ κ ∈
    (univ : Finset (Fin N → Wick.VertexKind)).filter (fun κ => ∑ t, (κ t).order = 5), _) 5,
    QED.TwoLoop.Enumeration.sum_filter_le_four_five]
  ring

variable {n : ℕ} {H : Fin n → HeavyLepton} {X : Fin n → ℝ}

/-- **The flavour-block split of the order-`e⁵` vertex.** At `ε > 0`, with T1's Pauli–Villars
conditions for the electron and admissible auxiliary masses (`AuxOK`, which contains each heavy
lepton's own Pauli–Villars conditions), the multi-lepton vertex (F₉) is T1's vertex (HV₁) at `P`
plus `∑_ℓ ∑_j w_{ℓ j}` times T1's vertex at the auxiliary parameter sets. -/
theorem vertexOrderFive_leptonFlavors_eq (P : Params) (hε : 0 < P.ε)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hok : AuxOK H X P.m) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    vertexOrderFive P (leptonFlavors P H) p' p μ =
      QED.TwoLoop.vertexOrderFive P p' p μ +
        ∑ ℓ, ∑ j, (auxWeight P (H ℓ) (X ℓ) j : ℂ) •
          QED.TwoLoop.vertexOrderFive (auxParams P (H ℓ) (X ℓ) j) p' p μ := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 :=
    (add_sub_cancel p p').symm
  ext a b
  simp only [← vertexOrderFive_t1F, vertexOrderFive, Matrix.of_apply, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [onePIFunction₂_five_sub_four_eq, onePIFunction₂_five_sub_four_eq]
  simp only [onePIFunction₂_five_sub_four_eq]
  rw [orderFiveSum_congr fun N κ hκ C hC => contractionValue₂_leptonFlavors_eq P hε hc₁ hc₂ hok
    hκ C hC hmom _ _ _, orderFiveSum_add, orderFiveSum_sum, mul_add, mul_sum]
  congr 1
  refine sum_congr rfl fun ℓ _ => ?_
  rw [orderFiveSum_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [orderFiveSum_const_mul]
  ring

end QED.Lepton.Proof.HM

end
