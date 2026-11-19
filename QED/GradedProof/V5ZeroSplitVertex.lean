/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.V5ZeroSplit
public import QED.LeptonProof.HMVertex

/-!
# The general-flavour order-`e⁵` vertex through T1 parameter sets

Helper level for the Phase 5 Stage 2 goal (G-ex₂), the `V5Zero` effort. With the parameter sets
and weights of `QED/GradedProof/V5ZeroSplit.lean`, at every `ε > 0`, for flavour data `Φ` with
`Q.m = Φ.mass Φ.openLine` and the total Pauli–Villars conditions:

* `contractionValue₂_split`: the value of every order-`e⁵` 1PI contraction splits;
* `vertexOrderFive_split`: **the order-`e⁵` vertex (F₉) is T1's vertex (HV₁) at `zParams Q X`
  plus `∑_g w_g` times T1's vertex at `gParams Q Φ X g`.**

The proof follows the Stage 0 heavy-lepton split (`QED/LeptonProof/HMSplit.lean`,
`QED/LeptonProof/HMVertex.lean`): the integrands split pointwise, each T1 integrand is integrable
(the sealed (HV₀)), and the order-`5` part of (F₈) is the fixed functional `orderFiveSum` of the
contraction values.
-/

@[expose] public section

open Complex Finset
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂)
open QED.Lepton.Proof.HM (t1F vertexOrderFive_t1F jointIntegrable_t1F jointIntegrable_const_mul
  jointIntegrable_sum jointIntegral_add jointIntegral_sum jointIntegral_const_mul
  isSimple_of_orderFive orderFiveSum_congr orderFiveSum_add orderFiveSum_sum
  orderFiveSum_const_mul onePIFunction₂_five_sub_four_eq)

namespace QED.GradedProof.V5Zero.Split

variable {F : Type} [Fintype F] [DecidableEq F] {Q : Params} {Φ : Lepton.Flavors F} {X : ℝ}

/-- **The value of an order-`e⁵` 1PI contraction splits** into the T1 values at `zParams` and
the `gParams g`. -/
theorem contractionValue₂_split (hε : 0 < Q.ε) (hm : Q.m = Φ.mass Φ.openLine)
    (h₁ : ∑ g, Φ.coeff g = 0) (h₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0)
    (hXm : X ^ 2 ≠ Q.m ^ 2) (hX : ∀ g, Φ.mass g ^ 2 ≠ X ^ 2)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (hκ : ∑ t, (κ t).order = 5)
    (C : Contraction 1 1 κ) (hC : IsOnePI C) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    Lepton.contractionValue₂ Q Φ C pOut pIn kIn αOut βIn μ =
      Lepton.contractionValue₂ (zParams Q X) (t1F (zParams Q X)) C pOut pIn kIn αOut βIn μ +
        ∑ g, (weight Q Φ X g : ℂ) *
          Lepton.contractionValue₂ (gParams Q Φ X g) (t1F (gParams Q Φ X g)) C
            pOut pIn kIn αOut βIn μ := by
  have hS := isSimple_of_orderFive hκ C hC
  unfold Lepton.contractionValue₂
  set c : ℂ := (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹
  have hZ := jointIntegrable_t1F (zParams Q X) hε (zParams_PV₁ Q X) (zParams_PV₂ Q X) hκ C hC
    hmom αOut βIn μ
  have hQ : ∀ g, QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun x =>
      (weight Q Φ X g : ℂ) * (c * Lepton.regulatedAmplitude₂ (gParams Q Φ X g)
        (t1F (gParams Q Φ X g)) C pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ) :=
    fun g => jointIntegrable_const_mul _ (jointIntegrable_t1F (gParams Q Φ X g) hε
      (gParams_PV₁ Q Φ X g) (gParams_PV₂ Q Φ X g (hX g)) hκ C hC hmom αOut βIn μ)
  have e : (fun x : Fin (loopCount C) → Fin 4 → ℝ => c * Lepton.regulatedAmplitude₂ Q Φ C pIn
      kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ) = fun x =>
      c * Lepton.regulatedAmplitude₂ (zParams Q X) (t1F (zParams Q X)) C pIn kIn
          (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ +
        ∑ g, (weight Q Φ X g : ℂ) * (c * Lepton.regulatedAmplitude₂ (gParams Q Φ X g)
          (t1F (gParams Q Φ X g)) C pIn kIn (lineMomentum₂ C pOut pIn kIn x) αOut βIn μ) := by
    funext x
    rw [regulatedAmplitude₂_split hm h₁ h₂ hXm hX hS, mul_add, mul_sum]
    congr 1
    refine sum_congr rfl fun g _ => ?_
    ring
  rw [e, jointIntegral_add hZ (jointIntegrable_sum _ fun g _ => hQ g),
    jointIntegral_sum _ fun g _ => hQ g]
  congr 1
  refine sum_congr rfl fun g _ => ?_
  rw [jointIntegral_const_mul]

/-- **The general-flavour order-`e⁵` vertex through T1 parameter sets.** At `ε > 0`, with
`Q.m = Φ.mass Φ.openLine`, the total Pauli–Villars conditions of `Φ`, `X² ≠ m²` and
`M_g² ≠ X²`, the vertex (F₉) is T1's vertex (HV₁) at `zParams Q X` plus `∑_g w_g` times T1's
vertex at `gParams Q Φ X g`. -/
theorem vertexOrderFive_split (hε : 0 < Q.ε) (hm : Q.m = Φ.mass Φ.openLine)
    (h₁ : ∑ g, Φ.coeff g = 0) (h₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0)
    (hXm : X ^ 2 ≠ Q.m ^ 2) (hX : ∀ g, Φ.mass g ^ 2 ≠ X ^ 2) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Lepton.vertexOrderFive Q Φ p' p μ =
      QED.TwoLoop.vertexOrderFive (zParams Q X) p' p μ +
        ∑ g, (weight Q Φ X g : ℂ) • QED.TwoLoop.vertexOrderFive (gParams Q Φ X g) p' p μ := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 :=
    (add_sub_cancel p p').symm
  ext a b
  simp only [← vertexOrderFive_t1F, Lepton.vertexOrderFive, Matrix.of_apply, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, onePIFunction₂_five_sub_four_eq]
  rw [orderFiveSum_congr fun N κ hκ C hC => contractionValue₂_split hε hm h₁ h₂ hXm hX
    hκ C hC hmom _ _ _, orderFiveSum_add, orderFiveSum_sum, mul_add, mul_sum]
  congr 1
  refine sum_congr rfl fun g _ => ?_
  rw [orderFiveSum_const_mul]
  ring

end QED.GradedProof.V5Zero.Split

end
