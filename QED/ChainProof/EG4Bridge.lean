/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.FamilyVertex
public import QED.Frozen.VPChain.VertexChain
public import QED.GradedProof.Embed
public import QED.ChainProof.QuickOrder

/-!
# The graded set (b) vertex is the chain vertex

Helper proof of the D-58 goal (E-G₄) `QED.Graded.familyVertex_isVPChain_two`, as
`QED.ChainProof.EG4.familyVertex_isVPChain_two'`.

A chain contraction (C₁) with two insertions has only `gauge` and `photonCt` vertices
(`kind_of_isVPChain`) and total order (V₁) `7` (`QED.ChainProof.Quick.order_sum_of_isVPChain`).
So at graded order `7` its grading is zero: no counterterm of level `≥ 1` enters. The graded
order part (G₆) is then the sum over the vertex sequences of order `7` at the zero grading
(`QED.GradedProof.selectedPart_eq_sum_order`), with the same `1/N!` and fermionic signs as the
family function (C₂). Every fermion vertex is a `gauge` vertex, so the graded value (G₅) at the
zero grading is the value (F₇) with the parameters `P`, once the level-`0` photon counterterm
`e² d₃ 0` is `δ₃` (`QED.GradedProof.contractionValue_zero_eq`).
-/

@[expose] public section

open QED.WickModel (Params Contraction IsOnePI)
open QED.Graded

namespace QED.ChainProof.EG4

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- Every vertex of a chain is a `gauge` or a `photonCt` vertex. -/
theorem kind_of_isVPChain {n : ℕ} {C : Contraction 1 1 κ} (h : QED.VPChain.IsVPChain n C)
    (t : Fin N) : κ t = .gauge ∨ κ t = .photonCt := by
  obtain ⟨a, b, c, sb, src, dst, ha, hb, hc, -, -, -, -, -, -, -, -, -, hins, hall⟩ := h
  rcases hall t with rfl | rfl | rfl | ⟨i, rfl | rfl⟩
  · exact Or.inl ha
  · exact Or.inl hb
  · exact Or.inl hc
  · rcases hins i with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · rcases hins i with ⟨-, h2, -⟩ | ⟨h1, h2, -⟩
    · exact Or.inl h2
    · rw [h2]
      exact Or.inr h1

/-- A chain grading of graded order `2n + 3` is zero. -/
theorem grading_eq_zero_of_isVPChain {n : ℕ} {C : Contraction 1 1 κ}
    (h : QED.VPChain.IsVPChain n C) {g : Grading κ} (hg : gradedOrder κ g = 2 * n + 3) :
    g = 0 := by
  have ho := QED.ChainProof.Quick.order_sum_of_isVPChain h
  unfold gradedOrder at hg
  have hs : ∑ t : CtVertex κ, 2 * g t = 0 := by omega
  funext t
  have := (Finset.sum_eq_zero_iff.1 hs) t (Finset.mem_univ _)
  simp only [Pi.zero_apply]
  omega

open scoped Classical in
/-- **(E-G₄)** The family vertex (Gf₁) of the 1PI two-insertion chains at order `7` is the chain
vertex (C₃) at `n = 2`, when the level-`0` photon counterterm is `δ₃ / e²`. -/
theorem familyVertex_isVPChain_two' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (h₃ : P.δ₃ = P.e ^ 2 * D.d₃ 0)
    (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    familyVertex P Φ D (fun C _ => IsOnePI C ∧ VPChain.IsVPChain 2 C) 7 p' p μ =
      VPChain.vertexChain 2 P Φ p' p μ := by
  ext i j
  simp only [familyVertex, VPChain.vertexChain, Matrix.of_apply, Nat.reduceMul, Nat.reduceAdd]
  refine congrArg (fun x => 1 / Complex.I * x) ?_
  rw [QED.GradedProof.selectedPart_eq_sum_order P Φ D 1 1
    (fun C => IsOnePI C ∧ VPChain.IsVPChain 2 C) 7 _ _ _ _ _ _
    fun g hg hne C hC => absurd (grading_eq_zero_of_isVPChain hC.2 hg) hne]
  unfold Lepton.onePIFamilyFunction₂
  refine Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ _ => ?_)
  split_ifs with hK
  · refine Finset.sum_congr (by ext; simp) fun C hC => ?_
    have hCh := (Finset.mem_filter.1 hC).2.2
    have hk := kind_of_isVPChain hCh
    refine congrArg _ (QED.GradedProof.contractionValue_zero_eq P P Φ D C
      (fun t ht => absurd ((hk t.1).resolve_right t.2) ht) rfl rfl rfl rfl
      (fun t h => by rcases hk t with h' | h' <;> rw [h'] at h <;> cases h)
      (fun t h => by rcases hk t with h' | h' <;> rw [h'] at h <;> cases h)
      (fun _ _ => h₃) _ _ _ _ _ _)
  · refine (Finset.sum_eq_zero fun C hC => ?_).symm
    exact absurd (QED.ChainProof.Quick.order_sum_of_isVPChain (Finset.mem_filter.1 hC).2.2) hK

end QED.ChainProof.EG4

end
