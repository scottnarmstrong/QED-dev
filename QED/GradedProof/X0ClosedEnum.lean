/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0ClosedOne
public import QED.GradedProof.X0OneCtEnum

/-!
# (X₀): the one-loop closed-loop test for the eleven kind sequences, and `OneLoopGoal`

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57). For a `(1, 1)`
contraction let `zOf C` be the fermion vertices off the cycle of the external field. `ClosedCrit`
asks that `zOf C` is one cycle, that the loop momentum runs exactly through its fermion lines, and
the counts `d ≤ 4`, `d < 2 r` of `jointEnergyFirstIntegrable_closedOne`. For each of the eleven
kind sequences of `OneLoopGoal`, every attached connected contraction with a fermion field off the
external cycle passes `ClosedCrit` (kernel evaluation, `decide +kernel`). With the open-line part
(`jointEnergyFirstIntegrable_openCt_five`) this proves `OneLoopGoal` under the block hypotheses
of (X₀) (`oneLoopGoal`).
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.WickModel (Params Contraction ExternalsAttached VerticesConnected loopCount FermionLine
  PhotonLine Line)
open QED.TwoLoop.Enumeration (withSigmaK mem_withSigmaK IsInvolK lineData reachE
  verticesConnected_iff le_sum_order filter_order_eq_five_one filter_order_eq_five_two
  filter_order_eq_five_three filter_order_eq_five_four filter_order_eq_five_five
  k_ggC invs_ggC_invol invs_ggC_complete k_gCg invs_gCg_invol invs_gCg_complete k_Cgg
  invs_Cgg_invol invs_Cgg_complete k_gggf invs_gggf_invol invs_gggf_complete k_ggfg
  invs_ggfg_invol invs_ggfg_complete k_gfgg invs_gfgg_invol invs_gfgg_complete k_fggg
  invs_fggg_invol invs_fggg_complete k_gggp invs_gggp_invol invs_gggp_complete k_ggpg
  invs_ggpg_invol invs_ggpg_complete k_gpgg invs_gpgg_invol invs_gpgg_complete k_pggg
  invs_pggg_invol invs_pggg_complete invs_ggC invs_gCg invs_Cgg invs_gggf invs_ggfg invs_gfgg
  invs_fggg invs_gggp invs_ggpg invs_gpgg invs_pggg)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The fermion vertices off the cycle of the external field. -/
def zOf (C : Contraction 1 nA κ) (s : Wick.FermionVertex κ) : Prop :=
  ¬ C.1.1.SameCycle (.inr s) (.inl 0)

instance (C : Contraction 1 nA κ) : DecidablePred (zOf C) := fun _ => by
  unfold zOf; infer_instance

theorem isZ_zOf (C : Contraction 1 nA κ) (x : Fin 1 ⊕ Wick.FermionVertex κ) :
    isZ (zOf C) x = !decide (C.1.1.SameCycle x (.inl 0)) := by
  rcases x with i | s
  · obtain rfl := Subsingleton.elim i 0
    simp [isZ, Equiv.Perm.SameCycle.refl]
  · simp [isZ, zOf]

theorem isZ_zOf_apply (C : Contraction 1 nA κ) (x : Fin 1 ⊕ Wick.FermionVertex κ) :
    isZ (zOf C) (C.1.1 x) = isZ (zOf C) x := by
  rw [isZ_zOf, isZ_zOf]
  exact congrArg (!·) (decide_eq_decide.mpr Equiv.Perm.sameCycle_apply_left)

/-- **The closed one-loop test.** -/
def ClosedCrit (C : Contraction 1 1 κ) : Prop :=
  (∃ t₀, zOf C t₀ ∧ ∀ t, zOf C t → C.1.1.SameCycle (.inr t) (.inr t₀)) ∧
  (∀ f : FermionLine C, QED.GradedProof.X0.loopCoeff C (.inl f) 0 ≠ 0 ↔ zOf C f.1) ∧
  (∀ g : PhotonLine C, QED.GradedProof.X0.loopCoeff C (.inr g) 0 = 0) ∧
  Fintype.card (ZLine C (zOf C)) +
      ∑ s : {s // zOf C s}, vDeg (fun l => QED.GradedProof.X0.loopCoeff C l 0) s.1.1 ≤ 4 ∧
  Fintype.card (ZLine C (zOf C)) +
      ∑ s : {s // zOf C s}, vDeg (fun l => QED.GradedProof.X0.loopCoeff C l 0) s.1.1 <
    2 * Fintype.card (ZLine C (zOf C))

instance (C : Contraction 1 1 κ) : Decidable (ClosedCrit C) := by
  unfold ClosedCrit; infer_instance

/-- The kernel test for one kind sequence and one fermion pairing. -/
def ClosedCheckσ (invs : List (Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ)))
    (hinv : ∀ τ ∈ invs, IsInvolK τ) (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex κ)) : Prop :=
  ∀ C ∈ withSigmaK invs hinv σ, C.1.2 (.inl 0) ≠ .inl 0 →
    (∀ (h : 0 < N) (w : Fin N), w ∈ reachE (lineData C) (fun _ => true) ⟨0, h⟩ N) →
      ClosedCrit C

instance (invs : List (Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ)))
    (hinv : ∀ τ ∈ invs, IsInvolK τ) (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex κ)) :
    Decidable (ClosedCheckσ invs hinv σ) := by
  unfold ClosedCheckσ; infer_instance

/-- The kernel test for one kind sequence. -/
def ClosedCheck (invs : List (Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ)))
    (hinv : ∀ τ ∈ invs, IsInvolK τ) : Prop :=
  ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex κ), ¬ (∀ x, Equiv.Perm.SameCycle σ x (.inl 0)) →
    σ (.inl 0) ≠ .inl 0 → ClosedCheckσ invs hinv σ

instance (invs : List (Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ)))
    (hinv : ∀ τ ∈ invs, IsInvolK τ) : Decidable (ClosedCheck invs hinv) := by
  unfold ClosedCheck; infer_instance

theorem closedCrit_of_check {invs : List (Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ))}
    {hinv : ∀ τ ∈ invs, IsInvolK τ} (hcomp : ∀ τ, IsInvolK τ → τ ∈ invs)
    (hchk : ClosedCheck invs hinv) (C : Contraction 1 1 κ) (hA : ExternalsAttached C)
    (hcyc : ¬ ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (hV : VerticesConnected C) :
    ClosedCrit C :=
  hchk C.1.1 hcyc (hA.1 0 0) C (mem_withSigmaK hinv hcomp C) (hA.2 0 0)
    ((verticesConnected_iff C).mp hV)

theorem closedCheck_ggC : ClosedCheck invs_ggC invs_ggC_invol := by
  decide +kernel

theorem closedCheck_gCg : ClosedCheck invs_gCg invs_gCg_invol := by
  decide +kernel

theorem closedCheck_Cgg : ClosedCheck invs_Cgg invs_Cgg_invol := by
  decide +kernel

theorem closedCheck_gggf : ClosedCheck invs_gggf invs_gggf_invol := by
  decide +kernel

theorem closedCheck_ggfg : ClosedCheck invs_ggfg invs_ggfg_invol := by
  decide +kernel

theorem closedCheck_gfgg : ClosedCheck invs_gfgg invs_gfgg_invol := by
  decide +kernel

theorem closedCheck_fggg : ClosedCheck invs_fggg invs_fggg_invol := by
  decide +kernel

theorem closedCheck_gggp : ClosedCheck invs_gggp invs_gggp_invol := by
  decide +kernel

theorem closedCheck_ggpg : ClosedCheck invs_ggpg invs_ggpg_invol := by
  decide +kernel

theorem closedCheck_gpgg : ClosedCheck invs_gpgg invs_gpgg_invol := by
  decide +kernel

theorem closedCheck_pggg : ClosedCheck invs_pggg invs_pggg_invol := by
  decide +kernel

/-- **Every one-loop contraction of order `5` with a closed fermion loop passes
`ClosedCrit`.** -/
theorem closedCrit_of_order_five {N : ℕ} (κ : Fin N → Wick.VertexKind) (C : Contraction 1 1 κ)
    (h5 : ∑ t, (κ t).order = 5) (hA : ExternalsAttached C) (hV : VerticesConnected C)
    (hL : loopCount C = 1) (hcyc : ¬ ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) :
    ClosedCrit C := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp at h5
    · exact h
  have h3 := QED.TwoLoop.LoopBoundTwo.two_mul_loopCount_add_eq hA hV hN
  rw [hL] at h3
  have hle := le_sum_order κ
  have hmem : κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 5) := Finset.mem_filter.2 ⟨Finset.mem_univ _, h5⟩
  obtain rfl | rfl | rfl | rfl | rfl : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 := by omega
  · rw [filter_order_eq_five_one] at hmem
    simp at hmem
  · rw [filter_order_eq_five_two] at hmem
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
  · rw [filter_order_eq_five_three] at hmem
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact closedCrit_of_check invs_ggC_complete closedCheck_ggC C hA hcyc hV
    · exact closedCrit_of_check invs_gCg_complete closedCheck_gCg C hA hcyc hV
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact closedCrit_of_check invs_Cgg_complete closedCheck_Cgg C hA hcyc hV
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
  · rw [filter_order_eq_five_four] at hmem
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact closedCrit_of_check invs_gggf_complete closedCheck_gggf C hA hcyc hV
    · exact closedCrit_of_check invs_gggp_complete closedCheck_gggp C hA hcyc hV
    · exact closedCrit_of_check invs_ggfg_complete closedCheck_ggfg C hA hcyc hV
    · exact closedCrit_of_check invs_ggpg_complete closedCheck_ggpg C hA hcyc hV
    · exact closedCrit_of_check invs_gfgg_complete closedCheck_gfgg C hA hcyc hV
    · exact closedCrit_of_check invs_gpgg_complete closedCheck_gpgg C hA hcyc hV
    · exact closedCrit_of_check invs_fggg_complete closedCheck_fggg C hA hcyc hV
    · exact closedCrit_of_check invs_pggg_complete closedCheck_pggg C hA hcyc hV
  · rw [filter_order_eq_five_five] at hmem
    rw [Finset.mem_singleton.mp hmem] at h3
    exact absurd h3 (by decide)

/-- **`OneLoopGoal` under the block hypotheses of (X₀).** -/
theorem oneLoopGoal (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : QED.Graded.Counterterms F) (rep : F → F) (hε : 0 < P.ε)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0) :
    OneLoopGoal P Φ D := by
  intro N κ C h5 hA hV hL pOut pIn kIn _ αOut βIn μ
  by_cases hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)
  · exact jointEnergyFirstIntegrable_openCt_five P Φ D hε κ C h5 hA hV hL hcyc pOut pIn kIn αOut
      βIn μ
  obtain ⟨h1, h2, h3, h4, h5'⟩ := closedCrit_of_order_five κ C h5 hA hV hL hcyc
  have hC : ClosedShape C (zOf C) :=
    ⟨isZ_zOf_apply C, fun t ht => not_not.mp ht, h1⟩
  exact jointEnergyFirstIntegrable_closedOne P Φ D rep hrep hPV₁ hPV₂ hD hε C hC hL h2 h3 h4 h5'
    pOut pIn kIn αOut βIn μ

end QED.GradedProof.X0

end
