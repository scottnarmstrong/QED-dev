/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0OneCtCrit
public import QED.TwoLoop.EnumerationOrderFive

/-!
# (X₀): the one-loop open-line test for the eleven kind sequences

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57). An attached connected
`(1, 1)` contraction with one loop whose vertex orders sum to `5` has three `gauge` or `gaugeCt`
vertices (`two_mul_loopCount_add_eq`), so its kind sequence is one of the eleven sequences `ggC`,
`gCg`, `Cgg`, `gggf`, `ggfg`, `gfgg`, `fggg`, `gggp`, `ggpg`, `gpgg`, `pggg`
(`filter_order_eq_five_*`). For each, every connected contraction whose fermion fields all lie on
the cycle of the external field passes `OneCrit` (kernel evaluation over all fermion pairings and
the listed photon pairings, `decide +kernel`, peak memory about 4.7 GB including the imports).
Hence (`jointEnergyFirstIntegrable_openCt_five`) the open-line part of `OneLoopGoal`.
-/

@[expose] public section

namespace QED.GradedProof.X0

open QED.WickModel (Params Contraction ExternalsAttached VerticesConnected loopCount)
open QED.TwoLoop.Enumeration (withSigmaK mem_withSigmaK IsInvolK lineData reachE
  verticesConnected_iff le_sum_order filter_order_eq_five_zero filter_order_eq_five_one
  filter_order_eq_five_two filter_order_eq_five_three filter_order_eq_five_four
  filter_order_eq_five_five gauges
  k_Cf k_Cp k_fC k_pC k_gff k_gfp k_gpf k_gpp k_fgf k_fgp k_ffg k_fpg k_pgf k_pgp k_pfg k_ppg
  k_ggC invs_ggC_invol invs_ggC_complete k_gCg invs_gCg_invol invs_gCg_complete k_Cgg
  invs_Cgg_invol invs_Cgg_complete k_gggf invs_gggf_invol invs_gggf_complete k_ggfg
  invs_ggfg_invol invs_ggfg_complete k_gfgg invs_gfgg_invol invs_gfgg_complete k_fggg
  invs_fggg_invol invs_fggg_complete k_gggp invs_gggp_invol invs_gggp_complete k_ggpg
  invs_ggpg_invol invs_ggpg_complete k_gpgg invs_gpgg_invol invs_gpgg_complete k_pggg
  invs_pggg_invol invs_pggg_complete invs_ggC invs_gCg invs_Cgg invs_gggf invs_ggfg invs_gfgg
  invs_fggg invs_gggp invs_ggpg invs_gpgg invs_pggg)

/-- The kernel test for one kind sequence. -/
def OneCtCheck {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (invs : List (Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ))) (hinv : ∀ τ ∈ invs, IsInvolK τ) :
    Prop :=
  ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex κ), (∀ x, Equiv.Perm.SameCycle σ x (.inl 0)) →
    ∀ C ∈ withSigmaK invs hinv σ, (∀ (h : 0 < N) (w : Fin N),
      w ∈ reachE (lineData C) (fun _ => true) ⟨0, h⟩ N) → OneCrit (lineData C) κ

theorem oneCrit_of_check {N : ℕ} {κ : Fin N → Wick.VertexKind}
    {invs : List (Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ))} {hinv : ∀ τ ∈ invs, IsInvolK τ}
    (hcomp : ∀ τ, IsInvolK τ → τ ∈ invs) (hchk : OneCtCheck invs hinv) (C : Contraction 1 1 κ)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (hV : VerticesConnected C) :
    OneCrit (lineData C) κ :=
  hchk C.1.1 hcyc C (mem_withSigmaK hinv hcomp C) ((verticesConnected_iff C).mp hV)

theorem oneCtCheck_ggC : OneCtCheck invs_ggC invs_ggC_invol := by
  unfold OneCtCheck
  decide +kernel

theorem oneCtCheck_gCg : OneCtCheck invs_gCg invs_gCg_invol := by
  unfold OneCtCheck
  decide +kernel

theorem oneCtCheck_Cgg : OneCtCheck invs_Cgg invs_Cgg_invol := by
  unfold OneCtCheck
  decide +kernel

theorem oneCtCheck_gggf : OneCtCheck invs_gggf invs_gggf_invol := by
  unfold OneCtCheck
  decide +kernel

theorem oneCtCheck_ggfg : OneCtCheck invs_ggfg invs_ggfg_invol := by
  unfold OneCtCheck
  decide +kernel

theorem oneCtCheck_gfgg : OneCtCheck invs_gfgg invs_gfgg_invol := by
  unfold OneCtCheck
  decide +kernel

theorem oneCtCheck_fggg : OneCtCheck invs_fggg invs_fggg_invol := by
  unfold OneCtCheck
  decide +kernel

theorem oneCtCheck_gggp : OneCtCheck invs_gggp invs_gggp_invol := by
  unfold OneCtCheck
  decide +kernel

theorem oneCtCheck_ggpg : OneCtCheck invs_ggpg invs_ggpg_invol := by
  unfold OneCtCheck
  decide +kernel

theorem oneCtCheck_gpgg : OneCtCheck invs_gpgg invs_gpgg_invol := by
  unfold OneCtCheck
  decide +kernel

theorem oneCtCheck_pggg : OneCtCheck invs_pggg invs_pggg_invol := by
  unfold OneCtCheck
  decide +kernel

/-- **Every one-loop open-line contraction of order `5` passes `OneCrit`.** -/
theorem oneCrit_of_order_five {N : ℕ} (κ : Fin N → Wick.VertexKind) (C : Contraction 1 1 κ)
    (h5 : ∑ t, (κ t).order = 5) (hA : ExternalsAttached C) (hV : VerticesConnected C)
    (hL : loopCount C = 1) (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) :
    OneCrit (lineData C) κ := by
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
    · exact oneCrit_of_check invs_ggC_complete oneCtCheck_ggC C hcyc hV
    · exact oneCrit_of_check invs_gCg_complete oneCtCheck_gCg C hcyc hV
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact oneCrit_of_check invs_Cgg_complete oneCtCheck_Cgg C hcyc hV
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
    · exact oneCrit_of_check invs_gggf_complete oneCtCheck_gggf C hcyc hV
    · exact oneCrit_of_check invs_gggp_complete oneCtCheck_gggp C hcyc hV
    · exact oneCrit_of_check invs_ggfg_complete oneCtCheck_ggfg C hcyc hV
    · exact oneCrit_of_check invs_ggpg_complete oneCtCheck_ggpg C hcyc hV
    · exact oneCrit_of_check invs_gfgg_complete oneCtCheck_gfgg C hcyc hV
    · exact oneCrit_of_check invs_gpgg_complete oneCtCheck_gpgg C hcyc hV
    · exact oneCrit_of_check invs_fggg_complete oneCtCheck_fggg C hcyc hV
    · exact oneCrit_of_check invs_pggg_complete oneCtCheck_pggg C hcyc hV
  · rw [filter_order_eq_five_five] at hmem
    rw [Finset.mem_singleton.mp hmem] at h3
    exact absurd h3 (by decide)

/-- **(X₀), open-line part of `OneLoopGoal`.** -/
theorem jointEnergyFirstIntegrable_openCt_five (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : QED.Graded.Counterterms F) (hε : 0 < P.ε)
    {N : ℕ} (κ : Fin N → Wick.VertexKind) (C : Contraction 1 1 κ) (h5 : ∑ t, (κ t).order = 5)
    (hA : ExternalsAttached C) (hV : VerticesConnected C) (hL : loopCount C = 1)
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C)
      (integrand P Φ D C 0 pOut pIn kIn αOut βIn μ) :=
  jointEnergyFirstIntegrable_openCt P Φ D hε C hcyc hL
    (oneCrit_of_order_five κ C h5 hA hV hL hcyc) pOut pIn kIn αOut βIn μ

end QED.GradedProof.X0

end
