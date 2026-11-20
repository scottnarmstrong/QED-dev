/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Classes

/-!
# The order-`e⁴` self-energy with coefficient one per class

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57). At
every T1 parameter set `S`, the order-exactly-`4` sum of the 1PI one-fermion contractions,
`∑_{N ≤ 4} (1/N!) ∑_κ ∑_C sign(C) · value(C)`, is the signed sum of the eight class values
`R + X - V + F + P0 + P1 + C1 + C2` (`sum_order_four_eq_seClassSum`): the lists of
`QED/GradedProof/SE2Classes.lean` are relabellings of the representatives, the value and the
sign are relabelling invariant, and the multiplicities are `N!`.
-/

@[expose] public section

namespace QED.GradedProof.WI2

open QED.WickModel QED.GradedProof.SE2 QED.TwoLoop.Relabel

/-- **The signed class sum of the T1 order-`4` self-energy** at `(p, p)`. -/
noncomputable def seClassSum (S : Params) (p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  contractionValue₂ S repR ![p] ![p] ![] ![α] ![β] ![] +
    contractionValue₂ S repX ![p] ![p] ![] ![α] ![β] ![] -
    contractionValue₂ S repV ![p] ![p] ![] ![α] ![β] ![] +
    contractionValue₂ S repF ![p] ![p] ![] ![α] ![β] ![] +
    contractionValue₂ S repP0 ![p] ![p] ![] ![α] ![β] ![] +
    contractionValue₂ S repP1 ![p] ![p] ![] ![α] ![β] ![] +
    contractionValue₂ S repC1 ![p] ![p] ![] ![α] ![β] ![] +
    contractionValue₂ S repC2 ![p] ![p] ![] ![α] ![β] ![]

section Sum

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The signed sum over the 1PI contractions of `κ` as a list sum. -/
theorem sum_isOnePI_eq_list {instF : Fintype (Contraction 1 0 κ)}
    {instD : DecidablePred (IsOnePI (nf := 1) (nA := 0) (κ := κ))}
    (L : List (Contraction 1 0 κ)) (hL : L.Nodup) (hs : ∀ C, IsOnePI C ↔ C ∈ L)
    (G : Contraction 1 0 κ → ℂ) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 1 0 κ)).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) * G C = (L.map fun C => ((fermionSign C : ℤ) : ℂ) * G C).sum := by
  classical
  have hs' : (Finset.univ : Finset (Contraction 1 0 κ)).filter IsOnePI = L.toFinset :=
    Finset.ext fun C => by simp [hs]
  rw [hs', List.sum_toFinset _ hL]

end Sum

theorem nodup_kinds_two : ([k_gC, k_Cg, k_ff, k_fp, k_pf, k_pp] :
    List (Fin 2 → Wick.VertexKind)).Nodup := by decide +kernel

theorem nodup_kinds_three : ([k_ggf, k_ggp, k_gfg, k_gpg, k_fgg, k_pgg] :
    List (Fin 3 → Wick.VertexKind)).Nodup := by decide +kernel

/-- **The order-`4` T1 self-energy with coefficient one per class.** -/
theorem sum_order_four_eq_seClassSum
    {instD : ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind),
      DecidablePred (IsOnePI (nf := 1) (nA := 0) (κ := κ))}
    (S : Params) (p : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ N ∈ Finset.range (4 + 1), (N.factorial : ℂ)⁻¹ *
      ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
          (fun κ => ∑ t, (κ t).order = 4),
        ∑ C ∈ @Finset.filter (Contraction 1 0 κ) (fun C => IsOnePI C) (instD N κ) Finset.univ,
          ((fermionSign C : ℤ) : ℂ) * contractionValue₂ S C ![p] ![p] ![] ![α] ![β] ![] =
      seClassSum S p α β := by
  obtain rfl : instD = fun N κ => Classical.decPred _ := Subsingleton.elim _ _
  have hmom : ∑ i, (![p] : Fin 1 → Fin 4 → ℝ) i =
      ∑ i, (![p] : Fin 1 → Fin 4 → ℝ) i + ∑ j, (![] : Fin 0 → Fin 4 → ℝ) j := by simp
  have hinv : ∀ {N : ℕ} {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
      (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 1 0 κ), IsOnePI C →
      ((fermionSign (relabelK π hκ C) : ℤ) : ℂ) *
          contractionValue₂ S (relabelK π hκ C) ![p] ![p] ![] ![α] ![β] ![] =
        ((fermionSign C : ℤ) : ℂ) * contractionValue₂ S C ![p] ![p] ![] ![α] ![β] ![] :=
    fun π hκ C hC => by
      rw [fermionSign_relabelK, contractionValue₂_relabelK_of_isOnePI S π hκ hC hmom]
  obtain ⟨sR, sX, sV, sF, sP0, sP1, sC1, sC2⟩ := fermionSign_reps
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, filter_order_eq_four_zero,
    filter_order_eq_four_one, filter_order_eq_four_two, filter_order_eq_four_three,
    filter_order_eq_four_four, Finset.sum_empty, Finset.sum_singleton,
    List.sum_toFinset _ nodup_kinds_two, List.sum_toFinset _ nodup_kinds_three,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [sum_isOnePI_eq_list _ onePI_gC_nodup isOnePI_iff_gC,
    sum_isOnePI_eq_list _ onePI_Cg_nodup isOnePI_iff_Cg,
    sum_isOnePI_eq_list _ onePI_ff_nodup isOnePI_iff_ff,
    sum_isOnePI_eq_list _ onePI_fp_nodup isOnePI_iff_fp,
    sum_isOnePI_eq_list _ onePI_pf_nodup isOnePI_iff_pf,
    sum_isOnePI_eq_list _ onePI_pp_nodup isOnePI_iff_pp,
    sum_isOnePI_eq_list _ onePI_ggf_nodup isOnePI_iff_ggf,
    sum_isOnePI_eq_list _ onePI_ggp_nodup isOnePI_iff_ggp,
    sum_isOnePI_eq_list _ onePI_gfg_nodup isOnePI_iff_gfg,
    sum_isOnePI_eq_list _ onePI_gpg_nodup isOnePI_iff_gpg,
    sum_isOnePI_eq_list _ onePI_fgg_nodup isOnePI_iff_fgg,
    sum_isOnePI_eq_list _ onePI_pgg_nodup isOnePI_iff_pgg,
    sum_isOnePI_eq_list _ onePI_gggg_nodup isOnePI_iff_gggg,
    ← List.take_append_drop 36 onePI_gggg, onePI_gggg_take_eq_relabelK,
    onePI_gggg_drop_eq_relabelK, onePI_gC_eq_relabelK, onePI_Cg_eq_relabelK,
    onePI_ggf_eq_relabelK, onePI_ggp_eq_relabelK, onePI_gfg_eq_relabelK, onePI_gpg_eq_relabelK,
    onePI_fgg_eq_relabelK, onePI_pgg_eq_relabelK]
  simp only [onePI_ff, onePI_fp, onePI_pf, onePI_pp, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.cons_append, List.nil_append, hinv _ _ _ repR_isOnePI,
    hinv _ _ _ repX_isOnePI, hinv _ _ _ repV_isOnePI, hinv _ _ _ repF_isOnePI,
    hinv _ _ _ repP0_isOnePI, hinv _ _ _ repP1_isOnePI, hinv _ _ _ repC1_isOnePI,
    hinv _ _ _ repC2_isOnePI, sR, sX, sV, sF, sP0, sP1, sC1, sC2]
  simp only [seClassSum, Nat.factorial]
  push_cast
  ring

end QED.GradedProof.WI2

end
