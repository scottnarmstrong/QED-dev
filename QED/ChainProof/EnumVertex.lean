/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.EnumSum
public import QED.Frozen.VPChain.VertexChain
public import QED.ChainProof.EnumLeptonRelabel

/-!
# The set (b) chain vertex as the signed sum of nine class values

Helper for obligation O3-4 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53), the analogue of
`QED.TwoLoop.Relabel.onePIFunction₂_five_sub_four_eq_all_classes` at two loops.

* `QED.ChainProof.Enum.sum_chain`: the structural count. For every `G` invariant under
  relabelling 1PI contractions, the sum over the kind sequences of `N` vertices of total order at
  most `7` and their 1PI set (b) contractions of `fermionSign C * G C` is `N!` times the signed sum
  of `G` over the representatives with `N` vertices: each class has `N!` members.
* `QED.ChainProof.Enum.vertexChain_two_eq_classes_flavors`: at any flavour data `Φ`, with incoming
  photon momentum `p' - p`, the chain vertex (C₃) `vertexChain 2` is `(1/i)` times the signed sum
  of the values (F₇) of the nine representatives, each with coefficient one: `+` bubble–bubble,
  `-` the two bubble–`δ₃` and the two `δ₃`–bubble, `+` the four `δ₃`–`δ₃`. The `1/N!` is
  cancelled by the `N!` relabellings, which have the same value
  (`QED.ChainProof.Enum.contractionValue₂_relabelK_of_isOnePI_lepton`).
* `QED.ChainProof.Enum.vertexChain_two_eq_classes`: the same at T1's flavours
  `⟨P.mass, P.loopCoeff, 0⟩` (the flavours of the headline (HC₃)), with T1's values (T₁₀); the
  value at T1's flavours is T1's value by `rfl` (the statement of (M₃)).
* `QED.ChainProof.Enum.isOnePI_of_isVPChain_two`, `order_of_isVPChain_two`,
  `loopCount_of_isVPChain_two`, `fermionSign_of_isVPChain_two`: the implications noted in the
  docstring of (C₁) at `n = 2`: one-particle irreducibility, total order `7`, `1 + #bubbles` loops
  and sign `(-1)^#bubbles`, where `#bubbles = 2 - #photonCt`.
-/

@[expose] public section

namespace QED.ChainProof.Enum

open Complex QED.WickModel QED.TwoLoop.Relabel

variable {N : ℕ}

/-! ### The count -/

/-- **Each class has `N!` members** (obligation O3-4). For every function `G` of the contractions
with `N` vertices invariant under relabelling 1PI contractions across kind sequences, the sum
over the kind sequences of total order at most `7` and over their 1PI set (b) chain contractions
of `fermionSign C * G C` is `N!` times the signed sum of `G` over the representatives with `N`
vertices. The instances are arbitrary (in particular the classical ones of (C₂)). -/
theorem sum_chain {instF : ∀ κ : Fin N → Wick.VertexKind, Fintype (Contraction 1 1 κ)}
    {instK : DecidablePred fun κ : Fin N → Wick.VertexKind => ∑ t, (κ t).order ≤ 7}
    {instC : ∀ κ : Fin N → Wick.VertexKind,
      DecidablePred fun C : Contraction 1 1 κ => IsOnePI C ∧ QED.VPChain.IsVPChain 2 C}
    (G : ∀ {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → ℂ)
    (hG : ∀ {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
      (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 1 1 κ), IsOnePI C → G (relabelK π hκ C) = G C) :
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ 7),
      ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter
          (fun C => IsOnePI C ∧ QED.VPChain.IsVPChain 2 C),
        ((fermionSign C : ℤ) : ℂ) * G C =
      (N.factorial : ℂ) * ∑ i : Fin (repsOf N).length,
        ((fermionSign ((repsOf N).get i).rep : ℤ) : ℂ) * G ((repsOf N).get i).rep := by
  set R : Fin (repsOf N).length → Rep N := fun i => (repsOf N).get i with hRdef
  have hR : ∀ i, R i ∈ repsOf N := fun i => List.get_mem _ _
  set g : Fin (repsOf N).length × Equiv.Perm (Fin N) → (Fin N → Wick.VertexKind) :=
    fun p => (R p.1).kinds ∘ p.2.symm with hg
  set F : Fin (repsOf N).length × Equiv.Perm (Fin N) → ℂ :=
    fun p => ((fermionSign (R p.1).rep : ℤ) : ℂ) * G (R p.1).rep with hF
  have hκ_of : ∀ {κ : Fin N → Wick.VertexKind} {p}, g p = κ → ∀ t, κ (p.2 t) = (R p.1).kinds t :=
    fun {κ} {p} hp t => by rw [← hp]; simp [hg]
  have inner : ∀ κ : Fin N → Wick.VertexKind,
      ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter
          (fun C => IsOnePI C ∧ QED.VPChain.IsVPChain 2 C), ((fermionSign C : ℤ) : ℂ) * G C =
        ∑ p ∈ (Finset.univ : Finset (Fin (repsOf N).length × Equiv.Perm (Fin N))).filter
          (fun p => g p = κ), F p := by
    intro κ
    symm
    refine Finset.sum_bij
      (fun p hp => relabelK p.2 (hκ_of (Finset.mem_filter.mp hp).2) (R p.1).rep) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨h1, h2, -, -⟩ := repsOf_props _ (hR p.1)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact (isOnePI_relabelK_iff _ _ _).mpr h1
      · exact isVPChain_relabelK _ _ ((isVPChain_iff 2 _).mpr ⟨_, h2⟩)
    · intro p _ q _ hpq
      obtain ⟨h1, h2⟩ := relabelK_rep_inj _ _ hpq
      exact Prod.ext h1 h2
    · intro C hC
      obtain ⟨R', hR', π, hκ, rfl⟩ := exists_rep (Finset.mem_filter.mp hC).2.2
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hR'
      refine ⟨(i, π), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      funext s
      simp only [hg, hRdef, Function.comp_apply]
      rw [← hκ, Equiv.apply_symm_apply]
    · intro p _
      obtain ⟨h1, -, -, -⟩ := repsOf_props _ (hR p.1)
      simp only [hF, fermionSign_relabelK, hG _ _ _ h1]
  have hmaps : ∀ p ∈ (Finset.univ : Finset (Fin (repsOf N).length × Equiv.Perm (Fin N))),
      g p ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ 7) := by
    intro p _
    obtain ⟨-, -, h3, -⟩ := repsOf_props _ (hR p.1)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp only [hg, Function.comp_apply]
    rw [Equiv.sum_comp p.2.symm (fun t => ((R p.1).kinds t).order), h3]
  rw [Finset.sum_congr rfl fun κ _ => inner κ, Finset.sum_fiberwise_of_maps_to hmaps F,
    Fintype.sum_prod_type]
  simp only [hF, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, Finset.mul_sum]
  rfl

/-! ### The vertex -/

theorem repsOf_lt_five {N : ℕ} (h : N < 5) : repsOf N = [] :=
  repsOf_eq_nil (by omega) (by omega) (by omega)

theorem repsOf_five : repsOf 5 = reps5 := rfl

theorem repsOf_six : repsOf 6 = reps6 := rfl

theorem repsOf_seven : repsOf 7 = reps7 := rfl

/-- (M₃) at the helper level: at T1's flavours the value (F₇) is T1's value (T₁₀), by `rfl`. -/
theorem contractionValue₂_params' (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) :
    QED.Lepton.contractionValue₂ P ⟨P.mass, P.loopCoeff, 0⟩ C =
      QED.WickModel.contractionValue₂ P C :=
  rfl

/-- **The chain vertex by vertex number**, at any flavour data `Φ`: `(1/i)` times, over the
numbers of vertices `N ≤ 7`, the signed sum of the values (F₇) of the representatives with `N`
vertices, each with coefficient one. -/
theorem vertexChain_two_eq_flavors (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : QED.Lepton.Flavors F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    QED.VPChain.vertexChain 2 P Φ p' p μ =
      Matrix.of fun α β => (1 / I) * ∑ N ∈ Finset.range 8, ∑ i : Fin (repsOf N).length,
        ((fermionSign ((repsOf N).get i).rep : ℤ) : ℂ) *
          QED.Lepton.contractionValue₂ P Φ ((repsOf N).get i).rep (fun _ => p') (fun _ => p)
            (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) := by
  ext α β
  simp only [QED.VPChain.vertexChain, QED.Lepton.onePIFamilyFunction₂, Matrix.of_apply,
    Nat.reduceMul, Nat.reduceAdd]
  congr 1
  refine Finset.sum_congr rfl fun N _ => ?_
  have hmom : ∑ i : Fin 1, (fun _ => p') i =
      ∑ i : Fin 1, (fun _ => p) i + ∑ j : Fin 1, (fun _ => p' - p) j := by
    simp
  rw [sum_chain (N := N) (fun C => QED.Lepton.contractionValue₂ P Φ C
      (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ))
    (fun π hκ C hC => contractionValue₂_relabelK_of_isOnePI_lepton Φ P π hκ hC hmom _ _ _)]
  have hN : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- **The set (b) chain vertex is the signed sum of the nine class values, each with
coefficient one** (obligation O3-4), at any flavour data `Φ`: for all momenta `p'`, `p` (incoming
photon momentum `p' - p`), the chain vertex (C₃) `vertexChain 2` is `(1/i)` times
`V(BB) - V(BD₀) - V(BD₁) - V(DB₀) - V(DB₁) + V(DD₀₀) + V(DD₀₁) + V(DD₁₀) + V(DD₁₁)`, with `V` the
value (F₇) of the representative: bubble–bubble (three loops, sign `+1`), bubble–`δ₃` and
`δ₃`–bubble with either field of the `photonCt` vertex towards the vertex `a` (two loops, sign
`-1`), `δ₃`–`δ₃` with the four field pairings (one loop, sign `+1`). -/
theorem vertexChain_two_eq_classes_flavors (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : QED.Lepton.Flavors F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    QED.VPChain.vertexChain 2 P Φ p' p μ =
      Matrix.of fun α β =>
        let V := fun {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) =>
          QED.Lepton.contractionValue₂ P Φ C (fun _ => p') (fun _ => p) (fun _ => p' - p)
            (fun _ => α) (fun _ => β) (fun _ => μ)
        (1 / I) * (V repBB - V (repBD 0) - V (repBD 1) - V (repDB 0) - V (repDB 1) +
          V (repDD 0 0) + V (repDD 0 1) + V (repDD 1 0) + V (repDD 1 1)) := by
  rw [vertexChain_two_eq_flavors]
  ext α β
  simp only [Matrix.of_apply]
  congr 1
  have key : ∀ N : ℕ, (∑ i : Fin (repsOf N).length, ((fermionSign ((repsOf N).get i).rep : ℤ) : ℂ) *
      QED.Lepton.contractionValue₂ P Φ ((repsOf N).get i).rep (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) : ℂ) =
      ((repsOf N).map fun R => ((fermionSign R.rep : ℤ) : ℂ) *
        QED.Lepton.contractionValue₂ P Φ R.rep (fun _ => p') (fun _ => p)
          (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)).sum := fun N => by
    simp only [List.get_eq_getElem]
    exact Fin.sum_univ_fun_getElem (repsOf N) fun R => ((fermionSign R.rep : ℤ) : ℂ) *
      QED.Lepton.contractionValue₂ P Φ R.rep (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)
  simp only [key, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  rw [repsOf_lt_five (by norm_num : 0 < 5), repsOf_lt_five (by norm_num : 1 < 5),
    repsOf_lt_five (by norm_num : 2 < 5), repsOf_lt_five (by norm_num : 3 < 5),
    repsOf_lt_five (by norm_num : 4 < 5), repsOf_five, repsOf_six, repsOf_seven]
  simp only [reps5, reps6, reps7, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    fermionSign_repBB, fermionSign_repBD, fermionSign_repDB, fermionSign_repDD]
  push_cast
  ring

/-- **The chain vertex at T1's flavours by vertex number**, with T1's values (T₁₀). -/
theorem vertexChain_two_eq (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    QED.VPChain.vertexChain 2 P (⟨P.mass, P.loopCoeff, 0⟩ : QED.Lepton.Flavors (Fin 3)) p' p μ =
      Matrix.of fun α β => (1 / I) * ∑ N ∈ Finset.range 8, ∑ i : Fin (repsOf N).length,
        ((fermionSign ((repsOf N).get i).rep : ℤ) : ℂ) *
          QED.WickModel.contractionValue₂ P ((repsOf N).get i).rep (fun _ => p') (fun _ => p)
            (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) :=
  vertexChain_two_eq_flavors P _ p' p μ

/-- **The set (b) chain vertex at T1's flavours** (the flavours of the headline (HC₃)) is the
signed sum of the T1 values (T₁₀) of the nine representatives, each with coefficient one. -/
theorem vertexChain_two_eq_classes (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    QED.VPChain.vertexChain 2 P (⟨P.mass, P.loopCoeff, 0⟩ : QED.Lepton.Flavors (Fin 3)) p' p μ =
      Matrix.of fun α β =>
        let V := fun {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ) =>
          QED.WickModel.contractionValue₂ P C (fun _ => p') (fun _ => p) (fun _ => p' - p)
            (fun _ => α) (fun _ => β) (fun _ => μ)
        (1 / I) * (V repBB - V (repBD 0) - V (repBD 1) - V (repDB 0) - V (repDB 1) +
          V (repDD 0 0) + V (repDD 0 1) + V (repDD 1 0) + V (repDD 1 1)) :=
  vertexChain_two_eq_classes_flavors P _ p' p μ

/-! ### The implications of (C₁) at `n = 2` -/

section Implications

variable {κ : Fin N → Wick.VertexKind}

/-- The number of `photonCt` vertices. -/
def ctCount (κ : Fin N → Wick.VertexKind) : ℕ :=
  (Finset.univ.filter fun t => κ t = .photonCt).card

theorem ctCount_comp {κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ (π t) = κ' t) : ctCount κ = ctCount κ' := by
  unfold ctCount
  refine Finset.card_bij (fun t _ => π.symm t) (fun t ht => ?_)
    (fun _ _ _ _ h => π.symm.injective h)
    (fun t ht => ⟨π t, ?_, π.symm_apply_apply t⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    rw [← hκ, Equiv.apply_symm_apply, ht]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    rw [hκ, ht]

theorem rep_facts : ∀ R ∈ repsOf N, ctCount R.kinds ≤ 2 ∧
    loopCount R.rep = 1 + (2 - ctCount R.kinds) ∧
    fermionSign R.rep = (-1) ^ (2 - ctCount R.kinds) := by
  refine repsOf_cases (fun N R => ctCount R.kinds ≤ 2 ∧
    loopCount R.rep = 1 + (2 - ctCount R.kinds) ∧
    fermionSign R.rep = (-1) ^ (2 - ctCount R.kinds)) ?_ ?_ ?_
  · simp only [reps5, List.mem_cons, List.not_mem_nil, or_false]
    have hc : ctCount kDD = 2 := by decide
    rintro R (rfl | rfl | rfl | rfl) <;>
      exact ⟨by rw [hc], by rw [loopCount_repDD, hc], by rw [fermionSign_repDD, hc]; rfl⟩
  · simp only [reps6, List.mem_cons, List.not_mem_nil, or_false]
    have hc : ctCount kBD = 1 := by decide
    have hc' : ctCount kDB = 1 := by decide
    rintro R (rfl | rfl | rfl | rfl)
    · exact ⟨by simp [hc], by rw [loopCount_repBD, hc], by rw [fermionSign_repBD, hc]; rfl⟩
    · exact ⟨by simp [hc], by rw [loopCount_repBD, hc], by rw [fermionSign_repBD, hc]; rfl⟩
    · exact ⟨by simp [hc'], by rw [loopCount_repDB, hc'], by rw [fermionSign_repDB, hc']; rfl⟩
    · exact ⟨by simp [hc'], by rw [loopCount_repDB, hc'], by rw [fermionSign_repDB, hc']; rfl⟩
  · simp only [reps7, List.mem_cons, List.not_mem_nil, or_false]
    have hc : ctCount kBB = 0 := by decide
    rintro R rfl
    exact ⟨by rw [hc]; omega, by rw [loopCount_repBB, hc], by rw [fermionSign_repBB, hc]; rfl⟩

/-- (C₁) with `n = 2` implies one-particle irreducibility (X₁₈). -/
theorem isOnePI_of_isVPChain_two {C : Contraction 1 1 κ} (hC : QED.VPChain.IsVPChain 2 C) :
    IsOnePI C := by
  obtain ⟨R, hR, π, hκ, rfl⟩ := exists_rep hC
  exact (isOnePI_relabelK_iff _ _ _).mpr (repsOf_props R hR).1

/-- (C₁) with `n = 2` implies total order `2n + 3 = 7`. -/
theorem order_of_isVPChain_two {C : Contraction 1 1 κ} (hC : QED.VPChain.IsVPChain 2 C) :
    ∑ t, (κ t).order = 7 := by
  obtain ⟨R, hR, π, hκ, rfl⟩ := exists_rep hC
  rw [← (repsOf_props R hR).2.2.1, ← Equiv.sum_comp π (fun t => (κ t).order)]
  simp only [hκ]

/-- (C₁) with `n = 2` has `2 - #photonCt` bubbles, and `1 + #bubbles` loops (T₂). -/
theorem loopCount_of_isVPChain_two {C : Contraction 1 1 κ} (hC : QED.VPChain.IsVPChain 2 C) :
    ctCount κ ≤ 2 ∧ loopCount C = 1 + (2 - ctCount κ) := by
  obtain ⟨R, hR, π, hκ, rfl⟩ := exists_rep hC
  obtain ⟨h1, h2, h3⟩ := rep_facts R hR
  rw [ctCount_comp π hκ, loopCount_relabelK _ _ _ (repsOf_props R hR).1.2.1]
  exact ⟨h1, h2⟩

/-- (C₁) with `n = 2` has fermionic sign (X₅) `(-1)^#bubbles`. -/
theorem fermionSign_of_isVPChain_two {C : Contraction 1 1 κ} (hC : QED.VPChain.IsVPChain 2 C) :
    fermionSign C = (-1) ^ (2 - ctCount κ) := by
  obtain ⟨R, hR, π, hκ, rfl⟩ := exists_rep hC
  rw [ctCount_comp π hκ, fermionSign_relabelK]
  exact (rep_facts R hR).2.2

end Implications

end QED.ChainProof.Enum

end
