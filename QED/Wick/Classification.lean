/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Wick.Gauge3
import QED.Wick.ClassificationSmall
import QED.Wick.ClassificationGauge3

/-!
# Reduction of the Wick vertex to the trees and the vertex corrections

The combinatorial part of the packet 5 theorem goal (decision D-20). The Wick vertex
`QED.Wick.wickVertex` sums over the vertex sequences of total order at most `3`:
`[]`, the four single vertices, the five pairs `[g, g]`, `[g, fermionCt]`, `[fermionCt, g]`,
`[g, photonCt]`, `[photonCt, g]` (with `g = gauge`), and `[g, g, g]`.

* `[]`, `[fermionCt]`, `[photonCt]` and `[g, g]` have no contraction: an odd number of photon
  fields admits no fixed-point-free involution.
* The other four pairs have contractions, but none is 1PI: at most one internal line joins the
  two vertices.
* `[g]` and `[gaugeCt]` each have exactly one 1PI contraction, of sign `+1` and without internal
  lines; their values are the trees `i e γ^μ` and `i δ₁ e γ^μ`.
* The 1PI contractions of `[g, g, g]` are the six vertex corrections `IsChain C a b c`, each of
  sign `+1`.

## Main statements

* `wickVertex_eq_chains`: the Wick vertex is the tree `i (1 + δ₁) e γ^μ` plus `1/3!` times the
  sum of the values of the vertex corrections.
* `card_isChain`: there are six vertex corrections.
-/

@[expose] public section

namespace QED.Wick

/-- The order of a vertex is at least `1`, with equality only for `gauge`, so three vertices of
total order at most `3` are three gauge vertices. -/
theorem eq_gauge3_of_sum_order_le {κ : Fin 3 → VertexKind} (h : ∑ t, (κ t).order ≤ 3) :
    κ = gauge3 := by
  have key : ∀ k₀ k₁ k₂ : VertexKind, k₀.order + k₁.order + k₂.order ≤ 3 →
      k₀ = .gauge ∧ k₁ = .gauge ∧ k₂ = .gauge := by
    decide
  rw [Fin.sum_univ_three] at h
  obtain ⟨h0, h1, h2⟩ := key _ _ _ h
  funext t
  fin_cases t <;> assumption

/-- The 1PI part of three gauge vertices: the sum over the vertex corrections, each of sign
`+1`. -/
theorem sum_isOnePI_gauge3 [DecidablePred (IsOnePI (κ := gauge3))]
    [DecidablePred fun C : Contraction gauge3 => ∃ a b c, IsChain C a b c]
    (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ C ∈ (Finset.univ : Finset (Contraction gauge3)).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) • contractionValue e δ₁ δ₂ δm δ₃ m mγ Λ ε C p' p μ =
      ∑ C ∈ (Finset.univ : Finset (Contraction gauge3)).filter
          (fun C => ∃ a b c, IsChain C a b c),
        contractionValue e δ₁ δ₂ δm δ₃ m mγ Λ ε C p' p μ := by
  rw [Finset.filter_congr fun C _ => isOnePI_iff_exists_isChain C]
  refine Finset.sum_congr rfl fun C hC => ?_
  obtain ⟨a, b, c, h⟩ := (Finset.mem_filter.mp hC).2
  rw [h.fermionSign_eq_one]
  simp

open scoped Classical in
/-- **The Wick vertex as trees plus vertex corrections.** The order-`e³` 1PI part of the Wick
expansion is the counterterm-corrected tree `i (1 + δ₁) e γ^μ`, from the single `gauge` and
`gaugeCt` vertices, plus `1/3!` times the sum of the values of the vertex corrections of three
gauge vertices (each of fermionic sign `+1`). No other vertex sequence contributes. -/
theorem wickVertex_eq_chains (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    wickVertex e δ₁ δ₂ δm δ₃ m mγ Λ ε p' p μ =
      (Complex.I * (((1 + δ₁) * e : ℝ) : ℂ)) • Dirac.gamma μ +
        ((6 : ℂ)⁻¹) • ∑ C ∈ (Finset.univ : Finset (Contraction gauge3)).filter
            (fun C => ∃ a b c, IsChain C a b c),
          contractionValue e δ₁ δ₂ δm δ₃ m mγ Λ ε C p' p μ := by
  rw [wickVertex]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- no vertices
  rw [Finset.sum_eq_zero fun κ _ => sum_isOnePI_eq_zero not_isOnePI_of_fin_zero _]
  -- one vertex: the trees
  rw [Finset.sum_eq_add (fun _ => .gauge) (fun _ => .gaugeCt) (fun h => by
      have := congrFun h 0
      cases this) (fun κ _ hκ => by
      obtain ⟨k, rfl⟩ : ∃ k, κ = fun _ => k :=
        ⟨κ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
      cases k
      · exact absurd rfl hκ.1
      · exact absurd rfl hκ.2
      · exact sum_isOnePI_eq_zero
          (fun C => (isEmpty_contraction_of_not_two_dvd (by decide)).elim C) _
      · exact sum_isOnePI_eq_zero
          (fun C => (isEmpty_contraction_of_not_two_dvd (by decide)).elim C) _)
      (fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩) h)
      (fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩) h),
    sum_isOnePI_gauge, sum_isOnePI_gaugeCt]
  -- two vertices
  rw [Finset.sum_eq_zero fun κ hκ =>
    sum_isOnePI_eq_zero (not_isOnePI_of_fin_two κ (Finset.mem_filter.mp hκ).2) _]
  -- three vertices
  rw [Finset.sum_eq_single_of_mem gauge3 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩)
      fun κ hκ hne => absurd (eq_gauge3_of_sum_order_le (Finset.mem_filter.mp hκ).2) hne,
    sum_isOnePI_gauge3]
  simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.cast_mul, Nat.cast_one, smul_zero, zero_add,
    add_zero, mul_one, inv_one, one_smul]
  rw [← add_smul]
  congr 2
  · push_cast
    ring
  · norm_num

open scoped Classical in
/-- There are six vertex corrections of three gauge vertices, one for each ordering of the
vertices. -/
theorem card_isChain : ((Finset.univ : Finset (Contraction gauge3)).filter
    (fun C => ∃ a b c, IsChain C a b c)).card = 6 := by
  rw [← card_distinct_triples]
  symm
  refine Finset.card_bij (fun p hp => chainContraction p.1 p.2.1 p.2.2
      (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2.1
      (Finset.mem_filter.mp hp).2.2.2) (fun p hp => ?_) (fun p hp q hq hpq => ?_)
      (fun C hC => ?_)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, _, _, isChain_chainContraction _ _ _ _ _ _⟩
  · have hq' := isChain_chainContraction q.1 q.2.1 q.2.2 (Finset.mem_filter.mp hq).2.1
      (Finset.mem_filter.mp hq).2.2.1 (Finset.mem_filter.mp hq).2.2.2
    rw [← hpq] at hq'
    obtain ⟨h1, h2, h3⟩ := (isChain_chainContraction _ _ _ _ _ _).unique hq'
    exact Prod.ext h1 (Prod.ext h2 h3)
  · obtain ⟨a, b, c, h⟩ := (Finset.mem_filter.mp hC).2
    exact ⟨(a, b, c), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1, h.2.1, h.2.2.1⟩,
      (isChain_chainContraction _ _ _ _ _ _).ext h⟩

end QED.Wick

end
