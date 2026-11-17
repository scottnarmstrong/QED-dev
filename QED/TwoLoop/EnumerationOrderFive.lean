/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.OnePIFunction
public import QED.TwoLoop.EnumerationGauge5
public import QED.TwoLoop.EnumerationCounterterm

/-!
# The order-`e⁵` part of the two-loop 1PI vertex as an explicit finite sum

Obligation O2-2 (section 3 of `docs/TWO-LOOP-DERIVATION.md`), combinatorial part. The order-5
vertex of candidate packet T3 is `onePIFunction₂ P 1 1 5 - onePIFunction₂ P 1 1 4` (T₁₁,
decision D-38). This file shows, at every fixed `P` and every external data, that it is

* `1/5!` times the sum over the nine classes of five gauge vertices (`Class5`) of the class sign
  times the sum of the contraction values over the `5!` relabellings of the representative;
* plus `1/4!` times the sum of the values of the `8 × 12` listed 1PI contractions with one
  `fermionCt` or one `photonCt` vertex (all of sign `+1`);
* plus `1/3!` times the sum of the values of the `3 × 6` listed 1PI contractions with one
  `gaugeCt` vertex (all of sign `+1`).

No other kind sequence contributes: the sequences of total order exactly `5` are listed
(`filter_order_eq_five_*`), and the 16 sequences other than these 12 have no 1PI contraction
(trees). In particular no tadpole and no contraction with two closed loops occurs (obligation
O2-4 for the 1PI function), and no counterterm vertex appears in a tree of order 5 (section
3.2).

## Main statements

* `QED.TwoLoop.Enumeration.onePIFunction₂_five_sub_four`: the explicit finite sum.
* `QED.TwoLoop.Enumeration.onePIFunction₂_five_sub_four_of_invariant`: if the value of a
  contraction of five gauge vertices is invariant under relabelling (not proved here; see
  `docs/TWO-LOOP-ENUMERATION.md`), the five-gauge part is `∑ c, sign c * value (rep c)`: each of
  the nine classes enters with coefficient one and its sign.
-/

@[expose] public section

namespace QED.TwoLoop.Enumeration

open QED.WickModel

/-- The sum of the values (T₁₀) of a list of contractions. -/
noncomputable def listValue (P : Params) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (L : List (Contraction 1 1 κ)) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    ℂ :=
  (L.map fun C => contractionValue₂ P C pOut pIn kIn αOut βIn μ).sum

theorem one_le_order (k : Wick.VertexKind) : 1 ≤ k.order := by
  cases k <;> decide

theorem le_sum_order {N : ℕ} (κ : Fin N → Wick.VertexKind) : N ≤ ∑ t, (κ t).order := by
  calc N = ∑ _t : Fin N, 1 := by simp
    _ ≤ ∑ t, (κ t).order := Finset.sum_le_sum fun t _ => one_le_order _

theorem sum_filter_le_five {N : ℕ} (F : (Fin N → Wick.VertexKind) → ℂ) :
    ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ 5), F κ =
      ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
          (fun κ => ∑ t, (κ t).order ≤ 4), F κ +
        ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
          (fun κ => ∑ t, (κ t).order = 5), F κ := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  split_ifs <;> first | omega | simp

theorem sum_filter_le_four_five (F : (Fin 5 → Wick.VertexKind) → ℂ) :
    ∑ κ ∈ (Finset.univ : Finset (Fin 5 → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order ≤ 4), F κ = 0 :=
  Finset.sum_eq_zero fun κ hκ =>
    absurd (Finset.mem_filter.mp hκ).2 (by have := le_sum_order κ; omega)

/-! ### The kind sequences of order five -/

theorem filter_order_eq_five_zero :
    (Finset.univ : Finset (Fin 0 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 5) = ∅ := by decide +kernel

theorem filter_order_eq_five_one :
    (Finset.univ : Finset (Fin 1 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 5) = ∅ := by decide +kernel

theorem filter_order_eq_five_two :
    (Finset.univ : Finset (Fin 2 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 5) = [k_Cf, k_Cp, k_fC, k_pC].toFinset := by decide +kernel

theorem filter_order_eq_five_three :
    (Finset.univ : Finset (Fin 3 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 5) =
      [k_ggC, k_gCg, k_gff, k_gfp, k_gpf, k_gpp, k_Cgg, k_fgf, k_fgp, k_ffg, k_fpg, k_pgf, k_pgp,
        k_pfg, k_ppg].toFinset := by
  decide +kernel

theorem filter_order_eq_five_four :
    (Finset.univ : Finset (Fin 4 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 5) =
      [k_gggf, k_gggp, k_ggfg, k_ggpg, k_gfgg, k_gpgg, k_fggg, k_pggg].toFinset := by
  decide +kernel

theorem filter_order_eq_five_five :
    (Finset.univ : Finset (Fin 5 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 5) = {gauges 5} := by decide +kernel

theorem nodup_two : ([k_Cf, k_Cp, k_fC, k_pC] : List (Fin 2 → Wick.VertexKind)).Nodup := by
  decide +kernel

theorem nodup_three : ([k_ggC, k_gCg, k_gff, k_gfp, k_gpf, k_gpp, k_Cgg, k_fgf, k_fgp, k_ffg, k_fpg,
    k_pgf, k_pgp, k_pfg, k_ppg] : List (Fin 3 → Wick.VertexKind)).Nodup := by
  decide +kernel

theorem nodup_four :
    ([k_gggf, k_gggp, k_ggfg, k_ggpg, k_gfgg, k_gpgg, k_fggg, k_pggg] :
      List (Fin 4 → Wick.VertexKind)).Nodup := by
  decide +kernel

/-! ### The order-five vertex -/

/-- **The order-`e⁵` 1PI vertex as an explicit finite sum** (obligation O2-2, combinatorial
part). At every fixed parameter set `P` and external data, the order-exactly-5 part
`onePIFunction₂ P 1 1 5 - onePIFunction₂ P 1 1 4` of the two-loop 1PI function (T₁₁) is the
signed sum over the nine classes of five gauge vertices, each summed over its `5!` relabellings,
divided by `5!`, plus the 1PI contractions with one counterterm vertex, divided by `N!`. -/
theorem onePIFunction₂_five_sub_four (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    onePIFunction₂ P 1 1 5 pOut pIn kIn αOut βIn μ -
        onePIFunction₂ P 1 1 4 pOut pIn kIn αOut βIn μ =
      (Nat.factorial 5 : ℂ)⁻¹ * ∑ c : Class5, (c.sign : ℂ) *
          ∑ π : Equiv.Perm (Fin 5), contractionValue₂ P (relabel π c.rep) pOut pIn kIn αOut βIn μ +
        (Nat.factorial 4 : ℂ)⁻¹ * (listValue P onePI_gggf pOut pIn kIn αOut βIn μ +
          listValue P onePI_gggp pOut pIn kIn αOut βIn μ +
          listValue P onePI_ggfg pOut pIn kIn αOut βIn μ +
          listValue P onePI_ggpg pOut pIn kIn αOut βIn μ +
          listValue P onePI_gfgg pOut pIn kIn αOut βIn μ +
          listValue P onePI_gpgg pOut pIn kIn αOut βIn μ +
          listValue P onePI_fggg pOut pIn kIn αOut βIn μ +
          listValue P onePI_pggg pOut pIn kIn αOut βIn μ) +
        (Nat.factorial 3 : ℂ)⁻¹ * (listValue P onePI_ggC pOut pIn kIn αOut βIn μ +
          listValue P onePI_gCg pOut pIn kIn αOut βIn μ +
          listValue P onePI_Cgg pOut pIn kIn αOut βIn μ) := by
  unfold onePIFunction₂
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, sum_filter_le_five]
  rw [sum_filter_le_four_five, filter_order_eq_five_zero, filter_order_eq_five_one,
    filter_order_eq_five_two, filter_order_eq_five_three, filter_order_eq_five_four,
    filter_order_eq_five_five, List.sum_toFinset _ nodup_two, List.sum_toFinset _ nodup_three,
    List.sum_toFinset _ nodup_four, Finset.sum_singleton, Finset.sum_empty, Finset.sum_empty]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [sum_isOnePI_Cf, sum_isOnePI_Cp, sum_isOnePI_fC, sum_isOnePI_pC, sum_isOnePI_ggC,
    sum_isOnePI_gCg, sum_isOnePI_gff, sum_isOnePI_gfp, sum_isOnePI_gpf, sum_isOnePI_gpp,
    sum_isOnePI_Cgg, sum_isOnePI_fgf, sum_isOnePI_fgp, sum_isOnePI_ffg, sum_isOnePI_fpg,
    sum_isOnePI_pgf, sum_isOnePI_pgp, sum_isOnePI_pfg, sum_isOnePI_ppg, sum_isOnePI_gggf,
    sum_isOnePI_gggp, sum_isOnePI_ggfg, sum_isOnePI_ggpg, sum_isOnePI_gfgg, sum_isOnePI_gpgg,
    sum_isOnePI_fggg, sum_isOnePI_pggg, sum_isOnePI_gauges5]
  simp only [listValue, onePI_Cf, onePI_Cp, onePI_fC, onePI_pC, onePI_gff, onePI_gfp, onePI_gpf,
    onePI_gpp, onePI_fgf, onePI_fgp, onePI_ffg, onePI_fpg, onePI_pgf, onePI_pgp, onePI_pfg,
    onePI_ppg,
    List.map_nil, List.sum_nil]
  ring

/-- **Coefficient one per class.** If the value (T₁₀) of a contraction of five gauge vertices is
invariant under relabelling the vertices, each of the nine classes enters the order-`e⁵` vertex
with coefficient one and its sign. -/
theorem onePIFunction₂_five_sub_four_of_invariant (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4)
    (hinv : ∀ (π : Equiv.Perm (Fin 5)) (C : Contraction 1 1 (gauges 5)),
      contractionValue₂ P (relabel π C) pOut pIn kIn αOut βIn μ =
        contractionValue₂ P C pOut pIn kIn αOut βIn μ) :
    onePIFunction₂ P 1 1 5 pOut pIn kIn αOut βIn μ -
        onePIFunction₂ P 1 1 4 pOut pIn kIn αOut βIn μ =
      ∑ c : Class5, (c.sign : ℂ) * contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ +
        (Nat.factorial 4 : ℂ)⁻¹ * (listValue P onePI_gggf pOut pIn kIn αOut βIn μ +
          listValue P onePI_gggp pOut pIn kIn αOut βIn μ +
          listValue P onePI_ggfg pOut pIn kIn αOut βIn μ +
          listValue P onePI_ggpg pOut pIn kIn αOut βIn μ +
          listValue P onePI_gfgg pOut pIn kIn αOut βIn μ +
          listValue P onePI_gpgg pOut pIn kIn αOut βIn μ +
          listValue P onePI_fggg pOut pIn kIn αOut βIn μ +
          listValue P onePI_pggg pOut pIn kIn αOut βIn μ) +
        (Nat.factorial 3 : ℂ)⁻¹ * (listValue P onePI_ggC pOut pIn kIn αOut βIn μ +
          listValue P onePI_gCg pOut pIn kIn αOut βIn μ +
          listValue P onePI_Cgg pOut pIn kIn αOut βIn μ) := by
  rw [onePIFunction₂_five_sub_four]
  congr 2
  simp only [hinv, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : (Nat.factorial 5 : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos 5).ne'
  field_simp

end QED.TwoLoop.Enumeration

end
