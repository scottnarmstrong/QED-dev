/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.IntegrableOrderFiveCt
public import QED.TwoLoop.ClassIntegrable
public import QED.TwoLoop.ClassIntegrableVP
public import QED.TwoLoop.ClassIntegrableFurry
public import QED.TwoLoop.RelabelCountertermClasses
public import QED.TwoLoop.EnumerationOrderFive

/-!
# Every term of the order-`e⁵` vertex is a genuine integral (HV₀)

Decision D-44 item 2, obligation O2-7. Let `ε > 0` and let the regulator fermions satisfy the
Pauli–Villars conditions `1 + c₁ + c₂ = 0`, `m² + c₁ M₁² + c₂ M₂² = 0`. For every 1PI contraction
`C` with one external fermion pair and one external photon whose vertices have total order exactly
`5` (the contractions summed in (HV₁) `QED.TwoLoop.vertexOrderFive`), at all external momenta with
momentum conservation and all external indices, the integrand of the value (T₁₀) satisfies (T₉′):
both stages of the joint energy-first integral (T₉) converge absolutely
(`jointEnergyFirstIntegrable_of_order_five`).

## Proof

The enumeration (obligation O2-2) lists the kind sequences of total order `5`
(`QED.TwoLoop.Enumeration.filter_order_eq_five_*`): none with `0` or `1` vertices; with `2` or
`3` vertices only those whose 1PI contractions are listed (`isOnePI_iff_*`), the lists being empty
except for one `gaugeCt` vertex and two gauge vertices; with `4` vertices the eight sequences of
three gauge vertices and one `fermionCt` or `photonCt` vertex; with `5` vertices only five gauge
vertices. No sequence has more than `5` vertices, since every vertex has order at least `1`.

* **Five gauge vertices.** Every 1PI contraction is a relabelling of one of the nine class
  representatives (`QED.TwoLoop.Enumeration.exists_rep_of_isOnePI`). Each representative satisfies
  (T₉′): the six open-line classes by `QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_open`,
  `VP` by `jointEnergyFirstIntegrable_VP`, `F₊`, `F₋` by `jointEnergyFirstIntegrable_Fp`, `…_Fm`
  (the last three with the Pauli–Villars conditions). (T₉′) passes to relabellings
  (`jointEnergyFirstIntegrable_relabel`).
* **One counterterm vertex.** Every listed contraction is a relabelling across kind sequences of
  one of the seven counterterm class representatives (`QED.TwoLoop.Relabel.onePI_*_eq_relabelK`),
  each of which satisfies (T₉′) (`jointEnergyFirstIntegrable_ctClass`, at any masses), and (T₉′)
  passes to such relabellings (`jointEnergyFirstIntegrable_relabelK`).
-/

public section

open MeasureTheory

namespace QED.TwoLoop.IntegrableOrderFive

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel

/-- (T₉′) for the integrand `(2π)^{-4L} A(ℓ)` of the value (T₁₀) of `C` in the frozen routing. -/
def ValueIntegrable (P : Params) {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) : Prop :=
  QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
    (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ

section Terms

variable (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
  (αOut βIn μ : Fin 1 → Fin 4)

include hmom in
theorem valueIntegrable_relabelK {N : ℕ} {κ κ' : Fin N → Wick.VertexKind}
    (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) {C : Contraction 1 1 κ}
    (hC : IsOnePI C) (h : ValueIntegrable P C pOut pIn kIn αOut βIn μ) :
    ValueIntegrable P (relabelK π hκ C) pOut pIn kIn αOut βIn μ :=
  jointEnergyFirstIntegrable_relabelK P π hκ hC (by simp only [Fin.sum_univ_one, hmom]) αOut βIn μ
    h

include hmom in
theorem valueIntegrable_relabel {N : ℕ} (π : Equiv.Perm (Fin N)) {C : Contraction 1 1 (gauges N)}
    (hC : IsOnePI C) (h : ValueIntegrable P C pOut pIn kIn αOut βIn μ) :
    ValueIntegrable P (relabel π C) pOut pIn kIn αOut βIn μ :=
  jointEnergyFirstIntegrable_relabel P π hC (by simp only [Fin.sum_univ_one, hmom]) αOut βIn μ h

/-! ### The nine classes of five gauge vertices -/

include hmom in
theorem valueIntegrable_class5 (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (c : Class5) :
    ValueIntegrable P c.rep pOut pIn kIn αOut βIn μ := by
  unfold ValueIntegrable
  rw [loopCount_rep c]
  cases c
  · exact ClassIntegrable.jointEnergyFirstIntegrable_open (by decide) P hε hmom αOut βIn μ
  · exact ClassIntegrable.jointEnergyFirstIntegrable_open (by decide) P hε hmom αOut βIn μ
  · exact ClassIntegrable.jointEnergyFirstIntegrable_open (by decide) P hε hmom αOut βIn μ
  · exact ClassIntegrable.jointEnergyFirstIntegrable_open (by decide) P hε hmom αOut βIn μ
  · exact ClassIntegrable.jointEnergyFirstIntegrable_open (by decide) P hε hmom αOut βIn μ
  · exact ClassIntegrable.jointEnergyFirstIntegrable_open (by decide) P hε hmom αOut βIn μ
  · exact ClassIntegrable.jointEnergyFirstIntegrable_VP P hε hc₁ hc₂ hmom αOut βIn μ
  · exact ClassIntegrable.jointEnergyFirstIntegrable_Fp P hε hc₁ hc₂ hmom αOut βIn μ
  · exact ClassIntegrable.jointEnergyFirstIntegrable_Fm P hε hc₁ hc₂ hmom αOut βIn μ

include hmom in
/-- **Five gauge vertices.** -/
theorem valueIntegrable_gauges5 (hε : 0 < P.ε) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {C : Contraction 1 1 (gauges 5)}
    (hC : IsOnePI C) : ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  obtain ⟨c, π, rfl⟩ := exists_rep_of_isOnePI hC
  exact valueIntegrable_relabel P hmom αOut βIn μ π (rep_isOnePI c)
    (valueIntegrable_class5 P hmom αOut βIn μ hε hc₁ hc₂ c)

/-! ### The counterterm contractions -/

section Ct

variable (hε : 0 < P.ε)
include hε hmom

theorem valueIntegrable_repD2In : ValueIntegrable P repD2In pOut pIn kIn αOut βIn μ :=
  jointEnergyFirstIntegrable_ctClass P hε hmom αOut βIn μ .d2In

theorem valueIntegrable_repD2Out : ValueIntegrable P repD2Out pOut pIn kIn αOut βIn μ :=
  jointEnergyFirstIntegrable_ctClass P hε hmom αOut βIn μ .d2Out

theorem valueIntegrable_repD3Slot0 : ValueIntegrable P repD3Slot0 pOut pIn kIn αOut βIn μ :=
  jointEnergyFirstIntegrable_ctClass P hε hmom αOut βIn μ .d3Slot0

theorem valueIntegrable_repD3Slot1 : ValueIntegrable P repD3Slot1 pOut pIn kIn αOut βIn μ :=
  jointEnergyFirstIntegrable_ctClass P hε hmom αOut βIn μ .d3Slot1

theorem valueIntegrable_repD1At1 : ValueIntegrable P repD1At1 pOut pIn kIn αOut βIn μ :=
  jointEnergyFirstIntegrable_ctClass P hε hmom αOut βIn μ .d1At1

theorem valueIntegrable_repD1At2 : ValueIntegrable P repD1At2 pOut pIn kIn αOut βIn μ :=
  jointEnergyFirstIntegrable_ctClass P hε hmom αOut βIn μ .d1At2

theorem valueIntegrable_repD1At3 : ValueIntegrable P repD1At3 pOut pIn kIn αOut βIn μ :=
  jointEnergyFirstIntegrable_ctClass P hε hmom αOut βIn μ .d1At3

/-- The `fermionCt` contractions: relabellings of `repD2In`, `repD2Out`. -/
theorem valueIntegrable_of_d2 {κ : Fin 4 → Wick.VertexKind} {C : Contraction 1 1 κ}
    (h : ∃ (π : Equiv.Perm (Fin 4)) (hκ : ∀ t, κ (π t) = k_gggf t),
      C = relabelK π hκ repD2In ∨ C = relabelK π hκ repD2Out) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  obtain ⟨π, hκ, rfl | rfl⟩ := h
  · exact valueIntegrable_relabelK P hmom αOut βIn μ π hκ repD2In_isOnePI
      (valueIntegrable_repD2In P hmom αOut βIn μ hε)
  · exact valueIntegrable_relabelK P hmom αOut βIn μ π hκ repD2Out_isOnePI
      (valueIntegrable_repD2Out P hmom αOut βIn μ hε)

/-- The `photonCt` contractions: relabellings of `repD3Slot0`, `repD3Slot1`. -/
theorem valueIntegrable_of_d3 {κ : Fin 4 → Wick.VertexKind} {C : Contraction 1 1 κ}
    (h : ∃ (π : Equiv.Perm (Fin 4)) (hκ : ∀ t, κ (π t) = k_gggp t),
      C = relabelK π hκ repD3Slot0 ∨ C = relabelK π hκ repD3Slot1) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  obtain ⟨π, hκ, rfl | rfl⟩ := h
  · exact valueIntegrable_relabelK P hmom αOut βIn μ π hκ repD3Slot0_isOnePI
      (valueIntegrable_repD3Slot0 P hmom αOut βIn μ hε)
  · exact valueIntegrable_relabelK P hmom αOut βIn μ π hκ repD3Slot1_isOnePI
      (valueIntegrable_repD3Slot1 P hmom αOut βIn μ hε)

/-- The `gaugeCt` contractions: relabellings of `repD1At1`, `repD1At2`, `repD1At3`. -/
theorem valueIntegrable_of_d1 {κ : Fin 3 → Wick.VertexKind} {C : Contraction 1 1 κ}
    (h : ∃ (π : Equiv.Perm (Fin 3)) (hκ : ∀ t, κ (π t) = k_ggC t),
      C = relabelK π hκ repD1At1 ∨ C = relabelK π hκ repD1At2 ∨ C = relabelK π hκ repD1At3) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  obtain ⟨π, hκ, rfl | rfl | rfl⟩ := h
  · exact valueIntegrable_relabelK P hmom αOut βIn μ π hκ repD1At1_isOnePI
      (valueIntegrable_repD1At1 P hmom αOut βIn μ hε)
  · exact valueIntegrable_relabelK P hmom αOut βIn μ π hκ repD1At2_isOnePI
      (valueIntegrable_repD1At2 P hmom αOut βIn μ hε)
  · exact valueIntegrable_relabelK P hmom αOut βIn μ π hκ repD1At3_isOnePI
      (valueIntegrable_repD1At3 P hmom αOut βIn μ hε)

end Ct

/-! ### The listed contractions with one counterterm vertex -/

section Lists

variable (hε : 0 < P.ε)
include hε hmom

theorem valueIntegrable_ggC {C : Contraction 1 1 k_ggC} (hC : IsOnePI C) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  have hm := (isOnePI_iff_ggC C).mp hC
  rw [onePI_ggC_eq_relabelK] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h <;>
        first
        | with_reducible exact valueIntegrable_of_d1 P hmom αOut βIn μ hε ⟨_, _, Or.inl h⟩
        | with_reducible exact valueIntegrable_of_d1 P hmom αOut βIn μ hε ⟨_, _, Or.inr (Or.inl h)⟩
        | with_reducible exact valueIntegrable_of_d1 P hmom αOut βIn μ hε ⟨_, _, Or.inr (Or.inr h)⟩

theorem valueIntegrable_gCg {C : Contraction 1 1 k_gCg} (hC : IsOnePI C) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  have hm := (isOnePI_iff_gCg C).mp hC
  rw [onePI_gCg_eq_relabelK] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h <;>
        first
        | with_reducible exact valueIntegrable_of_d1 P hmom αOut βIn μ hε ⟨_, _, Or.inl h⟩
        | with_reducible exact valueIntegrable_of_d1 P hmom αOut βIn μ hε ⟨_, _, Or.inr (Or.inl h)⟩
        | with_reducible exact valueIntegrable_of_d1 P hmom αOut βIn μ hε ⟨_, _, Or.inr (Or.inr h)⟩

theorem valueIntegrable_Cgg {C : Contraction 1 1 k_Cgg} (hC : IsOnePI C) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  have hm := (isOnePI_iff_Cgg C).mp hC
  rw [onePI_Cgg_eq_relabelK] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h <;>
        first
        | with_reducible exact valueIntegrable_of_d1 P hmom αOut βIn μ hε ⟨_, _, Or.inl h⟩
        | with_reducible exact valueIntegrable_of_d1 P hmom αOut βIn μ hε ⟨_, _, Or.inr (Or.inl h)⟩
        | with_reducible exact valueIntegrable_of_d1 P hmom αOut βIn μ hε ⟨_, _, Or.inr (Or.inr h)⟩

theorem valueIntegrable_gggf {C : Contraction 1 1 k_gggf} (hC : IsOnePI C) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  have hm := (isOnePI_iff_gggf C).mp hC
  rw [onePI_gggf_eq_relabelK] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h <;>
        first
        | with_reducible exact valueIntegrable_of_d2 P hmom αOut βIn μ hε ⟨_, _, Or.inl h⟩
        | with_reducible exact valueIntegrable_of_d2 P hmom αOut βIn μ hε ⟨_, _, Or.inr h⟩

theorem valueIntegrable_ggfg {C : Contraction 1 1 k_ggfg} (hC : IsOnePI C) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  have hm := (isOnePI_iff_ggfg C).mp hC
  rw [onePI_ggfg_eq_relabelK] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h <;>
        first
        | with_reducible exact valueIntegrable_of_d2 P hmom αOut βIn μ hε ⟨_, _, Or.inl h⟩
        | with_reducible exact valueIntegrable_of_d2 P hmom αOut βIn μ hε ⟨_, _, Or.inr h⟩

theorem valueIntegrable_gfgg {C : Contraction 1 1 k_gfgg} (hC : IsOnePI C) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  have hm := (isOnePI_iff_gfgg C).mp hC
  rw [onePI_gfgg_eq_relabelK] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h <;>
        first
        | with_reducible exact valueIntegrable_of_d2 P hmom αOut βIn μ hε ⟨_, _, Or.inl h⟩
        | with_reducible exact valueIntegrable_of_d2 P hmom αOut βIn μ hε ⟨_, _, Or.inr h⟩

theorem valueIntegrable_fggg {C : Contraction 1 1 k_fggg} (hC : IsOnePI C) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  have hm := (isOnePI_iff_fggg C).mp hC
  rw [onePI_fggg_eq_relabelK] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h <;>
        first
        | with_reducible exact valueIntegrable_of_d2 P hmom αOut βIn μ hε ⟨_, _, Or.inl h⟩
        | with_reducible exact valueIntegrable_of_d2 P hmom αOut βIn μ hε ⟨_, _, Or.inr h⟩

theorem valueIntegrable_gggp {C : Contraction 1 1 k_gggp} (hC : IsOnePI C) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  have hm := (isOnePI_iff_gggp C).mp hC
  rw [onePI_gggp_eq_relabelK] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h <;>
        first
        | with_reducible exact valueIntegrable_of_d3 P hmom αOut βIn μ hε ⟨_, _, Or.inl h⟩
        | with_reducible exact valueIntegrable_of_d3 P hmom αOut βIn μ hε ⟨_, _, Or.inr h⟩

theorem valueIntegrable_ggpg {C : Contraction 1 1 k_ggpg} (hC : IsOnePI C) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  have hm := (isOnePI_iff_ggpg C).mp hC
  rw [onePI_ggpg_eq_relabelK] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h <;>
        first
        | with_reducible exact valueIntegrable_of_d3 P hmom αOut βIn μ hε ⟨_, _, Or.inl h⟩
        | with_reducible exact valueIntegrable_of_d3 P hmom αOut βIn μ hε ⟨_, _, Or.inr h⟩

theorem valueIntegrable_gpgg {C : Contraction 1 1 k_gpgg} (hC : IsOnePI C) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  have hm := (isOnePI_iff_gpgg C).mp hC
  rw [onePI_gpgg_eq_relabelK] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h <;>
        first
        | with_reducible exact valueIntegrable_of_d3 P hmom αOut βIn μ hε ⟨_, _, Or.inl h⟩
        | with_reducible exact valueIntegrable_of_d3 P hmom αOut βIn μ hε ⟨_, _, Or.inr h⟩

theorem valueIntegrable_pggg {C : Contraction 1 1 k_pggg} (hC : IsOnePI C) :
    ValueIntegrable P C pOut pIn kIn αOut βIn μ := by
  have hm := (isOnePI_iff_pggg C).mp hC
  rw [onePI_pggg_eq_relabelK] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h <;>
        first
        | with_reducible exact valueIntegrable_of_d3 P hmom αOut βIn μ hε ⟨_, _, Or.inl h⟩
        | with_reducible exact valueIntegrable_of_d3 P hmom αOut βIn μ hε ⟨_, _, Or.inr h⟩

end Lists

end Terms

/-! ### The theorem -/

/-- **(HV₀) Every term of the order-`e⁵` vertex is a genuine integral** (decision D-44, item 2;
obligation O2-7). Let `ε > 0` and let the regulator fermions satisfy the Pauli–Villars conditions
`1 + c₁ + c₂ = 0` and `m² + c₁ M₁² + c₂ M₂² = 0`. Then for every 1PI contraction `C` with one
external fermion pair and one external photon whose vertices have total order exactly `5` (the
contractions summed in (HV₁)), at all external momenta with momentum conservation and all external
indices, the integrand of its value (T₁₀) satisfies (T₉′): both stages of the joint energy-first
integral (T₉) converge absolutely. -/
theorem jointEnergyFirstIntegrable_of_order_five (P : Params) (hε : 0 < P.ε)
    (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {N : ℕ} {κ : Fin N → Wick.VertexKind} (hκ : ∑ t, (κ t).order = 5)
    (C : Contraction 1 1 κ) (hC : IsOnePI C) {pOut pIn : Fin 1 → Fin 4 → ℝ}
    {kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  change ValueIntegrable P C pOut pIn kIn αOut βIn μ
  have hmem : κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 5) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hκ⟩
  have hN : N ≤ 5 := hκ ▸ le_sum_order κ
  interval_cases N
  · rw [filter_order_eq_five_zero] at hmem
    simp at hmem
  · rw [filter_order_eq_five_one] at hmem
    simp at hmem
  · rw [filter_order_eq_five_two, List.mem_toFinset] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact absurd ((isOnePI_iff_Cf C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_Cp C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_fC C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_pC C).mp hC) List.not_mem_nil
  · rw [filter_order_eq_five_three, List.mem_toFinset] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact valueIntegrable_ggC P hmom αOut βIn μ hε hC
    · exact valueIntegrable_gCg P hmom αOut βIn μ hε hC
    · exact absurd ((isOnePI_iff_gff C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_gfp C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_gpf C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_gpp C).mp hC) List.not_mem_nil
    · exact valueIntegrable_Cgg P hmom αOut βIn μ hε hC
    · exact absurd ((isOnePI_iff_fgf C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_fgp C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_ffg C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_fpg C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_pgf C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_pgp C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_pfg C).mp hC) List.not_mem_nil
    · exact absurd ((isOnePI_iff_ppg C).mp hC) List.not_mem_nil
  · rw [filter_order_eq_five_four, List.mem_toFinset] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact valueIntegrable_gggf P hmom αOut βIn μ hε hC
    · exact valueIntegrable_gggp P hmom αOut βIn μ hε hC
    · exact valueIntegrable_ggfg P hmom αOut βIn μ hε hC
    · exact valueIntegrable_ggpg P hmom αOut βIn μ hε hC
    · exact valueIntegrable_gfgg P hmom αOut βIn μ hε hC
    · exact valueIntegrable_gpgg P hmom αOut βIn μ hε hC
    · exact valueIntegrable_fggg P hmom αOut βIn μ hε hC
    · exact valueIntegrable_pggg P hmom αOut βIn μ hε hC
  · rw [filter_order_eq_five_five, Finset.mem_singleton] at hmem
    subst hmem
    exact valueIntegrable_gauges5 P hmom αOut βIn μ hε hc₁ hc₂ hC

end QED.TwoLoop.IntegrableOrderFive

end
