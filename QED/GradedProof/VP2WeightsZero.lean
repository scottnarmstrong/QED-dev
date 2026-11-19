/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2WeightsRelabel

/-!
# The zero-grading part of the order-four two-photon function

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2, step L0. At the
zero grading, the sum over the vertex sequences of total order `4` of the 1PI two-photon values
weighted by `sign(C)/N!` is minus the sum of the values of the seven representatives
(`zeroSum_eq`): every kind sequence of order `4` with a 1PI two-photon contraction is `gC`, `Cg`
(`N = 2`, two contractions each, one of each class `G0`, `G1`), `ggf`, `gfg`, `fgg` (`N = 3`, four
each, two of each class `F0`, `F1`) or `gggg` (`N = 4`, `72` contractions, `24` of each class `VA`,
`VB`, `VC`); the relabelled contractions have the values and signs of their representatives,
and every representative has sign `-1`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Relabel QED.TwoLoop.Enumeration QED.GradedProof.SE2
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂ fermionSign)

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (k : Fin 4 → ℝ) (μ ν : Fin 4)

/-- The value at the zero grading in the two-photon kinematics `(k, -k)`, indices `(μ, ν)`. -/
noncomputable def val0 {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 0 2 κ) : ℂ :=
  contractionValue P Φ D C 0 ![] ![] ![k, -k] ![] ![] ![μ, ν]

/-- The signed value of a contraction. -/
noncomputable def sval {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 0 2 κ) : ℂ :=
  ((fermionSign C : ℤ) : ℂ) * val0 P Φ D k μ ν C

theorem sval_relabelK {N : ℕ} {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ' (π t) = κ t) {C : Contraction 0 2 κ} (hC : IsOnePI C) :
    sval P Φ D k μ ν (relabelK π hκ C) = sval P Φ D k μ ν C := by
  unfold sval val0
  rw [fermionSign_relabelK]
  congr 1
  exact contractionValue_relabelK P Φ D π hκ hC 0 (mom_two k) _ _ _

/-! ### The representatives are 1PI -/

theorem isOnePI_repVA : IsOnePI repVA :=
  (isOnePI2_iff_gggg _).2 (by simp only [onePI2_gggg]; decide +kernel)
theorem isOnePI_repVB : IsOnePI repVB :=
  (isOnePI2_iff_gggg _).2 (by simp only [onePI2_gggg]; decide +kernel)
theorem isOnePI_repVC : IsOnePI repVC :=
  (isOnePI2_iff_gggg _).2 (by simp only [onePI2_gggg]; decide +kernel)
theorem isOnePI_repG0 : IsOnePI repG0 := (isOnePI2_iff_gC _).2 (by decide +kernel)
theorem isOnePI_repG1 : IsOnePI repG1 := (isOnePI2_iff_gC _).2 (by decide +kernel)
theorem isOnePI_repF0 : IsOnePI repF0 := (isOnePI2_iff_ggf _).2 (by decide +kernel)
theorem isOnePI_repF1 : IsOnePI repF1 := (isOnePI2_iff_ggf _).2 (by decide +kernel)

/-! ### Sums over the lists -/

/-- A finite sum over a set with the elements of a list without repetitions. -/
theorem sum_eq_list {α : Type*} [DecidableEq α] (s : Finset α) (l : List α) (hl : l.Nodup)
    (h : ∀ C, C ∈ s ↔ C ∈ l) (f : α → ℂ) : ∑ C ∈ s, f C = (l.map f).sum := by
  rw [← List.sum_toFinset f hl]
  exact Finset.sum_congr (Finset.ext fun C => by simp [h C]) fun _ _ => rfl

/-- The sum over the 1PI contractions of a kind sequence with a listed enumeration. -/
theorem sum_onePI_eq_list {N : ℕ} {κ : Fin N → Wick.VertexKind} [DecidableEq (Contraction 0 2 κ)]
    {p : Contraction 0 2 κ → Prop} [DecidablePred p] (l : List (Contraction 0 2 κ))
    (hl : l.Nodup) (hp : ∀ C, p C ↔ IsOnePI C) (h : ∀ C : Contraction 0 2 κ, IsOnePI C ↔ C ∈ l)
    (f : Contraction 0 2 κ → ℂ) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 0 2 κ)).filter p, f C = (l.map f).sum :=
  sum_eq_list _ l hl (fun C => by simp [hp C, h C]) f

theorem disjoint_of_forall {α : Type*} {l₁ l₂ : List α} (h : ∀ a ∈ l₁, a ∉ l₂) :
    l₁.Disjoint l₂ :=
  fun a h₁ h₂ => h a h₁ h₂

theorem gggg_nodup : onePI2_gggg.Nodup := by
  simp only [onePI2_gggg, onePIG0, List.nil_append]
  refine List.Nodup.append (List.Nodup.append (List.Nodup.append onePIG1_nodup onePIG2_nodup
    (disjoint_of_forall (by decide +kernel))) onePIG3_nodup ?_) onePIG4_nodup ?_
  · rw [List.disjoint_append_left]
    exact ⟨disjoint_of_forall (by decide +kernel), disjoint_of_forall (by decide +kernel)⟩
  · rw [List.disjoint_append_left, List.disjoint_append_left]
    exact ⟨⟨disjoint_of_forall (by decide +kernel), disjoint_of_forall (by decide +kernel)⟩,
      disjoint_of_forall (by decide +kernel)⟩

/-! ### The sums over the kind sequences -/

section Kinds

variable {N : ℕ} {κ : Fin N → Wick.VertexKind} {p : Contraction 0 2 κ → Prop} [DecidablePred p]

/-- The signed sum over the 1PI contractions of `κ`. -/
noncomputable def zsum (κ : Fin N → Wick.VertexKind) (p : Contraction 0 2 κ → Prop)
    [DecidablePred p] : ℂ :=
  ∑ C ∈ (Finset.univ : Finset (Contraction 0 2 κ)).filter p, sval P Φ D k μ ν C

variable {P Φ D k μ ν}

theorem zsum_gC {p : Contraction 0 2 k_gC → Prop} [DecidablePred p] (hp : ∀ C, p C ↔ IsOnePI C) :
    zsum P Φ D k μ ν k_gC p = sval P Φ D k μ ν repG0 + sval P Φ D k μ ν repG1 := by
  rw [zsum, sum_onePI_eq_list _ onePI2_gC_nodup hp isOnePI2_iff_gC, onePI2_gC_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sval_relabelK P Φ D k μ ν _ _ isOnePI_repG0, sval_relabelK P Φ D k μ ν _ _ isOnePI_repG1]
  ring

theorem zsum_Cg {p : Contraction 0 2 k_Cg → Prop} [DecidablePred p] (hp : ∀ C, p C ↔ IsOnePI C) :
    zsum P Φ D k μ ν k_Cg p = sval P Φ D k μ ν repG0 + sval P Φ D k μ ν repG1 := by
  rw [zsum, sum_onePI_eq_list _ onePI2_Cg_nodup hp isOnePI2_iff_Cg, onePI2_Cg_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sval_relabelK P Φ D k μ ν _ _ isOnePI_repG0, sval_relabelK P Φ D k μ ν _ _ isOnePI_repG1]
  ring

theorem zsum_ggf {p : Contraction 0 2 k_ggf → Prop} [DecidablePred p]
    (hp : ∀ C, p C ↔ IsOnePI C) :
    zsum P Φ D k μ ν k_ggf p = 2 * (sval P Φ D k μ ν repF0 + sval P Φ D k μ ν repF1) := by
  rw [zsum, sum_onePI_eq_list _ onePI2_ggf_nodup hp isOnePI2_iff_ggf, onePI2_ggf_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sval_relabelK P Φ D k μ ν _ _ isOnePI_repF0, sval_relabelK P Φ D k μ ν _ _ isOnePI_repF1]
  ring

theorem zsum_gfg {p : Contraction 0 2 k_gfg → Prop} [DecidablePred p]
    (hp : ∀ C, p C ↔ IsOnePI C) :
    zsum P Φ D k μ ν k_gfg p = 2 * (sval P Φ D k μ ν repF0 + sval P Φ D k μ ν repF1) := by
  rw [zsum, sum_onePI_eq_list _ onePI2_gfg_nodup hp isOnePI2_iff_gfg, onePI2_gfg_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sval_relabelK P Φ D k μ ν _ _ isOnePI_repF0, sval_relabelK P Φ D k μ ν _ _ isOnePI_repF1]
  ring

theorem zsum_fgg {p : Contraction 0 2 k_fgg → Prop} [DecidablePred p]
    (hp : ∀ C, p C ↔ IsOnePI C) :
    zsum P Φ D k μ ν k_fgg p = 2 * (sval P Φ D k μ ν repF0 + sval P Φ D k μ ν repF1) := by
  rw [zsum, sum_onePI_eq_list _ onePI2_fgg_nodup hp isOnePI2_iff_fgg, onePI2_fgg_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sval_relabelK P Φ D k μ ν _ _ isOnePI_repF0, sval_relabelK P Φ D k μ ν _ _ isOnePI_repF1]
  ring

theorem zsum_gggg {p : Contraction 0 2 k_gggg → Prop} [DecidablePred p]
    (hp : ∀ C, p C ↔ IsOnePI C) :
    zsum P Φ D k μ ν k_gggg p = 24 * (sval P Φ D k μ ν repVA + sval P Φ D k μ ν repVB +
      sval P Φ D k μ ν repVC) := by
  rw [zsum, sum_onePI_eq_list _ gggg_nodup hp isOnePI2_iff_gggg]
  simp only [onePI2_gggg, onePIG0, List.nil_append, List.map_append, List.sum_append]
  rw [onePIG1_eq_relabelK, onePIG2_eq_relabelK, onePIG3_eq_relabelK, onePIG4_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sval_relabelK P Φ D k μ ν _ _ isOnePI_repVA, sval_relabelK P Φ D k μ ν _ _ isOnePI_repVB,
    sval_relabelK P Φ D k μ ν _ _ isOnePI_repVC]
  ring

/-- A kind sequence without a 1PI two-photon contraction. -/
theorem zsum_nil {p : Contraction 0 2 κ → Prop} [DecidablePred p] (hp : ∀ C, p C ↔ IsOnePI C)
    (h : ∀ C : Contraction 0 2 κ, IsOnePI C ↔ C ∈ ([] : List (Contraction 0 2 κ))) :
    zsum P Φ D k μ ν κ p = 0 := by
  classical
  rw [zsum, sum_onePI_eq_list _ List.nodup_nil hp h]
  rfl

end Kinds

end QED.GradedProof.VP2

end
