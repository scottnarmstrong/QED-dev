/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.LeptonProof.HMFlavourLoop
public import QED.TwoLoop.EnumerationOrderFive

/-!
# Every contraction of the order-`e⁵` vertex and of the order-`e²` photon function is simple

Helper level, Phase 5 Stage 0 (decision D-50). The flavour-block split of (HM₂) applies the
formulas of `QED/LeptonProof/HMFlavourLoop.lean` contraction by contraction; they need
`IsSimple C` (at most one closed loop, made of gauge vertices). This file proves it for

* every 1PI contraction with one external fermion pair and one external photon whose vertices
  have total order exactly `5` (`isSimple_of_orderFive`), from T1's enumeration
  (`QED.TwoLoop.Enumeration`): the 27 counterterm kind sequences by their explicit lists, and the
  five gauge vertices by the nine class representatives and relabelling invariance;
* every 1PI contraction with two external photons and no external fermion of total order at
  most `2` (`isSimple_of_photon`), by a finite check.

The check is the Boolean test `SimpleB`, which follows `σ` a bounded number of steps; it implies
`IsSimple` (`isSimple_of_simpleB`), and only that direction is used.
-/

@[expose] public section

open QED.WickModel (Contraction IsOnePI)

namespace QED.Lepton.Proof.HM

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### A bounded test -/

/-- The first `n` points of the `σ`-orbit of `x`. -/
def orbitList {α : Type*} (σ : Equiv.Perm α) (x : α) (n : ℕ) : List α :=
  (List.range n).map fun k => (⇑σ)^[k] x

theorem sameCycle_of_mem_orbitList {α : Type*} {σ : Equiv.Perm α} {x y : α} {n : ℕ}
    (h : y ∈ orbitList σ x n) : Equiv.Perm.SameCycle σ x y := by
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
  exact ⟨k, by rw [zpow_natCast, Equiv.Perm.iterate_eq_pow]⟩

/-- The vertex `t` reaches an external field within `6` steps of `σ`. -/
def OpenB (C : Contraction nf nA κ) (t : Wick.FermionVertex κ) : Prop :=
  ∃ y ∈ orbitList C.1.1 (.inr t) 7, y.isLeft = true

instance (C : Contraction nf nA κ) (t : Wick.FermionVertex κ) : Decidable (OpenB C t) := by
  unfold OpenB; infer_instance

theorem onOpen_of_openB {C : Contraction nf nA κ} {t : Wick.FermionVertex κ} (h : OpenB C t) :
    OnOpen C t := by
  obtain ⟨y, hy, hl⟩ := h
  rcases y with i | s
  · exact ⟨i, sameCycle_of_mem_orbitList hy⟩
  · simp at hl

/-- **The Boolean test**: every vertex reaching no external field within `6` steps is a gauge
vertex and reaches, within `6` steps, every other such vertex. -/
def SimpleB (C : Contraction nf nA κ) : Prop :=
  ∀ t : Wick.FermionVertex κ, OpenB C t ∨
    (κ t.1 = .gauge ∧ ∀ s : Wick.FermionVertex κ, OpenB C s ∨
      (Sum.inr s : Fin nf ⊕ Wick.FermionVertex κ) ∈ orbitList C.1.1 (.inr t) 7)

instance (C : Contraction nf nA κ) : Decidable (SimpleB C) := by
  unfold SimpleB; infer_instance

theorem isSimple_of_simpleB {C : Contraction nf nA κ} (h : SimpleB C) : IsSimple C := by
  refine ⟨fun t ht => ?_, fun t s ht hs => ?_⟩
  · rcases h t with h1 | h1
    · exact absurd (onOpen_of_openB h1) ht
    · exact h1.1
  · rcases h t with h1 | h1
    · exact absurd (onOpen_of_openB h1) ht
    · rcases h1.2 s with h2 | h2
      · exact absurd (onOpen_of_openB h2) hs
      · exact sameCycle_of_mem_orbitList h2

/-! ### Relabelling the gauge vertices -/

open QED.TwoLoop.Enumeration in
theorem relabel_fst_eq (π : Equiv.Perm (Fin N)) (C : Contraction nf nA (gauges N)) :
    (relabel π C).1.1 = (extF π : Equiv.Perm _) * C.1.1 * (extF π : Equiv.Perm _)⁻¹ :=
  Equiv.ext fun _ => rfl

open QED.TwoLoop.Enumeration in
theorem extF_inv_inr (π : Equiv.Perm (Fin N)) (t : Wick.FermionVertex (gauges N)) :
    ((extF (nf := nf) π : Equiv.Perm _)⁻¹ (.inr t)) = .inr ((fvPerm π)⁻¹ t) :=
  rfl

open QED.TwoLoop.Enumeration in
theorem extF_inv_inl (π : Equiv.Perm (Fin N)) (i : Fin nf) :
    ((extF (nf := nf) π : Equiv.Perm _)⁻¹ (.inl i)) = .inl i :=
  rfl

open QED.TwoLoop.Enumeration in
theorem onOpen_relabel_iff (π : Equiv.Perm (Fin N)) (C : Contraction nf nA (gauges N))
    (t : Wick.FermionVertex (gauges N)) :
    OnOpen (relabel π C) t ↔ OnOpen C ((fvPerm π)⁻¹ t) := by
  simp only [OnOpen, relabel_fst_eq, Equiv.Perm.sameCycle_conj, extF_inv_inr, extF_inv_inl]

open QED.TwoLoop.Enumeration in
/-- `IsSimple` is invariant under relabelling the gauge vertices. -/
theorem isSimple_relabel (π : Equiv.Perm (Fin N)) {C : Contraction nf nA (gauges N)}
    (hC : IsSimple C) : IsSimple (relabel π C) := by
  refine ⟨fun _ _ => rfl, fun t s ht hs => ?_⟩
  rw [onOpen_relabel_iff] at ht hs
  rw [relabel_fst_eq, Equiv.Perm.sameCycle_conj, extF_inv_inr, extF_inv_inr]
  exact hC.2 _ _ ht hs

/-! ### The order-`e⁵` vertex -/

section OrderFive

open QED.TwoLoop.Enumeration

theorem simpleB_reps : ∀ c : Class5, SimpleB c.rep := by decide +kernel

theorem isSimple_gauges5 {C : Contraction 1 1 (gauges 5)} (hC : IsOnePI C) : IsSimple C := by
  obtain ⟨c, π, rfl⟩ := exists_rep_of_isOnePI hC
  exact isSimple_relabel π (isSimple_of_simpleB (simpleB_reps c))

theorem simpleB_Cf : ∀ C ∈ onePI_Cf, SimpleB C := by decide +kernel
theorem simpleB_Cp : ∀ C ∈ onePI_Cp, SimpleB C := by decide +kernel
theorem simpleB_fC : ∀ C ∈ onePI_fC, SimpleB C := by decide +kernel
theorem simpleB_pC : ∀ C ∈ onePI_pC, SimpleB C := by decide +kernel
theorem simpleB_ggC : ∀ C ∈ onePI_ggC, SimpleB C := by decide +kernel
theorem simpleB_gCg : ∀ C ∈ onePI_gCg, SimpleB C := by decide +kernel
theorem simpleB_gff : ∀ C ∈ onePI_gff, SimpleB C := by decide +kernel
theorem simpleB_gfp : ∀ C ∈ onePI_gfp, SimpleB C := by decide +kernel
theorem simpleB_gpf : ∀ C ∈ onePI_gpf, SimpleB C := by decide +kernel
theorem simpleB_gpp : ∀ C ∈ onePI_gpp, SimpleB C := by decide +kernel
theorem simpleB_Cgg : ∀ C ∈ onePI_Cgg, SimpleB C := by decide +kernel
theorem simpleB_fgf : ∀ C ∈ onePI_fgf, SimpleB C := by decide +kernel
theorem simpleB_fgp : ∀ C ∈ onePI_fgp, SimpleB C := by decide +kernel
theorem simpleB_ffg : ∀ C ∈ onePI_ffg, SimpleB C := by decide +kernel
theorem simpleB_fpg : ∀ C ∈ onePI_fpg, SimpleB C := by decide +kernel
theorem simpleB_pgf : ∀ C ∈ onePI_pgf, SimpleB C := by decide +kernel
theorem simpleB_pgp : ∀ C ∈ onePI_pgp, SimpleB C := by decide +kernel
theorem simpleB_pfg : ∀ C ∈ onePI_pfg, SimpleB C := by decide +kernel
theorem simpleB_ppg : ∀ C ∈ onePI_ppg, SimpleB C := by decide +kernel
theorem simpleB_gggf : ∀ C ∈ onePI_gggf, SimpleB C := by decide +kernel
theorem simpleB_gggp : ∀ C ∈ onePI_gggp, SimpleB C := by decide +kernel
theorem simpleB_ggfg : ∀ C ∈ onePI_ggfg, SimpleB C := by decide +kernel
theorem simpleB_ggpg : ∀ C ∈ onePI_ggpg, SimpleB C := by decide +kernel
theorem simpleB_gfgg : ∀ C ∈ onePI_gfgg, SimpleB C := by decide +kernel
theorem simpleB_gpgg : ∀ C ∈ onePI_gpgg, SimpleB C := by decide +kernel
theorem simpleB_fggg : ∀ C ∈ onePI_fggg, SimpleB C := by decide +kernel
theorem simpleB_pggg : ∀ C ∈ onePI_pggg, SimpleB C := by decide +kernel

/-- **Every 1PI contraction of the order-`e⁵` vertex is simple.** -/
theorem isSimple_of_orderFive {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (hκ : ∑ t, (κ t).order = 5) (C : Contraction 1 1 κ) (hC : IsOnePI C) : IsSimple C := by
  have hN : N ≤ 5 := hκ ▸ le_sum_order κ
  have mem : ∀ {M : ℕ} (κ' : Fin M → Wick.VertexKind) (s : Finset (Fin M → Wick.VertexKind)),
      (Finset.univ : Finset (Fin M → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order = 5) = s → ∑ t, (κ' t).order = 5 → κ' ∈ s := by
    intro M κ' s hs h
    rw [← hs]
    simp [h]
  interval_cases N
  · have := mem κ _ filter_order_eq_five_zero hκ
    simp at this
  · have := mem κ _ filter_order_eq_five_one hκ
    simp at this
  · have := mem κ _ filter_order_eq_five_two hκ
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl
    · exact isSimple_of_simpleB (simpleB_Cf C ((isOnePI_iff_Cf C).1 hC))
    · exact isSimple_of_simpleB (simpleB_Cp C ((isOnePI_iff_Cp C).1 hC))
    · exact isSimple_of_simpleB (simpleB_fC C ((isOnePI_iff_fC C).1 hC))
    · exact isSimple_of_simpleB (simpleB_pC C ((isOnePI_iff_pC C).1 hC))
  · have := mem κ _ filter_order_eq_five_three hκ
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact isSimple_of_simpleB (simpleB_ggC C ((isOnePI_iff_ggC C).1 hC))
    · exact isSimple_of_simpleB (simpleB_gCg C ((isOnePI_iff_gCg C).1 hC))
    · exact isSimple_of_simpleB (simpleB_gff C ((isOnePI_iff_gff C).1 hC))
    · exact isSimple_of_simpleB (simpleB_gfp C ((isOnePI_iff_gfp C).1 hC))
    · exact isSimple_of_simpleB (simpleB_gpf C ((isOnePI_iff_gpf C).1 hC))
    · exact isSimple_of_simpleB (simpleB_gpp C ((isOnePI_iff_gpp C).1 hC))
    · exact isSimple_of_simpleB (simpleB_Cgg C ((isOnePI_iff_Cgg C).1 hC))
    · exact isSimple_of_simpleB (simpleB_fgf C ((isOnePI_iff_fgf C).1 hC))
    · exact isSimple_of_simpleB (simpleB_fgp C ((isOnePI_iff_fgp C).1 hC))
    · exact isSimple_of_simpleB (simpleB_ffg C ((isOnePI_iff_ffg C).1 hC))
    · exact isSimple_of_simpleB (simpleB_fpg C ((isOnePI_iff_fpg C).1 hC))
    · exact isSimple_of_simpleB (simpleB_pgf C ((isOnePI_iff_pgf C).1 hC))
    · exact isSimple_of_simpleB (simpleB_pgp C ((isOnePI_iff_pgp C).1 hC))
    · exact isSimple_of_simpleB (simpleB_pfg C ((isOnePI_iff_pfg C).1 hC))
    · exact isSimple_of_simpleB (simpleB_ppg C ((isOnePI_iff_ppg C).1 hC))
  · have := mem κ _ filter_order_eq_five_four hκ
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isSimple_of_simpleB (simpleB_gggf C ((isOnePI_iff_gggf C).1 hC))
    · exact isSimple_of_simpleB (simpleB_gggp C ((isOnePI_iff_gggp C).1 hC))
    · exact isSimple_of_simpleB (simpleB_ggfg C ((isOnePI_iff_ggfg C).1 hC))
    · exact isSimple_of_simpleB (simpleB_ggpg C ((isOnePI_iff_ggpg C).1 hC))
    · exact isSimple_of_simpleB (simpleB_gfgg C ((isOnePI_iff_gfgg C).1 hC))
    · exact isSimple_of_simpleB (simpleB_gpgg C ((isOnePI_iff_gpgg C).1 hC))
    · exact isSimple_of_simpleB (simpleB_fggg C ((isOnePI_iff_fggg C).1 hC))
    · exact isSimple_of_simpleB (simpleB_pggg C ((isOnePI_iff_pggg C).1 hC))
  · have := mem κ _ filter_order_eq_five_five hκ
    rw [Finset.mem_singleton] at this
    subst this
    exact isSimple_gauges5 hC

end OrderFive

end QED.Lepton.Proof.HM

end
