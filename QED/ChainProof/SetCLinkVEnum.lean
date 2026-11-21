/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.EnumWitness
public import QED.TwoLoop.RelabelCountertermClasses
public import QED.LeptonProof.HMVertex

/-!
# Set (c), model link: the vacuum-polarization family of the T1 order-`e⁵` vertex

Helper for the input (I2) of (G-ex-s) `QED.ThreeLoop.existsUnique_isVPShareOnShell` (decision
D-58). The vertex selection `selV` of (Sc₂) keeps, at the zero grading, the 1PI contractions with
`VPFam C`: the one-insertion chain (C₁) `IsVPChain 1 C`, or no `gauge` vertex. Among the 1PI
contractions of total order `5` these are the relabellings of three class representatives: the
vacuum-polarization class `VP` of five gauge vertices and the two `δ₃` classes `d3Slot0`,
`d3Slot1` (`QED/TwoLoop/RelabelCountertermClasses.lean`).

* `OpenThree C`: the open line is `Ψ̄(y) → c → b → a → Ψ(x)` with three `gauge` vertices. It is
  implied by (C₁) (`openThree_of_isVPChain`) and pulled back along relabellings
  (`openThree_of_relabelK`); the other representatives fail it (checked by `decide +kernel`).
* `selVal S … C`: the T1 value of `C` if `VPFam C`, else `0`; relabelling invariant on the
  relabellings of the representatives.
* **`sum_order_five_selVal`**: at every T1 parameter set, under momentum conservation, the sum over
  the kind sequences of total order `5` of `(1/N!) ∑_{C 1PI} sign(C) selVal(C)` is
  `vpFamValue = -value(VP) + value(d3Slot0) + value(d3Slot1)`, each class with coefficient one.
-/

@[expose] public section

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel QED.VPChain

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The family condition of the vertex selection `selV`, beyond one-particle irreducibility. -/
def VPFam (C : Contraction 1 1 κ) : Prop :=
  IsVPChain 1 C ∨ ∀ t, κ t ≠ .gauge

/-- The open line has three `gauge` vertices. -/
def OpenThree (C : Contraction 1 1 κ) : Prop :=
  ∃ a b c : Wick.FermionVertex κ, κ a.1 = .gauge ∧ κ b.1 = .gauge ∧ κ c.1 = .gauge ∧
    C.1.1 (.inl 0) = .inr a ∧ C.1.1 (.inr a) = .inr b ∧ C.1.1 (.inr b) = .inr c ∧
    C.1.1 (.inr c) = .inl 0

theorem openThree_of_isVPChain {n : ℕ} {C : Contraction 1 1 κ} (h : IsVPChain n C) :
    OpenThree C := by
  obtain ⟨a, b, c, -, -, -, ha, hb, hc, h0, h1, h2, h3, -⟩ := h
  exact ⟨a, b, c, ha, hb, hc, h0, h1, h2, h3⟩

section Relabel

variable {κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t)

theorem extFK_symm_inr (a : Wick.FermionVertex κ') :
    (.inr a : Fin 1 ⊕ Wick.FermionVertex κ') = extFK π hκ (.inr ((fvMap π hκ).symm a)) := by
  rw [extFK_inr, Equiv.apply_symm_apply]

/-- **`OpenThree` pulls back along a relabelling.** -/
theorem openThree_of_relabelK {C : Contraction 1 1 κ} (h : OpenThree (relabelK π hκ C)) :
    OpenThree C := by
  obtain ⟨a, b, c, ha, hb, hc, h0, h1, h2, h3⟩ := h
  have hk : ∀ x : Wick.FermionVertex κ', κ ((fvMap π hκ).symm x).1 = κ' x.1 := fun x => by
    have := hκ ((fvMap π hκ).symm x).1
    rw [← this]
    congr 1
    exact congrArg Subtype.val ((fvMap π hκ).apply_symm_apply x)
  have hf : ∀ z, extFK π hκ (C.1.1 z) = (relabelK π hκ C).1.1 (extFK π hκ z) := fun z =>
    (relabelK_fst_apply π hκ C z).symm
  have inj := (extFK (nf := 1) π hκ).injective
  refine ⟨(fvMap π hκ).symm a, (fvMap π hκ).symm b, (fvMap π hκ).symm c, by rw [hk]; exact ha,
    by rw [hk]; exact hb, by rw [hk]; exact hc, inj ?_, inj ?_, inj ?_, inj ?_⟩
  · rw [hf, show extFK (nf := 1) π hκ (.inl 0) = .inl 0 from rfl, h0, extFK_symm_inr π hκ]
  · rw [hf, ← extFK_symm_inr π hκ, h1, extFK_symm_inr π hκ]
  · rw [hf, ← extFK_symm_inr π hκ, h2, extFK_symm_inr π hκ]
  · rw [hf, ← extFK_symm_inr π hκ, h3]
    rfl

theorem vpFam_relabelK {C : Contraction 1 1 κ} (h : VPFam C) : VPFam (relabelK π hκ C) := by
  rcases h with h | h
  · exact Or.inl (Enum.isVPChain_relabelK π hκ h)
  · refine Or.inr fun t ht => h (π.symm t) ?_
    rw [← hκ, Equiv.apply_symm_apply, ht]

theorem not_vpFam_relabelK {C : Contraction 1 1 κ} (hN : ¬ OpenThree C) (t₀ : Fin N)
    (h₀ : κ t₀ = .gauge) : ¬ VPFam (relabelK π hκ C) := by
  rintro (h | h)
  · exact hN (openThree_of_relabelK π hκ (openThree_of_isVPChain h))
  · exact h (π t₀) (by rw [hκ, h₀])

end Relabel

/-! ### The selected T1 value -/

open scoped Classical in
/-- The T1 value of a contraction of the vacuum-polarization family, and `0` otherwise. -/
noncomputable def selVal (S : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) (C : Contraction 1 1 κ) : ℂ :=
  if VPFam C then contractionValue₂ S C pOut pIn kIn αOut βIn μ else 0

/-- The signed T1 values of the three classes of the vacuum-polarization family. -/
noncomputable def vpFamValue (S : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) : ℂ :=
  (Class5.VP.sign : ℂ) * contractionValue₂ S Class5.VP.rep pOut pIn kIn αOut βIn μ +
    contractionValue₂ S repD3Slot0 pOut pIn kIn αOut βIn μ +
    contractionValue₂ S repD3Slot1 pOut pIn kIn αOut βIn μ

section Value

variable (S : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
  (αOut βIn μ : Fin 1 → Fin 4)
include hmom

theorem selVal_relabelK_pos {κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ' (π t) = κ t) {C : Contraction 1 1 κ} (hC : IsOnePI C) (h : VPFam C) :
    selVal S pOut pIn kIn αOut βIn μ (relabelK π hκ C) =
      contractionValue₂ S C pOut pIn kIn αOut βIn μ := by
  simp only [selVal, vpFam_relabelK π hκ h, ↓reduceIte, value_relabelK S hmom hC]

omit hmom in
theorem selVal_relabelK_neg {κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ' (π t) = κ t) {C : Contraction 1 1 κ} (hN : ¬ OpenThree C) (t₀ : Fin N)
    (h₀ : κ t₀ = .gauge) : selVal S pOut pIn kIn αOut βIn μ (relabelK π hκ C) = 0 := by
  simp only [selVal, not_vpFam_relabelK π hκ hN t₀ h₀, ↓reduceIte]

end Value

/-! ### The representatives -/

/-- The fermion vertex `t` of five gauge vertices. -/
def gv5 (t : Fin 5) : Wick.FermionVertex (gauges 5) :=
  ⟨t, fun h => Wick.VertexKind.noConfusion h⟩

/-- The photon field of the gauge vertex `t`. -/
def gp5 (t : Fin 5) : Wick.PhotonSlot (gauges 5) := ⟨t, ⟨0, Nat.one_pos⟩⟩

theorem isVPChain_VP : IsVPChain 1 Class5.VP.rep := by
  refine ⟨gv5 2, gv5 1, gv5 0, gp5 1, ![gp5 2, gp5 3], ![gp5 4, gp5 0], ?_⟩
  decide +kernel

theorem isVPChain_d3Slot0 : IsVPChain 1 repD3Slot0 := by
  refine ⟨fvK k_gggp 2, fvK k_gggp 1, fvK k_gggp 0, psK k_gggp 1 0,
    ![psK k_gggp 2 0, psK k_gggp 3 0], ![psK k_gggp 3 1, psK k_gggp 0 0], ?_⟩
  decide +kernel

theorem isVPChain_d3Slot1 : IsVPChain 1 repD3Slot1 := by
  refine ⟨fvK k_gggp 2, fvK k_gggp 1, fvK k_gggp 0, psK k_gggp 1 0,
    ![psK k_gggp 2 0, psK k_gggp 3 1], ![psK k_gggp 3 0, psK k_gggp 0 0], ?_⟩
  decide +kernel

theorem not_openThree_class5 : ∀ c : Class5, c ≠ .VP → ¬ OpenThree c.rep := by
  unfold OpenThree
  decide +kernel

theorem not_openThree_d2In : ¬ OpenThree repD2In := by
  unfold OpenThree
  decide +kernel

theorem not_openThree_d2Out : ¬ OpenThree repD2Out := by
  unfold OpenThree
  decide +kernel

theorem not_openThree_d1At1 : ¬ OpenThree repD1At1 := by
  unfold OpenThree
  decide +kernel

theorem not_openThree_d1At2 : ¬ OpenThree repD1At2 := by
  unfold OpenThree
  decide +kernel

theorem not_openThree_d1At3 : ¬ OpenThree repD1At3 := by
  unfold OpenThree
  decide +kernel

theorem relabel_eq_relabelK {nf nA : ℕ} (π : Equiv.Perm (Fin N))
    (C : Contraction nf nA (gauges N)) : relabel π C = relabelK π (fun _ => rfl) C := rfl

/-! ### The count -/

section Count

variable (S : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
  (αOut βIn μ : Fin 1 → Fin 4)
include hmom

theorem sum_class5_selVal :
    ∑ c : Class5, (c.sign : ℂ) *
        ∑ π : Equiv.Perm (Fin 5), selVal S pOut pIn kIn αOut βIn μ (relabel π c.rep) =
      (Nat.factorial 5 : ℂ) * ((Class5.VP.sign : ℂ) *
        contractionValue₂ S Class5.VP.rep pOut pIn kIn αOut βIn μ) := by
  rw [Finset.sum_eq_single Class5.VP]
  · simp only [relabel_eq_relabelK, selVal_relabelK_pos S hmom αOut βIn μ _ _
      (rep_isOnePI _) (Or.inl isVPChain_VP), Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    ring
  · intro c _ hc
    simp only [relabel_eq_relabelK, selVal_relabelK_neg S αOut βIn μ _ _
      (not_openThree_class5 c hc) 0 rfl, Finset.sum_const_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The vacuum-polarization family of the T1 order-`e⁵` vertex with coefficient one per
class**, as the order-`5` functional `orderFiveSum` of `selVal`. -/
theorem sum_order_five_selVal :
    QED.Lepton.Proof.HM.orderFiveSum (fun _ _ C => selVal S pOut pIn kIn αOut βIn μ C) =
      vpFamValue S pOut pIn kIn αOut βIn μ := by
  unfold QED.Lepton.Proof.HM.orderFiveSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [filter_order_eq_five_zero, filter_order_eq_five_one, filter_order_eq_five_two,
    filter_order_eq_five_three, filter_order_eq_five_four, filter_order_eq_five_five,
    List.sum_toFinset _ nodup_two, List.sum_toFinset _ nodup_three,
    List.sum_toFinset _ nodup_four, Finset.sum_singleton, Finset.sum_empty, Finset.sum_empty]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [sum_isOnePI_Cf, sum_isOnePI_Cp, sum_isOnePI_fC, sum_isOnePI_pC, sum_isOnePI_ggC,
    sum_isOnePI_gCg, sum_isOnePI_gff, sum_isOnePI_gfp, sum_isOnePI_gpf, sum_isOnePI_gpp,
    sum_isOnePI_Cgg, sum_isOnePI_fgf, sum_isOnePI_fgp, sum_isOnePI_ffg, sum_isOnePI_fpg,
    sum_isOnePI_pgf, sum_isOnePI_pgp, sum_isOnePI_pfg, sum_isOnePI_ppg, sum_isOnePI_gggf,
    sum_isOnePI_gggp, sum_isOnePI_ggfg, sum_isOnePI_ggpg, sum_isOnePI_gfgg, sum_isOnePI_gpgg,
    sum_isOnePI_fggg, sum_isOnePI_pggg, sum_isOnePI_gauges5]
  simp only [onePI_Cf, onePI_Cp, onePI_fC, onePI_pC, onePI_gff, onePI_gfp, onePI_gpf,
    onePI_gpp, onePI_fgf, onePI_fgp, onePI_ffg, onePI_fpg, onePI_pgf, onePI_pgp, onePI_pfg,
    onePI_ppg, List.map_nil, List.sum_nil]
  rw [sum_class5_selVal S hmom, onePI_gggf_eq_relabelK, onePI_ggfg_eq_relabelK,
    onePI_gfgg_eq_relabelK, onePI_fggg_eq_relabelK, onePI_gggp_eq_relabelK,
    onePI_ggpg_eq_relabelK, onePI_gpgg_eq_relabelK, onePI_pggg_eq_relabelK,
    onePI_ggC_eq_relabelK, onePI_gCg_eq_relabelK, onePI_Cgg_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    selVal_relabelK_pos S hmom αOut βIn μ _ _ repD3Slot0_isOnePI (Or.inl isVPChain_d3Slot0),
    selVal_relabelK_pos S hmom αOut βIn μ _ _ repD3Slot1_isOnePI (Or.inl isVPChain_d3Slot1),
    selVal_relabelK_neg S αOut βIn μ _ _ not_openThree_d2In 0 rfl,
    selVal_relabelK_neg S αOut βIn μ _ _ not_openThree_d2Out 0 rfl,
    selVal_relabelK_neg S αOut βIn μ _ _ not_openThree_d1At1 0 rfl,
    selVal_relabelK_neg S αOut βIn μ _ _ not_openThree_d1At2 0 rfl,
    selVal_relabelK_neg S αOut βIn μ _ _ not_openThree_d1At3 0 rfl]
  simp only [vpFamValue, Nat.factorial]
  push_cast
  ring

end Count

end QED.ChainProof.SetCLink

end
