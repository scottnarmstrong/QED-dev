/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2SEClass
public import QED.Frozen.ThreeLoop.IsVPSelfEnergy

/-!
# Set (c), model link: the vacuum-polarization family of the T1 order-`e⁴` self-energy

Helper for the input (I3) of (WI-s) `QED.ThreeLoop.isVPShareOnShell_d₁_eq_d₂` (decision D-58).
The self-energy selection `selSE` of (Sc₂) keeps, at the zero grading, the 1PI contractions with
`SEFam C`: the vacuum-polarization self-energy `IsVPSelfEnergy C`, or no `gauge` vertex. Among
the 1PI contractions of total order `4` these are the relabellings of the three class
representatives `V`, `P0`, `P1` (`QED/GradedProof/SE2Classes.lean`).

* `OpenTwo C`: the open line is `Ψ̄(y) → c → a → Ψ(x)` with two `gauge` vertices. It is implied
  by `IsVPSelfEnergy` and pulled back along relabellings (`openTwo_of_relabelK`); the other
  representatives `R`, `X`, `F`, `C1`, `C2` fail it (checked by `decide +kernel`).
* `isVPSelfEnergy_relabelK`: `IsVPSelfEnergy` is invariant under relabelling.
* **`sum_order_four_seSelVal`**: at every T1 parameter set, the sum over the kind sequences of
  total order `4` of `(1/N!) ∑_{C 1PI} sign(C) seSelVal(C)` is
  `seVPValue = -value(V) + value(P0) + value(P1)`.
-/

@[expose] public section

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel QED.GradedProof.SE2
open QED.GradedProof.WI2 (sum_isOnePI_eq_list nodup_kinds_two nodup_kinds_three)

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The family condition of the self-energy selection `selSE`, beyond one-particle
irreducibility. -/
def SEFam (C : Contraction 1 0 κ) : Prop :=
  ThreeLoop.IsVPSelfEnergy C ∨ ∀ t, κ t ≠ .gauge

/-- The open line has two `gauge` vertices. -/
def OpenTwo (C : Contraction 1 0 κ) : Prop :=
  ∃ a c : Wick.FermionVertex κ, κ a.1 = .gauge ∧ κ c.1 = .gauge ∧
    C.1.1 (.inl 0) = .inr a ∧ C.1.1 (.inr a) = .inr c ∧ C.1.1 (.inr c) = .inl 0

theorem openTwo_of_isVPSelfEnergy {C : Contraction 1 0 κ} (h : ThreeLoop.IsVPSelfEnergy C) :
    OpenTwo C := by
  obtain ⟨a, c, -, -, -, -, ha, hc, h0, h1, h2, -⟩ := h
  exact ⟨a, c, ha, hc, h0, h1, h2⟩

section Relabel

variable {κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t)

theorem extFK_symm_inr₀ (a : Wick.FermionVertex κ') :
    (.inr a : Fin 1 ⊕ Wick.FermionVertex κ') = extFK π hκ (.inr ((fvMap π hκ).symm a)) := by
  rw [extFK_inr, Equiv.apply_symm_apply]

/-- **`OpenTwo` pulls back along a relabelling.** -/
theorem openTwo_of_relabelK {C : Contraction 1 0 κ} (h : OpenTwo (relabelK π hκ C)) :
    OpenTwo C := by
  obtain ⟨a, c, ha, hc, h0, h1, h2⟩ := h
  have hk : ∀ x : Wick.FermionVertex κ', κ ((fvMap π hκ).symm x).1 = κ' x.1 := fun x => by
    have := hκ ((fvMap π hκ).symm x).1
    rw [← this]
    congr 1
    exact congrArg Subtype.val ((fvMap π hκ).apply_symm_apply x)
  have hf : ∀ z, extFK π hκ (C.1.1 z) = (relabelK π hκ C).1.1 (extFK π hκ z) := fun z =>
    (relabelK_fst_apply π hκ C z).symm
  have inj := (extFK (nf := 1) π hκ).injective
  refine ⟨(fvMap π hκ).symm a, (fvMap π hκ).symm c, by rw [hk]; exact ha,
    by rw [hk]; exact hc, inj ?_, inj ?_, inj ?_⟩
  · rw [hf, show extFK (nf := 1) π hκ (.inl 0) = .inl 0 from rfl, h0, extFK_symm_inr₀ π hκ]
  · rw [hf, ← extFK_symm_inr₀ π hκ, h1, extFK_symm_inr₀ π hκ]
  · rw [hf, ← extFK_symm_inr₀ π hκ, h2]
    rfl

theorem relabelK_fst_inr₀ (C : Contraction 1 0 κ) (t : Wick.FermionVertex κ) :
    (relabelK π hκ C).1.1 (.inr (fvMap π hκ t)) = extFK π hκ (C.1.1 (.inr t)) :=
  relabelK_fst_apply π hκ C (.inr t)

theorem relabelK_snd_inr₀ (C : Contraction 1 0 κ) (s : Wick.PhotonSlot κ) :
    (relabelK π hκ C).1.2 (.inr (psMap π hκ s)) = extPK π hκ (C.1.2 (.inr s)) :=
  relabelK_snd_apply π hκ C (.inr s)

/-- **`IsVPSelfEnergy` is invariant under relabelling.** -/
theorem isVPSelfEnergy_relabelK {C : Contraction 1 0 κ} (h : ThreeLoop.IsVPSelfEnergy C) :
    ThreeLoop.IsVPSelfEnergy (relabelK π hκ C) := by
  obtain ⟨a, c, sa, sc, x, y, ha, hc, h0, h1, h2, hsa, hsc, hx, hy, hr⟩ := h
  have hall : ∀ P : Fin N → Prop, (∀ t, P t) → ∀ t, P (π.symm t) := fun P hP t => hP _
  refine ⟨fvMap π hκ a, fvMap π hκ c, psMap π hκ sa, psMap π hκ sc, psMap π hκ x,
    psMap π hκ y, by simp only [fvMap_val, hκ, ha], by simp only [fvMap_val, hκ, hc], ?_, ?_, ?_,
    by simp only [psMap_fst, fvMap_val, hsa], by simp only [psMap_fst, fvMap_val, hsc], ?_, ?_, ?_⟩
  · rw [show (.inl 0 : Fin 1 ⊕ Wick.FermionVertex κ') = extFK π hκ (.inl 0) from rfl,
      relabelK_fst_apply, h0, extFK_inr]
  · rw [relabelK_fst_inr₀, h1, extFK_inr]
  · rw [relabelK_fst_inr₀, h2]
    rfl
  · rw [relabelK_snd_inr₀, hx, extPK_inr]
  · rw [relabelK_snd_inr₀, hy, extPK_inr]
  · rcases hr with ⟨kx, hyx, hne, hex⟩ | ⟨kx, ky, hne, ⟨u, w, hu, hw, huw, hwu⟩, hex⟩
    · refine Or.inl ⟨by simp only [psMap_fst, hκ, kx], by simp only [psMap_fst, hyx],
        fun e => hne ((psMap π hκ).injective e), fun t => ?_⟩
      obtain ⟨t, rfl⟩ := π.surjective t
      simp only [fvMap_val, psMap_fst, π.injective.eq_iff]
      exact hex t
    · refine Or.inr ⟨by simp only [psMap_fst, hκ, kx], by simp only [psMap_fst, hκ, ky],
        by simp only [psMap_fst, ne_eq, π.injective.eq_iff, hne, not_false_eq_true],
        ⟨fvMap π hκ u, fvMap π hκ w, by simp only [fvMap_val, psMap_fst, hu],
          by simp only [fvMap_val, psMap_fst, hw], ?_, ?_⟩, fun t => ?_⟩
      · rw [relabelK_fst_inr₀, huw, extFK_inr]
      · rw [relabelK_fst_inr₀, hwu, extFK_inr]
      · obtain ⟨t, rfl⟩ := π.surjective t
        simp only [fvMap_val, psMap_fst, π.injective.eq_iff]
        exact hex t

theorem seFam_relabelK {C : Contraction 1 0 κ} (h : SEFam C) : SEFam (relabelK π hκ C) := by
  rcases h with h | h
  · exact Or.inl (isVPSelfEnergy_relabelK π hκ h)
  · refine Or.inr fun t ht => h (π.symm t) ?_
    rw [← hκ, Equiv.apply_symm_apply, ht]

theorem not_seFam_relabelK {C : Contraction 1 0 κ} (hN : ¬ OpenTwo C) (t₀ : Fin N)
    (h₀ : κ t₀ = .gauge) : ¬ SEFam (relabelK π hκ C) := by
  rintro (h | h)
  · exact hN (openTwo_of_relabelK π hκ (openTwo_of_isVPSelfEnergy h))
  · exact h (π t₀) (by rw [hκ, h₀])

end Relabel

/-! ### The selected T1 value -/

open scoped Classical in
/-- The T1 value of a contraction of the vacuum-polarization family, and `0` otherwise. -/
noncomputable def seSelVal (S : Params) (p : Fin 4 → ℝ) (α β : Fin 4)
    (C : Contraction 1 0 κ) : ℂ :=
  if SEFam C then contractionValue₂ S C ![p] ![p] ![] ![α] ![β] ![] else 0

/-- The signed T1 values of the three classes `V`, `P0`, `P1`. -/
noncomputable def seVPValue (S : Params) (p : Fin 4 → ℝ) (α β : Fin 4) : ℂ :=
  -contractionValue₂ S repV ![p] ![p] ![] ![α] ![β] ![] +
    contractionValue₂ S repP0 ![p] ![p] ![] ![α] ![β] ![] +
    contractionValue₂ S repP1 ![p] ![p] ![] ![α] ![β] ![]

/-! ### The representatives -/

theorem isVPSelfEnergy_repV : ThreeLoop.IsVPSelfEnergy repV := by
  refine ⟨fvK k_gggg 1, fvK k_gggg 0, psK k_gggg 1 0, psK k_gggg 0 0, psK k_gggg 3 0,
    psK k_gggg 2 0, ?_⟩
  decide +kernel

theorem isVPSelfEnergy_repP0 : ThreeLoop.IsVPSelfEnergy repP0 := by
  refine ⟨fvK k_ggp 1, fvK k_ggp 0, psK k_ggp 1 0, psK k_ggp 0 0, psK k_ggp 2 1,
    psK k_ggp 2 0, ?_⟩
  decide +kernel

theorem isVPSelfEnergy_repP1 : ThreeLoop.IsVPSelfEnergy repP1 := by
  refine ⟨fvK k_ggp 1, fvK k_ggp 0, psK k_ggp 1 0, psK k_ggp 0 0, psK k_ggp 2 0,
    psK k_ggp 2 1, ?_⟩
  decide +kernel

theorem not_openTwo_repR : ¬ OpenTwo repR := by
  unfold OpenTwo
  decide +kernel

theorem not_openTwo_repX : ¬ OpenTwo repX := by
  unfold OpenTwo
  decide +kernel

theorem not_openTwo_repF : ¬ OpenTwo repF := by
  unfold OpenTwo
  decide +kernel

theorem not_openTwo_repC1 : ¬ OpenTwo repC1 := by
  unfold OpenTwo
  decide +kernel

theorem not_openTwo_repC2 : ¬ OpenTwo repC2 := by
  unfold OpenTwo
  decide +kernel

/-! ### The count -/

/-- **The selected order-`4` T1 self-energy is the vacuum-polarization family.** -/
theorem sum_order_four_seSelVal
    {instD : ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind),
      DecidablePred (IsOnePI (nf := 1) (nA := 0) (κ := κ))}
    (S : Params) (p : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ N ∈ Finset.range (4 + 1), (N.factorial : ℂ)⁻¹ *
      ∑ κ ∈ (Finset.univ : Finset (Fin N → Wick.VertexKind)).filter
          (fun κ => ∑ t, (κ t).order = 4),
        ∑ C ∈ @Finset.filter (Contraction 1 0 κ) (fun C => IsOnePI C) (instD N κ) Finset.univ,
          ((fermionSign C : ℤ) : ℂ) * seSelVal S p α β C =
      seVPValue S p α β := by
  obtain rfl : instD = fun N κ => Classical.decPred _ := Subsingleton.elim _ _
  have hmom : ∑ i, (![p] : Fin 1 → Fin 4 → ℝ) i =
      ∑ i, (![p] : Fin 1 → Fin 4 → ℝ) i + ∑ j, (![] : Fin 0 → Fin 4 → ℝ) j := by simp
  have hpos : ∀ {N : ℕ} {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
      (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 1 0 κ), IsOnePI C → SEFam C →
      ((fermionSign (relabelK π hκ C) : ℤ) : ℂ) * seSelVal S p α β (relabelK π hκ C) =
        ((fermionSign C : ℤ) : ℂ) * contractionValue₂ S C ![p] ![p] ![] ![α] ![β] ![] :=
    fun π hκ C hC hF => by
      simp only [seSelVal, seFam_relabelK π hκ hF, ↓reduceIte]
      rw [fermionSign_relabelK, contractionValue₂_relabelK_of_isOnePI S π hκ hC hmom]
  have hneg : ∀ {N : ℕ} {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
      (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 1 0 κ), ¬ OpenTwo C → ∀ t₀, κ t₀ = .gauge →
      ((fermionSign (relabelK π hκ C) : ℤ) : ℂ) * seSelVal S p α β (relabelK π hκ C) = 0 :=
    fun π hκ C hN t₀ h₀ => by
      simp only [seSelVal, not_seFam_relabelK π hκ hN t₀ h₀, ↓reduceIte, mul_zero]
  obtain ⟨-, -, sV, -, sP0, sP1, -, -⟩ := fermionSign_reps
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
    List.sum_nil, List.cons_append, List.nil_append,
    hneg _ _ repR not_openTwo_repR 0 rfl, hneg _ _ repX not_openTwo_repX 0 rfl,
    hpos _ _ repV repV_isOnePI (Or.inl isVPSelfEnergy_repV),
    hneg _ _ repF not_openTwo_repF 0 rfl,
    hpos _ _ repP0 repP0_isOnePI (Or.inl isVPSelfEnergy_repP0),
    hpos _ _ repP1 repP1_isOnePI (Or.inl isVPSelfEnergy_repP1),
    hneg _ _ repC1 not_openTwo_repC1 0 rfl, hneg _ _ repC2 not_openTwo_repC2 0 rfl,
    sV, sP0, sP1]
  simp only [seVPValue, Nat.factorial]
  push_cast
  ring

end QED.ChainProof.SetCLink

end
