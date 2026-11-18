/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFunction
public import QED.Frozen.WickModel.OnePIFunction
public import QED.Frozen.TwoLoop.OnePIFunctionEqOnePIFunction
import QED.WickModel.TwoPointClassificationTree
import QED.WickModel.TwoPointClassificationSelfEnergy

/-!
# The electron conditions do not see the flavours

Proof of the Phase 5 Stage 0 embedding goal (E₅) `QED.Lepton.onePIFunction₂_one_zero`
(decision D-50), as the helper theorem `QED.Lepton.Proof.onePIFunction₂_one_zero'`.

* If every fermion field of a vertex lies on the same `σ`-cycle as an external field
  (`Reaches C`), then a flavouring preserved by `C` is the constant open-line flavouring, `C` has
  no closed fermion loop, and the regulated amplitude of `C` depends on the flavour data only
  through the open-line mass (`regulatedAmplitude₂_eq_of_reaches`).
* Every 1PI contraction of the one-electron function of order at most `3` has this property
  (`reaches_of_one_zero`): an odd total order gives an odd number of photon fields, hence no
  contraction; order `0` has no 1PI contraction; order `2` gives the `fermionCt` tree or a
  self-energy loop on two gauge vertices (packet 6a's classification).
* So, through order `3`, the one-electron function (F₈) for any flavours whose open line has mass
  `P.m` equals the function at T1's flavours, which is (T₁₁) by `rfl`, and that is (X₂₈) by the
  sealed (T₁₄).
-/

@[expose] public section

open QED.WickModel (Params Contraction IsOnePI)

namespace QED.Lepton.Proof

/-! ### Flavourings of contractions without closed loops -/

section Reaches

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- Every fermion field of a vertex lies on the `σ`-cycle of an external field: no fermion line
of `C` is closed. -/
def Reaches (C : Contraction nf nA κ) : Prop :=
  ∀ t : Wick.FermionVertex κ, ∃ i : Fin nf, C.1.1.SameCycle (.inl i) (.inr t)

/-- The constant flavouring at the open-line flavour. -/
def constFlavoring {F : Type} (Φ : Flavors F) (κ : Fin N → Wick.VertexKind) : Flavoring Φ κ :=
  ⟨fun _ => Φ.openLine, fun _ _ => rfl⟩

theorem constFlavoring_apply {F : Type} (Φ : Flavors F) (t : Wick.FermionVertex κ) :
    (constFlavoring Φ κ).1 t = Φ.openLine := rfl

theorem fermionFlavor_constFlavoring {F : Type} (Φ : Flavors F)
    (a : Fin nf ⊕ Wick.FermionVertex κ) : fermionFlavor Φ (constFlavoring Φ κ) a = Φ.openLine := by
  rcases a with i | t <;> rfl

theorem preserves_constFlavoring {F : Type} (Φ : Flavors F) (C : Contraction nf nA κ) :
    Preserves Φ C (constFlavoring Φ κ) := fun a => by
  rw [fermionFlavor_constFlavoring, fermionFlavor_constFlavoring]

/-- A preserved flavouring is constant on the cycles of `σ`. -/
theorem fermionFlavor_eq_of_sameCycle {F : Type} {Φ : Flavors F} {C : Contraction nf nA κ}
    {φ : Flavoring Φ κ} (hφ : Preserves Φ C φ) {a b : Fin nf ⊕ Wick.FermionVertex κ}
    (hab : C.1.1.SameCycle a b) : fermionFlavor Φ φ a = fermionFlavor Φ φ b := by
  have key : ∀ (z : ℤ) (x : Fin nf ⊕ Wick.FermionVertex κ),
      fermionFlavor Φ φ ((C.1.1 ^ z) x) = fermionFlavor Φ φ x := by
    intro z
    induction z using Int.induction_on with
    | zero => intro x; rfl
    | succ z ih =>
      intro x
      rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hφ]
    | pred z ih =>
      intro x
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
      have := hφ (C.1.1⁻¹ x)
      have hx : C.1.1 (C.1.1⁻¹ x) = x := by simp
      rwa [hx, eq_comm] at this
  obtain ⟨z, rfl⟩ := hab
  exact (key z a).symm

/-- When `C` has no closed fermion line, the constant flavouring is the only preserved one. -/
theorem eq_constFlavoring_of_reaches {F : Type} {Φ : Flavors F} {C : Contraction nf nA κ}
    (hC : Reaches C) {φ : Flavoring Φ κ} (hφ : Preserves Φ C φ) : φ = constFlavoring Φ κ := by
  refine Subtype.ext (funext fun t => ?_)
  obtain ⟨i, hi⟩ := hC t
  exact (fermionFlavor_eq_of_sameCycle hφ hi).symm

/-- When `C` has no closed fermion line, it has no closed loop (X₆). -/
theorem isEmpty_closedLoop_of_reaches {C : Contraction nf nA κ} (hC : Reaches C) :
    IsEmpty (QED.WickModel.ClosedLoop C) := by
  refine ⟨fun ⟨q, hq⟩ => ?_⟩
  induction q using Quotient.inductionOn with
  | h x =>
    rcases x with i | t
    · exact hq i rfl
    · obtain ⟨i, hi⟩ := hC t
      exact hq i (Quotient.sound hi)

theorem loopWeight_of_reaches {F : Type} (Φ : Flavors F) {C : Contraction nf nA κ}
    (hC : Reaches C) (φ : Flavoring Φ κ) : loopWeight Φ C φ = 1 := by
  have := isEmpty_closedLoop_of_reaches hC
  simp only [loopWeight, Finset.univ_eq_empty, Finset.prod_empty]

open scoped Classical in
/-- When `C` has no closed fermion line, its regulated amplitude (F₆) depends on the flavours
only through the open-line mass. -/
theorem regulatedAmplitude₂_eq_of_reaches (P : Params) {F G : Type} [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G] (Φ : Flavors F) (Ψ : Flavors G)
    (hmass : Φ.mass Φ.openLine = Ψ.mass Ψ.openLine) {C : Contraction nf nA κ}
    (hC : Reaches C) : regulatedAmplitude₂ P Φ C = regulatedAmplitude₂ P Ψ C := by
  funext pIn kIn k αOut βIn μ
  simp only [regulatedAmplitude₂]
  rw [Finset.sum_eq_single_of_mem (constFlavoring Φ κ)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, preserves_constFlavoring Φ C⟩)
      fun φ hφ hne => absurd (eq_constFlavoring_of_reaches hC (Finset.mem_filter.mp hφ).2) hne,
    Finset.sum_eq_single_of_mem (constFlavoring Ψ κ)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, preserves_constFlavoring Ψ C⟩)
      fun φ hφ hne => absurd (eq_constFlavoring_of_reaches hC (Finset.mem_filter.mp hφ).2) hne,
    loopWeight_of_reaches Φ hC, loopWeight_of_reaches Ψ hC]
  simp only [contractionAmplitude₂, constFlavoring_apply, hmass]

end Reaches

/-! ### The one-electron contractions through order `3` -/

theorem photonSlots_mod_two (k : Wick.VertexKind) : k.photonSlots % 2 = k.order % 2 := by
  cases k <;> rfl

theorem one_le_order (k : Wick.VertexKind) : 1 ≤ k.order := by
  cases k <;> decide

/-- A vertex sequence of odd total order has an odd number of photon fields, so without external
photons it has no contraction. -/
theorem isEmpty_contraction_of_not_two_dvd_order {nf N : ℕ} {κ : Fin N → Wick.VertexKind}
    (h : ¬ 2 ∣ ∑ t, (κ t).order) : IsEmpty (Contraction nf 0 κ) := by
  apply QED.WickModel.isEmpty_contraction_of_not_two_dvd
  rw [Fintype.card_sum, Fintype.card_fin, zero_add, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Nat.dvd_iff_mod_eq_zero, Finset.sum_nat_mod] at h ⊢
  simpa only [photonSlots_mod_two] using h

theorem card_le_sum_order {N : ℕ} (κ : Fin N → Wick.VertexKind) : N ≤ ∑ t, (κ t).order := by
  calc N = ∑ _t : Fin N, 1 := by simp
    _ ≤ ∑ t, (κ t).order := Finset.sum_le_sum fun t _ => one_le_order (κ t)

theorem sameCycle_of_apply_eq {α : Type} {σ : Equiv.Perm α} {a b : α} (h : σ a = b) :
    σ.SameCycle a b :=
  h ▸ Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl σ a)

/-- **The 1PI one-electron contractions of order at most `3` have no closed fermion line.** -/
theorem reaches_of_one_zero {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (hκ : ∑ t, (κ t).order ≤ 3) (C : Contraction 1 0 κ) (hC : IsOnePI C) : Reaches C := by
  by_cases hodd : 2 ∣ ∑ t, (κ t).order
  swap
  · exact ((isEmpty_contraction_of_not_two_dvd_order hodd).false C).elim
  have hN := card_le_sum_order κ
  obtain _ | _ | _ | N := N
  · exact absurd hC (QED.WickModel.not_isOnePI_of_fin_zero_left C)
  · obtain ⟨k, rfl⟩ : ∃ k, κ = QED.WickModel.oneVertex k := ⟨κ 0, QED.WickModel.eq_oneVertex κ⟩
    by_cases hk : k = .fermionCt
    · subst hk
      obtain rfl := (QED.WickModel.isOnePI_iff_eq_selfEnergyTree C).mp hC
      intro t
      rw [QED.WickModel.eq_ctFv t]
      exact ⟨0, sameCycle_of_apply_eq (by simp [QED.WickModel.selfEnergyTree])⟩
    · exact absurd hC (QED.WickModel.not_isOnePI_oneVertex_selfEnergy hk C)
  · by_cases h2 : ∑ t, (κ t).order ≤ 2
    · obtain rfl := QED.WickModel.eq_gauge2_of_sum_order_le h2
      obtain ⟨a, b, hab⟩ := QED.WickModel.IsOnePI.exists_isSelfEnergyLoop hC
      intro t
      refine ⟨0, ?_⟩
      have ha : C.1.1.SameCycle (.inl 0) (.inr (QED.WickModel.fv2 a)) :=
        sameCycle_of_apply_eq hab.psi_out
      rcases QED.WickModel.fv2_eq_or a b hab.ne t with rfl | rfl
      · exact ha
      · exact ha.trans (sameCycle_of_apply_eq hab.psi_a)
    · exfalso
      omega
  · exfalso
    omega

/-! ### (E₅) -/

/-- (E₅) **The electron conditions do not see the flavours.** -/
theorem onePIFunction₂_one_zero' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F)
    (hΦ : Φ.mass Φ.openLine = P.m) {K : ℕ} (hK : K ≤ 3) :
    onePIFunction₂ P Φ 1 0 K = QED.WickModel.onePIFunction P 1 0 K := by
  classical
  funext pOut pIn kIn αOut βIn μ
  rw [← QED.WickModel.onePIFunction₂_eq_onePIFunction P 1 0 K (by omega)]
  change _ = onePIFunction₂ P ⟨P.mass, P.loopCoeff, 0⟩ 1 0 K pOut pIn kIn αOut βIn μ
  unfold onePIFunction₂
  refine Finset.sum_congr rfl fun N _ => congrArg (HMul.hMul _) ?_
  refine Finset.sum_congr rfl fun κ hκ => Finset.sum_congr rfl fun C hC => ?_
  have hr := reaches_of_one_zero ((Finset.mem_filter.mp hκ).2.trans hK) C
    (Finset.mem_filter.mp hC).2
  unfold contractionValue₂
  rw [regulatedAmplitude₂_eq_of_reaches P Φ ⟨P.mass, P.loopCoeff, 0⟩ (hΦ.trans rfl) hr]

end QED.Lepton.Proof

end
