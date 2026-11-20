/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CAmpGen
public import QED.GradedProof.X1CLinesIn
public import QED.GradedProof.Embed

/-!
# (X₁) piece C: flavours and closed loops of `glueIn`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C3 (value factorization).

* `zpow_apply_of_comm`, `not_sameCycle_map`, `sameCycle_of_map`: a map intertwining two
  permutations off the cycle of a point `z₀` intertwines their powers there, and moves cycles
  into cycles.
* `openPathIn_left`, `openPathIn_right`: the open cycles of the pieces lie on the open cycle of
  `glueIn e C₁ C₂` (the open fermion path runs through `C₁` to the bridge, then through `C₂`).
* `preserves_glueIn_iff`: `glueIn e C₁ C₂` preserves `φ` iff the pieces preserve `flL φ`,
  `flR φ`.
* `loopWeight_glueIn`: the closed loops of the glue are those of the pieces, so the regulator
  weight is multiplicative.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction ClosedLoop)
open QED.Graded
open Equiv.Perm (SameCycle)

/-! ### Intertwining maps -/

section Intertwine

variable {X Y : Type*} {σ : Equiv.Perm X} {τ : Equiv.Perm Y} {f : X → Y} {z₀ : X}
  (hcomm : ∀ z, ¬ SameCycle σ z z₀ → τ (f z) = f (σ z))

include hcomm in
theorem zpow_apply_of_comm (n : ℤ) : ∀ z, ¬ SameCycle σ z z₀ → (τ ^ n) (f z) = f ((σ ^ n) z) := by
  induction n using Int.induction_on with
  | zero => intro z _; rfl
  | succ n ih =>
    intro z hz
    rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hcomm z hz,
      ih (σ z) (by rwa [Equiv.Perm.sameCycle_apply_left])]
  | pred n ih =>
    intro z hz
    have hz' : ¬ SameCycle σ (σ.symm z) z₀ := by rwa [Equiv.Perm.sameCycle_symm_apply_left]
    have h1 : τ.symm (f z) = f (σ.symm z) := by
      rw [Equiv.symm_apply_eq, hcomm _ hz', Equiv.apply_symm_apply]
    rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_def, Equiv.Perm.inv_def, h1, ih _ hz']

include hcomm in
theorem not_sameCycle_map (hf : Function.Injective f) {z : X} (hz : ¬ SameCycle σ z z₀) :
    ¬ SameCycle τ (f z) (f z₀) := by
  rintro ⟨n, hn⟩
  rw [zpow_apply_of_comm hcomm n z hz] at hn
  exact hz ⟨n, hf hn⟩

include hcomm in
theorem sameCycle_of_map (hf : Function.Injective f) {z w : X} (hz : ¬ SameCycle σ z z₀)
    (h : SameCycle τ (f z) (f w)) : SameCycle σ z w := by
  obtain ⟨n, hn⟩ := h
  rw [zpow_apply_of_comm hcomm n z hz] at hn
  exact ⟨n, hf hn⟩

include hcomm in
theorem sameCycle_map {z w : X} (hz : ¬ SameCycle σ z z₀) (h : SameCycle σ z w) :
    SameCycle τ (f z) (f w) := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n, zpow_apply_of_comm hcomm n z hz⟩

end Intertwine

/-! ### The open cycle of `glueIn` -/

variable {N N₁ N₂ nA : ℕ} {F : Type} {κ : Fin N → Wick.VertexKind}
  {e : Fin N₁ ⊕ Fin N₂ ≃ Fin N}
  (C₁ : Contraction 1 nA (leftKinds κ e)) (C₂ : Contraction 1 0 (rightKinds κ e))
  {a : Wick.FermionVertex (leftKinds κ e)} {c : Wick.FermionVertex (rightKinds κ e)}
  (ha : C₁.1.1 (.inr a) = .inl 0) (hc : C₂.1.1 (.inl 0) = .inr c)

include ha in
theorem glueIn_comm_left {z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)} (hz : z ≠ .inr a) :
    (glueIn e C₁ C₂).1.1 (fL κ e 1 (.inl z)) = fL κ e 1 (.inl (C₁.1.1 z)) := by
  rcases h : C₁.1.1 z with i | t
  · refine absurd (C₁.1.1.injective ?_) hz
    rw [h, ha, Subsingleton.elim i 0]
  · rw [glueIn_left C₁ C₂ h, fL_inl_inr]

theorem glueIn_comm_right (z : Wick.FermionVertex (rightKinds κ e)) :
    (glueIn e C₁ C₂).1.1 (fR κ e 1 (.inr (.inr z))) = fR κ e 1 (.inr (C₂.1.1 (.inr z))) := by
  rw [fR_inr_inr, glueIn_right]

include ha in
theorem openPathIn_left (n : ℕ) :
    SameCycle (glueIn e C₁ C₂).1.1 (fL κ e 1 (.inl ((C₁.1.1 ^ n) (.inl 0)))) (.inl 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    by_cases hw : (C₁.1.1 ^ n) (.inl 0) = .inr a
    · rw [hw, ha]
      rfl
    · rw [← glueIn_comm_left C₁ C₂ ha hw, Equiv.Perm.sameCycle_apply_left]
      exact ih

include ha hc in
theorem openPathIn_right (n : ℕ) :
    SameCycle (glueIn e C₁ C₂).1.1 (fR κ e 1 (.inr ((C₂.1.1 ^ n) (.inl 0)))) (.inl 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    rcases hw : (C₂.1.1 ^ n) (.inl 0) with i | t
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rw [hc, fR_inr_inr]
      have h := openPathIn_left C₁ C₂ ha 1
      rw [pow_one, Equiv.Perm.sameCycle_comm] at h
      have h2 := glueIn_bridge C₁ C₂ ha hc
      rw [← h2, Equiv.Perm.sameCycle_apply_left]
      have h3 : C₁.1.1.SameCycle (.inr a) (.inl 0) := ⟨1, by simp [ha]⟩
      obtain ⟨m, hm⟩ := (Equiv.Perm.SameCycle.symm h3).exists_nat_pow_eq
      have h4 := openPathIn_left C₁ C₂ ha m
      rwa [hm] at h4
    · rw [← glueIn_comm_right C₁ C₂ t, Equiv.Perm.sameCycle_apply_left]
      rw [hw] at ih
      exact ih

theorem fermionFlavor_fL (Φ : Lepton.Flavors F) (φ : Flavoring F κ)
    (z : Fin 1 ⊕ Wick.FermionVertex (leftKinds κ e)) :
    fermionFlavor Φ φ (fL κ e 1 (.inl z)) = fermionFlavor Φ (flL κ e φ) z := by
  rcases z with i | t <;> rfl

theorem fermionFlavor_fR (Φ : Lepton.Flavors F) (φ : Flavoring F κ)
    (z : Fin 1 ⊕ Wick.FermionVertex (rightKinds κ e)) :
    fermionFlavor Φ φ (fR κ e 1 (.inr z)) = fermionFlavor Φ (flR κ e φ) z := by
  rcases z with i | t <;> rfl

include ha hc in
/-- **`glueIn` preserves a flavouring iff the pieces preserve its restrictions.** -/
theorem preserves_glueIn_iff (Φ : Lepton.Flavors F) (φ : Flavoring F κ) :
    Preserves Φ (glueIn e C₁ C₂) φ ↔
      Preserves Φ C₁ (flL κ e φ) ∧ Preserves Φ C₂ (flR κ e φ) := by
  have hA : SameCycle (glueIn e C₁ C₂).1.1 (fL κ e 1 (.inl (.inr a))) (.inl 0) := by
    have h3 : C₁.1.1.SameCycle (.inl 0) (.inr a) :=
      Equiv.Perm.SameCycle.symm (⟨1, by simp [ha]⟩ : C₁.1.1.SameCycle (.inr a) (.inl 0))
    obtain ⟨m, hm⟩ := h3.exists_nat_pow_eq
    have h4 := openPathIn_left C₁ C₂ ha m
    rwa [hm] at h4
  have hC : SameCycle (glueIn e C₁ C₂).1.1 (fR κ e 1 (.inr (.inr c))) (.inl 0) := by
    have h := openPathIn_right C₁ C₂ ha hc 1
    rwa [pow_one, hc] at h
  constructor
  · intro hφ
    have hfa : flL κ e φ a = Φ.openLine := by
      have := fermionFlavor_eq_of_sameCycle hφ hA
      rwa [fermionFlavor_fL] at this
    have hfc : flR κ e φ c = Φ.openLine := by
      have := fermionFlavor_eq_of_sameCycle hφ hC
      rwa [fermionFlavor_fR] at this
    refine ⟨fun z => ?_, fun z => ?_⟩
    · by_cases hz : z = .inr a
      · subst hz
        rw [ha]
        exact hfa.symm
      · have := hφ (fL κ e 1 (.inl z))
        rwa [glueIn_comm_left C₁ C₂ ha hz, fermionFlavor_fL, fermionFlavor_fL] at this
    · rcases z with i | t
      · have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        rw [hc]
        exact hfc
      · have := hφ (fR κ e 1 (.inr (.inr t)))
        rwa [glueIn_comm_right, fermionFlavor_fR, fermionFlavor_fR] at this
  · rintro ⟨h₁, h₂⟩ z
    rcases z with i | t
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      have := h₁ (.inl 0)
      rw [← fermionFlavor_fL Φ φ, ← fermionFlavor_fL Φ φ,
        ← glueIn_comm_left C₁ C₂ ha (by simp)] at this
      exact this
    · obtain ⟨x, rfl⟩ := (fvSplit κ e).surjective t
      rcases x with t | t
      · by_cases ht : t = a
        · subst ht
          rw [glueIn_bridge C₁ C₂ ha hc]
          have h1 := h₁ (.inr t)
          have h2 := h₂ (.inl 0)
          rw [ha] at h1
          rw [hc] at h2
          change flR κ e φ c = flL κ e φ t
          exact h2.trans h1
        · have := h₁ (.inr t)
          rw [← fermionFlavor_fL Φ φ, ← fermionFlavor_fL Φ φ,
            ← glueIn_comm_left C₁ C₂ ha (by simpa using ht)] at this
          exact this
      · have := h₂ (.inr t)
        rw [← fermionFlavor_fR Φ φ, ← fermionFlavor_fR Φ φ, ← glueIn_comm_right] at this
        exact this

end QED.GradedProof.X1C

end
