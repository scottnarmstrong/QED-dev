/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetA
public import QED.ChainProof.EnumWitness

/-!
# The closed loop of a set (a) contraction

Helper for the Phase 5 Stage 3a enumeration (decision D-58), the loop branch of (A₁)
`QED.ThreeLoop.IsSetA`: the vertex `u` of the insertion field `x` lies on a cycle of the fermion
pairing `σ` without external field, and every vertex off the open line lies on it.

* `QED.ChainProof.SetALink.mem_of_sameCycle_of_mapsTo`: a finite set containing `p` and mapped
  into itself by a permutation contains the whole cycle of `p`. With the walk `u, σ u, σ² u, …`
  this pins the cycle of `u` once the walk returns to `u`.
* `QED.ChainProof.SetALink.loop_step`: `σ` maps a vertex on the cycle of `u` to a vertex on it;
  `ne_of_sameCycle`: such a vertex is not the open-line vertex `a` (nor, by the same argument
  with `σ a = b`, `σ b = c`, the vertices `b`, `c`).
-/

@[expose] public section

namespace QED.ChainProof.SetALink

open QED.WickModel QED.ChainProof.Enum

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **A finite set mapped into itself by `σ` contains the cycles of its points.** -/
theorem mem_of_sameCycle_of_mapsTo {α : Type*} [DecidableEq α] {σ : Equiv.Perm α}
    {T : Finset α} (hT : ∀ t ∈ T, σ t ∈ T) {p r : α} (hp : p ∈ T) (h : σ.SameCycle p r) :
    r ∈ T := by
  have hinv : ∀ t ∈ T, σ⁻¹ t ∈ T := by
    have hs : T.image σ = T :=
      Finset.eq_of_subset_of_card_le (fun t ht => by
        obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 ht
        exact hT t' ht') (by rw [Finset.card_image_of_injective _ σ.injective])
    intro t ht
    rw [← hs] at ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 ht
    simpa using ht'
  obtain ⟨i, rfl⟩ := h
  induction i using Int.induction_on with
  | zero => simpa using hp
  | succ k ih =>
    rw [show (k : ℤ) + 1 = 1 + k by ring, zpow_add, zpow_one, Equiv.Perm.mul_apply]
    exact hT _ ih
  | pred k ih =>
    rw [show -(k : ℤ) - 1 = -1 + -k by ring, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
    exact hinv _ ih

/-- **One step along the loop.** If the cycle of `u` contains no external field, then `σ` maps
a vertex `v` on the cycle of `u` to a vertex `v'` on it. -/
theorem loop_step (C : Contraction 1 1 κ) {u v : Wick.FermionVertex κ}
    (hsep : ¬ (C.1.1).SameCycle (.inl 0) (.inr u))
    (hv : (C.1.1).SameCycle (.inr u) (.inr v)) :
    ∃ v' : Wick.FermionVertex κ, C.1.1 (.inr v) = .inr v' ∧
      (C.1.1).SameCycle (.inr u) (.inr v') := by
  have hstep : (C.1.1).SameCycle (.inr u) (C.1.1 (.inr v)) :=
    hv.trans (Equiv.Perm.SameCycle.refl _ _).apply_right
  rcases e : C.1.1 (.inr v) with i | v'
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [e] at hstep
    exact absurd hstep.symm hsep
  · exact ⟨v', rfl, e ▸ hstep⟩

/-- A vertex on the cycle of `u` is not the vertex `a` paired with the external `Ψ(x)`. -/
theorem ne_of_sameCycle (C : Contraction 1 1 κ) {a u v : Wick.FermionVertex κ}
    (s0a : C.1.1 (.inl 0) = .inr a) (hsep : ¬ (C.1.1).SameCycle (.inl 0) (.inr u))
    (hv : (C.1.1).SameCycle (.inr u) (.inr v)) : v ≠ a := by
  rintro rfl
  have h0 : (C.1.1).SameCycle (.inl 0) (.inr v) := ⟨1, by simpa using s0a⟩
  exact hsep (h0.trans hv.symm)

end QED.ChainProof.SetALink

end
