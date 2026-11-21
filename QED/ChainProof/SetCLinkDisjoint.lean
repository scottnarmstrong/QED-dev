/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetC
public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.VPChain.IsVPChain
public import QED.Frozen.Graded.GradedOrder
public import QED.Frozen.Wick.VertexKindOrder

/-!
# Set (c), model link: sets (a), (b), (c) are disjoint at order `7`

Provider-ready proof of (MC₂) `QED.ThreeLoop.isSetC_disjoint` (decision D-58).

The three predicates (A₁) `IsSetA`, (C₁) `IsVPChain 2` and (Sc₃) `IsSetC` meet only through
the open line. (A₁) and (C₁) both fix it to `Ψ̄(y) → c → b → a → Ψ(x)` with three `gauge`
vertices, so every fermion vertex on the cycle through `Ψ(x)` is `a`, `b` or `c`
(`mem_openLine_of_sameCycle`). Then each of the three clauses of (Sc₃) leaves at most two further
vertices: a level-`0` `photonCt` or two `gauge` vertices; or none, which contradicts the
VP-share clause's counterterm vertex. So the graded order is at most `5`
(`gradedOrder_le_five_of_isSetC`), not `7`.
-/

@[expose] public section

open QED.WickModel (Contraction)

namespace QED.ChainProof.SetCLink

/-- A set closed under a permutation contains the forward orbit of each of its points. -/
theorem pow_apply_mem_of_closed {α : Type} (σ : Equiv.Perm α) (S : Set α)
    (hS : ∀ z ∈ S, σ z ∈ S) {x : α} (hx : x ∈ S) (i : ℕ) : (σ ^ i) x ∈ S := by
  induction i with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hS _ ih

/-- **The open line has three vertices**: if the fermion pairing runs
`Ψ(x) → a → b → c → Ψ̄(y)`, every fermion vertex on the cycle through `Ψ(x)` is `a`, `b` or `c`. -/
theorem mem_openLine_of_sameCycle {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    {a b c : Wick.FermionVertex κ} (h₀ : C.1.1 (.inl 0) = .inr a)
    (h₁ : C.1.1 (.inr a) = .inr b) (h₂ : C.1.1 (.inr b) = .inr c)
    (h₃ : C.1.1 (.inr c) = .inl 0) {v : Wick.FermionVertex κ}
    (hv : (C.1.1).SameCycle (.inl 0) (.inr v)) : v = a ∨ v = b ∨ v = c := by
  obtain ⟨i, hi⟩ := hv.exists_nat_pow_eq
  have hmem := pow_apply_mem_of_closed C.1.1
    {z | z = .inl 0 ∨ z = .inr a ∨ z = .inr b ∨ z = .inr c}
    (by
      rintro z (rfl | rfl | rfl | rfl)
      · exact Or.inr (Or.inl h₀)
      · exact Or.inr (Or.inr (Or.inl h₁))
      · exact Or.inr (Or.inr (Or.inr h₂))
      · exact Or.inl h₃)
    (Or.inl rfl) i
  rw [hi] at hmem
  rcases hmem with h | h | h | h
  · exact absurd h Sum.inr_ne_inl
  · exact Or.inl (Sum.inr_injective h)
  · exact Or.inr (Or.inl (Sum.inr_injective h))
  · exact Or.inr (Or.inr (Sum.inr_injective h))

/-- A sum over `insert x s` is at most the term at `x` plus the sum over `s`. -/
theorem sum_insert_le_add {α : Type} [DecidableEq α] (f : α → ℕ) (x : α) (s : Finset α) :
    ∑ t ∈ insert x s, f t ≤ f x + ∑ t ∈ s, f t := by
  by_cases hx : x ∈ s
  · rw [Finset.insert_eq_of_mem hx]
    exact Nat.le_add_left _ _
  · rw [Finset.sum_insert hx]

/-- **(Sc₃) above a three-vertex open line has graded order at most `5`.** -/
theorem gradedOrder_le_five_of_isSetC {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 1 κ) (g : Graded.Grading κ) {a b c : Wick.FermionVertex κ}
    (ha : κ a.1 = .gauge) (hb : κ b.1 = .gauge) (hc : κ c.1 = .gauge)
    (h₀ : C.1.1 (.inl 0) = .inr a) (h₁ : C.1.1 (.inr a) = .inr b)
    (h₂ : C.1.1 (.inr b) = .inr c) (h₃ : C.1.1 (.inr c) = .inl 0) (hC : ThreeLoop.IsSetC C g) :
    Graded.gradedOrder κ g ≤ 5 := by
  -- every vertex on the open line is one of `a`, `b`, `c`
  have hline : ∀ t : Fin N, (∃ v : Wick.FermionVertex κ, v.1 = t ∧
      (C.1.1).SameCycle (.inl 0) (.inr v)) → t = a.1 ∨ t = b.1 ∨ t = c.1 := by
    rintro t ⟨v, rfl, hv⟩
    rcases mem_openLine_of_sameCycle C h₀ h₁ h₂ h₃ hv with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hgline : ∀ t : Fin N, (t = a.1 ∨ t = b.1 ∨ t = c.1) → κ t = .gauge := by
    rintro t (rfl | rfl | rfl) <;> assumption
  obtain ⟨hpct, hC | hC | hC⟩ := hC
  · -- a `δ₃` element: `photonCt` at level `0`, the rest on the open line
    obtain ⟨t₀, ht₀, hall⟩ := hC
    have hT : ∀ t : Fin N, t ∈ ({t₀, a.1, b.1, c.1} : Finset (Fin N)) := by
      intro t
      rcases hall t with rfl | h
      · simp
      · rcases hline t h with rfl | rfl | rfl <;> simp
    have hct : ∀ t : Graded.CtVertex κ, g t = 0 := by
      intro t
      rcases hall t.1 with h | h
      · exact hpct t (h ▸ ht₀)
      · exact absurd (hgline _ (hline _ h)) t.2
    have hord : ∑ t, (κ t).order ≤ 5 := by
      calc ∑ t, (κ t).order ≤ ∑ t ∈ ({t₀, a.1, b.1, c.1} : Finset (Fin N)), (κ t).order :=
            Finset.sum_le_sum_of_subset fun t _ => hT t
        _ ≤ (κ t₀).order + ((κ a.1).order + ((κ b.1).order + (κ c.1).order)) := by
          refine (sum_insert_le_add _ _ _).trans (Nat.add_le_add_left ?_ _)
          refine (sum_insert_le_add _ _ _).trans (Nat.add_le_add_left ?_ _)
          refine (sum_insert_le_add _ _ _).trans ?_
          simp
        _ = 5 := by rw [ht₀, ha, hb, hc]; rfl
    unfold Graded.gradedOrder
    simpa [hct] using hord
  · -- a bubble: two `gauge` vertices, the rest on the open line
    obtain ⟨u, w, hu, hw, -, -, -, hall⟩ := hC
    have hT : ∀ t : Fin N, t ∈ ({u.1, w.1, a.1, b.1, c.1} : Finset (Fin N)) := by
      intro t
      rcases hall t with rfl | rfl | h
      · simp
      · simp
      · rcases hline t h with rfl | rfl | rfl <;> simp
    have hgauge : ∀ t : Fin N, κ t = .gauge := by
      intro t
      rcases hall t with rfl | rfl | h
      · exact hu
      · exact hw
      · exact hgline _ (hline _ h)
    have hct : ∀ t : Graded.CtVertex κ, g t = 0 := fun t => absurd (hgauge t.1) t.2
    have hord : ∑ t, (κ t).order ≤ 5 := by
      calc ∑ t, (κ t).order ≤ ∑ t ∈ ({u.1, w.1, a.1, b.1, c.1} : Finset (Fin N)), (κ t).order :=
            Finset.sum_le_sum_of_subset fun t _ => hT t
        _ ≤ (κ u.1).order + ((κ w.1).order + ((κ a.1).order + ((κ b.1).order +
              (κ c.1).order))) := by
          refine (sum_insert_le_add _ _ _).trans (Nat.add_le_add_left ?_ _)
          refine (sum_insert_le_add _ _ _).trans (Nat.add_le_add_left ?_ _)
          refine (sum_insert_le_add _ _ _).trans (Nat.add_le_add_left ?_ _)
          refine (sum_insert_le_add _ _ _).trans ?_
          simp
        _ = 5 := by rw [hu, hw, ha, hb, hc]; rfl
    unfold Graded.gradedOrder
    simpa [hct] using hord
  · -- a VP-share counterterm: every vertex is on the open line, so there is no counterterm
    obtain ⟨hall, t₀, -, -⟩ := hC
    exact absurd (hgline _ (hline _ (hall t₀.1))) t₀.2

/-- **(MC₂) Sets (a), (b), (c) are disjoint at order `7`**, in the statement of
`QED.ThreeLoop.isSetC_disjoint`. -/
theorem isSetC_disjoint {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7) :
    ¬ (ThreeLoop.IsSetC C g ∧ ThreeLoop.IsSetA C) ∧
      ¬ (ThreeLoop.IsSetC C g ∧ VPChain.IsVPChain 2 C) := by
  refine ⟨fun ⟨hC, hA⟩ => ?_, fun ⟨hC, hB⟩ => ?_⟩
  · obtain ⟨a, b, c, -, -, -, -, -, ha, hb, hc, h₀, h₁, h₂, h₃, -⟩ := hA
    have := gradedOrder_le_five_of_isSetC C g ha hb hc h₀ h₁ h₂ h₃ hC
    omega
  · obtain ⟨a, b, c, -, -, -, ha, hb, hc, h₀, h₁, h₂, h₃, -⟩ := hB
    have := gradedOrder_le_five_of_isSetC C g ha hb hc h₀ h₁ h₂ h₃ hC
    omega

end QED.ChainProof.SetCLink

end
