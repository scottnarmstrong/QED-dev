/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0Entry
public import QED.GradedProof.X0Product

/-!
# (X₀): (T₉′) for a two-loop contraction whose loops share no line

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), step X0d (the
`sixList` contractions: two one-loop self-energies). Suppose that in the frozen routing (T₄) no
line carries both loop momenta. Then for every choice of the spinor and Lorentz indices the
summand of the amplitude (T₇) of a contraction of `gauge` vertices is a constant (the vertex
factors and the lines carrying no loop momentum) times a product `A(ℓ₀) B(ℓ₁)` of propagator
entries; each factor satisfies (T₉′) at one loop if its lines pass the one-loop count
(`jointEnergyFirstIntegrable_entries`), and the product does by Fubini
(`jointEnergyFirstIntegrable_mul`). The hypotheses are decided on the line data (`SepCrit`), and
`jointEnergyFirstIntegrable_of_sepCrit` gives (T₉′) for any masses and `ε > 0`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.WickModel
open QED.TwoLoop.Enumeration (lineData mem_lineData)

/-- (T₉′) for a finite sum, without weights. -/
theorem jointEnergyFirstIntegrable_sum' {ι : Type*} (s : Finset ι) {L : ℕ}
    {G : ι → (Fin L → Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegrable L (G i)) :
    QED.TwoLoop.jointEnergyFirstIntegrable L fun ℓ => ∑ i ∈ s, G i ℓ := by
  simpa using SE2.jointEnergyFirstIntegrable_sum s (fun _ => 1) G h

/-- A product over a finite type, split along two predicates. -/
theorem prod_split3 {T : Type*} [Fintype T] (a b : T → Prop) [DecidablePred a] [DecidablePred b]
    (h : T → ℂ) :
    ∏ t, h t = (∏ t ∈ Finset.univ.filter a, h t) *
      ((∏ t ∈ Finset.univ.filter (fun t => ¬ a t ∧ b t), h t) *
        ∏ t ∈ Finset.univ.filter (fun t => ¬ a t ∧ ¬ b t), h t) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ a,
    ← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter fun t => ¬ a t) b,
    Finset.filter_filter, Finset.filter_filter]

/-- A product over lines each carrying at most one of two loop momenta, split by the loop
momentum carried. -/
theorem prod_sep {T : Type*} [Fintype T] (X : T → (Fin 4 → ℝ) → ℂ) (c₀ c₁ : T → ℤ)
    (hF : ∀ f, c₀ f = 0 ∨ c₁ f = 0) (p : T → Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ f, X f ((c₀ f : ℝ) • ℓ 0 + (c₁ f : ℝ) • ℓ 1 + p f) =
      (∏ f ∈ Finset.univ.filter (fun f => c₀ f ≠ 0), X f ((c₀ f : ℝ) • ℓ 0 + p f)) *
        ((∏ f ∈ Finset.univ.filter (fun f => ¬ c₀ f ≠ 0 ∧ c₁ f ≠ 0),
          X f ((c₁ f : ℝ) • ℓ 1 + p f)) *
        ∏ f ∈ Finset.univ.filter (fun f => ¬ c₀ f ≠ 0 ∧ ¬ c₁ f ≠ 0), X f (p f)) := by
  classical
  rw [prod_split3 (fun f => c₀ f ≠ 0) (fun f => c₁ f ≠ 0)]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun f hf => ?_)
    (congrArg₂ (· * ·) (Finset.prod_congr rfl fun f hf => ?_)
      (Finset.prod_congr rfl fun f hf => ?_))
  · rcases hF f with h | h
    · exact absurd h (Finset.mem_filter.mp hf).2
    · simp [h]
  · simp [not_not.mp (Finset.mem_filter.mp hf).2.1]
  · simp [not_not.mp (Finset.mem_filter.mp hf).2.1, not_not.mp (Finset.mem_filter.mp hf).2.2]

/-- **(T₉′) for a product of propagator entries whose lines each carry at most one of two loop
momenta.** -/
theorem jointEnergyFirstIntegrable_sepEntries {F G : Type*} [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G] (c₀ c₁ : F → ℤ) (d₀ d₁ : G → ℤ)
    (hF : ∀ f, c₀ f = 0 ∨ c₁ f = 0) (hG : ∀ g, d₀ g = 0 ∨ d₁ g = 0) (pF : F → Fin 4 → ℝ)
    (MF : F → ℝ) (aF bF : F → Fin 4) (pG : G → Fin 4 → ℝ) (μG νG : G → Fin 4) (mγ Λ : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (h₀F : (Finset.univ.filter fun f => c₀ f ≠ 0).card ≤ 3)
    (h₀ : 4 < (Finset.univ.filter fun f => c₀ f ≠ 0).card +
      4 * (Finset.univ.filter fun g => d₀ g ≠ 0).card)
    (h₁F : (Finset.univ.filter fun f => ¬ c₀ f ≠ 0 ∧ c₁ f ≠ 0).card ≤ 3)
    (h₁ : 4 < (Finset.univ.filter fun f => ¬ c₀ f ≠ 0 ∧ c₁ f ≠ 0).card +
      4 * (Finset.univ.filter fun g => ¬ d₀ g ≠ 0 ∧ d₁ g ≠ 0).card) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      (∏ f, (1 / I) * QED.OneLoop.electronPropagator (MF f) ε
        ((c₀ f : ℝ) • ℓ 0 + (c₁ f : ℝ) • ℓ 1 + pF f) (aF f) (bF f)) *
      ∏ g, (1 / I) * QED.OneLoop.photonPropagator mγ Λ ε
        ((d₀ g : ℝ) • ℓ 0 + (d₁ g : ℝ) • ℓ 1 + pG g) (μG g) (νG g) := by
  set F0 := Finset.univ.filter fun f => c₀ f ≠ 0
  set F1 := Finset.univ.filter fun f => ¬ c₀ f ≠ 0 ∧ c₁ f ≠ 0
  set Fn := Finset.univ.filter fun f => ¬ c₀ f ≠ 0 ∧ ¬ c₁ f ≠ 0
  set G0 := Finset.univ.filter fun g => d₀ g ≠ 0
  set G1 := Finset.univ.filter fun g => ¬ d₀ g ≠ 0 ∧ d₁ g ≠ 0
  set Gn := Finset.univ.filter fun g => ¬ d₀ g ≠ 0 ∧ ¬ d₁ g ≠ 0
  have hA : QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ' =>
      (∏ f : F0, (1 / I) * QED.OneLoop.electronPropagator (MF f.1) ε
        ((c₀ f.1 : ℝ) • ℓ' 0 + pF f.1) (aF f.1) (bF f.1)) *
      ∏ g : G0, (1 / I) * QED.OneLoop.photonPropagator mγ Λ ε
        ((d₀ g.1 : ℝ) • ℓ' 0 + pG g.1) (μG g.1) (νG g.1) :=
    jointEnergyFirstIntegrable_entries (fun f : F0 => (c₀ f.1 : ℝ))
      (fun f => Int.cast_ne_zero.mpr (Finset.mem_filter.mp f.2).2) _ _ _ _
      (fun g : G0 => (d₀ g.1 : ℝ)) (fun g => Int.cast_ne_zero.mpr (Finset.mem_filter.mp g.2).2)
      _ _ _ mγ Λ hε (by rwa [Fintype.card_coe]) (by rwa [Fintype.card_coe, Fintype.card_coe])
  have hB : QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ' =>
      (∏ f : F1, (1 / I) * QED.OneLoop.electronPropagator (MF f.1) ε
        ((c₁ f.1 : ℝ) • ℓ' 0 + pF f.1) (aF f.1) (bF f.1)) *
      ∏ g : G1, (1 / I) * QED.OneLoop.photonPropagator mγ Λ ε
        ((d₁ g.1 : ℝ) • ℓ' 0 + pG g.1) (μG g.1) (νG g.1) :=
    jointEnergyFirstIntegrable_entries (fun f : F1 => (c₁ f.1 : ℝ))
      (fun f => Int.cast_ne_zero.mpr (Finset.mem_filter.mp f.2).2.2) _ _ _ _
      (fun g : G1 => (d₁ g.1 : ℝ))
      (fun g => Int.cast_ne_zero.mpr (Finset.mem_filter.mp g.2).2.2)
      _ _ _ mγ Λ hε (by rwa [Fintype.card_coe]) (by rwa [Fintype.card_coe, Fintype.card_coe])
  have hK := QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul
    ((∏ f ∈ Fn, (1 / I) * QED.OneLoop.electronPropagator (MF f) ε (pF f) (aF f) (bF f)) *
      ∏ g ∈ Gn, (1 / I) * QED.OneLoop.photonPropagator mγ Λ ε (pG g) (μG g) (νG g))
    (jointEnergyFirstIntegrable_mul hA hB)
  refine (congrArg _ (funext fun ℓ => ?_)).mp hK
  have hXF := prod_sep (fun f k => (1 / I) * QED.OneLoop.electronPropagator (MF f) ε k (aF f)
    (bF f)) c₀ c₁ hF pF ℓ
  have hYG := prod_sep (fun g k => (1 / I) * QED.OneLoop.photonPropagator mγ Λ ε k (μG g) (νG g))
    d₀ d₁ hG pG ℓ
  have a0 := Finset.prod_coe_sort F0 fun f => (1 / I) * QED.OneLoop.electronPropagator (MF f) ε
    ((c₀ f : ℝ) • ℓ 0 + pF f) (aF f) (bF f)
  have a1 := Finset.prod_coe_sort F1 fun f => (1 / I) * QED.OneLoop.electronPropagator (MF f) ε
    ((c₁ f : ℝ) • ℓ 1 + pF f) (aF f) (bF f)
  have b0 := Finset.prod_coe_sort G0 fun g => (1 / I) * QED.OneLoop.photonPropagator mγ Λ ε
    ((d₀ g : ℝ) • ℓ 0 + pG g) (μG g) (νG g)
  have b1 := Finset.prod_coe_sort G1 fun g => (1 / I) * QED.OneLoop.photonPropagator mγ Λ ε
    ((d₁ g : ℝ) • ℓ 1 + pG g) (μG g) (νG g)
  beta_reduce at hXF hYG a0 a1 b0 b1
  have hc0 : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := rfl
  have hc1 : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := rfl
  simp only [hc0, hc1]
  rw [hXF, hYG, a0, a1, b0, b1]
  ring

/-! ### The criterion on the line data -/

section Edges

variable {N : ℕ}

/-- The number of edges of a given kind (fermion or photon) satisfying a predicate. -/
def edgeCount (E : Multiset (ℕ × Fin N × Fin N)) (fer : Bool) (p : ℕ × Fin N × Fin N → Prop)
    [DecidablePred p] : ℕ :=
  (E.map fun y => if decide (y.1 < N) = fer ∧ p y then 1 else 0).sum

/-- **The separated criterion**: no edge carries both loop momenta, and the edges along each
loop momentum pass the one-loop count (at most three fermion edges, and `4 < #fermion +
4 #photon`). -/
def SepCrit (E : Multiset (ℕ × Fin N × Fin N)) : Prop :=
  (∀ x ∈ E, edgeCoeff E x 0 = 0 ∨ edgeCoeff E x 1 = 0) ∧
    edgeCount E true (fun y => edgeCoeff E y 0 ≠ 0) ≤ 3 ∧
    4 < edgeCount E true (fun y => edgeCoeff E y 0 ≠ 0) +
      4 * edgeCount E false (fun y => edgeCoeff E y 0 ≠ 0) ∧
    edgeCount E true (fun y => ¬ edgeCoeff E y 0 ≠ 0 ∧ edgeCoeff E y 1 ≠ 0) ≤ 3 ∧
    4 < edgeCount E true (fun y => ¬ edgeCoeff E y 0 ≠ 0 ∧ edgeCoeff E y 1 ≠ 0) +
      4 * edgeCount E false (fun y => ¬ edgeCoeff E y 0 ≠ 0 ∧ edgeCoeff E y 1 ≠ 0)

instance (E : Multiset (ℕ × Fin N × Fin N)) : Decidable (SepCrit E) := by
  unfold SepCrit; infer_instance

end Edges

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}

theorem card_filter_fermion (p : ℕ × Fin N × Fin N → Prop) [DecidablePred p] :
    (Finset.univ.filter fun f : FermionLine C => p (edgeOf (.inl f : Line C))).card =
      edgeCount (lineData C) true p := by
  classical
  rw [edgeCount, sum_lineData, Finset.card_filter, Fintype.sum_sum_type]
  have h0 : ∀ g : PhotonLine C, ¬ (edgeOf (Sum.inr g : Line C)).1 < N := fun g => by
    simp [label_lt_iff]
  simp only [h0, decide_false, Bool.false_eq_true, false_and, ite_false, Finset.sum_const_zero,
    add_zero]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [label_lt_iff, Sum.isLeft_inl, decide_true, true_and]

theorem card_filter_photon (p : ℕ × Fin N × Fin N → Prop) [DecidablePred p] :
    (Finset.univ.filter fun g : PhotonLine C => p (edgeOf (.inr g : Line C))).card =
      edgeCount (lineData C) false p := by
  classical
  rw [edgeCount, sum_lineData, Finset.card_filter, Fintype.sum_sum_type]
  have h0 : ∀ f : FermionLine C, (edgeOf (Sum.inl f : Line C)).1 < N := fun f => by
    simp [label_lt_iff]
  simp only [h0, decide_true, Bool.true_eq_false, false_and, ite_false, Finset.sum_const_zero,
    zero_add]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : ¬ (edgeOf (Sum.inr g : Line C)).1 < N := by simp [label_lt_iff]
  simp only [h1, decide_false, true_and]

/-- **(T₉′) for a two-loop contraction of `gauge` vertices passing the separated criterion**,
for any masses and `ε > 0`. -/
theorem jointEnergyFirstIntegrable_of_sepCrit (P : Params) (hε : 0 < P.ε)
    (hκ : ∀ t, κ t = .gauge) (φ : Flavoring κ) (hcrit : SepCrit (lineData C))
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) (c : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      c * contractionAmplitude₂ P C φ pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ := by
  classical
  obtain ⟨hsep, h0F, h0, h1F, h1⟩ := hcrit
  have hsep' : ∀ l : Line C, edgeCoeff (lineData C) (edgeOf l) 0 = 0 ∨
      edgeCoeff (lineData C) (edgeOf l) 1 = 0 := fun l =>
    hsep _ (mem_lineData.mpr ⟨l, rfl⟩)
  have hk : ∀ (ℓ : Fin 2 → Fin 4 → ℝ) (l : Line C), lineMomentum₂ C pOut pIn kIn ℓ l =
      ((edgeCoeff (lineData C) (edgeOf l) 0 : ℤ) : ℝ) • ℓ 0 +
        ((edgeCoeff (lineData C) (edgeOf l) 1 : ℤ) : ℝ) • ℓ 1 +
        extPart C pOut pIn kIn l := by
    intro ℓ l
    rw [lineMomentum₂_eq_loopCoeff, Fin.sum_univ_two]
    rfl
  set p0 : ℕ × Fin N × Fin N → Prop := fun y => edgeCoeff (lineData C) y 0 ≠ 0 with hp0
  set p1 : ℕ × Fin N × Fin N → Prop := fun y => ¬ edgeCoeff (lineData C) y 0 ≠ 0 ∧
    edgeCoeff (lineData C) y 1 ≠ 0 with hp1
  unfold contractionAmplitude₂
  simp only [Finset.mul_sum]
  refine jointEnergyFirstIntegrable_sum' _ fun α _ => jointEnergyFirstIntegrable_sum' _ fun β _ =>
    jointEnergyFirstIntegrable_sum' _ fun lor _ => ?_
  have hv : ∀ ℓ : Fin 2 → Fin 4 → ℝ, (∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
      (psiMomentum₂ C pIn (lineMomentum₂ C pOut pIn kIn ℓ))
      (photonMomentum₂ C kIn (lineMomentum₂ C pOut pIn kIn ℓ)) t) =
      ∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor 0 0 t := fun ℓ =>
    Finset.prod_congr rfl fun t _ => vertexFactor_eq_of_gauge _ _ _ _ _ _ _ _ _ _ _ _ _ t (hκ t)
  have h := jointEnergyFirstIntegrable_sepEntries (F := FermionLine C) (G := PhotonLine C)
    (fun f => edgeCoeff (lineData C) (edgeOf (.inl f : Line C)) 0)
    (fun f => edgeCoeff (lineData C) (edgeOf (.inl f : Line C)) 1)
    (fun g => edgeCoeff (lineData C) (edgeOf (.inr g : Line C)) 0)
    (fun g => edgeCoeff (lineData C) (edgeOf (.inr g : Line C)) 1)
    (fun f => hsep' _) (fun g => hsep' _) (fun f => extPart C pOut pIn kIn (.inl f))
    (fun f => P.mass (φ.1 f.1)) (fun f => β f.1) (fun f => α f.tail)
    (fun g => extPart C pOut pIn kIn (.inr g)) (fun g => lor g.1) (fun g => lor g.head) P.mγ P.Λ hε
    (by have e1 := card_filter_fermion (C := C) p0; beta_reduce at e1 ⊢; rw [e1]; exact h0F)
    (by
      have e1 := card_filter_fermion (C := C) p0
      have e2 := card_filter_photon (C := C) p0
      beta_reduce at e1 e2 ⊢; rw [e1, e2]; exact h0)
    (by have e1 := card_filter_fermion (C := C) p1; beta_reduce at e1 ⊢; rw [e1]; exact h1F)
    (by
      have e1 := card_filter_fermion (C := C) p1
      have e2 := card_filter_photon (C := C) p1
      beta_reduce at e1 e2 ⊢; rw [e1, e2]; exact h1)
  have h' := QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul
    (c * ((if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
          (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
          (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
      ∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor 0 0 t)) h
  refine (congrArg _ (funext fun ℓ => ?_)).mp h'
  simp only [hv, hk]
  ring

end QED.GradedProof.X0

end
