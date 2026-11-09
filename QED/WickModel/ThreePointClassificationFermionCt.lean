/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointClassificationBasic

/-!
# The fermion counterterm on an electron leg

The connected contractions of the three-point function `connectedFunction P 1 1 3` (packet 6a,
decision D-24) with one gauge vertex `g` and one fermion counterterm vertex `h` (the sequences
`[gauge, fermionCt]` and `[fermionCt, gauge]`). The external photon is contracted with the photon
field of `g`, and a connected contraction is a fermion chain through both vertices:

* `IsCtChain C a b`: the fermion line runs `Ψ̄(y) → b → a → Ψ(x)`.
* With `a = g`, the counterterm sits on the incoming leg: the value is
  `[i e γ^μ (1/i) S̃(p)]_{αγ} [-i (δ₂ p̸ + δ_m m)]_{γβ}`.
* With `a = h`, it sits on the outgoing leg: the value is
  `[-i (δ₂ p̸' + δ_m m)]_{αγ} [(1/i) S̃(p') i e γ^μ]_{γβ}`.

Both have fermionic sign `+1`, and their single internal line is a bridge, so they are not 1PI.

## Main statements

* `isBridge_of_forall_eq`, `contractionValue_of_forall_eq`, `lineMomentum_of_forall_eq`: a
  contraction with a single internal line, which is not a self-loop.
* `sum_nonOnePI_fermionCt`: the sum over the connected contractions that are not 1PI.
-/

@[expose] public section

open Complex

namespace QED.WickModel

/-! ### A single internal line -/

section SingleLine

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction nf nA κ}

/-- The only internal line of a contraction is a bridge unless it is a self-loop. -/
theorem isBridge_of_forall_eq {f₀ : Line C} (hall : ∀ g, g = f₀)
    (hne : f₀.ends.1 ≠ f₀.ends.2) : IsBridge f₀ :=
  isBridge_of_closed {f₀.ends.1} rfl (fun h' => hne (Set.mem_singleton_iff.mp h').symm)
    fun g hg => absurd (hall g) hg

/-- A contraction whose only internal line is a bridge has no loop line. -/
theorem not_isLoopLine_of_forall_eq {f₀ : Line C} (hall : ∀ g, g = f₀)
    (hne : f₀.ends.1 ≠ f₀.ends.2) (g : Line C) : ¬ IsLoopLine g := fun h =>
  h.1 (by rw [hall g]; exact isBridge_of_forall_eq hall hne)

/-- A contraction whose only internal line is a bridge has the value of its regulated amplitude at
zero loop momentum. -/
theorem contractionValue_of_forall_eq (P : Params) {f₀ : Line C} (hall : ∀ g, g = f₀)
    (hne : f₀.ends.1 ≠ f₀.ends.2) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue P C pOut pIn kIn αOut βIn μ =
      regulatedAmplitude P C pOut pIn kIn 0 αOut βIn μ := by
  rw [contractionValue, ite_eq_right fun ⟨g, hg⟩ => not_isLoopLine_of_forall_eq hall hne g hg]

/-- The only internal line of a contraction, if it is not a self-loop, carries the momentum
injected at its tail. -/
theorem lineMomentum_of_forall_eq {f₀ : Line C} (hall : ∀ g, g = f₀)
    (hne : f₀.ends.1 ≠ f₀.ends.2) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) :
    lineMomentum C pOut pIn kIn ℓ f₀ = externalMomentum C pOut pIn kIn f₀.ends.1 := by
  rw [lineMomentum_of_forall_not_joined (not_isLoopLine_of_forall_eq hall hne f₀)
    (fun w ⟨g, hg, _⟩ => absurd (Or.inl (hall g)) hg)]
  simp [not_isLoopLine_of_forall_eq hall hne]

end SingleLine

/-! ### Fermion chains through two vertices -/

section Chain

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The fermion line of `C` runs `Ψ̄(y) → b → a → Ψ(x)`: the external `Ψ(x)` is contracted with
`Ψ̄_a`, `Ψ_a` with `Ψ̄_b`, and `Ψ_b` with the external `Ψ̄(y)`. -/
def IsCtChain (C : Contraction 1 nA κ) (a b : Wick.FermionVertex κ) : Prop :=
  C.1.1 (.inl 0) = .inr a ∧ C.1.1 (.inr a) = .inr b ∧ C.1.1 (.inr b) = .inl 0

namespace IsCtChain

variable {C : Contraction 1 nA κ} {a b : Wick.FermionVertex κ}

/-- The fermion pairing of a chain. -/
theorem fst_eq (hC : IsCtChain C a b) (hab : a ≠ b) (hX : ∀ x, x = a ∨ x = b) :
    C.1.1 = Equiv.swap (.inl 0) (.inr b) * Equiv.swap (.inl 0) (.inr a) := by
  ext1 x
  rcases x with i | t
  · rw [Subsingleton.elim i 0, hC.1, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (Sum.inr_injective.ne hab)]
  · rcases hX t with rfl | rfl
    · rw [hC.2.1, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
    · rw [hC.2.2, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (Sum.inr_injective.ne hab.symm),
        Equiv.swap_apply_right]

/-- A chain through the two fermion vertices has fermionic sign `+1`: `(-1)²` from the vertices
times the sign `+1` of a 3-cycle. -/
theorem fermionSign_eq (hC : IsCtChain C a b) (hab : a ≠ b) (hX : ∀ x, x = a ∨ x = b) :
    fermionSign C = 1 := by
  have hcard : Fintype.card (Wick.FermionVertex κ) = 2 := by
    rw [← Finset.card_univ, show (Finset.univ : Finset (Wick.FermionVertex κ)) = {a, b} by
      ext x; simpa using hX x, Finset.card_pair hab]
  rw [fermionSign, hcard, hC.fst_eq hab hX, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap Sum.inl_ne_inr, Equiv.Perm.sign_swap Sum.inl_ne_inr]
  simp

/-- The internal fermion line of a chain, from `b` to `a`. -/
def line (hC : IsCtChain C a b) : FermionLine C := ⟨a, by simp [hC.2.1]⟩

/-- The fermion line is indexed by the `Ψ` of `a`. -/
@[simp]
theorem line_val (hC : IsCtChain C a b) : hC.line.1 = a := rfl

/-- The fermion line starts at `b`. -/
@[simp]
theorem tail_line (hC : IsCtChain C a b) : hC.line.tail = b := FermionLine.tail_eq hC.2.1

/-- The fermion line runs from `b` to `a`. -/
theorem ends_line (hC : IsCtChain C a b) : Line.ends (.inl hC.line : Line C) = (b.1, a.1) := by
  change (hC.line.tail.1, hC.line.1.1) = (b.1, a.1)
  rw [tail_line]
  rfl

/-- The fermion line is the only internal fermion line. -/
theorem eq_line (hC : IsCtChain C a b) (hX : ∀ x, x = a ∨ x = b) (f : FermionLine C) :
    f = hC.line := by
  obtain ⟨t, ht⟩ := f
  apply Subtype.ext
  rcases hX t with rfl | rfl
  · rfl
  · rw [hC.2.2] at ht
    exact absurd ht Bool.false_ne_true

/-- A product over the internal fermion lines. -/
theorem prod_fermionLine (hC : IsCtChain C a b) (hX : ∀ x, x = a ∨ x = b) {M : Type*}
    [CommMonoid M] (F : FermionLine C → M) : ∏ f, F f = F hC.line :=
  Fintype.prod_eq_single _ fun f hf => absurd (hC.eq_line hX f) hf

/-- **Flavor collapse.** Both fermion vertices lie on the open fermion line, so the only
flavoring that the chain preserves is the all-electron one. -/
theorem eq_electronFlavoring (hC : IsCtChain C a b) (hX : ∀ x, x = a ∨ x = b)
    {φ : Flavoring κ} (hφ : Preserves C φ) : φ = electronFlavoring κ := by
  have ha : φ.1 a = 0 := by
    have := hφ (.inl 0)
    rwa [hC.1] at this
  have hb : φ.1 b = 0 := by
    have := hφ (.inr a)
    rw [hC.2.1] at this
    exact this.trans ha
  apply Subtype.ext
  funext t
  rcases hX t with rfl | rfl
  · exact ha
  · exact hb

/-- The external `Ψ(x)` is attached to `a`. -/
theorem fermion_attached (hC : IsCtChain C a b) (i j : Fin 1) : C.1.1 (.inl i) ≠ .inl j := by
  rw [Subsingleton.elim i 0, hC.1]
  exact Sum.inr_ne_inl

end IsCtChain

end Chain

/-! ### The vertices of a gauge vertex and a fermion counterterm -/

section Vertices

variable {κ : Fin 2 → Wick.VertexKind} {g h : Fin 2}

/-- The gauge vertex `g` as a fermion vertex. -/
def gaugeFv (hκg : κ g = .gauge) : Wick.FermionVertex κ := ⟨g, by rw [hκg]; decide⟩

/-- The photon field of the gauge vertex `g`. -/
def gaugePs (hκg : κ g = .gauge) : Wick.PhotonSlot κ := ⟨g, ⟨0, by rw [hκg]; decide⟩⟩

/-- The fermion counterterm vertex `h` as a fermion vertex. -/
def fermionCtFv (hκh : κ h = .fermionCt) : Wick.FermionVertex κ := ⟨h, by rw [hκh]; decide⟩

/-- The vertex of `gaugeFv`. -/
@[simp]
theorem gaugeFv_val (hκg : κ g = .gauge) : (gaugeFv hκg).1 = g := rfl

/-- The vertex of `gaugePs`. -/
@[simp]
theorem gaugePs_fst (hκg : κ g = .gauge) : (gaugePs hκg).1 = g := rfl

/-- The vertex of `fermionCtFv`. -/
@[simp]
theorem fermionCtFv_val (hκh : κ h = .fermionCt) : (fermionCtFv hκh).1 = h := rfl

variable (hgh : g ≠ h) (hκg : κ g = .gauge) (hκh : κ h = .fermionCt)
include hgh hκg hκh

/-- The two fermion vertices are distinct. -/
theorem gaugeFv_ne_fermionCtFv : gaugeFv hκg ≠ fermionCtFv hκh := fun h' =>
  hgh (congrArg Subtype.val h')

/-- The fermion vertices are the gauge vertex and the counterterm vertex. -/
theorem fv_cases_fermionCt (x : Wick.FermionVertex κ) :
    x = gaugeFv hκg ∨ x = fermionCtFv hκh := by
  obtain ⟨t, ht⟩ := x
  rcases (by omega : t = g ∨ t = h) with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The only photon field is that of the gauge vertex. -/
theorem ps_eq_gaugePs_of_fermionCt (s : Wick.PhotonSlot κ) : s = gaugePs hκg := by
  obtain ⟨t, i⟩ := s
  rcases (by omega : t = g ∨ t = h) with rfl | rfl
  · have hi := i.2
    simp only [hκg, Wick.VertexKind.photonSlots] at hi
    exact Sigma.ext rfl (heq_of_eq (Fin.ext (by simp [gaugePs]; omega)))
  · have hi := i.2
    simp only [hκh, Wick.VertexKind.photonSlots] at hi
    omega

end Vertices

/-! ### The contractions -/

section Contractions

variable {κ : Fin 2 → Wick.VertexKind} {g h : Fin 2} (hgh : g ≠ h) (hκg : κ g = .gauge)
  (hκh : κ h = .fermionCt)
include hgh hκg hκh

/-- The external photon is contracted with the photon field of the gauge vertex. -/
theorem snd_inl_of_fermionCt (C : Contraction 1 1 κ) : C.1.2 (.inl 0) = .inr (gaugePs hκg) := by
  rcases hC : C.1.2 (.inl 0) with i | s
  · rw [Subsingleton.elim i 0] at hC
    exact absurd hC (C.2 _).2
  · rw [ps_eq_gaugePs_of_fermionCt hgh hκg hκh s]

/-- There is no internal photon line. -/
theorem isEmpty_photonLine_of_fermionCt (C : Contraction 1 1 κ) : IsEmpty (PhotonLine C) :=
  ⟨fun l => by
    obtain ⟨s, s', hs, -⟩ := l
    rw [ps_eq_gaugePs_of_fermionCt hgh hκg hκh s, ← snd_inl_of_fermionCt hgh hκg hκh C,
      (C.2 _).1] at hs
    exact Sum.inl_ne_inr hs⟩

/-- **The connected contractions are the chains.** With the externals attached and the vertices
connected, the fermion line runs through both vertices, in either order. -/
theorem isCtChain_of_connected {C : Contraction 1 1 κ} (hext : ExternalsAttached C)
    (hconn : VerticesConnected C) :
    IsCtChain C (gaugeFv hκg) (fermionCtFv hκh) ∨ IsCtChain C (fermionCtFv hκh) (gaugeFv hκg) := by
  have hX := fv_cases_fermionCt hgh hκg hκh
  have hne := gaugeFv_ne_fermionCtFv hgh hκg hκh
  have key : ∀ a b : Wick.FermionVertex κ, a ≠ b → (∀ x, x = a ∨ x = b) →
      C.1.1 (.inl 0) = .inr a → IsCtChain C a b := by
    intro a b hab hX' ha
    have ha' : C.1.1 (.inr a) ≠ .inr a := fun h' =>
      Sum.inl_ne_inr (C.1.1.injective (ha.trans h'.symm))
    rcases hσa : C.1.1 (.inr a) with i | s
    · exfalso
      rw [Subsingleton.elim i 0] at hσa
      have hσb : C.1.1 (.inr b) = .inr b := by
        rcases hσb : C.1.1 (.inr b) with j | s
        · rw [Subsingleton.elim j 0] at hσb
          exact absurd (Sum.inr_injective (C.1.1.injective (hσa.trans hσb.symm))) hab
        · rcases hX' s with rfl | rfl
          · exact absurd (C.1.1.injective (hσb.trans ha.symm)) Sum.inr_ne_inl
          · rfl
      obtain ⟨w, hw⟩ : ∃ w : Fin 2, b.1 ≠ w := ⟨a.1, fun h' => hab (Subtype.ext h'.symm)⟩
      refine not_verticesConnected_of_forall_not_crosses hw
        (forall_not_crosses_of_isolated (fun t s hts => ?_) (fun s s' hss => ?_)) hconn
      · rcases hX' t with rfl | rfl
        · rw [hσa] at hts
          exact absurd hts Sum.inl_ne_inr
        · rw [hσb] at hts
          rw [Sum.inr_injective hts]
      · rw [ps_eq_gaugePs_of_fermionCt hgh hκg hκh s, ← snd_inl_of_fermionCt hgh hκg hκh C,
          (C.2 _).1] at hss
        exact absurd hss Sum.inl_ne_inr
    · rcases hX' s with rfl | rfl
      · exact absurd hσa ha'
      refine ⟨ha, hσa, ?_⟩
      rcases hσb : C.1.1 (.inr s) with j | t
      · rw [Subsingleton.elim j 0]
      · exfalso
        rcases hX' t with rfl | rfl
        · exact Sum.inr_ne_inl (C.1.1.injective (hσb.trans ha.symm))
        · exact hab (Sum.inr_injective (C.1.1.injective (hσa.trans hσb.symm)))
  rcases hσx : C.1.1 (.inl 0) with i | t
  · exact absurd hσx (hext.1 0 i)
  · rcases hX t with rfl | rfl
    · exact Or.inl (key _ _ hne hX hσx)
    · exact Or.inr (key _ _ hne.symm (fun x => (hX x).symm) hσx)

end Contractions

/-! ### Chains: lines, connectivity and values -/

section Values

variable {κ : Fin 2 → Wick.VertexKind} {g h : Fin 2}

/-- The factor of the gauge vertex `g`. -/
theorem vertexFactor_gaugeFv (hκg : κ g = .gauge) (e δ₁ δ₂ δm δ₃ m : ℝ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA g =
      I * e * Dirac.gamma (lor (gaugePs hκg)) (α (gaugeFv hκg)) (β (gaugeFv hκg)) :=
  vertexFactor_of_gauge _ _ _ _ _ _ _ _ _ _ _ hκg

/-- The factor of the fermion counterterm vertex `h`. -/
theorem vertexFactor_fermionCtFv (hκh : κ h = .fermionCt) (e δ₁ δ₂ δm δ₃ m : ℝ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ m α β lor kψ kA h =
      -I * (((δ₂ : ℂ) • Dirac.slash (kψ (fermionCtFv hκh))
        + ((δm * m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
          (α (fermionCtFv hκh)) (β (fermionCtFv hκh))) :=
  vertexFactor_of_fermionCt _ _ _ _ _ _ _ _ _ _ _ hκh

variable (hgh : g ≠ h) (hκg : κ g = .gauge) (hκh : κ h = .fermionCt)
include hgh hκg hκh

/-- The fermion line is the only internal line. -/
theorem IsCtChain.eq_inl_line {C : Contraction 1 1 κ} {a b : Wick.FermionVertex κ}
    (hC : IsCtChain C a b) (hX : ∀ x, x = a ∨ x = b) (l : Line C) : l = .inl hC.line := by
  rcases l with f | l
  · rw [hC.eq_line hX f]
  · exact (isEmpty_photonLine_of_fermionCt hgh hκg hκh C).elim l

/-- **A chain is connected but not 1PI**: its single internal line joins the two vertices and is a
bridge. -/
theorem IsCtChain.connected_not_isOnePI {C : Contraction 1 1 κ} {a b : Wick.FermionVertex κ}
    (hC : IsCtChain C a b) (hab : a ≠ b) (hX : ∀ x, x = a ∨ x = b) :
    (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C := by
  have hne : (Line.ends (.inl hC.line : Line C)).1 ≠ (Line.ends (.inl hC.line : Line C)).2 := by
    rw [hC.ends_line]
    exact fun h' => hab (Subtype.ext h'.symm)
  refine ⟨⟨⟨hC.fermion_attached, photon_attached_of_one⟩, ?_⟩, fun h1 => h1.2.2 _
    (isBridge_of_forall_eq (hC.eq_inl_line hgh hκg hκh hX) hne)⟩
  rw [hC.ends_line] at hne
  exact verticesConnected_of_two hne (joined_of_ends (Set.notMem_empty _) hC.ends_line)

/-- The amplitude of the incoming-leg chain `Ψ̄(y) → h → g → Ψ(x)`, with line momentum `k`. -/
theorem IsCtChain.contractionAmplitude_in (P : Params) {C : Contraction 1 1 κ}
    (hC : IsCtChain C (gaugeFv hκg) (fermionCtFv hκh)) {k p' p : Fin 4 → ℝ} (ℓ : Fin 4 → ℝ)
    (hk : lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inl hC.line) = k)
    (hψ : psiMomentum C ![p'] ![p] ![p' - p] ℓ (fermionCtFv hκh) = k) (α β μ : Fin 4) :
    contractionAmplitude P C (electronFlavoring κ) ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] =
      ∑ γ, ((I * P.e) • Dirac.gamma μ *
          ((1 / I) • QED.OneLoop.electronPropagator P.m P.ε k)) α γ *
        (-I * (((P.δ₂ : ℂ) • Dirac.slash k +
          ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) γ β)) := by
  have hX := fv_cases_fermionCt hgh hκg hκh
  have := isEmpty_photonLine_of_fermionCt hgh hκg hκh C
  have hne := gaugeFv_ne_fermionCtFv hgh hκg hκh
  rw [contractionAmplitude]
  simp only [spinor_constraint_out_iff_of_one hC.1, spinor_constraint_in_iff_of_one hC.2.2,
    lorentz_constraint_iff_of_one (snd_inl_of_fermionCt hgh hκg hκh C),
    prod_fin_two_eq_mul hgh, hC.prod_fermionLine hX, IsCtChain.line_val, IsCtChain.tail_line,
    vertexFactor_gaugeFv hκg, vertexFactor_fermionCtFv hκh, hk, hψ, Finset.univ_eq_empty,
    Finset.prod_empty, mul_one, mass_electronFlavoring]
  rw [show (∑ α : Wick.FermionVertex κ → Fin 4, ∑ β : Wick.FermionVertex κ → Fin 4,
      ∑ lor : Wick.PhotonSlot κ → Fin 4, _) =
      ∑ lor : Wick.PhotonSlot κ → Fin 4, ∑ α : Wick.FermionVertex κ → Fin 4,
        ∑ β : Wick.FermionVertex κ → Fin 4, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [sum_pi_eq_of_forall_eq (ps_eq_gaugePs_of_fermionCt hgh hκg hκh),
    sum_pi_eq_of_forall_eq_or_eq hne hX, ite_true, hne.symm, ite_false]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
    Matrix.cons_val_zero]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- The amplitude of the outgoing-leg chain `Ψ̄(y) → g → h → Ψ(x)`, with line momentum `k`. -/
theorem IsCtChain.contractionAmplitude_out (P : Params) {C : Contraction 1 1 κ}
    (hC : IsCtChain C (fermionCtFv hκh) (gaugeFv hκg)) {k p' p : Fin 4 → ℝ} (ℓ : Fin 4 → ℝ)
    (hk : lineMomentum C ![p'] ![p] ![p' - p] ℓ (.inl hC.line) = k)
    (hψ : psiMomentum C ![p'] ![p] ![p' - p] ℓ (fermionCtFv hκh) = k) (α β μ : Fin 4) :
    contractionAmplitude P C (electronFlavoring κ) ![p'] ![p] ![p' - p] ℓ ![α] ![β] ![μ] =
      ∑ γ, (-I * (((P.δ₂ : ℂ) • Dirac.slash k +
          ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α γ)) *
        (((1 / I) • QED.OneLoop.electronPropagator P.m P.ε k) *
          (I * P.e) • Dirac.gamma μ) γ β := by
  have hX := fv_cases_fermionCt hgh hκg hκh
  have hX' : ∀ x, x = fermionCtFv hκh ∨ x = gaugeFv hκg := fun x => (hX x).symm
  have := isEmpty_photonLine_of_fermionCt hgh hκg hκh C
  have hne := gaugeFv_ne_fermionCtFv hgh hκg hκh
  rw [contractionAmplitude]
  simp only [spinor_constraint_out_iff_of_one hC.1, spinor_constraint_in_iff_of_one hC.2.2,
    lorentz_constraint_iff_of_one (snd_inl_of_fermionCt hgh hκg hκh C),
    prod_fin_two_eq_mul hgh, hC.prod_fermionLine hX', IsCtChain.line_val, IsCtChain.tail_line,
    vertexFactor_gaugeFv hκg, vertexFactor_fermionCtFv hκh, hk, hψ, Finset.univ_eq_empty,
    Finset.prod_empty, mul_one, mass_electronFlavoring]
  rw [show (∑ α : Wick.FermionVertex κ → Fin 4, ∑ β : Wick.FermionVertex κ → Fin 4,
      ∑ lor : Wick.PhotonSlot κ → Fin 4, _) =
      ∑ lor : Wick.PhotonSlot κ → Fin 4, ∑ α : Wick.FermionVertex κ → Fin 4,
        ∑ β : Wick.FermionVertex κ → Fin 4, _ from
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm]
  simp only [sum_pi_eq_of_forall_eq (ps_eq_gaugePs_of_fermionCt hgh hκg hκh),
    sum_pi_eq_of_forall_eq_or_eq hne hX, ite_true, hne.symm, ite_false]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    Matrix.cons_val_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **The value of the incoming-leg chain**:
`[i e γ^μ (1/i) S̃(p)]_{αγ} [-i (δ₂ p̸ + δ_m m)]_{γβ}`. -/
theorem IsCtChain.contractionValue_in (P : Params) {C : Contraction 1 1 κ}
    (hC : IsCtChain C (gaugeFv hκg) (fermionCtFv hκh)) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    contractionValue P C ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      ∑ γ, ((I * P.e) • Dirac.gamma μ *
          ((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p)) α γ *
        (-I * (((P.δ₂ : ℂ) • Dirac.slash p +
          ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) γ β)) := by
  have hX := fv_cases_fermionCt hgh hκg hκh
  have hne := gaugeFv_ne_fermionCtFv hgh hκg hκh
  have hall := hC.eq_inl_line hgh hκg hκh hX
  have hends : (Line.ends (.inl hC.line : Line C)).1 ≠ (Line.ends (.inl hC.line : Line C)).2 := by
    rw [hC.ends_line]
    exact fun h' => hne (Subtype.ext h'.symm)
  have hgP : (gaugePs hκg).1 ≠ h := hgh
  have hk : lineMomentum C ![p'] ![p] ![p' - p] 0 (.inl hC.line) = p := by
    rw [lineMomentum_of_forall_eq hall hends, hC.ends_line,
      externalMomentum_eq_of_one hC.1 hC.2.2 (snd_inl_of_fermionCt hgh hκg hκh C)]
    change (if h = h then _ else _) + (if g = h then _ else _) - (if g = h then _ else _) = _
    simp [hgh]
  have hψ : psiMomentum C ![p'] ![p] ![p' - p] 0 (fermionCtFv hκh) = p :=
    psiMomentum_of_eq_inl hC.2.2 _ _ _ _
  rw [contractionValue_of_forall_eq P hall hends,
    regulatedAmplitude_eq_of_forall_preserves P (fun φ hφ => hC.eq_electronFlavoring hX hφ),
    hC.contractionAmplitude_in hgh hκg hκh P 0 hk hψ]

/-- **The value of the outgoing-leg chain**:
`[-i (δ₂ p̸' + δ_m m)]_{αγ} [(1/i) S̃(p') i e γ^μ]_{γβ}`. -/
theorem IsCtChain.contractionValue_out (P : Params) {C : Contraction 1 1 κ}
    (hC : IsCtChain C (fermionCtFv hκh) (gaugeFv hκg)) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    contractionValue P C ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      ∑ γ, (-I * (((P.δ₂ : ℂ) • Dirac.slash p' +
          ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α γ)) *
        (((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p') *
          (I * P.e) • Dirac.gamma μ) γ β := by
  have hX := fv_cases_fermionCt hgh hκg hκh
  have hX' : ∀ x, x = fermionCtFv hκh ∨ x = gaugeFv hκg := fun x => (hX x).symm
  have hne := gaugeFv_ne_fermionCtFv hgh hκg hκh
  have hall := hC.eq_inl_line hgh hκg hκh hX'
  have hends : (Line.ends (.inl hC.line : Line C)).1 ≠ (Line.ends (.inl hC.line : Line C)).2 := by
    rw [hC.ends_line]
    exact fun h' => hne (Subtype.ext h')
  have hk : lineMomentum C ![p'] ![p] ![p' - p] 0 (.inl hC.line) = p' := by
    rw [lineMomentum_of_forall_eq hall hends, hC.ends_line,
      externalMomentum_eq_of_one hC.1 hC.2.2 (snd_inl_of_fermionCt hgh hκg hκh C)]
    change (if g = g then _ else _) + (if g = g then _ else _) - (if h = g then _ else _) = _
    simp [hgh.symm]
  have hψ : psiMomentum C ![p'] ![p] ![p' - p] 0 (fermionCtFv hκh) = p' := by
    rw [← IsCtChain.line_val hC, psiMomentum_eq_lineMomentum, hk]
  rw [contractionValue_of_forall_eq P hall hends,
    regulatedAmplitude_eq_of_forall_preserves P (fun φ hφ => hC.eq_electronFlavoring hX' hφ),
    hC.contractionAmplitude_out hgh hκg hκh P 0 hk hψ]

end Values

/-! ### The sum over the connected contractions -/

section Sum

variable {κ : Fin 2 → Wick.VertexKind} {g h : Fin 2}

/-- The photon pairing of a gauge vertex and a fermion counterterm: `A(z)` with the photon field
of the gauge vertex. -/
def fermionCtPhotonPairing (hκg : κ g = .gauge) : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ) :=
  Equiv.swap (.inl 0) (.inr (gaugePs hκg))

variable (hgh : g ≠ h) (hκg : κ g = .gauge) (hκh : κ h = .fermionCt)
include hgh hκg hκh

/-- The photon pairing is a fixed-point-free involution. -/
theorem fermionCtPhotonPairing_involutive (x : Fin 1 ⊕ Wick.PhotonSlot κ) :
    fermionCtPhotonPairing hκg (fermionCtPhotonPairing hκg x) = x ∧
      fermionCtPhotonPairing hκg x ≠ x := by
  refine ⟨Equiv.swap_apply_self _ _ _, ?_⟩
  rcases x with i | s
  · rw [Subsingleton.elim i 0, fermionCtPhotonPairing, Equiv.swap_apply_left]
    exact Sum.inr_ne_inl
  · rw [ps_eq_gaugePs_of_fermionCt hgh hκg hκh s, fermionCtPhotonPairing,
      Equiv.swap_apply_right]
    exact Sum.inl_ne_inr

/-- The chain `Ψ̄(y) → b → a → Ψ(x)` as a contraction. -/
def ctChain (a b : Wick.FermionVertex κ) : Contraction 1 1 κ :=
  ⟨(Equiv.swap (.inl 0) (.inr b) * Equiv.swap (.inl 0) (.inr a), fermionCtPhotonPairing hκg),
    fermionCtPhotonPairing_involutive hgh hκg hκh⟩

/-- `ctChain a b` is the chain `Ψ̄(y) → b → a → Ψ(x)`. -/
theorem isCtChain_ctChain {a b : Wick.FermionVertex κ} (hab : a ≠ b) :
    IsCtChain (ctChain hgh hκg hκh a b) a b := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [ctChain, Equiv.Perm.mul_apply]
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl
      (Sum.inr_injective.ne hab)]
  · rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
  · rw [Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (Sum.inr_injective.ne hab.symm),
      Equiv.swap_apply_right]

/-- A chain is determined by its vertex order. -/
theorem IsCtChain.eq_ctChain {C : Contraction 1 1 κ} {a b : Wick.FermionVertex κ}
    (hC : IsCtChain C a b) (hab : a ≠ b) (hX : ∀ x, x = a ∨ x = b) :
    C = ctChain hgh hκg hκh a b := by
  apply Subtype.ext
  apply Prod.ext
  · exact hC.fst_eq hab hX
  · ext1 x
    change C.1.2 x = fermionCtPhotonPairing hκg x
    rcases x with i | s
    · rw [Subsingleton.elim i 0, snd_inl_of_fermionCt hgh hκg hκh C, fermionCtPhotonPairing,
        Equiv.swap_apply_left]
    · rw [ps_eq_gaugePs_of_fermionCt hgh hκg hκh s, ← snd_inl_of_fermionCt hgh hκg hκh C,
        (C.2 _).1, snd_inl_of_fermionCt hgh hκg hκh C, fermionCtPhotonPairing,
        Equiv.swap_apply_right]

/-- **The connected contractions of a gauge vertex and a fermion counterterm that are not 1PI**:
the two chains, with the counterterm on the incoming and on the outgoing leg. Each has sign
`+1`. -/
theorem sum_nonOnePI_fermionCt (P : Params) [Fintype (Contraction 1 1 κ)]
    [DecidablePred fun C : Contraction 1 1 κ =>
      (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C]
    (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter
        (fun C => (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C),
      ((fermionSign C : ℤ) : ℂ) * contractionValue P C ![p'] ![p] ![p' - p] ![α] ![β] ![μ] =
      ∑ γ, ((I * P.e) • Dirac.gamma μ *
          ((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p)) α γ *
        (-I * (((P.δ₂ : ℂ) • Dirac.slash p +
          ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) γ β)) +
      ∑ γ, (-I * (((P.δ₂ : ℂ) • Dirac.slash p' +
          ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α γ)) *
        (((1 / I) • QED.OneLoop.electronPropagator P.m P.ε p') *
          (I * P.e) • Dirac.gamma μ) γ β := by
  classical
  have hX := fv_cases_fermionCt hgh hκg hκh
  have hX' : ∀ x, x = fermionCtFv hκh ∨ x = gaugeFv hκg := fun x => (hX x).symm
  have hne := gaugeFv_ne_fermionCtFv hgh hκg hκh
  have hin := isCtChain_ctChain hgh hκg hκh hne
  have hout := isCtChain_ctChain hgh hκg hκh hne.symm
  have hfilter : (Finset.univ : Finset (Contraction 1 1 κ)).filter
      (fun C => (ExternalsAttached C ∧ VerticesConnected C) ∧ ¬ IsOnePI C) =
      {ctChain hgh hκg hκh (gaugeFv hκg) (fermionCtFv hκh),
        ctChain hgh hκg hκh (fermionCtFv hκh) (gaugeFv hκg)} := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hext, hconn⟩, -⟩
      rcases isCtChain_of_connected hgh hκg hκh hext hconn with h' | h'
      · exact Or.inl (h'.eq_ctChain hgh hκg hκh hne hX)
      · exact Or.inr (h'.eq_ctChain hgh hκg hκh hne.symm hX')
    · rintro (rfl | rfl)
      · exact hin.connected_not_isOnePI hgh hκg hκh hne hX
      · exact hout.connected_not_isOnePI hgh hκg hκh hne.symm hX'
  have hdist : ctChain hgh hκg hκh (gaugeFv hκg) (fermionCtFv hκh) ≠
      ctChain hgh hκg hκh (fermionCtFv hκh) (gaugeFv hκg) := fun h' => by
    have h1 := hin.1
    rw [h', hout.1] at h1
    exact hne (Sum.inr_injective h1).symm
  rw [hfilter, Finset.sum_pair hdist, hin.fermionSign_eq hne hX, hout.fermionSign_eq hne.symm hX',
    hin.contractionValue_in hgh hκg hκh, hout.contractionValue_out hgh hκg hκh]
  simp

end Sum

end QED.WickModel

end
