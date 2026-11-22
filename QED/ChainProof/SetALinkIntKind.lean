/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetALinkInt
public import QED.GradedProof.VP2Relabel
public import QED.TwoLoop.RelabelCountertermValue

/-!
# Changing `gaugeCt` vertices into `gauge` vertices

Helper for the Phase 5 Stage 3a goal (HA₀) `QED.ThreeLoop.jointEnergyFirstIntegrable_setA`
(decision D-58), classes `GW`, `GU`. Let `κ` be a kind sequence of `gauge` and `gaugeCt`
vertices. Both kinds carry one `Ψ̄ Ψ` pair and one photon field, so a contraction `C` of `κ` is
also a contraction `toG C` of `gauges N` (the same pairings, `kindChangeG`), with the same
lines and line ends (`corrG`, a line correspondence fixing the vertices and the orientations).
The `gaugeCt` factor (V₁₉) at level `0` and flavour `f` is `e² d₁ f 0` times the `gauge` factor,
so the graded amplitude (G₃) of `C` at the zero grading is the product `ctW` of these numbers
times that of `toG C` (`contractionAmplitude_toG`). If that product times the loop weight of `C`
is the loop weight of `toG C` for twisted loop coefficients `c'`, the regulated amplitudes (G₄)
agree (`regulatedAmplitude_toG`), and (T₉′) passes from `toG C` with the coefficients `c'` to
`C` (`jointEnergyFirstIntegrable_of_toG`).

`loopWeight_eq_of_one_loop` evaluates the loop weight of a contraction with a single closed
fermion loop.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetALink

open QED.WickModel QED.Graded QED.TwoLoop.Routing QED.TwoLoop.Relabel
open QED.TwoLoop.Enumeration (gauges tail_eq head_eq)

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### Fields -/

section Fields

variable (hκ : ∀ t, κ t = .gauge ∨ κ t = .gaugeCt)

include hκ in
theorem kindG_ne_photonCt (t : Fin N) : κ t ≠ .photonCt := by
  rcases hκ t with h | h <;> rw [h] <;> decide

include hκ in
theorem kindG_photonSlots (t : Fin N) : (κ t).photonSlots = (gauges N t).photonSlots := by
  rcases hκ t with h | h
  · rw [h]
  · rw [h]
    rfl

/-- The fermion vertices of `κ` are those of `gauges N`. -/
def fvG : Wick.FermionVertex κ ≃ Wick.FermionVertex (gauges N) :=
  Equiv.subtypeEquivRight fun t => iff_of_true (kindG_ne_photonCt hκ t) fun h => nomatch h

/-- The photon fields of `κ` are those of `gauges N`. -/
def psG : Wick.PhotonSlot κ ≃ Wick.PhotonSlot (gauges N) :=
  Equiv.sigmaCongrRight fun t => finCongr (kindG_photonSlots hκ t)

@[simp] theorem fvG_val (t : Wick.FermionVertex κ) : (fvG hκ t).1 = t.1 := rfl

@[simp] theorem psG_fst (a : Wick.PhotonSlot κ) : (psG hκ a).1 = a.1 := rfl

theorem photonKey_psG (a : Wick.PhotonSlot κ) : Wick.photonKey (psG hκ a) = Wick.photonKey a :=
  rfl

/-- The fermion fields, the externals fixed. -/
def extFG : Fin nf ⊕ Wick.FermionVertex κ ≃ Fin nf ⊕ Wick.FermionVertex (gauges N) :=
  Equiv.sumCongr (Equiv.refl _) (fvG hκ)

/-- The photon fields, the externals fixed. -/
def extPG : Fin nA ⊕ Wick.PhotonSlot κ ≃ Fin nA ⊕ Wick.PhotonSlot (gauges N) :=
  Equiv.sumCongr (Equiv.refl _) (psG hκ)

@[simp] theorem extFG_inl (i : Fin nf) : extFG hκ (.inl i) = .inl i := rfl

@[simp] theorem extFG_inr (t : Wick.FermionVertex κ) :
    extFG (nf := nf) hκ (.inr t) = .inr (fvG hκ t) := rfl

@[simp] theorem extPG_inl (i : Fin nA) : extPG hκ (.inl i) = .inl i := rfl

@[simp] theorem extPG_inr (a : Wick.PhotonSlot κ) :
    extPG (nA := nA) hκ (.inr a) = .inr (psG hκ a) := rfl

/-- **A contraction of `gauge` and `gaugeCt` vertices as a contraction of `gauge` vertices.** -/
def toG (C : Contraction nf nA κ) : Contraction nf nA (gauges N) :=
  ⟨((extFG hκ).permCongr C.1.1, (extPG hκ).permCongr C.1.2), fun b => by
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, (C.2 _).1, Equiv.apply_symm_apply,
      true_and]
    intro h
    exact (C.2 _).2 ((extPG hκ).injective (h.trans ((extPG hκ).apply_symm_apply b).symm))⟩

variable (C : Contraction nf nA κ)

theorem toG_fst_apply (x : Fin nf ⊕ Wick.FermionVertex κ) :
    (toG hκ C).1.1 (extFG hκ x) = extFG hκ (C.1.1 x) := by
  simp [toG]

theorem toG_snd_apply (x : Fin nA ⊕ Wick.PhotonSlot κ) :
    (toG hκ C).1.2 (extPG hκ x) = extPG hκ (C.1.2 x) := by
  simp [toG]

theorem extFG_eq_inl_iff (y : Fin nf ⊕ Wick.FermionVertex κ) (i : Fin nf) :
    extFG hκ y = .inl i ↔ y = .inl i := by
  cases y <;> simp

theorem extFG_eq_inr_iff (y : Fin nf ⊕ Wick.FermionVertex κ) (t : Wick.FermionVertex (gauges N)) :
    extFG hκ y = .inr t ↔ y = .inr ((fvG hκ).symm t) := by
  cases y <;> simp [Equiv.eq_symm_apply]

theorem extPG_eq_inr_iff (y : Fin nA ⊕ Wick.PhotonSlot κ) (a : Wick.PhotonSlot (gauges N)) :
    extPG hκ y = .inr a ↔ y = .inr ((psG hκ).symm a) := by
  cases y <;> simp [Equiv.eq_symm_apply]

theorem toG_fst_inl (i : Fin nf) : (toG hκ C).1.1 (.inl i) = extFG hκ (C.1.1 (.inl i)) :=
  toG_fst_apply hκ C (.inl i)

theorem toG_fst_inr (t : Wick.FermionVertex (gauges N)) :
    (toG hκ C).1.1 (.inr t) = extFG hκ (C.1.1 (.inr ((fvG hκ).symm t))) := by
  simpa using toG_fst_apply hκ C (.inr ((fvG hκ).symm t))

theorem toG_snd_inl (j : Fin nA) : (toG hκ C).1.2 (.inl j) = extPG hκ (C.1.2 (.inl j)) :=
  toG_snd_apply hκ C (.inl j)

theorem toG_snd_inr {a b : Wick.PhotonSlot κ} (h : C.1.2 (.inr a) = .inr b) :
    (toG hκ C).1.2 (.inr (psG hκ a)) = .inr (psG hκ b) := by
  have := toG_snd_apply hκ C (.inr a)
  simp only [extPG_inr, h] at this
  exact this

/-- The external momentum flowing into `v` is the same in `toG C` and in `C`. -/
theorem externalMomentum_toG (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (v : Fin N) :
    externalMomentum (toG hκ C) pOut pIn kIn v = externalMomentum C pOut pIn kIn v := by
  have hF : ∀ Q : Wick.FermionVertex (gauges N) → Prop, (∃ t, Q t) ↔ ∃ s, Q (fvG hκ s) :=
    fun Q => (fvG hκ).exists_congr_right.symm
  have hP : ∀ Q : Wick.PhotonSlot (gauges N) → Prop, (∃ a, Q a) ↔ ∃ b, Q (psG hκ b) :=
    fun Q => (psG hκ).exists_congr_right.symm
  unfold externalMomentum
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;>
    refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
  · refine (hF _).trans ?_
    simp only [fvG_val, toG_fst_inr, Equiv.symm_apply_apply, extFG_eq_inl_iff]
  · refine (hP _).trans ?_
    simp only [psG_fst, toG_snd_inl, extPG_eq_inr_iff, Equiv.symm_apply_apply]
  · refine (hF _).trans ?_
    simp only [fvG_val, toG_fst_inl, extFG_eq_inr_iff, Equiv.symm_apply_apply]

end Fields

/-! ### Lines -/

section Lines

variable (hκ : ∀ t, κ t = .gauge ∨ κ t = .gaugeCt) (C : Contraction nf nA κ)

/-- The fermion lines of `C` and of `toG C`. -/
def fermionLineG : FermionLine C ≃ FermionLine (toG hκ C) :=
  Equiv.subtypeEquiv (fvG hκ) fun t => by
    have := toG_fst_apply hκ C (.inr t)
    simp only [extFG_inr] at this
    rw [this]
    cases C.1.1 (.inr t) <;> rfl

theorem fermionLineG_val (f : FermionLine C) : (fermionLineG hκ C f).1 = fvG hκ f.1 := rfl

theorem tail_fermionLineG (f : FermionLine C) :
    (fermionLineG hκ C f).tail = fvG hκ f.tail := by
  obtain ⟨s, hs⟩ : ∃ s, C.1.1 (.inr f.1) = .inr s := Sum.isRight_iff.mp f.2
  have h' : (toG hκ C).1.1 (.inr (fermionLineG hκ C f).1) = .inr (fvG hκ s) := by
    have := toG_fst_apply hκ C (.inr f.1)
    simp only [extFG_inr, hs] at this
    exact this
  rw [tail_eq _ h', tail_eq _ hs]

/-- The photon lines of `C` and of `toG C`: the same indexing fields. -/
def photonLineG : PhotonLine C ≃ PhotonLine (toG hκ C) :=
  Equiv.subtypeEquiv (psG hκ) fun a => by
    constructor
    · rintro ⟨b, hb, hk⟩
      exact ⟨psG hκ b, toG_snd_inr hκ C hb, hk⟩
    · rintro ⟨b', hb', hk⟩
      obtain ⟨b, rfl⟩ := (psG hκ).surjective b'
      refine ⟨b, ?_, hk⟩
      have := toG_snd_apply hκ C (.inr a)
      rw [extPG_inr, hb'] at this
      rcases h : C.1.2 (.inr a) with j | c
      · rw [h] at this
        simp at this
      · rw [h, extPG_inr] at this
        rw [(psG hκ).injective (Sum.inr_injective this)]

theorem photonLineG_val (g : PhotonLine C) : (photonLineG hκ C g).1 = psG hκ g.1 := rfl

theorem head_photonLineG (g : PhotonLine C) :
    (photonLineG hκ C g).head = psG hκ g.head :=
  head_eq _ (toG_snd_inr hκ C (QED.TwoLoop.LoopBound.apply_inr_photonLine g))

/-- The internal lines of `C` and of `toG C`. -/
def lineG : Line C ≃ Line (toG hκ C) :=
  Equiv.sumCongr (fermionLineG hκ C) (photonLineG hκ C)

theorem lineG_ends (f : Line C) : (lineG hκ C f).ends = f.ends := by
  rcases f with f | g
  · change ((fermionLineG hκ C f).tail.1, (fermionLineG hκ C f).1.1) = (f.tail.1, f.1.1)
    rw [tail_fermionLineG]
    rfl
  · change ((photonLineG hκ C g).1.1, (photonLineG hκ C g).head.1) = (g.1.1, g.head.1)
    rw [head_photonLineG]
    rfl

/-- **The line correspondence of `C` and `toG C`**: the vertices and orientations fixed. -/
def corrG : LineCorr C (toG hκ C) where
  vtx := Equiv.refl _
  line := lineG hκ C
  rev := fun _ => false
  ends_line f := by
    rw [lineG_ends]
    rfl

theorem corrG_pull (k' : Line (toG hκ C) → Fin 4 → ℝ) (f : Line C) :
    (corrG hκ C).pull k' f = k' (lineG hκ C f) := by
  simp [LineCorr.pull, corrG]

theorem corrG_symm_pull (k : Line C → Fin 4 → ℝ) (f : Line (toG hκ C)) :
    (corrG hκ C).symm.pull k f = k ((lineG hκ C).symm f) := by
  simp [LineCorr.pull, LineCorr.symm, corrG]

theorem corrG_pull_symm_pull (k : Line C → Fin 4 → ℝ) :
    (corrG hκ C).pull ((corrG hκ C).symm.pull k) = k := by
  funext f
  rw [corrG_pull, corrG_symm_pull, Equiv.symm_apply_apply]

end Lines

/-! ### Momenta -/

section Momenta

variable (hκ : ∀ t, κ t = .gauge ∨ κ t = .gaugeCt) (C : Contraction nf nA κ)

theorem psiMomentum₂_toG (pIn : Fin nf → Fin 4 → ℝ) (k' : Line (toG hκ C) → Fin 4 → ℝ)
    (t : Wick.FermionVertex κ) :
    psiMomentum₂ (toG hκ C) pIn k' (fvG hκ t) =
      psiMomentum₂ C pIn ((corrG hκ C).pull k') t := by
  by_cases hf : (C.1.1 (.inr t)).isRight
  · have hf' : ((toG hκ C).1.1 (.inr (fvG hκ t))).isRight := (fermionLineG hκ C ⟨t, hf⟩).2
    rw [psiMomentum₂_of_isRight hf', psiMomentum₂_of_isRight hf, corrG_pull]
    rfl
  · obtain ⟨i, hi⟩ : ∃ i, C.1.1 (.inr t) = .inl i := by
      rcases h : C.1.1 (.inr t) with i | s
      · exact ⟨i, rfl⟩
      · rw [h] at hf
        exact absurd rfl hf
    have hi' : (toG hκ C).1.1 (.inr (fvG hκ t)) = .inl i := by
      have := toG_fst_apply hκ C (.inr t)
      rw [extFG_inr, hi, extFG_inl] at this
      exact this
    rw [psiMomentum₂_of_inl hi', psiMomentum₂_of_inl hi]

theorem photonMomentum₂_toG (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (toG hκ C) → Fin 4 → ℝ)
    (a : Wick.PhotonSlot κ) :
    photonMomentum₂ (toG hκ C) kIn k' (psG hκ a) =
      photonMomentum₂ C kIn ((corrG hκ C).pull k') a := by
  unfold photonMomentum₂
  congr 1
  · refine Finset.sum_congr rfl fun j _ => if_congr ?_ rfl rfl
    rw [toG_snd_inl, extPG_eq_inr_iff, Equiv.symm_apply_apply]
  · symm
    refine Fintype.sum_equiv (photonLineG hκ C) _ _ fun g => ?_
    rw [head_photonLineG, photonLineG_val, corrG_pull]
    simp only [(psG hκ).injective.eq_iff]
    rfl

theorem psiMomentum₂_toG_eq (pIn : Fin nf → Fin 4 → ℝ) (k' : Line (toG hκ C) → Fin 4 → ℝ) :
    psiMomentum₂ (toG hκ C) pIn k' =
      psiMomentum₂ C pIn ((corrG hκ C).pull k') ∘ (fvG hκ).symm := by
  funext s
  obtain ⟨t, rfl⟩ := (fvG hκ).surjective s
  simp only [Function.comp_apply, Equiv.symm_apply_apply, psiMomentum₂_toG]

theorem photonMomentum₂_toG_eq (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (toG hκ C) → Fin 4 → ℝ) :
    photonMomentum₂ (toG hκ C) kIn k' =
      photonMomentum₂ C kIn ((corrG hκ C).pull k') ∘ (psG hκ).symm := by
  funext b
  obtain ⟨a, rfl⟩ := (psG hκ).surjective b
  simp only [Function.comp_apply, Equiv.symm_apply_apply, photonMomentum₂_toG]

end Momenta

/-! ### Amplitudes -/

section Amplitude

variable (hκ : ∀ t, κ t = .gauge ∨ κ t = .gaugeCt) {F : Type}

/-- The fermion vertex of a vertex `t`. -/
def fvOfG (t : Fin N) : Wick.FermionVertex κ := ⟨t, kindG_ne_photonCt hκ t⟩

/-- The flavourings of `C` and of `toG C`. -/
def flavG : Graded.Flavoring F κ ≃ Graded.Flavoring F (gauges N) :=
  Equiv.arrowCongr (fvG hκ) (Equiv.refl F)

@[simp] theorem flavG_apply (φ : Graded.Flavoring F κ) (t : Wick.FermionVertex (gauges N)) :
    flavG hκ φ t = φ ((fvG hκ).symm t) :=
  rfl

/-- The product of the `gaugeCt` coefficients `e² d₁ f 0` of a flavouring. -/
noncomputable def ctW (P : Params) (D : Counterterms F) (φ : Graded.Flavoring F κ) : ℂ :=
  ∏ t, if κ t = .gaugeCt then ((P.e ^ 2 * D.d₁ (φ (fvOfG hκ t)) 0 : ℝ) : ℂ) else 1

/-- The loop coefficients of `Φ` replaced by `c'`. -/
def twistΦ (Φ : Lepton.Flavors F) (c' : F → ℝ) : Lepton.Flavors F :=
  ⟨Φ.mass, c', Φ.openLine⟩

variable (Φ : Lepton.Flavors F) (C : Contraction nf nA κ)

theorem fermionFlavor_flavG (φ : Graded.Flavoring F κ) (x : Fin nf ⊕ Wick.FermionVertex κ) :
    Graded.fermionFlavor Φ (flavG hκ φ) (extFG hκ x) = Graded.fermionFlavor Φ φ x := by
  cases x <;> simp [Graded.fermionFlavor]

theorem preserves_toG_iff (φ : Graded.Flavoring F κ) :
    Graded.Preserves Φ (toG hκ C) (flavG hκ φ) ↔ Graded.Preserves Φ C φ := by
  constructor
  · intro h x
    have := h (extFG hκ x)
    rwa [toG_fst_apply, fermionFlavor_flavG, fermionFlavor_flavG] at this
  · intro h a
    obtain ⟨x, rfl⟩ := (extFG hκ).surjective a
    rw [toG_fst_apply, fermionFlavor_flavG, fermionFlavor_flavG]
    exact h x

theorem amp_toG_aux {a b c d w a' b' c' d' : ℂ} (h1 : a = a') (h2 : b = w * b') (h3 : c = c')
    (h4 : d = d') : a * (b * c * d) = w * (a' * (b' * c' * d')) := by
  subst h1 h2 h3 h4
  ring

open scoped Classical in
/-- **The graded amplitude (G₃) at the zero grading** of `C` is `ctW` times that of `toG C`. -/
theorem contractionAmplitude_toG (P : Params) (D : Counterterms F) (φ : Graded.Flavoring F κ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k' : Line (toG hκ C) → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.contractionAmplitude P Φ D C φ 0 pIn kIn ((corrG hκ C).pull k') αOut βIn μ =
      ctW hκ P D φ *
        Graded.contractionAmplitude P Φ D (toG hκ C) (flavG hκ φ) 0 pIn kIn k' αOut βIn μ := by
  unfold Graded.contractionAmplitude
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.arrowCongr (fvG hκ) (Equiv.refl (Fin 4))) _ _ fun α => ?_
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.arrowCongr (fvG hκ) (Equiv.refl (Fin 4))) _ _ fun β => ?_
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.arrowCongr (psG hκ) (Equiv.refl (Fin 4))) _ _ fun lor => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.id_comp]
  have hα : (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ↔
      (∀ i t, (toG hκ C).1.1 (.inl i) = .inr t →
        (α ∘ (fvG hκ).symm) t = αOut i) := by
    simp only [toG_fst_inl, extFG_eq_inr_iff, Function.comp_apply]
    exact forall_congr' fun i => ((fvG hκ).symm.forall_congr_right
      (q := fun t => C.1.1 (.inl i) = .inr t → α t = αOut i)).symm
  have hβ : (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ↔
      (∀ t i, (toG hκ C).1.1 (.inr t) = .inl i →
        (β ∘ (fvG hκ).symm) t = βIn i) := by
    simp only [toG_fst_inr, extFG_eq_inl_iff, Function.comp_apply]
    exact ((fvG hκ).symm.forall_congr_right
      (q := fun t => ∀ i, C.1.1 (.inr t) = .inl i → β t = βIn i)).symm
  have hlor : (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) ↔
      (∀ j a, (toG hκ C).1.2 (.inl j) = .inr a →
        (lor ∘ (psG hκ).symm) a = μ j) := by
    simp only [toG_snd_inl, extPG_eq_inr_iff, Function.comp_apply]
    exact forall_congr' fun j => ((psG hκ).symm.forall_congr_right
      (q := fun a => C.1.2 (.inl j) = .inr a → lor a = μ j)).symm
  refine amp_toG_aux (if_congr (and_congr hα (and_congr hβ hlor)) rfl rfl) ?_ ?_ ?_
  · rw [psiMomentum₂_toG_eq, photonMomentum₂_toG_eq]
    unfold ctW
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [vertexFactor_eq_of_gauge (κ₀ := gauges N) (t := t) (h := rfl)]
    rcases hκ t with h | h
    · have h' : κ t ≠ .gaugeCt := by rw [h]; decide
      rw [vertexFactor_eq_of_gauge (h := h)]
      simp only [h', ↓reduceIte, one_mul]
      rfl
    · rw [vertexFactor_eq_of_gaugeCt (h := h)]
      simp only [h, ↓reduceIte, Pi.zero_apply]
      push_cast
      ring_nf
      rfl
  · refine Fintype.prod_equiv (fermionLineG hκ C) _ _ fun f => ?_
    simp only [Function.comp_apply, flavG_apply, tail_fermionLineG, fermionLineG_val,
      Equiv.symm_apply_apply, corrG_pull]
    rfl
  · refine Fintype.prod_equiv (photonLineG hκ C) _ _ fun g => ?_
    simp only [Function.comp_apply, head_photonLineG, photonLineG_val, Equiv.symm_apply_apply,
      corrG_pull]
    rfl

/-- **The regulated amplitude (G₄) at the zero grading** of `C` is that of `toG C` with the
loop coefficients `c'`, if `ctW` times the loop weight of `C` is the loop weight of `toG C` for
`c'`. -/
theorem regulatedAmplitude_toG [Fintype F] [DecidableEq F] (P : Params) (D : Counterterms F)
    (c' : F → ℝ) (hw : ∀ φ, Graded.Preserves Φ C φ →
      (Graded.loopWeight Φ C φ : ℂ) * ctW hκ P D φ =
        Graded.loopWeight (twistΦ Φ c') (toG hκ C) (flavG hκ φ))
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k' : Line (toG hκ C) → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    Graded.regulatedAmplitude P Φ D C 0 pIn kIn ((corrG hκ C).pull k') αOut βIn μ =
      Graded.regulatedAmplitude P (twistΦ Φ c') D (toG hκ C) 0 pIn kIn k' αOut βIn μ := by
  classical
  unfold Graded.regulatedAmplitude
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Fintype.sum_equiv (flavG hκ) _ _ fun φ => ?_
  by_cases hφ : Graded.Preserves Φ C φ
  · have hφ' : Graded.Preserves (twistΦ Φ c') (toG hκ C) (flavG hκ φ) :=
      (preserves_toG_iff hκ Φ C φ).mpr hφ
    simp only [hφ, hφ', ↓reduceIte, contractionAmplitude_toG, ← hw φ hφ]
    rw [mul_assoc]
    rfl
  · have hφ' : ¬ Graded.Preserves (twistΦ Φ c') (toG hκ C) (flavG hκ φ) :=
      mt (preserves_toG_iff hκ Φ C φ).mp hφ
    simp only [hφ, hφ', ↓reduceIte]

/-- **(T₉′) passes from `toG C` with the loop coefficients `c'` to `C`**, under momentum
conservation. -/
theorem jointEnergyFirstIntegrable_of_toG [Fintype F] [DecidableEq F] (P : Params)
    (D : Counterterms F) (c' : F → ℝ) (hA : ExternalsAttached C) (hV : VerticesConnected C)
    (hV' : VerticesConnected (toG hκ C)) (hL : loopCount (toG hκ C) = loopCount C)
    (hw : ∀ φ, Graded.Preserves Φ C φ →
      (Graded.loopWeight Φ C φ : ℂ) * ctW hκ P D φ =
        Graded.loopWeight (twistΦ Φ c') (toG hκ C) (flavG hκ φ))
    {pOut pIn : Fin nf → Fin 4 → ℝ} {kIn : Fin nA → Fin 4 → ℝ}
    (hmom : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4)
    (h : QED.TwoLoop.jointEnergyFirstIntegrable (loopCount (toG hκ C)) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount (toG hκ C)) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P (twistΦ Φ c') D (toG hκ C) 0 pIn kIn
          (lineMomentum₂ (toG hκ C) pOut pIn kIn ℓ) αOut βIn μ) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        Graded.regulatedAmplitude P Φ D C 0 pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn
          μ := by
  have hsum : ∑ v, externalMomentum C pOut pIn kIn v = 0 := by
    rw [sum_externalMomentum hA, hmom, sub_self]
  have hsum' : ∑ v, externalMomentum (toG hκ C) pOut pIn kIn v = 0 := by
    simp only [externalMomentum_toG, hsum]
  obtain ⟨M, hM, a, hr⟩ := (corrG hκ C).symm.exists_routing_change hV' hV
    (fun v => (externalMomentum_toG hκ C pOut pIn kIn v).symm) hsum' rfl hL.symm
  rw [← hL]
  exact QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_of_matAct M hM a h fun ℓ => by
    rw [← corrG_pull_symm_pull hκ C (lineMomentum₂ C pOut pIn kIn ℓ), hr,
      regulatedAmplitude_toG hκ Φ C P D c' hw]

end Amplitude

/-! ### A single closed loop -/

open scoped Classical in
/-- **The loop weight (G₁‴) of a contraction with one closed fermion loop**, through the
vertex `x₀`, is the coefficient of the flavour of `x₀`. -/
theorem loopWeight_eq_of_one_loop {F : Type} (Φ : Lepton.Flavors F) {C : Contraction nf nA κ}
    {φ : Graded.Flavoring F κ} (hφ : Graded.Preserves Φ C φ) (x₀ : Wick.FermionVertex κ)
    (h₀ : ∀ i, ¬ C.1.1.SameCycle (.inl i) (.inr x₀))
    (hall : ∀ x, (∃ i, C.1.1.SameCycle x (.inl i)) ∨ C.1.1.SameCycle x (.inr x₀)) :
    Graded.loopWeight Φ C φ = Φ.coeff (φ x₀) := by
  unfold Graded.loopWeight
  let q₀ : ClosedLoop C := ⟨Quotient.mk _ (.inr x₀), fun i h => h₀ i (Quotient.exact h)⟩
  have hout : C.1.1.SameCycle q₀.1.out (.inr x₀) := Quotient.exact (Quotient.out_eq q₀.1)
  rw [Fintype.prod_eq_single q₀ fun q hq => absurd ?_ hq]
  · rw [QED.GradedProof.VP2.fermionFlavor_eq_of_sameCycle Φ hφ hout]
    rfl
  · rcases hall q.1.out with ⟨i, hi⟩ | hx
    · exact absurd ((Quotient.out_eq q.1).symm.trans (Quotient.sound hi)).symm (q.2 i)
    · exact Subtype.ext ((Quotient.out_eq q.1).symm.trans (Quotient.sound hx))

end QED.ChainProof.SetALink

end
