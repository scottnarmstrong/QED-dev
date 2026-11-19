/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0ClosedSum
public import QED.GradedProof.X0ClosedFlavor
public import QED.GradedProof.X0OneCt

/-!
# (X₀): the index terms of a contraction with one closed fermion loop

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57). This file collects
the algebra behind `X0ClosedOne`:

* `contractionAmplitude_zero_eq`: at the zero grading the amplitude (G₃) is the sum over the
  spinor and Lorentz indices of `ampTerm`, with level-`0` vertex factors `vf0`;
* `vertexFactor_pure`: on a fermion vertex the factor (V₁₉) is chirality-pure in the mass `M`;
* `prod_sgn_closed`, `card_zLine`: around the closed loop `Z` the vertices and the lines are in
  bijection (by the head and by the tail of a line), so the sign product of the entries is `1`
  and their number is even;
* `prod_split_loopT`: the vertex product split into the loop and the other vertices.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel
open QED.TwoLoop.FurryIntegrable (sgn)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type}

/-- The level-`0` vertex factor of flavour `x` and mass `M`. -/
noncomputable def vf0 (P : Params) (D : Counterterms F) (x : F) (M : ℝ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4)
    (kψ : Wick.FermionVertex κ → Fin 4 → ℝ) (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) :
    ℂ :=
  Wick.vertexFactor P.e (P.e ^ 2 * D.d₁ x 0) (P.e ^ 2 * D.d₂ x 0) (P.e ^ 2 * D.dm x 0)
    (P.e ^ 2 * D.d₃ 0) M α β lor kψ kA t

/-- The flavour read by the vertex factor of `t`. -/
def flOf (Φ : Lepton.Flavors F) (φ : Flavoring F κ) (t : Fin N) : F :=
  if h : κ t = .photonCt then Φ.openLine else φ ⟨t, h⟩

open scoped Classical in
/-- One index term of the amplitude (G₃) at the zero grading. -/
noncomputable def ampTerm (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (C : Contraction 1 nA κ) (φ : Flavoring F κ) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) :
    ℂ :=
  (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
    ((∏ t, vf0 P D (flOf Φ φ t) (Φ.mass (flOf Φ φ t)) α β lor (psiMomentum₂ C pIn k)
        (photonMomentum₂ C kIn k) t) *
      (∏ f : FermionLine C, (1 / I) *
        QED.OneLoop.electronPropagator (Φ.mass (φ f.1)) P.ε (k (.inl f)) (β f.1) (α f.tail)) *
      ∏ g' : PhotonLine C, (1 / I) *
        QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr g')) (lor g'.1) (lor g'.head))

theorem contractionAmplitude_zero_eq (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (C : Contraction 1 nA κ) (φ : Flavoring F κ) (pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) :
    QED.Graded.contractionAmplitude P Φ D C φ 0 pIn kIn k αOut βIn μ =
      ∑ α, ∑ β, ∑ lor, ampTerm P Φ D C φ pIn kIn k αOut βIn μ α β lor := by
  unfold QED.Graded.contractionAmplitude ampTerm vf0 flOf
  simp only [Pi.zero_apply, dite_eq_ite, ite_self, zero_add, mul_one]

/-- **The vertex factor of a fermion vertex is chirality-pure** in the mass. -/
theorem vertexFactor_pure (e δ₁ δ₂ δm δ₃ M : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (s : Wick.FermionVertex κ) :
    Wick.vertexFactor e δ₁ δ₂ δm δ₃ M α β lor kψ kA s.1 =
      if blk (α s) = blk (β s) then (M : ℂ) * (if κ s.1 = .fermionCt then
          -I * (δm : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ) (α s) (β s) else 0)
      else Wick.vertexFactor e δ₁ δ₂ 0 δ₃ 0 α β lor kψ kA s.1 := by
  unfold Wick.vertexFactor
  split
  next h =>
    simp only [h, reduceCtorEq, ite_false, mul_zero]
    split_ifs with hb
    · rw [gamma_eq_zero_of_blk _ hb, mul_zero]
    · rfl
  next h =>
    simp only [h, reduceCtorEq, ite_false, mul_zero]
    split_ifs with hb
    · rw [gamma_eq_zero_of_blk _ hb, mul_zero]
    · rfl
  next h =>
    simp only [h, ite_true, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs with hb
    · rw [slash_eq_zero_of_blk _ hb]
      push_cast
      ring
    · rw [one_eq_zero_of_blk hb]
      push_cast
      ring
  next h => exact absurd h s.2

/-! ### The loop vertices and lines -/

/-- `t` is a vertex of the closed loop `Z`. -/
def isLoopT (Z : Wick.FermionVertex κ → Prop) [DecidablePred Z] (t : Fin N) : Bool :=
  if h : κ t = .photonCt then false else decide (Z ⟨t, h⟩)

variable {Z : Wick.FermionVertex κ → Prop} [DecidablePred Z]

theorem isLoopT_iff (t : Fin N) : isLoopT Z t = true ↔ ∃ h : κ t ≠ .photonCt, Z ⟨t, h⟩ := by
  unfold isLoopT
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The vertex product split into the loop vertices and the others. -/
theorem prod_split_loopT (G : Fin N → ℂ) :
    ∏ t, G t = (∏ s : {s : Wick.FermionVertex κ // Z s}, G s.1.1) *
      ∏ t, (if isLoopT Z t = true then 1 else G t) := by
  have h1 : ∏ t, G t = (∏ t, if isLoopT Z t = true then G t else 1) *
      ∏ t, (if isLoopT Z t = true then 1 else G t) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    split_ifs <;> simp
  rw [h1, prod_ite_one_eq_subtype]
  congr 1
  refine (Fintype.prod_bijective (fun s : {s : Wick.FermionVertex κ // Z s} =>
    (⟨s.1.1, (isLoopT_iff _).2 ⟨s.1.2, s.2⟩⟩ : {t // isLoopT Z t = true})) ⟨fun s s' h => ?_,
      fun t => ?_⟩ _ _ fun s => rfl).symm
  · apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  · obtain ⟨h, hz⟩ := (isLoopT_iff _).1 t.2
    exact ⟨⟨⟨t.1, h⟩, hz⟩, rfl⟩

variable {C : Contraction 1 nA κ}

/-- The lines of the closed loop. -/
abbrev ZLine (C : Contraction 1 nA κ) (Z : Wick.FermionVertex κ → Prop) : Type :=
  {f : FermionLine C // Z f.1}

theorem sigma_tail (f : FermionLine C) : C.1.1 (.inr f.1) = .inr f.tail :=
  (Sum.inr_getRight _ _).symm

theorem isRight_of_Z (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x) {s : Wick.FermionVertex κ}
    (hs : Z s) : (C.1.1 (.inr s)).isRight := by
  have := hZ (.inr s)
  rcases h : C.1.1 (.inr s) with i | s'
  · rw [h] at this
    simp [isZ, hs] at this
  · rfl

theorem Z_tail (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x) (f : ZLine C Z) : Z f.1.tail := by
  have := hZ (.inr f.1.1)
  rw [sigma_tail] at this
  simpa [isZ, f.2] using this

theorem head_bijective (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x) :
    Function.Bijective fun f : ZLine C Z => (⟨f.1.1, f.2⟩ : {s // Z s}) :=
  ⟨fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun s => s.1) h)),
    fun s => ⟨⟨⟨s.1, isRight_of_Z hZ s.2⟩, s.2⟩, rfl⟩⟩

theorem tail_bijective (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x) :
    Function.Bijective fun f : ZLine C Z => (⟨f.1.tail, Z_tail hZ f⟩ : {s // Z s}) := by
  refine ⟨fun f f' h => ?_, fun s => ?_⟩
  · have h' : C.1.1 (.inr f.1.1) = C.1.1 (.inr f'.1.1) := by
      rw [sigma_tail, sigma_tail]
      exact congrArg (fun s => Sum.inr s.1) h
    exact Subtype.ext (Subtype.ext (Sum.inr_injective (C.1.1.injective h')))
  · set y := C.1.1.symm (.inr s.1) with hy
    have hσy : C.1.1 y = .inr s.1 := by simp [hy]
    have hzy : isZ Z y = true := by
      rw [← hZ y, hσy]
      simp [isZ, s.2]
    rcases y with i | s'
    · simp [isZ] at hzy
    · have hs' : Z s' := by simpa [isZ] using hzy
      have hr : (C.1.1 (.inr s')).isRight := by rw [hσy]; rfl
      refine ⟨⟨⟨s', hr⟩, hs'⟩, Subtype.ext ?_⟩
      have := sigma_tail (C := C) ⟨s', hr⟩
      rw [hσy] at this
      exact (Sum.inr_injective this).symm

theorem card_zLine (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x) :
    Fintype.card (ZLine C Z) = Fintype.card {s : Wick.FermionVertex κ // Z s} :=
  Fintype.card_of_bijective (head_bijective hZ)

theorem sgn_sq (a : Fin 4) : sgn a * sgn a = 1 := by
  fin_cases a <;> norm_num [sgn]

/-- **The sign product around the closed loop is `1`.** -/
theorem prod_sgn_closed (hZ : ∀ x, isZ Z (C.1.1 x) = isZ Z x)
    (α β : Wick.FermionVertex κ → Fin 4) :
    (∏ s : {s // Z s}, sgn (α s.1) * sgn (β s.1)) *
      ∏ f : ZLine C Z, sgn (β f.1.1) * sgn (α f.1.tail) = 1 := by
  rw [Finset.prod_mul_distrib (f := fun f : ZLine C Z => sgn (β f.1.1)),
    Fintype.prod_bijective _ (head_bijective hZ) (fun f : ZLine C Z => sgn (β f.1.1))
      (fun s => sgn (β s.1)) fun _ => rfl,
    Fintype.prod_bijective _ (tail_bijective hZ) (fun f : ZLine C Z => sgn (α f.1.tail))
      (fun s => sgn (α s.1)) fun _ => rfl,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun s _ => ?_
  linear_combination (sgn (β s.1) * sgn (β s.1)) * sgn_sq (α s.1) + sgn_sq (β s.1)

end QED.GradedProof.X0

end
