/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0NsLines

/-!
# (X₀): the index terms of a contraction with one closed loop, line by line

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), part B of
`TwoLoopClosedGoal`. Let `C` be a contraction of `gauge` vertices with the closed fermion loop
`zOf C` and flavour `f` on it. One index term of the amplitude (G₃) at the zero grading is a
constant times a product over the lines `l` of `C` of line factors (`ampTerm_ns`). On a loop
line the propagator entry is `M_f^{[same block]} N_l(k_l) D_{M_f}(k_l)⁻¹` with the pure entry
`N_l` (`electronNumerator_eq_ite`); on every other line it is `N_l(k_l) ∏_{M ∈ ms l} D_M(k_l)⁻¹`
(`nsNum`, `nsMs`; the photon propagator as two Pauli–Villars lines). Hence the term is
`M_f^p W(ℓ) ∏_{loop} D_{M_f}(k_l)⁻¹` with `p` even (`prod_nsFac`, `even_nsP`), the shape of
`jointEnergyFirstIntegrable_blockSumGen`, and its expansion terms have the shape of
`jointEnergyFirstIntegrable_lines` (`prod_nsNum_zExt`, `length_nsMs_zExt`, `affPoly_nsNum`).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.X0

open QED.Graded
open QED.WickModel
open QED.TwoLoop.Bridge (propDenom propDenom_ne_zero electronNumerator electronPropagator_apply
  photonPropagator_eq_mul)
open QED.TwoLoop.FurryIntegrable (sgn)

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind} {F : Type} {C : Contraction 1 nA κ}

/-- The index pair of a fermion line is in one chirality block. -/
def sameB (α β : Wick.FermionVertex κ → Fin 4) : Line C → Bool
  | .inl f => decide (blk (β f.1) = blk (α f.tail))
  | .inr _ => false

@[simp] theorem sameB_inl (α β : Wick.FermionVertex κ → Fin 4) (f : FermionLine C) :
    sameB α β (Sum.inl f : Line C) = decide (blk (β f.1) = blk (α f.tail)) := rfl

@[simp] theorem sameB_inr (α β : Wick.FermionVertex κ → Fin 4) (g : PhotonLine C) :
    sameB α β (Sum.inr g : Line C) = false := rfl

@[simp] theorem isZL_inl (f : FermionLine C) : isZL C (Sum.inl f) = decide (zOf C f.1) := rfl

@[simp] theorem isZL_inr (g : PhotonLine C) : isZL C (Sum.inr g) = false := rfl

/-- The numerator factor of a line. -/
noncomputable def nsNum (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) :
    Line C → (Fin 4 → ℝ) → ℂ
  | .inl f, k => if isZL C (.inl f) = true then
      (1 / I) * (if blk (β f.1) = blk (α f.tail) then (1 : Matrix (Fin 4) (Fin 4) ℂ) (β f.1)
        (α f.tail) else -Dirac.slash k (β f.1) (α f.tail))
      else if isTree C (.inl f) = true then
        (1 / I) * QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε k (β f.1) (α f.tail)
      else (1 / I) * electronNumerator (Φ.mass Φ.openLine) k (β f.1) (α f.tail)
  | .inr g, k => if isTree C (.inr g) = true then
      (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k (lor g.1) (lor g.head)
      else (1 / I) * ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)

/-- The masses of the denominators of a line off the loop. -/
def nsMs (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ) : Line C → List ℝ
  | .inl f => if isZL C (.inl f) = true then [] else
      if isTree C (.inl f) = true then [] else [Φ.mass Φ.openLine]
  | .inr g => if isTree C (.inr g) = true then [] else [P.mγ, P.Λ]

/-- The propagator entry of a line, mass `M` on the loop. -/
noncomputable def nsFac (P : Params) (Φ : Lepton.Flavors F) (C : Contraction 1 nA κ)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (M : ℝ) :
    Line C → (Fin 4 → ℝ) → ℂ
  | .inl f, k => (1 / I) * QED.OneLoop.electronPropagator
      (if isZL C (.inl f) = true then M else Φ.mass Φ.openLine) P.ε k (β f.1) (α f.tail)
  | .inr g, k => (1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε k (lor g.1) (lor g.head)

/-- The product of the inverse denominators with the masses of a list. -/
noncomputable def dProd (ε : ℝ) (ms : List ℝ) (k : Fin 4 → ℝ) : ℂ :=
  (ms.map fun M => (propDenom M ε k)⁻¹).prod

/-- **A line factor, split.** -/
theorem nsFac_eq (P : Params) (Φ : Lepton.Flavors F) (hε : P.ε ≠ 0)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (M : ℝ) (l : Line C)
    (k : Fin 4 → ℝ) :
    nsFac P Φ C α β lor M l k =
      (if isZL C l = true ∧ sameB α β l = true then (M : ℂ) else 1) *
        (nsNum P Φ C α β lor l k * dProd P.ε (nsMs P Φ C l) k) *
        (if isZL C l = true then (propDenom M P.ε k)⁻¹ else 1) := by
  rcases l with f | g
  · by_cases hz : isZL C (.inl f) = true
    · simp only [nsFac, nsNum, nsMs, sameB, hz, ↓reduceIte, true_and, dProd, List.map_nil,
        List.prod_nil, mul_one, decide_eq_true_eq]
      rw [electronPropagator_apply, electronNumerator_eq_ite]
      split_ifs <;> ring
    · by_cases ht : isTree C (.inl f) = true
      · simp [nsFac, nsNum, nsMs, hz, ht, dProd]
      · simp only [nsFac, nsNum, nsMs, hz, ht, Bool.false_eq_true, ↓reduceIte, false_and,
          dProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul]
        rw [electronPropagator_apply]
        ring
  · have hz : isZL C (.inr g) = false := rfl
    by_cases ht : isTree C (.inr g) = true
    · simp [nsFac, nsNum, nsMs, hz, ht, dProd]
    · simp only [nsFac, nsNum, nsMs, hz, ht, Bool.false_eq_true, ↓reduceIte, false_and,
        dProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul]
      rw [photonPropagator_eq_mul P.mγ P.Λ hε]
      ring

/-- The loop lines as a subtype of the lines. -/
abbrev ZL (C : Contraction 1 nA κ) : Type :=
  {l : Line C // isZL C l = true}

/-- The number of same-block loop entries. -/
def nsP (α β : Wick.FermionVertex κ → Fin 4) (C : Contraction 1 nA κ) : ℕ :=
  ((zSet C).filter fun l => sameB α β l = true).card

/-- **The product of the line factors**: `M^p W ∏_{loop} D_M⁻¹`. -/
theorem prod_nsFac (P : Params) (Φ : Lepton.Flavors F) (hε : P.ε ≠ 0)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) (M : ℝ)
    (k : Line C → Fin 4 → ℝ) :
    ∏ l, nsFac P Φ C α β lor M l (k l) =
      (M : ℂ) ^ nsP α β C * (∏ l, (nsNum P Φ C α β lor l (k l) *
        dProd P.ε (nsMs P Φ C l) (k l))) * ∏ x : ZL C, (propDenom M P.ε (k x.1))⁻¹ := by
  classical
  simp only [nsFac_eq P Φ hε α β lor M _ (k _), Finset.prod_mul_distrib]
  congr 1
  · congr 1
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, nsP, zSet,
      Finset.filter_filter]
  · exact prod_ite_one_eq_subtype (fun l => isZL C l = true) fun l => (propDenom M P.ε (k l))⁻¹

/-- The extra denominators `G x` on the loop lines. -/
def zExt (G : ZL C → List ℝ) (l : Line C) : List ℝ :=
  if h : isZL C l = true then G ⟨l, h⟩ else []

/-- **The expansion terms in the shape of `jointEnergyFirstIntegrable_lines`.** -/
theorem prod_nsNum_zExt (P : Params) (Φ : Lepton.Flavors F) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (G : ZL C → List ℝ) (k : Line C → Fin 4 → ℝ) :
    ∏ l, (nsNum P Φ C α β lor l (k l) * dProd P.ε (nsMs P Φ C l ++ zExt G l) (k l)) =
      (∏ l, (nsNum P Φ C α β lor l (k l) * dProd P.ε (nsMs P Φ C l) (k l))) *
        ∏ x : ZL C, dProd P.ε (G x) (k x.1) := by
  classical
  have h1 : ∀ l, dProd P.ε (nsMs P Φ C l ++ zExt G l) (k l) =
      dProd P.ε (nsMs P Φ C l) (k l) * dProd P.ε (zExt G l) (k l) := fun l => by
    simp only [dProd, List.map_append, List.prod_append]
  simp only [h1, ← mul_assoc, Finset.prod_mul_distrib]
  congr 1
  have h2 : ∀ l, dProd P.ε (zExt G l) (k l) =
      if h : isZL C l = true then dProd P.ε (G ⟨l, h⟩) (k l) else 1 := fun l => by
    unfold zExt
    split_ifs <;> simp [dProd]
  simp only [h2]
  have h3 : ∀ l, (if h : isZL C l = true then dProd P.ε (G ⟨l, h⟩) (k l) else 1) =
      if isZL C l = true then (if h : isZL C l = true then dProd P.ε (G ⟨l, h⟩) (k l) else 1)
        else 1 := fun l => by split_ifs <;> rfl
  rw [Finset.prod_congr rfl fun l _ => h3 l, prod_ite_one_eq_subtype (fun l => isZL C l = true)]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp only [x.2, ↓reduceDIte]

theorem zExt_pos (G : ZL C → List ℝ) {l : Line C} (h : isZL C l = true) :
    zExt G l = G ⟨l, h⟩ := by
  simp [zExt, h]

theorem zExt_neg (G : ZL C → List ℝ) {l : Line C} (h : isZL C l = false) : zExt G l = [] := by
  simp [zExt, h]

/-- The lengths of the lists of masses. -/
theorem length_nsMs_zExt (P : Params) (Φ : Lepton.Flavors F) (G : ZL C → List ℝ)
    (g : Line C → ℕ) (hG : ∀ x, (G x).length = 1 + g x.1)
    (hg : ∀ l, isZL C l = false → g l = 0) :
    (fun l => (nsMs P Φ C l ++ zExt G l).length) = fun l => baseN C l + g l := by
  funext l
  rcases l with f | g'
  · by_cases hz : isZL C (.inl f) = true
    · rw [zExt_pos G hz, List.length_append, hG]
      simp only [nsMs, baseN, hz, ↓reduceIte, List.length_nil]
      omega
    · have hz' : isZL C (.inl f) = false := by simpa using hz
      rw [zExt_neg G hz', List.append_nil, hg _ hz', add_zero]
      simp only [nsMs, baseN, hz', Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> rfl
  · rw [zExt_neg G rfl, List.append_nil, hg _ rfl, add_zero]
    simp only [nsMs, baseN]
    split_ifs <;> rfl

/-! ### The amplitude term, the parity, the degrees -/

open scoped Classical in
/-- The constant part of an index term: the external index constraints and the vertex
factors. -/
noncomputable def nsConst (P : Params) (C : Contraction 1 nA κ) (αOut βIn : Fin 1 → Fin 4)
    (μ : Fin nA → Fin 4) (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) :
    ℂ :=
  (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
      (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
      (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
    ∏ t, Wick.vertexFactor P.e 0 0 0 0 0 α β lor 0 0 t

/-- **An index term with flavour `f` on the closed loop** as a product of line factors. -/
theorem ampTerm_ns (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F)
    (hκ : ∀ t, κ t = .gauge) (f : F) (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4)
    (α β : Wick.FermionVertex κ → Fin 4) (lor : Wick.PhotonSlot κ → Fin 4) :
    ampTerm P Φ D C (closedFlavoring Φ (zOf C) f) pIn kIn k αOut βIn μ α β lor =
      nsConst P C αOut βIn μ α β lor * ∏ l, nsFac P Φ C α β lor (Φ.mass f) l (k l) := by
  have hv : ∀ t, vf0 P D (flOf Φ (closedFlavoring Φ (zOf C) f) t)
      (Φ.mass (flOf Φ (closedFlavoring Φ (zOf C) f) t)) α β lor (psiMomentum₂ C pIn k)
      (photonMomentum₂ C kIn k) t = Wick.vertexFactor P.e 0 0 0 0 0 α β lor 0 0 t :=
    fun t => vf0_gauge _ _ _ _ _ _ _ _ _ t (hκ t)
  have hm : ∀ fl : FermionLine C, Φ.mass (closedFlavoring Φ (zOf C) f fl.1) =
      if isZL C (.inl fl) = true then Φ.mass f else Φ.mass Φ.openLine := fun fl => by
    by_cases h : zOf C fl.1 <;> simp [closedFlavoring, isZL, h]
  unfold ampTerm nsConst
  rw [Fintype.prod_sum_type]
  simp only [hv, hm, nsFac]
  ring

/-- The line momenta at two loops. -/
theorem lineMomentum₂_eq_rowMom (pOut pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (l : Line C) :
    lineMomentum₂ C pOut pIn kIn ℓ l = rowMom (rowOf C l) (extPart C pOut pIn kIn l) ℓ := by
  rw [lineMomentum₂_eq_loopCoeff, Fin.sum_univ_two]
  simp [rowMom, rowOf]

/-- **Parity**: an even number of loop entries are same-block. -/
theorem even_nsP (α β : Wick.FermionVertex κ → Fin 4)
    (hZ : ∀ x, isZ (zOf C) (C.1.1 x) = isZ (zOf C) x)
    (hd : ∀ s : Wick.FermionVertex κ, ¬ blk (α s) = blk (β s)) : Even (nsP α β C) := by
  classical
  have h := even_card_blk_of_prod (fun f : ZLine C (zOf C) => β f.1.1)
    (fun f => α f.1.tail) (prod_sgn_zLine hZ α β fun s => hd s.1)
  have hc : (Finset.univ.filter fun f : ZLine C (zOf C) => blk (β f.1.1) = blk (α f.1.tail)).card
      = nsP α β C := by
    refine Finset.card_bij (fun f _ => (Sum.inl f.1 : Line C)) (fun f hf => ?_)
      (fun f _ f' _ h => Subtype.ext (Sum.inl_injective h)) (fun l hl => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      simp only [zSet, Finset.mem_filter, Finset.mem_univ, true_and, isZL_inl, sameB_inl,
        decide_eq_true_eq]
      exact ⟨f.2, hf⟩
    · simp only [zSet, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      rcases l with fl | g
      · refine ⟨⟨fl, by simpa [isZL] using hl.1⟩, ?_, rfl⟩
        simpa [sameB] using hl.2
      · simp [isZL] at hl
  rw [← hc]
  exact h

/-- The loop lines with a different-block entry. -/
def nsE (α β : Wick.FermionVertex κ → Fin 4) (C : Contraction 1 nA κ) : Finset (Line C) :=
  (zSet C).filter fun l => sameB α β l = false

theorem card_zSet_eq (α β : Wick.FermionVertex κ → Fin 4) :
    (zSet C).card = nsP α β C + (nsE α β C).card := by
  rw [nsP, nsE, ← Finset.card_filter_add_card_filter_not (s := zSet C)
    (fun l => sameB α β l = true)]
  congr 2

/-- An affine entry is `AffPoly 1`. -/
theorem affPoly_of_affine {G : (Fin 4 → ℝ) → ℂ}
    (hG : ∃ u : ℂ, ∃ w : Fin 4 → ℂ, ∀ k, G k = u + ∑ ν, w ν * (k ν : ℂ)) : AffPoly 1 G := by
  obtain ⟨u, w, h⟩ := hG
  rw [show G = fun k => u + ∑ ν, w ν * (k ν : ℂ) from funext h]
  exact AffPoly.aff u w

theorem rowOf_eq_zero {l : Line C} (h : isTree C l = true) : rowOf C l = 0 := by
  simp only [isTree, decide_eq_true_eq] at h
  funext i
  fin_cases i <;> simp [rowOf, h.1, h.2]

/-- **The degrees of the numerator factors.** -/
theorem affPoly_nsNum (P : Params) (Φ : Lepton.Flavors F) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (l : Line C) :
    AffPoly (baseD C (nsE α β C) l) (nsNum P Φ C α β lor l) ∨ rowOf C l = 0 := by
  rcases l with f | g
  · by_cases hz : isZL C (.inl f) = true
    · refine Or.inl ?_
      by_cases hb : blk (β f.1) = blk (α f.tail)
      · have hE : (Sum.inl f : Line C) ∉ nsE α β C := by
          simp only [nsE, Finset.mem_filter, sameB_inl, hb, decide_true, Bool.true_eq_false,
            and_false, not_false_eq_true]
        simp only [baseD, hz, hE, ↓reduceIte]
        refine (congrArg (AffPoly 0) (funext fun k => ?_)).mp (AffPoly.const ((1 / I) *
          (1 : Matrix (Fin 4) (Fin 4) ℂ) (β f.1) (α f.tail)))
        simp [nsNum, hz, hb]
      · have hE : (Sum.inl f : Line C) ∈ nsE α β C := by
          simp only [nsE, zSet, Finset.mem_filter, Finset.mem_univ, true_and, sameB_inl, hb,
            decide_false, and_true]
          exact hz
        simp only [baseD, hz, hE, ↓reduceIte]
        refine (congrArg (AffPoly 1) (funext fun k => ?_)).mp
          ((affPoly_of_affine (electronNumerator_affine 0 (β f.1) (α f.tail))).const_mul (1 / I))
        simp [nsNum, hz, hb, electronNumerator]
    · by_cases ht : isTree C (.inl f) = true
      · exact Or.inr (rowOf_eq_zero ht)
      · refine Or.inl ?_
        simp only [baseD, hz, ht, Bool.false_eq_true, ↓reduceIte]
        refine (congrArg (AffPoly 1) (funext fun k => ?_)).mp
          ((affPoly_of_affine (electronNumerator_affine (Φ.mass Φ.openLine) (β f.1)
            (α f.tail))).const_mul (1 / I))
        simp [nsNum, hz, ht]
  · by_cases ht : isTree C (.inr g) = true
    · exact Or.inr (rowOf_eq_zero ht)
    · refine Or.inl ?_
      simp only [baseD]
      refine (congrArg (AffPoly 0) (funext fun k => ?_)).mp (AffPoly.const ((1 / I) *
        ((Minkowski.metric (lor g.1) (lor g.head) * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)))
      simp [nsNum, ht]

end QED.GradedProof.X0

end
