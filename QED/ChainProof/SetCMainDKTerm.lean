/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainDKRoute

/-!
# Set (c), the `δ₃` classes: the terms of the longitudinal chain after the Ward identities

Helper level for the open links `QED.ChainProof.SetCMain.DKLimLink`, `DKCovLink`. After the Ward
identities of `QED/ChainProof/SetCMainDKWard.lean` every term of the longitudinal chain is a
chain `kOpen` whose two fixed vertices are one of `1`, `q̸`, `2m - A(p')`, `A(p) - 2m` (`KSlot`)
and whose electron matrices are those of the lines in a set `K`, the others replaced by `1`.

* `refinedBoundMat_openChain`, `refinedBoundMat_kOpen`, `isLoopPolyMat_kOpen`: the pointwise
  bound and the degree of a chain from those of its factors;
* `kK`, `kQ`: the electron and element momenta as line momenta of the ten-line unit;
* `KSlot`, `kSlotM`, `kNum`, `kSet`: the terms; **`refinedBoundMat_kNum`**,
  **`isLoopPolyMat_kNum`**, **`kNum_map`** (covariance under a spinor-lifted `L`);
* `RefinedBound.comp_filter`: the bound on the unit restricted along an injective line map.
-/

@[expose] public section
open Complex Matrix
open QED.Dirac (gamma slash vecAct)

namespace QED.ChainProof.SetCMain

open QED.TwoLoop.Enumeration QED.ChainProof.SetCUnitM QED.TwoLoop.LimitCovariance
open QED.WickModel (Params)
open QED.TwoLoop.Bridge (electronNumerator extMomenta IsLoopPoly IsLoopPolyMat IsLoopAffine
  isLoopAffine_lineMomentum)
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat refinedBound_electronNumerator)
open QED.TwoLoop.CountertermLimit (isLoopPolyMat_mono isLoopPolyMat_smul isLoopPolyMat_neg)
open QED.Integration.TwoLoop (lineMomentum castLoopMatrix class5LoopMatrix pvLines RefinedBound
  lineWeight)

/-! ### Bounds and degrees of chains -/

section Generic

variable {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ}

/-- **The pointwise bound of an open chain** whose factors are bounded by pairwise disjoint line
sets. -/
theorem refinedBoundMat_openChain
    {G : Fin 5 → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    {E : Fin 4 → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    {sG : Fin 5 → Finset (Fin (m + 1))} {sE : Fin 4 → Finset (Fin (m + 1))}
    {g : Fin 5 → ℕ} {e : Fin 4 → ℕ}
    (hG : ∀ t, RefinedBoundMat α (sG t) (g t) (G t))
    (hE : ∀ j, RefinedBoundMat α (sE j) (e j) (E j))
    (hGG : ∀ t t', t ≠ t' → Disjoint (sG t) (sG t')) (hGE : ∀ t j, Disjoint (sG t) (sE j))
    (hEE : ∀ j j', j ≠ j' → Disjoint (sE j) (sE j')) {S : Finset (Fin (m + 1))} {k : ℕ}
    (hSG : ∀ t, sG t ⊆ S) (hSE : ∀ j, sE j ⊆ S) (hk : ∑ t, g t + ∑ j, e j ≤ k) :
    RefinedBoundMat α S k fun ℓ => openChain (fun t => G t ℓ) (fun j => E j ℓ) := by
  have hEG : ∀ j t, Disjoint (sE j) (sG t) := fun j t => (hGE t j).symm
  have h := ((((((((hG 4).mul (hE 3) (hGE 4 3)).mul (hG 3) ?_).mul (hE 2) ?_).mul (hG 2)
    ?_).mul (hE 1) ?_).mul (hG 1) ?_).mul (hE 0) ?_).mul (hG 0) ?_
  · intro a b
    refine (h a b).mono ?_ ?_
    · simp only [Finset.union_subset_iff]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨hSG 4, hSE 3⟩, hSG 3⟩, hSE 2⟩, hSG 2⟩, hSE 1⟩, hSG 1⟩, hSE 0⟩, hSG 0⟩
    · simp only [Fin.sum_univ_five, Fin.sum_univ_four] at hk
      omega
  all_goals simp only [Finset.disjoint_union_left]
  · exact ⟨hGG 4 3 (by decide), hEG 3 3⟩
  · exact ⟨⟨hGE 4 2, hEE 3 2 (by decide)⟩, hGE 3 2⟩
  · exact ⟨⟨⟨hGG 4 2 (by decide), hEG 3 2⟩, hGG 3 2 (by decide)⟩, hEG 2 2⟩
  · exact ⟨⟨⟨⟨hGE 4 1, hEE 3 1 (by decide)⟩, hGE 3 1⟩, hEE 2 1 (by decide)⟩, hGE 2 1⟩
  · exact ⟨⟨⟨⟨⟨hGG 4 1 (by decide), hEG 3 1⟩, hGG 3 1 (by decide)⟩, hEG 2 1⟩,
      hGG 2 1 (by decide)⟩, hEG 1 1⟩
  · exact ⟨⟨⟨⟨⟨⟨hGE 4 0, hEE 3 0 (by decide)⟩, hGE 3 0⟩, hEE 2 0 (by decide)⟩, hGE 2 0⟩,
      hEE 1 0 (by decide)⟩, hGE 1 0⟩
  · exact ⟨⟨⟨⟨⟨⟨⟨hGG 4 0 (by decide), hEG 3 0⟩, hGG 3 0 (by decide)⟩, hEG 2 0⟩,
      hGG 2 0 (by decide)⟩, hEG 1 0⟩, hGG 1 0 (by decide)⟩, hEG 0 0⟩

/-- The degree of an open chain. -/
theorem isLoopPolyMat_openChain {G : Fin 5 → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    {E : Fin 4 → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} {g : Fin 5 → ℕ} {e : Fin 4 → ℕ}
    (hG : ∀ t, IsLoopPolyMat 2 (g t) (G t)) (hE : ∀ j, IsLoopPolyMat 2 (e j) (E j)) {k : ℕ}
    (hk : ∑ t, g t + ∑ j, e j ≤ k) :
    IsLoopPolyMat 2 k fun ℓ => openChain (fun t => G t ℓ) (fun j => E j ℓ) := by
  refine isLoopPolyMat_mono ((((((((((hG 4).mul (hE 3)).mul (hG 3)).mul (hE 2)).mul (hG 2)).mul
    (hE 1)).mul (hG 1)).mul (hE 0)).mul (hG 0))) ?_
  simp only [Fin.sum_univ_five, Fin.sum_univ_four] at hk
  omega

theorem refinedBoundMat_sum_smul {S : Finset (Fin (m + 1))} {k : ℕ} (c : Fin 4 → ℂ)
    {M : Fin 4 → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ z, RefinedBoundMat α S k (M z)) :
    RefinedBoundMat α S k fun ℓ => ∑ z, c z • M z ℓ := fun a b => by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact RefinedBound.sum _ fun z _ => (h z a b).const_mul _

variable (π : Equiv.Perm (Fin 5)) (μ : Fin 4)

/-- **The pointwise bound of `kOpen`** from those of its fixed vertices and electron matrices. -/
theorem refinedBoundMat_kOpen {X Y : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    {E : Fin 4 → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    {SX SY S : Finset (Fin (m + 1))} {SE : Fin 4 → Finset (Fin (m + 1))} {dX dY k : ℕ}
    {dE : Fin 4 → ℕ} (hX : RefinedBoundMat α SX dX X) (hY : RefinedBoundMat α SY dY Y)
    (hE : ∀ j, RefinedBoundMat α (SE j) (dE j) (E j)) (hXY : Disjoint SX SY)
    (hXE : ∀ j, Disjoint SX (SE j)) (hYE : ∀ j, Disjoint SY (SE j))
    (hEE : ∀ j j', j ≠ j' → Disjoint (SE j) (SE j')) (hSX : SX ⊆ S) (hSY : SY ⊆ S)
    (hSE : ∀ j, SE j ⊆ S) (hk : dX + dY + ∑ j, dE j ≤ k) :
    RefinedBoundMat α S k fun ℓ => kOpen π μ (X ℓ) (Y ℓ) (fun j => E j ℓ) := by
  unfold kOpen
  refine refinedBoundMat_sum_smul _ fun z => ?_
  have hW : ∀ t, RefinedBoundMat α ((![∅, SX, SY, ∅, ∅] : Fin 5 → Finset (Fin (m + 1))) t)
      ((![0, dX, dY, 0, 0] : Fin 5 → ℕ) t)
      (fun ℓ => (![gamma μ, X ℓ, Y ℓ, gamma z, gamma z] : Fin 5 → _) t) := fun t => by
    fin_cases t
    · exact RefinedBoundMat.const _
    · exact hX
    · exact hY
    · exact RefinedBoundMat.const _
    · exact RefinedBoundMat.const _
  have hWW : ∀ t t', t ≠ t' → Disjoint ((![∅, SX, SY, ∅, ∅] : Fin 5 → Finset (Fin (m + 1))) t)
      ((![∅, SX, SY, ∅, ∅] : Fin 5 → Finset (Fin (m + 1))) t') := fun t t' h => by
    fin_cases t <;> fin_cases t' <;> simp_all [hXY.symm]
  have hWE : ∀ t j, Disjoint ((![∅, SX, SY, ∅, ∅] : Fin 5 → Finset (Fin (m + 1))) t)
      (SE j) := fun t j => by
    fin_cases t <;> simp [hXE, hYE]
  have hSW : ∀ t, (![∅, SX, SY, ∅, ∅] : Fin 5 → Finset (Fin (m + 1))) t ⊆ S := fun t => by
    fin_cases t <;> simp [hSX, hSY]
  have h := refinedBoundMat_openChain (S := S) (k := k)
    (G := fun t ℓ => (![gamma μ, X ℓ, Y ℓ, gamma z, gamma z] : Fin 5 → _) (π.symm t))
    (sG := fun t => (![∅, SX, SY, ∅, ∅] : Fin 5 → Finset (Fin (m + 1))) (π.symm t))
    (g := fun t => (![0, dX, dY, 0, 0] : Fin 5 → ℕ) (π.symm t)) (fun t => hW _) hE
    (fun t t' h => hWW _ _ fun h' => h (π.symm.injective h')) (fun t j => hWE _ j) hEE
    (fun t => hSW _) hSE (by
      rw [Equiv.sum_comp π.symm (![0, dX, dY, 0, 0] : Fin 5 → ℕ)]
      simp only [Fin.sum_univ_five, Matrix.cons_val]
      omega)
  exact h

/-- **The degree of `kOpen`.** -/
theorem isLoopPolyMat_kOpen {X Y : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    {E : Fin 4 → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} {dX dY k : ℕ} {dE : Fin 4 → ℕ}
    (hX : IsLoopPolyMat 2 dX X) (hY : IsLoopPolyMat 2 dY Y)
    (hE : ∀ j, IsLoopPolyMat 2 (dE j) (E j)) (hk : dX + dY + ∑ j, dE j ≤ k) :
    IsLoopPolyMat 2 k fun ℓ => kOpen π μ (X ℓ) (Y ℓ) (fun j => E j ℓ) := by
  unfold kOpen
  intro a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine IsLoopPoly.sum _ fun z _ => IsLoopPoly.const_mul _ ?_
  have hW : ∀ t, IsLoopPolyMat 2 ((![0, dX, dY, 0, 0] : Fin 5 → ℕ) t)
      (fun ℓ => (![gamma μ, X ℓ, Y ℓ, gamma z, gamma z] : Fin 5 → _) t) := fun t => by
    fin_cases t
    · exact IsLoopPolyMat.const _
    · exact hX
    · exact hY
    · exact IsLoopPolyMat.const _
    · exact IsLoopPolyMat.const _
  exact isLoopPolyMat_openChain (k := k)
    (G := fun t ℓ => (![gamma μ, X ℓ, Y ℓ, gamma z, gamma z] : Fin 5 → _) (π.symm t))
    (g := fun t => (![0, dX, dY, 0, 0] : Fin 5 → ℕ) (π.symm t)) (fun t => hW _) hE (by
      rw [Equiv.sum_comp π.symm (![0, dX, dY, 0, 0] : Fin 5 → ℕ)]
      simp only [Fin.sum_univ_five, Matrix.cons_val]
      omega) a b

end Generic

/-! ### The momenta of the unit -/

/-- The unit line of the electron line `j`. -/
def eIdx (j : Fin 4) : Fin 10 := Fin.castLE (by omega) j

theorem eIdx_injective : Function.Injective eIdx := fun a b h => by
  simpa [eIdx, Fin.ext_iff] using h

theorem eIdx_ne_eight (j : Fin 4) : eIdx j ≠ 8 := by
  fin_cases j <;> decide

/-- The momentum of the electron line `j` of the unit. -/
noncomputable def kK (c : Class5) (σ : Fin 8) (p p' : Fin 4 → ℝ) (j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 4 → ℝ :=
  lineMomentum (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)) (unitMMomenta c σ ![1, 1] p p') (eIdx j) ℓ

/-- The element momentum, the momentum of the extra line `8` of the unit. -/
noncomputable def kQ (c : Class5) (σ : Fin 8) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Fin 4 → ℝ :=
  lineMomentum (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)) (unitMMomenta c σ ![1, 1] p p') 8 ℓ

theorem one_one_eq : ∀ j, (![1, 1] : Fin 2 → ℝ) j = 1 := by
  intro j; fin_cases j <;> rfl

theorem pvLines_mLine_eIdx : ∀ (σ : Fin 8) (j : Fin 4),
    pvLines (mLine (r := 2) σ (eIdx j)) = Fin.castLE (by omega) j := by
  decide

theorem mLine_eight : ∀ σ : Fin 8, mLine (r := 2) σ 8 = σ := by
  decide

theorem lineMomentum_class_eq_kK (c : Class5) (σ : Fin 8) (p p' : Fin 4 → ℝ) (j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (castLoopMatrix (class5LoopMatrix c)) (extMomenta c p p')
      (Fin.castLE (by omega) j) ℓ = kK c σ p p' j ℓ := by
  rw [kK, lineMomentum_unitM_one c σ one_one_eq, pvLines_mLine_eIdx]

theorem elemMom_eq_kQ (c : Class5) (σ : Fin 8) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    elemMom c σ p p' ℓ = kQ c σ p p' ℓ := by
  rw [kQ, lineMomentum_unitM_one c σ one_one_eq, mLine_eight]
  rfl

theorem dkMasses_eIdx (R : Params) (j : Fin 4) : dkMasses R (eIdx j) = R.m := by
  fin_cases j <;> rfl

section Map

variable {L : Matrix (Fin 4) (Fin 4) ℝ}

theorem kK_map (c : Class5) (σ : Fin 8) (p p' : Fin 4 → ℝ) (j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    kK c σ (L *ᵥ p) (L *ᵥ p') j (loopAct L ℓ) = L *ᵥ kK c σ p p' j ℓ := by
  unfold kK
  rw [unitMMomenta_map]
  exact QED.TwoLoop.ReflCovariance.lineMomentum_map _ _ _ _

theorem kQ_map (c : Class5) (σ : Fin 8) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kQ c σ (L *ᵥ p) (L *ᵥ p') (loopAct L ℓ) = L *ᵥ kQ c σ p p' ℓ := by
  unfold kQ
  rw [unitMMomenta_map]
  exact QED.TwoLoop.ReflCovariance.lineMomentum_map _ _ _ _

end Map

/-! ### The terms -/

/-- The fixed vertices of the terms: `1`, `q̸`, `2m - A(p')`, `A(p) - 2m`. -/
inductive KSlot
  | one
  | q
  | out
  | inn
  deriving DecidableEq

/-- The matrix of a fixed vertex. -/
noncomputable def kSlotM (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ) :
    KSlot → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ
  | .one, _ => 1
  | .q, ℓ => slash (kQ c σ p p' ℓ)
  | .out, _ => (2 * (m : ℂ)) • 1 - electronNumerator m p'
  | .inn, _ => electronNumerator m p - (2 * (m : ℂ)) • 1

/-- The lines bounding a fixed vertex. -/
def kSlotS : KSlot → Finset (Fin 10)
  | .q => {8}
  | _ => ∅

/-- The degree of a fixed vertex. -/
def kSlotD : KSlot → ℕ
  | .q => 1
  | _ => 0

theorem slash_eq_neg (k : Fin 4 → ℝ) : slash k = -electronNumerator 0 k := by
  simp [electronNumerator]

theorem refinedBoundMat_kSlotM (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ)
    (X : KSlot) :
    RefinedBoundMat (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)) (kSlotS X) (kSlotD X)
      (kSlotM c σ m p p' X) := by
  cases X
  · exact RefinedBoundMat.const _
  · intro a b
    simp only [kSlotM, kSlotS, kSlotD, slash_eq_neg, Matrix.neg_apply]
    exact (refinedBound_electronNumerator _ _ 8 0 a b).neg
  · exact RefinedBoundMat.const _
  · exact RefinedBoundMat.const _

theorem isLoopPolyMat_kSlotM (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ) (X : KSlot) :
    IsLoopPolyMat 2 (kSlotD X) (kSlotM c σ m p p' X) := by
  cases X
  · exact IsLoopPolyMat.const _
  · have e : kSlotM c σ m p p' .q = fun ℓ => -electronNumerator 0 (kQ c σ p p' ℓ) :=
      funext fun ℓ => slash_eq_neg _
    rw [e]
    exact isLoopPolyMat_neg ((isLoopAffine_lineMomentum _ _ _).isLoopPolyMat_electronNumerator 0)
  · exact IsLoopPolyMat.const _
  · exact IsLoopPolyMat.const _

theorem kSlotS_subset (X : KSlot) : kSlotS X ⊆ {8} := by
  cases X <;> simp [kSlotS]

theorem kSlotM_map {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S T) (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ) (X : KSlot)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * kSlotM c σ m (L *ᵥ p) (L *ᵥ p') X (loopAct L ℓ) * T = kSlotM c σ m p p' X ℓ := by
  cases X
  · simp [kSlotM, h.mul_eq_one]
  · simp only [kSlotM, kQ_map, h.mul_slash_mul]
  · simp only [kSlotM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, h.mul_eq_one, h.mul_electronNumerator_mul]
  · simp only [kSlotM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, h.mul_eq_one, h.mul_electronNumerator_mul]

/-- The electron matrices of a term: the lines in `K`, the others `1`. -/
noncomputable def kEK (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ) (K : Finset (Fin 4))
    (j : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  if j ∈ K then electronNumerator m (kK c σ p p' j ℓ) else 1

theorem kEK_update (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ) (K : Finset (Fin 4))
    (d : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Function.update (fun j => kEK c σ m p p' K j ℓ) d 1 =
      fun j => kEK c σ m p p' (K.erase d) j ℓ := by
  funext j
  by_cases h : j = d
  · subst h; simp [kEK]
  · simp [kEK, h]

/-- **A term**: the chain `kOpen` with fixed vertices `X`, `Y` and the electron lines `K`. -/
noncomputable def kNum (π : Equiv.Perm (Fin 5)) (c : Class5) (σ : Fin 8) (m : ℝ)
    (p p' : Fin 4 → ℝ) (X Y : KSlot) (K : Finset (Fin 4)) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  kOpen π μ (kSlotM c σ m p p' X ℓ) (kSlotM c σ m p p' Y ℓ) (fun j => kEK c σ m p p' K j ℓ)

/-- The lines bounding a term. -/
def kSet (X Y : KSlot) (K : Finset (Fin 4)) : Finset (Fin 10) :=
  K.image eIdx ∪ kSlotS X ∪ kSlotS Y

section Term

variable (π : Equiv.Perm (Fin 5)) (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ)
  (X Y : KSlot) (K : Finset (Fin 4)) (μ : Fin 4)

theorem refinedBoundMat_kEK (j : Fin 4) :
    RefinedBoundMat (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)) (if j ∈ K then {eIdx j} else ∅)
      (if j ∈ K then 1 else 0) (kEK c σ m p p' K j) := by
  by_cases h : j ∈ K
  · have e : kEK c σ m p p' K j = fun ℓ => electronNumerator m (kK c σ p p' j ℓ) :=
      funext fun ℓ => by simp [kEK, h]
    simp only [h, ite_true, e]
    exact fun a b => refinedBound_electronNumerator _ _ (eIdx j) m a b
  · have e : kEK c σ m p p' K j = fun _ => 1 := funext fun ℓ => by simp [kEK, h]
    simp only [h, ite_false, e]
    exact RefinedBoundMat.const _

theorem isLoopPolyMat_kEK (j : Fin 4) :
    IsLoopPolyMat 2 (if j ∈ K then 1 else 0) (kEK c σ m p p' K j) := by
  by_cases h : j ∈ K
  · have e : kEK c σ m p p' K j = fun ℓ => electronNumerator m (kK c σ p p' j ℓ) :=
      funext fun ℓ => by simp [kEK, h]
    simp only [h, ite_true, e]
    exact (isLoopAffine_lineMomentum _ _ _).isLoopPolyMat_electronNumerator m
  · have e : kEK c σ m p p' K j = fun _ => 1 := funext fun ℓ => by simp [kEK, h]
    simp only [h, ite_false, e]
    exact IsLoopPolyMat.const _

theorem sum_ite_mem_one (K : Finset (Fin 4)) : ∑ j, (if j ∈ K then 1 else 0) = K.card := by
  simp

/-- **The pointwise bound of a term** on the unit. -/
theorem refinedBoundMat_kNum (hXY : Disjoint (kSlotS X) (kSlotS Y))
    (hd : kSlotD X + kSlotD Y + K.card ≤ 4) :
    RefinedBoundMat (unitMMatrix c σ (![1, 1] : Fin 2 → ℝ)) (kSet X Y K) 4
      (kNum π c σ m p p' X Y K μ) := by
  have hE8 : ∀ (Z : KSlot) (j : Fin 4), Disjoint (kSlotS Z) (if j ∈ K then {eIdx j} else ∅) :=
    fun Z j => by
      refine Finset.disjoint_of_subset_left (kSlotS_subset Z) ?_
      split_ifs
      · simpa using (eIdx_ne_eight j).symm
      · simp
  refine refinedBoundMat_kOpen π μ (refinedBoundMat_kSlotM c σ m p p' X)
    (refinedBoundMat_kSlotM c σ m p p' Y) (refinedBoundMat_kEK c σ m p p' K) hXY (hE8 X)
    (hE8 Y) (fun j j' h => ?_) ?_ ?_ (fun j => ?_) ?_
  · split_ifs <;> simp [eIdx_injective.ne h]
  · unfold kSet; exact Finset.subset_union_right.trans Finset.subset_union_left
  · unfold kSet; exact Finset.subset_union_right
  · split_ifs with h
    · unfold kSet
      simpa using Or.inl ⟨j, h, rfl⟩
    · simp
  · rw [sum_ite_mem_one]; exact hd

/-- **The degree of a term.** -/
theorem isLoopPolyMat_kNum (hd : kSlotD X + kSlotD Y + K.card ≤ 4) :
    IsLoopPolyMat 2 4 (kNum π c σ m p p' X Y K μ) :=
  isLoopPolyMat_kOpen π μ (isLoopPolyMat_kSlotM c σ m p p' X) (isLoopPolyMat_kSlotM c σ m p p' Y)
    (isLoopPolyMat_kEK c σ m p p' K) (by rw [sum_ite_mem_one]; exact hd)

/-- **Covariance of a term** under a spinor-lifted `L`. -/
theorem kNum_map {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S T) (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * kNum π c σ m (L *ᵥ p) (L *ᵥ p') X Y K μ (loopAct L ℓ) * T =
      vecAct L (fun ν => kNum π c σ m p p' X Y K ν ℓ) μ := by
  refine mul_kOpen_mul h π (kSlotM_map h c σ m p p' X ℓ) (kSlotM_map h c σ m p p' Y ℓ)
    (fun j => ?_) μ
  unfold kEK
  split_ifs
  · rw [kK_map]; exact h.mul_electronNumerator_mul _ _
  · simp [h.mul_eq_one]

end Term

/-! ### Restriction along a line map -/

/-- **The pointwise bound along an injective line map** whose range contains the lines. -/
theorem RefinedBound.comp_filter {m k n : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ}
    (ι : Fin (k + 1) → Fin (m + 1)) (hι : Function.Injective ι) {S : Finset (Fin (m + 1))}
    (hS : ∀ x ∈ S, ∃ a, ι a = x) {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (h : RefinedBound α S n F) :
    RefinedBound (fun a => α (ι a)) (Finset.univ.filter fun a => ι a ∈ S) n F := by
  obtain ⟨C, hC, hF⟩ := h
  refine ⟨C, hC, fun A hA ℓ => ?_⟩
  have himg : (Finset.univ.filter fun a => ι a ∈ S).image ι = S := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun ⟨a, ha, hax⟩ => hax ▸ ha, fun hx => ?_⟩
    obtain ⟨a, ha⟩ := hS x hx
    exact ⟨a, ha ▸ hx, ha⟩
  have hw : lineWeight (fun a => α (ι a)) (Finset.univ.filter fun a => ι a ∈ S) A =
      lineWeight α S A := by
    unfold lineWeight
    calc _ = ∏ x ∈ (Finset.univ.filter fun a => ι a ∈ S).image ι,
          Real.sqrt (1 + α x ⬝ᵥ A⁻¹ *ᵥ α x) :=
          (Finset.prod_image fun a _ b _ h => hι h).symm
      _ = _ := by rw [himg]
  rw [hw]
  exact hF A hA ℓ

end QED.ChainProof.SetCMain

end
