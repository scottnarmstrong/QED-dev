/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKQ

/-!
# Set (c): the second-level identities of the doubly pinched values

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSum` (`QED/ChainProof/SetCRegKKNorm.lean`).
A doubly pinched value `QED.ChainProof.SetCRegDisp.kkQ` carries no element momentum in its
numerator: the chain has `1` at both ends of the element line, and `k²` only depends on the sign
of `k`. Two doubly pinched values of different classes agree when, after a unimodular change of
loop momenta, the kept lines match one to one with equal masses and integer vectors equal up to
sign, the element momenta agree up to sign, and the two chains agree with the electron lines
identified along the change. Six such identities of the second Ward level:

`Q(0, 0, 3) = Q(3, 3, 0)`, `Q(1, 0, 3) = Q(2, 0, 3)`, `Q(10, 0, 3) = Q(9, 3, 0)`,
`Q(1, 0, 2) = Q(7, 2, 0)`, `Q(7, 2, 1) = Q(8, 2, 3)`, `Q(6, 0, 3) = Q(4, 0, 3)`;

the last one exchanges the two photon lines `4 ↔ 5`, `6 ↔ 7` of the two slots.

* `dkCls`, `dkMasses_cls`: the mass classes of the ten lines;
* **`kkDen_chgD_perm`**: the denominators after a change, along a matching of the lines;
* `kkQ_comm`: `Q(i, d, d') = Q(i, d', d)`;
* `QChain`, **`kNi_one_one_chgD`**: the chains with `1` at both ends after a change;
* `QChg`, **`kkQ_chgD`**: the criterion for two doubly pinched values to agree;
* **`kkQ_zero_three`**, **`kkQ_one_two`**, **`kkQ_ten_nine`**, **`kkQ_one_seven`**,
  **`kkQ_seven_eight`**, **`kkQ_six_four`**: the six identities.
-/

@[expose] public section

open Complex
open QED.WickModel (Params)
open QED.Dirac (gamma slash)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.TwoLoop.Enumeration QED.TwoLoop.LimitCovariance
open QED.TwoLoop.Bridge (electronNumerator)
open QED.Integration.TwoLoop (lineDenom)

/-! ### Masses and denominators along a matching of the lines -/

/-- The mass class of a line of the unit: `m`, `m_γ`, `Λ`. -/
def dkCls : Fin 10 → Fin 3 := ![0, 0, 0, 0, 1, 1, 2, 2, 1, 2]

theorem dkMasses_cls (R : Params) (q : Fin 10) :
    dkMasses R q = (![R.m, R.mγ, R.Λ] : Fin 3 → ℝ) (dkCls q) := by
  fin_cases q <;> rfl

section Den

variable {k : ℕ} (i i' : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ)
  (M : Matrix (Fin 2) (Fin 2) ℤ) (A : Fin 2 → Fin 2 → ℤ)

/-- **The denominators after the change, along a matching `σ` of the lines**: equal when the
matched lines have the same mass class and the same integer vectors up to sign. -/
theorem kkDen_chgD_perm (ι ι' : Fin (k + 1) → Fin 10) (σ : Equiv.Perm (Fin (k + 1)))
    (h : ∀ b, uVec i M A (ι b) = uVec i' 1 0 (ι' (σ b)) ∨
      uVec i M A (ι b) = -uVec i' 1 0 (ι' (σ b)))
    (hc : ∀ b, dkCls (ι b) = dkCls (ι' (σ b))) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkDen i R p p' ι ε (chgD M A p (p' - p) ℓ) = kkDen i' R p p' ι' ε ℓ := by
  unfold kkDen
  refine Fintype.prod_equiv σ _ _ fun b => ?_
  have e : ∀ (j : Fin 12) (ι₀ : Fin (k + 1) → Fin 10) (c : Fin (k + 1))
      (ℓ' : Fin 2 → Fin 4 → ℝ),
      lineDenom (fun a => unitMMatrix (repBClass j) (repBSlot j) (![1, 1] : Fin 2 → ℝ) (ι₀ a))
        (fun a => unitMMomenta (repBClass j) (repBSlot j) ![1, 1] p p' (ι₀ a))
        (fun a => dkMasses R (ι₀ a)) ε c ℓ' =
      lineDenom (unitMMatrix (repBClass j) (repBSlot j) (![1, 1] : Fin 2 → ℝ))
        (unitMMomenta (repBClass j) (repBSlot j) ![1, 1] p p') (dkMasses R) ε (ι₀ c) ℓ' :=
    fun _ _ _ _ => rfl
  rw [e, e]
  unfold lineDenom
  rw [lineMomentum_unit_chgD, lineMomentum_unit_eq, dot_mvReal_of (h b), dkMasses_cls,
    dkMasses_cls R (ι' (σ b)), hc b]

/-- **A term after the change, along a matching of the lines.** -/
theorem kkT_chgD_perm (ι ι' : Fin (k + 1) → Fin 10) (σ : Equiv.Perm (Fin (k + 1)))
    (F F' : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (h : ∀ b, uVec i M A (ι b) = uVec i' 1 0 (ι' (σ b)) ∨
      uVec i M A (ι b) = -uVec i' 1 0 (ι' (σ b)))
    (hc : ∀ b, dkCls (ι b) = dkCls (ι' (σ b)))
    (h8 : uVec i M A 8 = uVec i' 1 0 8 ∨ uVec i M A 8 = -uVec i' 1 0 8)
    (hF : ∀ ℓ, F (chgD M A p (p' - p) ℓ) = F' ℓ) (ε x : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kkT i R p p' t ι F ε x (chgD M A p (p' - p) ℓ) = kkT i' R p p' t ι' F' ε x ℓ := by
  unfold kkT
  rw [hF, kkDen_chgD_perm i i' R p p' M A ι ι' σ h hc, kkSpec_chgD i i' p p' t M A h8]

end Den

/-! ### Exchanging the two deleted lines -/

theorem qι_comm : ∀ d d' : Fin 4, d ≠ d' → qι d d' = qι d' d := by
  decide

theorem erase_erase_comm (d d' : Fin 4) :
    (Finset.univ.erase d).erase d' = (Finset.univ.erase d').erase d :=
  Finset.erase_right_comm

/-- `Q(i, d, d') = Q(i, d', d)`. -/
theorem kkQ_comm (i : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) {d d' : Fin 4}
    (hd : d ≠ d') (μ a b : Fin 4) (x : ℝ) :
    kkQ i R p p' t d d' μ a b x = kkQ i R p p' t d' d μ a b x := by
  unfold kkQ
  rw [qι_comm d d' hd, erase_erase_comm]

/-! ### The chains with `1` at both ends -/

/-- The chains of `repB i` with the electron lines `K` and of `repB i'` with the electron lines
`K'` agree, the line `j ∈ K` identified with `τ j ∈ K'`. -/
def QChain (i : Fin 12) (K : Finset (Fin 4)) (i' : Fin 12) (K' : Finset (Fin 4))
    (τ : Fin 4 → Fin 4) : Prop :=
  ∀ (μ : Fin 4) (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ),
    kOpen (kPermD i) μ 1 1 (fun j => if j ∈ K then E (τ j) else 1) =
      kOpen (kPermD i') μ 1 1 (fun j => if j ∈ K' then E j else 1)

/-- **The chains with `1` at both ends after the change.** -/
theorem kNi_one_one_chgD {i i' : Fin 12} {K K' : Finset (Fin 4)} {τ : Fin 4 → Fin 4}
    {M : Matrix (Fin 2) (Fin 2) ℤ} {A : Fin 2 → Fin 2 → ℤ} (hc : QChain i K i' K' τ)
    (hK : ∀ j ∈ K, uVec i M A (eIdx j) = uVec i' 1 0 (eIdx (τ j)))
    (R : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kNi i R p p' .one .one K μ (chgD M A p (p' - p) ℓ) = kNi i' R p p' .one .one K' μ ℓ := by
  have hE : (fun j => kEK (repBClass i) (repBSlot i) R.m p p' K j (chgD M A p (p' - p) ℓ)) =
      fun j => if j ∈ K then (fun j' => electronNumerator R.m
        (kK (repBClass i') (repBSlot i') p p' j' ℓ)) (τ j) else 1 := by
    funext j
    unfold kEK
    split_ifs with hj
    · rw [kK_chgD, hK j hj, ← kK_chgD, chgD_one_zero]
    · rfl
  unfold kNi kNum
  simp only [kSlotM]
  rw [hE]
  exact hc μ fun j' => electronNumerator R.m (kK (repBClass i') (repBSlot i') p p' j' ℓ)

/-! ### The criterion -/

/-- The kernel-decidable line data of a second-level identity: along the change `M`, `A` and
the matching `σ`, the kept lines of `Q(i, d, d')` match those of `Q(i', e, e')` up to sign with
the same mass classes, the element momenta agree up to sign, and the kept electron line `j`
becomes the electron line `τ j`. -/
def QChg (i : Fin 12) (d d' : Fin 4) (i' : Fin 12) (e e' : Fin 4) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (A : Fin 2 → Fin 2 → ℤ) (σ : Equiv.Perm (Fin 8)) (τ : Fin 4 → Fin 4) : Prop :=
  (∀ b, uVec i M A (qι d d' b) = uVec i' 1 0 (qι e e' (σ b)) ∨
      uVec i M A (qι d d' b) = -uVec i' 1 0 (qι e e' (σ b))) ∧
    (∀ b, dkCls (qι d d' b) = dkCls (qι e e' (σ b))) ∧
    (uVec i M A 8 = uVec i' 1 0 8 ∨ uVec i M A 8 = -uVec i' 1 0 8) ∧
    ∀ j ∈ (Finset.univ.erase d).erase d', uVec i M A (eIdx j) = uVec i' 1 0 (eIdx (τ j))

instance (i : Fin 12) (d d' : Fin 4) (i' : Fin 12) (e e' : Fin 4) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (A : Fin 2 → Fin 2 → ℤ) (σ : Equiv.Perm (Fin 8)) (τ : Fin 4 → Fin 4) :
    Decidable (QChg i d d' i' e e' M A σ τ) := by
  unfold QChg; infer_instance

theorem elemSq_chgD {i i' : Fin 12} {M : Matrix (Fin 2) (Fin 2) ℤ} {A : Fin 2 → Fin 2 → ℤ}
    (h8 : uVec i M A 8 = uVec i' 1 0 8 ∨ uVec i M A 8 = -uVec i' 1 0 8) (p p' : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    elemSq (repBClass i) (repBSlot i) p p' (chgD M A p (p' - p) ℓ) =
      elemSq (repBClass i') (repBSlot i') p p' ℓ := by
  unfold elemSq
  rw [elemMom_chgD, ← chgD_one_zero p (p' - p) ℓ, elemMom_chgD, chgD_one_zero,
    dot_mvReal_of h8]

/-- **Two doubly pinched values agree** under the line data `QChg` and the chain identity. -/
theorem kkQ_chgD {i i' : Fin 12} {d d' e e' : Fin 4} {M : Matrix (Fin 2) (Fin 2) ℤ}
    {A : Fin 2 → Fin 2 → ℤ} {σ : Equiv.Perm (Fin 8)} {τ : Fin 4 → Fin 4} (hM : IsUnit M.det)
    (h : QChg i d d' i' e e' M A σ τ)
    (hc : QChain i ((Finset.univ.erase d).erase d') i' ((Finset.univ.erase e).erase e') τ)
    (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (μ a b : Fin 4) (x : ℝ) :
    kkQ i R p p' t d d' μ a b x = kkQ i' R p p' t e e' μ a b x := by
  obtain ⟨hl, hm, h8, hK⟩ := h
  have hF : ∀ ℓ, kNi i R p p' .one .one ((Finset.univ.erase d).erase d') μ
        (chgD M A p (p' - p) ℓ) a b * elemSq (repBClass i) (repBSlot i) p p'
          (chgD M A p (p' - p) ℓ) =
      kNi i' R p p' .one .one ((Finset.univ.erase e).erase e') μ ℓ a b *
        elemSq (repBClass i') (repBSlot i') p p' ℓ := fun ℓ => by
    rw [kNi_one_one_chgD hc hK, elemSq_chgD h8]
  unfold kkQ
  exact (kkLimX_chgD M hM A p (p' - p) (fun ε x ℓ => (kkT_chgD_perm i i' R p p' t M A
    (qι d d') (qι e e') σ _ _ hl hm h8 hF ε x ℓ).symm) x).symm

/-! ### The six identities -/

section Pairs

variable (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (μ a b : Fin 4) (x : ℝ)

theorem qChain_zero_three :
    QChain 0 ((Finset.univ.erase 0).erase 3) 3 ((Finset.univ.erase 0).erase 3) id := by
  intro μ E
  unfold kOpen
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ocW_eq, ocW_eq, kPermD_symm (i := 0) (t := 2) (k := 0) rfl,
    kPermD_symm (i := 0) (t := 4) (k := 1) rfl, kPermD_symm (i := 0) (t := 0) (k := 2) rfl,
    kPermD_symm (i := 0) (t := 3) (k := 3) rfl, kPermD_symm (i := 0) (t := 1) (k := 4) rfl,
    kPermD_symm (i := 3) (t := 2) (k := 0) rfl, kPermD_symm (i := 3) (t := 3) (k := 1) rfl,
    kPermD_symm (i := 3) (t := 0) (k := 2) rfl, kPermD_symm (i := 3) (t := 4) (k := 3) rfl,
    kPermD_symm (i := 3) (t := 1) (k := 4) rfl]
  simp [Matrix.mul_assoc]

/-- The change of loop momenta from `repB 0` to `repB 3`. -/
def chgQ_zero_three : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, -1]

theorem isUnit_det_chgQ_zero_three : IsUnit chgQ_zero_three.det := by
  rw [Int.isUnit_iff]; simp [chgQ_zero_three, Matrix.det_fin_two]

/-- **`Q(0, 0, 3) = Q(3, 3, 0)`: the term of `0` with both lines deleted and the second
doubly pinched value of `P(3, 3)`.** -/
theorem kkQ_zero_three :
    kkQ 0 R p p' t 0 3 μ a b x = kkQ 3 R p p' t 3 0 μ a b x := by
  rw [kkQ_comm 3 R p p' t (by decide : (3 : Fin 4) ≠ 0)]
  exact kkQ_chgD (A := 0) (σ := Equiv.refl _) isUnit_det_chgQ_zero_three
    (by decide +kernel) qChain_zero_three R p p' t μ a b x

theorem qChain_one_two :
    QChain 1 ((Finset.univ.erase 0).erase 3) 2 ((Finset.univ.erase 0).erase 3) id := by
  intro μ E
  unfold kOpen
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ocW_eq, ocW_eq, kPermD_symm (i := 1) (t := 2) (k := 0) rfl,
    kPermD_symm (i := 1) (t := 1) (k := 1) rfl, kPermD_symm (i := 1) (t := 3) (k := 2) rfl,
    kPermD_symm (i := 1) (t := 4) (k := 3) rfl, kPermD_symm (i := 1) (t := 0) (k := 4) rfl,
    kPermD_symm (i := 2) (t := 2) (k := 0) rfl, kPermD_symm (i := 2) (t := 1) (k := 1) rfl,
    kPermD_symm (i := 2) (t := 4) (k := 2) rfl, kPermD_symm (i := 2) (t := 3) (k := 3) rfl,
    kPermD_symm (i := 2) (t := 0) (k := 4) rfl]
  simp [Matrix.mul_assoc]

/-- The change of loop momenta from `repB 1` to `repB 2`. -/
def chgQ_one_two : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, -1]

theorem isUnit_det_chgQ_one_two : IsUnit chgQ_one_two.det := by
  rw [Int.isUnit_iff]; simp [chgQ_one_two, Matrix.det_fin_two]

/-- **`Q(1, 0, 3) = Q(2, 0, 3)`.** -/
theorem kkQ_one_two :
    kkQ 1 R p p' t 0 3 μ a b x = kkQ 2 R p p' t 0 3 μ a b x := by
  exact kkQ_chgD (A := 0) (σ := Equiv.refl _) isUnit_det_chgQ_one_two
    (by decide +kernel) qChain_one_two R p p' t μ a b x

theorem qChain_ten_nine :
    QChain 10 ((Finset.univ.erase 0).erase 3) 9 ((Finset.univ.erase 0).erase 3) id := by
  intro μ E
  unfold kOpen
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ocW_eq, ocW_eq, kPermD_symm (i := 10) (t := 1) (k := 0) rfl,
    kPermD_symm (i := 10) (t := 4) (k := 1) rfl, kPermD_symm (i := 10) (t := 0) (k := 2) rfl,
    kPermD_symm (i := 10) (t := 3) (k := 3) rfl, kPermD_symm (i := 10) (t := 2) (k := 4) rfl,
    kPermD_symm (i := 9) (t := 1) (k := 0) rfl, kPermD_symm (i := 9) (t := 3) (k := 1) rfl,
    kPermD_symm (i := 9) (t := 0) (k := 2) rfl, kPermD_symm (i := 9) (t := 4) (k := 3) rfl,
    kPermD_symm (i := 9) (t := 2) (k := 4) rfl]
  simp [Matrix.mul_assoc]

/-- The change of loop momenta from `repB 10` to `repB 9`. -/
def chgQ_ten_nine : Matrix (Fin 2) (Fin 2) ℤ := 1

theorem isUnit_det_chgQ_ten_nine : IsUnit chgQ_ten_nine.det := by
  rw [Int.isUnit_iff]; simp [chgQ_ten_nine]

/-- **`Q(10, 0, 3) = Q(9, 3, 0)`: the term of `10` with both lines deleted and the second
doubly pinched value of `P(9, 3)` (the same loop routing).** -/
theorem kkQ_ten_nine :
    kkQ 10 R p p' t 0 3 μ a b x = kkQ 9 R p p' t 3 0 μ a b x := by
  rw [kkQ_comm 9 R p p' t (by decide : (3 : Fin 4) ≠ 0)]
  exact kkQ_chgD (A := 0) (σ := Equiv.refl _) isUnit_det_chgQ_ten_nine
    (by decide +kernel) qChain_ten_nine R p p' t μ a b x

theorem qChain_one_seven :
    QChain 1 ((Finset.univ.erase 0).erase 2) 7 ((Finset.univ.erase 0).erase 2) id := by
  intro μ E
  unfold kOpen
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ocW_eq, ocW_eq, kPermD_symm (i := 1) (t := 2) (k := 0) rfl,
    kPermD_symm (i := 1) (t := 1) (k := 1) rfl, kPermD_symm (i := 1) (t := 3) (k := 2) rfl,
    kPermD_symm (i := 1) (t := 4) (k := 3) rfl, kPermD_symm (i := 1) (t := 0) (k := 4) rfl,
    kPermD_symm (i := 7) (t := 3) (k := 0) rfl, kPermD_symm (i := 7) (t := 2) (k := 1) rfl,
    kPermD_symm (i := 7) (t := 1) (k := 2) rfl, kPermD_symm (i := 7) (t := 4) (k := 3) rfl,
    kPermD_symm (i := 7) (t := 0) (k := 4) rfl]
  simp [Matrix.mul_assoc]

/-- The change of loop momenta from `repB 1` to `repB 7`. -/
def chgQ_one_seven : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 1, 0]

theorem isUnit_det_chgQ_one_seven : IsUnit chgQ_one_seven.det := by
  rw [Int.isUnit_iff]; simp [chgQ_one_seven, Matrix.det_fin_two]

/-- **`Q(1, 0, 2) = Q(7, 2, 0)`.** -/
theorem kkQ_one_seven :
    kkQ 1 R p p' t 0 2 μ a b x = kkQ 7 R p p' t 2 0 μ a b x := by
  rw [kkQ_comm 7 R p p' t (by decide : (2 : Fin 4) ≠ 0)]
  exact kkQ_chgD (A := 0) (σ := Equiv.refl _) isUnit_det_chgQ_one_seven
    (by decide +kernel) qChain_one_seven R p p' t μ a b x

theorem qChain_seven_eight :
    QChain 7 ((Finset.univ.erase 2).erase 1) 8 ((Finset.univ.erase 2).erase 3) ![0, 0, 0, 1] := by
  intro μ E
  unfold kOpen
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ocW_eq, ocW_eq, kPermD_symm (i := 7) (t := 3) (k := 0) rfl,
    kPermD_symm (i := 7) (t := 2) (k := 1) rfl, kPermD_symm (i := 7) (t := 1) (k := 2) rfl,
    kPermD_symm (i := 7) (t := 4) (k := 3) rfl, kPermD_symm (i := 7) (t := 0) (k := 4) rfl,
    kPermD_symm (i := 8) (t := 1) (k := 0) rfl, kPermD_symm (i := 8) (t := 2) (k := 1) rfl,
    kPermD_symm (i := 8) (t := 4) (k := 2) rfl, kPermD_symm (i := 8) (t := 3) (k := 3) rfl,
    kPermD_symm (i := 8) (t := 0) (k := 4) rfl]
  simp [Matrix.mul_assoc]

/-- The change of loop momenta from `repB 7` to `repB 8`. -/
def chgQ_seven_eight : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, -1]

theorem isUnit_det_chgQ_seven_eight : IsUnit chgQ_seven_eight.det := by
  rw [Int.isUnit_iff]; simp [chgQ_seven_eight, Matrix.det_fin_two]

/-- **`Q(7, 2, 1) = Q(8, 2, 3)`: the electron line `3` of `7` is the line `1` of `8`.** -/
theorem kkQ_seven_eight :
    kkQ 7 R p p' t 2 1 μ a b x = kkQ 8 R p p' t 2 3 μ a b x := by
  exact kkQ_chgD (A := 0) (σ := Equiv.refl _) isUnit_det_chgQ_seven_eight
    (by decide +kernel) qChain_seven_eight R p p' t μ a b x

theorem qChain_six_four :
    QChain 6 ((Finset.univ.erase 0).erase 3) 4 ((Finset.univ.erase 0).erase 3) id := by
  intro μ E
  unfold kOpen
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ocW_eq, ocW_eq, kPermD_symm (i := 6) (t := 3) (k := 0) rfl,
    kPermD_symm (i := 6) (t := 4) (k := 1) rfl, kPermD_symm (i := 6) (t := 0) (k := 2) rfl,
    kPermD_symm (i := 6) (t := 2) (k := 3) rfl, kPermD_symm (i := 6) (t := 1) (k := 4) rfl,
    kPermD_symm (i := 4) (t := 3) (k := 0) rfl, kPermD_symm (i := 4) (t := 1) (k := 1) rfl,
    kPermD_symm (i := 4) (t := 4) (k := 2) rfl, kPermD_symm (i := 4) (t := 2) (k := 3) rfl,
    kPermD_symm (i := 4) (t := 0) (k := 4) rfl]
  simp [Matrix.mul_assoc]

/-- The change of loop momenta from `repB 6` to `repB 4`. -/
def chgQ_six_four : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 1]

theorem isUnit_det_chgQ_six_four : IsUnit chgQ_six_four.det := by
  rw [Int.isUnit_iff]; simp [chgQ_six_four, Matrix.det_fin_two]

/-- **`Q(6, 0, 3) = Q(4, 0, 3)`: the term of `6` with both lines deleted; the photon lines
`4`, `6` of `6` are the lines `5`, `7` of `4` and conversely.** -/
theorem kkQ_six_four :
    kkQ 6 R p p' t 0 3 μ a b x = kkQ 4 R p p' t 0 3 μ a b x := by
  exact kkQ_chgD (A := 0) (σ := Equiv.swap 2 3 * Equiv.swap 4 5) isUnit_det_chgQ_six_four
    (by decide +kernel) qChain_six_four R p p' t μ a b x


end Pairs

end QED.ChainProof.SetCRegDisp

end
