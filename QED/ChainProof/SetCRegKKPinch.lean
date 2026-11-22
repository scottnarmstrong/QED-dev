/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKChg

/-!
# Set (c): the pinched terms of the longitudinal integrand, first level

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSum` (`QED/ChainProof/SetCRegKKNorm.lean`).
At an internal Ward vertex `kWardD i = j + 1` the pointwise limit of the longitudinal integrand of
`repB i` is `kCst · sgn · (P(i, j + 1) - P(i, j))` (`QED.ChainProof.SetCMainB.kkLimX_kkH_int`),
where `P(i, d)` is the pinched value: the term with the electron line `d` deleted, the vertex
`1` at the Ward vertex and `q̸` at the other end, with the extra line `9` removed against `k²`.
For three pairs of classes the pinched terms coincide after a change of loop momenta
(the chain of the two classes is the same once the deleted line is gone), and they enter the sum
over the classes with opposite signs:

* `kkPin`, **`kkLimX_kkH_pin`**: the pinched value and the limit at an internal Ward vertex;
* `PinLines`, `PinMom`, `PinChain`, `kNi_pin_chgD`, **`kkPin_chgD`**: two pinched values agree
  when the kept lines match after a unimodular change and the two chains agree once the line
  is deleted;
* **`kkPin_one_eleven`**, **`kkPin_two_eight`**, **`kkPin_three_five`**: `P(1, 1) = P(11, 1)`,
  `P(2, 1) = P(8, 1)`, `P(3, 2) = P(5, 2)`.
-/

@[expose] public section

open Complex MeasureTheory Set
open QED.WickModel (Params)
open QED.Dirac (gamma slash)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.TwoLoop.Enumeration QED.TwoLoop.LimitCovariance

/-! ### The pinched value -/

/-- The line map deleting the electron line `d` and the extra line `9`. -/
def pinι₈ (d : Fin 4) : Fin 8 → Fin 10 := fun c => (eIdx d).succAbove ((8 : Fin 9).succAbove c)

/-- The line map deleting the electron line `d`. -/
def pinι₉ (d : Fin 4) : Fin 9 → Fin 10 := fun c => (eIdx d).succAbove c

/-- **The pinched value** `P(i, d)`: the term with the electron line `d` deleted, the vertex `1`
at the Ward vertex and `q̸` at the other end, with `k²/(k² + Λ²) = 1 - Λ²/(k² + Λ²)`. -/
noncomputable def kkPin (i : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (d : Fin 4)
    (μ a b : Fin 4) (x : ℝ) : ℂ :=
  kkLimX (kkT i R p p' t (pinι₈ d)
      fun ℓ => kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b) x -
    ((R.Λ ^ 2 : ℝ) : ℂ) * kkLimX (kkT i R p p' t (pinι₉ d)
      fun ℓ => kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b) x

/-- **The pointwise limit at an internal Ward vertex** in pinched values. -/
theorem kkLimX_kkH_pin {i : Fin 12} {R : Params} {p p' : Fin 4 → ℝ} {t x : ℝ}
    (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
    (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (ht : R.m ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1) (j : Fin 3) (hj : kWardD i = j.succ.castSucc)
    (μ a b : Fin 4) :
    kkLimX (kkH i R p p' t μ a b) x = kCst R * (((kSgnW i : ℤ) : ℝ) : ℂ) *
      (kkPin i R p p' t j.succ μ a b x - kkPin i R p p' t j.castSucc μ a b x) := by
  rw [kkLimX_kkH_int (w := fun _ => 1) hm hγ hγΛ hp hp' hq ht (integrableOn_const (by simp))
    hx j hj μ a b, kkPin, kkPin]
  rw [show ∀ u v : ℂ, u + -1 * v = u - v from fun u v => by ring]
  rfl

/-! ### Equality of pinched values after a change of loop momenta -/

section Chg

variable (i i' : Fin 12) (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (d : Fin 4) (μ a b : Fin 4)
  (M : Matrix (Fin 2) (Fin 2) ℤ) (A : Fin 2 → Fin 2 → ℤ)

/-- The kept lines of a pinched term match after the change, up to sign. -/
def PinLines : Prop :=
  ∀ c : Fin 9, uVec i M A (pinι₉ d c) = uVec i' 1 0 (pinι₉ d c) ∨
    uVec i M A (pinι₉ d c) = -uVec i' 1 0 (pinι₉ d c)

/-- The element momentum and the kept electron momenta match exactly after the change. -/
def PinMom : Prop :=
  uVec i M A 8 = uVec i' 1 0 8 ∧ ∀ j : Fin 4, j ≠ d → uVec i M A (eIdx j) = uVec i' 1 0 (eIdx j)

instance : Decidable (PinLines i i' d M A) := by unfold PinLines; infer_instance

instance : Decidable (PinMom i i' d M A) := by unfold PinMom; infer_instance

/-- The two chains agree once the electron line `d` is deleted. -/
def PinChain : Prop :=
  ∀ (μ : Fin 4) (Y : Matrix (Fin 4) (Fin 4) ℂ) (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ), E d = 1 →
    kOpen (kPermD i) μ 1 Y E = kOpen (kPermD i') μ 1 Y E

variable {i i' d M A}

theorem kNi_pin_chgD (hm : PinMom i i' d M A) (hc : PinChain i i' d) (ℓ : Fin 2 → Fin 4 → ℝ) :
    kNi i R p p' .one .q (Finset.univ.erase d) μ (chgD M A p (p' - p) ℓ) a b =
      kNi i' R p p' .one .q (Finset.univ.erase d) μ ℓ a b := by
  have hQ : kQ (repBClass i) (repBSlot i) p p' (chgD M A p (p' - p) ℓ) =
      kQ (repBClass i') (repBSlot i') p p' ℓ := by
    rw [kQ_chgD, hm.1, ← kQ_chgD, chgD_one_zero]
  have hK : ∀ j ∈ Finset.univ.erase d, kK (repBClass i) (repBSlot i) p p' j
      (chgD M A p (p' - p) ℓ) = kK (repBClass i') (repBSlot i') p p' j ℓ := fun j hj => by
    rw [kK_chgD, hm.2 j (Finset.ne_of_mem_erase hj), ← kK_chgD, chgD_one_zero]
  have key : kNum (kPermD i) (repBClass i) (repBSlot i) R.m p p' .one .q (Finset.univ.erase d) μ
      (chgD M A p (p' - p) ℓ) = kNum (kPermD i') (repBClass i') (repBSlot i') R.m p p' .one .q
        (Finset.univ.erase d) μ ℓ := by
    rw [kNum_chgD _ _ _ _ _ _ _ _ _ _ _ _ _ _ hQ hK]
    unfold kNum
    simp only [kSlotM]
    exact hc μ _ _ (by simp [kEK])
  exact congrFun (congrFun key a) b

theorem pinLines_eight (h : PinLines i i' d M A) (c : Fin 8) :
    uVec i M A (pinι₈ d c) = uVec i' 1 0 (pinι₈ d c) ∨
      uVec i M A (pinι₈ d c) = -uVec i' 1 0 (pinι₈ d c) :=
  h _

/-- **Two pinched values agree** when the kept lines and momenta match after a unimodular change
and the chains agree once the line is deleted. -/
theorem kkPin_chgD (hM : IsUnit M.det) (hl : PinLines i i' d M A) (hm : PinMom i i' d M A)
    (hc : PinChain i i' d) (x : ℝ) :
    kkPin i R p p' t d μ a b x = kkPin i' R p p' t d μ a b x := by
  have h8 : uVec i M A 8 = uVec i' 1 0 8 ∨ uVec i M A 8 = -uVec i' 1 0 8 := Or.inl hm.1
  have hF : ∀ ℓ, kNi i R p p' .one .q (Finset.univ.erase d) μ (chgD M A p (p' - p) ℓ) a b =
      kNi i' R p p' .one .q (Finset.univ.erase d) μ ℓ a b := kNi_pin_chgD R p p' μ a b hm hc
  unfold kkPin
  rw [kkLimX_chgD M hM A p (p' - p) (fun ε x ℓ => (kkT_chgD i i' R p p' t M A (pinι₈ d)
      (fun ℓ => kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b) _
      (pinLines_eight hl) h8 hF ε x ℓ).symm) x,
    kkLimX_chgD M hM A p (p' - p) (fun ε x ℓ => (kkT_chgD i i' R p p' t M A (pinι₉ d)
      (fun ℓ => kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b) _
      hl h8 hF ε x ℓ).symm) x]

end Chg

/-! ### The three first-level pairs -/

/-- The chains of `repB 1` and `repB 11` with the electron line `1` deleted:
`γ^z A₃ q̸ A₂ γ^μ A₀ γ^z`. -/
theorem pinChain_one_eleven : PinChain 1 11 1 := by
  intro μ Y E hE
  unfold kOpen
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ocW_eq, ocW_eq, kPermD_symm (i := 1) (t := 2) (k := 0) rfl,
    kPermD_symm (i := 1) (t := 1) (k := 1) rfl, kPermD_symm (i := 1) (t := 3) (k := 2) rfl,
    kPermD_symm (i := 1) (t := 4) (k := 3) rfl, kPermD_symm (i := 1) (t := 0) (k := 4) rfl,
    kPermD_symm (i := 11) (t := 1) (k := 0) rfl, kPermD_symm (i := 11) (t := 2) (k := 1) rfl,
    kPermD_symm (i := 11) (t := 3) (k := 2) rfl, kPermD_symm (i := 11) (t := 4) (k := 3) rfl,
    kPermD_symm (i := 11) (t := 0) (k := 4) rfl, hE]
  simp [Matrix.mul_assoc]

/-- The chains of `repB 2` and `repB 8` with the electron line `1` deleted:
`q̸ A₃ γ^z A₂ γ^μ A₀ γ^z`. -/
theorem pinChain_two_eight : PinChain 2 8 1 := by
  intro μ Y E hE
  unfold kOpen
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ocW_eq, ocW_eq, kPermD_symm (i := 2) (t := 2) (k := 0) rfl,
    kPermD_symm (i := 2) (t := 1) (k := 1) rfl, kPermD_symm (i := 2) (t := 4) (k := 2) rfl,
    kPermD_symm (i := 2) (t := 3) (k := 3) rfl, kPermD_symm (i := 2) (t := 0) (k := 4) rfl,
    kPermD_symm (i := 8) (t := 1) (k := 0) rfl, kPermD_symm (i := 8) (t := 2) (k := 1) rfl,
    kPermD_symm (i := 8) (t := 4) (k := 2) rfl, kPermD_symm (i := 8) (t := 3) (k := 3) rfl,
    kPermD_symm (i := 8) (t := 0) (k := 4) rfl, hE]
  simp [Matrix.mul_assoc]

/-- The chains of `repB 3` and `repB 5` with the electron line `2` deleted:
`γ^z A₃ γ^μ A₁ γ^z A₀ q̸`. -/
theorem pinChain_three_five : PinChain 3 5 2 := by
  intro μ Y E hE
  unfold kOpen
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ocW_eq, ocW_eq, kPermD_symm (i := 3) (t := 2) (k := 0) rfl,
    kPermD_symm (i := 3) (t := 3) (k := 1) rfl, kPermD_symm (i := 3) (t := 0) (k := 2) rfl,
    kPermD_symm (i := 3) (t := 4) (k := 3) rfl, kPermD_symm (i := 3) (t := 1) (k := 4) rfl,
    kPermD_symm (i := 5) (t := 3) (k := 0) rfl, kPermD_symm (i := 5) (t := 2) (k := 1) rfl,
    kPermD_symm (i := 5) (t := 0) (k := 2) rfl, kPermD_symm (i := 5) (t := 4) (k := 3) rfl,
    kPermD_symm (i := 5) (t := 1) (k := 4) rfl, hE]
  simp [Matrix.mul_assoc]

/-- The change of loop momenta from `repB 11` to `repB 1`. -/
def chgOneEleven : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 1]

/-- The change of loop momenta from `repB 8` to `repB 2`. -/
def chgTwoEight : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

theorem isUnit_det_chgOneEleven : IsUnit chgOneEleven.det := by
  rw [Int.isUnit_iff]; simp [chgOneEleven, Matrix.det_fin_two]

theorem isUnit_det_chgTwoEight : IsUnit chgTwoEight.det := by
  rw [Int.isUnit_iff]; simp [chgTwoEight, Matrix.det_fin_two]

section Pairs

variable (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (μ a b : Fin 4) (x : ℝ)

/-- **`P(1, 1) = P(11, 1)`**: the electron line `1` deleted from `repB 1` (fused upwards at the
Ward vertex `1`) and from `repB 11` (fused downwards at the Ward vertex `2`). -/
theorem kkPin_one_eleven : kkPin 1 R p p' t 1 μ a b x = kkPin 11 R p p' t 1 μ a b x :=
  kkPin_chgD R p p' t μ a b (A := 0) isUnit_det_chgOneEleven (by decide +kernel) (by decide +kernel)
    pinChain_one_eleven x

/-- **`P(2, 1) = P(8, 1)`**: the electron line `1` deleted from `repB 2` and from `repB 8`. -/
theorem kkPin_two_eight : kkPin 2 R p p' t 1 μ a b x = kkPin 8 R p p' t 1 μ a b x :=
  kkPin_chgD R p p' t μ a b (A := 0) isUnit_det_chgTwoEight (by decide +kernel) (by decide +kernel)
    pinChain_two_eight x

/-- **`P(3, 2) = P(5, 2)`**: the electron line `2` deleted from `repB 3` and from `repB 5`
(the same loop routing). -/
theorem kkPin_three_five : kkPin 3 R p p' t 2 μ a b x = kkPin 5 R p p' t 2 μ a b x :=
  kkPin_chgD R p p' t μ a b (M := 1) (A := 0) (by simp) (by decide +kernel) (by decide +kernel)
    pinChain_three_five x

end Pairs

end QED.ChainProof.SetCRegDisp

end
