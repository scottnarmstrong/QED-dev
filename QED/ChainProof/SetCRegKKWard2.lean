/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKPinch

/-!
# Set (c): the second Ward step on the pinched numerators

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSum` (`QED/ChainProof/SetCRegKKNorm.lean`).
A pinched value `QED.ChainProof.SetCRegDisp.kkPin` carries the vertex `1` at the Ward vertex and
`q̸` at the other end `kOthD i` of the element line. The Ward identity at that end splits its
numerator once more: at an internal end into two terms with one more electron line deleted, at
the outgoing (incoming) end into a term with `2m - A(p')` (`A(p) - 2m`), which has zero Pauli
weight (`QED/ChainProof/SetCRegKKShell.lean`), and a term with the line `3` (`0`) deleted. This
is the numerator algebra of the second step; the deleted lines are removed from the values by
the scalar reductions of `QED/ChainProof/SetCMainBKKTerm.lean`.

* `kOpen_swap`: the two fixed vertices exchanged with their labels;
* **`kNum_ward_Y_int`**, **`kNum_ward_Y_out`**, **`kNum_ward_Y_in`**: the Ward identity at the
  vertex `π 2` of a numerator term with `1` at `π 1`;
* `kQ_oth_int`, `kQ_oth_out`: the element momentum at the other end of the element line;
* **`kNi_pin_ward_int`**, **`kNi_pin_ward_out`**, **`kNi_pin_ward_in`**: the second step on the
  numerator of a pinched value of `repB i`.
-/

@[expose] public section

open Complex
open QED.WickModel (Params)
open QED.Dirac (gamma slash)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.TwoLoop.Enumeration QED.TwoLoop.LimitCovariance
open QED.TwoLoop.Bridge (electronNumerator)

/-! ### Exchanging the fixed vertices -/

/-- **The fixed vertices exchanged with their labels.** -/
theorem kOpen_swap (π : Equiv.Perm (Fin 5)) (μ : Fin 4) (X Y : Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    kOpen (π * Equiv.swap 1 2) μ Y X E = kOpen π μ X Y E := by
  unfold kOpen ocW
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 2
  funext t
  rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  generalize π.symm t = k
  fin_cases k <;> rfl

/-! ### The Ward identity at the second fixed vertex -/

section Ward

variable (π : Equiv.Perm (Fin 5)) (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ)
  (K : Finset (Fin 4)) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) (s : ℝ)

/-- The scalar `k² + m²` of the electron line `j`. -/
noncomputable abbrev kSc (j : Fin 4) : ℂ :=
  ((Minkowski.dot (kK c σ p p' j ℓ) (kK c σ p p' j ℓ) + m ^ 2 : ℝ) : ℂ)

/-- **Ward at an internal second vertex** `π 2 = j + 1`. -/
theorem kNum_ward_Y_int (j : Fin 3) (hπ : π 2 = j.succ.castSucc)
    (hq : kQ c σ p p' ℓ = s • (kK c σ p p' j.succ ℓ - kK c σ p p' j.castSucc ℓ))
    (h1 : j.succ ∈ K) (h2 : j.castSucc ∈ K) :
    kNum π c σ m p p' .one .q K μ ℓ = (s : ℂ) •
      (kSc c σ m p p' ℓ j.succ • kNum π c σ m p p' .one .one (K.erase j.succ) μ ℓ -
        kSc c σ m p p' ℓ j.castSucc • kNum π c σ m p p' .one .one (K.erase j.castSucc) μ ℓ) := by
  unfold kNum
  simp only [kSlotM]
  rw [← kOpen_swap, kOpen_ward_int (π * Equiv.swap 1 2) μ m s j (by simp [hπ]) 1 _ _ _ _ hq
    (by simp [kEK, h1]) (by simp [kEK, h2]), kOpen_swap, kOpen_swap, kEK_update, kEK_update]

/-- **Ward at the outgoing second vertex** `π 2 = 4`. -/
theorem kNum_ward_Y_out (hπ : π 2 = 4) (hq : kQ c σ p p' ℓ = s • (p' - kK c σ p p' 3 ℓ))
    (h3 : 3 ∈ K) :
    kNum π c σ m p p' .one .q K μ ℓ = (s : ℂ) •
      (kNum π c σ m p p' .one .out K μ ℓ -
        kSc c σ m p p' ℓ 3 • kNum π c σ m p p' .one .one (K.erase 3) μ ℓ) := by
  unfold kNum
  simp only [kSlotM]
  rw [← kOpen_swap, kOpen_ward_out (π * Equiv.swap 1 2) μ m s (by simp [hπ]) 1 _ p' _ _ hq
    (by simp [kEK, h3]), kOpen_swap, kOpen_swap, kEK_update]

/-- **Ward at the incoming second vertex** `π 2 = 0`. -/
theorem kNum_ward_Y_in (hπ : π 2 = 0) (hq : kQ c σ p p' ℓ = s • (kK c σ p p' 0 ℓ - p))
    (h0 : 0 ∈ K) :
    kNum π c σ m p p' .one .q K μ ℓ = (s : ℂ) •
      (kNum π c σ m p p' .one .inn K μ ℓ +
        kSc c σ m p p' ℓ 0 • kNum π c σ m p p' .one .one (K.erase 0) μ ℓ) := by
  unfold kNum
  simp only [kSlotM]
  rw [kOpen_ward_in π μ m s hπ 1 _ p _ _ hq (by simp [kEK, h0]), kEK_update]

end Ward

/-! ### The second step on the pinched numerators of `repB i` -/

section Pin

variable (i : Fin 12) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)

theorem kQ_oth_int (j : Fin 3) (hj : kOthD i = j.succ.castSucc) :
    kQ (repBClass i) (repBSlot i) p p' ℓ = ((kSgnO i : ℤ) : ℝ) •
      (kK (repBClass i) (repBSlot i) p p' j.succ ℓ -
        kK (repBClass i) (repBSlot i) p p' j.castSucc ℓ) := by
  rw [← elemMom_eq_kQ, (elemMom_eq_kMom i p p' ℓ).2, hj,
    show (j.succ.castSucc : Fin 5).succ = j.succ.succ.castSucc from rfl, kMom_electron,
    show (j.succ.castSucc : Fin 5).castSucc = j.castSucc.succ.castSucc from rfl, kMom_electron,
    lineMomentum_class_eq_kK (repBClass i) (repBSlot i),
    lineMomentum_class_eq_kK (repBClass i) (repBSlot i)]

theorem kQ_oth_out (hO : kOthD i = 4) :
    kQ (repBClass i) (repBSlot i) p p' ℓ = ((kSgnO i : ℤ) : ℝ) •
      (p' - kK (repBClass i) (repBSlot i) p p' 3 ℓ) := by
  rw [← elemMom_eq_kQ, (elemMom_eq_kMom i p p' ℓ).2, hO,
    show (4 : Fin 5).succ = 5 from rfl, kMom_five,
    show (4 : Fin 5).castSucc = (3 : Fin 4).succ.castSucc from rfl, kMom_electron,
    lineMomentum_class_eq_kK (repBClass i) (repBSlot i)]

variable (R : Params) (d : Fin 4) (μ : Fin 4)

/-- **The second step at an internal other end** `kOthD i = j + 1`, the deleted line `d` not
next to it. -/
theorem kNi_pin_ward_int (j : Fin 3) (hj : kOthD i = j.succ.castSucc) (h1 : j.succ ≠ d)
    (h2 : j.castSucc ≠ d) :
    kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ = ((kSgnO i : ℤ) : ℂ) •
      (kSc (repBClass i) (repBSlot i) R.m p p' ℓ j.succ •
          kNi i R p p' .one .one ((Finset.univ.erase d).erase j.succ) μ ℓ -
        kSc (repBClass i) (repBSlot i) R.m p p' ℓ j.castSucc •
          kNi i R p p' .one .one ((Finset.univ.erase d).erase j.castSucc) μ ℓ) := by
  have h := kNum_ward_Y_int (kPermD i) (repBClass i) (repBSlot i) R.m p p' (Finset.univ.erase d) μ ℓ
    _ j (by rw [(kPermD_apply i).2.2.1, hj])
    (kQ_oth_int i p p' ℓ j hj) (by simp [h1]) (by simp [h2])
  rw [show (((kSgnO i : ℤ) : ℝ) : ℂ) = ((kSgnO i : ℤ) : ℂ) by push_cast; rfl] at h
  exact h

/-- **The second step at the outgoing other end** `kOthD i = 4`, the line `3` kept. -/
theorem kNi_pin_ward_out (hO : kOthD i = 4) (h3 : (3 : Fin 4) ≠ d) :
    kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ = ((kSgnO i : ℤ) : ℂ) •
      (kNi i R p p' .one .out (Finset.univ.erase d) μ ℓ -
        kSc (repBClass i) (repBSlot i) R.m p p' ℓ 3 •
          kNi i R p p' .one .one ((Finset.univ.erase d).erase 3) μ ℓ) := by
  have h := kNum_ward_Y_out (kPermD i) (repBClass i) (repBSlot i) R.m p p' (Finset.univ.erase d) μ ℓ
    _ (by rw [(kPermD_apply i).2.2.1, hO])
    (kQ_oth_out i p p' ℓ hO) (by simp [h3])
  rw [show (((kSgnO i : ℤ) : ℝ) : ℂ) = ((kSgnO i : ℤ) : ℂ) by push_cast; rfl] at h
  exact h

/-- **The second step at the incoming other end** `kOthD i = 0`, the line `0` kept. -/
theorem kNi_pin_ward_in (hO : kOthD i = 0) (h0 : (0 : Fin 4) ≠ d) :
    kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ = ((kSgnO i : ℤ) : ℂ) •
      (kNi i R p p' .one .inn (Finset.univ.erase d) μ ℓ +
        kSc (repBClass i) (repBSlot i) R.m p p' ℓ 0 •
          kNi i R p p' .one .one ((Finset.univ.erase d).erase 0) μ ℓ) := by
  have h := kNum_ward_Y_in (kPermD i) (repBClass i) (repBSlot i) R.m p p' (Finset.univ.erase d) μ ℓ
    _ (by rw [(kPermD_apply i).2.2.1, hO])
    (kQ_in i p p' hO ℓ) (by simp [h0])
  rw [show (((kSgnO i : ℤ) : ℝ) : ℂ) = ((kSgnO i : ℤ) : ℂ) by push_cast; rfl] at h
  exact h

end Pin

end QED.ChainProof.SetCRegDisp

end
