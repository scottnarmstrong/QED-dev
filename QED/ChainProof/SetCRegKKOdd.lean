/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKPinch

/-!
# Set (c): the pinched terms odd in the element momentum

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSum` (`QED/ChainProof/SetCRegKKNorm.lean`).
Two pinched values `QED.ChainProof.SetCRegDisp.kkPin` vanish: in `P(11, 2)` and `P(7, 1)` the
deleted electron line is the only one carrying the element momentum `k` between the Ward vertex
and the other end, so after the deletion no electron line carries `k`. The integrand is then odd
under the unimodular change `k ↦ -k` (the electron momenta fixed, the factor `q̸` changing sign,
the denominators and the spectral factor even), and its joint energy-first integral vanishes.

* `ocW_neg_two`, `kNum_q_neg`: the numerator changes sign with `q̸`;
* **`kkLimX_eq_zero_of_odd`**: a family odd under a unimodular change has zero pointwise limit;
* **`kkPin_eq_zero_of_odd`**: the criterion for a pinched value;
* **`kkPin_eleven_two`**, **`kkPin_seven_one`**: `P(11, 2) = 0`, `P(7, 1) = 0`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Dirac (gamma slash)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain QED.ChainProof.SetCUnitM
open QED.TwoLoop.Enumeration

/-! ### The numerator changes sign with `q̸` -/

theorem ocW_neg_two (π : Equiv.Perm (Fin 5)) (X₀ X₁ Y X₃ X₄ : Matrix (Fin 4) (Fin 4) ℂ)
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ocW π ![X₀, X₁, -Y, X₃, X₄] E = -ocW π ![X₀, X₁, Y, X₃, X₄] E := by
  rw [ocW_slot π 2 ![X₀, X₁, -Y, X₃, X₄] (fun _ => ![X₀, X₁, Y, X₃, X₄]) E
    (fun x => if x = 0 then -1 else 0) (fun x j hj => by fin_cases j <;> simp_all)
    (by simp)]
  simp

theorem slash_neg' (k : Fin 4 → ℝ) : slash (-k) = -slash k := by
  rw [← neg_one_smul ℝ k, QED.Dirac.slash_smul]
  simp

/-- **The numerator with `q̸` at the other end changes sign with the element momentum.** -/
theorem kNum_q_neg (π : Equiv.Perm (Fin 5)) (c : Class5) (σ : Fin 8) (m : ℝ) (p p' : Fin 4 → ℝ)
    (K : Finset (Fin 4)) (μ : Fin 4) (L L' : Fin 2 → Fin 4 → ℝ)
    (hQ : kQ c σ p p' L = -kQ c σ p p' L') (hK : ∀ j ∈ K, kK c σ p p' j L = kK c σ p p' j L') :
    kNum π c σ m p p' .one .q K μ L = -kNum π c σ m p p' .one .q K μ L' := by
  have hE : (fun j => kEK c σ m p p' K j L) = fun j => kEK c σ m p p' K j L' := by
    funext j
    unfold kEK
    split_ifs with hj
    · rw [hK j hj]
    · rfl
  unfold kNum kOpen
  simp only [kSlotM, hQ, slash_neg', hE, ocW_neg_two, smul_neg, Finset.sum_neg_distrib]

/-! ### Odd families -/

/-- **A family odd under a unimodular change of loop momenta has zero pointwise limit.** -/
theorem kkLimX_eq_zero_of_odd {H : ℝ → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ}
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : IsUnit M.det) (a : Fin 2 → Fin 2 → ℤ) (p q : Fin 4 → ℝ)
    (h : ∀ ε x ℓ, H ε x (chgD M a p q ℓ) = -H ε x ℓ) (x : ℝ) : kkLimX H x = 0 := by
  have h0 : ∀ ε, QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε x) = 0 := fun ε => by
    have e := QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_eq_of_comp (H := fun ℓ =>
      (-1 : ℂ) * H ε x ℓ) (G := H ε x) M hM _ fun ℓ => by
        rw [show H ε x ((fun s => ∑ r, M s r • ℓ r) + _) = H ε x (chgD M a p q ℓ) from rfl, h]
        ring
    rw [QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul] at e
    linear_combination -e / 2
  unfold kkLimX
  simp only [h0]
  exact tendsto_const_nhds.limUnder_eq

/-- **A pinched value vanishes** when a unimodular change fixes the kept electron momenta,
reverses the element momentum and keeps the other lines up to sign. -/
theorem kkPin_eq_zero_of_odd {i : Fin 12} {d : Fin 4} {M : Matrix (Fin 2) (Fin 2) ℤ}
    {A : Fin 2 → Fin 2 → ℤ} (hM : IsUnit M.det) (hl : PinLines i i d M A)
    (h8 : uVec i M A 8 = -uVec i 1 0 8)
    (hK : ∀ j : Fin 4, j ≠ d → uVec i M A (eIdx j) = uVec i 1 0 (eIdx j))
    (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (μ a b : Fin 4) (x : ℝ) :
    kkPin i R p p' t d μ a b x = 0 := by
  have hF : ∀ ℓ, kNi i R p p' .one .q (Finset.univ.erase d) μ (chgD M A p (p' - p) ℓ) a b =
      -kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b := fun ℓ => by
    have key := kNum_q_neg (kPermD i) (repBClass i) (repBSlot i) R.m p p'
      (Finset.univ.erase d) μ (chgD M A p (p' - p) ℓ) ℓ
      (by rw [kQ_chgD, h8, map_neg, ← kQ_chgD, chgD_one_zero])
      (fun j hj => by rw [kK_chgD, hK j (Finset.ne_of_mem_erase hj), ← kK_chgD, chgD_one_zero])
    exact congrFun (congrFun key a) b
  have hodd : ∀ {k : ℕ} (ι : Fin (k + 1) → Fin 10), (∀ c, uVec i M A (ι c) = uVec i 1 0 (ι c) ∨
      uVec i M A (ι c) = -uVec i 1 0 (ι c)) → ∀ ε x ℓ,
      kkT i R p p' t ι (fun ℓ => kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b) ε x
        (chgD M A p (p' - p) ℓ) =
      -kkT i R p p' t ι (fun ℓ => kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b) ε x ℓ :=
    fun ι hι ε x ℓ => by
      rw [kkT_chgD i i R p p' t M A ι _
        (fun ℓ => -kNi i R p p' .one .q (Finset.univ.erase d) μ ℓ a b) hι (Or.inr h8) hF]
      simp only [kkT]
      ring
  unfold kkPin
  rw [kkLimX_eq_zero_of_odd M hM A p (p' - p) (hodd (pinι₈ d) fun c => hl _) x,
    kkLimX_eq_zero_of_odd M hM A p (p' - p) (hodd (pinι₉ d) hl) x]
  simp

/-! ### The two odd pinched values -/

/-- The change `k ↦ -k` for `repB 11` with the electron line `2` deleted. -/
def chgOddEleven : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 0, -1]

/-- The change `k ↦ -k` for `repB 7` with the electron line `1` deleted. -/
def chgOddSeven : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

theorem isUnit_det_chgOddEleven : IsUnit chgOddEleven.det := by
  rw [Int.isUnit_iff]; simp [chgOddEleven, Matrix.det_fin_two]

theorem isUnit_det_chgOddSeven : IsUnit chgOddSeven.det := by
  rw [Int.isUnit_iff]; simp [chgOddSeven, Matrix.det_fin_two]

/-- **`P(11, 2) = 0`**: odd in the element momentum. -/
theorem kkPin_eleven_two (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (μ a b : Fin 4) (x : ℝ) :
    kkPin 11 R p p' t 2 μ a b x = 0 :=
  kkPin_eq_zero_of_odd (A := 0) isUnit_det_chgOddEleven (by decide +kernel) (by decide +kernel)
    (by decide +kernel) R p p' t μ a b x

/-- **`P(7, 1) = 0`**: odd in the element momentum. -/
theorem kkPin_seven_one (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (μ a b : Fin 4) (x : ℝ) :
    kkPin 7 R p p' t 1 μ a b x = 0 :=
  kkPin_eq_zero_of_odd (A := 0) isUnit_det_chgOddSeven (by decide +kernel) (by decide +kernel)
    (by decide +kernel) R p p' t μ a b x

end QED.ChainProof.SetCRegDisp

end
