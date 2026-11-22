/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegKKOdd

/-!
# Set (c): the first Ward step summed over the twelve main classes

Helper level for `QED.ChainProof.SetCRegDisp.IsKKSum` (`QED/ChainProof/SetCRegKKNorm.lean`).
The nine classes with an internal Ward vertex give, through
`QED.ChainProof.SetCRegDisp.kkLimX_kkH_pin`, eighteen pinched values. Three pairs cancel
(`kkPin_one_eleven`, `kkPin_two_eight`, `kkPin_three_five`) and two vanish
(`kkPin_eleven_two`, `kkPin_seven_one`); ten survive. The three classes `0`, `6`, `10` with the
Ward identities at both ends are kept as they are.

* `sum_fin_twelve`: the sum over the twelve classes written out;
* **`kkLimX_sum_first`**: `∑ᵢ K_i = K₀ + K₆ + K₁₀ + kCst · S`, `S` the ten surviving pinched values
  `P(1,0) + P(2,0) + P(3,3) - P(4,1) + P(4,0) - P(5,1) + P(7,2) - P(8,2) + P(9,3) - P(9,2)`.
-/

@[expose] public section

open Complex Set
open QED.WickModel (Params)

namespace QED.ChainProof.SetCRegDisp

open QED.ChainProof.SetCMainB QED.ChainProof.SetCMain

theorem sum_fin_twelve (f : Fin 12 → ℂ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring_nf
  rfl

/-- The ten pinched values surviving the first Ward step. -/
noncomputable def kkSurv (R : Params) (p p' : Fin 4 → ℝ) (t : ℝ) (μ a b : Fin 4) (x : ℝ) : ℂ :=
  kkPin 1 R p p' t 0 μ a b x + kkPin 2 R p p' t 0 μ a b x + kkPin 3 R p p' t 3 μ a b x -
    kkPin 4 R p p' t 1 μ a b x + kkPin 4 R p p' t 0 μ a b x - kkPin 5 R p p' t 1 μ a b x +
    kkPin 7 R p p' t 2 μ a b x - kkPin 8 R p p' t 2 μ a b x + kkPin 9 R p p' t 3 μ a b x -
    kkPin 9 R p p' t 2 μ a b x

/-- **The first Ward step summed over the twelve main classes**: the pinched values of the nine
classes with an internal Ward vertex reduce to the ten survivors `kkSurv`. -/
theorem kkLimX_sum_first {R : Params} {p p' : Fin 4 → ℝ} {t x : ℝ}
    (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) (hp : Minkowski.dot p p = -R.m ^ 2)
    (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (ht : R.m ≤ t) (hx : x ∈ Ioo (0 : ℝ) 1) (μ a b : Fin 4) :
    ∑ i, kkLimX (kkH i R p p' t μ a b) x =
      kkLimX (kkH 0 R p p' t μ a b) x + kkLimX (kkH 6 R p p' t μ a b) x +
        kkLimX (kkH 10 R p p' t μ a b) x + kCst R * kkSurv R p p' t μ a b x := by
  have e := fun (i : Fin 12) (j : Fin 3) (hj : kWardD i = j.succ.castSucc) =>
    kkLimX_kkH_pin hm hγ hγΛ hp hp' hq ht hx (i := i) j hj μ a b
  rw [sum_fin_twelve, e 1 0 rfl, e 2 0 rfl, e 3 2 rfl, e 4 0 rfl, e 5 1 rfl, e 7 1 rfl,
    e 8 1 rfl, e 9 2 rfl, e 11 1 rfl]
  have h₁ := kkPin_one_eleven R p p' t μ a b x
  have h₂ := kkPin_two_eight R p p' t μ a b x
  have h₃ := kkPin_three_five R p p' t μ a b x
  have h₄ := kkPin_eleven_two R p p' t μ a b x
  have h₅ := kkPin_seven_one R p p' t μ a b x
  simp only [kSgnW, kkSurv]
  change _ + kCst R * ((-1 : ℤ) : ℝ) * (kkPin 1 R p p' t 1 μ a b x - kkPin 1 R p p' t 0 μ a b x)
    + kCst R * ((-1 : ℤ) : ℝ) * (kkPin 2 R p p' t 1 μ a b x - kkPin 2 R p p' t 0 μ a b x)
    + kCst R * ((1 : ℤ) : ℝ) * (kkPin 3 R p p' t 3 μ a b x - kkPin 3 R p p' t 2 μ a b x)
    + kCst R * ((-1 : ℤ) : ℝ) * (kkPin 4 R p p' t 1 μ a b x - kkPin 4 R p p' t 0 μ a b x)
    + kCst R * ((1 : ℤ) : ℝ) * (kkPin 5 R p p' t 2 μ a b x - kkPin 5 R p p' t 1 μ a b x)
    + _ + kCst R * ((1 : ℤ) : ℝ) * (kkPin 7 R p p' t 2 μ a b x - kkPin 7 R p p' t 1 μ a b x)
    + kCst R * ((-1 : ℤ) : ℝ) * (kkPin 8 R p p' t 2 μ a b x - kkPin 8 R p p' t 1 μ a b x)
    + kCst R * ((1 : ℤ) : ℝ) * (kkPin 9 R p p' t 3 μ a b x - kkPin 9 R p p' t 2 μ a b x)
    + _ + kCst R * ((-1 : ℤ) : ℝ) * (kkPin 11 R p p' t 2 μ a b x -
      kkPin 11 R p p' t 1 μ a b x) = _
  rw [h₁, h₂, h₃, h₄, h₅]
  push_cast
  ring

end QED.ChainProof.SetCRegDisp

end
