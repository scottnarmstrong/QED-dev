/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.IBPCertPilotData
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Pilot IBP reduction certificates checked by the kernel (layer L2, pilot PE2)

The generated certificates of `QED.Algebra.IBPCertPilotData` are checked here by
`decide +kernel`, together with the well-formedness of their families.

## Main statements

* `QED.Algebra.IBPCert.Pilot.check_oneLoop₁₁`, `check_oneLoop₃₂`, `check_twoLoop`: the kernel
  checks.
* `QED.Algebra.IBPCert.Pilot.oneLoop_reduction₁₁`: on shell, `I(1, 1) = (d - 2) / (2(d - 3)) ·
  I(0, 1)` for every `d ≠ 3` and every `I` satisfying the IBP relations and the zero sector of
  the one-loop family.
* `QED.Algebra.IBPCert.Pilot.twoLoop_reduction`: the two-loop target reduces to the five masters
  for `d` off a finite set.
-/

@[expose] public section

namespace QED.Algebra.IBPCert.Pilot

theorem wellFormed_oneLoopSE : oneLoopSE.wellFormed = true := by decide +kernel

theorem wellFormed_twoLoopSE : twoLoopSE.wellFormed = true := by decide +kernel

theorem check_oneLoop₁₁ : oneLoopCert₁₁.check oneLoopSE = true := by decide +kernel

theorem check_oneLoop₃₂ : oneLoopCert₃₂.check oneLoopSE = true := by decide +kernel

theorem check_twoLoop : twoLoopCert.check twoLoopSE = true := by decide +kernel

/-! ### Rejected certificates -/

/-- A wrong denominator is rejected. -/
example : ({ oneLoopCert₁₁ with den := [-12, 5] }).check oneLoopSE = false := by decide +kernel

/-- A certificate with a seed dropped is rejected. -/
example : ({ twoLoopCert with seeds := twoLoopCert.seeds.tail }).check twoLoopSE = false := by
  decide +kernel

/-- A zero denominator is rejected. -/
example : ({ oneLoopCert₁₁ with den := [0, 0], masters := [] }).check oneLoopSE = false := by
  decide +kernel

/-! ### The reductions -/

/-- On shell, `I(1, 1) = (d - 2) / (2(d - 3)) · I(0, 1)` for `d ≠ 3`, for every family of values
satisfying the IBP relations and the zero sector of `oneLoopSE`. -/
theorem oneLoop_reduction₁₁ {K : Type*} [Field K] [CharZero K]
    (I : (Fin oneLoopSE.nProp → ℤ) → K → K) (d : K) (hI : oneLoopSE.IBPHolds I d)
    (hz : oneLoopSE.ZeroSectors I d) (hd : d ≠ 3) :
    I ![1, 1] d = (d - 2) / (2 * (d - 3)) * I ![0, 1] d := by
  have hd' : d - 3 ≠ 0 := sub_ne_zero.2 hd
  have hq : Poly.eval d oneLoopCert₁₁.den = 4 * (d - 3) := by
    simp only [oneLoopCert₁₁, Poly.eval_cons, Poly.eval_nil]; push_cast; ring
  have hden : Poly.eval d oneLoopCert₁₁.den ≠ 0 := by
    rw [hq]; exact mul_ne_zero (by norm_num) hd'
  have h := Cert.sound check_oneLoop₁₁ I d hI hz hden
  have h1 : toVec oneLoopSE.nProp oneLoopCert₁₁.target = ![1, 1] := by
    funext i; fin_cases i <;> rfl
  have h2 : toVec oneLoopSE.nProp [0, 1] = ![0, 1] := by
    funext i; fin_cases i <;> rfl
  rw [h1, hq] at h
  simp only [oneLoopCert₁₁, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2,
    Poly.eval_cons, Poly.eval_nil] at h
  rw [h]
  push_cast
  field_simp
  ring

/-- The two-loop target `I(1, 1, 1, 1, 1)` is the certified combination of the five masters for
`d` off a finite set, for every family of values satisfying the IBP relations and the zero
sectors of `twoLoopSE` there. -/
theorem twoLoop_reduction {K : Type*} [Field K] [CharZero K] :
    ∃ s : Finset K, ∀ d ∉ s, Poly.eval d twoLoopCert.den ≠ 0 ∧
      ∀ I : (Fin twoLoopSE.nProp → ℤ) → K → K, twoLoopSE.IBPHolds I d →
        twoLoopSE.ZeroSectors I d →
        I (toVec twoLoopSE.nProp twoLoopCert.target) d =
          (twoLoopCert.masters.map fun m =>
            Poly.eval d m.2 / Poly.eval d twoLoopCert.den *
              I (toVec twoLoopSE.nProp m.1) d).sum :=
  Cert.exists_finset_sound check_twoLoop

end QED.Algebra.IBPCert.Pilot
