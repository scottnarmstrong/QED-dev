/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.OneParticleMomentum
public import QED.Algebra.Minkowski
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One-electron momenta

The on-shell condition `p·p = -m²` and the positive energy of the frozen one-electron
four-momentum `QED.OneLoop.oneParticleMomentum` (packet 4b, decision D-18). The frozen current
density `QED.OneLoop.packetCurrentDensity` passes these proofs to the vertex function.
-/

@[expose] public section

namespace QED.OneLoop

theorem dot_oneParticleMomentum (m : ℝ) (k : Fin 3 → ℝ) :
    Minkowski.dot (oneParticleMomentum m k) (oneParticleMomentum m k) = -m ^ 2 := by
  have h : 0 ≤ m ^ 2 + ∑ j, k j ^ 2 := by positivity
  rw [Minkowski.dot_eq]
  simp only [oneParticleMomentum, Fin.cons_zero]
  have h1 : (Fin.cons (Real.sqrt (m ^ 2 + ∑ j, k j ^ 2)) k : Fin 4 → ℝ) 1 = k 0 := rfl
  have h2 : (Fin.cons (Real.sqrt (m ^ 2 + ∑ j, k j ^ 2)) k : Fin 4 → ℝ) 2 = k 1 := rfl
  have h3 : (Fin.cons (Real.sqrt (m ^ 2 + ∑ j, k j ^ 2)) k : Fin 4 → ℝ) 3 = k 2 := rfl
  rw [h1, h2, h3, ← sq, ← sq, ← sq, ← sq, Real.sq_sqrt h, Fin.sum_univ_three]
  ring

theorem oneParticleMomentum_pos {m : ℝ} (hm : 0 < m) (k : Fin 3 → ℝ) :
    0 < oneParticleMomentum m k 0 := by
  simp only [oneParticleMomentum, Fin.cons_zero]
  exact Real.sqrt_pos.2 (by positivity)

end QED.OneLoop

end
