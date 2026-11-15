/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Frozen.OneLoop.VertexOneLoop
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import QED.Numerics.PauliEnclosures
import Mathlib.Tactic.Positivity

/-!
# Provider for `QED.OneLoop.isFormFactorPair_vertexOneLoop_pauli_enclosure_ten`

Proves the frozen theorem goal `QED.OneLoop.isFormFactorPair_vertexOneLoop_pauli_enclosure_ten`
(packet Q, decision D-35) as
`QED.Provider.OneLoop.isFormFactorPair_vertexOneLoop_pauli_enclosure_ten`, with the binder
convention of decision D-13. By `QED.Numerics.Pauli.isFormFactorPair_vertexOneLoop_pauli_mem`
(existence and uniqueness of the form-factor pair, and `F₂ = (e²/8π²) ∫ pauliIntegrand`), it
suffices to enclose the integral, which is the kernel-checked certificate
`QED.Numerics.Pauli.integral_pauliIntegrand_ten`. It must never import the frozen anchor.
-/

@[expose] public section

namespace QED.Provider.OneLoop

open QED.OneLoop in
/-- Packet Q's (Q₁), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem isFormFactorPair_vertexOneLoop_pauli_enclosure_ten {e m : ℝ}
    (he : e ≠ 0 := by assumption) (hm : 0 < m := by assumption) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2 := by assumption)
    (hp : Minkowski.dot p p = -m ^ 2 := by assumption) (hp0' : 0 < p' 0 := by assumption)
    (hp0 : 0 < p 0 := by assumption)
    (hq : Minkowski.dot (p' - p) (p' - p) = m ^ 2 / 10000 := by assumption) :
    (∃ F : ℂ × ℂ, IsFormFactorPair e m p' p
      (vertexOneLoop e m (m / 10) (10 * m) hm (div_pos hm Nat.ofNat_pos)
        (mul_pos Nat.ofNat_pos hm) p' p hp' hp hp0' hp0) F) ∧
    ∀ F : ℂ × ℂ, IsFormFactorPair e m p' p
        (vertexOneLoop e m (m / 10) (10 * m) hm (div_pos hm Nat.ofNat_pos)
          (mul_pos Nat.ofNat_pos hm) p' p hp' hp hp0' hp0) F →
      ∃ t ∈ Set.Icc (0.7668 : ℝ) 0.7673, F.2 = ((e ^ 2 / (8 * Real.pi ^ 2) * t : ℝ) : ℂ) := by
  have hq0 : 0 < Minkowski.dot (p' - p) (p' - p) := by rw [hq]; positivity
  refine QED.Numerics.Pauli.isFormFactorPair_vertexOneLoop_pauli_mem he hm _ _ hp' hp hp0' hp0
    hq0 ?_
  rw [hq]
  exact QED.Numerics.Pauli.integral_pauliIntegrand_ten hm.ne'

end QED.Provider.OneLoop

end
