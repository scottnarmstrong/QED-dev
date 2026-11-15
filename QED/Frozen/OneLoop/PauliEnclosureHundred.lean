-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.IsFormFactorPair
public import QED.Frozen.OneLoop.VertexOneLoop
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import QED.Provider.OneLoop.PauliEnclosureHundred

@[expose] public section

namespace QED.OneLoop

/-- (Q₂) **The regulated one-loop Pauli form factor at regulator point 2 (Phase 3 theorem goal;
decision D-34).** For `e ≠ 0`, `m > 0`, photon mass `m_γ = m / 100`, Pauli–Villars mass
`Λ = m²/m_γ = 100 * m` and on-shell positive-energy momenta with momentum transfer
`q² = m²/10⁴`, the one-loop vertex (F) has a form-factor pair (G₀) (by (G) exactly one), and
every such pair has its Pauli component `F₂ = (e²/8π²) t` with `t ∈ [0.9700, 0.9705]`.
(The value is `t ≈ 0.970249`; as `m_γ → 0⁺`, `Λ → ∞` and `q² → 0⁺`, `t → 1` by (I).) -/
theorem isFormFactorPair_vertexOneLoop_pauli_enclosure_hundred (e m : ℝ) (he : e ≠ 0) (hm : 0 < m)
    (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : Minkowski.dot (p' - p) (p' - p) = m ^ 2 / 10000) :
    (∃ F : ℂ × ℂ, IsFormFactorPair e m p' p
      (vertexOneLoop e m (m / 100) (100 * m) hm (div_pos hm Nat.ofNat_pos)
        (mul_pos Nat.ofNat_pos hm) p' p hp' hp hp0' hp0) F) ∧
    ∀ F : ℂ × ℂ, IsFormFactorPair e m p' p
        (vertexOneLoop e m (m / 100) (100 * m) hm (div_pos hm Nat.ofNat_pos)
          (mul_pos Nat.ofNat_pos hm) p' p hp' hp hp0' hp0) F →
      ∃ t ∈ Set.Icc (0.9700 : ℝ) 0.9705, F.2 = ((e ^ 2 / (8 * Real.pi ^ 2) * t : ℝ) : ℂ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.OneLoop.isFormFactorPair_vertexOneLoop_pauli_enclosure_hundred
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.OneLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
