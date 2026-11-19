/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Algebra.Contraction
public import QED.Algebra.Dirac
public import QED.Frozen.OneLoop.ElectronPropagator
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-!
# The zero-momentum vertex insertion on an electron line

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57). A
photon vertex of zero momentum contracted with `p` on an electron line of momentum `k` replaces
the propagator `S(k)` by `S(k) p̸ S(k)`. With `{a̸, b̸} = -2 a·b` (mostly-plus metric):

* `numerator_slash_numerator`: `(m - k̸) p̸ (m - k̸) = (k·k + m²) p̸ + 2 (p·k) (m - k̸)`;
* `electronPropagator_slash_electronPropagator`: hence
  `S(k) p̸ S(k) = D⁻² ((k·k + m²) p̸ + 2 (p·k) (m - k̸))` with `D = k·k + m² - iε`.

Along the line `k + t c p` the derivative of the numerator `m - k̸` is `-c p̸` and that of
`k·k + m²` is `2 c (p·k)`, so the first term is (up to the `iε` defect `k·k + m² = D + iε`) the
derivative of the numerator over `D`, and the second the derivative of `D⁻¹`: the Ward–Takahashi
identity `c S p̸ S = -∂ₜ S + c iε p̸ / D²` line by line.
-/

@[expose] public section

open Matrix Complex

namespace QED.GradedProof.WI2

open QED.Dirac

/-- **The insertion numerator**: `(m - k̸) p̸ (m - k̸) = (k·k + m²) p̸ + 2 (p·k) (m - k̸)`. -/
theorem numerator_slash_numerator (m : ℝ) (k p : Fin 4 → ℝ) :
    ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - slash k) * slash p *
        ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - slash k) =
      ((Minkowski.dot k k + m ^ 2 : ℝ) : ℂ) • slash p +
        ((2 * Minkowski.dot p k : ℝ) : ℂ) •
          ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - slash k) := by
  have hkp := slash_anticomm k p
  have hkk := slash_mul_slash k
  have hdot : Minkowski.dot k p = Minkowski.dot p k := by
    simp only [Minkowski.dot_eq]; ring
  -- `k̸ p̸ k̸ = (k·k) p̸ - 2 (p·k) k̸`
  have hkpk : slash k * slash p * slash k =
      ((Minkowski.dot k k : ℝ) : ℂ) • slash p - ((2 * Minkowski.dot p k : ℝ) : ℂ) • slash k := by
    have h1 : slash k * slash p = ((-2 * Minkowski.dot k p : ℝ) : ℂ) • 1 - slash p * slash k :=
      eq_sub_of_add_eq hkp
    rw [h1, sub_mul, Matrix.mul_assoc, hkk, smul_mul_assoc, Matrix.one_mul, mul_smul_comm,
      Matrix.mul_one, hdot]
    push_cast
    simp only [neg_mul, neg_smul, sub_neg_eq_add]
    abel
  have e : ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - slash k) * slash p *
        ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - slash k) =
      ((m : ℂ) ^ 2) • slash p - (m : ℂ) • (slash k * slash p + slash p * slash k) +
        slash k * slash p * slash k := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    module
  rw [e, hkpk, hkp, hdot]
  push_cast
  module

/-- **The insertion on a propagator**: `S(k) p̸ S(k) = D⁻² ((k·k + m²) p̸ + 2 (p·k)(m - k̸))`,
`D = k·k + m² - iε`. -/
theorem electronPropagator_slash_electronPropagator (m ε : ℝ) (k p : Fin 4 → ℝ) :
    QED.OneLoop.electronPropagator m ε k * slash p * QED.OneLoop.electronPropagator m ε k =
      ((((Minkowski.dot k k + m ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) ^ 2)⁻¹ •
        (((Minkowski.dot k k + m ^ 2 : ℝ) : ℂ) • slash p +
          ((2 * Minkowski.dot p k : ℝ) : ℂ) •
            ((m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - slash k)) := by
  rw [← numerator_slash_numerator]
  simp only [QED.OneLoop.electronPropagator, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [← mul_inv, ← sq]

end QED.GradedProof.WI2

end
