/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.ElectronPropagator
import Mathlib.Tactic.FinCases

/-!
# Charge conjugation in the Weyl representation

The charge-conjugation matrix of the project's gamma matrices (`QED.Dirac.gamma`, the Weyl
representation of the primary source's (36.7)) and its action on the electron propagator, as
used for Furry's theorem (obligation O2-3, `docs/TWO-LOOP-DERIVATION.md`; Srednicki
problem 58.2).

The matrix `C = γ⁰γ²` is a signed permutation matrix: `C a b = i s(a)` if `b = p(a)` and `0`
otherwise, with the index involution `p = (0 1)(2 3)` (`ccIdx`) and the signs
`s = (1, -1, -1, 1)` (`ccSign`). It satisfies `C² = 1` and `C γ^μ C = -(γ^μ)ᵀ`. Because `C` is a
signed permutation, conjugation by `C` acts on matrix entries by reindexing and signs, which is
the form used in the Furry cancellation:

* `QED.Dirac.chargeConj_mul_gamma_mul_chargeConj`: `C γ^μ C⁻¹ = -(γ^μ)ᵀ`, with `C⁻¹ = C`
  (`QED.Dirac.chargeConj_mul_self`).
* `QED.Dirac.gamma_ccIdx`: entrywise, `γ^μ_{p(b) p(a)} = -s(a) s(b) γ^μ_{a b}`.
* `QED.OneLoop.electronPropagator_ccIdx`: `S̃(k)_{p(a) p(b)} = s(a) s(b) S̃(-k)_{b a}`, at every
  mass, every `ε` and every momentum: the `iε` multiplies the identity part of the denominator,
  which is even in `k`, so the Feynman prescription does not break the symmetry. In matrix form,
  `C S̃(k) C⁻¹ = S̃(-k)ᵀ`.
-/

@[expose] public section

open Matrix Complex

namespace QED.Dirac

/-- The index involution `p = (0 1)(2 3)` of the charge-conjugation matrix. -/
def ccIdx : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- The signs `s = (1, -1, -1, 1)` of the charge-conjugation matrix. -/
def ccSign : Fin 4 → ℂ := ![1, -1, -1, 1]

/-- The charge-conjugation matrix `C = γ⁰γ²` of the Weyl representation. -/
def chargeConj : Matrix (Fin 4) (Fin 4) ℂ := gamma 0 * gamma 2

@[simp] theorem ccIdx_ccIdx (a : Fin 4) : ccIdx (ccIdx a) = a := by
  fin_cases a <;> rfl

theorem ccSign_ccIdx (a : Fin 4) : ccSign (ccIdx a) = -ccSign a := by
  fin_cases a <;> simp [ccSign, ccIdx]

theorem ccSign_mul_self (a : Fin 4) : ccSign a * ccSign a = 1 := by
  fin_cases a <;> simp [ccSign]

/-- `C` is the signed permutation matrix `C a b = i s(a) δ_{b, p(a)}`. -/
theorem chargeConj_apply (a b : Fin 4) :
    chargeConj a b = if b = ccIdx a then I * ccSign a else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [chargeConj, ccIdx, ccSign, gamma, Matrix.mul_apply, Fin.sum_univ_four]

/-- `C² = 1`, so `C⁻¹ = C`. -/
theorem chargeConj_mul_self : chargeConj * chargeConj = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [chargeConj_apply, ccIdx, ccSign, Matrix.mul_apply]

/-- Entrywise charge conjugation of the gamma matrices: `γ^μ_{p(b) p(a)} = -s(a) s(b) γ^μ_{a b}`. -/
theorem gamma_ccIdx (μ a b : Fin 4) :
    gamma μ (ccIdx b) (ccIdx a) = -(ccSign a * ccSign b) * gamma μ a b := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;> simp [gamma, ccIdx, ccSign]

/-- **Charge conjugation of the gamma matrices**: `C γ^μ C⁻¹ = -(γ^μ)ᵀ` with `C⁻¹ = C`. -/
theorem chargeConj_mul_gamma_mul_chargeConj (μ : Fin 4) :
    chargeConj * gamma μ * chargeConj = -(gamma μ)ᵀ := by
  ext a b
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    simp [chargeConj_apply, ccIdx, ccSign, gamma, Matrix.mul_apply, Fin.sum_univ_four]

/-- Entrywise charge conjugation of the slash: `p̸_{p(b) p(a)} = -s(a) s(b) p̸_{a b}`. -/
theorem slash_ccIdx (p : Fin 4 → ℝ) (a b : Fin 4) :
    slash p (ccIdx b) (ccIdx a) = -(ccSign a * ccSign b) * slash p a b := by
  simp only [slash, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, gamma_ccIdx,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

/-- The slash is odd: `(-p)̸ = -p̸`. -/
theorem slash_neg (p : Fin 4 → ℝ) : slash (-p) = -slash p := by
  simp [slash, Minkowski.lower, Finset.sum_neg_distrib]

end QED.Dirac

namespace QED.OneLoop

open QED.Dirac

/-- **Charge conjugation of the electron propagator**, entrywise:
`S̃(k)_{p(a) p(b)} = s(a) s(b) S̃(-k)_{b a}`, for every mass, every `ε` and every momentum. In matrix
form, `C S̃(k) C⁻¹ = S̃(-k)ᵀ`. -/
theorem electronPropagator_ccIdx (m ε : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    electronPropagator m ε k (ccIdx a) (ccIdx b) =
      ccSign a * ccSign b * electronPropagator m ε (-k) b a := by
  have hd : Minkowski.dot (-k) (-k) = Minkowski.dot k k := by
    simp [Minkowski.dot]
  have hs := slash_ccIdx k b a
  have h1 : (1 : Matrix (Fin 4) (Fin 4) ℂ) (ccIdx a) (ccIdx b) =
      ccSign a * ccSign b * (1 : Matrix (Fin 4) (Fin 4) ℂ) b a := by
    by_cases hab : a = b
    · subst hab
      simp [ccSign_mul_self]
    · have : ccIdx a ≠ ccIdx b := fun h => hab (by simpa using congrArg ccIdx h)
      simp [Matrix.one_apply_ne this, Matrix.one_apply_ne (Ne.symm hab)]
  simp only [electronPropagator, hd, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, slash_neg,
    Matrix.neg_apply, h1, hs]
  ring

end QED.OneLoop

end
