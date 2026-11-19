/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.ClassLimitParametric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The closed-form moment functional of the parametric integrand

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A1 (`STATUS.md` of the WI₂ effort: the parametric derivative identity). At a fixed Feynman
point the parametric integrand `QED.TwoLoop.ClassLimit.paramIntegrand` of `m + 1` lines is
`U⁻² Ê_m[P](X, W)` with the shift `X = -S`, `W = V - iε` and

`Ê_m[P](X, W) = (m-4)! W^{3-m} P(X) + (m-5)!/2 W^{4-m} ∑ H(X) G + (m-6)!/4 W^{5-m} ∑ R Π(G)`,

`G = loopMetricInv A` (`paramIntegrand_eq_ehat`). Differentiating the denominator power raises
the number of lines by one (`hasDerivAt_ehat`): `∂_W Ê_m[P] = -Ê_{m+1}[P]`. This is the
`W`-part of the parametric derivative identity
`∂ₜ Ê_m[Pₜ] = Ê_m[∂ₜ P] - Ê_{m+1}[P ∂ₜ Q_z]`, checked exactly in the scratch script
`check_pa.py` of the WI₂ effort.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.WI2

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.Integration.Feynman (simplexPoint)

/-- **The moment functional** `Ê_m[P](X, W)` of `m + 1` lines, with `G = loopMetricInv A`. -/
noncomputable def ehat (m : ℕ) (P : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X : LoopIndex → ℂ) (W : ℂ) : ℂ :=
  ((m - 4).factorial : ℂ) * (W ^ (m - 3))⁻¹ * P.evalC X +
    ((m - 5).factorial : ℂ) / 2 * (W ^ (m - 4))⁻¹ * P.contractTwo A X +
    ((m - 6).factorial : ℂ) / 4 * (W ^ (m - 5))⁻¹ * P.contractFour A

/-- The parametric integrand is `U⁻²` times the moment functional at `X = -S`, `W = V - iε`. -/
theorem paramIntegrand_eq_ehat {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (ε : ℝ) (x : Fin m → ℝ) :
    paramIntegrand P α p M ε x =
      ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
        ehat m P (symanzikMatrix α (simplexPoint x))
          (loopComp (-loopShift α p (simplexPoint x)))
          (((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I) := by
  rfl

theorem hasDerivAt_inv_pow {k : ℕ} {W : ℂ} (hW : W ≠ 0) :
    HasDerivAt (fun w : ℂ => (w ^ k)⁻¹) (-((k : ℂ) * (W ^ (k + 1))⁻¹)) W := by
  have h := (hasDerivAt_pow k W).inv (pow_ne_zero k hW)
  convert h using 1
  rcases k with _ | k
  · simp
  · field_simp
    push_cast
    ring

/-- **Differentiating the denominator power adds a line**: `∂_W Ê_{n+6}[P] = -Ê_{n+7}[P]`. -/
theorem hasDerivAt_ehat (n : ℕ) (P : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X : LoopIndex → ℂ) {W : ℂ} (hW : W ≠ 0) :
    HasDerivAt (fun w => ehat (n + 6) P A X w) (-ehat (n + 7) P A X W) W := by
  have e6 : ∀ w, ehat (n + 6) P A X w =
      ((n + 2).factorial : ℂ) * (w ^ (n + 3))⁻¹ * P.evalC X +
        ((n + 1).factorial : ℂ) / 2 * (w ^ (n + 2))⁻¹ * P.contractTwo A X +
        (n.factorial : ℂ) / 4 * (w ^ (n + 1))⁻¹ * P.contractFour A := fun w => by
    simp only [ehat, show n + 6 - 4 = n + 2 by omega, show n + 6 - 3 = n + 3 by omega,
      show n + 6 - 5 = n + 1 by omega, show n + 6 - 6 = n by omega]
  have e7 : ehat (n + 7) P A X W =
      ((n + 3).factorial : ℂ) * (W ^ (n + 4))⁻¹ * P.evalC X +
        ((n + 2).factorial : ℂ) / 2 * (W ^ (n + 3))⁻¹ * P.contractTwo A X +
        ((n + 1).factorial : ℂ) / 4 * (W ^ (n + 2))⁻¹ * P.contractFour A := by
    simp only [ehat, show n + 7 - 4 = n + 3 by omega, show n + 7 - 3 = n + 4 by omega,
      show n + 7 - 5 = n + 2 by omega, show n + 7 - 6 = n + 1 by omega]
  simp only [e6]
  have h := ((((hasDerivAt_inv_pow (k := n + 3) hW).const_mul
      ((n + 2).factorial : ℂ)).mul_const (P.evalC X)).add
    (((hasDerivAt_inv_pow (k := n + 2) hW).const_mul
      (((n + 1).factorial : ℂ) / 2)).mul_const (P.contractTwo A X))).add
    (((hasDerivAt_inv_pow (k := n + 1) hW).const_mul
      ((n.factorial : ℂ) / 4)).mul_const (P.contractFour A))
  convert h using 1
  rw [e7, Nat.factorial_succ (n + 2), Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  push_cast
  ring

end QED.GradedProof.WI2

end
