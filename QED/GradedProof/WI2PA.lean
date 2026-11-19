/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2Square

/-!
# The parametric derivative identity (PA)

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A1, assembled. Along the line `s ↦ p + s q` of external line momenta and a path `P s` of
numerators of degree at most three, at every Feynman point with `W = V - iε ≠ 0`
(`hasDerivAt_paramIntegrand_line`):

`∂ₛ paramIntegrand_N[P s](p + s q) = paramIntegrand_N[P'] - U⁻² Ê_{N+1}[P · ∑ᵢ zᵢ ∂ₛDᵢ]`,

with the same `U, S, V, G` in the `(N+1)`-line functional and `∂ₛDᵢ(ℓ) = 2 kᵢ(ℓ)·qᵢ` (the
affine form `dLineC + dLineL·ℓ`). The proof combines the path derivative
(`hasDerivAt_ehat_path`), the Stein identity (`ehat_mulLin`), the derivative of the completed
square (`hasDerivAt_symanzikV`) and `G ∑ᵢ zᵢ dLineL = 2 S(q)` (`sum_loopMetricInv_dLineL`). This is
the identity checked exactly in `check_pa.py` of the WI₂ effort.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.WI2

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.Minkowski
open QED.Integration.Feynman (simplexPoint)

variable {m : ℕ}

/-- The combined derivative `∑ᵢ zᵢ ∂ₛDᵢ` at `ℓ` is `∑ᵢ zᵢ 2 kᵢ(ℓ)·qᵢ`. -/
theorem sum_dLineC_add_linF (α : Fin (m + 1) → Fin 2 → ℝ) (P q : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ i, (z i : ℂ) * dLineC (P i) (q i) +
        linF (fun a => ∑ i, (z i : ℂ) * dLineL (α i) (q i) a) (loopComp ℓ) =
      ((∑ i, z i * (2 * dot (lineMomentum α P i ℓ) (q i)) : ℝ) : ℂ) := by
  have hl : linF (fun a => ∑ i, (z i : ℂ) * dLineL (α i) (q i) a) (loopComp ℓ) =
      ∑ i, (z i : ℂ) * linF (dLineL (α i) (q i)) (loopComp ℓ) := by
    simp only [linF, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hl, ← Finset.sum_add_distrib]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_add, dLineC_add_linF]
  rfl

/-- **The parametric derivative identity (PA).** -/
theorem hasDerivAt_paramIntegrand_line (n : ℕ) {P : ℝ → LoopQuartic} {P' : LoopQuartic}
    {t : ℝ} (hP : HasQDerivAt P P' t) (hq : (P t).quart = 0)
    (α : Fin (n + 6 + 1) → Fin 2 → ℝ) (p q : Fin (n + 6 + 1) → Fin 4 → ℝ)
    (M : Fin (n + 6 + 1) → ℝ) (ε : ℝ) (x : Fin (n + 6) → ℝ)
    (hW : ((symanzikV α (p + t • q) M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I ≠ 0) :
    HasDerivAt (fun s => paramIntegrand (P s) α (p + s • q) M ε x)
      (paramIntegrand P' α (p + t • q) M ε x -
        ((symanzikU α (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
          ehat (n + 7) (Cubic.mulLin (P t)
              (∑ i, (simplexPoint x i : ℂ) * dLineC ((p + t • q) i) (q i))
              (fun a => ∑ i, (simplexPoint x i : ℂ) * dLineL (α i) (q i) a))
            (symanzikMatrix α (simplexPoint x))
            (loopComp (-loopShift α (p + t • q) (simplexPoint x)))
            (((symanzikV α (p + t • q) M (simplexPoint x) : ℝ) : ℂ) - (ε : ℂ) * I)) t := by
  simp only [paramIntegrand_eq_ehat]
  set z := simplexPoint x
  set A := symanzikMatrix α z
  have hA : A.transpose = A := (symanzikMatrix_isSymm α z).eq
  have hX := hasDerivAt_loopComp_shift α p q z t
  have hWd := ((hasDerivAt_symanzikV α p q M z t).ofReal_comp).sub_const ((ε : ℂ) * I)
  have h := (hasDerivAt_ehat_path n hP A hX hWd hW).const_mul
    (((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹)
  convert h using 1
  set X := loopComp (-loopShift α (p + t • q) z)
  set W := ((symanzikV α (p + t • q) M z : ℝ) : ℂ) - (ε : ℂ) * I
  set Y : LoopIndex → ℂ := fun a => 2 * loopComp (loopShift α q z) a
  have hY : ∀ a, ∑ d, ((loopMetricInv A a d : ℝ) : ℂ) *
      (fun a => ∑ i, (z i : ℂ) * dLineL (α i) (q i) a) d = Y a :=
    sum_loopMetricInv_dLineL α q z
  have hX' : loopComp (-loopShift α q z) = fun a => (-1 / 2 : ℂ) * Y a := by
    funext a
    simp only [Y, loopComp, Pi.neg_apply]
    push_cast
    ring
  rw [ehat_mulLin (P t) hq n _ _ Y hA hY, sum_dLineC_add_linF, gradPart_eq (P t) hq, hX',
    ehat_dirDeriv_smul (P t) hq n A X Y (-1 / 2) W]
  ring

end QED.GradedProof.WI2

end
