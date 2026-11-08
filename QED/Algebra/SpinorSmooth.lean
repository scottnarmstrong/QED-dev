/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Algebra.Bar
public import QED.Frozen.Algebra.Spinor
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity

/-!
# Smoothness of spinor expressions

Real smoothness of the spinor-valued maps used in matrix elements. Spinors are functions
`Fin n → ℂ`, and matrices enter only through their entries, so no norm on matrices is needed.
The Dirac adjoint involves complex conjugation, so all statements are over `ℝ`.

## Main statements

* `QED.Dirac.contDiff_ofReal_comp`: the complexification of a real `C^n` function is `C^n`.
* `QED.Dirac.contDiff_bar_comp`: the Dirac adjoint of a `C^n` spinor field is `C^n`.
* `QED.Dirac.contDiff_dotProduct_mulVec`: the sandwich `w ⬝ᵥ (M *ᵥ v)` is `C^n` when `w`, `v`, and
  the entries of `M` are.
* `QED.Dirac.contDiff_spinor_comp`: `x ↦ u_s(p(x))` is `C^n` when `p` is `C^n` with `p⁰ > 0`.
-/

public section

open Matrix Complex

namespace QED.Dirac

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}

/-- The complexification of a real `C^n` function is `C^n` over `ℝ`. -/
theorem contDiff_ofReal_comp {f : E → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => (f x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

/-- The Dirac adjoint of a `C^n` spinor field is `C^n` over `ℝ`. -/
theorem contDiff_bar_comp {u : E → Fin 4 → ℂ} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (fun x => bar (u x)) := by
  refine contDiff_pi.2 fun j => ?_
  simp only [bar, vecMul, dotProduct, Pi.star_apply]
  exact ContDiff.sum fun i _ =>
    (Complex.conjCLE.contDiff.comp (contDiff_pi.1 hu i)).mul contDiff_const

/-- The sandwich `w ⬝ᵥ (M *ᵥ v)` is `C^n` when `w`, `v`, and every entry of `M` are `C^n`. -/
theorem contDiff_dotProduct_mulVec {ι : Type*} [Fintype ι] {w v : E → ι → ℂ}
    {M : E → Matrix ι ι ℂ} (hw : ContDiff ℝ n w) (hv : ContDiff ℝ n v)
    (hM : ∀ i j, ContDiff ℝ n (fun x => M x i j)) :
    ContDiff ℝ n (fun x => w x ⬝ᵥ (M x *ᵥ v x)) := by
  simp only [dotProduct, mulVec]
  exact ContDiff.sum fun i _ => (contDiff_pi.1 hw i).mul
    (ContDiff.sum fun j _ => (hM i j).mul (contDiff_pi.1 hv j))

/-- The covariant components of a `C^n` four-vector field are `C^n`. -/
theorem contDiff_lower_comp {p : E → Fin 4 → ℝ} (hp : ContDiff ℝ n p) (μ : Fin 4) :
    ContDiff ℝ n (fun x => Minkowski.lower (p x) μ) := by
  unfold Minkowski.lower
  exact ContDiff.sum fun ν _ => contDiff_const.mul (contDiff_pi.1 hp ν)

/-- For `m > 0`, the on-shell spinor `u_s(p(x))` is `C^n` in `x` when `p` is `C^n` with
positive energy `p⁰ > 0`. -/
theorem contDiff_spinor_comp {m : ℝ} (hm : 0 < m) {p : E → Fin 4 → ℝ} (hp : ContDiff ℝ n p)
    (hp0 : ∀ x, 0 < p x 0) (s : Fin 2) :
    ContDiff ℝ n (fun x => spinor m (p x) s) := by
  have hpos : ∀ x, 0 < 2 * m * (m + p x 0) := fun x => by have := hp0 x; positivity
  have hc : ContDiff ℝ n (fun x => (((Real.sqrt (2 * m * (m + p x 0)))⁻¹ : ℝ) : ℂ)) :=
    contDiff_ofReal_comp
      (((contDiff_const.mul (contDiff_const.add (contDiff_pi.1 hp 0))).sqrt
        fun x => (hpos x).ne').inv fun x => (Real.sqrt_pos.2 (hpos x)).ne')
  refine contDiff_pi.2 fun i => ?_
  simp only [spinor, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Matrix.sub_apply, slash,
    Matrix.sum_apply, Matrix.smul_apply]
  exact hc.mul (ContDiff.sum fun j _ => (contDiff_const.sub (ContDiff.sum fun μ _ =>
    (contDiff_ofReal_comp (contDiff_lower_comp hp μ)).mul contDiff_const)).mul contDiff_const)

end QED.Dirac

end
