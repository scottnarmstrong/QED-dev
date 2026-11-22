/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersGamma2
public import QED.DimReg.MasslessBubble
public import QED.DimReg.VacuumTwoMass

/-!
# Set (d): the closed forms behind `I₁₄` and `I₁₆` are derived from parametric integrals

`QED.ThreeLoopD.SetDMastersGamma2` builds the masters `I₁₄` and `I₁₆` from four one- and two-loop
closed forms. Two of them, the tadpole (`QED.DimReg.integral_tadpoleFamily`) and the on-shell
one-loop integral (`QED.DimReg.OneLoopSchwinger.schw_eq_phi`), were already proved from their
parametric integrals. Here we prove the other two, which `SetDMastersGamma2` takes as
definitions:

* `QED.ThreeLoopD.masslessBubble_eq_integral`: the massless bubble `G(1, 1)` is the normalized
  Lee–Pomeransky integral of the one-loop massless bubble at `q² = 1`
  (`QED.DimReg.masslessBubbleFamily`), for `2 < re d < 4`;
* `QED.ThreeLoopD.vacuumTwoMass_eq_integral`: `vacuumTwoMass ν d` is the normalized
  Lee–Pomeransky integral of the two-loop vacuum graph with two unit masses and a massless line
  of power `ν` (`QED.DimReg.vacuumTwoMassFamily`), in its region of convergence.

Both closed forms are meromorphic in `d` (`QED.ThreeLoopD.meromorphic_masslessBubble`,
`QED.ThreeLoopD.meromorphic_vacuumTwoMass`), so they are the meromorphic continuations of the
integrals. For `I₁₄` the two strips overlap: for `2/3 < re ω < 1` the master is the product of
the two parametric integrals (`QED.ThreeLoopD.lr96I14_eq_integral`). (For `I₁₆` the strips of
the tadpole, `re ω > 1`, and of the bubble, `re ω < 1`, are disjoint; each factor is the
continuation of its own integral.)

What remains a convention is the momentum-space factorization of each three-loop graph into
these one- and two-loop pieces and the Wick rotation, as in `QED.DimReg.LR96Family`.
-/

@[expose] public section

open Complex QED.DimReg

namespace QED.ThreeLoopD

/-- **The massless bubble, derived.** For `2 < re d < 4`, `G(1, 1)` is the normalized
Lee–Pomeransky integral of the one-loop massless bubble with `q² = 1`. -/
theorem masslessBubble_eq_integral {d : ℂ} (h1 : 2 < d.re) (h2 : d.re < 4) :
    (masslessBubbleFamily 1).integral (fun _ => 1) d = masslessBubble d := by
  rw [integral_masslessBubbleFamily one_pos (by simp) (by simp; linarith) (by simp; linarith)
    (by simp; linarith), masslessBubbleCoeff, masslessBubble, ofReal_one, one_cpow, mul_one,
    Gamma_one, show d - 1 - 1 = d - 2 by ring, show (1 : ℂ) + 1 - d / 2 = 2 - d / 2 by ring]
  ring

/-- **The two-mass vacuum integral, derived.** In its region of absolute convergence,
`vacuumTwoMass ν d` is the normalized Lee–Pomeransky integral of the two-loop vacuum graph with
two unit-mass lines (power `1`) and a massless line of power `ν`. -/
theorem vacuumTwoMass_eq_integral {ν d : ℂ} (h0 : 0 < ν.re) (h1 : 0 < (d / 2 - ν).re)
    (h2 : 0 < (2 + ν - d).re) (h3 : 0 < (3 * d / 2 - 2 - ν).re) (h4 : 0 < (1 + ν - d / 2).re) :
    vacuumTwoMassFamily.integral ![1, 1, ν] d = vacuumTwoMass ν d := by
  have e2 : (1 : ℂ) + 1 + ν - d = 2 + ν - d := by ring
  have e3 : 3 * d / 2 - 1 - 1 - ν = 3 * d / 2 - 2 - ν := by ring
  rw [integral_vacuumTwoMassFamily (by simpa using h0) (by simpa using h1) (by simpa [e2] using h2)
    (by simpa [e3] using h3) (by simpa using h4) (by simpa using h4), vacuumTwoMassCoeff,
    vacuumTwoMass]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Gamma_one, one_mul]
  rw [show (1 : ℂ) + 1 + ν - d = 2 + ν - d by ring,
    show (1 : ℂ) + 1 + 2 * ν - d = 2 + 2 * ν - d by ring]
  ring

/-- **`I₁₄` from parametric integrals.** For `2/3 < re ω < 1` (where both integrals converge
absolutely), LR96's `I₁₄` is `π ^ (3ω)` times the massless bubble integral times the two-mass
vacuum integral with massless power `ω`, at `d = 4 - 2ω`. -/
theorem lr96I14_eq_integral {ω : ℂ} (h1 : 2 / 3 < ω.re) (h2 : ω.re < 1) :
    lr96I14 ω = lr96LoopFactor (4 - 2 * ω) ^ 3 *
      ((masslessBubbleFamily 1).integral (fun _ => 1) (4 - 2 * ω) *
        vacuumTwoMassFamily.integral ![1, 1, ω] (4 - 2 * ω)) := by
  have hν : 2 - (4 - 2 * ω) / 2 = ω := by ring
  rw [lr96I14, hν, masslessBubble_eq_integral (by simp; linarith) (by simp; linarith),
    vacuumTwoMass_eq_integral (by linarith) (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith)]

/-- The massless bubble closed form is meromorphic in `d` on `ℂ`. -/
theorem meromorphic_masslessBubble : Meromorphic masslessBubble := by
  intro z
  unfold masslessBubble
  exact ((meromorphicAt_Gamma_comp (by fun_prop)).mul
    ((meromorphicAt_Gamma_comp (by fun_prop)).pow 2)).div (meromorphicAt_Gamma_comp (by fun_prop))

/-- The two-mass vacuum closed form is meromorphic in `d` on `ℂ`, for `ν` any analytic function
of `d` (e.g. `ν = 2 - d/2` in `I₁₄`). -/
theorem meromorphic_vacuumTwoMass {ν : ℂ → ℂ} (hν : Differentiable ℂ ν) :
    Meromorphic fun d => vacuumTwoMass (ν d) d := by
  intro z
  have hνz : AnalyticAt ℂ ν z := hν.analyticAt z
  unfold vacuumTwoMass
  exact ((((meromorphicAt_Gamma_comp (by fun_prop)).pow 2).mul
    (meromorphicAt_Gamma_comp (by fun_prop))).mul (meromorphicAt_Gamma_comp (by fun_prop))).div
    ((meromorphicAt_Gamma_comp (by fun_prop)).mul (meromorphicAt_Gamma_comp (by fun_prop)))

end QED.ThreeLoopD
