/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Symanzik polynomials of on-shell one-mass families, and positivity

A family of the on-shell lepton type has `L` loop momenta `k = (k₁, …, k_L)`, one external
momentum `p` with `p² = -1` (mass shell, `m = 1`, in the metric where propagators read
`q² + m²`), and `N` propagators of two kinds:
* massive lines `Dᵢ = (p - vᵢ·k)² + 1`, and
* massless lines `Dᵢ = (vᵢ·k)²`,
with integer coefficient vectors `vᵢ ∈ ℤᴸ` (`QED.DimReg.OnShellGraph`). Since `p² + 1 = 0`, a
massive line is `(vᵢ·k)² - 2 p·(vᵢ·k)`, so `∑ xᵢ Dᵢ = kᵀ A k - 2 (β·k)·p` with
`A = ∑ᵢ xᵢ vᵢ vᵢᵀ` and `β = ∑_{massive} xᵢ vᵢ`. Completing the square, the Symanzik polynomials
are `U = det A` and `F = U · (-p²) βᵀ A⁻¹ β = βᵀ adj(A) β`
(`QED.DimReg.OnShellGraph.symU`, `QED.DimReg.OnShellGraph.symF`).

If every loop momentum occurs alone on some line (`vᵢ = eⱼ`), then `A` is positive definite on
the open orthant, so `U > 0` and `F = det A · βᵀ A⁻¹ β ≥ 0` there
(`QED.DimReg.OnShellGraph.eval_symU_pos`, `QED.DimReg.OnShellGraph.eval_symF_nonneg`). In
particular the Lee–Pomeransky polynomial `G = U + F` is positive on the orthant, which is the
hypothesis of the convergence, dimension-shift and integration-by-parts theorems: on shell the
integrand is real and positive and needs no `iε`.

## Main definitions and results

* `QED.DimReg.OnShellGraph`, `symA`, `symβ`, `symU`, `symF`, `toFamily`.
* `QED.DimReg.OnShellGraph.posDef_evalA`: `A(x)` is positive definite on the orthant.
* `QED.DimReg.OnShellGraph.eval_symU_pos`, `eval_symF_nonneg`, `lpPoly_toFamily_pos`.
* `QED.DimReg.oneLoopSelfEnergy_symF`: sanity check, `U = x₁ + x₂`, `F = x₁²` at one loop.
-/

@[expose] public section

open MvPolynomial Matrix

namespace QED.DimReg

/-- An on-shell one-mass family: for each of the `N` lines the coefficients `vᵢ ∈ ℤᴸ` of its
loop momentum `vᵢ·k`, and whether it is massive (`Dᵢ = (p - vᵢ·k)² + 1`) or massless
(`Dᵢ = (vᵢ·k)²`). -/
structure OnShellGraph (N L : ℕ) where
  /-- The loop-momentum coefficients of each line. -/
  v : Fin N → Fin L → ℤ
  /-- Whether the line is massive (carries `p` and mass `1`). -/
  massive : Fin N → Bool

namespace OnShellGraph

variable {N L : ℕ} (g : OnShellGraph N L)

/-- The matrix `A = ∑ᵢ xᵢ vᵢ vᵢᵀ` of the quadratic form in the loop momenta. -/
noncomputable def symA : Matrix (Fin L) (Fin L) (MvPolynomial (Fin N) ℝ) :=
  fun j k => ∑ i, X i * C ((g.v i j : ℝ) * (g.v i k : ℝ))

/-- The vector `β = ∑_{massive} xᵢ vᵢ` of the linear term. -/
noncomputable def symβ : Fin L → MvPolynomial (Fin N) ℝ :=
  fun j => ∑ i, if g.massive i then X i * C (g.v i j : ℝ) else 0

/-- The first Symanzik polynomial `U = det A`. -/
noncomputable def symU : MvPolynomial (Fin N) ℝ := (g.symA).det

/-- The second Symanzik polynomial on shell, `F = βᵀ adj(A) β`. -/
noncomputable def symF : MvPolynomial (Fin N) ℝ := g.symβ ⬝ᵥ (g.symA.adjugate *ᵥ g.symβ)

/-- The Feynman family with loop number `L` and Symanzik polynomials `U`, `F`. -/
noncomputable def toFamily : FeynmanFamily N := ⟨L, g.symU, g.symF⟩

/-- `A` evaluated at a point. -/
noncomputable def evalA (x : Fin N → ℝ) : Matrix (Fin L) (Fin L) ℝ :=
  fun j k => ∑ i, x i * ((g.v i j : ℝ) * (g.v i k : ℝ))

/-- `β` evaluated at a point. -/
noncomputable def evalβ (x : Fin N → ℝ) : Fin L → ℝ :=
  fun j => ∑ i, if g.massive i then x i * (g.v i j : ℝ) else 0

theorem mapMatrix_symA (x : Fin N → ℝ) : (eval x).mapMatrix g.symA = g.evalA x := by
  ext j k
  simp [symA, evalA]

theorem eval_symβ (x : Fin N → ℝ) (j : Fin L) : eval x (g.symβ j) = g.evalβ x j := by
  simp only [symβ, evalβ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem eval_symU (x : Fin N → ℝ) : eval x g.symU = (g.evalA x).det := by
  rw [symU, RingHom.map_det, mapMatrix_symA]

theorem eval_symF (x : Fin N → ℝ) :
    eval x g.symF = g.evalβ x ⬝ᵥ ((g.evalA x).adjugate *ᵥ g.evalβ x) := by
  have hadj : ∀ j k, eval x (g.symA.adjugate j k) = (g.evalA x).adjugate j k := by
    intro j k
    rw [← mapMatrix_symA, ← RingHom.map_adjugate]
    rfl
  simp only [symF, dotProduct, mulVec, map_sum, map_mul, hadj, eval_symβ]

/-- The quadratic form of `A(x)` is `∑ᵢ xᵢ (vᵢ·y)²`. -/
theorem dotProduct_evalA_mulVec (y : Fin L → ℝ) (x : Fin N → ℝ) :
    y ⬝ᵥ (g.evalA x *ᵥ y) = ∑ i, x i * (∑ j, (g.v i j : ℝ) * y j) ^ 2 := by
  simp only [dotProduct, mulVec, evalA, Finset.mul_sum, Finset.sum_mul, sq]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/-- If every loop momentum occurs alone on some line, `A(x)` is positive definite on the open
orthant. -/
theorem posDef_evalA (hspan : ∀ j : Fin L, ∃ i : Fin N, g.v i = Pi.single j 1)
    {x : Fin N → ℝ} (hx : x ∈ posOrthant N) : (g.evalA x).PosDef := by
  rw [mem_posOrthant] at hx
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun y hy => ?_⟩
  · ext j k
    simp only [conjTranspose_apply, star_trivial, evalA]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · simp only [star_trivial]
    rw [dotProduct_evalA_mulVec g y x]
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
      by_contra h
      exact hy (funext fun j => by_contra fun hj => h ⟨j, hj⟩)
    obtain ⟨i, hi⟩ := hspan j
    have hterm : 0 < x i * (∑ l, (g.v i l : ℝ) * y l) ^ 2 := by
      have : (∑ l, (g.v i l : ℝ) * y l) = y j := by
        rw [hi]
        simp [Pi.single_apply]
      rw [this]
      exact mul_pos (hx i) (by positivity)
    exact hterm.trans_le (Finset.single_le_sum (f := fun i => x i * (∑ l, (g.v i l : ℝ) * y l) ^ 2)
      (fun i _ => mul_nonneg (hx i).le (sq_nonneg _)) (Finset.mem_univ i))

/-- `U > 0` on the open orthant. -/
theorem eval_symU_pos (hspan : ∀ j : Fin L, ∃ i : Fin N, g.v i = Pi.single j 1)
    {x : Fin N → ℝ} (hx : x ∈ posOrthant N) : 0 < eval x g.symU := by
  rw [eval_symU]
  exact (g.posDef_evalA hspan hx).det_pos

/-- **On-shell positivity.** `F = βᵀ adj(A) β ≥ 0` on the open orthant. -/
theorem eval_symF_nonneg (hspan : ∀ j : Fin L, ∃ i : Fin N, g.v i = Pi.single j 1)
    {x : Fin N → ℝ} (hx : x ∈ posOrthant N) : 0 ≤ eval x g.symF := by
  have hA := g.posDef_evalA hspan hx
  have hdet := hA.det_pos
  have hadj : (g.evalA x).adjugate = (g.evalA x).det • (g.evalA x)⁻¹ := by
    rw [inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hdet.ne', one_smul]
  rw [eval_symF, hadj, smul_mulVec, dotProduct_smul, smul_eq_mul]
  refine mul_nonneg hdet.le ?_
  simpa using hA.posSemidef.inv.dotProduct_mulVec_nonneg (g.evalβ x)

/-- The Lee–Pomeransky polynomial `G = U + F` is positive on the open orthant. -/
theorem lpPoly_toFamily_pos (hspan : ∀ j : Fin L, ∃ i : Fin N, g.v i = Pi.single j 1)
    {x : Fin N → ℝ} (hx : x ∈ posOrthant N) : 0 < g.toFamily.lpPoly x := by
  simp only [FeynmanFamily.lpPoly, toFamily, map_add]
  exact add_pos_of_pos_of_nonneg (g.eval_symU_pos hspan hx) (g.eval_symF_nonneg hspan hx)

end OnShellGraph

/-- The one-loop on-shell self-energy: an electron line `(p - k)² + 1` and a photon `k²`. -/
def oneLoopSelfEnergy : OnShellGraph 2 1 where
  v := fun _ _ => 1
  massive := fun i => i = 0

/-- Sanity check: at one loop `U = x₁ + x₂`. -/
theorem oneLoopSelfEnergy_symU : oneLoopSelfEnergy.symU = X 0 + X 1 := by
  simp [OnShellGraph.symU, OnShellGraph.symA, oneLoopSelfEnergy, Fin.sum_univ_two]

/-- Sanity check: at one loop on shell `F = x₁²`. -/
theorem oneLoopSelfEnergy_symF : oneLoopSelfEnergy.symF = X 0 ^ 2 := by
  simp [OnShellGraph.symF, OnShellGraph.symβ, oneLoopSelfEnergy, dotProduct,
    mulVec, adjugate_fin_one, sq]

end QED.DimReg
