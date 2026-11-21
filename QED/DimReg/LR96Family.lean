/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.OnShellFamily
public import QED.DimReg.VacuumThreeLoop

/-!
# The Laporta–Remiddi triple-cross family: positivity on shell and normalization

**The family.** Laporta and Remiddi (1996; arXiv:hep-ph/9602417), eq. (9), use the eight
denominators (in `m = 1` units, metric with propagators `q² + m²` and on-shell `p² = -1`)
`D₁ = (p - k₁)² + 1`, `D₂ = (p - k₁ - k₂)² + 1`, `D₃ = (p - k₁ - k₂ - k₃)² + 1`,
`D₄ = (p - k₂ - k₃)² + 1`, `D₅ = (p - k₃)² + 1`, `D₆ = k₁²`, `D₇ = k₂²`, `D₈ = k₃²`.
`QED.DimReg.lr96Graph` encodes them as an on-shell one-mass family, and
`QED.DimReg.lr96Graph_lpPoly_pos` shows that its Lee–Pomeransky polynomial `U + F` is positive
on the open orthant (`U > 0`, `F ≥ 0`), so every integral of the family is a real integral of a
positive integrand, with no `iε`.

**The normalization.** LR96 normalize every three-loop integral by
`((-i) / π ^ (n - 2))³ ∫ dⁿk₁ dⁿk₂ dⁿk₃` (source, definition of `I₁ … I₁₈` before eq. (14)), with
`n = 4 - 2ω`. In their metric the Wick rotation `k₀ = i k_E,₀` (which crosses no pole, the
propagator poles lying in the second and fourth quadrants) gives `dⁿk = i dⁿk_E`, so each loop
carries `dⁿk_E / π ^ (n - 2) = π ^ (2 - n / 2) · dⁿk_E / π ^ (n / 2)`. Relative to the
normalization of `QED.DimReg.FeynmanFamily.integral` (`dᵈk_E / π ^ (d / 2)` per loop) the factor
is therefore `π ^ (2 - d / 2) = π ^ ω` per loop (`QED.DimReg.lr96LoopFactor`). For `I₁₈`, the
product of three unit tadpoles, this gives `I₁₈ = π ^ (3ω) Γ(-1 + ω)³`, and LR96 eq. (14) with
`C(ω) = (π ^ ω Γ(1 + ω))³` holds exactly (`QED.DimReg.lr96I18_laurent`). The Wick rotation
itself is a convention recorded here, not a formal theorem.
-/

@[expose] public section

open MvPolynomial Complex

namespace QED.DimReg

/-- The LR96 triple-cross family (their eq. (9)): lines `1 … 5` massive with loop momenta
`k₁, k₁ + k₂, k₁ + k₂ + k₃, k₂ + k₃, k₃`, lines `6, 7, 8` the photons `k₁, k₂, k₃`. -/
def lr96Graph : OnShellGraph 8 3 where
  v := ![![1, 0, 0], ![1, 1, 0], ![1, 1, 1], ![0, 1, 1], ![0, 0, 1], ![1, 0, 0], ![0, 1, 0],
    ![0, 0, 1]]
  massive := fun i => decide (i.val < 5)

theorem lr96Graph_span : ∀ j : Fin 3, ∃ i : Fin 8, lr96Graph.v i = Pi.single j 1 := by
  intro j
  fin_cases j
  · exact ⟨5, by funext k; fin_cases k <;> simp [lr96Graph]⟩
  · exact ⟨6, by funext k; fin_cases k <;> simp [lr96Graph]⟩
  · exact ⟨7, by funext k; fin_cases k <;> simp [lr96Graph]⟩

/-- The LR96 family as a parametric family: `L = 3`, `U = det A`, `F = βᵀ adj(A) β`. -/
noncomputable def lr96Family : FeynmanFamily 8 := lr96Graph.toFamily

/-- `U > 0` on the open orthant for the LR96 family. -/
theorem lr96Graph_symU_pos {x : Fin 8 → ℝ} (hx : x ∈ posOrthant 8) :
    0 < eval x lr96Graph.symU :=
  lr96Graph.eval_symU_pos lr96Graph_span hx

/-- **On-shell positivity of LR96's family**: `F ≥ 0` on the open orthant. -/
theorem lr96Graph_symF_nonneg {x : Fin 8 → ℝ} (hx : x ∈ posOrthant 8) :
    0 ≤ eval x lr96Graph.symF :=
  lr96Graph.eval_symF_nonneg lr96Graph_span hx

/-- The Lee–Pomeransky polynomial `U + F` of the LR96 family is positive on the orthant. -/
theorem lr96Graph_lpPoly_pos {x : Fin 8 → ℝ} (hx : x ∈ posOrthant 8) :
    0 < lr96Family.lpPoly x :=
  lr96Graph.lpPoly_toFamily_pos lr96Graph_span hx

/-- The LR96 normalization relative to ours, per loop: `π ^ (2 - d / 2)`. -/
noncomputable def lr96LoopFactor (d : ℂ) : ℂ := (Real.pi : ℂ) ^ (2 - d / 2)

theorem lr96LoopFactor_four_sub (ω : ℂ) : lr96LoopFactor (4 - 2 * ω) = (Real.pi : ℂ) ^ ω := by
  rw [lr96LoopFactor]
  congr 1
  ring

/-- `I₁₈` in LR96's normalization: the cube of the unit `ν = 1` tadpole, each loop carrying
`lr96LoopFactor`. -/
noncomputable def lr96I18 (ω : ℂ) : ℂ := (lr96LoopFactor (4 - 2 * ω) * tadpole 1 1 (4 - 2 * ω)) ^ 3

/-- **LR96 eq. (14), with their normalization pinned.** For `ω ≠ 0, 1`,
`I₁₈ = C(ω) (-ω⁻³ - 3ω⁻² - 6ω⁻¹ - 10 - 15ω - 21ω² - 28ω³ + ω⁴ R(ω))` with
`C(ω) = (π ^ ω Γ(1 + ω))³`. -/
theorem lr96I18_laurent {ω : ℂ} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    lr96I18 ω = ((Real.pi : ℂ) ^ ω * Gamma (1 + ω)) ^ 3 *
      (vacuumLaurentPoly ω + ω ^ 4 * vacuumRemainder ω) := by
  rw [lr96I18, lr96LoopFactor_four_sub, mul_pow, ← vacuumProduct]
  exact mul_cube_vacuumProduct_laurent _ h0 h1

end QED.DimReg
