/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.V5ZeroDiracBoost
public import QED.GradedProof.SE2RealSharp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# A covariant `♯`-fixed vertex at `p' = p` is a real multiple of `γ^μ` on shell

Helper level for the order-`e⁵` vertex at `q = 0` (`QED.GradedProof.GEx2.VertexZeroInput`). By
`exists_sandwich_eq_of_cov`, a covariant vertex `V p` at `p' = p` satisfies
`w V(p)^μ u = c · w γ^μ u` between on-shell spinors for one `c ∈ ℂ`. If moreover each `V(p)^μ` is
fixed by the antilinear automorphism `X♯ = C X̄ C⁻¹` (`QED.GradedProof.SE2Real.sharp`), then `c`
is real (`exists_real_sandwich_eq_of_cov`): at the rest momentum, with `e = (1, 0, 1, 0)` and
`f = (0, 1, 0, 1)`, `e V⁰ e = 2c`, `f V⁰ f = 2c`, and `V⁰♯ = V⁰` gives `f V⁰ f = conj (e V⁰ e)`
(`im_eq_zero_of_sharp`).
-/

@[expose] public section

open Matrix Complex

namespace QED.GradedProof.V5Zero.Dirac

open QED.Dirac QED.TwoLoop.LimitCovariance QED.GradedProof.SE2Real

theorem slash_restVec_mulVec {m : ℝ} {u : Fin 4 → ℂ} (hu : gamma 0 *ᵥ u = u) :
    slash (restVec m) *ᵥ u = -((m : ℂ) • u) := by
  rw [slash_restVec, smul_mulVec, hu, neg_smul]

theorem vecMul_slash_restVec {m : ℝ} {w : Fin 4 → ℂ} (hw : w ᵥ* gamma 0 = w) :
    w ᵥ* slash (restVec m) = -((m : ℂ) • w) := by
  rw [slash_restVec, vecMul_smul, hw, neg_smul]

/-- **Reality of the rest-frame coefficient.** If `Y♯ = Y` and `w Y u = c · w γ⁰ u` between
on-shell spinors at `p₀ = (m, 0, 0, 0)`, then `c` is real. -/
theorem im_eq_zero_of_sharp {m : ℝ} {Y : Matrix (Fin 4) (Fin 4) ℂ} (hY : sharp Y = Y) {c : ℂ}
    (hc : SandwichEq m (restVec m) Y c (gamma 0)) : c.im = 0 := by
  have hs : ∀ i j, sharp Y i j = Y i j := fun i j => by rw [hY]
  have h33 := hs 3 3
  have h31 := hs 3 1
  have h13 := hs 1 3
  have h11 := hs 1 1
  simp only [sharp, Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_four,
    Matrix.map_apply] at h33 h31 h13 h11
  simp [cMat] at h33 h31 h13 h11
  have he := hc ![1, 0, 1, 0] ![1, 0, 1, 0]
    (slash_restVec_mulVec (by ext i; fin_cases i <;> simp [gamma, mulVec]))
    (vecMul_slash_restVec (by ext i; fin_cases i <;> simp [gamma, vecMul]))
  have hf := hc ![0, 1, 0, 1] ![0, 1, 0, 1]
    (slash_restVec_mulVec (by ext i; fin_cases i <;> simp [gamma, mulVec]))
    (vecMul_slash_restVec (by ext i; fin_cases i <;> simp [gamma, vecMul]))
  simp [gamma, mulVec, dotProduct, Fin.sum_univ_four] at he hf
  have e2 := congrArg (starRingEnd ℂ) he
  simp only [map_add, map_mul, map_one] at e2
  have hconj : starRingEnd ℂ c = c := by
    linear_combination (hf - e2 + h33 + h31 + h13 + h11) / 2
  exact Complex.conj_eq_iff_im.mp hconj

/-- **A covariant `♯`-fixed vertex at `p' = p` is a real multiple of `γ^μ` on shell.** The
covariance hypothesis is the form of `QED.TwoLoop.PauliZero.conj_vertexLimit_map` at
`p' = p`; the conclusion is the shape of `QED.GradedProof.GEx2.VertexZeroInput`. -/
theorem exists_real_sandwich_eq_of_cov {m : ℝ} (hm : 0 < m)
    (V : (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hcov : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ),
      IsSpinLift L S T → ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -m ^ 2 → 0 < p 0 →
        0 < (L *ᵥ p) 0 → ∀ μ, S * V (L *ᵥ p) μ * T = vecAct L (V p) μ)
    (hsharp : ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -m ^ 2 → 0 < p 0 → ∀ μ,
      sharp (V p μ) = V p μ) :
    ∃ c : ℝ, ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -m ^ 2 → 0 < p 0 → ∀ (μ : Fin 4)
      (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((m : ℂ) • u) →
      w ᵥ* Dirac.slash p = -((m : ℂ) • w) →
      w ⬝ᵥ (V p μ *ᵥ u) = (c : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) := by
  obtain ⟨c, hc⟩ := exists_sandwich_eq_of_cov hm V hcov
  have him : c.im = 0 := im_eq_zero_of_sharp (hsharp _ (dot_restVec m) hm 0)
    fun u w hu hw => hc _ (dot_restVec m) hm 0 u w hu hw
  have hre : ((c.re : ℝ) : ℂ) = c := Complex.ext (by simp) (by simp [him])
  exact ⟨c.re, by rw [hre]; exact hc⟩

end QED.GradedProof.V5Zero.Dirac

end
