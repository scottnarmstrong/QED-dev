/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.V5ZeroDiracRest
public import QED.TwoLoop.LimitCovarianceLorentz
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# A covariant vertex at `p' = p` is a multiple of `γ^μ` on shell

Helper level for the order-`e⁵` vertex at `q = 0` (`QED.GradedProof.GEx2.VertexZeroInput`). Let
`V p` be a vertex at `p' = p` for on-shell `p` (`p² = -m²`, `p⁰ > 0`), covariant in the sense of
`QED.TwoLoop.PauliZero.conj_vertexLimit_map` at `p' = p`:
`S V(L p)^μ T = L^μ_ν V(p)^ν` for every spinor lift `(S, T)` of `L` keeping `p` and `L p` of
positive energy. Then one `c` gives `w V(p)^μ u = c · w γ^μ u` for every on-shell `p` and all
on-shell `u, w` (`exists_sandwich_eq_of_cov`; reflections suffice,
`exists_sandwich_eq_of_reflect_cov`).

* `sandwichEq_transfer`: a sandwich identity at `q` for all `ν` transfers along a spinor lift of
  `L` with `L q = p`;
* at the rest momentum `p₀` the reflections in spatial vectors fix `p₀`
  (`QED.GradedProof.V5Zero.Dirac.sandwichEq_restVec`);
* every other on-shell `p` is `R_K p₀` for the reflection in the spacelike `K = p - p₀`.
-/

@[expose] public section

open Matrix Complex

namespace QED.GradedProof.V5Zero.Dirac

open QED.Dirac QED.TwoLoop.LimitCovariance

/-- `w (L V)^μ v = L^μ_ν · w V^ν v`. -/
theorem dotProduct_vecAct_mulVec (w v : Fin 4 → ℂ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    w ⬝ᵥ (vecAct L W μ *ᵥ v) = ∑ ν, ((L μ ν : ℝ) : ℂ) * (w ⬝ᵥ (W ν *ᵥ v)) := by
  simp only [vecAct, sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **Transfer along a spinor lift.** If `(S, T)` lifts `L`, `L q = p`, `S X^μ T = L^μ_ν W^ν`,
and `w W^ν u = c · w γ^ν u` between on-shell spinors at `q` for every `ν`, then
`w X^μ u = c · w γ^μ u` between on-shell spinors at `p`. -/
theorem sandwichEq_transfer {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsSpinLift L S T) {m : ℝ} {q p : Fin 4 → ℝ} (hqp : L *ᵥ q = p)
    {X W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ} (hX : ∀ μ, S * X μ * T = vecAct L W μ) {c : ℂ}
    (hW : ∀ ν, SandwichEq m q (W ν) c (gamma ν)) (μ : Fin 4) :
    SandwichEq m p (X μ) c (gamma μ) := by
  intro u w hu hw
  have hsl : S * slash p * T = slash q := by rw [← hqp]; exact h.mul_slash_mul q
  have hTS := h.mul_eq_one'
  have hS : slash q * S = S * slash p := by
    rw [← hsl, Matrix.mul_assoc, hTS, Matrix.mul_one]
  have hT : T * slash q = slash p * T := by
    rw [← hsl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hTS, Matrix.one_mul]
  have hu' := onShell_mulVec hS hu
  have hw' := onShell_vecMul hT hw
  have back : ∀ Y : Matrix (Fin 4) (Fin 4) ℂ, T * (S * Y * T) * S = Y := fun Y => by
    simp only [← Matrix.mul_assoc, hTS, Matrix.one_mul]
    rw [Matrix.mul_assoc, hTS, Matrix.mul_one]
  have e : ∀ Y : Matrix (Fin 4) (Fin 4) ℂ,
      w ⬝ᵥ (Y *ᵥ u) = (w ᵥ* T) ⬝ᵥ ((S * Y * T) *ᵥ (S *ᵥ u)) := fun Y => by
    rw [dotProduct_conj, back]
  rw [e (X μ), e (gamma μ), hX, h.mul_gamma_mul, dotProduct_vecAct_mulVec]
  have hg : ∑ ν, ((L μ ν : ℝ) : ℂ) • gamma ν = vecAct L gamma μ := rfl
  rw [hg, dotProduct_vecAct_mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [hW ν _ _ hu' hw']
  ring

/-- The spinor lift of the reflection in `K`. -/
theorem isSpinLift_reflSpin {K : Fin 4 → ℝ} (hK : Minkowski.dot K K ≠ 0) :
    IsSpinLift (reflectMatrix K) (reflSpin K) (((Minkowski.dot K K : ℝ) : ℂ)⁻¹ • reflSpin K) :=
  ⟨reflSpin_mul_inv hK, isCovariantUnder_reflect_gamma hK⟩

/-- **A reflection-covariant vertex at `p' = p` is `c γ^μ` on shell.** Covariance is required
only under the reflections `R_K` (with the lift `(K̸Γ, K̸Γ/(K·K))`). -/
theorem exists_sandwich_eq_of_reflect_cov {m : ℝ} (hm : 0 < m)
    (V : (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hcov : ∀ K : Fin 4 → ℝ, Minkowski.dot K K ≠ 0 → ∀ p : Fin 4 → ℝ,
      Minkowski.dot p p = -m ^ 2 → 0 < p 0 → 0 < (reflectMatrix K *ᵥ p) 0 → ∀ μ,
        reflSpin K * V (reflectMatrix K *ᵥ p) μ * (((Minkowski.dot K K : ℝ) : ℂ)⁻¹ • reflSpin K) =
          vecAct (reflectMatrix K) (V p) μ) :
    ∃ c : ℂ, ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -m ^ 2 → 0 < p 0 → ∀ (μ : Fin 4)
      (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((m : ℂ) • u) →
      w ᵥ* Dirac.slash p = -((m : ℂ) • w) →
      w ⬝ᵥ (V p μ *ᵥ u) = c * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) := by
  set p₀ := restVec m with hp₀
  have hm0 : m ≠ 0 := hm.ne'
  have hp₀0 : 0 < p₀ 0 := hm
  have hrest : ∀ μ, SandwichEq m p₀ (V p₀ μ) (V p₀ 0 3 3 + V p₀ 0 3 1) (gamma μ) := by
    refine sandwichEq_restVec hm0 fun n hn hn0 μ => ?_
    have hfix : reflectMatrix n *ᵥ p₀ = p₀ := by
      rw [reflectMatrix_mulVec]
      exact reflect_of_dot_eq_zero (by simp [Minkowski.dot_eq, hp₀, restVec, hn0])
    have := hcov n hn p₀ (dot_restVec m) hp₀0 (by rw [hfix]; exact hp₀0) μ
    rwa [hfix] at this
  refine ⟨V p₀ 0 3 3 + V p₀ 0 3 1, fun p hp hp0 μ u w hu hw => ?_⟩
  set a : Fin 4 → ℝ := p - p₀ with ha
  have hpc : -(p 0 * p 0) + p 1 * p 1 + p 2 * p 2 + p 3 * p 3 = -m ^ 2 := by
    rw [← Minkowski.dot_eq]; exact hp
  have haa : Minkowski.dot a a = 2 * m * (p 0 - m) := by
    simp only [ha, hp₀, restVec, Minkowski.dot_eq, Pi.sub_apply]
    simp
    linear_combination hpc
  by_cases h0 : Minkowski.dot a a = 0
  · have e0 : p 0 = m := by
      rw [haa] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (by linarith : m = 0) hm0
      · linarith
    rw [e0] at hpc
    have e1 : p 1 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
    have e2 : p 2 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
    have e3 : p 3 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
    have hpp : p = p₀ := by
      funext i
      fin_cases i <;> simp [hp₀, restVec, e0, e1, e2, e3]
    subst hpp
    exact hrest μ u w hu hw
  · have hap : 2 * Minkowski.dot a p₀ / Minkowski.dot a a = -1 := by
      rw [div_eq_iff h0, haa]
      simp only [ha, hp₀, restVec, Minkowski.dot_eq, Pi.sub_apply]
      simp
      ring
    have hRp : reflectMatrix a *ᵥ p₀ = p := by
      rw [reflectMatrix_mulVec, reflect, hap, ha]
      funext i
      simp
    have hX : ∀ ν, reflSpin a * V p ν * (((Minkowski.dot a a : ℝ) : ℂ)⁻¹ • reflSpin a) =
        vecAct (reflectMatrix a) (V p₀) ν := fun ν => by
      have := hcov a h0 p₀ (dot_restVec m) hp₀0 (by rw [hRp]; exact hp0) ν
      rwa [hRp] at this
    exact sandwichEq_transfer (isSpinLift_reflSpin h0) hRp hX hrest μ u w hu hw

/-- **A covariant vertex at `p' = p` is `c γ^μ` on shell**, with the covariance hypothesis in the
form given by `QED.TwoLoop.PauliZero.conj_vertexLimit_map` at `p' = p`. -/
theorem exists_sandwich_eq_of_cov {m : ℝ} (hm : 0 < m)
    (V : (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hcov : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ),
      IsSpinLift L S T → ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -m ^ 2 → 0 < p 0 →
        0 < (L *ᵥ p) 0 → ∀ μ, S * V (L *ᵥ p) μ * T = vecAct L (V p) μ) :
    ∃ c : ℂ, ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -m ^ 2 → 0 < p 0 → ∀ (μ : Fin 4)
      (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((m : ℂ) • u) →
      w ᵥ* Dirac.slash p = -((m : ℂ) • w) →
      w ⬝ᵥ (V p μ *ᵥ u) = c * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) :=
  exists_sandwich_eq_of_reflect_cov hm V fun _ hK =>
    hcov _ _ _ (isSpinLift_reflSpin hK)

end QED.GradedProof.V5Zero.Dirac

end
