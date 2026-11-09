/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.VertexEnergyFirst
import QED.OneLoop.VertexSpatial
import QED.Integration.LoopBounds
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform estimates for the one-loop vertex off the mass shell

The proof of the frozen theorem (E), `QED.OneLoop.vertexLimit_existsUnique`, in
`QED.OneLoop.VertexEnergyFirst` uses the on-shell premises only through the lower bound
`feynmanMass_pos` on the Feynman mass term `D_M = feynmanMass m M x y p' p` over the unit square.
This module redoes the estimates of that proof under the hypothesis `c₀ ≤ D_M` on the unit
square, for both regulator masses `M ∈ {m_γ, Λ}`, with constants that depend only on `c₀` and on a
bound `R` for the momenta. It does not assume that `p'` and `p` are on shell.

## Main statements

* `exists_norm_vertexNumerator_le_uniform`: quadratic growth of the numerator, uniformly for
  momenta in a ball.
* `norm_timeT_sub_le_of_massW_ge`: the pointwise Pauli–Villars bound, given a quadratic lower
  bound on both mass terms `massW`.
* `exists_norm_timeT_sub_le_uniform`, `exists_norm_spatialG_le_uniform`: the `(1 + ‖v‖)⁻⁵` bounds,
  for all `ε ≥ 0`, uniformly over momenta in a ball with `c₀ ≤ D_M` on the unit square.
* `tendsto_energyFirstIntegral_of_feynmanMass_ge`: under `c₀ ≤ D_M`, the energy-first integral
  converges as `ε → 0⁺` to `∫ v, spatialG 0 v`; `integrable_spatialG_of_feynmanMass_ge` gives the
  integrability of the outer stage at every `ε > 0`.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexOffShell

open QED.OneLoop.VertexLimit

/-! ### Uniform growth of the numerator -/

section Growth

/-! The growth bound uses the `ℓ∞` operator norm on matrices, which is submultiplicative. -/

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem norm_apply_le_norm (A : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (f := fun j => ‖A i j‖₊) (fun _ _ => zero_le)
      (Finset.mem_univ j)).trans
        (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i))
  exact_mod_cast h

private theorem norm_lower_le (ℓ : Fin 4 → ℝ) (κ : Fin 4) : ‖Minkowski.lower ℓ κ‖ ≤ ‖ℓ‖ := by
  have h := norm_le_pi_norm ℓ
  rw [Minkowski.lower_eq]
  fin_cases κ
  · simpa using h 0
  · simpa using h 1
  · simpa using h 2
  · simpa using h 3

private theorem norm_slash_le (ℓ : Fin 4 → ℝ) :
    ‖Dirac.slash ℓ‖ ≤ (∑ κ, ‖Dirac.gamma κ‖) * ‖ℓ‖ := by
  rw [Dirac.slash, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => ?_)
  rw [norm_smul, Complex.norm_real, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_lower_le ℓ κ) (norm_nonneg _)

private theorem norm_vertexForm_le (μ : Fin 4) (X Y : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    ‖vertexForm μ X Y i j‖ ≤
      (∑ ν, ∑ ρ, ‖((Minkowski.metric ν ρ : ℝ) : ℂ)‖ *
        (‖Dirac.gamma ρ‖ * ‖Dirac.gamma μ‖ * ‖Dirac.gamma ν‖)) * (‖X‖ * ‖Y‖) := by
  rw [vertexForm, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ _ => ?_)
  have hM : ‖(Dirac.gamma ρ * X * Dirac.gamma μ * Y * Dirac.gamma ν) i j‖ ≤
      ‖Dirac.gamma ρ‖ * ‖X‖ * ‖Dirac.gamma μ‖ * ‖Y‖ * ‖Dirac.gamma ν‖ := by
    refine (norm_apply_le_norm _ i j).trans ?_
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact norm_mul_le _ _
  calc ‖((Minkowski.metric ν ρ : ℝ) : ℂ) *
        (Dirac.gamma ρ * X * Dirac.gamma μ * Y * Dirac.gamma ν) i j‖
      ≤ ‖((Minkowski.metric ν ρ : ℝ) : ℂ)‖ *
        (‖Dirac.gamma ρ‖ * ‖X‖ * ‖Dirac.gamma μ‖ * ‖Y‖ * ‖Dirac.gamma ν‖) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hM (norm_nonneg _)
    _ = _ := by ring

/-- `‖m - (q + ℓ)̸‖ ≤ B (1 + ‖ℓ‖)` uniformly for `‖q‖ ≤ R`, with `B = ‖m‖ + G |R| + G`. -/
private theorem norm_mass_sub_slash_le_uniform (m R : ℝ) {q : Fin 4 → ℝ} (hq : ‖q‖ ≤ R)
    (ℓ : Fin 4 → ℝ) :
    ‖(m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - Dirac.slash (q + ℓ)‖ ≤
      (‖(m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)‖ + (∑ κ, ‖Dirac.gamma κ‖) * |R|
        + ∑ κ, ‖Dirac.gamma κ‖) * (1 + ‖ℓ‖) := by
  set G := ∑ κ, ‖Dirac.gamma κ‖
  set a := ‖(m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)‖
  have hG : 0 ≤ G := Finset.sum_nonneg fun κ _ => norm_nonneg _
  have ha : 0 ≤ a := norm_nonneg _
  have h1 := norm_slash_le (q + ℓ)
  have h2 : ‖q + ℓ‖ ≤ |R| + ‖ℓ‖ := (norm_add_le _ _).trans (by linarith [le_abs_self R])
  have h3 : G * ‖q + ℓ‖ ≤ G * (|R| + ‖ℓ‖) := mul_le_mul_of_nonneg_left h2 hG
  have h4 : 0 ≤ (a + G * |R|) * ‖ℓ‖ := by positivity
  refine (norm_sub_le _ _).trans ?_
  nlinarith

/-- Quadratic growth of the numerator, uniformly for momenta in the ball of radius `R`. -/
theorem exists_norm_vertexNumerator_le_uniform (m : ℝ) (μ i j : Fin 4) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p' p ℓ : Fin 4 → ℝ, ‖p'‖ ≤ R → ‖p‖ ≤ R →
      ‖vertexNumerator m p' p μ ℓ i j‖ ≤ C * (1 + ‖ℓ‖) ^ 2 := by
  set K := ∑ ν, ∑ ρ, ‖((Minkowski.metric ν ρ : ℝ) : ℂ)‖ *
    (‖Dirac.gamma ρ‖ * ‖Dirac.gamma μ‖ * ‖Dirac.gamma ν‖)
  set B := ‖(m : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)‖ + (∑ κ, ‖Dirac.gamma κ‖) * |R|
    + ∑ κ, ‖Dirac.gamma κ‖
  have hK : 0 ≤ K := Finset.sum_nonneg fun ν _ => Finset.sum_nonneg fun ρ _ =>
    mul_nonneg (norm_nonneg _) (by positivity)
  have hG : 0 ≤ ∑ κ, ‖Dirac.gamma κ‖ := Finset.sum_nonneg fun κ _ => norm_nonneg _
  have hB : 0 ≤ B := by positivity
  refine ⟨K * (B * B), by positivity, fun p' p ℓ hp' hp => ?_⟩
  rw [vertexNumerator_eq_vertexForm]
  refine (norm_vertexForm_le μ _ _ i j).trans ?_
  rw [mul_assoc, sq, mul_mul_mul_comm]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (norm_mass_sub_slash_le_uniform m R hp' ℓ)
    (norm_mass_sub_slash_le_uniform m R hp ℓ) (norm_nonneg _) (by positivity)) hK

end Growth

/-! ### The pointwise Pauli–Villars bound -/

/-- The Pauli–Villars difference of the closed-form energy integrals at one point `(z, v)`,
given quadratic lower bounds on both mass terms and a quadratic bound on the numerator. This is
the pointwise content of `QED.OneLoop.VertexLimit.norm_timeT_sub_le`, with the on-shell
premises replaced by the hypotheses they were used to derive. -/
theorem norm_timeT_sub_le_of_massW_ge {m mγ Λ ε : ℝ} (hε : 0 < ε) {p' p : Fin 4 → ℝ}
    (μ i j : Fin 4) {z : ℝ × ℝ} (hz : z.2 ∈ Icc (0 : ℝ) 1) {v : Fin 3 → ℝ} {c1 CN : ℝ}
    (hc1 : 0 < c1) (hWγ : c1 * (1 + ‖v‖) ^ 2 ≤ massW m mγ p' p z v)
    (hWΛ : c1 * (1 + ‖v‖) ^ 2 ≤ massW m Λ p' p z v)
    (hN : ‖vertexNumerator m p' p μ (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) i j‖
      ≤ CN * (1 + ‖v‖) ^ 2) :
    ‖timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v‖
      ≤ (π / 8 * ‖alphaN m p' p μ i j‖ * (3 / 2 * (mγ ^ 2 + Λ ^ 2) * c1 ^ (-(3 / 2 + 1 : ℝ)))
        + 3 * π / 8 * CN * (5 / 2 * (mγ ^ 2 + Λ ^ 2) * c1 ^ (-(5 / 2 + 1 : ℝ))))
        * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  set u : ℝ := 1 + ‖v‖ with hu_def
  have hu1 : 1 ≤ u := by simp only [u]; linarith [norm_nonneg v]
  have hu0 : 0 ≤ u := by linarith
  set Wγ : ℝ := massW m mγ p' p z v
  set WΛ : ℝ := massW m Λ p' p z v
  set α : ℂ := alphaN m p' p μ i j
  set L : ℝ := mγ ^ 2 + Λ ^ 2
  set N : ℂ := vertexNumerator m p' p μ (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) i j
  have hpos : 0 < c1 * u ^ 2 := by positivity
  have hCN : 0 ≤ CN := by
    have h0 : 0 ≤ CN * u ^ 2 := (norm_nonneg _).trans hN
    by_contra hC
    have h1 : 0 < u ^ 2 := by positivity
    nlinarith [not_le.mp hC]
  have hWγ0 : 0 < Wγ := hpos.trans_le hWγ
  have hWΛ0 : 0 < WΛ := hpos.trans_le hWΛ
  have hmin : c1 * u ^ 2 ≤ min Wγ WΛ := le_min hWγ hWΛ
  have hΔ : |Wγ - WΛ| ≤ L := by
    have h : Wγ - WΛ = (1 - z.2) * (mγ ^ 2 - Λ ^ 2) := by
      simp only [Wγ, WΛ, massW]
      rw [← feynmanMass_sub m mγ Λ z.1 z.2 p' p]
      ring
    have hy0 : 0 ≤ 1 - z.2 := by linarith [hz.2]
    have hy1 : 1 - z.2 ≤ 1 := by linarith [hz.1]
    rw [h, abs_mul, abs_of_nonneg hy0]
    have : |mγ ^ 2 - Λ ^ 2| ≤ L := by
      simp only [L]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg mγ, sq_nonneg Λ]
    nlinarith [abs_nonneg (mγ ^ 2 - Λ ^ 2)]
  have hs32 : (-(((3 / 2 : ℝ)) : ℂ)) = -(3 / 2 : ℂ) := by push_cast; ring
  have hs52 : (-(((5 / 2 : ℝ)) : ℂ)) = -(5 / 2 : ℂ) := by push_cast; ring
  have l1 := norm_cpow_sub_cpow_le (s := 3 / 2) hWγ0 hWΛ0 hε (by norm_num)
  have l2 := norm_cpow_sub_cpow_le (s := 5 / 2) hWγ0 hWΛ0 hε (by norm_num)
  rw [hs32] at l1
  rw [hs52] at l2
  have r1 : (min Wγ WΛ) ^ (-(3 / 2 + 1 : ℝ)) ≤ c1 ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)) := by
    calc (min Wγ WΛ) ^ (-(3 / 2 + 1 : ℝ)) ≤ (c1 * u ^ 2) ^ (-(3 / 2 + 1 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hpos hmin (by norm_num)
      _ = c1 ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)) := by
          rw [rpow_mul_sq_neg hc1.le hu0]; norm_num
  have r2 : (min Wγ WΛ) ^ (-(5 / 2 + 1 : ℝ)) ≤ c1 ^ (-(5 / 2 + 1 : ℝ)) * u ^ (-(7 : ℝ)) := by
    calc (min Wγ WΛ) ^ (-(5 / 2 + 1 : ℝ)) ≤ (c1 * u ^ 2) ^ (-(5 / 2 + 1 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hpos hmin (by norm_num)
      _ = c1 ^ (-(5 / 2 + 1 : ℝ)) * u ^ (-(7 : ℝ)) := by
          rw [rpow_mul_sq_neg hc1.le hu0]; norm_num
  have hu5 : u ^ 2 * u ^ (-(7 : ℝ)) = u ^ (-(5 : ℝ)) := by
    rw [← Real.rpow_natCast u 2, ← Real.rpow_add (by linarith)]
    norm_num
  have hsplit : timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v
      = -((π / 8 : ℂ) * α * ((-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
          - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))))
        - (3 * π / 8 : ℂ) * N
          * ((-(Wγ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ))) := by
    simp only [timeT, Wγ, WΛ, α, N]
    ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_mul, norm_ofReal_div_eight_pi,
    norm_ofReal_three_div_eight_pi]
  have t1 : π / 8 * ‖α‖ * ‖(-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
        - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))‖
      ≤ π / 8 * ‖α‖ * (3 / 2 * L * c1 ^ (-(3 / 2 + 1 : ℝ))) * u ^ (-(5 : ℝ)) := by
    calc π / 8 * ‖α‖ * ‖(-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
          - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))‖
        ≤ π / 8 * ‖α‖ * (3 / 2 * |Wγ - WΛ| * (min Wγ WΛ) ^ (-(3 / 2 + 1 : ℝ))) := by
          gcongr
      _ ≤ π / 8 * ‖α‖ * (3 / 2 * L * (c1 ^ (-(3 / 2 + 1 : ℝ)) * u ^ (-(5 : ℝ)))) := by
          gcongr
      _ = π / 8 * ‖α‖ * (3 / 2 * L * c1 ^ (-(3 / 2 + 1 : ℝ))) * u ^ (-(5 : ℝ)) := by ring
  have t2 : 3 * π / 8 * ‖N‖
        * ‖(-(Wγ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ))‖
      ≤ 3 * π / 8 * CN * (5 / 2 * L * c1 ^ (-(5 / 2 + 1 : ℝ))) * u ^ (-(5 : ℝ)) := by
    calc 3 * π / 8 * ‖N‖
          * ‖(-(Wγ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ))‖
        ≤ 3 * π / 8 * (CN * u ^ 2)
          * (5 / 2 * |Wγ - WΛ| * (min Wγ WΛ) ^ (-(5 / 2 + 1 : ℝ))) := by
          gcongr
      _ ≤ 3 * π / 8 * (CN * u ^ 2)
          * (5 / 2 * L * (c1 ^ (-(5 / 2 + 1 : ℝ)) * u ^ (-(7 : ℝ)))) := by
          gcongr
      _ = 3 * π / 8 * CN * (5 / 2 * L * c1 ^ (-(5 / 2 + 1 : ℝ)))
          * (u ^ 2 * u ^ (-(7 : ℝ))) := by ring
      _ = 3 * π / 8 * CN * (5 / 2 * L * c1 ^ (-(5 / 2 + 1 : ℝ))) * u ^ (-(5 : ℝ)) := by
          rw [hu5]
  calc π / 8 * ‖α‖ * ‖(-(Wγ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))
          - (-(WΛ : ℂ) + ε * I) ^ (-(3 / 2 : ℂ))‖
        + 3 * π / 8 * ‖N‖
          * ‖(-(Wγ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ)) - (-(WΛ : ℂ) + ε * I) ^ (-(5 / 2 : ℂ))‖
      ≤ π / 8 * ‖α‖ * (3 / 2 * L * c1 ^ (-(3 / 2 + 1 : ℝ))) * u ^ (-(5 : ℝ))
        + 3 * π / 8 * CN * (5 / 2 * L * c1 ^ (-(5 / 2 + 1 : ℝ))) * u ^ (-(5 : ℝ)) :=
        add_le_add t1 t2
    _ = _ := by ring

/-! ### Uniform bounds under a lower bound on the Feynman mass -/

/-- A lower bound on the Feynman mass term makes `massW` positive. -/
theorem massW_pos_of_le {m M c0 : ℝ} (hc0 : 0 < c0) {p' p : Fin 4 → ℝ} {z : ℝ × ℝ}
    (hD : c0 ≤ feynmanMass m M z.1 z.2 p' p) (v : Fin 3 → ℝ) : 0 < massW m M p' p z v := by
  have h3 : 0 ≤ ∑ k : Fin 3, (v k + shiftK p' p z k.succ) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  simp only [massW]
  linarith

/-- The Pauli–Villars difference of the closed-form energy integrals decays like `(1 + ‖v‖)⁻⁵`,
for every `ε ≥ 0`, uniformly over the Feynman parameters and over the momenta `p', p` in the ball
of radius `R` whose Feynman mass terms are at least `c₀` on the unit square. -/
theorem exists_norm_timeT_sub_le_uniform (m mγ Λ : ℝ) (μ i j : Fin 4) {c0 : ℝ} (hc0 : 0 < c0)
    (R : ℝ) :
    ∃ Cb : ℝ, ∀ p' p : Fin 4 → ℝ, ‖p'‖ ≤ R → ‖p‖ ≤ R →
      (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, c0 ≤ feynmanMass m mγ z.1 z.2 p' p) →
      (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, c0 ≤ feynmanMass m Λ z.1 z.2 p' p) →
      ∀ ε : ℝ, 0 ≤ ε → ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
        ‖timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v‖
          ≤ Cb * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  obtain ⟨CN, -, hCN⟩ := exists_norm_vertexNumerator_le_uniform m μ i j R
  obtain ⟨c1, hc1, hcoer⟩ := exists_mul_one_add_norm_sq_le (n := 3) (2 * R) hc0
  refine ⟨π / 8 * ‖vertexForm μ (Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ))
        (Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ)) i j‖
        * (3 / 2 * (mγ ^ 2 + Λ ^ 2) * c1 ^ (-(3 / 2 + 1 : ℝ)))
      + 3 * π / 8 * (CN * (1 + 2 * R) ^ 2) * (5 / 2 * (mγ ^ 2 + Λ ^ 2) * c1 ^ (-(5 / 2 + 1 : ℝ))),
    fun p' p hp' hp hDγ hDΛ ε hε z hz v => ?_⟩
  have hA : ‖p'‖ + ‖p‖ ≤ 2 * R := by linarith
  have hR : 0 ≤ R := (norm_nonneg _).trans hp'
  have hK : ‖shiftK p' p z‖ ≤ 2 * R := (norm_shiftK_le p' p hz).trans hA
  have hb : ‖(fun k : Fin 3 => shiftK p' p z k.succ)‖ ≤ 2 * R :=
    (pi_norm_le_iff_of_nonneg (by linarith)).2 fun k =>
      (norm_le_pi_norm (shiftK p' p z) k.succ).trans hK
  have hWγ : c1 * (1 + ‖v‖) ^ 2 ≤ massW m mγ p' p z v := hcoer v _ _ hb (hDγ z hz)
  have hWΛ : c1 * (1 + ‖v‖) ^ 2 ≤ massW m Λ p' p z v := hcoer v _ _ hb (hDΛ z hz)
  have hN : ‖vertexNumerator m p' p μ (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) i j‖
      ≤ CN * (1 + 2 * R) ^ 2 * (1 + ‖v‖) ^ 2 := by
    refine (hCN p' p _ hp' hp).trans ?_
    have hCN0 : 0 ≤ CN := by
      have h0 := (norm_nonneg _).trans (hCN p' p 0 hp' hp)
      have h1 : 0 < (1 + ‖(0 : Fin 4 → ℝ)‖) ^ 2 := by positivity
      by_contra hC
      nlinarith [not_le.mp hC]
    have ha : |-shiftK p' p z 0| ≤ 2 * R := by
      rw [abs_neg]
      exact (Real.norm_eq_abs _ ▸ norm_le_pi_norm (shiftK p' p z) 0).trans hK
    have h1 := norm_finCons_le (-shiftK p' p z 0) v
    have h2 : 1 + ‖(Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖ ≤ (1 + 2 * R) * (1 + ‖v‖) := by
      nlinarith [norm_nonneg v]
    calc CN * (1 + ‖(Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖) ^ 2
        ≤ CN * ((1 + 2 * R) * (1 + ‖v‖)) ^ 2 := by gcongr
      _ = CN * (1 + 2 * R) ^ 2 * (1 + ‖v‖) ^ 2 := by ring
  have hpt : ∀ ε' : ℝ, 0 < ε' →
      ‖timeT m mγ ε' p' p μ i j z v - timeT m Λ ε' p' p μ i j z v‖
        ≤ (π / 8 * ‖vertexForm μ (Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ))
            (Dirac.slash (Fin.cons 1 0 : Fin 4 → ℝ)) i j‖
            * (3 / 2 * (mγ ^ 2 + Λ ^ 2) * c1 ^ (-(3 / 2 + 1 : ℝ)))
          + 3 * π / 8 * (CN * (1 + 2 * R) ^ 2)
            * (5 / 2 * (mγ ^ 2 + Λ ^ 2) * c1 ^ (-(5 / 2 + 1 : ℝ)))) * (1 + ‖v‖) ^ (-(5 : ℝ)) :=
    fun ε' hε' => by
      have h := norm_timeT_sub_le_of_massW_ge hε' μ i j hz.2 hc1 hWγ hWΛ hN
      rwa [alphaN_eq] at h
  rcases hε.lt_or_eq with hε | rfl
  · exact hpt ε hε
  · have hpos : 0 < c1 * (1 + ‖v‖) ^ 2 := by positivity
    have hlim := ((tendsto_timeT μ i j (hpos.trans_le hWγ)).sub
      (tendsto_timeT μ i j (hpos.trans_le hWΛ))).norm
    exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall hpt)

/-- The uniform `(1 + ‖v‖)⁻⁵` bound on the energy integral `spatialG`, for every `ε ≥ 0`. -/
theorem exists_norm_spatialG_le_uniform (e m mγ Λ : ℝ) (μ i j : Fin 4) {c0 : ℝ} (hc0 : 0 < c0)
    (R : ℝ) :
    ∃ C : ℝ, ∀ p' p : Fin 4 → ℝ, ‖p'‖ ≤ R → ‖p‖ ≤ R →
      (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, c0 ≤ feynmanMass m mγ z.1 z.2 p' p) →
      (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, c0 ≤ feynmanMass m Λ z.1 z.2 p' p) →
      ∀ ε : ℝ, 0 ≤ ε → ∀ v : Fin 3 → ℝ,
        ‖spatialG e m mγ Λ ε p' p μ i j v‖ ≤ C * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  obtain ⟨Cb, hCb⟩ := exists_norm_timeT_sub_le_uniform m mγ Λ μ i j hc0 R
  refine ⟨‖kappa e‖ * 2 * Cb * feynmanMeasure.real univ,
    fun p' p hp' hp hDγ hDΛ ε hε v => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := feynmanMeasure)
    (f := fun z => kappa e * (2 * (z.2 : ℂ)) *
      (timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v))
    (C := ‖kappa e‖ * 2 * (Cb * (1 + ‖v‖) ^ (-(5 : ℝ))))
    (ae_feynmanMeasure.mono fun z hz => by
      have hzI := Ioc_prod_subset hz
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hz.2.1]
      calc ‖kappa e‖ * (2 * z.2) *
            ‖timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v‖
          ≤ ‖kappa e‖ * (2 * 1) * (Cb * (1 + ‖v‖) ^ (-(5 : ℝ))) := by
            gcongr
            · exact hz.2.2
            · exact hCb p' p hp' hp hDγ hDΛ ε hε z hzI v
        _ = ‖kappa e‖ * 2 * (Cb * (1 + ‖v‖) ^ (-(5 : ℝ))) := by ring)
  refine h.trans (le_of_eq ?_)
  ring

/-! ### The limit `ε → 0⁺` under a lower bound on the Feynman mass -/

section Limit

variable {e m mγ Λ c0 : ℝ} {p' p : Fin 4 → ℝ}

theorem tendsto_spatialG_of_feynmanMass_ge (hc0 : 0 < c0)
    (hDγ : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, c0 ≤ feynmanMass m mγ z.1 z.2 p' p)
    (hDΛ : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, c0 ≤ feynmanMass m Λ z.1 z.2 p' p)
    (μ i j : Fin 4) (v : Fin 3 → ℝ) :
    Tendsto (fun ε : ℝ => spatialG e m mγ Λ ε p' p μ i j v) (𝓝[>] 0)
      (𝓝 (spatialG e m mγ Λ 0 p' p μ i j v)) := by
  obtain ⟨Cb, hCb'⟩ := exists_norm_timeT_sub_le_uniform m mγ Λ μ i j hc0 (‖p'‖ + ‖p‖)
  have hCb := hCb' p' p (by linarith [norm_nonneg p]) (by linarith [norm_nonneg p']) hDγ hDΛ
  have hz0 : ((0 : ℝ), (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    simp
  have hCb0 : 0 ≤ Cb := by
    have h := hCb 1 zero_le_one _ hz0 v
    have hu : 0 < (1 + ‖v‖) ^ (-(5 : ℝ)) := by positivity
    by_contra hC
    nlinarith [norm_nonneg (timeT m mγ 1 p' p μ i j (0, 0) v - timeT m Λ 1 p' p μ i j (0, 0) v),
      not_le.mp hC]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖kappa e‖ * 2 * Cb) ?_ ?_
    (integrable_const _) ?_
  · refine eventually_nhdsWithin_of_forall fun ε hε => ?_
    have h1 := continuous_timeT hε m mγ p' p μ i j v
    have h2 := continuous_timeT hε m Λ p' p μ i j v
    exact (by fun_prop : Continuous fun z : ℝ × ℝ => kappa e * (2 * (z.2 : ℂ)) *
      (timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v)).aestronglyMeasurable
  · refine eventually_nhdsWithin_of_forall fun ε hε => ae_feynmanMeasure.mono fun z hz => ?_
    have hzI := Ioc_prod_subset hz
    have hb := hCb ε (le_of_lt hε) z hzI v
    have hu : (1 + ‖v‖) ^ (-(5 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg v]) (by norm_num)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hz.2.1]
    calc ‖kappa e‖ * (2 * z.2) *
          ‖timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v‖
        ≤ ‖kappa e‖ * (2 * 1) * (Cb * 1) := by
          gcongr
          · exact hz.2.2
          · exact hb.trans (mul_le_mul_of_nonneg_left hu hCb0)
      _ = ‖kappa e‖ * 2 * Cb := by ring
  · refine ae_feynmanMeasure.mono fun z hz => ?_
    have hzI := Ioc_prod_subset hz
    exact ((tendsto_timeT μ i j (massW_pos_of_le hc0 (hDγ z hzI) v)).sub
      (tendsto_timeT μ i j (massW_pos_of_le hc0 (hDΛ z hzI) v))).const_mul _

/-- Under a lower bound on the Feynman mass, the outer (spatial) stage of the energy-first
integral is integrable at every `ε > 0`. -/
theorem integrable_spatialG_of_feynmanMass_ge (hc0 : 0 < c0)
    (hDγ : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, c0 ≤ feynmanMass m mγ z.1 z.2 p' p)
    (hDΛ : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, c0 ≤ feynmanMass m Λ z.1 z.2 p' p)
    (μ i j : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    Integrable (spatialG e m mγ Λ ε p' p μ i j) := by
  obtain ⟨C, hC⟩ := exists_norm_spatialG_le_uniform e m mγ Λ μ i j hc0 (‖p'‖ + ‖p‖)
  have h := integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5) (by simp; norm_num)
  exact (h.const_mul C).mono' (aestronglyMeasurable_spatialG hε e m mγ Λ p' p μ i j)
    (Eventually.of_forall fun v => hC p' p (by linarith [norm_nonneg p])
      (by linarith [norm_nonneg p']) hDγ hDΛ ε hε.le v)

/-- Under a lower bound on the Feynman mass, the energy-first integral of each entry of the
integrand converges, as `ε → 0⁺`, to `∫ v, spatialG 0 v`. No on-shell premise is used. -/
theorem tendsto_energyFirstIntegral_of_feynmanMass_ge (hc0 : 0 < c0)
    (hDγ : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, c0 ≤ feynmanMass m mγ z.1 z.2 p' p)
    (hDΛ : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, c0 ≤ feynmanMass m Λ z.1 z.2 p' p)
    (μ i j : Fin 4) :
    Tendsto (fun ε : ℝ => energyFirstIntegral fun ℓ => vertexIntegrand e m mγ Λ ε p' p μ ℓ i j)
      (𝓝[>] 0) (𝓝 (∫ v, spatialG e m mγ Λ 0 p' p μ i j v)) := by
  obtain ⟨C, hC'⟩ := exists_norm_spatialG_le_uniform e m mγ Λ μ i j hc0 (‖p'‖ + ‖p‖)
  have hC := hC' p' p (by linarith [norm_nonneg p]) (by linarith [norm_nonneg p']) hDγ hDΛ
  have hbnd := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul C
  have hlim : Tendsto (fun ε : ℝ => ∫ v, spatialG e m mγ Λ ε p' p μ i j v) (𝓝[>] 0)
      (𝓝 (∫ v, spatialG e m mγ Λ 0 p' p μ i j v)) :=
    tendsto_integral_filter_of_dominated_convergence _
      (eventually_nhdsWithin_of_forall fun ε hε =>
        aestronglyMeasurable_spatialG hε e m mγ Λ p' p μ i j)
      (eventually_nhdsWithin_of_forall fun ε hε => Eventually.of_forall (hC ε (le_of_lt hε)))
      hbnd
      (Eventually.of_forall fun v => tendsto_spatialG_of_feynmanMass_ge hc0 hDγ hDΛ μ i j v)
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  exact (energyFirstIntegral_eq_integral_spatialG hε e m mγ Λ p' p μ i j).symm

end Limit

end QED.OneLoop.VertexOffShell

end
