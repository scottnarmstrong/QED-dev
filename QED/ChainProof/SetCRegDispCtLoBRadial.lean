/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBEngine
public import QED.ChainProof.SetCRegDispShellSEQuad
import QED.ChainProof.SetCRegDispShellSECov
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The spatial integral of the doubled vertex at zero prescription

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), first step of the
value of the doubled vertex (layer 5 of the plan in `QED/ChainProof/SetCRegDispCtLoBEngine.lean`).
The `ε → 0⁺` limits of the doubled vertex are spatial integrals of the closed-form energy integral
`QED.TwoLoop.VPHalfAtLimit.timeP` of order `n = i + 1` at zero prescription, which contains
`(-W)^{-(i+5/2)}` and `(-W)^{-(i+7/2)}`, `W = |v⃗ + K⃗|² + Δ`, `Δ = feynmanMass > 0`. For a
numerator that is quadratic in the spatial loop momentum after the translation
`v⃗ ↦ v⃗ - K⃗`, `N((-K⁰, w⃗ - K⃗)) = N₀ + Σₖ Lₖ wₖ + Σₖₗ Qₖₗ wₖ wₗ`, the odd and mixed moments
vanish, the diagonal second moments are a third of the radial one, and the radial integrals of
`QED/ChainProof/SetCRegDispShellSERad.lean` give

`∫ timeP(0) d³v = (-1)^{i+4} [α (K_{i+3} - K_{i+4}) e^{-iπ(i+5/2)} 4π c_i Δ^{-(i+1)}`
`  + K_{i+4} e^{-iπ(i+7/2)} (N₀ 4π c_{i+1} Δ^{-(i+2)} + ⅓ (Σₖ Qₖₖ) 4π (c_i - c_{i+1}) Δ^{-(i+1)})]`

(`K` = `QED.TwoLoop.VPHalfAtLimit.energyConst`, `c_i` = `QED.ChainProof.SetCRegDispSE.seRadC`).

* `massW_sub_shiftK`: the translation;
* `dblTimeY`, **`integral_timeP_zero`**: the closed form above;
* `energyConst_one`, `energyConst_three`, `energyConst_four`; **`dblTimeY_zero`**: at order one
  (`i = 0`, the doubled vertex with one photon denominator) the closed form is
  `i (π²/12) (Σₖ Qₖₖ - α)/Δ + i (π²/6) N₀/Δ²`;
* **`integral_spatialW_zero`**: with a weight `w` on the Feynman square, the spatial integral of
  `spatialW w` at zero prescriptions is the Feynman-parameter integral of `w · dblTimeY`, when
  `Δ > 0` and the quadratic decomposition hold on the open square.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.TwoLoop.VPHalfAtLimit
open QED.ChainProof.SetCRegDispSE (seRadC neg_ofReal_cpow_neg integral_sum_sq_add_rpow_half
  integral_sum_sq_mul_sum_sq_add_rpow_half)
open QED.ChainProof.SetCRegDisp (integrable_coord_mul_rpow integrable_coord_mul_coord_mul_rpow
  integral_coord_mul_coord_mul_rpow)

/-- The spatial part `K⃗` of the Feynman shift. -/
noncomputable def shiftKs (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) : Fin 3 → ℝ :=
  fun k => shiftK p' p z k.succ

theorem massW_sub_shiftK (m M : ℝ) (p' p : Fin 4 → ℝ) (z : ℝ × ℝ) (w : Fin 3 → ℝ) :
    massW m M p' p z (w - shiftKs p' p z) = ∑ k, w k ^ 2 + feynmanMass m M z.1 z.2 p' p := by
  simp [massW, shiftKs]

/-- The closed form of the spatial integral of `timeP` of order `i + 1` at zero prescription, for
the quadratic data `(N₀, Q)` and the leading energy coefficient `α`. -/
noncomputable def dblTimeY (α N₀ : ℂ) (Q : Fin 3 → Fin 3 → ℂ) (i : ℕ) (Δ : ℝ) : ℂ :=
  (-1) ^ (i + 4) *
    (α * ((energyConst (i + 3) - energyConst (i + 4) : ℝ) : ℂ) *
        (exp (π * I * (-(((i : ℝ) + 5 / 2 : ℝ) : ℂ))) *
          ((4 * π * (seRadC i * Δ ^ (-((i : ℝ) + 1))) : ℝ) : ℂ)) +
      ((energyConst (i + 4) : ℝ) : ℂ) * exp (π * I * (-(((i : ℝ) + 7 / 2 : ℝ) : ℂ))) *
        (N₀ * ((4 * π * (seRadC (i + 1) * Δ ^ (-((i : ℝ) + 2))) : ℝ) : ℂ) +
          (∑ k, Q k k) *
            ((4 * π * ((seRadC i - seRadC (i + 1)) * Δ ^ (-((i : ℝ) + 1))) / 3 : ℝ) : ℂ)))

/-- **The spatial integral of `timeP` of order `i + 1` at zero prescription**, for a numerator
quadratic in the translated spatial momentum. -/
theorem integral_timeP_zero (α : ℂ) {N : (Fin 4 → ℝ) → ℂ} (m M : ℝ) (i : ℕ)
    (p' p : Fin 4 → ℝ) {z : ℝ × ℝ} (hΔ : 0 < feynmanMass m M z.1 z.2 p' p) (N₀ : ℂ)
    (L : Fin 3 → ℂ) (Q : Fin 3 → Fin 3 → ℂ)
    (hN : ∀ w : Fin 3 → ℝ, N (Fin.cons (-shiftK p' p z 0) (w - shiftKs p' p z) : Fin 4 → ℝ) =
      N₀ + ∑ k, (w k : ℂ) * L k + ∑ k, ∑ l, ((w k * w l : ℝ) : ℂ) * Q k l) :
    ∫ v, timeP α N m M (i + 1) 0 p' p z v =
      dblTimeY α N₀ Q i (feynmanMass m M z.1 z.2 p' p) := by
  set Δ := feynmanMass m M z.1 z.2 p' p with hΔdef
  set a : Fin 3 → ℝ := shiftKs p' p z
  set s₁ : ℝ := (i : ℝ) + 5 / 2
  set s₂ : ℝ := (i : ℝ) + 7 / 2
  set K₃ : ℂ := (-1) ^ (i + 4) * ((energyConst (i + 3) - energyConst (i + 4) : ℝ) : ℂ)
  set K₄ : ℂ := (-1) ^ (i + 4) * ((energyConst (i + 4) : ℝ) : ℂ)
  set ph₁ : ℂ := exp (π * I * (-((s₁ : ℝ) : ℂ)))
  set ph₂ : ℂ := exp (π * I * (-((s₂ : ℝ) : ℂ)))
  have hs₁ : ((i + 1 : ℕ) : ℝ) + 3 / 2 = s₁ := by push_cast; simp only [s₁]; ring
  have hs₂ : ((i + 1 : ℕ) : ℝ) + 5 / 2 = s₂ := by push_cast; simp only [s₂]; ring
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hpt : ∀ v : Fin 3 → ℝ, timeP α N m M (i + 1) 0 p' p z (v - a) =
      K₃ * ph₁ * α * (((∑ k, v k ^ 2 + Δ) ^ (-s₁) : ℝ) : ℂ) +
        (K₄ * ph₂ * N₀ * (((∑ k, v k ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) +
          (∑ k, K₄ * ph₂ * L k * ((v k * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) +
            ∑ k, ∑ l, K₄ * ph₂ * Q k l *
              ((v k * v l * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ))) := by
    intro v
    have hX : 0 < ∑ k, v k ^ 2 + Δ := by positivity
    simp only [timeP]
    rw [massW_sub_shiftK, ← hΔdef, hs₁, hs₂, hN v]
    simp only [ofReal_zero, zero_mul, add_zero]
    rw [neg_ofReal_cpow_neg hX s₁, neg_ofReal_cpow_neg hX s₂]
    simp only [K₃, K₄, ph₁, ph₂]
    push_cast
    rw [show i + 1 + 3 = i + 4 by ring, show i + 1 + 2 = i + 3 by ring]
    simp only [Fin.sum_univ_three]
    ring
  have hint1 : Integrable fun v : Fin 3 → ℝ => (((∑ k, v k ^ 2 + Δ) ^ (-s₁) : ℝ) : ℂ) :=
    (integrable_sum_sq_add_rpow hΔ (by simp only [s₁]; linarith)).ofReal
  have hint2 : Integrable fun v : Fin 3 → ℝ => (((∑ k, v k ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) :=
    (integrable_sum_sq_add_rpow hΔ (by simp only [s₂]; linarith)).ofReal
  have hint3 : ∀ k : Fin 3, Integrable fun v : Fin 3 → ℝ =>
      ((v k * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) := fun k =>
    (integrable_coord_mul_rpow hΔ (by simp only [s₂]; linarith) k).ofReal
  have hint4 : ∀ k l : Fin 3, Integrable fun v : Fin 3 → ℝ =>
      ((v k * v l * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) := fun k l =>
    (integrable_coord_mul_coord_mul_rpow hΔ (by simp only [s₂]; linarith) k l).ofReal
  have hodd : ∀ k : Fin 3,
      ∫ v : Fin 3 → ℝ, ((v k * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) = 0 := by
    intro k
    rw [integral_complex_ofReal]
    have h := integral_coord_smul_radial (fun x : ℝ => (x + Δ) ^ (-s₂)) k
    simp only [smul_eq_mul] at h
    rw [h, ofReal_zero]
  have hrad : ∫ v : Fin 3 → ℝ, (∑ j, v j ^ 2) * (∑ j, v j ^ 2 + Δ) ^ (-s₂) =
      4 * π * ((seRadC i - seRadC (i + 1)) * Δ ^ (-((i : ℝ) + 1))) :=
    integral_sum_sq_mul_sum_sq_add_rpow_half hΔ i
  have hsec : ∀ k l : Fin 3,
      ∫ v : Fin 3 → ℝ, ((v k * v l * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) =
        if k = l then ((4 * π * ((seRadC i - seRadC (i + 1)) * Δ ^ (-((i : ℝ) + 1))) / 3 : ℝ) :
          ℂ) else 0 := by
    intro k l
    rw [integral_complex_ofReal,
      integral_coord_mul_coord_mul_rpow hΔ (by simp only [s₂]; linarith) k l, hrad]
    split_ifs <;> push_cast <;> ring
  have hF2 : ∫ v : Fin 3 → ℝ, (((∑ k, v k ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) =
      ((4 * π * (seRadC (i + 1) * Δ ^ (-((i : ℝ) + 2)))) : ℝ) := by
    rw [integral_complex_ofReal]
    have h := integral_sum_sq_add_rpow_half hΔ (i + 1)
    have e1 : (((i + 1 : ℕ) : ℝ) + 5 / 2) = s₂ := by push_cast; simp only [s₂]; ring
    have e2 : (((i + 1 : ℕ) : ℝ) + 1) = (i : ℝ) + 2 := by push_cast; ring
    rw [e1, e2] at h
    rw [h]
  have hF1 : ∫ v : Fin 3 → ℝ, (((∑ k, v k ^ 2 + Δ) ^ (-s₁) : ℝ) : ℂ) =
      ((4 * π * (seRadC i * Δ ^ (-((i : ℝ) + 1)))) : ℝ) := by
    rw [integral_complex_ofReal, integral_sum_sq_add_rpow_half hΔ i]
  have hS3 : Integrable fun v : Fin 3 → ℝ =>
      ∑ k, K₄ * ph₂ * L k * ((v k * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) :=
    integrable_finsetSum _ fun k _ => (hint3 k).const_mul _
  have hS4 : Integrable fun v : Fin 3 → ℝ =>
      ∑ k, ∑ l, K₄ * ph₂ * Q k l * ((v k * v l * (∑ j, v j ^ 2 + Δ) ^ (-s₂) : ℝ) : ℂ) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hint4 k l).const_mul _
  rw [← integral_sub_right_eq_self _ a]
  simp_rw [hpt]
  rw [integral_add (hint1.const_mul _) ?h1, integral_add (hint2.const_mul _) ?h2,
    integral_add hS3 hS4,
    integral_finsetSum _ fun k _ => (hint3 k).const_mul _,
    integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hint4 k l).const_mul _]
  simp_rw [integral_finsetSum _ fun l _ => (hint4 _ l).const_mul _]
  simp only [integral_const_mul, hodd, hsec, hF1, hF2, mul_zero, Finset.sum_const_zero,
    mul_ite, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [dblTimeY, K₃, K₄, ph₁, ph₂, s₁, s₂, Fin.sum_univ_three]
  · push_cast
    ring
  all_goals first
    | exact hS3.add hS4
    | exact (hint2.const_mul _).add (hS3.add hS4)

/-! ### Order one -/

theorem energyConst_one : energyConst 1 = π := by
  unfold energyConst
  simp

theorem energyConst_three : energyConst 3 = 3 * π / 8 := by
  have h2 := QED.ChainProof.SetCRegDisp.energyConst_succ_succ 0
  have h3 := QED.ChainProof.SetCRegDisp.energyConst_succ_succ 1
  norm_num [energyConst_one] at h2 h3
  rw [h3, h2]
  ring

theorem energyConst_four : energyConst 4 = 5 * π / 16 := by
  have h4 := QED.ChainProof.SetCRegDisp.energyConst_succ_succ 2
  norm_num [energyConst_three] at h4
  rw [h4]
  ring

theorem exp_neg_five_halves_pi_I : exp (π * I * (-(((0 : ℕ) : ℝ) + 5 / 2 : ℝ) : ℂ)) = -I := by
  have e : (π : ℂ) * I * (-(((0 : ℕ) : ℝ) + 5 / 2 : ℝ) : ℂ) =
      -((π / 2 : ℝ) : ℂ) * I + (-1 : ℤ) * (2 * π * I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, neg_mul,
    Complex.exp_neg, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

theorem exp_neg_seven_halves_pi_I : exp (π * I * (-(((0 : ℕ) : ℝ) + 7 / 2 : ℝ) : ℂ)) = I := by
  have e : (π : ℂ) * I * (-(((0 : ℕ) : ℝ) + 7 / 2 : ℝ) : ℂ) =
      ((π / 2 : ℝ) : ℂ) * I + (-2 : ℤ) * (2 * π * I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- **The closed form at order one**: `i (π²/12) (Σₖ Qₖₖ - α)/Δ + i (π²/6) N₀/Δ²`. -/
theorem dblTimeY_zero (α N₀ : ℂ) (Q : Fin 3 → Fin 3 → ℂ) {Δ : ℝ} (hΔ : 0 < Δ) :
    dblTimeY α N₀ Q 0 Δ = I * ((π ^ 2 / 12 : ℝ) : ℂ) * ((∑ k, Q k k) - α) / (Δ : ℂ) +
      I * ((π ^ 2 / 6 : ℝ) : ℂ) * N₀ / (Δ : ℂ) ^ 2 := by
  have h1 : Δ ^ (-(((0 : ℕ) : ℝ) + 1)) = Δ⁻¹ := by simp [Real.rpow_neg_one]
  have h2 : Δ ^ (-(((0 : ℕ) : ℝ) + 2)) = (Δ ^ 2)⁻¹ := by
    rw [show -(((0 : ℕ) : ℝ) + 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hΔ.le,
      Real.rpow_natCast]
  have hD : (Δ : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ.ne'
  unfold dblTimeY
  rw [exp_neg_five_halves_pi_I, exp_neg_seven_halves_pi_I, h1, h2]
  simp only [zero_add, energyConst_three, energyConst_four, seRadC]
  push_cast
  field_simp
  ring

/-- **The spatial integral of `spatialW w` at zero prescriptions**: the Feynman-parameter integral
of `w · dblTimeY`, when the Feynman mass is positive and the numerator is quadratic in the
translated spatial momentum on the open square. -/
theorem integral_spatialW_zero {w : ℝ × ℝ → ℂ} (hw : Continuous w) {Cw : ℝ}
    (hwb : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖w z‖ ≤ Cw) {m M₀ : ℝ} (hm : 0 < m)
    (hM₀ : 0 < M₀) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (α : ℂ) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {M : ℝ} (hM : M₀ ≤ M) (i : ℕ)
    (N₀ : ℝ × ℝ → ℂ) (L : ℝ × ℝ → Fin 3 → ℂ) (Q : ℝ × ℝ → Fin 3 → Fin 3 → ℂ)
    (hΔ : ∀ z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1, 0 < feynmanMass m M z.1 z.2 p' p)
    (hN : ∀ z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1, ∀ w' : Fin 3 → ℝ,
      N (Fin.cons (-shiftK p' p z 0) (w' - shiftKs p' p z) : Fin 4 → ℝ) =
        N₀ z + ∑ k, (w' k : ℂ) * L z k + ∑ k, ∑ l, ((w' k * w' l : ℝ) : ℂ) * Q z k l) :
    ∫ v, spatialW w α N m M (i + 1) 0 0 p' p v =
      ∫ z, w z * dblTimeY α (N₀ z) (Q z) i (feynmanMass m M z.1 z.2 p' p) ∂feynmanMeasure := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb (n := i + 1)
    (by omega)
  have hCw : 0 ≤ Cw := (norm_nonneg _).trans (hwb (1, 1) ⟨⟨zero_le_one, le_rfl⟩,
    ⟨zero_le_one, le_rfl⟩⟩)
  set f : (Fin 3 → ℝ) × (ℝ × ℝ) → ℂ := fun q =>
    w q.2 * timeP α N m M (i + 1) (effEps 0 0 q.2) p' p q.2 q.1
  have hfm : Measurable f := measurable_timeW hw hNc α m M (i + 1) 0 0 p' p
  have hint : Integrable f ((volume : Measure (Fin 3 → ℝ)).prod feynmanMeasure) := by
    have hb := ((integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
      (by simp; norm_num)).const_mul (Cw * C)).mul_prod (integrable_const (1 : ℝ))
      (ν := feynmanMeasure)
    refine hb.mono' hfm.aestronglyMeasurable ?_
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin 3 → ℝ)))
      (ν := feynmanMeasure)).ae ae_feynmanMeasure
    filter_upwards [h2] with q hq
    have hz := Ioc_prod_subset hq
    rw [mul_one, norm_mul, mul_assoc]
    exact mul_le_mul (hwb _ hz) (hC M hM _ _ hz q.1) (norm_nonneg _) hCw
  unfold spatialW
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_feynmanMeasure.mono fun z hz => ?_)
  dsimp only
  have he : effEps 0 0 z = 0 := by simp [effEps]
  rw [he, integral_const_mul,
    integral_timeP_zero α m M i p' p (hΔ z hz) (N₀ z) (L z) (Q z) (hN z hz)]

end QED.ChainProof.CtLoB

end
