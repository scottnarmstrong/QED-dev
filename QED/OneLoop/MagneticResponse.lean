/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.MagneticMoment
public import QED.OneLoop.ChargeCondition
public import QED.Algebra.BreitFrame
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Breit-frame magnetic response of the vertex function

For Breit-frame on-shell momenta along `x` and spin-up spinors, the `J²` matrix element of the
vertex function `QED.OneLoop.vertexFunction` is `i e q (Z₁ + A(q²) + B(q²))`
(`breit_sandwich_vertexFunction`). Its linear-in-`q` coefficient therefore has the limit
`2 i m μ₀` with `μ₀ = e (Z₁ + A(0) + B(0)) / (2m)` (`magneticMu_spec`). This coefficient is unique
(`eq_of_magnetic_spec`), because Breit momenta exist for every `q` (`exists_breit`).

These are internal helpers for the response definition of the magnetic moment (author ruling
D-9).
-/

@[expose] public section

open Matrix Complex
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexLimit

/-- The Pauli coefficient at `q² = 0`. -/
noncomputable def pauliB0 (e m mγ Λ : ℝ) : ℝ :=
  e ^ 2 / (8 * π ^ 2) * ∫ z, pauliIntegrand m (mγ, Λ, 0) z ∂feynmanMeasure

/-- The response magnetic moment `μ₀ = e (Z₁ + A(0) + B(0)) / (2m)`. -/
noncomputable def magneticMu (e Z₁ m mγ Λ : ℝ) : ℝ :=
  e * (Z₁ + chargeA0 e m mγ Λ + pauliB0 e m mγ Λ) / (2 * m)

theorem breit_dot_sub {m q : ℝ} {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (h1' : p' 1 = q / 2)
    (h1 : p 1 = -(q / 2)) (h2' : p' 2 = 0) (h2 : p 2 = 0) (h3' : p' 3 = 0) (h3 : p 3 = 0) :
    Minkowski.dot (p' - p) (p' - p) = q ^ 2 := by
  have hE := (Dirac.breit_energy hp' hp hp0' hp0 h1' h1 h2' h2 h3' h3).1
  rw [Minkowski.dot_eq]
  simp only [Pi.sub_apply, hE, h1', h1, h2', h2, h3', h3]
  ring

/-- The Breit-frame `J²` matrix element of the vertex function, spin up. -/
theorem breit_sandwich_vertexFunction {e Z₁ m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {q : ℝ} {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2)
    (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (h1' : p' 1 = q / 2)
    (h1 : p 1 = -(q / 2)) (h2' : p' 2 = 0) (h2 : p 2 = 0) (h3' : p' 3 = 0) (h3 : p 3 = 0) :
    Dirac.bar (Dirac.spinor m p' 0) ⬝ᵥ
        (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 2 *ᵥ Dirac.spinor m p 0)
      = I * e * q * ((Z₁ + formFactorA e m mγ Λ p' p + formFactorB e m mγ Λ p' p : ℝ) : ℂ) := by
  have hu := Dirac.slash_mulVec_spinor m p hp 0
  have hw := Dirac.bar_vecMul_slash m p' _ (Dirac.slash_mulVec_spinor m p' hp' 0)
  have hg := Dirac.breit_bar_spinor_gamma_two_spinor hm hp' hp hp0' hp0 h1' h1 h2' h2 h3' h3
  have hS := Dirac.breit_bar_spinor_lorentzGen_two_spinor hm hp' hp hp0' hp0 h1' h1 h2' h2 h3' h3
  have hloop := sandwich_vertexLimit (e := e) hm hmγ hΛ hp' hp hp0' hp0 2 hu hw
  rw [← vertexOneLoop_eq_limit hm hmγ hΛ hp' hp hp0' hp0 2] at hloop
  simp only [vertexFunction, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, hloop, Matrix.sub_mulVec, dotProduct_sub, hg, hS]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp
  ring

/-- Breit momenta along `x` exist for every `q`. -/
theorem exists_breit {m : ℝ} (hm : 0 < m) (q : ℝ) :
    ∃ p' p : Fin 4 → ℝ, Minkowski.dot p' p' = -m ^ 2 ∧ Minkowski.dot p p = -m ^ 2 ∧
      0 < p' 0 ∧ 0 < p 0 ∧ p' 1 = q / 2 ∧ p 1 = -(q / 2) ∧ p' 2 = 0 ∧ p 2 = 0 ∧ p' 3 = 0 ∧
      p 3 = 0 := by
  set E := Real.sqrt (m ^ 2 + q ^ 2 / 4)
  have hE : 0 < E := Real.sqrt_pos.2 (by positivity)
  have hE2 : E ^ 2 = m ^ 2 + q ^ 2 / 4 := Real.sq_sqrt (by positivity)
  refine ⟨![E, q / 2, 0, 0], ![E, -(q / 2), 0, 0], ?_, ?_, by simpa using hE, by simpa using hE,
    by simp, by simp, by simp, by simp, by simp, by simp⟩
  · rw [Minkowski.dot_eq]; simp; nlinarith [hE2]
  · rw [Minkowski.dot_eq]; simp; nlinarith [hE2]

/-- The little-o characterization of the response magnetic moment holds for `magneticMu`. -/
theorem magneticMu_spec {e Z₁ m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    ∀ η > 0, ∃ δ > 0, ∀ (q : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2)
      (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
      0 < q → q < δ → p' 1 = q / 2 → p 1 = -(q / 2) → p' 2 = 0 → p 2 = 0 → p' 3 = 0 →
      p 3 = 0 →
      ‖Dirac.bar (Dirac.spinor m p' 0) ⬝ᵥ
          (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 2 *ᵥ Dirac.spinor m p 0)
        - 2 * I * m * magneticMu e Z₁ m mγ Λ * q‖ ≤ η * q := by
  intro η hη
  set cA : ℝ := |e| * (e ^ 2 / (16 * π ^ 2)) + 1
  set cB : ℝ := |e| * (e ^ 2 / (8 * π ^ 2)) + 1
  have hcA : 0 < cA := by positivity
  have hcB : 0 < cB := by positivity
  obtain ⟨δA, hδA, hA⟩ := exists_abs_integral_formIntegrandAq_sub_lt hm hmγ hΛ
    (η := η / (2 * cA)) (by positivity)
  obtain ⟨δB, hδB, hB⟩ := exists_abs_integral_pauliIntegrand_sub_lt hm hmγ hΛ
    (η := η / (2 * cB)) (by positivity)
  refine ⟨min 1 (min δA δB), by positivity, fun q p' p hp' hp hp0' hp0 hq hqδ h1' h1 h2' h2 h3'
    h3 => ?_⟩
  have hq1 : q < 1 := hqδ.trans_le (min_le_left _ _)
  have hq2 : q ^ 2 < min δA δB := by
    have : q ^ 2 ≤ q := by nlinarith
    exact this.trans_lt (hqδ.trans_le (min_le_right _ _))
  have hqA : q ^ 2 < δA := hq2.trans_le (min_le_left _ _)
  have hqB : q ^ 2 < δB := hq2.trans_le (min_le_right _ _)
  have hsq : 0 < q ^ 2 := by positivity
  have hd := breit_dot_sub hp' hp hp0' hp0 h1' h1 h2' h2 h3' h3
  rw [breit_sandwich_vertexFunction hm hmγ hΛ hp' hp hp0' hp0 h1' h1 h2' h2 h3' h3,
    formFactorA_eq_q hp' hp, formFactorB_eq hp' hp, hd]
  set IA := ∫ z, formIntegrandAq m mγ Λ (q ^ 2) z ∂feynmanMeasure
  set IA0 := ∫ z, formIntegrandAq m mγ Λ 0 z ∂feynmanMeasure
  set IB := ∫ z, pauliIntegrand m (mγ, Λ, q ^ 2) z ∂feynmanMeasure
  set IB0 := ∫ z, pauliIntegrand m (mγ, Λ, 0) z ∂feynmanMeasure
  have hdiff : I * e * q * ((Z₁ + e ^ 2 / (16 * π ^ 2) * IA + e ^ 2 / (8 * π ^ 2) * IB : ℝ) : ℂ)
      - 2 * I * m * magneticMu e Z₁ m mγ Λ * q
      = I * ((e * q * (e ^ 2 / (16 * π ^ 2) * (IA - IA0) + e ^ 2 / (8 * π ^ 2) * (IB - IB0)) : ℝ)
          : ℂ) := by
    simp only [magneticMu, chargeA0, pauliB0]
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
    ring
  rw [hdiff, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hbA := hA (q ^ 2) hsq hqA
  have hbB := hB (q ^ 2) hsq hqB
  calc |e * q * (e ^ 2 / (16 * π ^ 2) * (IA - IA0) + e ^ 2 / (8 * π ^ 2) * (IB - IB0))|
      ≤ |e| * q * ((e ^ 2 / (16 * π ^ 2)) * |IA - IA0| + (e ^ 2 / (8 * π ^ 2)) * |IB - IB0|) := by
        have ha : 0 ≤ e ^ 2 / (16 * π ^ 2) := by positivity
        have hb : 0 ≤ e ^ 2 / (8 * π ^ 2) := by positivity
        have hab : |e ^ 2 / (16 * π ^ 2) * (IA - IA0) + e ^ 2 / (8 * π ^ 2) * (IB - IB0)|
            ≤ e ^ 2 / (16 * π ^ 2) * |IA - IA0| + e ^ 2 / (8 * π ^ 2) * |IB - IB0| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        rw [abs_mul, abs_mul, abs_of_pos hq]
        exact mul_le_mul_of_nonneg_left hab (by positivity)
    _ ≤ q * (cA * (η / (2 * cA)) + cB * (η / (2 * cB))) := by
        have h1 : |e| * (e ^ 2 / (16 * π ^ 2) * |IA - IA0|) ≤ cA * (η / (2 * cA)) := by
          calc |e| * (e ^ 2 / (16 * π ^ 2) * |IA - IA0|)
              = (|e| * (e ^ 2 / (16 * π ^ 2))) * |IA - IA0| := by ring
            _ ≤ cA * (η / (2 * cA)) := by
                gcongr
                simp only [cA]; linarith
        have h2 : |e| * (e ^ 2 / (8 * π ^ 2) * |IB - IB0|) ≤ cB * (η / (2 * cB)) := by
          calc |e| * (e ^ 2 / (8 * π ^ 2) * |IB - IB0|)
              = (|e| * (e ^ 2 / (8 * π ^ 2))) * |IB - IB0| := by ring
            _ ≤ cB * (η / (2 * cB)) := by
                gcongr
                simp only [cB]; linarith
        nlinarith
    _ = η * q := by field_simp; ring

/-- Two coefficients satisfying the little-o characterization are equal. -/
theorem eq_of_magnetic_spec {e Z₁ m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {μ₁ μ₂ : ℝ}
    (h₁ : ∀ η > 0, ∃ δ > 0, ∀ (q : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2)
      (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
      0 < q → q < δ → p' 1 = q / 2 → p 1 = -(q / 2) → p' 2 = 0 → p 2 = 0 → p' 3 = 0 →
      p 3 = 0 →
      ‖Dirac.bar (Dirac.spinor m p' 0) ⬝ᵥ
          (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 2 *ᵥ Dirac.spinor m p 0)
        - 2 * I * m * μ₁ * q‖ ≤ η * q)
    (h₂ : ∀ η > 0, ∃ δ > 0, ∀ (q : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -m ^ 2)
      (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
      0 < q → q < δ → p' 1 = q / 2 → p 1 = -(q / 2) → p' 2 = 0 → p 2 = 0 → p' 3 = 0 →
      p 3 = 0 →
      ‖Dirac.bar (Dirac.spinor m p' 0) ⬝ᵥ
          (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 2 *ᵥ Dirac.spinor m p 0)
        - 2 * I * m * μ₂ * q‖ ≤ η * q) :
    μ₁ = μ₂ := by
  by_contra hne
  have hd : 0 < |μ₁ - μ₂| := abs_pos.2 (sub_ne_zero.2 hne)
  set η := m * |μ₁ - μ₂| / 2
  have hη : 0 < η := by positivity
  obtain ⟨δ₁, hδ₁, H₁⟩ := h₁ η hη
  obtain ⟨δ₂, hδ₂, H₂⟩ := h₂ η hη
  set q := min δ₁ δ₂ / 2
  have hq : 0 < q := by positivity
  have hq₁ : q < δ₁ := by simp only [q]; linarith [min_le_left δ₁ δ₂]
  have hq₂ : q < δ₂ := by simp only [q]; linarith [min_le_right δ₁ δ₂]
  obtain ⟨p', p, hp', hp, hp0', hp0, h1', h1, h2', h2, h3', h3⟩ := exists_breit hm q
  have b₁ := H₁ q p' p hp' hp hp0' hp0 hq hq₁ h1' h1 h2' h2 h3' h3
  have b₂ := H₂ q p' p hp' hp hp0' hp0 hq hq₂ h1' h1 h2' h2 h3' h3
  set M := Dirac.bar (Dirac.spinor m p' 0) ⬝ᵥ
    (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p' p hp' hp hp0' hp0 2 *ᵥ Dirac.spinor m p 0)
  have htri : ‖(2 * I * m * μ₂ * q : ℂ) - 2 * I * m * μ₁ * q‖ ≤ η * q + η * q := by
    calc ‖(2 * I * m * μ₂ * q : ℂ) - 2 * I * m * μ₁ * q‖
        = ‖(M - 2 * I * m * μ₁ * q) - (M - 2 * I * m * μ₂ * q)‖ := by ring_nf
      _ ≤ ‖M - 2 * I * m * μ₁ * q‖ + ‖M - 2 * I * m * μ₂ * q‖ := norm_sub_le _ _
      _ ≤ η * q + η * q := add_le_add b₁ b₂
  have heq : (2 * I * m * μ₂ * q : ℂ) - 2 * I * m * μ₁ * q
      = I * ((2 * m * q * (μ₂ - μ₁) : ℝ) : ℂ) := by push_cast; ring
  rw [heq, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_mul, abs_mul, abs_of_pos hm, abs_of_pos hq, abs_sub_comm] at htri
  have : |(2 : ℝ)| = 2 := abs_of_pos two_pos
  rw [this] at htri
  simp only [η] at htri
  have hpos := mul_pos (mul_pos hm hq) hd
  nlinarith [hpos, abs_sub_comm μ₁ μ₂]

end QED.OneLoop.VertexLimit

end
