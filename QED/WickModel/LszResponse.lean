/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsLSZResponseMagneticMoment
public import QED.Frozen.OneLoop.IsResponseMagneticMoment
import QED.Algebra.BreitFrame
import QED.OneLoop.MagneticResponse
import QED.WickModel.LszClosedForm
import QED.WickModel.LszPhotonLeg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The LSZ response magnetic moment is the response magnetic moment (R₀)

By the closed form (`QED.WickModel.LszClosedForm.lszAmplitude_eq_closedForm`), the LSZ amplitude
`M²_{++}(p', p)` differs from the vertex sandwich `ū₊(p') V²(p', p) u₊(p)` at `Z₁ = 1 + δ₁` by the
photon-leg term `e q_B² D(q_B²) Π(q_B²) ū₊(p') γ² u₊(p)`, with
`D(s) = 1/(s + m_γ²) - 1/(s + Λ²)`. In the Breit frame `q_B² = q²` and `ū₊(p') γ² u₊(p) = i q`,
`|q² D(q²)| ≤ q² (1/m_γ² + 1/Λ²)`, and `Π = -δ₃ + Π_loop` is bounded on `[0, 1]`, since `Π_loop`
is continuous there. So the difference is at most `C q³` for `0 < q ≤ 1`, which is `o(q)`, and
the two little-o conditions (L₅) and (R₀) are equivalent.

## Main statements

* `QED.WickModel.LszResponse.exists_norm_lszAmplitude_sub_le`: the bound `C q³`.
* `QED.WickModel.LszResponse.isResponseMagneticMoment_of_isLSZ`: (L₅) implies (R₀).
* `QED.WickModel.LszResponse.isLSZ_of_isResponseMagneticMoment`: (R₀) implies (L₅).
* `QED.WickModel.LszResponse.isLSZResponseMagneticMoment_iff`: (L₅) holds if and only if (R₀)
  holds at `Z₁ = 1 + δ₁`.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Set

namespace QED.WickModel

/-- **The photon-leg term is `O(q³)` in the Breit frame.** There is `C ≥ 0` such that for
Breit-frame on-shell momenta with `0 < q ≤ 1` the LSZ amplitude `M²_{++}(p', p)` and the vertex
sandwich `ū₊(p') V²(p', p) u₊(p)` at `Z₁ = 1 + δ₁` differ by at most `C q³`. -/
theorem LszResponse.exists_norm_lszAmplitude_sub_le (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℝ) (p' p : Fin 4 → ℝ) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
      (hp : Minkowski.dot p p = -P.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0),
      0 < q → q ≤ 1 → p' 1 = q / 2 → p 1 = -(q / 2) → p' 2 = 0 → p 2 = 0 → p' 3 = 0 →
      p 3 = 0 →
      ‖lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 0 0 2
        - Dirac.bar (Dirac.spinor P.m p' 0) ⬝ᵥ
          (QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0'
            hp0 2 *ᵥ Dirac.spinor P.m p 0)‖ ≤ C * q ^ 3 := by
  -- `Π_loop` is bounded on `[0, 1]`.
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioi (-(4 * P.m ^ 2)) := fun s hs => by
    have : 0 < 4 * P.m ^ 2 := by positivity
    simp only [mem_Ioi]
    linarith [hs.1]
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuousOn_vacuumPolarizationLoop hm hM₁ hM₂).mono hsub)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, zero_le_one⟩)
  set D : ℝ := (P.mγ ^ 2)⁻¹ + (P.Λ ^ 2)⁻¹ with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨|P.e| * D * (|P.δ₃| + K), by positivity,
    fun q p' p hp' hp hp0' hp0 hq hq1 h1' h1 h2' h2 h3' h3 => ?_⟩
  have hd := QED.OneLoop.VertexLimit.breit_dot_sub hp' hp hp0' hp0 h1' h1 h2' h2 h3' h3
  rw [LszClosedForm.lszAmplitude_eq_vertex_add_photonLeg, add_sub_cancel_left,
    vacuumPolarization_eq_loop,
    Dirac.breit_bar_spinor_gamma_two_spinor hm hp' hp hp0' hp0 h1' h1 h2' h2 h3' h3]
  simp only [hd]
  -- The pole factor: `|q² D(q²)| ≤ q² (1/m_γ² + 1/Λ²)`.
  have hq2 : 0 ≤ q ^ 2 := by positivity
  have hγ : 0 < q ^ 2 + P.mγ ^ 2 := by positivity
  have hΛ2 : 0 < q ^ 2 + P.Λ ^ 2 := by positivity
  have hpole : |q ^ 2 * ((q ^ 2 + P.mγ ^ 2)⁻¹ - (q ^ 2 + P.Λ ^ 2)⁻¹)| ≤ q ^ 2 * D := by
    rw [abs_mul, abs_of_nonneg hq2]
    refine mul_le_mul_of_nonneg_left ?_ hq2
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos (inv_pos.mpr hγ), abs_of_pos (inv_pos.mpr hΛ2), hD]
    have : 0 < P.mγ ^ 2 := by positivity
    have : 0 < P.Λ ^ 2 := by positivity
    gcongr <;> linarith
  -- The vacuum polarization: `|Π(q²)| ≤ |δ₃| + K`.
  have hPi : ‖-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (q ^ 2) : ℂ)‖ ≤ |P.δ₃| + K := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs]
    have hs : q ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨hq2, by nlinarith⟩
    linarith [hK (q ^ 2) hs]
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, norm_I,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq]
  calc |P.e| * |q ^ 2 * ((q ^ 2 + P.mγ ^ 2)⁻¹ - (q ^ 2 + P.Λ ^ 2)⁻¹)|
        * ‖-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (q ^ 2) : ℂ)‖ * (1 * q)
      ≤ |P.e| * (q ^ 2 * D) * (|P.δ₃| + K) * (1 * q) := by gcongr
    _ = |P.e| * D * (|P.δ₃| + K) * q ^ 3 := by ring

/-- For `0 ≤ C`, `0 < q ≤ 1` and `q < η / (2 (C + 1))`: `C q³ ≤ (η / 2) q`. -/
theorem LszResponse.mul_cube_le {C η q : ℝ} (hC : 0 ≤ C) (hq : 0 < q) (hq1 : q ≤ 1)
    (hqη : q < η / (2 * (C + 1))) : C * q ^ 3 ≤ η / 2 * q := by
  have h1 : q ^ 2 ≤ q := by nlinarith
  have h2 : q * (2 * (C + 1)) < η := (lt_div_iff₀ (by positivity)).1 hqη
  have h3 : C * q ≤ η / 2 := by nlinarith
  have h4 : C * q ^ 2 ≤ η / 2 := (mul_le_mul_of_nonneg_left h1 hC).trans h3
  calc C * q ^ 3 = C * q ^ 2 * q := by ring
    _ ≤ η / 2 * q := mul_le_mul_of_nonneg_right h4 hq.le

/-- **(L₅) implies (R₀).** If `μ` is the LSZ response magnetic moment, it is the response
magnetic moment of the vertex function at `Z₁ = 1 + δ₁`. -/
theorem LszResponse.isResponseMagneticMoment_of_isLSZ (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (μ : ℝ)
    (h : IsLSZResponseMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ) :
    QED.OneLoop.IsResponseMagneticMoment P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ μ := by
  obtain ⟨C, hC0, hC⟩ :=
    LszResponse.exists_norm_lszAmplitude_sub_le P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon
  intro η hη
  obtain ⟨δ₁, hδ₁, hb⟩ := h (η / 2) (by positivity)
  refine ⟨min δ₁ (min 1 (η / (2 * (C + 1)))), by positivity,
    fun q p' p hp' hp hp0' hp0 hq hqδ h1' h1 h2' h2 h3' h3 => ?_⟩
  have hqδ₁ : q < δ₁ := hqδ.trans_le (min_le_left _ _)
  have hq1 : q < 1 := (hqδ.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hqη : q < η / (2 * (C + 1)) :=
    (hqδ.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hA := hb q p' p hp' hp hp0' hp0 hq hqδ₁ h1' h1 h2' h2 h3' h3
  have hB := (hC q p' p hp' hp hp0' hp0 hq hq1.le h1' h1 h2' h2 h3' h3).trans
    (LszResponse.mul_cube_le hC0 hq hq1.le hqη)
  set L := lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 0 0 2
  set V := Dirac.bar (Dirac.spinor P.m p' 0) ⬝ᵥ
    (QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0' hp0 2
      *ᵥ Dirac.spinor P.m p 0)
  calc ‖V - 2 * I * P.m * μ * q‖ = ‖(L - 2 * I * P.m * μ * q) - (L - V)‖ := by ring_nf
    _ ≤ ‖L - 2 * I * P.m * μ * q‖ + ‖L - V‖ := norm_sub_le _ _
    _ ≤ η / 2 * q + η / 2 * q := add_le_add hA hB
    _ = η * q := by ring

/-- **(R₀) implies (L₅).** If `μ` is the response magnetic moment of the vertex function at
`Z₁ = 1 + δ₁`, it is the LSZ response magnetic moment. -/
theorem LszResponse.isLSZ_of_isResponseMagneticMoment (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (μ : ℝ)
    (h : QED.OneLoop.IsResponseMagneticMoment P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ μ) :
    IsLSZResponseMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ := by
  obtain ⟨C, hC0, hC⟩ :=
    LszResponse.exists_norm_lszAmplitude_sub_le P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon
  intro η hη
  obtain ⟨δ₁, hδ₁, hb⟩ := h (η / 2) (by positivity)
  refine ⟨min δ₁ (min 1 (η / (2 * (C + 1)))), by positivity,
    fun q p' p hp' hp hp0' hp0 hq hqδ h1' h1 h2' h2 h3' h3 => ?_⟩
  have hqδ₁ : q < δ₁ := hqδ.trans_le (min_le_left _ _)
  have hq1 : q < 1 := (hqδ.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hqη : q < η / (2 * (C + 1)) :=
    (hqδ.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hA := hb q p' p hp' hp hp0' hp0 hq hqδ₁ h1' h1 h2' h2 h3' h3
  have hB := (hC q p' p hp' hp hp0' hp0 hq hq1.le h1' h1 h2' h2 h3' h3).trans
    (LszResponse.mul_cube_le hC0 hq hq1.le hqη)
  set L := lszAmplitude P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 0 0 2
  set V := Dirac.bar (Dirac.spinor P.m p' 0) ⬝ᵥ
    (QED.OneLoop.vertexFunction P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ p' p hp' hp hp0' hp0 2
      *ᵥ Dirac.spinor P.m p 0)
  calc ‖L - 2 * I * P.m * μ * q‖ = ‖(V - 2 * I * P.m * μ * q) + (L - V)‖ := by ring_nf
    _ ≤ ‖V - 2 * I * P.m * μ * q‖ + ‖L - V‖ := norm_add_le _ _
    _ ≤ η / 2 * q + η / 2 * q := add_le_add hA hB
    _ = η * q := by ring

/-- **(L₅) is (R₀).** A real `μ` is the LSZ response magnetic moment if and only if it is the
response magnetic moment of the vertex function at `Z₁ = 1 + δ₁`. -/
theorem LszResponse.isLSZResponseMagneticMoment_iff (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (μ : ℝ) :
    IsLSZResponseMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ ↔
      QED.OneLoop.IsResponseMagneticMoment P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ μ :=
  ⟨LszResponse.isResponseMagneticMoment_of_isLSZ P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ,
    LszResponse.isLSZ_of_isResponseMagneticMoment P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon μ⟩

end QED.WickModel

end
