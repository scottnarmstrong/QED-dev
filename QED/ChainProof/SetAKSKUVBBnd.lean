/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVBNode

/-!
# Set (a), stage D: the node bound of the `VB` photon-mass integral

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral of the `VB` class). The node
difference of the `VB` antiderivative (`ksUPsiB`) splits into a moment part, a logarithm and a
dilogarithm part (`ksU_ksUPsiB_sub`). In the coordinates `(ρ, β)` (slope `b₀ ≥ ρ kA/(1 - ρ)`,
`B = b₀ + Λ/ρ`) each part times `ρ` is bounded by a multiple of the integrable weight
`ksUg ρ = 1 + ρ^{-1/2} + (1 - ρ)^{-1/2}`.

Main results:

* `ksU_ksUPsiB_sub`: the node difference in parts;
* `ksU_wt_moment`, `ksU_wt_log`, `ksU_wt_K`: the three weight bounds.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace QED.ChainProof.SetAKS

/-- **The node difference of the `VB` antiderivative**, in parts. -/
theorem ksU_ksUPsiB_sub (A Y τ c : ℝ) (E H : Fin 3 → ℝ) (B b₀ : ℝ) :
    ksUPsiB A Y τ c E H B - ksUPsiB A Y τ c E H b₀ =
      τ⁻¹ * (ksUGc A E H 0 * (ksDJ1 A b₀ Y 0 - ksDJ1 A B Y 0) +
        ksUGc A E H 1 * (ksDJ1 A b₀ Y 1 - ksDJ1 A B Y 1) +
        ksUGc A E H 2 * (ksDJ1 A b₀ Y 2 - ksDJ1 A B Y 2)) +
      (2 * τ)⁻¹ * ksUPY Y H * (Real.log (A + B * Y) - Real.log (A + b₀ * Y)) +
      c * (ksUK (B * Y / A) - ksUK (b₀ * Y / A)) := by
  unfold ksUPsiB
  ring

/-- The moment weight: `(1 - ρ)⁻¹ J1ₚ(A, b₀, Y) ≤ 4 kA⁻¹ ksUg ρ` for `b₀ ≥ ρ kA/(1 - ρ)`. -/
theorem ksU_wt_moment {ρ kA A b₀ Y : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hkA : 0 < kA)
    (hkAA : kA ≤ A) (hb₀ : ρ * kA / (1 - ρ) ≤ b₀) (hY : 0 ≤ Y) (hY1 : Y ≤ 1) (p : ℕ) :
    (1 - ρ)⁻¹ * ksDJ1 A b₀ Y p ≤ 4 * kA⁻¹ * ksUg ρ := by
  obtain ⟨r0, r1⟩ := hρ
  have h1 : 0 < 1 - ρ := by linarith
  have hb₁ : 0 < ρ * kA / (1 - ρ) := by positivity
  have hJ := ksU_J1_le_ref hkA hkAA hb₁ hb₀ hY hY1 p
  have href : ksDJ1 kA (ρ * kA / (1 - ρ)) 1 0 = -Real.log (1 - ρ) * (1 - ρ) / (ρ * kA) := by
    simp only [ksDJ1]
    have : (kA + ρ * kA / (1 - ρ) * 1) / kA = (1 - ρ)⁻¹ := by field_simp; ring
    rw [this, Real.log_inv]
    field_simp
  rw [href] at hJ
  have hL : 0 ≤ -Real.log (1 - ρ) := by
    have := Real.log_nonpos h1.le (by linarith); linarith
  have hg := ksU_one_le_ksUg ⟨r0, r1⟩
  have hgr := (ksU_rpow_le_ksUg ⟨r0, r1⟩).2
  -- `-log(1 - ρ)/ρ ≤ 4 ksUg ρ`
  have key : -Real.log (1 - ρ) ≤ 4 * ρ * ksUg ρ := by
    rcases le_or_gt ρ (1 / 2) with h | h
    · have hl := Real.one_sub_inv_le_log_of_pos h1
      have : (1 - ρ)⁻¹ ≤ 2 := by rw [inv_le_comm₀ h1 two_pos]; linarith
      have e : 1 - (1 - ρ)⁻¹ = -(ρ * (1 - ρ)⁻¹) := by field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_left this r0.le]
    · have hl := ksU_abs_log_le h1 (by linarith)
      rw [abs_of_nonpos (by linarith)] at hl
      nlinarith
  have hJ' : (1 - ρ)⁻¹ * ksDJ1 A b₀ Y p ≤ (1 - ρ)⁻¹ * (-Real.log (1 - ρ) * (1 - ρ) / (ρ * kA)) :=
    mul_le_mul_of_nonneg_left hJ (inv_pos.2 h1).le
  refine hJ'.trans ?_
  have e : (1 - ρ)⁻¹ * (-Real.log (1 - ρ) * (1 - ρ) / (ρ * kA)) =
      -Real.log (1 - ρ) / ρ * kA⁻¹ := by field_simp
  rw [e]
  have : -Real.log (1 - ρ) / ρ ≤ 4 * ksUg ρ := by
    rw [div_le_iff₀ r0]; linarith
  have := inv_pos.2 hkA
  nlinarith

/-- The logarithm weight: `(1 - ρ)⁻¹ log(1 + (Λ/ρ)Y/(A + b₀Y)) ≤ 4 √(Λ/kA) ksUg ρ`. -/
theorem ksU_wt_log {ρ kA A b₀ Y Λ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hkA : 0 < kA)
    (hkAA : kA ≤ A) (hb₀ : ρ * kA / (1 - ρ) ≤ b₀) (hY : 0 ≤ Y) (hY1 : Y ≤ 1) (hΛ : 0 ≤ Λ) :
    (1 - ρ)⁻¹ * Real.log (1 + Λ / ρ * Y / (A + b₀ * Y)) ≤
      4 * Real.sqrt (Λ / kA) * ksUg ρ := by
  obtain ⟨r0, r1⟩ := hρ
  have h1 : 0 < 1 - ρ := by linarith
  have hA : 0 < A := hkA.trans_le hkAA
  have hb₁ : 0 < ρ * kA / (1 - ρ) := by positivity
  have hb0 : 0 < b₀ := hb₁.trans_le hb₀
  have hD : 0 < A + b₀ * Y := by positivity
  set z := Λ / ρ * Y / (A + b₀ * Y) with hz
  have hz0 : 0 ≤ z := by positivity
  have hlog := ksU_log_one_add_le hz0
  have hg := (ksU_rpow_le_ksUg ⟨r0, r1⟩)
  have hsq0 : 0 ≤ Real.sqrt (Λ / kA) := Real.sqrt_nonneg _
  rcases le_or_gt ρ (1 / 2) with h | h
  · have hzle : z ≤ Λ / kA / ρ := by
      rw [hz, div_le_div_iff₀ hD r0]
      have : kA * Y ≤ A + b₀ * Y := by nlinarith
      have : Λ / ρ * Y * ρ = Λ * Y := by field_simp
      rw [this]
      calc Λ * Y ≤ Λ * Y + Λ / kA * (A + b₀ * Y - kA * Y) := by
            have := div_nonneg hΛ hkA.le; nlinarith
        _ = Λ / kA * (A + b₀ * Y) := by field_simp; ring
    have hs := (Real.sqrt_le_sqrt hzle).trans (ksU_sqrt_le_mul_rpow (div_nonneg hΛ hkA.le) r0)
    have hi : (1 - ρ)⁻¹ ≤ 2 := by rw [inv_le_comm₀ h1 two_pos]; linarith
    have hl0 : 0 ≤ Real.log (1 + z) := Real.log_nonneg (by linarith)
    calc (1 - ρ)⁻¹ * Real.log (1 + z) ≤ 2 * (2 * (Real.sqrt (Λ / kA) * ρ ^ (-(1 / 2 : ℝ)))) := by
          refine mul_le_mul hi (hlog.trans (by linarith)) hl0 (by norm_num)
      _ ≤ 4 * Real.sqrt (Λ / kA) * ksUg ρ := by nlinarith [mul_le_mul_of_nonneg_left hg.1 hsq0]
  · have hzle : z / (1 - ρ) ^ 2 ≤ 4 * (Λ / kA) / (1 - ρ) := by
      have hzb : z ≤ Λ / ρ / b₀ := by
        rw [hz, div_le_div_iff₀ hD hb0]
        have := div_nonneg hΛ r0.le
        nlinarith [mul_nonneg this hY, mul_nonneg this hA.le]
      have hb0' : Λ / ρ / b₀ ≤ Λ / ρ / (ρ * kA / (1 - ρ)) :=
        div_le_div_of_nonneg_left (div_nonneg hΛ r0.le) hb₁ hb₀
      have e : Λ / ρ / (ρ * kA / (1 - ρ)) = Λ * (1 - ρ) / (ρ ^ 2 * kA) := by field_simp
      rw [e] at hb0'
      have hρ2 : 1 / 4 ≤ ρ ^ 2 := by nlinarith
      have : Λ * (1 - ρ) / (ρ ^ 2 * kA) ≤ 4 * (Λ / kA) * (1 - ρ) := by
        rw [div_le_iff₀ (by positivity)]
        have : 0 ≤ Λ * (1 - ρ) := mul_nonneg hΛ h1.le
        have e2 : 4 * (Λ / kA) * (1 - ρ) * (ρ ^ 2 * kA) = 4 * ρ ^ 2 * (Λ * (1 - ρ)) := by
          field_simp
        rw [e2]; nlinarith
      rw [div_le_div_iff₀ (by positivity) h1]
      nlinarith [hzb.trans (hb0'.trans this)]
    have hs := (Real.sqrt_le_sqrt hzle).trans
      (ksU_sqrt_le_mul_rpow (by positivity : (0 : ℝ) ≤ 4 * (Λ / kA)) h1)
    rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ (1 - ρ) ^ 2), Real.sqrt_sq h1.le,
      Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hs
    have hl0 : 0 ≤ Real.log (1 + z) := Real.log_nonneg (by linarith)
    calc (1 - ρ)⁻¹ * Real.log (1 + z) ≤ 2 * (Real.sqrt z / (1 - ρ)) := by
          rw [mul_comm]; rw [div_eq_mul_inv]
          nlinarith [inv_pos.2 h1]
      _ ≤ 2 * (2 * Real.sqrt (Λ / kA) * (1 - ρ) ^ (-(1 / 2 : ℝ))) := by linarith
      _ ≤ 4 * Real.sqrt (Λ / kA) * ksUg ρ := by nlinarith [mul_le_mul_of_nonneg_left hg.2 hsq0]

/-- The dilogarithm weight: `K(BY/A) ≤ (18 + 16√(Kb/kA) + 16√(Λ/kA)) ksUg ρ` for
`B = b₀ + Λ/ρ`, `b₀ ≤ Kb/(1 - ρ)`. -/
theorem ksU_wt_K {ρ kA A b₀ Y Λ Kb : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hkA : 0 < kA)
    (hkAA : kA ≤ A) (hb0 : 0 ≤ b₀) (hb₀ : b₀ ≤ Kb / (1 - ρ)) (hY : 0 ≤ Y) (hY1 : Y ≤ 1)
    (hΛ : 0 ≤ Λ) (hKb : 0 ≤ Kb) :
    ksUK ((b₀ + Λ / ρ) * Y / A) ≤
      (18 + 16 * Real.sqrt (Kb / kA) + 16 * Real.sqrt (Λ / kA)) * ksUg ρ := by
  obtain ⟨r0, r1⟩ := hρ
  have h1 : 0 < 1 - ρ := by linarith
  have hA : 0 < A := hkA.trans_le hkAA
  set z := (b₀ + Λ / ρ) * Y / A with hz
  have hB : 0 ≤ b₀ + Λ / ρ := by have := div_nonneg hΛ r0.le; linarith
  have hz0 : 0 ≤ z := by positivity
  have hK := ksU_ksUK_le_log hz0
  have hsq := ksU_one_add_log_sq_le hz0
  have hl0 : 0 ≤ Real.log (1 + z) := Real.log_nonneg (by linarith)
  have hzle : z ≤ Kb / kA / (1 - ρ) + Λ / kA / ρ := by
    have : z ≤ (b₀ + Λ / ρ) / kA := by
      rw [hz, div_le_div_iff₀ hA hkA]
      nlinarith [mul_le_mul_of_nonneg_left hY1 hB, mul_le_mul_of_nonneg_left hkAA hB]
    refine this.trans ?_
    have e : Kb / kA / (1 - ρ) + Λ / kA / ρ = (Kb / (1 - ρ) + Λ / ρ) / kA := by
      field_simp
    rw [e]
    gcongr
  have hs : Real.sqrt z ≤ Real.sqrt (Kb / kA) * (1 - ρ) ^ (-(1 / 2 : ℝ)) +
      Real.sqrt (Λ / kA) * ρ ^ (-(1 / 2 : ℝ)) :=
    (Real.sqrt_le_sqrt hzle).trans ((ksU_sqrt_add_le (by positivity) (by positivity)).trans
      (add_le_add (ksU_sqrt_le_mul_rpow (by positivity) h1)
        (ksU_sqrt_le_mul_rpow (by positivity) r0)))
  have hg := ksU_rpow_le_ksUg ⟨r0, r1⟩
  have hg1 := ksU_one_le_ksUg ⟨r0, r1⟩
  have a1 := Real.sqrt_nonneg (Kb / kA)
  have a2 := Real.sqrt_nonneg (Λ / kA)
  have hlsq : Real.log (1 + z) ^ 2 / 2 ≤ (1 + Real.log (1 + z)) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hg.1 a2, mul_le_mul_of_nonneg_left hg.2 a1]

end QED.ChainProof.SetAKS

end
