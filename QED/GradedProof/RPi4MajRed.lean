/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4AsmCore

/-!
# (R-Π₄) step L10: reduction of the majorant to the limit and a fixed-regulator bound

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The majorant
`AsmMajorant` asks for one constant `C` that bounds `Π(s)/e⁴ = (Q(m_γ, Λ; s) - Q(m_γ, Λ; 0))/e⁴`
by `C (1 + log(1 + s/m²))²` for all `s ≥ 0`, uniformly in the fermion regulators beyond a
threshold and in the photon regulators beyond thresholds that may depend on the fermion
regulators. It splits into two statements of different nature:

* `MajLimBound`: the same majorant, with a regulator-independent constant, for the
  photon-regulator limit `asmPolLim` (step L8) alone: no photon regulators are left, so this is a
  statement about the limit function and its dependence on the fermion regulators (the
  territory of the decoupling, step L9);
* `MajFixedBound`: at **each** fermion-regulator point, a bound `K (1 + log(1 + s/m²))` for all
  `s ≥ 0`, with `K` allowed to depend on that point, uniformly in the photon regulators beyond
  thresholds. One logarithm less than the majorant, and no uniformity in the fermion regulators.

Main result: `maj_majorant_of_lim_fixed`: `AsmFaceIds → MajLimBound → MajFixedBound →
AsmMajorant`. For `s` beyond a point-dependent `S₁`, `MajFixedBound` alone gives the majorant
(its single logarithm is eventually below the square); on `[0, S₁]` the joint limit with its rate
(`asm_exists_norm_sub_polLim_le`, which uses `AsmFaceIds`) moves the bound of `MajLimBound` to
the photon regulators, at the cost of `+1` in the constant.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.RPi4

section Maj

variable {n : ℕ} (P₀ : Params) (mH : Fin n → ℝ)

/-- **(L10, limit part)** the majorant of the photon-regulator limit `asmPolLim`, for all
`s ≥ 0`, with a constant independent of the fermion regulators beyond a threshold. -/
def MajLimBound : Prop :=
  ∃ C RM : ℝ, ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ → RM < M₁ → RM < M₂ →
    1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
    ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
      (∀ ℓ, RM < MH₁ ℓ) → (∀ ℓ, RM < MH₂ ℓ) → (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
      (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
        ∀ s : ℝ, 0 ≤ s →
          ‖asmPolLim (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e s /
            (P₀.e : ℂ) ^ 4‖ ≤ C * (1 + Real.log (1 + s / P₀.m ^ 2)) ^ 2

/-- **(L10, fixed-regulator part)** at each fermion-regulator point, the subtracted class sum
grows at most like one logarithm of `s`, for all `s ≥ 0`, uniformly in the photon regulators
beyond thresholds; the constant may depend on the point. -/
def MajFixedBound : Prop :=
  ∀ M₁ M₂ c₁ c₂ : ℝ, P₀.m < M₁ → P₀.m < M₂ →
    1 + c₁ + c₂ = 0 → P₀.m ^ 2 + c₁ * M₁ ^ 2 + c₂ * M₂ ^ 2 = 0 →
    ∀ MH₁ MH₂ cH₁ cH₂ : Fin n → ℝ, (∀ ℓ, mH ℓ < MH₁ ℓ) → (∀ ℓ, mH ℓ < MH₂ ℓ) →
      (∀ ℓ, 1 + cH₁ ℓ + cH₂ ℓ = 0) →
      (∀ ℓ, mH ℓ ^ 2 + cH₁ ℓ * MH₁ ℓ ^ 2 + cH₂ ℓ * MH₂ ℓ ^ 2 = 0) →
      ∃ K δ : ℝ, 0 < δ ∧ ∃ R : ℝ, ∀ mγ Λ : ℝ, 0 < mγ → mγ < δ → R < Λ →
        ∀ s : ℝ, 0 ≤ s →
          ‖qPair (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e mγ Λ s -
              qPair (asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂) leptonRep P₀.e mγ Λ 0‖ ≤
            K * (1 + Real.log (1 + s / P₀.m ^ 2))

/-- Beyond `m² exp T`, the logarithm `log(1 + s/m²)` is at least `T`. -/
theorem maj_le_log_of_le {m T s : ℝ} (hm : 0 < m) (hs : m ^ 2 * Real.exp T ≤ s) :
    T ≤ Real.log (1 + s / m ^ 2) := by
  have hm2 : 0 < m ^ 2 := by positivity
  have h : Real.exp T ≤ 1 + s / m ^ 2 := by
    have : Real.exp T ≤ s / m ^ 2 := by rw [le_div_iff₀ hm2]; linarith
    linarith
  calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
    _ ≤ Real.log (1 + s / m ^ 2) := Real.log_le_log (Real.exp_pos T) h

/-- `log(1 + s/m²) ≥ 0` for `s ≥ 0`. -/
theorem maj_log_nonneg {m s : ℝ} (hs : 0 ≤ s) : 0 ≤ Real.log (1 + s / m ^ 2) :=
  Real.log_nonneg (by have : 0 ≤ s / m ^ 2 := div_nonneg hs (sq_nonneg m); linarith)

/-- **(L10) the majorant from its limit part and its fixed-regulator part**, given the
face-limit identity (L6d3, used through the joint limit L8). -/
theorem maj_majorant_of_lim_fixed (he : P₀.e ≠ 0) (hm : 0 < P₀.m) (hmH : ∀ ℓ, P₀.m < mH ℓ)
    (hId : AsmFaceIds P₀ mH) (hLim : MajLimBound P₀ mH) (hFix : MajFixedBound P₀ mH) :
    AsmMajorant P₀ mH := by
  obtain ⟨C₀, RM, hLim⟩ := hLim
  refine ⟨max C₀ 0 + 1, RM, fun M₁ M₂ c₁ c₂ hM₁ hM₂ hR₁ hR₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂
    hRH₁ hRH₂ hcH₁ hcH₂ => ?_⟩
  set Φ := asmΦ P₀ mH M₁ M₂ c₁ c₂ MH₁ MH₂ cH₁ cH₂ with hΦ
  have hmass : ∀ g, P₀.m ≤ Φ.mass g :=
    le_leptonFlavors_mass (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ) (heavyH mH MH₁ MH₂ cH₁ cH₂) hM₁ hM₂
      hmH hMH₁ hMH₂
  have hPV₁ := leptonFlavors_blockPV₁ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ)
    (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₁ hcH₁
  have hPV₂ := leptonFlavors_blockPV₂ (regP P₀ M₁ M₂ c₁ c₂ P₀.mγ P₀.Λ)
    (heavyH mH MH₁ MH₂ cH₁ cH₂) hc₂ hcH₂
  have hlim := hLim M₁ M₂ c₁ c₂ hM₁ hM₂ hR₁ hR₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hRH₁ hRH₂
    hcH₁ hcH₂
  obtain ⟨K, δ₀, hδ₀, R₀, hfix⟩ :=
    hFix M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂
  have he4 : 0 < |P₀.e| ^ 4 := by positivity
  -- the point-dependent cut `S₁` beyond which the fixed bound suffices
  set T : ℝ := |K| / |P₀.e| ^ 4 with hT
  set S₁ : ℝ := P₀.m ^ 2 * Real.exp T with hS₁
  have h00 : -(4 * P₀.m ^ 2) < (0 : ℝ) := by nlinarith
  obtain ⟨C₈, hC₈⟩ := asm_exists_norm_sub_polLim_le Φ leptonRep P₀ hm hmass leptonRep_idem
    hPV₁ hPV₂ he (S := S₁) h00 fun s h₀ h₁ =>
      hId M₁ M₂ c₁ c₂ hM₁ hM₂ hc₁ hc₂ MH₁ MH₂ cH₁ cH₂ hMH₁ hMH₂ hcH₁ hcH₂ _ s
        (by linarith [abs_nonneg (max S₁ 0)]) (h00.trans_le ((min_self (0 : ℝ)).symm.le.trans h₀))
        (h₁.trans_lt (asm_max_lt_two_mul_sq S₁))
  set r : ℝ := |P₀.e| ^ 4 / (2 * (|C₈| + 1)) with hr
  have hr0 : 0 < r := by positivity
  refine ⟨min δ₀ (min 1 (r ^ 2)), lt_min hδ₀ (lt_min one_pos (by positivity)),
    max R₀ (max 1 r⁻¹), fun mγ Λ hmγ hΛ hmγδ hRΛ s hs => ?_⟩
  have hL0 := maj_log_nonneg (m := P₀.m) hs
  set L : ℝ := Real.log (1 + s / P₀.m ^ 2) with hL
  have hC : 0 ≤ max C₀ 0 := le_max_right _ _
  have hsq1 : 1 ≤ (1 + L) ^ 2 := by nlinarith
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ he4]
  rcases le_or_gt s S₁ with hsS | hsS
  · -- `s ≤ S₁`: the limit bound, moved to the photon regulators by L8
    have hmγ1 : mγ ≤ 1 := (hmγδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
    have hmγr : mγ < r ^ 2 := hmγδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hΛ1 : 1 ≤ Λ := ((le_max_left _ _).trans (le_max_right _ _)).trans hRΛ.le
    have hΛr : r⁻¹ < Λ := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hRΛ
    have hsq : Real.sqrt mγ < r := by
      rw [show r = Real.sqrt (r ^ 2) from (Real.sqrt_sq hr0.le).symm]
      exact Real.sqrt_lt_sqrt hmγ.le hmγr
    have hinv : Λ⁻¹ < r := by
      rw [inv_lt_comm₀ (one_pos.trans_le hΛ1) hr0]
      exact hΛr
    have hinv0 : 0 ≤ Λ⁻¹ := (inv_pos.2 (one_pos.trans_le hΛ1)).le
    have e8 := hC₈ s hs hsS mγ Λ hmγ hmγ1 hΛ1
    have e8' : ‖qPair Φ leptonRep P₀.e mγ Λ s - qPair Φ leptonRep P₀.e mγ Λ 0 -
        asmPolLim Φ leptonRep P₀.e s‖ ≤ |P₀.e| ^ 4 := by
      have hsum0 : 0 ≤ Real.sqrt mγ + Λ⁻¹ := by positivity
      calc _ ≤ C₈ * (Real.sqrt mγ + Λ⁻¹) := e8
        _ ≤ (|C₈| + 1) * (2 * r) :=
          mul_le_mul (by linarith [le_abs_self C₈]) (by linarith) hsum0 (by positivity)
        _ = |P₀.e| ^ 4 := by rw [hr]; field_simp
    have el := hlim s hs
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ he4] at el
    have hsplit : qPair Φ leptonRep P₀.e mγ Λ s - qPair Φ leptonRep P₀.e mγ Λ 0 =
        (qPair Φ leptonRep P₀.e mγ Λ s - qPair Φ leptonRep P₀.e mγ Λ 0 -
          asmPolLim Φ leptonRep P₀.e s) + asmPolLim Φ leptonRep P₀.e s := by ring
    rw [hsplit]
    have hC0 : C₀ * (1 + L) ^ 2 ≤ max C₀ 0 * (1 + L) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ |P₀.e| ^ 4 + C₀ * (1 + L) ^ 2 * |P₀.e| ^ 4 := add_le_add e8' el
      _ ≤ (max C₀ 0 + 1) * (1 + L) ^ 2 * |P₀.e| ^ 4 := by nlinarith
  · -- `s > S₁`: the fixed-regulator bound, one logarithm below the square
    have ef := hfix mγ Λ hmγ (hmγδ.trans_le (min_le_left _ _))
      ((le_max_left _ _).trans_lt hRΛ) s hs
    have hTL : T ≤ L := maj_le_log_of_le hm hsS.le
    have hK : |K| ≤ L * |P₀.e| ^ 4 := by
      rw [hT, div_le_iff₀ he4] at hTL
      exact hTL
    have h1L : 0 ≤ 1 + L := by linarith
    calc _ ≤ K * (1 + L) := ef
      _ ≤ |K| * (1 + L) := mul_le_mul_of_nonneg_right (le_abs_self K) h1L
      _ ≤ (L * |P₀.e| ^ 4) * (1 + L) := mul_le_mul_of_nonneg_right hK h1L
      _ ≤ (max C₀ 0 + 1) * (1 + L) ^ 2 * |P₀.e| ^ 4 := by
        have h2 : L * (1 + L) ≤ (max C₀ 0 + 1) * (1 + L) ^ 2 := by nlinarith [mul_nonneg hC h1L]
        nlinarith [mul_le_mul_of_nonneg_right h2 he4.le]

end Maj

end QED.GradedProof.RPi4

end
