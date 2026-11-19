/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.CountertermLimitProduct

/-!
# Positivity of `V` below threshold for one-loop self-energy product data

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2. For product data given by line kinds
(`QED.TwoLoop.CountertermLimit.LineKind`) with only incoming electron lines (momentum `p + ℓ₀`),
photon lines (`ℓ₀`) and auxiliary lines (`ℓ₁`), electron and auxiliary masses at least `m_e`,
photon masses at least `μ`, and an off-shell `p` below the threshold, `p² > -(m_e + μ)²`
(mostly-plus metric):

`V ≥ min(1, 1 + p²/(m_e + μ)²) · min(m_e², μ²) > 0`  (`symanzikV_kinds_se_ge`).

## Proof

All external momenta are multiples of `p`, so `V = ∑ᵢ zᵢ Mᵢ² + p² R` with `R ≥ 0` the remainder
of the electron indicator (`symanzikV_smul_add_smul`). With `X`, `Y` the electron and photon
weights, the shift `y = -X/(X + Y)` of the first loop momentum gives `R (X + Y) ≤ X Y`
(`remainder_le_sum_sq`), and `(m_e + μ)² X Y ≤ (m_e² X + μ² Y)(X + Y)` is
`(m_e X - μ Y)² ≥ 0`. So `(m_e + μ)² R ≤ ∑ᵢ zᵢ Mᵢ²`, and for `p² < 0`,
`V ≥ (1 + p²/(m_e + μ)²) ∑ᵢ zᵢ Mᵢ²`.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit

/-- **Positivity of `V` below threshold** for self-energy product data. -/
theorem symanzikV_kinds_se_ge {m : ℕ} (κ : Fin (m + 1) → LineKind) (hκ : ∀ i, κ i ≠ .out)
    (Ms : Fin (m + 1) → ℝ) {me μ : ℝ} (hme : 0 < me) (hμ : 0 < μ) {p : Fin 4 → ℝ}
    (hs : -(me + μ) ^ 2 < Minkowski.dot p p)
    (hMe : ∀ i, κ i ≠ .pho → me ^ 2 ≤ Ms i ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    {z : Fin (m + 1) → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix fun i => (κ i).dir) z ≠ 0) :
    min 1 (1 + Minkowski.dot p p / (me + μ) ^ 2) * min (me ^ 2) (μ ^ 2) ≤
      symanzikV (castLoopMatrix fun i => (κ i).dir) (fun i => (κ i).mom p p) Ms z := by
  set α : Fin (m + 1) → Fin 2 → ℝ := castLoopMatrix fun i => (κ i).dir with hα
  set a : Fin (m + 1) → ℝ := fun i => if κ i = .inn then 1 else 0 with ha
  set g : Fin (m + 1) → ℝ := fun i => if κ i = .pho then 1 else 0 with hg
  have hmom : (fun i => (κ i).mom p p) = fun i => a i • p + (0 : ℝ) • (0 : Fin 4 → ℝ) := by
    funext i ν
    have := hκ i
    rcases h : κ i with _ | _ | _ | _ <;> simp_all [LineKind.mom, a]
  have hdot0 : Minkowski.dot p 0 = 0 := by simp [Minkowski.dot_eq]
  rw [hmom, symanzikV_smul_add_smul α Ms z a (fun _ => 0) hdot0]
  have hd00 : Minkowski.dot (0 : Fin 4 → ℝ) 0 = 0 := by simp [Minkowski.dot_eq]
  rw [hd00, zero_mul, add_zero]
  set s := Minkowski.dot p p
  set T := me + μ with hT
  have hT0 : 0 < T := by positivity
  set W := ∑ i, z i * Ms i ^ 2 with hW
  set X := ∑ i, z i * a i with hX
  set Y := ∑ i, z i * g i with hY
  set c := min (me ^ 2) (μ ^ 2) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by positivity)
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (by
    simp only [a]; split_ifs <;> norm_num)
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (by
    simp only [g]; split_ifs <;> norm_num)
  -- the mass term
  have hWc : c ≤ W := by
    rw [← mul_one c, ← hz1, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm c]
    refine mul_le_mul_of_nonneg_left ?_ (hz i)
    by_cases h : κ i = .pho
    · exact (min_le_right _ _).trans (hMp i h)
    · exact (min_le_left _ _).trans (hMe i h)
  have hWXY : me ^ 2 * X + μ ^ 2 * Y ≤ W := by
    simp only [hX, hY, hW, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h : κ i = .pho
    · have := mul_le_mul_of_nonneg_left (hMp i h) (hz i)
      rw [show a i = 0 by simp [a, h], show g i = 1 by simp [g, h]]
      linarith
    · by_cases h' : κ i = .inn
      · have := mul_le_mul_of_nonneg_left (hMe i h) (hz i)
        rw [show a i = 1 by simp [a, h'], show g i = 0 by simp [g, h]]
        linarith
      · have := mul_nonneg (hz i) (sq_nonneg (Ms i))
        rw [show a i = 0 by simp [a, h'], show g i = 0 by simp [g, h]]
        linarith
  -- the remainder
  have hR0 := remainder_nonneg α hz hU a
  have hRle : T ^ 2 * remainder α z a ≤ W := by
    rcases (add_nonneg hX0 hY0).eq_or_lt with h0 | hpos
    · have hX00 : X = 0 := by linarith
      have h := remainder_le_sum_sq α hz hU a 0
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at h
      have hsq : ∑ i, z i * a i ^ 2 = X := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [a]; split_ifs <;> ring
      have : remainder α z a = 0 := le_antisymm (by linarith) hR0
      rw [this, mul_zero]
      linarith
    · set y0 := -X / (X + Y) with hy0
      have h := remainder_le_sum_sq α hz hU a ![y0, 0]
      have hsum : ∑ i, z i * (∑ s, α i s * (![y0, 0] : Fin 2 → ℝ) s + a i) ^ 2 =
          X * (y0 + 1) ^ 2 + Y * y0 ^ 2 := by
        simp only [hX, hY, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have := hκ i
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hα, castLoopMatrix,
          a, g]
        rcases hk : κ i with _ | _ | _ | _ <;> simp_all [LineKind.dir]
      rw [hsum] at h
      have hval : X * (y0 + 1) ^ 2 + Y * y0 ^ 2 = X * Y / (X + Y) := by
        rw [hy0]
        field_simp
        ring
      rw [hval, le_div_iff₀ hpos] at h
      have hkey : T ^ 2 * (X * Y) ≤ (me ^ 2 * X + μ ^ 2 * Y) * (X + Y) := by
        rw [hT]
        nlinarith [sq_nonneg (me * X - μ * Y)]
      have : T ^ 2 * remainder α z a * (X + Y) ≤ W * (X + Y) := by
        calc T ^ 2 * remainder α z a * (X + Y) = T ^ 2 * (remainder α z a * (X + Y)) := by ring
          _ ≤ T ^ 2 * (X * Y) := mul_le_mul_of_nonneg_left h (by positivity)
          _ ≤ (me ^ 2 * X + μ ^ 2 * Y) * (X + Y) := hkey
          _ ≤ W * (X + Y) := mul_le_mul_of_nonneg_right hWXY hpos.le
      exact le_of_mul_le_mul_right this hpos
  -- conclusion
  rcases le_or_gt 0 s with hs0 | hs0
  · calc min 1 (1 + s / T ^ 2) * c ≤ 1 * c :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hc0.le
      _ ≤ W + s * remainder α z a := by nlinarith
  · have hδ : 0 < 1 + s / T ^ 2 := by
      have hT2 : 0 < T ^ 2 := by positivity
      have h1 : 0 < T ^ 2 + s := by linarith
      calc (0 : ℝ) < (T ^ 2 + s) / T ^ 2 := by positivity
        _ = 1 + s / T ^ 2 := by field_simp
    have hRW : remainder α z a ≤ W / T ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    calc min 1 (1 + s / T ^ 2) * c ≤ (1 + s / T ^ 2) * c :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hc0.le
      _ ≤ (1 + s / T ^ 2) * W := mul_le_mul_of_nonneg_left hWc hδ.le
      _ = W + s * (W / T ^ 2) := by ring
      _ ≤ W + s * remainder α z a := by nlinarith

end QED.GradedProof.SE2

end
