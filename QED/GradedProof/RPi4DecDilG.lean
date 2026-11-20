/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecNull
public import QED.GradedProof.RPi4PairQ

/-!
# (R-Π₄) step L9, D3a: generic dilation lemmas (integrals, `ε → 0⁺` limits, the projection)

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (decoupling),
part D3a (dimensional analysis of the regulated class sum, `DecDilQ`). Model-free pieces:

* `dec_jef_smul`, `dec_efi_smul`: the two- and one-loop energy-first integrals under `ℓ ↦ l ℓ`
  (exact for every integrand: Lebesgue measure is Haar, no integrability needed);
* `dec_limT_smul`: if `H(l² ε, l k) = l² G(ε, k)` for `ε > 0` and `G` has a limit at `k`, then
  `limT H (l k) = l² limT G k`;
* `dec_canonVec_mul`: `canonVec (l² s) = l canonVec s` for `s ≠ 0`; `dec_trProj_smul`;
* **`dec_projS_smul`**: under the same hypothesis with `HasVPLim T G`,
  `projS (limT H) (l² s) = projS (limT G) s` on the region, including `s = 0` (the null readout,
  through `dec_null_smul`).
-/

@[expose] public section

open Complex Filter Topology MeasureTheory
open QED.GradedProof.VP2
open QED.GradedProof.SE2 (canonVec dot_canonVec nullVec dot_nullVec dot_smul_nullVec)

namespace QED.GradedProof.RPi4

/-! ### The energy-first integrals under a dilation of the loop momenta -/

theorem dec_smul_cons (l t : ℝ) (v : Fin 3 → ℝ) :
    l • (Fin.cons t v : Fin 4 → ℝ) = Fin.cons (l * t) (l • v) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- **The two-loop energy-first integral under `ℓ ↦ l ℓ`.** -/
theorem dec_jef_smul (F : (Fin 2 → Fin 4 → ℝ) → ℂ) {l : ℝ} (hl : 0 < l) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 F =
      ((l ^ 8 : ℝ) : ℂ) * QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ => F (l • ℓ) := by
  simp only [QED.TwoLoop.jointEnergyFirstIntegral]
  have e1 : ∀ (v : Fin 2 → Fin 3 → ℝ) (t : Fin 2 → ℝ),
      (l • fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)) =
        fun s => (Fin.cons ((l • t) s) ((l • v) s) : Fin 4 → ℝ) := fun v t => by
    funext s
    simp only [Pi.smul_apply, dec_smul_cons, smul_eq_mul]
  simp only [e1]
  have h1 := fun v : Fin 2 → Fin 3 → ℝ => Measure.integral_comp_smul (μ := volume)
    (fun t : Fin 2 → ℝ => F fun s => (Fin.cons (t s) ((l • v) s) : Fin 4 → ℝ)) l
  simp only [h1]
  rw [integral_smul, Measure.integral_comp_smul (μ := volume)
    (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ, F fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ))
    l]
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Complex.real_smul]
  rw [← mul_assoc]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
  push_cast
  field_simp

/-- **The one-loop energy-first integral under `q ↦ l q`.** -/
theorem dec_efi_smul (F : (Fin 4 → ℝ) → ℂ) {l : ℝ} (hl : 0 < l) :
    QED.OneLoop.energyFirstIntegral F =
      ((l ^ 4 : ℝ) : ℂ) * QED.OneLoop.energyFirstIntegral fun q => F (l • q) := by
  simp only [QED.OneLoop.energyFirstIntegral, dec_smul_cons]
  have h1 := fun v : Fin 3 → ℝ => Measure.integral_comp_mul_left
    (fun t : ℝ => F (Fin.cons t (l • v) : Fin 4 → ℝ)) l
  simp only [h1]
  rw [integral_smul, Measure.integral_comp_smul (μ := volume)
    (fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t v : Fin 4 → ℝ)) l]
  simp only [Module.finrank_pi, Fintype.card_fin, Complex.real_smul]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  rw [abs_of_pos (by positivity : (0 : ℝ) < (l ^ 3)⁻¹), abs_of_pos (inv_pos.2 hl)]
  push_cast
  field_simp

/-! ### Limits and the projection -/

variable {T : ℝ} {G H : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} {l : ℝ}

theorem dec_tendsto_div_sq (hl : 0 < l) :
    Tendsto (fun ε : ℝ => ε / l ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h := ((continuous_id.div_const (l ^ 2)).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact div_pos hε (by positivity)

/-- **The limit of a dilated family.** -/
theorem dec_limT_smul (hG : HasVPLim T G) (hl : 0 < l)
    (hH : ∀ ε, 0 < ε → ∀ k μ ν, H (l ^ 2 * ε) (l • k) μ ν = ((l ^ 2 : ℝ) : ℂ) * G ε k μ ν)
    {k : Fin 4 → ℝ} (hk : -T ^ 2 < Minkowski.dot k k) :
    limT H (l • k) = fun μ ν => ((l ^ 2 : ℝ) : ℂ) * limT G k μ ν := by
  funext μ ν
  refine limT_eq ?_
  have t := ((tendsto_limT_of_hasVPLim hG hk μ ν).comp (dec_tendsto_div_sq hl)).const_mul
    ((l ^ 2 : ℝ) : ℂ)
  refine t.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have h := hH (ε / l ^ 2) (div_pos hε (by positivity)) k μ ν
  rw [mul_div_cancel₀ _ (by positivity)] at h
  exact h.symm

theorem dec_canonVec_mul (hl : 0 < l) {s : ℝ} (hs : s ≠ 0) :
    canonVec (l ^ 2 * s) = l • canonVec s := by
  have hsq : ∀ x : ℝ, Real.sqrt (l ^ 2 * x) = l * Real.sqrt x := fun x => by
    rw [Real.sqrt_mul (sq_nonneg l), Real.sqrt_sq hl.le]
  have hl2 : 0 < l ^ 2 := by positivity
  rcases lt_or_gt_of_ne hs with h | h
  · have h' : l ^ 2 * s < 0 := mul_neg_of_pos_of_neg hl2 h
    simp only [canonVec, h, h', ite_true]
    rw [show -(l ^ 2 * s) = l ^ 2 * -s by ring, hsq]
    funext i
    fin_cases i <;> simp
  · have h' : 0 < l ^ 2 * s := mul_pos hl2 h
    simp only [canonVec, not_lt.2 h.le, not_lt.2 h'.le, h, h', ite_true, ite_false]
    rw [hsq]
    funext i
    fin_cases i <;> simp

theorem dec_trProj_smul (hl : l ≠ 0) {k : Fin 4 → ℝ} (hk : Minkowski.dot k k ≠ 0)
    (X : Fin 4 → Fin 4 → ℂ) :
    trProj (l • k) (fun μ ν => ((l ^ 2 : ℝ) : ℂ) * X μ ν) = trProj k X := by
  have hd : Minkowski.dot (l • k) (l • k) = l ^ 2 * Minkowski.dot k k := by
    simp only [Minkowski.dot_eq, Pi.smul_apply, smul_eq_mul]
    ring
  have hlow : ∀ μ, Minkowski.lower (l • k) μ = l * Minkowski.lower k μ := fun μ => by
    simp only [Minkowski.lower, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hk' : ((Minkowski.dot k k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  simp only [trProj, trWt, hd, hlow]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  push_cast
  field_simp

/-- **The projection of a dilated family** at `l² s` is the projection at `s`. -/
theorem dec_projS_smul (hG : HasVPLim T G) (hT : 0 < T) (hl : 0 < l)
    (hH : ∀ ε, 0 < ε → ∀ k μ ν, H (l ^ 2 * ε) (l • k) μ ν = ((l ^ 2 : ℝ) : ℂ) * G ε k μ ν)
    {s : ℝ} (hs : -T ^ 2 < s) : projS (limT H) (l ^ 2 * s) = projS (limT G) s := by
  have hT2 : -T ^ 2 < 0 := by nlinarith
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [mul_zero]
    simp only [projS, ite_true, nProj]
    have hk : -T ^ 2 < Minkowski.dot (l⁻¹ • nullVec) (l⁻¹ • nullVec) := by
      rw [dot_smul_nullVec]; exact hT2
    have e1 := congrFun (congrFun (dec_limT_smul hG hl hH hk) 0) 1
    rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul] at e1
    rw [e1, dec_null_smul (tcov_limT hG) hT2 (fun μ ν => tendsto_limT_nullVec hG hT2 μ ν)
      (inv_pos.2 hl)]
    have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    push_cast
    field_simp
  · have hs' : l ^ 2 * s ≠ 0 := mul_ne_zero (by positivity) hs0
    simp only [projS, hs0, hs', ite_false]
    rw [dec_canonVec_mul hl hs0, dec_limT_smul hG hl hH (by rwa [dot_canonVec]),
      dec_trProj_smul hl.ne' (by rwa [dot_canonVec])]

end QED.GradedProof.RPi4

end
