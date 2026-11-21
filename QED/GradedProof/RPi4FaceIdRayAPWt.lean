/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SymanzikIntegrabilityQuadratic

/-!
# (R-Π₄) step L10, T2.UV: integrability of monomial weights on the simplex

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (input (A) of
`QED.GradedProof.RPi4.faceIdRay_of_size_rate`). The majorants of the merged pieces along the ray
are sums of weights `U⁻ᵏ ∏ₜ zₜ^{wₜ}` with real exponents: positive ones (a photon weight
`z_γ^a`, the parameters of the adjugate `adj A = ∑ₜ zₜ (J αₜ)(J αₜ)ᵀ`) and small negative ones
(the cut weight `B^{-δ} ≤ C (z_a z_b)^{-δ}`, the flow weight `(zᵢ zⱼ)^{-1/2}`). This file gives a
power-counting criterion for such a weight, one line class at a time.

For a line `l` let `S_l` be the lines not parallel to `l`, `σ = ∑_{t ∈ S_l} zₜ`. Where
`z_l ≥ 1/(m+1)`, `U ≥ κ σ`; the positive exponents on `S_l` give `σ^{∑ w⁺}`, so the weight is at
most `κ^{-k} σ^{-p} ∏ₜ zₜ^{-eₜ}` with `p = max(k - ∑_{S_l} w⁺, 0)`, `eₜ = max(-wₜ, 0)`, and
the arithmetic–geometric mean inequality turns `σ^{-p}` into `∏_{t ∈ S_l} zₜ^{-p/|S_l|}`. If
`p/|S_l| + eₜ ≤ s < 1` for `t ∈ S_l` and `eₜ ≤ s` for all `t`, the weight is at most
`κ^{-k} ∏ₜ zₜ^{-s}`, which is integrable
(`QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow`).

* `faceIdRayAPLines`: the lines `S_l`; `faceIdRayAP_rpow_split`;
* `faceIdRayAP_wt_le`: the pointwise bound;
* **`faceIdRayAP_integrableOn_wt`**: the criterion.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ}

/-- The lines not parallel to `l`. -/
noncomputable def faceIdRayAPLines (α : Fin (m + 1) → Fin 2 → ℝ) (l : Fin (m + 1)) :
    Finset (Fin (m + 1)) :=
  Finset.univ.filter fun j => pairDet α l j ≠ 0

/-- `zʷ = z^{w⁺} z^{-e}`, `w⁺ = max(w, 0)`, `e = max(-w, 0)`, for `z > 0`. -/
theorem faceIdRayAP_rpow_split {z : ℝ} (hz : 0 < z) (w : ℝ) :
    z ^ w = z ^ max w 0 * z ^ (-max (-w) 0) := by
  rw [← Real.rpow_add hz]
  congr 1
  rcases le_total w 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- **The pointwise bound of a monomial weight** at a point where `U ≥ κ σ`,
`σ = ∑_{t ∈ S_l} zₜ`. -/
theorem faceIdRayAP_wt_le (α : Fin (m + 1) → Fin 2 → ℝ) (k : ℕ) (w : Fin (m + 1) → ℝ)
    {s κ : ℝ} (hs0 : 0 ≤ s) (hκ : 0 < κ) (he : ∀ j, -w j ≤ s) {z : Fin (m + 1) → ℝ}
    (hz : ∀ t, 0 < z t) (hzs : ∑ t, z t ≤ 1) (l : Fin (m + 1))
    (hS : (faceIdRayAPLines α l).Nonempty)
    (hcrit : ∀ j ∈ faceIdRayAPLines α l, ((k : ℝ) - ∑ t ∈ faceIdRayAPLines α l, max (w t) 0) /
      (faceIdRayAPLines α l).card + max (-w j) 0 ≤ s)
    (hU : κ * ∑ t ∈ faceIdRayAPLines α l, z t ≤ symanzikU α z) :
    (symanzikU α z ^ k)⁻¹ * ∏ t, z t ^ w t ≤ (κ ^ k)⁻¹ * ∏ t, z t ^ (-s) := by
  classical
  set S := faceIdRayAPLines α l with hSdef
  set σ := ∑ t ∈ S, z t with hσ
  set n := S.card with hn
  have hn0 : 0 < n := Finset.card_pos.mpr hS
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hz0 : ∀ t, 0 ≤ z t := fun t => (hz t).le
  have hσ0 : 0 < σ := Finset.sum_pos (fun t _ => hz t) hS
  have hσ1 : σ ≤ 1 := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    fun i _ _ => hz0 i).trans hzs
  have hz1 : ∀ t, z t ≤ 1 := fun t =>
    (Finset.single_le_sum (fun i _ => hz0 i) (Finset.mem_univ t)).trans hzs
  have hzσ : ∀ t ∈ S, z t ≤ σ := fun t ht => Finset.single_le_sum (fun i _ => hz0 i) ht
  set Sw := ∑ t ∈ S, max (w t) 0 with hSw
  set p := max ((k : ℝ) - Sw) 0 with hp
  have hp0 : 0 ≤ p := le_max_right _ _
  set e : Fin (m + 1) → ℝ := fun t => max (-w t) 0 with he_def
  -- `U⁻ᵏ ≤ κ⁻ᵏ σ^{-k}`
  have hU0 : 0 < symanzikU α z := lt_of_lt_of_le (mul_pos hκ hσ0) hU
  have h1 : (symanzikU α z ^ k)⁻¹ ≤ (κ ^ k)⁻¹ * σ ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg hσ0.le, Real.rpow_natCast, ← mul_inv, ← mul_pow]
    exact inv_anti₀ (pow_pos (mul_pos hκ hσ0) k) (pow_le_pow_left₀ (by positivity) hU k)
  -- the positive exponents
  have h2 : ∏ t, z t ^ max (w t) 0 ≤ σ ^ Sw := by
    rw [hSw, Real.rpow_sum_of_pos hσ0, ← Finset.prod_mul_prod_compl S]
    have hc : ∏ t ∈ Sᶜ, z t ^ max (w t) 0 ≤ 1 :=
      Finset.prod_le_one₀ (fun t _ => Real.rpow_nonneg (hz0 t) _)
        fun t _ => Real.rpow_le_one (hz0 t) (hz1 t) (le_max_right _ _)
    have hS' : ∏ t ∈ S, z t ^ max (w t) 0 ≤ ∏ t ∈ S, σ ^ max (w t) 0 :=
      Finset.prod_le_prod₀ (fun t _ => Real.rpow_nonneg (hz0 t) _)
        fun t ht => Real.rpow_le_rpow (hz0 t) (hzσ t ht) (le_max_right _ _)
    calc (∏ t ∈ S, z t ^ max (w t) 0) * ∏ t ∈ Sᶜ, z t ^ max (w t) 0
        ≤ (∏ t ∈ S, σ ^ max (w t) 0) * 1 :=
          mul_le_mul hS' hc (Finset.prod_nonneg fun t _ => Real.rpow_nonneg (hz0 t) _)
            (Finset.prod_nonneg fun t _ => Real.rpow_nonneg hσ0.le _)
      _ = _ := mul_one _
  -- `σ^{-k} σ^{Sw} ≤ σ^{-p}`
  have h3 : σ ^ (-(k : ℝ)) * σ ^ Sw ≤ σ ^ (-p) := by
    rw [← Real.rpow_add hσ0]
    exact Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (by
      have := le_max_left ((k : ℝ) - Sw) 0
      linarith)
  -- the arithmetic–geometric mean step
  have hG : ∏ t ∈ S, z t ^ (1 / (n : ℝ)) ≤ σ := by
    have h := card_mul_prod_rpow_le_sum S hn0 rfl hz0
    have hG0 : 0 ≤ ∏ t ∈ S, z t ^ (1 / (n : ℝ)) :=
      Finset.prod_nonneg fun t _ => Real.rpow_nonneg (hz0 t) _
    have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    nlinarith
  have hG0 : 0 < ∏ t ∈ S, z t ^ (1 / (n : ℝ)) :=
    Finset.prod_pos fun t _ => Real.rpow_pos_of_pos (hz t) _
  have h4 : σ ^ (-p) ≤ ∏ t ∈ S, z t ^ (-(p / n)) := by
    refine (Real.rpow_le_rpow_of_nonpos hG0 hG (by linarith)).trans (le_of_eq ?_)
    rw [← Real.finsetProd_rpow S _ fun t _ => Real.rpow_nonneg (hz0 t) _]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← Real.rpow_mul (hz0 t)]
    congr 1
    ring
  -- the exponents per line
  have h5 : (∏ t ∈ S, z t ^ (-(p / n))) * ∏ t, z t ^ (-e t) ≤ ∏ t, z t ^ (-s) := by
    have hite : ∏ t ∈ S, z t ^ (-(p / n)) = ∏ t, if t ∈ S then z t ^ (-(p / n)) else 1 := by
      rw [Finset.prod_ite_mem, Finset.univ_inter]
    rw [hite, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun t _ => mul_nonneg (by
      split_ifs <;> [exact Real.rpow_nonneg (hz0 t) _; exact zero_le_one])
      (Real.rpow_nonneg (hz0 t) _)) fun t _ => ?_
    have het : e t ≤ s := max_le (by linarith [he t]) hs0
    split_ifs with ht
    · rw [← Real.rpow_add (hz t)]
      refine Real.rpow_le_rpow_of_exponent_ge (hz t) (hz1 t) ?_
      have hpn : p / n + e t ≤ s := by
        rcases le_total ((k : ℝ) - Sw) 0 with hk | hk
        · rw [hp, max_eq_right hk, zero_div, zero_add]; exact het
        · rw [hp, max_eq_left hk]; exact hcrit t ht
      linarith
    · rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_ge (hz t) (hz1 t) (by linarith)
  -- assembly
  have hsplit : ∏ t, z t ^ w t = (∏ t, z t ^ max (w t) 0) * ∏ t, z t ^ (-e t) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => faceIdRayAP_rpow_split (hz t) (w t)
  rw [hsplit]
  have hP0 : 0 ≤ ∏ t, z t ^ (-e t) := Finset.prod_nonneg fun t _ => Real.rpow_nonneg (hz0 t) _
  have hW0 : 0 ≤ ∏ t, z t ^ max (w t) 0 :=
    Finset.prod_nonneg fun t _ => Real.rpow_nonneg (hz0 t) _
  have hσk : 0 ≤ σ ^ (-(k : ℝ)) := Real.rpow_nonneg hσ0.le _
  have hκk : 0 ≤ (κ ^ k)⁻¹ := by positivity
  calc (symanzikU α z ^ k)⁻¹ * ((∏ t, z t ^ max (w t) 0) * ∏ t, z t ^ (-e t))
      ≤ ((κ ^ k)⁻¹ * σ ^ (-(k : ℝ))) * (σ ^ Sw * ∏ t, z t ^ (-e t)) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 hP0) (mul_nonneg hW0 hP0)
          (mul_nonneg hκk hσk)
    _ = (κ ^ k)⁻¹ * ((σ ^ (-(k : ℝ)) * σ ^ Sw) * ∏ t, z t ^ (-e t)) := by ring
    _ ≤ (κ ^ k)⁻¹ * ((∏ t ∈ S, z t ^ (-(p / n))) * ∏ t, z t ^ (-e t)) := by
        gcongr
        exact h3.trans h4
    _ ≤ (κ ^ k)⁻¹ * ∏ t, z t ^ (-s) := mul_le_mul_of_nonneg_left h5 hκk

/-- **Integrability of a monomial weight**: `U⁻ᵏ ∏ₜ zₜ^{wₜ}` is integrable on the simplex if for
some `0 ≤ s < 1` every negative exponent is `≥ -s` and, for every line `l` and `j ∈ S_l`,
`(k - ∑_{t ∈ S_l} max(wₜ, 0))/|S_l| + max(-w_j, 0) ≤ s` (every line has a non-parallel line). -/
theorem faceIdRayAP_integrableOn_wt (α : Fin (m + 1) → Fin 2 → ℝ) (k : ℕ)
    (w : Fin (m + 1) → ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (he : ∀ j, -w j ≤ s)
    (hS : ∀ l, (faceIdRayAPLines α l).Nonempty)
    (hcrit : ∀ l, ∀ j ∈ faceIdRayAPLines α l,
      ((k : ℝ) - ∑ t ∈ faceIdRayAPLines α l, max (w t) 0) / (faceIdRayAPLines α l).card +
        max (-w j) 0 ≤ s) :
    IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ k)⁻¹ *
      ∏ t, simplexPoint x t ^ w t) (simplexSet m) := by
  classical
  have hm : 0 < m := by
    obtain ⟨j, hj⟩ := hS 0
    have h := (Finset.mem_filter.mp hj).2
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have hj0 : j = 0 := Fin.ext (by have := j.isLt; omega)
      subst hj0
      exact absurd (by simp only [pairDet]; ring) h
    · exact h0
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_pairDet_sq α
  set κ : ℝ := c / (2 * ((m : ℝ) + 1)) with hκ
  have hκ0 : 0 < κ := by positivity
  have hint : IntegrableOn (fun x => (κ ^ k)⁻¹ * ∏ t, simplexPoint x t ^ (-s))
      (simplexSet m) :=
    (integrableOn_prod_simplexPoint_rpow Finset.univ hs0 hs1).const_mul _
  have hmeas : Measurable fun x : Fin m → ℝ => (symanzikU α (simplexPoint x) ^ k)⁻¹ *
      ∏ t, simplexPoint x t ^ w t :=
    ((continuous_symanzikU_comp_simplexPoint α).pow k).measurable.inv.mul
      (Finset.measurable_prod _ fun t _ =>
        ((continuous_apply t).comp continuous_simplexPoint').measurable.pow_const _)
  refine hint.mono' hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' (QED.Integration.Feynman.measurableSet_simplexSet m)]
  filter_upwards [ae_simplexPoint_ne_zero hm] with x hx0 hxS
  obtain ⟨hz0, hz1⟩ := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
  set z := simplexPoint x with hzdef
  have hzpos : ∀ i, 0 < z i := fun i => lt_of_le_of_ne (hz0 i) (hx0 i).symm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  obtain ⟨l, -, hl⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
    (f := fun _ => ((m : ℝ) + 1)⁻¹) (g := z) (by
      rw [hz1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [mul_inv_cancel₀ hm1.ne'])
  have hrow := mul_sum_pairDet_sq_le_two_mul_symanzikU α hz0 l
  have hsub : c * ∑ t ∈ faceIdRayAPLines α l, z t ≤ ∑ t, z t * pairDet α l t ^ 2 := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun t ht => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun t _ _ => mul_nonneg (hz0 t) (sq_nonneg _))
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hc l t (Finset.mem_filter.mp ht).2) (hz0 t)
  have hUl : κ * ∑ t ∈ faceIdRayAPLines α l, z t ≤ symanzikU α z := by
    have h1 : ((m : ℝ) + 1)⁻¹ * (c * ∑ t ∈ faceIdRayAPLines α l, z t) ≤
        z l * ∑ t, z t * pairDet α l t ^ 2 :=
      mul_le_mul hl hsub (mul_nonneg hc0.le (Finset.sum_nonneg fun t _ => hz0 t)) (hz0 l)
    have e : κ * ∑ t ∈ faceIdRayAPLines α l, z t =
        ((m : ℝ) + 1)⁻¹ * (c * ∑ t ∈ faceIdRayAPLines α l, z t) / 2 := by
      rw [hκ]; field_simp
    rw [e]
    linarith
  have hb := faceIdRayAP_wt_le α k w hs0 hκ0 he hzpos hz1.le l (hS l) (hcrit l) hUl
  have hnn : 0 ≤ (symanzikU α z ^ k)⁻¹ * ∏ t, z t ^ w t :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg (by
      have := symanzikU_nonneg α hz0
      exact this) k)) (Finset.prod_nonneg fun t _ => Real.rpow_nonneg (hz0 t) _)
  rw [Real.norm_of_nonneg hnn]
  exact hb

end QED.GradedProof.RPi4

end
