/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayAPWt
public import Mathlib.Analysis.MeanInequalities

/-!
# (R-Π₄) step L10, T2.UV: monomial weights on the simplex, total-degree criterion

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (input (A) of
`QED.GradedProof.RPi4.faceIdRay_of_size_rate`). A sharper form of
`QED.GradedProof.RPi4.faceIdRayAP_integrableOn_wt`: on the region `z_l ≥ 1/(m+1)` the weight
`U⁻ᵏ ∏ₜ zₜ^{wₜ}` is at most `κ^{-k} σ^{-p} ∏ₜ zₜ^{-eₜ}` (`σ = ∑_{S_l} zₜ`,
`p = (k - ∑_{S_l} w⁺)⁺`, `e = w⁻`), and the weighted arithmetic–geometric mean inequality
spreads `σ^{-p}` over `S_l` with weights `θₜ ∝ s - eₜ`. So the criterion is the total degree:
`k - ∑_{S_l} w⁺ + ∑_{S_l} w⁻ ≤ |S_l| s` for every `l`, with `eₜ ≤ s < 1`. Negative exponents on
the lines of `S_l` (the flow weights `z^{-1/2}`) are then paid by the other lines of `S_l`.

For data whose rows are `(1,0)`, `(0,1)`, `(1,-1)` (a line class `cl`), the criterion for the
weights `wₜ = eₜ/2 + a [t = γ] - [t ∈ {t₁, t₂}]/100` (a photon weight `z_γ^a`, a cut pair, half
integer exponents `eₜ`) for every `0 < a ≤ 1` follows from a decidable integer check
(`FaceIdRayAQCheck`).

* `faceIdRayAQ_wt_le`, **`faceIdRayAQ_integrableOn_wt`**: the total-degree criterion;
* `faceIdRayAQRow`, `faceIdRayAQ_lines_eq`: the line classes;
* `faceIdRayAQWs`, `FaceIdRayAQCheck`, `faceIdRayAQW`, **`faceIdRayAQ_integrableOn_check`**;
* `faceIdRayAQ_prod_rpow_add`, `faceIdRayAQ_prod_rpow_ite`: products of powers.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)

variable {m : ℕ}

/-- **The pointwise bound with the total-degree criterion**, at a point where `U ≥ κ σ`,
`σ = ∑_{t ∈ S_l} zₜ`. -/
theorem faceIdRayAQ_wt_le (α : Fin (m + 1) → Fin 2 → ℝ) (k : ℕ) (w : Fin (m + 1) → ℝ)
    {s κ : ℝ} (hs0 : 0 ≤ s) (hκ : 0 < κ) (he : ∀ j, -w j ≤ s) {z : Fin (m + 1) → ℝ}
    (hz : ∀ t, 0 < z t) (hzs : ∑ t, z t ≤ 1) (l : Fin (m + 1))
    (hS : (faceIdRayAPLines α l).Nonempty)
    (hcrit : (k : ℝ) - ∑ t ∈ faceIdRayAPLines α l, max (w t) 0 +
      ∑ t ∈ faceIdRayAPLines α l, max (-w t) 0 ≤ (faceIdRayAPLines α l).card * s)
    (hU : κ * ∑ t ∈ faceIdRayAPLines α l, z t ≤ symanzikU α z) :
    (symanzikU α z ^ k)⁻¹ * ∏ t, z t ^ w t ≤ (κ ^ k)⁻¹ * ∏ t, z t ^ (-s) := by
  classical
  set S := faceIdRayAPLines α l with hSdef
  set σ := ∑ t ∈ S, z t with hσ
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
  have hes : ∀ t, e t ≤ s := fun t => max_le (he t) hs0
  set R := ∑ t ∈ S, (s - e t) with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun t _ => by linarith [hes t]
  have hpR : p ≤ R := by
    have hR' : R = S.card * s - ∑ t ∈ S, e t := by
      rw [hR, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    refine max_le ?_ hR0
    rw [hR']
    linarith
  set θ : Fin (m + 1) → ℝ := fun t => if t ∈ S then (s - e t) * p / R else 0 with hθ
  have hθ0 : ∀ t, 0 ≤ θ t := fun t => by
    simp only [hθ]
    split_ifs
    · rcases eq_or_lt_of_le hR0 with h | h
      · rw [← h, div_zero]
      · exact div_nonneg (mul_nonneg (by linarith [hes t]) hp0) h.le
    · exact le_rfl
  have hθs : ∀ t ∈ S, θ t + e t ≤ s := fun t ht => by
    simp only [hθ, ite_eq_left ht]
    rcases eq_or_lt_of_le hR0 with h | h
    · rw [← h, div_zero]; linarith [hes t]
    · have : (s - e t) * p / R ≤ s - e t := by
        rw [div_le_iff₀ h]
        exact mul_le_mul_of_nonneg_left hpR (by linarith [hes t])
      linarith
  -- `U⁻ᵏ ≤ κ⁻ᵏ σ^{-k}`
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
  have h3 : σ ^ (-(k : ℝ)) * σ ^ Sw ≤ σ ^ (-p) := by
    rw [← Real.rpow_add hσ0]
    exact Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (by
      have := le_max_left ((k : ℝ) - Sw) 0
      linarith)
  -- the weighted arithmetic–geometric mean step
  have h4 : σ ^ (-p) ≤ ∏ t, z t ^ (-θ t) := by
    rcases eq_or_lt_of_le hp0 with hp' | hp'
    · have hθz : ∀ t, θ t = 0 := fun t => by
        simp only [hθ, ← hp', mul_zero, zero_div, ite_self]
      simp only [← hp', hθz, neg_zero, Real.rpow_zero, Finset.prod_const_one, le_refl]
    · have hRp : 0 < R := hp'.trans_le hpR
      set lam : Fin (m + 1) → ℝ := fun t => (s - e t) / R with hlam
      have hl0 : ∀ t ∈ S, 0 ≤ lam t := fun t _ => div_nonneg (by linarith [hes t]) hRp.le
      have hl1 : ∑ t ∈ S, lam t = 1 := by
        rw [hlam, ← Finset.sum_div, ← hR, div_self hRp.ne']
      have hG := Real.geom_mean_le_arith_mean_weighted S lam z hl0 hl1 fun t _ => hz0 t
      have hA : ∑ t ∈ S, lam t * z t ≤ σ := by
        calc ∑ t ∈ S, lam t * z t ≤ ∑ t ∈ S, lam t * σ :=
              Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (hzσ t ht) (hl0 t ht)
          _ = σ := by rw [← Finset.sum_mul, hl1, one_mul]
      have hG0 : 0 < ∏ t ∈ S, z t ^ lam t :=
        Finset.prod_pos fun t _ => Real.rpow_pos_of_pos (hz t) _
      refine (Real.rpow_le_rpow_of_nonpos hG0 (hG.trans hA) (by linarith)).trans
        (le_of_eq ?_)
      rw [← Real.finsetProd_rpow S _ fun t _ => Real.rpow_nonneg (hz0 t) _,
        ← Finset.prod_subset (Finset.subset_univ S) fun t _ ht => by
          simp only [hθ, ite_eq_right ht, neg_zero, Real.rpow_zero]]
      refine Finset.prod_congr rfl fun t ht => ?_
      rw [← Real.rpow_mul (hz0 t)]
      congr 1
      simp only [hθ, ite_eq_left ht, hlam]
      ring
  -- the exponents per line
  have h5 : (∏ t, z t ^ (-θ t)) * ∏ t, z t ^ (-e t) ≤ ∏ t, z t ^ (-s) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun t _ => mul_nonneg (Real.rpow_nonneg (hz0 t) _)
      (Real.rpow_nonneg (hz0 t) _)) fun t _ => ?_
    rw [← Real.rpow_add (hz t)]
    refine Real.rpow_le_rpow_of_exponent_ge (hz t) (hz1 t) ?_
    by_cases ht : t ∈ S
    · linarith [hθs t ht]
    · simp only [hθ, ite_eq_right ht]
      linarith [hes t]
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
    _ ≤ (κ ^ k)⁻¹ * ((∏ t, z t ^ (-θ t)) * ∏ t, z t ^ (-e t)) := by
        gcongr
        exact h3.trans h4
    _ ≤ (κ ^ k)⁻¹ * ∏ t, z t ^ (-s) := mul_le_mul_of_nonneg_left h5 hκk

/-- **Integrability of a monomial weight, total-degree criterion**: `U⁻ᵏ ∏ₜ zₜ^{wₜ}` is
integrable on the simplex if for some `0 ≤ s < 1` every negative exponent is `≥ -s` and, for
every line `l`, `k - ∑_{t ∈ S_l} max(wₜ, 0) + ∑_{t ∈ S_l} max(-wₜ, 0) ≤ |S_l| s` (every line has
a non-parallel line). -/
theorem faceIdRayAQ_integrableOn_wt (α : Fin (m + 1) → Fin 2 → ℝ) (k : ℕ)
    (w : Fin (m + 1) → ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (he : ∀ j, -w j ≤ s)
    (hS : ∀ l, (faceIdRayAPLines α l).Nonempty)
    (hcrit : ∀ l, (k : ℝ) - ∑ t ∈ faceIdRayAPLines α l, max (w t) 0 +
      ∑ t ∈ faceIdRayAPLines α l, max (-w t) 0 ≤ (faceIdRayAPLines α l).card * s) :
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
  have hb := faceIdRayAQ_wt_le α k w hs0 hκ0 he hzpos hz1.le l (hS l) (hcrit l) hUl
  have hnn : 0 ≤ (symanzikU α z ^ k)⁻¹ * ∏ t, z t ^ w t :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg (symanzikU_nonneg α hz0) k))
      (Finset.prod_nonneg fun t _ => Real.rpow_nonneg (hz0 t) _)
  rw [Real.norm_of_nonneg hnn]
  exact hb

/-! ### Line classes and the integer check -/

/-- The three loop rows `(1,0)`, `(0,1)`, `(1,-1)`. -/
def faceIdRayAQRow : Fin 3 → Fin 2 → ℝ := ![![1, 0], ![0, 1], ![1, -1]]

/-- **The lines not parallel to `l`** are the lines of another class. -/
theorem faceIdRayAQ_lines_eq (α : Fin (m + 1) → Fin 2 → ℝ) (cl : Fin (m + 1) → Fin 3)
    (hα : ∀ t, α t = faceIdRayAQRow (cl t)) (l : Fin (m + 1)) :
    faceIdRayAPLines α l = Finset.univ.filter fun j => cl j ≠ cl l := by
  ext j
  simp only [faceIdRayAPLines, Finset.mem_filter, Finset.mem_univ, true_and, pairDet, hα]
  generalize cl l = a
  generalize cl j = b
  fin_cases a <;> fin_cases b <;> simp [faceIdRayAQRow]

/-- The scaled weights `200 wₜ` without the photon weight: `100 eₜ - 2 [t ∈ {t₁, t₂}]`. -/
def faceIdRayAQWs (t₁ t₂ : Fin (m + 1)) (e : Fin (m + 1) → ℤ) (t : Fin (m + 1)) : ℤ :=
  100 * e t - if t = t₁ ∨ t = t₂ then 2 else 0

/-- **The integer check** of the weight `U⁻ᵏ z_γ^a ∏ₜ zₜ^{eₜ/2} (z_{t₁} z_{t₂})^{-1/100}`:
the photon exponent is nonnegative, all exponents are `≥ -9/10`, every line has a line of
another class, and for every line `l` the scaled total degree `V_l` of `S_l` is at most
`180 |S_l|`, or at most `200 |S_l|` with the photon line in `S_l`. -/
def FaceIdRayAQCheck (cl : Fin (m + 1) → Fin 3) (γ t₁ t₂ : Fin (m + 1)) (k : ℕ)
    (e : Fin (m + 1) → ℤ) : Prop :=
  0 ≤ faceIdRayAQWs t₁ t₂ e γ ∧ (∀ j, -faceIdRayAQWs t₁ t₂ e j ≤ 180) ∧
    ∀ l, (∃ j, cl j ≠ cl l) ∧
      (200 * (k : ℤ) - ∑ t ∈ Finset.univ.filter (fun j => cl j ≠ cl l),
          max (faceIdRayAQWs t₁ t₂ e t) 0 +
        ∑ t ∈ Finset.univ.filter (fun j => cl j ≠ cl l), max (-faceIdRayAQWs t₁ t₂ e t) 0 ≤
          180 * (Finset.univ.filter (fun j => cl j ≠ cl l)).card ∨
        (cl γ ≠ cl l ∧ 200 * (k : ℤ) - ∑ t ∈ Finset.univ.filter (fun j => cl j ≠ cl l),
            max (faceIdRayAQWs t₁ t₂ e t) 0 +
          ∑ t ∈ Finset.univ.filter (fun j => cl j ≠ cl l), max (-faceIdRayAQWs t₁ t₂ e t) 0 ≤
            200 * (Finset.univ.filter (fun j => cl j ≠ cl l)).card))

instance (cl : Fin (m + 1) → Fin 3) (γ t₁ t₂ : Fin (m + 1)) (k : ℕ) (e : Fin (m + 1) → ℤ) :
    Decidable (FaceIdRayAQCheck cl γ t₁ t₂ k e) := by
  unfold FaceIdRayAQCheck; infer_instance

/-- The real exponents `eₜ/2 + a [t = γ] - [t ∈ {t₁, t₂}]/100`. -/
noncomputable def faceIdRayAQW (γ t₁ t₂ : Fin (m + 1)) (e : Fin (m + 1) → ℤ) (a : ℝ)
    (t : Fin (m + 1)) : ℝ :=
  (faceIdRayAQWs t₁ t₂ e t : ℝ) / 200 + if t = γ then a else 0

theorem faceIdRayAQW_eq (γ t₁ t₂ : Fin (m + 1)) (e : Fin (m + 1) → ℤ) (a : ℝ)
    (t : Fin (m + 1)) : faceIdRayAQW γ t₁ t₂ e a t =
      (e t : ℝ) / 2 + (if t = γ then a else 0) - if t = t₁ ∨ t = t₂ then 1 / 100 else 0 := by
  simp only [faceIdRayAQW, faceIdRayAQWs]
  split_ifs <;> push_cast <;> ring

/-- **Integrability from the integer check**, for every photon exponent `0 < a ≤ 1`. -/
theorem faceIdRayAQ_integrableOn_check (α : Fin (m + 1) → Fin 2 → ℝ)
    (cl : Fin (m + 1) → Fin 3) (hα : ∀ t, α t = faceIdRayAQRow (cl t))
    (γ t₁ t₂ : Fin (m + 1)) (k : ℕ) (e : Fin (m + 1) → ℤ)
    (hc : FaceIdRayAQCheck cl γ t₁ t₂ k e) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x => (symanzikU α (simplexPoint x) ^ k)⁻¹ *
      ∏ t, simplexPoint x t ^ faceIdRayAQW γ t₁ t₂ e a t) (simplexSet m) := by
  classical
  obtain ⟨hγ, he, hl⟩ := hc
  set ws := faceIdRayAQWs t₁ t₂ e with hws
  set s : ℝ := max (9 / 10) (1 - a / ((m : ℝ) + 1)) with hs
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs1 : s < 1 := max_lt (by norm_num) (by
    have : 0 < a / ((m : ℝ) + 1) := div_pos ha hm1
    linarith)
  have hs0 : 9 / 10 ≤ s := le_max_left _ _
  have hW : ∀ t, faceIdRayAQW γ t₁ t₂ e a t = (ws t : ℝ) / 200 + if t = γ then a else 0 :=
    fun t => rfl
  refine faceIdRayAQ_integrableOn_wt α k _ (by linarith) hs1 (fun j => ?_) (fun l => ?_)
    (fun l => ?_)
  · rw [hW]
    have h1 : (-(ws j) : ℝ) ≤ 180 := by exact_mod_cast he j
    have h2 : 0 ≤ (if j = γ then a else 0) := by split_ifs <;> linarith
    linarith
  · obtain ⟨⟨j, hj⟩, -⟩ := hl l
    rw [faceIdRayAQ_lines_eq α cl hα l]
    exact ⟨j, by simp [hj]⟩
  · obtain ⟨-, hV⟩ := hl l
    rw [faceIdRayAQ_lines_eq α cl hα l]
    set S := Finset.univ.filter fun j => cl j ≠ cl l with hS
    set V : ℤ := 200 * (k : ℤ) - ∑ t ∈ S, max (ws t) 0 + ∑ t ∈ S, max (-ws t) 0 with hVdef
    have hVR : (V : ℝ) = 200 * (k : ℝ) - ∑ t ∈ S, max (ws t : ℝ) 0 +
        ∑ t ∈ S, max (-(ws t : ℝ)) 0 := by
      simp only [hVdef]; push_cast; ring
    -- the positive parts
    have hpos : ∑ t ∈ S, max ((ws t : ℝ) / 200) 0 + (if γ ∈ S then a else 0) ≤
        ∑ t ∈ S, max (faceIdRayAQW γ t₁ t₂ e a t) 0 := by
      have hγ' : (0 : ℝ) ≤ ws γ := by exact_mod_cast hγ
      by_cases hγS : γ ∈ S
      · rw [ite_eq_left hγS, ← Finset.add_sum_erase S _ hγS, ← Finset.add_sum_erase S _ hγS]
        have e1 : max (faceIdRayAQW γ t₁ t₂ e a γ) 0 = (ws γ : ℝ) / 200 + a := by
          rw [hW, ite_eq_left rfl, max_eq_left (by positivity)]
        have e2 : max ((ws γ : ℝ) / 200) 0 = (ws γ : ℝ) / 200 :=
          max_eq_left (by positivity)
        rw [e1, e2]
        have : ∑ t ∈ S.erase γ, max ((ws t : ℝ) / 200) 0 ≤
            ∑ t ∈ S.erase γ, max (faceIdRayAQW γ t₁ t₂ e a t) 0 :=
          Finset.sum_le_sum fun t ht => by
            rw [hW, ite_eq_right (Finset.ne_of_mem_erase ht), add_zero]
        linarith
      · rw [ite_eq_right hγS, add_zero]
        exact Finset.sum_le_sum fun t _ => max_le_max (by
          rw [hW]; split_ifs <;> linarith) le_rfl
    have hneg : ∑ t ∈ S, max (-faceIdRayAQW γ t₁ t₂ e a t) 0 ≤
        ∑ t ∈ S, max (-((ws t : ℝ) / 200)) 0 :=
      Finset.sum_le_sum fun t _ => max_le_max (by
        rw [hW]; split_ifs <;> linarith) le_rfl
    have hsc : ∀ f : Fin (m + 1) → ℝ, ∑ t ∈ S, max (f t / 200) 0 =
        (∑ t ∈ S, max (f t) 0) / 200 := fun f => by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun t _ => by
        rw [← max_div_div_right (c := (200 : ℝ)) (by norm_num), zero_div]
    have hsc' : ∑ t ∈ S, max (-((ws t : ℝ) / 200)) 0 =
        (∑ t ∈ S, max (-(ws t : ℝ)) 0) / 200 := by
      rw [← hsc]
      exact Finset.sum_congr rfl fun t _ => by rw [neg_div]
    have hkey : (k : ℝ) - ∑ t ∈ S, max (faceIdRayAQW γ t₁ t₂ e a t) 0 +
        ∑ t ∈ S, max (-faceIdRayAQW γ t₁ t₂ e a t) 0 ≤
          (V : ℝ) / 200 - (if γ ∈ S then a else 0) := by
      rw [hVR]
      have := hsc fun t => (ws t : ℝ)
      linarith
    have hn : ((S.card : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
      have := Finset.card_le_univ S
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have hn0 : (0 : ℝ) ≤ S.card := by positivity
    rcases hV with hV | ⟨hγl, hV⟩
    · have hV' : (V : ℝ) ≤ 180 * S.card := by exact_mod_cast hV
      have : (0 : ℝ) ≤ if γ ∈ S then a else 0 := by split_ifs <;> linarith
      nlinarith
    · have hV' : (V : ℝ) ≤ 200 * S.card := by exact_mod_cast hV
      have hγS : γ ∈ S := by simp [hS, hγl]
      rw [ite_eq_left hγS] at hkey
      have h2 : (S.card : ℝ) * (1 - a / ((m : ℝ) + 1)) ≤ S.card * s :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hn0
      have h3 : (S.card : ℝ) - a ≤ S.card * (1 - a / ((m : ℝ) + 1)) := by
        rw [mul_sub, mul_one, mul_div_assoc']
        have : (S.card : ℝ) * a / ((m : ℝ) + 1) ≤ a := by
          rw [div_le_iff₀ hm1]; nlinarith
        linarith
      linarith

/-! ### Products of powers -/

theorem faceIdRayAQ_prod_rpow_add {z : Fin (m + 1) → ℝ} (hz : ∀ t, 0 < z t)
    (f g : Fin (m + 1) → ℝ) :
    ∏ t, z t ^ (f t + g t) = (∏ t, z t ^ f t) * ∏ t, z t ^ g t := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t _ => Real.rpow_add (hz t) _ _

theorem faceIdRayAQ_prod_rpow_ite (z : Fin (m + 1) → ℝ) (j : Fin (m + 1)) (c : ℝ) :
    ∏ t, z t ^ (if t = j then c else 0) = z j ^ c := by
  rw [Finset.prod_eq_single j (fun t _ ht => by rw [ite_eq_right ht, Real.rpow_zero])
    (fun h => absurd (Finset.mem_univ j) h), ite_eq_left rfl]

end QED.GradedProof.RPi4

end
