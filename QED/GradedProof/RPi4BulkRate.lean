/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Bulk
public import QED.GradedProof.RPi4SectorEl

/-!
# (R-Π₄) step L6d1: the bulk rate `u^{-1/2}`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d1. On the bulk of
a collapsed piece (`bulkSet`) the integrand is `≤ D t (c₁ + t u)^{-2}` with `D` uniform over a
family (`norm_pieceF_le_bulk`), so `u` times the bulk integral is `O(u^{-1/2})` (`bulk_rate`).
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

variable {m : ℕ}

/-- **The collapsed integrand on the bulk**: `‖pieceF‖ ≤ t D (c₁ + t u)^{-2}`, `t = z_γ`, with
`D` depending only on the numerator bound, the momentum bound, `ρ₀` and `c₁`. -/
theorem norm_pieceF_le_bulk {ι : Type*} (α : Fin (m + 1) → Fin 2 → ℝ) (γ₀ : Fin (m + 1))
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ c₁ KP : ℝ} (hρ₀ : 0 < ρ₀) (hc₁ : 0 < c₁) (hP : ∀ s l, ‖pp s l‖ ≤ KP) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s (z : Fin (m + 1) → ℝ), (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      z ∈ bulkSet α ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) z → ∀ u : ℝ, 0 ≤ u →
      ‖pieceF n (Q s) α (pp s) (M s) γ₀ u z‖ ≤ z γ₀ * (D * ((c₁ + z γ₀ * u) ^ 2)⁻¹) := by
  set B' := max BQ 0 with hB'
  have hB0 : 0 ≤ B' := le_max_right _ _
  have hQ' : LQBdd Q B' := ⟨fun i => (hQ.const i).trans (le_max_left _ _),
    fun i a => (hQ.lin i a).trans (le_max_left _ _),
    fun i a b => (hQ.quad i a b).trans (le_max_left _ _),
    fun i a b c => (hQ.cub i a b c).trans (le_max_left _ _),
    fun i a b c d => (hQ.quart i a b c d).trans (le_max_left _ _)⟩
  set g : ℝ := (ρ₀ ^ 3)⁻¹ with hg
  have hg0 : 0 ≤ g := by positivity
  set K : ℝ := 2 * g * max KP 0 with hK
  have hK0 : 0 ≤ K := by positivity
  set a : ℝ := 6 * (4681 * B' * (1 + K) ^ 4) * g ^ 2
  set b : ℝ := 26176 * B' * (1 + (K + K ^ 2)) * g * g ^ 2
  set c : ℝ := 4096 * B' * (3 * g ^ 2) * g ^ 2
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  refine ⟨(a + b + c) * (1 + c₁⁻¹) ^ 2, by positivity, fun s z hz hz1 hbulk hV u hu => ?_⟩
  have hU3 := symanzikU_ge_bulk hrow z hρ₀ hz hz1 hbulk
  have hU : 0 < symanzikU α z := lt_of_lt_of_le (by positivity) hU3
  have hUi : (symanzikU α z ^ 2)⁻¹ ≤ g ^ 2 := by
    rw [hg, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hU3 2)
  have hgent : ∀ r t, |(symanzikMatrix α z)⁻¹ r t| ≤ g := fun r t => by
    refine (abs_inv_le_chain (α := α) (hα := hrow) (hz := hz) (hU := hU.ne') r t).trans ?_
    rw [← sum_chain hrow z, hz1, hg, one_div]
    exact inv_anti₀ (by positivity) hU3
  have hP' : ∀ l, ‖pp s l‖ ≤ max KP 0 := fun l => (hP s l).trans (le_max_left _ _)
  have hX : ∀ a, ‖loopComp (-loopShift α (pp s) z) a‖ ≤ K := fun a => by
    simp only [loopComp, Complex.norm_real, Real.norm_eq_abs, Pi.neg_apply, abs_neg]
    exact abs_loopShift_le_bulk hrow hz hz1 hP' hgent a.1 a.2
  have key : ∀ {x y : ℝ}, 0 ≤ y → x ≤ y → x / symanzikU α z ^ 2 ≤ y * g ^ 2 := fun hy hxy => by
    rw [div_eq_mul_inv]
    exact mul_le_mul hxy hUi (by positivity) hy
  have hn7 : (n - 4).factorial ≤ (6 : ℝ) ∧ ((n - 5).factorial : ℝ) / 2 ≤ 1 := by
    rcases hn with rfl | ⟨rfl, -⟩ <;> norm_num [Nat.factorial]
  have h1 : ‖cOneAt n (Q s) α (pp s) z‖ ≤ a := by
    refine (norm_cOneAt_le (n := n) (α := α) (z := z) (hK := hK0) (hX := hX) (hU := hU)).trans
      (key (by positivity) ?_)
    exact mul_le_mul hn7.1 (mul_le_mul_of_nonneg_right (lqNorm_le hQ' s) (by positivity))
      (mul_nonneg (lqNorm_nonneg _) (by positivity)) (by norm_num)
  have h2 : ‖cTwoAt n (Q s) α (pp s) z‖ ≤ b := by
    refine (norm_cTwoAt_le (n := n) (α := α) (z := z) (hK := hK0) (hX := hX) (hU := hU)
      (hg := hgent)).trans (key (by positivity) ?_)
    have e : ((n - 5).factorial : ℝ) / 2 * (lqHess (Q s) * (1 + (K + K ^ 2)) * g) ≤
        1 * (26176 * B' * (1 + (K + K ^ 2)) * g) :=
      mul_le_mul hn7.2 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (lqHess_le hQ' s) (by positivity)) hg0)
        (mul_nonneg (mul_nonneg (lqHess_nonneg _) (by positivity)) hg0) (by norm_num)
    linarith
  have hv0 : 0 < c₁ + z γ₀ * u := by have := hz γ₀; positivity
  have hv : c₁ + z γ₀ * u ≤ symanzikV α (pp s) (M s) z + z γ₀ * u := by linarith
  have hvp : 0 < symanzikV α (pp s) (M s) z + z γ₀ * u := hv0.trans_le hv
  set v := symanzikV α (pp s) (M s) z + z γ₀ * u with hvdef
  have hcv : c₁ ≤ v := by have := hz γ₀; nlinarith
  have hpar : ‖paramAtV n (Q s) α (pp s) z v‖ ≤ (a + b + c) * (1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹ := by
    rcases hn with rfl | ⟨rfl, hq0⟩
    · have h3 : ‖cThreeAt 7 (Q s) α z‖ ≤ c := by
        refine (norm_cThreeAt_le (n := 7) (α := α) (z := z) (hU := hU) (hg := hgent)).trans
          (key (by positivity) ?_)
        have := lqQuart_le hQ' s
        norm_num [Nat.factorial]
        nlinarith [sq_nonneg g, lqQuart_nonneg (Q s)]
      refine (norm_paramAtV_le_of_coeff (hv := hvp) (h1 := h1) (h2 := h2) (h3 := h3)).trans ?_
      have e4 := inv_pow_le_sq hc₁ hcv (k := 7 - 3) (by norm_num) (by norm_num)
      have e3 := inv_pow_le_sq hc₁ hcv (k := 7 - 4) (by norm_num) (by norm_num)
      have e2 := inv_pow_le_sq hc₁ hcv (k := 7 - 5) (by norm_num) (by norm_num)
      have f4 := mul_le_mul_of_nonneg_left e4 ha
      have f3 := mul_le_mul_of_nonneg_left e3 hb
      have f2 := mul_le_mul_of_nonneg_left e2 hc
      rw [mul_assoc]
      have : (a + b + c) * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) = a * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) +
          b * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) + c * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) := by ring
      linarith
    · have h3 : ‖cThreeAt 6 (Q s) α z‖ ≤ 0 := by
        refine (norm_cThreeAt_le (n := 6) (α := α) (z := z) (hU := hU) (hg := hgent)).trans
          (le_of_eq ?_)
        simp [lqQuart, hq0 s]
      refine (norm_paramAtV_le_of_coeff (hv := hvp) (h1 := h1) (h2 := h2) (h3 := h3)).trans ?_
      have e3 := inv_pow_le_sq hc₁ hcv (k := 6 - 3) (by norm_num) (by norm_num)
      have e2 := inv_pow_le_sq hc₁ hcv (k := 6 - 4) (by norm_num) (by norm_num)
      have hw : 0 ≤ (1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹ := by positivity
      have f3 := mul_le_mul_of_nonneg_left e3 ha
      have f2 := mul_le_mul_of_nonneg_left e2 hb
      have fc : 0 ≤ c * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) := mul_nonneg hc hw
      rw [mul_assoc, zero_mul, add_zero]
      have : (a + b + c) * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) = a * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) +
          b * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) + c * ((1 + c₁⁻¹) ^ 2 * (v ^ 2)⁻¹) := by ring
      linarith
  have hvv : (v ^ 2)⁻¹ ≤ ((c₁ + z γ₀ * u) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hv0.le hv 2)
  rw [pieceF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hz γ₀)]
  refine mul_le_mul_of_nonneg_left (hpar.trans ?_) (hz γ₀)
  exact mul_le_mul_of_nonneg_left hvv (by positivity)

theorem bulk_scalar {t u c D : ℝ} (ht : 0 < t) (hu : 0 < u) (hc : 0 < c) (hD : 0 ≤ D) :
    u * (t * (D * ((c + t * u) ^ 2)⁻¹)) ≤
      D * c ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) * u ^ (-(1 / 2) : ℝ) := by
  have htu : 0 < t * u := mul_pos ht hu
  have h1 := inv_sq_add_le_rpow hc htu
  have h2 : t * u * (t * u) ^ (-(3 / 2) : ℝ) = t ^ (-(1 / 2) : ℝ) * u ^ (-(1 / 2) : ℝ) := by
    rw [← Real.mul_rpow ht.le hu.le]
    have e : t * u = (t * u) ^ (1 : ℝ) := (Real.rpow_one _).symm
    calc t * u * (t * u) ^ (-(3 / 2) : ℝ) = (t * u) ^ (1 : ℝ) * (t * u) ^ (-(3 / 2) : ℝ) := by
          rw [← e]
      _ = (t * u) ^ (-(1 / 2) : ℝ) := by rw [← Real.rpow_add htu]; norm_num
  calc u * (t * (D * ((c + t * u) ^ 2)⁻¹)) = D * (t * u * ((c + t * u) ^ 2)⁻¹) := by ring
    _ ≤ D * (t * u * (c ^ (-(1 / 2) : ℝ) * (t * u) ^ (-(3 / 2) : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 htu.le) hD
    _ = D * c ^ (-(1 / 2) : ℝ) * (t * u * (t * u) ^ (-(3 / 2) : ℝ)) := by ring
    _ = _ := by rw [h2]; ring

/-- **The bulk sector of a family of collapsed pieces, with rate `u^{-1/2}` uniform over the
family**: `‖u ∫_{bulk} pieceF‖ ≤ C u^{-1/2}` (`m > 0`; `V₀ ≥ c₁` on the bulk). -/
theorem bulk_rate {ι : Type*} (hm : 0 < m) (α : Fin (m + 1) → Fin 2 → ℝ) (γ₀ : Fin (m + 1))
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ c₁ KP : ℝ} (hρ₀ : 0 < ρ₀) (hc₁ : 0 < c₁) (hP : ∀ s l, ‖pp s l‖ ≤ KP)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → w ∈ bulkSet α ρ₀ →
      c₁ ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      ‖u • ∫ x in simplexSet m,
          (bulkSet α ρ₀).indicator (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)‖ ≤
        C * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨D, hD, hDb⟩ := norm_pieceF_le_bulk α γ₀ hrow pp M n Q hQ hn hρ₀ hc₁ hP
  have hI := integrableOn_simplexPoint_rpow hm γ₀
  set I := ∫ x in simplexSet m, simplexPoint x γ₀ ^ (-(1 / 2) : ℝ)
  refine ⟨D * c₁ ^ (-(1 / 2) : ℝ) * I, fun s u hu => ?_⟩
  have hg : ∀ x ∈ simplexSet m, ‖u • (bulkSet α ρ₀).indicator
      (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)‖ ≤
      D * c₁ ^ (-(1 / 2) : ℝ) * u ^ (-(1 / 2) : ℝ) * simplexPoint x γ₀ ^ (-(1 / 2) : ℝ) := by
    intro x hx
    obtain ⟨hz, hz1⟩ := simplexPoint_mem_stdSimplex hx
    have hR : 0 ≤ D * c₁ ^ (-(1 / 2) : ℝ) * u ^ (-(1 / 2) : ℝ) *
        simplexPoint x γ₀ ^ (-(1 / 2) : ℝ) := by
      have := hz γ₀
      positivity
    by_cases hb : simplexPoint x ∈ bulkSet α ρ₀
    · rw [indicator_of_mem hb, norm_smul, Real.norm_of_nonneg hu.le]
      rcases (hz γ₀).eq_or_lt with ht | ht
      · have : pieceF n (Q s) α (pp s) (M s) γ₀ u (simplexPoint x) = 0 := by
          rw [pieceF, ← ht]; simp
        rw [this, norm_zero, mul_zero]
        exact hR
      · refine (mul_le_mul_of_nonneg_left (hDb s _ hz hz1 hb (hV s _ hz hz1 hb) u hu.le)
          hu.le).trans ?_
        have := bulk_scalar ht hu hc₁ hD
        linarith
    · rw [indicator_of_notMem hb, smul_zero, norm_zero]
      exact hR
  rw [← integral_smul]
  refine (norm_integral_le_of_norm_le ((hI.const_mul (D * c₁ ^ (-(1 / 2) : ℝ) *
    u ^ (-(1 / 2) : ℝ)))) (ae_restrict_of_forall_mem (measurableSet_simplexSet m) hg)).trans
    (le_of_eq ?_)
  rw [integral_const_mul]
  ring

end QED.GradedProof.RPi4

end
