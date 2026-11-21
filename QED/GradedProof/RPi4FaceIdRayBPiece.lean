/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayBFace
public import QED.GradedProof.RPi4Sectors

/-!
# (R-Π₄) step L10, T2.UV: the rate of one piece with the lower bound of `V₀` tracked

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (the rate input
(B) of `QED.GradedProof.RPi4.faceIdRay_of_size_rate`). `QED.GradedProof.RPi4.piece_rate` asks a
lower bound `V₀ ≥ c₀ · ferSum` common to the family. Here `c₀ s` is per member and the rate
constant is `C (1 + (c₀ s)⁻¹)^N` with `C`, `N` common: the two faces from
`QED.GradedProof.RPi4.faceIdRayB_face_rate_loop1` / `…_loop0`, the loop-UV corner from
`QED.GradedProof.RPi4.corner_rate` (it only asks `V₀ ≥ 0`), the bulk with `c₁` explicit:

* `faceIdRayB_quarter_le`: `(1 + (c/4)⁻¹)^j ≤ 4^N (1 + c⁻¹)^N`, `j ≤ N`;
* `faceIdRayB_norm_pieceF_le_bulk`, `faceIdRayB_bulk_rate`: the bulk, `C (1 + c₁⁻¹)³ u^{-1/2}`;
* **`faceIdRayB_piece_rate`**: `‖u ∫ pieceF - L‖ ≤ C (1 + (c₀ s)⁻¹)^N u^{-1/2}` for `u ≥ 1`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

/-- `(1 + (c/4)⁻¹)^j ≤ 4^N (1 + c⁻¹)^N` for `0 < c`, `j ≤ N`. -/
theorem faceIdRayB_quarter_le {c : ℝ} (hc : 0 < c) {N : ℕ} (j : ℕ) (hj : j ≤ N) :
    (1 + (c / 4)⁻¹) ^ j ≤ 4 ^ N * (1 + c⁻¹) ^ N := by
  have hi := inv_pos.2 hc
  have h1 : 1 + (c / 4)⁻¹ ≤ 4 * (1 + c⁻¹) := by
    rw [inv_div, div_eq_mul_inv]; linarith
  have h4 : 1 ≤ 4 * (1 + c⁻¹) := by linarith
  calc (1 + (c / 4)⁻¹) ^ j ≤ (4 * (1 + c⁻¹)) ^ j := pow_le_pow_left₀ (by positivity) h1 j
    _ ≤ (4 * (1 + c⁻¹)) ^ N := pow_le_pow_right₀ h4 hj
    _ = 4 ^ N * (1 + c⁻¹) ^ N := mul_pow _ _ _

/-- **The collapsed integrand on the bulk, with the lower bound tracked**:
`‖pieceF‖ ≤ t D (1 + c₁⁻¹)² (c₁ + t u)^{-2}`, `t = z_γ`, for every `c₁ ≤ V₀`, with `D` depending
only on the numerator bound, the momentum bound and `ρ₀` (`norm_pieceF_le_bulk` with `c₁`
explicit). -/
theorem faceIdRayB_norm_pieceF_le_bulk {ι : Type*} {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1))
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP : ℝ} (hρ₀ : 0 < ρ₀) (hP : ∀ s l, ‖pp s l‖ ≤ KP) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s (z : Fin (m + 1) → ℝ), (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      z ∈ bulkSet α ρ₀ → ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ symanzikV α (pp s) (M s) z → ∀ u : ℝ, 0 ≤ u →
      ‖pieceF n (Q s) α (pp s) (M s) γ₀ u z‖ ≤
        z γ₀ * (D * (1 + c₁⁻¹) ^ 2 * ((c₁ + z γ₀ * u) ^ 2)⁻¹) := by
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
  refine ⟨a + b + c, by positivity, fun s z hz hz1 hbulk c₁ hc₁ hV u hu => ?_⟩
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

/-- **The bulk sector of a family of collapsed pieces, with rate `C (1 + c₁⁻¹)³ u^{-1/2}`**
(`V₀ ≥ c₁ s` on the bulk, per member). -/
theorem faceIdRayB_bulk_rate {ι : Type*} {m : ℕ} (hm : 0 < m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1)) (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (pp : ι → Fin (m + 1) → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ) (n : ℕ)
    (Q : ι → LoopQuartic) {BQ : ℝ} (hQ : LQBdd Q BQ)
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0))
    {ρ₀ KP : ℝ} (hρ₀ : 0 < ρ₀) (hP : ∀ s l, ‖pp s l‖ ≤ KP) (c₁ : ι → ℝ) (hc₁ : ∀ s, 0 < c₁ s)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → w ∈ bulkSet α ρ₀ →
      c₁ s ≤ symanzikV α (pp s) (M s) w) :
    ∃ C : ℝ, ∀ s, ∀ u : ℝ, 0 < u →
      ‖u • ∫ x in simplexSet m,
          (bulkSet α ρ₀).indicator (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)‖ ≤
        C * (1 + (c₁ s)⁻¹) ^ 3 * u ^ (-(1 / 2) : ℝ) := by
  obtain ⟨D, hD, hDb⟩ := faceIdRayB_norm_pieceF_le_bulk α γ₀ hrow pp M n Q hQ hn hρ₀ hP
  have hI := integrableOn_simplexPoint_rpow hm γ₀
  set I := ∫ x in simplexSet m, simplexPoint x γ₀ ^ (-(1 / 2) : ℝ)
  refine ⟨D * |I|, fun s u hu => ?_⟩
  set c := c₁ s
  have hc := hc₁ s
  set D' := D * (1 + c⁻¹) ^ 2
  have hD' : 0 ≤ D' := by positivity
  have hg : ∀ x ∈ simplexSet m, ‖u • (bulkSet α ρ₀).indicator
      (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)‖ ≤
      D' * c ^ (-(1 / 2) : ℝ) * u ^ (-(1 / 2) : ℝ) * simplexPoint x γ₀ ^ (-(1 / 2) : ℝ) := by
    intro x hx
    obtain ⟨hz, hz1⟩ := simplexPoint_mem_stdSimplex hx
    have hR : 0 ≤ D' * c ^ (-(1 / 2) : ℝ) * u ^ (-(1 / 2) : ℝ) *
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
      · refine (mul_le_mul_of_nonneg_left (hDb s _ hz hz1 hb c hc (hV s _ hz hz1 hb) u hu.le)
          hu.le).trans ?_
        have := bulk_scalar ht hu hc hD'
        linarith
    · rw [indicator_of_notMem hb, smul_zero, norm_zero]
      exact hR
  rw [← integral_smul]
  refine (norm_integral_le_of_norm_le ((hI.const_mul (D' * c ^ (-(1 / 2) : ℝ) *
    u ^ (-(1 / 2) : ℝ)))) (ae_restrict_of_forall_mem (measurableSet_simplexSet m) hg)).trans ?_
  rw [integral_const_mul]
  have hr := faceIdRayB_rpow_le hc
  have hu' : 0 ≤ u ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hu.le _
  have hc' : 0 ≤ c ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hc.le _
  have h1 : D' * c ^ (-(1 / 2) : ℝ) ≤ D * (1 + c⁻¹) ^ 3 :=
    (mul_le_mul_of_nonneg_left hr hD').trans (le_of_eq (by simp only [D']; ring))
  calc D' * c ^ (-(1 / 2) : ℝ) * u ^ (-(1 / 2) : ℝ) * I
      ≤ D' * c ^ (-(1 / 2) : ℝ) * u ^ (-(1 / 2) : ℝ) * |I| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ ≤ D * (1 + c⁻¹) ^ 3 * u ^ (-(1 / 2) : ℝ) * |I| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hu') (abs_nonneg _)
    _ = D * |I| * (1 + c⁻¹) ^ 3 * u ^ (-(1 / 2) : ℝ) := by ring

/-- **The rate of one collapsed piece with the lower bound of `V₀` tracked**: as `piece_rate`,
with a per-member lower bound `V₀ ≥ c₀ s · ferSum`; the constant is `C (1 + (c₀ s)⁻¹)^N`. -/
theorem faceIdRayB_piece_rate {ι : Type*} {m n : ℕ} (hnm : n - 3 < m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1)) (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hA1 : 2 ≤ (Finset.univ.filter fun l => α l ≠ ![1, 0]).card) (hR1 : ∃ l, α l = ![1, 0])
    (hA0 : 2 ≤ (Finset.univ.filter fun l => α l ≠ ![0, 1]).card) (hR0 : ∃ l, α l = ![0, 1])
    (cs : Fin (m + 1) → ℝ) (k : ι → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ)
    (Q Q₁ Q₀ : ι → LoopQuartic) {BQ B₁ B₀ : ℝ} (hQ : LQBdd Q BQ) (hQ₁ : LQBdd Q₁ B₁)
    (hQ₀ : LQBdd Q₀ B₀) (he₁ : ∀ s, (Q₁ s).eval = (Q s).eval)
    (he₀ : ∀ s, (Q₀ s).eval = (Q s).eval)
    (hd1 : ∀ s, LoopDegLe 1 3 (Q₁ s))
    (hd11 : (Finset.univ.filter fun l => α l ≠ ![1, 0]).card = 2 → ∀ s, LoopDegLe 1 1 (Q₁ s))
    (hd0 : ∀ s, LoopDegLe 0 3 (Q₀ s))
    (hd01 : (Finset.univ.filter fun l => α l ≠ ![0, 1]).card = 2 → ∀ s, LoopDegLe 0 1 (Q₀ s))
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0 ∧ (Q₁ s).quart = 0 ∧ (Q₀ s).quart = 0))
    {KP KM : ℝ} (hk : ∀ s, ‖k s‖ ≤ KP) (hM : ∀ s l, |M s l| ≤ KM) (c₀ : ι → ℝ)
    (hc₀ : ∀ s, 0 < c₀ s)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → symanzikU α w ≠ 0 →
      c₀ s * ferSum α w ≤ symanzikV α (fun i => cs i • k s) (M s) w) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x))
        (simplexSet m) →
      ‖u • (∫ x in simplexSet m,
          pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x)) - L s‖ ≤
        C * (1 + (c₀ s)⁻¹) ^ N * u ^ (-(1 / 2) : ℝ) := by
  have hγ : α γ₀ = ![1, -1] := (huniq γ₀).mpr rfl
  set ρ₀ : ℝ := 1 / 4 with hρ₀
  set c₁ : ι → ℝ := fun s => c₀ s / 4 with hc₁
  have hc₁0 : ∀ s, 0 < c₁ s := fun s => by have := hc₀ s; simp only [hc₁]; positivity
  set pp : ι → Fin (m + 1) → Fin 4 → ℝ := fun s i => cs i • k s with hpp
  set KP' : ℝ := (∑ l, |cs l|) * KP
  have hP : ∀ s l, ‖pp s l‖ ≤ KP' := fun s l => by
    simp only [hpp, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (Finset.single_le_sum (f := fun l => |cs l|) (fun l _ => abs_nonneg _)
      (Finset.mem_univ l)) (hk s) (norm_nonneg _) (Finset.sum_nonneg fun l _ => abs_nonneg _)
  have hkμ : ∀ s μ, |k s μ| ≤ KP := fun s μ => (norm_le_pi_norm (k s) μ).trans (hk s)
  -- the lower bounds of `V₀` in the forms the four sectors ask for
  have hVface : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w γ₀ ≤ ρ₀ → c₁ s ≤ symanzikV α (pp s) (M s) w := fun s w hw hw1 hU h => by
    have := hV s w hw hw1 hU
    rw [ferSum_eq_one_sub huniq hw1] at this
    have h' : w γ₀ ≤ 1 / 4 := h
    have : c₀ s * (3 / 4) ≤ c₀ s * (1 - w γ₀) :=
      mul_le_mul_of_nonneg_left (by linarith) (hc₀ s).le
    have := hc₀ s
    show c₀ s / 4 ≤ _
    linarith
  have hVbulk : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      w ∈ bulkSet α ρ₀ → c₁ s ≤ symanzikV α (pp s) (M s) w := fun s w hw hw1 hb => by
    have hU := symanzikU_ge_bulk hrow w (by norm_num) hw hw1 hb
    have := hV s w hw hw1 (by positivity)
    have : c₀ s * (1 / 4) ≤ c₀ s * ferSum α w :=
      mul_le_mul_of_nonneg_left hb.2.2.le (hc₀ s).le
    show c₀ s / 4 ≤ _
    linarith
  have hVcorner : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      w ∈ cornerSet α ρ₀ → symanzikU α w ≠ 0 → 0 ≤ symanzikV α (pp s) (M s) w :=
    fun s w hw hw1 _ hU => by
      have := hV s w hw hw1 hU
      have : 0 ≤ c₀ s * ferSum α w := mul_nonneg (hc₀ s).le (Finset.sum_nonneg fun l _ => hw l)
      linarith
  have hm0 : 0 < m := by rcases hn with rfl | ⟨rfl, -⟩ <;> omega
  have hnQ : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0) := by
    rcases hn with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, fun s => (h' s).1⟩
  have hnQ₁ : n = 7 ∨ (n = 6 ∧ ∀ s, (Q₁ s).quart = 0) := by
    rcases hn with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, fun s => (h' s).2.1⟩
  have hnQ₀ : n = 7 ∨ (n = 6 ∧ ∀ s, (Q₀ s).quart = 0) := by
    rcases hn with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, fun s => (h' s).2.2⟩
  have hF : ∀ (P : ι → LoopQuartic), (∀ s, (P s).eval = (Q s).eval) →
      ∀ s, pieceF n (P s) α (pp s) (M s) γ₀ = pieceF n (Q s) α (pp s) (M s) γ₀ :=
    fun P hP s => by
      funext u z
      simp only [pieceF, paramAtV_congr (hP s)]
  obtain ⟨C₁, N₁, L₁, h₁⟩ := faceIdRayB_face_rate_loop1 α γ₀ hγ hrow hA1 hR1 pp M n Q₁ hQ₁ hd1
    hd11 hnQ₁ (by norm_num) (by norm_num) c₁ hc₁0 hP hM hVface
  obtain ⟨C₀, N₀, L₀, h₀⟩ := faceIdRayB_face_rate_loop0 α γ₀ hγ hrow hA0 hR0 pp M n Q₀ hQ₀ hd0
    hd01 hnQ₀ (by norm_num) (by norm_num) c₁ hc₁0 hP hM hVface
  simp only [hF Q₁ he₁] at h₁
  simp only [hF Q₀ he₀] at h₀
  obtain ⟨Cc, hc⟩ := corner_rate hnm α γ₀ huniq hrow cs k M Q hQ hnQ (by norm_num) (by norm_num)
    hkμ hVcorner
  obtain ⟨Cb, hb⟩ := faceIdRayB_bulk_rate hm0 α γ₀ hrow pp M n Q hQ hnQ (by norm_num) hP c₁ hc₁0
    hVbulk
  set N := N₁ + N₀ + 3
  refine ⟨(|C₁| + |C₀| + |Cc| + |Cb|) * 4 ^ N, N, fun s => L₁ s + L₀ s, fun s u hu hI => ?_⟩
  have hu0 : 0 < u := one_pos.trans_le hu
  have hsplit := integral_sector_eq hrow (ρ₀ := ρ₀) (by norm_num) hI
  have e1 := h₁ s u hu0 hI
  have e0 := h₀ s u hu0 hI
  have ec := hc s u hu
  have eb := hb s u hu0
  have hinv : u⁻¹ ≤ u ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
  have ec' : ‖u • ∫ x in simplexSet m, (cornerSet α ρ₀).indicator
      (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)‖ ≤ |Cc| * u ^ (-(1 / 2) : ℝ) :=
    ec.trans (mul_le_mul (le_abs_self _) hinv (by positivity) (abs_nonneg _))
  rw [hsplit, smul_add, smul_add, smul_add]
  set a := u • ∫ x in simplexSet m, {w | faceSum α w ≤ ρ₀}.indicator
    (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)
  set b := u • ∫ x in simplexSet m, {w | faceSum0 α w ≤ ρ₀}.indicator
    (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)
  set c := u • ∫ x in simplexSet m, (cornerSet α ρ₀).indicator
    (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)
  set d := u • ∫ x in simplexSet m, (bulkSet α ρ₀).indicator
    (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)
  have e : a + b + c + d - (L₁ s + L₀ s) = (a - L₁ s) + (b - L₀ s) + c + d := by ring
  rw [e]
  have hW := faceIdRayB_quarter_le (hc₀ s) (N := N)
  have w1 := hW N₁ (by omega)
  have w0 := hW N₀ (by omega)
  have wb := hW 3 (by omega)
  have hWN : 1 ≤ 4 ^ N * (1 + (c₀ s)⁻¹) ^ N := by
    have h1 : 1 ≤ 1 + (c₀ s)⁻¹ := by have := inv_pos.2 (hc₀ s); linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ h1)
  have hr : 0 ≤ u ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hu0.le _
  have hW1 : 0 ≤ 1 + (c₁ s)⁻¹ := by have := hc₁0 s; positivity
  set X := 4 ^ N * (1 + (c₀ s)⁻¹) ^ N
  have g1 : C₁ * (1 + (c₁ s)⁻¹) ^ N₁ * u ^ (-(1 / 2) : ℝ) ≤ |C₁| * X * u ^ (-(1 / 2) : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) w1 (pow_nonneg hW1 _) (abs_nonneg _)) hr
  have g0 : C₀ * (1 + (c₁ s)⁻¹) ^ N₀ * u ^ (-(1 / 2) : ℝ) ≤ |C₀| * X * u ^ (-(1 / 2) : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) w0 (pow_nonneg hW1 _) (abs_nonneg _)) hr
  have gb : Cb * (1 + (c₁ s)⁻¹) ^ 3 * u ^ (-(1 / 2) : ℝ) ≤ |Cb| * X * u ^ (-(1 / 2) : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) wb (pow_nonneg hW1 _) (abs_nonneg _)) hr
  have gc : |Cc| * u ^ (-(1 / 2) : ℝ) ≤ |Cc| * X * u ^ (-(1 / 2) : ℝ) :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (abs_nonneg _) hWN) hr
  calc ‖(a - L₁ s) + (b - L₀ s) + c + d‖ ≤ ‖a - L₁ s‖ + ‖b - L₀ s‖ + ‖c‖ + ‖d‖ :=
        norm_add₄_le
    _ ≤ C₁ * (1 + (c₁ s)⁻¹) ^ N₁ * u ^ (-(1 / 2) : ℝ) +
          C₀ * (1 + (c₁ s)⁻¹) ^ N₀ * u ^ (-(1 / 2) : ℝ) + |Cc| * u ^ (-(1 / 2) : ℝ) +
          Cb * (1 + (c₁ s)⁻¹) ^ 3 * u ^ (-(1 / 2) : ℝ) := by gcongr
    _ ≤ |C₁| * X * u ^ (-(1 / 2) : ℝ) + |C₀| * X * u ^ (-(1 / 2) : ℝ) +
          |Cc| * X * u ^ (-(1 / 2) : ℝ) + |Cb| * X * u ^ (-(1 / 2) : ℝ) := by linarith
    _ = _ := by simp only [X]; ring

end QED.GradedProof.RPi4

end
