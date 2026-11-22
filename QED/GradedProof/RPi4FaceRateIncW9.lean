/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncW8
public import QED.GradedProof.RPi4MajDPCov

/-!
# (R-Π₄) step L10, B-inc: differentiating a scaled family under the integral

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10, the rate (B) of
the face-rate increment. In the scaled frame a merged piece along the ray is
`F(τ) = ∑ᵢ cᵢ(τ) pieceF n Rᵢ (τ^{-1/2} M) (u/τ)` for fixed quartics `Rᵢ` and differentiable
weights `cᵢ`. If `∑ cᵢ'(τ) Rᵢ` and `τ⁻¹ ∑ cᵢ(τ) R''ᵢ` have the same value (the Euler numerator),
then pointwise (`faceIdRayD_hasDerivAt_pieceF`)

`∂_τ F = τ⁻¹ H(τ)`, `H(τ) = ∑ᵢ cᵢ(τ) (pieceF n R''ᵢ + pieceFd n Rᵢ - pieceFw (n + 1) Rᵢ)`.

On `τ ∈ (σ/2, 2σ)` the value `v ≥ c₀/(2σ)` (from `τ v ≥ c₀`), so all three terms are dominated
by the integrable coefficient bound of `faceIdRayE_norm_pieceF_le` and `faceIdRayD_norm_pieceFd_le`,
and the weights are bounded (compactness). Hence:

* `scaledSumF`, `scaledSumH`;
* **`faceIdRayE_hasDerivAt_scaled`**: `∂_τ ∫ F(τ) = τ⁻¹ ∫ H(τ)`, and `τ ↦ ∫ H(τ)` is continuous.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.TwoLoop.LimitCovariance (qsum eval_qsum)
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex
  measurableSet_simplexSet)

variable {m : ℕ} {κ : Type*}

/-- The scaled family `∑ᵢ cᵢ(τ) pieceF n Rᵢ (τ^{-1/2} M) (u/τ)`. -/
noncomputable def scaledSumF [Fintype κ] (n : ℕ) (cf : κ → ℝ → ℂ) (R : κ → LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (Ms : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (u τ : ℝ) (z : Fin (m + 1) → ℝ) : ℂ :=
  ∑ i, cf i τ * pieceF n (R i) α pp ((Real.sqrt τ)⁻¹ • Ms) γ (u / τ) z

/-- `τ` times its derivative: `∑ᵢ cᵢ(τ) (pieceF n R''ᵢ + pieceFd n Rᵢ - pieceFw (n + 1) Rᵢ)`. -/
noncomputable def scaledSumH [Fintype κ] (n : ℕ) (cf : κ → ℝ → ℂ) (R R'' : κ → LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (Ms : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (u τ : ℝ) (z : Fin (m + 1) → ℝ) : ℂ :=
  ∑ i, cf i τ * (pieceF n (R'' i) α pp ((Real.sqrt τ)⁻¹ • Ms) γ (u / τ) z +
    (pieceFd n (R i) α pp ((Real.sqrt τ)⁻¹ • Ms) γ (u / τ) z -
      pieceFw (n + 1) (R i) α pp ((Real.sqrt τ)⁻¹ • Ms) γ (u / τ) z))

/-- `pieceF` is linear in the quartic. -/
theorem faceIdRayE_pieceF_qsum (n : ℕ) (s : Finset κ) (w : κ → ℂ) (Q : κ → LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (u : ℝ) (z : Fin (m + 1) → ℝ) :
    pieceF n (qsum s w Q) α pp M γ u z = ∑ i ∈ s, w i * pieceF n (Q i) α pp M γ u z := by
  simp only [pieceF, paramAtV_qsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `pieceFd` is linear in the quartic. -/
theorem faceIdRayE_pieceFd_qsum (n : ℕ) (s : Finset κ) (w : κ → ℂ) (Q : κ → LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (u : ℝ) (z : Fin (m + 1) → ℝ) :
    pieceFd n (qsum s w Q) α pp M γ u z = ∑ i ∈ s, w i * pieceFd n (Q i) α pp M γ u z := by
  simp only [faceIdRayD_pieceFd_eq, faceIdRayE_pieceF_qsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `pieceFw` is linear in the quartic. -/
theorem faceIdRayE_pieceFw_qsum (n : ℕ) (s : Finset κ) (w : κ → ℂ) (Q : κ → LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) (u : ℝ) (z : Fin (m + 1) → ℝ) :
    pieceFw n (qsum s w Q) α pp M γ u z = ∑ i ∈ s, w i * pieceFw n (Q i) α pp M γ u z := by
  simp only [pieceFw, faceIdRayE_pieceF_qsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem faceIdRayE_pieceF_U_zero {n : ℕ} {Q : LoopQuartic} {α : Fin (m + 1) → Fin 2 → ℝ}
    {pp : Fin (m + 1) → Fin 4 → ℝ} {M : Fin (m + 1) → ℝ} {γ : Fin (m + 1)} (u : ℝ)
    {z : Fin (m + 1) → ℝ} (hU : symanzikU α z = 0) :
    pieceF n Q α pp M γ u z = 0 ∧ pieceFd n Q α pp M γ u z = 0 ∧
      pieceFw (n + 1) Q α pp M γ u z = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [pieceF, pieceFd, pieceFw, paramAtV, hU]

/-- The value `v` at the scaled data is continuous in the scale. -/
theorem faceIdRayE_continuousAt_v (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ)
    (Ms : Fin (m + 1) → ℝ) (γ : Fin (m + 1)) (u : ℝ) (z : Fin (m + 1) → ℝ) {σ : ℝ}
    (hσ : 0 < σ) :
    ContinuousAt (fun τ => (((symanzikV α pp ((Real.sqrt τ)⁻¹ • Ms) z + z γ * (u / τ) : ℝ)) : ℂ))
      σ := by
  have h : ContinuousAt (fun τ : ℝ => (((symanzikV α pp 0 z +
      τ⁻¹ * (∑ i, z i * Ms i ^ 2 + z γ * u) : ℝ)) : ℂ)) σ :=
    Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_const.add ((continuousAt_inv₀ hσ.ne').mul continuousAt_const))
  refine h.congr ?_
  filter_upwards [lt_mem_nhds hσ] with τ hτ
  rw [faceIdRayD_v_scaled α pp Ms γ u z hτ]

section Scaled

variable [Fintype κ] {n : ℕ} (hn : 6 ≤ n) (cf cf' : κ → ℝ → ℂ) (R R'' : κ → LoopQuartic)
  (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (Ms : Fin (m + 1) → ℝ)
  (γ₀ : Fin (m + 1)) {u : ℝ} (hu : 0 ≤ u)
  (hcf : ∀ i τ, 0 < τ → HasDerivAt (cf i) (cf' i τ) τ)
  (heval : ∀ τ, 0 < τ → (qsum Finset.univ (fun i => cf' i τ) R).eval =
    (qsum Finset.univ (fun i => ((τ⁻¹ : ℝ) : ℂ) * cf i τ) R'').eval)
  (kR : ∀ i,
    IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cOneAt n (R i) α pp (simplexPoint y))
      (simplexSet m) ∧
    IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cTwoAt n (R i) α pp (simplexPoint y))
      (simplexSet m) ∧
    IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cThreeAt n (R i) α (simplexPoint y))
      (simplexSet m))
  (kR'' : ∀ i,
    IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cOneAt n (R'' i) α pp (simplexPoint y))
      (simplexSet m) ∧
    IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cTwoAt n (R'' i) α pp (simplexPoint y))
      (simplexSet m) ∧
    IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cThreeAt n (R'' i) α (simplexPoint y))
      (simplexSet m))
  {c₀ : ℝ} (hc₀ : 0 < c₀)
  (hv : ∀ τ, 0 < τ → ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
    c₀ ≤ τ * (symanzikV α pp ((Real.sqrt τ)⁻¹ • Ms) (simplexPoint y) +
      simplexPoint y γ₀ * (u / τ)))
  (hB : ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
    0 ≤ symanzikV α pp 0 (simplexPoint y))

include hn hu hcf heval kR kR'' hc₀ hv hB

/-- **Differentiation of a scaled family under the integral**: at `σ > 0`,
`∂_τ ∫ F(τ) = σ⁻¹ ∫ H(σ)`, and `τ ↦ ∫ H(τ)` is continuous at `σ`. -/
theorem faceIdRayE_hasDerivAt_scaled {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun τ => ∫ y in simplexSet m,
        scaledSumF n cf R α pp Ms γ₀ u τ (simplexPoint y))
      (((σ⁻¹ : ℝ) : ℂ) * ∫ y in simplexSet m,
        scaledSumH n cf R R'' α pp Ms γ₀ u σ (simplexPoint y)) σ ∧
    ContinuousAt (fun τ => ∫ y in simplexSet m,
      scaledSumH n cf R R'' α pp Ms γ₀ u τ (simplexPoint y)) σ := by
  classical
  set S := simplexSet m
  set a : ℝ := σ / 2 with ha_def
  set b : ℝ := 2 * σ with hb_def
  have ha : 0 < a := by rw [ha_def]; positivity
  have haσ : a < σ := by rw [ha_def]; linarith
  have hσb : σ < b := by rw [hb_def]; linarith
  set I : Set ℝ := Ioo a b
  have hI : I ∈ 𝓝 σ := Ioo_mem_nhds haσ hσb
  have hIpos : ∀ τ ∈ I, 0 < τ := fun τ hτ => ha.trans hτ.1
  -- the weights are bounded on `[a, b]`
  have hKf : ∀ i, ∃ K, ∀ τ ∈ Icc a b, ‖cf i τ‖ ≤ K := fun i =>
    isCompact_Icc.exists_bound_of_continuousOn fun τ hτ =>
      (hcf i τ (ha.trans_le hτ.1)).continuousAt.continuousWithinAt
  choose Kf hKf using hKf
  set K : ℝ := ∑ i, |Kf i|
  have hK : ∀ i, ∀ τ ∈ I, ‖cf i τ‖ ≤ K := fun i τ hτ =>
    ((hKf i τ (Ioo_subset_Icc_self hτ)).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun j => |Kf j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => abs_nonneg _
  -- the lower bound of `v` on `I`
  set c₁ : ℝ := c₀ / b
  have hc₁ : 0 < c₁ := div_pos hc₀ (ha.trans (haσ.trans hσb))
  have hv₁ : ∀ τ ∈ I, ∀ y ∈ S, symanzikU α (simplexPoint y) ≠ 0 →
      c₁ ≤ symanzikV α pp ((Real.sqrt τ)⁻¹ • Ms) (simplexPoint y) +
        simplexPoint y γ₀ * (u / τ) := fun τ hτ y hy hU => by
    have h := hv τ (hIpos τ hτ) y hy hU
    have hτ0 := hIpos τ hτ
    set v := symanzikV α pp ((Real.sqrt τ)⁻¹ • Ms) (simplexPoint y) + simplexPoint y γ₀ * (u / τ)
    have hvp : 0 < v := by
      by_contra hcon
      have h' := le_of_not_gt hcon
      nlinarith
    have hb : τ * v ≤ b * v := mul_le_mul_of_nonneg_right hτ.2.le hvp.le
    rw [div_le_iff₀ (ha.trans (haσ.trans hσb))]
    linarith
  -- the coefficient bound
  set CB : LoopQuartic → (Fin m → ℝ) → ℝ := fun Q y =>
    ‖(simplexPoint y γ₀ : ℂ) * cOneAt n Q α pp (simplexPoint y)‖ * (c₁ ^ (n - 3))⁻¹ +
      ‖(simplexPoint y γ₀ : ℂ) * cTwoAt n Q α pp (simplexPoint y)‖ * (c₁ ^ (n - 4))⁻¹ +
      ‖(simplexPoint y γ₀ : ℂ) * cThreeAt n Q α (simplexPoint y)‖ * (c₁ ^ (n - 5))⁻¹
    with hCB
  have hCBi : ∀ Q, (IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) *
      cOneAt n Q α pp (simplexPoint y)) S ∧
      IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cTwoAt n Q α pp (simplexPoint y)) S ∧
      IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cThreeAt n Q α (simplexPoint y)) S) →
      IntegrableOn (CB Q) S := fun Q ⟨k1, k2, k3⟩ =>
    ((k1.norm.mul_const _).add (k2.norm.mul_const _)).add (k3.norm.mul_const _)
  set bnd : (Fin m → ℝ) → ℝ := fun y =>
    K * ∑ i, (CB (R'' i) y + 2 * ((n - 3 : ℕ) : ℝ) * CB (R i) y)
  have hbnd : IntegrableOn bnd S :=
    Integrable.const_mul (integrable_finsetSum _ fun i _ =>
      (hCBi _ (kR'' i)).add ((hCBi _ (kR i)).const_mul _)) K
  have hn3 : (0 : ℝ) ≤ ((n - 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hH : ∀ τ ∈ I, ∀ y ∈ S,
      ‖scaledSumH n cf R R'' α pp Ms γ₀ u τ (simplexPoint y)‖ ≤ bnd y := fun τ hτ y hy => by
    have hz := simplexPoint_mem_stdSimplex hy
    have huτ : 0 ≤ u / τ := div_nonneg hu (hIpos τ hτ).le
    have hvt := hv₁ τ hτ y hy
    have hBt := hB y hy
    have e1 : ∀ Q, ‖pieceF n Q α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀ (u / τ) (simplexPoint y)‖ ≤
        CB Q y := fun Q => faceIdRayE_norm_pieceF_le hc₁ (hz.1 γ₀) hvt
    have e2 : ∀ Q, ‖pieceFd n Q α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀ (u / τ) (simplexPoint y)‖ ≤
        ((n - 3 : ℕ) : ℝ) * CB Q y := fun Q =>
      (faceIdRayD_norm_pieceFd_le hn huτ hz.1 hBt).trans
        (mul_le_mul_of_nonneg_left (faceIdRayE_mul_absBr_le hc₁ (hz.1 γ₀) hvt) hn3)
    have e3 : ∀ Q, ‖pieceFw (n + 1) Q α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀ (u / τ)
        (simplexPoint y)‖ ≤ ((n - 3 : ℕ) : ℝ) * CB Q y := fun Q =>
      (faceIdRayD_norm_pieceFw_le hn huτ hz.1 hBt).trans
        (mul_le_mul_of_nonneg_left (faceIdRayE_mul_absBr_le hc₁ (hz.1 γ₀) hvt) hn3)
    refine (norm_sum_le _ _).trans ?_
    show _ ≤ K * ∑ i, (CB (R'' i) y + 2 * ((n - 3 : ℕ) : ℝ) * CB (R i) y)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul]
    refine mul_le_mul (hK i τ hτ) ?_ (norm_nonneg _) hK0
    calc _ ≤ ‖pieceF n (R'' i) α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀ (u / τ) (simplexPoint y)‖ +
          (‖pieceFd n (R i) α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀ (u / τ) (simplexPoint y)‖ +
            ‖pieceFw (n + 1) (R i) α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀ (u / τ)
              (simplexPoint y)‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
      _ ≤ _ := by linarith [e1 (R'' i), e2 (R i), e3 (R i)]
  -- integrability of the pieces at each `τ ∈ I`
  have hIF : ∀ τ ∈ I, ∀ Q, (IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) *
      cOneAt n Q α pp (simplexPoint y)) S ∧
      IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cTwoAt n Q α pp (simplexPoint y)) S ∧
      IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cThreeAt n Q α (simplexPoint y)) S) →
      IntegrableOn (fun y => pieceF n Q α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀ (u / τ)
        (simplexPoint y)) S ∧
      IntegrableOn (fun y => pieceFd n Q α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀ (u / τ)
        (simplexPoint y)) S ∧
      IntegrableOn (fun y => pieceFw (n + 1) Q α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀ (u / τ)
        (simplexPoint y)) S := fun τ hτ Q ⟨k1, k2, k3⟩ =>
    ⟨integrableOn_pieceF hc₁ k1 k2 k3 (hv₁ τ hτ),
      faceIdRayE_integrableOn_pieceFdw hn hc₁ (div_nonneg hu (hIpos τ hτ).le) k1 k2 k3
        (hv₁ τ hτ) hB⟩
  have hFint : ∀ τ ∈ I, IntegrableOn (fun y => scaledSumF n cf R α pp Ms γ₀ u τ
      (simplexPoint y)) S := fun τ hτ =>
    integrable_finsetSum _ fun i _ => ((hIF τ hτ (R i) (kR i)).1).const_mul _
  have hHint : ∀ τ ∈ I, IntegrableOn (fun y => scaledSumH n cf R R'' α pp Ms γ₀ u τ
      (simplexPoint y)) S := fun τ hτ =>
    integrable_finsetSum _ fun i _ => Integrable.const_mul (((hIF τ hτ (R'' i) (kR'' i)).1).add
      (((hIF τ hτ (R i) (kR i)).2.1).sub ((hIF τ hτ (R i) (kR i)).2.2))) _
  have hσI : σ ∈ I := ⟨haσ, hσb⟩
  -- the pointwise derivative
  have hdiff : ∀ y ∈ S, ∀ τ ∈ I, HasDerivAt
      (fun τ' => scaledSumF n cf R α pp Ms γ₀ u τ' (simplexPoint y))
      (((τ⁻¹ : ℝ) : ℂ) * scaledSumH n cf R R'' α pp Ms γ₀ u τ (simplexPoint y)) τ := by
    intro y hy τ hτ
    by_cases hU : symanzikU α (simplexPoint y) = 0
    · have h0 : (fun τ' => scaledSumF n cf R α pp Ms γ₀ u τ' (simplexPoint y)) = fun _ => 0 := by
        funext τ'
        simp only [scaledSumF, (faceIdRayE_pieceF_U_zero _ hU).1, mul_zero, Finset.sum_const_zero]
      have h1 : scaledSumH n cf R R'' α pp Ms γ₀ u τ (simplexPoint y) = 0 := by
        simp only [scaledSumH, (faceIdRayE_pieceF_U_zero _ hU).1,
          (faceIdRayE_pieceF_U_zero _ hU).2.1, (faceIdRayE_pieceF_U_zero _ hU).2.2]
        simp
      rw [h0, h1, mul_zero]
      exact hasDerivAt_const _ _
    · have hτ0 := hIpos τ hτ
      have hv0 : symanzikV α pp ((Real.sqrt τ)⁻¹ • Ms) (simplexPoint y) +
          simplexPoint y γ₀ * (u / τ) ≠ 0 := (hc₁.trans_le (hv₁ τ hτ y hy hU)).ne'
      have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hcf i τ hτ0).mul
        (faceIdRayD_hasDerivAt_pieceF hn (R i) α pp Ms γ₀ u (simplexPoint y) hτ0 hv0)
      refine h.congr_deriv ?_
      have hq : pieceF n (qsum Finset.univ (fun i => cf' i τ) R) α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀
          (u / τ) (simplexPoint y) = pieceF n (qsum Finset.univ
            (fun i => ((τ⁻¹ : ℝ) : ℂ) * cf i τ) R'') α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀ (u / τ)
          (simplexPoint y) := by
        simp only [pieceF, paramAtV_congr (heval τ hτ0)]
      rw [faceIdRayE_pieceF_qsum, faceIdRayE_pieceF_qsum] at hq
      rw [Finset.sum_add_distrib, hq, scaledSumH, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
  constructor
  · obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict S) (F := fun τ y => scaledSumF n cf R α pp Ms γ₀ u τ (simplexPoint y))
      (F' := fun τ y => ((τ⁻¹ : ℝ) : ℂ) * scaledSumH n cf R R'' α pp Ms γ₀ u τ (simplexPoint y))
      (bound := fun y => 2 / σ * bnd y) hI
      (by filter_upwards [hI] with τ hτ; exact (hFint τ hτ).aestronglyMeasurable)
      (hFint σ hσI) ((hHint σ hσI).const_mul _).aestronglyMeasurable
      (ae_restrict_of_forall_mem (measurableSet_simplexSet m) fun y hy τ hτ => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (hIpos τ hτ).le)]
        have h1 : τ⁻¹ ≤ 2 / σ := by
          rw [inv_le_comm₀ (hIpos τ hτ) (by positivity), inv_div]
          have := hτ.1
          rw [ha_def] at this
          exact this.le
        exact mul_le_mul h1 (hH τ hτ y hy) (norm_nonneg _) (by positivity))
      (hbnd.const_mul _)
      (ae_restrict_of_forall_mem (measurableSet_simplexSet m) fun y hy τ hτ => hdiff y hy τ hτ)
    rw [integral_const_mul] at hD
    exact hD
  · refine continuousAt_of_dominated (bound := bnd)
      (by filter_upwards [hI] with τ hτ; exact (hHint τ hτ).aestronglyMeasurable)
      (by
        filter_upwards [hI] with τ hτ
        exact ae_restrict_of_forall_mem (measurableSet_simplexSet m) fun y hy => hH τ hτ y hy)
      hbnd (ae_restrict_of_forall_mem (measurableSet_simplexSet m) fun y hy => ?_)
    by_cases hU : symanzikU α (simplexPoint y) = 0
    · have h0 : (fun τ => scaledSumH n cf R R'' α pp Ms γ₀ u τ (simplexPoint y)) =
          fun _ => 0 := by
        funext τ
        simp only [scaledSumH, (faceIdRayE_pieceF_U_zero _ hU).1,
          (faceIdRayE_pieceF_U_zero _ hU).2.1, (faceIdRayE_pieceF_U_zero _ hU).2.2]
        simp
      rw [h0]
      exact continuousAt_const
    · have hv0 : symanzikV α pp ((Real.sqrt σ)⁻¹ • Ms) (simplexPoint y) +
          simplexPoint y γ₀ * (u / σ) ≠ 0 := (hc₁.trans_le (hv₁ σ hσI y hy hU)).ne'
      have hP : ∀ Q, ContinuousAt (fun τ => pieceF (n + 1) Q α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀
          (u / τ) (simplexPoint y)) σ := fun Q =>
        (faceIdRayD_hasDerivAt_pieceF (n := n + 1) (by omega) Q α pp Ms γ₀ u (simplexPoint y)
          hσ hv0).continuousAt
      have hd : ∀ Q, ContinuousAt (fun τ => pieceFd n Q α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀
          (u / τ) (simplexPoint y)) σ := fun Q => by
        simp only [faceIdRayD_pieceFd_eq]
        exact (faceIdRayE_continuousAt_v α pp Ms γ₀ u _ hσ).mul (hP Q)
      have hw : ∀ Q, ContinuousAt (fun τ => pieceFw (n + 1) Q α pp ((Real.sqrt τ)⁻¹ • Ms) γ₀
          (u / τ) (simplexPoint y)) σ := fun Q => by
        simp only [pieceFw]
        exact continuousAt_const.mul (hP Q)
      exact tendsto_finsetSum _ fun i _ => ((hcf i σ hσ).continuousAt).mul
        (((faceIdRayD_hasDerivAt_pieceF hn (R'' i) α pp Ms γ₀ u (simplexPoint y) hσ
          hv0).continuousAt).add ((hd (R i)).sub (hw (R i))))

end Scaled

end QED.GradedProof.RPi4

end
