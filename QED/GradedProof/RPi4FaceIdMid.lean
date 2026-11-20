/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdShift
public import QED.GradedProof.RPi4FaceIdLapF

/-!
# (R-Π₄) step L6d3: the self-energy face average is a midpoint value

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The self-energy
face of a piece is the reduced one-loop functional of the `Δ₁`-average of `faceIdSET S Q`
(`faceId_faceIdVal_se_shift`), whose slice values are `∫ Q(ℓ₀, y(W)) dW` with `y` affine in the
face weights. A numerator of loop-`1` degree at most one is affine along loop `1`, so the average
is the value at the midpoint `W = (½, ½)`:

* `faceId_eval_add_sub_deg_one`, `faceId_integral_simplex_one_mid`, `faceId_simplexPoint_one`;
* `faceIdSEy` (the slice point), `faceId_seY_add`, `faceId_continuous_seY`;
* **`faceId_eval_avg_seT_mid`**: `(faceIdAvg (vol Δ₁) (faceIdSET S Q)).eval (ℓ₀, 0) =
  Q.eval (ℓ₀, y(½))`;
* `faceId_seY_half_01`, `faceId_seY_half_10`: `y(½) = (ℓ₀ + p_γ - p_f)/2` for the two orders of
  the face rows;
* `faceId_faceIdRedVal_slice` (the reduced functional sees the numerator on the slice `ℓ₁ = 0`
  only); the face values in the form used by the Dirac identities: **`faceId_faceIdVal_se_mid`**
  (`Q(ℓ₀, y(½)) = P(ℓ₀, 0)` ⇒ SE face `= faceIdRedVal (n - 2) P`) and
  **`faceId_faceIdVal_vtx_lapF`** (`faceIdLapF 1 Q.eval (ℓ₀, 0) = P(ℓ₀, 0)` ⇒ vertex face
  `= vol Δ₂ · faceIdRedVal (n - 3) P`).
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (simplexPoint_castSucc simplexPoint_last)

/-- **A numerator of loop-`1` degree at most one is affine along loop `1`.** -/
theorem faceId_eval_add_sub_deg_one {Q : LoopQuartic} (hQ : LoopDegLe 1 1 Q)
    (ℓ δ : Fin 2 → Fin 4 → ℝ) (hδ : δ 0 = 0) :
    Q.eval (ℓ + δ) + Q.eval (ℓ - δ) = 2 * Q.eval ℓ := by
  have h0 : ∀ a : LoopIndex, a.1 ≠ 1 → loopComp δ a = 0 := by
    rintro ⟨t, μ⟩ ht
    have : t = 0 := by fin_cases t <;> simp_all
    subst this
    simp [loopComp, hδ]
  have hH : ∑ a, ∑ b, Q.hess (loopComp ℓ) a b * (loopComp δ a * loopComp δ b) = 0 := by
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    by_cases ha : a.1 = 1
    · by_cases hb : b.1 = 1
      · rw [hess_eq_zero_of_loopDeg hQ _ ha hb, zero_mul]
      · rw [h0 b hb]; ring
    · rw [h0 a ha]; ring
  have hR : Q.quartPart (loopComp δ) = 0 := by
    simp only [LoopQuartic.quartPart]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    by_cases hall : a.1 = 1 ∧ b.1 = 1 ∧ c.1 = 1 ∧ d.1 = 1
    · rw [hQ.quart a b c d (by
        rw [loopInd_of_eq hall.1, loopInd_of_eq hall.2.1, loopInd_of_eq hall.2.2.1,
          loopInd_of_eq hall.2.2.2]; omega), zero_mul]
    · by_cases ha : a.1 = 1
      · by_cases hb : b.1 = 1
        · by_cases hc : c.1 = 1
          · rw [h0 d fun hd => hall ⟨ha, hb, hc, hd⟩]; ring
          · rw [h0 c hc]; ring
        · rw [h0 b hb]; ring
      · rw [h0 a ha]; ring
  rw [LoopQuartic.eval_add_add_eval_sub, hH, hR]
  ring

/-- **The average over `Δ₁` of a function symmetric about the midpoint**: if
`f t + f (1 - t) = 2c`, then `∫_{Δ₁} f(W₀) dW = c`. -/
theorem faceId_integral_simplex_one_mid {f : ℝ → ℂ} (hf : Continuous f) {c : ℂ}
    (h : ∀ t, f t + f (1 - t) = 2 * c) :
    ∫ W in simplexSet (0 + 1), f (W 0) = c := by
  have hset : simplexSet (0 + 1) = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Icc 0 1 := by
    ext W
    rw [mem_simplexSet_iff_forall]
    simp [MeasurableEquiv.funUnique, Fin.forall_fin_one]
  have e1 : ∫ W in simplexSet (0 + 1), f (W 0) = ∫ t in (0 : ℝ)..1, f t := by
    rw [hset, intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    exact (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding f (Icc 0 1)
  have e2 : ∫ t in (0 : ℝ)..1, f (1 - t) = ∫ t in (0 : ℝ)..1, f t := by
    rw [intervalIntegral.integral_comp_sub_left (fun t => f t) (1 : ℝ)]
    norm_num
  have hi : IntervalIntegrable f volume 0 1 := hf.intervalIntegrable 0 1
  have hi' : IntervalIntegrable (fun t => f (1 - t)) volume 0 1 :=
    (hf.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 1
  have e3 := intervalIntegral.integral_add hi hi'
  simp only [h, intervalIntegral.integral_const, sub_zero, e2] at e3
  rw [e1]
  rw [one_smul] at e3
  linear_combination -e3 / 2

theorem faceId_simplexPoint_one (W : Fin (0 + 1) → ℝ) : simplexPoint W = ![W 0, 1 - W 0] := by
  funext i
  fin_cases i
  · exact simplexPoint_castSucc W 0
  · simpa using simplexPoint_last W

/-- **The reduced functional sees the numerator on the slice `ℓ₁ = 0` only.** -/
theorem faceId_faceIdRedVal_slice {p q : ℕ} (S : FaceShape p q) (n : ℕ) {R P : LoopQuartic}
    (h : ∀ ℓ₀ : Fin 4 → ℝ, R.eval ![ℓ₀, 0] = P.eval ![ℓ₀, 0]) :
    S.faceIdRedVal n R = S.faceIdRedVal n P := by
  simp only [FaceShape.faceIdRedVal, faceIdX0]
  congr 1
  funext V
  exact faceId_faceIdRedBr_slice h n _ _

section SE

variable {q : ℕ} (S : FaceShape (0 + 1) q) {Q : LoopQuartic}

/-- The loop-`1` point of the self-energy slice at the face weights `(t, 1 - t)`. -/
noncomputable def faceIdSEy (ℓ₀ : Fin 4 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  -S.b₁ ![t, 1 - t] - S.b ![t, 1 - t] • ℓ₀

theorem faceId_seY_add (ℓ₀ : Fin 4 → ℝ) (t : ℝ) :
    faceIdSEy S ℓ₀ t + faceIdSEy S ℓ₀ (1 - t) = (2 : ℝ) • faceIdSEy S ℓ₀ (1 / 2) := by
  funext μ
  simp only [faceIdSEy, FaceShape.b, FaceShape.b₁, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  simp
  ring

theorem faceId_continuous_seY (ℓ₀ : Fin 4 → ℝ) : Continuous (faceIdSEy S ℓ₀) := by
  refine continuous_pi fun μ => ?_
  simp only [faceIdSEy, FaceShape.b, FaceShape.b₁, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  simp
  fun_prop

/-- **The self-energy average is the value at the midpoint of the face simplex** (numerator of
loop-`1` degree at most one). -/
theorem faceId_eval_avg_seT_mid (hQ : LoopDegLe 1 1 Q) (ℓ₀ : Fin 4 → ℝ) :
    (faceIdAvg (volume.restrict (simplexSet (0 + 1))) (faceIdSET S Q)).eval ![ℓ₀, 0] =
      Q.eval ![ℓ₀, faceIdSEy S ℓ₀ (1 / 2)] := by
  rw [faceId_eval_avg (faceId_coefInt_seT S Q)]
  have hW : ∀ W : Fin (0 + 1) → ℝ, (faceIdSET S Q W).eval ![ℓ₀, 0] =
      Q.eval ![ℓ₀, faceIdSEy S ℓ₀ (W 0)] := fun W => by
    rw [faceId_eval_seT, faceId_simplexPoint_one]
    rfl
  simp only [hW]
  refine faceId_integral_simplex_one_mid (f := fun t => Q.eval ![ℓ₀, faceIdSEy S ℓ₀ t]) ?_
    fun t => ?_
  · refine Q.continuous_eval.comp (continuous_pi fun i => ?_)
    fin_cases i
    · exact continuous_const
    · exact faceId_continuous_seY S ℓ₀
  · have hδ : (![0, faceIdSEy S ℓ₀ t - faceIdSEy S ℓ₀ (1 / 2)] : Fin 2 → Fin 4 → ℝ) 0 = 0 := rfl
    have h := faceId_eval_add_sub_deg_one hQ ![ℓ₀, faceIdSEy S ℓ₀ (1 / 2)] _ hδ
    have hy := faceId_seY_add S ℓ₀ t
    have e1 : (![ℓ₀, faceIdSEy S ℓ₀ (1 / 2)] : Fin 2 → Fin 4 → ℝ) +
        ![0, faceIdSEy S ℓ₀ t - faceIdSEy S ℓ₀ (1 / 2)] = ![ℓ₀, faceIdSEy S ℓ₀ t] := by
      funext i
      fin_cases i <;> simp
    have e2 : (![ℓ₀, faceIdSEy S ℓ₀ (1 / 2)] : Fin 2 → Fin 4 → ℝ) -
        ![0, faceIdSEy S ℓ₀ t - faceIdSEy S ℓ₀ (1 / 2)] = ![ℓ₀, faceIdSEy S ℓ₀ (1 - t)] := by
      funext i
      fin_cases i
      · simp
      · have hy' : faceIdSEy S ℓ₀ (1 - t) =
            (2 : ℝ) • faceIdSEy S ℓ₀ (1 / 2) - faceIdSEy S ℓ₀ t := by
          rw [← hy]; abel
        simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply, hy']
        funext μ
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
    rw [e1, e2] at h
    exact h

/-- The midpoint for the face rows `(0, 1)` (fermion, line `0`) and `(1, -1)` (photon, line `1`):
`y = (ℓ₀ + p_γ - p_f)/2`. -/
theorem faceId_seY_half_01 (h0 : S.αF 0 = ![0, 1]) (h1 : S.αF 1 = ![1, -1])
    (ℓ₀ : Fin 4 → ℝ) : faceIdSEy S ℓ₀ (1 / 2) = (1 / 2 : ℝ) • (ℓ₀ + S.pF 1 - S.pF 0) := by
  funext μ
  simp only [faceIdSEy, FaceShape.b, FaceShape.b₁, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  simp [h0, h1]
  ring

/-- The midpoint for the face rows `(1, -1)` (photon, line `0`) and `(0, 1)` (fermion, line `1`):
`y = (ℓ₀ + p_γ - p_f)/2`. -/
theorem faceId_seY_half_10 (h0 : S.αF 0 = ![1, -1]) (h1 : S.αF 1 = ![0, 1])
    (ℓ₀ : Fin 4 → ℝ) : faceIdSEy S ℓ₀ (1 / 2) = (1 / 2 : ℝ) • (ℓ₀ + S.pF 0 - S.pF 1) := by
  funext μ
  simp only [faceIdSEy, FaceShape.b, FaceShape.b₁, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  simp [h0, h1]
  ring

/-- **The SE face value through the midpoint**: if the numerator at the midpoint of the face
simplex is `P` on the slice, the face value is the reduced functional of `P`. -/
theorem faceId_faceIdVal_se_mid {n : ℕ} (hQ : LoopDegLe 1 1 Q)
    (hn : n = 7 ∨ (n = 6 ∧ Q.quart = 0))
    (hint : IntegrableOn (fun x : (Fin (0 + 1) → ℝ) × (Fin q → ℝ) =>
      faceIdRedBr (n - 2) (faceIdSET S Q x.1) (faceIdX0 (S.P0 (simplexPoint x.2)))
        (S.mR (simplexPoint x.2) -
          Minkowski.dot (S.P0 (simplexPoint x.2)) (S.P0 (simplexPoint x.2))))
      (simplexSet (0 + 1) ×ˢ simplexSet q))
    {P : LoopQuartic} (hP : ∀ ℓ₀ : Fin 4 → ℝ, Q.eval ![ℓ₀, faceIdSEy S ℓ₀ (1 / 2)] =
      P.eval ![ℓ₀, 0]) :
    faceIdVal n S Q = S.faceIdRedVal (n - 2) P := by
  rw [faceId_faceIdVal_se_shift S Q hQ hn hint]
  exact faceId_faceIdRedVal_slice S (n - 2) fun ℓ₀ => (faceId_eval_avg_seT_mid S hQ ℓ₀).trans
    (hP ℓ₀)

end SE

/-- **The vertex face value through the function-level Laplacian**: if the half loop-`1`
Laplacian of the numerator is `P` on the slice, the face value is `vol Δ₂` times the reduced
functional of `P`. -/
theorem faceId_faceIdVal_vtx_lapF {q n : ℕ} (S : FaceShape (1 + 1) q) {Q : LoopQuartic}
    (hQ : LoopDegLe 1 2 Q) (hn : n = 7 ∨ (n = 6 ∧ Q.quart = 0)) {P : LoopQuartic}
    (hP : ∀ ℓ₀ : Fin 4 → ℝ, faceIdLapF 1 Q.eval ![ℓ₀, 0] = P.eval ![ℓ₀, 0]) :
    faceIdVal n S Q =
      ((volume (simplexSet (1 + 1))).toReal : ℂ) * S.faceIdRedVal (n - 3) P := by
  rw [faceId_faceIdVal_vtx S hQ hn,
    faceId_faceIdRedVal_slice S (n - 3) fun ℓ₀ => (faceId_eval_faceIdLap hQ _).trans (hP ℓ₀)]

end QED.GradedProof.RPi4

end
