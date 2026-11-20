/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdSlice

/-!
# (R-Π₄) step L6d3: averaging the self-energy slice family

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The
self-energy face value is an integral over `Δ₁ × Δ_q` of reduced brackets of a family `T W` of
quartics (`faceId_faceIdVal_se_slice`). The reduced bracket is linear in the coefficients of the
quartic, so the `W`-integral may be taken coefficient by coefficient: the face value is the
reduced functional of the averaged quartic `faceIdAvg`, whose values are the `W`-averages of the
values of `T W` (the `θ`-average of the slices, to be identified with the insertion numerator).

* `FaceIdCoefInt` (integrable coefficients), `faceId_coefInt_of_continuous`, **`faceIdAvg`**;
* `faceId_evalC_avg`, `faceId_eval_avg`, `faceId_hess_avg`, `faceId_cTwoG_avg`,
  `faceId_cFourG_avg`, **`faceId_redBr_avg`**;
* **`faceId_faceIdVal_se_avg`**: the self-energy face value is
  `S.faceIdRedVal (n - 2) (faceIdAvg T)`.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

section Avg

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (T : α → LoopQuartic)

/-- Integrability of every coefficient of a family of quartics. -/
structure FaceIdCoefInt : Prop where
  const : Integrable (fun w => (T w).const) μ
  lin : ∀ a, Integrable (fun w => (T w).lin a) μ
  quad : ∀ a b, Integrable (fun w => (T w).quad a b) μ
  cub : ∀ a b c, Integrable (fun w => (T w).cub a b c) μ
  quart : ∀ a b c d, Integrable (fun w => (T w).quart a b c d) μ

/-- **The average of a family of quartics**, coefficient by coefficient. -/
noncomputable def faceIdAvg : LoopQuartic where
  const := ∫ w, (T w).const ∂μ
  lin a := ∫ w, (T w).lin a ∂μ
  quad a b := ∫ w, (T w).quad a b ∂μ
  cub a b c := ∫ w, (T w).cub a b c ∂μ
  quart a b c d := ∫ w, (T w).quart a b c d ∂μ

variable {μ T}

/-- The integral of a finite sum of integrable functions. -/
theorem faceId_integral_sum {ι : Type*} [Fintype ι] {F : ι → α → ℂ}
    (hF : ∀ i, Integrable (F i) μ) : ∫ w, ∑ i, F i w ∂μ = ∑ i, ∫ w, F i w ∂μ :=
  integral_finsetSum _ fun i _ => hF i

/-- A finite sum of integrable functions is integrable. -/
theorem faceId_integrable_sum {ι : Type*} [Fintype ι] {F : ι → α → ℂ}
    (hF : ∀ i, Integrable (F i) μ) : Integrable (fun w => ∑ i, F i w) μ :=
  integrable_finsetSum _ fun i _ => hF i

/-- The integral of a sum of three integrable functions. -/
theorem faceId_integral_add3 {f g k : α → ℂ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hk : Integrable k μ) :
    ∫ w, f w + g w + k w ∂μ = ∫ w, f w ∂μ + ∫ w, g w ∂μ + ∫ w, k w ∂μ := by
  rw [integral_add (f := fun w => f w + g w) (hf.add hg) hk, integral_add hf hg]

/-- **Integrable coefficients from continuous ones** on a compact set. -/
theorem faceId_coefInt_of_continuous [TopologicalSpace α] [T2Space α] [OpensMeasurableSpace α]
    [IsFiniteMeasureOnCompacts μ] {K : Set α} (hK : IsCompact K)
    (h0 : Continuous fun w => (T w).const) (h1 : ∀ a, Continuous fun w => (T w).lin a)
    (h2 : ∀ a b, Continuous fun w => (T w).quad a b)
    (h3 : ∀ a b c, Continuous fun w => (T w).cub a b c)
    (h4 : ∀ a b c d, Continuous fun w => (T w).quart a b c d) :
    FaceIdCoefInt (μ.restrict K) T where
  const := h0.continuousOn.integrableOn_compact hK
  lin a := (h1 a).continuousOn.integrableOn_compact hK
  quad a b := (h2 a b).continuousOn.integrableOn_compact hK
  cub a b c := (h3 a b c).continuousOn.integrableOn_compact hK
  quart a b c d := (h4 a b c d).continuousOn.integrableOn_compact hK

section Coef

variable (h : FaceIdCoefInt μ T)
include h

/-- The values of the family are integrable. -/
theorem FaceIdCoefInt.integrable_evalC (X : LoopIndex → ℂ) :
    Integrable (fun w => (T w).evalC X) μ := by
  unfold LoopQuartic.evalC
  refine (((h.const.add ?_).add ?_).add ?_).add ?_
  · exact faceId_integrable_sum fun a => (h.lin a).mul_const _
  · exact faceId_integrable_sum fun a => faceId_integrable_sum fun b => (h.quad a b).mul_const _
  · exact faceId_integrable_sum fun a => faceId_integrable_sum fun b =>
      faceId_integrable_sum fun c => (h.cub a b c).mul_const _
  · exact faceId_integrable_sum fun a => faceId_integrable_sum fun b =>
      faceId_integrable_sum fun c => faceId_integrable_sum fun d => (h.quart a b c d).mul_const _

/-- **The value of the average is the average of the values.** -/
theorem faceId_evalC_avg (X : LoopIndex → ℂ) :
    (faceIdAvg μ T).evalC X = ∫ w, (T w).evalC X ∂μ := by
  have h1 := faceId_integrable_sum fun a => (h.lin a).mul_const (X a)
  have h2 := faceId_integrable_sum fun a => faceId_integrable_sum fun b =>
    (h.quad a b).mul_const (X a * X b)
  have h3 := faceId_integrable_sum fun a => faceId_integrable_sum fun b =>
    faceId_integrable_sum fun c => (h.cub a b c).mul_const (X a * X b * X c)
  have h4 := faceId_integrable_sum fun a => faceId_integrable_sum fun b =>
    faceId_integrable_sum fun c => faceId_integrable_sum fun d =>
      (h.quart a b c d).mul_const (X a * X b * X c * X d)
  have i1 : Integrable (fun w => (T w).const + ∑ a, (T w).lin a * X a) μ := h.const.add h1
  have i2 : Integrable (fun w => (T w).const + ∑ a, (T w).lin a * X a +
      ∑ a, ∑ b, (T w).quad a b * (X a * X b)) μ := i1.add h2
  have i3 : Integrable (fun w => (T w).const + ∑ a, (T w).lin a * X a +
      ∑ a, ∑ b, (T w).quad a b * (X a * X b) +
      ∑ a, ∑ b, ∑ c, (T w).cub a b c * (X a * X b * X c)) μ := i2.add h3
  unfold LoopQuartic.evalC
  rw [integral_add i3 h4, integral_add i2 h3, integral_add i1 h2, integral_add h.const h1]
  simp only [faceIdAvg]
  rw [faceId_integral_sum fun a => (h.lin a).mul_const _,
    faceId_integral_sum fun a => faceId_integrable_sum fun b => (h.quad a b).mul_const _,
    faceId_integral_sum fun a => faceId_integrable_sum fun b =>
      faceId_integrable_sum fun c => (h.cub a b c).mul_const _,
    faceId_integral_sum fun a => faceId_integrable_sum fun b =>
      faceId_integrable_sum fun c => faceId_integrable_sum fun d =>
        (h.quart a b c d).mul_const _]
  simp only [faceId_integral_sum fun _ => (h.quad _ _).mul_const _,
    faceId_integral_sum fun _ => faceId_integrable_sum fun _ => (h.cub _ _ _).mul_const _,
    faceId_integral_sum fun _ => (h.cub _ _ _).mul_const _,
    faceId_integral_sum fun _ => faceId_integrable_sum fun _ => faceId_integrable_sum fun _ =>
      (h.quart _ _ _ _).mul_const _,
    faceId_integral_sum fun _ => faceId_integrable_sum fun _ => (h.quart _ _ _ _).mul_const _,
    faceId_integral_sum fun _ => (h.quart _ _ _ _).mul_const _, integral_mul_const]

/-- The value of the average is the average of the values. -/
theorem faceId_eval_avg (ℓ : Fin 2 → Fin 4 → ℝ) :
    (faceIdAvg μ T).eval ℓ = ∫ w, (T w).eval ℓ ∂μ :=
  faceId_evalC_avg h _

/-- The symmetrized quartic coefficients are integrable. -/
theorem FaceIdCoefInt.integrable_quartSym (a b c d : LoopIndex) :
    Integrable (fun w => (T w).quartSym a b c d) μ :=
  (((((h.quart a b c d).add (h.quart a c b d)).add (h.quart a c d b)).add
    (h.quart c a b d)).add (h.quart c a d b)).add (h.quart c d a b)

/-- The symmetrized quartic coefficients of the average. -/
theorem faceId_quartSym_avg (a b c d : LoopIndex) :
    (faceIdAvg μ T).quartSym a b c d = ∫ w, (T w).quartSym a b c d ∂μ := by
  have i3 : Integrable (fun w => (T w).quart a b c d + (T w).quart a c b d +
      (T w).quart a c d b) μ := ((h.quart a b c d).add (h.quart a c b d)).add (h.quart a c d b)
  have i4 : Integrable (fun w => (T w).quart a b c d + (T w).quart a c b d +
      (T w).quart a c d b + (T w).quart c a b d) μ := i3.add (h.quart c a b d)
  have i5 : Integrable (fun w => (T w).quart a b c d + (T w).quart a c b d +
      (T w).quart a c d b + (T w).quart c a b d + (T w).quart c a d b) μ :=
    i4.add (h.quart c a d b)
  unfold LoopQuartic.quartSym
  rw [integral_add i5 (h.quart c d a b), integral_add i4 (h.quart c a d b),
    integral_add i3 (h.quart c a b d),
    faceId_integral_add3 (h.quart a b c d) (h.quart a c b d) (h.quart a c d b)]
  rfl

/-- The Hessian coefficients are integrable. -/
theorem FaceIdCoefInt.integrable_hess (X : LoopIndex → ℂ) (a b : LoopIndex) :
    Integrable (fun w => (T w).hess X a b) μ := by
  unfold LoopQuartic.hess
  exact ((h.quad a b).add (faceId_integrable_sum fun c =>
    (((h.cub a b c).add (h.cub a c b)).add (h.cub c a b)).mul_const (X c))).add
    (faceId_integrable_sum fun c => faceId_integrable_sum fun d =>
      (h.integrable_quartSym a b c d).mul_const (X c * X d))

/-- The Hessian coefficients of the average. -/
theorem faceId_hess_avg (X : LoopIndex → ℂ) (a b : LoopIndex) :
    (faceIdAvg μ T).hess X a b = ∫ w, (T w).hess X a b ∂μ := by
  have hc : ∀ c, Integrable (fun w => ((T w).cub a b c + (T w).cub a c b + (T w).cub c a b) *
      X c) μ := fun c => (((h.cub a b c).add (h.cub a c b)).add (h.cub c a b)).mul_const _
  have hq : ∀ c d, Integrable (fun w => (T w).quartSym a b c d * (X c * X d)) μ :=
    fun c d => (h.integrable_quartSym a b c d).mul_const _
  have hq' : ∀ c, Integrable (fun w => ∑ d, (T w).quartSym a b c d * (X c * X d)) μ :=
    fun c => faceId_integrable_sum (hq c)
  unfold LoopQuartic.hess
  rw [faceId_integral_add3 (h.quad a b) (faceId_integrable_sum hc) (faceId_integrable_sum hq'),
    faceId_integral_sum hc, faceId_integral_sum hq']
  simp only [faceId_integral_sum (hq _), integral_mul_const, faceId_quartSym_avg h]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [faceId_integral_add3 (h.cub a b c) (h.cub a c b) (h.cub c a b)]
  rfl

/-- The quadratic contractions are integrable. -/
theorem FaceIdCoefInt.integrable_cTwoG (G : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) :
    Integrable (fun w => cTwoG (T w) G X) μ :=
  faceId_integrable_sum fun a => faceId_integrable_sum fun b =>
    (h.integrable_hess X a b).mul_const _

/-- The quadratic contraction of the average. -/
theorem faceId_cTwoG_avg (G : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) :
    cTwoG (faceIdAvg μ T) G X = ∫ w, cTwoG (T w) G X ∂μ := by
  unfold cTwoG
  rw [faceId_integral_sum fun a => faceId_integrable_sum fun b =>
    (h.integrable_hess X a b).mul_const _]
  simp only [faceId_integral_sum fun _ => (h.integrable_hess X _ _).mul_const _,
    integral_mul_const, faceId_hess_avg h]

/-- The quartic contractions are integrable. -/
theorem FaceIdCoefInt.integrable_cFourG (G : Matrix (Fin 2) (Fin 2) ℝ) :
    Integrable (fun w => cFourG (T w) G) μ :=
  faceId_integrable_sum fun a => faceId_integrable_sum fun b => faceId_integrable_sum fun c =>
    faceId_integrable_sum fun d => (h.quart a b c d).mul_const _

/-- The quartic contraction of the average. -/
theorem faceId_cFourG_avg (G : Matrix (Fin 2) (Fin 2) ℝ) :
    cFourG (faceIdAvg μ T) G = ∫ w, cFourG (T w) G ∂μ := by
  unfold cFourG
  rw [faceId_integral_sum fun a => faceId_integrable_sum fun b => faceId_integrable_sum fun c =>
    faceId_integrable_sum fun d => (h.quart a b c d).mul_const _]
  simp only [faceId_integral_sum fun _ => faceId_integrable_sum fun _ =>
      faceId_integrable_sum fun _ => (h.quart _ _ _ _).mul_const _,
    faceId_integral_sum fun _ => faceId_integrable_sum fun _ => (h.quart _ _ _ _).mul_const _,
    faceId_integral_sum fun _ => (h.quart _ _ _ _).mul_const _, integral_mul_const]
  rfl

/-- **The reduced bracket of the average is the average of the reduced brackets.** -/
theorem faceId_redBr_avg (n : ℕ) (X : LoopIndex → ℂ) (v : ℝ) :
    faceIdRedBr n (faceIdAvg μ T) X v = ∫ w, faceIdRedBr n (T w) X v ∂μ := by
  unfold faceIdRedBr
  rw [faceId_integral_add3 (((h.integrable_evalC X).const_mul _).mul_const _)
    (((h.integrable_cTwoG _ X).const_mul _).mul_const _)
    ((h.integrable_cFourG _).const_mul _ |>.mul_const _)]
  simp only [integral_mul_const, integral_const_mul, faceId_evalC_avg h, faceId_cTwoG_avg h,
    faceId_cFourG_avg h]

end Coef

end Avg

open QED.Integration.Feynman (simplexSet simplexPoint) in
/-- **The self-energy face value as one reduced functional**: for a family `T W` representing the
slices `ℓ₀ ↦ Q(ℓ₀, -b₁(W) - b(W)ℓ₀)` with integrable coefficients on `Δ₁`, the face value is the
reduced functional of the `W`-average of `T`. -/
theorem faceId_faceIdVal_se_avg {q n : ℕ} (S : FaceShape (0 + 1) q) {Q : LoopQuartic}
    (hQ : LoopDegLe 1 1 Q) (hn : n = 7 ∨ (n = 6 ∧ Q.quart = 0))
    (T : (Fin (0 + 1) → ℝ) → LoopQuartic)
    (hT : ∀ W ℓ₀, (T W).eval ![ℓ₀, 0] = Q.eval ![ℓ₀, -S.b₁ (simplexPoint W) -
      S.b (simplexPoint W) • ℓ₀])
    (hc : FaceIdCoefInt (volume.restrict (simplexSet (0 + 1))) T)
    (hint : IntegrableOn (fun x : (Fin (0 + 1) → ℝ) × (Fin q → ℝ) =>
      faceIdRedBr (n - 2) (T x.1) (faceIdX0 (S.P0 (simplexPoint x.2)))
        (S.mR (simplexPoint x.2) -
          Minkowski.dot (S.P0 (simplexPoint x.2)) (S.P0 (simplexPoint x.2))))
      (simplexSet (0 + 1) ×ˢ simplexSet q)) :
    faceIdVal n S Q =
      S.faceIdRedVal (n - 2) (faceIdAvg (volume.restrict (simplexSet (0 + 1))) T) := by
  rw [faceId_faceIdVal_se_slice S hQ hn T hT, Measure.volume_eq_prod, setIntegral_prod _ hint]
  have hint' : Integrable (Function.uncurry fun (W : Fin (0 + 1) → ℝ) (V : Fin q → ℝ) =>
      faceIdRedBr (n - 2) (T W) (faceIdX0 (S.P0 (simplexPoint V)))
        (S.mR (simplexPoint V) - Minkowski.dot (S.P0 (simplexPoint V)) (S.P0 (simplexPoint V))))
      ((volume.restrict (simplexSet (0 + 1))).prod (volume.restrict (simplexSet q))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hint
  rw [integral_integral_swap hint']
  unfold FaceShape.faceIdRedVal
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  exact (faceId_redBr_avg hc _ _ _).symm

end QED.GradedProof.RPi4

end
