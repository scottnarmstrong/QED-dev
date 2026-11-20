/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdBridge

/-!
# (R-Π₄) step L6d3: three-line rests by duplicating a line

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The vertex
faces of the six-line pieces leave a one-loop rest of three lines with a constant numerator `C`;
its reduced functional is `∫_{Δ₂} C V̂⁻¹`. The one-loop limits through padded data
(`faceId_pvOf_pad`) need at least four one-loop lines, so the three-line integrand is written
with line `0` doubled and the numerator `C·D₀` (`D₀` the denominator of line `0`). This file
proves the parametric side of that rewriting:
`∫_{Δ₃} redBr(4, C·D₀) = ∫_{Δ₂} C V̂⁻¹` (the two copies of line `0` merge in join coordinates,
then one integration by parts in the merged weight `ρ`:
`(1 - ρ)/V - ρ(1 - ρ)(D₀/V² + 2/V) = (ρ(1 - ρ)²/V)'`).

* `faceIdDenQ`: the quartic `C·((ℓ₀ + p₀)² + M₀²)`; `faceId_eval_denQ_prop`,
  `faceId_cTwoG_denQ`, `faceId_loopDegLe_denQ`;
* `faceIdDupP`, `faceIdDupM`: the duplicated data; `faceId_VR_merge`, `faceId_dup_V_ge`;
* `faceId_blk_P0`, `faceId_blk_VR`: the shift and `V̂` at a join point of a block of copies;
* `faceId_dup_ibp`: the integration by parts;
* **`faceId_dup_three`**: the duplication identity;
* **`faceId_pvOf_dup`**: the padded one-loop value of `C·D₀` is `iπ² ∫_{Δ₂} C V̂⁻¹`;
* **`faceId_faceIdVal_vtx_six`**: the vertex face of a six-line piece is such a functional.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit
open QED.Integration.Feynman (simplexSet simplexPoint isCompact_simplexSet
  measurableSet_simplexSet simplexPoint_mem_stdSimplex)

/-! ### The integration by parts -/

/-- The one-loop `V` along the merged line: `ρ m + (1 - ρ) β + ρ(1 - ρ) δ`. -/
def faceIdDupV (m β δ ρ : ℝ) : ℝ := ρ * m + (1 - ρ) * β + ρ * (1 - ρ) * δ

/-- **The integration by parts of the duplication identity.** -/
theorem faceId_dup_ibp {m β δ : ℝ} (hV : ∀ ρ ∈ Icc (0 : ℝ) 1, 0 < faceIdDupV m β δ ρ) :
    ∫ ρ in (0 : ℝ)..1, ρ * (1 - ρ) * (((1 - ρ) ^ 2 * δ + m) / faceIdDupV m β δ ρ ^ 2 +
      2 / faceIdDupV m β δ ρ) = ∫ ρ in (0 : ℝ)..1, (1 - ρ) / faceIdDupV m β δ ρ := by
  set V := faceIdDupV m β δ with hVdef
  have hV' : ∀ ρ ∈ uIcc (0 : ℝ) 1, V ρ ≠ 0 := fun ρ hρ => by
    rw [uIcc_of_le zero_le_one] at hρ; exact (hV ρ hρ).ne'
  have hVd : ∀ ρ, HasDerivAt V (m - β + (1 - 2 * ρ) * δ) ρ := fun ρ => by
    have h : V = fun x => β + (m - β + δ) * x - δ * x ^ 2 := by
      funext x; simp only [hVdef, faceIdDupV]; ring
    rw [h]
    have := (((hasDerivAt_id ρ).const_mul (m - β + δ)).const_add β).sub
      ((hasDerivAt_pow 2 ρ).const_mul δ)
    convert this using 1
    · funext x; simp only [Pi.sub_apply, id]
    · norm_num; ring
  have hcV : Continuous V := by
    show Continuous fun ρ => ρ * m + (1 - ρ) * β + ρ * (1 - ρ) * δ
    fun_prop
  set F : ℝ → ℝ := fun ρ => ρ * (1 - ρ) ^ 2 / V ρ with hF
  have hderiv : ∀ ρ ∈ uIcc (0 : ℝ) 1, HasDerivAt F ((1 - ρ) / V ρ -
      ρ * (1 - ρ) * (((1 - ρ) ^ 2 * δ + m) / V ρ ^ 2 + 2 / V ρ)) ρ := by
    intro ρ hρ
    have hn : HasDerivAt (fun x : ℝ => x * (1 - x) ^ 2) ((1 - ρ) ^ 2 - 2 * ρ * (1 - ρ)) ρ := by
      have := (hasDerivAt_id' ρ).mul (((hasDerivAt_id' ρ).const_sub 1).pow 2)
      convert this using 1
      norm_num; ring
    have h := hn.div (hVd ρ) (hV' ρ hρ)
    convert h using 1
    have h0 := hV' ρ hρ
    simp only [hVdef, faceIdDupV] at h0 ⊢
    field_simp
    ring
  have hc1 : ContinuousOn (fun ρ => (1 - ρ) / V ρ) (uIcc (0 : ℝ) 1) :=
    (Continuous.continuousOn (by fun_prop)).div hcV.continuousOn hV'
  have hc2 : ContinuousOn (fun ρ => ρ * (1 - ρ) * (((1 - ρ) ^ 2 * δ + m) / V ρ ^ 2 +
      2 / V ρ)) (uIcc (0 : ℝ) 1) :=
    (Continuous.continuousOn (by fun_prop)).mul
      (((Continuous.continuousOn (by fun_prop)).div (hcV.pow 2).continuousOn
        fun ρ hρ => pow_ne_zero 2 (hV' ρ hρ)).add
        (continuousOn_const.div hcV.continuousOn hV'))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hc1.intervalIntegrable.sub hc2.intervalIntegrable)
  rw [intervalIntegral.integral_sub hc1.intervalIntegrable hc2.intervalIntegrable] at hFTC
  simp only [hF] at hFTC
  norm_num at hFTC
  linarith

/-! ### The denominator quartic -/

/-- **The denominator quartic** `C · (ℓ₀ + p₀)·(ℓ₀ + p₀) + C M₀²` (loop `0` only). -/
noncomputable def faceIdDenQ (C : ℂ) (p₀ : Fin 4 → ℝ) (M₀ : ℝ) : LoopQuartic where
  const := C * ((Minkowski.dot p₀ p₀ + M₀ ^ 2 : ℝ) : ℂ)
  lin a := if a.1 = 0 then C * ((2 * ∑ ν, Minkowski.metric a.2 ν * p₀ ν : ℝ) : ℂ) else 0
  quad a b := if a.1 = 0 ∧ b.1 = 0 then C * (Minkowski.metric a.2 b.2 : ℂ) else 0
  cub _ _ _ := 0
  quart _ _ _ _ := 0

section Den

variable (C : ℂ) (p₀ : Fin 4 → ℝ) (M₀ : ℝ)

/-- The value of the denominator quartic. -/
theorem faceId_eval_denQ (ℓ : Fin 2 → Fin 4 → ℝ) :
    (faceIdDenQ C p₀ M₀).eval ℓ =
      C * ((Minkowski.dot (ℓ 0 + p₀) (ℓ 0 + p₀) + M₀ ^ 2 : ℝ) : ℂ) := by
  simp only [LoopQuartic.eval, LoopQuartic.evalC, faceIdDenQ, loopComp, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_four, Minkowski.dot_eq, Minkowski.metric]
  simp
  ring

/-- The denominator quartic is `C` times the propagator denominator of the line. -/
theorem faceId_eval_denQ_prop (ℓ : Fin 2 → Fin 4 → ℝ) :
    (faceIdDenQ C p₀ M₀).eval ℓ = C * QED.TwoLoop.Bridge.propDenom M₀ 0 (ℓ 0 + p₀) := by
  rw [faceId_eval_denQ]
  simp [QED.TwoLoop.Bridge.propDenom]

/-- The half Laplacian of the denominator quartic in loop `0`: `4C`. -/
theorem faceId_cTwoG_denQ (X : LoopIndex → ℂ) : cTwoG (faceIdDenQ C p₀ M₀) (eS 0) X = 4 * C := by
  simp only [cTwoG, LoopQuartic.hess, LoopQuartic.quartSym, faceIdDenQ, gMet, eS,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four, Minkowski.metric]
  simp
  ring

/-- The denominator quartic has no quartic part. -/
theorem faceId_quart_denQ : (faceIdDenQ C p₀ M₀).quart = 0 := rfl

/-- The denominator quartic does not depend on loop `1`. -/
theorem faceId_loopDegLe_denQ : LoopDegLe 1 0 (faceIdDenQ C p₀ M₀) where
  lin a ha := by
    have : a.1 ≠ 0 := fun h => by simp [loopInd, h] at ha
    simp [faceIdDenQ, this]
  quad a b ha := by
    have : ¬(a.1 = 0 ∧ b.1 = 0) := fun h => by simp [loopInd, h.1, h.2] at ha
    simp only [faceIdDenQ, this, ite_false]
  cub _ _ _ _ := rfl
  quart _ _ _ _ _ := rfl

end Den

/-! ### A block of copies at a join point -/

section Block

variable {p q : ℕ} (p₀ : Fin 4 → ℝ) (M₀ : ℝ) (pT : Fin (q + 1) → Fin 4 → ℝ) (MT : Fin (q + 1) → ℝ)
  (ρ : ℝ) (a : Fin (p + 1) → ℝ) (b : Fin (q + 1) → ℝ)

/-- The shift at the join point `(ρa, (1 - ρ)b)` when the first block consists of copies of one
line: `ρp₀ + (1 - ρ)Q(b)`. -/
theorem faceId_blk_P0 (ha : ∑ i, a i = 1) :
    faceIdP0 (p := p + 1 + q) (Fin.append (m := p + 1) (n := q + 1) (fun _ : Fin (p + 1) => p₀) pT)
        (Fin.append (m := p + 1) (n := q + 1) (ρ • a) ((1 - ρ) • b)) =
      ρ • p₀ + (1 - ρ) • faceIdP0 pT b := by
  funext μ
  simp only [faceIdP0]
  erw [Fin.sum_univ_add (a := p + 1) (b := q + 1)]
  simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ha]
  simp only [faceIdP0, Finset.mul_sum, mul_one, mul_assoc]

/-- `V̂` at the join point: `ρM₀² + (1 - ρ)V̂(b) + ρ(1 - ρ)(p₀ - Q(b))²`. -/
theorem faceId_blk_VR (ha : ∑ i, a i = 1) :
    faceIdVR (p := p + 1 + q) (Fin.append (m := p + 1) (n := q + 1) (fun _ : Fin (p + 1) => p₀) pT)
        (Fin.append (m := p + 1) (n := q + 1) (fun _ : Fin (p + 1) => M₀) MT)
        (Fin.append (m := p + 1) (n := q + 1) (ρ • a) ((1 - ρ) • b)) =
      ρ * M₀ ^ 2 + (1 - ρ) * faceIdVR pT MT b +
        ρ * (1 - ρ) * Minkowski.dot (p₀ - faceIdP0 pT b) (p₀ - faceIdP0 pT b) := by
  unfold faceIdVR
  rw [faceId_blk_P0 p₀ pT ρ a b ha]
  erw [Fin.sum_univ_add (a := p + 1) (b := q + 1)]
  simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ha]
  simp only [mul_assoc, ← Finset.mul_sum]
  generalize ∑ j, b j * (MT j ^ 2 + Minkowski.dot (pT j) (pT j)) = S
  generalize faceIdP0 pT b = Q
  simp only [Minkowski.dot_eq, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Block

/-! ### The duplicated data and the merged point -/

/-- The duplicated four-line momenta: line `0` twice, then lines `1`, `2`. -/
def faceIdDupP (pR : Fin 3 → Fin 4 → ℝ) : Fin (1 + 1 + (1 + 1)) → Fin 4 → ℝ :=
  Fin.append (m := 1 + 1) (n := 1 + 1) (fun _ => pR 0) fun j => pR j.succ

/-- The duplicated four-line masses. -/
def faceIdDupM (MR : Fin 3 → ℝ) : Fin (1 + 1 + (1 + 1)) → ℝ :=
  Fin.append (m := 1 + 1) (n := 1 + 1) (fun _ => MR 0) fun j => MR j.succ

/-- Three-line data as a block of one line followed by two. -/
theorem faceId_three_append {X : Type*} (f : Fin 3 → X) :
    f = Fin.append (m := 0 + 1) (n := 1 + 1) (fun _ => f 0) fun j => f j.succ := by
  funext i
  fin_cases i <;> rfl

/-- The merged point: the weights of the two copies of line `0` added. -/
def faceIdMerge (z : Fin (1 + 1 + (1 + 1)) → ℝ) : Fin 3 → ℝ :=
  ![z (Fin.castAdd (1 + 1) 0) + z (Fin.castAdd (1 + 1) 1), z (Fin.natAdd (1 + 1) 0),
    z (Fin.natAdd (1 + 1) 1)]

section Merge

variable (pR : Fin 3 → Fin 4 → ℝ) (MR : Fin 3 → ℝ)

/-- The shift of the duplicated data is the shift at the merged point. -/
theorem faceId_P0_merge (z : Fin (1 + 1 + (1 + 1)) → ℝ) :
    faceIdP0 (faceIdDupP pR) z = faceIdP0 pR (faceIdMerge z) := by
  funext μ
  have e : (Fin.succ 0 : Fin (1 + 1)) = 1 := rfl
  simp only [faceIdP0]
  erw [Fin.sum_univ_add (a := 1 + 1) (b := 1 + 1)]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, faceIdDupP,
    Fin.append_left, Fin.append_right, faceIdMerge, Matrix.cons_val_zero, Matrix.cons_val_succ, e]
  ring

/-- `V̂` of the duplicated data is `V̂` at the merged point. -/
theorem faceId_VR_merge (z : Fin (1 + 1 + (1 + 1)) → ℝ) :
    faceIdVR (faceIdDupP pR) (faceIdDupM MR) z = faceIdVR pR MR (faceIdMerge z) := by
  have e : (Fin.succ 0 : Fin (1 + 1)) = 1 := rfl
  unfold faceIdVR
  rw [faceId_P0_merge]
  erw [Fin.sum_univ_add (a := 1 + 1) (b := 1 + 1)]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, faceIdDupP, faceIdDupM,
    Fin.append_left, Fin.append_right, faceIdMerge, Matrix.cons_val_zero, Matrix.cons_val_succ, e]
  ring

/-- The merged point of a point of the standard simplex lies in the standard simplex. -/
theorem faceId_merge_std {z : Fin (1 + 1 + (1 + 1)) → ℝ} (h0 : ∀ i, 0 ≤ z i)
    (h1 : ∑ i, z i = 1) : (∀ i, 0 ≤ faceIdMerge z i) ∧ ∑ i, faceIdMerge z i = 1 := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · exact add_nonneg (h0 _) (h0 _)
    · exact h0 _
    · exact h0 _
  · have e : (Fin.succ 0 : Fin (1 + 1)) = 1 := rfl
    erw [Fin.sum_univ_add (a := 1 + 1) (b := 1 + 1)] at h1
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, e] at h1
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, faceIdMerge,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    linarith

/-- **`V` of the duplicated data is bounded below on the simplex** when `V` of the three lines
is, at every point of the standard simplex. -/
theorem faceId_dup_V_ge {c : ℝ}
    (hV : ∀ z : Fin 3 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → c ≤ faceIdVR pR MR z) :
    ∀ x ∈ simplexSet 3, c ≤ faceIdVR (faceIdDupP pR) (faceIdDupM MR) (simplexPoint x) := by
  intro x hx
  obtain ⟨h0, h1⟩ := simplexPoint_mem_stdSimplex hx
  obtain ⟨g0, g1⟩ := faceId_merge_std h0 h1
  rw [faceId_VR_merge]
  exact hV _ g0 g1

end Merge

/-- **The reduced bracket of three lines** when the contractions vanish: `P(X) v⁻¹`. -/
theorem faceId_redBr_three {P : LoopQuartic} {X : LoopIndex → ℂ} (h2 : cTwoG P (eS 0) X = 0)
    (h4 : cFourG P (eS 0) = 0) (v : ℝ) :
    faceIdRedBr 3 P X v = P.evalC X * ((v : ℝ) : ℂ)⁻¹ := by
  simp [faceIdRedBr, h2, h4]

/-! ### Continuity and the join point -/

/-- The reduced bracket along the simplex is continuous where `V̂ ≠ 0`. -/
theorem faceId_continuousOn_redBr {p : ℕ} (pR : Fin (p + 1) → Fin 4 → ℝ) (MR : Fin (p + 1) → ℝ)
    (n : ℕ) (Q : LoopQuartic) {S : Set (Fin p → ℝ)}
    (hS : ∀ w ∈ S, faceIdVR pR MR (simplexPoint w) ≠ 0) :
    ContinuousOn (fun w => faceIdRedBr n Q (faceIdX0 (faceIdP0 pR (simplexPoint w)))
      (faceIdVR pR MR (simplexPoint w))) S := by
  have hV := faceId_continuous_VR pR MR
  have hX := faceId_continuous_X0 pR
  have hinv : ∀ k, ContinuousOn
      (fun w => (((faceIdVR pR MR (simplexPoint w) ^ k : ℝ) : ℂ))⁻¹) S := fun k =>
    (continuous_ofReal.comp (hV.pow k)).continuousOn.inv₀ fun w hw =>
      ofReal_ne_zero.2 (pow_ne_zero _ (hS w hw))
  unfold faceIdRedBr
  exact (((continuous_const.mul (faceId_continuous_evalC.comp hX)).continuousOn.mul
    (hinv _)).add ((continuous_const.mul ((faceId_continuous_cTwoG _).comp hX)).continuousOn.mul
      (hinv _))).add (continuousOn_const.mul (hinv _))

/-- A join point of two points of standard simplices lies in the standard simplex. -/
theorem faceId_join_std {p q : ℕ} {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) {a : Fin (p + 1) → ℝ}
    {b : Fin (q + 1) → ℝ} (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1) (hb0 : ∀ i, 0 ≤ b i)
    (hb1 : ∑ i, b i = 1) :
    (∀ i, 0 ≤ Fin.append (m := p + 1) (n := q + 1) (ρ • a) ((1 - ρ) • b) i) ∧
      ∑ i, Fin.append (m := p + 1) (n := q + 1) (ρ • a) ((1 - ρ) • b) i = 1 := by
  constructor
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact mul_nonneg hρ.1 (ha0 j)
    · rw [Fin.append_right]; exact mul_nonneg (sub_nonneg.2 hρ.2) (hb0 j)
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      ha1, hb1]
    ring

/-- `simplexPoint` maps `Δₘ` into the standard simplex. -/
theorem faceId_simplexPoint_std {m : ℕ} {x : Fin m → ℝ} (hx : x ∈ simplexSet m) :
    (∀ i, 0 ≤ simplexPoint x i) ∧ ∑ i, simplexPoint x i = 1 :=
  simplexPoint_mem_stdSimplex hx

/-- Every point of `ℝ⁰` lies in `Δ₀`. -/
theorem faceId_mem_simplexSet_zero (w : Fin 0 → ℝ) : w ∈ simplexSet 0 := by
  rw [mem_simplexSet_iff_forall]
  exact ⟨fun i => i.elim0, by simp⟩

/-! ### The duplication identity -/

section Main

variable (pR : Fin 3 → Fin 4 → ℝ) (MR : Fin 3 → ℝ)

/-- The shift of the last two lines at the point `v` of their simplex. -/
def faceIdDupQ (v : Fin 1 → ℝ) : Fin 4 → ℝ :=
  faceIdP0 (fun j : Fin (1 + 1) => pR j.succ) (simplexPoint v)

/-- `V̂` of the last two lines at `v`. -/
def faceIdDupB (v : Fin 1 → ℝ) : ℝ :=
  faceIdVR (fun j : Fin (1 + 1) => pR j.succ) (fun j => MR j.succ) (simplexPoint v)

/-- `(p₀ - Q(v))²`. -/
def faceIdDupD (v : Fin 1 → ℝ) : ℝ :=
  Minkowski.dot (pR 0 - faceIdDupQ pR v) (pR 0 - faceIdDupQ pR v)

/-- `V̂` of the three lines at a join point. -/
theorem faceId_dup_VR3 (ρ : ℝ) (w : Fin 0 → ℝ) (v : Fin 1 → ℝ) :
    faceIdVR pR MR (Fin.append (m := 0 + 1) (n := 1 + 1) (ρ • simplexPoint w)
      ((1 - ρ) • simplexPoint v)) =
      faceIdDupV (MR 0 ^ 2) (faceIdDupB pR MR v) (faceIdDupD pR v) ρ := by
  have h := faceId_blk_VR (p := 0) (q := 1) (pR 0) (MR 0) (fun j => pR j.succ)
    (fun j => MR j.succ) ρ (simplexPoint w) (simplexPoint v) (sum_simplexPoint w)
  rw [← faceId_three_append pR, ← faceId_three_append MR] at h
  exact h

/-- The reduced bracket of the duplicated data at a join point. -/
theorem faceId_dup_pt4 (C : ℂ) (ρ : ℝ) (w v : Fin 1 → ℝ) :
    faceIdRedBr 4 (faceIdDenQ C (pR 0) (MR 0))
        (faceIdX0 (faceIdP0 (faceIdDupP pR) (Fin.append (m := 1 + 1) (n := 1 + 1)
          (ρ • simplexPoint w) ((1 - ρ) • simplexPoint v))))
        (faceIdVR (faceIdDupP pR) (faceIdDupM MR) (Fin.append (m := 1 + 1) (n := 1 + 1)
          (ρ • simplexPoint w) ((1 - ρ) • simplexPoint v))) =
      C * ((((1 - ρ) ^ 2 * faceIdDupD pR v + MR 0 ^ 2) /
          faceIdDupV (MR 0 ^ 2) (faceIdDupB pR MR v) (faceIdDupD pR v) ρ ^ 2 +
        2 / faceIdDupV (MR 0 ^ 2) (faceIdDupB pR MR v) (faceIdDupD pR v) ρ : ℝ) : ℂ) := by
  have hP := faceId_blk_P0 (p := 1) (q := 1) (pR 0) (fun j => pR j.succ) ρ (simplexPoint w)
    (simplexPoint v) (sum_simplexPoint w)
  have hV := faceId_blk_VR (p := 1) (q := 1) (pR 0) (MR 0) (fun j => pR j.succ)
    (fun j => MR j.succ) ρ (simplexPoint w) (simplexPoint v) (sum_simplexPoint w)
  unfold faceIdDupP faceIdDupM
  rw [hP, hV]
  have hE := faceId_eval_denQ C (pR 0) (MR 0)
    ![-(ρ • pR 0 + (1 - ρ) • faceIdP0 (fun j : Fin (1 + 1) => pR j.succ) (simplexPoint v)), 0]
  have hd : Minkowski.dot
      ((![-(ρ • pR 0 + (1 - ρ) • faceIdP0 (fun j : Fin (1 + 1) => pR j.succ) (simplexPoint v)),
        0] : Fin 2 → Fin 4 → ℝ) 0 + pR 0)
      ((![-(ρ • pR 0 + (1 - ρ) • faceIdP0 (fun j : Fin (1 + 1) => pR j.succ) (simplexPoint v)),
        0] : Fin 2 → Fin 4 → ℝ) 0 + pR 0) = (1 - ρ) ^ 2 * faceIdDupD pR v := by
    simp only [faceIdDupD, faceIdDupQ, Matrix.cons_val_zero, Minkowski.dot_eq, Pi.add_apply,
      Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hd] at hE
  unfold faceIdRedBr faceIdX0
  rw [show (faceIdDenQ C (pR 0) (MR 0)).evalC (loopComp ![-(ρ • pR 0 + (1 - ρ) •
      faceIdP0 (fun j : Fin (1 + 1) => pR j.succ) (simplexPoint v)), 0]) = _ from hE,
    faceId_cTwoG_denQ, FaceBr.cFourG_of_quart (faceId_quart_denQ C (pR 0) (MR 0))]
  simp only [faceIdDupD, faceIdDupQ, faceIdDupB, faceIdDupV]
  norm_num [Nat.factorial]
  push_cast
  ring

/-- **The duplication identity of three-line rests.** The reduced functional of three lines with
a constant numerator `C` is the reduced functional of four lines, line `0` doubled, with the
numerator `C·D₀` (`D₀` the denominator of line `0`): `∫_{Δ₂} C V̂⁻¹ = ∫_{Δ₃} redBr(4, C·D₀)`. -/
theorem faceId_dup_three (C : ℂ) {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin 3 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → c ≤ faceIdVR pR MR z) :
    ∫ x in simplexSet 3, faceIdRedBr 4 (faceIdDenQ C (pR 0) (MR 0))
        (faceIdX0 (faceIdP0 (faceIdDupP pR) (simplexPoint x)))
        (faceIdVR (faceIdDupP pR) (faceIdDupM MR) (simplexPoint x)) =
      ∫ x in simplexSet 2, C * ((faceIdVR pR MR (simplexPoint x) : ℝ) : ℂ)⁻¹ := by
  set W : ℝ → (Fin 1 → ℝ) → ℝ := fun ρ v =>
    faceIdDupV (MR 0 ^ 2) (faceIdDupB pR MR v) (faceIdDupD pR v) ρ with hWdef
  have hW : ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ v ∈ simplexSet 1, c ≤ W ρ v := by
    intro ρ hρ v hv
    have w0 : Fin 0 → ℝ := fun i => i.elim0
    obtain ⟨h0, h1⟩ := faceId_join_std (p := 0) (q := 1) hρ
      (faceId_simplexPoint_std (faceId_mem_simplexSet_zero w0)).1 (sum_simplexPoint w0)
      (faceId_simplexPoint_std hv).1 (sum_simplexPoint v)
    have := hV _ h0 h1
    rwa [faceId_dup_VR3] at this
  have hV4 := faceId_dup_V_ge pR MR hV
  have hint4 : IntegrableOn (fun x : Fin (1 + 1 + 1) → ℝ =>
      faceIdRedBr 4 (faceIdDenQ C (pR 0) (MR 0))
        (faceIdX0 (faceIdP0 (faceIdDupP pR) (simplexPoint x)))
        (faceIdVR (faceIdDupP pR) (faceIdDupM MR) (simplexPoint x))) (simplexSet (1 + 1 + 1)) :=
    (faceId_continuousOn_redBr (faceIdDupP pR) (faceIdDupM MR) 4 _
      fun w hw => (hc.trans_le (hV4 w hw)).ne').integrableOn_compact (isCompact_simplexSet _)
  have hint3 : IntegrableOn (fun x : Fin (0 + 1 + 1) → ℝ =>
      C * ((faceIdVR pR MR (simplexPoint x) : ℝ) : ℂ)⁻¹) (simplexSet (0 + 1 + 1)) := by
    refine ContinuousOn.integrableOn_compact (isCompact_simplexSet _) ?_
    refine continuousOn_const.mul ((continuous_ofReal.comp
      (faceId_continuous_VR pR MR)).continuousOn.inv₀ fun x hx => ofReal_ne_zero.2 ?_)
    obtain ⟨h0, h1⟩ := faceId_simplexPoint_std hx
    exact (hc.trans_le (hV _ h0 h1)).ne'
  have h4 := integral_simplex_join (p := 1) (q := 1) (f := fun z =>
    faceIdRedBr 4 (faceIdDenQ C (pR 0) (MR 0)) (faceIdX0 (faceIdP0 (faceIdDupP pR) z))
      (faceIdVR (faceIdDupP pR) (faceIdDupM MR) z)) hint4
  have h3 := integral_simplex_join (p := 0) (q := 1)
    (f := fun z => C * ((faceIdVR pR MR z : ℝ) : ℂ)⁻¹) hint3
  refine h4.trans (Eq.trans ?_ h3.symm)
  have hvol1 : (volume (simplexSet 1)).toReal = 1 := by
    rw [faceId_volume_simplexSet]; norm_num
  have hvol0 : (volume (simplexSet 0)).toReal = 1 := by
    rw [faceId_volume_simplexSet]; norm_num
  have L : ∫ ρ in (0 : ℝ)..1, (ρ ^ 1 * (1 - ρ) ^ 1) • ∫ w in simplexSet 1, ∫ v in simplexSet 1,
      faceIdRedBr 4 (faceIdDenQ C (pR 0) (MR 0))
        (faceIdX0 (faceIdP0 (faceIdDupP pR) (Fin.append (m := 1 + 1) (n := 1 + 1)
          (ρ • simplexPoint w) ((1 - ρ) • simplexPoint v))))
        (faceIdVR (faceIdDupP pR) (faceIdDupM MR) (Fin.append (m := 1 + 1) (n := 1 + 1)
          (ρ • simplexPoint w) ((1 - ρ) • simplexPoint v))) =
      ∫ ρ in (0 : ℝ)..1, ∫ v in simplexSet 1, C * ((ρ * (1 - ρ) *
        (((1 - ρ) ^ 2 * faceIdDupD pR v + MR 0 ^ 2) / W ρ v ^ 2 + 2 / W ρ v) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun ρ _ => ?_
    simp only [faceId_dup_pt4, setIntegral_const, Measure.real, hvol1, one_smul]
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hWdef, Complex.real_smul]
    push_cast
    ring
  have R : ∫ ρ in (0 : ℝ)..1, (ρ ^ 0 * (1 - ρ) ^ 1) • ∫ w in simplexSet 0, ∫ v in simplexSet 1,
      C * ((faceIdVR pR MR (Fin.append (m := 0 + 1) (n := 1 + 1) (ρ • simplexPoint w)
        ((1 - ρ) • simplexPoint v)) : ℝ) : ℂ)⁻¹ =
      ∫ ρ in (0 : ℝ)..1, ∫ v in simplexSet 1, C * (((1 - ρ) / W ρ v : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun ρ _ => ?_
    simp only [faceId_dup_VR3, setIntegral_const, Measure.real, hvol0, one_smul]
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hWdef, Complex.real_smul]
    push_cast
    ring
  refine L.trans (Eq.trans ?_ R.symm)
  have hQ : Continuous (faceIdDupQ pR) := faceId_continuous_P0 _
  have hB : Continuous (faceIdDupB pR MR) := faceId_continuous_VR _ _
  have hD : Continuous (faceIdDupD pR) := by
    have h1 : Continuous fun v => pR 0 - faceIdDupQ pR v := continuous_const.sub hQ
    show Continuous fun v => Minkowski.dot (pR 0 - faceIdDupQ pR v) (pR 0 - faceIdDupQ pR v)
    simp only [Minkowski.dot_eq]
    fun_prop
  have hWc : Continuous fun q : ℝ × (Fin 1 → ℝ) => W q.1 q.2 := by
    simp only [hWdef, faceIdDupV]
    fun_prop
  have hne : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ simplexSet 1, W q.1 q.2 ≠ 0 := fun q hq =>
    (hc.trans_le (hW q.1 hq.1 q.2 hq.2)).ne'
  have hc4 : ContinuousOn (fun q : ℝ × (Fin 1 → ℝ) => C * ((q.1 * (1 - q.1) *
      (((1 - q.1) ^ 2 * faceIdDupD pR q.2 + MR 0 ^ 2) / W q.1 q.2 ^ 2 + 2 / W q.1 q.2) : ℝ) : ℂ))
      (Icc (0 : ℝ) 1 ×ˢ simplexSet 1) := by
    refine continuousOn_const.mul (continuous_ofReal.comp_continuousOn ?_)
    refine (Continuous.continuousOn (by fun_prop)).mul (ContinuousOn.add ?_ ?_)
    · exact (Continuous.continuousOn (by fun_prop)).div (hWc.pow 2).continuousOn
        fun q hq => pow_ne_zero 2 (hne q hq)
    · exact continuousOn_const.div hWc.continuousOn hne
  have hc3 : ContinuousOn (fun q : ℝ × (Fin 1 → ℝ) => C * (((1 - q.1) / W q.1 q.2 : ℝ) : ℂ))
      (Icc (0 : ℝ) 1 ×ˢ simplexSet 1) :=
    continuousOn_const.mul (continuous_ofReal.comp_continuousOn
      ((Continuous.continuousOn (by fun_prop)).div hWc.continuousOn hne))
  rw [faceId_integral_swap _ hc4, faceId_integral_swap _ hc3]
  refine setIntegral_congr_fun (measurableSet_simplexSet 1) fun v hv => ?_
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  congr 2
  exact faceId_dup_ibp fun ρ hρ => hc.trans_le (hW ρ hρ v hv)

/-- **Three-line rests as padded one-loop limits.** With the duplicated data, the one-loop value
of the numerator `C·D₀` through the padded data is `iπ² ∫_{Δ₂} C V̂⁻¹`, the reduced functional of
the three lines with the constant numerator `C`. -/
theorem faceId_pvOf_dup (C : ℂ) {m₀ c : ℝ} (hc : 0 < c) (hm₀ : 0 < m₀)
    (hV : ∀ z : Fin 3 → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → c ≤ faceIdVR pR MR z)
    (hint : IntegrableOn (QED.TwoLoop.ClassLimit.paramIntegrand (faceIdDenQ C (pR 0) (MR 0))
      (faceIdPadα (0 + 3)) (faceIdPadP (faceIdDupP pR)) (faceIdPadM (faceIdDupM MR) m₀) 0)
      (simplexSet (0 + 3 + 1 + 2))) :
    (auxLimit m₀)⁻¹ * pvOf (faceIdDenQ C (pR 0) (MR 0)).eval (faceIdPadα (0 + 3))
        (faceIdPadP (faceIdDupP pR)) (faceIdPadM (faceIdDupM MR) m₀) =
      I * (π : ℂ) ^ 2 * ∫ x in simplexSet 2, C * ((faceIdVR pR MR (simplexPoint x) : ℝ) : ℂ)⁻¹ := by
  rw [faceId_pvOf_pad (r := 0) ((faceId_loopDegLe_denQ C (pR 0) (MR 0)).mono zero_le_one)
    (fun _ => faceId_quart_denQ C (pR 0) (MR 0)) (faceIdDupP pR) (faceIdDupM MR) hc hm₀
    (faceId_dup_V_ge pR MR hV) rfl hint]
  congr 1
  exact faceId_dup_three pR MR C hc hV

end Main

/-- **The vertex face of a six-line piece** with a representative of degree at most two: the
three-line reduced functional `∫_{Δ₂} (C/2) V̂⁻¹` of the rest, `C` the constant half loop-`1`
Laplacian (`vol Δ₂ = 1/2`). With `faceId_dup_three` it is a four-line functional. -/
theorem faceId_faceIdVal_vtx_six (S : FaceShape (1 + 1) 2) {Q : LoopQuartic}
    (hQ : LoopDegLe 1 2 Q) (hq : Q.quart = 0) (hcub : Q.cub = 0) :
    faceIdVal 6 S Q = ∫ x in simplexSet 2,
      (faceIdLap Q).const / 2 * ((faceIdVR S.pR S.MR (simplexPoint x) : ℝ) : ℂ)⁻¹ := by
  have hE : ∀ X, (faceIdLap Q).evalC X = (faceIdLap Q).const := fun X => by
    simp [LoopQuartic.evalC, faceIdLap, hcub, hq, LoopQuartic.quartSym]
  have hvol : ((volume (simplexSet (1 + 1))).toReal : ℂ) = 1 / 2 := by
    rw [faceId_volume_simplexSet]; norm_num
  rw [faceId_faceIdVal_vtx S hQ (Or.inr ⟨rfl, hq⟩), hvol]
  unfold FaceShape.faceIdRedVal
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [faceId_redBr_three (faceId_cTwoG_faceIdLap_of_quart hq _ _) (faceId_cFourG_faceIdLap _ _),
    hE]
  have hv : S.mR (simplexPoint x) - Minkowski.dot (S.P0 (simplexPoint x)) (S.P0 (simplexPoint x))
      = faceIdVR S.pR S.MR (simplexPoint x) := rfl
  rw [hv]
  ring

end QED.GradedProof.RPi4

end
