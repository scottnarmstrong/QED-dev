/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdSE
public import QED.GradedProof.RPi4FaceIdBeta
public import QED.GradedProof.RPi4FaceBrInst
public import QED.GradedProof.RPi4FaceCoeff

/-!
# (R-Π₄) step L6d3: integrating out the auxiliary loop

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The limits of the
one-loop integrands are parametric values of padded two-loop data: the one-loop lines (row
`(1, 0)`) followed by three auxiliary lines (row `(0, 1)`, momentum `0`, mass `m₀`), divided by
the auxiliary loop (`QED.GradedProof.RPi4.tendsto_kinds`, `faceId_tendsto_kinds_cubic`). This file
integrates the auxiliary block out: for a numerator of loop-1 degree at most one, the parametric
integral of the padded data is `(2m₀²)⁻¹` times the reduced one-loop functional
`∫_Δ faceIdRedBr` of the one-loop lines (the functional of the face values,
`FaceShape.faceIdRedVal`).

At the join point `z = (ρ w, (1 - ρ) v)`: `A = diag(ρ, 1 - ρ)`, `U = ρ(1 - ρ)`, shift `(P₀(w), 0)`,
`V = ρ v̂(w) + (1 - ρ) m₀²`; the `v`-integral is `vol(Δ₂) = 1/2`, and the `ρ`-integrals are
`faceId_integral_beta`.

* `faceIdPadα`, `faceIdPadP`, `faceIdPadM`: the padded data; `faceIdP0`, `faceIdVR`: the one-loop
  shift and `V̂ = m_R - P₀²`; `faceIdPF`: the parametric integrand at a point;
* `faceId_pad_symanzikU`, `faceId_pad_inv`, `faceId_pad_symanzikV`, `faceId_pad_loopShift`: the
  join-point data; **`faceId_pad_pf`**: the integrand at the join point;
* `faceId_integral_swap`: Fubini on `[0, 1] × Δ` for continuous integrands;
* **`faceId_integral_pad`**: the parametric integral of the padded data.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint isCompact_simplexSet measurableSet_simplexSet)

/-! ### The padded data -/

section Data

variable {p : ℕ}

/-- The loop rows of the padded data: `(1, 0)` on the one-loop lines, `(0, 1)` on the three
auxiliary lines. -/
def faceIdPadα (p : ℕ) : Fin (p + 1 + (2 + 1)) → Fin 2 → ℝ :=
  Fin.append (fun _ : Fin (p + 1) => ![1, 0]) fun _ : Fin (2 + 1) => ![0, 1]

/-- The momenta of the padded data (`0` on the auxiliary lines). -/
def faceIdPadP (pR : Fin (p + 1) → Fin 4 → ℝ) : Fin (p + 1 + (2 + 1)) → Fin 4 → ℝ :=
  Fin.append pR fun _ => 0

/-- The masses of the padded data (`m₀` on the auxiliary lines). -/
def faceIdPadM (MR : Fin (p + 1) → ℝ) (m₀ : ℝ) : Fin (p + 1 + (2 + 1)) → ℝ :=
  Fin.append MR fun _ => m₀

/-- The one-loop shift `P₀(z) = ∑ zⱼ pⱼ`. -/
def faceIdP0 (pR : Fin (p + 1) → Fin 4 → ℝ) (z : Fin (p + 1) → ℝ) : Fin 4 → ℝ :=
  fun μ => ∑ j, z j * pR j μ

/-- The one-loop `V̂ = ∑ zⱼ (Mⱼ² + pⱼ²) - P₀²`. -/
def faceIdVR (pR : Fin (p + 1) → Fin 4 → ℝ) (MR : Fin (p + 1) → ℝ) (z : Fin (p + 1) → ℝ) : ℝ :=
  ∑ j, z j * (MR j ^ 2 + Minkowski.dot (pR j) (pR j)) -
    Minkowski.dot (faceIdP0 pR z) (faceIdP0 pR z)

end Data

/-- **The parametric integrand at a point `z`** (at `ε = 0`): `paramIntegrand Q α p M 0 x` is
`faceIdPF Q α p M (simplexPoint x)`. -/
noncomputable def faceIdPF {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ) : ℂ :=
  ((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ *
    (((m - 4).factorial : ℂ) *
        ((((symanzikV α p M z : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) ^ (m - 3))⁻¹ *
        P.eval (-loopShift α p z) +
      ((m - 5).factorial : ℂ) / 2 *
        ((((symanzikV α p M z : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) ^ (m - 4))⁻¹ *
        P.contractTwo (symanzikMatrix α z) (loopComp (-loopShift α p z)) +
      ((m - 6).factorial : ℂ) / 4 *
        ((((symanzikV α p M z : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) ^ (m - 5))⁻¹ *
        P.contractFour (symanzikMatrix α z))

theorem faceId_paramIntegrand_eq_pf {m : ℕ} (P : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (x : Fin m → ℝ) :
    QED.TwoLoop.ClassLimit.paramIntegrand P α p M 0 x = faceIdPF P α p M (simplexPoint x) :=
  rfl

/-! ### The data at the join point -/

section Join

variable {p : ℕ} (ρ : ℝ) (w : Fin p → ℝ) (v : Fin 2 → ℝ)

/-- The join point `(ρ w, (1 - ρ) v)`. -/
noncomputable def faceIdJz : Fin (p + 1 + (2 + 1)) → ℝ :=
  Fin.append (ρ • simplexPoint w) ((1 - ρ) • simplexPoint v)

theorem faceId_padα_rows (i : Fin (p + 1 + (2 + 1))) :
    faceIdPadα p i = ![1, 0] ∨ faceIdPadα p i = ![0, 1] ∨ faceIdPadα p i = ![1, -1] := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · left; simp [faceIdPadα]
  · right; left; simp [faceIdPadα]

theorem faceId_sum_pad {M : Type*} [AddCommMonoid M] (f : Fin (p + 1 + (2 + 1)) → M) :
    ∑ i, f i = ∑ i : Fin (p + 1), f (Fin.castAdd (2 + 1) i) +
      ∑ j : Fin (2 + 1), f (Fin.natAdd (p + 1) j) :=
  Fin.sum_univ_add f

theorem faceId_pad_chainZ :
    chainZ (faceIdPadα p) (faceIdJz ρ w v) ![1, 0] = ρ ∧
      chainZ (faceIdPadα p) (faceIdJz ρ w v) ![0, 1] = 1 - ρ ∧
      chainZ (faceIdPadα p) (faceIdJz ρ w v) ![1, -1] = 0 := by
  have h1 : (![0, 1] : Fin 2 → ℝ) ≠ ![1, 0] := fun h => by simpa using congrFun h 0
  have h2 : (![1, 0] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 1; norm_num at this
  have h3 : (![0, 1] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by simpa using congrFun h 0
  have hw := sum_simplexPoint w
  have hv := sum_simplexPoint v
  simp only [chainZ, faceId_sum_pad, faceIdPadα, faceIdJz, Fin.append_left, Fin.append_right,
    Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · simp only [ite_true, h1, ite_false, Finset.sum_const_zero, add_zero, ← Finset.mul_sum, hw,
      mul_one]
  · simp only [ite_true, h1.symm, ite_false, Finset.sum_const_zero, zero_add, ← Finset.mul_sum,
      hv, mul_one]
  · simp [h2, h3]

theorem faceId_pad_symanzikU :
    symanzikU (faceIdPadα p) (faceIdJz ρ w v) = ρ * (1 - ρ) := by
  obtain ⟨h1, h2, h3⟩ := faceId_pad_chainZ ρ w v
  rw [symanzikU_chain _ _ faceId_padα_rows, h1, h2, h3]
  ring

theorem faceId_pad_inv (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (symanzikMatrix (faceIdPadα p) (faceIdJz ρ w v))⁻¹ = ρ⁻¹ • eS 0 + (1 - ρ)⁻¹ • eS 1 := by
  obtain ⟨h00, h11, h01, h10⟩ := symanzikMatrix_inv_chain (faceIdPadα p) (faceIdJz ρ w v)
    faceId_padα_rows
  obtain ⟨c1, c2, c3⟩ := faceId_pad_chainZ ρ w v
  simp only [faceId_pad_symanzikU, c1, c2, c3] at h00 h11 h01 h10
  have h1ρ : (1 - ρ) ≠ 0 := by linarith
  ext s t
  fin_cases s <;> fin_cases t <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, h00, h11, h01, h10, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, eS] <;> norm_num <;> field_simp

/-- The vectors `B = (ρ P₀(w), 0)` at the join point. -/
theorem faceId_pad_vec (pR : Fin (p + 1) → Fin 4 → ℝ) (μ : Fin 4) :
    symanzikVector (faceIdPadα p) (faceIdPadP pR) (faceIdJz ρ w v) 0 μ =
        ρ * faceIdP0 pR (simplexPoint w) μ ∧
      symanzikVector (faceIdPadα p) (faceIdPadP pR) (faceIdJz ρ w v) 1 μ = 0 := by
  simp only [symanzikVector, faceId_sum_pad, faceIdPadα, faceIdPadP, faceIdJz, Fin.append_left,
    Fin.append_right, Pi.smul_apply, smul_eq_mul, faceIdP0, Finset.mul_sum]
  constructor
  · simp only [Matrix.cons_val_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp

theorem faceId_dot_smul (t : ℝ) (x : Fin 4 → ℝ) :
    Minkowski.dot (t • x) (t • x) = t ^ 2 * Minkowski.dot x x := by
  simp only [Minkowski.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **`V` at the join point**: `ρ v̂(w) + (1 - ρ) m₀²`. -/
theorem faceId_pad_symanzikV (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (pR : Fin (p + 1) → Fin 4 → ℝ)
    (MR : Fin (p + 1) → ℝ) (m₀ : ℝ) :
    symanzikV (faceIdPadα p) (faceIdPadP pR) (faceIdPadM MR m₀) (faceIdJz ρ w v) =
      ρ * faceIdVR pR MR (simplexPoint w) + (1 - ρ) * m₀ ^ 2 := by
  have hB0 : symanzikVector (faceIdPadα p) (faceIdPadP pR) (faceIdJz ρ w v) 0 =
      ρ • faceIdP0 pR (simplexPoint w) := funext fun μ => (faceId_pad_vec ρ w v pR μ).1
  have hB1 : symanzikVector (faceIdPadα p) (faceIdPadP pR) (faceIdJz ρ w v) 1 = 0 :=
    funext fun μ => (faceId_pad_vec ρ w v pR μ).2
  have hw := sum_simplexPoint w
  have hv := sum_simplexPoint v
  have h0 : Minkowski.dot (0 : Fin 4 → ℝ) 0 = 0 := by simp [Minkowski.dot]
  rw [symanzikV, faceId_pad_inv ρ w v hρ0 hρ1, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two, hB0, hB1, faceId_sum_pad]
  simp only [faceIdPadP, faceIdPadM, faceIdJz, Fin.append_left, Fin.append_right, Pi.smul_apply,
    smul_eq_mul, h0, add_zero, Matrix.add_apply, Matrix.smul_apply, eS, faceId_dot_smul]
  have hr : ∑ i : Fin (2 + 1), (1 - ρ) * simplexPoint v i * m₀ ^ 2 = (1 - ρ) * m₀ ^ 2 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hv, mul_one]
  rw [hr]
  have h1ρ : (1 - ρ) ≠ 0 := by linarith
  simp only [faceIdVR, Fin.isValue, and_self, ite_true, mul_one, zero_ne_one, and_false,
    ite_false, mul_zero, add_zero, one_ne_zero, false_and, zero_add, zero_mul]
  simp only [mul_assoc, ← Finset.mul_sum]
  field_simp
  ring

/-- **The shift at the join point**: `(P₀(w), 0)`. -/
theorem faceId_pad_loopShift (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (pR : Fin (p + 1) → Fin 4 → ℝ) :
    loopShift (faceIdPadα p) (faceIdPadP pR) (faceIdJz ρ w v) =
      ![faceIdP0 pR (simplexPoint w), 0] := by
  have hc : ∀ μ, coefVec (faceIdPadα p) (faceIdJz ρ w v) (fun i => faceIdPadP pR i μ) =
      ![ρ * faceIdP0 pR (simplexPoint w) μ, 0] := fun μ => funext fun s => by
    fin_cases s
    · exact (faceId_pad_vec ρ w v pR μ).1
    · exact (faceId_pad_vec ρ w v pR μ).2
  have hρ : ρ ≠ 0 := hρ0.ne'
  funext s μ
  refine Fin.cases ?_ (fun c => ?_) μ
  · simp only [loopShift, loopMomenta, Fin.cons_zero, energyShift, hc,
      faceId_pad_inv ρ w v hρ0 hρ1]
    fin_cases s <;> simp [Matrix.mulVec, dotProduct, eS, hρ]
  · simp only [loopShift, loopMomenta, Fin.cons_succ, spatialShift, hc,
      faceId_pad_inv ρ w v hρ0 hρ1]
    fin_cases s <;> simp [Matrix.mulVec, dotProduct, eS, hρ]

theorem faceId_cTwoG_pad {Q : LoopQuartic} (hQ : LoopDegLe 1 1 Q) (a b : ℝ)
    (X : LoopIndex → ℂ) : cTwoG Q (a • eS 0 + b • eS 1) X = a * cTwoG Q (eS 0) X := by
  have h0 : cTwoG Q 0 X = 0 := by simp [cTwoG, gMet]
  have h := cTwoG_add_smul Q 0 (eS 0) a X
  rw [zero_add, h0, zero_add] at h
  rw [cTwoG_add_smul, faceId_cTwoG_eS1_deg1 hQ, h, mul_zero, add_zero]

theorem faceId_cFourG_pad {Q : LoopQuartic} (hQ : LoopDegLe 1 1 Q) (a b : ℝ) :
    cFourG Q (a • eS 0 + b • eS 1) = a ^ 2 * cFourG Q (eS 0) := by
  have h0 : cFourG Q 0 = 0 := by simp [cFourG, gMet, matPair]
  have h0' : cFourX Q 0 (eS 0) = 0 := by simp [cFourX, gMet, pairX]
  have h := cFourG_add_smul Q 0 (eS 0) a
  rw [zero_add, h0, h0', zero_add, mul_zero, zero_add] at h
  rw [cFourG_add_smul, faceId_cFourX_eS1_deg1 hQ, cFourG_eS (hQ.mono (by norm_num)), h]
  ring

theorem faceId_neg_pair (P : Fin 4 → ℝ) : -(![P, 0] : Fin 2 → Fin 4 → ℝ) = ![-P, 0] := by
  funext s
  fin_cases s <;> simp

/-- **The parametric integrand at the join point** (`0 < ρ < 1`, loop-1 degree at most one):
`(ρ(1 - ρ))⁻² [(m-4)! N(X̂) W^{3-m} + (m-5)!/2 ρ⁻¹ c₂ W^{4-m} + (m-6)!/4 ρ⁻² c₄ W^{5-m}]`,
`W = ρ v̂(w) + (1 - ρ) m₀²`, `X̂ = (-P₀(w), 0)`. -/
theorem faceId_pad_pf (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {Q : LoopQuartic} (hQ : LoopDegLe 1 1 Q)
    (pR : Fin (p + 1) → Fin 4 → ℝ) (MR : Fin (p + 1) → ℝ) (m₀ : ℝ) :
    faceIdPF Q (faceIdPadα p) (faceIdPadP pR) (faceIdPadM MR m₀) (faceIdJz ρ w v) =
      (((ρ * (1 - ρ)) ^ 2 : ℝ) : ℂ)⁻¹ *
        (((p + 1 + 2 - 4).factorial : ℂ) *
            ((((ρ * faceIdVR pR MR (simplexPoint w) + (1 - ρ) * m₀ ^ 2 : ℝ) : ℂ)) ^
              (p + 1 + 2 - 3))⁻¹ * Q.evalC (faceIdX0 (faceIdP0 pR (simplexPoint w))) +
          ((p + 1 + 2 - 5).factorial : ℂ) / 2 *
            ((((ρ * faceIdVR pR MR (simplexPoint w) + (1 - ρ) * m₀ ^ 2 : ℝ) : ℂ)) ^
              (p + 1 + 2 - 4))⁻¹ *
            ((ρ⁻¹ : ℝ) * cTwoG Q (eS 0) (faceIdX0 (faceIdP0 pR (simplexPoint w)))) +
          ((p + 1 + 2 - 6).factorial : ℂ) / 4 *
            ((((ρ * faceIdVR pR MR (simplexPoint w) + (1 - ρ) * m₀ ^ 2 : ℝ) : ℂ)) ^
              (p + 1 + 2 - 5))⁻¹ * (((ρ⁻¹ ^ 2 : ℝ) : ℂ) * cFourG Q (eS 0))) := by
  have hX : loopComp (-loopShift (faceIdPadα p) (faceIdPadP pR) (faceIdJz ρ w v)) =
      faceIdX0 (faceIdP0 pR (simplexPoint w)) := by
    rw [faceId_pad_loopShift ρ w v hρ0 hρ1, faceId_neg_pair]
    rfl
  simp only [faceIdPF, LoopQuartic.eval, hX, contractTwo_eq_cTwoG, contractFour_eq_cFourG,
    faceId_pad_inv ρ w v hρ0 hρ1, faceId_cTwoG_pad hQ, faceId_cFourG_pad hQ,
    faceId_pad_symanzikU, faceId_pad_symanzikV ρ w v hρ0 hρ1, ofReal_zero, zero_mul, sub_zero]
  push_cast
  ring

end Join




/-! ### Fubini on `[0, 1] × Δ` and continuity of the coefficients -/

/-- **Fubini on `[0, 1] × Δₚ`** for an integrand continuous on the closed product. -/
theorem faceId_integral_swap {p : ℕ} (G : ℝ → (Fin p → ℝ) → ℂ)
    (hG : ContinuousOn (Function.uncurry G) (Icc (0 : ℝ) 1 ×ˢ simplexSet p)) :
    ∫ ρ in (0 : ℝ)..1, ∫ w in simplexSet p, G ρ w =
      ∫ w in simplexSet p, ∫ ρ in (0 : ℝ)..1, G ρ w := by
  have hint : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (simplexSet p))) := by
    rw [Measure.prod_restrict]
    exact ((hG.integrableOn_compact (μ := volume.prod volume)
      (isCompact_Icc.prod (isCompact_simplexSet p))).mono_set
      (prod_mono Ioc_subset_Icc_self subset_rfl))
  simp only [intervalIntegral.integral_of_le zero_le_one]
  exact integral_integral_swap hint

section Cont

variable {p : ℕ} (pR : Fin (p + 1) → Fin 4 → ℝ) (MR : Fin (p + 1) → ℝ)

theorem faceId_continuous_P0 : Continuous fun w : Fin p → ℝ => faceIdP0 pR (simplexPoint w) := by
  refine continuous_pi fun μ => ?_
  simp only [faceIdP0]
  exact continuous_finsetSum _ fun j _ =>
    (continuous_simplexPoint j).mul continuous_const

theorem faceId_continuous_VR : Continuous fun w : Fin p → ℝ => faceIdVR pR MR (simplexPoint w) := by
  have h := faceId_continuous_P0 pR
  simp only [faceIdVR, Minkowski.dot]
  refine (continuous_finsetSum _ fun j _ => (continuous_simplexPoint j).mul
    continuous_const).sub (continuous_finsetSum _ fun μ _ => continuous_finsetSum _ fun ν _ =>
      (continuous_const.mul ((continuous_apply μ).comp h)).mul ((continuous_apply ν).comp h))

theorem faceId_continuous_X0 :
    Continuous fun w : Fin p → ℝ => faceIdX0 (faceIdP0 pR (simplexPoint w)) := by
  have h := faceId_continuous_P0 pR
  have h2 : Continuous fun w : Fin p → ℝ =>
      (![-faceIdP0 pR (simplexPoint w), 0] : Fin 2 → Fin 4 → ℝ) := by
    refine continuous_pi fun s => ?_
    fin_cases s
    · exact h.neg
    · simpa using continuous_const
  exact continuous_loopComp.comp h2

theorem faceId_continuous_evalC {Q : LoopQuartic} : Continuous fun X => Q.evalC X := by
  unfold LoopQuartic.evalC
  fun_prop

theorem faceId_continuous_cTwoG {Q : LoopQuartic} (G : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous fun X => cTwoG Q G X := by
  unfold cTwoG
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    (Q.continuous_hess a b).mul continuous_const

end Cont

/-! ### The parametric integral of the padded data -/

section Main

variable {r : ℕ} (pR : Fin (r + 3 + 1) → Fin 4 → ℝ) (MR : Fin (r + 3 + 1) → ℝ) (m₀ : ℝ)

/-- The `ρ`-profile `ρᵏ (ρa + (1 - ρ)b)^{-(k+2)}` of the beta integral. -/
noncomputable def faceIdPhi (k : ℕ) (a b ρ : ℝ) : ℝ := ρ ^ k * ((ρ * a + (1 - ρ) * b) ^ (k + 2))⁻¹

/-- The integrand on `[0, 1] × Δ` after the auxiliary block is integrated out. -/
noncomputable def faceIdPadG (Q : LoopQuartic) (ρ : ℝ) (w : Fin (r + 3) → ℝ) : ℂ :=
  ((r + 2).factorial / 2 : ℂ) * Q.evalC (faceIdX0 (faceIdP0 pR (simplexPoint w))) *
      (faceIdPhi (r + 1) (faceIdVR pR MR (simplexPoint w)) (m₀ ^ 2) ρ : ℂ) +
    ((r + 1).factorial / 4 : ℂ) * cTwoG Q (eS 0) (faceIdX0 (faceIdP0 pR (simplexPoint w))) *
      (faceIdPhi r (faceIdVR pR MR (simplexPoint w)) (m₀ ^ 2) ρ : ℂ) +
    (r.factorial / 8 : ℂ) * cFourG Q (eS 0) *
      (faceIdPhi (r - 1) (faceIdVR pR MR (simplexPoint w)) (m₀ ^ 2) ρ : ℂ)

theorem faceId_L_pos {a b c ρ : ℝ} (hb : 0 < b) (hc : 0 < c) (ha : c ≤ a) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    0 < ρ * a + (1 - ρ) * b := by
  rcases eq_or_lt_of_le hρ.1 with h | h
  · rw [← h]; simpa using hb
  · nlinarith [hρ.2, mul_nonneg hρ.1 (sub_nonneg.2 ha), mul_nonneg (sub_nonneg.2 hρ.2) hb.le]

/-- **The join-point integrand, weighted and integrated over the auxiliary simplex.** -/
theorem faceId_pad_inner {Q : LoopQuartic} (hQ : LoopDegLe 1 1 Q) (hq : r = 0 → Q.quart = 0)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {c : ℝ} (hc : 0 < c) (hm₀ : 0 < m₀) {w : Fin (r + 3) → ℝ}
    (hw : c ≤ faceIdVR pR MR (simplexPoint w)) :
    (ρ ^ (r + 3) * (1 - ρ) ^ 2) • ∫ v in simplexSet 2, faceIdPF Q (faceIdPadα (r + 3))
      (faceIdPadP pR) (faceIdPadM MR m₀) (faceIdJz ρ w v) = faceIdPadG pR MR m₀ Q ρ w := by
  simp only [faceId_pad_pf ρ w _ hρ0 hρ1 hQ pR MR m₀, setIntegral_const, Measure.real,
    faceId_volume_simplexSet_two]
  have hL := faceId_L_pos (sq_pos_of_pos hm₀) hc hw ⟨hρ0.le, hρ1.le⟩
  have h1ρ : (1 - ρ) ≠ 0 := by linarith
  have e1 : r + 3 + 1 + 2 - 4 = r + 2 := by omega
  have e2 : r + 3 + 1 + 2 - 3 = r + 1 + 2 := by omega
  have e3 : r + 3 + 1 + 2 - 5 = r + 1 := by omega
  rw [e1, e2, e3]
  simp only [faceIdPadG, faceIdPhi, Complex.real_smul]
  set W := ρ * faceIdVR pR MR (simplexPoint w) + (1 - ρ) * m₀ ^ 2 with hWdef
  have hWc : (W : ℂ) ≠ 0 := ofReal_ne_zero.mpr hL.ne'
  have hρc : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ0.ne'
  have h1ρc : (1 - (ρ : ℂ)) ≠ 0 := by
    have : ((1 - ρ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1ρ
    simpa using this
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    rw [FaceBr.cFourG_of_quart (hq rfl)]
    simp only [zero_add, Nat.factorial, Nat.zero_sub]
    push_cast
    field_simp
    ring
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

theorem faceId_intervalIntegrable_phi (k : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (C : ℂ) :
    IntervalIntegrable (fun ρ => C * (faceIdPhi k a b ρ : ℂ)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  refine continuousOn_const.mul (continuous_ofReal.comp_continuousOn ?_)
  refine (continuousOn_pow k).mul (ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop))
    fun ρ hρ => (pow_pos (faceId_L_pos hb ha le_rfl hρ) _).ne')

theorem faceId_integral_phi (k : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (C : ℂ) :
    ∫ ρ in (0 : ℝ)..1, C * (faceIdPhi k a b ρ : ℂ) =
      C * ((((k + 1 : ℕ) : ℝ) * a ^ (k + 1) * b)⁻¹ : ℝ) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  simp only [faceIdPhi, faceId_integral_beta k ha hb]

/-- **The `ρ`-integral of the reduced integrand** is `(2m₀²)⁻¹` times the reduced bracket. -/
theorem faceId_padG_integral {Q : LoopQuartic} (hq : r = 0 → Q.quart = 0) (hm₀ : 0 < m₀)
    {w : Fin (r + 3) → ℝ} (ha : 0 < faceIdVR pR MR (simplexPoint w)) :
    ∫ ρ in (0 : ℝ)..1, faceIdPadG pR MR m₀ Q ρ w = ((2 * m₀ ^ 2 : ℝ) : ℂ)⁻¹ *
      faceIdRedBr (r + 3 + 1) Q (faceIdX0 (faceIdP0 pR (simplexPoint w)))
        (faceIdVR pR MR (simplexPoint w)) := by
  have hb : 0 < m₀ ^ 2 := by positivity
  simp only [faceIdPadG]
  rw [intervalIntegral.integral_add ((faceId_intervalIntegrable_phi _ ha hb _).add
      (faceId_intervalIntegrable_phi _ ha hb _)) (faceId_intervalIntegrable_phi _ ha hb _),
    intervalIntegral.integral_add (faceId_intervalIntegrable_phi _ ha hb _)
      (faceId_intervalIntegrable_phi _ ha hb _),
    faceId_integral_phi _ ha hb, faceId_integral_phi _ ha hb, faceId_integral_phi _ ha hb]
  set a := faceIdVR pR MR (simplexPoint w)
  have hac : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hmc : (m₀ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm₀.ne'
  have e1 : r + 3 + 1 - 3 = r + 1 := by omega
  have e2 : r + 3 + 1 - 2 = r + 2 := by omega
  have e3 : r + 3 + 1 - 4 = r := by omega
  have e4 : r + 3 + 1 - 5 = r - 1 := by omega
  simp only [faceIdRedBr, e1, e2, e3, e4]
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    rw [FaceBr.cFourG_of_quart (hq rfl)]
    simp only [Nat.factorial, Nat.zero_sub]
    push_cast
    field_simp
    ring
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have h1 : (s : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
    have h2 : (s : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (s + 1)
    have h3 : (s : ℂ) + 1 + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (s + 1 + 1)
    have h3' : (s : ℂ) + 1 + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (s + 1 + 1)
    simp only [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem faceId_continuousOn_padG (Q : LoopQuartic) {c : ℝ} (hc : 0 < c) (hm₀ : 0 < m₀)
    (hV : ∀ w ∈ simplexSet (r + 3), c ≤ faceIdVR pR MR (simplexPoint w)) :
    ContinuousOn (Function.uncurry (faceIdPadG pR MR m₀ Q))
      (Icc (0 : ℝ) 1 ×ˢ simplexSet (r + 3)) := by
  have hb : 0 < m₀ ^ 2 := by positivity
  have hVc := faceId_continuous_VR pR MR
  have hX := faceId_continuous_X0 pR
  have hphi : ∀ k, ContinuousOn (fun q : ℝ × (Fin (r + 3) → ℝ) =>
      ((faceIdPhi k (faceIdVR pR MR (simplexPoint q.2)) (m₀ ^ 2) q.1 : ℝ) : ℂ))
      (Icc (0 : ℝ) 1 ×ˢ simplexSet (r + 3)) := fun k => by
    refine continuous_ofReal.comp_continuousOn ?_
    simp only [faceIdPhi]
    refine (continuous_fst.pow k).continuousOn.mul (ContinuousOn.inv₀ ?_ fun q hq =>
      (pow_pos (faceId_L_pos hb hc (hV q.2 hq.2) hq.1) _).ne')
    exact (((continuous_fst.mul (hVc.comp continuous_snd)).add
      ((continuous_const.sub continuous_fst).mul continuous_const)).pow _).continuousOn
  have hE : Continuous fun q : ℝ × (Fin (r + 3) → ℝ) =>
      Q.evalC (faceIdX0 (faceIdP0 pR (simplexPoint q.2))) :=
    faceId_continuous_evalC.comp (hX.comp continuous_snd)
  have hC : Continuous fun q : ℝ × (Fin (r + 3) → ℝ) =>
      cTwoG Q (eS 0) (faceIdX0 (faceIdP0 pR (simplexPoint q.2))) :=
    (faceId_continuous_cTwoG _).comp (hX.comp continuous_snd)
  have hG : Function.uncurry (faceIdPadG pR MR m₀ Q) = fun q =>
      ((r + 2).factorial / 2 : ℂ) * Q.evalC (faceIdX0 (faceIdP0 pR (simplexPoint q.2))) *
          (faceIdPhi (r + 1) (faceIdVR pR MR (simplexPoint q.2)) (m₀ ^ 2) q.1 : ℂ) +
        ((r + 1).factorial / 4 : ℂ) * cTwoG Q (eS 0) (faceIdX0 (faceIdP0 pR (simplexPoint q.2))) *
          (faceIdPhi r (faceIdVR pR MR (simplexPoint q.2)) (m₀ ^ 2) q.1 : ℂ) +
        (r.factorial / 8 : ℂ) * cFourG Q (eS 0) *
          (faceIdPhi (r - 1) (faceIdVR pR MR (simplexPoint q.2)) (m₀ ^ 2) q.1 : ℂ) := rfl
  rw [hG]
  exact (((continuous_const.mul hE).continuousOn.mul (hphi (r + 1))).add
    ((continuous_const.mul hC).continuousOn.mul (hphi r))).add
    (continuousOn_const.mul (hphi (r - 1)))

/-- **Integrating out the auxiliary loop.** For padded data with `r + 4` one-loop lines and a
numerator of loop-1 degree at most one (cubic when `r = 0`), with `V̂ ≥ c > 0` on the one-loop
simplex, the parametric integral is `(2m₀²)⁻¹` times the reduced one-loop functional. -/
theorem faceId_integral_pad {Q : LoopQuartic} (hQ : LoopDegLe 1 1 Q) (hq : r = 0 → Q.quart = 0)
    {c : ℝ} (hc : 0 < c) (hm₀ : 0 < m₀)
    (hV : ∀ w ∈ simplexSet (r + 3), c ≤ faceIdVR pR MR (simplexPoint w))
    (hint : IntegrableOn (fun x => faceIdPF Q (faceIdPadα (r + 3)) (faceIdPadP pR)
      (faceIdPadM MR m₀) (simplexPoint x)) (simplexSet (r + 3 + 1 + 2))) :
    ∫ x in simplexSet (r + 3 + 1 + 2), faceIdPF Q (faceIdPadα (r + 3)) (faceIdPadP pR)
        (faceIdPadM MR m₀) (simplexPoint x) =
      ((2 * m₀ ^ 2 : ℝ) : ℂ)⁻¹ * ∫ w in simplexSet (r + 3), faceIdRedBr (r + 3 + 1) Q
        (faceIdX0 (faceIdP0 pR (simplexPoint w))) (faceIdVR pR MR (simplexPoint w)) := by
  rw [integral_simplex_join (p := r + 3) (q := 2)
    (f := faceIdPF Q (faceIdPadα (r + 3)) (faceIdPadP pR) (faceIdPadM MR m₀)) hint]
  have step : ∫ ρ in (0 : ℝ)..1, (ρ ^ (r + 3) * (1 - ρ) ^ 2) •
      ∫ w in simplexSet (r + 3), ∫ v in simplexSet 2, faceIdPF Q (faceIdPadα (r + 3))
        (faceIdPadP pR) (faceIdPadM MR m₀) (faceIdJz ρ w v) =
      ∫ ρ in (0 : ℝ)..1, ∫ w in simplexSet (r + 3), faceIdPadG pR MR m₀ Q ρ w := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with ρ hρ1' hρ
    rw [uIoc_of_le zero_le_one] at hρ
    have hρ1 : ρ < 1 := lt_of_le_of_ne hρ.2 hρ1'
    rw [← integral_smul]
    refine setIntegral_congr_fun (measurableSet_simplexSet _) fun w hw => ?_
    exact faceId_pad_inner pR MR m₀ hQ hq hρ.1 hρ1 hc hm₀ (hV w hw)
  refine step.trans ?_
  rw [faceId_integral_swap _ (faceId_continuousOn_padG pR MR m₀ Q hc hm₀ hV),
    ← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_simplexSet _) fun w hw => ?_
  exact faceId_padG_integral pR MR m₀ hq hm₀ (hc.trans_le (hV w hw))

end Main


end QED.GradedProof.RPi4

end
