/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBNVBSlice
public import QED.ChainProof.SetAKSKBNVBCW
public import QED.ChainProof.SetAKSKBVDens

/-!
# Set (a), stage B3: the nested one-loop form of the vertex class `VB`

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B3. The five-line
integrand of `VB` (stage B2, `ksB_vDens_VB`) has no equal lines; its inner vertex is the triple
of lines `ℓ₁ - k`, `ℓ₁`, `ℓ₀ - ℓ₁ + k` (positions `1, 2, 4`). Hierarchical Cheng–Wu variables
with the inner triple on the simplex (`ksN_nest3`) and the slice identity `ksN_slice_VB` give
the nested form:

* **`ksN_nest_VB`**: `∫_{Δ₄} ∑_f c_f ksBAtom(VB, M_f) =
  ∫_{x ∈ Δ₂} (1 - x₃)⁻¹ ∫_{Δ₂} ∑_f c_f K ksNGB(M_f, u, x, k) dx`, with `K = faceIdKV e 0 1`, the
  outer function integrable on `Δ₂`;
* **`ksN_vDens_VB`**: `vDens(VB)₂₃ = -π⁴ ∫_{x ∈ Δ₂} (1 - x₃)⁻¹ ∫_{Δ₂} ∑_f c_f K ksNGB dx`.

Here `x = (x₁, x₂, x₃)` are the inner Feynman parameters (lines `ℓ₁ - k`, `ℓ₁`, photon) and, on
the outer simplex (`y₀` on `ℓ₀`, `y₁` on `k + ℓ₀`, `y₂` the inner vertex),
`ksNGB = k²k³ [y₂/τ · (e/D² + (h₀₀ + 2x₃h₀₁ + x₃²h₁₁)/(2D)) + h₁₁/(2D)]`, `τ = x₃(1 - x₃)`,
`D = (y₀ + y₁)M² + y₁s + y₂ m_v'² - (y₁ + βy₂)²s` (see `SetAKSKBNVBSlice`). (Numerically equal to
the outer Feynman form `setAKS4/outerVB.py`, `setAKS10/n2_vbnum.py`.)
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.GradedProof.RPi4 QED.GradedProof.VP2
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.ChengWu

theorem ksN_simplexPoint_two_pos {y : Fin 2 → ℝ} (hy : y ∈ openSimplex 2) :
    0 < simplexPoint y 2 := by
  have h : simplexPoint y 2 = 1 - ∑ i, y i := simplexPoint_last y
  rw [h]
  linarith [(mem_openSimplex.1 hy).2]

/-- **The vertex nest with the weight `(1 - x₃)⁻¹`.** -/
theorem ksN_nest3_weight {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : (Fin 5 → ℝ) → E}
    (hF : ∀ z : Fin 5 → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t → F (t • z) = (t ^ 5)⁻¹ • F z)
    (hI : IntegrableOn (fun y => F (simplexPoint y)) (simplexSet 4))
    (G : (Fin 3 → ℝ) → (Fin 3 → ℝ) → E)
    (hG : ∀ q : Fin 3 → ℝ, (∀ i, 0 < q i) → ∑ i, q i = 1 → ∀ z : Fin 3 → ℝ, (∀ i, 0 < z i) →
      ∀ t : ℝ, 0 < t → G q (t • z) = (t ^ 3)⁻¹ • G q z)
    (hslice : ∀ q : Fin 3 → ℝ, (∀ i, 0 < q i) → ∑ i, q i = 1 → ∀ v ∈ ksNPos 2,
      F (ksNIns q v) = q 2 • G q (Fin.snoc v (q 2 * (1 - q 2)))) :
    IntegrableOn (fun x => (1 - simplexPoint x 2)⁻¹ •
      ∫ y in simplexSet 2, G (simplexPoint x) (simplexPoint y)) (simplexSet 2) ∧
    ∫ y in simplexSet 4, F (simplexPoint y) = ∫ x in simplexSet 2, (1 - simplexPoint x 2)⁻¹ •
      ∫ y in simplexSet 2, G (simplexPoint x) (simplexPoint y) := by
  have hτ : ∀ q : Fin 3 → ℝ, (∀ i, 0 < q i) → ∑ i, q i = 1 → 0 < q 2 * (1 - q 2) := by
    intro q hq h1
    rw [Fin.sum_univ_three] at h1
    exact mul_pos (hq 2) (by linarith [hq 0, hq 1])
  obtain ⟨h1, h2⟩ := ksN_nest3 hF (fun q => q 2) (fun q => q 2 * (1 - q 2)) G hτ hG hslice hI
  have hae := simplexSet_ae_eq_openSimplex (0 : Fin 2)
  have hpt : EqOn (fun y => ksNNestR (fun q => q 2) (fun q => q 2 * (1 - q 2)) G
      (simplexPoint y)) (fun x => (1 - simplexPoint x 2)⁻¹ •
        ∫ y in simplexSet 2, G (simplexPoint x) (simplexPoint y)) (openSimplex 2) := by
    intro y hy
    have h0 := (ksN_simplexPoint_two_pos hy).ne'
    simp only [ksNNestR]
    congr 1
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
  refine ⟨?_, ?_⟩
  · exact ((h1.congr_set_ae hae.symm).congr_fun hpt
      (ksN_measurableSet_openSimplex 2)).congr_set_ae hae
  · rw [h2]
    exact (setIntegral_congr_set hae).trans ((setIntegral_congr_fun
      (ksN_measurableSet_openSimplex 2) hpt).trans (setIntegral_congr_set hae).symm)

theorem ksN_snoc_two (v : Fin 2 → ℝ) (τ : ℝ) : (Fin.snoc v τ : Fin 3 → ℝ) = ![v 0, v 1, τ] := by
  funext i
  fin_cases i <;> rfl

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hPV₁ : ∑ f, Φ.coeff f = 0)
  (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k)
  {u : ℝ} (hu : 0 < u)

/-- The flavour sum of the outer `VB` integrands at the inner point `x`. -/
noncomputable def ksNGBsum (e u : ℝ) (k : Fin 4 → ℝ) (x y : Fin 3 → ℝ) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * (faceIdKV e 0 1 * (ksNGB (Φ.mass f) u x k y : ℂ))

theorem ksN_eval_VB (M : ℝ) :
    (ksBRep e aVB baseVB cVB M k).eval =
      fun ℓ => faceIdKV e 0 1 * (ksNTB M (ℓ 0) (ℓ 1) k : ℂ) := by
  rw [ksBRep_eval]
  funext ℓ
  exact ksN_vNum_VB e M k ℓ

include hPV₁ hPV₂ hm₀ hmass hk hu

/-- **The nested form of `VB`**: hierarchical Cheng–Wu variables, inner vertex first. -/
theorem ksN_nest_VB :
    IntegrableOn (fun x => (1 - simplexPoint x 2)⁻¹ •
      ∫ y in simplexSet 2, ksNGBsum Φ e u k (simplexPoint x) (simplexPoint y)) (simplexSet 2) ∧
    ∫ y in simplexSet 4, ∑ f, (Φ.coeff f : ℂ) * ksBAtom baseVB cVB k
      (ksBRep e aVB baseVB cVB (Φ.mass f) k) u (simplexPoint y) (fun _ => Φ.mass f) =
    ∫ x in simplexSet 2, (1 - simplexPoint x 2)⁻¹ •
      ∫ y in simplexSet 2, ksNGBsum Φ e u k (simplexPoint x) (simplexPoint y) := by
  obtain ⟨hI5, -⟩ := ksB_vDens_VB Φ hPV₁ hPV₂ hm₀ hmass e hk hu
  set Qf := fun f => ksBRep e aVB baseVB cVB (Φ.mass f) k
  simp only [ksBAtom] at hI5 ⊢
  refine ksN_nest3_weight (F := fun z => ∑ f, (Φ.coeff f : ℂ) * pieceF 5 (Qf f)
    (castLoopMatrix baseVB) (fun l => cVB l • k) (ksBM5 fun _ => Φ.mass f) (Fin.last 4) u z)
    ?_ hI5 (ksNGBsum Φ e u k) ?_ ?_
  · intro z _ t ht
    rw [Complex.real_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [ksN_pieceF_smul (ht := ht.ne')]
    push_cast
    ring
  · intro q _ _ z hz t ht
    simp only [ksNGBsum, Complex.real_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [ksN_ksNGB_smul _ _ _ _ _ ht hz]
    push_cast
    ring
  · intro q hq hq1 v hv
    rw [Fin.sum_univ_three] at hq1
    have hqe : q = ![q 0, 1 - q 0 - q 2, q 2] := by
      funext i
      fin_cases i
      · rfl
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        linarith
      · rfl
    have h2 : 0 < 1 - q 0 - q 2 := by linarith [hq 1]
    have hins : ksNIns q v = ![v 0, q 0, 1 - q 0 - q 2, v 1, q 2] := by
      rw [ksNIns, hqe]
      rfl
    rw [hins, ksN_snoc_two]
    simp only [ksNGBsum, Complex.real_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have h := ksN_slice_VB k (ksN_eval_VB e (Φ.mass f)) (ksBRep_contractFour e aVB baseVB cVB
      ksB_flip_VB (Φ.mass f) k) u (hq 0) (hq 2) h2 (hv 0) (hv 1)
    rw [h, ← hqe]
    ring

/-- **`VB` at the entry `(2, 3)` in nested one-loop form.** -/
theorem ksN_vDens_VB :
    IntegrableOn (fun x => (1 - simplexPoint x 2)⁻¹ •
      ∫ y in simplexSet 2, ksNGBsum Φ e u k (simplexPoint x) (simplexPoint y)) (simplexSet 2) ∧
    vDens aVB baseVB cVB Φ e m₀ u k 2 3 = -((π : ℂ) ^ 4) *
      ∫ x in simplexSet 2, (1 - simplexPoint x 2)⁻¹ •
        ∫ y in simplexSet 2, ksNGBsum Φ e u k (simplexPoint x) (simplexPoint y) := by
  obtain ⟨h1, h2⟩ := ksN_nest_VB Φ hPV₁ hPV₂ hm₀ hmass e hk hu
  exact ⟨h1, by rw [(ksB_vDens_VB Φ hPV₁ hPV₂ hm₀ hmass e hk hu).2, h2]⟩

end Classes

end QED.ChainProof.SetAKS

end
