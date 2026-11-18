/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLGraphReduceBound
public import QED.TwoLoop.UnitLGraphReduceMerge
public import QED.Integration.SimplexMergePV
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The ladder graph half on the 3-simplex of the merged pairs

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the L link, graph half, item (ii). The four line
pairs of the ladder are merged (`QED/TwoLoop/UnitLGraphReduceMerge.lean`): the electron splits
contribute the group-volume factors `z_A z_B`, and the two Pauli–Villars splits are integrated
out as divided differences (`QED/Integration/SimplexMergePV.lean`), which cancel the factor
`(Λ² - m_γ²)²`. With `V_{μ_a μ_b} = E + μ_a z_a + μ_b z_b` (`μ ∈ {m_γ², Λ²}`) and
`ladderTerm μ_a μ_b = z_A z_B z_a [Q/(2U⁵ V²) + (9c + a)/(2U⁴ V)]`:

* `ladderMerged_ladderG`: for positive group sums,
  `(Λ² - m_γ²)² ∫∫∫∫ ladderG = ladderF4 = ∑_{μ_a, μ_b} ± ladderTerm μ_a μ_b`, the signs `+` for
  equal masses and `-` otherwise (the product of the two Pauli–Villars signs);
* `sixteen_pi_pow_four_mul_graphHalf_eq_simplex`: **the ladder graph half on `Δ₃`**,
  `16π⁴ · graphHalf P = ∫_{Δ₃} ladderF4(z_A, z_B, z_a, z_b)`, for `m = e = 1`, `0 < m_γ < Λ`,
  and `ladderF4 ∘ simplexPoint` is integrable on `Δ₃`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace QED.TwoLoop.UnitLGraphReduce

open QED.WickModel QED.TwoLoop.UnitLGraphTrace
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.SimplexMerge

/-! ### The integrand on the merged simplex -/

/-- One mass combination of the merged integrand:
`z_A z_B z_a [Q/(2U⁵ V²) + (9c + a)/(2U⁴ V)]`, `V = E + μ_a z_a + μ_b z_b`. -/
noncomputable def ladderTerm (μa μb A B a b : ℝ) : ℝ :=
  A * B * a * (gQ A B a b / (2 * gU A B a b ^ 5 * (gE A B a b + μa * a + μb * b) ^ 2) +
    (9 * gc B b + ga A B b) / (2 * gU A B a b ^ 4 * (gE A B a b + μa * a + μb * b)))

/-- **The merged integrand**: the Pauli–Villars-signed sum of the four mass combinations. -/
noncomputable def ladderF4 (P : Params) (w : Fin 4 → ℝ) : ℝ :=
  ladderTerm (P.mγ ^ 2) (P.mγ ^ 2) (w 0) (w 1) (w 2) (w 3) -
    ladderTerm (P.mγ ^ 2) (P.Λ ^ 2) (w 0) (w 1) (w 2) (w 3) -
    ladderTerm (P.Λ ^ 2) (P.mγ ^ 2) (w 0) (w 1) (w 2) (w 3) +
    ladderTerm (P.Λ ^ 2) (P.Λ ^ 2) (w 0) (w 1) (w 2) (w 3)

theorem gU_pos {A B a b : ℝ} (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hb : 0 < b) :
    0 < gU A B a b := by
  unfold gU ga gS gc; positivity

theorem gE_nonneg {A B a b : ℝ} (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ gE A B a b := by
  have := gU_pos hA hB ha hb
  unfold gE ga gS gc at *; positivity

/-! ### Evaluating the split integrals -/

section Eval

variable {P : Params} {w : Fin 4 → ℝ}

theorem ladderSplit_lzA (t₄ t₃ t₂ t₁ : ℝ) : lzA (ladderSplit w t₄ t₃ t₂ t₁) = w 0 := by
  simp [lzA, ladderSplit]
theorem ladderSplit_lzB (t₄ t₃ t₂ t₁ : ℝ) : lzB (ladderSplit w t₄ t₃ t₂ t₁) = w 1 := by
  simp [lzB, ladderSplit]
theorem ladderSplit_lza (t₄ t₃ t₂ t₁ : ℝ) : lza (ladderSplit w t₄ t₃ t₂ t₁) = w 2 := by
  simp [lza, ladderSplit]
theorem ladderSplit_lzb (t₄ t₃ t₂ t₁ : ℝ) : lzb (ladderSplit w t₄ t₃ t₂ t₁) = w 3 := by
  simp [lzb, ladderSplit]

/-- `ladderG` at a split point: `T₁ V⁻⁴ + T₂ V⁻³` with `V = K + β t₂ + β t₁`,
`K = E + Λ² (z_a + z_b)`, `β = m_γ² - Λ²`. -/
theorem ladderG_ladderSplit (t₄ t₃ t₂ t₁ : ℝ) :
    ladderG P (ladderSplit w t₄ t₃ t₂ t₁) =
      3 * w 2 * gQ (w 0) (w 1) (w 2) (w 3) / gU (w 0) (w 1) (w 2) (w 3) ^ 5 *
          (((gE (w 0) (w 1) (w 2) (w 3) + P.Λ ^ 2 * (w 2 + w 3) + (P.mγ ^ 2 - P.Λ ^ 2) * t₂) +
            (P.mγ ^ 2 - P.Λ ^ 2) * t₁) ^ 4)⁻¹ +
        w 2 * (9 * gc (w 1) (w 3) + ga (w 0) (w 1) (w 3)) / gU (w 0) (w 1) (w 2) (w 3) ^ 4 *
          (((gE (w 0) (w 1) (w 2) (w 3) + P.Λ ^ 2 * (w 2 + w 3) + (P.mγ ^ 2 - P.Λ ^ 2) * t₂) +
            (P.mγ ^ 2 - P.Λ ^ 2) * t₁) ^ 3)⁻¹ := by
  have eV : ladderV P (ladderSplit w t₄ t₃ t₂ t₁) =
      (gE (w 0) (w 1) (w 2) (w 3) + P.Λ ^ 2 * (w 2 + w 3) + (P.mγ ^ 2 - P.Λ ^ 2) * t₂) +
        (P.mγ ^ 2 - P.Λ ^ 2) * t₁ := by
    simp only [ladderV, ladderSplit_lzA, ladderSplit_lzB, ladderSplit_lza, ladderSplit_lzb]
    have e4 : ladderSplit w t₄ t₃ t₂ t₁ 4 = t₂ := rfl
    have e5 : ladderSplit w t₄ t₃ t₂ t₁ 5 = t₁ := rfl
    have e6 : ladderSplit w t₄ t₃ t₂ t₁ 6 = w 2 - t₂ := rfl
    have e7 : ladderSplit w t₄ t₃ t₂ t₁ 7 = w 3 - t₁ := rfl
    rw [e4, e5, e6, e7]
    ring
  have key : ∀ x y U V : ℝ, x / (U ^ 5 * V ^ 4) + y / (U ^ 4 * V ^ 3) =
      x / U ^ 5 * (V ^ 4)⁻¹ + y / U ^ 4 * (V ^ 3)⁻¹ := fun x y U V => by
    simp only [div_eq_mul_inv, mul_inv, mul_assoc]
  unfold ladderG
  rw [eV, ladderSplit_lzA, ladderSplit_lzB, ladderSplit_lza, ladderSplit_lzb]
  exact key _ _ _ _

/-- **The split integrals of the ladder integrand**: for positive group sums and
`0 < m_γ < Λ`, `(Λ² - m_γ²)² ladderMerged ladderG = ladderF4`. -/
theorem ladderMerged_ladderG (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) (hw : ∀ i, 0 < w i) :
    (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * ladderMerged (ladderG P) w = ladderF4 P w := by
  unfold ladderMerged ladderF4
  simp only [ladderG_ladderSplit]
  obtain ⟨A, hA_def⟩ : ∃ A, w 0 = A := ⟨_, rfl⟩
  obtain ⟨B, hB_def⟩ : ∃ B, w 1 = B := ⟨_, rfl⟩
  obtain ⟨a, ha_def⟩ : ∃ a, w 2 = a := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b, w 3 = b := ⟨_, rfl⟩
  have hA : 0 < A := hA_def ▸ hw 0
  have hB : 0 < B := hB_def ▸ hw 1
  have ha : 0 < a := ha_def ▸ hw 2
  have hb : 0 < b := hb_def ▸ hw 3
  rw [hA_def, hB_def, ha_def, hb_def]
  obtain ⟨E, hE_def⟩ : ∃ E, gE A B a b = E := ⟨_, rfl⟩
  have hE : 0 ≤ E := hE_def ▸ gE_nonneg hA hB ha hb
  have hU : 0 < gU A B a b := gU_pos hA hB ha hb
  simp only [ladderTerm, hE_def]
  obtain ⟨β, hβ_def⟩ : ∃ β, P.mγ ^ 2 - P.Λ ^ 2 = β := ⟨_, rfl⟩
  have hm2 : 0 < P.mγ ^ 2 := by positivity
  have hΛpos : 0 < P.Λ := by linarith
  have hΛ2 : P.mγ ^ 2 < P.Λ ^ 2 := by nlinarith
  have hβ : β ≠ 0 := by rw [← hβ_def]; linarith
  rw [hβ_def]
  obtain ⟨K, hK_def⟩ : ∃ K, E + P.Λ ^ 2 * (a + b) = K := ⟨_, rfl⟩
  rw [hK_def]
  have hab : 0 < P.Λ ^ 2 * (a + b) := by positivity
  -- positivity of the four `V`s and of the intermediate values
  have pK : 0 < K := by rw [← hK_def]; linarith
  have pKa : 0 < K + β * a := by rw [← hK_def, ← hβ_def]; nlinarith
  have pKb : 0 < K + β * b := by rw [← hK_def, ← hβ_def]; nlinarith
  have pKab : 0 < K + β * b + β * a := by rw [← hK_def, ← hβ_def]; nlinarith
  have pos₁ : ∀ t₂ ∈ uIcc 0 a, 0 < K + β * t₂ := fun t₂ ht₂ =>
    pos_of_mem_uIcc_affine pK pKa ht₂
  have pos₂ : ∀ t₂ ∈ uIcc 0 a, 0 < K + β * t₂ + β * b := fun t₂ ht₂ => by
    have := pos_of_mem_uIcc_affine pKb pKab ht₂
    linarith
  obtain ⟨T₁, hT₁⟩ : ∃ T, 3 * a * gQ A B a b / gU A B a b ^ 5 = T := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ T, a * (9 * gc B b + ga A B b) / gU A B a b ^ 4 = T := ⟨_, rfl⟩
  rw [hT₁, hT₂]
  -- the inner photon split
  have h₁ : ∀ t₂ ∈ uIcc 0 a,
      ∫ t₁ in (0 : ℝ)..b, (T₁ * ((K + β * t₂ + β * t₁) ^ 4)⁻¹ +
          T₂ * ((K + β * t₂ + β * t₁) ^ 3)⁻¹) =
        T₁ / (3 * β) * (((K + β * t₂) ^ 3)⁻¹ - ((K + β * b + β * t₂) ^ 3)⁻¹) +
        T₂ / (2 * β) * (((K + β * t₂) ^ 2)⁻¹ - ((K + β * b + β * t₂) ^ 2)⁻¹) := by
    intro t₂ ht₂
    rw [intervalIntegral.integral_add
        ((intervalIntegrable_inv_pow_affine 4 (pos₁ t₂ ht₂) (pos₂ t₂ ht₂)).const_mul _)
        ((intervalIntegrable_inv_pow_affine 3 (pos₁ t₂ ht₂) (pos₂ t₂ ht₂)).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_inv_pow_four_affine hβ (pos₁ t₂ ht₂) (pos₂ t₂ ht₂),
      integral_inv_pow_three_affine hβ (pos₁ t₂ ht₂) (pos₂ t₂ ht₂),
      show K + β * t₂ + β * b = K + β * b + β * t₂ by ring]
    ring
  -- the outer photon split
  have h₂ : ∫ t₂ in (0 : ℝ)..a, ∫ t₁ in (0 : ℝ)..b, (T₁ * ((K + β * t₂ + β * t₁) ^ 4)⁻¹ +
          T₂ * ((K + β * t₂ + β * t₁) ^ 3)⁻¹) =
        T₁ / (3 * β) * (((K ^ 2)⁻¹ - ((K + β * a) ^ 2)⁻¹) / (2 * β) -
          (((K + β * b) ^ 2)⁻¹ - ((K + β * b + β * a) ^ 2)⁻¹) / (2 * β)) +
        T₂ / (2 * β) * ((K⁻¹ - (K + β * a)⁻¹) / β -
          ((K + β * b)⁻¹ - (K + β * b + β * a)⁻¹) / β) := by
    rw [intervalIntegral.integral_congr h₁]
    rw [intervalIntegral.integral_add
        (((intervalIntegrable_inv_pow_affine 3 pK pKa).sub
          (intervalIntegrable_inv_pow_affine 3 pKb pKab)).const_mul _)
        (((intervalIntegrable_inv_pow_affine 2 pK pKa).sub
          (intervalIntegrable_inv_pow_affine 2 pKb pKab)).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (intervalIntegrable_inv_pow_affine 3 pK pKa)
        (intervalIntegrable_inv_pow_affine 3 pKb pKab),
      intervalIntegral.integral_sub (intervalIntegrable_inv_pow_affine 2 pK pKa)
        (intervalIntegrable_inv_pow_affine 2 pKb pKab),
      integral_inv_pow_three_affine hβ pK pKa, integral_inv_pow_three_affine hβ pKb pKab,
      integral_inv_pow_two_affine hβ pK pKa, integral_inv_pow_two_affine hβ pKb pKab]
  -- the electron splits
  simp only [h₂, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  -- the four `V`s
  have eK : E + P.Λ ^ 2 * a + P.Λ ^ 2 * b = K := by rw [← hK_def]; ring
  have eKa : E + P.mγ ^ 2 * a + P.Λ ^ 2 * b = K + β * a := by rw [← hK_def, ← hβ_def]; ring
  have eKb : E + P.Λ ^ 2 * a + P.mγ ^ 2 * b = K + β * b := by rw [← hK_def, ← hβ_def]; ring
  have eKab : E + P.mγ ^ 2 * a + P.mγ ^ 2 * b = K + β * b + β * a := by
    rw [← hK_def, ← hβ_def]; ring
  have hβ' : P.Λ ^ 2 - P.mγ ^ 2 = -β := by rw [← hβ_def]; ring
  rw [eK, eKa, eKb, eKab, hβ', ← hT₁, ← hT₂]
  have n1 := pK.ne'
  have n2 := pKa.ne'
  have n3 := pKb.ne'
  have n4 := pKab.ne'
  have nU := hU.ne'
  field_simp
  ring

end Eval

/-! ### The ladder graph half on `Δ₃` -/

theorem ae_simplexPoint_pos {m : ℕ} (hm : 0 < m) :
    ∀ᵐ y ∂(volume.restrict (simplexSet m)), ∀ i, 0 < simplexPoint y i := by
  filter_upwards [ae_mem_openSimplex hm] with y hy
  exact simplexPoint_pos_of_mem_openSimplex hy

/-- **The ladder graph half on the 3-simplex of the merged pairs** (`m = e = 1`,
`0 < m_γ < Λ`): `16π⁴ · graphHalf P = ∫_{Δ₃} ladderF4`, and `ladderF4` is integrable on `Δ₃`. -/
theorem sixteen_pi_pow_four_mul_graphHalf_eq_simplex {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    IntegrableOn (fun y => ladderF4 P (simplexPoint y)) (simplexSet 3) ∧
    16 * (π : ℂ) ^ 4 * QED.TwoLoop.UnitLLink.graphHalf P =
      ((∫ y in simplexSet 3, ladderF4 P (simplexPoint y) : ℝ) : ℂ) := by
  obtain ⟨hI, he'⟩ := integral_simplex_ladderSplit (integrableOn_ladderG hm hmγ hΛ.le)
  have hae : (fun y => (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * ladderMerged (ladderG P) (simplexPoint y))
      =ᵐ[volume.restrict (simplexSet 3)] fun y => ladderF4 P (simplexPoint y) := by
    filter_upwards [ae_simplexPoint_pos (by norm_num : 0 < 3)] with y hy
    exact ladderMerged_ladderG hmγ hΛ hy
  refine ⟨(hI.const_mul ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2)).congr hae, ?_⟩
  rw [sixteen_pi_pow_four_mul_graphHalf hm he, he', ← integral_const_mul, integral_congr_ae hae]

end QED.TwoLoop.UnitLGraphReduce

end
