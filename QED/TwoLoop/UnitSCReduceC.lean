/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCReduceCBound
public import QED.TwoLoop.UnitSCReduceCMerge
public import QED.TwoLoop.UnitXGraphReduce
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The corner pair on the 4-simplex of the merged groups

Section 8 of `docs/TWO-LOOP-UNITS.md`, the `S + C` link, reductions for the corner classes (the
analogue of `QED/TwoLoop/UnitXGraphReduce.lean`). The three line pairs of `C₊` are merged
(`QED/TwoLoop/UnitSCReduceCMerge.lean`): the split `t = z₀` of the outer electron pair enters
`M₁, M₂` affinely at fixed `z_o` (`gCM1_affine`, `gCM2_affine`), so its integral is `z_o` times
the value at the midpoint `t = z_o/2`; the two Pauli–Villars splits are integrated out as divided
differences (`QED.TwoLoop.UnitXGraph.integral_pv_double`), which cancel the factor
`(Λ² - m_γ²)²`. With `V_{μ_a μ_b} = E + μ_a z_a + μ_b z_b` (`μ ∈ {m_γ², Λ²}`) and
`cornerTerm μ_a μ_b = z_o [W M₁(z_o/2)/(2U⁶ V²) - M₂(z_o/2)/(2U⁵ V)]`:

* `cornerMerged_cornerG`: for positive group sums,
  `(Λ² - m_γ²)² cornerMerged cornerG = cornerF4 = ∑_{μ_a, μ_b} ± cornerTerm μ_a μ_b`, the signs
  `+` for equal masses and `-` otherwise;
* `sixteen_pi_pow_four_mul_openZero_Cp_eq_simplex`: **the class `C₊` on `Δ₄`**,
  `16π⁴ (1/(64 m⁵)) (1/i) openZero C₊ = ∫_{Δ₄} cornerF4(z_o, y₃, y₄, z_a, z_b)`, for `m = e = 1`,
  `0 < m_γ < Λ`, and `cornerF4 ∘ simplexPoint` is integrable on `Δ₄`.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.TwoLoop.UnitSCReduce

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitSCGraph
open QED.TwoLoop.UnitLGraphReduce QED.TwoLoop.UnitXGraph
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.SimplexMerge

/-! ### The polynomials in the group sums -/

/-- `W = (y₃ + y₄ + z_b) z_o + y₃ z_b`. -/
def gCW (o y3 y4 b : ℝ) : ℝ := (y3 + y4 + b) * o + y3 * b

/-- `M₁` in the group sums and the split `t = z₀` of the outer electron pair. -/
def gCM1 (o t y3 y4 a b : ℝ) : ℝ :=
  cpM1pa t (o - t) y3 y4 a b + cpM1pb t (o - t) y3 y4 a b + cpM1pc t (o - t) y3 y4 a b +
    cpM1pd t (o - t) y3 y4 a b

/-- `M₂` in the group sums and the split `t = z₀` of the outer electron pair. -/
def gCM2 (o t y3 y4 a b : ℝ) : ℝ :=
  cpM2pa t (o - t) y3 y4 a b + cpM2pb t (o - t) y3 y4 a b + cpM2pc t (o - t) y3 y4 a b +
    cpM2pd t (o - t) y3 y4 a b

/-- **`M₁` is affine in the split** at fixed `z_o`. -/
theorem gCM1_affine (o t y3 y4 a b : ℝ) :
    gCM1 o t y3 y4 a b = gCM1 o 0 y3 y4 a b + t * (gCM1 o 1 y3 y4 a b - gCM1 o 0 y3 y4 a b) := by
  simp only [gCM1, cpM1pa, cpM1pb, cpM1pc, cpM1pd]
  ring

/-- **`M₂` is affine in the split** at fixed `z_o`. -/
theorem gCM2_affine (o t y3 y4 a b : ℝ) :
    gCM2 o t y3 y4 a b = gCM2 o 0 y3 y4 a b + t * (gCM2 o 1 y3 y4 a b - gCM2 o 0 y3 y4 a b) := by
  simp only [gCM2, cpM2pa, cpM2pb, cpM2pc, cpM2pd]
  ring

/-! ### The integrand on the merged simplex -/

/-- One mass combination of the merged integrand:
`z_o [W M₁(z_o/2)/(2U⁶ V²) - M₂(z_o/2)/(2U⁵ V)]`, `V = E + μ_a z_a + μ_b z_b`. -/
noncomputable def cornerTerm (μa μb o y3 y4 a b : ℝ) : ℝ :=
  o * (gCW o y3 y4 b * gCM1 o (o / 2) y3 y4 a b /
      (2 * gCU o y3 y4 a b ^ 6 * (gCE o y3 y4 a b + μa * a + μb * b) ^ 2) -
    gCM2 o (o / 2) y3 y4 a b / (2 * gCU o y3 y4 a b ^ 5 * (gCE o y3 y4 a b + μa * a + μb * b)))

/-- **The merged integrand**: the Pauli–Villars-signed sum of the four mass combinations. -/
noncomputable def cornerF4 (P : Params) (w : Fin 5 → ℝ) : ℝ :=
  cornerTerm (P.mγ ^ 2) (P.mγ ^ 2) (w 0) (w 1) (w 2) (w 3) (w 4) -
    cornerTerm (P.mγ ^ 2) (P.Λ ^ 2) (w 0) (w 1) (w 2) (w 3) (w 4) -
    cornerTerm (P.Λ ^ 2) (P.mγ ^ 2) (w 0) (w 1) (w 2) (w 3) (w 4) +
    cornerTerm (P.Λ ^ 2) (P.Λ ^ 2) (w 0) (w 1) (w 2) (w 3) (w 4)

theorem gCU_pos {o y3 y4 a b : ℝ} (ho : 0 < o) (h3 : 0 < y3) (h4 : 0 < y4) (ha : 0 < a)
    (hb : 0 < b) : 0 < gCU o y3 y4 a b := by
  have e : gCU o y3 y4 a b = (o + a) * (y3 + y4 + b) + y3 * (y4 + b) := by unfold gCU; ring
  rw [e]; positivity

theorem gCE_nonneg {o y3 y4 a b : ℝ} (ho : 0 < o) (h3 : 0 < y3) (h4 : 0 < y4) (ha : 0 < a)
    (hb : 0 < b) : 0 ≤ gCE o y3 y4 a b := by
  have := gCU_pos ho h3 h4 ha hb
  unfold gCE gCEn
  positivity

/-! ### Evaluating the split integrals -/

section Eval

variable {P : Params} {w : Fin 5 → ℝ}

theorem cornerSplit_apply (t₃ t₂ t₁ : ℝ) :
    cornerSplit w t₃ t₂ t₁ 0 = t₃ ∧ cornerSplit w t₃ t₂ t₁ 1 = w 0 - t₃ ∧
      cornerSplit w t₃ t₂ t₁ 2 = w 1 ∧ cornerSplit w t₃ t₂ t₁ 3 = w 2 ∧
      cornerSplit w t₃ t₂ t₁ 4 = t₂ ∧ cornerSplit w t₃ t₂ t₁ 5 = t₁ ∧
      cornerSplit w t₃ t₂ t₁ 6 = w 3 - t₂ ∧ cornerSplit w t₃ t₂ t₁ 7 = w 4 - t₁ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `cornerG` at a split point: `T₁ V⁻⁴ + T₂ V⁻³` with `T₁ = 3 W M₁(t₃)/U⁶`,
`T₂ = -M₂(t₃)/U⁵` and `V = K + β t₂ + β t₁`, `K = E + Λ² (z_a + z_b)`, `β = m_γ² - Λ²`. -/
theorem cornerG_cornerSplit (t₃ t₂ t₁ : ℝ) :
    cornerG P (cornerSplit w t₃ t₂ t₁) =
      3 * (gCW (w 0) (w 1) (w 2) (w 4) * gCM1 (w 0) t₃ (w 1) (w 2) (w 3) (w 4)) /
          gCU (w 0) (w 1) (w 2) (w 3) (w 4) ^ 6 *
          (((gCE (w 0) (w 1) (w 2) (w 3) (w 4) + P.Λ ^ 2 * (w 3 + w 4) +
            (P.mγ ^ 2 - P.Λ ^ 2) * t₂) + (P.mγ ^ 2 - P.Λ ^ 2) * t₁) ^ 4)⁻¹ +
        -gCM2 (w 0) t₃ (w 1) (w 2) (w 3) (w 4) / gCU (w 0) (w 1) (w 2) (w 3) (w 4) ^ 5 *
          (((gCE (w 0) (w 1) (w 2) (w 3) (w 4) + P.Λ ^ 2 * (w 3 + w 4) +
            (P.mγ ^ 2 - P.Λ ^ 2) * t₂) + (P.mγ ^ 2 - P.Λ ^ 2) * t₁) ^ 3)⁻¹ := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := cornerSplit_apply (w := w) t₃ t₂ t₁
  have ho : cornerSplit w t₃ t₂ t₁ 0 + cornerSplit w t₃ t₂ t₁ 1 = w 0 := by rw [e0, e1]; ring
  have ha : spza (cornerSplit w t₃ t₂ t₁) = w 3 := by unfold spza; rw [e4, e6]; ring
  have hb : spzb (cornerSplit w t₃ t₂ t₁) = w 4 := by unfold spzb; rw [e5, e7]; ring
  have eV : cornerV P (cornerSplit w t₃ t₂ t₁ 0 + cornerSplit w t₃ t₂ t₁ 1)
      (cornerSplit w t₃ t₂ t₁ 2) (cornerSplit w t₃ t₂ t₁ 3) (spza (cornerSplit w t₃ t₂ t₁))
      (spzb (cornerSplit w t₃ t₂ t₁)) (cornerSplit w t₃ t₂ t₁) =
      (gCE (w 0) (w 1) (w 2) (w 3) (w 4) + P.Λ ^ 2 * (w 3 + w 4) + (P.mγ ^ 2 - P.Λ ^ 2) * t₂) +
        (P.mγ ^ 2 - P.Λ ^ 2) * t₁ := by
    rw [ho, ha, hb, e2, e3]
    unfold cornerV
    rw [e4, e5, e6, e7]
    ring
  have eU : cpU (cornerSplit w t₃ t₂ t₁) = gCU (w 0) (w 1) (w 2) (w 3) (w 4) := by
    rw [cpU_eq_gCU, ho, ha, hb, e2, e3]
  have eW : cpW (cornerSplit w t₃ t₂ t₁) = gCW (w 0) (w 1) (w 2) (w 4) := by
    unfold cpW gCW
    rw [hb, e0, e1, e2, e3]
    ring
  have eM1 : cpM1 (cornerSplit w t₃ t₂ t₁) = gCM1 (w 0) t₃ (w 1) (w 2) (w 3) (w 4) := by
    unfold cpM1 gCM1
    rw [ha, hb, e0, e1, e2, e3]
  have eM2 : cpM2 (cornerSplit w t₃ t₂ t₁) = gCM2 (w 0) t₃ (w 1) (w 2) (w 3) (w 4) := by
    unfold cpM2 gCM2
    rw [ha, hb, e0, e1, e2, e3]
  unfold cornerG cornerGz
  rw [eV, eU, eW, eM1, eM2]
  simp only [div_eq_mul_inv, mul_inv, neg_mul]
  ring

/-- **The split integrals of the `C₊` integrand**: for positive group sums and
`0 < m_γ < Λ`, `(Λ² - m_γ²)² cornerMerged cornerG = cornerF4`. -/
theorem cornerMerged_cornerG (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) (hw : ∀ i, 0 < w i) :
    (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * cornerMerged (cornerG P) w = cornerF4 P w := by
  unfold cornerMerged cornerF4
  simp only [cornerG_cornerSplit]
  obtain ⟨o, ho_def⟩ : ∃ o, w 0 = o := ⟨_, rfl⟩
  obtain ⟨y3, h3_def⟩ : ∃ y, w 1 = y := ⟨_, rfl⟩
  obtain ⟨y4, h4_def⟩ : ∃ y, w 2 = y := ⟨_, rfl⟩
  obtain ⟨a, ha_def⟩ : ∃ a, w 3 = a := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b, w 4 = b := ⟨_, rfl⟩
  have ho : 0 < o := ho_def ▸ hw 0
  have h3 : 0 < y3 := h3_def ▸ hw 1
  have h4 : 0 < y4 := h4_def ▸ hw 2
  have ha : 0 < a := ha_def ▸ hw 3
  have hb : 0 < b := hb_def ▸ hw 4
  rw [ho_def, h3_def, h4_def, ha_def, hb_def]
  obtain ⟨E, hE_def⟩ : ∃ E, gCE o y3 y4 a b = E := ⟨_, rfl⟩
  have hE : 0 ≤ E := hE_def ▸ gCE_nonneg ho h3 h4 ha hb
  have hU : 0 < gCU o y3 y4 a b := gCU_pos ho h3 h4 ha hb
  simp only [cornerTerm, hE_def]
  obtain ⟨β, hβ_def⟩ : ∃ β, P.mγ ^ 2 - P.Λ ^ 2 = β := ⟨_, rfl⟩
  have hm2 : 0 < P.mγ ^ 2 := by positivity
  have hΛpos : 0 < P.Λ := by linarith
  have hΛ2 : P.mγ ^ 2 < P.Λ ^ 2 := by nlinarith
  have hβ : β ≠ 0 := by rw [← hβ_def]; linarith
  rw [hβ_def]
  obtain ⟨K, hK_def⟩ : ∃ K, E + P.Λ ^ 2 * (a + b) = K := ⟨_, rfl⟩
  rw [hK_def]
  have hab : 0 < P.Λ ^ 2 * (a + b) := by positivity
  have pK : 0 < K := by rw [← hK_def]; linarith
  have pKa : 0 < K + β * a := by rw [← hK_def, ← hβ_def]; nlinarith
  have pKb : 0 < K + β * b := by rw [← hK_def, ← hβ_def]; nlinarith
  have pKab : 0 < K + β * b + β * a := by rw [← hK_def, ← hβ_def]; nlinarith
  obtain ⟨X₁, hX₁⟩ : ∃ X, ((K ^ 2)⁻¹ - ((K + β * a) ^ 2)⁻¹) / (2 * β) -
      (((K + β * b) ^ 2)⁻¹ - ((K + β * b + β * a) ^ 2)⁻¹) / (2 * β) = X := ⟨_, rfl⟩
  obtain ⟨X₂, hX₂⟩ : ∃ X, (K⁻¹ - (K + β * a)⁻¹) / β -
      ((K + β * b)⁻¹ - (K + β * b + β * a)⁻¹) / β = X := ⟨_, rfl⟩
  -- the photon splits at fixed electron split
  have h₂ : ∀ t₃ : ℝ, ∫ t₂ in (0 : ℝ)..a, ∫ t₁ in (0 : ℝ)..b,
      (3 * (gCW o y3 y4 b * gCM1 o t₃ y3 y4 a b) / gCU o y3 y4 a b ^ 6 *
          ((K + β * t₂ + β * t₁) ^ 4)⁻¹ +
        -gCM2 o t₃ y3 y4 a b / gCU o y3 y4 a b ^ 5 * ((K + β * t₂ + β * t₁) ^ 3)⁻¹) =
      3 * (gCW o y3 y4 b * gCM1 o t₃ y3 y4 a b) / gCU o y3 y4 a b ^ 6 / (3 * β) * X₁ +
        -gCM2 o t₃ y3 y4 a b / gCU o y3 y4 a b ^ 5 / (2 * β) * X₂ := fun t₃ => by
    rw [integral_pv_double hβ pK pKa pKb pKab, hX₁, hX₂]
  simp only [h₂]
  -- the electron split
  rw [integral_affine_eq_mid
    (3 * (gCW o y3 y4 b * gCM1 o 0 y3 y4 a b) / gCU o y3 y4 a b ^ 6 / (3 * β) * X₁ +
      -gCM2 o 0 y3 y4 a b / gCU o y3 y4 a b ^ 5 / (2 * β) * X₂)
    (3 * (gCW o y3 y4 b * (gCM1 o 1 y3 y4 a b - gCM1 o 0 y3 y4 a b)) / gCU o y3 y4 a b ^ 6 /
        (3 * β) * X₁ +
      -(gCM2 o 1 y3 y4 a b - gCM2 o 0 y3 y4 a b) / gCU o y3 y4 a b ^ 5 / (2 * β) * X₂)
    (fun t => by rw [gCM1_affine o t, gCM2_affine o t]; ring)]
  -- the four `V`s
  have eK : E + P.Λ ^ 2 * a + P.Λ ^ 2 * b = K := by rw [← hK_def]; ring
  have eKa : E + P.mγ ^ 2 * a + P.Λ ^ 2 * b = K + β * a := by rw [← hK_def, ← hβ_def]; ring
  have eKb : E + P.Λ ^ 2 * a + P.mγ ^ 2 * b = K + β * b := by rw [← hK_def, ← hβ_def]; ring
  have eKab : E + P.mγ ^ 2 * a + P.mγ ^ 2 * b = K + β * b + β * a := by
    rw [← hK_def, ← hβ_def]; ring
  have hβ' : P.Λ ^ 2 - P.mγ ^ 2 = -β := by rw [← hβ_def]; ring
  rw [eK, eKa, eKb, eKab, hβ', ← hX₁, ← hX₂]
  have n1 := pK.ne'
  have n2 := pKa.ne'
  have n3 := pKb.ne'
  have n4 := pKab.ne'
  have nU := hU.ne'
  field_simp
  ring

end Eval

/-! ### The class `C₊` on `Δ₄` -/

/-- **The class `C₊` on the 4-simplex of the merged groups** (`m = e = 1`, `0 < m_γ < Λ`):
`16π⁴ (1/(64 m⁵)) (1/i) openZero C₊ = ∫_{Δ₄} cornerF4`, and `cornerF4` is integrable on `Δ₄`. -/
theorem sixteen_pi_pow_four_mul_openZero_Cp_eq_simplex {P : Params} (hm : P.m = 1)
    (he : P.e = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    IntegrableOn (fun y => cornerF4 P (simplexPoint y)) (simplexSet 4) ∧
    16 * (π : ℂ) ^ 4 * (1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * openZero .Cp P)) =
      ((∫ y in simplexSet 4, cornerF4 P (simplexPoint y) : ℝ) : ℂ) := by
  obtain ⟨hI, he'⟩ := integral_simplex_cornerSplit (integrableOn_cornerG hm hmγ hΛ.le)
  have hae : (fun y => (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * cornerMerged (cornerG P) (simplexPoint y))
      =ᵐ[volume.restrict (simplexSet 4)] fun y => cornerF4 P (simplexPoint y) := by
    filter_upwards [ae_simplexPoint_pos (by norm_num : 0 < 4)] with y hy
    exact cornerMerged_cornerG hmγ hΛ hy
  refine ⟨(hI.const_mul ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2)).congr hae, ?_⟩
  rw [sixteen_pi_pow_four_mul_openZero_Cp hm he, he', ← integral_const_mul, integral_congr_ae hae]

end QED.TwoLoop.UnitSCReduce

end
