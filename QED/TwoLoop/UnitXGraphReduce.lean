/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraphReduceBound
public import QED.TwoLoop.UnitXGraphReduceMerge
public import QED.TwoLoop.UnitLGraphReduce
public import QED.Integration.SimplexMergePV
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The crossed-ladder unit on the 4-simplex of the merged groups

Section 8 of `docs/TWO-LOOP-UNITS.md`, the graph half of the X unit, item (ii) (the analogue of
`QED/TwoLoop/UnitLGraphReduce.lean`). The three line pairs of the crossed ladder are merged
(`QED/TwoLoop/UnitXGraphReduceMerge.lean`): the split `t` of the electron pair enters `Ψ₁, Ψ₂`
affinely (`gPsi1_affine`, `gPsi2_affine`), so its integral is `z_M` times the value at the
midpoint `t = z_M/2`; the two Pauli–Villars splits are integrated out as divided differences
(`integral_pv_double`), which cancel the factor `(Λ² - m_γ²)²`. With
`V_{μ_a μ_b} = E + μ_a z_a + μ_b z_b` (`μ ∈ {m_γ², Λ²}`) and
`crossedTerm μ_a μ_b = z_M [Ψ₁(z_M/2)/(2U⁶ V²) - Ψ₂(z_M/2)/(2U⁵ V)]`:

* `crossedMerged_crossedG`: for positive group sums,
  `(Λ² - m_γ²)² ∫∫∫ crossedG = crossedF4 = ∑_{μ_a, μ_b} ± crossedTerm μ_a μ_b`, the signs `+` for
  equal masses and `-` otherwise;
* `sixteen_pi_pow_four_mul_unitF2_X_eq_simplex`: **the crossed-ladder unit on `Δ₄`**,
  `16π⁴ · unitF2 X P = ∫_{Δ₄} crossedF4(z_A, z_M, z_c, z_a, z_b)`, for `m = e = 1`,
  `0 < m_γ < Λ`, and `crossedF4 ∘ simplexPoint` is integrable on `Δ₄`.

At `m_γ = 0`, `Λ = ∞` the term `crossedTerm 0 0` is the integrand `A₂/D² + A₁/D` of the engine of
`scripts/numerics/two_loop_unit_integrals.py` for the graph `X` in the groups
`(z₁, z₂, z₃, z_a, z_b) = (z_A, z_M, z_c, z_a, z_b)` (exact identity checked by
`scripts/numerics/crossed_graph/target_check.py`), the starting point (4.1) of section 4 of the
document.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace QED.TwoLoop.UnitXGraph

open QED.WickModel QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.UnitLGraphReduce
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.SimplexMerge

/-! ### The polynomials in the group sums -/

/-- `Ψ₁` in the group sums and the split `t` of the electron pair. -/
def gPsi1 (A t M c a b : ℝ) : ℝ :=
  psiT1h (gXan A M c a b 0) (gXan A M c a b 1) (gXan A M c a b 2) (gXan A M c a b 3)
    (gXbn A t M c a b 0) (gXbn A t M c a b 1) (gXbn A t M c a b 2) (gXbn A t M c a b 3)
    (gXU A M c a b)

/-- `Ψ₂` in the group sums and the split `t` of the electron pair. -/
def gPsi2 (A t M c a b : ℝ) : ℝ :=
  psiT2h (gXan A M c a b 0) (gXan A M c a b 1) (gXan A M c a b 2) (gXan A M c a b 3)
    (gXbn A t M c a b 0) (gXbn A t M c a b 1) (gXbn A t M c a b 2) (gXbn A t M c a b 3)
    (A + a) (A + a) (-M) (A + c + a + b) (c + b) (c + b) (gXU A M c a b)

theorem psiT1h_affine (a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 u t : ℝ) :
    psiT1h a0 a1 a2 a3 (b0 + t * d0) (b1 + t * d1) (b2 + t * d2) (b3 + t * d3) u =
      psiT1h a0 a1 a2 a3 b0 b1 b2 b3 u +
        t * (psiT1h a0 a1 a2 a3 (b0 + d0) (b1 + d1) (b2 + d2) (b3 + d3) u -
          psiT1h a0 a1 a2 a3 b0 b1 b2 b3 u) := by
  simp only [psiT1h]; ring

theorem psiT2h_affine (a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 c01 c02 c03 c12 c13 c23 u t : ℝ) :
    psiT2h a0 a1 a2 a3 (b0 + t * d0) (b1 + t * d1) (b2 + t * d2) (b3 + t * d3) c01 c02 c03 c12
        c13 c23 u =
      psiT2h a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u +
        t * (psiT2h a0 a1 a2 a3 (b0 + d0) (b1 + d1) (b2 + d2) (b3 + d3) c01 c02 c03 c12 c13 c23
          u - psiT2h a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u) := by
  simp only [psiT2h]; ring

theorem gXbn_affine (A t M c a b : ℝ) (k : Fin 4) :
    gXbn A t M c a b k = gXbn A 0 M c a b k + t * (gXbn A 1 M c a b k - gXbn A 0 M c a b k) := by
  fin_cases k <;> simp [gXbn] <;> ring

/-- `Ψ₁` is affine in the split. -/
theorem gPsi1_affine (A t M c a b : ℝ) :
    gPsi1 A t M c a b = gPsi1 A 0 M c a b + t * (gPsi1 A 1 M c a b - gPsi1 A 0 M c a b) := by
  unfold gPsi1
  rw [gXbn_affine A t M c a b 0, gXbn_affine A t M c a b 1, gXbn_affine A t M c a b 2,
    gXbn_affine A t M c a b 3, psiT1h_affine]
  simp only [add_sub_cancel]

/-- `Ψ₂` is affine in the split. -/
theorem gPsi2_affine (A t M c a b : ℝ) :
    gPsi2 A t M c a b = gPsi2 A 0 M c a b + t * (gPsi2 A 1 M c a b - gPsi2 A 0 M c a b) := by
  unfold gPsi2
  rw [gXbn_affine A t M c a b 0, gXbn_affine A t M c a b 1, gXbn_affine A t M c a b 2,
    gXbn_affine A t M c a b 3, psiT2h_affine]
  simp only [add_sub_cancel]

/-- The integral of an affine function is the length times the midpoint value. -/
theorem integral_affine_eq_mid {f : ℝ → ℝ} (p q : ℝ) (hf : ∀ t, f t = p + t * q) (M : ℝ) :
    ∫ t in (0 : ℝ)..M, f t = M * f (M / 2) := by
  have hi : IntervalIntegrable (fun t : ℝ => t * q) volume 0 M :=
    (continuous_id.mul continuous_const).intervalIntegrable 0 M
  rw [intervalIntegral.integral_congr (g := fun t => p + t * q) fun t _ => hf t,
    intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_const, intervalIntegral.integral_mul_const, integral_id, hf]
  simp only [smul_eq_mul, sub_zero]
  ring

/-! ### The integrand on the merged simplex -/

/-- One mass combination of the merged integrand:
`z_M [Ψ₁(z_M/2)/(2U⁶ V²) - Ψ₂(z_M/2)/(2U⁵ V)]`, `V = E + μ_a z_a + μ_b z_b`. -/
noncomputable def crossedTerm (μa μb A M c a b : ℝ) : ℝ :=
  M * (gPsi1 A (M / 2) M c a b / (2 * gXU A M c a b ^ 6 * (gXE A M c a b + μa * a + μb * b) ^ 2) -
    gPsi2 A (M / 2) M c a b / (2 * gXU A M c a b ^ 5 * (gXE A M c a b + μa * a + μb * b)))

/-- **The merged integrand**: the Pauli–Villars-signed sum of the four mass combinations. -/
noncomputable def crossedF4 (P : Params) (w : Fin 5 → ℝ) : ℝ :=
  crossedTerm (P.mγ ^ 2) (P.mγ ^ 2) (w 0) (w 1) (w 2) (w 3) (w 4) -
    crossedTerm (P.mγ ^ 2) (P.Λ ^ 2) (w 0) (w 1) (w 2) (w 3) (w 4) -
    crossedTerm (P.Λ ^ 2) (P.mγ ^ 2) (w 0) (w 1) (w 2) (w 3) (w 4) +
    crossedTerm (P.Λ ^ 2) (P.Λ ^ 2) (w 0) (w 1) (w 2) (w 3) (w 4)

theorem gXU_pos {A M c a b : ℝ} (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a)
    (hb : 0 < b) : 0 < gXU A M c a b := by
  unfold gXU; positivity

theorem gXE_nonneg {A M c a b : ℝ} (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) (ha : 0 < a)
    (hb : 0 < b) : 0 ≤ gXE A M c a b := by
  have := gXU_pos hA hM hc ha hb
  unfold gXE gXEn at *; positivity

/-! ### The Pauli–Villars double split -/

/-- **The two Pauli–Villars split integrals** as double divided differences. -/
theorem integral_pv_double {K β a b T₁ T₂ : ℝ} (hβ : β ≠ 0) (pK : 0 < K) (pKa : 0 < K + β * a)
    (pKb : 0 < K + β * b) (pKab : 0 < K + β * b + β * a) :
    ∫ t₂ in (0 : ℝ)..a, ∫ t₁ in (0 : ℝ)..b, (T₁ * ((K + β * t₂ + β * t₁) ^ 4)⁻¹ +
        T₂ * ((K + β * t₂ + β * t₁) ^ 3)⁻¹) =
      T₁ / (3 * β) * (((K ^ 2)⁻¹ - ((K + β * a) ^ 2)⁻¹) / (2 * β) -
        (((K + β * b) ^ 2)⁻¹ - ((K + β * b + β * a) ^ 2)⁻¹) / (2 * β)) +
      T₂ / (2 * β) * ((K⁻¹ - (K + β * a)⁻¹) / β -
        ((K + β * b)⁻¹ - (K + β * b + β * a)⁻¹) / β) := by
  have pos₁ : ∀ t₂ ∈ uIcc 0 a, 0 < K + β * t₂ := fun t₂ ht₂ =>
    pos_of_mem_uIcc_affine pK pKa ht₂
  have pos₂ : ∀ t₂ ∈ uIcc 0 a, 0 < K + β * t₂ + β * b := fun t₂ ht₂ => by
    have := pos_of_mem_uIcc_affine pKb pKab ht₂
    linarith
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

/-! ### Evaluating the split integrals -/

section Eval

variable {P : Params} {w : Fin 5 → ℝ}

theorem crossedSplit_xA (t₃ t₂ t₁ : ℝ) : xA (crossedSplit w t₃ t₂ t₁) = w 0 := rfl
theorem crossedSplit_xt (t₃ t₂ t₁ : ℝ) : xt (crossedSplit w t₃ t₂ t₁) = t₃ := rfl
theorem crossedSplit_xM (t₃ t₂ t₁ : ℝ) : xM (crossedSplit w t₃ t₂ t₁) = w 1 := by
  simp [xM, crossedSplit]
theorem crossedSplit_xc (t₃ t₂ t₁ : ℝ) : xc (crossedSplit w t₃ t₂ t₁) = w 2 := rfl
theorem crossedSplit_xa (t₃ t₂ t₁ : ℝ) : xa (crossedSplit w t₃ t₂ t₁) = w 3 := by
  simp [xa, crossedSplit]
theorem crossedSplit_xb (t₃ t₂ t₁ : ℝ) : xb (crossedSplit w t₃ t₂ t₁) = w 4 := by
  simp [xb, crossedSplit]

/-- `crossedG` at a split point: `T₁ V⁻⁴ + T₂ V⁻³` with `T₁ = 3Ψ₁(t₃)/U⁶`, `T₂ = -Ψ₂(t₃)/U⁵`
and `V = K + β t₂ + β t₁`, `K = E + Λ² (z_a + z_b)`, `β = m_γ² - Λ²`. -/
theorem crossedG_crossedSplit (t₃ t₂ t₁ : ℝ) :
    crossedG P (crossedSplit w t₃ t₂ t₁) =
      3 * gPsi1 (w 0) t₃ (w 1) (w 2) (w 3) (w 4) / gXU (w 0) (w 1) (w 2) (w 3) (w 4) ^ 6 *
          (((gXE (w 0) (w 1) (w 2) (w 3) (w 4) + P.Λ ^ 2 * (w 3 + w 4) +
            (P.mγ ^ 2 - P.Λ ^ 2) * t₂) + (P.mγ ^ 2 - P.Λ ^ 2) * t₁) ^ 4)⁻¹ +
        -gPsi2 (w 0) t₃ (w 1) (w 2) (w 3) (w 4) / gXU (w 0) (w 1) (w 2) (w 3) (w 4) ^ 5 *
          (((gXE (w 0) (w 1) (w 2) (w 3) (w 4) + P.Λ ^ 2 * (w 3 + w 4) +
            (P.mγ ^ 2 - P.Λ ^ 2) * t₂) + (P.mγ ^ 2 - P.Λ ^ 2) * t₁) ^ 3)⁻¹ := by
  have eV : crossedV P (crossedSplit w t₃ t₂ t₁) =
      (gXE (w 0) (w 1) (w 2) (w 3) (w 4) + P.Λ ^ 2 * (w 3 + w 4) + (P.mγ ^ 2 - P.Λ ^ 2) * t₂) +
        (P.mγ ^ 2 - P.Λ ^ 2) * t₁ := by
    simp only [crossedV, crossedSplit_xA, crossedSplit_xM, crossedSplit_xc, crossedSplit_xa,
      crossedSplit_xb]
    have e4 : crossedSplit w t₃ t₂ t₁ 4 = t₂ := rfl
    have e5 : crossedSplit w t₃ t₂ t₁ 5 = t₁ := rfl
    have e6 : crossedSplit w t₃ t₂ t₁ 6 = w 3 - t₂ := rfl
    have e7 : crossedSplit w t₃ t₂ t₁ 7 = w 4 - t₁ := rfl
    rw [e4, e5, e6, e7]
    ring
  have eU : xU (crossedSplit w t₃ t₂ t₁) = gXU (w 0) (w 1) (w 2) (w 3) (w 4) := by
    simp only [xU, crossedSplit_xA, crossedSplit_xM, crossedSplit_xc, crossedSplit_xa,
      crossedSplit_xb]
  have e1 : xPsi1 (crossedSplit w t₃ t₂ t₁) = gPsi1 (w 0) t₃ (w 1) (w 2) (w 3) (w 4) := by
    simp only [xPsi1, gPsi1, xan, xbn, eU, crossedSplit_xA, crossedSplit_xt, crossedSplit_xM,
      crossedSplit_xc, crossedSplit_xa, crossedSplit_xb]
  have e2 : xPsi2 (crossedSplit w t₃ t₂ t₁) = gPsi2 (w 0) t₃ (w 1) (w 2) (w 3) (w 4) := by
    simp only [xPsi2, gPsi2, xan, xbn, xCn, eU, crossedSplit_xA, crossedSplit_xt,
      crossedSplit_xM, crossedSplit_xc, crossedSplit_xa, crossedSplit_xb]
    rfl
  unfold crossedG
  rw [eV, eU, e1, e2]
  simp only [div_eq_mul_inv, mul_inv, neg_mul]
  ring

/-- **The split integrals of the crossed-ladder integrand**: for positive group sums and
`0 < m_γ < Λ`, `(Λ² - m_γ²)² crossedMerged crossedG = crossedF4`. -/
theorem crossedMerged_crossedG (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) (hw : ∀ i, 0 < w i) :
    (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * crossedMerged (crossedG P) w = crossedF4 P w := by
  unfold crossedMerged crossedF4
  simp only [crossedG_crossedSplit]
  obtain ⟨A, hA_def⟩ : ∃ A, w 0 = A := ⟨_, rfl⟩
  obtain ⟨M, hM_def⟩ : ∃ M, w 1 = M := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c, w 2 = c := ⟨_, rfl⟩
  obtain ⟨a, ha_def⟩ : ∃ a, w 3 = a := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b, w 4 = b := ⟨_, rfl⟩
  have hA : 0 < A := hA_def ▸ hw 0
  have hM : 0 < M := hM_def ▸ hw 1
  have hc : 0 < c := hc_def ▸ hw 2
  have ha : 0 < a := ha_def ▸ hw 3
  have hb : 0 < b := hb_def ▸ hw 4
  rw [hA_def, hM_def, hc_def, ha_def, hb_def]
  obtain ⟨E, hE_def⟩ : ∃ E, gXE A M c a b = E := ⟨_, rfl⟩
  have hE : 0 ≤ E := hE_def ▸ gXE_nonneg hA hM hc ha hb
  have hU : 0 < gXU A M c a b := gXU_pos hA hM hc ha hb
  simp only [crossedTerm, hE_def]
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
      (3 * gPsi1 A t₃ M c a b / gXU A M c a b ^ 6 * ((K + β * t₂ + β * t₁) ^ 4)⁻¹ +
        -gPsi2 A t₃ M c a b / gXU A M c a b ^ 5 * ((K + β * t₂ + β * t₁) ^ 3)⁻¹) =
      3 * gPsi1 A t₃ M c a b / gXU A M c a b ^ 6 / (3 * β) * X₁ +
        -gPsi2 A t₃ M c a b / gXU A M c a b ^ 5 / (2 * β) * X₂ := fun t₃ => by
    rw [integral_pv_double hβ pK pKa pKb pKab, hX₁, hX₂]
  simp only [h₂]
  -- the electron split
  rw [integral_affine_eq_mid
    (3 * gPsi1 A 0 M c a b / gXU A M c a b ^ 6 / (3 * β) * X₁ +
      -gPsi2 A 0 M c a b / gXU A M c a b ^ 5 / (2 * β) * X₂)
    (3 * (gPsi1 A 1 M c a b - gPsi1 A 0 M c a b) / gXU A M c a b ^ 6 / (3 * β) * X₁ +
      -(gPsi2 A 1 M c a b - gPsi2 A 0 M c a b) / gXU A M c a b ^ 5 / (2 * β) * X₂)
    (fun t => by rw [gPsi1_affine A t, gPsi2_affine A t]; ring)]
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

/-! ### The crossed-ladder unit on `Δ₄` -/

/-- **The crossed-ladder unit on the 4-simplex of the merged groups** (`m = e = 1`,
`0 < m_γ < Λ`): `16π⁴ · unitF2 X P = ∫_{Δ₄} crossedF4`, and `crossedF4` is integrable on `Δ₄`. -/
theorem sixteen_pi_pow_four_mul_unitF2_X_eq_simplex {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (hmγ : 0 < P.mγ) (hΛ : P.mγ < P.Λ) :
    IntegrableOn (fun y => crossedF4 P (simplexPoint y)) (simplexSet 4) ∧
    16 * (π : ℂ) ^ 4 * QED.TwoLoop.UnitsRegulated.unitF2 .X P =
      ((∫ y in simplexSet 4, crossedF4 P (simplexPoint y) : ℝ) : ℂ) := by
  obtain ⟨hI, he'⟩ := integral_simplex_crossedSplit (integrableOn_crossedG hm hmγ hΛ.le)
  have hae : (fun y => (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 * crossedMerged (crossedG P) (simplexPoint y))
      =ᵐ[volume.restrict (simplexSet 4)] fun y => crossedF4 P (simplexPoint y) := by
    filter_upwards [ae_simplexPoint_pos (by norm_num : 0 < 4)] with y hy
    exact crossedMerged_crossedG hmγ hΛ hy
  refine ⟨(hI.const_mul ((P.Λ ^ 2 - P.mγ ^ 2) ^ 2)).congr hae, ?_⟩
  rw [sixteen_pi_pow_four_mul_unitF2_X hm he, he', ← integral_const_mul, integral_congr_ae hae]

end QED.TwoLoop.UnitXGraph

end
