/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraphReduceV
public import QED.TwoLoop.UnitLGraphReduceBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integrability of the crossed-ladder integrand on the simplex

The real integrand `crossedG` of the crossed-ladder unit (`QED/TwoLoop/UnitXGraphReduceV.lean`)
is integrable on the simplex `Δ₇` (`integrableOn_crossedG`), for `0 < m_γ ≤ Λ` and `m = 1`.

The bound: on the open simplex the slot numerators satisfy `|ãₖ|, |b̃ₖ| ≤ 2U`
(`abs_xan_le`, `abs_xbn_le`) and the contraction numerators `|C̃_{kl}| ≤ 1`; by homogeneity
`Ψ₁ = U⁴ Ψ₁(ã/U, b̃/U, 1)`, `Ψ₂ = U² Ψ₂(ã/U, b̃/U, C̃, 1)`, and the polynomials are bounded on the
compact cubes (`exists_bound_psiT1h`, `exists_bound_psiT2h`), so `|Ψ₁| ≤ C₁ U⁴`, `|Ψ₂| ≤ C₂ U²`.
With `U ≤ 1` and `V ≥ v₀ = (3/4) min(1/4, m_γ²)`
(`QED.Integration.TwoLoop.symanzikV_classXPV_ge`), `|crossedG| ≤ C/U³`. Finally
`∏ₖ zₖ ≤ (z_A z_M)(z_M z_c)(z_a z_b)² ≤ U⁴`, so `U⁻³ ≤ ∏ₖ zₖ^{-3/4}`, which is integrable on the
simplex (`QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow`).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.TwoLoop.UnitXGraph

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitLGraph
open QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.Bridge QED.TwoLoop.UnitLGraphReduce
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikV symanzikU
  simplexPoint_castSucc simplexPoint_last)

/-! ### Bounds on the slot data -/

section Slots

variable {z : Fin 8 → ℝ}

theorem xU_pos (hz : ∀ i, 0 < z i) : 0 < xU z := by
  have := hz 0; have := hz 1; have := hz 2; have := hz 3
  have := hz 4; have := hz 5; have := hz 6; have := hz 7
  unfold xU gXU xA xM xc xa xb
  positivity

theorem abs_xan_le (hz : ∀ i, 0 < z i) (k : Fin 4) : |xan z k| ≤ 2 * xU z := by
  have h0 := (hz 0).le; have h1 := (hz 1).le; have h2 := (hz 2).le; have h3 := (hz 3).le
  have h4 := (hz 4).le; have h5 := (hz 5).le; have h6 := (hz 6).le; have h7 := (hz 7).le
  rw [abs_le]
  fin_cases k <;>
    simp only [xan, gXan, xU, gXU, xA, xM, xc, xa, xb, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] <;>
    constructor <;> nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h0 h3,
      mul_nonneg h0 h5, mul_nonneg h0 h7, mul_nonneg h1 h3, mul_nonneg h2 h3, mul_nonneg h1 h4,
      mul_nonneg h1 h5, mul_nonneg h1 h6, mul_nonneg h1 h7, mul_nonneg h2 h4, mul_nonneg h2 h5,
      mul_nonneg h2 h6, mul_nonneg h2 h7, mul_nonneg h3 h4, mul_nonneg h3 h6, mul_nonneg h4 h5,
      mul_nonneg h4 h7, mul_nonneg h6 h5, mul_nonneg h6 h7, mul_nonneg h0 h4, mul_nonneg h0 h6,
      mul_nonneg h3 h5, mul_nonneg h3 h7]

theorem abs_xbn_le (hz : ∀ i, 0 < z i) (k : Fin 4) : |xbn z k| ≤ 2 * xU z := by
  have h0 := (hz 0).le; have h1 := (hz 1).le; have h2 := (hz 2).le; have h3 := (hz 3).le
  have h4 := (hz 4).le; have h5 := (hz 5).le; have h6 := (hz 6).le; have h7 := (hz 7).le
  rw [abs_le]
  fin_cases k <;>
    simp only [xbn, gXbn, xU, gXU, xA, xt, xM, xc, xa, xb, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    constructor <;> nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h0 h3,
      mul_nonneg h0 h5, mul_nonneg h0 h7, mul_nonneg h1 h3, mul_nonneg h2 h3, mul_nonneg h1 h4,
      mul_nonneg h1 h5, mul_nonneg h1 h6, mul_nonneg h1 h7, mul_nonneg h2 h4, mul_nonneg h2 h5,
      mul_nonneg h2 h6, mul_nonneg h2 h7, mul_nonneg h3 h4, mul_nonneg h3 h6, mul_nonneg h4 h5,
      mul_nonneg h4 h7, mul_nonneg h6 h5, mul_nonneg h6 h7, mul_nonneg h0 h4, mul_nonneg h0 h6,
      mul_nonneg h3 h5, mul_nonneg h3 h7]

theorem abs_xCn_le (hz : ∀ i, 0 < z i) (hz1 : ∑ i, z i = 1) (k : Fin 6) : |xCn z k| ≤ 2 := by
  rw [Fin.sum_univ_eight] at hz1
  have h0 := (hz 0).le; have h1 := (hz 1).le; have h2 := (hz 2).le; have h3 := (hz 3).le
  have h4 := (hz 4).le; have h5 := (hz 5).le; have h6 := (hz 6).le; have h7 := (hz 7).le
  rw [abs_le]
  fin_cases k <;> simp [xCn, xA, xM, xc, xa, xb] <;> constructor <;> linarith

theorem xU_le_one (hz : ∀ i, 0 < z i) (hz1 : ∑ i, z i = 1) : xU z ≤ 1 := by
  rw [Fin.sum_univ_eight] at hz1
  have h0 := (hz 0).le; have h1 := (hz 1).le; have h2 := (hz 2).le; have h3 := (hz 3).le
  have h4 := (hz 4).le; have h5 := (hz 5).le; have h6 := (hz 6).le; have h7 := (hz 7).le
  have hsq : xU z ≤ (z 0 + z 1 + z 2 + z 3 + z 4 + z 5 + z 6 + z 7) ^ 2 := by
    unfold xU gXU xA xM xc xa xb
    nlinarith [sq_nonneg (z 0), sq_nonneg (z 1 + z 2), sq_nonneg (z 3), sq_nonneg (z 4 + z 6),
      sq_nonneg (z 5 + z 7), mul_nonneg h0 h4, mul_nonneg h0 h6, mul_nonneg h3 h5,
      mul_nonneg h3 h7, mul_nonneg h1 h2]
  rw [hz1, one_pow] at hsq
  exact hsq

end Slots

/-! ### Bounds on the polynomials -/

/-- `Ψ₂` is homogeneous of degree `2` in the slot data and `u`. -/
theorem psiT2h_smul_slot (s a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u : ℝ) :
    psiT2h (s * a0) (s * a1) (s * a2) (s * a3) (s * b0) (s * b1) (s * b2) (s * b3) c01 c02 c03
        c12 c13 c23 (s * u) =
      s ^ 2 * psiT2h a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 u := by
  simp only [psiT2h]; ring

/-- The cube `[-2, 2]ⁿ`. -/
def cube2 (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Icc (-2 : ℝ) 2

theorem isCompact_cube2 (n : ℕ) : IsCompact (cube2 n) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem exists_bound_psiT1h : ∃ C : ℝ, ∀ a0 a1 a2 a3 b0 b1 b2 b3 : ℝ,
    a0 ∈ Icc (-2 : ℝ) 2 → a1 ∈ Icc (-2 : ℝ) 2 → a2 ∈ Icc (-2 : ℝ) 2 → a3 ∈ Icc (-2 : ℝ) 2 →
    b0 ∈ Icc (-2 : ℝ) 2 → b1 ∈ Icc (-2 : ℝ) 2 → b2 ∈ Icc (-2 : ℝ) 2 → b3 ∈ Icc (-2 : ℝ) 2 →
    |psiT1h a0 a1 a2 a3 b0 b1 b2 b3 1| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_cube2 8).exists_bound_of_continuousOn
    (f := fun v : Fin 8 → ℝ => psiT1h (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) 1)
    (by unfold psiT1h; fun_prop)
  refine ⟨C, fun a0 a1 a2 a3 b0 b1 b2 b3 h0 h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  have hv : ![a0, a1, a2, a3, b0, b1, b2, b3] ∈ cube2 8 := by
    intro i _
    fin_cases i <;> simpa
  simpa [Real.norm_eq_abs] using hC _ hv

theorem exists_bound_psiT2h : ∃ C : ℝ, ∀ a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 : ℝ,
    a0 ∈ Icc (-2 : ℝ) 2 → a1 ∈ Icc (-2 : ℝ) 2 → a2 ∈ Icc (-2 : ℝ) 2 → a3 ∈ Icc (-2 : ℝ) 2 →
    b0 ∈ Icc (-2 : ℝ) 2 → b1 ∈ Icc (-2 : ℝ) 2 → b2 ∈ Icc (-2 : ℝ) 2 → b3 ∈ Icc (-2 : ℝ) 2 →
    c01 ∈ Icc (-2 : ℝ) 2 → c02 ∈ Icc (-2 : ℝ) 2 → c03 ∈ Icc (-2 : ℝ) 2 →
    c12 ∈ Icc (-2 : ℝ) 2 → c13 ∈ Icc (-2 : ℝ) 2 → c23 ∈ Icc (-2 : ℝ) 2 →
    |psiT2h a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 1| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_cube2 14).exists_bound_of_continuousOn
    (f := fun v : Fin 14 → ℝ => psiT2h (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)
      (v 9) (v 10) (v 11) (v 12) (v 13) 1)
    (by unfold psiT2h; fun_prop)
  refine ⟨C, fun a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10 h11 h12 h13 => ?_⟩
  have hv : ![a0, a1, a2, a3, b0, b1, b2, b3, c01, c02, c03, c12, c13, c23] ∈ cube2 14 := by
    intro i _
    fin_cases i <;> simpa
  simpa [Real.norm_eq_abs] using hC _ hv

theorem mem_Icc_div_of_abs_le {x U : ℝ} (hU : 0 < U) (h : |x| ≤ 2 * U) :
    x / U ∈ Icc (-2 : ℝ) 2 := by
  rw [abs_le] at h
  constructor
  · rw [le_div_iff₀ hU]; linarith
  · rw [div_le_iff₀ hU]; linarith

theorem abs_xPsi1_le {C : ℝ} (hC : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : ℝ,
      a0 ∈ Icc (-2 : ℝ) 2 → a1 ∈ Icc (-2 : ℝ) 2 → a2 ∈ Icc (-2 : ℝ) 2 → a3 ∈ Icc (-2 : ℝ) 2 →
      b0 ∈ Icc (-2 : ℝ) 2 → b1 ∈ Icc (-2 : ℝ) 2 → b2 ∈ Icc (-2 : ℝ) 2 → b3 ∈ Icc (-2 : ℝ) 2 →
      |psiT1h a0 a1 a2 a3 b0 b1 b2 b3 1| ≤ C)
    {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i) : |xPsi1 z| ≤ C * xU z ^ 4 := by
  have hU := xU_pos hz
  have hb := hC _ _ _ _ _ _ _ _ (mem_Icc_div_of_abs_le hU (abs_xan_le hz 0))
    (mem_Icc_div_of_abs_le hU (abs_xan_le hz 1)) (mem_Icc_div_of_abs_le hU (abs_xan_le hz 2))
    (mem_Icc_div_of_abs_le hU (abs_xan_le hz 3)) (mem_Icc_div_of_abs_le hU (abs_xbn_le hz 0))
    (mem_Icc_div_of_abs_le hU (abs_xbn_le hz 1)) (mem_Icc_div_of_abs_le hU (abs_xbn_le hz 2))
    (mem_Icc_div_of_abs_le hU (abs_xbn_le hz 3))
  have hc : ∀ x, xU z * (x / xU z) = x := fun x => by field_simp
  have e := psiT1h_smul (xU z) (xan z 0 / xU z) (xan z 1 / xU z) (xan z 2 / xU z)
    (xan z 3 / xU z) (xbn z 0 / xU z) (xbn z 1 / xU z) (xbn z 2 / xU z) (xbn z 3 / xU z) 1
  simp only [hc, mul_one] at e
  rw [xPsi1, e, abs_mul, abs_of_pos (by positivity), mul_comm]
  exact mul_le_mul_of_nonneg_right hb (by positivity)

theorem abs_xPsi2_le {C : ℝ} (hC : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 : ℝ,
      a0 ∈ Icc (-2 : ℝ) 2 → a1 ∈ Icc (-2 : ℝ) 2 → a2 ∈ Icc (-2 : ℝ) 2 → a3 ∈ Icc (-2 : ℝ) 2 →
      b0 ∈ Icc (-2 : ℝ) 2 → b1 ∈ Icc (-2 : ℝ) 2 → b2 ∈ Icc (-2 : ℝ) 2 → b3 ∈ Icc (-2 : ℝ) 2 →
      c01 ∈ Icc (-2 : ℝ) 2 → c02 ∈ Icc (-2 : ℝ) 2 → c03 ∈ Icc (-2 : ℝ) 2 →
      c12 ∈ Icc (-2 : ℝ) 2 → c13 ∈ Icc (-2 : ℝ) 2 → c23 ∈ Icc (-2 : ℝ) 2 →
      |psiT2h a0 a1 a2 a3 b0 b1 b2 b3 c01 c02 c03 c12 c13 c23 1| ≤ C)
    {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i) (hz1 : ∑ i, z i = 1) : |xPsi2 z| ≤ C * xU z ^ 2 := by
  have hU := xU_pos hz
  have hc2 : ∀ k, xCn z k ∈ Icc (-2 : ℝ) 2 := fun k => abs_le.mp (abs_xCn_le hz hz1 k)
  have hb := hC _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mem_Icc_div_of_abs_le hU (abs_xan_le hz 0))
    (mem_Icc_div_of_abs_le hU (abs_xan_le hz 1)) (mem_Icc_div_of_abs_le hU (abs_xan_le hz 2))
    (mem_Icc_div_of_abs_le hU (abs_xan_le hz 3)) (mem_Icc_div_of_abs_le hU (abs_xbn_le hz 0))
    (mem_Icc_div_of_abs_le hU (abs_xbn_le hz 1)) (mem_Icc_div_of_abs_le hU (abs_xbn_le hz 2))
    (mem_Icc_div_of_abs_le hU (abs_xbn_le hz 3)) (hc2 0) (hc2 1) (hc2 2) (hc2 3) (hc2 4) (hc2 5)
  have hc : ∀ x, xU z * (x / xU z) = x := fun x => by field_simp
  have e := psiT2h_smul_slot (xU z) (xan z 0 / xU z) (xan z 1 / xU z) (xan z 2 / xU z)
    (xan z 3 / xU z) (xbn z 0 / xU z) (xbn z 1 / xU z) (xbn z 2 / xU z) (xbn z 3 / xU z)
    (xCn z 0) (xCn z 1) (xCn z 2) (xCn z 3) (xCn z 4) (xCn z 5) 1
  simp only [hc, mul_one] at e
  rw [xPsi2, e, abs_mul, abs_of_pos (by positivity), mul_comm]
  exact mul_le_mul_of_nonneg_right hb (by positivity)

/-! ### The pointwise bound -/

/-- **The pointwise bound** `|crossedG| ≤ (3C₁/v₀⁴ + C₂/v₀³)/U³` on the open simplex. -/
theorem abs_crossedG_le {P : Params} {C₁ C₂ v₀ : ℝ} (hv₀ : 0 < v₀) {z : Fin 8 → ℝ}
    (hz : ∀ i, 0 < z i) (hz1 : ∑ i, z i = 1) (h₁ : |xPsi1 z| ≤ C₁ * xU z ^ 4)
    (h₂ : |xPsi2 z| ≤ C₂ * xU z ^ 2) (hV : v₀ ≤ crossedV P z) :
    |crossedG P z| ≤ (3 * C₁ / v₀ ^ 4 + C₂ / v₀ ^ 3) / xU z ^ 3 := by
  have hU := xU_pos hz
  have hU1 := xU_le_one hz hz1
  have hV0 : 0 < crossedV P z := hv₀.trans_le hV
  have hC₁ : 0 ≤ C₁ := by
    have := (abs_nonneg _).trans h₁
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have hC₂ : 0 ≤ C₂ := by
    have := (abs_nonneg _).trans h₂
    exact nonneg_of_mul_nonneg_left this (by positivity)
  set U := xU z
  set V := crossedV P z
  have e1 : |3 * xPsi1 z / (U ^ 6 * V ^ 4)| ≤ 3 * C₁ / v₀ ^ 4 / U ^ 3 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < U ^ 6 * V ^ 4), abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc 3 * |xPsi1 z| / (U ^ 6 * V ^ 4) ≤ 3 * (C₁ * U ^ 4) / (U ^ 6 * v₀ ^ 4) := by
          refine div_le_div₀ (by positivity) (by linarith) (by positivity) ?_
          gcongr
      _ = 3 * C₁ / v₀ ^ 4 / U ^ 2 := by field_simp
      _ ≤ 3 * C₁ / v₀ ^ 4 / U ^ 3 := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          calc U ^ 3 = U ^ 2 * U := by ring
            _ ≤ U ^ 2 * 1 := by gcongr
            _ = U ^ 2 := mul_one _
  have e2 : |xPsi2 z / (U ^ 5 * V ^ 3)| ≤ C₂ / v₀ ^ 3 / U ^ 3 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < U ^ 5 * V ^ 3)]
    calc |xPsi2 z| / (U ^ 5 * V ^ 3) ≤ C₂ * U ^ 2 / (U ^ 5 * v₀ ^ 3) := by
          refine div_le_div₀ (by positivity) h₂ (by positivity) ?_
          gcongr
      _ = C₂ / v₀ ^ 3 / U ^ 3 := by field_simp
  unfold crossedG
  calc _ ≤ _ := abs_sub _ _
    _ ≤ 3 * C₁ / v₀ ^ 4 / U ^ 3 + C₂ / v₀ ^ 3 / U ^ 3 := add_le_add e1 e2
    _ = (3 * C₁ / v₀ ^ 4 + C₂ / v₀ ^ 3) / U ^ 3 := by ring

/-! ### The product of the coordinates -/

theorem prod_le_xU_pow_four {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ xU z ^ 4 := by
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
  have h4 := hz 4; have h5 := hz 5; have h6 := hz 6; have h7 := hz 7
  have hA : 0 ≤ xA z := h0
  have hM : 0 ≤ xM z := by unfold xM; positivity
  have hc : 0 ≤ xc z := h3
  have ha : 0 ≤ xa z := by unfold xa; positivity
  have hb : 0 ≤ xb z := by unfold xb; positivity
  have h12 : z 1 * z 2 ≤ xM z ^ 2 := by unfold xM; nlinarith
  have h46 : z 4 * z 6 ≤ xa z ^ 2 := by unfold xa; nlinarith
  have h57 : z 5 * z 7 ≤ xb z ^ 2 := by unfold xb; nlinarith
  have hU0 : 0 ≤ xU z := by unfold xU gXU; positivity
  have hAM : xA z * xM z ≤ xU z := by
    unfold xU gXU
    nlinarith [mul_nonneg hA hc, mul_nonneg hA hb, mul_nonneg hM hc, mul_nonneg hM ha,
      mul_nonneg hM hb, mul_nonneg hc ha, mul_nonneg ha hb]
  have hMc : xM z * xc z ≤ xU z := by
    unfold xU gXU
    nlinarith [mul_nonneg hA hc, mul_nonneg hA hb, mul_nonneg hA hM, mul_nonneg hM ha,
      mul_nonneg hM hb, mul_nonneg hc ha, mul_nonneg ha hb]
  have hab : xa z * xb z ≤ xU z := by
    unfold xU gXU
    nlinarith [mul_nonneg hA hc, mul_nonneg hA hb, mul_nonneg hA hM, mul_nonneg hM ha,
      mul_nonneg hM hb, mul_nonneg hc ha, mul_nonneg hM hc]
  rw [Fin.prod_univ_eight]
  calc z 0 * z 1 * z 2 * z 3 * z 4 * z 5 * z 6 * z 7 =
        xA z * xc z * (z 1 * z 2) * (z 4 * z 6) * (z 5 * z 7) := by unfold xA xc; ring
    _ ≤ xA z * xc z * xM z ^ 2 * xa z ^ 2 * xb z ^ 2 := by
        have p12 := mul_nonneg h1 h2
        have p46 := mul_nonneg h4 h6
        have p57 := mul_nonneg h5 h7
        have pAc := mul_nonneg hA hc
        exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h12 pAc) h46 p46
          (by positivity)) h57 p57 (by positivity)
    _ = (xA z * xM z) * (xM z * xc z) * (xa z * xb z) * (xa z * xb z) := by ring
    _ ≤ xU z * xU z * xU z * xU z := by
        have := mul_nonneg hA hM; have := mul_nonneg hM hc; have := mul_nonneg ha hb
        gcongr
    _ = xU z ^ 4 := by ring

theorem inv_xU_pow_three_le_prod_rpow {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i) :
    (xU z ^ 3)⁻¹ ≤ ∏ i, z i ^ (-(3 / 4 : ℝ)) := by
  have hz' : ∀ i, 0 ≤ z i := fun i => (hz i).le
  have hP : 0 < ∏ i, z i := Finset.prod_pos fun i _ => hz i
  have hle := prod_le_xU_pow_four hz'
  have hU : 0 < xU z := xU_pos hz
  rw [Real.finsetProd_rpow _ _ (fun i _ => hz' i)]
  calc (xU z ^ 3)⁻¹ = (xU z ^ 4) ^ (-(3 / 4 : ℝ)) := by
        rw [← Real.rpow_natCast (xU z) 4, ← Real.rpow_mul hU.le]
        norm_num
    _ ≤ (∏ i, z i) ^ (-(3 / 4 : ℝ)) := Real.rpow_le_rpow_of_nonpos hP hle (by norm_num)

/-! ### Integrability -/

theorem measurable_crossedG (P : Params) : Measurable (crossedG P) := by
  unfold crossedG crossedV gXE gXEn xPsi1 xPsi2 psiT1h psiT2h xan xbn xCn gXan gXbn xU gXU xA xt
    xM xc xa xb
  fun_prop

/-- The lower bound `V ≥ (3/4) min(1/4, m_γ²)` on the simplex. -/
theorem le_crossedV {P : Params} (hm : P.m = 1) (hΛ : P.mγ ^ 2 ≤ P.Λ ^ 2) {z : Fin 8 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : xU z ≠ 0) :
    3 / 4 * min (1 / 4) (P.mγ ^ 2) ≤ crossedV P z := by
  have h := QED.Integration.TwoLoop.symanzikV_classXPV_ge (mass := 1) (mγ := P.mγ)
    (lam₁ := P.mγ) (lam₂ := P.mγ) (lam₃ := P.Λ) (lam₄ := P.Λ)
    (p := restMomentum 1) (p' := restMomentum 1) (by rw [dot_restMomentum])
    (by rw [dot_restMomentum]) (by simp [QED.Minkowski.dot_eq]) le_rfl le_rfl hΛ hΛ hz hz1
    (by rw [← symanzikU_crossed] at hU; exact hU)
  rw [← symanzikV_crossed P hm z]
  convert h using 2
  · norm_num
  · funext i
    rw [hm]
    rfl
  · simp [pvMasses, hm]

/-- **The crossed-ladder integrand is integrable on the simplex** (`m = 1`, `0 < m_γ ≤ Λ`). -/
theorem integrableOn_crossedG {P : Params} (hm : P.m = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ ≤ P.Λ) :
    IntegrableOn (fun x => crossedG P (simplexPoint x)) (simplexSet 7) := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_psiT1h
  obtain ⟨C₂, hC₂⟩ := exists_bound_psiT2h
  set v₀ : ℝ := 3 / 4 * min (1 / 4) (P.mγ ^ 2)
  have hv₀ : 0 < v₀ := by positivity
  have hΛ2 : P.mγ ^ 2 ≤ P.Λ ^ 2 := pow_le_pow_left₀ hmγ.le hΛ 2
  set C : ℝ := 3 * C₁ / v₀ ^ 4 + C₂ / v₀ ^ 3
  have hint : IntegrableOn (fun x => C * ∏ i ∈ Finset.univ, simplexPoint x i ^ (-(3 / 4 : ℝ)))
      (simplexSet 7) :=
    (QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow Finset.univ (by norm_num)
      (by norm_num)).const_mul C
  refine hint.mono' ((measurable_crossedG P).comp
    QED.Integration.TwoLoop.continuous_simplexPoint'.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_mem_openSimplex (by norm_num : 0 < 7)] with x hx
  set z := simplexPoint x
  have hzpos := simplexPoint_pos_of_mem_openSimplex hx
  have hz1 : ∑ i, z i = 1 := by
    simp only [z, Fin.sum_univ_castSucc, simplexPoint_castSucc, simplexPoint_last]; ring
  have hU : 0 < xU z := xU_pos hzpos
  have hV := le_crossedV hm hΛ2 (fun i => (hzpos i).le) hz1 hU.ne'
  have hb := abs_crossedG_le hv₀ hzpos hz1 (abs_xPsi1_le hC₁ hzpos) (abs_xPsi2_le hC₂ hzpos hz1) hV
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans hb
    exact nonneg_of_mul_nonneg_left (by rwa [div_eq_mul_inv] at this) (by positivity)
  rw [Real.norm_eq_abs]
  refine hb.trans ?_
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_xU_pow_three_le_prod_rpow hzpos) hC

end QED.TwoLoop.UnitXGraph

end
