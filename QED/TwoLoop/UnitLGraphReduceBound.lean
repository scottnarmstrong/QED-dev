/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLGraphReduceV
public import QED.Integration.ChengWu
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integrability of the ladder integrand on the simplex

The real integrand `ladderG` of the ladder graph half (`QED/TwoLoop/UnitLGraphReduceV.lean`) is
integrable on the simplex `Δ₇` (`integrableOn_ladderG`), for `0 < m_γ ≤ Λ` and `m = 1`.

The bound is elementary. On the simplex the group sums are at most `1`, `a, c, s z_a ≤ U ≤ 1`
and `|z_a Q| ≤ 6 U²`, and `V ≥ v₀ = (3/4) min(1, m_γ²)`
(`QED.Integration.TwoLoop.symanzikV_classLPV_ge`), so `|ladderG| ≤ C/U³` (`abs_ladderG_core_le`).
Moreover `∏ₖ zₖ ≤ (z_A z_B z_a z_b)² ≤ U⁴`, because `z_A z_b + z_a z_B ≤ U`; hence
`U⁻³ ≤ ∏ₖ zₖ^{-3/4}`, which is integrable on the simplex
(`QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow`).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.TwoLoop.UnitLGraphReduce

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitLGraph
open QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.Bridge
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikV symanzikU
  simplexPoint_castSucc simplexPoint_last)

/-! ### The pointwise bound -/

theorem abs_gQ_le {A B a b : ℝ} (hB : 0 ≤ B) (hb : 0 ≤ b) :
    |gQ A B a b| ≤ 2 * gS B b * ga A B b ^ 2 + 2 * gS B b ^ 2 * |ga A B b| * |a| +
      2 * gS B b * gc B b * a ^ 2 := by
  have hs : 0 ≤ gS B b := by unfold gS; linarith
  have hc : 0 ≤ gc B b := by unfold gc; positivity
  have h1 : |3 * B - 2 * gS B b| ≤ 2 * gS B b := by
    rw [abs_le]; unfold gS; constructor <;> linarith
  have h2 : |4 * B * gS B b - B ^ 2 - 2 * gS B b ^ 2| ≤ 2 * gS B b ^ 2 := by
    rw [abs_le]; unfold gS; constructor <;> nlinarith [sq_nonneg (B + 2 * b), mul_nonneg hB hb]
  unfold gQ
  calc |(3 * B - 2 * gS B b) * ga A B b ^ 2 +
          (4 * B * gS B b - B ^ 2 - 2 * gS B b ^ 2) * ga A B b * a -
          2 * gS B b * gc B b * a ^ 2|
      ≤ |(3 * B - 2 * gS B b) * ga A B b ^ 2| +
          |(4 * B * gS B b - B ^ 2 - 2 * gS B b ^ 2) * ga A B b * a| +
          |2 * gS B b * gc B b * a ^ 2| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ 2 * gS B b * ga A B b ^ 2 + 2 * gS B b ^ 2 * |ga A B b| * |a| +
          2 * gS B b * gc B b * a ^ 2 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (ga A B b)),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * gS B b * gc B b * a ^ 2)]
        gcongr

/-- **The pointwise bound** `|ladderG| ≤ (18/v₀⁴ + 10/v₀³)/U³` on the simplex. -/
theorem abs_ladderG_core_le {A B a b V v₀ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (h1 : A + B + a + b = 1) (hU : 0 < gU A B a b) (hv₀ : 0 < v₀) (hV : v₀ ≤ V) :
    |3 * a * gQ A B a b / (gU A B a b ^ 5 * V ^ 4) +
        a * (9 * gc B b + ga A B b) / (gU A B a b ^ 4 * V ^ 3)| ≤
      (18 / v₀ ^ 4 + 10 / v₀ ^ 3) / gU A B a b ^ 3 := by
  set U := gU A B a b with hU_def
  have hs : 0 ≤ gS B b := by unfold gS; linarith
  have hc : 0 ≤ gc B b := by unfold gc; positivity
  have ha' : 0 ≤ ga A B b := by unfold ga; positivity
  have hsa : gS B b * a ≤ U := by rw [hU_def]; unfold gU; linarith
  have ha'U : ga A B b ≤ U := by
    rw [hU_def]; unfold gU; nlinarith [mul_nonneg hs ha]
  have hcU : gc B b ≤ U := by
    refine le_trans ?_ ha'U; unfold ga; nlinarith [mul_nonneg hs hA]
  have hU1 : U ≤ 1 := by
    have : U ≤ (A + B + a + b) ^ 2 := by
      rw [hU_def]; unfold gU ga gS gc
      nlinarith [mul_nonneg hA ha, mul_nonneg hB hb, sq_nonneg (A + a), sq_nonneg B, sq_nonneg b,
        mul_nonneg hA hB, mul_nonneg hA hb, mul_nonneg ha hB, mul_nonneg ha hb]
    calc U ≤ (A + B + a + b) ^ 2 := this
      _ = 1 := by simp [h1]
  have ha1 : a ≤ 1 := by linarith
  have hV0 : 0 < V := hv₀.trans_le hV
  -- the numerator of the first term
  have haQ : |a * gQ A B a b| ≤ 6 * U ^ 2 := by
    have hQ := abs_gQ_le (A := A) (a := a) hB hb
    rw [abs_of_nonneg ha', abs_of_nonneg ha] at hQ
    have t1 : (gS B b * a) * ga A B b ^ 2 ≤ U * U ^ 2 :=
      mul_le_mul hsa (pow_le_pow_left₀ ha' ha'U 2) (sq_nonneg _) hU.le
    have t2 : (gS B b * a) ^ 2 * ga A B b ≤ U ^ 2 * U :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hsa 2) ha'U ha' (sq_nonneg _)
    have t3 : (gS B b * a) * gc B b * a ^ 2 ≤ U * U * 1 :=
      mul_le_mul (mul_le_mul hsa hcU hc hU.le) (by nlinarith) (sq_nonneg _) (by positivity)
    have hU3 : U * U ^ 2 ≤ U ^ 2 := by nlinarith [sq_nonneg U]
    rw [abs_mul, abs_of_nonneg ha]
    calc a * |gQ A B a b| ≤ a * (2 * gS B b * ga A B b ^ 2 + 2 * gS B b ^ 2 * ga A B b * a +
          2 * gS B b * gc B b * a ^ 2) := mul_le_mul_of_nonneg_left hQ ha
      _ = 2 * ((gS B b * a) * ga A B b ^ 2) + 2 * ((gS B b * a) ^ 2 * ga A B b) +
          2 * ((gS B b * a) * gc B b * a ^ 2) := by ring
      _ ≤ 6 * U ^ 2 := by nlinarith
  have hnum2 : a * (9 * gc B b + ga A B b) ≤ 10 * U := by
    have : 9 * gc B b + ga A B b ≤ 10 * U := by linarith
    calc a * (9 * gc B b + ga A B b) ≤ 1 * (10 * U) :=
          mul_le_mul ha1 this (by positivity) zero_le_one
      _ = 10 * U := one_mul _
  have e1 : |3 * a * gQ A B a b / (U ^ 5 * V ^ 4)| ≤ 18 / v₀ ^ 4 / U ^ 3 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < U ^ 5 * V ^ 4), mul_assoc, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc 3 * |a * gQ A B a b| / (U ^ 5 * V ^ 4) ≤ 3 * (6 * U ^ 2) / (U ^ 5 * v₀ ^ 4) := by
          refine div_le_div₀ (by positivity) (by linarith) (by positivity) ?_
          gcongr
      _ = 18 / v₀ ^ 4 / U ^ 3 := by field_simp; ring
  have e2 : |a * (9 * gc B b + ga A B b) / (U ^ 4 * V ^ 3)| ≤ 10 / v₀ ^ 3 / U ^ 3 := by
    rw [abs_of_nonneg (by positivity)]
    calc a * (9 * gc B b + ga A B b) / (U ^ 4 * V ^ 3) ≤ 10 * U / (U ^ 4 * v₀ ^ 3) := by
          refine div_le_div₀ (by positivity) hnum2 (by positivity) ?_
          gcongr
      _ = 10 / v₀ ^ 3 / U ^ 3 := by field_simp
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 18 / v₀ ^ 4 / U ^ 3 + 10 / v₀ ^ 3 / U ^ 3 := add_le_add e1 e2
    _ = (18 / v₀ ^ 4 + 10 / v₀ ^ 3) / U ^ 3 := by ring

/-! ### The product of the coordinates -/

theorem prod_le_lU_pow_four {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ lU z ^ 4 := by
  have h03 : z 0 * z 3 ≤ lzA z ^ 2 := by unfold lzA; nlinarith [hz 0, hz 3]
  have h12 : z 1 * z 2 ≤ lzB z ^ 2 := by unfold lzB; nlinarith [hz 1, hz 2]
  have h46 : z 4 * z 6 ≤ lza z ^ 2 := by unfold lza; nlinarith [hz 4, hz 6]
  have h57 : z 5 * z 7 ≤ lzb z ^ 2 := by unfold lzb; nlinarith [hz 5, hz 7]
  have hA : 0 ≤ lzA z := by unfold lzA; linarith [hz 0, hz 3]
  have hB : 0 ≤ lzB z := by unfold lzB; linarith [hz 1, hz 2]
  have ha : 0 ≤ lza z := by unfold lza; linarith [hz 4, hz 6]
  have hb : 0 ≤ lzb z := by unfold lzb; linarith [hz 5, hz 7]
  have hsum : lzA z * lzb z + lza z * lzB z ≤ lU z := by
    unfold lU la lc lS
    nlinarith [mul_nonneg hA hB, mul_nonneg ha hb, mul_nonneg hB hb]
  have hprod : (lzA z * lzb z) * (lza z * lzB z) ≤ lU z ^ 2 := by
    nlinarith [sq_nonneg (lzA z * lzb z - lza z * lzB z), mul_nonneg hA hb, mul_nonneg ha hB]
  rw [Fin.prod_univ_eight]
  have hp : 0 ≤ (lzA z * lzb z) * (lza z * lzB z) := by positivity
  calc z 0 * z 1 * z 2 * z 3 * z 4 * z 5 * z 6 * z 7 =
        (z 0 * z 3) * (z 1 * z 2) * (z 4 * z 6) * (z 5 * z 7) := by ring
    _ ≤ lzA z ^ 2 * lzB z ^ 2 * lza z ^ 2 * lzb z ^ 2 := by
        have p03 := mul_nonneg (hz 0) (hz 3)
        have p12 := mul_nonneg (hz 1) (hz 2)
        have p46 := mul_nonneg (hz 4) (hz 6)
        have p57 := mul_nonneg (hz 5) (hz 7)
        exact mul_le_mul (mul_le_mul (mul_le_mul h03 h12 p12 (sq_nonneg _)) h46 p46
          (by positivity)) h57 p57 (by positivity)
    _ = ((lzA z * lzb z) * (lza z * lzB z)) ^ 2 := by ring
    _ ≤ (lU z ^ 2) ^ 2 := pow_le_pow_left₀ hp hprod 2
    _ = lU z ^ 4 := by ring

theorem lU_pos {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i) : 0 < lU z := by
  have hs : 0 < z 1 + z 2 + (z 5 + z 7) := by linarith [hz 1, hz 2, hz 5, hz 7]
  have hA : 0 < z 0 + z 3 := by linarith [hz 0, hz 3]
  have hB : 0 < z 1 + z 2 := by linarith [hz 1, hz 2]
  have hb : 0 < z 5 + z 7 := by linarith [hz 5, hz 7]
  have ha : 0 < z 4 + z 6 := by linarith [hz 4, hz 6]
  unfold lU la lc lS lzA lzB lza lzb
  positivity

theorem inv_pow_three_le_prod_rpow {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i) :
    (lU z ^ 3)⁻¹ ≤ ∏ i, z i ^ (-(3 / 4 : ℝ)) := by
  have hz' : ∀ i, 0 ≤ z i := fun i => (hz i).le
  have hP : 0 < ∏ i, z i := Finset.prod_pos fun i _ => hz i
  have hle := prod_le_lU_pow_four hz'
  have hU : 0 < lU z := lU_pos hz
  rw [Real.finsetProd_rpow _ _ (fun i _ => hz' i)]
  calc (lU z ^ 3)⁻¹ = (lU z ^ 4) ^ (-(3 / 4 : ℝ)) := by
        rw [← Real.rpow_natCast (lU z) 4, ← Real.rpow_mul hU.le]
        norm_num
    _ ≤ (∏ i, z i) ^ (-(3 / 4 : ℝ)) := Real.rpow_le_rpow_of_nonpos hP hle (by norm_num)

/-! ### Integrability -/

theorem measurable_ladderG (P : Params) : Measurable (ladderG P) := by
  unfold ladderG ladderV gE gU gQ ga gc gS lzA lzB lza lzb
  fun_prop

theorem simplexPoint_pos_of_mem_openSimplex {m : ℕ} {x : Fin m → ℝ}
    (hx : x ∈ QED.Integration.ChengWu.openSimplex m) : ∀ i, 0 < simplexPoint x i := by
  intro i
  induction i using Fin.lastCases with
  | last => rw [simplexPoint_last]; linarith [(QED.Integration.ChengWu.mem_openSimplex.mp hx).2]
  | cast j =>
    rw [simplexPoint_castSucc]; exact (QED.Integration.ChengWu.mem_openSimplex.mp hx).1 j

theorem ae_mem_openSimplex {m : ℕ} (hm : 0 < m) :
    ∀ᵐ x ∂(volume.restrict (simplexSet m)), x ∈ QED.Integration.ChengWu.openSimplex m := by
  have h := QED.Integration.ChengWu.simplexSet_ae_eq_openSimplex (⟨0, hm⟩ : Fin m)
  filter_upwards [ae_restrict_mem (measurableSet_simplexSet m),
    ae_restrict_of_ae h] with x hx hx'
  exact (hx'.mp hx : _)

/-- The lower bound `V ≥ (3/4) min(1, m_γ²)` on the simplex. -/
theorem le_ladderV {P : Params} (hm : P.m = 1) (hΛ : P.mγ ^ 2 ≤ P.Λ ^ 2) {z : Fin 8 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : lU z ≠ 0) :
    3 / 4 * min 1 (P.mγ ^ 2) ≤ ladderV P z := by
  have h := QED.Integration.TwoLoop.symanzikV_classLPV_ge (mass := 1) (mγ := P.mγ)
    (lam₁ := P.mγ) (lam₂ := P.mγ) (lam₃ := P.Λ) (lam₄ := P.Λ)
    (p := restMomentum 1) (p' := restMomentum 1) (by rw [dot_restMomentum]) (by rw [dot_restMomentum])
    (by simp [QED.Minkowski.dot_eq]) le_rfl le_rfl hΛ hΛ hz hz1
    (by rw [← symanzikU_ladder] at hU; exact hU)
  rw [← symanzikV_ladder P hm hU]
  convert h using 2
  · norm_num
  · funext i
    rw [hm]
    rfl
  · simp [pvMasses, hm]

/-- **The ladder integrand is integrable on the simplex** (`m = 1`, `0 < m_γ ≤ Λ`). -/
theorem integrableOn_ladderG {P : Params} (hm : P.m = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ ≤ P.Λ) :
    IntegrableOn (fun x => ladderG P (simplexPoint x)) (simplexSet 7) := by
  set v₀ : ℝ := 3 / 4 * min 1 (P.mγ ^ 2)
  have hv₀ : 0 < v₀ := by positivity
  have hΛ2 : P.mγ ^ 2 ≤ P.Λ ^ 2 := pow_le_pow_left₀ hmγ.le hΛ 2
  set C : ℝ := 18 / v₀ ^ 4 + 10 / v₀ ^ 3
  have hint : IntegrableOn (fun x => C * ∏ i ∈ Finset.univ, simplexPoint x i ^ (-(3 / 4 : ℝ)))
      (simplexSet 7) :=
    (QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow Finset.univ (by norm_num)
      (by norm_num)).const_mul C
  refine hint.mono' ((measurable_ladderG P).comp
    QED.Integration.TwoLoop.continuous_simplexPoint'.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_mem_openSimplex (by norm_num : 0 < 7)] with x hx
  set z := simplexPoint x
  have hzpos := simplexPoint_pos_of_mem_openSimplex hx
  have hz1 : ∑ i, z i = 1 := by
    simp only [z, Fin.sum_univ_castSucc, simplexPoint_castSucc, simplexPoint_last]; ring
  have hU : 0 < lU z := lU_pos hzpos
  have hV := le_ladderV hm hΛ2 (fun i => (hzpos i).le) hz1 hU.ne'
  have hsum : lzA z + lzB z + lza z + lzb z = 1 := by
    rw [Fin.sum_univ_eight] at hz1; unfold lzA lzB lza lzb; linarith
  have hb := abs_ladderG_core_le (A := lzA z) (B := lzB z) (a := lza z) (b := lzb z)
    (by unfold lzA; linarith [hzpos 0, hzpos 3]) (by unfold lzB; linarith [hzpos 1, hzpos 2])
    (by unfold lza; linarith [hzpos 4, hzpos 6]) (by unfold lzb; linarith [hzpos 5, hzpos 7])
    hsum (by rw [← lU_eq]; exact hU) hv₀ hV
  rw [Real.norm_eq_abs]
  refine hb.trans ?_
  rw [← lU_eq, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_pow_three_le_prod_rpow hzpos) (by positivity)

end QED.TwoLoop.UnitLGraphReduce

end
