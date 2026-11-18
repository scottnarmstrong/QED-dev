/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCReduceSV
public import QED.TwoLoop.UnitLGraphReduceBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integrability of the `S₊` integrand on the simplex

The real integrand `selfG` of the class `S₊` (`QED/TwoLoop/UnitSCReduceSV.lean`) is integrable on
the simplex `Δ₇` (`integrableOn_selfG`), for `0 < m_γ ≤ Λ` and `m = 1`.

The bound. On the simplex, with `s = Y + z_b`, `a ≤ U`, `z_a s ≤ U`, `z_a z_b ≤ U`, `Y, z_b ≤ s`,
so `|N₁| ≤ 9 s U³` and `|N₂| ≤ 10 s U²`, and `V ≥ v₀ = (3/4) min(1, m_γ²)`
(`QED.Integration.TwoLoop.symanzikV_classSpPV_ge`): `|selfG| ≤ C s/U³` (`abs_selfGz_le`).
Unlike the ladder's `C/U³` this keeps the factor `s`, which vanishes on the face of the inner
(ultraviolet-divergent) self-energy subgraph. Moreover `∏ₖ zₖ ≤ z_o³ Y z_a² z_b²` and
`(z_o³ Y z_a² z_b²)³ s⁴ ≤ (z_o s)⁴ (z_o Y)³ (z_a z_b)⁵ ≤ U¹²`, so
`s/U³ ≤ ∏ₖ zₖ^{-3/4}` (`self_div_pow_three_le_prod_rpow`), which is integrable on the simplex
(`QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow`).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.TwoLoop.UnitSCReduce

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitSCGraph
open QED.TwoLoop.UnitLGraphReduce QED.TwoLoop.Bridge
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.TwoLoop (castLoopMatrix class5LoopMatrixPV symanzikV symanzikU
  simplexPoint_castSucc simplexPoint_last)

/-! ### The pointwise bound -/

/-- **The pointwise bound** `|selfGz| ≤ (9/v₀⁴ + 10/v₀³) s/U³` on the simplex. -/
theorem abs_selfGz_le {A B a b V v₀ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : A + B + a + b = 1) (hU : 0 < gU A B a b) (hv₀ : 0 < v₀) (hV : v₀ ≤ V) :
    |selfGz A B a b V| ≤ (9 / v₀ ^ 4 + 10 / v₀ ^ 3) * (gS B b / gU A B a b ^ 3) := by
  set U := gU A B a b with hU_def
  set s := gS B b with hs_def
  have hs : 0 ≤ s := by rw [hs_def]; unfold gS; linarith
  have hc : 0 ≤ gc B b := by unfold gc; positivity
  have ha' : 0 ≤ ga A B b := by unfold ga; positivity
  have hsa : s * a ≤ U := by rw [hU_def, hs_def]; unfold gU; linarith
  have ha'U : ga A B b ≤ U := by
    rw [hU_def]; unfold gU; nlinarith [mul_nonneg hs ha]
  have hab : a * b ≤ U := by
    have : a * b ≤ s * a := by rw [hs_def]; unfold gS; nlinarith [mul_nonneg ha hB]
    linarith
  have ha1 : a ≤ 1 := by linarith
  have hBs : B ≤ s := by rw [hs_def]; unfold gS; linarith
  have hbs : b ≤ s := by rw [hs_def]; unfold gS; linarith
  have hVpos : 0 < V := lt_of_lt_of_le hv₀ hV
  have hn1 : |selfN1 A B a b| ≤ 9 * (s * U ^ 3) := by
    unfold selfN1
    rw [abs_neg, ← hs_def, ← hU_def]
    rw [abs_of_nonneg (by positivity)]
    have h2 : 2 * U + a * b ≤ 3 * U := by linarith
    have h3 : ga A B b ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ ha' ha'U 2
    calc 3 * a * s * ga A B b ^ 2 * (2 * U + a * b)
        ≤ 3 * 1 * s * U ^ 2 * (3 * U) := by gcongr
      _ = 9 * (s * U ^ 3) := by ring
  have hn2 : |selfN2 A B a b| ≤ 10 * (s * U ^ 2) := by
    unfold selfN2
    rw [← hs_def, ← hU_def]
    rw [abs_of_nonneg (by positivity)]
    have e : 2 * a * s * (3 * B * U + 2 * s * a * b) =
        6 * (s * a) * B * U + 4 * (s * a) ^ 2 * b := by ring
    rw [e]
    have t1 : 6 * (s * a) * B * U ≤ 6 * U * s * U := by gcongr
    have t2 : 4 * (s * a) ^ 2 * b ≤ 4 * U ^ 2 * s := by gcongr
    nlinarith
  have e1 : |selfN1 A B a b / (U ^ 6 * V ^ 4)| ≤ 9 / v₀ ^ 4 * (s / U ^ 3) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < U ^ 6 * V ^ 4)]
    calc |selfN1 A B a b| / (U ^ 6 * V ^ 4) ≤ 9 * (s * U ^ 3) / (U ^ 6 * v₀ ^ 4) := by
          refine div_le_div₀ (by positivity) hn1 (by positivity) ?_
          gcongr
      _ = 9 / v₀ ^ 4 * (s / U ^ 3) := by field_simp
  have e2 : |selfN2 A B a b / (U ^ 5 * V ^ 3)| ≤ 10 / v₀ ^ 3 * (s / U ^ 3) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < U ^ 5 * V ^ 3)]
    calc |selfN2 A B a b| / (U ^ 5 * V ^ 3) ≤ 10 * (s * U ^ 2) / (U ^ 5 * v₀ ^ 3) := by
          refine div_le_div₀ (by positivity) hn2 (by positivity) ?_
          gcongr
      _ = 10 / v₀ ^ 3 * (s / U ^ 3) := by field_simp
  unfold selfGz
  rw [← hU_def]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 9 / v₀ ^ 4 * (s / U ^ 3) + 10 / v₀ ^ 3 * (s / U ^ 3) := add_le_add e1 e2
    _ = (9 / v₀ ^ 4 + 10 / v₀ ^ 3) * (s / U ^ 3) := by ring

/-! ### The product of the coordinates -/

theorem spU_eq_gU (z : Fin 8 → ℝ) : spU z = gU (spzo z) (spY z) (spza z) (spzb z) := rfl

theorem spU_pos {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i) : 0 < spU z := by
  have := hz 0; have := hz 1; have := hz 2; have := hz 3
  have := hz 4; have := hz 5; have := hz 6; have := hz 7
  unfold spU spa spc spS spzo spY spza spzb
  positivity

/-- `(∏ₖ zₖ)³ s⁴ ≤ U¹²` on the simplex. -/
theorem prod_pow_three_mul_le {z : Fin 8 → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) :
    (∏ i, z i) ^ 3 * spS z ^ 4 ≤ spU z ^ 12 := by
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
  have h4 := hz 4; have h5 := hz 5; have h6 := hz 6; have h7 := hz 7
  rw [Fin.sum_univ_eight] at hz1
  have ho : 0 ≤ spzo z := by unfold spzo; linarith
  have hY : 0 ≤ spY z := h2
  have ha : 0 ≤ spza z := by unfold spza; linarith
  have hb : 0 ≤ spzb z := by unfold spzb; linarith
  have hs : 0 ≤ spS z := by unfold spS; linarith
  have ho1 : spzo z ≤ 1 := by unfold spzo; linarith
  have ha1 : spza z ≤ 1 := by unfold spza; linarith
  have hb1 : spzb z ≤ 1 := by unfold spzb; linarith
  -- the product of the coordinates by the group sums
  have hp3 : z 0 * z 1 * z 3 ≤ spzo z ^ 3 := by
    have e1 : z 0 ≤ spzo z := by unfold spzo; linarith
    have e2 : z 1 ≤ spzo z := by unfold spzo; linarith
    have e3 : z 3 ≤ spzo z := by unfold spzo; linarith
    calc z 0 * z 1 * z 3 ≤ spzo z * spzo z * spzo z := by gcongr
      _ = spzo z ^ 3 := by ring
  have hp46 : z 4 * z 6 ≤ spza z ^ 2 := by unfold spza; nlinarith
  have hp57 : z 5 * z 7 ≤ spzb z ^ 2 := by unfold spzb; nlinarith
  have hprod : ∏ i, z i ≤ spzo z ^ 3 * spY z * spza z ^ 2 * spzb z ^ 2 := by
    rw [Fin.prod_univ_eight]
    have e : z 0 * z 1 * z 2 * z 3 * z 4 * z 5 * z 6 * z 7 =
        (z 0 * z 1 * z 3) * z 2 * (z 4 * z 6) * (z 5 * z 7) := by ring
    rw [e]
    unfold spY
    gcongr
  -- three monomials bounded by `U`
  have hU1 : spzo z * spS z ≤ spU z := by
    unfold spU spa spc; nlinarith [mul_nonneg hY hb, mul_nonneg hs ha]
  have hU2 : spzo z * spY z ≤ spU z := by
    have : spzo z * spY z ≤ spzo z * spS z := by
      unfold spS; nlinarith [mul_nonneg ho hb]
    linarith
  have hU3 : spza z * spzb z ≤ spU z := by
    have : spza z * spzb z ≤ spS z * spza z := by unfold spS; nlinarith [mul_nonneg ha hY]
    unfold spU spa spc at *
    nlinarith [mul_nonneg hY hb, mul_nonneg hs ho]
  have hP0 : 0 ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => hz i
  have hmono : spzo z ^ 9 * spY z ^ 3 * spza z ^ 6 * spzb z ^ 6 ≤
      spzo z ^ 7 * spY z ^ 3 * spza z ^ 5 * spzb z ^ 5 := by
    have q1 : spzo z ^ 9 ≤ spzo z ^ 7 := pow_le_pow_of_le_one ho ho1 (by norm_num)
    have q2 : spza z ^ 6 ≤ spza z ^ 5 := pow_le_pow_of_le_one ha ha1 (by norm_num)
    have q3 : spzb z ^ 6 ≤ spzb z ^ 5 := pow_le_pow_of_le_one hb hb1 (by norm_num)
    gcongr
  calc (∏ i, z i) ^ 3 * spS z ^ 4
      ≤ (spzo z ^ 3 * spY z * spza z ^ 2 * spzb z ^ 2) ^ 3 * spS z ^ 4 := by gcongr
    _ = (spzo z ^ 9 * spY z ^ 3 * spza z ^ 6 * spzb z ^ 6) * spS z ^ 4 := by ring
    _ ≤ (spzo z ^ 7 * spY z ^ 3 * spza z ^ 5 * spzb z ^ 5) * spS z ^ 4 := by gcongr
    _ = (spzo z * spS z) ^ 4 * (spzo z * spY z) ^ 3 * (spza z * spzb z) ^ 5 := by ring
    _ ≤ spU z ^ 4 * spU z ^ 3 * spU z ^ 5 := by
        have := mul_nonneg ho hs; have := mul_nonneg ho hY; have := mul_nonneg ha hb
        have hU0 : 0 ≤ spU z := le_trans (mul_nonneg ho hs) hU1
        gcongr
    _ = spU z ^ 12 := by ring

/-- `s/U³ ≤ ∏ₖ zₖ^{-3/4}` on the open simplex. -/
theorem self_div_pow_three_le_prod_rpow {z : Fin 8 → ℝ} (hz : ∀ i, 0 < z i) (hz1 : ∑ i, z i = 1) :
    spS z / spU z ^ 3 ≤ ∏ i, z i ^ (-(3 / 4 : ℝ)) := by
  have hz' : ∀ i, 0 ≤ z i := fun i => (hz i).le
  have hP : 0 < ∏ i, z i := Finset.prod_pos fun i _ => hz i
  have hU : 0 < spU z := spU_pos hz
  have hs : 0 ≤ spS z := by unfold spS spY spzb; linarith [hz 2, hz 5, hz 7]
  rw [Real.finsetProd_rpow _ _ (fun i _ => hz' i)]
  set p := ∏ i, z i
  have hq : 0 < p ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hP _
  have key : spS z * p ^ (3 / 4 : ℝ) ≤ spU z ^ 3 := by
    have h4 : (spS z * p ^ (3 / 4 : ℝ)) ^ 4 ≤ (spU z ^ 3) ^ 4 := by
      have e : (p ^ (3 / 4 : ℝ)) ^ 4 = p ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hP.le]
        norm_num
      calc (spS z * p ^ (3 / 4 : ℝ)) ^ 4 = p ^ 3 * spS z ^ 4 := by rw [mul_pow, e]; ring
        _ ≤ spU z ^ 12 := prod_pow_three_mul_le hz' hz1
        _ = (spU z ^ 3) ^ 4 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h4
  rw [Real.rpow_neg hP.le, div_le_iff₀ (by positivity)]
  rw [inv_mul_eq_div, le_div_iff₀ hq]
  exact key

/-! ### Integrability -/

theorem measurable_selfG (P : Params) : Measurable (selfG P) := by
  unfold selfG selfGz selfN1 selfN2 selfV gE gU ga gc gS spzo spY spza spzb
  fun_prop

/-- The lower bound `V ≥ (3/4) min(1, m_γ²)` on the simplex (`S₊`). -/
theorem le_selfV {P : Params} (hm : P.m = 1) (hΛ : P.mγ ^ 2 ≤ P.Λ ^ 2) {z : Fin 8 → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1) (hU : spU z ≠ 0) :
    3 / 4 * min 1 (P.mγ ^ 2) ≤ selfV P (spzo z) (spY z) (spza z) (spzb z) z := by
  have h := QED.Integration.TwoLoop.symanzikV_classSpPV_ge (mass := 1) (mγ := P.mγ)
    (lam₁ := P.mγ) (lam₂ := P.mγ) (lam₃ := P.Λ) (lam₄ := P.Λ)
    (p := restMomentum 1) (p' := restMomentum 1) (by rw [dot_restMomentum])
    (by rw [dot_restMomentum]) (by simp [QED.Minkowski.dot_eq]) le_rfl le_rfl hΛ hΛ hz hz1
    (by rw [← symanzikU_Sp] at hU; exact hU)
  rw [← symanzikV_Sp P hm hU]
  convert h using 2
  · norm_num
  · funext i
    rw [hm]
    rfl
  · simp [pvMasses, hm]

/-- **The `S₊` integrand is integrable on the simplex** (`m = 1`, `0 < m_γ ≤ Λ`). -/
theorem integrableOn_selfG {P : Params} (hm : P.m = 1) (hmγ : 0 < P.mγ) (hΛ : P.mγ ≤ P.Λ) :
    IntegrableOn (fun x => selfG P (simplexPoint x)) (simplexSet 7) := by
  set v₀ : ℝ := 3 / 4 * min 1 (P.mγ ^ 2)
  have hv₀ : 0 < v₀ := by positivity
  have hΛ2 : P.mγ ^ 2 ≤ P.Λ ^ 2 := pow_le_pow_left₀ hmγ.le hΛ 2
  set C : ℝ := 9 / v₀ ^ 4 + 10 / v₀ ^ 3
  have hint : IntegrableOn (fun x => C * ∏ i ∈ Finset.univ, simplexPoint x i ^ (-(3 / 4 : ℝ)))
      (simplexSet 7) :=
    (QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow Finset.univ (by norm_num)
      (by norm_num)).const_mul C
  refine hint.mono' ((measurable_selfG P).comp
    QED.Integration.TwoLoop.continuous_simplexPoint'.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_mem_openSimplex (by norm_num : 0 < 7)] with x hx
  set z := simplexPoint x
  have hzpos := simplexPoint_pos_of_mem_openSimplex hx
  have hz1 : ∑ i, z i = 1 := by
    simp only [z, Fin.sum_univ_castSucc, simplexPoint_castSucc, simplexPoint_last]; ring
  have hU : 0 < spU z := spU_pos hzpos
  have hV := le_selfV hm hΛ2 (fun i => (hzpos i).le) hz1 hU.ne'
  have hsum : spzo z + spY z + spza z + spzb z = 1 := by
    rw [Fin.sum_univ_eight] at hz1; unfold spzo spY spza spzb; linarith
  have hb := abs_selfGz_le (A := spzo z) (B := spY z) (a := spza z) (b := spzb z)
    (by unfold spzo; linarith [hzpos 0, hzpos 1, hzpos 3]) (hzpos 2).le
    (by unfold spza; linarith [hzpos 4, hzpos 6]) (by unfold spzb; linarith [hzpos 5, hzpos 7])
    hsum (by rw [← spU_eq_gU]; exact hU) hv₀ hV
  rw [Real.norm_eq_abs]
  refine hb.trans ?_
  rw [← spU_eq_gU]
  exact mul_le_mul_of_nonneg_left (self_div_pow_three_le_prod_rpow hzpos hz1) (by positivity)

end QED.TwoLoop.UnitSCReduce

end
