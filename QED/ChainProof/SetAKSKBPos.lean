/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBPiece
public import QED.GradedProof.RPi4MajDPNull

/-!
# Set (a), stage B2: positivity and integrability at every photon mass

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B2. Below threshold
and with fermion masses at least `m₀ > 0`, `V ≥ c₀ (1 - z_γ)` on the simplex
(`QED.GradedProof.RPi4.symanzikV_vp_ge_fermion`), so `V + z_γ t ≥ min(c₀, t) > 0` for every
`t > 0`:

* `ksB_V_lower`: the lower bound;
* **`ksB_integrableOn_pieceF`**: the merged pieces are integrable for every `t > 0` (the version
  `QED.GradedProof.RPi4.integrableOn_pairDensIntegrand` has `t ≥ 1`);
* `ksB_pos5`, `ksB_pos6`: the hypotheses `KsBPos`, `KsBPos6` of the piece merges;
* `ksB_update_ge`, `ksB_sq_ne`: the mass conditions.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.GradedProof.RPi4 QED.GradedProof.VP2
open QED.GradedProof.SE2 QED.TwoLoop.Bridge
open QED.GradedProof.WI2 (dbl)
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex)
open QED.TwoLoop.PauliZeroExplicit (numQuartic eval_numQuartic)

section Pos

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)

include hflow

/-- The lower bound of `V` on the fermion lines below threshold. -/
noncomputable def ksBc₀ (m₀ : ℝ) (k : Fin 4 → ℝ) : ℝ :=
  min 1 (1 + Minkowski.dot k k / (2 * m₀) ^ 2) * m₀ ^ 2

omit hflow in
theorem ksBc₀_pos {m₀ : ℝ} (hm₀ : 0 < m₀) {k : Fin 4 → ℝ}
    (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) : 0 < ksBc₀ m₀ k := by
  have hT : 0 < (2 * m₀) ^ 2 := by positivity
  refine mul_pos (lt_min one_pos ?_) (by positivity)
  have : -1 < Minkowski.dot k k / (2 * m₀) ^ 2 := by rw [lt_div_iff₀ hT]; linarith
  linarith

/-- **`V + z_γ t ≥ min(c₀, t)` on the simplex**, for data whose only photon line is `γ`, fermion
masses at least `m₀` and a momentum below threshold. -/
theorem ksB_V_lower {n : ℕ} (r : Fin (n + 1) → Fin 5) (γ : Fin (n + 1))
    (hr : ∀ l, r l = 4 ↔ l = γ) (Ms : Fin (n + 1) → ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hf : ∀ l, r l ≠ 4 → m₀ ≤ Ms l) {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k)
    (t : ℝ) {z : Fin (n + 1) → ℝ} (hz0 : ∀ l, 0 ≤ z l) (hz1 : ∑ l, z l = 1)
    (hU : symanzikU (castLoopMatrix fun l => base (r l)) z ≠ 0) :
    min (ksBc₀ m₀ k) t ≤
      symanzikV (castLoopMatrix fun l => base (r l)) (fun l => c (r l) • k) Ms z + z γ * t := by
  have P := symanzikV_vp_ge_fermion base c y₁ y₂ hflow r Ms hm₀ hf hk hz0 hU
  have hsum : ∑ l ∈ Finset.univ.filter (fun l => r l ≠ 4), z l = 1 - z γ := by
    rw [Finset.sum_filter]
    have e : ∀ l, (if r l ≠ 4 then z l else 0) = z l - if γ = l then z l else 0 := fun l => by
      by_cases h : l = γ
      · subst h; simp [(hr l).2 rfl]
      · have h' : r l ≠ 4 := fun h4 => h ((hr l).1 h4)
        simp [h', Ne.symm h]
    simp only [e, Finset.sum_sub_distrib, hz1, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hsum] at P
  have hzγ := hz0 γ
  have hzγ1 : z γ ≤ 1 := by
    rw [← hz1]
    exact Finset.single_le_sum (fun j _ => hz0 j) (Finset.mem_univ γ)
  change ksBc₀ m₀ k * (1 - z γ) ≤ _ at P
  have e1 := mul_le_mul_of_nonneg_right (min_le_left (ksBc₀ m₀ k) t) (sub_nonneg.2 hzγ1)
  have e2 := mul_le_mul_of_nonneg_right (min_le_right (ksBc₀ m₀ k) t) hzγ
  nlinarith

/-- **The merged pieces are integrable at every photon mass `t > 0`**, with any quartic `Q`
representing the numerator (`QED.GradedProof.RPi4.integrableOn_pairDensIntegrand` has `t ≥ 1`). -/
theorem ksB_integrableOn_pieceF {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (F : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (m + 1 - 3) F)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 F) (Q : LoopQuartic)
    (hQ : Q.eval = F) {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l) {k : Fin 4 → ℝ}
    (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => pieceF (m + 1) Q
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t (simplexPoint x)) (simplexSet m) := by
  classical
  have hm0 : 0 < m := by omega
  set γ₀ := Fin.last m with hγ₀
  set α := castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc) with hα_def
  set p : Fin (m + 1) → Fin 4 → ℝ := fun i => c (sh i.castSucc) • k with hp_def
  have hr : ∀ l : Fin (m + 1), sh l.castSucc = 4 ↔ l = γ₀ := fun l => by
    rw [hsh, Fin.ext_iff]
    simp only [Fin.val_castSucc, γ₀, Fin.val_last]
    have := l.isLt
    omega
  have hl : sh (Fin.last (m + 1)) = sh (Fin.last m).castSucc := by
    rw [(hsh _).2 (by simp), (hsh _).2 (by simp)]
  have hαd : castLoopMatrix (fun l => base (sh l)) = dbl γ₀ α :=
    comp_eq_dbl sh hl fun r s => (base r s : ℝ)
  have hcrit' : NoSubdivergenceRefined 2 E (dbl γ₀ α) :=
    hαd ▸ (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).2 hcrit
  obtain ⟨Qg, hq, hBQ, hQg⟩ := good_of_poly (n := m + 1) (by omega) hpoly (hαd ▸ hB)
  have hcoef : IntegrableOn (coeffOne Qg (dbl γ₀ α) (dbl γ₀ p)) (simplexSet (m + 1)) ∧
      IntegrableOn (coeffTwo Qg (dbl γ₀ α) (dbl γ₀ p)) (simplexSet (m + 1)) ∧
      IntegrableOn (coeffThree Qg (dbl γ₀ α)) (simplexSet (m + 1)) := by
    rcases hq with h7 | hq0
    · exact integrableOn_coeff Qg (dbl γ₀ α) (dbl γ₀ p) h7 hcrit' hBQ
    · exact integrableOn_coeff_cubic Qg (dbl γ₀ α) (dbl γ₀ p) hq0 (by omega) hcrit' hBQ
  have k1 := integrableOn_mul_of_dbl hm0 γ₀ (f := cOneAt (m + 1) Qg (dbl γ₀ α) (dbl γ₀ p))
    (g := cOneAt (m + 1) Qg α p) (cOneAt_dbl _ Qg α p · γ₀) hcoef.1
  have k2 := integrableOn_mul_of_dbl hm0 γ₀ (f := cTwoAt (m + 1) Qg (dbl γ₀ α) (dbl γ₀ p))
    (g := cTwoAt (m + 1) Qg α p) (cTwoAt_dbl _ Qg α p · γ₀) hcoef.2.1
  have k3 := integrableOn_mul_of_dbl hm0 γ₀ (f := cThreeAt (m + 1) Qg (dbl γ₀ α))
    (g := cThreeAt (m + 1) Qg α) (cThreeAt_dbl _ Qg α · γ₀) hcoef.2.2
  have hIg := integrableOn_pieceF (n := m + 1) (Q := Qg) (pp := p) (M := Ms) (u := t)
    (lt_min (ksBc₀_pos hm₀ hk) ht) k1 k2 k3 fun y hy hU => by
      have hz := simplexPoint_mem_stdSimplex hy
      exact ksB_V_lower base c y₁ y₂ hflow (fun l => sh l.castSucc) γ₀ hr Ms hm₀ hf hk t hz.1
        hz.2 hU
  refine hIg.congr_fun (fun x _ => ?_) (QED.Integration.Feynman.measurableSet_simplexSet m)
  simp only [pieceF, paramAtV_congr (hQg.trans hQ.symm)]

/-- **`V > 0` on `Δ₄`** for fermion masses at least `m₀` (`u > 0`). -/
theorem ksB_pos5 {m₀ : ℝ} (hm₀ : 0 < m₀) {k : Fin 4 → ℝ}
    (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) {u : ℝ} (hu : 0 < u) {mf : Fin 4 → ℝ}
    (hmf : ∀ l, m₀ ≤ mf l) : KsBPos base c k u mf := by
  intro y hy hU
  have hz := simplexPoint_mem_stdSimplex hy
  have h := ksB_V_lower base c y₁ y₂ hflow (fun l : Fin 5 => l) (Fin.last 4)
    (fun l => by fin_cases l <;> decide) (ksBM5 mf) hm₀
    (fun l hl => by fin_cases l <;> first | exact hmf _ | exact absurd rfl hl) hk u hz.1 hz.2 hU
  exact lt_of_lt_of_le (lt_min (ksBc₀_pos hm₀ hk) hu) h

/-- **`V > 0` on `Δ₅`** for the six-line data of `shB i`. -/
theorem ksB_pos6 {m₀ : ℝ} (hm₀ : 0 < m₀) {k : Fin 4 → ℝ}
    (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) {u : ℝ} (hu : 0 < u) (i : Fin 4)
    {mf : Fin 4 → ℝ} (hmf : ∀ l, m₀ ≤ mf l) {X : ℝ} (hX : m₀ ≤ X) :
    KsBPos6 base c k u i mf X := by
  intro y hy hU
  have hz := simplexPoint_mem_stdSimplex hy
  have h := ksB_V_lower base c y₁ y₂ hflow (fun l : Fin 6 => shB i l.castSucc) (Fin.last 5)
    (fun l => by fin_cases i <;> fin_cases l <;> decide) (ksBM6 mf X) hm₀
    (fun l hl => by
      fin_cases l <;> first | exact hmf _ | exact hX | exact absurd (by fin_cases i <;> rfl) hl)
    hk u hz.1 hz.2 hU
  exact lt_of_lt_of_le (lt_min (ksBc₀_pos hm₀ hk) hu) h

end Pos

theorem ksB_update_ge {m₀ : ℝ} {mf : Fin 4 → ℝ} (hmf : ∀ l, m₀ ≤ mf l) (i : Fin 4) {b : ℝ}
    (hb : m₀ ≤ b) : ∀ l, m₀ ≤ Function.update mf i b l := fun l => by
  rw [Function.update_apply]; split_ifs
  · exact hb
  · exact hmf l

/-- The three masses are distinct in square. -/
theorem ksB_sq_ne {a b : ℝ} (ha : 0 < a) (hab : a < b) : a ^ 2 ≠ b ^ 2 := by
  nlinarith

end QED.ChainProof.SetAKS

end
