/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajDPCov

/-!
# (R-Π₄) step L10, two loops: the null half of `WireDRay` and the reduction to ray pieces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.UV). The
input `QED.GradedProof.RPi4.WireDRay` asks `MajDRay` of the three class densities `vDens`.

* `integrableOn_pairDensIntegrand`: the entries of the integrand of a merged piece are integrable
  at every momentum below threshold and photon mass `t ≥ 1` (from the doubled data, as in
  `QED.GradedProof.RPi4.heavyRate_vpPiece`);
* `tcov_triDens`, `tcov_blockDens`, `tcov_vDens_VA/VB/VC`: **the class densities are reflection
  covariant** in the momentum at every `u ≥ 1`;
* **`majDRayNull_vDens_VA/VB/VC`**: the null half of `MajDRay` of the three classes (covariance
  and the heavy-photon rate at `tiltVec 1 0`);
* `vNumE4_two_three`: the entry `(2, 3)` of the `m⁴` coefficient vanishes, so the padded merged
  piece vanishes at `(2, 3)` (`majDPieceP_two_three`);
* `MajDPiecesRay`: the ray half for the ten pieces with seven lines and the four with six lines;
* **`majD_wireDRay_of_rayPieces`**: `MajDPiecesRay` of the three class numerators at `(2, 3)`
  gives `WireDRay`. This replaces `QED.GradedProof.RPi4.majD_wireDRay_of_pieces`: the null vector
  and the padded piece are done.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.CountertermLimit
open QED.GradedProof.WI2 (dbl)
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex)
open QED.TwoLoop.Bridge
open QED.TwoLoop.PauliZeroExplicit (numQuartic eval_numQuartic)

/-! ### Integrability of the entries of a merged piece -/

section Piece

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])

include hflow hrow hrow4

/-- **The entries of the integrand of a merged piece are integrable** at a momentum below
threshold and a photon mass `t ≥ 1`. -/
theorem integrableOn_pairDensIntegrand {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) {k : Fin 4 → ℝ} {μ ν : Fin 4}
    (hpoly : IsLoopPoly 2 (m + 1 - 3) fun ℓ => N k ℓ μ ν)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 fun ℓ => N k ℓ μ ν)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ) (hMs : Ms (Fin.last m) = 0)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) {t : ℝ} (ht : 1 ≤ t) :
    IntegrableOn (pairDensIntegrand N (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc)) Ms (Fin.last m) t k μ ν) (simplexSet m) := by
  classical
  have hm0 : 0 < m := by omega
  set γ₀ := Fin.last m with hγ₀
  set α := castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc) with hα_def
  set cs : Fin (m + 1) → ℝ := fun l => c (sh l.castSucc) with hcs
  have hrows := castLoopMatrix_rows base hrow hrow4 fun l : Fin (m + 1) => sh l.castSucc
  have hne : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 ↔ l ≠ γ₀ := fun l => by
    rw [Ne, hsh, Ne, Fin.ext_iff]
    simp only [Fin.val_castSucc, γ₀, Fin.val_last]
    have := l.isLt
    omega
  have hr10 : (![1, 0] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 1; simp at this
  have hr01 : (![0, 1] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 0; simp at this
  have huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀ := fun l => by
    constructor
    · intro h
      by_contra hl
      rcases (hrows l).1 ((hne l).2 hl) with h' | h'
      · exact hr10 (h'.symm.trans h)
      · exact hr01 (h'.symm.trans h)
    · intro hl
      exact (hrows l).2 (not_not.1 fun h => (hne l).1 h hl)
  set c₀ := min 1 (1 + Minkowski.dot k k / (2 * m₀) ^ 2) * m₀ ^ 2 with hc₀_def
  have hT : 0 < (2 * m₀) ^ 2 := by positivity
  have hc₀ : 0 < c₀ := by
    refine mul_pos (lt_min one_pos ?_) (by positivity)
    have : -1 < Minkowski.dot k k / (2 * m₀) ^ 2 := by rw [lt_div_iff₀ hT]; linarith
    linarith
  have hferF : ∀ z : Fin (m + 1) → ℝ, ferSum α z =
      ∑ i ∈ Finset.univ.filter (fun i => sh (Fin.castSucc i) ≠ 4), z i := fun z => by
    simp only [ferSum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ne, huniq l, hne l]
  have hV : ∀ z : Fin (m + 1) → ℝ, (∀ l, 0 ≤ z l) → symanzikU α z ≠ 0 →
      c₀ * ferSum α z ≤ symanzikV α (fun i => cs i • k) Ms z := by
    intro z hz hU
    have hP0 := symanzikV_vp_ge_fermion base c y₁ y₂ hflow (fun l : Fin (m + 1) => sh l.castSucc)
      Ms hm₀ hf (k := k) hk hz hU
    rw [← hferF] at hP0
    exact hP0
  have hl : sh (Fin.last (m + 1)) = sh (Fin.last m).castSucc := by
    rw [(hsh _).2 (by simp), (hsh _).2 (by simp)]
  have hαd : castLoopMatrix (fun l => base (sh l)) = dbl γ₀ α :=
    comp_eq_dbl sh hl fun r s => (base r s : ℝ)
  have hcrit' : NoSubdivergenceRefined 2 E (dbl γ₀ α) :=
    hαd ▸ (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).2 hcrit
  set p : Fin (m + 1) → Fin 4 → ℝ := fun i => cs i • k with hp_def
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
    (lt_min hc₀ one_pos) k1 k2 k3 fun y hy hU => by
      have hz := simplexPoint_mem_stdSimplex hy
      have h1 := hV _ hz.1 hU
      rw [ferSum_eq_one_sub huniq hz.2] at h1
      have hzγ := hz.1 γ₀
      have hzγ1 : simplexPoint y γ₀ ≤ 1 := by
        rw [← hz.2]
        exact Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ γ₀)
      have e1 := mul_le_mul_of_nonneg_right (min_le_left c₀ 1) (sub_nonneg.2 hzγ1)
      have e2 := mul_le_mul_of_nonneg_right (min_le_right c₀ 1) hzγ
      have e3 := mul_le_mul_of_nonneg_left ht hzγ
      nlinarith
  have hMu : Function.update Ms γ₀ 0 = Ms := by
    rw [Function.update_eq_self_iff]; exact hMs.symm
  have hQe : Qg.eval = (numQuartic fun ℓ => N k ℓ μ ν).eval :=
    hQg.trans (eval_numQuartic ⟨Qg, hQg⟩).symm
  refine hIg.congr_fun (fun x _ => ?_) (QED.Integration.Feynman.measurableSet_simplexSet m)
  simp only [pieceF, pairDensIntegrand, hMu, paramAtV_congr hQe]
  rfl

end Piece

/-! ### Covariance of the class densities -/

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1]) {m₀ : ℝ} (hm₀ : 0 < m₀)

include hflow hrow hrow4 hm₀

/-- **The fifteen pieces of `triDens` are reflection covariant** at every `u ≥ 1`. -/
theorem tcov_triDens
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E0 E2 : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hE : ∀ m k ℓ a b, Num m k ℓ a b =
      E0 k ℓ a b + (m : ℂ) ^ 2 * E2 k ℓ a b + ((m : ℂ) ^ 2) ^ 2 * E4 k a b)
    (hP : ∀ m k a b, IsLoopPoly 2 4 fun ℓ => Num m k ℓ a b)
    (hP2 : ∀ k a b, IsLoopPoly 2 2 fun ℓ => E2 k ℓ a b)
    (hBA : ∀ m k a b i j, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun ℓ => Num m k ℓ a b)
    (hBB : ∀ m k a b i, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3} 4
      fun ℓ => Num m k ℓ a b)
    (hcov : ∀ m, TCov2 (Num m))
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) {u : ℝ} (hu : 1 ≤ u) :
    TCov (2 * m₀) fun k μ ν => triDens base c Num E4 M X Y u k μ ν := by
  have hE4 : ∀ k ℓ a b, E4 k a b =
      1 / 12 * (Num 2 k ℓ a b - 4 * Num 1 k ℓ a b + 3 * Num 0 k ℓ a b) := fun k ℓ a b => by
    rw [hE, hE, hE]; push_cast; ring
  have cov4 : TCov2 fun k (_ : Fin 2 → Fin 4 → ℝ) a b => E4 k a b := by
    have e : (fun k (ℓ : Fin 2 → Fin 4 → ℝ) a b => E4 k a b) = fun k ℓ a b =>
        1 / 12 * (Num 2 k ℓ a b - 4 * Num 1 k ℓ a b + 3 * Num 0 k ℓ a b) :=
      funext fun k => funext fun ℓ => funext fun a => funext fun b => hE4 k ℓ a b
    rw [e]
    exact (((hcov 2).sub ((hcov 1).const_mul 4)).add ((hcov 0).const_mul 3)).const_mul _
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
  -- the ten pieces with seven lines
  have PA : ∀ i j : Fin 4, TCov (2 * m₀) fun k μ ν => if i ≤ j then
      pairDens (fun ℓ => C * Num M k ℓ μ ν)
        (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
        (fun l => c (shA i j l.castSucc) • k)
        ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0]
        (Fin.last 6) u
      else 0 := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hij, ite_true]
      have hMf : ∀ l, m₀ ≤ mA M X Y i j l := fun l => by unfold mA; split_ifs <;> assumption
      refine tcov_pairDens (N := fun k ℓ μ ν => C * Num M k ℓ μ ν) ((hcov M).const_mul C)
        (fun k μ ν => IsLoopPoly.exists_loopQuartic ((hP M k μ ν).const_mul _)) _
        (fun l => c (shA i j l.castSucc)) _ _ u fun k hk μ ν => ?_
      exact integrableOn_pairDensIntegrand base c y₁ y₂ hflow hrow hrow4 (Or.inr rfl) (shA i j)
        (fun l => by fin_cases l <;> simp [shA, Fin.ext_iff] <;> omega) (hcA i j) _
        ((hP M k μ ν).const_mul _) ((hBA M k μ ν i j).const_mul _) hm₀ _ rfl
        (fun l hl => by
          fin_cases l
          exacts [hMf 0, hMf 1, hMf 2, hMf 3, hX, hY, absurd rfl hl]) hk hu
    · simp only [hij, ite_false]
      exact majDP_tcov_zero
  -- the four pieces with six lines
  have PB : ∀ i : Fin 4, TCov (2 * m₀) fun k μ ν =>
      pairDens (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν))
        (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
        (fun l => c (shB i l.castSucc) • k)
        ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] (Fin.last 5) u := by
    intro i
    have hpoly : ∀ k a b, IsLoopPoly 2 3 fun ℓ =>
        -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ a b - Num M k ℓ a b) := by
      intro k a b
      have e : (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ a b - Num M k ℓ a b)) =
          fun ℓ => (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
            (E2 k ℓ a b + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * E4 k a b) := by
        funext ℓ; rw [hE, hE]; ring
      rw [e]
      exact (((hP2 k a b).add (IsLoopPoly.const _)).const_mul _).mono (by norm_num)
    have hMf : ∀ l, m₀ ≤ mB X Y i l := fun l => by unfold mB; split_ifs <;> assumption
    refine tcov_pairDens
      (N := fun k ℓ μ ν => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν))
      (((hcov X).sub (hcov M)).const_mul _)
      (fun k μ ν => IsLoopPoly.exists_loopQuartic ((hpoly k μ ν).mono (by norm_num))) _
      (fun l => c (shB i l.castSucc)) _ _ u fun k hk μ ν => ?_
    exact integrableOn_pairDensIntegrand base c y₁ y₂ hflow hrow hrow4 (Or.inl rfl) (shB i)
      (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]; omega) (hcB i) _ (hpoly k μ ν)
      ((((hBB X k μ ν i).sub (hBB M k μ ν i)).const_mul _).mono (by decide) le_rfl) hm₀ _ rfl
      (fun l hl => by
        fin_cases l
        exacts [hMf 0, hMf 1, hMf 2, hMf 3, hY, absurd rfl hl]) hk hu
  -- the padded piece
  have PC : TCov (2 * m₀) fun k μ ν =>
      pairDens (fun ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
        (castLoopMatrix fun l : Fin 6 => base (shB 0 l.castSucc))
        (fun l => c (shB 0 l.castSucc) • k) ![Y, Y, Y, Y, Y, 0] (Fin.last 5) u := by
    have cov1 : TCov2 fun k ℓ a b => C * E4 k a b * propDenom Y 0 (fm base (ppc c k) 0 ℓ) := by
      have e : (fun k ℓ a b => C * E4 k a b * propDenom Y 0 (fm base (ppc c k) 0 ℓ)) =
          fun k ℓ a b => propDenom Y 0 (fm base (ppc c k) 0 ℓ) * (C * E4 k a b) :=
        funext fun k => funext fun ℓ => funext fun a => funext fun b => mul_comm _ _
      rw [e]
      exact (cov4.const_mul C).mul_inv fun L S S' hL k ℓ =>
        propDenom_lineMomentum_inv base c Y 0 _ L S S' hL k ℓ
    have hpoly : ∀ k a b, IsLoopPoly 2 (5 + 1 - 3) fun ℓ =>
        C * E4 k a b * propDenom Y 0 (fm base (ppc c k) 0 ℓ) := fun k a b =>
      ((IsLoopPoly.const (n := 0) _).mul
        ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y 0)).mono (by norm_num)
    refine tcov_pairDens
      (N := fun k ℓ a b => C * E4 k a b * propDenom Y 0 (fm base (ppc c k) 0 ℓ)) cov1
      (fun k μ ν => IsLoopPoly.exists_loopQuartic ((hpoly k μ ν).mono (by norm_num))) _
      (fun l => c (shB 0 l.castSucc)) _ _ u fun k hk μ ν => ?_
    exact integrableOn_pairDensIntegrand base c y₁ y₂ hflow hrow hrow4 (Or.inl rfl) (shB 0)
      (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]) (hcB 0) _ (hpoly k μ ν)
      (((rb_propDenom_pad base (ppc c k) (shB 0) 0 4 (by decide) 0 rfl rfl Y
        0).const_mul _).mono (by decide) (by norm_num)) hm₀ _ rfl
      (fun l hl => by
        fin_cases l
        exacts [hY, hY, hY, hY, hY, absurd rfl hl]) hk hu
  exact majDP_tcov_congr (majDP_tcov_add (majDP_tcov_add
    (majDP_tcov_sum Finset.univ fun i _ => majDP_tcov_sum Finset.univ fun j _ => PA i j)
    (majDP_tcov_sum Finset.univ fun i _ => PB i)) PC) fun k μ ν => by simp only [triDens, hC]

/-- **The block-summed flavour sum is reflection covariant** at every `u ≥ 1`. -/
theorem tcov_blockDens
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E0 E2 : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hE : ∀ m k ℓ a b, Num m k ℓ a b =
      E0 k ℓ a b + (m : ℂ) ^ 2 * E2 k ℓ a b + ((m : ℂ) ^ 2) ^ 2 * E4 k a b)
    (hP : ∀ m k a b, IsLoopPoly 2 4 fun ℓ => Num m k ℓ a b)
    (hP2 : ∀ k a b, IsLoopPoly 2 2 fun ℓ => E2 k ℓ a b)
    (hBA : ∀ m k a b i j, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun ℓ => Num m k ℓ a b)
    (hBB : ∀ m k a b i, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3} 4
      fun ℓ => Num m k ℓ a b)
    (hcov : ∀ m, TCov2 (Num m))
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) {u : ℝ}
    (hu : 1 ≤ u) :
    TCov (2 * m₀) fun k μ ν => blockDens base c Num E4 Φ m₀ u k μ ν := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  exact majDP_tcov_sum Finset.univ fun f _ => majDP_tcov_const_mul (tcov_triDens base c y₁ y₂
    hflow hrow hrow4 hm₀ hcA hcB Num E0 E2 E4 hE hP hP2 hBA hBB hcov (hmass f) hX (by linarith)
    hu) (Φ.coeff f : ℂ)

end Setting

/-! ### The three classes: covariance and the null half -/

theorem majDP_hS₀ {m₀ : ℝ} (hm₀ : 0 < m₀) : -(2 * m₀) ^ 2 < 0 := by nlinarith

/-- The constant segment at `tiltVec 1 0` has square `0`. -/
theorem majDP_hseg : ∀ u : ℝ, |u| ≤ 1 / 2 →
    (0 : ℝ) ≤ Minkowski.dot (lineK (tiltVec 1 0) 0 u) (lineK (tiltVec 1 0) 0 u) := by
  intro u _
  have hk : lineK (tiltVec 1 0) 0 u = tiltVec 1 0 := by simp [lineK]
  rw [hk, dot_tiltVec (by norm_num)]

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ)

include hm₀ hmass

theorem tcov_vDens_VA {u : ℝ} (hu : 1 ≤ u) :
    TCov (2 * m₀) fun k μ ν => vDens aVA baseVA cVA Φ e m₀ u k μ ν := by
  have hA := fun a b ρ σ => isOddG_aVA a b ρ σ
  exact tcov_blockDens baseVA cVA ![0, 0] ![-1, -1] flowVA (by decide) (by decide) hm₀
    critA_VA critB_VA _ _ _ _ (vNum_eq e 0 1 aVA baseVA cVA hA)
    (isLoopPoly_vNum e 0 1 aVA baseVA cVA) (isLoopPoly_vNumE2 e 0 1 aVA baseVA cVA)
    (fun m k a' b' i j => rb_vNum e 0 1 aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (tcov_vNumA e 0 1 baseVA cVA) Φ hmass hu

theorem tcov_vDens_VB {u : ℝ} (hu : 1 ≤ u) :
    TCov (2 * m₀) fun k μ ν => vDens aVB baseVB cVB Φ e m₀ u k μ ν := by
  have hA := fun a b ρ σ => isOddG_aVB a b ρ σ
  exact tcov_blockDens baseVB cVB ![0, 1] ![-1, 0] flowVB (by decide) (by decide) hm₀
    critA_VB critB_VB _ _ _ _ (vNum_eq e 0 1 aVB baseVB cVB hA)
    (isLoopPoly_vNum e 0 1 aVB baseVB cVB) (isLoopPoly_vNumE2 e 0 1 aVB baseVB cVB)
    (fun m k a' b' i j => rb_vNum e 0 1 aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (tcov_vNumB e 0 1 baseVB cVB) Φ hmass hu

theorem tcov_vDens_VC {u : ℝ} (hu : 1 ≤ u) :
    TCov (2 * m₀) fun k μ ν => vDens aVC baseVC cVC Φ e m₀ u k μ ν := by
  have hA := fun a b ρ σ => isOddG_aVC a b ρ σ
  exact tcov_blockDens baseVC cVC ![0, 1] ![-1, 0] flowVC (by decide) (by decide) hm₀
    critA_VC critB_VC _ _ _ _ (vNum_eq e 0 1 aVC baseVC cVC hA)
    (isLoopPoly_vNum e 0 1 aVC baseVC cVC) (isLoopPoly_vNumE2 e 0 1 aVC baseVC cVC)
    (fun m k a' b' i j => rb_vNum e 0 1 aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (tcov_vNumC e 0 1 baseVC cVC) Φ hmass hu

/-- **The null half of `MajDRay` for the class `VA`.** -/
theorem majDRayNull_vDens_VA :
    MajDRayNull fun u k => vDens aVA baseVA cVA Φ e m₀ u k 2 3 :=
  majDRayNull_of_tcov (T := 2 * m₀) (by positivity)
    (W := fun u k μ ν => vDens aVA baseVA cVA Φ e m₀ u k μ ν)
    (fun _ hu => tcov_vDens_VA Φ hm₀ hmass e hu)
    (heavyRate_vDens_VA Φ hm₀ hmass e (majDP_hS₀ hm₀) majDP_hseg 2 3)

/-- **The null half of `MajDRay` for the class `VB`.** -/
theorem majDRayNull_vDens_VB :
    MajDRayNull fun u k => vDens aVB baseVB cVB Φ e m₀ u k 2 3 :=
  majDRayNull_of_tcov (T := 2 * m₀) (by positivity)
    (W := fun u k μ ν => vDens aVB baseVB cVB Φ e m₀ u k μ ν)
    (fun _ hu => tcov_vDens_VB Φ hm₀ hmass e hu)
    (heavyRate_vDens_VB Φ hm₀ hmass e (majDP_hS₀ hm₀) majDP_hseg 2 3)

/-- **The null half of `MajDRay` for the class `VC`.** -/
theorem majDRayNull_vDens_VC :
    MajDRayNull fun u k => vDens aVC baseVC cVC Φ e m₀ u k 2 3 :=
  majDRayNull_of_tcov (T := 2 * m₀) (by positivity)
    (W := fun u k μ ν => vDens aVC baseVC cVC Φ e m₀ u k μ ν)
    (fun _ hu => tcov_vDens_VC Φ hm₀ hmass e hu)
    (heavyRate_vDens_VC Φ hm₀ hmass e (majDP_hS₀ hm₀) majDP_hseg 2 3)

end Classes

/-! ### The padded piece vanishes at `(2, 3)` -/

/-- `pairDens` of the zero numerator is zero. -/
theorem majDP_pairDens_zero {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (u : ℝ) :
    pairDens (fun _ => (0 : ℂ)) α p M i u = 0 := by
  set Q0 := qsum (∅ : Finset (Fin 1)) (fun _ => (0 : ℂ)) fun _ => numQuartic fun _ => (0 : ℂ)
    with hQ0
  have h0 : Q0.eval = fun _ => 0 := by
    funext ℓ
    simp [hQ0, eval_qsum]
  rw [pairDens_eq h0]
  simp [hQ0, paramAtV_qsum]

/-- **The `m⁴` coefficient of a covariant numerator has no entry `(2, 3)`**: it does not depend
on the momentum, so reflection covariance makes it a multiple of the metric. -/
theorem majDP_E4_two_three (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hcov : TCov2 fun k (_ : Fin 2 → Fin 4 → ℝ) a b => E4 k a b)
    (hconst : ∀ k, E4 k = E4 0) (k : Fin 4 → ℝ) : E4 k 2 3 = 0 := by
  have hT : TCov 1 E4 := by
    intro a ha k' _
    funext μ ν
    have h := hcov.reflect ha (QED.Dirac.reflect a k') 0 μ ν
    rw [QED.Dirac.reflect_reflect ha] at h
    exact h
  rw [hconst k]
  exact eq_zero_of_flip hT 2 rfl (by simp [Minkowski.dot_eq]) (Or.inl ⟨rfl, by decide⟩)

theorem vNumE4_cov (e : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
    (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l))
    (hcov : ∀ m, TCov2 (vNum e 0 1 A base c m)) :
    TCov2 fun k (_ : Fin 2 → Fin 4 → ℝ) a b => vNumE4 e 0 1 A k a b := by
  have hE := vNum_eq e 0 1 A base c hA
  have e' : (fun k (ℓ : Fin 2 → Fin 4 → ℝ) a b => vNumE4 e 0 1 A k a b) = fun k ℓ a b =>
      1 / 12 * (vNum e 0 1 A base c 2 k ℓ a b - 4 * vNum e 0 1 A base c 1 k ℓ a b +
        3 * vNum e 0 1 A base c 0 k ℓ a b) := by
    funext k ℓ a b
    rw [hE, hE, hE]; push_cast; ring
  rw [e']
  exact (((hcov 2).sub ((hcov 1).const_mul 4)).add ((hcov 0).const_mul 3)).const_mul _

/-- **The padded merged piece vanishes at `(2, 3)`** for an `m⁴` coefficient with no entry
`(2, 3)`. -/
theorem majDPieceP_two_three (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
    (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (h : ∀ k, E4 k 2 3 = 0) (M X Y u : ℝ)
    (k : Fin 4 → ℝ) : majDPieceP base c E4 M X Y 2 3 u k = 0 := by
  unfold majDPieceP
  simp only [h, mul_zero, zero_mul]
  exact majDP_pairDens_zero _ _ _ _ _

/-! ### The ray half from the merged pieces -/

section Ray

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
  (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (μ ν : Fin 4)

/-- **The ray half for the merged pieces with seven and with six lines**, every three-flavour
combination with masses `≥ m₀`. -/
def MajDPiecesRay (m₀ : ℝ) : Prop :=
  ∀ M X Y : ℝ, m₀ ≤ M → m₀ ≤ X → m₀ ≤ Y →
    (∀ i j : Fin 4, i ≤ j → MajDRayRay (majDPieceA base c Num M X Y μ ν i j)) ∧
      ∀ i : Fin 4, MajDRayRay (majDPieceB base c Num M X Y μ ν i)

theorem majDRayRay_triDens_of_pieces {M X Y : ℝ}
    (hA : ∀ i j : Fin 4, i ≤ j → MajDRayRay (majDPieceA base c Num M X Y μ ν i j))
    (hB : ∀ i : Fin 4, MajDRayRay (majDPieceB base c Num M X Y μ ν i))
    (hP : MajDRayRay (majDPieceP base c E4 M X Y μ ν)) :
    MajDRayRay fun u k => triDens base c Num E4 M X Y u k μ ν := by
  have hA' : ∀ i j : Fin 4, MajDRayRay fun u k =>
      if i ≤ j then majDPieceA base c Num M X Y μ ν i j u k else 0 := fun i j => by
    by_cases hij : i ≤ j
    · simpa only [hij, ite_true] using hA i j hij
    · simpa only [hij, ite_false] using (MajDRayRay.zero : MajDRayRay fun _ _ => 0)
  exact ((MajDRayRay.sum Finset.univ fun i _ => MajDRayRay.sum Finset.univ fun j _ =>
    hA' i j).add (MajDRayRay.sum Finset.univ fun i _ => hB i)).add hP

theorem majDRayRay_blockDens_of_pieces {m₀ : ℝ} (hm₀ : 0 < m₀)
    (h : MajDPiecesRay base c Num μ ν m₀)
    (hP : ∀ M X Y, MajDRayRay (majDPieceP base c E4 M X Y μ ν))
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    MajDRayRay fun u k => blockDens base c Num E4 Φ m₀ u k μ ν := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  refine MajDRayRay.sum Finset.univ fun f _ => MajDRayRay.const_mul ?_ (Φ.coeff f : ℂ)
  obtain ⟨hA, hB⟩ := h (Φ.mass f) (blockX Φ m₀) (blockX Φ m₀ + 1) (hmass f) hX (by linarith)
  exact majDRayRay_triDens_of_pieces base c Num E4 μ ν hA hB (hP _ _ _)

end Ray

/-- **The ray half of a class density from its merged pieces** (entry `(2, 3)`, the padded piece
vanishing there). -/
theorem majDRayRay_vDens_of_pieces
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (e : ℝ)
    (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l))
    (hcov : ∀ m, TCov2 (vNum e 0 1 A base c m)) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (h : MajDPiecesRay base c (vNum e 0 1 A base c) 2 3 m₀)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    MajDRayRay fun u k => vDens A base c Φ e m₀ u k 2 3 := by
  have h4 : ∀ k, vNumE4 e 0 1 A k 2 3 = 0 :=
    majDP_E4_two_three _ (vNumE4_cov e A base c hA hcov) fun _ => rfl
  refine majDRayRay_blockDens_of_pieces base c _ (vNumE4 e 0 1 A) 2 3 hm₀ h
    (fun M X Y => (MajDRayRay.zero).congr fun s _ u _ => ?_) Φ hmass
  rw [majDPieceP_two_three base c _ h4]

/-- **`WireDRay` from the ray half of the merged pieces of the three classes.** The null half
and the padded pieces are proved here. -/
theorem majD_wireDRay_of_rayPieces (e : ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hA : MajDPiecesRay baseVA cVA (vNum e 0 1 aVA baseVA cVA) 2 3 m₀)
    (hB : MajDPiecesRay baseVB cVB (vNum e 0 1 aVB baseVB cVB) 2 3 m₀)
    (hC : MajDPiecesRay baseVC cVC (vNum e 0 1 aVC baseVC cVC) 2 3 m₀)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    WireDRay Φ e m₀ :=
  ⟨majDRay_of_halves (majDRayRay_vDens_of_pieces _ _ _ e (isOddG_aVA · · · ·)
      (tcov_vNumA e 0 1 baseVA cVA) hm₀ hA Φ hmass) (majDRayNull_vDens_VA Φ hm₀ hmass e),
    majDRay_of_halves (majDRayRay_vDens_of_pieces _ _ _ e (isOddG_aVB · · · ·)
      (tcov_vNumB e 0 1 baseVB cVB) hm₀ hB Φ hmass) (majDRayNull_vDens_VB Φ hm₀ hmass e),
    majDRay_of_halves (majDRayRay_vDens_of_pieces _ _ _ e (isOddG_aVC · · · ·)
      (tcov_vNumC e 0 1 baseVC cVC) hm₀ hC Φ hmass) (majDRayNull_vDens_VC Φ hm₀ hmass e)⟩

end QED.GradedProof.RPi4

end
