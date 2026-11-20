/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecSegCont
public import QED.GradedProof.RPi4LightClass

/-!
# (R-Π₄) step L9: the two-loop classes are continuous along a segment at a fixed photon pair

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (continuity of the
per-flavour function at `s = 0`). At a fixed photon pair `0 < a ≤ b` the explicit class values
`QED.GradedProof.RPi4.vVal` (the limits `wV` of `VA`, `VB`, `VC`) are finite sums of parametric
values with `V ≥ c₀ y + (1 - y) a² ≥ min(c₀, a²) > 0` (fermion sum `y`, P0 bound
`QED.GradedProof.RPi4.symanzikV_vp_ge_fermion`), so each is continuous along a segment of
momenta below threshold (`QED.GradedProof.RPi4.dec_segCont_pvOf_line`).

* `dec_integrableOn_paramNum_of_coeff`: the parametric numerator from its three coefficients;
* `dec_segCont_vpPiece`: one piece (as `QED.GradedProof.RPi4.lightBdd_vpPiece`);
* `dec_segCont_pieceA`, `dec_segCont_pieceB`, `dec_segCont_triVal`, `dec_segCont_blockVal`;
* `dec_segCont_vVal_VA`, `dec_segCont_vVal_VB`, `dec_segCont_vVal_VC`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.CountertermLimit
open QED.TwoLoop.PauliZeroLimit
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.Bridge

/-- The parametric numerator is integrable when its three coefficients are. -/
theorem dec_integrableOn_paramNum_of_coeff {m : ℕ} (hm0 : 0 < m) (Q : LoopQuartic)
    (α : Fin (m + 1) → Fin 2 → ℝ) (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0)
    (p : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (hT₁ : IntegrableOn (coeffOne Q α p) (simplexSet m))
    (hT₂ : IntegrableOn (coeffTwo Q α p) (simplexSet m))
    (hT₃ : IntegrableOn (coeffThree Q α) (simplexSet m)) :
    IntegrableOn (paramNum Q α p M) (simplexSet m) := by
  set K := ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2)
  have hK := ae_abs_symanzikV_le α p M hm0 hspan
  have hVm : AEStronglyMeasurable (fun x => ((symanzikV α p M (simplexPoint x) : ℝ) : ℂ))
      (volume.restrict (simplexSet m)) :=
    (Complex.measurable_ofReal.comp ((measurable_symanzikV α p M).comp
      continuous_simplexPoint'.measurable)).aestronglyMeasurable
  have hb1 : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      ‖((symanzikV α p M (simplexPoint x) : ℝ) : ℂ)‖ ≤ K := by
    filter_upwards [hK] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have hb2 : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      ‖((symanzikV α p M (simplexPoint x) : ℝ) : ℂ) ^ 2‖ ≤ K ^ 2 := by
    filter_upwards [hb1] with x hx
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  exact (hT₁.add (hT₂.mul_bdd hVm hb1)).add (hT₃.mul_bdd (hVm.pow 2) hb2)

/-! ### A piece of a vacuum-polarization class at a fixed photon pair -/

/-- **A piece of a vacuum-polarization class at a fixed photon pair `0 < a ≤ b` is continuous**
along a segment of momenta below threshold (hypotheses as in `lightBdd_vpPiece`). -/
theorem dec_segCont_vpPiece (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
    (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
      |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
    (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
    (hrow4 : base 4 = ![1, -1]) {n : ℕ} (hn : n = 6 ∨ n = 7) (sh : Fin (n + 1) → Fin 5)
    (hsh : ∀ l : Fin (n + 1), sh l = 4 ↔ n - 1 ≤ (l : ℕ)) (Ms : ℝ → ℝ → Fin (n + 1) → ℝ)
    (hMs : ∀ a b l, Ms a b l ^ 2 = Ms 0 0 l ^ 2 + (if (l : ℕ) = n - 1 then a ^ 2 else 0) +
      (if (l : ℕ) = n then b ^ 2 else 0))
    {E : Finset (Fin (n + 1))} (hcrit : IntNoSubdivergenceRefined 2 E fun i => base (sh i))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 (n - 3) (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun i => base (sh i)) E 4 (N k))
    {d : ℕ} (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (hf : ∀ l, sh l ≠ 4 → m₀ ≤ Ms 0 0 l)
    {k₀ w : Fin 4 → ℝ} {S₀ : ℝ} (hS₀ : -(2 * m₀) ^ 2 < S₀)
    (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    DecSegCont k₀ w fun k => pvOf (fun ℓ => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * N k ℓ)
      (castLoopMatrix fun l => base (sh l)) (fun l => c (sh l) • k) (Ms a b) := by
  set α := castLoopMatrix fun l => base (sh l) with hα_def
  have hn6 : 6 ≤ n := by omega
  have hm0 : 0 < n := by omega
  have hcrit' : NoSubdivergenceRefined 2 E α :=
    (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    NoSubdivergence.span (α := α) fun i => by
      have := hcrit'.noSubdivergenceOfOrder i; omega
  have hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧
      ∀ q, IntegrableOn (paramNum Q α q (Ms a b)) (simplexSet n) := fun k => by
    obtain ⟨Q, hq, hb, he⟩ := good_of_poly hn (hpoly k) (hB k)
    refine ⟨Q, he, fun q => ?_⟩
    obtain ⟨h1, h2, h3⟩ : IntegrableOn (coeffOne Q α q) (simplexSet n) ∧
        IntegrableOn (coeffTwo Q α q) (simplexSet n) ∧
        IntegrableOn (coeffThree Q α) (simplexSet n) := by
      rcases hq with h7 | hq0
      · exact integrableOn_coeff Q α q h7 hcrit' hb
      · exact integrableOn_coeff_cubic Q α q hq0 hn6 hcrit' hb
    exact dec_integrableOn_paramNum_of_coeff hm0 Q α hspan q _ h1 h2 h3
  have hrows := castLoopMatrix_rows base hrow hrow4 sh
  -- the parameter sums of the fermion and photon lines
  have hsums : ∀ x ∈ simplexSet n,
      ∑ i, (if sh i = 4 then 0 else simplexPoint x i) = headSum (n - 1) x ∧
        ∑ i, (if sh i = 4 then simplexPoint x i else 0) = 1 - headSum (n - 1) x := by
    intro x hx
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx
    have h1 := sum_fermion_simplexPoint sh hsh x
    refine ⟨h1, ?_⟩
    have h2 : ∑ i, simplexPoint x i = ∑ i, (if sh i = 4 then 0 else simplexPoint x i) +
        ∑ i, (if sh i = 4 then simplexPoint x i else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
    rw [hz.2, h1] at h2
    linarith
  set c₀ := min 1 (1 + S₀ / (2 * m₀) ^ 2) * m₀ ^ 2
  have hT : 0 < (2 * m₀) ^ 2 := by positivity
  have hc₀ : 0 < c₀ := by
    refine mul_pos (lt_min one_pos ?_) (by positivity)
    have : -1 < S₀ / (2 * m₀) ^ 2 := by rw [lt_div_iff₀ hT]; linarith
    linarith
  have hV : ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ x ∈ simplexSet n,
      symanzikU α (simplexPoint x) ≠ 0 →
      c₀ * headSum (n - 1) x + (1 - headSum (n - 1) x) * a ^ 2 ≤
        symanzikV α (fun i => c (sh i) • lineK k₀ w u) (Ms a b) (simplexPoint x) := by
    intro u hu x hx hU0
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx
    set k := lineK k₀ w u
    have hs := hseg u hu
    have hP0 := symanzikV_vp_ge_fermion base c y₁ y₂ hflow sh (Ms 0 0) hm₀ hf
      (k := k) (by linarith) hz.1 hU0
    have hZ : ∑ i ∈ Finset.univ.filter (fun i => sh i ≠ 4), simplexPoint x i =
        headSum (n - 1) x := by
      rw [← (hsums x hx).1, Finset.sum_filter]
      exact Finset.sum_congr rfl fun i _ => by by_cases h4 : sh i = 4 <;> simp [h4]
    rw [hZ] at hP0
    have hy0 : 0 ≤ headSum (n - 1) x := by
      rw [← (hsums x hx).1]
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hz.1 i]
    have hmin : c₀ ≤ min 1 (1 + Minkowski.dot k k / (2 * m₀) ^ 2) * m₀ ^ 2 := by
      refine mul_le_mul_of_nonneg_right (min_le_min le_rfl ?_) (by positivity)
      have := div_le_div_of_nonneg_right hs hT.le
      linarith
    have hdiff := symanzikV_sub_mass α (fun i => c (sh i) • k) (Ms a b) (Ms 0 0) (simplexPoint x)
    have hph : (1 - headSum (n - 1) x) * a ^ 2 ≤
        ∑ i, simplexPoint x i * (Ms a b i ^ 2 - Ms 0 0 i ^ 2) := by
      rw [← (hsums x hx).2, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hMs a b i]
      have hzi := hz.1 i
      by_cases h4 : sh i = 4
      · have hi := (hsh i).mp h4
        have hin : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
        simp only [h4, ite_true]
        rcases Nat.eq_or_lt_of_le hi with h | h
        · have h1 : (i : ℕ) = n - 1 := h.symm
          have h2 : ¬ (i : ℕ) = n := by omega
          rw [ite_eq_left h1, ite_eq_right h2]
          nlinarith
        · have h1 : ¬ (i : ℕ) = n - 1 := by omega
          have h2 : (i : ℕ) = n := by omega
          rw [ite_eq_right h1, ite_eq_left h2]
          nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hab 2) hzi]
      · simp only [h4, ite_false, zero_mul]
        have h1 : 0 ≤ (if (i : ℕ) = n - 1 then a ^ 2 else 0) := by split_ifs <;> positivity
        have h2 : 0 ≤ (if (i : ℕ) = n then b ^ 2 else 0) := by split_ifs <;> positivity
        nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hmin hy0]
  have hca : 0 < min c₀ (a ^ 2) := lt_min hc₀ (by positivity)
  have hV' : ∀ᵐ x ∂(volume.restrict (simplexSet n)), ∀ u : ℝ, |u| ≤ 1 / 2 →
      min c₀ (a ^ 2) ≤
        symanzikV α (fun i => c (sh i) • lineK k₀ w u) (Ms a b) (simplexPoint x) := by
    filter_upwards [ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩ u hu
    have h := hV u hu x hxS hPD.det_pos.ne'
    have hxle := (QED.Integration.SimplexMerge.mem_simplexSet_iff_le hm0 x).mp hxS
    have hy1 : headSum (n - 1) x ≤ 1 := headSum_le_one hxle.1 hxle.2
    have hy0 : 0 ≤ headSum (n - 1) x := by
      rw [← (hsums x hxS).1]
      have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hz.1 i]
    have m1 := min_le_left c₀ (a ^ 2)
    have m2 := min_le_right c₀ (a ^ 2)
    nlinarith
  have h := dec_segCont_pvOf_line (by omega) α (fun l => c (sh l)) (Ms a b) k₀ w N hk hQ hca hV'
  refine (h.const_mul ((b ^ 2 - a ^ 2 : ℝ) : ℂ)).congr fun u _ => ?_
  obtain ⟨Q, hQe, -⟩ := hQ (lineK k₀ w u)
  exact (pvOf_const_mul hQe _ _ _ _).symm

/-! ### The pieces, the three-flavour combination and the block sum -/

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])
  {m₀ : ℝ} (hm₀ : 0 < m₀) {k₀ w : Fin 4 → ℝ} {S₀ : ℝ} (hS₀ : -(2 * m₀) ^ 2 < S₀)
  (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
  {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)

include hflow hrow hrow4 hm₀ hS₀ hseg ha hab

/-- **A piece with eight lines at a fixed photon pair.** -/
theorem dec_segCont_pieceA (i j : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (Mf : Fin 4 → ℝ) (hMf : ∀ l, m₀ ≤ Mf l) {X Y : ℝ} (hX : m₀ ≤ X) (hY : m₀ ≤ Y)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 4 (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4 (N k))
    {d : ℕ} (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) :
    DecSegCont k₀ w fun k => pvOf (fun ℓ => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * N k ℓ)
      (castLoopMatrix fun l => base (shA i j l)) (fun l => c (shA i j l) • k)
      ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, a, b] :=
  dec_segCont_vpPiece base c y₁ y₂ hflow hrow hrow4 (Or.inr rfl) (shA i j)
    (fun l => by fin_cases l <;> simp [shA, Fin.ext_iff] <;> omega)
    (fun a b => ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, a, b])
    (fun a b l => by fin_cases l <;> simp) hcrit N hpoly hB hk hm₀
    (fun l hl => by
      fin_cases l
      exacts [hMf 0, hMf 1, hMf 2, hMf 3, hX, hY, absurd rfl hl, absurd rfl hl])
    hS₀ hseg ha hab

/-- **A piece with seven lines at a fixed photon pair.** -/
theorem dec_segCont_pieceB (i : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Mf : Fin 4 → ℝ) (hMf : ∀ l, m₀ ≤ Mf l) {Y : ℝ} (hY : m₀ ≤ Y)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 3 (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3, 4} 4 (N k))
    {d : ℕ} (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) :
    DecSegCont k₀ w fun k => pvOf (fun ℓ => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * N k ℓ)
      (castLoopMatrix fun l => base (shB i l)) (fun l => c (shB i l) • k)
      ![Mf 0, Mf 1, Mf 2, Mf 3, Y, a, b] :=
  dec_segCont_vpPiece base c y₁ y₂ hflow hrow hrow4 (Or.inl rfl) (shB i)
    (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]; omega)
    (fun a b => ![Mf 0, Mf 1, Mf 2, Mf 3, Y, a, b])
    (fun a b l => by fin_cases l <;> simp) hcrit N hpoly hB hk hm₀
    (fun l hl => by
      fin_cases l
      exacts [hMf 0, hMf 1, hMf 2, hMf 3, hY, absurd rfl hl, absurd rfl hl])
    hS₀ hseg ha hab

/-- **The three-flavour combination at a fixed photon pair** (numerator with the photon factor
`b² - a²`). -/
theorem dec_segCont_triVal
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
    {d : ℕ} (hk : ∀ m ℓ a b, IsLoopPoly 1 d fun y => Num m (y 0) ℓ a b)
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (μ ν : Fin 4) :
    DecSegCont k₀ w fun k =>
      triVal base c (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν)
        (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * E4 k μ ν) a b M X Y k μ ν := by
  have hE4 : ∀ k ℓ a b, E4 k a b =
      1 / 12 * (Num 2 k ℓ a b - 4 * Num 1 k ℓ a b + 3 * Num 0 k ℓ a b) := fun k ℓ a b => by
    rw [hE, hE, hE]; push_cast; ring
  have hk4 : ∀ (ℓ : Fin 2 → Fin 4 → ℝ) a b, IsLoopPoly 1 d fun y => E4 (y 0) a b := by
    intro ℓ a b
    have e : (fun y : Fin 1 → Fin 4 → ℝ => E4 (y 0) a b) = fun y =>
        1 / 12 * (Num 2 (y 0) ℓ a b - 4 * Num 1 (y 0) ℓ a b + 3 * Num 0 (y 0) ℓ a b) :=
      funext fun y => hE4 (y 0) ℓ a b
    rw [e]
    exact (((hk 2 ℓ a b).sub ((hk 1 ℓ a b).const_mul 4)).add
      ((hk 0 ℓ a b).const_mul 3)).const_mul _
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
  -- the ten pieces with eight lines
  have PA : ∀ i j : Fin 4, DecSegCont k₀ w fun k => if i ≤ j then
      pieceVal base c (shA i j) ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2,
        mA M X Y i j 3, X, Y, a, b]
        (fun k ℓ μ ν => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν) M k ℓ μ ν) k μ ν
      else 0 := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hij, ite_true]
      refine (dec_segCont_pieceA base c y₁ y₂ hflow hrow hrow4 hm₀ hS₀ hseg ha hab i j
        (hcA i j) (mA M X Y i j) (fun l => by unfold mA; split_ifs <;> assumption) hX hY
        (fun k ℓ => C * Num M k ℓ μ ν) (fun k => (hP M k μ ν).const_mul _)
        (fun k => (hBA M k μ ν i j).const_mul _) (fun ℓ => (hk M ℓ μ ν).const_mul _)).congr
        fun u _ => ?_
      simp only [pieceVal]
      exact pvOf_congr_fun (fun ℓ => by simp only [hC]; ring) _ _ _
    · simp only [hij, ite_false]
      exact DecSegCont.zero
  -- the four pieces with seven lines
  have PB : ∀ i : Fin 4, DecSegCont k₀ w fun k =>
      pieceVal base c (shB i) ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, a, b]
        (fun k ℓ μ ν => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          ((fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν) X k ℓ μ ν -
            (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν) M k ℓ μ ν)) k μ ν := by
    intro i
    have hpoly : ∀ k, IsLoopPoly 2 3 fun ℓ =>
        -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν) := by
      intro k
      have e : (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) =
          fun ℓ => (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
            (E2 k ℓ μ ν + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * E4 k μ ν) := by
        funext ℓ; rw [hE, hE]; ring
      rw [e]
      exact (((hP2 k μ ν).add (IsLoopPoly.const _)).const_mul _).mono (by norm_num)
    refine (dec_segCont_pieceB base c y₁ y₂ hflow hrow hrow4 hm₀ hS₀ hseg ha hab i (hcB i)
      (mB X Y i) (fun l => by unfold mB; split_ifs <;> assumption) hY
      (fun k ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) hpoly
      (fun k => (((hBB X k μ ν i).sub (hBB M k μ ν i)).const_mul _).mono (by decide) le_rfl)
      (fun ℓ => ((hk X ℓ μ ν).sub (hk M ℓ μ ν)).const_mul _)).congr fun u _ => ?_
    simp only [pieceVal]
    exact pvOf_congr_fun (fun ℓ => by ring) _ _ _
  -- the padded piece
  have PC : DecSegCont k₀ w fun k =>
      pieceVal base c (shB 0) ![Y, Y, Y, Y, Y, a, b]
        (fun k ℓ μ ν => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * E4 k μ ν) k μ ν *
          propDenom Y 0 (fm base (ppc c k) 0 ℓ)) k μ ν := by
    refine (dec_segCont_pieceB base c y₁ y₂ hflow hrow hrow4 hm₀ hS₀ hseg ha hab 0 (hcB 0)
      (fun _ => Y) (fun _ => hY) hY
      (fun k ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
      (fun k => ((IsLoopPoly.const (n := 0) _).mul
        ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y 0)).mono (by norm_num))
      (fun k => ((rb_propDenom_pad base (ppc c k) (shB 0) 0 4 (by decide) 0 rfl rfl Y
        0).const_mul _).mono (by decide) (by norm_num))
      (fun ℓ => ((hk4 ℓ μ ν).const_mul C).mul
        ((isLoopAffine_lineMomentum_k base c _ ℓ).isLoopPoly_propDenom Y 0))).congr
      fun u _ => ?_
    simp only [pieceVal]
    exact pvOf_congr_fun (fun ℓ => by simp only [hC]; ring) _ _ _
  refine (((DecSegCont.sum Finset.univ fun i _ =>
    DecSegCont.sum Finset.univ fun j _ => PA i j).add
    (DecSegCont.sum Finset.univ fun i _ => PB i)).add PC).congr fun u _ => ?_
  simp only [triVal]

/-- **The block-summed flavour sum at a fixed photon pair.** -/
theorem dec_segCont_blockVal
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
    {d : ℕ} (hk : ∀ m ℓ a b, IsLoopPoly 1 d fun y => Num m (y 0) ℓ a b)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) (μ ν : Fin 4) :
    DecSegCont k₀ w fun k =>
      blockVal base c (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Num m k ℓ μ ν)
        (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * E4 k μ ν) Φ m₀ a b k μ ν := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  exact DecSegCont.sum Finset.univ fun f _ => (dec_segCont_triVal base c y₁ y₂ hflow hrow hrow4
    hm₀ hS₀ hseg ha hab hcA hcB Num E0 E2 E4 hE hP hP2 hBA hBB hk (hmass f) hX (by linarith)
    μ ν).const_mul (Φ.coeff f : ℂ)

end Setting

/-! ### The three classes -/

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) {k₀ w : Fin 4 → ℝ} {S₀ : ℝ}
  (hS₀ : -(2 * m₀) ^ 2 < S₀)
  (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u))
  {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (μ ν : Fin 4)

include hm₀ hmass hS₀ hseg ha hab

/-- **The class `VA` at a fixed photon pair is continuous along the segment.** -/
theorem dec_segCont_vVal_VA :
    DecSegCont k₀ w fun k => vVal aVA baseVA cVA Φ e m₀ a b k μ ν := by
  refine (dec_segCont_blockVal baseVA cVA ![0, 0] ![-1, -1] flowVA (by decide) (by decide) hm₀
    hS₀ hseg ha hab critA_VA critB_VA _ _ _ _
    (vNum_eq e 0 1 aVA baseVA cVA fun a b ρ σ => isOddG_aVA a b ρ σ)
    (isLoopPoly_vNum e 0 1 aVA baseVA cVA) (isLoopPoly_vNumE2 e 0 1 aVA baseVA cVA)
    (fun m k a' b' i j => rb_vNum e 0 1 aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (isLoopPoly_vNum_k e 0 1 aVA baseVA cVA) Φ hmass μ ν).congr fun u _ => ?_
  rw [vVal_eq_blockVal]

/-- **The class `VB` at a fixed photon pair is continuous along the segment.** -/
theorem dec_segCont_vVal_VB :
    DecSegCont k₀ w fun k => vVal aVB baseVB cVB Φ e m₀ a b k μ ν := by
  refine (dec_segCont_blockVal baseVB cVB ![0, 1] ![-1, 0] flowVB (by decide) (by decide) hm₀
    hS₀ hseg ha hab critA_VB critB_VB _ _ _ _
    (vNum_eq e 0 1 aVB baseVB cVB fun a b ρ σ => isOddG_aVB a b ρ σ)
    (isLoopPoly_vNum e 0 1 aVB baseVB cVB) (isLoopPoly_vNumE2 e 0 1 aVB baseVB cVB)
    (fun m k a' b' i j => rb_vNum e 0 1 aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (isLoopPoly_vNum_k e 0 1 aVB baseVB cVB) Φ hmass μ ν).congr fun u _ => ?_
  rw [vVal_eq_blockVal]

/-- **The class `VC` at a fixed photon pair is continuous along the segment.** -/
theorem dec_segCont_vVal_VC :
    DecSegCont k₀ w fun k => vVal aVC baseVC cVC Φ e m₀ a b k μ ν := by
  refine (dec_segCont_blockVal baseVC cVC ![0, 1] ![-1, 0] flowVC (by decide) (by decide) hm₀
    hS₀ hseg ha hab critA_VC critB_VC _ _ _ _
    (vNum_eq e 0 1 aVC baseVC cVC fun a b ρ σ => isOddG_aVC a b ρ σ)
    (isLoopPoly_vNum e 0 1 aVC baseVC cVC) (isLoopPoly_vNumE2 e 0 1 aVC baseVC cVC)
    (fun m k a' b' i j => rb_vNum e 0 1 aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (isLoopPoly_vNum_k e 0 1 aVC baseVC cVC) Φ hmass μ ν).congr fun u _ => ?_
  rw [vVal_eq_blockVal]

end Classes

end QED.GradedProof.RPi4

end
