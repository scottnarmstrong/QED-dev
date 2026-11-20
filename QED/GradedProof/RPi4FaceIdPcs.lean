/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4InstPiece
public import QED.GradedProof.RPi4FaceIdFace

/-!
# (R-Π₄) step L6d3: the limit of one merged piece at a fixed momentum

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. For a merged
piece of a vacuum-polarization shape (as in `heavyRate_vpPiece`, photon line last) at one momentum
`k` below threshold, `t · pairDens(t, k)` tends to `-π⁴` times the sum of its loop-`1` and loop-`0`
face limits, written with any representative `Q` of the numerator. The hypotheses the face
wrappers of `RPi4FaceIdFace` need are provided here as well:

* `faceId_vp_rows`: the rows of the merged shape (photon line unique, rows in three kinds);
* `faceId_pieceF_congr`: two representatives give the same collapsed integrand;
* `faceIdC0`, `faceId_c0_pos`, **`faceId_vp_hV`**, **`faceId_vp_hV_face`**: the lower bound
  `V₀ ≥ c₀ ferSum` (P0) and its face form `w γ₀ ≤ 1/4 ⇒ (3/4) c₀ ≤ V₀`;
* **`faceId_vp_hint`**: integrability of the collapsed integrand of any representative;
* **`faceId_vp_tendsto`**: `t · pairDens → -π⁴ (face₁ + face₀)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit
open QED.GradedProof.WI2 (dbl)
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex)
open QED.TwoLoop.Bridge (IsLoopPoly)

/-- **The P0 constant** `min(1, 1 + k²/(2m₀)²) m₀²`. -/
noncomputable def faceIdC0 (m₀ : ℝ) (k : Fin 4 → ℝ) : ℝ :=
  min 1 (1 + Minkowski.dot k k / (2 * m₀) ^ 2) * m₀ ^ 2

theorem faceId_c0_pos {m₀ : ℝ} (hm₀ : 0 < m₀) {k : Fin 4 → ℝ}
    (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) : 0 < faceIdC0 m₀ k := by
  have hT : 0 < (2 * m₀) ^ 2 := by positivity
  refine mul_pos (lt_min one_pos ?_) (by positivity)
  have : -1 < Minkowski.dot k k / (2 * m₀) ^ 2 := by rw [lt_div_iff₀ hT]; linarith
  linarith

/-- **Two representatives of one numerator give the same collapsed integrand.** -/
theorem faceId_pieceF_congr {m : ℕ} {Q Q' : LoopQuartic} (h : Q.eval = Q'.eval) (n : ℕ)
    (α : Fin (m + 1) → Fin 2 → ℝ) (pp : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ)
    (γ : Fin (m + 1)) : pieceF n Q α pp M γ = pieceF n Q' α pp M γ := by
  funext u z
  simp only [pieceF, paramAtV_congr h]

section Piece

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])

include hrow hrow4

/-- **The rows of a merged piece**: the photon line `Fin.last m` is the unique line of row
`(1, -1)`; every row is `(1, 0)`, `(0, 1)` or `(1, -1)`. -/
theorem faceId_vp_rows {m : ℕ} (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) :
    (∀ l, castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l = ![1, -1] ↔
      l = Fin.last m) ∧
    ∀ l, castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l = ![1, 0] ∨
      castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l = ![0, 1] ∨
      castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l = ![1, -1] := by
  set α := castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)
  have hrows := castLoopMatrix_rows base hrow hrow4 fun l : Fin (m + 1) => sh l.castSucc
  have hne : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 ↔ l ≠ Fin.last m := fun l => by
    rw [Ne, hsh, Ne, Fin.ext_iff]
    simp only [Fin.val_castSucc, Fin.val_last]
    have := l.isLt
    omega
  have hr10 : (![1, 0] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 1; simp at this
  have hr01 : (![0, 1] : Fin 2 → ℝ) ≠ ![1, -1] := fun h => by
    have := congrFun h 0; simp at this
  refine ⟨fun l => ⟨fun h => ?_, fun hl => ?_⟩, fun l => ?_⟩
  · by_contra hl
    rcases (hrows l).1 ((hne l).2 hl) with h' | h'
    · exact hr10 (h'.symm.trans h)
    · exact hr01 (h'.symm.trans h)
  · exact (hrows l).2 (not_not.1 fun h => (hne l).1 h hl)
  · by_cases h4 : sh l.castSucc = 4
    · exact Or.inr (Or.inr ((hrows l).2 h4))
    · rcases (hrows l).1 h4 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

variable (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)

include hflow

/-- **P0 for a merged piece at one momentum**: `V₀ ≥ c₀ · ferSum`. -/
theorem faceId_vp_hV {m : ℕ} (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (Ms : Fin (m + 1) → ℝ) (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (w : Fin (m + 1) → ℝ)
    (hw : ∀ l, 0 ≤ w l) (hU : symanzikU (castLoopMatrix fun l : Fin (m + 1) =>
      base (sh l.castSucc)) w ≠ 0) :
    faceIdC0 m₀ k * ferSum (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) w ≤
      symanzikV (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
        (fun l => c (sh l.castSucc) • k) Ms w := by
  have huniq := (faceId_vp_rows base hrow hrow4 sh hsh).1
  have hne : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 ↔ l ≠ Fin.last m := fun l => by
    rw [Ne, hsh, Ne, Fin.ext_iff]
    simp only [Fin.val_castSucc, Fin.val_last]
    have := l.isLt
    omega
  have hP0 := symanzikV_vp_ge_fermion base c y₁ y₂ hflow (fun l : Fin (m + 1) => sh l.castSucc)
    Ms hm₀ hf hk hw hU
  have hfer : ferSum (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) w =
      ∑ i ∈ Finset.univ.filter (fun i => sh (Fin.castSucc i) ≠ 4), w i := by
    simp only [ferSum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ne, huniq l, hne l]
  rw [hfer]
  exact hP0

/-- **The face form of P0**: `w γ₀ ≤ 1/4 ⇒ (3/4) c₀ ≤ V₀` on the simplex. -/
theorem faceId_vp_hV_face {m : ℕ} (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (Ms : Fin (m + 1) → ℝ) (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (w : Fin (m + 1) → ℝ)
    (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (hU : symanzikU (castLoopMatrix fun l : Fin (m + 1) =>
      base (sh l.castSucc)) w ≠ 0) (hγ : w (Fin.last m) ≤ 1 / 4) :
    3 / 4 * faceIdC0 m₀ k ≤
      symanzikV (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
        (fun l => c (sh l.castSucc) • k) Ms w := by
  have h := faceId_vp_hV base c hrow hrow4 y₁ y₂ hflow sh hsh hm₀ Ms hf hk w hw hU
  rw [ferSum_eq_one_sub (faceId_vp_rows base hrow hrow4 sh hsh).1 hw1] at h
  have h0 := faceId_c0_pos hm₀ hk
  have : faceIdC0 m₀ k * (3 / 4) ≤ faceIdC0 m₀ k * (1 - w (Fin.last m)) :=
    mul_le_mul_of_nonneg_left (by linarith) h0.le
  linarith

/-- **Integrability of the collapsed integrand of a merged piece** at every `t ≥ 1`, for any
representative `Q` of the numerator. -/
theorem faceId_vp_hint {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (m + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q : LoopQuartic) (hQ : Q.eval = N)
    (t : ℝ) (ht : 1 ≤ t) :
    IntegrableOn (fun x => pieceF (m + 1) Q
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t (simplexPoint x)) (simplexSet m) := by
  have hm0 : 0 < m := by omega
  set γ₀ := Fin.last m
  set α := castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc) with hα_def
  set p : Fin (m + 1) → Fin 4 → ℝ := fun l => c (sh l.castSucc) • k
  have huniq := (faceId_vp_rows base hrow hrow4 sh hsh).1
  have hc₀ := faceId_c0_pos hm₀ hk
  have hl : sh (Fin.last (m + 1)) = sh (Fin.last m).castSucc := by
    rw [(hsh _).2 (by simp), (hsh _).2 (by simp)]
  have hαd : castLoopMatrix (fun l => base (sh l)) = dbl γ₀ α :=
    comp_eq_dbl sh hl fun r s => (base r s : ℝ)
  have hcrit' : NoSubdivergenceRefined 2 E (dbl γ₀ α) :=
    hαd ▸ (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).2 hcrit
  have hpd : (fun l => c (sh l) • k) = dbl γ₀ p := comp_eq_dbl sh hl fun r => c r • k
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
      have h1 := faceId_vp_hV base c hrow hrow4 y₁ y₂ hflow sh hsh hm₀ Ms hf hk _ hz.1 hU
      rw [ferSum_eq_one_sub huniq hz.2] at h1
      have hzγ := hz.1 γ₀
      have hzγ1 : simplexPoint y γ₀ ≤ 1 := by
        rw [← hz.2]
        exact Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ γ₀)
      have e1 := mul_le_mul_of_nonneg_right (min_le_left (faceIdC0 m₀ k) 1) (sub_nonneg.2 hzγ1)
      have e2 := mul_le_mul_of_nonneg_right (min_le_right (faceIdC0 m₀ k) 1) hzγ
      have e3 := mul_le_mul_of_nonneg_left ht hzγ
      nlinarith
  refine hIg.congr_fun (fun x _ => ?_) (QED.Integration.Feynman.measurableSet_simplexSet m)
  simp only [pieceF, paramAtV_congr (hQg.trans hQ.symm)]

/-- **The limit of one merged piece at a fixed momentum**: `t · pairDens(t, k) → -π⁴ (face₁ +
face₀)`, the face limits written with any representative `Q` of the numerator. -/
theorem faceId_vp_tendsto {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (m + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N) {d₁ d₀ : ℕ}
    (hQ₁ : ∃ Q : LoopQuartic, Q.eval = N ∧ LoopDegLe 1 d₁ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hQ₀ : ∃ Q : LoopQuartic, Q.eval = N ∧ LoopDegLe 0 d₀ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hd₁ : d₁ ≤ 3) (hd₀ : d₀ ≤ 3)
    (hA1 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card)
    (hd11 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card = 2 →
      d₁ ≤ 1)
    (hR1 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![1, 0])
    (hA0 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card)
    (hd01 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card = 2 →
      d₀ ≤ 1)
    (hR0 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![0, 1])
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ) (hMs : Ms (Fin.last m) = 0)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q : LoopQuartic)
    (hQ : Q.eval = N) :
    Tendsto (fun t : ℝ => (t : ℂ) * pairDens N
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t) atTop
      (𝓝 (-((π : ℂ) ^ 4) * (limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
        {w | faceSum (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (m + 1) Q (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) u) (simplexPoint x)) +
        limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
        {w | faceSum0 (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (m + 1) Q (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) u) (simplexPoint x))))) := by
  set γ₀ := Fin.last m with hγ₀
  set α := castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc) with hα_def
  set cs : Fin (m + 1) → ℝ := fun l => c (sh l.castSucc) with hcs
  obtain ⟨huniq, hrow3⟩ := faceId_vp_rows base hrow hrow4 sh hsh
  have hf10 : (Finset.univ.filter fun l => α l ≠ ![1, 0]) =
      Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0] := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, α]
    exact not_congr (castLoopMatrix_eq_row10_iff _ l)
  have hf01 : (Finset.univ.filter fun l => α l ≠ ![0, 1]) =
      Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1] := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, α]
    exact not_congr (castLoopMatrix_eq_row01_iff _ l)
  obtain ⟨Q₁, hQ₁e, hQ₁d, hQ₁q⟩ := hQ₁
  obtain ⟨Q₀, hQ₀e, hQ₀d, hQ₀q⟩ := hQ₀
  obtain ⟨B₁, hB₁⟩ := lqBdd_finite fun _ : Unit => Q₁
  obtain ⟨B₀, hB₀⟩ := lqBdd_finite fun _ : Unit => Q₀
  have hn : m + 1 = 7 ∨ (m + 1 = 6 ∧ ∀ _ : Unit, Q₁.quart = 0 ∧ Q₁.quart = 0 ∧
      Q₀.quart = 0) := by
    rcases hm with h5 | h6
    · refine Or.inr ⟨by omega, fun _ => ?_⟩
      have q₁ := hQ₁q.resolve_left (by omega)
      exact ⟨q₁, q₁, hQ₀q.resolve_left (by omega)⟩
    · exact Or.inl (by omega)
  have hc₀ := faceId_c0_pos hm₀ hk
  have hV : ∀ (_ : Unit) (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → faceIdC0 m₀ k * ferSum α w ≤
        symanzikV α (fun i => cs i • (fun _ : Unit => k) ()) Ms w :=
    fun _ w hw _ hU => faceId_vp_hV base c hrow hrow4 y₁ y₂ hflow sh hsh hm₀ Ms hf hk w hw hU
  have hint : ∀ (_ : Unit) (u : ℝ), 1 ≤ u → IntegrableOn
      (fun x => pieceF (m + 1) Q₁ α (fun i => cs i • (fun _ : Unit => k) ()) Ms γ₀ u
        (simplexPoint x)) (simplexSet m) := fun _ u hu =>
    faceId_vp_hint base c hrow hrow4 y₁ y₂ hflow hm sh hsh hcrit N hpoly hB hm₀ Ms hf hk Q₁
      hQ₁e u hu
  have hMb : ∀ (_ : Unit) l, |Ms l| ≤ ∑ j, |Ms j| := fun _ l =>
    Finset.single_le_sum (f := fun j => |Ms j|) (fun j _ => abs_nonneg _) (Finset.mem_univ l)
  have hkb : ∀ _ : Unit, ‖k‖ ≤ ‖k‖ := fun _ => le_rfl
  have hR1' : ∃ l, α l = ![1, 0] := by
    obtain ⟨l, hl⟩ := hR1; exact ⟨l, (castLoopMatrix_eq_row10_iff _ l).2 hl⟩
  have hR0' : ∃ l, α l = ![0, 1] := by
    obtain ⟨l, hl⟩ := hR0; exact ⟨l, (castLoopMatrix_eq_row01_iff _ l).2 hl⟩
  obtain ⟨C, hC⟩ := faceId_piece_rate (n := m + 1) (by omega) α γ₀ huniq hrow3 (by rwa [hf10])
    hR1' (by rwa [hf01]) hR0' cs (fun _ : Unit => k) (fun _ => Ms) (fun _ => Q₁)
    (fun _ => Q₁) (fun _ => Q₀) hB₁ hB₁ hB₀ (fun _ => rfl) (fun _ => hQ₀e.trans hQ₁e.symm)
    (fun _ => hQ₁d.mono hd₁) (fun h _ => hQ₁d.mono (hd11 (by rwa [hf10] at h)))
    (fun _ => hQ₀d.mono hd₀) (fun h _ => hQ₀d.mono (hd01 (by rwa [hf01] at h))) hn hkb hMb hc₀
    hV hint
  have hlim := faceId_piece_limUnder (n := m + 1) (by omega) α γ₀ huniq hrow3 (by rwa [hf10])
    hR1' (by rwa [hf01]) hR0' cs (fun _ : Unit => k) (fun _ => Ms) (fun _ => Q₁)
    (fun _ => Q₁) (fun _ => Q₀) hB₁ hB₁ hB₀ (fun _ => rfl) (fun _ => hQ₀e.trans hQ₁e.symm)
    (fun _ => hQ₁d.mono hd₁) (fun h _ => hQ₁d.mono (hd11 (by rwa [hf10] at h)))
    (fun _ => hQ₀d.mono hd₀) (fun h _ => hQ₀d.mono (hd01 (by rwa [hf01] at h))) hn hkb hMb hc₀
    hV hint ()
  have hPF := faceId_pieceF_congr (hQ₁e.trans hQ.symm) (m + 1) α (fun i => cs i • k) Ms γ₀
  simp only [hPF] at hC hlim
  have hMu : Function.update Ms γ₀ 0 = Ms := by
    rw [Function.update_eq_self_iff]; exact hMs.symm
  have hpd : ∀ t : ℝ, pairDens N α (fun l => cs l • k) Ms γ₀ t =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m,
        pieceF (m + 1) Q α (fun i => cs i • k) Ms γ₀ t (simplexPoint x) := fun t => by
    rw [pairDens_eq hQ, hMu]
    rfl
  rw [← hlim]
  refine faceId_tendsto_of_rate (C := π ^ 4 * C) fun t ht => ?_
  rw [hpd]
  have e : (t : ℂ) * (-((π : ℂ) ^ 4) * ∫ x in simplexSet m,
      pieceF (m + 1) Q α (fun i => cs i • k) Ms γ₀ t (simplexPoint x)) -
      -((π : ℂ) ^ 4) * limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
        pieceF (m + 1) Q α (fun i => cs i • k) Ms γ₀ u (simplexPoint x)) =
      -((π : ℂ) ^ 4) * (t • (∫ x in simplexSet m,
        pieceF (m + 1) Q α (fun i => cs i • k) Ms γ₀ t (simplexPoint x)) -
        limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
          pieceF (m + 1) Q α (fun i => cs i • k) Ms γ₀ u (simplexPoint x))) := by
    rw [Complex.real_smul]; ring
  rw [e, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC () t ht) (by positivity)

end Piece

end QED.GradedProof.RPi4

end
