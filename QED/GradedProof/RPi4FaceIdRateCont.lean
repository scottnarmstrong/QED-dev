/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4InstClass

/-!
# (R-Π₄) step L10, T2.UV: continuity of a collapsed piece in the photon mass

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.UV, the
input `QED.GradedProof.RPi4.MajFaceRate`). The collapsed integral `∫ pieceF(u)` of a piece is a
continuous function of the squared photon mass `u > 0` as soon as its photon-weighted
coefficients are integrable and `V₀ ≥ c₀ (1 - z_γ)` where `U ≠ 0` (the form of P0): on
`u ≥ u₀/2` the remainder `V₀ + z_γ u` is at least `min(c₀, u₀/2)`, and dominated convergence
applies to the three terms of `paramAtV`.

* `faceIdRate_pieceF_eq`: the three-term form of `pieceF`;
* **`faceIdRate_continuousAt_pieceF`**, **`faceIdRate_continuousOn_pieceF`**;
* `faceIdRate_continuousOn_vpPiece`: one merged piece of a vacuum-polarization shape (the
  integrability of `heavyRate_vpPiece`, P0 `symanzikV_vp_ge_fermion`);
* `faceIdRate_continuousOn_triDens`, `faceIdRate_continuousOn_blockDens`;
* **`faceIdRate_continuousOn_vDens_VA`**, `…_VB`, `…_VC`: the class densities are continuous on
  `u > 0` at every momentum below threshold.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

variable {m n : ℕ} {Q : LoopQuartic} {α : Fin (m + 1) → Fin 2 → ℝ}
  {pp : Fin (m + 1) → Fin 4 → ℝ} {M : Fin (m + 1) → ℝ} {γ₀ : Fin (m + 1)}

/-- **The three-term form of `pieceF`** at a simplex point. -/
theorem faceIdRate_pieceF_eq (u : ℝ) (y : Fin m → ℝ) :
    pieceF n Q α pp M γ₀ u (simplexPoint y) =
      (simplexPoint y γ₀ : ℂ) * cOneAt n Q α pp (simplexPoint y) *
          (((symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u : ℝ) : ℂ) ^ (n - 3))⁻¹ +
        (simplexPoint y γ₀ : ℂ) * cTwoAt n Q α pp (simplexPoint y) *
          (((symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u : ℝ) : ℂ) ^ (n - 4))⁻¹ +
        (simplexPoint y γ₀ : ℂ) * cThreeAt n Q α (simplexPoint y) *
          (((symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u : ℝ) : ℂ) ^ (n - 5))⁻¹ := by
  simp only [pieceF, paramAtV_eq]
  ring

/-- **Continuity at one photon mass** by dominated convergence, given a uniform lower bound on
the remainder for `u` near `u₀`. -/
theorem faceIdRate_continuousAt_pieceF {u₀ c : ℝ} (hc : 0 < c)
    (k1 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cOneAt n Q α pp (simplexPoint y))
      (simplexSet m))
    (k2 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cTwoAt n Q α pp (simplexPoint y))
      (simplexSet m))
    (k3 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cThreeAt n Q α (simplexPoint y))
      (simplexSet m))
    (hV : ∀ᶠ u in 𝓝 u₀, ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      c ≤ symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u) :
    ContinuousAt (fun u => ∫ y in simplexSet m, pieceF n Q α pp M γ₀ u (simplexPoint y))
      u₀ := by
  set g₁ : (Fin m → ℝ) → ℂ := fun y => (simplexPoint y γ₀ : ℂ) * cOneAt n Q α pp (simplexPoint y)
  set g₂ : (Fin m → ℝ) → ℂ := fun y => (simplexPoint y γ₀ : ℂ) * cTwoAt n Q α pp (simplexPoint y)
  set g₃ : (Fin m → ℝ) → ℂ := fun y => (simplexPoint y γ₀ : ℂ) * cThreeAt n Q α (simplexPoint y)
  set V : ℝ → (Fin m → ℝ) → ℝ := fun u y =>
    symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u with hV_def
  have e : ∀ u y, pieceF n Q α pp M γ₀ u (simplexPoint y) =
      g₁ y * (((V u y : ℂ)) ^ (n - 3))⁻¹ + g₂ y * (((V u y : ℂ)) ^ (n - 4))⁻¹ +
        g₃ y * (((V u y : ℂ)) ^ (n - 5))⁻¹ := fun u y => faceIdRate_pieceF_eq u y
  have hg0 : ∀ y, symanzikU α (simplexPoint y) = 0 → g₁ y = 0 ∧ g₂ y = 0 ∧ g₃ y = 0 :=
    fun y hU => by simp [g₁, g₂, g₃, cOneAt, cTwoAt, cThreeAt, hU]
  have hb : ∀ u (k : ℕ) y, c ≤ V u y → ‖(((V u y : ℂ)) ^ k)⁻¹‖ ≤ (c ^ k)⁻¹ := fun u k y hcv => by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hc.le.trans hcv)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le hcv k)
  set bound : (Fin m → ℝ) → ℝ := fun y => ‖g₁ y‖ * (c ^ (n - 3))⁻¹ +
    ‖g₂ y‖ * (c ^ (n - 4))⁻¹ + ‖g₃ y‖ * (c ^ (n - 5))⁻¹ with hbound
  refine continuousAt_of_dominated (bound := bound) ?_ ?_ ?_ ?_
  · filter_upwards [hV] with u hu
    exact (integrableOn_pieceF hc k1 k2 k3 hu).aestronglyMeasurable
  · filter_upwards [hV] with u hu
    refine ae_restrict_of_forall_mem (measurableSet_simplexSet m) fun y hy => ?_
    rw [e]
    by_cases hU : symanzikU α (simplexPoint y) = 0
    · obtain ⟨h1, h2, h3⟩ := hg0 y hU
      rw [h1, h2, h3]
      simp only [zero_mul, add_zero, norm_zero, hbound]
      positivity
    · have hcv := hu y hy hU
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      all_goals rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hb u _ y hcv) (norm_nonneg _)
  · exact ((k1.norm.mul_const _).add (k2.norm.mul_const _)).add (k3.norm.mul_const _)
  · refine ae_restrict_of_forall_mem (measurableSet_simplexSet m) fun y hy => ?_
    by_cases hU : symanzikU α (simplexPoint y) = 0
    · obtain ⟨h1, h2, h3⟩ := hg0 y hU
      simp only [e, h1, h2, h3, zero_mul, add_zero]
      exact continuousAt_const
    · have hcv := hV.self_of_nhds y hy hU
      have hne : ((V u₀ y : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]; exact (hc.trans_le hcv).ne'
      have hVc : ContinuousAt (fun u => ((V u y : ℝ) : ℂ)) u₀ := by
        simp only [hV_def]; fun_prop
      have term : ∀ k : ℕ, ContinuousAt (fun u => (((V u y : ℝ) : ℂ) ^ k)⁻¹) u₀ := fun k =>
        (hVc.pow k).inv₀ (pow_ne_zero k hne)
      simp only [e]
      exact (((term _).const_mul _).add ((term _).const_mul _)).add ((term _).const_mul _)

/-- **Continuity on `u > 0`** under the P0 form `V₀ ≥ c₀ (1 - z_γ)` where `U ≠ 0`. -/
theorem faceIdRate_continuousOn_pieceF {c₀ : ℝ} (hc₀ : 0 < c₀)
    (k1 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cOneAt n Q α pp (simplexPoint y))
      (simplexSet m))
    (k2 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cTwoAt n Q α pp (simplexPoint y))
      (simplexSet m))
    (k3 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cThreeAt n Q α (simplexPoint y))
      (simplexSet m))
    (hV : ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      c₀ * (1 - simplexPoint y γ₀) ≤ symanzikV α pp M (simplexPoint y)) :
    ContinuousOn (fun u => ∫ y in simplexSet m, pieceF n Q α pp M γ₀ u (simplexPoint y))
      (Ioi 0) := by
  intro u₀ hu₀
  have hu₀' : (0 : ℝ) < u₀ := hu₀
  refine (faceIdRate_continuousAt_pieceF (c := min c₀ (u₀ / 2)) (lt_min hc₀ (by linarith))
    k1 k2 k3 ?_).continuousWithinAt
  filter_upwards [lt_mem_nhds (show u₀ / 2 < u₀ by linarith)] with u hu y hy hU
  have hz := simplexPoint_mem_stdSimplex hy
  have hzγ := hz.1 γ₀
  have hzγ1 : simplexPoint y γ₀ ≤ 1 := by
    rw [← hz.2]
    exact Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ γ₀)
  have h1 := hV y hy hU
  have e1 := mul_le_mul_of_nonneg_right (min_le_left c₀ (u₀ / 2)) (sub_nonneg.2 hzγ1)
  have e2 := mul_le_mul_of_nonneg_right (min_le_right c₀ (u₀ / 2)) hzγ
  have e3 := mul_le_mul_of_nonneg_left hu.le hzγ
  nlinarith

/-! ### One merged piece -/

section Piece

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZeroLimit
open QED.GradedProof.WI2 (dbl)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])

include hflow hrow hrow4

/-- **Continuity in the photon mass of one merged piece** of a vacuum-polarization shape (the
doubled shape `sh` with its two photon lines last), at a momentum below threshold. -/
theorem faceIdRate_continuousOn_vpPiece {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (m + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ) (hMs : Ms (Fin.last m) = 0)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) :
    ContinuousOn (fun t => pairDens N
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t) (Ioi 0) := by
  classical
  have hm0 : 0 < m := by omega
  set γ₀ := Fin.last m with hγ₀
  set α := castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc) with hα_def
  set p : Fin (m + 1) → Fin 4 → ℝ := fun l => c (sh l.castSucc) • k with hp
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
  have hferF : ∀ z : Fin (m + 1) → ℝ, ferSum α z =
      ∑ i ∈ Finset.univ.filter (fun i => sh (Fin.castSucc i) ≠ 4), z i := fun z => by
    simp only [ferSum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ne, huniq l, hne l]
  set c₀ := min 1 (1 + Minkowski.dot k k / (2 * m₀) ^ 2) * m₀ ^ 2 with hc₀_def
  have hT : 0 < (2 * m₀) ^ 2 := by positivity
  have hc₀ : 0 < c₀ := by
    refine mul_pos (lt_min one_pos ?_) (by positivity)
    have : -1 < Minkowski.dot k k / (2 * m₀) ^ 2 := by rw [lt_div_iff₀ hT]; linarith
    linarith
  have hV : ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      c₀ * (1 - simplexPoint y γ₀) ≤ symanzikV α p Ms (simplexPoint y) := by
    intro y hy hU
    have hz := simplexPoint_mem_stdSimplex hy
    have hP0 := symanzikV_vp_ge_fermion base c y₁ y₂ hflow (fun l : Fin (m + 1) => sh l.castSucc)
      Ms hm₀ hf hk hz.1 hU
    rw [← hferF, ferSum_eq_one_sub huniq hz.2] at hP0
    exact hP0
  -- integrability of the photon-weighted coefficients
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
  have hcont := faceIdRate_continuousOn_pieceF (M := Ms) hc₀ k1 k2 k3 hV
  have hMu : Function.update Ms γ₀ 0 = Ms := by
    rw [Function.update_eq_self_iff]; exact hMs.symm
  refine ((continuousOn_const (c := -((Real.pi : ℂ) ^ 4))).mul hcont).congr fun t _ => ?_
  rw [pairDens_eq hQg, hMu]
  rfl

/-- **Continuity of the fifteen pieces** (`triDens`) in the photon mass. -/
theorem faceIdRate_continuousOn_triDens
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
    {m₀ : ℝ} (hm₀ : 0 < m₀) {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (μ ν : Fin 4) :
    ContinuousOn (fun t => triDens base c Num E4 M X Y t k μ ν) (Ioi 0) := by
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
  have PA : ∀ i j : Fin 4, ContinuousOn (fun t => if i ≤ j then
      pairDens (fun ℓ => C * Num M k ℓ μ ν)
        (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
        (fun l => c (shA i j l.castSucc) • k)
        ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0]
        (Fin.last 6) t
      else 0) (Ioi 0) := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hij, ite_true]
      have hMf : ∀ l, m₀ ≤ mA M X Y i j l := fun l => by unfold mA; split_ifs <;> assumption
      exact faceIdRate_continuousOn_vpPiece base c y₁ y₂ hflow hrow hrow4 (Or.inr rfl) (shA i j)
        (fun l => by fin_cases l <;> simp [shA, Fin.ext_iff] <;> omega) (hcA i j)
        (fun ℓ => C * Num M k ℓ μ ν) ((hP M k μ ν).const_mul _)
        ((hBA M k μ ν i j).const_mul _) hm₀ _ rfl
        (fun l hl => by
          fin_cases l
          exacts [hMf 0, hMf 1, hMf 2, hMf 3, hX, hY, absurd rfl hl]) hk
    · simp only [hij, ite_false]
      exact continuousOn_const
  have PB : ∀ i : Fin 4, ContinuousOn (fun t =>
      pairDens (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν))
        (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
        (fun l => c (shB i l.castSucc) • k)
        ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] (Fin.last 5) t) (Ioi 0) := by
    intro i
    have hpoly : IsLoopPoly 2 3 fun ℓ =>
        -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν) := by
      have e : (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) =
          fun ℓ => (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
            (E2 k ℓ μ ν + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * E4 k μ ν) := by
        funext ℓ; rw [hE, hE]; ring
      rw [e]
      exact (((hP2 k μ ν).add (IsLoopPoly.const _)).const_mul _).mono (by norm_num)
    have hMf : ∀ l, m₀ ≤ mB X Y i l := fun l => by unfold mB; split_ifs <;> assumption
    exact faceIdRate_continuousOn_vpPiece base c y₁ y₂ hflow hrow hrow4 (Or.inl rfl) (shB i)
      (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]; omega) (hcB i)
      (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) hpoly
      ((((hBB X k μ ν i).sub (hBB M k μ ν i)).const_mul _).mono (by decide) le_rfl) hm₀ _ rfl
      (fun l hl => by
        fin_cases l
        exacts [hMf 0, hMf 1, hMf 2, hMf 3, hY, absurd rfl hl]) hk
  have PC : ContinuousOn (fun t =>
      pairDens (fun ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
        (castLoopMatrix fun l : Fin 6 => base (shB 0 l.castSucc))
        (fun l => c (shB 0 l.castSucc) • k) ![Y, Y, Y, Y, Y, 0] (Fin.last 5) t) (Ioi 0) :=
    faceIdRate_continuousOn_vpPiece base c y₁ y₂ hflow hrow hrow4 (Or.inl rfl) (shB 0)
      (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]) (hcB 0)
      (fun ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
      (((IsLoopPoly.const (n := 0) _).mul
        ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y 0)).mono (by norm_num))
      (((rb_propDenom_pad base (ppc c k) (shB 0) 0 4 (by decide) 0 rfl rfl Y
        0).const_mul _).mono (by decide) (by norm_num)) hm₀ _ rfl
      (fun l hl => by
        fin_cases l
        exacts [hY, hY, hY, hY, hY, absurd rfl hl]) hk
  refine (((continuousOn_finsetSum Finset.univ fun i _ =>
    continuousOn_finsetSum Finset.univ fun j _ => PA i j).add
      (continuousOn_finsetSum Finset.univ fun i _ => PB i)).add PC).congr fun t _ => ?_
  simp only [triDens, hC, Pi.add_apply]

/-- **Continuity of the block-summed flavour sum** in the photon mass. -/
theorem faceIdRate_continuousOn_blockDens
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
    {m₀ : ℝ} (hm₀ : 0 < m₀) {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k)
    (μ ν : Fin 4) :
    ContinuousOn (fun t => blockDens base c Num E4 Φ m₀ t k μ ν) (Ioi 0) := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  refine (continuousOn_finsetSum Finset.univ fun f _ =>
    (faceIdRate_continuousOn_triDens base c y₁ y₂ hflow hrow hrow4 hcA hcB Num E0 E2 E4 hE hP
      hP2 hBA hBB hm₀ (hmass f) hX (Y := blockX Φ m₀ + 1) (by linarith) hk μ ν).const_smul
        (Φ.coeff f : ℂ)).congr fun t _ => ?_
  simp only [blockDens, Pi.smul_apply, smul_eq_mul]

end Piece

/-! ### The three classes -/

section Classes

open QED.GradedProof.VP2

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) {k : Fin 4 → ℝ}
  (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (μ ν : Fin 4)

include hm₀ hmass hk

/-- **The class density `VA` is continuous** in the photon mass `u > 0`. -/
theorem faceIdRate_continuousOn_vDens_VA :
    ContinuousOn (fun u => vDens aVA baseVA cVA Φ e m₀ u k μ ν) (Ioi 0) :=
  faceIdRate_continuousOn_blockDens baseVA cVA ![0, 0] ![-1, -1] flowVA (by decide) (by decide)
    critA_VA critB_VA _ _ _ _
    (vNum_eq e 0 1 aVA baseVA cVA fun a b ρ σ => isOddG_aVA a b ρ σ)
    (isLoopPoly_vNum e 0 1 aVA baseVA cVA) (isLoopPoly_vNumE2 e 0 1 aVA baseVA cVA)
    (fun m k a' b' i j => rb_vNum e 0 1 aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b') hm₀ Φ hmass hk μ ν

/-- **The class density `VB` is continuous** in the photon mass `u > 0`. -/
theorem faceIdRate_continuousOn_vDens_VB :
    ContinuousOn (fun u => vDens aVB baseVB cVB Φ e m₀ u k μ ν) (Ioi 0) :=
  faceIdRate_continuousOn_blockDens baseVB cVB ![0, 1] ![-1, 0] flowVB (by decide) (by decide)
    critA_VB critB_VB _ _ _ _
    (vNum_eq e 0 1 aVB baseVB cVB fun a b ρ σ => isOddG_aVB a b ρ σ)
    (isLoopPoly_vNum e 0 1 aVB baseVB cVB) (isLoopPoly_vNumE2 e 0 1 aVB baseVB cVB)
    (fun m k a' b' i j => rb_vNum e 0 1 aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b') hm₀ Φ hmass hk μ ν

/-- **The class density `VC` is continuous** in the photon mass `u > 0`. -/
theorem faceIdRate_continuousOn_vDens_VC :
    ContinuousOn (fun u => vDens aVC baseVC cVC Φ e m₀ u k μ ν) (Ioi 0) :=
  faceIdRate_continuousOn_blockDens baseVC cVC ![0, 1] ![-1, 0] flowVC (by decide) (by decide)
    critA_VC critB_VC _ _ _ _
    (vNum_eq e 0 1 aVC baseVC cVC fun a b ρ σ => isOddG_aVC a b ρ σ)
    (isLoopPoly_vNum e 0 1 aVC baseVC cVC) (isLoopPoly_vNumE2 e 0 1 aVC baseVC cVC)
    (fun m k a' b' i j => rb_vNum e 0 1 aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b') hm₀ Φ hmass hk μ ν

end Classes

end QED.GradedProof.RPi4

end
