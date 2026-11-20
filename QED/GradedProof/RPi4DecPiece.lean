/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4DecPoint
public import QED.GradedProof.RPi4InstPiece

/-!
# (R-Π₄) step L9: second differences of one piece of a vacuum-polarization class

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L9 (second
differences in `s`, the class inputs `QED.GradedProof.RPi4.DecVTwo`). The photon-mass density
`pairDens` of a merged piece of a vacuum-polarization shape (photon line last) at the tilted
momenta `k'(s) = tiltVec c s` is, for every photon mass `t > 0`, of class
`QED.GradedProof.RPi4.DecTwoReg` on `[-δ, δ]` with second-difference constant `K(t) ≤ B / t`
(`dec_pieceTwo_vpPiece`). The proof integrates the pointwise bound `dec_twoReg_point` (constants
`Λ · decNodeMaj`) and bounds `t ∫ decMajF` at each interpolation node by `dec_maj_rate`.

`DecPieceTwo c δ D` names the conclusion; it is closed under sums and constant multiples.
`dec_kNode_dot`: at `c = 1` the nodes of the tilted segment over `[-δ, δ]` have squares in
`(-3, δ]` when `δ (D + 1) ≤ 1/4`; `dec_vTwo_of_pieceTwo`: the class input
`QED.GradedProof.RPi4.DecVTwo` from `DecPieceTwo` of the class density.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit
open QED.GradedProof.WI2 (dbl)
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex
  measurableSet_simplexSet)
open QED.TwoLoop.Bridge (IsLoopPoly)
open QED.TwoLoop.PauliZeroExplicit (numQuartic eval_numQuartic)

/-- **Second differences of a photon-mass density at the tilted momenta, `O(1/t)`**: for every
`t > 0`, `s ↦ D(t, k'(s))` is of class `DecTwoReg` on `[-δ, δ]` with `t K(t) ≤ B`. -/
def DecPieceTwo (c δ : ℝ) (D : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ B : ℝ, ∀ t : ℝ, 0 < t → ∃ M L K : ℝ,
    DecTwoReg (-δ) δ (fun s => D t (tiltVec c s)) M L K ∧ t * K ≤ B

namespace DecPieceTwo

variable {c δ : ℝ} {D D' : ℝ → (Fin 4 → ℝ) → ℂ}

theorem add (h : DecPieceTwo c δ D) (h' : DecPieceTwo c δ D') :
    DecPieceTwo c δ fun t k => D t k + D' t k := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨B', hB'⟩ := h'
  refine ⟨B + B', fun t ht => ?_⟩
  obtain ⟨M, L, K, hr, hK⟩ := hB t ht
  obtain ⟨M', L', K', hr', hK'⟩ := hB' t ht
  exact ⟨_, _, _, hr.add hr', by rw [mul_add]; linarith⟩

theorem const_mul (h : DecPieceTwo c δ D) (r : ℂ) : DecPieceTwo c δ fun t k => r * D t k := by
  obtain ⟨B, hB⟩ := h
  refine ⟨‖r‖ * B, fun t ht => ?_⟩
  obtain ⟨M, L, K, hr, hK⟩ := hB t ht
  refine ⟨_, _, _, hr.const_mul r, ?_⟩
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left hK (norm_nonneg r)

theorem zero : DecPieceTwo c δ fun _ _ => 0 :=
  ⟨0, fun _ _ => ⟨0, 0, 0, DecTwoReg.zero, by simp⟩⟩

theorem sum {ι : Type*} (s : Finset ι) {D : ι → ℝ → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, DecPieceTwo c δ (D i)) : DecPieceTwo c δ fun t k => ∑ i ∈ s, D i t k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : DecPieceTwo c δ fun _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem congr (h : DecPieceTwo c δ D)
    (e : ∀ t : ℝ, 0 < t → ∀ s : ℝ, |s| ≤ δ → D t (tiltVec c s) = D' t (tiltVec c s)) :
    DecPieceTwo c δ D' := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun t ht => ?_⟩
  obtain ⟨M, L, K, hr, hK⟩ := hB t ht
  exact ⟨M, L, K, hr.congr fun s hs => e t ht s (abs_le.mpr hs), hK⟩

end DecPieceTwo

/-! ### One piece -/

section Piece

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])

include hflow hrow hrow4

/-- **Second differences of one merged piece of a vacuum-polarization shape at the tilted
momenta**, `O(1/t)` for every photon mass `t > 0`. Hypotheses as in `heavyRate_vpPiece`; the
point `S₀ < -δ` lies above the threshold `-(2m₀)²`, and the interpolation nodes (degree
`2d + 8`) of the tilted segment over `[Sl, S] ⊇ [-δ, δ]` have squares in `(S₀, S]`. -/
theorem dec_pieceTwo_vpPiece {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 (m + 1 - 3) (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 (N k))
    {d : ℕ} (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) {d₁ d₀ : ℕ}
    (hQ₁ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧ LoopDegLe 1 d₁ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hQ₀ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧ LoopDegLe 0 d₀ Q ∧ (m = 6 ∨ Q.quart = 0))
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
    {cc S₀ Sl S δ : ℝ} (hδ : 0 < δ) (hS₀ : S₀ < -δ) (hSl : Sl ≤ -δ) (hS : δ ≤ S)
    (hSc : S < 2 * cc ^ 2) (hthr : -(2 * m₀) ^ 2 < S₀)
    (hnode : ∀ l, S₀ < Minkowski.dot (decKNode cc Sl S (2 * d + 8) l)
        (decKNode cc Sl S (2 * d + 8) l) ∧
      Minkowski.dot (decKNode cc Sl S (2 * d + 8) l) (decKNode cc Sl S (2 * d + 8) l) ≤ S) :
    DecPieceTwo cc δ fun t k => pairDens (N k)
      (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t := by
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
  have hrow3 : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1] := fun l => by
    by_cases h4 : sh l.castSucc = 4
    · exact Or.inr (Or.inr ((hrows l).2 h4))
    · rcases (hrows l).1 h4 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
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
  have hferF : ∀ z : Fin (m + 1) → ℝ, ferSum α z =
      ∑ i ∈ Finset.univ.filter (fun i => sh (Fin.castSucc i) ≠ 4), z i := fun z => by
    simp only [ferSum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ne, huniq l, hne l]
  -- the lower bound of `V₀` at every momentum above `S₀`
  set c₀ := min 1 (1 + S₀ / (2 * m₀) ^ 2) * m₀ ^ 2 with hc₀_def
  have hT : 0 < (2 * m₀) ^ 2 := by positivity
  have hc₀ : 0 < c₀ := by
    refine mul_pos (lt_min one_pos ?_) (by positivity)
    have : -1 < S₀ / (2 * m₀) ^ 2 := by rw [lt_div_iff₀ hT]; linarith
    linarith
  have hV : ∀ k : Fin 4 → ℝ, S₀ ≤ Minkowski.dot k k → ∀ z : Fin (m + 1) → ℝ, (∀ l, 0 ≤ z l) →
      symanzikU α z ≠ 0 → c₀ * ferSum α z ≤ symanzikV α (fun i => cs i • k) Ms z := by
    intro k hs z hz hU
    have hP0 := symanzikV_vp_ge_fermion base c y₁ y₂ hflow (fun l : Fin (m + 1) => sh l.castSucc)
      Ms hm₀ hf (k := k) (by linarith) hz hU
    rw [← hferF] at hP0
    have hmin : c₀ ≤ min 1 (1 + Minkowski.dot k k / (2 * m₀) ^ 2) * m₀ ^ 2 := by
      refine mul_le_mul_of_nonneg_right (min_le_min le_rfl ?_) (by positivity)
      have := div_le_div_of_nonneg_right hs hT.le
      linarith
    have hF0 : 0 ≤ ferSum α z := Finset.sum_nonneg fun l _ => hz l
    exact (mul_le_mul_of_nonneg_right hmin hF0).trans hP0
  have hVt : ∀ k : Fin 4 → ℝ, S₀ ≤ Minkowski.dot k k → ∀ t : ℝ, 0 < t →
      ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      min c₀ t ≤ symanzikV α (fun i => cs i • k) Ms (simplexPoint y) +
        simplexPoint y γ₀ * t := by
    intro k hs t ht y hy hU
    have hz := simplexPoint_mem_stdSimplex hy
    have h1 := hV k hs _ hz.1 hU
    rw [ferSum_eq_one_sub huniq hz.2] at h1
    have hzγ := hz.1 γ₀
    have hzγ1 : simplexPoint y γ₀ ≤ 1 := by
      rw [← hz.2]
      exact Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ γ₀)
    have e1 := mul_le_mul_of_nonneg_right (min_le_left c₀ t) (sub_nonneg.2 hzγ1)
    have e2 := mul_le_mul_of_nonneg_right (min_le_right c₀ t) hzγ
    nlinarith
  -- integrable coefficients at every momentum
  have hl : sh (Fin.last (m + 1)) = sh (Fin.last m).castSucc := by
    rw [(hsh _).2 (by simp), (hsh _).2 (by simp)]
  have hαd : castLoopMatrix (fun l => base (sh l)) = dbl γ₀ α :=
    comp_eq_dbl sh hl fun r s => (base r s : ℝ)
  have hcrit' : NoSubdivergenceRefined 2 E (dbl γ₀ α) :=
    hαd ▸ (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).2 hcrit
  have hcoef : ∀ k : Fin 4 → ℝ,
      IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) *
        cOneAt (m + 1) (numQuartic (N k)) α (fun i => cs i • k) (simplexPoint y))
        (simplexSet m) ∧
      IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) *
        cTwoAt (m + 1) (numQuartic (N k)) α (fun i => cs i • k) (simplexPoint y))
        (simplexSet m) ∧
      IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) *
        cThreeAt (m + 1) (numQuartic (N k)) α (simplexPoint y)) (simplexSet m) := by
    intro k
    set p : Fin (m + 1) → Fin 4 → ℝ := fun i => cs i • k
    obtain ⟨Qg, hq, hBQ, hQg⟩ := good_of_poly (n := m + 1) (by omega) (hpoly k) (hαd ▸ hB k)
    have hQe : Qg.eval = (numQuartic (N k)).eval :=
      hQg.trans (eval_numQuartic ⟨Qg, hQg⟩).symm
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
    simp only [dec_cOneAt_congr (m + 1) α p _ hQe, dec_cTwoAt_congr (m + 1) α p _ hQe,
      dec_cThreeAt_congr (m + 1) α _ hQe] at k1 k2 k3
    exact ⟨k1, k2, k3⟩
  -- the pointwise bound
  set D := 2 * d + 8 with hD
  obtain ⟨Λ, hΛ, hpt⟩ := dec_twoReg_point (n := m + 1) (by omega) α γ₀ cs Ms N hk
    (fun k => by obtain ⟨Q, hQe, -⟩ := hQ₁ k; exact ⟨Q, hQe⟩) hδ hS₀ hSl hS hSc hnode
  -- the majorant rate at the nodes
  choose Qf₁ hQf₁e hQf₁d hQf₁q using hQ₁
  choose Qf₀ hQf₀e hQf₀d hQf₀q using hQ₀
  set kk : Fin (D + 1) → Fin 4 → ℝ := fun l => decKNode cc Sl S D l with hkk
  set Q₁ : Fin (D + 1) → LoopQuartic := fun l => Qf₁ (kk l)
  set Q₀ : Fin (D + 1) → LoopQuartic := fun l => Qf₀ (kk l)
  obtain ⟨B₁, hB₁⟩ := lqBdd_finite Q₁
  obtain ⟨B₀, hB₀⟩ := lqBdd_finite Q₀
  have hn : m + 1 = 7 ∨ (m + 1 = 6 ∧ ∀ l, (Q₁ l).quart = 0 ∧ (Q₁ l).quart = 0 ∧
      (Q₀ l).quart = 0) := by
    rcases hm with h5 | h6
    · refine Or.inr ⟨by omega, fun l => ?_⟩
      have q₁ : (Q₁ l).quart = 0 := (hQf₁q _).resolve_left (by omega)
      exact ⟨q₁, q₁, (hQf₀q _).resolve_left (by omega)⟩
    · exact Or.inl (by omega)
  have hkb : ∀ l, ‖kk l‖ ≤ ∑ l', ‖kk l'‖ := fun l =>
    Finset.single_le_sum (f := fun l => ‖kk l‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)
  have hMb : ∀ (_ : Fin (D + 1)) l, |Ms l| ≤ ∑ j, |Ms j| := fun _ l =>
    Finset.single_le_sum (f := fun j => |Ms j|) (fun j _ => abs_nonneg _) (Finset.mem_univ l)
  obtain ⟨Cm, hCm⟩ := dec_maj_rate (n := m + 1) (by omega) α γ₀ huniq hrow3 (by rwa [hf10])
    (by obtain ⟨l, hl⟩ := hR1; exact ⟨l, (castLoopMatrix_eq_row10_iff _ l).2 hl⟩)
    (by rwa [hf01])
    (by obtain ⟨l, hl⟩ := hR0; exact ⟨l, (castLoopMatrix_eq_row01_iff _ l).2 hl⟩)
    cs kk (fun _ => Ms) Q₁ Q₁ Q₀ hB₁ hB₁ hB₀ (fun _ => rfl)
    (fun l => (hQf₀e _).trans (hQf₁e _).symm) (fun l => (hQf₁d _).mono hd₁)
    (fun h l => (hQf₁d _).mono (hd11 (by rwa [hf10] at h))) (fun l => (hQf₀d _).mono hd₀)
    (fun h l => (hQf₀d _).mono (hd01 (by rwa [hf01] at h))) hn hkb hMb hc₀
    (fun l z hz _ hU => hV (kk l) (hnode l).1.le z hz hU)
  refine ⟨‖-((π : ℂ) ^ 4)‖ * (Λ * ∑ _l : Fin (D + 1), Cm), fun t ht => ?_⟩
  have hMu : Function.update Ms γ₀ 0 = Ms := by
    rw [Function.update_eq_self_iff]; exact hMs.symm
  have hQe : ∀ l, (Q₁ l).eval = (numQuartic (N (kk l))).eval := fun l =>
    (hQf₁e _).trans (eval_numQuartic ⟨_, hQf₁e (kk l)⟩).symm
  -- integrability of the node majorant
  have hIl : ∀ l, IntegrableOn (fun y => decMajF (m + 1) (numQuartic (N (kk l))) α
      (fun i => cs i • kk l) Ms γ₀ t (simplexPoint y)) (simplexSet m) := fun l => by
    obtain ⟨k1, k2, k3⟩ := hcoef (kk l)
    exact integrableOn_decMajF (lt_min hc₀ ht) k1 k2 k3 (hVt (kk l) (hnode l).1.le t ht)
  have hImaj : Integrable (fun x => Λ * decNodeMaj (m + 1) N α cs Ms γ₀ cc Sl S D t
      (simplexPoint x)) (volume.restrict (simplexSet m)) := by
    refine Integrable.const_mul ?_ Λ
    simp only [decNodeMaj]
    exact integrable_finsetSum _ fun l _ => hIl l
  -- the integral
  have hdot : ∀ s ∈ Icc (-δ) δ, S₀ ≤ Minkowski.dot (tiltVec cc s) (tiltVec cc s) := fun s hs => by
    rw [dot_tiltVec (by linarith [hs.2])]; linarith [hs.1]
  have hFm : ∀ s ∈ Icc (-δ) δ, AEStronglyMeasurable (fun x => (simplexPoint x γ₀ : ℂ) *
      paramAtV (m + 1) (numQuartic (N (tiltVec cc s))) α (fun i => cs i • tiltVec cc s)
        (simplexPoint x) (symanzikV α (fun i => cs i • tiltVec cc s) Ms (simplexPoint x) +
          simplexPoint x γ₀ * t)) (volume.restrict (simplexSet m)) := fun s hs => by
    obtain ⟨k1, k2, k3⟩ := hcoef (tiltVec cc s)
    exact (integrableOn_pieceF (lt_min hc₀ ht) k1 k2 k3
      (hVt (tiltVec cc s) (hdot s hs) t ht)).aestronglyMeasurable
  have hF : ∀ᵐ x ∂(volume.restrict (simplexSet m)), DecTwoReg (-δ) δ
      (fun s => (simplexPoint x γ₀ : ℂ) *
        paramAtV (m + 1) (numQuartic (N (tiltVec cc s))) α (fun i => cs i • tiltVec cc s)
          (simplexPoint x) (symanzikV α (fun i => cs i • tiltVec cc s) Ms (simplexPoint x) +
            simplexPoint x γ₀ * t))
      (Λ * decNodeMaj (m + 1) N α cs Ms γ₀ cc Sl S D t (simplexPoint x))
      (Λ * decNodeMaj (m + 1) N α cs Ms γ₀ cc Sl S D t (simplexPoint x))
      (Λ * decNodeMaj (m + 1) N α cs Ms γ₀ cc Sl S D t (simplexPoint x)) := by
    refine ae_restrict_of_forall_mem (measurableSet_simplexSet m) fun x hx => ?_
    have hz := simplexPoint_mem_stdSimplex hx
    by_cases hU : symanzikU α (simplexPoint x) = 0
    · have h0 : decNodeMaj (m + 1) N α cs Ms γ₀ cc Sl S D t (simplexPoint x) = 0 := by
        simp only [decNodeMaj]
        exact Finset.sum_eq_zero fun l _ => decMajF_eq_zero_of_U _ _ _ _ _ hU
      rw [h0, mul_zero]
      exact DecTwoReg.zero.congr fun s _ => by simp [paramAtV, hU]
    · have h0 : 0 ≤ symanzikV α (fun i => cs i • tiltVec cc S₀) Ms (simplexPoint x) := by
        have := hV (tiltVec cc S₀) (by rw [dot_tiltVec (by linarith)]) _ hz.1 hU
        exact (mul_nonneg hc₀.le (Finset.sum_nonneg fun l _ => hz.1 l)).trans this
      exact hpt _ hz.1 hU h0 t ht.le ((lt_min hc₀ ht).trans_le
        (hVt (tiltVec cc (-δ)) (hdot _ ⟨le_rfl, by linarith⟩) t ht x hx hU))
  have hI := DecTwoReg.integral hImaj hImaj hImaj hFm hF
  refine ⟨_, _, _, (hI.const_mul (-((π : ℂ) ^ 4))).congr fun s _ => ?_, ?_⟩
  · simp only [pairDens, hMu]
    rfl
  · rw [integral_const_mul]
    simp only [decNodeMaj]
    rw [integral_finsetSum _ fun l _ => hIl l, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    have e : (fun y => decMajF (m + 1) (Q₁ l) α (fun i => cs i • kk l) Ms γ₀ t (simplexPoint y)) =
        fun y => decMajF (m + 1) (numQuartic (N (kk l))) α (fun i => cs i • kk l) Ms γ₀ t
          (simplexPoint y) :=
      funext fun y => decMajF_congr (m + 1) (Q₁ l) α _ _ (hQe l) Ms γ₀ t
    have h := hCm l t ht (by rw [e]; exact hIl l)
    rw [e] at h
    have hc := norm_nonneg (-((π : ℂ) ^ 4))
    calc t * (‖-((π : ℂ) ^ 4)‖ * (Λ * ∫ x in simplexSet m, decMajF (m + 1)
          (numQuartic (N (kk l))) α (fun i => cs i • kk l) Ms γ₀ t (simplexPoint x)))
        = ‖-((π : ℂ) ^ 4)‖ * (Λ * (t * ∫ x in simplexSet m, decMajF (m + 1)
          (numQuartic (N (kk l))) α (fun i => cs i • kk l) Ms γ₀ t (simplexPoint x))) := by
          ring
      _ ≤ ‖-((π : ℂ) ^ 4)‖ * (Λ * Cm) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hΛ) hc

end Piece

/-! ### The interpolation nodes of a short tilted segment -/

/-- **The nodes of the tilted segment over `[-δ, δ]` at `c = 1`** have squares in `(-3, δ]` when
`δ (D + 1) ≤ 1/4` and `δ ≤ 1/4`. -/
theorem dec_kNode_dot {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (D : ℕ)
    (hδD : δ * (D + 1) ≤ 1 / 4) (l : Fin (D + 1)) :
    -3 < Minkowski.dot (decKNode 1 (-δ) δ D l) (decKNode 1 (-δ) δ D l) ∧
      Minkowski.dot (decKNode 1 (-δ) δ D l) (decKNode 1 (-δ) δ D l) ≤ δ := by
  set lo := Real.sqrt (2 * 1 ^ 2 - δ) with hlo
  set hi := Real.sqrt (2 * 1 ^ 2 - -δ) with hhi
  set u := node D l with hu
  have hD : (0 : ℝ) < D + 1 := by positivity
  have hu0 : 0 ≤ u := div_nonneg (Nat.cast_nonneg _) hD.le
  have hlD : (l : ℝ) + 1 ≤ D + 1 := by exact_mod_cast l.isLt
  have hu1 : u + 1 / (D + 1) ≤ 1 := by
    rw [hu, node, ← add_div, div_le_one hD]; exact hlD
  have hu1' : u < 1 := by
    have : 0 < 1 / (D + 1 : ℝ) := by positivity
    linarith
  have hlo2 : lo ^ 2 = 2 - δ := by rw [hlo, Real.sq_sqrt (by linarith)]; ring
  have hhi2 : hi ^ 2 = 2 + δ := by rw [hhi, Real.sq_sqrt (by linarith)]; ring
  have hlo0 : 0 ≤ lo := Real.sqrt_nonneg _
  have hhi0 : 0 ≤ hi := Real.sqrt_nonneg _
  have hlo1 : 1 ≤ lo := by nlinarith
  have hhi1 : hi ≤ 3 / 2 := by nlinarith
  have hlohi : lo ≤ hi := Real.sqrt_le_sqrt (by linarith)
  have hsq : (hi - lo) * (hi + lo) = 2 * δ := by
    rw [show (hi - lo) * (hi + lo) = hi ^ 2 - lo ^ 2 by ring, hhi2, hlo2]; ring
  have hdiff : hi - lo ≤ δ := by nlinarith
  -- `tpar u ∈ [0, D + 1]`
  have hw : 1 / (D + 1) ≤ 1 - u ^ 2 := by nlinarith
  have hwp : 0 < 1 - u ^ 2 := lt_of_lt_of_le (by positivity) hw
  have ht0 : 0 ≤ tpar u := div_nonneg hu0 hwp.le
  have ht1 : tpar u ≤ D + 1 := by
    rw [tpar, div_le_iff₀ hwp]
    have : 1 ≤ (D + 1) * (1 - u ^ 2) := by
      have := mul_le_mul_of_nonneg_left hw hD.le
      rwa [mul_one_div_cancel hD.ne'] at this
    nlinarith
  have hk : decKNode 1 (-δ) δ D l = ![(lo + hi) / 2 + tpar u * (3 / 4 * (hi - lo)), 0, 1, 1] := by
    rw [decKNode, lineK_tilt]
  rw [hk]
  simp only [Minkowski.dot_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  set a := (lo + hi) / 2 + tpar u * (3 / 4 * (hi - lo)) with hadef
  have ha0 : lo ≤ a := by
    have : 0 ≤ tpar u * (3 / 4 * (hi - lo)) := mul_nonneg ht0 (by linarith)
    rw [hadef]; linarith
  have ha1 : a ≤ 3 / 2 + 3 / 16 := by
    have e1 : tpar u * (3 / 4 * (hi - lo)) ≤ (D + 1) * (3 / 4 * δ) :=
      mul_le_mul ht1 (by linarith) (by linarith) hD.le
    rw [hadef]; nlinarith
  have ha2 : a * a ≤ (3 / 2 + 3 / 16) * (3 / 2 + 3 / 16) :=
    mul_self_le_mul_self (hlo0.trans ha0) ha1
  have ha3 : lo * lo ≤ a * a := mul_self_le_mul_self hlo0 ha0
  have hlo3 : lo * lo = 2 - δ := by rw [← hlo2]; ring
  constructor
  · norm_num
    linarith
  · norm_num
    linarith

/-! ### The class input -/

/-- **`DecVTwo` from `DecPieceTwo`** of the class density (with `q = 0`). -/
theorem dec_vTwo_of_pieceTwo
    {A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {base : Fin 5 → Fin 2 → ℤ} {cv : Fin 5 → ℝ} {F : Type} [Fintype F]
    {Φ : Lepton.Flavors F} {e m₀ c δ : ℝ}
    (h : DecPieceTwo c δ fun t k => vDens A base cv Φ e m₀ t k 2 3) :
    DecVTwo A base cv Φ e m₀ c δ := by
  obtain ⟨B, hB⟩ := h
  refine ⟨max B 0, 0, le_max_right _ _, le_rfl, by norm_num, fun s h hs hs2 t ht => ?_⟩
  obtain ⟨M, L, K, hr, hK⟩ := hB t ht
  have h2 := hr.two s h (abs_le.mp hs) (abs_le.mp hs2)
  have hKt : K ≤ max B 0 * (t ^ ((0 : ℝ) / 2) + t ^ (-((0 : ℝ) / 2))) / t := by
    rw [zero_div, neg_zero, Real.rpow_zero, le_div_iff₀ ht]
    have := le_max_left B 0
    have := le_max_right B 0
    nlinarith [hr.nonneg.2.2]
  exact h2.trans (mul_le_mul_of_nonneg_right hKt (sq_nonneg h))

end QED.GradedProof.RPi4

end
