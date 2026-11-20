/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4JointBdd
public import QED.GradedProof.RPi4PairDens
public import QED.GradedProof.RPi4LightVP

/-!
# (R-Π₄) step L6d: the heavy-photon rate of one piece of a vacuum-polarization class

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), instantiation of the sector
analysis. The photon-mass density `pairDens` of a merged piece of a vacuum-polarization shape
(photon line last) satisfies `‖t · pairDens(t, k(u)) - L(u)‖ ≤ C t^{-1/2}` for `t ≥ 1`, uniformly
along a segment `k(u) = lineK k₀ w u`, `|u| ≤ 1/2`, of momenta below threshold
(`heavyRate_vpPiece`). It is `QED.GradedProof.RPi4.piece_rate` with:

* the numerators along the segment given by the joint quartics of node quartics of bounded degree
  along each loop (`lqBdd_jointQuartic`, `loopDegLe_jointQuartic`, `quart_jointQuartic`);
* the lower bound `V₀ ≥ c₀ · ferSum` from P0 (`symanzikV_vp_ge_fermion`);
* the integrability of the collapsed integrand at every `t ≥ 1` from the integrable coefficients
  of the doubled data (`integrableOn_mul_of_dbl`, `integrableOn_pieceF`).

`HeavyRate k₀ w D` names the conclusion; it is closed under sums and constant multiples.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.PauliZeroLimit
open QED.GradedProof.WI2 (dbl)
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex)
open QED.TwoLoop.Bridge (IsLoopPoly)

/-! ### The heavy-photon rate along a segment -/

/-- **The heavy-photon rate** of a photon-mass density `D t k` along the segment `lineK k₀ w`:
there are `C` and limits `L u` with `‖t D(t, k(u)) - L(u)‖ ≤ C t^{-1/2}` for `t ≥ 1`,
`|u| ≤ 1/2`. -/
def HeavyRate (k₀ w : Fin 4 → ℝ) (D : ℝ → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ C : ℝ, ∃ L : ℝ → ℂ, ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ t : ℝ, 1 ≤ t →
    ‖(t : ℂ) * D t (lineK k₀ w u) - L u‖ ≤ C * t ^ (-(1 / 2) : ℝ)

namespace HeavyRate

variable {k₀ w : Fin 4 → ℝ} {D D' : ℝ → (Fin 4 → ℝ) → ℂ}

theorem add (h : HeavyRate k₀ w D) (h' : HeavyRate k₀ w D') :
    HeavyRate k₀ w fun t k => D t k + D' t k := by
  obtain ⟨C, L, hC⟩ := h
  obtain ⟨C', L', hC'⟩ := h'
  refine ⟨C + C', fun u => L u + L' u, fun u hu t ht => ?_⟩
  have e : (t : ℂ) * (D t (lineK k₀ w u) + D' t (lineK k₀ w u)) - (L u + L' u) =
      ((t : ℂ) * D t (lineK k₀ w u) - L u) + ((t : ℂ) * D' t (lineK k₀ w u) - L' u) := by ring
  rw [e, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC u hu t ht) (hC' u hu t ht))

theorem const_mul (h : HeavyRate k₀ w D) (r : ℂ) : HeavyRate k₀ w fun t k => r * D t k := by
  obtain ⟨C, L, hC⟩ := h
  refine ⟨‖r‖ * C, fun u => r * L u, fun u hu t ht => ?_⟩
  have e : (t : ℂ) * (r * D t (lineK k₀ w u)) - r * L u =
      r * ((t : ℂ) * D t (lineK k₀ w u) - L u) := by ring
  rw [e, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC u hu t ht) (norm_nonneg _)

theorem zero : HeavyRate k₀ w fun _ _ => 0 :=
  ⟨0, fun _ => 0, fun _ _ t _ => by simp⟩

theorem sum {ι : Type*} (s : Finset ι) {D : ι → ℝ → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, HeavyRate k₀ w (D i)) : HeavyRate k₀ w fun t k => ∑ i ∈ s, D i t k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : HeavyRate k₀ w fun _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem congr (h : HeavyRate k₀ w D)
    (e : ∀ u : ℝ, |u| ≤ 1 / 2 → ∀ t : ℝ, 1 ≤ t → D t (lineK k₀ w u) = D' t (lineK k₀ w u)) :
    HeavyRate k₀ w D' := by
  obtain ⟨C, L, hC⟩ := h
  exact ⟨C, L, fun u hu t ht => by rw [← e u hu t ht]; exact hC u hu t ht⟩

end HeavyRate

/-! ### Rows of a cast loop matrix -/

theorem castLoopMatrix_eq_row10_iff {n : ℕ} (f : Fin (n + 1) → Fin 2 → ℤ) (l : Fin (n + 1)) :
    castLoopMatrix f l = ![1, 0] ↔ f l = ![1, 0] := by
  constructor
  · intro h
    funext s
    have := congrFun h s
    fin_cases s <;> simp_all [castLoopMatrix]
  · intro h
    funext s
    fin_cases s <;> simp [castLoopMatrix, h]

theorem castLoopMatrix_eq_row01_iff {n : ℕ} (f : Fin (n + 1) → Fin 2 → ℤ) (l : Fin (n + 1)) :
    castLoopMatrix f l = ![0, 1] ↔ f l = ![0, 1] := by
  constructor
  · intro h
    funext s
    have := congrFun h s
    fin_cases s <;> simp_all [castLoopMatrix]
  · intro h
    funext s
    fin_cases s <;> simp [castLoopMatrix, h]

theorem norm_lineK_le {k₀ w : Fin 4 → ℝ} {u : ℝ} (hu : |u| ≤ 1 / 2) :
    ‖lineK k₀ w u‖ ≤ ∑ ν, (|k₀ ν| + |w ν|) :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => by
    rw [Real.norm_eq_abs]; exact norm_lineK_apply_le hu μ

/-! ### One piece -/

section Piece

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])

include hflow hrow hrow4

/-- **The heavy-photon rate of one merged piece of a vacuum-polarization shape.** The doubled
shape `sh` has its two photon lines last; the merged density is `pairDens` with the photon line
`Fin.last m` of mass `0`. The numerator `N k` is polynomial of degree `d` in `k`, and at every
`k` it has representatives of degree `≤ d₁` along loop `1` and `≤ d₀` along loop `0` (without
quartic part for `m = 5`); the degrees are `≤ 3`, and `≤ 1` when the corresponding face block of
the merged shape has two lines. -/
theorem heavyRate_vpPiece {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
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
    {k₀ w : Fin 4 → ℝ} {S₀ : ℝ} (hS₀ : -(2 * m₀) ^ 2 < S₀)
    (hseg : ∀ u : ℝ, |u| ≤ 1 / 2 → S₀ ≤ Minkowski.dot (lineK k₀ w u) (lineK k₀ w u)) :
    HeavyRate k₀ w fun t k => pairDens (N k)
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
  -- the family: the segment
  let ι := {u : ℝ // |u| ≤ 1 / 2}
  set kk : ι → Fin 4 → ℝ := fun s => lineK k₀ w s.1 with hkk
  set F : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ := fun u ℓ => N (lineK k₀ w u) ℓ with hF_def
  have hF : IsUPoly (2 * d) fun ℓ u => wt u ^ d * F u ℓ := fun ℓ => by
    have h := isUPoly_eval_of_isLoopPoly (hk ℓ) (ι := Unit)
      (ℓ := fun _ u _ => lineK k₀ w u) fun _ ν => by
        simpa using isUPoly_lineK (ι := Unit) 1 k₀ w ν
    exact h ()
  have hIoo : ∀ s : ι, s.1 ∈ Ioo (-1 : ℝ) 1 := fun s => by
    have := abs_le.1 s.2
    exact ⟨by linarith, by linarith⟩
  choose Qf₁ hQf₁e hQf₁d hQf₁q using hQ₁
  choose Qf₀ hQf₀e hQf₀d hQf₀q using hQ₀
  set Qk₁ : Fin (2 * d + 1) → LoopQuartic := fun j => Qf₁ (lineK k₀ w (node (2 * d) j))
  set Qk₀ : Fin (2 * d + 1) → LoopQuartic := fun j => Qf₀ (lineK k₀ w (node (2 * d) j))
  set Q₁ : ι → LoopQuartic := fun s => jointQuartic (2 * d) d Qk₁ s.1 with hQ₁_def
  set Q₀ : ι → LoopQuartic := fun s => jointQuartic (2 * d) d Qk₀ s.1 with hQ₀_def
  have hQ₁e : ∀ s, (Q₁ s).eval = N (kk s) := fun s =>
    eval_jointQuartic hF (fun j => hQf₁e _) (hIoo s)
  have hQ₀e : ∀ s, (Q₀ s).eval = N (kk s) := fun s =>
    eval_jointQuartic hF (fun j => hQf₀e _) (hIoo s)
  obtain ⟨B₁, hB₁⟩ := lqBdd_jointQuartic (2 * d) d Qk₁
  obtain ⟨B₀, hB₀⟩ := lqBdd_jointQuartic (2 * d) d Qk₀
  have hD₁ : ∀ s, LoopDegLe 1 d₁ (Q₁ s) := fun s =>
    loopDegLe_jointQuartic (2 * d) d (fun j => hQf₁d _) s.1
  have hD₀ : ∀ s, LoopDegLe 0 d₀ (Q₀ s) := fun s =>
    loopDegLe_jointQuartic (2 * d) d (fun j => hQf₀d _) s.1
  have hn : m + 1 = 7 ∨ (m + 1 = 6 ∧ ∀ s, (Q₁ s).quart = 0 ∧ (Q₁ s).quart = 0 ∧
      (Q₀ s).quart = 0) := by
    rcases hm with h5 | h6
    · refine Or.inr ⟨by omega, fun s => ?_⟩
      have q₁ : (Q₁ s).quart = 0 := quart_jointQuartic (2 * d) d
        (fun j => (hQf₁q _).resolve_left (by omega)) s.1
      have q₀ : (Q₀ s).quart = 0 := quart_jointQuartic (2 * d) d
        (fun j => (hQf₀q _).resolve_left (by omega)) s.1
      exact ⟨q₁, q₁, q₀⟩
    · exact Or.inl (by omega)
  -- bounds of the momenta and masses; the lower bound of `V₀`
  set Kk := ∑ ν, (|k₀ ν| + |w ν|)
  have hkb : ∀ s : ι, ‖kk s‖ ≤ Kk := fun s => norm_lineK_le s.2
  have hMb : ∀ (_ : ι) l, |Ms l| ≤ ∑ j, |Ms j| := fun _ l =>
    Finset.single_le_sum (f := fun j => |Ms j|) (fun j _ => abs_nonneg _) (Finset.mem_univ l)
  set c₀ := min 1 (1 + S₀ / (2 * m₀) ^ 2) * m₀ ^ 2 with hc₀_def
  have hT : 0 < (2 * m₀) ^ 2 := by positivity
  have hc₀ : 0 < c₀ := by
    refine mul_pos (lt_min one_pos ?_) (by positivity)
    have : -1 < S₀ / (2 * m₀) ^ 2 := by rw [lt_div_iff₀ hT]; linarith
    linarith
  have hferF : ∀ z : Fin (m + 1) → ℝ, ferSum α z =
      ∑ i ∈ Finset.univ.filter (fun i => sh (Fin.castSucc i) ≠ 4), z i := fun z => by
    simp only [ferSum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ne, huniq l, hne l]
  have hV : ∀ (s : ι) (z : Fin (m + 1) → ℝ), (∀ l, 0 ≤ z l) → ∑ l, z l = 1 →
      symanzikU α z ≠ 0 → c₀ * ferSum α z ≤ symanzikV α (fun i => cs i • kk s) Ms z := by
    intro s z hz _ hU
    have hs := hseg s.1 s.2
    have hP0 := symanzikV_vp_ge_fermion base c y₁ y₂ hflow (fun l : Fin (m + 1) => sh l.castSucc)
      Ms hm₀ hf (k := kk s) (by linarith) hz hU
    rw [← hferF] at hP0
    have hmin : c₀ ≤ min 1 (1 + Minkowski.dot (kk s) (kk s) / (2 * m₀) ^ 2) * m₀ ^ 2 := by
      refine mul_le_mul_of_nonneg_right (min_le_min le_rfl ?_) (by positivity)
      have := div_le_div_of_nonneg_right hs hT.le
      linarith
    have hF0 : 0 ≤ ferSum α z := Finset.sum_nonneg fun l _ => hz l
    exact (mul_le_mul_of_nonneg_right hmin hF0).trans hP0
  -- the rate of `piece_rate`
  obtain ⟨C, L, hC⟩ := piece_rate (n := m + 1) (by omega) α γ₀ huniq hrow3 (by rwa [hf10])
    (by obtain ⟨l, hl⟩ := hR1; exact ⟨l, (castLoopMatrix_eq_row10_iff _ l).2 hl⟩)
    (by rwa [hf01])
    (by obtain ⟨l, hl⟩ := hR0; exact ⟨l, (castLoopMatrix_eq_row01_iff _ l).2 hl⟩)
    cs kk (fun _ => Ms) Q₁ Q₁ Q₀ hB₁ hB₁ hB₀ (fun _ => rfl)
    (fun s => (hQ₀e s).trans (hQ₁e s).symm) (fun s => (hD₁ s).mono hd₁)
    (fun h s => (hD₁ s).mono (hd11 (by rwa [hf10] at h))) (fun s => (hD₀ s).mono hd₀)
    (fun h s => (hD₀ s).mono (hd01 (by rwa [hf01] at h))) hn hkb hMb hc₀ hV
  -- integrability of the collapsed integrand at every `t ≥ 1`
  have hl : sh (Fin.last (m + 1)) = sh (Fin.last m).castSucc := by
    rw [(hsh _).2 (by simp), (hsh _).2 (by simp)]
  have hαd : castLoopMatrix (fun l => base (sh l)) = dbl γ₀ α :=
    comp_eq_dbl sh hl fun r s => (base r s : ℝ)
  have hcrit' : NoSubdivergenceRefined 2 E (dbl γ₀ α) :=
    hαd ▸ (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).2 hcrit
  have hint : ∀ (s : ι) (t : ℝ), 1 ≤ t → IntegrableOn
      (fun x => pieceF (m + 1) (Q₁ s) α (fun i => cs i • kk s) Ms γ₀ t (simplexPoint x))
      (simplexSet m) := by
    intro s t ht
    set p : Fin (m + 1) → Fin 4 → ℝ := fun i => cs i • kk s
    have hpd : (fun l => c (sh l) • kk s) = dbl γ₀ p := comp_eq_dbl sh hl fun r => c r • kk s
    obtain ⟨Qg, hq, hBQ, hQg⟩ := good_of_poly (n := m + 1) (by omega) (hpoly (kk s))
      (hαd ▸ hB (kk s))
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
        have h1 := hV s _ hz.1 hz.2 hU
        rw [ferSum_eq_one_sub huniq hz.2] at h1
        have hzγ := hz.1 γ₀
        have hzγ1 : simplexPoint y γ₀ ≤ 1 := by
          rw [← hz.2]
          exact Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ γ₀)
        have e1 := mul_le_mul_of_nonneg_right (min_le_left c₀ 1) (sub_nonneg.2 hzγ1)
        have e2 := mul_le_mul_of_nonneg_right (min_le_right c₀ 1) hzγ
        have e3 := mul_le_mul_of_nonneg_left ht hzγ
        nlinarith
    refine hIg.congr_fun (fun x _ => ?_) (QED.Integration.Feynman.measurableSet_simplexSet m)
    simp only [pieceF, paramAtV_congr (hQg.trans (hQ₁e s).symm)]
  -- assembly
  refine ⟨π ^ 4 * C, fun u => if h : |u| ≤ 1 / 2 then -((π : ℂ) ^ 4) * L ⟨u, h⟩ else 0,
    fun u hu t ht => ?_⟩
  set s : ι := ⟨u, hu⟩
  have hMu : Function.update Ms γ₀ 0 = Ms := by
    rw [Function.update_eq_self_iff]; exact hMs.symm
  have hpd : pairDens (N (lineK k₀ w u)) α (fun l => c (sh l.castSucc) • lineK k₀ w u) Ms γ₀ t =
      -((π : ℂ) ^ 4) * ∫ x in simplexSet m,
        pieceF (m + 1) (Q₁ s) α (fun i => cs i • kk s) Ms γ₀ t (simplexPoint x) := by
    rw [pairDens_eq (hQ₁e s), hMu]
    rfl
  simp only [hu, dite_true]
  rw [hpd]
  have e : (t : ℂ) * (-((π : ℂ) ^ 4) * ∫ x in simplexSet m,
      pieceF (m + 1) (Q₁ s) α (fun i => cs i • kk s) Ms γ₀ t (simplexPoint x)) -
      -((π : ℂ) ^ 4) * L s = -((π : ℂ) ^ 4) * (t • (∫ x in simplexSet m,
      pieceF (m + 1) (Q₁ s) α (fun i => cs i • kk s) Ms γ₀ t (simplexPoint x)) - L s) := by
    rw [Complex.real_smul]; ring
  rw [e, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC s t ht (hint s t ht)) (by positivity)

end Piece

end QED.GradedProof.RPi4

end
