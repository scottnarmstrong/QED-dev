/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2RealPiece
public import QED.GradedProof.SE2RealDecomp
public import QED.GradedProof.SE2FormV

/-!
# The reality class obligation for `V`

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `SEReal`; the reality counterpart of `QED/GradedProof/SE2FormV.lean`.

The numerators of `V` are `κ C K` times self-energy chains `seChain(m - k̸₀, D[T])`, with real
`κ = (2π)⁻⁸`, `K = (M₁² - m²)(M₂² - m²)`, the coupling `C = (ie)⁴ (1/i)⁵ = -ie⁴` (`conj_vC`),
and real photon tensors `D[T]` (`T` the trace of a `♯`-fixed loop chain, or `tr(γ^σ γ^τ)`). So
`N♯ = -N` (`sharp_numV1`, `sharp_numV2`), each piece has a limit with phase `-1`
(`hasSharpLim_vPiece`), and so has the class (`classSharp_repV`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.SE2Real

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Integration.TwoLoop (lineDenom castLoopMatrix RefinedBound IntNoSubdivergenceRefined
  symanzikU symanzikV noSubdivergenceRefined_castLoopMatrix_iff)
open QED.GradedProof.SE2

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S S' : Matrix (Fin 4) (Fin 4) ℂ}

/-! ### The phases -/

theorem conj_vκ : starRingEnd ℂ vκ = vκ := by
  simp only [vκ, map_inv₀, Complex.conj_ofReal]

theorem conj_vK (Q : Params) : starRingEnd ℂ (vK Q) = vK Q := by
  simp only [vK, Complex.conj_ofReal]

theorem conj_vC (Q : Params) : starRingEnd ℂ (vC Q) = -vC Q := by
  simp only [vC, map_mul, map_pow, map_div₀, map_one, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem conj_vκCK (Q : Params) :
    starRingEnd ℂ (vκ * vC Q * vK Q) = -(vκ * vC Q * vK Q) := by
  rw [map_mul, map_mul, conj_vκ, conj_vC, conj_vK]
  ring

/-! ### The numerators -/

theorem conj_trSE (u v : Fin 4 → ℝ) (σ τ : Fin 4) :
    starRingEnd ℂ (trSE 0 u v σ τ) = trSE 0 u v σ τ :=
  conj_trace_of_sharp (by simp only [sharp_mul, sharp_gamma, sharp_electronNumerator])

theorem conj_trG (σ τ : Fin 4) : starRingEnd ℂ (trG σ τ) = trG σ τ :=
  conj_trace_of_sharp (by simp only [sharp_mul, sharp_gamma])

theorem conj_DV (Q : Params) {T : Fin 4 → Fin 4 → ℂ} (hT : ∀ a b, starRingEnd ℂ (T a b) = T a b)
    (a b : Fin 4) : starRingEnd ℂ (DV Q T a b) = DV Q T a b := by
  simp only [DV, map_sum, map_mul, Complex.conj_ofReal, hT]

theorem sharp_numV1 (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    sharp (numV1 Q p ℓ) = (-1 : ℂ) • numV1 Q p ℓ := by
  rw [numV1_eq, sharp_smul, conj_vκCK, sharp_add, sharp_smul, Complex.conj_ofReal,
    sharp_seChain (sharp_electronNumerator _ _) (conj_DV Q (conj_trSE _ _)),
    sharp_seChain (sharp_electronNumerator _ _) (conj_DV Q conj_trG), smul_smul]
  ring_nf

theorem sharp_numV2 (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    sharp (numV2 Q p ℓ) = (-1 : ℂ) • numV2 Q p ℓ := by
  rw [numV2_eq, sharp_smul, map_neg, conj_vκCK,
    sharp_seChain (sharp_electronNumerator _ _) (conj_DV Q conj_trG), smul_smul]
  ring_nf

/-! ### The pieces and the class `V` -/

/-- **A piece of `V` with a `♯`-symmetric numerator has a `♯`-symmetric limit.** -/
theorem hasSharpLim_vPiece {n : ℕ} (hn : 7 ≤ n) (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ)
    {E : Finset (Fin (n + 1))} (hcrit : IntNoSubdivergenceRefined 2 E fun i => baseA (sh i))
    (F : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hpoly : ∀ p i j, IsLoopPoly 2 4 fun ℓ => F p ℓ i j)
    (hB : ∀ p i j, RefinedBound (castLoopMatrix fun i => baseA (sh i)) E 4 fun ℓ => F p ℓ i j)
    (hcov : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Matrix (Fin 4) (Fin 4) ℂ),
      IsSpinLift L S S' → ∀ p ℓ, S * F (L *ᵥ p) (loopAct L ℓ) * S' = F p ℓ)
    {c : ℂ} (hsharp : ∀ p ℓ, sharp (F p ℓ) = c • F p ℓ)
    {m m₀ ν : ℝ}
    (hm0 : 0 < m₀) (hmm : m₀ ≤ m) (hν0 : 0 < ν) (hν2 : ν ≤ 2 * m₀)
    (h0 : ∀ i, sh i = 0 → m ≤ Ms i) (h12 : ∀ i, sh i = 1 ∨ sh i = 2 → m₀ ≤ Ms i)
    (h34 : ∀ i, sh i = 3 ∨ sh i = 4 → ν ≤ Ms i) :
    HasSharpLim (m + ν) c fun ε p i j =>
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => F p ℓ i j * ∏ k,
        (lineDenom (castLoopMatrix fun i => baseA (sh i)) (fun i => basePP p (sh i)) Ms ε k
          ℓ)⁻¹) := by
  have hm : 0 < m := hm0.trans_le hmm
  have hc : 0 < min (m₀ ^ 2) (ν ^ 2) := lt_min (by positivity) (by positivity)
  have hMc : ∀ i, min (m₀ ^ 2) (ν ^ 2) ≤ Ms i ^ 2 := by
    intro i
    rcases (by decide : ∀ j : Fin 5, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) (sh i) with
      h | h | h | h | h
    · exact (min_le_left _ _).trans (pow_le_pow_left₀ hm0.le (hmm.trans (h0 i h)) 2)
    · exact (min_le_left _ _).trans (pow_le_pow_left₀ hm0.le (h12 i (Or.inl h)) 2)
    · exact (min_le_left _ _).trans (pow_le_pow_left₀ hm0.le (h12 i (Or.inr h)) 2)
    · exact (min_le_right _ _).trans (pow_le_pow_left₀ hν0.le (h34 i (Or.inl h)) 2)
    · exact (min_le_right _ _).trans (pow_le_pow_left₀ hν0.le (h34 i (Or.inr h)) 2)
  have hpp : ∀ p : Fin 4 → ℝ, (fun i => basePP p (sh i)) = fun i => aVc (sh i) • p :=
    fun p => funext fun i => basePP_eq p (sh i)
  let D : SEData :=
    { m := n
      α := castLoopMatrix fun i => baseA (sh i)
      cs := fun i => aVc (sh i)
      M := Ms
      E := E
      hm := by omega
      hcrit := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit }
  let P : SEPiece (m + ν) :=
    { D := D
      N := F
      hQ := fun p i j => by
        obtain ⟨Q', hQ'⟩ := (hpoly p i j).exists_loopQuartic
        exact ⟨Q', ⟨Or.inl hn, hQ' ▸ hB p i j⟩, hQ'⟩
      hV := fun p hp => ⟨_, min_one_mul_pos (by positivity) hc hp, fun z hz hz1 hU => by
        have e := symanzikV_vShape_ge sh Ms hm hν0 hν2 h0 h12 h34 hc hMc hp hz hz1 hU
        rw [hpp] at e
        exact e⟩
      hcov := hcov }
  refine SEPiece.hasSharpLim P hsharp (h := fun _ => 1) (h₀ := 1) (by simp)
    fun p _ i j => Eventually.of_forall fun ε => ?_
  show _ = 1 * QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => F p ℓ i j *
    ∏ k, (lineDenom (castLoopMatrix fun i => baseA (sh i)) (fun i => aVc (sh i) • p) Ms ε k
      ℓ)⁻¹)
  rw [one_mul, ← hpp]

theorem classSharp_repV : ClassSharp repV := by
  intro Q hQ m₀ ν hm0 hmm hM1 hM2 hν0 hν hν2
  have hγ : ν ≤ Q.mγ := hν.trans (min_le_left _ _)
  have hΛ : ν ≤ Q.Λ := hν.trans (min_le_right _ _)
  obtain ⟨c1, c2, c3, c4, c5⟩ := crit_sh
  obtain ⟨a1, b1, d1⟩ := cond_sh1 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a2, b2, d2⟩ := cond_sh2 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a3, b3, d3⟩ := cond_sh3 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a4, b4, d4⟩ := cond_sh4 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a5, b5, d5⟩ := cond_sh5 Q hM1 hM2 hmm hγ hΛ
  have p1 := fun p i j => isLoopPoly_vF1 Q p i j
  have p2 := fun p i j => isLoopPoly_vF2 Q p i j
  have cv1 := fun L S S' (h : IsSpinLift L S S') p ℓ => cov_numV1 Q h p ℓ
  have cv2 := fun L S S' (h : IsSpinLift L S S') p ℓ => cov_numV2 Q h p ℓ
  have s1 := sharp_numV1 Q
  have s2 := sharp_numV2 Q
  have h1 := hasSharpLim_vPiece (by norm_num) sh1 (ms1 Q) c1 (numV1 Q) p1
    (fun p i j => refinedBound_vF1 Q p i j sh1 rfl rfl rfl) cv1 s1
    hm0 hmm hν0 hν2 a1 b1 d1
  have h2 := hasSharpLim_vPiece (by norm_num) sh2 (ms2 Q) c2 (numV1 Q) p1
    (fun p i j => refinedBound_vF1 Q p i j sh2 rfl rfl rfl) cv1 s1
    hm0 hmm hν0 hν2 a2 b2 d2
  have h3 := hasSharpLim_vPiece (by norm_num) sh3 (ms3 Q) c3 (numV1 Q) p1
    (fun p i j => refinedBound_vF1 Q p i j sh3 rfl rfl rfl) cv1 s1
    hm0 hmm hν0 hν2 a3 b3 d3
  have h4 := hasSharpLim_vPiece (by norm_num) sh4 (ms4 Q) c4 (numV2 Q) p2
    (fun p i j => refinedBound_vF2 Q p i j sh4 rfl) cv2 s2
    hm0 hmm hν0 hν2 a4 b4 d4
  have h5 := hasSharpLim_vPiece (by norm_num) sh5 (ms5 Q) c5 (numV2 Q) p2
    (fun p i j => refinedBound_vF2 Q p i j sh5 rfl) cv2 s2
    hm0 hmm hν0 hν2 a5 b5 d5
  refine ((((h1.add h2).add h3).add h4).add h5).congr fun p _ α β => ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (contractionValue₂_repV_eq hQ.pv₁ hQ.pv₂ hε p α β).symm

end QED.GradedProof.SE2Real

end
