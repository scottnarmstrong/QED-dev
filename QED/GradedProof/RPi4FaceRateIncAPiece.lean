/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncAGen
public import QED.GradedProof.RPi4FaceIdRayAQPiece

/-!
# (R-Π₄) step L10: (A) for increments of the merged pieces `A_{ij}`, `B_i`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The merged pieces
`QED.GradedProof.RPi4.majDPieceA` (seven lines `(i, j)`) and `QED.GradedProof.RPi4.majDPieceB`
(six lines `i`) of a class numerator satisfy (A) for increments at every photon mass,
`QED.GradedProof.RPi4.FaceRateIncAQPow`, under the hypotheses of the value bound (A) with a power
loss (`QED.GradedProof.RPi4.faceIdRayAQ_pieceA`, `…B`) and the integrability data of the class
(the flow bounds, the rows, the no-subdivergence criterion and the refined bounds of the pieces).

The proofs are those of `faceIdRayAQ_pieceA`, `faceIdRayAQ_pieceB` with the final step
`QED.GradedProof.RPi4.faceIdRayAQ_pow_pairDens` replaced by
`QED.GradedProof.RPi4.faceRateIncAQ_pow_pairDens`; its integrability input along the ray is
`QED.GradedProof.RPi4.integrableOn_pairDensIntegrand` at `k = majRayVec σ`, `σ ≥ 1`, which lies
below threshold (`faceRateIncAQ_dot_ray`).

* `faceRateIncAQ_dot_ray`;
* **`faceRateIncAQ_pieceA`**, **`faceRateIncAQ_pieceB`**.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- The ray momenta `majRayVec σ`, `σ ≥ 1`, lie below the threshold `(2 m₀)²`. -/
theorem faceRateIncAQ_dot_ray (m₀ : ℝ) {σ : ℝ} (hσ : 1 ≤ σ) :
    -(2 * m₀) ^ 2 < Minkowski.dot (majRayVec σ) (majRayVec σ) := by
  rw [dot_majRayVec (by linarith)]
  linarith [sq_nonneg (2 * m₀)]

section Pieces

variable (e : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l)) (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (clB : Fin 5 → Fin 3) (hclB : ∀ r, base r = faceIdRayAQRowZ (clB r)) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (μ ν : Fin 4) {d₀ d₁ : ℕ} (K₂ K₁ K₃ : Fin 3 → Prop) [DecidablePred K₂] [DecidablePred K₁]
  [DecidablePred K₃]
  (hBd : ∀ {n : ℕ} (α : Fin (n + 1) → Fin 2 → ℝ) (cl : Fin (n + 1) → Fin 3),
    (∀ t, α t = faceIdRayAQRow (cl t)) → ∀ (cs : Fin (n + 1) → ℝ) (Q : Fin 3 → LoopQuartic),
      (∀ t, LoopDegLe 0 d₀ (Q t) ∧ LoopDegLe 1 d₁ (Q t)) → FaceIdRayAQBd α cs cl K₂ K₁ K₃ Q)
  (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])

include hA hclB hm₀ hBd hflow hrow hrow4

/-- **(A) for increments of a piece with seven lines `(i, j)`.** -/
theorem faceRateIncAQ_pieceA (hd₀ : loopDegOf base 0 ≤ d₀) (hd₁ : loopDegOf base 1 ≤ d₁)
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (i j : Fin 4) (t₁ t₂ : Fin 7)
    (ht : t₁ ≠ t₂) (hcl : faceIdRayAQClA clB i j t₁ = faceIdRayAQClA clB i j t₂)
    (hcs : c (shA i j t₁.castSucc) ≠ c (shA i j t₂.castSucc)) (j' : Fin 7) (hj' : j' = 1 ∨ j' = 3)
    (c₁ : FaceIdRayAQCheck (faceIdRayAQClA clB i j) (Fin.last 6) t₁ t₂ 2 0)
    (c₂ : FaceIdRayAQCheck (faceIdRayAQClA clB i j) (Fin.last 6) t₁ t₂ 2
      fun t => (if t = 0 then -1 else 0) + (if t = j' then -1 else 0))
    (c₃ : ∀ u, K₂ (faceIdRayAQClA clB i j u) →
      FaceIdRayAQCheck (faceIdRayAQClA clB i j) (Fin.last 6) t₁ t₂ 3
        fun t => if t = u then 2 else 0)
    (c₄ : ∀ u v, K₁ (faceIdRayAQClA clB i j u) → K₃ (faceIdRayAQClA clB i j v) →
      FaceIdRayAQCheck (faceIdRayAQClA clB i j) (Fin.last 6) t₁ t₂ 4
        fun t => (if t = u then 2 else 0) + (if t = v then 2 else 0))
    (hcA : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hBA : ∀ m k a b, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun ℓ => vNum e 0 1 A base c m k ℓ a b) :
    FaceRateIncAQPow (majDPieceA base c (vNum e 0 1 A base c) M X Y μ ν i j) := by
  set α := castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc) with hαdef
  set cl := faceIdRayAQClA clB i j with hcldef
  have hα : ∀ t, α t = faceIdRayAQRow (cl t) :=
    faceIdRayAQ_castLoopMatrix_row _ cl fun t => hclB _
  set cs : Fin 7 → ℝ := fun l => c (shA i j l.castSucc) with hcsdef
  set v := majRayVec 1 with hv
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
  have hE := vNum_eq e 0 1 A base c hA
  have h0 : ∀ k ℓ, vNum e 0 1 A base c 0 k ℓ μ ν = vNumE0 e 0 1 A base c k ℓ μ ν :=
    fun k ℓ => by rw [hE]; simp
  -- the quartic of `E₀`
  obtain ⟨Q2, h20, h21, -, hQ2⟩ := faceIdRayAQ_exists_loopQuartic (n := 4) le_rfl
    ((isLoopPoly_vNum e 0 1 A base c 0 v μ ν).const_mul C)
    (((isLoopPolyDeg_vNum e 0 1 A base c 0 0 v μ ν).const_mul C).mono hd₀ le_rfl)
    (((isLoopPolyDeg_vNum e 0 1 A base c 1 0 v μ ν).const_mul C).mono hd₁ le_rfl)
  -- the quartic of `M² E₂`
  have e2 : (fun ℓ => C * (M : ℂ) ^ 2 * vNumE2 e 0 1 A base c v ℓ μ ν) = fun ℓ =>
      C * (M : ℂ) ^ 2 * (vNum e 0 1 A base c 1 v ℓ μ ν - vNum e 0 1 A base c 0 v ℓ μ ν -
        vNumE4 e 0 1 A v μ ν) :=
    funext fun ℓ => by rw [maj_vNumE2_eq e A hA base c μ ν]
  have hD1 : ∀ s : Fin 2, IsLoopPolyDeg s (loopDegOf base s) 4
      fun ℓ => C * (M : ℂ) ^ 2 * vNumE2 e 0 1 A base c v ℓ μ ν := fun s => by
    rw [e2]
    exact (((isLoopPolyDeg_vNum e 0 1 A base c s 1 v μ ν).sub
      (isLoopPolyDeg_vNum e 0 1 A base c s 0 v μ ν)).sub (IsLoopPolyDeg.const _)).const_mul _
  obtain ⟨Q1, h10, h11, -, hQ1⟩ := faceIdRayAQ_exists_loopQuartic (n := 4) le_rfl
    (((isLoopPoly_vNumE2 e 0 1 A base c v μ ν).const_mul (C * (M : ℂ) ^ 2)).mono
      (by norm_num)) ((hD1 0).mono hd₀ le_rfl) ((hD1 1).mono hd₁ le_rfl)
  -- the constant quartic
  obtain ⟨Q0, h00, h01, -, hQ0⟩ := faceIdRayAQ_exists_loopQuartic (n := 0) (by norm_num)
    (IsLoopPoly.const (C * ((M : ℂ) ^ 2) ^ 2 * vNumE4 e 0 1 A v μ ν))
    (IsLoopPolyDeg.const (d := d₀) (C * ((M : ℂ) ^ 2) ^ 2 * vNumE4 e 0 1 A v μ ν))
    (IsLoopPolyDeg.const (d := d₁) (C * ((M : ℂ) ^ 2) ^ 2 * vNumE4 e 0 1 A v μ ν))
  set Q : Fin 3 → LoopQuartic := ![Q0, Q1, Q2] with hQ
  have hdeg : ∀ t, LoopDegLe 0 d₀ (Q t) ∧ LoopDegLe 1 d₁ (Q t) := fun t => by
    fin_cases t
    exacts [⟨h00, h01⟩, ⟨h10, h11⟩, ⟨h20, h21⟩]
  have hBdQ := hBd α cl hα cs Q hdeg
  -- the top monomial
  have hTop : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Fin 6 → ℝ, (∀ i, 0 ≤ simplexPoint x i) →
      0 < symanzikU α (simplexPoint x) →
        ‖faceIdRayAPOne (Q 2) α (fun i => cs i • majRayVec 1) x‖ *
          (2 * Real.sqrt (simplexPoint x 0 * simplexPoint x j')) ≤
            K * remainder α (simplexPoint x) cs / symanzikU α (simplexPoint x) ^ 2 := by
    obtain ⟨Cτ, hCτ0, hCτ⟩ := maj_exists_abs_flow_le α cs
    set E0 : ℂ := ∑ ρ, ∑ σ, kV e 0 1 ρ σ * vE0 (A μ ν ρ σ) (fun _ => v) with hE0
    refine ⟨‖C‖ * ‖E0‖ * Cτ ^ 2, by positivity, fun x hz hUp => ?_⟩
    set z := simplexPoint x with hzd
    set τ := majFlow α z cs with hτ
    have hU0 : symanzikU α z ≠ 0 := hUp.ne'
    have hfl : ∀ l : Fin 4, fm base (ppc c v) l (-loopShift α (fun l => cs l • v) z) =
        (![τ 0, τ 1, τ 2, τ 3] l) • v := by
      intro l
      fin_cases l
      · exact maj_fm_shift base c (fun l : Fin 7 => shA i j l.castSucc) z v (l' := 0) rfl
      · exact maj_fm_shift base c (fun l : Fin 7 => shA i j l.castSucc) z v (l' := 1) rfl
      · exact maj_fm_shift base c (fun l : Fin 7 => shA i j l.castSucc) z v (l' := 2) rfl
      · exact maj_fm_shift base c (fun l : Fin 7 => shA i j l.castSucc) z v (l' := 3) rfl
    have hval : (Q 2).eval (-loopShift α (fun l => cs l • v) z) =
        C * (((τ 0 * τ 1 * τ 2 * τ 3 : ℝ)) : ℂ) * E0 := by
      show Q2.eval _ = _
      rw [hQ2]
      dsimp only
      rw [h0, maj_vNumE0_flow base c e 0 1 A v _ _ hfl μ ν]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hE0]
      push_cast
      ring
    have hprod : |τ 0 * τ 1 * τ 2 * τ 3| * (2 * Real.sqrt (z 0 * z j')) ≤
        Cτ ^ 2 * remainder α z cs := by
      have hw : 0 ≤ 2 * Real.sqrt (z 0 * z j') := by positivity
      rcases hj' with rfl | rfl
      · refine maj_abs_four_le hw hCτ0 ?_ (hCτ z hz hU0 2) (hCτ z hz hU0 3)
        exact maj_abs_flow_mul_le α hz hU0 cs (show (0 : Fin 7) ≠ 1 by decide)
      · rw [show τ 0 * τ 1 * τ 2 * τ 3 = τ 0 * τ 3 * τ 1 * τ 2 by ring]
        refine maj_abs_four_le hw hCτ0 ?_ (hCτ z hz hU0 1) (hCτ z hz hU0 2)
        exact maj_abs_flow_mul_le α hz hU0 cs (show (0 : Fin 7) ≠ 3 by decide)
    have hUp2 : 0 < symanzikU α z ^ 2 := pow_pos hUp 2
    have hone : faceIdRayAPOne (Q 2) α (fun i => cs i • majRayVec 1) x =
        ((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ * (Q 2).eval (-loopShift α (fun l => cs l • v) z) :=
      rfl
    rw [hone, hval, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hUp2,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc (symanzikU α z ^ 2)⁻¹ * (‖C‖ * |τ 0 * τ 1 * τ 2 * τ 3| * ‖E0‖) *
          (2 * Real.sqrt (z 0 * z j'))
        = ‖C‖ * ‖E0‖ * (symanzikU α z ^ 2)⁻¹ * (|τ 0 * τ 1 * τ 2 * τ 3| *
          (2 * Real.sqrt (z 0 * z j'))) := by ring
      _ ≤ ‖C‖ * ‖E0‖ * (symanzikU α z ^ 2)⁻¹ * (Cτ ^ 2 * remainder α z cs) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by rw [div_eq_mul_inv]; ring
  -- the numerator along the ray
  have hN : ∀ r : ℝ, 1 ≤ r → ∀ ℓ, C * vNum e 0 1 A base c M (r • majRayVec 1) ℓ μ ν =
      ∑ t : Fin 3, ((r : ℂ) ^ 2) ^ (t : ℕ) * (Q t).eval (r⁻¹ • ℓ) := by
    intro r hr ℓ
    have hr0 : r ≠ 0 := by positivity
    rw [hE, Fin.sum_univ_three]
    simp only [hQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hQ0, hQ1, hQ2, Fin.val_zero, Fin.val_one, Fin.val_two,
      h0, maj_vNumE0_smul base c e 0 1 A (majRayVec 1) ℓ hr0,
      maj_vNumE2_smul base c e 0 1 A (majRayVec 1) ℓ hr0, vNumE4]
    ring
  have hMv : ∀ l : Fin 7, l ≠ Fin.last 6 → m₀ ^ 2 ≤
      (![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0] : Fin 7 → ℝ)
        l ^ 2 := by
    have hmA : ∀ l, m₀ ≤ mA M X Y i j l := fun l => by unfold mA; split_ifs <;> assumption
    intro l hl
    fin_cases l
    · exact faceIdRayAQ_sq_le hm₀.le (hmA 0)
    · exact faceIdRayAQ_sq_le hm₀.le (hmA 1)
    · exact faceIdRayAQ_sq_le hm₀.le (hmA 2)
    · exact faceIdRayAQ_sq_le hm₀.le (hmA 3)
    · exact faceIdRayAQ_sq_le hm₀.le hX
    · exact faceIdRayAQ_sq_le hm₀.le hY
    · exact absurd rfl hl
  have hMf : ∀ l, m₀ ≤ mA M X Y i j l := fun l => by unfold mA; split_ifs <;> assumption
  have hInt : ∀ σ : ℝ, 1 ≤ σ → ∀ u : ℝ, 1 ≤ u → IntegrableOn
      (pairDensIntegrand (fun k ℓ a b => C * vNum e 0 1 A base c M k ℓ a b) α cs
        ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0]
        (Fin.last 6) u (majRayVec σ) μ ν) (simplexSet 6) := fun σ hσ u hu =>
    integrableOn_pairDensIntegrand base c y₁ y₂ hflow hrow hrow4 (Or.inr rfl) (shA i j)
      (fun l => by fin_cases l <;> simp [shA, Fin.ext_iff] <;> omega) hcA _
      ((isLoopPoly_vNum e 0 1 A base c M _ μ ν).const_mul C) ((hBA M _ μ ν).const_mul C) hm₀ _
      rfl (fun l hl => by
        fin_cases l
        exacts [hMf 0, hMf 1, hMf 2, hMf 3, hX, hY, absurd rfl hl])
      (faceRateIncAQ_dot_ray m₀ hσ) hu
  exact faceRateIncAQ_pow_pairDens (by norm_num) α cs _ (Fin.last 6) hm₀ hMv
    (fun k ℓ => C * vNum e 0 1 A base c M k ℓ μ ν) Q hN (Or.inl le_rfl)
    (faceIdRayAQ_hMaj α cl hα cs (Fin.last 6) t₁ t₂ 0 j' ht hcl hcs Q (fun u => K₂ (cl u))
      (fun u => K₁ (cl u)) (fun u => K₃ (cl u)) hBdQ.1 hBdQ.2 hTop c₁ c₂ c₃ c₄) hInt


/-- **(A) for increments of a piece with six lines `i`.** -/
theorem faceRateIncAQ_pieceB (hd₀ : loopDegOf base 0 ≤ d₀) (hd₁ : loopDegOf base 1 ≤ d₁)
    {M X Y : ℝ} (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (i : Fin 4) (t₁ t₂ : Fin 6)
    (ht : t₁ ≠ t₂) (hcl : faceIdRayAQClB clB i t₁ = faceIdRayAQClB clB i t₂)
    (hcs : c (shB i t₁.castSucc) ≠ c (shB i t₂.castSucc)) (j' : Fin 6)
    (c₁ : FaceIdRayAQCheck (faceIdRayAQClB clB i) (Fin.last 5) t₁ t₂ 2 0)
    (c₂ : FaceIdRayAQCheck (faceIdRayAQClB clB i) (Fin.last 5) t₁ t₂ 2
      fun t => (if t = 0 then -1 else 0) + (if t = j' then -1 else 0))
    (c₃ : ∀ u, K₂ (faceIdRayAQClB clB i u) →
      FaceIdRayAQCheck (faceIdRayAQClB clB i) (Fin.last 5) t₁ t₂ 3
        fun t => if t = u then 2 else 0)
    (c₄ : ∀ u v, K₁ (faceIdRayAQClB clB i u) → K₃ (faceIdRayAQClB clB i v) →
      FaceIdRayAQCheck (faceIdRayAQClB clB i) (Fin.last 5) t₁ t₂ 4
        fun t => (if t = u then 2 else 0) + (if t = v then 2 else 0))
    (hcB : IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (hBB : ∀ m k a b, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3} 4
      fun ℓ => vNum e 0 1 A base c m k ℓ a b) :
    FaceRateIncAQPow (majDPieceB base c (vNum e 0 1 A base c) M X Y μ ν i) := by
  set α := castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc) with hαdef
  set cl := faceIdRayAQClB clB i with hcldef
  have hα : ∀ t, α t = faceIdRayAQRow (cl t) :=
    faceIdRayAQ_castLoopMatrix_row _ cl fun t => hclB _
  set cs : Fin 6 → ℝ := fun l => c (shB i l.castSucc) with hcsdef
  set v := majRayVec 1 with hv
  set K' : ℂ := -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) with hK'
  have hE := vNum_eq e 0 1 A base c hA
  have e2 : (fun ℓ => K' * vNumE2 e 0 1 A base c v ℓ μ ν) = fun ℓ =>
      K' * (vNum e 0 1 A base c 1 v ℓ μ ν - vNum e 0 1 A base c 0 v ℓ μ ν -
        vNumE4 e 0 1 A v μ ν) :=
    funext fun ℓ => by rw [maj_vNumE2_eq e A hA base c μ ν]
  have hD1 : ∀ s : Fin 2, IsLoopPolyDeg s (loopDegOf base s) 4
      fun ℓ => K' * vNumE2 e 0 1 A base c v ℓ μ ν := fun s => by
    rw [e2]
    exact (((isLoopPolyDeg_vNum e 0 1 A base c s 1 v μ ν).sub
      (isLoopPolyDeg_vNum e 0 1 A base c s 0 v μ ν)).sub (IsLoopPolyDeg.const _)).const_mul _
  obtain ⟨Q1, h10, h11, hq1, hQ1⟩ := faceIdRayAQ_exists_loopQuartic (n := 2) (by norm_num)
    ((isLoopPoly_vNumE2 e 0 1 A base c v μ ν).const_mul K') ((hD1 0).mono hd₀ le_rfl)
    ((hD1 1).mono hd₁ le_rfl)
  set d : ℂ := K' * (((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * vNumE4 e 0 1 A v μ ν) with hd
  obtain ⟨Q0, h00, h01, hq0, hQ0⟩ := faceIdRayAQ_exists_loopQuartic (n := 0) (by norm_num)
    (IsLoopPoly.const d) (IsLoopPolyDeg.const (d := d₀) d) (IsLoopPolyDeg.const (d := d₁) d)
  set Q : Fin 3 → LoopQuartic := ![Q0, Q1, majZeroQ] with hQ
  have hdeg : ∀ t, LoopDegLe 0 d₀ (Q t) ∧ LoopDegLe 1 d₁ (Q t) := fun t => by
    fin_cases t
    exacts [⟨h00, h01⟩, ⟨h10, h11⟩, ⟨LoopDegLe.zero, LoopDegLe.zero⟩]
  have hBdQ := hBd α cl hα cs Q hdeg
  have hN : ∀ r : ℝ, 1 ≤ r → ∀ ℓ, -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      (vNum e 0 1 A base c X (r • majRayVec 1) ℓ μ ν -
        vNum e 0 1 A base c M (r • majRayVec 1) ℓ μ ν) =
      ∑ t : Fin 3, ((r : ℂ) ^ 2) ^ (t : ℕ) * (Q t).eval (r⁻¹ • ℓ) := by
    intro r hr ℓ
    have hr0 : r ≠ 0 := by positivity
    rw [hE, hE, maj_vNumE2_smul base c e 0 1 A (majRayVec 1) ℓ hr0, Fin.sum_univ_three]
    simp only [hQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hQ0, hQ1, majZeroQ_eval, Fin.val_zero, Fin.val_one,
      Fin.val_two, vNumE4, hd, hK']
    ring
  have hMv : ∀ l : Fin 6, l ≠ Fin.last 5 → m₀ ^ 2 ≤
      (![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] : Fin 6 → ℝ) l ^ 2 := by
    have hmB : ∀ l, m₀ ≤ mB X Y i l := fun l => by unfold mB; split_ifs <;> assumption
    intro l hl
    fin_cases l
    · exact faceIdRayAQ_sq_le hm₀.le (hmB 0)
    · exact faceIdRayAQ_sq_le hm₀.le (hmB 1)
    · exact faceIdRayAQ_sq_le hm₀.le (hmB 2)
    · exact faceIdRayAQ_sq_le hm₀.le (hmB 3)
    · exact faceIdRayAQ_sq_le hm₀.le hY
    · exact absurd rfl hl
  have hpoly : ∀ k a b, IsLoopPoly 2 3 fun ℓ =>
      -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (vNum e 0 1 A base c X k ℓ a b -
        vNum e 0 1 A base c M k ℓ a b) := by
    intro k a b
    have e' : (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (vNum e 0 1 A base c X k ℓ a b -
        vNum e 0 1 A base c M k ℓ a b)) =
        fun ℓ => (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
          (vNumE2 e 0 1 A base c k ℓ a b + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * vNumE4 e 0 1 A k a b) := by
      funext ℓ; rw [hE, hE]; ring
    rw [e']
    exact (((isLoopPoly_vNumE2 e 0 1 A base c k a b).add (IsLoopPoly.const _)).const_mul _).mono
      (by norm_num)
  have hMf : ∀ l, m₀ ≤ mB X Y i l := fun l => by unfold mB; split_ifs <;> assumption
  have hInt : ∀ σ : ℝ, 1 ≤ σ → ∀ u : ℝ, 1 ≤ u → IntegrableOn
      (pairDensIntegrand (fun k ℓ a b => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        (vNum e 0 1 A base c X k ℓ a b - vNum e 0 1 A base c M k ℓ a b)) α cs
        ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0]
        (Fin.last 5) u (majRayVec σ) μ ν) (simplexSet 5) := fun σ hσ u hu =>
    integrableOn_pairDensIntegrand base c y₁ y₂ hflow hrow hrow4 (Or.inl rfl) (shB i)
      (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]; omega) hcB _ (hpoly _ μ ν)
      ((((hBB X _ μ ν).sub (hBB M _ μ ν)).const_mul _).mono (by decide) le_rfl) hm₀ _ rfl
      (fun l hl => by
        fin_cases l
        exacts [hMf 0, hMf 1, hMf 2, hMf 3, hY, absurd rfl hl])
      (faceRateIncAQ_dot_ray m₀ hσ) hu
  exact faceRateIncAQ_pow_pairDens (by norm_num) α cs _ (Fin.last 5) hm₀ hMv
    (fun k ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      (vNum e 0 1 A base c X k ℓ μ ν - vNum e 0 1 A base c M k ℓ μ ν)) Q hN
    (Or.inr fun t => by fin_cases t; exacts [hq0 (by norm_num), hq1 (by norm_num), rfl])
    (faceIdRayAQ_hMaj α cl hα cs (Fin.last 5) t₁ t₂ 0 j' ht hcl hcs Q (fun u => K₂ (cl u))
      (fun u => K₁ (cl u)) (fun u => K₃ (cl u)) hBdQ.1 hBdQ.2
      (faceIdRayAQ_top_zero α cs 0 j') c₁ c₂ c₃ c₄) hInt

end Pieces

end QED.GradedProof.RPi4

end
