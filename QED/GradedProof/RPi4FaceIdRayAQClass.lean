/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayAQPiece
public import QED.GradedProof.RPi4FaceIdRayBClass

/-!
# (R-Π₄) step L10, T2.UV: (A) with a power loss for the three classes, and `MajFaceRate`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The class
densities `vDens` of `VA`, `VB`, `VC` satisfy `FaceIdRayAQPow` (for all `u ≥ 1`) for every
flavour set with masses `≥ m₀ > 0`; with the rate (B) of `QED.GradedProof.RPi4.faceIdRayB_cfg4_VA`
(and `VB`, `VC`) this gives `MajFaceRate (decCfg 1 4) (fun _ => 0) P.e 1`.

The cut pairs are the lines `(0, 3)` (`VA`, `VB`) and `(0, 1)` (`VC`); the pieces `(1,1)`,
`(1,2)`, `(2,2)`, `1`, `2` of `VB` cut `(1, 2)`. The flow lines are `(0, 3)` (`VA`, `VC`) and
`(0, 1)` (`VB`). The integer checks are decided.

* `FaceIdRayAQPieceOK`, `faceIdRayAQ_pieces`, `faceIdRayAQ_vDens`;
* `faceIdRayAQ_vDens_VA`, `faceIdRayAQ_vDens_VB`, `faceIdRayAQ_vDens_VC`;
* **`faceIdRayAQ_majFaceRate_cfg4`**.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.WickModel (Params)

/-- **The decided data of a piece**: a cut pair of the same class, and the four integer checks
(flow lines `0, j'`). -/
def FaceIdRayAQPieceOK {n : ℕ} (cl : Fin (n + 1) → Fin 3) (t₁ t₂ j' : Fin (n + 1))
    (K₂ K₁ K₃ : Fin 3 → Prop) [DecidablePred K₂] [DecidablePred K₁] [DecidablePred K₃] :
    Prop :=
  t₁ ≠ t₂ ∧ cl t₁ = cl t₂ ∧ FaceIdRayAQCheck cl (Fin.last n) t₁ t₂ 2 0 ∧
    FaceIdRayAQCheck cl (Fin.last n) t₁ t₂ 2
      (fun t => (if t = 0 then -1 else 0) + (if t = j' then -1 else 0)) ∧
    (∀ u, K₂ (cl u) → FaceIdRayAQCheck cl (Fin.last n) t₁ t₂ 3 fun t => if t = u then 2 else 0) ∧
    ∀ u v, K₁ (cl u) → K₃ (cl v) → FaceIdRayAQCheck cl (Fin.last n) t₁ t₂ 4
      fun t => (if t = u then 2 else 0) + (if t = v then 2 else 0)

instance {n : ℕ} (cl : Fin (n + 1) → Fin 3) (t₁ t₂ j' : Fin (n + 1))
    (K₂ K₁ K₃ : Fin 3 → Prop) [DecidablePred K₂] [DecidablePred K₁] [DecidablePred K₃] :
    Decidable (FaceIdRayAQPieceOK cl t₁ t₂ j' K₂ K₁ K₃) := by
  unfold FaceIdRayAQPieceOK; infer_instance

section Pieces

variable (e : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l)) (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (clB : Fin 5 → Fin 3) (hclB : ∀ r, base r = faceIdRayAQRowZ (clB r)) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (μ ν : Fin 4) {d₀ d₁ : ℕ} (K₂ K₁ K₃ : Fin 3 → Prop) [DecidablePred K₂] [DecidablePred K₁]
  [DecidablePred K₃]
  (hBd : ∀ {n : ℕ} (α : Fin (n + 1) → Fin 2 → ℝ) (cl : Fin (n + 1) → Fin 3),
    (∀ t, α t = faceIdRayAQRow (cl t)) → ∀ (cs : Fin (n + 1) → ℝ) (Q : Fin 3 → LoopQuartic),
      (∀ t, LoopDegLe 0 d₀ (Q t) ∧ LoopDegLe 1 d₁ (Q t)) → FaceIdRayAQBd α cs cl K₂ K₁ K₃ Q)
  (hd₀ : loopDegOf base 0 ≤ d₀) (hd₁ : loopDegOf base 1 ≤ d₁) (hd₀' : 2 ≤ d₀)
  (hb0 : base (0 : Fin 4).castSucc = ![1, 0])
  (tA : Fin 4 → Fin 4 → Fin 7 × Fin 7) (tB : Fin 4 → Fin 6 × Fin 6) (jA : Fin 7) (jB : Fin 6)
  (hjA : jA = 1 ∨ jA = 3)
  (hokA : ∀ i j : Fin 4, i ≤ j →
    FaceIdRayAQPieceOK (faceIdRayAQClA clB i j) (tA i j).1 (tA i j).2 jA K₂ K₁ K₃)
  (hokB : ∀ i : Fin 4, FaceIdRayAQPieceOK (faceIdRayAQClB clB i) (tB i).1 (tB i).2 jB K₂ K₁ K₃)
  (hcsA : ∀ i j : Fin 4, i ≤ j → c (shA i j (tA i j).1.castSucc) ≠ c (shA i j (tA i j).2.castSucc))
  (hcsB : ∀ i : Fin 4, c (shB i (tB i).1.castSucc) ≠ c (shB i (tB i).2.castSucc))

include hA hclB hm₀ hBd hd₀ hd₁ hd₀' hb0 hjA hokA hokB hcsA hcsB

/-- **The merged pieces of a class at `(M, X, Y)`**, masses `≥ m₀`. -/
theorem faceIdRayAQ_pieces {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) :
    FaceIdRayAQPow fun u k => triDens base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) M X Y u k μ ν
      := by
  have PA : ∀ i j : Fin 4, FaceIdRayAQPow fun u k =>
      if i ≤ j then faceIdRayAPieceA base c (vNum e 0 1 A base c) M X Y μ ν i j u k else 0 :=
    fun i j => by
      by_cases hij : i ≤ j
      · simp only [hij, ite_true]
        obtain ⟨ht, hcl, c₁, c₂, c₃, c₄⟩ := hokA i j hij
        exact faceIdRayAQ_pieceA e A hA base c clB hclB hm₀ μ ν K₂ K₁ K₃ hBd hd₀ hd₁ hM hX hY
          i j _ _ ht hcl (hcsA i j hij) jA hjA c₁ c₂ c₃ c₄
      · simpa only [hij, ite_false] using FaceIdRayAQPow.zero
  have PB : ∀ i : Fin 4, FaceIdRayAQPow
      (faceIdRayAPieceB base c (vNum e 0 1 A base c) M X Y μ ν i) := fun i => by
    obtain ⟨ht, hcl, c₁, c₂, c₃, c₄⟩ := hokB i
    exact faceIdRayAQ_pieceB e A hA base c clB hclB hm₀ μ ν K₂ K₁ K₃ hBd hd₀ hd₁ hX hY
      i _ _ ht hcl (hcsB i) jB c₁ c₂ c₃ c₄
  have PP : FaceIdRayAQPow (faceIdRayAPieceP base c (vNumE4 e 0 1 A) M X Y μ ν) := by
    obtain ⟨ht, hcl, c₁, c₂, c₃, c₄⟩ := hokB 0
    exact faceIdRayAQ_pieceP base c clB hclB hm₀ μ ν K₂ K₁ K₃ hBd hd₀' hb0 hY _
      (fun _ => rfl) _ _ ht hcl (hcsB 0) jB c₁ c₂ c₃ c₄
  exact ((FaceIdRayAQPow.sum Finset.univ fun i _ =>
    FaceIdRayAQPow.sum Finset.univ fun j _ => PA i j).add
    (FaceIdRayAQPow.sum Finset.univ fun i _ => PB i)).add PP

/-- **A class density**, flavours with masses `≥ m₀`. -/
theorem faceIdRayAQ_vDens {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    FaceIdRayAQPow fun u k => vDens A base c Φ e m₀ u k μ ν := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g := Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  exact FaceIdRayAQPow.sum Finset.univ fun f _ =>
    (faceIdRayAQ_pieces e A hA base c clB hclB hm₀ μ ν K₂ K₁ K₃ hBd hd₀ hd₁ hd₀' hb0 tA tB jA jB
      hjA hokA hokB hcsA hcsB (hmass f) hX (by linarith)).const_mul (Φ.coeff f : ℂ)

end Pieces

/-! ### The three classes -/

/-- The line classes of the rows of `VA`. -/
def faceIdRayAQClVA : Fin 5 → Fin 3 := ![0, 1, 0, 0, 2]

/-- The line classes of the rows of `VB`. -/
def faceIdRayAQClVB : Fin 5 → Fin 3 := ![0, 1, 1, 0, 2]

/-- The line classes of the rows of `VC`. -/
def faceIdRayAQClVC : Fin 5 → Fin 3 := ![0, 0, 1, 0, 2]

/-- The cut pairs of the pieces with seven lines of `VB`. -/
def faceIdRayAQCutVB (i j : Fin 4) : Fin 7 × Fin 7 :=
  if (i = 1 ∨ i = 2) ∧ (j = 1 ∨ j = 2) then (1, 2) else (0, 3)

/-- The cut pairs of the pieces with six lines of `VB`. -/
def faceIdRayAQCutVBB (i : Fin 4) : Fin 6 × Fin 6 :=
  if i = 1 ∨ i = 2 then (1, 2) else (0, 3)

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) (μ ν : Fin 4)

include hm₀ hmass

/-- **(A) with a power loss for all `u ≥ 1`, class `VA`.** -/
theorem faceIdRayAQ_vDens_VA : FaceIdRayAQPow fun u k => vDens aVA baseVA cVA Φ e m₀ u k μ ν :=
  faceIdRayAQ_vDens e aVA (fun a b ρ σ => isOddG_aVA a b ρ σ) baseVA cVA faceIdRayAQClVA
    (by decide) hm₀ μ ν (· ≠ 0) (· ≠ 0) (· = 2)
    (fun α cl hα cs Q hQ => faceIdRayAQBd_VA α cl hα cs Q hQ)
    (by rw [loopDegOf_VA_zero]) (by rw [loopDegOf_VA]) (by norm_num) (by decide)
    (fun _ _ => (0, 3)) (fun _ => (0, 3)) 3 3 (Or.inr rfl) (by decide) (by decide)
    (fun i j _ => by fin_cases i <;> fin_cases j <;> norm_num [shA, cVA])
    (fun i => by fin_cases i <;> norm_num [shB, cVA]) Φ hmass

/-- **(A) with a power loss for all `u ≥ 1`, class `VB`.** -/
theorem faceIdRayAQ_vDens_VB : FaceIdRayAQPow fun u k => vDens aVB baseVB cVB Φ e m₀ u k μ ν :=
  faceIdRayAQ_vDens e aVB (fun a b ρ σ => isOddG_aVB a b ρ σ) baseVB cVB faceIdRayAQClVB
    (by decide) hm₀ μ ν (fun _ => True) (· ≠ 1) (· ≠ 0)
    (fun α cl hα cs Q hQ => faceIdRayAQBd_VB α cl hα cs Q hQ)
    (by rw [loopDegOf_VB.2]; norm_num) (by rw [loopDegOf_VB.1]; norm_num) (by norm_num)
    (by decide) faceIdRayAQCutVB faceIdRayAQCutVBB 1 1 (Or.inl rfl) (by decide) (by decide)
    (fun i j _ => by fin_cases i <;> fin_cases j <;> norm_num [shA, cVB, faceIdRayAQCutVB])
    (fun i => by fin_cases i <;> norm_num [shB, cVB, faceIdRayAQCutVBB]) Φ hmass

/-- **(A) with a power loss for all `u ≥ 1`, class `VC`.** -/
theorem faceIdRayAQ_vDens_VC : FaceIdRayAQPow fun u k => vDens aVC baseVC cVC Φ e m₀ u k μ ν :=
  faceIdRayAQ_vDens e aVC (fun a b ρ σ => isOddG_aVC a b ρ σ) baseVC cVC faceIdRayAQClVC
    (by decide) hm₀ μ ν (· ≠ 0) (· ≠ 0) (· = 2)
    (fun α cl hα cs Q hQ => faceIdRayAQBd_VA α cl hα cs Q hQ)
    (by rw [loopDegOf_VC_zero]) (by rw [loopDegOf_VC]) (by norm_num) (by decide)
    (fun _ _ => (0, 1)) (fun _ => (0, 1)) 3 3 (Or.inr rfl) (by decide) (by decide)
    (fun i j _ => by fin_cases i <;> fin_cases j <;> norm_num [shA, cVC])
    (fun i => by fin_cases i <;> norm_num [shB, cVC]) Φ hmass

end Classes

/-! ### `MajFaceRate` at `decCfg 1 4` -/

/-- **`MajFaceRate (decCfg 1 4) (fun _ => 0) P.e 1`**, unconditionally. -/
theorem faceIdRayAQ_majFaceRate_cfg4 (P : Params) (he : P.e ≠ 0) :
    MajFaceRate (decCfg 1 4) (fun _ => 0) P.e 1 := by
  obtain ⟨BA, pA, hpA, LA, rA⟩ := faceIdRayB_cfg4_VA P.e
  obtain ⟨BB, pB, hpB, LB, rB⟩ := faceIdRayB_cfg4_VB P.e
  obtain ⟨BC, pC, hpC, LC, rC⟩ := faceIdRayB_cfg4_VC P.e
  exact faceIdRate_cfg4_of_pow_rate P he (L := ![LA, LB, LC]) (B := ![BA, BB, BC])
    (p := ![pA, pB, pC]) (fun i => by fin_cases i <;> assumption)
    (faceIdRayAQ_vDens_VA _ one_pos faceIdRayB_cfg4_mass P.e 2 3).faceIdRayAPow
    (faceIdRayAQ_vDens_VB _ one_pos faceIdRayB_cfg4_mass P.e 2 3).faceIdRayAPow
    (faceIdRayAQ_vDens_VC _ one_pos faceIdRayB_cfg4_mass P.e 2 3).faceIdRayAPow rA rB rC

end QED.GradedProof.RPi4

end
