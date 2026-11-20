/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdVtx

/-!
# (R-Π₄) step L6d3: the self-energy face as a reduced bracket of a substituted numerator

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3.

At `ρ = 0` the self-energy face (one fermion line and the photon in the face block, `b = -θ`)
has the face matrix `Ĝ = faceG 0 1 b 1 = [[1, -b], [-b, 0]]` and the point
`X̂ = (-P₀, -(b₁ - b P₀))`. With the loop substitution `ℓ₁ ↦ ℓ₁ - b ℓ₀` (`faceIdMb b`, acting on
the quartic by `lmap`), `Ĝ` becomes `eS 0` up to a multiple of `eS 1`, which a numerator of
loop-`1` degree `≤ 1` does not see, and `X̂` becomes `(-P₀, -b₁)`. Hence the `σ`-integrated
self-energy bracket is the reduced one-loop bracket (`faceIdRedBr`, `n - 2` lines) of the
substituted quartic `ℓ ↦ Q(ℓ₀, ℓ₁ - b ℓ₀)` at `(-P₀, -b₁)` (**`faceId_se_pt`**,
**`faceId_se₂_pt`**), and the self-energy face value is the integral of that over the face and
rest simplices (**`faceId_faceIdVal_se`**).

* `faceIdM`, `faceId_conj_gMet`, `faceId_cTwoG_lmap`, `faceId_cFourG_lmap`;
* `faceId_cTwoG_eS1_deg1`, `faceId_cFourG_eS1_deg1`, `faceId_cFourX_eS1_deg1`;
* `faceIdMb`, `faceId_actC_faceIdMb`, `faceId_cTwoG_faceG_deg1`, `faceId_cFourG_faceG_deg1`;
* **`faceId_se_pt`**, **`faceId_se₂_pt`**, **`faceId_faceIdVal_se`**.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Matrix

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.TwoLoop.LimitCovariance (lmap actC evalC_lmap hessForm_lmap
  sum_mul_symm_eq_of_quadForm_eq conj_apply sum_block2 sum_block4 matPair_conj)

/-! ### Substitutions acting on the loop label only -/

/-- The substitution `m ⊗ 1` on `LoopIndex = Fin 2 × Fin 4`. -/
def faceIdM (m : Matrix (Fin 2) (Fin 2) ℝ) : Matrix LoopIndex LoopIndex ℝ :=
  fun a b => if a.2 = b.2 then m a.1 b.1 else 0

theorem faceId_conj_gMet (m G : Matrix (Fin 2) (Fin 2) ℝ) :
    faceIdM m * gMet G * (faceIdM m)ᵀ = gMet (m * G * mᵀ) := by
  ext a b
  rw [conj_apply]
  simp only [faceIdM, gMet, Fintype.sum_prod_type, ite_mul, zero_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_two]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

variable {Q : LoopQuartic}

/-- **The quadratic contraction of a substituted quartic** (symmetric matrix). -/
theorem faceId_cTwoG_lmap (M : Matrix LoopIndex LoopIndex ℝ) (Q : LoopQuartic)
    {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : ∀ r s, G r s = G s r) (X : LoopIndex → ℂ) :
    cTwoG (lmap M Q) G X =
      ∑ a, ∑ b, Q.hess (actC M X) a b * (((M * gMet G * Mᵀ) a b : ℝ) : ℂ) := by
  classical
  set H' : LoopIndex → LoopIndex → ℂ := fun b c =>
    ∑ a, ∑ a', ((M a b : ℂ) * M a' c) * Q.hess (actC M X) a a' with hH'
  have hq : ∀ D : LoopIndex → ℂ, ∑ a, ∑ b, (lmap M Q).hess X a b * (D a * D b) =
      ∑ a, ∑ b, H' a b * (D a * D b) := by
    intro D
    rw [hessForm_lmap]
    simp only [hH', actC, Finset.sum_mul, Finset.mul_sum]
    rw [sum_block2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hpol := sum_mul_symm_eq_of_quadForm_eq _ _ hq
    (fun a b => ((gMet G a b : ℝ) : ℂ)) fun a b => by rw [faceId_gMet_symm hG]
  unfold cTwoG
  rw [hpol]
  simp only [hH', conj_apply, Finset.sum_mul]
  push_cast
  rw [sum_block2]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The quartic contraction of a substituted quartic.** -/
theorem faceId_cFourG_lmap (M : Matrix LoopIndex LoopIndex ℝ) (Q : LoopQuartic)
    (G : Matrix (Fin 2) (Fin 2) ℝ) :
    cFourG (lmap M Q) G = ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄,
      Q.quart a₁ a₂ a₃ a₄ * (matPair (M * gMet G * Mᵀ) a₁ a₂ a₃ a₄ : ℂ) := by
  unfold cFourG
  simp only [lmap, Finset.sum_mul]
  rw [sum_block4]
  refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ =>
    Finset.sum_congr rfl fun a₃ _ => Finset.sum_congr rfl fun a₄ _ => ?_
  rw [← matPair_conj]
  push_cast
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem faceId_cTwoG_lmap_faceIdM (m : Matrix (Fin 2) (Fin 2) ℝ) (Q : LoopQuartic)
    {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : ∀ r s, G r s = G s r) (X : LoopIndex → ℂ) :
    cTwoG (lmap (faceIdM m) Q) G X = cTwoG Q (m * G * mᵀ) (actC (faceIdM m) X) := by
  rw [faceId_cTwoG_lmap _ Q hG, faceId_conj_gMet]
  rfl

theorem faceId_cFourG_lmap_faceIdM (m : Matrix (Fin 2) (Fin 2) ℝ) (Q : LoopQuartic)
    (G : Matrix (Fin 2) (Fin 2) ℝ) :
    cFourG (lmap (faceIdM m) Q) G = cFourG Q (m * G * mᵀ) := by
  rw [faceId_cFourG_lmap, faceId_conj_gMet]
  rfl

/-! ### Loop-`1` degree `≤ 1` does not see `eS 1` -/

theorem faceId_cTwoG_eS1_deg1 (hQ : LoopDegLe 1 1 Q) (X : LoopIndex → ℂ) :
    cTwoG Q (eS 1) X = 0 := by
  unfold cTwoG
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  by_cases hab : a.1 = 1 ∧ b.1 = 1
  · have ia := loopInd_of_eq hab.1
    have ib := loopInd_of_eq hab.2
    have h : Q.hess X a b = 0 := by
      simp only [LoopQuartic.hess, LoopQuartic.quartSym]
      rw [hQ.quad a b (by omega)]
      have h1 : ∀ c, (Q.cub a b c + Q.cub a c b + Q.cub c a b) * X c = 0 := fun c => by
        rw [hQ.cub a b c (by omega), hQ.cub a c b (by omega), hQ.cub c a b (by omega)]
        simp
      have h2 : ∀ c d, (Q.quart a b c d + Q.quart a c b d + Q.quart a c d b + Q.quart c a b d +
          Q.quart c a d b + Q.quart c d a b) * (X c * X d) = 0 := fun c d => by
        rw [hQ.quart a b c d (by omega), hQ.quart a c b d (by omega),
          hQ.quart a c d b (by omega), hQ.quart c a b d (by omega),
          hQ.quart c a d b (by omega), hQ.quart c d a b (by omega)]
        simp
      simp only [h1, h2, Finset.sum_const_zero, add_zero]
    rw [h, zero_mul]
  · have : gMet (eS 1) a b = 0 := by simp [gMet, eS, hab]
    rw [this]
    simp

theorem faceId_cFourX_eS1_deg1 (hQ : LoopDegLe 1 1 Q) (G : Matrix (Fin 2) (Fin 2) ℝ) :
    cFourX Q G (eS 1) = 0 := by
  rw [faceId_cFourX_eS1 (hQ.mono (by norm_num)) G]
  have h : cFourX Q (eS 0) (eS 1) = 0 := by
    unfold cFourX
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    have hz : ∀ x y : LoopIndex, gMet (eS 1) x y ≠ 0 → x.1 = 1 ∧ y.1 = 1 := fun x y h => by
      by_contra hxy
      exact h (by simp [gMet, eS, hxy])
    by_cases hq : Q.quart a b c d = 0
    · simp [hq]
    · have hl : loopInd 1 a + loopInd 1 b + loopInd 1 c + loopInd 1 d ≤ 1 := by
        by_contra hc
        exact hq (hQ.quart a b c d (by omega))
      have e : ∀ x y : LoopIndex, loopInd 1 x + loopInd 1 y ≤ 1 → gMet (eS 1) x y = 0 :=
        fun x y hxy => gMet_eS_eq_zero hxy
      simp only [pairX]
      rw [e c d (by omega), e a b (by omega), e b d (by omega), e a c (by omega),
        e b c (by omega), e a d (by omega)]
      simp
  rw [h, mul_zero]

theorem faceId_cFourG_eS1_deg1 (hQ : LoopDegLe 1 1 Q) : cFourG Q (eS 1) = 0 := by
  unfold cFourG
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
  by_cases hq : Q.quart a b c d = 0
  · simp [hq]
  · have hl : loopInd 1 a + loopInd 1 b + loopInd 1 c + loopInd 1 d ≤ 1 := by
      by_contra hc
      exact hq (hQ.quart a b c d (by omega))
    have e : ∀ x y : LoopIndex, loopInd 1 x + loopInd 1 y ≤ 1 → gMet (eS 1) x y = 0 :=
      fun x y hxy => gMet_eS_eq_zero hxy
    simp only [matPair]
    rw [e a b (by omega), e a c (by omega), e a d (by omega)]
    simp

/-! ### The self-energy face -/

/-- The substitution `ℓ₁ ↦ ℓ₁ - b ℓ₀` on the loop labels. -/
def faceIdMb (b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; -b, 1]

theorem faceId_conj_eS0 (b : ℝ) :
    faceIdMb b * eS 0 * (faceIdMb b)ᵀ = faceG 0 1 b 1 + (b ^ 2) • eS 1 := by
  ext r s
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  fin_cases r <;> fin_cases s <;> simp [faceIdMb, eS, faceG, uHat, sq]

theorem faceId_actC_faceIdMb (b : ℝ) (P₀ b₁ : Fin 4 → ℝ) :
    actC (faceIdM (faceIdMb b)) (loopComp ![-P₀, -b₁]) = faceX 0 1 b 1 P₀ b₁ := by
  funext a
  obtain ⟨a1, a2⟩ := a
  simp only [actC, faceIdM, Fintype.sum_prod_type]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), ofReal_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Fin.sum_univ_two]
  fin_cases a1 <;>
    simp [faceIdMb, faceX, loopComp, shat, uHat, sub_eq_add_neg]

theorem faceId_faceG_symm' (b : ℝ) : ∀ r s, faceG 0 1 b 1 r s = faceG 0 1 b 1 s r :=
  faceId_faceG_symm 0 1 b 1

theorem faceId_cTwoG_faceG_deg1 (hQ : LoopDegLe 1 1 Q) (b : ℝ) (P₀ b₁ : Fin 4 → ℝ) :
    cTwoG Q (faceG 0 1 b 1) (faceX 0 1 b 1 P₀ b₁) =
      cTwoG (lmap (faceIdM (faceIdMb b)) Q) (eS 0) (loopComp ![-P₀, -b₁]) := by
  rw [faceId_cTwoG_lmap_faceIdM _ Q (faceId_eS_symm 0), faceId_conj_eS0,
    faceId_actC_faceIdMb, cTwoG_add_smul, faceId_cTwoG_eS1_deg1 hQ]
  ring

theorem faceId_cFourG_faceG_deg1 (hQ : LoopDegLe 1 1 Q) (b : ℝ) :
    cFourG Q (faceG 0 1 b 1) = cFourG (lmap (faceIdM (faceIdMb b)) Q) (eS 0) := by
  rw [faceId_cFourG_lmap_faceIdM, faceId_conj_eS0, cFourG_add_smul,
    faceId_cFourX_eS1_deg1 hQ, faceId_cFourG_eS1_deg1 hQ]
  ring

theorem faceId_evalC_faceX_lmap (Q : LoopQuartic) (b : ℝ) (P₀ b₁ : Fin 4 → ℝ) :
    Q.evalC (faceX 0 1 b 1 P₀ b₁) =
      (lmap (faceIdM (faceIdMb b)) Q).evalC (loopComp ![-P₀, -b₁]) := by
  rw [evalC_lmap, faceId_actC_faceIdMb]

/-- **The self-energy bracket at `ρ = 0`, integrated in `σ`** (seven lines), is the reduced
bracket (five lines) of the substituted quartic at `(-P₀, -b₁)`. -/
theorem faceId_se_pt (hQ : LoopDegLe 1 1 Q) (b : ℝ) (P₀ b₁ : Fin 4 → ℝ) (v : ℝ) :
    ∑ j, (FaceBr.se 7 Q).C j 0 1 b 1 P₀ b₁ *
      (((v ^ ((FaceBr.se 7 Q).k j - 1) : ℝ) : ℂ)⁻¹ / (((FaceBr.se 7 Q).k j : ℂ) - 1)) =
      faceIdRedBr 5 (lmap (faceIdM (faceIdMb b)) Q) (loopComp ![-P₀, -b₁]) v := by
  rw [Fin.sum_univ_three]
  simp only [FaceBr.se, faceIdRedBr]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [faceId_evalC_faceX_lmap, faceId_cTwoG_faceG_deg1 hQ, faceId_cFourG_faceG_deg1 hQ]
  norm_num [Nat.factorial]
  ring

/-- **The two-term self-energy bracket at `ρ = 0`, integrated in `σ`** (six lines, no quartic
part), is the reduced bracket (four lines) of the substituted quartic at `(-P₀, -b₁)`. -/
theorem faceId_se₂_pt (hQ : LoopDegLe 1 1 Q) (hq : Q.quart = 0) (b : ℝ) (P₀ b₁ : Fin 4 → ℝ)
    (v : ℝ) :
    ∑ j, (FaceBr.se₂ 6 Q).C j 0 1 b 1 P₀ b₁ *
      (((v ^ ((FaceBr.se₂ 6 Q).k j - 1) : ℝ) : ℂ)⁻¹ / (((FaceBr.se₂ 6 Q).k j : ℂ) - 1)) =
      faceIdRedBr 4 (lmap (faceIdM (faceIdMb b)) Q) (loopComp ![-P₀, -b₁]) v := by
  rw [Fin.sum_univ_two]
  simp only [FaceBr.se₂, faceIdRedBr]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [faceId_evalC_faceX_lmap, faceId_cTwoG_faceG_deg1 hQ, ← faceId_cFourG_faceG_deg1 hQ,
    FaceBr.cFourG_of_quart hq]
  norm_num [Nat.factorial]
  ring

/-- **The self-energy face value** (face block with one fermion line and the photon), for a
representative of loop-`1` degree `≤ 1`: the integral over the face and rest simplices of the
reduced bracket (`n - 2` lines) of the substituted quartic `ℓ ↦ Q(ℓ₀, ℓ₁ - b ℓ₀)` at
`(-P₀, -b₁)`. -/
theorem faceId_faceIdVal_se {q n : ℕ} (S : FaceShape (0 + 1) q) (hQ : LoopDegLe 1 1 Q)
    (hn : n = 7 ∨ (n = 6 ∧ Q.quart = 0)) :
    faceIdVal n S Q = ∫ x in simplexSet (0 + 1) ×ˢ simplexSet q,
      faceIdRedBr (n - 2) (lmap (faceIdM (faceIdMb (S.b (simplexPoint x.1)))) Q)
        (loopComp ![-S.P0 (simplexPoint x.2), -S.b₁ (simplexPoint x.1)])
        (S.mR (simplexPoint x.2) -
          Minkowski.dot (S.P0 (simplexPoint x.2)) (S.P0 (simplexPoint x.2))) := by
  rcases hn with rfl | ⟨rfl, hq⟩
  · have hv : faceIdVal 7 S Q = S.faceIdInt (FaceBr.se 7 Q) := by simp [faceIdVal]
    rw [hv, S.faceId_faceIdInt_eq _ rfl]
    simp_rw [faceId_se_pt hQ]
  · have hv : faceIdVal 6 S Q = S.faceIdInt (FaceBr.se₂ 6 Q) := by simp [faceIdVal]
    rw [hv, S.faceId_faceIdInt_eq _ rfl]
    simp_rw [faceId_se₂_pt hQ hq]

end QED.GradedProof.RPi4

end
