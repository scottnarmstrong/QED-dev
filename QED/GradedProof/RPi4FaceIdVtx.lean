/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdCongr

/-!
# (R-Π₄) step L6d3: the reduced one-loop bracket and the vertex face

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3.

**The reduced one-loop bracket** `faceIdRedBr n P X v` of a numerator `P` of the loop momentum
`ℓ₀` alone, with `n` lines: `(n-3)! P(X) v^{2-n} + (n-4)!/2 Δ₀P(X) v^{3-n} + (n-5)!/4 Δ₀²P v^{4-n}`
(`Δ₀` the contraction with `eS 0`, i.e. with the metric on loop `0`): the self-energy face bracket
with the face matrix replaced by `eS 0`. Its integral over the rest simplex of a face shape,
`faceIdRedVal`, is the reduced one-loop functional the face values are compared with.

**The vertex face** (`p = 1`: two fermion lines and the photon in the face block), for a
representative of degree `≤ 2` along loop `1`: at `ρ = 0` only the terms with `E₁ = eS 1` survive,
they depend neither on the face point nor on the loop-`1` part of the shift, and they are the
reduced bracket of `faceIdLap Q = ½ Δ₁Q` (the half loop-`1` Laplacian). Hence
`faceIdVal n S Q = vol(Δ₂) · faceIdRedVal (n - 3) (faceIdLap Q)` (**`faceId_faceIdVal_vtx`**).
The vertex face identity is thereby reduced to the function identity `½ Δ₁ N = c · N_ins` for the
numerator `N` (`faceId_faceIdRedBr_congr`).

* `faceIdRedBr`, `faceIdX0`, `faceIdRedVal`, `faceId_faceIdRedBr_congr`;
* `faceIdLap`, `faceId_evalC_faceIdLap`, `faceId_cTwoG_eS1_congr0`, `faceId_cFourX_eS1`,
  `faceId_cFourX_eS0_eS1`;
* **`faceId_faceIdVal_vtx`**.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint simplexPoint_mem_stdSimplex)
open QED.TwoLoop.PauliZeroExplicit.NumeratorCongr (sum_comm4)

/-! ### The reduced one-loop bracket -/

/-- **The reduced one-loop bracket** with `n` lines at the point `X` and the value `v`. -/
noncomputable def faceIdRedBr (n : ℕ) (P : LoopQuartic) (X : LoopIndex → ℂ) (v : ℝ) : ℂ :=
  ((n - 3).factorial : ℂ) * P.evalC X * ((v ^ (n - 2) : ℝ) : ℂ)⁻¹ +
    ((n - 4).factorial : ℂ) / 2 * cTwoG P (eS 0) X * ((v ^ (n - 3) : ℝ) : ℂ)⁻¹ +
    ((n - 5).factorial : ℂ) / 4 * cFourG P (eS 0) * ((v ^ (n - 4) : ℝ) : ℂ)⁻¹

/-- The point `(-P₀, 0)` of the reduced bracket. -/
noncomputable def faceIdX0 (P₀ : Fin 4 → ℝ) : LoopIndex → ℂ := loopComp ![-P₀, 0]

/-- **The reduced one-loop functional** on the rest of a face shape: the reduced bracket at
`(-P₀(V), V̂(0) = m_R - P₀·P₀)` integrated over the rest simplex. -/
noncomputable def FaceShape.faceIdRedVal {p q : ℕ} (S : FaceShape p q) (n : ℕ) (P : LoopQuartic) :
    ℂ :=
  ∫ V in simplexSet q, faceIdRedBr n P (faceIdX0 (S.P0 (simplexPoint V)))
    (S.mR (simplexPoint V) - Minkowski.dot (S.P0 (simplexPoint V)) (S.P0 (simplexPoint V)))

/-- **The reduced bracket depends only on the numerator function.** -/
theorem faceId_faceIdRedBr_congr {P P' : LoopQuartic} (h : P.eval = P'.eval) (n : ℕ)
    (P₀ : Fin 4 → ℝ) (v : ℝ) :
    faceIdRedBr n P (faceIdX0 P₀) v = faceIdRedBr n P' (faceIdX0 P₀) v := by
  simp only [faceIdRedBr, faceIdX0, faceId_cTwoG_congr h (faceId_eS_symm 0),
    faceId_cFourG_congr h (faceId_eS_symm 0)]
  rw [show P.evalC (loopComp ![-P₀, 0]) = P'.evalC (loopComp ![-P₀, 0]) from congrFun h _]

/-! ### The half loop-`1` Laplacian -/

/-- **The half loop-`1` Laplacian** of a quartic: the quadratic `X ↦ ½ cTwoG Q (eS 1) X`. -/
noncomputable def faceIdLap (Q : LoopQuartic) : LoopQuartic where
  const := 1 / 2 * ∑ a, ∑ b, Q.quad a b * (gMet (eS 1) a b : ℂ)
  lin c := 1 / 2 * ∑ a, ∑ b, (Q.cub a b c + Q.cub a c b + Q.cub c a b) * (gMet (eS 1) a b : ℂ)
  quad c d := 1 / 2 * ∑ a, ∑ b, Q.quartSym a b c d * (gMet (eS 1) a b : ℂ)
  cub _ _ _ := 0
  quart _ _ _ _ := 0

theorem faceId_evalC_faceIdLap (Q : LoopQuartic) (X : LoopIndex → ℂ) :
    (faceIdLap Q).evalC X = 1 / 2 * cTwoG Q (eS 1) X := by
  have h1 : ∑ c, (faceIdLap Q).lin c * X c = 1 / 2 * ∑ a, ∑ b,
      (∑ c, (Q.cub a b c + Q.cub a c b + Q.cub c a b) * X c) * (gMet (eS 1) a b : ℂ) := by
    simp only [faceIdLap, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have h2 : ∑ c, ∑ d, (faceIdLap Q).quad c d * (X c * X d) = 1 / 2 * ∑ a, ∑ b,
      (∑ c, ∑ d, Q.quartSym a b c d * (X c * X d)) * (gMet (eS 1) a b : ℂ) := by
    simp only [faceIdLap, Finset.mul_sum, Finset.sum_mul]
    rw [← sum_comm4]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have h0 : (faceIdLap Q).const = 1 / 2 * ∑ a, ∑ b, Q.quad a b * (gMet (eS 1) a b : ℂ) := rfl
  simp only [LoopQuartic.evalC, h1, h2, h0]
  simp only [faceIdLap, zero_mul, Finset.sum_const_zero, add_zero, cTwoG, LoopQuartic.hess,
    add_mul, Finset.sum_add_distrib, mul_add]

theorem faceId_hess_faceIdLap (Q : LoopQuartic) (X : LoopIndex → ℂ) (c d : LoopIndex) :
    (faceIdLap Q).hess X c d = (faceIdLap Q).quad c d := by
  simp [LoopQuartic.hess, LoopQuartic.quartSym, faceIdLap]

theorem faceId_fin_two (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

variable {Q : LoopQuartic}

/-- **On loop-`1` index pairs, the Hessian of a quartic of loop-`1` degree `≤ 2` depends only on
the loop-`0` components of the point.** -/
theorem faceId_hess_congr0 (hQ : LoopDegLe 1 2 Q) {X X' : LoopIndex → ℂ}
    (hX : ∀ c : LoopIndex, c.1 = 0 → X c = X' c) {a b : LoopIndex} (ha : a.1 = 1)
    (hb : b.1 = 1) : Q.hess X a b = Q.hess X' a b := by
  have ia := loopInd_of_eq ha
  have ib := loopInd_of_eq hb
  have h1 : ∑ c, (Q.cub a b c + Q.cub a c b + Q.cub c a b) * X c =
      ∑ c, (Q.cub a b c + Q.cub a c b + Q.cub c a b) * X' c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rcases faceId_fin_two c.1 with h | h
    · rw [hX c h]
    · have ic := loopInd_of_eq h
      rw [hQ.cub a b c (by omega), hQ.cub a c b (by omega), hQ.cub c a b (by omega)]
      simp
  have h2 : ∑ c, ∑ d, Q.quartSym a b c d * (X c * X d) =
      ∑ c, ∑ d, Q.quartSym a b c d * (X' c * X' d) := by
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases hcd : c.1 = 0 ∧ d.1 = 0
    · rw [hX c hcd.1, hX d hcd.2]
    · have hz : Q.quartSym a b c d = 0 := by
        have : loopInd 1 c + loopInd 1 d ≥ 1 := by
          rcases faceId_fin_two c.1 with hc | hc
          · rcases faceId_fin_two d.1 with hd | hd
            · exact absurd ⟨hc, hd⟩ hcd
            · rw [loopInd_of_eq hd]; omega
          · rw [loopInd_of_eq hc]; omega
        simp only [LoopQuartic.quartSym]
        rw [hQ.quart a b c d (by omega), hQ.quart a c b d (by omega),
          hQ.quart a c d b (by omega), hQ.quart c a b d (by omega),
          hQ.quart c a d b (by omega), hQ.quart c d a b (by omega)]
        simp
      rw [hz, zero_mul, zero_mul]
  simp only [LoopQuartic.hess, h1, h2]

/-- **The `eS 1` contraction depends only on the loop-`0` components of the point.** -/
theorem faceId_cTwoG_eS1_congr0 (hQ : LoopDegLe 1 2 Q) {X X' : LoopIndex → ℂ}
    (hX : ∀ c : LoopIndex, c.1 = 0 → X c = X' c) : cTwoG Q (eS 1) X = cTwoG Q (eS 1) X' := by
  unfold cTwoG
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a.1 = 1 ∧ b.1 = 1
  · rw [faceId_hess_congr0 hQ hX hab.1 hab.2]
  · have : gMet (eS 1) a b = 0 := by simp [gMet, eS, hab]
    rw [this]
    simp

theorem faceId_gMet_cross (G : Matrix (Fin 2) (Fin 2) ℝ) (R : ℂ) (x y z w : LoopIndex)
    (hq : 2 < loopInd 1 x + loopInd 1 y + loopInd 1 z + loopInd 1 w → R = 0) :
    R * ((gMet G x y : ℂ) * (gMet (eS 1) z w : ℂ)) =
      ((G 0 0 : ℝ) : ℂ) * (R * ((gMet (eS 0) x y : ℂ) * (gMet (eS 1) z w : ℂ))) := by
  by_cases hzw : z.1 = 1 ∧ w.1 = 1
  · have iz := loopInd_of_eq hzw.1
    have iw := loopInd_of_eq hzw.2
    by_cases hxy : x.1 = 0 ∧ y.1 = 0
    · simp only [gMet, hxy.1, hxy.2, eS]
      push_cast
      simp
      ring
    · have : R = 0 := by
        refine hq ?_
        rcases faceId_fin_two x.1 with hx | hx
        · rcases faceId_fin_two y.1 with hy | hy
          · exact absurd ⟨hx, hy⟩ hxy
          · rw [loopInd_of_eq hy]; omega
        · rw [loopInd_of_eq hx]; omega
      simp [this]
  · have : gMet (eS 1) z w = 0 := by simp [gMet, eS, hzw]
    simp [this]

/-- **The cross quartic contraction with `eS 1`** of a quartic of loop-`1` degree `≤ 2` sees only
the `(0, 0)` entry of the other matrix. -/
theorem faceId_cFourX_eS1 (hQ : LoopDegLe 1 2 Q) (G : Matrix (Fin 2) (Fin 2) ℝ) :
    cFourX Q G (eS 1) = ((G 0 0 : ℝ) : ℂ) * cFourX Q (eS 0) (eS 1) := by
  unfold cFourX
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  have hq : ∀ i j k l : LoopIndex, loopInd 1 i + loopInd 1 j + loopInd 1 k + loopInd 1 l =
      loopInd 1 a + loopInd 1 b + loopInd 1 c + loopInd 1 d →
      2 < loopInd 1 i + loopInd 1 j + loopInd 1 k + loopInd 1 l → Q.quart a b c d = 0 :=
    fun i j k l e h => hQ.quart a b c d (by omega)
  have t1 := faceId_gMet_cross G (Q.quart a b c d) a b c d (hq _ _ _ _ (by omega))
  have t2 := faceId_gMet_cross G (Q.quart a b c d) c d a b (hq _ _ _ _ (by omega))
  have t3 := faceId_gMet_cross G (Q.quart a b c d) a c b d (hq _ _ _ _ (by omega))
  have t4 := faceId_gMet_cross G (Q.quart a b c d) b d a c (hq _ _ _ _ (by omega))
  have t5 := faceId_gMet_cross G (Q.quart a b c d) a d b c (hq _ _ _ _ (by omega))
  have t6 := faceId_gMet_cross G (Q.quart a b c d) b c a d (hq _ _ _ _ (by omega))
  simp only [pairX]
  push_cast
  linear_combination t1 + t2 + t3 + t4 + t5 + t6

/-- **The cross contraction `(eS 0, eS 1)` is the `eS 0` contraction of twice the half
Laplacian.** -/
theorem faceId_cFourX_eS0_eS1 (Q : LoopQuartic) (X : LoopIndex → ℂ) :
    cFourX Q (eS 0) (eS 1) = 2 * cTwoG (faceIdLap Q) (eS 0) X := by
  have h := sum_mul_matPair_add Q.quart (gMet (eS 1)) (gMet (eS 0))
  have hm : ∀ a b c d, (matPair (gMet (eS 1) + gMet (eS 0)) a b c d : ℂ) =
      (matPair (gMet (eS 1)) a b c d : ℂ) + (matPair (gMet (eS 0)) a b c d : ℂ) +
        (pairX (gMet (eS 0)) (gMet (eS 1)) a b c d : ℂ) := fun a b c d => by
    simp only [matPair, pairX, Matrix.add_apply]
    push_cast
    ring
  simp only [hm, mul_add, Finset.sum_add_distrib] at h
  have hX : cFourX Q (eS 0) (eS 1) = ∑ a, ∑ b, ∑ c, ∑ d, (Q.quart a b c d +
      Q.quart a c b d + Q.quart a c d b + Q.quart c a b d + Q.quart c a d b + Q.quart c d a b) *
      ((gMet (eS 1) a b * gMet (eS 0) c d : ℝ) : ℂ) := by
    unfold cFourX
    linear_combination h
  rw [hX]
  simp only [cTwoG, faceId_hess_faceIdLap]
  simp only [faceIdLap, LoopQuartic.quartSym, Finset.mul_sum, Finset.sum_mul]
  rw [← sum_comm4]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

theorem faceId_cFourG_faceIdLap (Q : LoopQuartic) (G : Matrix (Fin 2) (Fin 2) ℝ) :
    cFourG (faceIdLap Q) G = 0 := by
  simp [cFourG, faceIdLap]

theorem faceId_cTwoG_faceIdLap_of_quart (hq : Q.quart = 0) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (X : LoopIndex → ℂ) : cTwoG (faceIdLap Q) G X = 0 := by
  simp only [cTwoG, faceId_hess_faceIdLap]
  simp [faceIdLap, LoopQuartic.quartSym, hq]

/-! ### The vertex face -/

theorem faceId_faceX_zero_loop0 (b : ℝ) (P₀ b₁ : Fin 4 → ℝ) (c : LoopIndex) (hc : c.1 = 0) :
    faceX 0 1 b 1 P₀ b₁ c = faceIdX0 P₀ c := by
  obtain ⟨c1, c2⟩ := c
  simp only at hc
  subst hc
  simp [faceX, faceIdX0, loopComp, shat, uHat]

theorem faceId_cTwoG_eS1_faceX (hQ : LoopDegLe 1 2 Q) (b : ℝ) (P₀ b₁ : Fin 4 → ℝ) :
    cTwoG Q (eS 1) (faceX 0 1 b 1 P₀ b₁) = 2 * (faceIdLap Q).evalC (faceIdX0 P₀) := by
  rw [faceId_evalC_faceIdLap, faceId_cTwoG_eS1_congr0 hQ (faceId_faceX_zero_loop0 b P₀ b₁)]
  ring

theorem faceId_cFourX_faceG (hQ : LoopDegLe 1 2 Q) (b : ℝ) (X : LoopIndex → ℂ) :
    cFourX Q (faceG 0 1 b 1) (eS 1) = 2 * cTwoG (faceIdLap Q) (eS 0) X := by
  rw [faceId_cFourX_eS1 hQ, faceId_cFourX_eS0_eS1 Q X]
  simp [faceG, uHat]

/-- **The vertex bracket at `ρ = 0`, integrated in `σ`** (seven lines), is the reduced bracket of
the half loop-`1` Laplacian with four lines. -/
theorem faceId_vtx_pt (hQ : LoopDegLe 1 2 Q) (b : ℝ) (P₀ b₁ : Fin 4 → ℝ) (v : ℝ) :
    ∑ j, (FaceBr.vtx 7 Q).C j 0 1 b 1 P₀ b₁ *
      (((v ^ ((FaceBr.vtx 7 Q).k j - 1) : ℝ) : ℂ)⁻¹ / (((FaceBr.vtx 7 Q).k j : ℂ) - 1)) =
      faceIdRedBr 4 (faceIdLap Q) (faceIdX0 P₀) v := by
  rw [Fin.sum_univ_three]
  simp only [FaceBr.vtx, faceIdRedBr]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ofReal_zero, zero_mul, zero_add, mul_zero]
  rw [faceId_cTwoG_eS1_faceX hQ, faceId_cFourX_faceG hQ b (faceIdX0 P₀),
    faceId_cFourG_faceIdLap]
  have hu : uHat 0 1 b 1 = 1 := by simp [uHat]
  simp only [hu, div_one, ofReal_one, one_mul]
  norm_num [Nat.factorial]
  ring

/-- **The two-term vertex bracket at `ρ = 0`, integrated in `σ`** (six lines, no quartic part),
is the reduced bracket of the half loop-`1` Laplacian with three lines. -/
theorem faceId_vtx₂_pt (hQ : LoopDegLe 1 2 Q) (hq : Q.quart = 0) (b : ℝ) (P₀ b₁ : Fin 4 → ℝ)
    (v : ℝ) :
    ∑ j, (FaceBr.vtx₂ 6 Q).C j 0 1 b 1 P₀ b₁ *
      (((v ^ ((FaceBr.vtx₂ 6 Q).k j - 1) : ℝ) : ℂ)⁻¹ / (((FaceBr.vtx₂ 6 Q).k j : ℂ) - 1)) =
      faceIdRedBr 3 (faceIdLap Q) (faceIdX0 P₀) v := by
  rw [Fin.sum_univ_two]
  simp only [FaceBr.vtx₂, faceIdRedBr]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ofReal_zero, zero_mul, zero_add,
    mul_zero]
  rw [faceId_cTwoG_eS1_faceX hQ, faceId_cTwoG_faceIdLap_of_quart hq, faceId_cFourG_faceIdLap]
  have hu : uHat 0 1 b 1 = 1 := by simp [uHat]
  simp only [hu, div_one, ofReal_one, one_mul]
  norm_num [Nat.factorial]
  left
  ring

theorem faceId_setIntegral_snd {p q : ℕ} (g : (Fin q → ℝ) → ℂ) :
    ∫ x in simplexSet p ×ˢ simplexSet q, g x.2 =
      ((volume (simplexSet p)).toReal : ℂ) * ∫ V in simplexSet q, g V := by
  rw [Measure.volume_eq_prod]
  have h := setIntegral_prod_mul (μ := volume) (ν := volume) (fun _ => (1 : ℂ)) g
    (simplexSet p) (simplexSet q)
  simp only [one_mul] at h
  rw [h, setIntegral_const]
  simp [Measure.real]

/-- **The vertex face value** (face block with two fermion lines and the photon), for a
representative of loop-`1` degree `≤ 2`: `vol(Δ₂)` times the reduced one-loop functional of the
half loop-`1` Laplacian, with `n - 3` lines. -/
theorem faceId_faceIdVal_vtx {q n : ℕ} (S : FaceShape (1 + 1) q) (hQ : LoopDegLe 1 2 Q)
    (hn : n = 7 ∨ (n = 6 ∧ Q.quart = 0)) :
    faceIdVal n S Q =
      ((volume (simplexSet (1 + 1))).toReal : ℂ) * S.faceIdRedVal (n - 3) (faceIdLap Q) := by
  rcases hn with rfl | ⟨rfl, hq⟩
  · have hv : faceIdVal 7 S Q = S.faceIdInt (FaceBr.vtx 7 Q) := by simp [faceIdVal]
    rw [hv, S.faceId_faceIdInt_eq _ rfl]
    simp_rw [faceId_vtx_pt hQ]
    exact faceId_setIntegral_snd (fun V => faceIdRedBr 4 (faceIdLap Q)
      (faceIdX0 (S.P0 (simplexPoint V))) (S.mR (simplexPoint V) -
        Minkowski.dot (S.P0 (simplexPoint V)) (S.P0 (simplexPoint V))))
  · have hv : faceIdVal 6 S Q = S.faceIdInt (FaceBr.vtx₂ 6 Q) := by simp [faceIdVal]
    rw [hv, S.faceId_faceIdInt_eq _ rfl]
    simp_rw [faceId_vtx₂_pt hQ hq]
    exact faceId_setIntegral_snd (fun V => faceIdRedBr 3 (faceIdLap Q)
      (faceIdX0 (S.P0 (simplexPoint V))) (S.mR (simplexPoint V) -
        Minkowski.dot (S.P0 (simplexPoint V)) (S.P0 (simplexPoint V))))

end QED.GradedProof.RPi4

end
