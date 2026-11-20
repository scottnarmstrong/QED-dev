/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4LoopDeg
public import QED.GradedProof.RPi4UnifLip

/-!
# (R-Π₄) step L6d2: the contractions with a general matrix, and their face expansion

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2. On a face of
loop `s` the inverse Symanzik matrix is `A⁻¹ = Ĝ + t Eₛ` with `Ĝ` bounded, `Eₛ` the unit matrix
at `(s, s)` and `t ≍ ρ⁻¹`. The contractions are linear (`contractTwo`) and quadratic
(`contractFour`) in `A⁻¹`, so they are written with a general matrix `G` in place of `A⁻¹`:

* `gMet G` (the loop metric `η_{μν} G_{st}`), `cTwoG Q G X`, `cFourG Q G`, and the cross term
  `cFourX Q G E` of `cFourG` at `G + t E`; `contractTwo_eq_cTwoG`, `contractFour_eq_cFourG`;
* `cTwoG_add_smul`, `cFourG_add_smul`: the expansion in `t`;
* `cTwoG_eS`, `cFourX_eS` (degree `≤ 1` along loop `s`) and `cFourG_eS` (degree `≤ 2`): the
  terms with `Eₛ` that vanish;
* `UnifLip.evalC`, `UnifLip.hess`, `UnifLip.cTwoG`, `UnifLip.cFourG`, `UnifLip.cFourX`: the
  contractions of uniformly Lipschitz data are uniformly Lipschitz.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

/-! ### Contractions with a general matrix -/

/-- The loop metric `η_{μν} G_{st}` of a `2 × 2` matrix `G` (in place of `A⁻¹`). -/
noncomputable def gMet (G : Matrix (Fin 2) (Fin 2) ℝ) : Matrix LoopIndex LoopIndex ℝ :=
  fun a b => Minkowski.metric a.2 b.2 * G a.1 b.1

theorem loopMetricInv_eq_gMet (A : Matrix (Fin 2) (Fin 2) ℝ) : loopMetricInv A = gMet A⁻¹ := rfl

/-- The quadratic contraction with `G` in place of `A⁻¹`. -/
noncomputable def cTwoG (Q : LoopQuartic) (G : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) :
    ℂ :=
  ∑ a, ∑ b, Q.hess X a b * (gMet G a b : ℂ)

/-- The quartic contraction with `G` in place of `A⁻¹`. -/
noncomputable def cFourG (Q : LoopQuartic) (G : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, Q.quart a b c d * (matPair (gMet G) a b c d : ℂ)

/-- The six pairings with one factor `G` and one factor `E`. -/
def pairX (G E : Matrix LoopIndex LoopIndex ℝ) (a b c d : LoopIndex) : ℝ :=
  G a b * E c d + E a b * G c d + G a c * E b d + E a c * G b d + G a d * E b c + E a d * G b c

/-- The cross term of the quartic contraction. -/
noncomputable def cFourX (Q : LoopQuartic) (G E : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, Q.quart a b c d * (pairX (gMet G) (gMet E) a b c d : ℂ)

theorem contractTwo_eq_cTwoG (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X : LoopIndex → ℂ) : Q.contractTwo A X = cTwoG Q A⁻¹ X := rfl

theorem contractFour_eq_cFourG (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Q.contractFour A = cFourG Q A⁻¹ := rfl

section Expand

variable (Q : LoopQuartic) (G E : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)

theorem gMet_add_smul (a b : LoopIndex) :
    gMet (G + t • E) a b = gMet G a b + t * gMet E a b := by
  simp only [gMet, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem cTwoG_add_smul (X : LoopIndex → ℂ) :
    cTwoG Q (G + t • E) X = cTwoG Q G X + t * cTwoG Q E X := by
  simp only [cTwoG, gMet_add_smul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

theorem cFourG_add_smul :
    cFourG Q (G + t • E) = cFourG Q G + t * cFourX Q G E + t ^ 2 * cFourG Q E := by
  simp only [cFourG, cFourX, matPair, pairX, gMet_add_smul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  push_cast
  ring

end Expand

/-! ### The terms with the unit matrix at `(s, s)` -/

/-- The unit matrix at `(s, s)`. -/
def eS (s : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ := fun r t => if r = s ∧ t = s then 1 else 0

theorem gMet_eS_eq_zero {s : Fin 2} {a b : LoopIndex} (h : loopInd s a + loopInd s b ≤ 1) :
    gMet (eS s) a b = 0 := by
  have : ¬(a.1 = s ∧ b.1 = s) := fun hab => by
    rw [loopInd_of_eq hab.1, loopInd_of_eq hab.2] at h; omega
  simp [gMet, eS, this]

variable {s : Fin 2} {Q : LoopQuartic}

theorem LoopDegLe.mono {d d' : ℕ} (h : LoopDegLe s d Q) (hd : d ≤ d') : LoopDegLe s d' Q where
  lin a ha := h.lin a (by omega)
  quad a b ha := h.quad a b (by omega)
  cub a b c ha := h.cub a b c (by omega)
  quart a b c e ha := h.quart a b c e (by omega)

theorem cTwoG_eS (hQ : LoopDegLe s 1 Q) (X : LoopIndex → ℂ) : cTwoG Q (eS s) X = 0 := by
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  by_cases hab : a.1 = s ∧ b.1 = s
  · rw [hess_eq_zero_of_loopDeg hQ X hab.1 hab.2, zero_mul]
  · have : gMet (eS s) a b = 0 := by simp [gMet, eS, hab]
    rw [this, ofReal_zero, mul_zero]

theorem cFourX_eS (hQ : LoopDegLe s 1 Q) (G : Matrix (Fin 2) (Fin 2) ℝ) :
    cFourX Q G (eS s) = 0 := by
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
  by_cases hq : 1 < loopInd s a + loopInd s b + loopInd s c + loopInd s d
  · rw [hQ.quart a b c d hq, zero_mul]
  · have h := fun x y (hxy : loopInd s x + loopInd s y ≤ 1) => gMet_eS_eq_zero (s := s) hxy
    simp only [pairX]
    rw [h c d (by omega), h a b (by omega), h b d (by omega), h a c (by omega),
      h b c (by omega), h a d (by omega)]
    simp

theorem cFourG_eS (hQ : LoopDegLe s 2 Q) : cFourG Q (eS s) = 0 := by
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
  by_cases hq : 2 < loopInd s a + loopInd s b + loopInd s c + loopInd s d
  · rw [hQ.quart a b c d hq, zero_mul]
  · have h1 := loopInd_le_one s a
    have h2 := loopInd_le_one s b
    have h3 := loopInd_le_one s c
    have h4 := loopInd_le_one s d
    have h := fun x y (hxy : loopInd s x + loopInd s y ≤ 1) => gMet_eS_eq_zero (s := s) hxy
    have key : matPair (gMet (eS s)) a b c d = 0 := by
      simp only [matPair]
      have e1 : gMet (eS s) a b * gMet (eS s) c d = 0 := by
        rcases Nat.lt_or_ge (loopInd s a + loopInd s b) 2 with hab | hab
        · rw [h a b (by omega), zero_mul]
        · rw [h c d (by omega), mul_zero]
      have e2 : gMet (eS s) a c * gMet (eS s) b d = 0 := by
        rcases Nat.lt_or_ge (loopInd s a + loopInd s c) 2 with hab | hab
        · rw [h a c (by omega), zero_mul]
        · rw [h b d (by omega), mul_zero]
      have e3 : gMet (eS s) a d * gMet (eS s) b c = 0 := by
        rcases Nat.lt_or_ge (loopInd s a + loopInd s d) 2 with hab | hab
        · rw [h a d (by omega), zero_mul]
        · rw [h b c (by omega), mul_zero]
      rw [e1, e2, e3]
      ring
    rw [key, ofReal_zero, mul_zero]

/-! ### Uniformly Lipschitz contractions -/

namespace UnifLip

variable {ι : Type*} {ρ₀ : ℝ}

theorem evalC (Q : LoopQuartic) {X : ι → ℝ → LoopIndex → ℂ}
    (hX : ∀ a, UnifLip ρ₀ fun i ρ => X i ρ a) : UnifLip ρ₀ fun i ρ => Q.evalC (X i ρ) := by
  unfold LoopQuartic.evalC
  have h1 : UnifLip ρ₀ fun i ρ => ∑ a, Q.lin a * X i ρ a :=
    sum _ fun a _ => (const _).mul (hX a)
  have h2 : UnifLip ρ₀ fun i ρ => ∑ a, ∑ b, Q.quad a b * (X i ρ a * X i ρ b) :=
    sum _ fun a _ => sum _ fun b _ => (const _).mul ((hX a).mul (hX b))
  have h3 : UnifLip ρ₀ fun i ρ => ∑ a, ∑ b, ∑ c, Q.cub a b c * (X i ρ a * X i ρ b * X i ρ c) :=
    sum _ fun a _ => sum _ fun b _ => sum _ fun c _ =>
      (const _).mul (((hX a).mul (hX b)).mul (hX c))
  have h4 : UnifLip ρ₀ fun i ρ => ∑ a, ∑ b, ∑ c, ∑ d,
      Q.quart a b c d * (X i ρ a * X i ρ b * X i ρ c * X i ρ d) :=
    sum _ fun a _ => sum _ fun b _ => sum _ fun c _ => sum _ fun d _ =>
      (const _).mul ((((hX a).mul (hX b)).mul (hX c)).mul (hX d))
  exact (((((const _).add h1).add h2).add h3).add h4)

theorem hess (Q : LoopQuartic) {X : ι → ℝ → LoopIndex → ℂ}
    (hX : ∀ a, UnifLip ρ₀ fun i ρ => X i ρ a) (a b : LoopIndex) :
    UnifLip ρ₀ fun i ρ => Q.hess (X i ρ) a b := by
  unfold LoopQuartic.hess
  exact ((const _).add (sum _ fun c _ => (const _).mul (hX c))).add
    (sum _ fun c _ => sum _ fun d _ => (const _).mul ((hX c).mul (hX d)))

theorem gMet {G : ι → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : ∀ r t, UnifLip ρ₀ fun i ρ => ((G i ρ r t : ℝ) : ℂ)) (a b : LoopIndex) :
    UnifLip ρ₀ fun i ρ => ((RPi4.gMet (G i ρ) a b : ℝ) : ℂ) := by
  simp only [RPi4.gMet, ofReal_mul]
  exact (const _).mul (hG _ _)

theorem cTwoG (Q : LoopQuartic) {G : ι → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {X : ι → ℝ → LoopIndex → ℂ} (hG : ∀ r t, UnifLip ρ₀ fun i ρ => ((G i ρ r t : ℝ) : ℂ))
    (hX : ∀ a, UnifLip ρ₀ fun i ρ => X i ρ a) :
    UnifLip ρ₀ fun i ρ => RPi4.cTwoG Q (G i ρ) (X i ρ) :=
  sum _ fun a _ => sum _ fun b _ => (hess Q hX a b).mul (gMet hG a b)

theorem cFourG (Q : LoopQuartic) {G : ι → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : ∀ r t, UnifLip ρ₀ fun i ρ => ((G i ρ r t : ℝ) : ℂ)) :
    UnifLip ρ₀ fun i ρ => RPi4.cFourG Q (G i ρ) := by
  unfold RPi4.cFourG matPair
  push_cast
  have g := gMet hG
  exact sum _ fun a _ => sum _ fun b _ => sum _ fun c _ => sum _ fun d _ =>
    (const _).mul ((((g a b).mul (g c d)).add ((g a c).mul (g b d))).add ((g a d).mul (g b c)))

theorem cFourX (Q : LoopQuartic) {G E : ι → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : ∀ r t, UnifLip ρ₀ fun i ρ => ((G i ρ r t : ℝ) : ℂ))
    (hE : ∀ r t, UnifLip ρ₀ fun i ρ => ((E i ρ r t : ℝ) : ℂ)) :
    UnifLip ρ₀ fun i ρ => RPi4.cFourX Q (G i ρ) (E i ρ) := by
  unfold RPi4.cFourX pairX
  push_cast
  have g := gMet hG
  have e := gMet hE
  exact sum _ fun a _ => sum _ fun b _ => sum _ fun c _ => sum _ fun d _ =>
    (const _).mul ((((((g a b).mul (e c d)).add ((e a b).mul (g c d))).add
      ((g a c).mul (e b d))).add ((e a c).mul (g b d))).add ((g a d).mul (e b c)) |>.add
      ((e a d).mul (g b c)))

end UnifLip

end QED.GradedProof.RPi4

end
