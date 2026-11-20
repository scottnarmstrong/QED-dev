/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRate

/-!
# (R-Π₄) step L6d2: the self-energy and vertex brackets satisfy the face hypotheses

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2. The brackets
`FaceBr.se n Q` and `FaceBr.vtx n Q` of the eight-line pieces (`n = 7`, exponents `4, 3, 2`) and
their two-term versions `FaceBr.se₂`, `FaceBr.vtx₂` for the seven-line pieces (`n = 6`, numerator
cubic so the `v^{-1}` term vanishes; exponents `3, 2`) satisfy the hypotheses of
`FaceShape.face_rate`: exponents `≥ 2` and measurable coefficients (the uniform Lipschitz bounds
are in `RPi4FaceFam`).

* `FaceBr.se₂`, `FaceBr.vtx₂`, `rep_se₂`, `rep_vtx₂` (from `Q.quart = 0`);
* `FaceBr.k_se`, `k_vtx`, `k_se₂`, `k_vtx₂`; `meas_se`, `meas_vtx`, `meas_se₂`, `meas_vtx₂`.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

namespace FaceBr

/-- The two-term self-energy bracket (numerator with no quartic part). -/
noncomputable def se₂ (n : ℕ) (Q : LoopQuartic) : FaceBr 2 where
  d := 1
  k := ![n - 3, n - 4]
  C := ![fun ρ a b c β₀ b₁ => ((n - 4).factorial : ℂ) * Q.evalC (faceX ρ a b c β₀ b₁),
    fun ρ a b c β₀ b₁ => ((n - 5).factorial : ℂ) / 2 *
      cTwoG Q (faceG ρ a b c) (faceX ρ a b c β₀ b₁)]

/-- The two-term vertex bracket (numerator with no quartic part). -/
noncomputable def vtx₂ (n : ℕ) (Q : LoopQuartic) : FaceBr 2 where
  d := 2
  k := ![n - 3, n - 4]
  C := ![fun ρ a b c β₀ b₁ => ((n - 4).factorial : ℂ) * ((ρ : ℂ) * Q.evalC (faceX ρ a b c β₀ b₁)),
    fun ρ a b c β₀ b₁ => ((n - 5).factorial : ℂ) / 2 *
      ((ρ : ℂ) * cTwoG Q (faceG ρ a b c) (faceX ρ a b c β₀ b₁) +
        ((a / uHat ρ a b c : ℝ) : ℂ) * cTwoG Q (eS 1) (faceX ρ a b c β₀ b₁))]

variable {n : ℕ} {Q : LoopQuartic}

theorem cFourG_of_quart (hq : Q.quart = 0) (G : Matrix (Fin 2) (Fin 2) ℝ) : cFourG Q G = 0 := by
  simp [cFourG, hq]

theorem cFourX_of_quart (hq : Q.quart = 0) (G E : Matrix (Fin 2) (Fin 2) ℝ) :
    cFourX Q G E = 0 := by
  simp [cFourX, hq]

theorem val_se₂ (hq : Q.quart = 0) (ρ a b c : ℝ) (β₀ b₁ : Fin 4 → ℝ) (v : ℝ) :
    (se₂ n Q).val ρ a b c β₀ b₁ v = (se n Q).val ρ a b c β₀ b₁ v := by
  simp only [val, se, se₂]
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  simp [cFourG_of_quart hq]

theorem val_vtx₂ (hq : Q.quart = 0) (ρ a b c : ℝ) (β₀ b₁ : Fin 4 → ℝ) (v : ℝ) :
    (vtx₂ n Q).val ρ a b c β₀ b₁ v = (vtx n Q).val ρ a b c β₀ b₁ v := by
  simp only [val, vtx, vtx₂]
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  simp [cFourG_of_quart hq, cFourX_of_quart hq]

variable {p m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {pp : Fin (m + 1) → Fin 4 → ℝ}

theorem rep_se₂ (hQ : LoopDegLe 1 1 Q) (hq : Q.quart = 0) (hp : 1 ≤ p) :
    (se₂ n Q).Rep n p Q α pp :=
  fun z ρ a b c b₁ h hρ hu hβ v => by
    rw [val_se₂ hq]; exact rep_se hQ hp z ρ a b c b₁ h hρ hu hβ v

theorem rep_vtx₂ (hQ : LoopDegLe 1 2 Q) (hq : Q.quart = 0) (hp : 2 ≤ p) :
    (vtx₂ n Q).Rep n p Q α pp :=
  fun z ρ a b c b₁ h hρ hu hβ v => by
    rw [val_vtx₂ hq]; exact rep_vtx hQ hp z ρ a b c b₁ h hρ hu hβ v

theorem k_se (hn : 7 ≤ n) (j : Fin 3) : 2 ≤ (se n Q).k j := by
  fin_cases j <;> simp [se] <;> omega

theorem k_vtx (hn : 7 ≤ n) (j : Fin 3) : 2 ≤ (vtx n Q).k j := by
  fin_cases j <;> simp [vtx] <;> omega

theorem k_se₂ (hn : 6 ≤ n) (j : Fin 2) : 2 ≤ (se₂ n Q).k j := by
  fin_cases j <;> simp [se₂] <;> omega

theorem k_vtx₂ (hn : 6 ≤ n) (j : Fin 2) : 2 ≤ (vtx₂ n Q).k j := by
  fin_cases j <;> simp [vtx₂] <;> omega

theorem meas_se : (se n Q).Meas := by
  intro j
  fin_cases j <;> simp only [se, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    simp only [faceX, shat, loopComp, uHat, LoopQuartic.evalC, cTwoG, cFourG,
      gMet, faceG, matPair, LoopQuartic.hess, LoopQuartic.quartSym] <;> fun_prop

theorem meas_vtx : (vtx n Q).Meas := by
  intro j
  fin_cases j <;> simp only [vtx, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    simp only [faceX, shat, loopComp, uHat, LoopQuartic.evalC, cTwoG, cFourG, cFourX, pairX,
      gMet, faceG, eS, matPair, LoopQuartic.hess, LoopQuartic.quartSym] <;> fun_prop

theorem meas_se₂ : (se₂ n Q).Meas := by
  intro j
  fin_cases j <;> simp only [se₂, Fin.zero_eta, Fin.mk_one, Matrix.cons_val] <;>
    simp only [faceX, shat, loopComp, uHat, LoopQuartic.evalC, cTwoG,
      gMet, faceG, LoopQuartic.hess, LoopQuartic.quartSym] <;> fun_prop

theorem meas_vtx₂ : (vtx₂ n Q).Meas := by
  intro j
  fin_cases j <;> simp only [vtx₂, Fin.zero_eta, Fin.mk_one, Matrix.cons_val] <;>
    simp only [faceX, shat, loopComp, uHat, LoopQuartic.evalC, cTwoG,
      gMet, faceG, eS, LoopQuartic.hess, LoopQuartic.quartSym] <;> fun_prop

end FaceBr

end QED.GradedProof.RPi4

end
