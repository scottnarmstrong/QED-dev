/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceBrInst

/-!
# (R-Π₄) step L6d2: face coefficients uniformly Lipschitz over a family of numerators

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2. The numerator of a
piece depends on the external momentum `k(s)`, so the face analysis must be uniform over a family
of numerators `Q s` with uniformly bounded coefficients (`LQBdd`). This file repeats the
`UnifLip` closure of `RPi4FaceScale`/`RPi4FaceLip` with the numerator varying with the index, and
gives the hypothesis `FamHyp.hD` of `RPi4FaceRate` for the brackets `se`, `vtx`, `se₂`, `vtx₂`:

* `LQBdd`, `UnifLip.evalCF`, `hessF`, `cTwoGF`, `cFourGF`, `cFourXF`;
* `FaceData.unifLip_coeff_seF`, `FaceData.unifLip_coeff_vtxF`;
* **`unifLip_coefJ_se`**, **`unifLip_coefJ_vtx`**, **`unifLip_coefJ_se₂`**,
  **`unifLip_coefJ_vtx₂`** (families of face shapes and numerators).
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

/-- **A family of numerators with uniformly bounded coefficients.** -/
structure LQBdd {ι : Type*} (Q : ι → LoopQuartic) (B : ℝ) : Prop where
  const : ∀ i, ‖(Q i).const‖ ≤ B
  lin : ∀ i a, ‖(Q i).lin a‖ ≤ B
  quad : ∀ i a b, ‖(Q i).quad a b‖ ≤ B
  cub : ∀ i a b c, ‖(Q i).cub a b c‖ ≤ B
  quart : ∀ i a b c d, ‖(Q i).quart a b c d‖ ≤ B

namespace UnifLip

variable {ι : Type*} {ρ₀ BQ : ℝ} {Q : ι → LoopQuartic}

theorem evalCF (hQ : LQBdd Q BQ) {X : ι → ℝ → LoopIndex → ℂ}
    (hX : ∀ a, UnifLip ρ₀ fun i ρ => X i ρ a) : UnifLip ρ₀ fun i ρ => (Q i).evalC (X i ρ) := by
  unfold LoopQuartic.evalC
  have h1 : UnifLip ρ₀ fun i ρ => ∑ a, (Q i).lin a * X i ρ a :=
    sum _ fun a _ => (const_bdd _ fun i => hQ.lin i a).mul (hX a)
  have h2 : UnifLip ρ₀ fun i ρ => ∑ a, ∑ b, (Q i).quad a b * (X i ρ a * X i ρ b) :=
    sum _ fun a _ => sum _ fun b _ => (const_bdd _ fun i => hQ.quad i a b).mul ((hX a).mul (hX b))
  have h3 : UnifLip ρ₀ fun i ρ =>
      ∑ a, ∑ b, ∑ c, (Q i).cub a b c * (X i ρ a * X i ρ b * X i ρ c) :=
    sum _ fun a _ => sum _ fun b _ => sum _ fun c _ =>
      (const_bdd _ fun i => hQ.cub i a b c).mul (((hX a).mul (hX b)).mul (hX c))
  have h4 : UnifLip ρ₀ fun i ρ => ∑ a, ∑ b, ∑ c, ∑ d,
      (Q i).quart a b c d * (X i ρ a * X i ρ b * X i ρ c * X i ρ d) :=
    sum _ fun a _ => sum _ fun b _ => sum _ fun c _ => sum _ fun d _ =>
      (const_bdd _ fun i => hQ.quart i a b c d).mul ((((hX a).mul (hX b)).mul (hX c)).mul (hX d))
  exact ((((const_bdd _ hQ.const).add h1).add h2).add h3).add h4

theorem hessF (hQ : LQBdd Q BQ) {X : ι → ℝ → LoopIndex → ℂ}
    (hX : ∀ a, UnifLip ρ₀ fun i ρ => X i ρ a) (a b : LoopIndex) :
    UnifLip ρ₀ fun i ρ => (Q i).hess (X i ρ) a b := by
  unfold LoopQuartic.hess LoopQuartic.quartSym
  have hc : ∀ c, UnifLip ρ₀ fun i (_ : ℝ) =>
      (Q i).cub a b c + (Q i).cub a c b + (Q i).cub c a b := fun c =>
    ((const_bdd _ fun i => hQ.cub i a b c).add (const_bdd _ fun i => hQ.cub i a c b)).add
      (const_bdd _ fun i => hQ.cub i c a b)
  have hq : ∀ c d, UnifLip ρ₀ fun i (_ : ℝ) =>
      (Q i).quart a b c d + (Q i).quart a c b d + (Q i).quart a c d b + (Q i).quart c a b d +
        (Q i).quart c a d b + (Q i).quart c d a b := fun c d =>
    (((((const_bdd _ fun i => hQ.quart i a b c d).add (const_bdd _ fun i => hQ.quart i a c b d)).add
      (const_bdd _ fun i => hQ.quart i a c d b)).add (const_bdd _ fun i => hQ.quart i c a b d)).add
      (const_bdd _ fun i => hQ.quart i c a d b)).add (const_bdd _ fun i => hQ.quart i c d a b)
  exact ((const_bdd _ fun i => hQ.quad i a b).add (sum _ fun c _ => (hc c).mul (hX c))).add
    (sum _ fun c _ => sum _ fun d _ => (hq c d).mul ((hX c).mul (hX d)))

theorem cTwoGF (hQ : LQBdd Q BQ) {G : ι → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {X : ι → ℝ → LoopIndex → ℂ} (hG : ∀ r t, UnifLip ρ₀ fun i ρ => ((G i ρ r t : ℝ) : ℂ))
    (hX : ∀ a, UnifLip ρ₀ fun i ρ => X i ρ a) :
    UnifLip ρ₀ fun i ρ => RPi4.cTwoG (Q i) (G i ρ) (X i ρ) :=
  sum _ fun a _ => sum _ fun b _ => (hessF hQ hX a b).mul (gMet hG a b)

theorem cFourGF (hQ : LQBdd Q BQ) {G : ι → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : ∀ r t, UnifLip ρ₀ fun i ρ => ((G i ρ r t : ℝ) : ℂ)) :
    UnifLip ρ₀ fun i ρ => RPi4.cFourG (Q i) (G i ρ) := by
  unfold RPi4.cFourG matPair
  push_cast
  have g := gMet hG
  exact sum _ fun a _ => sum _ fun b _ => sum _ fun c _ => sum _ fun d _ =>
    (const_bdd _ fun i => hQ.quart i a b c d).mul
      ((((g a b).mul (g c d)).add ((g a c).mul (g b d))).add ((g a d).mul (g b c)))

theorem cFourXF (hQ : LQBdd Q BQ) {G E : ι → ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : ∀ r t, UnifLip ρ₀ fun i ρ => ((G i ρ r t : ℝ) : ℂ))
    (hE : ∀ r t, UnifLip ρ₀ fun i ρ => ((E i ρ r t : ℝ) : ℂ)) :
    UnifLip ρ₀ fun i ρ => RPi4.cFourX (Q i) (G i ρ) (E i ρ) := by
  unfold RPi4.cFourX pairX
  push_cast
  have g := gMet hG
  have e := gMet hE
  exact sum _ fun a _ => sum _ fun b _ => sum _ fun c _ => sum _ fun d _ =>
    (const_bdd _ fun i => hQ.quart i a b c d).mul
      ((((((g a b).mul (e c d)).add ((e a b).mul (g c d))).add
      ((g a c).mul (e b d))).add ((e a c).mul (g b d))).add ((g a d).mul (e b c)) |>.add
      ((e a d).mul (g b c)))

end UnifLip

/-! ### The coefficients of the brackets, over a family of numerators -/

section Coeff

variable {ι : Type*} {ρ₀ : ℝ} {a₀ a₁ b c : ι → ℝ} {P₀ P₁ b₁ : ι → Fin 4 → ℝ} {K c₀ BQ : ℝ}
  {Q : ι → LoopQuartic} (n : ℕ)

theorem FaceData.unifLip_coeff_seF (h : FaceData ρ₀ a₀ a₁ b c P₀ P₁ b₁ K c₀)
    (hQ : LQBdd Q BQ) :
    (UnifLip ρ₀ fun i ρ => ((n - 4).factorial : ℂ) *
      (Q i).evalC (faceX ρ (a₀ i + ρ * a₁ i) (b i) (c i) (fun μ => P₀ i μ + ρ * P₁ i μ) (b₁ i))) ∧
    (UnifLip ρ₀ fun i ρ => ((n - 5).factorial : ℂ) / 2 *
      cTwoG (Q i) (faceG ρ (a₀ i + ρ * a₁ i) (b i) (c i))
        (faceX ρ (a₀ i + ρ * a₁ i) (b i) (c i) (fun μ => P₀ i μ + ρ * P₁ i μ) (b₁ i))) ∧
    (UnifLip ρ₀ fun i ρ => ((n - 6).factorial : ℂ) / 4 *
      cFourG (Q i) (faceG ρ (a₀ i + ρ * a₁ i) (b i) (c i))) :=
  ⟨(UnifLip.const _).mul (UnifLip.evalCF hQ h.unifLip_faceX),
    (UnifLip.const _).mul (UnifLip.cTwoGF hQ h.unifLip_faceG h.unifLip_faceX),
    (UnifLip.const _).mul (UnifLip.cFourGF hQ h.unifLip_faceG)⟩

theorem FaceData.unifLip_coeff_vtxF (h : FaceData ρ₀ a₀ a₁ b c P₀ P₁ b₁ K c₀)
    (hQ : LQBdd Q BQ) :
    (UnifLip ρ₀ fun i ρ => ((n - 4).factorial : ℂ) * ((ρ : ℂ) *
      (Q i).evalC
        (faceX ρ (a₀ i + ρ * a₁ i) (b i) (c i) (fun μ => P₀ i μ + ρ * P₁ i μ) (b₁ i)))) ∧
    (UnifLip ρ₀ fun i ρ => ((n - 5).factorial : ℂ) / 2 *
      ((ρ : ℂ) * cTwoG (Q i) (faceG ρ (a₀ i + ρ * a₁ i) (b i) (c i))
        (faceX ρ (a₀ i + ρ * a₁ i) (b i) (c i) (fun μ => P₀ i μ + ρ * P₁ i μ) (b₁ i)) +
      (((a₀ i + ρ * a₁ i) / uHat ρ (a₀ i + ρ * a₁ i) (b i) (c i) : ℝ) : ℂ) *
        cTwoG (Q i) (eS 1)
          (faceX ρ (a₀ i + ρ * a₁ i) (b i) (c i) (fun μ => P₀ i μ + ρ * P₁ i μ) (b₁ i)))) ∧
    (UnifLip ρ₀ fun i ρ => ((n - 6).factorial : ℂ) / 4 *
      ((ρ : ℂ) * cFourG (Q i) (faceG ρ (a₀ i + ρ * a₁ i) (b i) (c i)) +
      (((a₀ i + ρ * a₁ i) / uHat ρ (a₀ i + ρ * a₁ i) (b i) (c i) : ℝ) : ℂ) *
        cFourX (Q i) (faceG ρ (a₀ i + ρ * a₁ i) (b i) (c i)) (eS 1))) :=
  ⟨(UnifLip.const _).mul (UnifLip.id.mul (UnifLip.evalCF hQ h.unifLip_faceX)),
    (UnifLip.const _).mul ((UnifLip.id.mul (UnifLip.cTwoGF hQ h.unifLip_faceG h.unifLip_faceX)).add
      (h.unifLip_a_div.mul (UnifLip.cTwoGF hQ (fun r t => unifLip_eS 1 r t) h.unifLip_faceX))),
    (UnifLip.const _).mul ((UnifLip.id.mul (UnifLip.cFourGF hQ h.unifLip_faceG)).add
      (h.unifLip_a_div.mul (UnifLip.cFourXF hQ h.unifLip_faceG fun r t => unifLip_eS 1 r t)))⟩

end Coeff

/-! ### The hypothesis `FamHyp.hD` for the four brackets -/

namespace FaceShape

open FaceBr

variable {ι : Type*} {p q : ℕ} (S : ι → FaceShape p q) {K ρ₀ BQ : ℝ}
  (hK : ∀ s, (S s).kF ≤ K) (hρ₁ : ρ₀ < 1) (n : ℕ) {Q : ι → LoopQuartic} (hQ : LQBdd Q BQ)
include hK hρ₁ hQ

theorem unifLip_coefJ_se (j : Fin 3) :
    UnifLip ρ₀ fun (i : ι × FaceIdx p q) ρ =>
      (S i.1).coefJ (se n (Q i.1)) j ρ (Wi i.2) (Vi i.2) := by
  have h := faceDataFam S hK hρ₁
  obtain ⟨h1, h2, h3⟩ := h.unifLip_coeff_seF n (hQ := fun_lqbdd hQ)
  have hU := h.unifLip_uHat_inv_sq
  have hP := UnifLip.id (ι := ι × FaceIdx p q) (ρ₀ := ρ₀) |>.pow (p - 1)
  fin_cases j
  · exact hU.mul (hP.mul h1)
  · exact hU.mul (hP.mul h2)
  · exact hU.mul (hP.mul h3)
where
  /-- The numerators indexed by the pair. -/
  fun_lqbdd {Q : ι → LoopQuartic} (hQ : LQBdd Q BQ) :
      LQBdd (fun i : ι × FaceIdx p q => Q i.1) BQ :=
    ⟨fun i => hQ.const i.1, fun i => hQ.lin i.1, fun i => hQ.quad i.1, fun i => hQ.cub i.1,
      fun i => hQ.quart i.1⟩

theorem unifLip_coefJ_vtx (j : Fin 3) :
    UnifLip ρ₀ fun (i : ι × FaceIdx p q) ρ =>
      (S i.1).coefJ (vtx n (Q i.1)) j ρ (Wi i.2) (Vi i.2) := by
  have h := faceDataFam S hK hρ₁
  obtain ⟨h1, h2, h3⟩ := h.unifLip_coeff_vtxF n (hQ := unifLip_coefJ_se.fun_lqbdd hQ)
  have hU := h.unifLip_uHat_inv_sq
  have hP := UnifLip.id (ι := ι × FaceIdx p q) (ρ₀ := ρ₀) |>.pow (p - 2)
  fin_cases j
  · exact hU.mul (hP.mul h1)
  · exact hU.mul (hP.mul h2)
  · exact hU.mul (hP.mul h3)

theorem unifLip_coefJ_se₂ (j : Fin 2) :
    UnifLip ρ₀ fun (i : ι × FaceIdx p q) ρ =>
      (S i.1).coefJ (se₂ n (Q i.1)) j ρ (Wi i.2) (Vi i.2) := by
  have h := faceDataFam S hK hρ₁
  obtain ⟨h1, h2, -⟩ := h.unifLip_coeff_seF n (hQ := unifLip_coefJ_se.fun_lqbdd hQ)
  have hU := h.unifLip_uHat_inv_sq
  have hP := UnifLip.id (ι := ι × FaceIdx p q) (ρ₀ := ρ₀) |>.pow (p - 1)
  fin_cases j
  · exact hU.mul (hP.mul h1)
  · exact hU.mul (hP.mul h2)

theorem unifLip_coefJ_vtx₂ (j : Fin 2) :
    UnifLip ρ₀ fun (i : ι × FaceIdx p q) ρ =>
      (S i.1).coefJ (vtx₂ n (Q i.1)) j ρ (Wi i.2) (Vi i.2) := by
  have h := faceDataFam S hK hρ₁
  obtain ⟨h1, h2, -⟩ := h.unifLip_coeff_vtxF n (hQ := unifLip_coefJ_se.fun_lqbdd hQ)
  have hU := h.unifLip_uHat_inv_sq
  have hP := UnifLip.id (ι := ι × FaceIdx p q) (ρ₀ := ρ₀) |>.pow (p - 2)
  fin_cases j
  · exact hU.mul (hP.mul h1)
  · exact hU.mul (hP.mul h2)

end FaceShape

end QED.GradedProof.RPi4

end
