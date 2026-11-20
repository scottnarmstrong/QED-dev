/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceInv

/-!
# (R-Π₄) step L6d2: the rescaled face coefficients are Lipschitz in `ρ`

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2. In the join
coordinates of a face the rescaled data are affine in `ρ`: `a = a₀ + ρ a₁`, `β₀ = P₀ + ρ P₁`,
while `b`, `c`, `b₁` do not depend on `ρ`. With a uniform lower bound `Û ≥ c₀ > 0` every
coefficient of the rescaled brackets `faceBrSE`, `faceBrVtx` of `RPi4FaceInv` is then uniformly
bounded and uniformly Lipschitz at `ρ = 0` (`UnifLip`), which is the `ρ`-modulus needed by the
face lemma `norm_face_sub_le`, including on the vertex faces (the term `(a/Û) cTwoG E₁` carries
the order of `cTwoG` that the pointwise bound loses).

* `FaceData`: the uniform bounds on the data of a family;
* `unifLip_aff`, `unifLip_uHat_inv`, `unifLip_faceX`, `unifLip_faceG`, `unifLip_eS`;
* **`unifLip_coeff_se`**, **`unifLip_coeff_vtx`**: the three coefficients of each bracket;
* `unifLip_uHat_inv_sq`: the prefactor `Û⁻²`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

variable {ι : Type*} {ρ₀ : ℝ}

/-- **Uniform bounds on the rescaled face data of a family**: all entries bounded by `K`, and
`Û(ρ) ≥ c₀ > 0` on `[0, ρ₀]`, with `a = a₀ + ρ a₁` and `β₀ = P₀ + ρ P₁`. -/
structure FaceData (ρ₀ : ℝ) (a₀ a₁ b c : ι → ℝ) (P₀ P₁ b₁ : ι → Fin 4 → ℝ) (K c₀ : ℝ) :
    Prop where
  c₀_pos : 0 < c₀
  ha₀ : ∀ i, |a₀ i| ≤ K
  ha₁ : ∀ i, |a₁ i| ≤ K
  hb : ∀ i, |b i| ≤ K
  hc : ∀ i, |c i| ≤ K
  hP₀ : ∀ i μ, |P₀ i μ| ≤ K
  hP₁ : ∀ i μ, |P₁ i μ| ≤ K
  hb₁ : ∀ i μ, |b₁ i μ| ≤ K
  hU : ∀ i ρ, 0 ≤ ρ → ρ ≤ ρ₀ → c₀ ≤ uHat ρ (a₀ i + ρ * a₁ i) (b i) (c i)

theorem unifLip_ofReal_bdd (x : ι → ℝ) {K : ℝ} (hx : ∀ i, |x i| ≤ K) :
    UnifLip ρ₀ fun i (_ : ℝ) => ((x i : ℝ) : ℂ) :=
  UnifLip.const_bdd _ fun i => by rw [norm_real, Real.norm_eq_abs]; exact hx i

/-- An affine function of `ρ` with bounded coefficients. -/
theorem unifLip_aff (x y : ι → ℝ) {K : ℝ} (hx : ∀ i, |x i| ≤ K) (hy : ∀ i, |y i| ≤ K) :
    UnifLip ρ₀ fun i ρ => ((x i : ℝ) : ℂ) + (ρ : ℂ) * ((y i : ℝ) : ℂ) :=
  (unifLip_ofReal_bdd x hx).add (UnifLip.id.mul (unifLip_ofReal_bdd y hy))

variable {a₀ a₁ b c : ι → ℝ} {P₀ P₁ b₁ : ι → Fin 4 → ℝ} {K c₀ : ℝ}

theorem FaceData.unifLip_a (h : FaceData ρ₀ a₀ a₁ b c P₀ P₁ b₁ K c₀) :
    UnifLip ρ₀ fun i ρ => ((a₀ i : ℝ) : ℂ) + (ρ : ℂ) * ((a₁ i : ℝ) : ℂ) :=
  unifLip_aff a₀ a₁ h.ha₀ h.ha₁

theorem FaceData.unifLip_uHat (h : FaceData ρ₀ a₀ a₁ b c P₀ P₁ b₁ K c₀) :
    UnifLip ρ₀ fun i ρ => ((uHat ρ (a₀ i + ρ * a₁ i) (b i) (c i) : ℝ) : ℂ) := by
  simp only [uHat]
  push_cast
  exact ((unifLip_aff a₀ a₁ h.ha₀ h.ha₁).mul (unifLip_ofReal_bdd c h.hc)).sub
    (UnifLip.id.mul ((unifLip_ofReal_bdd b h.hb).pow 2))

/-- The inverse of `Û`. -/
theorem FaceData.unifLip_uHat_inv (h : FaceData ρ₀ a₀ a₁ b c P₀ P₁ b₁ K c₀) :
    UnifLip ρ₀ fun i ρ => ((uHat ρ (a₀ i + ρ * a₁ i) (b i) (c i) : ℝ) : ℂ)⁻¹ :=
  h.unifLip_uHat.inv h.c₀_pos fun i ρ hρ hρ' => by
    rw [norm_real, Real.norm_eq_abs]
    exact (h.hU i ρ hρ hρ').trans (le_abs_self _)

/-- The prefactor `Û⁻²`. -/
theorem FaceData.unifLip_uHat_inv_sq (h : FaceData ρ₀ a₀ a₁ b c P₀ P₁ b₁ K c₀) :
    UnifLip ρ₀ fun i ρ => ((uHat ρ (a₀ i + ρ * a₁ i) (b i) (c i) ^ 2 : ℝ) : ℂ)⁻¹ := by
  push_cast
  simpa only [inv_pow] using h.unifLip_uHat_inv.pow 2

theorem FaceData.unifLip_faceX (h : FaceData ρ₀ a₀ a₁ b c P₀ P₁ b₁ K c₀) (x : LoopIndex) :
    UnifLip ρ₀ fun i ρ =>
      faceX ρ (a₀ i + ρ * a₁ i) (b i) (c i) (fun μ => P₀ i μ + ρ * P₁ i μ) (b₁ i) x := by
  obtain ⟨s, μ⟩ := x
  have hB := fun i => h.hb₁ i μ
  fin_cases s
  · simp only [faceX, loopComp, shat, Pi.neg_apply, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero, ofReal_neg, ofReal_div]
    push_cast
    simp only [div_eq_mul_inv]
    exact ((((unifLip_ofReal_bdd c h.hc).mul (unifLip_aff (fun i => P₀ i μ) (fun i => P₁ i μ)
      (fun i => h.hP₀ i μ) (fun i => h.hP₁ i μ))).sub ((UnifLip.id.mul
        (unifLip_ofReal_bdd b h.hb)).mul (unifLip_ofReal_bdd _ hB))).mul
      h.unifLip_uHat_inv).neg
  · simp only [faceX, loopComp, shat, Pi.neg_apply, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_zero, ofReal_neg, ofReal_div]
    push_cast
    simp only [div_eq_mul_inv]
    exact (((h.unifLip_a.mul (unifLip_ofReal_bdd _ hB)).sub ((unifLip_ofReal_bdd b h.hb).mul
      (unifLip_aff (fun i => P₀ i μ) (fun i => P₁ i μ) (fun i => h.hP₀ i μ)
        (fun i => h.hP₁ i μ)))).mul h.unifLip_uHat_inv).neg

theorem FaceData.unifLip_faceG (h : FaceData ρ₀ a₀ a₁ b c P₀ P₁ b₁ K c₀) (r t : Fin 2) :
    UnifLip ρ₀ fun i ρ => ((faceG ρ (a₀ i + ρ * a₁ i) (b i) (c i) r t : ℝ) : ℂ) := by
  have hu := h.unifLip_uHat_inv
  fin_cases r <;> fin_cases t <;>
    simp only [faceG, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;> push_cast <;> (try simp only [div_eq_mul_inv])
  · exact (unifLip_ofReal_bdd c h.hc).mul hu
  · exact (unifLip_ofReal_bdd b h.hb).neg.mul hu
  · exact (unifLip_ofReal_bdd b h.hb).neg.mul hu
  · exact UnifLip.const 0

theorem unifLip_eS (s r t : Fin 2) :
    UnifLip ρ₀ fun (_ : ι) (_ : ℝ) => ((eS s r t : ℝ) : ℂ) :=
  UnifLip.const _

theorem FaceData.unifLip_a_div (h : FaceData ρ₀ a₀ a₁ b c P₀ P₁ b₁ K c₀) :
    UnifLip ρ₀ fun i ρ =>
      (((a₀ i + ρ * a₁ i) / uHat ρ (a₀ i + ρ * a₁ i) (b i) (c i) : ℝ) : ℂ) := by
  rw [show (fun i ρ => (((a₀ i + ρ * a₁ i) / uHat ρ (a₀ i + ρ * a₁ i) (b i) (c i) : ℝ) : ℂ)) =
    fun i ρ => ((a₀ i + ρ * a₁ i : ℝ) : ℂ) *
      ((uHat ρ (a₀ i + ρ * a₁ i) (b i) (c i) : ℝ) : ℂ)⁻¹ from by
    funext i ρ; rw [ofReal_div, div_eq_mul_inv]]
  have ha := h.unifLip_a
  simp only [← ofReal_mul, ← ofReal_add] at ha
  exact ha.mul h.unifLip_uHat_inv

/-! ### The coefficients of the brackets -/

variable (n : ℕ) (Q : LoopQuartic)

/-- **The coefficients of the self-energy bracket are uniformly Lipschitz in `ρ`.** -/
theorem FaceData.unifLip_coeff_se (h : FaceData ρ₀ a₀ a₁ b c P₀ P₁ b₁ K c₀) :
    (UnifLip ρ₀ fun i ρ => ((n - 4).factorial : ℂ) *
      Q.evalC (faceX ρ (a₀ i + ρ * a₁ i) (b i) (c i) (fun μ => P₀ i μ + ρ * P₁ i μ) (b₁ i))) ∧
    (UnifLip ρ₀ fun i ρ => ((n - 5).factorial : ℂ) / 2 *
      cTwoG Q (faceG ρ (a₀ i + ρ * a₁ i) (b i) (c i))
        (faceX ρ (a₀ i + ρ * a₁ i) (b i) (c i) (fun μ => P₀ i μ + ρ * P₁ i μ) (b₁ i))) ∧
    (UnifLip ρ₀ fun i ρ => ((n - 6).factorial : ℂ) / 4 *
      cFourG Q (faceG ρ (a₀ i + ρ * a₁ i) (b i) (c i))) :=
  ⟨(UnifLip.const _).mul (UnifLip.evalC Q h.unifLip_faceX),
    (UnifLip.const _).mul (UnifLip.cTwoG Q h.unifLip_faceG h.unifLip_faceX),
    (UnifLip.const _).mul (UnifLip.cFourG Q h.unifLip_faceG)⟩

/-- **The coefficients of the vertex bracket are uniformly Lipschitz in `ρ`.** -/
theorem FaceData.unifLip_coeff_vtx (h : FaceData ρ₀ a₀ a₁ b c P₀ P₁ b₁ K c₀) :
    (UnifLip ρ₀ fun i ρ => ((n - 4).factorial : ℂ) * ((ρ : ℂ) *
      Q.evalC (faceX ρ (a₀ i + ρ * a₁ i) (b i) (c i) (fun μ => P₀ i μ + ρ * P₁ i μ) (b₁ i)))) ∧
    (UnifLip ρ₀ fun i ρ => ((n - 5).factorial : ℂ) / 2 *
      ((ρ : ℂ) * cTwoG Q (faceG ρ (a₀ i + ρ * a₁ i) (b i) (c i))
        (faceX ρ (a₀ i + ρ * a₁ i) (b i) (c i) (fun μ => P₀ i μ + ρ * P₁ i μ) (b₁ i)) +
      (((a₀ i + ρ * a₁ i) / uHat ρ (a₀ i + ρ * a₁ i) (b i) (c i) : ℝ) : ℂ) *
        cTwoG Q (eS 1)
          (faceX ρ (a₀ i + ρ * a₁ i) (b i) (c i) (fun μ => P₀ i μ + ρ * P₁ i μ) (b₁ i)))) ∧
    (UnifLip ρ₀ fun i ρ => ((n - 6).factorial : ℂ) / 4 *
      ((ρ : ℂ) * cFourG Q (faceG ρ (a₀ i + ρ * a₁ i) (b i) (c i)) +
      (((a₀ i + ρ * a₁ i) / uHat ρ (a₀ i + ρ * a₁ i) (b i) (c i) : ℝ) : ℂ) *
        cFourX Q (faceG ρ (a₀ i + ρ * a₁ i) (b i) (c i)) (eS 1))) :=
  ⟨(UnifLip.const _).mul (UnifLip.id.mul (UnifLip.evalC Q h.unifLip_faceX)),
    (UnifLip.const _).mul ((UnifLip.id.mul (UnifLip.cTwoG Q h.unifLip_faceG h.unifLip_faceX)).add
      (h.unifLip_a_div.mul (UnifLip.cTwoG Q (fun r t => unifLip_eS 1 r t) h.unifLip_faceX))),
    (UnifLip.const _).mul ((UnifLip.id.mul (UnifLip.cFourG Q h.unifLip_faceG)).add
      (h.unifLip_a_div.mul (UnifLip.cFourX Q h.unifLip_faceG fun r t => unifLip_eS 1 r t)))⟩

end QED.GradedProof.RPi4

end
