/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecUStar

/-!
# Set (a), obligation (N): the class matching `hsum`

Helper level for obligation (N) of `QED.ChainProof.SetAPauli.SetALimitLink`: the hypothesis
`hsum` of `QED.ChainProof.SetANest.familyVertex_setA_eq_nested`.

In the outer vertex chain `QED.ChainProof.SetANest.nestInt` the photon momentum `ℓ` leaves the
insertion at its field `x` (index `a`, towards the open-line vertex `a`) and enters at `y` (index
`b`). With the external photon `0` of a two-photon class at `x` and `1` at `y`, the incoming
momenta of the class are `(-ℓ, ℓ)`: the inner tensor of a loop class `R` is
`X_R(ℓ)^{ab} = (1/i) val0(C_R)(-ℓ)^{ab}`, `C_R` the matching two-photon class (`GW ↦ G0`,
`GU ↦ G1`, and the fermion and vertex-type classes up to the orientation of the loop, i.e. up
to the mirrors `FA ↔ FB`, `VA ↔ VC`).

* `SAUTerm.val_neg`, `SAUTerm.val_swap`, **`SAUForm.neg_swap`**: an `ε`-uniform spectral tensor
  form (`QED.ChainProof.SetASpec.SAUForm`) is even in `k` and symmetric in its indices on
  `ε ∈ (0, 1]` (its terms are `g^{μν}` or `k^μ k^ν` times functions of `k²`).
* **`val0_neg_swap`**: hence, under the hypotheses of T★ᵤ
  (`QED.ChainProof.SetASpec.setASpecU_vacuumPolarizationPart_two_form`), each of the seven
  two-photon class values is even in `k` and symmetric in `(μ, ν)` at every `ε ∈ (0, 1]`.
* **`hsum_of_groups`**: if the inner tensors of the three groups of loop classes (vertex-type,
  `gaugeCt`, `fermionCt`) sum to `(1/i)` times the values of the matching two-photon classes at
  `-ℓ`, the hypothesis `hsum` holds. Any bijection inside a group (the mirrors) is allowed.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.ChainProof.SetANest

open QED.ChainProof.SetASpec QED.GradedProof.VP2 QED.Graded

theorem dot_neg_self (k : Fin 4 → ℝ) : Minkowski.dot (-k) (-k) = Minkowski.dot k k :=
  QED.TwoLoop.CountertermMirror.dot_neg_neg k

theorem saTens_neg (t : Bool) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    saTens t (-k) μ ν = saTens t k μ ν := by
  cases t <;> simp [saTens]

theorem saTens_swap (t : Bool) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    saTens t k ν μ = saTens t k μ ν := by
  cases t
  · simp only [saTens, Minkowski.metric]
    split_ifs <;> simp_all [eq_comm]
  · simp only [saTens, mul_comm]

theorem fDen_neg (M ε x : ℝ) (k : Fin 4 → ℝ) :
    QED.TwoLoop.VPHalfAtAssembly.fDen M ε x (-k) = QED.TwoLoop.VPHalfAtAssembly.fDen M ε x k := by
  simp only [QED.TwoLoop.VPHalfAtAssembly.fDen, dot_neg_self]

theorem SAUTerm.val_neg (τ : SAUTerm) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    τ.val ε (-k) μ ν = τ.val ε k μ ν := by
  simp only [SAUTerm.val, saTens_neg, dot_neg_self, fDen_neg]

theorem SAUTerm.val_swap (τ : SAUTerm) (ε : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    τ.val ε k ν μ = τ.val ε k μ ν := by
  simp only [SAUTerm.val, saTens_swap]

/-- **A uniform spectral tensor form is even and symmetric** on `ε ∈ (0, 1]`. -/
theorem SAUForm.neg_swap {Mlo : ℝ} {W : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hW : SAUForm Mlo W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    W ε (-k) μ ν = W ε k μ ν ∧ W ε k ν μ = W ε k μ ν := by
  obtain ⟨l, -, hl⟩ := hW
  rw [hl ε hε hε1, hl ε hε hε1, hl ε hε hε1]
  simp only [SAUTerm.val_neg, SAUTerm.val_swap, and_self]

/-- **Each two-photon class value is even in `k` and symmetric in `(μ, ν)`**, at every
`ε ∈ (0, 1]`, under the hypotheses of T★ᵤ. -/
theorem val0_neg_swap (P : QED.WickModel.Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) {m₀ : ℝ} (hε : 0 < P.ε) (hε1 : P.ε ≤ 1)
    {N : ℕ} {κ : Fin N → Wick.VertexKind}
    {C : QED.WickModel.Contraction 0 2 κ}
    (hC : SAUForm (min m₀ (min P.mγ P.Λ)) fun ε k a b => val0 { P with ε := ε } Φ D k a b C)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    val0 P Φ D (-k) μ ν C = val0 P Φ D k μ ν C ∧ val0 P Φ D k ν μ C = val0 P Φ D k μ ν C :=
  SAUForm.neg_swap hC hε hε1 k μ ν

section Classes

variable (P : QED.WickModel.Params) {F : Type} [Fintype F] [DecidableEq F]
  (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ)
  (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
    D.dm f 0 = D.dm (rep f) 0)
include hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD

/-- The seven two-photon class values have the uniform spectral tensor form (the classwise
content of T★ᵤ). -/
theorem saUForm_val0_seven :
    let Mlo := min m₀ (min P.mγ P.Λ)
    SAUForm Mlo (fun ε k a b => val0 { P with ε := ε } Φ D k a b repVA) ∧
      SAUForm Mlo (fun ε k a b => val0 { P with ε := ε } Φ D k a b repVB) ∧
      SAUForm Mlo (fun ε k a b => val0 { P with ε := ε } Φ D k a b repVC) ∧
      SAUForm Mlo (fun ε k a b => val0 { P with ε := ε } Φ D k a b repG0) ∧
      SAUForm Mlo (fun ε k a b => val0 { P with ε := ε } Φ D k a b repG1) ∧
      SAUForm Mlo (fun ε k a b => val0 { P with ε := ε } Φ D k a b repF0) ∧
      SAUForm Mlo (fun ε k a b => val0 { P with ε := ε } Φ D k a b repF1) := by
  intro Mlo
  have hlo0 : 0 ≤ Mlo := le_min hm₀.le (le_min hmγ.le hΛ.le)
  have hlo : Mlo ≤ m₀ := min_le_left _ _
  have hloγ : Mlo ≤ P.mγ := (min_le_right _ _).trans (min_le_left _ _)
  have hloΛ : Mlo ≤ P.Λ := (min_le_right _ _).trans (min_le_right _ _)
  have hD1 : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 := fun f => (hD f).1
  have hD2 : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 := fun f => (hD f).2
  refine ⟨?_, ?_, ?_, saUForm_val0_repG0 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hlo hD1,
    saUForm_val0_repG1 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hlo hD1,
    saUForm_val0_repF0 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD2 hlo0 hlo,
    saUForm_val0_repF1 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD2 hlo0 hlo⟩
  · exact (saUj_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hlo0 hlo hloγ hloΛ).2.congr
      fun ε hε _ k a b => (val0_repVA Φ D P hε.ne' k a b).symm
  · exact (saUj_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hlo0 hlo hloγ hloΛ).2.congr
      fun ε hε _ k a b => (val0_repVB Φ D P hε.ne' k a b).symm
  · exact (saUj_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hlo0 hlo hloγ hloΛ).2.congr
      fun ε hε _ k a b => (val0_repVC Φ D P hε.ne' k a b).symm

/-- **The class matching `hsum`.** At `ε ∈ (0, 1]`, under the hypotheses of T★ᵤ: if the inner
tensors of the vertex-type, `gaugeCt` and `fermionCt` loop classes sum, group by group, to `(1/i)`
times the values at `-ℓ` of the matching two-photon classes, then the seven tensors sum to `-i`
times the seven two-photon class values at `ℓ`, the hypothesis `hsum` of
`familyVertex_setA_eq_nested`. -/
theorem hsum_of_groups (hε : 0 < P.ε) (hε1 : P.ε ≤ 1)
    (XVA XVB XVC XGW XGU XFA XFB : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hV : ∀ ℓ a b, XVA ℓ a b + XVB ℓ a b + XVC ℓ a b = (1 / I) * (val0 P Φ D (-ℓ) a b repVA +
      val0 P Φ D (-ℓ) a b repVB + val0 P Φ D (-ℓ) a b repVC))
    (hG : ∀ ℓ a b, XGW ℓ a b + XGU ℓ a b =
      (1 / I) * (val0 P Φ D (-ℓ) a b repG0 + val0 P Φ D (-ℓ) a b repG1))
    (hF : ∀ ℓ a b, XFA ℓ a b + XFB ℓ a b =
      (1 / I) * (val0 P Φ D (-ℓ) a b repF0 + val0 P Φ D (-ℓ) a b repF1)) :
    ∀ ℓ a b, XVA ℓ a b + (XVB ℓ a b + (XVC ℓ a b + (XGW ℓ a b + (XGU ℓ a b +
        (XFA ℓ a b + XFB ℓ a b))))) =
      -(I * (val0 P Φ D ℓ a b repVA + val0 P Φ D ℓ a b repVB + val0 P Φ D ℓ a b repVC +
        val0 P Φ D ℓ a b repG0 + val0 P Φ D ℓ a b repG1 + val0 P Φ D ℓ a b repF0 +
        val0 P Φ D ℓ a b repF1)) := by
  intro ℓ a b
  obtain ⟨sVA, sVB, sVC, sG0, sG1, sF0, sF1⟩ :=
    saUForm_val0_seven P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD
  have e : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : QED.WickModel.Contraction 0 2 κ},
      SAUForm (min m₀ (min P.mγ P.Λ)) (fun ε k a b => val0 { P with ε := ε } Φ D k a b C) →
      val0 P Φ D (-ℓ) a b C = val0 P Φ D ℓ a b C := fun hC =>
    (val0_neg_swap P Φ D hε hε1 hC ℓ a b).1
  have h := congrArg₂ (· + ·) (hV ℓ a b) (congrArg₂ (· + ·) (hG ℓ a b) (hF ℓ a b))
  simp only [e sVA, e sVB, e sVC, e sG0, e sG1, e sF0, e sF1] at h
  rw [show XVA ℓ a b + (XVB ℓ a b + (XVC ℓ a b + (XGW ℓ a b + (XGU ℓ a b +
      (XFA ℓ a b + XFB ℓ a b))))) = XVA ℓ a b + XVB ℓ a b + XVC ℓ a b +
      (XGW ℓ a b + XGU ℓ a b + (XFA ℓ a b + XFB ℓ a b)) by ring, h, one_div, Complex.inv_I]
  ring

end Classes

end QED.ChainProof.SetANest

end
