/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecVCls
public import QED.ChainProof.SetASpecFCls
public import QED.ChainProof.SetASpecGCls
public import QED.GradedProof.VP2Weights

/-!
# Set (a): the fixed-`ε` spectral form `T★` of the two-loop vacuum polarization

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
At every parameter set with `ε = P.ε > 0`, under the hypotheses of (G-Π₂)
(`QED.GradedProof.VP2.vacuumPolarizationPart_two_existsUnique'`), the two-loop vacuum
polarization `Π⁽⁴⁾_ε(k)^{μν}` is, **for every `k ∈ ℝ⁴`**, a finite sum of spectral terms

`t(k)^{μν} (k²)ʲ ∫_Δ w(x) fDen(M(x), ε, ξ(x), k)^{-r}`,

`t = g` or `k k`, with integrable weights, masses `M ≥ M_lo = min(m₀, m_γ, Λ)`, Feynman parameters
`ξ ∈ (0, 1)` almost everywhere and `j + [t = k k] ≤ 2`.

* **`setASpec_vacuumPolarizationPart_two`**: `SAForm M_lo P.ε (Π⁽⁴⁾)`. By
  `QED.GradedProof.VP2.vacuumPolarizationPart_two_eq`, `Π⁽⁴⁾ = -e⁴ d₃(1) (k² g - k k) + i ∑_X v_X`:
  the counterterm is two constant terms (`saForm_ct`); `VA, VB, VC` are `saj_VA`, `saj_VB`,
  `saj_VC` through `val0_repVA`, …; `F0, F1` are `saForm_val0_repF0`, `saForm_val0_repF1`; `G0, G1`
  are `saForm_val0_repG0`, `saForm_val0_repG1`.
* `SAForm.exists_indexed`: an `SAForm` as a sum over a finite index type with mass squares
  `A ≥ M_lo²` everywhere (`A = max(M_lo, M)²`, equal to `M²` almost everywhere) and the factor
  `fDen(√A)^{-r}` written as a product of `r` copies;
* **`setASpec_vacuumPolarizationPart_two_spectral`**: `T★` in that indexed form.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.Graded QED.GradedProof.VP2 QED.TwoLoop.VPHalfAtAssembly
open QED.Integration.Feynman (simplexSet)
open QED.WickModel (Params)

/-- **`T★`, the fixed-`ε` spectral tensor form of `Π⁽⁴⁾_ε`.** -/
theorem setASpec_vacuumPolarizationPart_two (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0) (hε : 0 < P.ε) :
    SAForm (min m₀ (min P.mγ P.Λ)) P.ε fun k μ ν => vacuumPolarizationPart P Φ D 2 k μ ν := by
  set Mlo : ℝ := min m₀ (min P.mγ P.Λ) with hMlo
  have hlo0 : 0 ≤ Mlo := le_min hm₀.le (le_min hmγ.le hΛ.le)
  have hlo : Mlo ≤ m₀ := min_le_left _ _
  have hloγ : Mlo ≤ P.mγ := (min_le_right _ _).trans (min_le_left _ _)
  have hloΛ : Mlo ≤ P.Λ := (min_le_right _ _).trans (min_le_right _ _)
  have VA : SAForm Mlo P.ε fun k a b => val0 P Φ D k a b repVA :=
    ((saj_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hlo0 hlo hloγ hloΛ) P.ε hε).2.congr
      fun k a b => (val0_repVA Φ D P hε.ne' k a b).symm
  have VB : SAForm Mlo P.ε fun k a b => val0 P Φ D k a b repVB :=
    ((saj_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hlo0 hlo hloγ hloΛ) P.ε hε).2.congr
      fun k a b => (val0_repVB Φ D P hε.ne' k a b).symm
  have VC : SAForm Mlo P.ε fun k a b => val0 P Φ D k a b repVC :=
    ((saj_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hlo0 hlo hloγ hloΛ) P.ε hε).2.congr
      fun k a b => (val0_repVC Φ D P hε.ne' k a b).symm
  have hD1 : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 := fun f => (hD f).1
  have hD2 : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 := fun f => (hD f).2
  have G0 := saForm_val0_repG0 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hlo hε hD1
  have G1 := saForm_val0_repG1 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hlo hε hD1
  have F0 := saForm_val0_repF0 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD2 hlo0 hlo hε
  have F1 := saForm_val0_repF1 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD2 hlo0 hlo hε
  refine ((saForm_ct (P.e ^ 4 * D.d₃ 1)).add
    ((((((VA.add VB).add VC).add G0).add G1).add F0).add F1 |>.const_mul I)).congr
    fun k μ ν => ?_
  rw [vacuumPolarizationPart_two_eq]

/-! ### The indexed form -/

/-- **An `SAForm` as a sum over a finite index type.** -/
theorem SAForm.exists_indexed {Mlo ε : ℝ} (hMlo : 0 ≤ Mlo)
    {W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} (h : SAForm Mlo ε W) :
    ∃ (ι : Type) (_ : Fintype ι) (m j r : ι → ℕ) (t : ι → Bool)
      (w : ∀ τ, (Fin (m τ) → ℝ) → ℂ) (A ξ : ∀ τ, (Fin (m τ) → ℝ) → ℝ),
      (∀ τ, IntegrableOn (w τ) (simplexSet (m τ))) ∧
      (∀ τ, Measurable (A τ) ∧ Measurable (ξ τ)) ∧ (∀ τ x, Mlo ^ 2 ≤ A τ x) ∧
      (∀ τ, ∀ᵐ x ∂(volume.restrict (simplexSet (m τ))), ξ τ x ∈ Ioo (0 : ℝ) 1) ∧
      (∀ τ, j τ + (if t τ then 1 else 0) ≤ 2) ∧
      ∀ k μ ν, W k μ ν = ∑ τ, saTens (t τ) k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j τ *
        ∫ x in simplexSet (m τ), w τ x * ∏ _i : Fin (r τ), (fDen (√(A τ x)) ε (ξ τ x) k)⁻¹ := by
  obtain ⟨l, hl, hW⟩ := h
  have hg : ∀ τ : Fin l.length, (l.get τ).Good Mlo := fun τ => hl _ (List.get_mem l τ)
  refine ⟨Fin l.length, inferInstance, fun τ => (l.get τ).m, fun τ => (l.get τ).j,
    fun τ => (l.get τ).r, fun τ => (l.get τ).t, fun τ => (l.get τ).w,
    fun τ x => max Mlo ((l.get τ).mass x) ^ 2, fun τ => (l.get τ).xi,
    fun τ => (hg τ).1, fun τ => ⟨(measurable_const.max (hg τ).2.1).pow_const 2, (hg τ).2.2.1⟩,
    fun τ x => pow_le_pow_left₀ hMlo (le_max_left _ _) 2,
    fun τ => (hg τ).2.2.2.1.mono fun x hx => hx.2, fun τ => (hg τ).2.2.2.2, fun k μ ν => ?_⟩
  rw [hW k μ ν, ← Fin.sum_univ_fun_getElem]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← List.get_eq_getElem]
  simp only [SATerm.val]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [(hg τ).2.2.2.1] with x hx
  rw [Real.sqrt_sq (le_max_of_le_left hMlo), max_eq_right hx.1, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, inv_pow]

/-- **`T★` in indexed form**: the fixed-`ε` two-loop vacuum polarization at every `k` is a finite
sum of spectral terms with mass squares at least `M_lo² = min(m₀, m_γ, Λ)²`. -/
theorem setASpec_vacuumPolarizationPart_two_spectral (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0) (hε : 0 < P.ε) :
    ∃ (ι : Type) (_ : Fintype ι) (m j r : ι → ℕ) (t : ι → Bool)
      (w : ∀ τ, (Fin (m τ) → ℝ) → ℂ) (A ξ : ∀ τ, (Fin (m τ) → ℝ) → ℝ),
      (∀ τ, IntegrableOn (w τ) (simplexSet (m τ))) ∧
      (∀ τ, Measurable (A τ) ∧ Measurable (ξ τ)) ∧
      (∀ τ x, min m₀ (min P.mγ P.Λ) ^ 2 ≤ A τ x) ∧
      (∀ τ, ∀ᵐ x ∂(volume.restrict (simplexSet (m τ))), ξ τ x ∈ Ioo (0 : ℝ) 1) ∧
      (∀ τ, j τ + (if t τ then 1 else 0) ≤ 2) ∧
      ∀ k μ ν, vacuumPolarizationPart P Φ D 2 k μ ν =
        ∑ τ, saTens (t τ) k μ ν * ((Minkowski.dot k k : ℝ) : ℂ) ^ j τ *
          ∫ x in simplexSet (m τ), w τ x *
            ∏ _i : Fin (r τ), (fDen (√(A τ x)) P.ε (ξ τ x) k)⁻¹ :=
  (setASpec_vacuumPolarizationPart_two P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD
    hε).exists_indexed (le_min hm₀.le (le_min hmγ.le hΛ.le))

end QED.ChainProof.SetASpec

end
