/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecUChain
public import QED.ChainProof.SetASpecUFCls
public import QED.ChainProof.SetASpecUGCls
public import QED.ChainProof.SetASpecOuterTerm
public import QED.GradedProof.VP2Weights

/-!
# Set (a): the `ε`-uniform spectral form `T★ᵤ` of the two-loop vacuum polarization

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
Under the hypotheses of (G-Π₂) (`QED.GradedProof.VP2.vacuumPolarizationPart_two_existsUnique'`),
**one** list of spectral terms gives the two-loop vacuum polarization `Π⁽⁴⁾_ε(k)^{μν}` of
`{P with ε := ε}` for every `ε ∈ (0, 1]` and every `k ∈ ℝ⁴`:

`Π⁽⁴⁾_ε(k)^{μν} = ∑_τ t_τ(k)^{μν} (k²)^{j_τ} ∫_Δ w_τ(ε, x) fDen(√A_τ(x), ε, ξ_τ(x), k)^{-r_τ}`,

with the simplex dimension, `t`, `j`, `r`, the mass squares `A ≥ M_lo²` (everywhere) and the
parameters `ξ ∈ (0, 1)` (almost everywhere) independent of `ε`, `j + [t = k k] ≤ 2`, and weights
with one integrable majorant on `(0, 1]` converging almost everywhere as `ε → 0⁺`
(`M_lo = min(m₀, m_γ, Λ)`).

* **`setASpecU_vacuumPolarizationPart_two_form`**: `SAUForm M_lo (ε ↦ Π⁽⁴⁾_ε)`, from
  `QED.GradedProof.VP2.vacuumPolarizationPart_two_eq` and the uniform class lemmas;
* `SAUTerm.toOuter`: a uniform term as a `QED.ChainProof.SetASpec.SAOuterTerm` with
  `A = max(M_lo, M)²`;
* **`setASpecU_vacuumPolarizationPart_two`** (`T★ᵤ`): `Π⁽⁴⁾_ε = saOuterTensor L ε` for one list
  `L` of good outer terms with constant coefficients, the input of
  `QED.ChainProof.SetASpec.saOuterForm_list`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Real

namespace QED.ChainProof.SetASpec

open QED.Graded QED.GradedProof.VP2 QED.TwoLoop.VPHalfAtAssembly
open QED.Integration.Feynman (simplexSet)
open QED.WickModel (Params)

/-- **`T★ᵤ` as a uniform form**: `ε ↦ Π⁽⁴⁾_ε` is `SAUForm M_lo`. -/
theorem setASpecU_vacuumPolarizationPart_two_form (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0) :
    SAUForm (min m₀ (min P.mγ P.Λ)) fun ε k μ ν =>
      vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν := by
  set Mlo : ℝ := min m₀ (min P.mγ P.Λ) with hMlo
  have hlo0 : 0 ≤ Mlo := le_min hm₀.le (le_min hmγ.le hΛ.le)
  have hlo : Mlo ≤ m₀ := min_le_left _ _
  have hloγ : Mlo ≤ P.mγ := (min_le_right _ _).trans (min_le_left _ _)
  have hloΛ : Mlo ≤ P.Λ := (min_le_right _ _).trans (min_le_right _ _)
  have VA : SAUForm Mlo fun ε k a b => val0 { P with ε := ε } Φ D k a b repVA :=
    (saUj_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hlo0 hlo hloγ hloΛ).2.congr
      fun ε hε _ k a b => (val0_repVA Φ D P hε.ne' k a b).symm
  have VB : SAUForm Mlo fun ε k a b => val0 { P with ε := ε } Φ D k a b repVB :=
    (saUj_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hlo0 hlo hloγ hloΛ).2.congr
      fun ε hε _ k a b => (val0_repVB Φ D P hε.ne' k a b).symm
  have VC : SAUForm Mlo fun ε k a b => val0 { P with ε := ε } Φ D k a b repVC :=
    (saUj_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hlo0 hlo hloγ hloΛ).2.congr
      fun ε hε _ k a b => (val0_repVC Φ D P hε.ne' k a b).symm
  have hD1 : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 := fun f => (hD f).1
  have hD2 : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 := fun f => (hD f).2
  have G0 := saUForm_val0_repG0 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hlo hD1
  have G1 := saUForm_val0_repG1 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hlo hD1
  have F0 := saUForm_val0_repF0 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD2 hlo0 hlo
  have F1 := saUForm_val0_repF1 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD2 hlo0 hlo
  refine ((saUForm_ct (P.e ^ 4 * D.d₃ 1)).add
    ((((((VA.add VB).add VC).add G0).add G1).add F0).add F1 |>.const_mul I)).congr
    fun ε _ _ k μ ν => ?_
  rw [vacuumPolarizationPart_two_eq]

/-! ### The outer terms -/

/-- A uniform term as an outer term, with mass square `A = max(M_lo, M)²`. -/
noncomputable def SAUTerm.toOuter (Mlo : ℝ) (τ : SAUTerm) : SAOuterTerm :=
  ⟨τ.t, τ.j, τ.r, τ.m, fun x => max Mlo (τ.mass x) ^ 2, τ.xi, τ.w, τ.w₀⟩

theorem SAUTerm.good_toOuter {Mlo : ℝ} (hMlo : 0 ≤ Mlo) {τ : SAUTerm} (h : τ.Good Mlo) :
    (τ.toOuter Mlo).Good Mlo :=
  ⟨h.2.2.2.2.2, (measurable_const.max h.2.2.1).pow_const 2, h.2.2.2.1,
    fun _ => pow_le_pow_left₀ hMlo (le_max_left _ _) 2, h.2.2.2.2.1.mono fun _ hx => hx.2,
    h.1, h.2.1⟩

theorem SAUTerm.val_toOuter {Mlo : ℝ} (hMlo : 0 ≤ Mlo) {τ : SAUTerm} (h : τ.Good Mlo)
    (ε : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) : (τ.toOuter Mlo).val ε k a b = τ.val ε k a b := by
  simp only [SAOuterTerm.val, saSpecScalar, SAUTerm.val, toOuter]
  rw [mul_assoc]
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [h.2.2.2.2.1] with x hx
  rw [Real.sqrt_sq (le_max_of_le_left hMlo), max_eq_right hx.1]

/-- **`T★ᵤ`, the `ε`-uniform spectral form of `Π⁽⁴⁾_ε`**: one list `L` of outer terms, good at
`M_lo = min(m₀, m_γ, Λ)`, with constant coefficients, gives `Π⁽⁴⁾` at `{P with ε := ε}` for every
`ε ∈ (0, 1]` and every `k`. -/
theorem setASpecU_vacuumPolarizationPart_two (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0) :
    ∃ L : List (ℂ × SAOuterTerm), (∀ q ∈ L, q.2.Good (min m₀ (min P.mγ P.Λ))) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k a b,
        vacuumPolarizationPart { P with ε := ε } Φ D 2 k a b = saOuterTensor L ε k a b := by
  have hlo0 : 0 ≤ min m₀ (min P.mγ P.Λ) := le_min hm₀.le (le_min hmγ.le hΛ.le)
  obtain ⟨l, hl, hW⟩ := setASpecU_vacuumPolarizationPart_two_form P Φ D rep m₀ hm₀ hmass hmγ hΛ
    hrep hPV₁ hPV₂ hD
  refine ⟨l.map fun τ => (1, τ.toOuter (min m₀ (min P.mγ P.Λ))), fun q hq => ?_,
    fun ε h0 h1 k a b => ?_⟩
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hq
    exact SAUTerm.good_toOuter hlo0 (hl τ hτ)
  · rw [show vacuumPolarizationPart { P with ε := ε } Φ D 2 k a b = _ from hW ε h0 h1 k a b,
      saOuterTensor, List.map_map]
    congr 1
    refine List.map_congr_left fun τ hτ => ?_
    simp only [Function.comp_apply, one_mul]
    exact (SAUTerm.val_toOuter hlo0 (hl τ hτ) ε k a b).symm

end QED.ChainProof.SetASpec

end
