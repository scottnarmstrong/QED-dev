/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkSEInput
public import QED.ChainProof.SetCLinkWard
public import QED.Frozen.Graded.IsRenormalizedThrough

/-!
# Set (c), model link: (G-ex-s) and (WI-s)

Provider-ready proofs of the two frozen goals of decision D-58 on the VP share, with exactly the
frozen statements:

* **`existsUnique_isVPShareOnShell_c`**: (G-ex-s) `QED.ThreeLoop.existsUnique_isVPShareOnShell`;
* **`isVPShareOnShell_d₁_eq_d₂_c`**: (WI-s) `QED.ThreeLoop.isVPShareOnShell_d₁_eq_d₂`.

The block Pauli–Villars conditions sum to the total ones (`GEx2.sum_eq_zero_of_blocks`); the
three inputs of `SetCLinkShareAlg` hold for the data `dZero D` (`vpSEInput`, `vpVInput`,
`vpWardInput`). The renormalization hypothesis `hD` is not used.
-/

@[expose] public section

open QED.WickModel (Params)

namespace QED.ChainProof.SetCLink

open QED.GradedProof

/-- **(G-ex-s)**, the frozen statement of `QED.ThreeLoop.existsUnique_isVPShareOnShell`. -/
theorem existsUnique_isVPShareOnShell_c (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (m₀ : ℝ) (he : P.e ≠ 0)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : Graded.IsRenormalizedThrough P Φ D rep 1) :
    ∃! s : ℝ × ℝ × ℝ, ThreeLoop.IsVPShareOnShell P Φ D s := by
  have h₁ := GEx2.sum_eq_zero_of_blocks rep hrep _ hPV₁
  have h₂ := GEx2.sum_eq_zero_of_blocks rep hrep _ hPV₂
  exact existsUnique_isVPShareOnShell_of_inputs P Φ D he (hm₀.trans_le (hmass _))
    (vpSEInput P Φ (dZero D) m₀ hm₀ hmass hmγ hΛ h₁ h₂)
    (vpVInput P Φ D m₀ hm₀ hmass hmγ hΛ h₁ h₂)

/-- **(WI-s)**, the frozen statement of `QED.ThreeLoop.isVPShareOnShell_d₁_eq_d₂`. -/
theorem isVPShareOnShell_d₁_eq_d₂_c (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (m₀ : ℝ) (he : P.e ≠ 0)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : Graded.IsRenormalizedThrough P Φ D rep 1) (s : ℝ × ℝ × ℝ)
    (hs : ThreeLoop.IsVPShareOnShell P Φ D s) : s.1 = s.2.1 := by
  have h₁ := GEx2.sum_eq_zero_of_blocks rep hrep _ hPV₁
  have h₂ := GEx2.sum_eq_zero_of_blocks rep hrep _ hPV₂
  exact isVPShareOnShell_d₁_eq_d₂_of_inputs P Φ D he (hm₀.trans_le (hmass _))
    (vpSEInput P Φ (dZero D) m₀ hm₀ hmass hmγ hΛ h₁ h₂)
    (vpVInput P Φ D m₀ hm₀ hmass hmγ hΛ h₁ h₂)
    (vpWardInput P Φ D m₀ hm₀ hmass hmγ hΛ h₁ h₂ he) s hs

end QED.ChainProof.SetCLink

end
