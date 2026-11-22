/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBPiece

/-!
# Set (a), stage B2: the Leibniz rule of the auxiliary-mass partial fractions

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B2. On the five-line
simplex `Δ₄` the fourteen merged pieces of a class density (`ksB_pieceA_merge`,
`ksB_pieceB_merge`) are divided differences, in the squared masses of the fermion lines, of the
five-line collapsed integrand. With `G`, `H` the integrands of the numerators at the masses `M`
and `X` (as functions of the four fermion masses), their sum is the Leibniz expansion of the
second divided difference of the diagonal, at the squared masses `(M², X², Y²)`, times
`(X² - M²)(Y² - M²)`, for a numerator affine in the squared mass:

* **`ksB_leibniz`**: `∑_{i ≤ j} (pieces A) + ∑ᵢ (pieces B) = G(M⁴) + (Y² - M²)/(X² - Y²) H(X⁴)
  + (Y² - M²)/(Y² - X²) H(Y⁴) - G(Y⁴)`.

This is an identity of finitely many values of `G` and `H`, for every function `G`, `H` of four
masses. The last three terms are affine in `M²`, so the flavour sum with the two Pauli–Villars
conditions removes them.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.SetAKS

open QED.GradedProof.VP2 (mA mB)

/-- The value of a function of four masses, as a function of the mass vector. -/
def ksBOf (G : ℝ → ℝ → ℝ → ℝ → ℂ) (mf : Fin 4 → ℝ) : ℂ := G (mf 0) (mf 1) (mf 2) (mf 3)

/-- **The Leibniz rule of the pieces.** The ten pieces `A` (lines `i ≤ j` doubled, masses
`mA M X Y i j`) and the four pieces `B` (line `i` doubled, masses `mB X Y i`) of a numerator
affine in the squared mass, merged on `Δ₄`, sum to the values on the diagonal. -/
theorem ksB_leibniz (G H : ℝ → ℝ → ℝ → ℝ → ℂ) {M X Y : ℝ} (hMX : M ^ 2 ≠ X ^ 2)
    (hMY : M ^ 2 ≠ Y ^ 2) (hXY : X ^ 2 ≠ Y ^ 2) :
    (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then
      ksBdd (fun mf' => ksBdd (fun mf => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ksBOf G mf) mf' i X) (mA M X Y i j) j Y else 0) +
    ∑ i : Fin 4, ksBdd (fun mf => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (ksBOf H mf - ksBOf G mf))
      (mB X Y i) i Y =
    G M M M M + ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) * H X X X X +
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) / ((Y : ℂ) ^ 2 - (X : ℂ) ^ 2) * H Y Y Y Y - G Y Y Y Y := by
  have h1 : ((M : ℂ) ^ 2 - (X : ℂ) ^ 2) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hMX
  have h2 : ((M : ℂ) ^ 2 - (Y : ℂ) ^ 2) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hMY
  have h3 : ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hXY
  have h3' : ((Y : ℂ) ^ 2 - (X : ℂ) ^ 2) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hXY.symm
  simp only [Fin.sum_univ_four, ksBdd, ksBOf, mA, mB, Function.update_apply]
  simp (config := { decide := true }) only [ite_true, ite_false]
  push_cast
  field_simp
  ring

end QED.ChainProof.SetAKS

end
