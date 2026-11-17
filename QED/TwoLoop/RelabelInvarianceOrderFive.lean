/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.RelabelInvariance
public import QED.TwoLoop.EnumerationOrderFive

/-!
# The order-`e⁵` vertex with coefficient one per class

Obligation O2-2 (section 3.3 of `docs/TWO-LOOP-DERIVATION.md`). Under momentum conservation
`pOut 0 = pIn 0 + kIn 0`, each of the nine classes of 1PI contractions of five gauge vertices
enters the order-`e⁵` part `onePIFunction₂ P 1 1 5 - onePIFunction₂ P 1 1 4` of the two-loop 1PI
function (T₁₁) with coefficient one and its sign: the `1/5!` is cancelled by the `5!`
relabellings of the representative, which all have the same value
(`QED.TwoLoop.Relabel.contractionValue₂_relabel_of_isOnePI`).

* `QED.TwoLoop.Relabel.onePIFunction₂_five_sub_four_eq`: the explicit finite sum with
  coefficient one per class, with no hypothesis other than momentum conservation.
-/

@[expose] public section

namespace QED.TwoLoop.Relabel

open QED.WickModel QED.TwoLoop.Enumeration

/-- **The order-`e⁵` 1PI vertex with coefficient one per class** (obligation O2-2): under
momentum conservation `pOut 0 = pIn 0 + kIn 0`, at every parameter set `P` and all spinor and
Lorentz indices, `onePIFunction₂ P 1 1 5 - onePIFunction₂ P 1 1 4` is the signed sum of the values
of the nine class representatives of five gauge vertices, plus the 1PI contractions with one
counterterm vertex, divided by `N!`. -/
theorem onePIFunction₂_five_sub_four_eq (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    onePIFunction₂ P 1 1 5 pOut pIn kIn αOut βIn μ -
        onePIFunction₂ P 1 1 4 pOut pIn kIn αOut βIn μ =
      ∑ c : Class5, (c.sign : ℂ) * contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ +
        (Nat.factorial 4 : ℂ)⁻¹ * (listValue P onePI_gggf pOut pIn kIn αOut βIn μ +
          listValue P onePI_gggp pOut pIn kIn αOut βIn μ +
          listValue P onePI_ggfg pOut pIn kIn αOut βIn μ +
          listValue P onePI_ggpg pOut pIn kIn αOut βIn μ +
          listValue P onePI_gfgg pOut pIn kIn αOut βIn μ +
          listValue P onePI_gpgg pOut pIn kIn αOut βIn μ +
          listValue P onePI_fggg pOut pIn kIn αOut βIn μ +
          listValue P onePI_pggg pOut pIn kIn αOut βIn μ) +
        (Nat.factorial 3 : ℂ)⁻¹ * (listValue P onePI_ggC pOut pIn kIn αOut βIn μ +
          listValue P onePI_gCg pOut pIn kIn αOut βIn μ +
          listValue P onePI_Cgg pOut pIn kIn αOut βIn μ) := by
  have hmom' : ∑ i, pOut i = ∑ i, pIn i + ∑ j, kIn j := by
    simp only [Fin.sum_univ_one, hmom]
  have hinv : ∀ (π : Equiv.Perm (Fin 5)) (c : Class5),
      contractionValue₂ P (relabel π c.rep) pOut pIn kIn αOut βIn μ =
        contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ := fun π c =>
    contractionValue₂_relabel_of_isOnePI P π (rep_isOnePI c) hmom' αOut βIn μ
  rw [onePIFunction₂_five_sub_four]
  congr 2
  simp only [hinv, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : (Nat.factorial 5 : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos 5).ne'
  field_simp

end QED.TwoLoop.Relabel

end
