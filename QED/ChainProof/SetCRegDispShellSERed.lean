/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSEPF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The photon products of the class `V` limit in two- and three-line blocks

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan (b1a). The limit
`QED.ChainProof.SetCRegDispSE.seProdLim` of a photon product passes any partial-fraction identity
of the product `∏ⱼ (D + Mⱼ²)⁻¹` (in `D = k² - iε`) to the limit (`seProdLim_eq_sum`). The
products of the class `V` limit (the masses `a = m_γ`, `b = Λ` of `d(k)²` and the spectral mass
`μ`) are reduced to the two-line blocks `![x, y]` (affine numerators, `k₀ = 0`) and the three-line
blocks `![a, a, b]`, `![a, b, b]`, `![a, b, μ]` (quadratic numerator, `k₀ = 1`), with `A = a²`,
`B = b²`, `U = μ²` pairwise distinct.

* **`seProdLim_eq_sum`**: the general transfer;
* `SEPFId`, `sePFId_*`: the partial-fraction identities (all with coefficients in `A, B, U`);
* `seProdLim_bab_red`, `seProdLim_abu_red`, `seProdLim_babu_red`, `seProdLim_ababu_red`: the
  affine reductions to two-line blocks;
* `seProdLim_abab_q_red`, `seProdLim_bab_q_red`, `seProdLim_babu_q_red`,
  `seProdLim_ababu_q_red`: the quadratic reductions to three-line blocks.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.OneLoop
open QED.TwoLoop.VPHalfAtLimit (massShift denom_eq_add_massShift denom_ne_zero_of_pos)
open QED.ChainProof.SetCRegDispSE (seProd seProdLim)
open QED.TwoLoop.VPUnitNested (EFInt)

/-- A partial-fraction identity of the photon product, on the region `Im D ≠ 0`. -/
def SEPFId {k j n : ℕ} (Ms : Fin (k + 2) → ℝ) (Bs : Fin n → Fin (j + 2) → ℝ) (c : Fin n → ℂ) :
    Prop :=
  ∀ D : ℂ, D.im ≠ 0 → ∏ x, (D + ((Ms x ^ 2 : ℝ) : ℂ))⁻¹ =
    ∑ i, c i * ∏ y, (D + ((Bs i y ^ 2 : ℝ) : ℂ))⁻¹

theorem add_ofReal_ne_zero {D : ℂ} (hD : D.im ≠ 0) (x : ℝ) : D + (x : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hD this

section Limit

variable {α : ℂ} {N : (Fin 4 → ℝ) → ℂ} {m M₀ K : ℝ} {Pv : Fin 4 → ℝ} {k₀ : ℕ}
  (hE : SEEngU N m M₀ Pv K k₀) (hL : SELimU α N m M₀ Pv k₀)

include hE hL in
/-- **Partial fractions pass to the limit**: a partial-fraction identity of the photon products
gives the same identity between their limits `seProdLim`. -/
theorem seProdLim_eq_sum {k j n : ℕ} (hj : k₀ ≤ j) (hjk : j ≤ k) (hk3 : k ≤ 3)
    {Ms : Fin (k + 2) → ℝ} (hMs : ∀ x, M₀ ≤ Ms x) {Bs : Fin n → Fin (j + 2) → ℝ}
    (hBs : ∀ i y, M₀ ≤ Bs i y) {c : Fin n → ℂ} (hid : SEPFId Ms Bs c) :
    seProdLim α N m Ms Pv = ∑ i, c i * seProdLim α N m (Bs i) Pv := by
  have hlim := hL k (hj.trans hjk) hk3 Ms hMs _ tendsto_const_eps
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hsum := tendsto_efi_sum (c := fun i _ => c i)
    (X := fun i ε => seProd N m (Bs i) (fun _ => ε) ε Pv) (c₀ := c)
    (a := fun i => seProdLim α N m (Bs i) Pv) (l := 𝓝[>] (0 : ℝ))
    (by filter_upwards [hpos] with ε hε i
        exact (hE ε hε j hj (hjk.trans hk3) _ _ (hBs i) fun _ => hε).1)
    (fun i => hL j hj (hjk.trans hk3) (Bs i) (hBs i) _ tendsto_const_eps)
    (fun i => tendsto_const_nhds)
  refine tendsto_nhds_unique hlim (hsum.congr' ?_)
  filter_upwards [hpos] with ε hε
  congr 1
  funext ℓ
  set D : ℂ := ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) - (ε : ℂ) * I
  have hD : D.im ≠ 0 := by simp [D]; exact hε.ne'
  have hd : ∀ M : ℝ, denom M ε ℓ = D + ((M ^ 2 : ℝ) : ℂ) := fun M => by
    rw [denom_eq_add_massShift]; simp only [massShift, D]; ring
  simp only [seProd, hd]
  rw [hid D hD, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Limit

/-! ### The partial-fraction identities -/

section Identities

variable {a b μ : ℝ} (hAB : (a ^ 2 - b ^ 2 : ℂ) ≠ 0) (hAU : (a ^ 2 - μ ^ 2 : ℂ) ≠ 0)
  (hBU : (b ^ 2 - μ ^ 2 : ℂ) ≠ 0)

include hAB in
theorem sePFId_bab :
    SEPFId ![b, a, b] ![![b, b], ![a, b]]
      ![(a ^ 2 - b ^ 2 : ℂ)⁻¹,
        -(a ^ 2 - b ^ 2 : ℂ)⁻¹] := by
  intro D hD
  have h1 := add_ofReal_ne_zero hD (a ^ 2)
  have h2 := add_ofReal_ne_zero hD (b ^ 2)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one]
  push_cast at h1 h2 ⊢
  field_simp
  ring

include hAB in
theorem sePFId_abu :
    SEPFId ![a, b, μ] ![![a, μ], ![b, μ]]
      ![-(a ^ 2 - b ^ 2 : ℂ)⁻¹,
        (a ^ 2 - b ^ 2 : ℂ)⁻¹] := by
  intro D hD
  have h1 := add_ofReal_ne_zero hD (a ^ 2)
  have h2 := add_ofReal_ne_zero hD (b ^ 2)
  have h3 := add_ofReal_ne_zero hD (μ ^ 2)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one]
  push_cast at h1 h2 h3 ⊢
  field_simp
  ring

include hAB hBU in
theorem sePFId_babu :
    SEPFId ![b, a, b, μ] ![![b, b], ![a, μ], ![b, μ]]
      ![-((a ^ 2 - b ^ 2 : ℂ) * (b ^ 2 - μ ^ 2 : ℂ))⁻¹,
        ((a ^ 2 - b ^ 2 : ℂ) ^ 2)⁻¹,
        (a ^ 2 - 2 * b ^ 2 + μ ^ 2 : ℂ) /
          ((a ^ 2 - b ^ 2 : ℂ) ^ 2 * (b ^ 2 - μ ^ 2 : ℂ))] := by
  intro D hD
  have h1 := add_ofReal_ne_zero hD (a ^ 2)
  have h2 := add_ofReal_ne_zero hD (b ^ 2)
  have h3 := add_ofReal_ne_zero hD (μ ^ 2)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one]
  push_cast at h1 h2 h3 ⊢
  field_simp
  ring

include hAB hAU hBU in
theorem sePFId_ababu :
    SEPFId ![a, b, a, b, μ] ![![a, a], ![b, b], ![a, μ], ![b, μ]]
      ![-((a ^ 2 - b ^ 2 : ℂ) ^ 2 * (a ^ 2 - μ ^ 2 : ℂ))⁻¹,
        -((a ^ 2 - b ^ 2 : ℂ) ^ 2 * (b ^ 2 - μ ^ 2 : ℂ))⁻¹,
        (3 * a ^ 2 - b ^ 2 - 2 * μ ^ 2 : ℂ) /
          ((a ^ 2 - b ^ 2 : ℂ) ^ 3 * (a ^ 2 - μ ^ 2 : ℂ)),
        (a ^ 2 - 3 * b ^ 2 + 2 * μ ^ 2 : ℂ) /
          ((a ^ 2 - b ^ 2 : ℂ) ^ 3 * (b ^ 2 - μ ^ 2 : ℂ))] := by
  intro D hD
  have h1 := add_ofReal_ne_zero hD (a ^ 2)
  have h2 := add_ofReal_ne_zero hD (b ^ 2)
  have h3 := add_ofReal_ne_zero hD (μ ^ 2)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one]
  push_cast at h1 h2 h3 ⊢
  field_simp
  ring

include hAB in
theorem sePFId_abab_q :
    SEPFId ![a, b, a, b] ![![a, a, b], ![a, b, b]]
      ![-(a ^ 2 - b ^ 2 : ℂ)⁻¹,
        (a ^ 2 - b ^ 2 : ℂ)⁻¹] := by
  intro D hD
  have h1 := add_ofReal_ne_zero hD (a ^ 2)
  have h2 := add_ofReal_ne_zero hD (b ^ 2)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one]
  push_cast at h1 h2 ⊢
  field_simp
  ring

theorem sePFId_bab_q :
    SEPFId ![b, a, b] ![![a, b, b]]
      ![1] := by
  intro D hD
  have h1 := add_ofReal_ne_zero hD (a ^ 2)
  have h2 := add_ofReal_ne_zero hD (b ^ 2)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one]
  push_cast at h1 h2 ⊢
  field_simp
  ring

include hBU in
theorem sePFId_babu_q :
    SEPFId ![b, a, b, μ] ![![a, b, b], ![a, b, μ]]
      ![-(b ^ 2 - μ ^ 2 : ℂ)⁻¹,
        (b ^ 2 - μ ^ 2 : ℂ)⁻¹] := by
  intro D hD
  have h1 := add_ofReal_ne_zero hD (a ^ 2)
  have h2 := add_ofReal_ne_zero hD (b ^ 2)
  have h3 := add_ofReal_ne_zero hD (μ ^ 2)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one]
  push_cast at h1 h2 h3 ⊢
  field_simp
  ring

include hAB hAU hBU in
theorem sePFId_ababu_q :
    SEPFId ![a, b, a, b, μ] ![![a, a, b], ![a, b, b], ![a, b, μ]]
      ![((a ^ 2 - b ^ 2 : ℂ) * (a ^ 2 - μ ^ 2 : ℂ))⁻¹,
        -((a ^ 2 - b ^ 2 : ℂ) * (b ^ 2 - μ ^ 2 : ℂ))⁻¹,
        ((a ^ 2 - μ ^ 2 : ℂ) * (b ^ 2 - μ ^ 2 : ℂ))⁻¹] := by
  intro D hD
  have h1 := add_ofReal_ne_zero hD (a ^ 2)
  have h2 := add_ofReal_ne_zero hD (b ^ 2)
  have h3 := add_ofReal_ne_zero hD (μ ^ 2)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one]
  push_cast at h1 h2 h3 ⊢
  field_simp
  ring

end Identities

section Reductions

variable {α : ℂ} {N : (Fin 4 → ℝ) → ℂ} {m M₀ K : ℝ} {Pv : Fin 4 → ℝ} {k₀ : ℕ}
  (hE : SEEngU N m M₀ Pv K k₀) (hL : SELimU α N m M₀ Pv k₀) {a b μ : ℝ}
  (ha : M₀ ≤ a) (hb : M₀ ≤ b) (hμ : M₀ ≤ μ) (hAB : (a ^ 2 - b ^ 2 : ℂ) ≠ 0)
  (hAU : (a ^ 2 - μ ^ 2 : ℂ) ≠ 0) (hBU : (b ^ 2 - μ ^ 2 : ℂ) ≠ 0)

include hE hL ha hb hAB in
theorem seProdLim_bab_red (hk₀ : k₀ = 0) :
    seProdLim α N m ![b, a, b] Pv =
      ((a ^ 2 - b ^ 2 : ℂ)⁻¹) * seProdLim α N m ![b, b] Pv +
        (-(a ^ 2 - b ^ 2 : ℂ)⁻¹) * seProdLim α N m ![a, b] Pv := by
  rw [seProdLim_eq_sum hE hL (j := 0) (k := 1) (by omega) (by norm_num) (by norm_num)
    (fun x => by fin_cases x <;> simpa) (fun i y => by fin_cases i <;> fin_cases y <;> simpa)
    (sePFId_bab hAB)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

include hE hL ha hb hμ hAB in
theorem seProdLim_abu_red (hk₀ : k₀ = 0) :
    seProdLim α N m ![a, b, μ] Pv =
      (-(a ^ 2 - b ^ 2 : ℂ)⁻¹) * seProdLim α N m ![a, μ] Pv +
        ((a ^ 2 - b ^ 2 : ℂ)⁻¹) * seProdLim α N m ![b, μ] Pv := by
  rw [seProdLim_eq_sum hE hL (j := 0) (k := 1) (by omega) (by norm_num) (by norm_num)
    (fun x => by fin_cases x <;> simpa) (fun i y => by fin_cases i <;> fin_cases y <;> simpa)
    (sePFId_abu hAB)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

include hE hL ha hb hμ hAB hBU in
theorem seProdLim_babu_red (hk₀ : k₀ = 0) :
    seProdLim α N m ![b, a, b, μ] Pv =
      (-((a ^ 2 - b ^ 2 : ℂ) * (b ^ 2 - μ ^ 2 : ℂ))⁻¹) * seProdLim α N m ![b, b] Pv +
        (((a ^ 2 - b ^ 2 : ℂ) ^ 2)⁻¹) * seProdLim α N m ![a, μ] Pv +
        ((a ^ 2 - 2 * b ^ 2 + μ ^ 2 : ℂ) /
          ((a ^ 2 - b ^ 2 : ℂ) ^ 2 * (b ^ 2 - μ ^ 2 : ℂ))) * seProdLim α N m ![b, μ] Pv := by
  rw [seProdLim_eq_sum hE hL (j := 0) (k := 2) (by omega) (by norm_num) (by norm_num)
    (fun x => by fin_cases x <;> simpa) (fun i y => by fin_cases i <;> fin_cases y <;> simpa)
    (sePFId_babu hAB hBU)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

include hE hL ha hb hμ hAB hAU hBU in
theorem seProdLim_ababu_red (hk₀ : k₀ = 0) :
    seProdLim α N m ![a, b, a, b, μ] Pv =
      (-((a ^ 2 - b ^ 2 : ℂ) ^ 2 * (a ^ 2 - μ ^ 2 : ℂ))⁻¹) * seProdLim α N m ![a, a] Pv +
        (-((a ^ 2 - b ^ 2 : ℂ) ^ 2 * (b ^ 2 - μ ^ 2 : ℂ))⁻¹) * seProdLim α N m ![b, b] Pv +
        ((3 * a ^ 2 - b ^ 2 - 2 * μ ^ 2 : ℂ) /
          ((a ^ 2 - b ^ 2 : ℂ) ^ 3 * (a ^ 2 - μ ^ 2 : ℂ))) * seProdLim α N m ![a, μ] Pv +
        ((a ^ 2 - 3 * b ^ 2 + 2 * μ ^ 2 : ℂ) /
          ((a ^ 2 - b ^ 2 : ℂ) ^ 3 * (b ^ 2 - μ ^ 2 : ℂ))) * seProdLim α N m ![b, μ] Pv := by
  rw [seProdLim_eq_sum hE hL (j := 0) (k := 3) (by omega) (by norm_num) (by norm_num)
    (fun x => by fin_cases x <;> simpa) (fun i y => by fin_cases i <;> fin_cases y <;> simpa)
    (sePFId_ababu hAB hAU hBU)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

include hE hL ha hb hAB in
theorem seProdLim_abab_q_red (hk₀ : k₀ ≤ 1) :
    seProdLim α N m ![a, b, a, b] Pv =
      (-(a ^ 2 - b ^ 2 : ℂ)⁻¹) * seProdLim α N m ![a, a, b] Pv +
        ((a ^ 2 - b ^ 2 : ℂ)⁻¹) * seProdLim α N m ![a, b, b] Pv := by
  rw [seProdLim_eq_sum hE hL (j := 1) (k := 2) (by omega) (by norm_num) (by norm_num)
    (fun x => by fin_cases x <;> simpa) (fun i y => by fin_cases i <;> fin_cases y <;> simpa)
    (sePFId_abab_q hAB)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

include hE hL ha hb in
theorem seProdLim_bab_q_red (hk₀ : k₀ ≤ 1) :
    seProdLim α N m ![b, a, b] Pv =
      seProdLim α N m ![a, b, b] Pv := by
  rw [seProdLim_eq_sum hE hL (j := 1) (k := 1) (by omega) (by norm_num) (by norm_num)
    (fun x => by fin_cases x <;> simpa) (fun i y => by fin_cases i; fin_cases y <;> simpa)
    (sePFId_bab_q)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

include hE hL ha hb hμ hBU in
theorem seProdLim_babu_q_red (hk₀ : k₀ ≤ 1) :
    seProdLim α N m ![b, a, b, μ] Pv =
      (-(b ^ 2 - μ ^ 2 : ℂ)⁻¹) * seProdLim α N m ![a, b, b] Pv +
        ((b ^ 2 - μ ^ 2 : ℂ)⁻¹) * seProdLim α N m ![a, b, μ] Pv := by
  rw [seProdLim_eq_sum hE hL (j := 1) (k := 2) (by omega) (by norm_num) (by norm_num)
    (fun x => by fin_cases x <;> simpa) (fun i y => by fin_cases i <;> fin_cases y <;> simpa)
    (sePFId_babu_q hBU)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

include hE hL ha hb hμ hAB hAU hBU in
theorem seProdLim_ababu_q_red (hk₀ : k₀ ≤ 1) :
    seProdLim α N m ![a, b, a, b, μ] Pv =
      (((a ^ 2 - b ^ 2 : ℂ) * (a ^ 2 - μ ^ 2 : ℂ))⁻¹) * seProdLim α N m ![a, a, b] Pv +
        (-((a ^ 2 - b ^ 2 : ℂ) * (b ^ 2 - μ ^ 2 : ℂ))⁻¹) * seProdLim α N m ![a, b, b] Pv +
        (((a ^ 2 - μ ^ 2 : ℂ) * (b ^ 2 - μ ^ 2 : ℂ))⁻¹) * seProdLim α N m ![a, b, μ] Pv := by
  rw [seProdLim_eq_sum hE hL (j := 1) (k := 3) (by omega) (by norm_num) (by norm_num)
    (fun x => by fin_cases x <;> simpa) (fun i y => by fin_cases i <;> fin_cases y <;> simpa)
    (sePFId_ababu_q hAB hAU hBU)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

end Reductions

end QED.ChainProof.SetCRegDisp

end
