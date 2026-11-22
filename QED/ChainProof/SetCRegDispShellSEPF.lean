/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSELimG
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Partial fractions of the photon product in the limit of vanishing prescription

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan (the closed form
of the class `V` limit). The limits `QED.ChainProof.SetCRegDispSE.seProdLim` of the photon
products with masses `(m_γ, Λ, m_γ, Λ[, μ])` are reduced to products with fewer distinct
photon lines, so that no divided difference at repeated masses is needed. The identities hold at
every positive prescription when all photon prescriptions are equal, and pass to the limit by
uniqueness of limits.

* **`seProdLim_comp_perm`**: `seProdLim` is invariant under a permutation of the photon masses;
* **`seProdLim_pf`**: for `M₀² ≠ M₁²`,
  `seProdLim(Ms) = (seProdLim(Ms without M₁) - seProdLim(Ms without M₀)) / (M₁² - M₀²)`;
* **`seProdLim_abab`**: `seProdLim ![a, b, a, b]` (the photon `d(k)²`) in two-line blocks.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.OneLoop
open QED.TwoLoop.VPHalfAtLimit (massShift denom_eq_add_massShift denom_ne_zero_of_pos)
open QED.ChainProof.SetCRegDispSE (seProd seProdLim efi_const_mul_se
  energyFirstIntegral_sub_of_efInt tendsto_efi_of_eq_sub)
open QED.TwoLoop.VPUnitNested (EFInt)

/-! ### The identities at a fixed prescription -/

/-- The photon product is invariant under a permutation of the photon lines. -/
theorem seProd_comp_perm (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ)
    (σ : Equiv.Perm (Fin (k + 2))) (ε : ℝ) (P ℓ : Fin 4 → ℝ) :
    seProd N m (Ms ∘ σ) (es ∘ σ) ε P ℓ = seProd N m Ms es ε P ℓ := by
  simp only [seProd, Function.comp_apply]
  congr 2
  exact Equiv.prod_comp σ fun j => (denom (Ms j) (es j) ℓ)⁻¹

theorem prod_inv_denom_succ_succ {k : ℕ} (Ms es : Fin (k + 3) → ℝ) (ℓ : Fin 4 → ℝ) :
    ∏ j, (denom (Ms j) (es j) ℓ)⁻¹ = (denom (Ms 0) (es 0) ℓ)⁻¹ *
      ((denom (Ms 1) (es 1) ℓ)⁻¹ * ∏ j : Fin (k + 1),
        (denom (Ms j.succ.succ) (es j.succ.succ) ℓ)⁻¹) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  rfl

theorem prod_inv_denom_removeNth_one {k : ℕ} (Ms es : Fin (k + 3) → ℝ) (ℓ : Fin 4 → ℝ) :
    ∏ j, (denom (Fin.removeNth 1 Ms j) (Fin.removeNth 1 es j) ℓ)⁻¹ =
      (denom (Ms 0) (es 0) ℓ)⁻¹ * ∏ j : Fin (k + 1),
        (denom (Ms j.succ.succ) (es j.succ.succ) ℓ)⁻¹ := by
  rw [Fin.prod_univ_succ]
  have h0 : (1 : Fin (k + 3)).succAbove 0 = 0 := rfl
  have h1 : ∀ j : Fin (k + 1), (1 : Fin (k + 3)).succAbove j.succ = j.succ.succ := fun j => by
    rw [show (1 : Fin (k + 3)) = Fin.succ 0 from rfl, Fin.succ_succAbove_succ,
      Fin.succAbove_zero]
  simp only [Fin.removeNth, h0, h1]

theorem prod_inv_denom_tail {k : ℕ} (Ms es : Fin (k + 3) → ℝ) (ℓ : Fin 4 → ℝ) :
    ∏ j, (denom (Fin.tail Ms j) (Fin.tail es j) ℓ)⁻¹ =
      (denom (Ms 1) (es 1) ℓ)⁻¹ * ∏ j : Fin (k + 1),
        (denom (Ms j.succ.succ) (es j.succ.succ) ℓ)⁻¹ := by
  rw [Fin.prod_univ_succ]
  rfl

/-- **Partial fractions of the first two photon lines** at equal prescriptions. -/
theorem seProd_pf (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms : Fin (k + 3) → ℝ) {e : ℝ}
    (he : 0 < e) (hM : Ms 0 ^ 2 ≠ Ms 1 ^ 2) (ε : ℝ) (P ℓ : Fin 4 → ℝ) :
    seProd N m Ms (fun _ => e) ε P ℓ =
      ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ)⁻¹ *
          seProd N m (Fin.removeNth 1 Ms) (Fin.removeNth 1 fun _ => e) ε P ℓ -
        ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ)⁻¹ *
          seProd N m (Fin.tail Ms) (Fin.tail fun _ => e) ε P ℓ := by
  simp only [seProd]
  rw [prod_inv_denom_succ_succ, prod_inv_denom_removeNth_one, prod_inv_denom_tail]
  have h0 := denom_ne_zero_of_pos (M := Ms 0) he ℓ
  have h1 := denom_ne_zero_of_pos (M := Ms 1) he ℓ
  have hc : ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 (Ne.symm hM)
  have hd : denom (Ms 1) e ℓ - denom (Ms 0) e ℓ = ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ) := by
    rw [denom_eq_add_massShift, denom_eq_add_massShift]
    simp only [massShift]
    push_cast
    ring
  rw [← hd]
  have hc' : denom (Ms 1) e ℓ - denom (Ms 0) e ℓ ≠ 0 := hd ▸ hc
  field_simp

/-! ### Passing to the limit -/

section Limit

variable {α : ℂ} {N : (Fin 4 → ℝ) → ℂ} {m M₀ K : ℝ} {Pv : Fin 4 → ℝ} {k₀ : ℕ}
  (hE : SEEngU N m M₀ Pv K k₀) (hL : SELimU α N m M₀ Pv k₀)

theorem tendsto_const_eps : ∀ {n : ℕ} (j : Fin n),
    Tendsto (fun ε : ℝ => (fun _ : Fin n => ε) j) (𝓝[>] 0) (𝓝[>] 0) :=
  fun _ => tendsto_id

include hL in
/-- **`seProdLim` is invariant under a permutation of the photon masses.** -/
theorem seProdLim_comp_perm {k : ℕ} (hk : k₀ ≤ k) (hk3 : k ≤ 3) {Ms : Fin (k + 2) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (σ : Equiv.Perm (Fin (k + 2))) :
    seProdLim α N m (Ms ∘ σ) Pv = seProdLim α N m Ms Pv := by
  have h1 := hL k hk hk3 (Ms ∘ σ) (fun j => hMs (σ j)) _ tendsto_const_eps
  have h2 := hL k hk hk3 Ms hMs _ tendsto_const_eps
  refine tendsto_nhds_unique (h1.congr fun ε => ?_) h2
  congr 1
  funext ℓ
  exact seProd_comp_perm N m Ms (fun _ => ε) σ ε Pv ℓ

include hE hL in
/-- **Partial fractions in the limit**: for `M₀² ≠ M₁²`,
`seProdLim(Ms) = (seProdLim(removeNth 1 Ms) - seProdLim(tail Ms)) / (M₁² - M₀²)`. -/
theorem seProdLim_pf {k : ℕ} (hk : k₀ ≤ k) (hk3 : k + 1 ≤ 3) {Ms : Fin (k + 3) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (hM : Ms 0 ^ 2 ≠ Ms 1 ^ 2) :
    seProdLim α N m Ms Pv = ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ)⁻¹ *
      (seProdLim α N m (Fin.removeNth 1 Ms) Pv - seProdLim α N m (Fin.tail Ms) Pv) := by
  set c : ℂ := ((Ms 1 ^ 2 - Ms 0 ^ 2 : ℝ) : ℂ)⁻¹
  have hR : ∀ j, M₀ ≤ Fin.removeNth 1 Ms j := fun j => hMs _
  have hT : ∀ j, M₀ ≤ Fin.tail Ms j := le_tail_of_le hMs
  have hlim := hL (k + 1) (by omega) hk3 Ms hMs _ tendsto_const_eps
  have hA := hL k hk (by omega) _ hR _ tendsto_const_eps
  have hB := hL k hk (by omega) _ hT _ tendsto_const_eps
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have h := tendsto_efi_of_eq_sub (c := fun _ => (1 : ℂ))
    (X := fun ε => seProd N m Ms (fun _ => ε) ε Pv)
    (Y := fun ε ℓ => c * seProd N m (Fin.removeNth 1 Ms) (fun _ => ε) ε Pv ℓ)
    (Z := fun ε ℓ => c * seProd N m (Fin.tail Ms) (fun _ => ε) ε Pv ℓ) ?_ ?_ ?_
    ((hA.const_mul c).congr fun ε => (efi_const_mul_se c _).symm)
    ((hB.const_mul c).congr fun ε => (efi_const_mul_se c _).symm) tendsto_const_nhds
  · refine tendsto_nhds_unique hlim (h.congr fun ε => rfl) |>.trans ?_
    ring
  · filter_upwards [hpos] with ε hε ℓ
    rw [one_mul]
    exact seProd_pf N m Ms hε hM ε Pv ℓ
  · filter_upwards [hpos] with ε hε
    exact (hE ε hε k hk (by omega) _ _ hR fun _ => hε).1.const_mul c
  · filter_upwards [hpos] with ε hε
    exact (hE ε hε k hk (by omega) _ _ hT fun _ => hε).1.const_mul c


include hE hL in
/-- **The photon product `d_a(k)² d_b(k)²` in two-line blocks** (`k₀ = 0`, e.g. the affine
numerators): `seProdLim ![a, b, a, b] = (seProdLim ![a, a] + seProdLim ![b, b]
- 2 seProdLim ![a, b]) / (b² - a²)²`. -/
theorem seProdLim_abab (hk₀ : k₀ = 0) {a b : ℝ} (ha : M₀ ≤ a) (hb : M₀ ≤ b)
    (hab : a ^ 2 ≠ b ^ 2) :
    seProdLim α N m ![a, b, a, b] Pv = ((b ^ 2 - a ^ 2 : ℝ) : ℂ)⁻¹ ^ 2 *
      (seProdLim α N m ![a, a] Pv + seProdLim α N m ![b, b] Pv -
        2 * seProdLim α N m ![a, b] Pv) := by
  subst hk₀
  have h2 : ∀ x y : ℝ, M₀ ≤ x → M₀ ≤ y → ∀ j, M₀ ≤ (![x, y] : Fin 2 → ℝ) j := by
    intro x y hx hy j; fin_cases j <;> simpa
  have h3 : ∀ x y z : ℝ, M₀ ≤ x → M₀ ≤ y → M₀ ≤ z → ∀ j, M₀ ≤ (![x, y, z] : Fin 3 → ℝ) j := by
    intro x y z hx hy hz j; fin_cases j <;> simpa
  have h4 : ∀ j, M₀ ≤ (![a, b, a, b] : Fin 4 → ℝ) j := by
    intro j; fin_cases j <;> simpa
  -- the first step: `(a, b, a, b) → (a, a, b), (b, a, b)`
  have s1 := seProdLim_pf hE hL (k := 1) (Nat.zero_le _) (by norm_num) h4 hab
  have r1 : (Fin.removeNth 1 ![a, b, a, b] : Fin 3 → ℝ) = ![a, a, b] := by
    funext i; fin_cases i <;> rfl
  have t1 : (Fin.tail ![a, b, a, b] : Fin 3 → ℝ) = ![b, a, b] := by
    funext i; fin_cases i <;> rfl
  rw [r1, t1] at s1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at s1
  -- `(a, a, b) = (a, b, a) ∘ swap 1 2`, and `(a, b, a) → (a, a), (b, a)`
  have p1 : (![a, b, a] ∘ Equiv.swap (1 : Fin 3) 2 : Fin 3 → ℝ) = ![a, a, b] := by
    funext i; fin_cases i <;> rfl
  have q1 := seProdLim_comp_perm hL (k := 1) (Nat.zero_le _) (by norm_num) (h3 a b a ha hb ha)
    (Equiv.swap 1 2)
  rw [p1] at q1
  have s2 := seProdLim_pf hE hL (k := 0) le_rfl (by norm_num) (h3 a b a ha hb ha) hab
  have r2 : (Fin.removeNth 1 ![a, b, a] : Fin 2 → ℝ) = ![a, a] := by
    funext i; fin_cases i <;> rfl
  have t2 : (Fin.tail ![a, b, a] : Fin 2 → ℝ) = ![b, a] := by
    funext i; fin_cases i <;> rfl
  rw [r2, t2] at s2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at s2
  -- `(b, a, b) → (b, b), (a, b)`
  have hba : b ^ 2 ≠ a ^ 2 := Ne.symm hab
  have s3 := seProdLim_pf hE hL (k := 0) le_rfl (by norm_num) (h3 b a b hb ha hb) hba
  have r3 : (Fin.removeNth 1 ![b, a, b] : Fin 2 → ℝ) = ![b, b] := by
    funext i; fin_cases i <;> rfl
  have t3 : (Fin.tail ![b, a, b] : Fin 2 → ℝ) = ![a, b] := by
    funext i; fin_cases i <;> rfl
  rw [r3, t3] at s3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at s3
  -- `(b, a) = (a, b) ∘ swap 0 1`
  have p2 : (![a, b] ∘ Equiv.swap (0 : Fin 2) 1 : Fin 2 → ℝ) = ![b, a] := by
    funext i; fin_cases i <;> rfl
  have q2 := seProdLim_comp_perm hL (k := 0) le_rfl (by norm_num) (h2 a b ha hb)
    (Equiv.swap 0 1)
  rw [p2] at q2
  have hc : ((b ^ 2 - a ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hba
  have e : ((a ^ 2 - b ^ 2 : ℝ) : ℂ) = -((b ^ 2 - a ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e] at s3
  rw [s1, q1, s2, s3, q2]
  field_simp
  ring

end Limit

end QED.ChainProof.SetCRegDisp

end
