/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSERed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The flavour pieces of the class `V` limit in two- and three-line blocks

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S6 of the plan (b1a). The
limits `seL1`, `seL2`, `seL3` of `(k²)ʲ seProd` over the photon masses `a = m_γ`, `b = Λ` of
`d(k)²` (and the spectral mass `μ`) are expanded into the blocks of
`QED/ChainProof/SetCRegDispShellSERed.lean`: the two-line blocks `L(x, y) = seProdLim ![x, y]`
for numerators with `k₀ = 0` and the three-line blocks `Q(x, y, z) = seProdLim ![x, y, z]` for
numerators with `k₀ ≤ 1`. With `A = a²`, `B = b²`, `U = μ²` pairwise distinct:

* `seL1_abab_red`: `seL1 ![a,b,a,b] = (A-B)⁻² (-A L(a,a) - B L(b,b) + (A+B) L(a,b))`;
* `seL2_abab_red`: `seL2 ![a,b,a,b] = (A-B)⁻² (A² L(a,a) + B² L(b,b) - 2AB L(a,b))`;
* `seL3_ababu_red`: `seL3 ![a,b,a,b,μ]` in `L(a,a), L(b,b), L(a,μ), L(b,μ)` (no `L(a,b)`);
* `seL1_abab_q_red`, `seL2_ababu_q_red`: the quadratic analogues in `Q(a,a,b), Q(a,b,b)
  [, Q(a,b,μ)]`;
* **`sePieceLim_eq_blocks`**: the limit of one flavour piece of the class `V`,
  `sePieceLim = i c₁ w₁(x) (seAffBlk + seQuadBlk)` with
  `seAffBlk = -A²U/((A-B)²(A-U)) L(a,a) - B²U/((A-B)²(B-U)) L(b,b) - 2AB/(A-B)² L(a,b)
    + A²(2AB + AU - 3BU)/((A-B)³(A-U)) L(a,μ) - B²(2AB - 3AU + BU)/((A-B)³(B-U)) L(b,μ)`,
  `seQuadBlk = 2AU/((A-B)(A-U)) Q(a,a,b) - 2BU/((A-B)(B-U)) Q(a,b,b)
    + 2U²/((A-U)(B-U)) Q(a,b,μ)`.

These are the coefficients of the partial fractions of the dressed photon
`s² d(s)²/(s + U)` against the one-loop self-energy numerators.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel QED.OneLoop
open QED.TwoLoop.VPHalfAtAssembly (cOne wOne specMu)
open QED.ChainProof.SetCRegDispSE (seProdLim seL1 seL2 seL3)

section Generic

variable {α : ℂ} {N : (Fin 4 → ℝ) → ℂ} {m M₀ K : ℝ} {Pv : Fin 4 → ℝ} {k₀ : ℕ}
  (hE : SEEngU N m M₀ Pv K k₀) (hL : SELimU α N m M₀ Pv k₀) {a b μ : ℝ}
  (ha : M₀ ≤ a) (hb : M₀ ≤ b) (hμ : M₀ ≤ μ) (hAB : (a ^ 2 - b ^ 2 : ℂ) ≠ 0)
  (hAU : (a ^ 2 - μ ^ 2 : ℂ) ≠ 0) (hBU : (b ^ 2 - μ ^ 2 : ℂ) ≠ 0)

theorem tail_abab : (Fin.tail ![a, b, a, b] : Fin 3 → ℝ) = ![b, a, b] := by
  funext i; fin_cases i <;> rfl

theorem tail_bab : (Fin.tail ![b, a, b] : Fin 2 → ℝ) = ![a, b] := by
  funext i; fin_cases i <;> rfl

theorem tail_ababu : (Fin.tail ![a, b, a, b, μ] : Fin 4 → ℝ) = ![b, a, b, μ] := by
  funext i; fin_cases i <;> rfl

theorem tail_babu : (Fin.tail ![b, a, b, μ] : Fin 3 → ℝ) = ![a, b, μ] := by
  funext i; fin_cases i <;> rfl

theorem tail_abu : (Fin.tail ![a, b, μ] : Fin 2 → ℝ) = ![b, μ] := by
  funext i; fin_cases i <;> rfl

/-- The real-to-complex form of `seProdLim_abab`. -/
theorem seProdLim_abab_c (hk₀ : k₀ = 0) (hE : SEEngU N m M₀ Pv K k₀)
    (hL : SELimU α N m M₀ Pv k₀) (ha : M₀ ≤ a) (hb : M₀ ≤ b) (hAB : (a ^ 2 - b ^ 2 : ℂ) ≠ 0) :
    seProdLim α N m ![a, b, a, b] Pv = ((a ^ 2 - b ^ 2 : ℂ) ^ 2)⁻¹ *
      (seProdLim α N m ![a, a] Pv + seProdLim α N m ![b, b] Pv -
        2 * seProdLim α N m ![a, b] Pv) := by
  have hab : a ^ 2 ≠ b ^ 2 := by
    intro h; apply hAB; exact_mod_cast sub_eq_zero.2 h
  rw [seProdLim_abab hE hL hk₀ ha hb hab]
  push_cast
  rw [inv_pow, show ((b : ℂ) ^ 2 - a ^ 2) ^ 2 = (a ^ 2 - b ^ 2) ^ 2 by ring]

include hE hL ha hb hAB in
/-- **`seL1` of `d_a² d_b²` in two-line blocks** (`k₀ = 0`). -/
theorem seL1_abab_red (hk₀ : k₀ = 0) :
    seL1 α N m ![a, b, a, b] Pv = ((a ^ 2 - b ^ 2 : ℂ) ^ 2)⁻¹ *
      (-(a : ℂ) ^ 2 * seProdLim α N m ![a, a] Pv - (b : ℂ) ^ 2 * seProdLim α N m ![b, b] Pv +
        ((a : ℂ) ^ 2 + b ^ 2) * seProdLim α N m ![a, b] Pv) := by
  unfold seL1
  rw [tail_abab, seProdLim_bab_red hE hL ha hb hAB hk₀, seProdLim_abab_c hk₀ hE hL ha hb hAB]
  simp only [Matrix.cons_val_zero]
  push_cast
  field_simp
  ring

include hE hL ha hb hAB in
/-- **`seL2` of `d_a² d_b²` in two-line blocks** (`k₀ = 0`). -/
theorem seL2_abab_red (hk₀ : k₀ = 0) :
    seL2 α N m ![a, b, a, b] Pv = ((a ^ 2 - b ^ 2 : ℂ) ^ 2)⁻¹ *
      ((a : ℂ) ^ 4 * seProdLim α N m ![a, a] Pv + (b : ℂ) ^ 4 * seProdLim α N m ![b, b] Pv -
        2 * (a : ℂ) ^ 2 * b ^ 2 * seProdLim α N m ![a, b] Pv) := by
  unfold seL2
  rw [seL1_abab_red hE hL ha hb hAB hk₀]
  unfold seL1
  rw [tail_abab, tail_bab, seProdLim_bab_red hE hL ha hb hAB hk₀]
  simp only [Matrix.cons_val_zero]
  push_cast
  field_simp
  ring

include hE hL ha hb hμ hAB hAU hBU in
/-- **`seL3` of `d_a² d_b²` and the spectral line in two-line blocks** (`k₀ = 0`). -/
theorem seL3_ababu_red (hk₀ : k₀ = 0) :
    seL3 α N m ![a, b, a, b, μ] Pv =
      (a : ℂ) ^ 6 / ((a ^ 2 - b ^ 2 : ℂ) ^ 2 * (a ^ 2 - μ ^ 2 : ℂ)) *
          seProdLim α N m ![a, a] Pv +
        (b : ℂ) ^ 6 / ((a ^ 2 - b ^ 2 : ℂ) ^ 2 * (b ^ 2 - μ ^ 2 : ℂ)) *
          seProdLim α N m ![b, b] Pv -
        (a : ℂ) ^ 4 * (2 * a ^ 2 * b ^ 2 + a ^ 2 * μ ^ 2 - 3 * b ^ 2 * μ ^ 2) /
            ((a ^ 2 - b ^ 2 : ℂ) ^ 3 * (a ^ 2 - μ ^ 2 : ℂ)) * seProdLim α N m ![a, μ] Pv +
        (b : ℂ) ^ 4 * (2 * a ^ 2 * b ^ 2 - 3 * a ^ 2 * μ ^ 2 + b ^ 2 * μ ^ 2) /
            ((a ^ 2 - b ^ 2 : ℂ) ^ 3 * (b ^ 2 - μ ^ 2 : ℂ)) * seProdLim α N m ![b, μ] Pv := by
  unfold seL3 seL2 seL1
  rw [tail_ababu, tail_babu, tail_abu, seProdLim_abu_red hE hL ha hb hμ hAB hk₀,
    seProdLim_babu_red hE hL ha hb hμ hAB hBU hk₀,
    seProdLim_ababu_red hE hL ha hb hμ hAB hAU hBU hk₀]
  simp only [Matrix.cons_val_zero]
  push_cast
  field_simp
  ring

include hE hL ha hb hAB in
/-- **`seL1` of `d_a² d_b²` in three-line blocks** (`k₀ ≤ 1`). -/
theorem seL1_abab_q_red (hk₀ : k₀ ≤ 1) :
    seL1 α N m ![a, b, a, b] Pv = (a ^ 2 - b ^ 2 : ℂ)⁻¹ *
      ((a : ℂ) ^ 2 * seProdLim α N m ![a, a, b] Pv -
        (b : ℂ) ^ 2 * seProdLim α N m ![a, b, b] Pv) := by
  unfold seL1
  rw [tail_abab, seProdLim_bab_q_red hE hL ha hb hk₀, seProdLim_abab_q_red hE hL ha hb hAB hk₀]
  simp only [Matrix.cons_val_zero]
  push_cast
  field_simp
  ring

include hE hL ha hb hμ hAB hAU hBU in
/-- **`seL2` of `d_a² d_b²` and the spectral line in three-line blocks** (`k₀ ≤ 1`). -/
theorem seL2_ababu_q_red (hk₀ : k₀ ≤ 1) :
    seL2 α N m ![a, b, a, b, μ] Pv =
      (a : ℂ) ^ 4 / ((a ^ 2 - b ^ 2 : ℂ) * (a ^ 2 - μ ^ 2 : ℂ)) *
          seProdLim α N m ![a, a, b] Pv -
        (b : ℂ) ^ 4 / ((a ^ 2 - b ^ 2 : ℂ) * (b ^ 2 - μ ^ 2 : ℂ)) *
          seProdLim α N m ![a, b, b] Pv +
        (μ : ℂ) ^ 4 / ((a ^ 2 - μ ^ 2 : ℂ) * (b ^ 2 - μ ^ 2 : ℂ)) *
          seProdLim α N m ![a, b, μ] Pv := by
  unfold seL2 seL1
  rw [tail_ababu, tail_babu, seProdLim_babu_q_red hE hL ha hb hμ hBU hk₀,
    seProdLim_ababu_q_red hE hL ha hb hμ hAB hAU hBU hk₀]
  simp only [Matrix.cons_val_zero]
  push_cast
  field_simp
  ring

end Generic

/-! ### The flavour piece -/

/-- The affine blocks of one flavour piece (numerator `N`, masses `a, b`, spectral mass `μ`). -/
noncomputable def seAffBlk (N : (Fin 4 → ℝ) → ℂ) (m a b μ : ℝ) (Pv : Fin 4 → ℝ) : ℂ :=
  -((a : ℂ) ^ 4 * μ ^ 2 / ((a ^ 2 - b ^ 2 : ℂ) ^ 2 * (a ^ 2 - μ ^ 2 : ℂ))) *
      seProdLim 0 N m ![a, a] Pv -
    (b : ℂ) ^ 4 * μ ^ 2 / ((a ^ 2 - b ^ 2 : ℂ) ^ 2 * (b ^ 2 - μ ^ 2 : ℂ)) *
      seProdLim 0 N m ![b, b] Pv -
    2 * (a : ℂ) ^ 2 * b ^ 2 / (a ^ 2 - b ^ 2 : ℂ) ^ 2 * seProdLim 0 N m ![a, b] Pv +
    (a : ℂ) ^ 4 * (2 * a ^ 2 * b ^ 2 + a ^ 2 * μ ^ 2 - 3 * b ^ 2 * μ ^ 2) /
        ((a ^ 2 - b ^ 2 : ℂ) ^ 3 * (a ^ 2 - μ ^ 2 : ℂ)) * seProdLim 0 N m ![a, μ] Pv -
    (b : ℂ) ^ 4 * (2 * a ^ 2 * b ^ 2 - 3 * a ^ 2 * μ ^ 2 + b ^ 2 * μ ^ 2) /
        ((a ^ 2 - b ^ 2 : ℂ) ^ 3 * (b ^ 2 - μ ^ 2 : ℂ)) * seProdLim 0 N m ![b, μ] Pv

/-- The quadratic blocks of one flavour piece (numerator `N` with energy coefficient `α`). -/
noncomputable def seQuadBlk (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m a b μ : ℝ) (Pv : Fin 4 → ℝ) :
    ℂ :=
  2 * (a : ℂ) ^ 2 * μ ^ 2 / ((a ^ 2 - b ^ 2 : ℂ) * (a ^ 2 - μ ^ 2 : ℂ)) *
      seProdLim α N m ![a, a, b] Pv -
    2 * (b : ℂ) ^ 2 * μ ^ 2 / ((a ^ 2 - b ^ 2 : ℂ) * (b ^ 2 - μ ^ 2 : ℂ)) *
      seProdLim α N m ![a, b, b] Pv +
    2 * (μ : ℂ) ^ 4 / ((a ^ 2 - μ ^ 2 : ℂ) * (b ^ 2 - μ ^ 2 : ℂ)) *
      seProdLim α N m ![a, b, μ] Pv

section Generic2

variable {α : ℂ} {N Nq : (Fin 4 → ℝ) → ℂ} {m M₀ K Kq : ℝ} {Pv : Fin 4 → ℝ}
  (hE : SEEngU N m M₀ Pv K 0) (hL : SELimU 0 N m M₀ Pv 0)
  (hEq : SEEngU Nq m M₀ Pv Kq 1) (hLq : SELimU α Nq m M₀ Pv 1) {a b μ : ℝ}
  (ha : M₀ ≤ a) (hb : M₀ ≤ b) (hμ : M₀ ≤ μ) (hAB : (a ^ 2 - b ^ 2 : ℂ) ≠ 0)
  (hAU : (a ^ 2 - μ ^ 2 : ℂ) ≠ 0) (hBU : (b ^ 2 - μ ^ 2 : ℂ) ≠ 0)

include hE hL ha hb hμ hAB hAU hBU in
theorem seL2_sub_seL3_red :
    seL2 0 N m ![a, b, a, b] Pv - seL3 0 N m ![a, b, a, b, μ] Pv = seAffBlk N m a b μ Pv := by
  rw [seL2_abab_red hE hL ha hb hAB rfl, seL3_ababu_red hE hL ha hb hμ hAB hAU hBU rfl]
  unfold seAffBlk
  field_simp
  ring

include hEq hLq ha hb hμ hAB hAU hBU in
theorem seL1_sub_seL2_q_red :
    -2 * seL1 α Nq m ![a, b, a, b] Pv + 2 * seL2 α Nq m ![a, b, a, b, μ] Pv =
      seQuadBlk α Nq m a b μ Pv := by
  rw [seL1_abab_q_red hEq hLq ha hb hAB le_rfl,
    seL2_ababu_q_red hEq hLq ha hb hμ hAB hAU hBU le_rfl]
  unfold seQuadBlk
  field_simp
  ring

end Generic2

variable {M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀)

include hM₀ hc₀ in
/-- **The limit of one flavour piece of the class `V` in blocks**: below threshold (the
Feynman mass of `(m, M₀)` at `-p` bounded below by `c₀ > 0`), with the photon masses and the
spectral mass `μ = specMu M_f x` at least `M₀` and with pairwise distinct squares,
`sePieceLim = i c₁ w₁(x) (seAffBlk + seQuadBlk)`. -/
theorem sePieceLim_eq_blocks (P : Params) (p : Fin 4 → ℝ) (α β : Fin 4) (x : ℝ) (f : Fin 3)
    (hP : ∀ y ∈ Icc (0 : ℝ) 1,
      c₀ ≤ selfEnergyFeynmanMass P.m M₀ (Minkowski.dot (-p) (-p)) y)
    (ha : M₀ ≤ P.mγ) (hb : M₀ ≤ P.Λ) (hμ : M₀ ≤ specMu (P.mass f) x)
    (hAB : (P.mγ ^ 2 - P.Λ ^ 2 : ℂ) ≠ 0)
    (hAU : (P.mγ ^ 2 - specMu (P.mass f) x ^ 2 : ℂ) ≠ 0)
    (hBU : (P.Λ ^ 2 - specMu (P.mass f) x ^ 2 : ℂ) ≠ 0) :
    sePieceLim P p α β x f = I * cOne P * wOne x *
      (seAffBlk (seAff (seCL P p α β) 3 α β) P.m P.mγ P.Λ (specMu (P.mass f) x) (-p) +
        seQuadBlk (seQuadA p α β) (seQuad p α β) P.m P.mγ P.Λ (specMu (P.mass f) x) (-p)) := by
  obtain ⟨K, -, hE⟩ := exists_seEngU_seAff hM₀ hc₀ hP (seCL P p α β) 3 α β
  have hL := seLimU_seAff hM₀ hc₀ hP (seCL P p α β) 3 α β
  obtain ⟨Kq, -, hEq⟩ := exists_seEngU_seQuad hM₀ hc₀ hP p α β
  have hLq := seLimU_seQuad hM₀ hc₀ hP p α β
  have h1 := seL2_sub_seL3_red hE hL ha hb hμ hAB hAU hBU
  have h2 := seL1_sub_seL2_q_red hEq hLq ha hb hμ hAB hAU hBU
  unfold sePieceLim seMs4 seMs5
  rw [← h1, ← h2]
  ring

end QED.ChainProof.SetCRegDisp

end
