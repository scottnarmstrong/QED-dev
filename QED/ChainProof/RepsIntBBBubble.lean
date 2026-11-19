/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntBBBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Pauli–Villars bubble at rotated loop energies

Helper for obligation O3-5 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53). At the rotated energies
`(1 + s i) t`, every denominator is elliptic (`one_add_sq_add_le_rot`), and the flavour sum of the
one-loop bubble decays fast enough to be integrable in its loop momentum uniformly in the photon
momentum:

* `trace_gamma_three`: the trace of three gamma matrices vanishes, so the trace of the bubble is
  `T₀ + M² T₂` with `T₀ = Tr[A̸ γ^μ B̸ γ^ν]`, `T₂ = Tr[γ^μ γ^ν]` (`trace_epC_eq`).
* `pv_identity`: with `α = A⁻¹`, `u = (A + x)⁻¹` (and `β`, `v` for `B`),
  `(T₀ + x T₂) u v = T₀ α β + x (…) + x² R`, so under the two Pauli–Villars conditions
  `∑ c_f = 0`, `∑ c_f M_f² = 0` only the `x² R` terms survive (`vpC_eq_sum_R`).
* `norm_pvR_le`: the bound of the remainder `R` by `σ_A⁻⁵ + σ_B⁻⁵`, with
  `σ_A = 1 + |t_A| + |y_A|` for `q + k` and `σ_B` for `q`; it gives the bubble bound
  `‖Π(k, q)‖ ≤ C (σ_A⁻⁵ + σ_B⁻⁵)` (`exists_vpC_rot`, `QED/ChainProof/RepsIntBBRot.lean`), with `C`
  independent of all momenta. No mass condition is used beyond the two Pauli–Villars conditions.
-/

@[expose] public section

open Complex

namespace QED.ChainProof.RepsIntBB

open QED.WickModel

/-! ### Traces -/

theorem trace_gamma_three (a b c : Fin 4) :
    Matrix.trace (Dirac.gamma a * Dirac.gamma b * Dirac.gamma c) = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [Dirac.gamma, Matrix.trace, Fin.sum_univ_four]

theorem trace_slashC_mul (A : Fin 4 → ℂ) (μ ν : Fin 4) :
    Matrix.trace (slashC A * Dirac.gamma μ * Dirac.gamma ν) = 0 := by
  unfold slashC
  rw [Finset.sum_mul, Finset.sum_mul, Matrix.trace_sum]
  simp [Matrix.trace_smul, trace_gamma_three]

theorem trace_mul_slashC_mul (B : Fin 4 → ℂ) (μ ν : Fin 4) :
    Matrix.trace (Dirac.gamma μ * slashC B * Dirac.gamma ν) = 0 := by
  unfold slashC
  rw [Matrix.mul_sum, Finset.sum_mul, Matrix.trace_sum]
  simp [Matrix.trace_smul, trace_gamma_three]

theorem numC_expand (M : ℝ) (A B : Fin 4 → ℂ) (μ ν : Fin 4) :
    numC M A * Dirac.gamma μ * numC M B * Dirac.gamma ν =
      ((M : ℂ) ^ 2) • (Dirac.gamma μ * Dirac.gamma ν) -
        (M : ℂ) • (slashC A * Dirac.gamma μ * Dirac.gamma ν) -
        (M : ℂ) • (Dirac.gamma μ * slashC B * Dirac.gamma ν) +
        slashC A * Dirac.gamma μ * slashC B * Dirac.gamma ν := by
  simp only [numC, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_smul, Matrix.mul_assoc]
  rw [sq]
  abel

/-- The bilinear part `T₀ = Tr[A̸ γ^μ B̸ γ^ν]`. -/
noncomputable def traceT0 (A B : Fin 4 → ℂ) (μ ν : Fin 4) : ℂ :=
  Matrix.trace (slashC A * Dirac.gamma μ * slashC B * Dirac.gamma ν)

/-- The mass part `T₂ = Tr[γ^μ γ^ν]`. -/
noncomputable def traceT2 (μ ν : Fin 4) : ℂ := Matrix.trace (Dirac.gamma μ * Dirac.gamma ν)

theorem trace_numC (M : ℝ) (A B : Fin 4 → ℂ) (μ ν : Fin 4) :
    Matrix.trace (numC M A * Dirac.gamma μ * numC M B * Dirac.gamma ν) =
      traceT0 A B μ ν + (M : ℂ) ^ 2 * traceT2 μ ν := by
  rw [numC_expand]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, trace_slashC_mul,
    trace_mul_slashC_mul, smul_eq_mul, mul_zero, sub_zero, traceT0, traceT2]
  ring

theorem trace_epC_eq (M ε : ℝ) (A B : Fin 4 → ℂ) (μ ν : Fin 4) :
    Matrix.trace (epC M ε A * Dirac.gamma μ * epC M ε B * Dirac.gamma ν) =
      (denC M ε A)⁻¹ * (denC M ε B)⁻¹ * (traceT0 A B μ ν + (M : ℂ) ^ 2 * traceT2 μ ν) := by
  rw [← trace_numC]
  unfold epC
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_smul, smul_eq_mul]
  ring

theorem denC_eq_add (M ε : ℝ) (A : Fin 4 → ℂ) : denC M ε A = denC 0 ε A + (M : ℂ) ^ 2 := by
  unfold denC
  push_cast
  ring

/-! ### The Pauli–Villars identity -/

/-- The remainder `R = (T₀ + x T₂) W - T₂ (α² β + α β²)`,
`W = α² β² + α² u v + (α - x α²) β² v`. -/
def pvR (T0 T2 x α β u v : ℂ) : ℂ :=
  (T0 + x * T2) * (α ^ 2 * β ^ 2 + α ^ 2 * u * v + (α - x * α ^ 2) * β ^ 2 * v) -
    T2 * (α ^ 2 * β + α * β ^ 2)

theorem pv_identity (T0 T2 A B x : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hAx : A + x ≠ 0)
    (hBx : B + x ≠ 0) :
    (A + x)⁻¹ * (B + x)⁻¹ * (T0 + x * T2) =
      T0 * (A⁻¹ * B⁻¹) + x * (T2 * (A⁻¹ * B⁻¹) - T0 * (A⁻¹ ^ 2 * B⁻¹ + A⁻¹ * B⁻¹ ^ 2)) +
        x ^ 2 * pvR T0 T2 x A⁻¹ B⁻¹ (A + x)⁻¹ (B + x)⁻¹ := by
  unfold pvR
  field_simp
  ring

/-- **The flavour-summed bubble keeps only the `x²` remainders.** -/
theorem vpC_eq_sum_R (P : Params) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (k q : Fin 4 → ℂ)
    (hA : NZ P.ε (q + k)) (hB : NZ P.ε q) (μ ν : Fin 4) :
    vpC P k q μ ν = vpConst P * ∑ f, (P.loopCoeff f : ℂ) * ((P.mass f : ℂ) ^ 2) ^ 2 *
      pvR (traceT0 (q + k) q μ ν) (traceT2 μ ν) ((P.mass f : ℂ) ^ 2) (denC 0 P.ε (q + k))⁻¹
        (denC 0 P.ε q)⁻¹ (denC (P.mass f) P.ε (q + k))⁻¹ (denC (P.mass f) P.ε q)⁻¹ := by
  unfold vpC
  congr 1
  have key : ∀ f, Matrix.trace (epC (P.mass f) P.ε (q + k) * Dirac.gamma μ *
      epC (P.mass f) P.ε q * Dirac.gamma ν) =
      traceT0 (q + k) q μ ν * ((denC 0 P.ε (q + k))⁻¹ * (denC 0 P.ε q)⁻¹) +
        (P.mass f : ℂ) ^ 2 * (traceT2 μ ν * ((denC 0 P.ε (q + k))⁻¹ * (denC 0 P.ε q)⁻¹) -
          traceT0 (q + k) q μ ν * ((denC 0 P.ε (q + k))⁻¹ ^ 2 * (denC 0 P.ε q)⁻¹ +
            (denC 0 P.ε (q + k))⁻¹ * (denC 0 P.ε q)⁻¹ ^ 2)) +
        ((P.mass f : ℂ) ^ 2) ^ 2 * pvR (traceT0 (q + k) q μ ν) (traceT2 μ ν)
          ((P.mass f : ℂ) ^ 2) (denC 0 P.ε (q + k))⁻¹ (denC 0 P.ε q)⁻¹
          (denC (P.mass f) P.ε (q + k))⁻¹ (denC (P.mass f) P.ε q)⁻¹ := by
    intro f
    rw [trace_epC_eq]
    have e1 := denC_eq_add (P.mass f) P.ε (q + k)
    have e2 := denC_eq_add (P.mass f) P.ε q
    have h := pv_identity (traceT0 (q + k) q μ ν) (traceT2 μ ν) (denC 0 P.ε (q + k))
      (denC 0 P.ε q) ((P.mass f : ℂ) ^ 2) (hA 0) (hB 0) (e1 ▸ hA _) (e2 ▸ hB _)
    rw [← e1, ← e2] at h
    rw [h]
  simp only [key]
  have s1 : ∑ f, (P.loopCoeff f : ℂ) = 0 := by
    simp only [Fin.sum_univ_three, Params.loopCoeff]
    simp
    exact_mod_cast hc₁
  have s2 : ∑ f, (P.loopCoeff f : ℂ) * (P.mass f : ℂ) ^ 2 = 0 := by
    simp only [Fin.sum_univ_three, Params.loopCoeff, Params.mass]
    simp
    exact_mod_cast hc₂
  simp only [mul_add, Finset.sum_add_distrib]
  have e3 : ∑ f, (P.loopCoeff f : ℂ) * (traceT0 (q + k) q μ ν *
      ((denC 0 P.ε (q + k))⁻¹ * (denC 0 P.ε q)⁻¹)) = 0 := by
    rw [← Finset.sum_mul, s1, zero_mul]
  have e4 : ∀ Z : ℂ, ∑ f, (P.loopCoeff f : ℂ) * ((P.mass f : ℂ) ^ 2 * Z) = 0 := by
    intro Z
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, s2, zero_mul]
  rw [e3, e4, zero_add, zero_add]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

/-! ### Real inequalities -/

theorem mono_le_pow_five {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hp1 : p ≤ 1) (hq1 : q ≤ 1)
    {i j : ℕ} (hij : 5 ≤ i + j) : p ^ i * q ^ j ≤ p ^ 5 + q ^ 5 := by
  rcases le_total p q with h | h
  · calc p ^ i * q ^ j ≤ q ^ i * q ^ j := by gcongr
      _ = q ^ (i + j) := (pow_add q i j).symm
      _ ≤ q ^ 5 := pow_le_pow_of_le_one hq hq1 hij
      _ ≤ p ^ 5 + q ^ 5 := le_add_of_nonneg_left (by positivity)
  · calc p ^ i * q ^ j ≤ p ^ i * p ^ j := by gcongr
      _ = p ^ (i + j) := (pow_add p i j).symm
      _ ≤ p ^ 5 := pow_le_pow_of_le_one hp hp1 hij
      _ ≤ p ^ 5 + q ^ 5 := le_add_of_nonneg_right (by positivity)

/-- **The bound on the remainder**, with `‖α‖, ‖u‖ ≤ K p²`, `‖β‖, ‖v‖ ≤ K q²`,
`‖T₀‖ p q ≤ L`, `‖T₂‖ ≤ L`, `‖x‖ ≤ X` and `0 < p, q ≤ 1`. -/
theorem norm_pvR_le {T0 T2 x α β u v : ℂ} {p q K L X : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hp1 : p ≤ 1) (hq1 : q ≤ 1) (hK : 0 ≤ K) (hL : 0 ≤ L) (hX : 0 ≤ X)
    (hα : ‖α‖ ≤ K * p ^ 2) (hu : ‖u‖ ≤ K * p ^ 2) (hβ : ‖β‖ ≤ K * q ^ 2)
    (hv : ‖v‖ ≤ K * q ^ 2) (hT0 : ‖T0‖ * (p * q) ≤ L) (hT2 : ‖T2‖ ≤ L) (hx : ‖x‖ ≤ X) :
    ‖pvR T0 T2 x α β u v‖ ≤
      (L * (1 + X) * (3 * K ^ 4 + X * K ^ 5) + 2 * L * K ^ 3) * (p ^ 5 + q ^ 5) := by
  have hpq : 0 < p * q := mul_pos hp hq
  have hpq1 : p * q ≤ 1 := by nlinarith
  have hT0' : ‖T0‖ ≤ L / (p * q) := by rw [le_div_iff₀ hpq]; exact hT0
  have hS : ‖T0 + x * T2‖ ≤ L * (1 + X) / (p * q) := by
    calc ‖T0 + x * T2‖ ≤ ‖T0‖ + ‖x‖ * ‖T2‖ := (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ L / (p * q) + X * L := by gcongr
      _ ≤ L / (p * q) + X * L / (p * q) := by
          gcongr
          rw [le_div_iff₀ hpq]
          nlinarith [mul_nonneg hX hL]
      _ = L * (1 + X) / (p * q) := by ring
  have hW : ‖α ^ 2 * β ^ 2 + α ^ 2 * u * v + (α - x * α ^ 2) * β ^ 2 * v‖ ≤
      K ^ 4 * (p ^ 4 * q ^ 4 + p ^ 6 * q ^ 2 + p ^ 2 * q ^ 6) + X * K ^ 5 * (p ^ 4 * q ^ 6) := by
    have h1 : ‖α ^ 2 * β ^ 2‖ ≤ (K * p ^ 2) ^ 2 * (K * q ^ 2) ^ 2 := by
      rw [norm_mul, norm_pow, norm_pow]; gcongr
    have h2 : ‖α ^ 2 * u * v‖ ≤ (K * p ^ 2) ^ 2 * (K * p ^ 2) * (K * q ^ 2) := by
      rw [norm_mul, norm_mul, norm_pow]; gcongr
    have h3 : ‖α - x * α ^ 2‖ ≤ K * p ^ 2 + X * (K * p ^ 2) ^ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_pow]
      gcongr
    have h4 : ‖(α - x * α ^ 2) * β ^ 2 * v‖ ≤
        (K * p ^ 2 + X * (K * p ^ 2) ^ 2) * (K * q ^ 2) ^ 2 * (K * q ^ 2) := by
      rw [norm_mul, norm_mul, norm_pow]; gcongr
    calc _ ≤ ‖α ^ 2 * β ^ 2‖ + ‖α ^ 2 * u * v‖ + ‖(α - x * α ^ 2) * β ^ 2 * v‖ :=
          norm_add₃_le
      _ ≤ (K * p ^ 2) ^ 2 * (K * q ^ 2) ^ 2 + (K * p ^ 2) ^ 2 * (K * p ^ 2) * (K * q ^ 2) +
          (K * p ^ 2 + X * (K * p ^ 2) ^ 2) * (K * q ^ 2) ^ 2 * (K * q ^ 2) := by gcongr
      _ = _ := by ring
  have hV : ‖T2 * (α ^ 2 * β + α * β ^ 2)‖ ≤ L * (K ^ 3 * (p ^ 4 * q ^ 2 + p ^ 2 * q ^ 4)) := by
    rw [norm_mul]
    gcongr
    calc ‖α ^ 2 * β + α * β ^ 2‖ ≤ ‖α ^ 2 * β‖ + ‖α * β ^ 2‖ := norm_add_le _ _
      _ ≤ (K * p ^ 2) ^ 2 * (K * q ^ 2) + (K * p ^ 2) * (K * q ^ 2) ^ 2 := by
          rw [norm_mul, norm_mul, norm_pow, norm_pow]; gcongr
      _ = _ := by ring
  have m := fun (i j : ℕ) (hij : 5 ≤ i + j) => mono_le_pow_five hp.le hq.le hp1 hq1 hij
  have hprod : ‖(T0 + x * T2) * (α ^ 2 * β ^ 2 + α ^ 2 * u * v + (α - x * α ^ 2) * β ^ 2 * v)‖ ≤
      L * (1 + X) * (3 * K ^ 4 + X * K ^ 5) * (p ^ 5 + q ^ 5) := by
    rw [norm_mul]
    calc _ ≤ L * (1 + X) / (p * q) *
          (K ^ 4 * (p ^ 4 * q ^ 4 + p ^ 6 * q ^ 2 + p ^ 2 * q ^ 6) + X * K ^ 5 * (p ^ 4 * q ^ 6)) :=
          mul_le_mul hS hW (norm_nonneg _) (by positivity)
      _ = L * (1 + X) * (K ^ 4 * (p ^ 3 * q ^ 3 + p ^ 5 * q ^ 1 + p ^ 1 * q ^ 5) +
          X * K ^ 5 * (p ^ 3 * q ^ 5)) := by field_simp
      _ ≤ L * (1 + X) * (K ^ 4 * ((p ^ 5 + q ^ 5) + (p ^ 5 + q ^ 5) + (p ^ 5 + q ^ 5)) +
          X * K ^ 5 * (p ^ 5 + q ^ 5)) := by
          gcongr
          · exact m 3 3 (by norm_num)
          · exact m 5 1 (by norm_num)
          · exact m 1 5 (by norm_num)
          · exact m 3 5 (by norm_num)
      _ = _ := by ring
  have hV' : L * (K ^ 3 * (p ^ 4 * q ^ 2 + p ^ 2 * q ^ 4)) ≤ 2 * L * K ^ 3 * (p ^ 5 + q ^ 5) := by
    have := m 4 2 (by norm_num)
    have := m 2 4 (by norm_num)
    have hLK : 0 ≤ L * K ^ 3 := by positivity
    nlinarith
  unfold pvR
  calc _ ≤ ‖(T0 + x * T2) * (α ^ 2 * β ^ 2 + α ^ 2 * u * v + (α - x * α ^ 2) * β ^ 2 * v)‖ +
        ‖T2 * (α ^ 2 * β + α * β ^ 2)‖ := norm_sub_le _ _
    _ ≤ _ := by nlinarith

end QED.ChainProof.RepsIntBB

end
