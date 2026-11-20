/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCYInt
public import QED.ChainProof.SetCKFormXPol
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (c), Stage K, closed forms: the regularized `κ`-part `Â` of the outer-massive corner

Helper level (no frozen statement). Step 3 of the `ρ_oC` route (Stage K notes, Session 29+).
The `Y`-integral of `Y κ` at `y₃ = a Y` is `A = formOCLaurI(κ-coefficients)(Y_c)`
(`formOC_integral_kap`); it diverges like `-β_c log v` at `v = 0⁺`, with
`β_c = x⁴/(4 D₀ (x - 1))` (**`formOCbeta`**). The regularized function
`Â = A + β_c log v` (**`formOCAh`**) has, with `E = x + a(Q(x) + v)` (**`formOCE`**),
`λ = a(1 - x)/((1 - a x) E)` (**`formOClam`**) and `Y_c = v λ`, the scaled form
(**`formOCAh_eq`**, `v > 0`)

`Â = R₀ - x p̃₀ Y_c - x p̃₁ Y_c²/2 - x ñ₁ log λ - v m₁ log v` (**`formOCAhR`**),

where `R₀`, `p̃₀ = p₀/x`, `p̃₁ = p₁/x`, `ñ₁ = n₁/x` and `m₁ = (n₁ - β_c)/v` are polynomials in
`v` over `K Dᵏ` (`formOCRat`, coefficient vectors `formOC…N`; scratch `stageK/foc3/a1.py`,
`a3.py`, `gA.py`). The scaled form is differentiable on `(0, ∞)` with derivative
**`formOCSA`** (**`hasDerivAt_formOCAhR`**); its continuity on `[0, ∞)` and the FTC are in
`SetCKFormOCAhBd`.
The quotient rule for `formXPol c v/(K D(v)ᵏ)` is **`formOC_hasDerivAt_rat`**.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- A polynomial in `v` over `K Dᵏ`. -/
noncomputable def formOCRat {n : ℕ} (c : Fin n → ℝ) (K : ℝ) (k : ℕ) (D v : ℝ) : ℝ :=
  formXPol c v / (K * D ^ k)

/-- Its derivative when `D' = δ`. -/
noncomputable def formOCRatD {n : ℕ} (c : Fin (n + 1) → ℝ) (K : ℝ) (k : ℕ) (D δ v : ℝ) : ℝ :=
  (formXPol (formXPolD c) v * D - k * δ * formXPol c v) / (K * D ^ (k + 1))

theorem formOC_hasDerivAt_rat {n : ℕ} (c : Fin (n + 1) → ℝ) (K : ℝ) (k : ℕ) {D : ℝ → ℝ}
    {δ v : ℝ} (hD : HasDerivAt D δ v) (h0 : D v ≠ 0) (hK : K ≠ 0) :
    HasDerivAt (fun z => formOCRat c K k (D z) z) (formOCRatD c K k (D v) δ v) v := by
  have h1 := (hasDerivAt_formXPol c v).div ((hD.pow k).const_mul K)
    (mul_ne_zero hK (pow_ne_zero k h0))
  refine h1.congr_deriv ?_
  unfold formOCRatD
  simp only [Pi.pow_apply]
  rcases k with _ | k
  · simp only [pow_zero, mul_one, Nat.cast_zero, zero_mul, mul_zero, sub_zero, zero_add, pow_one]
    field_simp
  · simp only [Nat.add_sub_cancel]
    field_simp
    push_cast
    ring

/-- `E = x + a (Q(x) + v)`: `Y_c = a v (1 - x)/((1 - a x) E)`. -/
noncomputable def formOCE (a x v : ℝ) : ℝ := x + a * (setCKQ x + v)

/-- `λ = Y_c/v = a (1 - x)/((1 - a x) E)`. -/
noncomputable def formOClam (a x v : ℝ) : ℝ := a * (1 - x) / ((1 - a * x) * formOCE a x v)

/-- `β_c = x⁴/(4 D₀ (x - 1))`, the coefficient of `1/Y` in `Y κ` at `v = 0`. -/
noncomputable def formOCbeta (a x : ℝ) : ℝ := x ^ 4 / (4 * formOCD0 a x * (x - 1))

/-- Numerator coefficients (in `v`) of `R₀`, the `E`-denominator-free rational part of `Â`. -/
noncomputable def formOCR0N (x a q D0 : ℝ) : Fin 3 → ℝ :=
  ![
    -x*(2*D0^2*a^2*x^4 - 2*D0^2*a^2*x^3 - 4*D0^2*a*x^4 + 4*D0^2*a*x^3 + 4*D0^2*a*x^2 + 4*D0^2*x^3
      - 10*D0^2*x^2 + 6*D0^2*x - 4*D0*a^2*q*x^2 + 4*D0*a*q*x - 4*D0*a*x^3 + 4*D0*x^2 + a^4*q^2*x^3
      - 2*a^4*q^2*x^2 - 2*a^3*q^2*x^2 + 4*a^3*q^2*x + 2*a^3*q*x^4 - 4*a^3*q*x^3 + a^2*q^2*x
      - 2*a^2*q^2 - 4*a^2*q*x^3 + 8*a^2*q*x^2 + a^2*x^5 - 2*a^2*x^4 + 2*a*q*x^2 - 4*a*q*x
      - 2*a*x^4 + 4*a*x^3 + x^3 - 2*x^2),
    2*a*x*(2*D0*a^3*x^4 - 2*D0*a^3*x^3 - 7*D0*a^2*x^4 + 8*D0*a^2*x^3 + 3*D0*a^2*x^2 + 2*D0*a*x^4
      + 6*D0*a*x^3 - 14*D0*a*x^2 + 4*D0*a*x - 2*D0*x^3 - D0*x^2 + 6*D0*x - 5*D0 + a^3*q*x^3
      - 6*a^3*q*x^2 + 4*a^3*q*x + 2*a^2*q*x^3 - 4*a^2*q*x^2 + 8*a^2*q*x - 4*a^2*q + a^2*x^4
      - 6*a^2*x^3 + 4*a^2*x^2 - 2*a*q*x^2 + 3*a*q*x - 2*a*q + 2*a*x^4 - 4*a*x^3 + 8*a*x^2 - 4*a*x
      - 2*x^3 + 3*x^2 - 2*x),
    -a^2*x*(2*a^4*x^4 - 2*a^4*x^3 - 10*a^3*x^4 + 12*a^3*x^3 + 2*a^3*x^2 + 8*a^2*x^4 - a^2*x^3
      - 6*a^2*x^2 - 6*a^2*x - 16*a*x^3 + 16*a*x^2 - 2*a + 3*x^3 + 4*x^2 - 14*x + 10)]

/-- Numerator coefficients (in `v`) of `p₀/x`. -/
noncomputable def formOCP0xN (x a _q D0 : ℝ) : Fin 3 → ℝ :=
  ![
    D0^2*x*(x - 2)*(a*x^2 - x + 1),
    -D0*a*(a*x - 1)*(3*a*x^3 - 6*a*x^2 + a*x - x^3 + x^2 + 3*x - 3),
    a^2*(a*x - 1)^2*(2*a*x^2 - 4*a*x + a - 2*x^2 + 5*x - 3)]

/-- Numerator coefficients (in `v`) of `p₁/x`. -/
noncomputable def formOCP1xN (x a _q D0 : ℝ) : Fin 2 → ℝ :=
  ![
    -D0*x*(a*x - 1)^2,
    a*(a*x - 1)^3]

/-- Numerator coefficients (in `v`) of `n₁/x`. -/
noncomputable def formOCN1xN (x a _q D0 : ℝ) : Fin 3 → ℝ :=
  ![
    D0^2*x^3,
    2*D0*a*(a*x^4 - 3*a*x^3 - a*x^2 + 2*a*x + 3*x^2 - 4*x + 2),
    -a^2*(a*x - 1)*(2*a*x^3 - 5*a*x^2 - 2*a*x + 4*a - 2*x^3 + 10*x^2 - 13*x + 6)]

/-- Numerator coefficients (in `v`) of `m₁ = (n₁ - β_c)/v`. -/
noncomputable def formOCm1N (x a _q D0 : ℝ) : Fin 2 → ℝ :=
  ![
    2*D0*a*x*(x - 1)*(a*x^3 - a*x^2 - 2*a*x - x^2 + 2*x - 2),
    -a^2*x*(x - 1)*(2*a^2*x^3 - 2*a^2*x^2 - 4*a^2*x - 2*a*x^3 + 4*a*x^2 - 4*a*x + 4*a + 3*x^2
      - 7*x + 6)]

/-- `R₀`. -/
noncomputable def formOCR0 (a x v : ℝ) : ℝ :=
  formOCRat (formOCR0N x a (setCKQ x) (formOCD0 a x)) (8 * formOCD0 a x * (x - 1)) 2
    (formOCD a x v) v

/-- `p̃₀ = p₀/x`. -/
noncomputable def formOCP0x (a x v : ℝ) : ℝ :=
  formOCRat (formOCP0xN x a (setCKQ x) (formOCD0 a x)) (2 * formOCD0 a x * (x - 1)) 2
    (formOCD a x v) v

/-- `p̃₁ = p₁/x`. -/
noncomputable def formOCP1x (a x v : ℝ) : ℝ :=
  formOCRat (formOCP1xN x a (setCKQ x) (formOCD0 a x)) (2 * formOCD0 a x) 1 (formOCD a x v) v

/-- `ñ₁ = n₁/x`. -/
noncomputable def formOCN1x (a x v : ℝ) : ℝ :=
  formOCRat (formOCN1xN x a (setCKQ x) (formOCD0 a x)) (4 * formOCD0 a x * (x - 1)) 2
    (formOCD a x v) v

/-- `m₁ = (n₁ - β_c)/v`. -/
noncomputable def formOCm1 (a x v : ℝ) : ℝ :=
  formOCRat (formOCm1N x a (setCKQ x) (formOCD0 a x)) (4 * formOCD0 a x * (x - 1)) 2
    (formOCD a x v) v

/-- **`Â = A + β_c log v`**, `A = ∫₀¹ Y κ dY` at `y₃ = a Y` (`formOC_integral_kap`). -/
noncomputable def formOCAh (a x v : ℝ) : ℝ :=
  formOCLaurI (formOCkapn3 x a v (formOCD a x v) (formOCD0 a x))
      (formOCkapn2 x a v (formOCD a x v) (formOCD0 a x))
      (formOCkapn1 x a v (formOCD a x v) (formOCD0 a x))
      (formOCkapp0 x a v (formOCD a x v) (formOCD0 a x))
      (formOCkapp1 x a v (formOCD a x v) (formOCD0 a x)) (formOCYc a x v) +
    formOCbeta a x * log v

/-- **The scaled form of `Â`**, continuous at `v = 0`. -/
noncomputable def formOCAhR (a x v : ℝ) : ℝ :=
  formOCR0 a x v - x * formOCP0x a x v * formOCYc a x v -
    x * formOCP1x a x v * formOCYc a x v ^ 2 / 2 - x * formOCN1x a x v * log (formOClam a x v) -
    formOCm1 a x v * (v * log v)

section

variable {a x v : ℝ}

theorem formOCE_pos (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 ≤ v) :
    0 < formOCE a x v := by
  have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  have := ha.1
  have := hx.1
  unfold formOCE
  positivity

theorem formOCD_pos' (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 ≤ v) :
    0 < formOCD a x v := by
  have h1 : 0 < a * (1 - a) := mul_pos ha.1 (by linarith [ha.2])
  have := setCKQ_nonneg ⟨hx.1.le, hx.2.le⟩
  unfold formOCD
  positivity

theorem formOClam_pos (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 ≤ v) :
    0 < formOClam a x v := by
  have hE := formOCE_pos ha hx hv
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have h2 : 0 < 1 - a * x := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have := ha.1
  unfold formOClam
  positivity

theorem formOCYc_eq_mul : formOCYc a x v = v * formOClam a x v := by
  unfold formOCYc formOClam formOCE
  ring

theorem formOC_simp_rat3 (c : Fin 3 → ℝ) (K D v : ℝ) (k : ℕ) :
    formOCRat c K k D v = (c 0 + c 1 * v + c 2 * v ^ 2) / (K * D ^ k) := by
  simp [formOCRat, formXPol, Fin.sum_univ_succ]
  ring

theorem formOC_simp_rat2 (c : Fin 2 → ℝ) (K D v : ℝ) (k : ℕ) :
    formOCRat c K k D v = (c 0 + c 1 * v) / (K * D ^ k) := by
  simp [formOCRat, formXPol, Fin.sum_univ_succ]

section Atoms

variable {a x v q D0 : ℝ}

theorem formOC_p0_eq (hD : D0 + a * (1 - a) * v ≠ 0) (hD0 : D0 ≠ 0) (hx1 : x - 1 ≠ 0) :
    formOCkapp0 x a v (D0 + a * (1 - a) * v) D0 =
      x * formOCRat (formOCP0xN x a q D0) (2 * D0 * (x - 1)) 2 (D0 + a * (1 - a) * v) v := by
  rw [formOC_simp_rat3]
  simp only [formOCkapp0, formOCP0xN, Matrix.cons_val]
  field_simp
  ring

theorem formOC_p1_eq (hD : D0 + a * (1 - a) * v ≠ 0) (hD0 : D0 ≠ 0) :
    formOCkapp1 x a v (D0 + a * (1 - a) * v) D0 =
      x * formOCRat (formOCP1xN x a q D0) (2 * D0) 1 (D0 + a * (1 - a) * v) v := by
  rw [formOC_simp_rat2]
  simp only [formOCkapp1, formOCP1xN, Matrix.cons_val]
  field_simp
  ring

theorem formOC_n1_eq (hD : D0 + a * (1 - a) * v ≠ 0) (hD0 : D0 ≠ 0) (hx1 : x - 1 ≠ 0) :
    formOCkapn1 x a v (D0 + a * (1 - a) * v) D0 =
      x * formOCRat (formOCN1xN x a q D0) (4 * D0 * (x - 1)) 2 (D0 + a * (1 - a) * v) v := by
  rw [formOC_simp_rat3]
  simp only [formOCkapn1, formOCN1xN, Matrix.cons_val]
  field_simp
  ring

theorem formOC_m1_eq (hD : D0 + a * (1 - a) * v ≠ 0) (hD0 : D0 ≠ 0) (hx1 : x - 1 ≠ 0) :
    formOCkapn1 x a v (D0 + a * (1 - a) * v) D0 - x ^ 4 / (4 * D0 * (x - 1)) =
      v * formOCRat (formOCm1N x a q D0) (4 * D0 * (x - 1)) 2 (D0 + a * (1 - a) * v) v := by
  rw [formOC_simp_rat2]
  simp only [formOCkapn1, formOCm1N, Matrix.cons_val]
  field_simp
  ring

theorem formOC_R0_eq (hD : D0 + a * (1 - a) * v ≠ 0) (hD0 : D0 ≠ 0) (hx1 : x - 1 ≠ 0)
    (hc : a * (1 - x) / ((1 - a * x) * (x + a * q + a * v)) ≠ 0) (hv : v ≠ 0) :
    formOCkapn3 x a v (D0 + a * (1 - a) * v) D0 *
          (1 / (v * (a * (1 - x) / ((1 - a * x) * (x + a * q + a * v)))) ^ 2 - 1) / 2 +
        formOCkapn2 x a v (D0 + a * (1 - a) * v) D0 *
          (1 / (v * (a * (1 - x) / ((1 - a * x) * (x + a * q + a * v)))) - 1) +
        formOCkapp0 x a v (D0 + a * (1 - a) * v) D0 +
        formOCkapp1 x a v (D0 + a * (1 - a) * v) D0 / 2 =
      formOCRat (formOCR0N x a q D0) (8 * D0 * (x - 1)) 2 (D0 + a * (1 - a) * v) v := by
  have ha : a ≠ 0 := by rintro rfl; simp at hc
  have h1x : 1 - x ≠ 0 := by rintro h; simp [h] at hc
  have hL : 1 - a * x ≠ 0 := by rintro h; simp [h] at hc
  have hE : x + a * q + a * v ≠ 0 := by rintro h; simp [h] at hc
  rw [formOC_simp_rat3]
  simp only [formOCkapn3, formOCkapn2, formOCkapp0, formOCkapp1, formOCR0N, Matrix.cons_val]
  field_simp
  ring

end Atoms

/-- **The scaled form of `Â`.** -/
theorem formOCAh_eq (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    formOCAh a x v = formOCAhR a x v := by
  have hlam := formOClam_pos ha hx hv.le
  have hE := (formOCE_pos ha hx hv.le).ne'
  have hD := (formOCD_pos' ha hx hv.le).ne'
  have hD0 := (formOCD0_pos ha hx).ne'
  have hx1 : x - 1 ≠ 0 := by linarith [hx.2]
  have eD : formOCD a x v = formOCD0 a x + a * (1 - a) * v := by
    unfold formOCD formOCD0
    ring
  have eE : formOCE a x v = x + a * setCKQ x + a * v := by unfold formOCE; ring
  have hp0 := formOC_p0_eq (q := setCKQ x) (eD ▸ hD) hD0 hx1
  have hp1 := formOC_p1_eq (x := x) (q := setCKQ x) (eD ▸ hD) hD0
  have hn1 := formOC_n1_eq (q := setCKQ x) (eD ▸ hD) hD0 hx1
  have hm1 := formOC_m1_eq (q := setCKQ x) (eD ▸ hD) hD0 hx1
  have hR0 := formOC_R0_eq (eD ▸ hD) hD0 hx1 (by rw [← eE]; exact hlam.ne') hv.ne'
  unfold formOCAh formOCAhR formOCLaurI formOCR0 formOCP0x formOCP1x formOCN1x formOCm1
  rw [formOCYc_eq_mul, log_mul hv.ne' hlam.ne']
  rw [← eD] at hp0 hp1 hn1 hm1 hR0
  have hlam' : formOClam a x v = a * (1 - x) / ((1 - a * x) * (x + a * setCKQ x + a * v)) := by
    rw [formOClam, eE]
  rw [← hlam'] at hR0
  unfold formOCbeta
  linear_combination hR0 - formOClam a x v * v * hp0 - (formOClam a x v * v) ^ 2 / 2 * hp1 -
    (log v + log (formOClam a x v)) * hn1 + log v * hn1 - log v * hm1

end

/-- `Y_c' = a (1 - x)(x + a Q(x))/((1 - a x) E²)`. -/
noncomputable def formOCdc (a x v : ℝ) : ℝ :=
  a * (1 - x) * (x + a * setCKQ x) / ((1 - a * x) * formOCE a x v ^ 2)

/-- `R₀'`. -/
noncomputable def formOCdR0 (a x v : ℝ) : ℝ :=
  formOCRatD (formOCR0N x a (setCKQ x) (formOCD0 a x)) (8 * formOCD0 a x * (x - 1)) 2
    (formOCD a x v) (a * (1 - a)) v

/-- `p̃₀'`. -/
noncomputable def formOCdP0x (a x v : ℝ) : ℝ :=
  formOCRatD (formOCP0xN x a (setCKQ x) (formOCD0 a x)) (2 * formOCD0 a x * (x - 1)) 2
    (formOCD a x v) (a * (1 - a)) v

/-- `p̃₁'`. -/
noncomputable def formOCdP1x (a x v : ℝ) : ℝ :=
  formOCRatD (formOCP1xN x a (setCKQ x) (formOCD0 a x)) (2 * formOCD0 a x) 1
    (formOCD a x v) (a * (1 - a)) v

/-- `ñ₁'`. -/
noncomputable def formOCdN1x (a x v : ℝ) : ℝ :=
  formOCRatD (formOCN1xN x a (setCKQ x) (formOCD0 a x)) (4 * formOCD0 a x * (x - 1)) 2
    (formOCD a x v) (a * (1 - a)) v

/-- `m₁'`. -/
noncomputable def formOCdm1 (a x v : ℝ) : ℝ :=
  formOCRatD (formOCm1N x a (setCKQ x) (formOCD0 a x)) (4 * formOCD0 a x * (x - 1)) 2
    (formOCD a x v) (a * (1 - a)) v

/-- **`S_A = ∂_v Â`.** -/
noncomputable def formOCSA (a x v : ℝ) : ℝ :=
  formOCdR0 a x v - x * (formOCdP0x a x v * formOCYc a x v + formOCP0x a x v * formOCdc a x v) -
    x * (formOCdP1x a x v * formOCYc a x v ^ 2 / 2 +
      formOCP1x a x v * formOCYc a x v * formOCdc a x v) -
    x * formOCdN1x a x v * log (formOClam a x v) + x * formOCN1x a x v * (a / formOCE a x v) -
    (formOCm1 a x v + v * formOCdm1 a x v) * log v - formOCm1 a x v

section

variable {a x v : ℝ}

theorem formOC_hasDerivAt_D (a x v : ℝ) : HasDerivAt (formOCD a x) (a * (1 - a)) v := by
  have h := ((hasDerivAt_id v).const_add (setCKQ x)).const_mul (a * (1 - a)) |>.const_add 1
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro z
  simp only [formOCD, id]

theorem formOC_hasDerivAt_E (a x v : ℝ) : HasDerivAt (formOCE a x) a v := by
  have h := ((hasDerivAt_id v).const_add (setCKQ x)).const_mul a |>.const_add x
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro z
  simp only [formOCE, id]

theorem formOC_hasDerivAt_Yc (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 ≤ v) :
    HasDerivAt (formOCYc a x) (formOCdc a x v) v := by
  have hE := (formOCE_pos ha hx hv).ne'
  have hL : 1 - a * x ≠ 0 := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have h := ((hasDerivAt_id v).const_mul (a * (1 - x))).div
    ((formOC_hasDerivAt_E a x v).const_mul (1 - a * x)) (mul_ne_zero hL hE)
  have e : formOCYc a x = fun z => a * (1 - x) * id z / ((1 - a * x) * formOCE a x z) := by
    funext z
    simp only [formOCYc, formOCE, id]
    ring
  rw [e]
  refine h.congr_deriv ?_
  unfold formOCdc
  have eE : formOCE a x v - a * v = x + a * setCKQ x := by unfold formOCE; ring
  rw [← eE]
  simp only [id]
  field_simp

theorem formOC_hasDerivAt_loglam (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hv : 0 ≤ v) :
    HasDerivAt (fun z => log (formOClam a x z)) (-(a / formOCE a x v)) v := by
  have hE := (formOCE_pos ha hx hv).ne'
  have hL : 1 - a * x ≠ 0 := by nlinarith [ha.1, ha.2, hx.1, hx.2]
  have h1x : 1 - x ≠ 0 := by linarith [hx.2]
  have hE' := formOC_hasDerivAt_E a x v
  have h := ((hE'.const_mul (1 - a * x)).log (mul_ne_zero hL hE)).const_sub (log (a * (1 - x)))
  have hev : ∀ᶠ z in nhds v, formOCE a x z ≠ 0 := hE'.continuousAt.eventually_ne hE
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · field_simp
  · filter_upwards [hev] with z hz
    rw [formOClam, log_div (mul_ne_zero ha.1.ne' h1x) (mul_ne_zero hL hz)]

/-- **`Â` (scaled form) has derivative `S_A`** for `v > 0`. -/
theorem hasDerivAt_formOCAhR (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    HasDerivAt (formOCAhR a x) (formOCSA a x v) v := by
  have hD := (formOCD_pos' ha hx hv.le).ne'
  have hD0 := (formOCD0_pos ha hx).ne'
  have hx1 : x - 1 ≠ 0 := by linarith [hx.2]
  have hDv := formOC_hasDerivAt_D a x v
  have hR0 : HasDerivAt (formOCR0 a x) (formOCdR0 a x v) v :=
    formOC_hasDerivAt_rat _ _ 2 hDv hD (by positivity)
  have hP0 : HasDerivAt (formOCP0x a x) (formOCdP0x a x v) v :=
    formOC_hasDerivAt_rat _ _ 2 hDv hD (by positivity)
  have hP1 : HasDerivAt (formOCP1x a x) (formOCdP1x a x v) v :=
    formOC_hasDerivAt_rat _ _ 1 hDv hD (by positivity)
  have hN1 : HasDerivAt (formOCN1x a x) (formOCdN1x a x v) v :=
    formOC_hasDerivAt_rat _ _ 2 hDv hD (by positivity)
  have hm1 : HasDerivAt (formOCm1 a x) (formOCdm1 a x v) v :=
    formOC_hasDerivAt_rat _ _ 2 hDv hD (by positivity)
  have hYc := formOC_hasDerivAt_Yc ha hx hv.le
  have hll := formOC_hasDerivAt_loglam ha hx hv.le
  have hvl := Real.hasDerivAt_mul_log hv.ne'
  have h := (((hR0.sub ((hP0.const_mul x).mul hYc)).sub
    (((hP1.const_mul x).mul (hYc.pow 2)).div_const 2)).sub ((hN1.const_mul x).mul hll)).sub
    (hm1.mul hvl)
  refine h.congr_deriv ?_
  unfold formOCSA
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

end

end QED.ChainProof.SetCK

end
