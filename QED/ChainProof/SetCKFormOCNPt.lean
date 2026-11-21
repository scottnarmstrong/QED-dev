/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCF0
public import QED.ChainProof.SetCKFormOCKFub

/-!
# Set (c), Stage K, closed forms: the `x`-integrand of `N(a, X)` in reduced form

Helper level (no frozen statement). Item 3 of the `ρ_oC` route (Stage K notes, Session 30+).
At fixed `(a, x)` and `v > 0`, put `q = Q(x) + v` (on the fibre `v = Q(X) - Q(x)` this is
`Q(X)`, independent of `x`). The sum of the closed-form `Y`-integral `g_k` (`formOCgk`) and of
`S_A = ∂_v Â` (`formOCSA`) is

`g_k + S_A = T₁ - T₂ - T₃ + T₄ + T₅ + R log Y_c` (**`formOC_gk_add_SA`**),

with `T_i = formOCNT_i a q x` and `R = formOCNR a q x` rational in `(a, q, x)`, whose only
denominators are `D = 1 + a(1 - a) q`, `E = x + a q`, `1 - a x` and `1 - x + a x`
(scratch `stageK/foc5/m1.py`, `m3.py`, `gpt.py`; checked exactly in sympy). The coefficients of
`log λ` and of `log v` in `g_k + S_A` coincide (both are `R`), so they combine to `log Y_c`.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- Piece `T1` of the `N`-integrand. -/
noncomputable def formOCNT1 (a q x : ℝ) : ℝ :=
  (a^5*q*x^4 - a^5*q*x^3 + a^4*q*x^4 - a^4*q*x^3 - 6*a^4*q*x^2 - 2*a^3*q*x^4 + 5*a^3*q*x^3
    - a^3*q*x^2 + 3*a^3*q*x + 3*a^3*x^4 - 7*a^3*x^3 + a^2*q*x^3 - 5*a^2*q*x^2 + 5*a^2*q*x
    - 2*a^2*x^4 + 2*a^2*x^3 + 6*a^2*x^2 + a*x^3 - 5*a*x^2 + 5*a*x) /
    (4 * (1 + a * (1 - a) * q) ^ 3)

/-- Piece `T2` of the `N`-integrand. -/
noncomputable def formOCNT2 (a q x : ℝ) : ℝ :=
  (3*a^6*q^3*x^4 - 6*a^6*q^3*x^3 + 2*a^6*q^3*x^2 + 2*a^6*q^2*x^5 - 2*a^6*q^2*x^4 - 4*a^5*q^3*x^4
    + 8*a^5*q^3*x^3 - 4*a^5*q^3*x^2 + a^5*q^3*x - 2*a^5*q^2*x^4 - 2*a^5*q^2*x^3 + a^5*q*x^6
    - a^5*q*x^5 + a^4*q^3*x^4 - 4*a^4*q^3*x^2 + 3*a^4*q^3*x - 2*a^4*q^2*x^5 + 3*a^4*q^2*x^4
    + 2*a^4*q^2*x^3 - a^4*q*x^5 - 4*a^4*q*x^4 + 5*a^3*q^2*x^4 - 10*a^3*q^2*x^3 + 2*a^3*q^2*x^2
    + 3*a^3*q^2*x - a^3*q*x^6 + 3*a^3*q*x^5 + a^3*q*x^4 + a^3*x^6 - 3*a^3*x^5 + a^2*q*x^5
    + a^2*q*x^4 - 8*a^2*q*x^3 + 6*a^2*q*x^2 - a^2*x^6 + 4*a^2*x^5 - 2*a^2*x^4 + a*x^5 - 3*a*x^4
    + 2*a*x^3) /
    (2 * (x + a * q) ^ 2 * (1 + a * (1 - a) * q) ^ 3)

/-- Piece `T3` of the `N`-integrand. -/
noncomputable def formOCNT3 (a q x : ℝ) : ℝ :=
  (2*a^4*q^2*x^4 - 4*a^4*q^2*x^3 + 2*a^4*q^2*x^2 + 2*a^4*q*x^5 - 2*a^4*q*x^4 - a^3*q^2*x^4
    + a^3*q^2*x^3 + a^3*q^2*x^2 - a^3*q^2*x - 2*a^3*q*x^4 + 2*a^3*q*x^3 + a^3*x^6 - a^3*x^5
    - 2*a^2*q*x^4 + 4*a^2*q*x^3 - 2*a^2*q*x^2 - 2*a^2*x^5 + 2*a^2*x^4) /
    (4 * (x + a * q) ^ 2 * (1 + a * (1 - a) * q) ^ 2)

/-- Piece `T4` of the `N`-integrand. -/
noncomputable def formOCNT4 (a q x : ℝ) : ℝ :=
  (-a^5*q^2*x^4 + 2*a^5*q*x^6 - 2*a^5*q*x^5 - 4*a^5*q*x^4 + 2*a^4*q^2*x^4 - 4*a^4*q*x^6
    + 8*a^4*q*x^5 - 2*a^4*q*x^4 + 4*a^4*x^6 - 8*a^4*x^5 - a^3*q^2*x^4 + 2*a^3*q*x^6 - 3*a^3*q*x^5
    + 3*a^3*q*x^4 - 2*a^3*q*x^3 + 4*a^3*q*x^2 - 5*a^3*x^6 + 12*a^3*x^5 - 4*a^3*x^4 - 3*a^2*q*x^5
    + 8*a^2*q*x^4 - 13*a^2*q*x^3 + 6*a^2*q*x^2 + a^2*x^6 + a^2*x^5 - 8*a^2*x^4 + 8*a^2*x^3
    - 2*a*x^5 + 5*a*x^4 - 8*a*x^3 + 4*a*x^2) /
    (4 * (x + a * q) * (1 - a * x) * (1 - x + a * x) * (1 + a * (1 - a) * q) ^ 2)

/-- Piece `T5` of the `N`-integrand. -/
noncomputable def formOCNT5 (a q x : ℝ) : ℝ :=
  (8*a^5*q^2*x^3 - 6*a^5*q^2*x^2 - 32*a^4*q^2*x^3 + 22*a^4*q^2*x^2 + 24*a^3*q^2*x^3
    - 59*a^3*q^2*x^2 + 40*a^3*q^2*x - 16*a^3*q*x^4 - 32*a^3*q*x^3 + 12*a^3*q*x^2 + 13*a^2*q^2*x^2
    - 10*a^2*q^2*x + 16*a^2*q*x^4 - 23*a^2*q*x^3 + 16*a^2*q*x^2 - 24*a^2*x^4 + 11*a*q*x^3
    + 11*a*q*x^2 - 16*a*q*x + 10*a*x^4 - 6*a*x^2 + 17*x^3 - 14*x^2) /
    (8 * (x + a * q) * (1 + a * (1 - a) * q) ^ 2)

/-- Piece `Ll` of the `N`-integrand. -/
noncomputable def formOCNR (a q x : ℝ) : ℝ :=
  (8*a^4*q^2*x^3 - a^4*q^2*x^2 - 6*a^4*q^2*x + 10*a^4*q*x^4 - 4*a^4*q*x^2 - 8*a^3*q^2*x^3
    + 18*a^3*q^2*x^2 - 32*a^3*q^2*x + 20*a^3*q^2 - 10*a^3*q*x^4 + 40*a^3*q*x^3 - 48*a^3*q*x^2
    + 12*a^3*q*x + 20*a^3*x^4 - 16*a^3*x^3 - 2*a^2*q^2*x^2 + 8*a^2*q^2*x - 5*a^2*q^2
    - 8*a^2*q*x^3 - 12*a^2*q*x^2 + 18*a^2*q*x - 5*a^2*x^4 - 4*a^2*x^3 + 4*a^2*x^2 + 10*a*q*x
    - 8*a*q - 8*a*x^3 + 4*a*x^2 + 4*a*x + 5*x^2 - 4*x) /
    (4 * (1 + a * (1 - a) * q) ^ 3)

theorem formOCN_ratD3 (c : Fin 3 → ℝ) (K D δ v : ℝ) (k : ℕ) :
    formOCRatD c K k D δ v =
      ((c 1 + 2 * c 2 * v) * D - k * δ * (c 0 + c 1 * v + c 2 * v ^ 2)) / (K * D ^ (k + 1)) := by
  simp [formOCRatD, formXPol, formXPolD, Fin.sum_univ_succ]
  ring

theorem formOCN_ratD2 (c : Fin 2 → ℝ) (K D δ v : ℝ) (k : ℕ) :
    formOCRatD c K k D δ v = (c 1 * D - k * δ * (c 0 + c 1 * v)) / (K * D ^ (k + 1)) := by
  simp [formOCRatD, formXPol, formXPolD, Fin.sum_univ_succ]

section

variable {a x v q : ℝ}

/-- The atoms on the fibre `q = Q(x) + v`. -/
theorem formOCN_atoms (hx : 1 - x ≠ 0) (hq : setCKQ x + v = q) :
    formOCD a x v = 1 + a * (1 - a) * q ∧
      formOCD0 a x = (1 - a * x) * (1 - x + a * x) / (1 - x) ∧
      formOCE a x v = x + a * q ∧ v = q - x ^ 2 / (1 - x) ∧ setCKQ x = x ^ 2 / (1 - x) := by
  refine ⟨by rw [formOCD, hq], ?_, by rw [formOCE, hq], by rw [← hq, setCKQ]; ring, rfl⟩
  rw [eq_div_iff hx, formOCD0_eq_mul (fun h => hx (by rw [h]; ring))]

theorem formOC_NT1_eq (hx : 1 - x ≠ 0) (hL : 1 - a * x ≠ 0) (hM : 1 - x + a * x ≠ 0)
    (hq : setCKQ x + v = q) : formOCdR0 a x v = formOCNT1 a q x := by
  obtain ⟨eD, eD0, -, ev, eQ⟩ := formOCN_atoms (a := a) hx hq
  have hx' : x - 1 ≠ 0 := fun h => hx (by linarith)
  unfold formOCdR0
  rw [formOCN_ratD3, eD, eD0]
  simp only [formOCR0N, Matrix.cons_val, eQ]
  push_cast
  subst ev
  unfold formOCNT1
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  generalize hEg : x + a * q = Eg at *
  generalize hLg : 1 - a * x = Lg at *
  generalize hMg : 1 - x + a * x = Mg at *
  generalize hOg : 1 - x = Og at *
  field_simp
  subst hDg hEg hLg hMg
  obtain rfl : x = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOC_NT2_eq (hx : 1 - x ≠ 0) (hL : 1 - a * x ≠ 0) (hM : 1 - x + a * x ≠ 0)
    (hE : x + a * q ≠ 0) (hD : 1 + a * (1 - a) * q ≠ 0)
    (hq : setCKQ x + v = q) :
    x * (formOCdP0x a x v * formOCYc a x v + formOCP0x a x v * formOCdc a x v) =
      formOCNT2 a q x := by
  obtain ⟨eD, eD0, eE, ev, eQ⟩ := formOCN_atoms (a := a) hx hq
  have hx' : x - 1 ≠ 0 := fun h => hx (by linarith)
  have eY : formOCYc a x v = a * v * (1 - x) / ((1 - a * x) * (x + a * q)) := by
    rw [formOCYc, hq]
  unfold formOCdP0x formOCP0x formOCdc
  rw [formOCN_ratD3, formOC_simp_rat3, eD, eD0, eY, eE]
  simp only [formOCP0xN, Matrix.cons_val, eQ]
  push_cast
  subst ev
  unfold formOCNT2
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  generalize hEg : x + a * q = Eg at *
  generalize hLg : 1 - a * x = Lg at *
  generalize hMg : 1 - x + a * x = Mg at *
  generalize hOg : 1 - x = Og at *
  field_simp
  subst hDg hEg hLg hMg
  obtain rfl : x = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOC_NT3_eq (hx : 1 - x ≠ 0) (hL : 1 - a * x ≠ 0) (hM : 1 - x + a * x ≠ 0)
    (hE : x + a * q ≠ 0) (hD : 1 + a * (1 - a) * q ≠ 0)
    (hq : setCKQ x + v = q) :
    x * (formOCdP1x a x v * formOCYc a x v ^ 2 / 2 +
      formOCP1x a x v * formOCYc a x v * formOCdc a x v) = formOCNT3 a q x := by
  obtain ⟨eD, eD0, eE, ev, eQ⟩ := formOCN_atoms (a := a) hx hq
  have hx' : x - 1 ≠ 0 := fun h => hx (by linarith)
  have eY : formOCYc a x v = a * v * (1 - x) / ((1 - a * x) * (x + a * q)) := by
    rw [formOCYc, hq]
  unfold formOCdP1x formOCP1x formOCdc
  rw [formOCN_ratD2, formOC_simp_rat2, eD, eD0, eY, eE]
  simp only [formOCP1xN, Matrix.cons_val, eQ]
  push_cast
  subst ev
  unfold formOCNT3
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  generalize hEg : x + a * q = Eg at *
  generalize hLg : 1 - a * x = Lg at *
  generalize hMg : 1 - x + a * x = Mg at *
  generalize hOg : 1 - x = Og at *
  field_simp
  subst hDg hEg hLg hMg
  obtain rfl : x = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOC_NT4_eq (hx : 1 - x ≠ 0) (hL : 1 - a * x ≠ 0) (hM : 1 - x + a * x ≠ 0)
    (hE : x + a * q ≠ 0) (hD : 1 + a * (1 - a) * q ≠ 0)
    (hq : setCKQ x + v = q) :
    x * formOCN1x a x v * (a / formOCE a x v) - formOCm1 a x v = formOCNT4 a q x := by
  obtain ⟨eD, eD0, eE, ev, -⟩ := formOCN_atoms (a := a) hx hq
  have hx' : x - 1 ≠ 0 := fun h => hx (by linarith)
  unfold formOCN1x formOCm1
  rw [formOC_simp_rat3, formOC_simp_rat2, eD, eD0, eE]
  simp only [formOCN1xN, formOCm1N, Matrix.cons_val]
  subst ev
  unfold formOCNT4
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  generalize hEg : x + a * q = Eg at *
  generalize hLg : 1 - a * x = Lg at *
  generalize hMg : 1 - x + a * x = Mg at *
  generalize hOg : 1 - x = Og at *
  field_simp
  subst hDg hEg hLg hMg
  obtain rfl : x = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOC_NT5_eq (hx : 1 - x ≠ 0) (hL : 1 - a * x ≠ 0) (ha : a ≠ 0)
    (hE : x + a * q ≠ 0) (hv : v ≠ 0) (hD : 1 + a * (1 - a) * q ≠ 0)
    (hq : setCKQ x + v = q) :
    formOCkn3 x a v (formOCD a x v) * (1 / formOCYc a x v ^ 2 - 1) / 2 +
        formOCkn2 x a v (formOCD a x v) * (1 / formOCYc a x v - 1) +
        formOCkp0 x a v (formOCD a x v) * (1 - formOCYc a x v) +
        formOCkp1 x a v (formOCD a x v) * (1 - formOCYc a x v ^ 2) / 2 -
        x ^ 2 * formOCYc a x v ^ 2 / (4 * v) = formOCNT5 a q x := by
  obtain ⟨eD, -, -, ev, eQ⟩ := formOCN_atoms (a := a) hx hq
  have eY : formOCYc a x v = a * v * (1 - x) / ((1 - a * x) * (x + a * q)) := by
    rw [formOCYc, hq]
  rw [eY, eD]
  unfold formOCkn3 formOCkn2 formOCkp0 formOCkp1 formOCNT5
  subst ev
  have hv' : q * (1 - x) - x ^ 2 ≠ 0 := fun h => hv (by field_simp; linarith)
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  generalize hEg : x + a * q = Eg at *
  generalize hLg : 1 - a * x = Lg at *
  generalize hMg : 1 - x + a * x = Mg at *
  generalize hOg : 1 - x = Og at *
  field_simp
  subst hDg hEg hLg hMg
  obtain rfl : x = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOC_NRl_eq (hx : 1 - x ≠ 0) (hL : 1 - a * x ≠ 0) (hM : 1 - x + a * x ≠ 0)
    (hD : 1 + a * (1 - a) * q ≠ 0)
    (hq : setCKQ x + v = q) :
    -(x * formOCdN1x a x v) - formOCkn1 x a v (formOCD a x v) = formOCNR a q x := by
  obtain ⟨eD, eD0, -, ev, -⟩ := formOCN_atoms (a := a) hx hq
  have hx' : x - 1 ≠ 0 := fun h => hx (by linarith)
  unfold formOCdN1x
  rw [formOCN_ratD3, eD, eD0]
  simp only [formOCN1xN, Matrix.cons_val]
  push_cast
  subst ev
  unfold formOCkn1 formOCNR
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  generalize hEg : x + a * q = Eg at *
  generalize hLg : 1 - a * x = Lg at *
  generalize hMg : 1 - x + a * x = Mg at *
  generalize hOg : 1 - x = Og at *
  field_simp
  subst hDg hEg hLg hMg
  obtain rfl : x = 1 - Og := by rw [← hOg]; ring
  ring

theorem formOC_NRv_eq (hx : 1 - x ≠ 0) (hL : 1 - a * x ≠ 0) (hM : 1 - x + a * x ≠ 0)
    (hD : 1 + a * (1 - a) * q ≠ 0)
    (hq : setCKQ x + v = q) :
    -(formOCm1 a x v + v * formOCdm1 a x v) - formOCkn1 x a v (formOCD a x v) =
      formOCNR a q x := by
  obtain ⟨eD, eD0, -, ev, -⟩ := formOCN_atoms (a := a) hx hq
  have hx' : x - 1 ≠ 0 := fun h => hx (by linarith)
  unfold formOCm1 formOCdm1
  rw [formOCN_ratD2, formOC_simp_rat2, eD, eD0]
  simp only [formOCm1N, Matrix.cons_val]
  push_cast
  subst ev
  unfold formOCkn1 formOCNR
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  generalize hEg : x + a * q = Eg at *
  generalize hLg : 1 - a * x = Lg at *
  generalize hMg : 1 - x + a * x = Mg at *
  generalize hOg : 1 - x = Og at *
  field_simp
  subst hDg hEg hLg hMg
  obtain rfl : x = 1 - Og := by rw [← hOg]; ring
  ring

/-- **The `x`-integrand of `N` in reduced form.** -/
theorem formOC_gk_add_SA (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    formOCgk x a v + formOCSA a x v =
      formOCNT1 a (setCKQ x + v) x - formOCNT2 a (setCKQ x + v) x -
        formOCNT3 a (setCKQ x + v) x + formOCNT4 a (setCKQ x + v) x +
        formOCNT5 a (setCKQ x + v) x +
        formOCNR a (setCKQ x + v) x * log (formOCYc a x v) := by
  have hlam := formOClam_pos ha hx hv.le
  have hE := formOCE_pos ha hx hv.le
  have h1x : 1 - x ≠ 0 := by linarith [hx.2]
  have hL : 1 - a * x ≠ 0 := by nlinarith [ha.2, hx.2, ha.1, hx.1]
  have hM : 1 - x + a * x ≠ 0 := by nlinarith [ha.2, hx.2, ha.1, hx.1]
  have hE' : x + a * (setCKQ x + v) ≠ 0 := by rw [← formOCE]; exact hE.ne'
  have hD' : 1 + a * (1 - a) * (setCKQ x + v) ≠ 0 := by
    rw [← formOCD]; exact (formOCD_pos' ha hx hv.le).ne'
  have e1 := formOC_NT1_eq h1x hL hM (a := a) (v := v) rfl
  have e2 := formOC_NT2_eq h1x hL hM hE' hD' rfl
  have e3 := formOC_NT3_eq h1x hL hM hE' hD' rfl
  have e4 := formOC_NT4_eq h1x hL hM hE' hD' rfl
  have e5 := formOC_NT5_eq h1x hL ha.1.ne' hE' hv.ne' hD' rfl
  have el := formOC_NRl_eq h1x hL hM hD' (v := v) rfl
  have ev := formOC_NRv_eq h1x hL hM hD' (v := v) rfl
  unfold formOCgk formOCLaurI formOCSA
  rw [formOCYc_eq_mul, log_mul hv.ne' hlam.ne'] at *
  linear_combination e1 - e2 - e3 + e4 + e5 + log (formOClam a x v) * el + log v * ev

end

end QED.ChainProof.SetCK

end
