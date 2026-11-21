/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCNPt

/-!
# Set (c), Stage K, closed forms: the `x`-antiderivative of the `N`-integrand

Helper level (no frozen statement). Item 3 of the `ρ_oC` route (Stage K notes, Session 30+).
On the fibre the `N`-integrand is `T + R log Y_c` (`formOC_gk_add_SA`), with
`T = T₁ - T₂ - T₃ + T₄ + T₅` and `R = formOCNR a q x` a polynomial of degree four in `x`
(coefficients **`formOCNcR`**). The rational part splits (**`formOCN_T_eq`**, `a ≠ 1/2`) as

`T = polyT(x) + r₁/(1 - a x) + r₂/(1 - x + a x) + r₃/(x + a q) + r₄/(x + a q)²`.

With `P = ∫₀ˣ R` (**`formOCNcP`**) and the difference quotients `formOCNquo` of `P`, the
function **`formOCNF`** (polynomial part, `P(x)(log a - log(1 - X))`,
`-quo_X(x) (X - x) log(X - x)`, `(P(x) - P(ρ)) log(X + (1 - X) x)` with `ρ = -X/(1 - X)`, and
`(P(r) - P(x) + c) log ℓ` for the remaining linear letters, plus `-r₄/(x + a q)`) has derivative
the integrand **`formOCNIg`** on `(0, X)` (**`hasDerivAt_formOCNF`**). Here `q` and `X` are
independent parameters; the fibre relation `q = Q(X)` enters only when `log Y_c` is split.
Scratch: `stageK/foc5/g1.py`, `g2.py`.
-/

@[expose] public section

open Real Set

namespace QED.ChainProof.SetCK

/-- The difference quotient `(p(x) - p(r))/(x - r)` of a quintic, as a coefficient vector. -/
noncomputable def formOCNquo (c : Fin 6 → ℝ) (r : ℝ) : Fin 5 → ℝ :=
  ![c 1 + c 2 * r + c 3 * r ^ 2 + c 4 * r ^ 3 + c 5 * r ^ 4,
    c 2 + c 3 * r + c 4 * r ^ 2 + c 5 * r ^ 3, c 3 + c 4 * r + c 5 * r ^ 2, c 4 + c 5 * r, c 5]

/-- The antiderivative vanishing at `0` of a quartic. -/
noncomputable def formOCNint (c : Fin 5 → ℝ) : Fin 6 → ℝ :=
  ![0, c 0, c 1 / 2, c 2 / 3, c 3 / 4, c 4 / 5]

theorem formOCN_quo (c : Fin 6 → ℝ) (r x : ℝ) :
    formXPol c x - formXPol c r = (x - r) * formXPol (formOCNquo c r) x := by
  simp [formXPol, Fin.sum_univ_succ, formOCNquo]
  ring

theorem formOCN_hasDerivAt_int (c : Fin 5 → ℝ) (x : ℝ) :
    HasDerivAt (formXPol (formOCNint c)) (formXPol c x) x := by
  refine (hasDerivAt_formXPol (formOCNint c) x).congr_deriv ?_
  simp [formXPol, formXPolD, formOCNint, Fin.sum_univ_succ]
  ring

theorem formOCN_pol5 (c : Fin 5 → ℝ) (x : ℝ) :
    formXPol c x = c 0 + c 1 * x + c 2 * x ^ 2 + c 3 * x ^ 3 + c 4 * x ^ 4 := by
  simp [formXPol, Fin.sum_univ_succ]
  ring

/-- `(A log ℓ)' = A' log ℓ + A β/ℓ` for `ℓ = α + β x > 0`. -/
theorem formOCN_hasDerivAt_mul_log {A : ℝ → ℝ} {A' α β x : ℝ} (hA : HasDerivAt A A' x)
    (hl : 0 < α + β * x) :
    HasDerivAt (fun z => A z * log (α + β * z)) (A' * log (α + β * x) + A x * (β / (α + β * x)))
      x := by
  have hl' : HasDerivAt (fun z => α + β * z) β x := by
    simpa using ((hasDerivAt_id x).const_mul β).const_add α
  exact (hA.mul (hl'.log hl.ne')).congr_deriv (by ring)

/-- Coefficients (in `x`) of `R`. -/
noncomputable def formOCNcR (a q : ℝ) : Fin 5 → ℝ :=
  ![
    -a*q*(20*a^2*q - 5*a*q - 8)/(4*(-(1 + a*(1 - a)*q))^3),
    (3*a^4*q^2 + 16*a^3*q^2 - 6*a^3*q - 4*a^2*q^2 - 9*a^2*q - 5*a*q - 2*a + 2)/(2*(-(1 + a*(1
      - a)*q))^3),
    (a^4*q^2 + 4*a^4*q - 18*a^3*q^2 + 48*a^3*q + 2*a^2*q^2 + 12*a^2*q - 4*a^2 - 4*a - 5)/(4*(-(1
      + a*(1 - a)*q))^3),
    -a*(2*a^3*q^2 - 2*a^2*q^2 + 10*a^2*q - 4*a^2 - 2*a*q - a - 2)/(-(1 + a*(1 - a)*q))^3,
    -5*a^2*(2*a^2*q - 2*a*q + 4*a - 1)/(4*(-(1 + a*(1 - a)*q))^3)]

/-- Polynomial part of `T1`. -/
noncomputable def formOCNcT1 (a q : ℝ) : Fin 5 → ℝ :=
  ![
    0,
    -a*(3*a^2*q + 5*a*q + 5)/(4*(-(1 + a*(1 - a)*q))^3),
    a*(6*a^3*q + a^2*q + 5*a*q - 6*a + 5)/(4*(-(1 + a*(1 - a)*q))^3),
    a*(a^4*q + a^3*q - 5*a^2*q + 7*a^2 - a*q - 2*a - 1)/(4*(-(1 + a*(1 - a)*q))^3),
    -a^2*(a^3*q + a^2*q - 2*a*q + 3*a - 2)/(4*(-(1 + a*(1 - a)*q))^3)]

/-- Polynomial part of `T2`. -/
noncomputable def formOCNcT2 (a q : ℝ) : Fin 5 → ℝ :=
  ![
    a^2*q*(3*a*q + 2)/2,
    -a*(2*a^7*q^4 - 6*a^6*q^4 + a^6*q^3 + 6*a^5*q^4 - 9*a^5*q^3 - 2*a^4*q^4 + 15*a^4*q^3
      - 3*a^4*q^2 - 7*a^3*q^3 + 12*a^3*q^2 - 9*a^2*q^2 + 4*a^2*q - 2*a*q + 2)/(2*(-(1 + a*(1
      - a)*q))^3),
    a*(a^6*q^3 - 3*a^5*q^3 + 3*a^4*q^3 - 3*a^4*q^2 - a^3*q^3 + 6*a^3*q^2 - 2*a^3*q - 3*a^2*q^2
      + 7*a^2*q + a*q + 2*a + 3)/(2*(-(1 + a*(1 - a)*q))^3),
    a*(a^4*q + 3*a^3*q - 5*a^2*q + 3*a^2 - a*q - 4*a - 1)/(2*(-(1 + a*(1 - a)*q))^3),
    -a^2*(a - 1)*(a^2*q + a*q + 1)/(2*(-(1 + a*(1 - a)*q))^3)]

/-- Coefficient of `1/(x + a q)²` in `T2`. -/
noncomputable def formOCNrT2E2 (a q : ℝ) : ℝ :=
  a^4*q^3*(a*q + 1)/2

/-- Coefficient of `1/(x + a q)` in `T2`. -/
noncomputable def formOCNrT2E (a q : ℝ) : ℝ :=
  -a^3*q^2*(4*a*q + 3)/2

/-- Polynomial part of `T3`. -/
noncomputable def formOCNcT3 (a q : ℝ) : Fin 5 → ℝ :=
  ![
    -a^2*q*(3*a*q + 2)/4,
    a^2*q*(2*a^4*q^2 - 4*a^3*q^2 + a^3*q + 2*a^2*q^2 - 6*a^2*q + 5*a*q - 2*a + 4)/(4*(-(1 + a*(1
      - a)*q))^2),
    -a^2*(a^3*q^2 - 2*a^2*q^2 + a*q^2 - 2*a*q + 2*q - 2)/(4*(-(1 + a*(1 - a)*q))^2),
    -a^2*(a + 2)/(4*(-(1 + a*(1 - a)*q))^2),
    a^3/(4*(-(1 + a*(1 - a)*q))^2)]

/-- Coefficient of `1/(x + a q)²` in `T3`. -/
noncomputable def formOCNrT3E2 (a q : ℝ) : ℝ :=
  -a^4*q^3*(a*q + 1)/4

/-- Coefficient of `1/(x + a q)` in `T3`. -/
noncomputable def formOCNrT3E (a q : ℝ) : ℝ :=
  a^3*q^2*(4*a*q + 3)/4

/-- Polynomial part of `T4`. -/
noncomputable def formOCNcT4 (a q : ℝ) : Fin 5 → ℝ :=
  ![
    (2*a^8*q^3 - 4*a^7*q^3 + 6*a^7*q^2 + 2*a^6*q^3 - 12*a^6*q^2 + 4*a^6*q + 6*a^5*q^2 - 8*a^5*q
      + 4*a^4*q + a^2 - a + 1)/(4*a^2*(a - 1)^2*(-(1 + a*(1 - a)*q))),
    -(2*a^5*q^2 - 2*a^4*q^2 + 6*a^4*q - 6*a^3*q + 4*a^3 - 4*a^2 + 1)/(4*a*(a - 1)*(-(1 + a*(1
      - a)*q))),
    (2*a^4*q^2 - 2*a^3*q^2 + 6*a^3*q - 7*a^2*q + 8*a^2 - a*q - 4*a - 1)/(4*(-(1 + a*(1 - a)*q))^2),
    -a*(2*a^2*q - 2*a*q + 4*a - 1)/(4*(-(1 + a*(1 - a)*q))^2),
    0]

/-- Coefficient of `1/(1 - a x)` in `T4`. -/
noncomputable def formOCNrT4L (a q : ℝ) : ℝ :=
  -(a - 1)/(4*a^2*(2*a - 1)*(-(1 + a*(1 - a)*q)))

/-- Coefficient of `1/(1 - x + a x)` in `T4`. -/
noncomputable def formOCNrT4M (a q : ℝ) : ℝ :=
  -a/(4*(a - 1)^2*(2*a - 1)*(-(1 + a*(1 - a)*q)))

/-- Coefficient of `1/(x + a q)` in `T4`. -/
noncomputable def formOCNrT4E (a q : ℝ) : ℝ :=
  -a^3*q^2*(a*q + 1)*(a*q + 2)/(2*(-(1 + a*(1 - a)*q)))

/-- Polynomial part of `T5`. -/
noncomputable def formOCNcT5 (a q : ℝ) : Fin 5 → ℝ :=
  ![
    a*q*(4*a^2*q + 3*a - 1)/4,
    -(4*a^6*q^3 - 8*a^5*q^3 + 3*a^5*q^2 + 4*a^4*q^3 - 15*a^4*q^2 + 13*a^3*q^2 - 6*a^3*q - a^2*q^2
      - 8*a^2*q + 3*a*q + 3*a + 7)/(4*(-(1 + a*(1 - a)*q))^2),
    (8*a^5*q^2 - 16*a^4*q^2 + 8*a^3*q^2 - 8*a^3*q - 33*a^2*q + 11*a*q + 17)/(8*(-(1 + a*(1
      - a)*q))^2),
    -a*(8*a^2*q - 8*a*q + 12*a - 5)/(4*(-(1 + a*(1 - a)*q))^2),
    0]

/-- Coefficient of `1/(x + a q)` in `T5`. -/
noncomputable def formOCNrT5E (a q : ℝ) : ℝ :=
  -a^2*q^2*(4*a^2*q + 3*a - 1)/4

/-- Coefficients (in `x`) of the polynomial part of `T`. -/
noncomputable def formOCNcT (a q : ℝ) : Fin 5 → ℝ := fun i =>
  formOCNcT1 a q i - formOCNcT2 a q i - formOCNcT3 a q i + formOCNcT4 a q i + formOCNcT5 a q i

/-- Coefficient of `1/(1 - a x)` in `T`. -/
noncomputable def formOCNr1 (a q : ℝ) : ℝ := formOCNrT4L a q

/-- Coefficient of `1/(1 - x + a x)` in `T`. -/
noncomputable def formOCNr2 (a q : ℝ) : ℝ := formOCNrT4M a q

/-- Coefficient of `1/(x + a q)` in `T`. -/
noncomputable def formOCNr3 (a q : ℝ) : ℝ :=
  -formOCNrT2E a q - formOCNrT3E a q + formOCNrT4E a q + formOCNrT5E a q

/-- Coefficient of `1/(x + a q)²` in `T`. -/
noncomputable def formOCNr4 (a q : ℝ) : ℝ := -formOCNrT2E2 a q - formOCNrT3E2 a q

/-- `P = ∫₀ˣ R`. -/
noncomputable def formOCNcP (a q : ℝ) : Fin 6 → ℝ := formOCNint (formOCNcR a q)

/-- The root `ρ = -X/(1 - X)` of `X + (1 - X) x`. -/
noncomputable def formOCNrho (X : ℝ) : ℝ := -X / (1 - X)

/-- The coefficients of the polynomial part of `F'`. -/
noncomputable def formOCNcd (a q X : ℝ) : Fin 5 → ℝ := fun i =>
  formOCNcT a q i - formOCNquo (formOCNcP a q) (formOCNrho X) i +
    formOCNquo (formOCNcP a q) (1 / a) i + formOCNquo (formOCNcP a q) (-(a * q)) i -
    formOCNquo (formOCNcP a q) X i

/-- **The `x`-antiderivative of the `N`-integrand.** -/
noncomputable def formOCNF (a q X x : ℝ) : ℝ :=
  formXPol (formOCNint (formOCNcd a q X)) x +
    formXPol (formOCNcP a q) x * (log a - log (1 - X)) -
    formXPol (formOCNquo (formOCNcP a q) X) x * ((X - x) * log (X - x)) +
    (formXPol (formOCNcP a q) x - formXPol (formOCNcP a q) (formOCNrho X)) *
      log (X + (1 - X) * x) +
    (formXPol (formOCNcP a q) (1 / a) - formXPol (formOCNcP a q) x - formOCNr1 a q / a) *
      log (1 + -a * x) +
    (formXPol (formOCNcP a q) (-(a * q)) - formXPol (formOCNcP a q) x + formOCNr3 a q) *
      log (a * q + 1 * x) +
    formOCNr2 a q / (a - 1) * log (1 + (a - 1) * x) - formOCNr4 a q / (x + a * q)

/-- **The `N`-integrand** `T + R log Y_c`, with `log Y_c` split into letters. -/
noncomputable def formOCNIg (a q X x : ℝ) : ℝ :=
  formOCNT1 a q x - formOCNT2 a q x - formOCNT3 a q x + formOCNT4 a q x + formOCNT5 a q x +
    formOCNR a q x * (log a + log (X - x) + log (X + (1 - X) * x) - log (1 - X) -
      log (1 + -a * x) - log (a * q + 1 * x))

section

variable {a q X x : ℝ}

theorem formOCN_R_eq (hD : 1 + a * (1 - a) * q ≠ 0) :
    formXPol (formOCNcR a q) x = formOCNR a q x := by
  rw [formOCN_pol5]
  simp only [formOCNcR, formOCNR, Matrix.cons_val]
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  field_simp
  subst hDg
  ring

theorem formOCN_T1_pf (hD : 1 + a * (1 - a) * q ≠ 0) :
    formOCNT1 a q x =
      formXPol (formOCNcT1 a q) x := by
  rw [formOCN_pol5]
  simp only [formOCNcT1, Matrix.cons_val]
  unfold formOCNT1
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  generalize hEg : x + a * q = Eg at *
  generalize hLg : 1 - a * x = Lg at *
  generalize hMg : 1 - x + a * x = Mg at *
  field_simp
  subst hDg hLg hMg
  obtain rfl : x = Eg - a * q := by rw [← hEg]; ring
  ring

theorem formOCN_T2_pf (hD : 1 + a * (1 - a) * q ≠ 0) (hE : x + a * q ≠ 0) :
    formOCNT2 a q x =
      formXPol (formOCNcT2 a q) x +
        formOCNrT2E a q / (x + a * q) +
        formOCNrT2E2 a q / (x + a * q) ^ 2 := by
  rw [formOCN_pol5]
  simp only [formOCNcT2, Matrix.cons_val]
  unfold formOCNT2 formOCNrT2E formOCNrT2E2
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  generalize hEg : x + a * q = Eg at *
  generalize hLg : 1 - a * x = Lg at *
  generalize hMg : 1 - x + a * x = Mg at *
  field_simp
  subst hDg hLg hMg
  obtain rfl : x = Eg - a * q := by rw [← hEg]; ring
  ring

theorem formOCN_T3_pf (hD : 1 + a * (1 - a) * q ≠ 0) (hE : x + a * q ≠ 0) :
    formOCNT3 a q x =
      formXPol (formOCNcT3 a q) x +
        formOCNrT3E a q / (x + a * q) +
        formOCNrT3E2 a q / (x + a * q) ^ 2 := by
  rw [formOCN_pol5]
  simp only [formOCNcT3, Matrix.cons_val]
  unfold formOCNT3 formOCNrT3E formOCNrT3E2
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  generalize hEg : x + a * q = Eg at *
  generalize hLg : 1 - a * x = Lg at *
  generalize hMg : 1 - x + a * x = Mg at *
  field_simp
  subst hDg hLg hMg
  obtain rfl : x = Eg - a * q := by rw [← hEg]; ring
  ring

theorem formOCN_T4_pf (hD : 1 + a * (1 - a) * q ≠ 0) (hE : x + a * q ≠ 0)
    (hL : 1 - a * x ≠ 0) (hM : 1 - x + a * x ≠ 0) (ha : a ≠ 0) (ha1 : a - 1 ≠ 0)
    (h2a : 2 * a - 1 ≠ 0) :
    formOCNT4 a q x =
      formXPol (formOCNcT4 a q) x +
        formOCNrT4L a q / (1 - a * x) +
        formOCNrT4M a q / (1 - x + a * x) +
        formOCNrT4E a q / (x + a * q) := by
  rw [formOCN_pol5]
  simp only [formOCNcT4, Matrix.cons_val]
  unfold formOCNT4 formOCNrT4L formOCNrT4M formOCNrT4E
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  generalize hEg : x + a * q = Eg at *
  generalize hLg : 1 - a * x = Lg at *
  generalize hMg : 1 - x + a * x = Mg at *
  generalize hAg : 2 * a - 1 = Ag at *
  field_simp
  subst hDg hEg hLg hMg hAg
  ring

theorem formOCN_T5_pf (hD : 1 + a * (1 - a) * q ≠ 0) (hE : x + a * q ≠ 0) :
    formOCNT5 a q x =
      formXPol (formOCNcT5 a q) x +
        formOCNrT5E a q / (x + a * q) := by
  rw [formOCN_pol5]
  simp only [formOCNcT5, Matrix.cons_val]
  unfold formOCNT5 formOCNrT5E
  generalize hDg : 1 + a * (1 - a) * q = Dg at *
  generalize hEg : x + a * q = Eg at *
  generalize hLg : 1 - a * x = Lg at *
  generalize hMg : 1 - x + a * x = Mg at *
  field_simp
  subst hDg hLg hMg
  obtain rfl : x = Eg - a * q := by rw [← hEg]; ring
  ring

theorem formOCN_T_eq (hD : 1 + a * (1 - a) * q ≠ 0) (hE : x + a * q ≠ 0) (hL : 1 - a * x ≠ 0)
    (hM : 1 - x + a * x ≠ 0) (ha : a ≠ 0) (ha1 : a - 1 ≠ 0) (h2a : 2 * a - 1 ≠ 0) :
    formOCNT1 a q x - formOCNT2 a q x - formOCNT3 a q x + formOCNT4 a q x + formOCNT5 a q x =
      formXPol (formOCNcT a q) x + formOCNr1 a q / (1 - a * x) +
        formOCNr2 a q / (1 - x + a * x) + formOCNr3 a q / (x + a * q) +
        formOCNr4 a q / (x + a * q) ^ 2 := by
  rw [formOCN_T1_pf hD, formOCN_T2_pf hD hE, formOCN_T3_pf hD hE,
    formOCN_T4_pf hD hE hL hM ha ha1 h2a, formOCN_T5_pf hD hE]
  simp only [formOCN_pol5, formOCNcT, formOCNr1, formOCNr2, formOCNr3, formOCNr4]
  ring

theorem formOCN_cd_eq (a q X x : ℝ) :
    formXPol (formOCNcd a q X) x = formXPol (formOCNcT a q) x -
      formXPol (formOCNquo (formOCNcP a q) (formOCNrho X)) x +
      formXPol (formOCNquo (formOCNcP a q) (1 / a)) x +
      formXPol (formOCNquo (formOCNcP a q) (-(a * q))) x -
      formXPol (formOCNquo (formOCNcP a q) X) x := by
  simp only [formOCN_pol5, formOCNcd]
  ring

/-- **The derivative of the `x`-antiderivative.** -/
theorem hasDerivAt_formOCNF (ha : a ∈ Ioo (0 : ℝ) 1) (h2a : 2 * a - 1 ≠ 0) (hq : 0 < q)
    (hX1 : X < 1) (hx : x ∈ Ioo 0 X) :
    HasDerivAt (formOCNF a q X) (formOCNIg a q X x) x := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hx0, hxX⟩ := hx
  have h1X : 0 < 1 - X := by linarith
  have hXx : 0 < X - x := by linarith
  have hl2 : 0 < X + (1 - X) * x := by nlinarith
  have hlL : 0 < 1 + -a * x := by nlinarith
  have hlE : 0 < a * q + 1 * x := by nlinarith
  have hlM : 0 < 1 + (a - 1) * x := by nlinarith
  have hE : 0 < x + a * q := by nlinarith
  set P := formXPol (formOCNcP a q) with hPdef
  set R := formXPol (formOCNcR a q) with hRdef
  set QX := formXPol (formOCNquo (formOCNcP a q) X) with hQXdef
  set Qρ := formXPol (formOCNquo (formOCNcP a q) (formOCNrho X)) with hQρdef
  set Q1 := formXPol (formOCNquo (formOCNcP a q) (1 / a)) with hQ1def
  set QE := formXPol (formOCNquo (formOCNcP a q) (-(a * q))) with hQEdef
  have hP : ∀ z, HasDerivAt P (R z) z := fun z => formOCN_hasDerivAt_int _ z
  have hQX : HasDerivAt QX (formXPol (formXPolD (formOCNquo (formOCNcP a q) X)) x) x :=
    hasDerivAt_formXPol _ x
  -- `R = QX + (x - X) QX'`
  have dX : R x = QX x + (x - X) * formXPol (formXPolD (formOCNquo (formOCNcP a q) X)) x := by
    have e : (fun z => P z - P X) = fun z => (z - X) * QX z := funext fun z => formOCN_quo _ X z
    have h1 : HasDerivAt (fun z => P z - P X) (R x) x := (hP x).sub_const _
    have h2 : HasDerivAt (fun z => (z - X) * QX z)
        (1 * QX x + (x - X) * formXPol (formXPolD (formOCNquo (formOCNcP a q) X)) x) x :=
      ((hasDerivAt_id x).sub_const X).mul hQX
    rw [e] at h1
    rw [h1.unique h2, one_mul]
  have h1 := formOCN_hasDerivAt_int (formOCNcd a q X) x
  have h2 : HasDerivAt (fun z => P z * (log a - log (1 - X))) (R x * (log a - log (1 - X))) x :=
    (hP x).mul_const _
  have h3 : HasDerivAt (fun z => QX z * ((X - z) * log (X - z)))
      (-(R x * log (X - x)) - QX x) x := by
    have hu : HasDerivAt (fun z => X - z) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub X
    refine (hQX.mul (hu.mul (hu.log hXx.ne'))).congr_deriv ?_
    simp only [Pi.mul_apply]
    rw [dX]
    field_simp
    ring
  have h4 : HasDerivAt (fun z => (P z - P (formOCNrho X)) * log (X + (1 - X) * z))
      (R x * log (X + (1 - X) * x) + Qρ x) x := by
    refine (formOCN_hasDerivAt_mul_log ((hP x).sub_const _) hl2).congr_deriv ?_
    have e : X + (1 - X) * x = (1 - X) * (x - formOCNrho X) := by
      unfold formOCNrho
      field_simp
      ring
    have hne : x - formOCNrho X ≠ 0 := fun h => by rw [h, mul_zero] at e; linarith
    have e2 : (1 - X) / (X + (1 - X) * x) = 1 / (x - formOCNrho X) := by
      rw [e]
      field_simp
    rw [formOCN_quo, e2]
    field_simp
    rfl
  have h5 : HasDerivAt (fun z => (P (1 / a) - P z - formOCNr1 a q / a) * log (1 + -a * z))
      (-R x * log (1 + -a * x) + (-Q1 x + formOCNr1 a q / (1 - a * x))) x := by
    refine (formOCN_hasDerivAt_mul_log (((hP x).const_sub _).sub_const _) hlL).congr_deriv ?_
    have e := formOCN_quo (formOCNcP a q) (1 / a) x
    rw [show P (1 / a) = P x - (x - 1 / a) * Q1 x by rw [← hPdef] at e; linarith]
    have : 1 - a * x ≠ 0 := by linarith
    rw [show 1 + -a * x = 1 - a * x by ring]
    field_simp
    ring
  have h6 : HasDerivAt (fun z => (P (-(a * q)) - P z + formOCNr3 a q) * log (a * q + 1 * z))
      (-R x * log (a * q + 1 * x) + (-QE x + formOCNr3 a q / (x + a * q))) x := by
    refine (formOCN_hasDerivAt_mul_log (((hP x).const_sub _).add_const _) hlE).congr_deriv ?_
    have e := formOCN_quo (formOCNcP a q) (-(a * q)) x
    rw [show P (-(a * q)) = P x - (x + a * q) * QE x by rw [← hPdef] at e; linarith,
      show a * q + 1 * x = x + a * q by ring]
    field_simp
    ring
  have h7 : HasDerivAt (fun z => formOCNr2 a q / (a - 1) * log (1 + (a - 1) * z))
      (formOCNr2 a q / (1 - x + a * x)) x := by
    refine (formOCN_hasDerivAt_mul_log (hasDerivAt_const x (formOCNr2 a q / (a - 1)))
      hlM).congr_deriv ?_
    have : a - 1 ≠ 0 := by linarith
    have : 1 - x + a * x ≠ 0 := by linarith
    field_simp
    ring
  have h8 : HasDerivAt (fun z => formOCNr4 a q / (z + a * q)) (-(formOCNr4 a q / (x + a * q) ^ 2))
      x := by
    refine ((hasDerivAt_const x (formOCNr4 a q)).div ((hasDerivAt_id x).add_const (a * q))
      hE.ne').congr_deriv ?_
    simp
    ring
  have h := ((((((h1.add h2).sub h3).add h4).add h5).add h6).add h7).sub h8
  refine h.congr_deriv ?_
  have eT := formOCN_T_eq (a := a) (q := q) (x := x) (by nlinarith) hE.ne' (by linarith)
    (by linarith) ha0.ne' (by linarith) h2a
  have eR := formOCN_R_eq (a := a) (q := q) (x := x) (by nlinarith)
  have ecd := formOCN_cd_eq a q X x
  unfold formOCNIg
  linear_combination ecd - eT + (log a + log (X - x) + log (X + (1 - X) * x) - log (1 - X) -
    log (1 + -a * x) - log (a * q + 1 * x)) * eR

end

end QED.ChainProof.SetCK

end
