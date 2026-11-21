/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCLeib

/-!
# Set (c), Stage K, closed forms: `ℓ_a` in letters

Helper level (no frozen statement). Item 2 (OCLeib) of the `ρ_oC` route, the closed form.
For `a ∈ (0, 1)`, `a ≠ 1/2`, `X ∈ (0, 1)` (**`formOCell_eq`**):

`ℓ_a(X) = r + c_X (log X - log(1 - X)) + c_L log(1 - a X) + c_M log(1 - X + a X)
  + c_2 log(2 - X)` (**`formOCellC`**),

with the rational coefficients `formOCellCR`, `formOCellCX`, `formOCellCL`, `formOCellCM`,
`formOCellC2` (Stage K notes, `foc4/n5.out`, `ell`; the `a = 1/2` poles of `c_L`, `c_M` are
spurious). Proof: the by-parts antiderivative in `s` of the integrand `formOCLg`,

`G(s) = (s β(X s) - β(X)) Λ(s, X) + R(s) + c_L log(1 - a X s) + c_M log(1 - X s + a X s)
  + c_2 log(1 + s - X s) - (c_X/2) log(1 - X s)` (**`formOCLG`**),

has derivative `formOCLg` on `(0, 1)` (**`hasDerivAt_formOCLG`**; the rational identity
`formOCLG_alg` is split into `formOCL_S1`–`formOCL_S3` with opaque atoms), `G(0⁺) = G(0)`, and
at `s = 1⁻` the term `(s β(X s) - β(X)) log(1 - s) = -h(s) (1 - s) log(1 - s) → 0`.
-/

@[expose] public section

open Real Set Filter MeasureTheory Topology

namespace QED.ChainProof.SetCK

/-- Rational part of `ℓ_a`. -/
noncomputable def formOCellCR (a X : ℝ) : ℝ :=
  -X ^ 2 * (X - 2) * (3 * X ^ 2 * a ^ 2 - 3 * X ^ 2 * a - 3 * X * a ^ 2 + 3 * X * a - 2 * X +
    2 * a ^ 2 - 2 * a + 2) / (8 * a ^ 2 * (X - 1) ^ 3 * (a - 1) ^ 2)

/-- Coefficient of `log(1 - a X)` in `ℓ_a`. -/
noncomputable def formOCellCL (a X : ℝ) : ℝ :=
  X * (X - 2) * (a - 1) / (4 * a ^ 3 * (X - 1) * (2 * a - 1) * (X * a - 1) * (X * a - X + 1))

/-- Coefficient of `log(1 - X + a X)` in `ℓ_a`. -/
noncomputable def formOCellCM (a X : ℝ) : ℝ :=
  -X * a * (X - 2) / (4 * (X - 1) * (a - 1) ^ 3 * (2 * a - 1) * (X * a - 1) * (X * a - X + 1))

/-- Coefficient of `log(2 - X)` in `ℓ_a`. -/
noncomputable def formOCellC2 (a X : ℝ) : ℝ :=
  X ^ 4 * (X ^ 4 - 4 * X ^ 3 + 6 * X ^ 2 - 4 * X + 2) /
    (4 * (X - 1) ^ 4 * (X * a - 1) * (X * a - X + 1))

/-- Coefficient of `log X - log(1 - X)` in `ℓ_a`. -/
noncomputable def formOCellCX (a X : ℝ) : ℝ := X ^ 4 / (2 * (X * a - 1) * (X * a - X + 1))

/-- **`ℓ_a` in letters.** -/
noncomputable def formOCellC (a X : ℝ) : ℝ :=
  formOCellCR a X + formOCellCX a X * (log X - log (1 - X)) +
    formOCellCL a X * log (1 - a * X) + formOCellCM a X * log (1 - X + a * X) +
    formOCellC2 a X * log (2 - X)

/-- The polynomial part of the `s`-antiderivative. -/
noncomputable def formOCLRp (a X s : ℝ) : ℝ :=
  -X ^ 2 * (X - 2) / (8 * a ^ 2 * (X - 1) ^ 3 * (a - 1) ^ 2) *
    (s * ((X ^ 2 * a ^ 2 - X ^ 2 * a - X * a ^ 2 + X * a) * s +
      (2 * X ^ 2 * a ^ 2 - 2 * X ^ 2 * a - 2 * X * a ^ 2 + 2 * X * a - 2 * X + 2 * a ^ 2 -
        2 * a + 2)))

/-- The `log`-free remainder of the `s`-antiderivative. -/
noncomputable def formOCLGH (a X s : ℝ) : ℝ :=
  (s * formOCbr a (X * s) - formOCbr a X) *
      (2 * log X + log (1 + s - X * s) - log (1 - X) - log (1 - X * s)) +
    formOCLRp a X s + formOCellCL a X * log (1 - a * (X * s)) +
    formOCellCM a X * log (1 - X * s + a * (X * s)) + formOCellC2 a X * log (1 + s - X * s) -
    formOCellCX a X / 2 * log (1 - X * s)

/-- **The `s`-antiderivative of `formOCLg`** (by parts). -/
noncomputable def formOCLG (a X s : ℝ) : ℝ :=
  (s * formOCbr a (X * s) - formOCbr a X) * log (1 - s) + formOCLGH a X s

/-- `(s β(X s) - β(X))/(s - 1)`. -/
noncomputable def formOCLh (a X s : ℝ) : ℝ :=
  -X ^ 4 * (s ^ 4 * (X ^ 2 * a ^ 2 - X ^ 2 * a + X - 1) +
      s ^ 3 * (X ^ 2 * a ^ 2 - X ^ 2 * a + X - 1) +
      s ^ 2 * (X ^ 2 * a ^ 2 - X ^ 2 * a + X - 1) + s * (X - 1) - 1) /
    (4 * (X * a - 1) * (X * a - X + 1) * (1 - a * (X * s)) * (1 - X * s + a * (X * s)))

/-- `((1 - X) β(X) - s β(X s) - c₂ (1 - X))/(1 + s - X s)`. -/
noncomputable def formOCLk (a X s : ℝ) : ℝ :=
  -X ^ 4 * (s ^ 4 * (X ^ 4 * a ^ 2 - X ^ 4 * a - 2 * X ^ 3 * a ^ 2 + 2 * X ^ 3 * a + X ^ 3 +
      X ^ 2 * a ^ 2 - X ^ 2 * a - 3 * X ^ 2 + 3 * X - 1) +
      s ^ 3 * (X ^ 3 * a ^ 2 - X ^ 3 * a - X ^ 2 * a ^ 2 + X ^ 2 * a + X ^ 2 - 2 * X + 1) +
      s ^ 2 * (X ^ 2 * a ^ 2 - X ^ 2 * a + X - 1) + s - 1) /
    (4 * (X - 1) ^ 3 * (X * a - 1) * (X * a - X + 1) * (1 - a * (X * s)) *
      (1 - X * s + a * (X * s)))

section

variable {a X s : ℝ}

/-- The nonvanishing atoms. -/
structure FormOCLNe (a X s : ℝ) : Prop where
  a0 : a ≠ 0
  a1 : a - 1 ≠ 0
  a2 : 2 * a - 1 ≠ 0
  X1 : X - 1 ≠ 0
  Xa : X * a - 1 ≠ 0
  Xb : X * a - X + 1 ≠ 0
  T : 1 - s ≠ 0
  P : 1 + s - X * s ≠ 0
  Z : 1 - X * s ≠ 0
  L : 1 - a * (X * s) ≠ 0
  M : 1 - X * s + a * (X * s) ≠ 0

theorem formOCL_S1 (h : FormOCLNe a X s) :
    s * formOCbr a (X * s) - formOCbr a X = (s - 1) * formOCLh a X s := by
  have hP1 : 1 - a * X ≠ 0 := fun e => h.Xa (by linarith)
  have hP2 : 1 - X + a * X ≠ 0 := fun e => h.Xb (by linarith)
  have := h.L
  have := h.M
  have := h.Xa
  have := h.Xb
  unfold formOCbr formOCLh
  generalize eL : 1 - a * (X * s) = L at *
  generalize eM : 1 - X * s + a * (X * s) = M at *
  generalize eP : X * a - 1 = p at *
  generalize eQ : X * a - X + 1 = q at *
  generalize eA : 1 - a * X = A at *
  generalize eB : 1 - X + a * X = B at *
  field_simp
  subst eL eM eP eQ eA eB
  ring

theorem formOCL_S2 (h : FormOCLNe a X s) :
    (1 - X) * formOCbr a X - s * formOCbr a (X * s) =
      (1 + s - X * s) * formOCLk a X s + formOCellC2 a X * (1 - X) := by
  have hP1 : 1 - a * X ≠ 0 := fun e => h.Xa (by linarith)
  have hP2 : 1 - X + a * X ≠ 0 := fun e => h.Xb (by linarith)
  have := h.L
  have := h.M
  have := h.Xa
  have := h.Xb
  have := h.X1
  unfold formOCbr formOCLk formOCellC2
  generalize eL : 1 - a * (X * s) = L at *
  generalize eM : 1 - X * s + a * (X * s) = M at *
  generalize eP : X * a - 1 = p at *
  generalize eQ : X * a - X + 1 = q at *
  generalize eA : 1 - a * X = A at *
  generalize eB : 1 - X + a * X = B at *
  field_simp
  subst eL eM eP eQ eA eB
  ring

theorem formOCL_S3 (h : FormOCLNe a X s) :
    formOCbr a (X * s) * (2 - X) / (1 - X) + formOCLk a X s - formOCLh a X s =
      -X ^ 2 * (X - 2) / (8 * a ^ 2 * (X - 1) ^ 3 * (a - 1) ^ 2) *
        (2 * (X ^ 2 * a ^ 2 - X ^ 2 * a - X * a ^ 2 + X * a) * s +
          (2 * X ^ 2 * a ^ 2 - 2 * X ^ 2 * a - 2 * X * a ^ 2 + 2 * X * a - 2 * X + 2 * a ^ 2 -
            2 * a + 2)) +
      formOCellCL a X * (-(a * X)) / (1 - a * (X * s)) +
      formOCellCM a X * ((a - 1) * X) / (1 - X * s + a * (X * s)) := by
  have h1X : 1 - X ≠ 0 := fun e => h.X1 (by linarith)
  have := h.L
  have := h.M
  have := h.Xa
  have := h.Xb
  have := h.X1
  have := h.a0
  have := h.a1
  have := h.a2
  unfold formOCbr formOCLk formOCLh formOCellCL formOCellCM
  generalize eL : 1 - a * (X * s) = L at *
  generalize eM : 1 - X * s + a * (X * s) = M at *
  generalize eP : X * a - 1 = p at *
  generalize eQ : X * a - X + 1 = q at *
  field_simp
  subst eL eM eP eQ
  ring

theorem formOCellCX_eq (h : FormOCLNe a X s) : formOCellCX a X = 2 * formOCbr a X := by
  have := h.Xa
  have := h.Xb
  unfold formOCellCX formOCbr
  generalize eP : X * a - 1 = p at *
  generalize eQ : X * a - X + 1 = q at *
  generalize eA : 1 - a * X = A at *
  generalize eB : 1 - X + a * X = B at *
  have hA : A = -p := by subst eA eP; ring
  have hB : B = q := by subst eB eQ; ring
  subst hA hB
  field_simp
  ring

theorem formOCLG_group (h : FormOCLNe a X s) (u w : ℝ) :
    u * formOCLI X s - (s * u - w) * (-1 / (1 - s) + (1 - X) / (1 + s - X * s) + X / (1 - X * s)) =
      u * (2 - X) / (1 - X) + ((1 - X) * w - s * u) / (1 + s - X * s) + X * w / (1 - X * s) +
        (s * u - w) / (1 - s) := by
  have h1X : 1 - X ≠ 0 := fun e => h.X1 (by linarith)
  have := h.T
  have := h.P
  have := h.Z
  unfold formOCLI
  generalize eP : 1 + s - X * s = P at *
  generalize eZ : 1 - X * s = Z at *
  generalize eT : 1 - s = T at *
  generalize eU : 1 - X = U at *
  field_simp
  subst eP eZ eT eU
  ring

/-- **The derivative identity** behind the `s`-antiderivative. -/
theorem formOCLG_alg (h : FormOCLNe a X s) :
    (s * formOCbr a (X * s) - formOCbr a X) *
        (-1 / (1 - s) + (1 - X) / (1 + s - X * s) + X / (1 - X * s)) +
      -X ^ 2 * (X - 2) / (8 * a ^ 2 * (X - 1) ^ 3 * (a - 1) ^ 2) *
        (2 * (X ^ 2 * a ^ 2 - X ^ 2 * a - X * a ^ 2 + X * a) * s +
          (2 * X ^ 2 * a ^ 2 - 2 * X ^ 2 * a - 2 * X * a ^ 2 + 2 * X * a - 2 * X + 2 * a ^ 2 -
            2 * a + 2)) +
      formOCellCL a X * (-(a * X)) / (1 - a * (X * s)) +
      formOCellCM a X * ((a - 1) * X) / (1 - X * s + a * (X * s)) +
      formOCellC2 a X * (1 - X) / (1 + s - X * s) - formOCellCX a X / 2 * (-X) / (1 - X * s) =
    formOCbr a (X * s) * formOCLI X s := by
  have g1 := formOCLG_group h (formOCbr a (X * s)) (formOCbr a X)
  have e1 : (s * formOCbr a (X * s) - formOCbr a X) / (1 - s) = -formOCLh a X s := by
    rw [formOCL_S1 h]
    have := h.T
    rw [show s - 1 = -(1 - s) by ring, neg_mul, neg_div, mul_div_cancel_left₀ _ this]
  have e2 : ((1 - X) * formOCbr a X - s * formOCbr a (X * s)) / (1 + s - X * s) =
      formOCLk a X s + formOCellC2 a X * (1 - X) / (1 + s - X * s) := by
    rw [formOCL_S2 h, add_div, mul_div_cancel_left₀ _ h.P]
  have e3 : X * formOCbr a X / (1 - X * s) = -(formOCellCX a X / 2 * (-X) / (1 - X * s)) := by
    rw [formOCellCX_eq h]
    ring
  have e4 := formOCL_S3 h
  linear_combination -g1 - e1 - e2 - e3 - e4

theorem formOCLNe_of (ha : a ∈ Ioo (0 : ℝ) 1) (ha2 : a ≠ 1 / 2) (hX : X ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) : FormOCLNe a X s := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hX0, hX1⟩ := hX
  obtain ⟨hs0, hs1⟩ := hs
  have hXs : X * s < X := mul_lt_of_lt_one_right hX0 hs1
  have hXs0 : 0 < X * s := mul_pos hX0 hs0
  have haX : a * X < X := mul_lt_of_lt_one_left hX0 ha1
  have haXs : a * (X * s) < X * s := mul_lt_of_lt_one_left hXs0 ha1
  have haXs0 : 0 < a * (X * s) := mul_pos ha0 hXs0
  refine ⟨ha0.ne', by linarith, fun e => ha2 (by linarith), by linarith, by nlinarith,
    by nlinarith, by linarith, by nlinarith, by linarith, by linarith, by linarith⟩

theorem formOCLG_eq (a X s : ℝ) :
    formOCLG a X s = (s * formOCbr a (X * s) - formOCbr a X) * formOCLam X s +
      formOCLRp a X s + formOCellCL a X * log (1 - a * (X * s)) +
      formOCellCM a X * log (1 - X * s + a * (X * s)) + formOCellC2 a X * log (1 + s - X * s) -
      formOCellCX a X / 2 * log (1 - X * s) := by
  unfold formOCLG formOCLGH formOCLam
  ring

/-- **`formOCLG` is an antiderivative of `formOCLg`** on `(0, 1)`. -/
theorem hasDerivAt_formOCLG (ha : a ∈ Ioo (0 : ℝ) 1) (ha2 : a ≠ 1 / 2) (hX : X ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) : HasDerivAt (formOCLG a X) (formOCLg a X s) s := by
  have h := formOCLNe_of ha ha2 hX hs
  have hXs : HasDerivAt (fun s => X * s) X s := by
    simpa using (hasDerivAt_id' s).const_mul X
  have hP0 : (1 - a * (X * s)) * (1 - X * s + a * (X * s)) ≠ 0 := mul_ne_zero h.L h.M
  have hφ : HasDerivAt (fun s => s * formOCbr a (X * s) - formOCbr a X)
      ((X * s) ^ 4 * formOCbrE a (X * s)) s := by
    have hc : HasDerivAt (fun s => formOCbr a (X * s)) (formOCbrD a (X * s) * X) s :=
      HasDerivAt.comp (h₂ := formOCbr a) (h := fun s => X * s) s (hasDerivAt_formOCbr hP0) hXs
    have := ((hasDerivAt_id' s).mul hc).sub_const (formOCbr a X)
    convert this using 1
    rw [← formOCbr_add_mul_brD hP0]
    ring
  have hT : HasDerivAt (fun s => 1 - s) (-1) s := by simpa using (hasDerivAt_id' s).const_sub 1
  have hPd : HasDerivAt (fun s => 1 + s - X * s) (1 - X) s := by
    exact ((hasDerivAt_id' s).const_add 1).sub hXs
  have hZd : HasDerivAt (fun s => 1 - X * s) (-X) s := by simpa using hXs.const_sub 1
  have hLd : HasDerivAt (fun s => 1 - a * (X * s)) (-(a * X)) s := by
    simpa using (hXs.const_mul a).const_sub 1
  have hMd : HasDerivAt (fun s => 1 - X * s + a * (X * s)) ((a - 1) * X) s := by
    have := (hXs.const_sub 1).add (hXs.const_mul a)
    convert this using 1
    ring
  have hΛ : HasDerivAt (fun s => formOCLam X s)
      (-1 / (1 - s) + (1 - X) / (1 + s - X * s) + X / (1 - X * s)) s := by
    have := ((((hT.log h.T).const_add (2 * log X)).add (hPd.log h.P)).sub_const
      (log (1 - X))).sub (hZd.log h.Z)
    convert this using 1
    · funext s
      simp only [formOCLam, Pi.add_apply, Pi.sub_apply]
    · ring
  have hR : HasDerivAt (fun s => formOCLRp a X s)
      (-X ^ 2 * (X - 2) / (8 * a ^ 2 * (X - 1) ^ 3 * (a - 1) ^ 2) *
        (2 * (X ^ 2 * a ^ 2 - X ^ 2 * a - X * a ^ 2 + X * a) * s +
          (2 * X ^ 2 * a ^ 2 - 2 * X ^ 2 * a - 2 * X * a ^ 2 + 2 * X * a - 2 * X + 2 * a ^ 2 -
            2 * a + 2))) s := by
    have := ((hasDerivAt_id' s).mul (((hasDerivAt_id' s).const_mul
      (X ^ 2 * a ^ 2 - X ^ 2 * a - X * a ^ 2 + X * a)).add_const
      (2 * X ^ 2 * a ^ 2 - 2 * X ^ 2 * a - 2 * X * a ^ 2 + 2 * X * a - 2 * X + 2 * a ^ 2 -
        2 * a + 2))).const_mul (-X ^ 2 * (X - 2) / (8 * a ^ 2 * (X - 1) ^ 3 * (a - 1) ^ 2))
    unfold formOCLRp
    convert this using 1
    ring
  have := (((((hφ.mul hΛ).add hR).add ((hLd.log h.L).const_mul (formOCellCL a X))).add
    ((hMd.log h.M).const_mul (formOCellCM a X))).add
    ((hPd.log h.P).const_mul (formOCellC2 a X))).sub
    ((hZd.log h.Z).const_mul (formOCellCX a X / 2))
  have e : formOCLG a X = fun s => (s * formOCbr a (X * s) - formOCbr a X) * formOCLam X s +
      formOCLRp a X s + formOCellCL a X * log (1 - a * (X * s)) +
      formOCellCM a X * log (1 - X * s + a * (X * s)) + formOCellC2 a X * log (1 + s - X * s) -
      formOCellCX a X / 2 * log (1 - X * s) := funext (formOCLG_eq a X)
  rw [e]
  convert this using 1
  unfold formOCLg
  linear_combination -formOCLG_alg h

/-- The value of the antiderivative at `s = 0`. -/
theorem formOCLG_zero (a X : ℝ) :
    formOCLG a X 0 = -formOCbr a X * (2 * log X - log (1 - X)) := by
  simp [formOCLG, formOCLGH, formOCLRp]

theorem formOCLGH_one (a X : ℝ) :
    formOCLGH a X 1 = formOCLRp a X 1 + formOCellCL a X * log (1 - a * X) +
      formOCellCM a X * log (1 - X + a * X) + formOCellC2 a X * log (2 - X) -
      formOCellCX a X / 2 * log (1 - X) := by
  simp only [formOCLGH, mul_one, one_mul, sub_self, zero_mul, zero_add]
  rw [show (1 : ℝ) + 1 - X = 2 - X by ring]

theorem formOCLG_tendsto_zero (a X : ℝ) :
    Tendsto (formOCLG a X) (𝓝[>] 0) (𝓝 (formOCLG a X 0)) := by
  refine (ContinuousAt.tendsto ?_).mono_left nhdsWithin_le_nhds
  have h1 : (1 : ℝ) - 0 ≠ 0 := by norm_num
  have h2 : (1 : ℝ) + 0 - X * 0 ≠ 0 := by norm_num
  have h3 : (1 : ℝ) - X * 0 ≠ 0 := by norm_num
  have h4 : (1 : ℝ) - a * (X * 0) ≠ 0 := by norm_num
  have h5 : (1 : ℝ) - X * 0 + a * (X * 0) ≠ 0 := by norm_num
  have h6 : 4 * (((1 : ℝ) - a * (X * 0)) * (1 - X * 0 + a * (X * 0))) ≠ 0 := by norm_num
  unfold formOCLG formOCLGH formOCLRp formOCbr
  fun_prop (disch := assumption)

/-- `(1 - s) log(1 - s) → 0` kills the `log(1 - s)` term at `s = 1⁻`. -/
theorem formOCLG_tendsto_one (ha : a ∈ Ioo (0 : ℝ) 1) (ha2 : a ≠ 1 / 2) (hX : X ∈ Ioo (0 : ℝ) 1) :
    Tendsto (formOCLG a X) (𝓝[<] 1) (𝓝 (formOCLGH a X 1)) := by
  have hL : 0 < 1 - a * X := by nlinarith [ha.1, ha.2, hX.1, hX.2]
  have hM : 0 < 1 - X + a * X := by nlinarith [ha.1, ha.2, hX.1, hX.2]
  have hGH : ContinuousAt (formOCLGH a X) 1 := by
    have h1 : (1 : ℝ) + 1 - X * 1 ≠ 0 := by linarith [hX.2]
    have h2 : (1 : ℝ) - X * 1 ≠ 0 := by linarith [hX.2]
    have h3 : (1 : ℝ) - a * (X * 1) ≠ 0 := by rw [mul_one]; exact hL.ne'
    have h4 : (1 : ℝ) - X * 1 + a * (X * 1) ≠ 0 := by rw [mul_one]; exact hM.ne'
    have h5 : 4 * (((1 : ℝ) - a * (X * 1)) * (1 - X * 1 + a * (X * 1))) ≠ 0 := by
      rw [mul_one]; positivity
    have h6 : 4 * (((1 : ℝ) - a * X) * (1 - X + a * X)) ≠ 0 := by positivity
    have h7 : X ≠ 0 := hX.1.ne'
    have h8 : 1 - X ≠ 0 := by linarith [hX.2]
    unfold formOCLGH formOCLRp formOCbr
    fun_prop (disch := assumption)
  have hh : ContinuousAt (formOCLh a X) 1 := by
    have h := formOCLNe_of ha ha2 hX ⟨one_half_pos, one_half_lt_one⟩
    have h3 : (1 : ℝ) - a * (X * 1) ≠ 0 := by rw [mul_one]; exact hL.ne'
    have h4 : (1 : ℝ) - X * 1 + a * (X * 1) ≠ 0 := by rw [mul_one]; exact hM.ne'
    have h5 : 4 * (X * a - 1) * (X * a - X + 1) * (1 - a * (X * 1)) *
        (1 - X * 1 + a * (X * 1)) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero four_ne_zero h.Xa) h.Xb) h3) h4
    unfold formOCLh
    fun_prop (disch := assumption)
  have hx : Tendsto (fun s : ℝ => formOCxlog (1 - s)) (𝓝 1) (𝓝 0) := by
    have hc : Continuous fun s : ℝ => formOCxlog (1 - s) :=
      Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
    have := hc.tendsto 1
    simpa [formOCxlog] using this
  have hlim : Tendsto (fun s => -formOCLh a X s * formOCxlog (1 - s) + formOCLGH a X s)
      (𝓝[<] 1) (𝓝 (formOCLGH a X 1)) := by
    have := ((hh.tendsto.neg.mul hx).add hGH.tendsto).mono_left
      (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
  have h := formOCLNe_of ha ha2 hX hs
  rw [formOCLG, formOCL_S1 h, formOCxlog]
  ring

/-- **`ℓ_a` in closed form** (`a ≠ 1/2`). -/
theorem formOCell_eq (ha : a ∈ Ioo (0 : ℝ) 1) (ha2 : a ≠ 1 / 2) (hX : X ∈ Ioo (0 : ℝ) 1) :
    formOCell a X = formOCellC a X := by
  have hi := (hasDerivAt_formOCLs ⟨ha.1.le, ha.2.le⟩ hX).1
  have hii : IntervalIntegrable (formOCLg a X) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hi
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun s hs => hasDerivAt_formOCLG ha ha2 hX hs) hii (formOCLG_tendsto_zero a X)
    (formOCLG_tendsto_one ha ha2 hX)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hF
  have h := formOCLNe_of ha ha2 hX ⟨one_half_pos, one_half_lt_one⟩
  unfold formOCell
  rw [hF, formOCLGH_one, formOCLG_zero, formOCellC, formOCellCX_eq h]
  unfold formOCLRp formOCellCR
  ring

end

end QED.ChainProof.SetCK

end
