/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ThreeLoopSector7
public import QED.DimReg.ThreeLoopLineRel

/-!
# The three-loop integrals with `ν₇, ν₈ ≤ 0` through the face `x₇ = x₈ = 0`

At a label `n` with `n₇ = -k₇ ≤ 0`, `n₈ = -k₈ ≤ 0` the factors `1/Γ(ν₇) 1/Γ(ν₈)` of the
normalization turn the integrals over `x₇`, `x₈` into derivatives at `0` (the face theorem):
`(1/Γ(s)) ∫₀^∞ x^{s-1} g → (-1)^k g^{(k)}(0)` as `s → -k`. With `K = k₇ + k₈`,
`∂₇^{k₇} ∂₈^{k₈} G^{-d/2} = Σⱼ (-d/2)↓ⱼ G^{-d/2-j} Aⱼ`, where `A^{(0)}_0 = 1` and one derivative
in `x_b` maps `Aⱼ ↦ ∂_b Aⱼ + A_{j-1} ∂_b G` (`derivStep`, `aPolys`). Restricted to the face, each
monomial `c x^β` of `Aⱼ` gives a Lee–Pomeransky integral of `G₇` at the label `n' + β` in
dimension `d + 2j`; the ratio of the normalizations is
`(-1)^j (z)_{4j-|β|-K} ∏_b (n_b)_{β_b}` (rising factorials, `z = 2d - |n'| + K`).

* `Iline3`: this combination of the continued integrals `QED.DimReg.ThreeLoop.F7.Iline` along
  the lines of `F7`; `val3`: the same combination of the values `F7.val`;
* `tendsto_Iline3`: at every label (in particular every label with `n₇, n₈ ≤ 0`) and every
  `d₀ ∉ ℚ`, `Iline3 → val3` as `λ → 0`.

That `Iline3` is the continuation of the nine-variable integral is the face theorem, not
proved here.
-/

@[expose] public section

open Complex Filter Topology QED.DimReg QED.DimReg.Sector QED.DimReg.LineCont
open QED.DimReg.TwoLoopSESector (poch Irr analyticAt_poch)

namespace QED.DimReg.ThreeLoop

/-! ### The derivative polynomials -/

/-- One derivative in `x_b`: `Aⱼ ↦ ∂_b Aⱼ + A_{j-1} ∂_b G`. -/
def derivStep (b : ℕ) (A : List ZPoly) : List ZPoly :=
  (List.range (A.length + 1)).map fun j =>
    ZPoly.diff b (A.getD j []) ++
      if j = 0 then [] else ZPoly.mul (A.getD (j - 1) []) (ZPoly.diff b (ZPoly.ofN lpPoly))

/-- The polynomials `Aⱼ` of `∂₇^{k₇} ∂₈^{k₈} G^{-d/2} = Σⱼ (-d/2)↓ⱼ G^{-d/2-j} Aⱼ`. -/
def aPolys (k₇ k₈ : ℕ) : List ZPoly :=
  (derivStep 8)^[k₈] ((derivStep 7)^[k₇] [[([], 1)]])

/-- The terms of a polynomial in nine variables with `x₇`- and `x₈`-exponent `0`, in the first
seven variables. -/
def faceZ (P : ZPoly) : ZPoly :=
  (P.filter fun t => t.1.getD 7 0 == 0 && t.1.getD 8 0 == 0).map fun t => (t.1.take 7, t.2)

/-- The orders `k₇ = -n₇`, `k₈ = -n₈`. -/
def ord7 (n : Fin 9 → ℤ) : ℕ := (-n 7).toNat

/-- The order `k₈ = -n₈`. -/
def ord8 (n : Fin 9 → ℤ) : ℕ := (-n 8).toNat

/-- The terms `(j, (β, c))` of the face restrictions of the `Aⱼ`. -/
def terms3 (n : Fin 9 → ℤ) : List (ℕ × (List ℕ × ℤ)) :=
  (List.range (ord7 n + ord8 n + 1)).flatMap fun j =>
    (faceZ ((aPolys (ord7 n) (ord8 n)).getD j [])).map fun t => (j, t)

/-- The seven-variable label `n' + β`. -/
def lbl3 (n : Fin 9 → ℤ) (β : List ℕ) : Fin 7 → ℤ := fun b =>
  n (Fin.castLE (by omega) b) + β.getD b 0

/-- The coefficient of the term `(j, (β, c))` along the line, `λ ↦ (n' + λw₇, d₀ + 6λ)`. -/
noncomputable def coef3 (n : Fin 9 → ℤ) (d₀ : ℂ) (j : ℕ) (β : List ℕ) (c : ℤ) (l : ℂ) : ℂ :=
  (-1) ^ (ord7 n + ord8 n + j) * c *
    poch (2 * lineD h7 d₀ l - ∑ b : Fin 7, lineNu w7 (lbl3 n []) l b + (ord7 n + ord8 n))
      (4 * j - β.sum - (ord7 n + ord8 n)) *
    ∏ b : Fin 7, poch (lineNu w7 (lbl3 n []) l b) (β.getD b 0)

/-- **The combination of continued integrals of `G₇`** along the line through `n`. -/
noncomputable def Iline3 (n : Fin 9 → ℤ) (d₀ : ℂ) (l : ℂ) : ℂ :=
  ((terms3 n).map fun t =>
    coef3 n d₀ t.1 t.2.1 t.2.2 l * F7.Iline (lbl3 n t.2.1) (d₀ + 2 * t.1) l).sum

/-- **The three-loop integral at a label with `n₇, n₈ ≤ 0`**, by the derivative formula. -/
noncomputable def val3 (n : Fin 9 → ℤ) (d₀ : ℂ) : ℂ :=
  ((terms3 n).map fun t =>
    coef3 n d₀ t.1 t.2.1 t.2.2 0 * F7.val (lbl3 n t.2.1) (d₀ + 2 * t.1)).sum

theorem irr_add_two_mul {d : ℂ} (hd : Irr d) : ∀ j : ℕ, Irr (d + 2 * j)
  | 0 => by simpa using hd
  | j + 1 => by
    have := (irr_add_two_mul hd j).add_two
    push_cast
    rwa [show d + 2 * ((j : ℂ) + 1) = d + 2 * j + 2 by ring]

theorem continuous_coef3 (n : Fin 9 → ℤ) (d₀ : ℂ) (j : ℕ) (β : List ℕ) (c : ℤ) :
    Continuous (coef3 n d₀ j β c) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hz : AnalyticAt ℂ (fun l => 2 * lineD h7 d₀ l - ∑ b : Fin 7, lineNu w7 (lbl3 n []) l b +
      (ord7 n + ord8 n : ℂ)) z := by
    unfold lineD lineNu; fun_prop
  have hp : AnalyticAt ℂ (fun l => ∏ b : Fin 7, poch (lineNu w7 (lbl3 n []) l b) (β.getD b 0))
      z :=
    Finset.analyticAt_fun_prod _ fun b _ => analyticAt_poch (by unfold lineNu; fun_prop) _
  unfold coef3
  exact ((analyticAt_const.mul (analyticAt_poch hz _)).mul hp).continuousAt

/-- **The limit at every label**: `Iline3 n d₀ λ → val3 n d₀` as `λ → 0`, for `d₀ ∉ ℚ`. -/
theorem tendsto_Iline3 (n : Fin 9 → ℤ) {d₀ : ℂ} (hd : Irr d₀) :
    Tendsto (Iline3 n d₀) (𝓝[≠] 0) (𝓝 (val3 n d₀)) := by
  refine TwoLoopSESector.tendsto_list_sum (terms3 n) fun t _ => ?_
  exact ((continuous_coef3 n d₀ t.1 t.2.1 t.2.2).tendsto 0 |>.mono_left
    nhdsWithin_le_nhds).mul (F7.tendsto_Iline (lbl3 n t.2.1) (irr_add_two_mul hd t.1))

end QED.DimReg.ThreeLoop
