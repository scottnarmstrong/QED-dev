/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.LszLegs

/-!
# (X₁): the electron legs from the on-shell conditions in limit form

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57). On an external electron leg of the connected function the self-energy
`Σ(r) = A(r²) r̸ + B(r²) m` contributes `S̃₀(r) Σ(r)` next to the external spinor. The one-loop
leg limits `QED.WickModel.tendsto_electronLeg_in`, `QED.WickModel.tendsto_electronLeg_out`
assume that `A` and `B` are differentiable at `-m²`. The graded on-shell condition (G₉)
`QED.Graded.IsOnShellAt` gives less: `Σ(-m) = 0` and `Σ'(-m) = 0` for the function
`Σ(z) = A(-z²) z + B(-z²) m` only. This module proves the leg limits from these two conditions
and the continuity of `A` at `-m²` alone (`m > 0`).

With `x = -√(-r²)` (so `r² = -x²` near the shell, and `x → -m`),
`m (B - A)(r²) = Σ(x) - (x + m) A(r²)` and `r² + m² = (x + m)(m - x)`, hence
`m (B - A)(r²) / (r² + m²) = Σ(x) / (x + m) / (m - x) - A(r²) / (m - x) → -A(-m²) / (2m)`
(`tendsto_coeffs`), and `S̃₀(r) Σ(r) u → A(-m²) u - A(-m²)/(2m) · 2m u = 0`.

## Main statements

* `QED.GradedProof.X1.tendsto_coeffs`: the two scalar limits.
* `QED.GradedProof.X1.tendsto_leg_in`: `S̃₀(r) Σ(r) u → 0` for `(p̸ + m) u = 0`.
* `QED.GradedProof.X1.tendsto_leg_out`: `w Σ(r') S̃₀(r') → 0` for `w (p̸' + m) = 0`.
-/

@[expose] public section

open Matrix Complex Filter Topology

namespace QED.GradedProof.X1

/-- The `4 × 4` identity matrix. -/
local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The two scalar limits of an electron leg, from `Σ(-m) = 0`, `Σ'(-m) = 0` and the continuity
of `A` at `-m²`: through off-shell momenta near an on-shell `p`, `A(r²) → A(-m²)` and
`m (B - A)(r²) / (r² + m²) → -A(-m²) / (2m)`. -/
theorem tendsto_coeffs {m : ℝ} (hm : 0 < m) {A B : ℝ → ℂ} (hA : ContinuousAt A (-m ^ 2))
    (h0 : A (-m ^ 2) * ((-m : ℝ) : ℂ) + B (-m ^ 2) * m = 0)
    (hd : HasDerivAt (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * m) 0 (-m))
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2) :
    Tendsto (fun r : Fin 4 → ℝ => A (Minkowski.dot r r))
        (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 (A (-m ^ 2))) ∧
      Tendsto (fun r : Fin 4 → ℝ => (m : ℂ) * (B (Minkowski.dot r r) - A (Minkowski.dot r r)) /
          ((Minkowski.dot r r + m ^ 2 : ℝ) : ℂ))
        (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 (-A (-m ^ 2) / (2 * m))) := by
  set S := {r : Fin 4 → ℝ | Minkowski.dot r r ≠ -m ^ 2}
  have hs : Tendsto (fun r : Fin 4 → ℝ => Minkowski.dot r r) (𝓝[S] p) (𝓝 (-m ^ 2)) :=
    (WickModel.LszLegs.tendsto_dot_self_offShell m hp).mono_right nhdsWithin_le_nhds
  have hAt : Tendsto (fun r : Fin 4 → ℝ => A (Minkowski.dot r r)) (𝓝[S] p) (𝓝 (A (-m ^ 2))) :=
    hA.tendsto.comp hs
  refine ⟨hAt, ?_⟩
  set x : (Fin 4 → ℝ) → ℝ := fun r => -Real.sqrt (-Minkowski.dot r r) with hx
  have hx0 : Tendsto x (𝓝[S] p) (𝓝 (-m)) := by
    have h := ((Real.continuous_sqrt.tendsto _).comp hs.neg).neg
    rwa [neg_neg, Real.sqrt_sq hm.le] at h
  have hneg : ∀ᶠ r in 𝓝[S] p, Minkowski.dot r r < 0 :=
    hs (Iio_mem_nhds (by nlinarith))
  have hsq : ∀ᶠ r in 𝓝[S] p, -(x r) ^ 2 = Minkowski.dot r r := by
    filter_upwards [hneg] with r hr
    rw [hx, neg_sq, Real.sq_sqrt (by linarith), neg_neg]
  have hxne : ∀ᶠ r in 𝓝[S] p, x r ≠ -m := by
    filter_upwards [hsq, self_mem_nhdsWithin] with r hr hS hxr
    exact hS (by rw [← hr, hxr, neg_sq])
  have hxw : Tendsto x (𝓝[S] p) (𝓝[≠] (-m)) := tendsto_nhdsWithin_iff.mpr ⟨hx0, hxne⟩
  set g : ℝ → ℂ := fun z => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * m with hgdef
  have hg0 : g (-m) = 0 := by
    simp only [hgdef, neg_sq]
    simpa only [ofReal_neg] using h0
  have hsl : Tendsto (fun z : ℝ => g z / ((z + m : ℝ) : ℂ)) (𝓝[≠] (-m)) (𝓝 0) := by
    refine (hasDerivAt_iff_tendsto_slope.mp hd).congr fun z => ?_
    rw [slope_def_module, hg0, sub_zero, Complex.real_smul, sub_neg_eq_add, ofReal_inv,
      div_eq_inv_mul]
  have h2m : ((2 * m : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hmx : Tendsto (fun r => ((m - x r : ℝ) : ℂ)) (𝓝[S] p) (𝓝 ((2 * m : ℝ) : ℂ)) := by
    have h := (continuous_ofReal.tendsto _).comp (hx0.const_sub m)
    rwa [sub_neg_eq_add, ← two_mul] at h
  have hlim := ((hsl.comp hxw).div hmx h2m).sub (hAt.div hmx h2m)
  rw [zero_div, zero_sub, ← neg_div, ofReal_mul, ofReal_ofNat] at hlim
  refine hlim.congr' ?_
  filter_upwards [hsq, self_mem_nhdsWithin] with r hr hS
  have hxm : 0 < m - x r := by
    have : 0 ≤ Real.sqrt (-Minkowski.dot r r) := Real.sqrt_nonneg _
    simp only [hx]
    linarith
  have hxm' : x r + m ≠ 0 := fun h =>
    hS (by rw [← hr, show x r = -m by linarith, neg_sq])
  simp only [Pi.div_apply, Function.comp_apply]
  rw [← hr]
  have c1 : ((x r : ℂ) + m) ≠ 0 := by exact_mod_cast hxm'
  have c2 : ((m : ℂ) - x r) ≠ 0 := by exact_mod_cast hxm.ne'
  push_cast
  have c3 : (-(x r : ℂ) ^ 2 + m ^ 2) ≠ 0 := by
    rw [show (-(x r : ℂ) ^ 2 + m ^ 2) = ((x r : ℂ) + m) * ((m : ℂ) - x r) by ring]
    exact mul_ne_zero c1 c2
  field_simp
  ring

/-- The limit vector vanishes: `a v + (-a/(2m)) (m v - (-(m v))) = 0`. -/
theorem limit_eq_zero {m : ℝ} (hm : 0 < m) (a : ℂ) (v : Fin 4 → ℂ) :
    a • v + (-a / (2 * m)) • ((m : ℂ) • v - -((m : ℂ) • v)) = 0 := by
  have hm' : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
  rw [show a • v + (-a / (2 * m)) • ((m : ℂ) • v - -((m : ℂ) • v)) =
      (a - a / (2 * m) * (2 * m)) • v by module, div_mul_cancel₀ _ (by simp [hm']), sub_self,
    zero_smul]

/-- **The incoming electron leg vanishes on shell, from (G₉)-type data.** For `m > 0`, `A`
continuous at `-m²`, `Σ(-m) = 0` and `Σ'(-m) = 0` for `Σ(z) = A(-z²) z + B(-z²) m`, an on-shell
`p` and `(p̸ + m) u = 0`: `S̃₀(r) Σ(r) u → 0` as `r → p` through off-shell momenta. -/
theorem tendsto_leg_in {m : ℝ} (hm : 0 < m) {A B : ℝ → ℂ} (hA : ContinuousAt A (-m ^ 2))
    (h0 : A (-m ^ 2) * ((-m : ℝ) : ℂ) + B (-m ^ 2) * m = 0)
    (hd : HasDerivAt (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * m) 0 (-m))
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2) {u : Fin 4 → ℂ}
    (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u)) :
    Tendsto (fun r => (QED.OneLoop.electronPropagator m 0 r *
        (A (Minkowski.dot r r) • Dirac.slash r + (B (Minkowski.dot r r) * m) • 𝟙)) *ᵥ u)
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 0) := by
  obtain ⟨hA0, hk⟩ := tendsto_coeffs hm hA h0 hd hp
  have hv : Tendsto (fun r => ((m : ℂ) • 𝟙 - Dirac.slash r) *ᵥ u)
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 (((m : ℂ) • 𝟙 - Dirac.slash p) *ᵥ u)) :=
    (((continuous_const.sub WickModel.LszLegs.continuous_slash).matrix_mulVec
      continuous_const).tendsto p).mono_left nhdsWithin_le_nhds
  have hlim := (hA0.smul_const u).add (hk.smul hv)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hu, limit_eq_zero hm] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with r hr
  rw [WickModel.electronPropagator_zero_mul_selfEnergyForm hr, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

/-- **The outgoing electron leg vanishes on shell, from (G₉)-type data.** Under the hypotheses of
`tendsto_leg_in` on `A`, `B`, for an on-shell `p'` and `w (p̸' + m) = 0`,
`w Σ(r') S̃₀(r') → 0` as `r' → p'` through off-shell momenta. -/
theorem tendsto_leg_out {m : ℝ} (hm : 0 < m) {A B : ℝ → ℂ} (hA : ContinuousAt A (-m ^ 2))
    (h0 : A (-m ^ 2) * ((-m : ℝ) : ℂ) + B (-m ^ 2) * m = 0)
    (hd : HasDerivAt (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * m) 0 (-m))
    {p' : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) {w : Fin 4 → ℂ}
    (hw : w ᵥ* Dirac.slash p' = -((m : ℂ) • w)) :
    Tendsto (fun r' => w ᵥ* ((A (Minkowski.dot r' r') • Dirac.slash r' +
        (B (Minkowski.dot r' r') * m) • 𝟙) * QED.OneLoop.electronPropagator m 0 r'))
      (𝓝[{r' | Minkowski.dot r' r' ≠ -m ^ 2}] p') (𝓝 0) := by
  obtain ⟨hA0, hk⟩ := tendsto_coeffs hm hA h0 hd hp'
  have hv : Tendsto (fun r' => w ᵥ* ((m : ℂ) • 𝟙 - Dirac.slash r'))
      (𝓝[{r' | Minkowski.dot r' r' ≠ -m ^ 2}] p') (𝓝 (w ᵥ* ((m : ℂ) • 𝟙 - Dirac.slash p'))) :=
    ((continuous_const.matrix_vecMul
      (continuous_const.sub WickModel.LszLegs.continuous_slash)).tendsto p').mono_left
        nhdsWithin_le_nhds
  have hlim := (hA0.smul_const w).add (hk.smul hv)
  rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, hw, limit_eq_zero hm] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with r' hr'
  rw [WickModel.selfEnergyForm_mul_electronPropagator_zero hr', Matrix.vecMul_add,
    Matrix.vecMul_smul, Matrix.vecMul_one, Matrix.vecMul_smul]

end QED.GradedProof.X1

end
