/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.SelfEnergyExistsUnique
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The electron on-shell conditions for the one-loop self-energy

Facts about the one-loop self-energy that fix the fermion counterterms `δ₂` and `δ_m`
((62.36)–(62.38); decisions D-23, D-25). They are stated for the loop coefficients
`QED.WickModel.selfEnergyLoopA` and `QED.WickModel.selfEnergyLoopB`, so that they apply to any
pair of form factors with the limit property of (Z₁) `QED.WickModel.selfEnergy_existsUnique`.

Write `A = selfEnergyLoopA P`, `B = selfEnergyLoopB P` (real-valued functions of `s = p²`) and
`Σ(z) = (A(-z²) - δ₂) z + (B(-z²) - δ_m) m`. The conditions `Σ(-m) = 0` and `Σ'(-m) = 0` read
`δ₂ - δ_m = A(-m²) - B(-m²)` and `δ₂ = A(-m²) - 2m² A'(-m²) + 2m² B'(-m²)`, so
`δ₂ = A(-m²) - 2m² A'(-m²) + 2m² B'(-m²)` and `δ_m = B(-m²) - 2m² A'(-m²) + 2m² B'(-m²)`.

## Main definitions

* `QED.WickModel.onShellδ₂`, `QED.WickModel.onShellδm`: the two counterterms above.

## Main statements

* `QED.WickModel.eq_selfEnergyLoop_of_tendsto`: any pair `(A, B)` with the limit property of
  (Z₁) is `(A_loop - δ₂, B_loop - δ_m)`.
* `QED.WickModel.selfEnergyLoop_onShell_iff`: `Σ(-m) = 0` and `Σ'(-m) = 0` hold exactly when
  `δ₂ = onShellδ₂ P` and `δ_m = onShellδm P`.
* `QED.WickModel.hasDerivAt_comp_projIcc_iff`: a clamp `Set.projIcc` does not change the
  derivative at an interior point.
-/

@[expose] public section

open Complex Filter Topology Set
open scoped ContDiff

namespace QED.WickModel

/-! ### The form factors in closed form -/

/-- **The limit of the one-loop self-energy.** For `m, m_γ, Λ > 0` and
`p² > -(m + min(m_γ, Λ))²`, `Σ_ε(p) = (1/i) [i Σ_ε(p)]` tends as `ε → 0⁺` to
`(A_loop(p²) - δ₂) p̸ + (B_loop(p²) - δ_m) m`, entry by entry. -/
theorem tendsto_onePIFunction_selfEnergyLoop (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (p : Fin 4 → ℝ) (hp : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot p p)
    (α β : Fin 4) :
    Tendsto (fun ε : ℝ => (1 / I) *
        onePIFunction { P with ε := ε } 1 0 2 ![p] ![p] ![] ![α] ![β] ![])
      (𝓝[>] 0)
      (𝓝 (((selfEnergyLoopA P (Minkowski.dot p p) - P.δ₂) • Dirac.slash p
        + ((selfEnergyLoopB P (Minkowski.dot p p) - P.δm) * P.m) •
          (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)) := by
  have hmin : -(P.m + P.mγ) ^ 2 ≤ -(P.m + min P.mγ P.Λ) ^ 2 ∧
      -(P.m + P.Λ) ^ 2 ≤ -(P.m + min P.mγ P.Λ) ^ 2 := by
    have h0 : 0 ≤ P.m + min P.mγ P.Λ := by positivity
    exact ⟨neg_le_neg (pow_le_pow_left₀ h0 (by linarith [min_le_left P.mγ P.Λ]) 2),
      neg_le_neg (pow_le_pow_left₀ h0 (by linarith [min_le_right P.mγ P.Λ]) 2)⟩
  have hlim := tendsto_energyFirstIntegral_selfEnergyIntegrand hm hmγ hΛ
    (hmin.1.trans_lt hp) (hmin.2.trans_lt hp) α β
  set X : ℂ := ((P.δ₂ : ℂ) • Dirac.slash p +
    ((P.δm * P.m : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β
  have heq : (fun ε : ℝ => (1 / I) *
      onePIFunction { P with ε := ε } 1 0 2 ![p] ![p] ![] ![α] ![β] ![]) =
      fun ε : ℝ => (1 / I) * (-I * X) + (1 / I) *
        QED.OneLoop.energyFirstIntegral fun ℓ => selfEnergyIntegrand P ε p ℓ α β := by
    funext ε
    rw [onePIFunction_selfEnergy, mul_add]
    rfl
  rw [heq]
  convert (hlim.const_mul (1 / I)).const_add ((1 / I) * (-I * X)) using 2
  simp only [X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  push_cast
  ring

/-- **The self-energy form factors in closed form.** For `m, m_γ, Λ > 0`, a pair `(A, B)` of
functions on `s > -(m + min(m_γ, Λ))²` with the limit property of (Z₁)
`QED.WickModel.selfEnergy_existsUnique` is `(A_loop - δ₂, B_loop - δ_m)`, with
`A_loop = selfEnergyLoopA P` and `B_loop = selfEnergyLoopB P`. -/
theorem eq_selfEnergyLoop_of_tendsto (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {AB : {s : ℝ // -(P.m + min P.mγ P.Λ) ^ 2 < s} → ℂ × ℂ}
    (hAB : ∀ (p : Fin 4 → ℝ) (hp : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot p p)
      (α β : Fin 4),
      Tendsto (fun ε : ℝ => (1 / I) *
          onePIFunction { P with ε := ε } 1 0 2 ![p] ![p] ![] ![α] ![β] ![])
        (𝓝[>] 0)
        (𝓝 (((AB ⟨_, hp⟩).1 • Dirac.slash p
          + ((AB ⟨_, hp⟩).2 * P.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) :
    AB = fun s => (selfEnergyLoopA P s.1 - P.δ₂, selfEnergyLoopB P s.1 - P.δm) :=
  (selfEnergy_existsUnique_of_twoPoint P hm hmγ hΛ).2.unique hAB
    (tendsto_onePIFunction_selfEnergyLoop P hm hmγ hΛ)

/-! ### Clamping -/

/-- The clamp `Set.projIcc a b` is the identity near an interior point of `[a, b]`. -/
theorem projIcc_eventuallyEq_id {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Ioo a b) :
    (fun z => (projIcc a b hab z : ℝ)) =ᶠ[𝓝 x] id :=
  eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) fun _ hz =>
    congrArg Subtype.val (projIcc_of_mem hab (Ioo_subset_Icc_self hz))

/-- **A clamp does not change the derivative at an interior point.** If `f` agrees with `g`
near an interior point `x` of `[a, b]`, then `f ∘ projIcc a b` has derivative `f'` at `x` if
and only if `g` does. -/
theorem hasDerivAt_comp_projIcc_iff_of_eventuallyEq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : ℝ → E} {f' : E} {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Ioo a b)
    (hfg : f =ᶠ[𝓝 x] g) :
    HasDerivAt (fun z => f (projIcc a b hab z)) f' x ↔ HasDerivAt g f' x := by
  refine Filter.EventuallyEq.hasDerivAt_iff ?_
  filter_upwards [projIcc_eventuallyEq_id hab hx, hfg] with z hz hz'
  have hz₀ : (projIcc a b hab z : ℝ) = z := hz
  rw [hz₀, hz']

/-- **A clamp does not change the derivative at an interior point.** At an interior point `x`
of `[a, b]`, `f ∘ projIcc a b` has derivative `f'` if and only if `f` does. -/
theorem hasDerivAt_comp_projIcc_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Ioo a b) :
    HasDerivAt (fun z => f (projIcc a b hab z)) f' x ↔ HasDerivAt f f' x :=
  hasDerivAt_comp_projIcc_iff_of_eventuallyEq hab hx EventuallyEq.rfl

/-! ### The on-shell conditions for a general pair of coefficients -/

/-- The derivative of `Σ(z) = (A(-z²) - c₂) z + (B(-z²) - c_m) m` at `z = -m`. -/
theorem hasDerivAt_selfEnergyForm {A B : ℝ → ℂ} {A' B' : ℂ} {m : ℝ}
    (hA : HasDerivAt A A' (-m ^ 2)) (hB : HasDerivAt B B' (-m ^ 2)) (c₂ cm : ℂ) :
    HasDerivAt (fun z : ℝ => (A (-z ^ 2) - c₂) * z + (B (-z ^ 2) - cm) * m)
      (A (-m ^ 2) - c₂ - 2 * m ^ 2 * A' + 2 * m ^ 2 * B') (-m) := by
  have hsq : HasDerivAt (fun z : ℝ => -z ^ 2) (2 * m) (-m) := by
    simpa using (hasDerivAt_pow 2 (-m)).fun_neg
  have hy : -m ^ 2 = (fun z : ℝ => -z ^ 2) (-m) := by
    simp only [neg_sq]
  have hA' := hA.scomp_of_eq (-m) hsq hy
  have hB' := hB.scomp_of_eq (-m) hsq hy
  refine (((hA'.sub_const c₂).fun_mul (hasDerivAt_id' (-m)).ofReal_comp).add
    ((hB'.sub_const cm).mul_const (m : ℂ))).congr_deriv ?_
  simp only [Function.comp_apply, neg_sq, real_smul]
  push_cast
  ring

/-- **The on-shell conditions for a general pair of coefficients.** For `m ≠ 0` and `A`, `B`
differentiable at `-m²`, the function `Σ(z) = (A(-z²) - c₂) z + (B(-z²) - c_m) m` has
`Σ(-m) = 0` and `Σ'(-m) = 0` exactly when `c₂ = A(-m²) - 2m² A'(-m²) + 2m² B'(-m²)` and
`c_m = B(-m²) - 2m² A'(-m²) + 2m² B'(-m²)`. -/
theorem selfEnergyForm_onShell_iff {A B : ℝ → ℂ} {A' B' : ℂ} {m : ℝ} (hm : m ≠ 0)
    (hA : HasDerivAt A A' (-m ^ 2)) (hB : HasDerivAt B B' (-m ^ 2)) (c₂ cm : ℂ) :
    ((A (-(-m) ^ 2) - c₂) * ((-m : ℝ) : ℂ) + (B (-(-m) ^ 2) - cm) * m = 0 ∧
      HasDerivAt (fun z : ℝ => (A (-z ^ 2) - c₂) * z + (B (-z ^ 2) - cm) * m) 0 (-m)) ↔
    c₂ = A (-m ^ 2) - 2 * m ^ 2 * A' + 2 * m ^ 2 * B' ∧
      cm = B (-m ^ 2) - 2 * m ^ 2 * A' + 2 * m ^ 2 * B' := by
  have hD := hasDerivAt_selfEnergyForm hA hB c₂ cm
  have hm' : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm
  rw [neg_sq]
  constructor
  · rintro ⟨h0, h1⟩
    have hL := hD.unique h1
    refine ⟨by linear_combination -hL, mul_left_cancel₀ hm' ?_⟩
    push_cast at h0
    linear_combination -h0 - (m : ℂ) * hL
  · rintro ⟨rfl, rfl⟩
    exact ⟨by push_cast; ring, hD.congr_deriv (by ring)⟩

/-! ### The on-shell conditions for the one-loop coefficients -/

/-- `-m²` lies below both photon thresholds. -/
theorem neg_sq_mem_Ioi_inter_Ioi {m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    -m ^ 2 ∈ Ioi (-(m + mγ) ^ 2) ∩ Ioi (-(m + Λ) ^ 2) :=
  ⟨by simp only [mem_Ioi]; nlinarith, by simp only [mem_Ioi]; nlinarith⟩

/-- `selfEnergyLoopA` is real-valued. -/
theorem ofReal_re_selfEnergyLoopA (P : Params) (s : ℝ) :
    ((selfEnergyLoopA P s).re : ℂ) = selfEnergyLoopA P s := by
  simp only [selfEnergyLoopA, ofReal_re]

/-- `selfEnergyLoopB` is real-valued. -/
theorem ofReal_re_selfEnergyLoopB (P : Params) (s : ℝ) :
    ((selfEnergyLoopB P s).re : ℂ) = selfEnergyLoopB P s := by
  simp only [selfEnergyLoopB, ofReal_re]

/-- `selfEnergyLoopA` is differentiable below both thresholds. -/
theorem differentiableAt_selfEnergyLoopA {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {s : ℝ} (hs : s ∈ Ioi (-(P.m + P.mγ) ^ 2) ∩ Ioi (-(P.m + P.Λ) ^ 2)) :
    DifferentiableAt ℝ (selfEnergyLoopA P) s :=
  ((contDiffOn_selfEnergyLoopA hm hmγ hΛ).differentiableOn (by simp)).differentiableAt
    ((isOpen_Ioi.inter isOpen_Ioi).mem_nhds hs)

/-- `selfEnergyLoopB` is differentiable below both thresholds. -/
theorem differentiableAt_selfEnergyLoopB {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {s : ℝ} (hs : s ∈ Ioi (-(P.m + P.mγ) ^ 2) ∩ Ioi (-(P.m + P.Λ) ^ 2)) :
    DifferentiableAt ℝ (selfEnergyLoopB P) s :=
  ((contDiffOn_selfEnergyLoopB hm hmγ hΛ).differentiableOn (by simp)).differentiableAt
    ((isOpen_Ioi.inter isOpen_Ioi).mem_nhds hs)

/-- The derivative of a real-valued function `ℝ → ℂ` is the derivative of its real part. -/
theorem deriv_eq_ofReal_deriv_re {f : ℝ → ℂ} {s : ℝ} (hf : DifferentiableAt ℝ f s)
    (hre : ∀ t, ((f t).re : ℂ) = f t) :
    deriv f s = ((deriv (fun t => (f t).re) s : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ (fun t => (f t).re) s := by
    simpa [Function.comp_def] using reCLM.differentiableAt.comp s hf
  have h := hd.hasDerivAt.ofReal_comp
  simp only [hre] at h
  exact h.deriv

/-- The derivative of `selfEnergyLoopA` below both thresholds is real. -/
theorem deriv_selfEnergyLoopA {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {s : ℝ} (hs : s ∈ Ioi (-(P.m + P.mγ) ^ 2) ∩ Ioi (-(P.m + P.Λ) ^ 2)) :
    deriv (selfEnergyLoopA P) s = ((deriv (fun t => (selfEnergyLoopA P t).re) s : ℝ) : ℂ) :=
  deriv_eq_ofReal_deriv_re (differentiableAt_selfEnergyLoopA hm hmγ hΛ hs)
    (ofReal_re_selfEnergyLoopA P)

/-- The derivative of `selfEnergyLoopB` below both thresholds is real. -/
theorem deriv_selfEnergyLoopB {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {s : ℝ} (hs : s ∈ Ioi (-(P.m + P.mγ) ^ 2) ∩ Ioi (-(P.m + P.Λ) ^ 2)) :
    deriv (selfEnergyLoopB P) s = ((deriv (fun t => (selfEnergyLoopB P t).re) s : ℝ) : ℂ) :=
  deriv_eq_ofReal_deriv_re (differentiableAt_selfEnergyLoopB hm hmγ hΛ hs)
    (ofReal_re_selfEnergyLoopB P)

/-- The counterterm `δ₂` fixed by the electron on-shell conditions,
`δ₂ = A(-m²) - 2m² A'(-m²) + 2m² B'(-m²)`, for the real-valued coefficients
`A = selfEnergyLoopA P`, `B = selfEnergyLoopB P` and the derivative `'` in `s = p²`. -/
noncomputable def onShellδ₂ (P : Params) : ℝ :=
  (selfEnergyLoopA P (-P.m ^ 2)).re
    - 2 * P.m ^ 2 * deriv (fun s => (selfEnergyLoopA P s).re) (-P.m ^ 2)
    + 2 * P.m ^ 2 * deriv (fun s => (selfEnergyLoopB P s).re) (-P.m ^ 2)

/-- The counterterm `δ_m` fixed by the electron on-shell conditions,
`δ_m = B(-m²) - 2m² A'(-m²) + 2m² B'(-m²)`, for the real-valued coefficients
`A = selfEnergyLoopA P`, `B = selfEnergyLoopB P` and the derivative `'` in `s = p²`. -/
noncomputable def onShellδm (P : Params) : ℝ :=
  (selfEnergyLoopB P (-P.m ^ 2)).re
    - 2 * P.m ^ 2 * deriv (fun s => (selfEnergyLoopA P s).re) (-P.m ^ 2)
    + 2 * P.m ^ 2 * deriv (fun s => (selfEnergyLoopB P s).re) (-P.m ^ 2)

/-- `δ₂ = A(-m²) - 2m² A'(-m²) + 2m² B'(-m²)` in terms of the complex coefficients. -/
theorem ofReal_onShellδ₂ {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    (onShellδ₂ P : ℂ) = selfEnergyLoopA P (-P.m ^ 2)
      - 2 * P.m ^ 2 * deriv (selfEnergyLoopA P) (-P.m ^ 2)
      + 2 * P.m ^ 2 * deriv (selfEnergyLoopB P) (-P.m ^ 2) := by
  have hs := neg_sq_mem_Ioi_inter_Ioi hm hmγ hΛ
  rw [deriv_selfEnergyLoopA hm hmγ hΛ hs, deriv_selfEnergyLoopB hm hmγ hΛ hs, onShellδ₂]
  push_cast
  rw [ofReal_re_selfEnergyLoopA]

/-- `δ_m = B(-m²) - 2m² A'(-m²) + 2m² B'(-m²)` in terms of the complex coefficients. -/
theorem ofReal_onShellδm {P : Params} (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    (onShellδm P : ℂ) = selfEnergyLoopB P (-P.m ^ 2)
      - 2 * P.m ^ 2 * deriv (selfEnergyLoopA P) (-P.m ^ 2)
      + 2 * P.m ^ 2 * deriv (selfEnergyLoopB P) (-P.m ^ 2) := by
  have hs := neg_sq_mem_Ioi_inter_Ioi hm hmγ hΛ
  rw [deriv_selfEnergyLoopA hm hmγ hΛ hs, deriv_selfEnergyLoopB hm hmγ hΛ hs, onShellδm]
  push_cast
  rw [ofReal_re_selfEnergyLoopB]

/-- **The on-shell conditions fix the counterterms.** For `m, m_γ, Λ > 0` and real `δ₂`, `δ_m`,
the function `Σ(z) = (A(-z²) - δ₂) z + (B(-z²) - δ_m) m`, with `A = selfEnergyLoopA P` and
`B = selfEnergyLoopB P`, has `Σ(-m) = 0` and `Σ'(-m) = 0` exactly when `δ₂ = onShellδ₂ P` and
`δ_m = onShellδm P`. -/
theorem selfEnergyLoop_onShell_iff (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (δ₂ δm : ℝ) :
    ((selfEnergyLoopA P (-(-P.m) ^ 2) - δ₂) * ((-P.m : ℝ) : ℂ)
        + (selfEnergyLoopB P (-(-P.m) ^ 2) - δm) * P.m = 0 ∧
      HasDerivAt (fun z : ℝ => (selfEnergyLoopA P (-z ^ 2) - δ₂) * z
        + (selfEnergyLoopB P (-z ^ 2) - δm) * P.m) 0 (-P.m)) ↔
    δ₂ = onShellδ₂ P ∧ δm = onShellδm P := by
  have hs := neg_sq_mem_Ioi_inter_Ioi hm hmγ hΛ
  rw [selfEnergyForm_onShell_iff hm.ne' (differentiableAt_selfEnergyLoopA hm hmγ hΛ hs).hasDerivAt
    (differentiableAt_selfEnergyLoopB hm hmγ hΛ hs).hasDerivAt, ← ofReal_onShellδ₂ hm hmγ hΛ,
    ← ofReal_onShellδm hm hmγ hΛ, ofReal_inj, ofReal_inj]

end QED.WickModel

end
