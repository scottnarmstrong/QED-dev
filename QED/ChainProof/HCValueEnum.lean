/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCValueLink
public import QED.ChainProof.EnumVertex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The counterterm combination (O3-7) on the nine set (b) classes

Helper level, Phase 5 Stage 1a. The enumeration of set (b) (O3-4,
`QED.ChainProof.Enum.vertexChain_two_eq_classes_flavors`) writes the chain vertex as `(1/i)` times
`V(BB) - V(BD₀) - V(BD₁) - V(DB₀) - V(DB₁) + V(DD₀₀) + V(DD₀₁) + V(DD₁₀) + V(DD₁₁)`, with `V` the
value (F₇) of the representative. This file takes these nine signed class vertices as the class
decomposition `X = enumClass` of `QED/ChainProof/HCClasses.lean` and attaches to each class its
photon function:

* bubble–bubble: `Π_loop(s)² s² D(s)³`;
* each of the four bubble–`δ₃` and `δ₃`–bubble classes (one `photonCt` field pairing each):
  `-(δ₃/2) Π_loop(s) s² D(s)³`;
* each of the four `δ₃`–`δ₃` classes: `(δ₃²/4) s² D(s)³`.

They sum to `(Π_loop - δ₃)² s² D³ = chainPhoton P` (`enumPhoton_sum`), which is the algebra of the
counterterm combination O3-7; the split of the `δ₃` part evenly over the field pairings is the
two-loop pattern (`-vpZero P + 2 d3Zero P`, one `δ₃` slot per class) and is part of the per-class
hypothesis, not proved here.

## Main statements

* `chainClassDecomposition_enum`: **`ChainClassDecomposition enumClass`**, from O3-4.
* `classPhotonData_enum`: the nine photon functions are integrable at every `q² ≥ 0` (each is
  bounded on `[0, ∞)`: `abs_pow_mul_photon_le`) and sum to `chainPhoton P`.
* `chainPauliAtLink_of_enum`: **`ChainPauliAtLink` from the per-class limit link
  `ClassLimitLink enumClass` (O3-5/O3-6, `ε → 0⁺`) and the per-class nested values
  `ClassNestedAtLink enumClass enumPhoton` (O3-6 at fixed `q`).**
-/

@[expose] public section

open Complex Matrix MeasureTheory Set Filter Topology
open scoped Real
open QED.WickModel (Params vacuumPolarizationLoop Contraction)

namespace QED.ChainProof.HCValue

open QED.TwoLoop.UnitVPLink QED.TwoLoop.VPUnit QED.TwoLoop.VPHalf QED.Chain.ChainB
open QED.ChainProof.Enum

/-! ### The nine signed class vertices -/

/-- `(1/i)` times the value (F₇) of a contraction `C`, at T1's flavours read off `P`, with the
external data of the chain vertex. -/
noncomputable def classV {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => (1 / I) * QED.Lepton.contractionValue₂ P (chainFlavors P) C
    (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)

/-- **The nine signed class vertices of set (b)**: `+BB`, `-BD₀`, `-BD₁`, `-DB₀`, `-DB₁`,
`+DD₀₀`, `+DD₀₁`, `+DD₁₀`, `+DD₁₁`. -/
noncomputable def enumClass :
    Fin 9 → Params → (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![classV repBB, fun P p' p μ => -classV (repBD 0) P p' p μ,
    fun P p' p μ => -classV (repBD 1) P p' p μ, fun P p' p μ => -classV (repDB 0) P p' p μ,
    fun P p' p μ => -classV (repDB 1) P p' p μ, classV (repDD 0 0), classV (repDD 0 1),
    classV (repDD 1 0), classV (repDD 1 1)]

/-- **The class decomposition of the chain vertex (O3-4)**, in the form of
`QED.ChainProof.ChainClassDecomposition`. -/
theorem chainClassDecomposition_enum : ChainClassDecomposition enumClass := by
  intro P _ ε _ p' p _ μ
  rw [vertexChain_two_eq_classes_flavors]
  ext α β
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.add_apply, Matrix.neg_apply,
    Matrix.of_apply, enumClass, classV, Matrix.cons_val_zero, Matrix.cons_val_succ,
    add_zero]
  ring

/-! ### The nine photon functions -/

/-- The power of `Π_loop` in the photon function of class `r` (number of bubbles). -/
def enumPow : Fin 9 → ℕ := ![2, 1, 1, 1, 1, 0, 0, 0, 0]

/-- The coefficient of the photon function of class `r`: `1`, `-δ₃/2` (four times), `δ₃²/4`
(four times). -/
noncomputable def enumCoeff (P : Params) : Fin 9 → ℝ :=
  ![1, -P.δ₃ / 2, -P.δ₃ / 2, -P.δ₃ / 2, -P.δ₃ / 2, P.δ₃ ^ 2 / 4, P.δ₃ ^ 2 / 4, P.δ₃ ^ 2 / 4,
    P.δ₃ ^ 2 / 4]

/-- **The photon function of class `r`**: `enumCoeff r · Π_loop(s)^(enumPow r) · s² D(s)³`. -/
noncomputable def enumPhoton (r : Fin 9) (P : Params) (s : ℝ) : ℝ :=
  enumCoeff P r * vacuumPolarizationLoop P s ^ enumPow r * s ^ 2 * photonD P.mγ P.Λ s ^ 3

/-- **The counterterm combination**: the nine photon functions sum to `(Π_loop - δ₃)² s² D³`. -/
theorem enumPhoton_sum (P : Params) (s : ℝ) : ∑ r, enumPhoton r P s = chainPhoton P s := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, enumPhoton, enumCoeff, enumPow, chainPhoton,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

/-! ### Boundedness and integrability -/

/-- `s² D(s)³ ≤ 1/m_γ²` and `s³ D(s)³ ≤ 1` for `s ≥ 0`, `0 < m_γ ≤ Λ`. -/
theorem photon_moments_le {mγ Λ s : ℝ} (hmγ : 0 < mγ) (hmΛ : mγ ≤ Λ) (hs : 0 ≤ s) :
    s ^ 2 * photonD mγ Λ s ^ 3 ≤ 1 / mγ ^ 2 ∧ s ^ 3 * photonD mγ Λ s ^ 3 ≤ 1 := by
  obtain ⟨d0, d1⟩ := photonD_bounds hmγ hmΛ hs
  have hD := photonD_nonneg hmγ hmΛ hs
  have hDle : photonD mγ Λ s ≤ 1 / mγ ^ 2 := by
    unfold photonD
    have ha : 0 < s + mγ ^ 2 := by positivity
    have h1 : 1 / (s + mγ ^ 2) ≤ 1 / mγ ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 : 0 ≤ 1 / (s + Λ ^ 2) := by positivity
    linarith
  have e2 : s ^ 2 * photonD mγ Λ s ^ 3 = (s * photonD mγ Λ s) ^ 2 * photonD mγ Λ s := by ring
  have e3 : s ^ 3 * photonD mγ Λ s ^ 3 = (s * photonD mγ Λ s) ^ 3 := by ring
  constructor
  · rw [e2]
    calc (s * photonD mγ Λ s) ^ 2 * photonD mγ Λ s ≤ 1 * photonD mγ Λ s := by
          gcongr
          nlinarith
      _ ≤ 1 / mγ ^ 2 := by linarith
  · rw [e3]
    calc (s * photonD mγ Λ s) ^ 3 ≤ 1 ^ 3 := by gcongr
      _ = 1 := one_pow 3

/-- **A bounded insertion**: if `|x| ≤ a + b s` with `a, b ≥ 0`, then for `j ≤ 2`
`|x^j s² D³| ≤ (1 + a)²/m_γ² + 2(1 + a) b + b² Λ²`. -/
theorem abs_pow_mul_photon_le {mγ Λ s x a b : ℝ} {j : ℕ} (hj : j ≤ 2) (hmγ : 0 < mγ)
    (hmΛ : mγ ≤ Λ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : |x| ≤ a + b * s) :
    |x ^ j * s ^ 2 * photonD mγ Λ s ^ 3| ≤
      (1 + a) ^ 2 / mγ ^ 2 + 2 * (1 + a) * b + b ^ 2 * Λ ^ 2 := by
  have hD := photonD_nonneg hmγ hmΛ hs
  obtain ⟨m2, m3⟩ := photon_moments_le hmγ hmΛ hs
  obtain ⟨-, m4⟩ := sq_sq_photonD_cube_le hmγ hmΛ hs
  have hT : 0 ≤ s ^ 2 * photonD mγ Λ s ^ 3 := by positivity
  have hxj : |x| ^ j ≤ (1 + a + b * s) ^ 2 := by
    have hx0 := abs_nonneg x
    have h1 : |x| ^ j ≤ (1 + |x|) ^ 2 := by
      interval_cases j <;> nlinarith
    exact h1.trans (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  rw [mul_assoc, abs_mul, abs_pow, abs_of_nonneg hT]
  calc |x| ^ j * (s ^ 2 * photonD mγ Λ s ^ 3)
      ≤ (1 + a + b * s) ^ 2 * (s ^ 2 * photonD mγ Λ s ^ 3) :=
        mul_le_mul_of_nonneg_right hxj hT
    _ = (1 + a) ^ 2 * (s ^ 2 * photonD mγ Λ s ^ 3) +
          2 * (1 + a) * b * (s ^ 3 * photonD mγ Λ s ^ 3) +
          b ^ 2 * (s ^ 4 * photonD mγ Λ s ^ 3) := by ring
    _ ≤ (1 + a) ^ 2 * (1 / mγ ^ 2) + 2 * (1 + a) * b * 1 + b ^ 2 * Λ ^ 2 := by
        gcongr
    _ = (1 + a) ^ 2 / mγ ^ 2 + 2 * (1 + a) * b + b ^ 2 * Λ ^ 2 := by ring

/-- The spectral form `Π_loop(0) + (e²/(4π²)) ∑_f c_f specJ(M_f, s)` of the loop function. -/
noncomputable def piSpec (P : Params) (s : ℝ) : ℝ :=
  vacuumPolarizationLoop P 0 + P.e ^ 2 / (4 * π ^ 2) * ∑ f, P.loopCoeff f * specJ (P.mass f) s

theorem measurable_piSpec (P : Params) : Measurable (piSpec P) := by
  unfold piSpec
  have hS : Measurable (fun s => ∑ f, P.loopCoeff f * specJ (P.mass f) s) :=
    Finset.measurable_sum _ fun f _ => (measurable_specJ _).const_mul _
  exact measurable_const.add (hS.const_mul _)

theorem vacuumPolarizationLoop_eq_piSpec {P : Params} (hmass : ∀ f, P.mass f ≠ 0) {s : ℝ}
    (hs : 0 ≤ s) : vacuumPolarizationLoop P s = piSpec P s := by
  unfold piSpec
  rw [← vacuumPolarizationLoop_sub_zero P hmass hs]
  ring

theorem abs_piSpec_le {P : Params} (hmass : ∀ f, P.mass f ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    |piSpec P s| ≤ |vacuumPolarizationLoop P 0| + |P.e ^ 2 / (4 * π ^ 2)| * specConst P * s := by
  unfold piSpec
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, mul_assoc]
  gcongr
  exact abs_sum_specJ_le hmass hs

/-- **Each class photon function gives an integrable integrand** at every `q² = Q ≥ 0`, at
admissible parameters. -/
theorem integrableAt_enumPhoton {P : Params} (hA : ChainAdmissible P) {Q : ℝ} (hQ : 0 ≤ Q)
    (r : Fin 9) : IntegrableAt P.m Q (enumPhoton r P) := by
  have hmass := mass_ne_zero_of_admissible hA
  set R' : ℝ → ℝ := fun s =>
    enumCoeff P r * piSpec P s ^ enumPow r * s ^ 2 * photonD P.mγ P.Λ s ^ 3 with hR'
  have hR'm : Measurable R' := by
    simp only [hR']
    exact (((measurable_const.mul ((measurable_piSpec P).pow_const _)).mul
      (measurable_id.pow_const 2)).mul ((measurable_photonD _ _).pow_const 3))
  have heq : ∀ t, 0 ≤ t → enumPhoton r P t = R' t := fun t ht => by
    simp only [enumPhoton, hR', vacuumPolarizationLoop_eq_piSpec hmass ht]
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => enumPhoton r P (vpK P.m Q z))
      QED.Integration.feynmanMeasure := by
    have hK : Measurable fun z : ℝ × ℝ => vpK P.m Q z := by
      unfold vpK QED.TwoLoop.VPUnitNested.kC
      fun_prop
    refine (hR'm.comp hK).aestronglyMeasurable.congr ?_
    filter_upwards [QED.OneLoop.VertexLimit.ae_feynmanMeasure_mem_Icc] with z hz
    exact (heq _ (vpK_nonneg hQ hz)).symm
  have hj : enumPow r ≤ 2 := by fin_cases r <;> decide
  refine integrableAt_of_bound hQ hmeas (C := |enumCoeff P r| *
    ((1 + |vacuumPolarizationLoop P 0|) ^ 2 / P.mγ ^ 2 +
      2 * (1 + |vacuumPolarizationLoop P 0|) * (|P.e ^ 2 / (4 * π ^ 2)| * specConst P) +
      (|P.e ^ 2 / (4 * π ^ 2)| * specConst P) ^ 2 * P.Λ ^ 2)) fun t ht => ?_
  have hc0 : 0 ≤ specConst P :=
    Finset.sum_nonneg fun f _ => div_nonneg (abs_nonneg _) (by positivity)
  have hx : |vacuumPolarizationLoop P t| ≤
      |vacuumPolarizationLoop P 0| + |P.e ^ 2 / (4 * π ^ 2)| * specConst P * t := by
    rw [vacuumPolarizationLoop_eq_piSpec hmass ht]
    exact abs_piSpec_le hmass ht
  have key := abs_pow_mul_photon_le hj hA.hmγ hA.hmγΛ.le ht (abs_nonneg _)
    (mul_nonneg (abs_nonneg _) hc0) hx
  have e : enumPhoton r P t = enumCoeff P r *
      (vacuumPolarizationLoop P t ^ enumPow r * t ^ 2 * photonD P.mγ P.Λ t ^ 3) := by
    simp only [enumPhoton]
    ring
  rw [e, abs_mul]
  exact mul_le_mul_of_nonneg_left key (abs_nonneg _)

/-- **The nine photon functions are class photon data**: integrable at every `q² > 0` and summing
to `chainPhoton P`. -/
theorem classPhotonData_enum : ClassPhotonData enumPhoton where
  integrable P hA := by
    filter_upwards [self_mem_nhdsWithin] with Q (hQ : 0 < Q)
    exact fun r => integrableAt_enumPhoton hA hQ.le r
  sum P _ s _ := enumPhoton_sum P s

/-- **`ChainPauliAtLink` from the per-class limits and the per-class nested values**, on the
nine classes of the enumeration (O3-4). The two hypotheses are the per-class `ε → 0⁺` limit link
(O3-5/O3-6) and the per-class nested value at fixed `q` (O3-6). -/
theorem chainPauliAtLink_of_enum (hL : ClassLimitLink enumClass)
    (hN : ClassNestedAtLink enumClass enumPhoton) : ChainPauliAtLink :=
  chainPauliAtLink_of_classes chainClassDecomposition_enum hL hN classPhotonData_enum

end QED.ChainProof.HCValue

end
