/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBMassLim
public import QED.ChainProof.SetAKSKSDm
public import QED.ChainProof.SetAKSKDens

/-!
# Set (a), stage B4: the mass class in closed form

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B4 (the mass
class). The reduced one-loop functionals `J_A`, `J_B` of `ksMass_fLim_eq_param` have all four
lines of one mass `M`, the `k`-lines forming one block, so in join coordinates the integrand
depends on the block weight `ρ` only: `P₀ = ρk`, `V̂ = M² + ρ(1 - ρ)s` (`s = k·k`). One
integration by parts gives, with `κ = k²k³` and `D` the one-loop mass derivative `ksDm`,
`M²(J_A + J_B) = κ (-1/3 - D(s/M²)/2)`. The constant drops out of the flavour sum:

* `ksMass_join_eval`: the four-line functional of a block of `k`-lines as a `ρ`-integral;
* `ksMass_J_A`, `ksMass_J_B`, `ksMass_redBr`: the two functionals explicitly;
* `ksMassR`, `ksMass_hasDerivAt_R`: the antiderivative of the integration by parts;
* **`ksMass_J_sum`**: `M²(J_A + J_B) = κ (-1/3 - D(s/M²)/2)`;
* **`ksMass_fLim`**: on a flavour set with `∑ c_f = 0` and `δ (rep f) = d`,
  `fLim δ (k)₂₃ = d · i e²/(4π²) · k²k³ · ∑_f c_f D(k·k/M_f²)`;
* `ksMassF`, **`ksMass_qDens_mass`**: the mass class of `qDens` at the configuration
  `decCfg μ x`: `-(i/c²) ∑_g σ(M_g, u) fLim(single g 1)(k'(s))₂₃ = σ(μ, u) · ksMassF e μ x s`,
  with the real closed form `ksMassF e μ x s = e²/(4π²) ∑_f c_f D(s/M_f²)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real
open QED.WickModel (Params)
open QED.Graded

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.TwoLoop.Bridge QED.GradedProof.VP2 QED.GradedProof.RPi4
open QED.Integration.Feynman (simplexSet simplexPoint)

/-! ### The functional of a block of `k`-lines in join coordinates -/

theorem ksMass_P0_zero {q : ℕ} (b : Fin (q + 1) → ℝ) :
    faceIdP0 (fun _ : Fin (q + 1) => (0 : Fin 4 → ℝ)) b = 0 := by
  funext μ
  simp [faceIdP0]

theorem ksMass_VR_const {q : ℕ} (M : ℝ) (b : Fin (q + 1) → ℝ) (hb : ∑ i, b i = 1) :
    faceIdVR (fun _ : Fin (q + 1) => (0 : Fin 4 → ℝ)) (fun _ => M) b = M ^ 2 := by
  simp only [faceIdVR, ksMass_P0_zero]
  simp only [Minkowski.dot_eq, Pi.zero_apply]
  rw [← Finset.sum_mul, hb]
  ring

/-- **The four-line functional of a block of `k`-lines in join coordinates.** -/
theorem ksMass_join_eval {p q : ℕ} (Q : LoopQuartic) (M : ℝ) (k : Fin 4 → ℝ)
    (hint : IntegrableOn (fun x : Fin (p + 1 + q) → ℝ => faceIdRedBr 4 Q
      (faceIdX0 (faceIdP0 (Fin.append (m := p + 1) (n := q + 1) (fun _ => k) fun _ => 0)
        (simplexPoint x)))
      (faceIdVR (Fin.append (m := p + 1) (n := q + 1) (fun _ => k) fun _ => 0)
        (Fin.append (m := p + 1) (n := q + 1) (fun _ => M) fun _ => M) (simplexPoint x)))
      (simplexSet (p + 1 + q))) :
    ∫ x in simplexSet (p + 1 + q), faceIdRedBr 4 Q
        (faceIdX0 (faceIdP0 (Fin.append (m := p + 1) (n := q + 1) (fun _ => k) fun _ => 0)
          (simplexPoint x)))
        (faceIdVR (Fin.append (m := p + 1) (n := q + 1) (fun _ => k) fun _ => 0)
          (Fin.append (m := p + 1) (n := q + 1) (fun _ => M) fun _ => M) (simplexPoint x)) =
      ∫ ρ in (0 : ℝ)..1, ((ρ ^ p * (1 - ρ) ^ q * (volume (simplexSet p)).toReal *
        (volume (simplexSet q)).toReal : ℝ) : ℂ) *
        faceIdRedBr 4 Q (faceIdX0 (ρ • k)) (M ^ 2 + ρ * (1 - ρ) * Minkowski.dot k k) := by
  rw [integral_simplex_join (p := p) (q := q) (f := fun z => faceIdRedBr 4 Q
    (faceIdX0 (faceIdP0 (Fin.append (m := p + 1) (n := q + 1) (fun _ => k) fun _ => 0) z))
    (faceIdVR (Fin.append (m := p + 1) (n := q + 1) (fun _ => k) fun _ => 0)
      (Fin.append (m := p + 1) (n := q + 1) (fun _ => M) fun _ => M) z)) hint]
  refine intervalIntegral.integral_congr fun ρ _ => ?_
  have hpt : ∀ (w : Fin p → ℝ) (v : Fin q → ℝ),
      faceIdRedBr 4 Q (faceIdX0 (faceIdP0 (Fin.append (m := p + 1) (n := q + 1) (fun _ => k)
          fun _ => 0) (Fin.append (m := p + 1) (n := q + 1) (ρ • simplexPoint w)
            ((1 - ρ) • simplexPoint v))))
        (faceIdVR (Fin.append (m := p + 1) (n := q + 1) (fun _ => k) fun _ => 0)
          (Fin.append (m := p + 1) (n := q + 1) (fun _ => M) fun _ => M)
          (Fin.append (m := p + 1) (n := q + 1) (ρ • simplexPoint w) ((1 - ρ) • simplexPoint v))) =
      faceIdRedBr 4 Q (faceIdX0 (ρ • k)) (M ^ 2 + ρ * (1 - ρ) * Minkowski.dot k k) := by
    intro w v
    have hP := faceId_blk_P0 (p := p) (q := q) k (fun _ => 0) ρ (simplexPoint w)
      (simplexPoint v) (sum_simplexPoint w)
    have hV := faceId_blk_VR (p := p) (q := q) k M (fun _ => 0) (fun _ => M) ρ (simplexPoint w)
      (simplexPoint v) (sum_simplexPoint w)
    rw [hP, hV, ksMass_P0_zero, ksMass_VR_const M _ (sum_simplexPoint v)]
    have h0 : k - (0 : Fin 4 → ℝ) = k := sub_zero k
    rw [h0]
    congr 2
    · simp
    · ring
  simp only [hpt, setIntegral_const, Measure.real, Complex.real_smul]
  push_cast
  ring

/-! ### The two functionals -/

theorem ksMass_bp_A (k : Fin 4 → ℝ) :
    (faceIdBP k ksMassBA : Fin 4 → Fin 4 → ℝ) =
      Fin.append (m := 0 + 1) (n := 2 + 1) (fun _ => k) fun _ => 0 := by
  funext i
  fin_cases i <;> rfl

theorem ksMass_bp_B (k : Fin 4 → ℝ) :
    (faceIdBP k ksMassBB : Fin 4 → Fin 4 → ℝ) =
      Fin.append (m := 1 + 1) (n := 1 + 1) (fun _ => k) fun _ => 0 := by
  funext i
  fin_cases i <;> rfl

theorem ksMass_M_A (M : ℝ) :
    (fun _ : Fin 4 => M) = Fin.append (m := 0 + 1) (n := 2 + 1) (fun _ => M) fun _ => M := by
  funext i
  fin_cases i <;> rfl

theorem ksMass_M_B (M : ℝ) :
    (fun _ : Fin 4 => M) = Fin.append (m := 1 + 1) (n := 1 + 1) (fun _ => M) fun _ => M := by
  funext i
  fin_cases i <;> rfl

section Func

variable {m₀ M : ℝ} (hm₀ : 0 < m₀) (hM : m₀ ≤ M) {k : Fin 4 → ℝ}
  (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k)
include hm₀ hM hk

theorem ksMass_int (b : Fin 4 → Bool) (Q : LoopQuartic) :
    IntegrableOn (fun x : Fin 3 → ℝ => faceIdRedBr 4 Q
      (faceIdX0 (faceIdP0 (faceIdBP k b) (simplexPoint x)))
      (faceIdVR (faceIdBP k b) (fun _ => M) (simplexPoint x))) (simplexSet 3) :=
  (faceId_continuousOn_redBr (faceIdBP k b) (fun _ => M) 4 Q fun w hw =>
    ((faceId_VR_pos hm₀ hk).trans_le (faceId_VR_ge_simplex k b (fun _ => M) hm₀
      (fun _ => hM) w hw)).ne').integrableOn_compact
    (QED.Integration.Feynman.isCompact_simplexSet _)

theorem ksMass_J_A (Q : LoopQuartic) :
    ksMassJ ksMassBA Q M k = ∫ ρ in (0 : ℝ)..1, (((1 - ρ) ^ 2 / 2 : ℝ) : ℂ) *
      faceIdRedBr 4 Q (faceIdX0 (ρ • k)) (M ^ 2 + ρ * (1 - ρ) * Minkowski.dot k k) := by
  have hint := ksMass_int hm₀ hM hk ksMassBA Q
  rw [ksMass_bp_A, ksMass_M_A] at hint
  unfold ksMassJ
  rw [ksMass_bp_A, ksMass_M_A]
  rw [ksMass_join_eval (p := 0) (q := 2) Q M k hint, faceId_volume_simplexSet_two,
    faceId_volume_simplexSet]
  refine intervalIntegral.integral_congr fun ρ _ => ?_
  simp only [Nat.factorial, pow_zero]
  push_cast
  ring

theorem ksMass_J_B (Q : LoopQuartic) :
    ksMassJ ksMassBB Q M k = ∫ ρ in (0 : ℝ)..1, ((ρ * (1 - ρ) : ℝ) : ℂ) *
      faceIdRedBr 4 Q (faceIdX0 (ρ • k)) (M ^ 2 + ρ * (1 - ρ) * Minkowski.dot k k) := by
  have hint := ksMass_int hm₀ hM hk ksMassBB Q
  rw [ksMass_bp_B, ksMass_M_B] at hint
  unfold ksMassJ
  rw [ksMass_bp_B, ksMass_M_B]
  rw [ksMass_join_eval (p := 1) (q := 1) Q M k hint, faceId_volume_simplexSet]
  refine intervalIntegral.integral_congr fun ρ _ => ?_
  simp only [Nat.factorial, pow_one]
  push_cast
  ring

end Func

/-- **The reduced bracket of the cubic numerators** at the shift `ρk`. -/
theorem ksMass_redBr (k : Fin 4 → ℝ) (a b c d e : ℂ) (ρ V : ℝ) :
    faceIdRedBr 4 (ksMassQ k a b c d e) (faceIdX0 (ρ • k)) V =
      ksMassN k a b c d e (-(ρ • k)) * ((V ^ 2 : ℝ) : ℂ)⁻¹ +
        (-(a + 6 * e) * ((ksMassL k (ρ • k) : ℝ) : ℂ) + 2 * d * ((k 2 * k 3 : ℝ) : ℂ)) / 2 *
          ((V : ℝ) : ℂ)⁻¹ := by
  simp only [faceIdRedBr, ksMassQ_evalC_X0, ksMassQ_cTwoG_X0,
    FaceBr.cFourG_of_quart (ksMassQ_quart k a b c d e),
    show (4 : ℕ) - 3 = 1 from rfl, show (4 : ℕ) - 4 = 0 from rfl, show (4 : ℕ) - 2 = 2 from rfl,
    Nat.factorial, pow_one]
  push_cast
  ring

/-! ### The integration by parts -/

/-- The one-loop `V̂ = M² + ρ(1 - ρ)s`. -/
def ksMassV (M s ρ : ℝ) : ℝ := M ^ 2 + ρ * (1 - ρ) * s

/-- The integrand of `J_A` (real form; `κ = k²k³`). -/
noncomputable def ksMassTA (M s κ ρ : ℝ) : ℝ :=
  (1 - ρ) ^ 2 / 2 * ((-4 * s * ρ ^ 2 * κ * (1 - 2 * ρ)) / ksMassV M s ρ ^ 2 +
      8 * ρ * κ / ksMassV M s ρ)

/-- The integrand of `J_B` (real form). -/
noncomputable def ksMassTB (M s κ ρ : ℝ) : ℝ :=
  ρ * (1 - ρ) * ((4 * ρ ^ 3 * s * κ - 2 * s * ρ ^ 2 * κ -
      2 * ρ * κ * (s + 2 * M ^ 2 - 2 * ρ * s + 2 * ρ ^ 2 * s)) / ksMassV M s ρ ^ 2 +
      2 * κ * (1 - 4 * ρ) / ksMassV M s ρ)

/-- The integrand of `J_A + J_B`. -/
noncomputable def ksMassT (M s κ ρ : ℝ) : ℝ := ksMassTA M s κ ρ + ksMassTB M s κ ρ

/-- The numerator of the antiderivative. -/
def ksMassRN (M s κ ρ : ℝ) : ℝ :=
  κ * ρ * (1 - ρ) * (M ^ 2 * (1 + 10 * ρ - 12 * ρ ^ 2) + s * ρ * (1 - ρ) * (1 - 2 * ρ))

/-- The derivative of `ksMassRN` in `ρ`. -/
def ksMassRN' (M s κ ρ : ℝ) : ℝ :=
  κ * (1 - 2 * ρ) * (M ^ 2 * (1 + 10 * ρ - 12 * ρ ^ 2) + s * ρ * (1 - ρ) * (1 - 2 * ρ)) +
    κ * ρ * (1 - ρ) * (M ^ 2 * (10 - 24 * ρ) + s * (1 - 6 * ρ + 6 * ρ ^ 2))

/-- **The antiderivative** `R = κρ(1 - ρ)(M²(1 + 10ρ - 12ρ²) + sρ(1 - ρ)(1 - 2ρ))/(3M²V̂)`. -/
noncomputable def ksMassR (M s κ ρ : ℝ) : ℝ := ksMassRN M s κ ρ / (3 * M ^ 2 * ksMassV M s ρ)

theorem ksMass_hasDerivAt_RN (M s κ ρ : ℝ) :
    HasDerivAt (ksMassRN M s κ) (ksMassRN' M s κ ρ) ρ := by
  have h : ksMassRN M s κ = fun ρ => κ * (M ^ 2 * (ρ + 9 * ρ ^ 2 - 22 * ρ ^ 3 + 12 * ρ ^ 4) +
      s * (ρ ^ 2 - 4 * ρ ^ 3 + 5 * ρ ^ 4 - 2 * ρ ^ 5)) := by
    funext ρ
    simp only [ksMassRN]
    ring
  rw [h]
  have := ((((((hasDerivAt_id ρ).add ((hasDerivAt_pow 2 ρ).const_mul 9)).sub
    ((hasDerivAt_pow 3 ρ).const_mul 22)).add ((hasDerivAt_pow 4 ρ).const_mul 12)).const_mul
    (M ^ 2)).add (((((hasDerivAt_pow 2 ρ).sub ((hasDerivAt_pow 3 ρ).const_mul 4)).add
    ((hasDerivAt_pow 4 ρ).const_mul 5)).sub ((hasDerivAt_pow 5 ρ).const_mul 2)).const_mul
    s)).const_mul κ
  refine this.congr_deriv ?_
  simp only [ksMassRN']
  norm_num
  ring

theorem ksMass_hasDerivAt_V (M s ρ : ℝ) :
    HasDerivAt (ksMassV M s) ((1 - 2 * ρ) * s) ρ := by
  have h : ksMassV M s = fun ρ => M ^ 2 + s * ρ - s * ρ ^ 2 := by
    funext ρ
    simp only [ksMassV]
    ring
  rw [h]
  have := (((hasDerivAt_id ρ).const_mul s).const_add (M ^ 2)).sub
    ((hasDerivAt_pow 2 ρ).const_mul s)
  refine this.congr_deriv ?_
  norm_num
  ring

theorem ksMass_hasDerivAt_R {M s κ ρ : ℝ} (hM : M ≠ 0) (hV : ksMassV M s ρ ≠ 0) :
    HasDerivAt (ksMassR M s κ) (ksMassT M s κ ρ - κ / M ^ 2 *
      (-1 / 3 + 2 * QED.ChainProof.SetAKS.ksDmKer (s / M ^ 2) ρ)) ρ := by
  have hD : 3 * M ^ 2 * ksMassV M s ρ ≠ 0 := by positivity
  have h := (ksMass_hasDerivAt_RN M s κ ρ).div
    ((ksMass_hasDerivAt_V M s ρ).const_mul (3 * M ^ 2)) hD
  convert h using 1
  · funext x
    rfl
  have hK : ksDmKer (s / M ^ 2) ρ = ρ ^ 2 * (1 - ρ) ^ 2 * s / ksMassV M s ρ := by
    have e : 1 + ρ * (1 - ρ) * (s / M ^ 2) = ksMassV M s ρ / M ^ 2 := by
      simp only [ksMassV]
      field_simp
    simp only [ksDmKer, e]
    field_simp
  rw [hK]
  simp only [ksMassT, ksMassTA, ksMassTB, ksMassRN', ksMassRN]
  field_simp
  ring_nf
  simp only [ksMassV]
  ring

/-! ### The value of `J_A + J_B` -/

theorem ksMass_V_pos {m₀ M s ρ : ℝ} (hm₀ : 0 < m₀) (hM : m₀ ≤ M) (hs : -(4 * m₀ ^ 2) < s)
    (hρ : ρ ∈ Icc (0 : ℝ) 1) : 0 < ksMassV M s ρ := by
  have hM0 : 0 < M := hm₀.trans_le hM
  have hσ : -4 < s / M ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hM hM hm₀.le hM0.le]
  have h := ksS_den_pos hσ hρ
  have e : ksMassV M s ρ = M ^ 2 * (1 + ρ * (1 - ρ) * (s / M ^ 2)) := by
    simp only [ksMassV]
    field_simp
  rw [e]
  positivity

theorem ksMass_fA (k : Fin 4 → ℝ) (M ρ : ℝ)
    (hV : ksMassV M (Minkowski.dot k k) ρ ≠ 0) :
    (((1 - ρ) ^ 2 / 2 : ℝ) : ℂ) * faceIdRedBr 4 (ksMassQA k) (faceIdX0 (ρ • k))
        (M ^ 2 + ρ * (1 - ρ) * Minkowski.dot k k) =
      ((ksMassTA M (Minkowski.dot k k) (k 2 * k 3) ρ : ℝ) : ℂ) := by
  have hV' : ((M ^ 2 + ρ * (1 - ρ) * Minkowski.dot k k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hV
  rw [ksMassQA, ksMass_redBr]
  simp only [ksMassTA, ksMassN, ksMassL, ksMassV, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    Minkowski.dot_eq] at hV' ⊢
  push_cast at hV' ⊢
  field_simp
  ring

theorem ksMass_fB (k : Fin 4 → ℝ) (M ρ : ℝ)
    (hV : ksMassV M (Minkowski.dot k k) ρ ≠ 0) :
    ((ρ * (1 - ρ) : ℝ) : ℂ) * faceIdRedBr 4 (ksMassQB k M) (faceIdX0 (ρ • k))
        (M ^ 2 + ρ * (1 - ρ) * Minkowski.dot k k) =
      ((ksMassTB M (Minkowski.dot k k) (k 2 * k 3) ρ : ℝ) : ℂ) := by
  have hV' : ((M ^ 2 + ρ * (1 - ρ) * Minkowski.dot k k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hV
  rw [ksMassQB, ksMass_redBr]
  simp only [ksMassTB, ksMassN, ksMassL, ksMassV, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    Minkowski.dot_eq] at hV' ⊢
  push_cast at hV' ⊢
  field_simp
  ring

theorem ksMass_integral_T {m₀ M s κ : ℝ} (hm₀ : 0 < m₀) (hM : m₀ ≤ M)
    (hs : -(4 * m₀ ^ 2) < s) :
    M ^ 2 * ((∫ ρ in (0 : ℝ)..1, ksMassTA M s κ ρ) + ∫ ρ in (0 : ℝ)..1, ksMassTB M s κ ρ) =
      κ * (-1 / 3 - ksDm (s / M ^ 2) / 2) := by
  have hM0 : M ≠ 0 := (hm₀.trans_le hM).ne'
  have hσ : -4 < s / M ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hM hM hm₀.le (hm₀.trans_le hM).le]
  have hVne : ∀ ρ ∈ Icc (0 : ℝ) 1, ksMassV M s ρ ≠ 0 := fun ρ hρ =>
    (ksMass_V_pos hm₀ hM hs hρ).ne'
  have hVc : Continuous (ksMassV M s) := by
    unfold ksMassV
    fun_prop
  have hV2 : ∀ ρ ∈ Icc (0 : ℝ) 1, ksMassV M s ρ ^ 2 ≠ 0 := fun ρ hρ => pow_ne_zero 2 (hVne ρ hρ)
  have hVc2 : Continuous fun ρ => ksMassV M s ρ ^ 2 := hVc.pow 2
  have cA : ContinuousOn (ksMassTA M s κ) (Icc 0 1) := by
    unfold ksMassTA
    exact (by fun_prop : ContinuousOn (fun ρ : ℝ => (1 - ρ) ^ 2 / 2) _).mul
      (((by fun_prop : ContinuousOn (fun ρ : ℝ => -4 * s * ρ ^ 2 * κ * (1 - 2 * ρ)) _).div
        hVc2.continuousOn hV2).add
      ((by fun_prop : ContinuousOn (fun ρ : ℝ => 8 * ρ * κ) _).div hVc.continuousOn hVne))
  have cB : ContinuousOn (ksMassTB M s κ) (Icc 0 1) := by
    unfold ksMassTB
    exact (by fun_prop : ContinuousOn (fun ρ : ℝ => ρ * (1 - ρ)) _).mul
      (((by fun_prop : ContinuousOn (fun ρ : ℝ => 4 * ρ ^ 3 * s * κ - 2 * s * ρ ^ 2 * κ -
        2 * ρ * κ * (s + 2 * M ^ 2 - 2 * ρ * s + 2 * ρ ^ 2 * s)) _).div
        hVc2.continuousOn hV2).add
      ((by fun_prop : ContinuousOn (fun ρ : ℝ => 2 * κ * (1 - 4 * ρ)) _).div
        hVc.continuousOn hVne))
  have iA := cA.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have iB := cB.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have iK := (ksS_continuousOn_ksDmKer hσ).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have iG : IntervalIntegrable (fun ρ => κ / M ^ 2 * (-1 / 3 + 2 * ksDmKer (s / M ^ 2) ρ))
      volume 0 1 := (intervalIntegrable_const.add (iK.const_mul 2)).const_mul _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := ksMassR M s κ)
    (f' := fun ρ => ksMassT M s κ ρ - κ / M ^ 2 * (-1 / 3 + 2 * ksDmKer (s / M ^ 2) ρ))
    (a := 0) (b := 1) (fun ρ hρ => by
      rw [uIcc_of_le zero_le_one] at hρ
      exact ksMass_hasDerivAt_R hM0 (hVne ρ hρ)) ((iA.add iB).sub iG)
  have hR0 : ksMassR M s κ 0 = 0 := by simp [ksMassR, ksMassRN]
  have hR1 : ksMassR M s κ 1 = 0 := by simp [ksMassR, ksMassRN]
  rw [hR0, hR1, sub_zero] at hFTC
  simp only [ksMassT] at hFTC
  rw [intervalIntegral.integral_sub (iA.add iB) iG, intervalIntegral.integral_add iA iB] at hFTC
  rw [sub_eq_zero.mp hFTC, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add intervalIntegrable_const (iK.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp only [ksDm]
  field_simp
  ring

section Val

variable {m₀ M : ℝ} (hm₀ : 0 < m₀) (hM : m₀ ≤ M) {k : Fin 4 → ℝ}
  (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k)
include hm₀ hM hk

/-- **`M²(J_A + J_B) = κ (-1/3 - D(s/M²)/2)`**, `κ = k²k³`, `s = k·k`. -/
theorem ksMass_J_sum :
    (M : ℂ) ^ 2 * (ksMassJ ksMassBA (ksMassQA k) M k + ksMassJ ksMassBB (ksMassQB k M) M k) =
      ((k 2 * k 3 * (-1 / 3 - ksDm (Minkowski.dot k k / M ^ 2) / 2) : ℝ) : ℂ) := by
  have hV : ∀ ρ ∈ uIcc (0 : ℝ) 1, ksMassV M (Minkowski.dot k k) ρ ≠ 0 := fun ρ hρ => by
    rw [uIcc_of_le zero_le_one] at hρ
    exact (ksMass_V_pos hm₀ hM hk hρ).ne'
  rw [ksMass_J_A hm₀ hM hk, ksMass_J_B hm₀ hM hk,
    intervalIntegral.integral_congr fun ρ hρ => ksMass_fA k M ρ (hV ρ hρ),
    intervalIntegral.integral_congr fun ρ hρ => ksMass_fB k M ρ (hV ρ hρ),
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    ← ksMass_integral_T (κ := k 2 * k 3) hm₀ hM hk]
  push_cast
  ring

end Val

/-! ### The mass class -/

theorem ksMass_kF (e : ℝ) : kF e = -((e ^ 2 / (2 * π) ^ 4 : ℝ) : ℂ) := by
  have hI : (1 / I) ^ 3 = I := by
    rw [one_div, inv_I, neg_pow, I_pow_three]
    ring
  simp only [kF, hI]
  push_cast
  ring_nf
  rw [I_pow_four]
  ring

/-- **The mass-derivative block at `(2, 3)` in closed form**: on a flavour set with
`∑_f c_f = 0` and `δ (rep f) = d` for every `f`,
`fLim δ (k)₂₃ = d · i e²/(4π²) · k²k³ · ∑_f c_f D(k·k/M_f²)`. -/
theorem ksMass_fLim {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hsum : ∑ f, Φ.coeff f = 0) {e : ℝ} (he : e ≠ 0) (δ : F → ℝ) {d : ℝ}
    (hδ : ∀ f, δ (rep f) = d) {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) :
    fLim Φ rep e δ k 2 3 = (d : ℂ) * I * ((e ^ 2 / (4 * π ^ 2) : ℝ) : ℂ) *
      ((k 2 * k 3 : ℝ) : ℂ) *
        ∑ f, ((Φ.coeff f * ksDm (Minkowski.dot k k / Φ.mass f ^ 2) : ℝ) : ℂ) := by
  rw [ksMass_fLim_eq_param Φ rep hm₀ hmass hrep hPV₁ hPV₂ he δ hδ hk]
  have hterm : ∀ f, ((Φ.coeff f : ℂ) * (d : ℂ) * (8 * kF e * (Φ.mass f : ℂ) ^ 2)) *
      (I * (π : ℂ) ^ 2 * (ksMassJ ksMassBA (ksMassQA k) (Φ.mass f) k +
        ksMassJ ksMassBB (ksMassQB k (Φ.mass f)) (Φ.mass f) k)) =
      8 * kF e * (d : ℂ) * I * (π : ℂ) ^ 2 * ((k 2 * k 3 : ℝ) : ℂ) *
        ((-1 / 3 : ℂ) * (Φ.coeff f : ℂ) -
          (1 / 2 : ℂ) * ((Φ.coeff f * ksDm (Minkowski.dot k k / Φ.mass f ^ 2) : ℝ) : ℂ)) := by
    intro f
    have h := ksMass_J_sum hm₀ (hmass f) hk
    push_cast at h ⊢
    linear_combination 8 * kF e * (d : ℂ) * I * (π : ℂ) ^ 2 * (Φ.coeff f : ℂ) * h
  simp only [hterm]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hs : ∑ f, (Φ.coeff f : ℂ) = 0 := by exact_mod_cast hsum
  rw [hs, ksMass_kF]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- **The closed-form mass-derivative bubble** of the configuration `decCfg μ x`:
`ksMassF e μ x s = e²/(4π²) ∑_f c_f D(s/M_f²)`. -/
noncomputable def ksMassF (e μ x s : ℝ) : ℝ :=
  e ^ 2 / (4 * π ^ 2) *
    ∑ f, (decCfg μ x).coeff f * ksDm (s / (decCfg μ x).mass f ^ 2)

/-- **The mass class of `qDens`** at the configuration `decCfg μ x`:
`-(i/c²) ∑_g σ(M_g, u) fLim(single g 1)(k'(s))₂₃ = σ(μ, u) · ksMassF e μ x s`. -/
theorem ksMass_qDens_mass {e μ x c s u : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hc : 0 < c) (hs : -(4 * μ ^ 2) < s) (hs2 : s < 2 * c ^ 2) :
    -I / ((c ^ 2 : ℝ) : ℂ) * ∑ g, (sigma e ((decCfg μ x).mass g) u : ℂ) *
        fLim (decCfg μ x) (fun _ => 0) e (Pi.single g 1) (tiltVec c s) 2 3 =
      (sigma e μ u : ℂ) * (ksMassF e μ x s : ℂ) := by
  have hk : -(4 * μ ^ 2) < Minkowski.dot (tiltVec c s) (tiltVec c s) := by
    rw [dot_tiltVec hs2.le]
    exact hs
  have hpv := ksK_pv hμ hx
  have hsum : ∑ f, (decCfg μ x).coeff f = 0 := by
    have := hpv.1 0 rfl
    rwa [Finset.filter_true_of_mem fun _ _ => rfl] at this
  have hg : ∀ g, fLim (decCfg μ x) (fun _ => 0) e (Pi.single g 1) (tiltVec c s) 2 3 =
      (((Pi.single g 1 : Fin 3 → ℝ) 0 : ℝ) : ℂ) * I * ((e ^ 2 / (4 * π ^ 2) : ℝ) : ℂ) *
        ((tiltVec c s 2 * tiltVec c s 3 : ℝ) : ℂ) *
        ∑ f, (((decCfg μ x).coeff f * ksDm (Minkowski.dot (tiltVec c s) (tiltVec c s) /
          (decCfg μ x).mass f ^ 2) : ℝ) : ℂ) := fun g =>
    ksMass_fLim (decCfg μ x) (fun _ => 0) hμ (ksK_mass hμ hx) (fun _ => rfl) hpv.1 hpv.2 hsum
      he (Pi.single g 1) (d := (Pi.single g 1 : Fin 3 → ℝ) 0) (fun _ => rfl) hk
  simp only [hg]
  rw [Fin.sum_univ_three]
  simp only [Pi.single_eq_same, ne_eq, Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne,
    ofReal_zero, zero_mul, mul_zero, add_zero, ofReal_one, one_mul]
  have h23 : tiltVec c s 2 * tiltVec c s 3 = c ^ 2 := by
    simp only [tiltVec, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  have hm0 : (decCfg μ x).mass 0 = μ := rfl
  rw [h23, hm0, dot_tiltVec hs2.le]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hc2 : ((c ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hc 2).ne'
  simp only [ksMassF]
  push_cast at hc2 ⊢
  field_simp
  ring_nf
  rw [I_sq]
  ring

end QED.ChainProof.SetAKS

end
