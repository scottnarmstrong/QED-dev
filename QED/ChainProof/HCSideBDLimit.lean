/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideBDPauli
public import QED.ChainProof.HCSideKernel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The `ε → 0⁺` limit of the Pauli-projected bubble–`δ₃` outer integrand

Helper level, Phase 5 Stage 1a (O3-6 for `QED.ChainProof.Enum.repBD s`, `repDB s`). The Pauli
projection of the bubble–`δ₃` outer integrand is
`-(i/2) δ₃ (Λ² - m_γ²)² (t_Λ hIntG(…, Λ) - t_{m_γ} hIntG(…, m_γ))`
(`QED.ChainProof.HCSide.pauliNum_bdIntegrand`). This file takes its limit with the generic engine
of `QED/TwoLoop/VPHalfAtGen*.lean` and identifies the limits of the extra photon lines with the
five-denominator kernels.

* `tendsto_efi_pauliNum_bdIntegrand`: the energy-first integral of the Pauli projection tends to
  `-(i/2) δ₃ (b² - a²)² (b² L_b - a² L_a)`, `L_M` the limit of
  `QED.TwoLoop.VPHalfAtGen.tendsto_efi_hIntG` over the masses `(a, b, a, b, M)`.
* `powLimit_one_comb`: `b² L¹_b - a² L¹_a = L²_a - L²_b` for the `k²` (resp. `k⁴`) vertices over
  `(a, b, a, b, M)`: `t_b/D_b - t_a/D_a = k² d(k)` and `(b² - a²)/(D_a D_b) = 1/D_a - 1/D_b`.
* `powLimit_two_sideMs`: the `k⁴` vertex over `(a, b, a, b, M)` is
  `QED.TwoLoop.VPHalfAtLimit.s2Prod5Limit`, hence `∫ kernVP m a b M`.
* `powLimit_two_snoc`: one more photon-type line `μ ≠ M` is a difference quotient:
  `L²(…, M, μ) = (L²(…, M) - L²(…, μ))/(μ² - M²)`.
* `kernVP_side_eq_photon`: the corresponding combination of kernels is
  `2 y² m² K³ D(K)³/(K + μ²)` in photon-function form.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.VPUnitNested QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.VPHalfAtAssembly (P4 cOne logSum efi_sub ev_pos_le_one)
open QED.TwoLoop.VPHalfAtLimit (prodIntegrand massShift denom_ne_zero_of_pos
  denom_eq_add_massShift s2Prod5Integrand s2Prod5Limit tendsto_energyFirstIntegral_s2Prod5Integrand)
open QED.TwoLoop.VPHalfAtGen
open QED.TwoLoop.VPHalf (kernVP kern5 vpK kDen_eq_vpK kC_eq_vpK)
open QED.TwoLoop.UnitVPLink (photonD)
open QED.Integration (feynmanMeasure)
open QED.OneLoop (energyFirstIntegral)

/-! ### The photon-type vertices over `(a, b, a, b, M)` -/

theorem powInt_sideMs (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) (a b M ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    powInt N m j (sideMs a b M) (fun _ => ε) ε p' p ℓ =
      ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ j * prodIntegrand N m ![a, b, a, b] (fun _ => ε) ε p' p ℓ *
        (QED.OneLoop.denom M ε ℓ)⁻¹ := by
  unfold powInt sideMs
  rw [const_eq_snoc (k := 2) ε, prodIntegrand_snoc]
  ring

theorem powInt_snoc_sideMs (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) (j : ℕ) (a b M μ ε : ℝ)
    (p' p ℓ : Fin 4 → ℝ) :
    powInt N m j (Fin.snoc (sideMs a b M) μ : Fin (2 + 1 + 1 + 2) → ℝ) (fun _ => ε) ε p' p ℓ =
      powInt N m j (sideMs a b M) (fun _ => ε) ε p' p ℓ * (QED.OneLoop.denom μ ε ℓ)⁻¹ := by
  rw [const_eq_snoc (k := 2 + 1) ε, powInt_snoc]

/-- **The pointwise identity behind `powLimit_one_comb`.** -/
theorem powInt_one_comb (N : (Fin 4 → ℝ) → ℂ) (m a b : ℝ) {ε : ℝ} (hε : 0 < ε)
    (p' p ℓ : Fin 4 → ℝ) :
    massShift b ε * powInt N m 1 (sideMs a b b) (fun _ => ε) ε p' p ℓ -
        massShift a ε * powInt N m 1 (sideMs a b a) (fun _ => ε) ε p' p ℓ =
      powInt N m 2 (sideMs a b a) (fun _ => ε) ε p' p ℓ -
        powInt N m 2 (sideMs a b b) (fun _ => ε) ε p' p ℓ := by
  have h := kSq_mul_photonScalar a b hε ℓ
  rw [photonScalar_eq_denom] at h
  simp only [powInt_sideMs]
  set Q := prodIntegrand N m ![a, b, a, b] (fun _ => ε) ε p' p ℓ
  set s : ℂ := ((Minkowski.dot ℓ ℓ : ℝ) : ℂ)
  linear_combination (-(s * Q)) * h

/-- **The pointwise identity behind `powLimit_two_snoc`.** -/
theorem powInt_two_snoc (N : (Fin 4 → ℝ) → ℂ) (m a b : ℝ) {M μ : ℝ} (hMμ : μ ^ 2 ≠ M ^ 2)
    {ε : ℝ} (hε : 0 < ε) (p' p ℓ : Fin 4 → ℝ) :
    powInt N m 2 (Fin.snoc (sideMs a b M) μ : Fin (2 + 1 + 1 + 2) → ℝ) (fun _ => ε) ε p' p ℓ =
      (((μ ^ 2 - M ^ 2 : ℝ) : ℂ))⁻¹ * (powInt N m 2 (sideMs a b M) (fun _ => ε) ε p' p ℓ -
        powInt N m 2 (sideMs a b μ) (fun _ => ε) ε p' p ℓ) := by
  rw [powInt_snoc_sideMs, powInt_sideMs, powInt_sideMs]
  have hM := denom_ne_zero_of_pos (M := M) hε ℓ
  have hμ := denom_ne_zero_of_pos (M := μ) hε ℓ
  have hd : ((μ ^ 2 - M ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hMμ
  have e : QED.OneLoop.denom μ ε ℓ - QED.OneLoop.denom M ε ℓ = ((μ ^ 2 - M ^ 2 : ℝ) : ℂ) := by
    simp only [QED.OneLoop.denom]; push_cast; ring
  rw [← e]
  rw [← e] at hd
  field_simp

theorem s2Prod5Integrand_eq_powInt (N : (Fin 4 → ℝ) → ℂ) (m a b M ε : ℝ) (p' p ℓ : Fin 4 → ℝ) :
    s2Prod5Integrand N m ![a, b, a, b, M] (fun _ => ε) ε p' p ℓ =
      powInt N m 2 (sideMs a b M) (fun _ => ε) ε p' p ℓ := by
  rw [powInt_sideMs]
  unfold s2Prod5Integrand prodIntegrand
  rw [Fin.prod_univ_five, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  ring

/-! ### Identities between the limits -/

section Limits

variable {m : ℝ} {p' p : Fin 4 → ℝ} {N : (Fin 4 → ℝ) → ℂ} {α : ℂ} {CN : ℝ}

theorem tendsto_efi_sideMs (hm : 0 < m) {M₀ : ℝ} (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {j k : ℕ} (hjk : j ≤ k) {Ms : Fin (k + 2) → ℝ}
    (hMs : ∀ i, M₀ ≤ Ms i) :
    Tendsto (fun ε => energyFirstIntegral (powInt N m j Ms (fun _ => ε) ε p' p)) (𝓝[>] 0)
      (𝓝 (powLimit α N m p' p j Ms)) :=
  tendsto_efi_powInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb tendsto_id j k hjk Ms (fun ε _ => ε) hMs
    (fun _ => tendsto_id)

theorem efInt_sideMs (hm : 0 < m) {M₀ : ℝ} (hM₀ : 0 < M₀)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {j k : ℕ} (hjk : j ≤ k) {Ms : Fin (k + 2) → ℝ}
    (hMs : ∀ i, M₀ ≤ Ms i) {ε : ℝ} (hε : 0 < ε) :
    EFInt (powInt N m j Ms (fun _ => ε) ε p' p) :=
  efInt_powInt hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hjk hMs (fun _ => hε) hε

theorem sideMs_ge {a b M M₀ : ℝ} (ha : M₀ ≤ a) (hb : M₀ ≤ b) (hM : M₀ ≤ M) :
    ∀ i, M₀ ≤ sideMs a b M i := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [sideMs] using hM
  · simp only [sideMs, Fin.snoc_castSucc]
    fin_cases j <;> simp [ha, hb]

theorem snoc_sideMs_ge {a b M μ M₀ : ℝ} (ha : M₀ ≤ a) (hb : M₀ ≤ b) (hM : M₀ ≤ M)
    (hμ : M₀ ≤ μ) : ∀ i, M₀ ≤ (Fin.snoc (sideMs a b M) μ : Fin (2 + 1 + 1 + 2) → ℝ) i := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · convert hμ using 1
    exact Fin.snoc_last (α := fun _ => ℝ) _ _
  · simpa using sideMs_ge ha hb hM j

theorem tendsto_massShift_nhds (M : ℝ) :
    Tendsto (fun ε => massShift M ε) (𝓝[>] 0) (𝓝 ((M ^ 2 : ℝ) : ℂ)) :=
  tendsto_massShift M (tendsto_id.mono_left nhdsWithin_le_nhds)

/-- **`b² L¹_b - a² L¹_a = L²_a - L²_b`.** -/
theorem powLimit_one_comb (hm : 0 < m) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) :
    ((b ^ 2 : ℝ) : ℂ) * powLimit α N m p' p 1 (sideMs a b b) -
        ((a ^ 2 : ℝ) : ℂ) * powLimit α N m p' p 1 (sideMs a b a) =
      powLimit α N m p' p 2 (sideMs a b a) - powLimit α N m p' p 2 (sideMs a b b) := by
  set M₀ := min a b
  have hM₀ : 0 < M₀ := lt_min ha hb
  have hga := sideMs_ge (min_le_left a b) (min_le_right a b) (min_le_left a b)
  have hgb := sideMs_ge (min_le_left a b) (min_le_right a b) (min_le_right a b)
  have T1a := tendsto_efi_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 1) (by omega) hga
  have T1b := tendsto_efi_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 1) (by omega) hgb
  have T2a := tendsto_efi_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 2) (by omega) hga
  have T2b := tendsto_efi_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 2) (by omega) hgb
  have L := ((tendsto_massShift_nhds b).mul T1b).sub ((tendsto_massShift_nhds a).mul T1a)
  refine tendsto_nhds_unique L ((T2a.sub T2b).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have i1a := efInt_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 1) (by omega) hga hε
  have i1b := efInt_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 1) (by omega) hgb hε
  have i2a := efInt_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 2) (by omega) hga hε
  have i2b := efInt_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 2) (by omega) hgb hε
  rw [← efi_sub i2a i2b, ← efi_const_mul, ← efi_const_mul,
    ← efi_sub (i1b.const_mul _) (i1a.const_mul _)]
  congr 1
  funext ℓ
  exact (powInt_one_comb N m a b hε p' p ℓ).symm

/-- **The `k⁴` vertex over `(a, b, a, b, M)` is `s2Prod5Limit`.** -/
theorem powLimit_two_sideMs (hm : 0 < m) {a b M : ℝ} (ha : 0 < a) (hb : 0 < b) (hM : 0 < M)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) :
    powLimit α N m p' p 2 (sideMs a b M) = s2Prod5Limit α N m ![a, b, a, b, M] p' p := by
  set M₀ := min a (min b M)
  have hM₀ : 0 < M₀ := lt_min ha (lt_min hb hM)
  have h1 : M₀ ≤ a := min_le_left _ _
  have h2 : M₀ ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : M₀ ≤ M := (min_le_right _ _).trans (min_le_right _ _)
  have T := tendsto_efi_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 2) (by omega)
    (sideMs_ge h1 h2 h3)
  have S := tendsto_energyFirstIntegral_s2Prod5Integrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
    (Ms := ![a, b, a, b, M]) (fun j => by fin_cases j <;> simp [h1, h2, h3])
    (l := 𝓝[>] (0 : ℝ)) (ε := id) (es := fun ε _ => ε) tendsto_id (fun _ => tendsto_id)
  refine tendsto_nhds_unique T (S.congr fun ε => ?_)
  congr 1
  funext ℓ
  exact s2Prod5Integrand_eq_powInt N m a b M ε p' p ℓ

/-- **One more photon-type line is a difference quotient**, `μ² ≠ M²`. -/
theorem powLimit_two_snoc (hm : 0 < m) {a b M μ : ℝ} (ha : 0 < a) (hb : 0 < b) (hM : 0 < M)
    (hμ : 0 < μ) (hMμ : μ ^ 2 ≠ M ^ 2)
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (hNc : Continuous N)
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) :
    powLimit α N m p' p 2 (Fin.snoc (sideMs a b M) μ : Fin (2 + 1 + 1 + 2) → ℝ) =
      (((μ ^ 2 - M ^ 2 : ℝ) : ℂ))⁻¹ *
        (powLimit α N m p' p 2 (sideMs a b M) - powLimit α N m p' p 2 (sideMs a b μ)) := by
  set M₀ := min (min a b) (min M μ)
  have hM₀ : 0 < M₀ := lt_min (lt_min ha hb) (lt_min hM hμ)
  have h1 : M₀ ≤ a := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : M₀ ≤ b := (min_le_left _ _).trans (min_le_right _ _)
  have h3 : M₀ ≤ M := (min_le_right _ _).trans (min_le_left _ _)
  have h4 : M₀ ≤ μ := (min_le_right _ _).trans (min_le_right _ _)
  have T6 := tendsto_efi_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 2) (k := 2 + 1 + 1)
    (by omega) (snoc_sideMs_ge h1 h2 h3 h4)
  have TM := tendsto_efi_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 2) (by omega)
    (sideMs_ge h1 h2 h3)
  have Tμ := tendsto_efi_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 2) (by omega)
    (sideMs_ge h1 h2 h4)
  refine tendsto_nhds_unique T6 (((TM.sub Tμ).const_mul _).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have iM := efInt_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 2) (by omega)
    (sideMs_ge h1 h2 h3) hε
  have iμ := efInt_sideMs hm hM₀ hp' hp hp0' hp0 hNc hNq hNb (j := 2) (by omega)
    (sideMs_ge h1 h2 h4) hε
  rw [← efi_sub iM iμ, ← efi_const_mul]
  congr 1
  funext ℓ
  exact (powInt_two_snoc N m a b hMμ hε p' p ℓ).symm

end Limits

/-! ### The kernels in photon-function form -/

/-- **The spectral combination of kernels in photon-function form**: for `μ² ≠ a², b²`, on the
open square, `(b² - a²)² (b² (kernVP_b - kernVP_μ)/(μ² - b²) - a² (kernVP_a - kernVP_μ)/(μ² - a²))
= 2 y² m² K³ D(K)³/(K + μ²)`. -/
theorem kernVP_side_eq_photon {m a b μ s : ℝ} {z : ℝ × ℝ} (hm : 0 < m) (hs : 0 ≤ s)
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) (hy1 : z.2 ≠ 1) (hμa : μ ^ 2 ≠ a ^ 2)
    (hμb : μ ^ 2 ≠ b ^ 2) :
    (b ^ 2 - a ^ 2) ^ 2 * (b ^ 2 / (μ ^ 2 - b ^ 2) * (kernVP m a b b s z - kernVP m a b μ s z) -
      a ^ 2 / (μ ^ 2 - a ^ 2) * (kernVP m a b a s z - kernVP m a b μ s z)) =
      2 * (z.2 ^ 2 * m ^ 2 * (vpK m s z ^ 3 * photonD a b (vpK m s z) ^ 3 /
        (vpK m s z + μ ^ 2))) := by
  have h1 : 0 < 1 - z.2 := sub_pos.2 (lt_of_le_of_ne hz.2.2 hy1)
  have hK : 0 < vpK m s z := div_pos (QED.TwoLoop.VPUnitNested.kC_pos' hm hs hz) h1
  have hKa : vpK m s z + a ^ 2 ≠ 0 := by positivity
  have hKb : vpK m s z + b ^ 2 ≠ 0 := by positivity
  have hKμ : vpK m s z + μ ^ 2 ≠ 0 := by positivity
  have hμa' : μ ^ 2 - a ^ 2 ≠ 0 := sub_ne_zero.2 hμa
  have hμb' : μ ^ 2 - b ^ 2 ≠ 0 := sub_ne_zero.2 hμb
  simp only [kernVP, kern5, kDen_eq_vpK h1.ne', kC_eq_vpK h1.ne', photonD]
  field_simp
  ring

end QED.ChainProof.HCSide

end
