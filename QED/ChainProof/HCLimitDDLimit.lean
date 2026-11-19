/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCLimitDD
public import QED.ChainProof.HCLimit
public import QED.TwoLoop.CountertermLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The `ε → 0⁺` limit of the `δ₃`–`δ₃` classes of set (b)

Helper level, Phase 5 Stage 1a (O3-6 for the one-loop classes). With the value of
`QED/ChainProof/HCLimitDD.lean`, the four `δ₃`–`δ₃` representatives have `ε → 0⁺` limits.

* `ddInsertion_eq`: the double insertion is `(1/i)(-(i/2)δ₃) k² d(k)` times the single insertion
  `photonInsertion` of the two-loop `δ₃` class (`V g V = -(i/2)δ₃ k² V`, the transverse projector
  identity), and `k² d(k) = (Λ² - m_γ²)(D_Λ⁻¹ - (m_γ² - iε) D_{m_γ}⁻¹ D_Λ⁻¹)` (`kSq_mul_scalar`).
  The integrand is therefore a combination of two one-loop integrands with the numerator of the
  two-loop `δ₃` class (degree four) and seven, resp. eight, propagators, with the coefficient
  `m_γ² - iε`.
* `integrableD_of_product`: a one-loop integrand whose product with the auxiliary loop
  `(k'² + M² - iε)⁻³` satisfies (T₉′) at two loops is integrable in both stages of (D).
* `exists_tendsto_of_kinds'`: the limit and the integrability for product data given by kinds
  (`QED.TwoLoop.CountertermLimit.exists_tendsto_of_kinds` with integrability).
* `exists_tendsto_ddIntegrand`: **the energy-first integral of the `δ₃`–`δ₃` integrand converges as
  `ε → 0⁺`**, for `m, m_γ, Λ > 0`, on-shell `p, p'` with `q² ≥ 0`.
* **`repLimit_repDD`**: `RepLimit (repDD s₀ s₁)` for all four field pairings.
* `classLimitLink_enum_of_reps'`: `ClassLimitLink enumClass` from the five remaining
  representatives (bubble–bubble, bubble–`δ₃`, `δ₃`–bubble).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.ChainProof.HCLimit

open QED.WickModel QED.TwoLoop.Insertion QED.TwoLoop.Bridge QED.TwoLoop.CountertermLimit
open QED.ChainProof.Enum QED.ChainProof.HCValue
open QED.Integration.TwoLoop (lineDenom castLoopMatrix LoopQuartic RefinedBound
  NoSubdivergenceRefined IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff)

/-! ### The double insertion -/

/-- The scalar part `d(k) = D_{m_γ}⁻¹ - D_Λ⁻¹` of the photon propagator. -/
noncomputable def pvScalar (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) : ℂ :=
  (((Minkowski.dot k k + mγ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹ -
    (((Minkowski.dot k k + Λ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I)⁻¹

theorem photonPropagator_eq_metric (mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (a b : Fin 4) :
    QED.OneLoop.photonPropagator mγ Λ ε k a b = (Minkowski.metric a b : ℂ) * pvScalar mγ Λ ε k :=
  rfl

theorem sum_metric_mul (a : Fin 4) (f : Fin 4 → ℂ) :
    ∑ x, (Minkowski.metric a x : ℂ) * f x = (Minkowski.metric a a : ℂ) * f a := by
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [Minkowski.metric, Ne.symm hx])
    (fun h => absurd (Finset.mem_univ a) h)]

theorem sum_mul_metric (a : Fin 4) (f : Fin 4 → ℂ) :
    ∑ x, f x * (Minkowski.metric x a : ℂ) = f a * (Minkowski.metric a a : ℂ) := by
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [Minkowski.metric, hx])
    (fun h => absurd (Finset.mem_univ a) h)]

/-- **The transverse projector identity** for the `photonCt` factor:
`∑_y V_{xy} g_{yy} V_{yw} = -(i/2) δ₃ k² V_{xw}`. -/
theorem sum_photonCtFactor_metric (δ₃ : ℝ) (k : Fin 4 → ℝ) (x w : Fin 4) :
    ∑ y, photonCtFactor δ₃ k x y * (Minkowski.metric y y : ℂ) * photonCtFactor δ₃ k y w =
      (-(I / 2) * δ₃) * ((Minkowski.dot k k : ℝ) : ℂ) * photonCtFactor δ₃ k x w := by
  simp only [photonCtFactor, Fin.sum_univ_four, Minkowski.dot_eq]
  fin_cases x <;> fin_cases w <;> simp [Minkowski.metric] <;> ring

theorem ddInsertion_eq (δ₃ mγ Λ ε : ℝ) (k : Fin 4 → ℝ) (ν ρ : Fin 4) :
    ddInsertion δ₃ mγ Λ ε k ν ρ =
      ((1 / I) * (-(I / 2) * δ₃)) * (((Minkowski.dot k k : ℝ) : ℂ) * pvScalar mγ Λ ε k) *
        photonInsertion δ₃ mγ Λ ε k ν ρ := by
  set d := pvScalar mγ Λ ε k
  have s1 : ddInsertion δ₃ mγ Λ ε k ν ρ = (1 / I) ^ 2 * ∑ x, (Minkowski.metric ν x : ℂ) *
      ((∑ y, ∑ z, (Minkowski.metric y z : ℂ) * (photonCtFactor δ₃ k x y *
        ∑ w, photonCtFactor δ₃ k z w * (Minkowski.metric w ρ : ℂ))) * d ^ 3) := by
    unfold ddInsertion
    simp only [photonPropagator_eq_metric, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
    ring
  have hy : ∀ x, ∑ y, (Minkowski.metric y y : ℂ) * (photonCtFactor δ₃ k x y *
      (photonCtFactor δ₃ k y ρ * (Minkowski.metric ρ ρ : ℂ))) =
      (∑ y, photonCtFactor δ₃ k x y * (Minkowski.metric y y : ℂ) * photonCtFactor δ₃ k y ρ) *
        (Minkowski.metric ρ ρ : ℂ) := fun x => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hpi : photonInsertion δ₃ mγ Λ ε k ν ρ = (1 / I) * ∑ a, (Minkowski.metric ν a : ℂ) *
      ((∑ b, photonCtFactor δ₃ k a b * (Minkowski.metric b ρ : ℂ)) * d ^ 2) := by
    unfold photonInsertion
    simp only [photonPropagator_eq_metric, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Minkowski.metric_symm ρ b]
    ring
  rw [s1, hpi]
  simp only [sum_mul_metric, sum_metric_mul]
  rw [hy, sum_photonCtFactor_metric]
  ring

/-- `k² d(k) = (Λ² - m_γ²)(D_Λ⁻¹ - (m_γ² - iε) D_{m_γ}⁻¹ D_Λ⁻¹)` for `ε > 0`. -/
theorem kSq_mul_pvScalar (mγ Λ : ℝ) {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) :
    ((Minkowski.dot k k : ℝ) : ℂ) * pvScalar mγ Λ ε k =
      ((Λ ^ 2 - mγ ^ 2 : ℝ) : ℂ) * ((propDenom Λ ε k)⁻¹ -
        (((mγ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) * ((propDenom mγ ε k)⁻¹ * (propDenom Λ ε k)⁻¹)) := by
  have hne : ∀ M : ℝ, propDenom M ε k ≠ 0 := fun M =>
    QED.TwoLoop.NestedVPFubiniBound.denom_ne_zero M hε k
  have h1 := hne mγ
  have h2 := hne Λ
  unfold pvScalar
  change ((Minkowski.dot k k : ℝ) : ℂ) * ((propDenom mγ ε k)⁻¹ - (propDenom Λ ε k)⁻¹) = _
  field_simp
  simp only [propDenom]
  push_cast
  ring

/-! ### Integrability from the product with the auxiliary loop -/

theorem auxSpatial_ne_zero {M : ℝ} (hM : 0 < M) (ε : ℝ) (v : Fin 3 → ℝ) :
    auxSpatial M ε v ≠ 0 := by
  unfold auxSpatial
  refine neg_ne_zero.mpr (mul_ne_zero (by
    have := Real.pi_pos
    exact_mod_cast (by positivity : (3 * Real.pi / 8 : ℝ) ≠ 0)) ?_)
  rw [Complex.cpow_def_of_ne_zero (aux_ne_zero hM ε v)]
  exact Complex.exp_ne_zero _

theorem propDenom_ne_zero (M : ℝ) {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) : propDenom M ε k ≠ 0 :=
  QED.TwoLoop.NestedVPFubiniBound.denom_ne_zero M hε k

/-- **A one-loop integrand is integrable in both stages of (D)** when its product with the
auxiliary loop `(k'² + M² - iε)⁻³` satisfies (T₉′) at two loops. -/
theorem integrableD_of_product {F : (Fin 4 → ℝ) → ℂ} {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    (hJ : QED.TwoLoop.jointEnergyFirstIntegrable 2
      (fun ℓ => F (ℓ 0) * ((propDenom M ε (ℓ 1))⁻¹) ^ 3)) :
    QED.TwoLoop.NestedVP.IntegrableD F := by
  obtain ⟨h1, h2⟩ := hJ
  constructor
  · intro v
    have h := (QED.TwoLoop.NestedVP.integrable_finTwo_iff _).mp (h1 ![v, 0])
    obtain ⟨y, hy⟩ := h.prod_left_ae.exists
    have hy' := hy.mul_const ((((propDenom M ε (Fin.cons y 0)))⁻¹) ^ 3)⁻¹
    refine hy'.congr (Eventually.of_forall fun t => ?_)
    have hne : ((propDenom M ε (Fin.cons y 0))⁻¹) ^ 3 ≠ 0 :=
      pow_ne_zero _ (inv_ne_zero (propDenom_ne_zero M hε _))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact mul_inv_cancel_right₀ hne _
  · have hin : ∀ v : Fin 2 → Fin 3 → ℝ,
        ∫ t : Fin 2 → ℝ, F (Fin.cons (t 0) (v 0)) * ((propDenom M ε (Fin.cons (t 1) (v 1)))⁻¹) ^ 3 =
          (∫ t : ℝ, F (Fin.cons t (v 0))) * auxSpatial M ε (v 1) := fun v => by
      rw [integral_finTwo_mul (fun t => F (Fin.cons t (v 0)))
        (fun t => ((propDenom M ε (Fin.cons t (v 1)))⁻¹) ^ 3), integral_aux_time M hε]
    have h2' : Integrable fun v : Fin 2 → Fin 3 → ℝ =>
        (∫ t : ℝ, F (Fin.cons t (v 0))) * auxSpatial M ε (v 1) :=
      h2.congr (Eventually.of_forall fun v => hin v)
    have h := (QED.TwoLoop.NestedVP.integrable_finTwo_iff _).mp h2'
    obtain ⟨y, hy⟩ := h.prod_left_ae.exists
    have hy' := hy.mul_const (auxSpatial M ε y)⁻¹
    refine hy'.congr (Eventually.of_forall fun v => ?_)
    have hne := auxSpatial_ne_zero hM ε y
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact mul_inv_cancel_right₀ hne _

/-- **The one-loop limit and integrability for product data given by kinds**: the hypotheses of
`QED.TwoLoop.CountertermLimit.exists_tendsto_of_kinds` give, besides the limit, the integrability of
`F ε` in both stages of (D) for every `ε > 0`. -/
theorem exists_tendsto_of_kinds' {m : ℕ} (hm7 : 7 ≤ m) (κ : Fin (m + 1) → LineKind)
    (Ms : Fin (m + 1) → ℝ) {mass μ : ℝ} (hmass : 0 < mass) (hμ : 0 < μ) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hMe : ∀ i, κ i ≠ .pho → Ms i ^ 2 = mass ^ 2) (hMp : ∀ i, κ i = .pho → μ ^ 2 ≤ Ms i ^ 2)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun i => (κ i).dir)
    (hcard : ({0, 1, 2, 3} : Finset (Fin (m + 1))).card = 4)
    (hE : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))), κ e ≠ .aux)
    (N : (Fin 4 → ℝ) → ℂ) (hN : IsLoopPoly 2 4 fun ℓ => N (ℓ 0))
    (F : ℝ → (Fin 4 → ℝ) → ℂ)
    (hfac : ∀ ε : ℝ, 0 < ε → ∀ ℓ : Fin 2 → Fin 4 → ℝ,
      N (ℓ 0) * ∏ i, (propDenom (Ms i) ε ((κ i).lineMom p p' ℓ))⁻¹ =
        F ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3) :
    (∀ ε : ℝ, 0 < ε → QED.TwoLoop.NestedVP.IntegrableD (F ε)) ∧
      ∃ L : ℂ, Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (F ε)) (𝓝[>] 0) (𝓝 L) := by
  refine ⟨fun ε hε => ?_, exists_tendsto_of_kinds hm7 κ Ms hmass hμ hp hp' hq hMe hMp hcrit
    hcard hE N hN F hfac⟩
  obtain ⟨Q, hQ⟩ := hN.exists_loopQuartic
  have hα : ∀ e ∈ ({0, 1, 2, 3} : Finset (Fin (m + 1))),
      (castLoopMatrix fun i => (κ i).dir) e = ![1, 0] := by
    intro e he
    have h := hE e he
    funext s
    rcases hk : κ e with _ | _ | _ | _
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · fin_cases s <;> simp [castLoopMatrix, hk, LineKind.dir]
    · exact absurd hk h
  have hB : RefinedBound (castLoopMatrix fun i => (κ i).dir) {0, 1, 2, 3} 4 Q.eval :=
    refinedBound_of_dependsOnZero _ hcard hα Q fun ℓ => by simp only [hQ, Matrix.cons_val_zero]
  have hJ := QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
    Q (castLoopMatrix fun i => (κ i).dir) (fun i => (κ i).mom p p') Ms hm7 hε
    ((noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit) hB
  refine integrableD_of_product hmass hε ?_
  have e : (fun ℓ : Fin 2 → Fin 4 → ℝ => Q.eval ℓ *
      ∏ i, (lineDenom (castLoopMatrix fun i => (κ i).dir) (fun i => (κ i).mom p p') Ms ε i ℓ)⁻¹) =
      fun ℓ => F ε (ℓ 0) * ((propDenom mass ε (ℓ 1))⁻¹) ^ 3 := by
    funext ℓ
    rw [hQ, prod_lineDenom_kinds]
    exact hfac ε hε ℓ
  rw [← e]
  exact hJ

/-! ### The limit of the `δ₃`–`δ₃` integrand -/

/-- The line kinds of the first piece: the `δ₃` class lines and one more photon line. -/
def kindsDD1 : Fin 10 → LineKind := ![.out, .inn, .pho, .pho, .pho, .pho, .pho, .aux, .aux, .aux]

/-- The line masses of the first piece. -/
def massesDD1 (P : Params) : Fin 10 → ℝ :=
  ![P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.Λ, P.m, P.m, P.m]

/-- The line kinds of the second piece: the `δ₃` class lines and two more photon lines. -/
def kindsDD2 : Fin 11 → LineKind :=
  ![.out, .inn, .pho, .pho, .pho, .pho, .pho, .pho, .aux, .aux, .aux]

/-- The line masses of the second piece. -/
def massesDD2 (P : Params) : Fin 11 → ℝ :=
  ![P.m, P.m, P.mγ, P.Λ, P.mγ, P.Λ, P.mγ, P.Λ, P.m, P.m, P.m]

/-- The `δ₃` class integrand times `D_Λ⁻¹`. -/
noncomputable def ddPiece1 (P : Params) (p' p : Fin 4 → ℝ) (μ α β : Fin 4) (ε : ℝ)
    (k : Fin 4 → ℝ) : ℂ :=
  vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
    (QED.OneLoop.electronPropagator P.m ε (p + k)) (photonInsertion P.δ₃ P.mγ P.Λ ε k) α β *
    (propDenom P.Λ ε k)⁻¹

/-- The `δ₃` class integrand times `D_{m_γ}⁻¹ D_Λ⁻¹`. -/
noncomputable def ddPiece2 (P : Params) (p' p : Fin 4 → ℝ) (μ α β : Fin 4) (ε : ℝ)
    (k : Fin 4 → ℝ) : ℂ :=
  vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
    (QED.OneLoop.electronPropagator P.m ε (p + k)) (photonInsertion P.δ₃ P.mγ P.Λ ε k) α β *
    ((propDenom P.mγ ε k)⁻¹ * (propDenom P.Λ ε k)⁻¹)

/-- The coefficient `(1/i)(-(i/2)δ₃)(Λ² - m_γ²)` of the two pieces. -/
noncomputable def ddCoeff (P : Params) : ℂ :=
  (1 / I) * (-(I / 2) * P.δ₃) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ)

/-- **The `δ₃`–`δ₃` integrand in two pieces**, for `ε > 0`. -/
theorem ddIntegrand_eq (P : Params) {ε : ℝ} (hε : 0 < ε) (p' p : Fin 4 → ℝ) (μ α β : Fin 4)
    (k : Fin 4 → ℝ) :
    vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
        (QED.OneLoop.electronPropagator P.m ε (p + k)) (ddInsertion P.δ₃ P.mγ P.Λ ε k) α β =
      ddCoeff P * (ddPiece1 P p' p μ α β ε k -
        (((P.mγ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) * ddPiece2 P p' p μ α β ε k) := by
  have e : ddInsertion P.δ₃ P.mγ P.Λ ε k = fun ν ρ =>
      (((1 / I) * (-(I / 2) * P.δ₃)) * (((Minkowski.dot k k : ℝ) : ℂ) * pvScalar P.mγ P.Λ ε k)) *
        photonInsertion P.δ₃ P.mγ P.Λ ε k ν ρ := funext fun ν => funext fun ρ =>
    ddInsertion_eq P.δ₃ P.mγ P.Λ ε k ν ρ
  rw [e, vertexChain_smul_photon, Matrix.smul_apply, smul_eq_mul, kSq_mul_pvScalar _ _ hε]
  unfold ddPiece1 ddPiece2 ddCoeff
  ring

theorem efi_sub_mul {f g : (Fin 4 → ℝ) → ℂ} (hf : QED.TwoLoop.NestedVP.IntegrableD f)
    (hg : QED.TwoLoop.NestedVP.IntegrableD g) (a : ℂ) :
    QED.OneLoop.energyFirstIntegral (fun k => f k - a * g k) =
      QED.OneLoop.energyFirstIntegral f - a * QED.OneLoop.energyFirstIntegral g := by
  unfold QED.OneLoop.energyFirstIntegral
  have hin : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, (f (Fin.cons t v) - a * g (Fin.cons t v)) =
      (∫ t : ℝ, f (Fin.cons t v)) - a * ∫ t : ℝ, g (Fin.cons t v) := fun v => by
    rw [integral_sub (hf.1 v) ((hg.1 v).const_mul a), integral_const_mul]
  simp_rw [hin]
  rw [integral_sub hf.2 (hg.2.const_mul a), integral_const_mul]

/-- **The energy-first integral of the `δ₃`–`δ₃` integrand converges as `ε → 0⁺`**, for
`m, m_γ, Λ > 0`, on-shell `p, p'` with `q² ≥ 0`, and all indices. -/
theorem exists_tendsto_ddIntegrand (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ α β : Fin 4) :
    ∃ L : ℂ, Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun k =>
      vertexChain P.e μ (QED.OneLoop.electronPropagator P.m ε (p' + k))
        (QED.OneLoop.electronPropagator P.m ε (p + k)) (ddInsertion P.δ₃ P.mγ P.Λ ε k) α β)
      (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨h1, h2⟩ := sq_min_le P hmγ hΛ
  obtain ⟨hI1, L1, hL1⟩ := exists_tendsto_of_kinds' (by norm_num) kindsDD1 (massesDD1 P) hm
    (lt_min hmγ hΛ) hp hp' hq
    (fun i hi => by fin_cases i <;> simp_all [kindsDD1, massesDD1])
    (fun i hi => by fin_cases i <;> simp_all [kindsDD1, massesDD1])
    (by decide) (by decide) (by decide)
    (fun k => numD3 P p' p μ k α β) (isLoopPoly_numD3 P _ _ _ _ _) (ddPiece1 P p' p μ α β)
    (fun ε hε ℓ => by
      rw [ddPiece1, integrand_d3_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsDD1, massesDD1,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  obtain ⟨hI2, L2, hL2⟩ := exists_tendsto_of_kinds' (by norm_num) kindsDD2 (massesDD2 P) hm
    (lt_min hmγ hΛ) hp hp' hq
    (fun i hi => by fin_cases i <;> simp_all [kindsDD2, massesDD2])
    (fun i hi => by fin_cases i <;> simp_all [kindsDD2, massesDD2])
    (by decide) (by decide) (by decide)
    (fun k => numD3 P p' p μ k α β) (isLoopPoly_numD3 P _ _ _ _ _) (ddPiece2 P p' p μ α β)
    (fun ε hε ℓ => by
      rw [ddPiece2, integrand_d3_eq P hε.ne', Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, kindsDD2, massesDD2,
        LineKind.lineMom, Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring)
  have ha : Tendsto (fun ε : ℝ => ((P.mγ ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I) (𝓝[>] 0)
      (𝓝 (((P.mγ ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I)) :=
    ((continuous_const.sub (continuous_ofReal.mul continuous_const)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  refine ⟨ddCoeff P * (L1 - (((P.mγ ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) * L2),
    ((hL1.sub (ha.mul hL2)).const_mul (ddCoeff P)).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [ddIntegrand_eq P hε]
  rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul, efi_sub_mul (hI1 ε hε) (hI2 ε hε)]

/-- **The `δ₃`–`δ₃` representatives have `ε → 0⁺` limits**, for all four field pairings. -/
theorem repLimit_repDD (s₀ s₁ : Fin 2) : RepLimit (repDD s₀ s₁) := by
  intro P hA p' p hpq α β μ
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  obtain ⟨L, hL⟩ := exists_tendsto_ddIntegrand P hA.hm hA.hmγ hA.hΛ hp hp' hq.le μ α β
  refine ⟨L, hL.congr' (Eventually.of_forall fun ε => ?_)⟩
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hΦ : chainFlavors P =
      (⟨({ P with ε := ε } : Params).mass, ({ P with ε := ε } : Params).loopCoeff, 0⟩ :
        QED.Lepton.Flavors (Fin 3)) := rfl
  dsimp only
  rw [hΦ, QED.ChainProof.Enum.contractionValue₂_params', contractionValue₂_repDD { P with ε := ε } s₀ s₁
    hmom (fun _ => α) (fun _ => β) (fun _ => μ)]

/-- **`ClassLimitLink enumClass` from the bubble–bubble, bubble–`δ₃` and `δ₃`–bubble
representatives**: the four `δ₃`–`δ₃` classes are discharged by `repLimit_repDD`. -/
theorem classLimitLink_enum_of_reps' (hBB : RepLimit repBB) (hBD : ∀ s, RepLimit (repBD s))
    (hDB : ∀ s, RepLimit (repDB s)) : ClassLimitLink enumClass :=
  classLimitLink_enum_of_reps hBB hBD hDB repLimit_repDD

end QED.ChainProof.HCLimit

end
