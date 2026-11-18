/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtLimitEngine
public import QED.Integration.FeynmanParameterGeneral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The one-loop vertex with a product of photon denominators and their own prescriptions

The second layer of the analytic engine for the `ε → 0⁺` limit of the vacuum-polarization class
in closed form (obligation O2-8 at the `ε → 0` level). Fix on-shell positive-energy `p, p'`, a
numerator `N` quadratic in the loop energy with constant leading coefficient and of quadratic
growth, and `k + 2 ≥ 2` photon denominators with masses `M_j ≥ M₀ > 0` and prescriptions
`ε_j > 0`, possibly repeated and possibly different:

`F(ℓ) = N(ℓ) / (D_m(p' + ℓ; ε) D_m(p + ℓ; ε) ∏_j D_{M_j}(ℓ; ε_j))` (`prodIntegrand`).

* **Photon superposition** (`prodIntegrand_eq_integral`): by the general Feynman formula
  (`QED.Integration.Feynman.prod_inv_eq_factorial_mul_integral_simplex`), the photon product is
  `(k+1)! ∫_Δ D_{M(u)}(ℓ; ε(u))^{-(k+2)} du` with `M(u)² = ∑_j u_j M_j²` (`mixMass`) and
  `ε(u) = ∑_j u_j ε_j` (`mixEps`): the different prescriptions combine into one.
* **Exchange with the energy-first integral** (`energyFirstIntegral_prodIntegrand_eq`): the
  energy-first integral of `F` is `(k+1)!` times the simplex integral of the energy-first
  integrals of `QED.TwoLoop.VPHalfAtLimit.powIntegrand`, by two Fubini steps (energy × simplex at
  fixed spatial momentum, then space × simplex), with the bounds of
  `QED/TwoLoop/VPHalfAtLimitEngine.lean`, uniform on the simplex.
* **The limit** (`tendsto_energyFirstIntegral_prodIntegrand`): when `ε → 0⁺` and every
  `ε_j → 0⁺` (along any countably generated filter), the energy-first integral tends to
  `prodLimit = (k+1)! ∫_Δ ∫ spatialP(0, 0, M(u))`, which does not depend on the prescriptions.
* **Continuity in the masses** (`tendsto_prodLimit`): `prodLimit` is continuous in the photon
  masses, on `M_j ≥ M₀ > 0`; repeated masses are therefore limits of distinct ones.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtLimit

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.Integration.Feynman

/-! ### Definitions -/

/-- The integrand with a product of `k + 2` photon denominators. -/
noncomputable def prodIntegrand (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ)
    (ε : ℝ) (p' p ℓ : Fin 4 → ℝ) : ℂ :=
  N ℓ * ((denom m ε (p' + ℓ) * denom m ε (p + ℓ))⁻¹ * ∏ j, (denom (Ms j) (es j) ℓ)⁻¹)

/-- `M(u)² = ∑_j u_j M_j²` at the barycentric point of `u`. -/
def mixMassSq {k : ℕ} (Ms : Fin (k + 2) → ℝ) (u : Fin (k + 1) → ℝ) : ℝ :=
  ∑ j, simplexPoint u j * Ms j ^ 2

/-- The mixed photon mass `M(u) = √(∑_j u_j M_j²)`. -/
noncomputable def mixMass {k : ℕ} (Ms : Fin (k + 2) → ℝ) (u : Fin (k + 1) → ℝ) : ℝ :=
  Real.sqrt (mixMassSq Ms u)

/-- The mixed prescription `ε(u) = ∑_j u_j ε_j`. -/
def mixEps {k : ℕ} (es : Fin (k + 2) → ℝ) (u : Fin (k + 1) → ℝ) : ℝ :=
  ∑ j, simplexPoint u j * es j

/-- The limit: `(k+1)! ∫_Δ ∫ spatialP(0, 0, M(u))`. -/
noncomputable def prodLimit (α : ℂ) (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) (p' p : Fin 4 → ℝ) : ℂ :=
  ((k + 1).factorial : ℂ) *
    ∫ u in simplexSet (k + 1), ∫ v, spatialP α N m (mixMass Ms u) (k + 1) 0 0 p' p v

/-! ### The mixed mass and prescription -/

instance isFiniteMeasure_restrict_simplexSet (m : ℕ) :
    IsFiniteMeasure (volume.restrict (simplexSet m) : Measure (Fin m → ℝ)) :=
  isFiniteMeasure_restrict.mpr (isCompact_simplexSet m).measure_lt_top.ne

theorem simplexPoint_eq_re {k : ℕ} (j : Fin (k + 1)) (u : Fin k → ℝ) :
    simplexPoint u j = (simplexComb (Pi.single j (1 : ℂ)) u).re := by
  rw [simplexComb_eq_sum_simplexPoint, Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · simp

theorem continuous_simplexPoint_apply {k : ℕ} (j : Fin (k + 1)) :
    Continuous fun u : Fin k → ℝ => simplexPoint u j := by
  simp_rw [simplexPoint_eq_re j]
  exact continuous_re.comp (continuous_simplexComb _)

theorem continuous_mixMassSq {k : ℕ} (Ms : Fin (k + 2) → ℝ) : Continuous (mixMassSq Ms) := by
  unfold mixMassSq
  exact continuous_finsetSum _ fun j _ => (continuous_simplexPoint_apply j).mul continuous_const

theorem continuous_mixMass {k : ℕ} (Ms : Fin (k + 2) → ℝ) : Continuous (mixMass Ms) :=
  (continuous_mixMassSq Ms).sqrt

theorem continuous_mixEps {k : ℕ} (es : Fin (k + 2) → ℝ) : Continuous (mixEps es) := by
  unfold mixEps
  exact continuous_finsetSum _ fun j _ => (continuous_simplexPoint_apply j).mul continuous_const

theorem mixEps_ge {k : ℕ} {es : Fin (k + 2) → ℝ} {e₀ : ℝ} (h : ∀ j, e₀ ≤ es j)
    {u : Fin (k + 1) → ℝ} (hu : u ∈ simplexSet (k + 1)) : e₀ ≤ mixEps es u := by
  obtain ⟨h0, h1⟩ := simplexPoint_mem_stdSimplex hu
  calc e₀ = ∑ j, simplexPoint u j * e₀ := by rw [← Finset.sum_mul, h1, one_mul]
    _ ≤ mixEps es u := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (h0 j)

theorem mixMassSq_nonneg {k : ℕ} (Ms : Fin (k + 2) → ℝ) {u : Fin (k + 1) → ℝ}
    (hu : u ∈ simplexSet (k + 1)) : 0 ≤ mixMassSq Ms u :=
  Finset.sum_nonneg fun j _ => mul_nonneg ((simplexPoint_mem_stdSimplex hu).1 j) (sq_nonneg _)

theorem mixMass_ge {k : ℕ} {Ms : Fin (k + 2) → ℝ} {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (h : ∀ j, M₀ ≤ Ms j) {u : Fin (k + 1) → ℝ} (hu : u ∈ simplexSet (k + 1)) :
    M₀ ≤ mixMass Ms u := by
  obtain ⟨h0, h1⟩ := simplexPoint_mem_stdSimplex hu
  refine Real.le_sqrt_of_sq_le ?_
  calc M₀ ^ 2 = ∑ j, simplexPoint u j * M₀ ^ 2 := by rw [← Finset.sum_mul, h1, one_mul]
    _ ≤ mixMassSq Ms u := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM₀ (h j) 2) (h0 j)

/-- On the simplex, the Feynman combination of the photon denominators is one photon denominator
with the mixed mass and the mixed prescription. -/
theorem simplexComb_denom {k : ℕ} (Ms es : Fin (k + 2) → ℝ) (ℓ : Fin 4 → ℝ)
    {u : Fin (k + 1) → ℝ} (hu : u ∈ simplexSet (k + 1)) :
    simplexComb (fun j => denom (Ms j) (es j) ℓ) u = denom (mixMass Ms u) (mixEps es u) ℓ := by
  obtain ⟨_, h1⟩ := simplexPoint_mem_stdSimplex hu
  have hsq : mixMass Ms u ^ 2 = mixMassSq Ms u := Real.sq_sqrt (mixMassSq_nonneg Ms hu)
  have h1' : ∑ j, (simplexPoint u j : ℂ) = 1 := by exact_mod_cast h1
  rw [simplexComb_eq_sum_simplexPoint]
  have hpt : ∀ j, (simplexPoint u j : ℂ) * denom (Ms j) (es j) ℓ =
      (simplexPoint u j : ℂ) * (Minkowski.dot ℓ ℓ : ℂ) +
        ((simplexPoint u j * Ms j ^ 2 : ℝ) : ℂ) - ((simplexPoint u j * es j : ℝ) : ℂ) * I :=
    fun j => by simp only [denom]; push_cast; ring
  rw [Finset.sum_congr rfl fun j _ => hpt j, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, h1', ← Finset.sum_mul]
  simp only [denom, hsq, mixMassSq, mixEps]
  push_cast
  ring

/-! ### Photon superposition -/

theorem prodIntegrand_eq_integral (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) (ε : ℝ)
    (p' p ℓ : Fin 4 → ℝ) :
    prodIntegrand N m Ms es ε p' p ℓ = ((k + 1).factorial : ℂ) *
      ∫ u in simplexSet (k + 1), powIntegrand N m (mixMass Ms u) (k + 1) ε (mixEps es u) p' p ℓ := by
  have ha : ∀ j, (denom (Ms j) (es j) ℓ).im < 0 := fun j => by rw [denom_im]; linarith [hes j]
  have hpt : ∀ u ∈ simplexSet (k + 1),
      powIntegrand N m (mixMass Ms u) (k + 1) ε (mixEps es u) p' p ℓ =
        N ℓ * (denom m ε (p' + ℓ) * denom m ε (p + ℓ))⁻¹ *
          (simplexComb (fun j => denom (Ms j) (es j) ℓ) u ^ (k + 1 + 1))⁻¹ := by
    intro u hu
    rw [powIntegrand, simplexComb_denom Ms es ℓ hu, mul_inv (denom m ε (p' + ℓ) *
      denom m ε (p + ℓ)), mul_assoc]
  rw [prodIntegrand, prod_inv_eq_factorial_mul_integral_simplex ha,
    setIntegral_congr_fun (measurableSet_simplexSet _) hpt, integral_const_mul]
  ring

/-! ### Exchange with the energy-first integral -/

theorem continuous_denom_joint {X : Type*} [TopologicalSpace X] {M e : X → ℝ}
    {ℓ : X → Fin 4 → ℝ} (hM : Continuous M) (he : Continuous e) (hℓ : Continuous ℓ) :
    Continuous fun x => denom (M x) (e x) (ℓ x) := by
  have := continuous_dot_comp hℓ hℓ
  unfold denom
  fun_prop

theorem measurable_powIntegrand_mix {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (m : ℝ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) (ε : ℝ) (p' p : Fin 4 → ℝ) :
    Measurable fun q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ =>
      powIntegrand N m (mixMass Ms q.1.2) (k + 1) ε (mixEps es q.1.2) p' p
        (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
  have hℓ : Continuous fun q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ =>
      (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd (continuous_fst.fst)
  have hA := (continuous_denom_joint continuous_const continuous_const
    (continuous_const.add hℓ) (M := fun _ => m) (e := fun _ => ε) (X := _)
    (ℓ := fun q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ => p' + Fin.cons q.2 q.1.1)).measurable
  have hB := (continuous_denom_joint continuous_const continuous_const
    (continuous_const.add hℓ) (M := fun _ => m) (e := fun _ => ε) (X := _)
    (ℓ := fun q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ => p + Fin.cons q.2 q.1.1)).measurable
  have hC := (continuous_denom_joint ((continuous_mixMass Ms).comp continuous_fst.snd)
    ((continuous_mixEps es).comp continuous_fst.snd) hℓ).measurable
  have hN := (hNc.comp hℓ).measurable
  unfold powIntegrand
  simp only [Function.comp_def] at hN hC
  fun_prop

theorem norm_denom_ge_eps (M e : ℝ) (ℓ : Fin 4 → ℝ) (he : 0 ≤ e) : e ≤ ‖denom M e ℓ‖ := by
  have := abs_im_le_norm (denom M e ℓ)
  rwa [denom_im, abs_neg, abs_of_nonneg he] at this

theorem denom_add_cons (m ε : ℝ) (K : Fin 4 → ℝ) (t : ℝ) (v : Fin 3 → ℝ) :
    denom m ε (K + (Fin.cons t v : Fin 4 → ℝ)) =
      -((t : ℂ) + K 0) ^ 2 + ((∑ j : Fin 3, (v j + K j.succ) ^ 2 + m ^ 2 : ℝ) : ℂ) - ε * I := by
  rw [denom, add_comm K, dot_cons_add]
  push_cast
  ring

/-- At fixed spatial momentum the integrand of `powIntegrand` is bounded by `G (1 + t²)⁻¹`,
uniformly in the photon mass and in photon prescriptions `≥ e₀ > 0`. -/
theorem exists_norm_powIntegrand_cons_le {N : (Fin 4 → ℝ) → ℂ} {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) (n : ℕ) {ε e₀ : ℝ} (hε : 0 < ε)
    (he₀ : 0 < e₀) (p' p : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    ∃ G : ℝ, ∀ M η : ℝ, e₀ ≤ η → ∀ t : ℝ,
      ‖powIntegrand N m M n ε η p' p (Fin.cons t v : Fin 4 → ℝ)‖ ≤ G * (1 + t ^ 2)⁻¹ := by
  have hCN0 := nonneg_of_norm_le hNb
  set W₁ : ℝ := ∑ j : Fin 3, (v j + p' j.succ) ^ 2 + m ^ 2
  set W₂ : ℝ := ∑ j : Fin 3, (v j + p j.succ) ^ 2 + m ^ 2
  obtain ⟨c, hc, hcb⟩ := exists_mul_one_add_sq_le_norm hε (|p' 0| + |p 0|) (max W₁ W₂)
  refine ⟨CN * (2 * (1 + ‖v‖) ^ 2) * ((c ^ 2)⁻¹ * (e₀ ^ (n + 1))⁻¹), fun M η hη t => ?_⟩
  have h1t : 0 < 1 + t ^ 2 := by positivity
  have hA : c * (1 + t ^ 2) ≤ ‖denom m ε (p' + (Fin.cons t v : Fin 4 → ℝ))‖ := by
    rw [denom_add_cons]
    exact hcb t _ _ (le_add_of_nonneg_right (abs_nonneg _)) (le_max_left _ _)
  have hB : c * (1 + t ^ 2) ≤ ‖denom m ε (p + (Fin.cons t v : Fin 4 → ℝ))‖ := by
    rw [denom_add_cons]
    exact hcb t _ _ (le_add_of_nonneg_left (abs_nonneg _)) (le_max_right _ _)
  have hC : e₀ ≤ ‖denom M η (Fin.cons t v : Fin 4 → ℝ)‖ :=
    hη.trans (norm_denom_ge_eps M η _ (he₀.le.trans hη))
  have hN := norm_cons_numerator_le hNb hCN0 t v
  have hpos : 0 < c * (1 + t ^ 2) := by positivity
  rw [powIntegrand, norm_mul, norm_inv, norm_mul, norm_mul, norm_pow]
  calc ‖N (Fin.cons t v : Fin 4 → ℝ)‖ *
        (‖denom m ε (p' + (Fin.cons t v : Fin 4 → ℝ))‖ *
          ‖denom m ε (p + (Fin.cons t v : Fin 4 → ℝ))‖ *
          ‖denom M η (Fin.cons t v : Fin 4 → ℝ)‖ ^ (n + 1))⁻¹
      ≤ (CN * (2 * (1 + ‖v‖) ^ 2) * (1 + t ^ 2)) *
        ((c * (1 + t ^ 2)) * (c * (1 + t ^ 2)) * e₀ ^ (n + 1))⁻¹ := by
        gcongr
    _ = CN * (2 * (1 + ‖v‖) ^ 2) * ((c ^ 2)⁻¹ * (e₀ ^ (n + 1))⁻¹) * (1 + t ^ 2)⁻¹ := by
        field_simp

theorem exists_pos_le_all {k : ℕ} {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) :
    ∃ e₀ > 0, ∀ j, e₀ ≤ es j :=
  ⟨Finset.univ.inf' Finset.univ_nonempty es,
    (Finset.lt_inf'_iff _).2 fun j _ => hes j, fun j => Finset.inf'_le _ (Finset.mem_univ j)⟩

/-- The integrand of `powIntegrand` at the mixed mass and prescription, as a function of
`((v, u), t)`. -/
noncomputable def mixIntegrand (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ)
    (ε : ℝ) (p' p : Fin 4 → ℝ) (q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ) : ℂ :=
  powIntegrand N m (mixMass Ms q.1.2) (k + 1) ε (mixEps es q.1.2) p' p
    (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)

/-- Step 1: energy × simplex at fixed spatial momentum. -/
theorem integrable_mixIntegrand_time {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) (p' p : Fin 4 → ℝ)
    (v : Fin 3 → ℝ) :
    Integrable (fun q : ℝ × (Fin (k + 1) → ℝ) => mixIntegrand N m Ms es ε p' p ((v, q.2), q.1))
      ((volume : Measure ℝ).prod (volume.restrict (simplexSet (k + 1)))) := by
  obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all hes
  obtain ⟨G, hG⟩ := exists_norm_powIntegrand_cons_le hNb m (k + 1) hε he₀ p' p v
  have hFm : Measurable (mixIntegrand N m Ms es ε p' p) :=
    measurable_powIntegrand_mix hNc m Ms es ε p' p
  have hc : Measurable fun q : ℝ × (Fin (k + 1) → ℝ) =>
      (((v, q.2), q.1) : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ) := by fun_prop
  refine Integrable.mono' (g := fun q : ℝ × (Fin (k + 1) → ℝ) => G * (1 + q.1 ^ 2)⁻¹ * 1)
    ((integrable_inv_one_add_sq.const_mul G).mul_prod (integrable_const (1 : ℝ)))
    (hFm.comp hc).aestronglyMeasurable ?_
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
    (ν := volume.restrict (simplexSet (k + 1)))).ae
    (ae_restrict_mem (measurableSet_simplexSet (k + 1)))
  filter_upwards [h2] with q hq
  rw [mul_one]
  exact hG _ _ (mixEps_ge hes₀ hq) q.1

theorem integral_time_prodIntegrand {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) (p' p : Fin 4 → ℝ)
    (v : Fin 3 → ℝ) :
    ∫ t : ℝ, prodIntegrand N m Ms es ε p' p (Fin.cons t v : Fin 4 → ℝ) =
      ((k + 1).factorial : ℂ) * ∫ u in simplexSet (k + 1),
        ∫ t : ℝ, mixIntegrand N m Ms es ε p' p ((v, u), t) := by
  simp_rw [prodIntegrand_eq_integral N m Ms hes ε p' p]
  rw [integral_const_mul]
  congr 1
  exact integral_integral_swap (integrable_mixIntegrand_time hNc hNb m Ms hes hε p' p v)

theorem integrable_time_prodIntegrand {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) (p' p : Fin 4 → ℝ)
    (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => prodIntegrand N m Ms es ε p' p (Fin.cons t v : Fin 4 → ℝ) := by
  refine ((integrable_mixIntegrand_time hNc hNb m Ms hes hε p' p v).integral_prod_left.const_mul
    ((k + 1).factorial : ℂ)).congr (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [prodIntegrand_eq_integral N m Ms hes ε p' p]
  rfl

/-- Step 2: space × simplex. -/
theorem integrable_mixIntegrand_space {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k : ℕ} {Ms es : Fin (k + 2) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : (Fin 3 → ℝ) × (Fin (k + 1) → ℝ) =>
        ∫ t : ℝ, mixIntegrand N m Ms es ε p' p (x, t))
      ((volume : Measure (Fin 3 → ℝ)).prod (volume.restrict (simplexSet (k + 1)))) := by
  obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all hes
  obtain ⟨C, _, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb (n := k + 1)
    (by omega)
  have hFm : StronglyMeasurable (mixIntegrand N m Ms es ε p' p) :=
    (measurable_powIntegrand_mix hNc m Ms es ε p' p).stronglyMeasurable
  have hGm : StronglyMeasurable fun x : (Fin 3 → ℝ) × (Fin (k + 1) → ℝ) =>
      ∫ t : ℝ, mixIntegrand N m Ms es ε p' p (x, t) :=
    hFm.integral_prod_right'
  have hb := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul (((k + 1 : ℕ) + 1) * ((k + 1 : ℕ) + 2) * C)
  refine Integrable.mono' (hb.mul_prod (integrable_const (1 : ℝ))) hGm.aestronglyMeasurable ?_
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin 3 → ℝ)))
    (ν := volume.restrict (simplexSet (k + 1)))).ae
    (ae_restrict_mem (measurableSet_simplexSet (k + 1)))
  filter_upwards [h2] with x hx
  rw [mul_one]
  have hs : ∫ t : ℝ, mixIntegrand N m Ms es ε p' p (x, t) =
      spatialP α N m (mixMass Ms x.2) (k + 1) ε (mixEps es x.2) p' p x.1 :=
    integral_time_powIntegrand hNc hNq hNb m (mixMass Ms x.2) (k + 1) (η := mixEps es x.2) hε
      (he₀.trans_le (mixEps_ge hes₀ hx)) p' p x.1
  rw [hs]
  exact norm_spatialP_le (fun z hz v => hC (mixMass Ms x.2) (mixMass_ge hM₀.le hMs hx) _ z hz v)
    x.1

/-- **Exchange of the photon superposition with the energy-first integral**, at fixed positive
prescriptions, with both stages of the energy-first integral of `prodIntegrand` integrable. -/
theorem energyFirstIntegral_prodIntegrand_eq {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k : ℕ} {Ms es : Fin (k + 2) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
        prodIntegrand N m Ms es ε p' p (Fin.cons t v : Fin 4 → ℝ)) ∧
      Integrable (fun v : Fin 3 → ℝ =>
        ∫ t : ℝ, prodIntegrand N m Ms es ε p' p (Fin.cons t v : Fin 4 → ℝ)) ∧
      energyFirstIntegral (prodIntegrand N m Ms es ε p' p) = ((k + 1).factorial : ℂ) *
        ∫ u in simplexSet (k + 1),
          energyFirstIntegral (powIntegrand N m (mixMass Ms u) (k + 1) ε (mixEps es u) p' p) := by
  have hint2 := integrable_mixIntegrand_space hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs hes hε
  have hstep1 := integral_time_prodIntegrand hNc hNb m Ms hes hε p' p
  refine ⟨integrable_time_prodIntegrand hNc hNb m Ms hes hε p' p, ?_, ?_⟩
  · exact (hint2.integral_prod_left.const_mul ((k + 1).factorial : ℂ)).congr
      (Eventually.of_forall fun v => (hstep1 v).symm)
  · rw [energyFirstIntegral]
    simp_rw [hstep1]
    rw [integral_const_mul, integral_integral_swap hint2]
    rfl

/-! ### The limit and its continuity in the masses -/

theorem continuous_mixMass_masses {k : ℕ} (u : Fin (k + 1) → ℝ) :
    Continuous fun Ms : Fin (k + 2) → ℝ => mixMass Ms u := by
  unfold mixMass mixMassSq
  fun_prop

theorem continuous_mixEps_eps {k : ℕ} (u : Fin (k + 1) → ℝ) :
    Continuous fun es : Fin (k + 2) → ℝ => mixEps es u := by
  unfold mixEps
  fun_prop

/-- The common bound on the spatial integrals: `‖∫ spatialP‖ ≤ ∫ (n+1)(n+2) C (1 + ‖v‖)⁻⁵`. -/
theorem norm_integral_spatialP_le {α : ℂ} {N : (Fin 4 → ℝ) → ℂ} {m M : ℝ} {n : ℕ} {ε η : ℝ}
    {p' p : Fin 4 → ℝ} {C : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖timeP α N m M n (effEps ε η z) p' p z v‖ ≤ C * (1 + ‖v‖) ^ (-(5 : ℝ))) :
    ‖∫ v, spatialP α N m M n ε η p' p v‖ ≤
      ∫ v : Fin 3 → ℝ, (n + 1) * (n + 2) * C * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  refine norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun v => norm_spatialP_le hC v)
  have h := (integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
    (by simp; norm_num)).const_mul ((n + 1) * (n + 2) * C)
  simpa only [mul_assoc] using h

theorem stronglyMeasurable_integral_spatialP_mix {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N)
    (α : ℂ) (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ) (ε η : ℝ) (p' p : Fin 4 → ℝ) :
    StronglyMeasurable fun u : Fin (k + 1) → ℝ =>
      ∫ v, spatialP α N m (mixMass Ms u) (k + 1) ε η p' p v := by
  have hf : Measurable fun q : ((Fin (k + 1) → ℝ) × (Fin 3 → ℝ)) × (ℝ × ℝ) =>
      feynWt (k + 1) q.2 * timeP α N m (mixMass Ms q.1.1) (k + 1) (effEps ε η q.2) p' p q.2 q.1.2 :=
    (measurable_timeP_mass hNc α m (k + 1) ε η p' p).comp
      ((((continuous_mixMass Ms).comp continuous_fst.fst).prodMk
        continuous_fst.snd).measurable.prodMk measurable_snd)
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := feynmanMeasure)).integral_prod_right'

/-- **The limit of the photon-product vertex**: when `ε → 0⁺` and every photon prescription
`ε_j → 0⁺`, the energy-first integral of `prodIntegrand` tends to `prodLimit`, which does not
depend on the prescriptions. -/
theorem tendsto_energyFirstIntegral_prodIntegrand {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k : ℕ} {Ms : Fin (k + 2) → ℝ}
    (hMs : ∀ j, M₀ ≤ Ms j) {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot]
    {ε : ι → ℝ} {es : ι → Fin (k + 2) → ℝ} (hε : Tendsto ε l (𝓝[>] 0))
    (hes : ∀ j, Tendsto (fun i => es i j) l (𝓝[>] 0)) :
    Tendsto (fun i => energyFirstIntegral (prodIntegrand N m Ms (es i) (ε i) p' p)) l
      (𝓝 (prodLimit α N m Ms p' p)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb (n := k + 1)
    (by omega)
  have hεpos : ∀ᶠ i in l, 0 < ε i := hε self_mem_nhdsWithin
  have hespos : ∀ᶠ i in l, ∀ j, 0 < es i j :=
    eventually_all.2 fun j => (hes j) self_mem_nhdsWithin
  set Δ := simplexSet (k + 1)
  set B : ℝ := ∫ v : Fin 3 → ℝ, ((k + 1 : ℕ) + 1) * ((k + 1 : ℕ) + 2) * C * (1 + ‖v‖) ^ (-(5 : ℝ))
  have hΔ : ∀ᵐ u ∂(volume.restrict Δ), u ∈ Δ := ae_restrict_mem (measurableSet_simplexSet _)
  have hes0 : Tendsto es l (𝓝 0) := tendsto_pi_nhds.2 fun j => (hes j).mono_right nhdsWithin_le_nhds
  have hlim : Tendsto (fun i => ∫ u in Δ,
      energyFirstIntegral (powIntegrand N m (mixMass Ms u) (k + 1) (ε i) (mixEps (es i) u) p' p))
      l (𝓝 (∫ u in Δ, ∫ v, spatialP α N m (mixMass Ms u) (k + 1) 0 0 p' p v)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_
      (integrable_const B) ?_
    · refine Eventually.of_forall fun i => ?_
      have h := ((measurable_powIntegrand_mix hNc m Ms (es i) (ε i) p' p).stronglyMeasurable
        |>.integral_prod_right' (ν := (volume : Measure ℝ))).integral_prod_left'
          (μ := (volume : Measure (Fin 3 → ℝ)))
      exact h.aestronglyMeasurable
    · filter_upwards [hεpos, hespos] with i h1 h2
      obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all h2
      filter_upwards [hΔ] with u hu
      rw [energyFirstIntegral_powIntegrand_eq hNc hNq hNb m _ _ h1
        (he₀.trans_le (mixEps_ge hes₀ hu)) p' p]
      exact norm_integral_spatialP_le
        (fun z hz v => hC (mixMass Ms u) (mixMass_ge hM₀.le hMs hu) _ z hz v)
    · filter_upwards [hΔ] with u hu
      have hη : Tendsto (fun i => mixEps (es i) u) l (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have := ((continuous_mixEps_eps u).tendsto 0).comp hes0
          simpa [mixEps, Function.comp_def] using this
        · filter_upwards [hespos] with i h2
          obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all h2
          exact he₀.trans_le (mixEps_ge hes₀ hu)
      exact tendsto_energyFirstIntegral_powIntegrand hm hM₀ hp' hp hp0' hp0 hNc hNq hNb
        (by omega) hε hη tendsto_const_nhds
        (Eventually.of_forall fun _ => mixMass_ge hM₀.le hMs hu)
  refine (hlim.const_mul ((k + 1).factorial : ℂ)).congr' ?_
  filter_upwards [hεpos, hespos] with i h1 h2
  exact (energyFirstIntegral_prodIntegrand_eq hm hM₀ hp' hp hp0' hp0 hNc hNq hNb hMs h2 h1).2.2.symm

/-- **Continuity of the limit in the photon masses**, on `M_j ≥ M₀ > 0`. -/
theorem tendsto_prodLimit {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (α : ℂ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {k : ℕ} {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [l.NeBot] {Ms : ι → Fin (k + 2) → ℝ} {Ms₀ : Fin (k + 2) → ℝ}
    (hMs : Tendsto Ms l (𝓝 Ms₀)) (hge : ∀ᶠ i in l, ∀ j, M₀ ≤ Ms i j) :
    Tendsto (fun i => prodLimit α N m (Ms i) p' p) l (𝓝 (prodLimit α N m Ms₀ p' p)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_timeP_le hm hM₀ hp' hp hp0' hp0 α hNb (n := k + 1)
    (by omega)
  set Δ := simplexSet (k + 1)
  set B : ℝ := ∫ v : Fin 3 → ℝ, ((k + 1 : ℕ) + 1) * ((k + 1 : ℕ) + 2) * C * (1 + ‖v‖) ^ (-(5 : ℝ))
  have hΔ : ∀ᵐ u ∂(volume.restrict Δ), u ∈ Δ := ae_restrict_mem (measurableSet_simplexSet _)
  refine Tendsto.const_mul _ ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_
    (integrable_const B) ?_
  · exact Eventually.of_forall fun i =>
      (stronglyMeasurable_integral_spatialP_mix hNc α m (Ms i) 0 0 p' p).aestronglyMeasurable
  · filter_upwards [hge] with i hi
    filter_upwards [hΔ] with u hu
    exact norm_integral_spatialP_le
      (fun z hz v => hC (mixMass (Ms i) u) (mixMass_ge hM₀.le hi hu) _ z hz v)
  · filter_upwards [hΔ] with u hu
    exact tendsto_integral_spatialP hm hM₀ hp' hp hp0' hp0 hNc α hNb (by omega)
      tendsto_const_nhds tendsto_const_nhds (Eventually.of_forall fun _ => le_rfl)
      (Eventually.of_forall fun _ => le_rfl)
      (((continuous_mixMass_masses u).tendsto Ms₀).comp hMs)
      (hge.mono fun i hi => mixMass_ge hM₀.le hi hu)

end QED.TwoLoop.VPHalfAtLimit

end
