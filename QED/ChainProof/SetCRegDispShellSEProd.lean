/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSEPow
public import QED.TwoLoop.VPHalfAtGenFubini
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform bounds for one-loop self-energies with several photon-type denominators

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step S4 of the plan. The building
block of `QED/ChainProof/SetCRegDispShellSEPow.lean` is extended to a product of `k + 2`
photon-type denominators with their own masses `M_j ≥ M₀` and prescriptions `ε_j > 0`:

`F(ℓ) = N(ℓ) / (D_m(P + ℓ; ε) ∏_j D_{M_j}(ℓ; ε_j))` (`seProd`).

* `GoodEF4 F C`: `F` is integrable in both stages of the energy-first integral and its energy
  integral is bounded by `C (1 + ‖v‖)⁻⁴` (the self-energy analogue of
  `QED.TwoLoop.VPHalfAtAssembly.GoodEF`, one power weaker); closed under sums and multiples.
* `seProd_eq_integral`: the photon superposition (as in
  `QED.TwoLoop.VPHalfAtLimit.prodIntegrand_eq_integral`).
* **`exists_goodEF4_seProd`**: below threshold, `seProd` is `GoodEF4` with one constant for all
  masses `≥ M₀`, all photon prescriptions and all electron prescriptions, when the numerator has
  degree `d ≤ 2k + 1` and is at most linear in the energy unless `k ≥ 1`.
* `seProd_mul_s`, `goodEF4_s1`, `goodEF4_s2`, `goodEF4_s3`: a factor `k²` is absorbed by the
  first photon denominator, `k²/D₀ = 1 - t₀/D₀`.
* **`efi_integral_eq_of_goodEF4`**: the energy-first integral commutes with an integral over a
  finite measure, for a jointly measurable family that is `GoodEF4` with one constant and has a
  pointwise bound `G(v) (1 + t²)⁻¹`, both for almost every parameter.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDispSE

open QED.OneLoop QED.Integration QED.Integration.Feynman QED.WickModel
open QED.TwoLoop.VPUnitNested (EFInt)
open QED.TwoLoop.VPHalfAtAssembly (PtBd)
open QED.TwoLoop.VPHalfAtLimit (mixMass mixEps mixMassSq mixEps_ge mixMass_ge mixMassSq_nonneg
  simplexComb_denom continuous_mixMass continuous_mixEps continuous_denom_joint
  denom_add_cons exists_pos_le_all norm_ofReal_sub_mul_I_mono nonneg_of_norm_le
  norm_cons_numerator_le massShift denom_eq_add_massShift denom_ne_zero_of_pos)
open QED.OneLoop.VertexLimit (continuous_dot_comp)

/-! ### The predicate -/

/-- `F` is integrable in both stages of the energy-first integral, and its energy integral is
bounded by `C (1 + ‖v‖)⁻⁴`. -/
def GoodEF4 (F : (Fin 4 → ℝ) → ℂ) (C : ℝ) : Prop :=
  EFInt F ∧ ∀ v : Fin 3 → ℝ, ‖∫ t : ℝ, F (Fin.cons t v : Fin 4 → ℝ)‖ ≤ C * (1 + ‖v‖) ^ (-(4 : ℝ))

theorem integrable_one_add_norm_four :
    Integrable fun v : Fin 3 → ℝ => (1 + ‖v‖) ^ (-(4 : ℝ)) :=
  integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 4) (by simp; norm_num)

namespace GoodEF4

variable {F G : (Fin 4 → ℝ) → ℂ} {C D : ℝ}

theorem congr (hF : GoodEF4 F C) (h : ∀ ℓ, F ℓ = G ℓ) : GoodEF4 G C := by
  have e : F = G := funext h
  exact e ▸ hF

theorem mono' (hF : GoodEF4 F C) (h : C ≤ D) : GoodEF4 F D :=
  ⟨hF.1, fun v => (hF.2 v).trans (by gcongr)⟩

theorem add (hF : GoodEF4 F C) (hG : GoodEF4 G D) :
    GoodEF4 (fun ℓ => F ℓ + G ℓ) (C + D) := by
  refine ⟨hF.1.add hG.1, fun v => ?_⟩
  rw [integral_add (hF.1.1 v) (hG.1.1 v)]
  refine (norm_add_le _ _).trans ?_
  have := hF.2 v
  have := hG.2 v
  linarith

theorem const_mul (hF : GoodEF4 F C) (c : ℂ) : GoodEF4 (fun ℓ => c * F ℓ) (‖c‖ * C) := by
  refine ⟨hF.1.const_mul c, fun v => ?_⟩
  rw [integral_const_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hF.2 v) (norm_nonneg _)

theorem sub (hF : GoodEF4 F C) (hG : GoodEF4 G D) : GoodEF4 (fun ℓ => F ℓ - G ℓ) (C + D) := by
  have h := hF.add (hG.const_mul (-1))
  simp only [norm_neg, norm_one, one_mul] at h
  exact h.congr fun ℓ => by ring

theorem nonneg_const (hF : GoodEF4 F C) : 0 ≤ C := by
  have h := (norm_nonneg _).trans (hF.2 0)
  simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at h
  exact h

theorem norm_efi_le (hF : GoodEF4 F C) :
    ‖energyFirstIntegral F‖ ≤ C * ∫ v : Fin 3 → ℝ, (1 + ‖v‖) ^ (-(4 : ℝ)) := by
  unfold energyFirstIntegral
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  exact integral_mono hF.1.2.norm (integrable_one_add_norm_four.const_mul C) hF.2

end GoodEF4

/-! ### The photon product -/

/-- The self-energy with `k + 2` photon-type denominators. -/
noncomputable def seProd (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ)
    (ε : ℝ) (P ℓ : Fin 4 → ℝ) : ℂ :=
  N ℓ * ((denom m ε (P + ℓ))⁻¹ * ∏ j, (denom (Ms j) (es j) ℓ)⁻¹)

theorem seProd_eq_integral (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) (ε : ℝ)
    (P ℓ : Fin 4 → ℝ) :
    seProd N m Ms es ε P ℓ = ((k + 1).factorial : ℂ) *
      ∫ u in simplexSet (k + 1), sePow N m (mixMass Ms u) (k + 1) ε (mixEps es u) P ℓ := by
  have ha : ∀ j, (denom (Ms j) (es j) ℓ).im < 0 := fun j => by rw [denom_im]; linarith [hes j]
  have hpt : ∀ u ∈ simplexSet (k + 1),
      sePow N m (mixMass Ms u) (k + 1) ε (mixEps es u) P ℓ =
        N ℓ * (denom m ε (P + ℓ))⁻¹ *
          (simplexComb (fun j => denom (Ms j) (es j) ℓ) u ^ (k + 1 + 1))⁻¹ := by
    intro u hu
    rw [sePow, simplexComb_denom Ms es ℓ hu, mul_inv (denom m ε (P + ℓ)), mul_assoc]
  rw [seProd, prod_inv_eq_factorial_mul_integral_simplex ha,
    setIntegral_congr_fun (measurableSet_simplexSet _) hpt, integral_const_mul]
  ring

theorem measurable_sePow_mix {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (m : ℝ) {k : ℕ}
    (Ms es : Fin (k + 2) → ℝ) (ε : ℝ) (P : Fin 4 → ℝ) :
    Measurable fun q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ =>
      sePow N m (mixMass Ms q.1.2) (k + 1) ε (mixEps es q.1.2) P
        (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) := by
  have hℓ : Continuous fun q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ =>
      (Fin.cons q.2 q.1.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd (continuous_fst.fst)
  have hA := (continuous_denom_joint continuous_const continuous_const
    (continuous_const.add hℓ) (M := fun _ => m) (e := fun _ => ε) (X := _)
    (ℓ := fun q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ => P + Fin.cons q.2 q.1.1)).measurable
  have hC := (continuous_denom_joint ((continuous_mixMass Ms).comp continuous_fst.snd)
    ((continuous_mixEps es).comp continuous_fst.snd) hℓ).measurable
  have hN := (hNc.comp hℓ).measurable
  unfold sePow
  simp only [Function.comp_def] at hN hC
  fun_prop

theorem denom_cons_eq (M e t : ℝ) (v : Fin 3 → ℝ) :
    denom M e (Fin.cons t v : Fin 4 → ℝ) =
      -((t : ℂ) + (0 : ℝ)) ^ 2 + ((∑ j : Fin 3, (v j + 0) ^ 2 + M ^ 2 : ℝ) : ℂ) - e * I := by
  have h := denom_add_cons M e 0 t v
  simp only [zero_add, Pi.zero_apply] at h
  rw [h]

theorem mixMassSq_le {k : ℕ} (Ms : Fin (k + 2) → ℝ) {u : Fin (k + 1) → ℝ}
    (hu : u ∈ simplexSet (k + 1)) : mixMassSq Ms u ≤ ∑ j, Ms j ^ 2 := by
  obtain ⟨h0, h1⟩ := simplexPoint_mem_stdSimplex hu
  have hle : ∀ j, simplexPoint u j ≤ 1 := fun j => by
    rw [← h1]
    exact Finset.single_le_sum (f := fun i => simplexPoint u i) (fun i _ => h0 i)
      (Finset.mem_univ j)
  unfold mixMassSq
  exact Finset.sum_le_sum fun j _ =>
    mul_le_of_le_one_left (sq_nonneg _) (hle j)

/-- At fixed spatial momentum the building block at the mixed mass and prescription is bounded
by `G (1 + t²)⁻¹`, uniformly on the simplex. -/
theorem exists_norm_sePow_mix_le {N : (Fin 4 → ℝ) → ℂ} {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ)
    {ε e₀ : ℝ} (hε : 0 < ε) (he₀ : 0 < e₀) (hes : ∀ j, e₀ ≤ es j) (P : Fin 4 → ℝ)
    (v : Fin 3 → ℝ) :
    ∃ G : ℝ, ∀ u ∈ simplexSet (k + 1), ∀ t : ℝ,
      ‖sePow N m (mixMass Ms u) (k + 1) ε (mixEps es u) P (Fin.cons t v : Fin 4 → ℝ)‖ ≤
        G * (1 + t ^ 2)⁻¹ := by
  have hCN0 := nonneg_of_norm_le hNb
  set ε₀ := min ε e₀
  have hε₀ : 0 < ε₀ := lt_min hε he₀
  set W₁ : ℝ := ∑ j : Fin 3, (v j + P j.succ) ^ 2 + m ^ 2
  set W₂ : ℝ := ∑ j : Fin 3, (v j + 0) ^ 2 + ∑ j, Ms j ^ 2
  obtain ⟨c, hc, hcb⟩ := exists_mul_one_add_sq_le_norm hε₀ |P 0| (max W₁ W₂)
  refine ⟨CN * (2 * (1 + ‖v‖) ^ 2) * (c ^ (k + 3))⁻¹, fun u hu t => ?_⟩
  have h1t : 0 < 1 + t ^ 2 := by positivity
  have hpos : 0 < c * (1 + t ^ 2) := by positivity
  have hmono : ∀ (X : ℝ) (a : ℝ), ε₀ ≤ a →
      ‖(X : ℂ) - ε₀ * I‖ ≤ ‖(X : ℂ) - a * I‖ := fun X a ha =>
    norm_ofReal_sub_mul_I_mono hε₀.le ha
  have hA : c * (1 + t ^ 2) ≤ ‖denom m ε (P + (Fin.cons t v : Fin 4 → ℝ))‖ := by
    rw [denom_add_cons]
    refine (hcb t _ _ le_rfl (le_max_left _ _)).trans ?_
    have e : ∀ a : ℝ, -((t : ℂ) + P 0) ^ 2 + ((W₁ : ℝ) : ℂ) - a * I =
        ((-(t + P 0) ^ 2 + W₁ : ℝ) : ℂ) - a * I := fun a => by push_cast; ring
    rw [e, e]
    exact hmono _ _ (min_le_left _ _)
  have hC : c * (1 + t ^ 2) ≤
      ‖denom (mixMass Ms u) (mixEps es u) (Fin.cons t v : Fin 4 → ℝ)‖ := by
    rw [denom_cons_eq]
    have hsq : mixMass Ms u ^ 2 = mixMassSq Ms u := Real.sq_sqrt (mixMassSq_nonneg Ms hu)
    have hW : ∑ j : Fin 3, (v j + 0) ^ 2 + mixMass Ms u ^ 2 ≤ max W₁ W₂ := by
      rw [hsq]
      exact le_max_of_le_right (by simp only [W₂]; linarith [mixMassSq_le Ms hu])
    refine (hcb t 0 _ (by simp) hW).trans ?_
    have e : ∀ a : ℝ, -((t : ℂ) + ((0 : ℝ) : ℂ)) ^ 2 +
        ((∑ j : Fin 3, (v j + 0) ^ 2 + mixMass Ms u ^ 2 : ℝ) : ℂ) - a * I =
        ((-(t + 0) ^ 2 + (∑ j : Fin 3, (v j + 0) ^ 2 + mixMass Ms u ^ 2) : ℝ) : ℂ) - a * I :=
      fun a => by push_cast; ring
    rw [e, e]
    exact hmono _ _ ((min_le_right _ _).trans (mixEps_ge hes hu))
  have hN := norm_cons_numerator_le hNb hCN0 t v
  rw [sePow, norm_mul, norm_inv, norm_mul, norm_pow]
  calc ‖N (Fin.cons t v : Fin 4 → ℝ)‖ *
        (‖denom m ε (P + (Fin.cons t v : Fin 4 → ℝ))‖ *
          ‖denom (mixMass Ms u) (mixEps es u) (Fin.cons t v : Fin 4 → ℝ)‖ ^ (k + 1 + 1))⁻¹
      ≤ (CN * (2 * (1 + ‖v‖) ^ 2) * (1 + t ^ 2)) *
        ((c * (1 + t ^ 2)) * (c * (1 + t ^ 2)) ^ (k + 1 + 1))⁻¹ := by
        gcongr
    _ = CN * (2 * (1 + ‖v‖) ^ 2) * (c ^ (k + 3))⁻¹ * ((1 + t ^ 2) ^ (k + 2))⁻¹ := by
        rw [show (c * (1 + t ^ 2)) * (c * (1 + t ^ 2)) ^ (k + 1 + 1) =
          c ^ (k + 3) * (1 + t ^ 2) ^ (k + 3) by rw [mul_pow]; ring]
        field_simp
        ring
    _ ≤ CN * (2 * (1 + ‖v‖) ^ 2) * (c ^ (k + 3))⁻¹ * (1 + t ^ 2)⁻¹ := by
        gcongr
        exact le_self_pow₀ (le_add_of_nonneg_right (sq_nonneg t)) (by omega)

/-- The building block at the mixed mass and prescription, as a function of `((v, u), t)`. -/
noncomputable def seMix (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 2) → ℝ)
    (ε : ℝ) (P : Fin 4 → ℝ) (q : ((Fin 3 → ℝ) × (Fin (k + 1) → ℝ)) × ℝ) : ℂ :=
  sePow N m (mixMass Ms q.1.2) (k + 1) ε (mixEps es q.1.2) P (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)

theorem integrable_seMix_time {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) (P : Fin 4 → ℝ)
    (v : Fin 3 → ℝ) :
    Integrable (fun q : ℝ × (Fin (k + 1) → ℝ) => seMix N m Ms es ε P ((v, q.2), q.1))
      ((volume : Measure ℝ).prod (volume.restrict (simplexSet (k + 1)))) := by
  obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all hes
  obtain ⟨G, hG⟩ := exists_norm_sePow_mix_le hNb m Ms es hε he₀ hes₀ P v
  have hFm : Measurable (seMix N m Ms es ε P) := measurable_sePow_mix hNc m Ms es ε P
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
  exact hG _ hq q.1

theorem integral_time_seProd {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) (P : Fin 4 → ℝ)
    (v : Fin 3 → ℝ) :
    ∫ t : ℝ, seProd N m Ms es ε P (Fin.cons t v : Fin 4 → ℝ) =
      ((k + 1).factorial : ℂ) * ∫ u in simplexSet (k + 1),
        ∫ t : ℝ, seMix N m Ms es ε P ((v, u), t) := by
  simp_rw [seProd_eq_integral N m Ms hes ε P]
  rw [integral_const_mul]
  congr 1
  exact integral_integral_swap (integrable_seMix_time hNc hNb m Ms hes hε P v)

theorem integrable_time_seProd {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {CN : ℝ}
    (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) (m : ℝ) {k : ℕ} (Ms : Fin (k + 2) → ℝ)
    {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) {ε : ℝ} (hε : 0 < ε) (P : Fin 4 → ℝ)
    (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => seProd N m Ms es ε P (Fin.cons t v : Fin 4 → ℝ) := by
  refine ((integrable_seMix_time hNc hNb m Ms hes hε P v).integral_prod_left.const_mul
    ((k + 1).factorial : ℂ)).congr (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [seProd_eq_integral N m Ms hes ε P]
  rfl

theorem continuous_seProd_cons {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) (m : ℝ) {k : ℕ}
    (Ms : Fin (k + 2) → ℝ) {es : Fin (k + 2) → ℝ} (hes : ∀ j, 0 < es j) {ε : ℝ}
    (hε : 0 < ε) (P : Fin 4 → ℝ) :
    Continuous fun q : (Fin 3 → ℝ) × ℝ =>
      seProd N m Ms es ε P (Fin.cons q.2 q.1 : Fin 4 → ℝ) := by
  have hℓ : Continuous fun q : (Fin 3 → ℝ) × ℝ => (Fin.cons q.2 q.1 : Fin 4 → ℝ) :=
    Continuous.finCons (A := fun _ : Fin 4 => ℝ) continuous_snd continuous_fst
  unfold seProd
  refine (hNc.comp hℓ).mul (Continuous.mul ?_ ?_)
  · exact (continuous_denom_joint continuous_const continuous_const
      (continuous_const.add hℓ)).inv₀ fun q => denom_ne_zero_of_pos hε _
  · exact continuous_finsetProd _ fun j _ => (continuous_denom_joint continuous_const
      continuous_const hℓ).inv₀ fun q => denom_ne_zero_of_pos (hes j) _

/-- **The photon product is `GoodEF4` uniformly**: below threshold, one constant for all photon
masses `≥ M₀`, all photon prescriptions and all electron prescriptions. -/
theorem exists_goodEF4_seProd {m M₀ c₀ : ℝ} (hM₀ : 0 ≤ M₀) (hc₀ : 0 < c₀) {P : Fin 4 → ℝ}
    (hP : ∀ y ∈ Icc (0 : ℝ) 1, c₀ ≤ selfEnergyFeynmanMass m M₀ (Minkowski.dot P P) y)
    {N : (Fin 4 → ℝ) → ℂ} (hNc : Continuous N) {α : ℂ}
    (hNq : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      N (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ)
    {CN : ℝ} (hNb : ∀ ℓ, ‖N ℓ‖ ≤ CN * (1 + ‖ℓ‖) ^ 2) {d : ℕ} {CN' : ℝ}
    (hNd : ∀ ℓ, ‖N ℓ‖ ≤ CN' * (1 + ‖ℓ‖) ^ d) (k : ℕ) (hd : d ≤ 2 * k + 1)
    (hα : α = 0 ∨ 1 ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Ms es : Fin (k + 2) → ℝ, (∀ j, M₀ ≤ Ms j) → (∀ j, 0 < es j) →
      ∀ ε : ℝ, 0 < ε → GoodEF4 (seProd N m Ms es ε P) K := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_seTime_le hM₀ hc₀ hP α hNd (n := k + 1) (by omega)
    (by rcases hα with h | h; exacts [Or.inl h, Or.inr (by omega)])
  set Δ := simplexSet (k + 1)
  set B : ℝ := (((k + 1 : ℕ) : ℝ) + 1) * C
  have hB0 : 0 ≤ B := by positivity
  set K : ℝ := ((k + 1).factorial : ℝ) * (B * (volume : Measure (Fin (k + 1) → ℝ)).real Δ)
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, fun Ms es hMs hes ε hε => ?_⟩
  obtain ⟨e₀, he₀, hes₀⟩ := exists_pos_le_all hes
  have hbd : ∀ v : Fin 3 → ℝ,
      ‖∫ t : ℝ, seProd N m Ms es ε P (Fin.cons t v : Fin 4 → ℝ)‖ ≤
        K * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
    intro v
    rw [integral_time_seProd hNc hNb m Ms hes hε P v, norm_mul, Complex.norm_natCast]
    have hΔ : ∀ᵐ u ∂(volume.restrict Δ), u ∈ Δ := ae_restrict_mem (measurableSet_simplexSet _)
    have hb : ∀ᵐ u ∂(volume.restrict Δ),
        ‖∫ t : ℝ, seMix N m Ms es ε P ((v, u), t)‖ ≤ B * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
      filter_upwards [hΔ] with u hu
      have hs : ∫ t : ℝ, seMix N m Ms es ε P ((v, u), t) =
          seSpatial α N m (mixMass Ms u) (k + 1) ε (mixEps es u) P v :=
        integral_time_sePow hNc hNq hNb m (mixMass Ms u) (k + 1) (η := mixEps es u) hε
          (he₀.trans_le (mixEps_ge hes₀ hu)) P v
      rw [hs]
      refine (norm_seSpatial_le (fun y hy w => hC (mixMass Ms u) (mixMass_ge hM₀ hMs hu) _ y
        hy w) v).trans (le_of_eq ?_)
      simp only [B]
    have h := norm_integral_le_of_norm_le_const hb
    rw [Measure.real, Measure.restrict_apply_univ] at h
    calc ((k + 1).factorial : ℝ) * ‖∫ u in Δ, ∫ t : ℝ, seMix N m Ms es ε P ((v, u), t)‖
        ≤ ((k + 1).factorial : ℝ) * (B * (1 + ‖v‖) ^ (-(4 : ℝ)) * (volume Δ).toReal) := by
          gcongr
      _ = K * (1 + ‖v‖) ^ (-(4 : ℝ)) := by
          simp only [K, Measure.real]; ring
  refine ⟨⟨fun v => integrable_time_seProd hNc hNb m Ms hes hε P v, ?_⟩, hbd⟩
  have hm : StronglyMeasurable fun v : Fin 3 → ℝ =>
      ∫ t : ℝ, seProd N m Ms es ε P (Fin.cons t v : Fin 4 → ℝ) :=
    (continuous_seProd_cons hNc m Ms hes hε P).stronglyMeasurable.integral_prod_right'
  exact (integrable_one_add_norm_four.const_mul K).mono' hm.aestronglyMeasurable
    (Eventually.of_forall hbd)

/-! ### Absorbing `k²` into a photon denominator -/

/-- `k² · seProd(Ms) = seProd(tail Ms) - t₀ seProd(Ms)`, with `t₀ = M₀² - i ε₀`. -/
theorem seProd_mul_s (N : (Fin 4 → ℝ) → ℂ) (m : ℝ) {k : ℕ} (Ms es : Fin (k + 3) → ℝ)
    (hes0 : 0 < es 0) (ε : ℝ) (P ℓ : Fin 4 → ℝ) :
    ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) * seProd N m Ms es ε P ℓ =
      seProd N m (Fin.tail Ms) (Fin.tail es) ε P ℓ -
        massShift (Ms 0) (es 0) * seProd N m Ms es ε P ℓ := by
  have h0 := denom_ne_zero_of_pos (M := Ms 0) hes0 ℓ
  have e0 := denom_eq_add_massShift (Ms 0) (es 0) ℓ
  simp only [seProd]
  rw [Fin.prod_univ_succ]
  simp only [Fin.tail]
  have hs : ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) = denom (Ms 0) (es 0) ℓ - massShift (Ms 0) (es 0) := by
    rw [e0]; ring
  rw [hs]
  field_simp

section Absorb

variable {N : (Fin 4 → ℝ) → ℂ} {m ε K T : ℝ} {P : Fin 4 → ℝ}

/-- One factor `k²`. -/
theorem goodEF4_s1 {k : ℕ} (Ms es : Fin (k + 3) → ℝ) (hes0 : 0 < es 0)
    (hT : ‖massShift (Ms 0) (es 0)‖ ≤ T)
    (h1 : GoodEF4 (seProd N m (Fin.tail Ms) (Fin.tail es) ε P) K)
    (h2 : GoodEF4 (seProd N m Ms es ε P) K) :
    GoodEF4 (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) * seProd N m Ms es ε P ℓ) ((1 + T) * K) := by
  have hK := h2.nonneg_const
  have h := h1.sub (h2.const_mul (massShift (Ms 0) (es 0)))
  refine (h.congr fun ℓ => (seProd_mul_s N m Ms es hes0 ε P ℓ).symm).mono' ?_
  nlinarith

/-- Two factors `k²`. -/
theorem goodEF4_s2 {k : ℕ} (Ms es : Fin (k + 4) → ℝ) (hes0 : 0 < es 0) (hes1 : 0 < es 1)
    (hT0 : 0 ≤ T) (hT : ‖massShift (Ms 0) (es 0)‖ ≤ T)
    (hT' : ‖massShift (Ms 1) (es 1)‖ ≤ T)
    (h1 : GoodEF4 (seProd N m (Fin.tail (Fin.tail Ms)) (Fin.tail (Fin.tail es)) ε P) K)
    (h2 : GoodEF4 (seProd N m (Fin.tail Ms) (Fin.tail es) ε P) K)
    (h3 : GoodEF4 (seProd N m Ms es ε P) K) :
    GoodEF4 (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ 2 * seProd N m Ms es ε P ℓ)
      ((1 + T) ^ 2 * K) := by
  have hK := h3.nonneg_const
  have a1 := goodEF4_s1 (k := k) (Fin.tail Ms) (Fin.tail es) hes1 hT' h1 h2
  have a2 := goodEF4_s1 (k := k + 1) Ms es hes0 hT h2 h3
  have h := a1.sub (a2.const_mul (massShift (Ms 0) (es 0)))
  refine (h.congr fun ℓ => ?_).mono' ?_
  · linear_combination (-((Minkowski.dot ℓ ℓ : ℝ) : ℂ)) *
      seProd_mul_s N m Ms es hes0 ε P ℓ
  · have := mul_le_mul_of_nonneg_right hT (by positivity : 0 ≤ (1 + T) * K)
    nlinarith

/-- Three factors `k²`. -/
theorem goodEF4_s3 {k : ℕ} (Ms es : Fin (k + 5) → ℝ) (hes0 : 0 < es 0) (hes1 : 0 < es 1)
    (hes2 : 0 < es 2) (hT0 : 0 ≤ T) (hT : ‖massShift (Ms 0) (es 0)‖ ≤ T)
    (hT' : ‖massShift (Ms 1) (es 1)‖ ≤ T) (hT'' : ‖massShift (Ms 2) (es 2)‖ ≤ T)
    (h1 : GoodEF4 (seProd N m (Fin.tail (Fin.tail (Fin.tail Ms)))
      (Fin.tail (Fin.tail (Fin.tail es))) ε P) K)
    (h2 : GoodEF4 (seProd N m (Fin.tail (Fin.tail Ms)) (Fin.tail (Fin.tail es)) ε P) K)
    (h3 : GoodEF4 (seProd N m (Fin.tail Ms) (Fin.tail es) ε P) K)
    (h4 : GoodEF4 (seProd N m Ms es ε P) K) :
    GoodEF4 (fun ℓ => ((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ 3 * seProd N m Ms es ε P ℓ)
      ((1 + T) ^ 3 * K) := by
  have hK := h4.nonneg_const
  have a1 := goodEF4_s2 (k := k) (Fin.tail Ms) (Fin.tail es) hes1 hes2 hT0 hT' hT'' h1 h2 h3
  have a2 := goodEF4_s2 (k := k + 1) Ms es hes0 hes1 hT0 hT hT' h2 h3 h4
  have h := a1.sub (a2.const_mul (massShift (Ms 0) (es 0)))
  refine (h.congr fun ℓ => ?_).mono' ?_
  · linear_combination (-((Minkowski.dot ℓ ℓ : ℝ) : ℂ) ^ 2) *
      seProd_mul_s N m Ms es hes0 ε P ℓ
  · have := mul_le_mul_of_nonneg_right hT (by positivity : 0 ≤ (1 + T) ^ 2 * K)
    nlinarith

end Absorb

/-! ### Exchange with an integral over parameters -/

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- **The exchange of the energy-first integral with an integral over parameters**, for a jointly
measurable family that is `GoodEF4` with one constant and has a pointwise bound `G(v)(1+t²)⁻¹`,
both for almost every parameter. -/
theorem efi_integral_eq_of_goodEF4 [IsFiniteMeasure ν] (g : X → (Fin 4 → ℝ) → ℂ)
    (hgm : Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ => g q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ))
    {C : ℝ} {G : (Fin 3 → ℝ) → ℝ} (hg : ∀ᵐ x ∂ν, GoodEF4 (g x) C)
    (hpt : ∀ᵐ x ∂ν, PtBd (g x) G) :
    EFInt (fun ℓ => ∫ x, g x ℓ ∂ν) ∧
      energyFirstIntegral (fun ℓ => ∫ x, g x ℓ ∂ν) = ∫ x, energyFirstIntegral (g x) ∂ν := by
  refine QED.TwoLoop.VPHalfAtGen.efi_integral_swap g (fun v => ?_) ?_
  · have hm : Measurable fun q : ℝ × X => g q.2 (Fin.cons q.1 v : Fin 4 → ℝ) :=
      hgm.comp (by fun_prop : Measurable fun q : ℝ × X => (((v, q.2), q.1) :
        ((Fin 3 → ℝ) × X) × ℝ))
    refine Integrable.mono' (g := fun q : ℝ × X => G v * (1 + q.1 ^ 2)⁻¹ * 1)
      ((integrable_inv_one_add_sq.const_mul (G v)).mul_prod (integrable_const (1 : ℝ)))
      hm.aestronglyMeasurable ?_
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := ν)).ae hpt
    filter_upwards [h2] with q hq
    rw [mul_one]
    exact hq v q.1
  · have hm : StronglyMeasurable fun q : (Fin 3 → ℝ) × X =>
        ∫ t : ℝ, g q.2 (Fin.cons t q.1 : Fin 4 → ℝ) :=
      hgm.stronglyMeasurable.integral_prod_right'
    refine Integrable.mono' (g := fun q : (Fin 3 → ℝ) × X => C * (1 + ‖q.1‖) ^ (-(4 : ℝ)) * 1)
      ((integrable_one_add_norm_four.const_mul C).mul_prod (integrable_const (1 : ℝ)))
      hm.aestronglyMeasurable ?_
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin 3 → ℝ)))
      (ν := ν)).ae hg
    filter_upwards [h2] with q hq
    rw [mul_one]
    exact hq.2 q.1

end QED.ChainProof.SetCRegDispSE

end
