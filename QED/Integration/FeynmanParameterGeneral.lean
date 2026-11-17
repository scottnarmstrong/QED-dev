/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import QED.Integration.FeynmanParameter
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Feynman parameters for `n` complex factors

The general Feynman formula (AKN (32); `docs/TWO-LOOP-DERIVATION.md`, section 4.4, obligation
O2-10): for `n = m + 1` complex numbers `a₀, …, aₘ` in the open lower half plane,
`∏ᵢ aᵢ⁻¹ = m! ∫_{Δₘ} (∑ᵢ xᵢ aᵢ)^{-(m+1)} dx`.

## The integration domain

The simplex is parametrized by its first `m` coordinates: `Δₘ = simplexSet m` is the set of
`x : Fin m → ℝ` with `xᵢ ≥ 0` and `∑ᵢ xᵢ ≤ 1`, and the last barycentric coordinate is
`xₘ = 1 - ∑ᵢ xᵢ`. The measure is Lebesgue measure `volume` on `Fin m → ℝ` restricted to
`Δₘ` (`simplexMeasure m`); it has total mass `1/m!`, so `m! dx` is the probability measure of
the flat simplex. The combined denominator is
`simplexComb a x = ∑_{i<m} xᵢ a_i + (1 - ∑ᵢ xᵢ) aₘ`, which is `∑ᵢ zᵢ aᵢ` for the barycentric
point `z = simplexPoint x = (x, 1 - ∑ᵢ xᵢ)` (`simplexComb_eq_sum_simplexPoint`).

For `m = 2` the one-loop file `QED/Integration/FeynmanParameter.lean` uses the unit square with
the weight `2y` instead; the two are related by `x₁ = yx`, `x₂ = y(1-x)`.

## Proof

Induction on `m`. Peel off the last coordinate `t = xₘ₋₁` of `x ∈ Δₘ` (Fubini via
`MeasurableEquiv.piFinSuccAbove`), rescale the remaining coordinates by `1 - t` (Jacobian
`(1-t)^{m-1}`), which turns the combination into `t aₘ₋₁ + (1-t) L` with `L` the combination
of the other `m` factors over `Δₘ₋₁`, swap the order of integration, and integrate in `t` by the
one-variable identity `∫₀¹ (1-t)^m (t c + (1-t) L)^{-(m+2)} dt = 1/((m+1) c L^{m+1})`
(`integral_one_sub_pow_mul_inv_pow`), proved by the fundamental theorem of calculus with no case
split on `c = L`.

## Main statements

* `QED.Integration.Feynman.simplexComb_im_neg`: on the simplex the combination lies in the open
  lower half plane (indeed `Im ≤ maxᵢ Im aᵢ`).
* `QED.Integration.Feynman.integrableOn_simplex_inv_pow`: `(simplexComb a x)^{-k}` is integrable
  on the simplex for every `k`.
* `QED.Integration.Feynman.integral_one_sub_pow_mul_inv_pow`: the one-variable identity.
* `QED.Integration.Feynman.prod_inv_eq_factorial_mul_integral_simplex`: the Feynman formula
  `∏ᵢ aᵢ⁻¹ = m! ∫_{Δₘ} (simplexComb a x)^{-(m+1)} dx`.
-/

public section

open MeasureTheory Set

namespace QED.Integration.Feynman

/-! ### The simplex -/

/-- The standard `m`-simplex in its first `m` coordinates: `xᵢ ≥ 0` and `∑ᵢ xᵢ ≤ 1`. -/
def simplexSet (m : ℕ) : Set (Fin m → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- The measure `dx` on the simplex: Lebesgue measure on `Fin m → ℝ` restricted to
`simplexSet m`. -/
noncomputable def simplexMeasure (m : ℕ) : Measure (Fin m → ℝ) :=
  volume.restrict (simplexSet m)

/-- The barycentric point `(x, 1 - ∑ᵢ xᵢ)` of `x ∈ simplexSet m`. -/
def simplexPoint {m : ℕ} (x : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.snoc x (1 - ∑ i, x i)

/-- The combined Feynman denominator `∑_{i<m} xᵢ aᵢ + (1 - ∑ᵢ xᵢ) aₘ`. -/
noncomputable def simplexComb {m : ℕ} (a : Fin (m + 1) → ℂ) (x : Fin m → ℝ) : ℂ :=
  ∑ i, (x i : ℂ) * a i.castSucc + (1 - ∑ i, (x i : ℂ)) * a (Fin.last m)

theorem simplexComb_eq_sum_simplexPoint {m : ℕ} (a : Fin (m + 1) → ℂ) (x : Fin m → ℝ) :
    simplexComb a x = ∑ i, (simplexPoint x i : ℂ) * a i := by
  simp [simplexComb, simplexPoint, Fin.sum_univ_castSucc]

theorem simplexPoint_mem_stdSimplex {m : ℕ} {x : Fin m → ℝ} (hx : x ∈ simplexSet m) :
    (∀ i, 0 ≤ simplexPoint x i) ∧ ∑ i, simplexPoint x i = 1 := by
  refine ⟨fun i => ?_, ?_⟩
  · induction i using Fin.lastCases with
    | last => simpa [simplexPoint] using hx.2
    | cast i => simpa [simplexPoint] using hx.1 i
  · simp [simplexPoint, Fin.sum_univ_castSucc]

theorem isClosed_simplexSet (m : ℕ) : IsClosed (simplexSet m) := by
  have h1 : IsClosed {x : Fin m → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact h1.inter (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i)
    continuous_const)

theorem measurableSet_simplexSet (m : ℕ) : MeasurableSet (simplexSet m) :=
  (isClosed_simplexSet m).measurableSet

theorem simplexSet_subset_Icc (m : ℕ) : simplexSet m ⊆ Icc 0 1 := fun _ hx =>
  ⟨fun i => hx.1 i, fun i => (Finset.single_le_sum (fun j _ => hx.1 j)
    (Finset.mem_univ i)).trans hx.2⟩

theorem isCompact_simplexSet (m : ℕ) : IsCompact (simplexSet m) :=
  isCompact_Icc.of_isClosed_subset (isClosed_simplexSet m) (simplexSet_subset_Icc m)

instance (m : ℕ) : IsFiniteMeasure (simplexMeasure m) :=
  isFiniteMeasure_restrict.mpr (isCompact_simplexSet m).measure_lt_top.ne

/-! ### The combined denominator -/

theorem continuous_simplexComb {m : ℕ} (a : Fin (m + 1) → ℂ) : Continuous (simplexComb a) := by
  unfold simplexComb
  fun_prop

theorem simplexComb_im {m : ℕ} (a : Fin (m + 1) → ℂ) (x : Fin m → ℝ) :
    (simplexComb a x).im =
      ∑ i, x i * (a i.castSucc).im + (1 - ∑ i, x i) * (a (Fin.last m)).im := by
  simp [simplexComb, Complex.im_sum, Complex.re_sum]

/-- On the simplex, `Im (simplexComb a x) ≤ maxᵢ Im aᵢ`. -/
theorem simplexComb_im_le {m : ℕ} (a : Fin (m + 1) → ℂ) {x : Fin m → ℝ}
    (hx : x ∈ simplexSet m) :
    (simplexComb a x).im ≤ Finset.univ.sup' Finset.univ_nonempty fun i => (a i).im := by
  set M := Finset.univ.sup' Finset.univ_nonempty fun i => (a i).im
  have hM : ∀ i, (a i).im ≤ M := fun i => Finset.le_sup' (fun i => (a i).im) (Finset.mem_univ i)
  rw [simplexComb_im]
  calc ∑ i, x i * (a i.castSucc).im + (1 - ∑ i, x i) * (a (Fin.last m)).im
      ≤ ∑ i, x i * M + (1 - ∑ i, x i) * M := by
        gcongr with i
        · exact hx.1 i
        · exact hM _
        · linarith [hx.2]
        · exact hM _
    _ = M := by rw [← Finset.sum_mul]; ring

/-- On the simplex, the combination of points of the open lower half plane lies in the open
lower half plane. -/
theorem simplexComb_im_neg {m : ℕ} {a : Fin (m + 1) → ℂ} (ha : ∀ i, (a i).im < 0)
    {x : Fin m → ℝ} (hx : x ∈ simplexSet m) : (simplexComb a x).im < 0 :=
  (simplexComb_im_le a hx).trans_lt ((Finset.sup'_lt_iff _).mpr fun i _ => ha i)

theorem simplexComb_ne_zero {m : ℕ} {a : Fin (m + 1) → ℂ} (ha : ∀ i, (a i).im < 0)
    {x : Fin m → ℝ} (hx : x ∈ simplexSet m) : simplexComb a x ≠ 0 :=
  QED.Integration.ne_zero_of_im_neg (simplexComb_im_neg ha hx)

/-- **Integrability.** `(simplexComb a x)^{-k}` is integrable on the simplex, for every `k`. -/
theorem integrableOn_simplex_inv_pow {m : ℕ} {a : Fin (m + 1) → ℂ} (ha : ∀ i, (a i).im < 0)
    (k : ℕ) : IntegrableOn (fun x => (simplexComb a x ^ k)⁻¹) (simplexSet m) := by
  refine ContinuousOn.integrableOn_compact (isCompact_simplexSet m) ?_
  exact ((continuous_simplexComb a).pow k).continuousOn.inv₀ fun x hx =>
    pow_ne_zero _ (simplexComb_ne_zero ha hx)

/-! ### The one-variable identity -/

/-- `∫₀¹ (1-t)^m (t c + (1-t) L)^{-(m+2)} dt = 1/((m+1) c L^{m+1})` for `c, L` in the open lower
half plane. -/
theorem integral_one_sub_pow_mul_inv_pow {L c : ℂ} (hL : L.im < 0) (hc : c.im < 0) (m : ℕ) :
    ∫ t in (0 : ℝ)..1, (1 - (t : ℂ)) ^ m * (((t : ℂ) * c + (1 - t) * L) ^ (m + 2))⁻¹ =
      (((m : ℂ) + 1) * c * L ^ (m + 1))⁻¹ := by
  have hI : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hc0 : c ≠ 0 := QED.Integration.ne_zero_of_im_neg hc
  have hm0 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hD : ∀ x ∈ Set.Icc (0 : ℝ) 1, (x : ℂ) * c + (1 - x) * L ≠ 0 := fun x hx =>
    QED.Integration.convex_combo_ne_zero hc hL hx
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
      (fun x : ℝ => (1 - (x : ℂ)) ^ (m + 1) /
        (-((m : ℂ) + 1) * c * ((x : ℂ) * c + (1 - x) * L) ^ (m + 1)))
      ((1 - (x : ℂ)) ^ m * (((x : ℂ) * c + (1 - x) * L) ^ (m + 2))⁻¹) x := by
    intro x hx
    have hL0 := hD x (hI ▸ hx)
    have hLd : HasDerivAt (fun w : ℂ => w * c + (1 - w) * L) (c - L) x := by
      have := ((hasDerivAt_id' (x := (x : ℂ))).mul_const c).fun_add
        (((hasDerivAt_id' (x := (x : ℂ))).const_sub 1).mul_const L)
      convert this using 1; ring
    have h1 : HasDerivAt (fun w : ℂ => (1 - w) ^ (m + 1))
        (((m + 1 : ℕ) : ℂ) * (1 - (x : ℂ)) ^ (m + 1 - 1) * (-1)) x := by
      have := ((hasDerivAt_id' (x := (x : ℂ))).const_sub 1).fun_pow (m + 1)
      convert this using 1
    have hd := h1.fun_div ((hLd.fun_pow (m + 1)).const_mul (-((m : ℂ) + 1) * c))
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hm0) hc0) (pow_ne_zero _ hL0))
    refine HasDerivAt.comp_ofReal (e := fun w : ℂ => (1 - w) ^ (m + 1) /
      (-((m : ℂ) + 1) * c * (w * c + (1 - w) * L) ^ (m + 1))) ?_
    convert hd using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have hcont : ContinuousOn
      (fun x : ℝ => (1 - (x : ℂ)) ^ m * (((x : ℂ) * c + (1 - x) * L) ^ (m + 2))⁻¹)
      (Set.uIcc 0 1) :=
    ContinuousOn.mul (by fun_prop) (ContinuousOn.inv₀ (by fun_prop)
      fun x hx => pow_ne_zero _ (hD x (hI ▸ hx)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hm1 : (-1 + -(m : ℂ)) ≠ 0 := by
    rw [show (-1 + -(m : ℂ)) = -((m : ℂ) + 1) by ring]
    exact neg_ne_zero.mpr hm0
  simp
  field_simp
  ring

/-! ### The induction step -/

/-- The family `a : Fin (m + 2) → ℂ` with its entry `a_m` (the second to last) removed. -/
def dropPenult {m : ℕ} (a : Fin (m + 2) → ℂ) : Fin (m + 1) → ℂ :=
  Fin.snoc (fun i : Fin m => a i.castSucc.castSucc) (a (Fin.last (m + 1)))

theorem dropPenult_im_neg {m : ℕ} {a : Fin (m + 2) → ℂ} (ha : ∀ i, (a i).im < 0)
    (i : Fin (m + 1)) : (dropPenult a i).im < 0 := by
  induction i using Fin.lastCases with
  | last => simpa [dropPenult] using ha _
  | cast i => simpa [dropPenult] using ha _

theorem prod_inv_eq_mul_prod_inv_dropPenult {m : ℕ} (a : Fin (m + 2) → ℂ) :
    ∏ i, (a i)⁻¹ = (a (Fin.last m).castSucc)⁻¹ * ∏ i, (dropPenult a i)⁻¹ := by
  simp only [dropPenult, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem snoc_mem_simplexSet_iff {m : ℕ} (x : Fin m → ℝ) (t : ℝ) :
    (Fin.snoc x t : Fin (m + 1) → ℝ) ∈ simplexSet (m + 1) ↔
      (∀ i, 0 ≤ x i) ∧ 0 ≤ t ∧ ∑ i, x i + t ≤ 1 := by
  simp [simplexSet, Fin.forall_fin_succ', Fin.sum_univ_castSucc, and_assoc]

theorem snoc_smul_mem_simplexSet_iff {m : ℕ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (y : Fin m → ℝ) :
    (Fin.snoc ((1 - t) • y) t : Fin (m + 1) → ℝ) ∈ simplexSet (m + 1) ↔ y ∈ simplexSet m := by
  have hR : 0 < 1 - t := by linarith [ht.2]
  rw [snoc_mem_simplexSet_iff]
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨fun i => (mul_nonneg_iff_of_pos_left hR).mp (h1 i), by nlinarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => mul_nonneg hR.le (h1 i), ht.1.le, by nlinarith⟩

theorem snoc_notMem_simplexSet {m : ℕ} {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) (x : Fin m → ℝ) :
    (Fin.snoc x t : Fin (m + 1) → ℝ) ∉ simplexSet (m + 1) := by
  rw [snoc_mem_simplexSet_iff]
  rintro ⟨h1, h2, h3⟩
  exact ht ⟨h2, by linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => h1 i]⟩

/-- Rescaling the first `m` coordinates by `1 - t` turns the combination into
`t aₘ + (1 - t) L`, with `L` the combination of the other `m + 1` factors. -/
theorem simplexComb_snoc_smul {m : ℕ} (a : Fin (m + 2) → ℂ) (y : Fin m → ℝ) (t : ℝ) :
    simplexComb a (Fin.snoc ((1 - t) • y) t) =
      (t : ℂ) * a (Fin.last m).castSucc + (1 - t) * simplexComb (dropPenult a) y := by
  simp only [simplexComb, dropPenult, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Pi.smul_apply, smul_eq_mul]
  push_cast
  have h1 : ∑ i, (1 - (t : ℂ)) * (y i : ℂ) * a i.castSucc.castSucc =
      (1 - t) * ∑ i, (y i : ℂ) * a i.castSucc.castSucc := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, (1 - (t : ℂ)) * (y i : ℂ) = (1 - t) * ∑ i, (y i : ℂ) := by
    rw [Finset.mul_sum]
  rw [h1, h2]
  ring

/-- The rescaled integrand is integrable on `(0, 1) × Δₘ`. -/
theorem integrableOn_Ioo_prod_simplex {m : ℕ} {c : ℂ} (hc : c.im < 0) {b : Fin (m + 1) → ℂ}
    (hb : ∀ i, (b i).im < 0) :
    IntegrableOn (fun q : ℝ × (Fin m → ℝ) => (1 - (q.1 : ℂ)) ^ m *
      (((q.1 : ℂ) * c + (1 - q.1) * simplexComb b q.2) ^ (m + 2))⁻¹)
      (Ioo 0 1 ×ˢ simplexSet m) := by
  refine (ContinuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_simplexSet m))
    ?_).mono_set (prod_mono Ioo_subset_Icc_self subset_rfl)
  have := continuous_simplexComb b
  refine ContinuousOn.mul (by fun_prop) (ContinuousOn.inv₀ (by fun_prop) ?_)
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  exact pow_ne_zero _ (QED.Integration.convex_combo_ne_zero hc (simplexComb_im_neg hb hy) ht)

/-- **The induction step.** -/
theorem integral_simplex_succ {m : ℕ} {a : Fin (m + 2) → ℂ} (ha : ∀ i, (a i).im < 0) :
    ∫ x in simplexSet (m + 1), (simplexComb a x ^ (m + 2))⁻¹ =
      (((m : ℂ) + 1) * a (Fin.last m).castSucc)⁻¹ *
        ∫ y in simplexSet m, (simplexComb (dropPenult a) y ^ (m + 1))⁻¹ := by
  set c := a (Fin.last m).castSucc with hc_def
  have hc : c.im < 0 := ha _
  have hb := dropPenult_im_neg ha
  set f : (Fin (m + 1) → ℝ) → ℂ := fun x => (simplexComb a x ^ (m + 2))⁻¹ with hf
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  have he : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  have hsymm : ∀ q : ℝ × (Fin m → ℝ), e.symm q = Fin.snoc q.2 q.1 := fun q => by
    simp [e, Fin.snocEquiv]
  have hind : Integrable ((simplexSet (m + 1)).indicator f) :=
    (integrableOn_simplex_inv_pow ha (m + 2)).integrable_indicator (measurableSet_simplexSet _)
  have hprod : Integrable (fun q => (simplexSet (m + 1)).indicator f (e.symm q))
      (volume.prod volume) :=
    ((MeasurePreserving.symm e he).integrable_comp_emb e.symm.measurableEmbedding).mpr hind
  rw [← integral_indicator (measurableSet_simplexSet _),
    ← (MeasurePreserving.symm e he).integral_comp', integral_prod _ hprod]
  simp only [hsymm]
  have hout : ∀ t ∉ Icc (0 : ℝ) 1,
      ∫ x' : Fin m → ℝ, (simplexSet (m + 1)).indicator f (Fin.snoc x' t) = 0 := by
    intro t ht
    simp [Set.indicator_of_notMem (snoc_notMem_simplexSet ht _)]
  have hin : ∀ t ∈ Ioo (0 : ℝ) 1,
      ∫ x' : Fin m → ℝ, (simplexSet (m + 1)).indicator f (Fin.snoc x' t) =
        ∫ y in simplexSet m, (1 - (t : ℂ)) ^ m *
          (((t : ℂ) * c + (1 - t) * simplexComb (dropPenult a) y) ^ (m + 2))⁻¹ := by
    intro t ht
    have hR : 0 < 1 - t := by linarith [ht.2]
    set g : (Fin m → ℝ) → ℂ := fun x' => (simplexSet (m + 1)).indicator f (Fin.snoc x' t)
      with hg_def
    have hscale := Measure.integral_comp_smul (μ := (volume : Measure (Fin m → ℝ))) g (1 - t)
    rw [Module.finrank_fin_fun, abs_of_pos (by positivity)] at hscale
    have hg' : ∫ x', g x' = (1 - t) ^ m • ∫ y, g ((1 - t) • y) := by
      rw [hscale, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    have hg : ∀ y, g ((1 - t) • y) = (simplexSet m).indicator (fun y =>
        (((t : ℂ) * c + (1 - t) * simplexComb (dropPenult a) y) ^ (m + 2))⁻¹) y := by
      intro y
      show (simplexSet (m + 1)).indicator f (Fin.snoc ((1 - t) • y) t) = _
      by_cases hy : y ∈ simplexSet m
      · rw [indicator_of_mem hy, indicator_of_mem ((snoc_smul_mem_simplexSet_iff ht y).mpr hy)]
        simp only [hf, simplexComb_snoc_smul, hc_def]
      · rw [indicator_of_notMem hy,
          indicator_of_notMem (mt (snoc_smul_mem_simplexSet_iff ht y).mp hy)]
    rw [hg']
    simp only [hg]
    rw [integral_indicator (measurableSet_simplexSet m), Complex.real_smul,
      ← integral_const_mul]
    push_cast
    rfl
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout, integral_Icc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hin]
  have hFint := integrableOn_Ioo_prod_simplex hc hb
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hFint
  rw [integral_integral_swap hFint, ← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_simplexSet m) fun y hy => ?_
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_one_sub_pow_mul_inv_pow (simplexComb_im_neg hb hy) hc m, mul_inv, mul_inv]

/-! ### The Feynman formula -/

/-- **The Feynman formula for `m + 1` factors.** For `a₀, …, aₘ` in the open lower half plane,
`∏ᵢ aᵢ⁻¹ = m! ∫_{Δₘ} (∑_{i<m} xᵢ aᵢ + (1 - ∑ᵢ xᵢ) aₘ)^{-(m+1)} dx`, with `Δₘ = simplexSet m`
and Lebesgue measure on `Fin m → ℝ`. -/
theorem prod_inv_eq_factorial_mul_integral_simplex :
    ∀ {m : ℕ} {a : Fin (m + 1) → ℂ}, (∀ i, (a i).im < 0) →
      ∏ i, (a i)⁻¹ = (m.factorial : ℂ) * ∫ x in simplexSet m, (simplexComb a x ^ (m + 1))⁻¹
  | 0, a, _ => by
    have h1 : simplexSet 0 = univ := by ext x; simp [simplexSet]
    have h2 : ∀ x : Fin 0 → ℝ, simplexComb a x = a 0 := fun x => by simp [simplexComb]
    simp [h1, h2, measureReal_def, volume_pi]
  | m + 1, a, ha => by
    rw [integral_simplex_succ ha, prod_inv_eq_mul_prod_inv_dropPenult,
      prod_inv_eq_factorial_mul_integral_simplex (dropPenult_im_neg ha), Nat.factorial_succ]
    have hm0 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    push_cast
    field_simp

/-- The Feynman formula against `simplexMeasure`. -/
theorem prod_inv_eq_factorial_mul_integral_simplexMeasure {m : ℕ} {a : Fin (m + 1) → ℂ}
    (ha : ∀ i, (a i).im < 0) :
    ∏ i, (a i)⁻¹ = (m.factorial : ℂ) * ∫ x, (simplexComb a x ^ (m + 1))⁻¹ ∂simplexMeasure m :=
  prod_inv_eq_factorial_mul_integral_simplex ha

end QED.Integration.Feynman

end
