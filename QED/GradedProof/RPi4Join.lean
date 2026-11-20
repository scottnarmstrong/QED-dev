/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SimplexMerge
public import QED.Integration.ChengWu
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# (R-Π₄) step L6c′: the simplex as a join of two faces

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6c′ (chain
coordinates for the heavy-photon sectors). The simplex `Δₙ` (`simplexSet n`, Lebesgue measure on
the first `n` barycentric coordinates) is the join of two complementary faces: a point with
barycentric coordinates `z` is `(ρ w, (1 - ρ) v)` with `ρ` the weight of the first block and
`w`, `v` barycentric points of the two faces. The Jacobian is `ρᵖ (1 - ρ)^q`.

* `integral_simplex_peel`: `∫_{Δₘ₊₁} g = ∫₀¹ (1 - t)ᵐ ∫_{Δₘ} g((1 - t) y, t)` (Fubini in the last
  free coordinate and a linear scaling);
* `integral_simplex_cone`: the cone over the facet opposite the last vertex,
  `∫_{Δₘ₊₁} f(z) = ∫₀¹ ρᵐ ∫_{Δₘ} f(ρ w, 1 - ρ)`;
* `appendME`, `measurePreserving_appendME`: concatenation `ℝᵖ × ℝ^q ≃ ℝ^{p+q}`;
* `integral_simplex_append`: Fubini over a block of free coordinates, which ranges over a scaled
  simplex `(1 - ∑ a) Δ_q`;
* `integral_simplex_join` (**the join**): for blocks of `p + 1` and `q + 1` barycentric
  coordinates, `∫_{Δ_{p+q+1}} f(z) = ∫₀¹ ρᵖ (1 - ρ)^q ∫_{Δ_p} ∫_{Δ_q} f(ρ w, (1 - ρ) v)`.

Applied twice it gives the chain coordinates `(a₀, a₁, t) × Δ(S₀) × Δ(S₁)` of the theta graph.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  snoc_smul_mem_simplexSet_iff snoc_notMem_simplexSet)
open QED.Integration.Feynman (snoc_mem_simplexSet_iff)
open QED.Integration.TwoLoop (simplexPoint_castSucc simplexPoint_last sum_simplexPoint
  simplexPoint_eq_snoc)
open QED.Integration.SimplexMerge (integral_simplex_comp_perm integrableOn_simplex_comp_perm_iff)

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The cone over a facet -/

/-- **Peeling the last free coordinate**: for `g` integrable on `Δₘ₊₁`,
`∫_{Δₘ₊₁} g = ∫₀¹ (1 - t)ᵐ ∫_{Δₘ} g((1 - t) y, t) dy dt`. -/
theorem integral_simplex_peel {g : (Fin (m + 1) → ℝ) → E}
    (hg : IntegrableOn g (simplexSet (m + 1))) :
    ∫ x in simplexSet (m + 1), g x =
      ∫ t in (0 : ℝ)..1, (1 - t) ^ m • ∫ y in simplexSet m, g (Fin.snoc ((1 - t) • y) t) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  have he : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  have hsymm : ∀ q : ℝ × (Fin m → ℝ), e.symm q = Fin.snoc q.2 q.1 := fun q => by
    simp [e, Fin.snocEquiv]
  have hind : Integrable ((simplexSet (m + 1)).indicator g) :=
    hg.integrable_indicator (measurableSet_simplexSet _)
  have hprod : Integrable (fun q => (simplexSet (m + 1)).indicator g (e.symm q))
      (volume.prod volume) :=
    ((MeasurePreserving.symm e he).integrable_comp_emb e.symm.measurableEmbedding).mpr hind
  rw [← integral_indicator (measurableSet_simplexSet _),
    ← (MeasurePreserving.symm e he).integral_comp', integral_prod _ hprod]
  simp only [hsymm]
  have hout : ∀ t ∉ Icc (0 : ℝ) 1,
      ∫ x' : Fin m → ℝ, (simplexSet (m + 1)).indicator g (Fin.snoc x' t) = 0 := by
    intro t ht
    simp [Set.indicator_of_notMem (snoc_notMem_simplexSet ht _)]
  have hin : ∀ t ∈ Ioo (0 : ℝ) 1,
      ∫ x' : Fin m → ℝ, (simplexSet (m + 1)).indicator g (Fin.snoc x' t) =
        (1 - t) ^ m • ∫ y in simplexSet m, g (Fin.snoc ((1 - t) • y) t) := by
    intro t ht
    have hR : 0 < 1 - t := by linarith [ht.2]
    set G : (Fin m → ℝ) → E := fun x' => (simplexSet (m + 1)).indicator g (Fin.snoc x' t)
      with hG
    have hscale := Measure.integral_comp_smul (μ := (volume : Measure (Fin m → ℝ))) G (1 - t)
    rw [Module.finrank_fin_fun, abs_of_pos (by positivity)] at hscale
    have hG' : ∫ x', G x' = (1 - t) ^ m • ∫ y, G ((1 - t) • y) := by
      rw [hscale, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    have hGy : ∀ y, G ((1 - t) • y) =
        (simplexSet m).indicator (fun y => g (Fin.snoc ((1 - t) • y) t)) y := by
      intro y
      show (simplexSet (m + 1)).indicator g (Fin.snoc ((1 - t) • y) t) = _
      by_cases hy : y ∈ simplexSet m
      · rw [indicator_of_mem hy, indicator_of_mem ((snoc_smul_mem_simplexSet_iff ht y).mpr hy)]
      · rw [indicator_of_notMem hy,
          indicator_of_notMem (mt (snoc_smul_mem_simplexSet_iff ht y).mp hy)]
    rw [hG']
    simp only [hGy]
    rw [integral_indicator (measurableSet_simplexSet m)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout, integral_Icc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hin, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

/-- The barycentric point of the peeled coordinates, with the last two coordinates swapped. -/
theorem simplexPoint_snoc_smul_comp_swap (y : Fin m → ℝ) (t : ℝ) :
    simplexPoint (Fin.snoc ((1 - t) • y) t : Fin (m + 1) → ℝ) ∘
        Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1)) =
      Fin.snoc ((1 - t) • simplexPoint y) t := by
  funext k
  simp only [Function.comp_apply]
  induction k using Fin.lastCases with
  | last =>
    rw [Equiv.swap_apply_right, simplexPoint_castSucc, Fin.snoc_last, Fin.snoc_last]
  | cast j =>
    rw [Fin.snoc_castSucc]
    induction j using Fin.lastCases with
    | last =>
      rw [Equiv.swap_apply_left, simplexPoint_last, Pi.smul_apply, simplexPoint_last,
        Fin.sum_univ_castSucc, Fin.snoc_last]
      simp only [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      ring
    | cast i =>
      rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega)
        (by simp [Fin.ext_iff]; omega),
        simplexPoint_castSucc, Fin.snoc_castSucc, Pi.smul_apply, Pi.smul_apply,
        simplexPoint_castSucc]

/-- **The simplex as a cone over a facet**: with `ρ` the total weight of the first `m + 1`
barycentric coordinates, `∫_{Δₘ₊₁} f(z) = ∫₀¹ ρᵐ ∫_{Δₘ} f(ρ w, 1 - ρ) dw dρ`. -/
theorem integral_simplex_cone {f : (Fin (m + 2) → ℝ) → E}
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet (m + 1))) :
    ∫ x in simplexSet (m + 1), f (simplexPoint x) =
      ∫ ρ in (0 : ℝ)..1, ρ ^ m •
        ∫ y in simplexSet m, f (Fin.snoc (ρ • simplexPoint y) (1 - ρ)) := by
  set σ := Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1))
  rw [← integral_simplex_comp_perm σ f]
  have hf' : IntegrableOn (fun x => f (simplexPoint x ∘ σ)) (simplexSet (m + 1)) :=
    (integrableOn_simplex_comp_perm_iff σ f).mpr hf
  rw [integral_simplex_peel hf']
  simp only [σ, simplexPoint_snoc_smul_comp_swap]
  have h := intervalIntegral.integral_comp_sub_left (fun ρ : ℝ =>
    ρ ^ m • ∫ y in simplexSet m, f (Fin.snoc (ρ • simplexPoint y) (1 - ρ))) (a := 0) (b := 1)
    (1 : ℝ)
  simp only [sub_sub_cancel, sub_zero, sub_self] at h
  rw [← h]


/-! ### The join of two faces -/

/-- Membership in `Δₘ` for every `m` (including `m = 0`). -/
theorem mem_simplexSet_iff_forall (x : Fin m → ℝ) :
    x ∈ simplexSet m ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by
  have ht : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  rw [← snoc_smul_mem_simplexSet_iff ht x, snoc_mem_simplexSet_iff]
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨fun i => by nlinarith [h1 i], by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by nlinarith [h1 i], by norm_num, by linarith⟩

/-- Concatenation `(a, c) ↦ a ++ c` as a measurable equivalence. -/
noncomputable def appendME (p q : ℕ) : (Fin p → ℝ) × (Fin q → ℝ) ≃ᵐ (Fin (p + q) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin p ⊕ Fin q => ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) finSumFinEquiv)

theorem appendME_apply (p q : ℕ) (z : (Fin p → ℝ) × (Fin q → ℝ)) :
    appendME p q z = Fin.append z.1 z.2 := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [Fin.append_left, ← finSumFinEquiv_apply_left, appendME, MeasurableEquiv.trans_apply,
      MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  · rw [Fin.append_right, ← finSumFinEquiv_apply_right, appendME, MeasurableEquiv.trans_apply,
      MeasurableEquiv.piCongrLeft_apply_apply]
    rfl

theorem measurePreserving_appendME (p q : ℕ) :
    MeasurePreserving (appendME p q) (volume.prod volume) volume :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin (p + q) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin p ⊕ Fin q => ℝ))

theorem append_mem_simplexSet_iff {p q : ℕ} (a : Fin p → ℝ) (c : Fin q → ℝ) :
    Fin.append a c ∈ simplexSet (p + q) ↔
      (∀ i, 0 ≤ a i) ∧ (∀ j, 0 ≤ c j) ∧ ∑ i, a i + ∑ j, c j ≤ 1 := by
  simp only [mem_simplexSet_iff_forall, Fin.forall_fin_add, Fin.append_left, Fin.append_right,
    Fin.sum_univ_add, and_assoc]

/-- The barycentric point of a concatenation. -/
theorem simplexPoint_append {p q : ℕ} (a : Fin p → ℝ) (c : Fin q → ℝ) :
    simplexPoint (Fin.append a c) =
      Fin.append a (Fin.snoc c (1 - ∑ i, a i - ∑ j, c j) : Fin (q + 1) → ℝ) := by
  rw [Fin.append_snoc]
  simp only [simplexPoint_eq_snoc, Fin.sum_univ_add, Fin.append_left, Fin.append_right, sub_sub]

/-- The scaled second block: `c = (1 - ∑ a) v`. -/
theorem simplexPoint_append_smul {p q : ℕ} (a : Fin p → ℝ) (v : Fin q → ℝ) :
    simplexPoint (Fin.append a ((1 - ∑ i, a i) • v)) =
      Fin.append a ((1 - ∑ i, a i) • simplexPoint v) := by
  rw [simplexPoint_append]
  congr 1
  funext k
  induction k using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last, Pi.smul_apply, simplexPoint_last, smul_eq_mul]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring
  | cast j => rw [Fin.snoc_castSucc, Pi.smul_apply, Pi.smul_apply, simplexPoint_castSucc]

/-- **Fubini over the second block, with its scaling**: for `f` integrable on `Δ_{p+q}`,
`∫_{Δ_{p+q}} f = ∫_{a ∈ Δ_p} (1 - ∑ a)^q ∫_{v ∈ Δ_q} f(a, (1 - ∑ a) v)`. -/
theorem integral_simplex_append {p q : ℕ} {g : (Fin (p + 1 + q) → ℝ) → E}
    (hg : IntegrableOn g (simplexSet (p + 1 + q))) :
    IntegrableOn (fun a : Fin (p + 1) → ℝ => (1 - ∑ i, a i) ^ q •
        ∫ v in simplexSet q, g (Fin.append a ((1 - ∑ i, a i) • v))) (simplexSet (p + 1)) ∧
    ∫ x in simplexSet (p + 1 + q), g x =
      ∫ a in simplexSet (p + 1), (1 - ∑ i, a i) ^ q •
        ∫ v in simplexSet q, g (Fin.append a ((1 - ∑ i, a i) • v)) := by
  set e := appendME (p + 1) q
  have he := measurePreserving_appendME (p + 1) q
  set G : (Fin (p + 1) → ℝ) → E := fun a => (1 - ∑ i, a i) ^ q •
    ∫ v in simplexSet q, g (Fin.append a ((1 - ∑ i, a i) • v)) with hG
  have hind : Integrable ((simplexSet (p + 1 + q)).indicator g) :=
    hg.integrable_indicator (measurableSet_simplexSet _)
  have hprod : Integrable (fun z => (simplexSet (p + 1 + q)).indicator g (e z))
      (volume.prod volume) := (he.integrable_comp_emb e.measurableEmbedding).mpr hind
  have hinner : ∀ a : Fin (p + 1) → ℝ, ∑ i, a i ≠ 1 →
      ∫ c, (simplexSet (p + 1 + q)).indicator g (e (a, c)) =
        (simplexSet (p + 1)).indicator G a := by
    intro a ha1
    simp only [e, appendME_apply]
    by_cases ha : a ∈ simplexSet (p + 1)
    · have ha' := (mem_simplexSet_iff_forall a).mp ha
      have hlt : ∑ i, a i < 1 := lt_of_le_of_ne ha'.2 ha1
      have hR : 0 < 1 - ∑ i, a i := by linarith
      rw [indicator_of_mem ha]
      set R := 1 - ∑ i, a i
      set H : (Fin q → ℝ) → E := fun c => (simplexSet (p + 1 + q)).indicator g (Fin.append a c)
      have hscale := Measure.integral_comp_smul (μ := (volume : Measure (Fin q → ℝ))) H R
      rw [Module.finrank_fin_fun, abs_of_pos (by positivity)] at hscale
      have hH : ∫ c, H c = R ^ q • ∫ v, H (R • v) := by
        rw [hscale, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
      have hHv : ∀ v, H (R • v) =
          (simplexSet q).indicator (fun v => g (Fin.append a (R • v))) v := by
        intro v
        show (simplexSet (p + 1 + q)).indicator g (Fin.append a (R • v)) = _
        have hiff : Fin.append a (R • v) ∈ simplexSet (p + 1 + q) ↔ v ∈ simplexSet q := by
          rw [append_mem_simplexSet_iff, mem_simplexSet_iff_forall]
          simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
          constructor
          · rintro ⟨-, h1, h2⟩
            refine ⟨fun j => (mul_nonneg_iff_of_pos_left hR).mp (h1 j), ?_⟩
            nlinarith
          · rintro ⟨h1, h2⟩
            exact ⟨ha'.1, fun j => mul_nonneg hR.le (h1 j), by nlinarith⟩
        by_cases hv : v ∈ simplexSet q
        · rw [indicator_of_mem hv, indicator_of_mem (hiff.mpr hv)]
        · rw [indicator_of_notMem hv, indicator_of_notMem (mt hiff.mp hv)]
      show ∫ c, H c = _
      rw [hH]
      simp only [hHv]
      rw [integral_indicator (measurableSet_simplexSet q)]
    · rw [indicator_of_notMem ha]
      have : ∀ c, Fin.append a c ∉ simplexSet (p + 1 + q) := by
        intro c hc
        rw [append_mem_simplexSet_iff] at hc
        refine ha ((mem_simplexSet_iff_forall a).mpr ⟨hc.1, ?_⟩)
        by_contra h
        have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hc.2.1 j
        linarith [hc.2.2]
      simp [indicator_of_notMem (this _)]
  have hae : (fun a => ∫ c, (simplexSet (p + 1 + q)).indicator g (e (a, c))) =ᵐ[volume]
      (simplexSet (p + 1)).indicator G := by
    have hnull := QED.Integration.ChengWu.volume_sum_eq_one (m := p + 1) 0
    have hne : ∀ᵐ a ∂(volume : Measure (Fin (p + 1) → ℝ)), ∑ i, a i ≠ 1 := by
      rw [ae_iff]
      simpa only [not_not] using hnull
    filter_upwards [hne] with a ha using hinner a ha
  have hint := (hprod.integral_prod_left).congr hae
  refine ⟨(integrable_indicator_iff (measurableSet_simplexSet _)).mp hint, ?_⟩
  rw [← integral_indicator (measurableSet_simplexSet _), ← he.integral_comp',
    integral_prod _ hprod, integral_congr_ae hae, integral_indicator (measurableSet_simplexSet _)]

/-- **The simplex join**: the barycentric coordinates of `Δ_{p+q+1}` split into a block of
`p + 1` and a block of `q + 1`; with `ρ` the weight of the first block,
`∫_{Δ_{p+q+1}} f(z) = ∫₀¹ ρᵖ (1 - ρ)^q ∫_{Δ_p} ∫_{Δ_q} f(ρ w, (1 - ρ) v) dv dw dρ`. -/
theorem integral_simplex_join {p q : ℕ} {f : (Fin (p + 1 + (q + 1)) → ℝ) → E}
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet (p + 1 + q))) :
    ∫ x in simplexSet (p + 1 + q), f (simplexPoint x) =
      ∫ ρ in (0 : ℝ)..1, (ρ ^ p * (1 - ρ) ^ q) • ∫ w in simplexSet p, ∫ v in simplexSet q,
        f (Fin.append (ρ • simplexPoint w) ((1 - ρ) • simplexPoint v)) := by
  obtain ⟨hGi, hJ⟩ := integral_simplex_append hf
  rw [hJ]
  set G : (Fin (p + 1) → ℝ) → E := fun a => (1 - ∑ i, a i) ^ q •
    ∫ v in simplexSet q, f (simplexPoint (Fin.append a ((1 - ∑ i, a i) • v))) with hG
  have hinit : ∀ x : Fin (p + 1) → ℝ, Fin.init (simplexPoint x) = x := fun x => by
    rw [simplexPoint_eq_snoc, Fin.init_snoc]
  have hc := integral_simplex_cone (m := p) (f := fun z => G (Fin.init z)) (by
    simpa only [hinit] using hGi)
  simp only [hinit, Fin.init_snoc] at hc
  rw [hc]
  refine intervalIntegral.integral_congr fun ρ _ => ?_
  have hsum : ∀ w : Fin p → ℝ, ∑ i, (ρ • simplexPoint w) i = ρ := fun w => by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_simplexPoint, mul_one]
  have hGw : ∀ w : Fin p → ℝ, G (ρ • simplexPoint w) = (1 - ρ) ^ q •
      ∫ v in simplexSet q, f (Fin.append (ρ • simplexPoint w) ((1 - ρ) • simplexPoint v)) := by
    intro w
    simp only [hG, simplexPoint_append_smul, hsum]
  simp only [hGw]
  rw [integral_smul, smul_smul]

end QED.GradedProof.RPi4

end
