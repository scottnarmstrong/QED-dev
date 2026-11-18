/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SymanzikIntegrability
public import QED.Integration.FeynmanParameterGeneral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.GroupTheory.Perm.Sign

/-!
# Permuting and merging barycentric coordinates on the simplex

Integrals over the simplex `Δₘ = simplexSet m` of functions of the barycentric point
`z = simplexPoint x ∈ ℝ^{m+1}` (Lebesgue measure on the first `m` coordinates):

* **Permutation invariance** (`integral_simplex_comp_perm`, `integrableOn_simplex_comp_perm_iff`):
  for every permutation `σ` of the `m + 1` barycentric coordinates,
  `∫_{Δₘ} f(z ∘ σ) = ∫_{Δₘ} f(z)`, and integrability is preserved. Every permutation is a product
  of exchanges of a coordinate with the last one, and each of these is the measure-preserving
  affine involution `simplexSwap` of `QED/Integration/SymanzikIntegrability.lean`.
* **Merging two coordinates** (`integral_simplex_splitAt`): for `f` integrable on `Δₘ₊₁` and a
  coordinate `i` of `ℝ^{m+1}`,
  `∫_{Δₘ₊₁} f(z) = ∫_{Δₘ} ∫₀^{zᵢ} f(splitAt i z t) dt`,
  where `splitAt i z t = (z with zᵢ replaced by t, then zᵢ - t appended)` splits the coordinate
  `zᵢ` of the smaller simplex into the pair `(t, zᵢ - t)` (coordinates `i` and `m + 1`). If `f`
  depends on the pair only through its sum, the inner integral is `zᵢ f` (the group-volume factor
  of a merged pair). The integrand on the right is integrable on `Δₘ`.

The merging step is Fubini in the last free coordinate (`integral_simplexSet_succ`), composed with
two permutations.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.Integration.SimplexMerge

open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet snoc_mem_simplexSet_iff)
open QED.Integration.TwoLoop (simplexSwap simplexSwapEquiv simplexPoint_simplexSwap
  preimage_simplexSwap measurePreserving_simplexSwap simplexPoint_castSucc simplexPoint_last)

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Permutations of the barycentric coordinates -/

/-- `ψ` realizes the permutation `σ` of the barycentric coordinates: it is measure preserving,
maps the simplex onto itself, and `simplexPoint (ψ x) = simplexPoint x ∘ σ`. -/
def IsSimplexPerm (σ : Equiv.Perm (Fin (m + 1))) (ψ : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ)) : Prop :=
  MeasurePreserving ψ volume volume ∧ ψ ⁻¹' simplexSet m = simplexSet m ∧
    ∀ x, simplexPoint (ψ x) = simplexPoint x ∘ σ

theorem IsSimplexPerm.mul {σ₁ σ₂ : Equiv.Perm (Fin (m + 1))} {ψ₁ ψ₂ : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ)}
    (h₁ : IsSimplexPerm σ₁ ψ₁) (h₂ : IsSimplexPerm σ₂ ψ₂) :
    IsSimplexPerm (σ₂ * σ₁) (ψ₂.trans ψ₁) := by
  refine ⟨h₁.1.comp h₂.1, ?_, fun x => ?_⟩
  · change (fun x => ψ₁ (ψ₂ x)) ⁻¹' simplexSet m = simplexSet m
    rw [show (fun x => ψ₁ (ψ₂ x)) ⁻¹' simplexSet m = ψ₂ ⁻¹' (ψ₁ ⁻¹' simplexSet m) from rfl,
      h₁.2.1, h₂.2.1]
  · change simplexPoint (ψ₁ (ψ₂ x)) = _
    rw [h₁.2.2, h₂.2.2, Equiv.Perm.coe_mul]
    rfl

theorem isSimplexPerm_swap_last (j : Fin m) :
    IsSimplexPerm (Equiv.swap j.castSucc (Fin.last m)) (simplexSwapEquiv j) :=
  ⟨measurePreserving_simplexSwap j, preimage_simplexSwap j,
    fun x => funext fun i => simplexPoint_simplexSwap j x i⟩

theorem exists_isSimplexPerm_swap_last (a : Fin (m + 1)) :
    ∃ ψ, IsSimplexPerm (Equiv.swap a (Fin.last m)) ψ := by
  induction a using Fin.lastCases with
  | last =>
    refine ⟨MeasurableEquiv.refl _, MeasurePreserving.id _, rfl, fun x => ?_⟩
    rw [Equiv.swap_self, Equiv.coe_refl]
    rfl
  | cast j => exact ⟨_, isSimplexPerm_swap_last j⟩

theorem exists_isSimplexPerm_swap (a b : Fin (m + 1)) :
    ∃ ψ, IsSimplexPerm (Equiv.swap a b) ψ := by
  by_cases ha : a = Fin.last m
  · subst ha
    rw [Equiv.swap_comm]
    exact exists_isSimplexPerm_swap_last b
  by_cases hb : b = Fin.last m
  · subst hb
    exact exists_isSimplexPerm_swap_last a
  by_cases hab : a = b
  · subst hab
    rw [Equiv.swap_self]
    exact ⟨MeasurableEquiv.refl _, MeasurePreserving.id _, rfl, fun x => rfl⟩
  obtain ⟨ψ₁, h₁⟩ := exists_isSimplexPerm_swap_last a
  obtain ⟨ψ₂, h₂⟩ := exists_isSimplexPerm_swap_last b
  have h₁' : IsSimplexPerm (Equiv.swap (Fin.last m) a) ψ₁ := by rwa [Equiv.swap_comm]
  have hs : Equiv.swap (Fin.last m) a * Equiv.swap b (Fin.last m) * Equiv.swap (Fin.last m) a =
      Equiv.swap a b := Equiv.swap_mul_swap_mul_swap hb (Ne.symm hab)
  rw [← hs, mul_assoc]
  exact ⟨_, (h₁'.mul h₂).mul h₁'⟩

/-- **Every permutation of the barycentric coordinates is realized** by a measure-preserving
bijection of the simplex. -/
theorem exists_isSimplexPerm (σ : Equiv.Perm (Fin (m + 1))) : ∃ ψ, IsSimplexPerm σ ψ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨MeasurableEquiv.refl _, MeasurePreserving.id _, rfl, fun x => rfl⟩
  | swap_mul σ a b _ ih =>
    obtain ⟨ψ, hψ⟩ := ih
    obtain ⟨φ, hφ⟩ := exists_isSimplexPerm_swap a b
    exact ⟨_, hψ.mul hφ⟩

/-- **Permutation invariance of the simplex integral.** -/
theorem integral_simplex_comp_perm (σ : Equiv.Perm (Fin (m + 1)))
    (f : (Fin (m + 1) → ℝ) → E) :
    ∫ x in simplexSet m, f (simplexPoint x ∘ σ) = ∫ x in simplexSet m, f (simplexPoint x) := by
  obtain ⟨ψ, hmp, hpre, hpt⟩ := exists_isSimplexPerm σ
  have h := hmp.setIntegral_preimage_emb ψ.measurableEmbedding (fun y => f (simplexPoint y))
    (simplexSet m)
  rw [hpre] at h
  rw [← h]
  exact setIntegral_congr_fun (measurableSet_simplexSet m) fun x _ => by rw [hpt]

omit [NormedSpace ℝ E] in
/-- **Permutation invariance of integrability on the simplex.** -/
theorem integrableOn_simplex_comp_perm_iff (σ : Equiv.Perm (Fin (m + 1)))
    (f : (Fin (m + 1) → ℝ) → E) :
    IntegrableOn (fun x => f (simplexPoint x ∘ σ)) (simplexSet m) ↔
      IntegrableOn (fun x => f (simplexPoint x)) (simplexSet m) := by
  obtain ⟨ψ, hmp, hpre, hpt⟩ := exists_isSimplexPerm σ
  have h := hmp.integrableOn_comp_preimage ψ.measurableEmbedding
    (f := fun y => f (simplexPoint y)) (s := simplexSet m)
  rw [hpre] at h
  rw [← h]
  refine integrableOn_congr_fun (fun x _ => ?_) (measurableSet_simplexSet m)
  simp only [Function.comp, hpt]

/-! ### Fubini in the last free coordinate -/

/-- Membership in the simplex, for `m > 0`. -/
theorem mem_simplexSet_iff_le (hm : 0 < m) (x : Fin m → ℝ) :
    x ∈ simplexSet m ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 := by
  rw [QED.Integration.TwoLoop.mem_simplexSet_iff hm]
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · simpa [simplexPoint_castSucc] using h i.castSucc
    · have := h (Fin.last m)
      rw [simplexPoint_last] at this
      linarith
  · rintro ⟨h1, h2⟩ i
    induction i using Fin.lastCases with
    | last => rw [simplexPoint_last]; linarith
    | cast j => rw [simplexPoint_castSucc]; exact h1 j

omit [NormedSpace ℝ E] in
theorem indicator_snoc_eq (hm : 0 < m) {g : (Fin (m + 1) → ℝ) → E} (y : Fin m → ℝ) (t : ℝ) :
    (simplexSet (m + 1)).indicator g (Fin.snoc y t) =
      (simplexSet m).indicator (fun y => (Icc 0 (1 - ∑ i, y i)).indicator
        (fun t => g (Fin.snoc y t)) t) y := by
  by_cases hy : y ∈ simplexSet m
  · rw [mem_simplexSet_iff_le hm] at hy
    rw [indicator_of_mem ((mem_simplexSet_iff_le hm y).mpr hy)]
    by_cases ht : t ∈ Icc 0 (1 - ∑ i, y i)
    · rw [indicator_of_mem ht, indicator_of_mem]
      rw [snoc_mem_simplexSet_iff]
      exact ⟨hy.1, ht.1, by linarith [ht.2]⟩
    · rw [indicator_of_notMem ht, indicator_of_notMem]
      rw [snoc_mem_simplexSet_iff]
      rintro ⟨-, h1, h2⟩
      exact ht ⟨h1, by linarith⟩
  · rw [indicator_of_notMem hy, indicator_of_notMem]
    rw [snoc_mem_simplexSet_iff]
    rintro ⟨h1, h2, h3⟩
    exact hy ((mem_simplexSet_iff_le hm y).mpr ⟨h1, by linarith⟩)

theorem integral_indicator_snoc (hm : 0 < m) {g : (Fin (m + 1) → ℝ) → E} (y : Fin m → ℝ) :
    ∫ t, (simplexSet (m + 1)).indicator g (Fin.snoc y t) =
      (simplexSet m).indicator
        (fun y => ∫ t in (0 : ℝ)..(1 - ∑ i, y i), g (Fin.snoc y t)) y := by
  simp only [indicator_snoc_eq hm]
  by_cases hy : y ∈ simplexSet m
  · simp only [indicator_of_mem hy]
    have hw : 0 ≤ 1 - ∑ i, y i := by linarith [((mem_simplexSet_iff_le hm y).mp hy).2]
    rw [integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le hw,
      integral_Icc_eq_integral_Ioc]
  · simp [indicator_of_notMem hy]

/-- **Fubini in the last free coordinate**: for `g` integrable on `Δₘ₊₁`,
`∫_{Δₘ₊₁} g = ∫_{y ∈ Δₘ} ∫₀^{1 - ∑ y} g(y, t) dt`, and the inner integral is integrable on `Δₘ`. -/
theorem integral_simplexSet_succ (hm : 0 < m) {g : (Fin (m + 1) → ℝ) → E}
    (hg : IntegrableOn g (simplexSet (m + 1))) :
    IntegrableOn (fun y => ∫ t in (0 : ℝ)..(1 - ∑ i, y i), g (Fin.snoc y t)) (simplexSet m) ∧
    ∫ x in simplexSet (m + 1), g x =
      ∫ y in simplexSet m, ∫ t in (0 : ℝ)..(1 - ∑ i, y i), g (Fin.snoc y t) := by
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
  have hpt : ∀ y : Fin m → ℝ, ∫ t, (simplexSet (m + 1)).indicator g (e.symm (t, y)) =
      (simplexSet m).indicator
        (fun y => ∫ t in (0 : ℝ)..(1 - ∑ i, y i), g (Fin.snoc y t)) y := fun y => by
    simp only [hsymm]
    exact integral_indicator_snoc hm y
  refine ⟨?_, ?_⟩
  · have h := hprod.integral_prod_right
    simp only [hpt] at h
    exact (integrable_indicator_iff (measurableSet_simplexSet m)).mp h
  · rw [← integral_indicator (measurableSet_simplexSet _),
      ← (MeasurePreserving.symm e he).integral_comp', integral_prod_symm _ hprod,
      ← integral_indicator (measurableSet_simplexSet m)]
    exact integral_congr_ae (ae_of_all _ hpt)

/-! ### Splitting a barycentric coordinate -/

/-- Split the coordinate `zᵢ` of `z ∈ ℝ^{m+1}` into the pair `(t, zᵢ - t)`, at the positions `i`
and `m + 1` of `ℝ^{m+2}`. -/
def splitAt (i : Fin (m + 1)) (z : Fin (m + 1) → ℝ) (t : ℝ) : Fin (m + 2) → ℝ :=
  Fin.snoc (Function.update z i t) (z i - t)

theorem splitAt_castSucc (i : Fin (m + 1)) (z : Fin (m + 1) → ℝ) (t : ℝ) (j : Fin (m + 1)) :
    splitAt i z t j.castSucc = Function.update z i t j := by
  simp [splitAt]

theorem splitAt_last (i : Fin (m + 1)) (z : Fin (m + 1) → ℝ) (t : ℝ) :
    splitAt i z t (Fin.last (m + 1)) = z i - t := by
  simp [splitAt]

theorem simplexPoint_snoc (y : Fin m → ℝ) (t : ℝ) :
    simplexPoint (Fin.snoc y t : Fin (m + 1) → ℝ) =
      splitAt (Fin.last m) (simplexPoint y) t := by
  funext k
  induction k using Fin.lastCases with
  | last =>
    rw [simplexPoint_last, splitAt_last, simplexPoint_last, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring
  | cast j =>
    rw [simplexPoint_castSucc, splitAt_castSucc]
    induction j using Fin.lastCases with
    | last => simp
    | cast i =>
      rw [Function.update_of_ne (Fin.castSucc_ne_last i), simplexPoint_castSucc]
      simp

/-- **Merging the last two barycentric coordinates.** -/
theorem integral_simplex_splitAt_last (hm : 0 < m) {f : (Fin (m + 2) → ℝ) → E}
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet (m + 1))) :
    IntegrableOn (fun y => ∫ t in (0 : ℝ)..simplexPoint y (Fin.last m),
        f (splitAt (Fin.last m) (simplexPoint y) t)) (simplexSet m) ∧
    ∫ x in simplexSet (m + 1), f (simplexPoint x) =
      ∫ y in simplexSet m, ∫ t in (0 : ℝ)..simplexPoint y (Fin.last m),
        f (splitAt (Fin.last m) (simplexPoint y) t) := by
  obtain ⟨h1, h2⟩ := integral_simplexSet_succ hm hf
  simp only [simplexPoint_snoc] at h1 h2
  simp only [simplexPoint_last]
  exact ⟨h1, h2⟩

theorem splitAt_comp_swap (i : Fin (m + 1)) (z : Fin (m + 1) → ℝ) (t : ℝ) :
    splitAt (Fin.last m) (z ∘ Equiv.swap i (Fin.last m)) t ∘
        Equiv.swap i.castSucc (Fin.last m).castSucc = splitAt i z t := by
  funext k
  induction k using Fin.lastCases with
  | last =>
    simp only [Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_ne_last i).symm
      (Fin.castSucc_ne_last (Fin.last m)).symm, splitAt_last, splitAt_last,
      Function.comp_apply, Equiv.swap_apply_right]
  | cast j =>
    simp only [Function.comp_apply]
    rw [Function.Injective.swap_apply (Fin.castSucc_injective _), splitAt_castSucc,
      splitAt_castSucc]
    by_cases hj : j = i
    · subst hj
      rw [Equiv.swap_apply_left, Function.update_self, Function.update_self]
    · have hs : Equiv.swap i (Fin.last m) j ≠ Fin.last m := by
        intro h
        apply hj
        have := congrArg (Equiv.swap i (Fin.last m)) h
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      rw [Function.update_of_ne hs, Function.update_of_ne hj, Function.comp_apply,
        Equiv.swap_apply_self]

/-- **Merging two barycentric coordinates.** For `f` integrable on `Δₘ₊₁` and a coordinate `i`
of `ℝ^{m+1}`: `∫_{Δₘ₊₁} f(z) = ∫_{Δₘ} ∫₀^{zᵢ} f(splitAt i z t) dt`, and the inner integral is
integrable on `Δₘ`. -/
theorem integral_simplex_splitAt (hm : 0 < m) (i : Fin (m + 1)) {f : (Fin (m + 2) → ℝ) → E}
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet (m + 1))) :
    IntegrableOn (fun y => ∫ t in (0 : ℝ)..simplexPoint y i, f (splitAt i (simplexPoint y) t))
      (simplexSet m) ∧
    ∫ x in simplexSet (m + 1), f (simplexPoint x) =
      ∫ y in simplexSet m, ∫ t in (0 : ℝ)..simplexPoint y i, f (splitAt i (simplexPoint y) t) := by
  set τ := Equiv.swap i.castSucc (Fin.last m).castSucc
  set σ := Equiv.swap i (Fin.last m)
  set f' : (Fin (m + 2) → ℝ) → E := fun z => f (z ∘ τ)
  have hττ : ∀ z : Fin (m + 2) → ℝ, z ∘ τ ∘ τ = z := fun z => by
    funext k; simp [τ, Equiv.swap_apply_self]
  have hf' : IntegrableOn (fun x => f' (simplexPoint x)) (simplexSet (m + 1)) :=
    (integrableOn_simplex_comp_perm_iff τ f).mpr hf
  have hI : ∫ x in simplexSet (m + 1), f (simplexPoint x) =
      ∫ x in simplexSet (m + 1), f' (simplexPoint x) :=
    (integral_simplex_comp_perm τ f).symm
  obtain ⟨h1, h2⟩ := integral_simplex_splitAt_last hm hf'
  set h : (Fin (m + 1) → ℝ) → E := fun z => ∫ t in (0 : ℝ)..z (Fin.last m),
    f' (splitAt (Fin.last m) z t)
  have hpt : ∀ y : Fin m → ℝ, h (simplexPoint y ∘ σ) =
      ∫ t in (0 : ℝ)..simplexPoint y i, f (splitAt i (simplexPoint y) t) := fun y => by
    simp only [h, f', Function.comp_apply, σ, Equiv.swap_apply_right]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [← splitAt_comp_swap i (simplexPoint y) t]
  refine ⟨?_, ?_⟩
  · have := (integrableOn_simplex_comp_perm_iff σ h).mpr h1
    simpa only [hpt] using this
  · rw [hI, h2, ← integral_simplex_comp_perm σ h]
    simp only [hpt]

/-- **The group-volume factor**: if `f` depends on the pair `(t, zᵢ - t)` only through its sum,
the inner integral of the merging formula is `zᵢ • f(splitAt i z 0)`. -/
theorem integral_splitAt_of_forall_eq [CompleteSpace E] (i : Fin (m + 1)) (z : Fin (m + 1) → ℝ)
    {f : (Fin (m + 2) → ℝ) → E} (hf : ∀ t, f (splitAt i z t) = f (splitAt i z 0)) :
    ∫ t in (0 : ℝ)..z i, f (splitAt i z t) = z i • f (splitAt i z 0) := by
  simp only [hf]
  rw [intervalIntegral.integral_const, sub_zero]

end QED.Integration.SimplexMerge

end
