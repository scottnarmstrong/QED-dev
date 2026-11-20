/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Corner
public import QED.GradedProof.RPi4CollapsePiece

/-!
# (R-Π₄) step L6d1/L6d2: the sector partition and the rate of one piece

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), steps L6d1/L6d2. In the
chain sums of a collapsed piece the three pair sums `faceSum = Z₂ + Z₃`, `faceSum0 = Z₁ + Z₃`,
`ferSum = Z₁ + Z₂` add up to `2` and are each at most `1`, so for `ρ₀ < 1/2` at most one of them
is `≤ ρ₀`: the two faces, the loop-UV corner and the bulk partition the simplex
(`sector_indicator_eq`, `integral_sector_eq`). Adding the four sector rates
(`face_rate_loop1`, `face_rate_loop0`, `corner_rate`, `bulk_rate`) gives, for one piece and
uniformly over a family, `‖u ∫ pieceF - L‖ ≤ C u^{-1/2}` for `u ≥ 1` (`piece_rate`), where `L`
is the sum of the two face limits. The lower bound on `V₀` is asked in the single form
`V₀ ≥ c₀ · ferSum` where `U ≠ 0` (the form of P0, `symanzikV_vp_ge_fermion`).
`integrableOn_pieceF` gives the integrability of `pieceF` from that of the photon-weighted
coefficients.
-/

@[expose] public section

open MeasureTheory Set Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex)

variable {m : ℕ}

section Partition

variable {α : Fin (m + 1) → Fin 2 → ℝ}
  (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
  {z : Fin (m + 1) → ℝ} (hz : ∀ l, 0 ≤ z l) (hz1 : ∑ l, z l = 1)
include hrow hz hz1

/-- The three pair sums add up to `2`, and each is at most `1`. -/
theorem pairSums_simplex :
    faceSum α z + faceSum0 α z + ferSum α z = 2 ∧ faceSum α z ≤ 1 ∧ faceSum0 α z ≤ 1 ∧
      ferSum α z ≤ 1 := by
  rw [faceSum_chain hrow, faceSum0_chain hrow, ferSum_chain hrow]
  rw [sum_chain hrow] at hz1
  have h1 := chainZ_nonneg α hz ![1, 0]
  have h2 := chainZ_nonneg α hz ![0, 1]
  have h3 := chainZ_nonneg α hz ![1, -1]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **The sector partition** (`ρ₀ < 1/2`): at a point of the simplex, a function is the sum of
its restrictions to the two faces, the loop-UV corner and the bulk. -/
theorem sector_indicator_eq {E : Type*} [AddCommMonoid E] (f : (Fin (m + 1) → ℝ) → E) {ρ₀ : ℝ}
    (hρ : ρ₀ < 1 / 2) :
    f z = {w | faceSum α w ≤ ρ₀}.indicator f z + {w | faceSum0 α w ≤ ρ₀}.indicator f z +
      (cornerSet α ρ₀).indicator f z + (bulkSet α ρ₀).indicator f z := by
  obtain ⟨hs, ha1, hb1, hc1⟩ := pairSums_simplex hrow hz hz1
  rcases le_or_gt (faceSum α z) ρ₀ with ha | ha
  · have hb : ρ₀ < faceSum0 α z := by linarith
    have hc : ρ₀ < ferSum α z := by linarith
    rw [indicator_of_mem (s := {w | faceSum α w ≤ ρ₀}) ha,
      indicator_of_notMem (s := {w | faceSum0 α w ≤ ρ₀}) (not_le.2 hb),
      indicator_of_notMem (s := cornerSet α ρ₀) (not_le.2 hc),
      indicator_of_notMem (s := bulkSet α ρ₀) (fun h => absurd h.1 (not_lt.2 ha))]
    simp
  rcases le_or_gt (faceSum0 α z) ρ₀ with hb | hb
  · have hc : ρ₀ < ferSum α z := by linarith
    rw [indicator_of_notMem (s := {w | faceSum α w ≤ ρ₀}) (not_le.2 ha),
      indicator_of_mem (s := {w | faceSum0 α w ≤ ρ₀}) hb,
      indicator_of_notMem (s := cornerSet α ρ₀) (not_le.2 hc),
      indicator_of_notMem (s := bulkSet α ρ₀) (fun h => absurd h.2.1 (not_lt.2 hb))]
    simp
  rcases le_or_gt (ferSum α z) ρ₀ with hc | hc
  · rw [indicator_of_notMem (s := {w | faceSum α w ≤ ρ₀}) (not_le.2 ha),
      indicator_of_notMem (s := {w | faceSum0 α w ≤ ρ₀}) (not_le.2 hb),
      indicator_of_mem (s := cornerSet α ρ₀) hc,
      indicator_of_notMem (s := bulkSet α ρ₀) (fun h => absurd h.2.2 (not_lt.2 hc))]
    simp
  · rw [indicator_of_notMem (s := {w | faceSum α w ≤ ρ₀}) (not_le.2 ha),
      indicator_of_notMem (s := {w | faceSum0 α w ≤ ρ₀}) (not_le.2 hb),
      indicator_of_notMem (s := cornerSet α ρ₀) (not_le.2 hc),
      indicator_of_mem (s := bulkSet α ρ₀) ⟨ha, hb, hc⟩]
    simp

end Partition

theorem measurable_faceSum0 (α : Fin (m + 1) → Fin 2 → ℝ) : Measurable (faceSum0 α) := by
  unfold faceSum0
  fun_prop

theorem measurable_ferSum (α : Fin (m + 1) → Fin 2 → ℝ) : Measurable (ferSum α) := by
  unfold ferSum
  fun_prop

theorem measurableSet_bulkSet (α : Fin (m + 1) → Fin 2 → ℝ) (ρ₀ : ℝ) :
    MeasurableSet (bulkSet α ρ₀) :=
  (measurableSet_lt measurable_const (measurable_faceSum α)).inter
    ((measurableSet_lt measurable_const (measurable_faceSum0 α)).inter
      (measurableSet_lt measurable_const (measurable_ferSum α)))

theorem integrableOn_indicator_comp {f : (Fin (m + 1) → ℝ) → ℂ} {S : Set (Fin (m + 1) → ℝ)}
    (hS : MeasurableSet S) (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet m)) :
    IntegrableOn (fun x => S.indicator f (simplexPoint x)) (simplexSet m) := by
  have e : (fun x => S.indicator f (simplexPoint x)) =
      (simplexPoint ⁻¹' S).indicator (fun x => f (simplexPoint x)) := by
    funext x
    by_cases h : simplexPoint x ∈ S
    · rw [indicator_of_mem h, indicator_of_mem (show x ∈ simplexPoint ⁻¹' S from h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (show x ∉ simplexPoint ⁻¹' S from h)]
  rw [e]
  exact hf.indicator (hS.preimage continuous_simplexPoint'.measurable)

/-- **The integral over the simplex is the sum of the four sector integrals** (`ρ₀ < 1/2`). -/
theorem integral_sector_eq {α : Fin (m + 1) → Fin 2 → ℝ}
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1]) {ρ₀ : ℝ} (hρ : ρ₀ < 1 / 2)
    {f : (Fin (m + 1) → ℝ) → ℂ} (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet m)) :
    ∫ x in simplexSet m, f (simplexPoint x) =
      (∫ x in simplexSet m, {w | faceSum α w ≤ ρ₀}.indicator f (simplexPoint x)) +
      (∫ x in simplexSet m, {w | faceSum0 α w ≤ ρ₀}.indicator f (simplexPoint x)) +
      (∫ x in simplexSet m, (cornerSet α ρ₀).indicator f (simplexPoint x)) +
      ∫ x in simplexSet m, (bulkSet α ρ₀).indicator f (simplexPoint x) := by
  have h1 := integrableOn_indicator_comp (S := {w | faceSum α w ≤ ρ₀})
    (measurableSet_le (measurable_faceSum α) measurable_const) hf
  have h2 := integrableOn_indicator_comp (S := {w | faceSum0 α w ≤ ρ₀})
    (measurableSet_le (measurable_faceSum0 α) measurable_const) hf
  have h3 := integrableOn_indicator_comp (S := cornerSet α ρ₀) (measurableSet_le
    (measurable_ferSum α) measurable_const) hf
  have h4 := integrableOn_indicator_comp (measurableSet_bulkSet α ρ₀) hf
  set A := fun x => {w | faceSum α w ≤ ρ₀}.indicator f (simplexPoint x)
  set B := fun x => {w | faceSum0 α w ≤ ρ₀}.indicator f (simplexPoint x)
  set C := fun x => (cornerSet α ρ₀).indicator f (simplexPoint x)
  set D := fun x => (bulkSet α ρ₀).indicator f (simplexPoint x)
  have e3 : ∫ x in simplexSet m, (A x + B x + C x + D x) =
      (∫ x in simplexSet m, (A x + B x + C x)) + ∫ x in simplexSet m, D x :=
    integral_add ((h1.add h2).add h3) h4
  have e2 : ∫ x in simplexSet m, (A x + B x + C x) =
      (∫ x in simplexSet m, (A x + B x)) + ∫ x in simplexSet m, C x :=
    integral_add (h1.add h2) h3
  have e1 : ∫ x in simplexSet m, (A x + B x) =
      (∫ x in simplexSet m, A x) + ∫ x in simplexSet m, B x := integral_add h1 h2
  rw [← e1, ← e2, ← e3]
  refine setIntegral_congr_fun (measurableSet_simplexSet m) fun x hx => ?_
  obtain ⟨hz, hz1⟩ := simplexPoint_mem_stdSimplex hx
  exact sector_indicator_eq hrow hz hz1 f hρ

/-- **Integrability of the collapsed integrand** from that of the photon-weighted coefficients and
a lower bound `v ≥ c > 0` of the shifted `V` where `U ≠ 0` (where `U = 0`, `pieceF = 0`). -/
theorem integrableOn_pieceF {n : ℕ} {Q : LoopQuartic} {α : Fin (m + 1) → Fin 2 → ℝ}
    {pp : Fin (m + 1) → Fin 4 → ℝ} {M : Fin (m + 1) → ℝ} {γ₀ : Fin (m + 1)} {u c : ℝ}
    (hc : 0 < c)
    (k1 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cOneAt n Q α pp (simplexPoint y))
      (simplexSet m))
    (k2 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cTwoAt n Q α pp (simplexPoint y))
      (simplexSet m))
    (k3 : IntegrableOn (fun y => (simplexPoint y γ₀ : ℂ) * cThreeAt n Q α (simplexPoint y))
      (simplexSet m))
    (hV : ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      c ≤ symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u) :
    IntegrableOn (fun y => pieceF n Q α pp M γ₀ u (simplexPoint y)) (simplexSet m) := by
  set V : (Fin m → ℝ) → ℝ := fun y => symanzikV α pp M (simplexPoint y) + simplexPoint y γ₀ * u
  have e : (fun y => pieceF n Q α pp M γ₀ u (simplexPoint y)) = fun y =>
      (simplexPoint y γ₀ : ℂ) * cOneAt n Q α pp (simplexPoint y) * (((V y : ℂ)) ^ (n - 3))⁻¹ +
      (simplexPoint y γ₀ : ℂ) * cTwoAt n Q α pp (simplexPoint y) * (((V y : ℂ)) ^ (n - 4))⁻¹ +
      (simplexPoint y γ₀ : ℂ) * cThreeAt n Q α (simplexPoint y) *
        (((V y : ℂ)) ^ (n - 5))⁻¹ := by
    funext y
    simp only [pieceF, paramAtV_eq, V]
    ring
  have hzm : Measurable fun y : Fin m → ℝ => simplexPoint y γ₀ :=
    (continuous_apply γ₀).measurable.comp continuous_simplexPoint'.measurable
  have hVm : Measurable V :=
    ((measurable_symanzikV α pp M).comp continuous_simplexPoint'.measurable).add
      (hzm.mul measurable_const)
  have hw : ∀ k : ℕ, Measurable fun y => (((V y : ℂ)) ^ k)⁻¹ := fun k =>
    ((Complex.measurable_ofReal.comp hVm).pow_const k).inv
  have hb : ∀ k : ℕ, ∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) ≠ 0 →
      ‖(((V y : ℂ)) ^ k)⁻¹‖ ≤ (c ^ k)⁻¹ := fun k y hy hU => by
    have hcv := hV y hy hU
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hc.le.trans hcv)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le hcv k)
  have term : ∀ (g : (Fin m → ℝ) → ℂ) (k : ℕ), IntegrableOn g (simplexSet m) →
      (∀ y ∈ simplexSet m, symanzikU α (simplexPoint y) = 0 → g y = 0) →
      IntegrableOn (fun y => g y * (((V y : ℂ)) ^ k)⁻¹) (simplexSet m) := fun g k hg hg0 => by
    refine (hg.norm.mul_const (c ^ k)⁻¹).mono' (hg.aestronglyMeasurable.mul
      (hw k).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem (measurableSet_simplexSet m) fun y hy => ?_
    rw [norm_mul]
    by_cases hU : symanzikU α (simplexPoint y) = 0
    · rw [hg0 y hy hU, norm_zero, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (hb k y hy hU) (norm_nonneg _)
  rw [e]
  refine ((term _ _ k1 fun y _ hU => ?_).add (term _ _ k2 fun y _ hU => ?_)).add
    (term _ _ k3 fun y _ hU => ?_) <;> simp [cOneAt, cTwoAt, cThreeAt, hU]

/-- **The rate of one collapsed piece, uniform over a family**: for a piece with a unique photon
line `γ₀`, rows `(1,0)`, `(0,1)`, `(1,-1)` with both faces present, momenta `cs • k` with
`‖k‖ ≤ KP`, bounded masses, uniformly bounded numerators `Q` (and, for the two faces, uniformly
bounded representatives `Q₁`, `Q₀` of the same polynomial of degree `≤ 3` along loop `1`,
resp. `0`, and `≤ 1` when that face block has two lines), `n ∈ {6, 7}`, `n - 3 < m`, and
`V₀ ≥ c₀ · ferSum` where `U ≠ 0`: there are `C` and `L` with `‖u ∫ pieceF - L‖ ≤ C u^{-1/2}` for `u ≥ 1` wherever
`pieceF` is integrable. -/
theorem piece_rate {ι : Type*} {n : ℕ} (hnm : n - 3 < m) (α : Fin (m + 1) → Fin 2 → ℝ)
    (γ₀ : Fin (m + 1)) (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hA1 : 2 ≤ (Finset.univ.filter fun l => α l ≠ ![1, 0]).card) (hR1 : ∃ l, α l = ![1, 0])
    (hA0 : 2 ≤ (Finset.univ.filter fun l => α l ≠ ![0, 1]).card) (hR0 : ∃ l, α l = ![0, 1])
    (cs : Fin (m + 1) → ℝ) (k : ι → Fin 4 → ℝ) (M : ι → Fin (m + 1) → ℝ)
    (Q Q₁ Q₀ : ι → LoopQuartic) {BQ B₁ B₀ : ℝ} (hQ : LQBdd Q BQ) (hQ₁ : LQBdd Q₁ B₁)
    (hQ₀ : LQBdd Q₀ B₀) (he₁ : ∀ s, (Q₁ s).eval = (Q s).eval)
    (he₀ : ∀ s, (Q₀ s).eval = (Q s).eval)
    (hd1 : ∀ s, LoopDegLe 1 3 (Q₁ s))
    (hd11 : (Finset.univ.filter fun l => α l ≠ ![1, 0]).card = 2 → ∀ s, LoopDegLe 1 1 (Q₁ s))
    (hd0 : ∀ s, LoopDegLe 0 3 (Q₀ s))
    (hd01 : (Finset.univ.filter fun l => α l ≠ ![0, 1]).card = 2 → ∀ s, LoopDegLe 0 1 (Q₀ s))
    (hn : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0 ∧ (Q₁ s).quart = 0 ∧ (Q₀ s).quart = 0))
    {KP KM c₀ : ℝ} (hk : ∀ s, ‖k s‖ ≤ KP) (hM : ∀ s l, |M s l| ≤ KM) (hc₀ : 0 < c₀)
    (hV : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → symanzikU α w ≠ 0 →
      c₀ * ferSum α w ≤ symanzikV α (fun i => cs i • k s) (M s) w) :
    ∃ C : ℝ, ∃ L : ι → ℂ, ∀ s, ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x))
        (simplexSet m) →
      ‖u • (∫ x in simplexSet m,
          pieceF n (Q s) α (fun i => cs i • k s) (M s) γ₀ u (simplexPoint x)) - L s‖ ≤
        C * u ^ (-(1 / 2) : ℝ) := by
  have hγ : α γ₀ = ![1, -1] := (huniq γ₀).mpr rfl
  set ρ₀ : ℝ := 1 / 4 with hρ₀
  set c₁ : ℝ := c₀ / 4 with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set pp : ι → Fin (m + 1) → Fin 4 → ℝ := fun s i => cs i • k s with hpp
  set KP' : ℝ := (∑ l, |cs l|) * KP
  have hP : ∀ s l, ‖pp s l‖ ≤ KP' := fun s l => by
    simp only [hpp, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (Finset.single_le_sum (f := fun l => |cs l|) (fun l _ => abs_nonneg _)
      (Finset.mem_univ l)) (hk s) (norm_nonneg _) (Finset.sum_nonneg fun l _ => abs_nonneg _)
  have hkμ : ∀ s μ, |k s μ| ≤ KP := fun s μ => (norm_le_pi_norm (k s) μ).trans (hk s)
  -- the lower bounds of `V₀` in the forms the four sectors ask for
  have hVface : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w γ₀ ≤ ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) w := fun s w hw hw1 hU h => by
    have := hV s w hw hw1 hU
    rw [ferSum_eq_one_sub huniq hw1] at this
    have h' : w γ₀ ≤ 1 / 4 := h
    have : c₀ * (3 / 4) ≤ c₀ * (1 - w γ₀) := mul_le_mul_of_nonneg_left (by linarith) hc₀.le
    linarith
  have hVbulk : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      w ∈ bulkSet α ρ₀ → c₁ ≤ symanzikV α (pp s) (M s) w := fun s w hw hw1 hb => by
    have hU := symanzikU_ge_bulk hrow w (by norm_num) hw hw1 hb
    have := hV s w hw hw1 (by positivity)
    have : c₀ * (1 / 4) ≤ c₀ * ferSum α w := mul_le_mul_of_nonneg_left hb.2.2.le hc₀.le
    linarith
  have hVcorner : ∀ s (w : Fin (m + 1) → ℝ), (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      w ∈ cornerSet α ρ₀ → symanzikU α w ≠ 0 → 0 ≤ symanzikV α (pp s) (M s) w :=
    fun s w hw hw1 _ hU => by
      have := hV s w hw hw1 hU
      have : 0 ≤ c₀ * ferSum α w := mul_nonneg hc₀.le (Finset.sum_nonneg fun l _ => hw l)
      linarith
  have hm0 : 0 < m := by rcases hn with rfl | ⟨rfl, -⟩ <;> omega
  have hnQ : n = 7 ∨ (n = 6 ∧ ∀ s, (Q s).quart = 0) := by
    rcases hn with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, fun s => (h' s).1⟩
  have hnQ₁ : n = 7 ∨ (n = 6 ∧ ∀ s, (Q₁ s).quart = 0) := by
    rcases hn with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, fun s => (h' s).2.1⟩
  have hnQ₀ : n = 7 ∨ (n = 6 ∧ ∀ s, (Q₀ s).quart = 0) := by
    rcases hn with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, fun s => (h' s).2.2⟩
  have hF : ∀ (P : ι → LoopQuartic), (∀ s, (P s).eval = (Q s).eval) →
      ∀ s, pieceF n (P s) α (pp s) (M s) γ₀ = pieceF n (Q s) α (pp s) (M s) γ₀ :=
    fun P hP s => by
      funext u z
      simp only [pieceF, paramAtV_congr (hP s)]
  obtain ⟨C₁, L₁, h₁⟩ := face_rate_loop1 α γ₀ hγ hrow hA1 hR1 pp M n Q₁ hQ₁ hd1 hd11 hnQ₁
    (by norm_num) (by norm_num) hc₁0 hP hM hVface
  obtain ⟨C₀, L₀, h₀⟩ := face_rate_loop0 α γ₀ hγ hrow hA0 hR0 pp M n Q₀ hQ₀ hd0 hd01 hnQ₀
    (by norm_num) (by norm_num) hc₁0 hP hM hVface
  simp only [hF Q₁ he₁] at h₁
  simp only [hF Q₀ he₀] at h₀
  obtain ⟨Cc, hc⟩ := corner_rate hnm α γ₀ huniq hrow cs k M Q hQ hnQ (by norm_num) (by norm_num)
    hkμ hVcorner
  obtain ⟨Cb, hb⟩ := bulk_rate hm0 α γ₀ hrow pp M n Q hQ hnQ (by norm_num) hc₁0 hP hVbulk
  refine ⟨C₁ + C₀ + |Cc| + Cb, fun s => L₁ s + L₀ s, fun s u hu hI => ?_⟩
  have hu0 : 0 < u := one_pos.trans_le hu
  have hsplit := integral_sector_eq hrow (ρ₀ := ρ₀) (by norm_num) hI
  have e1 := h₁ s u hu0 hI
  have e0 := h₀ s u hu0 hI
  have ec := hc s u hu
  have eb := hb s u hu0
  have hinv : u⁻¹ ≤ u ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
  have ec' : ‖u • ∫ x in simplexSet m, (cornerSet α ρ₀).indicator
      (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)‖ ≤ |Cc| * u ^ (-(1 / 2) : ℝ) :=
    ec.trans (mul_le_mul (le_abs_self _) hinv (by positivity) (abs_nonneg _))
  rw [hsplit, smul_add, smul_add, smul_add]
  set a := u • ∫ x in simplexSet m, {w | faceSum α w ≤ ρ₀}.indicator
    (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)
  set b := u • ∫ x in simplexSet m, {w | faceSum0 α w ≤ ρ₀}.indicator
    (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)
  set c := u • ∫ x in simplexSet m, (cornerSet α ρ₀).indicator
    (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)
  set d := u • ∫ x in simplexSet m, (bulkSet α ρ₀).indicator
    (pieceF n (Q s) α (pp s) (M s) γ₀ u) (simplexPoint x)
  have e : a + b + c + d - (L₁ s + L₀ s) = (a - L₁ s) + (b - L₀ s) + c + d := by ring
  rw [e]
  calc ‖(a - L₁ s) + (b - L₀ s) + c + d‖ ≤ ‖a - L₁ s‖ + ‖b - L₀ s‖ + ‖c‖ + ‖d‖ :=
        norm_add₄_le
    _ ≤ C₁ * u ^ (-(1 / 2) : ℝ) + C₀ * u ^ (-(1 / 2) : ℝ) + |Cc| * u ^ (-(1 / 2) : ℝ) +
          Cb * u ^ (-(1 / 2) : ℝ) := by gcongr
    _ = _ := by ring

end QED.GradedProof.RPi4

end
