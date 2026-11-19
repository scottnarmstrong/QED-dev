/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0OneLoop
public import QED.TwoLoop.ClassIntegrableLoopPoly

/-!
# (X₀): (T₉′) at one loop for a numerator built from affine factors

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57), for the one-loop
contractions with a counterterm vertex. `AffPoly d N` says that the numerator `N(ℓ)` is a sum of
products of at most `d` factors affine in the loop momentum `ℓ` (electron numerators, the
`fermionCt` vertex factor, and the two factors of the `photonCt` vertex factor). If the one-loop
integrand has `n` lines with nonzero loop coefficients, `d ≤ 4`, and `4 + d < 2n`, it satisfies
(T₉′) for `ε > 0` and any masses (`jointEnergyFirstIntegrable_oneLoop_affPoly`).

## Proof

As in `jointEnergyFirstIntegrable_oneLoop`, with the auxiliary loop of power four. All lines of
the one-loop part are parallel in the two-loop data, so each affine factor of a term may be
bounded by any one of them: a term with `j ≤ d` factors is bounded by `j` of `d` fixed lines
(`refinedBound_affPoly`), and the cubic (`d ≤ 3`) or refined (`d = 4`, then `n ≥ 5`) two-loop
theorem applies.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.X0

open QED.TwoLoop.Bridge (propDenom IsLoopPoly isLoopAffine_lineMomentum)
open QED.Integration.TwoLoop (lineDenom lineMomentum RefinedBound refinedBound_lineMomentum
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined)

/-- `N` is a sum of products of at most `d` factors affine in `k ∈ ℝ⁴`. -/
inductive AffPoly : ℕ → ((Fin 4 → ℝ) → ℂ) → Prop
  | const (z : ℂ) : AffPoly 0 fun _ => z
  | aff (u : ℂ) (w : Fin 4 → ℂ) : AffPoly 1 fun k => u + ∑ ν, w ν * (k ν : ℂ)
  | mul {d d' : ℕ} {N N' : (Fin 4 → ℝ) → ℂ} : AffPoly d N → AffPoly d' N' →
      AffPoly (d + d') fun k => N k * N' k
  | add {d : ℕ} {N N' : (Fin 4 → ℝ) → ℂ} : AffPoly d N → AffPoly d N' →
      AffPoly d fun k => N k + N' k
  | mono {d d' : ℕ} {N : (Fin 4 → ℝ) → ℂ} : d ≤ d' → AffPoly d N → AffPoly d' N

namespace AffPoly

theorem const' (d : ℕ) (z : ℂ) : AffPoly d fun _ => z := mono (Nat.zero_le d) (const z)

theorem const_mul {d : ℕ} {N : (Fin 4 → ℝ) → ℂ} (z : ℂ) (h : AffPoly d N) :
    AffPoly d fun k => z * N k := by
  simpa using (const z).mul h

theorem sum {ι : Type*} (s : Finset ι) {d : ℕ} {N : ι → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, AffPoly d (N i)) : AffPoly d fun k => ∑ i ∈ s, N i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const' d 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) {N : ι → (Fin 4 → ℝ) → ℂ}
    (h : ∀ i ∈ s, AffPoly (d i) (N i)) :
    AffPoly (∑ i ∈ s, d i) fun k => ∏ i ∈ s, N i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- An affine function of an affine momentum `c k + p`. -/
theorem comp_affine {G : (Fin 4 → ℝ) → ℂ}
    (hG : ∃ u : ℂ, ∃ w : Fin 4 → ℂ, ∀ k, G k = u + ∑ ν, w ν * (k ν : ℂ)) (c : ℝ)
    (p : Fin 4 → ℝ) : AffPoly 1 fun k => G (c • k + p) := by
  obtain ⟨u, w, hG⟩ := hG
  have h := aff (u + ∑ ν, w ν * (p ν : ℂ)) fun ν => w ν * c
  refine (congrArg (AffPoly 1) (funext fun k => ?_)).mp h
  rw [hG]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofReal_add, ofReal_mul, mul_add,
    Finset.sum_add_distrib]
  ring_nf
  simp only [add_assoc, mul_comm, mul_left_comm]

/-- The degree bound: `N(ℓ₀)` is a polynomial of degree at most `d` in the loop momenta. -/
theorem isLoopPoly {d : ℕ} {N : (Fin 4 → ℝ) → ℂ} (h : AffPoly d N) :
    IsLoopPoly 2 d fun ℓ => N (ℓ 0) := by
  induction h with
  | const z => exact IsLoopPoly.const z
  | aff u w => exact (IsLoopPoly.const u).add (IsLoopPoly.sum _ fun ν _ =>
      (IsLoopPoly.coord 0 ν le_rfl).const_mul (w ν))
  | mul _ _ ih ih' => exact ih.mul ih'
  | add _ _ ih ih' => exact ih.add ih'
  | mono hd _ ih => exact ih.mono hd

end AffPoly

variable {n : ℕ}

/-- A coordinate of `ℓ₀` is bounded by any one-loop line of the auxiliary data. -/
theorem refinedBound_coord (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0) (i : Fin n) (ν : Fin 4) :
    RefinedBound (auxDir c) {Fin.castAdd 4 i} 1 fun ℓ => ((ℓ 0 ν : ℝ) : ℂ) := by
  have h := (refinedBound_lineMomentum (auxDir c) (auxShift fun _ => 0) (Fin.castAdd 4 i)
    ν).const_mul ((c i)⁻¹ : ℂ)
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [lineMomentum_auxDir_castAdd]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, ofReal_mul]
  field_simp [ofReal_ne_zero.mpr (hc i)]

/-- **The pointwise bound for an `AffPoly` numerator**, by any `d` one-loop lines. -/
theorem refinedBound_affPoly (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0) {d : ℕ}
    {N : (Fin 4 → ℝ) → ℂ} (h : AffPoly d N) :
    ∀ E : Finset (Fin n), E.card = d →
      RefinedBound (auxDir c) (E.image (Fin.castAdd 4)) d fun ℓ => N (ℓ 0) := by
  classical
  induction h with
  | const z =>
    intro E hE
    rw [Finset.card_eq_zero.mp hE, Finset.image_empty]
    exact RefinedBound.const z
  | aff u w =>
    intro E hE
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hE
    rw [Finset.image_singleton]
    exact ((RefinedBound.const u).mono (Finset.empty_subset _) (Nat.zero_le _)).add
      (RefinedBound.sum _ fun ν _ => (refinedBound_coord c hc i ν).const_mul (w ν))
  | @mul d d' N N' _ _ ih ih' =>
    intro E hE
    obtain ⟨E₁, hE₁, hc₁⟩ := Finset.exists_subset_card_eq (s := E) (n := d) (by omega)
    have hc₂ : (E \ E₁).card = d' := by rw [Finset.card_sdiff_of_subset hE₁]; omega
    have hm := (ih E₁ hc₁).mul (ih' (E \ E₁) hc₂) (by
      rw [Finset.disjoint_image (Fin.castAdd_injective _ _)]
      exact Finset.disjoint_sdiff)
    rwa [← Finset.image_union, Finset.union_sdiff_of_subset hE₁] at hm
  | add _ _ ih ih' => exact fun E hE => (ih E hE).add (ih' E hE)
  | @mono d d' N hd _ ih =>
    intro E hE
    obtain ⟨E₁, hE₁, hc₁⟩ := Finset.exists_subset_card_eq (s := E) (n := d) (by omega)
    exact (ih E₁ hc₁).mono (Finset.image_subset_image hE₁) hd

/-- **(T₉′) at one loop for an `AffPoly` numerator.** Lines `i` carry `cᵢ ℓ + qᵢ` with
`cᵢ ≠ 0`; the numerator is `AffPoly d` with `d ≤ 4` and `4 + d < 2n`. Then for `ε > 0` and any
masses the one-loop integrand satisfies (T₉′). -/
theorem jointEnergyFirstIntegrable_oneLoop_affPoly (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0)
    (q : Fin n → Fin 4 → ℝ) (Ms : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : d ≤ 4)
    (hcount : 4 + d < 2 * n) {N : (Fin 4 → ℝ) → ℂ} (hN : AffPoly d N) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      N (ℓ 0) * ∏ i, (propDenom (Ms i) ε (c i • ℓ 0 + q i))⁻¹ := by
  classical
  obtain ⟨E, -, hE⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := d) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  have hB := (refinedBound_affPoly c hc hN E hE).mono le_rfl hd
  have hcr := noSubdivergenceRefined_auxDir c hc E (by rw [hE]; exact hcount)
  set F : (Fin 4 → ℝ) → ℂ := fun k => N k * ∏ i, (propDenom (Ms i) ε (c i • k + q i))⁻¹ with hF
  have hfun : ∀ G : (Fin 2 → Fin 4 → ℝ) → ℂ, (∀ ℓ, G ℓ = N (ℓ 0)) →
      (fun ℓ => G ℓ * ∏ i, (lineDenom (auxDir c) (auxShift q) (auxMass Ms 0) ε i ℓ)⁻¹) =
        fun ℓ => F (ℓ 0) * ((propDenom 0 ε (ℓ 1))⁻¹) ^ 4 := by
    intro G hG
    funext ℓ
    rw [Fin.prod_univ_add (a := n) (b := 4), hG]
    simp only [hF, QED.TwoLoop.Bridge.lineDenom_eq_propDenom, lineMomentum_auxDir_castAdd,
      lineMomentum_auxDir_natAdd, auxMass, Fin.addCases_left, Fin.addCases_right,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hJ : QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      F (ℓ 0) * ((propDenom 0 ε (ℓ 1))⁻¹) ^ 4 := by
    rcases Nat.lt_or_ge d 4 with h3 | h4
    · obtain ⟨Q, hq, hQ⟩ := SE2.IsLoopPoly.exists_loopQuartic_cubic (hN.isLoopPoly.mono
        (by omega : d ≤ 3))
      rw [← hQ] at hB
      have h := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic Q
        (auxDir c) (auxShift q) (auxMass Ms 0) hq (by omega : 6 ≤ n + 3) hε hcr hB
      rwa [hfun Q.eval (fun ℓ => by rw [hQ])] at h
    · obtain ⟨Q, hQ⟩ := (hN.isLoopPoly.mono hd).exists_loopQuartic
      rw [← hQ] at hB
      have h := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined Q
        (auxDir c) (auxShift q) (auxMass Ms 0) (by omega : 7 ≤ n + 3) hε hcr hB
      rwa [hfun Q.eval (fun ℓ => by rw [hQ])] at h
  obtain ⟨h₁, h₂⟩ := energyFirst_of_mul_aux4 (F := F) 0 hε hJ
  exact jointEnergyFirstIntegrable_one_of_energyFirst h₁ h₂

/-- `jointEnergyFirstIntegrable_oneLoop_affPoly` with the lines indexed by any finite type. -/
theorem jointEnergyFirstIntegrable_oneLoop_affPoly' {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (hc : ∀ i, c i ≠ 0) (q : ι → Fin 4 → ℝ) (Ms : ι → ℝ) {ε : ℝ} (hε : 0 < ε) {d : ℕ}
    (hd : d ≤ 4) (hcount : 4 + d < 2 * Fintype.card ι) {N : (Fin 4 → ℝ) → ℂ} (hN : AffPoly d N) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      N (ℓ 0) * ∏ i, (propDenom (Ms i) ε (c i • ℓ 0 + q i))⁻¹ := by
  set e := Fintype.equivFin ι
  have h := jointEnergyFirstIntegrable_oneLoop_affPoly (fun i => c (e.symm i)) (fun i => hc _)
    (fun i => q (e.symm i)) (fun i => Ms (e.symm i)) hε hd hcount hN
  refine (congrArg _ (funext fun ℓ => ?_)).mp h
  rw [Equiv.prod_comp e.symm (fun i => (propDenom (Ms i) ε (c i • ℓ 0 + q i))⁻¹)]

end QED.GradedProof.X0

end
