/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X0TwoLoop
public import QED.TwoLoop.IntegrableOrderFiveTransfer
public import QED.TwoLoop.CountertermLimitProduct

/-!
# (X₀): (T₉′) at one loop through an auxiliary loop of power four

Helper level for the Phase 5 Stage 2 goal (X₀)
`QED.Graded.jointEnergyFirstIntegrable_connectedPart_five` (decision D-57). Let `n` lines carry
the momenta `cᵢ ℓ + qᵢ` (`cᵢ ≠ 0`) with masses `Mᵢ`, and let a set `E` of at most three of them
carry a numerator factor affine in the line momentum. If `4 + |E| < 2n`, then for `ε > 0` and any
masses the one-loop integrand `z ∏_{i ∈ E} gᵢ(kᵢ) ∏ᵢ (kᵢ² + Mᵢ² - iε)⁻¹` satisfies (T₉′)
(`jointEnergyFirstIntegrable_oneLoop`).

## Proof

Multiply by the auxiliary loop `(ℓ₁² - iε)⁻⁴`: the product is a two-loop integrand with `n + 4 ≥ 7`
lines, numerator of degree `|E| ≤ 3`, and the numerator-aware criterion holds (`n` lines along
`ℓ₀`, four along `ℓ₁`), so the cubic two-loop theorem gives (T₉′). The energy integral of the
auxiliary loop is `K (-(v⃗² - iε))^{-7/2}` with `K = ∫ (1 + s²)⁻⁴ > 0` (continuation to the slit
plane), which vanishes nowhere; so the one-loop factor is recovered
(`energyFirst_of_mul_aux4`).
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.GradedProof.X0

open QED.TwoLoop.Bridge (propDenom IsLoopPoly isLoopAffine_lineMomentum)
open QED.Integration.TwoLoop (lineDenom lineMomentum RefinedBound NoSubdivergenceRefined pairDet
  refinedBound_lineMomentum jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic)

/-! ### The auxiliary loop of power four -/

theorem integral_inv_one_add_sq_pow_four_pos : 0 < ∫ s : ℝ, ((1 + s ^ 2) ^ 4)⁻¹ := by
  refine (integral_pos_iff_support_of_nonneg (fun s => by simp only [Pi.zero_apply]; positivity)
    (QED.Integration.integrable_inv_one_add_sq_pow 4 (by norm_num))).mpr ?_
  have : Function.support (fun s : ℝ => ((1 + s ^ 2) ^ 4)⁻¹) = Set.univ :=
    Set.eq_univ_iff_forall.mpr fun s => Function.mem_support.mpr (by positivity)
  rw [this, Real.volume_univ]
  exact ENNReal.zero_lt_top

/-- The energy integral of the auxiliary loop of power four. -/
theorem integral_aux4_eq (M : ℝ) {ε : ℝ} (hε : 0 < ε) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, ((propDenom M ε (Fin.cons t v))⁻¹) ^ 4 =
      ((∫ s : ℝ, ((1 + s ^ 2) ^ 4)⁻¹ : ℝ) : ℂ) *
        (-((((∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - (ε : ℂ) * I)) ^ ((1 / 2 : ℂ) - (4 : ℕ)) := by
  set z := -((((∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - (ε : ℂ) * I) with hz
  have hpt : ∀ t : ℝ, ((propDenom M ε (Fin.cons t v))⁻¹) ^ 4 =
      ((t : ℂ) ^ 2 + z) ^ (-((4 : ℕ) : ℤ)) := by
    intro t
    have hx : (((-t ^ 2 + ∑ k, v k ^ 2 + M ^ 2 : ℝ)) : ℂ) - (ε : ℂ) * I = -((t : ℂ) ^ 2 + z) := by
      rw [hz]
      push_cast
      ring
    rw [propDenom, QED.TwoLoop.CountertermLimit.dot_cons_self, hx, inv_pow,
      Even.neg_pow (by decide), zpow_neg, zpow_natCast]
  simp_rw [hpt]
  exact QED.Integration.integral_sq_add_zpow_of_real 4 (by norm_num) _
    (fun a ha => QED.Integration.integral_sq_add_zpow_ofReal 4 ha rfl)
    (QED.TwoLoop.CountertermLimit.neg_aux_mem_slitPlane hε v)

/-- The energy integrals of the auxiliary loop of power four vanish nowhere at `ε > 0`. -/
theorem integral_aux4_ne_zero (M : ℝ) {ε : ℝ} (hε : 0 < ε) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, ((propDenom M ε (Fin.cons t v))⁻¹) ^ 4 ≠ 0 := by
  rw [integral_aux4_eq M hε v]
  refine mul_ne_zero (ofReal_ne_zero.mpr integral_inv_one_add_sq_pow_four_pos.ne') ?_
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl (slitPlane_ne_zero (QED.TwoLoop.CountertermLimit.neg_aux_mem_slitPlane hε v))

/-- **One-loop integrability out of a product with the auxiliary loop of power four.** -/
theorem energyFirst_of_mul_aux4 {F : (Fin 4 → ℝ) → ℂ} (M : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hJ : QED.TwoLoop.jointEnergyFirstIntegrable 2 fun ℓ =>
      F (ℓ 0) * ((propDenom M ε (ℓ 1))⁻¹) ^ 4) :
    (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => F (Fin.cons t v)) ∧
      Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t v) :=
  QED.TwoLoop.IntegrableOrderFive.energyFirst_of_jointEnergyFirstIntegrable_mul
    (H := fun k => ((propDenom M ε k)⁻¹) ^ 4)
    (fun k => pow_ne_zero _ (inv_ne_zero (QED.TwoLoop.Bridge.propDenom_ne_zero hε.ne' k)))
    (integral_aux4_ne_zero M hε) hJ

/-- (T₉′) with one loop momentum from the two stages of the energy-first integral. -/
theorem jointEnergyFirstIntegrable_one_of_energyFirst {G : (Fin 4 → ℝ) → ℂ}
    (h₁ : ∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => G (Fin.cons t v))
    (h₂ : Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, G (Fin.cons t v)) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ => G (ℓ 0) := by
  simpa using QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_one_sub h₁ h₂ 0

/-! ### The two-loop data of a one-loop integrand times the auxiliary loop -/

variable {n : ℕ}

/-- Directions: line `i < n` carries `cᵢ ℓ₀`, the four auxiliary lines carry `ℓ₁`. -/
def auxDir (c : Fin n → ℝ) : Fin (n + 4) → Fin 2 → ℝ :=
  Fin.addCases (fun i => ![c i, 0]) fun _ => ![0, 1]

/-- Shifts: `qᵢ` on the lines, `0` on the auxiliary lines. -/
def auxShift (q : Fin n → Fin 4 → ℝ) : Fin (n + 4) → Fin 4 → ℝ :=
  Fin.addCases q fun _ => 0

/-- Masses: `Mᵢ` on the lines, `M` on the auxiliary lines. -/
def auxMass (Ms : Fin n → ℝ) (M : ℝ) : Fin (n + 4) → ℝ :=
  Fin.addCases Ms fun _ => M

theorem lineMomentum_auxDir_castAdd (c : Fin n → ℝ) (q : Fin n → Fin 4 → ℝ) (i : Fin n)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (auxDir c) (auxShift q) (Fin.castAdd 4 i) ℓ = c i • ℓ 0 + q i := by
  funext μ
  simp [lineMomentum, auxDir, auxShift, Fin.sum_univ_two]

theorem lineMomentum_auxDir_natAdd (c : Fin n → ℝ) (q : Fin n → Fin 4 → ℝ) (j : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (auxDir c) (auxShift q) (Fin.natAdd n j) ℓ = ℓ 1 := by
  funext μ
  simp [lineMomentum, auxDir, auxShift, Fin.sum_univ_two]

theorem cases_castAdd_natAdd (x : Fin (n + 4)) :
    (∃ i, x = Fin.castAdd 4 i) ∨ ∃ j, x = Fin.natAdd n j :=
  Fin.addCases (motive := fun x : Fin (n + 4) => (∃ i, x = Fin.castAdd 4 i) ∨
    ∃ j, x = Fin.natAdd n j) (fun i => Or.inl ⟨i, rfl⟩) (fun j => Or.inr ⟨j, rfl⟩) x

/-- **The criterion for the one-loop lines and the auxiliary loop.** -/
theorem noSubdivergenceRefined_auxDir (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0) (E : Finset (Fin n))
    (hcount : 4 + E.card < 2 * n) :
    NoSubdivergenceRefined 2 (E.image (Fin.castAdd 4)) (auxDir c) := by
  intro x
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_image
    (fun a _ b _ h => Fin.castAdd_injective _ _ h), Fin.sum_univ_add (a := n) (b := 4)]
  rcases cases_castAdd_natAdd x with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · simp [pairDet, auxDir, hc i]
  · simp [pairDet, auxDir, hc]
    omega

/-- An affine function of a line momentum: degree one, bounded by that line. -/
theorem affine_lineMomentum {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (e : Fin (m + 1)) {G : (Fin 4 → ℝ) → ℂ}
    (hG : ∃ u : ℂ, ∃ w : Fin 4 → ℂ, ∀ k, G k = u + ∑ ν, w ν * (k ν : ℂ)) :
    IsLoopPoly 2 1 (fun ℓ => G (lineMomentum α p e ℓ)) ∧
      RefinedBound α {e} 1 (fun ℓ => G (lineMomentum α p e ℓ)) := by
  obtain ⟨u, w, hG⟩ := hG
  simp only [hG]
  exact ⟨(IsLoopPoly.const u).add (IsLoopPoly.sum _ fun ν _ =>
      ((isLoopAffine_lineMomentum α p e).isLoopPoly_coord ν).const_mul (w ν)),
    ((RefinedBound.const u).mono (Finset.empty_subset _) (Nat.zero_le _)).add
      (RefinedBound.sum _ fun ν _ => (refinedBound_lineMomentum α p e ν).const_mul (w ν))⟩

/-- **(T₉′) at one loop.** Lines `i` carry `cᵢ ℓ + qᵢ` with `cᵢ ≠ 0` and masses `Mᵢ`; the lines
of `E` (at most three) carry numerator factors `gᵢ` affine in their momenta; and
`4 + |E| < 2n`. Then for `ε > 0` and any masses the one-loop integrand satisfies (T₉′). -/
theorem jointEnergyFirstIntegrable_oneLoop (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0)
    (q : Fin n → Fin 4 → ℝ) (Ms : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) (E : Finset (Fin n))
    (hE : E.card ≤ 3) (hcount : 4 + E.card < 2 * n) (g : Fin n → (Fin 4 → ℝ) → ℂ)
    (hg : ∀ i ∈ E, ∃ u : ℂ, ∃ w : Fin 4 → ℂ, ∀ k, g i k = u + ∑ ν, w ν * (k ν : ℂ)) (z : ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 1 fun ℓ =>
      z * (∏ i ∈ E, g i (c i • ℓ 0 + q i)) * ∏ i, (propDenom (Ms i) ε (c i • ℓ 0 + q i))⁻¹ := by
  set N : (Fin 2 → Fin 4 → ℝ) → ℂ := fun ℓ =>
    z * ∏ i ∈ E, g i (lineMomentum (auxDir c) (auxShift q) (Fin.castAdd 4 i) ℓ) with hN
  have hpoly : IsLoopPoly 2 3 N := by
    have h := IsLoopPoly.prod (L := 2) E (fun _ => 1)
      (F := fun i ℓ => g i (lineMomentum (auxDir c) (auxShift q) (Fin.castAdd 4 i) ℓ))
      fun i hi => (affine_lineMomentum _ _ _ (hg i hi)).1
    rw [Finset.sum_const, smul_eq_mul, mul_one] at h
    exact (h.mono hE).const_mul z
  have hB : RefinedBound (auxDir c) (E.image (Fin.castAdd 4)) 4 N := by
    have h := RefinedBound.prod (α := auxDir c) E (Fin.castAdd 4)
      (fun a _ b _ h => Fin.castAdd_injective _ _ h)
      (g := fun i ℓ => g i (lineMomentum (auxDir c) (auxShift q) (Fin.castAdd 4 i) ℓ))
      fun i hi => (affine_lineMomentum _ _ _ (hg i hi)).2
    exact (h.const_mul z).mono le_rfl (by omega)
  obtain ⟨Q, hq, hQ⟩ := SE2.IsLoopPoly.exists_loopQuartic_cubic hpoly
  rw [← hQ] at hB
  have h := jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_cubic Q (auxDir c)
    (auxShift q) (auxMass Ms 0) hq (by omega : 6 ≤ n + 3) hε
    (noSubdivergenceRefined_auxDir c hc E hcount) hB
  rw [hQ] at h
  set F : (Fin 4 → ℝ) → ℂ := fun k => z * (∏ i ∈ E, g i (c i • k + q i)) *
    ∏ i, (propDenom (Ms i) ε (c i • k + q i))⁻¹ with hF
  have hfun : (fun ℓ => N ℓ * ∏ i, (lineDenom (auxDir c) (auxShift q) (auxMass Ms 0) ε i ℓ)⁻¹) =
      fun ℓ => F (ℓ 0) * ((propDenom 0 ε (ℓ 1))⁻¹) ^ 4 := by
    funext ℓ
    simp only [hF]
    rw [Fin.prod_univ_add (a := n) (b := 4)]
    simp only [hN, QED.TwoLoop.Bridge.lineDenom_eq_propDenom, lineMomentum_auxDir_castAdd,
      lineMomentum_auxDir_natAdd, auxMass, Fin.addCases_left, Fin.addCases_right,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [hfun] at h
  obtain ⟨h₁, h₂⟩ := energyFirst_of_mul_aux4 (F := F) 0 hε h
  exact jointEnergyFirstIntegrable_one_of_energyFirst h₁ h₂

end QED.GradedProof.X0

end
