/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdPcs

/-!
# (R-Π₄) step L6d3: photon-mass limits as one-loop limits

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3.
`FaceIdPL D Ψ` says that `t · D(t)` has a limit as `t → ∞` and that it is `iπ²` times the
`ε → 0⁺` limit of `Ψ(ε)`. Pieces satisfy it with `Ψ` the sum of their face integrals
(`faceId_PL_of_faces`: each face integral divided by its constant `1` (self-energy) or `2`
(vertex)), and it is closed under sums and constant multiples, so a class density satisfies it
with `Ψ` the sum of the one-loop integrals of all its faces. A face with a block of four or more
lines contributes `0` (`faceId_face1_zero`, `faceId_face0_zero`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- **A photon-mass limit given by a one-loop limit**: `t · D(t) → iπ² Λ` and `Ψ(ε) → Λ` as
`ε → 0⁺`, for some `Λ`. -/
def FaceIdPL (D Ψ : ℝ → ℂ) : Prop :=
  ∃ Λ : ℂ, Tendsto (fun t : ℝ => (t : ℂ) * D t) atTop (𝓝 (I * (π : ℂ) ^ 2 * Λ)) ∧
    Tendsto Ψ (𝓝[>] 0) (𝓝 Λ)

namespace FaceIdPL

variable {D D' Ψ Ψ' : ℝ → ℂ}

theorem add (h : FaceIdPL D Ψ) (h' : FaceIdPL D' Ψ') :
    FaceIdPL (fun t => D t + D' t) fun ε => Ψ ε + Ψ' ε := by
  obtain ⟨Λ, h1, h2⟩ := h
  obtain ⟨Λ', h1', h2'⟩ := h'
  refine ⟨Λ + Λ', ?_, h2.add h2'⟩
  rw [mul_add]
  exact (h1.add h1').congr fun t => by ring

theorem const_mul (h : FaceIdPL D Ψ) (r : ℂ) :
    FaceIdPL (fun t => r * D t) fun ε => r * Ψ ε := by
  obtain ⟨Λ, h1, h2⟩ := h
  refine ⟨r * Λ, ?_, h2.const_mul r⟩
  have e : I * (π : ℂ) ^ 2 * (r * Λ) = r * (I * (π : ℂ) ^ 2 * Λ) := by ring
  rw [e]
  exact (h1.const_mul r).congr fun t => by ring

theorem zero : FaceIdPL (fun _ => 0) fun _ => 0 :=
  ⟨0, by simp, tendsto_const_nhds⟩

theorem sum {κ : Type*} (s : Finset κ) {D : κ → ℝ → ℂ} {Ψ : κ → ℝ → ℂ}
    (h : ∀ i ∈ s, FaceIdPL (D i) (Ψ i)) :
    FaceIdPL (fun t => ∑ i ∈ s, D i t) fun ε => ∑ i ∈ s, Ψ i ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr (h : FaceIdPL D Ψ) (hD : ∀ t, D t = D' t) (hΨ : ∀ ε, 0 < ε → Ψ ε = Ψ' ε) :
    FaceIdPL D' Ψ' := by
  obtain ⟨Λ, h1, h2⟩ := h
  refine ⟨Λ, h1.congr fun t => by rw [hD], h2.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε using hΨ ε hε

/-- **Any limit of `Ψ` determines the limit of `t · D`.** -/
theorem tendsto (h : FaceIdPL D Ψ) {Λ : ℂ} (hΨ : Tendsto Ψ (𝓝[>] 0) (𝓝 Λ)) :
    Tendsto (fun t : ℝ => (t : ℂ) * D t) atTop (𝓝 (I * (π : ℂ) ^ 2 * Λ)) := by
  obtain ⟨Λ', h1, h2⟩ := h
  rwa [tendsto_nhds_unique hΨ h2]

end FaceIdPL

/-- **A piece from its two faces**: `t · D(t) → -π⁴ (F₁ + F₀)` and the face integrals `E_i`
tend to `c_i iπ² F_i` (`c_i ≠ 0`). -/
theorem faceId_PL_of_faces {D E₁ E₀ : ℝ → ℂ} {F₁ F₀ c₁ c₀ : ℂ} (hc₁ : c₁ ≠ 0) (hc₀ : c₀ ≠ 0)
    (hD : Tendsto (fun t : ℝ => (t : ℂ) * D t) atTop (𝓝 (-((π : ℂ) ^ 4) * (F₁ + F₀))))
    (h₁ : Tendsto E₁ (𝓝[>] 0) (𝓝 (c₁ * I * (π : ℂ) ^ 2 * F₁)))
    (h₀ : Tendsto E₀ (𝓝[>] 0) (𝓝 (c₀ * I * (π : ℂ) ^ 2 * F₀))) :
    FaceIdPL D fun ε => c₁⁻¹ * E₁ ε + c₀⁻¹ * E₀ ε := by
  refine ⟨I * (π : ℂ) ^ 2 * (F₁ + F₀), ?_, ?_⟩
  · have e : I * (π : ℂ) ^ 2 * (I * (π : ℂ) ^ 2 * (F₁ + F₀)) = -((π : ℂ) ^ 4) * (F₁ + F₀) := by
      linear_combination ((π : ℂ) ^ 4 * (F₁ + F₀)) * I_sq
    rwa [e]
  · have e : I * (π : ℂ) ^ 2 * (F₁ + F₀) =
        c₁⁻¹ * (c₁ * I * (π : ℂ) ^ 2 * F₁) + c₀⁻¹ * (c₀ * I * (π : ℂ) ^ 2 * F₀) := by
      field_simp
    rw [e]
    exact (h₁.const_mul _).add (h₀.const_mul _)

/-- **A vanishing face** as a face integral: `0 → c iπ² F` when `F = 0`. -/
theorem faceId_tendsto_zero_face {F c : ℂ} (h : F = 0) :
    Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[>] 0) (𝓝 (c * I * (π : ℂ) ^ 2 * F)) := by
  rw [h, mul_zero]
  exact tendsto_const_nhds

/-- **A loop-`1` face with four or more lines in its block has limit `0`.** -/
theorem faceId_face1_zero {p q : ℕ} (hp : 2 ≤ p) {α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ}
    {γ₀ : Fin (p + 1 + 1 + q + 1)} (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hcard : (Finset.univ.filter fun l => α l ≠ ![1, 0]).card = p + 1 + 1)
    (pp : Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ) (M : Fin (p + 1 + 1 + q + 1) → ℝ) (n : ℕ)
    (Q : LoopQuartic) (hd : LoopDegLe 1 3 Q) (hn : n = 7 ∨ (n = 6 ∧ Q.quart = 0))
    {ρ₀ c₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hc₁ : 0 < c₁)
    (hV : ∀ w : Fin (p + 1 + 1 + q + 1) → ℝ, (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w γ₀ ≤ ρ₀ → c₁ ≤ symanzikV α pp M w)
    (hint : ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF n Q α pp M γ₀ u (simplexPoint x))
        (simplexSet (p + 1 + 1 + q))) :
    limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet (p + 1 + 1 + q),
      {w | faceSum α w ≤ ρ₀}.indicator (pieceF n Q α pp M γ₀ u) (simplexPoint x)) = 0 := by
  obtain ⟨e, hS, hγ⟩ := faceId_exists_sort α γ₀ ((huniq γ₀).2 rfl) hrow hcard
  subst hγ
  obtain ⟨B, hB⟩ := lqBdd_finite fun _ : Unit => Q
  rw [faceId_face_limUnder_sort α hS hrow pp M n Q hB hd (fun h => by omega) hn hρ₀ hρ₁ hc₁
    hV hint]
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  exact faceId_faceIdVal_eq_zero n _ Q (by omega)

/-- **A loop-`0` face with four or more lines in its block has limit `0`.** -/
theorem faceId_face0_zero {p q : ℕ} (hp : 2 ≤ p) {α : Fin (p + 1 + 1 + q + 1) → Fin 2 → ℝ}
    {γ₀ : Fin (p + 1 + 1 + q + 1)} (huniq : ∀ l, α l = ![1, -1] ↔ l = γ₀)
    (hrow : ∀ l, α l = ![1, 0] ∨ α l = ![0, 1] ∨ α l = ![1, -1])
    (hcard : (Finset.univ.filter fun l => α l ≠ ![0, 1]).card = p + 1 + 1)
    (pp : Fin (p + 1 + 1 + q + 1) → Fin 4 → ℝ) (M : Fin (p + 1 + 1 + q + 1) → ℝ) (n : ℕ)
    (Q : LoopQuartic) (hd : LoopDegLe 0 3 Q) (hn : n = 7 ∨ (n = 6 ∧ Q.quart = 0))
    {ρ₀ c₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : ρ₀ < 1) (hc₁ : 0 < c₁)
    (hV : ∀ w : Fin (p + 1 + 1 + q + 1) → ℝ, (∀ l, 0 ≤ w l) → ∑ l, w l = 1 →
      symanzikU α w ≠ 0 → w γ₀ ≤ ρ₀ → c₁ ≤ symanzikV α pp M w)
    (hint : ∀ u : ℝ, 1 ≤ u →
      IntegrableOn (fun x => pieceF n Q α pp M γ₀ u (simplexPoint x))
        (simplexSet (p + 1 + 1 + q))) :
    limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet (p + 1 + 1 + q),
      {w | faceSum0 α w ≤ ρ₀}.indicator (pieceF n Q α pp M γ₀ u) (simplexPoint x)) = 0 := by
  have hγ' : swapFlip α γ₀ = ![1, -1] := swapFlip_row_1m1 ((huniq γ₀).2 rfl)
  obtain ⟨e, hS, hγ⟩ := faceId_exists_sort (swapFlip α) γ₀ hγ' (faceId_hrow_swapFlip hrow)
    (by rw [filter_swapFlip hrow]; exact hcard)
  subst hγ
  obtain ⟨B, hB⟩ := lqBdd_finite fun _ : Unit => Q
  rw [faceId_face_limUnder_sort0 α hS hrow pp M n Q hB hd (fun h => by omega) hn hρ₀ hρ₁ hc₁
    hV hint]
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  exact faceId_faceIdVal_eq_zero n _ _ (by omega)

end QED.GradedProof.RPi4

end
