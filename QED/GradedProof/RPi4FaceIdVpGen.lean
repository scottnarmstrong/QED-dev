/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdVpFace
public import QED.GradedProof.RPi4FaceIdLapC

/-!
# (R-Π₄) step L6d3: a merged piece as a one-loop limit, all face kinds

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. For a merged
piece (as in `faceId_vp_tendsto`) the one-loop integrals of its two faces are given by explicit
functions of `ε` chosen by the face kind, read off from the cards of the integer rows:

* `faceIdCard`: the number of lines off a row (the size of a face block);
* `faceIdPsi1`: loop-`1` face; block of `2` lines (self-energy): `EFI(N(x, ½(x + β k)) ∏ D⁻¹)`;
  `3` lines (vertex): `½ EFI(Δ₁N(x, 0) ∏ D⁻¹)`; otherwise `0`;
* `faceIdPsi0`: loop-`0` face; `3` lines (vertex): `½ EFI(Δ₀N(0, x) ∏ D⁻¹)`; otherwise `0`;

(`Δ_s` the half Laplacian `faceIdLapF s`, products over the rest lines of row `(1, 0)` resp.
`(0, 1)`). **`faceId_vp_face1`**, **`faceId_vp_face0`**: `Ψ_s → iπ² L_s` as `ε → 0⁺`;
**`faceId_vp_PL_gen`**: the piece density satisfies `FaceIdPL` with `Ψ = Ψ₁ + Ψ₀`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- The number of lines of a merged piece whose row is not `r` (the size of the face block). -/
def faceIdCard {m : ℕ} (base : Fin 5 → Fin 2 → ℤ) (sh : Fin (m + 2) → Fin 5) (r : Fin 2 → ℤ) :
    ℕ :=
  (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ r).card

/-- **The loop-`1` face integral of a merged piece**, chosen by the face kind. -/
noncomputable def faceIdPsi1 {m : ℕ} (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
    (sh : Fin (m + 2) → Fin 5) (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (Ms : Fin (m + 1) → ℝ) (β : ℝ)
    (k : Fin 4 → ℝ) (ε : ℝ) : ℂ :=
  if faceIdCard base sh ![1, 0] = 2 then
    QED.OneLoop.energyFirstIntegral fun x => N ![x, (1 / 2 : ℝ) • (x + β • k)] *
      ∏ l ∈ Finset.univ.filter (fun l =>
          castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l = ![1, 0]),
        (propDenom (Ms l) ε (c (sh l.castSucc) • k + x))⁻¹
  else if faceIdCard base sh ![1, 0] = 3 then
    2⁻¹ * QED.OneLoop.energyFirstIntegral fun x => faceIdLapF 1 N ![x, 0] *
      ∏ l ∈ Finset.univ.filter (fun l =>
          castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l = ![1, 0]),
        (propDenom (Ms l) ε (c (sh l.castSucc) • k + x))⁻¹
  else 0

/-- **The loop-`0` face integral of a merged piece**, chosen by the face kind. -/
noncomputable def faceIdPsi0 {m : ℕ} (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
    (sh : Fin (m + 2) → Fin 5) (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (Ms : Fin (m + 1) → ℝ)
    (k : Fin 4 → ℝ) (ε : ℝ) : ℂ :=
  if faceIdCard base sh ![0, 1] = 3 then
    2⁻¹ * QED.OneLoop.energyFirstIntegral fun x => faceIdLapF 0 N ![0, x] *
      ∏ l ∈ Finset.univ.filter (fun l =>
          castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l = ![0, 1]),
        (propDenom (Ms l) ε (c (sh l.castSucc) • k + x))⁻¹
  else 0

section Piece

theorem faceId_tendsto_half {E : ℝ → ℂ} {L : ℂ}
    (h : Tendsto E (𝓝[>] 0) (𝓝 (2 * I * (π : ℂ) ^ 2 * L))) :
    Tendsto (fun ε => 2⁻¹ * E ε) (𝓝[>] 0) (𝓝 (I * (π : ℂ) ^ 2 * L)) := by
  have e : I * (π : ℂ) ^ 2 * L = 2⁻¹ * (2 * I * (π : ℂ) ^ 2 * L) := by ring
  rw [e]
  exact h.const_mul _

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1]) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)

include hrow hrow4 hflow

/-- **The loop-`1` face of a merged piece**: `Ψ₁ → iπ² L₁`. -/
theorem faceId_vp_face1 {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (m + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q : LoopQuartic) (hQ : Q.eval = N)
    (hQd : LoopDegLe 1 3 Q)
    (hQq : m = 6 ∨ Q.quart = 0) (hR1 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![1, 0])
    (hA1 : 2 ≤ faceIdCard base sh ![1, 0])
    (hd11 : faceIdCard base sh ![1, 0] = 2 → LoopDegLe 1 1 Q)
    (hd12 : faceIdCard base sh ![1, 0] = 3 → LoopDegLe 1 2 Q)
    (hc : ∀ l : Fin (m + 1), base (sh l.castSucc) = ![1, 0] →
      c (sh l.castSucc) = 0 ∨ c (sh l.castSucc) = 1)
    (β : ℝ) (hβ : faceIdCard base sh ![1, 0] = 2 →
      ∀ f : Fin (m + 1), base (sh f.castSucc) = ![0, 1] →
      c (sh (Fin.last m).castSucc) - c (sh f.castSucc) = β)
    (hC : m = 5 → faceIdCard base sh ![1, 0] = 3 → ∃ C : ℂ, ∀ ℓ₀ : Fin 4 → ℝ,
      faceIdLapF 1 N ![ℓ₀, 0] = C) :
    Tendsto (faceIdPsi1 base c sh N Ms β k) (𝓝[>] 0) (𝓝 (I * (π : ℂ) ^ 2 *
      limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
        {w | faceSum (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (m + 1) Q (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) u) (simplexPoint x)))) := by
  subst hQ
  rw [show faceIdPsi1 base c sh Q.eval Ms β k = fun ε => faceIdPsi1 base c sh Q.eval Ms β k ε
    from rfl]
  by_cases h2 : faceIdCard base sh ![1, 0] = 2
  · simp only [faceIdPsi1, h2, ite_true]
    rw [← one_mul (I * _), ← mul_assoc 1 I]
    rcases hm with rfl | rfl
    · exact faceId_vpf_se1_six base c hrow hrow4 y₁ y₂ hflow sh hsh hcrit _ hpoly hB hm₀ Ms hf hk
        Q rfl (hd11 h2) (hQq.resolve_left (by omega)) h2 hc β (hβ h2)
    · exact faceId_vpf_se1_seven base c hrow hrow4 y₁ y₂ hflow sh hsh hcrit _ hpoly hB hm₀ Ms hf
        hk Q rfl (hd11 h2) h2 hc β (hβ h2)
  by_cases h3 : faceIdCard base sh ![1, 0] = 3
  · simp only [faceIdPsi1, h3, ite_true]
    refine faceId_tendsto_half ?_
    rcases hm with rfl | rfl
    · obtain ⟨C, hCe⟩ := hC rfl h3
      have hT := faceId_vpf_vtx1_six base c hrow hrow4 y₁ y₂ hflow sh hsh hcrit _ hpoly hB hm₀ Ms
        hf hk Q rfl (hd12 h3) (hQq.resolve_left (by omega)) h3 hc C hCe
      refine hT.congr fun ε => ?_
      simp only [hCe]
    · exact faceId_vpf_vtx1_seven base c hrow hrow4 y₁ y₂ hflow sh hsh hcrit _ hpoly hB hm₀ Ms hf
        hk Q rfl (hd12 h3) h3 hc
  · simp only [faceIdPsi1, h2, h3, ite_false]
    have h4 : 4 ≤ faceIdCard base sh ![1, 0] := by omega
    have hT := faceId_vpf_zero1 base c hrow hrow4 y₁ y₂ hflow hm sh hsh hcrit _ hpoly hB hm₀ Ms hf
      hk Q rfl hQd hQq h4 hR1 1
    rwa [one_mul] at hT

/-- **The loop-`0` face of a merged piece**: `Ψ₀ → iπ² L₀`. -/
theorem faceId_vp_face0 {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (m + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q : LoopQuartic) (hQ : Q.eval = N)
    (hQd : LoopDegLe 0 3 Q)
    (hQq : m = 6 ∨ Q.quart = 0) (hR0 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![0, 1])
    (hA0 : 3 ≤ faceIdCard base sh ![0, 1])
    (hd02 : faceIdCard base sh ![0, 1] = 3 → LoopDegLe 0 2 Q) {k' : Fin 4 → ℝ}
    (hk' : faceIdCard base sh ![0, 1] = 3 → -(4 * m₀ ^ 2) < Minkowski.dot k' k')
    (hpp : faceIdCard base sh ![0, 1] = 3 → ∀ l : Fin (m + 1), base (sh l.castSucc) = ![0, 1] →
      c (sh l.castSucc) • k = 0 ∨ c (sh l.castSucc) • k = k')
    (hC : m = 5 → faceIdCard base sh ![0, 1] = 3 → ∃ C : ℂ, ∀ x : Fin 4 → ℝ,
      faceIdLapF 0 N ![0, x] = C) :
    Tendsto (faceIdPsi0 base c sh N Ms k) (𝓝[>] 0) (𝓝 (I * (π : ℂ) ^ 2 *
      limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
        {w | faceSum0 (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (m + 1) Q (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) u) (simplexPoint x)))) := by
  subst hQ
  rw [show faceIdPsi0 base c sh Q.eval Ms k = fun ε => faceIdPsi0 base c sh Q.eval Ms k ε
    from rfl]
  by_cases h3 : faceIdCard base sh ![0, 1] = 3
  · simp only [faceIdPsi0, h3, ite_true]
    refine faceId_tendsto_half ?_
    rcases hm with rfl | rfl
    · obtain ⟨C, hCe⟩ := hC rfl h3
      have hT := faceId_vpf_vtx0_six base c hrow hrow4 y₁ y₂ hflow sh hsh hcrit _ hpoly hB hm₀ Ms
        hf hk Q rfl (hd02 h3) (hQq.resolve_left (by omega)) h3 (hk' h3) (hpp h3) C hCe
      refine hT.congr fun ε => ?_
      simp only [hCe]
    · exact faceId_vpf_vtx0_seven base c hrow hrow4 y₁ y₂ hflow sh hsh hcrit _ hpoly hB hm₀ Ms hf
        hk Q rfl (hd02 h3) h3 (hk' h3) (hpp h3)
  · simp only [faceIdPsi0, h3, ite_false]
    have h4 : 4 ≤ faceIdCard base sh ![0, 1] := by omega
    have hT := faceId_vpf_zero0 base c hrow hrow4 y₁ y₂ hflow hm sh hsh hcrit _ hpoly hB hm₀ Ms hf
      hk Q rfl hQd hQq h4 hR0 1
    rwa [one_mul] at hT

/-- **A merged piece as a one-loop limit**: `t · pairDens → iπ² Λ` and `Ψ₁ + Ψ₀ → Λ`. The
hypotheses are those of `faceId_vp_tendsto` and, for the face kinds that occur, the rest
momenta, the self-energy shift `β`, and the constancy of the slice Laplacian for six-line
pieces. -/
theorem faceId_vp_PL_gen {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (m + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ) (hMs : Ms (Fin.last m) = 0)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) {d₁ d₀ : ℕ}
    (hQ₁ : ∃ Q : LoopQuartic, Q.eval = N ∧ LoopDegLe 1 d₁ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hQ₀ : ∃ Q : LoopQuartic, Q.eval = N ∧ LoopDegLe 0 d₀ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hd₁ : d₁ ≤ 3) (hd₀ : d₀ ≤ 3) (hA1 : 2 ≤ faceIdCard base sh ![1, 0])
    (hd11 : faceIdCard base sh ![1, 0] = 2 → d₁ ≤ 1)
    (hd12 : faceIdCard base sh ![1, 0] = 3 → d₁ ≤ 2)
    (hR1 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![1, 0])
    (hA0 : 3 ≤ faceIdCard base sh ![0, 1]) (hd02 : faceIdCard base sh ![0, 1] = 3 → d₀ ≤ 2)
    (hR0 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![0, 1])
    (hc : ∀ l : Fin (m + 1), base (sh l.castSucc) = ![1, 0] →
      c (sh l.castSucc) = 0 ∨ c (sh l.castSucc) = 1)
    (β : ℝ) (hβ : faceIdCard base sh ![1, 0] = 2 →
      ∀ f : Fin (m + 1), base (sh f.castSucc) = ![0, 1] →
      c (sh (Fin.last m).castSucc) - c (sh f.castSucc) = β)
    (hC1 : m = 5 → faceIdCard base sh ![1, 0] = 3 → ∃ C : ℂ, ∀ ℓ₀ : Fin 4 → ℝ,
      faceIdLapF 1 N ![ℓ₀, 0] = C) {k' : Fin 4 → ℝ}
    (hk' : faceIdCard base sh ![0, 1] = 3 → -(4 * m₀ ^ 2) < Minkowski.dot k' k')
    (hpp : faceIdCard base sh ![0, 1] = 3 → ∀ l : Fin (m + 1), base (sh l.castSucc) = ![0, 1] →
      c (sh l.castSucc) • k = 0 ∨ c (sh l.castSucc) • k = k')
    (hC0 : m = 5 → faceIdCard base sh ![0, 1] = 3 → ∃ C : ℂ, ∀ x : Fin 4 → ℝ,
      faceIdLapF 0 N ![0, x] = C) :
    FaceIdPL (fun t => pairDens N (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t)
      fun ε => faceIdPsi1 base c sh N Ms β k ε + faceIdPsi0 base c sh N Ms k ε := by
  obtain ⟨Q₁, e₁, g₁, q₁⟩ := hQ₁
  obtain ⟨Q₀, e₀, g₀, q₀⟩ := hQ₀
  have h₁ := faceId_vp_face1 base c hrow hrow4 y₁ y₂ hflow hm sh hsh hcrit N hpoly hB hm₀ Ms hf hk
    Q₁ e₁ (g₁.mono hd₁) q₁ hR1 hA1 (fun h => g₁.mono (hd11 h)) (fun h => g₁.mono (hd12 h)) hc β
    hβ hC1
  have h₀ := faceId_vp_face0 base c hrow hrow4 y₁ y₂ hflow hm sh hsh hcrit N hpoly hB hm₀ Ms hf hk
    Q₀ e₀ (g₀.mono hd₀) q₀ hR0 hA0 (fun h => g₀.mono (hd02 h)) hk' hpp hC0
  rw [← one_mul (I * _), ← mul_assoc 1 I] at h₁ h₀
  refine (faceId_vp_PL base c hrow hrow4 y₁ y₂ hflow hm sh hsh hcrit N hpoly hB ⟨Q₁, e₁, g₁, q₁⟩
    ⟨Q₀, e₀, g₀, q₀⟩ hd₁ hd₀ hA1 hd11 hR1
    (by unfold faceIdCard at hA0; omega) (fun h => by unfold faceIdCard at hA0; omega) hR0
    hm₀ Ms hMs hf hk
    Q₁ Q₀ e₁ e₀ one_ne_zero one_ne_zero h₁ h₀).congr (fun _ => rfl) fun ε _ => ?_
  simp only [inv_one, one_mul]

end Piece

end QED.GradedProof.RPi4

end
