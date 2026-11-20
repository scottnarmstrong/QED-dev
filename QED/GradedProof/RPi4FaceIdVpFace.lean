/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdLap0
public import QED.GradedProof.RPi4FaceIdSERep

/-!
# (R-Π₄) step L6d3: the faces of a merged piece

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. For a merged
piece of a vacuum-polarization shape (as in `faceId_vp_tendsto`: shape `sh`, photon line last,
momenta `c(sh l) k`, one momentum `k` below threshold), the face wrappers of `RPi4FaceIdFace`
are specialized: their `huniq`, `hrow`, `hV`, `hint`, `hM`, `hQB` are discharged, the cards and
rows are stated on the integer shape, and the numerators are the representatives of
`RPi4FaceIdSERep` (self-energy: `Q(x, ½(x + β k))`) and `RPi4FaceIdLap0` (vertex: the slice
Laplacians). `faceId_vp_PL` assembles a piece into `FaceIdPL`.

* `faceId_vpf_ne4_10`, `faceId_vpf_ne4_01`, `faceId_vpf_card10`, `faceId_vpf_card01`,
  `faceId_vpf_pp`: rest lines, cards and rest momenta on the integer shape;
* **`faceId_vp_PL`**: the piece from its two face limits;
* **`faceId_vpf_se1_seven`**, **`faceId_vpf_se1_six`**: loop-`1` self-energy faces;
* **`faceId_vpf_vtx1_seven`**, **`faceId_vpf_vtx1_six`**: loop-`1` vertex faces;
* **`faceId_vpf_vtx0_seven`**, **`faceId_vpf_vtx0_six`**: loop-`0` vertex faces (rest momenta
  in `{0, s k}`, `s = ±1`);
* **`faceId_vpf_zero1`**, **`faceId_vpf_zero0`**: faces with four or more block lines.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.Integration.Feynman (simplexSet simplexPoint)

section Piece

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1]) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)

/-- The rest lines of row `(1, 0)` are fermion lines. -/
theorem faceId_vpf_ne4_10 (h4 : base 4 = ![1, -1]) {m : ℕ} (sh : Fin (m + 2) → Fin 5)
    (l : Fin (m + 1))
    (hl : castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l = ![1, 0]) :
    sh l.castSucc ≠ 4 := fun h => by
  rw [castLoopMatrix_eq_row10_iff, h, h4] at hl
  exact absurd (congrFun hl 1) (by simp)

/-- The rest lines of row `(0, 1)` are fermion lines. -/
theorem faceId_vpf_ne4_01 (h4 : base 4 = ![1, -1]) {m : ℕ} (sh : Fin (m + 2) → Fin 5)
    (l : Fin (m + 1))
    (hl : castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l = ![0, 1]) :
    sh l.castSucc ≠ 4 := fun h => by
  rw [castLoopMatrix_eq_row01_iff, h, h4] at hl
  exact absurd (congrFun hl 0) (by simp)

theorem faceId_vpf_card10 {m : ℕ} (sh : Fin (m + 2) → Fin 5) :
    (Finset.univ.filter fun l =>
      castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l ≠ ![1, 0]) =
      Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0] := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact not_congr (castLoopMatrix_eq_row10_iff _ l)

theorem faceId_vpf_card01 {m : ℕ} (sh : Fin (m + 2) → Fin 5) :
    (Finset.univ.filter fun l =>
      castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l ≠ ![0, 1]) =
      Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1] := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact not_congr (castLoopMatrix_eq_row01_iff _ l)

theorem faceId_vpf_pp {m : ℕ} (sh : Fin (m + 2) → Fin 5) (k : Fin 4 → ℝ) (s : ℝ)
    (P : Fin (m + 1) → Prop) (hc : ∀ l, P l → c (sh l.castSucc) = 0 ∨ c (sh l.castSucc) = s) :
    ∀ l, P l → c (sh l.castSucc) • k = 0 ∨ c (sh l.castSucc) • k = s • k := fun l hl => by
  rcases hc l hl with h | h <;> simp [h]

include hrow hrow4 hflow

/-- **A merged piece from its two face limits**: with `E₁ → c₁ iπ² L₁`, `E₀ → c₀ iπ² L₀` (the
face `limUnder`s of `faceId_vp_tendsto`, written with any representatives), the piece density
satisfies `FaceIdPL` with `Ψ = c₁⁻¹ E₁ + c₀⁻¹ E₀`. -/
theorem faceId_vp_PL {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (m + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N) {d₁ d₀ : ℕ}
    (hQ₁ : ∃ Q : LoopQuartic, Q.eval = N ∧ LoopDegLe 1 d₁ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hQ₀ : ∃ Q : LoopQuartic, Q.eval = N ∧ LoopDegLe 0 d₀ Q ∧ (m = 6 ∨ Q.quart = 0))
    (hd₁ : d₁ ≤ 3) (hd₀ : d₀ ≤ 3)
    (hA1 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card)
    (hd11 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card = 2 →
      d₁ ≤ 1)
    (hR1 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![1, 0])
    (hA0 : 2 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card)
    (hd01 : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card = 2 →
      d₀ ≤ 1)
    (hR0 : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![0, 1])
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ) (hMs : Ms (Fin.last m) = 0)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q₁ Q₀ : LoopQuartic)
    (hQ₁e : Q₁.eval = N) (hQ₀e : Q₀.eval = N) {E₁ E₀ : ℝ → ℂ} {c₁ c₀ : ℂ} (hc₁ : c₁ ≠ 0)
    (hc₀ : c₀ ≠ 0)
    (h₁ : Tendsto E₁ (𝓝[>] 0) (𝓝 (c₁ * I * (π : ℂ) ^ 2 *
      limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
        {w | faceSum (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (m + 1) Q₁ (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) u) (simplexPoint x)))))
    (h₀ : Tendsto E₀ (𝓝[>] 0) (𝓝 (c₀ * I * (π : ℂ) ^ 2 *
      limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
        {w | faceSum0 (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (m + 1) Q₀ (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) u) (simplexPoint x))))) :
    FaceIdPL (fun t => pairDens N (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
      (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) t) fun ε => c₁⁻¹ * E₁ ε + c₀⁻¹ * E₀ ε := by
  have hT := faceId_vp_tendsto base c hrow hrow4 y₁ y₂ hflow hm sh hsh hcrit N hpoly hB hQ₁ hQ₀
    hd₁ hd₀ hA1 hd11 hR1 hA0 hd01 hR0 hm₀ Ms hMs hf hk Q₁ hQ₁e
  rw [← faceId_pieceF_congr (hQ₁e.trans hQ₀e.symm)] at h₀
  exact faceId_PL_of_faces hc₁ hc₀ hT h₁ h₀

/-- **The loop-`1` self-energy face of a seven-line merged piece**: numerator
`Q(x, ½(x + β k))`, `β = c(photon) - c(face fermion)`. -/
theorem faceId_vpf_se1_seven (sh : Fin (6 + 2) → Fin 5)
    (hsh : ∀ l : Fin (6 + 2), sh l = 4 ↔ 6 ≤ (l : ℕ)) {E : Finset (Fin (6 + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (6 + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (6 + 1) → ℝ)
    (hf : ∀ l : Fin (6 + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q : LoopQuartic)
    (hQ : Q.eval = N) (hQ1 : LoopDegLe 1 1 Q)
    (hcard : (Finset.univ.filter fun l : Fin (6 + 1) => base (sh l.castSucc) ≠ ![1, 0]).card = 2)
    (hc : ∀ l : Fin (6 + 1), base (sh l.castSucc) = ![1, 0] →
      c (sh l.castSucc) = 0 ∨ c (sh l.castSucc) = 1)
    (β : ℝ) (hβ : ∀ f : Fin (6 + 1), base (sh f.castSucc) = ![0, 1] →
      c (sh (Fin.last 6).castSucc) - c (sh f.castSucc) = β) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x =>
        Q.eval ![x, (1 / 2 : ℝ) • (x + β • k)] *
        ∏ l ∈ Finset.univ.filter (fun l =>
          castLoopMatrix (fun l : Fin (6 + 1) => base (sh l.castSucc)) l = ![1, 0]),
          (propDenom (Ms l) ε (c (sh l.castSucc) • k + x))⁻¹)
      (𝓝[>] 0) (𝓝 (1 * I * (π : ℂ) ^ 2 *
        limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 6,
        {w | faceSum (castLoopMatrix fun l : Fin (6 + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (6 + 1) Q (castLoopMatrix fun l : Fin (6 + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last 6) u) (simplexPoint x)))) := by
  obtain ⟨huniq, hrw⟩ := faceId_vp_rows base hrow hrow4 sh hsh
  obtain ⟨hP1, hPN, -⟩ := faceId_se_rep Q (β • k)
  obtain ⟨BQ, hQB⟩ := lqBdd_finite fun _ : Unit => Q
  have hk' : -(4 * m₀ ^ 2) < Minkowski.dot k k := by linarith
  have hpp := faceId_vpf_pp c sh k 1
    (fun l => castLoopMatrix (fun l : Fin (6 + 1) => base (sh l.castSucc)) l = ![1, 0])
    fun l hl => hc l ((castLoopMatrix_eq_row10_iff _ l).1 hl)
  simp only [one_smul] at hpp
  rw [one_mul]
  refine faceId_face1_se_five hm₀ hk' hQB (ρ₀ := 1 / 4) (by norm_num) (by norm_num)
    (by have := faceId_c0_pos hm₀ hk; positivity) hP1 hPN huniq hrw
    (by rw [faceId_vpf_card10]; exact hcard) _ Ms hQ1
    (fun w hw hw1 hU hγ => faceId_vp_hV_face base c hrow hrow4 y₁ y₂ hflow sh hsh hm₀ Ms hf hk
      w hw hw1 hU hγ)
    (fun u hu => faceId_vp_hint base c hrow hrow4 y₁ y₂ hflow (Or.inr rfl) sh hsh hcrit N hpoly
      hB hm₀ Ms hf hk Q hQ u hu)
    (fun l hl => hf l (faceId_vpf_ne4_10 base hrow4 sh l hl))
    hpp
    (fun f hf₀ ℓ₀ => ?_)
  have hb := hβ f ((castLoopMatrix_eq_row01_iff _ f).1 hf₀)
  rw [add_sub_assoc, ← sub_smul, hb]

/-- **The loop-`1` self-energy face of a six-line merged piece** (no quartic part). -/
theorem faceId_vpf_se1_six (sh : Fin (5 + 2) → Fin 5)
    (hsh : ∀ l : Fin (5 + 2), sh l = 4 ↔ 5 ≤ (l : ℕ)) {E : Finset (Fin (5 + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (5 + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (5 + 1) → ℝ)
    (hf : ∀ l : Fin (5 + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q : LoopQuartic)
    (hQ : Q.eval = N) (hQ1 : LoopDegLe 1 1 Q) (hQq : Q.quart = 0)
    (hcard : (Finset.univ.filter fun l : Fin (5 + 1) => base (sh l.castSucc) ≠ ![1, 0]).card = 2)
    (hc : ∀ l : Fin (5 + 1), base (sh l.castSucc) = ![1, 0] →
      c (sh l.castSucc) = 0 ∨ c (sh l.castSucc) = 1)
    (β : ℝ) (hβ : ∀ f : Fin (5 + 1), base (sh f.castSucc) = ![0, 1] →
      c (sh (Fin.last 5).castSucc) - c (sh f.castSucc) = β) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x =>
        Q.eval ![x, (1 / 2 : ℝ) • (x + β • k)] *
        ∏ l ∈ Finset.univ.filter (fun l =>
          castLoopMatrix (fun l : Fin (5 + 1) => base (sh l.castSucc)) l = ![1, 0]),
          (propDenom (Ms l) ε (c (sh l.castSucc) • k + x))⁻¹)
      (𝓝[>] 0) (𝓝 (1 * I * (π : ℂ) ^ 2 *
        limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 5,
        {w | faceSum (castLoopMatrix fun l : Fin (5 + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (5 + 1) Q (castLoopMatrix fun l : Fin (5 + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last 5) u) (simplexPoint x)))) := by
  obtain ⟨huniq, hrw⟩ := faceId_vp_rows base hrow hrow4 sh hsh
  obtain ⟨BQ, hQB⟩ := lqBdd_finite fun _ : Unit => Q
  have hc₁ : 0 < 3 / 4 * faceIdC0 m₀ k := by have := faceId_c0_pos hm₀ hk; positivity
  have hk' : -(4 * m₀ ^ 2) < Minkowski.dot k k := by linarith
  have hpp := faceId_vpf_pp c sh k 1
    (fun l => castLoopMatrix (fun l : Fin (5 + 1) => base (sh l.castSucc)) l = ![1, 0])
    fun l hl => hc l ((castLoopMatrix_eq_row10_iff _ l).1 hl)
  simp only [one_smul] at hpp
  obtain ⟨hP1, hPN, hPq⟩ := faceId_se_rep Q (β • k)
  rw [one_mul]
  refine faceId_face1_se_four hm₀ hk' hQB (ρ₀ := 1 / 4) (by norm_num) (by norm_num) hc₁ hP1 hPN
    (hPq hQq) huniq hrw (by rw [faceId_vpf_card10]; exact hcard) _ Ms hQ1 hQq
    (fun w hw hw1 hU hγ => faceId_vp_hV_face base c hrow hrow4 y₁ y₂ hflow sh hsh hm₀ Ms hf hk
      w hw hw1 hU hγ)
    (fun u hu => faceId_vp_hint base c hrow hrow4 y₁ y₂ hflow (Or.inl rfl) sh hsh hcrit N hpoly
      hB hm₀ Ms hf hk Q hQ u hu)
    (fun l hl => hf l (faceId_vpf_ne4_10 base hrow4 sh l hl)) hpp (fun f hf₀ ℓ₀ => ?_)
  have hb := hβ f ((castLoopMatrix_eq_row01_iff _ f).1 hf₀)
  rw [add_sub_assoc, ← sub_smul, hb]

/-- **The loop-`1` vertex face of a seven-line merged piece**: numerator the slice Laplacian
`faceIdLapF 1 Q (x, 0)`. -/
theorem faceId_vpf_vtx1_seven (sh : Fin (6 + 2) → Fin 5)
    (hsh : ∀ l : Fin (6 + 2), sh l = 4 ↔ 6 ≤ (l : ℕ)) {E : Finset (Fin (6 + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (6 + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (6 + 1) → ℝ)
    (hf : ∀ l : Fin (6 + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q : LoopQuartic)
    (hQ : Q.eval = N) (hQ2 : LoopDegLe 1 2 Q)
    (hcard : (Finset.univ.filter fun l : Fin (6 + 1) => base (sh l.castSucc) ≠ ![1, 0]).card = 3)
    (hc : ∀ l : Fin (6 + 1), base (sh l.castSucc) = ![1, 0] →
      c (sh l.castSucc) = 0 ∨ c (sh l.castSucc) = 1) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x =>
        faceIdLapF 1 Q.eval ![x, 0] *
        ∏ l ∈ Finset.univ.filter (fun l =>
          castLoopMatrix (fun l : Fin (6 + 1) => base (sh l.castSucc)) l = ![1, 0]),
          (propDenom (Ms l) ε (c (sh l.castSucc) • k + x))⁻¹)
      (𝓝[>] 0) (𝓝 (2 * I * (π : ℂ) ^ 2 *
        limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 6,
        {w | faceSum (castLoopMatrix fun l : Fin (6 + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (6 + 1) Q (castLoopMatrix fun l : Fin (6 + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last 6) u) (simplexPoint x)))) := by
  obtain ⟨huniq, hrw⟩ := faceId_vp_rows base hrow hrow4 sh hsh
  obtain ⟨BQ, hQB⟩ := lqBdd_finite fun _ : Unit => Q
  have hc₁ : 0 < 3 / 4 * faceIdC0 m₀ k := by have := faceId_c0_pos hm₀ hk; positivity
  have hk' : -(4 * m₀ ^ 2) < Minkowski.dot k k := by linarith
  have hpp := faceId_vpf_pp c sh k 1
    (fun l => castLoopMatrix (fun l : Fin (6 + 1) => base (sh l.castSucc)) l = ![1, 0])
    fun l hl => hc l ((castLoopMatrix_eq_row10_iff _ l).1 hl)
  simp only [one_smul] at hpp
  obtain ⟨hPq, hP1, hPN⟩ := faceId_lap_rep hQ2
  exact faceId_face1_vtx_four hm₀ hk' hQB (ρ₀ := 1 / 4) (by norm_num) (by norm_num) hc₁ hPq hP1
    hPN huniq hrw (by rw [faceId_vpf_card10]; exact hcard) _ Ms hQ2
    (fun w hw hw1 hU hγ => faceId_vp_hV_face base c hrow hrow4 y₁ y₂ hflow sh hsh hm₀ Ms hf hk
      w hw hw1 hU hγ)
    (fun u hu => faceId_vp_hint base c hrow hrow4 y₁ y₂ hflow (Or.inr rfl) sh hsh hcrit N hpoly
      hB hm₀ Ms hf hk Q hQ u hu)
    (fun l hl => hf l (faceId_vpf_ne4_10 base hrow4 sh l hl)) hpp (fun _ => rfl)

/-- **The loop-`1` vertex face of a six-line merged piece**: the slice Laplacian is a
constant `C`. -/
theorem faceId_vpf_vtx1_six (sh : Fin (5 + 2) → Fin 5)
    (hsh : ∀ l : Fin (5 + 2), sh l = 4 ↔ 5 ≤ (l : ℕ)) {E : Finset (Fin (5 + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (5 + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (5 + 1) → ℝ)
    (hf : ∀ l : Fin (5 + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q : LoopQuartic)
    (hQ : Q.eval = N) (hQ2 : LoopDegLe 1 2 Q) (hQq : Q.quart = 0)
    (hcard : (Finset.univ.filter fun l : Fin (5 + 1) => base (sh l.castSucc) ≠ ![1, 0]).card = 3)
    (hc : ∀ l : Fin (5 + 1), base (sh l.castSucc) = ![1, 0] →
      c (sh l.castSucc) = 0 ∨ c (sh l.castSucc) = 1) (C : ℂ)
    (hL : ∀ ℓ₀ : Fin 4 → ℝ, faceIdLapF 1 Q.eval ![ℓ₀, 0] = C) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x => C *
        ∏ l ∈ Finset.univ.filter (fun l =>
          castLoopMatrix (fun l : Fin (5 + 1) => base (sh l.castSucc)) l = ![1, 0]),
          (propDenom (Ms l) ε (c (sh l.castSucc) • k + x))⁻¹)
      (𝓝[>] 0) (𝓝 (2 * I * (π : ℂ) ^ 2 *
        limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 5,
        {w | faceSum (castLoopMatrix fun l : Fin (5 + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (5 + 1) Q (castLoopMatrix fun l : Fin (5 + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last 5) u) (simplexPoint x)))) := by
  obtain ⟨huniq, hrw⟩ := faceId_vp_rows base hrow hrow4 sh hsh
  obtain ⟨BQ, hQB⟩ := lqBdd_finite fun _ : Unit => Q
  have hc₁ : 0 < 3 / 4 * faceIdC0 m₀ k := by have := faceId_c0_pos hm₀ hk; positivity
  have hk' : -(4 * m₀ ^ 2) < Minkowski.dot k k := by linarith
  have hpp := faceId_vpf_pp c sh k 1
    (fun l => castLoopMatrix (fun l : Fin (5 + 1) => base (sh l.castSucc)) l = ![1, 0])
    fun l hl => hc l ((castLoopMatrix_eq_row10_iff _ l).1 hl)
  simp only [one_smul] at hpp
  exact faceId_face1_vtx_three hm₀ hk' hQB (ρ₀ := 1 / 4) (by norm_num) (by norm_num) hc₁ C
    huniq hrw (by rw [faceId_vpf_card10]; exact hcard) _ Ms hQ2 hQq
    (fun w hw hw1 hU hγ => faceId_vp_hV_face base c hrow hrow4 y₁ y₂ hflow sh hsh hm₀ Ms hf hk
      w hw hw1 hU hγ)
    (fun u hu => faceId_vp_hint base c hrow hrow4 y₁ y₂ hflow (Or.inl rfl) sh hsh hcrit N hpoly
      hB hm₀ Ms hf hk Q hQ u hu)
    (fun l hl => hf l (faceId_vpf_ne4_10 base hrow4 sh l hl)) hpp hL

/-- **The loop-`0` vertex face of a seven-line merged piece**: rest momenta in `{0, k'}`,
numerator the slice Laplacian `faceIdLapF 0 Q (0, x)`. -/
theorem faceId_vpf_vtx0_seven (sh : Fin (6 + 2) → Fin 5)
    (hsh : ∀ l : Fin (6 + 2), sh l = 4 ↔ 6 ≤ (l : ℕ)) {E : Finset (Fin (6 + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (6 + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (6 + 1) → ℝ)
    (hf : ∀ l : Fin (6 + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q : LoopQuartic)
    (hQ : Q.eval = N) (hQ2 : LoopDegLe 0 2 Q)
    (hcard : (Finset.univ.filter fun l : Fin (6 + 1) => base (sh l.castSucc) ≠ ![0, 1]).card = 3)
    {k' : Fin 4 → ℝ} (hk' : -(4 * m₀ ^ 2) < Minkowski.dot k' k')
    (hpp : ∀ l : Fin (6 + 1), base (sh l.castSucc) = ![0, 1] →
      c (sh l.castSucc) • k = 0 ∨ c (sh l.castSucc) • k = k') :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x =>
        faceIdLapF 0 Q.eval ![0, x] *
        ∏ l ∈ Finset.univ.filter (fun l =>
          castLoopMatrix (fun l : Fin (6 + 1) => base (sh l.castSucc)) l = ![0, 1]),
          (propDenom (Ms l) ε (c (sh l.castSucc) • k + x))⁻¹)
      (𝓝[>] 0) (𝓝 (2 * I * (π : ℂ) ^ 2 *
        limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 6,
        {w | faceSum0 (castLoopMatrix fun l : Fin (6 + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (6 + 1) Q (castLoopMatrix fun l : Fin (6 + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last 6) u) (simplexPoint x)))) := by
  obtain ⟨huniq, hrw⟩ := faceId_vp_rows base hrow hrow4 sh hsh
  obtain ⟨BQ, hQB⟩ := lqBdd_finite fun _ : Unit => Q
  have hc₁ : 0 < 3 / 4 * faceIdC0 m₀ k := by have := faceId_c0_pos hm₀ hk; positivity
  obtain ⟨hPq, hP1, hPN⟩ := faceId_lap_rep0 hQ2
  exact faceId_face0_vtx_four hm₀ hk' hQB (ρ₀ := 1 / 4) (by norm_num) (by norm_num) hc₁ hPq hP1
    hPN huniq hrw (by rw [faceId_vpf_card01]; exact hcard) _ Ms hQ2
    (fun w hw hw1 hU hγ => faceId_vp_hV_face base c hrow hrow4 y₁ y₂ hflow sh hsh hm₀ Ms hf hk
      w hw hw1 hU hγ)
    (fun u hu => faceId_vp_hint base c hrow hrow4 y₁ y₂ hflow (Or.inr rfl) sh hsh hcrit N hpoly
      hB hm₀ Ms hf hk Q hQ u hu)
    (fun l hl => hf l (faceId_vpf_ne4_01 base hrow4 sh l hl))
    (fun l hl => hpp l ((castLoopMatrix_eq_row01_iff _ l).1 hl)) (fun _ => rfl)

/-- **The loop-`0` vertex face of a six-line merged piece**: the slice Laplacian is a
constant `C`. -/
theorem faceId_vpf_vtx0_six (sh : Fin (5 + 2) → Fin 5)
    (hsh : ∀ l : Fin (5 + 2), sh l = 4 ↔ 5 ≤ (l : ℕ)) {E : Finset (Fin (5 + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (5 + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (5 + 1) → ℝ)
    (hf : ∀ l : Fin (5 + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q : LoopQuartic)
    (hQ : Q.eval = N) (hQ2 : LoopDegLe 0 2 Q) (hQq : Q.quart = 0)
    (hcard : (Finset.univ.filter fun l : Fin (5 + 1) => base (sh l.castSucc) ≠ ![0, 1]).card = 3)
    {k' : Fin 4 → ℝ} (hk' : -(4 * m₀ ^ 2) < Minkowski.dot k' k')
    (hpp : ∀ l : Fin (5 + 1), base (sh l.castSucc) = ![0, 1] →
      c (sh l.castSucc) • k = 0 ∨ c (sh l.castSucc) • k = k') (C : ℂ)
    (hL : ∀ x : Fin 4 → ℝ, faceIdLapF 0 Q.eval ![0, x] = C) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral fun x => C *
        ∏ l ∈ Finset.univ.filter (fun l =>
          castLoopMatrix (fun l : Fin (5 + 1) => base (sh l.castSucc)) l = ![0, 1]),
          (propDenom (Ms l) ε (c (sh l.castSucc) • k + x))⁻¹)
      (𝓝[>] 0) (𝓝 (2 * I * (π : ℂ) ^ 2 *
        limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet 5,
        {w | faceSum0 (castLoopMatrix fun l : Fin (5 + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (5 + 1) Q (castLoopMatrix fun l : Fin (5 + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last 5) u) (simplexPoint x)))) := by
  obtain ⟨huniq, hrw⟩ := faceId_vp_rows base hrow hrow4 sh hsh
  obtain ⟨BQ, hQB⟩ := lqBdd_finite fun _ : Unit => Q
  have hc₁ : 0 < 3 / 4 * faceIdC0 m₀ k := by have := faceId_c0_pos hm₀ hk; positivity
  exact faceId_face0_vtx_three hm₀ hk' hQB (ρ₀ := 1 / 4) (by norm_num) (by norm_num) hc₁ C
    huniq hrw (by rw [faceId_vpf_card01]; exact hcard) _ Ms hQ2 hQq
    (fun w hw hw1 hU hγ => faceId_vp_hV_face base c hrow hrow4 y₁ y₂ hflow sh hsh hm₀ Ms hf hk
      w hw hw1 hU hγ)
    (fun u hu => faceId_vp_hint base c hrow hrow4 y₁ y₂ hflow (Or.inl rfl) sh hsh hcrit N hpoly
      hB hm₀ Ms hf hk Q hQ u hu)
    (fun l hl => hf l (faceId_vpf_ne4_01 base hrow4 sh l hl))
    (fun l hl => hpp l ((castLoopMatrix_eq_row01_iff _ l).1 hl)) hL

/-- **A loop-`1` face of a merged piece with four or more block lines contributes `0`.** -/
theorem faceId_vpf_zero1 {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (m + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q : LoopQuartic)
    (hQ : Q.eval = N) (hQd : LoopDegLe 1 3 Q) (hQq : m = 6 ∨ Q.quart = 0)
    (hcard : 4 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card)
    (hR : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![1, 0]) (C : ℂ) :
    Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[>] 0) (𝓝 (C * I * (π : ℂ) ^ 2 *
      limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
        {w | faceSum (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (m + 1) Q (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) u) (simplexPoint x)))) := by
  refine faceId_tendsto_zero_face ?_
  obtain ⟨huniq, hrw⟩ := faceId_vp_rows base hrow hrow4 sh hsh
  have hc₁ : 0 < 3 / 4 * faceIdC0 m₀ k := by have := faceId_c0_pos hm₀ hk; positivity
  have hV := fun w hw hw1 hU hγ => faceId_vp_hV_face base c hrow hrow4 y₁ y₂ hflow sh hsh hm₀ Ms
    hf hk w hw hw1 hU hγ
  have hint := fun u hu => faceId_vp_hint base c hrow hrow4 y₁ y₂ hflow hm sh hsh hcrit N hpoly
    hB hm₀ Ms hf hk Q hQ u hu
  have hle : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![1, 0]).card <
      m + 1 := by
    obtain ⟨l, hl⟩ := hR
    refine lt_of_lt_of_le (Finset.card_lt_card ?_) (Finset.card_univ.trans (Fintype.card_fin _)).le
    exact Finset.filter_ssubset.2 ⟨l, Finset.mem_univ _, fun h => h hl⟩
  rw [← faceId_vpf_card10] at hcard hle
  obtain ⟨n, hn⟩ : ∃ n, (Finset.univ.filter fun l =>
      castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l ≠ ![1, 0]).card = n := ⟨_, rfl⟩
  rw [hn] at hcard hle
  rcases hm with rfl | rfl
  · have hq : (5 + 1 = 7 ∨ (5 + 1 = 6 ∧ Q.quart = 0)) := Or.inr ⟨rfl, hQq.resolve_left (by omega)⟩
    interval_cases n
    · exact faceId_face1_zero (p := 2) (q := 1) (by norm_num) huniq hrw (by rw [hn]) _ Ms _ Q hQd hq
        (by norm_num) (by norm_num) hc₁ hV hint
    · exact faceId_face1_zero (p := 3) (q := 0) (by norm_num) huniq hrw (by rw [hn]) _ Ms _ Q hQd hq
        (by norm_num) (by norm_num) hc₁ hV hint
  · have hq : (6 + 1 = 7 ∨ (6 + 1 = 6 ∧ Q.quart = 0)) := Or.inl rfl
    interval_cases n
    · exact faceId_face1_zero (p := 2) (q := 2) (by norm_num) huniq hrw (by rw [hn]) _ Ms _ Q hQd hq
        (by norm_num) (by norm_num) hc₁ hV hint
    · exact faceId_face1_zero (p := 3) (q := 1) (by norm_num) huniq hrw (by rw [hn]) _ Ms _ Q hQd hq
        (by norm_num) (by norm_num) hc₁ hV hint
    · exact faceId_face1_zero (p := 4) (q := 0) (by norm_num) huniq hrw (by rw [hn]) _ Ms _ Q hQd hq
        (by norm_num) (by norm_num) hc₁ hV hint

/-- **A loop-`0` face of a merged piece with four or more block lines contributes `0`.** -/
theorem faceId_vpf_zero0 {m : ℕ} (hm : m = 5 ∨ m = 6) (sh : Fin (m + 2) → Fin 5)
    (hsh : ∀ l : Fin (m + 2), sh l = 4 ↔ m ≤ (l : ℕ)) {E : Finset (Fin (m + 2))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun l => base (sh l))
    (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : IsLoopPoly 2 (m + 1 - 3) N)
    (hB : RefinedBound (castLoopMatrix fun l => base (sh l)) E 4 N)
    {m₀ : ℝ} (hm₀ : 0 < m₀) (Ms : Fin (m + 1) → ℝ)
    (hf : ∀ l : Fin (m + 1), sh l.castSucc ≠ 4 → m₀ ≤ Ms l)
    {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (Q : LoopQuartic)
    (hQ : Q.eval = N) (hQd : LoopDegLe 0 3 Q) (hQq : m = 6 ∨ Q.quart = 0)
    (hcard : 4 ≤ (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card)
    (hR : ∃ l : Fin (m + 1), base (sh l.castSucc) = ![0, 1]) (C : ℂ) :
    Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[>] 0) (𝓝 (C * I * (π : ℂ) ^ 2 *
      limUnder atTop (fun u : ℝ => u • ∫ x in simplexSet m,
        {w | faceSum0 (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc)) w ≤
          1 / 4}.indicator
          (pieceF (m + 1) Q (castLoopMatrix fun l : Fin (m + 1) => base (sh l.castSucc))
            (fun l => c (sh l.castSucc) • k) Ms (Fin.last m) u) (simplexPoint x)))) := by
  refine faceId_tendsto_zero_face ?_
  obtain ⟨huniq, hrw⟩ := faceId_vp_rows base hrow hrow4 sh hsh
  have hc₁ : 0 < 3 / 4 * faceIdC0 m₀ k := by have := faceId_c0_pos hm₀ hk; positivity
  have hV := fun w hw hw1 hU hγ => faceId_vp_hV_face base c hrow hrow4 y₁ y₂ hflow sh hsh hm₀ Ms
    hf hk w hw hw1 hU hγ
  have hint := fun u hu => faceId_vp_hint base c hrow hrow4 y₁ y₂ hflow hm sh hsh hcrit N hpoly
    hB hm₀ Ms hf hk Q hQ u hu
  have hle : (Finset.univ.filter fun l : Fin (m + 1) => base (sh l.castSucc) ≠ ![0, 1]).card <
      m + 1 := by
    obtain ⟨l, hl⟩ := hR
    refine lt_of_lt_of_le (Finset.card_lt_card ?_) (Finset.card_univ.trans (Fintype.card_fin _)).le
    exact Finset.filter_ssubset.2 ⟨l, Finset.mem_univ _, fun h => h hl⟩
  rw [← faceId_vpf_card01] at hcard hle
  obtain ⟨n, hn⟩ : ∃ n, (Finset.univ.filter fun l =>
      castLoopMatrix (fun l : Fin (m + 1) => base (sh l.castSucc)) l ≠ ![0, 1]).card = n := ⟨_, rfl⟩
  rw [hn] at hcard hle
  rcases hm with rfl | rfl
  · have hq : (5 + 1 = 7 ∨ (5 + 1 = 6 ∧ Q.quart = 0)) := Or.inr ⟨rfl, hQq.resolve_left (by omega)⟩
    interval_cases n
    · exact faceId_face0_zero (p := 2) (q := 1) (by norm_num) huniq hrw (by rw [hn]) _ Ms _ Q hQd hq
        (by norm_num) (by norm_num) hc₁ hV hint
    · exact faceId_face0_zero (p := 3) (q := 0) (by norm_num) huniq hrw (by rw [hn]) _ Ms _ Q hQd hq
        (by norm_num) (by norm_num) hc₁ hV hint
  · have hq : (6 + 1 = 7 ∨ (6 + 1 = 6 ∧ Q.quart = 0)) := Or.inl rfl
    interval_cases n
    · exact faceId_face0_zero (p := 2) (q := 2) (by norm_num) huniq hrw (by rw [hn]) _ Ms _ Q hQd hq
        (by norm_num) (by norm_num) hc₁ hV hint
    · exact faceId_face0_zero (p := 3) (q := 1) (by norm_num) huniq hrw (by rw [hn]) _ Ms _ Q hQd hq
        (by norm_num) (by norm_num) hc₁ hV hint
    · exact faceId_face0_zero (p := 4) (q := 0) (by norm_num) huniq hrw (by rw [hn]) _ Ms _ Q hQd hq
        (by norm_num) (by norm_num) hc₁ hV hint

end Piece

end QED.GradedProof.RPi4

end
