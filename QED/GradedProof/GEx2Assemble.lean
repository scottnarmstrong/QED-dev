/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.GEx2Inputs
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Graded.SelectedPartCongr

/-!
# (G-ex₂) from its analytic inputs

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57). `existsUnique_withLevel_one_of_inputs` proves the frozen statement from the three
analytic inputs of `QED/GradedProof/GEx2Inputs.lean` (`SEReal`, `VPReal`, `VertexZeroInput`) at
the data `D₀ = D.withLevel 1 0 0`.

## Proof

Write `D₁ = D.withLevel 1 x y`. The constancy clause of (G₁₂) at level `0` is that of `D`, at level
`1` it says `x f = x (rep f)`. The order-`2` conditions read only level `0` (`selectedPart_congr`)
and hold by `hD`. At order `4`, by `isOnShellAt_two_iff`, `isChargeNormalizedAt_two_iff` and
`isPhotonOnShellAt_two_iff` (with `D₀`), each condition is an affine equation with coefficient
`e⁴` or `e⁵` in one component of `x f` (`rep f = f`) or in `y`; these have exactly one solution.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.GEx2

open QED.Graded
open QED.WickModel (Params)

/-- **The order-`2` conditions read only the level-`0` data.** -/
theorem order_two_congr (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D D' : Counterterms F)
    (h : ∀ f, D.d₁ f 0 = D'.d₁ f 0 ∧ D.d₂ f 0 = D'.d₂ f 0 ∧ D.dm f 0 = D'.dm f 0)
    (h₃ : D.d₃ 0 = D'.d₃ 0) :
    (∀ f, (IsOnShellAt P Φ D f 1 ↔ IsOnShellAt P Φ D' f 1) ∧
      (IsChargeNormalizedAt P Φ D f 1 ↔ IsChargeNormalizedAt P Φ D' f 1)) ∧
      (IsPhotonOnShellAt P Φ D 1 ↔ IsPhotonOnShellAt P Φ D' 1) := by
  have hk : ∀ K k, K ≤ 3 → 2 * k + 2 ≤ K → k = 0 := fun K k hK hk => by omega
  have hl : ∀ K, K ≤ 3 → ∀ g k, 2 * k + 2 ≤ K →
      D.d₁ g k = D'.d₁ g k ∧ D.d₂ g k = D'.d₂ g k ∧ D.dm g k = D'.dm g k :=
    fun K hK g k hkK => by rw [hk K k hK hkK]; exact h g
  have hl₃ : ∀ K, K ≤ 3 → ∀ k, 2 * k + 2 ≤ K → D.d₃ k = D'.d₃ k :=
    fun K hK k hkK => by rw [hk K k hK hkK]; exact h₃
  have hs : ∀ (Q : Params) f, selfEnergyPart Q Φ D f 1 = selfEnergyPart Q Φ D' f 1 := by
    intro Q f
    funext p
    ext α β
    simp only [selfEnergyPart, Matrix.of_apply, onePIPart]
    rw [selectedPart_congr Q _ D D' 1 0 _ (2 * 1) (hl _ (by norm_num)) (hl₃ _ (by norm_num))]
  have hv : ∀ (Q : Params) f, vertexPart Q Φ D f 1 = vertexPart Q Φ D' f 1 := by
    intro Q f
    funext p' p μ
    ext i j
    simp only [vertexPart, Matrix.of_apply, onePIPart]
    rw [selectedPart_congr Q _ D D' 1 1 _ (2 * 1 + 1) (hl _ (by norm_num))
      (hl₃ _ (by norm_num))]
  have hp : ∀ Q : Params, vacuumPolarizationPart Q Φ D 1 = vacuumPolarizationPart Q Φ D' 1 := by
    intro Q
    funext k μ ν
    simp only [vacuumPolarizationPart, onePIPart]
    rw [selectedPart_congr Q _ D D' 0 2 _ (2 * 1) (hl _ (by norm_num)) (hl₃ _ (by norm_num))]
  refine ⟨fun f => ⟨?_, ?_⟩, ?_⟩
  · simp only [IsOnShellAt, hs]
  · simp only [IsChargeNormalizedAt, hv]
  · simp only [IsPhotonOnShellAt, hp]

/-- **(G-ex₂) from the analytic inputs** `SEReal`, `VPReal`, `VertexZeroInput` at
`D₀ = D.withLevel 1 0 0`. -/
theorem existsUnique_withLevel_one_of_inputs (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ)
    (he : P.e ≠ 0) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : IsRenormalizedThrough P Φ D rep 1)
    (hSE : ∀ f, SEReal P Φ (D.withLevel 1 (fun _ => (0, 0, 0)) 0) f)
    (hVP : VPReal P Φ (D.withLevel 1 (fun _ => (0, 0, 0)) 0) m₀)
    (hV : ∀ f, VertexZeroInput P Φ (D.withLevel 1 (fun _ => (0, 0, 0)) 0) f) :
    ∃! x : (F → ℝ × ℝ × ℝ) × ℝ, IsRenormalizedThrough P Φ (D.withLevel 1 x.1 x.2) rep 2 := by
  classical
  set D₀ := D.withLevel 1 (fun _ => (0, 0, 0)) 0 with hD₀
  obtain ⟨hc0, hcond⟩ := hD
  have hPV₁t := sum_eq_zero_of_blocks rep hrep _ hPV₁
  have hPV₂t := sum_eq_zero_of_blocks rep hrep _ hPV₂
  have hpos : ∀ f, 0 < Φ.mass f := fun f => hm₀.trans_le (hmass f)
  have hse := fun f => exists_seData P Φ D₀ f hm₀ hmass hmγ hΛ hPV₁t hPV₂t (hSE f)
  choose r hr A B hlimSE σ₀ σ₁ hσ₀ hσ₁ using hse
  have hD0 : ∀ f, D₀.d₁ f 0 = D₀.d₁ (rep f) 0 ∧ D₀.d₂ f 0 = D₀.d₂ (rep f) 0 ∧
      D₀.dm f 0 = D₀.dm (rep f) 0 := fun f => by
    simpa [hD₀, Counterterms.withLevel] using hc0 f 0 (by norm_num)
  obtain ⟨π₀, hπ⟩ := exists_vpData P Φ D₀ rep hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD0 hVP
  choose c hc using hV
  -- the conditions in closed form
  have hiff : ∀ (x : F → ℝ × ℝ × ℝ) (y : ℝ),
      IsRenormalizedThrough P Φ (D.withLevel 1 x y) rep 2 ↔
        ((∀ f, x f = x (rep f)) ∧
          (∀ f, rep f = f → (P.e ^ 4 * (x f).2.1 = σ₁ f ∧
            P.e ^ 4 * (x f).2.2 * Φ.mass f = σ₀ f + σ₁ f * Φ.mass f) ∧
            c f + P.e ^ 5 * (x f).1 = 0) ∧
          P.e ^ 4 * y = -π₀) := by
    intro x y
    have l0 : ∀ g, (D.withLevel 1 x y).d₁ g 0 = D₀.d₁ g 0 ∧
        (D.withLevel 1 x y).d₂ g 0 = D₀.d₂ g 0 ∧ (D.withLevel 1 x y).dm g 0 = D₀.dm g 0 :=
      fun g => by simp [hD₀, Counterterms.withLevel]
    have l3 : (D.withLevel 1 x y).d₃ 0 = D₀.d₃ 0 := by simp [hD₀, Counterterms.withLevel]
    have z : ∀ g, D₀.d₁ g 1 = 0 ∧ D₀.d₂ g 1 = 0 ∧ D₀.dm g 1 = 0 :=
      fun g => by simp [hD₀, Counterterms.withLevel]
    have z3 : D₀.d₃ 1 = 0 := by simp [hD₀, Counterterms.withLevel]
    have v : ∀ g, (D.withLevel 1 x y).d₁ g 1 = (x g).1 ∧ (D.withLevel 1 x y).d₂ g 1 = (x g).2.1 ∧
        (D.withLevel 1 x y).dm g 1 = (x g).2.2 := fun g => by simp [Counterterms.withLevel]
    have v3 : (D.withLevel 1 x y).d₃ 1 = y := by simp [Counterterms.withLevel]
    have h1 : (∀ f, rep f = f → IsOnShellAt P Φ (D.withLevel 1 x y) f 1 ∧
        IsChargeNormalizedAt P Φ (D.withLevel 1 x y) f 1) ∧
        IsPhotonOnShellAt P Φ (D.withLevel 1 x y) 1 := by
      obtain ⟨hf, hph⟩ := hcond 1 le_rfl (by norm_num)
      have ht := order_two_congr P Φ (D.withLevel 1 x y) D
        (fun g => by simp [Counterterms.withLevel]) (by simp [Counterterms.withLevel])
      exact ⟨fun f hf' => ⟨((ht.1 f).1).2 (hf f hf').1, ((ht.1 f).2).2 (hf f hf').2⟩,
        ht.2.2 hph⟩
    have eS : ∀ f, IsOnShellAt P Φ (D.withLevel 1 x y) f 2 ↔ (P.e ^ 4 * (x f).2.1 = σ₁ f ∧
        P.e ^ 4 * (x f).2.2 * Φ.mass f = σ₀ f + σ₁ f * Φ.mass f) := fun f => by
      have := isOnShellAt_two_iff P Φ (D.withLevel 1 x y) D₀ f (fun g => (l0 g).1)
        (fun g => (l0 g).2.1) (fun g => (l0 g).2.2) l3 (z f).2.1 (z f).2.2 (hpos f) (hr f)
        (hlimSE f) (hσ₀ f) (hσ₁ f)
      rwa [(v f).2.1, (v f).2.2] at this
    have eV : ∀ f, IsChargeNormalizedAt P Φ (D.withLevel 1 x y) f 2 ↔
        c f + P.e ^ 5 * (x f).1 = 0 := fun f => by
      have := isChargeNormalizedAt_two_iff P Φ (D.withLevel 1 x y) D₀ f (l0 f).1 (l0 f).2.1
        (l0 f).2.2 l3 (z f).1 (hpos f) (hc f)
      rwa [(v f).1] at this
    have eP : IsPhotonOnShellAt P Φ (D.withLevel 1 x y) 2 ↔ P.e ^ 4 * y = -π₀ := by
      have := isPhotonOnShellAt_two_iff P Φ (D.withLevel 1 x y) D₀ (fun g => (l0 g).1)
        (fun g => (l0 g).2.1) (fun g => (l0 g).2.2) l3 z3 hπ
      rwa [v3] at this
    have eC : (∀ f k, k < 2 → (D.withLevel 1 x y).d₁ f k = (D.withLevel 1 x y).d₁ (rep f) k ∧
        (D.withLevel 1 x y).d₂ f k = (D.withLevel 1 x y).d₂ (rep f) k ∧
        (D.withLevel 1 x y).dm f k = (D.withLevel 1 x y).dm (rep f) k) ↔
        ∀ f, x f = x (rep f) := by
      constructor
      · intro h f
        obtain ⟨a1, a2, a3⟩ := h f 1 (by norm_num)
        rw [(v f).1, (v (rep f)).1] at a1
        rw [(v f).2.1, (v (rep f)).2.1] at a2
        rw [(v f).2.2, (v (rep f)).2.2] at a3
        exact Prod.ext a1 (Prod.ext a2 a3)
      · intro h f k hk
        interval_cases k
        · simpa [Counterterms.withLevel] using hc0 f 0 (by norm_num)
        · rw [(v f).1, (v f).2.1, (v f).2.2, (v (rep f)).1, (v (rep f)).2.1, (v (rep f)).2.2,
            ← h f]
          exact ⟨rfl, rfl, rfl⟩
    unfold IsRenormalizedThrough
    rw [eC]
    constructor
    · rintro ⟨hC, hJ⟩
      obtain ⟨hf2, hp2⟩ := hJ 2 (by norm_num) le_rfl
      exact ⟨hC, fun f hf => ⟨(eS f).1 (hf2 f hf).1, (eV f).1 (hf2 f hf).2⟩, eP.1 hp2⟩
    · rintro ⟨hC, hF, hP⟩
      refine ⟨hC, fun j hj1 hj2 => ?_⟩
      interval_cases j
      · exact h1
      · exact ⟨fun f hf => ⟨(eS f).2 (hF f hf).1, (eV f).2 (hF f hf).2⟩, eP.2 hP⟩
  have he4 : P.e ^ 4 ≠ 0 := pow_ne_zero _ he
  have he5 : P.e ^ 5 ≠ 0 := pow_ne_zero _ he
  refine ⟨(fun f => (-c (rep f) / P.e ^ 5, σ₁ (rep f) / P.e ^ 4,
    (σ₀ (rep f) + σ₁ (rep f) * Φ.mass (rep f)) / (P.e ^ 4 * Φ.mass (rep f))), -π₀ / P.e ^ 4),
    ?_, ?_⟩
  · refine (hiff _ _).2 ⟨fun f => by simp only [hrep], fun f hf => ?_, by field_simp⟩
    have hM := (hpos f).ne'
    simp only [hf]
    refine ⟨⟨by field_simp, by field_simp⟩, by field_simp; ring⟩
  · rintro ⟨x, y⟩ hxy
    rw [hiff] at hxy
    obtain ⟨hC, hF, hP⟩ := hxy
    refine Prod.ext (funext fun f => ?_) ?_
    · rw [hC f]
      obtain ⟨⟨e1, e2⟩, e3⟩ := hF (rep f) (hrep f)
      have hMr := (hpos (rep f)).ne'
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp only
        field_simp
        linarith
      · simp only
        field_simp
        linarith
      · simp only
        field_simp
        linarith
    · simp only
      field_simp
      linarith

end QED.GradedProof.GEx2

end
