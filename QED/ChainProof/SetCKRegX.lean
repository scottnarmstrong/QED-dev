/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCrossMirror

/-!
# Set (c), Stage K: the regulator link of the crossed unit

Helper level (no frozen statement). The crossed placements of the set (c) kernel are
`crossUnit 0 t` and `crossUnit t 0` (`QED.ChainProof.SetCK.crossT_eq_crossUnit`), the crossed unit
`∫_{Δ₄} T(μ_a, μ_b)` at `Λ = ∞` with photon masses² `μ_a` (line `z_a`) and `μ_b` (line `z_b`).
The crossed unit has no subdivergence, and with one photon massive no infrared divergence, so its
regulator link is dominated convergence with the bound of the Phase 4 X link
(`QED.TwoLoop.UnitXClose.crossedDom`, uniform in `μ_a, μ_b ≥ 0`):

* `tendsto_crossUnit`: if `μ_a → a ≥ 0` and `μ_b → b ≥ 0` along any countably generated filter,
  with `μ_a, μ_b ≥ 0` eventually, then `crossUnit μ_a μ_b → crossUnit a b`;
* `tendsto_crossUnit_atTop_left`, `tendsto_crossUnit_atTop_right`: if one photon mass² tends to
  `∞` (the other staying `≥ 0`), then `crossUnit μ_a μ_b → 0`.

These cover any finite combination of crossed units with per-line masses, in particular the
Pauli–Villars sum on the massless line,

`xReg t λ Λ = (crossUnit λ² t - crossUnit Λ² t) + (crossUnit t λ² - crossUnit t Λ²)`,

and **`tendsto_xReg`**: `xReg t λ Λ → crossUnit 0 t + crossUnit t 0` as `(λ, Λ) → (0⁺, ∞)`
jointly, for every `t ≥ 0`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitXGraph QED.TwoLoop.UnitXClose
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- The denominator `V = Ẽ + μ_a z_a + μ_b z_b` of the crossed integrand. -/
theorem crossedAt_eq_inv (μa μb : ℝ) (z : Fin 5 → ℝ) :
    crossedAt μa μb z =
      z 1 * (gPsi1 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4) /
            (2 * gXU (z 0) (z 1) (z 2) (z 3) (z 4) ^ 6) *
          ((gXE (z 0) (z 1) (z 2) (z 3) (z 4) + μa * z 3 + μb * z 4)⁻¹) ^ 2 -
        gPsi2 (z 0) (z 1 / 2) (z 1) (z 2) (z 3) (z 4) /
            (2 * gXU (z 0) (z 1) (z 2) (z 3) (z 4) ^ 5) *
          (gXE (z 0) (z 1) (z 2) (z 3) (z 4) + μa * z 3 + μb * z 4)⁻¹) :=
  crossedTerm_eq_inv _ _ _ _ _ _ _

/-- Pointwise continuity of the crossed integrand in the two photon masses². -/
theorem tendsto_crossedAt {ι : Type*} {l : Filter ι} {μa μb : ι → ℝ} {a b : ℝ}
    (ha : Tendsto μa l (𝓝 a)) (hb : Tendsto μb l (𝓝 b)) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    {z : Fin 5 → ℝ} (hz : ∀ k, 0 < z k) :
    Tendsto (fun i => crossedAt (μa i) (μb i) z) l (𝓝 (crossedAt a b z)) := by
  have hE := gXE_pos (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
  have hV : gXE (z 0) (z 1) (z 2) (z 3) (z 4) + a * z 3 + b * z 4 ≠ 0 := by
    have := mul_nonneg ha0 (hz 3).le
    have := mul_nonneg hb0 (hz 4).le
    linarith
  have hT : Tendsto (fun i => gXE (z 0) (z 1) (z 2) (z 3) (z 4) + μa i * z 3 + μb i * z 4) l
      (𝓝 (gXE (z 0) (z 1) (z 2) (z 3) (z 4) + a * z 3 + b * z 4)) :=
    ((tendsto_const_nhds.add (ha.mul_const _)).add (hb.mul_const _))
  have hi := hT.inv₀ hV
  simp only [crossedAt_eq_inv]
  exact tendsto_const_nhds.mul (((tendsto_const_nhds.mul (hi.pow 2))).sub
    (tendsto_const_nhds.mul hi))

/-- The crossed integrand tends to `0` when one photon mass² tends to `∞`. -/
theorem tendsto_crossedAt_atTop {ι : Type*} {l : Filter ι} {μa μb : ι → ℝ}
    (ha : Tendsto μa l atTop) (hb0 : ∀ᶠ i in l, 0 ≤ μb i) {z : Fin 5 → ℝ} (hz : ∀ k, 0 < z k) :
    Tendsto (fun i => crossedAt (μa i) (μb i) z) l (𝓝 0) := by
  refine tendsto_crossedTerm_zero_of_tendsto ?_
  have hE := gXE_pos (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)
  refine tendsto_atTop_mono' l ?_ ((ha.atTop_mul_const (hz 3)).atTop_add
    (tendsto_const_nhds (x := gXE (z 0) (z 1) (z 2) (z 3) (z 4))))
  filter_upwards [hb0] with i hi
  have := mul_nonneg hi (hz 4).le
  linarith

/-- Dominated convergence for the crossed unit, given pointwise convergence on the open simplex. -/
theorem tendsto_crossUnit_of_pointwise {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μa μb : ι → ℝ} (ha0 : ∀ᶠ i in l, 0 ≤ μa i) (hb0 : ∀ᶠ i in l, 0 ≤ μb i) {L : ℝ}
    (F : (Fin 5 → ℝ) → ℝ)
    (hpt : ∀ z : Fin 5 → ℝ, (∀ k, 0 < z k) →
      Tendsto (fun i => crossedAt (μa i) (μb i) z) l (𝓝 (F z)))
    (hL : ∫ y in simplexSet 4, F (simplexPoint y) = L) :
    Tendsto (fun i => crossUnit (μa i) (μb i)) l (𝓝 L) := by
  obtain ⟨C, s, hs0, hs1, hC⟩ := crossedDom
  have hint : IntegrableOn (fun y => C * ∏ k ∈ Finset.univ, simplexPoint y k ^ (-s))
      (simplexSet 4) :=
    (QED.Integration.TwoLoop.integrableOn_prod_simplexPoint_rpow Finset.univ hs0 hs1).const_mul _
  have hsp := QED.Integration.TwoLoop.continuous_simplexPoint' (m := 4)
  have hpos := QED.TwoLoop.UnitLGraphReduce.ae_simplexPoint_pos (by norm_num : 0 < 4)
  rw [← hL]
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hint ?_
  · exact Eventually.of_forall fun i =>
      ((measurable_crossedAt _ _).comp hsp.measurable).aestronglyMeasurable
  · filter_upwards [ha0, hb0] with i hai hbi
    filter_upwards [hpos] with y hy
    rw [Real.norm_eq_abs]
    exact hC _ _ hai hbi _ hy (sum_simplexPoint y)
  · filter_upwards [hpos] with y hy
    exact hpt _ hy

/-- **The crossed unit is continuous in the two photon masses²** on `[0, ∞)²`, along any
countably generated filter. -/
theorem tendsto_crossUnit {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {μa μb : ι → ℝ}
    {a b : ℝ} (ha : Tendsto μa l (𝓝 a)) (hb : Tendsto μb l (𝓝 b)) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha0' : ∀ᶠ i in l, 0 ≤ μa i) (hb0' : ∀ᶠ i in l, 0 ≤ μb i) :
    Tendsto (fun i => crossUnit (μa i) (μb i)) l (𝓝 (crossUnit a b)) :=
  tendsto_crossUnit_of_pointwise ha0' hb0' (crossedAt a b)
    (fun _ hz => tendsto_crossedAt ha hb ha0 hb0 hz) rfl

/-- **The crossed unit tends to `0` when the photon mass² of the line `z_a` tends to `∞`.** -/
theorem tendsto_crossUnit_atTop_left {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μa μb : ι → ℝ} (ha : Tendsto μa l atTop) (hb0 : ∀ᶠ i in l, 0 ≤ μb i) :
    Tendsto (fun i => crossUnit (μa i) (μb i)) l (𝓝 0) :=
  tendsto_crossUnit_of_pointwise (ha.eventually_ge_atTop 0) hb0 (fun _ => 0)
    (fun _ hz => tendsto_crossedAt_atTop ha hb0 hz) (by simp)

/-- **The crossed unit tends to `0` when the photon mass² of the line `z_b` tends to `∞`.** -/
theorem tendsto_crossUnit_atTop_right {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μa μb : ι → ℝ} (ha0 : ∀ᶠ i in l, 0 ≤ μa i) (hb : Tendsto μb l atTop) :
    Tendsto (fun i => crossUnit (μa i) (μb i)) l (𝓝 0) := by
  simp only [crossUnit_mirror (μa _)]
  exact tendsto_crossUnit_atTop_left hb ha0

/-- **The crossed pair at finite regulators**: the Pauli–Villars sum on the massless line
`(λ, Λ)`, the massive line at mass² `t`, in both placements. -/
noncomputable def xReg (t lam Lam : ℝ) : ℝ :=
  (crossUnit (lam ^ 2) t - crossUnit (Lam ^ 2) t) + (crossUnit t (lam ^ 2) - crossUnit t (Lam ^ 2))

/-- **The regulator link of the crossed pair**: for `t ≥ 0`,
`xReg t λ Λ → crossUnit 0 t + crossUnit t 0` as `(λ, Λ) → (0⁺, ∞)` jointly. -/
theorem tendsto_xReg {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun p : ℝ × ℝ => xReg t p.1 p.2) (𝓝[>] 0 ×ˢ atTop)
      (𝓝 (crossUnit 0 t + crossUnit t 0)) := by
  have h1 : Tendsto (fun p : ℝ × ℝ => p.1 ^ 2) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => x ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuous_pow 2).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact this.comp tendsto_fst
  have hL : Tendsto (fun p : ℝ × ℝ => p.2 ^ 2) (𝓝[>] 0 ×ˢ atTop) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_snd
  have hsq : ∀ᶠ p : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, 0 ≤ p.1 ^ 2 := Eventually.of_forall fun _ =>
    sq_nonneg _
  have hc : ∀ᶠ _ : ℝ × ℝ in 𝓝[>] 0 ×ˢ atTop, 0 ≤ t := Eventually.of_forall fun _ => ht
  have a1 := tendsto_crossUnit h1 tendsto_const_nhds le_rfl ht hsq hc
  have a2 := tendsto_crossUnit_atTop_left hL hc
  have a3 := tendsto_crossUnit tendsto_const_nhds h1 ht le_rfl hc hsq
  have a4 := tendsto_crossUnit_atTop_right hc hL
  have := (a1.sub a2).add (a3.sub a4)
  simpa [xReg] using this

end QED.ChainProof.SetCK
