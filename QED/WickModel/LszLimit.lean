/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.LszLimitShell
import QED.Algebra.Minkowski
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The LSZ amplitude of the electron current: existence, uniqueness and value

For `m, m_γ, Λ > 0`, regulator fermions as in (Z₂), counterterms on shell (Z₅), on-shell
positive-energy momenta `(p', p)`, spins `s'`, `s` and an index `μ`, consider the iterated limit
of `(1/i) ū_{s'}(p') G^μ_ε(r', r) u_s(p)`, with `G^μ_ε` the order-`e³` connected function: first
`ε → 0⁺` at off-shell `(r', r)`, then `(r', r) → (p', p)` through off-shell momenta. This module
proves that the limit exists, with value `LszLimit.closedForm`
(`QED.WickModel.LszLimit.exists_tendsto_offShell`), and that it is unique: two values with the
limit property agree, since near the shell there are off-shell pairs, such as
`((1 + t) p', (1 + t) p)` for small `t > 0`, at which both inner limits are the same number.

## Main statements

* `QED.WickModel.lszLimit_closedForm`: the iterated limit, with the value
  `LszLimit.closedForm`: `ū_{s'}(p') V^μ(p', p) u_s(p)`, with `V^μ` the vertex function (J) at
  `Z₁ = 1 + δ₁`, plus `e q² [1/(q² + m_γ²) - 1/(q² + Λ²)] Π(q²) ū_{s'}(p') γ^μ u_s(p)`,
  `q = p' - p`.
* `QED.WickModel.existsUnique_lszLimit`: the number with the limit property exists and is
  unique.

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Filter Topology Set

namespace QED.WickModel

/-! ### From the two limits to the `η`-`δ` statement -/

/-- **The `η`-`δ` form of the iterated limit.** If near `(p', p)` the inner limits `G(r', r)`
exist at off-shell pairs, and `G` tends to `L` through off-shell pairs, then for every `η > 0`
all off-shell pairs within some `δ` of `(p', p)` have an inner limit within `η` of `L`. -/
theorem LszLimit.etaDelta_of_tendsto {m : ℝ} {p' p : Fin 4 → ℝ}
    {F : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ → ℂ} {G : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℂ} {L : ℂ}
    (h1 : ∀ᶠ x : (Fin 4 → ℝ) × (Fin 4 → ℝ) in 𝓝 (p', p),
      Minkowski.dot x.1 x.1 ≠ -m ^ 2 → Minkowski.dot x.2 x.2 ≠ -m ^ 2 →
        Tendsto (F x.1 x.2) (𝓝[>] 0) (𝓝 (G x)))
    (h2 : Tendsto G (𝓝[LszLimit.offShellPairs m] (p', p)) (𝓝 L)) :
    ∀ η > 0, ∃ δ > 0, ∀ r' r : Fin 4 → ℝ,
      Minkowski.dot r' r' ≠ -m ^ 2 → Minkowski.dot r r ≠ -m ^ 2 →
      dist r' p' < δ → dist r p < δ →
      ∃ G : ℂ, Tendsto (F r' r) (𝓝[>] 0) (𝓝 G) ∧ ‖G - L‖ < η := by
  intro η hη
  have h3 : ∀ᶠ x in 𝓝[LszLimit.offShellPairs m] (p', p), ‖G x - L‖ < η := by
    filter_upwards [h2 (Metric.ball_mem_nhds L hη)] with x hx
    rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hx
  have h4 := (h1.filter_mono nhdsWithin_le_nhds).and h3
  rw [eventually_nhdsWithin_iff] at h4
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h4
  refine ⟨δ, hδ, fun r' r hr' hr hd' hd => ?_⟩
  have hx : dist (r', r) (p', p) < δ := by
    rw [Prod.dist_eq]
    exact max_lt hd' hd
  obtain ⟨hT, hn⟩ := hball hx ⟨hr', hr⟩
  exact ⟨G (r', r), hT hr' hr, hn⟩

/-! ### Uniqueness -/

/-- `(c p)² = c² p²`. -/
theorem LszLimit.dot_smul_self (c : ℝ) (p : Fin 4 → ℝ) :
    Minkowski.dot (c • p) (c • p) = c ^ 2 * Minkowski.dot p p := by
  simp only [Minkowski.dot_eq, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Off-shell pairs exist arbitrarily close to an on-shell pair**: for `m ≠ 0`, on-shell
`(p', p)` and `δ > 0`, the pair `((1 + t) p', (1 + t) p)` with `t = δ / (2 (‖p'‖ + ‖p‖ + 1))`
is off shell and within `δ` of `(p', p)`. -/
theorem LszLimit.exists_offShell_near {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ r' r : Fin 4 → ℝ, Minkowski.dot r' r' ≠ -m ^ 2 ∧ Minkowski.dot r r ≠ -m ^ 2 ∧
      dist r' p' < δ ∧ dist r p < δ := by
  set N := ‖p'‖ + ‖p‖ + 1 with hN
  have hNpos : 0 < N := by positivity
  set t := δ / (2 * N) with ht
  have htpos : 0 < t := by positivity
  have hm2 : 0 < m ^ 2 := by positivity
  have hoff : ∀ k : Fin 4 → ℝ, Minkowski.dot k k = -m ^ 2 →
      Minkowski.dot ((1 + t) • k) ((1 + t) • k) ≠ -m ^ 2 := by
    intro k hk h
    rw [LszLimit.dot_smul_self, hk] at h
    have h' : ((1 + t) ^ 2 - 1) * m ^ 2 = 0 := by linarith
    have hpos : 0 < ((1 + t) ^ 2 - 1) * m ^ 2 := by
      have : 0 < (1 + t) ^ 2 - 1 := by nlinarith
      positivity
    linarith
  have hnear : ∀ k : Fin 4 → ℝ, ‖k‖ ≤ N → dist ((1 + t) • k) k < δ := by
    intro k hk
    rw [dist_eq_norm, add_smul, one_smul, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos]
    calc t * ‖k‖ ≤ t * N := mul_le_mul_of_nonneg_left hk htpos.le
      _ = δ / 2 := by rw [ht]; field_simp
      _ < δ := by linarith
  refine ⟨(1 + t) • p', (1 + t) • p, hoff p' hp', hoff p hp, hnear p' ?_, hnear p ?_⟩
  · rw [hN]; linarith [norm_nonneg p]
  · rw [hN]; linarith [norm_nonneg p']

/-- **Uniqueness of the iterated limit.** For `m ≠ 0` and on-shell `(p', p)`, two numbers `M₁`,
`M₂` that both have the `η`-`δ` limit property for the same function `F` are equal. -/
theorem LszLimit.eq_of_etaDelta {m : ℝ} (hm : m ≠ 0) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    {F : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ → ℂ} {M₁ M₂ : ℂ}
    (h₁ : ∀ η > 0, ∃ δ > 0, ∀ r' r : Fin 4 → ℝ,
      Minkowski.dot r' r' ≠ -m ^ 2 → Minkowski.dot r r ≠ -m ^ 2 →
      dist r' p' < δ → dist r p < δ →
      ∃ G : ℂ, Tendsto (F r' r) (𝓝[>] 0) (𝓝 G) ∧ ‖G - M₁‖ < η)
    (h₂ : ∀ η > 0, ∃ δ > 0, ∀ r' r : Fin 4 → ℝ,
      Minkowski.dot r' r' ≠ -m ^ 2 → Minkowski.dot r r ≠ -m ^ 2 →
      dist r' p' < δ → dist r p < δ →
      ∃ G : ℂ, Tendsto (F r' r) (𝓝[>] 0) (𝓝 G) ∧ ‖G - M₂‖ < η) :
    M₁ = M₂ := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨δ₁, hδ₁, hb₁⟩ := h₁ (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, hb₂⟩ := h₂ (ε / 2) (by positivity)
  obtain ⟨r', r, hr', hr, hd', hd⟩ := LszLimit.exists_offShell_near hm hp' hp (lt_min hδ₁ hδ₂)
  obtain ⟨G₁, hG₁, hn₁⟩ := hb₁ r' r hr' hr (hd'.trans_le (min_le_left _ _))
    (hd.trans_le (min_le_left _ _))
  obtain ⟨G₂, hG₂, hn₂⟩ := hb₂ r' r hr' hr (hd'.trans_le (min_le_right _ _))
    (hd.trans_le (min_le_right _ _))
  have hG : G₁ = G₂ := tendsto_nhds_unique hG₁ hG₂
  rw [dist_eq_norm]
  calc ‖M₁ - M₂‖ = ‖(G₁ - M₂) - (G₁ - M₁)‖ := by ring_nf
    _ ≤ ‖G₁ - M₂‖ + ‖G₁ - M₁‖ := norm_sub_le _ _
    _ ≤ ε := by rw [hG] at hn₁ ⊢; linarith

/-! ### The main statements -/

/-- **The LSZ limit of the electron current, with its value.** For `m, m_γ, Λ > 0`, regulator
fermions as in (Z₂), counterterms on shell (Z₅), on-shell positive-energy momenta `(p', p)`,
spins `s'`, `s` and an index `μ`: for every `η > 0` there is `δ > 0` such that at all off-shell
`(r', r)` within `δ` of `(p', p)` the limit `G` of `(1/i) ū_{s'}(p') G^μ_ε(r', r) u_s(p)` as
`ε → 0⁺` exists and lies within `η` of `LszLimit.closedForm`, which is
`ū_{s'}(p') V^μ(p', p) u_s(p)`, with `V^μ` the vertex function (J) at `Z₁ = 1 + δ₁`, plus
`e q² [1/(q² + m_γ²) - 1/(q² + Λ²)] Π(q²) ū_{s'}(p') γ^μ u_s(p)`, `q = p' - p`. -/
theorem lszLimit_closedForm (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) (p' p : Fin 4 → ℝ)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (s' s : Fin 2) (μ : Fin 4) :
    ∀ η > 0, ∃ δ > 0, ∀ r' r : Fin 4 → ℝ,
        Minkowski.dot r' r' ≠ -P.m ^ 2 → Minkowski.dot r r ≠ -P.m ^ 2 →
        dist r' p' < δ → dist r p < δ →
        ∃ G : ℂ, Tendsto (fun ε : ℝ => (1 / I) *
            (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
              (Matrix.of (fun α β => connectedFunction { P with ε := ε } 1 1 3 ![r'] ![r]
                ![r' - r] ![α] ![β] ![μ]) *ᵥ Dirac.spinor P.m p s)))
          (𝓝[>] 0) (𝓝 G) ∧
          ‖G - LszLimit.closedForm P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ p' p hp' hp hp0' hp0 s' s μ‖
            < η := by
  obtain ⟨G, h1, h2⟩ := LszLimit.exists_tendsto_offShell P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon hp'
    hp hp0' hp0 s' s μ
  exact LszLimit.etaDelta_of_tendsto (F := fun r' r ε => (1 / I) *
    (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
      (Matrix.of (fun α β => connectedFunction { P with ε := ε } 1 1 3 ![r'] ![r]
        ![r' - r] ![α] ![β] ![μ]) *ᵥ Dirac.spinor P.m p s))) h1 h2

/-- **The LSZ amplitude of the electron current exists and is unique.** For `m, m_γ, Λ > 0`,
regulator fermions as in (Z₂) and counterterms on shell (Z₅), for on-shell positive-energy
momenta `(p', p)`, spins `s'`, `s` and an index `μ` there is exactly one number `M` that is the
iterated limit of `(1/i) ū_{s'}(p') G^μ_ε(r', r) u_s(p)`: first `ε → 0⁺` at off-shell `(r', r)`,
then `(r', r) → (p', p)` through off-shell momenta. It is `LszLimit.closedForm`
(`QED.WickModel.lszLimit_closedForm`). -/
theorem existsUnique_lszLimit (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ) :
    ∀ (p' p : Fin 4 → ℝ), Minkowski.dot p' p' = -P.m ^ 2 → Minkowski.dot p p = -P.m ^ 2 →
      0 < p' 0 → 0 < p 0 → ∀ (s' s : Fin 2) (μ : Fin 4),
      ∃! M : ℂ, ∀ η > 0, ∃ δ > 0, ∀ r' r : Fin 4 → ℝ,
        Minkowski.dot r' r' ≠ -P.m ^ 2 → Minkowski.dot r r ≠ -P.m ^ 2 →
        dist r' p' < δ → dist r p < δ →
        ∃ G : ℂ, Tendsto (fun ε : ℝ => (1 / I) *
            (Dirac.bar (Dirac.spinor P.m p' s') ⬝ᵥ
              (Matrix.of (fun α β => connectedFunction { P with ε := ε } 1 1 3 ![r'] ![r]
                ![r' - r] ![α] ![β] ![μ]) *ᵥ Dirac.spinor P.m p s)))
          (𝓝[>] 0) (𝓝 G) ∧ ‖G - M‖ < η := by
  intro p' p hp' hp hp0' hp0 s' s μ
  have hL := lszLimit_closedForm P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon p' p hp' hp hp0' hp0 s' s μ
  exact ⟨_, hL, fun M hM => LszLimit.eq_of_etaDelta hm.ne' hp' hp hM hL⟩

end QED.WickModel

end
