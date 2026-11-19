/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtLimitPauli
public import QED.TwoLoop.VPHalfSub
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The five-denominator vertex at a repeated spectral mass

Helper level, Phase 5 Stage 1a (O3-6 for the `δ₃`–`δ₃` classes of set (b)). The value
`QED.TwoLoop.VPHalfAtLimit.s2Prod5Limit_pauliChain_eq_kernVP` of the `(k²)²`, five-photon-denominator
vertex with masses `(a, b, a, b, μ)` is proved there for a spectral mass `μ` different from `a`
and `b`. The `δ₃`–`δ₃` classes need `μ = a` and `μ = b`.

* `tendsto_integral_kernVP_mu`: `∫ kernVP m a b μ s` is continuous in `μ` (dominated convergence,
  with the bound `2/(a² b²)` of `QED.TwoLoop.VPHalf.kern5_le`, which does not depend on `μ`).
* **`s2Prod5Limit_pauliChain_eq_kernVP_all`**: the value for every `μ > 0` (and `a ≠ b`), by
  continuity of both sides in `μ` from the right (`QED.TwoLoop.VPHalfAtLimit.tendsto_prodLimit`).
* `kernVP_sub_eq_photon`: `(b² - a²)² (kernVP m a b a s - kernVP m a b b s) = 2 y² m² K² D(K)³`
  on the open square, with `K = vpK m s z` and `D = photonD a b`: the outer integrand of the
  photon function `s² D(s)³` of the `δ₃`–`δ₃` classes.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.HCSide

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration
open QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtLimit QED.TwoLoop.VPHalf
open QED.TwoLoop.UnitVPLink (photonD)

/-! ### Continuity of the kernel integral in the spectral mass -/

/-- **`∫ kernVP m a b μ s` is continuous in `μ`.** -/
theorem tendsto_integral_kernVP_mu {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {m a b s μ₀ : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hs : 0 ≤ s) (μ : ι → ℝ)
    (hμ : Tendsto μ l (𝓝 μ₀)) :
    Tendsto (fun t => ∫ z, kernVP m a b (μ t) s z ∂feynmanMeasure) l
      (𝓝 (∫ z, kernVP m a b μ₀ s z ∂feynmanMeasure)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * ((a ^ 2)⁻¹ * (b ^ 2)⁻¹))
    (Eventually.of_forall fun t => (measurable_kern5 m a b a b (μ t) s).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_) (integrable_const _) ?_
  · filter_upwards [ae_feynmanMeasure] with z hz
    simp only [kernVP]
    rw [Real.norm_eq_abs, abs_of_nonneg (kern5_nonneg hm hs hz)]
    exact kern5_le ha hb hm hs hz
  · filter_upwards [ae_feynmanMeasure] with z hz
    have hDa := kDen_pos a hm hs hz
    have hDb := kDen_pos b hm hs hz
    have hDμ := kDen_pos μ₀ hm hs hz
    have hden : Tendsto (fun t => kDen m a s z * kDen m b s z * kDen m a s z * kDen m b s z *
        kDen m (μ t) s z) l
        (𝓝 (kDen m a s z * kDen m b s z * kDen m a s z * kDen m b s z * kDen m μ₀ s z)) :=
      (((continuousAt_kDen_mass m s z).tendsto μ₀).comp hμ).const_mul _
    have hne : kDen m a s z * kDen m b s z * kDen m a s z * kDen m b s z * kDen m μ₀ s z ≠ 0 := by
      positivity
    simp only [kernVP, kern5]
    exact tendsto_const_nhds.div hden hne

/-! ### The value at every spectral mass -/

theorem eventually_ne_nhdsGT {μ : ℝ} (c : ℝ) : ∀ᶠ ν in 𝓝[>] μ, ν ≠ c := by
  rcases le_or_gt c μ with h | h
  · exact eventually_nhdsWithin_of_forall fun ν (hν : μ < ν) => ne_of_gt (lt_of_le_of_lt h hν)
  · exact Filter.mem_of_superset (nhdsWithin_le_nhds (Iio_mem_nhds h))
      fun ν (hν : ν < c) => ne_of_lt hν

/-- **The value of the five-denominator vertex `(a, b, a, b, μ)` for every `μ > 0`**, including
the repeated masses `μ = a` and `μ = b`. -/
theorem s2Prod5Limit_pauliChain_eq_kernVP_all (e : ℝ) {m a b μ : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hb : 0 < b) (hμ : 0 < μ) {p' p : Fin 4 → ℝ}
    (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2) (hp0' : 0 < p' 0)
    (hp0 : 0 < p 0) (hq : 0 < Minkowski.dot (p' - p) (p' - p)) (hab : a ≠ b) {α : ℂ}
    (hα : ∀ v : Fin 3 → ℝ, ∃ β γ : ℂ, ∀ t : ℝ,
      pauliChain e m p' p (Fin.cons t v : Fin 4 → ℝ) = α * (t : ℂ) ^ 2 + β * t + γ) :
    s2Prod5Limit α (pauliChain e m p' p) m ![a, b, a, b, μ] p' p =
      I * ((e : ℂ) * (Minkowski.dot (p' - p) (p' - p) : ℂ) *
          (4 * (m : ℂ) ^ 2 + (Minkowski.dot (p' - p) (p' - p) : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) *
          ∫ z, kernVP m a b μ (Minkowski.dot (p' - p) (p' - p)) z ∂feynmanMeasure : ℝ) : ℂ) := by
  obtain ⟨CN, hCN⟩ := pauliChain_bound e m p' p
  set q2 := Minkowski.dot (p' - p) (p' - p)
  set M₀ := min a (min b μ)
  have hM₀ : 0 < M₀ := lt_min ha (lt_min hb hμ)
  have hgt : ∀ᶠ ν in 𝓝[>] μ, μ < ν := self_mem_nhdsWithin
  -- the value for `ν` near `μ`, `ν ≠ a, b`
  have hval : ∀ᶠ ν in 𝓝[>] μ, s2Prod5Limit α (pauliChain e m p' p) m ![a, b, a, b, ν] p' p =
      I * ((e : ℂ) * (q2 : ℂ) * (4 * (m : ℂ) ^ 2 + (q2 : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) * ∫ z, kernVP m a b ν q2 z ∂feynmanMeasure : ℝ) : ℂ) := by
    filter_upwards [hgt, eventually_ne_nhdsGT a, eventually_ne_nhdsGT b] with ν hν hνa hνb
    exact s2Prod5Limit_pauliChain_eq_kernVP e hm ha hb (hμ.trans hν) hp' hp hp0' hp0 hq hab
      hνa.symm hνb.symm hα
  -- continuity of the left side
  have hid : Tendsto (fun ν : ℝ => ν) (𝓝[>] μ) (𝓝 μ) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hge : ∀ {k : ℕ} (v : ℝ → Fin (k + 2) → ℝ),
      (∀ ν, μ < ν → ∀ j, M₀ ≤ v ν j) → ∀ᶠ ν in 𝓝[>] μ, ∀ j, M₀ ≤ v ν j :=
    fun v hv => hgt.mono fun ν hν => hv ν hν
  have hMa : M₀ ≤ a := min_le_left _ _
  have hMb : M₀ ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hMμ : M₀ ≤ μ := (min_le_right _ _).trans (min_le_right _ _)
  have hPL : ∀ {k : ℕ} (v : ℝ → Fin (k + 2) → ℝ) (v₀ : Fin (k + 2) → ℝ),
      Tendsto v (𝓝[>] μ) (𝓝 v₀) → (∀ ν, μ < ν → ∀ j, M₀ ≤ v ν j) →
      Tendsto (fun ν => prodLimit α (pauliChain e m p' p) m (v ν) p' p) (𝓝[>] μ)
        (𝓝 (prodLimit α (pauliChain e m p' p) m v₀ p' p)) :=
    fun v v₀ hv hb' => tendsto_prodLimit hm hM₀ hp' hp hp0' hp0 (continuous_pauliChain e m p' p) α
      hCN hv (hge v hb')
  have l1 := hPL (fun ν => ![a, b, ν]) ![a, b, μ]
    (tendsto_pi_nhds.2 fun j => by
      fin_cases j <;> simp [hid])
    (fun ν hν j => by fin_cases j <;> simp <;> linarith)
  have l2 := hPL (fun ν => ![a, a, b, ν]) ![a, a, b, μ]
    (tendsto_pi_nhds.2 fun j => by
      fin_cases j <;> simp [hid])
    (fun ν hν j => by fin_cases j <;> simp <;> linarith)
  have l3 := hPL (fun ν => ![b, a, b, ν]) ![b, a, b, μ]
    (tendsto_pi_nhds.2 fun j => by
      fin_cases j <;> simp [hid])
    (fun ν hν j => by fin_cases j <;> simp <;> linarith)
  have l4 := hPL (fun ν => ![a, b, a, b, ν]) ![a, b, a, b, μ]
    (tendsto_pi_nhds.2 fun j => by
      fin_cases j <;> simp [hid])
    (fun ν hν j => by fin_cases j <;> simp <;> linarith)
  have hL : Tendsto (fun ν => s2Prod5Limit α (pauliChain e m p' p) m ![a, b, a, b, ν] p' p)
      (𝓝[>] μ) (𝓝 (s2Prod5Limit α (pauliChain e m p' p) m ![a, b, a, b, μ] p' p)) := by
    have := ((l1.sub (l2.const_mul ((a ^ 2 : ℝ) : ℂ))).sub (l3.const_mul ((b ^ 2 : ℝ) : ℂ))).add
      (l4.const_mul (((a ^ 2 : ℝ) : ℂ) * ((b ^ 2 : ℝ) : ℂ)))
    simpa [s2Prod5Limit] using this
  -- continuity of the right side
  have hK := tendsto_integral_kernVP_mu (s := q2) ha hb hm hq.le (fun ν => ν) hid
  have hR : Tendsto (fun ν => I * ((e : ℂ) * (q2 : ℂ) * (4 * (m : ℂ) ^ 2 + (q2 : ℂ)) ^ 2 / m) *
      ((e ^ 2 / (8 * π ^ 2) * ∫ z, kernVP m a b ν q2 z ∂feynmanMeasure : ℝ) : ℂ))
      (𝓝[>] μ) (𝓝 (I * ((e : ℂ) * (q2 : ℂ) * (4 * (m : ℂ) ^ 2 + (q2 : ℂ)) ^ 2 / m) *
        ((e ^ 2 / (8 * π ^ 2) * ∫ z, kernVP m a b μ q2 z ∂feynmanMeasure : ℝ) : ℂ))) :=
    ((continuous_ofReal.tendsto _).comp (hK.const_mul _)).const_mul _
  exact tendsto_nhds_unique hL (hR.congr' (hval.mono fun ν h => h.symm))

/-! ### The photon-function form of the `δ₃`–`δ₃` kernel -/

/-- **The `δ₃`–`δ₃` kernel in photon-function form**: on the open square with `y ≠ 1`,
`(b² - a²)² (kernVP m a b a s - kernVP m a b b s) = 2 y² m² K² D(K)³`. -/
theorem kernVP_sub_eq_photon {m a b s : ℝ} {z : ℝ × ℝ} (hm : 0 < m) (hs : 0 ≤ s)
    (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) (hy1 : z.2 ≠ 1) :
    (b ^ 2 - a ^ 2) ^ 2 * (kernVP m a b a s z - kernVP m a b b s z) =
      2 * (z.2 ^ 2 * m ^ 2 * (vpK m s z ^ 2 * photonD a b (vpK m s z) ^ 3)) := by
  have h1 : 0 < 1 - z.2 := sub_pos.2 (lt_of_le_of_ne hz.2.2 hy1)
  have hK : 0 < vpK m s z := div_pos (kC_pos' hm hs hz) h1
  have hKa : vpK m s z + a ^ 2 ≠ 0 := by positivity
  have hKb : vpK m s z + b ^ 2 ≠ 0 := by positivity
  simp only [kernVP, kern5, kDen_eq_vpK h1.ne', kC_eq_vpK h1.ne', photonD]
  field_simp
  ring

end QED.ChainProof.HCSide

end
