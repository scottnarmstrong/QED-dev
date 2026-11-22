/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersLaurent
public import QED.DimReg.CubeMellin
public import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax

/-!
# Taylor expansion of a parametric integral through iterated slopes

For `f : ℂ → ℂ` let `D⁰ f = f` and `Dⁿ⁺¹ f = dslope (Dⁿ f) 0` (`QED.ThreeLoopD.i13Dsl`). Then

  `f ε = ∑_{k < n} Dᵏ f (0) εᵏ + εⁿ Dⁿ f (ε)`

identically (`QED.ThreeLoopD.i13Dsl_taylor`). If `f` is holomorphic on `ball 0 R`, so is every
`Dⁿ f` (removable singularities), and a bound `‖f‖ ≤ M` on the circle `‖ε‖ = ρ < R` gives
`‖Dⁿ f‖ ≤ 2ⁿ M / ρⁿ` on the closed disc (maximum modulus).

For a family `h t` of such functions, measurable in `t` and bounded on the circle by an
integrable `M t`, this gives (`QED.ThreeLoopD.hasTruncLaurent_integral_i13Dsl`)

  `∫ h t ε dμ = ∑_{k < n} εᵏ ∫ Dᵏ (h t) (0) dμ + εⁿ ∫ Dⁿ (h t) (ε) dμ`,

with the last integral holomorphic near `0`: a truncated expansion whose coefficients are
integrals of the pointwise Taylor coefficients. `QED.ThreeLoopD.i13Dsl_zero_eq_of_expansion`
identifies the pointwise coefficients from any expansion `f = ∑ aₖ εᵏ + εⁿ g`, `g` continuous.

## Main results

* `QED.ThreeLoopD.i13Dsl_taylor`, `QED.ThreeLoopD.norm_i13Dsl_le`.
* `QED.ThreeLoopD.hasTruncLaurent_integral_i13Dsl`.
* `QED.ThreeLoopD.i13Dsl_zero_eq_of_expansion`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Filter Topology

namespace QED.ThreeLoopD

/-- Iterated slopes at `0`: `D⁰ f = f`, `Dⁿ⁺¹ f = dslope (Dⁿ f) 0`. -/
noncomputable def i13Dsl (f : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => f
  | n + 1 => dslope (i13Dsl f n) 0

@[simp] theorem i13Dsl_zero (f : ℂ → ℂ) : i13Dsl f 0 = f := rfl

theorem i13Dsl_succ (f : ℂ → ℂ) (n : ℕ) : i13Dsl f (n + 1) = dslope (i13Dsl f n) 0 := rfl

theorem i13Dsl_step (f : ℂ → ℂ) (n : ℕ) (ε : ℂ) :
    i13Dsl f n ε = i13Dsl f n 0 + ε * i13Dsl f (n + 1) ε := by
  have := sub_smul_dslope (i13Dsl f n) 0 ε
  rw [sub_zero, smul_eq_mul] at this
  rw [i13Dsl_succ, this]
  ring

theorem i13Dsl_of_ne (f : ℂ → ℂ) (n : ℕ) {ε : ℂ} (hε : ε ≠ 0) :
    i13Dsl f (n + 1) ε = (i13Dsl f n ε - i13Dsl f n 0) / ε := by
  rw [eq_div_iff hε, i13Dsl_step f n ε]
  ring

/-- **The Taylor identity** `f ε = ∑_{k < n} Dᵏ f (0) εᵏ + εⁿ Dⁿ f (ε)`. -/
theorem i13Dsl_taylor (f : ℂ → ℂ) (n : ℕ) (ε : ℂ) :
    f ε = ∑ k ∈ Finset.range n, i13Dsl f k 0 * ε ^ k + ε ^ n * i13Dsl f n ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, i13Dsl_step f n ε]
    ring

theorem differentiableOn_i13Dsl {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (n : ℕ) :
    DifferentiableOn ℂ (i13Dsl f n) (ball 0 R) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (Complex.differentiableOn_dslope (ball_mem_nhds 0 hR)).mpr ih

/-- Maximum modulus on a disc inside the domain of holomorphy. -/
theorem i13_norm_le_of_sphere {h : ℂ → ℂ} {R ρ M : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hh : DifferentiableOn ℂ h (ball 0 R)) (hM : ∀ ε : ℂ, ‖ε‖ = ρ → ‖h ε‖ ≤ M) {ε : ℂ}
    (hε : ‖ε‖ ≤ ρ) : ‖h ε‖ ≤ M := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) ρ) isBounded_ball
    (hh.diffContOnCl_ball (closedBall_subset_ball hρR)) (fun z hz => ?_) ?_
  · rw [frontier_ball 0 hρ.ne'] at hz
    exact hM z (by simpa using hz)
  · rw [closure_ball 0 hρ.ne']
    simpa using hε

/-- **Bounds for the iterated slopes**: `‖Dⁿ f‖ ≤ 2ⁿ M / ρⁿ` on `‖ε‖ ≤ ρ`. -/
theorem norm_i13Dsl_le {f : ℂ → ℂ} {R ρ M : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hM : ∀ ε : ℂ, ‖ε‖ = ρ → ‖f ε‖ ≤ M) (n : ℕ) :
    ∀ ε : ℂ, ‖ε‖ ≤ ρ → ‖i13Dsl f n ε‖ ≤ 2 ^ n * M / ρ ^ n := by
  have hR : 0 < R := hρ.trans hρR
  induction n with
  | zero => intro ε hε; simpa using i13_norm_le_of_sphere hρ hρR hf hM hε
  | succ n ih =>
    refine fun ε hε => i13_norm_le_of_sphere hρ hρR (differentiableOn_i13Dsl hR hf _)
      (fun z hz => ?_) hε
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
    rw [i13Dsl_of_ne f n hz0, norm_div, hz, div_le_iff₀ hρ]
    have h1 := ih z hz.le
    have h2 := ih 0 (by simp [hρ.le])
    calc ‖i13Dsl f n z - i13Dsl f n 0‖ ≤ ‖i13Dsl f n z‖ + ‖i13Dsl f n 0‖ := norm_sub_le _ _
      _ ≤ 2 ^ n * M / ρ ^ n + 2 ^ n * M / ρ ^ n := add_le_add h1 h2
      _ = 2 ^ (n + 1) * M / ρ ^ (n + 1) * ρ := by
        field_simp
        ring

/-- **Measurability of the iterated slopes** of a family holomorphic in the parameter. -/
theorem aestronglyMeasurable_i13Dsl {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hd : ∀ᵐ t ∂μ, DifferentiableOn ℂ (h t) (ball 0 R))
    (hm : ∀ ε ∈ ball (0 : ℂ) R, AEStronglyMeasurable (fun t => h t ε) μ) (n : ℕ) :
    ∀ ε ∈ ball (0 : ℂ) R, AEStronglyMeasurable (fun t => i13Dsl (h t) n ε) μ := by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    have hne : ∀ ε ∈ ball (0 : ℂ) R, ε ≠ 0 →
        AEStronglyMeasurable (fun t => i13Dsl (h t) (n + 1) ε) μ := by
      intro ε hε hε0
      simp_rw [i13Dsl_of_ne _ n hε0, div_eq_mul_inv]
      exact ((ih ε hε).sub (ih 0 (mem_ball_self hR))).mul aestronglyMeasurable_const
    intro ε hε
    by_cases hε0 : ε ≠ 0
    · exact hne ε hε hε0
    rw [not_not] at hε0
    subst hε0
    set z : ℕ → ℂ := fun m => ((R / ((m : ℝ) + 2) : ℝ) : ℂ) with hz
    have hzpos : ∀ m : ℕ, 0 < R / (m + 2) := fun m => div_pos hR (by positivity)
    have hzb : ∀ m, z m ∈ ball (0 : ℂ) R := fun m => by
      rw [mem_ball, dist_zero_right, hz, norm_real, Real.norm_eq_abs, abs_of_pos (hzpos m),
        div_lt_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      nlinarith
    have hzt : Tendsto z atTop (𝓝 0) := by
      have : Tendsto (fun m : ℕ => R / ((m : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      have h2 := (continuous_ofReal.tendsto 0).comp this
      rw [ofReal_zero] at h2
      exact h2
    have hz0 : ∀ m, z m ≠ 0 := fun m => ofReal_ne_zero.mpr (hzpos m).ne'
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun m t => i13Dsl (h t) (n + 1) (z m))
      (fun m => hne _ (hzb m) (hz0 m)) ?_
    filter_upwards [hd] with t ht
    have hc := ((differentiableOn_i13Dsl hR ht (n + 1)).continuousOn.continuousAt
      (ball_mem_nhds 0 hR))
    exact hc.tendsto.comp hzt

/-- **Truncated expansion of a parametric integral.** If `h t` is holomorphic on `ball 0 R`
for a.e. `t`, measurable in `t`, and bounded on the circle `‖ε‖ = ρ` by an integrable `M`, then
`∫ h t ε dμ = ∑_{k < n} εᵏ ∫ Dᵏ (h t) 0 dμ + O(εⁿ)` with a holomorphic remainder. -/
theorem hasTruncLaurent_integral_i13Dsl {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℂ → ℂ} {R ρ : ℝ} {M : α → ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hMi : Integrable M μ)
    (hd : ∀ᵐ t ∂μ, DifferentiableOn ℂ (h t) (ball 0 R))
    (hm : ∀ ε ∈ ball (0 : ℂ) R, AEStronglyMeasurable (fun t => h t ε) μ)
    (hb : ∀ᵐ t ∂μ, ∀ ε : ℂ, ‖ε‖ = ρ → ‖h t ε‖ ≤ M t) (n : ℕ) :
    HasTruncLaurent (fun ε => ∫ t, h t ε ∂μ)
      (fun ε => ∑ k ∈ Finset.range n, (∫ t, i13Dsl (h t) k 0 ∂μ) * ε ^ k) n := by
  have hR : 0 < R := hρ.trans hρR
  have hmeas := aestronglyMeasurable_i13Dsl hR hd hm
  have hbd : ∀ k, ∀ᵐ t ∂μ, ∀ ε : ℂ, ‖ε‖ ≤ ρ → ‖i13Dsl (h t) k ε‖ ≤ 2 ^ k * M t / ρ ^ k :=
    fun k => by
      filter_upwards [hd, hb] with t ht htb
      exact norm_i13Dsl_le hρ hρR ht htb k
  have hball : ∀ ε : ℂ, ‖ε‖ ≤ ρ → ε ∈ ball (0 : ℂ) R := fun ε hε => by
    rw [mem_ball, dist_zero_right]; linarith
  have hint : ∀ k, ∀ ε : ℂ, ‖ε‖ ≤ ρ → Integrable (fun t => i13Dsl (h t) k ε) μ :=
    fun k ε hε => Integrable.mono' ((hMi.const_mul (2 ^ k)).div_const (ρ ^ k))
      (hmeas k ε (hball ε hε)) (by filter_upwards [hbd k] with t ht; exact ht ε hε)
  refine ⟨fun ε => ∫ t, i13Dsl (h t) n ε ∂μ, ?_, ?_⟩
  · have hdiff : ∀ ε₀ ∈ ball (0 : ℂ) (ρ / 2),
        DifferentiableAt ℂ (fun ε => ∫ t, i13Dsl (h t) n ε ∂μ) ε₀ := by
      intro ε₀ h0
      have hsub : ∀ ε ∈ ball ε₀ (ρ / 2), ‖ε‖ ≤ ρ := fun ε hε => by
        rw [mem_ball, dist_eq_norm] at hε
        rw [mem_ball, dist_zero_right] at h0
        linarith [norm_sub_norm_le ε ε₀]
      refine QED.DimReg.differentiableAt_integral_of_holomorphic (half_pos hρ)
        ((hMi.const_mul (2 ^ n)).div_const (ρ ^ n))
        (fun ε hε => hmeas n ε (hball ε (hsub ε hε))) ?_ ?_
      · filter_upwards [hbd n] with t ht ε hε using ht ε (hsub ε hε)
      · filter_upwards [hd] with t ht
        exact (differentiableOn_i13Dsl hR ht n).mono fun ε hε => hball ε (hsub ε hε)
    exact DifferentiableOn.analyticAt (fun ε hε => (hdiff ε hε).differentiableWithinAt)
      (ball_mem_nhds 0 (half_pos hρ))
  · refine eventually_nhdsWithin_of_eventually_nhds
      (eventually_of_mem (closedBall_mem_nhds 0 hρ) fun ε hε => ?_)
    rw [mem_closedBall, dist_zero_right] at hε
    have hsplit : ∀ t, h t ε = ∑ k ∈ Finset.range n, i13Dsl (h t) k 0 * ε ^ k +
        ε ^ n * i13Dsl (h t) n ε := fun t => i13Dsl_taylor (h t) n ε
    simp_rw [hsplit]
    have h0 : ‖(0 : ℂ)‖ ≤ ρ := by simp [hρ.le]
    rw [integral_add (integrable_finsetSum _ fun k _ => (hint k 0 h0).mul_const _)
        ((hint n ε hε).const_mul _), integral_finsetSum _ fun k _ => (hint k 0 h0).mul_const _,
      integral_const_mul]
    simp_rw [integral_mul_const]

/-- **Identification of the pointwise coefficients**: if `f = ∑_{k < n} aₖ εᵏ + εⁿ g` near `0`
with `f` holomorphic near `0` and `g` continuous at `0`, then `Dᵏ f (0) = aₖ` for `k < n`. -/
theorem i13Dsl_zero_eq_of_expansion {f g : ℂ → ℂ} {a : ℕ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : ContinuousAt g 0) {n : ℕ}
    (he : ∀ ε ∈ ball (0 : ℂ) R, f ε = ∑ k ∈ Finset.range n, a k * ε ^ k + ε ^ n * g ε) :
    ∀ k < n, i13Dsl f k 0 = a k := by
  -- Both sides give expansions of `f`; compare the remainders `εᵏ (Dᵏ f ε - rₖ ε)`.
  have key : ∀ k ≤ n, ∀ ε ∈ ball (0 : ℂ) R,
      i13Dsl f k ε = ∑ j ∈ Finset.range (n - k), a (k + j) * ε ^ j + ε ^ (n - k) * g ε := by
    intro k
    induction k with
    | zero => intro _ ε hε; simpa using he ε hε
    | succ k ih =>
      intro hk ε hε
      have hk' : k ≤ n := by omega
      have hnk : n - k = (n - (k + 1)) + 1 := by omega
      have hval : i13Dsl f k 0 = a k := by
        have := ih hk' 0 (mem_ball_self hR)
        rw [hnk, Finset.sum_range_succ'] at this
        simpa using this
      have hcont : ContinuousAt (i13Dsl f (k + 1)) ε :=
        ((differentiableOn_i13Dsl hR hf (k + 1)).continuousOn.continuousAt
          (isOpen_ball.mem_nhds hε))
      have hform : ∀ z ∈ ball (0 : ℂ) R, z ≠ 0 → i13Dsl f (k + 1) z =
          ∑ j ∈ Finset.range (n - (k + 1)), a (k + 1 + j) * z ^ j +
            z ^ (n - (k + 1)) * g z := by
        intro z hz hz0
        rw [i13Dsl_of_ne f k hz0, ih hk' z hz, hval, hnk, Finset.sum_range_succ',
          div_eq_iff hz0, add_mul, Finset.sum_mul, pow_succ]
        have hs : ∀ j ∈ Finset.range (n - (k + 1)), a (k + (j + 1)) * z ^ (j + 1) =
            a (k + 1 + j) * z ^ j * z := fun j _ => by
          rw [show k + (j + 1) = k + 1 + j by omega]; ring
        rw [Finset.sum_congr rfl hs]
        simp only [add_zero, pow_zero, mul_one]
        ring
      by_cases hε0 : ε = 0
      · subst hε0
        -- continuity: approach `0` along nonzero points
        set F : ℂ → ℂ := fun z => ∑ j ∈ Finset.range (n - (k + 1)), a (k + 1 + j) * z ^ j +
          z ^ (n - (k + 1)) * g z
        have hFc : ContinuousAt F 0 := by
          refine (continuous_finsetSum _ fun j _ => by fun_prop).continuousAt.add ?_
          exact (continuous_pow _).continuousAt.mul hg
        have hev : i13Dsl f (k + 1) =ᶠ[𝓝[≠] 0] F :=
          eventually_nhdsWithin_iff.mpr (eventually_of_mem (ball_mem_nhds 0 hR)
            fun z hz hz0 => hform z hz hz0)
        have h1 := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
        have h2 := (hFc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))).congr'
          hev.symm
        exact tendsto_nhds_unique h1 h2
      · exact hform ε hε hε0
  intro k hk
  have := key k hk.le 0 (mem_ball_self hR)
  rw [show n - k = (n - k - 1) + 1 by omega, Finset.sum_range_succ'] at this
  simpa using this

end QED.ThreeLoopD
