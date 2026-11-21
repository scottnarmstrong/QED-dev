/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdDone
public import QED.GradedProof.RPi4DecRep
public import QED.GradedProof.RPi4AsmJoint

/-!
# R-KS, step K1: the per-flavour limit `decT₀` as a photon-mass integral

Helper level for the identification (R-KS) of the regulator limit of the frozen goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` with the Källén–Sabry function (the open
input `SetAKSFix e`). The per-flavour limit `decT₀ e μ x s` is `asmPolLim / e⁴` at the
configuration `decCfg μ x` (counterterms at the flavour `0`). Here it is written as an integral
over the photon mass² `u` of the subtracted density `ksKDens(u) = qDens(s, u) - qDens(0, u)`,
absolutely convergent at `u → ∞` and improper at `u → 0`. The improper form at `u → 0` needs no
pointwise light-photon bound: it follows from the proved L8 limit and the heavy bound.

The individual classes are not integrable in `u` at either end (each carries a `1/u` tail), so
this summed density is the object every later step of (R-KS) must start from.

Main results:

* `ksKDens`: the subtracted photon-mass density of the configuration `decCfg μ x`;
* `ksK_tendsto_qPair`: the diagonal photon-regulator limit converges to `e⁴ decT₀`;
* `ksK_integrableOn_ksKDens`: `ksKDens` is integrable on `(1, ∞)`;
* `ksK_tendsto_integral_ksKDens`: `∫_a^1 ksKDens → e⁴ decT₀ - ∫_{(1, ∞)} ksKDens` as `a → 0⁺`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open QED.WickModel (Params)

namespace QED.ChainProof.SetAKS

open QED.GradedProof.RPi4

/-- **The subtracted photon-mass density** of the per-flavour configuration `decCfg μ x`
(counterterms at the flavour `0`), read at the tilt `c`. -/
noncomputable def ksKDens (e μ x c s u : ℝ) : ℂ :=
  qDens (decCfg μ x) (fun _ => 0) e μ c s u - qDens (decCfg μ x) (fun _ => 0) e μ c 0 u

/-- A parameter record with charge `e`; only its field `e` is read. -/
def ksKParams (e : ℝ) : Params := ⟨e, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩

theorem ksKParams_e (e : ℝ) : (ksKParams e).e = e := rfl

theorem ksK_mass {μ x : ℝ} (hμ : 0 < μ) (hx : μ ^ 2 ≤ x) (g : Fin 3) :
    μ ≤ (decCfg μ x).mass g :=
  dec_cfg_mass_ge le_rfl hμ hx g

theorem ksK_pv {μ x : ℝ} (hμ : 0 < μ) (hx : μ ^ 2 ≤ x) :
    DecPV (decCfg μ x) (fun _ => 0) (decCfg μ x).coeff :=
  dec_cfg_pv hμ.ne' ((sq_nonneg μ).trans hx)

/-- The face-limit identity at the configuration, on every admissible point. -/
theorem ksK_faceLimitId (e : ℝ) {μ x c s : ℝ} (hμ : 0 < μ) (hx : μ ^ 2 ≤ x) (hc : 0 < c)
    (hs : -(4 * μ ^ 2) < s) (hs2 : s < 2 * c ^ 2) :
    FaceLimitId (decCfg μ x) (fun _ => 0) e μ c s :=
  faceId_faceLimitId_all (decCfg μ x) (fun _ => 0) e hμ (ksK_mass hμ hx) (fun _ => rfl)
    (ksK_pv hμ hx).1 (ksK_pv hμ hx).2 hc hs hs2

theorem ksK_mul_decT₀ {e : ℝ} (he : e ≠ 0) (μ x s : ℝ) :
    (e : ℂ) ^ 4 * decT₀ e μ x s = asmPolLim (decCfg μ x) (fun _ => 0) e s := by
  have h : (e : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 (by exact_mod_cast he)
  rw [decT₀, mul_div_cancel₀ _ h]

/-- **K1a: the diagonal photon-regulator limit** of the subtracted class sum at the
configuration `decCfg μ x` converges to `e⁴ decT₀ e μ x s`. -/
theorem ksK_tendsto_qPair {e μ x s : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hs : -(4 * μ ^ 2) < s) :
    Tendsto (fun Λ : ℝ => qPair (decCfg μ x) (fun _ => 0) e Λ⁻¹ Λ s -
      qPair (decCfg μ x) (fun _ => 0) e Λ⁻¹ Λ 0) atTop
      (𝓝 ((e : ℂ) ^ 4 * decT₀ e μ x s)) := by
  have hpv := ksK_pv hμ hx
  have h00 : -(4 * μ ^ 2) < min s 0 := lt_min hs (by nlinarith)
  obtain ⟨C, hC⟩ := asm_exists_norm_sub_polLim_le (decCfg μ x) (fun _ => 0) (ksKParams e) hμ
    (ksK_mass hμ hx) (fun _ => rfl) hpv.1 hpv.2 he (S₀ := s) (S := s) hs
    fun s' h₀ h₁ => ksK_faceLimitId _ hμ hx (by positivity) (h00.trans_le h₀)
      (h₁.trans_lt (asm_max_lt_two_mul_sq s))
  rw [ksKParams_e] at hC
  rw [ksK_mul_decT₀ he, tendsto_iff_norm_sub_tendsto_zero]
  have hr : Tendsto (fun Λ : ℝ => C * (Real.sqrt Λ⁻¹ + Λ⁻¹)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun Λ : ℝ => Real.sqrt Λ⁻¹) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp tendsto_inv_atTop_zero
      rw [Real.sqrt_zero] at h
      exact h
    simpa using (h1.add tendsto_inv_atTop_zero).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_atTop.2 ⟨1, fun Λ hΛ => ?_⟩) hr
  have hΛ0 : 0 < Λ := one_pos.trans_le hΛ
  exact hC s le_rfl le_rfl Λ⁻¹ Λ (inv_pos.2 hΛ0) (inv_le_one_of_one_le₀ hΛ) hΛ

/-- `ksKDens` is interval integrable on `[a², b²]` for `0 < a < b`, with the photon-pair
value as its integral. -/
theorem ksK_qPair_sub_eq_integral {e μ x c s a b : ℝ} (he : e ≠ 0) (hμ : 0 < μ)
    (hx : μ ^ 2 ≤ x) (hc : 0 < c) (hs : -(4 * μ ^ 2) < s) (hs2 : s < 2 * c ^ 2) (ha : 0 < a)
    (hab : a < b) :
    IntervalIntegrable (ksKDens e μ x c s) volume (a ^ 2) (b ^ 2) ∧
      qPair (decCfg μ x) (fun _ => 0) e a b s - qPair (decCfg μ x) (fun _ => 0) e a b 0 =
        ∫ u in a ^ 2..b ^ 2, ksKDens e μ x c s u := by
  have hpv := ksK_pv hμ hx
  obtain ⟨i1, e1⟩ := qPair_eq_integral (decCfg μ x) (fun _ => 0) hμ (ksK_mass hμ hx)
    (fun _ => rfl) hpv.1 hpv.2 (ksKParams e) he ha hab hc hs hs2
  obtain ⟨i2, e2⟩ := qPair_eq_integral (decCfg μ x) (fun _ => 0) hμ (ksK_mass hμ hx)
    (fun _ => rfl) hpv.1 hpv.2 (ksKParams e) he ha hab hc (s := 0) (by nlinarith)
    (by positivity)
  have hf : ksKDens e μ x c s = fun u =>
      qDens (decCfg μ x) (fun _ => 0) (ksKParams e).e μ c s u -
        qDens (decCfg μ x) (fun _ => 0) (ksKParams e).e μ c 0 u := rfl
  refine ⟨hf ▸ i1.sub i2, ?_⟩
  rw [hf, intervalIntegral.integral_sub i1 i2, ← e1, ← e2]
  rfl

/-- **K1b: the heavy side.** `ksKDens` is integrable on `(1, ∞)`, with
`‖ksKDens(u)‖ ≤ C u^{-3/2}`. -/
theorem ksK_integrableOn_ksKDens {e μ x c s : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hc : 0 < c) (hs : -(4 * μ ^ 2) < s) (hs2 : s < 2 * c ^ 2) :
    IntegrableOn (ksKDens e μ x c s) (Ioi 1) := by
  have hpv := ksK_pv hμ hx
  have h00 : -(4 * μ ^ 2) < min s 0 := lt_min hs (by nlinarith)
  have hS : max s 0 < 2 * c ^ 2 := max_lt hs2 (by positivity)
  obtain ⟨C, hC⟩ := norm_qDens_sub_le (decCfg μ x) (fun _ => 0) (ksKParams e) hμ
    (ksK_mass hμ hx) (fun _ => rfl) hpv.1 hpv.2 he hc h00 (min_le_right _ _) (le_max_right _ _)
    hS fun s' h₀ h₁ => ksK_faceLimitId _ hμ hx hc (h00.trans_le h₀) (h₁.trans_lt hS)
  rw [ksKParams_e] at hC
  -- measurability, from interval integrability on `(1, (n + 2)²]`
  have hU : (⋃ n : ℕ, Ioc (1 : ℝ) (((n : ℝ) + 2) ^ 2)) = Ioi 1 := by
    ext t
    simp only [mem_iUnion, mem_Ioc, mem_Ioi]
    refine ⟨fun ⟨_, h, _⟩ => h, fun h => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_ge t
    refine ⟨n, h, ?_⟩
    nlinarith
  have hm : AEStronglyMeasurable (ksKDens e μ x c s) (volume.restrict (Ioi 1)) := by
    rw [← hU, aestronglyMeasurable_iUnion_iff]
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hi := (ksK_qPair_sub_eq_integral he hμ hx hc hs hs2 one_pos
      (show (1 : ℝ) < (n : ℝ) + 2 by linarith [n.cast_nonneg (α := ℝ)])).1
    rw [one_pow, intervalIntegrable_iff_integrableOn_Ioc_of_le (by nlinarith)] at hi
    exact hi.aestronglyMeasurable
  have hg : IntegrableOn (fun t : ℝ => C * t ^ (-(3 / 2) : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul C
  refine Integrable.mono' hg hm ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun t ht => ?_))
  exact hC s (min_le_left _ _) (le_max_left _ _) t (le_of_lt ht)

/-- **K1c: the light side, as an improper integral.**
`∫_a^1 ksKDens → e⁴ decT₀ - ∫_{(1, ∞)} ksKDens` as `a → 0⁺`. -/
theorem ksK_tendsto_integral_ksKDens {e μ x c s : ℝ} (he : e ≠ 0) (hμ : 0 < μ)
    (hx : μ ^ 2 ≤ x) (hc : 0 < c) (hs : -(4 * μ ^ 2) < s) (hs2 : s < 2 * c ^ 2) :
    Tendsto (fun a : ℝ => ∫ u in a..1, ksKDens e μ x c s u) (𝓝[>] 0)
      (𝓝 ((e : ℂ) ^ 4 * decT₀ e μ x s - ∫ u in Ioi 1, ksKDens e μ x c s u)) := by
  set f := ksKDens e μ x c s with hf
  set g : ℝ → ℂ := fun Λ => ∫ u in Λ⁻¹ ^ 2..1, f u with hg
  -- along `Λ → ∞`
  have hI := ksK_integrableOn_ksKDens he hμ hx hc hs hs2
  have hT : Tendsto g atTop (𝓝 ((e : ℂ) ^ 4 * decT₀ e μ x s - ∫ u in Ioi 1, f u)) := by
    have h1 := ksK_tendsto_qPair he hμ hx hs
    have h2 := intervalIntegral_tendsto_integral_Ioi 1 hI (tendsto_pow_atTop (n := 2) two_ne_zero)
    refine (h1.sub h2).congr' (eventually_atTop.2 ⟨2, fun Λ hΛ => ?_⟩)
    have hΛ1 : 1 < Λ := by linarith
    have hΛ0 : 0 < Λ := by linarith
    have hinv : Λ⁻¹ < Λ := (inv_lt_one_of_one_lt₀ hΛ1).trans hΛ1
    obtain ⟨hi, he'⟩ := ksK_qPair_sub_eq_integral he hμ hx hc hs hs2 (inv_pos.2 hΛ0) hinv
    have hlo : Λ⁻¹ ^ 2 ≤ 1 := by
      have : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ1.le
      nlinarith [inv_pos.2 hΛ0]
    have hhi : 1 ≤ Λ ^ 2 := by nlinarith
    have hs1 : uIcc (Λ⁻¹ ^ 2) 1 ⊆ uIcc (Λ⁻¹ ^ 2) (Λ ^ 2) := by
      rw [uIcc_of_le hlo, uIcc_of_le (hlo.trans hhi)]
      exact Icc_subset_Icc le_rfl hhi
    have hs2' : uIcc 1 (Λ ^ 2) ⊆ uIcc (Λ⁻¹ ^ 2) (Λ ^ 2) := by
      rw [uIcc_of_le hhi, uIcc_of_le (hlo.trans hhi)]
      exact Icc_subset_Icc hlo le_rfl
    have hi1 : IntervalIntegrable f volume (Λ⁻¹ ^ 2) 1 := hi.mono_set hs1
    have hi2 : IntervalIntegrable f volume 1 (Λ ^ 2) := hi.mono_set hs2'
    simp only [hg]
    rw [he', ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    ring
  -- along `a → 0⁺`, with `Λ = (√a)⁻¹`
  have hL : Tendsto (fun a : ℝ => (Real.sqrt a)⁻¹) (𝓝[>] 0) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun a ha =>
      Real.sqrt_pos.2 ha⟩
    simpa using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
  refine (hT.comp hL).congr' (eventually_nhdsWithin_of_forall fun a ha => ?_)
  simp only [Function.comp_apply, hg, inv_inv, Real.sq_sqrt (le_of_lt ha)]

end QED.ChainProof.SetAKS

end
