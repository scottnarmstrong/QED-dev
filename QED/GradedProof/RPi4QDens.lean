/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4PairDensClass
public import QED.GradedProof.RPi4Cov
public import QED.GradedProof.RPi4FLin

/-!
# (R-Π₄) step L6b′: the projected class sum as a photon-mass integral

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6b′ (heavy photon
pair). The projected class sum `qPair` at a photon pair `0 < a < b` is the photon-mass integral
`∫_{a²}^{b²} qDens(s, u) du` of a density read at the tilted momentum `k'(s)`
(`QED.GradedProof.RPi4.qPair_eq_tilt`): the class densities `vDens` of `VA`, `VB`, `VC` and the
mass-insertion density `∑_g σ(M_g, u) · fLim(single g 1)`.

* `ctPair_eq_integral_sigma`: `ctPair e m a b = ∫_{a²}^{b²} σ(e, m, u) du`;
  `sigma_monotoneOn`, `intervalIntegrable_sigma`.
* `qDens`, `qPair_eq_integral`.
* `norm_qPair_sub_le_of_dens` (**reduction of L6d**): a bound `‖qDens(s, u) - qDens(0, u)‖ ≤ g(u)`
  on `[R₀², ∞)` with `g` integrable there gives `‖ΔQ(b, d; s)‖ ≤ ∫_{b²}^{∞} g` for
  `R₀ ≤ b ≤ d`.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.WickModel (Params onShellδ₂ onShellδm)

/-- **The mass counterterm at a photon pair as a photon-mass integral.** -/
theorem ctPair_eq_integral_sigma (e : ℝ) {m a b : ℝ} (hm : m ≠ 0) (ha : 0 < a) (hb : 0 < b) :
    ctPair e m a b = ∫ u in a ^ 2..b ^ 2, sigma e m u := by
  let P : Params := ⟨e, 0, 0, 0, 0, m, a, b, 0, 0, 0, 0, 0⟩
  have h := onShellδm_sub_onShellδ₂_eq_integral_sigma P hm ha hb
  rw [onShellδm_sub_onShellδ₂_eq_integral] at h
  exact h

/-- `σ(e, m, ·)` is monotone on `(0, ∞)`. -/
theorem sigma_monotoneOn (e : ℝ) {m : ℝ} (hm : m ≠ 0) : MonotoneOn (sigma e m) (Ioi 0) := by
  intro u hu v hv huv
  have hint : ∀ w : ℝ, 0 < w → IntervalIntegrable
      (fun x => (1 - x ^ 2) / (x ^ 2 * m ^ 2 + (1 - x) * w)) volume 0 1 := fun w hw =>
    ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx =>
      (onShell_denom_pos hm (by rwa [uIcc_of_le zero_le_one] at hx) hw).ne')
  have hle : ∫ x in (0 : ℝ)..1, (1 - x ^ 2) / (x ^ 2 * m ^ 2 + (1 - x) * v) ≤
      ∫ x in (0 : ℝ)..1, (1 - x ^ 2) / (x ^ 2 * m ^ 2 + (1 - x) * u) := by
    refine intervalIntegral.integral_mono_on zero_le_one (hint v hv) (hint u hu) fun x hx => ?_
    have h1 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hu' := onShell_denom_pos hm hx (show (0 : ℝ) < u from hu)
    exact div_le_div_of_nonneg_left h1 hu' (by nlinarith [hx.2])
  simp only [sigma]
  have hc : 0 ≤ e ^ 2 / (8 * Real.pi ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hle hc]

theorem intervalIntegrable_sigma (e : ℝ) {m a b : ℝ} (hm : m ≠ 0) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (sigma e m) volume (a ^ 2) (b ^ 2) := by
  refine MonotoneOn.intervalIntegrable ((sigma_monotoneOn e hm).mono fun u hu => ?_)
  exact lt_of_lt_of_le (lt_min (pow_pos ha 2) (pow_pos hb 2)) hu.1

section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

/-- **The photon-mass density of the projected class sum**, read at the tilted momentum
`k'(s) = tiltVec c s`: `-(i/c²)(vDens_VA + vDens_VB + vDens_VC + ∑_g σ(M_g, u) fLim_g)²³`. -/
noncomputable def qDens (e m₀ c s u : ℝ) : ℂ :=
  -I / ((c ^ 2 : ℝ) : ℂ) *
    (vDens aVA baseVA cVA Φ e m₀ u (tiltVec c s) 2 3 +
      vDens aVB baseVB cVB Φ e m₀ u (tiltVec c s) 2 3 +
      vDens aVC baseVC cVC Φ e m₀ u (tiltVec c s) 2 3 +
      ∑ g, (sigma e (Φ.mass g) u : ℂ) * fLim Φ rep e (Pi.single g 1) (tiltVec c s) 2 3)

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The projected class sum at a photon pair is the photon-mass integral of `qDens`.** -/
theorem qPair_eq_integral (P : Params) (he : P.e ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {c s : ℝ} (hc : 0 < c) (hs : -(4 * m₀ ^ 2) < s) (hs2 : s < 2 * c ^ 2) :
    IntervalIntegrable (qDens Φ rep P.e m₀ c s) volume (a ^ 2) (b ^ 2) ∧
      qPair Φ rep P.e a b s = ∫ u in a ^ 2..b ^ 2, qDens Φ rep P.e m₀ c s u := by
  have hb : 0 < b := ha.trans hab
  set k := tiltVec c s
  have hk : -(4 * m₀ ^ 2) < Minkowski.dot k k := by rw [dot_tiltVec hs2.le]; exact hs
  have hk' : -(2 * m₀) ^ 2 < Minkowski.dot k k := by
    rw [show (2 * m₀) ^ 2 = 4 * m₀ ^ 2 by ring]; exact hk
  have hmg : ∀ g, Φ.mass g ≠ 0 := fun g => (hm₀.trans_le (hmass g)).ne'
  obtain ⟨iA, eA⟩ := pairInt_vVal_VA Φ hm₀ hmass P.e 2 3 k hk' a b ha hab
  obtain ⟨iB, eB⟩ := pairInt_vVal_VB Φ hm₀ hmass P.e 2 3 k hk' a b ha hab
  obtain ⟨iC, eC⟩ := pairInt_vVal_VC Φ hm₀ hmass P.e 2 3 k hk' a b ha hab
  dsimp only at iA iB iC eA eB eC
  have iS : ∀ g ∈ Finset.univ, IntervalIntegrable
      (fun u => (sigma P.e (Φ.mass g) u : ℂ) * fLim Φ rep P.e (Pi.single g 1) k 2 3)
      volume (a ^ 2) (b ^ 2) := fun g _ =>
    (show IntervalIntegrable (fun u => (sigma P.e (Φ.mass g) u : ℂ)) volume (a ^ 2) (b ^ 2) from
      ⟨(intervalIntegrable_sigma P.e (hmg g) ha hb).1.ofReal,
        (intervalIntegrable_sigma P.e (hmg g) ha hb).2.ofReal⟩).mul_const _
  have iSum : IntervalIntegrable (fun u => ∑ g, (sigma P.e (Φ.mass g) u : ℂ) *
      fLim Φ rep P.e (Pi.single g 1) k 2 3) volume (a ^ 2) (b ^ 2) := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ iS
  have hint : IntervalIntegrable (qDens Φ rep P.e m₀ c s) volume (a ^ 2) (b ^ 2) := by
    have := (((iA.add iB).add iC).add iSum).const_mul (-I / ((c ^ 2 : ℝ) : ℂ))
    refine this.congr fun u _ => ?_
    simp only [qDens, k]
  refine ⟨hint, ?_⟩
  rw [qPair_eq_tilt Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he ha hb hc hs hs2,
    wV_eq_vVal_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hk,
    wV_eq_vVal_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hk,
    wV_eq_vVal_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hk,
    fLim_eq_sum_single Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he _ hk, eA, eB, eC]
  have hS : ∑ g, ((ctPair P.e (Φ.mass g) a b : ℝ) : ℂ) * fLim Φ rep P.e (Pi.single g 1) k 2 3 =
      ∫ u in a ^ 2..b ^ 2, ∑ g, (sigma P.e (Φ.mass g) u : ℂ) *
        fLim Φ rep P.e (Pi.single g 1) k 2 3 := by
    rw [intervalIntegral.integral_finsetSum iS]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [intervalIntegral.integral_mul_const, ctPair_eq_integral_sigma P.e (hmg g) ha hb,
      intervalIntegral.integral_ofReal]
  rw [hS, ← intervalIntegral.integral_add iA iB, ← intervalIntegral.integral_add (iA.add iB) iC,
    ← intervalIntegral.integral_add ((iA.add iB).add iC) iSum,
    ← intervalIntegral.integral_const_mul]
  rfl

end Classes

/-! ### Reduction of the heavy-pair bound to a density bound -/

/-- **From a density bound to the heavy-pair bound.** If `ΔQ(b, d) = ∫_{b²}^{d²} Δ(u) du` for
`R₀ ≤ b < d` and `‖Δ(u)‖ ≤ g(u)` on `[R₀², ∞)` with `g` integrable there, then
`‖ΔQ(b, d)‖ ≤ ∫_{b²}^{∞} g` for `R₀ ≤ b ≤ d` (and `ΔQ(b, b) = 0`). -/
theorem norm_qPair_sub_le_of_dens {Q : ℝ → ℝ → ℂ} {Δ : ℝ → ℂ} {g : ℝ → ℝ} {R₀ : ℝ}
    (hR₀ : 0 < R₀)
    (hQ : ∀ b d, R₀ ≤ b → b < d → IntervalIntegrable Δ volume (b ^ 2) (d ^ 2) ∧
      Q b d = ∫ u in b ^ 2..d ^ 2, Δ u)
    (hQ0 : ∀ b, R₀ ≤ b → Q b b = 0)
    (hg : IntegrableOn g (Ici (R₀ ^ 2))) (hΔ : ∀ u, R₀ ^ 2 ≤ u → ‖Δ u‖ ≤ g u) :
    ∀ b d, R₀ ≤ b → b ≤ d → ‖Q b d‖ ≤ ∫ u in Ici (b ^ 2), g u := by
  intro b d hb hbd
  have hg0 : ∀ u ∈ Ici (b ^ 2), 0 ≤ g u := fun u hu =>
    (norm_nonneg _).trans (hΔ u ((pow_le_pow_left₀ hR₀.le hb 2).trans hu))
  have hgb : IntegrableOn g (Ici (b ^ 2)) :=
    hg.mono_set (Ici_subset_Ici.2 (pow_le_pow_left₀ hR₀.le hb 2))
  rcases eq_or_lt_of_le hbd with rfl | hlt
  · rw [hQ0 b hb, norm_zero]
    exact setIntegral_nonneg measurableSet_Ici hg0
  obtain ⟨-, he⟩ := hQ b d hb hlt
  have hbd2 : b ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (hR₀.le.trans hb) hbd 2
  have hgI : IntervalIntegrable g volume (b ^ 2) (d ^ 2) :=
    (hgb.mono_set (by rw [uIcc_of_le hbd2]; exact Icc_subset_Ici_self)).intervalIntegrable
  rw [he]
  refine (intervalIntegral.norm_integral_le_of_norm_le hbd2 ?_ hgI).trans ?_
  · filter_upwards with u hu
    exact hΔ u ((pow_le_pow_left₀ hR₀.le hb 2).trans hu.1.le)
  · rw [intervalIntegral.integral_of_le hbd2]
    exact setIntegral_mono_set hgb ((ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ hg0))
      (ae_of_all _ fun x (hx : x ∈ Ioc _ _) => (le_of_lt hx.1 : x ∈ Ici _))

end QED.GradedProof.RPi4

end
