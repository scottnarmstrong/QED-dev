/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellCovU
public import QED.ChainProof.SetCRegDispShellSEForm
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c): one flavour piece of the self-energy limit in terms of `covAU`, `covBU`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step b4. Below the shell
(`s = p² ∈ (-m² - δ, -m² + δ)`), at `x ∈ (0, 1)` with `Λ² ≠ μ²`, `μ = specMu M_f x`,
`T = μ²/m²`:

`seCfLim · sePieceLim = κ c_f w(x) (x(1-x))⁻¹ (covAU(T, s) p̸ - 3m covBU(T, s))`,

`κ = -π² seVK cOne`, `w(x) = (1 - 2x)(x²/2 - x³/3)` (`seCfLim_mul_sePieceLim_eq`).
The coincidences `m_γ² = μ²` cannot occur (`μ ≥ 2m > m_γ`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel
open QED.TwoLoop.VPHalfAtAssembly (cOne wOne specMu)

/-- The constant `κ = -π² seVK cOne` of the covariant form. -/
noncomputable def covKappa (P : Params) : ℂ := -((π ^ 2 : ℝ) : ℂ) * seVK P * cOne P

theorem setIntegral_Ioo_mul_ofReal (c : ℂ) (f : ℝ → ℝ) :
    ∫ y in Ioo (0 : ℝ) 1, c * (f y : ℂ) = c * ((∫ y in (0 : ℝ)..1, f y : ℝ) : ℂ) := by
  rw [integral_const_mul, integral_complex_ofReal, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

theorem integrableOn_Ioo_mul_ofReal (c : ℂ) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) :
    IntegrableOn (fun y => c * (f y : ℂ)) (Ioo 0 1) :=
  ((hf.1.mono_set Ioo_subset_Ioc_self).ofReal).const_mul c

/-- The Feynman mass below the shell: `min(m², m_γ²)/4 ≤ y m² + (1-y) m_γ² + y(1-y) s`. -/
theorem le_selfEnergyFeynmanMass_of_margin {m mγ δ s y : ℝ} (hδ : 0 < δ)
    (hδA : 2 * δ ≤ mγ ^ 2) (hs : -m ^ 2 - δ < s) (hy : y ∈ Icc (0 : ℝ) 1) :
    min (m ^ 2) (mγ ^ 2) / 4 ≤ selfEnergyFeynmanMass m mγ s y := by
  obtain ⟨hy0, hy1⟩ := hy
  have hyy : 0 ≤ y * (1 - y) := mul_nonneg hy0 (by linarith)
  have h1 : y * (1 - y) * (-m ^ 2 - δ) ≤ y * (1 - y) * s :=
    mul_le_mul_of_nonneg_left hs.le hyy
  have h2 : y * (1 - y) * δ ≤ (1 - y) * δ :=
    mul_le_mul_of_nonneg_right (by nlinarith) hδ.le
  have h3 : y ^ 2 * m ^ 2 + (1 - y) * (mγ ^ 2 / 2) ≤ selfEnergyFeynmanMass m mγ s y := by
    unfold selfEnergyFeynmanMass
    nlinarith
  have hmin1 := min_le_left (m ^ 2) (mγ ^ 2)
  have hmin2 := min_le_right (m ^ 2) (mγ ^ 2)
  refine le_trans ?_ h3
  rcases le_total y (1 / 2) with h | h
  · have : (1 - y) * (mγ ^ 2 / 2) ≥ mγ ^ 2 / 4 := by nlinarith [sq_nonneg mγ]
    nlinarith [sq_nonneg y, sq_nonneg m]
  · have hy2 : 1 / 4 ≤ y ^ 2 := by nlinarith
    have : m ^ 2 / 4 ≤ y ^ 2 * m ^ 2 := by nlinarith [sq_nonneg m]
    nlinarith [sq_nonneg mγ]

/-- `μ² = M²/(x(1-x)) ≥ 4M²`. -/
theorem specMu_sq_eq {M x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    specMu M x ^ 2 = M ^ 2 / (x * (1 - x)) ∧ 4 * M ^ 2 ≤ specMu M x ^ 2 := by
  have hx1 : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
  have e : specMu M x ^ 2 = M ^ 2 / (x * (1 - x)) := by
    unfold specMu
    rw [Real.sq_sqrt (by positivity)]
  refine ⟨e, ?_⟩
  rw [e, le_div_iff₀ hx1]
  nlinarith [sq_nonneg (2 * x - 1), sq_nonneg M]

/-- **One flavour piece of the self-energy limit below the shell.** -/
theorem seCfLim_mul_sePieceLim_eq {P : Params} {δ s x : ℝ} {f : Fin 3}
    (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hγΛ : P.mγ < P.Λ) (hγ2 : P.mγ < 2 * P.m)
    (hMf : P.m ≤ P.mass f) (hx : x ∈ Ioo (0 : ℝ) 1) (hΛμ : P.Λ ^ 2 ≠ specMu (P.mass f) x ^ 2)
    (hδ : 0 < δ) (hδA : 2 * δ ≤ P.mγ ^ 2) (hδm : δ ≤ P.m ^ 2)
    (hs : s ∈ Ioo (-P.m ^ 2 - δ) (-P.m ^ 2 + δ)) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = s) (α β : Fin 4) :
    seCfLim P x f * sePieceLim P p α β x f =
      covKappa P * (P.loopCoeff f : ℂ) * (((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) : ℝ) : ℂ) *
        ((x * (1 - x) : ℝ) : ℂ)⁻¹ *
        ((covAU P.m P.mγ P.Λ (specMu (P.mass f) x ^ 2 / P.m ^ 2) s : ℂ) * Dirac.slash p α β +
          ((-3 * P.m * covBU P.m P.mγ P.Λ (specMu (P.mass f) x ^ 2 / P.m ^ 2) s : ℝ) : ℂ) *
            (1 : Matrix (Fin 4) (Fin 4) ℂ) α β) := by
  set μ := specMu (P.mass f) x with hμdef
  set T := μ ^ 2 / P.m ^ 2 with hTdef
  have hMf0 : 0 < P.mass f := hm.trans_le hMf
  obtain ⟨hμ2, hμ4⟩ := specMu_sq_eq (M := P.mass f) hx
  rw [← hμdef] at hμ2 hμ4
  have hm4 : 4 * P.m ^ 2 ≤ μ ^ 2 := le_trans (by nlinarith) hμ4
  have hγμ2 : P.mγ ^ 2 < μ ^ 2 := lt_of_lt_of_le (by nlinarith) hm4
  have hμ0 : 0 ≤ μ := Real.sqrt_nonneg _
  have hγμ : P.mγ ≤ μ := (lt_of_pow_lt_pow_left₀ 2 hμ0 hγμ2).le
  have hab : P.mγ ^ 2 ≠ P.Λ ^ 2 := by
    have := pow_lt_pow_left₀ hγΛ hmγ.le two_ne_zero
    exact this.ne
  have hm2 : P.m ^ 2 ≠ 0 := pow_ne_zero 2 hm.ne'
  have hTm : T * P.m ^ 2 = μ ^ 2 := div_mul_cancel₀ _ hm2
  have hT : 0 < T := div_pos (by nlinarith) (by positivity)
  have hac : P.mγ ^ 2 ≠ T * P.m ^ 2 := by rw [hTm]; exact hγμ2.ne
  have hbc : P.Λ ^ 2 ≠ T * P.m ^ 2 := by rw [hTm]; exact hΛμ
  have hδB : 2 * δ ≤ P.Λ ^ 2 := le_trans hδA (pow_le_pow_left₀ hmγ.le hγΛ.le 2)
  have hδU : 2 * δ ≤ T * P.m ^ 2 := by rw [hTm]; nlinarith
  have hΛ : 0 < P.Λ := hmγ.trans hγΛ
  have hneg : Minkowski.dot (-p) (-p) = Minkowski.dot p p := by
    simp only [Minkowski.dot, Pi.neg_apply, neg_mul, mul_neg, neg_neg]
  have hc₀ : 0 < min (P.m ^ 2) (P.mγ ^ 2) / 4 := by
    have := lt_min (pow_pos hm 2) (pow_pos hmγ 2)
    linarith
  have hP : ∀ y ∈ Icc (0 : ℝ) 1, min (P.m ^ 2) (P.mγ ^ 2) / 4 ≤
      selfEnergyFeynmanMass P.m P.mγ (Minkowski.dot (-p) (-p)) y := fun y hy => by
    rw [hneg, hp]
    exact le_selfEnergyFeynmanMass_of_margin hδ hδA hs.1 hy
  rw [sePieceLim_eq_tails hmγ.le hc₀ P p α β x f hP hm.ne' le_rfl hγΛ.le hγμ hab
    hγμ2.ne hΛμ, hp, ← hμdef, ← hTdef]
  set k := μ ^ 2 / (P.mγ ^ 2 - P.Λ ^ 2) ^ 2 with hkdef
  set c₁ : ℂ := I * ((π ^ 2 : ℝ) : ℂ) * (-3 * (P.m : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ) α β)
    with hc₁
  set c₂ : ℂ := I * ((π ^ 2 : ℝ) : ℂ) * Dirac.slash p α β with hc₂
  have hs1 := hs.1
  have hs2 := hs.2
  have iB := intervalIntegrable_tail_seArg hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hs1
  have iA := intervalIntegrable_covAInt hm hmγ hΛ hT hδ hδA hδB hδU hab hac hbc hs1 hs2
  -- the pointwise identity on `(0, 1)`
  have hpt : ∀ y ∈ Ioo (0 : ℝ) 1,
      I * ((π ^ 2 : ℝ) : ℂ) * ((k * photonTail (vpPhotonT P.m P.mγ P.Λ T) (seArg P.m s y) : ℝ) :
          ℂ) * (-3 * (P.m : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ) α β +
            (3 * (y : ℂ) - 1) * Dirac.slash p α β) +
        I * ((π ^ 2 : ℝ) : ℂ) * ((k * (-2 * y ^ 2 * s *
            quadTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y) -
          (1 - y) * (bubTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y) -
            seArg P.m s y * quadTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y))) : ℝ) :
              ℂ) * Dirac.slash p α β =
        c₁ * ((k * photonTail (vpPhotonT P.m P.mγ P.Λ T) (seArg P.m s y) : ℝ) : ℂ) +
          c₂ * ((k * covAInt P.m P.mγ P.Λ T s y : ℝ) : ℂ) := by
    intro y hy
    have hw := seArg_gt hδ hy hs1
    have hbub : bubTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y) =
        photonTail (vpPhotonT P.m P.mγ P.Λ T) (seArg P.m s y) := by
      rw [← hTm, ← photonTailVP_eq_bubTailVP, photonTail_vpPhotonT_eq hab hac hbc
        (by linarith) (by linarith) (by linarith)]
    have h1 : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
    have hw' : (1 - y) * seArg P.m s y = y * P.m ^ 2 + y * (1 - y) * s := by
      unfold seArg
      field_simp
    have hr : (3 * y - 1) * photonTail (vpPhotonT P.m P.mγ P.Λ T) (seArg P.m s y) +
        (-2 * y ^ 2 * s * quadTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y) -
          (1 - y) * (bubTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y) -
            seArg P.m s y * quadTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y))) =
        covAInt P.m P.mγ P.Λ T s y := by
      rw [hbub]
      unfold covAInt
      rw [hTm]
      linear_combination quadTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y) * hw'
    rw [← hr, hc₁, hc₂]
    push_cast
    ring
  -- integrability of the original integrands
  have hq : IntervalIntegrable (fun y => k * (covAInt P.m P.mγ P.Λ T s y -
      (3 * y - 1) * photonTail (vpPhotonT P.m P.mγ P.Λ T) (seArg P.m s y))) volume 0 1 :=
    (iA.sub (iB.continuousOn_mul (by fun_prop))).const_mul k
  have hI₁ : IntegrableOn (fun y : ℝ => I * ((π ^ 2 : ℝ) : ℂ) *
      ((k * photonTail (vpPhotonT P.m P.mγ P.Λ T) (seArg P.m s y) : ℝ) : ℂ) *
        (-3 * (P.m : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ) α β +
          (3 * (y : ℂ) - 1) * Dirac.slash p α β)) (Ioo 0 1) := by
    refine ((integrableOn_Ioo_mul_ofReal c₁ (iB.const_mul k)).add
      (integrableOn_Ioo_mul_ofReal c₂ ((iB.const_mul k).continuousOn_mul
        (g := fun y => 3 * y - 1) (by fun_prop)))).congr_fun (fun y _ => ?_) measurableSet_Ioo
    simp only [hc₁, hc₂, Pi.add_apply]
    push_cast
    ring
  have hI₂ : IntegrableOn (fun y : ℝ => I * ((π ^ 2 : ℝ) : ℂ) * ((k * (-2 * y ^ 2 * s *
            quadTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y) -
          (1 - y) * (bubTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y) -
            seArg P.m s y * quadTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y))) : ℝ) :
              ℂ) * Dirac.slash p α β) (Ioo 0 1) := by
    refine (integrableOn_Ioo_mul_ofReal c₂ hq).congr_fun (fun y hy => ?_) measurableSet_Ioo
    have hw := seArg_gt hδ hy hs1
    have hbub : bubTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y) =
        photonTail (vpPhotonT P.m P.mγ P.Λ T) (seArg P.m s y) := by
      rw [← hTm, ← photonTailVP_eq_bubTailVP, photonTail_vpPhotonT_eq hab hac hbc
        (by linarith) (by linarith) (by linarith)]
    have h1 : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
    have hw' : (1 - y) * seArg P.m s y = y * P.m ^ 2 + y * (1 - y) * s := by
      unfold seArg
      field_simp
    have hr : covAInt P.m P.mγ P.Λ T s y -
        (3 * y - 1) * photonTail (vpPhotonT P.m P.mγ P.Λ T) (seArg P.m s y) =
        -2 * y ^ 2 * s * quadTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y) -
          (1 - y) * (bubTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y) -
            seArg P.m s y * quadTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y)) := by
      rw [hbub]
      unfold covAInt
      rw [hTm]
      linear_combination -quadTailVP (P.mγ ^ 2) (P.Λ ^ 2) (μ ^ 2) (seArg P.m s y) * hw'
    simp only [hc₂]
    rw [hr]
    ring
  have hJ := integral_add hI₁ hI₂
  rw [← hJ, setIntegral_congr_fun measurableSet_Ioo hpt,
    integral_add (integrableOn_Ioo_mul_ofReal c₁ (iB.const_mul k))
      (integrableOn_Ioo_mul_ofReal c₂ (iA.const_mul k)),
    setIntegral_Ioo_mul_ofReal, setIntegral_Ioo_mul_ofReal,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  change seCfLim P x f * (I * cOne P * wOne x * (c₁ * ((k * covBU P.m P.mγ P.Λ T s : ℝ) : ℂ) +
    c₂ * ((k * covAU P.m P.mγ P.Λ T s : ℝ) : ℂ))) = _
  have hx1 : x * (1 - x) ≠ 0 := (mul_pos hx.1 (by linarith [hx.2])).ne'
  have hAB2 : ((P.mγ ^ 2 - P.Λ ^ 2) ^ 2 : ℝ) = (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 := by ring
  have hk' : k = 1 / (x * (1 - x)) * (P.mass f ^ 2) / (P.Λ ^ 2 - P.mγ ^ 2) ^ 2 := by
    rw [hkdef, hμ2, hAB2]
    ring
  have key : seCfLim P x f * (I * cOne P * wOne x) * (I * ((π ^ 2 : ℝ) : ℂ)) * (k : ℂ) =
      covKappa P * (P.loopCoeff f : ℂ) * (((1 - 2 * x) * (x ^ 2 / 2 - x ^ 3 / 3) : ℝ) : ℂ) *
        ((x * (1 - x) : ℝ) : ℂ)⁻¹ := by
    simp only [seCfLim, covKappa, wOne]
    rw [hk']
    have h1 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
    have h2 : (1 : ℂ) - x ≠ 0 := by
      have : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
      exact_mod_cast this
    have h3 : ((P.Λ : ℂ) ^ 2 - (P.mγ : ℂ) ^ 2) ≠ 0 := by
      have : P.Λ ^ 2 - P.mγ ^ 2 ≠ 0 := sub_ne_zero.2 hab.symm
      exact_mod_cast this
    have h4 : (P.mass f : ℂ) ≠ 0 := by exact_mod_cast hMf0.ne'
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [hc₁, hc₂]
  push_cast at key ⊢
  linear_combination ((covAU P.m P.mγ P.Λ T s : ℂ) * Dirac.slash p α β +
    (-3 * (P.m : ℂ) * (covBU P.m P.mγ P.Λ T s : ℂ)) * (1 : Matrix (Fin 4) (Fin 4) ℂ) α β) * key

end QED.ChainProof.SetCRegDisp

end
