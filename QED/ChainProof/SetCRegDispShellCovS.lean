/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellCovD
public import QED.ChainProof.SetCRegDispShellSELimit
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c): the limit pair `(A, B)` of the selected self-energy below the shell

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step b4. At an admissible datum
and every limit pair `(A, B)` of `SELimitSel`, for `s` within `covMargin` of `-m²`:

`A(s) = (κ/i) covAX(s)`, `B(s) = -3 (κ/i) covBX(s)` (`seLimitSel_coef_eq`),

with `κ = covKappa = -i e⁴/(32π⁴)` (`covKappa_eq`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Interval

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel
open QED.ChainProof.SetCPauli QED.ChainProof.SetCK
open QED.ChainProof.SetAPauli (regParams regFlavors)
open QED.TwoLoop.VPHalfAtAssembly (cOne specMu mem_Ioo_mul_pos)

theorem covKappa_eq (P : Params) :
    covKappa P = -I * ((P.e ^ 4 / (32 * π ^ 4) : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [covKappa, seVK, cOne]
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The margin `min(m_γ²/2, m min(r, m_γ, m))` below and above the shell. -/
noncomputable def covMargin (m mγ r : ℝ) : ℝ := min (mγ ^ 2 / 2) (m * min r (min mγ m))

theorem covMargin_facts {m mγ r : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hr : 0 < r) :
    0 < covMargin m mγ r ∧ 2 * covMargin m mγ r ≤ mγ ^ 2 ∧ covMargin m mγ r ≤ m ^ 2 ∧
      covMargin m mγ r ≤ m * r ∧ covMargin m mγ r ≤ m * min mγ m := by
  unfold covMargin
  have h0 : 0 < min r (min mγ m) := lt_min hr (lt_min hmγ hm)
  have a1 := min_le_left (mγ ^ 2 / 2) (m * min r (min mγ m))
  have a2 := min_le_right (mγ ^ 2 / 2) (m * min r (min mγ m))
  have b1 := min_le_left r (min mγ m)
  have b2 := min_le_right r (min mγ m)
  have b3 := min_le_right mγ m
  refine ⟨lt_min (by positivity) (by positivity), by linarith, ?_, ?_, ?_⟩
  · refine a2.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left (b2.trans b3) hm.le]
  · exact a2.trans (mul_le_mul_of_nonneg_left b1 hm.le)
  · exact a2.trans (mul_le_mul_of_nonneg_left b2 hm.le)

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {S : ℝ × ℝ × ℝ}

theorem regParams_mass_ge (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D S) (f : Fin 3) :
    (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).m ≤ (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).mass f := by
  obtain ⟨hM₁, hM₂, -⟩ := hA
  fin_cases f <;> simp [Params.mass] <;> linarith

/-- **The limit pair below the shell.** -/
theorem seLimitSel_coef_eq (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D S) {r : ℝ} (hr : 0 < r)
    {A B : ℝ → ℂ} (hlim : SetCLink.SELimitSel (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (SetCLink.dZero D) r A B) {t : ℝ}
    (ht : t ∈ Ioo (-P₀.m ^ 2 - covMargin P₀.m mγ r) (-P₀.m ^ 2 + covMargin P₀.m mγ r)) :
    A t = (1 / I) * covKappa (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) *
        (covAX (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) t : ℂ) ∧
      B t = (1 / I) * covKappa (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) * (-3) *
        (covBX (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) t : ℂ) := by
  obtain ⟨hM₁, hM₂, -, -, hmγ, hΛ, hγΛ, hm2, -, -⟩ := id hA
  have hm : 0 < P₀.m := by linarith
  set P := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with hP
  have hmass := regParams_mass_ge hA
  obtain ⟨hδ, hδA, hδm, hδr, hδν⟩ := covMargin_facts hm hmγ hr
  set δ := covMargin P₀.m mγ r with hδdef
  set p := selfEnergyTestMomentum t with hpdef
  have hp : Minkowski.dot p p = t := dot_selfEnergyTestMomentum t
  have h1 : -(P₀.m + r) ^ 2 < Minkowski.dot p p := by
    rw [hp]
    nlinarith [ht.1]
  have hν : 0 < min mγ P₀.m := lt_min hmγ hm
  have h2 : -(P₀.m + min mγ P₀.m) ^ 2 < Minkowski.dot p p := by
    rw [hp]
    nlinarith [ht.1]
  have hP' : P.m = P₀.m := rfl
  obtain ⟨iA, -, -⟩ := hasDerivAt_covAX (P := P) hm hmγ hγΛ hm2 hmass hδ hδA hδm ht
  obtain ⟨iB, -, -⟩ := hasDerivAt_covBX (P := P) hm hmγ hγΛ hm2 hmass hδ hδA hδm ht
  have hint : ∀ α β : Fin 4, ∫ x in (0 : ℝ)..1, seGIntLim P p α β x =
      covKappa P * ((covAX P t : ℂ) * Dirac.slash p α β +
        ((-3 * P.m * covBX P t : ℝ) : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ) α β) := by
    intro α β
    have hpt : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (0 : ℝ) 1 → seGIntLim P p α β x =
        covKappa P * ((covG P covAU t x : ℂ) * Dirac.slash p α β +
          ((-3 * P.m * covG P covBU t x : ℝ) : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ) α β) := by
      filter_upwards [ae_covT_ne (P := P) (hmγ.trans hγΛ), Measure.ae_ne volume (1 : ℝ)]
        with x hx hx1 hxI
      rw [uIoc_of_le zero_le_one] at hxI
      have hxI' : x ∈ Ioo (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx1⟩
      have e := fun f => seCfLim_mul_sePieceLim_eq (P := P) (f := f) hm hmγ hγΛ hm2 (hmass f)
        hxI' (hx hxI' f) hδ hδA hδm ht hp α β
      simp only [seGIntLim, e, covG, covT, covWt, Fin.sum_univ_three]
      push_cast
      ring
    rw [intervalIntegral.integral_congr_ae hpt, intervalIntegral.integral_const_mul]
    have jA0 : IntervalIntegrable (fun x => (covG P covAU t x : ℂ)) volume 0 1 :=
      ⟨iA.1.ofReal, iA.2.ofReal⟩
    have jB0 : IntervalIntegrable (fun x => ((-3 * P.m * covG P covBU t x : ℝ) : ℂ)) volume 0 1 :=
      ⟨(iB.const_mul (-3 * P.m)).1.ofReal, (iB.const_mul (-3 * P.m)).2.ofReal⟩
    have jA := jA0.mul_const (Dirac.slash p α β)
    have jB := jB0.mul_const ((1 : Matrix (Fin 4) (Fin 4) ℂ) α β)
    rw [intervalIntegral.integral_add jA jB, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
    rfl
  have key : ∀ α β : Fin 4,
      (A t • Dirac.slash p + (B t * P₀.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β =
      (((1 / I) * covKappa P * (covAX P t : ℂ)) • Dirac.slash p +
        (((1 / I) * covKappa P * (-3) * (covBX P t : ℂ)) * P₀.m) •
          (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β := by
    intro α β
    have h := seLimitSel_apply_eq hA hlim h1 h2 α β
    rw [hp, hint α β] at h
    rw [h]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hP']
    push_cast
    ring
  have := eq_of_smul_slash_add_apply hm.ne' t key
  simp only [Prod.mk.injEq] at this
  exact this

end QED.ChainProof.SetCRegDisp

end
