/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Clause3

/-!
# (X₁): continuity of the order-`e⁴` form factor `A` at the mass shell

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57). The leg limits `QED.GradedProof.X1.tendsto_leg_in`, `tendsto_leg_out` need the
form factor `A` of the self-energy `A(p²) p̸ + B(p²) M` to be continuous at `-M²`. The on-shell
condition (G₉) does not say so; for the order-`e⁴` self-energy it follows from the internal
result of (G-Σ₂) that the limit along the time axis `p = t e₀` is differentiable in `t`
(`QED.GradedProof.SE2.hasSEFormD_selfEnergyPart`). There `A(-t²) t = -W(t)₀₂`, so near `t = M`
`A(-t²) = -W(t)₀₂ / t`, and `A(s) = -W(√(-s))₀₂ / √(-s)` near `s = -M²`.

## Main statements

* `QED.GradedProof.X1.continuousAt_A_of_hasSEFormD`: the generic statement.
* `QED.GradedProof.X1.continuousAt_A_selfEnergyPart_two`: for the order-`e⁴` self-energy of
  flavour `f`, any `A`, `B` with the limit property on a region `p² > -R²`, `R > M_f`.
-/

@[expose] public section

open Matrix Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded QED.GradedProof.SE2

namespace QED.GradedProof.X1

/-- **Continuity of `A` at `-M²`** for a family with a limit differentiable along lines, whose
limit is `A(p²) p̸ + B(p²) M` on a region `p² > -R²` with `R > M`. -/
theorem continuousAt_A_of_hasSEFormD {T M R : ℝ} {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hG : HasSEFormD T G) (hM : 0 < M) (hMT : M < T) (hMR : M < R) (A B : ℝ → ℂ)
    (hAB : ∀ p : Fin 4 → ℝ, -R ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε : ℝ => G ε p α β) (𝓝[>] 0)
        (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
          + (B (Minkowski.dot p p) * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) :
    ContinuousAt A (-M ^ 2) := by
  obtain ⟨W, hW⟩ := hG timeVec
  have hTM : -T ^ 2 < -M ^ 2 := by nlinarith
  have hRM : -R ^ 2 < -M ^ 2 := by nlinarith
  -- the continuous function `t ↦ -W(t)₀₂ / t` at `t = M`
  have hc : ContinuousAt (fun t : ℝ => -W t 0 2 / (t : ℂ)) M := by
    have hd := (hW M (by rwa [dot_smul_timeVec]) 0 2).2.continuousAt
    exact hd.neg.div continuous_ofReal.continuousAt (ofReal_ne_zero.mpr hM.ne')
  -- `s ↦ √(-s)` is continuous with value `M` at `-M²`
  have hs : ContinuousAt (fun s : ℝ => Real.sqrt (-s)) (-M ^ 2) :=
    (Real.continuous_sqrt.comp continuous_neg).continuousAt
  have hsM : Real.sqrt (-(-M ^ 2)) = M := by rw [neg_neg, Real.sqrt_sq hM.le]
  have hcomp : ContinuousAt (fun s : ℝ => -W (Real.sqrt (-s)) 0 2 / (Real.sqrt (-s) : ℂ))
      (-M ^ 2) := by
    have := ContinuousAt.comp (f := fun s : ℝ => Real.sqrt (-s)) (by rw [hsM]; exact hc) hs
    exact this
  refine hcomp.congr ?_
  -- near `-M²`: `s < 0`, `-T² < s`, `-R² < s`
  have hev : ∀ᶠ s : ℝ in 𝓝 (-M ^ 2), s < 0 ∧ -T ^ 2 < s ∧ -R ^ 2 < s := by
    have h0 : -M ^ 2 < 0 := by nlinarith
    filter_upwards [gt_mem_nhds h0, lt_mem_nhds hTM, lt_mem_nhds hRM] with s h1 h2 h3
    exact ⟨h1, h2, h3⟩
  filter_upwards [hev] with s ⟨hs0, hsT, hsR⟩
  set t := Real.sqrt (-s) with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr (by linarith)
  have hts : -t ^ 2 = s := by rw [ht, Real.sq_sqrt (by linarith), neg_neg]
  have hdot : Minkowski.dot (t • timeVec) (t • timeVec) = s := by rw [dot_smul_timeVec, hts]
  have h02 := tendsto_nhds_unique (hAB _ (by rwa [hdot]) 0 2)
    (hW t (by rwa [hdot]) 0 2).1
  obtain ⟨s02, -⟩ := slash_timeVec_apply
  simp only [hdot, Dirac.slash_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, s02,
    Matrix.one_apply_ne (show (0 : Fin 4) ≠ 2 by decide)] at h02
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr htpos.ne'
  rw [← h02]
  field_simp
  ring

/-- **Continuity of the order-`e⁴` form factor `A` at `-M_f²`**, for any `A`, `B` with the
limit property of the order-`e⁴` self-energy of flavour `f` on a region `p² > -R²`, `R > M_f`. -/
theorem continuousAt_A_selfEnergyPart_two (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) {R : ℝ}
    (hR : Φ.mass f < R) (A B : ℝ → ℂ)
    (hAB : ∀ p : Fin 4 → ℝ, -R ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f 2 p α β) (𝓝[>] 0)
        (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
          + (B (Minkowski.dot p p) * Φ.mass f) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) :
    ContinuousAt A (-Φ.mass f ^ 2) := by
  have hν0 : 0 < min (min P.mγ P.Λ) (2 * m₀) := lt_min (lt_min hmγ hΛ) (by linarith)
  exact continuousAt_A_of_hasSEFormD
    (hasSEFormD_selfEnergyPart (fun C h4 hC => classFormD_of_order_four classFormD_repR
      classFormD_repX classFormD_repV classFormD_repF classFormD_repP0 classFormD_repP1
      classFormD_repC1 classFormD_repC2 h4 C hC) P Φ D f m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂)
    (hm₀.trans_le (hmass f)) (by linarith) hR A B hAB

end QED.GradedProof.X1

end
