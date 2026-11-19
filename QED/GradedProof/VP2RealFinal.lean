/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2RealV
public import QED.GradedProof.VP2RealF
public import QED.GradedProof.VP2Final
public import QED.GradedProof.GEx2Inputs

/-!
# The input `VPReal` of (G-ex₂)

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57). Under the hypotheses of the sealed (G-Π₂)
`QED.GradedProof.VP2.vacuumPolarizationPart_two_existsUnique'`, the transverse form factor of the
order-`e⁴` vacuum polarization is real at `s = 0` (`QED.GradedProof.GEx2.VPReal`).

By `QED.GradedProof.VP2.vacuumPolarizationPart_two_eq` the vacuum polarization is a real tree term
plus `i` times the sum of the seven class values. Each class value has a purely imaginary limit:
`VA`, `VB`, `VC` (`hasConjLim_VA`, …), `F0`, `F1` (`hasConjLim_F0`, `hasConjLim_F1`), and `G0`,
`G1`, whose limit coefficient `polG` is imaginary (`conj_polG`). So the limit at the lightlike
`k = n₀ = (1, 1, 0, 0)` is real; there the `(0, 0)` entry of `k² g - k k` is `-1`, and the value
of the form factor at `0` is minus that real limit (`vpReal`).
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.VP2Real

open QED.Graded QED.GradedProof.SE2 QED.GradedProof.VP2
open QED.WickModel (Params)

/-- The limit coefficient of the classes `G0`, `G1` is purely imaginary. -/
theorem conj_polG (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (s : ℝ) :
    starRingEnd ℂ (polG P Φ D rep s) = -polG P Φ D rep s := by
  simp only [polG, polBlock, map_sum, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem vpT_nullVec : vpT nullVec 0 0 = -1 := by
  rw [vpT, dot_nullVec]
  simp [nullVec]

/-- **`VPReal` under the hypotheses of (G-Π₂).** -/
theorem vpReal (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (rep : F → F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0) :
    GEx2.VPReal P Φ D m₀ := by
  intro Pol hPol h0
  have hk : -(4 * m₀ ^ 2) < Minkowski.dot nullVec nullVec := by rw [dot_nullVec]; exact h0
  have hsub : (⟨Minkowski.dot nullVec nullVec, hk⟩ : {s : ℝ // -(4 * m₀ ^ 2) < s}) =
      ⟨0, h0⟩ := Subtype.ext dot_nullVec
  have hL := hPol nullVec hk 0 0
  rw [hsub] at hL
  have h2 : -(2 * m₀) ^ 2 < Minkowski.dot nullVec nullVec := by rw [dot_nullVec]; nlinarith
  have hF : -(m₀ + m₀) ^ 2 < Minkowski.dot nullVec nullVec := by rw [dot_nullVec]; nlinarith
  have hD' : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 := fun f =>
    ⟨(hD f).2.1, (hD f).2.2⟩
  obtain ⟨wA, hA, cA⟩ :=
    hasConjLim_VA Φ D P rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ nullVec h2 0 0
  obtain ⟨wB, hB, cB⟩ :=
    hasConjLim_VB Φ D P rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ nullVec h2 0 0
  obtain ⟨wC, hC, cC⟩ :=
    hasConjLim_VC Φ D P rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ nullVec h2 0 0
  obtain ⟨w0, hF0, c0⟩ :=
    hasConjLim_F0 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD' nullVec hF 0 0
  obtain ⟨w1, hF1, c1⟩ :=
    hasConjLim_F1 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD' nullVec hF 0 0
  have hG0 := tendsto_val0_repG0 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (fun f => (hD f).1) hk 0 0
  have hG1 := tendsto_val0_repG1 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (fun f => (hD f).1) hk 0 0
  set g := polG P Φ D rep (Minkowski.dot nullVec nullVec) * vpT nullVec 0 0
  set r : ℝ := P.e ^ 4 * D.d₃ 1 * (Minkowski.dot nullVec nullVec * Minkowski.metric 0 0 -
    nullVec 0 * nullVec 0)
  have hT := (tendsto_const_nhds (x := -(r : ℂ))).add
    ((((((((hA.add hB).add hC).add hG0).add hG1).add hF0).add hF1)).const_mul I)
  have hT' : Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 nullVec 0 0)
      (𝓝[>] 0) (𝓝 (-(r : ℂ) + I * (wA + wB + wC + g + g + w0 + w1))) :=
    hT.congr fun ε => by rw [vacuumPolarizationPart_two_eq]
  have he := tendsto_nhds_unique hL hT'
  change _ * vpT nullVec 0 0 = _ at he
  rw [vpT_nullVec] at he
  have hg : starRingEnd ℂ g = -g := by
    simp only [g, map_mul, conj_polG, vpT, Complex.conj_ofReal, neg_mul]
  have hval : Pol ⟨0, h0⟩ = (r : ℂ) - I * (wA + wB + wC + g + g + w0 + w1) := by
    linear_combination -he
  have hc : starRingEnd ℂ (Pol ⟨0, h0⟩) = Pol ⟨0, h0⟩ := by
    rw [hval]
    simp only [map_sub, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, cA, cB, cC, c0,
      c1, hg]
    ring
  exact Complex.conj_eq_iff_im.mp hc

end QED.GradedProof.VP2Real

end
