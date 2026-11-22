/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2RealFinal
public import QED.GradedProof.RPi4Setup

/-!
# The fixed-regulator form factor of `Π⁽⁴⁾` is real

Helper level for `QED.ChainProof.SetAPauli.SetANestedAt`. `QED.GradedProof.VP2Real.vpReal`
shows that the transverse form factor of the order-`e⁴` vacuum polarization is real at `s = 0`.
The same argument works at every `s > -4m₀²`: by
`QED.GradedProof.VP2.vacuumPolarizationPart_two_eq` the vacuum polarization is a real tree term
plus `i` times seven class values, each with a purely imaginary limit (`hasConjLim_VA`, …,
`conj_polG`), so its limit at `k = canonVec s` is real, and some entry of `k² g - k k` is a
nonzero real number there (`QED.GradedProof.VP2.exists_vpT_canonVec_ne`).

* **`pol_im_eq_zero`**: under the hypotheses of the sealed (G-Π₂), every form factor with the
  transverse limit property on `s > -4m₀²` (`QED.GradedProof.RPi4.IsPol`) is real there.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.ChainProof.SetANestedAt

open QED.Graded QED.GradedProof.SE2 QED.GradedProof.VP2 QED.GradedProof.VP2Real
open QED.WickModel (Params)

/-- **The fixed-regulator form factor of `Π⁽⁴⁾` is real** on `s > -4m₀²`. -/
theorem pol_im_eq_zero (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {Pol : ℝ → ℂ} (hPol : QED.GradedProof.RPi4.IsPol P Φ D (4 * m₀ ^ 2) Pol) {s : ℝ}
    (hs : -(4 * m₀ ^ 2) < s) : (Pol s).im = 0 := by
  set k := canonVec s
  have hk : -(4 * m₀ ^ 2) < Minkowski.dot k k := by rw [dot_canonVec]; exact hs
  obtain ⟨μ, ν, hv⟩ := exists_vpT_canonVec_ne s
  have hL := hPol k hk μ ν
  have h2 : -(2 * m₀) ^ 2 < Minkowski.dot k k := by nlinarith
  have hF : -(m₀ + m₀) ^ 2 < Minkowski.dot k k := by nlinarith
  have hD' : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 := fun f =>
    ⟨(hD f).2.1, (hD f).2.2⟩
  obtain ⟨wA, hA, cA⟩ := hasConjLim_VA Φ D P rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ k h2 μ ν
  obtain ⟨wB, hB, cB⟩ := hasConjLim_VB Φ D P rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ k h2 μ ν
  obtain ⟨wC, hC, cC⟩ := hasConjLim_VC Φ D P rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ k h2 μ ν
  obtain ⟨w0, hF0, c0⟩ := hasConjLim_F0 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD' k hF μ ν
  obtain ⟨w1, hF1, c1⟩ := hasConjLim_F1 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD' k hF μ ν
  have hG0 := tendsto_val0_repG0 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (fun f => (hD f).1) hk μ ν
  have hG1 := tendsto_val0_repG1 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (fun f => (hD f).1) hk μ ν
  set g := polG P Φ D rep (Minkowski.dot k k) * vpT k μ ν
  set r : ℝ := P.e ^ 4 * D.d₃ 1 * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν)
  have hT := (tendsto_const_nhds (x := -(r : ℂ))).add
    ((((((((hA.add hB).add hC).add hG0).add hG1).add hF0).add hF1)).const_mul I)
  have hT' : Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν)
      (𝓝[>] 0) (𝓝 (-(r : ℂ) + I * (wA + wB + wC + g + g + w0 + w1))) :=
    hT.congr fun ε => by rw [vacuumPolarizationPart_two_eq]
  have he := tendsto_nhds_unique hL hT'
  change _ * vpT k μ ν = _ at he
  have hvr : starRingEnd ℂ (vpT k μ ν) = vpT k μ ν := by simp only [vpT, Complex.conj_ofReal]
  have hg : starRingEnd ℂ g = -g := by
    simp only [g, map_mul, conj_polG, hvr, neg_mul]
  have hc : starRingEnd ℂ (Pol (Minkowski.dot k k) * vpT k μ ν) =
      Pol (Minkowski.dot k k) * vpT k μ ν := by
    rw [he]
    simp only [map_add, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, cA, cB, cC, c0,
      c1, hg]
    ring
  rw [map_mul, hvr] at hc
  have hc' := mul_right_cancel₀ hv hc
  rw [dot_canonVec] at hc'
  exact Complex.conj_eq_iff_im.mp hc'
