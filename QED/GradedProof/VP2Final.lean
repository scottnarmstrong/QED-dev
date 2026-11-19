/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VWardFin
public import QED.GradedProof.VP2FPol
public import QED.GradedProof.VP2LimG
public import QED.GradedProof.VP2Weights
public import QED.GradedProof.VP2Clause1V

/-!
# The order-`e⁴` vacuum polarization: existence and uniqueness of the form factor

Proves the frozen theorem goal (G-Π₂) `QED.Graded.vacuumPolarizationPart_two_existsUnique`
(decision D-57) as `QED.GradedProof.VP2.vacuumPolarizationPart_two_existsUnique'`.

* Clause 1 is `QED.GradedProof.VP2.vacuumPolarizationPart_two_clause1`.
* Clause 2: by `QED.GradedProof.VP2.vacuumPolarizationPart_two_eq` the vacuum polarization is
  `-e⁴ d₃(1) (k² g - k k) + i` times the sum of seven class values. The classes `VA + VB + VC`
  have a covariant limit with vanishing `k`-contraction (`hasVPLim_V`, `tendsto_wardV`), hence a
  transverse limit; so do `F0 + F1` (`exists_pol_F`); `G0`, `G1` tend to `polG (k²) (k² g - k k)`.
  Uniqueness: at `k = canonVec s` some component of `k² g - k k` is nonzero
  (`exists_vpT_canonVec_ne`).
-/

@[expose] public section

open Complex Filter Topology

namespace QED.GradedProof.VP2

open QED.Graded QED.GradedProof.SE2
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂)

theorem exists_vpT_canonVec_ne (s : ℝ) : ∃ μ ν : Fin 4, vpT (canonVec s) μ ν ≠ 0 := by
  by_cases hs : s = 0
  · refine ⟨0, 0, ?_⟩
    have h : canonVec s = nullVec := by simp [canonVec, hs]
    rw [h]
    simp only [vpT, dot_nullVec]
    simp [nullVec]
  · refine ⟨2, 2, ?_⟩
    have h2 : canonVec s 2 = 0 := by
      unfold canonVec
      split_ifs <;> rfl
    simp only [vpT, dot_canonVec, h2, mul_zero, sub_zero, ne_eq, Complex.ofReal_eq_zero]
    simpa [Minkowski.metric] using hs

/-- **(G-Π₂)**, with the binders of the frozen statement. -/
theorem vacuumPolarizationPart_two_existsUnique' (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0) :
    (∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = 4 →
      ∀ C : Contraction 0 2 κ, IsOnePI C → ∀ (k : Fin 4 → ℝ) (μ ν : Fin 4),
        QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude { P with ε := ε } Φ D C g ![] ![k, -k]
              (lineMomentum₂ C ![] ![] ![k, -k] ℓ) ![] ![] ![μ, ν]) ∧
    ∃! Pol : {s : ℝ // -(4 * m₀ ^ 2) < s} → ℂ,
      ∀ (k : Fin 4 → ℝ) (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
        Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν) (𝓝[>] 0)
          (𝓝 (Pol ⟨_, hk⟩ *
            ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))) := by
  refine ⟨vacuumPolarizationPart_two_clause1 P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD,
    ?_⟩
  obtain ⟨PV, hPV⟩ := (hasVPLim_V Φ D P rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ).exists_pol
    fun k hk ν => tendsto_wardV Φ D P rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ hk ν
  obtain ⟨PF, hPF⟩ := exists_pol_F P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂
    fun f => ⟨(hD f).2.1, (hD f).2.2⟩
  set c : ℂ := ((P.e ^ 4 * D.d₃ 1 : ℝ) : ℂ)
  let Pol : {s : ℝ // -(4 * m₀ ^ 2) < s} → ℂ := fun s =>
    -c + I * (PV s.1 + polG P Φ D rep s.1 + polG P Φ D rep s.1 + PF s.1)
  have hex : ∀ (k : Fin 4 → ℝ) (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
      Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν) (𝓝[>] 0)
        (𝓝 (Pol ⟨_, hk⟩ * vpT k μ ν)) := fun k hk μ ν => by
    have h2 : -(2 * m₀) ^ 2 < Minkowski.dot k k := by nlinarith
    have hF : -(m₀ + m₀) ^ 2 < Minkowski.dot k k := by nlinarith
    have hG0 := tendsto_val0_repG0 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (fun f => (hD f).1)
      hk μ ν
    have hG1 := tendsto_val0_repG1 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (fun f => (hD f).1)
      hk μ ν
    have hT := (tendsto_const_nhds (x := -(c * vpT k μ ν))).add
      (((((hPV k h2 μ ν).add hG0).add hG1).add (hPF k hF μ ν)).const_mul I)
    refine (hT.congr fun ε => ?_).trans (le_of_eq ?_)
    · rw [vacuumPolarizationPart_two_eq]
      simp only [c, vpT]
      push_cast
      ring
    · congr 1
      simp only [Pol]
      ring
  refine ⟨Pol, hex, fun Q hQ => funext fun s => ?_⟩
  obtain ⟨s, hs⟩ := s
  have hk : -(4 * m₀ ^ 2) < Minkowski.dot (canonVec s) (canonVec s) := by
    rwa [dot_canonVec]
  obtain ⟨μ, ν, hv⟩ := exists_vpT_canonVec_ne s
  have e := tendsto_nhds_unique (hQ _ hk μ ν) (hex _ hk μ ν)
  have hsub : (⟨_, hk⟩ : {s : ℝ // -(4 * m₀ ^ 2) < s}) = ⟨s, hs⟩ := Subtype.ext (dot_canonVec s)
  rw [hsub] at e
  exact mul_right_cancel₀ hv e

end QED.GradedProof.VP2

end
