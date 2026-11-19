/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.GEx2Solve
public import QED.Frozen.Graded.SelfEnergyPartTwoExistsUnique
public import QED.Frozen.Graded.VacuumPolarizationPartTwoExistsUnique

/-!
# The analytic inputs of (G-ex₂)

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57). The order-`e⁴` conditions are affine equations with **real** unknowns
(`QED/GradedProof/GEx2Solve.lean`), so besides the limits supplied by the sealed (G-Σ₂) and (G-Π₂)
they need the reality of the on-shell data, and for the vertex the order-`e⁵` limit at `q = 0`:

* `SEReal`: for every pair of form factors with the limit property of (G₉) at order `4`, the
  on-shell value `Σ(-M_f)` and the derivative `Σ'(-M_f)` are real;
* `VPReal`: the transverse form factor of (G-Π₂) is real at `s = 0`;
* `VertexZeroInput`: the sandwiched order-`5` vertex at `q = 0` tends to `c · w γ^μ u` for one
  real `c`.

From (G-Σ₂) with `SEReal` and (G-Π₂) with `VPReal` this file derives the data that
`isOnShellAt_two_iff` and `isPhotonOnShellAt_two_iff` consume (`exists_seData`, `exists_vpData`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.GEx2

open QED.Graded
open QED.WickModel (Params)

/-- **Reality of the order-`4` on-shell data of flavour `f`.** -/
def SEReal (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (f : F) : Prop :=
  ∀ r > 0, ∀ A B : ℝ → ℂ, SELimit P Φ D f r A B →
    (A (-Φ.mass f ^ 2) * ((-Φ.mass f : ℝ) : ℂ) + B (-Φ.mass f ^ 2) * Φ.mass f).im = 0 ∧
      (deriv (shellFun A B (Φ.mass f)) (-Φ.mass f)).im = 0

/-- **Reality of the order-`4` transverse form factor at `s = 0`.** -/
def VPReal (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (m₀ : ℝ) : Prop :=
  ∀ Pol : {s : ℝ // -(4 * m₀ ^ 2) < s} → ℂ,
    (∀ (k : Fin 4 → ℝ) (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
      Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν) (𝓝[>] 0)
        (𝓝 (Pol ⟨_, hk⟩ *
          ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) →
    ∀ h0 : -(4 * m₀ ^ 2) < 0, (Pol ⟨0, h0⟩).im = 0

/-- **The order-`5` vertex at `q = 0`**: between on-shell flavour-`f` spinors it tends to
`c · w γ^μ u` for one real `c`. -/
def VertexZeroInput (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (f : F) : Prop :=
  ∃ c : ℝ, ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -Φ.mass f ^ 2 → 0 < p 0 → ∀ (μ : Fin 4)
    (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((Φ.mass f : ℂ) • u) →
    w ᵥ* Dirac.slash p = -((Φ.mass f : ℂ) • w) →
    Tendsto (fun ε : ℝ => w ⬝ᵥ (vertexPart { P with ε := ε } Φ D f 2 p p μ *ᵥ u)) (𝓝[>] 0)
      (𝓝 ((c : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))))

/-- The block Pauli–Villars conditions give the total ones. -/
theorem sum_eq_zero_of_blocks {F : Type} [Fintype F] [DecidableEq F] (rep : F → F)
    (hrep : ∀ f, rep (rep f) = rep f) (c : F → ℝ)
    (h : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), c f = 0) :
    ∑ f, c f = 0 := by
  rw [← Finset.sum_fiberwise Finset.univ rep c]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : rep b = b
  · exact h b hb
  · refine Finset.sum_eq_zero fun f hf => ?_
    have hf' := (Finset.mem_filter.1 hf).2
    exact absurd (by rw [← hf', hrep]) hb

/-- **The self-energy data**: from (G-Σ₂) and `SEReal`, form factors on a region with real
on-shell value and derivative. -/
theorem exists_seData (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0)
    (hR : SEReal P Φ D f) :
    ∃ r > 0, ∃ A B : ℝ → ℂ, SELimit P Φ D f r A B ∧ ∃ σ₀ σ₁ : ℝ,
      A (-Φ.mass f ^ 2) * ((-Φ.mass f : ℝ) : ℂ) + B (-Φ.mass f ^ 2) * Φ.mass f = σ₀ ∧
      HasDerivAt (shellFun A B (Φ.mass f)) σ₁ (-Φ.mass f) := by
  obtain ⟨-, ⟨AB, hAB, -⟩, hdiff⟩ :=
    selfEnergyPart_two_existsUnique P Φ D f m₀ hm₀ hmass hmγ hΛ hPV₁ hPV₂
  have hr : 0 < min (min P.mγ P.Λ) (2 * m₀) := lt_min (lt_min hmγ hΛ) (by linarith)
  set A : ℝ → ℂ := fun s =>
    if h : -(Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) ^ 2 < s then (AB ⟨s, h⟩).1 else 0
  set B : ℝ → ℂ := fun s =>
    if h : -(Φ.mass f + min (min P.mγ P.Λ) (2 * m₀)) ^ 2 < s then (AB ⟨s, h⟩).2 else 0
  have hlim : SELimit P Φ D f (min (min P.mγ P.Λ) (2 * m₀)) A B := by
    intro p hp α β
    simpa only [A, B, hp, dite_true] using hAB p hp α β
  have hd := (hdiff A B hlim).hasDerivAt
  obtain ⟨h0, h1⟩ := hR _ hr A B hlim
  set v := A (-Φ.mass f ^ 2) * ((-Φ.mass f : ℝ) : ℂ) + B (-Φ.mass f ^ 2) * Φ.mass f
  set d := deriv (shellFun A B (Φ.mass f)) (-Φ.mass f)
  refine ⟨_, hr, A, B, hlim, v.re, d.re,
    Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact h0), ?_⟩
  have hdre : ((d.re : ℝ) : ℂ) = d :=
    Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im]; exact h1.symm)
  rw [hdre]
  exact hd

/-- **The vacuum-polarization datum**: from (G-Π₂) and `VPReal`, the real limit coefficient at
lightlike `k`. -/
theorem exists_vpData (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    (hR : VPReal P Φ D m₀) :
    ∃ π₀ : ℝ, ∀ k : Fin 4 → ℝ, Minkowski.dot k k = 0 → ∀ μ ν : Fin 4,
      Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν) (𝓝[>] 0)
        (𝓝 ((π₀ * (k μ * k ν) : ℝ) : ℂ)) := by
  obtain ⟨-, ⟨Pol, hPol, -⟩⟩ :=
    vacuumPolarizationPart_two_existsUnique P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD
  have h0 : -(4 * m₀ ^ 2) < 0 := by nlinarith
  have hre := hR Pol hPol h0
  refine ⟨-(Pol ⟨0, h0⟩).re, fun k hk μ ν => ?_⟩
  have hk' : -(4 * m₀ ^ 2) < Minkowski.dot k k := hk ▸ h0
  have hsub : (⟨Minkowski.dot k k, hk'⟩ : {s : ℝ // -(4 * m₀ ^ 2) < s}) = ⟨0, h0⟩ :=
    Subtype.ext hk
  have h := hPol k hk' μ ν
  rw [hsub, hk] at h
  convert h using 2
  have hP : Pol ⟨0, h0⟩ = ((Pol ⟨0, h0⟩).re : ℂ) := Complex.ext (by simp) (by simp [hre])
  rw [hP]
  push_cast
  simp only [Complex.ofReal_re]
  ring

end QED.GradedProof.GEx2

end
