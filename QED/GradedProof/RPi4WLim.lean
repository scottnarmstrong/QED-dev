/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Setup

/-!
# (R-Π₄) step L1: the named class limits and the transverse projection

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L1. In the proof of
(G-Π₂) the `ε → 0⁺` limits of the seven classes of the order-`e⁴` vacuum polarization are
existential (`QED.GradedProof.VP2.HasVPLim`). Here they get names.

* `limT G`: the `ε → 0⁺` limit of a tensor family, `limUnder`; `limT_eq` characterizes it, and
  for a family with `HasVPLim T` it is the limit on the region (`tendsto_limT_of_hasVPLim`),
  reflection covariant (`tcov_limT`) and continuous along the null ray (`tendsto_limT_nullVec`).
  Any later explicit (parametric) formula for a class limit is identified with the named value by
  `limT_eq`.
* `wCl P Φ D C`: the limit tensor of the class `C` at the regulators of `P`; the limits of the
  seven classes `VA`, `VB`, `VC`, `F0`, `F1`, `G0`, `G1` (`tendsto_wCl_VA`, …), with
  `wCl … repG0 = polG (k²) (k² g - k k)` (`wCl_G0`, `wCl_G1`).
* `trProj k X`: the transverse projection `(s g_{μν} - 4 k_μ k_ν) X^{μν} / (3 s²)`, `s = k²`. It is
  linear and `trProj k (k² g - k k) = 1` for `k² ≠ 0` (`trProj_vpT`). On `A g + B k k` it returns
  `-B`: it reads off the `k k` coefficient, which carries no non-transverse constant.
* `piCl P Φ D C s`: the transverse projection of the class limit at `canonVec s`.
* `pol_eq_piCl` (**L1**): every form factor of the fixed-regulator order-`e⁴` vacuum polarization
  is `-e⁴ d₃(1) + i (π_VA + π_VB + π_VC + 2 polG + π_F0 + π_F1)` at each `s ≠ 0` of the region.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params Contraction)
open QED.Graded
open QED.GradedProof.VP2
open QED.GradedProof.SE2 (canonVec dot_canonVec nullVec dot_nullVec dot_smul_nullVec)

namespace QED.GradedProof.RPi4

/-! ### The limit of a tensor family -/

/-- **The `ε → 0⁺` limit of a tensor family** (Lean's `limUnder`; a junk value where there is no
limit). -/
noncomputable def limT (G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => G ε k μ ν

section LimT

variable {G : ℝ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem limT_eq {k : Fin 4 → ℝ} {μ ν : Fin 4} {L : ℂ}
    (h : Tendsto (fun ε => G ε k μ ν) (𝓝[>] 0) (𝓝 L)) : limT G k μ ν = L :=
  h.limUnder_eq

theorem tendsto_limT {k : Fin 4 → ℝ} {μ ν : Fin 4} {L : ℂ}
    (h : Tendsto (fun ε => G ε k μ ν) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε => G ε k μ ν) (𝓝[>] 0) (𝓝 (limT G k μ ν)) := by
  rwa [limT_eq h]

variable {T : ℝ}

theorem limT_eq_of_hasVPLim {W : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hW : ∀ k : Fin 4 → ℝ, -T ^ 2 < Minkowski.dot k k → ∀ μ ν : Fin 4,
      Tendsto (fun ε => G ε k μ ν) (𝓝[>] 0) (𝓝 (W k μ ν)))
    {k : Fin 4 → ℝ} (hk : -T ^ 2 < Minkowski.dot k k) : limT G k = W k :=
  funext fun μ => funext fun ν => limT_eq (hW k hk μ ν)

theorem tendsto_limT_of_hasVPLim (h : HasVPLim T G) {k : Fin 4 → ℝ}
    (hk : -T ^ 2 < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε => G ε k μ ν) (𝓝[>] 0) (𝓝 (limT G k μ ν)) := by
  obtain ⟨W, hW, -, -⟩ := h
  exact tendsto_limT (hW k hk μ ν)

/-- **The named limit is reflection covariant.** -/
theorem tcov_limT (h : HasVPLim T G) : TCov T (limT G) := by
  obtain ⟨W, hW, hc, -⟩ := h
  intro a ha k hk
  have hk' : -T ^ 2 < Minkowski.dot (QED.Dirac.reflect a k) (QED.Dirac.reflect a k) := by
    rw [QED.Dirac.dot_reflect ha]
    exact hk
  rw [limT_eq_of_hasVPLim hW hk', limT_eq_of_hasVPLim hW hk]
  exact hc a ha k hk

/-- **The named limit is continuous along the null ray.** -/
theorem tendsto_limT_nullVec (h : HasVPLim T G) (hT : -T ^ 2 < 0) (μ ν : Fin 4) :
    Tendsto (fun t : ℝ => limT G (t • nullVec) μ ν) (𝓝[>] 0) (𝓝 (limT G 0 μ ν)) := by
  obtain ⟨W, hW, -, hn⟩ := h
  have hreg : ∀ t : ℝ, -T ^ 2 < Minkowski.dot (t • nullVec) (t • nullVec) := fun t => by
    rw [dot_smul_nullVec]
    exact hT
  have h0 : -T ^ 2 < Minkowski.dot (0 : Fin 4 → ℝ) 0 := by
    simpa [Minkowski.dot_eq] using hT
  rw [limT_eq_of_hasVPLim hW h0]
  refine (hn μ ν).congr fun t => ?_
  rw [limT_eq_of_hasVPLim hW (hreg t)]

end LimT

/-! ### The transverse projection -/

/-- The weight `(s g_{μν} - 4 k_μ k_ν) / (3 s²)`, `s = k²`, of the transverse projection. -/
noncomputable def trWt (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ((Minkowski.dot k k * Minkowski.metric μ ν - 4 * Minkowski.lower k μ * Minkowski.lower k ν :
    ℝ) : ℂ) / (3 * ((Minkowski.dot k k : ℝ) : ℂ) ^ 2)

/-- **The transverse projection** `(s g_{μν} - 4 k_μ k_ν) X^{μν} / (3 s²)`: the coefficient `-B`
of `X = A g + B k k`. -/
noncomputable def trProj (k : Fin 4 → ℝ) (X : Fin 4 → Fin 4 → ℂ) : ℂ :=
  ∑ μ, ∑ ν, trWt k μ ν * X μ ν

theorem sum_trWt_real (k : Fin 4 → ℝ) :
    ∑ μ, ∑ ν, (Minkowski.dot k k * Minkowski.metric μ ν -
        4 * Minkowski.lower k μ * Minkowski.lower k ν) *
      (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) =
      3 * Minkowski.dot k k ^ 2 := by
  simp only [Fin.sum_univ_four, Minkowski.lower_eq, Minkowski.dot_eq]
  simp [Minkowski.metric]
  ring

/-- **The projection of the transverse tensor is `1`.** -/
theorem trProj_vpT {k : Fin 4 → ℝ} (hs : Minkowski.dot k k ≠ 0) : trProj k (vpT k) = 1 := by
  have h := congrArg (fun r : ℝ => (r : ℂ)) (sum_trWt_real k)
  simp only [ofReal_sum, ofReal_mul] at h
  have hs' : ((Minkowski.dot k k : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
  simp only [trProj, trWt, vpT, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [div_eq_one_iff_eq (mul_ne_zero three_ne_zero (pow_ne_zero 2 hs')), h]
  push_cast
  ring

theorem trProj_mul_vpT {k : Fin 4 → ℝ} (hs : Minkowski.dot k k ≠ 0) (c : ℂ) :
    trProj k (fun μ ν => c * vpT k μ ν) = c := by
  have h := trProj_vpT hs
  simp only [trProj] at h ⊢
  simp_rw [mul_left_comm _ c, ← Finset.mul_sum, h, mul_one]

/-- The projection of the seven-class combination of (G-Π₂). -/
theorem trProj_combo (k : Fin 4 → ℝ) (c : ℂ) (A B C G₀ G₁ F₀ F₁ : Fin 4 → Fin 4 → ℂ) :
    trProj k (fun μ ν => -c * vpT k μ ν +
        I * (A μ ν + B μ ν + C μ ν + G₀ μ ν + G₁ μ ν + F₀ μ ν + F₁ μ ν)) =
      -c * trProj k (vpT k) + I * (trProj k A + trProj k B + trProj k C + trProj k G₀ +
        trProj k G₁ + trProj k F₀ + trProj k F₁) := by
  simp only [trProj, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring

theorem neg_sq_two_mul (m₀ : ℝ) : -(2 * m₀) ^ 2 = -(4 * m₀ ^ 2) := by ring

/-! ### The named class limits -/

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- **The limit tensor of a class** at the regulators of `P`. -/
noncomputable def wCl {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 0 2 κ) :
    (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ :=
  limT fun ε k μ ν => val0 { P with ε := ε } Φ D k μ ν C

/-- **The transverse projection of a class limit** at `s`, a function of `s` and the
regulators. -/
noncomputable def piCl {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 0 2 κ) (s : ℝ) :
    ℂ :=
  trProj (canonVec s) (wCl P Φ D C (canonVec s))

section Classes

variable (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)

include hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ

theorem hasVPLim_VA :
    HasVPLim (2 * m₀) fun ε k μ ν => val0 { P with ε := ε } Φ D k μ ν repVA :=
  (vpj_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ).hasVPLim.congr fun k _ μ ν => by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [val0_repVA Φ D P hε.ne']

theorem hasVPLim_VB :
    HasVPLim (2 * m₀) fun ε k μ ν => val0 { P with ε := ε } Φ D k μ ν repVB :=
  (vpj_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ).hasVPLim.congr fun k _ μ ν => by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [val0_repVB Φ D P hε.ne']

theorem hasVPLim_VC :
    HasVPLim (2 * m₀) fun ε k μ ν => val0 { P with ε := ε } Φ D k μ ν repVC :=
  (vpj_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ).hasVPLim.congr fun k _ μ ν => by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [val0_repVC Φ D P hε.ne']

theorem tendsto_wCl_VA {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => val0 { P with ε := ε } Φ D k μ ν repVA) (𝓝[>] 0)
      (𝓝 (wCl P Φ D repVA k μ ν)) :=
  tendsto_limT_of_hasVPLim (hasVPLim_VA P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ)
    (by rwa [neg_sq_two_mul]) μ ν

theorem tendsto_wCl_VB {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => val0 { P with ε := ε } Φ D k μ ν repVB) (𝓝[>] 0)
      (𝓝 (wCl P Φ D repVB k μ ν)) :=
  tendsto_limT_of_hasVPLim (hasVPLim_VB P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ)
    (by rwa [neg_sq_two_mul]) μ ν

theorem tendsto_wCl_VC {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => val0 { P with ε := ε } Φ D k μ ν repVC) (𝓝[>] 0)
      (𝓝 (wCl P Φ D repVC k μ ν)) :=
  tendsto_limT_of_hasVPLim (hasVPLim_VC P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ)
    (by rwa [neg_sq_two_mul]) μ ν

omit hmγ hΛ in
theorem tendsto_wCl_F0 (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0)
    {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => val0 { P with ε := ε } Φ D k μ ν repF0) (𝓝[>] 0)
      (𝓝 (wCl P Φ D repF0 k μ ν)) :=
  tendsto_limT_of_hasVPLim (hasVPLim_repF0 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD)
    (by nlinarith) μ ν

omit hmγ hΛ in
theorem tendsto_wCl_F1 (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0)
    {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => val0 { P with ε := ε } Φ D k μ ν repF1) (𝓝[>] 0)
      (𝓝 (wCl P Φ D repF1 k μ ν)) :=
  tendsto_limT_of_hasVPLim (hasVPLim_repF1 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD)
    (by nlinarith) μ ν

omit hmγ hΛ in
theorem wCl_G0 (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) :
    wCl P Φ D repG0 k = fun μ ν => polG P Φ D rep (Minkowski.dot k k) * vpT k μ ν :=
  funext fun μ => funext fun ν =>
    limT_eq (tendsto_val0_repG0 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD hk μ ν)

omit hmγ hΛ in
theorem wCl_G1 (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) :
    wCl P Φ D repG1 k = fun μ ν => polG P Φ D rep (Minkowski.dot k k) * vpT k μ ν :=
  funext fun μ => funext fun ν =>
    limT_eq (tendsto_val0_repG1 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD hk μ ν)

/-- **The fixed-regulator vacuum polarization converges to the class limits.** -/
theorem tendsto_vacuumPolarizationPart_wCl
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν) (𝓝[>] 0)
      (𝓝 (-((P.e ^ 4 * D.d₃ 1 : ℝ) : ℂ) * vpT k μ ν +
        I * (wCl P Φ D repVA k μ ν + wCl P Φ D repVB k μ ν + wCl P Φ D repVC k μ ν +
          wCl P Φ D repG0 k μ ν + wCl P Φ D repG1 k μ ν + wCl P Φ D repF0 k μ ν +
          wCl P Φ D repF1 k μ ν))) := by
  have hD₁ : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 := fun f => (hD f).1
  have hD₂ : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 :=
    fun f => (hD f).2
  have hG0 := tendsto_val0_repG0 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD₁ hk μ ν
  have hG1 := tendsto_val0_repG1 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD₁ hk μ ν
  rw [← congrFun (congrFun (wCl_G0 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD₁ hk) μ) ν] at hG0
  rw [← congrFun (congrFun (wCl_G1 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD₁ hk) μ) ν] at hG1
  have hT := (tendsto_const_nhds (x := -((P.e ^ 4 * D.d₃ 1 : ℝ) : ℂ) * vpT k μ ν)).add
    ((((((((tendsto_wCl_VA P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ hk μ ν).add
      (tendsto_wCl_VB P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ hk μ ν)).add
      (tendsto_wCl_VC P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ hk μ ν)).add hG0).add hG1).add
      (tendsto_wCl_F0 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD₂ hk μ ν)).add
      (tendsto_wCl_F1 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD₂ hk μ ν)).const_mul I)
  refine hT.congr fun ε => ?_
  rw [vacuumPolarizationPart_two_eq]
  simp only [vpT]
  push_cast
  ring

/-- **(L1) The form factor is the projected class sum** at every `k` of the region with
`k² ≠ 0`. -/
theorem pol_eq_trProj
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {Pol : ℝ → ℂ} (hPol : IsPol P Φ D (4 * m₀ ^ 2) Pol) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (hs : Minkowski.dot k k ≠ 0) :
    Pol (Minkowski.dot k k) = -((P.e ^ 4 * D.d₃ 1 : ℝ) : ℂ) +
      I * (trProj k (wCl P Φ D repVA k) + trProj k (wCl P Φ D repVB k) +
        trProj k (wCl P Φ D repVC k) + 2 * polG P Φ D rep (Minkowski.dot k k) +
        trProj k (wCl P Φ D repF0 k) + trProj k (wCl P Φ D repF1 k)) := by
  have e : (fun μ ν => Pol (Minkowski.dot k k) * vpT k μ ν) = fun μ ν =>
      -((P.e ^ 4 * D.d₃ 1 : ℝ) : ℂ) * vpT k μ ν +
        I * (wCl P Φ D repVA k μ ν + wCl P Φ D repVB k μ ν + wCl P Φ D repVC k μ ν +
          wCl P Φ D repG0 k μ ν + wCl P Φ D repG1 k μ ν + wCl P Φ D repF0 k μ ν +
          wCl P Φ D repF1 k μ ν) :=
    funext fun μ => funext fun ν => tendsto_nhds_unique (hPol k hk μ ν)
      (tendsto_vacuumPolarizationPart_wCl P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ hD hk μ ν)
  have h := congrArg (trProj k) e
  rw [trProj_mul_vpT hs, trProj_combo, trProj_vpT hs,
    wCl_G0 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ (fun f => (hD f).1) hk,
    wCl_G1 P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ (fun f => (hD f).1) hk, trProj_mul_vpT hs] at h
  rw [h]
  ring

/-- **(L1) at the canonical vectors**: `Π(s) = -e⁴ d₃(1) + i (π_VA + π_VB + π_VC + 2 polG + π_F0
+ π_F1)(s)` for `s ≠ 0` in the region. -/
theorem pol_eq_piCl
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    {Pol : ℝ → ℂ} (hPol : IsPol P Φ D (4 * m₀ ^ 2) Pol) {s : ℝ} (hs : -(4 * m₀ ^ 2) < s)
    (hs0 : s ≠ 0) :
    Pol s = -((P.e ^ 4 * D.d₃ 1 : ℝ) : ℂ) +
      I * (piCl P Φ D repVA s + piCl P Φ D repVB s + piCl P Φ D repVC s +
        2 * polG P Φ D rep s + piCl P Φ D repF0 s + piCl P Φ D repF1 s) := by
  have h := pol_eq_trProj P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ hD hPol
    (k := canonVec s) (by rwa [dot_canonVec]) (by rwa [dot_canonVec])
  rw [dot_canonVec] at h
  exact h

end Classes

end QED.GradedProof.RPi4

end
