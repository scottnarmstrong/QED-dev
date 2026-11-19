/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4WWard

/-!
# (R-Π₄): the subtraction at `s = 0`, the photon counterterm drops out

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57).

By `QED.GradedProof.RPi4.pol_eq_piCl_ctδ` the form factor is
`Π(s) = -e⁴ d₃(1) + i (π_VA + π_VB + π_VC + π_F0[ctδ] + π_F1[ctδ])(s)` at `s ≠ 0`. The projection
`trProj` divides by `s²`, so it cannot be used at `s = 0`. There the coefficient of `k k` is read
off at the null vector `n₀ = (1, 1, 0, 0)` from the entry `(0, 1)`, where `g` vanishes:
`nProj X = -X⁰¹`, which is `-B` on `A g + B n₀ n₀`, like `trProj`.

* `tensor_eq_ctδ`: the tensor identity behind `pol_eq_piCl_ctδ`, at every `k` of the region
  (including null `k`).
* `piClN P Φ D C s`: the projected class limit, `trProj` at `s ≠ 0` and `nProj` at the null
  vector for `s = 0`.
* `qSum`: `i (π_VA + π_VB + π_VC + π_F0[ctδ] + π_F1[ctδ])`.
* `e4d₃_eq_qSum_zero`: `e⁴ d₃(1) = Q(0) - Π(0)`; with the photon condition `Π(0) = 0`.
* `pol_eq_qSum_sub` (**the subtraction**): `Π(s) = Q(s) - Q(0)` on the whole region, for
  counterterms renormalized through order `e⁴`; `d₃(1)` no longer appears.

No continuity in `s` is used: `Q(0)` is the null-vector readout of the same class limits, and any
later explicit (parametric) form of the class limits valid on the whole region evaluates both
`Q(s)` and `Q(0)`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2
open QED.GradedProof.SE2 (canonVec dot_canonVec nullVec dot_nullVec)

namespace QED.GradedProof.RPi4

/-- **The null-vector readout** `-X⁰¹`: the coefficient `-B` of `X = A g + B n₀ n₀`. -/
def nProj (X : Fin 4 → Fin 4 → ℂ) : ℂ := -X 0 1

theorem vpT_nullVec_zero_one : vpT nullVec 0 1 = -1 := by
  simp [vpT, nullVec, Minkowski.metric]

theorem nProj_mul_vpT (c : ℂ) : nProj (fun μ ν => c * vpT nullVec μ ν) = c := by
  simp [nProj, vpT_nullVec_zero_one]

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- **The projected class limit** at `s`: `trProj` at `canonVec s` for `s ≠ 0`, and the null
readout `nProj` at `n₀` for `s = 0`. -/
noncomputable def piClN {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : QED.WickModel.Contraction 0 2 κ)
    (s : ℝ) : ℂ :=
  if s = 0 then nProj (wCl P Φ D C nullVec) else piCl P Φ D C s

theorem piClN_of_ne {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : QED.WickModel.Contraction 0 2 κ)
    {s : ℝ} (hs : s ≠ 0) : piClN P Φ D C s = piCl P Φ D C s := by
  simp [piClN, hs]

theorem piClN_zero {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : QED.WickModel.Contraction 0 2 κ) :
    piClN P Φ D C 0 = nProj (wCl P Φ D C nullVec) := by
  simp [piClN]

/-- **The class sum** `Q(s) = i (π_VA + π_VB + π_VC + π_F0[ctδ] + π_F1[ctδ])(s)`. -/
noncomputable def qSum (s : ℝ) : ℂ :=
  I * (piClN P Φ D repVA s + piClN P Φ D repVB s + piClN P Φ D repVC s +
    piClN P Φ (ctδ D) repF0 s + piClN P Φ (ctδ D) repF1 s)

section Tensor

variable (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
    D.dm f 0 = D.dm (rep f) 0)
  (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hd : ∀ f, D.d₁ f 0 = D.d₂ f 0)

include hm₀ hmass hrep hPV₁ hPV₂ hD hmγ hΛ hd

/-- **(L1 + L2) The tensor identity** at every `k` of the region:
`Π(k²) (k² g - k k) = -e⁴ d₃(1) (k² g - k k) + i (W_VA + W_VB + W_VC + W_F0[ctδ] + W_F1[ctδ])`. -/
theorem tensor_eq_ctδ {Pol : ℝ → ℂ} (hPol : IsPol P Φ D (4 * m₀ ^ 2) Pol) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) :
    (fun μ ν => Pol (Minkowski.dot k k) * vpT k μ ν) = fun μ ν =>
      -((P.e ^ 4 * D.d₃ 1 : ℝ) : ℂ) * vpT k μ ν +
        I * (wCl P Φ D repVA k μ ν + wCl P Φ D repVB k μ ν + wCl P Φ D repVC k μ ν +
          wCl P Φ (ctδ D) repF0 k μ ν + wCl P Φ (ctδ D) repF1 k μ ν) := by
  have hD' : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 := fun f => (hD f).2
  have hFδ0 := tendsto_wCl_F0 P Φ (ctδ D) rep hm₀ hmass hrep hPV₁ hPV₂ (hD_ctδ D rep hD') hk
  have hFδ1 := tendsto_wCl_F1 P Φ (ctδ D) rep hm₀ hmass hrep hPV₁ hPV₂ (hD_ctδ D rep hD') hk
  funext μ ν
  refine tendsto_nhds_unique (hPol k hk μ ν) ?_
  have hT := (tendsto_const_nhds (x := -((P.e ^ 4 * D.d₃ 1 : ℝ) : ℂ) * vpT k μ ν)).add
    (((((((tendsto_wCl_VA P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ hk μ ν).add
      (tendsto_wCl_VB P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ hk μ ν)).add
      (tendsto_wCl_VC P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hmγ hΛ hk μ ν)).add
      (tendsto_gauge_add_d₂ P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD hd hk μ ν)).add
      (hFδ0 μ ν)).add (hFδ1 μ ν)).const_mul I)
  refine (hT.congr' ?_).trans (le_of_eq (by ring_nf))
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [vacuumPolarizationPart_two_eq,
    val0_F0_split P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD hε k μ ν,
    val0_F1_split P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD hε k μ ν]
  simp only [vpT]
  push_cast
  ring

/-- **The photon counterterm is the null readout of the class sum**:
`e⁴ d₃(1) = Q(0) - Π(0)`. -/
theorem e4d₃_eq_qSum_zero {Pol : ℝ → ℂ} (hPol : IsPol P Φ D (4 * m₀ ^ 2) Pol) :
    ((P.e ^ 4 * D.d₃ 1 : ℝ) : ℂ) = qSum P Φ D 0 - Pol 0 := by
  have hk : -(4 * m₀ ^ 2) < Minkowski.dot nullVec nullVec := by
    rw [dot_nullVec]; nlinarith
  have h := congrArg nProj
    (tensor_eq_ctδ P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD hmγ hΛ hd hPol hk)
  rw [nProj_mul_vpT, dot_nullVec] at h
  simp only [nProj, vpT_nullVec_zero_one] at h
  simp only [qSum, piClN_zero, nProj]
  linear_combination h

/-- **The subtraction at `s = 0`**: `Π(s) = Q(s) - Q(0) + Π(0)` at every `s` of the region. -/
theorem pol_eq_qSum_sub_add {Pol : ℝ → ℂ} (hPol : IsPol P Φ D (4 * m₀ ^ 2) Pol) {s : ℝ}
    (hs : -(4 * m₀ ^ 2) < s) : Pol s = qSum P Φ D s - qSum P Φ D 0 + Pol 0 := by
  have h0 := e4d₃_eq_qSum_zero P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD hmγ hΛ hd hPol
  rcases eq_or_ne s 0 with rfl | hs0
  · ring
  have h := pol_eq_piCl_ctδ P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hD hmγ hΛ hd hPol hs hs0
  rw [h0] at h
  rw [h]
  simp only [qSum, piClN_of_ne P Φ D _ hs0, piClN_of_ne P Φ (ctδ D) _ hs0]
  ring

end Tensor

/-- **(R-Π₄) the subtraction at `s = 0` for renormalized counterterms**: `Π(s) = Q(s) - Q(0)` on
the whole region `s > -4m₀²`. The photon counterterm `d₃(1)` is gone. -/
theorem pol_eq_qSum_sub (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (he : P.e ≠ 0) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hR : IsRenormalizedThrough P Φ D rep 2)
    {Pol : ℝ → ℂ} (hPol : IsPol P Φ D (4 * m₀ ^ 2) Pol) {s : ℝ} (hs : -(4 * m₀ ^ 2) < s) :
    Pol s = qSum P Φ D s - qSum P Φ D 0 := by
  have hd := d₁_eq_d₂_of_renormalized P Φ D (n := 2) (by norm_num) he
    (fun g => hm₀.trans_le (hmass g)) hmγ hΛ hrep hR
  have h := pol_eq_qSum_sub_add P Φ D rep hm₀ hmass hrep hPV₁ hPV₂
    (hD_of_renormalized P Φ D hR) hmγ hΛ hd hPol hs
  rw [h, pol_zero P Φ D (by positivity) hPol (hR.2 2 (by norm_num) le_rfl).2]
  ring

end QED.GradedProof.RPi4

end
