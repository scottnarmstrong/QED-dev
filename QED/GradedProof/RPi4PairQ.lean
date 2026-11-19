/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4Pair
public import QED.GradedProof.RPi4PairF
public import QED.GradedProof.RPi4Null

/-!
# (R-Π₄) step L6: the projected class sum at a photon pair, and its additivity

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6. The class sum
`Q(s)` of `pol_eq_qSum_sub` depends on the photon masses only through the photon pair `(m_γ, Λ)`
of the two-loop classes and through the on-shell mass insertions. Here it is written as a function
`qPair … a b s` of an arbitrary photon pair `(a, b)`, which is **additive**:
`Q(a, d) = Q(a, b) + Q(b, d)`. So the regulator limits `Λ → ∞`, `m_γ → 0` become tail bounds
on `Q(a, b)` for a heavy (respectively light) pair, with no derivative in `Λ²`.

* `projS X s`: `trProj` at `canonVec s` for `s ≠ 0` and `nProj` at `n₀` for `s = 0`; the
  projected class limit `piClN` of `RPi4Null` is `projS (wCl …)`.
* `qPair Φ rep e a b s = i (projS W_VA(a, b) + projS W_VB(a, b) + projS W_VC(a, b) +
  projS fLim[δ(a, b)])(s)`, `δ(a, b)_g = ctPair e M_g a b`.
* `qSum_eq_qPair`: for counterterms renormalized through order `e⁴`, `Q(s) = qPair … m_γ Λ s`;
  hence `pol_eq_qPair_sub`: `Π(s) = qPair … m_γ Λ s - qPair … m_γ Λ 0`.
* `qPair_add`: `qPair … a d s = qPair … a b s + qPair … b d s` on the region.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2
open QED.GradedProof.SE2 (canonVec dot_canonVec nullVec dot_nullVec)

namespace QED.GradedProof.RPi4

/-! ### The projection at `s` -/

/-- **The projection at `s`**: `trProj` at `canonVec s` for `s ≠ 0`, `nProj` at `n₀` for
`s = 0`. -/
noncomputable def projS (X : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (s : ℝ) : ℂ :=
  if s = 0 then nProj (X nullVec) else trProj (canonVec s) (X (canonVec s))

theorem piClN_eq_projS (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : QED.WickModel.Contraction 0 2 κ) (s : ℝ) : piClN P Φ D C s = projS (wCl P Φ D C) s :=
  rfl

theorem trProj_add (k : Fin 4 → ℝ) (X Y : Fin 4 → Fin 4 → ℂ) :
    trProj k (fun μ ν => X μ ν + Y μ ν) = trProj k X + trProj k Y := by
  simp only [trProj, mul_add, Finset.sum_add_distrib]

/-- **The projection is additive** on tensors that add on the region `k² > -T`. -/
theorem projS_add {X Y Z : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ} {T : ℝ} (hT : 0 < T)
    (h : ∀ k : Fin 4 → ℝ, -T < Minkowski.dot k k → ∀ μ ν, X k μ ν = Y k μ ν + Z k μ ν)
    {s : ℝ} (hs : -T < s) : projS X s = projS Y s + projS Z s := by
  unfold projS
  split_ifs with h0
  · have e := h nullVec (by rw [dot_nullVec]; linarith)
    simp only [nProj, e 0 1]
    ring
  · have e := h (canonVec s) (by rwa [dot_canonVec])
    rw [show X (canonVec s) = fun μ ν => Y (canonVec s) μ ν + Z (canonVec s) μ ν from
      funext fun μ => funext fun ν => e μ ν, trProj_add]

/-! ### The class sum at a photon pair -/

section QPair

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)

omit [DecidableEq F] in
theorem fLim_congr (e : ℝ) {δ δ' : F → ℝ} (h : ∀ f, δ (rep f) = δ' (rep f)) :
    fLim Φ rep e δ = fLim Φ rep e δ' := by
  simp only [fLim, dBlockD, h]

/-- **The projected class sum at the photon pair `(a, b)`.** -/
noncomputable def qPair (e a b s : ℝ) : ℂ :=
  I * (projS (wV Φ e aVA baseVA cVA a b) s + projS (wV Φ e aVB baseVB cVB a b) s +
    projS (wV Φ e aVC baseVC cVC a b) s +
    projS (fLim Φ rep e fun g => ctPair e (Φ.mass g) a b) s)

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The class sum is additive in the photon pair**: `Q(a, d) = Q(a, b) + Q(b, d)` on the
region. -/
theorem qPair_add (P : Params) (he : P.e ≠ 0) {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) {s : ℝ} (hs : -(4 * m₀ ^ 2) < s) :
    qPair Φ rep P.e a d s = qPair Φ rep P.e a b s + qPair Φ rep P.e b d s := by
  have hT : 0 < 4 * m₀ ^ 2 := by positivity
  have hV := fun A base c (hX : ∀ k : Fin 4 → ℝ, -(4 * m₀ ^ 2) < Minkowski.dot k k →
      ∀ μ ν, wV Φ P.e A base c a d k μ ν =
        wV Φ P.e A base c a b k μ ν + wV Φ P.e A base c b d k μ ν) => projS_add hT hX hs
  have hA := hV aVA baseVA cVA fun k hk μ ν =>
    wV_VA_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hd hk μ ν
  have hB := hV aVB baseVB cVB fun k hk μ ν =>
    wV_VB_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hd hk μ ν
  have hC := hV aVC baseVC cVC fun k hk μ ν =>
    wV_VC_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e ha hb hd hk μ ν
  have hδ : (fun g => ctPair P.e (Φ.mass g) a d) =
      (fun g => ctPair P.e (Φ.mass g) a b) + fun g => ctPair P.e (Φ.mass g) b d :=
    funext fun g => ctPair_add P.e (hm₀.trans_le (hmass g)).ne' ha hb hd
  have hF := projS_add (X := fLim Φ rep P.e fun g => ctPair P.e (Φ.mass g) a d)
    (Y := fLim Φ rep P.e fun g => ctPair P.e (Φ.mass g) a b)
    (Z := fLim Φ rep P.e fun g => ctPair P.e (Φ.mass g) b d) hT (fun k hk μ ν => by
    rw [hδ]
    exact fLim_add Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he _ _ hk μ ν) hs
  simp only [qPair, hA, hB, hC, hF]
  ring

/-- **The class sum of renormalized counterterms is the class sum at the photon pair of the
model.** -/
theorem qSum_eq_qPair (P : Params) (D : Counterterms F) (he : P.e ≠ 0) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hR : IsRenormalizedThrough P Φ D rep 2) {s : ℝ}
    (hs : -(4 * m₀ ^ 2) < s) : qSum P Φ D s = qPair Φ rep P.e P.mγ P.Λ s := by
  have hT : 0 < 4 * m₀ ^ 2 := by positivity
  have hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 :=
    fun f => (hD_of_renormalized P Φ D hR f).2
  have hw : ∀ f, P.e ^ 2 * (D.dm (rep f) 0 - D.d₂ (rep f) 0) =
      ctPair P.e (Φ.mass (rep f)) P.mγ P.Λ := fun f =>
    sq_mul_dm_sub_d₂_eq_ctPair (hm₀.trans_le (hmass _)) hmγ hΛ
      ((hR.2 1 le_rfl (by norm_num)).1 (rep f) (hrep f)).1
  have hF := projS_add (X := fLim Φ rep P.e fun g => P.e ^ 2 * (D.dm g 0 - D.d₂ g 0)) hT
    (fun k hk μ ν => (wCl_F_eq_fLim Φ rep hm₀ hmass hrep hPV₁ hPV₂ P he D hD hk μ ν).symm) hs
  rw [fLim_congr Φ rep P.e (δ' := fun g => ctPair P.e (Φ.mass g) P.mγ P.Λ) hw] at hF
  simp only [qSum, qPair, piClN_eq_projS, wCl_VA_eq, wCl_VB_eq, wCl_VC_eq, hF]
  ring

/-- **(R-Π₄) the subtracted form factor at the photon pair of the model**:
`Π(s) = Q(m_γ, Λ; s) - Q(m_γ, Λ; 0)` on the region. -/
theorem pol_eq_qPair_sub (P : Params) (D : Counterterms F) (he : P.e ≠ 0) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hR : IsRenormalizedThrough P Φ D rep 2) {Pol : ℝ → ℂ}
    (hPol : IsPol P Φ D (4 * m₀ ^ 2) Pol) {s : ℝ} (hs : -(4 * m₀ ^ 2) < s) :
    Pol s = qPair Φ rep P.e P.mγ P.Λ s - qPair Φ rep P.e P.mγ P.Λ 0 := by
  rw [pol_eq_qSum_sub P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ he hmγ hΛ hR hPol hs,
    qSum_eq_qPair Φ rep hm₀ hmass hrep hPV₁ hPV₂ P D he hmγ hΛ hR hs,
    qSum_eq_qPair Φ rep hm₀ hmass hrep hPV₁ hPV₂ P D he hmγ hΛ hR (by nlinarith)]

end QPair

end QED.GradedProof.RPi4

end
