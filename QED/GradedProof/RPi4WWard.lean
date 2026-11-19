/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4WLim
public import QED.GradedProof.RPi4WRem

/-!
# (R-Π₄) step L2: the gauge classes cancel the `d₂` part of the insertions

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L2.

The level-`0` `fermionCt` vertex `d₂ y̸ + d_m M` splits as `d₂ (y̸ + M) + (d_m - d₂) M`. Accordingly
the counterterms split as `ctD₂ D` (`d_m := d₂`) and `ctδ D` (`d₂ := 0`, `d_m := d_m - d₂`), and
the values of the insertion classes `F0`, `F1` are additive in this split (`val0_F0_split`,
`val0_F1_split`). In the `d₂` part one propagator contracts: pointwise in the loop momentum,
`F_j(ctD₂ D) = -G_j(D) + iε remBlock` once `d₁ = d₂` (`fBubble_ctD₂_F0`, `fBubble_ctD₂_F1`). The
block-summed remainder converges (`QED.GradedProof.RPi4.vpf_remBlock`), so

* `tendsto_gauge_add_d₂`: `G0 + G1 + F0(ctD₂ D) + F1(ctD₂ D) → 0` as `ε → 0⁺` (**L2**);
* `pol_eq_piCl_ctδ`: the form factor is `-e⁴ d₃(1) + i (π_VA + π_VB + π_VC + π_F0 + π_F1)` with
  the insertion classes at the pure mass insertion `ctδ D`, `δ = e² (d_m - d₂)`.
-/

@[expose] public section

open Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded
open QED.GradedProof.VP2

namespace QED.GradedProof.RPi4

open QED.TwoLoop.Bridge (electronNumerator propDenom)
open QED.TwoLoop.Insertion (fermionCtMatrix)

local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-! ### The split of the insertion -/

/-- The projection of the five-class combination. -/
theorem trProj_combo5 (k : Fin 4 → ℝ) (c : ℂ) (A B C F₀ F₁ : Fin 4 → Fin 4 → ℂ) :
    trProj k (fun μ ν => -c * vpT k μ ν + I * (A μ ν + B μ ν + C μ ν + F₀ μ ν + F₁ μ ν)) =
      -c * trProj k (vpT k) + I * (trProj k A + trProj k B + trProj k C + trProj k F₀ +
        trProj k F₁) := by
  simp only [trProj, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring


theorem fermionCtMatrix_split (a b M : ℝ) (y : Fin 4 → ℝ) :
    fermionCtMatrix a b M y = fermionCtMatrix a a M y + fermionCtMatrix 0 (b - a) M y := by
  simp only [fermionCtMatrix, ofReal_zero, zero_smul, zero_add]
  rw [add_assoc, ← add_smul]
  congr 2
  push_cast
  ring

theorem insG_split (A B : Mat) (a b M ε : ℝ) (x y : Fin 4 → ℝ) :
    insG A B a b M ε x y = insG A B a a M ε x y + insG A B 0 (b - a) M ε x y := by
  simp only [insG, insTr]
  rw [fermionCtMatrix_split a b, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  ring

variable {F : Type}

/-- The counterterms of the `d₂` part of the insertion: `d_m := d₂`. -/
def ctD₂ (D : Counterterms F) : Counterterms F := { D with dm := D.d₂ }

/-- The counterterms of the pure mass insertion: `d₂ := 0`, `d_m := d_m - d₂`. -/
def ctδ (D : Counterterms F) : Counterterms F :=
  { D with d₂ := fun _ _ => 0, dm := fun f j => D.dm f j - D.d₂ f j }

variable [Fintype F] [DecidableEq F]

variable (P : Params) (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F)

omit [DecidableEq F] in
theorem fBubble_split (sw bx bY : Bool) (ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    fBubble P Φ D rep sw bx bY ε k q μ ν =
      fBubble P Φ (ctD₂ D) rep sw bx bY ε k q μ ν + fBubble P Φ (ctδ D) rep sw bx bY ε k q μ ν := by
  simp only [fBubble, ctD₂, ctδ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [insG_split _ _ (P.e ^ 2 * D.d₂ (rep f) 0) (P.e ^ 2 * D.dm (rep f) 0), mul_zero,
    ← mul_sub]
  ring

omit [Fintype F] [DecidableEq F] in
theorem hD_ctD₂ (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) :
    ∀ f, (ctD₂ D).d₂ f 0 = (ctD₂ D).d₂ (rep f) 0 ∧ (ctD₂ D).dm f 0 = (ctD₂ D).dm (rep f) 0 :=
  fun f => ⟨(hD f).1, (hD f).1⟩

omit [Fintype F] [DecidableEq F] in
theorem hD_ctδ (hD : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0) :
    ∀ f, (ctδ D).d₂ f 0 = (ctδ D).d₂ (rep f) 0 ∧ (ctδ D).dm f 0 = (ctδ D).dm (rep f) 0 :=
  fun f => ⟨rfl, by simp only [ctδ, (hD f).1, (hD f).2]⟩

/-! ### The contracted propagator -/

theorem kF_bubTr_F0 (e M ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    kF e * (bubTr (gAF true μ ν) (gBF true μ ν) M (zk k true q) (zk k false q) *
        (propDenom M ε (zk k true q))⁻¹ * (propDenom M ε (zk k false q))⁻¹) =
      -bubbleW e M ε k q μ ν := by
  rw [bubbleW_eq, kF_eq]
  simp only [wfB, bubTr, gAF, gBF, ite_true]
  ring

theorem kF_bubTr_F1 (e M ε : ℝ) (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    kF e * (bubTr (gAF false μ ν) (gBF false μ ν) M (zk k false q) (zk k true q) *
        (propDenom M ε (zk k false q))⁻¹ * (propDenom M ε (zk k true q))⁻¹) =
      -bubbleW e M ε k q μ ν := by
  rw [bubbleW_eq, kF_eq]
  simp only [wfB, bubTr, gAF, gBF, Bool.false_eq_true, ite_false]
  have h : (Dirac.gamma μ * electronNumerator M (zk k false q) * Dirac.gamma ν *
      electronNumerator M (zk k true q)).trace =
      (Dirac.gamma ν * electronNumerator M (zk k true q) * Dirac.gamma μ *
        electronNumerator M (zk k false q)).trace := by
    rw [Matrix.mul_assoc _ (Dirac.gamma ν), Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h]
  ring

/-- The coefficient `κ_F e² d₂` of the block remainder. -/
noncomputable def dR (r : F) : ℂ := kF P.e * ((P.e ^ 2 * D.d₂ r 0 : ℝ) : ℂ)

omit [DecidableEq F] in
/-- **The `d₂` part of `F0` is minus the gauge class up to `iε`.** -/
theorem fBubble_ctD₂_F0 (hd : ∀ f, D.d₁ f 0 = D.d₂ f 0) {ε : ℝ} (hε : ε ≠ 0)
    (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    fBubble P Φ (ctD₂ D) rep true true false ε k q μ ν =
      -gBubble { P with ε := ε } Φ D rep k q μ ν +
        (ε * I) * remBlock Φ rep (dR P D) true true false ε k q μ ν := by
  simp only [fBubble, gBubble, remBlock, ctD₂, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hT := kF_bubTr_F0 P.e (Φ.mass f) ε k q μ ν
  rw [insG_eq _ _ _ hε, sub_self, zero_mul, ofReal_zero, zero_mul, add_zero, hd (rep f)]
  simp only [remG, dR]
  linear_combination ((Φ.coeff f : ℂ) * ((P.e ^ 2 * D.d₂ (rep f) 0 : ℝ) : ℂ)) * hT

omit [DecidableEq F] in
/-- **The `d₂` part of `F1` is minus the gauge class up to `iε`.** -/
theorem fBubble_ctD₂_F1 (hd : ∀ f, D.d₁ f 0 = D.d₂ f 0) {ε : ℝ} (hε : ε ≠ 0)
    (k q : Fin 4 → ℝ) (μ ν : Fin 4) :
    fBubble P Φ (ctD₂ D) rep false false true ε k q μ ν =
      -gBubble { P with ε := ε } Φ D rep k q μ ν +
        (ε * I) * remBlock Φ rep (dR P D) false false true ε k q μ ν := by
  simp only [fBubble, gBubble, remBlock, ctD₂, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hT := kF_bubTr_F1 P.e (Φ.mass f) ε k q μ ν
  rw [insG_eq _ _ _ hε, sub_self, zero_mul, ofReal_zero, zero_mul, add_zero, hd (rep f)]
  simp only [remG, dR]
  linear_combination ((Φ.coeff f : ℂ) * ((P.e ^ 2 * D.d₂ (rep f) 0 : ℝ) : ℂ)) * hT

/-! ### The limit -/

section Limit

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
    D.dm f 0 = D.dm (rep f) 0)

include hm₀ hmass hrep hPV₁ hPV₂ hD

/-- **The values of `F0` are additive in the split of the insertion.** -/
theorem val0_F0_split {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    val0 { P with ε := ε } Φ D k μ ν repF0 =
      val0 { P with ε := ε } Φ (ctD₂ D) k μ ν repF0 +
        val0 { P with ε := ε } Φ (ctδ D) k μ ν repF0 := by
  have hD' : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 := fun f => (hD f).2
  rw [val0_repF0 _ Φ D rep hD', val0_repF0 _ Φ (ctD₂ D) rep (hD_ctD₂ D rep hD'),
    val0_repF0 _ Φ (ctδ D) rep (hD_ctδ D rep hD')]
  exact (congrArg _ (funext fun q => fBubble_split P Φ D rep true true false ε k q μ ν)).trans
    (efi_add
      ((vpf_fBubble P Φ (ctD₂ D) rep m₀ hm₀ hmass hrep hPV₁ hPV₂ true true false).2 ε hε k μ ν)
      ((vpf_fBubble P Φ (ctδ D) rep m₀ hm₀ hmass hrep hPV₁ hPV₂ true true false).2 ε hε k μ ν))

/-- **The values of `F1` are additive in the split of the insertion.** -/
theorem val0_F1_split {ε : ℝ} (hε : 0 < ε) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    val0 { P with ε := ε } Φ D k μ ν repF1 =
      val0 { P with ε := ε } Φ (ctD₂ D) k μ ν repF1 +
        val0 { P with ε := ε } Φ (ctδ D) k μ ν repF1 := by
  have hD' : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 := fun f => (hD f).2
  rw [val0_repF1 _ Φ D rep hD', val0_repF1 _ Φ (ctD₂ D) rep (hD_ctD₂ D rep hD'),
    val0_repF1 _ Φ (ctδ D) rep (hD_ctδ D rep hD')]
  exact (congrArg _ (funext fun q => fBubble_split P Φ D rep false false true ε k q μ ν)).trans
    (efi_add
      ((vpf_fBubble P Φ (ctD₂ D) rep m₀ hm₀ hmass hrep hPV₁ hPV₂ false false true).2 ε hε k μ ν)
      ((vpf_fBubble P Φ (ctδ D) rep m₀ hm₀ hmass hrep hPV₁ hPV₂ false false true).2 ε hε k μ ν))

omit hD in
/-- `G_j + F_j(ctD₂ D) = iε ∫ remBlock` at `ε > 0`. -/
theorem val0_G_add_F_eq (hd : ∀ f, D.d₁ f 0 = D.d₂ f 0) {ε : ℝ} (hε : 0 < ε)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) (sw bx bY : Bool) (hb : bx = sw ∧ bY = !sw)
    (hF : val0 { P with ε := ε } Φ (ctD₂ D) k μ ν (if sw then repF0 else repF1) =
      QED.OneLoop.energyFirstIntegral fun q => fBubble P Φ (ctD₂ D) rep sw bx bY ε k q μ ν)
    (hG : val0 { P with ε := ε } Φ D k μ ν (if sw then repG0 else repG1) =
      QED.OneLoop.energyFirstIntegral fun q => gBubble { P with ε := ε } Φ D rep k q μ ν) :
    val0 { P with ε := ε } Φ D k μ ν (if sw then repG0 else repG1) +
        val0 { P with ε := ε } Φ (ctD₂ D) k μ ν (if sw then repF0 else repF1) =
      (ε * I) * QED.OneLoop.energyFirstIntegral fun q =>
        remBlock Φ rep (dR P D) sw bx bY ε k q μ ν := by
  have hfB := (vpf_fBubble P Φ (ctD₂ D) rep m₀ hm₀ hmass hrep hPV₁ hPV₂ sw bx bY).2 ε hε k μ ν
  have hR := (vpf_remBlock Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (dR P D) sw bx bY).2 ε hε k μ ν
  have hpt : (fun q => gBubble { P with ε := ε } Φ D rep k q μ ν) = fun q =>
      (-1 : ℂ) * fBubble P Φ (ctD₂ D) rep sw bx bY ε k q μ ν +
        (ε * I) * remBlock Φ rep (dR P D) sw bx bY ε k q μ ν := by
    funext q
    cases sw
    · obtain ⟨rfl, rfl⟩ : bx = false ∧ bY = true := by simpa using hb
      rw [fBubble_ctD₂_F1 P Φ D rep hd hε.ne']
      ring
    · obtain ⟨rfl, rfl⟩ : bx = true ∧ bY = false := by simpa using hb
      rw [fBubble_ctD₂_F0 P Φ D rep hd hε.ne']
      ring
  rw [hG, hF, hpt, efi_add (hfB.const_mul _) (hR.const_mul _),
    QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul,
    QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  ring

/-- **(L2) The gauge classes cancel the `d₂` part of the insertions** in the limit `ε → 0⁺`,
once `d₁ = d₂` at level `0`. -/
theorem tendsto_gauge_add_d₂ (hd : ∀ f, D.d₁ f 0 = D.d₂ f 0) {k : Fin 4 → ℝ}
    (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => val0 { P with ε := ε } Φ D k μ ν repG0 +
        val0 { P with ε := ε } Φ D k μ ν repG1 +
        (val0 { P with ε := ε } Φ (ctD₂ D) k μ ν repF0 +
          val0 { P with ε := ε } Φ (ctD₂ D) k μ ν repF1)) (𝓝[>] 0) (𝓝 0) := by
  have hD₁ : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 := fun f => (hD f).1
  have hD' : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 := fun f => (hD f).2
  have hk' : -(m₀ + m₀) ^ 2 < Minkowski.dot k k := by nlinarith
  have lim : ∀ sw bx bY : Bool, Tendsto (fun ε : ℝ => (ε * I) *
      QED.OneLoop.energyFirstIntegral fun q => remBlock Φ rep (dR P D) sw bx bY ε k q μ ν)
      (𝓝[>] 0) (𝓝 0) := fun sw bx bY => by
    obtain ⟨W, hW, -, -⟩ :=
      (vpf_remBlock Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ (dR P D) sw bx bY).hasVPLim
    have h := tendsto_epsI.mul (hW k hk' μ ν)
    rwa [zero_mul] at h
  have h := (lim true true false).add (lim false false true)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have e0 := val0_G_add_F_eq P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hd hε k μ ν true true false
    ⟨rfl, rfl⟩ (val0_repF0 _ Φ (ctD₂ D) rep (hD_ctD₂ D rep hD') k μ ν)
    (val0_repG0 _ Φ D rep hD₁ k μ ν)
  have e1 := val0_G_add_F_eq P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ hd hε k μ ν false false true
    ⟨rfl, rfl⟩ (val0_repF1 _ Φ (ctD₂ D) rep (hD_ctD₂ D rep hD') k μ ν)
    (val0_repG1 _ Φ D rep hD₁ k μ ν)
  simp only [ite_true, Bool.false_eq_true, ite_false] at e0 e1
  rw [← e0, ← e1]
  ring

/-- **(L1 + L2) The form factor with the pure mass insertion**: at every `s ≠ 0` of the region,
`Π(s) = -e⁴ d₃(1) + i (π_VA + π_VB + π_VC + π_F0[ctδ D] + π_F1[ctδ D])(s)`. -/
theorem pol_eq_piCl_ctδ (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hd : ∀ f, D.d₁ f 0 = D.d₂ f 0)
    {Pol : ℝ → ℂ} (hPol : IsPol P Φ D (4 * m₀ ^ 2) Pol) {s : ℝ} (hs : -(4 * m₀ ^ 2) < s)
    (hs0 : s ≠ 0) :
    Pol s = -((P.e ^ 4 * D.d₃ 1 : ℝ) : ℂ) +
      I * (piCl P Φ D repVA s + piCl P Φ D repVB s + piCl P Φ D repVC s +
        piCl P Φ (ctδ D) repF0 s + piCl P Φ (ctδ D) repF1 s) := by
  set k := QED.GradedProof.SE2.canonVec s
  have hk : -(4 * m₀ ^ 2) < Minkowski.dot k k := by rwa [QED.GradedProof.SE2.dot_canonVec]
  have hks : Minkowski.dot k k ≠ 0 := by rwa [QED.GradedProof.SE2.dot_canonVec]
  have hD' : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 := fun f => (hD f).2
  have hFδ0 := tendsto_wCl_F0 P Φ (ctδ D) rep hm₀ hmass hrep hPV₁ hPV₂ (hD_ctδ D rep hD') hk
  have hFδ1 := tendsto_wCl_F1 P Φ (ctδ D) rep hm₀ hmass hrep hPV₁ hPV₂ (hD_ctδ D rep hD') hk
  have e : (fun μ ν => Pol (Minkowski.dot k k) * vpT k μ ν) = fun μ ν =>
      -((P.e ^ 4 * D.d₃ 1 : ℝ) : ℂ) * vpT k μ ν +
        I * (wCl P Φ D repVA k μ ν + wCl P Φ D repVB k μ ν + wCl P Φ D repVC k μ ν +
          wCl P Φ (ctδ D) repF0 k μ ν + wCl P Φ (ctδ D) repF1 k μ ν) := by
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
  have h := congrArg (trProj k) e
  rw [trProj_mul_vpT hks, trProj_combo5, trProj_vpT hks] at h
  rw [QED.GradedProof.SE2.dot_canonVec] at h
  simp only [piCl]
  rw [h]
  ring

end Limit

end QED.GradedProof.RPi4

end
