/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1EPiV
public import QED.GradedProof.X1EPiF
public import QED.GradedProof.RPi4VJVClass
public import QED.GradedProof.RPi4FVBlock
public import QED.GradedProof.VP2LimG
public import QED.GradedProof.VP2LimF
public import QED.GradedProof.VP2VLim
public import QED.GradedProof.VP2Weights
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.WickModel.LszPhotonLeg

/-!
# (X₁) piece E: the order-`e⁴` vacuum polarization near `k = 0`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece E. The photon legs of (X₁) are evaluated at `q = r' - r → 0`; they need the
`ε → 0⁺` limits of the vacuum-polarization parts near `k = 0`, continuous at `k = 0` with value
`0`. This is the proposition `VPZeroLim P Φ D n`.

* `vpZeroLim_of`: a limit on a region `k² > -T` (`T > 0`), continuous at `0`, together with the
  photon on-shell condition (`QED.Graded.IsPhotonOnShellAt`, which at `k = 0` says the limit
  there is `0`), gives `VPZeroLim`;
* `vpZeroLim_two`: `VPZeroLim P Φ D 2` under the hypotheses of (X₁). The limit is the explicit sum
  of the class values (`QED.GradedProof.VP2.vacuumPolarizationPart_two_eq`): the counterterm,
  `vVal` of `VA`, `VB`, `VC`, `polG (k²) (k² g - k k)` twice and `fbVal` of `F0`, `F1`; each is
  continuous at `k = 0` (`QED.GradedProof.X1E.continuousAt_vVal_VA`,
  `QED.GradedProof.X1E.continuousAt_fbVal`, and the continuity of the one-loop function).
-/

@[expose] public section

open Complex Filter Topology Set
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X1E

open QED.GradedProof.VP2 QED.GradedProof.RPi4

/-- The Minkowski square is continuous. -/
theorem continuous_dot_self : Continuous fun k : Fin 4 → ℝ => Minkowski.dot k k := by
  unfold Minkowski.dot
  refine continuous_finsetSum _ fun μ _ => continuous_finsetSum _ fun ν _ => ?_
  exact (continuous_const.mul (continuous_apply μ)).mul (continuous_apply ν)

theorem dot_zero_self : Minkowski.dot (0 : Fin 4 → ℝ) 0 = 0 := by simp [Minkowski.dot]

/-- The tensor `k² g^{μν} - k^μ k^ν` is continuous. -/
theorem continuous_vpT (μ ν : Fin 4) : Continuous fun k => vpT k μ ν := by
  unfold vpT
  exact continuous_ofReal.comp ((continuous_dot_self.mul continuous_const).sub
    ((continuous_apply μ).mul (continuous_apply ν)))

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- **The vacuum polarization part of order `2n` has a limit near `k = 0`, continuous at `0`,
with value `0` there.** -/
def VPZeroLim (n : ℕ) : Prop :=
  ∃ G : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ,
    (∀ᶠ k in 𝓝 (0 : Fin 4 → ℝ), ∀ μ ν, Tendsto
      (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D n k μ ν) (𝓝[>] 0)
      (𝓝 (G k μ ν))) ∧
    ∀ μ ν, ContinuousAt (fun k => G k μ ν) 0 ∧ G 0 μ ν = 0

theorem eventually_dot_gt {T : ℝ} (hT : 0 < T) :
    ∀ᶠ k in 𝓝 (0 : Fin 4 → ℝ), -T < Minkowski.dot k k :=
  (isOpen_lt continuous_const continuous_dot_self).mem_nhds (by
    show -T < Minkowski.dot (0 : Fin 4 → ℝ) 0
    rw [dot_zero_self]; linarith)

/-- **`VPZeroLim` from a limit on a region `k² > -T`**, continuous at `0`, and the photon on-shell
condition. -/
theorem vpZeroLim_of {n : ℕ} {T : ℝ} (hT : 0 < T) (G : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hlim : ∀ k, -T < Minkowski.dot k k → ∀ μ ν, Tendsto
      (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D n k μ ν) (𝓝[>] 0)
      (𝓝 (G k μ ν)))
    (hc : ∀ μ ν, ContinuousAt (fun k => G k μ ν) 0) (hon : IsPhotonOnShellAt P Φ D n) :
    VPZeroLim P Φ D n := by
  refine ⟨G, (eventually_dot_gt hT).mono fun k hk => hlim k hk, fun μ ν => ⟨hc μ ν, ?_⟩⟩
  have h0 : -T < Minkowski.dot (0 : Fin 4 → ℝ) 0 := by rw [dot_zero_self]; linarith
  exact tendsto_nhds_unique (hlim 0 h0 μ ν) (hon 0 dot_zero_self μ ν)

omit [DecidableEq F] in
/-- The block-summed one-loop coefficient is continuous at `s = 0`. -/
theorem continuousAt_polBlock (rep : F → F) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (d : F → ℂ) :
    ContinuousAt (polBlock P Φ rep d) 0 := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  have hlt : ∀ g, Φ.mass g < auxX Φ := fun g => by
    have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
    simp only [auxX]
    linarith
  unfold polBlock
  refine tendsto_finsetSum _ fun f _ => ?_
  have hL : ContinuousAt (QED.WickModel.vacuumPolarizationLoop
      (triParams P (Φ.mass f) (auxX Φ) (auxX Φ + 1))) 0 :=
    (QED.WickModel.continuousOn_vacuumPolarizationLoop (P := triParams P (Φ.mass f) (auxX Φ)
      (auxX Φ + 1)) (hpos f) (hlt f) (by show Φ.mass f < auxX Φ + 1; linarith [hlt f])
      ).continuousAt (Ioi_mem_nhds (by
        show -(4 * Φ.mass f ^ 2) < 0
        have := pow_pos (hpos f) 2; linarith))
  exact ((continuous_ofReal.continuousAt.comp hL).const_mul I |>.const_mul _).const_mul _

section Two

variable (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
  (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)

/-- The limit of the order-`e⁴` vacuum polarization part on `k² > -4 m₀²`. -/
noncomputable def piTwoLim (k : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  -((P.e ^ 4 * D.d₃ 1 * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ) : ℂ) +
    I * (vVal aVA baseVA cVA Φ P.e m₀ P.mγ P.Λ k μ ν +
      vVal aVB baseVB cVB Φ P.e m₀ P.mγ P.Λ k μ ν +
      vVal aVC baseVC cVC Φ P.e m₀ P.mγ P.Λ k μ ν +
      polG P Φ D rep (Minkowski.dot k k) * vpT k μ ν +
      polG P Φ D rep (Minkowski.dot k k) * vpT k μ ν +
      fbVal P Φ D rep m₀ true true false k μ ν + fbVal P Φ D rep m₀ false false true k μ ν)

include hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂

theorem tendsto_piTwo (hD₁ : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0)
    (hD₂ : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0)
    {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => vacuumPolarizationPart { P with ε := ε } Φ D 2 k μ ν) (𝓝[>] 0)
      (𝓝 (piTwoLim P Φ D rep m₀ k μ ν)) := by
  have hk2 : -(2 * m₀) ^ 2 < Minkowski.dot k k := by
    linarith [show (2 * m₀) ^ 2 = 4 * m₀ ^ 2 by ring]
  have hk2' : -(m₀ + m₀) ^ 2 < Minkowski.dot k k := by
    linarith [show (m₀ + m₀) ^ 2 = 4 * m₀ ^ 2 by ring]
  have hne : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε using (ne_of_gt hε)
  have TVA := ((vpjv_VA Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ).2 k hk2 μ ν).congr'
    (hne.mono fun ε hε => (val0_repVA Φ D P hε k μ ν).symm)
  have TVB := ((vpjv_VB Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ).2 k hk2 μ ν).congr'
    (hne.mono fun ε hε => (val0_repVB Φ D P hε k μ ν).symm)
  have TVC := ((vpjv_VC Φ rep hm₀ hmass hrep hPV₁ hPV₂ P.e hmγ hΛ).2 k hk2 μ ν).congr'
    (hne.mono fun ε hε => (val0_repVC Φ D P hε k μ ν).symm)
  have TG0 := tendsto_val0_repG0 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD₁ hk μ ν
  have TG1 := tendsto_val0_repG1 P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hD₁ hk μ ν
  have TF0 := ((vpfv_fBubble P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ true true false).2 k hk2' μ ν
    ).congr fun ε => (val0_repF0 { P with ε := ε } Φ D rep hD₂ k μ ν).symm
  have TF1 := ((vpfv_fBubble P Φ D rep hm₀ hmass hrep hPV₁ hPV₂ false false true).2 k hk2' μ ν
    ).congr fun ε => (val0_repF1 { P with ε := ε } Φ D rep hD₂ k μ ν).symm
  refine Tendsto.congr (fun ε => (vacuumPolarizationPart_two_eq _ Φ D k μ ν).symm) ?_
  exact tendsto_const_nhds.add
    (tendsto_const_nhds.mul ((((((TVA.add TVB).add TVC).add TG0).add TG1).add TF0).add TF1))

omit hrep hPV₁ hPV₂ in
theorem continuousAt_piTwoLim (μ ν : Fin 4) :
    ContinuousAt (fun k => piTwoLim P Φ D rep m₀ k μ ν) 0 := by
  have hpol : ContinuousAt (fun k : Fin 4 → ℝ => polG P Φ D rep (Minkowski.dot k k) * vpT k μ ν)
      0 :=
    (ContinuousAt.comp_of_eq (continuousAt_polBlock P Φ rep hm₀ hmass _)
      continuous_dot_self.continuousAt dot_zero_self).mul (continuous_vpT μ ν).continuousAt
  have hct : Continuous fun k : Fin 4 → ℝ =>
      -((P.e ^ 4 * D.d₃ 1 * (Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν) : ℝ) : ℂ) :=
    (continuous_ofReal.comp (continuous_const.mul ((continuous_dot_self.mul continuous_const).sub
      ((continuous_apply μ).mul (continuous_apply ν))))).neg
  exact hct.continuousAt.add (continuousAt_const.mul
    (((((((continuousAt_vVal_VA Φ hm₀ hmass P.e hmγ hΛ μ ν).add
      (continuousAt_vVal_VB Φ hm₀ hmass P.e hmγ hΛ μ ν)).add
      (continuousAt_vVal_VC Φ hm₀ hmass P.e hmγ hΛ μ ν)).add hpol).add hpol).add
      (continuousAt_fbVal P Φ D rep hm₀ hmass true true false μ ν)).add
      (continuousAt_fbVal P Φ D rep hm₀ hmass false false true μ ν)))

/-- **(X₁) piece E, order `e⁴`**: the vacuum polarization part of order `4` has a limit near
`k = 0`, continuous at `0`, with value `0`. -/
theorem vpZeroLim_two (hD : IsRenormalizedThrough P Φ D rep 2) : VPZeroLim P Φ D 2 := by
  have hD₁ : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 := fun f => (hD.1 f 0 (by norm_num)).1
  have hD₂ : ∀ f, D.d₂ f 0 = D.d₂ (rep f) 0 ∧ D.dm f 0 = D.dm (rep f) 0 :=
    fun f => (hD.1 f 0 (by norm_num)).2
  exact vpZeroLim_of P Φ D (by positivity : 0 < 4 * m₀ ^ 2) (piTwoLim P Φ D rep m₀)
    (fun k hk μ ν => tendsto_piTwo P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD₁ hD₂ hk μ ν)
    (continuousAt_piTwoLim P Φ D rep m₀ hm₀ hmass hmγ hΛ)
    (hD.2 2 (by norm_num) le_rfl).2

end Two

end QED.GradedProof.X1E

end
