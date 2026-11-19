/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2ClassG0
public import QED.GradedProof.VP2WeightsZero
public import QED.GradedProof.VP2TensorForm
public import QED.TwoLoop.NestedVP
public import QED.TwoLoop.JointIntegral
public import QED.WickModel.VacuumPolarizationLimit
public import QED.Integration.EnergyFirstShift

/-!
# The classes `G0`, `G1`: the `ε → 0⁺` limit

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), clause 2. The value of a
graded contraction with a single chord is the energy-first integral (D) of its shifted one-loop
integrand (`contractionValue_of_one_chord`). For `repG0`, `repG1` this integrand is the
block-summed bubble `∑_f c_f e² δ₁(rep f) W(M_f)`, which the block hypotheses rewrite as a sum
of three-flavour Pauli–Villars one-loop vacuum-polarization integrands; their limits
(`QED.WickModel.tendsto_energyFirstIntegral_vacuumPolarizationIntegrand`) are already transverse,
so no Ward step is needed: `val0 → polG(k²) (k² g - k k)` on `k² > -4 m₀²`
(`tendsto_val0_repG0`, `tendsto_val0_repG1`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology

namespace QED.GradedProof.VP2

open QED.Graded QED.TwoLoop.Enumeration QED.TwoLoop.Routing QED.TwoLoop.Insertion
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂ Line IsChord
  vacuumPolarizationIntegrand vacuumPolarizationLoop)

section OneChord

variable {nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **The value of a graded contraction with one chord** is the energy-first integral of the
shifted one-loop integrand of its routing. -/
theorem contractionValue_of_one_chord (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) {nf : ℕ} {C : Contraction nf nA κ}
    (g : Grading κ) {c : Line C} (hc : ∀ g, IsChord g ↔ g = c) {pOut pIn : Fin nf → Fin 4 → ℝ}
    {kIn : Fin nA → Fin 4 → ℝ} (mom : (Fin 4 → ℝ) → Line C → Fin 4 → ℝ)
    (hcons : ∀ ℓ, IsConserved C pOut pIn kIn (mom ℓ)) (hchord : ∀ ℓ, mom ℓ c = ℓ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) (G : (Fin 4 → ℝ) → ℂ) (s : Fin 4 → ℝ)
    (hpt : ∀ ℓ, (((2 * Real.pi) ^ 4 : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude P Φ D C g pIn kIn (mom ℓ) αOut βIn μ = G (ℓ - s)) :
    contractionValue P Φ D C g pOut pIn kIn αOut βIn μ = QED.OneLoop.energyFirstIntegral G := by
  unfold contractionValue
  rw [loopCount_eq_one_of_unique hc]
  have hfun : (fun ℓ : Fin 1 → Fin 4 → ℝ => (((2 * Real.pi) ^ (4 * 1) : ℝ) : ℂ)⁻¹ *
      regulatedAmplitude P Φ D C g pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) =
      fun ℓ => G (ℓ 0 - s) := by
    funext ℓ
    rw [QED.TwoLoop.IntegrableOrderFive.lineMomentum₂_eq_of_unique hc mom hcons hchord, mul_one,
      hpt]
  rw [hfun, QED.TwoLoop.jointEnergyFirstIntegral_one_eq (fun q => G (q - s)),
    QED.OneLoop.energyFirstIntegral_sub_right_eq_self]

end OneChord

section Block

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (rep : F → F)

/-- The auxiliary regulator mass `X = 1 + ∑ M_g`, above every flavour mass. -/
noncomputable def auxX : ℝ := 1 + ∑ g, Φ.mass g

/-- **The limit coefficient of the block-summed bubble**
`∑_f c_f (-d(rep f)) i Π_loop[M_f, X, X + 1](s)`. -/
noncomputable def polBlock (d : F → ℂ) (s : ℝ) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * (-d (rep f) *
    (I * (vacuumPolarizationLoop (triParams P (Φ.mass f) (auxX Φ) (auxX Φ + 1)) s : ℂ)))

/-- **The block-summed bubble converges** below `4 m₀²` to `polBlock(k²) (k² g - k k)`. -/
theorem tendsto_blockBubble (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (d : F → ℂ) {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun q =>
        ∑ f, (Φ.coeff f : ℂ) * (d (rep f) * bubbleW P.e (Φ.mass f) ε k q μ ν))
      (𝓝[>] 0) (𝓝 (polBlock P Φ rep d (Minkowski.dot k k) * vpT k μ ν)) := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set X : ℝ := auxX Φ with hX
  have hlt : ∀ g, Φ.mass g < X := fun g => by
    have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
    simp only [hX, auxX]
    linarith
  have hXY : ∀ g, Φ.mass g < X + 1 := fun g => (hlt g).trans (by linarith)
  set Q : F → Params := fun f => triParams P (Φ.mass f) X (X + 1) with hQ
  have hpv : ∀ f, 1 + (Q f).c₁ + (Q f).c₂ = 0 := fun f =>
    triA_triB_pv₁ _ _ _ (by nlinarith [hlt f, hpos f])
  have hpv₂ : ∀ f, (Q f).m ^ 2 + (Q f).c₁ * (Q f).M₁ ^ 2 + (Q f).c₂ * (Q f).M₂ ^ 2 = 0 :=
    fun f => triA_triB_pv₂ _ _ _ (by nlinarith [hlt f, hpos f])
  have hsplit : ∀ ε ℓ, ∑ f, (Φ.coeff f : ℂ) * (d (rep f) * bubbleW P.e (Φ.mass f) ε k ℓ μ ν) =
      ∑ f, (Φ.coeff f : ℂ) * (-d (rep f) * vacuumPolarizationIntegrand (Q f) ε k ℓ μ ν) :=
    fun ε ℓ => by
      rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1)
        (fun b M => d b * bubbleW P.e M ε k ℓ μ ν)]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [hQ, vacuumPolarizationIntegrand_triParams]
      ring
  have hD : ∀ ε, 0 < ε → ∀ f, QED.TwoLoop.NestedVP.IntegrableD fun ℓ =>
      (Φ.coeff f : ℂ) * (-d (rep f) * vacuumPolarizationIntegrand (Q f) ε k ℓ μ ν) :=
    fun ε hε f => ((QED.TwoLoop.NestedVP.IntegrableD.const_mul ⟨fun v =>
      QED.WickModel.VacuumPolarizationLimit.integrable_vacuumPolarizationIntegrand_time hε _ k μ
        ν v,
      QED.WickModel.VacuumPolarizationLimit.integrable_integral_vacuumPolarizationIntegrand
        (P := Q f) (hpos f) (hlt f) (hXY f) (hpv f) (hpv₂ f) hε k μ ν⟩ _).const_mul _)
  have heq : ∀ ε, 0 < ε → (QED.OneLoop.energyFirstIntegral fun q =>
      ∑ f, (Φ.coeff f : ℂ) * (d (rep f) * bubbleW P.e (Φ.mass f) ε k q μ ν)) =
      ∑ f, (Φ.coeff f : ℂ) * (-d (rep f) * QED.OneLoop.energyFirstIntegral fun ℓ =>
        vacuumPolarizationIntegrand (Q f) ε k ℓ μ ν) := fun ε hε => by
    simp only [hsplit ε]
    rw [QED.TwoLoop.NestedVP.energyFirstIntegral_finsetSum _ _ fun f _ => hD ε hε f]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul,
      QED.TwoLoop.NestedVP.energyFirstIntegral_const_mul]
  have hlim : ∀ f, Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun ℓ =>
      vacuumPolarizationIntegrand (Q f) ε k ℓ μ ν) (𝓝[>] 0)
      (𝓝 (I * (vacuumPolarizationLoop (Q f) (Minkowski.dot k k) : ℂ) * vpT k μ ν)) := fun f =>
    QED.WickModel.tendsto_energyFirstIntegral_vacuumPolarizationIntegrand (hpos f) (hlt f)
      (hXY f) (hpv f) (hpv₂ f)
      (show -(4 * Φ.mass f ^ 2) < Minkowski.dot k k by nlinarith [hmass f, hpos f]) μ ν
  have hsum := tendsto_finsetSum (Finset.univ : Finset F) fun f _ =>
    ((hlim f).const_mul (-d (rep f))).const_mul (Φ.coeff f : ℂ)
  refine (hsum.congr' ?_).trans ?_
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (heq ε hε).symm
  · refine le_of_eq (congrArg _ ?_)
    simp only [polBlock, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [hQ, hX]
    ring

end Block

/-! ### The classes `G0`, `G1` -/

section Classes

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) (rep : F → F)

/-- The block-summed bubble of the classes `G0`, `G1`. -/
noncomputable def gBubble (k q : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) * (((P.e ^ 2 * D.d₁ (rep f) 0 : ℝ) : ℂ) *
    bubbleW P.e (Φ.mass f) P.ε k q μ ν)

theorem val0_repG0 (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    val0 P Φ D k μ ν repG0 =
      QED.OneLoop.energyFirstIntegral fun q => gBubble P Φ D rep k q μ ν :=
  contractionValue_of_one_chord P Φ D 0 g0_isChord_iff (g0Mom k) (g0_isConserved k)
    (fun ℓ => (g0Mom_apply k ℓ).1) ![] ![] ![μ, ν] _ 0
    (fun ℓ => (g0_integrand P Φ D rep hD k ℓ μ ν).trans (by rw [sub_zero]; rfl))

theorem val0_repG1 (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    val0 P Φ D k μ ν repG1 =
      QED.OneLoop.energyFirstIntegral fun q => gBubble P Φ D rep k q μ ν :=
  contractionValue_of_one_chord P Φ D 0 g1_isChord_iff (g1Mom k) (g1_isConserved k)
    (fun ℓ => (g1Mom_apply k ℓ).1) ![] ![] ![μ, ν] _ k
    (fun ℓ => (g1_integrand P Φ D rep hD k ℓ μ ν).trans rfl)

/-- The limit coefficient of each of the classes `G0`, `G1`. -/
noncomputable def polG (s : ℝ) : ℂ :=
  polBlock P Φ rep (fun b => ((P.e ^ 2 * D.d₁ b 0 : ℝ) : ℂ)) s

theorem tendsto_gBubble (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => QED.OneLoop.energyFirstIntegral fun q =>
        gBubble { P with ε := ε } Φ D rep k q μ ν)
      (𝓝[>] 0) (𝓝 (polG P Φ D rep (Minkowski.dot k k) * vpT k μ ν)) :=
  tendsto_blockBubble P Φ rep m₀ hm₀ hmass hrep hPV₁ hPV₂ _ hk μ ν

/-- **The limit of the class `G0`.** -/
theorem tendsto_val0_repG0 (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0)
    {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => val0 { P with ε := ε } Φ D k μ ν repG0)
      (𝓝[>] 0) (𝓝 (polG P Φ D rep (Minkowski.dot k k) * vpT k μ ν)) := by
  refine (tendsto_gBubble P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hk μ ν).congr fun ε => ?_
  rw [val0_repG0 _ Φ D rep hD]

/-- **The limit of the class `G1`.** -/
theorem tendsto_val0_repG1 (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0)
    {k : Fin 4 → ℝ} (hk : -(4 * m₀ ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => val0 { P with ε := ε } Φ D k μ ν repG1)
      (𝓝[>] 0) (𝓝 (polG P Φ D rep (Minkowski.dot k k) * vpT k μ ν)) := by
  refine (tendsto_gBubble P Φ D rep m₀ hm₀ hmass hrep hPV₁ hPV₂ hk μ ν).congr fun ε => ?_
  rw [val0_repG1 _ Φ D rep hD]

end Classes

end QED.GradedProof.VP2

end
