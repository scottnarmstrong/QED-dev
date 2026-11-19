/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Classes
public import QED.GradedProof.LoopCycle
public import QED.TwoLoop.IntegrableOrderFiveTransfer
public import QED.TwoLoop.ClassLimitVP
public import QED.Frozen.Graded.RegulatedAmplitude
public import QED.Frozen.Graded.GradedOrder
public import QED.LeptonProof.HMSplit

/-!
# The integrability clause of (G-Σ₂) from eight T1 class obligations

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), steps 1–2. The first clause of (G-Σ₂) asserts (T₉′) for the integrand of every
1PI one-fermion contraction `C` of graded order exactly `4` at any grading `g`, for flavour data
`Φ` with masses at least `m₀ > 0`, the two Pauli–Villars conditions, open line `f` and any
counterterm data `D`. This file reduces it to (T₉′) for the eight class representatives of
`QED/GradedProof/SE2Classes.lean` in packet T1's model (`QED.WickModel.regulatedAmplitude₂`) at
every admissible T1 parameter set (`Adm`: `ε, m, M₁, M₂, m_γ, Λ > 0` and T1's two
Pauli–Villars conditions): `jointEnergyFirstIntegrable_of_classes`.

## Proof

* **Nonzero grading.** A counterterm vertex of level `≥ 1` has graded order `≥ 4`, so the vertex
  orders sum to at most `2`; a counterterm vertex costs two orders
  (`QED.GradedProof.two_mul_loopCount_add_le_sum_order`), so `C` has no loop and (T₉′) is
  trivial (`jointEnergyFirstIntegrable_zero`).
* **Zero grading.** The vertex orders sum to `4`. Every such 1PI contraction is simple and has
  its counterterm vertices on the open line (`isSimple_of_order_four`,
  `ctReaches_of_order_four`), so its graded integrand is the integrand of the flavour model at
  the parameters `seParams₂` carrying the open-line level-`0` data
  (`QED.GradedProof.regulatedAmplitude_zero_eq`), which is `A(M_f, M_f)` without a closed loop
  and `∑_g c_g A(M_f, M_g)` with one (`QED.Lepton.Proof.HM.regulatedAmplitude₂_of_hasLoop`),
  `A(a, b)` the amplitude with open-line mass `a` and loop mass `b`.
* Without a loop this is T1's integrand at `seParams₂` with the reference regulators
  `(2 M_f, 3 M_f)`, coefficients `(-8/5, 3/5)` (`refT1`). With a loop it is
  `∑_g w_g` times T1's integrand at `auxT1 g` (regulators `(M_g, X)`, coefficients fixed by
  T1's two conditions at the open-line mass `M_f`), with `X` above all masses and
  `w_g = c_g (M_g² - X²)/(X² - M_f²)`: the weights sum to `0` by the two Pauli–Villars
  conditions of `Φ`, and the auxiliary loops of masses `M_f` and `X` cancel
  (`sum_auxWeight_mul`).
* T1's (T₉′) passes to relabellings of 1PI contractions
  (`QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_relabelK`), so the eight class
  obligations give it for every listed contraction (`classInt_of_order_four`), and (T₉′) is
  stable under finite linear combinations.
-/

@[expose] public section

open Complex MeasureTheory
open QED.WickModel (Params Contraction IsOnePI loopCount lineMomentum₂)

namespace QED.GradedProof.SE2

open QED.Graded QED.Lepton.Proof.HM QED.TwoLoop.Relabel

/-! ### (T₉′) at zero loops and for finite sums -/

/-- With no loop momentum, (T₉′) holds for every integrand. -/
theorem jointEnergyFirstIntegrable_zero (F : (Fin 0 → Fin 4 → ℝ) → ℂ) :
    QED.TwoLoop.jointEnergyFirstIntegrable 0 F := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [Measure.volume_pi_eq_dirac]
    exact Integrable.of_finite
  · rw [Measure.volume_pi_eq_dirac]
    exact Integrable.of_finite

/-- (T₉′) is stable under finite linear combinations. -/
theorem jointEnergyFirstIntegrable_sum {ι : Type*} (s : Finset ι) {L : ℕ} (w : ι → ℂ)
    (G : ι → (Fin L → Fin 4 → ℝ) → ℂ)
    (h : ∀ i ∈ s, QED.TwoLoop.jointEnergyFirstIntegrable L (G i)) :
    QED.TwoLoop.jointEnergyFirstIntegrable L fun ℓ => ∑ i ∈ s, w i * G i ℓ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨fun _ => integrable_zero _ _ _, ?_⟩
    simp only [integral_zero]
    exact integrable_zero _ _ _
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add
      (QED.TwoLoop.ClassLimit.jointEnergyFirstIntegrable_const_mul _
        (h a (Finset.mem_insert_self a s)))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### The T1 class obligations -/

/-- **Admissible T1 parameters**: positive `ε`, masses and photon regulators, and T1's two
Pauli–Villars conditions. -/
structure Adm (Q : Params) : Prop where
  hε : 0 < Q.ε
  hm : 0 < Q.m
  hM₁ : 0 < Q.M₁
  hM₂ : 0 < Q.M₂
  hmγ : 0 < Q.mγ
  hΛ : 0 < Q.Λ
  pv₁ : 1 + Q.c₁ + Q.c₂ = 0
  pv₂ : Q.m ^ 2 + Q.c₁ * Q.M₁ ^ 2 + Q.c₂ * Q.M₂ ^ 2 = 0

/-- (T₉′) for the integrand of a one-fermion contraction of T1 at the self-energy kinematics
`pOut = pIn = p`, at every admissible parameter set. -/
def ClassInt {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 0 κ) : Prop :=
  ∀ Q : Params, Adm Q → ∀ (p : Fin 4 → ℝ) (α β : Fin 4),
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
        QED.WickModel.regulatedAmplitude₂ Q C ![p] ![] (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α]
          ![β] ![]

/-- The class obligation passes to relabellings of 1PI contractions. -/
theorem classInt_relabelK {N : ℕ} {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
    (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 1 0 κ) (hC : IsOnePI C) (h : ClassInt C) :
    ClassInt (relabelK π hκ C) := fun Q hQ p α β =>
  QED.TwoLoop.IntegrableOrderFive.jointEnergyFirstIntegrable_relabelK Q π hκ hC
    (by simp) ![α] ![β] ![] (h Q hQ p α β)

/-- **The eight class obligations give T1's (T₉′) for every 1PI one-fermion contraction of
total order `4`.** -/
theorem classInt_of_order_four (hR : ClassInt repR) (hX : ClassInt repX) (hV : ClassInt repV)
    (hF : ClassInt repF) (hP0 : ClassInt repP0) (hP1 : ClassInt repP1) (hC1 : ClassInt repC1)
    (hC2 : ClassInt repC2) {N : ℕ} {κ : Fin N → Wick.VertexKind} (h : ∑ t, (κ t).order = 4)
    (C : Contraction 1 0 κ) (hC : IsOnePI C) : ClassInt C :=
  induction_of_order_four (fun C => ClassInt C) (fun π hκ C hC h => classInt_relabelK π hκ C hC h)
    hR hX hV hF hP0 hP1 hC1 hC2 h C hC

/-! ### The T1 parameter sets -/

section Params

variable (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F)

/-- The parameters at the open-line level-`0` data of flavour `f`, with open-line mass `M_f`. -/
def seParams₂ : Params :=
  { P with
    δ₁ := P.e ^ 2 * D.d₁ f 0
    δ₂ := P.e ^ 2 * D.d₂ f 0
    δm := P.e ^ 2 * D.dm f 0
    δ₃ := P.e ^ 2 * D.d₃ 0
    m := Φ.mass f }

/-- T1 at `seParams₂` with the reference regulators `(2 M_f, 3 M_f)`, coefficients
`(-8/5, 3/5)`. -/
noncomputable def refT1 : Params :=
  { seParams₂ P Φ D f with M₁ := 2 * Φ.mass f, M₂ := 3 * Φ.mass f, c₁ := -8 / 5, c₂ := 3 / 5 }

/-- The coefficient of the regulator of mass `b` in the T1 set with regulators `(b, X)` at the
open-line mass `a`. -/
noncomputable def auxC (a b X : ℝ) : ℝ := (X ^ 2 - a ^ 2) / (b ^ 2 - X ^ 2)

/-- T1 at `seParams₂` with regulators `(M_g, X)` and the coefficients fixed by the two
Pauli–Villars conditions at the open-line mass `M_f`. -/
noncomputable def auxT1 (X : ℝ) (g : F) : Params :=
  { seParams₂ P Φ D f with
    M₁ := Φ.mass g, M₂ := X, c₁ := auxC (Φ.mass f) (Φ.mass g) X,
    c₂ := -1 - auxC (Φ.mass f) (Φ.mass g) X }

/-- The weight of `auxT1 X g`. -/
noncomputable def auxW (X : ℝ) (g : F) : ℝ :=
  Φ.coeff g * (Φ.mass g ^ 2 - X ^ 2) / (X ^ 2 - Φ.mass f ^ 2)

theorem adm_refT1 (hε : 0 < P.ε) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hf : 0 < Φ.mass f) :
    Adm (refT1 P Φ D f) where
  hε := hε
  hm := hf
  hM₁ := by simp only [refT1]; positivity
  hM₂ := by simp only [refT1]; positivity
  hmγ := hmγ
  hΛ := hΛ
  pv₁ := by simp only [refT1]; norm_num
  pv₂ := by simp only [refT1, seParams₂]; ring

theorem adm_auxT1 (hε : 0 < P.ε) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hf : 0 < Φ.mass f) {X : ℝ}
    (g : F) (hg : 0 < Φ.mass g) (hgX : Φ.mass g < X) : Adm (auxT1 P Φ D f X g) where
  hε := hε
  hm := hf
  hM₁ := hg
  hM₂ := hg.trans hgX
  hmγ := hmγ
  hΛ := hΛ
  pv₁ := by simp only [auxT1]; ring
  pv₂ := by
    simp only [auxT1, seParams₂, auxC]
    have : Φ.mass g ^ 2 - X ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring

end Params

/-! ### T1's integrand at the auxiliary sets -/

section Amplitudes

variable (P : Params) {F : Type} (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F)
  {N : ℕ} {κ : Fin N → Wick.VertexKind} {C : Contraction 1 0 κ} (hS : IsSimple C)
  (pIn : Fin 1 → Fin 4 → ℝ) (kIn : Fin 0 → Fin 4 → ℝ) (k : QED.WickModel.Line C → Fin 4 → ℝ)
  (αOut βIn : Fin 1 → Fin 4) (μ : Fin 0 → Fin 4)

/-- Without a closed loop, T1's integrand at `refT1` is the open-line amplitude at
`seParams₂`. -/
theorem regulatedAmplitude₂_refT1 (hL : ¬ HasLoop C) :
    QED.WickModel.regulatedAmplitude₂ (refT1 P Φ D f) C pIn kIn k αOut βIn μ =
      loopAmp (seParams₂ P Φ D f) hS (Φ.mass f) (Φ.mass f) pIn kIn k αOut βIn μ := by
  rw [← regulatedAmplitude₂_t1F, regulatedAmplitude₂_of_not_hasLoop _ _ hS hL]
  rfl

/-- With a closed loop, T1's integrand at `auxT1 X g` is `A(M_f, M_f) + a_g A(M_f, M_g) +
(-1 - a_g) A(M_f, X)`. -/
theorem regulatedAmplitude₂_auxT1 (hL : HasLoop C) (X : ℝ) (g : F) :
    QED.WickModel.regulatedAmplitude₂ (auxT1 P Φ D f X g) C pIn kIn k αOut βIn μ =
      loopAmp (seParams₂ P Φ D f) hS (Φ.mass f) (Φ.mass f) pIn kIn k αOut βIn μ +
        (auxC (Φ.mass f) (Φ.mass g) X : ℂ) *
          loopAmp (seParams₂ P Φ D f) hS (Φ.mass f) (Φ.mass g) pIn kIn k αOut βIn μ +
        ((-1 - auxC (Φ.mass f) (Φ.mass g) X : ℝ) : ℂ) *
          loopAmp (seParams₂ P Φ D f) hS (Φ.mass f) X pIn kIn k αOut βIn μ := by
  rw [← regulatedAmplitude₂_t1F, regulatedAmplitude₂_of_hasLoop _ _ hS hL, Fin.sum_univ_three]
  simp only [t1F, QED.WickModel.Params.loopCoeff, QED.WickModel.Params.mass,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Complex.ofReal_one, one_mul]
  rfl

end Amplitudes

/-- The weighted sum of the auxiliary integrands is the flavour-summed loop. -/
theorem sum_auxWeight_mul {F : Type} [Fintype F] (A₀ AX : ℂ) (A : F → ℂ) (w a c : F → ℝ)
    (hwa : ∀ g, w g * a g = c g) (hw : ∑ g, w g = 0) (hc : ∑ g, c g = 0) :
    ∑ g, (w g : ℂ) * (A₀ + (a g : ℂ) * A g + ((-1 - a g : ℝ) : ℂ) * AX) =
      ∑ g, (c g : ℂ) * A g := by
  have hw' : ∑ g, (w g : ℂ) = 0 := by exact_mod_cast hw
  have hc' : ∑ g, (c g : ℂ) = 0 := by exact_mod_cast hc
  calc ∑ g, (w g : ℂ) * (A₀ + (a g : ℂ) * A g + ((-1 - a g : ℝ) : ℂ) * AX)
      = ∑ g, ((w g : ℂ) * A₀ + (c g : ℂ) * A g - (w g : ℂ) * AX - (c g : ℂ) * AX) :=
        Finset.sum_congr rfl fun g _ => by rw [← hwa g]; push_cast; ring
    _ = (∑ g, (w g : ℂ)) * A₀ + ∑ g, (c g : ℂ) * A g - (∑ g, (w g : ℂ)) * AX -
          (∑ g, (c g : ℂ)) * AX := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul]
    _ = ∑ g, (c g : ℂ) * A g := by rw [hw', hc']; ring

/-! ### The integrability clause -/

/-- **The first clause of (G-Σ₂) from the eight T1 class obligations.** -/
theorem jointEnergyFirstIntegrable_of_classes (hR : ClassInt repR) (hX : ClassInt repX)
    (hV : ClassInt repV) (hF : ClassInt repF) (hP0 : ClassInt repP0) (hP1 : ClassInt repP1)
    (hC1 : ClassInt repC1) (hC2 : ClassInt repC2) (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) :
    ∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind) (g : Grading κ), gradedOrder κ g = 4 →
      ∀ C : Contraction 1 0 κ, IsOnePI C → ∀ (p : Fin 4 → ℝ) (α β : Fin 4),
        QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
          (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
            regulatedAmplitude { P with ε := ε } { Φ with openLine := f } D C g ![p] ![]
              (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![] := by
  intro ε hε N κ g hg C hC p α β
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  by_cases hg0 : g = 0
  · subst hg0
    have h4 : ∑ t, (κ t).order = 4 := by rwa [gradedOrder_zero] at hg
    have hS := isSimple_of_order_four h4 C hC
    have hCt := ctReaches_of_order_four h4 C hC
    have hCI := classInt_of_order_four hR hX hV hF hP0 hP1 hC1 hC2 h4 C hC
    have hε₁ : 0 < ({ P with ε := ε } : Params).ε := hε
    have hmγ₁ : 0 < ({ P with ε := ε } : Params).mγ := hmγ
    have hΛ₁ : 0 < ({ P with ε := ε } : Params).Λ := hΛ
    generalize ({ P with ε := ε } : Params) = P₁ at hε₁ hmγ₁ hΛ₁ ⊢
    have hz : ∀ k : QED.WickModel.Line C → Fin 4 → ℝ,
        regulatedAmplitude P₁ { Φ with openLine := f } D C 0 ![p] ![] k ![α] ![β] ![] =
          Lepton.regulatedAmplitude₂ (seParams₂ P₁ Φ D f) { Φ with openLine := f } C ![p] ![] k
            ![α] ![β] ![] := fun k =>
      regulatedAmplitude_zero_eq P₁ (seParams₂ P₁ Φ D f) { Φ with openLine := f } D C hCt rfl
        rfl rfl rfl (fun _ _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => rfl) ![p] ![] k
        ![α] ![β] ![]
    by_cases hL : HasLoop C
    · obtain ⟨X, hlt⟩ : ∃ X : ℝ, ∀ g, Φ.mass g < X := ⟨1 + ∑ g, Φ.mass g, fun g => by
        have := Finset.single_le_sum (f := Φ.mass) (fun g _ => (hpos g).le) (Finset.mem_univ g)
        linarith⟩
      have hXf : X ^ 2 - Φ.mass f ^ 2 ≠ 0 := by
        have := hlt f
        have := hpos f
        nlinarith
      have hJ := jointEnergyFirstIntegrable_sum Finset.univ (fun g => (auxW Φ f X g : ℂ))
        (fun g ℓ => (((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹ *
          QED.WickModel.regulatedAmplitude₂ (auxT1 P₁ Φ D f X g) C ![p] ![]
            (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![])
        fun g _ => hCI _ (adm_auxT1 P₁ Φ D f hε₁ hmγ₁ hΛ₁ (hpos f) g (hpos g) (hlt g)) p α β
      convert hJ using 1
      funext ℓ
      rw [hz, regulatedAmplitude₂_of_hasLoop _ _ hS hL]
      simp only [regulatedAmplitude₂_auxT1 P₁ Φ D f hS _ _ _ _ _ _ hL]
      have hsum := sum_auxWeight_mul
        (loopAmp (seParams₂ P₁ Φ D f) hS (Φ.mass f) (Φ.mass f) ![p] ![]
          (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![])
        (loopAmp (seParams₂ P₁ Φ D f) hS (Φ.mass f) X ![p] ![]
          (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![])
        (fun g => loopAmp (seParams₂ P₁ Φ D f) hS (Φ.mass f) (Φ.mass g) ![p] ![]
          (lineMomentum₂ C ![p] ![p] ![] ℓ) ![α] ![β] ![])
        (auxW Φ f X) (fun g => auxC (Φ.mass f) (Φ.mass g) X) Φ.coeff
        (fun g => by
          have : Φ.mass g ^ 2 - X ^ 2 ≠ 0 := by
            have := hlt g
            have := hpos g
            nlinarith
          simp only [auxW, auxC]
          field_simp)
        (by
          simp only [auxW, ← Finset.sum_div]
          rw [div_eq_zero_iff]
          left
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hPV₁, hPV₂, zero_mul,
            sub_zero])
        hPV₁
      simp only [mul_left_comm _ ((((2 * Real.pi) ^ (4 * loopCount C) : ℝ) : ℂ)⁻¹),
        ← Finset.mul_sum]
      rw [hsum]
    · have hJ := hCI _ (adm_refT1 P₁ Φ D f hε₁ hmγ₁ hΛ₁ (hpos f)) p α β
      convert hJ using 1
      funext ℓ
      rw [hz, regulatedAmplitude₂_of_not_hasLoop _ _ hS hL,
        regulatedAmplitude₂_refT1 P₁ Φ D f hS _ _ _ _ _ _ hL]
  · obtain ⟨t, ht⟩ : ∃ t : CtVertex κ, 1 ≤ g t := by
      obtain ⟨t, ht⟩ := Function.ne_iff.1 hg0
      exact ⟨t, Nat.one_le_iff_ne_zero.2 ht⟩
    have h2 := Finset.single_le_sum (f := fun t : CtVertex κ => 2 * g t)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have h4 := hg
    unfold gradedOrder at h4
    have hL := two_mul_loopCount_add_le_sum_order hC.1 hC.2.1 t.1 t.2
    have hL0 : loopCount C = 0 := by omega
    have key : ∀ (L : ℕ) (G : (Fin L → Fin 4 → ℝ) → ℂ), L = 0 →
        QED.TwoLoop.jointEnergyFirstIntegrable L G := by
      rintro L G rfl
      exact jointEnergyFirstIntegrable_zero G
    exact key _ _ hL0

end QED.GradedProof.SE2

end
