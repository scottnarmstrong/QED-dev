/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispShellSESum
public import QED.ChainProof.SetCRegDispCtVP
public import QED.ChainProof.SetCLinkShareTree
public import QED.WickModel.PhotonCounterterm
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (c): the limit of the selected self-energy at an admissible datum

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`, input `hCtS`
through `QED.ChainProof.SetCRegDisp.shellDisp_of_values_C`, step b3 (first half).

* **`seLimitSel_apply_eq`**: at an admissible datum, every limit pair `(A, B)` of
  `SetCLink.SELimitSel` satisfies, below threshold,
  `(A(p²) p̸ + B(p²) m)_{αβ} = (1/i) ∫₀¹ seGIntLim P p α β x dx` with `P` the regulated
  parameters. The self-energy is split into T1 sets (`SetCLink.selfEnergySelPart_split`), the
  limits are summed by `t1_sum_seVPLim`, and the counterterm part
  `κ_SE (c₁ L/6 - δ₃) seCtComb` vanishes by the photon renormalization `e² d₃(0) = Π_loop(0)`
  (`setCAdm_d3_zero`, `WickModel.vacuumPolarizationLoop_zero`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.ChainProof.SetCRegDisp

open QED.WickModel (Params)
open QED.Graded QED.GradedProof
open QED.TwoLoop.VPHalfAtAssembly (cOne logSum)
open QED.GradedProof.SE2 (kappaSE)
open QED.GradedProof.V5Zero.Split (zParams gParams weight)
open QED.ChainProof.SetCK QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-- The flavour sum of one-loop integrands is the regulated `x`-integrand. -/
theorem sum_regFlavors_seGIntM (Q : Params) (hm : Q.m = P₀.m) (he : Q.e = P₀.e)
    (hγ : Q.mγ = mγ) (hΛ : Q.Λ = Λ) (p : Fin 4 → ℝ) (α β : Fin 4) (x : ℝ) :
    ∑ g, (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).coeff g •
        seGIntM Q p α β x ((regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).mass g) =
      seGIntLim (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) p α β x := by
  have hQ : seGIntM Q p α β x = seGIntM (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) p α β x := by
    funext M
    simp only [seGIntM, seVK, cOne, seCL, seMs4, seMs5, hm, he, hγ, hΛ]
  rw [seGIntLim_eq_sum, hQ, Fintype.sum_sum_type]
  simp
  rfl

/-- **The counterterm part vanishes** at an admissible datum. -/
theorem ctPart_eq_zero (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) :
    cOne P₀ * (1 / 6) * ∑ g, (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).coeff g •
        log ((((regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).mass g ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) -
      ((P₀.e ^ 2 * D.d₃ 0 : ℝ) : ℂ) = 0 := by
  rw [setCAdm_d3_zero hA, QED.WickModel.vacuumPolarizationLoop_zero, Fintype.sum_sum_type]
  have hlog : ∀ M : ℝ, log (((M ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) = ((Real.log (M ^ 2) : ℝ) : ℂ) :=
    fun M => by
      rw [Complex.ofReal_zero, zero_mul, sub_zero, Complex.ofReal_log (sq_nonneg M)]
  simp only [hlog, Complex.real_smul, Finset.univ_eq_empty, Finset.sum_empty, add_zero, cOne]
  have hs : ∑ x : Fin 3, ((regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).coeff (Sum.inl x) : ℂ) *
      ((Real.log ((regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ).mass (Sum.inl x) ^ 2) : ℝ) : ℂ) =
      ∑ x : Fin 3, ((regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).loopCoeff x : ℂ) *
        ((Real.log ((regParams P₀ M₁ M₂ c₁ c₂ mγ Λ).mass x ^ 2) : ℝ) : ℂ) := rfl
  push_cast
  rw [hs]
  ring

/-- **The limit of the selected self-energy at an admissible datum**, below threshold: every
limit pair `(A, B)` of `SELimitSel` gives `(1/i) ∫₀¹ seGIntLim P p α β x dx`, `P` the regulated
parameters. -/
theorem seLimitSel_apply_eq (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) {r : ℝ} {A B : ℝ → ℂ}
    (hlim : SetCLink.SELimitSel (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ)
      (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (SetCLink.dZero D) r A B) {p : Fin 4 → ℝ}
    (h1 : -(P₀.m + r) ^ 2 < Minkowski.dot p p)
    (h2 : -(P₀.m + min mγ P₀.m) ^ 2 < Minkowski.dot p p) (α β : Fin 4) :
    (A (Minkowski.dot p p) • Dirac.slash p +
        (B (Minkowski.dot p p) * P₀.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β =
      (1 / I) * ∫ x in (0 : ℝ)..1, seGIntLim (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) p α β x := by
  classical
  obtain ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, hγΛ, hm2, -, -⟩ := id hA
  have hm : 0 < P₀.m := by linarith
  set P := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with hP
  set Φ := regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ with hΦ
  set D₁ := levelZero (SetCLink.dZero D) with hD₁
  have hD : ∀ f k, 1 ≤ k → D₁.d₁ f k = 0 ∧ D₁.d₂ f k = 0 ∧ D₁.dm f k = 0 := fun f k hk => by
    simp [hD₁, levelZero, show k ≠ 0 by omega]
  have hD₃ : ∀ k, 1 ≤ k → D₁.d₃ k = 0 := fun k hk => by
    simp [hD₁, levelZero, show k ≠ 0 by omega]
  set Q := GEx2.vParams P Φ D₁ Φ.openLine with hQ
  obtain ⟨X, -, hmX, -, hlt, -, hXm, hX⟩ := V5Zero.Split.exists_aux Q.m Φ.mass
  have hmass : ∀ g, P₀.m ≤ Φ.mass g := by
    rintro (i | ⟨j, _⟩)
    · fin_cases i <;> simp [Φ, Lepton.leptonFlavors, Params.mass] <;> linarith
    · exact j.elim0
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm.trans_le (hmass g)
  have hgt : ∀ g, g ≠ Φ.openLine → Q.m < Φ.mass g := by
    rintro (i | ⟨j, _⟩) hne
    · fin_cases i
      · exact absurd rfl hne
      · simpa [Q, Φ, Lepton.leptonFlavors, Params.mass, GEx2.vParams] using hM₁
      · simpa [Q, Φ, Lepton.leptonFlavors, Params.mass, GEx2.vParams] using hM₂
    · exact j.elim0
  have hΦ1 : ∑ g, Φ.coeff g = 0 := by
    simp [Φ, Lepton.leptonFlavors, Fintype.sum_sum_type, Fin.sum_univ_three, Params.loopCoeff]
    linarith
  have hΦ2 : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0 := by
    simp [Φ, Lepton.leptonFlavors, Fintype.sum_sum_type, Fin.sum_univ_three, Params.loopCoeff,
      Params.mass]
    linarith
  have hsplit : ∀ ε : ℝ, 0 < ε →
      selfEnergySelPart { P with ε := ε } Φ (SetCLink.dZero D) SetCLink.selSE Φ.openLine 2
        p α β =
        (1 / I) * (SetCLink.seVPValue { zParams Q X with ε := ε } p α β +
          ∑ g, (weight Q Φ X g : ℂ) *
            SetCLink.seVPValue { gParams Q Φ X g with ε := ε } p α β) := by
    intro ε hε
    have h2 := SetCLink.selfEnergySelPart_two_sub { P with ε := ε } Φ (SetCLink.dZero D) D₁
      (fun _ => by simp [hD₁, levelZero]) (fun _ => by simp [hD₁, levelZero])
      (fun _ => by simp [hD₁, levelZero]) (by simp [hD₁, levelZero]) Φ.openLine p α β
    have t0 : GEx2.seTree { P with ε := ε } Φ (SetCLink.dZero D) Φ.openLine p α β = 0 := by
      simp [GEx2.seTree, SetCLink.dZero, Counterterms.withLevel]
    have t1 : GEx2.seTree { P with ε := ε } Φ D₁ Φ.openLine p α β = 0 := by
      simp [GEx2.seTree, hD₁, levelZero]
    rw [t0, t1, add_zero, add_zero] at h2
    rw [h2, SetCLink.selfEnergySelPart_split { P with ε := ε } Φ D₁ Φ.openLine hε hmγ hΛ hpos
      hΦ1 hΦ2 hlt hD hD₃ p α β]
    rfl
  set ν : ℝ := min mγ P₀.m with hν
  have hν0 : 0 < ν := lt_min hmγ hm
  have hνγ : ν ≤ min Q.mγ Q.Λ := le_min (min_le_left _ _) ((min_le_left _ _).trans hγΛ.le)
  have hνm : ν ≤ Q.m := min_le_right _ _
  have hadmz : V5Zero.Adm P₀.m (zParams Q X) :=
    ⟨hm, le_rfl, hmγ, hΛ, le_rfl, hmX.le, V5Zero.Split.zParams_PV₁ Q X,
      V5Zero.Split.zParams_PV₂ Q X⟩
  have hadmg : ∀ g, V5Zero.Adm P₀.m (gParams Q Φ X g) := fun g =>
    ⟨hm, le_rfl, hmγ, hΛ, hmass g, hmX.le, V5Zero.Split.gParams_PV₁ Q Φ X g,
      V5Zero.Split.gParams_PV₂ Q Φ X g (hX g)⟩
  have hs : -(P₀.m + min (min mγ Λ) (2 * P₀.m)) ^ 2 < Minkowski.dot p p := by
    have hle : ν ≤ min (min mγ Λ) (2 * P₀.m) :=
      le_min (le_min (min_le_left _ _) ((min_le_left _ _).trans hγΛ.le))
        ((min_le_right _ _).trans (by linarith))
    nlinarith
  have hT := ((SetCLink.tendsto_seVPValue (zParams Q X) hadmz hs α β).add
    (tendsto_finsetSum Finset.univ fun g _ =>
      (SetCLink.tendsto_seVPValue (gParams Q Φ X g) (hadmg g) hs α β).const_mul
        (weight Q Φ X g : ℂ))).const_mul (1 / I)
  have huniq := tendsto_nhds_unique (hlim p h1 α β) (hT.congr' (by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (hsplit ε hε).symm))
  have hco : Φ.coeff Φ.openLine = 1 := by simp [Φ, Lepton.leptonFlavors, Params.loopCoeff]
  have huniq' : (A (Minkowski.dot p p) • Dirac.slash p +
      (B (Minkowski.dot p p) * P₀.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β =
      (1 / I) * (SetCLink.seVPLim (zParams Q X) p α β +
        ∑ g, (weight Q Φ X g : ℂ) * SetCLink.seVPLim (gParams Q Φ X g) p α β) := huniq
  rw [huniq', t1_sum_seVPLim (Q := Q) (Φ := Φ) (X := X) hm hmγ hΛ rfl hco hgt hΦ1 hΦ2 hmX hXm
    hX hν0 hνγ hνm h2 α β]
  have hd : Q.δ₃ = P₀.e ^ 2 * D.d₃ 0 := by
    simp [Q, GEx2.vParams, hD₁, levelZero, SetCLink.dZero, Counterterms.withLevel, P]
  have hct : cOne Q * (1 / 6) * ∑ g, Φ.coeff g •
      log (((Φ.mass g ^ 2 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I) - (Q.δ₃ : ℂ) = 0 := by
    rw [hd]
    exact ctPart_eq_zero hA
  rw [hct, mul_zero, zero_mul, add_zero]
  congr 1
  exact intervalIntegral.integral_congr fun x _ =>
    sum_regFlavors_seGIntM Q rfl rfl rfl rfl p α β x

end QED.ChainProof.SetCRegDisp

end
