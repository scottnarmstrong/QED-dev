/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkVSplit
public import QED.ChainProof.SetCLinkShareAlg
public import QED.GradedProof.V5ZeroInput

/-!
# Set (c), model link: the vertex input (I2) of the VP share

Helper for (G-ex-s) `QED.ThreeLoop.existsUnique_isVPShareOnShell` (decision D-58): the input
`QED.ChainProof.SetCLink.VPVInput`, the restriction of `QED.GradedProof.V5Zero.vertexZeroInput`
to the classes `VP`, `d3Slot0`, `d3Slot1`.

* `famLim S p`: `(1/i)(-W_VP + W_{d3Slot0} + W_{d3Slot1})` for the class limits at `p' = p`;
  the T1 family vertex `famT1` converges to it (`tendsto_famT1`), it is covariant under spinor
  lifts (`cov_famLim`: `V5Zero.Lim.classLimitV_VP_map`, `PauliZero.ctLimitV_map`) and `♯`-fixed
  (`sharp_famLim`: every class limit has `W♯ = -W`, and `conj (1/i) = -(1/i)`).
* **`vpVInput`**: under the hypotheses of (G-Σ₂), for every `D`, `VPVInput P Φ (dZero D)`: the
  selected vertex of `dZero D` is that of `levelZero (dZero D)` (`familyVertex_five_sub`), hence
  a real combination of T1 family vertices (`familyVertex_split`), whose sandwiched limit is
  `c · w γ^μ u` with one real `c` (`V5Zero.Dirac.exists_real_sandwich_eq_of_cov`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.ChainProof.SetCLink

open QED.Graded QED.GradedProof QED.GradedProof.V5Zero
open QED.WickModel (Params)
open QED.TwoLoop.Enumeration QED.TwoLoop.Relabel
open QED.TwoLoop.LimitCovariance (IsSpinLift classLimitV ctLimitV)
open QED.Dirac (vecAct)
open QED.TwoLoop.CountertermLimit (exists_tendsto_contractionValue₂_ctClass)

/-- The class limits of the vacuum-polarization family at `p' = p`. -/
noncomputable def famLim (S : Params) (p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => (1 / I) • ((Class5.VP.sign : ℂ) • classLimitV .VP S p p μ +
    ctLimitV .d3Slot0 S p p μ + ctLimitV .d3Slot1 S p p μ)

section Lim

variable {m₀ : ℝ} {S : Params} (h : Adm m₀ S) {p : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -S.m ^ 2) (hp0 : 0 < p 0)
include h hp hp0

theorem tendsto_famT1 (μ : Fin 4) :
    Tendsto (fun ε : ℝ => famT1 { S with ε := ε } p p μ) (𝓝[>] 0) (𝓝 (famLim S p μ)) := by
  have hmom : (fun _ : Fin 1 => p) 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p - p) 0 := by
    simp
  have hq := (dot_sub_self p).ge
  have hm : 0 < S.m := h.hm₀.trans_le h.hm
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hVP := tendsto_nhds_limUnder (Lim.exists_tendsto_contractionValue₂_nonFurry
    (c := .VP) (by decide) S h.hm₀ h.hm h.hmγ h.hΛ h.hM₁ h.hM₂ h.hc₁ h.hc₂
    (pOut := fun _ => p) (pIn := fun _ => p) (kIn := fun _ => p - p) hmom hp hp hq
    (fun _ => i) (fun _ => j) (fun _ => μ))
  have h0 := tendsto_nhds_limUnder (exists_tendsto_contractionValue₂_ctClass
    .d3Slot0 S hm h.hmγ h.hΛ (pOut := fun _ => p) (pIn := fun _ => p) (kIn := fun _ => p - p)
    hmom hp hp hp0 hp0 hq (fun _ => i) (fun _ => j) (fun _ => μ))
  have h1 := tendsto_nhds_limUnder (exists_tendsto_contractionValue₂_ctClass
    .d3Slot1 S hm h.hmγ h.hΛ (pOut := fun _ => p) (pIn := fun _ => p) (kIn := fun _ => p - p)
    hmom hp hp hp0 hp0 hq (fun _ => i) (fun _ => j) (fun _ => μ))
  have hT := (((hVP.const_mul (Class5.VP.sign : ℂ)).add h0).add h1).const_mul (1 / I)
  exact hT

theorem sharp_famLim (μ : Fin 4) :
    SE2Real.sharp (famLim S p μ) = famLim S p μ := by
  have hm : 0 < S.m := h.hm₀.trans_le h.hm
  have hq := (dot_sub_self p).ge
  have hconj : starRingEnd ℂ (1 / I) = -(1 / I) := by
    rw [map_div₀, map_one, Complex.conj_I, div_neg]
  simp only [famLim]
  rw [SE2Real.sharp_smul, hconj, SE2Real.sharp_add, SE2Real.sharp_add, SE2Real.sharp_smul,
    Sharp.sharp_classLimitV_VP S h.hm₀ h.hm h.hmγ h.hΛ h.hM₁ h.hM₂ h.hc₁ h.hc₂ hp hp hq μ,
    Sharp.sharp_ctLimitV _ S hm h.hmγ h.hΛ hp hp hp0 hp0 hq μ,
    Sharp.sharp_ctLimitV _ S hm h.hmγ h.hΛ hp hp hp0 hp0 hq μ, map_intCast]
  simp only [smul_neg, neg_smul, ← neg_add, neg_neg]

theorem cov_famLim {L : Matrix (Fin 4) (Fin 4) ℝ} {A B : Matrix (Fin 4) (Fin 4) ℂ}
    (hL : IsSpinLift L A B) (hLp0 : 0 < (L *ᵥ p) 0) (μ : Fin 4) :
    A * famLim S (L *ᵥ p) μ * B = vecAct L (famLim S p) μ := by
  have hm : 0 < S.m := h.hm₀.trans_le h.hm
  have hq := (dot_sub_self p).ge
  have eVP := Lim.classLimitV_VP_map S h.hm₀ h.hm h.hmγ h.hΛ h.hM₁ h.hM₂ h.hc₁ h.hc₂ hL hp hp
    hq μ
  have e0 := QED.TwoLoop.PauliZero.ctLimitV_map .d3Slot0 S hm h.hmγ h.hΛ hL hp hp hp0 hp0 hLp0
    hLp0 hq μ
  have e1 := QED.TwoLoop.PauliZero.ctLimitV_map .d3Slot1 S hm h.hmγ h.hΛ hL hp hp hp0 hp0 hLp0
    hLp0 hq μ
  calc A * famLim S (L *ᵥ p) μ * B = (1 / I) • ((Class5.VP.sign : ℂ) •
        (A * classLimitV .VP S (L *ᵥ p) (L *ᵥ p) μ * B) +
        A * ctLimitV .d3Slot0 S (L *ᵥ p) (L *ᵥ p) μ * B +
        A * ctLimitV .d3Slot1 S (L *ᵥ p) (L *ᵥ p) μ * B) := by
        simp only [famLim, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
    _ = vecAct L (famLim S p) μ := by
        rw [eVP, e0, e1]
        unfold famLim
        rw [QED.Dirac.vecAct_smul, QED.Dirac.vecAct_add, QED.Dirac.vecAct_add,
          QED.Dirac.vecAct_smul]

end Lim

/-- **Input (I2).** Under the hypotheses of (G-Σ₂), the selected order-`5` vertex of `dZero D`
at `q = 0` tends to `c · w γ^μ u` between on-shell spinors, for one real `c`. -/
theorem vpVInput (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (m₀ : ℝ) (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hPV₁ : ∑ g, Φ.coeff g = 0)
    (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) : VPVInput P Φ (dZero D) := by
  classical
  set D₁ := levelZero (dZero D) with hD₁
  have hD : ∀ f k, 1 ≤ k → D₁.d₁ f k = 0 ∧ D₁.d₂ f k = 0 ∧ D₁.dm f k = 0 := fun f k hk => by
    simp [hD₁, levelZero, show k ≠ 0 by omega]
  have hD₃ : ∀ k, 1 ≤ k → D₁.d₃ k = 0 := fun k hk => by
    simp [hD₁, levelZero, show k ≠ 0 by omega]
  have hfv : ∀ (Q : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4),
      familyVertex Q Φ (dZero D) selV 5 p' p μ = familyVertex Q Φ D₁ selV 5 p' p μ := by
    intro Q p' p μ
    rw [familyVertex_five_sub Q Φ (dZero D) D₁ (by simp [hD₁, levelZero])
      (by simp [hD₁, levelZero]) (by simp [hD₁, levelZero]) (by simp [hD₁, levelZero])
      (fun _ => by simp [hD₁, levelZero]) (fun _ => by simp [hD₁, levelZero])
      (fun _ => by simp [hD₁, levelZero])]
    simp [hD₁, levelZero, dZero, Counterterms.withLevel]
  set Q := GEx2.vParams P Φ D₁ Φ.openLine with hQ
  obtain ⟨X, -, hmX, -, -, -, hXm, hX⟩ := Split.exists_aux Q.m Φ.mass
  let S : Option F → Params := fun k => k.elim (Split.zParams Q X) (Split.gParams Q Φ X)
  let a : Option F → ℝ := fun k => k.elim 1 (Split.weight Q Φ X)
  have hmf : m₀ ≤ Q.m := hmass _
  have hadm : ∀ k, Adm m₀ (S k) := by
    rintro (_ | g)
    · exact ⟨hm₀, hmf, hmγ, hΛ, hmf, hmf.trans hmX.le, Split.zParams_PV₁ Q X,
        Split.zParams_PV₂ Q X⟩
    · exact ⟨hm₀, hmf, hmγ, hΛ, hmass g, hmf.trans hmX.le, Split.gParams_PV₁ Q Φ X g,
        Split.gParams_PV₂ Q Φ X g (hX g)⟩
  have hSm : ∀ k, (S k).m = Φ.mass Φ.openLine := by rintro (_ | _) <;> rfl
  have hM : 0 < Φ.mass Φ.openLine := hm₀.trans_le (hmass _)
  set comb : (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
    fun p μ => ∑ k, (a k : ℂ) • famLim (S k) p μ with hcomb
  obtain ⟨c, hc⟩ := Dirac.exists_real_sandwich_eq_of_cov hM comb
    (fun L A B hL p hp hp0 hLp0 μ => by
      have e : comb p = fun ν => ∑ k ∈ Finset.univ, (a k : ℂ) • famLim (S k) p ν := rfl
      rw [e, QED.TwoLoop.VertexCovariance.vecAct_finset_sum]
      simp only [hcomb, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [cov_famLim (hadm k) ((hSm k).symm ▸ hp) hp0 hL hLp0 μ])
    (fun p hp hp0 μ => by
      simp only [hcomb, SE2Real.sharp_sum, SE2Real.sharp_smul, Complex.conj_ofReal]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sharp_famLim (hadm k) ((hSm k).symm ▸ hp) hp0 μ])
  refine ⟨c, fun p hp hp0 μ u w hu hw => ?_⟩
  have key : ∀ ε : ℝ, 0 < ε → familyVertex { P with ε := ε } Φ (dZero D) selV 5 p p μ =
      ∑ k, (a k : ℂ) • famT1 { S k with ε := ε } p p μ := by
    intro ε hε
    rw [hfv, familyVertex_split (P := { P with ε := ε }) (X := X) hε hPV₁ hPV₂ hXm hX hD hD₃,
      Fintype.sum_option]
    simp only [S, a, Option.elim, Complex.ofReal_one, one_smul]
    rfl
  have hE : ∀ k, Tendsto (fun ε : ℝ => famT1 { S k with ε := ε } p p μ) (𝓝[>] 0)
      (𝓝 (famLim (S k) p μ)) := fun k =>
    tendsto_famT1 (hadm k) ((hSm k).symm ▸ hp) hp0 μ
  have hS : Tendsto (fun ε : ℝ => ∑ k, (a k : ℂ) • famT1 { S k with ε := ε } p p μ) (𝓝[>] 0)
      (𝓝 (comb p μ)) :=
    tendsto_finsetSum _ fun k _ => (hE k).const_smul _
  have hcont : Continuous fun M : Matrix (Fin 4) (Fin 4) ℂ => w ⬝ᵥ (M *ᵥ u) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hT := (hcont.tendsto _).comp hS
  rw [Function.comp_def, hc p hp hp0 μ u w hu hw] at hT
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [key ε hε]

end QED.ChainProof.SetCLink

end
