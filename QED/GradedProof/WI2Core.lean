/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2T1Ward
public import QED.GradedProof.WI2SESplit
public import QED.GradedProof.V5ZeroInput
public import QED.GradedProof.V5ZeroDirac
public import QED.GradedProof.GEx2Solve

/-!
# The order-`5` charge from the order-`4` slope

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57). For
counterterm data `D` whose level-`1` coefficients of flavour `f` vanish and whose level-`0` ones
obey `d₁ = d₂` (WI₁), let the order-`4` self-energy of `f` converge near the shell to
`A(p²) p̸ + B(p²) M` (`GEx2.SELimit`) with shell slope `σ₁` and the order-`5` vertex at `q = 0`
converge to `c γ^μ` between on-shell spinors. Then `c = -e σ₁` (`charge_eq_neg_e_mul_slope`).

Both sides are split into the same T1 parameter sets with the same real weights
(`selfEnergyPart_two_add_tree_eq_split`, `V5Zero.Split.vertexOrderFive_split`); each set obeys the
Ward identity `hasDerivAt_sandwich_seLim`. We differentiate `w Σ(t p) u` at `t = 1` in the rest
frame, where `w u ≠ 0`.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.WI2

open QED.Graded
open QED.WickModel (Params)
open QED.GradedProof.V5Zero (Adm limV combV)

/-- In the rest frame there are on-shell spinors with `w u ≠ 0`. -/
theorem exists_rest_sandwich_ne_zero {M : ℝ} (hM : 0 < M) :
    ∃ u w : Fin 4 → ℂ, Dirac.slash (V5Zero.Dirac.restVec M) *ᵥ u = -((M : ℂ) • u) ∧
      w ᵥ* Dirac.slash (V5Zero.Dirac.restVec M) = -((M : ℂ) • w) ∧ w ⬝ᵥ u ≠ 0 := by
  have hp := V5Zero.Dirac.dot_restVec M
  have hp0 : 0 < V5Zero.Dirac.restVec M 0 := by simp [V5Zero.Dirac.restVec, hM]
  obtain ⟨u, w, hu, hw, hne⟩ :=
    QED.OneLoop.VertexLimit.exists_sandwich_gamma_zero_ne_zero hM hp hp0
  refine ⟨u, w, hu, hw, ?_⟩
  have hM' : (-(M : ℂ)) ≠ 0 := neg_ne_zero.2 (by exact_mod_cast hM.ne')
  have h0 : Dirac.gamma 0 *ᵥ u = u := by
    apply smul_right_injective (Fin 4 → ℂ) hM'
    simp only
    rw [← Matrix.smul_mulVec, ← V5Zero.Dirac.slash_restVec, hu, neg_smul]
  rwa [h0] at hne

/-- The T1 vertex combination as a combination of the class sums. -/
theorem combV_eq_vtxSum {ι : Type*} [Fintype ι] {m₀ : ℝ} {S : ι → Params} (a : ι → ℝ)
    (h : ∀ k, Adm m₀ (S k)) {p : Fin 4 → ℝ} (hp : ∀ k, Minkowski.dot p p = -(S k).m ^ 2)
    (hp0 : 0 < p 0) (μ : Fin 4) :
    combV S a p μ = ∑ k, ((a k : ℂ) * (1 / I)) • vtxSum (S k) p μ := by
  simp only [combV]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := h k
  rw [V5Zero.Lim.eq_classLimits_of_isVertexOrderFiveLimit (S k) hk.hm₀ hk.hm hk.hmγ hk.hΛ hk.hM₁
    hk.hM₂ hk.hc₁ hk.hc₂ (hp k) (hp k) hp0 hp0 (V5Zero.dot_sub_self p).ge
    (V5Zero.isLimit_limV hk (hp k) hp0), mul_smul]
  rfl

/-- The shell function between on-shell spinors. -/
theorem sandwich_shell (A B : ℝ → ℂ) {M : ℝ} {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -M ^ 2)
    {u : Fin 4 → ℂ} (hu : Dirac.slash p *ᵥ u = -((M : ℂ) • u)) (w : Fin 4 → ℂ) (t : ℝ) :
    w ⬝ᵥ ((A (Minkowski.dot (t • p) (t • p)) • Dirac.slash (t • p) +
      (B (Minkowski.dot (t • p) (t • p)) * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) *ᵥ u) =
      GEx2.shellFun A B M (-(t * M)) * (w ⬝ᵥ u) := by
  have hd : Minkowski.dot (t • p) (t • p) = -(-(t * M)) ^ 2 := by
    rw [QED.GradedProof.SE2.dot_smul_smul, hp]
    ring
  simp only [GEx2.shellFun, hd, QED.Dirac.slash_smul, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec, hu, dotProduct_smul, dotProduct_add, dotProduct_neg, smul_eq_mul]
  push_cast
  ring

/-- **The order-`5` charge is `-e` times the order-`4` shell slope** (data with vanishing level-`1`
coefficients of flavour `f` and `d₁ = d₂` at level `0`). -/
theorem charge_eq_neg_e_mul_slope (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) (he : P.e ≠ 0)
    (hδ : D.d₁ f 0 = D.d₂ f 0) (h1₁ : D.d₁ f 1 = 0) (h1₂ : D.d₂ f 1 = 0) (h1m : D.dm f 1 = 0)
    {r : ℝ} (hr : 0 < r) {A B : ℝ → ℂ} (hlim : GEx2.SELimit P Φ D f r A B) {σ₁ : ℝ}
    (hσ₁ : HasDerivAt (GEx2.shellFun A B (Φ.mass f)) σ₁ (-Φ.mass f)) {c : ℝ}
    (hc : ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -Φ.mass f ^ 2 → 0 < p 0 → ∀ (μ : Fin 4)
      (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((Φ.mass f : ℂ) • u) →
      w ᵥ* Dirac.slash p = -((Φ.mass f : ℂ) • w) →
      Tendsto (fun ε : ℝ => w ⬝ᵥ (vertexPart { P with ε := ε } Φ D f 2 p p μ *ᵥ u)) (𝓝[>] 0)
        (𝓝 ((c : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))))) :
    c = -(P.e * σ₁) := by
  classical
  set M := Φ.mass f with hMdef
  have hM : 0 < M := hm₀.trans_le (hmass f)
  set Φ' : Lepton.Flavors F := { Φ with openLine := f } with hΦ'
  set Q := GEx2.vParams P Φ D f with hQ
  obtain ⟨X, -, hmX, -, hlt, -, hXm, hX⟩ := V5Zero.Split.exists_aux Q.m Φ'.mass
  let S : Option F → Params := fun k =>
    k.elim (V5Zero.Split.zParams Q X) (V5Zero.Split.gParams Q Φ' X)
  let a : Option F → ℝ := fun k => k.elim 1 (V5Zero.Split.weight Q Φ' X)
  have hmf : m₀ ≤ Q.m := hmass f
  have hadm : ∀ k, Adm m₀ (S k) := by
    rintro (_ | g)
    · exact ⟨hm₀, hmf, hmγ, hΛ, hmf, hmf.trans hmX.le, V5Zero.Split.zParams_PV₁ Q X,
        V5Zero.Split.zParams_PV₂ Q X⟩
    · exact ⟨hm₀, hmf, hmγ, hΛ, hmass g, hmf.trans hmX.le, V5Zero.Split.gParams_PV₁ Q Φ' X g,
        V5Zero.Split.gParams_PV₂ Q Φ' X g (hX g)⟩
  have hSm : ∀ k, (S k).m = M := by rintro (_ | _) <;> rfl
  have hSe : ∀ k, (S k).e ≠ 0 := by rintro (_ | _) <;> exact he
  have hSδ : ∀ k, (S k).δ₁ = (S k).δ₂ := by
    rintro (_ | _) <;>
      simp only [S, Option.elim, V5Zero.Split.zParams, V5Zero.Split.gParams, Q,
        GEx2.vParams, hδ]
  obtain ⟨u, w, hu, hw, hwu⟩ := exists_rest_sandwich_ne_zero hM
  set p := V5Zero.Dirac.restVec M
  have hp : Minkowski.dot p p = -M ^ 2 := V5Zero.Dirac.dot_restVec M
  have hp0 : 0 < p 0 := by simp [p, V5Zero.Dirac.restVec, hM]
  have hpk : ∀ k, Minkowski.dot p p = -(S k).m ^ 2 := fun k => by rw [hSm k]; exact hp
  have huk : ∀ k, Dirac.slash p *ᵥ u = -(((S k).m : ℂ) • u) := fun k => by rw [hSm k]; exact hu
  have hwk : ∀ k, w ᵥ* Dirac.slash p = -(((S k).m : ℂ) • w) := fun k => by rw [hSm k]; exact hw
  -- the vertex side
  have hV : ∀ μ, (c : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)) = w ⬝ᵥ (combV S a p μ *ᵥ u) := by
    intro μ
    have key : ∀ ε : ℝ, 0 < ε → vertexPart { P with ε := ε } Φ D f 2 p p μ =
        ∑ k, (a k : ℂ) • QED.TwoLoop.vertexOrderFive { S k with ε := ε } p p μ := by
      intro ε hε
      rw [GEx2.vertexPart_two_eq_vParams,
        show GEx2.vParams { P with ε := ε } Φ D f = { Q with ε := ε } from rfl,
        V5Zero.Split.vertexOrderFive_split (Q := { Q with ε := ε }) (Φ := Φ') (X := X) hε rfl
          hPV₁ hPV₂ hXm hX p p μ, Fintype.sum_option, h1₁]
      simp only [S, a, Option.elim, Complex.ofReal_one, one_smul, mul_zero, zero_mul,
        Complex.ofReal_zero, zero_smul, add_zero]
      rfl
    refine tendsto_nhds_unique (hc p hp hp0 μ u w hu hw)
      ((V5Zero.tendsto_combV a hadm hSm hp hp0 μ u w).congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [key ε hε]
  -- the self-energy side near `t = 1`
  have hSγ : ∀ k, (S k).mγ = P.mγ := by rintro (_ | _) <;> rfl
  have hSΛ : ∀ k, (S k).Λ = P.Λ := by rintro (_ | _) <;> rfl
  have hSe' : ∀ k, (S k).e = P.e := by rintro (_ | _) <;> rfl
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set ν : ℝ := min (min P.mγ P.Λ) (2 * m₀)
  have hν0 : 0 < ν := lt_min (lt_min hmγ hΛ) (by linarith)
  have hreg : ∀ T : ℝ, 0 < T → ∀ᶠ t in 𝓝 (1 : ℝ), -(M + T) ^ 2 < Minkowski.dot (t • p) (t • p) :=
    fun T hT => eventually_region p (by rw [one_smul, hp]; nlinarith)
  have hEq : ∀ᶠ t in 𝓝 (1 : ℝ), GEx2.shellFun A B M (-(t * M)) * (w ⬝ᵥ u) =
      (1 / I) * ∑ k, (a k : ℂ) * (w ⬝ᵥ (seLim (S k) (t • p) *ᵥ u)) := by
    filter_upwards [hreg r hr, hreg ν hν0] with t h1 h2
    have hmat : A (Minkowski.dot (t • p) (t • p)) • Dirac.slash (t • p) +
        (B (Minkowski.dot (t • p) (t • p)) * M) • (1 : Matrix (Fin 4) (Fin 4) ℂ) =
        (1 / I) • ∑ k, (a k : ℂ) • seLim (S k) (t • p) := by
      ext α β
      refine tendsto_nhds_unique (hlim (t • p) h1 α β) ?_
      have hT : ∀ k, Tendsto (fun ε => seClassSum { S k with ε := ε } (t • p) α β) (𝓝[>] 0)
          (𝓝 (seLim (S k) (t • p) α β)) := fun k =>
        tendsto_seClassSum (S k) (hadm k) (by rw [hSm k, hSγ k, hSΛ k]; exact h2) α β
      have hsum := (tendsto_finsetSum Finset.univ fun k _ =>
        (hT k).const_mul (a k : ℂ)).const_mul (1 / I)
      rw [show ((1 / I) • ∑ k, (a k : ℂ) • seLim (S k) (t • p)) α β =
          (1 / I) * ∑ k, (a k : ℂ) * seLim (S k) (t • p) α β by
        simp [Matrix.sum_apply]]
      refine hsum.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hs := selfEnergyPart_two_add_tree_eq_split { P with ε := ε } Φ D f hε hmγ hΛ hpos
        hPV₁ hPV₂ hlt (t • p) α β
      have h0 : GEx2.seTree { P with ε := ε } Φ D f (t • p) α β = 0 := by
        simp [GEx2.seTree, h1₂, h1m]
      rw [h0, add_zero] at hs
      rw [hs, Fintype.sum_option]
      simp only [a, S, Option.elim, Complex.ofReal_one, one_mul]
      rfl
    rw [← sandwich_shell A B hp hu w t, hmat, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      Matrix.sum_mulVec, dotProduct_sum]
    simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hH : HasDerivAt (fun t : ℝ => GEx2.shellFun A B M (-(t * M)) * (w ⬝ᵥ u))
      (((-M : ℝ) • (σ₁ : ℂ)) * (w ⬝ᵥ u)) 1 := by
    have hc' : HasDerivAt (fun t : ℝ => -(t * M)) (-M) 1 := by
      have := ((hasDerivAt_id (1 : ℝ)).mul_const M).neg
      simp only [id, one_mul] at this
      exact this
    have hs : HasDerivAt (GEx2.shellFun A B M) (σ₁ : ℂ) (-(1 * M)) := by
      rw [one_mul]
      exact hσ₁
    exact (hs.scomp 1 hc').mul_const (w ⬝ᵥ u)
  have hG := (HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (hasDerivAt_sandwich_seLim (S k) (hSe k) (hSδ k) (hadm k) (hpk k) hp0 (huk k)
      (hwk k)).const_mul (a k : ℂ)).const_mul (1 / I)
  have huniq := hH.unique (hG.congr_of_eventuallyEq hEq)
  simp only [hSe'] at huniq
  -- the vertex side contracted with `p`
  have hcomb : ∑ μ, ((Minkowski.lower p μ : ℝ) : ℂ) * (w ⬝ᵥ (combV S a p μ *ᵥ u)) =
      (c : ℂ) * (-(M : ℂ) * (w ⬝ᵥ u)) := by
    simp only [← hV, mul_left_comm _ (c : ℂ), ← Finset.mul_sum, sum_lower_sandwich_gamma, hu,
      dotProduct_neg, dotProduct_smul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun μ _ => by rw [combV_eq_vtxSum a hadm hpk hp0 μ]] at hcomb
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
    smul_eq_mul] at hcomb
  have hG' : (1 / I) * ∑ k, (a k : ℂ) * (-(1 / (P.e : ℂ)) * ∑ μ,
      ((Minkowski.lower p μ : ℝ) : ℂ) * (w ⬝ᵥ (vtxSum (S k) p μ *ᵥ u))) =
      -(1 / (P.e : ℂ)) * ∑ μ, ((Minkowski.lower p μ : ℝ) : ℂ) *
        ∑ k, (a k : ℂ) * (1 / I) * (w ⬝ᵥ (vtxSum (S k) p μ *ᵥ u)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hG', hcomb, Complex.real_smul] at huniq
  have he' : (P.e : ℂ) ≠ 0 := by exact_mod_cast he
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast at huniq
  field_simp at huniq
  have : ((c : ℝ) : ℂ) = ((-(P.e * σ₁) : ℝ) : ℂ) := by
    push_cast
    linear_combination -huniq
  exact_mod_cast this

end QED.GradedProof.WI2

end
