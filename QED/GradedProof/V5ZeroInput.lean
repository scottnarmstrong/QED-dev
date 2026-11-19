/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.GEx2Inputs
public import QED.GradedProof.GEx2Affine
public import QED.GradedProof.V5ZeroTotal
public import QED.GradedProof.V5ZeroSplitVertex
public import QED.GradedProof.V5ZeroSharp
public import QED.GradedProof.V5ZeroDirac

/-!
# The order-`e⁵` vertex at `q = 0`: the vertex input of (G-ex₂)

Helper level for the Phase 5 Stage 2 goal (G-ex₂) (decision D-57): `vertexZeroInput` proves
`QED.GradedProof.GEx2.VertexZeroInput P Φ D f` for every flavour `f`, every counterterm data `D`,
loop masses at least `m₀ > 0`, positive photon regulators and the total Pauli–Villars conditions.

* The order-`5` vertex of flavour `f` is the order-`5` vertex (F₉) at `vParams` plus a real
  multiple of the tree (`GEx2.vertexPart_two_eq_vParams`).
* (F₉) is a real combination of T1 vertices at T1 parameter sets whose loop masses are at least
  `m₀` (`V5Zero.Split.vertexOrderFive_split`), each with an `ε → 0⁺` limit (relaxed T1 limit,
  `V5Zero.Lim`), so the sandwiched vertex converges to the sandwiched combination `combV`.
* `combV` is covariant under spinor lifts (`V5Zero.Lim.conj_vertexLimit_map`) and `♯`-fixed
  (`V5Zero.Sharp.sharp_vertexLimit`, real weights), so between on-shell spinors it is `c γ^μ`
  with one real `c` (`V5Zero.Dirac.exists_real_sandwich_eq_of_cov`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.V5Zero

open QED.Graded
open QED.WickModel (Params)

theorem sharp_combV {ι : Type*} [Fintype ι] {m₀ m : ℝ} {S : ι → Params} (a : ι → ℝ)
    (h : ∀ k, Adm m₀ (S k)) (hm : ∀ k, (S k).m = m) {p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) (μ : Fin 4) :
    SE2Real.sharp (combV S a p μ) = combV S a p μ := by
  simp only [combV, SE2Real.sharp_sum, SE2Real.sharp_smul, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpk : Minkowski.dot p p = -(S k).m ^ 2 := by rw [hm k]; exact hp
  rw [Sharp.sharp_vertexLimit (S k) (h k).hm₀ (h k).hm (h k).hmγ (h k).hΛ (h k).hM₁ (h k).hM₂
    (h k).hc₁ (h k).hc₂ hpk hpk hp0 hp0 (dot_sub_self p).ge (isLimit_limV (h k) hpk hp0) μ]

/-- **The vertex input of (G-ex₂)**: the order-`5` vertex of flavour `f` at `q = 0` tends to
`c · w γ^μ u` between on-shell spinors, for one real `c`. -/
theorem vertexZeroInput (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) :
    GEx2.VertexZeroInput P Φ D f := by
  classical
  set Φ' : Lepton.Flavors F := { Φ with openLine := f } with hΦ'
  set Q := GEx2.vParams P Φ D f with hQ
  obtain ⟨X, -, hmX, -, -, -, hXm, hX⟩ := Split.exists_aux Q.m Φ'.mass
  let S : Option F → Params := fun k => k.elim (Split.zParams Q X) (Split.gParams Q Φ' X)
  let a : Option F → ℝ := fun k => k.elim 1 (Split.weight Q Φ' X)
  have hmf : m₀ ≤ Q.m := hmass f
  have hadm : ∀ k, Adm m₀ (S k) := by
    rintro (_ | g)
    · exact ⟨hm₀, hmf, hmγ, hΛ, hmf, hmf.trans hmX.le, Split.zParams_PV₁ Q X,
      Split.zParams_PV₂ Q X⟩
    · exact ⟨hm₀, hmf, hmγ, hΛ, hmass g, hmf.trans hmX.le, Split.gParams_PV₁ Q Φ' X g,
        Split.gParams_PV₂ Q Φ' X g (hX g)⟩
  have hSm : ∀ k, (S k).m = Φ.mass f := by rintro (_ | _) <;> rfl
  obtain ⟨c, hc⟩ := Dirac.exists_real_sandwich_eq_of_cov (hm₀.trans_le (hmass f)) (combV S a)
    (fun L A B hL p hp hp0 hLp0 μ => cov_combV a hadm hSm hL hp hp0 hLp0 μ)
    (fun p hp hp0 μ => sharp_combV a hadm hSm hp hp0 μ)
  set t : ℝ := P.e ^ 4 * D.d₁ f 1 * P.e
  refine ⟨c + t, fun p hp hp0 μ u w hu hw => ?_⟩
  have key : ∀ ε : ℝ, 0 < ε → vertexPart { P with ε := ε } Φ D f 2 p p μ =
      (∑ k, (a k : ℂ) • QED.TwoLoop.vertexOrderFive { S k with ε := ε } p p μ) +
        (t : ℂ) • Dirac.gamma μ := by
    intro ε hε
    rw [GEx2.vertexPart_two_eq_vParams,
      show GEx2.vParams { P with ε := ε } Φ D f = { Q with ε := ε } from rfl,
      Split.vertexOrderFive_split (Q := { Q with ε := ε }) (Φ := Φ') (X := X) hε rfl hPV₁ hPV₂
        hXm hX p p μ, Fintype.sum_option]
    simp only [S, a, Option.elim, Complex.ofReal_one, one_smul]
    rfl
  have hT := (tendsto_combV a hadm hSm hp hp0 μ u w).add_const
    ((t : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u)))
  rw [hc p hp hp0 μ u w hu hw] at hT
  refine (hT.congr' ?_).trans_eq ?_
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [key ε hε, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul]
  · push_cast
    ring

end QED.GradedProof.V5Zero

end
