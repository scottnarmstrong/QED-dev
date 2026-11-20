/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1DVertex
public import QED.GradedProof.GEx2Inputs
public import QED.GradedProof.GEx2Affine
public import QED.GradedProof.V5ZeroTotal
public import QED.GradedProof.V5ZeroSplitVertex
public import QED.Frozen.Graded.IsRenormalizedThrough

/-!
# (X₁) piece D: the graded order-`5` vertex off the mass shell

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece D, for the graded vertex (G₈ᵥ) `QED.Graded.vertexPart … 2`.

* `exists_vertexPart_two_offShell`: for loop masses at least `m₀ > 0`, positive photon
  regulators, the total Pauli–Villars conditions and an on-shell positive-energy pair `(p', p)` of
  flavour `f` with `(p' - p)² ≥ 0`, the vertex at `x = (r', r)` near `(p', p)` converges as
  `ε → 0⁺` to `V x`, and `V` is continuous at `(p', p)`. Through
  `QED.GradedProof.GEx2.vertexPart_two_eq_vParams` and
  `QED.GradedProof.V5Zero.Split.vertexOrderFive_split` (both at all momenta) the vertex is a real
  combination of two-loop vertices plus a multiple of the tree, and each two-loop vertex is
  `QED.GradedProof.X1D.exists_vertexOrderFive_offShell`.
* `exists_vertexPart_two_offShell_self`: under the hypotheses of (X₁), the same at `(p, p)`, and
  `V (p, p)` vanishes between on-shell spinors (charge condition at `j = 2` of
  `IsRenormalizedThrough … 2` and uniqueness of limits).
-/

@[expose] public section

open Complex Filter Topology Matrix
open QED.Graded
open QED.WickModel (Params)

namespace QED.GradedProof.X1D

/-- **(X₁) piece D: the graded order-`5` vertex off the shell, with a continuous limit.** -/
theorem exists_vertexPart_two_offShell (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hPV₁ : ∑ g, Φ.coeff g = 0) (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0) {p' p : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -Φ.mass f ^ 2) (hp' : Minkowski.dot p' p' = -Φ.mass f ^ 2)
    (hp0 : 0 < p 0) (hp0' : 0 < p' 0) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    ∃ V : (Fin 4 → ℝ) × (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ᶠ x in 𝓝 (p', p), ∀ μ, Tendsto (fun ε => vertexPart { P with ε := ε } Φ D f 2 x.1 x.2 μ)
        (𝓝[>] 0) (𝓝 (V x μ))) ∧ ContinuousAt V (p', p) := by
  classical
  set Φ' : Lepton.Flavors F := { Φ with openLine := f } with hΦ'
  set Q := GEx2.vParams P Φ D f with hQ
  obtain ⟨X, -, hmX, -, -, -, hXm, hX⟩ := V5Zero.Split.exists_aux Q.m Φ'.mass
  let S : Option F → Params := fun k =>
    k.elim (V5Zero.Split.zParams Q X) (V5Zero.Split.gParams Q Φ' X)
  let a : Option F → ℝ := fun k => k.elim 1 (V5Zero.Split.weight Q Φ' X)
  have hmf : m₀ ≤ Q.m := hmass f
  have hadm : ∀ k, V5Zero.Adm m₀ (S k) := by
    rintro (_ | g)
    · exact ⟨hm₀, hmf, hmγ, hΛ, hmf, hmf.trans hmX.le, V5Zero.Split.zParams_PV₁ Q X,
        V5Zero.Split.zParams_PV₂ Q X⟩
    · exact ⟨hm₀, hmf, hmγ, hΛ, hmass g, hmf.trans hmX.le, V5Zero.Split.gParams_PV₁ Q Φ' X g,
        V5Zero.Split.gParams_PV₂ Q Φ' X g (hX g)⟩
  have hSm : ∀ k, (S k).m = Φ.mass f := by rintro (_ | _) <;> rfl
  have hpk : ∀ k, Minkowski.dot p p = -(S k).m ^ 2 := fun k => by rw [hSm k]; exact hp
  have hp'k : ∀ k, Minkowski.dot p' p' = -(S k).m ^ 2 := fun k => by rw [hSm k]; exact hp'
  choose W hW hWc using fun k => exists_vertexOrderFive_offShell (S k) (hadm k).hm₀ (hadm k).hm
    (hadm k).hmγ (hadm k).hΛ (hadm k).hM₁ (hadm k).hM₂ (hadm k).hc₁ (hadm k).hc₂ (hpk k)
    (hp'k k) hp0 hp0' hq
  set t : ℝ := P.e ^ 4 * D.d₁ f 1 * P.e
  refine ⟨fun x μ => ∑ k, (a k : ℂ) • W k x μ + (t : ℂ) • Dirac.gamma μ, ?_, ?_⟩
  · filter_upwards [eventually_all.2 hW] with x hx μ
    have key : ∀ ε : ℝ, 0 < ε → vertexPart { P with ε := ε } Φ D f 2 x.1 x.2 μ =
        (∑ k, (a k : ℂ) • QED.TwoLoop.vertexOrderFive { S k with ε := ε } x.1 x.2 μ) +
          (t : ℂ) • Dirac.gamma μ := by
      intro ε hε
      rw [GEx2.vertexPart_two_eq_vParams,
        show GEx2.vParams { P with ε := ε } Φ D f = { Q with ε := ε } from rfl,
        V5Zero.Split.vertexOrderFive_split (Q := { Q with ε := ε }) (Φ := Φ') (X := X) hε rfl
          hPV₁ hPV₂ hXm hX x.1 x.2 μ, Fintype.sum_option]
      simp only [S, a, Option.elim, Complex.ofReal_one, one_smul]
      rfl
    refine ((tendsto_finsetSum _ fun k _ => (hx k μ).const_smul (a k : ℂ)).add_const
      ((t : ℂ) • Dirac.gamma μ)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [key ε hε]
  · refine continuousAt_pi.2 fun μ => ?_
    exact (tendsto_finsetSum _ fun k _ => (continuousAt_pi.1 (hWc k) μ).const_smul
      (a k : ℂ)).add continuousAt_const

/-- **(X₁) piece D at `(p, p)`, with the charge condition.** Under the hypotheses of (X₁), the
graded order-`5` vertex of the open line at `x = (r', r)` near `(p, p)` converges as `ε → 0⁺` to
`V x`, `V` is continuous at `(p, p)`, and `V (p, p)` vanishes between on-shell spinors. -/
theorem exists_vertexPart_two_offShell_self (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hopen : rep Φ.openLine = Φ.openLine) (hD : IsRenormalizedThrough P Φ D rep 2)
    (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -Φ.mass Φ.openLine ^ 2) (hp0 : 0 < p 0) :
    ∃ V : (Fin 4 → ℝ) × (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ᶠ x in 𝓝 (p, p), ∀ μ, Tendsto
        (fun ε => vertexPart { P with ε := ε } Φ D Φ.openLine 2 x.1 x.2 μ) (𝓝[>] 0)
          (𝓝 (V x μ))) ∧ ContinuousAt V (p, p) ∧
      ∀ (μ : Fin 4) (u w : Fin 4 → ℂ),
        Dirac.slash p *ᵥ u = -((Φ.mass Φ.openLine : ℂ) • u) →
        w ᵥ* Dirac.slash p = -((Φ.mass Φ.openLine : ℂ) • w) →
        w ⬝ᵥ (V (p, p) μ *ᵥ u) = 0 := by
  have h₁ := GEx2.sum_eq_zero_of_blocks rep hrep Φ.coeff hPV₁
  have h₂ := GEx2.sum_eq_zero_of_blocks rep hrep (fun f => Φ.coeff f * Φ.mass f ^ 2) hPV₂
  have hq : 0 ≤ Minkowski.dot (p - p) (p - p) := by simp [sub_self, Minkowski.dot]
  obtain ⟨V, hV, hVc⟩ := exists_vertexPart_two_offShell P Φ D Φ.openLine m₀ hm₀ hmass hmγ hΛ
    h₁ h₂ hp hp hp0 hp0 hq
  refine ⟨V, hV, hVc, fun μ u w hu hw => ?_⟩
  have hcharge := ((hD.2 2 (by norm_num) le_rfl).1 Φ.openLine hopen).2 p hp hp0 μ u w hu hw
  have hlim : Tendsto (fun ε : ℝ => w ⬝ᵥ (vertexPart { P with ε := ε } Φ D Φ.openLine 2 p p μ *ᵥ
      u)) (𝓝[>] 0) (𝓝 (w ⬝ᵥ (V (p, p) μ *ᵥ u))) := by
    have hcont : Continuous fun A : Matrix (Fin 4) (Fin 4) ℂ => w ⬝ᵥ (A *ᵥ u) :=
      continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    exact (hcont.tendsto _).comp (hV.self_of_nhds μ)
  exact tendsto_nhds_unique hlim hcharge

end QED.GradedProof.X1D

end
