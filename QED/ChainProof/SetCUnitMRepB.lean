/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMScale
public import QED.ChainProof.SetCUnitMPauliBd
public import QED.ChainProof.SetCLinkReps
public import QED.TwoLoop.ParametricBridgeLX

/-!
# The bubble classes of set (c) as multi-denominator units

Helper level for set (c) (stage L2, consumer side). Two pieces for the classes
`QED.ChainProof.SetCLink.repB i` (a two-loop vertex skeleton with the one-loop bubble on one
photon line, the element line).

**The relabelling** (kernel evaluation, all twelve skeletons). The open line of `repB i` runs
`Ψ(x) → 0 → 1 → ⋯ → 4`, that of `Class5.rep c` the other way, so the vertex `t` of the class
representative is the vertex `4 - t` of `repB i` (`Fin.rev`); with the bubble vertices `5, 6`
bypassed, the photon pairing of `repB i` is that of `Class5.rep (repBClass i)`:

| `i` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
| --- | - | - | - | - | - | - | - | - | - | - | -- | -- |
| class | `L` | `L` | `X` | `X` | `C₋` | `C₋` | `S₋` | `S₋` | `C₊` | `C₊` | `S₊` | `S₊` |
| element slot | 4 | 5 | 5 | 4 | 5 | 4 | 4 | 5 | 5 | 4 | 4 | 5 |

(the element slot is the line index `lineIdx` of the class line carrying the bubble, `4` for the
photon line through the vertex `0` of the class). This corrects the table of the stage L1 notes,
which read the vertices of `repB i` as those of the class without the reversal: only the ladder
skeletons `i = 0, 1` are unaffected.

* `repBClass`, `repBSlot`, `repBLow`; `embFB`, `embPB` (the vertex maps), `bypassB`;
* **`repB_sigma`**, **`repB_tau_bypass`**: the fermion and the bypassed photon pairings;
* `repBElemLine`, **`lineIdx_repBElemLine`**, `repB_elem_bubble`: the element line of the class
  representative, its line index, and the bubble on it.

**The transverse term as a unit.** The element line carries the four photon-type denominators
`(m_γ, Λ, m_γ, Λ)`, the spectral factor `M² + x(1-x)k² - iε` and `(k²)²`: the
multi-denominator unit with extras `[spectral, m_γ, Λ]` (`r = 3`), scales `[√(x(1-x)), 1, 1]`,
`n = 2`, both photon pairs `(m_γ, Λ)`.

* `repBKappa`, `repBExtra`; `trailOne_repBKappa`, `extraGe_repB`;
* `lineDenom_repB_spectral`, `lineDenom_repB_one`, `lineDenom_repB_two`: the extra lines;
* **`unitM_repB`**: integrability at every `ε > 0` and the `ε → 0⁺` limit;
* **`unitMLimitV_repB_eq`**: the limit is `(x(1-x))⁻¹` times the unscaled unit with masses
  `[specMu M x, m_γ, Λ]` (a dispersion line of mass `√(M²/(x(1-x)))`);
* **`norm_unitMLimitV_repB_le`**, **`continuousOn_unitMLimitV_repB`**: a bound uniform in
  `x ∈ (0, 1)` and the masses, and continuity in `x`;
* `unitMPauliS_descale`, `unitMPauliZeroPow_descale`: removing a scale from the Pauli values;
* **`tendsto_formFactorProj₂_repB`**, **`unitMPauliZeroPow_repB_eq`**,
  **`norm_unitMPauliZeroPow_repB_le`**: the `q² → 0⁺` Pauli limit, its dispersion form and a
  bound `C (1 + ∑ᵢ Mᵢ²)⁴` uniform in the masses (`Mᵢ` the masses of the unscaled unit).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.ClassLimit QED.ChainProof.SetCUnit QED.ChainProof.SetCLink
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit
open QED.TwoLoop.VPHalfAtAssembly (fDen specMu mem_Ioo_mul_pos mul_one_sub_le_one)
open QED.Integration.TwoLoop (lineDenom pvLines)

/-! ### The relabelling -/

/-- The class of the skeleton of `repB i`. -/
def repBClass : Fin 12 → Class5 := ![.L, .L, .X, .X, .Cm, .Cm, .Sm, .Sm, .Cp, .Cp, .Sp, .Sp]

/-- The unit slot of the element line of `repB i`. -/
def repBSlot : Fin 12 → Fin 8 := ![4, 5, 5, 4, 5, 4, 4, 5, 5, 4, 4, 5]

/-- The lower vertex (in the class labels) of the element line of `repB i`. -/
def repBLow : Fin 12 → Fin 5 := ![0, 1, 1, 0, 1, 0, 0, 1, 2, 0, 0, 2]

/-- The fermion fields of the class representative inside those of `repB i`: vertex `t` of the
class is vertex `4 - t` of `repB i`. -/
def embFB : Fin 1 ⊕ Wick.FermionVertex (gauges 5) → Fin 1 ⊕ Wick.FermionVertex kB
  | .inl a => .inl a
  | .inr v => .inr (fvB (Fin.castLE (by norm_num) (Fin.rev v.1)))

/-- The photon fields of the class representative inside those of `repB i`. -/
def embPB : Fin 1 ⊕ Wick.PhotonSlot (gauges 5) → Fin 1 ⊕ Wick.PhotonSlot kB
  | .inl a => .inl a
  | .inr y => .inr (plB (Fin.rev y.1))

/-- A photon pairing of `kB` with the path through the bubble fields `5`, `6` bypassed. -/
def bypassB (τ : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot kB)) (x : Fin 1 ⊕ Wick.PhotonSlot kB) :
    Fin 1 ⊕ Wick.PhotonSlot kB :=
  if τ x = .inr (pgB 5) then τ (.inr (pgB 6)) else
    if τ x = .inr (pgB 6) then τ (.inr (pgB 5)) else τ x

theorem repBClass_mem : ∀ i, repBClass i ∈ openClasses := by decide

theorem four_le_repBSlot : ∀ i, 4 ≤ (repBSlot i : ℕ) := by decide

/-- **The fermion pairing**: the open line of `repB i` is that of the class representative,
vertex `t` of the class being vertex `4 - t` of `repB i`. -/
theorem repB_sigma : ∀ i x, (repB i).1.1 (embFB x) = embFB ((repBClass i).rep.1.1 x) := by
  decide +kernel

/-- **The photon pairing**: with the bubble bypassed, the photon pairing of `repB i` is that of
the class representative. -/
theorem repB_tau_bypass : ∀ i x,
    bypassB (repB i).1.2 (embPB x) = embPB ((repBClass i).rep.1.2 x) := by
  decide +kernel

theorem repBLow_spec : ∀ i, ∃ b, (repBClass i).rep.1.2 (.inr (ps5 (repBLow i))) = .inr b ∧
    Wick.photonKey (ps5 (repBLow i)) < Wick.photonKey b := by
  decide +kernel

/-- The element line of `repB i` as a photon line of the class representative. -/
def repBElemLine (i : Fin 12) : PhotonLine (repBClass i).rep := ⟨ps5 (repBLow i), repBLow_spec i⟩

/-- **The element line is the line of the unit slot**: its line index is `pvLines (repBSlot i)`. -/
theorem lineIdx_repBElemLine : ∀ i,
    lineIdx (.inr (repBElemLine i) : Line (repBClass i).rep) = pvLines (repBSlot i) := by
  decide +kernel

/-- The bubble sits on the element line. -/
theorem repB_elem_bubble : ∀ i,
    (repB i).1.2 (embPB (.inr (ps5 (repBLow i)))) = .inr (pgB 5) ∨
      (repB i).1.2 (embPB (.inr (ps5 (repBLow i)))) = .inr (pgB 6) := by
  decide +kernel

/-- The ladder skeletons: `repB 0`, `repB 1` are the class `L` with the element on the photon
line `0 — 4` (slot `4`) and `1 — 3` (slot `5`). -/
theorem repB_ladder : repBClass 0 = .L ∧ repBClass 1 = .L ∧ repBSlot 0 = 4 ∧ repBSlot 1 = 5 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Removing a scale from the Pauli values -/

section PauliScale

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
include hc hm hs hμ₀ hM

theorem unitMPauliS_descale {r n : ℕ} {κ cs : Fin r → ℝ} (hnr : n ≤ r) (hT : TrailOne n κ)
    (hX : ExtraGe μ₀ κ cs) (e : Fin r) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    unitMPauliS c P s κ (unitMMasses P.m a A b B cs) n u =
      ((κ e ^ 2 : ℝ) : ℂ)⁻¹ * unitMPauliS c P s (Function.update κ e 1)
        (unitMMasses P.m a A b B (Function.update cs e (cs e / κ e))) n u := by
  have hq := (dot_curveMomentum_sub P.m hu).symm ▸ curveQ_nonneg P.m hu
  unfold unitMPauliS
  simp only [pauliNum_eq_sum_idx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [unitMLimitV_descale hc P hm hs hμ₀ hM (dot_restMomentum (m := P.m))
    (dot_curveMomentum P.m hu) hq hnr hT hX e]
  ring

/-- **Removing a scale from the `q → 0` value**: `Z(κ, cs) = κₑ⁻² Z(κ[e ↦ 1], cs[e ↦ csₑ/κₑ])`. -/
theorem unitMPauliZeroPow_descale {r n : ℕ} {κ cs : Fin r → ℝ} (hnr : n ≤ r)
    (hT : TrailOne n κ) (hX : ExtraGe μ₀ κ cs) (e : Fin r) :
    unitMPauliZeroPow c P s κ (unitMMasses P.m a A b B cs) n =
      ((κ e ^ 2 : ℝ) : ℂ)⁻¹ * unitMPauliZeroPow c P s (Function.update κ e 1)
        (unitMMasses P.m a A b B (Function.update cs e (cs e / κ e))) n := by
  have h' := tendsto_unitMPauliS_div_pow hc P hm hs hμ₀ hM n hnr (hT.update_one e)
    (hX.update_one hμ₀ e)
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hlim : Tendsto (fun u => unitMPauliS c P s κ (unitMMasses P.m a A b B cs) n u / (u : ℂ) ^ 2)
      (𝓝[≠] 0) (𝓝 (((κ e ^ 2 : ℝ) : ℂ)⁻¹ * unitMPauliZeroPow c P s (Function.update κ e 1)
        (unitMMasses P.m a A b B (Function.update cs e (cs e / κ e))) n)) := by
    refine (h'.const_mul _).congr' ?_
    filter_upwards [h0] with u hu
    rw [unitMPauliS_descale hc P hm hs hμ₀ hM hnr hT hX e hu, mul_div_assoc]
  unfold unitMPauliZeroPow
  rw [hlim.limUnder_eq]
  rfl

end PauliScale

/-! ### The transverse term of `repB` -/

/-- The scales of the extra lines: the spectral line `√(x(1-x))`, then two unscaled lines. -/
noncomputable def repBKappa (x : ℝ) : Fin 3 → ℝ := ![√(x * (1 - x)), 1, 1]

/-- The masses of the extra lines: the spectral mass `M`, then `m_γ`, `Λ`. -/
def repBExtra (M mγ Λ : ℝ) : Fin 3 → ℝ := ![M, mγ, Λ]

theorem trailOne_repBKappa (x : ℝ) : TrailOne 2 (repBKappa x) := fun j hj => by
  fin_cases j
  · simp at hj
  · rfl
  · rfl

theorem extraGe_repB {μ₀ x M mγ Λ : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hM : μ₀ ≤ M) (hmγ : μ₀ ≤ mγ)
    (hΛ : μ₀ ≤ Λ) : ExtraGe μ₀ (repBKappa x) (repBExtra M mγ Λ) := fun j => by
  fin_cases j
  · refine ⟨Real.sqrt_pos.2 (mem_Ioo_mul_pos hx), ?_, hM⟩
    exact Real.sqrt_le_one.mpr (mul_one_sub_le_one hx)
  · exact ⟨one_pos, le_rfl, hmγ⟩
  · exact ⟨one_pos, le_rfl, hΛ⟩

theorem update_repBKappa (x : ℝ) : Function.update (repBKappa x) 0 1 = fun _ => 1 := by
  funext j
  fin_cases j <;> simp [repBKappa]

theorem update_repBExtra (M mγ Λ w : ℝ) :
    Function.update (repBExtra M mγ Λ) 0 w = repBExtra w mγ Λ := by
  funext j
  fin_cases j <;> simp [repBExtra]

section Lines

variable (c : Class5) (s : Fin 8) (p p' : Fin 4 → ℝ) (m a A b B M mγ Λ ε : ℝ)
  (ℓ : Fin 2 → Fin 4 → ℝ)

/-- **The spectral line**: `D₈ = fDen M ε x k = M² + x(1-x)k² - iε`. -/
theorem lineDenom_repB_spectral {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    lineDenom (unitMMatrix c s (repBKappa x)) (unitMMomenta c s (repBKappa x) p p')
        (unitMMasses m a A b B (repBExtra M mγ Λ)) ε (mExtra 3 0) ℓ =
      fDen M ε x (elemMom c s p p' ℓ) :=
  lineDenom_unitM_spectral c s p p' m a A b B ε hx rfl rfl ℓ

/-- The photon-type extra line `D₉ = k² + m_γ² - iε`. -/
theorem lineDenom_repB_one (x : ℝ) :
    lineDenom (unitMMatrix c s (repBKappa x)) (unitMMomenta c s (repBKappa x) p p')
        (unitMMasses m a A b B (repBExtra M mγ Λ)) ε (mExtra 3 1) ℓ =
      ((Minkowski.dot (elemMom c s p p' ℓ) (elemMom c s p p' ℓ) + mγ ^ 2 : ℝ) : ℂ) -
        (ε : ℂ) * I := by
  rw [lineDenom_unitM_mExtra]
  simp [repBKappa, repBExtra]

/-- The photon-type extra line `D₁₀ = k² + Λ² - iε`. -/
theorem lineDenom_repB_two (x : ℝ) :
    lineDenom (unitMMatrix c s (repBKappa x)) (unitMMomenta c s (repBKappa x) p p')
        (unitMMasses m a A b B (repBExtra M mγ Λ)) ε (mExtra 3 2) ℓ =
      ((Minkowski.dot (elemMom c s p p' ℓ) (elemMom c s p p' ℓ) + Λ ^ 2 : ℝ) : ℂ) -
        (ε : ℂ) * I := by
  rw [lineDenom_unitM_mExtra]
  simp [repBKappa, repBExtra]

end Lines

section RepB

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ mγ Λ : ℝ} (hμ₀ : 0 < μ₀) (hmγ : μ₀ ≤ mγ) (hΛ : μ₀ ≤ Λ)
include hc hm hs hμ₀ hmγ hΛ

omit hc hm hs hμ₀ in
theorem massesGe_repB : MassesGe μ₀ mγ Λ mγ Λ := ⟨hmγ, hΛ, hmγ, hΛ⟩

variable {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
  (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))

include hp hp' hq in
/-- **The `ε → 0⁺` limit of the transverse unit of `repB`**: integrable at both stages for every
`ε > 0`, convergent as `ε → 0⁺`. -/
theorem unitM_repB {x M : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hM : μ₀ ≤ M) :
    (∀ ε, 0 < ε → ∀ μ i j, QED.TwoLoop.jointEnergyFirstIntegrable 2
      (unitMIntegrand c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p'
        2 μ i j)) ∧
    ∀ μ i j, Tendsto (fun ε => unitMValue c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) ε p p' 2 μ i j) (𝓝[>] 0)
      (𝓝 (unitMLimitV c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) p p' 2
        μ i j)) :=
  unitM_pow hc P hm hs hμ₀ (massesGe_repB hmγ hΛ) hp hp' hq 2 (by norm_num)
    (trailOne_repBKappa x) (extraGe_repB hx hM hmγ hΛ)

include hp hp' hq in
/-- **The dispersion form**: the limit is `(x(1-x))⁻¹` times the unscaled unit with extra masses
`[specMu M x, m_γ, Λ]`. -/
theorem unitMLimitV_repB_eq {x M : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hM : μ₀ ≤ M) (μ i j : Fin 4) :
    unitMLimitV c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) p p' 2 μ i j =
      ((x * (1 - x) : ℝ) : ℂ)⁻¹ * unitMLimitV c P s (fun _ => 1)
        (unitMMasses P.m mγ Λ mγ Λ (repBExtra (specMu M x) mγ Λ)) p p' 2 μ i j := by
  rw [unitMLimitV_spectral hc P hm hs hμ₀ (massesGe_repB hmγ hΛ) hp hp' hq (by norm_num)
    (trailOne_repBKappa x) (extraGe_repB hx hM hmγ hΛ) (e := 0) hx rfl μ i j,
    update_repBKappa, update_repBExtra]
  rfl

end RepB

/-- **A bound uniform in `x` and the masses**: one constant `C` with
`‖L‖ ≤ (x(1-x))⁻¹ C (1 + specMu(M, x)² + m_γ² + Λ²)²` for `x ∈ (0, 1)` and all masses `≥ μ₀`. -/
theorem norm_unitMLimitV_repB_le {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ i j : Fin 4) :
    ∃ C : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, ∀ M mγ Λ : ℝ, μ₀ ≤ M → μ₀ ≤ mγ → μ₀ ≤ Λ →
      ‖unitMLimitV c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) p p' 2
          μ i j‖ ≤
        (x * (1 - x))⁻¹ * (C * (1 + (specMu M x ^ 2 + mγ ^ 2 + Λ ^ 2)) ^ 2) := by
  obtain ⟨C, hC⟩ := norm_unitMLimitV_pow_le hc P hm hs hμ₀ hp hp' hq μ i j 2 (r := 3)
    (κ := fun _ => 1) (by norm_num) (fun _ _ => rfl) fun _ => ⟨one_pos, le_rfl⟩
  refine ⟨C, fun x hx M mγ Λ hM hmγ hΛ => ?_⟩
  have h0 := mem_Ioo_mul_pos hx
  rw [unitMLimitV_repB_eq hc P hm hs hμ₀ hmγ hΛ hp hp' hq hx hM μ i j, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg h0.le]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 h0.le)
  have h := hC mγ Λ mγ Λ (repBExtra (specMu M x) mγ Λ) (massesGe_repB hmγ hΛ) fun j => by
    fin_cases j
    · exact hM.trans (QED.TwoLoop.VPHalfAtAssembly.specMu_ge (hμ₀.trans_le hM) hx)
    · exact hmγ
    · exact hΛ
  simpa [Fin.sum_univ_three, repBExtra, add_assoc] using h

/-- **Continuity in the Feynman parameter**: `x ↦ L(x)` is continuous on `(0, 1)`. -/
theorem continuousOn_unitMLimitV_repB {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ M mγ Λ : ℝ} (hμ₀ : 0 < μ₀) (hM : μ₀ ≤ M)
    (hmγ : μ₀ ≤ mγ) (hΛ : μ₀ ≤ Λ) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (μ i j : Fin 4) :
    ContinuousOn (fun x => unitMLimitV c P s (repBKappa x)
      (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) p p' 2 μ i j) (Ioo 0 1) := by
  refine continuousOn_unitMLimitV_descale hc P hm hs hμ₀ hp hp' hq continuousOn_const
    continuousOn_const continuousOn_const continuousOn_const
    (fun _ _ => massesGe_repB hmγ hΛ) μ i j (r := 3) (n := 2) (by norm_num)
    (κ := repBKappa) (cs := fun _ => repBExtra M mγ Λ) (fun e => ?_)
    (fun _ => continuousOn_const) (fun x _ => trailOne_repBKappa x)
    (fun x hx => extraGe_repB hx hM hmγ hΛ)
  fin_cases e
  · exact (Real.continuous_sqrt.comp (continuous_id.mul (continuous_const.sub continuous_id)))
      |>.continuousOn
  · exact continuousOn_const
  · exact continuousOn_const

section RepBPauli

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ mγ Λ : ℝ} (hμ₀ : 0 < μ₀) (hmγ : μ₀ ≤ mγ) (hΛ : μ₀ ≤ Λ)
include hc hm hs hμ₀ hmγ hΛ

/-- **The `q² → 0⁺` Pauli limit of the transverse unit of `repB`.** -/
theorem tendsto_formFactorProj₂_repB {x M : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hM : μ₀ ≤ M) (e : ℝ) :
    Tendsto (fun Q => QED.OneLoop.formFactorProj₂ e P.m (boostMomentum P.m Q) (restMomentum P.m)
        (unitMLimitV c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ))
          (restMomentum P.m) (boostMomentum P.m Q) 2))
      (𝓝[>] 0) (𝓝 (unitMPauliZeroPow c P s (repBKappa x)
        (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2 / (64 * (e : ℂ) * (P.m : ℂ) ^ 5))) :=
  tendsto_formFactorProj₂_unitM hc P hm hs hμ₀ (massesGe_repB hmγ hΛ) (by norm_num)
    (trailOne_repBKappa x) (extraGe_repB hx hM hmγ hΛ) e

/-- **The dispersion form of the Pauli value**: `(x(1-x))⁻¹` times the value of the unscaled unit
with extra masses `[specMu M x, m_γ, Λ]`. -/
theorem unitMPauliZeroPow_repB_eq {x M : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hM : μ₀ ≤ M) :
    unitMPauliZeroPow c P s (repBKappa x) (unitMMasses P.m mγ Λ mγ Λ (repBExtra M mγ Λ)) 2 =
      ((x * (1 - x) : ℝ) : ℂ)⁻¹ * unitMPauliZeroPow c P s (fun _ => 1)
        (unitMMasses P.m mγ Λ mγ Λ (repBExtra (specMu M x) mγ Λ)) 2 := by
  have h0 := mem_Ioo_mul_pos hx
  rw [unitMPauliZeroPow_descale hc P hm hs hμ₀ (massesGe_repB hmγ hΛ) (by norm_num)
    (trailOne_repBKappa x) (extraGe_repB hx hM hmγ hΛ) 0, update_repBKappa]
  have hk : repBKappa x 0 = √(x * (1 - x)) := rfl
  have hc0 : repBExtra M mγ Λ 0 = M := rfl
  rw [hk, hc0, Real.sq_sqrt h0.le, div_sqrt_eq_specMu (hμ₀.le.trans hM) hx, update_repBExtra]

end RepBPauli

/-- **The Pauli value of the unscaled `repB` unit, bounded uniformly in the masses**: one
constant `C` with `‖Z‖ ≤ C (1 + ∑ᵢ Mᵢ²)⁴` for all extra masses `[t, m_γ, Λ]` with
`t, m_γ, Λ ≥ μ₀` (`Mᵢ` the masses of the `11` lines). With `unitMPauliZeroPow_repB_eq`, the
`repB` value at `x` is `(x(1-x))⁻¹` times such a value at `t = specMu M x`. -/
theorem norm_unitMPauliZeroPow_repB_le {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (hm : 0 < P.m) {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    ∃ C : ℝ, ∀ t mγ Λ : ℝ, μ₀ ≤ t → μ₀ ≤ mγ → μ₀ ≤ Λ →
      ‖unitMPauliZeroPow c P s (fun _ : Fin 3 => 1)
          (unitMMasses P.m mγ Λ mγ Λ (repBExtra t mγ Λ)) 2‖ ≤
        C * (1 + ∑ i, unitMMasses P.m mγ Λ mγ Λ (repBExtra t mγ Λ) i ^ 2) ^ (2 + 2) := by
  obtain ⟨C, hC⟩ := norm_unitMPauliZeroPow_le hc P hm hs hμ₀ 2 (r := 3) (κ := fun _ => 1)
    (by norm_num) (fun _ _ => rfl) fun _ => ⟨one_pos, le_rfl⟩
  refine ⟨C, fun t mγ Λ ht hmγ hΛ => ?_⟩
  refine hC mγ Λ mγ Λ _ (massesGe_repB hmγ hΛ) fun j => ?_
  fin_cases j
  · exact ht
  · exact hmγ
  · exact hΛ

end QED.ChainProof.SetCUnitM

end
