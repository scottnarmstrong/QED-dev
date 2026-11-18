/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroExplicitOpen
public import QED.TwoLoop.PauliZeroExplicitCt
public import QED.TwoLoop.PauliZeroLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The explicit Feynman-parameter form of the `q² → 0⁺` limit of the Pauli coefficient

Obligation O2-22 at fixed regulators (`docs/TWO-LOOP-DERIVATION.md`, section 5.4), explicit form.
`QED.TwoLoop.PauliZeroLimit.pauliZeroLimit P e` is the `q² → 0⁺` limit of the Pauli projection of
the `ε → 0⁺` limit of the order-`e⁵` vertex. This file proves

`pauliZeroLimit P e = 1/(64 e m⁵) · (1/i) · (∑_{c ∈ {L, X, C₊, C₋, S₊, S₋, VP}} σ_c Z_c + ∑_{c ∈ ct} Z_c)`

(`pauliZeroLimit_eq_explicit`), with `σ_c` the sign of the class (`-1` for `VP`, else `1`) and the
fourteen class values `Z_c` given by explicit Feynman-parameter integrals:

* `classZero c P` for the seven classes of five gauge vertices: `openZero c P` (six open-line
  classes, `∫_{Δ₇} c₂[N_c(x, ·)] / V_c(x)⁴`) and `vpZero P` (five pieces,
  `∑ₖ ∫_{Δ₉} c₂[N_{VP,k}(x, ·)] / V_{VP,k}(x)⁶`);
* `ctZero c P` for the seven counterterm classes: `d2InZero P`, `d2OutZero P` (product data,
  `∫_{Δ₇} … / V⁴ / auxLimit m`), `d3Zero P` for both `δ₃` slots (`∫_{Δ₈} … / V⁵ / auxLimit m`),
  and `d1Zero P = i δ₁ e (4m²)³ (e²/(8π²)) B(0) / m` for each of the three `δ₁` classes.

Here `N(x, u)` is the Pauli projection of the parametric numerator `T₁ + T₂ V + T₃ V²` of the class
along the curve `p'(u) = m((1+u²)/(1-u²), 2u/(1-u²), 0, 0)`, `p = (m, 0, 0, 0)`, `V(x)` the second
Symanzik function at `q = 0`, and `c₂ = secondCoeff` the second-order coefficient at `u = 0`
(`QED/TwoLoop/PauliZeroExplicitPiece.lean`). `pauliZeroLimit_eq_sum` writes the sums out.
-/

@[expose] public section

open Complex Matrix Filter Topology Set MeasureTheory
open scoped Real

namespace QED.TwoLoop.PauliZeroExplicit

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Relabel QED.TwoLoop.PauliZeroLimit

/-! ### The fourteen class values -/

/-- **The `q → 0` value of a class of five gauge vertices**: `vpZero P` for `VP`, `openZero c P`
otherwise. -/
noncomputable def classZero (c : Class5) (P : Params) : ℂ :=
  if c = .VP then vpZero P else openZero c P

/-- **The `q → 0` value of a counterterm class.** -/
noncomputable def ctZero : CtClass → Params → ℂ
  | .d2In, P => d2InZero P
  | .d2Out, P => d2OutZero P
  | .d3Slot0, P => d3Zero P
  | .d3Slot1, P => d3Zero P
  | .d1At1, P => d1Zero P
  | .d1At2, P => d1Zero P
  | .d1At3, P => d1Zero P

section Assembly

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁)
  (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
  (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)

include hm hmγ hΛ hM₁ hM₂ hc₁ hc₂

theorem tendsto_classNum_explicit {c : Class5} (hc : c ∈ Furry.nonFurry) :
    Tendsto (evenQuot (classNum P c)) (𝓝[≠] 0) (𝓝 (classZero c P)) := by
  by_cases hVP : c = .VP
  · subst hVP
    simp only [classZero, ite_true]
    exact tendsto_VP_explicit P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
  · simp only [classZero, hVP, ite_false]
    exact tendsto_open_explicit (VertexLimit.mem_openClasses_of_mem_nonFurry c hc hVP) P hm hmγ hΛ

omit hM₁ hM₂ hc₁ hc₂ in
theorem tendsto_ctNum_explicit (c : CtClass) :
    Tendsto (evenQuot (ctNum P c)) (𝓝[≠] 0) (𝓝 (ctZero c P)) := by
  cases c
  · exact tendsto_d2In_explicit P hm hmγ hΛ
  · exact tendsto_d2Out_explicit P hm hmγ hΛ
  · exact tendsto_d3Slot0_explicit P hm hmγ hΛ
  · have e : ctNum P .d3Slot1 = ctNum P .d3Slot0 := funext fun u => by
      simp only [ctNum, ctLimitV_d3Slot1_eq]
    rw [e]
    exact tendsto_d3Slot0_explicit P hm hmγ hΛ
  · exact tendsto_d1_explicit (Or.inl rfl) P hm hmγ hΛ
  · exact tendsto_d1_explicit (Or.inr (Or.inl rfl)) P hm hmγ hΛ
  · exact tendsto_d1_explicit (Or.inr (Or.inr rfl)) P hm hmγ hΛ

/-- The total of the fourteen class values, with the factor `1/i` of the vertex. -/
noncomputable def totalZero (P : Params) : ℂ :=
  (1 / I) * ((∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * classZero c P) + ∑ c : CtClass, ctZero c P)

/-- **`N(u)/u²` converges to the total of the class values.** -/
theorem tendsto_vertexNum_div_explicit :
    Tendsto (fun u => vertexNum P u / (u : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (totalZero P)) := by
  have hT := ((tendsto_finsetSum Furry.nonFurry fun c hc =>
    (tendsto_classNum_explicit P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hc).const_mul (c.sign : ℂ)).add
    (tendsto_finsetSum Finset.univ fun c _ =>
      tendsto_ctNum_explicit P hm hmγ hΛ c)).const_mul (1 / I)
  refine hT.congr' ?_
  have h0 : ∀ᶠ u in 𝓝[≠] (0 : ℝ), u ∈ Ioo (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [h0.and self_mem_nhdsWithin] with u ⟨hu, hu0⟩
  have hu' : -u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hu0' : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0
  have hev : vertexNum P (-u) = vertexNum P u :=
    pauliNum_vertexLimit_neg P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hu
  have e1 : vertexNum P u / (u : ℂ) ^ 2 = evenQuot (vertexNum P) u := by
    unfold evenQuot
    rw [hev]
    field_simp
    ring
  rw [e1]
  unfold evenQuot
  rw [vertexNum_eq P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hu, vertexNum_eq P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ hu']
  set D : ℂ := 2 * (u : ℂ) ^ 2
  have k1 : ∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * ((classNum P c u + classNum P c (-u)) / D) =
      ((∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * classNum P c u) +
        ∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * classNum P c (-u)) / D := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => by ring
  have k2 : ∑ c : CtClass, (ctNum P c u + ctNum P c (-u)) / D =
      ((∑ c : CtClass, ctNum P c u) + ∑ c : CtClass, ctNum P c (-u)) / D := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  rw [k1, k2]
  ring

/-- **The explicit form of the `q² → 0⁺` limit of the Pauli coefficient** (O2-22 at fixed
regulators): `pauliZeroLimit P e = 1/(64 e m⁵) · (1/i) · (∑_{c ∈ nonFurry} σ_c Z_c + ∑_{ct} Z_c)`,
with the explicit class values `Z_c` (`classZero`, `ctZero`). -/
theorem pauliZeroLimit_eq_explicit (e : ℝ) :
    pauliZeroLimit P e = 1 / (64 * (e : ℂ) * (P.m : ℂ) ^ 5) *
      ((1 / I) * ((∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * classZero c P) +
        ∑ c : CtClass, ctZero c P)) := by
  rw [pauliZeroLimit_eq P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ e,
    (tendsto_vertexNum_div_explicit P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂).limUnder_eq]
  have hm' : (P.m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
  unfold totalZero
  by_cases he : e = 0
  · subst he
    simp
  have he' : (e : ℂ) ≠ 0 := ofReal_ne_zero.mpr he
  field_simp

omit hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ in
/-- The signed sum over the seven classes of five gauge vertices, written out. -/
theorem sum_nonFurry_classZero :
    ∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * classZero c P =
      openZero .L P + openZero .X P + openZero .Cp P + openZero .Cm P + openZero .Sp P +
        openZero .Sm P - vpZero P := by
  simp only [Furry.nonFurry, classZero]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Class5.sign, reduceCtorEq, ite_false, ite_true, Int.cast_one, Int.cast_neg, one_mul,
    neg_mul]
  ring

omit hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ in
/-- The sum over the seven counterterm classes, written out. -/
theorem sum_ctZero :
    ∑ c : CtClass, ctZero c P = d2InZero P + d2OutZero P + 2 * d3Zero P + 3 * d1Zero P := by
  have h : (Finset.univ : Finset CtClass) =
      {.d2In, .d2Out, .d3Slot0, .d3Slot1, .d1At1, .d1At2, .d1At3} := rfl
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [ctZero]
  ring

/-- **The explicit form, written out over the fourteen classes**:
`pauliZeroLimit P e = 1/(64 e m⁵) · (1/i) · (Z_L + Z_X + Z_{C₊} + Z_{C₋} + Z_{S₊} + Z_{S₋} - Z_{VP}
+ Z_{δ₂ in} + Z_{δ₂ out} + 2 Z_{δ₃} + 3 Z_{δ₁})`. -/
theorem pauliZeroLimit_eq_sum (e : ℝ) :
    pauliZeroLimit P e = 1 / (64 * (e : ℂ) * (P.m : ℂ) ^ 5) * ((1 / I) *
      (openZero .L P + openZero .X P + openZero .Cp P + openZero .Cm P + openZero .Sp P +
        openZero .Sm P - vpZero P + d2InZero P + d2OutZero P + 2 * d3Zero P + 3 * d1Zero P)) := by
  rw [pauliZeroLimit_eq_explicit P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ e, sum_nonFurry_classZero,
    sum_ctZero]
  ring

end Assembly

end QED.TwoLoop.PauliZeroExplicit

end
