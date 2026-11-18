/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.PauliZeroExplicit
public import QED.TwoLoop.CountertermScaling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The regulated `[e⁴] F₂(0)` and its five units

Sections 5.2 and 5.6 of `docs/TWO-LOOP-DERIVATION.md`; section 8 of `docs/TWO-LOOP-UNITS.md`.

**The charge dependence.** With counterterms `δᵢ = e² dᵢ` (O2-27), the order-exactly-5 vertex is
`e⁵` times the vertex at `e = 1` with counterterms `dᵢ`
(`QED.TwoLoop.Scaling.onePIFunction₂_five_sub_four`), so its `ε → 0⁺` limit scales in the same way
(`vertexLimitAt_scale`), and the Pauli projection, which carries `1/e`, gives
`pauliZeroLimit P e = (e_P⁵ / e) · pauliZeroLimit P₁ 1` with `P₁ = atUnitCharge P d₁ d₂ d_m d₃`
(`pauliZeroLimit_scale`). Hence at `e = e_P ≠ 0`,

`pauliZeroLimit P e / e⁴ = pauliZeroFour P d₁ d₂ d_m d₃`

(`pauliZeroLimit_div_pow_four`), a number that does not involve the charge
(`pauliZeroFour_charge`): the regulated coefficient `[e⁴] F₂(0) = F₂⁽⁴⁾(0; m_γ, Λ, M₁, M₂)` of
section 5.6. With the counterterms fixed by the frozen conditions (Z₅), (Z₈), (K₀) at charge `e`
and at charge `1` (`pauliZeroLimit_eq_pow_four_mul_of_conditions`), the numbers `dᵢ` are unique
(`pauliZeroFour_eq_of_conditions`), so the coefficient is a function of the regulators alone.

**The units** (section 5.2). The fourteen classes group into five units, each a graph class with
its counterterm insertions (`unitZero`):

| unit | classes | value |
| --- | --- | --- |
| `VP` | `VP`, `δ₃` (two slots) | `-Z_{VP} + 2 Z_{δ₃}` |
| `S` | `S₊`, `S₋`, `δ₂ in`, `δ₂ out` | `Z_{S₊} + Z_{S₋} + Z_{δ₂ in} + Z_{δ₂ out}` |
| `C` | `C₊`, `C₋`, `δ₁` at `v₁`, `v₃` | `Z_{C₊} + Z_{C₋} + 2 Z_{δ₁}` |
| `L` | ladder, `δ₁` at the external vertex `v₂` | `Z_L + Z_{δ₁}` |
| `X` | crossed ladder | `Z_X` |

with the explicit Feynman-parameter values `Z` of `QED/TwoLoop/PauliZeroExplicit.lean`. The unit's
contribution to the Pauli coefficient at charge `1` is `unitF2 U P = (1/(64 m⁵)) (1/i) unitZero U P`,
and `pauliZeroFour P d = ∑_U unitF2 U P₁` (`pauliZeroFour_eq_sum_units`): each unit is a separate
explicit function of the regulators and of the `dᵢ`, the object on which the regulator limits
(O2-17, O2-19, O2-23) act.
-/

@[expose] public section

open Complex Matrix Filter Topology Set
open scoped Real

namespace QED.TwoLoop.UnitsRegulated

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.Enumeration QED.TwoLoop.Relabel

/-! ### The charge dependence -/

/-- The parameters at charge `1` with counterterms `dᵢ`, all regulators unchanged. -/
def atUnitCharge (P : Params) (d₁ d₂ dm d₃ : ℝ) : Params :=
  { P with e := 1, δ₁ := d₁, δ₂ := d₂, δm := dm, δ₃ := d₃ }

section Scaling

variable (P : Params) {d₁ d₂ dm d₃ : ℝ}
  (h₁ : P.δ₁ = P.e ^ 2 * d₁) (h₂ : P.δ₂ = P.e ^ 2 * d₂) (hδm : P.δm = P.e ^ 2 * dm)
  (h₃ : P.δ₃ = P.e ^ 2 * d₃)
include h₁ h₂ hδm h₃

/-- **The order-`e⁵` vertex at `δᵢ = e² dᵢ`** is `e⁵` times the vertex at `e = 1`, at every `ε`. -/
theorem vertexOrderFive_scale (ε : ℝ) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    vertexOrderFive { P with ε := ε } p' p μ =
      (P.e : ℂ) ^ 5 • vertexOrderFive { atUnitCharge P d₁ d₂ dm d₃ with ε := ε } p' p μ := by
  ext i j
  have h := QED.TwoLoop.Scaling.onePIFunction₂_five_sub_four { P with ε := ε } h₁ h₂ hδm h₃
    (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)
  simp only [vertexOrderFive, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [h]
  simp only [atUnitCharge]
  ring

/-- **The `ε → 0⁺` limit of the vertex at `δᵢ = e² dᵢ`** is `e⁵` times the limit at `e = 1`, when
the latter exists. -/
theorem vertexLimitAt_scale {p' p : Fin 4 → ℝ}
    (hV : IsVertexOrderFiveLimit (atUnitCharge P d₁ d₂ dm d₃) p' p
      (vertexLimitAt (atUnitCharge P d₁ d₂ dm d₃) p' p)) :
    vertexLimitAt P p' p = fun μ => (P.e : ℂ) ^ 5 • vertexLimitAt (atUnitCharge P d₁ d₂ dm d₃) p' p μ := by
  funext μ
  ext i j
  have hT : Tendsto (fun ε => vertexOrderFive { P with ε := ε } p' p μ i j) (𝓝[>] 0)
      (𝓝 ((P.e : ℂ) ^ 5 * vertexLimitAt (atUnitCharge P d₁ d₂ dm d₃) p' p μ i j)) := by
    refine ((hV μ i j).const_mul ((P.e : ℂ) ^ 5)).congr fun ε => ?_
    rw [vertexOrderFive_scale P h₁ h₂ hδm h₃ ε p' p μ, Matrix.smul_apply, smul_eq_mul]
  simp only [vertexLimitAt, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at hT ⊢
  exact hT.limUnder_eq

omit h₁ h₂ hδm h₃ in
/-- The Pauli projection carries `1/e`. -/
theorem formFactorProj₂_smul (e m : ℝ) (p' p : Fin 4 → ℝ) (a : ℂ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    QED.OneLoop.formFactorProj₂ e m p' p (fun μ => a • V μ) =
      a / e * QED.OneLoop.formFactorProj₂ 1 m p' p V := by
  rw [formFactorProj₂_eq_pauliNum, formFactorProj₂_eq_pauliNum, pauliNum_smul]
  by_cases he : (e : ℂ) = 0
  · simp [he]
  · push_cast
    field_simp

variable (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂)
  (hc₁ : 1 + P.c₁ + P.c₂ = 0) (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
include hm hmγ hΛ hM₁ hM₂ hc₁ hc₂

theorem pauliAt_scale (e : ℝ) {Q : ℝ} (hQ : 0 ≤ Q) :
    pauliAt P e Q = (P.e : ℂ) ^ 5 / e * pauliAt (atUnitCharge P d₁ d₂ dm d₃) 1 Q := by
  have hV := isVertexOrderFiveLimit_pauliAt (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
    hQ
  have hm1 : (atUnitCharge P d₁ d₂ dm d₃).m = P.m := rfl
  rw [hm1] at hV
  unfold pauliAt
  rw [hm1, vertexLimitAt_scale P h₁ h₂ hδm h₃ hV, formFactorProj₂_smul]

/-- **The charge dependence of the `q² → 0⁺` limit**:
`pauliZeroLimit P e = (e_P⁵ / e) · pauliZeroLimit P₁ 1` with `P₁ = atUnitCharge P d₁ d₂ d_m d₃`,
for counterterms `δᵢ = e_P² dᵢ`. -/
theorem pauliZeroLimit_scale (e : ℝ) :
    pauliZeroLimit P e =
      (P.e : ℂ) ^ 5 / e * pauliZeroLimit (atUnitCharge P d₁ d₂ dm d₃) 1 := by
  have hT := (tendsto_pauliZeroLimit (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
    1).const_mul ((P.e : ℂ) ^ 5 / e)
  have hT' : Tendsto (pauliAt P e) (𝓝[>] 0)
      (𝓝 ((P.e : ℂ) ^ 5 / e * pauliZeroLimit (atUnitCharge P d₁ d₂ dm d₃) 1)) := by
    refine hT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with Q (hQ : 0 < Q)
    exact (pauliAt_scale P h₁ h₂ hδm h₃ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ e hQ.le).symm
  unfold pauliZeroLimit
  rw [hT'.limUnder_eq]
  rfl

/-- At the physical charge `e = e_P`: `pauliZeroLimit P e_P = e_P⁴ · pauliZeroLimit P₁ 1`. -/
theorem pauliZeroLimit_self_scale :
    pauliZeroLimit P P.e = (P.e : ℂ) ^ 4 * pauliZeroLimit (atUnitCharge P d₁ d₂ dm d₃) 1 := by
  rw [pauliZeroLimit_scale P h₁ h₂ hδm h₃ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂]
  by_cases he : (P.e : ℂ) = 0
  · simp [he]
  · congr 1
    field_simp

end Scaling

/-- **The regulated coefficient `[e⁴] F₂(0) = F₂⁽⁴⁾(0; m_γ, Λ, M₁, M₂)`** (section 5.6), at
counterterms `δᵢ = e² dᵢ`: the `q² → 0⁺` limit of the Pauli projection at charge `1` with
counterterms `dᵢ`. It does not involve `P.e` (`pauliZeroFour_charge`). -/
noncomputable def pauliZeroFour (P : Params) (d₁ d₂ dm d₃ : ℝ) : ℂ :=
  pauliZeroLimit (atUnitCharge P d₁ d₂ dm d₃) 1

/-- `pauliZeroFour` does not depend on the charge or the counterterms of `P`. -/
theorem pauliZeroFour_charge (P : Params) (e δ₁ δ₂ δm δ₃ d₁ d₂ dm d₃ : ℝ) :
    pauliZeroFour { P with e := e, δ₁ := δ₁, δ₂ := δ₂, δm := δm, δ₃ := δ₃ } d₁ d₂ dm d₃ =
      pauliZeroFour P d₁ d₂ dm d₃ := rfl

/-- **`pauliZeroLimit / e⁴` is the charge-independent regulated coefficient**: for `e ≠ 0` and
counterterms `δᵢ = e² dᵢ`, `pauliZeroLimit P e / e⁴ = F₂⁽⁴⁾(0)`. -/
theorem pauliZeroLimit_div_pow_four (P : Params) {d₁ d₂ dm d₃ : ℝ}
    (h₁ : P.δ₁ = P.e ^ 2 * d₁) (h₂ : P.δ₂ = P.e ^ 2 * d₂) (hδm : P.δm = P.e ^ 2 * dm)
    (h₃ : P.δ₃ = P.e ^ 2 * d₃) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (he : P.e ≠ 0) :
    pauliZeroLimit P P.e / (P.e : ℂ) ^ 4 = pauliZeroFour P d₁ d₂ dm d₃ := by
  rw [pauliZeroLimit_self_scale P h₁ h₂ hδm h₃ hm hmγ hΛ hM₁ hM₂ hc₁ hc₂, pauliZeroFour]
  have he' : (P.e : ℂ) ≠ 0 := ofReal_ne_zero.mpr he
  field_simp

/-- **With the frozen counterterm conditions.** At fixed regulators, `e ≠ 0`: if the counterterms
of `P` satisfy (Z₅), (Z₈), (K₀) at charge `e` and `d₁, d₂, d_m, d₃` satisfy them at charge `1`,
then `pauliZeroLimit P e = e⁴ · F₂⁽⁴⁾(0)`. -/
theorem pauliZeroLimit_eq_pow_four_mul_of_conditions (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (he : P.e ≠ 0)
    (hel : IsElectronOnShell P hm hmγ hΛ) (hph : IsPhotonOnShell P hm hM₁ hM₂ hPV₁ hPV₂)
    (hch : QED.OneLoop.IsChargeNormalized P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ)
    {d₁ d₂ dm d₃ : ℝ}
    (hel₁ : IsElectronOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ)
    (hph₁ : IsPhotonOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hM₁ hM₂ hPV₁ hPV₂)
    (hch₁ : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ) :
    pauliZeroLimit P P.e = (P.e : ℂ) ^ 4 * pauliZeroFour P d₁ d₂ dm d₃ := by
  obtain ⟨h₁, h₂, hδm, h₃⟩ := QED.TwoLoop.Scaling.counterterms_eq_sq_mul P hm hmγ hΛ hM₁ hM₂ hPV₁
    hPV₂ he hel hph hch hel₁ hph₁ hch₁
  exact pauliZeroLimit_self_scale P h₁ h₂ hδm h₃ hm hmγ hΛ hM₁.le hM₂.le hPV₁ hPV₂

/-- **The counterterms at charge `1` are unique**, so `F₂⁽⁴⁾(0)` with the frozen conditions is a
function of the regulators alone. -/
theorem pauliZeroFour_eq_of_conditions (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {d₁ d₂ dm d₃ d₁' d₂' dm' d₃' : ℝ}
    (hel₁ : IsElectronOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ)
    (hph₁ : IsPhotonOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hM₁ hM₂ hPV₁ hPV₂)
    (hch₁ : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ)
    (hel₁' : IsElectronOnShell (atUnitCharge P d₁' d₂' dm' d₃') hm hmγ hΛ)
    (hph₁' : IsPhotonOnShell (atUnitCharge P d₁' d₂' dm' d₃') hm hM₁ hM₂ hPV₁ hPV₂)
    (hch₁' : QED.OneLoop.IsChargeNormalized 1 (1 + d₁') P.m P.mγ P.Λ hm hmγ hΛ) :
    pauliZeroFour P d₁ d₂ dm d₃ = pauliZeroFour P d₁' d₂' dm' d₃' := by
  obtain ⟨e₁, e₂, em, e₃⟩ := QED.TwoLoop.Scaling.counterterms_eq_sq_mul
    (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ one_ne_zero hel₁ hph₁ hch₁
    (d₁ := d₁') (d₂ := d₂') (dm := dm') (d₃ := d₃') hel₁' hph₁' hch₁'
  simp only [atUnitCharge, one_pow, one_mul] at e₁ e₂ em e₃
  rw [e₁, e₂, em, e₃]

/-! ### The five units -/

/-- The five units of section 5.2. -/
inductive TwoLoopUnit
  /-- vacuum polarization with its `δ₃` insertions -/
  | VP
  /-- the self-energy pair `S₊`, `S₋` with their `δ₂`, `δ_m` insertions -/
  | S
  /-- the corner pair `C₊`, `C₋` with `δ₁` at their internal vertices -/
  | C
  /-- the ladder with `δ₁` at the external vertex -/
  | L
  /-- the crossed ladder -/
  | X
  deriving DecidableEq

instance : Fintype TwoLoopUnit :=
  ⟨{.VP, .S, .C, .L, .X}, fun x => by cases x <;> simp⟩

/-- **The `q → 0` value of a unit**, the sum of the explicit values of its classes (with the sign
`-1` of the closed fermion loop of `VP`). -/
noncomputable def unitZero : TwoLoopUnit → Params → ℂ
  | .VP, P => -vpZero P + 2 * d3Zero P
  | .S, P => openZero .Sp P + openZero .Sm P + d2InZero P + d2OutZero P
  | .C, P => openZero .Cp P + openZero .Cm P + 2 * d1Zero P
  | .L, P => openZero .L P + d1Zero P
  | .X, P => openZero .X P

/-- **The contribution of a unit to the Pauli coefficient at charge `1`**:
`(1/(64 m⁵)) (1/i) unitZero U P`. -/
noncomputable def unitF2 (U : TwoLoopUnit) (P : Params) : ℂ :=
  1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * unitZero U P)

theorem sum_unitZero (P : Params) :
    ∑ U, unitZero U P = openZero .L P + openZero .X P + openZero .Cp P + openZero .Cm P +
      openZero .Sp P + openZero .Sm P - vpZero P + d2InZero P + d2OutZero P + 2 * d3Zero P +
        3 * d1Zero P := by
  have h : (Finset.univ : Finset TwoLoopUnit) = {.VP, .S, .C, .L, .X} := rfl
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [unitZero]
  ring

section Units

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁)
  (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
  (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
include hm hmγ hΛ hM₁ hM₂ hc₁ hc₂

/-- **The `q² → 0⁺` limit as the sum of the five units**:
`pauliZeroLimit P e = 1/(64 e m⁵) · (1/i) · ∑_U unitZero U P = (1/e) ∑_U unitF2 U P`. -/
theorem pauliZeroLimit_eq_units (e : ℝ) :
    pauliZeroLimit P e = 1 / (e : ℂ) * ∑ U, unitF2 U P := by
  rw [pauliZeroLimit_eq_sum P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ e]
  simp only [unitF2, ← Finset.mul_sum, sum_unitZero]
  by_cases he : (e : ℂ) = 0
  · simp [he]
  · have hm' : (P.m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
    field_simp

/-- **The regulated `[e⁴] F₂(0)` as the sum of the five units** at charge `1` with counterterms
`dᵢ`: `F₂⁽⁴⁾(0) = ∑_U unitF2 U P₁`. -/
theorem pauliZeroFour_eq_sum_units (d₁ d₂ dm d₃ : ℝ) :
    pauliZeroFour P d₁ d₂ dm d₃ = ∑ U, unitF2 U (atUnitCharge P d₁ d₂ dm d₃) := by
  rw [pauliZeroFour, pauliZeroLimit_eq_units (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ hM₁ hM₂ hc₁
    hc₂ 1]
  simp

end Units

end QED.TwoLoop.UnitsRegulated

end
