/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.CountertermInsertionD2
public import QED.TwoLoop.CountertermInsertionD3
public import QED.TwoLoop.OneLoopEmbedding

/-!
# The counterterm insertion identities at fixed `ε` (O2-13)

Obligation O2-13 of `docs/TWO-LOOP-DERIVATION.md`, section 5.1, in the strongest form available
at fixed `ε`: for each of the seven counterterm classes of the order-`e⁵` vertex
(`QED.TwoLoop.Relabel.CtClass`), the value (T₁₀) of its representative is written through the
one-loop vertex. Momentum conservation `pOut 0 = pIn 0 + kIn 0` is assumed throughout; nothing
else is assumed unless stated.

**The one-loop quantities** (all entries of energy-first integrals (D) at the fixed `ε`, outgoing
momentum `p' = pOut 0`, incoming `p = pIn 0`):

* `vertexValue`: the regulated one-loop vertex (62.40), `∫ vertexIntegrand` (the one-loop term of
  the frozen (W₁));
* `massInValue`, `massOutValue`: the one-loop vertex with `S̃ → S̃²` on the incoming, resp.
  outgoing, electron line;
* `defectInValue`, `defectOutValue`: the one-loop vertex integrand times `iε / (k² + m² - iε)`,
  `k` the momentum of the incoming, resp. outgoing, electron line (the `O(ε)` defect);
* `transverseValue`, `longitudinalValue`: the one-loop vertex with the photon factor
  `g_{νρ} d(ℓ) → g_{νρ} ℓ² d(ℓ)²`, resp. `→ d(ℓ)² ℓ_ν ℓ_ρ`.

**The identities.**

1. **`δ₁`, exact, no hypothesis** (`contractionValue₂_d1At1`, `…2`, `…3`): each `δ₁` class is
   `δ₁ · vertexValue`, for every `ε`. With (T₁₃) the same holds for the packet 6a value
   `contractionValue` (`contractionValue_d1At1`, …). (T₁₃) is used in the form proved in
   `QED/TwoLoop/OneLoopEmbedding.lean`, the same statement as the sealed
   `QED.WickModel.contractionValue₂_eq_contractionValue`, whose import closure contains a
   provider module.
2. **`δ₂`, `δ_m`, exact at fixed `ε ≠ 0`.** The integrand identity
   (`integrand_d2In`, `integrand_d2Out`) holds pointwise:
   `[class integrand] = -δ₂ [vertex integrand] + (δ₂ - δ_m) m [S̃² integrand]
     - δ₂ (iε / D) [vertex integrand]`. Under the integrability (both stages) of the three
   integrands on the right, the value identity follows (`contractionValue₂_d2In_eq`,
   `contractionValue₂_d2Out_eq`):
   `class = -δ₂ vertexValue + (δ₂ - δ_m) m massValue - δ₂ defectValue`.
   The defect term is not zero at any `ε ≠ 0`; the identity of section 5.1 without it holds only
   in the limit `ε → 0⁺`, which is not proved here.
3. **`δ₃`, exact, no `ε` defect.** The integrand identity (`integrand_d3`) holds pointwise for each
   slot pairing; under the integrability of the transverse and longitudinal integrands
   (`contractionValue₂_d3Slot0_eq`, `…Slot1_eq`):
   `class = -(δ₃/2) transverseValue + (δ₃/2) longitudinalValue`. The two slot pairings have the
   same value with no hypothesis (`contractionValue₂_d3Slot0_eq_d3Slot1`). The longitudinal term
   is O2-14 and is kept separate.
4. **All seven classes** (`countertermPart_eq_insertions`): with all the integrability
   hypotheses, the counterterm part of the order-`e⁵` vertex is
   `(3δ₁ - 2δ₂) vertexValue + (δ₂ - δ_m) m (massIn + massOut) - δ₂ (defectIn + defectOut)
     - δ₃ transverseValue + δ₃ longitudinalValue`,
   the fixed-`ε` form of the formula of section 5.1.
-/

@[expose] public section

namespace QED.TwoLoop.Insertion

open QED.WickModel QED.TwoLoop.Relabel Complex MeasureTheory

/-! ### Integrability in both stages and linearity -/

/-- Integrability in both stages of the energy-first prescription (D): in the energy at every
spatial momentum, and of the energy integral over the spatial momentum. -/
def EnergyFirstIntegrable (F : (Fin 4 → ℝ) → ℂ) : Prop :=
  (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ => F (Fin.cons t v)) ∧
    Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, F (Fin.cons t v)

theorem EnergyFirstIntegrable.const_mul {F : (Fin 4 → ℝ) → ℂ} (hF : EnergyFirstIntegrable F)
    (c : ℂ) : EnergyFirstIntegrable fun ℓ => c * F ℓ :=
  ⟨fun v => (hF.1 v).const_mul c, by simp only [integral_const_mul]; exact hF.2.const_mul c⟩

theorem EnergyFirstIntegrable.add {F G : (Fin 4 → ℝ) → ℂ} (hF : EnergyFirstIntegrable F)
    (hG : EnergyFirstIntegrable G) : EnergyFirstIntegrable fun ℓ => F ℓ + G ℓ := by
  refine ⟨fun v => (hF.1 v).add (hG.1 v), ?_⟩
  have h : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, F (Fin.cons t v) + G (Fin.cons t v) =
      (∫ t : ℝ, F (Fin.cons t v)) + ∫ t : ℝ, G (Fin.cons t v) := fun v =>
    integral_add (hF.1 v) (hG.1 v)
  simp_rw [h]
  exact hF.2.add hG.2

/-- The energy-first integral is additive on integrands integrable in both stages. -/
theorem energyFirstIntegral_add {F G : (Fin 4 → ℝ) → ℂ} (hF : EnergyFirstIntegrable F)
    (hG : EnergyFirstIntegrable G) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => F ℓ + G ℓ) =
      QED.OneLoop.energyFirstIntegral F + QED.OneLoop.energyFirstIntegral G := by
  unfold QED.OneLoop.energyFirstIntegral
  have h : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, F (Fin.cons t v) + G (Fin.cons t v) =
      (∫ t : ℝ, F (Fin.cons t v)) + ∫ t : ℝ, G (Fin.cons t v) := fun v =>
    integral_add (hF.1 v) (hG.1 v)
  simp_rw [h]
  exact integral_add hF.2 hG.2

/-- Linearity of the energy-first integral on two integrable integrands. -/
theorem energyFirstIntegral_linear₂ {F G : (Fin 4 → ℝ) → ℂ} (hF : EnergyFirstIntegrable F)
    (hG : EnergyFirstIntegrable G) (a b : ℂ) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => a * F ℓ + b * G ℓ) =
      a * QED.OneLoop.energyFirstIntegral F + b * QED.OneLoop.energyFirstIntegral G := by
  rw [energyFirstIntegral_add (hF.const_mul a) (hG.const_mul b), energyFirstIntegral_const_mul',
    energyFirstIntegral_const_mul']

/-- Linearity of the energy-first integral on three integrable integrands. -/
theorem energyFirstIntegral_linear₃ {F G H : (Fin 4 → ℝ) → ℂ} (hF : EnergyFirstIntegrable F)
    (hG : EnergyFirstIntegrable G) (hH : EnergyFirstIntegrable H) (a b c : ℂ) :
    QED.OneLoop.energyFirstIntegral (fun ℓ => a * F ℓ + b * G ℓ + c * H ℓ) =
      a * QED.OneLoop.energyFirstIntegral F + b * QED.OneLoop.energyFirstIntegral G +
        c * QED.OneLoop.energyFirstIntegral H := by
  rw [energyFirstIntegral_add ((hF.const_mul a).add (hG.const_mul b)) (hH.const_mul c),
    energyFirstIntegral_linear₂ hF hG, energyFirstIntegral_const_mul']

/-! ### The one-loop integrands and values -/

section Values

variable (P : Params) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)

/-- The entry `(i, j)` of the frozen one-loop vertex integrand (C). -/
noncomputable def vertexEntry (ℓ : Fin 4 → ℝ) : ℂ :=
  QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε p' p μ ℓ i j

/-- The regulated one-loop vertex (62.40) at the fixed `ε`: the energy-first integral of the
entry `(i, j)` of the frozen integrand (C), the one-loop term of (W₁). -/
noncomputable def vertexValue : ℂ :=
  QED.OneLoop.energyFirstIntegral (vertexEntry P p' p μ i j)

/-- The one-loop vertex integrand with `S̃ → S̃²` on the incoming electron line. -/
noncomputable def massInEntry (ℓ : Fin 4 → ℝ) : ℂ :=
  vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p' + ℓ))
    (QED.OneLoop.electronPropagator P.m P.ε (p + ℓ) * QED.OneLoop.electronPropagator P.m P.ε (p + ℓ))
    (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε ℓ) i j

/-- The one-loop vertex integrand with `S̃ → S̃²` on the outgoing electron line. -/
noncomputable def massOutEntry (ℓ : Fin 4 → ℝ) : ℂ :=
  vertexChain P.e μ
    (QED.OneLoop.electronPropagator P.m P.ε (p' + ℓ) * QED.OneLoop.electronPropagator P.m P.ε (p' + ℓ))
    (QED.OneLoop.electronPropagator P.m P.ε (p + ℓ))
    (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε ℓ) i j

/-- The `O(ε)` defect integrand of the incoming line: `iε / (k² + m² - iε)` times the one-loop
vertex integrand, `k = p + ℓ`. -/
noncomputable def defectInEntry (ℓ : Fin 4 → ℝ) : ℂ :=
  (P.ε : ℂ) * I / electronDenom P.m P.ε (p + ℓ) * vertexEntry P p' p μ i j ℓ

/-- The `O(ε)` defect integrand of the outgoing line, `k = p' + ℓ`. -/
noncomputable def defectOutEntry (ℓ : Fin 4 → ℝ) : ℂ :=
  (P.ε : ℂ) * I / electronDenom P.m P.ε (p' + ℓ) * vertexEntry P p' p μ i j ℓ

/-- The one-loop vertex integrand with the transverse photon factor `g_{νρ} ℓ² d(ℓ)²`. -/
noncomputable def transverseEntry (ℓ : Fin 4 → ℝ) : ℂ :=
  vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p' + ℓ))
    (QED.OneLoop.electronPropagator P.m P.ε (p + ℓ)) (transversePhoton P.mγ P.Λ P.ε ℓ) i j

/-- The one-loop vertex integrand with the longitudinal photon factor `d(ℓ)² ℓ_ν ℓ_ρ` (O2-14). -/
noncomputable def longitudinalEntry (ℓ : Fin 4 → ℝ) : ℂ :=
  vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p' + ℓ))
    (QED.OneLoop.electronPropagator P.m P.ε (p + ℓ)) (longitudinalPhoton P.mγ P.Λ P.ε ℓ) i j

/-- The mass-insertion value on the incoming line. -/
noncomputable def massInValue : ℂ := QED.OneLoop.energyFirstIntegral (massInEntry P p' p μ i j)

/-- The mass-insertion value on the outgoing line. -/
noncomputable def massOutValue : ℂ := QED.OneLoop.energyFirstIntegral (massOutEntry P p' p μ i j)

/-- The `O(ε)` defect value of the incoming line. -/
noncomputable def defectInValue : ℂ := QED.OneLoop.energyFirstIntegral (defectInEntry P p' p μ i j)

/-- The `O(ε)` defect value of the outgoing line. -/
noncomputable def defectOutValue : ℂ :=
  QED.OneLoop.energyFirstIntegral (defectOutEntry P p' p μ i j)

/-- The transverse value: the one-loop vertex with `d → ℓ² d²`. -/
noncomputable def transverseValue : ℂ :=
  QED.OneLoop.energyFirstIntegral (transverseEntry P p' p μ i j)

/-- The longitudinal value (O2-14). -/
noncomputable def longitudinalValue : ℂ :=
  QED.OneLoop.energyFirstIntegral (longitudinalEntry P p' p μ i j)

end Values

/-! ### `δ₁`: vertex factor proportionality, exact -/

section D1

variable (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
  (αOut βIn μ : Fin 1 → Fin 4)
include hmom

/-- **`δ₁` at `v₁`**: the class value is `δ₁` times the one-loop vertex, at every `ε`. -/
theorem contractionValue₂_d1At1 :
    contractionValue₂ P repD1At1 pOut pIn kIn αOut βIn μ =
      (P.δ₁ : ℂ) * vertexValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) :=
  contractionValue₂_repD1At1 P hmom αOut βIn μ

/-- **`δ₁` at the external-photon vertex `v₂`**: `δ₁` times the one-loop vertex, at every `ε`. -/
theorem contractionValue₂_d1At2 :
    contractionValue₂ P repD1At2 pOut pIn kIn αOut βIn μ =
      (P.δ₁ : ℂ) * vertexValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) :=
  contractionValue₂_repD1At2 P hmom αOut βIn μ

/-- **`δ₁` at `v₃`**: `δ₁` times the one-loop vertex, at every `ε`. -/
theorem contractionValue₂_d1At3 :
    contractionValue₂ P repD1At3 pOut pIn kIn αOut βIn μ =
      (P.δ₁ : ℂ) * vertexValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) :=
  contractionValue₂_repD1At3 P hmom αOut βIn μ

/-- **`δ₁` at `v₁`, packet 6a value**: through (T₁₃), the frozen one-loop value (X₂₇) of the
class representative is `δ₁` times the one-loop vertex. -/
theorem contractionValue_d1At1 :
    contractionValue P repD1At1 pOut pIn kIn αOut βIn μ =
      (P.δ₁ : ℂ) * vertexValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) := by
  rw [← QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one P repD1At1
    (loopCount_eq_one_of_unique d1c1_isChord_iff).le]
  exact contractionValue₂_d1At1 P hmom αOut βIn μ

/-- **`δ₁` at `v₂`, packet 6a value** (through (T₁₃)). -/
theorem contractionValue_d1At2 :
    contractionValue P repD1At2 pOut pIn kIn αOut βIn μ =
      (P.δ₁ : ℂ) * vertexValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) := by
  rw [← QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one P repD1At2
    (loopCount_eq_one_of_unique d1c2_isChord_iff).le]
  exact contractionValue₂_d1At2 P hmom αOut βIn μ

/-- **`δ₁` at `v₃`, packet 6a value** (through (T₁₃)). -/
theorem contractionValue_d1At3 :
    contractionValue P repD1At3 pOut pIn kIn αOut βIn μ =
      (P.δ₁ : ℂ) * vertexValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) := by
  rw [← QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one P repD1At3
    (loopCount_eq_one_of_unique d1c3_isChord_iff).le]
  exact contractionValue₂_d1At3 P hmom αOut βIn μ

end D1

/-! ### `δ₂`, `δ_m`: the electron line insertion at fixed `ε` -/

/-- **The `δ₂`, `δ_m` integrand identity, incoming line, at fixed `ε ≠ 0`**: the integrand of the
class (`contractionValue₂_repD2In`) is `-δ₂` times the one-loop vertex integrand, plus
`(δ₂ - δ_m) m` times the integrand with `S̃ → S̃²`, minus `δ₂ iε / D` times the vertex integrand. -/
theorem integrand_d2In (P : Params) (hε : P.ε ≠ 0) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 4 → ℝ) :
    vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p' + ℓ))
        (electronInsertion P.m P.ε P.δ₂ P.δm (p + ℓ))
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε ℓ) =
      (-(P.δ₂ : ℂ)) • QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε p' p μ ℓ +
        (((P.δ₂ - P.δm) * P.m : ℝ) : ℂ) •
          vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p' + ℓ))
            (QED.OneLoop.electronPropagator P.m P.ε (p + ℓ) *
              QED.OneLoop.electronPropagator P.m P.ε (p + ℓ))
            (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε ℓ) -
        ((P.δ₂ : ℂ) * ((P.ε : ℂ) * I / electronDenom P.m P.ε (p + ℓ))) •
          QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε p' p μ ℓ := by
  rw [electronInsertion_eq _ _ _ hε, vertexChain_sub_in, vertexChain_add_in, vertexChain_smul_in,
    vertexChain_smul_in, vertexChain_smul_in, vertexIntegrand_eq_vertexChain]

/-- **The `δ₂`, `δ_m` integrand identity, outgoing line, at fixed `ε ≠ 0`.** -/
theorem integrand_d2Out (P : Params) (hε : P.ε ≠ 0) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 4 → ℝ) :
    vertexChain P.e μ (electronInsertion P.m P.ε P.δ₂ P.δm (p' + ℓ))
        (QED.OneLoop.electronPropagator P.m P.ε (p + ℓ))
        (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε ℓ) =
      (-(P.δ₂ : ℂ)) • QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε p' p μ ℓ +
        (((P.δ₂ - P.δm) * P.m : ℝ) : ℂ) •
          vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p' + ℓ) *
              QED.OneLoop.electronPropagator P.m P.ε (p' + ℓ))
            (QED.OneLoop.electronPropagator P.m P.ε (p + ℓ))
            (QED.OneLoop.photonPropagator P.mγ P.Λ P.ε ℓ) -
        ((P.δ₂ : ℂ) * ((P.ε : ℂ) * I / electronDenom P.m P.ε (p' + ℓ))) •
          QED.OneLoop.vertexIntegrand P.e P.m P.mγ P.Λ P.ε p' p μ ℓ := by
  rw [electronInsertion_eq _ _ _ hε, vertexChain_sub_out, vertexChain_add_out,
    vertexChain_smul_out, vertexChain_smul_out, vertexChain_smul_out,
    vertexIntegrand_eq_vertexChain]

section D2

variable (P : Params) (hε : P.ε ≠ 0) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
  (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4)
include hε hmom

/-- **The `δ₂`, `δ_m` class on the incoming line, at fixed `ε ≠ 0`**: if the vertex, mass-insertion
and defect integrands are integrable in both stages, the class value is
`-δ₂ vertexValue + (δ₂ - δ_m) m massInValue - δ₂ defectInValue`. -/
theorem contractionValue₂_d2In_eq
    (hV : EnergyFirstIntegrable (vertexEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)))
    (hM : EnergyFirstIntegrable (massInEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)))
    (hE : EnergyFirstIntegrable (defectInEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0))) :
    contractionValue₂ P repD2In pOut pIn kIn αOut βIn μ =
      -(P.δ₂ : ℂ) * vertexValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) +
        (((P.δ₂ - P.δm) * P.m : ℝ) : ℂ) * massInValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) +
        (-(P.δ₂ : ℂ)) * defectInValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) := by
  rw [contractionValue₂_repD2In P hmom, vertexValue, massInValue, defectInValue,
    ← energyFirstIntegral_linear₃ hV hM hE]
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  rw [integrand_d2In P hε]
  simp only [vertexEntry, massInEntry, defectInEntry, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- **The `δ₂`, `δ_m` class on the outgoing line, at fixed `ε ≠ 0`**: under the integrability of
the three integrands, `-δ₂ vertexValue + (δ₂ - δ_m) m massOutValue - δ₂ defectOutValue`. -/
theorem contractionValue₂_d2Out_eq
    (hV : EnergyFirstIntegrable (vertexEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)))
    (hM : EnergyFirstIntegrable (massOutEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)))
    (hE : EnergyFirstIntegrable (defectOutEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0))) :
    contractionValue₂ P repD2Out pOut pIn kIn αOut βIn μ =
      -(P.δ₂ : ℂ) * vertexValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) +
        (((P.δ₂ - P.δm) * P.m : ℝ) : ℂ) * massOutValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) +
        (-(P.δ₂ : ℂ)) * defectOutValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) := by
  rw [contractionValue₂_repD2Out P hmom, vertexValue, massOutValue, defectOutValue,
    ← energyFirstIntegral_linear₃ hV hM hE]
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  rw [integrand_d2Out P hε]
  simp only [vertexEntry, massOutEntry, defectOutEntry, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

end D2

/-! ### `δ₃`: the photon line insertion, exact -/

/-- **The `δ₃` integrand identity, exact**: the integrand of either slot class
(`contractionValue₂_repD3Slot0`, `…Slot1`) is `-(δ₃/2)` times the transverse integrand plus
`δ₃/2` times the longitudinal integrand, for every `ε`. -/
theorem integrand_d3 (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 4 → ℝ) :
    vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p' + ℓ))
        (QED.OneLoop.electronPropagator P.m P.ε (p + ℓ)) (photonInsertion P.δ₃ P.mγ P.Λ P.ε ℓ) =
      (-(P.δ₃ / 2 : ℂ)) • vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p' + ℓ))
          (QED.OneLoop.electronPropagator P.m P.ε (p + ℓ)) (transversePhoton P.mγ P.Λ P.ε ℓ) +
        ((P.δ₃ / 2 : ℂ)) • vertexChain P.e μ (QED.OneLoop.electronPropagator P.m P.ε (p' + ℓ))
          (QED.OneLoop.electronPropagator P.m P.ε (p + ℓ)) (longitudinalPhoton P.mγ P.Λ P.ε ℓ) := by
  rw [← vertexChain_smul_photon, ← vertexChain_smul_photon, ← vertexChain_add_photon]
  exact congrArg _ (funext fun ν => funext fun ρ => photonInsertion_eq _ _ _ _ _ ν ρ)

section D3

variable (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
  (αOut βIn μ : Fin 1 → Fin 4)
include hmom

/-- **The two `δ₃` slot pairings have the same value**, at every `ε`. -/
theorem contractionValue₂_d3Slot0_eq_d3Slot1 :
    contractionValue₂ P repD3Slot0 pOut pIn kIn αOut βIn μ =
      contractionValue₂ P repD3Slot1 pOut pIn kIn αOut βIn μ := by
  rw [contractionValue₂_repD3Slot0 P hmom, contractionValue₂_repD3Slot1 P hmom]

/-- **The `δ₃` class, slot `0` towards `v₁`**: under the integrability of the transverse and
longitudinal integrands, `-(δ₃/2) transverseValue + (δ₃/2) longitudinalValue`, at every `ε`. -/
theorem contractionValue₂_d3Slot0_eq
    (hT : EnergyFirstIntegrable (transverseEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)))
    (hL : EnergyFirstIntegrable (longitudinalEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0))) :
    contractionValue₂ P repD3Slot0 pOut pIn kIn αOut βIn μ =
      (-(P.δ₃ / 2 : ℂ)) * transverseValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) +
        (P.δ₃ / 2 : ℂ) * longitudinalValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) := by
  rw [contractionValue₂_repD3Slot0 P hmom, transverseValue, longitudinalValue,
    ← energyFirstIntegral_linear₂ hT hL]
  refine congrArg QED.OneLoop.energyFirstIntegral (funext fun ℓ => ?_)
  rw [integrand_d3]
  simp only [transverseEntry, longitudinalEntry, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- **The `δ₃` class, slot `1` towards `v₁`**: the same as slot `0`. -/
theorem contractionValue₂_d3Slot1_eq
    (hT : EnergyFirstIntegrable (transverseEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)))
    (hL : EnergyFirstIntegrable (longitudinalEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0))) :
    contractionValue₂ P repD3Slot1 pOut pIn kIn αOut βIn μ =
      (-(P.δ₃ / 2 : ℂ)) * transverseValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) +
        (P.δ₃ / 2 : ℂ) * longitudinalValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) := by
  rw [← contractionValue₂_d3Slot0_eq_d3Slot1 P hmom]
  exact contractionValue₂_d3Slot0_eq P hmom αOut βIn μ hT hL

end D3

/-! ### All seven counterterm classes -/

/-- **The counterterm part of the order-`e⁵` vertex at fixed `ε ≠ 0`** (the fixed-`ε` form of the
formula of section 5.1): under momentum conservation and the integrability in both stages of the
seven one-loop integrands, the sum of the seven counterterm class values is
`(3δ₁ - 2δ₂) vertexValue + (δ₂ - δ_m) m (massIn + massOut) - δ₂ (defectIn + defectOut)
  - δ₃ transverseValue + δ₃ longitudinalValue`. -/
theorem countertermPart_eq_insertions (P : Params) (hε : P.ε ≠ 0)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4)
    (hV : EnergyFirstIntegrable (vertexEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)))
    (hMi : EnergyFirstIntegrable (massInEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)))
    (hMo : EnergyFirstIntegrable (massOutEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)))
    (hEi : EnergyFirstIntegrable (defectInEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)))
    (hEo : EnergyFirstIntegrable (defectOutEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)))
    (hT : EnergyFirstIntegrable (transverseEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)))
    (hL : EnergyFirstIntegrable (longitudinalEntry P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0))) :
    ∑ c : CtClass, contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ =
      (3 * (P.δ₁ : ℂ) - 2 * (P.δ₂ : ℂ)) *
          vertexValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) +
        (((P.δ₂ - P.δm) * P.m : ℝ) : ℂ) *
          (massInValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) +
            massOutValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)) -
        (P.δ₂ : ℂ) * (defectInValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) +
            defectOutValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0)) -
        (P.δ₃ : ℂ) * transverseValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) +
        (P.δ₃ : ℂ) * longitudinalValue P (pOut 0) (pIn 0) (μ 0) (αOut 0) (βIn 0) := by
  rw [sum_ctClass,
    contractionValue₂_d2In_eq P hε hmom αOut βIn μ hV hMi hEi,
    contractionValue₂_d2Out_eq P hε hmom αOut βIn μ hV hMo hEo,
    contractionValue₂_d3Slot0_eq P hmom αOut βIn μ hT hL,
    contractionValue₂_d3Slot1_eq P hmom αOut βIn μ hT hL,
    contractionValue₂_d1At1 P hmom, contractionValue₂_d1At2 P hmom,
    contractionValue₂_d1At3 P hmom]
  ring

end QED.TwoLoop.Insertion

end
