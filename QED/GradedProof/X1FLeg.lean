/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1Leg
public import QED.GradedProof.X1CStatement

/-!
# (X₁) piece F: the electron legs of the Dyson decomposition

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece F (assembly). The legs `QED.GradedProof.X1C.inLeg`,
`QED.GradedProof.X1C.outLeg` of orders `0, 2, 4` are products of the open-line propagator and the
self-energy parts of orders `2`, `4`. Given the on-shell data `(A_j, B_j)` of (G₉) for `j = 1, 2`:

* `tendsto_inLeg`, `tendsto_outLeg`: at a fixed off-shell `r`, the `ε → 0⁺` limits are
  `inLim`, `outLim` (the same products with `S̃₀(r)` and `A_j(r²) r̸ + B_j(r²) M`);
* `tendsto_prop_mul_seForm`, `tendsto_seForm_mul_prop`: `S̃₀ Σ` and `Σ S̃₀` converge as matrices
  through off-shell momenta (`A(-M²) 𝟙 - A(-M²)/(2M) (M 𝟙 - p̸)`);
* `tendsto_inLim_mulVec`, `tendsto_vecMul_outLim`: sandwiched with an on-shell spinor, the legs
  of orders `2` and `4` tend to `0` through off-shell momenta (for order `4` the chain term is
  `(S̃₀Σ₁) ((S̃₀Σ₁) u)`, a convergent matrix times a vector tending to `0`).
-/

@[expose] public section

open Matrix Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X1F

/-- The `4 × 4` identity matrix. -/
local notation "𝟙" => (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The self-energy form `A(r²) r̸ + B(r²) m`. -/
noncomputable def seForm (m : ℝ) (A B : ℝ → ℂ) (r : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  A (Minkowski.dot r r) • Dirac.slash r + (B (Minkowski.dot r r) * m) • 𝟙

/-- The `ε → 0⁺` limit of the in-leg of order `2c`. -/
noncomputable def inLim (m : ℝ) (A₁ B₁ A₂ B₂ : ℝ → ℂ) (c : ℕ) (r : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  match c with
  | 0 => 1
  | 1 => QED.OneLoop.electronPropagator m 0 r * seForm m A₁ B₁ r
  | 2 => QED.OneLoop.electronPropagator m 0 r * seForm m A₂ B₂ r +
      QED.OneLoop.electronPropagator m 0 r * seForm m A₁ B₁ r *
        (QED.OneLoop.electronPropagator m 0 r * seForm m A₁ B₁ r)
  | _ => 0

/-- The `ε → 0⁺` limit of the out-leg of order `2a`. -/
noncomputable def outLim (m : ℝ) (A₁ B₁ A₂ B₂ : ℝ → ℂ) (a : ℕ) (r : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  match a with
  | 0 => 1
  | 1 => seForm m A₁ B₁ r * QED.OneLoop.electronPropagator m 0 r
  | 2 => seForm m A₂ B₂ r * QED.OneLoop.electronPropagator m 0 r +
      seForm m A₁ B₁ r * QED.OneLoop.electronPropagator m 0 r *
        (seForm m A₁ B₁ r * QED.OneLoop.electronPropagator m 0 r)
  | _ => 0

section Eps

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F) {A₁ B₁ A₂ B₂ : ℝ → ℂ} {r : Fin 4 → ℝ}

theorem tendsto_matrix_of_entries {G : ℝ → Matrix (Fin 4) (Fin 4) ℂ}
    {L : Matrix (Fin 4) (Fin 4) ℂ}
    (h : ∀ α β, Tendsto (fun ε => G ε α β) (𝓝[>] 0) (𝓝 (L α β))) :
    Tendsto G (𝓝[>] 0) (𝓝 L) :=
  tendsto_pi_nhds.2 fun α => tendsto_pi_nhds.2 fun β => h α β

variable (hr : Minkowski.dot r r ≠ -Φ.mass Φ.openLine ^ 2)
  (h₁ : ∀ α β, Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D Φ.openLine 1 r α β)
    (𝓝[>] 0) (𝓝 (seForm (Φ.mass Φ.openLine) A₁ B₁ r α β)))
  (h₂ : ∀ α β, Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D Φ.openLine 2 r α β)
    (𝓝[>] 0) (𝓝 (seForm (Φ.mass Φ.openLine) A₂ B₂ r α β)))
include hr h₁ h₂

/-- **The `ε → 0⁺` limit of the in-leg** at an off-shell momentum. -/
theorem tendsto_inLeg (c : ℕ) :
    Tendsto (fun ε : ℝ => X1C.inLeg { P with ε := ε } Φ D c r) (𝓝[>] 0)
      (𝓝 (inLim (Φ.mass Φ.openLine) A₁ B₁ A₂ B₂ c r)) := by
  have hS : Tendsto (fun ε : ℝ => X1C.openProp { P with ε := ε } Φ r) (𝓝[>] 0)
      (𝓝 (QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) 0 r)) :=
    QED.WickModel.tendsto_electronPropagator_zero hr
  have H₁ := hS.mul (tendsto_matrix_of_entries h₁)
  have H₂ := hS.mul (tendsto_matrix_of_entries h₂)
  rcases c with _ | _ | _ | c
  · exact tendsto_const_nhds
  · exact H₁
  · exact H₂.add (H₁.mul H₁)
  · exact tendsto_const_nhds

/-- **The `ε → 0⁺` limit of the out-leg** at an off-shell momentum. -/
theorem tendsto_outLeg (a : ℕ) :
    Tendsto (fun ε : ℝ => X1C.outLeg { P with ε := ε } Φ D a r) (𝓝[>] 0)
      (𝓝 (outLim (Φ.mass Φ.openLine) A₁ B₁ A₂ B₂ a r)) := by
  have hS : Tendsto (fun ε : ℝ => X1C.openProp { P with ε := ε } Φ r) (𝓝[>] 0)
      (𝓝 (QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) 0 r)) :=
    QED.WickModel.tendsto_electronPropagator_zero hr
  have H₁ := (tendsto_matrix_of_entries h₁).mul hS
  have H₂ := (tendsto_matrix_of_entries h₂).mul hS
  rcases a with _ | _ | _ | a
  · exact tendsto_const_nhds
  · exact H₁
  · exact H₂.add (H₁.mul H₁)
  · exact tendsto_const_nhds

end Eps

section Shell

variable {m : ℝ} (hm : 0 < m) {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -m ^ 2)
include hm hp

/-- **`S̃₀ Σ` converges through off-shell momenta.** -/
theorem tendsto_prop_mul_seForm {A B : ℝ → ℂ} (hA : ContinuousAt A (-m ^ 2))
    (h0 : A (-m ^ 2) * ((-m : ℝ) : ℂ) + B (-m ^ 2) * m = 0)
    (hd : HasDerivAt (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * m) 0 (-m)) :
    Tendsto (fun r => QED.OneLoop.electronPropagator m 0 r * seForm m A B r)
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p)
      (𝓝 (A (-m ^ 2) • 𝟙 + (-A (-m ^ 2) / (2 * m)) • ((m : ℂ) • 𝟙 - Dirac.slash p))) := by
  obtain ⟨hA0, hk⟩ := X1.tendsto_coeffs hm hA h0 hd hp
  have hv : Tendsto (fun r => (m : ℂ) • 𝟙 - Dirac.slash r)
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 ((m : ℂ) • 𝟙 - Dirac.slash p)) :=
    ((continuous_const.sub QED.WickModel.LszLegs.continuous_slash).tendsto p).mono_left
      nhdsWithin_le_nhds
  refine ((hA0.smul_const 𝟙).add (hk.smul hv)).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with r hr
  exact (QED.WickModel.electronPropagator_zero_mul_selfEnergyForm hr _ _).symm

/-- **`Σ S̃₀` converges through off-shell momenta.** -/
theorem tendsto_seForm_mul_prop {A B : ℝ → ℂ} (hA : ContinuousAt A (-m ^ 2))
    (h0 : A (-m ^ 2) * ((-m : ℝ) : ℂ) + B (-m ^ 2) * m = 0)
    (hd : HasDerivAt (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * m) 0 (-m)) :
    Tendsto (fun r => seForm m A B r * QED.OneLoop.electronPropagator m 0 r)
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p)
      (𝓝 (A (-m ^ 2) • 𝟙 + (-A (-m ^ 2) / (2 * m)) • ((m : ℂ) • 𝟙 - Dirac.slash p))) := by
  obtain ⟨hA0, hk⟩ := X1.tendsto_coeffs hm hA h0 hd hp
  have hv : Tendsto (fun r => (m : ℂ) • 𝟙 - Dirac.slash r)
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 ((m : ℂ) • 𝟙 - Dirac.slash p)) :=
    ((continuous_const.sub QED.WickModel.LszLegs.continuous_slash).tendsto p).mono_left
      nhdsWithin_le_nhds
  refine ((hA0.smul_const 𝟙).add (hk.smul hv)).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with r hr
  exact (QED.WickModel.selfEnergyForm_mul_electronPropagator_zero hr _ _).symm

variable {A₁ B₁ A₂ B₂ : ℝ → ℂ} (hA₁ : ContinuousAt A₁ (-m ^ 2))
  (h0₁ : A₁ (-m ^ 2) * ((-m : ℝ) : ℂ) + B₁ (-m ^ 2) * m = 0)
  (hd₁ : HasDerivAt (fun z : ℝ => A₁ (-z ^ 2) * (z : ℂ) + B₁ (-z ^ 2) * m) 0 (-m))
  (hA₂ : ContinuousAt A₂ (-m ^ 2))
  (h0₂ : A₂ (-m ^ 2) * ((-m : ℝ) : ℂ) + B₂ (-m ^ 2) * m = 0)
  (hd₂ : HasDerivAt (fun z : ℝ => A₂ (-z ^ 2) * (z : ℂ) + B₂ (-z ^ 2) * m) 0 (-m))
include hA₁ h0₁ hd₁ hA₂ h0₂ hd₂

/-- **The in-legs of orders `2`, `4` vanish on shell**: `inLim c r *ᵥ u → 0` (`c = 1, 2`)
through off-shell momenta, for `p̸ u = -m u`. -/
theorem tendsto_inLim_mulVec {u : Fin 4 → ℂ} (hu : Dirac.slash p *ᵥ u = -((m : ℂ) • u)) {c : ℕ}
    (hc : c ≠ 0) :
    Tendsto (fun r => inLim m A₁ B₁ A₂ B₂ c r *ᵥ u) (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p)
      (𝓝 0) := by
  have l₁ := X1.tendsto_leg_in hm hA₁ h0₁ hd₁ hp hu
  have l₂ := X1.tendsto_leg_in hm hA₂ h0₂ hd₂ hp hu
  have hL := tendsto_prop_mul_seForm hm hp hA₁ h0₁ hd₁
  rcases c with _ | _ | _ | c
  · exact absurd rfl hc
  · exact l₁
  · have hc2 := ((continuous_fst.matrix_mulVec continuous_snd).tendsto _).comp
      (hL.prodMk_nhds l₁)
    rw [Matrix.mulVec_zero] at hc2
    have hs := l₂.add hc2
    rw [add_zero] at hs
    refine hs.congr fun r => ?_
    simp only [inLim, Function.comp_def, Matrix.add_mulVec, Matrix.mulVec_mulVec]
    rfl
  · simpa [inLim] using (tendsto_const_nhds : Tendsto (fun _ : Fin 4 → ℝ => (0 : Fin 4 → ℂ))
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 0))

/-- **The out-legs of orders `2`, `4` vanish on shell**: `w ᵥ* outLim a r' → 0` (`a = 1, 2`)
through off-shell momenta, for `w p̸ = -m w`. -/
theorem tendsto_vecMul_outLim {w : Fin 4 → ℂ} (hw : w ᵥ* Dirac.slash p = -((m : ℂ) • w))
    {a : ℕ} (ha : a ≠ 0) :
    Tendsto (fun r => w ᵥ* outLim m A₁ B₁ A₂ B₂ a r) (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p)
      (𝓝 0) := by
  have l₁ := X1.tendsto_leg_out hm hA₁ h0₁ hd₁ hp hw
  have l₂ := X1.tendsto_leg_out hm hA₂ h0₂ hd₂ hp hw
  have hL := tendsto_seForm_mul_prop hm hp hA₁ h0₁ hd₁
  rcases a with _ | _ | _ | a
  · exact absurd rfl ha
  · exact l₁
  · have hc2 := ((continuous_fst.matrix_vecMul continuous_snd).tendsto _).comp
      (l₁.prodMk_nhds hL)
    rw [Matrix.zero_vecMul] at hc2
    have hs := l₂.add hc2
    rw [add_zero] at hs
    refine hs.congr fun r => ?_
    simp only [outLim, Function.comp_def, Matrix.vecMul_add, Matrix.vecMul_vecMul]
    rfl
  · simpa [outLim] using (tendsto_const_nhds : Tendsto (fun _ : Fin 4 → ℝ => (0 : Fin 4 → ℂ))
      (𝓝[{r | Minkowski.dot r r ≠ -m ^ 2}] p) (𝓝 0))

end Shell

end QED.GradedProof.X1F

end
