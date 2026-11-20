/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.ConnectedPart
public import QED.Frozen.Graded.SelfEnergyPart
public import QED.Frozen.Graded.VertexPart
public import QED.Frozen.Graded.VacuumPolarizationPart
public import QED.Frozen.OneLoop.ElectronPropagator
public import QED.Frozen.OneLoop.PhotonPropagator

/-!
# (X₁) piece C: the statement of the order-`e⁵` Dyson decomposition

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C. At fixed `ε`, the order-`5` part (G₆″) of the connected three-point
function with outgoing momentum `r'`, incoming momentum `r` and photon momentum `q = r' - r` is
`i` times the sum of the products

`[out-leg of order 2a] V^{(2b+1)ν}(r', r) [in-leg of order 2c] [photon leg of order 2d]_ν^μ`,
`a + b + c + d = 2`,

with the frozen self-energy (G₈ₛ), vertex (G₈ᵥ) and vacuum polarization (G₈ₚ) of the open-line
flavour `f` as factors:

* in-leg (next to the incoming spinor): `1`, `S̃(r) Σ⁽²⁾(r)`,
  `S̃(r) Σ⁽⁴⁾(r) + S̃(r) Σ⁽²⁾(r) S̃(r) Σ⁽²⁾(r)`;
* out-leg: `1`, `Σ⁽²⁾(r') S̃(r')`, `Σ⁽⁴⁾(r') S̃(r') + Σ⁽²⁾(r') S̃(r') Σ⁽²⁾(r') S̃(r')`;
* photon leg (vertex index `ν`, external index `μ`, the external photon entering the first index
  of `Π`): `δ_ν^μ`, `∑_ρ Δ̃_{νρ}(q) Π⁽²⁾^{μρ}(q)`,
  `∑_ρ Δ̃_{νρ} Π⁽⁴⁾^{μρ} + ∑_{ρλκ} Δ̃_{νρ} Π⁽²⁾^{λρ} Δ̃_{λκ} Π⁽²⁾^{μκ}`.

Here `S̃` is the electron propagator of mass `M_f` and `Δ̃` the photon propagator at the fixed `ε`.
The factors `i` cancel: with the Feynman rules `[iΣ]`, `[iV]`, `[iΠ]` and `(1/i) S̃`, `(1/i) Δ̃`,
each product carries one overall `i`. The contractions containing a tadpole (a photon bridge with
no external field on one side) contribute `0`: their integrand is odd in the loop momenta of that
side. Ten index tuples `(a, b, c, d)`, thirteen products.

`DysonFive` is the decomposition as a proposition; `lszIntegrand_eventuallyEq` turns it, at every
`ε > 0`, into the equality of the sandwiched integrand of (G-L₁) with the sandwiched sum, which is
what the assembly (piece F) takes limits of.
-/

@[expose] public section

open Matrix Complex Filter Topology
open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof.X1C

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- The free electron propagator `S̃(r)` of the open-line flavour at the regulator `ε` of `P`. -/
noncomputable def openProp (r : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε r

/-- The in-leg chain of order `2n` (`n ≤ 2`), next to the incoming spinor. -/
noncomputable def inLeg (n : ℕ) (r : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  match n with
  | 0 => 1
  | 1 => openProp P Φ r * selfEnergyPart P Φ D Φ.openLine 1 r
  | 2 => openProp P Φ r * selfEnergyPart P Φ D Φ.openLine 2 r +
      openProp P Φ r * selfEnergyPart P Φ D Φ.openLine 1 r *
        (openProp P Φ r * selfEnergyPart P Φ D Φ.openLine 1 r)
  | _ => 0

/-- The out-leg chain of order `2n` (`n ≤ 2`), next to the outgoing spinor. -/
noncomputable def outLeg (n : ℕ) (r' : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  match n with
  | 0 => 1
  | 1 => selfEnergyPart P Φ D Φ.openLine 1 r' * openProp P Φ r'
  | 2 => selfEnergyPart P Φ D Φ.openLine 2 r' * openProp P Φ r' +
      selfEnergyPart P Φ D Φ.openLine 1 r' * openProp P Φ r' *
        (selfEnergyPart P Φ D Φ.openLine 1 r' * openProp P Φ r')
  | _ => 0

/-- The photon propagator `Δ̃_{νρ}(q)` at the regulators of `P`. -/
noncomputable def photonProp (q : Fin 4 → ℝ) (ν ρ : Fin 4) : ℂ :=
  QED.OneLoop.photonPropagator P.mγ P.Λ P.ε q ν ρ

/-- The photon-leg chain of order `2n` (`n ≤ 2`) from the vertex index `ν` to the external index
`μ`, the photon momentum `q` entering at `μ`. -/
noncomputable def photonLeg (n : ℕ) (q : Fin 4 → ℝ) (ν μ : Fin 4) : ℂ :=
  match n with
  | 0 => if ν = μ then 1 else 0
  | 1 => ∑ ρ, photonProp P q ν ρ * vacuumPolarizationPart P Φ D 1 q μ ρ
  | 2 => ∑ ρ, photonProp P q ν ρ * vacuumPolarizationPart P Φ D 2 q μ ρ +
      ∑ ρ, ∑ l, ∑ k, photonProp P q ν ρ * vacuumPolarizationPart P Φ D 1 q l ρ *
        (photonProp P q l k * vacuumPolarizationPart P Φ D 1 q μ k)
  | _ => 0

/-- **The right side of the order-`e⁵` Dyson decomposition** (divided by `i`): the sum over
`a + b + c + d = 2` and the vertex index `ν` of `[out-leg 2a] V^{(2b+1)ν}(r', r) [in-leg 2c]`
times the photon leg of order `2d`. -/
noncomputable def dysonFive (r' r : Fin 4 → ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ a ∈ Finset.range 3, ∑ b ∈ Finset.range 3, ∑ c ∈ Finset.range 3, ∑ d ∈ Finset.range 3,
    if a + b + c + d = 2 then
      ∑ ν, photonLeg P Φ D d (r' - r) ν μ •
        (outLeg P Φ D a r' * vertexPart P Φ D Φ.openLine b r' r ν * inLeg P Φ D c r)
    else 0

/-- The order-`5` connected three-point function (G₆″) as a matrix in the spinor indices. -/
noncomputable def connMatrix (r' r : Fin 4 → ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => connectedPart P Φ D 1 1 5 ![r'] ![r] ![r' - r] ![α] ![β] ![μ]

/-- **Piece C of (X₁), the order-`e⁵` Dyson decomposition at the regulators of `P`**: the connected
three-point function of order `5` is `i` times `dysonFive`, at all momenta and indices. -/
def DysonFive : Prop :=
  ∀ (r' r : Fin 4 → ℝ) (μ : Fin 4), connMatrix P Φ D r' r μ = I • dysonFive P Φ D r' r μ

/-- The sandwiched connected function equals the sandwiched decomposition. -/
theorem sandwich_eq (h : DysonFive P Φ D) (r' r : Fin 4 → ℝ) (μ : Fin 4) (w u : Fin 4 → ℂ) :
    (1 / I) * (w ⬝ᵥ (connMatrix P Φ D r' r μ *ᵥ u)) = w ⬝ᵥ (dysonFive P Φ D r' r μ *ᵥ u) := by
  rw [h, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← mul_assoc, one_div,
    inv_mul_cancel₀ I_ne_zero, one_mul]

/-- **The integrand of (G-L₁) from the decomposition**: if the decomposition holds at every
`ε > 0`, the sandwiched order-`5` connected function agrees, for `ε > 0`, with the sandwiched
`dysonFive`. -/
theorem lszIntegrand_eventuallyEq (h : ∀ ε > 0, DysonFive { P with ε := ε } Φ D)
    (r' r : Fin 4 → ℝ) (μ : Fin 4) (w u : Fin 4 → ℂ) :
    (fun ε : ℝ => (1 / I) * (w ⬝ᵥ ((Matrix.of fun α β => connectedPart { P with ε := ε } Φ D 1 1
        5 ![r'] ![r] ![r' - r] ![α] ![β] ![μ]) *ᵥ u))) =ᶠ[𝓝[>] 0]
      fun ε => w ⬝ᵥ (dysonFive { P with ε := ε } Φ D r' r μ *ᵥ u) := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact sandwich_eq { P with ε := ε } Φ D (h ε hε) r' r μ w u

end QED.GradedProof.X1C

end
