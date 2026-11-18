/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXGraphTraceData
public import QED.TwoLoop.UnitLGraphTraceJet
import Mathlib.Tactic.Ring

/-!
# Second-order jets of the crossed-ladder patterns

Section 8 of `docs/TWO-LOOP-UNITS.md`, the graph half of the X unit. The coefficients
`T₁, T₂, T₃` of the projected crossed numerator are planar expressions
(`QED/TwoLoop/UnitXGraphTraceData.lean`) in the Pauli data and the slot data, which depend on
`u` through `p'(u)`. With the planar jet calculus of `QED/TwoLoop/UnitLGraphTraceJet.lean`:

* the jets of the slot data at `m = 1`: `eₖ = (1, αₖ, 0, 0) + (0, 0, -2βₖ, 0) u + (0, 2βₖ, 0, 0) u²`
  and `sₖ = (0, -αₖ, 0, 0) + (0, 0, 2βₖ, 0) u + (0, -2βₖ, 0, 0) u²`, with `αₖ = aₖ + bₖ`,
  `βₖ = bₖ` (`jet_xE`, `jet_xS`);
* the jets of the patterns `om0`, `omG`, `bs`, `hg` (`hasJet2_om0Pl`, …);
* the values of the combinations entering `T₁, T₂, T₃` (`xT1_s2`, `x01_s2`, …, `x23_s2`,
  `xd1_eq`, `xd2_eq`, `xd3_eq`): all values and first-order coefficients vanish, and the
  second-order ones are explicit polynomials in the `αₖ, βₖ`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.TwoLoop.UnitXGraph

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraphTrace
open Pl

/-! ### The jets of the slot data at `m = 1` -/

/-- **The jet of a slot numerator**: `eₖ = (1, aₖ + bₖ p'⁰, -bₖ p'¹, 0)`. -/
theorem jet_xE {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) (k : Fin 4) :
    HasPJ (fun u => xE P z u k) (eJ ((xslotA z k : ℂ) + (xslotB z k : ℂ)) (xslotB z k : ℂ)) :=
  (HasPlJet.mk (HasJet2.const 1) ((HasJet2.const (xslotA z k : ℂ)).add
    (jet_P0.const_mul (xslotB z k : ℂ))) (jet_P1.const_mul (xslotB z k : ℂ)).neg
    (HasJet2.const 0)).of_eq
    (fun u => by
      ext <;> simp [ePl, crossedQ_apply, hm, restMomentum])
    (by ext <;> simp [eJ]) (by ext <;> simp [eJ, mul_comm]) (by ext <;> simp [eJ, mul_comm])

/-- The jet of the slash of `q = a p + b p'`, with `α = a + b`, `β = b`. -/
def sJ (α β : ℂ) : PJ := ⟨⟨0, -α, 0, 0⟩, ⟨0, 0, 2 * β, 0⟩, ⟨0, -2 * β, 0, 0⟩⟩

/-- **The jet of the slash of a slot momentum**: `sₖ = (0, -(aₖ + bₖ p'⁰), bₖ p'¹, 0)`. -/
theorem jet_xS {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) (k : Fin 4) :
    HasPJ (fun u => xS P z u k) (sJ ((xslotA z k : ℂ) + (xslotB z k : ℂ)) (xslotB z k : ℂ)) :=
  (HasPlJet.mk (HasJet2.const 0) ((HasJet2.const (xslotA z k : ℂ)).add
    (jet_P0.const_mul (xslotB z k : ℂ))).neg
    (jet_P1.const_mul (xslotB z k : ℂ)) (HasJet2.const 0)).of_eq
    (fun u => by
      ext <;> simp [sPl, crossedQ_apply, hm, restMomentum])
    (by ext <;> simp [sJ]) (by ext <;> simp [sJ, mul_comm]) (by ext <;> simp [sJ, mul_comm])

/-! ### Jet arithmetic for the nested patterns -/

section Patterns

variable {Q₀ Q₁ R A B Z : ℝ → Pl} {q₀ q₁ r a b z : PJ}

/-- The coefficients of `om0Pl` from the jets of its arguments. -/
def om0Jk (sel : PJ → ℂ) (q₀ q₁ r a b : PJ) : ℂ :=
  4 * sel (((q₀.mul a).mul (PJ.c g0)).mul b) + 4 * sel (((q₁.mul a).mul (PJ.c g1)).mul b) -
    8 * sel ((r.mul a.bar).mul b)

theorem hasJet2_om0Pl (hQ₀ : HasPJ Q₀ q₀) (hQ₁ : HasPJ Q₁ q₁) (hR : HasPJ R r)
    (hA : HasPJ A a) (hB : HasPJ B b) :
    HasJet2 (fun u => om0Pl (Q₀ u) (Q₁ u) (R u) (A u) (B u)) (om0Jk PJ.s0 q₀ q₁ r a b)
      (om0Jk PJ.s1 q₀ q₁ r a b) (om0Jk PJ.s2 q₀ q₁ r a b) := by
  have h1 := (((hQ₀.mul hA).mul (HasPJ.const g0)).mul hB).s
  have h2 := (((hQ₁.mul hA).mul (HasPJ.const g1)).mul hB).s
  have h3 := ((hR.mul hA.bar).mul hB).s
  exact ((h1.const_mul 4).add (h2.const_mul 4)).sub (h3.const_mul 8)

/-- The coefficients of `omGPl` from the jets of its arguments. -/
def omGJk (sel : PJ → ℂ) (q₀ q₁ r a b : PJ) : ℂ :=
  4 * sel (((q₀.gam.mul a).mul (PJ.c g0)).mul b) +
    4 * sel (((q₁.gam.mul a).mul (PJ.c g1)).mul b) - 8 * sel ((r.gamT.mul a.bar).mul b)

theorem hasJet2_omGPl (hQ₀ : HasPJ Q₀ q₀) (hQ₁ : HasPJ Q₁ q₁) (hR : HasPJ R r)
    (hA : HasPJ A a) (hB : HasPJ B b) :
    HasJet2 (fun u => omGPl (Q₀ u) (Q₁ u) (R u) (A u) (B u)) (omGJk PJ.s0 q₀ q₁ r a b)
      (omGJk PJ.s1 q₀ q₁ r a b) (omGJk PJ.s2 q₀ q₁ r a b) := by
  have h1 := (((hQ₀.gam.mul hA).mul (HasPJ.const g0)).mul hB).s
  have h2 := (((hQ₁.gam.mul hA).mul (HasPJ.const g1)).mul hB).s
  have h3 := ((hR.gamT.mul hA.bar).mul hB).s
  exact ((h1.const_mul 4).add (h2.const_mul 4)).sub (h3.const_mul 8)

/-- The coefficients of `bsPl` from the jets of its arguments. -/
def bsJk (sel : PJ → ℂ) (q₀ q₁ r a b z : PJ) : ℂ :=
  4 * sel ((((q₀.mul a).mul (PJ.c g0)).mul b).gam.mul z) +
    4 * sel ((((q₁.mul a).mul (PJ.c g1)).mul b).gam.mul z) -
    8 * sel (((r.mul a.bar).mul b).gam.mul z)

theorem hasJet2_bsPl (hQ₀ : HasPJ Q₀ q₀) (hQ₁ : HasPJ Q₁ q₁) (hR : HasPJ R r)
    (hA : HasPJ A a) (hB : HasPJ B b) (hZ : HasPJ Z z) :
    HasJet2 (fun u => bsPl (Q₀ u) (Q₁ u) (R u) (A u) (B u) (Z u)) (bsJk PJ.s0 q₀ q₁ r a b z)
      (bsJk PJ.s1 q₀ q₁ r a b z) (bsJk PJ.s2 q₀ q₁ r a b z) := by
  have h1 := ((((hQ₀.mul hA).mul (HasPJ.const g0)).mul hB).gam.mul hZ).s
  have h2 := ((((hQ₁.mul hA).mul (HasPJ.const g1)).mul hB).gam.mul hZ).s
  have h3 := (((hR.mul hA.bar).mul hB).gam.mul hZ).s
  exact ((h1.const_mul 4).add (h2.const_mul 4)).sub (h3.const_mul 8)

/-- The coefficients of `hgPl` from the jets of its arguments. -/
def hgJk (sel : PJ → ℂ) (q₀ q₁ r a b z : PJ) : ℂ :=
  4 * sel ((q₀.mul ((a.mul (PJ.c g0)).mul b).gam).mul z) +
    4 * sel ((q₁.mul ((a.mul (PJ.c g1)).mul b).gam).mul z) -
    8 * sel ((r.mul (a.mul b.bar).gamT.bar).mul z)

theorem hasJet2_hgPl (hQ₀ : HasPJ Q₀ q₀) (hQ₁ : HasPJ Q₁ q₁) (hR : HasPJ R r)
    (hA : HasPJ A a) (hB : HasPJ B b) (hZ : HasPJ Z z) :
    HasJet2 (fun u => hgPl (Q₀ u) (Q₁ u) (R u) (A u) (B u) (Z u)) (hgJk PJ.s0 q₀ q₁ r a b z)
      (hgJk PJ.s1 q₀ q₁ r a b z) (hgJk PJ.s2 q₀ q₁ r a b z) := by
  have h1 := ((hQ₀.mul ((hA.mul (HasPJ.const g0)).mul hB).gam).mul hZ).s
  have h2 := ((hQ₁.mul ((hA.mul (HasPJ.const g1)).mul hB).gam).mul hZ).s
  have h3 := ((hR.mul (hA.mul hB.bar).gamT.bar).mul hZ).s
  exact ((h1.const_mul 4).add (h2.const_mul 4)).sub (h3.const_mul 8)

end Patterns

/-! ### The combinations entering `T₁, T₂, T₃` -/

/-- The planar constant `2` as a jet. -/
abbrev c2 : PJ := PJ.c two₂

/-- The jet coefficients of the crossed contraction `xw(P; e)` of `T₁`. -/
def xT1k (sel : PJ → ℂ) (e₀ e₁ e₂ e₃ s₀ : PJ) : ℂ :=
  -lwJk sel qJ0 qJ1 rJ (PJ.c 1) (e₀.bar.mul e₁) e₂ e₃ - 2 * bsJk sel qJ0 qJ1 rJ (e₀.bar.mul e₁) e₂ e₃ +
    2 * hgJk sel qJ0 qJ1 rJ e₁ e₂ (e₃.mul s₀)

/-- The jet coefficients of the contraction `(0, 1)`. -/
def x01k (sel : PJ → ℂ) (e₂ e₃ : PJ) : ℂ :=
  -lwJk sel qJ0 qJ1 rJ (PJ.c 1) c2 e₂ e₃ - 2 * bsJk sel qJ0 qJ1 rJ c2 e₂ e₃

/-- The jet coefficients of the contraction `(0, 2)` at `m = 1`. -/
def x02k (sel : PJ → ℂ) (s₁ e₃ : PJ) : ℂ :=
  -16 * om0Jk sel qJ0 qJ1 rJ e₃ (PJ.c 1) - 4 * omGJk sel qJ0 qJ1 rJ s₁ e₃

/-- The jet coefficients of the contraction `(0, 3)`. -/
def x03k (sel : PJ → ℂ) (e₁ e₂ : PJ) : ℂ :=
  4 * hgJk sel qJ0 qJ1 rJ e₁ e₂ (PJ.c 1) + 16 * omGJk sel qJ0 qJ1 rJ e₁ e₂ - f3Jk sel qJ0 qJ1 rJ e₁ e₂

/-- The jet coefficients of the contraction `(1, 2)`. -/
def x12k (sel : PJ → ℂ) (e₀ e₃ s₀ : PJ) : ℂ :=
  -lwJk sel qJ0 qJ1 rJ (PJ.c 1) (e₀.bar.mul c2) (PJ.c 1) e₃ -
    2 * bsJk sel qJ0 qJ1 rJ (e₀.bar.mul c2) (PJ.c 1) e₃ + 2 * hgJk sel qJ0 qJ1 rJ c2 (PJ.c 1) (e₃.mul s₀)

/-- The jet coefficients of the contraction `(1, 3)` at `m = 1`. -/
def x13k (sel : PJ → ℂ) (e₀ s₀ s₂ : PJ) : ℂ :=
  -16 * om0Jk sel qJ0 qJ1 rJ (PJ.c 1) e₀ - 4 * omGJk sel qJ0 qJ1 rJ s₂ (PJ.c 1) +
    8 * om0Jk sel qJ0 qJ1 rJ s₂ s₀

/-- The jet coefficients of the contraction `(2, 3)`. -/
def x23k (sel : PJ → ℂ) (e₀ e₁ s₀ : PJ) : ℂ :=
  -lwJk sel qJ0 qJ1 rJ (PJ.c 1) (e₀.bar.mul e₁) c2 (PJ.c 1) -
    2 * bsJk sel qJ0 qJ1 rJ (e₀.bar.mul e₁) c2 (PJ.c 1) + 2 * hgJk sel qJ0 qJ1 rJ e₁ c2 s₀

section Values

variable (α₀ α₁ α₂ α₃ β₀ β₁ β₂ β₃ : ℂ)

/-- **The second-order coefficient of `xw(P; e)`.** -/
theorem xT1_s2 : xT1k PJ.s2 (eJ α₀ β₀) (eJ α₁ β₁) (eJ α₂ β₂) (eJ α₃ β₃) (sJ α₀ β₀) =
    512 * (2 * α₀ * α₁ * α₂ * α₃ - α₀ * α₁ * α₂ - 2 * α₀ * α₁ * α₃ * β₂ + α₀ * α₁ * β₂ -
      α₀ * α₁ * β₃ - α₀ * α₁ + 2 * α₀ * α₂ * α₃ * β₁ - α₀ * α₂ * α₃ - α₀ * α₂ * β₁ +
      α₀ * α₂ * β₃ + α₀ * α₃ * β₁ - α₀ * α₃ * β₂ - α₀ * β₁ + α₀ * β₂ + α₁ * α₂ * β₀ -
      α₁ * α₂ * β₃ - α₁ * α₂ - α₁ * α₃ * β₀ + α₁ * α₃ * β₂ + α₁ * β₀ - α₁ * β₂ + α₁ * β₃ +
      α₂ * α₃ * β₀ - α₂ * α₃ * β₁ - α₂ * α₃ - α₂ * β₀ + α₂ * β₁ - α₂ * β₃ + 2 * α₂ - α₃ * β₁ +
      α₃ * β₂ - α₃ - β₀ + 2 * β₁ - 2 * β₂ + β₃) := by
  simp [xT1k, lwJk, bsJk, hgJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, sJ, qJ0, qJ1,
    rJ, g0, g1]
  ring

theorem xT1_s0 : xT1k PJ.s0 (eJ α₀ β₀) (eJ α₁ β₁) (eJ α₂ β₂) (eJ α₃ β₃) (sJ α₀ β₀) = 0 := by
  simp [xT1k, lwJk, bsJk, hgJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, sJ, qJ0, qJ1,
    rJ, g0, g1]

theorem xT1_s1 : xT1k PJ.s1 (eJ α₀ β₀) (eJ α₁ β₁) (eJ α₂ β₂) (eJ α₃ β₃) (sJ α₀ β₀) = 0 := by
  simp [xT1k, lwJk, bsJk, hgJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, sJ, qJ0, qJ1,
    rJ, g0, g1]

theorem x01_s2 : x01k PJ.s2 (eJ α₂ β₂) (eJ α₃ β₃) =
    -1024 * (α₂ * α₃ + α₂ * β₃ - 2 * α₂ - α₃ * β₂ + α₃ + 2 * β₂ - β₃) := by
  simp [x01k, lwJk, bsJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem x01_s0 : x01k PJ.s0 (eJ α₂ β₂) (eJ α₃ β₃) = 0 := by
  simp [x01k, lwJk, bsJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ, g0, g1]

theorem x01_s1 : x01k PJ.s1 (eJ α₂ β₂) (eJ α₃ β₃) = 0 := by
  simp [x01k, lwJk, bsJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ, g0, g1]

theorem x02_s2 : x02k PJ.s2 (sJ α₁ β₁) (eJ α₃ β₃) =
    -1024 * (α₁ * α₃ - α₁ * β₃ - α₁ + α₃ * β₁ - 2 * α₃ + 2 * β₃) := by
  simp [x02k, om0Jk, omGJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, sJ, qJ0, qJ1, rJ,
    g0, g1]
  ring

theorem x02_s0 : x02k PJ.s0 (sJ α₁ β₁) (eJ α₃ β₃) = 0 := by
  simp [x02k, om0Jk, omGJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, sJ, qJ0, qJ1, rJ,
    g0, g1]

theorem x02_s1 : x02k PJ.s1 (sJ α₁ β₁) (eJ α₃ β₃) = 0 := by
  simp [x02k, om0Jk, omGJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, sJ, qJ0, qJ1, rJ,
    g0, g1]

theorem x03_s2 : x03k PJ.s2 (eJ α₁ β₁) (eJ α₂ β₂) =
    -1024 * (4 * α₁ * α₂ - 4 * α₁ * β₂ - α₁ + 4 * α₂ * β₁ - α₂) := by
  simp [x03k, hgJk, omGJk, f3Jk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, qJ0, qJ1, rJ,
    g0, g1]
  ring

theorem x03_s0 : x03k PJ.s0 (eJ α₁ β₁) (eJ α₂ β₂) = 0 := by
  simp [x03k, hgJk, omGJk, f3Jk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, qJ0, qJ1, rJ,
    g0, g1]

theorem x03_s1 : x03k PJ.s1 (eJ α₁ β₁) (eJ α₂ β₂) = 0 := by
  simp [x03k, hgJk, omGJk, f3Jk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, qJ0, qJ1, rJ,
    g0, g1]

theorem x12_s2 : x12k PJ.s2 (eJ α₀ β₀) (eJ α₃ β₃) (sJ α₀ β₀) = -1024 * (α₃ + β₀ - β₃) := by
  simp [x12k, lwJk, bsJk, hgJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, sJ, qJ0, qJ1,
    rJ, g0, g1]
  ring

theorem x12_s0 : x12k PJ.s0 (eJ α₀ β₀) (eJ α₃ β₃) (sJ α₀ β₀) = 0 := by
  simp [x12k, lwJk, bsJk, hgJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, sJ, qJ0, qJ1,
    rJ, g0, g1]

theorem x12_s1 : x12k PJ.s1 (eJ α₀ β₀) (eJ α₃ β₃) (sJ α₀ β₀) = 0 := by
  simp [x12k, lwJk, bsJk, hgJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, sJ, qJ0, qJ1,
    rJ, g0, g1]

theorem x13_s2 : x13k PJ.s2 (eJ α₀ β₀) (sJ α₀ β₀) (sJ α₂ β₂) =
    -1024 * (α₀ * α₂ - α₀ * β₂ + α₂ * β₀ - α₂ - 2 * β₀) := by
  simp [x13k, om0Jk, omGJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, sJ, qJ0, qJ1, rJ,
    g0, g1]
  ring

theorem x13_s0 : x13k PJ.s0 (eJ α₀ β₀) (sJ α₀ β₀) (sJ α₂ β₂) = 0 := by
  simp [x13k, om0Jk, omGJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, sJ, qJ0, qJ1, rJ,
    g0, g1]

theorem x13_s1 : x13k PJ.s1 (eJ α₀ β₀) (sJ α₀ β₀) (sJ α₂ β₂) = 0 := by
  simp [x13k, om0Jk, omGJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, sJ, qJ0, qJ1, rJ,
    g0, g1]

theorem x23_s2 : x23k PJ.s2 (eJ α₀ β₀) (eJ α₁ β₁) (sJ α₀ β₀) =
    -1024 * (α₀ * α₁ + α₀ * β₁ - α₁ * β₀ + β₀ - 2 * β₁) := by
  simp [x23k, lwJk, bsJk, hgJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, eJ, sJ, qJ0, qJ1,
    rJ, g0, g1]
  ring

theorem x23_s0 : x23k PJ.s0 (eJ α₀ β₀) (eJ α₁ β₁) (sJ α₀ β₀) = 0 := by
  simp [x23k, lwJk, bsJk, hgJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, sJ, qJ0, qJ1,
    rJ, g0, g1]

theorem x23_s1 : x23k PJ.s1 (eJ α₀ β₀) (eJ α₁ β₁) (sJ α₀ β₀) = 0 := by
  simp [x23k, lwJk, bsJk, hgJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, sJ, qJ0, qJ1,
    rJ, g0, g1]

end Values

/-! ### The constant patterns of `T₃` -/

/-- The jet coefficients of the double contraction `(01)(23)`. -/
def xd1k (sel : PJ → ℂ) : ℂ :=
  -lwJk sel qJ0 qJ1 rJ (PJ.c 1) c2 c2 (PJ.c 1) - 2 * bsJk sel qJ0 qJ1 rJ c2 c2 (PJ.c 1)

/-- The jet coefficients of the double contraction `(02)(13)`. -/
def xd2k (sel : PJ → ℂ) : ℂ := 8 * omGJk sel qJ0 qJ1 rJ (PJ.c 1) (PJ.c 1)

/-- The jet coefficients of the double contraction `(03)(12)`. -/
def xd3k (sel : PJ → ℂ) : ℂ :=
  4 * hgJk sel qJ0 qJ1 rJ c2 (PJ.c 1) (PJ.c 1) + 16 * omGJk sel qJ0 qJ1 rJ c2 (PJ.c 1) -
    f3Jk sel qJ0 qJ1 rJ c2 (PJ.c 1)

theorem xd1_eq (sel : PJ → ℂ) (h : sel = PJ.s0 ∨ sel = PJ.s1 ∨ sel = PJ.s2) : xd1k sel = 0 := by
  rcases h with rfl | rfl | rfl
  · simp [xd1k, lwJk, bsJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, qJ0, qJ1, rJ, g0, g1]
  · simp [xd1k, lwJk, bsJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, qJ0, qJ1, rJ, g0, g1]
  · simp [xd1k, lwJk, bsJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, qJ0, qJ1, rJ, g0, g1]
    norm_num

theorem xd2_eq (sel : PJ → ℂ) (h : sel = PJ.s0 ∨ sel = PJ.s1 ∨ sel = PJ.s2) : xd2k sel = 0 := by
  rcases h with rfl | rfl | rfl
  · simp [xd2k, omGJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, qJ0, qJ1, rJ, g0, g1]
  · simp [xd2k, omGJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, qJ0, qJ1, rJ, g0, g1]
  · simp [xd2k, omGJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, qJ0, qJ1, rJ, g0, g1]
    norm_num

theorem xd3_eq (sel : PJ → ℂ) (h : sel = PJ.s0 ∨ sel = PJ.s1 ∨ sel = PJ.s2) : xd3k sel = 0 := by
  rcases h with rfl | rfl | rfl
  · simp [xd3k, hgJk, omGJk, f3Jk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, qJ0, qJ1, rJ, g0,
      g1]
  · simp [xd3k, hgJk, omGJk, f3Jk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, qJ0, qJ1, rJ, g0,
      g1]
  · simp [xd3k, hgJk, omGJk, f3Jk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s2, qJ0, qJ1, rJ, g0,
      g1]
    norm_num

end QED.TwoLoop.UnitXGraph

end
