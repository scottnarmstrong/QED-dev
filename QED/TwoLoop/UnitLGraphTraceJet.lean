/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLGraphTraceData
public import QED.TwoLoop.ParamNumEvalJet
import Mathlib.Tactic.Ring

/-!
# Second-order jets of planar elements along the curve

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the L link, graph half. The coefficients
`T₁, T₂, T₃` of the projected ladder numerator are planar expressions in the Pauli data and the
slot momenta (`QED/TwoLoop/UnitLGraphTraceData.lean`), which depend on `u` through `p'(u)`. This
file extends the second-order jets of `QED/TwoLoop/ParamNumEvalJet.lean` to planar elements
(`HasPlJet`: a jet in each coordinate), with the rules for sums, scalar multiples, products, the
grade involution and the contractions, and gives the jets of the data at `m = 1`:
`p'(u) = (1 + 2u², 2u, 0, 0) + o(u²)`, `q² = 4u² + o(u²)`, the Pauli data `lQ0, lQ1, lR` and the
slot numerators `lE k = (1, aₖ + bₖ p'⁰, -bₖ p'¹, 0)`. The jets of the four contraction
patterns follow (`hasJet2_lwPl`, `hasJet2_omLPl`, `hasJet2_omRPl`, `hasJet2_f3Pl`, through the jet
arithmetic `PJ`), and their coefficients at the ladder data are evaluated (`lwJ_T1`, …): all
values and first-order coefficients vanish, and the second-order ones are explicit polynomials in
`αₖ = aₖ + bₖ`, `βₖ = bₖ`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.TwoLoop.UnitLGraphTrace

open QED.WickModel QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval
open Pl

/-- **A second-order jet of a planar element**: a jet in each coordinate. -/
def HasPlJet (X : ℝ → Pl) (x₀ x₁ x₂ : Pl) : Prop :=
  HasJet2 (fun u => (X u).s) x₀.s x₁.s x₂.s ∧ HasJet2 (fun u => (X u).a) x₀.a x₁.a x₂.a ∧
    HasJet2 (fun u => (X u).b) x₀.b x₁.b x₂.b ∧ HasJet2 (fun u => (X u).c) x₀.c x₁.c x₂.c

namespace HasPlJet

variable {X Y : ℝ → Pl} {x₀ x₁ x₂ y₀ y₁ y₂ : Pl}

theorem s (h : HasPlJet X x₀ x₁ x₂) : HasJet2 (fun u => (X u).s) x₀.s x₁.s x₂.s := h.1

theorem mk {s a b c : ℝ → ℂ} {s₀ s₁ s₂ a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ : ℂ}
    (hs : HasJet2 s s₀ s₁ s₂) (ha : HasJet2 a a₀ a₁ a₂) (hb : HasJet2 b b₀ b₁ b₂)
    (hc : HasJet2 c c₀ c₁ c₂) :
    HasPlJet (fun u => ⟨s u, a u, b u, c u⟩) ⟨s₀, a₀, b₀, c₀⟩ ⟨s₁, a₁, b₁, c₁⟩ ⟨s₂, a₂, b₂, c₂⟩ :=
  ⟨hs, ha, hb, hc⟩

theorem const (x : Pl) : HasPlJet (fun _ => x) x 0 0 :=
  ⟨HasJet2.const _, HasJet2.const _, HasJet2.const _, HasJet2.const _⟩

theorem of_eq (h : HasPlJet X x₀ x₁ x₂) (hXY : ∀ u, Y u = X u) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁)
    (h₂ : x₂ = y₂) : HasPlJet Y y₀ y₁ y₂ := by
  subst h₀ h₁ h₂
  obtain ⟨hs, ha, hb, hc⟩ := h
  exact ⟨hs.congr fun u => by rw [hXY], ha.congr fun u => by rw [hXY],
    hb.congr fun u => by rw [hXY], hc.congr fun u => by rw [hXY]⟩

theorem add (hX : HasPlJet X x₀ x₁ x₂) (hY : HasPlJet Y y₀ y₁ y₂) :
    HasPlJet (fun u => X u + Y u) (x₀ + y₀) (x₁ + y₁) (x₂ + y₂) :=
  ⟨hX.1.add hY.1, hX.2.1.add hY.2.1, hX.2.2.1.add hY.2.2.1, hX.2.2.2.add hY.2.2.2⟩

theorem sub (hX : HasPlJet X x₀ x₁ x₂) (hY : HasPlJet Y y₀ y₁ y₂) :
    HasPlJet (fun u => X u - Y u) (x₀ - y₀) (x₁ - y₁) (x₂ - y₂) :=
  ⟨hX.1.sub hY.1, hX.2.1.sub hY.2.1, hX.2.2.1.sub hY.2.2.1, hX.2.2.2.sub hY.2.2.2⟩

theorem smul {k : ℝ → ℂ} {k₀ k₁ k₂ : ℂ} (hk : HasJet2 k k₀ k₁ k₂) (hX : HasPlJet X x₀ x₁ x₂) :
    HasPlJet (fun u => k u • X u) (k₀ • x₀) (k₀ • x₁ + k₁ • x₀) (k₀ • x₂ + k₁ • x₁ + k₂ • x₀) :=
  ⟨hk.mul hX.1, hk.mul hX.2.1, hk.mul hX.2.2.1, hk.mul hX.2.2.2⟩

/-- **The product rule for planar jets.** -/
theorem mul (hX : HasPlJet X x₀ x₁ x₂) (hY : HasPlJet Y y₀ y₁ y₂) :
    HasPlJet (fun u => X u * Y u) (x₀ * y₀) (x₀ * y₁ + x₁ * y₀)
      (x₀ * y₂ + x₁ * y₁ + x₂ * y₀) := by
  obtain ⟨hs, ha, hb, hc⟩ := hX
  obtain ⟨hs', ha', hb', hc'⟩ := hY
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((((hs.mul hs').add (ha.mul ha')).sub (hb.mul hb')).add (hc.mul hc')).of_eq
      (fun u => by simp) (by simp) (by simp; ring) (by simp; ring)
  · exact ((((hs.mul ha').add (ha.mul hs')).add (hb.mul hc')).sub (hc.mul hb')).of_eq
      (fun u => by simp) (by simp) (by simp; ring) (by simp; ring)
  · exact ((((hs.mul hb').add (hb.mul hs')).add (ha.mul hc')).sub (hc.mul ha')).of_eq
      (fun u => by simp) (by simp) (by simp; ring) (by simp; ring)
  · exact ((((hs.mul hc').add (hc.mul hs')).add (ha.mul hb')).sub (hb.mul ha')).of_eq
      (fun u => by simp) (by simp) (by simp; ring) (by simp; ring)

theorem bar (hX : HasPlJet X x₀ x₁ x₂) : HasPlJet (fun u => Pl.bar (X u)) (Pl.bar x₀) (Pl.bar x₁)
    (Pl.bar x₂) :=
  ⟨hX.1, hX.2.1.neg, hX.2.2.1.neg, hX.2.2.2⟩

theorem gam (hX : HasPlJet X x₀ x₁ x₂) : HasPlJet (fun u => Pl.gam (X u)) (Pl.gam x₀) (Pl.gam x₁)
    (Pl.gam x₂) :=
  ⟨hX.1.const_mul _, hX.2.1.const_mul _, hX.2.2.1.const_mul _, HasJet2.const 0⟩

theorem gamT (hX : HasPlJet X x₀ x₁ x₂) :
    HasPlJet (fun u => Pl.gamT (X u)) (Pl.gamT x₀) (Pl.gamT x₁) (Pl.gamT x₂) :=
  ⟨hX.1.const_mul _, HasJet2.const 0, HasJet2.const 0, hX.2.2.2.const_mul _⟩

end HasPlJet

/-! ### The jets of the data at `m = 1` -/

theorem jet_P0 : HasJet2 (fun u => ((curveMomentum 1 u 0 : ℝ) : ℂ)) 1 0 2 :=
  (hasJet2_curveMomentum 1 0).of_eq (fun _ => rfl) (by norm_num [restMomentum]) (by norm_num)
    (by norm_num)

theorem jet_P1 : HasJet2 (fun u => ((curveMomentum 1 u 1 : ℝ) : ℂ)) 0 2 0 :=
  (hasJet2_curveMomentum 1 1).of_eq (fun _ => rfl) (by norm_num [restMomentum]) (by norm_num)
    (by norm_num)

/-- `q² = -(p'⁰ - 1)² + (p'¹)² = 4u² + o(u²)`. -/
theorem jet_Q2 :
    HasJet2 (fun u => ((Minkowski.dot (curveMomentum 1 u - restMomentum 1)
      (curveMomentum 1 u - restMomentum 1) : ℝ) : ℂ)) 0 0 4 := by
  have h := (((jet_P0.sub (HasJet2.const 1)).mul (jet_P0.sub (HasJet2.const 1))).neg).add
    (jet_P1.mul jet_P1)
  refine h.of_eq (fun u => ?_) (by ring) (by ring) (by ring)
  simp only [Minkowski.dot_eq, Pi.sub_apply, curveMomentum_two, curveMomentum_three,
    restMomentum_two, restMomentum_three]
  simp [restMomentum]

theorem jet_C1 : HasJet2 (fun u => pauliC1 1 (curveMomentum 1 u) (restMomentum 1)) 4 0 4 :=
  ((HasJet2.const (4 : ℂ)).add jet_Q2).of_eq (fun u => by simp [pauliC1]) (by ring) (by ring)
    (by ring)

theorem jet_C2 : HasJet2 (fun u => pauliC2 1 (curveMomentum 1 u) (restMomentum 1)) (-2) 0 4 :=
  (jet_Q2.sub (HasJet2.const (2 : ℂ))).of_eq (fun u => by simp [pauliC2]) (by ring) (by ring)
    (by ring)

theorem jet_S0 : HasJet2 (fun u => ((Minkowski.lower (curveMomentum 1 u + restMomentum 1) 0 : ℝ) :
    ℂ))
    (-2) 0 (-2) :=
  (jet_P0.add (HasJet2.const 1)).neg.of_eq
    (fun u => by simp [Minkowski.lower_eq, restMomentum, Matrix.vecHead, Matrix.vecTail])
    (by ring) (by ring) (by ring)

theorem jet_S1 : HasJet2 (fun u => ((Minkowski.lower (curveMomentum 1 u + restMomentum 1) 1 : ℝ) :
    ℂ))
    0 2 0 :=
  jet_P1.of_eq (fun u => by simp [Minkowski.lower_eq, restMomentum, Matrix.vecHead, Matrix.vecTail])
    rfl rfl rfl

theorem jet_ePl_curve :
    HasPlJet (fun u => ePl 1 (curveMomentum 1 u)) ⟨1, 1, 0, 0⟩ ⟨0, 0, -2, 0⟩ ⟨0, 2, 0, 0⟩ :=
  (HasPlJet.mk (HasJet2.const 1) jet_P0 jet_P1.neg (HasJet2.const 0)).of_eq
    (fun u => by simp [ePl]) (by simp) (by simp) (by simp)

theorem ePl_rest : ePl 1 (restMomentum 1) = ⟨1, 1, 0, 0⟩ := by
  ext <;> simp [ePl, restMomentum]

theorem jet_lQ0 {P : Params} (hm : P.m = 1) : HasPlJet (fun u => lQ0 P u) 0 0 ⟨-16, -16, 0, 0⟩ :=
  ((HasPlJet.smul jet_C1 (((HasPlJet.const (ePl 1 (restMomentum 1))).mul (HasPlJet.const g0L)).mul
      jet_ePl_curve)).add (HasPlJet.smul (jet_C2.mul jet_S0)
      ((HasPlJet.const (ePl 1 (restMomentum 1))).mul jet_ePl_curve))).of_eq
    (fun u => by simp only [lQ0, pauliQ, hm])
    (by ext <;> simp [ePl_rest, g0L] <;> norm_num) (by ext <;> simp [ePl_rest, g0L] <;> norm_num)
    (by ext <;> simp [ePl_rest, g0L] <;> norm_num)

theorem jet_lQ1 {P : Params} (hm : P.m = 1) : HasPlJet (fun u => lQ1 P u) 0 0 0 :=
  ((HasPlJet.smul jet_C1 (((HasPlJet.const (ePl 1 (restMomentum 1))).mul (HasPlJet.const g1)).mul
      jet_ePl_curve)).add (HasPlJet.smul (jet_C2.mul jet_S1)
      ((HasPlJet.const (ePl 1 (restMomentum 1))).mul jet_ePl_curve))).of_eq
    (fun u => by simp only [lQ1, pauliQ, hm])
    (by ext <;> simp [ePl_rest, g1]) (by ext <;> simp [ePl_rest, g1] <;> norm_num)
    (by ext <;> simp [ePl_rest, g1] <;> norm_num)

theorem jet_lR {P : Params} (hm : P.m = 1) :
    HasPlJet (fun u => lR P u) 0 ⟨0, 0, 8, 8⟩ ⟨-8, -8, 0, 0⟩ :=
  (HasPlJet.smul jet_C1 ((HasPlJet.const (ePl 1 (restMomentum 1))).mul jet_ePl_curve.bar)).of_eq
    (fun u => by simp only [lR, pauliR, hm])
    (by ext <;> simp [ePl_rest]) (by ext <;> simp [ePl_rest] <;> norm_num)
    (by ext <;> simp [ePl_rest] <;> norm_num)

/-- **The jet of a slot numerator**: `lE k = (1, aₖ + bₖ p'⁰, -bₖ p'¹, 0)`. -/
theorem jet_lE {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) (k : Fin 4) :
    HasPlJet (fun u => lE P z u k) ⟨1, (slotA z k : ℂ) + (slotB z k : ℂ), 0, 0⟩
      ⟨0, 0, -2 * (slotB z k : ℂ), 0⟩ ⟨0, 2 * (slotB z k : ℂ), 0, 0⟩ :=
  (HasPlJet.mk (HasJet2.const 1) ((HasJet2.const (slotA z k : ℂ)).add
    (jet_P0.const_mul (slotB z k : ℂ))) (jet_P1.const_mul (slotB z k : ℂ)).neg
    (HasJet2.const 0)).of_eq
    (fun u => by
      ext <;> simp [lE, ePl, ladderQ_apply, hm, restMomentum])
    (by ext <;> simp) (by ext <;> simp [mul_comm]) (by ext <;> simp [mul_comm])

/-- **The jet of `4m + 8 q̸ₖ`.** -/
theorem jet_wPl {P : Params} (hm : P.m = 1) (z : Fin 8 → ℝ) (k : Fin 4) :
    HasPlJet (fun u => wPl P.m (ladderQ P z u k))
      ⟨4, -8 * ((slotA z k : ℂ) + (slotB z k : ℂ)), 0, 0⟩
      ⟨0, 0, 16 * (slotB z k : ℂ), 0⟩ ⟨0, -16 * (slotB z k : ℂ), 0, 0⟩ :=
  (HasPlJet.mk (HasJet2.const 4) (((HasJet2.const (slotA z k : ℂ)).add
    (jet_P0.const_mul (slotB z k : ℂ))).const_mul (-8))
    ((jet_P1.const_mul (slotB z k : ℂ)).const_mul 8) (HasJet2.const 0)).of_eq
    (fun u => by
      ext <;> simp [wPl, ladderQ_apply, hm, restMomentum])
    (by ext <;> simp) (by ext <;> simp; ring) (by ext <;> simp; ring)

/-! ### Jet arithmetic for the contraction patterns -/

/-- A second-order jet `(x₀, x₁, x₂)` of planar elements. -/
structure PJ where
  /-- The value. -/
  j0 : Pl
  /-- The first-order coefficient. -/
  j1 : Pl
  /-- The second-order coefficient. -/
  j2 : Pl

namespace PJ

/-- The product of jets. -/
def mul (x y : PJ) : PJ := ⟨x.j0 * y.j0, x.j0 * y.j1 + x.j1 * y.j0, x.j0 * y.j2 + x.j1 * y.j1 +
    x.j2 * y.j0⟩
/-- The grade involution of a jet. -/
def bar (x : PJ) : PJ := ⟨Pl.bar x.j0, Pl.bar x.j1, Pl.bar x.j2⟩
/-- The contraction `Γ` of a jet. -/
def gam (x : PJ) : PJ := ⟨Pl.gam x.j0, Pl.gam x.j1, Pl.gam x.j2⟩
/-- The contraction `Γ_T` of a jet. -/
def gamT (x : PJ) : PJ := ⟨Pl.gamT x.j0, Pl.gamT x.j1, Pl.gamT x.j2⟩
/-- A constant jet. -/
def c (x : Pl) : PJ := ⟨x, 0, 0⟩
/-- The value of the scalar part. -/
def s0 (x : PJ) : ℂ := x.j0.s
/-- The first-order coefficient of the scalar part. -/
def s1 (x : PJ) : ℂ := x.j1.s
/-- The second-order coefficient of the scalar part. -/
def s2 (x : PJ) : ℂ := x.j2.s

end PJ

/-- A planar function with the jet `x`. -/
def HasPJ (X : ℝ → Pl) (x : PJ) : Prop := HasPlJet X x.j0 x.j1 x.j2

namespace HasPJ

variable {X Y : ℝ → Pl} {x y : PJ}

theorem mul (hX : HasPJ X x) (hY : HasPJ Y y) : HasPJ (fun u => X u * Y u) (x.mul y) :=
  HasPlJet.mul hX hY

theorem bar (hX : HasPJ X x) : HasPJ (fun u => Pl.bar (X u)) x.bar := HasPlJet.bar hX

theorem gam (hX : HasPJ X x) : HasPJ (fun u => Pl.gam (X u)) x.gam := HasPlJet.gam hX

theorem gamT (hX : HasPJ X x) : HasPJ (fun u => Pl.gamT (X u)) x.gamT := HasPlJet.gamT hX

theorem const (a : Pl) : HasPJ (fun _ => a) (PJ.c a) := HasPlJet.const a

theorem s (hX : HasPJ X x) : HasJet2 (fun u => (X u).s) x.j0.s x.j1.s x.s2 := hX.1

end HasPJ

section Patterns

variable {Q₀ Q₁ R Y₀ Y₁ Y₂ Y₃ : ℝ → Pl} {q₀ q₁ r y₀ y₁ y₂ y₃ : PJ}

/-- The second-order coefficient of `lwPl` from the jets of its arguments. -/
def lwJk (sel : PJ → ℂ) (q₀ q₁ r y₀ y₁ y₂ y₃ : PJ) : ℂ :=
  4 * sel (((q₀.gam.mul y₀).mul ((y₁.mul (PJ.c g0)).mul y₂).gam).mul y₃) +
    4 * sel (((q₁.gam.mul y₀).mul ((y₁.mul (PJ.c g1)).mul y₂).gam).mul y₃) -
    8 * sel (((r.gamT.mul y₀.bar).mul (y₁.mul y₂.bar).gamT.bar).mul y₃)

/-- The second-order coefficient of the pattern. -/
abbrev lwJ (q₀ q₁ r y₀ y₁ y₂ y₃ : PJ) : ℂ := lwJk PJ.s2 q₀ q₁ r y₀ y₁ y₂ y₃

theorem hasJet2_lwPl (hQ₀ : HasPJ Q₀ q₀) (hQ₁ : HasPJ Q₁ q₁)
    (hR : HasPJ R r) (hY₀ : HasPJ Y₀ y₀)
    (hY₁ : HasPJ Y₁ y₁) (hY₂ : HasPJ Y₂ y₂)
    (hY₃ : HasPJ Y₃ y₃) :
    HasJet2 (fun u => lwPl (Q₀ u) (Q₁ u) (R u) (Y₀ u) (Y₁ u) (Y₂ u) (Y₃ u))
      (lwJk PJ.s0 q₀ q₁ r y₀ y₁ y₂ y₃) (lwJk PJ.s1 q₀ q₁ r y₀ y₁ y₂ y₃)
      (lwJ q₀ q₁ r y₀ y₁ y₂ y₃) := by
  have h1 := ((((hQ₀.gam.mul hY₀).mul ((hY₁.mul (HasPJ.const g0)).mul hY₂).gam).mul hY₃).s)
  have h2 := ((((hQ₁.gam.mul hY₀).mul ((hY₁.mul (HasPJ.const g1)).mul hY₂).gam).mul hY₃).s)
  have h3 := ((((hR.gamT.mul hY₀.bar).mul (hY₁.mul hY₂.bar).gamT.bar).mul hY₃).s)
  exact ((h1.const_mul 4).add (h2.const_mul 4)).sub (h3.const_mul 8)

/-- The second-order coefficient of `omLPl` from the jets of its arguments. -/
def omLJk (sel : PJ → ℂ) (q₀ q₁ r z : PJ) : ℂ :=
  4 * sel ((q₀.gam.mul (PJ.c g0)).mul z) + 4 * sel ((q₁.gam.mul (PJ.c g1)).mul z) -
    8 * sel (r.gamT.mul z)

/-- The second-order coefficient of the pattern. -/
abbrev omLJ (q₀ q₁ r z : PJ) : ℂ := omLJk PJ.s2 q₀ q₁ r z

theorem hasJet2_omLPl {Z : ℝ → Pl} {z : PJ} (hQ₀ : HasPJ Q₀ q₀)
    (hQ₁ : HasPJ Q₁ q₁) (hR : HasPJ R r)
    (hZ : HasPJ Z z) :
    HasJet2 (fun u => omLPl (Q₀ u) (Q₁ u) (R u) (Z u)) (omLJk PJ.s0 q₀ q₁ r z)
      (omLJk PJ.s1 q₀ q₁ r z) (omLJ q₀ q₁ r z) := by
  have h1 := ((hQ₀.gam.mul (HasPJ.const g0)).mul hZ).s
  have h2 := ((hQ₁.gam.mul (HasPJ.const g1)).mul hZ).s
  have h3 := (hR.gamT.mul hZ).s
  exact ((h1.const_mul 4).add (h2.const_mul 4)).sub (h3.const_mul 8)

/-- The second-order coefficient of `omRPl` from the jets of its arguments. -/
def omRJk (sel : PJ → ℂ) (q₀ q₁ r z : PJ) : ℂ :=
  4 * sel ((q₀.gam.mul z).mul (PJ.c g0)) + 4 * sel ((q₁.gam.mul z).mul (PJ.c g1)) -
    8 * sel (r.gamT.mul z.bar)

/-- The second-order coefficient of the pattern. -/
abbrev omRJ (q₀ q₁ r z : PJ) : ℂ := omRJk PJ.s2 q₀ q₁ r z

theorem hasJet2_omRPl {Z : ℝ → Pl} {z : PJ} (hQ₀ : HasPJ Q₀ q₀)
    (hQ₁ : HasPJ Q₁ q₁) (hR : HasPJ R r)
    (hZ : HasPJ Z z) :
    HasJet2 (fun u => omRPl (Q₀ u) (Q₁ u) (R u) (Z u)) (omRJk PJ.s0 q₀ q₁ r z)
      (omRJk PJ.s1 q₀ q₁ r z) (omRJ q₀ q₁ r z) := by
  have h1 := ((hQ₀.gam.mul hZ).mul (HasPJ.const g0)).s
  have h2 := ((hQ₁.gam.mul hZ).mul (HasPJ.const g1)).s
  have h3 := (hR.gamT.mul hZ.bar).s
  exact ((h1.const_mul 4).add (h2.const_mul 4)).sub (h3.const_mul 8)

/-- The second-order coefficient of `f3Pl` from the jets of its arguments. -/
def f3Jk (sel : PJ → ℂ) (q₀ q₁ r y₁ y₂ : PJ) : ℂ :=
  4 * sel (q₀.gam.gam.mul ((y₁.mul (PJ.c g0)).mul y₂).gam) +
    4 * sel (q₁.gam.gam.mul ((y₁.mul (PJ.c g1)).mul y₂).gam) -
    8 * sel (r.gamT.gamT.mul (y₁.mul y₂.bar).gamT.bar)

/-- The second-order coefficient of the pattern. -/
abbrev f3J (q₀ q₁ r y₁ y₂ : PJ) : ℂ := f3Jk PJ.s2 q₀ q₁ r y₁ y₂

theorem hasJet2_f3Pl (hQ₀ : HasPJ Q₀ q₀) (hQ₁ : HasPJ Q₁ q₁)
    (hR : HasPJ R r) (hY₁ : HasPJ Y₁ y₁)
    (hY₂ : HasPJ Y₂ y₂) :
    HasJet2 (fun u => f3Pl (Q₀ u) (Q₁ u) (R u) (Y₁ u) (Y₂ u)) (f3Jk PJ.s0 q₀ q₁ r y₁ y₂)
      (f3Jk PJ.s1 q₀ q₁ r y₁ y₂) (f3J q₀ q₁ r y₁ y₂) := by
  have h1 := (hQ₀.gam.gam.mul ((hY₁.mul (HasPJ.const g0)).mul hY₂).gam).s
  have h2 := (hQ₁.gam.gam.mul ((hY₁.mul (HasPJ.const g1)).mul hY₂).gam).s
  have h3 := (hR.gamT.gamT.mul (hY₁.mul hY₂.bar).gamT.bar).s
  exact ((h1.const_mul 4).add (h2.const_mul 4)).sub (h3.const_mul 8)

end Patterns

/-! ### The second-order coefficients of the patterns -/

/-- The jet of `lQ0` at `m = 1`. -/
def qJ0 : PJ := ⟨0, 0, ⟨-16, -16, 0, 0⟩⟩
/-- The jet of `lQ1` at `m = 1`. -/
def qJ1 : PJ := ⟨0, 0, 0⟩
/-- The jet of `lR` at `m = 1`. -/
def rJ : PJ := ⟨0, ⟨0, 0, 8, 8⟩, ⟨-8, -8, 0, 0⟩⟩
/-- The jet of a slot numerator `(1, a + b p'⁰, -b p'¹, 0)`, with `α = a + b`, `β = b`. -/
def eJ (α β : ℂ) : PJ := ⟨⟨1, α, 0, 0⟩, ⟨0, 0, -2 * β, 0⟩, ⟨0, 2 * β, 0, 0⟩⟩
/-- The jet of `4 + 8 q̸` for `q = a p + b p'`, with `α = a + b`, `β = b`. -/
def wJ (α β : ℂ) : PJ := ⟨⟨4, -8 * α, 0, 0⟩, ⟨0, 0, 16 * β, 0⟩, ⟨0, -16 * β, 0, 0⟩⟩

section Values

variable (α₀ α₁ α₂ α₃ β₀ β₁ β₂ β₃ : ℂ)

theorem lwJ_T1 : lwJ qJ0 qJ1 rJ (eJ α₀ β₀) (eJ α₁ β₁) (eJ α₂ β₂) (eJ α₃ β₃) =
    -512 * (α₀ * α₁ * α₂ * β₃ - α₀ * α₁ * α₂ + α₀ * α₁ * α₃ * β₂ + 2 * α₀ * α₁ * α₃ - α₀ * α₁ -
      α₀ * α₂ * α₃ * β₁ + 2 * α₀ * α₂ * α₃ - α₀ * α₂ + α₀ * α₃ - α₀ * β₃ - α₀ - α₁ * α₂ * α₃ * β₀ -
      α₁ * α₂ * α₃ + α₁ * α₂ - α₁ * α₃ + α₁ * β₂ + 2 * α₁ - α₂ * α₃ - α₂ * β₁ + 2 * α₂ + α₃ * β₀ -
      α₃) := by
  simp [lwJ, lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c,
    PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem lwJ_01 : lwJ qJ0 qJ1 rJ (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) (eJ α₂ β₂) (eJ α₃ β₃) =
    1024 * (α₂ * α₃ - 2 * α₂ + α₃) := by
  simp [lwJ, lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c,
    PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem omLJ_02 : omLJ qJ0 qJ1 rJ ((wJ α₁ β₁).mul (eJ α₃ β₃)) =
    1024 * (2 * α₁ * β₃ - 2 * α₁ - 2 * α₃ * β₁ + α₃) := by
  simp [omLJ, omLJk, PJ.mul, PJ.gam, PJ.gamT, PJ.c,
    PJ.s2, eJ, wJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem f3J_03 : f3J qJ0 qJ1 rJ (eJ α₁ β₁) (eJ α₂ β₂) =
    -1024 * (α₁ * α₂ - α₁ * β₂ - 4 * α₁ + α₂ * β₁ - 4 * α₂) := by
  simp [f3J, f3Jk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c,
    PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem lwJ_12 : lwJ qJ0 qJ1 rJ (eJ α₀ β₀) (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) (eJ α₃ β₃) =
    -1024 * (α₀ * α₃ - α₀ * β₃ - α₀ + α₃ * β₀ - α₃) := by
  simp [lwJ, lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c,
    PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem omRJ_13 : omRJ qJ0 qJ1 rJ ((eJ α₀ β₀).mul (wJ α₂ β₂)) =
    1024 * (2 * α₀ * β₂ + α₀ - 2 * α₂ * β₀ - 2 * α₂) := by
  simp [omRJ, omRJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c,
    PJ.s2, eJ, wJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem lwJ_23 : lwJ qJ0 qJ1 rJ (eJ α₀ β₀) (eJ α₁ β₁) (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) =
    1024 * (α₀ * α₁ + α₀ - 2 * α₁) := by
  simp [lwJ, lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c,
    PJ.s2, eJ, qJ0, qJ1, rJ, g0, g1]
  ring

theorem lwJ_T3 : lwJ qJ0 qJ1 rJ (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) = 0 := by
  simp [lwJ, lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c,
    PJ.s2, qJ0, qJ1, rJ, g0, g1]
  norm_num

theorem omLJ_T3 : omLJ qJ0 qJ1 rJ (PJ.c 1) = 0 := by
  simp [omLJ, omLJk, PJ.mul, PJ.gam, PJ.gamT, PJ.c,
    PJ.s2, qJ0, qJ1, rJ, g0, g1]
  norm_num

theorem f3J_T3 : f3J qJ0 qJ1 rJ (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) = 0 := by
  simp [f3J, f3Jk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c,
    PJ.s2, qJ0, qJ1, rJ, g0, g1]
  norm_num

/-! The values and first-order coefficients of all the patterns vanish. -/

@[simp] theorem lwJk_T1_s0 :
    lwJk PJ.s0 qJ0 qJ1 rJ (eJ α₀ β₀) (eJ α₁ β₁) (eJ α₂ β₂) (eJ α₃ β₃) = 0 := by
  simp [lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem lwJk_T1_s1 :
    lwJk PJ.s1 qJ0 qJ1 rJ (eJ α₀ β₀) (eJ α₁ β₁) (eJ α₂ β₂) (eJ α₃ β₃) = 0 := by
  simp [lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem lwJk_01_s0 :
    lwJk PJ.s0 qJ0 qJ1 rJ (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) (eJ α₂ β₂) (eJ α₃ β₃) = 0 := by
  simp [lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem lwJk_01_s1 :
    lwJk PJ.s1 qJ0 qJ1 rJ (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) (eJ α₂ β₂) (eJ α₃ β₃) = 0 := by
  simp [lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem omLJk_02_s0 : omLJk PJ.s0 qJ0 qJ1 rJ ((wJ α₁ β₁).mul (eJ α₃ β₃)) = 0 := by
  simp [omLJk, PJ.mul, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, wJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem omLJk_02_s1 : omLJk PJ.s1 qJ0 qJ1 rJ ((wJ α₁ β₁).mul (eJ α₃ β₃)) = 0 := by
  simp [omLJk, PJ.mul, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, wJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem f3Jk_03_s0 : f3Jk PJ.s0 qJ0 qJ1 rJ (eJ α₁ β₁) (eJ α₂ β₂) = 0 := by
  simp [f3Jk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem f3Jk_03_s1 : f3Jk PJ.s1 qJ0 qJ1 rJ (eJ α₁ β₁) (eJ α₂ β₂) = 0 := by
  simp [f3Jk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem lwJk_12_s0 :
    lwJk PJ.s0 qJ0 qJ1 rJ (eJ α₀ β₀) (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) (eJ α₃ β₃) = 0 := by
  simp [lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem lwJk_12_s1 :
    lwJk PJ.s1 qJ0 qJ1 rJ (eJ α₀ β₀) (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) (eJ α₃ β₃) = 0 := by
  simp [lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem omRJk_13_s0 : omRJk PJ.s0 qJ0 qJ1 rJ ((eJ α₀ β₀).mul (wJ α₂ β₂)) = 0 := by
  simp [omRJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ, wJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem omRJk_13_s1 : omRJk PJ.s1 qJ0 qJ1 rJ ((eJ α₀ β₀).mul (wJ α₂ β₂)) = 0 := by
  simp [omRJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ, wJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem lwJk_23_s0 :
    lwJk PJ.s0 qJ0 qJ1 rJ (eJ α₀ β₀) (eJ α₁ β₁) (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) = 0 := by
  simp [lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0, eJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem lwJk_23_s1 :
    lwJk PJ.s1 qJ0 qJ1 rJ (eJ α₀ β₀) (eJ α₁ β₁) (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) = 0 := by
  simp [lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1, eJ,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem lwJk_T3_s0 : lwJk PJ.s0 qJ0 qJ1 rJ (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) (PJ.c ⟨2, 0, 0,
    0⟩) (PJ.c 1) = 0 := by
  simp [lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem lwJk_T3_s1 : lwJk PJ.s1 qJ0 qJ1 rJ (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) (PJ.c ⟨2, 0, 0,
    0⟩) (PJ.c 1) = 0 := by
  simp [lwJk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem omLJk_T3_s0 : omLJk PJ.s0 qJ0 qJ1 rJ (PJ.c 1) = 0 := by
  simp [omLJk, PJ.mul, PJ.gam, PJ.gamT, PJ.c, PJ.s0,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem omLJk_T3_s1 : omLJk PJ.s1 qJ0 qJ1 rJ (PJ.c 1) = 0 := by
  simp [omLJk, PJ.mul, PJ.gam, PJ.gamT, PJ.c, PJ.s1,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem f3Jk_T3_s0 : f3Jk PJ.s0 qJ0 qJ1 rJ (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) = 0 := by
  simp [f3Jk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s0,
    qJ0, qJ1, rJ, g0, g1]

@[simp] theorem f3Jk_T3_s1 : f3Jk PJ.s1 qJ0 qJ1 rJ (PJ.c ⟨2, 0, 0, 0⟩) (PJ.c 1) = 0 := by
  simp [f3Jk, PJ.mul, PJ.bar, PJ.gam, PJ.gamT, PJ.c, PJ.s1,
    qJ0, qJ1, rJ, g0, g1]

end Values

end QED.TwoLoop.UnitLGraphTrace

end
