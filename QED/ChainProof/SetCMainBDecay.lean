/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainBDecayLem
public import QED.ChainProof.SetCMainBWickInt
public import QED.ChainProof.HCLimitBounds
import QED.Integration.LoopBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Set (c), the bubble classes: the outer factor decays in the outer energies

Helper level for set (c), the bubble classes `QED.ChainProof.SetCLink.repB i`, at fixed
`ε > 0`. For all twelve orbits the outer factor `outerBW i` and the photon momentum `kBW i`
through the bubble satisfy the decay condition `OuterDecay'` of
`QED/ChainProof/SetCMainBDecayBub.lean`:

* the kernel facts `mv_photD_one`, `pmv_photD_zero`, `rows_photD`: the two photon lines at the
  bubble carry `K` and `-K`, `K` is `±ℓ₀` or `±(ℓ₁ - ℓ₀)` plus external momenta, and the third
  photon line carries the other one;
* `exists_norm_lineProd_repD_le`, `exists_norm_outerBW_le`: at fixed outer spatial momenta the
  electron propagators are bounded and each photon propagator decays like `(1 + |E|)⁻⁴` in its
  energy `E`;
* **`outerDecay'_outerBW`**: `|O| (1 + ‖K‖)⁶ ≤ C (1 + |t₀|)⁻² (1 + |t₁ - t₀|)⁻²`.

With continuity (`continuous_outerBW`, `continuous_kBW`) and (T₉′) of `repB i` transported to the
nested routing (`jointEnergyFirstIntegrable_nestB_repB`, from
`QED.ChainProof.SetCLink.classIntA_repB`), this gives **`contractionValue_repB_eq_outerBub`**:
the graded value of `repB i` is the joint energy-first integral at two loops of
`outerBub P (outerBW i) (kBW i)`, which is integrable in both stages.
-/

@[expose] public section

open Complex MeasureTheory
open QED.WickModel (Params Contraction FermionLine PhotonLine Line lineMomentum₂
  photonMomentum₂)

namespace QED.ChainProof.SetCMainB

open QED.ChainProof.SetCLink QED.ChainProof.SetALink QED.GradedProof.X0
open QED.ChainProof.SetCMain (photD)
open QED.ChainProof.Enum (pc)

/-! ### The photon lines of `repD i 0` -/

theorem mv_photD_one : ∀ i : Fin 12,
    mv (repD i 0) (.inr (photD i 0 1)) = -mv (repD i 0) (.inr (photD i 0 0)) := by
  decide +kernel

theorem pmv_photD_zero : ∀ i : Fin 12,
    pmv (repD i 0) (pc kD 5 0) = mv (repD i 0) (.inr (photD i 0 0)) := by
  decide +kernel

theorem rows_photD : ∀ i : Fin 12,
    (mv (repD i 0) (.inr (photD i 0 0)) 0 = 1 ∧ mv (repD i 0) (.inr (photD i 0 0)) 1 = 0 ∧
      mv (repD i 0) (.inr (photD i 0 2)) 0 = -1 ∧ mv (repD i 0) (.inr (photD i 0 2)) 1 = 1) ∨
    (mv (repD i 0) (.inr (photD i 0 0)) 0 = -1 ∧ mv (repD i 0) (.inr (photD i 0 0)) 1 = 1 ∧
      mv (repD i 0) (.inr (photD i 0 2)) 0 = 1 ∧ mv (repD i 0) (.inr (photD i 0 2)) 1 = 0) := by
  decide +kernel

/-! ### Line momenta at fixed outer spatial momenta -/

/-- The energy of the momentum of an integer vector at the outer energies `t'`. -/
noncomputable def enr (v : Fin 4 → ℤ) (t' : Fin 2 → ℝ) (p q : Fin 4 → ℝ) : ℝ :=
  (v 0 : ℝ) * t' 0 + (v 1 : ℝ) * t' 1 + ((v 2 : ℝ) * p 0 + (v 3 : ℝ) * q 0)

/-- The spatial part of the momentum of an integer vector at the outer spatial momenta `v'`. -/
noncomputable def spr (v' : Fin 2 → Fin 3 → ℝ) (p q : Fin 4 → ℝ) (v : Fin 4 → ℤ) :
    Fin 3 → ℝ :=
  Fin.tail (mvReal (fun s => (Fin.cons 0 (v' s) : Fin 4 → ℝ)) p q v)

theorem lineMomentum₂_cons {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0) (t' : Fin 2 → ℝ)
    (v' : Fin 2 → Fin 3 → ℝ) (l : Line C) :
    lineMomentum₂ C pOut pIn kIn (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) l =
      Fin.cons (enr (mv C l) t' (pIn 0) (kIn 0)) (spr v' (pIn 0) (kIn 0) (mv C l)) := by
  rw [lineMomentum₂_eq_mv C pOut pIn kIn hmom, mvReal_cons]
  rfl

theorem enr_neg (v : Fin 4 → ℤ) (t' : Fin 2 → ℝ) (p q : Fin 4 → ℝ) :
    enr (-v) t' p q = -enr v t' p q := by
  simp only [enr, Pi.neg_apply, Int.cast_neg]
  ring

variable {F : Type} (P : Params) (Φ : Lepton.Flavors F) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}

theorem norm_one_div_I_mul (z : ℂ) : ‖(1 / I) * z‖ = ‖z‖ := by
  rw [norm_mul, norm_div, norm_one, norm_I, div_one, one_mul]

/-- **The line factors of `repD i 0`** at fixed outer spatial momenta: bounded by the product of
`(1 + |E_r|)⁻⁴` over the three photon lines, uniformly in the indices. -/
theorem exists_norm_lineProd_repD_le (hε : 0 < P.ε) (hmom : pOut 0 = pIn 0 + kIn 0)
    (i : Fin 12) (v' : Fin 2 → Fin 3 → ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ (α β : Wick.FermionVertex kD → Fin 4) (lor : Wick.PhotonSlot kD → Fin 4)
      (t' : Fin 2 → ℝ), ‖lineProd P.ε (dNum P Φ α β lor) (dMs P Φ)
        (lineMomentum₂ (repD i 0) pOut pIn kIn fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ))‖ ≤
        B * ∏ r : Fin 3,
          ((1 + |enr (mv (repD i 0) (.inr (photD i 0 r))) t' (pIn 0) (kIn 0)|) ^ 4)⁻¹ := by
  set C := repD i 0
  set p := pIn 0
  set q := kIn 0
  obtain ⟨CE, hCE0, hCE⟩ := exists_uniform_bound (ι := FermionLine C) (X := Fin 4 × Fin 4 × ℝ)
    (f := fun f x => ‖QED.OneLoop.electronPropagator (Φ.mass Φ.openLine) P.ε
      (Fin.cons x.2.2 (spr v' p q (mv C (.inl f)))) x.1 x.2.1‖)
    (g := fun _ => 1) (fun _ => zero_le_one) (fun f => by
      obtain ⟨c, -, hc⟩ := exists_norm_electronPropagator_cons_apply_le (Φ.mass Φ.openLine) hε
        (spr v' p q (mv C (.inl f)))
      exact ⟨c, fun x => hc x.1 x.2.1 x.2.2⟩)
  obtain ⟨CP, hCP0, hCP⟩ := exists_uniform_bound (ι := Fin 3) (X := Fin 4 × Fin 4 × ℝ)
    (f := fun r x => ‖QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
      (Fin.cons x.2.2 (spr v' p q (mv C (.inr (photD i 0 r))))) x.1 x.2.1‖)
    (g := fun x => ((1 + |x.2.2|) ^ 4)⁻¹) (fun _ => by positivity) (fun r => by
      obtain ⟨c, -, hc⟩ := exists_norm_photonPropagator_cons_le P.mγ P.Λ hε
        (spr v' p q (mv C (.inr (photD i 0 r))))
      exact ⟨c, fun x => hc x.1 x.2.1 x.2.2⟩)
  refine ⟨CE ^ Fintype.card (FermionLine C) * CP ^ 3, by positivity, fun α β lor t' => ?_⟩
  rw [lineProd_eq_props P Φ hε.ne', norm_mul, norm_prod, norm_prod, prod_photD0 i]
  have he : ∏ f : FermionLine C, ‖(1 / I) * QED.OneLoop.electronPropagator
      (Φ.mass Φ.openLine) P.ε (lineMomentum₂ C pOut pIn kIn
        (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) (.inl f)) (β f.1) (α f.tail)‖ ≤
      CE ^ Fintype.card (FermionLine C) := by
    rw [← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun f _ => ?_
    rw [norm_one_div_I_mul, lineMomentum₂_cons C hmom]
    simpa using hCE f (β f.1, α f.tail, enr (mv C (.inl f)) t' p q)
  have hp : ∏ r : Fin 3, ‖(1 / I) * QED.OneLoop.photonPropagator P.mγ P.Λ P.ε
      (lineMomentum₂ C pOut pIn kIn (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ))
        (.inr (photD i 0 r))) (lor (photD i 0 r).1) (lor (photD i 0 r).head)‖ ≤
      CP ^ 3 * ∏ r : Fin 3, ((1 + |enr (mv C (.inr (photD i 0 r))) t' p q|) ^ 4)⁻¹ := by
    have h3 : CP ^ 3 = ∏ _r : Fin 3, CP := by simp
    rw [h3, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => ?_
    rw [norm_one_div_I_mul, lineMomentum₂_cons C hmom]
    exact hCP r ((lor (photD i 0 r).1), lor (photD i 0 r).head,
      enr (mv C (.inr (photD i 0 r))) t' p q)
  calc _ ≤ CE ^ Fintype.card (FermionLine C) *
        (CP ^ 3 * ∏ r : Fin 3, ((1 + |enr (mv C (.inr (photD i 0 r))) t' p q|) ^ 4)⁻¹) :=
        mul_le_mul he hp (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem norm_extI_le {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (αOut βIn μ : Fin 1 → Fin 4) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) : ‖extI C αOut βIn μ α β lor‖ ≤ 1 := by
  unfold extI
  split_ifs <;> simp

theorem norm_openIns_le (ρ σ : Fin 4) (lor : Wick.PhotonSlot kD → Fin 4) (k : Fin 4 → ℝ) :
    ‖openIns ρ σ lor k‖ ≤ 1 := by
  unfold openIns
  split_ifs <;> simp

/-- **The outer factor of `repD i 0`** at fixed outer spatial momenta: bounded by the product of
`(1 + |E_r|)⁻⁴` over the three photon lines. -/
theorem exists_norm_outerBW_le (hε : 0 < P.ε) (hmom : pOut 0 = pIn 0 + kIn 0) (i : Fin 12)
    (αOut βIn μ : Fin 1 → Fin 4) (v' : Fin 2 → Fin 3 → ℝ) (ρ σ : Fin 4) :
    ∃ B, 0 ≤ B ∧ ∀ t' : Fin 2 → ℝ,
      ‖outerBW P Φ i pOut pIn kIn αOut βIn μ (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ‖
        ≤ B * ∏ r : Fin 3,
          ((1 + |enr (mv (repD i 0) (.inr (photD i 0 r))) t' (pIn 0) (kIn 0)|) ^ 4)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_lineProd_repD_le P Φ hε hmom i v'
  set G := ∑ α, ∑ β, ∑ lor, ‖gV P.e α β lor‖
  have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨‖((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ))⁻¹‖ * (G * B), by positivity, fun t' => ?_⟩
  set Pr := ∏ r : Fin 3,
    ((1 + |enr (mv (repD i 0) (.inr (photD i 0 r))) t' (pIn 0) (kIn 0)|) ^ 4)⁻¹
  have hPr : 0 ≤ Pr := Finset.prod_nonneg fun _ _ => by positivity
  unfold outerBW insD
  rw [norm_neg, norm_mul]
  have hsum : ‖∑ α, ∑ β, ∑ lor, extI (repD i 0) αOut βIn μ α β lor *
      (openIns ρ σ lor (photonMomentum₂ (repD i 0) kIn (lineMomentum₂ (repD i 0) pOut pIn kIn
        fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) (pc kD 5 0)) *
        (gV P.e α β lor * lineProd P.ε (dNum P Φ α β lor) (dMs P Φ)
          (lineMomentum₂ (repD i 0) pOut pIn kIn
            fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ))))‖ ≤
      ∑ α, ∑ β, ∑ lor, ‖gV P.e α β lor‖ * (B * Pr) := by
    refine norm_sum_le_of_le _ fun α _ => norm_sum_le_of_le _ fun β _ =>
      norm_sum_le_of_le _ fun lor _ => ?_
    rw [norm_mul, norm_mul, norm_mul]
    have e1 := norm_extI_le (repD i 0) αOut βIn μ α β lor
    have e2 := norm_openIns_le ρ σ lor (photonMomentum₂ (repD i 0) kIn
      (lineMomentum₂ (repD i 0) pOut pIn kIn fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ))
        (pc kD 5 0))
    have e3 := mul_le_mul_of_nonneg_left (hB α β lor t') (norm_nonneg (gV P.e α β lor))
    have h0 : 0 ≤ ‖gV P.e α β lor‖ * (B * Pr) := by positivity
    calc _ ≤ 1 * (1 * (‖gV P.e α β lor‖ * (B * Pr))) :=
          mul_le_mul e1 (mul_le_mul e2 e3 (by positivity) zero_le_one) (by positivity)
            zero_le_one
      _ = _ := by ring
  have hG' : ∑ α, ∑ β, ∑ lor, ‖gV P.e α β lor‖ * (B * Pr) = G * (B * Pr) := by
    simp only [G, Finset.sum_mul]
  calc _ ≤ ‖((((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ))⁻¹‖ * (G * (B * Pr)) :=
        mul_le_mul_of_nonneg_left (hsum.trans hG'.le) (norm_nonneg _)
    _ = _ := by ring

/-! ### The decay -/

theorem one_add_norm_cons_le_mul (E : ℝ) (w : Fin 3 → ℝ) :
    1 + ‖(Fin.cons E w : Fin 4 → ℝ)‖ ≤ (1 + ‖w‖) * (1 + |E|) := by
  have h := QED.Integration.norm_finCons_le E w
  nlinarith [norm_nonneg w, abs_nonneg E]

theorem inv_one_add_abs_le_one (y : ℝ) : (1 + |y|)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by linarith [abs_nonneg y])

/-- **The decay of the outer factor of `repB i`** (twelve orbits, `ε > 0`). -/
theorem outerDecay'_outerBW (hε : 0 < P.ε) (hmom : pOut 0 = pIn 0 + kIn 0) (i : Fin 12)
    (αOut βIn μ : Fin 1 → Fin 4) :
    OuterDecay' (outerBW P Φ i pOut pIn kIn αOut βIn μ) (kBW i pOut pIn kIn) := by
  intro v' ρ σ
  obtain ⟨B, hB0, hB⟩ := exists_norm_outerBW_le P Φ hε hmom i αOut βIn μ v' ρ σ
  set p := pIn 0
  set q := kIn 0
  set v0 := mv (repD i 0) (.inr (photD i 0 0))
  set v2 := mv (repD i 0) (.inr (photD i 0 2))
  set w0 := spr v' p q v0
  set c0 := (v0 2 : ℝ) * p 0 + (v0 3 : ℝ) * q 0
  set c2 := (v2 2 : ℝ) * p 0 + (v2 3 : ℝ) * q 0
  set D := B * (1 + ‖w0‖) ^ 6 * ((1 + |c0|) ^ 2 * (1 + |c2|) ^ 2)
  refine ⟨fun t' => D * shearBound t', integrable_shearBound.const_mul D, fun t' => ?_⟩
  set y0 := (v0 0 : ℝ) * t' 0 + (v0 1 : ℝ) * t' 1
  set y2 := (v2 0 : ℝ) * t' 0 + (v2 1 : ℝ) * t' 1
  have hE0 : enr v0 t' p q = y0 + c0 := rfl
  have hE2 : enr v2 t' p q = y2 + c2 := rfl
  have hE1 : enr (mv (repD i 0) (.inr (photD i 0 1))) t' p q = -(y0 + c0) := by
    rw [mv_photD_one, enr_neg, hE0]
  have hK : kBW i pOut pIn kIn (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) =
      Fin.cons (y0 + c0) w0 := by
    rw [kBW, photonMomentum₂_eq_pmv _ _ _ _ hmom, pmv_photD_zero, mvReal_cons]
    rfl
  set X := (1 + |y0 + c0|)⁻¹
  set Y := (1 + |y2 + c2|)⁻¹
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hY1 : Y ≤ 1 := inv_one_add_abs_le_one _
  have hXa : X * (1 + |y0 + c0|) = 1 := inv_mul_cancel₀ (by positivity)
  have hO := hB t'
  rw [Fin.prod_univ_three, hE1, abs_neg] at hO
  change _ ≤ B * (((1 + |y0 + c0|) ^ 4)⁻¹ * ((1 + |y0 + c0|) ^ 4)⁻¹ * ((1 + |y2 + c2|) ^ 4)⁻¹)
    at hO
  rw [← inv_pow, ← inv_pow] at hO
  have hKb : (1 + ‖kBW i pOut pIn kIn (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ))‖) ^ 6 ≤
      (1 + ‖w0‖) ^ 6 * (1 + |y0 + c0|) ^ 6 := by
    rw [hK, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_norm_cons_le_mul _ _) 6
  have hstep : ‖outerBW P Φ i pOut pIn kIn αOut βIn μ
        (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ)) ρ σ‖ *
      (1 + ‖kBW i pOut pIn kIn (fun s => (Fin.cons (t' s) (v' s) : Fin 4 → ℝ))‖) ^ 6 ≤
      B * (1 + ‖w0‖) ^ 6 * (X ^ 2 * Y ^ 2) := by
    calc _ ≤ B * (X ^ 4 * X ^ 4 * Y ^ 4) * ((1 + ‖w0‖) ^ 6 * (1 + |y0 + c0|) ^ 6) :=
          mul_le_mul hO hKb (by positivity) (by positivity)
      _ = B * (1 + ‖w0‖) ^ 6 * (X ^ 2 * Y ^ 4 * (X * (1 + |y0 + c0|)) ^ 6) := by ring
      _ = B * (1 + ‖w0‖) ^ 6 * (X ^ 2 * Y ^ 4) := by rw [hXa]; ring
      _ ≤ B * (1 + ‖w0‖) ^ 6 * (X ^ 2 * Y ^ 2) := by
          have : Y ^ 4 ≤ Y ^ 2 := pow_le_pow_of_le_one hY0 hY1 (by norm_num)
          gcongr
  refine hstep.trans ?_
  have hXp := QED.ChainProof.HCLimit.inv_one_add_abs_add_le y0 c0
  have hYp := QED.ChainProof.HCLimit.inv_one_add_abs_add_le y2 c2
  have hXY : X ^ 2 * Y ^ 2 ≤ (1 + |c0|) ^ 2 * (1 + |c2|) ^ 2 *
      (((1 + |y0|)⁻¹) ^ 2 * ((1 + |y2|)⁻¹) ^ 2) := by
    calc X ^ 2 * Y ^ 2 ≤ ((1 + |c0|) * (1 + |y0|)⁻¹) ^ 2 * ((1 + |c2|) * (1 + |y2|)⁻¹) ^ 2 := by
          gcongr
      _ = _ := by ring
  have hsb : ((1 + |y0|)⁻¹) ^ 2 * ((1 + |y2|)⁻¹) ^ 2 = shearBound t' := by
    unfold shearBound
    rcases rows_photD i with ⟨a0, a1, b0, b1⟩ | ⟨a0, a1, b0, b1⟩
    · have ey0 : y0 = t' 0 := by simp only [y0, v0, a0, a1]; push_cast; ring
      have ey2 : y2 = t' 1 - t' 0 := by simp only [y2, v2, b0, b1]; push_cast; ring
      rw [ey0, ey2, inv_pow, inv_pow]
    · have ey0 : y0 = t' 1 - t' 0 := by simp only [y0, v0, a0, a1]; push_cast; ring
      have ey2 : y2 = t' 0 := by simp only [y2, v2, b0, b1]; push_cast; ring
      rw [ey0, ey2, inv_pow, inv_pow, mul_comm]
  calc B * (1 + ‖w0‖) ^ 6 * (X ^ 2 * Y ^ 2)
      ≤ B * (1 + ‖w0‖) ^ 6 * ((1 + |c0|) ^ 2 * (1 + |c2|) ^ 2 *
          (((1 + |y0|)⁻¹) ^ 2 * ((1 + |y2|)⁻¹) ^ 2)) := by gcongr
    _ = D * shearBound t' := by rw [hsb]; ring

/-! ### Continuity -/

theorem continuous_mvReal (p q : Fin 4 → ℝ) (v : Fin 4 → ℤ) :
    Continuous fun ℓ' : Fin 2 → Fin 4 → ℝ => mvReal ℓ' p q v := by
  simp only [mvReal, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  fun_prop

theorem continuous_lineMomentum₂ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (hmom : pOut 0 = pIn 0 + kIn 0) (l : Line C) :
    Continuous fun ℓ' : Fin 2 → Fin 4 → ℝ => lineMomentum₂ C pOut pIn kIn ℓ' l := by
  simp only [lineMomentum₂_eq_mv C pOut pIn kIn hmom]
  exact continuous_mvReal _ _ _

/-- The photon momentum through the bubble is continuous in the outer loop momenta. -/
theorem continuous_kBW (hmom : pOut 0 = pIn 0 + kIn 0) (i : Fin 12) :
    Continuous (kBW i pOut pIn kIn) := by
  unfold kBW
  simp only [photonMomentum₂_eq_pmv _ _ _ _ hmom]
  exact continuous_mvReal _ _ _

/-- The outer factor is continuous in the outer loop momenta, for `ε > 0`. -/
theorem continuous_outerBW (hε : 0 < P.ε) (hmom : pOut 0 = pIn 0 + kIn 0) (i : Fin 12)
    (αOut βIn μ : Fin 1 → Fin 4) (ρ σ : Fin 4) :
    Continuous fun ℓ' => outerBW P Φ i pOut pIn kIn αOut βIn μ ℓ' ρ σ := by
  unfold outerBW insD openIns
  simp only [lineProd_eq_props P Φ hε.ne']
  refine (continuous_const.mul (continuous_finsetSum _ fun α _ => continuous_finsetSum _
    fun β _ => continuous_finsetSum _ fun lor _ => ?_)).neg
  refine continuous_const.mul (continuous_const.mul (continuous_const.mul ?_))
  refine (continuous_finsetProd _ fun f _ => ?_).mul (continuous_finsetProd _ fun g _ => ?_)
  · exact continuous_const.mul ((QED.ChainProof.HCLimit.continuous_electronPropagator_comp _ hε
      (continuous_lineMomentum₂ _ hmom (.inl f))).matrix_elem _ _)
  · exact continuous_const.mul (QED.ChainProof.HCLimit.continuous_photonPropagator_comp _ _ hε
      (continuous_lineMomentum₂ _ hmom (.inr g)) _ _)

/-! ### Nested equals joint for the bubble classes -/

/-- **(T₉′) for `repB i` in the nested routing**, from the class obligation `classIntA_repB`. -/
theorem jointEnergyFirstIntegrable_nestB_repB [Fintype F] [DecidableEq F]
    (D : Graded.Counterterms F) (rep : F → F) (hH : IntHypA P Φ D rep) (hΦ : FlavorsLoop P Φ)
    (i : Fin 12) (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable 3
      (nestB P (outerBW P Φ i pOut pIn kIn αOut βIn μ) (kBW i pOut pIn kIn)) := by
  have h := classIntA_repB i P Φ D rep hH pOut pIn kIn hmom αOut βIn μ
  rw [loopCount_repB] at h
  have h2 := QED.TwoLoop.NestedVP.jointEnergyFirstIntegrable_comp_matrix_add 3 _ rotM
    isUnit_det_rotM 0 h
  refine (congrArg _ (funext fun ℓ => ?_)).mp h2
  rw [← rot_eq, integrand_repB P Φ D hH.hε.ne' hΦ i hmom]

variable (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
  (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)

include hm hM₁ hM₂ hPV₁ hPV₂ in
/-- **The value of the bubble classes with the bubble in closed form** (twelve orbits): under
the hypotheses of the class obligations, flavours with the loop sums of `P`, the mass ordering
and the Pauli–Villars conditions of `P`, the graded value of `repB i` is the joint energy-first
integral at two loops of `outerBub P (outerBW i) (kBW i)`, and the latter is integrable in both
stages. -/
theorem contractionValue_repB_eq_outerBub [Fintype F] [DecidableEq F]
    (D : Graded.Counterterms F) (rep : F → F) (hH : IntHypA P Φ D rep) (hΦ : FlavorsLoop P Φ)
    (i : Fin 12) (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.contractionValue P Φ D (repB i) 0 pOut pIn kIn αOut βIn μ =
        QED.TwoLoop.jointEnergyFirstIntegral 2
          (outerBub P (outerBW P Φ i pOut pIn kIn αOut βIn μ) (kBW i pOut pIn kIn)) ∧
      QED.TwoLoop.jointEnergyFirstIntegrable 2
        (outerBub P (outerBW P Φ i pOut pIn kIn αOut βIn μ) (kBW i pOut pIn kIn)) := by
  obtain ⟨h1, h2⟩ := jointEnergyFirstIntegral_nestB' hm hM₁ hM₂ hPV₁ hPV₂ hH.hε
    (continuous_outerBW P Φ hH.hε hmom i αOut βIn μ) (continuous_kBW hmom i)
    (outerDecay'_outerBW P Φ hH.hε hmom i αOut βIn μ)
    (jointEnergyFirstIntegrable_nestB_repB P Φ D rep hH hΦ i hmom αOut βIn μ)
  exact ⟨(contractionValue_repB_eq P Φ D hH.hε.ne' hΦ i hmom αOut βIn μ).trans h1, h2⟩

end QED.ChainProof.SetCMainB

end
