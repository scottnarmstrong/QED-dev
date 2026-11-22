/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBNVBQ
public import QED.ChainProof.SetAKSKDens

/-!
# Set (a), stage D: the photon-mass density with the tilt factor `k²k³ = c²` divided out

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification). The nested forms of stage B3 carry the factor `k²k³` of the
`(2, 3)` entry inside the outer integrands, and read `k` only through `k²k³` and `s = k·k`.
At the tilt `k = tiltVec c s` the factor is `c²`, which cancels the prefactor `1/c²` of
`qDens`. The result is a real density `ksDQ e μ x s u` that no longer depends on the tilt:

* `ksDGA`, `ksDGB`: the outer integrands as functions of `s` (`ksNGA = k²k³ · ksDGA(k·k)`);
* `ksDNestA`, `ksDNestB`: the nested integrals of their flavour sums;
* **`ksD_qDens`**: `qDens = π⁴e⁴/(2π)⁸ (2 ksDNestA + ksDNestB) + σ(e, μ, u) ksMassF e μ x s`;
* **`ksD_ksKDens`**: the subtracted density is `ksDQ(s, u) - ksDQ(0, u)` (real);
* **`ksD_tendsto_integral`**: `∫_a^1 (ksDQ(s, ·) - ksDQ(0, ·)) → e⁴ decT₀ - ∫_{u > 1} (…)`
  as `a → 0⁺`, with no tilt left.

The flavour sum stays inside the integrals: only the flavour sum of the class integrands is
integrable (stage B2).
-/

@[expose] public section

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.GradedProof.RPi4 QED.GradedProof.VP2
open QED.Integration.Feynman (simplexSet simplexPoint)

/-- **The outer `VA` integrand as a function of `s = k·k`** (`k²k³` removed). -/
noncomputable def ksDGA (M u x s : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  y 0 *
    (((y 0 + y 1 + y 2) ^ 2)⁻¹ * (16 * (y 1 / (y 0 + y 1 + y 2)) * (1 - y 1 / (y 0 + y 1 + y 2)) *
        (4 * M ^ 2 - (1 - x) * M ^ 2 +
          (1 - x) * (y 1 / (y 0 + y 1 + y 2)) ^ 2 * s)) /
      (y 1 * (y 0 + y 2) * s / (y 0 + y 1 + y 2) + (y 0 + y 1) * M ^ 2 +
        y 2 * (M ^ 2 / (1 - x) + u / x)) ^ 2 +
     2 * ((y 0 + y 1 + y 2) ^ 3)⁻¹ *
        (-8 * (1 - x) * (y 1 / (y 0 + y 1 + y 2)) * (4 * (y 1 / (y 0 + y 1 + y 2)) - 3)) /
      (y 1 * (y 0 + y 2) * s / (y 0 + y 1 + y 2) + (y 0 + y 1) * M ^ 2 +
        y 2 * (M ^ 2 / (1 - x) + u / x)))

theorem ksD_ksNGA (M u x : ℝ) (k : Fin 4 → ℝ) (y : Fin 3 → ℝ) :
    ksNGA M u x k y = k 2 * k 3 * ksDGA M u x (Minkowski.dot k k) y := by
  simp only [ksNGA, ksDGA, mul_assoc]

/-- The outer `VB` denominator as a function of `s = k·k`. -/
noncomputable def ksDDB (M u : ℝ) (x : Fin 3 → ℝ) (s : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (y 0 + y 1) * M ^ 2 + y 1 * s + y 2 * ksNEB M u x s -
    (y 1 + x 1 / (1 - x 2) * y 2) ^ 2 * s / (y 0 + y 1 + y 2)

/-- **The outer `VB` integrand as a function of `s = k·k`** (`k²k³` removed). -/
noncomputable def ksDGB (M u : ℝ) (x : Fin 3 → ℝ) (s : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  y 2 * (x 2 * (1 - x 2))⁻¹ * (((y 0 + y 1 + y 2) ^ 2)⁻¹ *
      (ksNeB M (ksNSigB0 x y) (ksNSigB1 x y) / ksDDB M u x s y ^ 2 +
        (ksNh00 (ksNSigB1 x y) + 2 * x 2 * ksNh01 (ksNSigB0 x y) (ksNSigB1 x y) +
          x 2 ^ 2 * ksNh11 (ksNSigB0 x y)) / (2 * (y 0 + y 1 + y 2) * ksDDB M u x s y))) +
    ((y 0 + y 1 + y 2) ^ 2)⁻¹ * ksNh11 (ksNSigB0 x y) / (2 * ksDDB M u x s y)

theorem ksD_ksNGB (M u : ℝ) (x : Fin 3 → ℝ) (k : Fin 4 → ℝ) (y : Fin 3 → ℝ) :
    ksNGB M u x k y = k 2 * k 3 * ksDGB M u x (Minkowski.dot k k) y := by
  simp only [ksNGB, ksDGB, ksNDB, ksDDB, mul_assoc]

/-- The real nested integral of the flavour sum of the reduced `VA` integrands. -/
noncomputable def ksDNestA {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (u s : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) 1, x⁻¹ * ∫ y in simplexSet 2,
    ∑ f, Φ.coeff f * ksDGA (Φ.mass f) u x s (simplexPoint y)

/-- The real nested integral of the flavour sum of the reduced `VB` integrands. -/
noncomputable def ksDNestB {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (u s : ℝ) : ℝ :=
  ∫ q in simplexSet 2, (1 - simplexPoint q 2)⁻¹ * ∫ y in simplexSet 2,
    ∑ f, Φ.coeff f * ksDGB (Φ.mass f) u (simplexPoint q) s (simplexPoint y)

theorem ksD_tiltVec_mul {c s : ℝ} : tiltVec c s 2 * tiltVec c s 3 = c ^ 2 := by
  simp only [tiltVec, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem ksD_ksNestA {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (u : ℝ) {c s : ℝ}
    (hs : s ≤ 2 * c ^ 2) : ksNestA Φ u (tiltVec c s) = c ^ 2 * ksDNestA Φ u s := by
  have h : ∀ x y, ∑ f, Φ.coeff f * ksNGA (Φ.mass f) u x (tiltVec c s) y =
      c ^ 2 * ∑ f, Φ.coeff f * ksDGA (Φ.mass f) u x s y := fun x y => by
    simp only [ksD_ksNGA, dot_tiltVec hs, ksD_tiltVec_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring
  simp only [ksNestA, ksDNestA, h, integral_const_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem ksD_ksNestB {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (u : ℝ) {c s : ℝ}
    (hs : s ≤ 2 * c ^ 2) : ksNestB Φ u (tiltVec c s) = c ^ 2 * ksDNestB Φ u s := by
  have h : ∀ x y, ∑ f, Φ.coeff f * ksNGB (Φ.mass f) u x (tiltVec c s) y =
      c ^ 2 * ∑ f, Φ.coeff f * ksDGB (Φ.mass f) u x s y := fun x y => by
    simp only [ksD_ksNGB, dot_tiltVec hs, ksD_tiltVec_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring
  simp only [ksNestB, ksDNestB, h, integral_const_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-- **The reduced photon-mass density** of the configuration `decCfg μ x` (no tilt). -/
noncomputable def ksDQ (e μ x s u : ℝ) : ℝ :=
  π ^ 4 * e ^ 4 / (2 * π) ^ 8 *
      (2 * ksDNestA (decCfg μ x) u s + ksDNestB (decCfg μ x) u s) +
    sigma e μ u * ksMassF e μ x s

/-- **The photon-mass density with `k²k³ = c²` divided out.** -/
theorem ksD_qDens {e μ x c s u : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x) (hc : 0 < c)
    (hs : -(4 * μ ^ 2) < s) (hs2 : s < 2 * c ^ 2) (hu : 0 < u) :
    qDens (decCfg μ x) (fun _ => 0) e μ c s u = (ksDQ e μ x s u : ℂ) := by
  rw [ksB_qDens_real he hμ hx hc hs hs2 hu, ksD_ksNestA _ _ hs2.le, ksD_ksNestB _ _ hs2.le, ksDQ]
  congr 1
  have hc2 : c ^ 2 ≠ 0 := (pow_pos hc 2).ne'
  field_simp

theorem ksD_ksKDens {e μ x c s u : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x) (hc : 0 < c)
    (hs : -(4 * μ ^ 2) < s) (hs2 : s < 2 * c ^ 2) (hu : 0 < u) :
    ksKDens e μ x c s u = ((ksDQ e μ x s u - ksDQ e μ x 0 u : ℝ) : ℂ) := by
  rw [ksKDens, ksD_qDens he hμ hx hc hs hs2 hu,
    ksD_qDens he hμ hx hc (by nlinarith) (by positivity) hu]
  push_cast
  ring

/-- The tilt used to read the density: `c = √(|s| + 1)`, with `s < 2c²`. -/
noncomputable def ksDTilt (s : ℝ) : ℝ := Real.sqrt (|s| + 1)

theorem ksD_tilt_pos (s : ℝ) : 0 < ksDTilt s := Real.sqrt_pos.2 (by positivity)

theorem ksD_lt_tilt (s : ℝ) : s < 2 * ksDTilt s ^ 2 := by
  rw [ksDTilt, Real.sq_sqrt (by positivity)]
  linarith [le_abs_self s, abs_nonneg s]

/-- The reduced subtracted density, as a real function of the photon mass² `u`. -/
noncomputable def ksDSub (e μ x s u : ℝ) : ℝ := ksDQ e μ x s u - ksDQ e μ x 0 u

theorem ksD_ksKDens_eqOn {e μ x s : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hs : -(4 * μ ^ 2) < s) :
    EqOn (ksKDens e μ x (ksDTilt s) s) (fun u => (ksDSub e μ x s u : ℂ)) (Ioi 0) :=
  fun _ hu => ksD_ksKDens he hμ hx (ksD_tilt_pos s) hs (ksD_lt_tilt s) hu

/-- `ksDSub` is integrable on `(1, ∞)`. -/
theorem ksD_integrableOn_ksDSub {e μ x s : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hs : -(4 * μ ^ 2) < s) : IntegrableOn (ksDSub e μ x s) (Ioi 1) := by
  have h := ksK_integrableOn_ksKDens he hμ hx (ksD_tilt_pos s) hs (ksD_lt_tilt s)
  have h' : IntegrableOn (fun u => (ksDSub e μ x s u : ℂ)) (Ioi 1) :=
    h.congr_fun (fun u hu => ksD_ksKDens_eqOn he hμ hx hs
      (lt_trans one_pos (mem_Ioi.1 hu))) measurableSet_Ioi
  exact h'.re

/-- **The per-flavour limit as an improper photon-mass integral of the reduced density**:
`∫_a^1 ksDSub → e⁴ decT₀ - ∫_{u > 1} ksDSub` as `a → 0⁺`. -/
theorem ksD_tendsto_integral {e μ x s : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hs : -(4 * μ ^ 2) < s) :
    Tendsto (fun a : ℝ => ((∫ u in a..1, ksDSub e μ x s u : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((e : ℂ) ^ 4 * decT₀ e μ x s - ((∫ u in Ioi 1, ksDSub e μ x s u : ℝ) : ℂ))) := by
  have h := ksK_tendsto_integral_ksKDens he hμ hx (ksD_tilt_pos s) hs (ksD_lt_tilt s)
  have hI : ∫ u in Ioi 1, ksKDens e μ x (ksDTilt s) s u =
      ((∫ u in Ioi 1, ksDSub e μ x s u : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioi fun u hu =>
      ksD_ksKDens_eqOn he hμ hx hs (lt_trans one_pos (mem_Ioi.1 hu))
  rw [hI] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun a ha => ?_)
  dsimp only
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun u hu => ?_
  have ha1 : a < 1 ∨ 1 ≤ a := lt_or_ge a 1
  have hu0 : 0 < u := by
    rcases ha1 with h1 | h1
    · rw [uIcc_of_le h1.le] at hu
      exact lt_of_lt_of_le (mem_Ioi.1 ha) hu.1
    · rw [uIcc_of_ge h1] at hu
      exact lt_of_lt_of_le one_pos hu.1
  exact ksD_ksKDens_eqOn he hμ hx hs hu0

/-- **The per-flavour limit is real**: `e⁴ decT₀ = lim_{a → 0⁺} ∫_a^1 ksDSub + ∫_{u > 1} ksDSub`
along `a → 0⁺` in the reals. -/
theorem ksD_tendsto_integral_re {e μ x s : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hs : -(4 * μ ^ 2) < s) :
    Tendsto (fun a : ℝ => ∫ u in a..1, ksDSub e μ x s u) (𝓝[>] 0)
      (𝓝 (((e : ℂ) ^ 4 * decT₀ e μ x s).re - ∫ u in Ioi 1, ksDSub e μ x s u)) := by
  have h := (Complex.continuous_re.tendsto _).comp (ksD_tendsto_integral he hμ hx hs)
  simpa [Function.comp_def] using h

theorem ksD_im_decT₀ {e μ x s : ℝ} (he : e ≠ 0) (hμ : 0 < μ) (hx : μ ^ 2 ≤ x)
    (hs : -(4 * μ ^ 2) < s) : ((e : ℂ) ^ 4 * decT₀ e μ x s).im = 0 := by
  have h := (Complex.continuous_im.tendsto _).comp (ksD_tendsto_integral he hμ hx hs)
  have h0 : Tendsto (fun a : ℝ => (((∫ u in a..1, ksDSub e μ x s u : ℝ) : ℂ)).im) (𝓝[>] 0)
      (𝓝 0) := by simp
  have := tendsto_nhds_unique (h0) (by simpa [Function.comp_def] using h)
  simpa using this.symm

end QED.ChainProof.SetAKS

end
