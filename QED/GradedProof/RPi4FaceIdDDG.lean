/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2VAlg

/-!
# (R-Π₄) step L6d3: the three-flavour combination of a face integrand

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The fifteen
pieces of a two-loop class (`QED.GradedProof.VP2.tri_v_eq`) come from the Leibniz rule for the
second divided difference in the squared mass `s` of the four fermion denominators. At a face
the lines of the face block drop out of the rest product. Writing the factor of a line as
`faceIdG b V s` (`(V + s)⁻¹` on a rest line, `b = true`; `1` on a block line) and its duplicated
factor as `faceIdW b V s` (`(V + s)⁻¹`, resp. `0`), the same Leibniz expansion gives the
three-flavour combination of the face integrand as the sum of the face integrands of the pieces,
the pieces that duplicate a block line contributing `0`:

* `faceIdG`, `faceIdW`, `faceId_dd1_G`, `faceId_dd2_G`;
* **`faceId_tri_g`**: the face analogue of `QED.GradedProof.VP2.tri_v_eq`.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

/-- The factor of a fermion line in a face integrand: `(V + s)⁻¹` on a rest line (`b = true`),
`1` on a line of the face block. -/
noncomputable def faceIdG (b : Bool) (V s : ℂ) : ℂ := if b then (V + s)⁻¹ else 1

/-- The factor of a duplicated fermion line: `(V + s)⁻¹` on a rest line, `0` on a block line. -/
noncomputable def faceIdW (b : Bool) (V s : ℂ) : ℂ := if b then (V + s)⁻¹ else 0

theorem faceId_dd1_G (b : Bool) {V x y : ℂ} (hx : V + x ≠ 0) (hy : V + y ≠ 0)
    (hxy : x - y ≠ 0) :
    dd1 (fun s => faceIdG b V s) x y = -(faceIdG b V x * faceIdW b V y) := by
  cases b
  · simp [faceIdG, faceIdW, dd1]
  · simpa [faceIdG, faceIdW] using dd1_inv hx hy hxy

theorem faceId_dd2_G (b : Bool) {V x y z : ℂ} (hx : V + x ≠ 0) (hy : V + y ≠ 0)
    (hz : V + z ≠ 0) (hxy : x - y ≠ 0) (hxz : x - z ≠ 0) (hyz : y - z ≠ 0) :
    dd2 (fun s => faceIdG b V s) x y z = faceIdG b V x * faceIdW b V y * faceIdW b V z := by
  cases b
  · simp [faceIdG, faceIdW, dd2, dd1]
  · simpa [faceIdG, faceIdW] using dd2_inv hx hy hz hxy hxz hyz

/-- The second divided difference of a quadratic over four line factors. -/
theorem faceId_dd2_quad_G (b : Fin 4 → Bool) (V : Fin 4 → ℂ) (s0 s1 s2 E0 E2 E4 : ℂ)
    (h01 : s0 - s1 ≠ 0) (h02 : s0 - s2 ≠ 0) (h12 : s1 - s2 ≠ 0) (h0 : ∀ i, V i + s0 ≠ 0)
    (h1 : ∀ i, V i + s1 ≠ 0) (h2 : ∀ i, V i + s2 ≠ 0) :
    dd2 (fun s : ℂ => (E0 + s * E2 + s ^ 2 * E4) *
      (faceIdG (b 0) (V 0) s * faceIdG (b 1) (V 1) s * faceIdG (b 2) (V 2) s *
        faceIdG (b 3) (V 3) s)) s0 s1 s2 =
        (E0 + s0 * E2 + s0 ^ 2 * E4) *
          (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then
            (∏ l : Fin 4, faceIdG (b l) (V l) (if l ≤ i then s0 else if l ≤ j then s1 else s2)) *
              faceIdW (b i) (V i) s1 * faceIdW (b j) (V j) s2 else 0) -
          (E2 + (s0 + s1) * E4) *
            (∑ i : Fin 4, (∏ l : Fin 4, faceIdG (b l) (V l) (if l ≤ i then s1 else s2)) *
              faceIdW (b i) (V i) s2) +
          E4 * ∏ l : Fin 4, faceIdG (b l) (V l) s2 := by
  rw [dd2_mul h01 h02 h12, dd2_mul h01 h02 h12, dd2_mul h01 h02 h12, dd2_mul h01 h02 h12]
  simp only [dd1_mul h01, dd1_mul h12, dd2_quad _ _ _ h01 h02 h12, dd1_quad _ _ _ h01,
    faceId_dd1_G _ (h0 _) (h1 _) h01, faceId_dd1_G _ (h1 _) (h2 _) h12,
    faceId_dd2_G _ (h0 _) (h1 _) (h2 _) h01 h02 h12]
  simp only [Fin.sum_univ_four, Fin.prod_univ_four]
  simp (config := {decide := true}) only [Fin.isValue, ite_true, ite_false]
  ring

/-- **The three-flavour combination of a face integrand as the sum of the pieces.** -/
theorem faceId_tri_g (b : Fin 4 → Bool) (V : Fin 4 → ℂ) (E0 E2 E4 s0 s1 s2 : ℂ)
    (h01 : s0 - s1 ≠ 0) (h02 : s0 - s2 ≠ 0) (h12 : s1 - s2 ≠ 0) (h0 : ∀ i, V i + s0 ≠ 0)
    (h1 : ∀ i, V i + s1 ≠ 0) (h2 : ∀ i, V i + s2 ≠ 0) :
    (E0 + s0 * E2 + s0 ^ 2 * E4) * ∏ l, faceIdG (b l) (V l) s0 +
        (s2 - s0) / (s1 - s2) * ((E0 + s1 * E2 + s1 ^ 2 * E4) * ∏ l, faceIdG (b l) (V l) s1) +
        (s0 - s1) / (s1 - s2) * ((E0 + s2 * E2 + s2 ^ 2 * E4) * ∏ l, faceIdG (b l) (V l) s2) =
      ∑ i : Fin 4, ∑ j : Fin 4, (if i ≤ j then
          (s1 - s0) * (s2 - s0) * (E0 + s0 * E2 + s0 ^ 2 * E4) *
            ((∏ l : Fin 4, faceIdG (b l) (V l) (if l ≤ i then s0 else if l ≤ j then s1 else s2)) *
              faceIdW (b i) (V i) s1 * faceIdW (b j) (V j) s2) else 0) +
        ∑ i : Fin 4, -((s1 - s0) * (s2 - s0)) * (E2 + (s0 + s1) * E4) *
          ((∏ l : Fin 4, faceIdG (b l) (V l) (if l ≤ i then s1 else s2)) *
            faceIdW (b i) (V i) s2) +
        (s1 - s0) * (s2 - s0) * E4 * ∏ l : Fin 4, faceIdG (b l) (V l) s2 := by
  set H : ℂ → ℂ := fun s => (E0 + s * E2 + s ^ 2 * E4) *
    (faceIdG (b 0) (V 0) s * faceIdG (b 1) (V 1) s * faceIdG (b 2) (V 2) s *
      faceIdG (b 3) (V 3) s) with hH
  have hT := tri_eq_dd2 h01 h02 h12 H
  have hL := faceId_dd2_quad_G b V s0 s1 s2 E0 E2 E4 h01 h02 h12 h0 h1 h2
  rw [← hH] at hL
  have e : ∀ s, (E0 + s * E2 + s ^ 2 * E4) * ∏ l, faceIdG (b l) (V l) s = H s := fun s => by
    simp only [hH, Fin.prod_univ_four]
  rw [e, e, e, hT, hL]
  simp only [Fin.sum_univ_four, Fin.prod_univ_four]
  simp (config := {decide := true}) only [Fin.isValue, ite_true, ite_false]
  ring

end QED.GradedProof.RPi4

end
