/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9Closed
public import QED.ThreeLoopD.SetDMastersI9Gamma
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Set (d), master `I₉`: the input from the expansions of `K` and `Rem`

`T = i9Closed + B(1 + ε, ε) K + Rem` (`QED.ThreeLoopD.i9T`). The first two pieces are expanded in
`QED.ThreeLoopD.SetDMastersI9Closed`. Here we show that the expansions

  `K = -3/2 - 10ε + (-47 + 31π²/4 + 3ζ₃) ε²
     + (-197 + 265π²/6 + 144ζ₃ - π⁴/12 - 72π² ln 2) ε³ + O(ε⁴)` (`QED.ThreeLoopD.i9KLaurent`),
  `Rem = (-π²/2 - 9ζ₃) ε + (-17π²/2 + 33ζ₃ - 73π⁴/60 + 24π² ln 2) ε² + O(ε³)`
     (`QED.ThreeLoopD.i9RemLaurent`)

give `HasTruncLaurent i9T i9TLaurent 3` (`QED.ThreeLoopD.hasTruncLaurent_i9T_of_K_Rem`; the
orders `ε⁻²` to `ε²` match by a polynomial identity checked by `ring`), hence the set (d) input
for `I₉` (`QED.ThreeLoopD.hasTruncLaurent_setDMasterI9_of_K_Rem`). The coefficients of `K` and
`Rem` are numerical identifications (PSLQ on high-precision quadrature); their proofs are the
two hypotheses that remain.

## Main results

* `QED.ThreeLoopD.hasTruncLaurent_i9T_of_K_Rem`,
  `QED.ThreeLoopD.hasTruncLaurent_setDMasterI9_of_K_Rem`.
* `QED.ThreeLoopD.SetDMasters.Expansions.of_I9_I14_I16_I18`: the eleven set (d) inputs from the
  seven remaining ones and the expansions of `K` and `Rem`.
-/

@[expose] public section

open Complex Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- **The target expansion of `K`** through `ε³`. -/
noncomputable def i9KLaurent (ε : ℂ) : ℂ :=
  -3 / 2 - 10 * ε + (-47 + 31 / 4 * (π : ℂ) ^ 2 + 3 * (zeta3 : ℂ)) * ε ^ 2 +
    (-197 + 265 / 6 * (π : ℂ) ^ 2 + 144 * (zeta3 : ℂ) - (π : ℂ) ^ 4 / 12 -
      72 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)) * ε ^ 3

/-- **The target expansion of `Rem`** through `ε²`. -/
noncomputable def i9RemLaurent (ε : ℂ) : ℂ :=
  (-(π : ℂ) ^ 2 / 2 - 9 * (zeta3 : ℂ)) * ε +
    (-17 / 2 * (π : ℂ) ^ 2 + 33 * (zeta3 : ℂ) - 73 / 60 * (π : ℂ) ^ 4 +
      24 * (π : ℂ) ^ 2 * (Real.log 2 : ℂ)) * ε ^ 2

/-- `ε B_L(ε)`, a polynomial. -/
noncomputable def i9BetaKLe (ε : ℂ) : ℂ :=
  1 - (π : ℂ) ^ 2 / 6 * ε ^ 2 + 2 * (zeta3 : ℂ) * ε ^ 3 - (π : ℂ) ^ 4 / 40 * ε ^ 4

/-- The polynomial `(ε² C_L + ε³ B_L K_L + ε² Rem_L - ε² T_L) / ε⁵`. -/
noncomputable def i9WireP (ε : ℂ) : ℂ :=
  (-301 / 240 * (π : ℂ) ^ 4 - 1 / 2 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 47 / 6 * (π : ℂ) ^ 2
    - 20 * (zeta3 : ℂ)) + (1 / 72 * (π : ℂ) ^ 6 + 12 * (π : ℂ) ^ 4 * (Real.log 2 : ℂ)
    - 64 / 9 * (π : ℂ) ^ 4 - 17 / 2 * (π : ℂ) ^ 2 * (zeta3 : ℂ) + 197 / 6 * (π : ℂ) ^ 2
    + 6 * (zeta3 : ℂ) ^ 2 - 94 * (zeta3 : ℂ)) * ε + (-31 / 160 * (π : ℂ) ^ 6
    - 29 / 120 * (π : ℂ) ^ 4 * (zeta3 : ℂ) + 47 / 40 * (π : ℂ) ^ 4
    - 144 * (π : ℂ) ^ 2 * (zeta3 : ℂ) * (Real.log 2 : ℂ) + 265 / 3 * (π : ℂ) ^ 2 * (zeta3 : ℂ)
    + 288 * (zeta3 : ℂ) ^ 2 - 394 * (zeta3 : ℂ)) * ε ^ 2 + (1 / 480 * (π : ℂ) ^ 8
    + 9 / 5 * (π : ℂ) ^ 6 * (Real.log 2 : ℂ) - 53 / 48 * (π : ℂ) ^ 6
    - 18 / 5 * (π : ℂ) ^ 4 * (zeta3 : ℂ) + 197 / 40 * (π : ℂ) ^ 4) * ε ^ 3

/-- The polynomial identity behind the expansion of `T`: the orders `ε⁻²` to `ε²` of
`C_L + B_L K_L + Rem_L` are those of `T_L`. -/
theorem i9Wire_key (ε : ℂ) :
    i9ClosedLe ε + ε * i9BetaKLe ε * i9KLaurent ε + ε ^ 2 * i9RemLaurent ε =
      i9TLe ε + ε ^ 5 * i9WireP ε := by
  simp only [i9ClosedLe, i9BetaKLe, i9KLaurent, i9RemLaurent, i9TLe, i9WireP]
  ring

/-- **The expansion of `T` from those of `K` and `Rem`**: if `K = K_L + ε⁴ R_K` and
`Rem = Rem_L + ε³ R_R` with `R_K`, `R_R` analytic at `0`, then `T = T_L + ε³ R_T` with `R_T`
analytic at `0`. -/
theorem hasTruncLaurent_i9T_of_K_Rem (hK : HasTruncLaurent i9K i9KLaurent 4)
    (hRem : HasTruncLaurent i9Rem i9RemLaurent 3) : HasTruncLaurent i9T i9TLaurent 3 := by
  obtain ⟨RC, hRC, hC⟩ := hasTruncLaurent_i9Closed
  obtain ⟨RB, hRB, hB⟩ := hasTruncLaurent_i9BetaK
  obtain ⟨RK, hRK, hKe⟩ := hK
  obtain ⟨RR, hRR, hRe⟩ := hRem
  refine ⟨fun ε => i9WireP ε + RC ε + RR ε + ε * RB ε * i9KLaurent ε + i9BetaKLe ε * RK ε +
    ε ^ 5 * RB ε * RK ε, ?_, ?_⟩
  · have hP : AnalyticAt ℂ i9WireP 0 := by unfold i9WireP; fun_prop
    have hL : AnalyticAt ℂ i9KLaurent 0 := by unfold i9KLaurent; fun_prop
    have hBL : AnalyticAt ℂ i9BetaKLe 0 := by unfold i9BetaKLe; fun_prop
    fun_prop
  filter_upwards [hC, hB, hKe, hRe, self_mem_nhdsWithin] with ε hCε hBε hKε hRε h0
  have h0 : ε ≠ 0 := h0
  have key := i9Wire_key ε
  have hCL : i9ClosedLaurent ε = i9ClosedLe ε / ε ^ 2 := by
    simp only [i9ClosedLaurent, i9ClosedLe]; field_simp
  have hBL : i9BetaKLaurent ε = i9BetaKLe ε / ε := by
    simp only [i9BetaKLaurent, i9BetaKLe]; field_simp
  have hTL : i9TLaurent ε = i9TLe ε / ε ^ 2 := by
    simp only [i9TLaurent, i9TLe]; field_simp
  rw [i9T, hCε, show i9Beta (1 + ε) ε = i9BetaKLaurent ε + ε ^ 4 * RB ε from hBε, hKε, hRε,
    hCL, hBL, hTL]
  generalize i9ClosedLe ε = C at *
  generalize i9BetaKLe ε = B at *
  generalize i9KLaurent ε = K at *
  generalize i9RemLaurent ε = R at *
  generalize i9TLe ε = T at *
  generalize i9WireP ε = P at *
  field_simp
  linear_combination key

/-- **The set (d) input for `I₉` from the expansions of `K` and `Rem`.** -/
theorem hasTruncLaurent_setDMasterI9_of_K_Rem (hK : HasTruncLaurent i9K i9KLaurent 4)
    (hRem : HasTruncLaurent i9Rem i9RemLaurent 3) :
    HasTruncLaurent setDMasterI9 setDLaurentI9 2 :=
  hasTruncLaurent_setDMasterI9_of_i9T (hasTruncLaurent_i9T_of_K_Rem hK hRem)

/-- The set (d) inputs with `I₉, I₁₄, I₁₆, I₁₈` discharged: if they are the masters defined
here, and `K` and `Rem` have their expansions, then the other seven inputs give all eleven. -/
theorem SetDMasters.Expansions.of_I9_I14_I16_I18 {M : SetDMasters} (h9 : M.I9 = setDMasterI9)
    (h14 : M.I14 = setDMasterI14) (h16 : M.I16 = setDMasterI16) (h18 : M.I18 = setDMasterI18)
    (hK : HasTruncLaurent i9K i9KLaurent 4) (hRem : HasTruncLaurent i9Rem i9RemLaurent 3)
    (h2 : HasTruncLaurent M.I2 setDLaurentI2 2) (h3 : HasTruncLaurent M.I3 setDLaurentI3 1)
    (h5 : HasTruncLaurent M.I5 setDLaurentI5 2) (h8 : HasTruncLaurent M.I8 setDLaurentI8 3)
    (h12 : HasTruncLaurent M.I12 setDLaurentI12 3)
    (h13 : HasTruncLaurent M.I13 setDLaurentI13 3)
    (h15 : HasTruncLaurent M.I15 setDLaurentI15 3) : M.Expansions :=
  SetDMasters.Expansions.of_I14_I16_I18 h14 h16 h18 h2 h3 h5 h8
    (h9 ▸ hasTruncLaurent_setDMasterI9_of_K_Rem hK hRem) h12 h13 h15

/-- **Set (d) from seven master inputs and the expansions of `K` and `Rem`**: the set (d)
combination tends to the Jegerlehner–Nyffeler value as `ε → 0`. -/
theorem SetDMasters.tendsto_of_I9_I14_I16_I18 {M : SetDMasters} (h9 : M.I9 = setDMasterI9)
    (h14 : M.I14 = setDMasterI14) (h16 : M.I16 = setDMasterI16) (h18 : M.I18 = setDMasterI18)
    (hK : HasTruncLaurent i9K i9KLaurent 4) (hRem : HasTruncLaurent i9Rem i9RemLaurent 3)
    (h2 : HasTruncLaurent M.I2 setDLaurentI2 2) (h3 : HasTruncLaurent M.I3 setDLaurentI3 1)
    (h5 : HasTruncLaurent M.I5 setDLaurentI5 2) (h8 : HasTruncLaurent M.I8 setDLaurentI8 3)
    (h12 : HasTruncLaurent M.I12 setDLaurentI12 3)
    (h13 : HasTruncLaurent M.I13 setDLaurentI13 3)
    (h15 : HasTruncLaurent M.I15 setDLaurentI15 3) :
    Tendsto (setDCombination M) (𝓝[≠] (0 : ℂ)) (𝓝 (a1SixSetDJN : ℂ)) :=
  (SetDMasters.Expansions.of_I9_I14_I16_I18 h9 h14 h16 h18 hK hRem h2 h3 h5 h8 h12 h13
    h15).tendsto

end QED.ThreeLoopD
