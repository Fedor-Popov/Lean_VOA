/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieChecksSkewA
import VOA.DeligneAudit.F4LieChecksSkewB
import VOA.DeligneAudit.F4LieChecksSkewC
import VOA.DeligneAudit.F4LieChecksSkewD
import VOA.DeligneAudit.F4LieChecksPairA
import VOA.DeligneAudit.F4LieChecksPairB
import VOA.DeligneAudit.F4LieChecksCasA
import VOA.DeligneAudit.F4LieChecksCasB
import VOA.DeligneAudit.F4LieChecksCasC
import VOA.DeligneAudit.F4LieChecksCasD
import VOA.AffineGeneral.F4Lie
import VOA.AffineGeneral.SimpleQuotient

/-!
# `LieData` for `𝔣₄` in the table basis, and `L_{-5/2}(𝔣₄)`

`f4CertData : LieData (formG f4Checks f4Gm) (Fin 52)`: the structure-constant algebra `f4Lie` of
`F4Table`, the invariant form `f4Gm = Killing/18` (long roots of length `2`, integer entries), its
dual family, and `h = 9` (the generic `lieDataOf`; all checks in `F4LieChecks*` by kernel
reduction). `f4CertData_sc`, `f4CertData_form`: structure constants and form are the table values.
`f4W := simpleVOA f4CertData (-5/2) _ = L_{-5/2}(𝔣₄)`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.F4Lie

open VOA.AffineGeneral VOA.AffineGeneral.SCLie

noncomputable section

theorem f4_skewOK (a : Fin 52) : skewOK f4T 52 f4Gm a = true := by
  apply skewOK_of_2 f4T 52 f4Gm f4_symm f4Gc f4_gc
  have ha : a.val < 52 := a.2
  rcases (show (0 ≤ a.val ∧ a.val < 13) ∨ (13 ≤ a.val ∧ a.val < 26) ∨ (26 ≤ a.val ∧ a.val < 39) ∨
      (39 ≤ a.val ∧ a.val < 52) by omega) with h | h | h | h
  · exact f4_skew0 a h.1 h.2
  · exact f4_skew1 a h.1 h.2
  · exact f4_skew2 a h.1 h.2
  · exact f4_skew3 a h.1 h.2

theorem f4Skew_all : ∀ c : Fin 52, Skew f4Checks f4Gm (basis f4Checks c) := fun c =>
  skew_basis_of_check f4Checks f4Gm f4_gInRange c (f4_skewOK c)

theorem f4_pair : pairOK 52 f4Gm f4dl f4D = true :=
  pairOK_of_chunks f4Gm f4dl f4D fun j hj => by
    rcases (show (0 ≤ j ∧ j < 26) ∨ (26 ≤ j ∧ j < 52) by omega) with h | h
    · exact ⟨0, 26, h.1, h.2, f4_pair0⟩
    · exact ⟨26, 52, h.1, h.2, f4_pair1⟩

theorem f4_cas : ∀ x : Fin 52, casOK f4T 52 f4dl f4D 2 18 x = true := by
  intro x
  have hx : x.val < 52 := x.2
  rcases (show (0 ≤ x.val ∧ x.val < 13) ∨ (13 ≤ x.val ∧ x.val < 26) ∨ (26 ≤ x.val ∧ x.val < 39) ∨
      (39 ≤ x.val ∧ x.val < 52) by omega) with h | h | h | h
  · exact f4_cas0 x h.1 h.2
  · exact f4_cas1 x h.1 h.2
  · exact f4_cas2 x h.1 h.2
  · exact f4_cas3 x h.1 h.2

/-- **Lie data for `𝔣₄` in the table basis**, form `Killing/18`, `h = 9`. -/
def f4CertData : LieData (formG f4Checks f4Gm) (Fin 52) :=
  lieDataOf f4Checks f4Gm f4_gInRange f4_symm f4Skew_all f4dl f4D f4_pair 2 18 (by norm_num) f4_cas

theorem f4CertData_h : f4CertData.h = 9 := by
  change (((18 : ℤ) : ℂ) / 2) = 9
  norm_num

theorem f4CertData_generator (a : Fin 52) : f4CertData.generator a = basis f4Checks a := rfl

theorem f4CertData_sc (a b g : Fin 52) :
    f4CertData.structureConstant a b g = (coef (entry f4T a b) g : ℂ) := by
  rw [LieData.structureConstant, LieData.coordinates, f4CertData_generator, f4CertData_generator]
  change (basis f4Checks).repr _ g = _
  rw [basis_eq_vec f4Checks a, basis_eq_vec f4Checks b,
    lie_vec f4Checks (by simp [inRange]) (by simp [inRange])]
  change (Pi.basisFun ℂ (Fin 52)).repr _ g = _
  rw [Pi.basisFun_repr]
  simp [vec, brL, coef_scale]

theorem f4CertData_form (a b : Fin 52) :
    f4CertData.formTable a b = (formV f4Gm [((a : ℕ), 1)] [((b : ℕ), 1)] : ℂ) := by
  rw [LieData.formTable, f4CertData_generator, f4CertData_generator]
  exact formG_basis f4Checks f4Gm f4_gInRange a b

theorem f4_level_ne : (-5/2 : ℂ) + f4CertData.h ≠ 0 := by rw [f4CertData_h]; norm_num

/-- `L_{-5/2}(𝔣₄)`. -/
abbrev f4W := simpleVOA f4CertData (-5/2) f4_level_ne

end

end VOA.DeligneAudit.F4Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.F4Lie.f4CertData
#print axioms VOA.DeligneAudit.F4Lie.f4CertData_sc
#print axioms VOA.DeligneAudit.F4Lie.f4CertData_form
end AxiomAudit
