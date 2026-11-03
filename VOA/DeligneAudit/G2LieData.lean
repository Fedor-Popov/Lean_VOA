/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.G2Lie
import VOA.AffineGeneral.SCLieData
import VOA.AffineGeneral.SimpleQuotient

set_option linter.style.longLine false

/-!
# `LieData` for `𝔤₂` in the table basis, and `L_{-5/3}(𝔤₂)`

`g2CertData : LieData (formG g2Checks g2Gm) (Fin 14)`: the structure-constant algebra `g2Lie` of `G2Table`
(basis `b₀, b₁` = simple coroots, `b₂..b₇` positive roots `α₁, α₂, α₁+α₂, 2α₁+α₂, 3α₁+α₂, 3α₁+2α₂` with `α₁`
short, `b₈..b₁₃` their negatives), the invariant form `g2Gm = Killing/8` (long roots of length `2`; integer
entries), its dual family `dⱼ = (1/Dⱼ) vec (g2dl j)`, and `h = 4`. All checks by kernel reduction
(data generated outside Lean, untrusted; Lean re-checks).

* `g2CertData_sc`, `g2CertData_form`: the structure constants and the form are the table values;
* `g2W := simpleVOA g2CertData (-5/3) _ = L_{-5/3}(𝔤₂)`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.G2Lie

open VOA.AffineGeneral VOA.AffineGeneral.SCLie

noncomputable section

/-- The invariant form `Killing/8` on the table basis. -/
def g2Gm : List (ℕ × ℕ × ℤ) := [(0, 0, 6), (0, 1, -3), (1, 0, -3), (1, 1, 2), (2, 8, -3), (3, 9, -1),
  (4, 10, -3), (5, 11, -3), (6, 12, -1), (7, 13, -1), (8, 2, -3), (9, 3, -1), (10, 4, -3), (11, 5, -3),
  (12, 6, -1), (13, 7, -1)]

/-- Numerators of the dual family. -/
def g2dlRaw : List (List (ℕ × ℤ)) := [[(0, 2), (1, 3)], [(0, 1), (1, 2)], [(8, -1)], [(9, -1)], [(10, -1)],
  [(11, -1)], [(12, -1)], [(13, -1)], [(2, -1)], [(3, -1)], [(4, -1)], [(5, -1)], [(6, -1)], [(7, -1)]]

def g2dl (j : ℕ) : List (ℕ × ℤ) := g2dlRaw.getD j []

/-- Denominators of the dual family. -/
def g2DRaw : List ℤ := [3, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 1]

def g2D (j : ℕ) : ℤ := g2DRaw.getD j 1

theorem g2_gInRange : gInRange 14 g2Gm = true := by decide +kernel

theorem g2_symm : symmPerm g2Gm = true := by decide +kernel

theorem g2_skewOK : ∀ a : Fin 14, skewOK g2T 14 g2Gm a = true := by decide +kernel

theorem g2Skew_all : ∀ c : Fin 14, Skew g2Checks g2Gm (basis g2Checks c) := fun c =>
  skew_basis_of_check g2Checks g2Gm g2_gInRange c (g2_skewOK c)

theorem g2_pair : pairOK 14 g2Gm g2dl g2D = true := by decide +kernel

theorem g2_cas : ∀ x : Fin 14, casOK g2T 14 g2dl g2D 3 8 x = true := by decide +kernel

/-- **Lie data for `𝔤₂` in the table basis**, form `Killing/8`, `h = 4`. -/
def g2CertData : LieData (formG g2Checks g2Gm) (Fin 14) :=
  lieDataOf g2Checks g2Gm g2_gInRange g2_symm g2Skew_all g2dl g2D g2_pair 3 8 (by norm_num) g2_cas

theorem g2CertData_h : g2CertData.h = 4 := by
  change (((8 : ℤ) : ℂ) / 2) = 4
  norm_num

theorem g2CertData_generator (a : Fin 14) : g2CertData.generator a = basis g2Checks a := rfl

/-- The structure constants are the table entries. -/
theorem g2CertData_sc (a b g : Fin 14) :
    g2CertData.structureConstant a b g = (coef (entry g2T a b) g : ℂ) := by
  rw [LieData.structureConstant, LieData.coordinates, g2CertData_generator, g2CertData_generator]
  change (basis g2Checks).repr _ g = _
  rw [basis_eq_vec g2Checks a, basis_eq_vec g2Checks b,
    lie_vec g2Checks (by simp [inRange]) (by simp [inRange])]
  change (Pi.basisFun ℂ (Fin 14)).repr _ g = _
  rw [Pi.basisFun_repr]
  simp [vec, brL, coef_scale]

/-- The form table is `g2Gm`. -/
theorem g2CertData_form (a b : Fin 14) :
    g2CertData.formTable a b = (formV g2Gm [((a : ℕ), 1)] [((b : ℕ), 1)] : ℂ) := by
  rw [LieData.formTable, g2CertData_generator, g2CertData_generator]
  exact formG_basis g2Checks g2Gm g2_gInRange a b

theorem g2_level_ne : (-5/3 : ℂ) + g2CertData.h ≠ 0 := by rw [g2CertData_h]; norm_num

/-- `L_{-5/3}(𝔤₂)`. -/
abbrev g2W := simpleVOA g2CertData (-5/3) g2_level_ne

end

end VOA.DeligneAudit.G2Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Lie.g2CertData
#print axioms VOA.DeligneAudit.G2Lie.g2CertData_sc
#print axioms VOA.DeligneAudit.G2Lie.g2CertData_form
end AxiomAudit
