/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.SingularQuad

/-!
# Quadratic singular vectors at rational level

the `quadState_mem_maxIdeal` (`SingularQuad`) puts a quadratic state `Σ cᵢ
J^{aᵢ}_{-1}J^{bᵢ}_{-1}|0⟩` into
the maximal ideal of `V^k(𝔤)` once the coefficient families `quadCoef1`, `quadCoef2` vanish. For
Lie data with
integer structure constants `scZ` and integer form `fZ`, at a rational level `k = p/r`, we clear the
denominator: `r · quadCoef1 = q1Z p r` and `r · quadCoef2 = q2Z p` are integers, checkable by kernel
reduction (`quadCoef1_eq`, `quadCoef2_eq`, **`quadStateQ_mem_maxIdeal`**). Generic in `(p, r)`, so
it
serves `G₂` (`k = -5/3`) and `F₄` (`k = -5/2`).
-/

namespace VOA.AffineGeneral

open VOA.AffineGeneral.LieData

noncomputable section

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι) (scZ : ι → ι → ι → ℤ) (fZ : ι → ι → ℤ)

/-- Integer terms as complex terms. -/
def termsZC (terms : List (ℤ × ι × ι)) : List (ℂ × ι × ι) := terms.map fun t => ((t.1 : ℂ), t.2)

/-- `r ·` the weight-one coefficient, at level `p/r`. -/
def q1Z (p r : ℤ) (terms : List (ℤ × ι × ι)) (x g : ι) : ℤ :=
  (terms.map fun t => t.1 * ((if t.2.1 = g then p * fZ x t.2.2 else 0)
    + (if t.2.2 = g then p * fZ x t.2.1 else 0)
    + r * ∑ c, scZ x t.2.1 c * scZ c t.2.2 g)).sum

/-- `r ·` the vacuum coefficient, at level `p/r`. -/
def q2Z (p : ℤ) (terms : List (ℤ × ι × ι)) (x : ι) : ℤ :=
  (terms.map fun t => t.1 * (p * ∑ c, scZ x t.2.1 c * fZ c t.2.2)).sum

variable {D scZ fZ}

omit [FiniteDimensional ℂ 𝔤] in
theorem quadCoef1_eq (hsc : ∀ a b c, D.structureConstant a b c = scZ a b c)
    (hf : ∀ a b, D.formTable a b = fZ a b) (p r : ℤ) (hr : (r : ℂ) ≠ 0)
    (terms : List (ℤ × ι × ι)) (x g : ι) :
    quadCoef1 D ((p : ℂ) / r) (termsZC terms) x g = (q1Z scZ fZ p r terms x g : ℂ) / r := by
  induction terms with
  | nil => simp [quadCoef1, q1Z, termsZC]
  | cons t terms ih =>
    simp only [quadCoef1, q1Z, termsZC, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [hsc, hf]
    push_cast
    split_ifs <;> field_simp <;> ring

omit [FiniteDimensional ℂ 𝔤] in
theorem quadCoef2_eq (hsc : ∀ a b c, D.structureConstant a b c = scZ a b c)
    (hf : ∀ a b, D.formTable a b = fZ a b) (p r : ℤ) (hr : (r : ℂ) ≠ 0)
    (terms : List (ℤ × ι × ι)) (x : ι) :
    quadCoef2 D ((p : ℂ) / r) (termsZC terms) x = (q2Z scZ fZ p terms x : ℂ) / r := by
  induction terms with
  | nil => simp [quadCoef2, q2Z, termsZC]
  | cons t terms ih =>
    simp only [quadCoef2, q2Z, termsZC, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [hsc, hf]
    push_cast
    field_simp

/-- **A quadratic state at rational level `p/r` lies in the maximal ideal** once the integer
checks `q1Z`, `q2Z` vanish. -/
theorem quadStateQ_mem_maxIdeal (hsc : ∀ a b c, D.structureConstant a b c = scZ a b c)
    (hf : ∀ a b, D.formTable a b = fZ a b) (p r : ℤ) (hr : (r : ℂ) ≠ 0)
    (hk : (p : ℂ) / r + D.h ≠ 0) (terms : List (ℤ × ι × ι))
    (h1 : ∀ x g, q1Z scZ fZ p r terms x g = 0) (h2 : ∀ x, q2Z scZ fZ p terms x = 0) :
    quadState D ((p : ℂ) / r) (termsZC terms) ∈ maxIdeal D ((p : ℂ) / r) hk :=
  quadState_mem_maxIdeal D _ hk _
    (fun x g => by rw [quadCoef1_eq hsc hf p r hr, h1]; simp)
    (fun x => by rw [quadCoef2_eq hsc hf p r hr, h2]; simp)

end

end VOA.AffineGeneral

section AxiomAudit
#print axioms VOA.AffineGeneral.quadStateQ_mem_maxIdeal
end AxiomAudit
