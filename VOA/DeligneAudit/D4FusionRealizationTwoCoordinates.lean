/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionD1TensorGRank
import Mathlib.LinearAlgebra.Pi

/-! Explicit standard coordinates on the actual two-site tensor space.
No matrix rank, filtration, character, or realization premise is used. -/
namespace VOA.DeligneAudit.D4Two

open VOA.DeligneAudit

noncomputable section

abbrev SiteIndex (n : ℕ) := Fin n ⊕ Unit
abbrev PairIndex (n : ℕ) := SiteIndex n × SiteIndex n

/-- Coordinates of the coadjoint summand and the extra trivial line. -/
def siteCoordinates (n : ℕ) :
    D1SiteG.Space n ≃ₗ[ℂ] (SiteIndex n → ℂ) where
  toFun u := Sum.elim u.1 (fun _ => u.2)
  invFun v := (fun i => v (Sum.inl i), v (Sum.inr ()))
  left_inv _ := rfl
  right_inv v := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => cases i; rfl
  map_add' u v := by
    funext i
    cases i <;> rfl
  map_smul' z u := by
    funext i
    cases i <;> rfl

@[simp] theorem siteCoordinates_inl (n : ℕ) (u : D1SiteG.Space n) (i : Fin n) :
    siteCoordinates n u (Sum.inl i) = u.1 i := rfl

@[simp] theorem siteCoordinates_inr (n : ℕ) (u : D1SiteG.Space n) :
    siteCoordinates n u (Sum.inr ()) = u.2 := rfl

/-- The explicit site basis transported from ordinary function coordinates. -/
def siteBasis (n : ℕ) : Module.Basis (SiteIndex n) ℂ (D1SiteG.Space n) :=
  (Pi.basisFun ℂ (SiteIndex n)).map (siteCoordinates n).symm

@[simp] theorem siteBasis_equivFun (n : ℕ) :
    (siteBasis n).equivFun = siteCoordinates n := by
  simp [siteBasis, Module.Basis.map_equivFun, Pi.basisFun_equivFun]

@[simp] theorem siteBasis_repr (n : ℕ) (u : D1SiteG.Space n) (i : SiteIndex n) :
    (siteBasis n).repr u i = siteCoordinates n u i := by
  change (siteBasis n).equivFun u i = _
  rw [siteBasis_equivFun]

/-- The two tensor indices are ordered as the two chosen sites. -/
def pairIndexEquiv (σ : Type*) : (Fin 2 → σ) ≃ σ × σ where
  toFun p := (p 0, p 1)
  invFun p := ![p.1, p.2]
  left_inv p := by
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl

/-- An actual product basis, with an explicit pair of site labels. -/
def twoBasis (n : ℕ) :
    Module.Basis (PairIndex n) ℂ (D1TensorG.Space n 2) :=
  (Basis.piTensorProduct (fun _ : Fin 2 => siteBasis n)).reindex
    (pairIndexEquiv (SiteIndex n))

/-- Standard coordinates are an equivalence of the actual tensor space. -/
def coordinates (n : ℕ) :
    D1TensorG.Space n 2 ≃ₗ[ℂ] (PairIndex n → ℂ) := (twoBasis n).equivFun

/-- On pure tensors these are exactly products of site coordinates. -/
theorem coordinates_tprod (n : ℕ) (u : Fin 2 → D1SiteG.Space n) (p : PairIndex n) :
    coordinates n (PiTensorProduct.tprod ℂ u) p =
      siteCoordinates n (u 0) p.1 * siteCoordinates n (u 1) p.2 := by
  change (twoBasis n).repr (PiTensorProduct.tprod ℂ u) p = _
  rw [twoBasis, Module.Basis.repr_reindex_apply,
    Basis.piTensorProduct_repr_tprod_apply]
  simp [pairIndexEquiv, Fin.prod_univ_two]

/-- Coordinate equality implies equality in the actual source module. -/
theorem coordinates_injective (n : ℕ) : Function.Injective (coordinates n) :=
  (coordinates n).injective

end
end VOA.DeligneAudit.D4Two

#print axioms VOA.DeligneAudit.D4Two.coordinates_tprod
#print axioms VOA.DeligneAudit.D4Two.coordinates_injective
