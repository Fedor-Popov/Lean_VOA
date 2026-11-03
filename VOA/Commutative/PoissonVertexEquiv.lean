/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.PoissonVertexHom

/-! # Poisson vertex equivalences, including compatibility of the inverse -/
namespace VOA.PoissonVertexAlgebra
noncomputable section
variable {A B C : Type*} [CommRing A] [Algebra ℂ A]
  [CommRing B] [Algebra ℂ B] [CommRing C] [Algebra ℂ C]

/-- An algebra equivalence preserving translation and every vertex Poisson product. -/
structure Equiv (P : VOA.PoissonVertexAlgebra A) (Q : VOA.PoissonVertexAlgebra B) where
  toAlgEquiv : A ≃ₐ[ℂ] B
  map_translation : ∀ x, toAlgEquiv (P.translation x) = Q.translation (toAlgEquiv x)
  map_mode : ∀ n x y, toAlgEquiv (P.mode n x y) = Q.mode n (toAlgEquiv x) (toAlgEquiv y)

/-- A bijective genuine PVA homomorphism is a PVA equivalence. -/
def Equiv.ofBijective {P : VOA.PoissonVertexAlgebra A} {Q : VOA.PoissonVertexAlgebra B}
    (f : Hom P Q) (hf : Function.Bijective f.toAlgHom) : Equiv P Q where
  toAlgEquiv := AlgEquiv.ofBijective f.toAlgHom hf
  map_translation := f.map_translation
  map_mode := f.map_mode

/-- The inverse preserves translation and all products as well. -/
def Equiv.symm {P : VOA.PoissonVertexAlgebra A} {Q : VOA.PoissonVertexAlgebra B}
    (e : Equiv P Q) : Equiv Q P where
  toAlgEquiv := e.toAlgEquiv.symm
  map_translation y := by
    apply e.toAlgEquiv.injective
    rw [AlgEquiv.apply_symm_apply, e.map_translation, AlgEquiv.apply_symm_apply]
  map_mode n x y := by
    apply e.toAlgEquiv.injective
    rw [AlgEquiv.apply_symm_apply, e.map_mode, AlgEquiv.apply_symm_apply,
      AlgEquiv.apply_symm_apply]

/-- Composition preserves the full PVA structure. -/
def Equiv.trans {P : VOA.PoissonVertexAlgebra A} {Q : VOA.PoissonVertexAlgebra B}
    {S : VOA.PoissonVertexAlgebra C} (e : Equiv P Q) (f : Equiv Q S) : Equiv P S where
  toAlgEquiv := e.toAlgEquiv.trans f.toAlgEquiv
  map_translation x := by
    simp only [AlgEquiv.trans_apply, e.map_translation, f.map_translation]
  map_mode n x y := by
    simp only [AlgEquiv.trans_apply, e.map_mode, f.map_mode]

end
end VOA.PoissonVertexAlgebra
