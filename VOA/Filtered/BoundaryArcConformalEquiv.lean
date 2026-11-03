import VOA.Filtered.BoundaryArcConformalSqueeze

/-! # Conformal compatibility of the actual boundary arc map

The target piece is defined by its actual Li components. Surjectivity transports
the conformal pieces, and injectivity gives compatibility of the inverse.
-/
namespace VOA.BoundaryArcConformalSqueeze
open VOA.BoundaryAuxiliary
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (W : VertexOperatorAlgebra V) (gen : Fin 3 → V)
    (hgen : ∀ i, gen i ∈ W.grading (1 : ℤ))

/-- The actual conformal piece of the Li algebra, including all Li depths. -/
def liConformalPiece (N : ℕ) : Submodule ℂ (liAssociatedGraded W) where
  carrier := {x | ∀ p M : ℕ, M ≠ N →
    DirectSum.component ℂ (ℕ × ℕ) (fun d => liWeightLayer W d.1 d.2) (p,M) x = 0}
  zero_mem' := by intro p M h; exact map_zero _
  add_mem' := by
    intro x y hx hy p M h
    rw [map_add, hx p M h, hy p M h, add_zero]
  smul_mem' := by
    intro a x hx p M h
    rw [map_smul, hx p M h, smul_zero]

/-- Homogeneous current jets have precisely their prescribed conformal weight. -/
theorem polynomialMap_mem_liConformalPiece {f : JetPoly ℂ} {N : ℕ}
    (hf : f.IsWeightedHomogeneous conformalWeight N) :
    polynomialMap W gen hgen f ∈ liConformalPiece W N := by
  intro p M hMN
  rw [← component_conformal W gen hgen p M f,
    hf.weightedHomogeneousComponent_ne M hMN, map_zero, map_zero]

/-- A conformally homogeneous Li element has a homogeneous polynomial preimage. -/
theorem polynomialMap_conformal_preimage
    (hsurj : Function.Surjective (polynomialMap W gen hgen))
    (N : ℕ) {y : liAssociatedGraded W} (hy : y ∈ liConformalPiece W N) :
    ∃ f : JetPoly ℂ, f.IsWeightedHomogeneous conformalWeight N ∧
      polynomialMap W gen hgen f = y := by
  obtain ⟨f,hf⟩ := hsurj y
  let q := MvPolynomial.weightedHomogeneousComponent conformalWeight N f
  have hq : q.IsWeightedHomogeneous conformalWeight N :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous N f
  refine ⟨q,hq,?_⟩
  apply DFinsupp.ext
  intro d
  change DirectSum.component ℂ (ℕ × ℕ) (fun e => liWeightLayer W e.1 e.2) d
      (polynomialMap W gen hgen q) =
    DirectSum.component ℂ (ℕ × ℕ) (fun e => liWeightLayer W e.1 e.2) d y
  obtain ⟨p,M⟩ := d
  by_cases h : M = N
  · subst M
    exact (component_conformal W gen hgen p N f).trans (congrArg
      (DirectSum.component ℂ (ℕ × ℕ) (fun e => liWeightLayer W e.1 e.2) (p,N)) hf)
  · rw [polynomialMap_mem_liConformalPiece W gen hgen hq p M h, hy p M h]

variable (m : ℕ)
variable (hI : sourceIdeal (R := ℂ) m ≤ RingHom.ker (polynomialMap W gen hgen).toRingHom)

/-- The actual canonical arc surjection maps exactly onto each conformal piece. -/
theorem sourcePiece_map_eq_liConformalPiece
    (hsurj : Function.Surjective (polynomialMap W gen hgen)) (N : ℕ) :
    (sourcePiece (K := ℂ) m N).map (sourceMap W gen hgen m hI).toLinearMap =
      liConformalPiece W N := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨f,hf,rfl⟩ := hx
    exact polynomialMap_mem_liConformalPiece W gen hgen hf
  · intro hy
    obtain ⟨f,hf,hfy⟩ := polynomialMap_conformal_preimage W gen hgen hsurj N hy
    exact ⟨Ideal.Quotient.mk (sourceIdeal (R := ℂ) m) f, ⟨f,hf,rfl⟩, hfy⟩

/-- Once injective, both the canonical map and its inverse preserve conformal pieces. -/
theorem sourceMap_mem_liConformalPiece_iff
    (hsurj : Function.Surjective (polynomialMap W gen hgen))
    (hinj : Function.Injective (sourceMap W gen hgen m hI))
    (N : ℕ) (x : Source (R := ℂ) m) :
    sourceMap W gen hgen m hI x ∈ liConformalPiece W N ↔
      x ∈ sourcePiece (K := ℂ) m N := by
  rw [← sourcePiece_map_eq_liConformalPiece W gen hgen m hI hsurj N]
  constructor
  · rintro ⟨z,hz,hzx⟩
    exact hinj hzx ▸ hz
  · intro hx
    exact ⟨x,hx,rfl⟩

end
end VOA.BoundaryArcConformalSqueeze
