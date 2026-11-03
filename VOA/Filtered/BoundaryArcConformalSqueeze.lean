/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.GordonConformalCharacter
import VOA.Filtered.InfiniteLiJetBidegree

/-!
# The Hilbert squeeze on the actual infinite boundary arc

The source dimensions are those computed in Sections 2--5. No finite-stage
Hilbert inequality or equality of Li-bigraded characters is required. A finite
product of exact Li layers has the dimension of the actual VOA weight space.
-/
namespace VOA.BoundaryArcConformalSqueeze
open scoped BigOperators DirectSum
open VOA.BoundaryAuxiliary
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (W : VertexOperatorAlgebra V) (gen : Fin 3 → V)
    (hgen : ∀ i, gen i ∈ W.grading (1 : ℤ))

abbrev polynomialMap : JetPoly ℂ →ₐ[ℂ] liAssociatedGraded W :=
  liInfiniteJetPolynomialMap W gen (fun _ => 1) hgen

/-- A fixed Li-bidegree component already has the required conformal weight. -/
theorem bidegree_component_conformal (p N : ℕ) (f : JetPoly ℂ) :
    MvPolynomial.weightedHomogeneousComponent (InfiniteJet.jetLiBidegree (fun _ : Fin 3 => 1))
      (p, N) (MvPolynomial.weightedHomogeneousComponent conformalWeight N f) =
    MvPolynomial.weightedHomogeneousComponent (InfiniteJet.jetLiBidegree (fun _ : Fin 3 => 1))
      (p, N) f := by
  ext d
  simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases hd : Finsupp.weight (InfiniteJet.jetLiBidegree (fun _ : Fin 3 => 1)) d = (p, N)
  · have hc : Finsupp.weight conformalWeight d = N := by
      have h := congrArg Prod.snd hd
      simpa [Finsupp.weight_apply, Finsupp.sum, Prod.snd_sum,
        InfiniteJet.jetLiBidegree, conformalWeight, Nat.add_comm] using h
    simp only [if_pos hd, if_pos hc]
  · simp only [if_neg hd]

/-- Conformal projection of a polynomial preserves the corresponding actual Li components. -/
theorem component_conformal (p N : ℕ) (f : JetPoly ℂ) :
    DirectSum.component ℂ (ℕ × ℕ) (fun d => liWeightLayer W d.1 d.2) (p, N)
      (polynomialMap W gen hgen (MvPolynomial.weightedHomogeneousComponent conformalWeight N f)) =
    DirectSum.component ℂ (ℕ × ℕ) (fun d => liWeightLayer W d.1 d.2) (p, N)
      (polynomialMap W gen hgen f) := by
  rw [liInfiniteJetPolynomialMap_component_eq_component_weightedHomogeneousComponent,
    bidegree_component_conformal,
    ← liInfiniteJetPolynomialMap_component_eq_component_weightedHomogeneousComponent]

variable (m : ℕ)
variable (hI : sourceIdeal (R := ℂ) m ≤ RingHom.ker (polynomialMap W gen hgen).toRingHom)

/-- The actual infinite boundary relation quotient mapped to the Li algebra. -/
def sourceMap : Source (R := ℂ) m →ₐ[ℂ] liAssociatedGraded W :=
  Ideal.Quotient.liftₐ (sourceIdeal (R := ℂ) m) (polynomialMap W gen hgen)
    (fun f hf => hI hf)

@[simp] theorem sourceMap_mk (f : JetPoly ℂ) :
    sourceMap W gen hgen m hI (Ideal.Quotient.mk (sourceIdeal (R := ℂ) m) f) =
      polynomialMap W gen hgen f := rfl

/-- The finite collection of exact layers in one actual conformal weight. -/
abbrev Layers (N : ℕ) := ∀ p : Fin (N + 1), liWeightLayer W p.val N

local instance layer_finite (p N : ℕ) : FiniteDimensional ℂ (liWeightLayer W p N) := by
  letI := liWeightPiece_finiteDimensional W p N
  infer_instance

instance layers_finite (N : ℕ) : FiniteDimensional ℂ (Layers W N) := by
  letI : ∀ p : Fin (N + 1), FiniteDimensional ℂ (liWeightLayer W p.val N) :=
    fun p => layer_finite W p.val N
  infer_instance

/-- Conformal telescoping identifies this target dimension with the actual VOA dimension. -/
theorem layers_finrank (N : ℕ) :
    Module.finrank ℂ (Layers W N) = Module.finrank ℂ (W.grading N) := by
  rw [Module.finrank_pi_fintype,
    Fin.sum_univ_eq_sum_range (fun p => Module.finrank ℂ (liWeightLayer W p N))]
  exact sum_liWeightLayer_finrank_eq_grading W N

/-- Project the actual arc conformal piece to all its exact Li-layer targets. -/
def pieceMap (N : ℕ) : sourcePiece (K := ℂ) m N →ₗ[ℂ] Layers W N :=
  LinearMap.pi (fun p =>
    (DirectSum.component ℂ (ℕ × ℕ) (fun d => liWeightLayer W d.1 d.2) (p.val, N)).comp
      ((sourceMap W gen hgen m hI).toLinearMap.comp (sourcePiece (K := ℂ) m N).subtype))

/-- The actual polynomial current surjection supplies all exact layers simultaneously. -/
theorem pieceMap_surjective
    (hsurj : Function.Surjective (polynomialMap W gen hgen)) (N : ℕ) :
    Function.Surjective (pieceMap W gen hgen m hI N) := by
  intro y
  let z : liAssociatedGraded W := ∑ p : Fin (N + 1),
    DirectSum.lof ℂ (ℕ × ℕ) (fun d => liWeightLayer W d.1 d.2) (p.val, N) (y p)
  obtain ⟨f, hf⟩ := hsurj z
  let q := MvPolynomial.weightedHomogeneousComponent conformalWeight N f
  let x : sourcePiece (K := ℂ) m N := ⟨Ideal.Quotient.mk (sourceIdeal (R := ℂ) m) q,
    Submodule.mem_map.mpr ⟨q, MvPolynomial.weightedHomogeneousComponent_mem _ _ _, rfl⟩⟩
  refine ⟨x, ?_⟩
  funext p
  change DirectSum.component ℂ (ℕ × ℕ) (fun d => liWeightLayer W d.1 d.2) (p.val, N)
    (polynomialMap W gen hgen q) = y p
  rw [component_conformal W gen hgen, hf]
  dsimp only [z]
  rw [map_sum]
  simp [DirectSum.component.of, Prod.mk.injEq, ← Fin.ext_iff]

/-- The ordinary conformal Hilbert bound suffices for injectivity on each actual arc piece. -/
theorem pieceMap_injective_of_hilbert_bound
    (hsurj : Function.Surjective (polynomialMap W gen hgen)) (N : ℕ)
    (hbound : Module.finrank ℂ (sourcePiece (K := ℂ) m N) ≤
      Module.finrank ℂ (W.grading N)) :
    Function.Injective (pieceMap W gen hgen m hI N) := by
  letI := finiteDimensional_sourcePiece (K := ℂ) m N
  apply FiniteHilbertSqueeze.injective_of_surjective_of_finrank_le
    (pieceMap W gen hgen m hI N) (pieceMap_surjective W gen hgen m hI hsurj N)
  rwa [layers_finrank W N]

include hI in
/-- All conformal projections of a kernel polynomial are genuine presentation relations. -/
theorem conformal_component_mem_of_kernel
    (hsurj : Function.Surjective (polynomialMap W gen hgen))
    (hbound : ∀ N, Module.finrank ℂ (sourcePiece (K := ℂ) m N) ≤
      Module.finrank ℂ (W.grading N)) (f : JetPoly ℂ)
    (hf : polynomialMap W gen hgen f = 0) (N : ℕ) :
    MvPolynomial.weightedHomogeneousComponent conformalWeight N f ∈ sourceIdeal (R := ℂ) m := by
  let q := MvPolynomial.weightedHomogeneousComponent conformalWeight N f
  let x : sourcePiece (K := ℂ) m N := ⟨Ideal.Quotient.mk (sourceIdeal (R := ℂ) m) q,
    Submodule.mem_map.mpr ⟨q, MvPolynomial.weightedHomogeneousComponent_mem _ _ _, rfl⟩⟩
  have hx : pieceMap W gen hgen m hI N x = 0 := by
    funext p
    change DirectSum.component ℂ (ℕ × ℕ) (fun d => liWeightLayer W d.1 d.2) (p.val, N)
      (polynomialMap W gen hgen q) = 0
    rw [component_conformal W gen hgen, hf, map_zero]
  have heq := pieceMap_injective_of_hilbert_bound W gen hgen m hI hsurj N (hbound N)
    (hx.trans (map_zero _).symm)
  have hq : Ideal.Quotient.mk (sourceIdeal (R := ℂ) m) q = 0 := congrArg Subtype.val heq
  exact (Ideal.Quotient.eq_zero_iff_mem).mp hq

/-- Direct injection of the canonical actual arc map, using only the ordinary
conformal Hilbert bound and the actual polynomial current surjection. -/
theorem sourceMap_injective_of_hilbert_bound
    (hsurj : Function.Surjective (polynomialMap W gen hgen))
    (hbound : ∀ N, Module.finrank ℂ (sourcePiece (K := ℂ) m N) ≤
      Module.finrank ℂ (W.grading N)) :
    Function.Injective (sourceMap W gen hgen m hI) := by
  classical
  apply (injective_iff_map_eq_zero (sourceMap W gen hgen m hI).toAddMonoidHom).mpr
  intro x hx
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← MvPolynomial.sum_weightedHomogeneousComponent conformalWeight f,
    finsum_eq_sum _ (MvPolynomial.weightedHomogeneousComponent_finsupp f)]
  apply Ideal.sum_mem
  intro N _
  exact conformal_component_mem_of_kernel W gen hgen m hI hsurj hbound f hx N

/-- Surjectivity also survives passage to the actual relation quotient. -/
theorem sourceMap_surjective
    (hsurj : Function.Surjective (polynomialMap W gen hgen)) :
    Function.Surjective (sourceMap W gen hgen m hI) := by
  intro y
  obtain ⟨f, hf⟩ := hsurj y
  exact ⟨Ideal.Quotient.mk _ f, hf⟩

end
end VOA.BoundaryArcConformalSqueeze
