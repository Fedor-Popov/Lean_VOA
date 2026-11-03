/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VacuumProjection

/-!
# Exactness of the actual affine Verma-to-vacuum sequence

The extra vacuum relation is precisely F_0 v=0. Induction in the actual
enveloping left ideal proves that its full kernel is the image of M(k,-2).
This holds at every complex level, independently of a determinant formula.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open HighestNormalOrdering UniversalEnvelopingAlgebra
noncomputable section

/-- On an enveloping representative the singular embedding acts by the
literal enveloping action on its chosen horizontal vector. -/
theorem horizontalEmbedding_mk (k : ℂ) (u : U) :
    horizontalEmbedding k (Submodule.Quotient.mk u)=u • horizontalVector k := by
  have hl : lift ℂ (rho k 0)=Algebra.lsmul ℂ ℂ (Verma k 0) := by
    symm
    apply (lift_unique ℂ _ _).mp
    rfl
  rw [horizontalEmbedding,universalMap_mk]
  change (lift ℂ (rho k 0) u) (horizontalVector k)=_
  rw [hl]
  rfl

/-- The embedding intertwines the whole enveloping algebra, not merely
individual Lie generators. Its range is therefore an actual submodule. -/
theorem horizontalEmbedding_smul (k : ℂ) (u : U) (v : Verma k (-2)) :
    horizontalEmbedding k (u • v)=u • horizontalEmbedding k v := by
  obtain ⟨a,rfl⟩ := Submodule.Quotient.mk_surjective (highestIdeal k (-2)) v
  rw [← Submodule.Quotient.mk_smul,smul_eq_mul,horizontalEmbedding_mk,
    horizontalEmbedding_mk,mul_smul]

/-- Every enveloping action preserves the range of the actual embedding. -/
theorem horizontal_range_smul (k : ℂ) (u : U) {v : Verma k 0}
    (hv : v∈LinearMap.range (horizontalEmbedding k)) :
    u • v∈LinearMap.range (horizontalEmbedding k) := by
  obtain ⟨w,rfl⟩ := hv
  exact ⟨u • w,horizontalEmbedding_smul k u w⟩

/-- The generating horizontal vector belongs to the embedded range with
its exact coefficient one. -/
theorem horizontal_mem_range (k : ℂ) :
    horizontalVector k∈LinearMap.range (horizontalEmbedding k) :=
  ⟨highestVector k (-2),universalMap_highest _ _ _⟩

/-- A nonnegative basis-coloured vacuum generator has image in the
horizontal submodule: it is zero except for the extra F_0 relation. -/
theorem vacuum_generator_basis_range (k : ℂ) (a : Fin 3) (n : ℤ) (hn : 0≤n) :
    (Submodule.Quotient.mk (ι ℂ (modeElement a n)) : Verma k 0)∈
      LinearMap.range (horizontalEmbedding k) := by
  have he : (Submodule.Quotient.mk (ι ℂ (modeElement a n)) : Verma k 0)=
      mode k 0 a n (highestVector k 0) := by rw [mode,highestVector,rho_mk,mul_one]
  rw [he]
  by_cases hl : IsLower a n
  · have ha : a=1 ∧ n=0 := by simp only [IsLower] at hl; omega
    rcases ha with ⟨rfl,rfl⟩
    exact horizontal_mem_range k
  · rw [mode_highest k 0 a n hl]
    simp only [zero_smul,ite_self]
    exact Submodule.zero_mem _

/-- The same kernel statement holds for an arbitrary sl2 colour, by its
actual three-coordinate decomposition. -/
theorem vacuum_generator_loop_range (k : ℂ) (x : Sl2) (n : ℤ) (hn : 0≤n) :
    (Submodule.Quotient.mk (ι ℂ (AffineLie.ofLoop kappaForm kappaForm_isInvariant x n)) :
      Verma k 0)∈LinearMap.range (horizontalEmbedding k) := by
  have hx : x=∑a : Fin 3,x a • basis a := by
    ext b
    simp [basis,Pi.single_apply]
  rw [hx,← AffineLie.ofLoopₗ_apply,map_sum,map_sum]
  change ((highestIdeal k 0).mkQ) (∑a : Fin 3,ι ℂ
    (AffineLie.ofLoopₗ kappaForm kappaForm_isInvariant n (x a • basis a)))∈_
  rw [map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [map_smul,map_smul]
  change ((highestIdeal k 0).mkQ) ((algebraMap ℂ U (x a)) • ι ℂ (modeElement a n))∈_
  rw [map_smul]
  exact horizontal_range_smul k _ (vacuum_generator_basis_range k a n hn)

/-- Every generator of the actual vacuum left ideal maps into the
horizontal submodule in the zero-weight Verma quotient. -/
theorem vacuum_generator_range (k : ℂ) (u : U)
    (hu : u∈AffineLie.vacuumGens kappaForm kappaForm_isInvariant k) :
    (Submodule.Quotient.mk u : Verma k 0)∈LinearMap.range (horizontalEmbedding k) := by
  rcases hu with ⟨x,n,hn,rfl⟩|rfl|rfl
  · exact vacuum_generator_loop_range k x n hn
  · have hz : (Submodule.Quotient.mk (ι ℂ (AffineLie.C kappaForm kappaForm_isInvariant)-
        algebraMap ℂ U k) : Verma k 0)=0 :=
      by
        rw [Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span (Or.inr (Or.inl rfl))
    rw [hz]
    exact Submodule.zero_mem _
  · have hz : (Submodule.Quotient.mk (ι ℂ (AffineLie.ell0 kappaForm kappaForm_isInvariant)) :
        Verma k 0)=0 :=
      by
        rw [Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span (Or.inr (Or.inr rfl))
    rw [hz]
    exact Submodule.zero_mem _

/-- The entire vacuum left ideal maps into the horizontal singular range.
This includes arbitrary enveloping multiples, with no gradedness premise. -/
theorem vacuum_ideal_range (k : ℂ) (u : U)
    (hu : u∈AffineLie.vacuumIdeal kappaForm kappaForm_isInvariant k) :
    (Submodule.Quotient.mk u : Verma k 0)∈LinearMap.range (horizontalEmbedding k) := by
  induction hu using Submodule.span_induction with
  | mem u hu => exact vacuum_generator_range k u hu
  | zero => simpa using (LinearMap.range (horizontalEmbedding k)).zero_mem
  | add u v hu hv ihu ihv =>
    change ((highestIdeal k 0).mkQ) (u+v)∈_
    rw [map_add]
    exact Submodule.add_mem _ ihu ihv
  | smul a u hu ihu =>
    change ((highestIdeal k 0).mkQ) (a • u)∈_
    rw [map_smul]
    exact horizontal_range_smul k a ihu

/-- Exactness of M(k,-2) -> M(k,0) -> V^k at every complex level. The
kernel equality is proved in the actual carriers, not inferred from characters. -/
theorem vacuumProjection_ker (k : ℂ) :
    LinearMap.ker (vacuumProjection k)=LinearMap.range (horizontalEmbedding k) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨u,rfl⟩ := Submodule.Quotient.mk_surjective (highestIdeal k 0) v
    have hz : vacuumProjection k (Submodule.Quotient.mk u)=0 := hv
    rw [vacuumProjection_mk] at hz
    rw [Submodule.Quotient.mk_eq_zero] at hz
    exact vacuum_ideal_range k u hz
  · rintro v ⟨u,rfl⟩
    exact LinearMap.congr_fun (vacuumProjection_horizontalEmbedding k) u

end
end VOA.AffineVOA.HighestModule
