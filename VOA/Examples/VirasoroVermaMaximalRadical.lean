/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaHighestProjection
import VOA.Examples.VirasoroVermaGramPolynomial

/-!
# The unique maximal proper Verma submodule

The actual contravariant radical contains every proper mode-stable subspace.
L0 interpolation extracts highest components without assuming gradedness;
adjointness then detects membership in the radical. The radical quotient
therefore has no nontrivial invariant subspaces. No determinant or character
formula is assumed in this construction of the irreducible quotient.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule VirDeformModes

/-- A linear subspace is invariant when every actual Virasoro mode
preserves it. The central action is scalar and hence automatically preserves it. -/
def VermaModeStable (c h : ℂ) (S : Submodule ℂ (Verma c h)) : Prop :=
  ∀ m : ℤ, ∀ v ∈ S, vermaMode c h m v∈S

/-- An invariant subspace containing the highest vector contains every
creation word and therefore the whole actual Verma module. -/
theorem verma_submodule_eq_top_of_highest (c h : ℂ) (S : Submodule ℂ (Verma c h))
    (hS : VermaModeStable c h S) (hv : highestVector c h∈S) : S=⊤ := by
  have hw : ∀ w : List ℕ, negWord c h w∈S := by
    intro w
    induction w with
    | nil => exact hv
    | cons i w ih => exact hS (-(i:ℤ)-1) _ ih
  apply top_unique
  intro v _
  rw [← (vermaSortedBasis c h).linearCombination_repr v]
  change (∑ w ∈ ((vermaSortedBasis c h).repr v).support,
    (vermaSortedBasis c h).repr v w • vermaSortedBasis c h w)∈S
  exact S.sum_mem (fun w _ => S.smul_mem _ (by simpa only [vermaSortedBasis_apply] using hw w.val))

/-- Every state in a proper invariant subspace has highest coefficient zero.
A nonzero coefficient would extract the highest vector by the finite L0
filter, and cyclicity would force the subspace to be the whole module. -/
theorem vermaHighestCoordinate_zero_of_proper (c h : ℂ)
    (S : Submodule ℂ (Verma c h)) (hS : VermaModeStable c h S) (hproper : S≠⊤)
    (v : Verma c h) (hv : v∈S) : vermaHighestCoordinate c h v=0 := by
  by_contra ha
  have hm := vermaHighestCoordinate_smul_mem c h S (hS 0) v hv
  have hh := S.smul_mem (vermaHighestCoordinate c h v)⁻¹ hm
  rw [smul_smul,inv_mul_cancel₀ ha,one_smul] at hh
  exact hproper (verma_submodule_eq_top_of_highest c h S hS hh)

/-- The canonical radical consists of states pairing to zero with every
actual Verma state. It is a concrete linear kernel of the constructed form. -/
noncomputable def vermaRadical (c h : ℂ) : Submodule ℂ (Verma c h) :=
  LinearMap.ker (vermaContravariant c h)

/-- Radical membership means the entire pairing functional is zero. -/
theorem mem_vermaRadical (c h : ℂ) (v : Verma c h) :
    v∈vermaRadical c h ↔ vermaContravariant c h v=0 := Iff.rfl

/-- Opposite-mode adjointness makes the actual radical invariant under all
Virasoro modes, at every central charge and highest weight. -/
theorem vermaRadical_stable (c h : ℂ) : VermaModeStable c h (vermaRadical c h) := by
  intro m v hv
  exact vermaContravariant_radical_mode c h m v hv

/-- The highest vector is outside the radical because its norm is exactly one. -/
theorem highest_not_mem_vermaRadical (c h : ℂ) : highestVector c h∉vermaRadical c h := by
  intro hv
  have he := LinearMap.congr_fun hv (highestVector c h)
  rw [vermaContravariant_normalized,LinearMap.zero_apply] at he
  exact one_ne_zero he

/-- The radical is proper for all parameters, even when some positive
levels are degenerate. The normalized highest line always survives. -/
theorem vermaRadical_ne_top (c h : ℂ) : vermaRadical c h≠⊤ := by
  intro he
  exact highest_not_mem_vermaRadical c h (he ▸ Submodule.mem_top)

/-- Every proper invariant subspace lies in the canonical radical. Move
creation words across the form until only a highest coefficient remains;
every intermediate state stays in the given subspace. No grading assumption
on that subspace is required. -/
theorem verma_proper_submodule_le_radical (c h : ℂ)
    (S : Submodule ℂ (Verma c h)) (hS : VermaModeStable c h S) (hproper : S≠⊤) :
    S≤vermaRadical c h := by
  have hz : ∀ (w : List ℕ) (v : Verma c h), v∈S →
      vermaContravariant c h v (negWord c h w)=0 := by
    intro w
    induction w with
    | nil =>
      intro v hv
      rw [negWord_nil,vermaContravariant_highest_right]
      exact vermaHighestCoordinate_zero_of_proper c h S hS hproper v hv
    | cons i w ih =>
      intro v hv
      rw [negWord_cons]
      have he := vermaContravariant_adj c h ((i:ℤ)+1) v (negWord c h w)
      rw [show -((i:ℤ)+1)=-(i:ℤ)-1 by omega] at he
      rw [← he]
      exact ih _ (hS _ v hv)
  intro v hv
  apply (vermaSortedBasis c h).ext
  intro w
  simpa only [vermaSortedBasis_apply,LinearMap.zero_apply] using hz w.val v hv

/-- An invariant subspace containing the radical is either the radical
itself or the whole Verma module. This is maximality in the actual module. -/
theorem vermaRadical_maximal (c h : ℂ) (S : Submodule ℂ (Verma c h))
    (hS : VermaModeStable c h S) (hr : vermaRadical c h≤S) :
    S=vermaRadical c h ∨ S=⊤ := by
  by_cases ht : S=⊤
  · exact Or.inr ht
  · exact Or.inl (le_antisymm (verma_proper_submodule_le_radical c h S hS ht) hr)

/-- The actual irreducible highest-weight carrier is the quotient by the
proved unique maximal proper invariant subspace. Its simplicity is proved
below; the definition does not assume a determinant or a character formula. -/
abbrev VermaSimple (c h : ℂ) := Verma c h ⧸ vermaRadical c h

/-- The actual mode on the radical quotient, descended by proved stability. -/
noncomputable def vermaSimpleMode (c h : ℂ) (m : ℤ) : Module.End ℂ (VermaSimple c h) :=
  (vermaRadical c h).mapQ (vermaRadical c h) (vermaMode c h m)
    (vermaRadical_stable c h m)

/-- Quotient projection intertwines every actual Virasoro mode. -/
theorem vermaSimpleMode_mkQ (c h : ℂ) (m : ℤ) (v : Verma c h) :
    vermaSimpleMode c h m ((vermaRadical c h).mkQ v)=
      (vermaRadical c h).mkQ (vermaMode c h m v) := rfl

/-- Descended modes satisfy the full Virasoro commutator with the original
central charge. Surjectivity of projection reduces the identity to actual
Verma representatives, so no relation is postulated on the quotient. -/
theorem vermaSimpleMode_comm (c h : ℂ) (m n : ℤ) :
    ⁅vermaSimpleMode c h m,vermaSimpleMode c h n⁆ =
      ((m:ℂ)-n) • vermaSimpleMode c h (m+n) +
        if m+n=0 then (((m:ℂ)^3-m)/12) •
          (c • (1 : Module.End ℂ (VermaSimple c h))) else 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨v,rfl⟩ := (vermaRadical c h).mkQ_surjective x
  have he := congrArg (vermaRadical c h).mkQ (vermaMode_comm_apply c h m n v)
  simp only [map_add,map_smul] at he
  change vermaSimpleMode c h m (vermaSimpleMode c h n _) -
    vermaSimpleMode c h n (vermaSimpleMode c h m _)=_
  simp only [vermaSimpleMode_mkQ,LinearMap.add_apply,LinearMap.smul_apply]
  split_ifs with hz
  · simp only [hz,if_true,LinearMap.smul_apply,Module.End.one_apply,map_smul] at he ⊢
    rw [he]
    module
  · simp only [hz,if_false,map_zero,add_zero,LinearMap.zero_apply] at he ⊢
    rw [he]
    module

/-- Package the actual quotient modes and their proved central commutator. -/
noncomputable def vermaSimpleData (c h : ℂ) : CentralVirasoroData (VermaSimple c h) where
  L := vermaSimpleMode c h
  central := c • 1
  comm := vermaSimpleMode_comm c h
  central_comm n := by
    change (c • (1 : Module.End ℂ (VermaSimple c h))) * vermaSimpleMode c h n =
      vermaSimpleMode c h n * (c • 1)
    simp

/-- The full Virasoro Lie representation on the actual radical quotient. -/
noncomputable def vermaSimpleRep (c h : ℂ) : VirRep (VermaSimple c h) where
  ρ := VirDeformModes.fixedRho (vermaSimpleData c h) rfl
  centralCharge := c
  acts_central := VirDeformModes.fixedRho_C _ _

/-- The full Lie action has precisely the descended quotient modes. -/
theorem vermaSimpleRep_mode (c h : ℂ) (m : ℤ) :
    LeeYangWardClosure.virMode (vermaSimpleRep c h) m=vermaSimpleMode c h m :=
  VirDeformModes.fixedRho_L (vermaSimpleData c h) rfl m

/-- The highest class in the radical quotient is nonzero, so this quotient
is a genuine nonzero representation at every pair of parameters. -/
theorem vermaSimple_highest_ne_zero (c h : ℂ) :
    (vermaRadical c h).mkQ (highestVector c h)≠0 := by
  intro he
  exact highest_not_mem_vermaRadical c h ((Submodule.Quotient.mk_eq_zero _).mp he)

/-- The surviving highest class satisfies the actual highest-weight
relations for the full quotient Lie representation, with parameters (c,h). -/
theorem vermaSimpleRep_highest (c h : ℂ) :
    IsHighestWeightVector (vermaSimpleRep c h)
      ((vermaRadical c h).mkQ (highestVector c h)) c h where
  centralCharge := rfl
  pos_annihilate m hm := by
    change LeeYangWardClosure.virMode (vermaSimpleRep c h) m _=0
    rw [vermaSimpleRep_mode,vermaSimpleMode_mkQ]
    have he : vermaMode c h m (highestVector c h)=0 := verma_pos_annihilate c h m hm
    rw [he,map_zero]
  zero_acts := by
    change LeeYangWardClosure.virMode (vermaSimpleRep c h) 0 _=_
    rw [vermaSimpleRep_mode,vermaSimpleMode_mkQ]
    have he : vermaMode c h 0 (highestVector c h)=h • highestVector c h := verma_zero_acts c h
    rw [he,map_smul]

/-- The actual radical quotient has no nonzero proper mode-invariant
subspace. Pullback turns any such subspace into a proper Verma submodule,
which is forced into the radical already killed by the quotient. -/
theorem vermaSimple_irreducible (c h : ℂ) (S : Submodule ℂ (VermaSimple c h))
    (hS : ∀ m : ℤ, ∀ v∈S, vermaSimpleMode c h m v∈S) : S=⊥ ∨ S=⊤ := by
  let P := S.comap (vermaRadical c h).mkQ
  have hP : VermaModeStable c h P := by
    intro m v hv
    change (vermaRadical c h).mkQ (vermaMode c h m v)∈S
    rw [← vermaSimpleMode_mkQ]
    exact hS m _ hv
  have hr : vermaRadical c h≤P := by
    intro v hv
    change (vermaRadical c h).mkQ v∈S
    have hz : (vermaRadical c h).mkQ v=0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hz]
    exact S.zero_mem
  rcases vermaRadical_maximal c h P hP hr with he | he
  · left
    apply bot_unique
    intro x hx
    obtain ⟨v,rfl⟩ := (vermaRadical c h).mkQ_surjective x
    have hv : v∈vermaRadical c h := he ▸ hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hv
  · right
    apply top_unique
    intro x _
    obtain ⟨v,rfl⟩ := (vermaRadical c h).mkQ_surjective x
    have hv : v∈P := he ▸ Submodule.mem_top
    exact hv

end VOA.InverseDS.VirasoroVerma
