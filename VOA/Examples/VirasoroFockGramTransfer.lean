/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFockLevelDimension
import VOA.Examples.VirasoroVermaMaximalRadical
import VOA.Examples.VirasoroVermaSingularEmbedding

/-!
# From actual charged Fock singular states to actual Gram roots

The universal map need not be injective or surjective in general. Under a
nondegenerate Gram determinant, its kernel vanishes at that level and all
earlier levels. Equal actual level dimensions then allow a Fock singular
state to be lifted, contradicting nondegeneracy. No faithfulness of a free
field realization or unproved character formula is assumed.
-/
namespace VOA.VirasoroScreening
open HeisenbergN MvPolynomial InverseDS.VirasoroVerma
open InverseDS.LeeYangFockVirasoro VirModule
open scoped Classical

/-- Nondegeneracy at level N excludes radical vectors at every earlier
level: a single negative mode carries any nonzero such vector to level N,
and descendant independence prevents its disappearance. -/
theorem verma_radical_zero_below (c h : ℂ) (N k : ℕ)
    (hd : (vermaGramMatrix c h N).det ≠ 0) (hk : k ≤ N)
    (v : Verma c h) (hv : v ∈ sortedSpan c h k)
    (hr : vermaContravariant c h v = 0) : v = 0 := by
  by_cases he : k = N
  · subst k; exact verma_radical_zero_of_det_ne_zero c h N hd v hv hr
  · by_contra hn
    let w : List ℕ := [N-k-1]
    have hw : SortedWord w := sortedWord_singleton _
    have hew : k + energyHW w = N := by simp [w, energyHW]; omega
    have hg := vermaDescendant_mem_level c h w k v hv
    rw [hew] at hg
    have hz := verma_radical_zero_of_det_ne_zero c h N hd _ hg
      (vermaDescendant_radical c h w v hr)
    exact (vermaDescendant_linearIndependent c h v hn).ne_zero ⟨w,hw⟩ hz

/-- The actual universal map sends the Verma highest vector to the
constant polynomial in the charged rank-one Fock representation. -/
noncomputable def chargedFockMap (ell p : ℂ) :
    Verma (1-24*ell^2) (p^2-2*ell*p) →ₗ[ℂ] FockN 1 :=
  universalMap (chargedFockRep ell p) (vacuumN 1) (chargedFock_isHighest ell p)

/-- Every integer mode intertwines with the actual charged Fock map. -/
theorem chargedFockMap_mode (ell p : ℂ) (m : ℤ)
    (v : Verma (1-24*ell^2) (p^2-2*ell*p)) :
    chargedFockMap ell p (vermaMode _ _ m v) =
      sectorVirasoro ell p m (chargedFockMap ell p v) := by
  simpa only [chargedFockMap, chargedFockRep, VirDeformModes.fixedRho_L,
    chargedFockData] using universalMap_intertwines (chargedFockRep ell p)
      (vacuumN 1) (chargedFock_isHighest ell p) (VOA.L m) v

/-- The kernel of the universal Fock map is a proper invariant submodule,
so it lies in the canonical contravariant radical. -/
theorem chargedFockMap_kernel_radical (ell p : ℂ)
    (v : Verma (1-24*ell^2) (p^2-2*ell*p))
    (hv : chargedFockMap ell p v = 0) : vermaContravariant _ _ v = 0 := by
  apply verma_proper_submodule_le_radical _ _ (LinearMap.ker (chargedFockMap ell p)) ?_ ?_ hv
  · intro m x hx
    change chargedFockMap ell p (vermaMode _ _ m x) = 0
    rw [chargedFockMap_mode, show chargedFockMap ell p x = 0 from hx, map_zero]
  · intro he
    have hh : highestVector (1-24*ell^2) (p^2-2*ell*p) ∈
        LinearMap.ker (chargedFockMap ell p) := he ▸ Submodule.mem_top
    change chargedFockMap ell p (highestVector _ _) = 0 at hh
    rw [chargedFockMap, universalMap_highestVector] at hh
    exact one_ne_zero hh

/-- The actual universal map preserves oscillator energy. This follows
from the zero-mode eigenvalue and individual polynomial coefficients. -/
theorem chargedFockMap_mem_level (ell p : ℂ) (N : ℕ)
    (v : Verma (1-24*ell^2) (p^2-2*ell*p)) (hv : v ∈ sortedSpan _ _ N) :
    chargedFockMap ell p v ∈ gradingWN 1 N := by
  have he := congrArg (chargedFockMap ell p)
    ((verma_mem_level_iff_eigen _ _ N v).mp hv)
  rw [chargedFockMap_mode, map_smul] at he
  intro d hd
  have hc := congrArg (coeff d) he
  rw [chargedFock_zero_coefficient, coeff_smul] at hc
  simp only [smul_eq_mul] at hc
  have hh : (Finsupp.weight weightFnN d:ℂ) = (N:ℂ) := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (by linear_combination hc :
      ((Finsupp.weight weightFnN d:ℂ)-(N:ℂ))*coeff d (chargedFockMap ell p v)=0)).resolve_right hd
  exact_mod_cast hh

/-- The genuine universal map restricted to the corresponding actual
finite-dimensional level subspaces. -/
noncomputable def chargedFockLevelMap (ell p : ℂ) (N : ℕ) :
    sortedSpan (1-24*ell^2) (p^2-2*ell*p) N →ₗ[ℂ] gradingWN 1 N :=
  ((chargedFockMap ell p).comp (sortedSpan _ _ N).subtype).codRestrict _
    (fun v => chargedFockMap_mem_level ell p N v v.property)

/-- If the level-N Gram matrix is nondegenerate, the actual universal map
is injective on every level at most N. Its kernel cannot hide an earlier
radical vector. -/
theorem chargedFockLevelMap_injective (ell p : ℂ) (N k : ℕ)
    (hd : (vermaGramMatrix (1-24*ell^2) (p^2-2*ell*p) N).det ≠ 0)
    (hk : k ≤ N) : Function.Injective (chargedFockLevelMap ell p k) := by
  intro x y he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply verma_radical_zero_below _ _ N k hd hk _ (Submodule.sub_mem _ x.property y.property)
  apply chargedFockMap_kernel_radical ell p
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val he)

/-- Equal proved level dimensions turn this injectivity into actual
surjectivity, without assuming a Fock character or a free-field isomorphism. -/
theorem chargedFockLevelMap_surjective (ell p : ℂ) (N : ℕ)
    (hd : (vermaGramMatrix (1-24*ell^2) (p^2-2*ell*p) N).det ≠ 0) :
    Function.Surjective (chargedFockLevelMap ell p N) := by
  letI := (vermaLevelBasis (1-24*ell^2) (p^2-2*ell*p) N).finiteDimensional_of_finite
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (fock_verma_level_finrank (1-24*ell^2) (p^2-2*ell*p) N).symm).mp
  exact chargedFockLevelMap_injective ell p N N hd le_rfl

/-- Under a nondegenerate level-N Gram matrix, annihilation of the Fock
image by a positive mode forces annihilation of its homogeneous Verma lift. -/
theorem chargedFockMap_lift_positive (ell p : ℂ) (N : ℕ)
    (hd : (vermaGramMatrix (1-24*ell^2) (p^2-2*ell*p) N).det ≠ 0)
    (v : Verma (1-24*ell^2) (p^2-2*ell*p)) (hv : v ∈ sortedSpan _ _ N)
    (m : ℤ) (hm : 0 < m)
    (hz : sectorVirasoro ell p m (chargedFockMap ell p v) = 0) :
    vermaMode _ _ m v = 0 := by
  by_cases hhigh : (N:ℤ) < m
  · exact verma_mode_above_level _ _ N v hv m hhigh
  · let k := ((N:ℤ)-m).toNat
    have hk : (N:ℤ)-m = (k:ℤ) := by dsimp [k]; omega
    apply verma_radical_zero_below _ _ N k hd (by omega) _
      (verma_mode_mem_level _ _ N k v hv m hk)
    apply chargedFockMap_kernel_radical ell p
    rw [chargedFockMap_mode, hz]

/-- A genuine positive-energy singular polynomial in the charged Fock
module forces a zero of the ACTUAL Verma Gram determinant at that energy.
The proof establishes the needed lifting internally; Fock faithfulness is
neither assumed nor asserted. -/
theorem chargedFock_singular_gram_root (ell p : ℂ) (N : ℕ) (hN : 0 < N)
    (P : FockN 1) (hP : P ∈ gradingWN 1 N) (hne : P ≠ 0)
    (h1 : sectorVirasoro ell p 1 P = 0) (h2 : sectorVirasoro ell p 2 P = 0) :
    (vermaGramMatrix (1-24*ell^2) (p^2-2*ell*p) N).det = 0 := by
  by_contra hd
  obtain ⟨v,hv⟩ := chargedFockLevelMap_surjective ell p N hd ⟨P,hP⟩
  have he : chargedFockMap ell p v = P := congrArg Subtype.val hv
  have hvne : (v : Verma (1-24*ell^2) (p^2-2*ell*p)) ≠ 0 := by
    intro hz
    apply hne
    rw [← he, hz, map_zero]
  have hv1 := chargedFockMap_lift_positive ell p N hd v v.property 1 (by norm_num)
    (by rw [he]; exact h1)
  have hv2 := chargedFockMap_lift_positive ell p N hd v v.property 2 (by norm_num)
    (by rw [he]; exact h2)
  obtain ⟨a,ha⟩ := exists_vermaLevelState (1-24*ell^2) (p^2-2*ell*p) N v v.property
  apply hd
  apply vermaGramMatrix_det_zero_of_singular _ _ N hN a
  · intro hz
    apply hvne
    rw [← ha, hz]
    exact (vermaLevelState_eq_zero_iff _ _ N 0).mpr rfl
  · simpa only [ha] using hv1
  · simpa only [ha] using hv2

end VOA.VirasoroScreening
