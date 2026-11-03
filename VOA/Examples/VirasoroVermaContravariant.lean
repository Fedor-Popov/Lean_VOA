/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaEigenspaces
import VOA.Examples.VirasoroVacuumEvaluation

/-!
# The actual normalized contravariant form on every Virasoro Verma module

Transpose the mode with opposite index on the algebraic dual. The resulting
Virasoro representation contains the highest-coordinate functional as a
highest-weight vector. The Verma universal property therefore constructs the
contravariant form, with no determinant or nondegeneracy assumption.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule VirDeformModes Module LeeYangWardClosure

/-- A dual mode acts on a functional by precomposition with the primal
mode of opposite index. This is complex bilinear, with no conjugation. -/
noncomputable def vermaDualMode (c h : ℂ) (m : ℤ) :
    End ℂ (Module.Dual ℂ (Verma c h)) := (vermaMode c h (-m)).dualMap

/-- Reversing both index and composition preserves the Virasoro relations,
including the sign and normalization of the central term. -/
theorem vermaDualMode_comm (c h : ℂ) (m n : ℤ) :
    ⁅vermaDualMode c h m, vermaDualMode c h n⁆ =
      ((m : ℂ)-n) • vermaDualMode c h (m+n) +
        if m+n=0 then (((m : ℂ)^3-m)/12) •
          (c • (1 : End ℂ (Module.Dual ℂ (Verma c h)))) else 0 := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro v
  have he := congrArg f (vermaMode_comm_apply c h (-n) (-m) v)
  simp only [map_add, map_smul] at he
  change f (vermaMode c h (-n) (vermaMode c h (-m) v)) -
    f (vermaMode c h (-m) (vermaMode c h (-n) v)) = _
  by_cases hz : m+n=0
  · have hn : n = -m := by omega
    subst n
    simp only [neg_neg, add_neg_cancel, if_true, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, vermaDualMode,
      LinearMap.dualMap_apply, Int.cast_neg] at he ⊢
    simp only [map_smul, neg_zero] at he ⊢
    linear_combination he
  · have hh : -n + -m ≠ 0 := by omega
    simp only [hh, if_false] at he
    simp only [hz, if_false, LinearMap.smul_apply,
      add_zero, vermaDualMode, LinearMap.dualMap_apply]
    have hi : -n + -m = -(m+n) := by omega
    rw [hi] at he
    push_cast at he
    simp only [map_zero] at he
    linear_combination he

/-- The dual modes have the original scalar central charge. This packages
the proved commutator into the full mode presentation. -/
noncomputable def vermaDualData (c h : ℂ) :
    CentralVirasoroData (Module.Dual ℂ (Verma c h)) where
  L := vermaDualMode c h
  central := c • 1
  comm := vermaDualMode_comm c h
  central_comm n := by
    change (c • (1 : End ℂ (Module.Dual ℂ (Verma c h)))) * vermaDualMode c h n =
      vermaDualMode c h n * (c • 1)
    simp

/-- Extend the dual modes to the actual full Virasoro Lie algebra. -/
noncomputable def vermaDualRep (c h : ℂ) : VirRep (Module.Dual ℂ (Verma c h)) where
  ρ := fixedRho (vermaDualData c h) rfl
  centralCharge := c
  acts_central := fixedRho_C _ _

/-- The full dual representation acts on each mode by the prescribed
opposite-index transpose. -/
theorem vermaDualRep_mode (c h : ℂ) (m : ℤ) :
    virMode (vermaDualRep c h) m = vermaDualMode c h m := fixedRho_L (vermaDualData c h) rfl m

/-- Extract the coefficient of the actual highest vector in the global
PBW basis. This functional is defined at every charge and highest weight. -/
noncomputable def vermaHighestCoordinate (c h : ℂ) : Module.Dual ℂ (Verma c h) :=
  (Finsupp.lapply ⟨[], sortedWord_nil⟩).comp (vermaSortedBasis c h).repr.toLinearMap

/-- The highest-coordinate functional is normalized on the highest vector. -/
@[simp] theorem vermaHighestCoordinate_highest (c h : ℂ) :
    vermaHighestCoordinate c h (highestVector c h) = 1 := by
  change (vermaSortedBasis c h).repr (negWord c h []) ⟨[], sortedWord_nil⟩ = 1
  rw [← vermaSortedBasis_apply c h ⟨[], sortedWord_nil⟩,
    Module.Basis.repr_self]
  simp

/-- A nonempty creation word has positive relative weight, so its highest
coordinate vanishes. This does not require that the word be sorted. -/
theorem vermaHighestCoordinate_cons (c h : ℂ) (i : ℕ) (w : List ℕ) :
    vermaHighestCoordinate c h (negWord c h (i::w)) = 0 := by
  apply verma_eigen_coordinate_zero c h _ (energyHW (i::w))
    (vermaMode_zero_negWord c h (i::w)) ⟨[], sortedWord_nil⟩
  simp only [energyHW_nil, Nat.cast_zero, ne_eq]
  have he : 0 < energyHW (i::w) := by rw [energyHW_cons]; omega
  exact (Ne.symm (by exact_mod_cast Nat.ne_of_gt he))

/-- The highest-coordinate functional is a highest-weight vector in the
dual representation, with the same charge and highest weight. -/
theorem vermaHighestCoordinate_isHighest (c h : ℂ) :
    IsHighestWeightVector (vermaDualRep c h) (vermaHighestCoordinate c h) c h where
  centralCharge := rfl
  pos_annihilate n hn := by
    rw [vermaDualRep_mode]
    apply (vermaSortedBasis c h).ext
    intro w
    simp only [vermaDualMode, LinearMap.dualMap_apply, vermaSortedBasis_apply,
      LinearMap.zero_apply]
    obtain ⟨i, hi⟩ : ∃ i : ℕ, -n = -(i : ℤ)-1 := ⟨(n-1).toNat, by omega⟩
    rw [hi, ← negWord_cons]
    exact vermaHighestCoordinate_cons c h i w.val
  zero_acts := by
    rw [vermaDualRep_mode]
    apply LinearMap.ext
    intro v
    change (vermaSortedBasis c h).repr (vermaMode c h (-0) v) ⟨[], sortedWord_nil⟩ =
      h * (vermaSortedBasis c h).repr v ⟨[], sortedWord_nil⟩
    rw [neg_zero, verma_L0_coordinate]
    simp

/-- The actual normalized bilinear contravariant form is the universal
Verma map into its algebraic dual, determined by the highest functional. -/
noncomputable def vermaContravariant (c h : ℂ) :
    Verma c h →ₗ[ℂ] Module.Dual ℂ (Verma c h) :=
  universalMap (vermaDualRep c h) (vermaHighestCoordinate c h)
    (vermaHighestCoordinate_isHighest c h)

/-- Pairing the highest vector on the left extracts the highest coordinate
on the right. This fixes the normalization of the entire form. -/
theorem vermaContravariant_highest_left (c h : ℂ) (v : Verma c h) :
    vermaContravariant c h (highestVector c h) v = vermaHighestCoordinate c h v := by
  rw [vermaContravariant, universalMap_highestVector]

/-- The form assigns squared norm one to the highest vector, at every
parameter, including those with a degenerate positive-weight form. -/
@[simp] theorem vermaContravariant_normalized (c h : ℂ) :
    vermaContravariant c h (highestVector c h) (highestVector c h) = 1 := by
  rw [vermaContravariant_highest_left, vermaHighestCoordinate_highest]

/-- Every mode is adjoint to its opposite index in the actual form. This
is inherited from the universal map to the proved dual representation. -/
theorem vermaContravariant_adj (c h : ℂ) (m : ℤ) (u v : Verma c h) :
    vermaContravariant c h (vermaMode c h m u) v =
      vermaContravariant c h u (vermaMode c h (-m) v) := by
  have he := universalMap_intertwines (vermaDualRep c h) (vermaHighestCoordinate c h)
    (vermaHighestCoordinate_isHighest c h) (L m) u
  change vermaContravariant c h (vermaMode c h m u) =
    virMode (vermaDualRep c h) m (vermaContravariant c h u) at he
  rw [he, vermaDualRep_mode]
  rfl


/-- The highest coordinate is also obtained when the highest vector is on
the right. Every nonempty word moves to positive modes killing that vector. -/
theorem vermaContravariant_highest_right (c h : ℂ) (v : Verma c h) :
    vermaContravariant c h v (highestVector c h) = vermaHighestCoordinate c h v := by
  have he : (vermaContravariant c h).flip (highestVector c h) =
      vermaHighestCoordinate c h := by
    apply (vermaSortedBasis c h).ext
    intro w
    simp only [LinearMap.flip_apply, vermaSortedBasis_apply]
    cases hw : w.val with
    | nil => simp [vermaContravariant_normalized]
    | cons i u =>
      rw [vermaHighestCoordinate_cons, negWord_cons, vermaContravariant_adj]
      have hz : vermaMode c h (-(-(i : ℤ)-1)) (highestVector c h) = 0 :=
        verma_pos_annihilate c h _ (by omega)
      rw [hz, map_zero]
  exact LinearMap.congr_fun he v

/-- Symmetry of the actual bilinear form follows from normalization and
opposite-mode adjointness on all creation words. It is proved, not a field
of a proposed form structure. -/
theorem vermaContravariant_symm (c h : ℂ) (u v : Verma c h) :
    vermaContravariant c h u v = vermaContravariant c h v u := by
  have hw : ∀ w : List ℕ, ∀ v : Verma c h,
      vermaContravariant c h (negWord c h w) v =
        vermaContravariant c h v (negWord c h w) := by
    intro w
    induction w with
    | nil => intro v; rw [negWord_nil, vermaContravariant_highest_left,
        vermaContravariant_highest_right]
    | cons i w ih =>
      intro v
      rw [negWord_cons, vermaContravariant_adj, ih, vermaContravariant_adj, neg_neg]
  have he : vermaContravariant c h = (vermaContravariant c h).flip := by
    apply (vermaSortedBasis c h).ext
    intro w
    apply LinearMap.ext
    intro v
    simpa only [LinearMap.flip_apply, vermaSortedBasis_apply] using hw w.val v
  exact LinearMap.congr_fun (LinearMap.congr_fun he u) v

/-- Distinct actual relative levels are orthogonal. The two eigenvalues of
L0 differ by the distinct natural levels, independently of highest weight. -/
theorem vermaContravariant_orthogonal (c h : ℂ) (n k : ℕ)
    (u v : Verma c h) (hu : u ∈ sortedSpan c h n) (hv : v ∈ sortedSpan c h k)
    (hne : n ≠ k) : vermaContravariant c h u v = 0 := by
  have he := vermaContravariant_adj c h 0 u v
  rw [neg_zero, (verma_mem_level_iff_eigen c h n u).mp hu,
    (verma_mem_level_iff_eigen c h k v).mp hv, map_smul,
    LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at he
  have hnk : (n : ℂ)-(k : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  apply (mul_eq_zero.mp (show ((n : ℂ)-(k : ℂ))*vermaContravariant c h u v = 0 by
    linear_combination he)).resolve_left hnk

/-- The radical is preserved by every mode because the form is actually
contravariant. This is the ordinary submodule used in determinant arguments. -/
theorem vermaContravariant_radical_mode (c h : ℂ) (m : ℤ) (u : Verma c h)
    (hu : vermaContravariant c h u = 0) :
    vermaContravariant c h (vermaMode c h m u) = 0 := by
  apply LinearMap.ext
  intro v
  rw [vermaContravariant_adj, hu, LinearMap.zero_apply, LinearMap.zero_apply]

/-- A positive-level singular state belongs to the actual Verma radical.
Only the L1 and L2 equations are required: they imply all positive equations,
and opposite-mode adjointness tests against every PBW word. -/
theorem vermaContravariant_singular_radical (c h : ℂ) (n : ℕ) (hn : 0 < n)
    (u : Verma c h) (hu : u ∈ sortedSpan c h n)
    (h1 : vermaMode c h 1 u = 0) (h2 : vermaMode c h 2 u = 0) :
    vermaContravariant c h u = 0 := by
  have hall := verma_positive_zero_of_one_two c h u h1 h2
  apply (vermaSortedBasis c h).ext
  intro w
  simp only [vermaSortedBasis_apply, LinearMap.zero_apply]
  cases hw : w.val with
  | nil =>
    rw [negWord_nil, vermaContravariant_highest_right]
    apply verma_eigen_coordinate_zero c h u n
      ((verma_mem_level_iff_eigen c h n u).mp hu) ⟨[], sortedWord_nil⟩
    simp only [energyHW_nil, Nat.cast_zero]
    exact Ne.symm (by exact_mod_cast Nat.ne_of_gt hn)
  | cons i w =>
    rw [negWord_cons]
    have he := vermaContravariant_adj c h ((i : ℤ)+1) u (negWord c h w)
    have hz := hall ((i : ℤ)+1) (by omega)
    rw [hz, map_zero, LinearMap.zero_apply] at he
    simpa only [neg_add_rev, neg_add, neg_neg, sub_eq_add_neg, add_comm] using he.symm


/-- Normalization and opposite-mode adjointness uniquely determine the
Verma form. This identifies externally constructed contravariant pairings
with the concrete form above without a determinant assumption. -/
theorem vermaContravariant_unique (c h : ℂ)
    (B : Verma c h →ₗ[ℂ] Module.Dual ℂ (Verma c h))
    (hnorm : B (highestVector c h) (highestVector c h) = 1)
    (hadj : ∀ m u v, B (vermaMode c h m u) v = B u (vermaMode c h (-m) v)) :
    B = vermaContravariant c h := by
  have htop : B (highestVector c h) = vermaHighestCoordinate c h := by
    apply (vermaSortedBasis c h).ext
    intro w
    rw [vermaSortedBasis_apply]
    cases hw : w.val with
    | nil => simpa using hnorm
    | cons i w =>
      rw [vermaHighestCoordinate_cons, negWord_cons]
      have he := hadj ((i : ℤ)+1) (highestVector c h) (negWord c h w)
      have hz : vermaMode c h ((i : ℤ)+1) (highestVector c h) = 0 :=
        verma_pos_annihilate c h _ (by omega)
      rw [hz, map_zero, LinearMap.zero_apply] at he
      simpa only [neg_add, sub_eq_add_neg] using he.symm
  have hw : ∀ w : List ℕ, ∀ v : Verma c h,
      B (negWord c h w) v = vermaContravariant c h (negWord c h w) v := by
    intro w
    induction w with
    | nil => intro v; rw [negWord_nil, htop, vermaContravariant_highest_left]
    | cons i w ih => intro v; rw [negWord_cons, hadj, vermaContravariant_adj, ih]
  apply (vermaSortedBasis c h).ext
  intro w
  apply LinearMap.ext
  intro v
  simpa only [vermaSortedBasis_apply] using hw w.val v

/-- The first translation descendant has squared norm 2h. In particular,
its norm vanishes simply in the highest-weight parameter at h=0; this fixes
the first normalization in a future Verma-to-vacuum determinant comparison. -/
theorem vermaContravariant_translation_norm (c h : ℂ) :
    vermaContravariant c h (negWord c h [0]) (negWord c h [0]) = 2*h := by
  simp only [negWord_cons, negWord_nil, Nat.cast_zero, neg_zero, zero_sub]
  rw [vermaContravariant_adj]
  norm_num only at *
  rw [vermaMode_comm_apply]
  have hp : vermaMode c h 1 (highestVector c h) = 0 := verma_pos_annihilate c h 1 (by norm_num)
  have hz : vermaMode c h 0 (highestVector c h) = h • highestVector c h := verma_zero_acts c h
  norm_num [hp, hz, vermaContravariant_normalized, smul_eq_mul]

end VOA.InverseDS.VirasoroVerma
