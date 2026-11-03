/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaContravariant

/-!
# Extracting the highest component inside an invariant subspace

A finite product of normalized L0 shifts kills every positive level in a
finite PBW expansion while fixing the highest vector. Thus every subspace
stable under L0 contains the highest component of each of its states.
No assumption that the subspace is graded is needed.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- The finite interpolation scalar which is one at level zero and kills
all positive integer levels up to N. Each denominator is a positive integer. -/
noncomputable def vermaHighestFilterScalar (N e : ℕ) : ℂ :=
  ∏ j ∈ Finset.range N, (1-(e:ℂ)/((j:ℂ)+1))

/-- Add the next normalized factor to the finite interpolation product. -/
theorem vermaHighestFilterScalar_succ (N e : ℕ) :
    vermaHighestFilterScalar (N+1) e=
      (1-(e:ℂ)/((N:ℂ)+1))*vermaHighestFilterScalar N e := by
  simp [vermaHighestFilterScalar,Finset.prod_range_succ,mul_comm]

/-- The interpolation filter fixes level zero exactly. -/
theorem vermaHighestFilterScalar_zero (N : ℕ) : vermaHighestFilterScalar N 0=1 := by
  simp [vermaHighestFilterScalar]

/-- A positive level within the cutoff is killed by its matching factor. -/
theorem vermaHighestFilterScalar_vanish (N e : ℕ) (he : 0<e) (hN : e≤N) :
    vermaHighestFilterScalar N e=0 := by
  apply Finset.prod_eq_zero (Finset.mem_range.mpr (show e-1<N by omega))
  have hn : ((e-1:ℕ):ℂ)+1=(e:ℂ) := by
    have hh : e-1+1=e := by omega
    exact_mod_cast hh
  rw [hn,div_self (by exact_mod_cast Nat.ne_of_gt he),sub_self]

/-- A finite polynomial in actual L0, normalized to fix the highest vector.
Its Nth step removes the relative eigenvalue N, without changing previous zeros. -/
noncomputable def vermaHighestFilter (c h : ℂ) : ℕ → Module.End ℂ (Verma c h)
  | 0 => LinearMap.id
  | N+1 => (LinearMap.id - (((N:ℂ)+1)⁻¹) •
      (vermaMode c h 0-h • LinearMap.id)).comp (vermaHighestFilter c h N)

/-- On each PBW word the actual filter acts by the finite interpolation
scalar at that word's energy. This identifies the operator, not only its roots. -/
theorem vermaHighestFilter_word (c h : ℂ) (N : ℕ) (w : List ℕ) :
    vermaHighestFilter c h N (negWord c h w)=
      vermaHighestFilterScalar N (energyHW w) • negWord c h w := by
  induction N with
  | zero => simp [vermaHighestFilter,vermaHighestFilterScalar]
  | succ N ih =>
    rw [vermaHighestFilter,LinearMap.comp_apply,ih,vermaHighestFilterScalar_succ]
    simp only [map_smul,LinearMap.sub_apply,LinearMap.id_apply,LinearMap.smul_apply,
      vermaMode_zero_negWord]
    module

/-- The finite L0 filter preserves any L0-stable linear subspace. This does
not assume that the subspace already decomposes into homogeneous levels. -/
theorem vermaHighestFilter_mem (c h : ℂ) (S : Submodule ℂ (Verma c h))
    (hS : ∀ v ∈ S, vermaMode c h 0 v ∈ S) (N : ℕ) (v : Verma c h) (hv : v∈S) :
    vermaHighestFilter c h N v∈S := by
  induction N with
  | zero => exact hv
  | succ N ih =>
    change vermaHighestFilter c h N v - ((N:ℂ)+1)⁻¹ •
      (vermaMode c h 0 (vermaHighestFilter c h N v)-h • vermaHighestFilter c h N v)∈S
    exact S.sub_mem ih (S.smul_mem _ (S.sub_mem (hS _ ih) (S.smul_mem h ih)))

/-- A nonempty creation word has positive relative energy. Only the empty
word has energy zero, so filtering positive levels isolates the highest line. -/
theorem verma_energy_zero_iff (w : List ℕ) : energyHW w=0 ↔ w=[] := by
  cases w with
  | nil => simp
  | cons i w => simp [energyHW_cons]

/-- After choosing a cutoff containing the finite PBW support of a state,
the actual filter returns precisely its highest-vector coordinate. -/
theorem vermaHighestFilter_eq_coordinate (c h : ℂ) (v : Verma c h) (N : ℕ)
    (hN : ∀ w ∈ ((vermaSortedBasis c h).repr v).support, energyHW w.val≤N) :
    vermaHighestFilter c h N v=
      vermaHighestCoordinate c h v • highestVector c h := by
  classical
  let b := vermaSortedBasis c h
  let a := b.repr v
  have he := congrArg (vermaHighestFilter c h N) (b.linearCombination_repr v)
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    b,vermaSortedBasis_apply,vermaHighestFilter_word] at he
  rw [← he]
  let z : {w : List ℕ // SortedWord w} := ⟨[],sortedWord_nil⟩
  rw [Finset.sum_eq_single z]
  · simp [z,vermaHighestFilterScalar_zero,vermaHighestCoordinate,a,b]
  · intro w hw hwz
    have hp : 0<energyHW w.val := by
      have hn : w.val≠[] := fun hh => hwz (Subtype.ext hh)
      have he := (verma_energy_zero_iff w.val).not.mpr hn
      omega
    rw [vermaHighestFilterScalar_vanish N _ hp (hN w hw),zero_smul,smul_zero]
  · intro hz
    have ha : a z=0 := Finsupp.notMem_support_iff.mp hz
    change a z • (vermaHighestFilterScalar N (energyHW z.val) • negWord c h z.val)=_
    rw [ha,zero_smul]

/-- Every L0-stable subspace contains the highest component of each state.
The cutoff is selected from its finite actual PBW support. -/
theorem vermaHighestCoordinate_smul_mem (c h : ℂ) (S : Submodule ℂ (Verma c h))
    (hS : ∀ v ∈ S, vermaMode c h 0 v∈S) (v : Verma c h) (hv : v∈S) :
    vermaHighestCoordinate c h v • highestVector c h∈S := by
  classical
  let a := (vermaSortedBasis c h).repr v
  let N := a.support.sup (fun w => energyHW w.val)
  rw [← vermaHighestFilter_eq_coordinate c h v N (fun w hw => Finset.le_sup (f := fun w => energyHW w.val) hw)]
  exact vermaHighestFilter_mem c h S hS N v hv

end VOA.InverseDS.VirasoroVerma
