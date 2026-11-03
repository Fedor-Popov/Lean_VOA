/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroSingularGram

/-!
# Vacuum Benoit–Saint-Aubin recursion

The parameter t=(N+1)/2 makes the (1,N) highest weight zero.
The recursion uses only the denominators r(N-r) at intermediate levels.
The terminal source is a candidate singular state. Its defining formula
alone is not a proof of singularity, nonvanishing or rigidity. Below, the
L₁ and L₂ Ward identities are proved from the actual mode commutators. They
show the terminal source is killed by all positive modes at c(2,N+1).
Nonvanishing for even N and the norm derivative are not proved here.

The candidate is the vacuum specialization of the Benoit–Saint-Aubin
recursion discussed in G. M. T. Watts, arXiv:2412.07505v2, section 3.
https://arxiv.org/html/2412.07505v2
The Lean proofs below derive the required identities directly; no theorem
from that reference is introduced as an axiom or an additional hypothesis.
-/
namespace VOA.VirModule

/-- The background parameter for the (1,N) zero-highest-weight specialization. -/
noncomputable def bsaParameter (N : ℕ) : ℂ := ((N : ℂ) + 1) / 2

/-- Intermediate vacuum states in the BSA recursion. The terminal denominator
is zero, so the singular candidate is the source sum, not the state at N. -/
noncomputable def bsaState (c : ℂ) (N : ℕ) : ℕ → VirUniv c
  | 0 => vacVec c
  | r+1 => (-bsaParameter N / (((r:ℂ)+1) * ((N:ℂ)-((r:ℂ)+1)))) •
      ∑ j : Fin (r+1), Lop c ((j:ℤ)-((r:ℤ)+1)) (bsaState c N j)
termination_by r => r

/-- The source at level r before division by r(N-r). The level-N source
is the candidate used to seek a singular vector. -/
noncomputable def bsaSource (c : ℂ) (N r : ℕ) : VirUniv c :=
  ∑ j : Fin r, Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j)

/-- The recursion begins at the genuine nonzero vacuum state. -/
theorem bsaState_zero (c : ℂ) (N : ℕ) : bsaState c N 0 = vacVec c := by
  rw [bsaState]

/-- At positive levels, the state is the source multiplied by its explicit
recursion coefficient. At r=N the source must instead be treated separately. -/
theorem bsaState_eq_source (c : ℂ) (N r : ℕ) (hr : 0 < r) :
    bsaState c N r = (-bsaParameter N / ((r:ℂ)*((N:ℂ)-(r:ℂ)))) • bsaSource c N r := by
  cases r with
  | zero => omega
  | succ r => simp only [bsaState, bsaSource, Nat.cast_add, Nat.cast_one]

/-- All intermediate denominators are nonzero. No cancellation or limiting
interpretation of a rational expression is required for this subfamily. -/
theorem bsa_denominator_ne_zero (N r : ℕ) (hr : 0 < r) (hrN : r < N) :
    ((r:ℂ)*((N:ℂ)-(r:ℂ))) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast Nat.ne_of_gt hr
  · apply sub_ne_zero.mpr
    exact_mod_cast Nat.ne_of_gt hrN

/-- Every recursively constructed state has its advertised conformal level,
including states whose coefficient happens to vanish. -/
theorem bsaState_mem_grading (c : ℂ) (N r : ℕ) :
    bsaState c N r ∈ gradingVir c (r:ℤ) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simpa [bsaState_zero] using (virasoroVOA c).vacuum_mem
    | succ r =>
      rw [bsaState]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro j hj
      have hh := Lop_maps_grading c ((j:ℤ)-((r:ℤ)+1)) (ih j j.isLt)
      simpa using hh

/-- The source sum is homogeneous too: each term raises the level j to r. -/
theorem bsaSource_mem_grading (c : ℂ) (N r : ℕ) :
    bsaSource c N r ∈ gradingVir c (r:ℤ) := by
  apply Submodule.sum_mem
  intro j hj
  have hh := Lop_maps_grading c ((j:ℤ)-(r:ℤ)) (bsaState_mem_grading c N j)
  simpa using hh


/-- Commuting L₁ through the next source sum collapses all interior terms
onto the previous source. This is the telescoping identity behind the
quasiprimary part of the BSA construction. -/
theorem bsaSource_L1_step (c : ℂ) (N r : ℕ)
    (hrec : ∀ j : Fin r, Lop c 1 (bsaState c N (j+1)) = (j:ℂ) • bsaState c N j) :
    Lop c 1 (bsaSource c N (r+1)) =
      ((r:ℂ)+2) • bsaSource c N r + (2*(r:ℂ)) • bsaState c N r := by
  classical
  have hcomm (j : Fin (r+1)) :
      Lop c 1 (Lop c ((j:ℤ)-((r:ℤ)+1)) (bsaState c N j)) =
        Lop c ((j:ℤ)-((r:ℤ)+1)) (Lop c 1 (bsaState c N j)) +
          ((r:ℂ)+2-(j:ℂ)) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j) := by
    have hh := Lop_apply_bracket c 1 ((j:ℤ)-((r:ℤ)+1)) (bsaState c N j)
    norm_num at hh
    convert hh using 1 <;> push_cast <;> ring
  have hA : (∑ j : Fin (r+1), Lop c ((j:ℤ)-((r:ℤ)+1)) (Lop c 1 (bsaState c N j))) =
      ∑ j : Fin r, (j:ℂ) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, bsaState_zero, Lop_vacuum c (by norm_num : (-1:ℤ) ≤ 1),
      map_zero, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Fin.val_succ]
    rw [hrec j, map_smul]
    congr 2
    simp
  have hB : (∑ j : Fin (r+1), ((r:ℂ)+2-(j:ℂ)) •
      Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j)) =
      (∑ j : Fin r, ((r:ℂ)+2-(j:ℂ)) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j)) +
        (2*(r:ℂ)) • bsaState c N r := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, sub_self,
      L0_grading_gen c _ (bsaState_mem_grading c N r), smul_smul]
    congr 1
    congr 1
    push_cast
    ring
  simp only [bsaSource, Nat.cast_add, Nat.cast_one, map_sum, hcomm, Finset.sum_add_distrib]
  rw [hA, hB, ← add_assoc, ← Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← add_smul]
  congr 1
  ring


/-- The first intermediate state vanishes because translation kills the
vacuum. This boundary term is essential in the vacuum specialization. -/
theorem bsaState_one (c : ℂ) (N : ℕ) : bsaState c N 1 = 0 := by
  rw [bsaState]
  simp [bsaState_zero, Lop_vacuum c (by norm_num : (-1:ℤ) ≤ -1)]

/-- Every intermediate recursion state satisfies the L₁ Ward identity.
This is proved uniformly in N and in the charge, by telescoping source sums. -/
theorem bsaState_L1 (c : ℂ) (N r : ℕ) (hr : r+1 < N) :
    Lop c 1 (bsaState c N (r+1)) = (r:ℂ) • bsaState c N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hz : r=0
    · subst r; simp [bsaState_one]
    have hs := bsaSource_L1_step c N r (fun j => ih j (by omega) (by omega))
    rw [bsaState_eq_source c N (r+1) (by omega), map_smul, hs]
    rw [bsaState_eq_source c N r (by omega)]
    simp only [smul_add, smul_smul, ← add_smul]
    congr 1
    have hd := bsa_denominator_ne_zero N r (by omega) (by omega)
    have hd' := bsa_denominator_ne_zero N (r+1) (by omega) hr
    unfold bsaParameter
    push_cast at hd' ⊢
    field_simp [hd, hd', (mul_ne_zero_iff.mp hd).1,
      (mul_ne_zero_iff.mp hd).2, (mul_ne_zero_iff.mp hd').1,
      (mul_ne_zero_iff.mp hd').2]
    <;> ring

/-- The terminal source is killed by L₁ for every charge and every N>=2.
This proves quasiprimary behavior only: the L₂ equation and nonvanishing
must still be checked before this candidate can supply a singular state. -/
theorem bsaSource_L1_terminal (c : ℂ) (N : ℕ) (hN : 2 ≤ N) :
    Lop c 1 (bsaSource c N N) = 0 := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  subst N
  rw [bsaSource_L1_step c (r+1) r (fun j => bsaState_L1 c (r+1) j (by omega)),
    bsaState_eq_source c (r+1) r (by omega), smul_smul, ← add_smul]
  have hd : (r:ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have he : ((r:ℂ)+2) + (2*(r:ℂ)) *
      (-bsaParameter (r+1) / ((r:ℂ)*(((r+1:ℕ):ℂ)-(r:ℂ)))) = 0 := by
    unfold bsaParameter
    push_cast
    field_simp
    <;> ring
  rw [he, zero_smul]


/-- The charge of the zero-highest-weight (1,N) specialization. For even N
it is the minimal-model charge c(2,N+1). -/
noncomputable def bsaCharge (N : ℕ) : ℂ :=
  13 - 3*((N:ℂ)+1) - 12/((N:ℂ)+1)

/-- Constant offset in the L₂ Ward identity for the intermediate states. -/
noncomputable def bsaL2Offset (N : ℕ) : ℂ := (3*(N:ℂ)-17)/8

/-- Commuting L₂ through a source reduces it to the source two levels below.
The final two summands give the zero-mode and central contributions; the
first two vanish by the vacuum boundary equations. -/
theorem bsaSource_L2_step (c : ℂ) (N r : ℕ) (b : ℂ)
    (h1 : Lop c 1 (bsaState c N (r+1)) = (r:ℂ) • bsaState c N r)
    (h2 : ∀ j : Fin r, Lop c 2 (bsaState c N (j+2)) =
      ((j:ℂ)+2+b) • bsaState c N j) :
    Lop c 2 (bsaSource c N (r+2)) =
      ((r:ℂ)+6+b) • bsaSource c N r + (7*(r:ℂ)+c/2) • bsaState c N r := by
  classical
  have hcomm (j : Fin (r+2)) :
      Lop c 2 (Lop c ((j:ℤ)-((r:ℤ)+2)) (bsaState c N j)) =
        Lop c ((j:ℤ)-((r:ℤ)+2)) (Lop c 2 (bsaState c N j)) +
          ((r:ℂ)+4-(j:ℂ)) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j) +
          (if j.val=r then c/2 else 0) • bsaState c N j := by
    have hh := Lop_apply_bracket c 2 ((j:ℤ)-((r:ℤ)+2)) (bsaState c N j)
    have he : (2:ℤ)+((j:ℤ)-((r:ℤ)+2)) = (j:ℤ)-(r:ℤ) := by ring
    rw [he] at hh
    have hi : ((j:ℤ)-(r:ℤ)=0) ↔ j.val=r := by omega
    simp only [hi] at hh
    convert hh using 1 <;> push_cast <;> ring
  have hA : (∑ j : Fin (r+2), Lop c ((j:ℤ)-((r:ℤ)+2)) (Lop c 2 (bsaState c N j))) =
      ∑ j : Fin r, ((j:ℂ)+2+b) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.cast_zero, Nat.zero_add,
      bsaState_zero, bsaState_one, Lop_vacuum c (by norm_num : (-1:ℤ) ≤ 2),
      map_zero, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show j.val+1+1=j.val+2 by omega, h2 j, map_smul]
    congr 2
    push_cast
    ring
  have hB : (∑ j : Fin (r+2), ((r:ℂ)+4-(j:ℂ)) •
      Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j)) =
      (∑ j : Fin r, ((r:ℂ)+4-(j:ℂ)) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j)) +
        (7*(r:ℂ)) • bsaState c N r := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one, sub_self,
      show (r:ℤ)+1-(r:ℤ)=1 by ring, h1,
      L0_grading_gen c _ (bsaState_mem_grading c N r), smul_smul]
    push_cast
    module
  have hC : (∑ j : Fin (r+2), (if j.val=r then c/2 else 0) • bsaState c N j) =
      (c/2) • bsaState c N r := by
    rw [Finset.sum_eq_single (⟨r,by omega⟩ : Fin (r+2))]
    · simp
    · intro j hj hjr
      have he : j.val ≠ r := fun he => hjr (Fin.ext he)
      simp [he]
    · simp
  simp only [bsaSource, Nat.cast_add, Nat.cast_ofNat, map_sum, hcomm,
    Finset.sum_add_distrib]
  rw [hA,hB,hC]
  rw [← add_assoc, ← Finset.sum_add_distrib, Finset.smul_sum]
  have hs : (∑ j : Fin r, (((j:ℂ)+2+b) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j) +
      ((r:ℂ)+4-(j:ℂ)) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j))) =
      ∑ j : Fin r, ((r:ℂ)+6+b) • Lop c ((j:ℤ)-(r:ℤ)) (bsaState c N j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← add_smul]
    congr 1
    ring
  rw [hs]
  module


/-- At the specialized charge, every intermediate state satisfies the L₂
Ward identity. The proof uses the explicit scalar recursion and its nonzero
intermediate denominators, rather than a fusion or singular-vector assumption. -/
theorem bsaState_L2 (N r : ℕ) (hr : r+2 < N) :
    Lop (bsaCharge N) 2 (bsaState (bsaCharge N) N (r+2)) =
      ((r:ℂ)+2+bsaL2Offset N) • bsaState (bsaCharge N) N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    have hs := bsaSource_L2_step (bsaCharge N) N r (bsaL2Offset N)
      (bsaState_L1 _ N r (by omega)) (fun j => ih j j.isLt (by omega))
    rw [bsaState_eq_source _ N (r+2) (by omega), map_smul, hs]
    have hn : (N:ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero N
    have hd' := bsa_denominator_ne_zero N (r+2) (by omega) hr
    by_cases hz : r=0
    · subst r
      simp only [bsaSource, Fin.sum_univ_zero, smul_zero, zero_add, smul_smul,
        Nat.cast_zero, Nat.cast_ofNat]
      congr 1
      unfold bsaParameter bsaCharge bsaL2Offset
      norm_num at hd' ⊢
      field_simp [hn, hd']
      <;> ring
    · rw [bsaState_eq_source _ N r (by omega)]
      simp only [smul_add, smul_smul, ← add_smul]
      congr 1
      have hd := bsa_denominator_ne_zero N r (by omega) (by omega)
      unfold bsaParameter bsaCharge bsaL2Offset
      push_cast at hd' ⊢
      field_simp [hn, hd, hd', (mul_ne_zero_iff.mp hd).1,
        (mul_ne_zero_iff.mp hd).2, (mul_ne_zero_iff.mp hd').1,
        (mul_ne_zero_iff.mp hd').2]
      <;> ring

/-- At the prescribed charge the terminal source is killed by L₂. Together
with the L₁ theorem this proves all positive-mode equations. It does not yet
prove that the terminal source is nonzero. -/
theorem bsaSource_L2_terminal (N : ℕ) (hN : 3 ≤ N) :
    Lop (bsaCharge N) 2 (bsaSource (bsaCharge N) N N) = 0 := by
  obtain ⟨r,hr⟩ : ∃ r : ℕ, N=r+2 := ⟨N-2,by omega⟩
  subst N
  rw [bsaSource_L2_step _ (r+2) r (bsaL2Offset (r+2))
    (bsaState_L1 _ (r+2) r (by omega))
    (fun j => bsaState_L2 (r+2) j (by omega)),
    bsaState_eq_source _ (r+2) r (by omega), smul_smul, ← add_smul]
  have hd : (r:ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hn : (r:ℂ)+3 ≠ 0 := by exact_mod_cast (show r+3 ≠ 0 by omega)
  have he : ((r:ℂ)+6+bsaL2Offset (r+2)) + (7*(r:ℂ)+bsaCharge (r+2)/2) *
      (-bsaParameter (r+2) / ((r:ℂ)*(((r+2:ℕ):ℂ)-(r:ℂ)))) = 0 := by
    unfold bsaParameter bsaCharge bsaL2Offset
    push_cast
    field_simp [hd, hn]
    <;> ring_nf
    <;> field_simp [show (3:ℂ)+(r:ℂ) ≠ 0 by simpa [add_comm] using hn]
    <;> ring
  rw [he, zero_smul]

/-- The terminal BSA source satisfies every positive-mode equation, uniformly
for N>=3 at its specialized charge. Nonvanishing is intentionally not claimed. -/
theorem bsaSource_positive_terminal (N : ℕ) (hN : 3 ≤ N) :
    ∀ m : ℤ, 0 < m → Lop (bsaCharge N) m (bsaSource (bsaCharge N) N N) = 0 :=
  VirDeformModes.NormalOrdering.Lop_positive_eq_zero_of_one_two _ _
    (bsaSource_L1_terminal _ N (by omega)) (bsaSource_L2_terminal N hN)


/-- The specialized charge is exactly c(2,N+1). To obtain coprime minimal
labels from this expression, N must be even. The equality itself needs no
coprimality assumption. -/
theorem bsaCharge_eq_minimal (N : ℕ) :
    bsaCharge N = (minimalCentralCharge 2 (N+1) : ℂ) := by
  have hn : (N:ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero N
  unfold bsaCharge minimalCentralCharge
  push_cast
  field_simp [hn]
  <;> ring

/-- The explicit terminal source lies in the canonical maximal ideal at
its prescribed charge. This statement also holds when the source is zero;
nonvanishing for even N remains a separate required construction step. -/
theorem bsaSource_mem_maxIdeal (N : ℕ) (hN : 3 ≤ N) :
    bsaSource (bsaCharge N) N N ∈ VirSimple.maxIdealVir (bsaCharge N) :=
  VirDeformModes.NormalOrdering.singular_mem_maxIdeal _ (by omega) _
    (bsaSource_mem_grading _ N N) (bsaSource_L1_terminal _ N (by omega))
    (bsaSource_L2_terminal N hN)
end VOA.VirModule
