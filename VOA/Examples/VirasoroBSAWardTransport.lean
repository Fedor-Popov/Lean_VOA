/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaBSA
import VOA.Examples.VirasoroDescendantTriangular

/-!
# Transporting the explicit BSA recursion with only positive Ward identities

Only commutators with modes 0, 1 and 2 are used. No relation between two
negative modes is assumed. The seed is highest for these operators; the
terminal conclusion is its two positive Ward equations, not nonvanishing.
-/
namespace VOA.BSAWardTransport
open VOA.InverseDS.VirasoroVerma VOA.VirModule
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Exactly the operator and seed identities used by the explicit BSA
proof. This is less than a Virasoro representation: no negative-negative
or higher positive relation is a field. It will be constructed for the
actual descendant operators, not assumed as a rigidity hypothesis. -/
structure System (V : Type*) [AddCommGroup V] [Module ℂ V] (c h : ℂ) where
  /-- Integer-indexed operators; only indices at most two enter the proof. -/
  mode : ℤ → Module.End ℂ V
  /-- The initial vector, allowed to be zero in this Ward-identity theorem. -/
  seed : V
  /-- The initial vector has weight h. -/
  seed_zero : mode 0 seed = h • seed
  /-- The first positive operator kills the seed. -/
  seed_one : mode 1 seed = 0
  /-- The second positive operator kills the seed. -/
  seed_two : mode 2 seed = 0
  /-- The three required positive/negative commutation identities. -/
  comm_law : ∀ (m n : ℤ), 0≤m → m≤2 → n<0 → ∀ v,
    mode m (mode n v)=mode n (mode m v)+((m:ℂ)-(n:ℂ)) • mode (m+n) v+
      (if m+n=0 then c*((m:ℂ)^3-(m:ℂ))/12 else 0) • v

/-- Apply the restricted commutator with its index bounds discharged explicitly. -/
theorem System.comm {c h : ℂ} (A : System V c h) (m n : ℤ) (v : V)
    (hm : 0≤m := by omega) (hm2 : m≤2 := by omega) (hn : n<0 := by omega) :
    A.mode m (A.mode n v)=A.mode n (A.mode m v)+((m:ℂ)-(n:ℂ)) • A.mode (m+n) v+
      (if m+n=0 then c*((m:ℂ)^3-(m:ℂ))/12 else 0) • v := A.comm_law m n hm hm2 hn v

/-- The free-parameter BSA recursion in the actual Verma module. The source
at the terminal level is kept separate from the zero terminal denominator. -/
noncomputable def transportState {c h : ℂ} (A : System V c h) (t : ℂ) (N : ℕ) : ℕ → V
  | 0 => A.seed
  | r+1 => (-t / (((r:ℂ)+1)*((N:ℂ)-((r:ℂ)+1)))) •
      ∑ j : Fin (r+1), A.mode ((j:ℤ)-((r:ℤ)+1)) (transportState A t N j)
termination_by r => r

/-- The source sum before division; its value at level N is the terminal
candidate. Unlike the vacuum case, the first intermediate state can be nonzero. -/
noncomputable def transportSource {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ) : V :=
  ∑ j : Fin r, A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j)

/-- Level zero is the actual highest vector. -/
@[simp] theorem transportState_zero {c h : ℂ} (A : System V c h) (t : ℂ) (N : ℕ) :
    transportState A t N 0=A.seed := by rw [transportState]

/-- At positive levels the recursion multiplies the source by its displayed
coefficient. Only intermediate levels are later divided by nonzero scalars. -/
theorem transportState_eq_source {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ) (hr : 0<r) :
    transportState A t N r=(-t/((r:ℂ)*((N:ℂ)-(r:ℂ)))) • transportSource A t N r := by
  cases r with
  | zero => omega
  | succ r => simp only [transportState,transportSource,Nat.cast_add,Nat.cast_one]

/-- Commuting L₀ through a source raises the relative level by exactly r. -/
theorem transportSource_L0 {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ)
    (ih : ∀ j : Fin r, A.mode 0 (transportState A t N j)=
      (h+(j:ℂ)) • transportState A t N j) :
    A.mode 0 (transportSource A t N r)=
      (h+(r:ℂ)) • transportSource A t N r := by
  simp only [transportSource,map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [A.comm 0 _ _ (by omega) (by omega) (by omega),ih]
  simp only [show ¬ (j:ℤ)-(r:ℤ)=0 by omega,if_false,add_zero,
    map_smul,zero_add,Int.cast_sub,Int.cast_natCast,Int.cast_zero]
  module

/-- All recursively constructed states have actual L₀ weight h+r. -/
theorem transportState_L0 {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ) :
    A.mode 0 (transportState A t N r)=
      (h+(r:ℂ)) • transportState A t N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : r=0
    · subst r
      simpa using A.seed_zero
    · rw [transportState_eq_source A t N r (by omega),map_smul,
        transportSource_L0 A t N r (fun j => ih j j.isLt),smul_comm]

/-- L₁ telescoping with the highest-weight boundary term retained. -/
theorem transportSource_L1_step {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ) (a : ℂ)
    (hrec : ∀ j : Fin r, A.mode 1 (transportState A t N (j+1)) = ((j:ℂ)+a) • transportState A t N j) :
    A.mode 1 (transportSource A t N (r+1)) =
      ((r:ℂ)+2+a) • transportSource A t N r + (2*(h+(r:ℂ))) • transportState A t N r := by
  classical
  have hcomm (j : Fin (r+1)) :
      A.mode 1 (A.mode ((j:ℤ)-((r:ℤ)+1)) (transportState A t N j)) =
        A.mode ((j:ℤ)-((r:ℤ)+1)) (A.mode 1 (transportState A t N j)) +
          ((r:ℂ)+2-(j:ℂ)) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j) := by
    have hh := A.comm 1 ((j:ℤ)-((r:ℤ)+1)) (transportState A t N j)
    norm_num at hh
    convert hh using 1 <;> push_cast <;> ring
  have hA : (∑ j : Fin (r+1), A.mode ((j:ℤ)-((r:ℤ)+1)) (A.mode 1 (transportState A t N j))) =
      ∑ j : Fin r, ((j:ℂ)+a) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, transportState_zero, show A.mode 1 (A.seed)=0 from A.seed_one,
      map_zero, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Fin.val_succ]
    rw [hrec j, map_smul]
    congr 2
    simp
  have hB : (∑ j : Fin (r+1), ((r:ℂ)+2-(j:ℂ)) •
      A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j)) =
      (∑ j : Fin r, ((r:ℂ)+2-(j:ℂ)) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j)) +
        (2*(h+(r:ℂ))) • transportState A t N r := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, sub_self,
      transportState_L0 A t N r, smul_smul]
    congr 1
    congr 1
    push_cast
    ring
  simp only [transportSource, Nat.cast_add, Nat.cast_one, map_sum, hcomm, Finset.sum_add_distrib]
  rw [hA, hB, ← add_assoc, ← Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← add_smul]
  congr 1
  ring





/-- The first state includes the L₋₁ descendant, which need not vanish in a
Verma module. Its coefficient is nonzero when t and N-1 are nonzero. -/
theorem transportState_one {c h : ℂ} (A : System V c h) (t : ℂ) (N : ℕ) :
    transportState A t N 1=(-t/((N:ℂ)-1)) • A.mode (-1) (A.seed) := by
  rw [transportState]
  simp

/-- Along the generic highest-weight curve, L₁ lowers every intermediate
state with an affine coefficient in its level. -/
theorem transportState_L1 (t : ℂ) (N r : ℕ) {c : ℂ} (A : System V c (vermaBSAWeight N t)) (ht : t≠0) (hr : r+1<N) :
    A.mode 1 (transportState A t N (r+1))=
      ((r:ℂ)+vermaBSAOffset1 N t) • transportState A t N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hz : r=0
    · subst r
      rw [transportState_one,map_smul,A.comm 1 (-1) A.seed]
      norm_num [A.seed_one,A.seed_two,A.seed_zero,transportState_zero]
      simp only [smul_smul]
      have hn : (N:ℂ)-1≠0 := by exact_mod_cast (show (N:ℤ)-1≠0 by omega)
      congr 1
      unfold vermaBSAWeight vermaBSAOffset1
      field_simp
      <;> ring
    · have hs := transportSource_L1_step A t N r
        (vermaBSAOffset1 N t) (fun j => ih j (by omega) (by omega))
      rw [transportState_eq_source A t N (r+1) (by omega),map_smul,hs]
      rw [transportState_eq_source A t N r (by omega)]
      simp only [smul_add,smul_smul,← add_smul]
      congr 1
      have hd := bsa_denominator_ne_zero N r (by omega) (by omega)
      have hd' := bsa_denominator_ne_zero N (r+1) (by omega) hr
      unfold vermaBSAWeight vermaBSAOffset1
      push_cast at hd' ⊢
      field_simp [ht,hd,hd',(mul_ne_zero_iff.mp hd).1,(mul_ne_zero_iff.mp hd).2,
        (mul_ne_zero_iff.mp hd').1,(mul_ne_zero_iff.mp hd').2]
      <;> ring

/-- The terminal source is killed by L₁ at every nonzero parameter on the
(1,N) highest-weight curve, independently of the central charge. -/
theorem transportSource_L1_terminal (t : ℂ) (N : ℕ) {c : ℂ} (A : System V c (vermaBSAWeight N t)) (ht : t≠0) (hN : 2≤N) :
    A.mode 1 (transportSource A t N N)=0 := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  subst N
  rw [transportSource_L1_step A t _ r (vermaBSAOffset1 (r+1) t)
      (fun j => transportState_L1 t (r+1) j A ht (by omega)),
    transportState_eq_source A t _ r (by omega),smul_smul,← add_smul]
  have hd : (r:ℂ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have he : ((r:ℂ)+2+vermaBSAOffset1 (r+1) t)+
      (2*(vermaBSAWeight (r+1) t+(r:ℂ)))*(-t/((r:ℂ)*(((r+1:ℕ):ℂ)-(r:ℂ))))=0 := by
    unfold vermaBSAOffset1 vermaBSAWeight
    push_cast
    field_simp
    <;> ring
  rw [he,zero_smul]



/-- L₂ kills the first intermediate state because the highest vector is
killed by L₁ and L₂. No vacuum translation relation is used. -/
theorem transportState_L2_one {c h : ℂ} (A : System V c h) (t : ℂ) (N : ℕ) :
    A.mode 2 (transportState A t N 1)=0 := by
  rw [transportState_one,map_smul,A.comm 2 (-1) A.seed]
  norm_num [A.seed_one,A.seed_two]

/-- L₂ telescoping, including the highest-weight and L₁ boundary terms. -/
theorem transportSource_L2_step {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ) (a b : ℂ)
    (h1 : A.mode 1 (transportState A t N (r+1)) = ((r:ℂ)+a) • transportState A t N r)
    (h2 : ∀ j : Fin r, A.mode 2 (transportState A t N (j+2)) =
      ((j:ℂ)+b) • transportState A t N j) :
    A.mode 2 (transportSource A t N (r+2)) =
      ((r:ℂ)+4+b) • transportSource A t N r + (7*(r:ℂ)+4*h+3*a+c/2) • transportState A t N r := by
  classical
  have hcomm (j : Fin (r+2)) :
      A.mode 2 (A.mode ((j:ℤ)-((r:ℤ)+2)) (transportState A t N j)) =
        A.mode ((j:ℤ)-((r:ℤ)+2)) (A.mode 2 (transportState A t N j)) +
          ((r:ℂ)+4-(j:ℂ)) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j) +
          (if j.val=r then c/2 else 0) • transportState A t N j := by
    have hh := A.comm 2 ((j:ℤ)-((r:ℤ)+2)) (transportState A t N j)
    have he : (2:ℤ)+((j:ℤ)-((r:ℤ)+2)) = (j:ℤ)-(r:ℤ) := by ring
    rw [he] at hh
    have hi : ((j:ℤ)-(r:ℤ)=0) ↔ j.val=r := by omega
    simp only [hi] at hh
    split_ifs at hh ⊢ <;> try simp only [zero_smul] at hh ⊢
    all_goals convert hh using 1 <;> push_cast <;> ring
  have hA : (∑ j : Fin (r+2), A.mode ((j:ℤ)-((r:ℤ)+2)) (A.mode 2 (transportState A t N j))) =
      ∑ j : Fin r, ((j:ℂ)+b) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.cast_zero, Nat.zero_add,
      transportState_zero, show A.mode 2 (A.seed)=0 from A.seed_two, transportState_L2_one,
      map_zero, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show j.val+1+1=j.val+2 by omega, h2 j, map_smul]
    congr 2
    push_cast
    ring
  have hB : (∑ j : Fin (r+2), ((r:ℂ)+4-(j:ℂ)) •
      A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j)) =
      (∑ j : Fin r, ((r:ℂ)+4-(j:ℂ)) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j)) +
        (7*(r:ℂ)+4*h+3*a) • transportState A t N r := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one, sub_self,
      show (r:ℤ)+1-(r:ℤ)=1 by ring, h1,
      transportState_L0 A t N r, smul_smul]
    push_cast
    module
  have hC : (∑ j : Fin (r+2), (if j.val=r then c/2 else 0) • transportState A t N j) =
      (c/2) • transportState A t N r := by
    rw [Finset.sum_eq_single (⟨r,by omega⟩ : Fin (r+2))]
    · simp
    · intro j hj hjr
      have he : j.val ≠ r := fun he => hjr (Fin.ext he)
      simp [he]
    · simp
  simp only [transportSource, Nat.cast_add, Nat.cast_ofNat, map_sum, hcomm,
    Finset.sum_add_distrib]
  rw [hA,hB,hC]
  rw [← add_assoc, ← Finset.sum_add_distrib, Finset.smul_sum]
  have hs : (∑ j : Fin r, (((j:ℂ)+b) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j) +
      ((r:ℂ)+4-(j:ℂ)) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j))) =
      ∑ j : Fin r, ((r:ℂ)+4+b) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← add_smul]
    congr 1
    ring
  rw [hs]
  module





/-- L₂ lowers the intermediate states on the full generic singular curve.
The proof keeps both the charge and highest-weight terms in the telescope. -/
theorem transportState_L2 (t : ℂ) (N r : ℕ) (A : System V (vermaBSACharge t) (vermaBSAWeight N t)) (ht : t≠0) (hr : r+2<N) :
    A.mode 2
      (transportState A t N (r+2))=
      ((r:ℂ)+vermaBSAOffset2 N t) •
        transportState A t N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    have hs := transportSource_L2_step A t N r
      (vermaBSAOffset1 N t) (vermaBSAOffset2 N t)
      (transportState_L1 t N r A ht (by omega)) (fun j => ih j j.isLt (by omega))
    rw [transportState_eq_source A t N (r+2) (by omega),map_smul,hs]
    have hd' := bsa_denominator_ne_zero N (r+2) (by omega) hr
    by_cases hz : r=0
    · subst r
      simp only [transportSource,Fin.sum_univ_zero,smul_zero,zero_add,smul_smul,
        Nat.cast_zero,Nat.cast_ofNat]
      congr 1
      unfold vermaBSACharge vermaBSAWeight vermaBSAOffset1 vermaBSAOffset2
      norm_num at hd' ⊢
      field_simp [ht,hd']
      <;> ring
    · rw [transportState_eq_source A t N r (by omega)]
      simp only [smul_add,smul_smul,← add_smul]
      congr 1
      have hd := bsa_denominator_ne_zero N r (by omega) (by omega)
      unfold vermaBSACharge vermaBSAWeight vermaBSAOffset1 vermaBSAOffset2
      push_cast at hd' ⊢
      field_simp [ht,hd,hd',(mul_ne_zero_iff.mp hd).1,(mul_ne_zero_iff.mp hd).2,
        (mul_ne_zero_iff.mp hd').1,(mul_ne_zero_iff.mp hd').2]
      <;> ring

/-- L₂ kills the terminal source on the generic (1,N) curve for N at least
three. No claim about the separate level-two boundary is needed here. -/
theorem transportSource_L2_terminal (t : ℂ) (N : ℕ) (A : System V (vermaBSACharge t) (vermaBSAWeight N t)) (ht : t≠0) (hN : 3≤N) :
    A.mode 2
      (transportSource A t N N)=0 := by
  obtain ⟨r,hr⟩ : ∃ r : ℕ, N=r+2 := ⟨N-2,by omega⟩
  subst N
  rw [transportSource_L2_step A t (r+2) r (vermaBSAOffset1 (r+2) t)
      (vermaBSAOffset2 (r+2) t)
      (transportState_L1 t (r+2) r A ht (by omega))
      (fun j => transportState_L2 t (r+2) j A ht (by omega)),
    transportState_eq_source A t (r+2) r (by omega),smul_smul,← add_smul]
  have hd : (r:ℂ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have he : ((r:ℂ)+4+vermaBSAOffset2 (r+2) t)+
      (7*(r:ℂ)+4*vermaBSAWeight (r+2) t+3*vermaBSAOffset1 (r+2) t+vermaBSACharge t/2)*
      (-t/((r:ℂ)*(((r+2:ℕ):ℂ)-(r:ℂ))))=0 := by
    unfold vermaBSAOffset1 vermaBSAOffset2 vermaBSAWeight vermaBSACharge
    push_cast
    field_simp
    <;> ring
  rw [he,zero_smul]


end VOA.BSAWardTransport
