/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSAOperator

/-!
# BSA transport retaining the first positive defect

The seed need only have the stated weight. Its first positive image is
transported explicitly, allowing later application to constructed sequences.
-/
namespace VOA.BSAWardDefect
open VOA.InverseDS.VirasoroVerma VOA.VirModule
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The commutators and weight equation, with NO positive seed equations.
Positive defects are retained explicitly rather than assumed to vanish. -/
structure System (V : Type*) [AddCommGroup V] [Module ℂ V] (c h : ℂ) where
  /-- Integer-indexed operators; only indices at most two enter the proof. -/
  mode : ℤ → Module.End ℂ V
  /-- The initial vector, allowed to be zero in this Ward-identity theorem. -/
  seed : V
  /-- The initial vector has weight h. -/
  seed_zero : mode 0 seed = h • seed
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


/-- The same finite negative-word expression, before choosing an input. -/
noncomputable def op {c h : ℂ} (A : System V c h) (t : ℂ) (N : ℕ) :
    ℕ → Module.End ℂ V
  | 0 => LinearMap.id
  | r+1 => (-t / (((r:ℂ)+1)*((N:ℂ)-((r:ℂ)+1)))) •
      ∑ j : Fin (r+1), A.mode ((j:ℤ)-((r:ℤ)+1)) * op A t N j
termination_by r => r

/-- The undivided source operator can act on the seed's positive defect. -/
noncomputable def sourceOp {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ) :
    Module.End ℂ V := ∑ j : Fin r, A.mode ((j:ℤ)-(r:ℤ)) * op A t N j

/-- Evaluating the operator at the seed recovers the state recursion. -/
theorem op_seed {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ) :
    op A t N r A.seed=transportState A t N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [op,transportState]
    | succ r =>
      simp only [op,transportState,LinearMap.smul_apply,LinearMap.sum_apply,Module.End.mul_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (by omega)]

/-- The positive-level operator is the scalar multiple of its source. -/
theorem op_eq_source {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ) (hr : 0<r) :
    op A t N r=(-t/((r:ℂ)*((N:ℂ)-(r:ℂ)))) • sourceOp A t N r := by
  cases r with
  | zero => omega
  | succ r => simp only [op,sourceOp,Nat.cast_add,Nat.cast_one]

/-- The first Ward telescoping identity with the entire seed defect retained. -/
theorem source_L1_step {c h : ℂ} (A : System V c h) (t : ℂ) (N r : ℕ) (a : ℂ)
    (hrec : ∀ j : Fin r, A.mode 1 (transportState A t N (j+1)) =
      op A t N (j+1) (A.mode 1 A.seed)+((j:ℂ)+a) • transportState A t N j) :
    A.mode 1 (transportSource A t N (r+1)) =
      sourceOp A t N (r+1) (A.mode 1 A.seed)+
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
      sourceOp A t N (r+1) (A.mode 1 A.seed)+
      ∑ j : Fin r, ((j:ℂ)+a) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j) := by
    simp only [sourceOp,LinearMap.sum_apply,Module.End.mul_apply,Nat.cast_add,Nat.cast_one]
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.cast_zero,transportState_zero,op,LinearMap.id_apply]
    rw [add_assoc]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Fin.val_succ]
    rw [hrec j,map_add,map_smul]
    congr 2
    simp
  have hB : (∑ j : Fin (r+1), ((r:ℂ)+2-(j:ℂ)) •
      A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j)) =
      (∑ j : Fin r, ((r:ℂ)+2-(j:ℂ)) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j)) +
        (2*(h+(r:ℂ))) • transportState A t N r := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,sub_self,transportState_L0 A t N r,smul_smul]
    congr 1
    congr 1
    push_cast
    ring
  simp only [transportSource,Nat.cast_add,Nat.cast_one,map_sum,hcomm,Finset.sum_add_distrib]
  rw [hA,hB]
  simp only [transportSource,Finset.smul_sum]
  have he : (∑ j : Fin r, ((j:ℂ)+a) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j))+
      (∑ j : Fin r, ((r:ℂ)+2-(j:ℂ)) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j)) =
      ∑ j : Fin r, ((r:ℂ)+2+a) • A.mode ((j:ℤ)-(r:ℤ)) (transportState A t N j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← add_smul]
    congr 1
    ring
  rw [← add_assoc,add_assoc (sourceOp A t N (r+1) (A.mode 1 A.seed)),he]
/-- The first intermediate state without any positive seed condition. -/
theorem state_one {c h : ℂ} (A : System V c h) (t : ℂ) (N : ℕ) :
    transportState A t N 1=(-t/((N:ℂ)-1)) • A.mode (-1) A.seed := by
  rw [transportState]
  simp

/-- The corresponding first intermediate operator. -/
theorem op_one {c h : ℂ} (A : System V c h) (t : ℂ) (N : ℕ) :
    op A t N 1=(-t/((N:ℂ)-1)) • A.mode (-1) := by
  rw [op]
  simp [op,show (LinearMap.id : Module.End ℂ V)=1 from rfl]

/-- At every intermediate index, the first positive defect is transported
by the same operator, plus the usual affine lowering coefficient. -/
theorem state_L1 (t : ℂ) (N r : ℕ) {c : ℂ} (A : System V c (vermaBSAWeight N t))
    (ht : t≠0) (hr : r+1<N) :
    A.mode 1 (transportState A t N (r+1))=
      op A t N (r+1) (A.mode 1 A.seed)+
      ((r:ℂ)+vermaBSAOffset1 N t) • transportState A t N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hz : r=0
    · subst r
      rw [state_one,op_one,map_smul,A.comm 1 (-1) A.seed]
      norm_num [A.seed_zero,transportState_zero]
      simp only [smul_add,smul_smul]
      congr 1
      have hn : (N:ℂ)-1≠0 := by exact_mod_cast (show (N:ℤ)-1≠0 by omega)
      congr 1
      unfold vermaBSAWeight vermaBSAOffset1
      field_simp
      <;> ring
    · have hs := source_L1_step A t N r
        (vermaBSAOffset1 N t) (fun j => ih j (by omega) (by omega))
      rw [transportState_eq_source A t N (r+1) (by omega),map_smul,hs,
        op_eq_source A t N (r+1) (by omega)]
      rw [transportState_eq_source A t N r (by omega)]
      simp only [LinearMap.smul_apply,smul_add,smul_smul,add_assoc,← add_smul]
      congr 1
      congr 1
      have hd := bsa_denominator_ne_zero N r (by omega) (by omega)
      have hd' := bsa_denominator_ne_zero N (r+1) (by omega) hr
      unfold vermaBSAWeight vermaBSAOffset1
      push_cast at hd' ⊢
      field_simp [ht,hd,hd',(mul_ne_zero_iff.mp hd).1,(mul_ne_zero_iff.mp hd).2,
        (mul_ne_zero_iff.mp hd').1,(mul_ne_zero_iff.mp hd').2]
      <;> ring

/-- At resonance the terminal source transports the first positive defect
exactly. No primary-seed equation is assumed. -/
theorem source_L1_terminal (t : ℂ) (N : ℕ) {c : ℂ}
    (A : System V c (vermaBSAWeight N t)) (ht : t≠0) (hN : 2≤N) :
    A.mode 1 (transportSource A t N N)=sourceOp A t N N (A.mode 1 A.seed) := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  subst N
  rw [source_L1_step A t _ r (vermaBSAOffset1 (r+1) t)
      (fun j => state_L1 t (r+1) j A ht (by omega)),
    transportState_eq_source A t _ r (by omega),smul_smul,add_assoc,← add_smul]
  have hd : (r:ℂ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have he : ((r:ℂ)+2+vermaBSAOffset1 (r+1) t)+
      (2*(vermaBSAWeight (r+1) t+(r:ℂ)))*(-t/((r:ℂ)*(((r+1:ℕ):ℂ)-(r:ℂ))))=0 := by
    unfold vermaBSAOffset1 vermaBSAWeight
    push_cast
    field_simp
    <;> ring
  rw [he,zero_smul,add_zero]
end VOA.BSAWardDefect


namespace VOA.InverseDS.VirasoroVerma

/-- The actual descendant system with only the field-weight equation.
The first and second positive defects are unrestricted. -/
noncomputable def wardDefectSystem (c h b a : ℂ) (f : ℂ → wardSequenceSpace c h)
    (h0 : wardWeight c h f=a • f) :
    BSAWardDefect.System (ℂ → wardSequenceSpace c h) c a where
  mode := wardTransportMode c h b
  seed := f
  seed_zero := h0
  comm_law m n hm hm2 hn v := by
    have hh := congrArg (fun T : Module.End ℂ (ℂ → wardSequenceSpace c h) => T v)
      (wardTransportMode_comm c h b m n hm hm2 hn)
    change wardTransportMode c h b m (wardTransportMode c h b n v)-
      wardTransportMode c h b n (wardTransportMode c h b m v)=_ at hh
    simpa only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,add_assoc] using
      (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

/-- The unrestricted defect transport uses the existing actual BSA operator. -/
theorem wardDefectSystem_op (c h b a t : ℂ) (N r : ℕ)
    (f : ℂ → wardSequenceSpace c h) (h0 : wardWeight c h f=a • f) :
    BSAWardDefect.op (wardDefectSystem c h b a f h0) t N r=wardBSAOperator c h b t N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [BSAWardDefect.op,wardBSAOperator]
    | succ r =>
      simp only [BSAWardDefect.op,wardBSAOperator]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (by omega)]
      rfl

/-- The unrestricted source likewise agrees with the actual source operator. -/
theorem wardDefectSystem_sourceOp (c h b a t : ℂ) (N r : ℕ)
    (f : ℂ → wardSequenceSpace c h) (h0 : wardWeight c h f=a • f) :
    BSAWardDefect.sourceOp (wardDefectSystem c h b a f h0) t N r=
      wardBSASourceOperator c h b t N r := by
  simp only [BSAWardDefect.sourceOp,wardBSASourceOperator,wardDefectSystem_op]
  rfl

/-- Evaluating the unrestricted source at its seed gives the actual output. -/
theorem wardDefectSystem_source (c h b a t : ℂ) (N r : ℕ)
    (f : ℂ → wardSequenceSpace c h) (h0 : wardWeight c h f=a • f) :
    BSAWardDefect.transportSource (wardDefectSystem c h b a f h0) t N r=
      wardBSASourceOperator c h b t N r f := by
  rw [← wardDefectSystem_sourceOp c h b a t N r f h0]
  simp only [BSAWardDefect.sourceOp,BSAWardDefect.transportSource,
    LinearMap.sum_apply,Module.End.mul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← BSAWardDefect.op_seed]
  rfl

/-- The actual BSA source intertwines the first positive defect at the
(1,N) field weight, without assuming any primary-seed equation. -/
theorem wardBSASourceOperator_L1_defect (c h b t : ℂ) (N : ℕ)
    (ht : t≠0) (hN : 2≤N) (f : ℂ → wardSequenceSpace c h)
    (h0 : wardWeight c h f=vermaBSAWeight N t • f) :
    wardP c h b (wardBSASourceOperator c h b t N N f)=
      wardBSASourceOperator c h b t N N (wardP c h b f) := by
  have hh := BSAWardDefect.source_L1_terminal t N
    (wardDefectSystem c h b (vermaBSAWeight N t) f h0) ht hN
  rw [wardDefectSystem_source,wardDefectSystem_sourceOp] at hh
  exact hh
end VOA.InverseDS.VirasoroVerma
