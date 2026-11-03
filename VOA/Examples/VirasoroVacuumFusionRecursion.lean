/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVacuumFusionSource

/-!
# The full scalar vacuum projection of every fusion source

The vacuum survival functional sees only L minus two among negative modes.
Consequently only the second descendant has a lower-coefficient term;
every descendant of index at least three is diagonal. Iterating these
actual operator identities gives the full finite source recursion for
arbitrary seed index, with no assumption that its terminal scalar is nonzero.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- At levels zero and one the negative-mode sum has no L-minus-two term.
At every later level its survival value is one half the input two levels earlier. -/
theorem vermaVacuumSurvival_source_all (c : ℂ) (f : ℕ → Verma c 0) (r : ℕ) :
    vermaVacuumSurvival c (wardSource c 0 f r)=
      if 2≤r then (2:ℂ)⁻¹*vermaVacuumSurvival c (f (r-2)) else 0 := by
  rcases r with _ | _ | r
  · simp [wardSource]
  · simp only [wardSource,Fin.sum_univ_one]
    have hh := vermaVacuumSurvival_mode c 0 (f 0)
    norm_num at hh ⊢
    exact hh
  · simpa using vermaVacuumSurvival_source c f r

/-- The second descendant's full scalar action, including its two initial
boundary coefficients. The field-weight shift is retained exactly. -/
theorem vermaVacuumSurvival_B_all (c b a : ℂ) (f : ℂ → wardSequenceSpace c 0) (r : ℕ) :
    vermaVacuumSurvival c ((wardB c 0 b f a).val r)=
      (2*b+a-2-(r:ℂ))*vermaVacuumSurvival c ((f (a-2)).val r)+
      if 2≤r then (2:ℂ)⁻¹*vermaVacuumSurvival c ((f (a-2)).val (r-2)) else 0 := by
  change vermaVacuumSurvival c (wardSource c 0 (f (a-2)).val r+
    (2*b+(a-2)-0-(r:ℂ)) • (f (a-2)).val r)=_
  rw [map_add,map_smul,smul_eq_mul,vermaVacuumSurvival_source_all]
  ring

set_option maxHeartbeats 1000000 in
/-- Every descendant of index at least three is diagonal under vacuum
survival. In the first commutator the two-level-earlier terms cancel;
subsequent commutators preserve diagonality. -/
theorem vermaVacuumSurvival_negative_higher (c b : ℂ) (n : ℕ)
    (f : ℂ → wardSequenceSpace c 0) (a : ℂ) (r : ℕ) :
    vermaVacuumSurvival c ((wardNegative c 0 b (n+1) f a).val r)=
      (-1:ℂ)^(n+1)*(((n:ℂ)+3)*b+a-((n:ℂ)+3)-(r:ℂ))*
        vermaVacuumSurvival c ((f (a-((n:ℂ)+3))).val r) := by
  induction n generalizing f a with
  | zero =>
    have he : wardNegative c 0 b 1=wardA c 0 b*wardB c 0 b-wardB c 0 b*wardA c 0 b := by
      simp [wardNegative,DescendantTower.tower,LieRing.of_associative_ring_bracket]
    rw [he]
    simp only [LinearMap.sub_apply,Module.End.mul_apply,Pi.sub_apply,Submodule.coe_sub,
      map_sub,vermaVacuumSurvival_A,vermaVacuumSurvival_B_all]
    simp only [show a-1-2=a-3 by ring,show a-2-1=a-3 by ring]
    split_ifs with hr
    · have hc : ((r-2:ℕ):ℂ)=(r:ℂ)-2 := by exact_mod_cast Int.ofNat_sub hr
      simp only [hc,Nat.cast_zero,zero_add,pow_one]
      ring
    · norm_num
      ring
  | succ n ih =>
    have he : wardNegative c 0 b (n+1+1)=((n:ℂ)+1+1)⁻¹ •
        (wardA c 0 b*wardNegative c 0 b (n+1)-
          wardNegative c 0 b (n+1)*wardA c 0 b) := by
      simp only [wardNegative,DescendantTower.tower,Nat.cast_add,Nat.cast_one,
        LieRing.of_associative_ring_bracket]
    rw [he]
    simp only [LinearMap.smul_apply,LinearMap.sub_apply,Module.End.mul_apply,
      Pi.smul_apply,Pi.sub_apply,Submodule.coe_smul,Submodule.coe_sub]
    rw [map_smul,map_sub,smul_eq_mul,vermaVacuumSurvival_A,
      ih f (a-1),ih ((wardA c 0 b) f) a,vermaVacuumSurvival_A]
    have hi : a-1-((n:ℂ)+3)=a-((n:ℂ)+3)-1 := by ring
    have hj : a-((n:ℂ)+3)-1=a-(((n:ℂ)+1)+3) := by ring
    simp only [hi,hj,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp [show (n:ℂ)+1+1≠0 by exact_mod_cast (by omega : n+1+1≠0)]
    <;> ring

/-- The vacuum scalar rule for a negative descendant: its ordinary diagonal,
plus one half the input two levels earlier only when the index is two. -/
noncomputable def wardVacuumStep (b a : ℂ) (k r : ℕ) (u : ℕ → ℂ) : ℂ :=
  wardCreationDiagonal 0 b a r k*u r+
    if k=2 ∧ 2≤r then (2:ℂ)⁻¹*u (r-2) else 0

/-- The scalar rule is the actual vacuum survival functional applied to
every negative transport mode, for arbitrary input sequences. -/
theorem vermaVacuumSurvival_transport (c b : ℂ) (k : ℕ) (hk : 0<k)
    (f : ℂ → wardSequenceSpace c 0) (a : ℂ) (r : ℕ) :
    vermaVacuumSurvival c ((wardTransportMode c 0 b (-(k:ℤ)) f a).val r)=
      wardVacuumStep b a k r (fun j => vermaVacuumSurvival c ((f (a-(k:ℂ))).val j)) := by
  rcases k with _ | _ | _ | n
  · omega
  · change vermaVacuumSurvival c ((wardA c 0 b f a).val r)=_
    rw [vermaVacuumSurvival_A]
    simp only [wardVacuumStep,wardCreationDiagonal,Nat.cast_add,Nat.cast_zero,
      Nat.cast_one,zero_add,pow_one,if_neg (by omega : ¬(0+1=2 ∧ 2≤r)),add_zero]
    ring
  · change vermaVacuumSurvival c ((wardB c 0 b f a).val r)=_
    rw [vermaVacuumSurvival_B_all]
    simp [wardVacuumStep,wardCreationDiagonal]
  · have hi : -((n+1+1+1:ℕ):ℤ)=Int.negSucc (n+2) := by omega
    rw [hi]
    change vermaVacuumSurvival c ((wardNegative c 0 b (n+1) f a).val r)=_
    rw [vermaVacuumSurvival_negative_higher]
    simp only [wardVacuumStep,wardCreationDiagonal,
      if_neg (by omega : ¬(n+1+1+1=2 ∧ 2≤r)),add_zero]
    have hc : ((n+1+1+1:ℕ):ℂ)=(n:ℂ)+3 := by push_cast; ring
    rw [hc]
    simp only [pow_succ]
    ring

/-- The intermediate scalar vacuum recursion at arbitrary seed index.
Stage n has input field weight a+n; all earlier coefficient contributions
are retained by wardVacuumStep. -/
noncomputable def wardBSAVacuum (b t a : ℂ) (N : ℕ) (u : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0,r => u r
  | n+1,r => (-t/(((n:ℂ)+1)*((N:ℂ)-((n:ℂ)+1)))) *
      ∑ j : Fin (n+1), wardVacuumStep b (a+((n+1:ℕ):ℂ)) (n+1-j) r
        (wardBSAVacuum b t a N u j)
termination_by n => n

/-- The terminal scalar source is an undivided finite sum, so it remains
meaningful at the singular index where the next recursion denominator is zero. -/
noncomputable def wardBSAVacuumSource (b t a : ℂ) (N n : ℕ) (u : ℕ → ℂ) (r : ℕ) : ℂ :=
  ∑ j : Fin n, wardVacuumStep b (a+(n:ℂ)) (n-j) r (wardBSAVacuum b t a N u j)

/-- Every intermediate scalar equals the actual vacuum survival value of
the corresponding BSA operator. This proves the full recursion rather
than merely its first potentially nonzero diagonal. -/
theorem wardBSAOperator_vacuum (c b t a : ℂ) (N n : ℕ)
    (f : ℂ → wardSequenceSpace c 0) (r : ℕ) :
    vermaVacuumSurvival c ((wardBSAOperator c 0 b t N n f (a+(n:ℂ))).val r)=
      wardBSAVacuum b t a N (fun j => vermaVacuumSurvival c ((f a).val j)) n r := by
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    cases n with
    | zero => simp [wardBSAOperator,wardBSAVacuum]
    | succ n =>
      simp only [wardBSAOperator,wardBSAVacuum,LinearMap.smul_apply,LinearMap.sum_apply,
        Module.End.mul_apply,Pi.smul_apply,Submodule.coe_smul,Submodule.coe_sum,
        Finset.sum_apply,map_smul,map_sum,smul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hi : (j:ℤ)-((n:ℤ)+1)=-((n+1-j:ℕ):ℤ) := by omega
      rw [hi,vermaVacuumSurvival_transport c b (n+1-j) (by omega)]
      have he : a+((n+1:ℕ):ℂ)-((n+1-j:ℕ):ℂ)=a+(j:ℂ) := by
        have hj' : ((n+1-j:ℕ):ℂ)+(j:ℂ)=((n+1:ℕ):ℂ) := by
          exact_mod_cast (Nat.sub_add_cancel (by omega : j.val≤n+1))
        linear_combination -hj'
      simp only [he,ih j (by omega)]

/-- The undivided scalar source equals the actual source under vacuum
projection at every coefficient and every seed index. -/
theorem wardBSASourceOperator_vacuum (c b t a : ℂ) (N n : ℕ)
    (f : ℂ → wardSequenceSpace c 0) (r : ℕ) :
    vermaVacuumSurvival c ((wardBSASourceOperator c 0 b t N n f (a+(n:ℂ))).val r)=
      wardBSAVacuumSource b t a N n (fun j => vermaVacuumSurvival c ((f a).val j)) r := by
  simp only [wardBSASourceOperator,wardBSAVacuumSource,LinearMap.sum_apply,
    Module.End.mul_apply,Submodule.coe_sum,Finset.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hi : (j:ℤ)-(n:ℤ)=-((n-j:ℕ):ℤ) := by omega
  rw [hi,vermaVacuumSurvival_transport c b (n-j) (by omega)]
  have he : a+(n:ℂ)-((n-j:ℕ):ℂ)=a+(j:ℂ) := by
    have hj' : ((n-j:ℕ):ℂ)+(j:ℂ)=(n:ℂ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : j.val≤n))
    linear_combination -hj'
  simp only [he,wardBSAOperator_vacuum]

/-- A source acting on an actual level sequence has precisely the finite
vacuum scalar recursion. The identity includes its terminal coefficient;
nonvanishing of that scalar is still a separate obligation. -/
theorem wardSourceAt_vacuum (c b t a : ℂ) (N : ℕ)
    (f : wardSequenceSpace c 0) (r : ℕ) :
    vermaVacuumSurvival c ((wardSourceAt c 0 b t a N f).val r)=
      wardBSAVacuumSource b t a N N (fun j => vermaVacuumSurvival c (f.val j)) r := by
  have hh := wardBSASourceOperator_vacuum c b t a N N (wardFieldLift c 0 a f) r
  simpa [wardSourceAt,wardFieldLift] using hh

end VOA.InverseDS.VirasoroVerma
