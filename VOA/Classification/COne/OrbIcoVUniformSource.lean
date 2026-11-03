import VOA.Classification.COne.OrbIcoVUniformProbe
import VOA.Examples.VirasoroVacuumFusionRecursion

/-! The universal C2 scalar rule of the actual BSA source in both
channels. All off-diagonal terms and field-weight shifts are retained. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA InverseDS.VirasoroVerma

theorem uniformProbe_source (c h : ℂ) (f : ℕ → Verma c h) (r : ℕ) :
    uniformProbe c h (wardSource c h f (r+2))=
      (2:ℂ)⁻¹*uniformProbe c h (f r) := by
  classical
  rw [wardSource,map_sum]
  have hh (j : Fin (r+2)) :
      uniformProbe c h (vermaMode c h ((j:ℤ)-((r+2:ℕ):ℤ)) (f j))=
      if (j:ℕ)=r then (2:ℂ)⁻¹*uniformProbe c h (f r) else 0 := by
    have he : (j:ℤ)-((r+2:ℕ):ℤ)=-((r+1-j.val:ℕ):ℤ)-1 := by omega
    rw [he,uniformProbe_creation]
    by_cases hj : (j:ℕ)=r
    · simp [hj]
    · rw [if_neg (by omega),if_neg hj,zero_mul]
  simp only [hh]
  exact Finset.sum_eq_single (⟨r,by omega⟩ : Fin (r+2))
    (by intro b hb hne; rw [if_neg (by intro he; apply hne; exact Fin.ext he)])
    (by simp) |>.trans (by simp)

/-- The first global negative descendant remains diagonal under the
survival test, with its actual field-weight shift retained. -/
theorem uniformProbe_A (c h b a : ℂ) (f : ℂ → wardSequenceSpace c h) (r : ℕ) :
    uniformProbe c h ((wardA c h b f a).val r)=
      (h-b-(a-1)+(r:ℂ))*uniformProbe c h ((f (a-1)).val r) := by
  change uniformProbe c h ((h-b-(a-1)+(r:ℂ)) • (f (a-1)).val r)=_
  simp [map_smul,smul_eq_mul]

theorem uniformProbe_source_all (c h : ℂ) (f : ℕ → Verma c h) (r : ℕ) :
    uniformProbe c h (wardSource c h f r)=
      if 2≤r then (2:ℂ)⁻¹*uniformProbe c h (f (r-2)) else 0 := by
  rcases r with _ | _ | r
  · simp [wardSource]
  · simp only [wardSource,Fin.sum_univ_one]
    have hh := uniformProbe_creation c h 0 (f 0)
    norm_num at hh ⊢
    exact hh
  · simpa using uniformProbe_source c h f r

/-- The second descendant's full scalar action, including its two initial
boundary coefficients. The field-weight shift is retained exactly. -/
theorem uniformProbe_B_all (c h b a : ℂ) (f : ℂ → wardSequenceSpace c h) (r : ℕ) :
    uniformProbe c h ((wardB c h b f a).val r)=
      (2*b+a-2-h-(r:ℂ))*uniformProbe c h ((f (a-2)).val r)+
      if 2≤r then (2:ℂ)⁻¹*uniformProbe c h ((f (a-2)).val (r-2)) else 0 := by
  change uniformProbe c h (wardSource c h (f (a-2)).val r+
    (2*b+(a-2)-h-(r:ℂ)) • (f (a-2)).val r)=_
  rw [map_add,map_smul,smul_eq_mul,uniformProbe_source_all]
  ring

set_option maxHeartbeats 1000000 in
/-- Every descendant of index at least three is diagonal under vacuum
survival. In the first commutator the two-level-earlier terms cancel;
subsequent commutators preserve diagonality. -/
theorem uniformProbe_negative_higher (c h b : ℂ) (n : ℕ)
    (f : ℂ → wardSequenceSpace c h) (a : ℂ) (r : ℕ) :
    uniformProbe c h ((wardNegative c h b (n+1) f a).val r)=
      (-1:ℂ)^(n+1)*(((n:ℂ)+3)*b+a-((n:ℂ)+3)-h-(r:ℂ))*
        uniformProbe c h ((f (a-((n:ℂ)+3))).val r) := by
  induction n generalizing f a with
  | zero =>
    have he : wardNegative c h b 1=wardA c h b*wardB c h b-wardB c h b*wardA c h b := by
      simp [wardNegative,DescendantTower.tower,LieRing.of_associative_ring_bracket]
    rw [he]
    simp only [LinearMap.sub_apply,Module.End.mul_apply,Pi.sub_apply,Submodule.coe_sub,
      map_sub,uniformProbe_A,uniformProbe_B_all]
    simp only [show a-1-2=a-3 by ring,show a-2-1=a-3 by ring]
    split_ifs with hr
    · have hc : ((r-2:ℕ):ℂ)=(r:ℂ)-2 := by exact_mod_cast Int.ofNat_sub hr
      simp only [hc,Nat.cast_zero,zero_add,pow_one]
      ring
    · norm_num
      ring
  | succ n ih =>
    have he : wardNegative c h b (n+1+1)=((n:ℂ)+1+1)⁻¹ •
        (wardA c h b*wardNegative c h b (n+1)-
          wardNegative c h b (n+1)*wardA c h b) := by
      simp only [wardNegative,DescendantTower.tower,Nat.cast_add,Nat.cast_one,
        LieRing.of_associative_ring_bracket]
    rw [he]
    simp only [LinearMap.smul_apply,LinearMap.sub_apply,Module.End.mul_apply,
      Pi.smul_apply,Pi.sub_apply,Submodule.coe_smul,Submodule.coe_sub]
    rw [map_smul,map_sub,smul_eq_mul,uniformProbe_A,
      ih f (a-1),ih ((wardA c h b) f) a,uniformProbe_A]
    have hi : a-1-((n:ℂ)+3)=a-((n:ℂ)+3)-1 := by ring
    have hj : a-((n:ℂ)+3)-1=a-(((n:ℂ)+1)+3) := by ring
    simp only [hi,hj,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp [show (n:ℂ)+1+1≠0 by exact_mod_cast (by omega : n+1+1≠0)]
    <;> ring

/-- The vacuum scalar rule for a negative descendant: its ordinary diagonal,
plus one half the input two levels earlier only when the index is two. -/
noncomputable def wardUniformStep (h b a : ℂ) (k r : ℕ) (u : ℕ → ℂ) : ℂ :=
  wardCreationDiagonal h b a r k*u r+
    if k=2 ∧ 2≤r then (2:ℂ)⁻¹*u (r-2) else 0

/-- The scalar rule is the actual vacuum survival functional applied to
every negative transport mode, for arbitrary input sequences. -/
theorem uniformProbe_transport (c h b : ℂ) (k : ℕ) (hk : 0<k)
    (f : ℂ → wardSequenceSpace c h) (a : ℂ) (r : ℕ) :
    uniformProbe c h ((wardTransportMode c h b (-(k:ℤ)) f a).val r)=
      wardUniformStep h b a k r (fun j => uniformProbe c h ((f (a-(k:ℂ))).val j)) := by
  rcases k with _ | _ | _ | n
  · omega
  · change uniformProbe c h ((wardA c h b f a).val r)=_
    rw [uniformProbe_A]
    simp only [wardUniformStep,wardCreationDiagonal,Nat.cast_add,Nat.cast_zero,
      Nat.cast_one,zero_add,pow_one,if_neg (by omega : ¬(0+1=2 ∧ 2≤r)),add_zero]
    ring
  · change uniformProbe c h ((wardB c h b f a).val r)=_
    rw [uniformProbe_B_all]
    simp [wardUniformStep,wardCreationDiagonal]
  · have hi : -((n+1+1+1:ℕ):ℤ)=Int.negSucc (n+2) := by omega
    rw [hi]
    change uniformProbe c h ((wardNegative c h b (n+1) f a).val r)=_
    rw [uniformProbe_negative_higher]
    simp only [wardUniformStep,wardCreationDiagonal,
      if_neg (by omega : ¬(n+1+1+1=2 ∧ 2≤r)),add_zero]
    have hc : ((n+1+1+1:ℕ):ℂ)=(n:ℂ)+3 := by push_cast; ring
    rw [hc]
    simp only [pow_succ]
    ring

/-- The intermediate scalar vacuum recursion at arbitrary seed index.
Stage n has input field weight a+n; all earlier coefficient contributions
are retained by wardUniformStep. -/
noncomputable def wardBSAUniform (h b t a : ℂ) (N : ℕ) (u : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0,r => u r
  | n+1,r => (-t/(((n:ℂ)+1)*((N:ℂ)-((n:ℂ)+1)))) *
      ∑ j : Fin (n+1), wardUniformStep h b (a+((n+1:ℕ):ℂ)) (n+1-j) r
        (wardBSAUniform h b t a N u j)
termination_by n => n

/-- The terminal scalar source is an undivided finite sum, so it remains
meaningful at the singular index where the next recursion denominator is zero. -/
noncomputable def wardBSAUniformSource (h b t a : ℂ) (N n : ℕ) (u : ℕ → ℂ) (r : ℕ) : ℂ :=
  ∑ j : Fin n, wardUniformStep h b (a+(n:ℂ)) (n-j) r (wardBSAUniform h b t a N u j)

/-- Every intermediate scalar equals the actual vacuum survival value of
the corresponding BSA operator. This proves the full recursion rather
than merely its first potentially nonzero diagonal. -/
theorem wardBSAOperator_uniform (c h b t a : ℂ) (N n : ℕ)
    (f : ℂ → wardSequenceSpace c h) (r : ℕ) :
    uniformProbe c h ((wardBSAOperator c h b t N n f (a+(n:ℂ))).val r)=
      wardBSAUniform h b t a N (fun j => uniformProbe c h ((f a).val j)) n r := by
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    cases n with
    | zero => simp [wardBSAOperator,wardBSAUniform]
    | succ n =>
      simp only [wardBSAOperator,wardBSAUniform,LinearMap.smul_apply,LinearMap.sum_apply,
        Module.End.mul_apply,Pi.smul_apply,Submodule.coe_smul,Submodule.coe_sum,
        Finset.sum_apply,map_smul,map_sum,smul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hi : (j:ℤ)-((n:ℤ)+1)=-((n+1-j:ℕ):ℤ) := by omega
      rw [hi,uniformProbe_transport c h b (n+1-j) (by omega)]
      have he : a+((n+1:ℕ):ℂ)-((n+1-j:ℕ):ℂ)=a+(j:ℂ) := by
        have hj' : ((n+1-j:ℕ):ℂ)+(j:ℂ)=((n+1:ℕ):ℂ) := by
          exact_mod_cast (Nat.sub_add_cancel (by omega : j.val≤n+1))
        linear_combination -hj'
      simp only [he,ih j (by omega)]

/-- The undivided scalar source equals the actual source under vacuum
projection at every coefficient and every seed index. -/
theorem wardBSASourceOperator_uniform (c h b t a : ℂ) (N n : ℕ)
    (f : ℂ → wardSequenceSpace c h) (r : ℕ) :
    uniformProbe c h ((wardBSASourceOperator c h b t N n f (a+(n:ℂ))).val r)=
      wardBSAUniformSource h b t a N n (fun j => uniformProbe c h ((f a).val j)) r := by
  simp only [wardBSASourceOperator,wardBSAUniformSource,LinearMap.sum_apply,
    Module.End.mul_apply,Submodule.coe_sum,Finset.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hi : (j:ℤ)-(n:ℤ)=-((n-j:ℕ):ℤ) := by omega
  rw [hi,uniformProbe_transport c h b (n-j) (by omega)]
  have he : a+(n:ℂ)-((n-j:ℕ):ℂ)=a+(j:ℂ) := by
    have hj' : ((n-j:ℕ):ℂ)+(j:ℂ)=(n:ℂ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : j.val≤n))
    linear_combination -hj'
  simp only [he,wardBSAOperator_uniform]

/-- A source acting on an actual level sequence has precisely the finite
vacuum scalar recursion. The identity includes its terminal coefficient;
nonvanishing of that scalar is still a separate obligation. -/
theorem wardSourceAt_uniform (c h b t a : ℂ) (N : ℕ)
    (f : wardSequenceSpace c h) (r : ℕ) :
    uniformProbe c h ((wardSourceAt c h b t a N f).val r)=
      wardBSAUniformSource h b t a N N (fun j => uniformProbe c h (f.val j)) r := by
  have hh := wardBSASourceOperator_uniform c h b t a N N (wardFieldLift c h a f) r
  simpa [wardSourceAt,wardFieldLift] using hh


end VOA.Classification.COne.OrbIcoV
