/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroTopCoordinate
import VOA.Examples.VirasoroFusionKernel

/-!
# The full scalar projection of the actual fusion source

The all-L-minus-one PBW coordinate sees only two adjacent coefficients
under each negative descendant. Iterating that rule gives a finite scalar
recursion for the whole actual BSA operator, including all its off-diagonal
terms. This is stronger than its already known first-surviving-coefficient
diagonal. No primary equation is assumed. Nonvanishing of the terminal
scalar remains a separate mathematical obligation.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- The scalar action of a negative descendant on top PBW coordinates.
The diagonal uses the current coefficient. Only indices at least two
also use the previous coefficient, with the alternating sign. -/
noncomputable def wardTopStep (h b a : ℂ) (k r : ℕ) (u : ℕ → ℂ) : ℂ :=
  wardCreationDiagonal h b a r k * u r +
    if 2≤k ∧ 0<r then (-1:ℂ)^k * u (r-1) else 0

/-- A negative transport mode has exactly the two-coefficient scalar
projection, at every coefficient including zero and at every negative index. -/
theorem vermaTopCoordinate_transport (c h b : ℂ) (k : ℕ) (hk : 0<k)
    (f : ℂ → wardSequenceSpace c h) (a : ℂ) (r : ℕ) :
    vermaTopCoordinate c h r ((wardTransportMode c h b (-(k:ℤ)) f a).val r)=
      wardTopStep h b a k r
        (fun j => vermaTopCoordinate c h j ((f (a-(k:ℂ))).val j)) := by
  cases r with
  | zero =>
    rw [wardTransportMode_diagonal c h b k hk f 0 (by intro a j hj; omega),
      map_smul,smul_eq_mul]
    simp [wardTopStep]
  | succ r =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero =>
        change vermaTopCoordinate c h (r+1) ((wardA c h b f a).val (r+1))=_
        rw [vermaTopCoordinate_wardA]
        simp only [wardTopStep]
        rw [if_neg (by omega : ¬(2≤0+1 ∧ 0<r+1))]
        norm_num only [wardCreationDiagonal, Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, pow_one, add_zero]
        ring
      | succ k =>
        have hi : -((k+1+1:ℕ):ℤ)=Int.negSucc (k+1) := by omega
        rw [hi]
        change vermaTopCoordinate c h (r+1) ((wardNegative c h b k f a).val (r+1))=_
        rw [vermaTopCoordinate_wardNegative]
        simp only [wardTopStep]
        rw [if_pos (by omega : 2≤k+1+1 ∧ 0<r+1)]
        simp only [wardCreationDiagonal,Nat.add_sub_cancel,
          Nat.cast_add,Nat.cast_one,pow_succ]
        have he : a-((k:ℂ)+2)=a-((k:ℂ)+1+1) := by ring
        rw [he]
        ring

/-- The intermediate top-coordinate recursion at a fixed input field weight.
The parameter a is the input weight, so stage n is evaluated at a+n.
Its input u is an arbitrary scalar coefficient sequence. -/
noncomputable def wardBSATop (h b t a : ℂ) (N : ℕ) (u : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, r => u r
  | n+1, r => (-t/(((n:ℂ)+1)*((N:ℂ)-((n:ℂ)+1)))) *
      ∑ j : Fin (n+1), wardTopStep h b (a+((n+1:ℕ):ℂ)) (n+1-j) r
        (wardBSATop h b t a N u j)
termination_by n => n

/-- The undivided top-coordinate source; at n=N this avoids the terminal
zero denominator exactly as the actual source operator does. -/
noncomputable def wardBSATopSource (h b t a : ℂ) (N n : ℕ) (u : ℕ → ℂ) (r : ℕ) : ℂ :=
  ∑ j : Fin n, wardTopStep h b (a+(n:ℂ)) (n-j) r (wardBSATop h b t a N u j)

/-- Every intermediate scalar coefficient is the actual top PBW coordinate
of the BSA operator. This includes all lower-coefficient contributions,
without a primary-seed or first-surviving-coefficient assumption. -/
theorem wardBSAOperator_top (c h b t a : ℂ) (N n : ℕ)
    (f : ℂ → wardSequenceSpace c h) (r : ℕ) :
    vermaTopCoordinate c h r ((wardBSAOperator c h b t N n f (a+(n:ℂ))).val r)=
      wardBSATop h b t a N (fun j => vermaTopCoordinate c h j ((f a).val j)) n r := by
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    cases n with
    | zero => simp [wardBSAOperator,wardBSATop]
    | succ n =>
      simp only [wardBSAOperator,wardBSATop,LinearMap.smul_apply,LinearMap.sum_apply,
        Module.End.mul_apply,Pi.smul_apply,Submodule.coe_smul,Submodule.coe_sum,
        Finset.sum_apply,map_smul,map_sum,smul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hi : (j:ℤ)-((n:ℤ)+1)=-((n+1-j:ℕ):ℤ) := by omega
      rw [hi,vermaTopCoordinate_transport c h b (n+1-j) (by omega)]
      have he : a+((n+1:ℕ):ℂ)-((n+1-j:ℕ):ℂ)=a+(j:ℂ) := by
        have hj' : ((n+1-j:ℕ):ℂ)+(j:ℂ)=((n+1:ℕ):ℂ) := by
          exact_mod_cast (Nat.sub_add_cancel (by omega : j.val≤n+1))
        linear_combination -hj'
      simp only [he,ih j (by omega)]

/-- The entire undivided actual source is identified with its finite scalar
projection, including the terminal coefficient at resonance. -/
theorem wardBSASourceOperator_top (c h b t a : ℂ) (N n : ℕ)
    (f : ℂ → wardSequenceSpace c h) (r : ℕ) :
    vermaTopCoordinate c h r ((wardBSASourceOperator c h b t N n f (a+(n:ℂ))).val r)=
      wardBSATopSource h b t a N n (fun j => vermaTopCoordinate c h j ((f a).val j)) r := by
  simp only [wardBSASourceOperator,wardBSATopSource,LinearMap.sum_apply,
    Module.End.mul_apply,Submodule.coe_sum,Finset.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hi : (j:ℤ)-(n:ℤ)=-((n-j:ℕ):ℤ) := by omega
  rw [hi,vermaTopCoordinate_transport c h b (n-j) (by omega)]
  have he : a+(n:ℂ)-((n-j:ℕ):ℂ)=a+(j:ℂ) := by
    have hj' : ((n-j:ℕ):ℂ)+(j:ℂ)=(n:ℂ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : j.val≤n))
    linear_combination -hj'
  simp only [he,wardBSAOperator_top]

/-- After the single-weight field lift, the source scalar depends only on
the actual top coordinates of the original level sequence. -/
theorem wardSourceAt_top (c h b t a : ℂ) (N : ℕ)
    (f : wardSequenceSpace c h) (r : ℕ) :
    vermaTopCoordinate c h r ((wardSourceAt c h b t a N f).val r)=
      wardBSATopSource h b t a N N (fun j => vermaTopCoordinate c h j (f.val j)) r := by
  have hh := wardBSASourceOperator_top c h b t a N N (wardFieldLift c h a f) r
  simpa [wardSourceAt,wardFieldLift] using hh

/-- At seed index three, the complete projected source has just one
subdiagonal. Its coefficient is explicit; no lower coefficients enter. -/
theorem wardBSATopSource_three (h b t a : ℂ) (u : ℕ → ℂ) (r : ℕ) :
    wardBSATopSource h b t a 3 3 u (r+1)=
      wardBSASourceDiagonal h b t 3 (r+1) 3 (a+3) * u (r+1)+
      (-1-t*(h-b-a+((r+1:ℕ):ℂ))+3*t/2)*u r := by
  simp only [wardBSATopSource,wardBSASourceDiagonal,Fin.sum_univ_three]
  iterate 4
    norm_num [wardTopStep,wardCreationDiagonal,wardBSATop,wardBSADiagonal]
    try simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  ring

/-- On the (A,2) outgoing curve the subdiagonal is t times an odd
half-integer. Thus it cannot vanish at an integer coefficient when t is nonzero. -/
theorem wardBSATopSource_label_three (A : ℕ) (t : ℂ) (ht : t≠0)
    (u : ℕ → ℂ) (r : ℕ) :
    wardBSATopSource (fusionKacWeight (A:ℂ) 2 t) (fusionKacWeight (A:ℂ) 0 t)
      t (vermaBSAWeight 3 t) 3 3 u (r+1)=
      wardBSASourceDiagonal (fusionKacWeight (A:ℂ) 2 t) (fusionKacWeight (A:ℂ) 0 t)
        t 3 (r+1) 3 (vermaBSAWeight 3 t+3)*u (r+1)+
      t*((A:ℂ)-(r:ℂ)-1/2)*u r := by
  rw [wardBSATopSource_three]
  congr 1
  unfold fusionKacWeight vermaBSAWeight
  push_cast
  field_simp
  ring

/-- The scalar top coordinates of the actual normalized preterminal
solution. Its leading coefficient is one, not an arbitrary normalization. -/
noncomputable def fusionKernelTop (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N)
    (r : ℕ) : ℂ :=
  vermaTopCoordinate (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) r
    ((fusionKernelSequence A N t him hN).val r)

/-- The highest Verma vector has top coordinate one at level zero. -/
theorem vermaTopCoordinate_highest (c h : ℂ) :
    vermaTopCoordinate c h 0 (highestVector c h)=1 := by
  have hh := vermaTopCoordinate_sorted c h 0 [] (sortedWord_replicate_zero 0)
  simpa [negWord] using hh

/-- The actual coefficient construction starts the scalar recursion at one. -/
@[simp] theorem fusionKernelTop_zero (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N) :
    fusionKernelTop A N t him hN 0=1 := by
  unfold fusionKernelTop
  rw [fusionKernelSequence_initial,vermaTopCoordinate_highest]

/-- Every preterminal scalar source equation follows from the actual
vector equation. There is no assumed scalar solution or matrix bridge. -/
theorem fusionKernelTop_source_below (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N)
    (r : ℕ) (hr : r<A*(N-1)) :
    wardBSATopSource (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) (fusionKacWeight (A:ℂ) 0 t)
      t (vermaBSAWeight N t) N N (fusionKernelTop A N t him hN) r=0 := by
  unfold fusionKernelTop
  rw [← wardSourceAt_top, fusionKernelSequence_source_below A N t him hN r hr,map_zero]

/-- At resonance the undivided scalar source is precisely a coordinate of
the actual terminal state. Nonzero scalar output would prove nonzero state. -/
theorem fusionTerminalState_top (A N : ℕ) (t : ℂ) (him : t.im≠0) (hN : 2≤N) :
    vermaTopCoordinate (vermaBSACharge t) (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (A*(N-1)) (fusionTerminalState A N t him hN).val=
      wardBSATopSource (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t) (fusionKacWeight (A:ℂ) 0 t)
        t (vermaBSAWeight N t) N N (fusionKernelTop A N t him hN) (A*(N-1)) := by
  exact wardSourceAt_top _ _ _ _ _ _ _ _

end VOA.InverseDS.VirasoroVerma
