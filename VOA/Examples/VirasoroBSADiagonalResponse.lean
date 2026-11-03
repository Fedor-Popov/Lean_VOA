/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSANormRecurrence

/-!
# Pairing the BSA state with its charge response

The diagonal response is the actual canonical pairing B(f_r,T_r).
Adjointness reduces it to a numerical recursion involving the already
proved intermediate norms. A contiguous relation evaluates the terminal
diagonal pairing as a nonzero multiple of the recurrence residual at every
even level at least four. This pairing is distinct from the terminal
norm derivative, which also contains translation descendants.
-/
namespace VOA.VirModule

/-- The actual diagonal pairing of the level-r BSA state and the undivided
L₂ response at the singular charge. Its identification with the terminal
norm derivative is not built into this definition. -/
noncomputable def bsaDiagonalResponse (N r : ℕ) : ℂ :=
  (VirGram4.canB (bsaCharge N)).form (bsaState (bsaCharge N) N r)
    (bsaL2SourceResponse (bsaCharge N) N r)

/-- Adjointness turns the response's negative modes into known positive
modes on the BSA state. Thus this genuine pairing satisfies an inhomogeneous
scalar recursion, with forcing one half of the actual intermediate norm. -/
theorem bsaDiagonalResponse_recursion (N r : ℕ) (hr : r<N) :
    bsaDiagonalResponse N r = bsaNormCoefficient N r/2 +
      ∑ j : Fin r, bsaWardCoefficient N r j *
        (-bsaParameter N/(((j:ℂ)+2)*((N:ℂ)-((j:ℂ)+2))))*
          bsaDiagonalResponse N j := by
  unfold bsaDiagonalResponse
  rw [bsaL2SourceResponse, map_add, map_smul, map_sum, smul_eq_mul,
    ← bsaNormCoefficient_eq_norm N r hr]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    rw [← VirGram4.canB_adj', show -((j:ℤ)-(r:ℤ))=(r:ℤ)-(j:ℤ) by ring,
      bsaState_positive_to N r j j.isLt hr, map_smul, LinearMap.smul_apply,
      bsaL2Response_eq_source, map_smul, smul_eq_mul, smul_eq_mul]
    ring

/-- At level zero the diagonal response is one half of the vacuum norm. -/
@[simp] theorem bsaDiagonalResponse_zero (N : ℕ) : bsaDiagonalResponse N 0=1/2 := by
  simp [bsaDiagonalResponse, bsaL2SourceResponse, bsaState_zero, VirGram4.canB_vac]

/-- The level-one response pairing vanishes because the level-one BSA
state is zero. This also supplies the second initial condition. -/
@[simp] theorem bsaDiagonalResponse_one (N : ℕ) : bsaDiagonalResponse N 1=0 := by
  simp [bsaDiagonalResponse, bsaState_one]

/-- The divided diagonal response, used only before r+2 reaches N. Its
coefficient is the same one that multiplies the actual vector response. -/
noncomputable def bsaDividedDiagonal (N r : ℕ) : ℂ :=
  (-bsaParameter N/(((r:ℂ)+2)*((N:ℂ)-((r:ℂ)+2))))*bsaDiagonalResponse N r

/-- The diagonal pairing is the inhomogeneous Ward sum of its divided
predecessors. This statement includes r=N-2 without dividing at that index. -/
theorem bsaDiagonalResponse_ward (N r : ℕ) (hr : r<N) :
    bsaDiagonalResponse N r = bsaNormCoefficient N r/2 +
      bsaWardSum N (bsaDividedDiagonal N) r := by
  rw [bsaDiagonalResponse_recursion N r hr]
  simp only [bsaWardSum, bsaDividedDiagonal, mul_assoc]

/-- Multiplying out the intermediate denominator gives an equation whose
forcing term is the actual diagonal response. The terminal index is excluded. -/
theorem bsaDividedDiagonal_ward (N r : ℕ) (hr : r+2<N) :
    ((r:ℂ)+2)*((r:ℂ)+2-(N:ℂ))*bsaDividedDiagonal N r =
      bsaParameter N*(bsaNormCoefficient N r/2 + bsaWardSum N (bsaDividedDiagonal N) r) := by
  have h1 : (r:ℂ)+2 ≠ 0 := by exact_mod_cast (show (r:ℤ)+2≠0 by omega)
  have h2 : (N:ℂ)-((r:ℂ)+2) ≠ 0 := by
    exact_mod_cast (show (N:ℤ)-((r:ℤ)+2)≠0 by omega)
  rw [← bsaDiagonalResponse_ward N r (by omega), bsaDividedDiagonal]
  all_goals field_simp
  all_goals ring


/-- The rational constant appearing in the contiguous relation between
the norm recurrence and the response recurrence. -/
noncomputable def bsaDiagonalFactor (N : ℕ) : ℂ :=
  ((N:ℂ)+1)/(3*((N:ℂ)-1)*((N:ℂ)+3))

/-- A candidate for the divided response, expressed locally through three
successive actual norm coefficients. The following recurrence argument
identifies it before the terminal level. -/
noncomputable def bsaDiagonalCandidate (N r : ℕ) : ℂ :=
  bsaDiagonalFactor N * (2*((r:ℂ)+2)*bsaNormCoefficient N (r+2) -
    3*((r:ℂ)+1)*bsaNormCoefficient N (r+1) +
    ((r:ℂ)-1/2)*bsaNormCoefficient N r)

/-- The local defect of the established three-term norm equation. It is
zero below the terminal index and records the undivided residual there. -/
noncomputable def bsaNormLocalDefect (N r : ℕ) : ℂ :=
  ((r:ℂ)+2)*((r:ℂ)+2-(N:ℂ))*bsaNormCoefficient N (r+2) -
    (2*((r:ℂ)+1)*((r:ℂ)+1-(N:ℂ))+bsaParameter N*((r:ℂ)+1))*bsaNormCoefficient N (r+1) +
    ((r:ℂ)*((r:ℂ)-(N:ℂ))-bsaParameter N*(bsaL2Offset N+2-(r:ℂ)))*bsaNormCoefficient N r

/-- The candidate's defect in the inhomogeneous response equation. Keeping
this quantity undivided makes its terminal value meaningful. -/
noncomputable def bsaDiagonalError (N r : ℕ) : ℂ :=
  ((r:ℂ)+2)*((r:ℂ)+2-(N:ℂ))*bsaDiagonalCandidate N r -
    bsaParameter N*(bsaNormCoefficient N r/2+bsaWardSum N (bsaDiagonalCandidate N) r)

/-- The candidate's second defect difference is a linear combination of
three norm defects. This polynomial identity is the contiguous relation
that makes the response calculation telescope. -/
theorem bsaDiagonalError_second (N r : ℕ) (hN : 4≤N) :
    bsaDiagonalError N (r+2)-2*bsaDiagonalError N (r+1)+bsaDiagonalError N r =
      bsaDiagonalFactor N*(2*((r:ℂ)+4)*bsaNormLocalDefect N (r+2) -
        (3*(r:ℂ)+11)*bsaNormLocalDefect N (r+1)+((r:ℂ)+7/2)*bsaNormLocalDefect N r) := by
  have hs := bsaWardSum_second_difference N r (bsaDiagonalCandidate N)
  unfold bsaDiagonalError
  have he : bsaWardSum N (bsaDiagonalCandidate N) (r+2) =
      2*bsaWardSum N (bsaDiagonalCandidate N) (r+1)-bsaWardSum N (bsaDiagonalCandidate N) r +
      ((r:ℂ)+1)*bsaDiagonalCandidate N (r+1)+(bsaL2Offset N+2-(r:ℂ))*bsaDiagonalCandidate N r := by
    linear_combination hs
  rw [he]
  unfold bsaDiagonalCandidate bsaNormLocalDefect bsaDiagonalFactor bsaParameter bsaL2Offset
  have hm : (N:ℂ)-1 ≠ 0 := by exact_mod_cast (show (N:ℤ)-1≠0 by omega)
  have hp : (N:ℂ)+3 ≠ 0 := by exact_mod_cast (show (N:ℤ)+3≠0 by omega)
  push_cast
  all_goals field_simp
  all_goals ring

/-- The second canonical norm coefficient is the first nontrivial Ward
value. Its explicit rational form supplies the contiguous relation's boundary. -/
theorem bsaNormCoefficient_two (N : ℕ) :
    bsaNormCoefficient N 2 = -bsaParameter N/(2*((N:ℂ)-2))*(bsaL2Offset N+2) := by
  rw [bsaNormCoefficient, Fin.sum_univ_two]
  norm_num [bsaWardCoefficient, bsaNormCoefficient_one,
    show bsaNormCoefficient N 0=1 by simp [bsaNormCoefficient]]
  all_goals ring_nf
  all_goals simp

/-- The next norm equals the second norm before the level-three boundary.
The equality follows from the Ward coefficients and t=(N+1)/2. -/
theorem bsaNormCoefficient_three (N : ℕ) (hN : 4≤N) :
    bsaNormCoefficient N 3 = bsaNormCoefficient N 2 := by
  have h2 : (N:ℂ)-2 ≠ 0 := by exact_mod_cast (show (N:ℤ)-2≠0 by omega)
  have h3 : (N:ℂ)-3 ≠ 0 := by exact_mod_cast (show (N:ℤ)-3≠0 by omega)
  rw [bsaNormCoefficient, Fin.sum_univ_three]
  norm_num [bsaWardCoefficient, bsaNormCoefficient_one,
    show bsaNormCoefficient N 0=1 by simp [bsaNormCoefficient], bsaNormCoefficient_two]
  unfold bsaParameter bsaL2Offset
  all_goals field_simp
  all_goals ring

/-- The candidate satisfies its response equation at level zero. This
uses the actual second norm coefficient, not a separately prescribed value. -/
theorem bsaDiagonalError_zero (N : ℕ) (hN : 4≤N) : bsaDiagonalError N 0=0 := by
  have h1 : (N:ℂ)-1 ≠ 0 := by exact_mod_cast (show (N:ℤ)-1≠0 by omega)
  have h2 : (N:ℂ)-2 ≠ 0 := by exact_mod_cast (show (N:ℤ)-2≠0 by omega)
  have hp : (N:ℂ)+3 ≠ 0 := by exact_mod_cast (show (N:ℤ)+3≠0 by omega)
  rw [bsaDiagonalError, bsaWardSum_zero]
  norm_num [bsaDiagonalCandidate, bsaNormCoefficient_two, bsaNormCoefficient_one,
    show bsaNormCoefficient N 0=1 by simp [bsaNormCoefficient], bsaDiagonalFactor, bsaParameter, bsaL2Offset]
  all_goals field_simp
  all_goals ring

/-- The second initial defect also vanishes; the first and third norm
coefficients enforce the level-one boundary of the contiguous relation. -/
theorem bsaDiagonalError_one (N : ℕ) (hN : 4≤N) : bsaDiagonalError N 1=0 := by
  have h1 : (N:ℂ)-1 ≠ 0 := by exact_mod_cast (show (N:ℤ)-1≠0 by omega)
  have h2 : (N:ℂ)-2 ≠ 0 := by exact_mod_cast (show (N:ℤ)-2≠0 by omega)
  have h3 : (N:ℂ)-3 ≠ 0 := by exact_mod_cast (show (N:ℤ)-3≠0 by omega)
  have hp : (N:ℂ)+3 ≠ 0 := by exact_mod_cast (show (N:ℤ)+3≠0 by omega)
  rw [bsaDiagonalError, bsaWardSum_one]
  norm_num [bsaDiagonalCandidate, bsaNormCoefficient_three N hN,
    bsaNormCoefficient_two, bsaNormCoefficient_one, bsaDiagonalFactor, bsaParameter, bsaL2Offset]

/-- The local norm defect vanishes below resonance by the already proved
three-term equation for the genuine intermediate norms. -/
theorem bsaNormLocalDefect_zero (N r : ℕ) (hr : r+2<N) :
    bsaNormLocalDefect N r=0 := bsaNormCoefficient_three_term N r hr

/-- At resonance the local defect equals minus t times the undivided
terminal residual. No value is assigned by division through zero. -/
theorem bsaNormLocalDefect_terminal (r : ℕ) :
    bsaNormLocalDefect (r+2) r = -bsaParameter (r+2)*bsaNormTerminalResidual (r+2) := by
  have hh := bsaNormTerminalResidual_eq r
  unfold bsaNormLocalDefect
  push_cast
  linear_combination hh

/-- The candidate solves the response equation at every intermediate
index: its second differences vanish and both initial defects are zero. -/
theorem bsaDiagonalError_zero_of_lt (N r : ℕ) (hN : 4≤N) (hr : r+2<N) :
    bsaDiagonalError N r=0 := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    obtain rfl | hr0 := Nat.eq_zero_or_pos r
    · exact bsaDiagonalError_zero N hN
    by_cases he : r=1
    · subst r; exact bsaDiagonalError_one N hN
    have hstep := bsaDiagonalError_second N (r-2) hN
    rw [bsaNormLocalDefect_zero N (r-2+2) (by omega),
      bsaNormLocalDefect_zero N (r-2+1) (by omega),
      bsaNormLocalDefect_zero N (r-2) (by omega),
      ih (r-2+1) (by omega) (by omega), ih (r-2) (by omega) (by omega)] at hstep
    simpa only [show r-2+2=r by omega, mul_zero, sub_zero, add_zero] using hstep

/-- Uniqueness of the triangular Ward recurrence identifies the numerical
candidate with the divided ACTUAL diagonal response below the terminal level. -/
theorem bsaDiagonalCandidate_eq (N r : ℕ) (hN : 4≤N) (hr : r+2<N) :
    bsaDiagonalCandidate N r=bsaDividedDiagonal N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    have he := bsaDiagonalError_zero_of_lt N r hN hr
    have hd := bsaDividedDiagonal_ward N r hr
    have hs : bsaWardSum N (bsaDiagonalCandidate N) r =
        bsaWardSum N (bsaDividedDiagonal N) r := by
      unfold bsaWardSum
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j j.isLt (by omega)]
    unfold bsaDiagonalError at he
    rw [hs] at he
    have h1 : (r:ℂ)+2≠0 := by exact_mod_cast (show (r:ℤ)+2≠0 by omega)
    have h2 : (r:ℂ)+2-(N:ℂ)≠0 := by exact_mod_cast (show (r:ℤ)+2-(N:ℤ)≠0 by omega)
    apply mul_left_cancel₀ (mul_ne_zero h1 h2)
    linear_combination he-hd


/-- At the terminal response level only the highest norm defect survives
the contiguous relation. This computes the candidate's terminal error in
terms of the already proved nonzero recurrence residual. -/
theorem bsaDiagonalError_terminal (r : ℕ) :
    bsaDiagonalError (r+4) (r+2) =
      -2*((r:ℂ)+4)*bsaDiagonalFactor (r+4)*bsaParameter (r+4)*bsaNormTerminalResidual (r+4) := by
  have hh := bsaDiagonalError_second (r+4) r (by omega)
  rw [bsaDiagonalError_zero_of_lt (r+4) (r+1) (by omega) (by omega),
    bsaDiagonalError_zero_of_lt (r+4) r (by omega) (by omega),
    bsaNormLocalDefect_zero (r+4) (r+1) (by omega),
    bsaNormLocalDefect_zero (r+4) r (by omega)] at hh
  have ht := bsaNormLocalDefect_terminal (r+2)
  rw [show r+2+2=r+4 by omega] at ht
  rw [ht] at hh
  linear_combination hh

/-- The ACTUAL diagonal source pairing at resonance is an explicit
nonzero rational multiple of the terminal norm recurrence residual. This
settles the second proposed scalar identity; it does not yet identify this
pairing with the full norm derivative involving translation descendants. -/
theorem bsaDiagonalResponse_terminal (r : ℕ) :
    bsaDiagonalResponse (r+4) (r+2) =
      2*((r:ℂ)+4)*bsaDiagonalFactor (r+4)*bsaNormTerminalResidual (r+4) := by
  have hh := bsaDiagonalError_terminal r
  have hs : bsaWardSum (r+4) (bsaDiagonalCandidate (r+4)) (r+2) =
      bsaWardSum (r+4) (bsaDividedDiagonal (r+4)) (r+2) := by
    unfold bsaWardSum
    apply Finset.sum_congr rfl
    intro j hj
    rw [bsaDiagonalCandidate_eq (r+4) j (by omega) (by have := j.isLt; omega)]
  unfold bsaDiagonalError at hh
  rw [hs, ← bsaDiagonalResponse_ward (r+4) (r+2) (by omega)] at hh
  have ht : bsaParameter (r+4)≠0 := by
    unfold bsaParameter
    exact div_ne_zero (Nat.cast_add_one_ne_zero _) (by norm_num)
  apply mul_left_cancel₀ ht
  push_cast at hh
  linear_combination -hh

/-- The rational contiguous-relation factor cannot vanish at the levels
used here: its numerator and both denominator factors are nonzero. -/
theorem bsaDiagonalFactor_ne_zero (N : ℕ) (hN : 4≤N) : bsaDiagonalFactor N≠0 := by
  unfold bsaDiagonalFactor
  apply div_ne_zero (Nat.cast_add_one_ne_zero _)
  have h1 : (N:ℂ)-1≠0 := by exact_mod_cast (show (N:ℤ)-1≠0 by omega)
  have h3 : (N:ℂ)+3≠0 := by exact_mod_cast (show (N:ℤ)+3≠0 by omega)
  exact mul_ne_zero (mul_ne_zero (by norm_num) h1) h3

/-- At every even singular level at least four, pairing the intermediate
state with the undivided L₂ response gives a nonzero scalar. This is a
genuine canonical pairing, not just a nonzero response vector. The full
norm derivative remains a different scalar until its translation sum is
identified with this diagonal pairing. -/
theorem bsaDiagonalResponse_even_ne_zero (k : ℕ) :
    bsaDiagonalResponse (2*(k+2)) (2*k+2) ≠ 0 := by
  have hh := bsaDiagonalResponse_terminal (2*k)
  rw [show 2*k+4=2*(k+2) by omega] at hh
  rw [hh]
  have hN : ((2*k:ℕ):ℂ)+4≠0 := by exact_mod_cast (show (2*k:ℤ)+4≠0 by omega)
  apply mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hN)
    (bsaDiagonalFactor_ne_zero _ (by omega)))
  convert bsaNormTerminalResidual_even_ne_zero (k+1) using 1


/-- Repeated translation in the first slot is adjoint to repeated L₁ in
the second slot. This connects the scalar norm response's positive-mode
sum with a single explicit state pairing. -/
theorem bsaTranslation_power_adj (c : ℂ) (m : ℕ) (u v : VirUniv c) :
    (VirGram4.canB c).form (((Lop c (-1))^m) u) v =
      (VirGram4.canB c).form u (((Lop c 1)^m) v) := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, VirGram4.canB_adj]
    norm_num only [neg_neg] at *
    rw [ih, pow_succ, Module.End.mul_apply]

/-- The coefficient of the formally translated state series exp(-z L₋₁)F(z).
It is a finite sum at each level, so no convergence or infinite operator
exponential is assumed. Its proposed equality to (-1)^r f_r is not assumed. -/
noncomputable def bsaReflectedState (c : ℂ) (N r : ℕ) : VirUniv c :=
  ∑ j : Fin (r+1), positiveLadderCoefficient (r-j.val) •
    (((Lop c (-1))^(r-j.val)) (bsaState c N j))

/-- The actual scalar norm derivative response is exactly one canonical
pairing with the reflected state. The remaining BSA gap is therefore a
specific translation-reflection identity (or its equality in the radical),
not an unspecified change of invariant form or deformation assumption. -/
theorem bsaScalarNormResponse_reflected (c : ℂ) (N r : ℕ) :
    bsaScalarNormResponse c N r =
      (VirGram4.canB c).form (bsaReflectedState c N r) (bsaL2SourceResponse c N r) := by
  simp only [bsaScalarNormResponse, bsaReflectedState, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, bsaTranslation_power_adj]

end VOA.VirModule
