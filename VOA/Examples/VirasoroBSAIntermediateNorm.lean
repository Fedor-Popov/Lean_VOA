/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSAChargeResponse

/-!
# Actual norms of intermediate BSA states

At the singular charge, every positive mode of an intermediate BSA state
is a scalar times an earlier state. The L₁ and L₂ identities generate the
whole family by commutators. Adjointness then reduces the actual canonical
norms to a scalar recursion. No determinant or norm-product formula is
assumed here, and this is not yet the derivative of the terminal norm.
-/
namespace VOA.VirModule

/-- All modes L_(m+2) act on intermediate BSA states by a linear scalar
coefficient. The proof iterates the commutator with L₁; the vacuum boundary
is included by writing the target level as r+m+2. -/
theorem bsaState_higher_positive (N m r : ℕ) (hr : r+m+2<N) :
    Lop (bsaCharge N) ((m:ℤ)+2) (bsaState (bsaCharge N) N (r+m+2)) =
      ((r:ℂ)+(m:ℂ)+2+((m:ℂ)+1)*bsaL2Offset N+(m:ℂ)) •
        bsaState (bsaCharge N) N r := by
  induction m generalizing r with
  | zero => simpa using bsaState_L2 N r hr
  | succ m ih =>
    have hA := ih (r+1) (by omega)
    have hB := ih r (by omega)
    have h1 := bsaState_L1 (bsaCharge N) N (r+m+2) (by omega)
    have h2 := bsaState_L1 (bsaCharge N) N r (by omega)
    have hh := LeeYang.Lop_apply_comm (bsaCharge N) 1 ((m:ℤ)+2)
      (bsaState (bsaCharge N) N (r+(m+1)+2))
    rw [show r+(m+1)+2=(r+1)+m+2 by omega, hA, map_smul, h2] at hh
    rw [show (r+1)+m+2=(r+m+2)+1 by omega, h1, map_smul, hB] at hh
    have hz : ¬ (1:ℤ)+((m:ℤ)+2)=0 := by omega
    simp only [if_neg hz, zero_smul, add_zero] at hh
    have hn : (1:ℂ)-((m:ℤ)+2) ≠ 0 := by
      push_cast
      have hm := Nat.cast_add_one_ne_zero (R := ℂ) m
      intro he
      apply hm
      linear_combination -he
    push_cast at hh
    apply smul_right_injective _ hn
    convert (show ((1:ℂ)-((m:ℤ)+2)) •
        Lop (bsaCharge N) (1+((m:ℤ)+2))
          (bsaState (bsaCharge N) N ((r+m+2)+1)) = _ from eq_sub_of_add_eq' hh.symm) using 1
    · congr 2 <;> push_cast <;> ring
    · push_cast at hh ⊢
      simp only [smul_smul, ← sub_smul]
      congr 1
      ring

/-- The scalar in a positive-mode action from level r down to j. L₁ has
its own boundary coefficient; modes at least two use the uniform Ward
coefficient. This definition is purely numerical. -/
noncomputable def bsaWardCoefficient (N r j : ℕ) : ℂ :=
  if j+1=r then (j:ℂ) else
    (r:ℂ)+((r:ℂ)-(j:ℂ)-1)*bsaL2Offset N+(r:ℂ)-(j:ℂ)-2

/-- Moving from any intermediate level r to a strictly lower level j is
controlled by the numerical Ward coefficient, including the L₁ case. -/
theorem bsaState_positive_to (N r j : ℕ) (hj : j<r) (hr : r<N) :
    Lop (bsaCharge N) ((r:ℤ)-(j:ℤ)) (bsaState (bsaCharge N) N r) =
      bsaWardCoefficient N r j • bsaState (bsaCharge N) N j := by
  by_cases he : j+1=r
  · subst r
    simpa [bsaWardCoefficient] using bsaState_L1 (bsaCharge N) N j hr
  · have hle : j+2≤r := by omega
    have hh := bsaState_higher_positive N (r-j-2) j (by omega)
    rw [show j+(r-j-2)+2=r by omega] at hh
    have hm : ((r-j-2:ℕ):ℤ)+2=(r:ℤ)-(j:ℤ) := by omega
    rw [hm] at hh
    rw [hh, bsaWardCoefficient, if_neg he]
    congr 1
    have hc : ((r-j-2:ℕ):ℂ)=(r:ℂ)-(j:ℂ)-2 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      norm_num
    rw [hc]
    ring

/-- A positive mode whose index exceeds the level kills the intermediate
state because its result would have negative conformal weight. -/
theorem bsaState_positive_above (c : ℂ) (N r m : ℕ) (hm : r<m) :
    Lop c (m:ℤ) (bsaState c N r) = 0 := by
  have hh := Lop_maps_grading c (m:ℤ) (bsaState_mem_grading c N r)
  rw [gradingVir_neg c _ (by omega)] at hh
  exact hh

/-- At a positive intermediate level the actual canonical norm is a weighted
sum of earlier norms. Adjointness moves each negative mode in the source to
the other slot, where the uniform positive-mode formula evaluates it. -/
theorem bsaState_norm_recursion (N r : ℕ) (hr0 : 0<r) (hrN : r<N) :
    (VirGram4.canB (bsaCharge N)).form
      (bsaState (bsaCharge N) N r) (bsaState (bsaCharge N) N r) =
      (-bsaParameter N / ((r:ℂ)*((N:ℂ)-(r:ℂ)))) *
        ∑ j : Fin r, bsaWardCoefficient N r j *
          (VirGram4.canB (bsaCharge N)).form
            (bsaState (bsaCharge N) N j) (bsaState (bsaCharge N) N j) := by
  conv_lhs => arg 1; arg 2; rw [bsaState_eq_source _ N r hr0]
  simp only [bsaSource, map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply,
    smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [VirGram4.canB_adj, show -((j:ℤ)-(r:ℤ))=(r:ℤ)-(j:ℤ) by ring,
    bsaState_positive_to N r j j.isLt hrN, map_smul, smul_eq_mul]

/-- A scalar algorithm for the intermediate norms: start with the normalized
vacuum value one and use the adjoint Ward recursion at each positive level.
Only entries below N will be identified with actual norms. -/
noncomputable def bsaNormCoefficient (N : ℕ) : ℕ → ℂ
  | 0 => 1
  | r+1 => (-bsaParameter N / (((r:ℂ)+1)*((N:ℂ)-((r:ℂ)+1)))) *
      ∑ j : Fin (r+1), bsaWardCoefficient N (r+1) j * bsaNormCoefficient N j
termination_by r => r

/-- The numerical recursion computes the genuine canonical norm, rather
than an independently chosen or hypothesized pairing. -/
theorem bsaNormCoefficient_eq_norm (N r : ℕ) (hr : r<N) :
    bsaNormCoefficient N r =
      (VirGram4.canB (bsaCharge N)).form
        (bsaState (bsaCharge N) N r) (bsaState (bsaCharge N) N r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [bsaNormCoefficient, bsaState_zero, VirGram4.canB_vac]
    | succ r =>
      rw [bsaNormCoefficient, bsaState_norm_recursion N (r+1) (by omega) hr]
      simp only [Nat.cast_add, Nat.cast_one]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j j.isLt (by omega)]

/-- The first scalar coefficient vanishes, reflecting that translation
annihilates the vacuum. This holds even outside the nonterminal range. -/
theorem bsaNormCoefficient_one (N : ℕ) : bsaNormCoefficient N 1 = 0 := by
  simp [bsaNormCoefficient, bsaWardCoefficient]


/-- The coefficient obtained when repeated commutation with L₁ expresses
L_(m+2) on a quasiprimary vector in terms of L₂. Recursion avoids any
choice of normalization: its closed form is (-1)^m/m!. -/
noncomputable def positiveLadderCoefficient : ℕ → ℂ
  | 0 => 1
  | m+1 => -positiveLadderCoefficient m / ((m:ℂ)+1)

/-- The commutator normalization is the familiar signed inverse factorial.
Every factorial is nonzero over the complex numbers. -/
theorem positiveLadderCoefficient_eq (m : ℕ) :
    positiveLadderCoefficient m = (-1:ℂ)^m / (m.factorial:ℂ) := by
  induction m with
  | zero => simp [positiveLadderCoefficient]
  | succ m ih =>
    rw [positiveLadderCoefficient, ih, Nat.factorial_succ, pow_succ]
    push_cast
    have hm : (m:ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero m
    have hf : (m.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    field_simp

/-- On any vector killed by L₁, every higher positive mode is an iterated
L₁ derivative of its L₂ image. This is a module identity at arbitrary charge,
so it also applies away from a singular charge. -/
theorem Lop_positive_of_quasiprimary (c : ℂ) (v : VirUniv c)
    (h1 : Lop c 1 v=0) (m : ℕ) :
    Lop c ((m:ℤ)+2) v = positiveLadderCoefficient m •
      ((Lop c 1)^m) (Lop c 2 v) := by
  induction m with
  | zero => simp [positiveLadderCoefficient]
  | succ m ih =>
    have hh := LeeYang.Lop_apply_comm c 1 ((m:ℤ)+2) v
    have hz : ¬ (1:ℤ)+((m:ℤ)+2)=0 := by omega
    rw [ih, map_smul, h1, map_zero, zero_add, if_neg hz, zero_smul, add_zero] at hh
    have hn : (-( (m:ℂ)+1)) ≠ 0 := neg_ne_zero.mpr (Nat.cast_add_one_ne_zero m)
    apply smul_right_injective _ hn
    dsimp only
    rw [positiveLadderCoefficient, pow_succ', Module.End.mul_apply, smul_smul]
    have he : (-((m:ℂ)+1))*(-positiveLadderCoefficient m/((m:ℂ)+1)) =
        positiveLadderCoefficient m := by field_simp
    rw [he]
    convert hh.symm using 1 <;> push_cast <;> congr 1 <;> ring

/-- Every positive mode of the terminal source has the same charge factor.
The remaining vector is an explicit L₁ iterate of the already constructed
L₂ response. -/
theorem bsaSource_positive_response (c : ℂ) (N r m : ℕ)
    (hN : N=r+2) (hr : 0<r) :
    Lop c ((m:ℤ)+2) (bsaSource c N N) =
      (c-bsaCharge N) • (positiveLadderCoefficient m •
        ((Lop c 1)^m) (bsaL2SourceResponse c N r)) := by
  rw [Lop_positive_of_quasiprimary c _ (bsaSource_L1_terminal c N (by omega)),
    bsaSource_L2_terminal_response c N r hN hr, map_smul, smul_comm]

/-- The scalar charge response of the terminal norm. It pairs intermediate
states with L₁ iterates of the L₂ response in the ACTUAL canonical bilinear
form. Computing this scalar at the singular charge is the remaining norm
problem; vector-response nonvanishing does not imply scalar nonvanishing. -/
noncomputable def bsaScalarNormResponse (c : ℂ) (N r : ℕ) : ℂ :=
  ∑ j : Fin (r+1), positiveLadderCoefficient (r-j.val) *
    (VirGram4.canB c).form (bsaState c N j)
      (((Lop c 1)^(r-j.val)) (bsaL2SourceResponse c N r))

/-- The actual terminal norm factors by c-c_N, with the remaining scalar
computed from the L₂ response. The last source term drops out because L₁
kills the terminal vector; all other positive modes use the ladder formula.
This proves a factorization, not nonvanishing of its scalar factor. -/
theorem bsaSource_norm_factor (c : ℂ) (N r : ℕ) (hN : N=r+2) (hr : 0<r) :
    (VirGram4.canB c).form (bsaSource c N N) (bsaSource c N N) =
      (c-bsaCharge N) * bsaScalarNormResponse c N r := by
  classical
  conv_lhs => arg 1; arg 2; rw [bsaSource]
  simp only [map_sum, LinearMap.sum_apply]
  rw [hN, show r+2=(r+1)+1 by omega, Fin.sum_univ_castSucc]
  have hlast : (VirGram4.canB c).form
      (Lop c ((((r+1:ℕ):ℤ))-(((r+1+1:ℕ):ℤ))) (bsaState c (r+1+1) (r+1)))
      (bsaSource c (r+1+1) (r+1+1)) = 0 := by
    rw [VirGram4.canB_adj]
    have he : -((((r+1:ℕ):ℤ))-(((r+1+1:ℕ):ℤ)))=1 := by push_cast; ring
    rw [he, bsaSource_L1_terminal c _ (by omega), map_zero]
  simp only [Fin.val_last, Fin.val_castSucc]
  rw [hlast, add_zero, bsaScalarNormResponse, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [VirGram4.canB_adj]
  have he : -((j:ℤ)-(((r+1+1:ℕ):ℤ)))=((r-j.val:ℕ):ℤ)+2 := by have := j.isLt; omega
  rw [he, bsaSource_positive_response c (r+1+1) r (r-j.val) (by omega) hr,
    map_smul, map_smul, smul_eq_mul, smul_eq_mul]

end VOA.VirModule
