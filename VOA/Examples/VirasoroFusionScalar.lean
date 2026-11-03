/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSADiagonalOperator
import VOA.Examples.VirasoroBSANormRecurrence

/-!
# A normalized scalar equation for the actual fusion diagonal

Removing the alternating sign and following the input field weight turns
the actual diagonal into a single finite convolution. Its second difference
is a three-term equation, with the terminal source left undivided.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- The sign-normalized BSA diagonal, as a function of the exponent y.
Only intermediate indices below N enter its terminal source. -/
noncomputable def fusionCoeff (b t y : ℂ) (N : ℕ) : ℕ → ℂ
  | 0 => 1
  | n+1 => (-t/(((n:ℂ)+1)*((N:ℂ)-((n:ℂ)+1)))) *
      ∑ j : Fin (n+1), (((n:ℂ)+1-(j:ℂ))*b+(j:ℂ)-y)*fusionCoeff b t y N j
termination_by n => n

/-- The affine convolution before division by n(N-n). -/
noncomputable def fusionSum (b y : ℂ) (q : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j : Fin n, (((n:ℂ)-(j:ℂ))*b+(j:ℂ)-y)*q j

/-- At positive indices the normalized coefficient is the displayed multiple
of its finite source; the terminal source will be used without this division. -/
theorem fusionCoeff_eq_sum (b t y : ℂ) (N n : ℕ) (hn : 0<n) :
    fusionCoeff b t y N n=(-t/((n:ℂ)*((N:ℂ)-(n:ℂ)))) *
      fusionSum b y (fusionCoeff b t y N) n := by
  cases n with
  | zero => omega
  | succ n => simp only [fusionCoeff,fusionSum,Nat.cast_add,Nat.cast_one]

/-- The normalized scalar is exactly the actual intermediate diagonal,
including its alternating sign and the shifted output field weight. -/
theorem wardBSADiagonal_normalized (h b t a : ℂ) (N r n : ℕ) :
    wardBSADiagonal h b t N r n (a+(n:ℂ))=
      (-1:ℂ)^n*fusionCoeff b t (h+(r:ℂ)-a) N n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [wardBSADiagonal,fusionCoeff]
    | succ n =>
      rw [wardBSADiagonal,fusionCoeff]
      rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : ((n+1-j:ℕ):ℂ)+(j:ℂ)=((n+1:ℕ):ℂ) := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : j.val≤n+1))
      have hi : a+((n+1:ℕ):ℂ)-((n+1-j:ℕ):ℂ)=a+(j:ℂ)  := by linear_combination -hj'
      rw [hi,ih j j.isLt,wardCreationDiagonal]
      have hp : (-1:ℂ)^(n+1-j)*(-1:ℂ)^j.val=(-1:ℂ)^(n+1) := by
        rw [← pow_add,Nat.sub_add_cancel (by omega : j.val≤n+1)]
      push_cast at hj' ⊢
      linear_combination hp*(((n:ℂ)+1-(j:ℂ))*b+(j:ℂ)-(h+(r:ℂ)-a))*fusionCoeff b t (h+(r:ℂ)-a) N j +
        ((-1:ℂ)^(n+1-j)*(-1:ℂ)^j.val)*fusionCoeff b t (h+(r:ℂ)-a) N j*(b-1)*hj'

/-- The undivided actual source has the same normalization. Thus root
statements about the convolution concern the real operator diagonal. -/
theorem wardBSASourceDiagonal_normalized (h b t a : ℂ) (N r n : ℕ) :
    wardBSASourceDiagonal h b t N r n (a+(n:ℂ))=
      (-1:ℂ)^n*fusionSum b (h+(r:ℂ)-a) (fusionCoeff b t (h+(r:ℂ)-a) N) n := by
  unfold wardBSASourceDiagonal fusionSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : ((n-j:ℕ):ℂ)+(j:ℂ)=(n:ℂ) := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : j.val≤n))
  have hi : a+(n:ℂ)-((n-j:ℕ):ℂ)=a+(j:ℂ)  := by linear_combination -hj'
  rw [hi,wardBSADiagonal_normalized,wardCreationDiagonal]
  have hp : (-1:ℂ)^(n-j)*(-1:ℂ)^j.val=(-1:ℂ)^n := by
    rw [← pow_add,Nat.sub_add_cancel (by omega : j.val≤n)]
  linear_combination hp*(((n:ℂ)-(j:ℂ))*b+(j:ℂ)-(h+(r:ℂ)-a))*fusionCoeff b t (h+(r:ℂ)-a) N j +
    ((-1:ℂ)^(n-j)*(-1:ℂ)^j.val)*fusionCoeff b t (h+(r:ℂ)-a) N j*(b-1)*hj'

/-- Second finite differences of the affine source cancel all old terms,
leaving just the two newest coefficients. -/
theorem fusionSum_second_difference (b y : ℂ) (q : ℕ → ℂ) (n : ℕ) :
    fusionSum b y q (n+2)-2*fusionSum b y q (n+1)+fusionSum b y q n=
      (b+(n:ℂ)+1-y)*q (n+1)+(y-(n:ℂ))*q n := by
  unfold fusionSum
  rw [show n+2=(n+1)+1 by omega,Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one]
  have hs : (∑ j : Fin n, (((n:ℂ)+1+1-(j:ℂ))*b+(j:ℂ)-y)*q j)-
      2*(∑ j : Fin n, (((n:ℂ)+1-(j:ℂ))*b+(j:ℂ)-y)*q j)+
      (∑ j : Fin n, (((n:ℂ)-(j:ℂ))*b+(j:ℂ)-y)*q j)=0 := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j hj
    ring
  linear_combination hs

/-- The undivided recurrence holds strictly before N, where its denominator
is nonzero. No terminal division is used. -/
theorem fusionCoeff_ward (b t y : ℂ) (N n : ℕ) (hn : n<N) :
    (n:ℂ)*((n:ℂ)-(N:ℂ))*fusionCoeff b t y N n=
      t*fusionSum b y (fusionCoeff b t y N) n := by
  cases n with
  | zero => simp [fusionSum]
  | succ n =>
    rw [fusionCoeff_eq_sum b t y N (n+1) (by omega)]
    have hd := bsa_denominator_ne_zero N (n+1) (by omega) hn
    push_cast at hd ⊢
    field_simp [(mul_ne_zero_iff.mp hd).1,(mul_ne_zero_iff.mp hd).2]
    <;> ring
end VOA.InverseDS.VirasoroVerma
