/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSATopRecursion

/-!
# The full fusion equation as a two-index scalar convolution

Remove the alternating sign of each BSA stage. The diagonal is the
affine convolution; the off-diagonal is a prefix sum of
the preceding coefficient. This makes the full equation accessible to
finite differences and a formal binomial gauge, without discarding any
contribution to the actual terminal vector.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- One sign-normalized contribution to the full source. The previous
coefficient occurs only for descendant index at least two. -/
noncomputable def fusionTopStep (b y : ℂ) (n j r : ℕ) (q : ℕ → ℕ → ℂ) : ℂ :=
  (((n:ℂ)-(j:ℂ))*b+(j:ℂ)-y-(r:ℂ))*q j r+
    if 2≤n-j ∧ 0<r then q j (r-1) else 0

/-- The complete normalized source at stage n and coefficient r. Unlike
the diagonal-only source, this retains contributions from coefficient r-1. -/
noncomputable def fusionTopSum (b y : ℂ) (q : ℕ → ℕ → ℂ) (n r : ℕ) : ℂ :=
  ∑ j : Fin n, fusionTopStep b y n j r q

/-- The finite normalized BSA recursion on an arbitrary scalar input.
Only stages strictly below N enter its undivided terminal source. -/
noncomputable def fusionTopCoeff (b t y : ℂ) (N : ℕ) (u : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, r => u r
  | n+1, r => (-t/(((n:ℂ)+1)*((N:ℂ)-((n:ℂ)+1)))) *
      ∑ j : Fin (n+1),
        ((((n:ℂ)+1-(j:ℂ))*b+(j:ℂ)-y-(r:ℂ))*fusionTopCoeff b t y N u j r+
          if 2≤n+1-j ∧ 0<r then fusionTopCoeff b t y N u j (r-1) else 0)
termination_by n => n

/-- At a positive stage the recursion is exactly its undivided source
multiplied by the prescribed coefficient; this does not divide at resonance. -/
theorem fusionTopCoeff_eq_sum (b t y : ℂ) (N n : ℕ) (u : ℕ → ℂ) (r : ℕ)
    (hn : 0<n) :
    fusionTopCoeff b t y N u n r=(-t/((n:ℂ)*((N:ℂ)-(n:ℂ)))) *
      fusionTopSum b y (fusionTopCoeff b t y N u) n r := by
  cases n with
  | zero => omega
  | succ n => simp only [fusionTopCoeff,fusionTopSum,fusionTopStep,Nat.cast_add,Nat.cast_one]

/-- A single actual top-coordinate term acquires precisely the total
stage sign after the intermediate stage is normalized. -/
theorem wardTopStep_normalized (h b a : ℂ) (n j r : ℕ) (hj : j≤n)
    (q : ℕ → ℕ → ℂ) :
    wardTopStep h b (a+(n:ℂ)) (n-j) r (fun k => (-1:ℂ)^j*q j k)=
      (-1:ℂ)^n*fusionTopStep b (h-a) n j r q := by
  have hc : ((n-j:ℕ):ℂ)+(j:ℂ)=(n:ℂ) := by exact_mod_cast Nat.sub_add_cancel hj
  have hp : (-1:ℂ)^(n-j)*(-1:ℂ)^j=(-1:ℂ)^n := by rw [← pow_add,Nat.sub_add_cancel hj]
  unfold wardTopStep wardCreationDiagonal fusionTopStep
  split_ifs
  · linear_combination hp*((((n:ℂ)-(j:ℂ))*b+(j:ℂ)-(h-a)-(r:ℂ))*q j r+q j (r-1))+
      ((-1:ℂ)^(n-j)*(-1:ℂ)^j)*q j r*(b-1)*hc
  · linear_combination hp*(((n:ℂ)-(j:ℂ))*b+(j:ℂ)-(h-a)-(r:ℂ))*q j r+
      ((-1:ℂ)^(n-j)*(-1:ℂ)^j)*q j r*(b-1)*hc

/-- The normalized two-index recursion is the complete actual scalar
projection, with the input field weight entering only through h-a. -/
theorem wardBSATop_normalized (h b t a : ℂ) (N n : ℕ) (u : ℕ → ℂ) (r : ℕ) :
    wardBSATop h b t a N u n r=(-1:ℂ)^n*fusionTopCoeff b t (h-a) N u n r := by
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    cases n with
    | zero => simp [wardBSATop,fusionTopCoeff]
    | succ n =>
      rw [wardBSATop,fusionTopCoeff_eq_sum b t (h-a) N (n+1) u r (by omega),mul_left_comm]
      simp only [Nat.cast_add,Nat.cast_one]
      congr 1
      rw [fusionTopSum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hh : wardBSATop h b t a N u j = fun k => (-1:ℂ)^j.val*fusionTopCoeff b t (h-a) N u j k := by
        funext k
        exact ih j j.isLt k
      rw [hh]
      simpa only [Nat.cast_add,Nat.cast_one] using
        wardTopStep_normalized h b a (n+1) j r (by omega) (fusionTopCoeff b t (h-a) N u)

/-- The undivided normalized source is exactly the actual full source,
including its terminal coefficient. This is not a diagonal approximation. -/
theorem wardBSATopSource_normalized (h b t a : ℂ) (N n : ℕ) (u : ℕ → ℂ) (r : ℕ) :
    wardBSATopSource h b t a N n u r=
      (-1:ℂ)^n*fusionTopSum b (h-a) (fusionTopCoeff b t (h-a) N u) n r := by
  unfold wardBSATopSource fusionTopSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hh : wardBSATop h b t a N u j = fun k => (-1:ℂ)^j.val*fusionTopCoeff b t (h-a) N u j k := by
    funext k
    exact wardBSATop_normalized h b t a N j u k
  rw [hh]
  exact wardTopStep_normalized h b a n j r (by omega) _

/-- The off-diagonal contribution at stage n+1 is a prefix of length n.
This precise endpoint is what produces a one-step source after finite differences. -/
theorem fusionTopSum_decompose (b y : ℂ) (q : ℕ → ℕ → ℂ) (n r : ℕ) :
    fusionTopSum b y q (n+1) r=
      fusionSum b (y+(r:ℂ)) (fun j => q j r) (n+1)+
        if 0<r then ∑ j : Fin n, q j (r-1) else 0 := by
  unfold fusionTopSum fusionTopStep fusionSum
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    ring
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    have hh (j : Fin n) : 2≤n+1-j.val := by omega
    simp only [hh,true_and]
    split_ifs <;> simp_all

/-- The initial source has no terms at all. -/
@[simp] theorem fusionTopSum_zero (b y : ℂ) (q : ℕ → ℕ → ℂ) (r : ℕ) :
    fusionTopSum b y q 0 r=0 := by simp [fusionTopSum]

/-- Before resonance, multiplying out the denominator gives the exact
undivided full Ward recursion. No condition on the input coefficients enters. -/
theorem fusionTopCoeff_ward (b t y : ℂ) (N n : ℕ) (u : ℕ → ℂ) (r : ℕ)
    (hn : n<N) :
    (n:ℂ)*((n:ℂ)-(N:ℂ))*fusionTopCoeff b t y N u n r=
      t*fusionTopSum b y (fusionTopCoeff b t y N u) n r := by
  cases n with
  | zero => simp
  | succ n =>
    rw [fusionTopCoeff_eq_sum b t y N (n+1) u r (by omega)]
    have hd := VirModule.bsa_denominator_ne_zero N (n+1) (by omega) hn
    push_cast at hd ⊢
    field_simp [(mul_ne_zero_iff.mp hd).1,(mul_ne_zero_iff.mp hd).2]
    <;> ring

end VOA.InverseDS.VirasoroVerma
