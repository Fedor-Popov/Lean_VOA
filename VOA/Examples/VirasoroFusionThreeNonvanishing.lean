/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSATopRecursion
import VOA.Examples.VirasoroFusionSecondWard

/-!
# Nonzero actual fusion output on every (A,2) curve

For seed index three the projected source is bidiagonal: coefficient r+1
uses only the input at r+1 and r. The subdiagonal is t(A-r-1/2), which
never vanishes for integer A,r and nonzero t. Starting at the actual
highest vector, the preterminal zero equations therefore force every
top coordinate before resonance to be nonzero. At resonance the diagonal
vanishes, leaving a nonzero output coordinate.

Together with the Ward equations proved earlier this gives genuine
nonzero singular Verma states on every (A,2) curve for nonreal t. It does
not assert rational specialization, vacuum survival or minimal-model rigidity.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- An integer difference cannot be a half-integer. This elementary
arithmetic is the entire nonvanishing input for the subdiagonal. -/
theorem fusionThree_half_ne_zero (A r : ℕ) : (A:ℂ)-(r:ℂ)-1/2≠0 := by
  intro hz
  have he : (2:ℂ)*(A:ℂ)=2*(r:ℂ)+1 := by linear_combination 2*hz
  have hn : 2*A=2*r+1 := by exact_mod_cast he
  omega

/-- Every preterminal top coordinate in the actual constructed sequence
is nonzero on the (A,2) curve. The argument uses the actual zero source
equations, rather than assuming a scalar solution. -/
theorem fusionKernelTop_three_ne_zero (A : ℕ) (t : ℂ) (him : t.im≠0)
    (r : ℕ) (hr : r<A*2) : fusionKernelTop A 3 t him (by omega) r≠0 := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  induction r with
  | zero => simp
  | succ r ih =>
    have hb := fusionKernelTop_source_below A 3 t him (by omega) (r+1) (by simpa using hr)
    norm_num only [Nat.cast_ofNat,show (3:ℂ)-1=2 by norm_num] at hb
    rw [wardBSATopSource_label_three A t ht] at hb
    intro hz
    rw [hz,mul_zero,zero_add] at hb
    exact (mul_ne_zero (mul_ne_zero ht (fusionThree_half_ne_zero A r)) (ih (by omega))) hb

/-- The top PBW coordinate of the terminal source is nonzero at seed
index three. At level 2A its diagonal disappears and its subdiagonal
multiplies the already nonzero coordinate at 2A-1. -/
theorem fusionTerminalState_three_top_ne_zero (A : ℕ) (t : ℂ) (him : t.im≠0)
    (hA : 0<A) :
    vermaTopCoordinate (vermaBSACharge t) (fusionKacWeight (A:ℂ) (((3:ℕ):ℂ)-1) t)
      (A*(3-1)) (fusionTerminalState A 3 t him (by omega)).val≠0 := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  rw [fusionTerminalState_top A 3 t him (by omega)]
  have he : A*(3-1)=(A*2-1)+1 := by omega
  rw [he]
  norm_num only [show (3:ℂ)-1=2 by norm_num]
  rw [wardBSATopSource_label_three A t ht]
  have hd := wardBSASourceDiagonal_label_terminal A 3 t (by omega) ht
  norm_num only [Nat.cast_ofNat,show (3:ℂ)-1=2 by norm_num] at hd
  have hi : A*2-1+1=A*(3-1) := by omega
  rw [hi,hd,zero_mul,zero_add]
  exact mul_ne_zero (mul_ne_zero ht (fusionThree_half_ne_zero A (A*2-1)))
    (fusionKernelTop_three_ne_zero A t him (A*2-1) (by omega))

/-- The actual terminal fusion output is nonzero for every positive A
and nonreal parameter on the (A,2) curve. This is vector nonvanishing,
not merely the nonvanishing of the input sequence. -/
theorem fusionTerminalState_three_ne_zero (A : ℕ) (t : ℂ) (him : t.im≠0)
    (hA : 0<A) : (fusionTerminalState A 3 t him (by omega)).val≠0 := by
  intro hz
  have hh := fusionTerminalState_three_top_ne_zero A t him hA
  rw [hz,map_zero] at hh
  exact hh rfl

/-- Every (A,2) Verma curve has an actual nonzero level-2A singular state
at every nonreal parameter. The positive-mode and weight assertions are
in the same actual Verma module as the proved nonzero vector. -/
theorem fusionThree_nonzero_highest (A : ℕ) (t : ℂ) (him : t.im≠0) (hA : 0<A) :
    ∃ v : sortedSpan (vermaBSACharge t) (fusionKacWeight (A:ℂ) (((3:ℕ):ℂ)-1) t) (A*(3-1)),
      v.val≠0 ∧
      (∀ m : ℤ, 0<m → vermaMode (vermaBSACharge t)
        (fusionKacWeight (A:ℂ) (((3:ℕ):ℂ)-1) t) m v.val=0) ∧
      vermaMode (vermaBSACharge t) (fusionKacWeight (A:ℂ) (((3:ℕ):ℂ)-1) t) 0 v.val=
        (fusionKacWeight (A:ℂ) (((3:ℕ):ℂ)-1) t+((A*(3-1):ℕ):ℂ)) • v.val :=
  ⟨fusionTerminalState A 3 t him (by omega),fusionTerminalState_three_ne_zero A t him hA,
    fusionTerminalState_positive A 3 t him hA (by omega),
    fusionTerminalState_weight A 3 t him (by omega)⟩

end VOA.InverseDS.VirasoroVerma
