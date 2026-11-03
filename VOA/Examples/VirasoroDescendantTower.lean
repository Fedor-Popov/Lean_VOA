/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroDescendantWard

/-!
# Generating all negative descendants from the first two

The recursion D_(k+1)=[D_1,D_k]/(k-1) is studied in an arbitrary complex
Lie algebra. The grading and two positive commutators follow from the
four initial Ward identities and Jacobi. This algebraic step does not
assert the remaining negative-mode relations or construct a fusion state.
-/
namespace VOA.DescendantTower
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- Term n represents negative mode n+2. The denominator is always positive,
so the construction has no singular terminal division. -/
noncomputable def tower (A B : L) : ℕ → L
  | 0 => B
  | n+1 => ((n:ℂ)+1)⁻¹ • ⁅A,tower A B n⁆

/-- The initial member is the prescribed second negative operator. -/
@[simp] theorem tower_zero (A B : L) : tower A B 0=B := rfl

/-- The defining recursion without division, convenient in commutators. -/
theorem bracket_tower (A B : L) (n : ℕ) :
    ⁅A,tower A B n⁆=((n:ℂ)+1) • tower A B (n+1) := by
  rw [tower,smul_smul,mul_inv_cancel₀ (by exact_mod_cast (Nat.succ_ne_zero n) : (n:ℂ)+1≠0),one_smul]

/-- If the first two operators have weights one and two, every generated
operator has its expected weight n+2. -/
theorem weight_tower (H A B : L) (hA : ⁅H,A⁆=A) (hB : ⁅H,B⁆=(2:ℂ) • B) (n : ℕ) :
    ⁅H,tower A B n⁆=((n:ℂ)+2) • tower A B n := by
  induction n with
  | zero => simpa using hB
  | succ n ih =>
    rw [tower,lie_smul,leibniz_lie,hA,ih,lie_smul]
    simp only [Nat.cast_add,Nat.cast_one]
    module

/-- The first positive operator has the correct commutator with every
negative operator of index at least three. Only Jacobi and the initial
weight/commutator equations are used. -/
theorem positive1_tower (H P A B : L)
    (hA : ⁅H,A⁆=A) (hB : ⁅H,B⁆=(2:ℂ) • B)
    (pA : ⁅P,A⁆=(2:ℂ) • H) (pB : ⁅P,B⁆=(3:ℂ) • A) (n : ℕ) :
    ⁅P,tower A B (n+1)⁆=((n:ℂ)+4) • tower A B n := by
  induction n with
  | zero =>
    simp only [tower,Nat.cast_zero,zero_add,inv_one,one_smul,leibniz_lie,pA,pB,
      smul_lie,lie_smul,hB,lie_self,smul_zero,add_zero,smul_smul]
    norm_num
  | succ n ih =>
    rw [tower,lie_smul,leibniz_lie,pA,smul_lie,weight_tower H A B hA hB,ih,
      lie_smul,bracket_tower A B n]
    simp only [Nat.cast_add,Nat.cast_one,smul_smul,← add_smul]
    congr 1
    field_simp [show (n:ℂ)+1+1≠0 by exact_mod_cast (by omega : n+1+1≠0)]
    <;> ring

/-- The next positive commutator at index three is five times D1. The
central contribution disappears because it commutes with D1. -/
theorem positive2_tower_one (H P Q A B Z : L)
    (hA : ⁅H,A⁆=A) (pB : ⁅P,B⁆=(3:ℂ) • A)
    (qA : ⁅Q,A⁆=(3:ℂ) • P) (qB : ⁅Q,B⁆=(4:ℂ) • H+Z)
    (aZ : ⁅A,Z⁆=0) : ⁅Q,tower A B 1⁆=(5:ℂ) • A := by
  have aH : ⁅A,H⁆ = -A := by rw [← lie_skew,hA]
  simp only [tower,Nat.cast_zero,zero_add,inv_one,one_smul,leibniz_lie,qA,qB,
    smul_lie,lie_add,lie_smul,pB,aH,aZ,add_zero]
  module

/-- The second positive operator has the correct commutator with every
negative operator of index at least four. The central term is needed only
at the initial second operator; no higher central term survives. -/
theorem positive2_tower (H P Q A B Z : L)
    (hA : ⁅H,A⁆=A) (hB : ⁅H,B⁆=(2:ℂ) • B)
    (pA : ⁅P,A⁆=(2:ℂ) • H) (pB : ⁅P,B⁆=(3:ℂ) • A)
    (qA : ⁅Q,A⁆=(3:ℂ) • P) (qB : ⁅Q,B⁆=(4:ℂ) • H+Z)
    (aZ : ⁅A,Z⁆=0) (n : ℕ) :
    ⁅Q,tower A B (n+2)⁆=((n:ℂ)+6) • tower A B n := by
  induction n with
  | zero =>
    rw [show tower A B 2=(2:ℂ)⁻¹ • ⁅A,tower A B 1⁆ by simp only [tower,Nat.cast_one]; norm_num,lie_smul,leibniz_lie,qA,smul_lie,
      positive1_tower H P A B hA hB pA pB 0,
      positive2_tower_one H P Q A B Z hA pB qA qB aZ,lie_smul,lie_self]
    simp only [Nat.cast_one,Nat.cast_zero,zero_add,smul_zero,add_zero,smul_smul]
    norm_num
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,tower,lie_smul,leibniz_lie,qA,smul_lie,
      positive1_tower H P A B hA hB pA pB (n+1),ih,lie_smul,bracket_tower A B n]
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,smul_smul,← add_smul]
    congr 1
    field_simp [show (n:ℂ)+2+1≠0 by exact_mod_cast (by omega : n+2+1≠0)]
    <;> ring
end VOA.DescendantTower
