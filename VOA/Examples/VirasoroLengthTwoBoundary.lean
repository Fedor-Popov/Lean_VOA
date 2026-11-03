/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroLengthTwoNorm
import VOA.Examples.VirasoroLengthTwoSpanning
import VOA.Examples.VirasoroLengthTwoQuotient
import VOA.Examples.VirasoroGradedUnitarity

/-!
# Length-two graded unitarity for boundary Virasoro models

This file descends the metric-independent universal tower basis to the simple boundary quotient.
It deliberately does not use Salazar's full admissible-basis theorem: in word length at most two,
the exact universal tower basis and the canonical norms detect every possible quotient loss.

The resulting quotient basis, orthogonality, and strict diagonal sign package are unconditional.
They are the algebraic content of graded unitarity through length two.  The final public
`LayerPositive` predicate additionally requires a `RealStructure` on the simple quotient.  That
structure is constructed downstream in `VirasoroBoundaryRealStructure`, and the bounded theorem
is assembled in `VirasoroLengthTwoLayerPositive`; this lower-level file does not import either one.
-/

set_option linter.style.longLine false

namespace VOA

namespace VirGradedUnitarity

open VOA.VirModule VOA.VirSimple VOA.VirGoodFil
open VOA.VirQuotForm VOA.VertexOperatorAlgebra

/-- The boundary minimal-model central charge, embedded in `ℂ`. -/
def boundaryCharge (n : ℕ) : ℂ := (boundaryMinimalCentralCharge n : ℂ)

/-- The first nontrivial boundary label has central charge −22/5, the Lee–Yang value. -/
@[simp] theorem boundaryCharge_two : boundaryCharge 2 = -(22 / 5 : ℂ) := by
  norm_num [boundaryCharge, boundaryMinimalCentralCharge]

/-- Identify the boundary-charge formula at label two with the named Lee–Yang charge, so its quotient relations can be reused without a normalization change. -/
theorem boundaryCharge_two_eq_leeYangC : boundaryCharge 2 = LeeYang.leeYangC := by
  norm_num [boundaryCharge, boundaryMinimalCentralCharge, LeeYang.leeYangC]

/-- Every nontrivial boundary charge is strictly negative. -/
theorem boundaryMinimalCentralCharge_neg (n : ℕ) (hn : 2 ≤ n) :
    boundaryMinimalCentralCharge n < 0 := by
  have h := neg_boundaryMinimalCentralCharge_sub_twentyTwo_fifths_nonneg n hn
  linarith

/-- Strict form of `rho_m ≤ 22/5` away from its unique initial index. -/
theorem lengthTwoRho_lt_twentyTwo_fifths (m : ℕ) (hm : 3 ≤ m) :
    lengthTwoRho m < 22 / 5 := by
  induction m, hm using Nat.le_induction with
  | base => simpa using lengthTwoRho_succ_lt 2 (by omega)
  | succ m hm ih => exact (lengthTwoRho_succ_lt m (by omega)).trans ih

/-- For `n>2`, the boundary charge lies strictly below the Lee--Yang charge. -/
theorem boundaryMinimalCentralCharge_lt_leeYang (n : ℕ) (hn : 3 ≤ n) :
    boundaryMinimalCentralCharge n < -(22 / 5) := by
  have heq := neg_boundaryMinimalCentralCharge_sub_twentyTwo_fifths n
  have hnQ : (3 : ℚ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (5 : ℚ) * (2 * n + 1) := by positivity
  have hn2 : (0 : ℚ) < n - 2 := by linarith
  have hnum : 0 < (6 : ℚ) * (n - 2) * (10 * n + 1) := by positivity
  have hpos : 0 < 6 * ((n : ℚ) - 2) * (10 * n + 1) / (5 * (2 * n + 1)) :=
    div_pos hnum hden
  linarith

/-- The second factor in the length-two norm is strictly negative except at the unique
Lee--Yang vector `n=m=2`. -/
theorem boundaryMinimalCentralCharge_add_lengthTwoRho_neg
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hex : n ≠ 2 ∨ m ≠ 2) :
    boundaryMinimalCentralCharge n + lengthTwoRho m < 0 := by
  rcases eq_or_lt_of_le hn with rfl | hn'
  · have hmne : m ≠ 2 := by tauto
    have hm3 : 3 ≤ m := by omega
    norm_num [boundaryMinimalCentralCharge]
    have hrQ := lengthTwoRho_lt_twentyTwo_fifths m hm3
    linarith
  · have hcQ := boundaryMinimalCentralCharge_lt_leeYang n (by omega)
    have hrQ := lengthTwoRho_le_twentyTwo_fifths m hm
    linarith

/-- The rational scalar occurring in the boundary norm formula. -/
def boundaryLengthTwoBaseNorm (n m : ℕ) : ℚ :=
  (1 / 2) * Nat.choose (4 * m - 2) (2 * m - 4) * boundaryMinimalCentralCharge n *
    (boundaryMinimalCentralCharge n + lengthTwoRho m)

/-- The rational boundary norm is positive precisely away from the unique Lee--Yang deletion. -/
theorem boundaryLengthTwoBaseNorm_pos (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hex : n ≠ 2 ∨ m ≠ 2) : 0 < boundaryLengthTwoBaseNorm n m := by
  have hchooseNat : 0 < Nat.choose (4 * m - 2) (2 * m - 4) :=
    Nat.choose_pos (by omega)
  have hchoose : (0 : ℚ) < Nat.choose (4 * m - 2) (2 * m - 4) := by exact_mod_cast hchooseNat
  have hc := boundaryMinimalCentralCharge_neg n hn
  have hsum := boundaryMinimalCentralCharge_add_lengthTwoRho_neg n m hn hm hex
  have hfirst : 0 < (1 / 2 : ℚ) * Nat.choose (4 * m - 2) (2 * m - 4) := by positivity
  have hneg : (1 / 2 : ℚ) * Nat.choose (4 * m - 2) (2 * m - 4) *
      boundaryMinimalCentralCharge n < 0 := mul_neg_of_pos_of_neg hfirst hc
  simpa only [boundaryLengthTwoBaseNorm] using mul_pos_of_neg_of_neg hneg hsum

/-- The complex canonical norm is the embedding of the rational boundary norm. -/
theorem canB_boundary_lengthTwoQ_self (n m : ℕ) (hm : 2 ≤ m) :
    (VirGram4.canB (boundaryCharge n)).form
      (lengthTwoQ (boundaryCharge n) m) (lengthTwoQ (boundaryCharge n) m) =
        (boundaryLengthTwoBaseNorm n m : ℂ) := by
  rw [canB_lengthTwoQ_self (boundaryCharge n) m hm]
  simp only [boundaryCharge, boundaryLengthTwoBaseNorm]
  push_cast
  ring

/-- The closed universal norm is strictly positive at every surviving boundary length-two base. -/
theorem canB_boundary_lengthTwoQ_self_pos (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hex : n ≠ 2 ∨ m ≠ 2) :
    0 < ((VirGram4.canB (boundaryCharge n)).form
      (lengthTwoQ (boundaryCharge n) m) (lengthTwoQ (boundaryCharge n) m)).re := by
  rw [canB_boundary_lengthTwoQ_self n m hm]
  exact_mod_cast boundaryLengthTwoBaseNorm_pos n m hn hm hex

/-- The same norm is nonzero, in the exact scalar form needed for quotient survival. -/
theorem canB_boundary_lengthTwoQ_self_ne_zero (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hex : n ≠ 2 ∨ m ≠ 2) :
    (VirGram4.canB (boundaryCharge n)).form
      (lengthTwoQ (boundaryCharge n) m) (lengthTwoQ (boundaryCharge n) m) ≠ 0 := by
  intro hzero
  have hpos := canB_boundary_lengthTwoQ_self_pos n m hn hm hex
  rw [hzero, Complex.zero_re] at hpos
  exact (lt_irrefl 0) hpos

/-- Every nontrivial boundary charge is nonzero because it is strictly negative. This prevents the stress-tensor norm from vanishing. -/
theorem boundaryCharge_ne_zero (n : ℕ) (hn : 2 ≤ n) : boundaryCharge n ≠ 0 := by
  have hq : boundaryMinimalCentralCharge n ≠ 0 := ne_of_lt (boundaryMinimalCentralCharge_neg n hn)
  intro hzero
  have hzero' : boundaryMinimalCentralCharge n = 0 := by
    change ((boundaryMinimalCentralCharge n : ℂ) = 0) at hzero
    exact_mod_cast hzero
  exact hq hzero'

/-! ## The retained quotient tower family -/

/-- The tower indices which survive in the boundary simple quotient.  The only deletion is
`m=2` in the Lee--Yang model `n=2`. -/
def BoundaryLengthLETwoTowerIndex (n N : ℕ) :=
  {m : LengthLETwoTowerIndex N // n ≠ 2 ∨ m.1 ≠ 2}

/-- Equality of retained tower indices is decidable by comparing their underlying finite tower labels. -/
instance (n N : ℕ) : DecidableEq (BoundaryLengthLETwoTowerIndex n N) :=
  Subtype.instDecidableEq

/-- At fixed weight there are finitely many retained towers: filter the universal finite index set by the single Lee–Yang deletion rule. -/
noncomputable instance (n N : ℕ) : Fintype (BoundaryLengthLETwoTowerIndex n N) :=
  Fintype.subtype
    ((Finset.univ : Finset (LengthLETwoTowerIndex N)).filter fun m => n ≠ 2 ∨ m.1 ≠ 2) (by
      intro m
      simp)

/-- The length-one tower in the simple boundary quotient. -/
noncomputable def boundaryLengthOneTowerAt (n N : ℕ) :
    VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n) :=
  ((virasoroSimple (boundaryCharge n)).L (-1) ^ (N - 2))
    (virasoroSimple (boundaryCharge n)).conformalVector

/-- The retained family of quotient towers in final weight `N`. -/
noncomputable def boundaryLengthLETwoTowerAt (n N : ℕ)
    (m : BoundaryLengthLETwoTowerIndex n N) :
    VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n) :=
  if hm : m.1.1 = 1 then boundaryLengthOneTowerAt n N
  else ((virasoroSimple (boundaryCharge n)).L (-1) ^ (N - 2 * m.1.1))
    (lengthTwoQSimple (boundaryCharge n) m.1.1)

/-- The quotient map intertwines every power of a Virasoro mode. -/
theorem mkQ_L_pow (c : ℂ) (k : ℤ) (r : ℕ) (x : VirUniv c) :
    (maxIdealVir c).mkQ (((virasoroVOA c).L k ^ r) x) =
      ((virasoroSimple c).L k ^ r) ((maxIdealVir c).mkQ x) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, mkQ_L, ih]

/-- Each retained simple tower is literally the quotient image of its universal counterpart. -/
theorem boundaryLengthLETwoTowerAt_eq_mkQ (n N : ℕ)
    (m : BoundaryLengthLETwoTowerIndex n N) :
    boundaryLengthLETwoTowerAt n N m =
      (maxIdealVir (boundaryCharge n)).mkQ
        (lengthLETwoTowerAt (boundaryCharge n) N m.1) := by
  by_cases hm : m.1.1 = 1
  · rw [boundaryLengthLETwoTowerAt, dif_pos hm, lengthLETwoTowerAt, dif_pos hm,
      boundaryLengthOneTowerAt, lengthOneTowerAt, mkQ_L_pow]
    rfl
  · have hm2 : 2 ≤ m.1.1 := by have := m.1.2.1; omega
    rw [boundaryLengthLETwoTowerAt, dif_neg hm,
      lengthLETwoTowerAt_of_two_le (boundaryCharge n) m.1 hm2,
      lengthTwoTowerAt, lengthTwoQSimple, mkQ_L_pow]

/-- The simple stress-tensor tower is a nonzero `L₋₁L₁` eigenvector. -/
theorem boundaryLengthOneTowerAt_hasEigenvector (n N : ℕ) (hn : 2 ≤ n) :
    (globalTowerOperator (virasoroSimple (boundaryCharge n))).HasEigenvector
      (globalTowerEigenvalue 2 (N - 2)) (boundaryLengthOneTowerAt n N) := by
  exact globalDescendant_hasEigenvector (virasoroSimple (boundaryCharge n))
    (m := (2 : ℤ)) (v := (virasoroSimple (boundaryCharge n)).conformalVector) (by omega)
    ((virasoroSimple (boundaryCharge n)).conformalVector_mem_grading_two)
    (L1_conformal_zero (virasoroSimple (boundaryCharge n)))
    (virasoroSimple_conformalVector_ne_zero (boundaryCharge n)
      (boundaryCharge_ne_zero n hn)) (N - 2)

/-- A surviving simple `Q_{2m}` tower is a nonzero `L₋₁L₁` eigenvector. -/
theorem boundaryLengthTwoTowerAt_hasEigenvector (n N m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hmN : 2 * m ≤ N) (hex : n ≠ 2 ∨ m ≠ 2) :
    (globalTowerOperator (virasoroSimple (boundaryCharge n))).HasEigenvector
      (globalTowerEigenvalue (2 * m) (N - 2 * m))
      (((virasoroSimple (boundaryCharge n)).L (-1) ^ (N - 2 * m))
        (lengthTwoQSimple (boundaryCharge n) m)) := by
  have hbase : lengthTwoQSimple (boundaryCharge n) m ≠ 0 :=
    lengthTwoQSimple_ne_zero_of_canB_self_ne_zero (boundaryCharge n) m
      (canB_boundary_lengthTwoQ_self_ne_zero n m hn hm hex)
  have hgr : lengthTwoQSimple (boundaryCharge n) m ∈
      (virasoroSimple (boundaryCharge n)).grading (2 * m : ℤ) := by
    apply goodFil_le_grading (boundaryCharge n) 2 (2 * m : ℤ)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      lengthTwoQSimple_mem_goodFil (boundaryCharge n) m hm
  exact globalDescendant_hasEigenvector (virasoroSimple (boundaryCharge n))
    (m := (2 * m : ℕ)) (v := lengthTwoQSimple (boundaryCharge n) m) (by omega)
    hgr (lengthTwoQSimple_quasiPrimary (boundaryCharge n) m hm) hbase (N - 2 * m)

/-- Each retained quotient tower is a nonzero `L₋₁L₁` eigenvector. -/
theorem boundaryLengthLETwoTowerAt_hasEigenvector (n N : ℕ) (hn : 2 ≤ n)
    (m : BoundaryLengthLETwoTowerIndex n N) :
    (globalTowerOperator (virasoroSimple (boundaryCharge n))).HasEigenvector
      (lengthLETwoTowerEigenvalue N m.1) (boundaryLengthLETwoTowerAt n N m) := by
  by_cases hm : m.1.1 = 1
  · rw [boundaryLengthLETwoTowerAt, dif_pos hm, boundaryLengthOneTowerAt,
      ← globalTowerEigenvalue_eq_lengthLETwoTowerEigenvalue N m.1]
    simpa only [hm] using boundaryLengthOneTowerAt_hasEigenvector n N hn
  · have hm1 : 1 ≤ m.1.1 := m.1.2.1
    have hm2 : 2 ≤ m.1.1 := by omega
    rw [boundaryLengthLETwoTowerAt, dif_neg hm,
      ← globalTowerEigenvalue_eq_lengthLETwoTowerEigenvalue N m.1]
    exact boundaryLengthTwoTowerAt_hasEigenvector n N m.1.1 hn hm2 m.1.2.2 m.2

/-- The retained quotient tower family is linearly independent. -/
theorem boundaryLengthLETwoTowerAt_linearIndependent (n N : ℕ) (hn : 2 ≤ n) :
    LinearIndependent ℂ (boundaryLengthLETwoTowerAt n N) := by
  exact (globalTowerOperator (virasoroSimple (boundaryCharge n))).eigenvectors_linearIndependent'
    (fun m : BoundaryLengthLETwoTowerIndex n N => lengthLETwoTowerEigenvalue N m.1)
    ((lengthLETwoTowerEigenvalue_injective N).comp Subtype.coe_injective)
    (boundaryLengthLETwoTowerAt n N) (boundaryLengthLETwoTowerAt_hasEigenvector n N hn)

/-- Every retained quotient tower is a nonzero vector. The earlier eigenvector construction includes nonvanishing, so the deletion rule has removed all possible losses in this family. -/
theorem boundaryLengthLETwoTowerAt_ne_zero (n N : ℕ) (hn : 2 ≤ n)
    (m : BoundaryLengthLETwoTowerIndex n N) : boundaryLengthLETwoTowerAt n N m ≠ 0 :=
  (boundaryLengthLETwoTowerAt_hasEigenvector n N hn m).2

/-- The one omitted universal tower maps to zero: it is exactly the Lee--Yang `Q₄` tower. -/
theorem mkQ_lengthLETwoTowerAt_eq_zero_of_deleted (n N : ℕ)
    (m : LengthLETwoTowerIndex N) (hdel : ¬(n ≠ 2 ∨ m.1 ≠ 2)) :
    (maxIdealVir (boundaryCharge n)).mkQ
      (lengthLETwoTowerAt (boundaryCharge n) N m) = 0 := by
  have hn : n = 2 := by tauto
  have hm : m.1 = 2 := by tauto
  subst n
  have hm2 : 2 ≤ m.1 := by omega
  rw [lengthLETwoTowerAt_of_two_le (boundaryCharge 2) m hm2, lengthTwoTowerAt,
    mkQ_L_pow, boundaryCharge_two_eq_leeYangC]
  simpa [hm] using LeeYang.lengthTwoQSimple_two_tower_eq_zero (N - 2 * m.1)

/-- The retained quotient towers span the full length-at-most-two filtration step.  No character
or admissible-basis theorem is used. -/
theorem goodFil_two_eq_span_boundaryTowers (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    goodFil (boundaryCharge n) 2 (N : ℤ) =
      Submodule.span ℂ (Set.range (boundaryLengthLETwoTowerAt n N)) := by
  apply le_antisymm
  · rw [goodFil, virFil_two_eq_span_towers (boundaryCharge n) N hN,
      Submodule.map_span, Submodule.span_le]
    rintro y ⟨x, ⟨m, rfl⟩, rfl⟩
    by_cases hkeep : n ≠ 2 ∨ m.1 ≠ 2
    · apply Submodule.subset_span
      exact ⟨⟨m, hkeep⟩, boundaryLengthLETwoTowerAt_eq_mkQ n N ⟨m, hkeep⟩⟩
    · rw [mkQ_lengthLETwoTowerAt_eq_zero_of_deleted n N m hkeep]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    rw [boundaryLengthLETwoTowerAt_eq_mkQ, goodFil]
    exact ⟨lengthLETwoTowerAt (boundaryCharge n) N m.1,
      lengthLETwoTowerAt_mem_virFil (boundaryCharge n) N m.1, rfl⟩

/-- The retained towers, packaged as a basis of the simple length-two filtration step. -/
noncomputable def boundaryGoodFilTwoTowerBasis (n N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) :
    Module.Basis (BoundaryLengthLETwoTowerIndex n N) ℂ
      (goodFil (boundaryCharge n) 2 (N : ℤ)) :=
  (Module.Basis.span (boundaryLengthLETwoTowerAt_linearIndependent n N hn)).map
    (LinearEquiv.ofEq _ _ (goodFil_two_eq_span_boundaryTowers n N hn hN).symm)

/-! ## Orthogonality and exact diagonal signs -/

/-- `L₋₁L₁` is self-adjoint for every invariant form. -/
theorem globalTowerOperator_selfAdjoint {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (B : InvariantForm W) (x y : V) :
    B.form (globalTowerOperator W x) y = B.form x (globalTowerOperator W y) := by
  rw [globalTowerOperator, Module.End.mul_apply, Module.End.mul_apply,
    B.virasoro_adj (-1), B.virasoro_adj 1, neg_neg]

/-- Distinct retained towers are mutually orthogonal for the simple canonical form. -/
theorem Bsimp_boundaryLengthLETwoTowerAt_orthogonal (n N : ℕ) (hn : 2 ≤ n)
    (i j : BoundaryLengthLETwoTowerIndex n N) (hij : i ≠ j) :
    (Bsimp (boundaryCharge n)).form (boundaryLengthLETwoTowerAt n N i)
      (boundaryLengthLETwoTowerAt n N j) = 0 := by
  let A := globalTowerOperator (virasoroSimple (boundaryCharge n))
  let vi := boundaryLengthLETwoTowerAt n N i
  let vj := boundaryLengthLETwoTowerAt n N j
  let ei := lengthLETwoTowerEigenvalue N i.1
  let ej := lengthLETwoTowerEigenvalue N j.1
  have hi := (boundaryLengthLETwoTowerAt_hasEigenvector n N hn i).apply_eq_smul
  have hj := (boundaryLengthLETwoTowerAt_hasEigenvector n N hn j).apply_eq_smul
  have he : ei ≠ ej := by
    intro heq
    apply hij
    apply Subtype.ext
    exact lengthLETwoTowerEigenvalue_injective N heq
  have hadj := globalTowerOperator_selfAdjoint (virasoroSimple (boundaryCharge n))
    (Bsimp (boundaryCharge n)) vi vj
  change (Bsimp (boundaryCharge n)).form (A vi) vj =
    (Bsimp (boundaryCharge n)).form vi (A vj) at hadj
  rw [hi, hj, map_smul (Bsimp (boundaryCharge n)).form ei vi,
    map_smul ((Bsimp (boundaryCharge n)).form vi) ej vj] at hadj
  simp only [LinearMap.smul_apply, smul_eq_mul] at hadj
  have hprod : (ei - ej) * (Bsimp (boundaryCharge n)).form vi vj = 0 := by
    linear_combination hadj
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr he)

/-- Exact diagonal formula for the retained quotient tower basis. -/
theorem Bsimp_boundaryLengthLETwoTowerAt_self (n N : ℕ) (hn : 2 ≤ n)
    (m : BoundaryLengthLETwoTowerIndex n N) :
    (Bsimp (boundaryCharge n)).form (boundaryLengthLETwoTowerAt n N m)
      (boundaryLengthLETwoTowerAt n N m) =
        if hm : m.1.1 = 1 then
          globalDescendantFactor 2 (N - 2) * (boundaryCharge n / 2)
        else globalDescendantFactor (2 * m.1.1) (N - 2 * m.1.1) *
          (boundaryLengthTwoBaseNorm n m.1.1 : ℂ) := by
  rw [boundaryLengthLETwoTowerAt_eq_mkQ, canB_quot_mkQ]
  by_cases hm : m.1.1 = 1
  · have hT : (VirGram4.canB (boundaryCharge n)).form
        (omegaVir (boundaryCharge n)) (omegaVir (boundaryCharge n)) = boundaryCharge n / 2 := by
      change (VirGram4.canB (boundaryCharge n)).form
        (LeeYang.L2vac (boundaryCharge n)) (LeeYang.L2vac (boundaryCharge n)) = _
      exact VirGram4.canB_L2_L2 (boundaryCharge n)
    rw [dif_pos hm, lengthLETwoTowerAt, dif_pos hm, lengthOneTowerAt,
      (VirGram4.canB (boundaryCharge n)).form_globalDescendant
        (omegaVir (boundaryCharge n))
        (omegaVir_mem_gradingVir_two (boundaryCharge n))]
    · rw [hT, smul_eq_mul]
    · simpa [virasoroVOA_L_eq_Lop] using
        L1_conformal_zero (virasoroVOA (boundaryCharge n))
  · have hm1 : 1 ≤ m.1.1 := m.1.2.1
    have hm2 : 2 ≤ m.1.1 := by omega
    rw [dif_neg hm, lengthLETwoTowerAt_of_two_le (boundaryCharge n) m.1 hm2,
      lengthTwoTowerAt,
      form_lengthTwoQ_tower (boundaryCharge n) (VirGram4.canB (boundaryCharge n)) m.1.1 hm2,
      canB_boundary_lengthTwoQ_self n m.1.1 hm2, smul_eq_mul]

/-- Odd (`m=1`) and even (`m≥2`) retained towers have the required strict diagonal signs. -/
theorem Bsimp_boundaryLengthLETwoTowerAt_self_sign (n N : ℕ) (hn : 2 ≤ n)
    (m : BoundaryLengthLETwoTowerIndex n N) :
    if hm : m.1.1 = 1 then
      ∃ r : ℝ, 0 < r ∧
        (Bsimp (boundaryCharge n)).form (boundaryLengthLETwoTowerAt n N m)
          (boundaryLengthLETwoTowerAt n N m) = -(r : ℂ)
    else
      ∃ r : ℝ, 0 < r ∧
        (Bsimp (boundaryCharge n)).form (boundaryLengthLETwoTowerAt n N m)
          (boundaryLengthLETwoTowerAt n N m) = (r : ℂ) := by
  by_cases hm : m.1.1 = 1
  · rw [dif_pos hm]
    obtain ⟨a, ha, hfactor⟩ := globalDescendantFactor_real_pos (m := (2 : ℤ)) (by omega) (N - 2)
    let r : ℝ := a * (-(boundaryMinimalCentralCharge n : ℝ) / 2)
    have hc : (boundaryMinimalCentralCharge n : ℝ) < 0 := by
      exact_mod_cast boundaryMinimalCentralCharge_neg n hn
    refine ⟨r, ?_, ?_⟩
    · dsimp [r]
      exact mul_pos ha (div_pos (neg_pos.mpr hc) (by norm_num))
    rw [Bsimp_boundaryLengthLETwoTowerAt_self n N hn m, dif_pos hm, hfactor]
    dsimp [r, boundaryCharge]
    push_cast
    ring
  · rw [dif_neg hm]
    have hm1 : 1 ≤ m.1.1 := m.1.2.1
    have hm2 : 2 ≤ m.1.1 := by omega
    obtain ⟨a, ha, hfactor⟩ := globalDescendantFactor_real_pos
      (m := 2 * (m.1.1 : ℤ)) (by omega) (N - 2 * m.1.1)
    let r : ℝ := a * (boundaryLengthTwoBaseNorm n m.1.1 : ℝ)
    have hr : (0 : ℝ) < (boundaryLengthTwoBaseNorm n m.1.1 : ℝ) := by
      exact_mod_cast boundaryLengthTwoBaseNorm_pos n m.1.1 hn hm2 m.2
    refine ⟨r, by dsimp [r]; positivity, ?_⟩
    rw [Bsimp_boundaryLengthLETwoTowerAt_self n N hn m, dif_neg hm, hfactor]
    dsimp [r]
    push_cast
    ring

/-- Every retained tower has nonzero canonical norm: the stress-tensor tower has a strictly negative real norm and the length-two towers have strictly positive real norms. -/
theorem Bsimp_boundaryLengthLETwoTowerAt_self_ne_zero (n N : ℕ) (hn : 2 ≤ n)
    (m : BoundaryLengthLETwoTowerIndex n N) :
    (Bsimp (boundaryCharge n)).form (boundaryLengthLETwoTowerAt n N m)
      (boundaryLengthLETwoTowerAt n N m) ≠ 0 := by
  by_cases hm : m.1.1 = 1
  · obtain ⟨r, hr, heq⟩ := dif_pos hm ▸ Bsimp_boundaryLengthLETwoTowerAt_self_sign n N hn m
    rw [heq]
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))
  · obtain ⟨r, hr, heq⟩ := dif_neg hm ▸ Bsimp_boundaryLengthLETwoTowerAt_self_sign n N hn m
    rw [heq]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hr)

end VirGradedUnitarity

end VOA
