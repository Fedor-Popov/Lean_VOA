/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSARecursion
import VOA.Examples.VirasoroDescendantIndependence

/-!
# Highest polynomial-degree terms of the vacuum BSA recursion

Translation preserves oscillator degree. All other negative modes raise it
by at most two. At even level r only L_(-2) applied to the level r-2 state
can contribute at degree r. This identifies the terminal leading term.
-/
namespace VOA.VirModule
open MvPolynomial (X)

/-- Translation differentiates a product of oscillator variables without
changing its number of factors, so it preserves the polynomial filtration. -/
theorem Lld_neg_one_mem_FDeg (lam : ℂ) {d : ℕ} {p : Fock} (hp : p ∈ FDeg d) :
    Lld lam (-1) p ∈ FDeg d := by
  have he : Lld lam (-1) = Lvir 1 (-1) := by simp [Lld]
  rw [he]
  have hh : ∀ l : List ℕ, Lvir 1 (-1) ((l.map X).prod : Fock) ∈ FDeg l.length := by
    intro l
    induction l with
    | nil => simpa [Lvir_one_vacuum] using (FDeg 0).zero_mem
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      have he := Lvir_neg_X 0 i ((l.map X).prod : Fock)
      norm_num at he
      rw [he]
      exact (FDeg _).add_mem
        ((FDeg _).smul_mem _ (mulX_mem_FDeg (i+1) (prod_mem_FDeg l)))
        (mulX_mem_FDeg i ih)
  induction hp using Submodule.span_induction with
  | mem y hy => obtain ⟨l,hl,rfl⟩ := hy; exact FDeg_mono hl (hh l)
  | zero => simp
  | add p q _ _ hp hq => simpa using (FDeg d).add_mem hp hq
  | smul a p _ hp => simpa using (FDeg d).smul_mem a hp

/-- Evaluation in Fock space commutes with the entire BSA source sum. -/
theorem fockMap_bsaSource {c lam : ℂ} (hlam : 1-12*lam^2=c) (N r : ℕ) :
    fockMap hlam (bsaSource c N r) =
      ∑ j : Fin r, Lld lam ((j:ℤ)-(r:ℤ)) (fockMap hlam (bsaState c N j)) := by
  simp only [bsaSource, map_sum, fockMap_Lop]

/-- Each intermediate state has oscillator degree at most its conformal level.
The translation summand is treated separately because its degree cost is zero. -/
theorem fockMap_bsaState_mem {c lam : ℂ} (hlam : 1-12*lam^2=c) (N r : ℕ) :
    fockMap hlam (bsaState c N r) ∈ FDeg r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : r=0
    · subst r
      simpa [bsaState_zero, vacVec, fockMap_mk] using one_mem_FDeg 0
    rw [bsaState_eq_source c N r (by omega), map_smul, fockMap_bsaSource]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro j hj
    have hp := ih j j.isLt
    by_cases he : j.val+1=r
    · rw [show (j:ℤ)-(r:ℤ) = -1 by omega]
      exact FDeg_mono (by omega) (Lld_neg_one_mem_FDeg lam hp)
    · have hle : j.val+2 ≤ r := by omega
      rw [show (j:ℤ)-(r:ℤ) = -((r-j.val-2:ℕ):ℤ)-2 by omega]
      exact FDeg_mono hle (Lld_mem_FDeg lam (r-j.val-2) hp)

/-- The source term two steps below the target is the only one which can
reach the target's full polynomial degree. All other summands have lower degree. -/
theorem fockMap_bsaSource_error {c lam : ℂ} (hlam : 1-12*lam^2=c) (N k : ℕ) :
    fockMap hlam (bsaSource c N (k+2)) -
      creationPoly 0 * fockMap hlam (bsaState c N k) ∈ FDeg (k+1) := by
  classical
  rw [fockMap_bsaSource]
  let j0 : Fin (k+2) := ⟨k,by omega⟩
  have hj0 : j0 ∈ (Finset.univ : Finset (Fin (k+2))) := Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ hj0]
  have he : Lld lam ((j0:ℤ)-((k+2:ℕ):ℤ)) (fockMap hlam (bsaState c N j0)) =
      Lld lam (-2) (fockMap hlam (bsaState c N k)) := by simp [j0]
  rw [he]
  have hs : ∀ a b d : Fock, a+b-d=(a-d)+b := by intros; ring
  rw [hs]
  apply Submodule.add_mem
  · simpa using errLd_mem lam 0 (fockMap_bsaState_mem hlam N k)
  · apply Submodule.sum_mem
    intro j hj
    have hjn : j.val ≠ k := by
      intro he
      exact (Finset.mem_erase.mp hj).1 (Fin.ext he)
    have hp := fockMap_bsaState_mem hlam N j
    by_cases he : j.val=k+1
    · rw [show (j:ℤ)-((k+2:ℕ):ℤ) = -1 by omega]
      exact FDeg_mono (by omega) (Lld_neg_one_mem_FDeg lam hp)
    · have hle : j.val+2 ≤ k+1 := by have := j.isLt; omega
      rw [show (j:ℤ)-((k+2:ℕ):ℤ) = -((k-j.val:ℕ):ℤ)-2 by have := j.isLt; omega]
      exact FDeg_mono hle (Lld_mem_FDeg lam (k-j.val) hp)

/-- The coefficient of the top power of the quadratic symbol, at even
intermediate levels. Only nonterminal denominators will be used for nonvanishing. -/
noncomputable def bsaTopCoefficient (N : ℕ) : ℕ → ℂ
  | 0 => 1
  | k+1 => (-bsaParameter N / (((2*(k+1):ℕ):ℂ)*((N:ℂ)-((2*(k+1):ℕ):ℂ)))) *
      bsaTopCoefficient N k


/-- A leading-term estimate at the previous even level propagates to the
next source. Every discarded summand has strictly smaller polynomial degree. -/
theorem bsaSource_top_of_state_top {c lam : ℂ} (hlam : 1-12*lam^2=c) (N k : ℕ)
    (hh : fockMap hlam (bsaState c N (2*k)) -
      bsaTopCoefficient N k • (creationPoly 0)^k ∈ FDeg (2*k-1)) :
    fockMap hlam (bsaSource c N (2*(k+1))) -
      bsaTopCoefficient N k • (creationPoly 0)^(k+1) ∈ FDeg (2*k+1) := by
  have he := fockMap_bsaSource_error hlam N (2*k)
  have hs : fockMap hlam (bsaSource c N (2*(k+1))) -
      bsaTopCoefficient N k • (creationPoly 0)^(k+1) =
      (fockMap hlam (bsaSource c N (2*k+2)) -
        creationPoly 0 * fockMap hlam (bsaState c N (2*k))) +
      creationPoly 0 * (fockMap hlam (bsaState c N (2*k)) -
        bsaTopCoefficient N k • (creationPoly 0)^k) := by
    rw [show 2*(k+1)=2*k+2 by omega, pow_succ]
    simp only [Algebra.smul_def]
    ring
  rw [hs]
  apply Submodule.add_mem _ he
  cases k with
  | zero => simp [bsaState_zero, vacVec, fockMap_mk, vacuum, bsaTopCoefficient]
  | succ k => exact FDeg_mono (by omega) (creationPoly_mul_mem 0 hh)

/-- At every even level the leading term is an explicit scalar times a power
of the quadratic creation symbol. The difference has strictly smaller degree. -/
theorem fockMap_bsaState_top {c lam : ℂ} (hlam : 1-12*lam^2=c) (N k : ℕ) :
    fockMap hlam (bsaState c N (2*k)) -
      bsaTopCoefficient N k • (creationPoly 0)^k ∈ FDeg (2*k-1) := by
  induction k with
  | zero => simp [bsaState_zero, vacVec, fockMap_mk, vacuum, bsaTopCoefficient]
  | succ k ih =>
    have hh := bsaSource_top_of_state_top hlam N k ih
    rw [bsaState_eq_source c N (2*(k+1)) (by omega), map_smul, bsaTopCoefficient]
    rw [mul_smul, ← smul_sub]
    simpa only [show 2*(k+1)-1=2*k+1 by omega] using (FDeg _).smul_mem _ hh

/-- The terminal source retains the previous state's leading coefficient;
there is no division by the zero terminal denominator. -/
theorem fockMap_bsaSource_top {c lam : ℂ} (hlam : 1-12*lam^2=c) (N k : ℕ) :
    fockMap hlam (bsaSource c N (2*(k+1))) -
      bsaTopCoefficient N k • (creationPoly 0)^(k+1) ∈ FDeg (2*k+1) :=
  bsaSource_top_of_state_top hlam N k (fockMap_bsaState_top hlam N k)

/-- Every factor in the leading coefficient is nonzero before the terminal
level. This is the step which distinguishes a singular vector from zero. -/
theorem bsaTopCoefficient_ne_zero (N k : ℕ) (hk : 2*k < N) :
    bsaTopCoefficient N k ≠ 0 := by
  induction k with
  | zero => simp [bsaTopCoefficient]
  | succ k ih =>
    rw [bsaTopCoefficient]
    apply mul_ne_zero
    · apply div_ne_zero
      · apply neg_ne_zero.mpr
        exact div_ne_zero (Nat.cast_add_one_ne_zero N) (by norm_num)
      · exact bsa_denominator_ne_zero N (2*(k+1)) (by omega) hk
    · exact ih (by omega)

/-- The explicit terminal BSA vector is nonzero at every even level, at any
central charge. Its Fock leading term has degree exactly the terminal level. -/
theorem bsaSource_even_ne_zero (c : ℂ) (k : ℕ) :
    bsaSource c (2*(k+1)) (2*(k+1)) ≠ 0 := by
  obtain ⟨lam,hlam⟩ := exists_lam c
  have hh := fockMap_bsaSource_top hlam (2*(k+1)) k
  have ha := bsaTopCoefficient_ne_zero (2*(k+1)) k (by omega)
  have hp : creationPoly 0 ≠ 0 := by
    intro hz
    have hn := tSub_creationPoly_ne_zero 2 0 (by omega)
    simpa [hz] using hn
  have hn : bsaTopCoefficient (2*(k+1)) k • (creationPoly 0)^(k+1) ≠ 0 :=
    smul_ne_zero ha (pow_ne_zero _ hp)
  have hom : (bsaTopCoefficient (2*(k+1)) k • (creationPoly 0)^(k+1)).IsHomogeneous
      (2*(k+1)) := by
    change _ ∈ MvPolynomial.homogeneousSubmodule ℕ ℂ (2*(k+1))
    exact Submodule.smul_mem _ _ ((creationPoly_isHomogeneous 0).pow (k+1))
  intro hz
  rw [hz, map_zero, zero_sub] at hh
  have hd := FDeg_totalDegree ((FDeg _).neg_mem hh)
  rw [neg_neg, hom.totalDegree hn] at hd
  omega

/-- The actual partition determinant has a root at every coprime M(2,q)
charge with odd q>=5. This is root existence, not a nonzero derivative or rigidity. -/
theorem partitionDeterminant_bsa_root (k : ℕ) (hk : 1 ≤ k) :
    ((VirDeformModes.NormalOrdering.partitionGramPolynomial (2*(k+1))).det).eval
      (bsaCharge (2*(k+1))) = 0 := by
  let N := 2*(k+1)
  let v : gradingVir (bsaCharge N) (N:ℤ) :=
    ⟨bsaSource (bsaCharge N) N N, bsaSource_mem_grading _ N N⟩
  have hv : v ≠ 0 := fun he => bsaSource_even_ne_zero (bsaCharge N) k
    (congrArg Subtype.val he)
  exact VirDeformModes.NormalOrdering.partitionDeterminant_eval_zero_of_singular _
    (by omega) v hv (bsaSource_L1_terminal _ N (by omega))
    (bsaSource_L2_terminal N (by omega))
end VOA.VirModule
