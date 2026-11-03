import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

set_option maxSynthPendingDepth 3

/-!
# The binomial obstruction in Miyamoto's cyclic C₂ argument

An algebraic proof of Lemma 13 of arXiv:1306.5031, using disjoint generalized
shift eigenspaces instead of eventual positivity. No VOA identities are assumed
or proved in this file.
-/

noncomputable section
namespace VOA.Classification.COne.OrbC2
open scoped BigOperators

abbrev Seq := ℕ → ℂ

def shift : Module.End ℂ Seq where
  toFun f n := f (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def difference (a : ℂ) : Module.End ℂ Seq := shift - a • 1

@[simp] theorem difference_apply (a : ℂ) (f : Seq) (n : ℕ) :
    difference a f n = f (n + 1) - a * f n := rfl

/-- The binomial transform with parameter `c`. -/
def binomial (c : ℂ) : Seq →ₗ[ℂ] Seq where
  toFun f n := ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * c ^ j * f (n - j)
  map_add' f g := by ext n; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    ext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

def sign : Seq →ₗ[ℂ] Seq where
  toFun f n := (-1 : ℂ) ^ n * f n
  map_add' f g := by ext n; exact mul_add _ _ _
  map_smul' a f := by ext n; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Pascal's identity intertwines the shift and the binomial transform. -/
theorem binomial_shift (c : ℂ) (f : Seq) :
    shift (binomial c f) = binomial c (shift f) + c • binomial c f := by
  ext n
  change (∑ j ∈ Finset.range (n + 2), ((n + 1).choose j : ℂ) *
    c ^ j * f (n + 1 - j)) = _
  simp_rw [mul_assoc]
  rw [Finset.sum_choose_succ_mul (fun i j => c ^ i * f j)]
  change _ = (∑ j ∈ Finset.range (n + 1), _) + c * ∑ j ∈ Finset.range (n + 1), _
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [show n + 1 - j = (n - j) + 1 by have := Finset.mem_range.mp hj; omega]
    simp only [shift, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring

theorem difference_binomial (c a : ℂ) (f : Seq) :
    difference (c + a) (binomial c f) = binomial c (difference a f) := by
  rw [difference, LinearMap.sub_apply, binomial_shift]
  change _ = binomial c (shift f - a • f)
  rw [map_sub, map_smul]
  ext n
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    LinearMap.smul_apply, Module.End.one_apply]
  ring

theorem difference_sign (f : Seq) :
    difference (-1) (sign f) = -sign (difference 1 f) := by
  ext n
  simp [difference_apply, sign, pow_succ]
  ring

theorem difference_pow_binomial (c a : ℂ) (k : ℕ) (f : Seq) :
    (difference (c + a) ^ k) (binomial c f) = binomial c ((difference a ^ k) f) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, difference_binomial,
      pow_succ', Module.End.mul_apply]

theorem difference_pow_sign (k : ℕ) (f : Seq) :
    (difference (-1) ^ k) (sign f) = (-1 : ℂ) ^ k • sign ((difference 1 ^ k) f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, difference_sign]
    simp [pow_succ', Module.End.mul_apply]

/-- Restriction to natural inputs commutes with forward differences. -/
theorem difference_pow_restrict (f : ℂ → ℂ) (k : ℕ) (n : ℕ) :
    (difference 1 ^ k) (fun j => f j) n = (fwdDiff (1 : ℂ))^[k] f n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, difference_apply, ih, ih,
      Function.iterate_succ_apply']
    simp [fwdDiff, Nat.cast_add, Nat.cast_one]

theorem polynomial_difference_nilpotent (P : Polynomial ℂ) :
    (difference 1 ^ (P.natDegree + 1)) (fun n : ℕ => P.eval (n : ℂ)) = 0 := by
  ext n
  rw [difference_pow_restrict (fun z => P.eval z), Polynomial.fwdDiff_iter_degree_add_one_eq_zero]
  rfl

/-- Distinct generalized shift eigenvalues cannot support the same sequence. -/
theorem difference_disjoint {a b : ℂ} (hab : a ≠ b) (f : Seq) (k l : ℕ)
    (ha : (difference a ^ k) f = 0) (hb : (difference b ^ l) f = 0) : f = 0 := by
  have h := shift.disjoint_genEigenspace hab k l
  have hfa : f ∈ shift.genEigenspace a k := by
    rw [Module.End.mem_genEigenspace_nat]
    exact ha
  have hfb : f ∈ shift.genEigenspace b l := by
    rw [Module.End.mem_genEigenspace_nat]
    exact hb
  exact (Submodule.disjoint_def.mp h) f hfa hfb

/-- Miyamoto's coefficient obstruction, in the more general finite-difference form. -/
theorem binomial_sign_eq_zero (c : ℂ) (hc : c + 1 ≠ -1) (f g : Seq)
    (k l : ℕ) (hf : (difference 1 ^ k) f = 0) (hg : (difference 1 ^ l) g = 0)
    (h : binomial c f = sign g) : binomial c f = 0 := by
  apply difference_disjoint hc _ k l
  · rw [difference_pow_binomial, hf, map_zero]
  · rw [h, difference_pow_sign, hg, map_zero, smul_zero]

/-- The binomial transform is triangular with diagonal entries one. -/
theorem binomial_injective (c : ℂ) : Function.Injective (binomial c) := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro f hf
  change f = 0
  have hz : binomial c f = 0 := hf
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congrFun hz n
    change (∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * c ^ j * f (n - j)) = 0 at hn
    rw [Finset.sum_eq_single 0] at hn
    · simpa using hn
    · intro j hj hj0
      rw [ih (n - j) (by have := Finset.mem_range.mp hj; omega)]
      simp
    · simp

theorem polynomial_eq_zero_of_nat_eval (P : Polynomial ℂ)
    (h : ∀ n : ℕ, P.eval (n : ℂ) = 0) : P = 0 := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℂ))).mono
  rintro _ ⟨n, rfl⟩
  simpa using h n

/-- Miyamoto Lemma 13: no nonzero polynomial pair satisfies equation (4.2).
The parameter condition is exact: `c = -2` is excluded. -/
theorem miyamoto_polynomial_obstruction (c : ℂ) (hc : c + 1 ≠ -1)
    (P Q : Polynomial ℂ)
    (h : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℂ) * c ^ j * P.eval ((n - j : ℕ) : ℂ)) = (-1 : ℂ) ^ n * Q.eval (n : ℂ)) :
    P = 0 ∧ Q = 0 := by
  have he : binomial c (fun n : ℕ => P.eval (n : ℂ)) =
      sign (fun n : ℕ => Q.eval (n : ℂ)) := funext h
  have hz := binomial_sign_eq_zero c hc _ _ (P.natDegree + 1) (Q.natDegree + 1)
    (polynomial_difference_nilpotent P) (polynomial_difference_nilpotent Q) he
  have hp : (fun n : ℕ => P.eval (n : ℂ)) = 0 :=
    binomial_injective c (hz.trans (map_zero (binomial c)).symm)
  refine ⟨polynomial_eq_zero_of_nat_eval P (congrFun hp), ?_⟩
  apply polynomial_eq_zero_of_nat_eval Q
  intro n
  have hq := congrFun (he.symm.trans hz) n
  exact (mul_eq_zero.mp hq).resolve_left (pow_ne_zero _ (by norm_num))

/-- The orders used in the cyclic-orbifold theorem satisfy the parameter condition. -/
theorem miyamoto_polynomial_obstruction_order (p : ℕ) (hp : 2 ≤ p)
    (P Q : Polynomial ℂ)
    (h : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℂ) * (p - 2 : ℂ) ^ j * P.eval ((n - j : ℕ) : ℂ)) =
        (-1 : ℂ) ^ n * Q.eval (n : ℂ)) : P = 0 ∧ Q = 0 := by
  apply miyamoto_polynomial_obstruction (p - 2) _ P Q h
  intro he
  have : (p : ℂ) = 0 := by linear_combination he
  have : p = 0 := by exact_mod_cast this
  omega

end VOA.Classification.COne.OrbC2
