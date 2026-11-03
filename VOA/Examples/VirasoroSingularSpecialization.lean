/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.Integer

/-!
# Nonzero specialization of polynomial kernel relations

A finite polynomial vector may vanish at a chosen parameter even when it is
not identically zero. Remove its common power of X-a before specializing.
A polynomial matrix kernel is saturated under this operation, so the new
vector still solves the equations and its specialization is nonzero.

For singular-vector recursions this separates local normalization from the
proof of the generic Ward relation. The latter is NOT supplied here. Nor
does a nonzero vector in a Verma module automatically survive its vacuum
quotient. Those representation-theory inputs remain separate.
-/
namespace VOA.VirasoroSpecialization
open Polynomial
variable {K : Type*} [Field K]
variable {ι κ : Type*} [Fintype κ]

/-- A nonzero finite polynomial vector has a smallest order of vanishing.
Removing that common power of X-a leaves at least one nonzero evaluated
coordinate. Zero coordinates impose no additional divisibility condition. -/
theorem exists_local_primitive_factor (v : κ → Polynomial K) (hv : v≠0) (a : K) :
    ∃ m : ℕ, ∃ u : κ → Polynomial K,
      (∀ j, v j=(X-C a)^m*u j) ∧ (fun j => (u j).eval a)≠0 := by
  classical
  let s := Finset.univ.filter (fun j => v j≠0)
  have hs : s.Nonempty := by
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hv
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  obtain ⟨j0,hj0,hmin⟩ := s.exists_min_image (fun j => (v j).rootMultiplicity a) hs
  have hv0 : v j0≠0 := (Finset.mem_filter.mp hj0).2
  let m := (v j0).rootMultiplicity a
  have hd (j : κ) : (X-C a)^m ∣ v j := by
    by_cases hj : v j=0
    · rw [hj]; exact dvd_zero _
    · exact dvd_trans (pow_dvd_pow _ (hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)))
        (pow_rootMultiplicity_dvd (v j) a)
  choose u hu using hd
  refine ⟨m,u,hu,?_⟩
  obtain ⟨q,hq,hqnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (v j0) hv0 a
  have hp : (X-C a)^m ≠ (0 : Polynomial K) := pow_ne_zero _ (X_sub_C_ne_zero a)
  have he : u j0=q := (mul_left_cancel₀ hp) ((hu j0).symm.trans hq)
  intro hz
  have heval := congrFun hz j0
  have hqeval : q.eval a=0 := by simpa only [he,Pi.zero_apply] using heval
  exact hqnd (dvd_iff_isRoot.mpr hqeval)

/-- Multiplying every coordinate by a common polynomial multiplies every
matrix equation by that polynomial. -/
theorem mulVec_common_factor (A : Matrix ι κ (Polynomial K)) (q : Polynomial K)
    (v : κ → Polynomial K) :
    A.mulVec (fun j => q*v j)=fun i => q*(A.mulVec v i) := by
  classical
  funext i
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Polynomial matrix kernels are saturated by any nonzero common scalar
factor: cancelling that factor preserves every row equation. -/
theorem mulVec_cancel_factor (A : Matrix ι κ (Polynomial K)) (q : Polynomial K)
    (hq : q≠0) (v : κ → Polynomial K)
    (hv : A.mulVec (fun j => q*v j)=0) : A.mulVec v=0 := by
  rw [mulVec_common_factor] at hv
  funext i
  exact (mul_eq_zero.mp (congrFun hv i)).resolve_left hq

/-- Evaluation commutes with finite polynomial matrix equations. No rational
function is evaluated at a pole. -/
theorem eval_mulVec (A : Matrix ι κ (Polynomial K)) (v : κ → Polynomial K) (a : K) :
    (A.map (Polynomial.evalRingHom a)).mulVec (fun j => (v j).eval a)=
      fun i => (A.mulVec v i).eval a := by
  classical
  funext i
  simp [Matrix.mulVec,dotProduct,Polynomial.eval_finsetSum,Polynomial.eval_mul]

/-- Every nonzero polynomial kernel vector can be normalized at any chosen
parameter while staying in the SAME polynomial kernel. It may differ from
the originally chosen recursion normalization by a common scalar factor. -/
theorem exists_primitive_kernel (A : Matrix ι κ (Polynomial K))
    (v : κ → Polynomial K) (hv : v≠0) (hAv : A.mulVec v=0) (a : K) :
    ∃ u : κ → Polynomial K, A.mulVec u=0 ∧ (fun j => (u j).eval a)≠0 := by
  obtain ⟨m,u,hu,hune⟩ := exists_local_primitive_factor v hv a
  refine ⟨u,?_,hune⟩
  apply mulVec_cancel_factor A ((X-C a)^m) (pow_ne_zero _ (X_sub_C_ne_zero a)) u
  simpa only [← hu] using hAv

/-- A nonzero polynomial kernel relation yields a nonzero kernel at EVERY
specialization, even when all its original coefficients vanish there. This
is a specialization theorem, not an existence proof for the initial relation. -/
theorem exists_specialized_kernel (A : Matrix ι κ (Polynomial K))
    (v : κ → Polynomial K) (hv : v≠0) (hAv : A.mulVec v=0) (a : K) :
    ∃ w : κ → K, w≠0 ∧ (A.map (Polynomial.evalRingHom a)).mulVec w=0 := by
  obtain ⟨u,hu,hune⟩ := exists_primitive_kernel A v hv hAv a
  refine ⟨fun j => (u j).eval a,hune,?_⟩
  rw [eval_mulVec,hu]
  funext i
  simp

/-- A ring homomorphism preserves finite matrix equations. This is used
both for extending polynomial scalars to rational functions and for returning
to polynomial equations through the injective fraction-field map. -/
theorem map_mulVec {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix ι κ R) (v : κ → R) :
    (A.map f).mulVec (fun j => f (v j))=fun i => f (A.mulVec v i) := by
  classical
  funext i
  simp [Matrix.mulVec,dotProduct]

/-- Clear a common denominator from a nonzero rational-function kernel
vector. The resulting polynomial vector is nonzero and solves the original
polynomial matrix equations, without any specialization of fractions. -/
theorem exists_polynomial_kernel_of_rational (A : Matrix ι κ (Polynomial K))
    (v : κ → RatFunc K) (hv : v≠0)
    (hAv : (A.map (algebraMap (Polynomial K) (RatFunc K))).mulVec v=0) :
    ∃ u : κ → Polynomial K, u≠0 ∧ A.mulVec u=0 := by
  classical
  obtain ⟨b,hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) v
  choose u hu using hb
  have hb0 : (b : Polynomial K)≠0 := nonZeroDivisors.coe_ne_zero b
  have hbF : algebraMap (Polynomial K) (RatFunc K) b≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mpr hb0
  refine ⟨u,?_,?_⟩
  · intro hz
    apply hv
    funext j
    have hh := hu j
    rw [show u j=0 from congrFun hz j,map_zero,Algebra.smul_def] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hbF
  · have hh : (A.map (algebraMap (Polynomial K) (RatFunc K))).mulVec
        (fun j => algebraMap (Polynomial K) (RatFunc K) (u j))=0 := by
      simp_rw [hu]
      change (A.map (algebraMap (Polynomial K) (RatFunc K))).mulVec ((b : Polynomial K) • v)=0
      rw [Matrix.mulVec_smul,hAv,smul_zero]
    rw [map_mulVec] at hh
    funext i
    apply IsFractionRing.injective (Polynomial K) (RatFunc K)
    simpa only [Pi.zero_apply,map_zero] using congrFun hh i

/-- A generic rational kernel relation specializes to a nonzero kernel at
every parameter of the polynomial equation matrix. Clearing denominators
and then removing common zeros are both proved internally. The rational
formula itself need not have a defined value at that parameter. -/
theorem exists_specialized_kernel_of_rational (A : Matrix ι κ (Polynomial K))
    (v : κ → RatFunc K) (hv : v≠0)
    (hAv : (A.map (algebraMap (Polynomial K) (RatFunc K))).mulVec v=0) (a : K) :
    ∃ w : κ → K, w≠0 ∧ (A.map (Polynomial.evalRingHom a)).mulVec w=0 := by
  obtain ⟨u,hu,hAu⟩ := exists_polynomial_kernel_of_rational A v hv hAv
  exact exists_specialized_kernel A u hu hAu a

end VOA.VirasoroSpecialization
