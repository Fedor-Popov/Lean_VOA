import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Light generic derivative identities for the cube projection calculation. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section
variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
variable [Algebra K A] [Algebra K B]

theorem deriv_pow_succ (D : Derivation K A A) (u : A) (k : ℕ) :
    D (u ^ (k+1)) = ((k+1:ℕ):A) * u^k * D u := by
  rw [Derivation.leibniz_pow,show k+1-1=k by omega]
  simp only [smul_eq_mul,nsmul_eq_mul]
  ring

/-- A two-step variable string gives a falling factorial at every order. -/
theorem iterate_deriv_power (D : Derivation K A A) (u v : A)
    (hu : D u = v) (hv : D v = 0) (k n : ℕ) :
    ((D : A → A)^[k]) (u^(n+k)) =
      ((n+k).descFactorial k:A) * u^n * v^k := by
  induction k generalizing n with
  | zero =>
      simp only [Function.iterate_zero_apply,Nat.add_zero,Nat.descFactorial_zero,
        Nat.cast_one,pow_zero,one_mul,mul_one]
  | succ k ih =>
      rw [Function.iterate_succ_apply',show n+(k+1)=(n+1)+k by omega,ih]
      rw [Nat.descFactorial_succ,show n+1+k-k=n+1 by omega]
      have hz : D (v^k) = 0 := by simp only [Derivation.leibniz_pow,hv,smul_zero]
      simp only [Derivation.leibniz,Derivation.map_natCast,deriv_pow_succ,
        hu,hz,smul_eq_mul]
      simp only [pow_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      ring

theorem iterate_deriv_power_of_le (D : Derivation K A A) (u v : A)
    (hu : D u = v) (hv : D v = 0) (r k : ℕ) (hk : k ≤ r) :
    ((D : A → A)^[k]) (u^r) =
      (r.descFactorial k:A) * u^(r-k) * v^k := by
  simpa only [Nat.sub_add_cancel hk] using iterate_deriv_power D u v hu hv k (r-k)

/-- A factor killed by the derivation stays outside every iterate. -/
theorem iterate_const_mul (D : Derivation K A A) (c : A) (hc : D c = 0)
    (p : A) (k : ℕ) :
    ((D : A → A)^[k]) (c*p) = c * ((D : A → A)^[k]) p := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply',ih,Derivation.leibniz,hc]
      simp only [smul_eq_mul,mul_zero,add_zero,Function.iterate_succ_apply']

/-- Symbolic intertwining transports all derivative iterates. -/
theorem map_iterate_deriv (f : A →ₐ[K] B)
    (D : Derivation K A A) (E : Derivation K B B)
    (h : ∀ p, f (D p) = E (f p)) (k : ℕ) (p : A) :
    f (((D : A → A)^[k]) p) = ((E : B → B)^[k]) (f p) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',h,ih,Function.iterate_succ_apply']

end
#print axioms iterate_deriv_power_of_le
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
