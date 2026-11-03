import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubePower

/-! One marked square-zero factor in the variable-power channel argument.
Square-zero is required only on the marked factor, not on the whole ring. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.VariablePower
noncomputable section
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem iterate_deriv_sub (D : Derivation K A A) (p q : A) (n : ℕ) :
    ((D : A → A)^[n]) (p-q) = ((D : A → A)^[n]) p - ((D : A → A)^[n]) q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',ih,map_sub]
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']

/-- Commuting derivations preserve the marked square-zero subspace. -/
theorem square_zero_iterate_of_commute (D E : Derivation K A A)
    (hDE : ∀ p, D (E p) = E (D p)) (f : A) (hf : D (D f) = 0) (k : ℕ) :
    D (D (((E : A → A)^[k]) f)) = 0 := by
  induction k with
  | zero => exact hf
  | succ k ih =>
      rw [Function.iterate_succ_apply',hDE,hDE,ih,map_zero]

/-- Exact two-term Leibniz rule for a factor killed by the second derivative. -/
theorem iterate_mul_of_square_zero (D : Derivation K A A) (f g : A)
    (hf : D (D f) = 0) (n : ℕ) :
    ((D : A → A)^[n+1]) (f*g) =
      f * ((D : A → A)^[n+1]) g + ((n+1:ℕ):A) * D f * ((D : A → A)^[n]) g := by
  induction n with
  | zero =>
      simp only [Nat.zero_add,Function.iterate_one,Function.iterate_zero_apply,
        Nat.cast_one,one_mul]
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      ring
  | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      simp only [map_add,Derivation.leibniz,Derivation.map_natCast,
        Derivation.map_one_eq_zero,hf,smul_eq_mul,mul_zero,zero_add,
        Function.iterate_succ_apply',Nat.cast_add,Nat.cast_one]
      ring

/-- The low channel factorization is valid on its marked square-zero
factor. It is not asserted as an unrestricted operator identity. -/
theorem low_channel_factorization (D : Derivation K A A) (f g : A)
    (hf : D (D f) = 0) (n : ℕ) :
    f * ((D : A → A)^[n+1]) g - ((n+2:ℕ):A) * D f * ((D : A → A)^[n]) g =
      ((D : A → A)^[n])
        (D (f*g) - ((2*(n+1)+1:ℕ):A) * D f * g) := by
  rw [iterate_deriv_sub]
  rw [show ((D : A → A)^[n]) (D (f*g)) =
    ((D : A → A)^[n+1]) (f*g) from (Function.iterate_succ_apply _ _ _).symm]
  rw [show ((2*(n+1)+1:ℕ):A) * D f * g =
    ((2*(n+1)+1:ℕ):A) * (D f * g) by ring]
  rw [iterate_const_mul D _ (by exact D.map_natCast _) (D f*g) n,
    iterate_const_mul D (D f) hf g n,iterate_mul_of_square_zero D f g hf n]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one]
  ring

end
#print axioms square_zero_iterate_of_commute
#print axioms iterate_mul_of_square_zero
#print axioms low_channel_factorization
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.VariablePower
