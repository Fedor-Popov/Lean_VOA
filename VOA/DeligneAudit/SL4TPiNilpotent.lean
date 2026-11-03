import VOA.DeligneAudit.SL4TPiPolynomial

/-! # Positive-degree elements act trivially on one-dimensional ideal cells -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Nilpotence suffices; no grading or choice of a maximal ideal is needed in the consumer. -/
theorem ideal_cell_nilpotent_mul (I K : Ideal R) (x p : R)
    (hcell : K.restrictScalars ℂ = I.restrictScalars ℂ ⊔ ℂ ∙ x)
    (hp : IsNilpotent p) : p * x ∈ I := by
  have hx : x ∈ K := by
    change x ∈ K.restrictScalars ℂ
    rw [hcell]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hpx : p * x ∈ I.restrictScalars ℂ ⊔ ℂ ∙ x := by
    rw [← hcell]
    exact K.mul_mem_left p hx
  obtain ⟨y, hy, z, hz, heq⟩ := Submodule.mem_sup.mp hpx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  let q : R →ₐ[ℂ] R ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hy0 : q y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hy
  have he : q p * q x = c • q x := by
    have he' := congrArg q heq
    simpa only [map_add, map_smul, map_mul, hy0, zero_add] using he'.symm
  have hpow : ∀ n : ℕ, q p ^ n * q x = c ^ n • q x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', mul_assoc, ih, mul_smul_comm, he, smul_smul, pow_succ]
  obtain ⟨n, hn⟩ := hp
  have hz : c ^ n • q x = 0 := by
    rw [← hpow n, ← map_pow, hn, map_zero, zero_mul]
  have hresult : q (p * x) = 0 := by
    rw [map_mul, he]
    by_cases hc : c = 0
    · simp [hc]
    · rw [(smul_eq_zero.mp hz).resolve_left (pow_ne_zero n hc), smul_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hresult

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.ideal_cell_nilpotent_mul
