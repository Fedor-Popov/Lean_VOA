import VOA.Huang.GaloisSymAlgebra

/-!
# From Galois column scalars to signs

An integral bilinear normalization is sufficient. For the usual symmetric
modular S, its integral square (charge conjugation) supplies this normalization
because `S^4 = 1`. Unitarity and cyclotomicity are not needed in this step.
-/

noncomputable section

namespace VOA.Huang.GaloisSym

open Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- Each column has norm one for one bilinear form with integral coefficients.
This is a normalization condition, not an assertion of positive definiteness. -/
def IntegralColumnNormalization (S : Matrix ι ι K) : Prop :=
  ∃ B : Matrix ι ι ℤ, ∀ x,
    ∑ a, ∑ b, (B a b : K) * S a x * S b x = 1

theorem integralColumnNormalization_of_matrix {S : Matrix ι ι K}
    (B : Matrix ι ι ℤ) (hB : S.transpose * (B.map (Int.castRingHom K) * S) = 1) :
    IntegralColumnNormalization S := by
  refine ⟨B, fun x => ?_⟩
  have h := congrFun (congrFun hB x) x
  simpa [Matrix.mul_apply, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc] using h

/-- Symmetry, an integral square and fourth power one give the needed normalization. -/
theorem integralColumnNormalization_of_square {S : Matrix ι ι K}
    (hs : S.transpose = S) (B : Matrix ι ι ℤ)
    (hB : S * S = B.map (Int.castRingHom K)) (h4 : S ^ 4 = 1) :
    IntegralColumnNormalization S := by
  apply integralColumnNormalization_of_matrix B
  rw [hs, ← hB]
  simpa [pow_succ, Matrix.mul_assoc] using h4

/-- The Coste–Gannon signed-column law, with normalization explicit. -/
theorem VerlindeSystem.galois_signed_columns
    {N : ι → ι → ι → ℕ} {S : Matrix ι ι K} {v0 : ι}
    (H : VerlindeSystem N S v0) (hnorm : IntegralColumnNormalization S) (σ : K ≃+* K) :
    ∃ (π : Equiv.Perm ι) (ε : ι → K), (∀ x, ε x = 1 ∨ ε x = -1) ∧
      ∀ a x, σ (S a x) = ε x * S a (π x) := by
  obtain ⟨π, d, _, hd⟩ := H.galois_columns σ
  obtain ⟨B, hB⟩ := hnorm
  refine ⟨π, d, fun x => ?_, hd⟩
  have he := congrArg σ (hB x)
  simp only [map_sum, map_mul, map_intCast, map_one, hd] at he
  have hs : (∑ a, ∑ b, (B a b : K) * (d x * S a (π x)) * (d x * S b (π x))) =
      d x ^ 2 * ∑ a, ∑ b, (B a b : K) * S a (π x) * S b (π x) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hs, hB, mul_one] at he
  exact (sq_eq_one_iff).mp he

/-- Symmetry changes the column law into the row convention `σ(S) = Gσ S`. -/
theorem VerlindeSystem.galois_signed_rows
    {N : ι → ι → ι → ℕ} {S : Matrix ι ι K} {v0 : ι}
    (H : VerlindeSystem N S v0) (hnorm : IntegralColumnNormalization S)
    (hs : S.transpose = S) (σ : K ≃+* K) :
    ∃ (π : Equiv.Perm ι) (ε : ι → K), (∀ a, ε a = 1 ∨ ε a = -1) ∧
      ∀ a b, σ (S a b) = ε a * S (π a) b := by
  have hsym : ∀ a b, S b a = S a b := fun a b => congrFun (congrFun hs a) b
  obtain ⟨π, ε, he, h⟩ := H.galois_signed_columns hnorm σ
  exact ⟨π, ε, he, fun a b => by rw [← hsym a b, h, hsym]⟩

/-- The two Galois actions commute on every entry: use the row law for one
automorphism and the column law for the other. This is the algebraic ingredient
in the abelian-field argument; no Kronecker–Weber theorem is invoked here. -/
theorem VerlindeSystem.galois_commute_entry
    {N : ι → ι → ι → ℕ} {S : Matrix ι ι K} {v0 : ι}
    (H : VerlindeSystem N S v0) (hnorm : IntegralColumnNormalization S)
    (hs : S.transpose = S) (σ τ : K ≃+* K) (a b : ι) :
    σ (τ (S a b)) = τ (σ (S a b)) := by
  obtain ⟨p, e, he, hσ⟩ := H.galois_signed_columns hnorm σ
  obtain ⟨q, d, hd, hτ⟩ := H.galois_signed_rows hnorm hs τ
  have hed : σ (d a) = d a := by rcases hd a with h | h <;> simp [h]
  have hee : τ (e b) = e b := by rcases he b with h | h <;> simp [h]
  rw [hτ, map_mul, hed, hσ, hσ, map_mul, hee, hτ]
  ring

end VOA.Huang.GaloisSym
