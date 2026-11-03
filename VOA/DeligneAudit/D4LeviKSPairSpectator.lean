import VOA.DeligneAudit.D4LeviKSPairSymmetricEmbeds

/-! PAIR restriction is linear over the unchanged Y and Z alphabets. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

theorem pairRestriction_Y_embedding (a b c : ℕ)
    (P : MvPolynomial (Fin b) ℂ) :
    pairRestriction a b c
      (rename (fun y : Fin b =>
        (Sum.inr (Sum.inl y) : PairSource a b c)) P) =
      rename (fun y : Fin b =>
        (Sum.inr (Sum.inl y) : PairTarget a b c)) P := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [pairRestriction]
  | add P Q hP hQ => simpa only [map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P y hP =>
      simp only [map_mul, hP]
      simp [pairRestriction, pairVariable]

theorem pairRestriction_Z_embedding (a b c : ℕ)
    (P : MvPolynomial (Fin c) ℂ) :
    pairRestriction a b c
      (rename (fun z : Fin c =>
        (Sum.inr (Sum.inr z) : PairSource a b c)) P) =
      rename (fun z : Fin c =>
        (Sum.inr (Sum.inr z) : PairTarget a b c)) P := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [pairRestriction]
  | add P Q hP hQ => simpa only [map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P z hP =>
      simp only [map_mul, hP]
      simp [pairRestriction, pairVariable]

/-- The explicit `Λ(y) ⊗ Λ(z)`-linearity formula. It holds even before
    restricting the Y and Z factors to symmetric polynomials. -/
theorem pairRestriction_YZ_linear (a b c : ℕ)
    (Ypoly : MvPolynomial (Fin b) ℂ)
    (Zpoly : MvPolynomial (Fin c) ℂ)
    (P : MvPolynomial (PairSource a b c) ℂ) :
    pairRestriction a b c
      (rename (fun y : Fin b =>
        (Sum.inr (Sum.inl y) : PairSource a b c)) Ypoly *
       rename (fun z : Fin c =>
        (Sum.inr (Sum.inr z) : PairSource a b c)) Zpoly * P) =
      rename (fun y : Fin b =>
        (Sum.inr (Sum.inl y) : PairTarget a b c)) Ypoly *
      rename (fun z : Fin c =>
        (Sum.inr (Sum.inr z) : PairTarget a b c)) Zpoly *
      pairRestriction a b c P := by
  rw [map_mul, map_mul, pairRestriction_Y_embedding,
    pairRestriction_Z_embedding]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_Y_embedding
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_Z_embedding
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_YZ_linear
