import VOA.DeligneAudit.SL4TMixedElementarySource

/-! Surjectivity of the elementary presentation of the second Levi coefficient source. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial
open scoped TensorProduct
attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {B : Type} [CommRing B] [Algebra ℂ B]

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Elementary-generator power sums recover the positional power sums in both alphabets. -/
theorem secondLeviElementaryAlphabet_powerSum (e₁ e₂ : ℕ) (j : Fin 2) (s : ℕ) :
    (secondLeviElementaryAlphabet (B := B) e₁ e₂ j
      (powerSumOfCoeff (if j = 0 then e₁ else e₂)
        (fun k => (-1) ^ k * elementary k) (s + 1))).val =
      secondLeviModePowerSum e₁ e₂ j (s + 1) := by
  rw [powerSumOfCoeff_map]
  change (secondLeviSymmetricModes e₁ e₂).val (powerSumOfCoeff _ _ _) = _
  rw [powerSumOfCoeff_map]
  simp only [map_mul, map_pow, map_neg, map_one, Subalgebra.val_apply,
    secondLeviElementaryAlphabet_elementary]
  fin_cases j
  · have he := powerSumOfCoeff_psum_map (Fin e₁)
      (aeval fun i => (X (.inl i) : MvPolynomial (SecondLeviModeSlot e₁ e₂) B))
      e₁ (s + 1) (by omega)
    simpa only [esymm, psum, map_sum, map_prod, map_pow, aeval_X, rename_X,
      secondLeviModePowerSum, if_pos rfl, ite_true] using he
  · have he := powerSumOfCoeff_psum_map (Fin e₂)
      (aeval fun i => (X (.inr i) : MvPolynomial (SecondLeviModeSlot e₁ e₂) B))
      e₂ (s + 1) (by omega)
    simpa only [esymm, psum, map_sum, map_prod, map_pow, aeval_X, rename_X,
      secondLeviModePowerSum, show (1 : Fin 2) ≠ 0 by decide, if_false, ite_false] using he

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The three elementary-generator images generate their tensor-product coefficient algebra. -/
theorem radicalGrassmannianAlphabet_generates (a b c : ℕ) (d : Fin 3 → ℕ)
    (S : Subalgebra ℂ (RadicalGrassmannianRing a b c d))
    (h : ∀ j P, radicalGrassmannianAlphabet a b c d j P ∈ S)
    (x : RadicalGrassmannianRing a b c d) : x ∈ S := by
  induction x using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | add x y hx hy => exact S.add_mem hx hy
  | tmul x y =>
    induction y using TensorProduct.induction_on with
    | zero => simpa using S.zero_mem
    | add y z hy hz => simpa only [TensorProduct.tmul_add] using S.add_mem hy hz
    | tmul y z =>
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ x
      obtain ⟨Q, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ y
      obtain ⟨T, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ z
      have he := S.mul_mem (S.mul_mem (h 0 P) (h 1 Q)) (h 2 T)
      simpa only [radicalGrassmannianAlphabet, AlgHom.comp_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.one_def, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one] using he

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Every base coefficient has a preimage in the five elementary alphabets. -/
theorem mixedElementarySource_base_mem_range (a b c : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (x : RadicalGrassmannianRing a b c d) :
    secondLeviSymmetricBase e₁ e₂ x ∈ (mixedElementarySource a b c d e₁ e₂).range := by
  apply radicalGrassmannianAlphabet_generates a b c d
    ((mixedElementarySource a b c d e₁ e₂).range.comap (secondLeviSymmetricBase e₁ e₂))
  intro j P
  refine ⟨mixedAlphabet ⟨j.val, by omega⟩ P, ?_⟩
  fin_cases j
  · exact mixedElementarySource_alphabet a b c d e₁ e₂ 0 P
  · exact mixedElementarySource_alphabet a b c d e₁ e₂ 1 P
  · exact mixedElementarySource_alphabet a b c d e₁ e₂ 2 P

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The change from elementary generators to symmetric mode polynomials is surjective. -/
theorem mixedElementarySource_surjective (a b c : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) :
    Function.Surjective (mixedElementarySource a b c d e₁ e₂) := by
  let φ := mixedElementarySource a b c d e₁ e₂
  let S := φ.range.map (secondLeviSymmetricModes e₁ e₂).val
  have hgen : secondLeviPowerSumAlgebra e₁ e₂ ≤ S := by
    apply Algebra.adjoin_le
    rintro P ((⟨x, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩)
    · exact Subalgebra.mem_map.mpr ⟨secondLeviSymmetricBase e₁ e₂ x,
        mixedElementarySource_base_mem_range a b c d e₁ e₂ x, rfl⟩
    · refine Subalgebra.mem_map.mpr ⟨_, ⟨mixedAlphabet 3
        (powerSumOfCoeff e₁ (fun k => (-1) ^ k * elementary k) (s + 1)), rfl⟩, ?_⟩
      change (mixedElementarySource a b c d e₁ e₂
        (mixedAlphabet 3 (powerSumOfCoeff e₁
          (fun k => (-1) ^ k * elementary k) (s + 1)))).val = _
      rw [mixedElementarySource_alphabet]
      exact secondLeviElementaryAlphabet_powerSum e₁ e₂ 0 s
    · refine Subalgebra.mem_map.mpr ⟨_, ⟨mixedAlphabet 4
        (powerSumOfCoeff e₂ (fun k => (-1) ^ k * elementary k) (s + 1)), rfl⟩, ?_⟩
      change (mixedElementarySource a b c d e₁ e₂
        (mixedAlphabet 4 (powerSumOfCoeff e₂
          (fun k => (-1) ^ k * elementary k) (s + 1)))).val = _
      rw [mixedElementarySource_alphabet]
      exact secondLeviElementaryAlphabet_powerSum e₁ e₂ 1 s
  intro P
  obtain ⟨Q, hQ, he⟩ := Subalgebra.mem_map.mp
    (hgen (secondLeviSymmetricModes_le_powerSumAlgebra e₁ e₂ P.property))
  have heq : Q = P := Subtype.ext he
  subst Q
  exact hQ

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviElementaryAlphabet_powerSum
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAlphabet_generates
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_base_mem_range
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_surjective
