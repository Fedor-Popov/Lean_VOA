import VOA.DeligneAudit.SL4TMixedElementarySource

/-! The mixed relation windows in the symmetric presentation of the second Levi source. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial
attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {R : Type*} [CommRing R] [Algebra ℂ R]

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Cancelling two complementary signs leaves the sign of the first degree. -/
theorem complementaryDegree_sign (i n : ℕ) (hi : i ≤ n) :
    (-1 : R) ^ n * (-1) ^ (n - i) = (-1) ^ i := by
  calc
    _ = ((-1 : R) ^ i * (-1) ^ (n - i)) * (-1) ^ (n - i) := by
      congr 1
      rw [← pow_add, Nat.add_sub_of_le hi]
    _ = _ := by rw [mul_assoc, ← mul_pow]; simp

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Newton coefficients of a virtual base alphabet are signed mixed ambient coefficients. -/
theorem mixedAmbient_newtonCoeff (φ : MixedPoly →ₐ[ℂ] R) (i j : Fin 5) (d e n : ℕ) :
    newtonCoeff (fun s =>
        powerSumOfCoeff d (fun k => (-1) ^ k * φ (mixedE i k)) s -
        powerSumOfCoeff e (fun k => (-1) ^ k * φ (mixedE j k)) s) n =
      (-1) ^ n * φ (mixedConv (mixedE i) (fun k => (-1) ^ k * mixedH j k) n) := by
  have he := newtonCoeff_difference_alphabets (φ.comp (mixedAlphabet i))
    (φ.comp (mixedAlphabet j)) d e n
  simp only [AlgHom.comp_apply] at he
  simp only [mixedE, mixedH] at ⊢
  rw [he]
  change _ = (-1) ^ n *
    φ (mixedConv (mixedE i) (fun k => (-1) ^ k * mixedH j k) n)
  simp only [mixedConv, map_sum, map_mul, map_pow, map_neg, map_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hs := complementaryDegree_sign (R := R) k n (by
    have := Finset.mem_range.mp hk
    omega)
  calc
    _ = ((-1 : R) ^ n * (-1) ^ (n - k)) *
        (φ (mixedE i k) * φ (mixedH j (n - k))) := by rw [hs]; simp only [mixedE, mixedH]; ring
    _ = _ := by ring

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- A relative complete coefficient is the signed complementary mixed coefficient. -/
theorem mixedRelative_signedCoefficient (φ : MixedPoly →ₐ[ℂ] R)
    (u : ℕ → MixedPoly) (i : Fin 5) (p : ℕ → R)
    (hp : ∀ n, newtonCoeff p n = (-1) ^ n * φ (u n)) (n : ℕ) :
    (∑ z ∈ Finset.antidiagonal n, φ (mixedH i z.1) * newtonCoeff p z.2) =
      (-1) ^ n * φ (mixedConv u (fun k => (-1) ^ k * mixedH i k) n) := by
  rw [← Finset.Nat.sum_antidiagonal_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Prod.swap, hp, mixedConv, map_sum, map_mul, map_pow, map_neg, map_one,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hs := complementaryDegree_sign (R := R) k n (by
    have := Finset.mem_range.mp hk
    omega)
  calc
    _ = ((-1 : R) ^ n * (-1) ^ (n - k)) *
        (φ (u k) * φ (mixedH i (n - k))) := by rw [hs]; simp only [mixedE, mixedH]; ring
    _ = _ := by ring

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The first retained Cartan has the first mixed ambient alphabet as Newton coefficients. -/
theorem mixedElementarySource_firstNewton (a b c : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ n : ℕ) :
    secondLeviSymmetricBase e₁ e₂ (newtonCoeff (radicalLeviPowerSum a b c d 0) n) =
      (-1) ^ n * mixedElementarySource a b c d e₁ e₂ (mixedU n) := by
  let φ := mixedElementarySource a b c d e₁ e₂
  have he := mixedAmbient_newtonCoeff φ 0 1 (d 0) (d 1) n
  rw [← newtonCoeff_map]
  have hseq : (fun s => secondLeviSymmetricBase e₁ e₂
      (radicalLeviPowerSum a b c d 0 s)) =
      (fun s => powerSumOfCoeff (d 0) (fun k => (-1) ^ k * φ (mixedE 0 k)) s -
        powerSumOfCoeff (d 1) (fun k => (-1) ^ k * φ (mixedE 1 k)) s) := by
    funext s
    simp only [radicalLeviPowerSum, if_pos rfl, ite_true, map_sub,
      radicalGrassmannianAlphabet_powerSum, powerSumOfCoeff_map,
      map_mul, map_pow, map_neg, map_one, φ, mixedE, mixedElementarySource_alphabet,
      mixedElementaryAlphabet, AlgHom.comp_apply]
  rw [hseq]
  exact he

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The last retained Cartan has the second mixed ambient alphabet as Newton coefficients. -/
theorem mixedElementarySource_secondNewton (a b c : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ n : ℕ) :
    secondLeviSymmetricBase e₁ e₂ (newtonCoeff (radicalLeviPowerSum a b c d 1) n) =
      (-1) ^ n * mixedElementarySource a b c d e₁ e₂ (mixedV n) := by
  let φ := mixedElementarySource a b c d e₁ e₂
  have he := mixedAmbient_newtonCoeff φ 1 2 (d 1) (d 2) n
  rw [← newtonCoeff_map]
  have hseq : (fun s => secondLeviSymmetricBase e₁ e₂
      (radicalLeviPowerSum a b c d 1 s)) =
      (fun s => powerSumOfCoeff (d 1) (fun k => (-1) ^ k * φ (mixedE 1 k)) s -
        powerSumOfCoeff (d 2) (fun k => (-1) ^ k * φ (mixedE 2 k)) s) := by
    funext s
    simp only [radicalLeviPowerSum, show (1 : Fin 2) ≠ 0 by decide, if_false, map_sub,
      radicalGrassmannianAlphabet_powerSum, powerSumOfCoeff_map,
      map_mul, map_pow, map_neg, map_one, φ, mixedE, mixedElementarySource_alphabet,
      mixedElementaryAlphabet, AlgHom.comp_apply]
  rw [hseq]
  exact he

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The first finite relative window agrees with the mixed complement relation. -/
theorem mixedElementarySource_firstRelative (a b c : ℕ) (d : Fin 3 → ℕ)
    (e₁ e₂ n : ℕ) :
    secondLeviRelativeGenerator e₁ e₂ 0 (radicalLeviPowerSum a b c d 0) n =
      (-1) ^ n * mixedElementarySource a b c d e₁ e₂ (mixedG1prime n) := by
  have hp (k : ℕ) := mixedElementarySource_firstNewton a b c d e₁ e₂ k
  simp_rw [← newtonCoeff_map] at hp
  have he := mixedRelative_signedCoefficient
    (mixedElementarySource a b c d e₁ e₂) mixedU 3 _ hp n
  change _ = (-1) ^ n * mixedElementarySource a b c d e₁ e₂
    (mixedConv _ _ n)
  rw [← he]
  apply Subtype.ext
  simp only [secondLeviRelativeGenerator, secondLeviRelativeComplete,
    AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, mixedH, mixedElementarySource_alphabet,
    mixedElementaryAlphabet, secondLeviElementaryAlphabet_complete, if_pos rfl, ite_true,
    newtonCoeff_map]
  rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The second finite relative window agrees with the mixed complement relation. -/
theorem mixedElementarySource_secondRelative (a b c : ℕ) (d : Fin 3 → ℕ)
    (e₁ e₂ n : ℕ) :
    secondLeviRelativeGenerator e₁ e₂ 1 (radicalLeviPowerSum a b c d 1) n =
      (-1) ^ n * mixedElementarySource a b c d e₁ e₂ (mixedG2prime n) := by
  have hp (k : ℕ) := mixedElementarySource_secondNewton a b c d e₁ e₂ k
  simp_rw [← newtonCoeff_map] at hp
  have he := mixedRelative_signedCoefficient
    (mixedElementarySource a b c d e₁ e₂) mixedV 4 _ hp n
  change _ = (-1) ^ n * mixedElementarySource a b c d e₁ e₂
    (mixedConv _ _ n)
  rw [← he]
  apply Subtype.ext
  simp only [secondLeviRelativeGenerator, secondLeviRelativeComplete,
    AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, mixedH, mixedElementarySource_alphabet,
    mixedElementaryAlphabet, secondLeviElementaryAlphabet_complete,
    show (1 : Fin 2) ≠ 0 by decide, if_false, newtonCoeff_map]
  rfl

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.complementaryDegree_sign
#print axioms VOA.DeligneAudit.SL4T.mixedAmbient_newtonCoeff
#print axioms VOA.DeligneAudit.SL4T.mixedRelative_signedCoefficient
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_firstNewton
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_secondNewton
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_firstRelative
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_secondRelative
