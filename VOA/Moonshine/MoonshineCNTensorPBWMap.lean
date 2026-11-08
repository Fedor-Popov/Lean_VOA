import VOA.Moonshine.MoonshineCNTensorNegative

/-! # Triangular negative words on the tensor sector

The additional matter mode preserves both polynomial filtration indices.
The sorted-word map is defined on actual tensor coefficients.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped TensorProduct BigOperators

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem hypTensorNegative_leading (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (j d w : ℕ) (v : V) (p : hypFock) (hp : p ∈ hypBHomogeneous d w) :
    hypTensorNegative D κ ell j (v ⊗ₜ[ℂ] p) -
      κ • (v ⊗ₜ[ℂ] (X (j, 1) * p)) ∈ hypTensorFiltered (d + 1) (w + j + 1) := by
  have h₁ := hypTensorFiltered_tmul (d + 1) (w + j + 1) (D j v) p
    (hypBFiltered_of_homogeneous hp (Or.inl (by omega)))
  have h₂ := hypTensorFiltered_tmul (d + 1) (w + j + 1) v _
    (hypSugawara_negative_leading_filtered κ ell j d w p hp)
  have h := (hypTensorFiltered (d + 1) (w + j + 1)).add_mem h₁ h₂
  simpa only [hypTensorNegative_tmul, TensorProduct.tmul_sub,
    TensorProduct.tmul_smul, add_sub_assoc] using h

theorem hypTensorNegative_filtered (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (j d w : ℕ) (x : V ⊗[ℂ] hypFock) (hx : x ∈ hypTensorFiltered d w) :
    hypTensorNegative D κ ell j x ∈ hypTensorFiltered (d + 1) (w + j + 1) := by
  apply hypTensorSupported_induction _
    ((hypTensorFiltered (d + 1) (w + j + 1)).comap (hypTensorNegative D κ ell j)) ?_ hx
  intro e he v
  change _ < _ ∨ (_ = _ ∧ _ < _) at he
  change hypTensorNegative D κ ell j (v ⊗ₜ[ℂ] monomial e 1) ∈
    hypTensorFiltered (d + 1) (w + j + 1)
  rw [hypTensorNegative_tmul]
  apply Submodule.add_mem
  · apply hypTensorFiltered_tmul
    exact hypBFiltered_of_homogeneous (hypBHomogeneous_monomial e 1) (Or.inl (by omega))
  · apply hypTensorFiltered_tmul
    apply hypSugawara_negative_filtered
    exact hypBFiltered_of_homogeneous (hypBHomogeneous_monomial e 1) he

/-- Tensor version of the full iterated leading-term formula. -/
theorem hypTensorNegative_word_leading (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (d w : ℕ) (v : V) (p : hypFock) (hp : p ∈ hypBHomogeneous d w) (l : List ℕ) :
    stringNegativeWord (hypTensorNegative D κ ell) (v ⊗ₜ[ℂ] p) l -
      κ ^ l.length • (v ⊗ₜ[ℂ] (hypBWordMonomial l * p)) ∈
      hypTensorFiltered (l.length + d) (stringWordEnergy l + w) := by
  induction l with
  | nil => simp [stringNegativeWord, hypBWordMonomial, stringWordEnergy]
  | cons j l ih =>
    have h₁ := hypTensorNegative_filtered D κ ell j _ _ _ ih
    have h₂ := (hypTensorFiltered (l.length + d + 1)
      (stringWordEnergy l + w + j + 1)).smul_mem (κ ^ l.length)
      (hypTensorNegative_leading D κ ell j _ _ v _
        (hypBHomogeneous_mul (hypBWordMonomial_homogeneous l) hp))
    have h := (hypTensorFiltered (l.length + d + 1)
      (stringWordEnergy l + w + j + 1)).add_mem h₁ h₂
    have he : hypTensorNegative D κ ell j
        (stringNegativeWord (hypTensorNegative D κ ell) (v ⊗ₜ[ℂ] p) l -
          κ ^ l.length • (v ⊗ₜ[ℂ] (hypBWordMonomial l * p))) +
        κ ^ l.length • (hypTensorNegative D κ ell j
          (v ⊗ₜ[ℂ] (hypBWordMonomial l * p)) -
            κ • (v ⊗ₜ[ℂ] (X (j, 1) * (hypBWordMonomial l * p)))) =
        stringNegativeWord (hypTensorNegative D κ ell) (v ⊗ₜ[ℂ] p) (j :: l) -
          κ ^ (j :: l).length • (v ⊗ₜ[ℂ] (hypBWordMonomial (j :: l) * p)) := by
      simp only [map_sub, map_smul, smul_sub, smul_smul, stringNegativeWord,
        List.length_cons, pow_succ, hypBWordMonomial, List.map_cons, List.prod_cons, mul_assoc]
      abel
    rw [he] at h
    convert h using 1
    simp only [List.length_cons, stringWordEnergy_cons]
    congr 1 <;> omega

def hypTensorWordOperator (D : ℕ → Module.End ℂ V) (κ ell : ℂ) (l : List ℕ) :
    Module.End ℂ (V ⊗[ℂ] hypFock) := (l.map (hypTensorNegative D κ ell)).prod

theorem hypTensorWordOperator_apply (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (l : List ℕ) (x : V ⊗[ℂ] hypFock) :
    hypTensorWordOperator D κ ell l x = stringNegativeWord (hypTensorNegative D κ ell) x l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simpa only [hypTensorWordOperator, List.map_cons, List.prod_cons,
      Module.End.mul_apply, stringNegativeWord] using congrArg (hypTensorNegative D κ ell j) ih

def hypTensorPBWMap (D : ℕ → Module.End ℂ V) (κ ell : ℂ) :
    Module.End ℂ (V ⊗[ℂ] hypFock) :=
  (Finsupp.lsum ℂ fun e => (hypTensorWordOperator D κ ell (hypCanonicalBWord e)).comp
    ((TensorProduct.mk ℂ V hypFock).flip (monomial (hypAExponent e) 1))).comp
      hypTensorCoordinates.toLinearMap

@[simp] theorem hypTensorPBWMap_monomial (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (v : V) (e : (ℕ × Fin 2) →₀ ℕ) :
    hypTensorPBWMap D κ ell (v ⊗ₜ[ℂ] monomial e 1) =
      stringNegativeWord (hypTensorNegative D κ ell)
        (v ⊗ₜ[ℂ] monomial (hypAExponent e) 1) (hypCanonicalBWord e) := by
  simp only [hypTensorPBWMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    hypTensorCoordinates_monomial, Finsupp.lsum_single, LinearMap.flip_apply,
    TensorProduct.mk_apply, hypTensorWordOperator_apply]

/-- Triangularity of the actual sector PBW map, with no relation assumed on `D`. -/
theorem hypTensorPBWMap_leading (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (v : V) (e : (ℕ × Fin 2) →₀ ℕ) :
    hypTensorPBWMap D κ ell (v ⊗ₜ[ℂ] monomial e 1) -
      κ ^ (Finsupp.weight hypBCountWeight e) • (v ⊗ₜ[ℂ] monomial e 1) ∈
      hypTensorFiltered (Finsupp.weight hypBCountWeight e) (Finsupp.weight hypBLevelWeight e) := by
  have h := hypTensorNegative_word_leading D κ ell 0 0 v _
    (hypOneFamily_bHomogeneous_zero _ (hypAExponent_oneFamily e 1)) (hypCanonicalBWord e)
  rw [hypCanonicalBWord_factorization, (hypCanonicalBWord_degrees e).1,
    (hypCanonicalBWord_degrees e).2] at h
  simpa only [hypTensorPBWMap_monomial, Nat.add_zero] using h

end VOA.Moonshine.ConwayNorton
