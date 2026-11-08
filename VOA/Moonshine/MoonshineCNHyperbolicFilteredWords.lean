import VOA.Moonshine.MoonshineCNHyperbolicFiltration
import VOA.Moonshine.MoonshineCNHyperbolicOneFamily
import VOA.Moonshine.MoonshineCNStringStraightening

/-! # Filtered negative words

The remainder estimate is stable under iteration. No nonzero-momentum
assumption is needed until the leading coefficient is used for invertibility.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped BigOperators

theorem hypBFiltered_mul_b (j d w : ℕ) (p : hypFock) (hp : p ∈ hypBFiltered d w) :
    X (j, 1) * p ∈ hypBFiltered (d + 1) (w + j + 1) := by
  classical
  rw [p.as_sum, Finset.mul_sum]
  apply Submodule.sum_mem
  intro e he
  apply hypBFiltered_of_homogeneous
    (hypBHomogeneous_mul (hypBHomogeneous_X (j, 1)) (hypBHomogeneous_monomial e _))
  have hs := (hypBFiltered_mem d w p).mp hp e (mem_support_iff.mp he)
  simp only [hypBCountWeight, hypBLevelWeight, if_true]
  omega

theorem hypSugawara_negative_filtered (κ ell : ℂ) (j d w : ℕ)
    (p : hypFock) (hp : p ∈ hypBFiltered d w) :
    hypSugawara κ ell (-(j + 1 : ℤ)) p ∈ hypBFiltered (d + 1) (w + j + 1) := by
  classical
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro e he
  have hs := (hypBFiltered_mem d w p).mp hp e (mem_support_iff.mp he)
  have hl := hypSugawara_negative_leading_filtered κ ell j _ _
    (monomial e (coeff e p)) (hypBHomogeneous_monomial e _)
  have hl' : hypSugawara κ ell (-(j + 1 : ℤ)) (monomial e (coeff e p)) -
      κ • (X (j, 1) * monomial e (coeff e p)) ∈
      hypBFiltered (d + 1) (w + j + 1) :=
    hypBFiltered_mono (by omega) hl
  have hm : monomial e (coeff e p) ∈ hypBFiltered d w :=
    hypBFiltered_of_homogeneous (hypBHomogeneous_monomial e _) hs
  have ha := (hypBFiltered (d + 1) (w + j + 1)).add_mem hl'
    ((hypBFiltered (d + 1) (w + j + 1)).smul_mem κ (hypBFiltered_mul_b j d w _ hm))
  simpa only [sub_add_cancel] using ha

def hypBWordMonomial (w : List ℕ) : hypFock := (w.map fun i => X (i, 1)).prod

theorem hypBWordMonomial_homogeneous (w : List ℕ) :
    hypBWordMonomial w ∈ hypBHomogeneous w.length (stringWordEnergy w) := by
  induction w with
  | nil => exact ⟨isWeightedHomogeneous_one _ _, isWeightedHomogeneous_one _ _⟩
  | cons i w ih =>
    have h := hypBHomogeneous_mul (hypBHomogeneous_X (i, 1)) ih
    simpa [hypBWordMonomial, hypBCountWeight, hypBLevelWeight,
      stringWordEnergy_cons, Nat.add_comm] using h

/-- The iterated strict leading-term estimate, for any homogeneous base. -/
theorem hypSugawara_negative_word_leading (κ ell : ℂ) (d w : ℕ)
    (p : hypFock) (hp : p ∈ hypBHomogeneous d w) (v : List ℕ) :
    stringNegativeWord (fun i => hypSugawara κ ell (-(i + 1 : ℤ))) p v -
      κ ^ v.length • (hypBWordMonomial v * p) ∈
      hypBFiltered (v.length + d) (stringWordEnergy v + w) := by
  induction v with
  | nil => simp [stringNegativeWord, hypBWordMonomial, stringWordEnergy]
  | cons i v ih =>
    have h₁ := hypSugawara_negative_filtered κ ell i _ _ _ ih
    have h₂ := (hypBFiltered (v.length + d + 1) (stringWordEnergy v + w + i + 1)).smul_mem
      (κ ^ v.length) (hypSugawara_negative_leading_filtered κ ell i _ _ _
        (hypBHomogeneous_mul (hypBWordMonomial_homogeneous v) hp))
    have h := (hypBFiltered (v.length + d + 1)
      (stringWordEnergy v + w + i + 1)).add_mem h₁ h₂
    have he : hypSugawara κ ell (-(i + 1 : ℤ))
        (stringNegativeWord (fun j => hypSugawara κ ell (-(j + 1 : ℤ))) p v -
          κ ^ v.length • (hypBWordMonomial v * p)) +
        κ ^ v.length • (hypSugawara κ ell (-(i + 1 : ℤ)) (hypBWordMonomial v * p) -
          κ • (X (i, 1) * (hypBWordMonomial v * p))) =
        stringNegativeWord (fun j => hypSugawara κ ell (-(j + 1 : ℤ))) p (i :: v) -
          κ ^ (i :: v).length • (hypBWordMonomial (i :: v) * p) := by
      simp only [map_sub, map_smul, smul_sub, smul_smul, stringNegativeWord,
        List.length_cons, pow_succ, hypBWordMonomial, List.map_cons, List.prod_cons,
        mul_assoc]
      abel
    rw [he] at h
    convert h using 1
    simp only [List.length_cons, stringWordEnergy_cons]
    congr 1 <;> omega

theorem hypOneFamily_bHomogeneous_zero (p : hypFock) (hp : p ∈ hypOneFamily 0) :
    p ∈ hypBHomogeneous 0 0 := by
  rw [hypOneFamily_eq_range, LinearMap.mem_range] at hp
  obtain ⟨f, rfl⟩ := hp
  induction f using MvPolynomial.induction_on with
  | C c =>
    simpa only [AlgHom.toLinearMap_apply, rename_C] using
      And.intro (isWeightedHomogeneous_C hypBCountWeight c)
        (isWeightedHomogeneous_C hypBLevelWeight c)
  | add f g hf hg =>
    simpa only [map_add] using (hypBHomogeneous 0 0).add_mem hf hg
  | mul_X f j hf =>
    simpa [hypBCountWeight, hypBLevelWeight] using
      hypBHomogeneous_mul hf (hypBHomogeneous_X (j, 0))

/-- Blueprint (F1b) on the actual b-free polynomial subspace. -/
theorem hypSugawara_negative_word_leading_oneFamily (κ ell : ℂ)
    (p : hypFock) (hp : p ∈ hypOneFamily 0) (v : List ℕ) :
    stringNegativeWord (fun i => hypSugawara κ ell (-(i + 1 : ℤ))) p v -
      κ ^ v.length • (hypBWordMonomial v * p) ∈
      hypBFiltered v.length (stringWordEnergy v) := by
  simpa only [Nat.add_zero] using hypSugawara_negative_word_leading κ ell 0 0 p
    (hypOneFamily_bHomogeneous_zero p hp) v

end VOA.Moonshine.ConwayNorton
