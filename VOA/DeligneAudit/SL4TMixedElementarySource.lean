import VOA.DeligneAudit.SL4TSecondLeviRelativeQuotient
import VOA.DeligneAudit.SL4TNewtonSeries
import VOA.DeligneAudit.SL4TMixed

/-! Elementary generators for the two symmetric mode alphabets and their Grassmannian base. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial
open scoped TensorProduct

attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {B : Type} [CommRing B] [Algebra ℂ B]

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Elementary functions in either lowering alphabet are separately symmetric. -/
theorem secondLeviElementary_symmetric (e₁ e₂ : ℕ) (j : Fin 2) (s : ℕ) :
    (if j = 0 then rename Sum.inl (esymm (Fin e₁) B s)
      else rename Sum.inr (esymm (Fin e₂) B s)) ∈ secondLeviSymmetricModes e₁ e₂ := by
  intro e
  by_cases hj : j = 0
  · simp only [if_pos hj, rename_rename]
    have he : (secondLeviSlotPermutation e₁ e₂ e : _ → _) ∘ Sum.inl =
        Sum.inl ∘ e.1 := rfl
    rw [he, ← rename_rename, rename_esymm]
  · simp only [if_neg hj, rename_rename]
    have he : (secondLeviSlotPermutation e₁ e₂ e : _ → _) ∘ Sum.inr =
        Sum.inr ∘ e.2 := rfl
    rw [he, ← rename_rename, rename_esymm]

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Abstract elementary generators specialize to either symmetric lowering alphabet. -/
def secondLeviElementaryAlphabet (e₁ e₂ : ℕ) (j : Fin 2) :
    SymPoly →ₐ[ℂ] secondLeviSymmetricModes (B := B) e₁ e₂ :=
  aeval fun s => ⟨if j = 0 then rename Sum.inl (esymm (Fin e₁) B (s + 1))
    else rename Sum.inr (esymm (Fin e₂) B (s + 1)),
    secondLeviElementary_symmetric e₁ e₂ j (s + 1)⟩

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
theorem secondLeviElementaryAlphabet_elementary (e₁ e₂ : ℕ) (j : Fin 2) (s : ℕ) :
    (secondLeviElementaryAlphabet (B := B) e₁ e₂ j (elementary s)).val =
      if j = 0 then rename Sum.inl (esymm (Fin e₁) B s)
        else rename Sum.inr (esymm (Fin e₂) B s) := by
  cases s with
  | zero => simp [elementary, esymm_zero]
  | succ s => simp [secondLeviElementaryAlphabet, elementary]

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
theorem secondLeviElementaryAlphabet_complete (e₁ e₂ : ℕ) (j : Fin 2) (s : ℕ) :
    (secondLeviElementaryAlphabet (B := B) e₁ e₂ j (complete s)).val =
      if j = 0 then rename Sum.inl (hsymm (Fin e₁) B s)
        else rename Sum.inr (hsymm (Fin e₂) B s) := by
  have first : (secondLeviSymmetricModes e₁ e₂).val.comp
        (secondLeviElementaryAlphabet (B := B) e₁ e₂ 0) =
      ((rename Sum.inl).restrictScalars ℂ).comp
        ((mapAlgHom (Algebra.ofId ℂ B)).comp (elementarySpecialization e₁)) := by
    ext n
    simp [secondLeviElementaryAlphabet, elementarySpecialization, map_esymm]
  have second : (secondLeviSymmetricModes e₁ e₂).val.comp
        (secondLeviElementaryAlphabet (B := B) e₁ e₂ 1) =
      ((rename Sum.inr).restrictScalars ℂ).comp
        ((mapAlgHom (Algebra.ofId ℂ B)).comp (elementarySpecialization e₂)) := by
    ext n
    simp [secondLeviElementaryAlphabet, elementarySpecialization, map_esymm]
  fin_cases j
  · have he := AlgHom.congr_fun first (complete s)
    simpa [elementarySpecialization_complete, map_hsymm] using he
  · have he := AlgHom.congr_fun second (complete s)
    simpa [elementarySpecialization_complete, map_hsymm] using he

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Constants as elements of the separately symmetric source. -/
def secondLeviSymmetricBase (e₁ e₂ : ℕ) :
    B →ₐ[ℂ] secondLeviSymmetricModes (B := B) e₁ e₂ :=
  (secondLeviBaseEmbedding e₁ e₂).codRestrict _ (fun b e => rename_C _ b)

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The three elementary-generator maps into the Grassmannian coefficient algebra. -/
def radicalGrassmannianAlphabet (a b c : ℕ) (d : Fin 3 → ℕ) (j : Fin 3) :
    SymPoly →ₐ[ℂ] RadicalGrassmannianRing a b c d :=
  match j with
  | 0 => Algebra.TensorProduct.includeLeft.comp (Ideal.Quotient.mkₐ ℂ _)
  | 1 => Algebra.TensorProduct.includeRight.comp
      (Algebra.TensorProduct.includeLeft.comp (Ideal.Quotient.mkₐ ℂ _))
  | 2 => Algebra.TensorProduct.includeRight.comp
      (Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ ℂ _))

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- All elementary tails already vanish in the coefficient algebra. -/
theorem radicalGrassmannianAlphabet_elementary_tail (a b c : ℕ) (d : Fin 3 → ℕ)
    (j : Fin 3) (s : ℕ) (hs : d j < s) :
    radicalGrassmannianAlphabet a b c d j (elementary s) = 0 := by
  fin_cases j
  · simp only [radicalGrassmannianAlphabet, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [show Ideal.Quotient.mk _ (elementary s) = 0 from
      eClass_eq_zero (d 0) (a - d 0) s hs, map_zero]
  · simp only [radicalGrassmannianAlphabet, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [show Ideal.Quotient.mk _ (elementary s) = 0 from
      eClass_eq_zero (d 1) (b - d 1) s hs, map_zero, map_zero]
  · simp only [radicalGrassmannianAlphabet, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [show Ideal.Quotient.mk _ (elementary s) = 0 from
      eClass_eq_zero (d 2) (c - d 2) s hs, map_zero, map_zero]

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- All complete tails already vanish in the coefficient algebra. -/
theorem radicalGrassmannianAlphabet_complete_tail (a b c : ℕ) (d : Fin 3 → ℕ)
    (j : Fin 3) (s : ℕ) (hs : A3Sector.weightABC a b c j - d j < s) :
    radicalGrassmannianAlphabet a b c d j (complete s) = 0 := by
  fin_cases j <;>
    simp only [radicalGrassmannianAlphabet, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  · rw [show Ideal.Quotient.mk _ (complete s) = 0 from
      hClass_eq_zero (d 0) (a - d 0) s hs, map_zero]
  · rw [show Ideal.Quotient.mk _ (complete s) = 0 from
      hClass_eq_zero (d 1) (b - d 1) s hs, map_zero, map_zero]
  · rw [show Ideal.Quotient.mk _ (complete s) = 0 from
      hClass_eq_zero (d 2) (c - d 2) s hs, map_zero, map_zero]

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Coefficient power sums are inverse Newton sums of the embedded elementary generators. -/
theorem radicalGrassmannianAlphabet_powerSum (a b c : ℕ) (d : Fin 3 → ℕ)
    (j : Fin 3) (s : ℕ) :
    radicalGrassmannianPowerSum a b c d j s =
      powerSumOfCoeff (d j)
        (fun k => (-1) ^ k * radicalGrassmannianAlphabet a b c d j (elementary k)) s := by
  have he := powerSumOfCoeff_map (radicalGrassmannianAlphabet a b c d j) (d j)
    (fun k => (-1) ^ k * elementary k) s
  simp only [map_mul, map_pow, map_neg, map_one] at he
  rw [← he]
  have hbase (n M : ℕ) : grassmannianPowerSum n M s =
      (Ideal.Quotient.mkₐ ℂ (grassIdeal n (M - n)))
        (powerSumOfCoeff n (fun k => (-1) ^ k * elementary k) s) := by
    rw [powerSumOfCoeff_map]
    simp only [grassmannianPowerSum, map_mul, map_pow, map_neg, map_one]
    rfl
  fin_cases j <;>
    simp only [radicalGrassmannianPowerSum, hbase, radicalGrassmannianAlphabet,
      AlgHom.comp_apply]
  all_goals rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The five abstract alphabets map to the Grassmannian base and the two mode alphabets. -/
def mixedElementaryAlphabet (a b c : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) (j : Fin 5) :
    SymPoly →ₐ[ℂ]
      secondLeviSymmetricModes (B := RadicalGrassmannianRing a b c d) e₁ e₂ :=
  match j with
  | 0 => (secondLeviSymmetricBase e₁ e₂).comp (radicalGrassmannianAlphabet a b c d 0)
  | 1 => (secondLeviSymmetricBase e₁ e₂).comp (radicalGrassmannianAlphabet a b c d 1)
  | 2 => (secondLeviSymmetricBase e₁ e₂).comp (radicalGrassmannianAlphabet a b c d 2)
  | 3 => secondLeviElementaryAlphabet e₁ e₂ 0
  | 4 => secondLeviElementaryAlphabet e₁ e₂ 1

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The change of polynomial generators before imposing the relative relations. -/
def mixedElementarySource (a b c : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) :
    MixedPoly →ₐ[ℂ]
      secondLeviSymmetricModes (B := RadicalGrassmannianRing a b c d) e₁ e₂ :=
  aeval fun z => mixedElementaryAlphabet a b c d e₁ e₂ z.1 (X z.2)

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
theorem mixedElementarySource_alphabet (a b c : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (j : Fin 5) (P : SymPoly) :
    mixedElementarySource a b c d e₁ e₂ (mixedAlphabet j P) =
      mixedElementaryAlphabet a b c d e₁ e₂ j P := by
  have he : (mixedElementarySource a b c d e₁ e₂).comp (mixedAlphabet j) =
      mixedElementaryAlphabet a b c d e₁ e₂ j := by
    ext n
    simp [mixedElementarySource, mixedAlphabet]
  exact AlgHom.congr_fun he P

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviElementary_symmetric
#print axioms VOA.DeligneAudit.SL4T.secondLeviElementaryAlphabet_elementary
#print axioms VOA.DeligneAudit.SL4T.secondLeviElementaryAlphabet_complete
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAlphabet_elementary_tail
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAlphabet_complete_tail
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAlphabet_powerSum
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_alphabet
