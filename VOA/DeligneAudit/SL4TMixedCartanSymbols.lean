import VOA.DeligneAudit.SL4TMixedRelativePresentation
import VOA.DeligneAudit.SL4TMixedPowerSum

/-! The mixed characteristic power sums as differences of the five alphabet power sums. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- The signed coefficient series of an abstract mixed alphabet under specialization. -/
def mixedSignedSeries (φ : MixedPoly →ₐ[ℂ] R) (f : ℕ → MixedPoly) : PowerSeries R :=
  PowerSeries.mk (fun n => (-1) ^ n * φ (f n))

/-- Power sums of any of the five elementary alphabets, before or after a quotient. -/
def mixedAlphabetPowerSum (φ : MixedPoly →ₐ[ℂ] R) (i : Fin 5) (d : ℕ) : ℕ → R :=
  powerSumOfCoeff d (fun n => (-1) ^ n * φ (mixedE i n))

/-- Signed coefficient convolution is multiplication of formal series. -/
theorem mixedSignedSeries_convolution (φ : MixedPoly →ₐ[ℂ] R) (f g : ℕ → MixedPoly) :
    mixedSignedSeries φ (mixedConv f g) = mixedSignedSeries φ f * mixedSignedSeries φ g := by
  ext n : 1
  simp only [mixedSignedSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mixedConv,
    map_sum, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i + (n - i) = n := by have := Finset.mem_range.mp hi; omega
  calc
    _ = ((-1 : R) ^ i * (-1) ^ (n - i)) * (φ (f i) * φ (g (n - i))) := by
      rw [← pow_add, hin]
    _ = _ := by ring

/-- The signed complete complement has the ordinary complete series. -/
theorem mixedSignedSeries_complete (φ : MixedPoly →ₐ[ℂ] R) (i : Fin 5) :
    mixedSignedSeries φ (fun n => (-1) ^ n * mixedH i n) =
      PowerSeries.mk (fun n => φ (mixedH i n)) := by
  ext n : 1
  simp only [mixedSignedSeries, PowerSeries.coeff_mk, map_mul, map_pow, map_neg, map_one]
  rw [← mul_assoc, ← mul_pow]
  simp

/-- Newton reconstruction of an elementary alphabet gives its signed series. -/
theorem newtonCoefficientSeries_mixedAlphabet (φ : MixedPoly →ₐ[ℂ] R)
    (i : Fin 5) (d : ℕ) :
    newtonCoefficientSeries (mixedAlphabetPowerSum φ i d) = mixedSignedSeries φ (mixedE i) := by
  ext n : 1
  simp only [newtonCoefficientSeries, mixedSignedSeries, PowerSeries.coeff_mk,
    mixedAlphabetPowerSum]
  exact newtonCoeff_powerSumOfCoeff d _ (by simp [mixedE]) n

/-- Subtracting an elementary alphabet divides its elementary series. -/
theorem newtonCoefficientSeries_relativeAlphabet (φ : MixedPoly →ₐ[ℂ] R)
    (u : ℕ → MixedPoly) (i : Fin 5) (d : ℕ) (p : ℕ → R)
    (hp : newtonCoefficientSeries p = mixedSignedSeries φ u) :
    newtonCoefficientSeries (fun s => p s - mixedAlphabetPowerSum φ i d s) =
      mixedSignedSeries φ (mixedConv u (fun n => (-1) ^ n * mixedH i n)) := by
  simp only [sub_eq_add_neg]
  rw [newtonCoefficientSeries_add, hp, mixedSignedSeries_convolution,
    mixedSignedSeries_complete]
  congr 1
  apply newtonCoefficientSeries_neg_of_inverse
  rw [newtonCoefficientSeries_mixedAlphabet]
  exact specializedElementary_complete_inverse (φ.comp (mixedAlphabet i))

/-- The relative base power sums recover the two mixed ambient series. -/
theorem newtonCoefficientSeries_mixedAmbient (φ : MixedPoly →ₐ[ℂ] R)
    (i j : Fin 5) (d e : ℕ) :
    newtonCoefficientSeries
        (fun s => mixedAlphabetPowerSum φ i d s - mixedAlphabetPowerSum φ j e s) =
      mixedSignedSeries φ (mixedConv (mixedE i) (fun n => (-1) ^ n * mixedH j n)) := by
  ext n : 1
  simp only [newtonCoefficientSeries, mixedSignedSeries, PowerSeries.coeff_mk,
    mixedAlphabetPowerSum]
  exact mixedAmbient_newtonCoeff φ i j d e n

/-- The last Cartan combines the first lowering alphabet and the second complementary one. -/
def mixedLastCartanPowerSum (φ : MixedPoly →ₐ[ℂ] R) (d₂ d₃ e₁ e₂ : ℕ) (s : ℕ) : R :=
  mixedAlphabetPowerSum φ 3 e₁ s +
    (mixedAlphabetPowerSum φ 1 d₂ s - mixedAlphabetPowerSum φ 2 d₃ s -
      mixedAlphabetPowerSum φ 4 e₂ s)

/-- The last Cartan power sums reconstruct the full mixed characteristic series. -/
theorem newtonCoefficientSeries_mixedLastCartan (φ : MixedPoly →ₐ[ℂ] R)
    (d₂ d₃ e₁ e₂ : ℕ) :
    newtonCoefficientSeries (mixedLastCartanPowerSum φ d₂ d₃ e₁ e₂) =
      mixedSignedSeries φ (mixedE 3) * mixedSignedSeries φ mixedG2prime := by
  unfold mixedLastCartanPowerSum
  rw [newtonCoefficientSeries_add, newtonCoefficientSeries_mixedAlphabet]
  congr 1
  exact newtonCoefficientSeries_relativeAlphabet φ mixedV 4 e₂ _
    (newtonCoefficientSeries_mixedAmbient φ 1 2 d₂ d₃)

/-- The finite mixed coefficient polynomial has the same full series as the last Cartan. -/
theorem mixedLastCartan_newtonCoeff (q : MixedParams) (hq : MixedValid q) (n : ℕ) :
    newtonCoeff (mixedLastCartanPowerSum (mixedEvaluation q)
        q.d2.toNat q.d3.toNat q.e1.toNat q.e2.toNat) n =
      (mixedCoefficientSeries q).coeff n := by
  have he := congrArg (PowerSeries.coeff n)
    (newtonCoefficientSeries_mixedLastCartan (mixedEvaluation q)
      q.d2.toNat q.d3.toNat q.e1.toNat q.e2.toNat)
  simp only [newtonCoefficientSeries, mixedSignedSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_mul] at he
  rw [he]
  simp only [mixedCoefficientSeries, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [coefficientPoly_coeff_of_tail _ q.e1.toNat (by
    intro k hk
    have hz : mixedEvaluation q (mixedE 3 k) = 0 := mixedRelation_zero q hq _
      (Or.inl ⟨3, k, by simpa [mixedLengths] using hk, rfl⟩)
    rw [hz, mul_zero]), coefficientPoly_coeff_of_tail _ (mixedQ q - q.e2).toNat (by
    intro k hk
    rw [mixedG2prime_tail q hq k hk]
    simp)]

/-- The power sums used in the mixed block bound are precisely the retained Cartan symbols. -/
theorem mixedPowerSum_eq_lastCartan (q : MixedParams) (hq : MixedValid q)
    (s : ℕ) (hs : 0 < s) :
    mixedPowerSum q s = mixedLastCartanPowerSum (mixedEvaluation q)
      q.d2.toNat q.d3.toNat q.e1.toNat q.e2.toNat s := by
  unfold mixedPowerSum
  rw [← funext (mixedLastCartan_newtonCoeff q hq)]
  exact powerSumOfCoeff_newtonCoeff _ _ s hs

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedSignedSeries_convolution
#print axioms VOA.DeligneAudit.SL4T.mixedSignedSeries_complete
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_mixedAlphabet
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_relativeAlphabet
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_mixedAmbient
#print axioms VOA.DeligneAudit.SL4T.newtonCoefficientSeries_mixedLastCartan
#print axioms VOA.DeligneAudit.SL4T.mixedLastCartan_newtonCoeff
#print axioms VOA.DeligneAudit.SL4T.mixedPowerSum_eq_lastCartan
