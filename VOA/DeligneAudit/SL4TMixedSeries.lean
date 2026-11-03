import VOA.DeligneAudit.SL4TMixedStateQuotient
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Convolution and top-coefficient identities for mixed alphabets -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Multiplication of formal series is the coefficient convolution used by the mixed rings. -/
theorem mixedConv_series (f g : ℕ → MixedPoly) :
    PowerSeries.mk (mixedConv f g) = PowerSeries.mk f * PowerSeries.mk g := by
  ext n : 1
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk, mixedConv]

/-- The elementary and complete series, with their usual signs, are inverse. -/
theorem mixedAlphabet_series_inverse (i : Fin 5) :
    PowerSeries.mk (mixedE i) *
      PowerSeries.mk (fun n => (-1) ^ n * mixedH i n) = 1 := by
  have hs : PowerSeries.mk (fun n => (-1) ^ n * mixedE i n) *
      PowerSeries.mk (mixedH i) = 1 := by
    ext n : 1
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk]
    by_cases hn : n = 0
    · subst n
      simp [mixedE, mixedH]
    · have h := congrArg (mixedAlphabet i) (complete_relation n (by omega))
      simpa [mixedE, mixedH, PowerSeries.coeff_one, hn] using h
  have h := congrArg (PowerSeries.rescale (-1 : MixedPoly)) hs
  simp only [map_mul, map_one, PowerSeries.rescale_mk] at h
  have he : (fun n => (-1 : MixedPoly) ^ n * ((-1) ^ n * mixedE i n)) = mixedE i := by
    funext n
    rw [← mul_assoc, ← mul_pow]
    simp
  rw [he] at h
  exact h

/-- Multiplying the first relative complement by its alphabet recovers its ambient series. -/
theorem mixedG1prime_convolution (n : ℕ) :
    mixedConv (mixedE 3) mixedG1prime n = mixedU n := by
  have h : PowerSeries.mk (mixedConv (mixedE 3) mixedG1prime) =
      PowerSeries.mk mixedU := by
    rw [mixedConv_series, mixedG1prime, mixedConv_series]
    calc
      _ = PowerSeries.mk mixedU *
          (PowerSeries.mk (mixedE 3) *
            PowerSeries.mk (fun n => (-1) ^ n * mixedH 3 n)) := by ring
      _ = _ := by rw [mixedAlphabet_series_inverse, mul_one]
  simpa only [PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff n) h

/-- The analogous convolution for the second relative complement. -/
theorem mixedG2prime_convolution (n : ℕ) :
    mixedConv (mixedE 4) mixedG2prime n = mixedV n := by
  have h : PowerSeries.mk (mixedConv (mixedE 4) mixedG2prime) =
      PowerSeries.mk mixedV := by
    rw [mixedConv_series, mixedG2prime, mixedConv_series]
    calc
      _ = PowerSeries.mk mixedV *
          (PowerSeries.mk (mixedE 4) *
            PowerSeries.mk (fun n => (-1) ^ n * mixedH 4 n)) := by ring
      _ = _ := by rw [mixedAlphabet_series_inverse, mul_one]
  simpa only [PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff n) h

/-- The top convolution isolates one product using only the finite relative window. -/
theorem mixedConv_top {R : Type*} [CommRing R] (φ : MixedPoly →+* R)
    (f g : ℕ → MixedPoly) (d w : ℕ)
    (hf : ∀ j, d < j → φ (f j) = 0)
    (hg : ∀ j, w < j → j ≤ d + w → φ (g j) = 0) :
    φ (mixedConv f g (d + w)) = φ (f d) * φ (g w) := by
  simp only [mixedConv, map_sum, map_mul]
  rw [Finset.sum_eq_single d]
  · rw [Nat.add_sub_cancel_left]
  · intro j hj hne
    by_cases hd : d < j
    · rw [hf j hd, zero_mul]
    · rw [hg (d + w - j) (by omega) (by omega), mul_zero]
  · intro hd
    exact False.elim (hd (Finset.mem_range.mpr (by omega)))

/-- The first relative top coefficient product, for every valid mixed tuple. -/
theorem mixedG1prime_top (q : MixedParams) (hq : MixedValid q) :
    mixedEvaluation q (mixedE 3 q.e1.toNat) *
        mixedEvaluation q (mixedG1prime (mixedP q - q.e1).toNat) =
      mixedEvaluation q (mixedU (mixedP q).toNat) := by
  have hp : q.e1.toNat + (mixedP q - q.e1).toNat = (mixedP q).toNat := by
    obtain ⟨_, _, _, _, _, _, _, _, he, hp, _, _⟩ := hq
    omega
  rw [← hp, ← mixedG1prime_convolution]
  apply (mixedConv_top (mixedEvaluation q).toRingHom _ _ _ _ ?_ ?_).symm
  · intro j hj
    exact mixedRelation_zero q hq _ (Or.inl ⟨3, j, by simpa [mixedLengths] using hj, rfl⟩)
  · intro j hj hu
    apply mixedRelation_zero q hq
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, by omega, rfl⟩))))

/-- The second relative top coefficient product, for every valid mixed tuple. -/
theorem mixedG2prime_top (q : MixedParams) (hq : MixedValid q) :
    mixedEvaluation q (mixedE 4 q.e2.toNat) *
        mixedEvaluation q (mixedG2prime (mixedQ q - q.e2).toNat) =
      mixedEvaluation q (mixedV (mixedQ q).toNat) := by
  have hp : q.e2.toNat + (mixedQ q - q.e2).toNat = (mixedQ q).toNat := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, he, hp⟩ := hq
    omega
  rw [← hp, ← mixedG2prime_convolution]
  apply (mixedConv_top (mixedEvaluation q).toRingHom _ _ _ _ ?_ ?_).symm
  · intro j hj
    exact mixedRelation_zero q hq _ (Or.inl ⟨4, j, by simpa [mixedLengths] using hj, rfl⟩)
  · intro j hj hu
    apply mixedRelation_zero q hq
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, hj, by omega, rfl⟩))))

/-- An alphabet with no elementary generators has no positive complete functions. -/
theorem mixedComplete_zero_of_empty (q : MixedParams) (hq : MixedValid q)
    (i : Fin 5) (hi : mixedLengths q i = 0) (n : ℕ) (hn : 0 < n) :
    mixedEvaluation q (mixedH i n) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [mixedH, complete_succ, map_neg, map_sum, map_mul, map_pow, map_one]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro j _
  have he : mixedEvaluation q (mixedE i (j + 1)) = 0 :=
    mixedRelation_zero q hq _ (Or.inl ⟨i, j + 1, by rw [hi]; omega, rfl⟩)
  change _ * mixedEvaluation q (mixedE i (j + 1)) * _ = 0
  rw [he, mul_zero, zero_mul]

/-- Once all b-sites have been removed, the first ambient alphabet is `x1`. -/
theorem mixedU_without_b_sites (q : MixedParams) (hq : MixedValid q)
    (hB : q.B = 0) (n : ℕ) :
    mixedEvaluation q (mixedU n) = mixedEvaluation q (mixedE 0 n) := by
  have hd : q.d2 = 0 := by obtain ⟨_, _, _, _, h, h', _⟩ := hq; omega
  simp only [mixedU, mixedConv, map_sum, map_mul, map_pow, map_neg, map_one]
  rw [Finset.sum_eq_single n]
  · simp [mixedH]
  · intro j hj hne
    have hj' := Finset.mem_range.mp hj
    rw [mixedComplete_zero_of_empty q hq 1 (by simp [mixedLengths, hd])
      (n - j) (by omega), mul_zero, mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

/-- Once all b-sites have been removed, the second ambient alphabet complements `x3`. -/
theorem mixedV_without_b_sites (q : MixedParams) (hq : MixedValid q)
    (hB : q.B = 0) (n : ℕ) :
    mixedEvaluation q (mixedV n) = (-1) ^ n * mixedEvaluation q (mixedH 2 n) := by
  have hd : q.d2 = 0 := by obtain ⟨_, _, _, _, h, h', _⟩ := hq; omega
  simp only [mixedV, mixedConv, map_sum, map_mul, map_pow, map_neg, map_one]
  rw [Finset.sum_eq_single 0]
  · simp [mixedE]
  · intro j _ hne
    have he : mixedEvaluation q (mixedE 1 j) = 0 :=
      mixedRelation_zero q hq _ (Or.inl ⟨1, j, by simp [mixedLengths, hd]; omega, rfl⟩)
    rw [he, zero_mul]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

/-- The first top-coefficient product at an a-site. -/
theorem mixedFirst_top_without_b_sites (q : MixedParams) (hq : MixedValid q)
    (hB : q.B = 0) :
    mixedEvaluation q (mixedE 3 q.e1.toNat) *
        mixedEvaluation q (mixedG1prime (mixedP q - q.e1).toNat) =
      mixedEvaluation q (mixedE 0 q.d1.toNat) := by
  have hd : q.d2 = 0 := by obtain ⟨_, _, _, _, h, h', _⟩ := hq; omega
  rw [mixedG1prime_top q hq, mixedU_without_b_sites q hq hB]
  simp [mixedP, hB, hd]

/-- The second top-coefficient product at an a-site, including its sign. -/
theorem mixedSecond_top_without_b_sites (q : MixedParams) (hq : MixedValid q)
    (hB : q.B = 0) :
    mixedEvaluation q (mixedE 4 q.e2.toNat) *
        mixedEvaluation q (mixedG2prime (mixedQ q - q.e2).toNat) =
      (-1) ^ (q.A - q.d3).toNat * mixedEvaluation q (mixedH 2 (q.A - q.d3).toNat) := by
  have hd : q.d2 = 0 := by obtain ⟨_, _, _, _, h, h', _⟩ := hq; omega
  rw [mixedG2prime_top q hq, mixedV_without_b_sites q hq hB]
  simp [mixedQ, hd]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedConv_series
#print axioms VOA.DeligneAudit.SL4T.mixedAlphabet_series_inverse
#print axioms VOA.DeligneAudit.SL4T.mixedG1prime_convolution
#print axioms VOA.DeligneAudit.SL4T.mixedG2prime_convolution
#print axioms VOA.DeligneAudit.SL4T.mixedConv_top
#print axioms VOA.DeligneAudit.SL4T.mixedG1prime_top
#print axioms VOA.DeligneAudit.SL4T.mixedG2prime_top

#print axioms VOA.DeligneAudit.SL4T.mixedComplete_zero_of_empty
#print axioms VOA.DeligneAudit.SL4T.mixedU_without_b_sites
#print axioms VOA.DeligneAudit.SL4T.mixedV_without_b_sites
#print axioms VOA.DeligneAudit.SL4T.mixedFirst_top_without_b_sites
#print axioms VOA.DeligneAudit.SL4T.mixedSecond_top_without_b_sites
