import VOA.DeligneAudit.D4CharDemazureConvolution

/-! The full all-n Demazure character as a four-part Gaussian GT sum. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open DeligneCharacter VOA.DeligneGaussian

noncomputable section

/-- Reindex the entire four-part convolution by the existing multinomial index set. -/
theorem rsFour_sum {A : Type*} [AddCommMonoid A] (n : ℕ) (f : (Fin 4 → ℕ) → A) :
    (∑ c ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (n - c + 1),
      ∑ b ∈ Finset.range (n - c - a + 1), f ![a, b, n - c - a - b, c]) =
      ∑ t ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) n, f t := by
  classical
  simp_rw [Finset.sum_sigma']
  have hm (t : Fin 4 → ℕ) :
      t ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) n ↔
        t 0 + t 1 + t 2 + t 3 = n := by
    simp [Finset.mem_piAntidiag, Fin.sum_univ_four]
  refine Finset.sum_bij' (fun z _ => ![z.2.1, z.2.2, n - z.1 - z.2.1 - z.2.2, z.1])
    (fun t _ => ⟨t 3, ⟨t 0, t 1⟩⟩) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_sigma, Finset.mem_range] at hz
    rw [hm]
    change z.2.1 + z.2.2 + (n - z.1 - z.2.1 - z.2.2) + z.1 = n
    omega
  · intro t ht
    have ht := (hm t).mp ht
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · intro z _
    rfl
  · intro t ht
    have ht := (hm t).mp ht
    ext i
    fin_cases i <;> simp <;> omega
  · intro z _
    rfl

/-- The same multinomial as qmultiPoly, evaluated at the actual nome. -/
def rsMultinomial (t : Fin 4 → ℕ) : D4K.Kq :=
  qbinom D4K.qq (∑ i, t i) (t 3) *
    qbinom D4K.qq (t 0 + t 1 + t 2) (t 2) *
    qbinom D4K.qq (t 0 + t 1) (t 0)

theorem rsMultinomial_poch (t : Fin 4 → ℕ) :
    rsMultinomial t *
      (D4K.qpoch (t 0) * D4K.qpoch (t 1) * D4K.qpoch (t 2) * D4K.qpoch (t 3)) =
        D4K.qpoch (∑ i, t i) := by
  have h₁ := CarrierChain.qbinom_mul_qpochGen D4K.qq
    (t 0 + t 1 + t 2 + t 3) (t 3) (by omega)
  have h₂ := CarrierChain.qbinom_mul_qpochGen D4K.qq
    (t 0 + t 1 + t 2) (t 2) (by omega)
  have h₃ := CarrierChain.qbinom_mul_qpochGen D4K.qq (t 0 + t 1) (t 0) (by omega)
  change qbinom D4K.qq _ _ * D4K.qpoch _ * D4K.qpoch _ = D4K.qpoch _ at h₁ h₂ h₃
  simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left] at h₁ h₂ h₃
  simp only [rsMultinomial, Fin.sum_univ_four]
  calc
    _ = qbinom D4K.qq (t 0 + t 1 + t 2 + t 3) (t 3) * D4K.qpoch (t 3) *
        (qbinom D4K.qq (t 0 + t 1 + t 2) (t 2) * D4K.qpoch (t 2) *
          (qbinom D4K.qq (t 0 + t 1) (t 0) * D4K.qpoch (t 0) * D4K.qpoch (t 1))) := by
      ring
    _ = _ := by rw [h₃, h₂, h₁]

/-- Cancellation of the four original inverse Pochhammers gives precisely qmultiPoly. -/
theorem rsMultinomial_inverse (t : Fin 4 → ℕ) :
    D4K.qpoch (∑ i, t i) * ((D4K.qpoch (t 3))⁻¹ *
      ((D4K.qpoch (t 0))⁻¹ * (D4K.qpoch (t 1))⁻¹ * (D4K.qpoch (t 2))⁻¹)) =
        rsMultinomial t := by
  rw [← rsMultinomial_poch t]
  field_simp [D4K.qpoch_ne_zero]

/-- Theorem A, retaining every Laurent weight and every q-degree. -/
theorem rsCdem_eq_gt_sum (n : ℕ) :
    D4K.Cdem n =
      ∑ t ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) n,
        rsMultinomial t • gtEval rsNome rsZAlphabet 4
          (gtMixedFourRow ((t 0 + t 1 : ℕ) : ℤ) (t 1)
            ((t 0 + t 2 : ℕ) : ℤ) (t 2)) := by
  have hh := congrArg (fun z : D4K.R => D4K.qpoch n • z) (rsCdem_convolution n)
  dsimp only at hh
  rw [smul_smul, mul_inv_cancel₀ (D4K.qpoch_ne_zero n), one_smul] at hh
  simp only [Finset.smul_sum, smul_smul] at hh
  have hr := rsFour_sum n (fun t =>
    (D4K.qpoch n * ((D4K.qpoch (t 3))⁻¹ *
      ((D4K.qpoch (t 0))⁻¹ * (D4K.qpoch (t 1))⁻¹ * (D4K.qpoch (t 2))⁻¹))) •
        gtEval rsNome rsZAlphabet 4
          (gtMixedFourRow ((t 0 + t 1 : ℕ) : ℤ) (t 1)
            ((t 0 + t 2 : ℕ) : ℤ) (t 2)))
  rw [hh]
  refine hr.trans ?_
  apply Finset.sum_congr rfl
  intro t ht
  have ht := (Finset.mem_piAntidiag.mp ht).1
  rw [← ht, rsMultinomial_inverse]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsFour_sum
#print axioms VOA.DeligneAudit.D4Char.rsMultinomial_poch
#print axioms VOA.DeligneAudit.D4Char.rsMultinomial_inverse
#print axioms VOA.DeligneAudit.D4Char.rsCdem_eq_gt_sum
