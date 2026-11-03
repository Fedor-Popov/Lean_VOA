import VOA.DeligneAudit.D4CharKernelProduct

/-! Identification with the original D4 kernel, with its extra scalar Euler factor. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open DeligneCharacter PowerSeries

noncomputable section

theorem rsMixed_numerator :
    ((expand 2 two_ne_zero (gtEulerPos rsNome rsPochhammerUnits
        ((rsXAlphabet 0 : D4K.R) * rsXAlphabet 0)) *
      expand 2 two_ne_zero (gtEulerPos rsNome rsPochhammerUnits
        ((rsXAlphabet 1 : D4K.R) * rsXAlphabet 0))) *
    (expand 2 two_ne_zero (gtEulerPos rsNome rsPochhammerUnits
        ((rsXAlphabet 0 : D4K.R) * rsXAlphabet 1)) *
      expand 2 two_ne_zero (gtEulerPos rsNome rsPochhammerUnits
        ((rsXAlphabet 1 : D4K.R) * rsXAlphabet 1)))) =
      D4K.EPos 1 0 2 two_ne_zero * D4K.tFactors := by
  simp only [rsXAlphabet, if_pos rfl, if_neg (by decide : (1 : ℕ) ≠ 0)]
  change ((expand 2 two_ne_zero (gtEulerPos rsNome rsPochhammerUnits
      (D4K.mon D4K.xv 1 * D4K.mon D4K.xv 1)) *
    expand 2 two_ne_zero (gtEulerPos rsNome rsPochhammerUnits
      (D4K.mon (-D4K.xv) 1 * D4K.mon D4K.xv 1))) *
    (expand 2 two_ne_zero (gtEulerPos rsNome rsPochhammerUnits
      (D4K.mon D4K.xv 1 * D4K.mon (-D4K.xv) 1)) *
    expand 2 two_ne_zero (gtEulerPos rsNome rsPochhammerUnits
      (D4K.mon (-D4K.xv) 1 * D4K.mon (-D4K.xv) 1)))) = _
  simp only [D4K.mon_mul_mon, mul_one, add_neg_cancel, neg_add_cancel,
    rsEulerPos_EPos]
  have hp : D4K.xv + D4K.xv = (2 : ℤ) • D4K.xv := by simp [two_smul]
  have hn : -D4K.xv + -D4K.xv = (-2 : ℤ) • D4K.xv := by simp [two_smul]
  rw [hp, hn, D4K.tFactors]
  ring

theorem rsMixed_hyper_factor (i : ℕ) :
    ((rescale (rsXAlphabet 0 : D4K.R)
        (gtEulerInv rsNome rsPochhammerUnits ((rsZAlphabet i)⁻¹ : D4K.Rˣ)) *
      rescale (rsXAlphabet 1 : D4K.R)
        (gtEulerInv rsNome rsPochhammerUnits ((rsZAlphabet i)⁻¹ : D4K.Rˣ))) *
    (rescale (rsXAlphabet 0 : D4K.R)
        (gtEulerInv rsNome rsPochhammerUnits (rsZAlphabet i : D4K.R)) *
      rescale (rsXAlphabet 1 : D4K.R)
        (gtEulerInv rsNome rsPochhammerUnits (rsZAlphabet i : D4K.R)))) =
      (D4K.EInv 1 (D4K.xv + -rsZVector i) 1 one_ne_zero *
        D4K.EInv 1 (-D4K.xv + -rsZVector i) 1 one_ne_zero) *
      (D4K.EInv 1 (D4K.xv + rsZVector i) 1 one_ne_zero *
        D4K.EInv 1 (-D4K.xv + rsZVector i) 1 one_ne_zero) := by
  simp only [rsXAlphabet, if_pos rfl, if_neg (by decide : (1 : ℕ) ≠ 0)]
  change ((rescale (D4K.mon D4K.xv 1)
      (gtEulerInv rsNome rsPochhammerUnits (D4K.mon (-rsZVector i) 1)) *
    rescale (D4K.mon (-D4K.xv) 1)
      (gtEulerInv rsNome rsPochhammerUnits (D4K.mon (-rsZVector i) 1))) *
    (rescale (D4K.mon D4K.xv 1)
      (gtEulerInv rsNome rsPochhammerUnits (D4K.mon (rsZVector i) 1)) *
    rescale (D4K.mon (-D4K.xv) 1)
      (gtEulerInv rsNome rsPochhammerUnits (D4K.mon (rsZVector i) 1)))) = _
  simp only [rsRescale_EInv]

/-- This is the original sixteen-factor product, with no restriction on series degree. -/
theorem rsMixed_hyper_product :
    (∏ i ∈ Finset.range 4,
      ((rescale (rsXAlphabet 0 : D4K.R)
          (gtEulerInv rsNome rsPochhammerUnits ((rsZAlphabet i)⁻¹ : D4K.Rˣ)) *
        rescale (rsXAlphabet 1 : D4K.R)
          (gtEulerInv rsNome rsPochhammerUnits ((rsZAlphabet i)⁻¹ : D4K.Rˣ))) *
      (rescale (rsXAlphabet 0 : D4K.R)
          (gtEulerInv rsNome rsPochhammerUnits (rsZAlphabet i : D4K.R)) *
        rescale (rsXAlphabet 1 : D4K.R)
          (gtEulerInv rsNome rsPochhammerUnits (rsZAlphabet i : D4K.R))))) =
      D4K.hyperFactors := by
  simp only [rsMixed_hyper_factor]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have h0 : rsZVector 0 = D4K.zv 0 := rsZVector_eq 0
  have h1 : rsZVector 1 = D4K.zv 1 := rsZVector_eq 1
  have h2 : rsZVector 2 = D4K.zv 2 := rsZVector_eq 2
  have h3 : rsZVector 3 = D4K.zv 3 := rsZVector_eq 3
  rw [h0, h1, h2, h3]
  simp [D4K.hyperFactors, D4K.hyperVecs, List.finRange_succ, neg_smul]
  ring

/-- The exact K8 identity of the paper, in the original D4 series ring. -/
theorem rsMixedKernel_eq_kernelM :
    rsMixedKernel = D4K.EPos 1 0 2 two_ne_zero * D4K.kernelM := by
  rw [rsMixedKernel, gtFourDiagonal_product, rsMixed_numerator, rsMixed_hyper_product,
    D4K.kernelM, mul_assoc]

/-- Removing the additional scalar factor uses the already proved Euler inverse. -/
theorem rsKernelM_eq_inv_mul_mixed :
    D4K.kernelM = D4K.EInv 1 0 2 two_ne_zero * rsMixedKernel := by
  rw [rsMixedKernel_eq_kernelM, ← mul_assoc,
    mul_comm (D4K.EInv 1 0 2 two_ne_zero), D4K.EPos_mul_EInv, one_mul]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsMixed_numerator
#print axioms VOA.DeligneAudit.D4Char.rsMixed_hyper_factor
#print axioms VOA.DeligneAudit.D4Char.rsMixed_hyper_product
#print axioms VOA.DeligneAudit.D4Char.rsMixedKernel_eq_kernelM
#print axioms VOA.DeligneAudit.D4Char.rsKernelM_eq_inv_mul_mixed
