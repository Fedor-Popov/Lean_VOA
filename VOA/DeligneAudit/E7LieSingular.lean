/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieData
import VOA.DeligneAudit.D4LieSingular
import VOA.DeligneAudit.E7LieSingularChecks

/-!
# The weight-two singular vector of `V^{-4}(𝔢₇)` dies in `L_{-4}(𝔢₇)`

`sv` is the highest-weight vector of `singular_cert/cert_E7.json` (highest weight `ω₆`, generating the
`1539`), written with the coefficients of relation `0` of `E7CarrierTables` (the certificate's vector up to
the sign `-1`), so its `C₂` symbol is that relation.  `J(1)` and `J(2)` kill it (integer checks
`oneZ_ok*`, `twoZ_ok`, chunked); `J(m ≥ 3)` by weight.  Hence `sv ∈ maxIdeal` (the generic Dong upgrade
`D4Lie.mem_maxIdeal_of_SingP`) and `simpleProjection_sv`.
-/

namespace VOA.DeligneAudit.E7Lie

open VOA VOA.AffineGeneral VOA.AffineGeneral.LieData VOA.DeligneAudit.D4Lie

noncomputable section

/-- `-4 + h ≠ 0`. -/
theorem hk7 : (-4 : ℂ) + e7CertData.h ≠ 0 := by rw [e7CertData_h]; norm_num

/-- `V^{-4}(𝔢₇)` on the cert basis. -/
abbrev V7 := Vacuum e7CertData (-4)

/-- `x_a(-1) x_b(-1) 𝟙`. -/
def w2 (a b : Fin 133) : V7 :=
  J e7CertData (-4) a (-1) (J e7CertData (-4) b (-1) (vacuumA e7CertData (-4)))

/-- **The weight-two singular vector** (highest weight `ω₆`). -/
def sv : V7 := ∑ i, (cz i : ℂ) • w2 (ta i) (tb i)

theorem sv_J_one (c : Fin 133) : J e7CertData (-4) c 1 sv = 0 := by
  rw [sv, map_sum]
  simp only [map_smul, w2, J_one_word2, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [← Finset.sum_smul]
  have h : (∑ i, (cz i : ℂ) * ((-4 : ℂ) * e7CertData.formTable c (tb i) *
      (if ta i = e then 1 else 0) + (-4 : ℂ) * e7CertData.formTable c (ta i) *
      (if tb i = e then 1 else 0) + ∑ d, e7CertData.structureConstant c (ta i) d *
        e7CertData.structureConstant d (tb i) e)) = (oneZ c e : ℂ) := by
    have hl : ∀ a b, (∑ d, (sZ c a d : ℂ) * (sZ d b e : ℂ)) =
        (((sL c a).map fun t => t.2 * sZ t.1 b e).sum : ℤ) := by
      intro a b; rw [← sum_sZ_mul c a (fun d => sZ d b e)]; push_cast; rfl
    simp only [formTable_eq, structureConstant_eq, hl, oneZ]
    push_cast
    rfl
  rw [h, oneZ_eq, Int.cast_zero, zero_smul]

theorem sv_J_two (c : Fin 133) : J e7CertData (-4) c 2 sv = 0 := by
  rw [sv, map_sum]
  simp only [map_smul, w2, J_two_word2, smul_smul]
  rw [← Finset.sum_smul]
  have h : (∑ i, (cz i : ℂ) * ∑ d, e7CertData.structureConstant c (ta i) d *
      ((-4 : ℂ) * e7CertData.formTable d (tb i))) = (twoZ c : ℂ) := by
    have hl : ∀ a b, (∑ d, (sZ c a d : ℂ) * ((-4 : ℂ) * (Gz d b : ℂ))) =
        (((sL c a).map fun t => t.2 * (-4 * Gz t.1 b)).sum : ℤ) := by
      intro a b; rw [← sum_sZ_mul c a (fun d => -4 * Gz d b)]; push_cast; rfl
    simp only [formTable_eq, structureConstant_eq, hl, twoZ]
    push_cast
    rfl
  rw [h, twoZ_ok, Int.cast_zero, zero_smul]

theorem sv_mem : sv ∈ gradingZA e7CertData (-4) 2 :=
  Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (word2_mem _ _ hk7 _ _)

theorem sv_singP : VOA.DeligneAudit.D4Lie.SingP e7CertData (-4) sv := by
  intro a i _
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | h3
  · exact sv_J_one a
  · exact sv_J_two a
  · have h : J e7CertData (-4) a i sv ∈ gradingZA e7CertData (-4) (2 - i) :=
      J_mem_gradingZA e7CertData (-4) hk7 a i sv_mem
    rw [gradingZA_positivity e7CertData (-4) (2 - i) (by omega)] at h
    exact (Submodule.mem_bot ℂ).mp h

/-- **The singular vector lies in the maximal ideal of `V^{-4}(𝔢₇)`.** -/
theorem sv_mem_maxIdeal : sv ∈ maxIdeal e7CertData (-4) hk7 :=
  VOA.DeligneAudit.D4Lie.mem_maxIdeal_of_SingP _ _ hk7 sv_singP (by norm_num) sv_mem

/-- **The singular vector vanishes in `L_{-4}(𝔢₇)`.** -/
theorem simpleProjection_sv : simpleProjection e7CertData (-4) hk7 sv = 0 := by
  rw [simpleProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact sv_mem_maxIdeal

end

end VOA.DeligneAudit.E7Lie

section AxiomAudit
open VOA.DeligneAudit.E7Lie
#print axioms sv_singP
#print axioms simpleProjection_sv
end AxiomAudit
