/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieData
import VOA.DeligneAudit.D4LieSingular
import VOA.DeligneAudit.E8LieSingularChecks

/-!
# The weight-two singular vector of `V^{-6}(𝔢₈)` dies in `L_{-6}(𝔢₈)`

`sv` is the highest-weight vector of `singular_cert/cert_E8.json` (highest weight `ω₁`, generating the
`3875`), written with the coefficients of relation `0` of `E8CarrierTables` (the certificate's vector up to
the sign `-1`), so its `C₂` symbol is that relation.  `J(1)` and `J(2)` kill it (integer checks
`oneZ_ok*`, `twoZ_ok`, chunked); `J(m ≥ 3)` by weight.  Hence `sv ∈ maxIdeal` (the generic Dong upgrade
`D4Lie.mem_maxIdeal_of_SingP`) and `simpleProjection_sv`.
-/

namespace VOA.DeligneAudit.E8Lie

open VOA VOA.AffineGeneral VOA.AffineGeneral.LieData VOA.DeligneAudit.D4Lie

noncomputable section

/-- `-6 + h ≠ 0`. -/
theorem hk8 : (-6 : ℂ) + e8CertData.h ≠ 0 := by rw [e8CertData_h]; norm_num

/-- `V^{-6}(𝔢₈)` on the cert basis. -/
abbrev V8 := Vacuum e8CertData (-6)

/-- `x_a(-1) x_b(-1) 𝟙`. -/
def w2 (a b : Fin 248) : V8 :=
  J e8CertData (-6) a (-1) (J e8CertData (-6) b (-1) (vacuumA e8CertData (-6)))

/-- **The weight-two singular vector** (highest weight `ω₆`). -/
def sv : V8 := ∑ i, (cz i : ℂ) • w2 (ta i) (tb i)

theorem sv_J_one (c : Fin 248) : J e8CertData (-6) c 1 sv = 0 := by
  rw [sv, map_sum]
  simp only [map_smul, w2, J_one_word2, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [← Finset.sum_smul]
  have h : (∑ i, (cz i : ℂ) * ((-6 : ℂ) * e8CertData.formTable c (tb i) *
      (if ta i = e then 1 else 0) + (-6 : ℂ) * e8CertData.formTable c (ta i) *
      (if tb i = e then 1 else 0) + ∑ d, e8CertData.structureConstant c (ta i) d *
        e8CertData.structureConstant d (tb i) e)) = (oneZ c e : ℂ) := by
    have hl : ∀ a b, (∑ d, (sZ c a d : ℂ) * (sZ d b e : ℂ)) =
        (((sL c a).map fun t => t.2 * sZ t.1 b e).sum : ℤ) := by
      intro a b; rw [← sum_sZ_mul c a (fun d => sZ d b e)]; push_cast; rfl
    simp only [formTable_eq, structureConstant_eq, hl, oneZ]
    push_cast
    rfl
  rw [h, oneZ_eq, Int.cast_zero, zero_smul]

theorem sv_J_two (c : Fin 248) : J e8CertData (-6) c 2 sv = 0 := by
  rw [sv, map_sum]
  simp only [map_smul, w2, J_two_word2, smul_smul]
  rw [← Finset.sum_smul]
  have h : (∑ i, (cz i : ℂ) * ∑ d, e8CertData.structureConstant c (ta i) d *
      ((-6 : ℂ) * e8CertData.formTable d (tb i))) = (twoZ c : ℂ) := by
    have hl : ∀ a b, (∑ d, (sZ c a d : ℂ) * ((-6 : ℂ) * (Gz d b : ℂ))) =
        (((sL c a).map fun t => t.2 * (-6 * Gz t.1 b)).sum : ℤ) := by
      intro a b; rw [← sum_sZ_mul c a (fun d => -6 * Gz d b)]; push_cast; rfl
    simp only [formTable_eq, structureConstant_eq, hl, twoZ]
    push_cast
    rfl
  rw [h, twoZ_ok, Int.cast_zero, zero_smul]

theorem sv_mem : sv ∈ gradingZA e8CertData (-6) 2 :=
  Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (word2_mem _ _ hk8 _ _)

theorem sv_singP : VOA.DeligneAudit.D4Lie.SingP e8CertData (-6) sv := by
  intro a i _
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | h3
  · exact sv_J_one a
  · exact sv_J_two a
  · have h := J_mem_gradingZA e8CertData (-6) hk8 a i sv_mem
    rw [gradingZA_positivity e8CertData (-6) (2 - i) (by omega)] at h
    exact (Submodule.mem_bot ℂ).mp h

/-- **The singular vector lies in the maximal ideal of `V^{-6}(𝔢₈)`.** -/
theorem sv_mem_maxIdeal : sv ∈ maxIdeal e8CertData (-6) hk8 :=
  VOA.DeligneAudit.D4Lie.mem_maxIdeal_of_SingP _ _ hk8 sv_singP (by norm_num) sv_mem

/-- **The singular vector vanishes in `L_{-6}(𝔢₈)`.** -/
theorem simpleProjection_sv : simpleProjection e8CertData (-6) hk8 sv = 0 := by
  rw [simpleProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact sv_mem_maxIdeal

end

end VOA.DeligneAudit.E8Lie

section AxiomAudit
open VOA.DeligneAudit.E8Lie
#print axioms sv_singP
#print axioms simpleProjection_sv
end AxiomAudit
