/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieData
import VOA.DeligneAudit.DeligneCarrierD4
import VOA.DeligneAudit.A2RelationsSingular
import VOA.DeligneAudit.D4LieSingularGeneric
import VOA.DeligneAudit.D4LieSingularChecks

/-!
# The three weight-two singular vectors of `V^{-2}(𝔰𝔬₈)` die in `L_{-2}(𝔰𝔬₈)`

* §1, for **any** `LieData` and noncritical level (port of the A₂ argument,
  `A2RelationsSingular`, to `AffineGeneral`): a vector killed by every strictly positive current
  mode (`SingP`) is killed by every non-weight-raising mode of every state; weight-one states are
  quasi-primary; hence every homogeneous `SingP` vector of positive weight lies in `maxIdeal`
  (`mem_maxIdeal_of_SingP`).  Also the explicit actions of `J(1)`, `J(2)` on `x(-1)y(-1)𝟙`
  (`J_one_word2`, `J_two_word2`).
* §2, `D = d4CertData`, `k = -2`: the three highest-weight vectors `sv r` of
  `singular_cert/cert_D4.json` (weights `2ω₁, 2ω₃, 2ω₄`; their `C₂` symbols are the relations
  `P0, P1, P2` of `DeligneCarrierD4`) satisfy `SingP` (integer checks `sv_one_cert`,
  `sv_two_cert`), so they vanish in `L_{-2}(𝔰𝔬₈)` (`simpleProjection_sv`).
-/

namespace VOA.DeligneAudit.D4Lie

open VOA VOA.AffineGeneral VOA.AffineGeneral.LieData
open Module (End)

noncomputable section

/-- `-2 + h ≠ 0`. -/
theorem hk4 : (-2 : ℂ) + d4CertData.h ≠ 0 := by rw [d4CertData_h]; norm_num

/-- `V^{-2}(𝔰𝔬₈)` on the cert basis. -/
abbrev V4 := Vacuum d4CertData (-2)

/-- `x_a(-1) x_b(-1) 𝟙`. -/
def w2 (a b : Fin 28) : V4 :=
  J d4CertData (-2) a (-1) (J d4CertData (-2) b (-1) (vacuumA d4CertData (-2)))

/-- **The three weight-two singular vectors** (highest weights `2ω₄, 2ω₃, 2ω₁`). -/
def sv (r : Fin 3) : V4 := ∑ i, (cz r i : ℂ) • w2 (ta r i) (tb r i)

theorem sv_J_one (r : Fin 3) (c : Fin 28) : J d4CertData (-2) c 1 (sv r) = 0 := by
  rw [sv, map_sum]
  simp only [map_smul, w2, J_one_word2, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [← Finset.sum_smul]
  have h : (∑ i, (cz r i : ℂ) * ((-2 : ℂ) * d4CertData.formTable c (tb r i) *
      (if ta r i = e then 1 else 0) + (-2 : ℂ) * d4CertData.formTable c (ta r i) *
      (if tb r i = e then 1 else 0) + ∑ d, d4CertData.structureConstant c (ta r i) d *
        d4CertData.structureConstant d (tb r i) e)) = (oneZ r c e : ℂ) := by
    have hl : ∀ a b, (∑ d, (sZ c a d : ℂ) * (sZ d b e : ℂ)) =
        (((sL c a).map fun t => t.2 * sZ t.1 b e).sum : ℤ) := by
      intro a b; rw [← sum_sZ_mul c a (fun d => sZ d b e)]; push_cast; rfl
    simp only [formTable_eq, structureConstant_eq, hl, oneZ]
    push_cast
    rfl
  rw [h, oneZ_eq, Int.cast_zero, zero_smul]

theorem sv_J_two (r : Fin 3) (c : Fin 28) : J d4CertData (-2) c 2 (sv r) = 0 := by
  rw [sv, map_sum]
  simp only [map_smul, w2, J_two_word2, smul_smul]
  rw [← Finset.sum_smul]
  have h : (∑ i, (cz r i : ℂ) * ∑ d, d4CertData.structureConstant c (ta r i) d *
      ((-2 : ℂ) * d4CertData.formTable d (tb r i))) = (twoZ r c : ℂ) := by
    have hl : ∀ a b, (∑ d, (sZ c a d : ℂ) * ((-2 : ℂ) * (Gz d b : ℂ))) =
        (((sL c a).map fun t => t.2 * (-2 * Gz t.1 b)).sum : ℤ) := by
      intro a b; rw [← sum_sZ_mul c a (fun d => -2 * Gz d b)]; push_cast; rfl
    simp only [formTable_eq, structureConstant_eq, hl, twoZ]
    push_cast
    rfl
  rw [h, twoZ_eq, Int.cast_zero, zero_smul]

theorem sv_mem (r : Fin 3) : sv r ∈ gradingZA d4CertData (-2) 2 :=
  Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (word2_mem _ _ hk4 _ _)

theorem sv_singP (r : Fin 3) : SingP d4CertData (-2) (sv r) := by
  intro a i _
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | h3
  · exact sv_J_one r a
  · exact sv_J_two r a
  · have h := J_mem_gradingZA _ _ hk4 a i (sv_mem r)
    rw [gradingZA_positivity _ _ (2 - i) (by omega)] at h
    exact (Submodule.mem_bot ℂ).mp h

/-- **The singular vectors lie in the maximal ideal of `V^{-2}(𝔰𝔬₈)`.** -/
theorem sv_mem_maxIdeal (r : Fin 3) : sv r ∈ maxIdeal d4CertData (-2) hk4 :=
  mem_maxIdeal_of_SingP _ _ hk4 (sv_singP r) (by norm_num) (sv_mem r)

/-- **The singular vectors vanish in `L_{-2}(𝔰𝔬₈)`.** -/
theorem simpleProjection_sv (r : Fin 3) : simpleProjection d4CertData (-2) hk4 (sv r) = 0 := by
  rw [simpleProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact sv_mem_maxIdeal r

end

end VOA.DeligneAudit.D4Lie

section AxiomAudit
open VOA.DeligneAudit.D4Lie
#print axioms mem_maxIdeal_of_SingP
#print axioms sv_singP
#print axioms simpleProjection_sv
end AxiomAudit
