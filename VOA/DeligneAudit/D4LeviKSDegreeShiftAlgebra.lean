import VOA.DeligneAudit.D4LeviKSMixedMaximalHeight
import VOA.DeligneAudit.D4LeviKSTargetKernelIdeal

/-! Symmetric mode shifts preserve strict-height source relations. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem xyzPowerSumAlgebra_height
    {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (shape : σ → Fin 6)
    (hshape : ∀ t, shape t = 1 ∨ shape t = 4 ∨ shape t = 5)
    (P : MvPolynomial σ ℂ) (hP : P ∈ xyzPowerSumAlgebra shape)
    (W : MvPolynomial σ ℂ)
    (hW : xyzEvaluation ρ w shape W ∈ heightHigherOrbit ρ w m k) :
    xyzEvaluation ρ w shape (symmetricShiftAction σ P W) ∈
      heightHigherOrbit ρ w m k := by
  let N := (heightHigherOrbit ρ w m k).comap (xyzEvaluation ρ w shape)
  have hInv (q : Fin 3) (r : ℕ) (v : V)
      (hv : v ∈ heightHigherOrbit ρ w m k) :
      selectiveCartan ρ q r v ∈ heightHigherOrbit ρ w m k :=
    heightHigherOrbit_selectiveCartan_inv ρ w m k q r hv
  have hgen : ∀ Q ∈ {P | ∃ (j : Fin 6) (r : ℕ),
      (j = 1 ∨ j = 4 ∨ j = 5) ∧ 0 < r ∧ P = colourPsum shape j r},
      Q ∈ preservingShiftAlgebra (MvPolynomial σ ℂ)
        (symmetricShiftAction σ) N := by
    intro Q hQ
    obtain ⟨j, r, hj, hr, rfl⟩ := hQ
    intro U hU
    change xyzEvaluation ρ w shape
      (symmetricShiftAction σ (colourPsum shape j r) U) ∈
        heightHigherOrbit ρ w m k
    have hc := xyzEvaluation_psum_intertwine ρ w m h shape hshape j hj r hr U
    have hh := hInv (if j = 1 then 0 else if j = 4 then 1 else 2)
      r _ hU
    rw [hc] at hh
    have hne : (if j = 5 then (1 : ℂ) else 2) ≠ 0 := by
      split_ifs <;> norm_num
    have hdiv := (heightHigherOrbit ρ w m k).smul_mem
      (if j = 5 then (1 : ℂ) else 2)⁻¹ hh
    simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using hdiv
  have hsub : xyzPowerSumAlgebra shape ≤
      preservingShiftAlgebra (MvPolynomial σ ℂ)
        (symmetricShiftAction σ) N := by
    exact Algebra.adjoin_le hgen
  exact hsub hP W hW

theorem pairSourceSymmetric_mul_height
    (ρ : CurrentModule D4sector.f V) (w : V) (m a b c : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (P Q : pairSourceSymmetric a b c)
    (hP : xyzEvaluation ρ w (pairSourceShape a b c) P ∈
      heightHigherOrbit ρ w m k) :
    xyzEvaluation ρ w (pairSourceShape a b c)
      (Q * P : pairSourceSymmetric a b c) ∈
        heightHigherOrbit ρ w m k := by
  have hQ : (Q : MvPolynomial (PairSource a b c) ℂ) ∈
      xyzPowerSumAlgebra (pairSourceShape a b c) :=
    pairSourceSymmetric_le_xyzPowerSumAlgebra a b c Q.property
  simpa only [Subalgebra.coe_mul, symmetricShiftAction_apply] using
    xyzPowerSumAlgebra_height ρ w m h k
      (pairSourceShape a b c) (pairSourceShape_xyz a b c)
      Q hQ P hP

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xyzPowerSumAlgebra_height
#print axioms VOA.DeligneAudit.D4Levi.pairSourceSymmetric_mul_height
