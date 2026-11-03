import VOA.DeligneAudit.D4LeviKSRzOrbitSpanAlgebra

/-! Finite linear combinations of general Rz orbit relations. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

noncomputable def rzBilinearTarget (a b k l s : ℕ)
    (P : MvPolynomial (Fin b ⊕ Fin a) ℂ)
    (R : MvPolynomial (Fin l) ℂ) :
    pairTargetSymmetric a b (k + l) :=
  ∑ p ∈ P.support, ∑ q ∈ R.support,
    (P.coeff p * R.coeff q) •
      rzTargetGenerator a b k l s (fun i => p i) (fun j => q j)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rzBilinearTarget_mem_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b k l s d : ℕ)
    (P : MvPolynomial (Fin b ⊕ Fin a) ℂ)
    (R : MvPolynomial (Fin l) ℂ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b (k + l) d)
    (hdegree : ∀ p ∈ P.support, ∀ q ∈ R.support,
      ((Finset.univ.toList : List (Fin b ⊕ Fin a)).map
          (fun i => p i)).sum +
        ((Finset.univ.toList : List (Fin l)).map
          (fun j => q j)).sum + s = d) :
    rzBilinearTarget a b k l s P R ∈
      (pairTargetQuotientEvaluation ρ w m i a b (k + l)
        (pairKernelPrefix_of_sat ρ w m i a b (k + l)
          d h hi hkey)).ker := by
  classical
  unfold rzBilinearTarget
  apply Submodule.sum_mem
  intro p hp
  apply Submodule.sum_mem
  intro q hq
  apply Submodule.smul_mem
  have hkey' : keyEnum m ⟨i, hi⟩ =
      pairFinalKey a b (k + l)
        (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map
            (fun i => p i)).sum +
          ((Finset.univ.toList : List (Fin l)).map
            (fun j => q j)).sum + s) := by
    rw [hdegree p hp q hq]
    exact hkey
  simpa [hdegree p hp q hq] using
    rzTargetGenerator_mem_ker ρ w m i a b k l s
      (fun i => p i) (fun j => q j) h hk hks hi hkey'

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzBilinearTarget_mem_ker
