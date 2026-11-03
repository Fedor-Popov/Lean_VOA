import VOA.DeligneAudit.D4LeviKSRzGeneralWord
import VOA.DeligneAudit.D4LeviKSPairSymmetricEmbeds
import VOA.DeligneAudit.D4LeviKSPairRecolour

/-! Symmetric orbit sums for the general Rz polynomial presentation. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def rzOrbitSum (σ : Type*) [Fintype σ]
    (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ := by
  classical
  exact ∑ e : Equiv.Perm σ, rename e P

theorem rzOrbitSum_symmetric (σ : Type*) [Fintype σ]
    (P : MvPolynomial σ ℂ) :
    rzOrbitSum σ P ∈ symmetricSubalgebra σ ℂ := by
  classical
  change (rzOrbitSum σ P).IsSymmetric
  intro e
  simp only [rzOrbitSum, map_sum]
  apply Finset.sum_bij (fun f _ => e * f)
  · intro f hf
    simp
  · intro f hf
    simp
  · intro f hf
    exact ⟨e⁻¹ * f, by simp, by group⟩
  · intro f hf
    simp [rename_rename]

theorem rzOrbitSum_source_X_mem (a b c : ℕ)
    (P : MvPolynomial (Fin b ⊕ Fin a) ℂ) :
    rename Sum.inl (rzOrbitSum (Fin b ⊕ Fin a) P) ∈
      pairSourceSymmetric a b c :=
  pairSource_symmetric_X_mem a b c _
    (rzOrbitSum_symmetric (Fin b ⊕ Fin a) P)

theorem rzOrbitSum_source_Z_mem (a b c : ℕ)
    (P : MvPolynomial (Fin c) ℂ) :
    rename (fun z : Fin c =>
      (Sum.inr (Sum.inr z) : PairSource a b c))
        (rzOrbitSum (Fin c) P) ∈ pairSourceSymmetric a b c :=
  pairSource_symmetric_Z_mem a b c _
    (rzOrbitSum_symmetric (Fin c) P)

theorem rzOrbitSum_evaluation {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (P : MvPolynomial σ ℂ)
    (hshape : ∀ e : Equiv.Perm σ, shape ∘ e = shape) :
    xyzEvaluation ρ w shape (rzOrbitSum σ P) =
      Nat.card (Equiv.Perm σ) • xyzEvaluation ρ w shape P := by
  classical
  calc
    xyzEvaluation ρ w shape (rzOrbitSum σ P) =
        ∑ e : Equiv.Perm σ, xyzEvaluation ρ w shape (rename e P) := by
      simp only [rzOrbitSum, map_sum]
    _ = ∑ _e : Equiv.Perm σ, xyzEvaluation ρ w shape P := by
      apply Finset.sum_congr rfl
      intro e he
      rw [xyzEvaluation_rename_equiv, hshape]
    _ = Nat.card (Equiv.Perm σ) • xyzEvaluation ρ w shape P := by
      simp [Nat.card_eq_fintype_card]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzOrbitSum_symmetric
#print axioms VOA.DeligneAudit.D4Levi.rzOrbitSum_source_X_mem
#print axioms VOA.DeligneAudit.D4Levi.rzOrbitSum_source_Z_mem
#print axioms VOA.DeligneAudit.D4Levi.rzOrbitSum_evaluation
