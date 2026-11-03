import VOA.DeligneAudit.D4LeviKSPairFactor

/-! The exact PAIR kernel obligation for the D4 word evaluator. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

/-- Fixed XYZ colours on the source's labelled positions. -/
def pairSourceShape (a b c : ℕ) : PairSource a b c → Fin 6
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => 4
  | Sum.inr (Sum.inr _) => 5

theorem pairSourceShape_xyz (a b c : ℕ) (t : PairSource a b c) :
    pairSourceShape a b c t = 1 ∨
      pairSourceShape a b c t = 4 ∨
        pairSourceShape a b c t = 5 := by
  rcases t with x | yz
  · exact Or.inl rfl
  rcases yz with y | z
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Evaluation of separately symmetric XYZ mode polynomials in the
    quotient by the descending key prefix. -/
noncomputable def pairSymmetricWordEvaluation
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c : ℕ) :
    pairSourceSymmetric a b c →ₗ[ℂ] V ⧸ keyPrefix ρ w m i :=
  ((keyPrefix ρ w m i).mkQ).comp
    ((xyzEvaluation ρ w (pairSourceShape a b c)).comp
      (Subalgebra.val (pairSourceSymmetric a b c)).toLinearMap)

theorem pairSymmetricWordEvaluation_eq_zero_iff
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c : ℕ)
    (P : pairSourceSymmetric a b c) :
    pairSymmetricWordEvaluation ρ w m i a b c P = 0 ↔
      xyzEvaluation ρ w (pairSourceShape a b c) P ∈
        keyPrefix ρ w m i := by
  change (Submodule.Quotient.mk
    (xyzEvaluation ρ w (pairSourceShape a b c) P) :
      V ⧸ keyPrefix ρ w m i) = 0 ↔ _
  exact (Submodule.Quotient.mk_eq_zero
    (p := keyPrefix ρ w m i)
    (x := xyzEvaluation ρ w (pairSourceShape a b c) P))

/-- The remaining D4-specific content of Lemma 1, stated on the exact
    symmetric kernel rather than the larger labelled polynomial kernel. -/
def PairKernelPrefix
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c : ℕ) : Prop :=
  ∀ P : pairSourceSymmetric a b c,
    pairSymmetricRestriction a b c P = 0 →
      xyzEvaluation ρ w (pairSourceShape a b c) P ∈
        keyPrefix ρ w m i

/-- PAIR holds precisely when word evaluation factors through symmetric
    restriction, with values in the key quotient. -/
theorem pairKernelPrefix_iff_factor
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c : ℕ) :
    PairKernelPrefix ρ w m i a b c ↔
      ∃ qbar : pairTargetSymmetric a b c →ₗ[ℂ]
        V ⧸ keyPrefix ρ w m i,
        ∀ P, qbar (pairSymmetricRestriction a b c P) =
          pairSymmetricWordEvaluation ρ w m i a b c P := by
  rw [pairSymmetric_factor_iff]
  exact forall_congr' fun P =>
    imp_congr_right fun _ =>
      (pairSymmetricWordEvaluation_eq_zero_iff ρ w m i a b c P).symm

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairSymmetricWordEvaluation_eq_zero_iff
#print axioms VOA.DeligneAudit.D4Levi.pairKernelPrefix_iff_factor
