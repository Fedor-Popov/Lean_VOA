import VOA.DeligneAudit.D4LeviKSOneBox

/-! The one-alphabet box lemma after any linear evaluation killing Garland relations. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.Sl2Weyl

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A graded Garland quotient is spanned by the images of its finite mode box. -/
theorem ksOneBox_eval_span (q n d : ℕ) (hn : n ≤ q)
    (L : R →ₗ[ℂ] V)
    (hJ : ∀ P ∈ J q, L P = 0)
    (P : R) (hP : MvPolynomial.IsWeightedHomogeneous om P (n, d)) :
    L P ∈ Submodule.span ℂ
      (L '' (ksOneBoxPolys q n d : Set R)) := by
  obtain ⟨B, hB, C, hC, rfl⟩ :=
    Submodule.mem_sup.mp (ksOneBox_span_graded q n d hn P hP)
  rw [map_add, hJ C hC, add_zero]
  have hmap : L B ∈
      (Submodule.span ℂ (ksOneBoxPolys q n d : Set R)).map L :=
    ⟨B, hB, rfl⟩
  simpa only [Submodule.map_span] using hmap

/-- If the requested number of letters exceeds the Garland weight,
every homogeneous evaluation is zero. -/
theorem ksOneBox_eval_zero (q n d : ℕ) (hn : q < n)
    (L : R →ₗ[ℂ] V)
    (hJ : ∀ P ∈ J q, L P = 0)
    (P : R) (hP : MvPolynomial.IsWeightedHomogeneous om P (n, d)) :
    L P = 0 :=
  hJ P (ksOneBox_J_of_length_gt q n d hn P hP)

/-- The homogeneous image of any Garland-compatible evaluation has the
binomial rank bound of the one-alphabet box. -/
theorem ksOneBox_eval_range_rank (q n d : ℕ) (hn : n ≤ q)
    (L : R →ₗ[ℂ] V)
    (hJ : ∀ P ∈ J q, L P = 0) :
    Module.finrank ℂ
      ((MvPolynomial.weightedHomogeneousSubmodule ℂ om (n, d)).map L) ≤
        q.choose n := by
  classical
  let B := ksOneBoxPolys q n d
  let E := B.image L
  have hspan :
      (MvPolynomial.weightedHomogeneousSubmodule ℂ om (n, d)).map L ≤
        Submodule.span ℂ (E : Set V) := by
    rintro v ⟨P, hP, rfl⟩
    have hp : MvPolynomial.IsWeightedHomogeneous om P (n, d) :=
      (MvPolynomial.mem_weightedHomogeneousSubmodule ℂ om (n, d) P).mp hP
    simpa only [E, Finset.coe_image] using
      ksOneBox_eval_span q n d hn L hJ P hp
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (E : Set V)) :=
    FiniteDimensional.span_of_finite _ (Finset.finite_toSet E)
  calc
    Module.finrank ℂ
        ((MvPolynomial.weightedHomogeneousSubmodule ℂ om (n, d)).map L) ≤
        Module.finrank ℂ (Submodule.span ℂ (E : Set V)) :=
      Submodule.finrank_mono hspan
    _ ≤ E.card := finrank_span_finset_le_card (R := ℂ) (s := E)
    _ ≤ B.card := Finset.card_image_le
    _ ≤ q.choose n := ksOneBoxPolys_card_le q n d hn

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksOneBox_eval_span
#print axioms VOA.DeligneAudit.D4Levi.ksOneBox_eval_zero
#print axioms VOA.DeligneAudit.D4Levi.ksOneBox_eval_range_rank
