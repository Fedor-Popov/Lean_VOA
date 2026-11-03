import VOA.DeligneAudit.SL4TStableSubmoduleMinors
import Mathlib.RingTheory.AdjoinRoot

/-! # Determinantal ideals of stable submodules in a monic polynomial quotient -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A : Type*} [CommRing A]

/-- The top coordinate minors in the power basis of a monic polynomial quotient. -/
def monicQuotientTopIdeal (P : Polynomial A) (hP : P.Monic) (j : ℕ)
    (U : Submodule A (AdjoinRoot P)) : Ideal A :=
  Ideal.span {a | ∃ p : Fin j → U, Matrix.det (fun i b : Fin j =>
    (AdjoinRoot.modByMonicHom hP (p b).val).coeff (P.natDegree - j + i.val)) = a}

/-- All coordinate minors in the power basis of a monic polynomial quotient. -/
def monicQuotientAllIdeal (P : Polynomial A) (hP : P.Monic) (j : ℕ)
    (U : Submodule A (AdjoinRoot P)) : Ideal A :=
  Ideal.span {a | ∃ (rows : Fin j → Fin P.natDegree) (p : Fin j → U),
    Matrix.det (fun i b : Fin j =>
      (AdjoinRoot.modByMonicHom hP (p b).val).coeff (rows i).val) = a}

/-- Arbitrary-row minors of a stable quotient submodule lie in its top-row ideal. -/
theorem monicQuotient_coefficient_minor_mem (P : Polynomial A) (hP : P.Monic)
    (j : ℕ) (hj : j ≤ P.natDegree) (U : Submodule A (AdjoinRoot P))
    (hU : ∀ u ∈ U, AdjoinRoot.root P * u ∈ U)
    (rows : Fin j → Fin P.natDegree) (p : Fin j → U) :
    Matrix.det (fun i b : Fin j =>
      (AdjoinRoot.modByMonicHom hP (p b).val).coeff (rows i).val) ∈
        monicQuotientTopIdeal P hP j U := by
  classical
  let W := U.comap (AdjoinRoot.mkₐ P).toLinearMap
  have hW : ∀ f ∈ W, Polynomial.X * f ∈ W := by
    intro f hf
    change AdjoinRoot.mk P (Polynomial.X * f) ∈ U
    rw [map_mul]
    exact hU _ hf
  choose q hq using fun b => AdjoinRoot.mk_surjective (p b).val
  let lifted : Fin j → W := fun b => ⟨q b, by
    change AdjoinRoot.mk P (q b) ∈ U
    rw [hq]
    exact (p b).property⟩
  have h := stableSubmodule_coefficient_minor_mem P P.natDegree j hP rfl hj W hW
    lifted rows
  have hle : polynomialSubmoduleTopIdeal P P.natDegree j W ≤
      monicQuotientTopIdeal P hP j U := by
    apply Ideal.span_le.mpr
    rintro a ⟨v, rfl⟩
    exact Ideal.subset_span
      ⟨fun b => ⟨AdjoinRoot.mk P (v b).val, (v b).property⟩, rfl⟩
  apply hle at h
  convert h using 1
  congr 1
  ext i b
  rw [← hq b, AdjoinRoot.modByMonicHom_mk]

/-- Top-row minors generate all minors for every variable-stable submodule
of a monic polynomial quotient, over every commutative coefficient ring. -/
theorem monicQuotient_allIdeal_eq_topIdeal (P : Polynomial A) (hP : P.Monic)
    (j : ℕ) (hj : j ≤ P.natDegree) (U : Submodule A (AdjoinRoot P))
    (hU : ∀ u ∈ U, AdjoinRoot.root P * u ∈ U) :
    monicQuotientAllIdeal P hP j U = monicQuotientTopIdeal P hP j U := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨rows, p, rfl⟩
    exact monicQuotient_coefficient_minor_mem P hP j hj U hU rows p
  · apply Ideal.span_le.mpr
    rintro a ⟨p, rfl⟩
    exact Ideal.subset_span
      ⟨fun a => ⟨P.natDegree - j + a.val, by omega⟩, p, rfl⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.monicQuotient_coefficient_minor_mem
#print axioms VOA.DeligneAudit.SL4T.monicQuotient_allIdeal_eq_topIdeal
