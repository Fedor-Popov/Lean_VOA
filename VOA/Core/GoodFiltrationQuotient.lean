/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.GoodFiltration
import VOA.Core.QuotientVOA

/-!
# Quotients of graded flags and good filtrations

A graded flag on a vertex operator algebra descends to any VOA quotient by taking the image of
each filtered weight space.  This is purely order-theoretic: it uses the quotient grading and the
surjectivity built into the quotient construction, but no strictness, associated-graded, or
inverse-DS hypothesis.

If the source flag is mode-compatible, its quotient is mode-compatible as well.  This second
statement uses the quotient morphism identity
`QuotVOA.quotientVOA_mkQ_smul`; it makes `GoodFiltration.quotient` immediate.

These definitions equip the quotient with the **induced** filtration.  They do not identify that
filtration with an independently characterized physical filtration, compute the initial ideal of
the quotient, or identify the quotient's `C₂`-algebra.
-/

namespace VOA

open VertexOperatorAlgebra

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

namespace GradedFlag

/-- The graded flag induced on a quotient VOA: the degree-`p`, weight-`n` piece is the image of
the corresponding source piece under the quotient map. -/
noncomputable def quotient {W : VertexOperatorAlgebra V} (F : GradedFlag W)
    (I : Submodule ℂ V) (hI : W.IsIdeal I) (hgr : QuotVOA.IsGradedIdeal W I) :
    GradedFlag (QuotVOA.quotientVOA W I hI hgr) where
  piece p n := (F.piece p n).map I.mkQ
  le_grading p n := Submodule.map_mono (F.le_grading p n)
  mono := fun {p q} n hpq => Submodule.map_mono (F.mono n hpq)
  bot n hn := by rw [F.bot n hn, Submodule.map_bot]
  vacuum_zero := by
    rw [F.vacuum_zero, Submodule.map_span, Set.image_singleton]
    rfl
  exhaustive n := by
    rw [← Submodule.map_iSup, F.exhaustive]
    rfl

@[simp] theorem quotient_piece {W : VertexOperatorAlgebra V} (F : GradedFlag W)
    (I : Submodule ℂ V) (hI : W.IsIdeal I) (hgr : QuotVOA.IsGradedIdeal W I)
    (p : ℕ) (n : ℤ) :
    (F.quotient I hI hgr).piece p n = (F.piece p n).map I.mkQ := rfl

/-- Mode compatibility descends through a VOA quotient.  This theorem is conditional only on
mode compatibility of the source flag; it has no filtration-strictness hypothesis. -/
theorem quotient_modeCompatible {W : VertexOperatorAlgebra V} (F : GradedFlag W)
    (I : Submodule ℂ V) (hI : W.IsIdeal I) (hgr : QuotVOA.IsGradedIdeal W I)
    (hmode : F.ModeCompatible) : (F.quotient I hI hgr).ModeCompatible := by
  intro p q m n j u v hu hv
  change u ∈ (F.piece p m).map I.mkQ at hu
  change v ∈ (F.piece q n).map I.mkQ at hv
  obtain ⟨u, hu, rfl⟩ := hu
  obtain ⟨v, hv, rfl⟩ := hv
  change (QuotVOA.quotientVOA W I hI hgr).smul (I.mkQ u) j (I.mkQ v) ∈
    (F.piece (p + q) (m + n - j - 1)).map I.mkQ
  rw [QuotVOA.quotientVOA_mkQ_smul]
  exact Submodule.mem_map_of_mem (hmode hu hv)

end GradedFlag

namespace GoodFiltration

/-- A good filtration descends to a good filtration on every VOA quotient. -/
noncomputable def quotient {W : VertexOperatorAlgebra V} (F : GoodFiltration W)
    (I : Submodule ℂ V) (hI : W.IsIdeal I) (hgr : QuotVOA.IsGradedIdeal W I) :
    GoodFiltration (QuotVOA.quotientVOA W I hI hgr) where
  toGradedFlag := F.toGradedFlag.quotient I hI hgr
  mode_mem := F.toGradedFlag.quotient_modeCompatible I hI hgr F.mode_mem

@[simp] theorem quotient_toGradedFlag {W : VertexOperatorAlgebra V} (F : GoodFiltration W)
    (I : Submodule ℂ V) (hI : W.IsIdeal I) (hgr : QuotVOA.IsGradedIdeal W I) :
    (F.quotient I hI hgr).toGradedFlag = F.toGradedFlag.quotient I hI hgr := rfl

end GoodFiltration

end VOA
