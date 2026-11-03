import VOA.DeligneAudit.D4LevelReductionCoreCellFiltration

/-!
Parabolic and Cartan currents on the honest-pair cells.
The full union-cutoff truncation remains a separate statement for the root currents.
-/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

/-- Positive power sums in every Grassmannian ring are nilpotent. -/
theorem coreGrassmannianPowerSum_nilpotent (d T s : ℕ) (hs : 0 < s) :
    IsNilpotent (SL4T.powerSumOfCoeff d
      (fun j => (-1) ^ j * SL4T.eClass d T j) s) := by
  apply SL4T.powerSumOfCoeff_nilpotent _ _ _ s hs
  intro j hj
  have hn := (Polynomial.isUnit_iff_coeff_isUnit_isNilpotent.mp
    (SL4T.grassSeries_unit d T)).2 j (by omega)
  have ht : ∀ k, d < k → (-1 : SL4T.GrassRing d T) ^ k * SL4T.eClass d T k = 0 := by
    intro k hk
    rw [SL4T.eClass_eq_zero d T k hk, mul_zero]
  simpa only [SL4T.grassSeries, SL4T.coefficientPoly_coeff_of_tail _ d ht] using hn

theorem coreComplementPowerSum_nilpotent (a b c s : ℕ) (hs : 0 < s) :
    IsNilpotent (coreComplementPowerSum a b c s) := by
  have h := (coreGrassmannianPowerSum_nilpotent (a + b) (a + b + c - (a + b)) s hs).map
    (SL4T.biLeft (a + b) (a + b + c - (a + b)) a (a + b + c - a))
  simpa only [SL4T.powerSumOfCoeff_map, map_mul, map_pow, map_neg, map_one,
    coreComplementPowerSum, SL4T.leftE] using h

theorem coreAdjointPowerSum_nilpotent (a b c s : ℕ) (hs : 0 < s) :
    IsNilpotent (coreAdjointPowerSum a b c s) := by
  have h := (coreGrassmannianPowerSum_nilpotent a (a + b + c - a) s hs).map
    (SL4T.biRight (a + b) (a + b + c - (a + b)) a (a + b + c - a))
  simpa only [SL4T.powerSumOfCoeff_map, map_mul, map_pow, map_neg, map_one,
    coreAdjointPowerSum, SL4T.rightE] using h

/-- Every positive Cartan symbol lowers every one-dimensional ideal cell. -/
theorem coreCartanSymbol_nilpotent (a b c : ℕ) (i : Fin 3) (s : ℕ) (hs : 0 < s) :
    IsNilpotent (coreCartanSymbol a b c i s) := by
  unfold coreCartanSymbol
  split_ifs
  · exact (Commute.all _ _).isNilpotent_sub
      (coreComplementPowerSum_nilpotent a b c s hs)
      (coreAdjointPowerSum_nilpotent a b c s hs)
  · exact coreAdjointPowerSum_nilpotent a b c s hs

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (a b c : ℕ) (Q : CurrentModule A3Sector.bracketTable V)
variable (π : CoreBaseRing a b c →ₗ[ℂ] V) (h : CoreRelations Q a b c π)
variable (F : CoreCellFlag a b c)

include h

/-- All positive parabolic currents annihilate every cell generator already before quotienting. -/
theorem coreCellGenerator_parabolic (i : ℕ) (e : Fin 15) (he : e.val < 6) (hne : e ≠ 3)
    (r : ℕ) : Q.op e r (π (F.generator i)) = 0 :=
  h.parabolic e he hne r (F.generator i)

/-- Positive Cartan currents send a cell generator into the preceding module term. -/
theorem coreCellGenerator_cartan (i : ℕ) (hi : i < (coreCellCatalog a b c).length)
    (j : Fin 3) (s : ℕ) (hs : 0 < s) :
    Q.op (A3Sector.simpleH j) s (π (F.generator i)) ∈
      coreCellFiltration a b c Q π F i := by
  rw [h.cartan j s hs]
  apply coreIdealSpan_contains
  exact SL4T.ideal_cell_nilpotent_mul _ _ _ _ (F.step i hi)
    (coreCartanSymbol_nilpotent a b c j s hs)

/-- The cell generator has the original dominant Cartan zero-mode weight. -/
theorem coreCellGenerator_weight (i : ℕ) (j : Fin 3) :
    (coreIdealQuotientCurrent a b c Q π (F.ideal i)).op (A3Sector.simpleH j) 0
      ((coreCellFiltration a b c Q π F i).mkQ (π (F.generator i))) =
        (A3Sector.weightABC a b a j : ℂ) •
          (coreCellFiltration a b c Q π F i).mkQ (π (F.generator i)) := by
  change (coreCellFiltration a b c Q π F i).mkQ
    (Q.op (A3Sector.simpleH j) 0 (π (F.generator i))) = _
  rw [h.weight, map_smul]

/-- In each cell quotient, the positive Cartan modes kill the generator. -/
theorem coreCellGenerator_cartan_zero (i : ℕ) (hi : i < (coreCellCatalog a b c).length)
    (j : Fin 3) (s : ℕ) (hs : 0 < s) :
    (coreIdealQuotientCurrent a b c Q π (F.ideal i)).op (A3Sector.simpleH j) s
      ((coreCellFiltration a b c Q π F i).mkQ (π (F.generator i))) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr
    (coreCellGenerator_cartan a b c Q π h F i hi j s hs)

omit h

/-- Once the union cutoff holds on a generator, it holds on the entire cyclic cell piece. -/
theorem coreCellTruncation_piece (htrunc : CoreCellTruncation a b c Q π F)
    (i : ℕ) (hi : i < (coreCellCatalog a b c).length)
    (e : Fin 15) (r : ℕ) (hr : coreCellCutoff a b c i ≤ r)
    (v : V ⧸ coreCellFiltration a b c Q π F i)
    (hv : v ∈ coreCellPiece a b c Q π F i) :
    (coreIdealQuotientCurrent a b c Q π (F.ideal i)).op e r v = 0 := by
  rw [coreCellPiece_cyclic a b c Q π F i hi] at hv
  let R := coreIdealQuotientCurrent a b c Q π (F.ideal i)
  have hI : IsLoopIdeal A3Sector.bracketTable (fun _ s => coreCellCutoff a b c i ≤ s) :=
    fun _ _ hs _ _ _ _ => hs.trans (Nat.le_add_right _ _)
  have hw : ∀ f s, coreCellCutoff a b c i ≤ s →
      R.op f s ((coreCellFiltration a b c Q π F i).mkQ (π (F.generator i))) = 0 := by
    intro f s hs
    exact (Submodule.Quotient.mk_eq_zero _).mpr (htrunc i hi f s hs)
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      exact op_wordOp_of_ideal R hI hw l e r hr
  | zero => exact map_zero _
  | add v w hv hw ihv ihw =>
      exact ((R.op e r).map_add v w).trans
        ((congrArg₂ (· + ·) ihv ihw).trans (add_zero 0))
  | smul z v hv ih =>
      exact ((R.op e r).map_smul z v).trans
        ((congrArg (fun x => z • x) ih).trans (smul_zero z))

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreGrassmannianPowerSum_nilpotent
#print axioms VOA.DeligneAudit.D4LevelReduction.coreComplementPowerSum_nilpotent
#print axioms VOA.DeligneAudit.D4LevelReduction.coreAdjointPowerSum_nilpotent
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCartanSymbol_nilpotent
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_parabolic
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_cartan
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_weight
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellGenerator_cartan_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCellTruncation_piece
