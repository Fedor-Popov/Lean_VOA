/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorChain
import VOA.DeligneAudit.DeligneCarrierA2
import VOA.DeligneAudit.A2SectorTop

/-!
# A₂ as an instance of the generic sector chain

`A2sector` packages the `A2data` with the `sl₃` Lie data: structure constants `bracketTable`
(Jacobi: `jacobiCoord`), ad-stability (`relationsStable`), `c₀ = f₁₂*` (index `5`), the local Weyl
data of `W_loc(mθ)` (`θ(h₁) = θ(h₂) = 1`), weights, and coadjoint cyclicity in depth `3`.
`A2_sectorFusionBound_generic` re-derives the A₂ sector fusion bound from the generic chain.
-/

namespace VOA.DeligneAudit.DeligneSector

open MvPolynomial VOA.AffineSl3 VOA.DeligneAudit.DeligneCarrier VOA.DeligneAudit.SectorLoop
open VOA.DeligneAudit.SectorWeyl VOA.QuadraticCurrentFunctionalCarrier

noncomputable section

/-! ## Coadjoint cyclicity for `sl₃` in depth 3 -/

theorem wordA_mem (l : List (Fin 8)) (hl : l.length ≤ 3) :
    wordA bracketTable l (Pi.single 5 1) ∈ slotWords bracketTable 5 3 :=
  Submodule.subset_span ⟨l, hl, rfl⟩

set_option maxHeartbeats 4000000 in -- explicit coadjoint computation
theorem w3 : wordA bracketTable [3] (Pi.single 5 1) = (Pi.single 4 1 : Fin 8 → ℂ) := by
  funext y
  fin_cases y <;> simp [wordA, slotA, Fin.sum_univ_eight, bracketTable, Pi.single_apply] <;> norm_num

set_option maxHeartbeats 4000000 in -- explicit coadjoint computation
theorem w4 : wordA bracketTable [4] (Pi.single 5 1) = (-Pi.single 3 1 : Fin 8 → ℂ) := by
  funext y
  fin_cases y <;> simp [wordA, slotA, Fin.sum_univ_eight, bracketTable, Pi.single_apply] <;> norm_num

set_option maxHeartbeats 4000000 in -- explicit coadjoint computation
theorem w53 : wordA bracketTable [5, 3] (Pi.single 5 1) = (-Pi.single 0 1 : Fin 8 → ℂ) := by
  funext y
  fin_cases y <;> simp [wordA, slotA, Fin.sum_univ_eight, bracketTable, Pi.single_apply] <;> norm_num

set_option maxHeartbeats 4000000 in -- explicit coadjoint computation
theorem w54 : wordA bracketTable [5, 4] (Pi.single 5 1) = (-Pi.single 1 1 : Fin 8 → ℂ) := by
  funext y
  fin_cases y <;> simp [wordA, slotA, Fin.sum_univ_eight, bracketTable, Pi.single_apply] <;> norm_num

set_option maxHeartbeats 4000000 in -- explicit coadjoint computation
theorem w55 : wordA bracketTable [5, 5] (Pi.single 5 1) = (-(2 : ℂ) • Pi.single 2 1 : Fin 8 → ℂ) := by
  funext y
  fin_cases y <;> simp [wordA, slotA, Fin.sum_univ_eight, bracketTable, Pi.single_apply] <;> norm_num

set_option maxHeartbeats 4000000 in -- explicit coadjoint computation
theorem w154 : wordA bracketTable [1, 5, 4] (Pi.single 5 1) = (Pi.single 6 1 - (2 : ℂ) • Pi.single 7 1 : Fin 8 → ℂ) := by
  funext y
  fin_cases y <;> simp [wordA, slotA, Fin.sum_univ_eight, bracketTable, Pi.single_apply] <;> norm_num

set_option maxHeartbeats 4000000 in -- explicit coadjoint computation
theorem w514 : wordA bracketTable [5, 1, 4] (Pi.single 5 1) = (-Pi.single 6 1 - Pi.single 7 1 : Fin 8 → ℂ) := by
  funext y
  fin_cases y <;> simp [wordA, slotA, Fin.sum_univ_eight, bracketTable, Pi.single_apply] <;> norm_num

theorem cyclic_A2 (c : Fin 8) : (Pi.single c 1 : Fin 8 → ℂ) ∈ slotWords bracketTable 5 3 := by
  have h3 := wordA_mem [3] (by decide); rw [w3] at h3
  have h4 := wordA_mem [4] (by decide); rw [w4] at h4
  have h53 := wordA_mem [5, 3] (by decide); rw [w53] at h53
  have h54 := wordA_mem [5, 4] (by decide); rw [w54] at h54
  have h55 := wordA_mem [5, 5] (by decide); rw [w55] at h55
  have h154 := wordA_mem [1, 5, 4] (by decide); rw [w154] at h154
  have h514 := wordA_mem [5, 1, 4] (by decide); rw [w514] at h514
  have h5 := wordA_mem [] (by decide)
  fin_cases c
  · simpa using Submodule.neg_mem _ h53
  · simpa using Submodule.neg_mem _ h54
  · have := Submodule.smul_mem _ (-(1 / 2 : ℂ)) h55
    convert this using 1
    funext y; fin_cases y <;> simp [Pi.single_apply] <;> norm_num
  · simpa using Submodule.neg_mem _ h4
  · simpa using h3
  · simpa using h5
  · have := Submodule.smul_mem _ (1 / 3 : ℂ) (Submodule.sub_mem _ h154 (Submodule.smul_mem _ 2 h514))
    convert this using 1
    funext y; fin_cases y <;> simp [Pi.single_apply] <;> norm_num
  · have := Submodule.smul_mem _ (-(1 / 3 : ℂ)) (Submodule.add_mem _ h154 h514)
    convert this using 1
    funext y; fin_cases y <;> simp [Pi.single_apply] <;> norm_num

/-! ## Weights in `Fin 2 → ℤ` -/

/-- The `sl₃` weights as vectors. -/
def wt2 (c : Fin 8) : Fin 2 → ℤ := ![(A2.wt c).1, (A2.wt c).2]

theorem wt2_eq_iff (c x y : Fin 8) : wt2 c = wt2 x + wt2 y ↔ A2.wt c = A2.wt x + A2.wt y := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [wt2] at h0 h1
    exact Prod.ext h0 h1
  · intro h
    funext k
    fin_cases k <;> simp [wt2, h]

theorem table_wt2 (x y c : Fin 8) (h : wt2 c ≠ wt2 x + wt2 y) : bracketTable x y c = 0 :=
  A2.table_wt x y c fun h' => h ((wt2_eq_iff c x y).mpr h')

theorem noweight2 (i : Fin 8) (hi : i = 3 ∨ i = 4) (m : ℕ) (t : Fin m → Fin 8) :
    ∑ j, wt2 (t j) ≠ m • wt2 5 - (m * 1 + 1) • wt2 i := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, wt2, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_one] at h0 h1
  have hp : ∑ j, A2.wt (t j) = m • A2.wt 5 - (m + 1) • A2.wt i := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sum, Prod.fst_sub, Prod.smul_fst]; exact h0
    · simp only [Prod.snd_sum, Prod.snd_sub, Prod.smul_snd]; exact h1
  rcases hi with rfl | rfl
  · exact A2.no_weight_f1 m t hp
  · exact A2.no_weight_f2 m t hp

/-! ## The A₂ sector data -/

/-- **A₂ as sector data.** -/
def A2sector : DeligneSectorData where
  n := A2data.n
  ρ := A2data.ρ
  rel := A2data.rel
  cas := A2data.cas
  u3 := A2data.u3
  ρFin := inferInstanceAs (Fintype (Fin 8))
  f := bracketTable
  jacobi := A2.jacobiCoord
  stable := by
    change RelationsStable bracketTable A2data.fullMatrix
    rw [A2data_fullMatrix]; exact A2.relationsStable
  c₀ := (5 : Fin 8)
  diag := by
    change ∀ r, A2data.fullMatrix r ((5 : Fin 8), (5 : Fin 8)) = 0
    rw [A2data_fullMatrix]; exact A2.fullMatrix_diag
  raising := fun e => e.val < 3
  raising_table := A2.raising_table
  cartan := fun h => 6 ≤ h.val
  thetaH := fun _ => 1
  cartan_table := by
    intro h hh y
    rw [A2.cartan_table h hh]
    split_ifs <;> simp_all
  hθ := (6 : Fin 8)
  hθ_cartan := by decide
  hθ_ne := one_ne_zero
  lowering := fun i => i = (3 : Fin 8) ∨ i = (4 : Fin 8)
  lowExp := fun _ => 1
  R := 2
  wt := wt2
  table_wt := table_wt2
  lowering_noweight := noweight2
  fusion := fun x => 3 ≤ x.val ∧ x.val < 6
  depth := 3
  cyclic := cyclic_A2

theorem A2sector_carrier : A2sector.toDeligneCarrierData = A2data := rfl

/-! ## Bridges to the A₂ statements -/

theorem localWeylRel_of_G {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule bracketTable V) (w : V) (m : ℕ) (h : LocalWeylRelG A2sector ρ w m) :
    LocalWeylRel ρ w m where
  raising e he r := h.raising e he r
  cartan_pos hh h6 r hr := h.cartan_pos hh h6 r hr
  cartan_zero hh h6 := by
    have := h.cartan_zero hh h6
    simpa [A2sector] using this
  lowering_f1 := by
    have := h.lowering (3 : Fin 8) (Or.inl rfl)
    simpa [A2sector] using this
  lowering_f2 := by
    have := h.lowering (4 : Fin 8) (Or.inr rfl)
    simpa [A2sector] using this
  fusion x hx1 hx2 := h.fusion x ⟨hx1, hx2⟩

theorem fusionModuleBoundG_of (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBound F) :
    FusionModuleBoundG A2sector F where
  le m V _ _ ρ w h b := hU5.le m V ρ w (localWeylRel_of_G ρ w m h) b
  total m V _ _ ρ w h B := hU5.total m V ρ w (localWeylRel_of_G ρ w m h) B

theorem divisorComparisonG_of (hD : A2.DivisorComparison) : DivisorComparisonG A2sector where
  le m x hx p hp := by
    have hx' : x ∈ currentCarrier A2.fullMatrix m 0 := by
      have : A2sector.fullMatrix = A2.fullMatrix := A2data_fullMatrix
      rw [← this]; exact hx
    exact hD.le m x hx' p hp

/-- **The A₂ sector fusion bound, re-derived from the generic chain.** -/
theorem A2_sectorFusionBound_generic (F : ℕ → PowerSeries ℚ) (hU5 : FusionModuleBound F)
    (hD : A2.DivisorComparison) : SectorFusionBound A2data F :=
  sectorFusionBoundG A2sector F (fusionModuleBoundG_of F hU5) (divisorComparisonG_of hD)

end

end VOA.DeligneAudit.DeligneSector

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneSector.cyclic_A2
#print axioms VOA.DeligneAudit.DeligneSector.A2sector
#print axioms VOA.DeligneAudit.DeligneSector.A2_sectorFusionBound_generic
end AxiomAudit
