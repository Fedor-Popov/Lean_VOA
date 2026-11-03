import VOA.Classification.COne.OrbPos5Support
import VOA.Moonshine.HeisenbergTwistedModuleLocality
import VOA.Moonshine.VnatBlock

/-!
# Mutual locality of all rescaled shifted lattice fields

Each rescaled field is a finite linear combination of integral monomial
shifts of ordinary lattice-module fields. Their mutual locality follows
from ordinary module Jacobi. Identification of their field products with
the twisted iterate is a separate identity, not asserted here.
-/

namespace VOA.Classification.COne.OrbPos5
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 LatMod TwistedReduction

noncomputable def ordinaryShiftSpan (j : ℤ) :
    Submodule ℂ (FormalDist (Module.End ℂ Space)) :=
  Submodule.span ℂ {F | ∃ (q : ℤ) (u : Space),
    F = zmul q ((latticeModule 1 le_rfl j).YM u)}

theorem ordinaryShiftSpan_local (j : ℤ)
    {F G : FormalDist (Module.End ℂ Space)}
    (hF : F ∈ ordinaryShiftSpan j) (hG : G ∈ ordinaryShiftSpan j) : Local F G := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨q, u, rfl⟩ := hF
    induction hG using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨r, v, rfl⟩ := hG
      exact Local.zmul_right (Local.zmul_left
        (Moonshine.VnatBlock.local_YM (latticeModule 1 le_rfl j).toWeakModule u v) q) r
    | zero => exact (Reconstruction.Local.zero_left _).symm
    | add G H _ _ hG hH => exact (VertexOperatorAlgebra.Local.add hG.symm hH.symm).symm
    | smul c G _ hG => exact (VertexOperatorAlgebra.Local.smul' c hG.symm).symm
  | zero => exact Reconstruction.Local.zero_left _
  | add F H _ _ hF hH => exact VertexOperatorAlgebra.Local.add hF hH
  | smul c F _ hF => exact VertexOperatorAlgebra.Local.smul' c hF

/-- Rescaling one coefficient gives an integral monomial shift of an
ordinary vertex operator, or zero when its charge misses the residue class. -/
theorem resc_coefficientField {n : ℕ} (hn : 0 < n) (a j β e : ℤ)
    (d : ℕ) (p : Osc) :
    resc (coefficientField n a j β d p) n e =
      if (e-a*β) % (n : ℤ) = 0 then
        zmul ((e-a*β)/(n : ℤ)-d) ((latticeModule 1 le_rfl j).YM
          (latStateGen (latP 1) p β)) else 0 := by
  have hn0 : (n : ℤ) ≠ 0 := by omega
  funext t
  simp only [resc, coefficientField, LinearMap.coe_mk, AddHom.coe_mk]
  rw [show (n : ℤ)*(-t-1)+e-a*β = (n : ℤ)*(-t-1)+(e-a*β) by ring]
  simp only [Int.add_emod, Int.mul_emod_right, zero_add, Int.emod_emod]
  split_ifs
  · rw [Int.mul_add_ediv_left _ _ hn0]
    simp only [mode_apply, zmul]
    rw [show -(-t - 1 + (e - a * β) / (n : ℤ) - d) - 1 =
      t - ((e - a * β) / (n : ℤ) - d) by ring]
  · rfl

theorem resc_coefficientField_mem {n : ℕ} (hn : 0 < n) (a j β e : ℤ)
    (d : ℕ) (p : Osc) :
    resc (coefficientField n a j β d p) n e ∈ ordinaryShiftSpan j := by
  rw [resc_coefficientField hn]
  split_ifs
  · exact Submodule.subset_span ⟨_, _, rfl⟩
  · exact Submodule.zero_mem _

/-- Rescaling is linear in the fractional mode family. -/
def rescaleLinear (n : ℕ) (e : ℤ) : Modes →ₗ[ℂ] FormalDist (Module.End ℂ Space) where
  toFun F := resc F n e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resc_sectorField_mem {n : ℕ} (hn : 0 < n) (a j β e : ℤ) (p : Osc) :
    resc (sectorField n a j β p) n e ∈ ordinaryShiftSpan j := by
  classical
  change rescaleLinear n e (sectorField n a j β p) ∈ ordinaryShiftSpan j
  rw [sectorField, LinearMap.comp_apply, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  exact Submodule.sum_mem _ fun d _ => resc_coefficientField_mem hn a j β e d _

theorem resc_shiftedY_mem {n : ℕ} (hn : 0 < n) (a j e : ℤ) (u : Space) :
    resc (shiftedY n a j u) n e ∈ ordinaryShiftSpan j := by
  have ht : (ordinaryShiftSpan j).comap ((rescaleLinear n e).comp (shiftedY n a j)) = ⊤ := by
    rw [eq_top_iff, ← latStateGen_span (latP 1)]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨p, β⟩, rfl⟩
    change resc (shiftedY n a j (latStateGen (latP 1) p β)) n e ∈ ordinaryShiftSpan j
    rw [shiftedY_latState]
    exact resc_sectorField_mem hn a j β e p
  have hu : u ∈ (ordinaryShiftSpan j).comap
      ((rescaleLinear n e).comp (shiftedY n a j)) := by rw [ht]; trivial
  exact hu

/-- Mutual locality on every pair of states and every pair of residue offsets.
This discharges the locality half of the library's twisted Jacobi reduction. -/
theorem shiftedY_local {n : ℕ} (hn : 0 < n) (a j e f : ℤ) (u v : Space) :
    Local (resc (shiftedY n a j u) n e) (resc (shiftedY n a j v) n f) :=
  ordinaryShiftSpan_local j (resc_shiftedY_mem hn a j e u) (resc_shiftedY_mem hn a j f v)

end VOA.Classification.COne.OrbPos5
