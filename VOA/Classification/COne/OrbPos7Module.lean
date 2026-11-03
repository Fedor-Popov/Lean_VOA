import VOA.Classification.COne.OrbPos7Induction

/-! # Unconditional inner-shifted lattice twisted modules

The field map, sign convention, and energy grading are exactly those of `OrbPos5`.
The all-state product identity discharges its last constructor premise.
-/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbPos7
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 OrbPos5 OrbPos6 LatMod TwistedReduction

/-- Star products on the actual torus eigenspace, with no charge projection left. -/
theorem starPF_eigen {n : ℕ} (hn : 0 < n) (a j : ℤ) (r : ℕ) (u : Space)
    (hu : u ∈ (shiftAut n a).twistedEigenspace n r) (v : Space) (e ℓ : ℤ) :
    star ((-(r : ℤ) : ℂ)/n) (rescaledField hn a j (-(r : ℤ)) u) ℓ
      (rescaledField hn a j e v) =
    rescaledField hn a j (-(r : ℤ)+e) ((V2m 1 le_rfl).smul u ℓ v) := by
  have he : shiftAut n a u = phase n (-(r : ℤ)) • u := by
    rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff] at hu
    convert hu using 2
    simp only [phase, Int.cast_neg, Int.cast_natCast]
    congr 1
    ring
  have hh := allStatePF hn a j u v (-(r : ℤ)) e ℓ
  rw [residueProjection_eigen hn a (-(r : ℤ)) u he] at hh
  simpa only [Int.cast_neg] using hh

/-- The full `OrbPos5` target, for every state. -/
theorem shiftedProductFormula {n : ℕ} (hn : 0 < n) (a j : ℤ) :
    OrbPos5.ShiftedProductFormula hn a j := by
  intro r u hu v e _ _ ℓ s x
  change mode (Fld.prod ℓ (rescaledField hn a j (-(r : ℤ)) u)
    (rescaledField hn a j e v)).1 s x = _
  obtain ⟨N₁, hN₁⟩ := Fld.prod_eventually_zero_of_local
    (rescaledField_local hn a j (-(r : ℤ)) e u v)
  obtain ⟨N₂, hN₂⟩ := PreVertexAlgebra.smul_eventually_zero (V2m 1 le_rfl).toPreVertexAlgebra u v
  have hp := pf_of_inverse ((-(r : ℤ) : ℂ)/n)
    (fun ℓ s => mode (Fld.prod ℓ (rescaledField hn a j (-(r : ℤ)) u)
      (rescaledField hn a j e v)).1 s x)
    (fun ℓ s => mode (rescaledField hn a j (-(r : ℤ)+e) ((V2m 1 le_rfl).smul u ℓ v)).1 s x)
    (max N₁ N₂)
    (fun ℓ s hℓ => by beta_reduce; rw [hN₁ ℓ (le_of_max_le_left hℓ), mode_fld_zero])
    (fun ℓ s hℓ => by beta_reduce; rw [hN₂ ℓ (le_of_max_le_right hℓ), map_zero, mode_fld_zero])
    (fun ℓ s => by
      beta_reduce
      obtain ⟨K, hK⟩ := exists_prod_offset_zero (rescaledField_local hn a j (-(r : ℤ)) e u v) ℓ
      rw [← starPF_eigen hn a j r u hu v e ℓ, star_eq_sum_range _ _ _ _ K hK,
        mode_fld_sum, finsum_nat_eq_sum_range K _ (fun d hd => by
          rw [hK d hd, mode_fld_zero, smul_zero])]
      apply Finset.sum_congr rfl
      intro d _
      rw [mode_fld_smul, mode_fzmul, sub_eq_add_neg]) ℓ s
  rw [hp]
  apply finsum_congr
  intro d
  change cbinom ((-(r : ℤ) : ℂ)/n) d •
    mode (resc (shiftedY n a j ((V2m 1 le_rfl).smul u (ℓ+d) v)) n (-(r : ℤ)+e)) (s-d) x = _
  rw [mode_resc]
  rw [show (n : ℤ)*(s-d)+(-(r : ℤ)+e) = (n : ℤ)*(s-d)-(r : ℤ)+e by ring]

/-- Full twisted Jacobi for the explicitly constructed shifted fields. -/
theorem shiftedJacobi {n : ℕ} (hn : 0 < n) (a j : ℤ) :
    TwistedJacobi (shiftAut n a) n (shiftedY n a j) :=
  shiftedJacobi_of_productFormula hn a j (shiftedProductFormula hn a j)

noncomputable def latticeShiftedTwistedModule {n : ℕ} (hn : 0 < n) (a j : ℤ) :
    TwistedModule (shiftAut n a) n Space :=
  OrbPos5.latticeShiftedTwistedModule hn a j (shiftedProductFormula hn a j)

theorem latticeShiftedTwistedModule_irreducible {n : ℕ} (hn : 0 < n) (a j : ℤ) :
    TwistedIrreducible (latticeShiftedTwistedModule hn a j) :=
  OrbPos5.latticeShiftedTwistedModule_irreducible hn a j (shiftedProductFormula hn a j)

theorem latticeShiftedTwistedModule_energyRealization {n : ℕ} (hn : 0 < n) (a j : ℤ) :
    LatticeEnergyRealization (latticeShiftedTwistedModule hn a j) a :=
  OrbPos5.latticeShiftedTwistedModule_energyRealization hn a j (shiftedProductFormula hn a j)

end VOA.Classification.COne.OrbPos7
