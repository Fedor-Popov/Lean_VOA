/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedBaseCase

/-!
# The twisted Jacobi identity of the lattice twisted module  (Moonshine step M6)

From the twisted product formula `PF_all` (`LatticeTwistedBaseCase`), for a `θ`-eigenvector
`u ∈ V_L^j` (so that `piE j u = u`, `piE_of_mem`), inverting the twisted product binomially
(`pf_of_inverse`) gives the product formula in the form required by
`TwistedReduction.twistedJacobi_of_local_pf`; together with the locality `YML_local` this yields

`twistedJacobi_YML : TwistedJacobi (thetaAut L hEven hPos) 2 (YML L hEven hU)` —
the (repaired, DLM) twisted Jacobi identity of `Modularity/Twisted.lean` for the twisted vertex
operator `YML` on `V_L^T = S[θ] ⊗ T`, for **all** pairs of states.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN IntegralLattice LatGen Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

variable (L : IntegralLattice.{0}) (hEven : L.Even) (hU : IsUnit (gramMat L).det) (hPos : L.PosDef)

theorem rescFld_YML (u : LatModuleGen L) (e : ℤ) :
    rescFld (by norm_num : 0 < 2) (YML_truncation L hEven hU u) e = FL L hEven hU e u :=
  Subtype.ext (resc_YML L hEven hU u e)

/-- **The product formula** for the lattice twisted vertex operator, in the form of the
reduction `twistedJacobi_of_local_pf`. -/
theorem productFormula_YML (j : ℕ) (u : LatModuleGen L)
    (hu : u ∈ (thetaAut L hEven hPos).twistedEigenspace 2 j) (v : LatModuleGen L) (e' : ℤ)
    (ℓ s : ℤ) (x : MT L hEven hU) :
    mode (Fld.prod ℓ (rescFld (by norm_num : 0 < 2) (YML_truncation L hEven hU u) (j : ℤ))
        (rescFld (by norm_num : 0 < 2) (YML_truncation L hEven hU v) e')).1 s x
      = ∑ᶠ t : ℕ, cbinom ((((j : ℤ) : ℤ) : ℂ) / (2 : ℕ)) t •
          YML L hEven hU ((latticeVOAGen L hEven hPos).smul u (ℓ + t) v)
            ((2 : ℕ) * (s - t) + (j : ℤ) + e') x := by
  rw [rescFld_YML, rescFld_YML]
  have hc : ((((j : ℤ) : ℤ) : ℂ) / (2 : ℕ)) = ((j : ℤ) : ℂ) / 2 := by push_cast; ring
  rw [hc]
  obtain ⟨N₁, hN₁⟩ := Fld.prod_eventually_zero_of_local (FLloc L hEven hU hPos j e' u v)
  obtain ⟨N₂, hN₂⟩ := PreVertexAlgebra.smul_eventually_zero
    (latticeVOAGen L hEven hPos).toPreVertexAlgebra u v
  have hpf := pf_of_inverse (((j : ℤ) : ℂ) / 2)
    (fun ℓ s => mode (Fld.prod ℓ (FL L hEven hU j u) (FL L hEven hU e' v)).1 s x)
    (fun ℓ s => mode (FL L hEven hU (j + e') ((latticeVOAGen L hEven hPos).smul u ℓ v)).1 s x)
    (max N₁ N₂)
    (fun ℓ s hℓ => by
      beta_reduce
      rw [hN₁ ℓ (le_of_max_le_left hℓ), mode_fld_zero])
    (fun ℓ s hℓ => by
      beta_reduce
      rw [show (latticeVOAGen L hEven hPos).smul u ℓ v = 0 from hN₂ ℓ (le_of_max_le_right hℓ),
        map_zero, mode_fld_zero])
    (fun ℓ s => by
      beta_reduce
      obtain ⟨K, hK⟩ := exists_prod_offset_zero (FLloc L hEven hU hPos j e' u v) ℓ
      have hpe := PF_all L hEven hU hPos u v j e' ℓ
      rw [piE_of_mem L hEven hPos j u hu j (by omega)] at hpe
      rw [← hpe, star_eq_sum_range _ _ _ _ K hK, mode_fld_sum,
        finsum_nat_eq_sum_range K _ (fun i hi => by rw [hK i hi, mode_fld_zero, smul_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mode_fld_smul, mode_fzmul, ← sub_eq_add_neg])
    ℓ s
  rw [hpf]
  refine finsum_congr fun t => ?_
  beta_reduce
  rw [show (2 : ℕ) * (s - t) + (j : ℤ) + e' = 2 * (s - t) + ((j : ℤ) + e') by push_cast; ring,
    YML_eq_mode]

/-- **The twisted Jacobi identity for the lattice twisted module**, for all pairs of states:
`TwistedJacobi (thetaAut L hEven hPos) 2 (YML L hEven hU)`. -/
theorem twistedJacobi_YML : TwistedJacobi (thetaAut L hEven hPos) 2 (YML L hEven hU) :=
  twistedJacobi_of_local_pf (thetaAut L hEven hPos) (YML L hEven hU) (by norm_num)
    (YML_truncation L hEven hU) (fun j => (j : ℤ)) (fun j => by push_cast; omega)
    (fun j u _ v e' _ _ => YML_local L hEven hU hPos u v j e')
    (fun j u hu v e' _ _ ℓ s x => productFormula_YML L hEven hU hPos j u hu v e' ℓ s x)

end VOA.Moonshine.LatticeTwisted
