/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenVOAInstance
import VOA.Examples.LatticeGenGrading

/-!
# The conformal layer of the general even-lattice VOA

The conformal vector `ω = ωN(rank L,1) ⊗ e^0`, the frame Sugawara field, the Virasoro relation with
central charge `c = rank L`, the `L₀`-grading and translation.  Cross-charge lift of A₁'s
`LatticeVOAInstance` conformal layer (`c = 1 → rank L`, single boson → frame sum `∑ₐ`).

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN Reconstruction

variable (L : IntegralLattice)

/-! ## §A  The conformal vector `ω`. -/

/-- The lattice conformal vector `ω = ωN(rank L, 1) ⊗ e^0` (the frame Sugawara state, charge 0). -/
noncomputable def omegaLatGen : LatModuleGen L := mkEα L 0 (HeisenbergN.ωN (rank L) 1)

/-- **`ω ∈ gradingLatGen 2`** (`conformal_mem`): `ω` is boson-weight-2, charge-0. -/
theorem omegaLatGen_mem : omegaLatGen L ∈ gradingLatGen L 2 := by
  have hb : HeisenbergN.ωN (rank L) 1 ∈ HeisenbergN.gradingZN (rank L) 2 :=
    HeisenbergN.ωN_mem_gradingZN_two (rank L) 1
  have hmem : omegaLatGen L ∈ bigradα L (2, 0) := by
    rw [omegaLatGen, bigradα]; exact Submodule.mem_map_of_mem hb
  have hle := bigradα_le_gradingLatGen L 2 0 hmem
  rwa [show (2 : ℤ) + halfNorm L 0 = 2 from by rw [halfNorm_zero]; ring] at hle

/-! ## §B  The frame Sugawara field `T(z) = ½∑ₐ :α^a(z)²:`. -/

/-- The **frame Sugawara field** `T(z) = ½∑ₐ :α^a(z)α^a(z):` (level-`1` orthonormal frame). -/
noncomputable def sugFieldGen : FormalDist (End ℂ (LatModuleGen L)) :=
  (1 / 2 : ℂ) • ∑ a : Fin (rank L), nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a)

theorem sugFieldGen_isField : IsField (sugFieldGen L) := by
  rw [sugFieldGen]
  exact IsField.smul (1 / 2) (IsField.finsetSum _ _ fun a _ =>
    IsField.nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a))

theorem sugFieldGen_DCovariant : Reconstruction.DCovariant (TrecGen L) (sugFieldGen L) := by
  rw [sugFieldGen]
  refine Reconstruction.DCovariant.smul (1 / 2) ?_
  refine Reconstruction.DCovariant.finsetSum _ _ fun a _ => ?_
  exact Reconstruction.DCovariant.nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a)
    (TrecGen_alphaLatGen_DCovariant L a) (TrecGen_alphaLatGen_DCovariant L a)

theorem sugFieldGen_vacuum_neg {q : ℤ} (hq : q < 0) : sugFieldGen L q (latVacuumGen L) = 0 := by
  rw [sugFieldGen]
  change (1 / 2 : ℂ) • (((∑ a : Fin (rank L),
      nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a)) q) (latVacuumGen L)) = 0
  rw [show ((∑ a : Fin (rank L),
          nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a)) q : End ℂ (LatModuleGen L))
        = ∑ a : Fin (rank L), nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a) q from
      Finset.sum_apply (s := Finset.univ)
        (g := fun a : Fin (rank L) => nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a)) q,
    LinearMap.coe_sum, Finset.sum_apply,
    Finset.sum_eq_zero (fun a _ => by
      exact nprod_vacuum_neg_gen (alphaLatGen_isField L a) (alphaLatGen_isField L a)
        (latVacuumGen L) (fun s hs => alphaLatGen_vacuum_neg L a hs)
        (fun s hs => alphaLatGen_vacuum_neg L a hs) hq),
    smul_zero]

theorem sugFieldGen_local_YwordLatGen (hEven : L.Even) (hPos : L.PosDef)
    (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    Local (sugFieldGen L) (YwordLatGen L l α) := by
  rw [sugFieldGen]
  refine VertexOperatorAlgebra.Local.smul' (1 / 2) ?_
  refine Local.sum_left _ _ _ fun a _ => ?_
  have hac : Local (alphaLatGen L a) (YwordLatGen L l α) := by
    rw [← genFieldLatGen_zero]; exact genFieldLatGen_local_YwordLatGen L hEven hPos a 0 l α
  exact dong_neg (alphaLatGen_isField L a) (alphaLatGen_isField L a)
    (alphaLatGen_self_local L a a) hac hac

/-! ## §C  The vacuum base value and the main identity `YfullGen ω = sugFieldGen`. -/

/-- The **per-frame Sugawara base value** `½ :α^a α^a:₀ |0⟩ = ωᵃ ⊗ e^0` (level `k = 1`). -/
theorem sugFieldGen_base_frame (a : Fin (rank L)) :
    (1 / 2 : ℂ) • (nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a) 0 (latVacuumGen L))
      = mkEα L 0 (HeisenbergN.ωNa (rank L) 1 a) := by
  rw [nprod_vacuum_base_gen (alphaLatGen_isField L a) (alphaLatGen_isField L a) (latVacuumGen L)
      (fun s hs => alphaLatGen_vacuum_neg L a hs) (fun s hs => alphaLatGen_vacuum_neg L a hs)]
  have ha0 : alphaLatGen L a 0 = LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a 0) := by
    rw [alphaLatGen_apply, if_neg (by norm_num : ¬ (0 : ℤ) = -1), add_zero]
  rw [ha0, latVacuumGen_eq_mkEα, mkEα_apply, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
    TensorProduct.smul_tmul', mkEα_apply, HeisenbergN.ωNa, currentN_apply,
    show (-(0 : ℤ) - 1) = -1 from by ring, show (1 / 2 : ℂ) = 1 / (2 * 1) from by norm_num]

/-- **`YfullGen ω = sugFieldGen`**: the field of the conformal vector is the frame Sugawara field
(operator-first uniqueness via the shared vacuum tower). -/
theorem YfullGen_omega_eq (hEven : L.Even) (hPos : L.PosDef) :
    YfullGen L hEven hPos (omegaLatGen L) = sugFieldGen L := by
  have hloc : ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      Local (YfullGen L hEven hPos (omegaLatGen L) - sugFieldGen L) (YwordLatGen L l α) := by
    intro l α
    have h1 : Local (YfullGen L hEven hPos (omegaLatGen L)) (YwordLatGen L l α) := by
      rw [← YfullGen_word L hEven hPos l α]
      exact YfullGen_local L hEven hPos (omegaLatGen L) (wordStateLatGen L l α)
    have h2 : Local (sugFieldGen L) (YwordLatGen L l α) :=
      sugFieldGen_local_YwordLatGen L hEven hPos l α
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (sugFieldGen L)]
    exact Reconstruction.Local.add_left h1 (VertexOperatorAlgebra.Local.smul' (-1) h2)
  have hbase : (YfullGen L hEven hPos (omegaLatGen L)) 0 (latVacuumGen L)
      = (sugFieldGen L) 0 (latVacuumGen L) := by
    rw [YfullGen_cre0]
    symm
    rw [sugFieldGen]
    change (1 / 2 : ℂ) • (((∑ a : Fin (rank L),
        nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a)) 0) (latVacuumGen L))
        = omegaLatGen L
    rw [show ((∑ a : Fin (rank L),
            nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a)) 0 : End ℂ (LatModuleGen L))
          = ∑ a : Fin (rank L), nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a) 0 from
        Finset.sum_apply (s := Finset.univ)
          (g := fun a : Fin (rank L) => nprod (alphaLatGen_isField L a) (alphaLatGen_isField L a)) 0,
      LinearMap.coe_sum, Finset.sum_apply, Finset.smul_sum,
      Finset.sum_congr rfl (fun a _ => sugFieldGen_base_frame L a), ← map_sum (mkEα L 0),
      ← HeisenbergN.ωN]
    rfl
  have hAvac : ∀ p : ℤ,
      (YfullGen L hEven hPos (omegaLatGen L) - sugFieldGen L) p (latVacuumGen L) = 0 := by
    intro p
    change ((YfullGen L hEven hPos (omegaLatGen L)) p - (sugFieldGen L) p) (latVacuumGen L) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact Reconstruction.tower_unique (YfullGen_DCov L hEven hPos (omegaLatGen L))
      (sugFieldGen_DCovariant L) (TrecGen_vacuum L) hbase
      (fun q hq => YfullGen_creneg L hEven hPos (omegaLatGen L) hq)
      (fun q hq => sugFieldGen_vacuum_neg L hq) p
  have hz := Reconstruction.field_eq_zero_of_vacuum (latVacuumGen L)
    (YfullGen L hEven hPos (omegaLatGen L) - sugFieldGen L)
    (Function.uncurry (wordStateLatGen L))
    (Function.uncurry (fun l α => YwordLatGen L l α))
    (fun lα => hloc lα.1 lα.2)
    (fun lα => YwordLatGen_vacuum_base L lα.1 lα.2)
    (fun lα q hq => YwordLatGen_vacuum_neg L lα.1 lα.2 hq)
    hAvac (wordStateLatGen_span L)
  rwa [sub_eq_zero] at hz

end VOA.LatGen
