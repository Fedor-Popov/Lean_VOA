import VOA.Moonshine.MoonshineCNStateFields

/-!
# Complex-frame lattice construction: Conformal

Structural adaptation of `LatticeGenConformal` using a complex bilinear
frame. The carrier, formal-distribution conventions and finite-support proofs
are preserved. No positive-definiteness hypothesis is introduced.
-/

set_option maxHeartbeats 1600000
set_option linter.style.longLine false

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct
open Module (End)
open IntegralLattice HeisenbergN LatGen Reconstruction

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

noncomputable def latticeConformalVector (L : IntegralLattice) : LatModuleGen L := mkEα L 0 (HeisenbergN.ωN (rank L) 1)


theorem latticeConformalVector_mem (L : IntegralLattice) : latticeConformalVector L ∈ gradingLatGen L 2 := by
  have hb : HeisenbergN.ωN (rank L) 1 ∈ HeisenbergN.gradingZN (rank L) 2 :=
    HeisenbergN.ωN_mem_gradingZN_two (rank L) 1
  have hmem : latticeConformalVector L ∈ bigradα L (2, 0) := by
    rw [latticeConformalVector, bigradα]; exact Submodule.mem_map_of_mem hb
  have hle := bigradα_le_gradingLatGen L 2 0 hmem
  rwa [show (2 : ℤ) + halfNorm L 0 = 2 from by rw [halfNorm_zero]; ring] at hle


noncomputable def frameSugawaraField : FormalDist (End ℂ (LatModuleGen L)) :=
  (1 / 2 : ℂ) • ∑ a : Fin (rank L), nprod (frameCurrent_isField F a) (frameCurrent_isField F a)


theorem frameSugawaraField_isField : IsField (frameSugawaraField F) := by
  rw [frameSugawaraField]
  exact IsField.smul (1 / 2) (IsField.finsetSum _ _ fun a _ =>
    IsField.nprod (frameCurrent_isField F a) (frameCurrent_isField F a))


theorem frameSugawaraField_DCovariant : Reconstruction.DCovariant (frameTranslation F) (frameSugawaraField F) := by
  rw [frameSugawaraField]
  refine Reconstruction.DCovariant.smul (1 / 2) ?_
  refine Reconstruction.DCovariant.finsetSum _ _ fun a _ => ?_
  exact Reconstruction.DCovariant.nprod (frameCurrent_isField F a) (frameCurrent_isField F a)
    (frameTranslation_frameCurrent_DCovariant F a) (frameTranslation_frameCurrent_DCovariant F a)


theorem frameSugawaraField_vacuum_neg {q : ℤ} (hq : q < 0) : frameSugawaraField F q (latVacuumGen L) = 0 := by
  rw [frameSugawaraField]
  change (1 / 2 : ℂ) • (((∑ a : Fin (rank L),
      nprod (frameCurrent_isField F a) (frameCurrent_isField F a)) q) (latVacuumGen L)) = 0
  rw [show ((∑ a : Fin (rank L),
          nprod (frameCurrent_isField F a) (frameCurrent_isField F a)) q : End ℂ (LatModuleGen L))
        = ∑ a : Fin (rank L), nprod (frameCurrent_isField F a) (frameCurrent_isField F a) q from
      Finset.sum_apply (s := Finset.univ)
        (g := fun a : Fin (rank L) => nprod (frameCurrent_isField F a) (frameCurrent_isField F a)) q,
    LinearMap.coe_sum, Finset.sum_apply,
    Finset.sum_eq_zero (fun a _ => by
      exact nprod_vacuum_neg_gen (frameCurrent_isField F a) (frameCurrent_isField F a)
        (latVacuumGen L) (fun s hs => frameCurrent_vacuum_neg F a hs)
        (fun s hs => frameCurrent_vacuum_neg F a hs) hq),
    smul_zero]


theorem frameSugawaraField_local_frameWordField (hEven : L.Even) 
    (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    Local (frameSugawaraField F) (frameWordField F l α) := by
  rw [frameSugawaraField]
  refine VertexOperatorAlgebra.Local.smul' (1 / 2) ?_
  refine Local.sum_left _ _ _ fun a _ => ?_
  have hac : Local (frameCurrent F a) (frameWordField F l α) := by
    rw [← frameDerivativeCurrent_zero]; exact frameDerivativeCurrent_local_frameWordField F hEven a 0 l α
  exact dong_neg (frameCurrent_isField F a) (frameCurrent_isField F a)
    (frameCurrent_self_local F a a) hac hac


theorem frameSugawaraField_base_frame (a : Fin (rank L)) :
    (1 / 2 : ℂ) • (nprod (frameCurrent_isField F a) (frameCurrent_isField F a) 0 (latVacuumGen L))
      = mkEα L 0 (HeisenbergN.ωNa (rank L) 1 a) := by
  rw [nprod_vacuum_base_gen (frameCurrent_isField F a) (frameCurrent_isField F a) (latVacuumGen L)
      (fun s hs => frameCurrent_vacuum_neg F a hs) (fun s hs => frameCurrent_vacuum_neg F a hs)]
  have ha0 : frameCurrent F a 0 = LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a 0) := by
    rw [frameCurrent_apply, if_neg (by norm_num : ¬ (0 : ℤ) = -1), add_zero]
  rw [ha0, latVacuumGen_eq_mkEα, mkEα_apply, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
    TensorProduct.smul_tmul', mkEα_apply, HeisenbergN.ωNa, currentN_apply,
    show (-(0 : ℤ) - 1) = -1 from by ring, show (1 / 2 : ℂ) = 1 / (2 * 1) from by norm_num]


theorem frameStateField_omega_eq (hEven : L.Even)  :
    frameStateField F hEven (latticeConformalVector L) = frameSugawaraField F := by
  have hloc : ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      Local (frameStateField F hEven (latticeConformalVector L) - frameSugawaraField F) (frameWordField F l α) := by
    intro l α
    have h1 : Local (frameStateField F hEven (latticeConformalVector L)) (frameWordField F l α) := by
      rw [← frameStateField_word F hEven l α]
      exact frameStateField_local F hEven (latticeConformalVector L) (frameWordState L l α)
    have h2 : Local (frameSugawaraField F) (frameWordField F l α) :=
      frameSugawaraField_local_frameWordField F hEven l α
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (frameSugawaraField F)]
    exact Reconstruction.Local.add_left h1 (VertexOperatorAlgebra.Local.smul' (-1) h2)
  have hbase : (frameStateField F hEven (latticeConformalVector L)) 0 (latVacuumGen L)
      = (frameSugawaraField F) 0 (latVacuumGen L) := by
    rw [frameStateField_cre0]
    symm
    rw [frameSugawaraField]
    change (1 / 2 : ℂ) • (((∑ a : Fin (rank L),
        nprod (frameCurrent_isField F a) (frameCurrent_isField F a)) 0) (latVacuumGen L))
        = latticeConformalVector L
    rw [show ((∑ a : Fin (rank L),
            nprod (frameCurrent_isField F a) (frameCurrent_isField F a)) 0 : End ℂ (LatModuleGen L))
          = ∑ a : Fin (rank L), nprod (frameCurrent_isField F a) (frameCurrent_isField F a) 0 from
        Finset.sum_apply (s := Finset.univ)
          (g := fun a : Fin (rank L) => nprod (frameCurrent_isField F a) (frameCurrent_isField F a)) 0,
      LinearMap.coe_sum, Finset.sum_apply, Finset.smul_sum,
      Finset.sum_congr rfl (fun a _ => frameSugawaraField_base_frame F a), ← map_sum (mkEα L 0),
      ← HeisenbergN.ωN]
    rfl
  have hAvac : ∀ p : ℤ,
      (frameStateField F hEven (latticeConformalVector L) - frameSugawaraField F) p (latVacuumGen L) = 0 := by
    intro p
    change ((frameStateField F hEven (latticeConformalVector L)) p - (frameSugawaraField F) p) (latVacuumGen L) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact Reconstruction.tower_unique (frameStateField_DCov F hEven (latticeConformalVector L))
      (frameSugawaraField_DCovariant F) (frameTranslation_vacuum F) hbase
      (fun q hq => frameStateField_creneg F hEven (latticeConformalVector L) hq)
      (fun q hq => frameSugawaraField_vacuum_neg F hq) p
  have hz := Reconstruction.field_eq_zero_of_vacuum (latVacuumGen L)
    (frameStateField F hEven (latticeConformalVector L) - frameSugawaraField F)
    (Function.uncurry (frameWordState L))
    (Function.uncurry (fun l α => frameWordField F l α))
    (fun lα => hloc lα.1 lα.2)
    (fun lα => frameWordField_vacuum_base F lα.1 lα.2)
    (fun lα q hq => frameWordField_vacuum_neg F lα.1 lα.2 hq)
    hAvac (frameWordState_span L)
  rwa [sub_eq_zero] at hz


end VOA.Moonshine.ConwayNorton
