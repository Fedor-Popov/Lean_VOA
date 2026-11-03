import VOA.Classification.COne.OrbC2eGenerator

/-! # The weight-sixteen seed and explicit fixedness implications

The nonzero weight-nine and weight-sixteen states are constructed in V₈⁺.
The two final implications assume the cubic action formulas on J and E;
those formulas for the actual transported automorphism are still unproved.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section

namespace VOA.Classification.COne.OrbC2e
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 LatMod PlusRat3 OrbC2c

open Classical in
theorem coord_charge_product (m : ℕ) (hm : 1 ≤ m)
    (β γ δ : ℤ) (n : ℤ) :
    coordEα (latP m) δ
      ((V2m m hm).smul (latChargeGen (latP m) β) n (latChargeGen (latP m) γ)) =
    latticeCocycle (latP m) β γ • (if δ = β+γ then
      evRc (a0 m) (chargeCoord (latP m) β (a0 m))
        (if 0 ≤ -n-1-(latP m).form β γ then
          schurR (-n-1-(latP m).form β γ).toNat else []) else 0) := by
  classical
  rw [V2m_charge_smul_charge, map_smul, latStateGen, coordEα_apply]
  congr 2

def weightSixteen : VP 4 four_ge_one :=
  (V2mPlus 4 four_ge_one).smul (J 4 four_ge_one) (-9) (J 4 four_ge_one) +
    (27 : ℂ) • (V2mPlus 4 four_ge_one).smul (EP 4 four_ge_one) (-9) (EP 4 four_ge_one)

/-- The second-charge coordinate is exactly 27 times its ground state. -/
theorem coord_weightSixteen :
    coordEα (latP 4) ((2 : ℤ) : (latP 4).carrier)
      (weightSixteen : LatModuleGen (latP 4)) = (27 : ℂ) • (1 : FockN (rank (latP 4))) := by
  classical
  have hJJ : coordEα (latP 4) ((2 : ℤ) : (latP 4).carrier)
      ((V2mPlus 4 four_ge_one).smul (J 4 four_ge_one) (-9) (J 4 four_ge_one) :
        LatModuleGen (latP 4)) = 0 := by
    rw [hasN_smul_left 4 four_ge_one (hasN_J 4 four_ge_one) (hasN_J 4 four_ge_one),
      ls, latStateGen, coordEα_apply]
    exact if_neg (by change ¬(2 : ℤ) = 0; omega)
  have hEE : coordEα (latP 4) ((2 : ℤ) : (latP 4).carrier)
      ((V2mPlus 4 four_ge_one).smul (EP 4 four_ge_one) (-9) (EP 4 four_ge_one) :
        LatModuleGen (latP 4)) = 1 := by
    rw [V2mPlus_smul_coe, EP_coe, PreVertexAlgebra.smul_add_left,
      PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_add_right, map_add, map_add, map_add]
    rw [coord_charge_product, coord_charge_product, coord_charge_product, coord_charge_product]
    norm_num [latP_form, PlusCharacterTable.rankOne_cocycle, schurR,
      evRc_cons, evRc_nil, evalWordC_nil]
  change coordEα (latP 4) (2 : ℤ) (_ + (27 : ℂ) • _) = _
  rw [map_add, map_smul, hJJ, hEE, zero_add]

theorem weightSixteen_ne_zero : weightSixteen ≠ 0 := by
  intro h
  have he := coord_weightSixteen
  rw [h] at he
  change (0 : FockN (rank (latP 4))) = (27 : ℂ) • 1 at he
  have hz := (smul_eq_zero.mp he.symm).resolve_left (by norm_num)
  exact one_ne_zero hz

theorem weightSixteen_mem_grading :
    weightSixteen ∈ (V2mPlus 4 four_ge_one).grading 16 := by
  have hJ := J_mem_grading_four 4 four_ge_one
  have hE : EP 4 four_ge_one ∈ (V2mPlus 4 four_ge_one).grading (4 : ℤ) :=
    EP_mem_grading 4 four_ge_one
  have hJJ := (V2mPlus 4 four_ge_one).smul_mem_grading hJ hJ (-9)
  have hEE := (V2mPlus 4 four_ge_one).smul_mem_grading hE hE (-9)
  exact Submodule.add_mem _ hJJ (Submodule.smul_mem _ _ hEE)

/-- The cubic generator action implies fixedness of the actual weight-nine state.
This does not assert that the action formulas hold for `kleinCubic`. -/
theorem weightNine_fixed_of_action (g : Aut (V2mPlus 4 four_ge_one))
    (hJ : g (J 4 four_ge_one) = (-1 / 2 : ℂ) • J 4 four_ge_one +
      (9 / 2 : ℂ) • EP 4 four_ge_one)
    (hE : g (EP 4 four_ge_one) = (-1 / 6 : ℂ) • J 4 four_ge_one +
      (-1 / 2 : ℂ) • EP 4 four_ge_one) : g weightNine = weightNine := by
  simp only [weightNine, map_sub, Aut.map_smul, hJ, hE, PreVertexAlgebra.smul_add_left,
    PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
  module

/-- The same action formulas also fix the constructed weight-sixteen seed. -/
theorem weightSixteen_fixed_of_action (g : Aut (V2mPlus 4 four_ge_one))
    (hJ : g (J 4 four_ge_one) = (-1 / 2 : ℂ) • J 4 four_ge_one +
      (9 / 2 : ℂ) • EP 4 four_ge_one)
    (hE : g (EP 4 four_ge_one) = (-1 / 6 : ℂ) • J 4 four_ge_one +
      (-1 / 2 : ℂ) • EP 4 four_ge_one) : g weightSixteen = weightSixteen := by
  simp only [weightSixteen, map_add, map_smul, Aut.map_smul, hJ, hE,
    PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
  module

end VOA.Classification.COne.OrbC2e
