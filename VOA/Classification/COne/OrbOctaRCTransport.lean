import VOA.Classification.COne.OrbOctaRCPrimary

/-! The explicit primary in the norm-eight model and its fixed-point transport. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice VOA.SparseRational
  HeisenbergN MvPolynomial PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g
  LatMod OrbOctaR OrbC2b OrbSpan ConverseUniverse

private abbrev frameScalar : ℂ :=
  oscMatrix (latP 4) (latP 1) (scaleIota 1 2) (a0 1) (a0 4)

theorem scale_fock_word (w : List ℕ) :
    fockMap (oscMatrix (latP 4) (latP 1) (scaleIota 1 2))
      (evalWord (xv (a0 4)) w) =
        frameScalar ^ w.length • evalWord (xv (a0 1)) w := by
  induction w with
  | nil => simp [evalWord_nil]
  | cons i w ih =>
    simp only [evalWord_cons, map_mul, fockMap_X, rankOne_sum, ih,
      List.length_cons, pow_succ, smul_mul_smul_comm]
    congr 1
    ring

theorem scale_fock_even (P : RawPoly ℕ) (hP : ∀ t ∈ P, Even t.2.length) :
    fockMap (oscMatrix (latP 4) (latP 1) (scaleIota 1 2)) (evR (a0 4) P) =
      evR (a0 1) P := by
  induction P with
  | nil => simp [evR_nil]
  | cons t P ih =>
    rcases t with ⟨q, w⟩
    have hw := hP (q, w) (by simp)
    have he : frameScalar ^ w.length = 1 := by
      obtain ⟨j, hj⟩ := hw
      rw [hj, ← two_mul, pow_mul, scale_osc_square, one_pow]
    rw [evR_cons, map_add, map_smul, scale_fock_word, he, one_smul,
      ih (fun t ht => hP t (by simp [ht])), evR_cons]

theorem primaryV8_value : scaleMorph 1 2 primaryV8 = (OrbOctaR.X : LatModuleGen (latP 1)) := by
  rw [primaryV8, map_add, map_add, map_smul, map_smul, X_lattice_value]
  have hN : scaleMorph 1 2 (ls 4 primaryNeutral) = ls 1 primaryNeutral := by
    change latMorph (latP 4) (latP 1) (scaleIota 1 2)
      (latStateGen (latP 4) (evR (a0 4) primaryNeutral) 0) = _
    rw [latMorph_latStateGen, rankOne_latCob, one_smul,
      scale_fock_even _ primaryNeutral_even, map_zero]
  have hE (d : ℤ) : scaleMorph 1 2 (latChargeGen (latP 4) d) =
      latChargeGen (latP 1) (2 * d) := by
    change latMorph (latP 4) (latP 1) (scaleIota 1 2) (latStateGen _ 1 d) = _
    rw [latMorph_latStateGen, rankOne_latCob, one_smul, map_one]
    rfl
  rw [hN, hE, hE]
  rfl

theorem primaryV8_primary : primaryV8 ∈ prim (V2m 4 four_ge_one) 16 := by
  have hf : IsVOAHom (V2m 4 four_ge_one) (V2m 1 le_rfl) (scaleMorph 1 2) :=
    scaleMorph_isVOAHom 1 le_rfl 2
  have hω : scaleMorph 1 2 (V2m 4 four_ge_one).conformalVector =
      (V2m 1 le_rfl).conformalVector := scaleMorph_omega 1 le_rfl 2
  obtain ⟨hg, hp⟩ := (mem_prim _).mp X_ambient_primary
  rw [mem_prim]
  constructor
  · apply mem_grading_of_L0
    apply scaleMorph_injective 1 le_rfl 2
    rw [hf.map_L hω, map_smul, primaryV8_value, (V2m 1 le_rfl).L_zero_grading _ hg]
  · intro m
    apply scaleMorph_injective 1 le_rfl 2
    rw [hf.map_L hω, primaryV8_value, hp, map_zero]

def Xklein : (orbifold klein).carrier :=
  ⟨(OrbOctaR.X : LatModuleGen (latP 1)),
    fun g hg => OrbOctaR.X.property g (OrbC2d.klein_le_octa hg)⟩

def primaryPlus : VP 4 four_ge_one := plusToKlein.symm Xklein

theorem primaryPlus_value : (primaryPlus : LatModuleGen (latP 4)) = primaryV8 := by
  apply scaleMorph_injective 1 le_rfl 2
  rw [← plusToKlein_val, primaryPlus, LinearEquiv.apply_symm_apply, primaryV8_value]
  rfl

theorem primaryV8_S4_fixed (g : Aut (V2m 1 le_rfl)) (hg : g ∈ octa) :
    g (scaleMorph 1 2 primaryV8) = scaleMorph 1 2 primaryV8 := by
  rw [primaryV8_value]
  exact OrbOctaR.X.property g hg

theorem primaryPlus_cubic_fixed : plusCubic primaryPlus = primaryPlus := by
  apply plusToKlein.injective
  rw [plusCubic_intertwine, primaryPlus, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  have hg : rotC ∈ octa := by
    rw [octa_eq_join]
    apply Subgroup.mem_sup_left
    rw [tetra_eq_join]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers rotC)
  exact OrbOctaR.X.property rotC hg

def fixedPrimaryV8 : (orbifold (Subgroup.zpowers plusCubic)).carrier :=
  ⟨primaryPlus, (mem_orbifold_zpowers_iff _ _).mpr primaryPlus_cubic_fixed⟩

theorem fixedEquivKlein_primary_value :
    ((fixedEquivKlein fixedPrimaryV8 : (orbifold klein).carrier) : LatModuleGen (latP 1)) =
      (OrbOctaR.X : LatModuleGen (latP 1)) := by
  change (plusToKlein primaryPlus : LatModuleGen (latP 1)) = _
  rw [primaryPlus, LinearEquiv.apply_symm_apply]
  rfl

end VOA.Classification.COne.OrbOctaRC
