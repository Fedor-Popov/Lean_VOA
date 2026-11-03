import VOA.Classification.COne.OrbC2eProducts

/-! # The weight-nine charged generator candidate

An actual nonzero state of V₈⁺ with an executable polynomial description.
Fixedness for the transported cubic action is not asserted here.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section

namespace VOA.Classification.COne.OrbC2e
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 LatMod PlusRat3 OrbC2c

theorem four_ge_one : 1 ≤ (4 : ℕ) := by decide

/-- Charged-left action on any neutral plus state, as a plus-state certificate. -/
theorem hasC_E_smul_neutral (m : ℕ) (hm : 1 ≤ m) {v : VP m hm} {Q : RawPoly ℕ}
    (hv : HasN m hm v Q) (n : ℤ) :
    HasC m hm ((V2mPlus m hm).smul (EP m hm) n v)
      (scaleR 2 (expPolyR (-n-1) (liftR Q))) := by
  have h := smul_xP_PP_of_theta m hm ((1 : ℤ) : (latP m).carrier) n
    (v : LatModuleGen (latP m)) ((mem_VP_iff m hm _).mp v.2)
  rw [PP_of_mem] at h
  change (V2mPlus m hm).smul (EP m hm) n v = _ at h
  rw [hv] at h
  have he : ls m Q = latStateGen (latP m)
      (evRc (a0 m) (cα m) (liftR Q)) 0 := by rw [evRc_liftR]
  rw [he, V2m_charge_smul_evRc, latticeCocycle_zero_right, one_smul] at h
  simp only [map_zero, sub_zero, add_zero] at h
  rw [HasC, h, stP, evRc_scaleR, latStateGen_csmul, map_smul]
  norm_num

def weightNine : VP 4 four_ge_one :=
  (V2mPlus 4 four_ge_one).smul (J 4 four_ge_one) (-2) (EP 4 four_ge_one) -
  (V2mPlus 4 four_ge_one).smul (EP 4 four_ge_one) (-2) (J 4 four_ge_one)

def weightNineRaw : RawPoly ℕ :=
  [(-2, [0,1,1,1,1,1]), (-20, [0,1,1,3]), (-15, [0,1,2,2]),
   (-12, [0,5]), (40, [1,1,1,2]), (60, [1,4]), (40, [2,3])]

theorem weightNine_cert :
    reduceR 8 (scaleR 2 (polyActWC JR 1 P0) ++
      scaleR (-1) (scaleR 2 (expPolyR 1 (liftR JR)))) = weightNineRaw := by
  decide +kernel

/-- Exact polynomial of J₍₋₂₎E − E₍₋₂₎J, with c²=8 reduced. -/
theorem weightNine_hasC : HasC 4 four_ge_one weightNine weightNineRaw := by
  have hJ := hasC_smul_left 4 four_ge_one (hasN_J _ _) (hasC_y0 _ _) (-2)
  have hJE := hasC_smul 4 four_ge_one hJ 2
  have hE := hasC_E_smul_neutral 4 four_ge_one (hasN_J _ _) (-2)
  have h := hasC_add 4 four_ge_one hJE (hasC_smul 4 four_ge_one hE (-1))
  have hsrc : weightNine = (2 : ℂ) •
      (V2mPlus 4 four_ge_one).smul (J 4 four_ge_one) (-2) (y0 4 four_ge_one) +
      (-1 : ℂ) • (V2mPlus 4 four_ge_one).smul (EP 4 four_ge_one) (-2)
        (J 4 four_ge_one) := by
    rw [weightNine, EP_eq_y0, PreVertexAlgebra.smul_smul_right, sub_eq_add_neg, neg_one_smul]
  rw [hsrc]
  norm_num only [Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] at h
  rw [HasC] at h ⊢
  rw [h, ← weightNine_cert, stP, stP, evRc_reduceR]
  convert cα_sq 4 four_ge_one using 1
  norm_num

/-- Projection onto the positive charge recovers half the certified polynomial. -/
theorem coord_stP (m : ℕ) (hm : 1 ≤ m) (P : RawPoly ℕ) :
    coordEα (latP m) ((1 : ℤ) : (latP m).carrier)
      (stP m hm P : LatModuleGen (latP m)) = (1/2 : ℂ) • evRc (a0 m) (cα m) P := by
  classical
  rw [stP, PP_coe, map_smul, map_add, thetaLat_latStateGen]
  simp only [latStateGen, coordEα_apply, al]
  simp only [ite_true]
  split
  · rename_i h
    have hf : False := by
      change (1 : ℤ) = -1 at h
      norm_num at h
    exact hf.elim
  · rw [add_zero]

/-- This algebra homomorphism detects the h(-5) term. -/
def fifthOscillator (m : ℕ) : FockN (rank (latP m)) →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval fun i => if i.1 = 4 then 1 else 0

theorem fifthOscillator_weightNineRaw :
    fifthOscillator 4 (evRc (a0 4) (cα 4) weightNineRaw) = -12 * cα 4 := by
  simp [weightNineRaw, evRc_cons, evRc_nil, evalWordC_cons, evalWordC_nil,
    xvc, fifthOscillator, map_mul]

/-- The constructed weight-nine state is nonzero in the actual plus VOA. -/
theorem weightNine_ne_zero : weightNine ≠ 0 := by
  intro h
  have hs : stP 4 four_ge_one weightNineRaw = 0 := (weightNine_hasC.symm).trans h
  have he := congrArg (fun v : VP 4 four_ge_one =>
    fifthOscillator 4 (coordEα (latP 4) ((1 : ℤ) : (latP 4).carrier)
      (v : LatModuleGen (latP 4)))) hs
  dsimp only at he
  rw [coord_stP, map_smul, fifthOscillator_weightNineRaw] at he
  simp only [ZeroMemClass.coe_zero, map_zero] at he
  change (1/2 : ℂ) * (-12 * cα 4) = 0 at he
  have hz : cα 4 = 0 := by linear_combination (-1/6 : ℂ) * he
  exact cα_ne_zero 4 four_ge_one hz

theorem J_mem_grading_four (m : ℕ) (hm : 1 ≤ m) :
    J m hm ∈ (V2mPlus m hm).grading 4 := by
  change (J m hm : LatModuleGen (latP m)) ∈ (V2m m hm).grading 4
  rw [hasN_J]
  exact latStateGen_mem_grading m hm (w := 4)
    (evR_mem_grading (a0 m) JR (by decide))

theorem weightNine_mem_grading : weightNine ∈ (V2mPlus 4 four_ge_one).grading 9 := by
  have hJ := J_mem_grading_four 4 four_ge_one
  have hE : EP 4 four_ge_one ∈ (V2mPlus 4 four_ge_one).grading (4 : ℤ) :=
    EP_mem_grading 4 four_ge_one
  have hJE := (V2mPlus 4 four_ge_one).smul_mem_grading hJ hE (-2)
  have hEJ := (V2mPlus 4 four_ge_one).smul_mem_grading hE hJ (-2)
  exact Submodule.sub_mem _ hJE hEJ

set_option maxHeartbeats 1600000 in
-- Nine exact normal-ordering certificates on the degree-five charged polynomial.
theorem weightNine_primary_cert (n : Fin 9) :
    reduceR 8 (polyActWC omR (-(n.val : ℤ)-3) weightNineRaw) = [] := by
  fin_cases n <;> decide +kernel

/-- All positive Virasoro modes annihilate the constructed state. -/
theorem weightNine_primary (n : ℤ) (hn : 0 < n) :
    (V2mPlus 4 four_ge_one).L n weightNine = 0 := by
  by_cases h9 : n ≤ 9
  · let i : Fin 9 := ⟨(n-1).toNat, by omega⟩
    have hi : (i.val : ℤ) = n-1 := by dsimp [i]; omega
    have hh := hasC_om 4 four_ge_one (n+1) weightNine_hasC
    have hcert : reduceR 8 (polyActWC omR (-(n+1)-1) weightNineRaw) = normR [] := by
      have hi' : -(n+1)-1 = -(i.val : ℤ)-3 := by omega
      rw [hi']
      exact weightNine_primary_cert i
    have h := hasC_of_reduceR_eq hh hcert
    rw [HasC] at h
    exact h.trans (hasC_zero 4 four_ge_one).symm
  · have h := (V2mPlus 4 four_ge_one).smul_mem_grading
      (V2mPlus 4 four_ge_one).conformal_mem weightNine_mem_grading (n+1)
    rw [(V2mPlus 4 four_ge_one).positivity (2+9-(n+1)-1) (by omega)] at h
    exact h

/-- A genuine primary vector in V₈⁺, with nonvanishing proved independently
by its positive-charge h(-5) coordinate. Cubic fixedness is a separate step. -/
theorem weightNine_nonzero_primary :
    weightNine ≠ 0 ∧ weightNine ∈ (V2mPlus 4 four_ge_one).grading 9 ∧
      ∀ n : ℤ, 0 < n → (V2mPlus 4 four_ge_one).L n weightNine = 0 :=
  ⟨weightNine_ne_zero, weightNine_mem_grading, weightNine_primary⟩

end VOA.Classification.COne.OrbC2e
