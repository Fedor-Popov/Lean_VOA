import VOA.Classification.COne.PlusSplitLatticeCharacters

/-! # The two half-lattice Zhu characters

The existing lattice module at j=m has two bottom exponentials. Their E
transitions give eigenvectors with eigenvalues +1 and -1. This constructs
characters of the actual plus Zhu algebra; plus irreducibility is not asserted.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusCharacterTable
open PlusUnitary LatMod VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN PlusC2

theorem rankOne_cocycle (m : ℕ) (a b : (latP m).carrier) :
    latticeCocycle (latP m) a b = 1 := by
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (latP m).carrier) = 1 := by
    rw [← Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ (latP m).carrier)]
    exact rank_latP m
  unfold VOA.IntegralLattice.latticeCocycle VOA.IntegralLattice.cocycle cocExp
  have he : ∀ i j : Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ (latP m).carrier)),
      ¬j < i := by intro i j; have := i.isLt; have := j.isLt; simp only [hc] at *; omega
  simp [he]

/-- The product of the two E transitions is exactly one, including the
comparison coboundary used by the concrete lattice module. -/
theorem half_transition_product (m : ℕ) :
    kap m m (-1) 0 * kap m m 1 (-1) = 1 := by
  have hs : sig m m (-1) * sig m m 1 = 1 := by
    rw [← sig_add]
    norm_num only [neg_add_cancel]
    unfold sig
    change latticeCocycle (glueLat m m) (glueIota m m (0 : (latP m).carrier)) _ = 1
    rw [map_zero, VOA.IntegralLattice.latticeCocycle_zero_left]
  have hc := latCob_ne_zero (latP m) (glueLat m m) (glueIota m m) ((-1 : ℤ) : (latP m).carrier)
  simp only [kap, kappa_eq, rankOne_cocycle, one_mul]
  norm_num only [neg_add_cancel, add_neg_cancel, neg_add_cancel_left, add_zero]
  rw [show (0 : ℤ) = (0 : (latP m).carrier) from rfl, latCob_zero]
  simp only [inv_one, mul_one]
  calc
    _ = (sig m m (-1) * sig m m 1) *
        (latCob (latP m) (glueLat m m) (glueIota m m) ((-1 : ℤ) : (latP m).carrier) *
         (latCob (latP m) (glueLat m m) (glueIota m m) ((-1 : ℤ) : (latP m).carrier))⁻¹) := by ring
    _ = 1 := by rw [hs, mul_inv_cancel₀ hc, one_mul]

/-- A concrete bottom eigenvector; s=1 and s=-1 give the two signs. -/
def halfVector (m : ℕ) (s : ℂ) : LatModuleGen (latP m) :=
  latVacuumGen (latP m) + (s * kap m m (-1) 0) •
    latStateGen (latP m) (vacuumN _) ((-1 : ℤ) : (latP m).carrier)

theorem halfVector_ne_zero (m : ℕ) (s : ℂ) : halfVector m s ≠ 0 := by
  intro h
  have he := congrArg (coordEα (latP m) 0) h
  simp [halfVector, latVacuumGen, latStateGen, coordEα_apply, vacuumN] at he

theorem halfVector_mem (m : ℕ) (hm : 1 ≤ m) (s : ℂ) :
    halfVector m s ∈ (resN m hm (latticeModule m hm m)).weight ((m : ℂ) / 4) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have he : ((((m : ℤ) : ℝ)^2 / (4*m) : ℝ) : ℂ) = (m : ℂ)/4 := by
    push_cast; field_simp
  have hx := latticeModule_vacuum_mem m hm (m : ℤ)
  rw [he] at hx
  have hy := oMod_mem_weight (latticeModule m hm m)
    (show ((EP m hm : VP m hm) : LatModuleGen (latP m)) ∈ (V2m m hm).grading (m : ℤ)
      from EP_mem_grading m hm) hx
  rw [oMod_E_lat_m_vac] at hy
  have hy' := (latticeModule m hm m).weight ((m : ℂ)/4) |>.smul_mem
    ((kap m m (-1) 0)⁻¹) hy
  rw [smul_smul, inv_mul_cancel₀ (kap_ne_zero m m (-1) 0), one_smul] at hy'
  exact Submodule.add_mem _ hx (Submodule.smul_mem _ _ hy')

theorem halfVector_E (m : ℕ) (hm : 1 ≤ m) (s : ℂ) (hs : s * s = 1) :
    oMod (resN m hm (latticeModule m hm m)) (EP m hm) (halfVector m s) =
      s • halfVector m s := by
  rw [oMod_resN m hm _ (EP_mem_grading m hm)]
  simp only [halfVector, map_add, map_smul, oMod_E_lat_m_vac, oMod_E_lat_m_neg,
    smul_add, smul_smul]
  rw [mul_assoc s, half_transition_product, mul_one, ← mul_assoc s s, hs, one_mul]
  exact add_comm _ _

/-- Both half-lattice characters, with precisely normalized (omega,W,E). -/
theorem half_character_exists (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (s : ℂ) (hs : s * s = 1) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ,
      χ (VOA.mk (V2mPlus m hm) (gP m hm 0)) = (m : ℂ)/4 ∧
      χ (VOA.mk (V2mPlus m hm) (gP m hm 1)) = (m : ℂ)/2 ∧
      χ (VOA.mk (V2mPlus m hm) (gP m hm 2)) = s := by
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  let N := resN m hm (latticeModule m hm m)
  have he : ((((m : ℤ) : ℝ)^2 / (4*m) : ℝ) : ℂ) = (m : ℂ)/4 := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    push_cast; field_simp
  have hl : IsLowestWeight N ((m : ℂ)/4) := by
    rw [← he]; exact latticeModule_isLowestWeight m hm m (by simp)
  have hx := halfVector_mem m hm s
  obtain ⟨χ, hχ⟩ := character_of_plus_top_vector m hm hm2 N hl
    (halfVector m s) hx (halfVector_ne_zero m s) ![(m : ℂ)/4, (m : ℂ)/2, s] (by
      intro i; fin_cases i
      · change oMod N (V2mPlus m hm).conformalVector _ = _
        rw [oMod_conformalVector]; exact N.L0_weight _ _ hx
      · change oMod N (WP m hm) _ = _
        rw [oMod_resN m hm _ (WP_mem_grading m hm), WP_coe,
          oMod_W_V2m m hm _ hl hx]
        congr 1; dsimp; ring
      · exact halfVector_E m hm s hs)
  exact ⟨χ, hχ 0, hχ 1, hχ 2⟩

theorem half_plus_character_exists (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm (.inr 2) χ := by
  simpa [HasValues, values, exceptional] using half_character_exists m hm hm2 1 (by norm_num)

theorem half_minus_character_exists (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm (.inr 3) χ := by
  simpa [HasValues, values, exceptional] using half_character_exists m hm hm2 (-1) (by norm_num)

end VOA.Classification.COne.PlusCharacterTable
