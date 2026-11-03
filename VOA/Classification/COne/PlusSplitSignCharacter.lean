import VOA.Classification.COne.PlusSplitHalfCharacters

/-! # The sign-sector ordinary module and its Zhu character

The anti-invariant part of the lattice adjoint module has bottom weight one.
The neutral one-oscillator vector gives the character (1,12,0).
No irreducibility assertion is needed for the character construction.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusCharacterTable
open PlusUnitary PlusC2 PlusC2Eval LatMod VOA.LatGen VOA.LatGen.Triplet
  VOA.IntegralLattice HeisenbergN VOA.Moonshine MvPolynomial VOA.SparseRational

def signSubmodule (m : ℕ) (hm : 1 ≤ m) :
    WeakModule.Submodule' (resN m hm (adjointModule (V2m m hm))).toWeakModule where
  carrier := LinearMap.ker ((thetaLat (latP m)).toLinearMap + LinearMap.id)
  act_mem := by
    intro u n x hx
    change thetaLat (latP m) x + x = 0 at hx
    change thetaLat (latP m) ((V2m m hm).smul u n x) + (V2m m hm).smul u n x = 0
    rw [theta_smul, (mem_VP_iff m hm _).mp u.2, eq_neg_of_add_eq_zero_left hx]
    simp [PreVertexAlgebra.smul_def]

def signModule (m : ℕ) (hm : 1 ≤ m) :
    OrdVModule (V2mPlus m hm) (signSubmodule m hm).carrier :=
  (resN m hm (adjointModule (V2m m hm))).submodule (signSubmodule m hm)

theorem sign_mem (m : ℕ) (hm : 1 ≤ m) (x : LatModuleGen (latP m)) :
    x ∈ (signSubmodule m hm).carrier ↔ thetaLat (latP m) x = -x := by
  change thetaLat (latP m) x + x = 0 ↔ _
  exact add_eq_zero_iff_eq_neg

theorem sign_weight_zero (m : ℕ) (hm : 1 ≤ m) : (signModule m hm).weight 0 = ⊥ := by
  apply bot_unique
  intro x hx
  change (x : LatModuleGen (latP m)) ∈ adjWeight (V2m m hm) 0 at hx
  rw [show (0 : ℂ) = ((0 : ℤ) : ℂ) by norm_num, adjWeight_cast,
    (V2m m hm).vacuum_grade] at hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  have ht := (sign_mem m hm x).mp x.2
  have hfix : thetaLat (latP m) x = x := by
    rw [← hc, map_smul]
    exact congrArg (c • ·) (thetaLat_vacuum (latP m))
  have hz : (x : LatModuleGen (latP m)) = 0 := by
    have : (2 : ℂ) • (x : LatModuleGen (latP m)) = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr (hfix.symm.trans ht)
    exact (smul_eq_zero.mp this).resolve_left (by norm_num)
  exact Subtype.ext hz

theorem signModule_isLowestWeight (m : ℕ) (hm : 1 ≤ m) :
    IsLowestWeight (signModule m hm) 1 := by
  intro a ha
  have ha' : (adjointModule (V2m m hm)).weight a ≠ ⊥ := by
    intro hz; apply ha
    change ((adjointModule (V2m m hm)).weight a).comap (signSubmodule m hm).carrier.subtype = ⊥
    rw [hz, Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.mpr (signSubmodule m hm).carrier.subtype_injective
  obtain ⟨n, hn⟩ := isLowestWeight_adjoint (V2m m hm) a ha'
  simp only [zero_add] at hn
  have hn0 : n ≠ 0 := by
    intro hz; subst n; simp only [Nat.cast_zero] at hn; subst a
    exact ha (sign_weight_zero m hm)
  refine ⟨n-1, ?_⟩
  rw [hn, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  ring

def signVector (m : ℕ) (hm : 1 ≤ m) : (signSubmodule m hm).carrier :=
  ⟨bosonState (latP m) (a0 m), by
    rw [sign_mem, bosonState, thetaLat_latStateGen, sigmaN_X, neg_zero]
    simp only [latStateGen, TensorProduct.neg_tmul]⟩

theorem signVector_ne_zero (m : ℕ) (hm : 1 ≤ m) : signVector m hm ≠ 0 := by
  intro hz
  have he := congrArg (fun x : (signSubmodule m hm).carrier =>
    coordEα (latP m) 0 (x : LatModuleGen (latP m))) hz
  change coordEα (latP m) 0 (bosonState (latP m) (a0 m)) = 0 at he
  rw [bosonState, latStateGen, coordEα_apply, if_pos rfl] at he
  exact (X_ne_zero (0, a0 m)) he

theorem signVector_mem (m : ℕ) (hm : 1 ≤ m) :
    signVector m hm ∈ (signModule m hm).weight 1 := by
  change bosonState (latP m) (a0 m) ∈ adjWeight (V2m m hm) 1
  rw [show (1 : ℂ) = ((1 : ℤ) : ℂ) by norm_num, adjWeight_cast, bosonState_eq_evR]
  exact h_mem_grading m hm

theorem signVector_W (m : ℕ) (hm : 1 ≤ m) :
    oMod (signModule m hm) (WP m hm) (signVector m hm) = (12 : ℂ) • signVector m hm := by
  apply Subtype.ext
  rw [oMod_homogeneous _ (WP_mem_grading m hm)]
  change (V2m m hm).smul (Wlat m) 3 (bosonState (latP m) (a0 m)) = _
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, W_smul_H]
  have hc : normR (polyAct WR (-4) 1 [(1, [0])]) = [(12, [0])] := by decide +kernel
  norm_num only [Nat.cast_ofNat, neg_sub] at *
  rw [hc]
  change _ = (12 : ℂ) • bosonState (latP m) (a0 m)
  rw [bosonState_eq_evR]
  rw [← latStateGen_csmul]
  congr 1
  simp [evalRaw, evalWord, MvPolynomial.smul_eq_C_mul]

/-- Positive boson modes annihilate every pure exponential. -/
theorem boson_positive_charge (m : ℕ) (hm : 1 ≤ m) (a : (latP m).carrier)
    (n : ℤ) (hn : 0 < n) :
    (V2m m hm).smul (bosonState (latP m) (a0 m)) n (latChargeGen (latP m) a) = 0 := by
  rw [V2m, latChargeGen, smul_bosonState_latStateGen, oscN_vacuum _ _ _ _ hn.le,
    if_neg (ne_of_gt hn)]
  simp [latStateGen]

theorem charge_positive_boson (m : ℕ) (hm : 1 ≤ m) (a : (latP m).carrier)
    (n : ℤ) (hn : 0 < n) :
    (V2m m hm).smul (latChargeGen (latP m) a) n (bosonState (latP m) (a0 m)) = 0 := by
  rw [VertexOperatorAlgebra.skew_mode]
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  have he : (V2m m hm).Y (bosonState (latP m) (a0 m)) (-n-1-j)
      (latChargeGen (latP m) a) = 0 := by
    rw [show -n-1-j = -(n+j)-1 by ring]
    exact boson_positive_charge m hm a (n+j) (by omega)
  rw [he, map_zero, smul_zero, smul_zero]

theorem signVector_E (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    oMod (signModule m hm) (EP m hm) (signVector m hm) = 0 := by
  apply Subtype.ext
  rw [oMod_homogeneous _ (EP_mem_grading m hm)]
  change (V2m m hm).smul ((EP m hm : VP m hm) : LatModuleGen (latP m))
    ((m : ℤ)-1) (bosonState (latP m) (a0 m)) = 0
  rw [EP_coe, PreVertexAlgebra.smul_add_left,
    charge_positive_boson m hm _ _ (by omega), charge_positive_boson m hm _ _ (by omega), zero_add]

theorem sign_character_exists (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm (.inr 1) χ := by
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  obtain ⟨χ, hχ⟩ := character_of_plus_top_vector m hm hm2 (signModule m hm)
    (signModule_isLowestWeight m hm) (signVector m hm) (signVector_mem m hm)
    (signVector_ne_zero m hm) ![1,12,0] (by
      intro i; fin_cases i
      · change oMod (signModule m hm) (V2mPlus m hm).conformalVector _ = _
        rw [oMod_conformalVector]; exact (signModule m hm).L0_weight _ _ (signVector_mem m hm)
      · exact signVector_W m hm
      · simpa using signVector_E m hm hm2)
  exact ⟨χ, hχ 0, hχ 1, hχ 2⟩

end VOA.Classification.COne.PlusCharacterTable
