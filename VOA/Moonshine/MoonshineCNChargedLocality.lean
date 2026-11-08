import VOA.Moonshine.MoonshineCNNegativeCollapse

/-!
# Mutual locality of the hyperbolic-lattice charged fields

The finite binomial-difference argument covers every integral pairing. The
exponent for a negative pairing is its absolute value; for a nonnegative
pairing the fields commute coefficientwise. Cocycle factors cancel the sign.
Proofs adapt `LatticeGenSameSignLocal` and `LatticeGenOppLocal` to complex frames.
-/

set_option maxHeartbeats 1200000
set_option linter.style.longLine false

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct
open Module (End)
open IntegralLattice HeisenbergN LatGen
open VOA.LatExp (kZ wt shear3g mulBySubPow_binom)

/-- Precisely the scalar identities used to cancel the bosonic reordering sign. -/
structure ChargeCommutationFactors (L : IntegralLattice) where
  value : L.carrier → L.carrier → ℂ
  add_right : ∀ α β γ, value α (β + γ) = value α β * value α γ
  swap : ∀ α β, value α β = (-1 : ℂ) ^ L.form α β * value β α

noncomputable def canonicalChargeCommutationFactors (L : IntegralLattice) (hEven : L.Even) :
    ChargeCommutationFactors L where
  value := latticeCocycle L
  add_right := latticeCocycle_add_right L
  swap := by
    intro α β
    rw [← latticeCocycle_comm L hEven α β, mul_assoc, latticeCocycle_sq, mul_one]

noncomputable def lorentzianChargeCommutationFactors : ChargeCommutationFactors lorentzianLattice where
  value := standardLorentzianCocycle
  add_right := by
    intro α β γ
    simp only [standardLorentzianCocycle, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    congr 1
    change α 1 * (β 0 + γ 0) = α 1 * β 0 + α 1 * γ 0
    ring
  swap := by
    intro α β
    have hsq : standardLorentzianCocycle β α * standardLorentzianCocycle β α = 1 := by
      rw [standardLorentzianCocycle, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        ← two_mul, zpow_mul]
      norm_num
    rw [← standardLorentzianCocycle_commutator α β, mul_assoc, hsq, mul_one]

variable {L : IntegralLattice} (F : ComplexLatticeFrame L) (C : ChargeCommutationFactors L)

theorem local_of_bracket_on_state (L : IntegralLattice) {F G : FormalDist (End ℂ (LatModuleGen L))}
    (h : ∀ (j k : ℤ) (γ : L.carrier) (p : FockN (rank L)),
      bracketDist F G j k (latStateGen L p γ) = 0) : Local F G := by
  refine local_of_bracketDist_eq_zero ?_
  refine FormalDist₂.ext fun j k => ?_
  refine LinearMap.ext fun y => ?_
  change bracketDist F G j k y = 0
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add y1 y2 h1 h2 => rw [map_add, h1, h2, add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, h1, h2, add_zero]
      | single γ a =>
          rw [(Finsupp.smul_single_one γ a).symm]
          erw [TensorProduct.tmul_smul, map_smul,
            show (Finsupp.single γ (1 : ℂ) : L.carrier →₀ ℂ) = eGen L γ from rfl]
          rw [show p ⊗ₜ[ℂ] eGen L γ = latStateGen L p γ from rfl, h, smul_zero]


theorem chargedField_nonnegative_pairing_bracket_on_state  (α β : L.carrier)
    (hsign : 0 ≤ L.form α β) (j k : ℤ) (γ : L.carrier) (p : FockN (rank L)) :
    bracketDist (chargedField F C.value α) (chargedField F C.value β) j k (latStateGen L p γ) = 0 := by
  obtain ⟨P, hP⟩ : ∃ P : ℕ, (P : ℤ) = L.form α β := ⟨(L.form α β).toNat, by omega⟩
  simp only [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, chargedField_tmul, map_smul]
  
  have hEE : dressingField F α (j - L.form α (β + γ)) (dressingField F β (k - L.form β γ) p)
      = (-1 : ℂ) ^ P • dressingField F β (k - L.form β (α + γ)) (dressingField F α (j - L.form α γ) p) := by
    rw [show j - L.form α (β + γ) = (j - L.form α γ) - P from by
          rw [map_add, hP]; ring,
      dressingComposition_positive_swap F α β P hP (j - L.form α γ) (k - L.form β γ) p,
      show k - L.form β γ - P = k - L.form β (α + γ) from by
        rw [map_add, hP, form_symm L β α]; ring]
  have hpp : (-1 : ℂ) ^ P * (-1 : ℂ) ^ P = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hsw : C.value α β = (-1 : ℂ) ^ P * C.value β α := by
    rw [C.swap α β, ← hP, zpow_natCast]
  rw [hEE, latStateGen_smul_boson, show α + (β + γ) = β + (α + γ) from by abel,
    C.add_right α β γ, C.add_right β α γ, hsw]
  simp only [smul_smul]
  rw [← sub_smul,
    show C.value β γ * ((-1 : ℂ) ^ P * C.value β α * C.value α γ
            * (-1 : ℂ) ^ P)
        - C.value α γ * (C.value β α * C.value β γ) = 0 from by
      linear_combination
        (C.value β γ * C.value β α * C.value α γ) * hpp,
    zero_smul]


theorem chargedField_nonnegative_pairing_local  (α β : L.carrier)
    (hsign : 0 ≤ L.form α β) : Local (chargedField F C.value α) (chargedField F C.value β) :=
  local_of_bracket_on_state L
    (fun j k γ p => chargedField_nonnegative_pairing_bracket_on_state F C α β hsign j k γ p)


theorem latStateGen_sub_boson (L : IntegralLattice) (p q : FockN (rank L)) (α : L.carrier) :
    latStateGen L (p - q) α = latStateGen L p α - latStateGen L q α := by
  simp only [latStateGen, TensorProduct.sub_tmul]


theorem chargedField_bracket_on_state (α β : L.carrier) (j k : ℤ) (γ : L.carrier) (p : FockN (rank L)) :
    bracketDist (chargedField F C.value α) (chargedField F C.value β) j k (latStateGen L p γ)
      = ((C.value β γ * C.value α (β + γ)) •
            dressingField F α ((j - L.form α γ) - L.form α β) (dressingField F β (k - L.form β γ) p)
          - (C.value α γ * C.value β (α + γ)) •
            dressingField F β ((k - L.form β γ) - L.form α β) (dressingField F α (j - L.form α γ) p))
        ⊗ₜ[ℂ] eGen L (α + β + γ) := by
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    chargedField_tmul, map_smul, chargedField_tmul, chargedField_tmul, map_smul, chargedField_tmul, smul_smul, smul_smul,
    show α + (β + γ) = α + β + γ from by abel, show β + (α + γ) = α + β + γ from by abel,
    show j - L.form α (β + γ) = (j - L.form α γ) - L.form α β from by rw [map_add]; ring,
    show k - L.form β (α + γ) = (k - L.form β γ) - L.form α β from by
      rw [map_add, form_symm L β α]; ring,
    latStateGen, latStateGen, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
    ← TensorProduct.sub_tmul]


theorem chargedField_negative_pairing_difference_on_state 
    (α β : L.carrier) (hsign : L.form α β ≤ -1) (j k : ℤ) (γ : L.carrier) (p : FockN (rank L)) :
    mulBySubPow ((-(L.form α β)).toNat) (bracketDist (chargedField F C.value α) (chargedField F C.value β)) j k
        (latStateGen L p γ) = 0 := by
  set Pn : ℕ := (-(L.form α β)).toNat with hPndef
  have hPnZ : (Pn : ℤ) = -(L.form α β) := by
    rw [hPndef, Int.toNat_of_nonneg (by omega)]
  have hPnC : ((L.form α β : ℤ) : ℂ) = -(Pn : ℂ) := by
    rw [show (L.form α β : ℤ) = -(Pn : ℤ) from by omega]; push_cast; ring
  
  have hcoc : (C.value β γ * C.value α (β + γ))
      - (C.value α γ * C.value β (α + γ)) * (-1 : ℂ) ^ Pn = 0 := by
    rw [C.add_right α β γ, C.add_right β α γ]
    have hsw : C.value α β = (-1 : ℂ) ^ Pn * C.value β α := by
      rw [C.swap α β, show L.form α β = -(Pn : ℤ) from by omega,
        zpow_neg, zpow_natCast, inv_eq_of_mul_eq_one_right
          (by rw [← pow_add, ← two_mul, pow_mul]; norm_num)]
    rw [hsw]; ring
  
  rw [show mulBySubPow Pn (bracketDist (chargedField F C.value α) (chargedField F C.value β)) j k
        = ∑ i ∈ Finset.range (Pn + 1),
            wt Pn i • bracketDist (chargedField F C.value α) (chargedField F C.value β) (j - ((Pn : ℤ) - i)) (k - i) from
      mulBySubPow_binom Pn (bracketDist (chargedField F C.value α) (chargedField F C.value β)) j k]
  rw [LinearMap.coe_sum, Finset.sum_apply]
  simp only [LinearMap.smul_apply]
  
  have hbody : ∀ i ∈ Finset.range (Pn + 1),
      wt Pn i • bracketDist (chargedField F C.value α) (chargedField F C.value β) (j - ((Pn : ℤ) - i)) (k - i)
          (latStateGen L p γ)
        = wt Pn i •
            (((C.value β γ * C.value α (β + γ)) •
                dressingField F α ((j - L.form α γ) + (i : ℤ))
                  (dressingField F β ((k - L.form β γ) - (i : ℤ)) p)
              - (C.value α γ * C.value β (α + γ)) •
                dressingField F β (((k - L.form β γ) + (Pn : ℤ)) - (i : ℤ))
                  (dressingField F α (((j - L.form α γ) - (Pn : ℤ)) + (i : ℤ)) p))
             ⊗ₜ[ℂ] eGen L (α + β + γ)) := by
    intro i _
    rw [chargedField_bracket_on_state F C α β (j - ((Pn : ℤ) - i)) (k - i) γ p,
      show (j - ((Pn : ℤ) - i)) - L.form α γ = ((j - L.form α γ) - (Pn : ℤ)) + (i : ℤ) from by omega,
      show (k - i) - L.form β γ = (k - L.form β γ) - (i : ℤ) from by omega,
      show ((k - L.form β γ) - (i : ℤ)) - L.form α β = ((k - L.form β γ) + (Pn : ℤ)) - (i : ℤ) from by
        omega,
      show (((j - L.form α γ) - (Pn : ℤ)) + (i : ℤ)) - L.form α β
          = (j - L.form α γ) + (i : ℤ) from by omega]
  rw [Finset.sum_congr rfl hbody]
  
  rw [show (∑ i ∈ Finset.range (Pn + 1), wt Pn i •
          (((C.value β γ * C.value α (β + γ)) •
              dressingField F α ((j - L.form α γ) + (i : ℤ)) (dressingField F β ((k - L.form β γ) - (i : ℤ)) p)
            - (C.value α γ * C.value β (α + γ)) •
              dressingField F β (((k - L.form β γ) + (Pn : ℤ)) - (i : ℤ))
                (dressingField F α (((j - L.form α γ) - (Pn : ℤ)) + (i : ℤ)) p))
           ⊗ₜ[ℂ] eGen L (α + β + γ)))
        = (((C.value β γ * C.value α (β + γ)) •
              ∑ i ∈ Finset.range (Pn + 1), wt Pn i •
                dressingField F α ((j - L.form α γ) + (i : ℤ)) (dressingField F β ((k - L.form β γ) - (i : ℤ)) p))
            - ((C.value α γ * C.value β (α + γ)) •
              ∑ i ∈ Finset.range (Pn + 1), wt Pn i •
                dressingField F β (((k - L.form β γ) + (Pn : ℤ)) - (i : ℤ))
                  (dressingField F α (((j - L.form α γ) - (Pn : ℤ)) + (i : ℤ)) p)))
          ⊗ₜ[ℂ] eGen L (α + β + γ) from by
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul', smul_sub,
        smul_comm (wt Pn i) (C.value β γ * C.value α (β + γ)),
        smul_comm (wt Pn i) (C.value α γ * C.value β (α + γ))]]
  
  rw [negativeDressing_right_difference F Pn α β hPnC (j - L.form α γ) (k - L.form β γ) p,
    negativeDressing_reversed_difference F Pn α β hPnC ((j - L.form α γ) - (Pn : ℤ)) ((k - L.form β γ) + (Pn : ℤ)) p,
    show ((j - L.form α γ) - (Pn : ℤ)) + (Pn : ℤ) = j - L.form α γ from by ring,
    show ((k - L.form β γ) + (Pn : ℤ)) - (Pn : ℤ) = k - L.form β γ from by ring]
  
  rw [smul_smul, ← sub_smul, hcoc, zero_smul, TensorProduct.zero_tmul]


theorem chargedField_negative_pairing_difference  (α β : L.carrier)
    (hsign : L.form α β ≤ -1) :
    mulBySubPow ((-(L.form α β)).toNat) (bracketDist (chargedField F C.value α) (chargedField F C.value β)) = 0 := by
  refine FormalDist₂.ext fun j k => ?_
  refine LinearMap.ext fun y => ?_
  change mulBySubPow ((-(L.form α β)).toNat) (bracketDist (chargedField F C.value α) (chargedField F C.value β)) j k y = 0
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add y1 y2 h1 h2 => rw [map_add, h1, h2, add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, h1, h2, add_zero]
      | single γ a =>
          rw [(Finsupp.smul_single_one γ a).symm]
          erw [TensorProduct.tmul_smul, map_smul,
            show (Finsupp.single γ (1 : ℂ) : L.carrier →₀ ℂ) = eGen L γ from rfl]
          rw [show p ⊗ₜ[ℂ] eGen L γ = latStateGen L p γ from rfl,
            chargedField_negative_pairing_difference_on_state F C α β hsign j k γ p, smul_zero]


theorem chargedField_negative_pairing_local  (α β : L.carrier)
    (hsign : L.form α β ≤ -1) : Local (chargedField F C.value α) (chargedField F C.value β) :=
  ⟨(-(L.form α β)).toNat, chargedField_negative_pairing_difference F C α β hsign⟩


theorem chargedField_local  (α β : L.carrier) :
    Local (chargedField F C.value α) (chargedField F C.value β) := by
  by_cases h : 0 ≤ L.form α β
  · exact chargedField_nonnegative_pairing_local F C α β h
  · exact chargedField_negative_pairing_local F C α β (by omega)


/-- Mutual locality on the entire Fock tensor group algebra, with explicit signs. -/
theorem lorentzianChargedField_local (α β : lorentzianLattice.carrier) :
    Local (lorentzianChargedField α) (lorentzianChargedField β) :=
  chargedField_local lorentzianComplexFrame lorentzianChargeCommutationFactors α β

/-- Mutual locality for the cocycle prescribed by `LorentzianVertexTarget`. -/
theorem lorentzianTargetChargedField_local (α β : lorentzianLattice.carrier) :
    Local (lorentzianTargetChargedField α) (lorentzianTargetChargedField β) :=
  chargedField_local lorentzianComplexFrame
    (canonicalChargeCommutationFactors lorentzianLattice lorentzian_even) α β

end VOA.Moonshine.ConwayNorton
