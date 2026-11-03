import VOA.DeligneAudit.D4LevelReductionRaisingChoices
import Mathlib.Data.List.Perm.Subperm

/-! Elementary-complete cancellation for the central alphabet after raising conversion. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open MvPolynomial
open VOA.DeligneAudit.SL4T
open VOA.DeligneAudit.D4Levi

/-- Cancelling a selected subalphabet leaves an elementary polynomial of the residual size. -/
theorem selectedAlphabet_complete_cancellation {A : Type*} [CommRing A] [Algebra ℂ A]
    (vs : List A) (j n : ℕ) (f : Fin j → A)
    (hf : List.Subperm (List.ofFn f) vs) (hn : vs.length < j + n) :
    ∑ i ∈ Finset.range (n + 1),
      (ksEPoly vs).coeff i * aeval f (hsymm (Fin j) ℂ (n - i)) = 0 := by
  obtain ⟨ls, hperm, hsub⟩ := List.subperm_iff.mp hf
  obtain ⟨ws, hws⟩ := hsub.exists_perm_append
  have hp := hperm.symm.trans hws
  have hlen : ws.length < n := by
    have he := hp.length_eq
    simp only [List.length_append, List.length_ofFn] at he
    omega
  have he : ksEPoly vs = ksEPoly (List.ofFn f) * ksEPoly ws := by
    calc
      ksEPoly vs = ksEPoly (List.ofFn f ++ ws) := (hp.map _).prod_eq
      _ = _ := by simp [ksEPoly]
  have hs : (ksEPoly vs : PowerSeries A) * ksHSeries (List.ofFn f) =
      (ksEPoly ws : PowerSeries A) := by
    rw [he, Polynomial.coe_mul]
    calc
      _ = (ksHSeries (List.ofFn f) * (ksEPoly (List.ofFn f) : PowerSeries A)) *
          (ksEPoly ws : PowerSeries A) := by ring
      _ = _ := by rw [ksHSeries_mul_EPoly, one_mul]
  have hc := congrArg (PowerSeries.coeff n) hs
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simpa only [Polynomial.coeff_coe, ksHSeries_coeff_aeval,
    ksEPoly_coeff_eq_zero ws n hlen] using hc

/-- The signed elementary product commutes with coefficient specialization. -/
theorem centralElementaryProduct_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (vs : List A) :
    (ksEPoly vs).map f = ksEPoly (vs.map f) := by
  change (Polynomial.mapRingHom f) _ = _
  simp [ksEPoly, map_list_prod, List.map_map, Function.comp_def]

/-- The coefficient alphabet of the core, represented by actual bottom mode polynomials. -/
def coreBottomModePolynomial (a c : ℕ) :
    BiSymPoly →ₐ[ℂ] MvPolynomial (BottomModeSlot a c) ℂ :=
  (xyzPowerSumAlgebra (bottomModeShape a c)).val.comp
    ((bottomElementaryModes a c).comp leftComplementAlphabet)

/-- A core complete function becomes a coefficient of the central elementary product. -/
theorem coreBottomModePolynomial_complete (a c n : ℕ) :
    coreBottomModePolynomial a c (alphabetIn false (complete n)) =
      (ksEPoly (List.ofFn fun i : Fin c =>
        (X (Sum.inl i) : MvPolynomial (BottomModeSlot a c) ℂ))).coeff n := by
  change (bottomElementaryModes a c
    (leftComplementAlphabet (alphabetIn false (complete n))) :
      MvPolynomial (BottomModeSlot a c) ℂ) = _
  rw [leftComplementAlphabet_left, complementAlphabet_complete]
  simp only [map_mul, map_pow, map_neg, map_one]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg,
    Subalgebra.coe_one]
  rw [bottomElementaryModes_central, elementarySpecialization_elementary]
  have he := congrArg (fun P => P.coeff n)
    (centralElementaryProduct_map
      (rename (Sum.inl : Fin c → BottomModeSlot a c)).toRingHom
      (List.ofFn fun i : Fin c => (X i : MvPolynomial (Fin c) ℂ)))
  have hmap : (List.ofFn fun i : Fin c => (X i : MvPolynomial (Fin c) ℂ)).map
      (rename (Sum.inl : Fin c → BottomModeSlot a c)).toRingHom =
        List.ofFn (fun i : Fin c => (X (Sum.inl i) :
          MvPolynomial (BottomModeSlot a c) ℂ)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact rename_X _ _
  dsimp only at he
  rw [hmap, Polynomial.coeff_map, elementaryProduct_coeff] at he
  simpa only [map_mul, map_pow, map_neg, map_one] using he

/-- A polynomial representative of the converted complete function before the core quotient. -/
def coreRaisingCompleteRepresentative (j n : ℕ) : MvPolynomial (Fin j) BiSymPoly :=
  ∑ i ∈ Finset.range (n + 1),
    MvPolynomial.C (alphabetIn false (complete i)) * hsymm (Fin j) BiSymPoly (n - i)

/-- Specialize the raising variables to their selected central slots. -/
def coreRaisingSubstitution (a c j : ℕ) (f : Fin j → BottomModeSlot a c) :
    MvPolynomial (Fin j) BiSymPoly →ₐ[ℂ] MvPolynomial (BottomModeSlot a c) ℂ :=
  aevalTower (coreBottomModePolynomial a c) (fun i => X (f i))

/-- Coefficient changes do not change the complete symmetric mode polynomial. -/
theorem coreRaisingSubstitution_hsymm (a c j n : ℕ) (f : Fin j → BottomModeSlot a c) :
    coreRaisingSubstitution a c j f (hsymm (Fin j) BiSymPoly n) =
      aeval (fun i => X (f i)) (hsymm (Fin j) ℂ n) := by
  rw [← map_hsymm (σ := Fin j) (R := ℂ) (S := BiSymPoly) n
    (algebraMap ℂ BiSymPoly), rz_hsymm_eq_sum_vectors]
  simp [coreRaisingSubstitution, map_sum, map_prod, map_pow]

/-- Every converted relation is an exact polynomial identity at every slot assignment. -/
theorem coreRaisingSubstitution_complete_zero (a c j n : ℕ)
    (q : (Fin j → BottomModeSlot a c) × (BottomModeSlot a c → Fin 6))
    (hq : q ∈ centralRaisingChoices (bottomModeShape a c) j) (hn : c < j + n) :
    coreRaisingSubstitution a c j q.1 (coreRaisingCompleteRepresentative j n) = 0 := by
  obtain ⟨hinj, hcol⟩ := centralRaisingChoices_injective j _ q hq
  have hsub : List.Subperm (List.ofFn q.1) (List.ofFn (Sum.inl : Fin c → BottomModeSlot a c)) := by
    apply List.subperm_of_subset (List.nodup_ofFn.mpr hinj)
    intro t ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    have hc := hcol i
    cases he : q.1 i with
    | inl k => exact List.mem_ofFn.mpr ⟨k, rfl⟩
    | inr k =>
        rw [he] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 5) hc)
  have hm := hsub.map (f := fun t => (X t : MvPolynomial (BottomModeSlot a c) ℂ))
    MvPolynomial.X_injective
  simp only [List.map_ofFn] at hm
  unfold coreRaisingCompleteRepresentative
  simp only [map_sum, map_mul, coreRaisingSubstitution_hsymm]
  simp only [coreRaisingSubstitution, aevalTower_C, coreBottomModePolynomial_complete]
  exact selectedAlphabet_complete_cancellation _ j n _ hm (by simpa using hn)

/-- The cancellation kills arbitrary polynomial multiples, without a key-prefix assumption. -/
theorem coreRaisingSubstitution_complete_mul_zero (a c j n : ℕ)
    (q : (Fin j → BottomModeSlot a c) × (BottomModeSlot a c → Fin 6))
    (hq : q ∈ centralRaisingChoices (bottomModeShape a c) j) (hn : c < j + n)
    (P : MvPolynomial (Fin j) BiSymPoly) :
    coreRaisingSubstitution a c j q.1 (P * coreRaisingCompleteRepresentative j n) = 0 := by
  rw [map_mul, coreRaisingSubstitution_complete_zero a c j n q hq hn, mul_zero]

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.selectedAlphabet_complete_cancellation
#print axioms VOA.DeligneAudit.D4LevelReduction.centralElementaryProduct_map
#print axioms VOA.DeligneAudit.D4LevelReduction.coreBottomModePolynomial_complete
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingSubstitution_hsymm
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingSubstitution_complete_zero
#print axioms VOA.DeligneAudit.D4LevelReduction.coreRaisingSubstitution_complete_mul_zero
