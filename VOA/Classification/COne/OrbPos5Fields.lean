import VOA.Classification.COne.OrbPos5Delta

/-!
# Fractional Li fields on all shifted lattice states

This constructs a linear field map on the entire actual lattice carrier.
Its definition is a finite polynomial substitution followed by the existing
ordinary lattice-module vertex operators. It is not yet a `TwistedModule`:
the twisted product/Jacobi identity still has to be established.
-/

namespace VOA.Classification.COne.OrbPos5
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 LatMod
open scoped TensorProduct

noncomputable abbrev Modes := ℤ → Module.End ℂ Space

/-- Insert one coefficient `p w^d` of Δ in a fixed lattice charge sector. -/
noncomputable def coefficientField (n : ℕ) (a j β : ℤ) (d : ℕ) : Osc →ₗ[ℂ] Modes where
  toFun p ℓ := if (ℓ - a * β) % (n : ℤ) = 0 then
    mode ((latticeModule 1 le_rfl j).YM (latStateGen (latP 1) p β))
      ((ℓ - a * β) / n - d)
    else 0
  map_add' p q := by
    funext ℓ
    simp only [Pi.add_apply, latStateGen_add_boson, map_add, mode_add]
    split_ifs <;> simp only [add_zero]
  map_smul' c p := by
    funext ℓ
    simp only [Pi.smul_apply, latStateGen_smul_boson, map_smul, mode_smul,
      RingHom.id_apply]
    split_ifs <;> simp only [smul_zero]

/-- The full field on a fixed charge sector; the sum over Δ-coefficients is finite. -/
noncomputable def sectorField (n : ℕ) (a j β : ℤ) : Osc →ₗ[ℂ] Modes :=
  (Finsupp.lsum ℂ (coefficientField n a j β)).comp (deltaCoeffs ((a : ℂ) / (2*n)))

/-- The candidate twisted vertex operator map on every lattice state. -/
noncomputable def shiftedY (n : ℕ) (a j : ℤ) : Space →ₗ[ℂ] Modes :=
  TensorProduct.lift (Finsupp.lsum ℂ fun β : ℤ =>
    LinearMap.toSpanSingleton ℂ (Osc →ₗ[ℂ] Modes) (sectorField n a j β)).flip

theorem shiftedY_latState (n : ℕ) (a j β : ℤ) (p : Osc) :
    shiftedY n a j (latStateGen (latP 1) p β) = sectorField n a j β p := by
  rw [latStateGen, shiftedY, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (fun γ : ℤ =>
    LinearMap.toSpanSingleton ℂ (Osc →ₗ[ℂ] Modes) (sectorField n a j γ)))
      (eGen (latP 1) β) p = _
  exact congrArg (fun f : Osc →ₗ[ℂ] Modes => f p)
    ((Finsupp.lsum_single ℂ (fun γ : ℤ =>
      LinearMap.toSpanSingleton ℂ (Osc →ₗ[ℂ] Modes) (sectorField n a j γ)) β (1 : ℂ)).trans
        (by simp only [LinearMap.toSpanSingleton_apply, one_smul]))

/-- This recovers the previous charged generators from an all-state linear map. -/
theorem shiftedY_charge (n : ℕ) (a j β ℓ : ℤ) :
    shiftedY n a j (latChargeGen (latP 1) β) ℓ = fractionalChargeMode n a j β ℓ := by
  rw [latChargeGen, shiftedY_latState]
  change ((Finsupp.lsum ℂ (coefficientField n a j β))
    (deltaCoeffs ((a : ℂ) / (2*n)) 1)) ℓ = _
  rw [deltaCoeffs_one, Finsupp.lsum_single]
  simp only [coefficientField, LinearMap.coe_mk, AddHom.coe_mk, Nat.cast_zero, sub_zero]
  rfl

/-- Explicit `E⁻E⁺ e^β z^β(0)` formula on the shifted carrier. The index `ℓ/n`
encodes the extra factor `z^(-aβ/n)`; the cocycle is the one in the existing
ordinary coset representation. -/
theorem shiftedY_charge_latState (n : ℕ) (a j β k ℓ : ℤ) (p : Osc)
    (h : (ℓ - a * β) % (n : ℤ) = 0) :
    shiftedY n a j (latChargeGen (latP 1) β) ℓ (latStateGen (latP 1) p k) =
      (latCob (latP 1) (glueLat 1 j) (glueIota 1 j) β *
        latticeCocycle (glueLat 1 j) (glueIota 1 j β)
          (glueIota 1 j k + glueDelta 1 j)) •
      latStateGen (latP 1)
        (EEVec (latP 1) β (-((ℓ-a*β)/(n : ℤ))-1-2*β*k-j*β) p) (β+k) := by
  rw [shiftedY_charge, fractionalChargeMode, if_pos h, mode_apply,
    latticeModule_latChargeGen]
  norm_num

theorem sectorField_support (n : ℕ) (a j β ℓ : ℤ) (p : Osc)
    (h : (ℓ - a * β) % (n : ℤ) ≠ 0) : sectorField n a j β p ℓ = 0 := by
  classical
  simp only [sectorField, LinearMap.comp_apply, Finsupp.lsum_apply, Finsupp.sum,
    Finset.sum_apply, coefficientField, LinearMap.coe_mk, AddHom.coe_mk, if_neg h,
    Finset.sum_const_zero]

/-- Lower truncation is a linear condition on mode families, for each test vector. -/
def truncatedAt (x : Space) : Submodule ℂ Modes where
  carrier := {F | ∃ K : ℤ, ∀ ℓ : ℤ, K ≤ ℓ → F ℓ x = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro F G ⟨KF, hF⟩ ⟨KG, hG⟩
    refine ⟨max KF KG, fun ℓ hℓ => ?_⟩
    change F ℓ x + G ℓ x = 0
    rw [hF ℓ (le_trans (le_max_left _ _) hℓ),
      hG ℓ (le_trans (le_max_right _ _) hℓ), add_zero]
  smul_mem' := by
    rintro c F ⟨K, hK⟩
    refine ⟨K, fun ℓ hℓ => ?_⟩
    change c • F ℓ x = 0
    rw [hK ℓ hℓ, smul_zero]

theorem coefficientField_truncation {n : ℕ} (hn : 0 < n)
    (a j β : ℤ) (d : ℕ) (p : Osc) (x : Space) :
    coefficientField n a j β d p ∈ truncatedAt x := by
  obtain ⟨K, hK⟩ := (latticeModule 1 le_rfl j).truncation
    (latStateGen (latP 1) p β) x
  refine ⟨(n : ℤ) * (K + d) + a * β, fun ℓ hℓ => ?_⟩
  change (if (ℓ-a*β) % (n : ℤ) = 0 then _ else (0 : Module.End ℂ Space)) x = 0
  split_ifs
  · apply hK
    have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
    have hdiv : K + d ≤ (ℓ-a*β) / (n : ℤ) := by
      rw [Int.le_ediv_iff_mul_le hnZ]
      nlinarith
    omega
  · rfl

theorem sectorField_truncation {n : ℕ} (hn : 0 < n)
    (a j β : ℤ) (p : Osc) (x : Space) : sectorField n a j β p ∈ truncatedAt x := by
  classical
  rw [sectorField, LinearMap.comp_apply, Finsupp.lsum_apply, Finsupp.sum]
  exact Submodule.sum_mem _ fun d _ => coefficientField_truncation hn a j β d _ x

/-- Every field in the constructed all-state map is lower truncated. -/
theorem shiftedY_truncation {n : ℕ} (hn : 0 < n) (a j : ℤ) (u x : Space) :
    ∃ K : ℤ, ∀ ℓ : ℤ, K ≤ ℓ → shiftedY n a j u ℓ x = 0 := by
  have ht : (truncatedAt x).comap (shiftedY n a j) = ⊤ := by
    rw [eq_top_iff, ← latStateGen_span (latP 1)]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨p, β⟩, rfl⟩
    change shiftedY n a j (latStateGen (latP 1) p β) ∈ truncatedAt x
    rw [shiftedY_latState]
    exact sectorField_truncation hn a j β p x
  have hu : u ∈ (truncatedAt x).comap (shiftedY n a j) := by rw [ht]; trivial
  exact hu

/-- The vacuum axiom is verified for the constructed full field map. -/
theorem shiftedY_vacuum {n : ℕ} (hn : 0 < n) (a j : ℤ) (ℓ : ℤ) :
    shiftedY n a j (V2m 1 le_rfl).vacuum ℓ = if ℓ = -(n : ℤ) then 1 else 0 := by
  change shiftedY n a j (latChargeGen (latP 1) 0) ℓ = _
  rw [shiftedY_charge]
  unfold fractionalChargeMode
  change (if (ℓ - a * (0 : ℤ)) % (n : ℤ) = 0 then
    mode ((latticeModule 1 le_rfl j).YM (V2m 1 le_rfl).vacuum)
      ((ℓ - a * (0 : ℤ)) / n) else 0) = _
  simp only [mul_zero, sub_zero]
  rw [(latticeModule 1 le_rfl j).vacuum_YM]
  simp only [mode_one]
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  by_cases h : ℓ % (n : ℤ) = 0
  · rw [if_pos h]
    have he : ℓ / (n : ℤ) = -1 ↔ ℓ = -(n : ℤ) := by
      have hd := Int.emod_add_mul_ediv ℓ (n : ℤ)
      rw [h, zero_add] at hd
      constructor
      · intro hq
        rw [hq, mul_neg_one] at hd
        exact hd.symm
      · intro hq
        rw [hq, Int.neg_ediv_of_dvd (dvd_refl _), Int.ediv_self (ne_of_gt hnZ)]
    simp only [he]
  · rw [if_neg h, if_neg (by intro he; apply h; rw [he]; simp)]

/-- Irreducibility of the constructed operator family, independently of Jacobi. -/
theorem shiftedY_irreducible {n : ℕ} (hn : 0 < n) (a j : ℤ)
    (S : Submodule ℂ Space)
    (hS : ∀ u ℓ x, x ∈ S → shiftedY n a j u ℓ x ∈ S) : S = ⊥ ∨ S = ⊤ := by
  apply fractionalChargeMode_irreducible hn a j S
  intro β ℓ x hx
  rw [← shiftedY_charge]
  exact hS _ _ _ hx

/-- At zero shift and denominator one the entire constructed field map,
including oscillator descendants, recovers the ordinary module. -/
theorem shiftedY_zero_one (j : ℤ) :
    shiftedY 1 0 j = (latticeModule 1 le_rfl j).toTwisted.YM := by
  apply LinearMap.ext_on_range (latStateGen_span (latP 1))
  rintro ⟨p, β⟩
  change ℤ at β
  rw [shiftedY_latState]
  rw [sectorField, LinearMap.comp_apply]
  simp only [Int.cast_zero, zero_div]
  rw [deltaCoeffs_zero, Finsupp.lsum_single]
  funext ℓ
  change (if (ℓ - 0 * (β : ℤ)) % (1 : ℤ) = 0 then
    mode ((latticeModule 1 le_rfl j).YM (latStateGen (latP 1) p β))
      ((ℓ-0*β)/(1 : ℤ)-(0 : ℕ)) else 0) = _
  simp only [zero_mul, sub_zero, Int.emod_one, ite_true, Int.ediv_one, Nat.cast_zero]
  rfl

end VOA.Classification.COne.OrbPos5
