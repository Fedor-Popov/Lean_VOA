import VOA.Classification.COne.OrbPos7Products

/-! # Oscillator-word propagation of the inner-twisted product formula -/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbPos7
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 OrbPos5 OrbPos6 LatMod TwistedReduction
open Moonshine.LatticeTwisted
open scoped TensorProduct

variable {n : ℕ} (hn : 0 < n) (a j : ℤ)

theorem h_charge_nonneg (β ℓ : ℤ) (hℓ : 0 ≤ ℓ) :
    (V2m 1 le_rfl).smul h ℓ (latChargeGen (latP 1) β) =
      if ℓ = 0 then chargeCoord (latP 1) β (a0 1) • latChargeGen (latP 1) β else 0 :=
  smul_hgen_echg_nonneg (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) (a0 1) hℓ β

theorem PF_word_charge (l : List (ℕ × Fin (rank (latP 1)))) (β γ : ℤ) :
    PF hn a j (wordStateN l ⊗ₜ[ℂ] eGen (latP 1) β) (latChargeGen (latP 1) γ) := by
  induction l with
  | nil => exact PF_charges hn a j β γ
  | cons c l ih =>
    set w := wordStateN l ⊗ₜ[ℂ] eGen (latP 1) β
    set v := latChargeGen (latP 1) γ
    set H := shiftedCurrent j ((a : ℂ)/(2*n))
    intro e f ℓ
    set X := rescaledField hn a j e w
    set Y := rescaledField hn a j f v
    have hFu : rescaledField hn a j e (wordStateN (c :: l) ⊗ₜ[ℂ] eGen (latP 1) β) =
        star 0 H (-(c.1 : ℤ)-1) X := by
      rw [word_cons, current_star]
    obtain ⟨N₁, hN₁⟩ := star_eventually_zero (rescaledField_local hn a j e f w v) ((e : ℂ)/n)
    obtain ⟨N₂, hN₂⟩ := star_eventually_zero
      (show Local H.1 Y.1 from by
        rw [show H = rescaledField hn a j 0 h from (resc_current hn a j).symm]
        exact rescaledField_local hn a j 0 f h v) 0
    obtain ⟨N₃, hN₃⟩ := PreVertexAlgebra.smul_eventually_zero
      (V2m 1 le_rfl).toPreVertexAlgebra (residueProjection n a e w) v
    set K : ℕ := (N₁-ℓ).toNat + N₂.toNat + (N₃-ℓ).toNat + 1
    have hYi : ∀ (i : ℕ) (q : ℤ), star ((e : ℂ)/n) X q
        (rescaledField hn a j f ((V2m 1 le_rfl).smul h i v)) =
        rescaledField hn a j (e+f) ((V2m 1 le_rfl).smul (residueProjection n a e w) q
          ((V2m 1 le_rfl).smul h i v)) := by
      intro i q
      rw [h_charge_nonneg γ i (by omega)]
      split_ifs
      · rw [map_smul, star_smul_right (rescaledField_local hn a j _ _ _ _), ih,
          PreVertexAlgebra.smul_smul_right, map_smul]
      · rw [map_zero, star_zero_right, PreVertexAlgebra.smul_zero_right, map_zero]
    rw [hFu, show (e : ℂ)/n = 0 + (e : ℂ)/n from (zero_add _).symm,
      star_iterate_range (fieldSet_local hn a j) (current_mem hn a j)
        (rescaledField_mem hn a j e w) (rescaledField_mem hn a j f v)
        0 ((e : ℂ)/n) (-(c.1 : ℤ)-1) ℓ K (fun i hi =>
          ⟨hN₁ _ (by dsimp [K] at hi; omega), hN₂ _ (by dsimp [K] at hi; omega)⟩)]
    have hterm : ∀ i ∈ Finset.range K,
        ((-1 : ℂ)^i * gBinom (-(c.1 : ℤ)-1) i) •
          (star 0 H (-(c.1 : ℤ)-1-i) (star ((e : ℂ)/n) X (ℓ+i) Y) -
            ((-1 : ℂ)^(-(c.1 : ℤ)-1)) • star ((e : ℂ)/n) X (-(c.1 : ℤ)-1+ℓ-i)
              (star 0 H i Y)) =
        rescaledField hn a j (e+f) (((-1 : ℂ)^i * gBinom (-(c.1 : ℤ)-1) i) •
          ((V2m 1 le_rfl).smul h (-(c.1 : ℤ)-1-i)
            ((V2m 1 le_rfl).smul (residueProjection n a e w) (ℓ+i) v) -
           ((-1 : ℂ)^(-(c.1 : ℤ)-1)) • (V2m 1 le_rfl).smul (residueProjection n a e w)
            (-(c.1 : ℤ)-1+ℓ-i) ((V2m 1 le_rfl).smul h i v))) := by
      intro i _
      rw [ih e f (ℓ+i), current_star, show Y = rescaledField hn a j f v from rfl,
        current_star, hYi, map_smul, map_sub, map_smul]
    rw [Finset.sum_congr rfl hterm, ← map_sum, word_cons, residueProjection_current,
      VertexOperatorAlgebra.mode_iterate]
    congr 1
    symm
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    rw [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    apply hi
    rw [hN₃ _ (by dsimp [K] at hc; omega), PreVertexAlgebra.smul_zero_right,
      h_charge_nonneg γ i (by omega), if_neg (by dsimp [K] at hc; omega),
      PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero, smul_zero]

theorem PF_charge_right (γ : ℤ) (u : Space) : PF hn a j u (latChargeGen (latP 1) γ) :=
  Moonshine.LatticeTwistedGeneral.latState_induction (latP 1)
    (P := fun u => PF hn a j u (latChargeGen (latP 1) γ))
    (PF_zero_left hn a j _) (fun _ _ hu hv => PF_add_left hn a j hu hv)
    (fun c _ hu => PF_smul_left hn a j c hu) (fun l β => PF_word_charge hn a j l β γ) u

theorem PF_word_right (l : List (ℕ × Fin (rank (latP 1)))) (β : ℤ) :
    ∀ u, PF hn a j u (wordStateN l ⊗ₜ[ℂ] eGen (latP 1) β) := by
  induction l with
  | nil => exact PF_charge_right hn a j β
  | cons c l ih =>
    intro u e f ℓ
    set v := wordStateN l ⊗ₜ[ℂ] eGen (latP 1) β
    set H := shiftedCurrent j ((a : ℂ)/(2*n))
    set p : ℤ := -(c.1 : ℤ)-1
    have hFv : rescaledField hn a j f (wordStateN (c :: l) ⊗ₜ[ℂ] eGen (latP 1) β) =
        star 0 H p (rescaledField hn a j f v) := by
      rw [word_cons, current_star]
    obtain ⟨K₁, hK₁⟩ := exists_prod_offset_zero
      (show Local H.1 (rescaledField hn a j e u).1 from by
        rw [show H = rescaledField hn a j 0 h from (resc_current hn a j).symm]
        exact rescaledField_local hn a j 0 e h u) 0
    obtain ⟨K₂, hK₂⟩ := PreVertexAlgebra.smul_eventually_zero
      (V2m 1 le_rfl).toPreVertexAlgebra h (residueProjection n a e u)
    set L : ℕ := K₁ + K₂.toNat
    have hT := star_comm (fieldSet_local hn a j) (current_mem hn a j)
      (rescaledField_mem hn a j e u) (rescaledField_mem hn a j f v)
      0 ((e : ℂ)/n) p ℓ L (fun s hs => by
        have hh := hK₁ s (by dsimp [L] at hs; omega)
        simpa only [zero_add] using hh)
    rw [ih u e f ℓ, current_star] at hT
    have hterm : ∀ s ∈ Finset.range L,
        gBinom p s • star (0+(e : ℂ)/n)
          (star 0 H s (rescaledField hn a j e u)) (p+ℓ-s) (rescaledField hn a j f v) =
        gBinom p s • rescaledField hn a j (e+f) ((V2m 1 le_rfl).smul
          ((V2m 1 le_rfl).smul h s (residueProjection n a e u)) (p+ℓ-s) v) := by
      intro s _
      rw [current_star, zero_add, ih, residueProjection_current]
    rw [Finset.sum_congr rfl hterm] at hT
    have hV := Moonshine.voa_comm (V2m 1 le_rfl) h (residueProjection n a e u) v p ℓ L
      (fun s hs => hK₂ _ (by dsimp [L] at hs; omega))
    rw [hFv, word_cons]
    have hFV := congrArg (rescaledField hn a j (e+f)) hV
    rw [map_sub, map_sum] at hFV
    simp only [map_smul] at hFV
    have hh := hT.trans hFV.symm
    exact sub_right_injective hh

/-- All-state projected twisted products, obtained by induction in both inputs. -/
theorem allStatePF (u v : Space) : PF hn a j u v :=
  Moonshine.LatticeTwistedGeneral.latState_induction (latP 1)
    (P := fun v => PF hn a j u v)
    (PF_zero_right hn a j u) (fun _ _ hv hw => PF_add_right hn a j hv hw)
    (fun c _ hv => PF_smul_right hn a j c hv) (fun l β => PF_word_right hn a j l β u) v

end VOA.Classification.COne.OrbPos7
