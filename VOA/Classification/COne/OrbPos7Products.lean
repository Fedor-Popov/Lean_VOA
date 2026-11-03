import VOA.Classification.COne.OrbPos7Projection

/-! # Twisted products and the charged base case -/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbPos7
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 OrbPos5 OrbPos6 LatMod TwistedReduction
open Moonshine.LatticeTwisted
open scoped TensorProduct

variable {n : ℕ} (hn : 0 < n) (a j : ℤ)

def fieldSet : Set (Fld Space) := {F | ∃ e u, F = rescaledField hn a j e u}

theorem fieldSet_local : ∀ A ∈ fieldSet hn a j, ∀ B ∈ fieldSet hn a j, Local A.1 B.1 := by
  rintro _ ⟨e, u, rfl⟩ _ ⟨f, v, rfl⟩
  exact rescaledField_local hn a j e f u v

theorem rescaledField_mem (e : ℤ) (u : Space) :
    rescaledField hn a j e u ∈ TGenerated (fieldSet hn a j) :=
  ⟨0, TGen.base ⟨e, u, rfl⟩⟩

theorem current_mem : shiftedCurrent j ((a : ℂ)/(2*n)) ∈ TGenerated (fieldSet hn a j) := by
  rw [← resc_current hn a j]
  exact rescaledField_mem hn a j 0 h

theorem current_star (e ℓ : ℤ) (u : Space) :
    star 0 (shiftedCurrent j ((a : ℂ)/(2*n))) ℓ (rescaledField hn a j e u) =
      rescaledField hn a j e ((V2m 1 le_rfl).smul h ℓ u) := by
  rw [TwistedReduction.star_zero, current_product]

/-- A projected star identity, meaningful for every input and every offset. -/
def PF (u v : Space) : Prop := ∀ e f ℓ : ℤ,
  star ((e : ℂ)/n) (rescaledField hn a j e u) ℓ (rescaledField hn a j f v) =
    rescaledField hn a j (e+f) ((V2m 1 le_rfl).smul (residueProjection n a e u) ℓ v)

theorem PF_zero_left (v : Space) : PF hn a j 0 v := by
  intro e f ℓ
  rw [map_zero, star_zero_left, map_zero, PreVertexAlgebra.smul_zero_left, map_zero]

theorem PF_add_left {u u' v : Space} (hu : PF hn a j u v) (hu' : PF hn a j u' v) :
    PF hn a j (u+u') v := by
  intro e f ℓ
  rw [map_add, star_add_left (rescaledField_local hn a j _ _ _ _)
    (rescaledField_local hn a j _ _ _ _), hu, hu', map_add, PreVertexAlgebra.smul_add_left, map_add]

theorem PF_smul_left {u v : Space} (c : ℂ) (hu : PF hn a j u v) : PF hn a j (c • u) v := by
  intro e f ℓ
  rw [map_smul, star_smul_left (rescaledField_local hn a j _ _ _ _), hu,
    map_smul, PreVertexAlgebra.smul_smul_left, map_smul]

theorem PF_zero_right (u : Space) : PF hn a j u 0 := by
  intro e f ℓ
  rw [map_zero, star_zero_right, PreVertexAlgebra.smul_zero_right, map_zero]

theorem PF_add_right {u v v' : Space} (hv : PF hn a j u v) (hv' : PF hn a j u v') :
    PF hn a j u (v+v') := by
  intro e f ℓ
  rw [map_add, star_add_right (rescaledField_local hn a j _ _ _ _)
    (rescaledField_local hn a j _ _ _ _), hv, hv', PreVertexAlgebra.smul_add_right, map_add]

theorem PF_smul_right {u v : Space} (c : ℂ) (hv : PF hn a j u v) : PF hn a j u (c • v) := by
  intro e f ℓ
  rw [map_smul, star_smul_right (rescaledField_local hn a j _ _ _ _), hv,
    PreVertexAlgebra.smul_smul_right, map_smul]

theorem PF_charges (β γ : ℤ) :
    PF hn a j (latChargeGen (latP 1) β) (latChargeGen (latP 1) γ) := by
  intro e f ℓ
  rw [show residueProjection n a e (latChargeGen (latP 1) β) =
    if (e-a*β) % (n : ℤ) = 0 then latChargeGen (latP 1) β else 0 from
      residueProjection_latState n a e β 1]
  by_cases he : (e-a*β) % (n : ℤ) = 0
  · rw [if_pos he]
    apply fld_ext_mode
    intro s x
    set U := latChargeGen (latP 1) β
    set V := latChargeGen (latP 1) γ
    obtain ⟨N₁, hN₁⟩ := Fld.prod_eventually_zero_of_local (rescaledField_local hn a j e f U V)
    obtain ⟨N₂, hN₂⟩ := PreVertexAlgebra.smul_eventually_zero (V2m 1 le_rfl).toPreVertexAlgebra U V
    have hi := pf_of_inverse (-((e : ℂ)/n))
      (fun ℓ s => mode (rescaledField hn a j (e+f) ((V2m 1 le_rfl).smul U ℓ V)).1 s x)
      (fun ℓ s => mode (Fld.prod ℓ (rescaledField hn a j e U) (rescaledField hn a j f V)).1 s x)
      (max N₁ N₂)
      (fun ℓ s hℓ => by beta_reduce; rw [hN₂ ℓ (le_of_max_le_right hℓ), map_zero, mode_fld_zero])
      (fun ℓ s hℓ => by beta_reduce; rw [hN₁ ℓ (le_of_max_le_left hℓ), mode_fld_zero])
      (fun ℓ s => by
        beta_reduce
        simp only [neg_neg]
        have hc := charge_product_all_right_offsets hn a j β γ e f ℓ s he x
        convert hc using 1
        apply finsum_congr
        intro d
        change _ = cbinom ((e : ℂ)/n) d •
          shiftedY n a j ((V2m 1 le_rfl).smul U (ℓ+d) V) ((n : ℤ)*(s-d)+e+f) x
        rw [show (rescaledField hn a j (e+f) ((V2m 1 le_rfl).smul U (ℓ+d) V)).1 =
          resc (shiftedY n a j ((V2m 1 le_rfl).smul U (ℓ+d) V)) n (e+f) from rfl, mode_resc]
        rw [show (n : ℤ)*(s-d)+(e+f) = (n : ℤ)*(s-d)+e+f by ring])
      ℓ s
    obtain ⟨K, hK⟩ := exists_prod_offset_zero (rescaledField_local hn a j e f U V) ℓ
    rw [star_eq_sum_range _ _ _ _ K hK, mode_fld_sum, hi,
      finsum_nat_eq_sum_range K _ (fun d hd => by rw [hK d hd, mode_fld_zero, smul_zero])]
    apply Finset.sum_congr rfl
    intro d _
    rw [mode_fld_smul, mode_fzmul, sub_eq_add_neg]
  · rw [if_neg he, PreVertexAlgebra.smul_zero_left, map_zero]
    have hz : rescaledField hn a j e (latChargeGen (latP 1) β) = 0 :=
      rescaledField_sector_off hn a j β e he 1
    rw [hz, star_zero_left]

end VOA.Classification.COne.OrbPos7
