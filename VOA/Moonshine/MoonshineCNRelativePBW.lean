import VOA.Moonshine.MoonshineCNRelativeInduction
import Mathlib.Data.Multiset.Sort

/-! Relative PBW freeness: sorted complementary monomials with arbitrary bottom module. -/

noncomputable section
open scoped TensorProduct
namespace VOA.Moonshine.ConwayNorton

open Module Finsupp
variable {g U : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup U] [Module ℂ U]
variable (p : LieSubalgebra ℂ g) (ρ : p →ₗ⁅ℂ⁆ End ℂ U)
variable {A : Type*} [LinearOrder A] {c : Submodule ℂ g}
variable (hc : IsCompl p.toSubmodule c) (bc : Basis A ℂ c)

/-- Evaluate an ordered word on the bottom of the balanced quotient. -/
def relativeInducedWord : List A → U →ₗ[ℂ] relativeInducedSpace p ρ
  | [] => PBWTheorem.bottom p ρ
  | a :: l => relativeInducedRep p ρ (bc a : g) ∘ₗ relativeInducedWord l

omit [LinearOrder A] in
theorem relativeInducedWord_nil (u : U) :
    relativeInducedWord p ρ bc [] u = PBWTheorem.bottom p ρ u := rfl

omit [LinearOrder A] in
theorem relativeInducedWord_cons (a : A) (l : List A) (u : U) :
    relativeInducedWord p ρ bc (a :: l) u =
      relativeInducedRep p ρ (bc a : g) (relativeInducedWord p ρ bc l u) := rfl

def relativeInducedWordMap : (Multiset A →₀ U) →ₗ[ℂ] relativeInducedSpace p ρ :=
  Finsupp.lsum ℂ fun m => relativeInducedWord p ρ bc (m.sort (· ≤ ·))

theorem relativeInducedWordMap_single (m : Multiset A) (u : U) :
    relativeInducedWordMap p ρ bc (single m u) = relativeInducedWord p ρ bc (m.sort (· ≤ ·)) u := by
  simp [relativeInducedWordMap]

theorem relativeInducedWordMap_zero (u : U) :
    relativeInducedWordMap p ρ bc (single 0 u) = PBWTheorem.bottom p ρ u := by
  simp [relativeInducedWordMap_single, relativeInducedWord]

theorem relativeInducedWordMap_low {a : A} {m : Multiset A}
    (h : ∀ b ∈ m, a ≤ b) (u : U) :
    relativeInducedWordMap p ρ bc (single (a ::ₘ m) u) =
      relativeInducedRep p ρ (bc a : g) (relativeInducedWordMap p ρ bc (single m u)) := by
  rw [relativeInducedWordMap_single, relativeInducedWordMap_single,
    Multiset.sort_cons _ _ _ h, relativeInducedWord_cons]

theorem relativeInducedRep_comm (z w : g) (q : relativeInducedSpace p ρ) :
    relativeInducedRep p ρ z (relativeInducedRep p ρ w q) =
      relativeInducedRep p ρ w (relativeInducedRep p ρ z q) + relativeInducedRep p ρ ⁅z, w⁆ q := by
  have h := DFunLike.congr_fun ((relativeInducedRep p ρ).map_lie z w) q
  change relativeInducedRep p ρ ⁅z, w⁆ q =
    relativeInducedRep p ρ z (relativeInducedRep p ρ w q) -
      relativeInducedRep p ρ w (relativeInducedRep p ρ z q) at h
  rw [h]
  abel

theorem relativePBWCoordinates_word (l : List A) (hl : l.Pairwise (· ≤ ·)) (u : U) :
    relativePBWCoordinates p ρ hc bc (relativeInducedWord p ρ bc l u) =
      single (l : Multiset A) u := by
  induction l with
  | nil => exact relativePBWCoordinates_bottom p ρ hc bc u
  | cons a l ih =>
      rw [List.pairwise_cons] at hl
      rw [relativeInducedWord_cons, relativePBWCoordinates_left, ih hl.2,
        PBWTheorem.rep_apply, PBWTheorem.act_y_low _ _ _ _
          (fun b hb => hl.1 b (Multiset.mem_coe.mp hb))]
      rfl

/-- The finite-degree recursion for PBW action agrees with actual left multiplication. -/
theorem relativeInducedWordMap_action_single (n : ℕ) :
    ∀ m : Multiset A, Multiset.card m = n → ∀ (z : g) (u : U),
      relativeInducedWordMap p ρ bc (PBWTheorem.act p hc bc ρ z (single m u)) =
        relativeInducedRep p ρ z (relativeInducedWordMap p ρ bc (single m u)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hmn z u
    have IH : ∀ j < Multiset.card m, ∀ (w : g) (v : Multiset A →₀ U),
        v ∈ PBWTheorem.Fil (K := ℂ) A U j →
          relativeInducedWordMap p ρ bc (PBWTheorem.act p hc bc ρ w v) =
            relativeInducedRep p ρ w (relativeInducedWordMap p ρ bc v) := by
      intro j hj w v hv
      exact PBWTheorem.eq_on_Fil
        (f := relativeInducedWordMap p ρ bc ∘ₗ PBWTheorem.act p hc bc ρ w)
        (f' := relativeInducedRep p ρ w ∘ₗ relativeInducedWordMap p ρ bc)
        (fun m' u' hm' => ih (Multiset.card m') (by omega) m' rfl w u') hv
    induction z using PBWTheorem.gen_induction p hc bc with
    | h0 => simp
    | hadd z z' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | hsmul r z h => simp only [map_smul, LinearMap.smul_apply, h]
    | hy a =>
        by_cases h : ∀ c ∈ m, a ≤ c
        · rw [PBWTheorem.act_y_low _ _ _ _ h, relativeInducedWordMap_low p ρ bc h]
        · have hm := PBWTheorem.ne_zero_of_not_lb h
          have hba : PBWTheorem.mmin m hm < a := by
            by_contra habs
            exact h fun c hcm => (not_lt.mp habs).trans (PBWTheorem.mmin_le m hm hcm)
          obtain ⟨b0, m', hb0, hba', rfl⟩ : ∃ b0 m', (∀ c ∈ m', b0 ≤ c) ∧ b0 < a ∧
              m = b0 ::ₘ m' :=
            ⟨_, _, PBWTheorem.mmin_lb m hm, hba,
              (Multiset.cons_erase (PBWTheorem.mmin_mem m hm)).symm⟩
          have hlt : Multiset.card m' < Multiset.card (b0 ::ₘ m') := by simp
          have hlow : ∀ c ∈ a ::ₘ m', b0 ≤ c := by
            intro c hc'
            rcases Multiset.mem_cons.mp hc' with rfl | hc'
            · exact hba'.le
            · exact hb0 c hc'
          set X := PBWTheorem.act p hc bc ρ (bc a : g) (single m' u) with hX
          have hXmem := PBWTheorem.act_y_sub_mem p hc bc ρ a m' u
          have e1 : relativeInducedWordMap p ρ bc (PBWTheorem.act p hc bc ρ (bc b0 : g) X) =
              relativeInducedRep p ρ (bc b0 : g) (relativeInducedWordMap p ρ bc X) := by
            have hsplit : X = (X - single (a ::ₘ m') u) + single (a ::ₘ m') u := by abel
            rw [hsplit, map_add, map_add, map_add, map_add,
              IH _ hlt _ _ hXmem, PBWTheorem.act_y_low _ _ _ _ hlow,
              relativeInducedWordMap_low p ρ bc hlow]
          rw [PBWTheorem.act_y_cons _ _ _ _ hba' hb0, map_add, e1, hX,
            ih _ (hmn ▸ hlt) m' rfl, ih _ (hmn ▸ hlt) m' rfl,
            relativeInducedWordMap_low p ρ bc hb0,
            relativeInducedRep_comm p ρ (bc a : g) (bc b0 : g)]
    | hp x =>
        by_cases hm : m = 0
        · subst hm
          rw [PBWTheorem.act_p_zero, relativeInducedWordMap_zero,
            relativeInducedWordMap_zero, relativeInducedRep_bottom]
        · obtain ⟨b0, m', hb0, rfl⟩ : ∃ b0 m', (∀ c ∈ m', b0 ≤ c) ∧ m = b0 ::ₘ m' :=
            ⟨_, _, PBWTheorem.mmin_lb m hm, (Multiset.cons_erase (PBWTheorem.mmin_mem m hm)).symm⟩
          have hlt : Multiset.card m' < Multiset.card (b0 ::ₘ m') := by simp
          have hXmem := PBWTheorem.act_p_mem p hc bc ρ x m' u
          rw [PBWTheorem.act_p_cons _ _ _ _ x hb0, map_add, IH _ hlt _ _ hXmem,
            ih _ (hmn ▸ hlt) m' rfl, ih _ (hmn ▸ hlt) m' rfl,
            relativeInducedWordMap_low p ρ bc hb0,
            relativeInducedRep_comm p ρ (x : g) (bc b0 : g)]

theorem relativeInducedWordMap_action (z : g) (v : Multiset A →₀ U) :
    relativeInducedWordMap p ρ bc (PBWTheorem.rep p hc bc ρ z v) =
      relativeInducedRep p ρ z (relativeInducedWordMap p ρ bc v) := by
  have h : relativeInducedWordMap p ρ bc ∘ₗ PBWTheorem.rep p hc bc ρ z =
      relativeInducedRep p ρ z ∘ₗ relativeInducedWordMap p ρ bc :=
    Finsupp.lhom_ext fun m u => relativeInducedWordMap_action_single p ρ hc bc _ m rfl z u
  exact LinearMap.congr_fun h v

theorem relativeInducedWordMap_enveloping_action (a : UniversalEnvelopingAlgebra ℂ g)
    (v : Multiset A →₀ U) :
    relativeInducedWordMap p ρ bc
      (UniversalEnvelopingAlgebra.lift ℂ (PBWTheorem.rep p hc bc ρ) a v) =
      relativeInducedAlgebra p ρ a (relativeInducedWordMap p ρ bc v) := by
  induction a using envelopingAlgebra_induction generalizing v with
  | hscalar r => simp
  | hlie z =>
      rw [UniversalEnvelopingAlgebra.lift_ι_apply]
      exact relativeInducedWordMap_action p ρ hc bc z v
  | hmul a b ha hb => simp only [map_mul, Module.End.mul_apply, ha, hb]
  | hadd a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

theorem relativePBWCoordinates_wordMap (v : Multiset A →₀ U) :
    relativePBWCoordinates p ρ hc bc (relativeInducedWordMap p ρ bc v) = v := by
  have h : relativePBWCoordinates p ρ hc bc ∘ₗ relativeInducedWordMap p ρ bc = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro m u
    simp only [LinearMap.comp_apply, LinearMap.id_apply, relativeInducedWordMap_single]
    rw [relativePBWCoordinates_word p ρ hc bc _ (Multiset.pairwise_sort m (· ≤ ·)),
      Multiset.sort_eq]
  exact LinearMap.congr_fun h v

theorem relativeInducedWordMap_coordinates (q : relativeInducedSpace p ρ) :
    relativeInducedWordMap p ρ bc (relativePBWCoordinates p ρ hc bc q) = q := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
      rw [relativePBWCoordinates_mk, relativeInducedWordMap_enveloping_action,
        relativeInducedWordMap_zero]
      change Submodule.Quotient.mk ((a * 1) ⊗ₜ[ℂ] u) = _
      rw [mul_one]
  | add t s ht hs => simpa only [Submodule.Quotient.mk_add, map_add] using congrArg₂ (· + ·) ht hs

/-- Full relative PBW freeness, with the explicit balanced quotient and its sorted-word inverse. -/
def relativePBWEquiv : relativeInducedSpace p ρ ≃ₗ[ℂ] (Multiset A →₀ U) :=
  LinearEquiv.ofLinear (relativePBWCoordinates p ρ hc bc) (relativeInducedWordMap p ρ bc)
    (LinearMap.ext (relativePBWCoordinates_wordMap p ρ hc bc))
    (LinearMap.ext (relativeInducedWordMap_coordinates p ρ hc bc))

end VOA.Moonshine.ConwayNorton
