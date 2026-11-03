/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLExtFixed
import VOA.Huang.RepPackagingSemisimple
import VOA.Huang.HKLExtHeadline

/-!
# HKL extensions: a haploid algebra in `Rep V` is of CFT type — `HKLCFTTypeInput`

`hklCFTTypeInput_holds : HKLCFTTypeInput`.  For nice `V` and an algebra `A` in `Ordinary V`
with `dim Hom(V, A) = 1`:

* `A ≅ ⊕_j R_j` with `R_j` irreducible (`semisimple_lw_pbw`, strong rationality);
* a summand `R_j ≇ V` has only weights of positive real part (pseudo-unitarity), a summand
  `R_j ≅ V` has the weights of `V` (CFT type: `V_0 = ℂ𝟙`, `V_{<0} = 0`);
* hence `A_k = 0` for `k < 0`, and `dim A_0 = #{j | R_j ≅ V} = dim Hom(V, A) = 1` (Schur);
* `η(𝟙) ∈ A_0` is nonzero (`eta_injective`), so `A_0 = ℂ η(𝟙)`.

Consequently `gannonRayhaun_hkl_two` — the forward Gannon–Rayhaun theorem with HKL reduced to
the two inputs `HKLLocalityInput` and `HKLNiceInput`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLExt

open CategoryTheory MonoidalCategory Limits Module
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.FusionUnit
  VOA.Huang.FusionProduct VOA.Huang.TensorCat.BraidRibbon VOA.Huang.TensorCat.RepPackaging

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-- `Hom(Z, ⨁ g) ≃ Π_k Hom(Z, g k)`, linearly, in `Ordinary V`. -/
def homBiproductEquivOrd {J : Type} [Fintype J] (g : J → Ordinary V) (Z : Ordinary V) :
    (Z ⟶ ⨁ g) ≃ₗ[ℂ] ((k : J) → (Z ⟶ g k)) where
  toFun h k := h ≫ biproduct.π g k
  map_add' a b := by funext k; simp [Preadditive.add_comp]
  map_smul' c a := by funext k; simp
  invFun p := biproduct.lift p
  left_inv h := by apply biproduct.hom_ext; intro k; simp
  right_inv p := by funext k; simp

/-- Weight spaces of a finite biproduct of ordinary modules. -/
theorem finrank_weight_biproduct {n : ℕ} (g : Fin n → Ordinary V) (α : ℂ) :
    finrank ℂ ((⨁ g).isMod.weight α) = ∑ k, finrank ℂ ((g k).isMod.weight α) :=
  finrank_weight_of_decomp g (fun k => biproduct.π g k) (fun k => biproduct.ι g k)
    biproduct.total (fun k => biproduct.ι_π_self g k) (fun _ _ hkl => biproduct.ι_π_ne g hkl) α

/-- The weights of the adjoint module: `dim (V as module)_k = dim V_k` for integral `k`. -/
theorem finrank_vacuumObject_weight (k : ℤ) :
    finrank ℂ ((vacuumObject (W := V)).isMod.weight (k : ℂ)) = finrank ℂ (V.grading k) := by
  change finrank ℂ (adjWeight V (k : ℂ)) = _
  rw [adjWeight_cast]

/-- **A haploid algebra in `Rep V` is of CFT type** (`HKLCFTTypeInput` holds). -/
theorem hklCFTTypeInput_holds : HKLCFTTypeInput.{u} := by
  classical
  intro 𝒱 _ _ V hV F
  letI := monoidalCategoryOfStronglyRational_pbw F hV.1
  intro A _ hhap
  have hhap' : finrank ℂ (vacuumObject ⟶ A) = 1 := hhap
  haveI : ∀ X Y : Ordinary V, FiniteDimensional ℂ (X ⟶ Y) := finiteDimensional_hom_pbw hV.1
  haveI hvacS : Simple (vacuumObject (W := V)) :=
    simple_of_irreducible _ ((isSimple_iff_adjointModule_isIrreducible V).mp
      hV.1.toStronglyFinite.simple)
  obtain ⟨n, R, hR, ⟨e⟩⟩ := semisimple_lw_pbw hV.1 A
  let g : Fin n → Ordinary V := fun j => Ordinary.of (R j).isMod
  haveI hgS : ∀ j, Simple (g j) := fun j => simple_of_irreducible _ (hR j)
  have hwt : ∀ α : ℂ, finrank ℂ (A.isMod.weight α) = ∑ j, finrank ℂ ((g j).isMod.weight α) :=
    fun α => (finrank_weight_congr e α).trans (finrank_weight_biproduct g α)
  -- each summand: either `≅ V`, or of positive weights
  have hsum : ∀ j, (Nonempty (vacuumObject ≅ g j)) ∨
      (∀ α : ℂ, (g j).isMod.weight α ≠ ⊥ → 0 < α.re) := by
    intro j
    by_cases hj : Nonempty (vacuumObject ≅ g j)
    · exact Or.inl hj
    · refine Or.inr (hV.2 (R j).carrier (R j).isMod (hR j) ⟨fun me => hj ?_⟩)
      exact ⟨(Ordinary.isoOfModuleEquiv (X := g j) (Y := vacuumObject) me).symm⟩
  have hdimj : ∀ j (k : ℤ), finrank ℂ ((g j).isMod.weight (k : ℂ)) =
      if Nonempty (vacuumObject ≅ g j) then finrank ℂ (V.grading k)
      else if 0 < k then finrank ℂ ((g j).isMod.weight (k : ℂ)) else 0 := by
    intro j k
    split_ifs with h1 h2
    · rw [← finrank_vacuumObject_weight k]
      exact (finrank_weight_congr h1.some (k : ℂ)).symm
    · rfl
    · rcases hsum j with h | h
      · exact absurd h h1
      · have hb : (g j).isMod.weight (k : ℂ) = ⊥ := by
          by_contra hne
          have := h _ hne
          simp only [Complex.intCast_re] at this
          exact h2 (by exact_mod_cast this)
        rw [hb, finrank_bot]
  -- negative weights
  have hneg : ∀ k : ℤ, k < 0 → A.isMod.weight (k : ℂ) = ⊥ := by
    intro k hk
    haveI := A.isMod.finrank (k : ℂ)
    apply Submodule.finrank_eq_zero.mp
    rw [hwt]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hdimj j k]
    split_ifs with h1 h2
    · rw [V.positivity k hk, finrank_bot]
    · omega
    · rfl
  refine ⟨?_, hneg⟩
  -- weight zero
  let η : vacuumObject ⟶ A := MonObj.one
  have hinj := eta_injective (m := (MonObj.mul : tensorObj F A A ⟶ A)) hV (MonObj.one_mul A) hhap'
  have hvne : η.val V.vacuum ≠ 0 := fun h0 =>
    hV.1.toStronglyFinite.vacuum_ne_zero (hinj (h0.trans (map_zero η.val).symm))
  have hmem : η.val V.vacuum ∈ A.isMod.weight 0 := by
    have := hom_mem_weight (M₂ := 𝒱) (A₂ := adjointModule V) η.property vacuum_mem_adj
    simpa using this
  -- `dim A_0 = 1`
  have hV0 : finrank ℂ (V.grading 0) = 1 := by
    rw [V.vacuum_grade, finrank_span_singleton hV.1.toStronglyFinite.vacuum_ne_zero]
  have hcount : ∑ j : Fin n, (if Nonempty (vacuumObject ≅ g j) then 1 else 0) = 1 := by
    have h1 : finrank ℂ (vacuumObject ⟶ A) = ∑ j, finrank ℂ (vacuumObject ⟶ g j) := by
      rw [(Linear.homCongr ℂ (Iso.refl _) e).finrank_eq,
        (homBiproductEquivOrd g vacuumObject).finrank_eq, Module.finrank_pi_fintype]
    refine Eq.trans ?_ (h1.symm.trans hhap')
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [finrank_hom_simple_simple ℂ]
  have hA0 : finrank ℂ (A.isMod.weight 0) = 1 := by
    have h := hwt ((0 : ℤ) : ℂ)
    rw [Int.cast_zero] at h
    rw [h, ← hcount]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 := hdimj j 0
    rw [Int.cast_zero] at h2
    rw [h2]
    split_ifs <;> simp_all
  haveI := A.isMod.finrank 0
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hmem
  · rw [finrank_span_singleton hvne, hA0]

/-- **Gannon–Rayhaun Theorem 3.1 (forward) with HKL reduced to two inputs**: locality of the
extension vertex operator (`HKLLocalityInput`, HKL 2015 Thm 3.2) and niceness of the extension of
a Frobenius algebra (`HKLNiceInput`, KO 2002 / CKM 2017 / GR Prop. 2.7). -/
theorem _root_.VOA.Classification.COne.gannonRayhaun_hkl_two
    (hC : VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u})
    (hG : VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2)
    (hL : HKLLocalityInput.{u}) (hN : HKLNiceInput.{u}) :
    GannonRayhaunStatement.{u} :=
  VOA.Classification.COne.gannonRayhaun_huang_rigid hC hG hQ
    (hklRepInputRigid_of_ordinary (hklOrdinaryInput_of_inputs hL hklCFTTypeInput_holds hN))

end VOA.Huang.HKLExt
