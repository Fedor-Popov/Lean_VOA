/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.GhostSystem

/-!
# Ghost number and the vertex products

The one-pair ghost-number decomposition of `GhostSystem` is compatible with every
vertex product.  The proof follows the construction of the fields: creation adds
the charge of its species, contraction removes that charge, differentiation
preserves charge, and normal products add charges.  This supplies the ghost-degree
input for the three-pair semi-infinite complex.
-/

namespace VOA.Ghost

open CliffordAlgebra VOA.SympFerm VOA.Reconstruction
open Module (End)

/-- Conjugate ghost species have opposite ghost numbers. -/
theorem ghCharge_add_one (a : Fin 2) : ghCharge (a + 1) = -ghCharge a := by
  fin_cases a <;> norm_num [ghCharge,
    show ((1 : Fin 2) + 1 = 0) from rfl]

/-- Creation adds the charge of the created species. -/
theorem creBase_mapsTo_ghostGrading (p : ℕ × Fin 2) (n : ℤ) :
    ghostGrading n ≤ (ghostGrading (n + ghCharge p.2)).comap (creBase p) := by
  rw [ghostGrading, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ghNum l = n := hl
  subst n
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  rw [creBase_stWordSF, add_comm (ghNum l), ← ghNum_cons]
  exact stWordSF_mem_ghostGrading (p :: l)

/-- Creation adds the charge of the created species, in membership form. -/
theorem creBase_mem_ghostGrading (p : ℕ × Fin 2) {n : ℤ} {x : FockSF}
    (hx : x ∈ ghostGrading n) :
    creBase p x ∈ ghostGrading (n + ghCharge p.2) :=
  creBase_mapsTo_ghostGrading p n hx

/-- Contraction removes the ghost charge of its index. -/
theorem annBase_stWordSF_mem_ghostGrading (p : ℕ × Fin 2) (l : SFWord) :
    annBase p (stWordSF l) ∈ ghostGrading (ghNum l - ghCharge p.2) := by
  induction l with
  | nil => rw [annBase_stWordSF_nil]; exact Submodule.zero_mem _
  | cons q rest ih =>
      rw [annBase_stWordSF_cons]
      refine Submodule.sub_mem _ ?_ ?_
      · by_cases h : p = q
        · subst q
          rw [if_pos rfl, one_smul, ghNum_cons,
            show ghCharge p.2 + ghNum rest - ghCharge p.2 = ghNum rest by omega]
          exact stWordSF_mem_ghostGrading rest
        · rw [if_neg h, zero_smul]
          exact Submodule.zero_mem _
      · rw [show ι QSF (Finsupp.single q (1 : ℂ)) * annBase p (stWordSF rest)
              = creBase q (annBase p (stWordSF rest)) from by
                rw [creBase, LinearMap.mulLeft_apply],
          ghNum_cons,
          show ghCharge q.2 + ghNum rest - ghCharge p.2
              = (ghNum rest - ghCharge p.2) + ghCharge q.2 by omega]
        exact creBase_mem_ghostGrading q ih

/-- Contraction lowers ghost number by the charge of the removed species. -/
theorem annBase_mapsTo_ghostGrading (p : ℕ × Fin 2) (n : ℤ) :
    ghostGrading n ≤ (ghostGrading (n - ghCharge p.2)).comap (annBase p) := by
  rw [ghostGrading, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ghNum l = n := hl
  subst n
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  exact annBase_stWordSF_mem_ghostGrading p l

/-- Contraction lowers ghost number, in membership form. -/
theorem annBase_mem_ghostGrading (p : ℕ × Fin 2) {n : ℤ} {x : FockSF}
    (hx : x ∈ ghostGrading n) :
    annBase p x ∈ ghostGrading (n - ghCharge p.2) :=
  annBase_mapsTo_ghostGrading p n hx

/-- Every mode of a basic ghost field has the ghost charge of its species. -/
theorem ghField_mem_ghostGrading (a : Fin 2) (j : ℤ) {n : ℤ} {x : FockSF}
    (hx : x ∈ ghostGrading n) :
    ghField a j x ∈ ghostGrading (ghCharge a + n) := by
  by_cases hj : 0 ≤ j
  · rw [ghField, if_pos hj]
    change creBase (j.toNat, a) x ∈ _
    simpa [add_comm] using creBase_mem_ghostGrading (j.toNat, a) hx
  · rw [ghField, if_neg hj]
    change annBase ((-j - 1).toNat, a + 1) x ∈ _
    simpa [ghCharge_add_one, sub_neg_eq_add, add_comm] using
      annBase_mem_ghostGrading ((-j - 1).toNat, a + 1) hx

/-- A field has ghost degree `d` when each coefficient shifts ghost number by `d`. -/
def ChargeField (f : FormalDist (End ℂ FockSF)) (d : ℤ) : Prop :=
  ∀ (j n : ℤ) (x : FockSF), x ∈ ghostGrading n → f j x ∈ ghostGrading (d + n)

/-- The identity field has ghost degree zero. -/
theorem idField_ChargeField : ChargeField idField 0 := by
  intro j n x hx
  rw [idField_apply]
  by_cases hj : j = 0
  · subst j
    simpa using hx
  · rw [if_neg hj, LinearMap.zero_apply]
    exact Submodule.zero_mem _

/-- Scalar multiplication preserves the ghost degree of a field. -/
theorem ChargeField.smul (c : ℂ) {f : FormalDist (End ℂ FockSF)} {d : ℤ}
    (hf : ChargeField f d) : ChargeField (c • f) d := by
  intro j n x hx
  change c • f j x ∈ _
  exact Submodule.smul_mem _ _ (hf j n x hx)

/-- Ghost degrees add under the super normal product. -/
theorem ChargeField.nprod (eps : ℂ) {a b : FormalDist (End ℂ FockSF)}
    (ha : IsField a) (hb : IsField b) {da db : ℤ}
    (hga : ChargeField a da) (hgb : ChargeField b db) :
    ChargeField (nprodε eps ha hb) (da + db) := by
  intro s n x hx
  rw [nprodε_apply]
  refine finsum_mem_submodule _ _ (normalOrderedε_diag_support_finite eps ha hb s x)
    (fun m => ?_)
  rw [normalOrderedε_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0]
    change a m (b (s - m) x) ∈ _
    simpa [add_assoc] using hga m (db + n) _ (hgb (s - m) n x hx)
  · rw [if_neg h0, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    change b (s - m) (a m x) ∈ _
    simpa [add_assoc, add_left_comm] using hgb (s - m) (da + n) _ (hga m n x hx)

/-- Differentiated generator fields retain their species' ghost charge. -/
theorem ghGenField_ChargeField (a : Fin 2) (k : ℕ) :
    ChargeField (ghGenField a k) (ghCharge a) := by
  intro j n x hx
  change ((k.factorial : ℂ)⁻¹ • (VOA.deriv^[k] (ghField a)) j) x ∈ _
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range k, (j + 1 + (i : ℤ))),
    LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (ghField_mem_ghostGrading a (j + (k : ℤ)) hx)

/-- A word field has the total ghost number of its word. -/
theorem YwordGh_ChargeField (l : SFWord) : ChargeField (YwordGh l) (ghNum l) := by
  induction l with
  | nil => rw [YwordGh_nil, ghNum_nil]; exact idField_ChargeField
  | cons p rest ih =>
      rw [YwordGh_cons, ghNum_cons]
      exact ChargeField.nprod _ (ghGenField_isField p.2 p.1) (YwordGh_isField rest)
        (ghGenField_ChargeField p.2 p.1) ih

/-- States whose vertex operators have ghost degree `d` form a submodule. -/
noncomputable def chargeStates (d : ℤ) : Submodule ℂ FockSF where
  carrier := {u : FockSF | ChargeField (YGh u) d}
  add_mem' := by
    intro u v hu hv j n x hx
    rw [map_add]
    change (YGh u) j x + (YGh v) j x ∈ _
    exact Submodule.add_mem _ (hu j n x hx) (hv j n x hx)
  zero_mem' := by
    intro j n x _
    rw [map_zero]
    change (0 : FockSF) ∈ _
    exact Submodule.zero_mem _
  smul_mem' := by
    intro c u hu j n x hx
    rw [map_smul]
    change c • ((YGh u) j x) ∈ _
    exact Submodule.smul_mem _ _ (hu j n x hx)

/-- Homogeneous ghost states produce fields of the same ghost degree. -/
theorem ghostGrading_le_chargeStates (d : ℤ) : ghostGrading d ≤ chargeStates d := by
  rw [ghostGrading, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : ghNum l = d := hl
  subst d
  change ChargeField (YGh (stWordSF l)) (ghNum l)
  rw [YGh_word]
  exact YwordGh_ChargeField l

/-- Ghost numbers add under every coefficient of the one-pair vertex operator. -/
theorem YGh_mem_ghostGrading {m n : ℤ} {u x : FockSF}
    (hu : u ∈ ghostGrading m) (hx : x ∈ ghostGrading n) (j : ℤ) :
    YGh u j x ∈ ghostGrading (m + n) :=
  ghostGrading_le_chargeStates m hu j n x hx

/-- Ghost numbers add under every mode of `bcGhostSVA`. -/
theorem bcGhostSVA_mode_ghostGrading {m n : ℤ} {u x : FockSF}
    (hu : u ∈ ghostGrading m) (hx : x ∈ ghostGrading n) (j : ℤ) :
    mode (bcGhostSVA.Y u) j x ∈ ghostGrading (m + n) :=
  YGh_mem_ghostGrading hu hx (-j - 1)

end VOA.Ghost
