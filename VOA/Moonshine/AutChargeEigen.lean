/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.AutZeroModes
import VOA.Moonshine.AutFockEigen
import VOA.Moonshine.LatticeInvolution

/-!
# Joint eigenvectors of the quadratic zero modes in a lattice VOA
(Aut(V♮) campaign, step 3, route C, node C3 transport, `Notes/MONSTER_AUT_PLAN.md`)

For an even positive-definite lattice `L` of rank `≥ 2`: if `v ∈ V_L` satisfies
`o(q_ab) v = β_a β_b · v` for all frame directions `a, b` (`β_a = chargeCoord β a`), then
`v ∈ span{e^β, e^{−β}}`.  Charge sector by charge sector, the Fock component is a joint
eigenvector of the operators `N_ab` (`smul_quadState_one`), hence constant with
`γ_a γ_b = β_a β_b` (`HeisenbergN.quadOp_joint_eigen`), hence `γ = ±β`.

## Main results
* `coordEα_smul_quadState` — `o(q_ab)` acts on the charge-`γ` component as `γ_aγ_b + N_ab`.
* `eq_of_chargeCoord_eq`, `chargeCoord_rankOne` — `γ_aγ_b = β_aβ_b` for all `a, b` forces `γ = ±β`.
* ⭐ `eigen_quadState_span` — the joint eigenvectors are `c₁ e^β + c₂ e^{−β}`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.AutMonster

open VOA VOA.LatGen VOA.IntegralLattice HeisenbergN MvPolynomial

variable (L : IntegralLattice)

/-! ## Charge components -/

open Classical in
theorem coordEα_eq_finsuppScalarRight' (n : L.carrier) (y : LatModuleGen L) :
    coordEα L n y = TensorProduct.finsuppScalarRight ℂ ℂ (FockN (rank L)) L.carrier y n := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, ha, hb, map_add, Finsupp.add_apply]
  | tmul p g =>
    rw [TensorProduct.finsuppScalarRight_apply_tmul_apply, coordEα, LinearMap.comp_apply,
      LinearMap.lTensor_tmul, Finsupp.lapply_apply]
    exact TensorProduct.rid_tmul _ _

/-- A lattice-VOA vector all of whose charge components vanish is zero. -/
theorem eq_zero_of_coordEα' {y : LatModuleGen L} (h : ∀ n, coordEα L n y = 0) : y = 0 := by
  classical
  have hf : TensorProduct.finsuppScalarRight ℂ ℂ (FockN (rank L)) L.carrier y = 0 := by
    ext n
    rw [← coordEα_eq_finsuppScalarRight', h n, Finsupp.coe_zero, Pi.zero_apply]
  exact (LinearEquiv.map_eq_zero_iff _).mp hf

open Classical in
theorem coordEα_latStateGen (γ δ : L.carrier) (p : FockN (rank L)) :
    coordEα L γ (latStateGen L p δ) = if γ = δ then p else 0 :=
  coordEα_apply L γ δ p

/-- `o(q_ab)` on the charge-`γ` component: `γ_aγ_b · p + N_ab p`. -/
theorem coordEα_smul_quadState (hEven : L.Even) (hPos : L.PosDef) (a b : Fin (rank L))
    (γ : L.carrier) (v : LatModuleGen L) :
    coordEα L γ ((latticeVOAGen L hEven hPos).smul (quadState L a b) 1 v)
      = (chargeCoord L γ a * chargeCoord L γ b) • coordEα L γ v
        + nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 b) (-2)
            (coordEα L γ v) := by
  have hlin : ∀ y, (latticeVOAGen L hEven hPos).smul (quadState L a b) 1 y
      = mode (YfullGen L hEven hPos (quadState L a b)) 1 y := fun y => rfl
  induction v using TensorProduct.induction_on with
  | zero => rw [hlin, map_zero, map_zero, smul_zero, map_zero, add_zero]
  | add x y hx hy =>
    rw [hlin, map_add, map_add, ← hlin, ← hlin, hx, hy, map_add (coordEα L γ), smul_add,
      map_add]
    abel
  | tmul p g =>
    induction g using Finsupp.induction_linear with
    | zero => rw [TensorProduct.tmul_zero, hlin, map_zero, map_zero, smul_zero, map_zero, add_zero]
    | add f g hf hg =>
      rw [TensorProduct.tmul_add, hlin, map_add, map_add, ← hlin, ← hlin, hf, hg,
        map_add (coordEα L γ), smul_add, map_add]
      abel
    | single δ c =>
      have hs : p ⊗ₜ[ℂ] Finsupp.single δ c = c • latStateGen L p δ := by
        rw [latStateGen, eGen, ← TensorProduct.tmul_smul, Finsupp.smul_single_one]
      rw [hs, PreVertexAlgebra.smul_smul_right, smul_quadState_one, map_smul, map_smul,
        coordEα_latStateGen, coordEα_latStateGen, map_smul]
      by_cases hγ : γ = δ
      · subst hγ
        simp only [if_true, smul_add]
        rw [smul_comm c]
      · simp only [if_neg hγ, map_zero, smul_zero, add_zero]

/-! ## Rank-one equality of charge coordinates -/

theorem eq_zero_of_chargeCoord (hPos : L.PosDef) (δ : L.carrier)
    (h : ∀ a, chargeCoord L δ a = 0) : δ = 0 := by
  by_contra hne
  have hpos := hPos δ hne
  have hs := sum_chargeCoord L hPos δ δ
  simp only [h, mul_zero, Finset.sum_const_zero] at hs
  have : L.form δ δ = 0 := by exact_mod_cast hs.symm
  omega

theorem chargeCoord_sub (γ β : L.carrier) (a : Fin (rank L)) :
    chargeCoord L (γ - β) a = chargeCoord L γ a - chargeCoord L β a := by
  rw [sub_eq_add_neg, chargeCoord_add, chargeCoord_neg, ← sub_eq_add_neg]

theorem eq_of_chargeCoord_eq (hPos : L.PosDef) {γ β : L.carrier}
    (h : ∀ a, chargeCoord L γ a = chargeCoord L β a) : γ = β :=
  sub_eq_zero.1 (eq_zero_of_chargeCoord L hPos _ fun a => by rw [chargeCoord_sub, h a, sub_self])

/-- `γ_aγ_b = β_aβ_b` for all `a, b` forces `γ = ±β`. -/
theorem chargeCoord_rankOne (hPos : L.PosDef) {γ β : L.carrier}
    (h : ∀ a b, chargeCoord L γ a * chargeCoord L γ b = chargeCoord L β a * chargeCoord L β b) :
    γ = β ∨ γ = -β := by
  by_cases hβ : ∀ a, chargeCoord L β a = 0
  · left
    have hγ : ∀ a, chargeCoord L γ a = 0 := fun a => by
      have := h a a
      rw [hβ a, mul_zero] at this
      exact mul_self_eq_zero.1 this
    rw [eq_zero_of_chargeCoord L hPos γ hγ, eq_zero_of_chargeCoord L hPos β hβ]
  · simp only [not_forall] at hβ
    obtain ⟨a₀, ha₀⟩ := hβ
    rcases mul_self_eq_mul_self_iff.1 (h a₀ a₀) with h0 | h0
    · left
      refine eq_of_chargeCoord_eq L hPos fun b => ?_
      have := h a₀ b
      rw [h0] at this
      exact mul_left_cancel₀ ha₀ this
    · right
      refine eq_of_chargeCoord_eq L hPos fun b => ?_
      rw [chargeCoord_neg]
      have := h a₀ b
      rw [h0] at this
      have h2 : chargeCoord L β a₀ * chargeCoord L γ b
          = chargeCoord L β a₀ * (-chargeCoord L β b) := by
        linear_combination -this
      exact mul_left_cancel₀ ha₀ h2

/-! ## The joint eigenvectors -/

theorem exists_levelBoundN {r : ℕ} (x : FockN r) : ∃ K : ℕ, ∀ v ∈ x.vars, v.1 < K :=
  ⟨x.vars.sup Prod.fst + 1, fun _ hv => Nat.lt_succ_of_le (Finset.le_sup (f := Prod.fst) hv)⟩

/-- In each charge sector, a joint eigenvector component is constant and sits at charge `±β`. -/
theorem coordEα_of_eigen (hEven : L.Even) (hPos : L.PosDef)
    (hr : ∀ b : Fin (rank L), ∃ a, a ≠ b) (β : L.carrier) (v : LatModuleGen L)
    (h : ∀ a b, (latticeVOAGen L hEven hPos).smul (quadState L a b) 1 v
      = (chargeCoord L β a * chargeCoord L β b) • v)
    (γ : L.carrier) (hne : coordEα L γ v ≠ 0) :
    (γ = β ∨ γ = -β) ∧ coordEα L γ v = MvPolynomial.C (coeff 0 (coordEα L γ v)) := by
  set p := coordEα L γ v with hp
  obtain ⟨K, hK⟩ := exists_levelBoundN p
  have heig : ∀ a b, quadOp (fun k => (k : ℂ) + 1) K a b p
      = (chargeCoord L β a * chargeCoord L β b - chargeCoord L γ a * chargeCoord L γ b) • p := by
    intro a b
    have h1 := coordEα_smul_quadState L hEven hPos a b γ v
    rw [h a b, map_smul, ← hp, nprod_currentN_neg_two_eq_quadOp a b p K hK] at h1
    rw [sub_smul, h1]
    abel
  obtain ⟨hc, hconst⟩ := quadOp_joint_eigen (fun k => (k : ℂ) + 1)
    (fun k k' => by
      have : ((k + k' + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      push_cast at this
      intro h0; apply this; linear_combination h0)
    (fun k k' h0 => by exact_mod_cast add_right_cancel h0)
    hr K p hK _ heig hne
  refine ⟨chargeCoord_rankOne L hPos fun a b => ?_, hconst⟩
  have := hc a b
  linear_combination -this

/-- ⭐ **Joint eigenvectors of the quadratic zero modes in `V_L`**: if `o(q_ab) v = β_aβ_b · v`
for all `a, b` (rank `≥ 2`), then `v = c₁ e^β + c₂ e^{−β}`. -/
theorem eigen_quadState_span (hEven : L.Even) (hPos : L.PosDef)
    (hr : ∀ b : Fin (rank L), ∃ a, a ≠ b) (β : L.carrier) (v : LatModuleGen L)
    (h : ∀ a b, (latticeVOAGen L hEven hPos).smul (quadState L a b) 1 v
      = (chargeCoord L β a * chargeCoord L β b) • v) :
    ∃ c₁ c₂ : ℂ, v = c₁ • latChargeGen L β + c₂ • latChargeGen L (-β) := by
  classical
  -- every component is a constant polynomial
  have hcomp : ∀ γ, coordEα L γ v = MvPolynomial.C (coeff 0 (coordEα L γ v)) := fun γ => by
    by_cases h0 : coordEα L γ v = 0
    · rw [h0, coeff_zero, MvPolynomial.C_0]
    · exact (coordEα_of_eigen L hEven hPos hr β v h γ h0).2
  -- components off `±β` vanish
  have hoff : ∀ γ, γ ≠ β → γ ≠ -β → coordEα L γ v = 0 := fun γ h1 h2 => by
    by_contra h0
    rcases (coordEα_of_eigen L hEven hPos hr β v h γ h0).1 with h3 | h3
    · exact h1 h3
    · exact h2 h3
  have hCone : ∀ c : ℂ, MvPolynomial.C c = c • vacuumN (rank L) := fun c => by
    rw [vacuumN, smul_eq_C_mul, mul_one]
  have hcharge : ∀ γ δ, coordEα L γ (latChargeGen L δ) = if γ = δ then vacuumN (rank L) else 0 :=
    fun γ δ => coordEα_latStateGen L γ δ _
  by_cases hβ0 : β = 0
  · subst hβ0
    refine ⟨coeff 0 (coordEα L 0 v), 0, ?_⟩
    rw [zero_smul, add_zero, ← sub_eq_zero]
    refine eq_zero_of_coordEα' L fun γ => ?_
    rw [map_sub, map_smul, hcharge]
    by_cases hγ : γ = 0
    · subst hγ
      rw [if_pos rfl, ← hCone, ← hcomp, sub_self]
    · rw [if_neg hγ, smul_zero, sub_zero, hoff γ hγ (by rw [neg_zero]; exact hγ)]
  · have hβn : β ≠ -β := by
      intro hb
      apply hβ0
      have hform : L.form β β = L.form β (-β) := by rw [← hb]
      rw [map_neg] at hform
      by_contra hne
      have := hPos β hne
      omega
    refine ⟨coeff 0 (coordEα L β v), coeff 0 (coordEα L (-β) v), ?_⟩
    rw [← sub_eq_zero]
    refine eq_zero_of_coordEα' L fun γ => ?_
    rw [map_sub, map_add, map_smul, map_smul, hcharge, hcharge]
    by_cases h1 : γ = β
    · subst h1
      rw [if_pos rfl, if_neg hβn, smul_zero, add_zero, ← hCone, ← hcomp, sub_self]
    · by_cases h2 : γ = -β
      · subst h2
        rw [if_neg h1, if_pos rfl, smul_zero, zero_add, ← hCone, ← hcomp, sub_self]
      · rw [if_neg h1, if_neg h2, smul_zero, smul_zero, add_zero, sub_zero, hoff γ h1 h2]

end VOA.Moonshine.AutMonster
