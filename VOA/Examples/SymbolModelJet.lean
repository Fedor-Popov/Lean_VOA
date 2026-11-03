/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.SymbolModelTaylor
import VOA.Examples.SymbolModelCore

/-!
# The jet polynomial ring of a column `(u(s), v(s))` and cyclicity at the base point

The loop algebra `sl₂[s]` acts on
formal columns `(u(s), v(s))` by

  `e_m u = 0, e_m v = s^m u,  f_m u = s^m v, f_m v = 0,  h_m u = s^m u, h_m v = -s^m v`.

On the jet coordinates `u = Σ u_j s^j`, `v = Σ v_j s^j` these are derivations of
`C[u_j, v_j]` (`jetDer`). This file proves, with an algebraic Taylor argument replacing the
loop-group orbit and density argument of the note:

* `jet_cyclic` — **evaluation at the base point `(u, v) = (0, 1)` is cyclic**: a jet polynomial
  `Q` with `ev((D_{k_1} ⋯ D_{k_ℓ}) Q) = 0` for every word in the nonnegative modes is zero.

(The note uses the base point `(1, 0)`; the point `(0, 1)` matches the charge convention of
`CyclicDual`, whose vector has `h₀`-weight `-2r` under the negative-transpose action.)

Everything is proved outright.
-/

namespace VOA.SymbolModel

open MvPolynomial
open VOA.CyclicEval (word)

noncomputable section

/-- The jet polynomial ring `C[u_j, v_j]`, with `u_j = X (0, j)` and `v_j = X (1, j)`. -/
abbrev JetPoly : Type := MvPolynomial (Fin 2 × ℕ) ℂ

/-- `s^m` times the jet series of colour `b`, at index `j`. -/
def shiftVar (b : Fin 2) (m j : ℕ) : JetPoly := if m ≤ j then X (b, j - m) else 0

/-- The values of the mode derivations on the jet coordinates
(`(0, m), (1, m), (2, m)` are `e_m, f_m, h_m`). -/
def jetDerVal (k : Fin 3 × ℕ) (x : Fin 2 × ℕ) : JetPoly :=
  if k.1 = 0 then (if x.1 = 1 then shiftVar 0 k.2 x.2 else 0)
  else if k.1 = 1 then (if x.1 = 0 then shiftVar 1 k.2 x.2 else 0)
  else (if x.1 = 0 then shiftVar 0 k.2 x.2 else -shiftVar 1 k.2 x.2)

/-- **The mode derivations** of `sl₂[s]` on the jet ring. -/
def jetDer (k : Fin 3 × ℕ) : Derivation ℂ JetPoly JetPoly := mkDerivation ℂ (jetDerVal k)

@[simp] theorem jetDer_X (k : Fin 3 × ℕ) (x : Fin 2 × ℕ) : jetDer k (X x) = jetDerVal k x :=
  mkDerivation_X _ _ _

/-- The mode action as linear endomorphisms. -/
def jetRho (k : Fin 3 × ℕ) : Module.End ℂ JetPoly := (jetDer k).toLinearMap

@[simp] theorem jetRho_apply (k : Fin 3 × ℕ) (Q : JetPoly) : jetRho k Q = jetDer k Q := rfl

theorem shiftVar_isHomogeneous (b : Fin 2) (m j : ℕ) : (shiftVar b m j).IsHomogeneous 1 := by
  unfold shiftVar
  split_ifs
  · exact isHomogeneous_X _ _
  · exact isHomogeneous_zero _ _ _

theorem jetDerVal_isHomogeneous (k : Fin 3 × ℕ) (x : Fin 2 × ℕ) :
    (jetDerVal k x).IsHomogeneous 1 := by
  unfold jetDerVal
  split_ifs <;> first
    | exact shiftVar_isHomogeneous _ _ _
    | exact isHomogeneous_zero _ _ _
    | exact (shiftVar_isHomogeneous _ _ _).neg

/-! ### The base point and the shift of `v_0` -/

/-- The base point `(u, v) = (0, 1)`. -/
def baseVal (x : Fin 2 × ℕ) : ℂ := if x = (1, 0) then 1 else 0

/-- Evaluation at the base point. -/
def evalBase : JetPoly →ₐ[ℂ] ℂ := aeval baseVal

/-- `v_0 ↦ v_0 + 1`. -/
def shiftUp : JetPoly →ₐ[ℂ] JetPoly := aeval fun x => X x + MvPolynomial.C (baseVal x)

/-- `v_0 ↦ v_0 - 1`. -/
def shiftDown : JetPoly →ₐ[ℂ] JetPoly := aeval fun x => X x - MvPolynomial.C (baseVal x)

@[simp] theorem shiftUp_X (x : Fin 2 × ℕ) :
    shiftUp (X x) = X x + MvPolynomial.C (baseVal x) := aeval_X _ _
@[simp] theorem shiftDown_X (x : Fin 2 × ℕ) : shiftDown (X x) = X x - MvPolynomial.C (baseVal x) :=
  aeval_X _ _

theorem shiftUp_shiftDown (Q : JetPoly) : shiftUp (shiftDown Q) = Q := by
  have h : shiftUp.comp shiftDown = AlgHom.id ℂ JetPoly :=
    algHom_ext fun x => by simp
  exact AlgHom.congr_fun h Q

theorem shiftDown_shiftUp (Q : JetPoly) : shiftDown (shiftUp Q) = Q := by
  have h : shiftDown.comp shiftUp = AlgHom.id ℂ JetPoly :=
    algHom_ext fun x => by simp
  exact AlgHom.congr_fun h Q

theorem evalBase_shiftDown (Q : JetPoly) : evalBase (shiftDown Q) = constantCoeff Q := by
  have h : evalBase.comp shiftDown = aeval (0 : Fin 2 × ℕ → ℂ) :=
    algHom_ext fun x => by simp [evalBase, aeval_X]
  rw [← AlgHom.comp_apply, h, aeval_zero]
  rfl

/-! ### Conjugated derivations -/

/-- `shiftUp ∘ D ∘ shiftDown`, a derivation. -/
def conjDer (D : Derivation ℂ JetPoly JetPoly) : Derivation ℂ JetPoly JetPoly where
  toLinearMap := shiftUp.toLinearMap ∘ₗ D.toLinearMap ∘ₗ shiftDown.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' a b := by
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
    rw [map_mul, Derivation.coeFn_coe, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul, shiftUp_shiftDown, shiftUp_shiftDown, smul_eq_mul, smul_eq_mul]

@[simp] theorem conjDer_apply (D : Derivation ℂ JetPoly JetPoly) (Q : JetPoly) :
    conjDer D Q = shiftUp (D (shiftDown Q)) := rfl

theorem shiftUp_shiftVar (b : Fin 2) (m j : ℕ) :
    shiftUp (shiftVar b m j) = shiftVar b m j + if b = 1 ∧ j = m then 1 else 0 := by
  unfold shiftVar
  by_cases h1 : m ≤ j
  · rw [if_pos h1, shiftUp_X]
    congr 1
    simp only [baseVal]
    by_cases hb : b = 1 ∧ j = m
    · obtain ⟨rfl, rfl⟩ := hb
      simp
    · rw [if_neg hb, if_neg, map_zero]
      intro h
      apply hb
      refine ⟨congrArg Prod.fst h, ?_⟩
      have := congrArg Prod.snd h
      simp only at this
      omega
  · rw [if_neg h1, map_zero, zero_add, if_neg]
    rintro ⟨-, rfl⟩
    exact h1 le_rfl

/-- The `f_m` conjugate is `∂_{u_m} + f_m`. -/
theorem conjDer_f (m : ℕ) :
    conjDer (jetDer (1, m)) = pderiv (0, m) + jetDer (1, m) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨b, j⟩
  simp only [conjDer_apply, shiftDown_X, map_sub, jetDer_X, Derivation.map_algebraMap,
    ← algebraMap_eq, sub_zero, Derivation.add_apply, pderiv_X]
  fin_cases b
  · simp only [jetDerVal, Fin.zero_eta, Fin.isValue, one_ne_zero, ↓reduceIte, Fin.mk_one]
    rw [shiftUp_shiftVar]
    simp only [Pi.single_apply, Prod.mk.injEq, true_and]
    by_cases hj : j = m
    · subst hj; simp [add_comm]
    · simp [hj]
  · simp only [jetDerVal]
    simp

/-- The `h_m` conjugate is `-∂_{v_m} + h_m`. -/
theorem conjDer_h (m : ℕ) :
    conjDer (jetDer (2, m)) = (-1 : ℂ) • pderiv (1, m) + jetDer (2, m) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨b, j⟩
  simp only [conjDer_apply, shiftDown_X, map_sub, jetDer_X, Derivation.map_algebraMap,
    ← algebraMap_eq, sub_zero, Derivation.add_apply, Derivation.smul_apply, pderiv_X]
  fin_cases b
  · simp only [jetDerVal]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.zero_eta]
    rw [shiftUp_shiftVar]
    simp [Pi.single_apply]
  · simp only [jetDerVal]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.mk_one, map_neg]
    rw [shiftUp_shiftVar]
    by_cases hj : j = m
    · subst hj; simp [Pi.single_apply]
    · simp [Pi.single_apply, hj]

/-! ### Cyclicity -/

/-- The space of jet polynomials all of whose translates vanish at the base point. -/
def baseNull : Submodule ℂ JetPoly where
  carrier := {Q | ∀ l : List (Fin 3 × ℕ), evalBase (word jetRho l Q) = 0}
  add_mem' {a b} ha hb l := by rw [map_add, map_add, ha l, hb l, add_zero]
  zero_mem' l := by rw [map_zero, map_zero]
  smul_mem' c a ha l := by rw [map_smul, map_smul, ha l, smul_zero]

theorem word_append_single (l : List (Fin 3 × ℕ)) (k : Fin 3 × ℕ) (Q : JetPoly) :
    word jetRho (l ++ [k]) Q = word jetRho l (jetRho k Q) := by
  simp [word, List.map_append, List.prod_append, Module.End.mul_apply]

theorem baseNull_stable (k : Fin 3 × ℕ) (Q : JetPoly) (hQ : Q ∈ baseNull) :
    jetRho k Q ∈ baseNull := fun l => by
  rw [← word_append_single]; exact hQ _

theorem jetDer_isHomogeneous (k : Fin 3 × ℕ) (d : ℕ) (R : JetPoly) (hR : R.IsHomogeneous d) :
    ((jetDer k).toLinearMap R).IsHomogeneous d :=
  derivation_isHomogeneous _ (fun y => by rw [jetDer_X]; exact jetDerVal_isHomogeneous _ y) d R hR

/-- The Taylor form of the conjugated `f_m` at `u_m`. -/
def taylorF (m : ℕ) : TaylorForm (conjDer (jetDer (1, m))).toLinearMap ((0 : Fin 2), m) where
  c := 1
  c_ne := one_ne_zero
  E := (jetDer (1, m)).toLinearMap
  E_hom := jetDer_isHomogeneous (1, m)
  eq := LinearMap.ext fun Q => by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Derivation.coeFn_coe, conjDer_f,
      Derivation.add_apply, one_smul]

/-- The Taylor form of the conjugated `h_m` at `v_m`. -/
def taylorH (m : ℕ) : TaylorForm (conjDer (jetDer (2, m))).toLinearMap ((1 : Fin 2), m) where
  c := -1
  c_ne := by norm_num
  E := (jetDer (2, m)).toLinearMap
  E_hom := jetDer_isHomogeneous (2, m)
  eq := LinearMap.ext fun Q => by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Derivation.coeFn_coe, conjDer_h,
      Derivation.add_apply, Derivation.smul_apply]

theorem exists_taylor (x : Fin 2 × ℕ) :
    ∃ k, Nonempty (TaylorForm (conjDer (jetDer k)).toLinearMap x) := by
  obtain ⟨b, m⟩ := x
  by_cases hb : b = 0
  · subst hb; exact ⟨(1, m), ⟨taylorF m⟩⟩
  · have : b = 1 := by omega
    subst this; exact ⟨(2, m), ⟨taylorH m⟩⟩

theorem comap_stable (k : Fin 3 × ℕ) (R : JetPoly)
    (hR : R ∈ baseNull.comap shiftDown.toLinearMap) :
    (conjDer (jetDer k)).toLinearMap R ∈ baseNull.comap shiftDown.toLinearMap := by
  rw [Submodule.mem_comap, AlgHom.toLinearMap_apply] at hR ⊢
  rw [Derivation.coeFn_coe, conjDer_apply, shiftDown_shiftUp]
  exact baseNull_stable k _ hR

theorem comap_constantCoeff (R : JetPoly) (hR : R ∈ baseNull.comap shiftDown.toLinearMap) :
    constantCoeff R = 0 := by
  rw [Submodule.mem_comap, AlgHom.toLinearMap_apply] at hR
  rw [← evalBase_shiftDown]
  have h := hR []
  rwa [word, List.map_nil, List.prod_nil, Module.End.one_apply] at h

theorem comap_eq_bot : baseNull.comap shiftDown.toLinearMap = ⊥ :=
  eq_bot_of_stable (fun k => (conjDer (jetDer k)).toLinearMap) exists_taylor _ comap_stable
    comap_constantCoeff

/-- **Cyclicity of evaluation at the base point** for the nonnegative-mode action on the jet
ring. -/
theorem jet_cyclic (Q : JetPoly)
    (hQ : ∀ l : List (Fin 3 × ℕ), evalBase (word jetRho l Q) = 0) : Q = 0 := by
  have hmem : shiftUp Q ∈ baseNull.comap shiftDown.toLinearMap := by
    rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, shiftDown_shiftUp]; exact hQ
  rw [comap_eq_bot, Submodule.mem_bot] at hmem
  rw [← shiftDown_shiftUp Q, hmem, map_zero]

end

end VOA.SymbolModel
