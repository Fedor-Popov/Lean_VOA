/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.LocalSystemBare
import VOA.Core.OPE

/-!
# The carrier action of a local field system

This is the second, still deliberately structural, phase of Li's local-system construction.
A system `L : LocalFieldSystem M` acts on its own carrier by its integer field products:
the mode of `a` at `n` sends `b` to `a₍ₙ₎b = Fld.prod n a b`.  We package that bilinear
action as a state-field map and prove the vacuum, creation, translation, and truncation laws
which follow directly from the definitions in `Core.LocalSystemBare`.

The last section isolates the generic implication from locality of two fields to a finite
mode-commutator formula.  Its only input is `Local a b`: the formula is derived through the
delta-derivative decomposition of the commutator and coefficient extraction.

This file does **not** assert that the induced state fields are mutually local, does not assume
a Jacobi identity, and does not package a `BarePreVA` or `PreVertexAlgebra`.
-/

namespace VOA

open Module (End)

universe u

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

namespace Fld

/-- The identity field has only its `(-1)`-st field product. -/
theorem prod_one_left_all (n : ℤ) (a : Fld M) :
    prod n one a = if n = -1 then a else 0 := by
  rcases lt_trichotomy n (-1) with hn | hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 :=
      ⟨(-n - 1).toNat, by omega⟩
    have hk : 0 < k := by omega
    rw [prod_one_left_negsucc hk]
    simp [show (-(k : ℤ) - 1) ≠ -1 by omega]
  · subst n
    rw [prod_one_left_neg_one]
    simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
    rw [prod_one_left_nat]
    simp

end Fld

namespace LocalFieldSystem

variable (L : LocalFieldSystem M)

/-- The identity field, regarded as the vacuum state in the carrier of `L`. -/
noncomputable def vacuum : L.carrier := ⟨Fld.one, L.one_mem⟩

@[simp] theorem vacuum_val : (vacuum L : Fld M) = Fld.one := rfl

/-- The `n`-th product as a bilinear action on the carrier of a local field system. -/
noncomputable def modeAction (n : ℤ) : L.carrier →ₗ[ℂ] End ℂ L.carrier where
  toFun a :=
    { toFun := fun b => ⟨Fld.prod n a.1 b.1, L.prod_mem n a.2 b.2⟩
      map_add' := fun b c => by
        apply Subtype.ext
        change Fld.prod n a.1 (b.1 + c.1) = Fld.prod n a.1 b.1 + Fld.prod n a.1 c.1
        exact Fld.prod_add_right n a.1 b.1 c.1
      map_smul' := fun d b => by
        apply Subtype.ext
        change Fld.prod n a.1 (d • b.1) = d • Fld.prod n a.1 b.1
        exact Fld.prod_smul_right n d a.1 b.1 }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change Fld.prod n (a.1 + b.1) c.1 = Fld.prod n a.1 c.1 + Fld.prod n b.1 c.1
    exact Fld.prod_add_left n a.1 b.1 c.1
  map_smul' d a := by
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    change Fld.prod n (d • a.1) b.1 = d • Fld.prod n a.1 b.1
    exact Fld.prod_smul_left n d a.1 b.1

@[simp] theorem modeAction_apply (n : ℤ) (a b : L.carrier) :
    (modeAction L n a b : Fld M) = Fld.prod n a.1 b.1 := rfl

/-- The state-field correspondence induced by the product action.  Its coefficient at `q`
is the mode with index `-q-1`. -/
noncomputable def stateField : L.carrier →ₗ[ℂ] FormalDist (End ℂ L.carrier) where
  toFun a := fun q => modeAction L (-q - 1) a
  map_add' a b := by
    funext q
    exact LinearMap.map_add (modeAction L (-q - 1)) a b
  map_smul' d a := by
    funext q
    exact LinearMap.map_smul (modeAction L (-q - 1)) d a

@[simp] theorem stateField_apply (a : L.carrier) (q : ℤ) :
    stateField L a q = modeAction L (-q - 1) a := rfl

@[simp] theorem mode_stateField (a b : L.carrier) (n : ℤ) :
    mode (stateField L a) n b = modeAction L n a b := by
  rw [mode_apply, stateField_apply]
  rw [show -(-n - 1) - 1 = n by ring]

/-- The induced state field is lower truncated on every carrier vector. -/
theorem stateField_isField (a : L.carrier) : IsField (stateField L a) := by
  intro b
  obtain ⟨N, hN⟩ := L.prod_eventually_zero a.2 b.2
  refine ⟨-N, fun q hq => ?_⟩
  apply Subtype.ext
  change Fld.prod (-q - 1) a.1 b.1 = 0
  exact hN (-q - 1) (by omega)

/-- The induced state field, retained together with its lower-truncation witness. -/
noncomputable def stateFld (a : L.carrier) : Fld L.carrier :=
  ⟨stateField L a, stateField_isField L a⟩

@[simp] theorem stateFld_val (a : L.carrier) : (stateFld L a).1 = stateField L a := rfl

/-- The vacuum state acts by the identity mode at `-1` and by zero at every other mode. -/
@[simp] theorem modeAction_vacuum_left (n : ℤ) (b : L.carrier) :
    modeAction L n (vacuum L) b = if n = -1 then b else 0 := by
  apply Subtype.ext
  change Fld.prod n Fld.one b.1 = (if n = -1 then b else 0 : L.carrier).1
  rw [Fld.prod_one_left_all]
  by_cases hn : n = -1 <;> simp [hn]

/-- The induced field of the vacuum is the identity field. -/
@[simp] theorem stateField_vacuum :
    stateField L (vacuum L) = (idField : FormalDist (End ℂ L.carrier)) := by
  funext q
  apply LinearMap.ext
  intro b
  rw [stateField_apply]
  by_cases hq : q = 0
  · subst q
    simp [modeAction_vacuum_left]
  · have hn : -q - 1 ≠ -1 := by omega
    rw [modeAction_vacuum_left, if_neg hn, idField_apply, if_neg hq]
    rfl

/-- Creation at mode `-1`. -/
@[simp] theorem creation_neg_one (a : L.carrier) :
    modeAction L (-1) a (vacuum L) = a := by
  apply Subtype.ext
  exact Fld.prod_one_right_neg_one a.1

/-- Nonnegative modes annihilate the vacuum. -/
theorem creation_nonneg (a : L.carrier) {n : ℤ} (hn : 0 ≤ n) :
    modeAction L n a (vacuum L) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
  apply Subtype.ext
  exact Fld.prod_one_right_nat k a.1

/-- Every negative vacuum coefficient is the divided derivative of the original field. -/
theorem creation_deriv (a : L.carrier) (k : ℕ) :
    (modeAction L (-(k : ℤ) - 1) a (vacuum L) : Fld M).1 =
      (k.factorial : ℂ)⁻¹ • (VOA.deriv^[k]) a.1.1 := by
  exact Fld.prod_one_right_negsucc k a.1

/-- The translation endomorphism supplied by the `(-2)`-nd vacuum product. -/
noncomputable def translation : End ℂ L.carrier where
  toFun a := modeAction L (-2) a (vacuum L)
  map_add' a b := by
    exact congrArg (fun f : End ℂ L.carrier => f (vacuum L))
      (LinearMap.map_add (modeAction L (-2)) a b)
  map_smul' d a := by
    exact congrArg (fun f : End ℂ L.carrier => f (vacuum L))
      (LinearMap.map_smul (modeAction L (-2)) d a)

@[simp] theorem translation_apply (a : L.carrier) :
    translation L a = modeAction L (-2) a (vacuum L) := rfl

/-- On the underlying weak vertex operator, local-system translation is the formal derivative. -/
theorem translation_val (a : L.carrier) :
    (translation L a : Fld M).1 = VOA.deriv a.1.1 := by
  simpa using creation_deriv L a 1

/-- Truncation in mode language for the induced product action. -/
theorem modeAction_eventually_zero (a b : L.carrier) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → modeAction L n a b = 0 := by
  obtain ⟨N, hN⟩ := L.prod_eventually_zero a.2 b.2
  exact ⟨N, fun n hn => by
    apply Subtype.ext
    exact hN n hn⟩

end LocalFieldSystem

/-! ## Locality implies the structural mode commutator -/

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- Locality alone gives a finite delta-derivative expansion of a field commutator. -/
theorem bracket_deltaSum_of_local {a b : FormalDist (End ℂ E)} (h : Local a b) :
    ∃ (N : ℕ) (c : Fin N → FormalDist (End ℂ E)),
      bracketDist a b = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, (local_iff_deltaSum _ N).mp hN⟩

/-- Coefficient extraction from a finite delta-derivative OPE, with no vertex-algebra shell. -/
theorem mode_bracket_ope_fields {a b : FormalDist (End ℂ E)} {N : ℕ}
    {c : Fin N → FormalDist (End ℂ E)}
    (h : bracketDist a b = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j)) (m n : ℤ) :
    ⁅mode a m, mode b n⁆ = ∑ j : Fin N,
      (∏ i ∈ Finset.range (j : ℕ), (m - (i : ℤ))) •
        mode (c j) (m + n - ((j : ℕ) : ℤ)) := by
  have hcomm : ⁅mode a m, mode b n⁆ = bracketDist a b (-m - 1) (-n - 1) := by
    simp only [bracketDist_apply, LieRing.of_associative_ring_bracket, mode_apply]
  rw [hcomm, h, formalDist₂_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deltaDeriv_apply,
    show (∏ i ∈ Finset.range (j : ℕ), (-(-m - 1) - 1 - (i : ℤ))) =
        ∏ i ∈ Finset.range (j : ℕ), (m - (i : ℤ)) from
      Finset.prod_congr rfl fun i _ => by ring]
  congr 1
  rw [mode_apply]
  congr 1
  ring

/-- The finite structural commutator formula derived from the single hypothesis `Local a b`. -/
theorem mode_commutator_of_local {a b : FormalDist (End ℂ E)} (h : Local a b) (m n : ℤ) :
    ∃ (N : ℕ) (c : Fin N → FormalDist (End ℂ E)),
      bracketDist a b = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j) ∧
      ⁅mode a m, mode b n⁆ = ∑ j : Fin N,
        (∏ i ∈ Finset.range (j : ℕ), (m - (i : ℤ))) •
          mode (c j) (m + n - ((j : ℕ) : ℤ)) := by
  obtain ⟨N, c, hc⟩ := bracket_deltaSum_of_local h
  exact ⟨N, c, hc, mode_bracket_ope_fields hc m n⟩

end VOA
