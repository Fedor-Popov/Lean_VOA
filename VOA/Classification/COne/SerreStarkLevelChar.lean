/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkLevelMult

/-!
# Serre–Stark S4-2: the character `ψ = χ·(t/·)` of an eigenform

For `4t ∣ N` (and `N` even), `v ↦ (t/v)` (Jacobi symbol) on units of `ZMod N` is a Dirichlet
character `kronChar N t` (periodicity `jacobiSym.mod_right'`). For a character `χ` mod `N`,
`eigenChar χ t = (χ · kronChar N t).primitiveCharacter` is the primitive character of conductor
`r ∣ N` with `ψ(v) = χ(v)(t/v)` for every `v` prime to `N` (`eigenChar_natCast`). This is the
character `ψ` of Serre–Stark's theta series `θ_{ψ,t}` attached to an eigenform supported on `t·□`.
-/

open Complex

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

variable {N t : ℕ}

theorem odd_val_of_isUnit (h2 : 2 ∣ N) {x : ZMod N} (hx : IsUnit x) : Odd x.val := by
  have hc : x.val.Coprime N := by
    have := ZMod.val_coe_unit_coprime hx.unit
    rwa [hx.unit_spec] at this
  rw [Nat.odd_iff]
  rcases Nat.mod_two_eq_zero_or_one x.val with h | h
  · exfalso
    have h2x : 2 ∣ x.val := Nat.dvd_of_mod_eq_zero h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1
      (Nat.Coprime.coprime_dvd_left h2x hc) h2
  · exact h

/-- `(t/b)` depends only on `b mod N` for odd `b`, when `4t ∣ N`. -/
theorem jacobiSym_mod_of_dvd (h4t : 4 * t ∣ N) {b : ℕ} (hb : Odd b) :
    jacobiSym (t : ℤ) (b % N) = jacobiSym (t : ℤ) b := by
  have h2 : 2 ∣ N := (Dvd.intro (2 * t) (by ring)).trans h4t
  have hbN : Odd (b % N) := by
    rw [Nat.odd_iff] at hb ⊢
    rw [← Nat.mod_mod_of_dvd b h2] at hb
    exact hb
  rw [jacobiSym.mod_right' t hbN, Nat.mod_mod_of_dvd b h4t, ← jacobiSym.mod_right' t hb]

open scoped Classical in
/-- The Kronecker-type character `v ↦ (t/v)` modulo `N` (`4t ∣ N`). -/
def kronChar (N t : ℕ) (h4t : 4 * t ∣ N) (hN1 : 1 < N) : DirichletCharacter ℂ N where
  toFun x := if IsUnit x then (jacobiSym (t : ℤ) x.val : ℂ) else 0
  map_one' := by
    haveI : Fact (1 < N) := ⟨hN1⟩
    simp [ZMod.val_one, jacobiSym.one_right]
  map_mul' x y := by
    have h2 : 2 ∣ N := (Dvd.intro (2 * t) (by ring)).trans h4t
    by_cases hx : IsUnit x
    · by_cases hy : IsUnit y
      · have hxy : IsUnit (x * y) := hx.mul hy
        simp only [hx, hy, hxy, if_true]
        have ox := odd_val_of_isUnit h2 hx
        have oy := odd_val_of_isUnit h2 hy
        rw [ZMod.val_mul, jacobiSym_mod_of_dvd h4t (ox.mul oy),
          jacobiSym.mul_right' _ (Nat.pos_of_ne_zero (fun h => by simp [h] at ox)).ne'
            (Nat.pos_of_ne_zero (fun h => by simp [h] at oy)).ne']
        push_cast; ring
      · have : ¬ IsUnit (x * y) := fun h => hy (IsUnit.mul_iff.1 h).2
        simp [hy, this]
    · have : ¬ IsUnit (x * y) := fun h => hx (IsUnit.mul_iff.1 h).1
      simp [hx, this]
  map_nonunit' a ha := by simp [ha]

open scoped Classical in
theorem kronChar_natCast (h4t : 4 * t ∣ N) (hN1 : 1 < N) {v : ℕ} (hv : v.Coprime N) :
    kronChar N t h4t hN1 (v : ZMod N) = (jacobiSym (t : ℤ) v : ℂ) := by
  have h2 : 2 ∣ N := (Dvd.intro (2 * t) (by ring)).trans h4t
  have hu : IsUnit (v : ZMod N) := (ZMod.isUnit_iff_coprime v N).2 hv
  have hvo : Odd v := by
    have := odd_val_of_isUnit h2 hu
    rw [ZMod.val_natCast] at this
    rw [Nat.odd_iff] at this ⊢
    rwa [Nat.mod_mod_of_dvd v h2] at this
  change (if IsUnit (v : ZMod N) then (jacobiSym (t : ℤ) (v : ZMod N).val : ℂ) else 0) = _
  rw [if_pos hu, ZMod.val_natCast, jacobiSym_mod_of_dvd h4t hvo]

/-- The level-`N` character `χ·(t/·)`. -/
def eigenCharN (χ : DirichletCharacter ℂ N) (h4t : 4 * t ∣ N) (hN1 : 1 < N) :
    DirichletCharacter ℂ N :=
  χ * kronChar N t h4t hN1

/-- The primitive character `ψ` attached to `χ` and `t`. -/
def eigenChar (χ : DirichletCharacter ℂ N) (h4t : 4 * t ∣ N) (hN1 : 1 < N) :
    DirichletCharacter ℂ (eigenCharN χ h4t hN1).conductor :=
  (eigenCharN χ h4t hN1).primitiveCharacter

theorem eigenChar_isPrimitive (χ : DirichletCharacter ℂ N) (h4t : 4 * t ∣ N) (hN1 : 1 < N) :
    (eigenChar χ h4t hN1).IsPrimitive :=
  DirichletCharacter.primitiveCharacter_isPrimitive _

theorem conductor_eigenChar_dvd (χ : DirichletCharacter ℂ N) (h4t : 4 * t ∣ N) (hN1 : 1 < N) :
    (eigenCharN χ h4t hN1).conductor ∣ N :=
  DirichletCharacter.conductor_dvd_level _

/-- `ψ(v) = χ(v)(t/v)` for `v` prime to `N`. -/
theorem eigenChar_natCast (χ : DirichletCharacter ℂ N) (h4t : 4 * t ∣ N) (hN1 : 1 < N) {v : ℕ}
    (hv : v.Coprime N) :
    eigenChar χ h4t hN1 (v : ZMod (eigenCharN χ h4t hN1).conductor) =
      χ (v : ZMod N) * (jacobiSym (t : ℤ) v : ℂ) := by
  set ε := eigenCharN χ h4t hN1
  have hd := DirichletCharacter.conductor_dvd_level ε
  have key := DirichletCharacter.changeLevel_eq_cast_of_dvd ε.primitiveCharacter hd
    (ZMod.unitOfCoprime v hv)
  rw [DirichletCharacter.changeLevel_primitiveCharacter, ZMod.coe_unitOfCoprime,
    ZMod.cast_natCast hd] at key
  rw [eigenChar, ← key]
  change (χ * kronChar N t h4t hN1) (v : ZMod N) = _
  rw [MulChar.mul_apply, kronChar_natCast h4t hN1 hv]

end SSHecke

end VOA.Classification.COne
