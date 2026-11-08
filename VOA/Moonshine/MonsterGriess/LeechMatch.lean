/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LeechLatticeVOA
import VOA.Moonshine.MonsterGriess.Short
import VOA.LatticesAndCodes.Leech.RepCount

/-!
# Our Leech lattice is Axiom's Leech lattice, up to the coordinate permutation `π`
(Aut(V♮) campaign, step 5, first brick; `Notes/MONSTER_AUT_PLAN.md`,
`Notes/monster_aut/STEP5_PHASE_A.md`)

Two models of the Leech lattice live in this repository, both in the `√8`-scaled integer
coordinates of Conway's construction with the form `x·y/8`:

* ours, `leech = ofEbeling Leech.lattice` (`VOA/LatticesAndCodes/Leech/Defs.lean`), with carrier
  `Leech.carrier = 2A ∪ (u + 2A) ⊆ ℤ²⁴` built from `Code.golay`, the row space of `[I₁₂ | B]` with
  the Paley matrix `B = golayB`;
* Axiom's, `MonsterGriess.codeLattice Code.C` (`VOA/Moonshine/MonsterGriess/Lattice.lean`), built
  from the MOG/hexacode Golay code `Code.C` (Axiom coordinate `r + 4j` = MOG row `r`, column `j`).

They differ only by a relabelling of the 24 coordinates.  The permutation, found numerically by
octad backtracking (`Notes/monster_aut/step5_phase_a.py`), is

`π = [0,1,2,3,4,8,13,15,23,7,20,18,19,10,17,14,11,21,5,16,22,6,12,9]`

(our coordinate `i` ↦ Axiom coordinate `π i`).  A vector `x` is transported to `x ∘ π⁻¹`
(`permLin`), so `(permLin σ x) (σ i) = x i`.

## Main results
* `piPerm : Equiv.Perm (Fin 24)` — `π`, with its inverse given explicitly (`piPerm_apply`,
  `piPerm_symm_apply`).
* ⭐ `golayRow_perm_mem_C` — the `12` rows of `[I₁₂ | B]`, permuted by `π`, lie in `Code.C`
  (`decide +kernel`).
* ⭐ `golay_map_le_C`, `golay_map_eq_C` — `π` maps `Code.golay` into, hence (dimension `12` on both
  sides) onto, `Code.C`; `perm_mem_C_iff`.
* ⭐ `golayEquivC : Code.golay ≃ₗ[ZMod 2] Code.C`, `card_golay`, `card_C` (`= 4096`).
* ⭐ `mem_codeLattice_golay_iff` — our carrier *is* `codeLattice Code.golay`: Axiom's congruence
  description applied to our code.
* `perm_mem_codeLattice_iff` — `codeLattice` is equivariant under coordinate permutations.
* ⭐ `perm_mem_codeLattice_C_iff` — `permLin π x ∈ codeLattice Code.C ↔ x ∈ Leech.carrier`.
* ⭐ `leechEquiv : leech.carrier ≃+ ↥(codeLatticeSubgroup Code.allOnes_mem_C)`, acting by
  `x ↦ x ∘ π⁻¹` (`leechEquiv_apply`).  **No rescaling:** both models use the same `√8`-scaled
  integer coordinates, so `leechEquiv` preserves the plain dot product (`leechEquiv_dotProduct`:
  `(leechEquiv x)·(leechEquiv y) = 8·⟪x,y⟫`) and carries our form to Axiom's `codeForm`
  (`codeForm_leechEquiv`: `codeForm (leechEquiv x) (leechEquiv y) = ⟪x,y⟫`, exactly).
* ⭐ `leechEquiv_mem_minVecs_iff`, `minEquiv` — minimal vectors (norm `4`) go to Axiom's `minVecs`,
  bijectively.
* ⭐ `classOf_eq_iff` — for `u, v ∈ minVecs`: `classOf u = classOf v ↔ u = v ∨ u = -v` (two minimal
  vectors are congruent mod `2Λ` iff equal up to sign), using the minimal norm `4` of our lattice
  (`four_le_form`).
* `isShortCoord_iff`, `exists_pm_of_shortIdx` — `IsShortCoord p` holds iff `phi0 p` is the class of
  one of *our* minimal vectors (moved by `π`), and then the minimal vectors in that class are
  exactly a pair `±α₀`.  So every `c : ShortIdx` determines a unique `±`-class of our minimal
  vectors.

## Status
All declarations `sorry`-free; no `native_decide` (the concrete Golay facts use
`decide +kernel`).  The converse direction of the `ShortIdx` matching (every `±`-class of our
minimal vectors is hit by exactly one `c : ShortIdx`) needs `Function.Bijective SpinLattice.phi0`,
the source's `phi0Equiv`, which is not ported (it rests on the theta-cocycle identities
`lamT_add`, `thetaD_add`); it is recorded below as the open statement, not assumed.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.MonsterGriess.LeechMatch

open scoped Matrix
open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.SpinLattice

/-! ## §1  The permutation `π` -/

/-- `π` as a function: our coordinate `i` ↦ Axiom coordinate `π i`. -/
def piFun : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 4, 8, 13, 15, 23, 7, 20, 18, 19, 10, 17, 14, 11, 21, 5, 16, 22, 6, 12, 9]

/-- The inverse of `π`, written out. -/
def piInvFun : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 4, 18, 21, 9, 5, 23, 13, 16, 22, 6, 15, 7, 19, 14, 11, 12, 10, 17, 20, 8]

theorem piInvFun_piFun : ∀ i, piInvFun (piFun i) = i := by decide

theorem piFun_piInvFun : ∀ i, piFun (piInvFun i) = i := by decide

/-- ⭐ **The coordinate permutation `π`** carrying `Code.golay` onto Axiom's `Code.C`. -/
def piPerm : Equiv.Perm (Fin 24) := ⟨piFun, piInvFun, piInvFun_piFun, piFun_piInvFun⟩

@[simp] theorem piPerm_apply (i : Fin 24) : piPerm i = piFun i := rfl

@[simp] theorem piPerm_symm_apply (i : Fin 24) : piPerm.symm i = piInvFun i := rfl

/-! ## §2  Transport of coordinates -/

/-- Coordinate transport along `σ`: `permLin R σ x = x ∘ σ⁻¹`, so `(permLin R σ x) (σ i) = x i`. -/
def permLin (R : Type*) [Semiring R] (σ : Equiv.Perm (Fin 24)) :
    (Fin 24 → R) ≃ₗ[R] (Fin 24 → R) where
  toFun x j := x (σ.symm j)
  invFun y i := y (σ i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := funext fun i => by simp
  right_inv y := funext fun j => by simp

theorem permLin_apply {R : Type*} [Semiring R] (σ : Equiv.Perm (Fin 24)) (x : Fin 24 → R)
    (j : Fin 24) : permLin R σ x j = x (σ.symm j) := rfl

theorem permLin_symm_apply {R : Type*} [Semiring R] (σ : Equiv.Perm (Fin 24))
    (y : Fin 24 → R) (i : Fin 24) : (permLin R σ).symm y i = y (σ i) := rfl

theorem permLin_apply_self {R : Type*} [Semiring R] (σ : Equiv.Perm (Fin 24)) (x : Fin 24 → R)
    (i : Fin 24) : permLin R σ x (σ i) = x i := by
  rw [permLin_apply, Equiv.symm_apply_apply]

theorem sum_permLin {R : Type*} [Semiring R] (σ : Equiv.Perm (Fin 24)) (x : Fin 24 → R) :
    ∑ j, permLin R σ x j = ∑ i, x i :=
  Equiv.sum_comp σ.symm x

theorem dotProduct_permLin {R : Type*} [CommSemiring R] (σ : Equiv.Perm (Fin 24))
    (x y : Fin 24 → R) : permLin R σ x ⬝ᵥ permLin R σ y = x ⬝ᵥ y :=
  Equiv.sum_comp σ.symm fun i => x i * y i

/-! ## §3  The Golay codes -/

/-- ⭐ **The `12` generator rows of `[I₁₂ | B]`, moved by `π`, are words of Axiom's code `C`.**
A kernel evaluation of the membership test `Code.mem_C_iff` (hexacode projection and column
parities) on `12` concrete words. -/
theorem golayRow_perm_mem_C : ∀ i : Fin 12,
    (fun j => _root_.Code.golayEnc (Pi.single i 1) (piPerm.symm j)) ∈ Code.C := by
  decide +kernel

/-- ⭐ **`π` maps our Golay code into Axiom's.** -/
theorem golay_map_le_C :
    _root_.Code.golay.map (permLin (ZMod 2) piPerm : (Fin 24 → ZMod 2) →ₗ[ZMod 2] _) ≤ Code.C := by
  rw [_root_.Code.golay_eq_span, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact golayRow_perm_mem_C i

/-- Axiom's code has dimension `12` (`basisC`). -/
theorem finrank_C : Module.finrank (ZMod 2) Code.C = 12 := by
  rw [Module.finrank_eq_card_basis Code.basisC, Fintype.card_fin]

/-- ⭐ **`π` maps our Golay code onto Axiom's**: both have dimension `12`. -/
theorem golay_map_eq_C :
    _root_.Code.golay.map (permLin (ZMod 2) piPerm : (Fin 24 → ZMod 2) →ₗ[ZMod 2] _) = Code.C :=
  Submodule.eq_of_le_of_finrank_eq golay_map_le_C
    (by rw [LinearEquiv.finrank_map_eq, finrank_C]; exact _root_.Code.golay_rank)

/-- A word `x` lies in our code iff `x ∘ π⁻¹` lies in Axiom's. -/
theorem perm_mem_C_iff (x : Fin 24 → ZMod 2) :
    permLin (ZMod 2) piPerm x ∈ Code.C ↔ x ∈ _root_.Code.golay := by
  rw [← golay_map_eq_C, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

/-- ⭐ **The code isomorphism** `Code.golay ≃ Code.C`, `c ↦ c ∘ π⁻¹`. -/
noncomputable def golayEquivC : _root_.Code.golay ≃ₗ[ZMod 2] Code.C :=
  ((permLin (ZMod 2) piPerm).submoduleMap _root_.Code.golay).trans
    (LinearEquiv.ofEq _ _ golay_map_eq_C)

theorem golayEquivC_apply (c : _root_.Code.golay) (j : Fin 24) :
    (golayEquivC c : Fin 24 → ZMod 2) j = (c : Fin 24 → ZMod 2) (piPerm.symm j) := rfl

/-- Axiom's code has `2¹² = 4096` words. -/
theorem card_C : Nat.card Code.C = 4096 := by
  rw [Nat.card_congr Code.basisC.equivFun.toEquiv]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- Our code has `4096` words, and `golayEquivC` is a bijection between the two word sets. -/
theorem card_golay : Nat.card _root_.Code.golay = 4096 := by
  rw [Nat.card_congr golayEquivC.toEquiv, card_C]

/-! ## §4  Our Leech carrier is `codeLattice Code.golay` -/

theorem uVec_emod_four (i : Fin 24) : Leech.uVec i % 4 = 1 := by
  by_cases h : i = 0 <;> simp [Leech.uVec, h]

/-- The even half: `y ∈ 2A` iff `y ≡ 2d (mod 4)` for a codeword `d` and `Σ y ≡ 0 (mod 8)`. -/
theorem mem_subA2_iff (y : Fin 24 → ℤ) :
    y ∈ Leech.subA2 ↔ ∃ d ∈ _root_.Code.golay,
      (∀ i, y i ≡ 0 + 2 * bitLift (d i) [ZMOD 4]) ∧ ∑ i, y i ≡ 4 * 0 [ZMOD 8] := by
  constructor
  · intro hy
    obtain ⟨a, ⟨ha, ha4⟩, rfl⟩ := Leech.mem_subA2.1 hy
    refine ⟨reduceMod 2 24 a, ha, fun i => ?_, ?_⟩
    · rw [reduceMod_apply, bitLift_intCast]
      simp only [Pi.smul_apply, smul_eq_mul]
      unfold Int.ModEq
      omega
    · have hs : ∑ i, ((2 : ℤ) • a) i = 2 * ∑ i, a i := by
        simp [Finset.mul_sum]
      rw [hs]
      obtain ⟨k, hk⟩ := ha4
      unfold Int.ModEq
      omega
  · rintro ⟨d, hd, hc, hs⟩
    have hev : ∀ i, 2 ∣ y i := fun i => by
      have := hc i
      unfold Int.ModEq at this
      omega
    set a : Fin 24 → ℤ := fun i => y i / 2 with ha_def
    have hya : (2 : ℤ) • a = y := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, ha_def]
      exact Int.mul_ediv_cancel' (hev i)
    have hred : reduceMod 2 24 a = d := by
      funext i
      rw [reduceMod_apply, ← bitLift_cast (d i), ZMod.intCast_eq_intCast_iff']
      have h1 := hc i
      have h2 := bitLift_zero_or_one (d i)
      have h3 := hev i
      unfold Int.ModEq at h1
      simp only [ha_def]
      push_cast
      omega
    refine Leech.mem_subA2.2 ⟨a, ⟨?_, ?_⟩, hya⟩
    · rw [Leech.mem_preG, hred]
      exact hd
    · have h2 : ∑ i, y i = 2 * ∑ i, a i := by
        rw [← hya]
        simp [Finset.mul_sum]
      unfold Int.ModEq at hs
      rw [h2] at hs
      exact ⟨(∑ i, a i) / 4, by omega⟩

/-- ⭐ **Our Leech carrier is Axiom's `codeLattice`, applied to our Golay code.** -/
theorem mem_codeLattice_golay_iff (x : Fin 24 → ℤ) :
    x ∈ codeLattice _root_.Code.golay ↔ x ∈ Leech.carrier := by
  rw [Leech.mem_carrier]
  constructor
  · rintro ⟨m, hm, d, hd, hc, hs⟩
    rcases hm with rfl | rfl
    · exact Or.inl ((mem_subA2_iff x).2 ⟨d, hd, hc, hs⟩)
    · refine Or.inr ((mem_subA2_iff _).2 ⟨d, hd, fun i => ?_, ?_⟩)
      · have h1 := hc i
        have h2 := uVec_emod_four i
        simp only [Pi.sub_apply]
        unfold Int.ModEq at h1 ⊢
        omega
      · have h1 : ∑ i, (x - Leech.uVec) i = ∑ i, x i - 28 := by
          rw [← Leech.sum_uVec, ← Finset.sum_sub_distrib]
          rfl
        rw [h1]
        unfold Int.ModEq at hs ⊢
        omega
  · rintro (hx | hx)
    · obtain ⟨d, hd, hc, hs⟩ := (mem_subA2_iff x).1 hx
      exact ⟨0, Or.inl rfl, d, hd, hc, hs⟩
    · obtain ⟨d, hd, hc, hs⟩ := (mem_subA2_iff _).1 hx
      refine ⟨1, Or.inr rfl, d, hd, fun i => ?_, ?_⟩
      · have h1 := hc i
        have h2 := uVec_emod_four i
        simp only [Pi.sub_apply] at h1
        unfold Int.ModEq at h1 ⊢
        omega
      · have h1 : ∑ i, (x - Leech.uVec) i = ∑ i, x i - 28 := by
          rw [← Leech.sum_uVec, ← Finset.sum_sub_distrib]
          rfl
        rw [h1] at hs
        unfold Int.ModEq at hs ⊢
        omega

/-- `codeLattice` is equivariant under coordinate permutations. -/
theorem perm_mem_codeLattice_iff (D : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (σ : Equiv.Perm (Fin 24)) (u : Fin 24 → ℤ) :
    permLin ℤ σ u ∈ codeLattice (D.map (permLin (ZMod 2) σ : (Fin 24 → ZMod 2) →ₗ[ZMod 2] _))
      ↔ u ∈ codeLattice D := by
  constructor
  · rintro ⟨m, hm, d', hd', hc, hs⟩
    rw [Submodule.mem_map_equiv] at hd'
    refine ⟨m, hm, _, hd', fun i => ?_, ?_⟩
    · have h := hc (σ i)
      rwa [permLin_apply_self] at h
    · rwa [sum_permLin] at hs
  · rintro ⟨m, hm, d, hd, hc, hs⟩
    refine ⟨m, hm, _, Submodule.mem_map_of_mem hd, fun j => ?_, ?_⟩
    · exact hc (σ.symm j)
    · rwa [sum_permLin]

/-- ⭐ **`π` carries our Leech carrier onto Axiom's `codeLattice C`.** -/
theorem perm_mem_codeLattice_C_iff (x : Fin 24 → ℤ) :
    permLin ℤ piPerm x ∈ codeLattice Code.C ↔ x ∈ Leech.carrier := by
  rw [← golay_map_eq_C, perm_mem_codeLattice_iff, mem_codeLattice_golay_iff]

/-! ## §5  The additive equivalence and the forms -/

/-- The equivalence on the `ℤ²⁴` level: `x ↦ x ∘ π⁻¹`. -/
def carrierEquiv : ↥Leech.carrier ≃+ ↥(codeLatticeSubgroup Code.allOnes_mem_C) where
  toFun x := ⟨permLin ℤ piPerm (x : Fin 24 → ℤ), (perm_mem_codeLattice_C_iff x).2 x.2⟩
  invFun y := ⟨(permLin ℤ piPerm).symm (y : Fin 24 → ℤ),
    (perm_mem_codeLattice_C_iff _).1 (by rw [LinearEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((permLin ℤ piPerm).symm_apply_apply (x : Fin 24 → ℤ))
  right_inv y := Subtype.ext ((permLin ℤ piPerm).apply_symm_apply (y : Fin 24 → ℤ))
  map_add' x y := Subtype.ext (map_add (permLin ℤ piPerm) (x : Fin 24 → ℤ) y)

/-- The integer coordinates of a vector of `leech` (whose carrier is `↥Leech.carrier`, by
definition: `leech = ofEbeling Leech.lattice`, `Leech.lattice = dotLattice 8 Leech.carrier _`). -/
abbrev vec (x : leech.carrier) : Fin 24 → ℤ := Subtype.val (p := (· ∈ Leech.carrier)) x

/-- ⭐ **Our Leech lattice is Axiom's**: `leech.carrier ≃+ ↥(codeLatticeSubgroup allOnes_mem_C)`,
`x ↦ x ∘ π⁻¹`. -/
def leechEquiv : leech.carrier ≃+ ↥(codeLatticeSubgroup Code.allOnes_mem_C) := carrierEquiv

theorem leechEquiv_apply (x : leech.carrier) (j : Fin 24) :
    (leechEquiv x : Fin 24 → ℤ) j = vec x (piPerm.symm j) := rfl

theorem leechEquiv_symm_apply (y : ↥(codeLatticeSubgroup Code.allOnes_mem_C)) (i : Fin 24) :
    vec (leechEquiv.symm y) i = (y : Fin 24 → ℤ) (piPerm i) := rfl

/-- Our form in coordinates: `8·⟪x,y⟫ = x·y`. -/
theorem eight_mul_form (x y : leech.carrier) :
    8 * leech.form x y = vec x ⬝ᵥ vec y :=
  Leech.eight_mul_lattice_bilin x y

/-- ⭐ **`leechEquiv` is an isometry of the integer coordinates** (no rescaling):
`(leechEquiv x)·(leechEquiv y) = x·y = 8·⟪x,y⟫`. -/
theorem leechEquiv_dotProduct (x y : leech.carrier) :
    (leechEquiv x : Fin 24 → ℤ) ⬝ᵥ (leechEquiv y : Fin 24 → ℤ) = 8 * leech.form x y := by
  rw [eight_mul_form]
  exact dotProduct_permLin piPerm _ _

/-- The integer vector of `y`, read in `ℚ²⁴` (the argument type of Axiom's `codeForm`). -/
def toQ (y : Fin 24 → ℤ) : Fin 24 → ℚ := fun i => (y i : ℚ)

theorem codeForm_toQ (u v : Fin 24 → ℤ) : codeForm (toQ u) (toQ v) = ((u ⬝ᵥ v : ℤ) : ℚ) / 8 := by
  simp [codeForm, toQ, dotProduct]

/-- ⭐ **`leechEquiv` carries our form to Axiom's `codeForm`, with scale factor `1`**:
`codeForm (leechEquiv x) (leechEquiv y) = ⟪x,y⟫`. -/
theorem codeForm_leechEquiv (x y : leech.carrier) :
    codeForm (toQ (leechEquiv x)) (toQ (leechEquiv y)) = (leech.form x y : ℚ) := by
  rw [codeForm_toQ, leechEquiv_dotProduct]
  push_cast
  ring

/-! ## §6  Minimal vectors -/

/-- ⭐ **Minimal vectors go to minimal vectors**: `leechEquiv α ∈ minVecs ↔ ⟪α,α⟫ = 4`. -/
theorem leechEquiv_mem_minVecs_iff (α : leech.carrier) :
    (leechEquiv α : Fin 24 → ℤ) ∈ minVecs ↔ leech.form α α = 4 := by
  have h := codeForm_leechEquiv α α
  refine ⟨fun ⟨_, h4⟩ => ?_, fun h4 => ⟨(leechEquiv α).2, ?_⟩⟩
  · change codeForm (toQ (leechEquiv α)) (toQ (leechEquiv α)) = 4 at h4
    rw [h] at h4
    exact_mod_cast h4
  · change codeForm (toQ (leechEquiv α)) (toQ (leechEquiv α)) = 4
    rw [h, h4]
    norm_num

theorem mem_minVecs_iff (u : Fin 24 → ℤ) :
    u ∈ minVecs ↔ ∃ h : u ∈ codeLattice Code.C,
      leech.form (leechEquiv.symm ⟨u, h⟩) (leechEquiv.symm ⟨u, h⟩) = 4 := by
  constructor
  · intro hu
    refine ⟨hu.1, ?_⟩
    rw [← leechEquiv_mem_minVecs_iff, AddEquiv.apply_symm_apply]
    exact hu
  · rintro ⟨h, h4⟩
    rw [← leechEquiv_mem_minVecs_iff, AddEquiv.apply_symm_apply] at h4
    exact h4

/-- ⭐ **The minimal vectors of the two models correspond bijectively.** -/
noncomputable def minEquiv : {α : leech.carrier // leech.form α α = 4} ≃ minVecs where
  toFun α := ⟨leechEquiv α.1, (leechEquiv_mem_minVecs_iff α.1).2 α.2⟩
  invFun u := ⟨leechEquiv.symm ⟨u.1, u.2.1⟩, by
    rw [← leechEquiv_mem_minVecs_iff, AddEquiv.apply_symm_apply]
    exact u.2⟩
  left_inv α := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)

theorem minEquiv_apply (α : {α : leech.carrier // leech.form α α = 4}) :
    (minEquiv α : Fin 24 → ℤ) = leechEquiv α.1 := rfl

/-! ## §7  `±`-classes of minimal vectors and `ShortIdx` -/

/-- Nonzero Leech vectors have norm at least `4` (even, positive definite, no roots). -/
theorem four_le_form (w : leech.carrier) (hw : w ≠ 0) : 4 ≤ leech.form w w := by
  have h1 := Leech.lattice_isEven w
  have h2 := Leech.lattice_isPosDef w hw
  have h3 := Leech.lattice_no_roots w
  simp only [_root_.IntegralLattice.normSq_def] at h1 h2 h3
  change 4 ≤ Leech.lattice.bilin w w
  obtain ⟨k, hk⟩ := h1
  omega

/-- Nonzero vectors of Axiom's lattice have `u·u ≥ 32`. -/
theorem thirtytwo_le_dot (w : ↥(codeLatticeSubgroup Code.allOnes_mem_C)) (hw : w ≠ 0) :
    32 ≤ (w : Fin 24 → ℤ) ⬝ᵥ (w : Fin 24 → ℤ) := by
  have hw' : leechEquiv.symm w ≠ 0 := by
    intro h
    exact hw (by rw [← AddEquiv.apply_symm_apply leechEquiv w, h, map_zero])
  have h4 := four_le_form _ hw'
  have h := leechEquiv_dotProduct (leechEquiv.symm w) (leechEquiv.symm w)
  rw [AddEquiv.apply_symm_apply] at h
  omega

theorem dot_self_of_mem_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : u ⬝ᵥ u = 32 := by
  have h := hu.2
  change codeForm (toQ u) (toQ u) = 4 at h
  rw [codeForm_toQ] at h
  have h' : ((u ⬝ᵥ u : ℤ) : ℚ) = 32 := by linarith
  exact_mod_cast h'

theorem classOf_of_mem {u : Fin 24 → ℤ} (hu : u ∈ codeLattice Code.C) :
    classOf u = Submodule.Quotient.mk (⟨u, hu⟩ : codeLatticeSubgroup Code.allOnes_mem_C) := by
  rw [classOf, dif_pos hu]

/-- ⭐ **Two minimal vectors are congruent mod `2Λ` iff they agree up to sign.** -/
theorem classOf_eq_iff {u v : Fin 24 → ℤ} (hu : u ∈ minVecs) (hv : v ∈ minVecs) :
    classOf u = classOf v ↔ u = v ∨ u = -v := by
  rw [classOf_of_mem hu.1, classOf_of_mem hv.1, Submodule.Quotient.eq, mem_two_range_iff]
  constructor
  · rintro ⟨w, hw⟩
    have hw' : (2 : ℤ) • (w : Fin 24 → ℤ) = u - v := hw
    by_cases h0 : w = 0
    · left
      rw [h0] at hw'
      simp only [ZeroMemClass.coe_zero, smul_zero] at hw'
      exact (sub_eq_zero.1 hw'.symm)
    · right
      have h32 := thirtytwo_le_dot w h0
      have huu := dot_self_of_mem_minVecs hu
      have hvv := dot_self_of_mem_minVecs hv
      have hdiff : (u - v) ⬝ᵥ (u - v) = 4 * ((w : Fin 24 → ℤ) ⬝ᵥ (w : Fin 24 → ℤ)) := by
        rw [← hw', smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        ring
      have hpar : (u + v) ⬝ᵥ (u + v) + (u - v) ⬝ᵥ (u - v) = 2 * (u ⬝ᵥ u) + 2 * (v ⬝ᵥ v) := by
        simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub]
        rw [dotProduct_comm v u]
        ring
      have hnn : 0 ≤ (u + v) ⬝ᵥ (u + v) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
      have hz : (u + v) ⬝ᵥ (u + v) = 0 := by omega
      rw [dotProduct_self_eq_zero] at hz
      exact eq_neg_of_add_eq_zero_left hz
  · rintro (h | h)
    · subst h
      exact ⟨0, by simp⟩
    · refine ⟨⟨u, hu.1⟩, ?_⟩
      have hv' : v = -u := by rw [h, neg_neg]
      change (2 : ℤ) • u = u - v
      rw [hv', sub_neg_eq_add, two_smul]

/-- `IsShortCoord p` iff `phi0 p` is the class of one of *our* minimal vectors, moved by `π`. -/
theorem isShortCoord_iff (p : Code.C × Spin.Cocode) :
    IsShortCoord p ↔ ∃ α : leech.carrier, leech.form α α = 4 ∧
      classOf (leechEquiv α : Fin 24 → ℤ) = phi0 p := by
  constructor
  · rintro ⟨u, hu, hcl⟩
    obtain ⟨α, hα⟩ := minEquiv.surjective ⟨u, hu⟩
    refine ⟨α.1, α.2, ?_⟩
    have : (leechEquiv α.1 : Fin 24 → ℤ) = u := congrArg Subtype.val hα
    rw [this, hcl]
  · rintro ⟨α, hα, hcl⟩
    exact ⟨_, (leechEquiv_mem_minVecs_iff α).2 hα, hcl⟩

/-- ⭐ **Every `c : ShortIdx` is a `±`-pair of our minimal vectors**: there is `α₀` of norm `4`
such that the minimal vectors `α` of our lattice whose class (after `π`) is `phi0 c` are exactly
`α₀` and `-α₀`. -/
theorem exists_pm_of_shortIdx (c : ShortIdx) :
    ∃ α₀ : leech.carrier, leech.form α₀ α₀ = 4 ∧
      ∀ α : leech.carrier, (leech.form α α = 4 ∧
        classOf (leechEquiv α : Fin 24 → ℤ) = phi0 c.1) ↔ (α = α₀ ∨ α = -α₀) := by
  obtain ⟨α₀, hα₀, hcl₀⟩ := (isShortCoord_iff c.1).1 c.2
  have hm₀ := (leechEquiv_mem_minVecs_iff α₀).2 hα₀
  refine ⟨α₀, hα₀, fun α => ⟨fun ⟨hα, hcl⟩ => ?_, ?_⟩⟩
  · have hm := (leechEquiv_mem_minVecs_iff α).2 hα
    rw [← hcl₀, classOf_eq_iff hm hm₀] at hcl
    rcases hcl with h | h
    · exact Or.inl (leechEquiv.injective (Subtype.ext h))
    · refine Or.inr (leechEquiv.injective (Subtype.ext ?_))
      rw [h, map_neg]
      rfl
  · have hneg : leech.form (-α₀) (-α₀) = 4 := by
      rw [LinearMap.map_neg₂, map_neg, neg_neg, hα₀]
    rintro (rfl | rfl)
    · exact ⟨hα₀, hcl₀⟩
    · refine ⟨hneg, ?_⟩
      rw [← hcl₀, classOf_eq_iff ((leechEquiv_mem_minVecs_iff _).2 hneg) hm₀, map_neg]
      exact Or.inr rfl

/-! ## §8  `±`-pairs of our minimal vectors, and the matching with `ShortIdx` -/

/-- Our minimal vectors (norm `4`). -/
abbrev MinVec : Type := {α : leech.carrier // leech.form α α = 4}

/-- `α ~ β ↔ α = ±β` on our minimal vectors. -/
def pmSetoid : Setoid MinVec where
  r α β := α.1 = β.1 ∨ α.1 = -β.1
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := fun {_ _} h => h.elim (fun h => Or.inl h.symm)
        (fun h => Or.inr (by rw [h, neg_neg]))
      trans := fun {_ _ _} h₁ h₂ => by
        rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
        · exact Or.inl (h₁.trans h₂)
        · exact Or.inr (h₁.trans h₂)
        · exact Or.inr (by rw [h₁, h₂])
        · exact Or.inl (by rw [h₁, h₂, neg_neg]) }

/-- The `±`-pairs of our minimal vectors. -/
abbrev PmClass : Type := Quotient pmSetoid

/-- `-α` of a minimal vector. -/
noncomputable def negMin (α : MinVec) : MinVec :=
  ⟨-α.1, by rw [LinearMap.map_neg₂, map_neg, neg_neg]; exact α.2⟩

theorem negMin_ne (α : MinVec) : negMin α ≠ α := by
  intro h
  have h1 : -α.1 = α.1 := congrArg Subtype.val h
  have h2 := congrArg (fun x => leech.form x α.1) h1
  simp only [LinearMap.map_neg₂] at h2
  have h3 := α.2
  omega

/-- ⭐ The `±` relation is exactly congruence mod `2Λ` after `π`. -/
theorem classOf_leechEquiv_eq_iff (α β : MinVec) :
    classOf (leechEquiv α.1 : Fin 24 → ℤ) = classOf (leechEquiv β.1 : Fin 24 → ℤ) ↔
      (α.1 = β.1 ∨ α.1 = -β.1) := by
  rw [classOf_eq_iff ((leechEquiv_mem_minVecs_iff _).2 α.2) ((leechEquiv_mem_minVecs_iff _).2 β.2)]
  have hneg : -(leechEquiv β.1 : Fin 24 → ℤ) = (leechEquiv (-β.1) : Fin 24 → ℤ) := by
    rw [map_neg]
    rfl
  rw [hneg, ← Subtype.ext_iff, ← Subtype.ext_iff, leechEquiv.injective.eq_iff,
    leechEquiv.injective.eq_iff]

/-- The class in Axiom's `Λ/2Λ` of a `±`-pair of our minimal vectors, after `π`. -/
noncomputable def pmClass : PmClass → L2 :=
  Quotient.lift (fun α : MinVec => classOf (leechEquiv α.1 : Fin 24 → ℤ))
    fun α β h => (classOf_leechEquiv_eq_iff α β).2 h

theorem pmClass_mk (α : MinVec) :
    pmClass (Quotient.mk pmSetoid α) = classOf (leechEquiv α.1 : Fin 24 → ℤ) := rfl

/-- ⭐ **Distinct `±`-pairs have distinct classes in `Λ/2Λ`.** -/
theorem pmClass_injective : Function.Injective pmClass := by
  intro q q' h
  induction q using Quotient.inductionOn
  induction q' using Quotient.inductionOn
  exact Quotient.sound ((classOf_leechEquiv_eq_iff _ _).1 h)

/-- The `±`-pair of our minimal vectors attached to `c : ShortIdx` (`exists_pm_of_shortIdx`). -/
noncomputable def shortToPm (c : ShortIdx) : PmClass :=
  Quotient.mk _ ⟨(exists_pm_of_shortIdx c).choose, (exists_pm_of_shortIdx c).choose_spec.1⟩

/-- ⭐ `shortToPm c` is the `±`-pair whose class (after `π`) is `phi0 c`. -/
theorem pmClass_shortToPm (c : ShortIdx) : pmClass (shortToPm c) = phi0 c.1 :=
  (((exists_pm_of_shortIdx c).choose_spec.2 _).2 (Or.inl rfl)).2

theorem shortToPm_injective (hφ : Function.Injective phi0) : Function.Injective shortToPm := by
  intro c c' h
  have h' := congrArg pmClass h
  rw [pmClass_shortToPm, pmClass_shortToPm] at h'
  exact Subtype.ext (hφ h')

theorem shortToPm_surjective (hφ : Function.Surjective phi0) : Function.Surjective shortToPm := by
  intro q
  induction q using Quotient.inductionOn with
  | h α =>
    obtain ⟨p, hp⟩ := hφ (classOf (leechEquiv α.1 : Fin 24 → ℤ))
    have hs : IsShortCoord p := (isShortCoord_iff p).2 ⟨α.1, α.2, hp.symm⟩
    refine ⟨⟨p, hs⟩, pmClass_injective ?_⟩
    rw [pmClass_shortToPm, pmClass_mk]
    exact hp

/-- ⭐ **`ShortIdx` is the set of `±`-pairs of our minimal vectors**, given that `phi0` is a
bijection (the source's `phi0Equiv`, not ported). -/
noncomputable def shortIdxEquivPm (hφ : Function.Bijective phi0) : ShortIdx ≃ PmClass :=
  Equiv.ofBijective shortToPm ⟨shortToPm_injective hφ.1, shortToPm_surjective hφ.2⟩

/-- Our lattice has `196560` minimal vectors (`Leech.repCount_four`). -/
theorem card_minVec : Nat.card MinVec = 196560 := Leech.repCount_four

open Classical in
/-- A minimal vector is its `±`-pair together with a sign relative to a chosen representative. -/
noncomputable def minVecEquivPmBool : MinVec ≃ PmClass × Bool where
  toFun α := (Quotient.mk _ α, decide (α = (Quotient.mk pmSetoid α).out))
  invFun qb := if qb.2 then qb.1.out else negMin qb.1.out
  left_inv α := by
    by_cases h : α = (Quotient.mk pmSetoid α).out
    · simp only [decide_eq_true h, if_true]
      exact h.symm
    · simp only [decide_eq_false h, Bool.false_eq_true, if_false]
      rcases Quotient.mk_out (s := pmSetoid) α with h' | h'
      · exact absurd (Subtype.ext h'.symm) h
      · refine Subtype.ext ?_
        change -((Quotient.mk pmSetoid α).out.1) = α.1
        rw [h', neg_neg]
  right_inv qb := by
    obtain ⟨q, b⟩ := qb
    cases b
    · have hq : Quotient.mk pmSetoid (negMin q.out) = q := by
        rw [← Quotient.out_eq q]
        refine Quotient.sound (Or.inr ?_)
        rw [Quotient.out_eq q]
        rfl
      simp only [Bool.false_eq_true, if_false, hq]
      exact Prod.ext rfl (decide_eq_false (negMin_ne _))
    · simp only [if_true, Quotient.out_eq]
      exact Prod.ext rfl (by simp)

/-- ⭐ **There are `98280` `±`-pairs of our minimal vectors.** -/
theorem card_pmClass : Nat.card PmClass = 98280 := by
  have h := Nat.card_congr minVecEquivPmBool
  rw [card_minVec, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
  omega

/-- ⭐ **`|ShortIdx| = 98280`**, given that `phi0` is a bijection. -/
theorem card_shortIdx_of_bijective (hφ : Function.Bijective phi0) : Nat.card ShortIdx = 98280 := by
  rw [Nat.card_congr (shortIdxEquivPm hφ), card_pmClass]

end VOA.Moonshine.MonsterGriess.LeechMatch
