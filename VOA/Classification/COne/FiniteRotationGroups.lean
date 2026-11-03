/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib

/-!
# The finite subgroups of `SO(3)`

We prove the classical theorem
(Klein): every finite subgroup `G` of the rotation group `SO(3, ℝ)` is isomorphic to a cyclic
group `ℤ_N`, a dihedral group `D_n`, the tetrahedral group `A₄`, the octahedral group `S₄`, or the
icosahedral group `A₅`.

## Conventions

* `SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ`, acting on `Fin 3 → ℝ` by `Matrix.mulVec`;
  unit vectors are `v ⬝ᵥ v = 1`.
* A *pole* of `G` is a unit vector fixed by some non-identity element of `G` (`IsPole`, the type
  `Poles G` with its `G`-action). The *signature* of `G` (`signature G`) is the multiset of the
  stabilizer orders `n_O`, one for each `G`-orbit `O` of poles.
* `DihedralGroup n` is Mathlib's dihedral group of order `2n` (so `D₂` is the Klein group).

## Main results

Stage 1 (geometry and counting):
* `fixed_units_of_ne_one` (Euler's rotation theorem): a non-identity rotation fixes exactly
  two unit vectors `±u`; `eq_one_of_fixes`: a rotation fixing two non-parallel vectors is `1`.
* `card_fixedBy_of_ne_one`, `card_poles_add` (Burnside): `|P| + 2(|G| - 1) = (#orbits) |G|`.
* `counting_identity`: `2 (1 - 1/|G|) = Σ_O (1 - 1/n_O)`.

Stage 2 (arithmetic):
* `signature_classification`: the Diophantine classification, for any multiset of divisors.
* `signature_cases`: the signature of a nontrivial `G` is `(N, N)`, `(2, 2, n)` with `N = 2n`,
  `(2, 3, 3)` with `N = 12`, `(2, 3, 4)` with `N = 24`, or `(2, 3, 5)` with `N = 60`.

Stage 3 (identification):
* `isCyclic_of_common_fixed`: a finite group of rotations about a common axis is cyclic (an
  injective character into `ℂ` read off from an orthonormal frame); `cyclic_of_orbitOrder_eq`.
* `dihedral_of_index_two` (abstract recognition of `D_n`) and
  `dihedral_of_stabilizer_index_two`: elements off the axis stabilizer are half-turns.
* `alternating_four_of_orbit`: faithful action on the 4-element orbit, image of index 2 in `S₄`.
* `perm_four_of_orbit`: faithful action on the four axes through the 8-element orbit
  (kernel lemma `eq_one_of_fix_or_neg`).
* `GroupTheory60.alternating_five_of`: a group of order 60 whose nontrivial normal subgroups
  have `≥ 16` elements and in which no element of order 5 centralizes a subgroup of order 4 is
  `A₅` (Sylow 2-normalizer has order 12, using Burnside's transfer theorem to exclude order 4;
  then the action on its five cosets). `sixteen_le_card_normal` (a double count of fixed poles)
  and `not_five_normalizes` verify the two hypotheses geometrically; `alternating_five`.
* `classification`: the final theorem.

## Status

Complete: all three stages are proved, with no `sorry` and no project axiom. Not addressed: the
converse (that each listed group occurs in `SO(3)`), and conjugacy of isomorphic subgroups.
-/

open Matrix

namespace VOA.Classification.COne.FiniteRotation

/-- The rotation group `SO(3, ℝ)`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

local notation "M3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "V3" => Fin 3 → ℝ

lemma transpose_mul_self (g : SO3) : (g : M3)ᵀ * (g : M3) = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp g.2.1
  simpa [Matrix.star_eq_conjTranspose] using this

lemma mul_transpose_self (g : SO3) : (g : M3) * (g : M3)ᵀ = 1 :=
  mul_eq_one_comm.mp (transpose_mul_self g)

lemma det_eq_one (g : SO3) : (g : M3).det = 1 := g.2.2

lemma coe_mul_mulVec (g h : SO3) (v : V3) :
    ((g * h : SO3) : M3) *ᵥ v = (g : M3) *ᵥ ((h : M3) *ᵥ v) := by
  simp [Matrix.mulVec_mulVec]

lemma dot_mulVec (g : SO3) (v w : V3) :
    ((g : M3) *ᵥ v) ⬝ᵥ ((g : M3) *ᵥ w) = v ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
    transpose_mul_self, Matrix.vecMul_one]

/-- For every `3 × 3` matrix, `Au × Aw = (adj A)ᵀ (u × w)`. -/
lemma cross_mulVec_adj (A : M3) (u w : V3) :
    (A *ᵥ u) ⨯₃ (A *ᵥ w) = (adjugate A)ᵀ *ᵥ (u ⨯₃ w) := by
  ext i
  fin_cases i <;>
  simp [cross_apply, adjugate_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

lemma adjugate_eq_transpose (g : SO3) : adjugate (g : M3) = (g : M3)ᵀ := by
  have h := Matrix.mul_adjugate (g : M3)
  rw [det_eq_one, one_smul] at h
  calc adjugate (g : M3) = ((g : M3)ᵀ * (g : M3)) * adjugate (g : M3) := by
        rw [transpose_mul_self, one_mul]
    _ = (g : M3)ᵀ := by rw [Matrix.mul_assoc, h, Matrix.mul_one]

lemma cross_mulVec (g : SO3) (u w : V3) :
    ((g : M3) *ᵥ u) ⨯₃ ((g : M3) *ᵥ w) = (g : M3) *ᵥ (u ⨯₃ w) := by
  rw [cross_mulVec_adj, adjugate_eq_transpose, Matrix.transpose_transpose]

/-- Every rotation has a nonzero fixed vector (Euler's rotation theorem, existence part). -/
lemma exists_fixed (g : SO3) : ∃ v : V3, v ≠ 0 ∧ (g : M3) *ᵥ v = v := by
  set A : M3 := (g : M3)
  have hfac : A - 1 = A * (1 - Aᵀ) := by
    rw [Matrix.mul_sub, Matrix.mul_one, mul_transpose_self]
  have hdet : (A - 1).det = 0 := by
    have h1 : (A - 1).det = (1 - A).det := by
      rw [hfac, Matrix.det_mul, det_eq_one, one_mul, ← Matrix.det_transpose,
        Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose]
    have h2 : (1 - A).det = - (A - 1).det := by
      rw [← neg_sub, Matrix.det_neg]; norm_num
    linarith
  obtain ⟨v, hv, h⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
  exact h


lemma cross_dot_self (u w : V3) :
    (u ⨯₃ w) ⬝ᵥ (u ⨯₃ w) = (u ⬝ᵥ u) * (w ⬝ᵥ w) - (u ⬝ᵥ w) ^ 2 := by
  rw [cross_dot_cross, dotProduct_comm w u]; ring

/-- Two unit vectors with vanishing cross product are equal or antipodal. -/
lemma eq_or_eq_neg_of_cross_eq_zero {u w : V3} (hu : u ⬝ᵥ u = 1) (hw : w ⬝ᵥ w = 1)
    (h : u ⨯₃ w = 0) : w = u ∨ w = -u := by
  have h1 := cross_dot_self u w
  rw [h, zero_dotProduct, hu, hw] at h1
  have h2 : (u ⬝ᵥ w - 1) * (u ⬝ᵥ w + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left
    have : (w - u) ⬝ᵥ (w - u) = 0 := by
      simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm w u]
      linear_combination hu + hw - 2 * h3
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp this)
  · right
    have : (w + u) ⬝ᵥ (w + u) = 0 := by
      simp only [add_dotProduct, dotProduct_add, dotProduct_comm w u]
      linear_combination hu + hw + 2 * h3
    exact eq_neg_of_add_eq_zero_left (dotProduct_self_eq_zero.mp this)

/-- A rotation fixing two non-parallel vectors is the identity. -/
lemma eq_one_of_fixes (g : SO3) {u w : V3} (h : u ⨯₃ w ≠ 0)
    (hu : (g : M3) *ᵥ u = u) (hw : (g : M3) *ᵥ w = w) : g = 1 := by
  set x := u ⨯₃ w with hxdef
  have hx : (g : M3) *ᵥ x = x := by rw [hxdef, ← cross_mulVec, hu, hw]
  set R : M3 := ![u, w, x]
  have hdet : R.det = x ⬝ᵥ x := by
    rw [← triple_product_eq_det, triple_product_permutation, triple_product_permutation]
  have hdet0 : R.det ≠ 0 := by
    rw [hdet]; exact fun h0 => h (dotProduct_self_eq_zero.mp h0)
  have key : R * (g : M3)ᵀ = R := by
    ext i j
    have e : ∀ v : V3, (g : M3) *ᵥ v = v → ∑ k, v k * (g : M3) j k = v j := by
      intro v hv
      have := congrFun hv j
      simp only [Matrix.mulVec, dotProduct] at this
      rw [← this]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    fin_cases i
    · simpa [R, Matrix.mul_apply] using e u hu
    · simpa [R, Matrix.mul_apply] using e w hw
    · simpa [R, Matrix.mul_apply] using e x hx
  have hinv : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (isUnit_iff_ne_zero.mpr hdet0)
  have hT : (g : M3)ᵀ = 1 := by
    calc (g : M3)ᵀ = R⁻¹ * (R * (g : M3)ᵀ) := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = 1 := by rw [key, hinv]
  apply Subtype.ext
  simpa using congrArg Matrix.transpose hT

lemma exists_unit_fixed (g : SO3) : ∃ u : V3, u ⬝ᵥ u = 1 ∧ (g : M3) *ᵥ u = u := by
  obtain ⟨v, hv, hgv⟩ := exists_fixed g
  have hpos : 0 < v ⬝ᵥ v := by
    rcases (show (0:ℝ) ≤ v ⬝ᵥ v from
      Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)).lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hv
  refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹ • v, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  · rw [Matrix.mulVec_smul, hgv]

/-- **Euler's rotation theorem.** A non-identity rotation fixes exactly two unit vectors,
an antipodal pair `±u`. -/
theorem fixed_units_of_ne_one (g : SO3) (hg : g ≠ 1) :
    ∃ u : V3, u ⬝ᵥ u = 1 ∧ (g : M3) *ᵥ u = u ∧
      ∀ v : V3, (v ⬝ᵥ v = 1 ∧ (g : M3) *ᵥ v = v) ↔ (v = u ∨ v = -u) := by
  obtain ⟨u, hu, hgu⟩ := exists_unit_fixed g
  refine ⟨u, hu, hgu, fun v => ⟨fun ⟨hv, hgv⟩ => ?_, ?_⟩⟩
  · by_contra hne
    exact hg (eq_one_of_fixes g (fun h0 => hne (eq_or_eq_neg_of_cross_eq_zero hu hv h0)) hgu hgv)
  · rintro (rfl | rfl)
    · exact ⟨hu, hgu⟩
    · refine ⟨by simpa using hu, by rw [Matrix.mulVec_neg, hgu]⟩

lemma ne_neg_of_unit {u : V3} (hu : u ⬝ᵥ u = 1) : u ≠ -u := by
  intro h
  have : u = 0 := by
    have h2 : (2 : ℝ) • u = 0 := by rw [two_smul]; nth_rewrite 2 [h]; simp
    simpa using h2
  rw [this] at hu; simp at hu


lemma inv_mulVec_mulVec (g : SO3) (v : V3) :
    ((g⁻¹ : SO3) : M3) *ᵥ ((g : M3) *ᵥ v) = v := by
  rw [← coe_mul_mulVec, inv_mul_cancel]; simp

lemma mulVec_eq_iff_inv (g : SO3) (v w : V3) :
    (g : M3) *ᵥ v = w ↔ ((g⁻¹ : SO3) : M3) *ᵥ w = v := by
  constructor
  · rintro rfl; exact inv_mulVec_mulVec g v
  · rintro rfl; rw [← coe_mul_mulVec, mul_inv_cancel]; simp

/-! ### Poles of a subgroup -/

section Poles

variable (G : Subgroup SO3)

/-- A *pole* of `G`: a unit vector fixed by some non-identity element of `G`. -/
def IsPole (v : V3) : Prop := v ⬝ᵥ v = 1 ∧ ∃ g ∈ G, g ≠ 1 ∧ (g : M3) *ᵥ v = v

/-- The set of poles of `G`, as a type. -/
def Poles : Type := {v : V3 // IsPole G v}

variable {G}

lemma isPole_smul {g : SO3} (hg : g ∈ G) {v : V3} (hv : IsPole G v) :
    IsPole G ((g : M3) *ᵥ v) := by
  obtain ⟨hv1, h, hh, hne, hhv⟩ := hv
  refine ⟨by rw [dot_mulVec, hv1], g * h * g⁻¹, G.mul_mem (G.mul_mem hg hh) (G.inv_mem hg),
    ?_, ?_⟩
  · intro h1
    apply hne
    have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
    rw [this, h1]; group
  · rw [coe_mul_mulVec, inv_mulVec_mulVec, coe_mul_mulVec, hhv]

instance : MulAction G (Poles G) where
  smul g p := ⟨((g : SO3) : M3) *ᵥ p.1, isPole_smul g.2 p.2⟩
  one_smul p := by apply Subtype.ext; change ((1 : SO3) : M3) *ᵥ p.1 = p.1; simp
  mul_smul g h p := by
    apply Subtype.ext
    change (((g * h : G) : SO3) : M3) *ᵥ p.1 = ((g : SO3) : M3) *ᵥ (((h : SO3) : M3) *ᵥ p.1)
    rw [Subgroup.coe_mul, coe_mul_mulVec]

@[simp] lemma smul_val (g : G) (p : Poles G) :
    (g • p).1 = ((g : SO3) : M3) *ᵥ p.1 := rfl

lemma poles_subset [Finite G] :
    {v : V3 | IsPole G v} ⊆
      ⋃ g ∈ (Set.univ : Set G), {v : V3 | v ⬝ᵥ v = 1 ∧ (g : M3) *ᵥ v = v ∧ (g : SO3) ≠ 1} := by
  rintro v ⟨hv, g, hg, hne, hgv⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨⟨g, hg⟩, Set.mem_univ _, hv, hgv, hne⟩

instance [Finite G] : Finite (Poles G) := by
  have hfin : ({v : V3 | IsPole G v}).Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion Set.finite_univ fun g _ => ?_) poles_subset
    by_cases hg : (g : SO3) = 1
    · simp [hg]
    · obtain ⟨u, -, -, hu⟩ := fixed_units_of_ne_one (g : SO3) hg
      refine (Set.toFinite ({u, -u} : Set V3)).subset ?_
      rintro v ⟨hv, hgv, -⟩
      rcases (hu v).mp ⟨hv, hgv⟩ with h | h <;> simp [h]
  exact hfin.to_subtype

/-- A non-identity element of `G` fixes exactly two poles. -/
lemma card_fixedBy_of_ne_one (g : G) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy (Poles G) g) = 2 := by
  have hg' : (g : SO3) ≠ 1 := fun h => hg (Subtype.ext h)
  obtain ⟨u, hu, hgu, hfix⟩ := fixed_units_of_ne_one (g : SO3) hg'
  have hpu : IsPole G u := ⟨hu, g, g.2, hg', hgu⟩
  have hpmu : IsPole G (-u) := ⟨by simpa using hu, g, g.2, hg', by rw [Matrix.mulVec_neg, hgu]⟩
  have hset : MulAction.fixedBy (Poles G) g =
      ({⟨u, hpu⟩, ⟨-u, hpmu⟩} : Set (Poles G)) := by
    ext p
    simp only [MulAction.mem_fixedBy, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h' : ((g : SO3) : M3) *ᵥ p.1 = p.1 := congrArg Subtype.val h
      rcases (hfix p.1).mp ⟨p.2.1, h'⟩ with h1 | h1
      · left; exact Subtype.ext h1
      · right; exact Subtype.ext h1
    · rintro (rfl | rfl)
      · exact Subtype.ext hgu
      · exact Subtype.ext (by
          change ((g : SO3) : M3) *ᵥ (-u) = -u
          rw [Matrix.mulVec_neg, hgu])
  rw [hset, Nat.card_coe_set_eq, Set.ncard_pair]
  intro h
  exact ne_neg_of_unit hu (congrArg Subtype.val h)

lemma card_fixedBy_one : Nat.card (MulAction.fixedBy (Poles G) (1 : G)) = Nat.card (Poles G) := by
  rw [show MulAction.fixedBy (Poles G) (1 : G) = Set.univ from
    Set.eq_univ_of_forall fun p => one_smul _ p]
  exact Nat.card_univ

/-- The stabilizer of a pole is nontrivial. -/
lemma one_lt_card_stabilizer [Finite G] (p : Poles G) :
    1 < Nat.card (MulAction.stabilizer G p) := by
  obtain ⟨-, g, hg, hne, hgp⟩ := p.2
  rw [Subgroup.one_lt_card_iff_ne_bot]
  intro hbot
  have hmem : (⟨g, hg⟩ : G) ∈ MulAction.stabilizer G p := Subtype.ext hgp
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hne (congrArg Subtype.val hmem)

/-- The orbits of `G` on its poles. -/
abbrev Orbits (G : Subgroup SO3) := Quotient (MulAction.orbitRel G (Poles G))

noncomputable instance [Finite G] : Fintype (Orbits G) := Fintype.ofFinite _

/-- The stabilizer order `n_O` attached to an orbit of poles. -/
noncomputable def orbitOrder (ω : Orbits G) : ℕ := Nat.card (MulAction.stabilizer G ω.out)

/-- **The counting identity**, integer form: `|P| + 2(|G| - 1) = (#orbits) |G|`. -/
theorem card_poles_add (G : Subgroup SO3) [Finite G] :
    Nat.card (Poles G) + 2 * (Nat.card G - 1) = Nat.card (Orbits G) * Nat.card G := by
  classical
  haveI : Fintype G := Fintype.ofFinite _
  haveI : Fintype (Poles G) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (Poles G)
  simp only [Fintype.card_eq_nat_card] at hB
  rw [← hB, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G)), card_fixedBy_one,
    Finset.sum_congr rfl (fun g hg => card_fixedBy_of_ne_one g (Finset.ne_of_mem_erase hg)),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_eq_nat_card, smul_eq_mul, mul_comm]

/-- The class formula `|P| = Σ_O |G| / n_O`. -/
theorem card_poles_eq_sum (G : Subgroup SO3) [Finite G] :
    Nat.card (Poles G) = ∑ ω : Orbits G, Nat.card G / orbitOrder ω := by
  classical
  haveI : Fintype G := Fintype.ofFinite _
  haveI : Fintype (Poles G) := Fintype.ofFinite _
  have h := MulAction.card_eq_sum_card_group_div_card_stabilizer G (Poles G)
  simp only [Fintype.card_eq_nat_card] at h
  exact h

lemma orbitOrder_dvd [Finite G] (ω : Orbits G) : orbitOrder ω ∣ Nat.card G :=
  Subgroup.card_subgroup_dvd_card _

lemma two_le_orbitOrder [Finite G] (ω : Orbits G) : 2 ≤ orbitOrder ω :=
  one_lt_card_stabilizer ω.out

/-- **The counting identity**: `2 (1 - 1/|G|) = Σ_O (1 - 1/n_O)`. -/
theorem counting_identity (G : Subgroup SO3) [Finite G] :
    (2 : ℚ) * (1 - 1 / Nat.card G) = ∑ ω : Orbits G, (1 - 1 / (orbitOrder ω : ℚ)) := by
  classical
  have hN : 0 < Nat.card G := Nat.card_pos
  have h1 := card_poles_add G
  rw [card_poles_eq_sum] at h1
  have h2 : ((∑ ω : Orbits G, Nat.card G / orbitOrder ω : ℕ) : ℚ) =
      ∑ ω : Orbits G, (Nat.card G : ℚ) / orbitOrder ω := by
    push_cast
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Nat.cast_div (orbitOrder_dvd ω)]
    exact_mod_cast (by have := two_le_orbitOrder ω; omega : orbitOrder ω ≠ 0)
  have h3 : ((Nat.card G - 1 : ℕ) : ℚ) = Nat.card G - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h1q : ((∑ ω : Orbits G, Nat.card G / orbitOrder ω : ℕ) : ℚ) + 2 * (Nat.card G - 1)
      = Nat.card (Orbits G) * Nat.card G := by
    rw [← h3]; exact_mod_cast h1
  rw [h2] at h1q
  have hNq : (Nat.card G : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]
  have h4 : ∑ ω : Orbits G, (1 / (orbitOrder ω : ℚ)) =
      (∑ ω : Orbits G, (Nat.card G : ℚ) / orbitOrder ω) / Nat.card G := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun ω _ => ?_
    field_simp
  rw [h4]
  field_simp
  linear_combination h1q

end Poles

/-! ### Stage 2: the Diophantine classification of signatures -/

lemma inv_le_of_le {a b : ℕ} (ha : 0 < a) (h : a ≤ b) : (1 : ℚ) / b ≤ 1 / a :=
  one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast h)

/-- The ordered three-orbit case. -/
lemma triple_ordered {a b c N : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hN : 0 < N)
    (h : (1 : ℚ) / a + 1 / b + 1 / c = 1 + 2 / N) :
    (a = 2 ∧ b = 2 ∧ N = 2 * c) ∨ (a = 2 ∧ b = 3 ∧ c = 3 ∧ N = 12) ∨
      (a = 2 ∧ b = 3 ∧ c = 4 ∧ N = 24) ∨ (a = 2 ∧ b = 3 ∧ c = 5 ∧ N = 60) := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hpos : (0 : ℚ) < 2 / N := by positivity
  have ha2 : a = 2 := by
    by_contra hne
    have h3 : 3 ≤ a := by omega
    have := inv_le_of_le (by norm_num) h3
    have := inv_le_of_le (by norm_num) (h3.trans hab)
    have := inv_le_of_le (by norm_num) (h3.trans (hab.trans hbc))
    push_cast at *
    linarith
  subst ha2
  have hb3 : b ≤ 3 := by
    by_contra hne
    have h4 : 4 ≤ b := by omega
    have := inv_le_of_le (by norm_num) h4
    have := inv_le_of_le (by norm_num) (h4.trans hbc)
    push_cast at *
    linarith
  interval_cases b
  · left
    refine ⟨rfl, rfl, ?_⟩
    have hc : (c : ℚ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
    have e : (2 : ℚ) / N = 1 / c := by push_cast at h; linarith
    rw [div_eq_div_iff hNq.ne' hc] at e
    exact_mod_cast (by linarith : (N : ℚ) = 2 * c)
  · have hc5 : c ≤ 5 := by
      by_contra hne
      have := inv_le_of_le (by norm_num) (by omega : 6 ≤ c)
      push_cast at *
      linarith
    right
    interval_cases c
    · left; refine ⟨rfl, rfl, rfl, ?_⟩
      have e : (2 : ℚ) / N = 1 / 6 := by push_cast at h; linarith
      rw [div_eq_div_iff hNq.ne' (by norm_num)] at e
      exact_mod_cast (by linarith : (N : ℚ) = 12)
    · right; left; refine ⟨rfl, rfl, rfl, ?_⟩
      have e : (2 : ℚ) / N = 1 / 12 := by push_cast at h; linarith
      rw [div_eq_div_iff hNq.ne' (by norm_num)] at e
      exact_mod_cast (by linarith : (N : ℚ) = 24)
    · right; right; refine ⟨rfl, rfl, rfl, ?_⟩
      have e : (2 : ℚ) / N = 1 / 30 := by push_cast at h; linarith
      rw [div_eq_div_iff hNq.ne' (by norm_num)] at e
      exact_mod_cast (by linarith : (N : ℚ) = 60)

lemma sort3 (a b c : ℕ) : ∃ x y z : ℕ, x ≤ y ∧ y ≤ z ∧
    ({a, b, c} : Multiset ℕ) = {x, y, z} := by
  rcases le_total a b with h1 | h1 <;> rcases le_total b c with h2 | h2 <;>
    rcases le_total a c with h3 | h3
  · exact ⟨a, b, c, h1, h2, rfl⟩
  · exact ⟨a, b, c, h1, h2, rfl⟩
  · exact ⟨a, c, b, h3, h2, by simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; abel⟩
  · exact ⟨c, a, b, h3, h1, by simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; abel⟩
  · exact ⟨b, a, c, h1, h3, by simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; abel⟩
  · exact ⟨b, c, a, h2, h3, by simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; abel⟩
  · exact ⟨c, b, a, h2, h1, by simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; abel⟩
  · exact ⟨c, b, a, h2, h1, by simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]; abel⟩

/-- **Stage 2**: the Diophantine classification of signatures. -/
theorem signature_classification {N : ℕ} {s : Multiset ℕ} (hN : 2 ≤ N)
    (hs : ∀ n ∈ s, 2 ≤ n ∧ n ∣ N)
    (h : (2 : ℚ) * (1 - 1 / N) = (s.map fun n : ℕ => (1 - 1 / (n : ℚ))).sum) :
    s = {N, N} ∨ (∃ n, 2 ≤ n ∧ N = 2 * n ∧ s = {2, 2, n}) ∨ (N = 12 ∧ s = {2, 3, 3}) ∨
      (N = 24 ∧ s = {2, 3, 4}) ∨ (N = 60 ∧ s = {2, 3, 5}) := by
  have hNq : (2 : ℚ) ≤ N := by exact_mod_cast hN
  have hle : ∀ n ∈ s, n ≤ N := fun n hn => Nat.le_of_dvd (by omega) (hs n hn).2
  -- each term lies in `[1/2, 1)`
  have hlow : ∀ x ∈ s.map (fun n : ℕ => (1 - 1 / (n : ℚ))), (1 / 2 : ℚ) ≤ x := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hx
    have := inv_le_of_le (by norm_num) (hs n hn).1
    push_cast at this; linarith
  have hcard4 : Multiset.card s < 4 := by
    by_contra hc
    have := Multiset.card_nsmul_le_sum hlow
    rw [Multiset.card_map, nsmul_eq_mul] at this
    have hc' : (4 : ℚ) ≤ Multiset.card s := by exact_mod_cast (not_lt.mp hc)
    have : (0 : ℚ) < 1 / N := by positivity
    nlinarith
  have hcard2 : 2 ≤ Multiset.card s := by
    by_contra hc
    have hN2 : (1 : ℚ) / N ≤ 1 / 2 := inv_le_of_le (by norm_num) hN
    rw [one_div] at hN2
    interval_cases hk : Multiset.card s
    · rw [Multiset.card_eq_zero] at hk; subst hk; simp at h; linarith
    · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hk
      simp only [one_div] at *
      simp at h
      have : (0 : ℚ) < (a : ℚ)⁻¹ := by
        have := (hs a (by simp)).1
        have : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
        positivity
      push_cast at *
      linarith
  interval_cases hk : Multiset.card s
  · left
    obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hk
    have ha := hs a (by simp); have hb := hs b (by simp)
    have hla := inv_le_of_le (by omega) (hle a (by simp))
    have hlb := inv_le_of_le (by omega) (hle b (by simp))
    simp only [one_div] at *
    simp at h
    have hNpos : (0 : ℚ) < N := by linarith
    have ea : (a : ℚ)⁻¹ = (N : ℚ)⁻¹ := by linarith
    have eb : (b : ℚ)⁻¹ = (N : ℚ)⁻¹ := by linarith
    have ha' : (a : ℚ) = N := by
      have h0 : (a : ℚ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
      exact inv_injective ea
    have hb' : (b : ℚ) = N := by
      have h0 : (b : ℚ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
      exact inv_injective eb
    have : a = N := by exact_mod_cast ha'
    have : b = N := by exact_mod_cast hb'
    subst a; subst b; rfl
  · right
    obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp hk
    obtain ⟨x, y, z, hxy, hyz, hxyz⟩ := sort3 a b c
    rw [hxyz] at h hs ⊢
    have hx := (hs x (by simp)).1
    have h' : (1 : ℚ) / x + 1 / y + 1 / z = 1 + 2 / N := by
      simp only [one_div] at *; simp at h; rw [div_eq_mul_inv]; linarith
    rcases triple_ordered hx hxy hyz (by omega) h' with
      ⟨rfl, rfl, hN2⟩ | ⟨rfl, rfl, rfl, hN2⟩ | ⟨rfl, rfl, rfl, hN2⟩ | ⟨rfl, rfl, rfl, hN2⟩
    · left; exact ⟨z, by omega, hN2, rfl⟩
    · right; left; exact ⟨hN2, rfl⟩
    · right; right; left; exact ⟨hN2, rfl⟩
    · right; right; right; exact ⟨hN2, rfl⟩

/-! ### Stages 1 + 2 combined -/

/-- The *signature* of `G`: the multiset of stabilizer orders `n_O`, one per orbit of poles. -/
noncomputable def signature (G : Subgroup SO3) [Finite G] : Multiset ℕ :=
  (Finset.univ : Finset (Orbits G)).val.map orbitOrder

/-- **Signature theorem.** For a nontrivial finite subgroup `G ≤ SO(3)` of order `N`, the
signature is `(N, N)`, `(2, 2, n)` with `N = 2n`, `(2, 3, 3)` with `N = 12`, `(2, 3, 4)` with
`N = 24`, or `(2, 3, 5)` with `N = 60`. -/
theorem signature_cases (G : Subgroup SO3) [Finite G] (hG : G ≠ ⊥) :
    signature G = {Nat.card G, Nat.card G} ∨
      (∃ n, 2 ≤ n ∧ Nat.card G = 2 * n ∧ signature G = {2, 2, n}) ∨
      (Nat.card G = 12 ∧ signature G = {2, 3, 3}) ∨
      (Nat.card G = 24 ∧ signature G = {2, 3, 4}) ∨
      (Nat.card G = 60 ∧ signature G = {2, 3, 5}) := by
  apply signature_classification
  · exact (Subgroup.one_lt_card_iff_ne_bot G).mpr hG
  · intro n hn
    obtain ⟨ω, -, rfl⟩ := Multiset.mem_map.mp hn
    exact ⟨two_le_orbitOrder ω, orbitOrder_dvd ω⟩
  · rw [counting_identity, signature, Multiset.map_map]
    rfl

/-! ### Stage 3a: rotations about a common axis form a cyclic group -/

/-- The third standard basis vector. -/
def e3 : V3 := ![0, 0, 1]

lemma exists_unit_smul {v : V3} (hv : v ≠ 0) : ∃ c : ℝ, (c • v) ⬝ᵥ (c • v) = 1 := by
  have hpos : 0 < v ⬝ᵥ v := by
    rcases (show (0:ℝ) ≤ v ⬝ᵥ v from
      Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)).lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hv
  refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹, ?_⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

/-- Every unit vector has a unit vector orthogonal to it. -/
lemma exists_unit_orthogonal (p : V3) :
    ∃ e : V3, e ⬝ᵥ e = 1 ∧ e ⬝ᵥ p = 0 := by
  have key : ∃ v : V3, v ≠ 0 ∧ v ⬝ᵥ p = 0 := by
    by_cases h : p 1 = 0 ∧ p 2 = 0
    · refine ⟨![0, 1, 0], fun h0 => by simpa using congrFun h0 1, ?_⟩
      simp [dotProduct, Fin.sum_univ_three, h.1]
    · refine ⟨![0, p 2, -p 1], fun h0 => h ⟨?_, ?_⟩, ?_⟩
      · simpa using congrFun h0 2
      · simpa using congrFun h0 1
      · simp [dotProduct, Fin.sum_univ_three]; ring
  obtain ⟨v, hv, hvp⟩ := key
  obtain ⟨c, hc⟩ := exists_unit_smul hv
  exact ⟨c • v, hc, by rw [smul_dotProduct, hvp, smul_zero]⟩

/-- An orthonormal frame moving a unit vector `p` to `e₃`. -/
lemma exists_frame {p : V3} (hp : p ⬝ᵥ p = 1) :
    ∃ M : M3, M * Mᵀ = 1 ∧ M *ᵥ p = e3 := by
  obtain ⟨e, he, hep⟩ := exists_unit_orthogonal p
  set f := p ⨯₃ e
  have hff : f ⬝ᵥ f = 1 := by rw [cross_dot_self, hp, he, dotProduct_comm, hep]; ring
  have hef : e ⬝ᵥ f = 0 := dot_cross_self p e
  have hpf : p ⬝ᵥ f = 0 := dot_self_cross p e
  refine ⟨![e, f, p], ?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply]
    have hrow : ∀ (u w : V3), ∑ k, u k * w k = u ⬝ᵥ w := fun _ _ => rfl
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.transpose_apply, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
        Matrix.one_apply] <;>
      (rw [hrow]; simp [he, hef, hep, hff, hpf, hp, dotProduct_comm f e, dotProduct_comm f p,
        dotProduct_comm p e])
  · ext i
    fin_cases i <;> simp [e3, Matrix.mulVec, hep, hpf, hp, dotProduct_comm f p]

/-- A rotation fixing `e₃` has the block form `[[a, -b, 0], [b, a, 0], [0, 0, 1]]`. -/
lemma block_form {B : M3} (h1 : B * Bᵀ = 1) (h2 : Bᵀ * B = 1) (hdet : B.det = 1)
    (hfix : B *ᵥ e3 = e3) :
    B 0 2 = 0 ∧ B 1 2 = 0 ∧ B 2 2 = 1 ∧ B 2 0 = 0 ∧ B 2 1 = 0 ∧ B 1 1 = B 0 0 ∧
      B 0 1 = - B 1 0 := by
  have c : ∀ i, B i 2 = e3 i := fun i => by
    have := congrFun hfix i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e3] using this
  have b02 : B 0 2 = 0 := by simpa [e3] using c 0
  have b12 : B 1 2 = 0 := by simpa [e3] using c 1
  have b22 : B 2 2 = 1 := by simpa [e3] using c 2
  have r22 := congrFun (congrFun h1 2) 2
  have q00 := congrFun (congrFun h2 0) 0
  have q11 := congrFun (congrFun h2 1) 1
  have q01 := congrFun (congrFun h2 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at r22 q00 q11 q01
  rw [b22] at r22
  have b20 : B 2 0 = 0 := by nlinarith
  have b21 : B 2 1 = 0 := by nlinarith
  rw [Matrix.det_fin_three, b02, b12, b22] at hdet
  rw [b20] at q00
  rw [b21] at q11
  have hsq : (B 1 1 - B 0 0) ^ 2 + (B 0 1 + B 1 0) ^ 2 = 0 := by nlinarith
  have hA : B 1 1 - B 0 0 = 0 := by nlinarith
  have hB : B 0 1 + B 1 0 = 0 := by nlinarith
  exact ⟨b02, b12, b22, b20, b21, by linarith, by linarith⟩

section Cyclic

variable {H : Type*} [Group H] (φ : H →* SO3) {M : M3}

/-- The conjugated matrix `M φ(h) Mᵀ`. -/
def conjM (M : M3) (h : H) : M3 := M * (φ h : M3) * Mᵀ

lemma conjM_props (hM : M * Mᵀ = 1) {p : V3} (hMp : M *ᵥ p = e3)
    (hfix : ∀ h, (φ h : M3) *ᵥ p = p) (h : H) :
    let B := conjM φ M h
    B * Bᵀ = 1 ∧ Bᵀ * B = 1 ∧ B.det = 1 ∧ B *ᵥ e3 = e3 := by
  have hM' : Mᵀ * M = 1 := mul_eq_one_comm.mp hM
  intro B
  have hBB : B * Bᵀ = 1 := by
    simp only [B, conjM, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc M * (φ h : M3) * Mᵀ * (M * ((φ h : M3)ᵀ * Mᵀ))
        = M * (φ h : M3) * (Mᵀ * M) * (φ h : M3)ᵀ * Mᵀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM', Matrix.mul_one, Matrix.mul_assoc M, mul_transpose_self,
            Matrix.mul_one, hM]
  refine ⟨hBB, mul_eq_one_comm.mp hBB, ?_, ?_⟩
  · simp only [B, conjM, Matrix.det_mul, Matrix.det_transpose, det_eq_one, mul_one]
    have := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    exact this
  · have hMt : Mᵀ *ᵥ e3 = p := by rw [← hMp, Matrix.mulVec_mulVec, hM', Matrix.one_mulVec]
    simp only [B, conjM, ← Matrix.mulVec_mulVec, hMt, hfix, hMp]

lemma conjM_mul (hM : M * Mᵀ = 1) (g h : H) :
    conjM φ M (g * h) = conjM φ M g * conjM φ M h := by
  have hM' : Mᵀ * M = 1 := mul_eq_one_comm.mp hM
  simp only [conjM, map_mul, Submonoid.coe_mul]
  calc M * ((φ g : M3) * (φ h : M3)) * Mᵀ
      = M * (φ g : M3) * (Mᵀ * M) * (φ h : M3) * Mᵀ := by
        rw [hM', Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

lemma conjM_block (hM : M * Mᵀ = 1) {p : V3} (hMp : M *ᵥ p = e3)
    (hfix : ∀ h, (φ h : M3) *ᵥ p = p) (h : H) :
    let B := conjM φ M h
    B 0 2 = 0 ∧ B 1 2 = 0 ∧ B 2 2 = 1 ∧ B 2 0 = 0 ∧ B 2 1 = 0 ∧ B 1 1 = B 0 0 ∧
      B 0 1 = - B 1 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := conjM_props φ hM hMp hfix h
  exact block_form h1 h2 h3 h4

/-- The character `H → ℂ` given by the rotation angle about the common axis. -/
noncomputable def angleChar (hM : M * Mᵀ = 1) {p : V3} (hMp : M *ᵥ p = e3)
    (hfix : ∀ h, (φ h : M3) *ᵥ p = p) : H →* ℂ where
  toFun h := ⟨conjM φ M h 0 0, conjM φ M h 1 0⟩
  map_one' := by
    have : conjM φ M 1 = 1 := by simp [conjM, hM]
    apply Complex.ext <;> simp [this]
  map_mul' g h := by
    obtain ⟨g02, g12, -, -, -, g11, g01⟩ := conjM_block φ hM hMp hfix g
    obtain ⟨-, -, -, h20, -, -, -⟩ := conjM_block φ hM hMp hfix h
    rw [conjM_mul φ hM]
    apply Complex.ext <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, g02, g12, g11, g01, h20] <;> ring

lemma angleChar_injective (hM : M * Mᵀ = 1) {p : V3} (hMp : M *ᵥ p = e3)
    (hfix : ∀ h, (φ h : M3) *ᵥ p = p) (hφ : Function.Injective φ) :
    Function.Injective (angleChar φ hM hMp hfix) := by
  intro g h hgh
  have e0 : conjM φ M g 0 0 = conjM φ M h 0 0 := congrArg Complex.re hgh
  have e1 : conjM φ M g 1 0 = conjM φ M h 1 0 := congrArg Complex.im hgh
  obtain ⟨g02, g12, g22, g20, g21, g11, g01⟩ := conjM_block φ hM hMp hfix g
  obtain ⟨h02, h12, h22, h20, h21, h11, h01⟩ := conjM_block φ hM hMp hfix h
  have hB : conjM φ M g = conjM φ M h := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  have hM' : Mᵀ * M = 1 := mul_eq_one_comm.mp hM
  have key : ∀ x : H, Mᵀ * conjM φ M x * M = (φ x : M3) := fun x => by
    simp only [conjM, Matrix.mul_assoc, hM', Matrix.mul_one]
    rw [← Matrix.mul_assoc, hM', Matrix.one_mul]
  apply hφ
  apply Subtype.ext
  rw [← key g, ← key h, hB]

/-- **Stage 3a.** A finite group of rotations with a common fixed unit vector is cyclic. -/
theorem isCyclic_of_common_fixed {H : Type*} [Group H] [Finite H] (φ : H →* SO3)
    (hφ : Function.Injective φ) {p : V3} (hp : p ⬝ᵥ p = 1)
    (hfix : ∀ h, (φ h : M3) *ᵥ p = p) : IsCyclic H := by
  obtain ⟨M, hM, hMp⟩ := exists_frame hp
  exact isCyclic_of_injective_ringHom (angleChar φ hM hMp hfix)
    (angleChar_injective φ hM hMp hfix hφ)

end Cyclic

/-! ### Group theory: recognizing `A₅` -/

namespace GroupTheory60

variable {Γ : Type*} [Group Γ] [Finite Γ]

/-- A Sylow `2`-subgroup of a group of order `60` has order `4`. -/
lemma card_sylow_two (hΓ : Nat.card Γ = 60) (V : Sylow 2 Γ) : Nat.card V = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp V.isPGroup'
  have hnd := V.not_dvd_index
  have hmul := (V : Subgroup Γ).index_mul_card
  rw [hk, hΓ] at hmul
  have hk5 : k ≤ 5 := by
    by_contra hlt
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ k ≤ 60 := Nat.le_of_dvd (by norm_num) ⟨_, by rw [← hmul, mul_comm]⟩
    omega
  rw [hk]
  interval_cases k <;> omega

/-- A subgroup of order `12` in a group of order `60` without nontrivial normal subgroups of
order `< 16` yields an isomorphism with `A₅`, via the action on the five cosets. -/
theorem alternating_five_of_card_twelve (hΓ : Nat.card Γ = 60)
    (hsmall : ∀ K : Subgroup Γ, K.Normal → K ≠ ⊥ → 16 ≤ Nat.card K)
    (N : Subgroup Γ) (hN : Nat.card N = 12) :
    Nonempty (Γ ≃* alternatingGroup (Fin 5)) := by
  have hidx : N.index = 5 := by
    have := N.index_mul_card
    rw [hN, hΓ] at this; omega
  let ψ0 := MulAction.toPermHom Γ (Γ ⧸ N)
  have hle : ψ0.ker ≤ N := by
    intro g hg
    have h1 : ψ0 g ((1 : Γ) : Γ ⧸ N) = ((1 : Γ) : Γ ⧸ N) := by
      rw [MonoidHom.mem_ker.mp hg]; rfl
    change g • ((1 : Γ) : Γ ⧸ N) = ((1 : Γ) : Γ ⧸ N) at h1
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq] at h1
    simpa using h1
  have hker : ψ0.ker = ⊥ := by
    by_contra hne
    have h16 := hsmall _ inferInstance hne
    have := Subgroup.card_le_of_le hle
    omega
  have hinj : Function.Injective ψ0 := (MonoidHom.ker_eq_bot_iff _).mp hker
  let e : Γ ⧸ N ≃ Fin 5 := Finite.equivFinOfCardEq hidx
  let ψ : Γ →* Equiv.Perm (Fin 5) := (Equiv.permCongrHom e).toMonoidHom.comp ψ0
  have hψ : Function.Injective ψ := (Equiv.permCongrHom e).injective.comp hinj
  have hcard : Nat.card ψ.range = 60 := by
    rw [← hΓ]; exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  have hidx2 : ψ.range.index = 2 := by
    have h := ψ.range.index_mul_card
    rw [hcard, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have h120 : Nat.factorial 5 = 120 := rfl
    omega
  exact ⟨(MonoidHom.ofInjective hψ).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx2))⟩

/-- The normalizer of a Sylow `2`-subgroup `V` of order `4` is not `V` itself: otherwise
Burnside's transfer theorem gives a normal complement of order `15`. -/
lemma normalizer_card_ne_four (hΓ : Nat.card Γ = 60)
    (hsmall : ∀ K : Subgroup Γ, K.Normal → K ≠ ⊥ → 16 ≤ Nat.card K)
    (V : Sylow 2 Γ) (hV : Nat.card V = 4)
    (hN : Nat.card (Subgroup.normalizer ((V : Subgroup Γ) : Set Γ)) = 4) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVN : (V : Subgroup Γ) ≤ Subgroup.normalizer ((V : Subgroup Γ) : Set Γ) :=
    Subgroup.le_normalizer
  have hNV : Subgroup.normalizer ((V : Subgroup Γ) : Set Γ) = V :=
    (Subgroup.eq_of_le_of_card_ge hVN (by rw [hV, hN])).symm
  have hP : Subgroup.normalizer ((V : Subgroup Γ) : Set Γ) ≤
      Subgroup.centralizer ((V : Subgroup Γ) : Set Γ) := by
    intro x hx
    rw [hNV] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := IsPGroup.commutative_of_card_eq_prime_sq (p := 2) (G := (V : Subgroup Γ))
      (by rw [hV]; norm_num) ⟨y, hy⟩ ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hc := (MonoidHom.ker_transferSylow_isComplement' V hP).card_mul
  rw [hV, hΓ] at hc
  have hK : (MonoidHom.ker (MonoidHom.transferSylow V hP)) ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hc; norm_num at hc
  have := hsmall _ inferInstance hK
  omega

/-- An element of order `5` normalizing a subgroup of order `4` centralizes it. -/
lemma commute_of_normalizer_order_five (V : Subgroup Γ) (hV : Nat.card V = 4)
    (ρ : Subgroup.normalizer (V : Set Γ)) (hρ : orderOf ρ = 5) :
    ∀ v ∈ V, (ρ : Γ) * v * (ρ : Γ)⁻¹ = v := by
  have hVN : V ≤ Subgroup.normalizer (V : Set Γ) := Subgroup.le_normalizer
  let f : Subgroup.normalizer (V : Set Γ) →*
      Equiv.Perm (V.subgroupOf (Subgroup.normalizer (V : Set Γ))) :=
    MonoidHom.comp (MulAut.toPerm _) MulAut.conjNormal
  have hVsub : Nat.card (V.subgroupOf (Subgroup.normalizer (V : Set Γ))) = 4 := by
    rw [← hV]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv
  have hord1 : orderOf (f ρ) ∣ 5 := hρ ▸ orderOf_map_dvd f ρ
  have hord2 : orderOf (f ρ) ∣ 24 := by
    have := orderOf_dvd_natCard (f ρ)
    rwa [Nat.card_perm, hVsub] at this
  have hf1 : f ρ = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 5 24)
      hord1 hord2)
  intro v hv
  set x : V.subgroupOf (Subgroup.normalizer (V : Set Γ)) :=
    ⟨⟨v, hVN hv⟩, by simpa [Subgroup.mem_subgroupOf] using hv⟩
  have key : (MulAut.conjNormal ρ : MulAut (V.subgroupOf (Subgroup.normalizer (V : Set Γ)))) x
      = x := by
    have := congrArg (fun σ : Equiv.Perm _ => σ x) hf1
    exact this
  have := congrArg (fun y : V.subgroupOf (Subgroup.normalizer (V : Set Γ)) =>
    (((y : Subgroup.normalizer (V : Set Γ))) : Γ)) key
  simp only [MulAut.conjNormal_apply] at this
  simpa [x] using this

/-- **Recognition of `A₅`.** A group of order `60` in which every nontrivial normal subgroup has
at least `16` elements, and no element of order `5` centralizes a subgroup of order `4`, is
isomorphic to `A₅`. -/
theorem alternating_five_of (hΓ : Nat.card Γ = 60)
    (hsmall : ∀ K : Subgroup Γ, K.Normal → K ≠ ⊥ → 16 ≤ Nat.card K)
    (hnot5 : ∀ V : Subgroup Γ, Nat.card V = 4 → ∀ ρ : Γ, orderOf ρ = 5 →
      (∀ v ∈ V, ρ * v * ρ⁻¹ = v) → False) :
    Nonempty (Γ ≃* alternatingGroup (Fin 5)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨V⟩ := (inferInstance : Nonempty (Sylow 2 Γ))
  have hV := card_sylow_two hΓ V
  have hVN : (V : Subgroup Γ) ≤ Subgroup.normalizer ((V : Subgroup Γ) : Set Γ) :=
    Subgroup.le_normalizer
  have hVne : (V : Subgroup Γ) ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hV; norm_num at hV
  have h4 : 4 ∣ Nat.card (Subgroup.normalizer ((V : Subgroup Γ) : Set Γ)) :=
    hV ▸ Subgroup.card_dvd_of_le hVN
  have h60 : Nat.card (Subgroup.normalizer ((V : Subgroup Γ) : Set Γ)) ∣ 60 :=
    hΓ ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, hj⟩ := h4
  have hj15 : j ∣ 15 := by
    rw [hj] at h60
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4)
      (by rw [show (60 : ℕ) = 4 * 15 from rfl] at h60; exact h60)
  have hjle : j ≤ 15 := Nat.le_of_dvd (by norm_num : 0 < 15) hj15
  interval_cases j <;> norm_num at hj15
  · exact (normalizer_card_ne_four hΓ hsmall V hV (by omega)).elim
  · exact alternating_five_of_card_twelve hΓ hsmall _ (by omega)
  · exfalso
    obtain ⟨ρ, hρ⟩ := exists_prime_orderOf_dvd_card'
      (G := Subgroup.normalizer ((V : Subgroup Γ) : Set Γ)) 5 (by rw [hj]; norm_num)
    have hc := commute_of_normalizer_order_five (V : Subgroup Γ) hV ρ hρ
    have hρ' : orderOf (ρ : Γ) = 5 := by rw [Subgroup.orderOf_coe, hρ]
    exact hnot5 (V : Subgroup Γ) hV (ρ : Γ) hρ' hc
  · exfalso
    have hNtop : Subgroup.normalizer ((V : Subgroup Γ) : Set Γ) = ⊤ :=
      (Subgroup.card_eq_iff_eq_top _).mp (by rw [hj, hΓ])
    have := hsmall _ (Subgroup.normalizer_eq_top_iff.mp hNtop) hVne
    omega

end GroupTheory60

/-! ### Stage 3b: stabilizers of poles, and the cyclic case -/

section Identification

variable {G : Subgroup SO3}

/-- The stabilizer of a pole is cyclic. -/
theorem isCyclic_stabilizer [Finite G] (p : Poles G) :
    IsCyclic (MulAction.stabilizer G p) := by
  refine isCyclic_of_common_fixed (G.subtype.comp (MulAction.stabilizer G p).subtype)
    (G.subtype_injective.comp (MulAction.stabilizer G p).subtype_injective) p.2.1 ?_
  intro h
  exact congrArg Subtype.val h.2

lemma mem_signature [Finite G] {n : ℕ} : n ∈ signature G ↔ ∃ ω : Orbits G, orbitOrder ω = n := by
  simp [signature]

/-- **Cyclic case.** If some pole is fixed by all of `G`, then `G ≅ ℤ_N`. -/
theorem cyclic_of_orbitOrder_eq [Finite G] (ω : Orbits G) (h : orbitOrder ω = Nat.card G) :
    Nonempty (G ≃* Multiplicative (ZMod (Nat.card G))) := by
  have htop : MulAction.stabilizer G ω.out = ⊤ := (Subgroup.card_eq_iff_eq_top _).mp h
  have hcyc : IsCyclic G := by
    refine isCyclic_of_common_fixed G.subtype G.subtype_injective ω.out.2.1 fun g => ?_
    have hg : g ∈ MulAction.stabilizer G ω.out := htop ▸ Subgroup.mem_top g
    exact congrArg Subtype.val hg
  exact ⟨(zmodCyclicMulEquiv hcyc).symm⟩

/-! ### Stage 3c: the dihedral case -/

/-- An element outside the stabilizer of a pole of index two sends the pole to its antipode. -/
lemma smul_eq_neg_of_not_mem [Finite G] (p : Poles G)
    (hidx : (MulAction.stabilizer G p).index = 2) {s : G}
    (hs : s ∉ MulAction.stabilizer G p) : ((s : SO3) : M3) *ᵥ p.1 = -p.1 := by
  set H := MulAction.stabilizer G p
  have hN : H.Normal := Subgroup.normal_of_index_eq_two hidx
  have hne : H ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot H).mp (one_lt_card_stabilizer p)
  obtain ⟨h, h1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have h1' : ((h : G) : SO3) ≠ 1 := fun e => h1 (Subtype.ext (Subtype.ext e))
  obtain ⟨w, -, -, hw⟩ := fixed_units_of_ne_one ((h : G) : SO3) h1'
  have hfixp : (((h : G) : SO3) : M3) *ᵥ p.1 = p.1 := congrArg Subtype.val h.2
  have hc : s⁻¹ * (h : G) * s ∈ H := by simpa using hN.conj_mem _ h.2 s⁻¹
  have hfixsp : (((h : G) : SO3) : M3) *ᵥ (((s : SO3) : M3) *ᵥ p.1) =
      ((s : SO3) : M3) *ᵥ p.1 := by
    have e := congrArg Subtype.val hc
    change (((s⁻¹ * (h : G) * s : G) : SO3) : M3) *ᵥ p.1 = p.1 at e
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_mul_mulVec, coe_mul_mulVec,
      Subgroup.coe_inv, ← mulVec_eq_iff_inv] at e
    exact e.symm
  have hu := (hw p.1).mp ⟨p.2.1, hfixp⟩
  have hsu := (hw _).mp ⟨by rw [dot_mulVec]; exact p.2.1, hfixsp⟩
  have hne' : ((s : SO3) : M3) *ᵥ p.1 ≠ p.1 := fun e => hs (Subtype.ext e)
  rcases hu with hu | hu <;> rcases hsu with hsu | hsu
  · exact absurd (hsu.trans hu.symm) hne'
  · rw [hsu, hu]
  · rw [hsu, hu, neg_neg]
  · exact absurd (hsu.trans hu.symm) hne'

/-- An element outside the stabilizer of a pole of index two is an involution. -/
lemma mul_self_eq_one_of_not_mem [Finite G] (p : Poles G)
    (hidx : (MulAction.stabilizer G p).index = 2) {s : G}
    (hs : s ∉ MulAction.stabilizer G p) : s * s = 1 := by
  have hsp := smul_eq_neg_of_not_mem p hidx hs
  obtain ⟨w, hw1, hsw⟩ := exists_unit_fixed (s : SO3)
  have hwp : w ⬝ᵥ p.1 = 0 := by
    have := dot_mulVec (s : SO3) w p.1
    rw [hsw, hsp, dotProduct_neg] at this
    linarith
  have hcross : w ⨯₃ p.1 ≠ 0 := by
    intro h0
    have := cross_dot_self w p.1
    rw [h0, zero_dotProduct, hw1, p.2.1, hwp] at this
    norm_num at this
  have : ((s * s : G) : SO3) = 1 := by
    refine eq_one_of_fixes _ hcross ?_ ?_
    · rw [Subgroup.coe_mul, coe_mul_mulVec, hsw, hsw]
    · rw [Subgroup.coe_mul, coe_mul_mulVec, hsp, Matrix.mulVec_neg, hsp, neg_neg]
  exact Subtype.ext this

/-- **Recognition of dihedral groups.** A finite group with a cyclic subgroup `H` of index two
all of whose non-elements are involutions is isomorphic to `D_{|H|}`. -/
theorem dihedral_of_index_two {K : Type*} [Group K] [Finite K] (H : Subgroup K)
    (hidx : H.index = 2) [hcyc : IsCyclic H] (hinv : ∀ s, s ∉ H → s * s = 1) :
    Nonempty (K ≃* DihedralGroup (Nat.card H)) := by
  set n := Nat.card H with hn
  haveI : NeZero n := ⟨Nat.card_pos.ne'⟩
  obtain ⟨ρ, hρ⟩ := IsCyclic.exists_generator (α := H)
  set r0 : K := (ρ : K)
  have hord : orderOf r0 = n := by
    rw [Subgroup.orderOf_coe]; exact orderOf_eq_card_of_forall_mem_zpowers hρ
  let gp : ZMod n → K := fun i => r0 ^ i.val
  have gp_add : ∀ i j, gp (i + j) = gp i * gp j := by
    intro i j
    simp only [gp, ← pow_add]
    rw [pow_eq_pow_iff_modEq, hord, ZMod.val_add]
    exact Nat.mod_modEq _ _
  have gp_zero : gp 0 = 1 := by simp [gp]
  have gp_neg : ∀ i, gp (-i) = (gp i)⁻¹ := fun i =>
    eq_inv_of_mul_eq_one_left (by rw [← gp_add, neg_add_cancel, gp_zero])
  have gp_mem : ∀ i, gp i ∈ H := fun i => H.pow_mem ρ.2 _
  obtain ⟨s, hs⟩ : ∃ s, s ∉ H := by
    by_contra hall
    push Not at hall
    have : H = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [this, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  have hss := hinv s hs
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have rel : ∀ x ∈ H, x * s = s * x⁻¹ := by
    intro x hx
    have hsx : s * x ∉ H := fun h => hs (by simpa using H.mul_mem h (H.inv_mem hx))
    have h := hinv _ hsx
    calc x * s = s⁻¹ * (s * x * (s * x)) * x⁻¹ := by group
      _ = s * x⁻¹ := by rw [h, hs']; group
  let f : DihedralGroup n → K := fun
    | .r i => gp i
    | .sr i => s * gp i
  have fmul : ∀ a b, f (a * b) = f a * f b := by
    rintro (i | i) (j | j)
    · change gp (i + j) = gp i * gp j
      exact gp_add i j
    · change s * gp (j - i) = gp i * (s * gp j)
      rw [← mul_assoc, rel _ (gp_mem i), sub_eq_neg_add, gp_add, gp_neg, mul_assoc]
    · change s * gp (i + j) = s * gp i * gp j
      rw [gp_add, mul_assoc]
    · change gp (j - i) = s * gp i * (s * gp j)
      rw [sub_eq_neg_add, gp_add, gp_neg]
      calc (gp i)⁻¹ * gp j = s * s * (gp i)⁻¹ * gp j := by rw [hss, one_mul]
        _ = s * (s * (gp i)⁻¹) * gp j := by group
        _ = s * gp i * (s * gp j) := by rw [← rel _ (gp_mem i)]; group
  let F : DihedralGroup n →* K := MonoidHom.mk' f fmul
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    rintro (i | i) h
    · change r0 ^ i.val = 1 at h
      have hd := orderOf_dvd_of_pow_eq_one h
      rw [hord] at hd
      have : i.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt i)
      rw [ZMod.val_eq_zero] at this
      rw [this, DihedralGroup.r_zero]
    · change s * gp i = 1 at h
      exact absurd (by rw [eq_inv_of_mul_eq_one_left h]; exact H.inv_mem (gp_mem i)) hs
  have hcard : Nat.card (DihedralGroup n) = Nat.card K := by
    rw [DihedralGroup.nat_card, ← H.index_mul_card, hidx]
  exact ⟨(MulEquiv.ofBijective F ((Nat.bijective_iff_injective_and_card F).mpr
    ⟨hinj, hcard⟩)).symm⟩

/-- **Dihedral case.** If `G` has a pole whose stabilizer has index two, then `G ≅ D_n` with
`n` the order of that stabilizer. -/
theorem dihedral_of_stabilizer_index_two [Finite G] (p : Poles G)
    (hidx : (MulAction.stabilizer G p).index = 2) :
    Nonempty (G ≃* DihedralGroup (Nat.card (MulAction.stabilizer G p))) := by
  haveI := isCyclic_stabilizer p
  exact dihedral_of_index_two _ hidx fun s hs => mul_self_eq_one_of_not_mem p hidx hs

/-! ### Stage 3d: the tetrahedral case -/

/-- A non-identity element fixes at most two unit vectors: if `g` fixes every point of a set of
at least three poles, then `g = 1`. -/
lemma eq_one_of_fixes_three [Finite G] (S : Set (Poles G)) (hS : 3 ≤ Nat.card S) (g : G)
    (hg : ∀ q ∈ S, g • q = q) : g = 1 := by
  by_contra hne
  have hne' : (g : SO3) ≠ 1 := fun e => hne (Subtype.ext e)
  obtain ⟨w, -, -, hw⟩ := fixed_units_of_ne_one (g : SO3) hne'
  let ι : S → ({w, -w} : Set V3) := fun q =>
    ⟨q.1.1, by
      have := (hw q.1.1).mp ⟨q.1.2.1, congrArg Subtype.val (hg q.1 q.2)⟩
      simpa using this⟩
  have hι : Function.Injective ι := by
    intro a b hab
    have h' := Subtype.ext_iff.mp hab
    exact Subtype.ext (Subtype.ext h')
  have h1 := Nat.card_le_card_of_injective ι hι
  have h2 : Nat.card ({w, -w} : Set V3) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le w {-w}).trans (by rw [Set.ncard_singleton])
  omega

lemma card_orbit_mul [Finite G] (p : Poles G) :
    Nat.card (MulAction.orbit G p) * Nat.card (MulAction.stabilizer G p) = Nat.card G := by
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, Subgroup.index_mul_card]

/-- The permutation representation of `G` on an orbit of at least three poles is faithful. -/
lemma toPermHom_orbit_injective [Finite G] (p : Poles G)
    (h3 : 3 ≤ Nat.card (MulAction.orbit G p)) :
    Function.Injective (MulAction.toPermHom G (MulAction.orbit G p)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine eq_one_of_fixes_three (MulAction.orbit G p) h3 g fun q hq => ?_
  have := congrArg (fun σ : Equiv.Perm (MulAction.orbit G p) => (σ ⟨q, hq⟩ : Poles G)) hg
  exact this

/-- **Tetrahedral case.** If `|G| = 12` and some orbit of poles has four elements, then
`G ≅ A₄`. -/
theorem alternating_four_of_orbit [Finite G] (p : Poles G)
    (hO : Nat.card (MulAction.orbit G p) = 4) (hG : Nat.card G = 12) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  let e : MulAction.orbit G p ≃ Fin 4 := Finite.equivFinOfCardEq hO
  let ψ : G →* Equiv.Perm (Fin 4) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom G (MulAction.orbit G p))
  have hψ : Function.Injective ψ :=
    (Equiv.permCongrHom e).injective.comp (toPermHom_orbit_injective p (by omega))
  have hcard : Nat.card ψ.range = 12 := by
    rw [← hG]; exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  have hidx : ψ.range.index = 2 := by
    have h := ψ.range.index_mul_card
    rw [hcard, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    norm_num [Nat.factorial] at h
    omega
  exact ⟨(MonoidHom.ofInjective hψ).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx))⟩

/-! ### Stage 3e: the octahedral case -/

/-- The antipode of a pole. -/
def Poles.neg (q : Poles G) : Poles G :=
  ⟨-q.1, by simpa using q.2.1, by
    obtain ⟨-, g, hg, hne, hgq⟩ := q.2
    exact ⟨g, hg, hne, by rw [Matrix.mulVec_neg, hgq]⟩⟩

@[simp] lemma Poles.neg_val (q : Poles G) : q.neg.1 = -q.1 := rfl

lemma Poles.smul_neg (g : G) (q : Poles G) : g • q.neg = (g • q).neg :=
  Subtype.ext (show ((g : SO3) : M3) *ᵥ (-q.1) = -(((g : SO3) : M3) *ᵥ q.1) from
    Matrix.mulVec_neg _ _)

lemma Poles.neg_neg (q : Poles G) : q.neg.neg = q := Subtype.ext (_root_.neg_neg _)

lemma Poles.neg_ne (q : Poles G) : q.neg ≠ q := fun h =>
  ne_neg_of_unit q.2.1 (congrArg Subtype.val h).symm

lemma Poles.neg_injective : Function.Injective (Poles.neg (G := G)) := fun a b h => by
  rw [← Poles.neg_neg a, h, Poles.neg_neg]

lemma stabilizer_neg (q : Poles G) :
    MulAction.stabilizer G q.neg = MulAction.stabilizer G q := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, Poles.smul_neg]
  exact Poles.neg_injective.eq_iff

/-- Two poles that are neither equal nor antipodal span a plane. -/
lemma cross_ne_zero_of_poles {q w : Poles G} (h1 : w ≠ q) (h2 : w ≠ q.neg) :
    q.1 ⨯₃ w.1 ≠ 0 := fun h0 => by
  rcases eq_or_eq_neg_of_cross_eq_zero q.2.1 w.2.1 h0 with h | h
  · exact h1 (Subtype.ext h)
  · exact h2 (Subtype.ext h)

lemma eq_one_of_fixes_poles {q w : Poles G} (h1 : w ≠ q) (h2 : w ≠ q.neg) (g : G)
    (hq : g • q = q) (hw : g • w = w) : g = 1 :=
  Subtype.ext (eq_one_of_fixes (g : SO3) (cross_ne_zero_of_poles h1 h2)
    (congrArg Subtype.val hq) (congrArg Subtype.val hw))

lemma card_stabilizer_of_mem_orbit {q r : Poles G} (h : q ∈ MulAction.orbit G r) :
    Nat.card (MulAction.stabilizer G q) = Nat.card (MulAction.stabilizer G r) :=
  Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv

lemma exists_third [Finite G] (S : Set (Poles G)) (hS : 3 ≤ Nat.card S) (q : Poles G) :
    ∃ w ∈ S, w ≠ q ∧ w ≠ q.neg := by
  by_contra hall
  push Not at hall
  have hsub : S ⊆ {q, q.neg} := fun w hw => by
    by_cases h : w = q
    · exact Or.inl h
    · exact Or.inr (hall w hw h)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({q, q.neg} : Set (Poles G)).ncard ≤ 2 :=
    (Set.ncard_insert_le q {q.neg}).trans (by rw [Set.ncard_singleton])
  rw [Nat.card_coe_set_eq] at hS
  omega

/-- **Kernel lemma for the octahedral case.** Let `S` be a `G`-stable set of at least three
poles, each with stabilizer of order three. An element of `G` sending every pole of `S` to
itself or to its antipode is the identity. -/
lemma eq_one_of_fix_or_neg [Finite G] (S : Set (Poles G)) (hS : 3 ≤ Nat.card S)
    (hstab : ∀ x : G, ∀ q ∈ S, x • q ∈ S)
    (h3 : ∀ q ∈ S, Nat.card (MulAction.stabilizer G q) = 3)
    (g : G) (hg : ∀ q ∈ S, g • q = q ∨ g • q = q.neg) : g = 1 := by
  have hcube : ∀ x : G, ∀ q ∈ S, x • q = q → x ^ 3 = 1 := by
    intro x q hq hxq
    have := pow_card_eq_one' (G := MulAction.stabilizer G q) (x := ⟨x, hxq⟩)
    rw [h3 q hq] at this
    exact congrArg Subtype.val this
  have hnonempty : ∃ q, q ∈ S := by
    by_contra h0
    push Not at h0
    have : S = ∅ := Set.eq_empty_of_forall_notMem h0
    rw [this] at hS; simp at hS
  obtain ⟨q₀, hq₀⟩ := hnonempty
  by_cases hfix : ∃ q ∈ S, g • q = q
  · -- `g` fixes a pole of `S`: then `g³ = 1` and `g` fixes or negates a non-parallel pole.
    obtain ⟨q, hq, hgq⟩ := hfix
    obtain ⟨w, hw, hw1, hw2⟩ := exists_third S hS q
    rcases hg w hw with hgw | hgw
    · exact eq_one_of_fixes_poles hw1 hw2 g hgq hgw
    · have hg2 : g ^ 2 = 1 := by
        refine eq_one_of_fixes_poles hw1 hw2 _ ?_ ?_
        · rw [pow_two, mul_smul, hgq, hgq]
        · rw [pow_two, mul_smul, hgw, Poles.smul_neg, hgw, Poles.neg_neg]
      have hg3 := hcube g q hq hgq
      calc g = g ^ 3 * (g ^ 2)⁻¹ := by group
        _ = 1 := by rw [hg3, hg2]; group
  · push Not at hfix
    have hneg : ∀ q ∈ S, g • q = q.neg := fun q hq =>
      (hg q hq).resolve_left (hfix q hq)
    by_contra hne
    -- pick a nontrivial rotation `ρ` about `q₀`
    have hne_bot : MulAction.stabilizer G q₀ ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, h3 q₀ hq₀]; norm_num
    obtain ⟨ρ', hρ'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne_bot
    set ρ : G := ρ'.1
    have hρq : ρ • q₀ = q₀ := ρ'.2
    have hρ1 : ρ ≠ 1 := fun h => hρ' (Subtype.ext h)
    -- `ρ` commutes with `g`
    have hcomm : g⁻¹ * (ρ * g * ρ⁻¹) = 1 := by
      refine eq_one_of_fixes_three S (by omega) _ fun q hq => ?_
      have hq' : ρ⁻¹ • q ∈ S := hstab _ _ hq
      have hgq : g • q = q.neg := hneg q hq
      rw [mul_smul, mul_smul, mul_smul, hneg _ hq', Poles.smul_neg, smul_inv_smul,
        inv_smul_eq_iff, hgq]
    have hcomm' : ρ * g = g * ρ := by
      have := congrArg (g * · * ρ) hcomm
      simpa [mul_assoc] using this
    have hg1 : (g : SO3) ≠ 1 := fun h => hne (Subtype.ext h)
    obtain ⟨x, hx1, hgx, hfixg⟩ := fixed_units_of_ne_one (g : SO3) hg1
    have hgq₀ : ((g : SO3) : M3) *ᵥ q₀.1 = -q₀.1 := congrArg Subtype.val (hneg q₀ hq₀)
    have hcross : q₀.1 ⨯₃ x ≠ 0 := by
      intro h0
      rcases eq_or_eq_neg_of_cross_eq_zero q₀.2.1 hx1 h0 with h | h
      · rw [h, hgq₀] at hgx; exact ne_neg_of_unit q₀.2.1 hgx.symm
      · rw [h, Matrix.mulVec_neg, hgq₀, _root_.neg_neg] at hgx
        exact ne_neg_of_unit q₀.2.1 hgx
    have hρq' : ((ρ : SO3) : M3) *ᵥ q₀.1 = q₀.1 := congrArg Subtype.val hρq
    have hρx : ((ρ : SO3) : M3) *ᵥ x = x ∨ ((ρ : SO3) : M3) *ᵥ x = -x := by
      refine (hfixg _).mp ⟨by rw [dot_mulVec, hx1], ?_⟩
      rw [← coe_mul_mulVec, ← Subgroup.coe_mul, ← hcomm', Subgroup.coe_mul, coe_mul_mulVec, hgx]
    rcases hρx with h | h
    · exact hρ1 (Subtype.ext (eq_one_of_fixes _ hcross hρq' h))
    · have hρ2 : ρ ^ 2 = 1 := by
        refine Subtype.ext (eq_one_of_fixes _ hcross ?_ ?_)
        · rw [pow_two, Subgroup.coe_mul, coe_mul_mulVec, hρq', hρq']
        · rw [pow_two, Subgroup.coe_mul, coe_mul_mulVec, h, Matrix.mulVec_neg, h,
            _root_.neg_neg]
      have hρ3 := hcube ρ q₀ hq₀ hρq
      exact hρ1 (calc ρ = ρ ^ 3 * (ρ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hρ3, hρ2]; group)

lemma count_signature [Finite G] (k : ℕ) :
    (signature G).count k = (Finset.univ.filter fun ω : Orbits G => orbitOrder ω = k).card := by
  classical
  rw [signature, Multiset.count_map, Finset.card, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun _ _ => eq_comm

/-- If the stabilizer order of an orbit occurs once in the signature, the orbit is closed under
the antipodal map. -/
lemma neg_mem_orbit_of_count [Finite G] (ω : Orbits G)
    (hc : (signature G).count (orbitOrder ω) = 1) :
    ω.out.neg ∈ MulAction.orbit G ω.out := by
  classical
  set ω' : Orbits G := Quotient.mk'' ω.out.neg with hω'
  have hord : orbitOrder ω' = orbitOrder ω := by
    unfold orbitOrder
    rw [card_stabilizer_of_mem_orbit (Quotient.mk_out' (s₁ := MulAction.orbitRel G (Poles G))
      ω.out.neg), stabilizer_neg]
  rw [count_signature] at hc
  have heq : ω' = ω := Finset.card_le_one.mp hc.le ω' (by simp [hord]) ω (by simp)
  have : (Quotient.mk'' ω.out.neg : Orbits G) = Quotient.mk'' ω.out := by
    rw [← hω', heq, Quotient.out_eq']
  exact Quotient.eq''.mp this

lemma card_orbit_mul_card_stabilizer {X : Type*} [MulAction G X] (x : X) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, Subgroup.index_mul_card]

open scoped Pointwise in
/-- **Octahedral case.** If `|G| = 24` and some pole `p` has stabilizer of order three and
antipode in its orbit, then `G ≅ S₄`, via the action on the four axes through the orbit. -/
theorem perm_four_of_orbit [Finite G] (p : Poles G) (hG : Nat.card G = 24)
    (h3 : Nat.card (MulAction.stabilizer G p) = 3) (hneg : p.neg ∈ MulAction.orbit G p) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  classical
  set O := MulAction.orbit G p with hOdef
  have hO : Nat.card O = 8 := by
    have : Nat.card O * 3 = 24 := by
      rw [← h3, ← hG]; exact card_orbit_mul_card_stabilizer (G := G) p
    omega
  set A0 : Set (Poles G) := {p, p.neg} with hA0
  have smulA0 : ∀ x : G, x • A0 = {x • p, (x • p).neg} := by
    intro x
    rw [hA0, Set.smul_set_insert, Set.smul_set_singleton, Poles.smul_neg]
  set Ax := MulAction.orbit G A0
  -- the stabilizer of the axis `A0` is strictly bigger than that of `p`
  have hle : MulAction.stabilizer G p ≤ MulAction.stabilizer G A0 := by
    intro x hx
    rw [MulAction.mem_stabilizer_iff] at hx ⊢
    rw [smulA0, hx]
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hneg
  have hhA : h ∈ MulAction.stabilizer G A0 := by
    rw [MulAction.mem_stabilizer_iff, smulA0, hh, Poles.neg_neg, Set.pair_comm]
  have hhp : h ∉ MulAction.stabilizer G p := fun hm => by
    rw [MulAction.mem_stabilizer_iff, hh] at hm
    exact Poles.neg_ne p hm
  have hdvd : 3 ∣ Nat.card (MulAction.stabilizer G A0) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [h3] at this
  have hne3 : Nat.card (MulAction.stabilizer G A0) ≠ 3 := fun he =>
    hhp ((Subgroup.eq_of_le_of_card_ge hle (by rw [he, h3])) ▸ hhA)
  have hAx : Nat.card Ax * Nat.card (MulAction.stabilizer G A0) = 24 := by
    rw [← hG]; exact card_orbit_mul_card_stabilizer (G := G) A0
  have hAx_le : Nat.card Ax ≤ 4 := by
    obtain ⟨c, hc⟩ := hdvd
    obtain ⟨k, hk⟩ : ∃ k, Nat.card Ax = k := ⟨_, rfl⟩
    rw [hc, hk] at hAx
    rw [hc] at hne3
    rw [hk]
    have : c ≠ 1 := fun h1 => hne3 (by rw [h1])
    have : c ≠ 0 := fun h0 => by rw [h0] at hAx; simp at hAx
    by_contra hlt
    have : 5 * (3 * 2) ≤ k * (3 * c) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left 3 (by omega))
    omega
  -- faithfulness of the action on axes
  have hinj : Function.Injective (MulAction.toPermHom G Ax) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hfixA : ∀ A ∈ Ax, g • A = A := fun A hA => by
      have := congrArg (fun σ : Equiv.Perm Ax => (σ ⟨A, hA⟩ : Set (Poles G))) hg
      exact this
    refine eq_one_of_fix_or_neg O (by omega) (fun x q hq => MulAction.mem_orbit_of_mem_orbit x hq)
      (fun q hq => (card_stabilizer_of_mem_orbit hq).trans h3) g fun q hq => ?_
    obtain ⟨x, rfl⟩ := MulAction.mem_orbit_iff.mp hq
    have hA : x • A0 ∈ Ax := MulAction.mem_orbit A0 x
    have hmem : g • (x • p) ∈ g • (x • A0) := Set.smul_mem_smul_set (by rw [smulA0]; simp)
    rw [hfixA _ hA, smulA0] at hmem
    simpa using hmem
  have hAx4 : Nat.card Ax = 4 := by
    have hle' := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm, hG] at hle'
    obtain ⟨k, hk⟩ : ∃ k, Nat.card Ax = k := ⟨_, rfl⟩
    rw [hk] at hle' ⊢
    by_contra hne
    have h3' : k ≤ 3 := by omega
    have := Nat.factorial_le h3'
    have h6 : Nat.factorial 3 = 6 := rfl
    omega
  let e : Ax ≃ Fin 4 := Finite.equivFinOfCardEq hAx4
  let ψ : G →* Equiv.Perm (Fin 4) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom G Ax)
  have hψ : Function.Injective ψ := (Equiv.permCongrHom e).injective.comp hinj
  have hcard : Nat.card G = Nat.card (Equiv.Perm (Fin 4)) := by
    rw [hG, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  exact ⟨MulEquiv.ofBijective ψ ((Nat.bijective_iff_injective_and_card ψ).mpr ⟨hψ, hcard⟩)⟩

/-! ### Stage 3f: the icosahedral case -/

lemma card_stab_mem_signature [Finite G] (q : Poles G) :
    Nat.card (MulAction.stabilizer G q) ∈ signature G := by
  rw [mem_signature]
  refine ⟨Quotient.mk'' q, ?_⟩
  unfold orbitOrder
  exact card_stabilizer_of_mem_orbit (Quotient.mk_out' (s₁ := MulAction.orbitRel G (Poles G)) q)

/-- In an icosahedral-type group, every pole stabilizer has order `2`, `3` or `5`. -/
lemma card_stab_cases [Finite G] (hsig : signature G = {2, 3, 5}) (q : Poles G) :
    Nat.card (MulAction.stabilizer G q) = 2 ∨ Nat.card (MulAction.stabilizer G q) = 3 ∨
      Nat.card (MulAction.stabilizer G q) = 5 := by
  have := card_stab_mem_signature q
  rw [hsig] at this
  simpa using this

/-- Every non-identity element fixes a pole. -/
lemma exists_pole_fixed (g : G) (hg : g ≠ 1) : ∃ q : Poles G, g • q = q := by
  have hg' : (g : SO3) ≠ 1 := fun h => hg (Subtype.ext h)
  obtain ⟨u, hu, hgu, -⟩ := fixed_units_of_ne_one (g : SO3) hg'
  exact ⟨⟨u, hu, g, g.2, hg', hgu⟩, Subtype.ext hgu⟩

/-- Double counting of pairs `(x, v)` with `1 ≠ x ∈ K` fixing the pole `v ∈ O`. -/
lemma double_count [Finite G] (K : Subgroup G) (O : Set (Poles G)) (n : ℕ)
    (hOK : ∀ v ∈ O, ∀ x ∈ MulAction.stabilizer G v, x ∈ K)
    (hn : ∀ v ∈ O, Nat.card (MulAction.stabilizer G v) = n) :
    Nat.card O * (n - 1) ≤ (Nat.card K - 1) * 2 := by
  classical
  haveI : Fintype G := Fintype.ofFinite _
  haveI : Fintype (Poles G) := Fintype.ofFinite _
  set Kf : Finset G := Finset.univ.filter fun x => x ∈ K ∧ x ≠ 1
  set Of : Finset (Poles G) := O.toFinset
  have hcomm : ∑ x ∈ Kf, (Of.filter fun v => x • v = v).card =
      ∑ v ∈ Of, (Kf.filter fun x => x • v = v).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hKf : Kf.card + 1 = Nat.card K := by
    have h1 : Kf = (Finset.univ.filter fun x => x ∈ K).erase 1 := by
      ext x; simp [Kf, and_comm]
    rw [h1, Finset.card_erase_of_mem (by simp [K.one_mem]), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    have : 0 < (Finset.univ.filter fun x => x ∈ K).card :=
      Finset.card_pos.mpr ⟨1, by simp [K.one_mem]⟩
    omega
  have hle : ∀ x ∈ Kf, (Of.filter fun v => x • v = v).card ≤ 2 := by
    intro x hx
    have hx1 : x ≠ 1 := (Finset.mem_filter.mp hx).2.2
    calc (Of.filter fun v => x • v = v).card
        = Set.ncard (↑(Of.filter fun v => x • v = v) : Set (Poles G)) :=
          (Set.ncard_coe_finset _).symm
      _ ≤ (MulAction.fixedBy (Poles G) x).ncard :=
          Set.ncard_le_ncard (fun v hv => by simpa using (Finset.mem_filter.mp hv).2)
            (Set.toFinite _)
      _ = 2 := by rw [← Nat.card_coe_set_eq]; exact card_fixedBy_of_ne_one x hx1
  have heq : ∀ v ∈ Of, (Kf.filter fun x => x • v = v).card = n - 1 := by
    intro v hv
    have hvO : v ∈ O := Set.mem_toFinset.mp hv
    have h1 : Kf.filter (fun x => x • v = v) =
        (Finset.univ.filter fun x => x ∈ MulAction.stabilizer G v).erase 1 := by
      ext x
      simp only [Kf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨hOK v hvO x (MulAction.mem_stabilizer_iff.mpr h2), h1⟩, h2⟩
    rw [h1, Finset.card_erase_of_mem (by simp)]
    have hc : (Finset.univ.filter fun x => x ∈ MulAction.stabilizer G v).card = n := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact hn v hvO
    rw [hc]
  have hL := Finset.sum_le_card_nsmul Kf (fun x => (Of.filter fun v => x • v = v).card) 2 hle
  rw [hcomm, Finset.sum_congr rfl heq, Finset.sum_const, Set.toFinset_card,
    ← Nat.card_eq_fintype_card] at hL
  simp only [smul_eq_mul] at hL
  rw [← hKf, Nat.add_sub_cancel]
  exact hL

/-- **No small normal subgroups.** In a group of order `60` with signature `(2, 3, 5)`, every
nontrivial normal subgroup has at least `16` elements. -/
lemma sixteen_le_card_normal [Finite G] (hG : Nat.card G = 60) (hsig : signature G = {2, 3, 5})
    (K : Subgroup G) [hKn : K.Normal] (hK : K ≠ ⊥) : 16 ≤ Nat.card K := by
  obtain ⟨k', hk'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK
  set k : G := k'.1
  have hk1 : k ≠ 1 := fun h => hk' (Subtype.ext h)
  obtain ⟨q, hkq⟩ := exists_pole_fixed k hk1
  obtain ⟨n, hn⟩ : ∃ n, Nat.card (MulAction.stabilizer G q) = n := ⟨_, rfl⟩
  have hncases := card_stab_cases hsig q
  rw [hn] at hncases
  have hprime : n.Prime := by
    rcases hncases with h | h | h <;> rw [h] <;> norm_num
  haveI := Fact.mk hprime
  -- the stabilizer of `q` is generated by `k`, hence lies in `K`
  have hstabK : ∀ x ∈ MulAction.stabilizer G q, x ∈ K := by
    intro x hx
    have hne : (⟨k, hkq⟩ : MulAction.stabilizer G q) ≠ 1 := fun h =>
      hk1 (congrArg Subtype.val h)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card hn (g' := ⟨x, hx⟩) hne)
    have := congrArg Subtype.val hm
    simp only [Subgroup.coe_zpow] at this
    rw [← this]
    exact K.zpow_mem k'.2 m
  have horbK : ∀ v ∈ MulAction.orbit G q, ∀ x ∈ MulAction.stabilizer G v, x ∈ K := by
    intro v hv x hx
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hv
    have h1 : g⁻¹ * x * g ∈ MulAction.stabilizer G q := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul,
        (MulAction.mem_stabilizer_iff.mp hx), inv_smul_smul]
    have := hKn.conj_mem _ (hstabK _ h1) g
    simpa [mul_assoc] using this
  have hOn : Nat.card (MulAction.orbit G q) * n = 60 := by
    rw [← hG, ← hn]; exact card_orbit_mul_card_stabilizer (G := G) q
  have hL := double_count K (MulAction.orbit G q) n horbK
    (fun v hv => (card_stabilizer_of_mem_orbit hv).trans hn)
  rcases hncases with h | h | h <;> rw [h] at hOn hL <;> omega

/-- Two poles fixed by the same non-identity element are equal or antipodal. -/
lemma pole_eq_or_neg_of_fixed {x : G} (hx : x ≠ 1) {a b : Poles G} (ha : x • a = a)
    (hb : x • b = b) : b = a ∨ b = a.neg := by
  have hx' : (x : SO3) ≠ 1 := fun h => hx (Subtype.ext h)
  obtain ⟨u, -, -, hu⟩ := fixed_units_of_ne_one (x : SO3) hx'
  have h1 := (hu a.1).mp ⟨a.2.1, congrArg Subtype.val ha⟩
  have h2 := (hu b.1).mp ⟨b.2.1, congrArg Subtype.val hb⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left; exact Subtype.ext (h2.trans h1.symm)
  · right; exact Subtype.ext (by rw [h2, Poles.neg_val, h1])
  · right; exact Subtype.ext (by rw [h2, Poles.neg_val, h1, _root_.neg_neg])
  · left; exact Subtype.ext (h2.trans h1.symm)

lemma orderOf_dvd_card_stab {x : G} {q : Poles G} (hx : x • q = q) [Finite G] :
    orderOf x ∣ Nat.card (MulAction.stabilizer G q) := by
  have h := orderOf_dvd_natCard (⟨x, hx⟩ : MulAction.stabilizer G q)
  rwa [← Subgroup.orderOf_coe] at h

/-- In an icosahedral-type group, a Sylow `2`-subgroup is not normalized by an element of
order `5`. -/
lemma not_five_normalizes [Finite G] (hsig : signature G = {2, 3, 5}) (V : Subgroup G)
    (hV : Nat.card V = 4) (ρ : G) (hρ : orderOf ρ = 5)
    (hcomm : ∀ v ∈ V, ρ * v * ρ⁻¹ = v) : False := by
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, orderOf_one] at hρ; norm_num at hρ
  obtain ⟨w, hρw⟩ := exists_pole_fixed ρ hρ1
  have h5 : Nat.card (MulAction.stabilizer G w) = 5 := by
    have hd := orderOf_dvd_card_stab hρw
    rw [hρ] at hd
    rcases card_stab_cases hsig w with h | h | h <;> rw [h] at hd ⊢ <;> norm_num at hd
  -- every non-identity element of `V` reverses `w`
  have hrev : ∀ v ∈ V, v ≠ 1 → v • w = w.neg := by
    intro v hv hv1
    have hfix : ρ • (v • w) = v • w := by
      rw [← mul_smul, ← (show ρ * v * ρ⁻¹ * ρ = ρ * v by group), hcomm v hv, mul_smul, hρw]
    rcases pole_eq_or_neg_of_fixed hρ1 hρw hfix with h | h
    · exfalso
      have h1 := orderOf_dvd_card_stab h
      rw [h5] at h1
      have h2 : orderOf v ∣ 4 := by
        have := orderOf_dvd_natCard (⟨v, hv⟩ : V)
        rwa [← Subgroup.orderOf_coe, hV] at this
      have : orderOf v = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 5 4) h1 h2
      exact hv1 (orderOf_eq_one_iff.mp this)
    · exact h
  -- two non-identity elements with non-identity product
  have hne : V ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hV; norm_num at hV
  obtain ⟨v1', hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  set v1 : G := v1'.1
  have hv1 : v1 ≠ 1 := fun h => hv1' (Subtype.ext h)
  obtain ⟨v2, hv2V, hv21, hv22⟩ : ∃ v2 ∈ V, v2 ≠ 1 ∧ v2 ≠ v1⁻¹ := by
    by_contra hall
    push Not at hall
    have hsub : (V : Set G) ⊆ {1, v1⁻¹} := fun x hx => by
      by_cases h : x = 1
      · exact Or.inl h
      · exact Or.inr (hall x hx h)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, v1⁻¹} : Set G).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hV] at this
    omega
  have h12 : v1 * v2 ≠ 1 := fun h => hv22 (eq_inv_of_mul_eq_one_right h)
  have := hrev _ (V.mul_mem v1'.2 hv2V) h12
  rw [mul_smul, hrev v2 hv2V hv21, Poles.smul_neg, hrev v1 v1'.2 hv1, Poles.neg_neg] at this
  exact Poles.neg_ne w this.symm

/-- **Icosahedral case.** A finite rotation group of order `60` with signature `(2, 3, 5)` is
isomorphic to `A₅`. -/
theorem alternating_five [Finite G] (hG : Nat.card G = 60) (hsig : signature G = {2, 3, 5}) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) :=
  GroupTheory60.alternating_five_of hG (fun K _ hK => sixteen_le_card_normal hG hsig K hK)
    (fun V hV ρ hρ hcomm => not_five_normalizes hsig V hV ρ hρ hcomm)

/-! ### Assembly -/

/-- **Classification of the finite subgroups of `SO(3)`.** Every finite subgroup `G` of
`SO(3, ℝ)` is isomorphic to a cyclic group `ℤ_N` (`N = |G|`), a dihedral group `D_n`
(`|G| = 2n`, `n ≥ 2`), the tetrahedral group `A₄`, the octahedral group `S₄`, or the
icosahedral group `A₅`. -/
theorem classification [Finite G] :
    Nonempty (G ≃* Multiplicative (ZMod (Nat.card G))) ∨
      (∃ n, 2 ≤ n ∧ Nat.card G = 2 * n ∧ Nonempty (G ≃* DihedralGroup n)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  by_cases hG : G = ⊥
  · left
    have h1 : Nat.card G = 1 := (Subgroup.card_eq_one).mpr hG
    haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact ⟨(zmodCyclicMulEquiv isCyclic_of_subsingleton).symm⟩
  rcases signature_cases G hG with h | ⟨n, hn, hN, h⟩ | ⟨hN, h⟩ | h | h
  · left
    obtain ⟨ω, hω⟩ := mem_signature.mp (show Nat.card G ∈ signature G by rw [h]; simp)
    exact cyclic_of_orbitOrder_eq ω hω
  · right; left
    obtain ⟨ω, hω⟩ := mem_signature.mp (show n ∈ signature G by rw [h]; simp)
    have hidx : (MulAction.stabilizer G ω.out).index = 2 := by
      have := (MulAction.stabilizer G ω.out).index_mul_card
      rw [show Nat.card (MulAction.stabilizer G ω.out) = n from hω, hN] at this
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    obtain ⟨e⟩ := dihedral_of_stabilizer_index_two ω.out hidx
    refine ⟨n, hn, hN, ⟨e.trans ?_⟩⟩
    rw [show Nat.card (MulAction.stabilizer G ω.out) = n from hω]
  · right; right; left
    obtain ⟨ω, hω⟩ := mem_signature.mp (show 3 ∈ signature G by rw [h]; simp)
    have hO : Nat.card (MulAction.orbit G ω.out) = 4 := by
      have := card_orbit_mul ω.out
      rw [show Nat.card (MulAction.stabilizer G ω.out) = 3 from hω, hN] at this
      omega
    exact alternating_four_of_orbit ω.out hO hN
  · right; right; right; left
    obtain ⟨hN, h⟩ := h
    obtain ⟨ω, hω⟩ := mem_signature.mp (show 3 ∈ signature G by rw [h]; simp)
    have hc : (signature G).count (orbitOrder ω) = 1 := by rw [hω, h]; decide
    exact perm_four_of_orbit ω.out hN hω (neg_mem_orbit_of_count ω hc)
  · right; right; right; right; exact alternating_five h.1 h.2

end Identification

end VOA.Classification.COne.FiniteRotation
