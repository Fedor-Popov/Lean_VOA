import VOA.Huang.DLNSmallTransfer

/-!
# Schur triviality of `SL₂(ℤ/3)`

`SL₂(ℤ/3)` (the binary tetrahedral group, order 24) contains the quaternion group
`{g | g⁴ = 1}` of index 3 and a cyclic subgroup of order 3 (index 8). Both are
Schur-trivial, so the coprime-index transfer criterion applies.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl

/-- `SL₂(ℤ/3)`. -/
abbrev SLThree := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

theorem card_SLThree : Fintype.card SLThree = 24 := by decide +kernel

/-- The quaternion subgroup `{g | g⁴ = 1}` of `SL₂(ℤ/3)`. -/
def quatThree : Subgroup SLThree where
  carrier := {g | g ^ 4 = 1}
  mul_mem' := by
    have h : ∀ a b : SLThree, a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by decide +kernel
    exact fun {a b} ha hb => h a b ha hb
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, inv_pow] at ha ⊢
    rw [ha, inv_one]

theorem mem_quatThree (g : SLThree) : g ∈ quatThree ↔ g ^ 4 = 1 := Iff.rfl

instance : DecidablePred (· ∈ quatThree) := fun g =>
  decidable_of_iff (g ^ 4 = 1) (mem_quatThree g).symm

private def qs : SLThree := ⟨!![0, 2; 1, 0], by decide⟩
private def qt : SLThree := ⟨!![1, 1; 1, 2], by decide⟩

theorem card_quatThree : Nat.card quatThree = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem index_quatThree : quatThree.index = 3 := by
  have h := Subgroup.card_mul_index quatThree
  rw [card_quatThree, Nat.card_eq_fintype_card, card_SLThree] at h
  omega

theorem schurTrivial_quatThree : SchurTrivial quatThree := by
  have hs : qs ∈ quatThree := by decide
  have ht : qt ∈ quatThree := by decide
  apply schurTrivial_of_quaternion_normal_forms (⟨qs, hs⟩ : quatThree) ⟨qt, ht⟩
  · apply Subtype.ext; simp only [Subgroup.coe_pow]; decide
  · apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; decide
  · intro h
    have := congrArg Subtype.val h
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    revert this; decide
  · have key : ∀ g : SLThree, g ^ 4 = 1 → ∃ i : Fin 4, ∃ j : Fin 2,
        g = qs ^ i.val * qt ^ j.val := by decide +kernel
    intro q
    obtain ⟨i, j, hij⟩ := key q.1 q.2
    exact ⟨i.val, j.val, Subtype.ext (by simpa using hij)⟩

private def qu : SLThree := ⟨!![1, 1; 0, 1], by decide⟩

theorem schurTrivial_SL_three : SchurTrivial SLThree := by
  have horder : orderOf qu = 3 :=
    orderOf_eq_prime (by decide : qu ^ 3 = 1) (by decide : qu ≠ 1)
  have hC : (Subgroup.zpowers qu).index = 8 := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers qu)
    rw [Nat.card_zpowers, horder, Nat.card_eq_fintype_card, card_SLThree] at h
    omega
  haveI : quatThree.FiniteIndex := ⟨by rw [index_quatThree]; norm_num⟩
  haveI : (Subgroup.zpowers qu).FiniteIndex := ⟨by rw [hC]; norm_num⟩
  apply schurTrivial_of_coprime_index quatThree (Subgroup.zpowers qu)
    schurTrivial_quatThree (schurTrivial_of_isCyclic _)
  rw [index_quatThree, hC]; norm_num

end VOA.Huang.DLNSchur
