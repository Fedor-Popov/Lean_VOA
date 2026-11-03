import VOA.Huang.DLNCommutatorLevelOne

/-!
# Existential-level relative-commutator bridge

`RelativeCommutatorCongruenceSome` is the remaining arithmetic obligation,
not a theorem asserted here. It suffices for genuine Zhu congruence, and for
the exact order-of-`T` conclusion through the existing Wohlfahrt theorem.

The equivalent `DerivedRelativeCommutatorCongruenceSome` confines the
remaining obligation to the derived subgroup: congruence of all characters
has been proved in `DLNCommutatorLevelOne`.
-/

namespace VOA.Huang.DLNLifting

open VOA.Huang.DLN VOA.Huang.DLNBridge CongruenceSubgroup

/-- The existential-level relative-commutator congruence statement.
This arithmetic statement remains unproved in this module. -/
def RelativeCommutatorCongruenceSome : Prop :=
  ∀ N : ℕ, 0 < N → ∃ L : ℕ, 0 < L ∧
    Gamma L ≤ ⁅(⊤ : Subgroup SL2Z), Gamma N⁆

/-- The remaining containment restricted to the derived subgroup.
This is an explicit unproved arithmetic obligation. -/
def DerivedRelativeCommutatorCongruenceSome : Prop :=
  ∀ N : ℕ, 0 < N → ∃ L : ℕ, 0 < L ∧
    Gamma L ⊓ commutator SL2Z ≤ ⁅(⊤ : Subgroup SL2Z), Gamma N⁆

/-- The exact congruence statement implies its existential-level version. -/
theorem relativeCommutatorCongruenceSome_of_exact (h : RelativeCommutatorCongruence) :
    RelativeCommutatorCongruenceSome := by
  intro N hN
  exact ⟨12 * N, Nat.mul_pos (by norm_num) hN, h N hN⟩

/-- Removing the character obstruction leaves precisely the derived-group obligation. -/
theorem relativeCommutatorCongruenceSome_iff_derived :
    RelativeCommutatorCongruenceSome ↔ DerivedRelativeCommutatorCongruenceSome := by
  constructor
  · intro h N hN
    obtain ⟨L, hL, hΓ⟩ := h N hN
    exact ⟨L, hL, inf_le_left.trans hΓ⟩
  · intro h N hN
    obtain ⟨L, hL, hΓ⟩ := h N hN
    refine ⟨12 * L, Nat.mul_pos (by norm_num) hL, ?_⟩
    intro γ hγ
    exact hΓ ⟨gamma_le_of_dvd (dvd_mul_left L 12) hγ,
      gamma_twelve_le_commutator (gamma_le_of_dvd (dvd_mul_right 12 L) hγ)⟩

/-- Some relative-commutator congruence level gives some genuine matrix-kernel level. -/
theorem matrix_congruenceSome_of_relativeCommutatorSome
    (hgroup : RelativeCommutatorCongruenceSome)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ} (hN : 0 < N)
    (hp : MatrixProjectiveCongruence ρ N) :
    ∃ L : ℕ, 0 < L ∧ KernelContainsGamma ρ L := by
  obtain ⟨L, hL, hΓ⟩ := hgroup N hN
  refine ⟨L, hL, fun γ hγ => ?_⟩
  have h := relativeCommutator_le_ker ρ hp (hΓ hγ)
  exact congrArg (fun a : (Matrix κ κ ℂ)ˣ => (a : Matrix κ κ ℂ)) h

/-- Once some genuine level is obtained, the existing exact-level theorem applies. -/
theorem matrix_kernel_orderOf_of_relativeCommutatorSome
    (hgroup : RelativeCommutatorCongruenceSome)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ} (hN : 0 < N)
    (hp : MatrixProjectiveCongruence ρ N) :
    IsOfFinOrder (ρ ModularGroup.T) ∧
      KernelContainsGamma ρ (orderOf (ρ ModularGroup.T)) := by
  obtain ⟨L, hL, hΓ⟩ := matrix_congruenceSome_of_relativeCommutatorSome hgroup ρ hN hp
  exact NSFinish.kernel_gamma_orderOf ρ hL hΓ

/-- The existential arithmetic contract suffices for the requested Zhu bridge. -/
theorem zhuCongruence_of_relativeCommutatorSome
    (hgroup : RelativeCommutatorCongruenceSome)
    (hP : ZhuProjectiveCongruenceInput.{u}) : ZhuCongruenceInput.{u} := by
  intro 𝒱 _ _ V hV D hD D' hZD
  obtain ⟨N, hN, hp⟩ := hP 𝒱 V hV D hD D' hZD
  exact matrix_congruenceSome_of_relativeCommutatorSome hgroup D'.rep hN hp

end VOA.Huang.DLNLifting
