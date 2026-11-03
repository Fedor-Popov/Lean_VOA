/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.PBWTheorem.Construction
import Mathlib.Tactic.LinearCombination

/-!
# The relative Poincaré–Birkhoff–Witt representation: the Lie identity

We prove that the operators `act` of `PBWTheorem.Construction` satisfy
`act ⁅z, z'⁆ = act z ∘ act z' - act z' ∘ act z` (`defect_eq_zero`), so that they form a
representation `rep : g →ₗ⁅K⁆ End (Multiset A →₀ U)` (Humphreys §17.4, Lemma A, relative form).
On the degree-`0` part it restricts to `ρ` on `p` (`rep_p_zero`).

The proof is the classical induction on the degree.  Writing `b` for the least letter of the
monomial `m = b :: Ψ`, every generator (`y a` or `x ∈ p`) is either *low* (`y a` with `a ≤ m`) or
*above `b`*.  If one of the two generators is low, the identity is a defining equation
(`defect_def_case`); if both are above `b`, it follows from the degree-`card Ψ` case and the
Jacobi identity (`defect_core`).
-/

set_option linter.unusedSectionVars false

namespace VOA.PBWTheorem

open Finsupp Module

variable {K : Type*} [Field K]
variable {g : Type*} [LieRing g] [LieAlgebra K g]
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {A : Type*} [LinearOrder A]
variable (p : LieSubalgebra K g) {c : Submodule K g} (hc : IsCompl p.toSubmodule c)
variable (bc : Basis A K c) (ρ : p →ₗ⁅K⁆ Module.End K U)

/-- A generator of `g` that is *above* the letter `b`: either `y a` with `b < a`, or an element
of `p` (which counts as larger than every complement letter). -/
def Above (b : A) (z : g) : Prop :=
  (∃ a, b < a ∧ z = (bc a : g)) ∨ (∃ x : p, z = (x : g))

theorem Above.mono {a b : A} {z : g} (h : Above p bc b z) (hab : a ≤ b) : Above p bc a z := by
  rcases h with ⟨a', h1, rfl⟩ | ⟨x, rfl⟩
  · exact Or.inl ⟨a', lt_of_le_of_lt hab h1, rfl⟩
  · exact Or.inr ⟨x, rfl⟩

/-- The unified defining equation for generators above `b`. -/
theorem act_above_cons {b : A} {z : g} (hz : Above p bc b z) {m : Multiset A}
    (hb : ∀ c ∈ m, b ≤ c) (u : U) :
    act p hc bc ρ z (single (b ::ₘ m) u) =
      act p hc bc ρ (bc b : g) (act p hc bc ρ z (single m u)) +
        act p hc bc ρ ⁅z, (bc b : g)⁆ (single m u) := by
  rcases hz with ⟨a, hba, rfl⟩ | ⟨x, rfl⟩
  · exact act_y_cons p hc bc ρ hba hb u
  · exact act_p_cons p hc bc ρ x hb u

/-- The leading term of a generator above `b` applied to `Ψ ⊗ u`, and the defining equation it
satisfies. -/
theorem exists_top {b : A} {z : g} (hz : Above p bc b z) {Ψ : Multiset A}
    (hb : ∀ c ∈ Ψ, b ≤ c) (u : U) :
    ∃ t : Car (K := K) A U,
      act p hc bc ρ z (single Ψ u) - t ∈ Fil (K := K) A U (Multiset.card Ψ) ∧
      ∀ w : g, Above p bc b w →
        act p hc bc ρ w (act p hc bc ρ (bc b : g) t) =
          act p hc bc ρ (bc b : g) (act p hc bc ρ w t) + act p hc bc ρ ⁅w, (bc b : g)⁆ t := by
  rcases hz with ⟨a, hba, rfl⟩ | ⟨x, rfl⟩
  · refine ⟨single (a ::ₘ Ψ) u, act_y_sub_mem p hc bc ρ a Ψ u, fun w hw => ?_⟩
    have hlow : ∀ c ∈ a ::ₘ Ψ, b ≤ c := by
      intro c hc'
      rcases Multiset.mem_cons.mp hc' with rfl | hc'
      · exact hba.le
      · exact hb c hc'
    rw [act_y_low p hc bc ρ hlow]
    exact act_above_cons p hc bc ρ hw hlow u
  · refine ⟨0, by simpa using act_p_mem p hc bc ρ x Ψ u, fun w _ => by simp⟩

/-- The failure of the representation identity, as a linear map. -/
noncomputable def defect (z z' : g) : Module.End K (Car (K := K) A U) :=
  act p hc bc ρ z ∘ₗ act p hc bc ρ z' - act p hc bc ρ z' ∘ₗ act p hc bc ρ z -
    act p hc bc ρ ⁅z, z'⁆

theorem defect_apply (z z' : g) (v : Car (K := K) A U) :
    defect p hc bc ρ z z' v =
      act p hc bc ρ z (act p hc bc ρ z' v) - act p hc bc ρ z' (act p hc bc ρ z v) -
        act p hc bc ρ ⁅z, z'⁆ v := rfl

theorem defect_eq_zero_iff (z z' : g) (v : Car (K := K) A U) :
    defect p hc bc ρ z z' v = 0 ↔
      act p hc bc ρ z (act p hc bc ρ z' v) =
        act p hc bc ρ z' (act p hc bc ρ z v) + act p hc bc ρ ⁅z, z'⁆ v := by
  rw [defect_apply, sub_sub, sub_eq_zero]

theorem defect_swap (z z' : g) (v : Car (K := K) A U) :
    defect p hc bc ρ z' z v = - defect p hc bc ρ z z' v := by
  rw [defect_apply, defect_apply, ← lie_skew, map_neg, LinearMap.neg_apply]
  abel

theorem defect_self (z : g) (v : Car (K := K) A U) : defect p hc bc ρ z z v = 0 := by
  rw [defect_apply, lie_self, map_zero, LinearMap.zero_apply, sub_self, sub_zero]

theorem defect_add_left (z₁ z₂ z' : g) (v : Car (K := K) A U) :
    defect p hc bc ρ (z₁ + z₂) z' v = defect p hc bc ρ z₁ z' v + defect p hc bc ρ z₂ z' v := by
  simp only [defect_apply, map_add, add_lie, LinearMap.add_apply]
  abel

theorem defect_smul_left (r : K) (z z' : g) (v : Car (K := K) A U) :
    defect p hc bc ρ (r • z) z' v = r • defect p hc bc ρ z z' v := by
  simp only [defect_apply, map_smul, smul_lie, LinearMap.smul_apply, smul_sub]

theorem defect_zero_left (z' : g) (v : Car (K := K) A U) : defect p hc bc ρ 0 z' v = 0 := by
  simp [defect_apply]

/-- **The low case.**  If `z' = y a'` with `a' ≤ m` and `z` is above `a'`, the identity is the
defining equation of `z` on `a' :: m`. -/
theorem defect_def_case {a' : A} {m : Multiset A} (ha' : ∀ c ∈ m, a' ≤ c) {z : g}
    (hz : Above p bc a' z) (u : U) : defect p hc bc ρ z (bc a' : g) (single m u) = 0 := by
  rw [defect_eq_zero_iff, act_y_low p hc bc ρ ha', act_above_cons p hc bc ρ hz ha']

/-- **The core case.**  Both generators above the least letter `b` of `b :: Ψ`. -/
theorem defect_core {b : A} {Ψ : Multiset A} (hb : ∀ c ∈ Ψ, b ≤ c) {z z' : g}
    (hz : Above p bc b z) (hz' : Above p bc b z') (u : U)
    (IH : ∀ w w' : g, ∀ v ∈ Fil (K := K) A U (Multiset.card Ψ), defect p hc bc ρ w w' v = 0) :
    defect p hc bc ρ z z' (single (b ::ₘ Ψ) u) = 0 := by
  obtain ⟨t, ht, hT⟩ := exists_top p hc bc ρ hz hb u
  obtain ⟨t', ht', hT'⟩ := exists_top p hc bc ρ hz' hb u
  have hs : single Ψ u ∈ Fil (K := K) A U (Multiset.card Ψ) := single_mem_Fil le_rfl u
  have hS : single (b ::ₘ Ψ) u = (act p hc bc ρ (bc b : g)) (single Ψ u) :=
    (act_y_low p hc bc ρ hb u).symm
  have e1 := act_above_cons p hc bc ρ hz hb u
  have e2 := act_above_cons p hc bc ρ hz' hb u
  have i1 := (defect_eq_zero_iff p hc bc ρ _ _ _).mp (IH z (bc b : g) _ ht')
  have i2 := (defect_eq_zero_iff p hc bc ρ _ _ _).mp (IH z' (bc b : g) _ ht)
  have i3 := (defect_eq_zero_iff p hc bc ρ _ _ _).mp (IH z z' (single Ψ u) hs)
  have i4 := (defect_eq_zero_iff p hc bc ρ _ _ _).mp (IH ⁅z, (bc b : g)⁆ z' (single Ψ u) hs)
  have i5 := (defect_eq_zero_iff p hc bc ρ _ _ _).mp (IH z ⁅z', (bc b : g)⁆ (single Ψ u) hs)
  have i6 := (defect_eq_zero_iff p hc bc ρ _ _ _).mp (IH ⁅z, z'⁆ (bc b : g) (single Ψ u) hs)
  have j1 := hT' z hz
  have j2 := hT z' hz'
  have jac : act p hc bc ρ ⁅⁅z, z'⁆, (bc b : g)⁆ (single Ψ u) =
      act p hc bc ρ ⁅⁅z, (bc b : g)⁆, z'⁆ (single Ψ u) +
        act p hc bc ρ ⁅z, ⁅z', (bc b : g)⁆⁆ (single Ψ u) := by
    rw [← LinearMap.add_apply, ← map_add]
    congr 2
    rw [leibniz_lie z z' (bc b : g), ← lie_skew z' ⁅z, (bc b : g)⁆]
    abel
  rw [defect_apply, e1, e2, hS]
  simp only [map_add, map_sub] at i1 i2 ⊢
  have i3' : act p hc bc ρ (bc b : g) (act p hc bc ρ z (act p hc bc ρ z' (single Ψ u))) =
      act p hc bc ρ (bc b : g) (act p hc bc ρ z' (act p hc bc ρ z (single Ψ u))) +
        act p hc bc ρ (bc b : g) (act p hc bc ρ ⁅z, z'⁆ (single Ψ u)) := by
    rw [i3, map_add]
  linear_combination (norm := abel) i1 + j1 - i2 - j2 + i5 + i4 - i6 + i3' - jac

/-- The generators of `g`: complement-basis vectors and elements of `p`. -/
def IsGen (z : g) : Prop := (∃ a, z = (bc a : g)) ∨ (∃ x : p, z = (x : g))

/-- Every generator is low, or (in degree `0`) an element of `p`, or above the least letter. -/
theorem classify {m : Multiset A} {z : g} (hz : IsGen p bc z) :
    (∃ a, z = (bc a : g) ∧ ∀ c ∈ m, a ≤ c) ∨ (m = 0 ∧ ∃ x : p, z = (x : g)) ∨
      (∃ h : m ≠ 0, Above p bc (mmin m h) z) := by
  rcases hz with ⟨a, rfl⟩ | ⟨x, rfl⟩
  · by_cases hm : m = 0
    · exact Or.inl ⟨a, rfl, by simp [hm]⟩
    · by_cases ha : a ≤ mmin m hm
      · exact Or.inl ⟨a, rfl, fun c hc' => ha.trans (mmin_le m hm hc')⟩
      · exact Or.inr (Or.inr ⟨hm, Or.inl ⟨a, lt_of_not_ge ha, rfl⟩⟩)
  · by_cases hm : m = 0
    · exact Or.inr (Or.inl ⟨hm, x, rfl⟩)
    · exact Or.inr (Or.inr ⟨hm, Or.inr ⟨x, rfl⟩⟩)

/-- The identity in degree `0` for two elements of `p`: it is the representation property of
`ρ`. -/
theorem defect_base (x x' : p) (u : U) :
    defect p hc bc ρ (x : g) (x' : g) (single 0 u) = 0 := by
  rw [defect_apply, ← LieSubalgebra.coe_bracket]
  simp only [act_p_zero, LieHom.map_lie, LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, single_sub, sub_self]

/-- The identity on a pair of generators, assuming it in lower degrees. -/
theorem defect_gen_pair {m : Multiset A}
    (IH : ∀ k < Multiset.card m, ∀ w w' : g, ∀ v ∈ Fil (K := K) A U k,
      defect p hc bc ρ w w' v = 0)
    {z z' : g} (hz : IsGen p bc z) (hz' : IsGen p bc z') (u : U) :
    defect p hc bc ρ z z' (single m u) = 0 := by
  rcases classify p bc (m := m) hz with ⟨a, rfl, ha⟩ | ⟨hm0, x, rfl⟩ | ⟨hm, hA⟩ <;>
  rcases classify p bc (m := m) hz' with ⟨a', rfl, ha'⟩ | ⟨hm0', x', rfl⟩ | ⟨hm', hA'⟩
  · rcases lt_trichotomy a a' with h | rfl | h
    · rw [defect_swap, defect_def_case p hc bc ρ ha (Or.inl ⟨a', h, rfl⟩) u, neg_zero]
    · exact defect_self p hc bc ρ _ _
    · exact defect_def_case p hc bc ρ ha' (Or.inl ⟨a, h, rfl⟩) u
  · rw [defect_swap, defect_def_case p hc bc ρ ha (Or.inr ⟨x', rfl⟩) u, neg_zero]
  · rw [defect_swap, defect_def_case p hc bc ρ ha (hA'.mono p bc (ha _ (mmin_mem m hm'))) u,
      neg_zero]
  · exact defect_def_case p hc bc ρ ha' (Or.inr ⟨x, rfl⟩) u
  · subst hm0
    exact defect_base p hc bc ρ x x' u
  · exact absurd hm0 hm'
  · exact defect_def_case p hc bc ρ ha' (hA.mono p bc (ha' _ (mmin_mem m hm))) u
  · exact absurd hm0' hm
  · have hA'' : Above p bc (mmin m hm) z' := hA'
    have key : ∀ (b : A) (Ψ : Multiset A), (∀ c ∈ Ψ, b ≤ c) → Above p bc b z →
        Above p bc b z' → m = b ::ₘ Ψ → defect p hc bc ρ z z' (single m u) = 0 := by
      rintro b Ψ hb h1 h2 rfl
      exact defect_core p hc bc ρ hb h1 h2 u (IH (Multiset.card Ψ) (by simp))
    exact key _ _ (mmin_lb m hm) hA hA'' (Multiset.cons_erase (mmin_mem m hm)).symm

/-- From generators to all of `g`, in both arguments. -/
theorem defect_of_gen {v : Car (K := K) A U}
    (h : ∀ z z' : g, IsGen p bc z → IsGen p bc z' → defect p hc bc ρ z z' v = 0)
    (z z' : g) : defect p hc bc ρ z z' v = 0 := by
  induction z using gen_induction p hc bc with
  | h0 => exact defect_zero_left p hc bc ρ _ _
  | hadd z₁ z₂ h₁ h₂ => rw [defect_add_left, h₁, h₂, add_zero]
  | hsmul r z h' => rw [defect_smul_left, h', smul_zero]
  | hy a =>
      rw [defect_swap, neg_eq_zero]
      induction z' using gen_induction p hc bc with
      | h0 => exact defect_zero_left p hc bc ρ _ _
      | hadd z₁ z₂ h₁ h₂ => rw [defect_add_left, h₁, h₂, add_zero]
      | hsmul r z h' => rw [defect_smul_left, h', smul_zero]
      | hy a' =>
          rw [defect_swap, neg_eq_zero]; exact h _ _ (Or.inl ⟨a, rfl⟩) (Or.inl ⟨a', rfl⟩)
      | hp x =>
          rw [defect_swap, neg_eq_zero]; exact h _ _ (Or.inl ⟨a, rfl⟩) (Or.inr ⟨x, rfl⟩)
  | hp x =>
      rw [defect_swap, neg_eq_zero]
      induction z' using gen_induction p hc bc with
      | h0 => exact defect_zero_left p hc bc ρ _ _
      | hadd z₁ z₂ h₁ h₂ => rw [defect_add_left, h₁, h₂, add_zero]
      | hsmul r z h' => rw [defect_smul_left, h', smul_zero]
      | hy a' =>
          rw [defect_swap, neg_eq_zero]; exact h _ _ (Or.inr ⟨x, rfl⟩) (Or.inl ⟨a', rfl⟩)
      | hp x' =>
          rw [defect_swap, neg_eq_zero]; exact h _ _ (Or.inr ⟨x, rfl⟩) (Or.inr ⟨x', rfl⟩)

theorem defect_single_aux (n : ℕ) :
    ∀ m : Multiset A, Multiset.card m = n → ∀ (z z' : g) (u : U),
      defect p hc bc ρ z z' (single m u) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hmn z z' u
    have IH : ∀ k < Multiset.card m, ∀ w w' : g, ∀ v ∈ Fil (K := K) A U k,
        defect p hc bc ρ w w' v = 0 := by
      intro k hk w w' v hv
      have := eq_on_Fil (f := defect p hc bc ρ w w') (f' := 0)
        (fun m' u' hm' => by
          rw [LinearMap.zero_apply]
          exact ih (Multiset.card m') (by omega) m' rfl w w' u') hv
      simpa using this
    exact defect_of_gen p hc bc ρ
      (fun w w' hw hw' => defect_gen_pair p hc bc ρ IH hw hw' u) z z'

/-- **The representation identity** `act ⁅z, z'⁆ = act z ∘ act z' - act z' ∘ act z`. -/
theorem defect_eq_zero (z z' : g) (v : Car (K := K) A U) : defect p hc bc ρ z z' v = 0 := by
  have : defect p hc bc ρ z z' = 0 := Finsupp.lhom_ext fun m u =>
    defect_single_aux p hc bc ρ _ m rfl z z' u
  rw [this, LinearMap.zero_apply]

/-- **The relative PBW representation** of `g` on `Multiset A →₀ U` (Humphreys §17.4, Lemma A,
relative form). -/
noncomputable def rep : g →ₗ⁅K⁆ Module.End K (Car (K := K) A U) :=
  { act p hc bc ρ with
    map_lie' := fun {z z'} => by
      refine LinearMap.ext fun v => ?_
      have h := (defect_eq_zero_iff p hc bc ρ z z' v).mp (defect_eq_zero p hc bc ρ z z' v)
      change act p hc bc ρ ⁅z, z'⁆ v = ⁅act p hc bc ρ z, act p hc bc ρ z'⁆ v
      rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
        Module.End.mul_apply, h]
      abel }

theorem rep_apply (z : g) (v : Car (K := K) A U) : rep p hc bc ρ z v = act p hc bc ρ z v := rfl

/-- On the degree-`0` part, `p` acts through `ρ`. -/
theorem rep_p_zero (x : p) (u : U) :
    rep p hc bc ρ (x : g) (single 0 u) = single 0 (ρ x u) :=
  act_p_zero p hc bc ρ x u

end VOA.PBWTheorem
