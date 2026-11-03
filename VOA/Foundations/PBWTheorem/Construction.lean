/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.Finset.Max

/-!
# The relative Poincaré–Birkhoff–Witt representation: construction

This file and its companions prove, from Mathlib alone, the relative PBW consequence used by the
library: **every representation of a Lie subalgebra `p ⊆ g` embeds `p`-equivariantly into a
representation of `g`.**  It is the relative form of Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §17.4, Lemma A.

## Set-up

* `g` is a Lie algebra over a field `K`, `p` a Lie subalgebra and `c` a linear complement of `p`.
* `bc : Basis A K c` is a basis of the complement, indexed by a *linearly ordered* type `A`.
* `ρ : p →ₗ⁅K⁆ End U` is a representation of `p`.

The carrier of the `g`-module is `M = Multiset A →₀ U`: a basis vector `single m u` stands for
`y^m ⊗ u`, where `m` is an (unordered, equivalently sorted) monomial in the complement basis
`y a = bc a`.  The operators are defined by recursion on the degree `card m`:

* `y a · (m ⊗ u) = (a :: m) ⊗ u` when `a ≤ m` (every letter of `m` is `≥ a`);
* otherwise, with `b = min m`, `m = b :: m'`:
  `y a · (b m' ⊗ u) = y b · (y a · (m' ⊗ u)) + ⁅y a, y b⁆ · (m' ⊗ u)`;
* `x · (0 ⊗ u) = 0 ⊗ ρ(x) u` for `x ∈ p`, and
  `x · (b m' ⊗ u) = y b · (x · (m' ⊗ u)) + ⁅x, y b⁆ · (m' ⊗ u)`.

Since the right-hand sides apply the operators to vectors of the *same* degree, the recursion is
organized through stages `stage n`, correct on degree `< n`; the stages stabilize (`stage_agr`)
and the limit `act` satisfies the defining equations `act_y_low`, `act_y_cons`, `act_p_zero`,
`act_p_cons`, together with the degree bounds `act_good`.

No PBW statement is assumed anywhere.
-/

set_option linter.unusedSectionVars false

namespace VOA.PBWTheorem

open Finsupp Module

variable {K : Type*} [Field K]
variable {g : Type*} [LieRing g] [LieAlgebra K g]
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {A : Type*} [LinearOrder A]

/-! ## Minimum of a nonempty multiset -/

/-- The least letter of a nonempty multiset. -/
noncomputable def mmin (m : Multiset A) (h : m ≠ 0) : A :=
  m.toFinset.min' (Multiset.toFinset_nonempty.mpr h)

theorem mmin_mem (m : Multiset A) (h : m ≠ 0) : mmin m h ∈ m :=
  Multiset.mem_toFinset.mp (Finset.min'_mem _ _)

theorem mmin_le (m : Multiset A) (h : m ≠ 0) {b : A} (hb : b ∈ m) : mmin m h ≤ b :=
  Finset.min'_le _ _ (Multiset.mem_toFinset.mpr hb)

theorem mmin_lb (m : Multiset A) (h : m ≠ 0) : ∀ b ∈ m.erase (mmin m h), mmin m h ≤ b :=
  fun _ hb => mmin_le m h (Multiset.mem_of_mem_erase hb)

theorem mmin_cons {b : A} {m : Multiset A} (hb : ∀ c ∈ m, b ≤ c) (h : b ::ₘ m ≠ 0) :
    mmin (b ::ₘ m) h = b := by
  refine le_antisymm (mmin_le _ _ (Multiset.mem_cons_self _ _)) ?_
  rcases Multiset.mem_cons.mp (mmin_mem _ h) with h1 | h1
  · rw [h1]
  · exact hb _ h1

theorem ne_zero_of_not_lb {a : A} {m : Multiset A} (h : ¬ ∀ b ∈ m, a ≤ b) : m ≠ 0 := by
  rintro rfl
  exact h (by simp)

/-! ## The degree filtration -/

/-- The degree-`≤ k` part of `Multiset A →₀ U`. -/
def Fil (A U : Type*) [AddCommGroup U] [Module K U] (k : ℕ) :
    Submodule K (Multiset A →₀ U) :=
  supported U K {m : Multiset A | Multiset.card m ≤ k}

theorem single_mem_Fil {k : ℕ} {m : Multiset A} (hm : Multiset.card m ≤ k) (u : U) :
    single m u ∈ Fil (K := K) A U k :=
  single_mem_supported K u hm

theorem Fil_mono {k l : ℕ} (h : k ≤ l) : Fil (K := K) A U k ≤ Fil (K := K) A U l :=
  supported_mono fun _ hm => le_trans hm h

theorem Fil_le_of {k : ℕ} {N : Submodule K (Multiset A →₀ U)}
    (h : ∀ m (u : U), Multiset.card m ≤ k → single m u ∈ N) : Fil (K := K) A U k ≤ N := by
  intro v hv
  rw [← v.sum_single]
  refine Submodule.sum_mem _ fun m hm => h m (v m) ?_
  exact (mem_supported K v).mp hv (Finset.mem_coe.mpr hm)

/-- Two linear maps agreeing on degree-`≤ k` basis vectors agree on `Fil k`. -/
theorem eq_on_Fil {N : Type*} [AddCommGroup N] [Module K N] {k : ℕ}
    {f f' : (Multiset A →₀ U) →ₗ[K] N}
    (h : ∀ m (u : U), Multiset.card m ≤ k → f (single m u) = f' (single m u))
    {v : Multiset A →₀ U} (hv : v ∈ Fil (K := K) A U k) : f v = f' v := by
  have : Fil (K := K) A U k ≤ LinearMap.eqLocus f f' := Fil_le_of fun m u hm => h m u hm
  exact this hv

/-! ## Generators of `g` -/

variable (p : LieSubalgebra K g) {c : Submodule K g} (hc : IsCompl p.toSubmodule c)
variable (bc : Basis A K c) (ρ : p →ₗ⁅K⁆ Module.End K U)

include hc in
theorem span_gens :
    Submodule.span K (Set.range (fun a => (bc a : g)) ∪ Set.range (fun x : p => (x : g))) = ⊤ := by
  rw [eq_top_iff, ← hc.sup_eq_top, sup_le_iff]
  constructor
  · intro x hx
    exact Submodule.subset_span (Or.inr ⟨⟨x, hx⟩, rfl⟩)
  · intro x hx
    have hx' : (⟨x, hx⟩ : c) ∈ Submodule.span K (Set.range bc) := bc.mem_span _
    have := Submodule.mem_map_of_mem (f := c.subtype) hx'
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact Or.inl ⟨a, rfl⟩

include hc in
/-- Induction principle: a property closed under `0`, `+`, scalars, holding on the complement
basis and on `p`, holds on all of `g`. -/
theorem gen_induction {P : g → Prop} (h0 : P 0) (hadd : ∀ z z', P z → P z' → P (z + z'))
    (hsmul : ∀ (r : K) z, P z → P (r • z)) (hy : ∀ a, P (bc a : g)) (hp : ∀ x : p, P x)
    (z : g) : P z := by
  have hz : z ∈ Submodule.span K
      (Set.range (fun a => (bc a : g)) ∪ Set.range (fun x : p => (x : g))) := by
    rw [span_gens p hc bc]; trivial
  induction hz using Submodule.span_induction with
  | mem z hz =>
      rcases hz with ⟨a, rfl⟩ | ⟨x, rfl⟩
      · exact hy a
      · exact hp x
  | zero => exact h0
  | add z z' _ _ h h' => exact hadd z z' h h'
  | smul r z _ h => exact hsmul r z h

/-! ## Assembling an action from the generators -/

/-- Assemble a linear map `g → End M` from its values on the complement basis and on `p`. -/
noncomputable def assemble {N : Type*} [AddCommGroup N] [Module K N]
    (Y : A → N) (X : p →ₗ[K] N) : g →ₗ[K] N :=
  LinearMap.ofIsCompl hc X (Finsupp.linearCombination K Y ∘ₗ bc.repr.toLinearMap)

theorem assemble_y {N : Type*} [AddCommGroup N] [Module K N]
    (Y : A → N) (X : p →ₗ[K] N) (a : A) : assemble p hc bc Y X (bc a : g) = Y a := by
  rw [assemble, LinearMap.ofIsCompl_apply_right]
  simp

theorem assemble_p {N : Type*} [AddCommGroup N] [Module K N]
    (Y : A → N) (X : p →ₗ[K] N) (x : p) : assemble p hc bc Y X (x : g) = X x := by
  rw [assemble]
  exact LinearMap.ofIsCompl_apply_left hc (u := x)

/-! ## One stage of the recursion -/

/-- Abbreviation for the carrier. -/
abbrev Car (A U : Type*) [AddCommGroup U] [Module K U] := Multiset A →₀ U

/-- The recursive clause for `y a` on `b :: m'` (with `b < a`, `b ≤ m'`). -/
noncomputable def Yrec (F : g →ₗ[K] Module.End K (Car (K := K) A U)) (a b : A) (m' : Multiset A) :
    U →ₗ[K] Car (K := K) A U :=
  lsingle (a ::ₘ b ::ₘ m') +
    F (bc b : g) ∘ₗ (F (bc a : g) ∘ₗ lsingle m' - lsingle (a ::ₘ m')) +
    F ⁅(bc a : g), (bc b : g)⁆ ∘ₗ lsingle m'

/-- One stage of the action of the complement-basis vector `y a`. -/
noncomputable def Ystep (F : g →ₗ[K] Module.End K (Car (K := K) A U)) (a : A) :
    Module.End K (Car (K := K) A U) :=
  Finsupp.lsum K fun m =>
    if h : ∀ b ∈ m, a ≤ b then lsingle (a ::ₘ m)
    else Yrec bc F a (mmin m (ne_zero_of_not_lb h)) (m.erase (mmin m (ne_zero_of_not_lb h)))

/-- The recursive clause for `x ∈ p` on `b :: m'`. -/
noncomputable def Xrec (F : g →ₗ[K] Module.End K (Car (K := K) A U)) (x : g) (b : A)
    (m' : Multiset A) : U →ₗ[K] Car (K := K) A U :=
  F (bc b : g) ∘ₗ F x ∘ₗ lsingle m' + F ⁅x, (bc b : g)⁆ ∘ₗ lsingle m'

theorem Xrec_add (F : g →ₗ[K] Module.End K (Car (K := K) A U)) (x x' : g) (b : A)
    (m' : Multiset A) : Xrec bc F (x + x') b m' = Xrec bc F x b m' + Xrec bc F x' b m' := by
  simp only [Xrec, map_add, add_lie, LinearMap.add_comp, LinearMap.comp_add]
  abel

theorem Xrec_smul (F : g →ₗ[K] Module.End K (Car (K := K) A U)) (r : K) (x : g) (b : A)
    (m' : Multiset A) : Xrec bc F (r • x) b m' = r • Xrec bc F x b m' := by
  simp only [Xrec, map_smul, smul_lie, LinearMap.smul_comp, LinearMap.comp_smul, smul_add]

/-- One stage of the action of `p`. -/
noncomputable def Xstep (F : g →ₗ[K] Module.End K (Car (K := K) A U)) :
    p →ₗ[K] Module.End K (Car (K := K) A U) where
  toFun x := Finsupp.lsum K fun m =>
    if h : m = 0 then lsingle 0 ∘ₗ (ρ x : Module.End K U)
    else Xrec bc F (x : g) (mmin m h) (m.erase (mmin m h))
  map_add' x x' := by
    refine Finsupp.lhom_ext fun m u => ?_
    simp only [LinearMap.add_apply, Finsupp.lsum_single]
    split_ifs with h
    · simp
    · rw [show ((x + x' : p) : g) = x + x' from rfl, Xrec_add, LinearMap.add_apply]
  map_smul' r x := by
    refine Finsupp.lhom_ext fun m u => ?_
    simp only [LinearMap.smul_apply, Finsupp.lsum_single, RingHom.id_apply]
    split_ifs with h
    · simp
    · rw [show ((r • x : p) : g) = r • (x : g) from rfl, Xrec_smul, LinearMap.smul_apply]

/-- One stage of the full action. -/
noncomputable def step (F : g →ₗ[K] Module.End K (Car (K := K) A U)) :
    g →ₗ[K] Module.End K (Car (K := K) A U) :=
  assemble p hc bc (Ystep bc F) (Xstep p bc ρ F)

/-- The stages of the recursion; `stage n` is correct in degree `< n`. -/
noncomputable def stage : ℕ → (g →ₗ[K] Module.End K (Car (K := K) A U))
  | 0 => 0
  | n + 1 => step p hc bc ρ (stage n)

theorem step_y_low (F : g →ₗ[K] Module.End K (Car (K := K) A U)) {a : A} {m : Multiset A}
    (h : ∀ b ∈ m, a ≤ b) (u : U) :
    step p hc bc ρ F (bc a : g) (single m u) = single (a ::ₘ m) u := by
  rw [step, assemble_y, Ystep, Finsupp.lsum_single, dif_pos h, lsingle_apply]

theorem step_y_high (F : g →ₗ[K] Module.End K (Car (K := K) A U)) {a : A} {m : Multiset A}
    (h : ¬ ∀ b ∈ m, a ≤ b) (u : U) :
    step p hc bc ρ F (bc a : g) (single m u) =
      Yrec bc F a (mmin m (ne_zero_of_not_lb h)) (m.erase (mmin m (ne_zero_of_not_lb h))) u := by
  rw [step, assemble_y, Ystep, Finsupp.lsum_single, dif_neg h]

theorem step_p_zero (F : g →ₗ[K] Module.End K (Car (K := K) A U)) (x : p) (u : U) :
    step p hc bc ρ F (x : g) (single 0 u) = single 0 (ρ x u) := by
  rw [step, assemble_p]
  simp [Xstep]

theorem step_p_ne (F : g →ₗ[K] Module.End K (Car (K := K) A U)) (x : p) {m : Multiset A}
    (h : m ≠ 0) (u : U) :
    step p hc bc ρ F (x : g) (single m u) =
      Xrec bc F (x : g) (mmin m h) (m.erase (mmin m h)) u := by
  rw [step, assemble_p]
  simp only [Xstep, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.lsum_single, dif_neg h]

/-! ## Degree bounds and agreement of stages -/

/-- The degree bounds `y a · (m ⊗ u) ≡ (a :: m) ⊗ u` and `x · (m ⊗ u) ∈ Fil (card m)`, in degrees
`< n`. -/
def Good (n : ℕ) (F : g →ₗ[K] Module.End K (Car (K := K) A U)) : Prop :=
  ∀ (m : Multiset A) (u : U), Multiset.card m < n →
    (∀ a, F (bc a : g) (single m u) - single (a ::ₘ m) u ∈ Fil (K := K) A U (Multiset.card m)) ∧
    (∀ x : p, F (x : g) (single m u) ∈ Fil (K := K) A U (Multiset.card m))

include hc in
theorem Good.raise_single {n : ℕ} {F : g →ₗ[K] Module.End K (Car (K := K) A U)}
    (hF : Good p bc n F) {m : Multiset A} (hm : Multiset.card m < n) (u : U) (z : g) :
    F z (single m u) ∈ Fil (K := K) A U (Multiset.card m + 1) := by
  induction z using gen_induction p hc bc with
  | h0 => simp
  | hadd z z' h h' => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ h h'
  | hsmul r z h => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ r h
  | hy a =>
      have h1 := (hF m u hm).1 a
      rw [← sub_add_cancel (F (bc a : g) (single m u)) (single (a ::ₘ m) u)]
      refine Submodule.add_mem _ (Fil_mono (Nat.le_succ _) h1) (single_mem_Fil ?_ u)
      simp
  | hp x => exact Fil_mono (Nat.le_succ _) ((hF m u hm).2 x)

include hc in
theorem Good.raise {n : ℕ} {F : g →ₗ[K] Module.End K (Car (K := K) A U)}
    (hF : Good p bc n F) {k : ℕ} (hk : k < n) (z : g) {v : Car (K := K) A U}
    (hv : v ∈ Fil (K := K) A U k) : F z v ∈ Fil (K := K) A U (k + 1) := by
  have : Fil (K := K) A U k ≤ (Fil (K := K) A U (k + 1)).comap (F z) :=
    Fil_le_of fun m u hm =>
      Fil_mono (Nat.succ_le_succ hm) (hF.raise_single p hc bc (lt_of_le_of_lt hm hk) u z)
  exact this hv

theorem card_erase_mmin (m : Multiset A) (h : m ≠ 0) :
    Multiset.card (m.erase (mmin m h)) + 1 = Multiset.card m :=
  Multiset.card_erase_add_one (mmin_mem m h)

theorem good_step {n : ℕ} {F : g →ₗ[K] Module.End K (Car (K := K) A U)}
    (hF : Good p bc n F) : Good p bc (n + 1) (step p hc bc ρ F) := by
  intro m u hm
  constructor
  · intro a
    by_cases h : ∀ b ∈ m, a ≤ b
    · rw [step_y_low p hc bc ρ F h, sub_self]; exact Submodule.zero_mem _
    · rw [step_y_high p hc bc ρ F h]
      have hcard := card_erase_mmin m (ne_zero_of_not_lb h)
      set b := mmin m (ne_zero_of_not_lb h)
      have hlt : Multiset.card (m.erase b) < n := by omega
      have hm' : a ::ₘ b ::ₘ m.erase b = a ::ₘ m := by
        rw [Multiset.cons_erase (mmin_mem m _)]
      simp only [Yrec, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        lsingle_apply, hm']
      rw [add_assoc, add_sub_cancel_left]
      refine Submodule.add_mem _ ?_ ?_
      · have := hF.raise p hc bc hlt (bc b : g) ((hF (m.erase b) u hlt).1 a)
        rwa [hcard] at this
      · have := hF.raise_single p hc bc hlt u ⁅(bc a : g), (bc b : g)⁆
        rwa [hcard] at this
  · intro x
    by_cases h : m = 0
    · subst h; rw [step_p_zero]; exact single_mem_Fil (le_refl _) _
    · rw [step_p_ne p hc bc ρ F x h]
      have hcard := card_erase_mmin m h
      set b := mmin m h
      have hlt : Multiset.card (m.erase b) < n := by omega
      simp only [Xrec, LinearMap.add_apply, LinearMap.comp_apply, lsingle_apply]
      refine Submodule.add_mem _ ?_ ?_
      · have := hF.raise p hc bc hlt (bc b : g) ((hF (m.erase b) u hlt).2 x)
        rwa [hcard] at this
      · have := hF.raise_single p hc bc hlt u ⁅(x : g), (bc b : g)⁆
        rwa [hcard] at this

/-- Agreement of two candidate actions in degrees `< n`. -/
def Agr (n : ℕ) (F G : g →ₗ[K] Module.End K (Car (K := K) A U)) : Prop :=
  ∀ (z : g) (m : Multiset A) (u : U), Multiset.card m < n → F z (single m u) = G z (single m u)

theorem Agr.on_Fil {n : ℕ} {F G : g →ₗ[K] Module.End K (Car (K := K) A U)} (h : Agr n F G)
    {k : ℕ} (hk : k < n) (z : g) {v : Car (K := K) A U} (hv : v ∈ Fil (K := K) A U k) :
    F z v = G z v :=
  eq_on_Fil (fun m u hm => h z m u (lt_of_le_of_lt hm hk)) hv

theorem agr_step {n : ℕ} {F G : g →ₗ[K] Module.End K (Car (K := K) A U)} (hFG : Agr n F G)
    (hF : Good p bc n F) : Agr (n + 1) (step p hc bc ρ F) (step p hc bc ρ G) := by
  intro z m u hm
  induction z using gen_induction p hc bc with
  | h0 => simp
  | hadd z z' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | hsmul r z h => simp only [map_smul, LinearMap.smul_apply, h]
  | hy a =>
      by_cases h : ∀ b ∈ m, a ≤ b
      · rw [step_y_low p hc bc ρ F h, step_y_low p hc bc ρ G h]
      · rw [step_y_high p hc bc ρ F h, step_y_high p hc bc ρ G h]
        have hcard := card_erase_mmin m (ne_zero_of_not_lb h)
        set b := mmin m (ne_zero_of_not_lb h)
        have hlt : Multiset.card (m.erase b) < n := by omega
        simp only [Yrec, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
          lsingle_apply]
        rw [hFG (bc a : g) _ u hlt, hFG _ _ u hlt]
        congr 2
        refine hFG.on_Fil hlt _ ?_
        rw [← hFG (bc a : g) _ u hlt]
        exact (hF (m.erase b) u hlt).1 a
  | hp x =>
      by_cases h : m = 0
      · subst h; rw [step_p_zero, step_p_zero]
      · rw [step_p_ne p hc bc ρ F x h, step_p_ne p hc bc ρ G x h]
        have hcard := card_erase_mmin m h
        set b := mmin m h
        have hlt : Multiset.card (m.erase b) < n := by omega
        simp only [Xrec, LinearMap.add_apply, LinearMap.comp_apply, lsingle_apply]
        rw [hFG (x : g) _ u hlt, hFG _ _ u hlt]
        congr 1
        refine hFG.on_Fil hlt _ ?_
        rw [← hFG (x : g) _ u hlt]
        exact (hF (m.erase b) u hlt).2 x

theorem stage_good (n : ℕ) : Good p bc n (stage p hc bc ρ n) := by
  induction n with
  | zero => intro m u hm; exact absurd hm (Nat.not_lt_zero _)
  | succ n ih => exact good_step p hc bc ρ ih

theorem stage_agr (n : ℕ) : Agr n (stage p hc bc ρ n) (stage p hc bc ρ (n + 1)) := by
  induction n with
  | zero => intro z m u hm; exact absurd hm (Nat.not_lt_zero _)
  | succ n ih => exact agr_step p hc bc ρ ih (stage_good p hc bc ρ n)

theorem stage_stable {m : Multiset A} {n : ℕ} (hn : Multiset.card m < n) (z : g) (u : U) :
    stage p hc bc ρ n z (single m u) = stage p hc bc ρ (Multiset.card m + 1) z (single m u) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [← stage_agr p hc bc ρ n z m u hn, ih]

theorem stage_succ (n : ℕ) : stage p hc bc ρ (n + 1) = step p hc bc ρ (stage p hc bc ρ n) := rfl

/-! ## The limiting action -/

/-- The action of `g` on `M = Multiset A →₀ U`: on degree-`d` basis vectors it is `stage (d+1)`. -/
noncomputable def act : g →ₗ[K] Module.End K (Car (K := K) A U) where
  toFun z := Finsupp.lsum K fun m => stage p hc bc ρ (Multiset.card m + 1) z ∘ₗ lsingle m
  map_add' z z' := by
    refine Finsupp.lhom_ext fun m u => ?_
    simp
  map_smul' r z := by
    refine Finsupp.lhom_ext fun m u => ?_
    simp

theorem act_single (z : g) (m : Multiset A) (u : U) :
    act p hc bc ρ z (single m u) = stage p hc bc ρ (Multiset.card m + 1) z (single m u) := by
  simp [act]

theorem act_eq_stage {m : Multiset A} {n : ℕ} (hn : Multiset.card m < n) (z : g) (u : U) :
    act p hc bc ρ z (single m u) = stage p hc bc ρ n z (single m u) := by
  rw [act_single, stage_stable p hc bc ρ hn]

theorem act_eq_stage_Fil {k n : ℕ} (hk : k < n) (z : g) {v : Car (K := K) A U}
    (hv : v ∈ Fil (K := K) A U k) : act p hc bc ρ z v = stage p hc bc ρ n z v :=
  eq_on_Fil (f := act p hc bc ρ z) (f' := stage p hc bc ρ n z)
    (fun _ u hm => act_eq_stage p hc bc ρ (lt_of_le_of_lt hm hk) z u) hv

/-- The degree bounds hold for the limiting action in every degree. -/
theorem act_good (n : ℕ) : Good p bc n (act p hc bc ρ) := by
  intro m u _
  have h := stage_good p hc bc ρ (Multiset.card m + 1) m u (Nat.lt_succ_self _)
  simp only [act_single]
  exact h

theorem act_raise {k : ℕ} (z : g) {v : Car (K := K) A U} (hv : v ∈ Fil (K := K) A U k) :
    act p hc bc ρ z v ∈ Fil (K := K) A U (k + 1) :=
  (act_good p hc bc ρ (k + 1)).raise p hc bc (Nat.lt_succ_self k) z hv

theorem act_y_sub_mem (a : A) (m : Multiset A) (u : U) :
    act p hc bc ρ (bc a : g) (single m u) - single (a ::ₘ m) u ∈
      Fil (K := K) A U (Multiset.card m) :=
  (act_good p hc bc ρ (Multiset.card m + 1) m u (Nat.lt_succ_self _)).1 a

theorem act_p_mem (x : p) (m : Multiset A) (u : U) :
    act p hc bc ρ (x : g) (single m u) ∈ Fil (K := K) A U (Multiset.card m) :=
  (act_good p hc bc ρ (Multiset.card m + 1) m u (Nat.lt_succ_self _)).2 x

/-- **Defining equation 1.** `y a · (m ⊗ u) = (a :: m) ⊗ u` when `a ≤ m`. -/
theorem act_y_low {a : A} {m : Multiset A} (h : ∀ b ∈ m, a ≤ b) (u : U) :
    act p hc bc ρ (bc a : g) (single m u) = single (a ::ₘ m) u := by
  rw [act_single, stage_succ, step_y_low p hc bc ρ _ h]

/-- **Defining equation 3.** `x · (0 ⊗ u) = 0 ⊗ ρ(x) u` for `x ∈ p`. -/
theorem act_p_zero (x : p) (u : U) :
    act p hc bc ρ (x : g) (single 0 u) = single 0 (ρ x u) := by
  rw [act_single, stage_succ, step_p_zero]

/-- **Defining equation 2.** For `b < a` and `b ≤ m`:
`y a · (b m ⊗ u) = y b · y a · (m ⊗ u) + ⁅y a, y b⁆ · (m ⊗ u)`. -/
theorem act_y_cons {a b : A} {m : Multiset A} (hba : b < a) (hb : ∀ c ∈ m, b ≤ c) (u : U) :
    act p hc bc ρ (bc a : g) (single (b ::ₘ m) u) =
      act p hc bc ρ (bc b : g) (act p hc bc ρ (bc a : g) (single m u)) +
        act p hc bc ρ ⁅(bc a : g), (bc b : g)⁆ (single m u) := by
  have hn : ¬ ∀ c ∈ b ::ₘ m, a ≤ c := fun h =>
    absurd (h b (Multiset.mem_cons_self _ _)) (not_le.mpr hba)
  rw [act_single, stage_succ, step_y_high p hc bc ρ _ hn]
  have hmin : mmin (b ::ₘ m) (ne_zero_of_not_lb hn) = b := mmin_cons hb _
  rw [hmin, Multiset.erase_cons_head]
  simp only [Yrec, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, lsingle_apply]
  have hlt : Multiset.card m < Multiset.card (b ::ₘ m) := by simp
  have hw := act_y_sub_mem p hc bc ρ a m u
  rw [← act_eq_stage p hc bc ρ hlt (bc a : g) u, ← act_eq_stage p hc bc ρ hlt _ u]
  rw [← act_eq_stage_Fil p hc bc ρ hlt (bc b : g) hw]
  have hlow : ∀ c ∈ a ::ₘ m, b ≤ c := by
    intro c hc'
    rcases Multiset.mem_cons.mp hc' with rfl | hc'
    · exact hba.le
    · exact hb c hc'
  rw [map_sub, act_y_low p hc bc ρ hlow, Multiset.cons_swap]
  abel

/-- **Defining equation 4.** For `x ∈ p` and `b ≤ m`:
`x · (b m ⊗ u) = y b · x · (m ⊗ u) + ⁅x, y b⁆ · (m ⊗ u)`. -/
theorem act_p_cons (x : p) {b : A} {m : Multiset A} (hb : ∀ c ∈ m, b ≤ c) (u : U) :
    act p hc bc ρ (x : g) (single (b ::ₘ m) u) =
      act p hc bc ρ (bc b : g) (act p hc bc ρ (x : g) (single m u)) +
        act p hc bc ρ ⁅(x : g), (bc b : g)⁆ (single m u) := by
  have hne : b ::ₘ m ≠ 0 := Multiset.cons_ne_zero
  rw [act_single, stage_succ, step_p_ne p hc bc ρ _ x hne]
  have hmin : mmin (b ::ₘ m) hne = b := mmin_cons hb _
  rw [hmin, Multiset.erase_cons_head]
  simp only [Xrec, LinearMap.add_apply, LinearMap.comp_apply, lsingle_apply]
  have hlt : Multiset.card m < Multiset.card (b ::ₘ m) := by simp
  have hw := act_p_mem p hc bc ρ x m u
  rw [← act_eq_stage p hc bc ρ hlt (x : g) u, ← act_eq_stage p hc bc ρ hlt _ u]
  rw [← act_eq_stage_Fil p hc bc ρ hlt (bc b : g) hw]

end VOA.PBWTheorem
