/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.AnFiniteDim
import VOA.Modules.ZhuModule
import Mathlib.Data.Set.Finite.List

/-!
# Gaberdiel–Neitzke Theorem 11: strict-decrease spanning ⟹ `C_m`-cofiniteness

Read from the primary source (Gaberdiel–Neitzke, `hep-th/0009235`):

> **Proposition 8.**  `ℋ` is spanned by the states `V_{(−N₁)}(W_{i₁})⋯V_{(−N_k)}(W_{i_k})Ω`
> where `N₁ > N₂ > ⋯ > N_k > 0`.
>
> **Theorem 11.**  Suppose `A_{(2)}` is finite-dimensional.  Then all `A_u` are
> finite-dimensional.

**Strict** decrease is the whole point, and this file is the half that consumes it.  Modulo
`C_m(𝒱)` a monomial dies as soon as its **outermost** mode index is `≥ m`; strict decrease then
confines the survivors to mode indices in `[1, m−1]`, *pairwise distinct*, so the **length** is
`< m` and there are finitely many survivors.  A weakly-decreasing spanning set — which is what
`Modularity.BuhlSpanningC2.orderedSpanningData_adjoint_of_C2Cofinite` supplies — is useless here:
`x₍₋₁₎^k 𝟙` is weakly decreasing of unbounded length and never dies.

## Main results

* `CGen_le_of_le` — `C_j(𝒱) ⊆ C_k(𝒱)` for `1 ≤ k ≤ j`, off the translation property;
* `modeWord`, `StrictDec`, `StrictSpanning` — GN Prop. 8 as a datum;
* `strictDec_length_le` — strict decrease bounds the length by the largest mode index;
* `cofinite_of_strictSpanning` — **GN Theorem 11**: the datum gives `dim 𝒱/C_m < ∞` for
  every `m ≥ 1`, with a *homogeneous* finite spanning family;
* `hcof_of_strictSpanning` — in exactly the shape
  `Modularity.RealizationCofinite.simpleAModsRealized_of_cofinite` consumes.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  `StrictSpanning` is GN Prop. 8, carried as a
**named datum** — this file is the consumption half only.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `C`-tower is decreasing -/

/-- `C_{k+1}(𝒱) ⊆ C_k(𝒱)` for `k ≥ 1`, since `a₍₋ₖ₋₁₎b = k⁻¹·(L₋₁a)₍₋ₖ₎b`. -/
theorem CGen_succ_le (W : VertexOperatorAlgebra 𝒱) {k : ℕ} (hk : 1 ≤ k) :
    CGen W (-((k : ℤ) + 1)) ≤ CGen W (-(k : ℤ)) := by
  rw [CGen, Submodule.span_le]
  rintro x ⟨a, b, rfl⟩
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrel := smul_L_neg_one W a b (-(k : ℤ))
  rw [show (-(k : ℤ) - 1) = (-((k : ℤ) + 1)) by ring, neg_neg] at hrel
  have hcast : ((k : ℤ)) • W.smul a (-((k : ℤ) + 1)) b
      = (k : ℂ) • W.smul a (-((k : ℤ) + 1)) b := by
    rw [← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    ring_nf
  rw [hcast] at hrel
  have hx : W.smul a (-((k : ℤ) + 1)) b
      = (k : ℂ)⁻¹ • W.smul (W.L (-1) a) (-(k : ℤ)) b := by
    rw [hrel, smul_smul, inv_mul_cancel₀ hk0, one_smul]
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨W.L (-1) a, b, rfl⟩)

/-- `C_j(𝒱) ⊆ C_k(𝒱)` for `1 ≤ k ≤ j`. -/
theorem CGen_le_of_le (W : VertexOperatorAlgebra 𝒱) {k : ℕ} (hk : 1 ≤ k) :
    ∀ j : ℕ, k ≤ j → CGen W (-(j : ℤ)) ≤ CGen W (-(k : ℤ)) := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ p ih =>
      intro hkp
      rcases Nat.lt_or_ge k (p + 1) with hlt | hge
      · have hkp' : k ≤ p := by omega
        refine le_trans ?_ (ih hkp')
        have hp1 : 1 ≤ p := by omega
        have := CGen_succ_le W hp1
        rwa [show ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) by push_cast; ring] at this
      · have : k = p + 1 := by omega
        rw [this]

/-! ## Mode words and strict decrease -/

/-- The monomial `gen_{i₁,(−n₁)} ⋯ gen_{i_k,(−n_k)} x`, outermost mode first. -/
noncomputable def modeWord (W : VertexOperatorAlgebra 𝒱) {g : ℕ} (gen : Fin g → 𝒱) :
    List (Fin g × ℕ) → 𝒱 → 𝒱
  | [], x => x
  | p :: l, x => W.smul (gen p.1) (-(p.2 : ℤ)) (modeWord W gen l x)

/-- **Strictly decreasing** mode indices, all `≥ 1`. -/
def StrictDec {g : ℕ} (l : List (Fin g × ℕ)) : Prop :=
  List.Pairwise (fun a b : Fin g × ℕ => b.2 < a.2) l ∧ ∀ p ∈ l, 1 ≤ p.2

/-- **Strict decrease bounds the length.**  A strictly decreasing list of positive mode indices
all `≤ n` has length `≤ n`. -/
theorem strictDec_length_le {g : ℕ} :
    ∀ (l : List (Fin g × ℕ)), StrictDec l → ∀ n : ℕ, (∀ p ∈ l, p.2 ≤ n) → l.length ≤ n := by
  intro l
  induction l with
  | nil => intro _ n _; simp
  | cons p l ih =>
      rintro ⟨hpw, hpos⟩ n hle
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpw
      have hp1 : 1 ≤ p.2 := hpos p (List.mem_cons_self ..)
      have hpn : p.2 ≤ n := hle p (List.mem_cons_self ..)
      have hrec : l.length ≤ p.2 - 1 := by
        refine ih ⟨htail, fun q hq => hpos q (List.mem_cons_of_mem _ hq)⟩ (p.2 - 1) ?_
        intro q hq
        have := hhead q hq
        omega
      simp only [List.length_cons]
      omega

/-- A mode word on the vacuum is homogeneous. -/
theorem modeWord_homog (W : VertexOperatorAlgebra 𝒱) {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) :
    ∀ l : List (Fin g × ℕ), IsHomog W (modeWord W gen l W.vacuum) := by
  intro l
  induction l with
  | nil => exact ⟨0, W.vacuum_mem_grading_zero⟩
  | cons p l ih =>
      obtain ⟨d, hd⟩ := ih
      exact ⟨(wt p.1 : ℤ) + d + (p.2 : ℤ) - 1, step_mem_grading W (hgen p.1) hd⟩

/-- A nonempty mode word lies in the `C`-space of its outermost mode index. -/
theorem modeWord_cons_mem_CGen (W : VertexOperatorAlgebra 𝒱) {g : ℕ} (gen : Fin g → 𝒱)
    (p : Fin g × ℕ) (l : List (Fin g × ℕ)) (x : 𝒱) :
    modeWord W gen (p :: l) x ∈ CGen W (-(p.2 : ℤ)) :=
  Submodule.subset_span ⟨gen p.1, modeWord W gen l x, rfl⟩

/-! ## GN Proposition 8, as a datum -/

/-- **Gaberdiel–Neitzke Prop. 8**: `𝒱` is spanned by mode words on the vacuum with **strictly
decreasing** positive mode indices, over finitely many homogeneous generators. -/
structure StrictSpanning (W : VertexOperatorAlgebra 𝒱) where
  /-- Number of generators. -/
  g : ℕ
  /-- The generators. -/
  gen : Fin g → 𝒱
  /-- Their conformal weights. -/
  wt : Fin g → ℕ
  /-- The generators are homogeneous. -/
  gen_mem : ∀ i, gen i ∈ W.grading (wt i : ℤ)
  /-- The strictly decreasing mode words span. -/
  spans : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ
    {x | ∃ l : List (Fin g × ℕ), StrictDec l ∧ x = modeWord W gen l W.vacuum}

/-! ## GN Theorem 11 -/

/-- **Gaberdiel–Neitzke Theorem 11.**  Strict-decrease spanning gives `C_m`-cofiniteness for
every `m ≥ 1`, with a homogeneous finite spanning family. -/
theorem cofinite_of_strictSpanning {W : VertexOperatorAlgebra 𝒱} (d : StrictSpanning W)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ S : Finset 𝒱, (∀ s ∈ (S : Set 𝒱), IsHomog W s) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (S : Set 𝒱) ⊔ CGen W (-(m : ℤ)) := by
  classical
  -- the surviving words: strictly decreasing, all mode indices `< m`
  set Surv : Set 𝒱 := {x | ∃ l : List (Fin d.g × ℕ), StrictDec l ∧ (∀ p ∈ l, p.2 < m) ∧
    x = modeWord W d.gen l W.vacuum} with hSurv
  have hfin : Surv.Finite := by
    have hsub : Surv ⊆ (fun L : List (Fin d.g × Fin m) =>
        modeWord W d.gen (L.map (fun q => (q.1, (q.2 : ℕ)))) W.vacuum) ''
        {L : List (Fin d.g × Fin m) | L.length ≤ m} := by
      rintro x ⟨l, hdec, hlt, rfl⟩
      refine ⟨l.pmap (fun p (hp : p.2 < m) => (p.1, (⟨p.2, hp⟩ : Fin m))) hlt, ?_, ?_⟩
      · rw [Set.mem_setOf_eq, List.length_pmap]
        exact strictDec_length_le l hdec m (fun p hp => le_of_lt (hlt p hp))
      · have hmp : (l.pmap (fun p (hp : p.2 < m) => (p.1, (⟨p.2, hp⟩ : Fin m))) hlt).map
            (fun q : Fin d.g × Fin m => (q.1, (q.2 : ℕ))) = l := by
          rw [List.map_pmap]
          simp
        show modeWord W d.gen ((l.pmap (fun p (hp : p.2 < m) =>
          (p.1, (⟨p.2, hp⟩ : Fin m))) hlt).map
            (fun q : Fin d.g × Fin m => (q.1, (q.2 : ℕ)))) W.vacuum
          = modeWord W d.gen l W.vacuum
        rw [hmp]
    exact Set.Finite.subset ((List.finite_length_le _ m).image _) hsub
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro s hs
    rw [Set.Finite.coe_toFinset] at hs
    obtain ⟨l, _, _, rfl⟩ := hs
    exact modeWord_homog W d.gen_mem l
  · refine le_antisymm ?_ le_top
    rw [d.spans, Submodule.span_le]
    rintro x ⟨l, hdec, rfl⟩
    match l, hdec with
    | [], hdec =>
        refine Submodule.mem_sup_left (Submodule.subset_span ?_)
        rw [Set.Finite.coe_toFinset]
        exact ⟨[], hdec, by simp, rfl⟩
    | (p :: l'), hdec =>
        by_cases hp : p.2 < m
        · refine Submodule.mem_sup_left (Submodule.subset_span ?_)
          rw [Set.Finite.coe_toFinset]
          refine ⟨p :: l', hdec, fun q hq => ?_, rfl⟩
          obtain ⟨hhead, _⟩ := List.pairwise_cons.mp hdec.1
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact hp
          · exact lt_trans (hhead q hq') hp
        · refine Submodule.mem_sup_right ?_
          refine CGen_le_of_le W hm p.2 (by omega) ?_
          exact modeWord_cons_mem_CGen W d.gen p l' W.vacuum

/-- In the shape `Modularity.RealizationCofinite.simpleAModsRealized_of_cofinite` consumes. -/
theorem hcof_of_strictSpanning {W : VertexOperatorAlgebra 𝒱} (d : StrictSpanning W) :
    ∀ n : ℕ, ∃ S : Finset 𝒱, (∀ s ∈ (S : Set 𝒱), IsHomog W s) ∧
      (⊤ : Submodule ℂ 𝒱)
        = Submodule.span ℂ (S : Set 𝒱) ⊔ CGen W (-((n : ℤ) + 2)) := by
  intro n
  obtain ⟨S, hShom, htop⟩ := cofinite_of_strictSpanning d (n + 2) (by omega)
  exact ⟨S, hShom, by rwa [show (((n + 2 : ℕ)) : ℤ) = (n : ℤ) + 2 by push_cast; ring] at htop⟩

end VOA
