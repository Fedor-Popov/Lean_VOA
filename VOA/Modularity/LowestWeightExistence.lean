/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchFaithfulBijection
import VOA.Modules.Rationality

/-!
# Every irreducible `𝒱`-module has a lowest weight — link **L3**

Link **(L3)** `#IrrLWModuleIsoClass = #Φ(𝒱)` of the count behind Zhu Thm 5.3.3 is Gannon
Lemma 5.3.3's existence half.  This file supplies it, unconditionally.

⚠ **Scope.**  `Modules/Rationality.lean:194-207` frames the residual of Lemma 5.3.3 as
the **rationality** `h(M) ∈ ℚ`, and defers it to the modularity layer as a consequence of modular
invariance.
That is right for rationality — but L3 needs only *existence* of `h ∈ ℂ`, which is a
Zhu-algebra-level
statement needing no modularity at all.  It is proved here from the `OrdVModule` axioms alone.

## The argument (Gannon Lemma 5.3.3, existence half)

All mode weight-shifts are integers: `v ∈ 𝒱_β` sends `M_α → M_{α+β-n-1}` (`mode_mem_weight`).
Hence for any `α₀` the span of the weight spaces along the coset `α₀ + ℤ` is a *weak submodule*
(`cosetSubmodule`).  If `M` is irreducible and `M_{α₀} ≠ 0`, that submodule is not `⊥`, so it is
`⊤`; independence of the grading then forces **every** nonzero weight to lie in `α₀ + ℤ`
(`weight_eq_coset_of_irreducible`).  The exponent set `{k : ℤ | M_{α₀+k} ≠ 0}` is nonempty and
bounded below — `OrdVModule.boundedBelow` bounds `Re` — so it has a least element `k₀`
(`Int.exists_least_of_bdd`), and `h := α₀ + k₀` is a realized lowest weight.

## Main results

* `OrdVModule.cosetSubmodule` — the coset span is a weak submodule (the one real computation);
* `OrdVModule.exists_isLowestWeight_of_irreducible` — Lemma 5.3.3, existence half;
* `OrdVModule.exists_hasConformalWeight_of_irreducible` — the same in Gannon's spelling;
* `IrrModule.toIrrLWModule` / `irrLWModuleIsoClass_equiv_Φ` — **L3**: `Φ(𝒱)` and the faithful
  `IrrLWModuleIsoClass W` are in bijection.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

namespace OrdVModule

/-! ## The coset span -/

/-- The `ℂ`-subspace spanned by the weight spaces along the coset `α₀ + ℤ`. -/
def cosetSpace (N : OrdVModule W M) (α₀ : ℂ) : Submodule ℂ M := ⨆ k : ℤ, N.weight (α₀ + (k : ℂ))

theorem weight_le_cosetSpace (N : OrdVModule W M) (α₀ : ℂ) (k : ℤ) :
    N.weight (α₀ + (k : ℂ)) ≤ N.cosetSpace α₀ := le_iSup (fun k : ℤ => N.weight (α₀ + (k : ℂ))) k

/-- A homogeneous mode of a homogeneous vector stays in the coset span: the weight shift
`α + β - n - 1` moves along `ℤ`. -/
theorem act_mem_cosetSpace_homog (N : OrdVModule W M) (α₀ : ℂ) {β : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading β) (n : ℤ) {k : ℤ} {x : M} (hx : x ∈ N.weight (α₀ + (k : ℂ))) :
    N.act u n x ∈ N.cosetSpace α₀ := by
  have hshift := mode_mem_weight N hu hx n
  refine weight_le_cosetSpace N α₀ (k + β - n - 1) ?_
  have : α₀ + ((k + β - n - 1 : ℤ) : ℂ) = α₀ + (k : ℂ) + (β : ℂ) - (n : ℂ) - 1 := by
    push_cast; ring
  rw [this]
  exact hshift

/-- Any mode of a *homogeneous* vector stays in the coset span (`u` arbitrary). -/
theorem act_mem_cosetSpace_of_weight (N : OrdVModule W M) (α₀ : ℂ) (u : 𝒱) (n : ℤ) {k : ℤ}
    {x : M} (hx : x ∈ N.weight (α₀ + (k : ℂ))) : N.act u n x ∈ N.cosetSpace α₀ := by
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => N.act u n x ∈ N.cosetSpace α₀) hutop ?_ ?_ ?_
  · intro β v hv; exact act_mem_cosetSpace_homog N α₀ hv n hx
  · change N.act (0 : 𝒱) n x ∈ N.cosetSpace α₀
    have hz : N.act (0 : 𝒱) n x = 0 := by
      have h0 := WeakModule.act_add_left N.toWeakModule (0 : 𝒱) (0 : 𝒱) n x
      rw [add_zero] at h0
      simpa using h0
    rw [hz]
    exact Submodule.zero_mem _
  · intro u₁ u₂ h₁ h₂
    change N.act (u₁ + u₂) n x ∈ N.cosetSpace α₀
    rw [WeakModule.act_add_left]
    exact Submodule.add_mem _ h₁ h₂

/-- **The coset span is a weak submodule.**  This is the one real computation of L3: every mode
shifts the weight by an *integer*, so the coset `α₀ + ℤ` is mode-stable. -/
def cosetSubmodule (N : OrdVModule W M) (α₀ : ℂ) : WeakModule.Submodule' N.toWeakModule where
  carrier := N.cosetSpace α₀
  act_mem := by
    intro u n x hx
    refine Submodule.iSup_induction (fun k : ℤ => N.weight (α₀ + (k : ℂ)))
      (motive := fun x => N.act u n x ∈ N.cosetSpace α₀) hx ?_ ?_ ?_
    · intro k y hy; exact act_mem_cosetSpace_of_weight N α₀ u n hy
    · change N.act u n (0 : M) ∈ N.cosetSpace α₀
      rw [WeakModule.act_zero_right]
      exact Submodule.zero_mem _
    · intro y z hy hz
      change N.act u n (y + z) ∈ N.cosetSpace α₀
      rw [WeakModule.act_add_right]
      exact Submodule.add_mem _ hy hz

/-! ## Existence of a realized lowest weight -/

/-- A nontrivial graded module has a nonzero weight space. -/
theorem exists_weight_ne_bot (N : OrdVModule W M) (hnt : Nontrivial M) :
    ∃ α : ℂ, N.weight α ≠ ⊥ := by
  by_contra hc
  push_neg at hc
  have htop : (⊤ : Submodule ℂ M) = ⊥ := by
    rw [← N.isInternal.submodule_iSup_eq_top]
    exact iSup_eq_bot.mpr hc
  obtain ⟨x, y, hxy⟩ := hnt
  have hx : x = 0 := by
    have : x ∈ (⊥ : Submodule ℂ M) := htop ▸ Submodule.mem_top
    rwa [Submodule.mem_bot] at this
  have hy : y = 0 := by
    have : y ∈ (⊥ : Submodule ℂ M) := htop ▸ Submodule.mem_top
    rwa [Submodule.mem_bot] at this
  exact hxy (hx.trans hy.symm)

/-- **All weights of an irreducible module lie in one `ℤ`-coset.** -/
theorem weight_eq_coset_of_irreducible (N : OrdVModule W M) (hirr : N.IsIrreducible)
    {α₀ : ℂ} (h₀ : N.weight α₀ ≠ ⊥) {α : ℂ} (hα : N.weight α ≠ ⊥) :
    ∃ k : ℤ, α = α₀ + (k : ℂ) := by
  classical
  -- The coset span is `⊤`.
  have hzero : N.weight α₀ ≤ N.cosetSpace α₀ := by
    have := weight_le_cosetSpace N α₀ 0
    simpa using this
  have htop : N.cosetSpace α₀ = ⊤ := by
    rcases hirr.2 (cosetSubmodule N α₀) with hb | ht
    · exact absurd (le_bot_iff.mp (hb ▸ hzero)) h₀
    · exact ht
  -- Pick a nonzero vector of weight `α` and expand it in the coset.
  by_contra hc
  push_neg at hc
  obtain ⟨y, hy, hy0⟩ : ∃ y ∈ N.weight α, y ≠ 0 := by
    by_contra hcc
    push_neg at hcc
    exact hα (Submodule.eq_bot_iff _ |>.mpr hcc)
  have hmem : y ∈ N.cosetSpace α₀ := htop ▸ Submodule.mem_top
  -- The coset span sits inside the supremum of the *other* weight spaces.
  have hle : N.cosetSpace α₀ ≤ ⨆ γ, ⨆ _ : γ ≠ α, N.weight γ := by
    refine iSup_le fun k => ?_
    refine le_trans (le_of_eq rfl) ?_
    exact le_iSup_of_le (α₀ + (k : ℂ)) (le_iSup_of_le (fun hEq => hc k hEq.symm) le_rfl)
  have hdisj := N.isInternal.submodule_iSupIndep α
  have : y ∈ (⊥ : Submodule ℂ M) :=
    (disjoint_iff.mp hdisj) ▸ Submodule.mem_inf.mpr ⟨hy, hle hmem⟩
  exact hy0 (Submodule.mem_bot _ |>.mp this)

/-- **Gannon Lemma 5.3.3, existence half.**  Every irreducible `𝒱`-module has a *realized*
lowest weight: some `h : ℂ` with `M_h ≠ 0` and every nonzero weight in `h + ℕ`. -/
theorem exists_isLowestWeight_of_irreducible (N : OrdVModule W M) (hirr : N.IsIrreducible) :
    ∃ h : ℂ, IsLowestWeight N h ∧ N.weight h ≠ ⊥ := by
  classical
  obtain ⟨α₀, h₀⟩ := exists_weight_ne_bot N hirr.1
  obtain ⟨B, hB⟩ := N.boundedBelow
  -- The exponent set of the coset.
  have hinh : ∃ k : ℤ, N.weight (α₀ + (k : ℂ)) ≠ ⊥ := ⟨0, by simpa using h₀⟩
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, N.weight (α₀ + (k : ℂ)) ≠ ⊥ → b ≤ k := by
    refine ⟨⌈B - α₀.re⌉, fun k hk => ?_⟩
    have hre : B ≤ (α₀ + (k : ℂ)).re := hB _ hk
    have : B - α₀.re ≤ (k : ℝ) := by
      simp only [Complex.add_re, Complex.intCast_re] at hre
      linarith
    exact Int.ceil_le.mpr (by simpa using this)
  obtain ⟨k₀, hk₀, hmin⟩ := Int.exists_least_of_bdd hbdd hinh
  refine ⟨α₀ + (k₀ : ℂ), ?_, hk₀⟩
  intro α hα
  obtain ⟨k, rfl⟩ := weight_eq_coset_of_irreducible N hirr h₀ hα
  have hle : k₀ ≤ k := hmin k hα
  refine ⟨(k - k₀).toNat, ?_⟩
  have : ((k - k₀).toNat : ℤ) = k - k₀ := Int.toNat_of_nonneg (by omega)
  have hcast : (((k - k₀).toNat : ℕ) : ℂ) = ((k - k₀ : ℤ) : ℂ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) this
  rw [hcast]
  push_cast
  ring

/-- Gannon's spelling: an irreducible module *has a conformal weight*. -/
theorem exists_hasConformalWeight_of_irreducible (N : OrdVModule W M) (hirr : N.IsIrreducible) :
    ∃ h : ℂ, HasConformalWeight N h := by
  obtain ⟨h, hlow, hne⟩ := exists_isLowestWeight_of_irreducible N hirr
  exact ⟨h, hne, hlow⟩

end OrdVModule

/-! ## L3 — the faithful domain is `Φ(𝒱)` -/

/-- Forgetting the lowest weight: an irreducible lowest-weight module *is* an irreducible module. -/
def IrrLWModule.forget (P : IrrLWModule W) : IrrModule W where
  carrier := P.1.carrier
  isMod := P.1.isMod
  irreducible := P.2

@[simp] theorem IrrLWModule.forget_isMod (P : IrrLWModule W) : (P.forget).isMod = P.1.isMod := rfl

/-- **The converse — every irreducible module carries a realized lowest weight** (Lemma 5.3.3,
existence half).  This is the map L3 was missing. -/
noncomputable def IrrModule.toIrrLWModule (V : IrrModule W) : IrrLWModule W :=
  ⟨{ carrier := V.carrier
     isMod := V.isMod
     h := (OrdVModule.exists_isLowestWeight_of_irreducible V.isMod V.irreducible).choose
     isLow := (OrdVModule.exists_isLowestWeight_of_irreducible V.isMod V.irreducible).choose_spec.1
     realized :=
       (OrdVModule.exists_isLowestWeight_of_irreducible V.isMod V.irreducible).choose_spec.2 },
   V.irreducible⟩

@[simp] theorem IrrModule.toIrrLWModule_isMod (V : IrrModule W) :
    (V.toIrrLWModule).1.isMod = V.isMod := rfl

/-- Forgetting the lowest weight is faithful on iso-classes: both notions of isomorphism are
`Nonempty (ModuleEquiv W _ _)` on the *same* underlying `OrdVModule`. -/
theorem IrrLWModule.iso_iff_forget (P Q : IrrLWModule W) :
    IrrLWModule.Iso P Q ↔ IrrModule.Iso W P.forget Q.forget := Iff.rfl

/-- The forgetful map on iso-classes. -/
def forgetClass (W : VertexOperatorAlgebra 𝒱) : IrrLWModuleIsoClass W → Φ W :=
  Quotient.lift (fun P => (Quotient.mk (IrrModule.setoid W) (IrrLWModule.forget P) : Φ W))
    (fun _ _ h => Quotient.sound h)

/-- Its inverse, supplied by the existence half of Lemma 5.3.3. -/
noncomputable def lowestWeightClass (W : VertexOperatorAlgebra 𝒱) : Φ W → IrrLWModuleIsoClass W :=
  Quotient.lift
    (fun V => (Quotient.mk (IrrLWModule.setoid W) (IrrModule.toIrrLWModule V)
      : IrrLWModuleIsoClass W))
    (fun _ _ h => Quotient.sound h)

/-- **L3.**  The faithful domain `IrrLWModuleIsoClass W` of Theorem 5.3.4 *is* Gannon's
`Φ(𝒱)`.  The forgetful map is a bijection: injectivity is definitional (both setoids are
`Nonempty (ModuleEquiv W _ _)` on the same underlying `OrdVModule`), and surjectivity is exactly the
existence half of Lemma 5.3.3, `OrdVModule.exists_isLowestWeight_of_irreducible`. -/
noncomputable def irrLWModuleIsoClass_equiv_Φ (W : VertexOperatorAlgebra 𝒱) :
    IrrLWModuleIsoClass W ≃ Φ W where
  toFun := forgetClass W
  invFun := lowestWeightClass W
  left_inv := by
    refine Quotient.ind fun P => ?_
    exact Quotient.sound ⟨ModuleEquiv.refl P.1.isMod⟩
  right_inv := by
    refine Quotient.ind fun V => ?_
    exact Quotient.sound ⟨ModuleEquiv.refl V.isMod⟩

/-- **L3 as a cardinality statement.** -/
theorem nonempty_equiv_irrLWModuleIsoClass_Φ (W : VertexOperatorAlgebra 𝒱) :
    Nonempty (IrrLWModuleIsoClass W ≃ Φ W) :=
  ⟨irrLWModuleIsoClass_equiv_Φ W⟩

end VOA
