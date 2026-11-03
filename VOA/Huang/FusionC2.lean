/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.FusionTop
import VOA.Classification.COne.Statement

/-!
# `C₂`-cofinite modules have finite-dimensional `M/O(M)`; finiteness of fusion rules

For a weak module `M` put `C₂(M) = span{a₍₋₂₎m}` (`C2M`) and call `M` **`C₂`-cofinite** if
`M/C₂(M)` is finite-dimensional (`ModuleC2Cofinite`).  For an `ℕ`-graded (admissible) module the
Frenkel–Zhu residue `fzRes p 0 a m = ∑_{i ≤ p} C(p,i) a₍ᵢ₋₂₎m ∈ O(M)` has leading term `a₍₋₂₎m` and
all other terms at strictly lower level, so modulo `O(M)` every `a₍₋₂₎m` drops in level
(`smul_negTwo_mem`); a level induction (`lev_le_span_sup_fzO`) shows that homogeneous
`C₂`-generators
span `M` modulo `O(M)`.  Hence

* `finiteDimensional_fzQuot_of_C2` — `M` admissible and `C₂`-cofinite ⟹ `M/O(M)` is
  finite-dimensional (the module analogue of `finiteDimensional_A_of_C2Cofinite`; Frenkel–Zhu /
  Abe–Buhl–Dong);
* `finiteDimensional_intertwiningSpace_of_C2` — for lowest-weight `P₁` that is `C₂`-cofinite
  and irreducible lowest-weight `P₂, P₃`, the space of intertwining operators of type
  `(P₃ / P₁ P₂)` is finite-dimensional, so `fusionRule` is an honest dimension, with the bound
  `fusionRule_le_of_C2`.
* `ModuleC2Input` — the named published input "irreducible modules of a strongly rational VOA are
  `C₂`-cofinite" (Buhl 2002; Abe–Buhl–Dong 2004), and
  `finiteDimensional_intertwiningSpace_nice`: for a nice `V`, all intertwiner spaces among
  irreducible lowest-weight modules are finite-dimensional, conditional on `ModuleC2Input` only.

## Status
No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

namespace VOA.Huang.FusionC2

open VOA VOA.FZ VOA.Huang.BottomRecovery VOA.Huang.LWBottomRecovery VOA.Huang.FusionTop
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- `C₂(M) = span{a₍₋₂₎m : a ∈ V, m ∈ M}`. -/
def C2M {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) : Submodule ℂ M :=
  Submodule.span ℂ {x | ∃ (a : 𝒱) (m : M), x = mode (A.YM a) (-2) m}

/-- A weak module is **`C₂`-cofinite** if `M/C₂(M)` is finite-dimensional. -/
def ModuleC2Cofinite {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) : Prop :=
  FiniteDimensional ℂ (M ⧸ C2M A)

section Admissible

variable {M : Type u} [AddCommGroup M] [Module ℂ M] (N : AdmissibleModule W M)

/-- Induction over the level decomposition of an admissible module. -/
@[elab_as_elim]
theorem induction_lev {motive : M → Prop} (w : M) (h0 : motive 0)
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hhom : ∀ k, ∀ x ∈ N.lev k, motive x) : motive w := by
  have htop : w ∈ ⨆ k, N.lev k := by
    rw [N.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := motive) htop hhom h0 hadd

/-- Induction over the grading of `V`. -/
@[elab_as_elim]
theorem induction_grading {motive : 𝒱 → Prop} (a : 𝒱) (h0 : motive 0)
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hhom : ∀ p, ∀ x ∈ W.grading p, motive x) : motive a := by
  have htop : a ∈ ⨆ p, W.grading p := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := motive) htop hhom h0 hadd

/-- The level-`k` homogeneous generators of `C₂(M)`. -/
def C2Deg (k : ℤ) : Submodule ℂ M :=
  Submodule.span ℂ {x | ∃ (a : 𝒱) (p j : ℤ) (m : M), a ∈ W.grading p ∧ m ∈ N.lev j ∧
    j + p + 1 = k ∧ x = mode (N.YM a) (-2) m}

/-- The level-`k` component of an element of `C₂(M)` lies in `C2Deg k`. -/
theorem levProj_C2M (k : ℤ) {c : M} (hc : c ∈ C2M N.toWeakModule) :
    levProj N k c ∈ C2Deg N k := by
  induction hc using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, m, rfl⟩ := hz
    refine induction_grading (W := W) (motive := fun a => levProj N k (mode (N.YM a) (-2) m) ∈ C2Deg N k)
      a (by simp) (fun x y hx hy => ?_) (fun p a ha => ?_)
    · simp only [map_add, mode_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hx hy
    · refine induction_lev N (motive := fun m => levProj N k (mode (N.YM a) (-2) m) ∈ C2Deg N k)
        m (by simp) (fun x y hx hy => ?_) (fun j m hm => ?_)
      · beta_reduce at hx hy ⊢
        rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
      · beta_reduce
        have hmem : mode (N.YM a) (-2) m ∈ N.lev (j + (p - (-2) - 1)) := N.act_lev ha hm
        by_cases hk : k = j + (p - (-2) - 1)
        · rw [hk, levProj_of_mem N hmem]
          exact Submodule.subset_span ⟨a, p, j, m, ha, hm, by omega, rfl⟩
        · rw [levProj_of_mem_ne N hmem hk]; exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- **The one-step absorption** (module version of `smul_negTwo_mem_of_lower_O`): for
`a ∈ V_p`, `m ∈ M(j)`, the vector `a₍₋₂₎m` (level `j + p + 1`) lies in every subspace containing
`O(M)` and all levels below `j + p + 1`. -/
theorem smul_negTwo_mem {p j : ℤ} {a : 𝒱} {m : M} (ha : a ∈ W.grading p) (hm : m ∈ N.lev j)
    (T : Submodule ℂ M) (hO : fzO N.toWeakModule ≤ T)
    (hT : ∀ k', k' < j + p + 1 → N.lev k' ≤ T) :
    mode (N.YM a) (-2) m ∈ T := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [W.positivity p hp, Submodule.mem_bot] at ha
    rw [ha, map_zero, mode_zero, LinearMap.zero_apply]; exact T.zero_mem
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, p = (P : ℤ) := ⟨p.toNat, by omega⟩
  have hres := fzRes_mem_fzO N.toWeakModule 0 ha m
  rw [fzRes, Finset.sum_range_succ'] at hres
  simp only [Nat.cast_zero, add_zero, zero_sub, cbz_zero, one_smul] at hres
  have hsum : ∑ i ∈ Finset.range P, cbz (P : ℤ) ((i + 1 : ℕ) : ℤ) •
      mode (N.YM a) (((i + 1 : ℕ) : ℤ) - 2) m ∈ T := by
    refine Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ ?_)
    have h := N.act_lev ha hm (p := ((i + 1 : ℕ) : ℤ) - 2)
    refine hT _ ?_ h
    simp only [Finset.mem_range] at hi
    push_cast; omega
  have := T.sub_mem (hO hres) hsum
  simp only [sub_zero] at this
  rwa [add_sub_cancel_left] at this

variable {N}

/-- **Level induction**: if homogeneous `S` spans `M` modulo `C₂(M)`, then every level lies in
`span S ⊔ O(M)`. -/
theorem lev_le_span_sup_fzO {S : Set M} (hShom : ∀ s ∈ S, ∃ k, s ∈ N.lev k)
    (htop : (⊤ : Submodule ℂ M) = Submodule.span ℂ S ⊔ C2M N.toWeakModule) (k : ℤ) :
    N.lev k ≤ Submodule.span ℂ S ⊔ fzO N.toWeakModule := by
  set T := Submodule.span ℂ S ⊔ fzO N.toWeakModule with hTdef
  rcases lt_or_ge k 0 with hk | hk
  · rw [N.lev_eq_bot_of_neg k hk]; exact bot_le
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, k = (K : ℤ) := ⟨k.toNat, by omega⟩
  induction K using Nat.strong_induction_on with
  | _ K IH =>
  have hlow : ∀ k', k' < (K : ℤ) → N.lev k' ≤ T := by
    intro k' hk'
    rcases lt_or_ge k' 0 with h0 | h0
    · rw [N.lev_eq_bot_of_neg k' h0]; exact bot_le
    · obtain ⟨K', rfl⟩ : ∃ K' : ℕ, k' = (K' : ℤ) := ⟨k'.toNat, by omega⟩
      exact IH K' (by exact_mod_cast hk') (by positivity)
  have hsS : ∀ s ∈ Submodule.span ℂ S, levProj N (K : ℤ) s ∈ Submodule.span ℂ S := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨m, hm⟩ := hShom z hz
      by_cases hkm : (K : ℤ) = m
      · rw [hkm, levProj_of_mem N hm]; exact Submodule.subset_span hz
      · rw [levProj_of_mem_ne N hm hkm]; exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  intro x hx
  have hxS : x ∈ Submodule.span ℂ S ⊔ C2M N.toWeakModule := by rw [← htop]; trivial
  obtain ⟨s, hs, c, hc, rfl⟩ := Submodule.mem_sup.mp hxS
  rw [← levProj_of_mem N hx, map_add]
  refine T.add_mem (le_sup_left (a := Submodule.span ℂ S) (hsS s hs)) ?_
  · have hD := levProj_C2M N (K : ℤ) hc
    refine (Submodule.span_le.mpr ?_) hD
    rintro _ ⟨a, p, j, m, ha, hm, hjk, rfl⟩
    exact smul_negTwo_mem N ha hm T le_sup_right (fun k' hk' => hlow k' (by omega))

theorem span_sup_fzO_eq_top {S : Set M} (hShom : ∀ s ∈ S, ∃ k, s ∈ N.lev k)
    (htop : (⊤ : Submodule ℂ M) = Submodule.span ℂ S ⊔ C2M N.toWeakModule) :
    (⊤ : Submodule ℂ M) = Submodule.span ℂ S ⊔ fzO N.toWeakModule := by
  refine le_antisymm (fun x _ => ?_) le_top
  exact induction_lev N (motive := fun x => x ∈ Submodule.span ℂ S ⊔ fzO N.toWeakModule) x
    (Submodule.zero_mem _) (fun _ _ hx hy => Submodule.add_mem _ hx hy)
    (fun k y hy => lev_le_span_sup_fzO hShom htop k hy)

/-- A finite set of homogeneous vectors spanning `M` modulo `C₂(M)`. -/
theorem exists_finset_homog (hC2 : ModuleC2Cofinite N.toWeakModule) :
    ∃ U : Finset M, (∀ s ∈ (U : Set M), ∃ k, s ∈ N.lev k) ∧
      (⊤ : Submodule ℂ M) = Submodule.span ℂ (U : Set M) ⊔ C2M N.toWeakModule := by
  classical
  set K := C2M N.toWeakModule
  haveI : FiniteDimensional ℂ (M ⧸ K) := hC2
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℂ (M ⧸ K)).FG)
  have hH : ∀ y : M, ∃ F : Finset M, (∀ s ∈ (F : Set M), ∃ k, s ∈ N.lev k) ∧
      y ∈ Submodule.span ℂ (F : Set M) := by
    intro y
    have hy : y ∈ Submodule.span ℂ {x : M | ∃ k, x ∈ N.lev k} := by
      refine induction_lev N (motive := fun y => y ∈ Submodule.span ℂ {x : M | ∃ k, x ∈ N.lev k})
        y (Submodule.zero_mem _) (fun _ _ hx hy => Submodule.add_mem _ hx hy)
        (fun k x hx => Submodule.subset_span ⟨k, hx⟩)
    obtain ⟨F, hF, hyF⟩ := Submodule.mem_span_finite_of_mem_span hy
    exact ⟨F, fun s hs => hF hs, hyF⟩
  choose lift hlift using fun q : M ⧸ K => Submodule.Quotient.mk_surjective K q
  choose F hFhom hFmem using hH
  refine ⟨t.biUnion (fun q => F (lift q)), ?_, ?_⟩
  · intro s hs
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hs
    obtain ⟨q, _, hsq⟩ := hs
    exact hFhom _ s hsq
  · refine le_antisymm ?_ le_top
    rw [sup_comm, ← Submodule.comap_map_mkQ K, ← Submodule.comap_top K.mkQ]
    refine Submodule.comap_mono ?_
    rw [← ht, Submodule.span_le]
    intro q hq
    rw [← hlift q, ← Submodule.mkQ_apply]
    refine Submodule.mem_map_of_mem ?_
    refine Submodule.span_mono ?_ (hFmem (lift q))
    intro s hs
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
    exact ⟨q, hq, hs⟩

/-- **`C₂`-cofinite admissible modules have finite-dimensional `M/O(M)`.** -/
theorem finiteDimensional_fzQuot_of_C2 (hC2 : ModuleC2Cofinite N.toWeakModule) :
    FiniteDimensional ℂ (M ⧸ fzO N.toWeakModule) := by
  obtain ⟨U, hU, htop⟩ := exists_finset_homog hC2
  have htop' := span_sup_fzO_eq_top hU htop
  set K := fzO N.toWeakModule
  have hsurj : Function.Surjective (K.mkQ.comp (Submodule.span ℂ (U : Set M)).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K q
    have hx : x ∈ Submodule.span ℂ (U : Set M) ⊔ K := by rw [← htop']; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨y, hy⟩, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    simpa using K.neg_mem hz
  exact Module.Finite.of_surjective _ hsurj

end Admissible

/-! ## Finiteness of fusion rules -/

section Fusion

variable (P₁ P₂ P₃ : LWModule W)

/-- `C₂`-cofinite lowest-weight modules have finite-dimensional `M/O(M)`. -/
theorem finiteDimensional_fzQuot_LW (hC2 : ModuleC2Cofinite P₁.isMod.toWeakModule) :
    FiniteDimensional ℂ (P₁.carrier ⧸ fzO P₁.isMod.toWeakModule) :=
  finiteDimensional_fzQuot_of_C2 (N := lwAdmissible P₁) hC2

variable {P₁ P₂ P₃}

/-- **Fusion rules are finite** for a `C₂`-cofinite lowest-weight `P₁` and irreducible
lowest-weight `P₂, P₃`. -/
theorem finiteDimensional_intertwiningSpace_of_C2 (hC2 : ModuleC2Cofinite P₁.isMod.toWeakModule)
    (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW) :
    FiniteDimensional ℂ (intertwiningSpace P₁.isMod P₂.isMod P₃.isMod) :=
  haveI := finiteDimensional_fzQuot_LW P₁ hC2
  finiteDimensional_intertwiningSpace h₂ h₃

/-- The explicit bound `N^{P₃}_{P₁P₂} ≤ dim(P₁/O(P₁)) · dim P₂(0) · dim P₃(0)` and the
Frenkel–Zhu bound `N ≤ dim fzSpace`, for `C₂`-cofinite `P₁`. -/
theorem fusionRule_le_of_C2 (hC2 : ModuleC2Cofinite P₁.isMod.toWeakModule)
    (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW) :
    fusionRule P₁.isMod P₂.isMod P₃.isMod
        ≤ Module.finrank ℂ (P₁.carrier ⧸ fzO P₁.isMod.toWeakModule)
          * (Module.finrank ℂ (bot P₂) * Module.finrank ℂ (bot P₃)) ∧
      fusionRule P₁.isMod P₂.isMod P₃.isMod ≤ Module.finrank ℂ (fzSpace P₁.isMod P₂ P₃) := by
  haveI := finiteDimensional_fzQuot_LW P₁ hC2
  haveI := finiteDimensional_fzSpace (A₁ := P₁.isMod) (P₂ := P₂) (P₃ := P₃)
  exact ⟨fusionRule_le h₂ h₃, fusionRule_le_finrank_fzSpace h₂ h₃⟩

end Fusion

/-! ## The named input and the nice case -/

/-- **Irreducible modules of a strongly rational VOA are `C₂`-cofinite.**

*Source.* K. Buhl, *A spanning set for VOA modules*, J. Algebra 254 (2002) 125–151 (a weak module
generated by one vector over a `C₂`-cofinite VOA has a spanning set of ordered monomials, whence it
is `C_n`-cofinite for every `n ≥ 2`); T. Abe, G. Buhl, C. Dong, *Rationality, regularity, and
`C₂`-cofiniteness*, Trans. AMS 356 (2004) 3391–3402.  An irreducible module is generated by any
nonzero vector.  The hypothesis `StronglyRational` (which contains `C₂`-cofiniteness and CFT type)
is stronger than what those papers need.

*Not vacuous.* `C2M` is the honest `span{a₍₋₂₎m}`; for the adjoint module it is `O₂(V)`. -/
def ModuleC2Input : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
    StronglyRational W → ∀ P : LWModule W, P.IsIrreducibleLW → ModuleC2Cofinite P.isMod.toWeakModule

/-- **Finite fusion rules for strongly rational `V`**, conditional on `ModuleC2Input` only:
the intertwiner space of type `(P₃ / P₁ P₂)` among irreducible lowest-weight modules is
finite-dimensional, so `fusionRule` is its true dimension. -/
theorem finiteDimensional_intertwiningSpace_stronglyRational (hIn : ModuleC2Input.{u})
    (hV : StronglyRational W) {P₁ P₂ P₃ : LWModule W} (h₁ : P₁.IsIrreducibleLW)
    (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW) :
    FiniteDimensional ℂ (intertwiningSpace P₁.isMod P₂.isMod P₃.isMod) :=
  finiteDimensional_intertwiningSpace_of_C2 (hIn 𝒱 W hV P₁ h₁) h₂ h₃

/-- The same for nice `V` (`Nice = StronglyRational ∧ PseudoUnitary`). -/
theorem finiteDimensional_intertwiningSpace_nice (hIn : ModuleC2Input.{u})
    (hV : Classification.COne.Nice W) {P₁ P₂ P₃ : LWModule W} (h₁ : P₁.IsIrreducibleLW)
    (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW) :
    FiniteDimensional ℂ (intertwiningSpace P₁.isMod P₂.isMod P₃.isMod) :=
  finiteDimensional_intertwiningSpace_stronglyRational hIn hV.1 h₁ h₂ h₃

end VOA.Huang.FusionC2
