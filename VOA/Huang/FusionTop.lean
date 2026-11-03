/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.LatticeFusion
import VOA.Huang.LWBottomRecovery
import VOA.Modules.FZBimodule

/-!
# Intertwining operators are determined by their top components (Frenkel–Zhu)

Let `M₁` be any graded `V`-module and `P₂, P₃` irreducible lowest-weight modules with lowest
weights `h₂, h₃` and bottoms `P₂(0) = (P₂)_{h₂}`, `P₃(0) = (P₃)_{h₃}`.  For an intertwining operator
`𝒴` of type `(P₃ / M₁ P₂)` and `w₁ ∈ (M₁)_α` the mode `𝒴(w₁)₍ₙ₎` shifts weights by `α − n − 1`
(`mem_weight`), so `𝒴(w₁)₍ₜ₍α₎₎`, `t(α) = α + h₂ − h₃ − 1`, maps `P₂(0)` into `P₃(0)`: the
**top component**.  This file proves

* `eq_zero_of_top` — **an intertwining operator whose top components all vanish is zero**
  (Frenkel–Zhu 1992 Thm 1.5.2, the injectivity half; Li 1998).  Proof: a non-top coefficient
  `x = 𝒴(w₁)₍ₙ₎w₂` (`w₂ ∈ P₂(0)`) at level `d > 0` of the irreducible `P₃` is moved by some
  homogeneous lowering mode `a₍q₎` (`exists_lowering_ne_zero`, from the words-on-a-vector
  argument `WS_below_zero`); by the commutator formula `a₍q₎x` is a sum of coefficients
  `𝒴(a₍ᵢ₎w₁)₍·₎w₂` at lower levels (the term `𝒴(w₁) a₍q₎w₂` dies because `a₍q₎` lowers `P₂(0)`),
  so strong induction on `d` kills `x`; then the right annihilator of `𝒴` contains `P₂(0) ≠ 0`
  and irreducibility of `P₂` gives `𝒴 = 0`.
* The three **Frenkel–Zhu top-level identities** for a genuine intertwiner, each a *single*
  instance of the intertwining Jacobi identity plus weight vanishing:
  `top_fzLeft`  (`π(a ∗ w₁) = o(a) π(w₁)`, Jacobi at `(ℓ, m) = (−1, p)`),
  `top_fzRight` (`π(w₁ ∗ a) = π(w₁) o(a)`, `(−1, p − 1)`, `p ≥ 1`),
  `top_fzRes`   (`π(O(M₁)) = 0`, `(−2 − k, p + k)`).
* `topMapQ` — the linear map `𝒴 ↦ π_𝒴 : M₁/O(M₁) → Hom(P₂(0), P₃(0))`, **injective**
  (`topMapQ_injective`).  Consequences:
  `finiteDimensional_intertwiningSpace` (if `M₁/O(M₁)` is finite-dimensional) and the
  bound `fusionRule_le` : `N^{P₃}_{M₁P₂} ≤ dim(M₁/O(M₁)) · dim P₂(0) · dim P₃(0)`.
* `fzSpace` — the space of bilinear maps `T : M₁ × P₂(0) → P₃(0)` vanishing on `O(M₁)`,
  with `T(a ∗ w₁, w₂) = o(a)T(w₁, w₂)` and `T(w₁ ∗ a, w₂) = T(w₁, o(a)w₂)` — i.e. Frenkel–Zhu's
  `Hom_{A(V)}(A(M₁) ⊗_{A(V)} P₂(0), P₃(0))` written without the (unformalized) bimodule structure
  on `M₁/O(M₁)` — and the **Frenkel–Zhu fusion-rule bound** `fusionRule_le_finrank_fzSpace`.

`O(M₁)` is the library's `FZ.fzO` (span of *all* residues `fzRes`, `k ≥ 0`); this only makes the
quotient smaller than Frenkel–Zhu's, so the bounds are (weakly) sharper than theirs.

## Status
No `sorry`, no new axioms.  Unconditional apart from the displayed hypotheses (irreducibility of
`P₂, P₃`; finite-dimensionality of `M₁/O(M₁)` where stated).
-/

set_option linter.style.longLine false

namespace VOA.Huang.FusionTop

open VOA VOA.Huang.BottomRecovery VOA.Huang.LWBottomRecovery VOA.FZ
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## §1  Weights of intertwiner coefficients -/

section Weight

variable {M₁ : Type u} {M₂ : Type u} {M₃ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
variable {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}
  {Y : IntertwiningModes M₁ M₂ M₃}

/-- **The `L₀`-conjugation property**: `𝒴(w₁)₍ₙ₎` maps `(M₂)_β` into `(M₃)_{α+β−n−1}` for
`w₁ ∈ (M₁)_α` (from the `L₀`-commutator, i.e. the commutator formula with `ω` and the
`L₋₁`-derivative property). -/
theorem mem_weight (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) {α β : ℂ} {w₁ : M₁} {w₂ : M₂}
    (h₁ : w₁ ∈ A₁.weight α) (h₂ : w₂ ∈ A₂.weight β) (n : ℂ) :
    Y n w₁ w₂ ∈ A₃.weight (α + β - n - 1) := by
  apply eigenvector_mem_weight A₃
  have h := LatFus.comm_L0 hY w₁ w₂ n
  rw [A₂.L0_weight β w₂ h₂, A₁.L0_weight α w₁ h₁, map_smul, map_smul,
    LinearMap.smul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  module

end Weight

/-! ## §2  Lowering modes in admissible and irreducible lowest-weight modules -/

section Lowering

variable {M : Type u} [AddCommGroup M] [Module ℂ M] (N : AdmissibleModule W M)

/-- **Words on lowering-killed vectors.** If every vector of `X` sits at level `d` and is killed
by every homogeneous mode that strictly lowers the level, then every word on `X` that lands
strictly below level `d` is zero. -/
theorem WS_below_zero {d : ℤ} {X : Set M} (hX : ∀ x ∈ X, x ∈ N.lev d)
    (hlow : ∀ ⦃a : 𝒱⦄ ⦃w p : ℤ⦄, a ∈ W.grading w → w - p - 1 < 0 →
      ∀ x ∈ X, N.toWeakModule.act a p x = 0) :
    ∀ j, ∀ z ∈ WS N.toWeakModule X j, ∀ k, k < d → z ∈ N.lev k → z = 0
  | 0 => fun z hz k hk hzk => eq_zero_of_mem_lev_ne N hzk (hX z hz) (by omega)
  | j + 1 => by
    rintro z ⟨a, w, p, y, ha, hy, rfl⟩ k hk hzk
    have IH := WS_below_zero hX hlow j
    obtain ⟨k', hk'⟩ := WS_homog N (fun x hx => ⟨d, hX x hx⟩) j y hy
    have hz' := act_lev' N (p := p) ha hk'
    by_cases hz0 : N.toWeakModule.act a p y = 0
    · exact hz0
    have hkk : k' + (w - p - 1) = k := by
      by_contra hne
      exact hz0 (eq_zero_of_mem_lev_ne N hz' hzk hne)
    rcases lt_or_ge k' d with hlt | hge
    · rw [IH y hy k' hlt hk', act_zero_right]
    · have hneg : w - p - 1 < 0 := by omega
      have hkill : N.toWeakModule.act a p '' X ⊆ {0} := by
        rintro _ ⟨x, hx, rfl⟩
        exact hlow ha hneg x hx
      have hmem := act_WS_mem N.toWeakModule ha p j X hy
      have hbot : Submodule.span ℂ (WS N.toWeakModule (N.toWeakModule.act a p '' X) j) = ⊥ := by
        rw [Submodule.span_eq_bot]
        intro x hx
        exact WS_subset_zero hkill j hx
      rw [hbot, bot_sup_eq] at hmem
      have key : ∀ z' ∈ Submodule.span ℂ (WS N.toWeakModule X j), levProj N k z' = 0 := by
        intro z' hz'
        induction hz' using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨m, hm⟩ := WS_homog N (fun x hx => ⟨d, hX x hx⟩) j z hz
          by_cases hkm : k = m
          · subst hkm
            rw [levProj_of_mem N hm]
            exact IH z hz k hk hm
          · exact levProj_of_mem_ne N hm hkm
        | zero => exact map_zero _
        | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
        | smul c x _ hx => rw [map_smul, hx, smul_zero]
      have hproj := key _ hmem
      rwa [levProj_of_mem N hzk] at hproj

/-- **Lowering modes detect non-bottom vectors.** In an irreducible lowest-weight module, a
nonzero vector at level `d > 0` is moved (nontrivially) by some homogeneous mode that strictly
lowers the weight. -/
theorem exists_lowering_ne_zero (P : LWModule W) (hirr : P.IsIrreducibleLW) {d : ℕ} (hd : 0 < d)
    {x : P.carrier} (hx : x ∈ P.isMod.weight (P.h + d)) (hx0 : x ≠ 0) :
    ∃ (a : 𝒱) (w p : ℤ), a ∈ W.grading w ∧ w - p - 1 < 0 ∧ mode (P.isMod.YM a) p x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let N := lwAdmissible P
  let S : Submodule ℂ P.carrier := Submodule.span ℂ {x}
  have hxd : x ∈ N.lev (d : ℤ) := by
    change x ∈ lwLev P (d : ℤ)
    rw [lwLev_eq_weight]; push_cast; exact hx
  have hSd : ∀ y ∈ (S : Set P.carrier), y ∈ N.lev (d : ℤ) := by
    intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact Submodule.smul_mem _ c hxd
  have hSlow : ∀ ⦃a : 𝒱⦄ ⦃w p : ℤ⦄, a ∈ W.grading w → w - p - 1 < 0 →
      ∀ y ∈ (S : Set P.carrier), N.toWeakModule.act a p y = 0 := by
    intro a w p ha hneg y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    change mode (P.isMod.YM a) p (c • x) = 0
    rw [map_smul, hcon a w p ha hneg, smul_zero]
  let G : WeakModule.Submodule' P.isMod.toWeakModule :=
    ⟨(genSub (N := N) S).carrier, fun u n _ hy => (genSub (N := N) S).act_mem u n hy⟩
  rcases hirr.2 G with hbot | htop
  · have : x ∈ G.carrier := le_genSub (N := N) S (Submodule.mem_span_singleton_self x)
    rw [hbot, Submodule.mem_bot] at this
    exact hx0 this
  · obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.realized
    have hbG : b ∈ G.carrier := by rw [htop]; trivial
    have hb0' : b ∈ N.lev 0 := by
      change b ∈ lwLev P 0
      rw [lwLev_zero]; exact hb
    have key : ∀ z' ∈ genCarrier (N := N) S, levProj N 0 z' = 0 := by
      intro z' hz'
      induction hz' using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
        obtain ⟨m, hm⟩ := WS_homog N (fun y hy => ⟨d, hSd y hy⟩) j z hj
        by_cases hm0 : (0 : ℤ) = m
        · subst hm0
          rw [levProj_of_mem N hm]
          exact WS_below_zero N hSd hSlow j z hj 0 (by exact_mod_cast hd) hm
        · exact levProj_of_mem_ne N hm hm0
      | zero => exact map_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
    have hproj := key b hbG
    rw [levProj_of_mem N hb0'] at hproj
    exact hb0 hproj

end Lowering

/-! ## §3  Top components determine the intertwiner -/

section Top

variable {M₁ : Type u} [AddCommGroup M₁] [Module ℂ M₁] {A₁ : OrdVModule W M₁}
variable {P₂ P₃ : LWModule W} {Y : IntertwiningModes M₁ P₂.carrier P₃.carrier}

/-- A vector of a lowest-weight module at a weight `h + k`, `k < 0`, is zero. -/
theorem eq_zero_of_below (P : LWModule W) {x : P.carrier} {γ : ℂ} (hx : x ∈ P.isMod.weight γ)
    (k : ℤ) (hk : k < 0) (hγ : γ = P.h + k) : x = 0 := by
  rw [hγ, weight_neg_eq_bot P hk, Submodule.mem_bot] at hx
  exact hx

/-- A weight of a lowest-weight module is `h + n`, `n ∈ ℕ`, unless the vector vanishes. -/
theorem eq_zero_or_level (P : LWModule W) {x : P.carrier} {γ : ℂ} (hx : x ∈ P.isMod.weight γ) :
    x = 0 ∨ ∃ n : ℕ, γ = P.h + n := by
  by_cases hγ : P.isMod.weight γ = ⊥
  · rw [hγ, Submodule.mem_bot] at hx; exact Or.inl hx
  · exact Or.inr (P.isLow γ hγ)

/-- The strong induction on the level: coefficients `𝒴(w₁)₍ₙ₎w₂`, `w₂ ∈ P₂(0)`, at level `d` of
`P₃` vanish when all top components vanish. -/
theorem coeff_eq_zero_of_top (hY : IsIntertwiningOperator A₁ P₂.isMod P₃.isMod Y)
    (h₃ : P₃.IsIrreducibleLW)
    (htop : ∀ (α : ℂ) (w₁ : M₁), w₁ ∈ A₁.weight α → ∀ w₂ ∈ P₂.isMod.weight P₂.h,
      Y (α + P₂.h - P₃.h - 1) w₁ w₂ = 0)
    {w₂ : P₂.carrier} (hw₂ : w₂ ∈ P₂.isMod.weight P₂.h) :
    ∀ (d : ℕ) (α : ℂ) (w₁ : M₁), w₁ ∈ A₁.weight α → ∀ n : ℂ,
      α + P₂.h - n - 1 = P₃.h + d → Y n w₁ w₂ = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro α w₁ hw₁ n hn
  have hx := mem_weight hY hw₁ hw₂ n
  rw [hn] at hx
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : n = α + P₂.h - P₃.h - 1 := by
      have := hn; push_cast at this; linear_combination -this
    rw [this]; exact htop α w₁ hw₁ w₂ hw₂
  by_contra hx0
  obtain ⟨a, w, q, ha, hneg, hne⟩ := exists_lowering_ne_zero P₃ h₃ hd hx hx0
  apply hne
  have hc := hY.commutator a w₁ w₂ q n
  have hlow2 : mode (P₂.isMod.YM a) q w₂ = 0 :=
    mode_lowering_vanish P₂.isMod P₂.isLow ha hw₂ (by omega)
  rw [hlow2, map_zero, sub_zero] at hc
  rw [hc]
  refine LatFus.finsum_eq_zero_of_forall (fun i => ?_)
  rcases lt_or_ge i 0 with hi | hi
  · rw [cbz_apply_neg q hi, zero_smul]
  · have hw₁' := mode_mem_weight A₁ ha hw₁ i
    have hxi := mem_weight hY hw₁' hw₂ ((q : ℂ) + n - i)
    -- the weight is `h₃ + (d + (w − q − 1))`
    have hγ : α + (w : ℂ) - i - 1 + P₂.h - ((q : ℂ) + n - i) - 1
        = P₃.h + (((d : ℤ) + (w - q - 1) : ℤ) : ℂ) := by
      push_cast; linear_combination hn
    rcases lt_or_ge ((d : ℤ) + (w - q - 1)) 0 with he | he
    · rw [eq_zero_of_below P₃ hxi _ he hγ, smul_zero]
    · obtain ⟨e, he'⟩ : ∃ e : ℕ, ((d : ℤ) + (w - q - 1)) = e := ⟨_, (Int.toNat_of_nonneg he).symm⟩
      have hed : e < d := by omega
      rw [IH e hed _ _ hw₁' _ (by rw [hγ, he']; push_cast; ring), smul_zero]

/-- **An intertwining operator is determined by its top components** (Frenkel–Zhu 1992,
Thm 1.5.2, injectivity half).  If `P₂, P₃` are irreducible lowest-weight modules and
`𝒴(w₁)₍α+h₂−h₃−1₎ w₂ = 0` for all homogeneous `w₁ ∈ (M₁)_α` and `w₂ ∈ P₂(0)`, then `𝒴 = 0`. -/
theorem eq_zero_of_top (hY : IsIntertwiningOperator A₁ P₂.isMod P₃.isMod Y)
    (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW)
    (htop : ∀ (α : ℂ) (w₁ : M₁), w₁ ∈ A₁.weight α → ∀ w₂ ∈ P₂.isMod.weight P₂.h,
      Y (α + P₂.h - P₃.h - 1) w₁ w₂ = 0) : Y = 0 := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P₂.realized
  refine LatFus.eq_zero_of_rightKer hY h₂ hb0 (fun w₁ n => ?_)
  have htopw : w₁ ∈ ⨆ α, A₁.weight α := by
    rw [A₁.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun w₁ => Y n w₁ b = 0) htopw ?_ ?_ ?_
  · intro α w₁ hw₁
    rcases eq_zero_or_level P₃ (mem_weight hY hw₁ hb n) with h0 | ⟨d, hd⟩
    · exact h0
    · exact coeff_eq_zero_of_top hY h₃ htop hb d α w₁ hw₁ n hd
  · simp
  · intro x y hx hy
    simp [hx, hy]

end Top

/-! ## §4  The Frenkel–Zhu top-level identities -/

section Identities

variable {M₁ : Type u} [AddCommGroup M₁] [Module ℂ M₁] {A₁ : OrdVModule W M₁}
variable {P₂ P₃ : LWModule W} {Y : IntertwiningModes M₁ P₂.carrier P₃.carrier}

/-- Rewrite a finite sum over `ℤ` supported in `[0, N]` as a sum over `range (N + 1)`. -/
theorem finsum_int_eq_range {X : Type*} [AddCommMonoid X] (f : ℤ → X) (N : ℕ)
    (h : ∀ i : ℤ, i < 0 ∨ (N : ℤ) < i → f i = 0) :
    ∑ᶠ i : ℤ, f i = ∑ i ∈ Finset.range (N + 1), f (i : ℤ) := by
  rw [finsum_eq_sum_of_support_subset f (s := (Finset.range (N + 1)).map Nat.castEmbedding)]
  · rw [Finset.sum_map]; rfl
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Nat.castEmbedding_apply]
    by_contra hcon
    apply hi
    apply h
    by_contra hcon'
    push Not at hcon'
    exact hcon ⟨i.toNat, by omega, by omega⟩

/-- `cbz p i = 0` outside `[0, p]` for `p ≥ 0`. -/
theorem cbz_out {p : ℕ} {i : ℤ} (h : i < 0 ∨ (p : ℤ) < i) : cbz (p : ℤ) i = 0 := by
  rcases h with h | h
  · exact cbz_apply_neg _ h
  · exact cbz_lt (by positivity) h

/-- **Top-level identity, left action** (`π(a ∗ w₁) = o(a)π(w₁)`): the Jacobi identity at
`(ℓ, m, n) = (−1, p, t(α))`. -/
theorem top_fzLeft (hY : IsIntertwiningOperator A₁ P₂.isMod P₃.isMod Y) {p : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (p : ℤ)) {α : ℂ} {w₁ : M₁} (hw₁ : w₁ ∈ A₁.weight α)
    {w₂ : P₂.carrier} (hw₂ : w₂ ∈ P₂.isMod.weight P₂.h) :
    ∑ i ∈ Finset.range (p + 1), cbz (p : ℤ) (i : ℤ) •
        Y (α + p - i + P₂.h - P₃.h - 1) (mode (A₁.YM a) ((i : ℤ) - 1) w₁) w₂
      = mode (P₃.isMod.YM a) ((p : ℤ) - 1) (Y (α + P₂.h - P₃.h - 1) w₁ w₂) := by
  set n : ℂ := α + P₂.h - P₃.h - 1 with hn
  have h := hY.jacobi a w₁ w₂ (-1) p n
  have hR : (∑ᶠ i : ℤ, cbz (p : ℤ) i • Y (((p : ℤ) : ℂ) + n - i) (mode (A₁.YM a) (-1 + i) w₁) w₂)
      = ∑ i ∈ Finset.range (p + 1), cbz (p : ℤ) (i : ℤ) •
          Y (α + p - i + P₂.h - P₃.h - 1) (mode (A₁.YM a) ((i : ℤ) - 1) w₁) w₂ := by
    rw [finsum_int_eq_range _ p (fun i hi => by rw [cbz_out hi, zero_smul])]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (((p : ℤ) : ℂ) + n - (((i : ℕ) : ℤ) : ℂ)) = α + p - i + P₂.h - P₃.h - 1 by
        rw [hn]; push_cast; ring,
      show (-1 : ℤ) + (i : ℤ) = (i : ℤ) - 1 by ring]
  have hL : (∑ᶠ i : ℤ, (negOnePow i * cbz (-1) i) •
        (mode (P₃.isMod.YM a) (-1 + p - i) (Y (n + i) w₁ w₂)
          - negOnePow (-1) • Y (((-1 : ℤ) : ℂ) + n - i) w₁ (mode (P₂.isMod.YM a) (p + i) w₂)))
      = mode (P₃.isMod.YM a) ((p : ℤ) - 1) (Y n w₁ w₂) := by
    rw [finsum_eq_single _ (0 : ℤ)]
    · have hl : mode (P₂.isMod.YM a) ((p : ℤ) + 0) w₂ = 0 :=
        mode_lowering_vanish P₂.isMod P₂.isLow ha hw₂ (by omega)
      rw [hl, map_zero, smul_zero, sub_zero, cbz_zero,
        show (-1 : ℤ) + p - 0 = p - 1 by ring]
      simp [negOnePow]
    · intro i hi
      rcases lt_or_gt_of_ne hi with hi | hi
      · rw [cbz_apply_neg _ hi, mul_zero, zero_smul]
      · have h1 : Y (n + i) w₁ w₂ = 0 :=
          eq_zero_of_below P₃ (mem_weight hY hw₁ hw₂ (n + i)) (-i) (by omega)
            (by rw [hn]; push_cast; ring)
        have h2 : mode (P₂.isMod.YM a) ((p : ℤ) + i) w₂ = 0 :=
          mode_lowering_vanish P₂.isMod P₂.isLow ha hw₂ (by omega)
        rw [h1, h2, map_zero, map_zero, smul_zero, sub_zero, smul_zero]
  rw [hL, hR] at h
  exact h.symm

/-- **Top-level identity, right action** (`π(w₁ ∗ a) = π(w₁) o(a)`): the Jacobi identity at
`(ℓ, m, n) = (−1, p − 1, t(α) + 1)`, for `p ≥ 1`. -/
theorem top_fzRight (hY : IsIntertwiningOperator A₁ P₂.isMod P₃.isMod Y) {p : ℕ} (hp : 1 ≤ p)
    {a : 𝒱} (ha : a ∈ W.grading (p : ℤ)) {α : ℂ} {w₁ : M₁} (hw₁ : w₁ ∈ A₁.weight α)
    {w₂ : P₂.carrier} (hw₂ : w₂ ∈ P₂.isMod.weight P₂.h) :
    ∑ i ∈ Finset.range (p + 1), cbz ((p : ℤ) - 1) (i : ℤ) •
        Y (α + p - i + P₂.h - P₃.h - 1) (mode (A₁.YM a) ((i : ℤ) - 1) w₁) w₂
      = Y (α + P₂.h - P₃.h - 1) w₁ (mode (P₂.isMod.YM a) ((p : ℤ) - 1) w₂) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  set n : ℂ := α + P₂.h - P₃.h with hn
  have hq : ((q + 1 : ℕ) : ℤ) - 1 = (q : ℤ) := by push_cast; ring
  rw [hq]
  have h := hY.jacobi a w₁ w₂ (-1) (q : ℤ) n
  have hR : (∑ᶠ i : ℤ, cbz (q : ℤ) i • Y (((q : ℤ) : ℂ) + n - i) (mode (A₁.YM a) (-1 + i) w₁) w₂)
      = ∑ i ∈ Finset.range (q + 1 + 1), cbz (q : ℤ) (i : ℤ) •
          Y (α + ((q + 1 : ℕ) : ℂ) - i + P₂.h - P₃.h - 1) (mode (A₁.YM a) ((i : ℤ) - 1) w₁) w₂ := by
    rw [finsum_int_eq_range _ (q + 1) (fun i hi => by
      rw [cbz_out (p := q) (by
        rcases hi with hi | hi
        · exact Or.inl hi
        · right; push_cast at hi; omega), zero_smul])]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (((q : ℤ) : ℂ) + n - (((i : ℕ) : ℤ) : ℂ))
        = α + ((q + 1 : ℕ) : ℂ) - i + P₂.h - P₃.h - 1 by rw [hn]; push_cast; ring,
      show (-1 : ℤ) + (i : ℤ) = (i : ℤ) - 1 by ring]
  have hL : (∑ᶠ i : ℤ, (negOnePow i * cbz (-1) i) •
        (mode (P₃.isMod.YM a) (-1 + q - i) (Y (n + i) w₁ w₂)
          - negOnePow (-1) • Y (((-1 : ℤ) : ℂ) + n - i) w₁ (mode (P₂.isMod.YM a) (q + i) w₂)))
      = Y (α + P₂.h - P₃.h - 1) w₁ (mode (P₂.isMod.YM a) (q : ℤ) w₂) := by
    rw [finsum_eq_single _ (0 : ℤ)]
    · have h1 : Y (n + ((0 : ℤ) : ℂ)) w₁ w₂ = 0 :=
        eq_zero_of_below P₃ (mem_weight hY hw₁ hw₂ _) (-1) (by omega)
          (by rw [hn]; push_cast; ring)
      have e1 : ((-1 : ℤ) : ℂ) + n - ((0 : ℤ) : ℂ) = α + P₂.h - P₃.h - 1 := by
        rw [hn]; push_cast; ring
      rw [h1, e1, map_zero, cbz_zero, add_zero]
      simp [negOnePow]
    · intro i hi
      rcases lt_or_gt_of_ne hi with hi | hi
      · rw [cbz_apply_neg _ hi, mul_zero, zero_smul]
      · have h1 : Y (n + i) w₁ w₂ = 0 :=
          eq_zero_of_below P₃ (mem_weight hY hw₁ hw₂ (n + i)) (-1 - i) (by omega)
            (by rw [hn]; push_cast; ring)
        have h2 : mode (P₂.isMod.YM a) ((q : ℤ) + i) w₂ = 0 :=
          mode_lowering_vanish P₂.isMod P₂.isLow ha hw₂ (by push_cast; omega)
        rw [h1, h2, map_zero, map_zero, smul_zero, sub_zero, smul_zero]
  rw [hL, hR] at h
  exact h.symm

/-- **Top-level identity, `O(M₁)`** (`π(O(M₁)) = 0`): the Jacobi identity at
`(ℓ, m, n) = (−2 − k, p + k, t(α) + 1)`; both terms of the left member vanish by weight. -/
theorem top_fzRes (hY : IsIntertwiningOperator A₁ P₂.isMod P₃.isMod Y) {p : ℕ} (k : ℕ) {a : 𝒱}
    (ha : a ∈ W.grading (p : ℤ)) {α : ℂ} {w₁ : M₁} (hw₁ : w₁ ∈ A₁.weight α)
    {w₂ : P₂.carrier} (hw₂ : w₂ ∈ P₂.isMod.weight P₂.h) :
    ∑ i ∈ Finset.range (p + k + 1), cbz ((p : ℤ) + k) (i : ℤ) •
        Y (α + p + k + 1 - i + P₂.h - P₃.h - 1) (mode (A₁.YM a) ((i : ℤ) - 2 - k) w₁) w₂ = 0 := by
  set n : ℂ := α + P₂.h - P₃.h with hn
  have h := hY.jacobi a w₁ w₂ (-2 - k) ((p + k : ℕ) : ℤ) n
  have hR : (∑ᶠ i : ℤ, cbz ((p + k : ℕ) : ℤ) i •
        Y ((((p + k : ℕ) : ℤ) : ℂ) + n - i) (mode (A₁.YM a) ((-2 - k : ℤ) + i) w₁) w₂)
      = ∑ i ∈ Finset.range (p + k + 1), cbz ((p : ℤ) + k) (i : ℤ) •
          Y (α + p + k + 1 - i + P₂.h - P₃.h - 1) (mode (A₁.YM a) ((i : ℤ) - 2 - k) w₁) w₂ := by
    rw [finsum_int_eq_range _ (p + k) (fun i hi => by rw [cbz_out hi, zero_smul])]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (((p + k : ℕ) : ℤ) : ℂ) + n - (((i : ℕ) : ℤ) : ℂ)
        = α + p + k + 1 - i + P₂.h - P₃.h - 1 by rw [hn]; push_cast; ring,
      show (-2 - k : ℤ) + (i : ℤ) = (i : ℤ) - 2 - k by ring,
      show (((p + k : ℕ) : ℤ)) = (p : ℤ) + k by push_cast; ring]
  have hL : (∑ᶠ i : ℤ, (negOnePow i * cbz (-2 - k) i) •
        (mode (P₃.isMod.YM a) ((-2 - k : ℤ) + ((p + k : ℕ) : ℤ) - i) (Y (n + i) w₁ w₂)
          - negOnePow (-2 - k) • Y (((-2 - k : ℤ) : ℂ) + n - i) w₁
              (mode (P₂.isMod.YM a) (((p + k : ℕ) : ℤ) + i) w₂))) = 0 := by
    refine LatFus.finsum_eq_zero_of_forall (fun i => ?_)
    rcases lt_or_ge i 0 with hi | hi
    · rw [cbz_apply_neg _ hi, mul_zero, zero_smul]
    · have h1 : Y (n + i) w₁ w₂ = 0 :=
        eq_zero_of_below P₃ (mem_weight hY hw₁ hw₂ (n + i)) (-1 - i) (by omega)
          (by rw [hn]; push_cast; ring)
      have h2 : mode (P₂.isMod.YM a) (((p + k : ℕ) : ℤ) + i) w₂ = 0 :=
        mode_lowering_vanish P₂.isMod P₂.isLow ha hw₂ (by push_cast; omega)
      rw [h1, h2, map_zero, map_zero, smul_zero, sub_zero, smul_zero]
  rw [hL, hR] at h
  exact h.symm

end Identities

/-! ## §5  The top map, the Frenkel–Zhu space and the fusion-rule bound -/

section TopMap



variable {M₁ : Type u} [AddCommGroup M₁] [Module ℂ M₁] (A₁ : OrdVModule W M₁)
variable (P₂ P₃ : LWModule W)

/-- The bottom `P(0) = P_h` of a lowest-weight module. -/
abbrev bot (P : LWModule W) : Submodule ℂ P.carrier := P.isMod.weight P.h

instance (P : LWModule W) : FiniteDimensional ℂ (bot P) := P.isMod.finrank P.h

/-- Induction over the weight decomposition of a graded module. -/
@[elab_as_elim]
theorem induction_weight {motive : M₁ → Prop} (w : M₁) (h0 : motive 0)
    (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hhom : ∀ α, ∀ x ∈ A₁.weight α, motive x) : motive w := by
  have htop : w ∈ ⨆ α, A₁.weight α := by
    rw [A₁.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := motive) htop hhom h0 hadd

/-- The **top component** of mode data, extended linearly over the weight decomposition of `M₁`:
`w₁ ∈ (M₁)_α ↦ 𝒴(w₁)₍α+h₂−h₃−1₎`. -/
noncomputable def topComp (Y : IntertwiningModes M₁ P₂.carrier P₃.carrier) :
    M₁ →ₗ[ℂ] P₂.carrier →ₗ[ℂ] P₃.carrier :=
  letI := DirectSum.IsInternal.chooseDecomposition A₁.weight A₁.isInternal
  (DFinsupp.lsum ℂ (fun α => (Y (α + P₂.h - P₃.h - 1)).comp (A₁.weight α).subtype)).comp
    (DirectSum.decomposeLinearEquiv A₁.weight).toLinearMap

variable {A₁ P₂ P₃}

theorem topComp_of_mem (Y : IntertwiningModes M₁ P₂.carrier P₃.carrier) {α : ℂ} {w : M₁}
    (hw : w ∈ A₁.weight α) : topComp A₁ P₂ P₃ Y w = Y (α + P₂.h - P₃.h - 1) w := by
  letI := DirectSum.IsInternal.chooseDecomposition A₁.weight A₁.isInternal
  change (DFinsupp.lsum ℂ (fun α => (Y (α + P₂.h - P₃.h - 1)).comp (A₁.weight α).subtype))
    (DirectSum.decompose A₁.weight w) = _
  rw [DirectSum.decompose_of_mem A₁.weight hw]
  exact DFinsupp.lsum_single ℂ (fun α => (Y (α + P₂.h - P₃.h - 1)).comp (A₁.weight α).subtype)
    α ⟨w, hw⟩

theorem topComp_of_mem' (Y : IntertwiningModes M₁ P₂.carrier P₃.carrier) {α q : ℂ} {w : M₁}
    (hw : w ∈ A₁.weight α) (hq : α + P₂.h - P₃.h - 1 = q) : topComp A₁ P₂ P₃ Y w = Y q w := by
  rw [topComp_of_mem Y hw, hq]

theorem topComp_add (Y Y' : IntertwiningModes M₁ P₂.carrier P₃.carrier) :
    topComp A₁ P₂ P₃ (Y + Y') = topComp A₁ P₂ P₃ Y + topComp A₁ P₂ P₃ Y' := by
  refine LinearMap.ext fun w => induction_weight A₁ w (by simp) (fun x y hx hy => ?_) ?_
  · simp only [map_add, hx, hy, LinearMap.add_apply]
  · intro α x hx
    rw [LinearMap.add_apply, topComp_of_mem _ hx, topComp_of_mem _ hx, topComp_of_mem _ hx]
    rfl

theorem topComp_smul (c : ℂ) (Y : IntertwiningModes M₁ P₂.carrier P₃.carrier) :
    topComp A₁ P₂ P₃ (c • Y) = c • topComp A₁ P₂ P₃ Y := by
  refine LinearMap.ext fun w => induction_weight A₁ w (by simp) (fun x y hx hy => ?_) ?_
  · simp only [map_add, hx, hy, LinearMap.smul_apply]
  · intro α x hx
    rw [LinearMap.smul_apply, topComp_of_mem _ hx, topComp_of_mem _ hx]
    rfl

/-- The top component of an intertwiner maps `P₂(0)` into `P₃(0)`. -/
theorem topComp_mem {Y : IntertwiningModes M₁ P₂.carrier P₃.carrier}
    (hY : IsIntertwiningOperator A₁ P₂.isMod P₃.isMod Y) (w₁ : M₁) {w₂ : P₂.carrier}
    (hw₂ : w₂ ∈ bot P₂) : topComp A₁ P₂ P₃ Y w₁ w₂ ∈ bot P₃ := by
  refine induction_weight A₁ w₁ (by simp) (fun x y hx hy => ?_) ?_
  · rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
  · intro α x hx
    rw [topComp_of_mem _ hx]
    have := mem_weight hY hx hw₂ (α + P₂.h - P₃.h - 1)
    rwa [show α + P₂.h - (α + P₂.h - P₃.h - 1) - 1 = P₃.h by ring] at this

/-- The bilinear **top map** `π_𝒴 : M₁ × P₂(0) → P₃(0)` of an intertwiner. -/
noncomputable def topBilin {Y : IntertwiningModes M₁ P₂.carrier P₃.carrier}
    (hY : IsIntertwiningOperator A₁ P₂.isMod P₃.isMod Y) : M₁ →ₗ[ℂ] bot P₂ →ₗ[ℂ] bot P₃ :=
  LinearMap.mk₂ ℂ (fun w₁ w₂ => ⟨topComp A₁ P₂ P₃ Y w₁ w₂, topComp_mem hY w₁ w₂.2⟩)
    (fun x y w₂ => Subtype.ext (by simp))
    (fun c x w₂ => Subtype.ext (by simp))
    (fun w₁ x y => Subtype.ext (by simp))
    (fun c w₁ x => Subtype.ext (by simp))

@[simp] theorem topBilin_apply {Y : IntertwiningModes M₁ P₂.carrier P₃.carrier}
    (hY : IsIntertwiningOperator A₁ P₂.isMod P₃.isMod Y) (w₁ : M₁) (w₂ : bot P₂) :
    (topBilin hY w₁ w₂ : P₃.carrier) = topComp A₁ P₂ P₃ Y w₁ w₂ := rfl

variable (A₁ P₂ P₃)

/-- The **top map** `𝒴 ↦ π_𝒴`, linear on the space of intertwining operators. -/
noncomputable def topMap :
    intertwiningSpace A₁ P₂.isMod P₃.isMod →ₗ[ℂ] (M₁ →ₗ[ℂ] bot P₂ →ₗ[ℂ] bot P₃) where
  toFun Y := topBilin Y.2
  map_add' Y Y' := by
    ext w₁ w₂
    simp [topComp_add]
  map_smul' c Y := by
    ext w₁ w₂
    simp [topComp_smul]

variable {A₁ P₂ P₃}

theorem topMap_apply (Y : intertwiningSpace A₁ P₂.isMod P₃.isMod) (w₁ : M₁) (w₂ : bot P₂) :
    (topMap A₁ P₂ P₃ Y w₁ w₂ : P₃.carrier) = topComp A₁ P₂ P₃ (Y : IntertwiningModes _ _ _) w₁ w₂ :=
  rfl

/-- **The top map is injective** on intertwining operators among `M₁` and irreducible
lowest-weight `P₂, P₃` (Frenkel–Zhu Thm 1.5.2, injectivity). -/
theorem topMap_injective (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW) :
    Function.Injective (topMap A₁ P₂ P₃) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY0
  apply Subtype.ext
  refine eq_zero_of_top Y.2 h₂ h₃ (fun α w₁ hw₁ w₂ hw₂ => ?_)
  have := congrArg (fun T => ((T w₁ ⟨w₂, hw₂⟩ : bot P₃) : P₃.carrier)) hY0
  simp only [topMap_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero] at this
  rwa [topComp_of_mem _ hw₁] at this

/-! ### The Frenkel–Zhu identities for the top map -/

theorem fzRes_add (N : WeakModule W M₁) (p k : ℕ) (a : 𝒱) (m m' : M₁) :
    fzRes N p k a (m + m') = fzRes N p k a m + fzRes N p k a m' := by
  simp only [fzRes, map_add, smul_add, Finset.sum_add_distrib]

theorem fzRes_zero (N : WeakModule W M₁) (p k : ℕ) (a : 𝒱) : fzRes N p k a 0 = 0 := by
  simp [fzRes]

theorem fzLeft_zero (N : WeakModule W M₁) (p : ℕ) (a : 𝒱) : fzLeft N p a 0 = 0 := by
  simp [fzLeft]

theorem fzRight_zero (N : WeakModule W M₁) (p : ℕ) (a : 𝒱) : fzRight N p a 0 = 0 := by
  simp [fzRight]

/-- `π_𝒴(fzRes) = 0` on all of `M₁`. -/
theorem topComp_fzRes {Y : IntertwiningModes M₁ P₂.carrier P₃.carrier}
    (hY : IsIntertwiningOperator A₁ P₂.isMod P₃.isMod Y) {p : ℕ} (k : ℕ) {a : 𝒱}
    (ha : a ∈ W.grading (p : ℤ)) (w₁ : M₁) {w₂ : P₂.carrier} (hw₂ : w₂ ∈ bot P₂) :
    topComp A₁ P₂ P₃ Y (fzRes A₁.toWeakModule p k a w₁) w₂ = 0 := by
  refine induction_weight A₁ w₁ (by simp [fzRes_zero]) (fun x y hx hy => ?_) ?_
  · rw [fzRes_add, map_add, LinearMap.add_apply, hx, hy, add_zero]
  · intro α x hx
    rw [← top_fzRes hY k ha hx hw₂, fzRes, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, LinearMap.smul_apply,
      topComp_of_mem' Y (q := α + p + k + 1 - i + P₂.h - P₃.h - 1)
        (mode_mem_weight A₁ ha hx _) (by push_cast; ring)]

/-- `π_𝒴(a ∗ w₁) = o(a) π_𝒴(w₁)` on all of `M₁`. -/
theorem topComp_fzLeft {Y : IntertwiningModes M₁ P₂.carrier P₃.carrier}
    (hY : IsIntertwiningOperator A₁ P₂.isMod P₃.isMod Y) {p : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (p : ℤ)) (w₁ : M₁) {w₂ : P₂.carrier} (hw₂ : w₂ ∈ bot P₂) :
    topComp A₁ P₂ P₃ Y (fzLeft A₁.toWeakModule p a w₁) w₂
      = mode (P₃.isMod.YM a) ((p : ℤ) - 1) (topComp A₁ P₂ P₃ Y w₁ w₂) := by
  refine induction_weight A₁ w₁ (by simp [fzLeft_zero]) (fun x y hx hy => ?_) ?_
  · rw [fzLeft_add, map_add, LinearMap.add_apply, hx, hy, map_add, LinearMap.add_apply, map_add]
  · intro α x hx
    rw [topComp_of_mem _ hx, ← top_fzLeft hY ha hx hw₂, fzLeft, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, LinearMap.smul_apply,
      topComp_of_mem' Y (q := α + p - i + P₂.h - P₃.h - 1)
        (mode_mem_weight A₁ ha hx _) (by push_cast; ring)]

/-- `π_𝒴(w₁ ∗ a) = π_𝒴(w₁) o(a)` on all of `M₁` (`p ≥ 1`). -/
theorem topComp_fzRight {Y : IntertwiningModes M₁ P₂.carrier P₃.carrier}
    (hY : IsIntertwiningOperator A₁ P₂.isMod P₃.isMod Y) {p : ℕ} (hp : 1 ≤ p) {a : 𝒱}
    (ha : a ∈ W.grading (p : ℤ)) (w₁ : M₁) {w₂ : P₂.carrier} (hw₂ : w₂ ∈ bot P₂) :
    topComp A₁ P₂ P₃ Y (fzRight A₁.toWeakModule p a w₁) w₂
      = topComp A₁ P₂ P₃ Y w₁ (mode (P₂.isMod.YM a) ((p : ℤ) - 1) w₂) := by
  refine induction_weight A₁ w₁ (by simp [fzRight_zero]) (fun x y hx hy => ?_) ?_
  · rw [fzRight_add, map_add, LinearMap.add_apply, hx, hy, map_add, LinearMap.add_apply]
  · intro α x hx
    rw [topComp_of_mem _ hx, ← top_fzRight hY hp ha hx hw₂, fzRight, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, LinearMap.smul_apply,
      topComp_of_mem' Y (q := α + p - i + P₂.h - P₃.h - 1)
        (mode_mem_weight A₁ ha hx _) (by push_cast; ring)]

/-! ### The Frenkel–Zhu space -/

variable (A₁ P₂ P₃)

/-- **The Frenkel–Zhu space**: bilinear maps `T : M₁ × P₂(0) → P₃(0)` that vanish on
`O(M₁)`, are left `A(V)`-linear (`T(a ∗ w₁, w₂) = o(a) T(w₁, w₂)`) and balanced
(`T(w₁ ∗ a, w₂) = T(w₁, o(a) w₂)`, `wt a ≥ 1`).  This is
`Hom_{A(V)}(A(M₁) ⊗_{A(V)} P₂(0), P₃(0))` of Frenkel–Zhu, written on `M₁` itself. -/
def fzSpace : Submodule ℂ (M₁ →ₗ[ℂ] bot P₂ →ₗ[ℂ] bot P₃) where
  carrier := {T |
    (∀ x ∈ fzO A₁.toWeakModule, T x = 0) ∧
    (∀ (p : ℕ) (a : 𝒱), a ∈ W.grading (p : ℤ) → ∀ (w₁ : M₁) (w₂ : bot P₂),
      (T (fzLeft A₁.toWeakModule p a w₁) w₂ : P₃.carrier)
        = mode (P₃.isMod.YM a) ((p : ℤ) - 1) (T w₁ w₂)) ∧
    (∀ (p : ℕ), 1 ≤ p → ∀ (a : 𝒱), a ∈ W.grading (p : ℤ) → ∀ (w₁ : M₁) (w₂ w₂' : bot P₂),
      (w₂' : P₂.carrier) = mode (P₂.isMod.YM a) ((p : ℤ) - 1) w₂ →
        T (fzRight A₁.toWeakModule p a w₁) w₂ = T w₁ w₂')}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ _ => rfl⟩
  add_mem' := by
    rintro T T' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨fun x hx => by simp [h1 x hx, h1' x hx], fun p a ha w₁ w₂ => ?_,
      fun p hp a ha w₁ w₂ w₂' he => by simp [h3 p hp a ha w₁ w₂ w₂' he, h3' p hp a ha w₁ w₂ w₂' he]⟩
    simp only [LinearMap.add_apply, Submodule.coe_add, h2 p a ha, h2' p a ha, map_add]
  smul_mem' := by
    rintro c T ⟨h1, h2, h3⟩
    refine ⟨fun x hx => by simp [h1 x hx], fun p a ha w₁ w₂ => ?_,
      fun p hp a ha w₁ w₂ w₂' he => by simp [h3 p hp a ha w₁ w₂ w₂' he]⟩
    simp only [LinearMap.smul_apply, Submodule.coe_smul, h2 p a ha, map_smul]

variable {A₁ P₂ P₃}

/-- The top map of every intertwiner lies in the Frenkel–Zhu space. -/
theorem topMap_mem_fzSpace (Y : intertwiningSpace A₁ P₂.isMod P₃.isMod) :
    topMap A₁ P₂ P₃ Y ∈ fzSpace A₁ P₂ P₃ := by
  have hY : IsIntertwiningOperator A₁ P₂.isMod P₃.isMod (Y : IntertwiningModes _ _ _) := Y.2
  refine ⟨fun x hx => ?_, fun p a ha w₁ w₂ => ?_, fun p hp a ha w₁ w₂ w₂' he => ?_⟩
  · induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, k, a, ha, m, rfl⟩ := hz
      ext w₂
      simp only [topMap_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero]
      exact topComp_fzRes hY k ha m w₂.2
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  · simp only [topMap_apply]
    exact topComp_fzLeft hY ha w₁ w₂.2
  · apply Subtype.ext
    simp only [topMap_apply, he]
    exact topComp_fzRight hY hp ha w₁ w₂.2

variable (A₁ P₂ P₃)

/-- The top map, corestricted to the Frenkel–Zhu space. -/
noncomputable def topMapFZ : intertwiningSpace A₁ P₂.isMod P₃.isMod →ₗ[ℂ] fzSpace A₁ P₂ P₃ :=
  (topMap A₁ P₂ P₃).codRestrict (fzSpace A₁ P₂ P₃) topMap_mem_fzSpace

/-- The Frenkel–Zhu space embeds in `Hom(M₁/O(M₁), Hom(P₂(0), P₃(0)))`. -/
noncomputable def fzSpaceToQuot :
    fzSpace A₁ P₂ P₃ →ₗ[ℂ] ((M₁ ⧸ fzO A₁.toWeakModule) →ₗ[ℂ] bot P₂ →ₗ[ℂ] bot P₃) where
  toFun T := (fzO A₁.toWeakModule).liftQ T.1 (fun x hx => T.2.1 x hx)
  map_add' T T' := by
    apply Submodule.linearMap_qext
    ext; simp
  map_smul' c T := by
    apply Submodule.linearMap_qext
    ext; simp

variable {A₁ P₂ P₃}

theorem topMapFZ_injective (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW) :
    Function.Injective (topMapFZ A₁ P₂ P₃) := fun _ _ h =>
  topMap_injective h₂ h₃ (congrArg Subtype.val h)

theorem fzSpaceToQuot_injective : Function.Injective (fzSpaceToQuot A₁ P₂ P₃) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro T hT
  apply Subtype.ext
  ext w₁ w₂
  have := congrArg (fun f => ((f (Submodule.Quotient.mk w₁) w₂ : bot P₃) : P₃.carrier)) hT
  simpa [fzSpaceToQuot] using this

/-- `fzSpace` is finite-dimensional when `M₁/O(M₁)` is. -/
theorem finiteDimensional_fzSpace [FiniteDimensional ℂ (M₁ ⧸ fzO A₁.toWeakModule)] :
    FiniteDimensional ℂ (fzSpace A₁ P₂ P₃) :=
  Module.Finite.of_injective (fzSpaceToQuot A₁ P₂ P₃) fzSpaceToQuot_injective

/-- **The Frenkel–Zhu fusion-rule bound**: `N^{P₃}_{M₁ P₂} ≤ dim fzSpace`
(`= dim Hom_{A(V)}(A(M₁) ⊗_{A(V)} P₂(0), P₃(0))`), for irreducible lowest-weight `P₂, P₃`, and the
intertwiner space is finite-dimensional. -/
theorem finiteDimensional_intertwiningSpace_of_fzSpace (h₂ : P₂.IsIrreducibleLW)
    (h₃ : P₃.IsIrreducibleLW) [FiniteDimensional ℂ (fzSpace A₁ P₂ P₃)] :
    FiniteDimensional ℂ (intertwiningSpace A₁ P₂.isMod P₃.isMod) :=
  Module.Finite.of_injective (topMapFZ A₁ P₂ P₃) (topMapFZ_injective h₂ h₃)

theorem fusionRule_le_finrank_fzSpace (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW)
    [FiniteDimensional ℂ (fzSpace A₁ P₂ P₃)] :
    fusionRule A₁ P₂.isMod P₃.isMod ≤ Module.finrank ℂ (fzSpace A₁ P₂ P₃) :=
  LinearMap.finrank_le_finrank_of_injective (topMapFZ_injective h₂ h₃)

/-- **Finiteness of fusion rules from `A(M₁)`**: if `M₁/O(M₁)` is finite-dimensional and
`P₂, P₃` are irreducible lowest-weight modules, the space of intertwining operators of type
`(P₃ / M₁ P₂)` is finite-dimensional. -/
theorem finiteDimensional_intertwiningSpace (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW)
    [FiniteDimensional ℂ (M₁ ⧸ fzO A₁.toWeakModule)] :
    FiniteDimensional ℂ (intertwiningSpace A₁ P₂.isMod P₃.isMod) :=
  haveI := finiteDimensional_fzSpace (A₁ := A₁) (P₂ := P₂) (P₃ := P₃)
  finiteDimensional_intertwiningSpace_of_fzSpace h₂ h₃

/-- **The explicit fusion-rule bound**
`N^{P₃}_{M₁ P₂} ≤ dim(M₁/O(M₁)) · dim P₂(0) · dim P₃(0)`. -/
theorem fusionRule_le (h₂ : P₂.IsIrreducibleLW) (h₃ : P₃.IsIrreducibleLW)
    [FiniteDimensional ℂ (M₁ ⧸ fzO A₁.toWeakModule)] :
    fusionRule A₁ P₂.isMod P₃.isMod
      ≤ Module.finrank ℂ (M₁ ⧸ fzO A₁.toWeakModule)
        * (Module.finrank ℂ (bot P₂) * Module.finrank ℂ (bot P₃)) := by
  haveI := finiteDimensional_fzSpace (A₁ := A₁) (P₂ := P₂) (P₃ := P₃)
  calc fusionRule A₁ P₂.isMod P₃.isMod ≤ Module.finrank ℂ (fzSpace A₁ P₂ P₃) :=
        fusionRule_le_finrank_fzSpace h₂ h₃
    _ ≤ Module.finrank ℂ ((M₁ ⧸ fzO A₁.toWeakModule) →ₗ[ℂ] bot P₂ →ₗ[ℂ] bot P₃) :=
        LinearMap.finrank_le_finrank_of_injective fzSpaceToQuot_injective
    _ = _ := by rw [Module.finrank_linearMap, Module.finrank_linearMap]

end TopMap

end VOA.Huang.FusionTop
