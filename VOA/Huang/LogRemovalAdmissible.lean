/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.LogRemovalSemisimple

/-!
# Log removal from complete reducibility (abstract part)

The natural route to log removal asks for: `Λ` (the span of the coefficient functionals) is
admissible,
completely reducible by rationality, its irreducible summands are ordinary (DLM 8.1(c) or `A(V)`),
hence `L'(0)` is semisimple on `Λ`.  This file shows that **the middle steps are unnecessary**:
complete reducibility of a weak module *alone* already forbids a Jordan block of `L(0)` of size
two, with no irreducible decomposition, no `A(V)`, no Schur/Dixmier lemma and no finiteness.

**The key lemma** (`sub_L0_eq_zero_of_sq`).  In any weak module `A`, the sum `E` of all
`L(0)`-eigenspaces is a weak submodule (`eigenSubmodule`: a mode of a homogeneous `v` maps the
`c`-eigenspace into the `c + wt v − m − 1`-eigenspace, `L0_commutator_weak`).  If `E` has a
complement `C` which is a weak submodule, then `(L(0) − n)² x = 0 ⟹ (L(0) − n) x = 0`:
write `x = a + c`; `y := (L(0)−n)x` is an eigenvector, so `(L(0)−n)c = y − (L(0)−n)a ∈ E ∩ C = 0`,
so `c` is an eigenvector, `c ∈ E ∩ C = 0`, `x ∈ E`; on `E` the operator `L(0) − n` maps into the sum
of the eigenspaces `≠ n`, which meets the `n`-eigenspace trivially.

**Application.**  The coefficient functions satisfy `(L'(0) − n) B_{n,k} = (k+1) B_{n,k+1}`
(`L0T_coefFun`).  Given (a) a log-degree bound for each fixed outside datum (`CoeffLogBounded`)
and (b) an admissible module structure on some space of functions containing `B_{n,0}` whose
`L(0)` is `L'(0)` (`CoeffAdmissibleInput`), rationality (`AdmissiblyRational`, part of
`StronglyRational`) and the key lemma kill the top log coefficient, and downward induction kills
all of them: `coeffL0Semisimple_of_admissible`.

Both inputs are TRUE named `Prop`s (consequences of Huang's associativity theorem — see their
docstrings), and `CoeffLogBounded` also follows from the target `CoeffL0Semisimple`
(`coeffLogBounded_of_coeffL0Semisimple`).

## Main results
* `L0_commutator_weak`, `mode_mem_eigenspace` — `[L(0), v_m] = (wt v − m − 1) v_m` on weak modules.
* `eigenSubmodule` — the sum of the `L(0)`-eigenspaces is a weak submodule.
* `sub_L0_eq_zero_of_sq` — complete reducibility forbids `2×2` Jordan blocks of `L(0)`.
* `CoeffLogBounded`, `CoeffAdmissibleInput` (named, TRUE).
* `coeffL0Semisimple_of_admissible`, `associativityInput_of_admissible`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.LogRemovalAdmissible

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff VOA.Huang.AssocCoeffReduction
open VOA.Huang.AssocCoeffRules VOA.Huang.LogRemovalSemisimple
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## `L(0)` on weak modules -/

section Weak

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The operator `L(0) = ω₍₁₎` of a weak module. -/
abbrev L0 (A : WeakModule W M) : End ℂ M := mode (A.YM W.conformalVector) 1

/-- For homogeneous `v ∈ 𝒱ᵦ`, `[L₀, v₍ₙ₎] x = (β − n − 1)·v₍ₙ₎ x`, on any weak module. -/
theorem L0_commutator_weak (A : WeakModule W M) {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β)
    (x : M) (n : ℤ) :
    L0 A (mode (A.YM v) n x)
      = ((β : ℂ) - n - 1) • mode (A.YM v) n x + mode (A.YM v) n (L0 A x) := by
  have hraw := L0_commutator_raw A v x n
  have h0 : W.smul W.conformalVector 0 v = W.L (-1) v := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def,
      show ((-1 : ℤ) + 1) = 0 from by ring]
  have h1 : W.smul W.conformalVector 1 v = W.L 0 v := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def,
      show ((0 : ℤ) + 1) = 1 from by ring]
  rw [h0, h1, W.L_zero_grading v hv] at hraw
  have hcov := act_T_covariance A v (1 + n) x
  simp only [WeakModule.act_def, show (1 + n - 1 : ℤ) = n from by ring] at hcov
  have hlin : mode (A.YM ((β : ℂ) • v)) n x = (β : ℂ) • mode (A.YM v) n x := by
    rw [map_smul, mode_smul]; rfl
  rw [hcov, hlin] at hraw
  rw [sub_eq_iff_eq_add] at hraw
  change mode (A.YM W.conformalVector) 1 (mode (A.YM v) n x) = _
  rw [hraw]
  have hscal : (-((1 + n : ℤ) : ℂ)) • mode (A.YM v) n x + (β : ℂ) • mode (A.YM v) n x
      = ((β : ℂ) - n - 1) • mode (A.YM v) n x := by
    rw [← add_smul]; congr 1; push_cast; ring
  rw [hscal]

/-- A homogeneous mode maps the `c`-eigenspace of `L(0)` into the `c + β − n − 1`-eigenspace. -/
theorem mode_mem_eigenspace (A : WeakModule W M) {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β)
    {c : ℂ} {x : M} (hx : x ∈ (L0 A).eigenspace c) (n : ℤ) :
    mode (A.YM v) n x ∈ (L0 A).eigenspace (c + β - n - 1) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [L0_commutator_weak A hv, hx, map_smul, ← add_smul]
  congr 1
  ring

/-- The sum of all `L(0)`-eigenspaces. -/
noncomputable def eigenSum (A : WeakModule W M) : Submodule ℂ M :=
  ⨆ c : ℂ, (L0 A).eigenspace c

theorem eigenspace_le_eigenSum (A : WeakModule W M) (c : ℂ) :
    (L0 A).eigenspace c ≤ eigenSum A :=
  le_iSup (fun c => (L0 A).eigenspace c) c

/-- Every mode preserves `eigenSum` (decompose `v` into homogeneous components). -/
theorem mode_mem_eigenSum (A : WeakModule W M) (v : 𝒱) (n : ℤ) {x : M}
    (hx : x ∈ eigenSum A) : mode (A.YM v) n x ∈ eigenSum A := by
  have hv : v ∈ ⨆ β : ℤ, W.grading β := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  induction hv using Submodule.iSup_induction' with
  | mem β v hv =>
    induction hx using Submodule.iSup_induction' with
    | mem c x hx =>
      exact eigenspace_le_eigenSum A _ (mode_mem_eigenspace A hv hx n)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | zero => simp only [map_zero, mode_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add v₁ v₂ _ _ h₁ h₂ =>
    simp only [map_add, mode_add, LinearMap.add_apply]
    exact Submodule.add_mem _ h₁ h₂

/-- **The eigen-submodule**: the sum of the `L(0)`-eigenspaces, as a weak submodule. -/
noncomputable def eigenSubmodule (A : WeakModule W M) : WeakModule.Submodule' A where
  carrier := eigenSum A
  act_mem u n _ hx := mode_mem_eigenSum A u n hx

/-- On `eigenSum`, `L(0) − n` lands in the sum of the eigenspaces with eigenvalue `≠ n`. -/
theorem sub_L0_mem_iSup_ne (A : WeakModule W M) (n : ℂ) {x : M} (hx : x ∈ eigenSum A) :
    (L0 A - n • 1) x ∈ ⨆ (c : ℂ) (_ : c ≠ n), (L0 A).eigenspace c := by
  induction hx using Submodule.iSup_induction' with
  | mem c x hx =>
    have hx' := hx
    rw [Module.End.mem_eigenspace_iff] at hx'
    have e : (L0 A - n • 1) x = (c - n) • x := by
      rw [LinearMap.sub_apply, hx', LinearMap.smul_apply, Module.End.one_apply, sub_smul]
    rw [e]
    by_cases hc : c = n
    · rw [hc, sub_self, zero_smul]; exact Submodule.zero_mem _
    · refine (le_iSup₂_of_le c hc le_rfl : (L0 A).eigenspace c ≤ _) ?_
      exact Submodule.smul_mem _ _ hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- **Complete reducibility forbids Jordan blocks of size two.**  If the eigen-submodule of a
weak module has a complement which is a weak submodule (e.g. if every weak submodule is
complemented), then `(L(0) − n)² x = 0` implies `(L(0) − n) x = 0`. -/
theorem sub_L0_eq_zero_of_sq (A : WeakModule W M)
    (hcompl : ∃ C : WeakModule.Submodule' A, IsCompl (eigenSubmodule A).carrier C.carrier)
    (n : ℂ) {x : M} (h2 : (L0 A - n • 1) ((L0 A - n • 1) x) = 0) :
    (L0 A - n • 1) x = 0 := by
  obtain ⟨C, hC⟩ := hcompl
  set g : End ℂ M := L0 A - n • 1 with hg
  have hgC : ∀ c ∈ C.carrier, g c ∈ C.carrier := by
    intro c hc
    rw [hg, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.sub_mem _ (C.act_mem W.conformalVector 1 hc) (Submodule.smul_mem _ _ hc)
  have hgE : ∀ a ∈ eigenSum A, g a ∈ eigenSum A := by
    intro a ha
    rw [hg, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.sub_mem _ (mode_mem_eigenSum A _ 1 ha) (Submodule.smul_mem _ _ ha)
  have hyeig : g x ∈ (L0 A).eigenspace n := by
    rw [Module.End.mem_eigenspace_iff]
    have : (L0 A - n • 1) (g x) = 0 := h2
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
    exact this
  have hyE : g x ∈ eigenSum A := eigenspace_le_eigenSum A n hyeig
  -- decompose `x = a + c`
  have hx : x ∈ (eigenSubmodule A).carrier ⊔ C.carrier := by rw [hC.sup_eq_top]; trivial
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  have ha' : a ∈ eigenSum A := ha
  have hgc : g c = 0 := by
    have h1 : g c ∈ C.carrier := hgC c hc
    have h2' : g c ∈ eigenSum A := by
      have : g c = g (a + c) - g a := by rw [map_add]; abel
      rw [this]; exact Submodule.sub_mem _ hyE (hgE a ha')
    have := hC.disjoint
    rw [Submodule.disjoint_def] at this
    exact this _ h2' h1
  have hc0 : c = 0 := by
    have hce : c ∈ (L0 A).eigenspace n := by
      rw [Module.End.mem_eigenspace_iff]
      rw [hg, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
        at hgc
      exact hgc
    have := hC.disjoint
    rw [Submodule.disjoint_def] at this
    exact this _ (eigenspace_le_eigenSum A n hce) hc
  subst hc0
  rw [add_zero] at hyeig ⊢
  have hne := sub_L0_mem_iSup_ne A n ha'
  have hdis := (Module.End.eigenspaces_iSupIndep (L0 A)) n
  rw [Submodule.disjoint_def] at hdis
  exact hdis _ hyeig hne

end Weak

/-! ## The two named inputs and log removal -/

/-- **Bounded log-degree for each fixed outside datum** (named; TRUE for strongly rational `W`:
the products are log-free — Huang 2005 Thm 3.5 — so `K = 0` works; see also
`coeffLogBounded_of_coeffL0Semisimple`).  For fixed `(f, w₃)` and intermediate weight `n`, the
coefficient functions `B_{n,k}` vanish identically (in the inside data) for `k ≫ 0`.  Contrast
`coefFun_eventually_zero`, which is only pointwise. -/
def CoeffLogBounded (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∀ (α₃ h₄ : ℂ) (w₃ : P₃.carrier) (f : P₄.carrier →ₗ[ℂ] ℂ),
    w₃ ∈ P₃.isMod.weight α₃ → SupportedAt P₄.isMod f h₄ →
  ∀ n : ℂ, ∃ K : ℕ, ∀ k, K < k → coefFun Y₁ Y₂ f w₃ α₃ h₄ n k = 0

/-- **An admissible module of functions through `B_{n,0}` with `L(0) = L'(0)`** (named; TRUE for
strongly rational `W`).  For each product, outside datum `(f, w₃)` and intermediate weight `n`,
there is a subspace `M` of the functions on homogeneous pairs, containing `B_{n,0}`, carrying an
admissible `V`-module structure whose `L(0) = ω₍₁₎` is the transpose operator `L'(0)` (`L0T`).

Why TRUE: by associativity (Huang 2005 Thm 3.5 / HL IV), `B_{n,0} = Σⱼ ⟨μⱼ, 𝒴₄ʲ(·)·⟩` for
`μⱼ ∈ (Qⱼ)'_n` (`coeffL0Semisimple_of_assocCoeffIdentity`); the map
`⊕ⱼ (Qⱼ)' → (functions)`, `μ ↦ (w₁, w₂) ↦ Σ_c μ_c((w₁)_{α₁+α₂−1−c} w₂)`, intertwines the
contragredient action with the Huang–Lepowsky `P(1)`-action `τ` on functions (the transpose of
the coproduct of the opposite modes), so its image (over the `j` with `h_{Qⱼ} ∈ n + ℤ`) is a
`τ`-stable space, `ℕ`-graded by `c − min h_{Qⱼ}`, on which `L(0)` is `L0T` (`L0T_iterFunAt`).
Constructively this is the output of the `P(1)`-construction (`PzTensor*`) and the lower bound on
intermediate weights. -/
def CoeffAdmissibleInput (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∀ (α₃ h₄ : ℂ) (w₃ : P₃.carrier) (f : P₄.carrier →ₗ[ℂ] ℂ),
    w₃ ∈ P₃.isMod.weight α₃ → SupportedAt P₄.isMod f h₄ →
  ∀ n : ℂ, ∃ (M : Submodule ℂ (HomPair P₁ P₂ → ℂ)) (A : AdmissibleModule W M),
    (∀ G : M, ((L0 A.toWeakModule G : M) : HomPair P₁ P₂ → ℂ) = L0T P₁ P₂ (G : HomPair P₁ P₂ → ℂ))
    ∧ coefFun Y₁ Y₂ f w₃ α₃ h₄ n 0 ∈ M

section Main

variable (hV : StronglyRational W)
  {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
  {α₃ h₄ : ℂ} {w₃ : P₃.carrier} {f : P₄.carrier →ₗ[ℂ] ℂ}
  (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf

/-- **All log coefficients vanish**, given a uniform log bound and an admissible module of
functions through `B_{n,0}` with `L(0) = L'(0)`. -/
theorem coefFun_log_eq_zero (n : ℂ) {K : ℕ}
    (hK : ∀ k, K < k → coefFun Y₁ Y₂ f w₃ α₃ h₄ n k = 0)
    (M : Submodule ℂ (HomPair P₁ P₂ → ℂ)) (A : AdmissibleModule W M)
    (hL : ∀ G : M,
      ((L0 A.toWeakModule G : M) : HomPair P₁ P₂ → ℂ) = L0T P₁ P₂ (G : HomPair P₁ P₂ → ℂ))
    (hB : coefFun Y₁ Y₂ f w₃ α₃ h₄ n 0 ∈ M) :
    ∀ k, 1 ≤ k → coefFun Y₁ Y₂ f w₃ α₃ h₄ n k = 0 := by
  set B : ℕ → HomPair P₁ P₂ → ℂ := fun k => coefFun Y₁ Y₂ f w₃ α₃ h₄ n k with hBdef
  have hrec : ∀ k, L0T P₁ P₂ (B k) = n • B k + ((k : ℂ) + 1) • B (k + 1) :=
    fun k => L0T_coefFun hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf n k
  -- `M` is stable under `L0T`
  have hstab : ∀ G ∈ M, L0T P₁ P₂ G ∈ M := by
    intro G hG
    rw [← hL ⟨G, hG⟩]
    exact Submodule.coe_mem _
  -- every `B k` lies in `M`
  have hmem : ∀ k, B k ∈ M := by
    intro k
    induction k with
    | zero => exact hB
    | succ k ih =>
      have e : B (k + 1) = ((k : ℂ) + 1)⁻¹ • (L0T P₁ P₂ (B k) - n • B k) := by
        rw [hrec k, add_sub_cancel_left, smul_smul,
          inv_mul_cancel₀ (Nat.cast_add_one_ne_zero k), one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hstab _ ih) (Submodule.smul_mem _ _ ih))
  -- the complement of the eigen-submodule, from rationality
  have hcompl := hV.rational A (eigenSubmodule A.toWeakModule)
  -- `(L(0) − n)` on `M` is `L0T − n` on functions
  have hsub : ∀ k, ((L0 A.toWeakModule - n • 1) ⟨B k, hmem k⟩ : HomPair P₁ P₂ → ℂ)
      = ((k : ℂ) + 1) • B (k + 1) := by
    intro k
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_sub,
      hL, Submodule.coe_smul, hrec k]
    simp only [add_sub_cancel_left]
  -- downward induction
  have key : ∀ j : ℕ, ∀ k, 1 ≤ k → K + 1 ≤ k + j → B k = 0 := by
    intro j
    induction j with
    | zero => intro k _ hk; exact hK k (by omega)
    | succ j ih =>
      intro k hk1 hkj
      have hnext : B (k + 1) = 0 := ih (k + 1) (by omega) (by omega)
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have h2 : (L0 A.toWeakModule - n • 1) ((L0 A.toWeakModule - n • 1) ⟨B k', hmem k'⟩) = 0 := by
        have e1 : (L0 A.toWeakModule - n • 1) ⟨B k', hmem k'⟩
            = ((k' : ℂ) + 1) • (⟨B (k' + 1), hmem (k' + 1)⟩ : M) := by
          apply Subtype.ext
          rw [hsub k', Submodule.coe_smul]
        rw [e1, map_smul]
        apply Subtype.ext
        rw [Submodule.coe_smul, hsub (k' + 1), hnext, smul_zero, smul_zero]
        rfl
      have h1 := sub_L0_eq_zero_of_sq A.toWeakModule hcompl n h2
      have h1' := congrArg (fun G : M => (G : HomPair P₁ P₂ → ℂ)) h1
      simp only at h1'
      rw [hsub k'] at h1'
      have hne : ((k' : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k'
      exact (smul_eq_zero.mp h1').resolve_left hne
  intro k hk
  exact key K k hk (by omega)

end Main

/-- **`CoeffL0Semisimple` from the two named inputs** (strongly rational `V`): rationality
replaces the ABD / DLM 8.1(c) / `A(V)` steps of the natural route. -/
theorem coeffL0Semisimple_of_admissible (hV : StronglyRational W) (hB : CoeffLogBounded W)
    (hM : CoeffAdmissibleInput W) : CoeffL0Semisimple W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ α₃ h₄ w₃ f h₃ hf n
  obtain ⟨K, hK⟩ := hB P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ α₃ h₄ w₃ f h₃ hf n
  obtain ⟨M, A, hL, hmem⟩ := hM P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ α₃ h₄ w₃ f h₃ hf n
  have hz := coefFun_log_eq_zero hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf n hK M A hL hmem 1 le_rfl
  refine ⟨{0}, fun _ => coefFun Y₁ Y₂ f w₃ α₃ h₄ n 0, fun _ => n, ?_, by simp⟩
  intro i _
  rw [L0T_coefFun hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf n 0]
  simp only [Nat.cast_zero, zero_add, one_smul, zero_add] at hz ⊢
  rw [hz, add_zero]

/-- **`AssociativityInput` from the named inputs** (strongly rational `V`). -/
theorem associativityInput_of_admissible (hV : StronglyRational W) (hB : CoeffLogBounded W)
    (hM : CoeffAdmissibleInput W) (hZ : AssocCoeffIdentityZero W) : AssociativityInput W :=
  associativityInput_of_split hV (coeffL0Semisimple_of_admissible hV hB hM) hZ

/-- Sanity: the log bound follows from the target (with `K = 0`). -/
theorem coeffLogBounded_of_coeffL0Semisimple (hV : StronglyRational W)
    (hS : CoeffL0Semisimple W) : CoeffLogBounded W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ α₃ h₄ w₃ f h₃ hf n
  refine ⟨0, fun k hk => ?_⟩
  funext x
  simp only [coefFun, Pi.zero_apply]
  exact prodExpCoeff_log_eq_zero hV hS i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hf _ hk

end VOA.Huang.LogRemovalAdmissible
