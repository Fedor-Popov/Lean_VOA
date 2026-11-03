/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LeeYangSingular
import VOA.Examples.VirasoroSimple
import VOA.Core.SingularVector

/-!
# Properness of the Lee–Yang singular submodule, and `V(-22/5,0)` is not simple

`Examples/LeeYangSingular` derives the Lee–Yang central charge `c = -22/5` and the level-4
singular vector `s = 5L₋₂²|0⟩ - 3L₋₄|0⟩` of the universal vacuum module
`V(-22/5,0) = VirUniv leeYangC`, and proves that the `U(𝔙𝔦𝔯)`-submodule
`leeYangSubmodule = U(𝔙𝔦𝔯)·s` it generates is **nonzero**.  It leaves open the complementary
half, quoted from that file: *"Not proved here: that this submodule is PROPER."*

This file closes that gap, and then converts it into the VOA statement.

## The argument

**Properness** is proved by the **straightening route based at `s`** — the analogue of
`Examples/VirasoroSpanning.negSpanVir_eq_top` with the vacuum replaced by `s`, and with words in
*all* strictly negative modes (unlike the vacuum case, `L₋₁s ≠ 0`) — closed off by an
`L₀`-eigenvalue argument rather than by a full graded decomposition:

1. `leeYangWord [n₁,…,n_r] = L₋ₙ₁₋₁ ⋯ L₋ₙᵣ₋₁ s` — the creation words based at `s`; their `ℂ`-span
   is `leeYangWordSpan`.
2. `Lop_leeYangWord` — **straightening**: *every* mode `Lₘ` (`m` of any sign) applied to a
   creation word stays in `leeYangWordSpan`.  The base case `r = 0` is exactly the singularity of
   `s` (`leeYangSingular_annihilated` for `m ≥ 1`, `leeYangSingular_L0` for `m = 0`, a length-one
   word for `m ≤ -1`); the induction step commutes `Lₘ` to the right past one creation operator,
   the central cocycle contributing the scalar `c`.
3. Hence `leeYangWordSpan` is a `U(𝔙𝔦𝔯)`-submodule containing `s`, so
   `leeYangSubmodule ≤ leeYangWordSpan` (`leeYangSubmodule_le_leeYangWordSpan`).
4. `L0_leeYangWord` — each creation word is an `L₀`-eigenvector of eigenvalue
   `leeYangEnergy ws = 4 + Σ(nᵢ+1) ≥ 4`, in particular of **nonzero** eigenvalue.  The vacuum is
   an `L₀`-eigenvector of eigenvalue `0`, and eigenspaces for distinct eigenvalues are independent
   (`Module.End.eigenspaces_iSupIndep`), so the vacuum — nonzero by
   `Examples/VirasoroNonvanishing.vacVec_ne_zero` — cannot lie in `leeYangWordSpan`.

**Non-simplicity of the VOA** needs one more step, because `Core/BilinearForm.IsIdeal` asks a
subspace to absorb *every* mode `u₍ₙ₎` of *every* state `u`, not merely the Virasoro modes
`Lₘ = ω₍ₘ₊₁₎`.  §5 supplies exactly that, for the Virasoro VOA and for an arbitrary central
charge: `virasoroVOA c` is reconstructed from `Y(ω,z)`, so each `Y(u,z)` is a `ℂ`-combination of
the word fields `YwordVir ws`, which are iterated normal-ordered products of `z`-derivatives of
`Y(ω,z)`; every coefficient of such a field is a locally finite sum of products of `Lₘ`'s.  Hence
`isIdeal_of_Lop_stable`: **every `𝔙𝔦𝔯`-stable subspace of `V(c,0)` is a VOA ideal.**  With it,
`leeYangWordSpan` is a proper nonzero ideal and `Core/SingularVector` does the rest.

## Main results

* `vacVec_notMem_leeYangSubmodule` — `|0⟩ ∉ U(𝔙𝔦𝔯)·s`; `leeYangSubmodule_ne_top`,
  `leeYangSubmodule_lt_top` — the submodule is **proper**.
* `leeYang_not_isSimpleModule` — `V(-22/5,0)` is not a simple `U(𝔙𝔦𝔯)`-module.
* `isIdeal_of_Lop_stable` — *(general `c`, of independent interest; a candidate for promotion
  to `VOA.VirModule`)* every `𝔙𝔦𝔯`-stable subspace of `V(c,0)` is an ideal of
  `virasoroVOA c`.
* `virasoroVOA_leeYang_not_isSimple` — **`V(-22/5,0)` is NOT SIMPLE as a VOA.**
* `maxIdealVir_leeYang_ne_bot` — the maximal proper ideal of `virasoroVOA leeYangC` is nonzero,
  so the simple quotient `L(-22/5,0) = virasoroSimple leeYangC` is a **proper** quotient:
  `leeYangSingular_mem_maxIdealVir`, `mkQ_leeYangSingular_eq_zero`, `mkQ_not_injective`.
* Supporting: `Lop_leeYangWord`, `L0_leeYangWord`, `leeYangWordSpan_smul_stable`,
  `leeYangWord_mem_eigenspace`, `CoeffStable` and its closure lemmas, `leeYangWordSpan_isIdeal`.

## Status

`sorry`-free, no new axioms (`propext`, `Classical.choice`, `Quot.sound` only), `pbw`-free.

What is **not** claimed: that `leeYangSubmodule` (or `leeYangWordSpan`) *equals* the maximal ideal,
i.e. that the singular vector generates all of it.  Only `≤` is proved
(`leeYangSingular_mem_maxIdealVir`), which is all that non-simplicity needs.
-/

set_option linter.style.longLine false

namespace VOA.LeeYang

open VOA
open VOA.VirModule
open Module (End)
open LieAlgebra LieAlgebra.Extension UniversalEnvelopingAlgebra

/-! ## §1  Creation words based at the singular vector.

Unlike the vacuum (where `L₋₁|0⟩ = 0` and only modes `≤ -2` occur), the singular vector `s` has
`L₋₁s ≠ 0`, so the words here run over **all** strictly negative modes `L₋ₙ₋₁`, `n : ℕ`. -/

/-- The **creation word based at `s`**: `leeYangWord [n₁,…,n_r] = L₋ₙ₁₋₁ ⋯ L₋ₙᵣ₋₁ s`. -/
noncomputable def leeYangWord : List ℕ → VirUniv leeYangC
  | [] => leeYangSingular
  | (n :: ws) => Lop leeYangC (-(n : ℤ) - 1) (leeYangWord ws)

@[simp] theorem leeYangWord_nil : leeYangWord [] = leeYangSingular := rfl

theorem leeYangWord_cons (n : ℕ) (ws : List ℕ) :
    leeYangWord (n :: ws) = Lop leeYangC (-(n : ℤ) - 1) (leeYangWord ws) := rfl

/-- The **conformal weight** of a creation word based at `s`: `4 + Σ(nᵢ+1)`, since `s` has weight
`4` and each `L₋ₙ₋₁` raises the weight by `n+1`. -/
def leeYangEnergy : List ℕ → ℕ
  | [] => 4
  | (n :: ws) => (n + 1) + leeYangEnergy ws

@[simp] theorem leeYangEnergy_nil : leeYangEnergy [] = 4 := rfl

theorem leeYangEnergy_cons (n : ℕ) (ws : List ℕ) :
    leeYangEnergy (n :: ws) = (n + 1) + leeYangEnergy ws := rfl

/-- Every creation word based at `s` has conformal weight at least `4` — the whole point. -/
theorem four_le_leeYangEnergy (ws : List ℕ) : 4 ≤ leeYangEnergy ws := by
  induction ws with
  | nil => exact le_rfl
  | cons n ws ih => rw [leeYangEnergy_cons]; omega

/-- The `ℂ`-span of the creation words based at `s`. -/
noncomputable def leeYangWordSpan : Submodule ℂ (VirUniv leeYangC) :=
  Submodule.span ℂ (Set.range leeYangWord)

theorem leeYangWord_mem (ws : List ℕ) : leeYangWord ws ∈ leeYangWordSpan :=
  Submodule.subset_span ⟨ws, rfl⟩

theorem leeYangSingular_mem_leeYangWordSpan : leeYangSingular ∈ leeYangWordSpan :=
  leeYangWord_mem []

/-- The creation modes `L₋ₙ₋₁` preserve the span (prepend another creation operator). -/
theorem leeYangWordSpan_neg_stable (n : ℕ) {v : VirUniv leeYangC} (hv : v ∈ leeYangWordSpan) :
    Lop leeYangC (-(n : ℤ) - 1) v ∈ leeYangWordSpan := by
  induction hv using Submodule.span_induction with
  | mem y hy => obtain ⟨ws, rfl⟩ := hy; exact leeYangWord_mem (n :: ws)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-! ## §2  Straightening based at `s`. -/

/-- **Straightening at `s`**: *any* Virasoro mode `Lₘ` applied to a creation word based at `s`
stays in `leeYangWordSpan`.  Induction on the word: the base case is the singularity of `s`
(`Lₘs = 0` for `m ≥ 1`, `L₀s = 4s`, and `Lₘs` is itself a length-one word for `m ≤ -1`); the step
commutes `Lₘ` past one creation operator via `virVacRho_comm`, the central cocycle reducing to the
scalar `leeYangC`. -/
theorem Lop_leeYangWord (m : ℤ) (ws : List ℕ) :
    Lop leeYangC m (leeYangWord ws) ∈ leeYangWordSpan := by
  induction ws generalizing m with
  | nil =>
      rw [leeYangWord_nil]
      rcases (by omega : m ≤ -1 ∨ m = 0 ∨ 1 ≤ m) with hm | hm | hm
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -(n : ℤ) - 1 := ⟨(-m - 1).toNat, by omega⟩
        exact leeYangWord_mem [n]
      · subst hm
        rw [leeYangSingular_L0]
        exact Submodule.smul_mem _ _ leeYangSingular_mem_leeYangWordSpan
      · rw [leeYangSingular_annihilated hm]; exact Submodule.zero_mem _
  | cons i ws ih =>
      rw [leeYangWord_cons]
      change virVacRho leeYangC (L m) (virVacRho leeYangC (L (-(i : ℤ) - 1)) (leeYangWord ws))
        ∈ leeYangWordSpan
      rw [virVacRho_comm]
      apply Submodule.add_mem
      · exact leeYangWordSpan_neg_stable i (ih m)
      · rw [virasoro_bracket, map_add, LinearMap.add_apply]
        apply Submodule.add_mem
        · rw [map_smul, LinearMap.smul_apply]
          exact Submodule.smul_mem _ _ (ih (m + (-(i : ℤ) - 1)))
        · split_ifs with hcond
          · rw [map_smul, LinearMap.smul_apply, vac_acts_central, LinearMap.smul_apply,
              LinearMap.id_coe, id_eq]
            exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (leeYangWord_mem ws))
          · rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _

/-- Any element of `𝔙𝔦𝔯` applied to a creation word stays in the span (reduce to the generators
`Lₙ`, `C` via `mem_span_gensVir`). -/
theorem virVacRho_leeYangWord_mem (x : Virasoro) (ws : List ℕ) :
    virVacRho leeYangC x (leeYangWord ws) ∈ leeYangWordSpan := by
  induction (mem_span_gensVir x) using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨n, rfl⟩ | hy
      · exact Lop_leeYangWord n ws
      · rw [Set.mem_singleton_iff] at hy; subst hy
        rw [vac_acts_central, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
        exact Submodule.smul_mem _ _ (leeYangWord_mem ws)
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ ha

/-- `leeYangWordSpan` is stable under the whole `𝔙𝔦𝔯`-action. -/
theorem leeYangWordSpan_rho_stable (x : Virasoro) {v : VirUniv leeYangC}
    (hv : v ∈ leeYangWordSpan) : virVacRho leeYangC x v ∈ leeYangWordSpan := by
  induction hv using Submodule.span_induction with
  | mem y hy => obtain ⟨ws, rfl⟩ := hy; exact virVacRho_leeYangWord_mem x ws
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

/-- `leeYangWordSpan` is stable under every Virasoro mode `Lₘ`. -/
theorem leeYangWordSpan_Lop_stable (m : ℤ) (v : VirUniv leeYangC) (hv : v ∈ leeYangWordSpan) :
    Lop leeYangC m v ∈ leeYangWordSpan :=
  leeYangWordSpan_rho_stable (L m) hv

/-- `leeYangWordSpan` is a `U(𝔙𝔦𝔯)`-submodule. -/
theorem leeYangWordSpan_smul_stable (r : UVir) {v : VirUniv leeYangC}
    (hv : v ∈ leeYangWordSpan) : r • v ∈ leeYangWordSpan := by
  suffices H : ∀ p : TensorAlgebra ℂ Virasoro, ∀ t ∈ leeYangWordSpan,
      (mkU p) • t ∈ leeYangWordSpan by
    obtain ⟨p, rfl⟩ := mkU_surjective r
    exact H p v hv
  intro p
  induction p using TensorAlgebra.induction with
  | algebraMap a =>
      intro t ht; rw [AlgHom.commutes, algebraMap_smul UVir]; exact Submodule.smul_mem _ a ht
  | ι x => intro t ht; exact leeYangWordSpan_rho_stable x ht
  | mul p q hp hq => intro t ht; rw [map_mul, mul_smul]; exact hp _ (hq t ht)
  | add p q hp hq =>
      intro t ht; rw [map_add, add_smul]; exact Submodule.add_mem _ (hp t ht) (hq t ht)

/-- **The submodule generated by `s` is contained in the span of the creation words based at
`s`** — the straightening theorem in its usable form. -/
theorem leeYangSubmodule_le_leeYangWordSpan {v : VirUniv leeYangC}
    (hv : v ∈ leeYangSubmodule) : v ∈ leeYangWordSpan := by
  rw [leeYangSubmodule, Submodule.mem_span_singleton] at hv
  obtain ⟨r, rfl⟩ := hv
  exact leeYangWordSpan_smul_stable r leeYangSingular_mem_leeYangWordSpan

/-! ## §3  The creation words are `L₀`-eigenvectors of weight `≥ 4`. -/

/-- **The energy identity based at `s`**: `L₀ · leeYangWord ws = leeYangEnergy ws · leeYangWord ws`.
Proved by commuting `L₀` to the right (`[L₀, L₋ₙ₋₁] = (n+1)L₋ₙ₋₁`, no central term since
`-n-1 ≠ 0`) where it meets `L₀s = 4s`. -/
theorem L0_leeYangWord (ws : List ℕ) :
    Lop leeYangC 0 (leeYangWord ws) = (leeYangEnergy ws : ℂ) • leeYangWord ws := by
  induction ws with
  | nil => rw [leeYangWord_nil, leeYangEnergy_nil, leeYangSingular_L0]; norm_num
  | cons i ws ih =>
      rw [leeYangWord_cons]
      change virVacRho leeYangC (L 0) (virVacRho leeYangC (L (-(i : ℤ) - 1)) (leeYangWord ws))
          = (leeYangEnergy (i :: ws) : ℂ)
              • virVacRho leeYangC (L (-(i : ℤ) - 1)) (leeYangWord ws)
      rw [virVacRho_comm]
      have hfirst : virVacRho leeYangC (L (-(i : ℤ) - 1))
            (virVacRho leeYangC (L 0) (leeYangWord ws))
          = (leeYangEnergy ws : ℂ) • virVacRho leeYangC (L (-(i : ℤ) - 1)) (leeYangWord ws) := by
        rw [show virVacRho leeYangC (L 0) (leeYangWord ws)
            = (leeYangEnergy ws : ℂ) • leeYangWord ws from ih, map_smul]
      have hbr : virVacRho leeYangC ⁅L 0, L (-(i : ℤ) - 1)⁆ (leeYangWord ws)
          = ((i : ℂ) + 1) • virVacRho leeYangC (L (-(i : ℤ) - 1)) (leeYangWord ws) := by
        rw [virasoro_bracket, show ((0 : ℤ) + (-(i : ℤ) - 1)) = -(i : ℤ) - 1 from by ring,
          if_neg (by omega : ¬ -(i : ℤ) - 1 = 0), add_zero, map_smul, LinearMap.smul_apply]
        congr 1; push_cast; ring
      rw [hfirst, hbr, ← add_smul]
      congr 1
      rw [leeYangEnergy_cons]; push_cast; ring

/-- Each creation word based at `s` lies in the `L₀`-eigenspace of its energy. -/
theorem leeYangWord_mem_eigenspace (ws : List ℕ) :
    leeYangWord ws ∈ Module.End.eigenspace (Lop leeYangC 0) ((leeYangEnergy ws : ℂ)) :=
  Module.End.mem_eigenspace_iff.mpr (L0_leeYangWord ws)

/-- The energy of a creation word is a **nonzero** complex number (a natural number `≥ 4`). -/
theorem leeYangEnergy_cast_ne_zero (ws : List ℕ) : ((leeYangEnergy ws : ℂ)) ≠ 0 := by
  have h4 := four_le_leeYangEnergy ws
  have : leeYangEnergy ws ≠ 0 := by omega
  exact_mod_cast Nat.cast_ne_zero.mpr this

/-- The span of the creation words sits inside the sum of the **nonzero** `L₀`-eigenspaces. -/
theorem leeYangWordSpan_le_nonzero_eigenspaces :
    leeYangWordSpan ≤ ⨆ (h : ℂ) (_ : h ≠ 0), Module.End.eigenspace (Lop leeYangC 0) h := by
  rw [leeYangWordSpan, Submodule.span_le]
  rintro _ ⟨ws, rfl⟩
  exact Submodule.mem_iSup_of_mem ((leeYangEnergy ws : ℂ))
    (Submodule.mem_iSup_of_mem (leeYangEnergy_cast_ne_zero ws) (leeYangWord_mem_eigenspace ws))

/-! ## §4  Properness. -/

/-- The vacuum is an `L₀`-eigenvector of eigenvalue `0`. -/
theorem vacVec_mem_eigenspace_zero :
    vacVec leeYangC ∈ Module.End.eigenspace (Lop leeYangC 0) 0 :=
  Module.End.mem_eigenspace_iff.mpr (by
    rw [Lop_vacuum leeYangC (by norm_num : (-1 : ℤ) ≤ 0), zero_smul])

/-- **Properness, span form**: the vacuum is not in the span of the creation words based at `s`.

Every creation word is an `L₀`-eigenvector of eigenvalue `≥ 4` (§3), while `|0⟩` is a nonzero
`L₀`-eigenvector of eigenvalue `0`; distinct eigenspaces are independent. -/
theorem vacVec_notMem_leeYangWordSpan : vacVec leeYangC ∉ leeYangWordSpan := by
  intro hspan
  have hhigh : vacVec leeYangC
      ∈ ⨆ (h : ℂ) (_ : h ≠ 0), Module.End.eigenspace (Lop leeYangC 0) h :=
    leeYangWordSpan_le_nonzero_eigenspaces hspan
  have hdis : Disjoint (Module.End.eigenspace (Lop leeYangC 0) 0)
      (⨆ (h : ℂ) (_ : h ≠ 0), Module.End.eigenspace (Lop leeYangC 0) h) :=
    Module.End.eigenspaces_iSupIndep (Lop leeYangC 0) 0
  exact vacVec_ne_zero leeYangC
    (Submodule.disjoint_def.mp hdis _ vacVec_mem_eigenspace_zero hhigh)

/-- **Properness of the Lee–Yang singular submodule**: the vacuum is **not** in `U(𝔙𝔦𝔯)·s`. -/
theorem vacVec_notMem_leeYangSubmodule : vacVec leeYangC ∉ leeYangSubmodule := fun hmem =>
  vacVec_notMem_leeYangWordSpan (leeYangSubmodule_le_leeYangWordSpan hmem)

/-- **The submodule generated by `s` is proper**. -/
theorem leeYangSubmodule_ne_top : leeYangSubmodule ≠ ⊤ := by
  intro h
  exact vacVec_notMem_leeYangSubmodule (by rw [h]; trivial)

/-- The submodule generated by `s` is *strictly* between `⊥` and `⊤`. -/
theorem leeYangSubmodule_lt_top : leeYangSubmodule < ⊤ :=
  lt_of_le_of_ne le_top leeYangSubmodule_ne_top

theorem bot_lt_leeYangSubmodule : ⊥ < leeYangSubmodule :=
  lt_of_le_of_ne bot_le (Ne.symm leeYangSubmodule_ne_bot)

/-- **`V(-22/5,0)` is not a simple `U(𝔙𝔦𝔯)`-module**: `U(𝔙𝔦𝔯)·s` is a nonzero proper
submodule.  (The VOA statement is `virasoroVOA_leeYang_not_isSimple`, §6.) -/
theorem leeYang_not_isSimpleModule : ¬ IsSimpleModule UVir (VirUniv leeYangC) := by
  intro hsimple
  rcases IsSimpleOrder.eq_bot_or_eq_top (α := Submodule UVir (VirUniv leeYangC))
      leeYangSubmodule with hbot | htop
  · exact leeYangSubmodule_ne_bot hbot
  · exact leeYangSubmodule_ne_top htop

/-- The quotient of `V(-22/5,0)` by the submodule generated by `s` is **nonzero**: the vacuum
survives it. -/
theorem leeYangQuotient_nontrivial : Nontrivial (VirUniv leeYangC ⧸ leeYangSubmodule) := by
  refine ⟨⟨Submodule.Quotient.mk (vacVec leeYangC), 0, ?_⟩⟩
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  exact vacVec_notMem_leeYangSubmodule

/-! ## §5  From `𝔙𝔦𝔯`-stability to VOA ideals — general in the central charge.

`Core/BilinearForm.IsIdeal` asks a subspace to absorb every mode `u₍ₙ₎` of every state `u`, not
merely the Virasoro modes.  For `virasoroVOA c` that is no stronger, because the whole vertex map
is reconstructed from `Y(ω,z)`: `virYA c u` is a `ℂ`-combination of the word fields `YwordVir ws`
(`negSpanVir_eq_top` + `virYA_word`), which are iterated normal-ordered products of `z`-derivatives
of `Y(ω,z)`, and every coefficient of such a field is a locally finite sum of products of `Lₘ`'s.

Nothing in this section is specific to Lee–Yang; it is stated for arbitrary `c` and is a candidate
for promotion to `VOA.VirModule`. -/

section CoeffStable

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- `I` is **coefficient-stable** for the distribution `a` when every coefficient of `a` maps `I`
into itself. -/
def CoeffStable (I : Submodule ℂ V) (a : FormalDist (End ℂ V)) : Prop :=
  ∀ (n : ℤ) (v : V), v ∈ I → a n v ∈ I

theorem CoeffStable.smul {I : Submodule ℂ V} {a : FormalDist (End ℂ V)} (h : CoeffStable I a)
    (r : ℂ) : CoeffStable I (r • a) := by
  intro n v hv
  change (r • a n) v ∈ I
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (h n v hv)

theorem CoeffStable.deriv {I : Submodule ℂ V} {a : FormalDist (End ℂ V)} (h : CoeffStable I a) :
    CoeffStable I (VOA.deriv a) := by
  intro n v hv
  rw [deriv_apply]
  change ((n + 1 : ℤ) • a (n + 1)) v ∈ I
  rw [LinearMap.smul_apply]
  exact zsmul_mem (h (n + 1) v hv) _

theorem CoeffStable.deriv_iterate {I : Submodule ℂ V} {a : FormalDist (End ℂ V)}
    (h : CoeffStable I a) : ∀ i : ℕ, CoeffStable I (VOA.deriv^[i] a)
  | 0 => h
  | (i + 1) => by
      rw [Function.iterate_succ_apply']
      exact (h.deriv_iterate i).deriv

/-- The same-variable normal-ordered product of two coefficient-stable fields is
coefficient-stable: each diagonal summand is a composite of two stable coefficients, and the
(locally finite) sum stays in the subspace. -/
theorem CoeffStable.nprod {I : Submodule ℂ V} {a b : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) (hA : CoeffStable I a) (hB : CoeffStable I b) :
    CoeffStable I (VOA.nprod ha hb) := by
  intro s v hv
  rw [nprod_apply]
  refine QuotVOA.finsum_mem_submodule I _ fun m => ?_
  rw [normalOrdered_apply]
  split_ifs with h0
  · rw [Module.End.mul_apply]; exact hA m _ (hB (s - m) v hv)
  · rw [Module.End.mul_apply]; exact hB (s - m) _ (hA m v hv)

end CoeffStable

variable (c : ℂ)

/-- A `𝔙𝔦𝔯`-stable subspace is coefficient-stable for `Y(ω,z)` (its coefficients are the `Lₘ`). -/
theorem coeffStable_YomegaVir {I : Submodule ℂ (VirUniv c)}
    (h : ∀ (m : ℤ) (v : VirUniv c), v ∈ I → Lop c m v ∈ I) : CoeffStable I (YomegaVir c) := by
  intro n v hv
  rw [YomegaVir_apply]
  exact h _ v hv

/-- … hence for each scaled generator field `(i!)⁻¹∂ⁱY(ω,z)`. -/
theorem coeffStable_genFieldVir {I : Submodule ℂ (VirUniv c)}
    (h : ∀ (m : ℤ) (v : VirUniv c), v ∈ I → Lop c m v ∈ I) (i : ℕ) :
    CoeffStable I (genFieldVir c i) := by
  rw [genFieldVir]
  exact ((coeffStable_YomegaVir c h).deriv_iterate i).smul _

/-- The identity field `Y(|0⟩,z)` is harmless. -/
theorem coeffStable_idFieldVir (I : Submodule ℂ (VirUniv c)) : CoeffStable I (idFieldVir c) := by
  intro n v hv
  rw [idFieldVir]
  split_ifs
  · exact hv
  · exact Submodule.zero_mem _

/-- … hence for every word field `:∂^{i₁}ω ⋯ ∂^{i_k}ω:`. -/
theorem coeffStable_YwordVir {I : Submodule ℂ (VirUniv c)}
    (h : ∀ (m : ℤ) (v : VirUniv c), v ∈ I → Lop c m v ∈ I) :
    ∀ ws : List ℕ, CoeffStable I (YwordVir c ws)
  | [] => by rw [YwordVir_nil]; exact coeffStable_idFieldVir c I
  | (i :: rest) => by
      rw [YwordVir_cons]
      exact CoeffStable.nprod _ _ (coeffStable_genFieldVir c h i) (coeffStable_YwordVir h rest)

/-- … hence for `Y(u,z)` for **every** state `u`, since the creation monomials span `V(c,0)` and
`virYA` is linear. -/
theorem coeffStable_virYA {I : Submodule ℂ (VirUniv c)}
    (h : ∀ (m : ℤ) (v : VirUniv c), v ∈ I → Lop c m v ∈ I) (u : VirUniv c) :
    CoeffStable I (virYA c u) := by
  have hu : u ∈ negSpanVir c := by rw [negSpanVir_eq_top c]; trivial
  induction hu using Submodule.span_induction with
  | mem y hy => obtain ⟨ws, rfl⟩ := hy; rw [virYA_word]; exact coeffStable_YwordVir c h ws
  | zero =>
      intro n v _
      rw [map_zero]
      change (0 : End ℂ (VirUniv c)) v ∈ I
      rw [LinearMap.zero_apply]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      intro n v hv
      rw [map_add]
      change (virYA c x n + virYA c y n) v ∈ I
      rw [LinearMap.add_apply]
      exact Submodule.add_mem _ (hx n v hv) (hy n v hv)
  | smul r x _ hx =>
      intro n v hv
      rw [map_smul]
      exact hx.smul r n v hv

/-- **Every `𝔙𝔦𝔯`-stable subspace of `V(c,0)` is a VOA ideal of `virasoroVOA c`.**  For the
Virasoro VOA the two notions of stability coincide, because the vertex map is reconstructed from
`Y(ω,z)` alone. -/
theorem isIdeal_of_Lop_stable {I : Submodule ℂ (VirUniv c)}
    (h : ∀ (m : ℤ) (v : VirUniv c), v ∈ I → Lop c m v ∈ I) : (virasoroVOA c).IsIdeal I := by
  intro u v n hv
  exact coeffStable_virYA c h u (-n - 1) v hv

/-! ## §6  `V(-22/5,0)` is not simple, and `L(-22/5,0)` is a proper quotient. -/

open VOA.SingVec
open VOA.VirSimple

/-- The span of the creation words based at `s` is a **VOA ideal** of `virasoroVOA leeYangC`. -/
theorem leeYangWordSpan_isIdeal : (virasoroVOA leeYangC).IsIdeal leeYangWordSpan :=
  isIdeal_of_Lop_stable leeYangC leeYangWordSpan_Lop_stable

/-- The VOA ideal generated by `s` is **proper**: it sits inside `leeYangWordSpan`, which misses
the vacuum. -/
theorem vacuum_notMem_idealGen :
    (virasoroVOA leeYangC).vacuum ∉ idealGen (virasoroVOA leeYangC) leeYangSingular :=
  vacuum_not_mem_idealGen_of_le leeYangWordSpan_isIdeal
    leeYangSingular_mem_leeYangWordSpan vacVec_notMem_leeYangWordSpan

/-- **`V(-22/5,0)` is NOT SIMPLE as a vertex operator algebra.**  The Lee–Yang singular vector
generates a nonzero proper ideal. -/
theorem virasoroVOA_leeYang_not_isSimple : ¬ (virasoroVOA leeYangC).IsSimple :=
  not_isSimple_of_idealGen_proper leeYangSingular_ne_zero vacuum_notMem_idealGen

/-- **The maximal proper ideal of `virasoroVOA leeYangC` is nonzero** — equivalently (by
`virasoroVOA_isSimple_iff`) `V(-22/5,0)` is not simple. -/
theorem maxIdealVir_leeYang_ne_bot : maxIdealVir leeYangC ≠ ⊥ := by
  intro h
  exact virasoroVOA_leeYang_not_isSimple ((virasoroVOA_isSimple_iff leeYangC).mpr h)

/-- The singular vector lies in the maximal ideal (only `≤` is claimed — not that it generates
it). -/
theorem leeYangSingular_mem_maxIdealVir : leeYangSingular ∈ maxIdealVir leeYangC :=
  le_maxIdealVir leeYangC leeYangWordSpan_isIdeal vacVec_notMem_leeYangWordSpan
    leeYangSingular_mem_leeYangWordSpan

/-- `s` dies in the simple quotient `L(-22/5,0) = virasoroSimple leeYangC`. -/
theorem mkQ_leeYangSingular_eq_zero : (maxIdealVir leeYangC).mkQ leeYangSingular = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr leeYangSingular_mem_maxIdealVir

/-- **`L(-22/5,0)` is a *proper* quotient of `V(-22/5,0)`**: the projection is not injective,
since it kills the nonzero vector `s`. -/
theorem mkQ_not_injective : ¬ Function.Injective (maxIdealVir leeYangC).mkQ := by
  intro hinj
  apply leeYangSingular_ne_zero
  apply hinj
  rw [mkQ_leeYangSingular_eq_zero, map_zero]

end VOA.LeeYang
