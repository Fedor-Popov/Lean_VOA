/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUFullMode
import VOA.Modules.ZhuVermaAnArchDJ27

/-!
# The `A(𝒱)`-balanced level-`n` piece on DJ's GENUINE ideal: `A_{n,0}(𝒱) ⊗_{A(𝒱)} U`

`ZhuVermaAnArchMUBalancedPiece` built the balanced piece `MUPieceBal W U n` over the **prime** ideal
`Onm` (= DJ's `O'_{n,0}`).  Over that ideal the mode operators do *not* descend to the balanced
quotient without the DJ Remark 2.10 closure.  This file redoes the
whole construction over Dong–Jiang's **actual** ideal `OnmFull` (`O' + O'' + O'''`), where the
needed closure is a THEOREM.

## Why the surgery works over `OnmFull` (STEP 2, the of this file)

Descending `oFullU W U N n v : A_{n,0}(𝒱) ⊗ U → A_{N,0}(𝒱) ⊗ U` to the balanced quotients needs
exactly one associativity statement in `𝒱`:

  `(v ∗^N_{0,n} x) ∗^N_0 a  −  v ∗^N_{0,n} (x ∗^n_0 a)  ∈  O_{N,0}(𝒱)`.

That is the `(p₁, p₂) = (0, n)` instance of the **bare Dong–Jiang associator**
`bareAssoc_mem_OnmFull` (`ZhuVermaAnArchDJ27`, the `u = 𝟙` specialization of the `O''_{N,0}`
generator via `anmGen_vacuum_diag`) — unconditional over `OnmFull`, and provably out of reach over
the prime ideal (DJ Rmk 2.10).  So the balanced mode operator `oBalFullU` is a term with no carried
hypothesis, and DJ Lemma 4.1 (`oFullU_comp`) transports verbatim.

## Contents (axiom-clean, pbw-free)

* **`balancingSetFull` / `balancingFull W U n`** — the `A(𝒱)`-balancing submodule of the ℂ-tensor
  cover `MUPieceFull W U n = A_{n,0}(𝒱) ⊗_ℂ U`, spanned by `[x ∗^n_0 a] ⊗ u − [x] ⊗ ρ(a)·u`.
* **`MUPieceBalFull W U n`** — the balanced level-`n` piece `A_{n,0}(𝒱) ⊗_{A(𝒱)} U` on DJ's genuine
  ideal, with projection `mkPieceBalFull` and the defining relation `mkPieceBalFull_balance`.
* **`anmGen_anmRight_assoc_mem_OnmFull`** — the surgery associativity, an instance of DJ's bare
  associator.
* **`oFullU_le_comap_balancingFull`** — `oFullU` maps the balancing into the balancing.
* **`oBalFullU W U N n v`** — the descended (balanced) DJ mode operator, unconditional.
* **`oBalFullU_comp`** — DJ Lemma 4.1 on the balanced pieces, plus vacuum diagonal/off-diagonal
  (`oBalFullU_vacuum_diag`, `oBalFullU_vacuum_offdiag`) and linearity in the acting vector.

pbw-free.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), §2 (`O_{n,m} = O' + O'' + O'''`, Lemma 2.8,
Thm 2.9, Rmk 2.10), §4 (Lemma 4.1, Thm 4.13); Gannon §5.3.2.  Cross-ref
`ZhuVermaAnArchMUBalancedPiece` (the prime-ideal template this mirrors).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## STEP 1 — the `A(𝒱)`-balancing submodule of the full-ideal ℂ-tensor cover -/

/-- **The balancing generators** at level `n` on DJ's genuine ideal: the differences
`[x ∗^n_0 a] ⊗ u − [x] ⊗ ρ(a)·u` (`x a : 𝒱`, `u : U`), i.e. the representative-level
`A(𝒱)`-balancing relations (right residue action on `A_{n,0}(𝒱)` versus left action on `U`). -/
def balancingSetFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    Set (MUPieceFull W U n) :=
  {z | ∃ (x a : 𝒱) (u : U.carrier),
    z = mkAnmFull W n 0 (anmRight W n 0 x a) ⊗ₜ[ℂ] u
        - mkAnmFull W n 0 x ⊗ₜ[ℂ] U.ρ (mk W a) u}

/-- **The `A(𝒱)`-balancing submodule** of `MUPieceFull W U n = A_{n,0}(𝒱) ⊗_ℂ U` (full ideal): the
`ℂ`-span of the balancing generators.  Quotienting by it realizes `A_{n,0}(𝒱) ⊗_{A(𝒱)} U`. -/
noncomputable def balancingFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    Submodule ℂ (MUPieceFull W U n) :=
  Submodule.span ℂ (balancingSetFull W U n)

/-- Each balancing generator lies in the balancing submodule. -/
theorem balancingFull_gen_mem (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) (x a : 𝒱)
    (u : U.carrier) :
    mkAnmFull W n 0 (anmRight W n 0 x a) ⊗ₜ[ℂ] u - mkAnmFull W n 0 x ⊗ₜ[ℂ] U.ρ (mk W a) u
      ∈ balancingFull W U n :=
  Submodule.subset_span ⟨x, a, u, rfl⟩

/-- **The `A(𝒱)`-balanced level-`n` piece on DJ's genuine ideal** `A_{n,0}(𝒱) ⊗_{A(𝒱)} U`, realized
as the ℂ-tensor cover `MUPieceFull W U n` modulo the balancing submodule. -/
abbrev MUPieceBalFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) : Type u :=
  MUPieceFull W U n ⧸ balancingFull W U n

/-- The canonical `ℂ`-linear projection `A_{n,0}(𝒱) ⊗_ℂ U ↠ MUPieceBalFull W U n`. -/
noncomputable def mkPieceBalFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    MUPieceFull W U n →ₗ[ℂ] MUPieceBalFull W U n := (balancingFull W U n).mkQ

/-- The balanced projection is surjective. -/
theorem mkPieceBalFull_surjective (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    Function.Surjective (mkPieceBalFull W U n) := Submodule.mkQ_surjective _

/-- **The defining balancing relation** in the balanced piece: `[x ∗^n_0 a] ⊗ u = [x] ⊗ ρ(a)·u`. -/
theorem mkPieceBalFull_balance (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) (x a : 𝒱)
    (u : U.carrier) :
    mkPieceBalFull W U n (mkAnmFull W n 0 (anmRight W n 0 x a) ⊗ₜ[ℂ] u)
      = mkPieceBalFull W U n (mkAnmFull W n 0 x ⊗ₜ[ℂ] U.ρ (mk W a) u) := by
  rw [← sub_eq_zero, mkPieceBalFull, ← map_sub, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact balancingFull_gen_mem W U n x a u

/-! ## STEP 2 — the surgery: the DJ mode operators descend to the balanced pieces

The single `𝒱`-level input is the bare Dong–Jiang associator at `(p₁, p₂) = (0, n)`. -/

/-- **The surgery associativity, unconditional.**
`(v ∗^N_{0,n} x) ∗^N_0 a − v ∗^N_{0,n} (x ∗^n_0 a) ∈ O_{N,0}(𝒱)` — the `(p₁, p₂) = (0, n)`,
`m = 0` instance of Dong–Jiang's bare associator `bareAssoc_mem_OnmFull` (itself the `u = 𝟙`
specialization of an `O''_{N,0}` generator).  This is the exact statement that lets the induced
module's mode operators descend to the `A(𝒱)`-balanced quotients; over the prime ideal `Onm` it is
out of reach (DJ Remark 2.10). -/
theorem anmGen_anmRight_assoc_mem_OnmFull (W : VertexOperatorAlgebra 𝒱) (N n : ℕ) (v x a : 𝒱) :
    anmRight W N 0 (anmGen W N 0 n v x) a - anmGen W N 0 n v (anmRight W n 0 x a)
      ∈ OnmFull W N 0 := by
  have h := bareAssoc_mem_OnmFull W N 0 0 n v x a
  rwa [anmGen_eq_anmRight W N 0, anmGen_eq_anmRight W n 0] at h

/-- **The mode operator `o_{N,n}(v)` preserves the balancing.**  `oFullU W U N n v` maps
`balancingFull W U n` into `balancingFull W U N`; the correction term between the image of a
balancing generator and a balancing generator at level `N` is killed by
`anmGen_anmRight_assoc_mem_OnmFull`. -/
theorem oFullU_le_comap_balancingFull (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (N n : ℕ)
    (v : 𝒱) :
    balancingFull W U n ≤ Submodule.comap (oFullU W U N n v) (balancingFull W U N) := by
  rw [balancingFull, Submodule.span_le]
  rintro z ⟨x, a, u, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, oFullU_tmul]
  have hgen := balancingFull_gen_mem W U N (anmGen W N 0 n v x) a u
  have heq : mkAnmFull W N 0 (anmGen W N 0 n v (anmRight W n 0 x a))
      = mkAnmFull W N 0 (anmRight W N 0 (anmGen W N 0 n v x) a) := by
    rw [mkAnmFull, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have h := anmGen_anmRight_assoc_mem_OnmFull W N n v x a
    have h2 := Submodule.neg_mem _ h
    rwa [neg_sub] at h2
  rw [heq]
  exact hgen

/-- **The balanced Dong–Jiang mode operator, unconditional.**  The descent of `oFullU W U N n v`
to the `A(𝒱)`-balanced pieces `A_{n,0}(𝒱) ⊗_{A(𝒱)} U → A_{N,0}(𝒱) ⊗_{A(𝒱)} U`; well defined by
`oFullU_le_comap_balancingFull`, i.e. by DJ's bare associator on the FULL ideal. -/
noncomputable def oBalFullU (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (N n : ℕ) (v : 𝒱) :
    MUPieceBalFull W U n →ₗ[ℂ] MUPieceBalFull W U N :=
  Submodule.mapQ (balancingFull W U n) (balancingFull W U N) (oFullU W U N n v)
    (oFullU_le_comap_balancingFull W U N n v)

/-- The balanced mode operator on a class: it is the class of the unbalanced mode operator. -/
@[simp] theorem oBalFullU_mk (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (N n : ℕ) (v : 𝒱)
    (z : MUPieceFull W U n) :
    oBalFullU W U N n v (mkPieceBalFull W U n z)
      = mkPieceBalFull W U N (oFullU W U N n v z) := rfl

/-- The balanced mode operator on a balanced elementary tensor: DJ's defining formula. -/
theorem oBalFullU_tmul (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (N n : ℕ) (v g : 𝒱)
    (u : U.carrier) :
    oBalFullU W U N n v (mkPieceBalFull W U n (mkAnmFull W n 0 g ⊗ₜ[ℂ] u))
      = mkPieceBalFull W U N (mkAnmFull W N 0 (anmGen W N 0 n v g) ⊗ₜ[ℂ] u) := by
  rw [oBalFullU_mk, oFullU_tmul]

/-- Two endomorphism-valued maps out of a balanced piece agree once they agree on classes. -/
theorem mkPieceBalFull_ext (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ)
    {M : Type*} [AddCommGroup M] [Module ℂ M] {f g : MUPieceBalFull W U n →ₗ[ℂ] M}
    (h : ∀ z : MUPieceFull W U n, f (mkPieceBalFull W U n z) = g (mkPieceBalFull W U n z)) :
    f = g := by
  refine LinearMap.ext (fun y => ?_)
  obtain ⟨z, rfl⟩ := mkPieceBalFull_surjective W U n y
  exact h z

/-- **DJ Lemma 4.1 on the balanced pieces, unconditional** —
`o_{N,p}(a) ∘ o_{p,m}(b) = o_{N,m}(a ∗^N_{m,p} b)`, transported from `oFullU_comp`. -/
theorem oBalFullU_comp (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (N m p : ℕ) (a b : 𝒱) :
    (oBalFullU W U N p a).comp (oBalFullU W U p m b)
      = oBalFullU W U N m (anmGen W N m p a b) := by
  refine mkPieceBalFull_ext W U m (fun z => ?_)
  rw [LinearMap.comp_apply, oBalFullU_mk, oBalFullU_mk, oBalFullU_mk]
  exact congrArg (mkPieceBalFull W U N) (LinearMap.congr_fun (oFullU_comp W U N m p a b) z)

/-- The balanced mode operator is additive in the acting vector. -/
theorem oBalFullU_add_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (N n : ℕ) (a b : 𝒱) :
    oBalFullU W U N n (a + b) = oBalFullU W U N n a + oBalFullU W U N n b := by
  refine mkPieceBalFull_ext W U n (fun z => ?_)
  rw [oBalFullU_mk, LinearMap.add_apply, oBalFullU_mk, oBalFullU_mk, ← map_add,
    ← LinearMap.add_apply, ← oFullU_add_acting]

/-- The balanced mode operator is homogeneous in the acting vector. -/
theorem oBalFullU_smul_acting (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (N n : ℕ) (c : ℂ)
    (a : 𝒱) : oBalFullU W U N n (c • a) = c • oBalFullU W U N n a := by
  refine mkPieceBalFull_ext W U n (fun z => ?_)
  rw [oBalFullU_mk, LinearMap.smul_apply, oBalFullU_mk, ← map_smul, ← LinearMap.smul_apply,
    ← oFullU_smul_acting]

/-- The vacuum mode is the identity on the balanced diagonal (DJ Lemma 4.6(2)). -/
theorem oBalFullU_vacuum_diag (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n : ℕ) :
    oBalFullU W U n n W.vacuum = LinearMap.id := by
  refine mkPieceBalFull_ext W U n (fun z => ?_)
  rw [oBalFullU_mk, oFullU_vacuum_diag]
  rfl

/-- The vacuum mode annihilates the balanced pieces off the diagonal (DJ Lemma 4.6(2)). -/
theorem oBalFullU_vacuum_offdiag (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {n' n : ℕ}
    (h : n' ≠ n) : oBalFullU W U n' n W.vacuum = 0 := by
  refine mkPieceBalFull_ext W U n (fun z => ?_)
  rw [oBalFullU_mk, oFullU_vacuum_offdiag W U h]
  simp

end VOA
