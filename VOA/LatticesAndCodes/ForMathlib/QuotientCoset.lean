/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Splitting a sum over a module into cosets of a submodule

A sum over a module `M` regroups, along a submodule `N` of finite index, into a finite sum of
sums over `N`:

`∑' m : M, f m = ∑_{c : M ⧸ N} ∑' x : N, f (c.out + x)`.

Mathlib has the non-canonical bijection `M ≃ (M ⧸ N) × N`
(`AddSubgroup.addGroupEquivQuotientProdAddSubgroup`) but its underlying function is buried in a
chain of `Equiv`s, so it cannot be used to rewrite the summand.  `Submodule.quotProdEquiv` below
is the same bijection written out, with `Quotient.out` as the choice of coset representative, so
that its underlying function is definitionally `(c, x) ↦ c.out + x`.

This is what turns the `S`-transformation of a theta series — a sum over the dual lattice `Γ*` —
into a sum over the **discriminant group** `Γ*/Γ` of theta series with characteristics.

## Main results

* `Submodule.quotProdEquiv` — the bijection `(M ⧸ N) × N ≃ M`, `(c, x) ↦ c.out + x`.
* `Submodule.tsum_eq_sum_tsum_quot` — the coset decomposition of a `tsum`, for `N` of finite
  index.
* `Submodule.summable_coset_of_summable` — the same for summability.
-/

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (N : Submodule R M)

theorem mk_out (c : M ⧸ N) : (Submodule.Quotient.mk (Quotient.out c) : M ⧸ N) = c :=
  Quotient.out_eq' c

theorem sub_out_mem (m : M) :
    m - Quotient.out (Submodule.Quotient.mk m : M ⧸ N) ∈ N :=
  (Submodule.Quotient.eq N).1 (mk_out N (Submodule.Quotient.mk m)).symm

/-- A (non-canonical) bijection `(M ⧸ N) × N ≃ M`, sending `(c, x)` to `c.out + x`.  Unlike
`AddSubgroup.addGroupEquivQuotientProdAddSubgroup` the underlying function is transparent, which
is what lets a `tsum` be rewritten along it. -/
noncomputable def quotProdEquiv : (M ⧸ N) × N ≃ M where
  toFun p := Quotient.out p.1 + (p.2 : M)
  invFun m :=
    (Submodule.Quotient.mk m,
      ⟨m - Quotient.out (Submodule.Quotient.mk m : M ⧸ N), sub_out_mem N m⟩)
  left_inv := by
    rintro ⟨c, x, hx⟩
    have hc : (Submodule.Quotient.mk (Quotient.out c + x) : M ⧸ N) = c := by
      rw [← mk_out N c]
      exact (Submodule.Quotient.eq N).2 (by simpa using hx)
    ext
    · exact hc
    · simp [hc]
  right_inv m := by simp

@[simp] theorem quotProdEquiv_apply (p : (M ⧸ N) × N) :
    quotProdEquiv N p = Quotient.out p.1 + (p.2 : M) := rfl

variable {N}

variable {α : Type*} [NormedAddCommGroup α] [CompleteSpace α]

omit [CompleteSpace α] in
/-- Summability over `M` is summability of the reindexed family over `(M ⧸ N) × N`. -/
theorem summable_quotProd_iff (f : M → α) :
    (Summable fun p : (M ⧸ N) × N => f (Quotient.out p.1 + (p.2 : M))) ↔ Summable f :=
  (quotProdEquiv N).summable_iff (f := f)

/-- Each coset sum converges when the whole sum does. -/
theorem summable_coset_of_summable {f : M → α} (hf : Summable f) (c : M ⧸ N) :
    Summable fun x : N => f (Quotient.out c + (x : M)) :=
  ((summable_quotProd_iff f).2 hf).prod_factor c

/-- **The coset decomposition of a sum.**  For a submodule `N` of finite index, a sum over `M`
is the finite sum over `M ⧸ N` of the sums over the cosets. -/
theorem tsum_eq_sum_tsum_quot [Fintype (M ⧸ N)] {f : M → α} (hf : Summable f) :
    ∑' m : M, f m = ∑ c : M ⧸ N, ∑' x : N, f (Quotient.out c + (x : M)) := by
  have hre : Summable fun p : (M ⧸ N) × N => f (Quotient.out p.1 + (p.2 : M)) :=
    (summable_quotProd_iff f).2 hf
  rw [← (quotProdEquiv N).tsum_eq f]
  simp only [quotProdEquiv_apply]
  rw [hre.tsum_prod' (fun c => hre.prod_factor c)]
  exact tsum_fintype _

section Nested

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
variable {α : Type*} [NormedAddCommGroup α] [CompleteSpace α]

/-- **The coset decomposition for a pair of nested submodules.**  If `L ≤ M` and `M ⧸ L` is
finite, a sum over `M` regroups into the finite sum over `M ⧸ L` of sums over `L`. -/
theorem tsum_eq_sum_tsum_quot_le {L M : Submodule R V} (hLM : L ≤ M)
    [Fintype (M ⧸ L.comap M.subtype)] {f : V → α} (hf : Summable fun y : M => f (y : V)) :
    ∑' y : M, f (y : V)
      = ∑ c : M ⧸ L.comap M.subtype, ∑' x : L, f (((Quotient.out c : M) : V) + (x : V)) := by
  rw [tsum_eq_sum_tsum_quot (N := L.comap M.subtype) (f := fun y : M => f (y : V)) hf]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← (Submodule.comapSubtypeEquivOfLe hLM).toEquiv.tsum_eq
    (fun y : L => f (((Quotient.out c : M) : V) + (y : V)))]
  exact tsum_congr fun x => congrArg f (by simp)

/-- Each coset sum converges when the whole sum does. -/
theorem summable_coset_le {L M : Submodule R V} (hLM : L ≤ M)
    {f : V → α} (hf : Summable fun y : M => f (y : V)) (c : M ⧸ L.comap M.subtype) :
    Summable fun x : L => f (((Quotient.out c : M) : V) + (x : V)) := by
  have h := summable_coset_of_summable (f := fun y : M => f (y : V)) hf c
  rw [← (Submodule.comapSubtypeEquivOfLe hLM).toEquiv.summable_iff] at *
  exact h.congr fun x => congrArg f (by simp)

end Nested

end Submodule
