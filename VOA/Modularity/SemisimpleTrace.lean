/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The commutator quotient of a finite-dimensional semisimple algebra

The last step of Zhu's genus-one dimension count (Dong–Li–Mason, *Modular invariance of trace
functions in orbifold theory*, **Lemma 10.7**) is a pure piece of linear algebra:

> a linear functional on `A(𝒱)` that is **symmetric** (`φ(ab) = φ(ba)`) is a combination of the
> traces of the finitely many simple modules — because for a finite-dimensional **semisimple**
> `ℂ`-algebra `A ≅ ⊕ᵢ Matₙᵢ(ℂ)` the commutator subspace `[A,A] = ⊕ᵢ 𝔰𝔩ₙᵢ` has codimension exactly
> the number of simple factors.

This file proves the inequality half — the half the count needs — from Mathlib's Artin–Wedderburn
theorem over an algebraically closed field
(`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`).

## Main results

* `commSpan K A` — the commutator subspace `span_K {ab − ba}`;
* `finrank_quot_commSpan_matrix` — `dim (Matₙ(K)/[·,·]) ≤ 1`: modulo commutators every matrix is
  `tr(M)·E₀₀`, since `Eᵢⱼ = [Eᵢⱼ, Eⱼⱼ]` for `i ≠ j` and `Eᵢᵢ − Eⱼⱼ = [Eᵢⱼ, Eⱼᵢ]`;
* `finrank_quot_commSpan_pi` — `dim ((∏_{i<n} Matₙᵢ(K))/[·,·]) ≤ n`;
* `finrank_quot_commSpan_le_of_algEquiv_pi_matrix` and
  `exists_wedderburn_finrank_quot_commSpan_le` — for a finite-dimensional semisimple algebra over an
  algebraically closed field, `dim (A/[A,A]) ≤ #(Wedderburn factors)`;
* `finrank_symmetricFunctionals_le` — the dual form: the space of **symmetric linear
  functionals** on `A` has dimension at most the number of Wedderburn factors.  This is the shape
  in which a genus-one block consumes it.

## Residual

Identifying the number of Wedderburn factors with `#Irr A` (hence, through
`zhuBijective`, with `#Φ(𝒱)`) is **not** proved here; it is the remaining bookkeeping step of
DLM Lemma 10.7.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators
open Module (finrank)

/-! ## The commutator subspace -/

variable (K : Type*) [Field K] (A : Type*) [Ring A] [Algebra K A]

/-- The **commutator subspace** `[A,A] = span_K {ab − ba}` of a `K`-algebra. -/
def commSpan : Submodule K A := Submodule.span K {x : A | ∃ a b : A, x = a * b - b * a}

variable {K A}

theorem mul_sub_mul_mem_commSpan (a b : A) : a * b - b * a ∈ commSpan K A :=
  Submodule.subset_span ⟨a, b, rfl⟩

/-! ## Bounding a finrank by a spanning family -/

theorem finrank_le_of_span_range {n : ℕ} {Q : Type*} [AddCommGroup Q] [Module K Q]
    (y : Fin n → Q) (hspan : Submodule.span K (Set.range y) = ⊤) : finrank K Q ≤ n := by
  classical
  let f : (Fin n → K) →ₗ[K] Q :=
    { toFun := fun c => ∑ i, c i • y i
      map_add' := fun c d => by
        simp only [Pi.add_apply, add_smul]
        exact Finset.sum_add_distrib
      map_smul' := fun c d => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  have hrange : LinearMap.range f = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨(Pi.single i 1 : Fin n → K), ?_⟩
    show ∑ j, (Pi.single i (1 : K) : Fin n → K) j • y j = y i
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun hj => absurd (Finset.mem_univ i) hj)]
    rw [Pi.single_eq_same, one_smul]
  have h2 := Submodule.finrank_map_le f (⊤ : Submodule K (Fin n → K))
  rw [Submodule.map_top, hrange, finrank_top, finrank_top, Module.finrank_fin_fun] at h2
  exact h2

/-! ## The matrix computation -/

section Matrices

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `Eᵢⱼ = Eᵢⱼ·Eⱼⱼ − Eⱼⱼ·Eᵢⱼ` for `i ≠ j`. -/
theorem single_mem_commSpan_of_ne {i j : m} (hij : i ≠ j) :
    Matrix.single i j (1 : K) ∈ commSpan K (Matrix m m K) := by
  have h1 : Matrix.single j j (1 : K) * Matrix.single i j (1 : K) = 0 := by
    apply Matrix.single_mul_single_of_ne
    exact Ne.symm hij
  have h : Matrix.single i j (1 : K)
      = Matrix.single i j (1 : K) * Matrix.single j j (1 : K)
        - Matrix.single j j (1 : K) * Matrix.single i j (1 : K) := by
    rw [Matrix.single_mul_single_same, mul_one, h1, sub_zero]
  rw [h]
  exact mul_sub_mul_mem_commSpan _ _

/-- `Eᵢᵢ − Eⱼⱼ = Eᵢⱼ·Eⱼᵢ − Eⱼᵢ·Eᵢⱼ`. -/
theorem single_diag_sub_mem_commSpan (i j : m) :
    Matrix.single i i (1 : K) - Matrix.single j j (1 : K) ∈ commSpan K (Matrix m m K) := by
  have h : Matrix.single i i (1 : K) - Matrix.single j j (1 : K)
      = Matrix.single i j (1 : K) * Matrix.single j i (1 : K)
        - Matrix.single j i (1 : K) * Matrix.single i j (1 : K) := by
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_one]
  rw [h]
  exact mul_sub_mul_mem_commSpan _ _

omit [Fintype m] in
theorem single_eq_smul_single (i j : m) (c : K) :
    Matrix.single i j c = c • Matrix.single i j (1 : K) := by
  ext a b
  simp only [Matrix.single, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h₁ : i = a <;> by_cases h₂ : j = b <;> simp [h₁, h₂]

/-- **Modulo commutators every matrix is `tr(M)·E₀₀`.** -/
theorem sub_trace_smul_single_mem_commSpan (i₀ : m) (M : Matrix m m K) :
    M - Matrix.trace M • Matrix.single i₀ i₀ (1 : K) ∈ commSpan K (Matrix m m K) := by
  classical
  set E : Matrix m m K := Matrix.single i₀ i₀ (1 : K) with hE
  have h1 : (∑ i : m, ∑ j : m, Matrix.single i j (M i j)) = M :=
    (Matrix.matrix_eq_sum_single M).symm
  have h2 : (∑ i : m, ∑ j : m, (if i = j then (M i j) • E else 0))
      = Matrix.trace M • E := by
    rw [Matrix.trace, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp
  have hsplit : M - Matrix.trace M • E
      = ∑ i : m, ∑ j : m,
          (Matrix.single i j (M i j) - (if i = j then (M i j) • E else 0)) := by
    calc M - Matrix.trace M • E
        = (∑ i : m, ∑ j : m, Matrix.single i j (M i j))
          - (∑ i : m, ∑ j : m, (if i = j then (M i j) • E else 0)) := by rw [h1, h2]
      _ = ∑ i : m, ∑ j : m,
            (Matrix.single i j (M i j) - (if i = j then (M i j) • E else 0)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_sub_distrib]
  rw [hsplit]
  refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => ?_))
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, single_eq_smul_single, ← smul_sub]
    exact Submodule.smul_mem _ _ (single_diag_sub_mem_commSpan i i₀)
  · rw [if_neg hij, sub_zero, single_eq_smul_single]
    exact Submodule.smul_mem _ _ (single_mem_commSpan_of_ne hij)

/-- **`dim (Matₘ(K)/[·,·]) ≤ 1`.** -/
theorem finrank_quot_commSpan_matrix [Nonempty m] :
    finrank K (Matrix m m K ⧸ commSpan K (Matrix m m K)) ≤ 1 := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty m›
  refine finrank_le_one ((commSpan K (Matrix m m K)).mkQ (Matrix.single i₀ i₀ (1 : K))) ?_
  intro w
  obtain ⟨M, rfl⟩ := (commSpan K (Matrix m m K)).mkQ_surjective w
  refine ⟨Matrix.trace M, ?_⟩
  rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hmem := (commSpan K (Matrix m m K)).neg_mem (sub_trace_smul_single_mem_commSpan (K := K) i₀ M)
  rwa [neg_sub] at hmem

end Matrices

/-! ## The product of matrix algebras -/

section Pi

variable {n : ℕ} (d : Fin n → Type*) [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

/-- `Pi.single i` carries commutators to commutators. -/
theorem map_single_commSpan_le (i : Fin n) :
    (commSpan K (Matrix (d i) (d i) K)).map
        (LinearMap.single K (fun j => Matrix (d j) (d j) K) i)
      ≤ commSpan K (∀ j, Matrix (d j) (d j) K) := by
  classical
  rw [commSpan, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨x, ⟨a, b, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨Pi.single i a, Pi.single i b, ?_⟩
  show (Pi.single i (a * b - b * a) : ∀ j, Matrix (d j) (d j) K) = _
  funext j
  by_cases hj : j = i
  · subst hj; simp [Pi.single_apply]
  · simp [Pi.single_apply, hj]

variable [∀ i, Nonempty (d i)]

/-- **`dim ((∏ᵢ Mat_{dᵢ}(K)) / [·,·]) ≤ n`.** -/
theorem finrank_quot_commSpan_pi :
    finrank K ((∀ i, Matrix (d i) (d i) K) ⧸ commSpan K (∀ i, Matrix (d i) (d i) K)) ≤ n := by
  classical
  set B : Type _ := ∀ i, Matrix (d i) (d i) K with hB
  set S : Submodule K B := commSpan K B with hS
  have i₀ : ∀ i : Fin n, d i := fun i => Classical.arbitrary (d i)
  refine finrank_le_of_span_range
    (fun i : Fin n => S.mkQ (Pi.single i (Matrix.single (i₀ i) (i₀ i) (1 : K)))) ?_
  rw [eq_top_iff]
  rintro q -
  obtain ⟨M, rfl⟩ := S.mkQ_surjective q
  have hdiff : M - ∑ i : Fin n,
      (Matrix.trace (M i)) • (Pi.single i (Matrix.single (i₀ i) (i₀ i) (1 : K)) : B) ∈ S := by
    have hM : M = ∑ i : Fin n, (Pi.single i (M i) : B) := by
      funext j
      rw [Finset.sum_apply,
        Finset.sum_eq_single j
          (fun i _ hij => by simp [Pi.single_apply, Ne.symm hij])
          (fun hj => absurd (Finset.mem_univ j) hj),
        Pi.single_eq_same]
    have hterm : ∀ i : Fin n, (LinearMap.single K (fun j => Matrix (d j) (d j) K) i)
        (M i - Matrix.trace (M i) • Matrix.single (i₀ i) (i₀ i) (1 : K))
        = (Pi.single i (M i) : B)
          - (Matrix.trace (M i)) • (Pi.single i (Matrix.single (i₀ i) (i₀ i) (1 : K)) : B) := by
      intro i
      rw [map_sub, map_smul]
      rfl
    have hstep : (∑ i : Fin n, (LinearMap.single K (fun j => Matrix (d j) (d j) K) i)
          (M i - Matrix.trace (M i) • Matrix.single (i₀ i) (i₀ i) (1 : K)))
        = M - ∑ i : Fin n,
            (Matrix.trace (M i)) • (Pi.single i (Matrix.single (i₀ i) (i₀ i) (1 : K)) : B) := by
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i), Finset.sum_sub_distrib,
        ← hM]
    rw [← hstep]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact map_single_commSpan_le d i
      ⟨_, sub_trace_smul_single_mem_commSpan (K := K) (i₀ i) (M i), rfl⟩
  have hpull : ∑ i : Fin n,
      (Matrix.trace (M i)) • S.mkQ (Pi.single i (Matrix.single (i₀ i) (i₀ i) (1 : K)))
      = S.mkQ (∑ i : Fin n,
          (Matrix.trace (M i)) • (Pi.single i (Matrix.single (i₀ i) (i₀ i) (1 : K)) : B)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => (map_smul _ _ _).symm)
  have heq : S.mkQ M = ∑ i : Fin n,
      (Matrix.trace (M i)) • S.mkQ (Pi.single i (Matrix.single (i₀ i) (i₀ i) (1 : K))) := by
    rw [hpull, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hdiff
  rw [heq]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-! ### Sharpening `finrank_quot_commSpan_pi` to an EQUALITY

The `n` block traces are symmetric functionals separating the `n` generators, so the bound is
exact — which makes the "number of Wedderburn factors" an **intrinsic** invariant of the algebra,
namely `dim (A/[A,A])`. -/

/-- The `j`-th block trace of a product of matrix algebras. -/
noncomputable def piTraceMap (j : Fin n) : (∀ i, Matrix (d i) (d i) K) →ₗ[K] K :=
  (Matrix.traceLinearMap (d j) K K).comp (LinearMap.proj j)

@[simp] theorem piTraceMap_apply (j : Fin n) (M : ∀ i, Matrix (d i) (d i) K) :
    piTraceMap d j M = Matrix.trace (M j) := rfl

/-- Block traces are symmetric, so they kill the commutator subspace. -/
theorem commSpan_le_ker_piTraceMap (j : Fin n) :
    commSpan K (∀ i, Matrix (d i) (d i) K) ≤ LinearMap.ker (piTraceMap d j) := by
  rw [commSpan, Submodule.span_le]
  rintro _ ⟨a, b, rfl⟩
  change Matrix.trace ((a * b - b * a) j) = 0
  show Matrix.trace (a j * b j - b j * a j) = 0
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- **The Wedderburn count is intrinsic**: `dim ((∏ᵢ Mat_{dᵢ}(K))/[·,·]) = n` exactly. -/
theorem finrank_quot_commSpan_pi_eq :
    finrank K ((∀ i, Matrix (d i) (d i) K) ⧸ commSpan K (∀ i, Matrix (d i) (d i) K)) = n := by
  classical
  have i₀ : ∀ i : Fin n, d i := fun i => Classical.arbitrary (d i)
  haveI : FiniteDimensional K (∀ i, Matrix (d i) (d i) K) := inferInstance
  haveI : FiniteDimensional K
      ((∀ i, Matrix (d i) (d i) K) ⧸ commSpan K (∀ i, Matrix (d i) (d i) K)) := inferInstance
  have hind : LinearIndependent K (fun i : Fin n =>
      (commSpan K (∀ i, Matrix (d i) (d i) K)).mkQ
        (Pi.single i (Matrix.single (i₀ i) (i₀ i) (1 : K)))) := by
    rw [linearIndependent_iff']
    intro s c hc j hj
    have hval := congrArg
      (Submodule.liftQ _ (piTraceMap d j) (commSpan_le_ker_piTraceMap d j)) hc
    rw [map_zero, map_sum] at hval
    have hterm : ∀ i ∈ s,
        (Submodule.liftQ _ (piTraceMap d j) (commSpan_le_ker_piTraceMap d j))
            (c i • (commSpan K (∀ i, Matrix (d i) (d i) K)).mkQ
              (Pi.single i (Matrix.single (i₀ i) (i₀ i) (1 : K))))
          = if i = j then c i else 0 := by
      intro i _
      rw [map_smul]
      have hz : (Submodule.liftQ _ (piTraceMap d j) (commSpan_le_ker_piTraceMap d j))
          ((commSpan K (∀ i, Matrix (d i) (d i) K)).mkQ
            (Pi.single i (Matrix.single (i₀ i) (i₀ i) (1 : K))))
          = Matrix.trace ((Pi.single i (Matrix.single (i₀ i) (i₀ i) (1 : K))
              : ∀ i, Matrix (d i) (d i) K) j) := rfl
      rw [hz]
      by_cases hij : i = j
      · subst hij
        rw [Pi.single_eq_same, Matrix.trace_single_eq_same, if_pos rfl, smul_eq_mul, mul_one]
      · rw [Pi.single_eq_of_ne (Ne.symm hij), if_neg hij, Matrix.trace_zero, smul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s j, if_pos hj] at hval
    exact hval
  refine le_antisymm (finrank_quot_commSpan_pi (K := K) d) ?_
  simpa using hind.fintype_card_le_finrank

end Pi

/-! ## Transport along an algebra equivalence, and Artin–Wedderburn -/

section Wedderburn

variable {B : Type*} [Ring B] [Algebra K B]

theorem commSpan_map_algEquiv (e : A ≃ₐ[K] B) :
    (commSpan K A).map (e.toLinearMap) = commSpan K B := by
  rw [commSpan, commSpan, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨a, b, rfl⟩, rfl⟩
    exact ⟨e a, e b, by simp⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨e.symm a * e.symm b - e.symm b * e.symm a, ⟨_, _, rfl⟩, by simp⟩

theorem finrank_quot_commSpan_congr (e : A ≃ₐ[K] B) :
    finrank K (A ⧸ commSpan K A) = finrank K (B ⧸ commSpan K B) :=
  (Submodule.Quotient.equiv (commSpan K A) (commSpan K B) e.toLinearEquiv
    (commSpan_map_algEquiv e)).finrank_eq

/-- **The Wedderburn count.**  If `A` is isomorphic to a product of `n` matrix algebras over
`K`, then its commutator quotient has dimension at most `n`.  (For `A` semisimple over an
algebraically closed field this is the Artin–Wedderburn shape.) -/
theorem finrank_quot_commSpan_le_of_algEquiv_pi_matrix {n : ℕ} {d : Fin n → ℕ}
    (hd : ∀ i, NeZero (d i))
    (e : A ≃ₐ[K] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) K) :
    finrank K (A ⧸ commSpan K A) ≤ n := by
  haveI : ∀ i : Fin n, Nonempty (Fin (d i)) := fun i =>
    ⟨⟨0, Nat.pos_of_ne_zero (hd i).out⟩⟩
  rw [finrank_quot_commSpan_congr e]
  exact finrank_quot_commSpan_pi (K := K) (fun i => Fin (d i))

/-- **The Wedderburn factor count is INTRINSIC**: it equals `dim (A/[A,A])`, so it does not
depend on the chosen decomposition. -/
theorem finrank_quot_commSpan_eq_of_algEquiv_pi_matrix {n : ℕ} {d : Fin n → ℕ}
    (hd : ∀ i, NeZero (d i))
    (e : A ≃ₐ[K] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) K) :
    finrank K (A ⧸ commSpan K A) = n := by
  haveI : ∀ i : Fin n, Nonempty (Fin (d i)) := fun i =>
    ⟨⟨0, Nat.pos_of_ne_zero (hd i).out⟩⟩
  rw [finrank_quot_commSpan_congr e]
  exact finrank_quot_commSpan_pi_eq (K := K) (fun i => Fin (d i))

/-- **Artin–Wedderburn form**: a finite-dimensional semisimple algebra over an algebraically
closed field has `dim (A/[A,A]) ≤ #(Wedderburn factors)`. -/
theorem exists_wedderburn_finrank_quot_commSpan_le [IsAlgClosed K] [IsSemisimpleRing A]
    [FiniteDimensional K A] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (A ≃ₐ[K] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) K) ∧
      finrank K (A ⧸ commSpan K A) ≤ n := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K A
  exact ⟨n, d, hd, ⟨e⟩, finrank_quot_commSpan_le_of_algEquiv_pi_matrix hd e⟩

end Wedderburn

/-! ## The dual form: symmetric linear functionals

This is the shape in which a genus-one block consumes the count: a block restricts to a linear
functional `φ` on `A(𝒱)` with `φ(ab) = φ(ba)`. -/

section Symmetric

variable (K A)

/-- The **symmetric (trace) linear functionals** on `A`. -/
def symmetricFunctionals : Submodule K (A →ₗ[K] K) where
  carrier := {φ : A →ₗ[K] K | ∀ a b : A, φ (a * b) = φ (b * a)}
  add_mem' := fun {φ ψ} hφ hψ a b => by
    change φ (a * b) + ψ (a * b) = φ (b * a) + ψ (b * a)
    rw [hφ a b, hψ a b]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c φ hφ a b => by
    change c * φ (a * b) = c * φ (b * a)
    rw [hφ a b]

variable {K A}

@[simp] theorem mem_symmetricFunctionals {φ : A →ₗ[K] K} :
    φ ∈ symmetricFunctionals K A ↔ ∀ a b : A, φ (a * b) = φ (b * a) := Iff.rfl

/-- A functional is symmetric exactly when it kills the commutator subspace. -/
theorem commSpan_le_ker_of_symmetric {φ : A →ₗ[K] K} (hφ : φ ∈ symmetricFunctionals K A) :
    commSpan K A ≤ LinearMap.ker φ := by
  rw [commSpan, Submodule.span_le]
  rintro _ ⟨a, b, rfl⟩
  change φ (a * b - b * a) = 0
  rw [map_sub, hφ a b, sub_self]

/-- The tautological injection of the symmetric functionals into the dual of the commutator
quotient. -/
noncomputable def symmetricLift :
    symmetricFunctionals K A →ₗ[K] Module.Dual K (A ⧸ commSpan K A) where
  toFun φ := Submodule.liftQ _ φ.1 (commSpan_le_ker_of_symmetric φ.2)
  map_add' φ ψ := by
    refine LinearMap.ext (fun q => ?_)
    obtain ⟨x, rfl⟩ := (commSpan K A).mkQ_surjective q
    rfl
  map_smul' c φ := by
    refine LinearMap.ext (fun q => ?_)
    obtain ⟨x, rfl⟩ := (commSpan K A).mkQ_surjective q
    rfl

theorem symmetricLift_injective :
    Function.Injective (symmetricLift : symmetricFunctionals K A →ₗ[K] _) := by
  intro φ ψ hφψ
  refine Subtype.ext (LinearMap.ext (fun x => ?_))
  have := congrArg (fun f => f ((commSpan K A).mkQ x)) hφψ
  exact this

/-- **The dimension bound in dual form**: the symmetric functionals on a finite-dimensional
semisimple algebra over an algebraically closed field span a space of dimension at most the number
of Wedderburn factors — DLM Lemma 10.7's linear-algebra core. -/
theorem finrank_symmetricFunctionals_le_of_algEquiv_pi_matrix [FiniteDimensional K A] {n : ℕ}
    {d : Fin n → ℕ} (hd : ∀ i, NeZero (d i))
    (e : A ≃ₐ[K] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) K) :
    finrank K (symmetricFunctionals K A) ≤ n := by
  haveI : FiniteDimensional K (A ⧸ commSpan K A) := inferInstance
  have hinj := LinearMap.finrank_le_finrank_of_injective
    (f := (symmetricLift : symmetricFunctionals K A →ₗ[K] _)) symmetricLift_injective
  refine hinj.trans ?_
  rw [Subspace.dual_finrank_eq]
  exact finrank_quot_commSpan_le_of_algEquiv_pi_matrix hd e

/-- The Artin–Wedderburn form of the same. -/
theorem exists_finrank_symmetricFunctionals_le [IsAlgClosed K] [IsSemisimpleRing A]
    [FiniteDimensional K A] :
    ∃ n : ℕ, (∃ d : Fin n → ℕ, (∀ i, NeZero (d i)) ∧
      Nonempty (A ≃ₐ[K] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) K)) ∧
      finrank K (symmetricFunctionals K A) ≤ n := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K A
  exact ⟨n, ⟨d, hd, ⟨e⟩⟩, finrank_symmetricFunctionals_le_of_algEquiv_pi_matrix hd e⟩

end Symmetric

end VOA
