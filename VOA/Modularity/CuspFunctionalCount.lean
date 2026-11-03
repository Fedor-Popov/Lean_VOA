/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockZeroMode
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Zhu's Theorem 5.3.3 at the cusp: `dim ≤ #(Wedderburn factors of A(𝒱))`

Assembling `Modularity.BlockZeroMode` (a functional killing `O(𝒱)` and every `a[0]v` is symmetric
for the Zhu product) with `Modularity.SemisimpleTrace` (a finite-dimensional semisimple `ℂ`-algebra
has at most `#(Wedderburn factors)` independent symmetric functionals) gives the **entire counting
half of Zhu's Theorem 5.3.3, at the `q → 0` fibre**:

  `dim_ℂ { φ : 𝒱 →ₗ ℂ | φ(O(𝒱)) = 0, φ(a[0]v) = 0 } ≤ #(Wedderburn factors of A(𝒱))`.

Dong–Li–Mason's Lemma 9.2(c) identifies the `q → 0` limit of Zhu's second block-condition family
with `a ∘ b`, i.e. with `O(𝒱)`; so `cuspFunctionals W` **is** the `q = 0` fibre of the genus-one
block conditions, and the theorem below is Zhu 5.3.3 for that fibre.

## What this does and does not give

It does **not** give `dim 𝔅 ≤ #Φ(𝒱)` at a fixed `z₀ ∈ ℍ`: `blockRelSpan W z₀` genuinely *moves*
with `z₀` and is not `O(𝒱) + [A(𝒱),A(𝒱)]`.  Passing from the cusp fibre to a general fibre is
the flatness statement — Zhu §4.4
Lemmas 4.4.1–4.4.2 plus Nakayama — which is the honest remaining residual.

## Main results

* `cuspFunctionals W` — the submodule of functionals killing `O(𝒱)` and every `a[0]v`;
* `finrank_cuspFunctionals_le_of_algEquiv_pi_matrix`, `exists_finrank_cuspFunctionals_le`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Carried hypotheses, all genuine hypotheses of Zhu's
theorem: `VacuumGradeZero` (`𝒱₀ ⊆ ℂ𝟙`), finite-dimensionality of `A(𝒱)` (from `C₂`-cofiniteness),
and semisimplicity of `A(𝒱)` (from rationality — **false** without it: the triplet `W_{1,p}` is
`C₂`-cofinite with `#Irr = 2p` but a `(3p−1)`-dimensional space of one-point functions).
-/

namespace VOA

open scoped BigOperators
open Module (finrank)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section Cusp

variable (W : VertexOperatorAlgebra 𝒱)

/-- The **cusp fibre of the genus-one block conditions**: linear functionals on `𝒱` killing
`O(𝒱)` (the `q → 0` limit of Zhu's `[−2]`-family, DLM Lemma 9.2(c)) and every square-bracket zero
mode `a[0]v` (block condition (i)). -/
def cuspFunctionals : Submodule ℂ (𝒱 →ₗ[ℂ] ℂ) where
  carrier := {φ : 𝒱 →ₗ[ℂ] ℂ |
    (∀ x ∈ O W, φ x = 0) ∧
      ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : 𝒱, φ (vSqZ W a ka 0 v) = 0}
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨fun x hx => by change φ x + ψ x = 0; rw [hφ.1 x hx, hψ.1 x hx, add_zero],
     fun ka hka a ha v => by
       change φ _ + ψ _ = 0
       rw [hφ.2 ka hka a ha v, hψ.2 ka hka a ha v, add_zero]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  smul_mem' := fun c φ hφ =>
    ⟨fun x hx => by change c * φ x = 0; rw [hφ.1 x hx, mul_zero],
     fun ka hka a ha v => by
       change c * φ _ = 0
       rw [hφ.2 ka hka a ha v, mul_zero]⟩

variable {W}

theorem mem_cuspFunctionals {φ : 𝒱 →ₗ[ℂ] ℂ} :
    φ ∈ cuspFunctionals W ↔
      (∀ x ∈ O W, φ x = 0) ∧
        ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : 𝒱, φ (vSqZ W a ka 0 v) = 0 :=
  Iff.rfl

theorem O_le_ker_of_mem_cuspFunctionals {φ : 𝒱 →ₗ[ℂ] ℂ} (hφ : φ ∈ cuspFunctionals W) :
    O W ≤ LinearMap.ker φ := fun x hx => hφ.1 x hx

/-- **The embedding of the cusp fibre into the symmetric functionals on `A(𝒱)`.** -/
noncomputable def cuspLift (hzero : VacuumGradeZero W) :
    letI := instRingA W
    letI := instAlgebraA W
    cuspFunctionals W →ₗ[ℂ] symmetricFunctionals ℂ (A W) :=
  letI := instRingA W
  letI := instAlgebraA W
  { toFun := fun φ =>
      ⟨Submodule.liftQ (O W) φ.1 (O_le_ker_of_mem_cuspFunctionals φ.2),
        symmetricFunctional_of_zeroModeVanishing hzero
          (O_le_ker_of_mem_cuspFunctionals φ.2) φ.2.2⟩
    map_add' := fun φ ψ => by
      refine Subtype.ext (LinearMap.ext (fun q => ?_))
      obtain ⟨x, rfl⟩ := (O W).mkQ_surjective q
      rfl
    map_smul' := fun c φ => by
      refine Subtype.ext (LinearMap.ext (fun q => ?_))
      obtain ⟨x, rfl⟩ := (O W).mkQ_surjective q
      rfl }

theorem cuspLift_injective :
    letI := instRingA W
    letI := instAlgebraA W
    Function.Injective (cuspLift (vacuumGradeZero_holds W)) := by
  letI := instRingA W
  letI := instAlgebraA W
  intro φ ψ hφψ
  refine Subtype.ext (LinearMap.ext (fun x => ?_))
  have h := congrArg (fun f => (f : A W →ₗ[ℂ] ℂ) ((O W).mkQ x)) (Subtype.ext_iff.mp hφψ)
  exact h

/-- **Zhu's Theorem 5.3.3 at the cusp** (the `q = 0` fibre), from an explicit Artin–Wedderburn
decomposition of `A(𝒱)`. -/
theorem finrank_cuspFunctionals_le_of_algEquiv_pi_matrix
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    {n : ℕ} {d : Fin n → ℕ} (hd : ∀ i, NeZero (d i))
    (e : letI := instRingA W; letI := instAlgebraA W;
      A W ≃ₐ[ℂ] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    finrank ℂ (cuspFunctionals W) ≤ n := by
  have hzero : VacuumGradeZero W := vacuumGradeZero_holds W
  letI := instRingA W
  letI := instAlgebraA W
  haveI := hfd
  refine le_trans ?_ (finrank_symmetricFunctionals_le_of_algEquiv_pi_matrix hd e)
  exact LinearMap.finrank_le_finrank_of_injective (f := cuspLift hzero) (cuspLift_injective)

/-- **Zhu's Theorem 5.3.3 at the cusp**, in Artin–Wedderburn form: for a finite-dimensional
**semisimple** `A(𝒱)`, the cusp fibre of the block conditions has dimension at most the number of
simple factors. -/
theorem exists_finrank_cuspFunctionals_le
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    (hss : letI := instRingA W; IsSemisimpleRing (A W)) :
    ∃ n : ℕ,
      (letI := instRingA W; letI := instAlgebraA W;
        ∃ d : Fin n → ℕ, (∀ i, NeZero (d i)) ∧
          Nonempty (A W ≃ₐ[ℂ] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ))
      ∧ finrank ℂ (cuspFunctionals W) ≤ n := by
  letI := instRingA W
  letI := instAlgebraA W
  haveI := hfd
  haveI := hss
  obtain ⟨n, d, hdz, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (A W)
  exact ⟨n, ⟨d, hdz, ⟨e⟩⟩,
    finrank_cuspFunctionals_le_of_algEquiv_pi_matrix hfd hdz e⟩

/-! ## The quotient form: the cusp fibre **is** `A(𝒱)/[A(𝒱),A(𝒱)]` -/

section Quotient

variable (W)

/-- The **cusp relation space** `O(𝒱) + span{a[0]v}` — the `q → 0` limit of `blockRelSpan W z₀`
(DLM Lemma 9.2(c) turns the `[−2]`-family into `a ∘ b`, i.e. into `O(𝒱)`). -/
def cuspRelSpan : Submodule ℂ 𝒱 :=
  O W ⊔ Submodule.span ℂ
    {x : 𝒱 | ∃ (ka : ℕ) (a v : 𝒱), 1 ≤ ka ∧ a ∈ W.grading (ka : ℤ) ∧ x = vSqZ W a ka 0 v}

variable {W}

/-- `a[0]v` lies in the cusp relation space. -/
theorem vSqZ_zero_mem_cuspRelSpan {ka : ℕ} (hka : 1 ≤ ka) {a : 𝒱}
    (ha : a ∈ W.grading (ka : ℤ)) (v : 𝒱) : vSqZ W a ka 0 v ∈ cuspRelSpan W :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨ka, a, v, hka, ha, rfl⟩)

theorem O_le_cuspRelSpan : O W ≤ cuspRelSpan W := le_sup_left

/-- **Every Zhu commutator lies in the cusp relation space** — the `⊇` half of the
identification with `[A(𝒱),A(𝒱)]`. -/
theorem zhuMul_sub_mem_cuspRelSpan (u v : 𝒱) :
    zhuMul W u v - zhuMul W v u ∈ cuspRelSpan W := by
  have hzero : VacuumGradeZero W := vacuumGradeZero_holds W
  refine reduce_homogeneous W
    (P := fun u => zhuMul W u v - zhuMul W v u ∈ cuspRelSpan W) ?_ ?_ ?_ u
  · intro k a ha
    rcases lt_trichotomy k 0 with hk | hk | hk
    · have h0 : a = 0 := by
        rw [W.positivity k hk] at ha
        simpa using ha
      subst h0
      simpa using (cuspRelSpan W).zero_mem
    · subst hk
      rw [zhuMul_comm_of_mem_span_vacuum (hzero ha) v, sub_self]
      exact (cuspRelSpan W).zero_mem
    · have hka : 1 ≤ k.toNat := by omega
      have hak : a ∈ W.grading ((k.toNat : ℕ) : ℤ) := by
        rwa [show ((k.toNat : ℕ) : ℤ) = k from by omega]
      have hsplit : zhuMul W a v - zhuMul W v a
          = (zhuMul W a v - zhuMul W v a - vSqZ W a k.toNat 0 v) + vSqZ W a k.toNat 0 v := by
        abel
      rw [hsplit]
      exact (cuspRelSpan W).add_mem
        (O_le_cuspRelSpan (zhuCommutatorLaw_holds W k.toNat hka a hak v))
        (vSqZ_zero_mem_cuspRelSpan hka hak v)
  · simpa using (cuspRelSpan W).zero_mem
  · intro x y hx hy
    have hrw : zhuMul W (x + y) v - zhuMul W v (x + y)
        = (zhuMul W x v - zhuMul W v x) + (zhuMul W y v - zhuMul W v y) := by
      rw [zhuMul_add_left, zhuMul_add_right]; abel
    rw [hrw]
    exact (cuspRelSpan W).add_mem hx hy

/-- `mk W` sends `a[0]v` to the Lie bracket of `A(𝒱)`. -/
theorem mk_vSqZ_zero_eq_lie {ka : ℕ} (hka : 1 ≤ ka) {a : 𝒱} (ha : a ∈ W.grading (ka : ℤ))
    (v : 𝒱) :
    letI := instRingA W
    mk W (vSqZ W a ka 0 v) = mk W a * mk W v - mk W v * mk W a := by
  letI := instRingA W
  have hmem := zhuCommutatorLaw_holds W ka hka a ha v
  have h0 : mk W (zhuMul W a v - zhuMul W v a - vSqZ W a ka 0 v) = 0 := by
    rw [mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  rw [map_sub, map_sub, sub_eq_zero] at h0
  rw [← h0, AsRing_mul_eq, AsRing_mul_eq, Amul_mk, Amul_mk, ← map_sub]

/-- **The cusp fibre IS the commutator quotient of Zhu's algebra**:
`𝒱 ⧸ (O(𝒱) + span{a[0]v})  ≃  A(𝒱) ⧸ [A(𝒱),A(𝒱)]`. -/
theorem map_mk_cuspRelSpan :
    letI := instRingA W
    letI := instAlgebraA W
    Submodule.map (mk W) (cuspRelSpan W) = commSpan ℂ (A W) := by
  letI := instRingA W
  letI := instAlgebraA W
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    refine sup_le (fun y hy => ?_) ?_
    · change mk W y ∈ commSpan ℂ (A W)
      have hy0 : mk W y = 0 := by
        rw [mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hy
      rw [hy0]
      exact (commSpan ℂ (A W)).zero_mem
    · rw [Submodule.span_le]
      rintro _ ⟨ka, a, v, hka, ha, rfl⟩
      change mk W (vSqZ W a ka 0 v) ∈ commSpan ℂ (A W)
      rw [mk_vSqZ_zero_eq_lie hka ha v]
      exact mul_sub_mul_mem_commSpan _ _
  · rw [commSpan, Submodule.span_le]
    rintro _ ⟨p, q, rfl⟩
    obtain ⟨x, rfl⟩ := mk_surjective W p
    obtain ⟨y, rfl⟩ := mk_surjective W q
    refine ⟨zhuMul W x y - zhuMul W y x, zhuMul_sub_mem_cuspRelSpan x y, ?_⟩
    rw [map_sub, ← Amul_mk, ← Amul_mk, ← AsRing_mul_eq, ← AsRing_mul_eq]

/-- **The cusp fibre, as a linear equivalence**:
`𝒱 ⧸ (O(𝒱) + span{a[0]v}) ≃ₗ A(𝒱) ⧸ [A(𝒱),A(𝒱)]`, unconditionally in `VacuumGradeZero`. -/
noncomputable def cuspRelSpanQuotEquiv (hzero : VacuumGradeZero W) :
    letI := instRingA W
    letI := instAlgebraA W
    (𝒱 ⧸ cuspRelSpan W) ≃ₗ[ℂ] A W ⧸ commSpan ℂ (A W) := by
  letI := instRingA W
  letI := instAlgebraA W
  have hker : cuspRelSpan W ≤ LinearMap.ker ((commSpan ℂ (A W)).mkQ.comp (mk W)) := by
    intro x hx
    change (commSpan ℂ (A W)).mkQ (mk W x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← map_mk_cuspRelSpan]
    exact ⟨x, hx, rfl⟩
  refine LinearEquiv.ofBijective
    (Submodule.liftQ _ ((commSpan ℂ (A W)).mkQ.comp (mk W)) hker) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot] at *
    rw [Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := (cuspRelSpan W).mkQ_surjective q
    have hx : (commSpan ℂ (A W)).mkQ (mk W x) = 0 := hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← map_mk_cuspRelSpan] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hdiff : x - y ∈ O W := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← mk, map_sub, hxy, sub_self]
    have hxmem : x ∈ cuspRelSpan W := by
      have := (cuspRelSpan W).add_mem (O_le_cuspRelSpan hdiff) hy
      simpa using this
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hxmem
  · intro q
    obtain ⟨p, rfl⟩ := (commSpan ℂ (A W)).mkQ_surjective q
    obtain ⟨x, rfl⟩ := mk_surjective W p
    exact ⟨(cuspRelSpan W).mkQ x, rfl⟩

/-- **The cusp fibre has the INTRINSIC dimension `dim A(𝒱)/[A(𝒱),A(𝒱)]`** — no
semisimplicity, no choice of Wedderburn decomposition. -/
theorem finrank_quot_cuspRelSpan_eq :
    letI := instRingA W
    letI := instAlgebraA W
    finrank ℂ (𝒱 ⧸ cuspRelSpan W) = finrank ℂ (A W ⧸ commSpan ℂ (A W)) :=
  have hzero : VacuumGradeZero W := vacuumGradeZero_holds W
  (cuspRelSpanQuotEquiv hzero).finrank_eq

/-- **Zhu's Theorem 5.3.3 at the cusp, quotient form** — the exact analogue of the open
target `dim (𝒱 ⧸ blockRelSpan z₀) ≤ #Φ(𝒱)`, at `q = 0`. -/
theorem finrank_quot_cuspRelSpan_le_of_algEquiv_pi_matrix
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    {n : ℕ} {d : Fin n → ℕ} (hd : ∀ i, NeZero (d i))
    (e : letI := instRingA W; letI := instAlgebraA W;
      A W ≃ₐ[ℂ] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    finrank ℂ (𝒱 ⧸ cuspRelSpan W) ≤ n := by
  letI := instRingA W
  letI := instAlgebraA W
  haveI := hfd
  rw [finrank_quot_cuspRelSpan_eq]
  exact finrank_quot_commSpan_le_of_algEquiv_pi_matrix hd e

/-- **Equality, not just a bound**: the cusp fibre has dimension **exactly** the number of
Wedderburn factors of `A(𝒱)`.  (For a rational `𝒱` that number is `#Irr A(𝒱) = #Φ(𝒱)`.) -/
theorem finrank_quot_cuspRelSpan_eq_of_algEquiv_pi_matrix
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    {n : ℕ} {d : Fin n → ℕ} (hd : ∀ i, NeZero (d i))
    (e : letI := instRingA W; letI := instAlgebraA W;
      A W ≃ₐ[ℂ] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    finrank ℂ (𝒱 ⧸ cuspRelSpan W) = n := by
  letI := instRingA W
  letI := instAlgebraA W
  haveI := hfd
  rw [finrank_quot_cuspRelSpan_eq]
  exact finrank_quot_commSpan_eq_of_algEquiv_pi_matrix hd e

/-- Artin–Wedderburn form of the quotient statement. -/
theorem exists_finrank_quot_cuspRelSpan_le
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    (hss : letI := instRingA W; IsSemisimpleRing (A W)) :
    ∃ n : ℕ,
      (letI := instRingA W; letI := instAlgebraA W;
        ∃ d : Fin n → ℕ, (∀ i, NeZero (d i)) ∧
          Nonempty (A W ≃ₐ[ℂ] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) ℂ))
      ∧ finrank ℂ (𝒱 ⧸ cuspRelSpan W) ≤ n := by
  letI := instRingA W
  letI := instAlgebraA W
  haveI := hfd
  haveI := hss
  obtain ⟨n, d, hdz, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (A W)
  exact ⟨n, ⟨d, hdz, ⟨e⟩⟩, finrank_quot_cuspRelSpan_le_of_algEquiv_pi_matrix hfd hdz e⟩

end Quotient

end Cusp

end VOA
