/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDE
import VOA.Modularity.AKModularODE

/-!
# From one weight-four trace identity to the AK recurrence (formal, type-generic)

Let `S(v) = tr_V o(v) q^{L₀ - c/24}` be the torus one-point function of the adjoint module and
`f = S(|0⟩)` the normalised character.  Zhu's `ω`-recursion (`zhuRecursion_omega`, proved in the
repository) and the exact Virasoro tower over the vacuum (`Lsq_tower`) give, with no hypothesis,

  `S(L[-2]²|0⟩) = θ²f + G₂ ⋆ (2 θf) + G₄ ⋆ ((c/2) f)`     (`torusOnePoint_Lsq_sq_vacuum`),

with Zhu's pinned Eisenstein family `G₂ = -E₂/12`, `G₄ = E₄/720`.  So the second-order AK MLDE is
equivalent to the single **weight-four trace identity**

  `VacuumQuarticRelation W κ :  S(L[-2]²|0⟩) = κ · G₄ ⋆ f`.

`isAKSolution_of_vacuumQuarticRelation`: if `c = -2(h+1)` and the identity holds with
`κ = (h+1)(5h-6)`, then the graded dimensions `dim V_N` solve the AK recurrence with `h`; hence
(`DeligneMLDE`) `dim V_N = mldeCoeff h N` and the `TargetLowerBoundQ W (mldeCoeff h)` holds.

Everything is formal: the coefficients are compared at `q^{N - c/24}`, no convergence, no
modularity and no Ramanujan identity is used.  The constant `κ` is forced: it is the value that
makes the indicial equation at `N = 0` hold with exponent `-c/24`.

`vacuumQuarticRelation_of_sqC2` reduces the trace identity further to a purely algebraic
statement inside `V`: `L[-2]²|0⟩` is a finite sum of square-bracket `C₂`-type terms `a[-2]b`
(with `a[2]b ∈ ℂ|0⟩`, `a[2m]b = 0` for `m ≥ 2`), plus `a[0]`-brackets and an `L[-1]`-derivative.
This is the form in which AK §7 derive the MLDE for the Deligne series (from `ω̄² = 0` in `R_V`).
-/

namespace VOA.DeligneAudit.DeligneMLDE

open VOA DeligneCharacter

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section Tower

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- `S(L[-2]|0⟩) = θ f`. -/
theorem torusOnePoint_Lsq_vacuum (N : OrdVModule W M) :
    torusOnePoint N (Lsq W (-2) W.vacuum) = qDeriv (torusPartition N) := by
  rw [zhuRecursion_omega N W.vacuum, torusOnePoint_vacuum]
  have h0 : ∀ m : ℕ, qConv (zhuG (m + 1))
      (torusOnePoint N (Lsq W (2 * (m + 1) - 2 : ℤ) W.vacuum)) = 0 := by
    intro m
    rw [Lsq_vacuum_eq_zero W (by omega), torusOnePoint_zero, qConv_zero_right]
  simp only [h0, finsum_zero, add_zero]

/-- **`S(L[-2]²|0⟩) = θ²f + G₂ ⋆ (2θf) + G₄ ⋆ ((c/2) f)`**, unconditionally. -/
theorem torusOnePoint_Lsq_sq_vacuum (N : OrdVModule W M) :
    torusOnePoint N (Lsq W (-2) (Lsq W (-2) W.vacuum))
      = qDeriv (qDeriv (torusPartition N))
        + (qConv (zhuG 1) ((2 : ℂ) • qDeriv (torusPartition N))
          + qConv (zhuG 2) ((W.centralCharge / 2) • torusPartition N)) := by
  have htow := Lsq_tower W (vacuum_isSqPrimary W) 1
  simp only [Function.iterate_one] at htow
  rw [zhuRecursion_omega N, torusOnePoint_Lsq_vacuum]
  congr 1
  set F : ℕ → FormalQSeries := fun m => qConv (zhuG (m + 1))
      (torusOnePoint N (Lsq W (2 * (m + 1) - 2 : ℤ) (Lsq W (-2) W.vacuum))) with hF
  have hidx : ∀ m : ℕ, (2 * ((m : ℤ) + 1) - 2) = 2 * (m : ℤ) := fun m => by ring
  have hF0 : F 0 = qConv (zhuG 1) ((2 : ℂ) • qDeriv (torusPartition N)) := by
    simp only [hF, hidx, Nat.cast_zero, mul_zero, zero_add]
    have h := htow 0
    rw [towerScalar_zero_left] at h
    simp only [Nat.cast_zero, mul_zero, Nat.sub_zero, Function.iterate_one] at h
    rw [h, torusOnePoint_smul, torusOnePoint_Lsq_vacuum]
    norm_num
  have hF1 : F 1 = qConv (zhuG 2) ((W.centralCharge / 2) • torusPartition N) := by
    simp only [hF, hidx, Nat.cast_one, mul_one, Nat.reduceAdd]
    have h := htow 1
    rw [towerScalar_one_one] at h
    simp only [Nat.cast_one, mul_one, Nat.sub_self, Function.iterate_zero, id] at h
    rw [h, torusOnePoint_smul, torusOnePoint_vacuum]
    norm_num
  have hF2 : ∀ m, 2 ≤ m → F m = 0 := by
    intro m hm
    simp only [hF, hidx]
    have h := htow m
    rw [towerScalar_eq_zero_of_lt _ _ (by omega : 1 < m), zero_smul] at h
    rw [h, torusOnePoint_zero, qConv_zero_right]
  change ∑ᶠ m : ℕ, F m = _
  rw [finsum_eq_sum_of_support_subset F (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_one, hF0, hF1]
  · intro m hm
    simp only [Function.mem_support] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hm (hF2 m (by omega))

end Tower

/-! ## The weight-four trace identity -/

/-- **The weight-four trace identity** `S(L[-2]²|0⟩) = κ · G₄ ⋆ S(|0⟩)` on the adjoint module.
For the Deligne series this is AK's second-order MLDE (with `κ = (h∨+1)(5h∨-6)`). -/
structure VacuumQuarticRelation (W : VertexOperatorAlgebra 𝒱) (κ : ℂ) : Prop where
  eq : torusOnePoint (adjointModule W) (Lsq W (-2) (Lsq W (-2) W.vacuum))
    = κ • qConv (zhuG 2) (torusPartition (adjointModule W))

section Coefficients

variable (W : VertexOperatorAlgebra 𝒱)

/-- The adjoint graded dimension at `q^{n - c/24}` is `dim V_n`. -/
theorem torusPartition_adjoint (n : ℤ) :
    torusPartition (adjointModule W) ((n : ℂ) - W.centralCharge / 24)
      = (Module.finrank ℂ (W.grading n) : ℂ) := by
  rw [torusPartition, gradedDim,
    show (n : ℂ) - W.centralCharge / 24 + W.centralCharge / 24 = (n : ℂ) from by ring]
  change (Module.finrank ℂ (adjWeight W (n : ℂ)) : ℂ) = _
  rw [adjWeight_cast]

theorem torusPartition_adjoint_sub (N m : ℕ) :
    torusPartition (adjointModule W) ((N : ℂ) - W.centralCharge / 24 - m)
      = if m ≤ N then (Module.finrank ℂ (W.grading ((N - m : ℕ) : ℤ)) : ℂ) else 0 := by
  split_ifs with hm
  · rw [← torusPartition_adjoint]
    congr 1
    push_cast [Nat.cast_sub hm]
    ring
  · have h := torusPartition_adjoint W ((N : ℤ) - m)
    rw [W.positivity _ (by omega), finrank_bot, Nat.cast_zero] at h
    rw [← h]
    congr 1
    push_cast
    ring

/-- Evaluating a convolution against a series supported in exponents `≥ -c/24`. -/
theorem qConv_eval (g : ℕ → ℂ) (φ : FormalQSeries) (e : ℂ) (N : ℕ)
    (hφ : ∀ m : ℕ, N < m → φ (e - m) = 0) :
    qConv g φ e = ∑ m ∈ Finset.range (N + 1), g m * φ (e - m) := by
  unfold qConv
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (N + 1))]
  intro m hm
  simp only [Function.mem_support] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hm (by rw [hφ m (by omega), mul_zero])

theorem zhuG_one_zero' : zhuG 1 0 = -(1 / 12 : ℂ) := by
  norm_num [zhuG_zero, bernoulli_two]

theorem zhuG_two_zero : zhuG 2 0 = (1 / 720 : ℂ) := by
  rw [zhuG_zero, show 2 * 2 = 4 from rfl,
    bernoulli_eq_bernoulli'_of_ne_one (by norm_num : (4 : ℕ) ≠ 1), bernoulli'_four]
  norm_num [Nat.factorial]

theorem zhuG_one_succ (r : ℕ) : zhuG 1 (r + 1) = 2 * (sigmaK 1 (r + 1) : ℂ) := by
  rw [zhuG_of_ne_zero 1 (Nat.succ_ne_zero r), lambertCoeff_eq_sigma, ArithmeticFunction.sigma_apply]
  simp [sigmaK]

theorem zhuG_two_succ (r : ℕ) : zhuG 2 (r + 1) = (sigmaK 3 (r + 1) : ℂ) / 3 := by
  rw [zhuG_of_ne_zero 2 (Nat.succ_ne_zero r), lambertCoeff_eq_sigma, ArithmeticFunction.sigma_apply]
  simp [sigmaK, Nat.factorial]
  ring

/-- **The formal second-order MLDE** for the adjoint character `f`, in Zhu's normalisation:
`θ²f + G₂ ⋆ (2θf) + G₄ ⋆ ((c/2) f) = κ · G₄ ⋆ f`. -/
def FormalMLDE (κ : ℂ) : Prop :=
  qDeriv (qDeriv (torusPartition (adjointModule W)))
      + (qConv (zhuG 1) ((2 : ℂ) • qDeriv (torusPartition (adjointModule W)))
        + qConv (zhuG 2) ((W.centralCharge / 2) • torusPartition (adjointModule W)))
    = κ • qConv (zhuG 2) (torusPartition (adjointModule W))

/-- The formal MLDE at `q^{N - c/24}`, with the `r = 0` terms split off. -/
theorem formalMLDE_coeff {κ : ℂ} (hE : FormalMLDE W κ) (N : ℕ) :
    ((N : ℂ) - W.centralCharge / 24) * (((N : ℂ) - W.centralCharge / 24)
        * (Module.finrank ℂ (W.grading ((N : ℕ) : ℤ)) : ℂ))
      + ((∑ k ∈ Finset.range N, zhuG 1 (k + 1) * (2 * ((((N : ℂ) - W.centralCharge / 24)
            - ((k + 1 : ℕ) : ℂ)) * torusPartition (adjointModule W)
              (((N : ℂ) - W.centralCharge / 24) - ((k + 1 : ℕ) : ℂ)))))
          + -(1 / 12) * (2 * (((N : ℂ) - W.centralCharge / 24)
            * (Module.finrank ℂ (W.grading ((N : ℕ) : ℤ)) : ℂ)))
        + ((∑ k ∈ Finset.range N, zhuG 2 (k + 1) * (W.centralCharge / 2
            * torusPartition (adjointModule W) (((N : ℂ) - W.centralCharge / 24) - ((k + 1 : ℕ) : ℂ))))
          + 1 / 720 * (W.centralCharge / 2 * (Module.finrank ℂ (W.grading ((N : ℕ) : ℤ)) : ℂ))))
      = κ * ((∑ k ∈ Finset.range N, zhuG 2 (k + 1)
            * torusPartition (adjointModule W) (((N : ℂ) - W.centralCharge / 24) - ((k + 1 : ℕ) : ℂ)))
          + 1 / 720 * (Module.finrank ℂ (W.grading ((N : ℕ) : ℤ)) : ℂ)) := by
  set f := torusPartition (adjointModule W) with hf
  have hfe : ∀ (N m : ℕ), f ((N : ℂ) - W.centralCharge / 24 - m)
      = if m ≤ N then (Module.finrank ℂ (W.grading ((N - m : ℕ) : ℤ)) : ℂ) else 0 :=
    fun N m => torusPartition_adjoint_sub W N m
  have hE' := congrFun hE ((N : ℂ) - W.centralCharge / 24)
  set e : ℂ := (N : ℂ) - W.centralCharge / 24 with he
  have hvan : ∀ m : ℕ, N < m → f (e - m) = 0 := fun m hm => by
    rw [hfe, if_neg (by omega)]
  have hvan' : ∀ m : ℕ, N < m → ((2 : ℂ) • qDeriv f) (e - m) = 0 := fun m hm => by
    simp only [Pi.smul_apply, qDeriv, hvan m hm, mul_zero, smul_zero]
  have hvan'' : ∀ m : ℕ, N < m → ((W.centralCharge / 2) • f) (e - m) = 0 := fun m hm => by
    simp only [Pi.smul_apply, hvan m hm, smul_zero]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hE'
  rw [qConv_eval _ _ e N hvan', qConv_eval _ _ e N hvan'', qConv_eval _ _ e N hvan] at hE'
  simp only [Pi.smul_apply, smul_eq_mul, qDeriv] at hE'
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ'] at hE'
  simp only [Nat.cast_zero, sub_zero, zhuG_one_zero', zhuG_two_zero] at hE'
  have hf0 : f e = (Module.finrank ℂ (W.grading ((N : ℕ) : ℤ)) : ℂ) := by
    have := hfe N 0
    simpa [he] using this
  rw [← hf, hf0] at hE'
  exact hE'

/-- **The constant is forced.**  The indicial equation (`N = 0`) of the formal MLDE determines `κ`:
with `c = -2(h+1)` and `|0⟩ ≠ 0`, necessarily `κ = (h+1)(5h-6)`. -/
theorem kappa_eq_of_formalMLDE (h : ℕ) (hc : W.centralCharge = -2 * ((h : ℂ) + 1))
    (hvac : W.vacuum ≠ 0) {κ : ℂ} (hE : FormalMLDE W κ) :
    κ = ((h : ℂ) + 1) * (5 * h - 6) := by
  have h0 := formalMLDE_coeff W hE 0
  have hd : (Module.finrank ℂ (W.grading ((0 : ℕ) : ℤ)) : ℂ) = 1 := by
    rw [Nat.cast_zero, W.vacuum_grade, finrank_span_singleton hvac, Nat.cast_one]
  rw [hd] at h0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.cast_zero] at h0
  rw [hc] at h0
  linear_combination (-720 : ℂ) * h0

/-- **The AK recurrence from the formal MLDE** (any `κ`; it is forced). -/
theorem isAKSolution_of_formalMLDE (h : ℕ)
    (hc : W.centralCharge = -2 * ((h : ℂ) + 1)) (hvac : W.vacuum ≠ 0) {κ : ℂ}
    (hE : FormalMLDE W κ) :
    IsAKSolution h (fun N : ℕ => (Module.finrank ℂ (W.grading N) : ℂ)) := by
  have hκ := kappa_eq_of_formalMLDE W h hc hvac hE
  set f := torusPartition (adjointModule W) with hf
  set D : ℕ → ℂ := fun n => (Module.finrank ℂ (W.grading ((n : ℕ) : ℤ)) : ℂ) with hD
  have hfe : ∀ (N m : ℕ), f ((N : ℂ) - W.centralCharge / 24 - m)
      = if m ≤ N then D (N - m) else 0 := fun N m => torusPartition_adjoint_sub W N m
  refine ⟨?_, ?_⟩
  · show (Module.finrank ℂ (W.grading ((0 : ℕ) : ℤ)) : ℂ) = 1
    rw [Nat.cast_zero, W.vacuum_grade, finrank_span_singleton hvac, Nat.cast_one]
  intro N hN
  have hE' := formalMLDE_coeff W hE N
  set e : ℂ := (N : ℂ) - W.centralCharge / 24 with he
  have hterm : ∀ r ∈ Finset.range N, (akKernel h N (r + 1) : ℂ) * D (N - (r + 1))
      = -6 * (zhuG 1 (r + 1) * (2 * ((e - ((r + 1 : ℕ) : ℂ)) * f (e - ((r + 1 : ℕ) : ℂ))))
        + zhuG 2 (r + 1) * (W.centralCharge / 2 * f (e - ((r + 1 : ℕ) : ℂ)))
        - ((h : ℂ) + 1) * (5 * h - 6) * (zhuG 2 (r + 1) * f (e - ((r + 1 : ℕ) : ℂ)))) := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hfr : f (e - ((r + 1 : ℕ) : ℂ)) = D (N - (r + 1)) := by
      rw [he, hfe, if_pos (by omega)]
    rw [hfr, zhuG_one_succ, zhuG_two_succ, he, hc]
    simp only [akKernel]
    push_cast [Nat.cast_sub (by omega : r + 1 ≤ N)]
    ring
  show (N : ℂ) * (6 * N + h) * D N = _
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum (Finset.range N) (fun r => zhuG 2 (r + 1) * f (e - ((r + 1 : ℕ) : ℂ)))
      (((h : ℂ) + 1) * (5 * h - 6))]
  set S1 := ∑ k ∈ Finset.range N,
    zhuG 1 (k + 1) * (2 * ((e - ((k + 1 : ℕ) : ℂ)) * f (e - ((k + 1 : ℕ) : ℂ)))) with hS1
  set S2 := ∑ k ∈ Finset.range N,
    zhuG 2 (k + 1) * (W.centralCharge / 2 * f (e - ((k + 1 : ℕ) : ℂ))) with hS2
  set S3 := ∑ k ∈ Finset.range N, zhuG 2 (k + 1) * f (e - ((k + 1 : ℕ) : ℂ)) with hS3
  clear_value S1 S2 S3
  rw [he, hc, hκ] at hE'
  linear_combination (6 : ℂ) * hE'

/-- The trace identity is the formal MLDE. -/
theorem formalMLDE_of_vacuumQuarticRelation {κ : ℂ} (hrel : VacuumQuarticRelation W κ) :
    FormalMLDE W κ :=
  (torusOnePoint_Lsq_sq_vacuum (adjointModule W)).symm.trans hrel.eq

/-- **The AK recurrence from the weight-four trace identity**, for any `κ` (forced to be
`(h+1)(5h-6)` by the indicial equation). -/
theorem isAKSolution_of_vacuumQuarticRelation (h : ℕ)
    (hc : W.centralCharge = -2 * ((h : ℂ) + 1)) (hvac : W.vacuum ≠ 0) {κ : ℂ}
    (hrel : VacuumQuarticRelation W κ) :
    IsAKSolution h (fun N : ℕ => (Module.finrank ℂ (W.grading N) : ℂ)) :=
  isAKSolution_of_formalMLDE W h hc hvac (formalMLDE_of_vacuumQuarticRelation W hrel)

end Coefficients

/-! ## The algebraic form: a square-bracket `C₂` relation at weight four -/

section Algebraic

variable (W : VertexOperatorAlgebra 𝒱)

/-- **Trace-null vectors**: the span of the square-bracket brackets `a[0]v` (`a` homogeneous of
weight `≥ 1`) and of the `L[-1]`-derivatives.  Every torus one-point function vanishes on it. -/
noncomputable def traceNull : Submodule ℂ 𝒱 :=
  Submodule.span ℂ ({x | ∃ (ka : ℕ) (a v : 𝒱), 1 ≤ ka ∧ a ∈ W.grading (ka : ℤ) ∧ x = vSqZ W a ka 0 v}
    ∪ Set.range (Lsq W (-1)))

theorem torusOnePoint_eq_zero_of_mem_traceNull {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) {x : 𝒱} (hx : x ∈ traceNull W) : torusOnePoint N x = 0 := by
  have : traceNull W ≤ LinearMap.ker (torusOnePointHom N) := by
    rw [traceNull, Submodule.span_le]
    rintro y (⟨ka, a, v, hka, ha, rfl⟩ | ⟨v, rfl⟩)
    · exact torusOnePoint_vSqZ_zero_eq_zero N hka ha v
    · exact torusOnePoint_Lsq_neg_one N v
  exact this hx

/-- One square-bracket `C₂` term `a[-2]b` of weight four: `a` homogeneous of weight `ka ≥ 1`,
`a[2]b = λ|0⟩` and `a[2m]b = 0` for `m ≥ 2`. -/
structure SqC2Term (W : VertexOperatorAlgebra 𝒱) where
  ka : ℕ
  a : 𝒱
  b : 𝒱
  lam : ℂ
  one_le : 1 ≤ ka
  mem : a ∈ W.grading (ka : ℤ)
  two : vSqZ W a ka 2 b = lam • W.vacuum
  high : ∀ m : ℕ, 2 ≤ m → vSqZ W a ka (2 * (m : ℤ)) b = 0

/-- `S(a[-2]b) = -3λ · G₄ ⋆ f` for a weight-four square-bracket `C₂` term. -/
theorem torusOnePoint_sqC2Term {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) (t : SqC2Term W) :
    torusOnePoint N (vSqZ W t.a t.ka (-2) t.b)
      = (-3 * t.lam) • qConv (zhuG 2) (torusPartition N) := by
  have h := zhuRecursion_neg_two N t.one_le t.mem t.b
  set F : ℕ → FormalQSeries := fun m => ((2 * (m + 1) - 1 : ℕ) : ℂ)
      • qConv (zhuG (m + 1)) (torusOnePoint N (vSqZ W t.a t.ka (2 * (m + 1) - 2 : ℤ) t.b)) with hF
  have hidx : ∀ m : ℕ, (2 * ((m : ℤ) + 1) - 2) = 2 * (m : ℤ) := fun m => by ring
  have hF0 : F 0 = 0 := by
    simp only [hF, hidx, Nat.cast_zero, mul_zero]
    rw [torusOnePoint_vSqZ_zero_eq_zero N t.one_le t.mem, qConv_zero_right, smul_zero]
  have hF1 : F 1 = (3 * t.lam) • qConv (zhuG 2) (torusPartition N) := by
    simp only [hF, hidx, Nat.cast_one, mul_one, Nat.reduceAdd]
    rw [t.two, torusOnePoint_smul, torusOnePoint_vacuum, qConv_smul_right, smul_smul]
    norm_num
  have hF2 : ∀ m, 2 ≤ m → F m = 0 := by
    intro m hm
    simp only [hF, hidx]
    rw [t.high m hm, torusOnePoint_zero, qConv_zero_right, smul_zero]
  have hsum : ∑ᶠ m : ℕ, F m = (3 * t.lam) • qConv (zhuG 2) (torusPartition N) := by
    rw [finsum_eq_sum_of_support_subset F (s := Finset.range 2)]
    · rw [Finset.sum_range_succ, Finset.sum_range_one, hF0, hF1, zero_add]
    · intro m hm
      simp only [Function.mem_support] at hm
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      exact hm (hF2 m (by omega))
  change torusOnePoint N (vSqZ W t.a t.ka (-2) t.b) + ∑ᶠ m : ℕ, F m = 0 at h
  rw [hsum] at h
  rw [eq_neg_of_add_eq_zero_left h, ← neg_smul, neg_mul]

/-- **The square-bracket `C₂` relation at weight four**: `L[-2]²|0⟩` equals a finite sum of
weight-four square-bracket `C₂` terms modulo trace-null vectors, with `κ = -3 ∑ λᵢ`.  Under Zhu's
change of coordinates this is `ω₍₋₁₎ω ∈ C₂(V)` (AK §7), i.e. `ω̄² = 0` in `R_V`. -/
structure SqC2QuarticRelation (W : VertexOperatorAlgebra 𝒱) (κ : ℂ) : Prop where
  rel : ∃ (s : Finset ℕ) (t : ℕ → SqC2Term W),
    Lsq W (-2) (Lsq W (-2) W.vacuum) - ∑ i ∈ s, vSqZ W (t i).a (t i).ka (-2) (t i).b
        ∈ traceNull W
      ∧ κ = -3 * ∑ i ∈ s, (t i).lam

/-- **The trace identity from the algebraic relation.** -/
theorem vacuumQuarticRelation_of_sqC2 {κ : ℂ} (h : SqC2QuarticRelation W κ) :
    VacuumQuarticRelation W κ := by
  obtain ⟨s, t, hmem, hκ⟩ := h.rel
  refine ⟨?_⟩
  have h0 := torusOnePoint_eq_zero_of_mem_traceNull W (adjointModule W) hmem
  rw [← torusOnePointHom_apply, map_sub, sub_eq_zero, map_sum] at h0
  rw [← torusOnePointHom_apply, h0, hκ, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [torusOnePointHom_apply, torusOnePoint_sqC2Term]

end Algebraic

/-! ## Assembly: the character target from the trace identity -/

/-- **the target lower bound from the weight-four trace identity** (type-generic). -/
theorem targetLowerBoundQ_of_vacuumQuarticRelation (W : VertexOperatorAlgebra 𝒱) (h : ℕ)
    (hc : W.centralCharge = -2 * ((h : ℂ) + 1)) (hvac : W.vacuum ≠ 0)
    {κ : ℂ} (hrel : VacuumQuarticRelation W κ) :
    DeligneCharacter.TargetLowerBoundQ W (DeligneCharacter.mldeCoeff h) :=
  targetLowerBoundQ_of_isAKSolution W (isAKSolution_of_vacuumQuarticRelation W h hc hvac hrel)

end VOA.DeligneAudit.DeligneMLDE

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneMLDE.torusOnePoint_Lsq_sq_vacuum
#print axioms VOA.DeligneAudit.DeligneMLDE.kappa_eq_of_formalMLDE
#print axioms VOA.DeligneAudit.DeligneMLDE.isAKSolution_of_formalMLDE
#print axioms VOA.DeligneAudit.DeligneMLDE.isAKSolution_of_vacuumQuarticRelation
#print axioms VOA.DeligneAudit.DeligneMLDE.targetLowerBoundQ_of_vacuumQuarticRelation
#print axioms VOA.DeligneAudit.DeligneMLDE.vacuumQuarticRelation_of_sqC2
end AxiomAudit
