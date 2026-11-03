import VOA.Huang.GenusOneCuspFunctional

/-! # The remaining algebra at the cusp

Miyamoto, math/0010180, Lemma 4.10 decomposes a symmetric functional on a
bimodule over a semisimple algebra into traces. We isolate its unweighted
case (choose the central element and its scalar to be zero). Theorem 2.10 (Li's converse to
the top correspondence) then lifts the resulting maps to intertwiners.

The two named inputs below isolate those algebraic steps. They are intended
for a rational VOA and a complete family of irreducible lowest-weight modules;
they are not asserted for an arbitrary family. Their consequence matches the
leading functional only, not an entire formal or analytic block.
-/
namespace VOA.Huang.GenusOne
open VOA VOA.FZ FusionTop
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

/-- For equal source and target, the top component is the insertion zero mode. -/
theorem topComp_self_eq_zeroMode (P : LWModule W)
    (Y : IntertwiningModes M P.carrier P.carrier) :
    topComp A P P Y = zeroMode A Y := by
  ext w
  refine FusionTop.induction_weight A w (by simp) (fun x y hx hy => ?_) ?_
  · simp only [map_add, hx, hy, LinearMap.add_apply]
  · intro α x hx
    rw [topComp_of_mem Y hx, zeroMode_of_mem A Y hx, add_sub_cancel_right]

/-- The lowest trace coefficient is the finite trace of the Frenkel–Zhu top map. -/
theorem trace_leading_eq_top (P : LWModule W)
    (Y : IntertwiningOperator A P.isMod P.isMod) (w : M) :
    trace Y w (P.h - W.centralCharge / 24) =
      LinearMap.trace ℂ (bot P) ((topMapFZ A P P Y).val w) := by
  rw [trace_eq, sub_add_cancel]
  congr 1
  ext x
  change zeroMode A Y.val w x = topComp A P P Y.val w x
  rw [topComp_self_eq_zeroMode]

variable {ι : Type u} [Fintype ι]

/-- Unweighted case of semisimple bimodule trace decomposition (Miyamoto Lemma 4.10).
This concerns functionals on `M/O(M)` and contains no analytic block hypothesis. -/
def InsertionSymmetricTopDecomposition (A : OrdVModule W M) (P : ι → LWModule W) : Prop :=
  ∀ ℓ : M →ₗ[ℂ] ℂ, fzO A.toWeakModule ≤ LinearMap.ker ℓ →
    (∀ (p : ℕ) (a : V), a ∈ W.grading (p : ℤ) → ∀ w : M,
      ℓ (fzLeft A.toWeakModule p a w) = ℓ (fzRight A.toWeakModule p a w)) →
    ∃ T : ∀ i, fzSpace A (P i) (P i),
      ∀ w, ℓ w = ∑ i, LinearMap.trace ℂ (bot (P i)) ((T i).val w)

/-- The converse top correspondence needed here (Miyamoto Theorem 2.10, citing Li).
`FusionTop.topMapFZ_injective` supplies the other direction for irreducible tops. -/
def InsertionTopSurjectivity (A : OrdVModule W M) (P : ι → LWModule W) : Prop :=
  ∀ i, Function.Surjective (topMapFZ A (P i) (P i))

/-- The two purely algebraic inputs realize every balanced quotient functional
by the lowest coefficients of actual intertwiner traces. -/
theorem functional_realized_on_tops (P : ι → LWModule W)
    (hdec : InsertionSymmetricTopDecomposition A P)
    (hlift : InsertionTopSurjectivity A P) (ℓ : M →ₗ[ℂ] ℂ)
    (hO : fzO A.toWeakModule ≤ LinearMap.ker ℓ)
    (hbal : ∀ (p : ℕ) (a : V), a ∈ W.grading (p : ℤ) → ∀ w : M,
      ℓ (fzLeft A.toWeakModule p a w) = ℓ (fzRight A.toWeakModule p a w)) :
    ∃ Y : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
      ∀ w, ℓ w = ∑ i, trace (Y i) w ((P i).h - W.centralCharge / 24) := by
  obtain ⟨T, hT⟩ := hdec ℓ hO hbal
  choose Y hY using fun i => hlift i (T i)
  refine ⟨Y, fun w => ?_⟩
  rw [hT w]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_leading_eq_top, hY i]

/-- Cusp realization applies to the leading functional just constructed.
The exponents on the right are each traced module's own lowest exponent. -/
theorem leading_realized_on_tops (P : ι → LWModule W)
    (hdec : InsertionSymmetricTopDecomposition A P)
    (hlift : InsertionTopSurjectivity A P)
    {S : M →ₗ[ℂ] FormalQSeries} {b : ℂ} (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) :
    ∃ Y : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
      ∀ w, S w b = ∑ i, trace (Y i) w ((P i).h - W.centralCharge / 24) :=
  functional_realized_on_tops P hdec hlift (Cusp.leading S b)
    (Cusp.leading_kills_fzO hsupp hS) (fun p _ ha w => Cusp.leading_balanced hS p ha w)

/-- With covariance discharged, finite trace interpolation is the sole input
left in the one-point S-closure reduction. -/
theorem insertionSClosure_of_interpolation
    (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    {U : Finset M} (hU : InsertionDetermining A U) (τ₀ : UpperHalfPlane)
    (hint : InsertionTraceInterpolation A Mfam h U τ₀) : InsertionSClosure A Mfam h :=
  insertionSClosure_of_covariance_spanning hC2 hA Mfam h hcw
    (insertionSBlockCovariance_of_irreducible hA)
    (insertionTraceSpanning_of_interpolation hC2 hA Mfam h hcw hU τ₀ hint)

end VOA.Huang.GenusOne
