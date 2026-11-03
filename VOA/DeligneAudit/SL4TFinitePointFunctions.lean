import VOA.DeligneAudit.SL4TInvariantDescent
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Polynomial functions on finite point sets and their invariant orbit count. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

attribute [local instance] Classical.propDecidable

variable {ι σ G : Type*}

/-- Simultaneous evaluation at a family of complex points. -/
def finitePointEvaluation (x : ι → σ → ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] (ι → ℂ) where
  toFun p i := MvPolynomial.aeval (x i) p
  map_zero' := by ext i; exact map_zero _
  map_one' := by ext i; exact map_one _
  map_add' p q := by ext i; exact map_add _ p q
  map_mul' p q := by ext i; exact map_mul _ p q
  commutes' c := by ext i; exact (MvPolynomial.aeval (x i)).commutes c

/-- Distinct points can be separated by an affine coordinate polynomial. -/
theorem finitePoint_separatingPolynomial (x : ι → σ → ℂ)
    (hx : Function.Injective x) {i j : ι} (hij : i ≠ j) :
    ∃ p : MvPolynomial σ ℂ,
      finitePointEvaluation x p i = 1 ∧ finitePointEvaluation x p j = 0 := by
  classical
  have h : ∃ s, x i s ≠ x j s := by
    by_contra hn
    apply hij
    apply hx
    funext s
    by_contra hs
    exact hn ⟨s, hs⟩
  obtain ⟨s, hs⟩ := h
  refine ⟨MvPolynomial.C (x i s - x j s)⁻¹ *
    (MvPolynomial.X s - MvPolynomial.C (x j s)), ?_, ?_⟩
  · change MvPolynomial.aeval (x i) _ = 1
    simp only [map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hs)
  · change MvPolynomial.aeval (x j) _ = 0
    simp

/-- A finite set of distinct points admits polynomial indicator functions. -/
theorem finitePoint_indicatorPolynomial [Fintype ι] (x : ι → σ → ℂ)
    (hx : Function.Injective x) (i : ι) :
    ∃ p : MvPolynomial σ ℂ, ∀ j,
      finitePointEvaluation x p j = if j = i then 1 else 0 := by
  classical
  let q : ι → MvPolynomial σ ℂ := fun j =>
    if h : i = j then 1 else (finitePoint_separatingPolynomial x hx h).choose
  have hqi (j : ι) : finitePointEvaluation x (q j) i = 1 := by
    by_cases h : i = j
    · simp [q, h]
    · simpa only [q, dif_neg h] using
        (finitePoint_separatingPolynomial x hx h).choose_spec.1
  have hqj (j : ι) (h : i ≠ j) : finitePointEvaluation x (q j) j = 0 := by
    simpa only [q, dif_neg h] using
      (finitePoint_separatingPolynomial x hx h).choose_spec.2
  refine ⟨∏ j, q j, fun j => ?_⟩
  change MvPolynomial.aeval (x j) (∏ a, q a) = _
  rw [map_prod]
  by_cases h : j = i
  · subst j
    simpa only [if_pos rfl] using Finset.prod_eq_one (fun a _ => hqi a)
  · rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (hqj j (Ne.symm h))

/-- Polynomial evaluation is onto all functions on any finite set of distinct points. -/
theorem finitePointEvaluation_surjective [Fintype ι] (x : ι → σ → ℂ)
    (hx : Function.Injective x) : Function.Surjective (finitePointEvaluation x) := by
  classical
  intro f
  let p := fun i => (finitePoint_indicatorPolynomial x hx i).choose
  refine ⟨∑ i, MvPolynomial.C (f i) * p i, ?_⟩
  funext j
  change MvPolynomial.aeval (x j) _ = _
  simp only [map_sum, map_mul, MvPolynomial.aeval_C]
  have hp (i : ι) : MvPolynomial.aeval (x j) (p i) = if j = i then 1 else 0 :=
    (finitePoint_indicatorPolynomial x hx i).choose_spec j
  simp [hp]

/-- The coordinate algebra of distinct finite points is the full function algebra. -/
def finitePointQuotientEquiv [Fintype ι] (x : ι → σ → ℂ) (hx : Function.Injective x) :
    (MvPolynomial σ ℂ ⧸ RingHom.ker (finitePointEvaluation x).toRingHom) ≃ₐ[ℂ]
      (ι → ℂ) :=
  Ideal.quotientKerAlgEquivOfSurjective (finitePointEvaluation_surjective x hx)

/-- The dimension of the coordinate algebra is the number of distinct points. -/
theorem finitePointQuotient_finrank [Fintype ι] (x : ι → σ → ℂ)
    (hx : Function.Injective x) :
    Module.finrank ℂ
      (MvPolynomial σ ℂ ⧸ RingHom.ker (finitePointEvaluation x).toRingHom) =
        Fintype.card ι := by
  rw [(finitePointQuotientEquiv x hx).toLinearEquiv.finrank_eq]
  simp

variable [Group G] [MulAction G ι]

/-- A group acts on functions by pullback along its inverse action on points. -/
def pointFunctionAction : G →* ((ι → ℂ) ≃ₐ[ℂ] (ι → ℂ)) where
  toFun g :=
    { toFun := fun f i => f (g⁻¹ • i)
      invFun := fun f i => f (g • i)
      left_inv := by intro f; ext i; simp
      right_inv := by intro f; ext i; simp
      map_add' := by intros; rfl
      map_mul' := by intros; rfl
      commutes' := by intros; rfl }
  map_one' := by ext f i; simp
  map_mul' g h := by ext f i; simp [mul_smul]

/-- Invariant functions are exactly functions constant on point orbits. -/
theorem pointFunction_fixed_iff (f : ι → ℂ) :
    f ∈ finiteActionFixedSubalgebra (pointFunctionAction (G := G) (ι := ι)) ↔
      ∀ (g : G) (i : ι), f (g • i) = f i := by
  constructor
  · intro h g i
    have hi := congrFun (h g⁻¹) i
    change f ((g⁻¹)⁻¹ • i) = f i at hi
    simpa only [inv_inv] using hi
  · intro h g
    funext i
    exact h g⁻¹ i

/-- Functions on the orbit set are the invariant point functions, as complex algebras. -/
def pointFunctionOrbitEquiv :
    (MulAction.orbitRel.Quotient G ι → ℂ) ≃ₐ[ℂ]
      finiteActionFixedSubalgebra (pointFunctionAction (G := G) (ι := ι)) where
  toFun f := ⟨fun i => f (Quotient.mk _ i), (pointFunction_fixed_iff _).mpr (by
    intro g i
    congr 1
    exact Quotient.sound ⟨g, rfl⟩)⟩
  invFun f := Quotient.lift f.val (by
    intro i j h
    obtain ⟨g, rfl⟩ := h
    exact (pointFunction_fixed_iff f.val).mp f.property g j)
  left_inv f := by ext q; induction q using Quotient.inductionOn; rfl
  right_inv f := by apply Subtype.ext; rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl
  commutes' := by intros; rfl

/-- The invariant dimension of a finite permutation algebra is the number of orbits. -/
theorem pointFunction_fixed_finrank [Finite ι] :
    Module.finrank ℂ
      (finiteActionFixedSubalgebra (pointFunctionAction (G := G) (ι := ι))) =
        Nat.card (MulAction.orbitRel.Quotient G ι) := by
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient G ι)
  rw [← (pointFunctionOrbitEquiv (G := G) (ι := ι)).toLinearEquiv.finrank_eq]
  simp [Nat.card_eq_fintype_card]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.finitePoint_separatingPolynomial
#print axioms VOA.DeligneAudit.SL4T.finitePoint_indicatorPolynomial
#print axioms VOA.DeligneAudit.SL4T.finitePointEvaluation_surjective
#print axioms VOA.DeligneAudit.SL4T.finitePointQuotient_finrank
#print axioms VOA.DeligneAudit.SL4T.pointFunction_fixed_iff
#print axioms VOA.DeligneAudit.SL4T.pointFunction_fixed_finrank
