import VOA.Huang.LiConverseResidue

/-! # Opposite mode systems and the full-dual action `Y*` (Li's regular representation, I)

H.-S. Li (*Regular representations of vertex operator algebras I*, math/9908108, §2–3)
builds the regular representation from a **right** (opposite) module structure on a
space `M`: the operators `Y°(v,x) = Y(e^{xL(1)}(−x⁻²)^{L(0)}v, x⁻¹)` satisfy the
*opposite* Jacobi identity and are *upper* truncated (`v°ₙ w = 0` for `n ≪ 0`).
Transposing them gives the action `Y*(v,x)α = α ∘ Y°(v,x)` on the full dual `M*`, which
satisfies the honest (left) Jacobi identity, but only *pointwise*: the infinite sums
become finite after evaluation at a vector `w ∈ M`.

This file axiomatises such a structure (`OppBase`) and develops its residue calculus with
Laurent-polynomial test functions, mirroring `LiConverseResidue`:

* `OppBase.bres a φ = Res_x φ(x) Y°(a,x) = Σₙ φₙ a°ₙ` (an endomorphism of `M`);
* `OppBase.bres_jacobi` — the opposite Jacobi identity with arbitrary test functions;
* `OppBase.ys a φ = (bres a φ)ᵀ` — the action `Y*` on `Module.Dual ℂ M`;
* `OppBase.ys_jacobi_apply` — the (left) residue Jacobi identity for `Y*`, evaluated at
  any `w ∈ M`; `OppBase.ys_commutator` — its `l = 0` case as an identity of functionals.

The instance coming from an ordinary module (via the library's `dualAdj` and the proved
module FHL identity) is in `LiRegularOpp`.

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.Huang.LiConverse LaurentPolynomial
open scoped BigOperators

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- An **opposite mode system** on `M`: a linear family of mode endomorphisms
`B a n = a°ₙ`, upper truncated, with the vacuum acting as the identity and satisfying the
*opposite* Jacobi identity (the composition order of the left-hand side is reversed with
respect to the module Jacobi identity). -/
structure OppBase (W : VertexOperatorAlgebra V) (M : Type v) [AddCommGroup M] [Module ℂ M] where
  /-- The modes `a°ₙ`. -/
  B : V →ₗ[ℂ] ℤ → Module.End ℂ M
  /-- Upper truncation: `a°ₙ w = 0` for `n ≪ 0`. -/
  trunc : ∀ (a : V) (w : M), ∃ K : ℤ, ∀ n : ℤ, n ≤ K → B a n w = 0
  /-- `Y°(𝟙, x) = id`. -/
  vacuum : ∀ (n : ℤ) (w : M), B W.vacuum n w = if n = -1 then w else 0
  /-- The opposite Jacobi identity in mode form. -/
  jacobi : ∀ (a b : V) (w : M) (l m n : ℤ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz l i) •
        (B b (n + i) (B a (l + m - i) w) - negOnePow l • B a (m + i) (B b (l + n - i) w)))
      = ∑ᶠ i : ℤ, cbz m i • B (W.smul a (l + i) b) (m + n - i) w

namespace OppBase

variable {W : VertexOperatorAlgebra V} {M : Type v} [AddCommGroup M] [Module ℂ M]
variable (Bs : OppBase W M)

/-! ## The residue pairing -/

/-- `bres a φ = Res_x φ(x) Y°(a,x) = Σₙ φₙ a°ₙ`. -/
noncomputable def bres (a : V) (φ : ℂ[T;T⁻¹]) : Module.End ℂ M :=
  Finsupp.linearCombination ℂ (Bs.B a) φ

theorem bres_single (a : V) (n : ℤ) (c : ℂ) :
    Bs.bres a (Finsupp.single n c) = c • Bs.B a n :=
  Finsupp.linearCombination_single ℂ _ _

theorem bres_CT (a : V) (n : ℤ) (c : ℂ) : Bs.bres a (LC c * T n) = c • Bs.B a n := by
  rw [← single_eq_C_mul_T]; exact Bs.bres_single a n c

theorem bres_T (a : V) (n : ℤ) : Bs.bres a (T n) = Bs.B a n := by
  simpa using Bs.bres_CT a n 1

theorem bres_add (a : V) (φ ψ : ℂ[T;T⁻¹]) :
    Bs.bres a (φ + ψ) = Bs.bres a φ + Bs.bres a ψ := map_add _ _ _

theorem bres_smul (a : V) (c : ℂ) (φ : ℂ[T;T⁻¹]) :
    Bs.bres a (c • φ) = c • Bs.bres a φ := map_smul _ _ _

theorem bres_zero (a : V) : Bs.bres a 0 = 0 := map_zero _

theorem bres_sub (a : V) (φ ψ : ℂ[T;T⁻¹]) :
    Bs.bres a (φ - ψ) = Bs.bres a φ - Bs.bres a ψ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ, Bs.bres_add, Bs.bres_smul, neg_one_smul,
    ← sub_eq_add_neg]

theorem bres_sum {ι : Type*} (a : V) (s : Finset ι) (f : ι → ℂ[T;T⁻¹]) :
    Bs.bres a (∑ i ∈ s, f i) = ∑ i ∈ s, Bs.bres a (f i) := map_sum _ _ _

theorem bres_add_a (a b : V) (φ : ℂ[T;T⁻¹]) :
    Bs.bres (a + b) φ = Bs.bres a φ + Bs.bres b φ := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [Bs.bres_add, Bs.bres_add, Bs.bres_add, hp, hq]; abel
  | C_mul_T n c => rw [Bs.bres_CT, Bs.bres_CT, Bs.bres_CT, map_add, Pi.add_apply, smul_add]

theorem bres_smul_a (c : ℂ) (a : V) (φ : ℂ[T;T⁻¹]) :
    Bs.bres (c • a) φ = c • Bs.bres a φ := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [Bs.bres_add, Bs.bres_add, hp, hq, smul_add]
  | C_mul_T n d => rw [Bs.bres_CT, Bs.bres_CT, map_smul, Pi.smul_apply, smul_comm]

theorem bres_zero_a (φ : ℂ[T;T⁻¹]) : Bs.bres 0 φ = 0 := by
  simpa using Bs.bres_smul_a 0 0 φ

/-- Upper truncation transported to residues: shifting a test function far enough to the
left kills the residue. -/
theorem bres_shift_eventually_zero (a : V) (w : M) (φ : ℂ[T;T⁻¹]) :
    ∃ J : ℤ, ∀ j : ℤ, J ≤ j → Bs.bres a (T (-j) * φ) w = 0 := by
  induction φ using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨J, hJ⟩ := hp
    obtain ⟨J', hJ'⟩ := hq
    exact ⟨max J J', fun j hj => by
      rw [mul_add, Bs.bres_add, LinearMap.add_apply, hJ j (le_trans (le_max_left _ _) hj),
        hJ' j (le_trans (le_max_right _ _) hj), add_zero]⟩
  | C_mul_T n c =>
    obtain ⟨K, hK⟩ := Bs.trunc a w
    refine ⟨n - K, fun j hj => ?_⟩
    rw [show T (-j) * (LC c * T n) = LC c * T (-j + n) by rw [T_add]; ring, Bs.bres_CT,
      LinearMap.smul_apply, hK _ (by omega), smul_zero]

/-! ## The opposite Jacobi identity with test functions -/

/-- Left summand of the opposite residue Jacobi identity. -/
noncomputable def jacL (a b : V) (w : M) (l : ℤ) (f g : ℂ[T;T⁻¹]) (j : ℤ) : M :=
  (negOnePow j * cbz l j) •
    (Bs.bres b (T j * g) (Bs.bres a (T (l - j) * f) w)
      - negOnePow l • Bs.bres a (T j * f) (Bs.bres b (T (l - j) * g) w))

/-- Right summand of the opposite residue Jacobi identity. -/
noncomputable def jacR (a b : V) (w : M) (l : ℤ) (f g : ℂ[T;T⁻¹]) (i : ℤ) : M :=
  Bs.bres (W.smul a (l + i) b) (dd i f * g) w

theorem jacL_support_finite (a b : V) (w : M) (l : ℤ) (f g : ℂ[T;T⁻¹]) :
    (Function.support (Bs.jacL a b w l f g)).Finite := by
  obtain ⟨J₁, hJ₁⟩ := Bs.bres_shift_eventually_zero a w (T l * f)
  obtain ⟨J₂, hJ₂⟩ := Bs.bres_shift_eventually_zero b w (T l * g)
  apply (Set.finite_Icc 0 (max J₁ J₂)).subset
  intro j hj
  rw [Function.mem_support] at hj
  refine ⟨not_lt.mp fun h => hj ?_, not_lt.mp fun h => hj ?_⟩
  · simp [jacL, cbz_apply_neg l h]
  · have e1 : T (l - j) * f = T (-j) * (T l * f) := by rw [← mul_assoc, ← T_add]; ring_nf
    have e2 : T (l - j) * g = T (-j) * (T l * g) := by rw [← mul_assoc, ← T_add]; ring_nf
    rw [jacL, e1, e2, hJ₁ j (le_trans (le_max_left _ _) h.le),
      hJ₂ j (le_trans (le_max_right _ _) h.le), map_zero, map_zero, smul_zero, sub_zero,
      smul_zero]

theorem jacR_support_finite (a b : V) (w : M) (l : ℤ) (f g : ℂ[T;T⁻¹]) :
    (Function.support (Bs.jacR a b w l f g)).Finite := by
  obtain ⟨N, hN⟩ := W.regularity a b
  apply (Set.finite_Icc 0 (N - l)).subset
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [jacR, dd_neg h, zero_mul, Bs.bres_zero, LinearMap.zero_apply]
  · have h0 : W.smul a (l + i) b = 0 := hN _ (by omega)
    rw [jacR, h0, Bs.bres_zero_a, LinearMap.zero_apply]

theorem jacL_add_left (a b : V) (w : M) (l : ℤ) (f f' g : ℂ[T;T⁻¹]) (j : ℤ) :
    Bs.jacL a b w l (f + f') g j = Bs.jacL a b w l f g j + Bs.jacL a b w l f' g j := by
  simp only [jacL, mul_add, Bs.bres_add, LinearMap.add_apply, map_add, smul_add, smul_sub]
  abel

theorem jacL_add_right (a b : V) (w : M) (l : ℤ) (f g g' : ℂ[T;T⁻¹]) (j : ℤ) :
    Bs.jacL a b w l f (g + g') j = Bs.jacL a b w l f g j + Bs.jacL a b w l f g' j := by
  simp only [jacL, mul_add, Bs.bres_add, LinearMap.add_apply, map_add, smul_add, smul_sub]
  abel

theorem jacR_add_left (a b : V) (w : M) (l : ℤ) (f f' g : ℂ[T;T⁻¹]) (i : ℤ) :
    Bs.jacR a b w l (f + f') g i = Bs.jacR a b w l f g i + Bs.jacR a b w l f' g i := by
  simp only [jacR, map_add, add_mul, Bs.bres_add, LinearMap.add_apply]

theorem jacR_add_right (a b : V) (w : M) (l : ℤ) (f g g' : ℂ[T;T⁻¹]) (i : ℤ) :
    Bs.jacR a b w l f (g + g') i = Bs.jacR a b w l f g i + Bs.jacR a b w l f g' i := by
  simp only [jacR, mul_add, Bs.bres_add, LinearMap.add_apply]

theorem jac_monomial (a b : V) (w : M) (l : ℤ) (c d : ℂ) (m n : ℤ) :
    (∑ᶠ j : ℤ, Bs.jacL a b w l (LC c * T m) (LC d * T n) j)
      = ∑ᶠ i : ℤ, Bs.jacR a b w l (LC c * T m) (LC d * T n) i := by
  have hL : ∀ j, Bs.jacL a b w l (LC c * T m) (LC d * T n) j = (c * d) •
      ((negOnePow j * cbz l j) •
        (Bs.B b (n + j) (Bs.B a (l + m - j) w)
          - negOnePow l • Bs.B a (m + j) (Bs.B b (l + n - j) w))) := by
    intro j
    have e1 : T j * (LC d * T n) = LC d * T (n + j) := by rw [T_add]; ring
    have e2 : T (l - j) * (LC c * T m) = LC c * T (l + m - j) := by
      rw [show l + m - j = (l - j) + m by ring, T_add]; ring
    have e3 : T j * (LC c * T m) = LC c * T (m + j) := by rw [T_add]; ring
    have e4 : T (l - j) * (LC d * T n) = LC d * T (l + n - j) := by
      rw [show l + n - j = (l - j) + n by ring, T_add]; ring
    rw [jacL, e1, e2, e3, e4, Bs.bres_CT, Bs.bres_CT, Bs.bres_CT, Bs.bres_CT]
    simp only [LinearMap.smul_apply, map_smul]
    module
  have hR : ∀ i, Bs.jacR a b w l (LC c * T m) (LC d * T n) i = (c * d) •
      (cbz m i • Bs.B (W.smul a (l + i) b) (m + n - i) w) := by
    intro i
    rw [jacR, dd_CT, show LC (c * cbz m i) * T (m - i) * (LC d * T n)
        = LC (c * cbz m i * d) * T (m + n - i) by
      rw [show m + n - i = (m - i) + n by ring, T_add]; simp only [map_mul]; ring, Bs.bres_CT,
      LinearMap.smul_apply, smul_smul]
    congr 1; ring
  rw [finsum_congr hL, finsum_congr hR, ← smul_finsum, ← smul_finsum, Bs.jacobi]

/-- **The opposite Jacobi identity with test functions.** -/
theorem bres_jacobi (a b : V) (w : M) (l : ℤ) (f g : ℂ[T;T⁻¹]) :
    (∑ᶠ j : ℤ, Bs.jacL a b w l f g j) = ∑ᶠ i : ℤ, Bs.jacR a b w l f g i := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [finsum_congr (Bs.jacL_add_left a b w l p q g),
      finsum_congr (Bs.jacR_add_left a b w l p q g),
      finsum_add_distrib (Bs.jacL_support_finite a b w l p g)
        (Bs.jacL_support_finite a b w l q g),
      finsum_add_distrib (Bs.jacR_support_finite a b w l p g)
        (Bs.jacR_support_finite a b w l q g), hp, hq]
  | C_mul_T m c =>
    induction g using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
      rw [finsum_congr (Bs.jacL_add_right a b w l _ p q),
        finsum_congr (Bs.jacR_add_right a b w l _ p q),
        finsum_add_distrib (Bs.jacL_support_finite a b w l _ p)
          (Bs.jacL_support_finite a b w l _ q),
        finsum_add_distrib (Bs.jacR_support_finite a b w l _ p)
          (Bs.jacR_support_finite a b w l _ q), hp, hq]
    | C_mul_T n d => exact Bs.jac_monomial a b w l c d m n

/-! ## The full-dual action `Y*` -/

/-- `ys a φ α = α ∘ Res_x φ(x) Y°(a,x)`: the transpose of `bres`. -/
noncomputable def ys (a : V) (φ : ℂ[T;T⁻¹]) : Module.Dual ℂ M →ₗ[ℂ] Module.Dual ℂ M :=
  (Bs.bres a φ).dualMap

@[simp] theorem ys_apply (a : V) (φ : ℂ[T;T⁻¹]) (α : Module.Dual ℂ M) (w : M) :
    Bs.ys a φ α w = α (Bs.bres a φ w) := rfl

theorem ys_add (a : V) (φ ψ : ℂ[T;T⁻¹]) (α : Module.Dual ℂ M) :
    Bs.ys a (φ + ψ) α = Bs.ys a φ α + Bs.ys a ψ α := by
  ext w; simp [Bs.bres_add]

theorem ys_smul (a : V) (c : ℂ) (φ : ℂ[T;T⁻¹]) (α : Module.Dual ℂ M) :
    Bs.ys a (c • φ) α = c • Bs.ys a φ α := by
  ext w; simp [Bs.bres_smul]

theorem ys_zero (a : V) (α : Module.Dual ℂ M) : Bs.ys a 0 α = 0 := by
  ext w; simp [Bs.bres_zero]

theorem ys_sub (a : V) (φ ψ : ℂ[T;T⁻¹]) (α : Module.Dual ℂ M) :
    Bs.ys a (φ - ψ) α = Bs.ys a φ α - Bs.ys a ψ α := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ, Bs.ys_add, Bs.ys_smul, neg_one_smul,
    ← sub_eq_add_neg]

theorem ys_sum {ι : Type*} (a : V) (s : Finset ι) (f : ι → ℂ[T;T⁻¹]) (α : Module.Dual ℂ M) :
    Bs.ys a (∑ i ∈ s, f i) α = ∑ i ∈ s, Bs.ys a (f i) α := by
  ext w; simp [Bs.bres_sum]

theorem ys_CT (a : V) (c : ℂ) (n : ℤ) (α : Module.Dual ℂ M) :
    Bs.ys a (LC c * T n) α = c • Bs.ys a (T n) α := by
  rw [← smul_eq_C_mul, Bs.ys_smul]

theorem ys_add_a (a b : V) (φ : ℂ[T;T⁻¹]) (α : Module.Dual ℂ M) :
    Bs.ys (a + b) φ α = Bs.ys a φ α + Bs.ys b φ α := by
  ext w; simp [Bs.bres_add_a]

theorem ys_smul_a (c : ℂ) (a : V) (φ : ℂ[T;T⁻¹]) (α : Module.Dual ℂ M) :
    Bs.ys (c • a) φ α = c • Bs.ys a φ α := by
  ext w; simp [Bs.bres_smul_a]

theorem ys_zero_a (φ : ℂ[T;T⁻¹]) (α : Module.Dual ℂ M) : Bs.ys 0 φ α = 0 := by
  ext w; simp [Bs.bres_zero_a]

/-- Left summand of the `Y*` Jacobi identity (a functional on `M`). -/
noncomputable def ysJacL (a b : V) (α : Module.Dual ℂ M) (l : ℤ) (f g : ℂ[T;T⁻¹]) (j : ℤ) :
    Module.Dual ℂ M :=
  (negOnePow j * cbz l j) •
    (Bs.ys a (T (l - j) * f) (Bs.ys b (T j * g) α)
      - negOnePow l • Bs.ys b (T (l - j) * g) (Bs.ys a (T j * f) α))

/-- Right summand of the `Y*` Jacobi identity. -/
noncomputable def ysJacR (a b : V) (α : Module.Dual ℂ M) (l : ℤ) (f g : ℂ[T;T⁻¹]) (i : ℤ) :
    Module.Dual ℂ M :=
  Bs.ys (W.smul a (l + i) b) (dd i f * g) α

theorem ysJacL_apply (a b : V) (α : Module.Dual ℂ M) (l : ℤ) (f g : ℂ[T;T⁻¹]) (j : ℤ)
    (w : M) : Bs.ysJacL a b α l f g j w = α (Bs.jacL a b w l f g j) := by
  simp only [ysJacL, jacL, LinearMap.smul_apply, LinearMap.sub_apply, ys_apply, map_smul,
    map_sub]

theorem ysJacR_apply (a b : V) (α : Module.Dual ℂ M) (l : ℤ) (f g : ℂ[T;T⁻¹]) (i : ℤ)
    (w : M) : Bs.ysJacR a b α l f g i w = α (Bs.jacR a b w l f g i) := rfl

/-- **The `Y*` Jacobi identity, evaluated at a vector.** The sums are finite after
evaluation at `w` (they need not be finite as functionals). -/
theorem ys_jacobi_apply (a b : V) (α : Module.Dual ℂ M) (l : ℤ) (f g : ℂ[T;T⁻¹]) (w : M) :
    (∑ᶠ j : ℤ, Bs.ysJacL a b α l f g j w) = ∑ᶠ i : ℤ, Bs.ysJacR a b α l f g i w := by
  simp only [ysJacL_apply, ysJacR_apply]
  rw [← map_finsum α (Bs.jacL_support_finite a b w l f g),
    ← map_finsum α (Bs.jacR_support_finite a b w l f g), Bs.bres_jacobi]

theorem ysJacR_support_finite (a b : V) (α : Module.Dual ℂ M) (l : ℤ) (f g : ℂ[T;T⁻¹]) :
    (Function.support (Bs.ysJacR a b α l f g)).Finite := by
  obtain ⟨N, hN⟩ := W.regularity a b
  apply (Set.finite_Icc 0 (N - l)).subset
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [ysJacR, dd_neg h, zero_mul, Bs.ys_zero]
  · have h0 : W.smul a (l + i) b = 0 := hN _ (by omega)
    rw [ysJacR, h0, Bs.ys_zero_a]

/-- **The commutator formula for `Y*`** (the `l = 0` case), an identity of functionals:
`Y*(a,f) Y*(b,g) α − Y*(b,g) Y*(a,f) α = Σᵢ Y*(a₍ᵢ₎b, f⁽ⁱ⁾ g) α`. -/
theorem ys_commutator (a b : V) (α : Module.Dual ℂ M) (f g : ℂ[T;T⁻¹]) :
    Bs.ys a f (Bs.ys b g α) - Bs.ys b g (Bs.ys a f α)
      = ∑ᶠ i : ℤ, Bs.ys (W.smul a i b) (dd i f * g) α := by
  ext w
  have h := Bs.ys_jacobi_apply a b α 0 f g w
  have hL : ∀ j, Bs.ysJacL a b α 0 f g j w
      = if j = 0 then (Bs.ys a f (Bs.ys b g α) - Bs.ys b g (Bs.ys a f α)) w else 0 := by
    intro j
    split_ifs with hj
    · subst hj
      have h1 : negOnePow (0 : ℤ) = 1 := by simp [negOnePow]
      simp [ysJacL, T_zero, h1]
    · rcases lt_or_gt_of_ne hj with h' | h'
      · simp [ysJacL, cbz_apply_neg 0 h']
      · rw [ysJacL, cbz_lt (p := 0) (c := j) le_rfl (by omega)]
        simp
  rw [finsum_congr hL, finsum_eq_single _ 0 (fun j hj => if_neg hj), if_pos rfl] at h
  rw [h]
  have hfin := Bs.ysJacR_support_finite a b α 0 f g
  have := map_finsum (LinearMap.applyₗ (R := ℂ) (M := M) (M₂ := ℂ) w) hfin
  simp only [LinearMap.applyₗ_apply_apply] at this
  rw [← this]
  simp [ysJacR]

end OppBase

end VOA.Huang.LiRegular
