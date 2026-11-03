/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Lattice.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.NhdsWithin
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Layer B: the Euclidean realisation of a positive definite lattice

`BLUEPRINT.md` D1 splits the library into an algebraic Layer A (`Lattice/Defs.lean` and
everything built on it) and an analytic Layer B, which is this file: the bridge sending a
positive definite `IntegralLattice` to an isometric embedding into `EuclideanSpace ℝ (Fin Γ.rank)`.

The crux is that positive definiteness *over `ℤ`* upgrades to positive definiteness of the Gram
matrix *over `ℝ`*. That step is genuinely analytic — the set where the real quadratic form is
nonnegative is closed and contains the (dense) rational points — and it is the only place in the
file where topology is used.

## Main results

* `IntegralLattice.gramReal` — the Gram matrix over `ℝ`.
* `IntegralLattice.posSemidef_gramReal`, `IntegralLattice.posDef_gramReal`.
* `IntegralLattice.euclideanMatrix` — a real matrix `B` with `Bᵀ B = G`.
* `IntegralLattice.toEuclidean` — the isometric embedding, and `inner_toEuclidean`.
* `IntegralLattice.finite_normSq_le` — finitely many lattice vectors of bounded norm. This one
  needs **no** analysis: it follows from Cauchy–Schwarz over `ℤ`
  (`IntegralLattice.IsPosDef.bilin_sq_le`).
* `IntegralLattice.covolume_toEuclidean` — the image is a full `ℤ`-lattice
  (`IntegralLattice.discreteTopology_range_toEuclidean`,
  `IntegralLattice.isZLattice_range_toEuclidean`) whose covolume is `√det`.

## References

Ebeling, *Lattices and Codes*, 3rd ed., §1.1.
-/

open scoped Matrix MatrixOrder
open Module (Basis finrank)

namespace IntegralLattice

variable (Γ : IntegralLattice)

/-! ### The Gram matrix over `ℝ` -/

/-- The Gram matrix of `Γ` in its chosen basis, viewed over `ℝ`. -/
noncomputable def gramReal : Matrix (Fin Γ.rank) (Fin Γ.rank) ℝ :=
  (Γ.gram Γ.chooseBasis).map (fun m : ℤ => (m : ℝ))

@[simp] theorem gramReal_apply (i j : Fin Γ.rank) :
    Γ.gramReal i j = ((Γ.gram Γ.chooseBasis i j : ℤ) : ℝ) := rfl

theorem gramReal_isHermitian : Γ.gramReal.IsHermitian := by
  show Γ.gramRealᴴ = Γ.gramReal
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  rw [Matrix.transpose_apply, gramReal_apply, gramReal_apply, gram_apply, gram_apply,
    Γ.bilin_symm]

theorem det_gramReal : Γ.gramReal.det = ((Γ.det : ℤ) : ℝ) := by
  have hmap := RingHom.map_det (Int.castRingHom ℝ) (Γ.gram Γ.chooseBasis)
  rw [det_eq_det_gram_chooseBasis, gramReal]
  exact hmap.symm

/-! ### The quadratic form in coordinates -/

theorem intVec_gram_eq_bilin (x y : Γ) :
    (fun i => Γ.chooseBasis.repr x i) ⬝ᵥ (Γ.gram Γ.chooseBasis) *ᵥ
        (fun i => Γ.chooseBasis.repr y i) = Γ.bilin x y := by
  have hmv : ∀ i, ((Γ.gram Γ.chooseBasis) *ᵥ (fun j => Γ.chooseBasis.repr y j)) i
      = Γ.bilin (Γ.chooseBasis i) y := fun i => Γ.gram_mulVec_repr Γ.chooseBasis y i
  rw [dotProduct]
  conv_rhs => rw [← Γ.chooseBasis.sum_repr x]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmv i, bilin_smul_left]

theorem intVec_gram_nonneg (h : Γ.IsPosDef) (v : Fin Γ.rank → ℤ) :
    0 ≤ v ⬝ᵥ (Γ.gram Γ.chooseBasis) *ᵥ v := by
  have hrepr : ∀ i, Γ.chooseBasis.repr (Γ.chooseBasis.equivFun.symm v) i = v i := by
    intro i
    have hv : Γ.chooseBasis.equivFun (Γ.chooseBasis.equivFun.symm v) = v :=
      Γ.chooseBasis.equivFun.apply_symm_apply v
    rw [Basis.equivFun_apply] at hv
    exact congrFun hv i
  have hfun : (fun i => Γ.chooseBasis.repr (Γ.chooseBasis.equivFun.symm v) i) = v := funext hrepr
  have := Γ.intVec_gram_eq_bilin (Γ.chooseBasis.equivFun.symm v) (Γ.chooseBasis.equivFun.symm v)
  rw [hfun] at this
  rw [this]
  exact h.normSq_nonneg _

/-! ### Positive definiteness over `ℝ` -/

private theorem hom_two (G : Matrix (Fin Γ.rank) (Fin Γ.rank) ℝ) (c : ℝ)
    (v : Fin Γ.rank → ℝ) : (c • v) ⬝ᵥ G *ᵥ (c • v) = c ^ 2 * (v ⬝ᵥ G *ᵥ v) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **Positive definiteness over `ℤ` upgrades to positive semidefiniteness over `ℝ`.**
The quadratic form is continuous, hence the set where it is nonnegative is closed; it contains
the rational points by clearing denominators, and those are dense. -/
theorem posSemidef_gramReal (h : Γ.IsPosDef) : Γ.gramReal.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg Γ.gramReal_isHermitian ?_
  intro w
  rw [show star w = w from star_trivial w]
  have hcont : Continuous fun v : Fin Γ.rank → ℝ => v ⬝ᵥ Γ.gramReal *ᵥ v := by
    unfold dotProduct Matrix.mulVec
    fun_prop
  have hclosed : IsClosed {v : Fin Γ.rank → ℝ | 0 ≤ v ⬝ᵥ Γ.gramReal *ᵥ v} :=
    isClosed_le continuous_const hcont
  have hint : ∀ v : Fin Γ.rank → ℤ,
      0 ≤ (fun i => ((v i : ℤ) : ℝ)) ⬝ᵥ Γ.gramReal *ᵥ (fun i => ((v i : ℤ) : ℝ)) := by
    intro v
    have hcast : (fun i => ((v i : ℤ) : ℝ)) ⬝ᵥ Γ.gramReal *ᵥ (fun i => ((v i : ℤ) : ℝ))
        = ((v ⬝ᵥ (Γ.gram Γ.chooseBasis) *ᵥ v : ℤ) : ℝ) := by
      simp only [dotProduct, Matrix.mulVec, gramReal, Matrix.map_apply]
      push_cast
      rfl
    rw [hcast]
    exact_mod_cast Γ.intVec_gram_nonneg h v
  have hrat : Set.pi Set.univ (fun _ : Fin Γ.rank => Set.range ((↑) : ℚ → ℝ))
      ⊆ {v : Fin Γ.rank → ℝ | 0 ≤ v ⬝ᵥ Γ.gramReal *ᵥ v} := by
    intro v hv
    simp only [Set.mem_univ_pi, Set.mem_range] at hv
    choose q hq using hv
    obtain ⟨d, hd, hm⟩ : ∃ d : ℕ, 0 < d ∧ ∀ i, ∃ m : ℤ, ((d : ℚ)) * q i = (m : ℚ) := by
      refine ⟨∏ i, (q i).den, Finset.prod_pos fun i _ => (q i).pos, fun i => ?_⟩
      obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
      have hq' : q i * ((q i).den : ℚ) = ((q i).num : ℚ) := Rat.mul_den_eq_num (q i)
      refine ⟨e * (q i).num, ?_⟩
      rw [he]
      push_cast
      linear_combination (e : ℚ) * hq'
    choose m hmm using hm
    have hdv : ((d : ℝ)) • v = (fun i => ((m i : ℤ) : ℝ)) := by
      funext i
      have hc := congrArg (fun t : ℚ => (t : ℝ)) (hmm i)
      push_cast at hc
      rw [Pi.smul_apply, smul_eq_mul, ← hq i]
      exact hc
    have h0 := hint m
    rw [← hdv, Γ.hom_two] at h0
    have hdpos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    show 0 ≤ v ⬝ᵥ Γ.gramReal *ᵥ v
    refine le_of_mul_le_mul_left ?_ hdpos
    rw [mul_zero]
    exact h0
  have hdense : Dense (Set.pi Set.univ (fun _ : Fin Γ.rank => Set.range ((↑) : ℚ → ℝ))) :=
    dense_pi Set.univ (fun _ _ => Rat.denseRange_cast)
  have huniv : {v : Fin Γ.rank → ℝ | 0 ≤ v ⬝ᵥ Γ.gramReal *ᵥ v} = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hdense.closure_eq]
    exact hclosed.closure_subset_iff.mpr hrat
  have hw : w ∈ {v : Fin Γ.rank → ℝ | 0 ≤ v ⬝ᵥ Γ.gramReal *ᵥ v} := by
    rw [huniv]; trivial
  exact hw

theorem posDef_gramReal (h : Γ.IsPosDef) : Γ.gramReal.PosDef := by
  rw [(Γ.posSemidef_gramReal h).posDef_iff_det_ne_zero, det_gramReal]
  exact_mod_cast h.det_ne_zero

/-! ### Positive definiteness in an arbitrary integral basis -/

/-- The Gram matrix in an arbitrary integral basis, viewed over `ℝ`. -/
noncomputable def gramRealOf {ι : Type*} [Fintype ι] (b : Basis ι ℤ Γ) :
    Matrix ι ι ℝ := (Γ.gram b).map (fun m : ℤ => (m : ℝ))

@[simp] theorem gramRealOf_apply {ι : Type*} [Fintype ι] (b : Basis ι ℤ Γ) (i j : ι) :
    Γ.gramRealOf b i j = ((Γ.bilin (b i) (b j) : ℤ) : ℝ) := rfl

theorem gramRealOf_isHermitian {ι : Type*} [Fintype ι] (b : Basis ι ℤ Γ) :
    (Γ.gramRealOf b).IsHermitian := by
  show (Γ.gramRealOf b)ᴴ = Γ.gramRealOf b
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  rw [Matrix.transpose_apply, gramRealOf_apply, gramRealOf_apply, Γ.bilin_symm]

theorem det_gramRealOf {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ Γ) :
    (Γ.gramRealOf b).det = ((Γ.det : ℤ) : ℝ) := by
  have hmap := RingHom.map_det (Int.castRingHom ℝ) (Γ.gram b)
  rw [gramRealOf, ← Γ.det_eq_gram_det b]
  exact hmap.symm

private theorem gramRealOf_hom_two {ι : Type*} [Fintype ι]
    (G : Matrix ι ι ℝ) (c : ℝ) (v : ι → ℝ) :
    (c • v) ⬝ᵥ G *ᵥ (c • v) = c ^ 2 * (v ⬝ᵥ G *ᵥ v) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

private theorem intVec_gramRealOf_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ Γ) (h : Γ.IsPosDef) (v : ι → ℤ) :
    0 ≤ (fun i => ((v i : ℤ) : ℝ)) ⬝ᵥ Γ.gramRealOf b *ᵥ
      (fun i => ((v i : ℤ) : ℝ)) := by
  let x : Γ := b.equivFun.symm v
  have hrepr : ∀ i, b.repr x i = v i := by
    intro i
    have hv := b.equivFun.apply_symm_apply v
    rw [Basis.equivFun_apply] at hv
    exact congrFun hv i
  have hquad : v ⬝ᵥ Γ.gram b *ᵥ v = Γ.bilin x x := by
    rw [dotProduct]
    have hrow (i : ι) : ((Γ.gram b) *ᵥ v) i = Γ.bilin (b i) x := by
      have h := Γ.gram_mulVec_repr b x i
      rw [show v = fun j => b.repr x j by funext j; exact (hrepr j).symm]
      exact h
    rw [Finset.sum_congr rfl fun i _ => by rw [hrow]]
    calc
      _ = Γ.bilin (∑ i, b.repr x i • b i) x := by
        rw [map_sum, LinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro i hi
        rw [bilin_smul_left, hrepr]
      _ = Γ.bilin x x := by rw [b.sum_repr]
  have hcast :
      (fun i => ((v i : ℤ) : ℝ)) ⬝ᵥ Γ.gramRealOf b *ᵥ
          (fun i => ((v i : ℤ) : ℝ)) =
        ((v ⬝ᵥ Γ.gram b *ᵥ v : ℤ) : ℝ) := by
    simp only [dotProduct, Matrix.mulVec, gramRealOf, Matrix.map_apply]
    push_cast
    rfl
  rw [hcast, hquad]
  exact_mod_cast h.normSq_nonneg x

/-- Positive definiteness of a lattice makes the real Gram matrix positive semidefinite in
every integral basis.  The proof clears denominators on rational coordinate vectors and uses
density, exactly as for the chosen-basis matrix `gramReal`. -/
theorem posSemidef_gramRealOf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ Γ) (h : Γ.IsPosDef) : (Γ.gramRealOf b).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Γ.gramRealOf_isHermitian b) ?_
  intro w
  rw [show star w = w from star_trivial w]
  have hcont : Continuous fun v : ι → ℝ => v ⬝ᵥ Γ.gramRealOf b *ᵥ v := by
    unfold dotProduct Matrix.mulVec
    fun_prop
  have hclosed : IsClosed {v : ι → ℝ | 0 ≤ v ⬝ᵥ Γ.gramRealOf b *ᵥ v} :=
    isClosed_le continuous_const hcont
  have hrat : Set.pi Set.univ (fun _ : ι => Set.range ((↑) : ℚ → ℝ)) ⊆
      {v : ι → ℝ | 0 ≤ v ⬝ᵥ Γ.gramRealOf b *ᵥ v} := by
    intro v hv
    simp only [Set.mem_univ_pi, Set.mem_range] at hv
    choose q hq using hv
    obtain ⟨d, hd, hm⟩ : ∃ d : ℕ, 0 < d ∧
        ∀ i, ∃ m : ℤ, ((d : ℚ)) * q i = (m : ℚ) := by
      refine ⟨∏ i, (q i).den, Finset.prod_pos fun i _ => (q i).pos, fun i => ?_⟩
      obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
      have hq' : q i * ((q i).den : ℚ) = ((q i).num : ℚ) := Rat.mul_den_eq_num (q i)
      refine ⟨e * (q i).num, ?_⟩
      rw [he]
      push_cast
      linear_combination (e : ℚ) * hq'
    choose m hmm using hm
    have hdv : ((d : ℝ)) • v = (fun i => ((m i : ℤ) : ℝ)) := by
      funext i
      have hc := congrArg (fun t : ℚ => (t : ℝ)) (hmm i)
      push_cast at hc
      rw [Pi.smul_apply, smul_eq_mul, ← hq i]
      exact hc
    have h0 := Γ.intVec_gramRealOf_nonneg b h m
    rw [← hdv, gramRealOf_hom_two] at h0
    have hdpos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    refine le_of_mul_le_mul_left ?_ hdpos
    rw [mul_zero]
    exact h0
  have hdense : Dense (Set.pi Set.univ (fun _ : ι => Set.range ((↑) : ℚ → ℝ))) :=
    dense_pi Set.univ (fun _ _ => Rat.denseRange_cast)
  have huniv : {v : ι → ℝ | 0 ≤ v ⬝ᵥ Γ.gramRealOf b *ᵥ v} = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hdense.closure_eq]
    exact hclosed.closure_subset_iff.mpr hrat
  have hw : w ∈ {v : ι → ℝ | 0 ≤ v ⬝ᵥ Γ.gramRealOf b *ᵥ v} := by
    rw [huniv]
    trivial
  exact hw

/-- Positive definiteness of the real Gram matrix in an arbitrary integral basis. -/
theorem posDef_gramRealOf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ Γ) (h : Γ.IsPosDef) : (Γ.gramRealOf b).PosDef := by
  rw [(Γ.posSemidef_gramRealOf b h).posDef_iff_det_ne_zero, Γ.det_gramRealOf b]
  exact_mod_cast h.det_ne_zero

/-! ### The isometric embedding -/

theorem exists_transpose_mul_self (h : Γ.IsPosDef) :
    ∃ B : Matrix (Fin Γ.rank) (Fin Γ.rank) ℝ, Γ.gramReal = Bᵀ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Γ.posSemidef_gramReal h).nonneg
  refine ⟨B, ?_⟩
  rw [hB, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- A real matrix `B` with `Bᵀ B = G`: the coordinates of a Euclidean realisation of `Γ`. -/
noncomputable def euclideanMatrix (h : Γ.IsPosDef) : Matrix (Fin Γ.rank) (Fin Γ.rank) ℝ :=
  (Γ.exists_transpose_mul_self h).choose

theorem euclideanMatrix_spec (h : Γ.IsPosDef) :
    Γ.gramReal = (Γ.euclideanMatrix h)ᵀ * (Γ.euclideanMatrix h) :=
  (Γ.exists_transpose_mul_self h).choose_spec

private theorem dotProduct_mulVec_mulVec (B : Matrix (Fin Γ.rank) (Fin Γ.rank) ℝ)
    (v w : Fin Γ.rank → ℝ) : (B *ᵥ v) ⬝ᵥ (B *ᵥ w) = v ⬝ᵥ (Bᵀ * B) *ᵥ w := by
  have hL : (B *ᵥ v) ⬝ᵥ (B *ᵥ w) = ∑ i, ∑ j, ∑ k, (B i j * v j) * (B i k * w k) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have hR : v ⬝ᵥ (Bᵀ * B) *ᵥ w = ∑ j, ∑ k, ∑ i, (B i j * v j) * (B i k * w k) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.transpose_apply]
    ring
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

/-- **The Euclidean realisation of a positive definite lattice** (`BLUEPRINT.md` D1, Layer B). -/
noncomputable def toEuclidean (h : Γ.IsPosDef) : Γ →ₗ[ℤ] EuclideanSpace ℝ (Fin Γ.rank) where
  toFun x :=
    WithLp.toLp 2 ((Γ.euclideanMatrix h) *ᵥ (fun i => ((Γ.chooseBasis.repr x i : ℤ) : ℝ)))
  map_add' x y := by
    have hc : (fun i => ((Γ.chooseBasis.repr (x + y) i : ℤ) : ℝ))
        = (fun i => ((Γ.chooseBasis.repr x i : ℤ) : ℝ))
          + (fun i => ((Γ.chooseBasis.repr y i : ℤ) : ℝ)) := by
      funext i; simp
    show WithLp.toLp 2 ((Γ.euclideanMatrix h) *ᵥ _) = _
    rw [hc, Matrix.mulVec_add, WithLp.toLp_add]
  map_smul' c x := by
    have hc : (fun i => ((Γ.chooseBasis.repr (c • x) i : ℤ) : ℝ))
        = (c : ℝ) • (fun i => ((Γ.chooseBasis.repr x i : ℤ) : ℝ)) := by
      funext i
      simp
    show WithLp.toLp 2 ((Γ.euclideanMatrix h) *ᵥ _) = _
    rw [hc, Matrix.mulVec_smul, WithLp.toLp_smul, RingHom.id_apply,
      Int.cast_smul_eq_zsmul ℝ c]

theorem toEuclidean_ofLp (h : Γ.IsPosDef) (x : Γ) :
    (Γ.toEuclidean h x).ofLp
      = (Γ.euclideanMatrix h) *ᵥ (fun i => ((Γ.chooseBasis.repr x i : ℤ) : ℝ)) := rfl

/-- **The embedding is an isometry**: it turns the lattice form into the Euclidean inner
product. -/
theorem inner_toEuclidean (h : Γ.IsPosDef) (x y : Γ) :
    inner ℝ (Γ.toEuclidean h x) (Γ.toEuclidean h y) = ((Γ.bilin x y : ℤ) : ℝ) := by
  rw [PiLp.inner_apply]
  have hsum : ∑ i, inner ℝ ((Γ.toEuclidean h x).ofLp i) ((Γ.toEuclidean h y).ofLp i)
      = (Γ.toEuclidean h x).ofLp ⬝ᵥ (Γ.toEuclidean h y).ofLp := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [RCLike.inner_apply, mul_comm]
  rw [hsum, toEuclidean_ofLp, toEuclidean_ofLp, Γ.dotProduct_mulVec_mulVec,
    ← Γ.euclideanMatrix_spec h]
  have hcast : (fun i => ((Γ.chooseBasis.repr x i : ℤ) : ℝ)) ⬝ᵥ Γ.gramReal *ᵥ
      (fun i => ((Γ.chooseBasis.repr y i : ℤ) : ℝ))
      = (((fun i => Γ.chooseBasis.repr x i) ⬝ᵥ (Γ.gram Γ.chooseBasis) *ᵥ
          (fun i => Γ.chooseBasis.repr y i) : ℤ) : ℝ) := by
    simp only [dotProduct, Matrix.mulVec, gramReal, Matrix.map_apply]
    push_cast
    rfl
  rw [hcast, Γ.intVec_gram_eq_bilin]

theorem toEuclidean_injective (h : Γ.IsPosDef) : Function.Injective (Γ.toEuclidean h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h0 : ((Γ.bilin x x : ℤ) : ℝ) = 0 := by
    rw [← Γ.inner_toEuclidean h x x, hx, inner_zero_left]
  have hz : normSq x = 0 := by exact_mod_cast h0
  exact (IsPosDef.normSq_eq_zero_iff h).mp hz

/-! ### Finiteness of vectors of bounded norm

This is a purely algebraic statement: Cauchy–Schwarz over `ℤ`
(`IntegralLattice.IsPosDef.bilin_sq_le`) bounds the pairings of a vector of bounded norm with the
basis vectors, and a bounded box in `ℤⁿ` is finite. No analysis is used. -/

theorem finite_normSq_le (h : Γ.IsPosDef) (c : ℤ) : {x : Γ | normSq x ≤ c}.Finite := by
  classical
  have hinj : Function.Injective (fun (x : Γ) (i : Fin Γ.rank) => Γ.bilin (Γ.chooseBasis i) x) := by
    intro x y hxy
    have hall : ∀ i, Γ.bilin (Γ.chooseBasis i) (x - y) = 0 := by
      intro i
      rw [bilin_sub_right]
      exact sub_eq_zero_of_eq (congrFun hxy i)
    have hflip : Γ.bilin.flip (x - y) = 0 := by
      refine Γ.chooseBasis.ext fun i => ?_
      rw [LinearMap.flip_apply, LinearMap.zero_apply]
      exact hall i
    have hz : Γ.bilin (x - y) (x - y) = 0 := by
      have hc := LinearMap.congr_fun hflip (x - y)
      rw [LinearMap.flip_apply, LinearMap.zero_apply] at hc
      rw [Γ.bilin_symm]
      exact hc
    have := (IsPosDef.normSq_eq_zero_iff h).mp hz
    exact sub_eq_zero.mp this
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine Set.Finite.subset
    (Set.Finite.pi (fun i : Fin Γ.rank => Set.finite_Icc
      (-(c * normSq (Γ.chooseBasis i))) (c * normSq (Γ.chooseBasis i)))) ?_
  rintro _ ⟨x, hx, rfl⟩
  intro i _
  have hxc : normSq x ≤ c := hx
  have hbi : 0 ≤ normSq (Γ.chooseBasis i) := IsPosDef.normSq_nonneg h _
  have hcs := IsPosDef.bilin_sq_le h (Γ.chooseBasis i) x
  have hbound : (Γ.bilin (Γ.chooseBasis i) x) ^ 2 ≤ c * normSq (Γ.chooseBasis i) := by
    calc (Γ.bilin (Γ.chooseBasis i) x) ^ 2
        ≤ normSq (Γ.chooseBasis i) * normSq x := hcs
      _ ≤ normSq (Γ.chooseBasis i) * c := mul_le_mul_of_nonneg_left hxc hbi
      _ = c * normSq (Γ.chooseBasis i) := mul_comm _ _
  have habs : |Γ.bilin (Γ.chooseBasis i) x| ≤ c * normSq (Γ.chooseBasis i) := by
    rcases eq_or_ne (Γ.bilin (Γ.chooseBasis i) x) 0 with h0 | h0
    · rw [h0, abs_zero]
      have h2 := hbound
      rw [h0] at h2
      simpa using h2
    · have h1 : 1 ≤ |Γ.bilin (Γ.chooseBasis i) x| := by
        rcases lt_trichotomy (Γ.bilin (Γ.chooseBasis i) x) 0 with hlt | heq | hgt
        · rw [abs_of_neg hlt]; omega
        · exact absurd heq h0
        · rw [abs_of_pos hgt]; omega
      calc |Γ.bilin (Γ.chooseBasis i) x|
          ≤ |Γ.bilin (Γ.chooseBasis i) x| * |Γ.bilin (Γ.chooseBasis i) x| :=
            le_mul_of_one_le_left (abs_nonneg _) h1
        _ = Γ.bilin (Γ.chooseBasis i) x * Γ.bilin (Γ.chooseBasis i) x := abs_mul_abs_self _
        _ = (Γ.bilin (Γ.chooseBasis i) x) ^ 2 := (sq _).symm
        _ ≤ c * normSq (Γ.chooseBasis i) := hbound
  rw [Set.mem_Icc]
  exact ⟨by linarith [neg_abs_le (Γ.bilin (Γ.chooseBasis i) x)],
    by linarith [le_abs_self (Γ.bilin (Γ.chooseBasis i) x)]⟩


/-! ### The covolume of the Euclidean realisation

Ebeling, *Lattices and Codes*, §1.1: the covolume of a lattice is the square root of its
determinant.  Here `IntegralLattice.det` is basis independent, so the statement is about the
image `LinearMap.range (Γ.toEuclidean h) ⊆ EuclideanSpace ℝ (Fin Γ.rank)`, which is a full
`ℤ`-lattice in the sense of `IsZLattice`. -/

section Covolume

open MeasureTheory

/-- The images of the chosen basis are linearly independent over `ℝ`: their Gram matrix is
`gramReal`, which is nonsingular. -/
theorem linearIndependent_toEuclidean (h : Γ.IsPosDef) :
    LinearIndependent ℝ fun i => Γ.toEuclidean h (Γ.chooseBasis i) := by
  have hdet : Γ.gramReal.det ≠ 0 := by
    rw [Γ.det_gramReal]; exact_mod_cast h.det_ne_zero
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hmul : Γ.gramReal *ᵥ c = 0 := by
    funext j
    have hj := congrArg (fun y => inner ℝ (Γ.toEuclidean h (Γ.chooseBasis j)) y) hc
    simp only [inner_sum, real_inner_smul_right, inner_zero_right] at hj
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hj]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Γ.inner_toEuclidean h, gramReal_apply, gram_apply, mul_comm]
  exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hmul) i

/-- The Euclidean images of the members of any integral basis are linearly independent over
`ℝ`.  This basis-independent form is useful when a root-system construction naturally supplies
a basis different from `chooseBasis`. -/
theorem linearIndependent_toEuclidean_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Γ.IsPosDef) (b : Basis ι ℤ Γ) :
    LinearIndependent ℝ fun i => Γ.toEuclidean h (b i) := by
  have hdet : (Γ.gramRealOf b).det ≠ 0 := by
    rw [Γ.det_gramRealOf b]
    exact_mod_cast h.det_ne_zero
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hmul : Γ.gramRealOf b *ᵥ c = 0 := by
    funext j
    have hj := congrArg (fun y => inner ℝ (Γ.toEuclidean h (b j)) y) hc
    simp only [inner_sum, real_inner_smul_right, inner_zero_right] at hj
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hj]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Γ.inner_toEuclidean h, gramRealOf_apply, mul_comm]
  exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hmul) i

/-- The `ℝ`-basis of `EuclideanSpace ℝ (Fin Γ.rank)` given by the images of `Γ.chooseBasis`. -/
noncomputable def euclideanBasis (h : Γ.IsPosDef) :
    Basis (Fin Γ.rank) ℝ (EuclideanSpace ℝ (Fin Γ.rank)) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (Γ.linearIndependent_toEuclidean h) (by simp)

@[simp] theorem coe_euclideanBasis (h : Γ.IsPosDef) :
    ⇑(Γ.euclideanBasis h) = fun i => Γ.toEuclidean h (Γ.chooseBasis i) :=
  coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _

theorem range_toEuclidean_eq_span (h : Γ.IsPosDef) :
    LinearMap.range (Γ.toEuclidean h) = Submodule.span ℤ (Set.range (Γ.euclideanBasis h)) := by
  rw [LinearMap.range_eq_map, ← Γ.chooseBasis.span_eq, Submodule.map_span, ← Set.range_comp,
    coe_euclideanBasis]
  rfl

theorem discreteTopology_range_toEuclidean (h : Γ.IsPosDef) :
    DiscreteTopology (LinearMap.range (Γ.toEuclidean h)) := by
  rw [Γ.range_toEuclidean_eq_span h]; infer_instance

theorem span_real_range_toEuclidean (h : Γ.IsPosDef) :
    Submodule.span ℝ ((LinearMap.range (Γ.toEuclidean h) :
      Submodule ℤ (EuclideanSpace ℝ (Fin Γ.rank))) : Set (EuclideanSpace ℝ (Fin Γ.rank))) = ⊤ := by
  rw [Γ.range_toEuclidean_eq_span h]; exact ZSpan.span_top _

theorem isZLattice_range_toEuclidean (h : Γ.IsPosDef) :
    letI := Γ.discreteTopology_range_toEuclidean h
    IsZLattice ℝ (LinearMap.range (Γ.toEuclidean h)) :=
  letI := Γ.discreteTopology_range_toEuclidean h
  ⟨Γ.span_real_range_toEuclidean h⟩

/-- The `ℤ`-basis of the image lattice obtained by transporting `Γ.chooseBasis`. -/
noncomputable def rangeBasis (h : Γ.IsPosDef) :
    Basis (Fin Γ.rank) ℤ (LinearMap.range (Γ.toEuclidean h)) :=
  Γ.chooseBasis.map (LinearEquiv.ofInjective (Γ.toEuclidean h) (Γ.toEuclidean_injective h))

@[simp] theorem coe_rangeBasis (h : Γ.IsPosDef) (i : Fin Γ.rank) :
    ((Γ.rangeBasis h i : LinearMap.range (Γ.toEuclidean h)) : EuclideanSpace ℝ (Fin Γ.rank))
      = Γ.toEuclidean h (Γ.chooseBasis i) := rfl

theorem toEuclidean_chooseBasis_ofLp (h : Γ.IsPosDef) (i j : Fin Γ.rank) :
    (Γ.toEuclidean h (Γ.chooseBasis j)).ofLp i = Γ.euclideanMatrix h i j := by
  classical
  rw [toEuclidean_ofLp, Matrix.mulVec, dotProduct]
  have hrep : ∀ k, ((Γ.chooseBasis.repr (Γ.chooseBasis j) k : ℤ) : ℝ) = if k = j then 1 else 0 := by
    intro k
    rw [Basis.repr_self, Finsupp.single_apply]
    split <;> rename_i hk
    · rw [if_pos hk.symm]; norm_num
    · rw [if_neg (fun hc => hk hc.symm)]; norm_num
  simp only [hrep, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The matrix of the image basis in the standard orthonormal basis is `euclideanMatrix`. -/
theorem det_rangeBasis (h : Γ.IsPosDef) :
    ((EuclideanSpace.basisFun (Fin Γ.rank) ℝ).toBasis).det
        ((↑) ∘ (Γ.rangeBasis h)) = (Γ.euclideanMatrix h).det := by
  classical
  rw [Basis.det_apply]
  congr 1
  ext i j
  rw [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, Function.comp_apply, coe_rangeBasis]
  exact Γ.toEuclidean_chooseBasis_ofLp h i j

/-- `|det B| = √(det Γ)` for the Euclidean coordinate matrix `B`. -/
theorem abs_det_euclideanMatrix (h : Γ.IsPosDef) :
    |(Γ.euclideanMatrix h).det| = Real.sqrt ((Γ.det : ℤ) : ℝ) := by
  have hsq : ((Γ.det : ℤ) : ℝ) = ((Γ.euclideanMatrix h).det) ^ 2 := by
    rw [← Γ.det_gramReal]
    conv_lhs => rw [Γ.euclideanMatrix_spec h]
    rw [Matrix.det_mul, Matrix.det_transpose, sq]
  rw [hsq, Real.sqrt_sq_eq_abs]

/-- **Ebeling, §1.1: the covolume of a positive definite lattice is `√det`.**
The Euclidean realisation `Γ.toEuclidean h` has image a full `ℤ`-lattice in
`EuclideanSpace ℝ (Fin Γ.rank)`, and its covolume for Lebesgue measure is `Real.sqrt Γ.det`. -/
theorem covolume_toEuclidean (h : Γ.IsPosDef) :
    ZLattice.covolume (LinearMap.range (Γ.toEuclidean h)) = Real.sqrt ((Γ.det : ℤ) : ℝ) := by
  classical
  have := Γ.discreteTopology_range_toEuclidean h
  have := Γ.isZLattice_range_toEuclidean h
  have hfd : (volume : Measure (EuclideanSpace ℝ (Fin Γ.rank))).real
      (ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin Γ.rank) ℝ).toBasis)) = 1 := by
    have h1 : volume (ZSpan.fundamentalDomain
        ((EuclideanSpace.basisFun (Fin Γ.rank) ℝ).toBasis))
        = volume (parallelepiped ⇑((EuclideanSpace.basisFun (Fin Γ.rank) ℝ).toBasis)) :=
      measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ volume)
    have h2 : volume (parallelepiped ⇑((EuclideanSpace.basisFun (Fin Γ.rank) ℝ).toBasis))
        = 1 := by
      rw [← (EuclideanSpace.basisFun (Fin Γ.rank) ℝ).addHaar_eq_volume]
      exact Basis.addHaar_self _
    rw [measureReal_def, h1, h2, ENNReal.toReal_one]
  rw [ZLattice.covolume_eq_det_mul_measureReal (L := LinearMap.range (Γ.toEuclidean h))
      (μ := volume) (Γ.rangeBasis h) ((EuclideanSpace.basisFun (Fin Γ.rank) ℝ).toBasis),
    hfd, mul_one, Γ.det_rangeBasis h, Γ.abs_det_euclideanMatrix h]

end Covolume

end IntegralLattice
