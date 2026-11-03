/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QuadraticCurrentFunctionalCarrier
import VOA.Commutative.QuadraticJetCoefficientPairing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# The current-algebra action on the current-only carrier, and step B5

`W_m = currentCarrier Q m 0` consists of tensor polynomials `p : (Fin m → σ) → K[z₁,…,z_m]`
(functionals on `g^{⊗m}` with polynomial dependence on the roots), symmetric under simultaneous
permutations, satisfying the collision equations for the quadratic relations `Q`.

The loop algebra `g[t]` acts by the coadjoint action at the points `z_i`:

  `(x ⊗ t^r) p (t) = - Σ_i z_i^r Σ_c f(x, t_i, c) p(t[i ↦ c])`,

with `f` the structure constants.  This file proves, for any `f`, `Q` such that the span of the
relations is stable under the induced derivation of `Sym² g` (`RelationsStable`), that `W_m` is
stable under the action (`loopOp_mem`), and, for a diagonal-free index `c₀` (`Q r (c₀,c₀) = 0`),
that the constant vector `δ_{(c₀,…,c₀)}` lies in `W_m`.  Hence the cyclic span
`Mspace = U(g[t]) · δ_{c₀}` lies in `W_m`: this is the paper's step **B5** (`M_m ⊂ W_m`).
-/

namespace VOA.DeligneAudit.SectorLoop

open VOA.DeligneAuxiliaryCollision VOA.QuadraticCurrentFunctionalCarrier
open VOA.QuadraticJetCoefficientPairing VOA.CollisionCommonFactors MvPolynomial

noncomputable section

variable {K σ ρ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

/-! ## Quadratic relations and their second derivatives -/

section D2

/-- `∂_a ∂_b (·)(0)`. -/
def d2 (a b : σ) : MvPolynomial σ K →ₗ[K] K :=
  (MvPolynomial.aeval (fun _ => (0 : K))).toLinearMap ∘ₗ
    ((pderiv a).toLinearMap ∘ₗ (pderiv b).toLinearMap)

omit [Fintype σ] in
theorem d2_XX (a b i j : σ) :
    d2 a b (X i * X j : MvPolynomial σ K) =
      (Pi.single (M := fun _ => K) b 1 i) * (Pi.single (M := fun _ => K) a 1 j)
        + (Pi.single (M := fun _ => K) b 1 j) * (Pi.single (M := fun _ => K) a 1 i) := by
  have hb : ∀ c d : σ, (Pi.single (M := fun _ => MvPolynomial σ K) c 1 d) =
      C (Pi.single (M := fun _ => K) c 1 d) := by
    intro c d
    by_cases h : c = d
    · subst h; simp
    · simp [Ne.symm h]
  simp only [d2, LinearMap.coe_comp, Function.comp_apply, Derivation.coeFn_coe,
    Derivation.leibniz, pderiv_X, hb, smul_eq_mul, map_add, pderiv_C, mul_zero, zero_add,
    AlgHom.toLinearMap_apply, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  ring

/-- The second derivative of a quadratic relation symmetrizes the matrix. -/
theorem d2_quadraticRelation (q : σ × σ → K) (a b : σ) :
    d2 a b (quadraticRelation q) = q (a, b) + q (b, a) := by
  classical
  rw [quadraticRelation, map_sum]
  simp only [map_smul, d2_XX, smul_eq_mul, Pi.single_apply]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq', add_comm]

end D2

/-! ## The loop operators -/

variable (f : σ → σ → σ → K)

/-- The root `z_i` of a current slot. -/
abbrev zr {m : ℕ} (i : Fin m) : MvPolynomial (Particle m 0) K := X (i.castAdd 0)

/-- The loop operator `x ⊗ t^r`, coadjoint at the points `z_i`. -/
def loopOp (m : ℕ) (x : σ) (r : ℕ) :
    TensorPolynomial (K := K) (σ := σ) m 0 →ₗ[K] TensorPolynomial (K := K) (σ := σ) m 0 where
  toFun p t := -∑ i, zr i ^ r * ∑ c, C (f x (t i) c) * p (Function.update t i c)
  map_add' p q := by
    funext t
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, neg_add]
  map_smul' a p := by
    funext t
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_C_mul, Finset.mul_sum, mul_neg]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
    ring

/-! ## Symmetry on the collision diagonal -/

section Swap

variable {m : ℕ}

/-- The two particles of an increasing pair of current slots. -/
abbrev pa (ij : IncreasingPair (Fin m)) : Particle m 0 := ij.1.1.castAdd 0
abbrev pb (ij : IncreasingPair (Fin m)) : Particle m 0 := ij.1.2.castAdd 0

theorem pb_ne_pa (ij : IncreasingPair (Fin m)) : pb ij ≠ pa ij :=
  (Fin.castAdd_injective m 0).ne (ne_of_gt ij.2)

/-- The collided value of a tensor at the pair `(x,y)`. -/
abbrev collide (p : TensorPolynomial (K := K) (σ := σ) m 0) (ij : IncreasingPair (Fin m))
    (t : Fin m → σ) (xy : σ × σ) : MvPolynomial {x : Particle m 0 // x ≠ pa ij} K :=
  collisionMap (pa ij) (pb ij) (pb_ne_pa ij) (p (insertPair ij t xy))

omit [Fintype σ] in
omit [DecidableEq σ] in
theorem insertPair_comp_swap (ij : IncreasingPair (Fin m)) (t : Fin m → σ) (x y : σ) :
    insertPair ij t (x, y) ∘ (Equiv.swap ij.1.1 ij.1.2).symm = insertPair ij t (y, x) := by
  have hne : ij.1.1 ≠ ij.1.2 := ne_of_lt ij.2
  funext k
  simp only [insertPair, Function.comp_apply, Equiv.symm_swap, Function.update_apply,
    Equiv.swap_apply_def]
  by_cases h1 : k = ij.1.1
  · subst h1; simp [hne]
  · by_cases h2 : k = ij.1.2
    · subst h2; simp [hne, Ne.symm hne]
    · simp [h1, h2]

omit [Fintype σ] [DecidableEq σ] in
theorem collide_swap (p : TensorPolynomial (K := K) (σ := σ) m 0) (hp : Symmetric p)
    (ij : IncreasingPair (Fin m)) (t : Fin m → σ) (x y : σ) :
    collide p ij t (x, y) = collide p ij t (y, x) := by
  let g := Equiv.swap ij.1.1 ij.1.2
  let e := Equiv.swap (pa ij) (pb ij)
  have he : ExtendsCurrentPermutation e g := fun i =>
    (Fin.castAdd_injective m 0).swap_apply _ _ _
  have hs := hp e g he (insertPair ij t (x, y))
  rw [insertPair_comp_swap] at hs
  unfold collide
  rw [← hs]
  simp only [collisionMap, MvPolynomial.rename_rename]
  have hidx : collisionIndex (pa ij) (pb ij) (pb_ne_pa ij) ∘ ⇑e =
      collisionIndex (pa ij) (pb ij) (pb_ne_pa ij) := by
    funext k
    simp only [Function.comp_apply, e, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; simp [collisionIndex, pb_ne_pa ij]
    · subst h2; simp [collisionIndex]
    · rfl
  rw [hidx]

omit [Fintype σ] in
theorem projectedDiagonal_sub (a b : Particle m 0) (hba : b ≠ a) {T : Type*} [Fintype T]
    (c c' : T → K) (P : T → MvPolynomial (Particle m 0) K) :
    projectedDiagonal a b hba c P - projectedDiagonal a b hba c' P =
      projectedDiagonal a b hba (c - c') P := by
  simp only [projectedDiagonal, ← Finset.sum_sub_distrib, Pi.sub_apply, map_sub, sub_mul]

/-- **On symmetric tensors the collision equation only sees the quadratic polynomial.** -/
theorem readback_congr [CharZero K] (p : TensorPolynomial (K := K) (σ := σ) m 0)
    (hp : Symmetric p) (ij : IncreasingPair (Fin m)) (t : Fin m → σ) (q q' : σ × σ → K)
    (hqq : quadraticRelation q = quadraticRelation q') :
    currentReadback q ij t p = currentReadback q' ij t p := by
  rw [← sub_eq_zero]
  unfold currentReadback
  rw [projectedDiagonal_sub]
  set D := q - q' with hD
  have hanti : ∀ a b, D (b, a) = -D (a, b) := by
    intro a b
    have h0 : quadraticRelation D = 0 := by
      rw [hD]
      have hlin : quadraticRelation (q - q') = quadraticRelation q - quadraticRelation q' := by
        simp [quadraticRelation, sub_smul, Finset.sum_sub_distrib]
      rw [hlin, hqq, sub_self]
    have := d2_quadraticRelation D a b
    rw [h0, map_zero] at this
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact this.symm
  set S := projectedDiagonal (pa ij) (pb ij) (pb_ne_pa ij) D
    (fun xy => p (insertPair ij t xy)) with hS
  have hSS : S = -S := by
    rw [hS]
    unfold projectedDiagonal
    rw [← Finset.sum_neg_distrib]
    rw [← (Equiv.prodComm σ σ).sum_comp]
    refine Finset.sum_congr rfl fun xy _ => ?_
    obtain ⟨x, y⟩ := xy
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [hanti, map_neg, neg_mul]
    congr 2
    exact collide_swap p hp ij t y x
  have h2 : (2 : K) • S = 0 := by
    rw [two_smul]; nth_rewrite 2 [hSS]; exact add_neg_cancel S
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

end Swap

/-! ## Stability of the carrier under the loop operators -/

section Stable

variable {m : ℕ}

/-- The coadjoint derivation, on coefficient matrices. -/
def adMatrix (x : σ) (q : σ × σ → K) : σ × σ → K := fun cd =>
  (∑ a, q (a, cd.2) * f x a cd.1) + ∑ b, q (cd.1, b) * f x b cd.2

/-- Stability of the span of the relations under the coadjoint derivations. -/
def RelationsStable (Q : ρ → σ × σ → K) : Prop :=
  ∀ x r, quadraticRelation (adMatrix f x (Q r)) ∈
    Submodule.span K (Set.range fun s => quadraticRelation (Q s))

omit [Fintype σ] [DecidableEq σ] in
theorem insertPair_apply_fst (ij : IncreasingPair (Fin m)) (t : Fin m → σ) (xy : σ × σ) :
    insertPair ij t xy ij.1.1 = xy.1 := by
  simp [insertPair, ne_of_lt ij.2]

omit [Fintype σ] [DecidableEq σ] in
theorem insertPair_apply_snd (ij : IncreasingPair (Fin m)) (t : Fin m → σ) (xy : σ × σ) :
    insertPair ij t xy ij.1.2 = xy.2 := by
  simp [insertPair]

omit [Fintype σ] [DecidableEq σ] in
theorem insertPair_apply_other (ij : IncreasingPair (Fin m)) (t : Fin m → σ) (xy : σ × σ)
    {k : Fin m} (hi : k ≠ ij.1.1) (hj : k ≠ ij.1.2) : insertPair ij t xy k = t k := by
  simp [insertPair, hi, hj]

omit [Fintype σ] [DecidableEq σ] in
theorem update_insertPair_fst (ij : IncreasingPair (Fin m)) (t : Fin m → σ) (xy : σ × σ) (c : σ) :
    Function.update (insertPair ij t xy) ij.1.1 c = insertPair ij t (c, xy.2) := by
  simp only [insertPair]
  rw [Function.update_comm (ne_of_lt ij.2).symm, Function.update_idem]

omit [Fintype σ] [DecidableEq σ] in
theorem update_insertPair_snd (ij : IncreasingPair (Fin m)) (t : Fin m → σ) (xy : σ × σ) (c : σ) :
    Function.update (insertPair ij t xy) ij.1.2 c = insertPair ij t (xy.1, c) := by
  simp only [insertPair, Function.update_idem]

omit [Fintype σ] [DecidableEq σ] in
theorem update_insertPair_other (ij : IncreasingPair (Fin m)) (t : Fin m → σ) (xy : σ × σ)
    {k : Fin m} (hi : k ≠ ij.1.1) (hj : k ≠ ij.1.2) (c : σ) :
    Function.update (insertPair ij t xy) k c = insertPair ij (Function.update t k c) xy := by
  simp only [insertPair]
  rw [Function.update_comm (Ne.symm hj), Function.update_comm (Ne.symm hi)]

theorem collisionMap_zr_fst (ij : IncreasingPair (Fin m)) (s : ℕ) :
    collisionMap (pa ij) (pb ij) (pb_ne_pa ij) (zr (K := K) ij.1.1 ^ s) =
      collisionMap (pa ij) (pb ij) (pb_ne_pa ij) (zr (K := K) ij.1.2 ^ s) := by
  show collisionMap (pa ij) (pb ij) (pb_ne_pa ij) (X (pa ij) ^ s) =
    collisionMap (pa ij) (pb ij) (pb_ne_pa ij) (X (pb ij) ^ s)
  rw [map_pow, map_pow, collisionMap_X_self, collisionMap_X_other _ _ _ _ (pb_ne_pa ij)]

omit [DecidableEq σ] in
/-- The collision equation is linear in the relation matrix. -/
theorem currentReadback_sum {ι : Type*} (S : Finset ι) (c : ι → K) (q : ι → σ × σ → K)
    (ij : IncreasingPair (Fin m)) (t : Fin m → σ) (p : TensorPolynomial (K := K) (σ := σ) m 0) :
    currentReadback (∑ i ∈ S, c i • q i) ij t p =
      ∑ i ∈ S, C (c i) * currentReadback (q i) ij t p := by
  classical
  unfold currentReadback projectedDiagonal
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun xy _ => ?_
  ring

end Stable

section Main

variable {m : ℕ}

omit [DecidableEq σ] in
/-- The pair term of the loop operator, in matrix form. -/
theorem pair_terms (q : σ × σ → K) (ij : IncreasingPair (Fin m)) (t : Fin m → σ) (x : σ)
    (Z : MvPolynomial {y : Particle m 0 // y ≠ pa ij} K)
    (p : TensorPolynomial (K := K) (σ := σ) m 0) :
    (∑ xy : σ × σ, ∑ c, C (q xy) * (Z * (C (f x xy.1 c) * collide p ij t (c, xy.2)))) +
      (∑ xy : σ × σ, ∑ c, C (q xy) * (Z * (C (f x xy.2 c) * collide p ij t (xy.1, c)))) =
      Z * currentReadback (adMatrix f x q) ij t p := by
  unfold currentReadback projectedDiagonal adMatrix
  simp only [map_add, map_sum, map_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul, Fintype.sum_prod_type, mul_add]
  have e1 : ∀ g : σ → σ → σ → MvPolynomial {y : Particle m 0 // y ≠ pa ij} K,
      ∑ a, ∑ b, ∑ c, g a b c = ∑ c, ∑ b, ∑ a, g a b c := by
    intro g
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm]
    exact Finset.sum_comm
  congr 1
  · rw [e1]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun a _ => ?_
    ring
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

omit [DecidableEq σ] in
theorem quadraticRelation_sum {ι : Type*} (S : Finset ι) (c : ι → K) (q : ι → σ × σ → K) :
    quadraticRelation (∑ i ∈ S, c i • q i) = ∑ i ∈ S, c i • quadraticRelation (q i) := by
  classical
  unfold quadraticRelation
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, Finset.smul_sum,
    smul_smul]
  exact Finset.sum_comm

/-- The coadjoint-transformed relation also vanishes on carrier vectors. -/
theorem readback_adMatrix_eq_zero [CharZero K] {Q : ρ → σ × σ → K} [Fintype ρ]
    (hQ : RelationsStable f Q) {p : TensorPolynomial (K := K) (σ := σ) m 0}
    (hp : p ∈ currentCarrier Q m 0) (x : σ) (r : ρ) (ij : IncreasingPair (Fin m))
    (t : Fin m → σ) : currentReadback (adMatrix f x (Q r)) ij t p = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hQ x r)
  rw [readback_congr p hp.1 ij t _ (∑ s, c s • Q s) (by rw [quadraticRelation_sum, hc]),
    currentReadback_sum]
  exact Finset.sum_eq_zero fun s _ => by rw [hp.2 s ij t, mul_zero]

/-- **The current equations are preserved by the loop operators.** -/
theorem loopOp_equations [CharZero K] {Q : ρ → σ × σ → K} [Fintype ρ]
    (hQ : RelationsStable f Q) {p : TensorPolynomial (K := K) (σ := σ) m 0}
    (hp : p ∈ currentCarrier Q m 0) (x : σ) (s : ℕ) :
    CurrentEquations Q (loopOp f m x s p) := by
  intro r ij t
  have hne : ij.1.1 ≠ ij.1.2 := ne_of_lt ij.2
  unfold currentReadback projectedDiagonal
  simp only [loopOp, LinearMap.coe_mk, AddHom.coe_mk, map_neg, map_sum, map_mul, mul_neg,
    Finset.sum_neg_distrib, neg_eq_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  set Zc : Fin m → MvPolynomial {y : Particle m 0 // y ≠ pa ij} K := fun k =>
    collisionMap (pa ij) (pb ij) (pb_ne_pa ij) (zr k ^ s) with hZc
  have hCc : ∀ a : K, collisionMap (pa ij) (pb ij) (pb_ne_pa ij) (C a) = C a := fun a => by
    simp [collisionMap]
  simp only [hCc, map_pow]
  rw [Finset.sum_eq_add_of_mem ij.1.1 ij.1.2 (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · -- the two pair terms
    simp only [insertPair_apply_fst, insertPair_apply_snd, update_insertPair_fst,
      update_insertPair_snd]
    have hZ := collisionMap_zr_fst (K := K) ij s
    simp only [map_pow] at hZ
    rw [hZ]
    have h := pair_terms f (Q r) ij t x
      (collisionMap (pa ij) (pb ij) (pb_ne_pa ij) (zr (K := K) ij.1.2) ^ s) p
    simp only [collide] at h
    rw [h, readback_adMatrix_eq_zero f hQ hp x r ij t, mul_zero]
  · -- spectator terms
    intro k _ hk
    simp only [insertPair_apply_other ij t _ hk.1 hk.2,
      update_insertPair_other ij t _ hk.1 hk.2]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    have h0 := hp.2 r ij (Function.update t k c)
    unfold currentReadback projectedDiagonal at h0
    calc _ = collisionMap (pa ij) (pb ij) (pb_ne_pa ij) (zr k) ^ s * C (f x (t k) c) *
          ∑ xy : σ × σ, C (Q r xy) * collisionMap (pa ij) (pb ij) (pb_ne_pa ij)
            (p (insertPair ij (Function.update t k c) xy)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun xy _ => ?_
            ring
      _ = 0 := by rw [h0, mul_zero]

omit [DecidableEq σ] in
/-- **Symmetry is preserved by the loop operators.** -/
theorem loopOp_symmetric {p : TensorPolynomial (K := K) (σ := σ) m 0} (hp : Symmetric p)
    (x : σ) (s : ℕ) : Symmetric (loopOp f m x s p) := by
  intro e g he t
  simp only [loopOp, LinearMap.coe_mk, AddHom.coe_mk, map_neg, map_sum, map_mul, map_pow,
    rename_C]
  congr 1
  conv_rhs => rw [← Equiv.sum_comp g]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz : rename e (zr (K := K) i) = zr (g i) := by
    simp only [zr, rename_X, he i]
  rw [hz]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hp e g he, Function.update_comp_equiv]
  simp

/-- **The carrier is stable under the loop operators.** -/
theorem loopOp_mem [CharZero K] {Q : ρ → σ × σ → K} [Fintype ρ] (hQ : RelationsStable f Q)
    {p : TensorPolynomial (K := K) (σ := σ) m 0} (hp : p ∈ currentCarrier Q m 0) (x : σ)
    (s : ℕ) : loopOp f m x s p ∈ currentCarrier Q m 0 :=
  ⟨loopOp_symmetric f hp.1 x s, loopOp_equations f hQ hp x s⟩

/-- The constant highest-weight vector `δ_{(c₀,…,c₀)}`. -/
def deltaVec (m : ℕ) (c₀ : σ) : TensorPolynomial (K := K) (σ := σ) m 0 :=
  fun t => if t = fun _ => c₀ then 1 else 0

theorem deltaVec_mem {Q : ρ → σ × σ → K} (c₀ : σ) (hdiag : ∀ r, Q r (c₀, c₀) = 0) :
    deltaVec (K := K) m c₀ ∈ currentCarrier Q m 0 := by
  refine ⟨fun e g he t => ?_, fun r ij t => ?_⟩
  · simp only [deltaVec]
    have : (t ∘ g.symm = fun _ => c₀) ↔ (t = fun _ => c₀) := by
      constructor
      · intro h; funext k; have := congrFun h (g k); simpa using this
      · intro h; subst h; rfl
    split_ifs with h1 h2 h2 <;> simp_all
  · unfold currentReadback projectedDiagonal
    refine Finset.sum_eq_zero fun xy _ => ?_
    simp only [deltaVec]
    split_ifs with h
    · have h1 := congrFun h ij.1.1
      have h2 := congrFun h ij.1.2
      rw [insertPair_apply_fst] at h1
      rw [insertPair_apply_snd] at h2
      obtain ⟨x, y⟩ := xy
      simp only at h1 h2
      subst h1 h2
      rw [hdiag, map_zero, zero_mul]
    · rw [map_zero, mul_zero]

/-- Words of loop operators applied to a vector. -/
def applyWord (m : ℕ) : List (σ × ℕ) → TensorPolynomial (K := K) (σ := σ) m 0 →
    TensorPolynomial (K := K) (σ := σ) m 0
  | [], v => v
  | (xs :: l), v => loopOp f m xs.1 xs.2 (applyWord m l v)

/-- **The cyclic `g[t]`-module `M_m = U(g[t]) · δ_{c₀}`.** -/
def Mspace (m : ℕ) (c₀ : σ) : Submodule K (TensorPolynomial (K := K) (σ := σ) m 0) :=
  Submodule.span K (Set.range fun l => applyWord f m l (deltaVec m c₀))

/-- **Step B5: `M_m ⊂ W_m`.** -/
theorem Mspace_le [CharZero K] {Q : ρ → σ × σ → K} [Fintype ρ] (hQ : RelationsStable f Q)
    (c₀ : σ) (hdiag : ∀ r, Q r (c₀, c₀) = 0) : Mspace f m c₀ ≤ currentCarrier Q m 0 := by
  rw [Mspace, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  induction l with
  | nil => exact deltaVec_mem c₀ hdiag
  | cons xs l ih => exact loopOp_mem f hQ ih xs.1 xs.2

end Main

/-! ## The matrix derivation is the coadjoint derivation of `Sym g` -/

section Der

/-- The coadjoint derivation of the polynomial ring on the basis. -/
def adDer (x : σ) : Derivation K (MvPolynomial σ K) (MvPolynomial σ K) :=
  mkDerivation K fun i => ∑ c, f x i c • X c

omit [DecidableEq σ] in
theorem triple_rev {R : Type*} [AddCommMonoid R] (g : σ → σ → σ → R) :
    ∑ a, ∑ b, ∑ c, g a b c = ∑ c, ∑ b, ∑ a, g a b c := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm]
  exact Finset.sum_comm

omit [DecidableEq σ] in
theorem quadraticRelation_adMatrix (x : σ) (q : σ × σ → K) :
    quadraticRelation (adMatrix f x q) = adDer f x (quadraticRelation q) := by
  unfold quadraticRelation adMatrix
  simp only [map_sum, Derivation.map_smul, Derivation.leibniz, adDer, mkDerivation_X,
    smul_eq_mul, add_smul, Finset.sum_add_distrib, Finset.sum_smul, Finset.mul_sum,
    Finset.smul_sum, Fintype.sum_prod_type, smul_add, mul_smul_comm]
  rw [add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
    rw [smul_smul, mul_comm]
  · rw [triple_rev]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    rw [smul_smul, mul_comm, mul_comm (X c) (X b)]

end Der

end

end VOA.DeligneAudit.SectorLoop

section AxiomAudit
#print axioms VOA.DeligneAudit.SectorLoop.readback_congr
#print axioms VOA.DeligneAudit.SectorLoop.loopOp_mem
#print axioms VOA.DeligneAudit.SectorLoop.Mspace_le
end AxiomAudit
