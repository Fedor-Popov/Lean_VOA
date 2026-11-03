/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.DeformationCurrentModes

/-!
# Current operators on the first-order state space

A current acts on a pair (v,v₁), representing v+t v₁, by the block operator
(v,v₁) ↦ (a₍ₙ₎v, a¹₍ₙ₎v+a₍ₙ₎v₁). Regularity of the correction on current pairs
makes these actual operators obey the undeformed affine commutator. A graded
correction also gives the usual degree covariance. These statements concern
operators on the whole first-order space; they impose no CFT-type assumption
on that space and do not yet identify its cyclic subspace with the closed carrier.
-/
namespace VOA.Deform
open Module (End)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V} (D : FirstOrderDeformation W)

/-- The ordinary commutator on two weight-one states, with its scalar vacuum
pairing exposed. Only the zero and first products survive in Jacobi. -/
theorem current_mode_commutator {a b : V} (ha : a ∈ W.grading 1)
    (hb : b ∈ W.grading 1) (β : ℂ) (hp : W.smul a 1 b = β • W.vacuum)
    (x : V) (m n : ℤ) :
    W.smul a m (W.smul b n x) - W.smul b n (W.smul a m x) =
      W.smul (W.smul a 0 b) (m + n) x +
        if m + n = 0 then ((m : ℂ) * β) • x else 0 := by
  have h := W.jacobi a b x 0 m n
  rw [finsum_eq_single _ (0 : ℤ)
    (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])] at h
  simp only [cbz_zero_left, mul_one, one_smul, negOnePow,
    Even.zero, if_pos, zero_add, add_zero, sub_zero] at h
  rw [h]
  let F : ℤ → V := fun i => cbz m i • W.smul (W.smul a i b) (m + n - i) x
  have hsupp : Function.support F ⊆ (↑({0, 1} : Finset ℤ) : Set ℤ) := by
    intro i hi
    by_contra hh
    have h0 : i ≠ 0 := fun h => hh (by simp [h])
    have h1 : i ≠ 1 := fun h => hh (by simp [h])
    apply hi
    dsimp [F]
    by_cases hn : i < 0
    · rw [cbz_apply_neg m hn, zero_smul]
    · rw [current_product_high ha hb (by omega), PreVertexAlgebra.smul_zero_left, smul_zero]
  change (∑ᶠ i : ℤ, F i) = _
  rw [finsum_eq_sum_of_support_subset F hsupp]
  have hb1 : cbz m 1 = (m : ℂ) := by simp [cbz, gBinom]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton, F, cbz_zero, one_smul, sub_zero, hp, hb1,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_vacuum_left]
  by_cases hmn : m + n = 0
  · simp [hmn, smul_smul]
  · have hmn' : m + n - 1 ≠ -1 := by omega
    simp [hmn, hmn']

/-- The mode of a pure constant state on the first-order extension. The first
coordinate is the ordinary action; the second contains both the correction
acting on the constant term and the ordinary action on the tangent term. -/
def liftedMode (a : V) (n : ℤ) : End ℂ (V × V) where
  toFun x := (W.smul a n x.1, D.smul₁ a n x.1 + W.smul a n x.2)
  map_add' x y := by
    apply Prod.ext
    · exact W.smul_add_right a n x.1 y.1
    · simp only [Prod.fst_add, Prod.snd_add, D.smul₁_add_right, W.smul_add_right]
      abel
  map_smul' r x := by
    apply Prod.ext
    · exact W.smul_smul_right a r n x.1
    · simp only [Prod.smul_fst, Prod.smul_snd, D.smul₁_smul_right,
        W.smul_smul_right, RingHom.id_apply, smul_add]

/-- The block formula for evaluating a lifted mode. -/
@[simp] theorem liftedMode_apply (a : V) (n : ℤ) (x : V × V) :
    liftedMode D a n x = (W.smul a n x.1, D.smul₁ a n x.1 + W.smul a n x.2) := rfl

/-- Lifted modes depend linearly on the acting state, as required for a Lie
representation of a whole current algebra rather than only chosen generators. -/
def liftedModeLinear (n : ℤ) : V →ₗ[ℂ] End ℂ (V × V) where
  toFun a := liftedMode D a n
  map_add' a b := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> simp only [liftedMode_apply, LinearMap.add_apply,
      W.smul_add_left, D.smul₁_add_left, Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' r a := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> simp only [liftedMode_apply, LinearMap.smul_apply,
      W.smul_smul_left, D.smul₁_smul_left, RingHom.id_apply,
      Prod.smul_fst, Prod.smul_snd, smul_add]

/-- Regular current corrections give genuine affine commutators on V × V.
The central coefficient is unchanged; the off-diagonal relation is exactly
the previously proved differentiated commutator. -/
theorem liftedMode_comm_of_regular (hreg : D.Regular) {a b : V}
    (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1)
    (β : ℂ) (hp : W.smul a 1 b = β • W.vacuum) (m n : ℤ) :
    ⁅liftedMode D a m, liftedMode D b n⁆ =
      liftedMode D (W.smul a 0 b) (m + n) +
        if m + n = 0 then ((m : ℂ) * β) • (1 : End ℂ (V × V)) else 0 := by
  by_cases hmn : m + n = 0
  all_goals
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · have h := current_mode_commutator ha hb β hp x.1 m n
      simpa only [hmn, if_true, if_false, LieRing.of_associative_ring_bracket,
        LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, liftedMode_apply,
        Prod.fst_sub, Prod.fst_add, LinearMap.smul_apply, Module.End.one_apply,
        LinearMap.zero_apply, Prod.smul_fst, Prod.fst_zero] using h
    · have h := current_mode_commutator ha hb β hp x.2 m n
      have hd := regular_current_commutator D hreg ha hb x.1 m n
      simp only [hmn, if_true, if_false] at h hd
      simp only [hmn, if_true, if_false, LieRing.of_associative_ring_bracket,
        LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, liftedMode_apply,
        Prod.snd_sub, Prod.snd_add, LinearMap.smul_apply, Module.End.one_apply,
        LinearMap.zero_apply, Prod.smul_snd, Prod.snd_zero, W.smul_add_right]
      rw [eq_sub_of_add_eq h.symm, ← hd]
      abel


/-- Any operator lowering weight by n has commutator n times itself with
minus L₀. The proof uses the grading on homogeneous vectors and then their
spanning property, so the relation holds on every state. -/
theorem lowering_operator_degree_comm (F : End ℂ V) (n : ℤ)
    (hF : ∀ k v, v ∈ W.grading k → F v ∈ W.grading (k - n)) :
    ⁅-W.L 0, F⁆ = (n : ℂ) • F := by
  let H : End ℂ V := ⁅-W.L 0, F⁆ - (n : ℂ) • F
  have hz : H = 0 := by
    apply LinearMap.ext
    intro x
    change H x = 0
    have hx : x ∈ ⨆ k, W.grading k := by
      rw [W.isInternal.submodule_iSup_eq_top]
      trivial
    refine Submodule.iSup_induction W.grading (motive := fun y => H y = 0) hx ?_ ?_ ?_
    · intro k v hv
      simp only [H, LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
        Module.End.mul_apply, LinearMap.neg_apply, LinearMap.smul_apply, map_neg]
      rw [W.L_zero_grading _ (hF k v hv), W.L_zero_grading _ hv, map_smul]
      push_cast
      module
    · exact H.map_zero
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  exact sub_eq_zero.mp hz

/-- The affine degree derivation on the first-order space is minus L₀ on each
coordinate. Its zero eigenspace is not assumed to be one dimensional. -/
def liftedDegree : End ℂ (V × V) := (-W.L 0).prodMap (-W.L 0)

/-- Explicit coordinate action of the lifted grading derivation. -/
@[simp] theorem liftedDegree_apply (x : V × V) :
    liftedDegree (W := W) x = (-W.L 0 x.1, -W.L 0 x.2) := rfl

/-- A graded correction gives the correct affine degree commutator for every
lifted current mode, including its first-order off-diagonal block. -/
theorem liftedDegree_comm (hD : D.IsGraded) {a : V} (ha : a ∈ W.grading 1) (n : ℤ) :
    ⁅liftedDegree (W := W), liftedMode D a n⁆ = (n : ℂ) • liftedMode D a n := by
  have hA := lowering_operator_degree_comm (W := W) (mode (W.Y a) n) n (by
    intro k v hv
    have h := W.smul_mem_grading ha hv n
    simpa only [show 1 + k - n - 1 = k - n by omega] using h)
  have hB := lowering_operator_degree_comm (W := W) (mode (D.Y1 a) n) n (by
    intro k v hv
    have h := hD 1 k a ha v hv n
    simpa only [show 1 + k - n - 1 = k - n by omega] using h)
  have ha' (v : V) : -W.L 0 (W.smul a n v) - W.smul a n (-W.L 0 v) =
      (n : ℂ) • W.smul a n v := congrArg (fun F : End ℂ V => F v) hA
  have hb' (v : V) : -W.L 0 (D.smul₁ a n v) - D.smul₁ a n (-W.L 0 v) =
      (n : ℂ) • D.smul₁ a n v := congrArg (fun F : End ℂ V => F v) hB
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact ha' x.1
  · change -W.L 0 (D.smul₁ a n x.1 + W.smul a n x.2) -
        (D.smul₁ a n (-W.L 0 x.1) + W.smul a n (-W.L 0 x.2)) =
      (n : ℂ) • (D.smul₁ a n x.1 + W.smul a n x.2)
    rw [map_add, neg_add, eq_add_of_sub_eq (hb' x.1), eq_add_of_sub_eq (ha' x.2)]
    module

/-- Nonnegative lifted current modes annihilate the pure vacuum. This follows
from ordinary creation and its first-order version, without regularity. -/
theorem liftedMode_vacuum {a : V} (n : ℤ) (hn : 0 ≤ n) :
    liftedMode D a n (W.vacuum, 0) = 0 := by
  simp [liftedMode_apply, W.toPreVertexAlgebra.smul_vacuum_nonneg a hn,
    D.smul₁_vacuum_right a n (by omega)]

/-- The pure vacuum has degree zero in both coordinates. -/
theorem liftedDegree_vacuum : liftedDegree (W := W) (W.vacuum, 0) = 0 := by
  simp [liftedDegree_apply, W.L_zero_grading W.vacuum W.vacuum_mem]

/-- If each subspace lies in a distinct member of an independent family, its
intersection with the sum of all subspaces recovers exactly that member.
Applied to eigenspaces, this says that taking an image cannot hide a weight-zero
vector among nonzero weights. No surjectivity of the sum is required. -/
theorem iSup_inf_eq_of_le_independent {ι : Type*} {p q : ι → Submodule ℂ V}
    (hpq : ∀ i, p i ≤ q i) (hq : iSupIndep q) (i : ι) :
    (⨆ j, p j) ⊓ q i = p i := by
  have hsplit : ⨆ j, p j = p i ⊔ ⨆ (j) (_ : j ≠ i), p j := by
    refine le_antisymm (iSup_le fun j => ?_)
      (sup_le (le_iSup p i) (iSup₂_le fun j _ => le_iSup p j))
    by_cases hj : j = i
    · subst hj; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂ (f := fun (j : ι) (_ : j ≠ i) => p j) j hj)
  have hbot : (⨆ (j) (_ : j ≠ i), p j) ⊓ q i = ⊥ := by
    rw [inf_comm]
    exact le_bot_iff.mp
      (le_trans (inf_le_inf_left (q i) (iSup₂_mono fun j _ => hpq j)) (hq i).le_bot)
  have hmod := sup_inf_assoc_of_le (α := Submodule ℂ V) (x := p i)
    (⨆ (j) (_ : j ≠ i), p j) (hpq i)
  rw [hsplit, hmod, hbot, sup_bot_eq]

/-- The integer weight space is exactly the corresponding L₀ eigenspace.
Containment follows from the VOA grading law; completeness and independence of
eigenspaces prevent any further eigenvectors outside that homogeneous piece. -/
theorem grading_eq_L_zero_eigenspace (n : ℤ) :
    W.grading n = Module.End.eigenspace (W.L 0) (n : ℂ) := by
  have h := iSup_inf_eq_of_le_independent (p := W.grading)
    (q := fun j : ℤ => Module.End.eigenspace (W.L 0) (j : ℂ))
    (fun j v hv => Module.End.mem_eigenspace_iff.mpr (W.L_zero_grading v hv))
    ((Module.End.eigenspaces_iSupIndep (W.L 0)).comp Int.cast_injective) n
  simpa only [W.isInternal.submodule_iSup_eq_top, top_inf_eq] using h.symm

end VOA.Deform
