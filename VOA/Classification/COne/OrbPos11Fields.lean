import VOA.Classification.COne.OrbPos11Support

/-! # Reconstructing the candidate twisted module

The candidate uses the given algebra action, on its original carrier and
grading. All `TwistedModule` fields other than twisted Jacobi are proved here.
The constructor is explicitly conditional on that remaining coefficient
identity; it does not assert the monodromy-to-Jacobi theorem.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbPos11
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct VOA.Huang.TensorCat
open VOA.Huang.HKLRational CategoryTheory MonoidalCategory OrbPos9 OrbPos10 OrbPos2

variable (G : Subgroup (Aut (V2m 1 le_rfl)))
  (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR)
  (X : Ordinary (orbifoldVOA G))
  (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X)

/-- Action laws with the specified categorical and algebra structures. -/
def ActionLaws : Prop :=
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  IsLeftAct a

set_option maxHeartbeats 1000000 in
-- The pinned unit and the concrete lattice scalar structures need unfolding.
/-- The action restricts to the *given* ordinary U-module on every complex mode. -/
theorem actionIntertwiner_fixed (ha : ActionLaws G hSR E X a) (z : ℂ)
    (v : (orbifold G).carrier) (x : X.carrier) :
    (actionIntertwiner G hSR X a).val z v.1 x = moduleModes X.isMod z v x := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  change IsLeftAct a at ha
  have hunit : tensorHom (fusionChoice_pbw hSR) (unitInclusion G) (𝟙 X) ≫ a =
      (leftUnitor (fusionChoice_pbw hSR) X).hom := by
    simpa only [E.one_eq] using ha.one_act
  have ht := tensorHom_intertwiner (fusionChoice_pbw hSR) (unitInclusion G) (𝟙 X) z v x
  rw [Ordinary.id_apply] at ht
  change a.val (((fusionChoice_pbw hSR) (ambient G) X).intertwiner.val z
    ((unitInclusion G).val v) x) = _
  rw [← ht, ← Ordinary.comp_apply, hunit, leftUnitor_intertwiner]
  rfl

/-- Restriction at integer modes, with arbitrary positive denominator. -/
theorem actionModes_fixed (ha : ActionLaws G hSR E X a) {N : ℕ} (hN : 0 < N)
    (v : (orbifold G).carrier) (k : ℤ) (x : X.carrier) :
    actionModes G hSR X a N v.1 ((N : ℤ) * k) x = mode (X.isMod.YM v) k x := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  change (actionIntertwiner G hSR X a).val (((N : ℤ) * k : ℤ) / (N : ℂ)) v.1 x = _
  rw [Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ hn,
    actionIntertwiner_fixed G hSR E X a ha, moduleModes_apply_intCast]

/-- The full fractional vacuum axiom, including off-integer indices. -/
theorem actionModes_vacuum (ha : ActionLaws G hSR E X a) {N : ℕ} (hN : 0 < N) (k : ℤ) :
    actionModes G hSR X a N (V2m 1 le_rfl).vacuum k =
      if k = -(N : ℤ) then 1 else 0 := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  ext x
  change (actionIntertwiner G hSR X a).val ((k : ℂ) / N)
    ((orbifoldVOA G).vacuum : (orbifold G).carrier).1 x = _
  rw [actionIntertwiner_fixed G hSR E X a ha]
  by_cases hk : k = -(N : ℤ)
  · subst k
    simp only [Int.cast_neg, Int.cast_natCast, neg_div, div_self hn]
    rw [show (-1 : ℂ) = ((-1 : ℤ) : ℂ) by norm_num, moduleModes_apply_intCast,
      ← WeakModule.act_def, WeakModule.act_vacuum]
    simp
  · rw [if_neg hk, LinearMap.zero_apply]
    by_cases hi : ∃ m : ℤ, (m : ℂ) = (k : ℂ) / N
    · obtain ⟨m, hm⟩ := hi
      rw [← hm, moduleModes_apply_intCast, ← WeakModule.act_def, WeakModule.act_vacuum]
      apply if_neg
      intro he
      subst m
      apply hk
      have he : (k : ℂ) = -(N : ℂ) := by
        have := (eq_div_iff hn).mp hm
        linear_combination -this
      exact_mod_cast he
    · rw [moduleModes_of_not_int X.isMod (fun m hm => hi ⟨m, hm⟩)]
      rfl

/-- Truncation along a rational grid follows from intertwiner truncation on
the finitely many residue classes. No field associativity is used. -/
theorem actionModes_truncation {N : ℕ} (hN : 0 < N)
    (v : (ambient G).carrier) (x : X.carrier) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k → actionModes G hSR X a N v k x = 0 := by
  classical
  have ht (r : Fin N) := (actionIntertwiner G hSR X a).property.truncation v x
    ((r.val : ℂ) / N)
  choose b hb using ht
  let B : ℤ := ∑ r : Fin N, max (b r) 0
  have hB (r : Fin N) : b r ≤ B :=
    (le_max_left _ _).trans (Finset.single_le_sum (fun i _ => le_max_right (b i) 0)
      (Finset.mem_univ r))
  have hnZ : (0 : ℤ) < N := by exact_mod_cast hN
  have hnC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨B * N, fun k hk => ?_⟩
  let r : Fin N := ⟨(k % N).toNat, by
    have hlt := Int.emod_lt_of_pos k hnZ
    have hpos := Int.emod_nonneg k hnZ.ne'
    omega⟩
  have hr : (r.val : ℤ) = k % N := Int.toNat_of_nonneg (Int.emod_nonneg k hnZ.ne')
  have he : (k : ℂ) / N = (r.val : ℂ) / N + (k / (N : ℤ) : ℤ) := by
    have hd : (k : ℂ) = (r.val : ℂ) + (N : ℂ) * ((k / (N : ℤ) : ℤ) : ℂ) := by
      exact_mod_cast (show k = (r.val : ℤ) + (N : ℤ) * (k / (N : ℤ)) by
        rw [hr, Int.emod_add_mul_ediv])
    rw [hd]
    field_simp
  change (actionIntertwiner G hSR X a).val ((k : ℂ) / N) v x = 0
  rw [he]
  exact hb r _ ((hB r).trans ((Int.le_ediv_iff_mul_le hnZ).mpr hk))

/-- Only twisted Jacobi remains to construct the module from these fields.
The carrier and grading are exactly those of `X`. -/
def actionTwistedModule (ha : ActionLaws G hSR E X a) (g : G)
    (hm : ActionMonodromyThrough G hSR X a g) {N : ℕ} (hN : 0 < N)
    (hJ : TwistedJacobi g.1 N (actionModes G hSR X a N)) :
    TwistedModule g.1 N X.carrier where
  YM := actionModes G hSR X a N
  vacuum_YM := actionModes_vacuum G hSR E X a ha hN
  truncation := actionModes_truncation G hSR X a hN
  support := actionModes_support G hSR X a g hm hN
  jacobi := hJ
  weight := X.isMod.weight
  isInternal := X.isMod.isInternal
  L0_weight α x hx := by
    have he := actionModes_fixed G hSR E X a ha hN (orbifoldVOA G).conformalVector 1 x
    simp only [mul_one] at he
    exact he.trans (X.isMod.L0_weight α x hx)
  finrank := X.isMod.finrank
  boundedBelow := X.isMod.boundedBelow

/-- Reconstruction restricts back to the original U-module, through the identity
linear equivalence, not merely through an equality of lowest weights. -/
def actionTwistedModule_restriction (ha : ActionLaws G hSR E X a) (g : G)
    (hm : ActionMonodromyThrough G hSR X a g) {N : ℕ} (hN : 0 < N)
    (hJ : TwistedJacobi g.1 N (actionModes G hSR X a N)) :
    ModuleEquiv (orbifoldVOA G) X.isMod
      (orbifoldRestriction G g (actionTwistedModule G hSR E X a ha g hm hN hJ) hN) where
  toLinearEquiv := LinearEquiv.refl ℂ X.carrier
  map_act v k x := by
    change mode (X.isMod.YM v) k x =
      mode (restrictedFields (actionTwistedModule G hSR E X a ha g hm hN hJ)
        (orbifold G) v) k x
    rw [mode_restrictedFields]
    exact (actionModes_fixed G hSR E X a ha hN v k x).symm

end VOA.Classification.COne.OrbPos11
