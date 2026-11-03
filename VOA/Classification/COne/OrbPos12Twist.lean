import VOA.Classification.COne.OrbPos11Dictionary
import VOA.Huang.AndersonMooreMain
import Mathlib.NumberTheory.Niven

/-! Finite order of the actual conformal twist, using strong rationality only.
This does not use positivity or rigidity of the ordinary module category. -/
noncomputable section
namespace VOA.Classification.COne.OrbPos12
open VOA CategoryTheory VOA.Huang.TensorCat VOA.Huang.FusionUnit
open VOA.Huang.TensorCat.BraidRibbon

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The actual conformal twist on the carrier, as a linear endomorphism. -/
def twistEnd (X : Ordinary W) : Module.End ℂ X.carrier := (twistIso X).hom.val

/-- Rational conformal phases have finite order. -/
theorem tw_rat_finiteOrder (q : ℚ) : IsOfFinOrder (tw (q : ℂ)) := by
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨2 * (2 * q).den, by positivity, ?_⟩
  have he : tw (q : ℂ) = Complex.exp (((2 * q : ℚ) : ℂ) * Real.pi * Complex.I) := by
    unfold tw
    congr 1
    push_cast
    ring
  rw [he]
  exact Complex.exp_rat_mul_pi_mul_I_pow_two_mul_den (2 * q)

/-- Naturality persists under every nonnegative power. -/
theorem twistEnd_pow_natural {X Y : Ordinary W} (f : X ⟶ Y) (n : ℕ)
    (x : X.carrier) : (twistEnd Y ^ n) (f.val x) = f.val ((twistEnd X ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    exact congrArg (fun t : X ⟶ Y => t.val ((twistEnd X ^ n) x)) (twist_naturality f)

/-- The twist of an irreducible ordinary module has finite order, without `Nice`. -/
theorem twistEnd_finiteOrder_of_irreducible (hW : StronglyRational W)
    (X : Ordinary W) (hX : X.isMod.IsIrreducible) : IsOfFinOrder (twistEnd X) := by
  obtain ⟨h, hh⟩ := X.isMod.exists_hasConformalWeight_of_irreducible hX
  obtain ⟨q, hq⟩ := (VOA.Huang.AndersonMoore.dlmRationalityInput_of_pbw_am
    VOA.Huang.ZhuModData.zhuPBWBottomInput_of_pbw V W hW).2 X.carrier X.isMod hX h hh
  have ht : twistEnd X = tw (q : ℂ) • (1 : Module.End ℂ X.carrier) := by
    have he := twistIso_eq_smul_of_weights X h hh.2
    subst h
    exact congrArg Subtype.val he
  obtain ⟨n, hn, hp⟩ := (tw_rat_finiteOrder q).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, by rw [ht, smul_pow, hp, one_pow, one_smul]⟩

/-- Every ordinary module has a finite-order conformal twist. A finite simple
presentation supplies a common period; the carrier need not be finite-dimensional. -/
theorem twistEnd_finiteOrder (hW : StronglyRational W) (X : Ordinary W) :
    IsOfFinOrder (twistEnd X) := by
  classical
  obtain ⟨P⟩ := simplePresentation_nonempty hW
    (VOA.Huang.PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hW) X
  have hp (j : Fin P.size) : IsOfFinOrder (twistEnd (Ordinary.of (P.part j).isMod)) :=
    twistEnd_finiteOrder_of_irreducible hW _ (P.irreducible j)
  obtain ⟨n, hn, hpow⟩ := (IsOfFinOrder.pi hp).exists_pow_eq_one
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  ext x
  conv_lhs => rw [← P.total x]
  rw [map_sum]
  have he (j : Fin P.size) : twistEnd (Ordinary.of (P.part j).isMod) ^ n = 1 :=
    congrFun hpow j
  calc
    _ = ∑ j, (P.inc j).val ((P.proj j).val x) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [twistEnd_pow_natural (P.inc j), he]
      rfl
    _ = _ := P.total x

end VOA.Classification.COne.OrbPos12
