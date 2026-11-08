import VOA.Moonshine.MoonshineCNBorcherdsData
import Mathlib.Order.CompactlyGenerated.Basic

/-! The positive cone and opposite parabolic, as complementary abstract Lie subalgebras. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

theorem borcherdsParabolicDegree_add {α β : ℤ × ℤ}
    (hα : ¬ borcherdsPositiveCone α) (hβ : ¬ borcherdsPositiveCone β)
    (hsα : borcherdsRootSupport α) (hsβ : borcherdsRootSupport β) :
    ¬ borcherdsPositiveCone (α + β) := by
  simp only [borcherdsRootSupport, borcherdsPositiveRoot, borcherdsPositiveCone,
    borcherdsRealRoot, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero,
    Prod.fst_neg, Prod.snd_neg, Prod.fst_add, Prod.snd_add] at *
  omega

namespace BorcherdsData

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)

def weightSpan (P : ℤ × ℤ → Prop) : Submodule ℂ g :=
  ⨆ γ, ⨆ (_ : P γ), D.weightSpace γ

theorem weightSpan_bracket (P : ℤ × ℤ → Prop)
    (hP : ∀ α β, P α → P β → borcherdsRootSupport α → borcherdsRootSupport β → P (α + β))
    (x y : g) (hx : x ∈ D.weightSpan P) (hy : y ∈ D.weightSpan P) :
    ⁅x, y⁆ ∈ D.weightSpan P := by
  induction hx using Submodule.iSup_induction' with
  | mem α x hx =>
      induction hx using Submodule.iSup_induction' with
      | mem hα x hx =>
          induction hy using Submodule.iSup_induction' with
          | mem β y hy =>
              induction hy using Submodule.iSup_induction' with
              | mem hβ y hy =>
                  by_cases hx0 : x = 0
                  · simp [hx0]
                  by_cases hy0 : y = 0
                  · simp [hy0]
                  have hsα := D.root_support α (fun h => hx0 (by simpa [h] using hx))
                  have hsβ := D.root_support β (fun h => hy0 (by simpa [h] using hy))
                  exact Submodule.mem_iSup_of_mem (α + β)
                    (Submodule.mem_iSup_of_mem (hP α β hα hβ hsα hsβ) (D.bracket_weight hx hy))
              | zero => simp
              | add y z _ _ hy hz => simpa only [lie_add] using Submodule.add_mem _ hy hz
          | zero => simp
          | add y z _ _ hy hz => simpa only [lie_add] using Submodule.add_mem _ hy hz
      | zero => simp
      | add x z _ _ hx hz => simpa only [add_lie] using Submodule.add_mem _ hx hz
  | zero => simp
  | add x z _ _ hx hz => simpa only [add_lie] using Submodule.add_mem _ hx hz

/-- The subalgebra with both Borcherds coordinates positive. -/
def positivePart : LieSubalgebra ℂ g where
  __ := D.weightSpan borcherdsPositiveCone
  lie_mem' {x y} hx hy := D.weightSpan_bracket borcherdsPositiveCone
    (fun _ _ hα hβ _ _ => borcherdsPositiveCone_add hα hβ) x y hx hy

/-- The opposite parabolic: the Cartan, both real root lines, and the negative cone. -/
def parabolicPart : LieSubalgebra ℂ g where
  __ := D.weightSpan (fun γ => ¬ borcherdsPositiveCone γ)
  lie_mem' {x y} hx hy := D.weightSpan_bracket (fun γ => ¬ borcherdsPositiveCone γ)
    (fun _ _ => borcherdsParabolicDegree_add) x y hx hy

/-- The two subalgebras are complementary as vector spaces, the input for relative PBW. -/
theorem positive_parabolic_isCompl :
    IsCompl D.positivePart.toSubmodule D.parabolicPart.toSubmodule := by
  constructor
  · exact D.weight_internal.submodule_iSupIndep.disjoint_biSup_biSup
      (s := {γ | borcherdsPositiveCone γ}) (t := {γ | ¬ borcherdsPositiveCone γ})
      (Set.disjoint_left.mpr (fun _ h h' => h' h))
  · apply codisjoint_iff.mpr
    apply top_unique
    rw [← D.weight_internal.submodule_iSup_eq_top]
    apply iSup_le
    intro γ
    by_cases hγ : borcherdsPositiveCone γ
    · exact le_sup_of_le_left (le_iSup_of_le γ (le_iSup_of_le hγ le_rfl))
    · exact le_sup_of_le_right (le_iSup_of_le γ (le_iSup_of_le hγ le_rfl))

end BorcherdsData
end VOA.Moonshine.ConwayNorton
