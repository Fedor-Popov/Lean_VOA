import VOA.Moonshine.MoonshineCNBorcherdsParabolic
import Mathlib.Algebra.Lie.Ideal

/-! The Levi factor, the negative cone, and its ideal in the opposite parabolic. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

def borcherdsNegativeCone (γ : ℤ × ℤ) : Prop := borcherdsPositiveCone (-γ)

def borcherdsLeviDegree (γ : ℤ × ℤ) : Prop :=
  γ = 0 ∨ γ = borcherdsRealRoot ∨ γ = -borcherdsRealRoot

namespace BorcherdsData

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)

theorem weightSpace_le_weightSpan {P : ℤ × ℤ → Prop} {γ : ℤ × ℤ} (hγ : P γ) :
    D.weightSpace γ ≤ D.weightSpan P :=
  le_iSup_of_le γ (le_iSup_of_le hγ le_rfl)

theorem weightSpan_mono_predicate {P Q : ℤ × ℤ → Prop}
    (h : ∀ γ, P γ → Q γ) : D.weightSpan P ≤ D.weightSpan Q := by
  exact iSup_le fun γ => iSup_le fun hγ => D.weightSpace_le_weightSpan (h γ hγ)

theorem weightSpan_le_of_supported {P : ℤ × ℤ → Prop} {S : Submodule ℂ g}
    (h : ∀ γ, P γ → borcherdsRootSupport γ → D.weightSpace γ ≤ S) :
    D.weightSpan P ≤ S := by
  refine iSup_le fun γ => iSup_le fun hγ => ?_
  by_cases hs : borcherdsRootSupport γ
  · exact h γ hγ hs
  · rw [D.weight_eq_bot_of_not_supported γ hs]
    exact bot_le

/-- Mixed bracket closure only needs the condition at supported output degrees. -/
theorem weightSpan_bracket_mem (P Q R : ℤ × ℤ → Prop)
    (h : ∀ α β, P α → Q β → borcherdsRootSupport α → borcherdsRootSupport β →
      borcherdsRootSupport (α + β) → R (α + β))
    {x y : g} (hx : x ∈ D.weightSpan P) (hy : y ∈ D.weightSpan Q) :
    ⁅x, y⁆ ∈ D.weightSpan R := by
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
                  have hb := D.bracket_weight hx hy
                  by_cases hs : borcherdsRootSupport (α + β)
                  · exact D.weightSpace_le_weightSpan (h α β hα hβ hsα hsβ hs) hb
                  · rw [D.weight_eq_bot_of_not_supported _ hs] at hb
                    have hz : ⁅x, y⁆ = 0 := hb
                    rw [hz]
                    exact (D.weightSpan R).zero_mem
              | zero => simp
              | add y z _ _ hy hz => simpa only [lie_add] using Submodule.add_mem _ hy hz
          | zero => simp
          | add y z _ _ hy hz => simpa only [lie_add] using Submodule.add_mem _ hy hz
      | zero => simp
      | add x z _ _ hx hz => simpa only [add_lie] using Submodule.add_mem _ hx hz
  | zero => simp
  | add x z _ _ hx hz => simpa only [add_lie] using Submodule.add_mem _ hx hz

/-- Both coordinates are strictly negative. -/
def negativePart : LieSubalgebra ℂ g where
  __ := D.weightSpan borcherdsNegativeCone
  lie_mem' {x y} hx hy := D.weightSpan_bracket_mem _ _ _ (by
    intro α β hα hβ _ _ _
    simpa only [borcherdsNegativeCone, neg_add] using borcherdsPositiveCone_add hα hβ) hx hy

/-- Cartan and the two real root lines. -/
def leviPart : LieSubalgebra ℂ g where
  __ := D.weightSpan borcherdsLeviDegree
  lie_mem' {x y} hx hy := D.weightSpan_bracket_mem _ _ _ (by
    intro α β hα hβ _ _ hs
    simp only [borcherdsLeviDegree, borcherdsRootSupport, borcherdsPositiveRoot,
      borcherdsPositiveCone, borcherdsRealRoot, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg] at *
    omega) hx hy

theorem negativePart_le_parabolic : D.negativePart ≤ D.parabolicPart := by
  apply D.weightSpan_mono_predicate
  intro γ hγ
  simp only [borcherdsNegativeCone, borcherdsPositiveCone, Prod.fst_neg, Prod.snd_neg] at *
  omega

theorem leviPart_le_parabolic : D.leviPart ≤ D.parabolicPart := by
  apply D.weightSpan_mono_predicate
  intro γ hγ
  simp only [borcherdsLeviDegree, borcherdsPositiveCone, borcherdsRealRoot,
    Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg] at *
  omega

theorem levi_normalizes_positive {x y : g} (hx : x ∈ D.leviPart)
    (hy : y ∈ D.positivePart) : ⁅x, y⁆ ∈ D.positivePart := by
  apply D.weightSpan_bracket_mem _ _ _ (by
    intro α β hα hβ _ _ hs
    simp only [borcherdsLeviDegree, borcherdsRootSupport, borcherdsPositiveRoot,
      borcherdsPositiveCone, borcherdsRealRoot, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg] at *
    omega) hx hy

theorem parabolic_normalizes_negative {x y : g} (hx : x ∈ D.parabolicPart)
    (hy : y ∈ D.negativePart) : ⁅x, y⁆ ∈ D.negativePart := by
  apply D.weightSpan_bracket_mem _ _ _ (by
    intro α β hα hβ hsα _ hs
    simp only [borcherdsNegativeCone, borcherdsRootSupport, borcherdsPositiveRoot,
      borcherdsPositiveCone, borcherdsRealRoot, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg] at *
    omega) hx hy

theorem levi_normalizes_negative {x y : g} (hx : x ∈ D.leviPart)
    (hy : y ∈ D.negativePart) : ⁅x, y⁆ ∈ D.negativePart :=
  D.parabolic_normalizes_negative (D.leviPart_le_parabolic hx) hy

/-- The actual negative ideal, with ambient algebra the opposite parabolic. -/
def negativeParabolicIdeal : LieIdeal ℂ D.parabolicPart where
  __ := D.negativePart.toSubmodule.comap D.parabolicPart.toSubmodule.subtype
  lie_mem := by
    intro x y hy
    exact D.parabolic_normalizes_negative x.property hy

theorem parabolic_eq_levi_sup_negative : D.parabolicPart.toSubmodule =
    D.leviPart.toSubmodule ⊔ D.negativePart.toSubmodule := by
  apply le_antisymm
  · apply D.weightSpan_le_of_supported
    intro γ hγ hs
    have h : borcherdsLeviDegree γ ∨ borcherdsNegativeCone γ := by
      simp only [borcherdsLeviDegree, borcherdsNegativeCone, borcherdsRootSupport,
        borcherdsPositiveRoot, borcherdsPositiveCone, borcherdsRealRoot, Prod.ext_iff,
        Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg] at *
      omega
    rcases h with h | h
    · exact le_sup_of_le_left (D.weightSpace_le_weightSpan h)
    · exact le_sup_of_le_right (D.weightSpace_le_weightSpan h)
  · exact sup_le D.leviPart_le_parabolic D.negativePart_le_parabolic

theorem levi_negative_disjoint :
    Disjoint D.leviPart.toSubmodule D.negativePart.toSubmodule := by
  apply D.weight_internal.submodule_iSupIndep.disjoint_biSup_biSup
    (s := {γ | borcherdsLeviDegree γ}) (t := {γ | borcherdsNegativeCone γ})
  apply Set.disjoint_left.mpr
  intro γ hγ hn
  change borcherdsLeviDegree γ at hγ
  change borcherdsNegativeCone γ at hn
  simp only [borcherdsLeviDegree, borcherdsNegativeCone, borcherdsPositiveCone,
    borcherdsRealRoot, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero,
    Prod.fst_neg, Prod.snd_neg] at *
  omega

end BorcherdsData
end VOA.Moonshine.ConwayNorton
