/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoFlagGeneric
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! Full finite-span stability supplies the endpoint independently of all
low-degree flag calculations. Actual source cyclicity then supplies spanning. -/
namespace VOA.DeligneAudit.D4Two

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {ι T : Type*} [AddCommGroup T] [Module ℂ T]

/-- This checks every selected vector, including those at the top level. -/
theorem span_stable_low (R : CurrentModule f T) (v : ι → T)
    (hlow : ∀ c k, k ≤ 3 → ∀ i,
      R.op c k (v i) ∈ Submodule.span ℂ (Set.range v))
    (c : Fin n) (k : ℕ) (hk : k ≤ 3) :
    Submodule.span ℂ (Set.range v) ≤
      (Submodule.span ℂ (Set.range v)).comap (R.op c k) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hlow c k hk i

/-- The actual high-mode identity turns the full four-mode certificate
into stability under every current mode. -/
theorem span_stable_all (R : CurrentModule f T) (v : ι → T)
    (hhigh : ∀ c k, 2 ≤ k → R.op c k =
      ((3 : ℂ) - (k : ℂ)) • R.op c 2 + ((k : ℂ) - 2) • R.op c 3)
    (hlow : ∀ c k, k ≤ 3 → ∀ i,
      R.op c k (v i) ∈ Submodule.span ℂ (Set.range v))
    (c : Fin n) (k : ℕ) :
    Submodule.span ℂ (Set.range v) ≤
      (Submodule.span ℂ (Set.range v)).comap (R.op c k) := by
  by_cases hk : k ≤ 3
  · exact span_stable_low R v hlow c k hk
  · intro x hx
    change R.op c k x ∈ Submodule.span ℂ (Set.range v)
    rw [hhigh c k (by omega), LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (span_stable_low R v hlow c 2 (by omega) hx)
    · exact Submodule.smul_mem _ _ (span_stable_low R v hlow c 3 (by omega) hx)

/-- The endpoint uses actual cyclicity, not an unproved assertion that
the degree-four flag is the whole source. -/
theorem span_top_of_low_action (R : CurrentModule f T) (w : T) (v : ι → T)
    (hcyclic : Submodule.span ℂ (Set.range fun l : List (Fin n × ℕ) =>
      wordOp R l w) = ⊤)
    (hw : w ∈ Submodule.span ℂ (Set.range v))
    (hhigh : ∀ c k, 2 ≤ k → R.op c k =
      ((3 : ℂ) - (k : ℂ)) • R.op c 2 + ((k : ℂ) - 2) • R.op c 3)
    (hlow : ∀ c k, k ≤ 3 → ∀ i,
      R.op c k (v i) ∈ Submodule.span ℂ (Set.range v)) :
    Submodule.span ℂ (Set.range v) = ⊤ := by
  apply top_unique
  rw [← hcyclic]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  induction l with
  | nil => exact hw
  | cons a l ih => exact span_stable_all R v hhigh hlow a.1 a.2 ih

/-- Once spanning is proved, the independently checked source rank turns
the finite word family into a basis. -/
def basisOfSpanningWords [Fintype ι] (v : ι → T)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤)
    (hcard : Fintype.card ι = Module.finrank ℂ T) : Module.Basis ι ℂ T :=
  basisOfTopLeSpanOfCardEqFinrank v (by rw [hspan]) hcard

@[simp] theorem basisOfSpanningWords_apply [Fintype ι] (v : ι → T)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤)
    (hcard : Fintype.card ι = Module.finrank ℂ T) (i : ι) :
    basisOfSpanningWords v hspan hcard i = v i := by
  rw [basisOfSpanningWords, coe_basisOfTopLeSpanOfCardEqFinrank]

end
end VOA.DeligneAudit.D4Two

#print axioms VOA.DeligneAudit.D4Two.span_top_of_low_action
