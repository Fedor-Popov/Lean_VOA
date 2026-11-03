import VOA.Examples.LeeYangCosetTransferDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The dimension squeeze starting from a quotient of the Virasoro image

The image `I` embeds in cohomology `H` and surjects onto the simple quotient `L`.
This is the direction supplied by maximality of the proper Virasoro ideal;
an injection from `L` into cohomology is a conclusion, not a premise.
All statements are level independent. The concrete maps and their filtration
compatibility must still be supplied when applying these linear algebra results.
-/

namespace VOA.LeeYangShortcut

open Module

universe u v w x t

variable {𝕜 : Type u} [DivisionRing 𝕜]
variable {I : Type v} [AddCommGroup I] [Module 𝕜 I]
variable {L : Type w} [AddCommGroup L] [Module 𝕜 L]
variable {H : Type x} [AddCommGroup H] [Module 𝕜 H]
variable {ι : Type t}

/-- Restrict a linear map to a specified piece and its exact image. -/
def pieceMap (q : I →ₗ[𝕜] L) (P : Submodule 𝕜 I) : P →ₗ[𝕜] P.map q :=
  (q.domRestrict P).codRestrict _ fun x => Submodule.mem_map.mpr ⟨x, x.2, rfl⟩

theorem pieceMap_surjective (q : I →ₗ[𝕜] L) (P : Submodule 𝕜 I) :
    Function.Surjective (pieceMap q P) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp y.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

section Finite

variable [FiniteDimensional 𝕜 H]

/-- The three dimensions in the image-to-simple squeeze agree. -/
theorem image_finranks_eq
    (j : I →ₗ[𝕜] H) (hj : Function.Injective j) (q : I →ₗ[𝕜] L)
    (P : Submodule 𝕜 I) (Q : Submodule 𝕜 L) (F : Submodule 𝕜 H)
    (hq : P.map q = Q) (hjP : P.map j ≤ F)
    (hupper : finrank 𝕜 F ≤ finrank 𝕜 Q) :
    finrank 𝕜 Q = finrank 𝕜 P ∧ finrank 𝕜 P = finrank 𝕜 F := by
  letI : FiniteDimensional 𝕜 I := Module.Finite.of_injective j hj
  have hQP : finrank 𝕜 Q ≤ finrank 𝕜 P := by
    rw [← hq]
    exact Submodule.finrank_map_le q P
  have hPF : finrank 𝕜 P ≤ finrank 𝕜 F :=
    LeeYangCosetTransfer.finrank_le_of_filtered_injective j hj P F hjP
  exact ⟨le_antisymm hQP (hPF.trans hupper),
    le_antisymm hPF (hupper.trans hQP)⟩

/-- The embedded Virasoro-image prefix exhausts the cohomology prefix. -/
theorem image_map_eq_of_quotient_squeeze
    (j : I →ₗ[𝕜] H) (hj : Function.Injective j) (q : I →ₗ[𝕜] L)
    (P : Submodule 𝕜 I) (Q : Submodule 𝕜 L) (F : Submodule 𝕜 H)
    (hq : P.map q = Q) (hjP : P.map j ≤ F)
    (hupper : finrank 𝕜 F ≤ finrank 𝕜 Q) : P.map j = F := by
  have hd := image_finranks_eq j hj q P Q F hq hjP hupper
  exact LeeYangCosetTransfer.map_eq_of_finrank_squeeze j hj P F
    (finrank 𝕜 Q) hjP hupper hd.1

/-- The map from an image prefix to its simple-quotient prefix is injective. -/
theorem pieceMap_injective_of_quotient_squeeze
    (j : I →ₗ[𝕜] H) (hj : Function.Injective j) (q : I →ₗ[𝕜] L)
    (P : Submodule 𝕜 I) (Q : Submodule 𝕜 L) (F : Submodule 𝕜 H)
    (hq : P.map q = Q) (hjP : P.map j ≤ F)
    (hupper : finrank 𝕜 F ≤ finrank 𝕜 Q) :
    Function.Injective (pieceMap q P) := by
  letI : FiniteDimensional 𝕜 I := Module.Finite.of_injective j hj
  have hd : finrank 𝕜 P = finrank 𝕜 (P.map q) := by
    rw [hq]
    exact (image_finranks_eq j hj q P Q F hq hjP hupper).1.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
    (pieceMap_surjective q P)

/-- Exhaustive prefixes make the image-to-simple quotient map injective. -/
theorem quotient_injective_of_image_squeeze
    (j : I →ₗ[𝕜] H) (hj : Function.Injective j) (q : I →ₗ[𝕜] L)
    (P : ι → Submodule 𝕜 I) (Q : ι → Submodule 𝕜 L)
    (F : ι → Submodule 𝕜 H)
    (hq : ∀ r, (P r).map q = Q r) (hjP : ∀ r, (P r).map j ≤ F r)
    (hupper : ∀ r, finrank 𝕜 (F r) ≤ finrank 𝕜 (Q r))
    (hexhaustive : ∀ x : I, ∃ r, x ∈ P r) : Function.Injective q := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨r, hr⟩ := hexhaustive x
  have hi := pieceMap_injective_of_quotient_squeeze j hj q
    (P r) (Q r) (F r) (hq r) (hjP r) (hupper r)
  have heq : pieceMap q (P r) ⟨x, hr⟩ = pieceMap q (P r) 0 := by
    apply Subtype.ext
    exact hx.trans (map_zero q).symm
  have hz := congrArg Subtype.val (hi heq)
  exact hz

/-- The surjection from the Virasoro image is an equivalence after the squeeze. -/
noncomputable def imageEquivSimple
    (j : I →ₗ[𝕜] H) (hj : Function.Injective j) (q : I →ₗ[𝕜] L)
    (hqs : Function.Surjective q)
    (P : ι → Submodule 𝕜 I) (Q : ι → Submodule 𝕜 L)
    (F : ι → Submodule 𝕜 H)
    (hq : ∀ r, (P r).map q = Q r) (hjP : ∀ r, (P r).map j ≤ F r)
    (hupper : ∀ r, finrank 𝕜 (F r) ≤ finrank 𝕜 (Q r))
    (hexhaustive : ∀ x : I, ∃ r, x ∈ P r) : I ≃ₗ[𝕜] L :=
  LinearEquiv.ofBijective q
    ⟨quotient_injective_of_image_squeeze j hj q P Q F hq hjP hupper hexhaustive, hqs⟩

/-- Inverting the injective quotient gives exact simple-prefix images in H. -/
theorem simple_map_eq_of_image_squeeze
    (j : I →ₗ[𝕜] H) (hj : Function.Injective j) (q : I →ₗ[𝕜] L)
    (hqs : Function.Surjective q)
    (P : ι → Submodule 𝕜 I) (Q : ι → Submodule 𝕜 L)
    (F : ι → Submodule 𝕜 H)
    (hq : ∀ r, (P r).map q = Q r) (hjP : ∀ r, (P r).map j ≤ F r)
    (hupper : ∀ r, finrank 𝕜 (F r) ≤ finrank 𝕜 (Q r))
    (hexhaustive : ∀ x : I, ∃ r, x ∈ P r) (r : ι) :
    (Q r).map (j.comp
      (imageEquivSimple j hj q hqs P Q F hq hjP hupper hexhaustive).symm.toLinearMap) =
        F r := by
  let e := imageEquivSimple j hj q hqs P Q F hq hjP hupper hexhaustive
  have hcancel : e.symm.toLinearMap.comp q = LinearMap.id := by
    ext x
    exact e.symm_apply_apply x
  rw [← hq r, ← Submodule.map_comp]
  change (P r).map ((j.comp e.symm.toLinearMap).comp q) = F r
  rw [LinearMap.comp_assoc, hcancel, LinearMap.comp_id]
  exact image_map_eq_of_quotient_squeeze j hj q (P r) (Q r) (F r)
    (hq r) (hjP r) (hupper r)

end Finite
end VOA.LeeYangShortcut
