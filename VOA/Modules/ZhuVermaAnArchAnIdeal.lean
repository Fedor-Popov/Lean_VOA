/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchABS
import VOA.Modules.ZhuVermaAnArchL1Close
import VOA.Modules.ZhuVermaAnArchRgenFinal
import VOA.Modules.ZhuVermaAnArchFiltrationFinal
import VOA.Modules.ZhuVermaAnArchAlgebra

/-!
# **`AnIdeal` ASSEMBLED unconditionally**: `Oₙ(𝒱)` is a 2-sided `*ₙ`-ideal.

All four generator-family cores of `AnIdeal_of_gens` are proved (each axiom-clean
`[propext, Classical.choice, Quot.sound]`):

| field   | statement                                  | lemma |
|---------|--------------------------------------------|-------|
| `hLcirc`| `Oₙ *ₙ 𝒱 ⊆ Oₙ` (circle gen, left slot)     | `hLcirc_closed` (LEFT tower, mirror of D19/20) |
| `hLgen` | `O^L *ₙ 𝒱 ⊆ Oₙ` (`(L₋₁+L₀)` gen, left)     | `leftProd_Lgen_mem_OnFull` (ABS vector identity) |
| `hRcirc`| `𝒱 *ₙ Oₙ ⊆ Oₙ` (circle gen, right slot)    | `leftProd_circ_right_mem_OnFull` (`leftProd_On_mem_On`) |
| `hRgen` | `𝒱 *ₙ O^L ⊆ Oₙ` (`(L₋₁+L₀)` gen, right)    | `hRgen_closed` (`RgenRest = w₀·circ`) |

Hence the **corrected Dong–Li–Mason target** `AnIdeal W n` (the FALSE `O₀`-targeting `AnBimoduleInputs`
is replaced) holds for every `n`, and `Aₙ(𝒱) = 𝒱/OnFull W n` is a well-defined ℂ-algebra under `*ₙ`,
with the unconditional surjection `Aₙ(𝒱) ↠ A₀(𝒱)` (`ZhuVermaAnArchFiltrationFinal`).

## References
Dong–Li–Mason, J. Algebra 206 (1998) 67–96 (Lemma 2.2); Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **`Oₙ(𝒱)` is a 2-sided `*ₙ`-ideal** (Dong–Li–Mason Lemma 2.2), assembled from the four
generator-family cores.  This is the corrected target replacing the FALSE `AnBimoduleInputs`. -/
theorem anIdeal_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : AnIdeal W n :=
  AnIdeal_of_gens W n
    (hLcirc_closed W n)
    (leftProd_Lgen_mem_OnFull W n)
    (leftProd_circ_right_mem_OnFull W n)
    (hRgen_closed W n)

/-- The left ideal `Oₙ *ₙ 𝒱 ⊆ Oₙ`, unconditional. -/
theorem OnFull_leftProd_mem (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    ∀ g ∈ OnFull W n, ∀ b : 𝒱, leftProd W n g b ∈ OnFull W n :=
  (anIdeal_holds W n).left

/-- The right ideal `𝒱 *ₙ Oₙ ⊆ Oₙ`, unconditional. -/
theorem OnFull_rightSlot_mem (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    ∀ a : 𝒱, ∀ g ∈ OnFull W n, leftProd W n a g ∈ OnFull W n :=
  (anIdeal_holds W n).right

/-! ## The unconditional `Aₙ(𝒱)` algebra product and the surjection `Aₙ ↠ A₀`. -/

/-- **The unconditional descended FZ product on `Aₙ(𝒱) = 𝒱/OnFull`** — `AnFull.mul` instantiated at
`anIdeal_holds`.  Well-defined `ℂ`-bilinear map `Aₙ →ₗ Aₙ →ₗ Aₙ` (`[a]·[x] = [a *ₙ x]`). -/
noncomputable def AnFull.mulU (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    AnFull W n →ₗ[ℂ] AnFull W n →ₗ[ℂ] AnFull W n :=
  AnFull.mul W n (anIdeal_holds W n)

@[simp] theorem AnFull.mulU_mk (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a x : 𝒱) :
    AnFull.mulU W n (mkAnFull W n a) (mkAnFull W n x) = mkAnFull W n (leftProd W n a x) :=
  AnFull.mul_mk W n (anIdeal_holds W n) a x

/-- **The unconditional surjection `Aₙ(𝒱) ↠ A₀(𝒱)`** (Dong–Li–Mason Prop. 2.4), from the proved
filtration `OnFull W n ≤ OnFull W 0`. -/
noncomputable def AnFull.surjU (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    AnFull W n →ₗ[ℂ] AnFull W 0 :=
  AnFull.surj W n (OnFull_le_OnFull_zero W n)

theorem AnFull.surjU_surjective (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    Function.Surjective (AnFull.surjU W n) :=
  AnFull.surj_surjective W n (OnFull_le_OnFull_zero W n)

end VOA
