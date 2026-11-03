/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteGrading
import VOA.Examples.Sl2SemiInfiniteGhosts

/-!
# Additivity of total ghost number

Convolution ghost number is additive under all tensor vertex products whenever
the factor gradings are additive and refine parity.  Applied twice to the
one-pair calculation, this proves the product compatibility of the three-pair
ghost grading used for semi-infinite `sl₂` cohomology.
-/

namespace VOA.Sl2SemiInfinite

open scoped TensorProduct
open TensorVA

section TensorProducts

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- Ghost numbers add under every coefficient of the vertex operator. -/
def GhostAdditive (V : SuperVertexAlgebra A) (P : ℤ → Submodule ℂ A) : Prop :=
  ∀ {m n : ℤ} {u x : A}, u ∈ P m → x ∈ P n → ∀ j : ℤ, V.Y u j x ∈ P (m + n)

/-- Induction on a convolution ghost-number component. -/
theorem tensorGhostGrading_induction (P : ℤ → Submodule ℂ A)
    (Q : ℤ → Submodule ℂ B) {n : ℤ} {motive : A ⊗[ℂ] B → Prop}
    (hz : motive 0) (hadd : ∀ x y, motive x → motive y → motive (x + y))
    (hsmul : ∀ (c : ℂ) x, motive x → motive (c • x))
    (htmul : ∀ j : ℤ, ∀ a ∈ P j, ∀ b ∈ Q (n - j), motive (a ⊗ₜ[ℂ] b))
    {u : A ⊗[ℂ] B} (hu : u ∈ tensorGhostGrading P Q n) : motive u := by
  refine Submodule.iSup_induction' (motive := fun x _ => motive x) _ ?_ hz
    (fun x y _ _ hx hy => hadd x y hx hy) hu
  intro j x hx
  exact tenSub_induction hz hadd hsmul (htmul j) hx

/-- The unsigned tensor coefficient adds the factor ghost degrees. -/
theorem rawCoeff_mem_tensorGhostGrading (V : SuperVertexAlgebra A)
    (W : SuperVertexAlgebra B) (P : ℤ → Submodule ℂ A) (Q : ℤ → Submodule ℂ B)
    (hV : GhostAdditive V P) (hW : GhostAdditive W Q)
    {m₁ m₂ n₁ n₂ : ℤ} {a x : A} {b y : B}
    (ha : a ∈ P m₁) (hb : b ∈ Q m₂) (hx : x ∈ P n₁) (hy : y ∈ Q n₂) (s : ℤ) :
    rawCoeff V W a b s (x ⊗ₜ[ℂ] y) ∈ tensorGhostGrading P Q (m₁ + m₂ + n₁ + n₂) := by
  rw [rawCoeff_tmul]
  refine finsum_mem_sub _ _ fun j => ?_
  have h := tmul_mem_tensorGhostGrading P Q (hV ha hx j) (hW hb hy (s - j))
  convert h using 1
  congr 1
  omega

/-- Ghost-degree additivity survives the Koszul-signed tensor construction. -/
theorem tenY_mem_tensorGhostGrading (V : SuperVertexAlgebra A)
    (W : SuperVertexAlgebra B) (P : ℤ → Submodule ℂ A) (Q : ℤ → Submodule ℂ B)
    (hV : GhostAdditive V P) (hW : GhostAdditive W Q)
    (hpV : ∀ n : ℤ, P n ≤ V.parity (n : ZMod 2))
    (hpW : ∀ n : ℤ, Q n ≤ W.parity (n : ZMod 2))
    {m n : ℤ} {u x : A ⊗[ℂ] B} (hu : u ∈ tensorGhostGrading P Q m)
    (hx : x ∈ tensorGhostGrading P Q n) (s : ℤ) :
    tenY V W u s x ∈ tensorGhostGrading P Q (m + n) := by
  refine tensorGhostGrading_induction P Q (n := m)
    (motive := fun w => ∀ x ∈ tensorGhostGrading P Q n,
      tenY V W w s x ∈ tensorGhostGrading P Q (m + n)) ?_ ?_ ?_ ?_ hu x hx
  · intro x _
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb x hx
    rw [map_add]
    exact Submodule.add_mem _ (ha x hx) (hb x hx)
  · intro c a ha x hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ (ha x hx)
  · intro m₁ a ha b hb x hx
    refine tensorGhostGrading_induction P Q (n := n)
      (motive := fun w => tenY V W (a ⊗ₜ[ℂ] b) s w ∈ tensorGhostGrading P Q (m + n))
      ?_ ?_ ?_ ?_ hx
    · change tenY V W (a ⊗ₜ[ℂ] b) s 0 ∈ tensorGhostGrading P Q (m + n)
      rw [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy
      rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x hx
      rw [map_smul]; exact Submodule.smul_mem _ _ hx
    · intro n₁ x hx y hy
      rw [tenY_tmul_parity V W a (hpW (m - m₁) hb) s,
        kappaTen_tmul,
        (parGr V).koszulOp_homog (m - m₁ : ℤ)
          (show x ∈ (parGr V).parity (n₁ : ZMod 2) from hpV n₁ hx)]
      have h := rawCoeff_mem_tensorGhostGrading V W P Q hV hW ha hb
        (Submodule.smul_mem (P n₁) (koszul ((m - m₁ : ℤ) : ZMod 2) (n₁ : ZMod 2)) hx) hy s
      convert h using 1
      congr 1
      omega

/-- Tensor vertex superalgebras inherit additive ghost number. -/
theorem ghostAdditive_tensorSVA (V : SuperVertexAlgebra A)
    (W : SuperVertexAlgebra B) (P : ℤ → Submodule ℂ A) (Q : ℤ → Submodule ℂ B)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W)
    (haV : GhostAdditive V P) (haW : GhostAdditive W Q)
    (hpV : ∀ n : ℤ, P n ≤ V.parity (n : ZMod 2))
    (hpW : ∀ n : ℤ, Q n ≤ W.parity (n : ZMod 2)) :
    GhostAdditive (tensorSVA V W hV hW hg) (tensorGhostGrading P Q) :=
  fun hu hx s => tenY_mem_tensorGhostGrading V W P Q haV haW hpV hpW hu hx s

end TensorProducts

/-- Ghost number is additive for one pair. -/
theorem ghostAdditive_bcGhostSVA : GhostAdditive Ghost.bcGhostSVA Ghost.ghostGrading :=
  fun hu hx j => Ghost.YGh_mem_ghostGrading hu hx j

/-- Ghost number is additive for the first two pairs. -/
theorem ghostAdditive_ghostPairSVA : GhostAdditive ghostPairSVA ghostPairGrading :=
  ghostAdditive_tensorSVA Ghost.bcGhostSVA Ghost.bcGhostSVA
    Ghost.ghostGrading Ghost.ghostGrading _ _ _
    ghostAdditive_bcGhostSVA ghostAdditive_bcGhostSVA
    Ghost.ghostGrading_le_evenOdd Ghost.ghostGrading_le_evenOdd

/-- Total ghost number is additive under every three-pair vertex product. -/
theorem ghostAdditive_sl2GhostSVA : GhostAdditive sl2GhostSVA sl2GhostGrading :=
  ghostAdditive_tensorSVA ghostPairSVA Ghost.bcGhostSVA
    ghostPairGrading Ghost.ghostGrading _ _ _
    ghostAdditive_ghostPairSVA ghostAdditive_bcGhostSVA
    ghostPairGrading_le_parity Ghost.ghostGrading_le_evenOdd

/-- Total ghost number is additive under every mode of the three-pair system. -/
theorem sl2GhostSVA_mode_ghostGrading {m n : ℤ} {u x : Sl2GhostSpace}
    (hu : u ∈ sl2GhostGrading m) (hx : x ∈ sl2GhostGrading n) (j : ℤ) :
    mode (sl2GhostSVA.Y u) j x ∈ sl2GhostGrading (m + n) :=
  ghostAdditive_sl2GhostSVA hu hx (-j - 1)

end VOA.Sl2SemiInfinite
