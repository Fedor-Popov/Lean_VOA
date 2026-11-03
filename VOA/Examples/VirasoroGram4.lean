/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.LeeYangKac
import VOA.Examples.LeeYangRigidity
import VOA.Core.GradedFormMatrix

/-!
# The **true** level-4 Kac matrix of `V(c,0)`: the Gram matrix of `gradedForm`

`Examples/LeeYangKac.gram4` is the level-4 Gram matrix of `RigidBridge.shapForm`, the *top-mode*
pairing `⟨a,b⟩ₖ = ε(a₍₂ₖ₋₁₎b)`.  That is **not** the form whose radical Li's theorem identifies
with the maximal graded ideal: that form is `LiRadical.gradedForm (canonicalInvariantForm hne hqp)`,
the restriction to `𝒱ₙ` of the canonical normalised fully invariant form.

The two forms agree only on quasi-primary vectors, and **at level 4 neither basis vector is
quasi-primary**: `L₁L₋₄|0⟩ = 5L₋₃|0⟩` and `L₁L₋₂²|0⟩ = 3L₋₁L₋₂|0⟩ = 3L₋₃|0⟩`.  (The quasi-primary
subspace of `𝒱₄` is the single line `ℂ ∙ (5L₋₂²|0⟩ - 3L₋₄|0⟩)`.)  `LeeYangKac` records the
discrepancy honestly — `S(c) ≠ 21·G(c)` entrywise — and observes that the two determinants agree
up to the constant `21`, so the *zero sets* match.  But **ranks are not determined by
determinants**, and rank is the only thing `Core/GradedFormMatrix.rank_gramMatrix_eq` computes.
So the `gradedForm` side has to be computed on its own.  That is what this file does.

## The derivation

Everything comes from two facts about `B = canonicalInvariantForm hne hqp`, and nothing else:

* **Virasoro adjointness** `B(Lₙa, b) = B(a, L₋ₙb)` — a *structure field* of `InvariantForm`
  (`virasoro_adj`), so it holds for every `n` with no extra hypothesis;
* **the normalisation** `B(𝟙, 𝟙) = +1` — `InvariantForm.Normalized`, the repository's convention.

Moving every `L₋ₘ` off the left slot onto the right and landing on `L₊|0⟩ = 0` reduces each entry
to a multiple of `B(𝟙,𝟙)`.  The four `Lop` computations needed already exist:
`Lop_four_L4vac`, `Lop_four_L2L2vac`, `Lop_two_two_L2L2vac`, `Lop_two_L4vac`, `Lop_two_L2vac`.

## The sign

With the normalisation `(𝟙|𝟙) = +1`, the entries agree with the textbook contravariant form:

  `canGram4 c = !![c(c+8)/2, 3c; 3c, 5c]`,   `det (canGram4 c) = c²(5c+22)/2`.

In particular the textbook level-4 vacuum Kac determinant `c²(5c+22)/2` is recovered exactly, and
`LeeYangKac.det_gram4 = 21 · det (canGram4 c)` for every `c`.

## Contents

* `canB`, `canB_adj`, `canB_vac` — the form, its adjointness, its normalisation.
* `canB_L2L2_L2L2`, `canB_L2L2_L4`, `canB_L4_L2L2`, `canB_L4_L4` — the four entries, derived.
* `canGram4_eq`, `det_canGram4` — the level-4 matrix and its determinant.
* `det_gram4_eq_21_mul_det_canGram4` — the exact relation to `LeeYangKac.det_gram4`.
* `basis4` — an honest `Basis (Fin 2) ℂ 𝒱₄`, so that the matrix is a genuine
  `GramMat.gramMatrix` and `rank_gramMatrix_add_finrank` applies.
* `canGram4_det_ne_zero_iff`, `maxIdealVir_inf_grading_four_eq_bot_iff` — the level-4
  degeneracy criterion, for the *right* form.
* `rank_canGram4_leeYang` — at `c = -22/5` the rank is `1`, matching `dim L(-22/5,0)₄ = 1`.
* `canB_eq_signed_shapForm_of_quasiPrimary` — the corrected (⚠ **signed**) comparison with
  `shapForm`, valid on quasi-primary vectors.
* §8: `rank_canGram4_leeYang_direct` and `finrank_maxGradedIdeal_leeYang_four_from_gram` —
  the calibration run **forward**: the rank is computed *from the matrix* and the level-4 radical
  dimension is then *read off*, using no prior knowledge of the Lee–Yang ideal.
* §9: ⚠ `rank_gram4_eq_rank_canGram4` — the honest calibration of the correction itself: at
  level `4` the `shapForm` and `gradedForm` matrices have the **same rank at every `c`**, so the
  pre-existing rank conclusion was never wrong; only the entries and the justification were.
-/

namespace VOA.VirGram4

open VOA VOA.LeeYang VOA.LeeYangKac VOA.VirModule
open VOA.VertexOperatorAlgebra
open Module (Basis finrank)

variable (c : ℂ)

/-! ## §1  The canonical form on `V(c,0)` -/

/-- The canonical normalised fully invariant form on `V(c,0)`.  Both hypotheses are free:
`vacVec_ne_zero` gives `𝟙 ≠ 0`, and `virasoroVOA_qp` gives `L₁𝒱₁ = 0` vacuously (`𝒱₁ = 0`). -/
noncomputable def canB : InvariantForm (virasoroVOA c) :=
  canonicalInvariantForm (vacVec_ne_zero c) (virasoroVOA_qp c)

/-- The canonical form respects the full vertex-algebra invariance identity, not only Virasoro adjointness. This is the hypothesis that later identifies its radical with the maximal graded ideal. -/
theorem canB_isFullyInvariant : (canB c).IsFullyInvariant :=
  canonicalInvariantForm_isFullyInvariant _ _

/-- The canonical bilinear form assigns norm one to the vacuum. This fixes the otherwise arbitrary scalar multiplying an invariant form. -/
theorem canB_normalized : (canB c).Normalized := canonicalInvariantForm_normalized _ _

/-- **The normalisation is `+1`** (`InvariantForm.Normalized`). -/
theorem canB_vac : (canB c).form (vacVec c) (vacVec c) = 1 := canB_normalized c

/-- **Virasoro adjointness** for `Lop`: a structure field of `InvariantForm`, transported along
`virasoroVOA_L_eq_Lop`. -/
theorem canB_adj (n : ℤ) (a b : VirUniv c) :
    (canB c).form (Lop c n a) b = (canB c).form a (Lop c (-n) b) := by
  rw [← virasoroVOA_L_eq_Lop, ← virasoroVOA_L_eq_Lop]
  exact (canB c).virasoro_adj n a b

/-- The form of adjointness used below: pull `L₋ₙ` off the left slot. -/
theorem canB_adj' (n : ℤ) (a b : VirUniv c) :
    (canB c).form (Lop c (-n) a) b = (canB c).form a (Lop c n b) := by
  rw [canB_adj, neg_neg]

/-- Evaluating against the vacuum: `B(𝟙, k·𝟙) = k`. -/
theorem canB_vac_smul (k : ℂ) : (canB c).form (vacVec c) (k • vacVec c) = k := by
  rw [map_smul, canB_vac, smul_eq_mul, mul_one]

/-! ## §2  The four entries, derived

The unfoldings `L₋₂|0⟩ = Lop c (-2) 𝟙`, `L₋₂²|0⟩ = Lop c (-2) (L₋₂|0⟩)` and
`L₋₄|0⟩ = Lop c (-4) 𝟙` are definitional. -/

/-- The named weight-two vacuum state is exactly the result of applying L minus two to the vacuum; this rewrite connects state notation with mode calculations. -/
private theorem hL2 : Lop c (-2) (vacVec c) = L2vac c := rfl
/-- The named two-mode weight-four state is obtained by applying L minus two once more to the weight-two state. -/
private theorem hL22 : Lop c (-2) (L2vac c) = L2L2vac c := rfl
/-- The other named weight-four state is the single L minus four mode applied to the vacuum. -/
private theorem hL4 : Lop c (-4) (vacVec c) = L4vac c := rfl

/-- The level-2 entry, as a warm-up and a sign check: `B(ω, ω) = c/2`.

⚠ `RigidBridge.shapForm` also gives `c/2` here (`LeeYangGram.shapForm_omegaVir_self`).  Since
`ω` is quasi-primary, this is a direct sign calibration.  See
`canB_eq_signed_shapForm_of_quasiPrimary` in §6. -/
theorem canB_L2_L2 : (canB c).form (L2vac c) (L2vac c) = c / 2 := by
  have h := canB_adj' c 2 (vacVec c) (L2vac c)
  rw [hL2] at h
  rw [h, Lop_two_L2vac, canB_vac_smul]

/-- `B(L₋₄|0⟩, L₋₄|0⟩) = 5c`. -/
theorem canB_L4_L4 : (canB c).form (L4vac c) (L4vac c) = 5 * c := by
  have h := canB_adj' c 4 (vacVec c) (L4vac c)
  rw [hL4] at h
  rw [h, Lop_four_L4vac, canB_vac_smul]

/-- `B(L₋₄|0⟩, L₋₂²|0⟩) = 3c`. -/
theorem canB_L4_L2L2 : (canB c).form (L4vac c) (L2L2vac c) = 3 * c := by
  have h := canB_adj' c 4 (vacVec c) (L2L2vac c)
  rw [hL4] at h
  rw [h, Lop_four_L2L2vac, canB_vac_smul]

/-- `B(L₋₂²|0⟩, L₋₄|0⟩) = 3c`.  Derived independently of `canB_L4_L2L2` — the form is not
known to be symmetric in this library, so both off-diagonal entries are computed. -/
theorem canB_L2L2_L4 : (canB c).form (L2L2vac c) (L4vac c) = 3 * c := by
  have h := canB_adj' c 2 (L2vac c) (L4vac c)
  rw [hL22] at h
  rw [h, Lop_two_L4vac, map_smul, canB_L2_L2, smul_eq_mul]
  ring

/-- `B(L₋₂²|0⟩, L₋₂²|0⟩) = c(c+8)/2`. -/
theorem canB_L2L2_L2L2 : (canB c).form (L2L2vac c) (L2L2vac c) = c * (c + 8) / 2 := by
  have h1 := canB_adj' c 2 (L2vac c) (L2L2vac c)
  rw [hL22] at h1
  have h2 := canB_adj' c 2 (vacVec c) (Lop c 2 (L2L2vac c))
  rw [hL2] at h2
  rw [h1, h2, Lop_two_two_L2L2vac, canB_vac_smul]
  ring

/-! ## §3  The level-4 matrix and its determinant -/

/-- **The true level-4 Gram matrix** of `V(c,0)`, in the ordered basis `(L₋₂²|0⟩, L₋₄|0⟩)`. -/
noncomputable def canGram4 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(canB c).form (L2L2vac c) (L2L2vac c), (canB c).form (L2L2vac c) (L4vac c);
     (canB c).form (L4vac c) (L2L2vac c), (canB c).form (L4vac c) (L4vac c)]

/-- **The level-4 Kac matrix for `gradedForm (canonicalInvariantForm …)`**, at arbitrary
central charge:

  `canGram4 c = !![c(c+8)/2, 3c; 3c, 5c]`.

Derived from Virasoro adjointness and `(𝟙|𝟙) = +1` alone. -/
theorem canGram4_eq :
    canGram4 c = !![c * (c + 8) / 2, 3 * c; 3 * c, 5 * c] := by
  rw [canGram4, canB_L2L2_L2L2, canB_L2L2_L4, canB_L4_L2L2, canB_L4_L4]

/-- **THE LEVEL-4 KAC DETERMINANT, for the right form**:

  `det (canGram4 c) = c²(5c+22)/2`.

Exactly the textbook level-4 vacuum-module Kac determinant. -/
theorem det_canGram4 : (canGram4 c).det = c ^ 2 * (5 * c + 22) / 2 := by
  rw [canGram4_eq, Matrix.det_fin_two_of]
  ring

/-- The exact relation to `LeeYangKac.det_gram4`: the `shapForm` determinant is `21` times this
one, for every `c`.  The factor `21` is the top-mode normalisation `(L₋₄|0⟩)₍₇₎ = 21·L₄`
(`LeeYangGram.smul_L4vac_seven`).  ⚠ This is a statement about determinants only; the matrices
are *not* proportional. -/
theorem det_gram4_eq_21_mul_det_canGram4 (hvac : (virasoroVOA c).vacuum ≠ 0) :
    (LeeYangKac.gram4 c hvac).det = 21 * (canGram4 c).det := by
  rw [LeeYangKac.det_gram4, det_canGram4]

/-- The determinant vanishes exactly at `c = 0` and `c = -22/5` — the same zero set as
`LeeYangKac.det_gram4_eq_zero_iff`, as it must be. -/
theorem det_canGram4_eq_zero_iff : (canGram4 c).det = 0 ↔ c = 0 ∨ c = leeYangC := by
  rw [det_canGram4, leeYangC]
  constructor
  · intro h
    have h' : c ^ 2 * (5 * c + 22) = 0 := by
      field_simp at h; linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h2
    · exact Or.inl (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1)
    · right; linear_combination h2 / 5
  · rintro (rfl | rfl) <;> ring

/-! ## §4  A genuine basis of `𝒱₄`, and the `gramMatrix` identification -/

/-- `(L₋₂²|0⟩, L₋₄|0⟩)`, as a family in `𝒱₄`. -/
noncomputable def vec4 : Fin 2 → (virasoroVOA c).grading 4 := ![L2L2vec4 c, L4vec4 c]

/-- The first member of the weight-four coordinate family is the state with two L minus two creation modes. -/
theorem vec4_zero : vec4 c 0 = L2L2vec4 c := rfl
/-- The second member of the weight-four coordinate family is the state created by L minus four. -/
theorem vec4_one : vec4 c 1 = L4vec4 c := rfl

/-- The two weight-four states have no nontrivial linear relation in the universal vacuum module, at any central charge. Their images can become dependent only after passing to a quotient. -/
theorem vec4_linearIndependent : LinearIndependent ℂ (vec4 c) := by
  rw [vec4, LinearIndependent.pair_iff]
  intro s t h
  have h' : s • L2L2vac c + t • L4vac c = 0 := congrArg Subtype.val h
  exact level4_indep c h'

/-- Every universal state of weight four is a linear combination of the two displayed creation states. Together with independence, this makes the chosen coordinates a basis. -/
theorem vec4_span : ⊤ ≤ Submodule.span ℂ (Set.range (vec4 c)) := by
  rintro ⟨x, hx⟩ -
  have hx' : x ∈ Submodule.span ℂ ({L2L2vac c, L4vac c} : Set (VirUniv c)) := by
    rw [← gradingVir_four c]; exact hx
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx'
  have hmem : (⟨x, hx⟩ : (virasoroVOA c).grading 4)
      = a • vec4 c 0 + b • vec4 c 1 := by
    apply Subtype.ext
    simpa [vec4] using hab.symm
  rw [hmem]
  exact add_mem
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

/-- An honest basis of the two-dimensional space `𝒱₄`, so that `canGram4` really is a Gram
matrix in the sense of `Core/GradedFormMatrix`. -/
noncomputable def basis4 : Basis (Fin 2) ℂ ((virasoroVOA c).grading 4) :=
  Basis.mk (vec4_linearIndependent c) (vec4_span c)

/-- Passing from the independent spanning family to a Lean basis leaves its vectors unchanged; this lets matrix entries be computed with the original creation states. -/
@[simp] theorem basis4_apply (i : Fin 2) : basis4 c i = vec4 c i := by
  rw [basis4, Basis.mk_apply]

/-- `canGram4` **is** the `Core/GradedFormMatrix` Gram matrix of the canonical form at
level `4`, in the basis `basis4`. -/
theorem gramMatrix_basis4 :
    GramMat.gramMatrix (canB c) 4 (basis4 c) = canGram4 c := by
  ext i j
  rw [GramMat.gramMatrix_apply, canGram4]
  fin_cases i <;> fin_cases j <;>
    simp [basis4_apply, vec4, L2L2vec4_coe, L4vec4_coe]

/-! ## §5  What the matrix computes -/

/-- **The level-4 degeneracy criterion, for the right form**:
`det (canGram4 c) ≠ 0` exactly when the maximal graded ideal of `V(c,0)` has nothing at
level `4`. -/
theorem canGram4_det_ne_zero_iff :
    (canGram4 c).det ≠ 0 ↔
      QuotVOA.maxGradedIdeal (virasoroVOA c) ⊓ (virasoroVOA c).grading 4 = ⊥ := by
  rw [← gramMatrix_basis4 c]
  exact GramMat.gramMatrix_det_ne_zero_iff _ 4 (basis4 c) (canB_isFullyInvariant c)
    (canB_normalized c)

/-- Restated at the two degenerate central charges: for `c ∉ {0, -22/5}` the maximal graded
ideal of `V(c,0)` is trivial at level `4`. -/
theorem maxGradedIdeal_inf_grading_four_eq_bot (h0 : c ≠ 0) (hLY : c ≠ leeYangC) :
    QuotVOA.maxGradedIdeal (virasoroVOA c) ⊓ (virasoroVOA c).grading 4 = ⊥ := by
  rw [← canGram4_det_ne_zero_iff]
  intro hdet
  rcases (det_canGram4_eq_zero_iff c).mp hdet with h | h
  · exact h0 h
  · exact hLY h

/-- **Rank, not determinant.**  `rank (canGram4 c) + dim (maxIdeal ⊓ 𝒱₄) = dim 𝒱₄ = 2`. -/
theorem rank_canGram4_add_finrank :
    (canGram4 c).rank
        + finrank ℂ (QuotVOA.maxGradedIdeal (virasoroVOA c) ⊓ (virasoroVOA c).grading 4 :
            Submodule ℂ (VirUniv c))
      = finrank ℂ ((virasoroVOA c).grading 4) := by
  rw [← gramMatrix_basis4 c]
  exact GramMat.rank_gramMatrix_add_finrank _ 4 (basis4 c) (canB_isFullyInvariant c)
    (canB_normalized c)

/-! ## §6  ⚠ The corrected comparison with `shapForm`

The repository **already** contains the right statement, in the right (signed) form:
`RigidBridge.invariantForm_eq_shapForm` gives, for `s ∈ 𝒱ₖ` with `L₁s = 0` and any fully
invariant normalised `B`,

  `B(s, y) = (-1)^k · ⟨s, y⟩ₖ`.

So the identity a caller wants is **not** `gradedForm = shapForm` but `gradedForm =
(-1)^n · shapForm`, and only on the quasi-primary locus.  Both qualifications matter here. -/

/-- The signed comparison, specialised to `V(c,0)`: on a quasi-primary `s ∈ 𝒱ₙ`,
`B(s, y) = (-1)^n·⟨s,y⟩ₙ`. -/
theorem canB_eq_signed_shapForm_of_quasiPrimary {n : ℤ} {s : VirUniv c}
    (hs : s ∈ (virasoroVOA c).grading n) (hL1 : Lop c 1 s = 0)
    (y : (virasoroVOA c).grading n) :
    (canB c).form s (y : VirUniv c)
      = (-1 : ℂ) ^ n * RigidBridge.shapForm (virasoroVOA c) (vacVec_ne_zero c) n ⟨s, hs⟩ y :=
  RigidBridge.invariantForm_eq_shapForm (canB_isFullyInvariant c) (canB_normalized c)
    (vacVec_ne_zero c) hs (by rw [virasoroVOA_L_eq_Lop]; exact hL1) y

/-- **Level 2 is where the two forms may be compared**, because `ω = L₋₂|0⟩` *is* quasi-primary
(`Lop_one_L2vac`).  There `(-1)^2 = +1`, and indeed `B(ω,ω) = c/2` (`canB_L2_L2`) agrees with
`⟨ω,ω⟩₂ = c/2` (`LeeYangGram.shapForm_omegaVir_self`).  This is the sign cross-check. -/
theorem canB_L2_L2_eq_shapForm :
    (canB c).form (L2vac c) (L2vac c)
      = RigidBridge.shapForm (virasoroVOA c) (vacVec_ne_zero c) 2
          ⟨omegaVir c, omegaVir_mem_gradingVir_two c⟩
          ⟨omegaVir c, omegaVir_mem_gradingVir_two c⟩ := by
  rw [canB_L2_L2, shapForm_omegaVir_self]

/-! ### Why the level-4 `shapForm` matrix may **not** be reused

Neither level-4 basis vector is quasi-primary, so `canB_eq_signed_shapForm_of_quasiPrimary`
does not apply to either of them, and the level-4 `shapForm` Gram matrix is a matrix of a
genuinely different form.  Its determinant happens to be `21 ×` the right one; its *rank* carries
no such guarantee. -/

/-- `L₋₄|0⟩` is **not** quasi-primary: `L₁L₋₄|0⟩ = 5L₋₃|0⟩ ≠ 0`. -/
theorem L4vac_not_quasiPrimary : Lop c 1 (L4vac c) ≠ 0 := by
  rw [Lop_one_L4vac]
  simpa using L3vac_ne_zero c

/-- `L₋₂²|0⟩` is **not** quasi-primary either: `L₁L₋₂²|0⟩ = 3L₋₃|0⟩ ≠ 0`.  (This is the half the
panel recipe missed — it noted only `L₋₄|0⟩`.) -/
theorem L2L2vac_not_quasiPrimary : Lop c 1 (L2L2vac c) ≠ 0 := by
  rw [Lop_one_L2L2vac]
  simpa using L3vac_ne_zero c

/-- The quasi-primary subspace of `𝒱₄` is the single line `ℂ ∙ (5L₋₂²|0⟩ - 3L₋₄|0⟩)`; here is
its generator, verified quasi-primary.  So at most a one-dimensional slice of the level-4 Gram
matrix could ever be read off `shapForm`. -/
theorem qp4_quasiPrimary :
    Lop c 1 ((5 : ℂ) • L2L2vac c - (3 : ℂ) • L4vac c) = 0 := by
  rw [map_sub, map_smul, map_smul, Lop_one_L2L2vac, Lop_one_L4vac, smul_smul, smul_smul]
  norm_num

/-! ## §7  The Lee–Yang calibration: at `c = -22/5` the rank drops to `1` -/

/-- The universal vacuum module has exactly two independent states at weight four. This dimension refers to the universal module, before its radical is divided out. -/
theorem finrank_grading_four : finrank ℂ ((virasoroVOA c).grading 4) = 2 :=
  VirDefLow.finrank_gradingVir_four c

/-- **The calibration.**  At `c = -22/5` the level-4 Gram matrix of the *canonical* form has
rank `1`, matching the independent ground truth `dim V(-22/5,0)₄ = 2`,
`dim L(-22/5,0)₄ = 1` (`LeeYangKac.finrank_maxIdealVir_leeYang_inf_grading_four`).

Note the direction: the rank identity `rank_canGram4_add_finrank` plus the *known* level-4
radical dimension gives the rank.  Read the other way it is the statement that a level-4 Gram
computation determines the graded dimension of the simple quotient. -/
theorem rank_canGram4_leeYang : (canGram4 leeYangC).rank = 1 := by
  have h := rank_canGram4_add_finrank leeYangC
  rw [finrank_grading_four leeYangC] at h
  have hrad : finrank ℂ (QuotVOA.maxGradedIdeal (virasoroVOA leeYangC)
      ⊓ (virasoroVOA leeYangC).grading 4 : Submodule ℂ (VirUniv leeYangC)) = 1 :=
    LeeYangKac.finrank_maxIdealVir_leeYang_inf_grading_four
  rw [hrad] at h
  omega

/-- Consistency: at `c = -22/5` the determinant does vanish, so the matrix is degenerate — but
degenerate is all a determinant says.  `rank_canGram4_leeYang` is the sharp statement. -/
theorem det_canGram4_leeYang : (canGram4 leeYangC).det = 0 :=
  (det_canGram4_eq_zero_iff leeYangC).mpr (Or.inr rfl)

/-! ## §8  The calibration run FORWARD: the Gram matrix *predicts* `dim L(-22/5,0)₄`

§7 reads the bridge **backwards**: it takes the level-4 radical dimension as already known (from
`LeeYangKac`, proved by an explicit description of the Lee–Yang submodule) and deduces the rank.
That is a consistency check, not a computation.

The direction the Gram-rank spine exists for is the other one — compute the rank **of the
matrix**, and *read off* the graded dimension of the simple quotient.  Nothing in this section
uses any prior knowledge of the Lee–Yang ideal, so
`finrank_maxGradedIdeal_leeYang_four_from_gram` is a genuinely independent second proof of
`dim L(-22/5,0)₄ = 1`, and the agreement with
`LeeYangKac.finrank_maxIdealVir_leeYang_inf_grading_four` is a real cross-validation of both
routes rather than a restatement. -/

/-- The level-4 matrix with its entries evaluated at `c = -22/5`:
`c(c+8)/2 = -198/25`, `3c = -66/5`, `5c = -22`. -/
theorem canGram4_leeYang_eq :
    canGram4 leeYangC = !![-(198 : ℂ) / 25, -66 / 5; -66 / 5, -22] := by
  rw [canGram4_eq, leeYangC]
  norm_num [Matrix.of_apply]

/-- The degeneracy at `c = -22/5`, made structural: the matrix is a **rank-one outer product**
`M = w vᵀ`, with `w = (3, 5)` and `v = (-66/25, -22/5)`. -/
theorem canGram4_leeYang_vecMulVec :
    canGram4 leeYangC = Matrix.vecMulVec ![(3 : ℂ), 5] ![-(66 : ℂ) / 25, -22 / 5] := by
  rw [canGram4_leeYang_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.vecMulVec_apply]

/-- At the Lee–Yang charge the canonical Gram matrix is an outer product, so all its columns lie in one line and its rank is at most one. -/
theorem rank_canGram4_leeYang_le_one : (canGram4 leeYangC).rank ≤ 1 := by
  rw [canGram4_leeYang_vecMulVec]
  exact Matrix.rank_vecMulVec_le _ _

/-- `1 ≤ rank`, because the `(1,1)` entry `5c = -22` is nonzero: the `1 × 1` submatrix it spans
is invertible, and passing to a submatrix cannot raise the rank. -/
theorem one_le_rank_canGram4_leeYang : 1 ≤ (canGram4 leeYangC).rank := by
  have hsub : ((canGram4 leeYangC).submatrix (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1)).rank
      ≤ (canGram4 leeYangC).rank := Matrix.rank_submatrix_le _ _ _
  have hunit :
      IsUnit ((canGram4 leeYangC).submatrix (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one]
    simp only [Matrix.submatrix_apply]
    rw [canGram4_leeYang_eq]
    norm_num
  rwa [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin] at hsub

/-- The rank of the level-4 Gram matrix at `c = -22/5`, computed **from the matrix itself** —
independently of `rank_canGram4_leeYang`, which gets the same number out of the already-known
radical dimension. -/
theorem rank_canGram4_leeYang_direct : (canGram4 leeYangC).rank = 1 :=
  le_antisymm rank_canGram4_leeYang_le_one one_le_rank_canGram4_leeYang

/-- **The forward calibration.**  From the level-4 Gram matrix alone, the maximal graded
ideal of `V(-22/5, 0)` is one-dimensional at level `4`; equivalently `dim L(-22/5,0)₄ = 2 - 1 = 1`.

This is the statement the Gram-rank spine is built to produce: a determinant would only have said
"degenerate somewhere", and the rank is what fixes the graded dimension. -/
theorem finrank_maxGradedIdeal_leeYang_four_from_gram :
    finrank ℂ (QuotVOA.maxGradedIdeal (virasoroVOA leeYangC) ⊓ (virasoroVOA leeYangC).grading 4 :
        Submodule ℂ (VirUniv leeYangC)) = 1 := by
  have h := rank_canGram4_add_finrank leeYangC
  rw [finrank_grading_four leeYangC, rank_canGram4_leeYang_direct] at h
  omega


/-! ## §9  ⚠ Honest calibration: at level 4 the correction changes **no number**

§3 and the file preamble are right that `LeeYangKac.gram4` is the matrix of a *different form*,
and right that **a determinant does not determine a rank**.  It would be over-claiming to leave
it there, so here is the sharp statement: at level `4` the two matrices have the **same rank at
every central charge**, so the pre-existing `LeeYangKac` rank conclusion was never wrong.

The reason is that a `2 × 2` rank is pinned by its determinant together with "is the matrix
zero", and the two matrices vanish identically at the same `c` (namely `c = 0`, from the entries
`105c` and `-5c`) and have proportional determinants.  What *was* wrong is the **entries**
(`c²/2 + 40c` against the true `c²/2 + 4c`) and the justification.

The methodological point becomes load-bearing only from level `5` upward, where a `≥ 3 × 3`
matrix can have two different ranks at a shared determinant zero.  Recorded here so that level 4
is not re-derived a third time in the expectation of a different answer. -/

/-- At zero charge all four entries of the canonical weight-four Gram matrix vanish. The entire weight-four space is then orthogonal to itself. -/
theorem canGram4_zero : canGram4 0 = 0 := by
  rw [canGram4_eq]; ext i j; fin_cases i <;> fin_cases j <;> norm_num

/-- The alternative top-mode pairing also gives the zero weight-four matrix at zero charge, despite differing from the canonical form at general charge. -/
theorem gram4_zero (hvac : (virasoroVOA (0 : ℂ)).vacuum ≠ 0) :
    LeeYangKac.gram4 0 hvac = 0 := by
  rw [LeeYangKac.gram4_eq]; ext i j; fin_cases i <;> fin_cases j <;> norm_num

/-- Away from zero and the Lee–Yang charge, the canonical weight-four Gram matrix is invertible because its determinant is nonzero. -/
theorem canGram4_isUnit (h0 : c ≠ 0) (hLY : c ≠ leeYangC) : IsUnit (canGram4 c) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h
  rcases (det_canGram4_eq_zero_iff c).mp h with h | h
  · exact h0 h
  · exact hLY h

/-- The alternative top-mode Gram matrix is invertible at the same nonexceptional charges: its determinant differs from the canonical determinant by the nonzero factor twenty-one. -/
theorem gram4_isUnit (hvac : (virasoroVOA c).vacuum ≠ 0) (h0 : c ≠ 0) (hLY : c ≠ leeYangC) :
    IsUnit (LeeYangKac.gram4 c hvac) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, LeeYangKac.det_gram4]
  intro h
  have h' : (canGram4 c).det = 0 := by rw [det_canGram4]; linear_combination h / 21
  rcases (det_canGram4_eq_zero_iff c).mp h' with h1 | h1
  · exact h0 h1
  · exact hLY h1

/-- The `shapForm` matrix is *also* a rank-one outer product at `c = -22/5`. -/
theorem gram4_leeYang_vecMulVec (hvac : (virasoroVOA leeYangC).vacuum ≠ 0) :
    LeeYangKac.gram4 leeYangC hvac
      = Matrix.vecMulVec ![(3 : ℂ), 5] ![-(1386 : ℂ) / 25, -462 / 5] := by
  rw [LeeYangKac.gram4_eq, leeYangC]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.vecMulVec_apply]

/-- The alternative top-mode matrix has rank exactly one at the Lee–Yang charge. An outer-product expression gives the upper bound, and a nonzero entry supplies the lower bound. -/
theorem rank_gram4_leeYang (hvac : (virasoroVOA leeYangC).vacuum ≠ 0) :
    (LeeYangKac.gram4 leeYangC hvac).rank = 1 := by
  refine le_antisymm ?_ ?_
  · rw [gram4_leeYang_vecMulVec]
    exact Matrix.rank_vecMulVec_le _ _
  · have hsub :
        ((LeeYangKac.gram4 leeYangC hvac).submatrix
            (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1)).rank
          ≤ (LeeYangKac.gram4 leeYangC hvac).rank := Matrix.rank_submatrix_le _ _ _
    have hunit : IsUnit ((LeeYangKac.gram4 leeYangC hvac).submatrix
        (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one]
      simp only [Matrix.submatrix_apply]
      rw [LeeYangKac.gram4_eq, leeYangC]
      norm_num
    rwa [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin] at hsub

/-- **The two level-4 matrices, of two genuinely different forms, have the same rank at every
central charge.**  So the level-4 *conclusion* drawn from `LeeYangKac.gram4` stands; only its
derivation had to be replaced.  ⚠ Do not read this as licence to substitute one form for the
other in general — it is a `2 × 2` accident, not a theorem about forms. -/
theorem rank_gram4_eq_rank_canGram4 (hvac : (virasoroVOA c).vacuum ≠ 0) :
    (LeeYangKac.gram4 c hvac).rank = (canGram4 c).rank := by
  by_cases h0 : c = 0
  · subst h0
    rw [gram4_zero, canGram4_zero]
  · by_cases hLY : c = leeYangC
    · subst hLY
      rw [rank_gram4_leeYang, rank_canGram4_leeYang_direct]
    · rw [Matrix.rank_of_isUnit _ (gram4_isUnit c hvac h0 hLY),
        Matrix.rank_of_isUnit _ (canGram4_isUnit c h0 hLY)]

end VOA.VirGram4
