/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.DSMorphismSl2

/-!
# Three pairs of ghosts for relative semi-infinite `sl₂` cohomology

The state space is `(bc ⊗ bc) ⊗ bc`, with the Koszul signs supplied by
`TensorVA.tensorSVA`.  Both tensor products are constructed without additional
grading hypotheses: the one-pair weights are nonnegative integers, and the
convolution lemmas of `DSMorphismSl2` discharge finite dimensionality.

The total ghost number is the sum of the three one-pair ghost numbers.  Its
components form an internal direct sum and refine the tensor parity.  The six
generator states have weights `1, 0` and ghost numbers `-1, +1`.

The full ghost affine-current action is proved downstream in
`Sl2SemiInfiniteGhostAffine`; the cubic BRST self-product is computed in
`Sl2SemiInfiniteCubicNilpotency`. This file constructs their actual carrier
and generators.
-/

namespace VOA.Sl2SemiInfinite

open scoped TensorProduct
open Module (End)

section TensorCompatibility

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- The parity involution of a tensor product is the tensor product of the two
parity involutions. -/
theorem parityInvol_tensorSVA (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) :
    (TensorVA.parGr (TensorVA.tensorSVA V W hV hW hg)).parityInvol =
      TensorVA.totInvol V W := by
  apply LinearMap.ext
  intro u
  have hu : u ∈ ⨆ p, TensorVA.tenParity V W p := by
    rw [TensorVA.tenParity_iSup_eq_top]
    trivial
  refine Submodule.iSup_induction' (motive := fun x _ =>
    (TensorVA.parGr (TensorVA.tensorSVA V W hV hW hg)).parityInvol x =
      TensorVA.totInvol V W x) _ ?_ ?_ ?_ hu
  · intro p x hx
    rw [(TensorVA.parGr (TensorVA.tensorSVA V W hV hW hg)).parityInvol_homog
      (show x ∈ (TensorVA.parGr (TensorVA.tensorSVA V W hV hW hg)).parity p from hx),
      TensorVA.totInvol_tenParity V W p hx]
  · simp only [map_zero]
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy]

/-- Parity compatibility is preserved by tensor products. -/
theorem parityCompatible_tensorSVA (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) :
    TensorVA.ParityCompatible (TensorVA.tensorSVA V W hV hW hg) := by
  intro h u hu
  rw [parityInvol_tensorSVA]
  change TensorVA.totInvol V W u ∈ TensorVA.tenGrading V W h
  refine TensorVA.tenGrading_induction V W
    (motive := fun x => TensorVA.totInvol V W x ∈ TensorVA.tenGrading V W h)
    ?_ ?_ ?_ ?_ hu
  · change TensorVA.totInvol V W 0 ∈ TensorVA.tenGrading V W h
    rw [map_zero]; exact Submodule.zero_mem _
  · intro x y hx hy
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x hx
    rw [map_smul]; exact Submodule.smul_mem _ c hx
  · intro h₁ x hx y hy
    rw [TensorVA.totInvol, TensorProduct.map_tmul]
    exact TensorVA.tmul_mem_tenGrading V W (hV h₁ x hx) (hW (h - h₁) y hy)

/-- Nonnegative integral weight support is preserved by tensor products. -/
theorem natSupported_tensorSVA (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W)
    (hnV : DSMor.NatSupported V.grading) (hnW : DSMor.NatSupported W.grading) :
    DSMor.NatSupported (TensorVA.tensorSVA V W hV hW hg).grading :=
  fun _ hh => DSMor.tenGrading_eq_bot_of_not_nat V W hnV hnW hh

/-- Tensoring two nonzero vacua gives a nonzero vacuum. -/
theorem tensorSVA_vacuum_ne_zero (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) (hv : V.vacuum ≠ 0) (hw : W.vacuum ≠ 0) :
    (TensorVA.tensorSVA V W hV hW hg).vacuum ≠ 0 := by
  intro hz
  apply hv
  apply DSMor.unitEmbed_injective W hw
  change V.vacuum ⊗ₜ[ℂ] W.vacuum = DSMor.unitEmbed W 0
  rw [map_zero]
  exact hz

end TensorCompatibility

/-- Two one-pair ghost Fock spaces. -/
abbrev GhostPairSpace := SympFerm.FockSF ⊗[ℂ] SympFerm.FockSF

/-- The three-pair ghost space; the parentheses fix all embedding conventions. -/
abbrev Sl2GhostSpace := GhostPairSpace ⊗[ℂ] SympFerm.FockSF

/-- The tensor product of the first two `bc` pairs. -/
noncomputable def ghostPairSVA : SuperVertexAlgebra GhostPairSpace :=
  TensorVA.tensorSVA Ghost.bcGhostSVA Ghost.bcGhostSVA
    DSMor.parityCompatible_bcGhostSVA DSMor.parityCompatible_bcGhostSVA
    (DSMor.tensorGradingHyp_of_natSupported _ _
      DSMor.natSupported_bcGhostSVA DSMor.natSupported_bcGhostSVA)

/-- The two-pair system is parity-compatible. -/
theorem parityCompatible_ghostPairSVA : TensorVA.ParityCompatible ghostPairSVA :=
  parityCompatible_tensorSVA _ _ _ _ _

/-- The two-pair system has nonnegative integral weight support. -/
theorem natSupported_ghostPairSVA : DSMor.NatSupported ghostPairSVA.grading :=
  natSupported_tensorSVA _ _ _ _ _
    DSMor.natSupported_bcGhostSVA DSMor.natSupported_bcGhostSVA

/-- The `sl₂` ghost vertex superalgebra: three independent `bc` pairs, each with
weights `(1,0)`, with all tensor-grading hypotheses discharged. -/
noncomputable def sl2GhostSVA : SuperVertexAlgebra Sl2GhostSpace :=
  TensorVA.tensorSVA ghostPairSVA Ghost.bcGhostSVA
    parityCompatible_ghostPairSVA DSMor.parityCompatible_bcGhostSVA
    (DSMor.tensorGradingHyp_of_natSupported _ _
      natSupported_ghostPairSVA DSMor.natSupported_bcGhostSVA)

/-- The three-pair system is parity-compatible. -/
theorem parityCompatible_sl2GhostSVA : TensorVA.ParityCompatible sl2GhostSVA :=
  parityCompatible_tensorSVA _ _ _ _ _

/-- The three-pair system has nonnegative integral weight support. -/
theorem natSupported_sl2GhostSVA : DSMor.NatSupported sl2GhostSVA.grading :=
  natSupported_tensorSVA _ _ _ _ _
    natSupported_ghostPairSVA DSMor.natSupported_bcGhostSVA

@[simp] theorem sl2GhostSVA_vacuum : sl2GhostSVA.vacuum =
    (SympFerm.vacSF ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] SympFerm.vacSF := rfl

/-- The three-pair construction has a nonzero vacuum. -/
theorem sl2GhostSVA_vacuum_ne_zero : sl2GhostSVA.vacuum ≠ 0 := by
  have hv : Ghost.bcGhostSVA.vacuum ≠ 0 := (one_ne_zero : (1 : SympFerm.FockSF) ≠ 0)
  have hp : ghostPairSVA.vacuum ≠ 0 := tensorSVA_vacuum_ne_zero _ _ _ _ _ hv hv
  exact tensorSVA_vacuum_ne_zero _ _ _ _ _ hp hv

section GhostGrading

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- Additive convolution of two integer gradings on a tensor product. -/
def tensorGhostGrading (P : ℤ → Submodule ℂ A) (Q : ℤ → Submodule ℂ B)
    (n : ℤ) : Submodule ℂ (A ⊗[ℂ] B) :=
  ⨆ j : ℤ, TensorVA.tenSub (P j) (Q (n - j))

/-- Ghost numbers add on pure tensors. -/
theorem tmul_mem_tensorGhostGrading (P : ℤ → Submodule ℂ A)
    (Q : ℤ → Submodule ℂ B) {m n : ℤ} {x : A} {y : B}
    (hx : x ∈ P m) (hy : y ∈ Q n) :
    x ⊗ₜ[ℂ] y ∈ tensorGhostGrading P Q (m + n) := by
  apply Submodule.mem_iSup_of_mem m
  apply TensorVA.tmul_mem_tenSub hx
  simpa only [add_sub_cancel_left] using hy

/-- The tensor ghost-number operator separates the convolution components. -/
theorem tensorGhostGrading_le_eigenspace (P : ℤ → Submodule ℂ A)
    (Q : ℤ → Submodule ℂ B) (NA : End ℂ A) (NB : End ℂ B)
    (hP : ∀ n : ℤ, P n ≤ Module.End.eigenspace NA (n : ℂ))
    (hQ : ∀ n : ℤ, Q n ≤ Module.End.eigenspace NB (n : ℂ)) (n : ℤ) :
    tensorGhostGrading P Q n ≤ Module.End.eigenspace (DSMor.L0tot NA NB) (n : ℂ) := by
  refine iSup_le fun j => ?_
  have h := DSMor.tenSub_le_eigen NA NB (j : ℂ) ((n - j : ℤ) : ℂ)
    (P j) (Q (n - j)) (hP j) (hQ (n - j))
  simpa only [Int.cast_sub, add_sub_cancel] using h

/-- Convolution preserves internal ghost-number decompositions. -/
theorem tensorGhostGrading_isInternal (P : ℤ → Submodule ℂ A)
    (Q : ℤ → Submodule ℂ B) (NA : End ℂ A) (NB : End ℂ B)
    (hP : ∀ n : ℤ, P n ≤ Module.End.eigenspace NA (n : ℂ))
    (hQ : ∀ n : ℤ, Q n ≤ Module.End.eigenspace NB (n : ℂ))
    (hiP : DirectSum.IsInternal P) (hiQ : DirectSum.IsInternal Q) :
    DirectSum.IsInternal (tensorGhostGrading P Q) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact ((Module.End.eigenspaces_iSupIndep (DSMor.L0tot NA NB)).comp
      (f := fun n : ℤ => (n : ℂ)) Int.cast_injective).mono
      (tensorGhostGrading_le_eigenspace P Q NA NB hP hQ)
  · refine TensorVA.eq_top_of_tmul_mem
      ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 hiP).2
      ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 hiQ).2 ?_
    intro m n x hx y hy
    exact Submodule.mem_iSup_of_mem (m + n) (tmul_mem_tensorGhostGrading P Q hx hy)

/-- Additive ghost gradings refining the factor parities also refine tensor parity. -/
theorem tensorGhostGrading_le_tenParity (V : SuperVertexAlgebra A)
    (W : SuperVertexAlgebra B) (P : ℤ → Submodule ℂ A) (Q : ℤ → Submodule ℂ B)
    (hP : ∀ n : ℤ, P n ≤ V.parity (n : ZMod 2))
    (hQ : ∀ n : ℤ, Q n ≤ W.parity (n : ZMod 2)) (n : ℤ) :
    tensorGhostGrading P Q n ≤ TensorVA.tenParity V W (n : ZMod 2) := by
  refine iSup_le fun j => ?_
  intro u hu
  refine TensorVA.tenSub_induction (P := P j) (Q := Q (n - j))
    (motive := fun x => x ∈ TensorVA.tenParity V W (n : ZMod 2))
    (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _)
    (fun c _ => Submodule.smul_mem _ c) ?_ hu
  intro x hx y hy
  apply TensorVA.tmul_mem_tenParity V W (hP j hx)
  simpa only [Int.cast_sub] using hQ (n - j) hy

end GhostGrading

/-- Ghost number on the first two pairs. -/
noncomputable def ghostPairGrading : ℤ → Submodule ℂ GhostPairSpace :=
  tensorGhostGrading Ghost.ghostGrading Ghost.ghostGrading

/-- The two-pair ghost-number operator. -/
noncomputable def ghostPairNumber : End ℂ GhostPairSpace := DSMor.L0tot Ghost.Ngh Ghost.Ngh

theorem ghostPairGrading_le_eigenspace (n : ℤ) :
    ghostPairGrading n ≤ Module.End.eigenspace ghostPairNumber (n : ℂ) :=
  tensorGhostGrading_le_eigenspace _ _ _ _
    Ghost.ghostGrading_le_eigenspace Ghost.ghostGrading_le_eigenspace n

theorem ghostPairGrading_isInternal : DirectSum.IsInternal ghostPairGrading :=
  tensorGhostGrading_isInternal _ _ _ _
    Ghost.ghostGrading_le_eigenspace Ghost.ghostGrading_le_eigenspace
    Ghost.ghostGrading_isInternal Ghost.ghostGrading_isInternal

theorem ghostPairGrading_le_parity (n : ℤ) :
    ghostPairGrading n ≤ ghostPairSVA.parity (n : ZMod 2) :=
  tensorGhostGrading_le_tenParity _ _ _ _
    Ghost.ghostGrading_le_evenOdd Ghost.ghostGrading_le_evenOdd n

/-- Total ghost number on the three `sl₂` ghost pairs. -/
noncomputable def sl2GhostGrading : ℤ → Submodule ℂ Sl2GhostSpace :=
  tensorGhostGrading ghostPairGrading Ghost.ghostGrading

/-- The total ghost-number operator. -/
noncomputable def sl2GhostNumber : End ℂ Sl2GhostSpace :=
  DSMor.L0tot ghostPairNumber Ghost.Ngh

theorem sl2GhostGrading_le_eigenspace (n : ℤ) :
    sl2GhostGrading n ≤ Module.End.eigenspace sl2GhostNumber (n : ℂ) :=
  tensorGhostGrading_le_eigenspace _ _ _ _
    ghostPairGrading_le_eigenspace Ghost.ghostGrading_le_eigenspace n

/-- The three-pair state space is the internal direct sum of its ghost-number pieces. -/
theorem sl2GhostGrading_isInternal : DirectSum.IsInternal sl2GhostGrading :=
  tensorGhostGrading_isInternal _ _ _ _
    ghostPairGrading_le_eigenspace Ghost.ghostGrading_le_eigenspace
    ghostPairGrading_isInternal Ghost.ghostGrading_isInternal

/-- Total ghost number reduces modulo two to the tensor parity. -/
theorem sl2GhostGrading_le_parity (n : ℤ) :
    sl2GhostGrading n ≤ sl2GhostSVA.parity (n : ZMod 2) :=
  tensorGhostGrading_le_tenParity _ _ _ _
    ghostPairGrading_le_parity Ghost.ghostGrading_le_evenOdd n

/-- The vacuum has total ghost number zero. -/
theorem sl2GhostSVA_vacuum_ghost : sl2GhostSVA.vacuum ∈ sl2GhostGrading 0 := by
  rw [sl2GhostSVA_vacuum]
  have hpair : SympFerm.vacSF ⊗ₜ[ℂ] SympFerm.vacSF ∈ ghostPairGrading 0 :=
    tmul_mem_tensorGhostGrading Ghost.ghostGrading Ghost.ghostGrading
      (m := 0) (n := 0) Ghost.vacSF_mem_ghostGrading Ghost.vacSF_mem_ghostGrading
  exact tmul_mem_tensorGhostGrading ghostPairGrading Ghost.ghostGrading
    (m := 0) (n := 0) hpair Ghost.vacSF_mem_ghostGrading

/-- Embed one state in the indicated ghost pair and put vacua in the other pairs. -/
noncomputable def ghostEmbed (a : Fin 3) (x : SympFerm.FockSF) : Sl2GhostSpace :=
  if a = 0 then (x ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] SympFerm.vacSF
  else if a = 1 then (SympFerm.vacSF ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] SympFerm.vacSF
  else (SympFerm.vacSF ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] x

/-- The antighost state in the indicated pair. -/
noncomputable def bGhost (a : Fin 3) : Sl2GhostSpace :=
  ghostEmbed a (SympFerm.stWordSF [((0, 0) : ℕ × Fin 2)])

/-- The ghost state in the indicated pair. -/
noncomputable def cGhost (a : Fin 3) : Sl2GhostSpace :=
  ghostEmbed a (SympFerm.stWordSF [((0, 1) : ℕ × Fin 2)])

/-- The unit embedding into any one of the three pairs preserves ghost number. -/
theorem ghostEmbed_ghost (a : Fin 3) {n : ℤ} {x : SympFerm.FockSF}
    (hx : x ∈ Ghost.ghostGrading n) : ghostEmbed a x ∈ sl2GhostGrading n := by
  unfold ghostEmbed
  split_ifs
  · simpa only [add_zero] using
      tmul_mem_tensorGhostGrading ghostPairGrading Ghost.ghostGrading
        (tmul_mem_tensorGhostGrading Ghost.ghostGrading Ghost.ghostGrading
          hx Ghost.vacSF_mem_ghostGrading) Ghost.vacSF_mem_ghostGrading
  · simpa only [add_zero, zero_add] using
      tmul_mem_tensorGhostGrading ghostPairGrading Ghost.ghostGrading
        (tmul_mem_tensorGhostGrading Ghost.ghostGrading Ghost.ghostGrading
          Ghost.vacSF_mem_ghostGrading hx) Ghost.vacSF_mem_ghostGrading
  · simpa only [zero_add] using
      tmul_mem_tensorGhostGrading ghostPairGrading Ghost.ghostGrading
        (tmul_mem_tensorGhostGrading Ghost.ghostGrading Ghost.ghostGrading
          Ghost.vacSF_mem_ghostGrading Ghost.vacSF_mem_ghostGrading) hx

/-- Antighosts have ghost number `-1`. -/
theorem bGhost_ghost (a : Fin 3) : bGhost a ∈ sl2GhostGrading (-1) := by
  apply ghostEmbed_ghost
  simpa only [Ghost.ghNum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, Ghost.ghCharge] using
    Ghost.stWordSF_mem_ghostGrading [((0, 0) : ℕ × Fin 2)]

/-- Ghosts have ghost number `+1`. -/
theorem cGhost_ghost (a : Fin 3) : cGhost a ∈ sl2GhostGrading 1 := by
  apply ghostEmbed_ghost
  simpa only [Ghost.ghNum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, Ghost.ghCharge] using
    Ghost.stWordSF_mem_ghostGrading [((0, 1) : ℕ × Fin 2)]

/-- All three antighost states are odd. -/
theorem bGhost_odd (a : Fin 3) : bGhost a ∈ sl2GhostSVA.parity 1 := by
  have h := sl2GhostGrading_le_parity (-1) (bGhost_ghost a)
  norm_num at h ⊢
  exact h

/-- All three ghost states are odd. -/
theorem cGhost_odd (a : Fin 3) : cGhost a ∈ sl2GhostSVA.parity 1 := by
  simpa only [Int.cast_one] using sl2GhostGrading_le_parity 1 (cGhost_ghost a)

/-- A convenient sum-index form of the tensor weight membership lemma. -/
theorem tmul_mem_tenGrading_add {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    {h k : ℂ} {x : A} {y : B} (hx : x ∈ V.grading h) (hy : y ∈ W.grading k) :
    x ⊗ₜ[ℂ] y ∈ TensorVA.tenGrading V W (h + k) := by
  apply TensorVA.tmul_mem_tenGrading V W hx
  simpa only [add_sub_cancel_left] using hy

/-- The unit embedding into any one of the three pairs preserves conformal weight. -/
theorem ghostEmbed_weight (a : Fin 3) {h : ℂ} {x : SympFerm.FockSF}
    (hx : x ∈ Ghost.bcGhostSVA.grading h) : ghostEmbed a x ∈ sl2GhostSVA.grading h := by
  unfold ghostEmbed
  split_ifs
  · simpa only [add_zero] using
      tmul_mem_tenGrading_add ghostPairSVA Ghost.bcGhostSVA
        (tmul_mem_tenGrading_add Ghost.bcGhostSVA Ghost.bcGhostSVA
          hx Ghost.bcGhostSVA.vacuum_mem) Ghost.bcGhostSVA.vacuum_mem
  · simpa only [add_zero, zero_add] using
      tmul_mem_tenGrading_add ghostPairSVA Ghost.bcGhostSVA
        (tmul_mem_tenGrading_add Ghost.bcGhostSVA Ghost.bcGhostSVA
          Ghost.bcGhostSVA.vacuum_mem hx) Ghost.bcGhostSVA.vacuum_mem
  · simpa only [zero_add] using
      tmul_mem_tenGrading_add ghostPairSVA Ghost.bcGhostSVA
        (tmul_mem_tenGrading_add Ghost.bcGhostSVA Ghost.bcGhostSVA
          Ghost.bcGhostSVA.vacuum_mem Ghost.bcGhostSVA.vacuum_mem) hx

/-- All three antighost states have conformal weight one. -/
theorem bGhost_weight (a : Fin 3) : bGhost a ∈ sl2GhostSVA.grading 1 := by
  apply ghostEmbed_weight
  simpa only [Ghost.stWordSF_singleton] using Ghost.b_mem_gradingGh_one

/-- All three ghost states have conformal weight zero. -/
theorem cGhost_weight (a : Fin 3) : cGhost a ∈ sl2GhostSVA.grading 0 := by
  apply ghostEmbed_weight
  simpa only [Ghost.stWordSF_singleton] using Ghost.c_mem_gradingGh_zero

section UnitField

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- A field placed in the left factor acts only in that factor. -/
theorem tenY_left_unit (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (a x : A) (y : B) (s : ℤ) :
    TensorVA.tenY V W (a ⊗ₜ[ℂ] W.vacuum) s (x ⊗ₜ[ℂ] y) =
      V.Y a s x ⊗ₜ[ℂ] y := by
  rw [TensorVA.tenY_tmul_parity V W a W.vacuum_parity,
    TensorVA.kappaTen_zero, LinearMap.id_apply, TensorVA.rawCoeff_tmul]
  rw [finsum_eq_single _ s (fun m hm => by
    rw [DSMor.Y_vacuum_applySVA, if_neg (by omega), TensorProduct.tmul_zero])]
  rw [sub_self, DSMor.Y_vacuum_applySVA, if_pos rfl]

/-- A right-factor field acts without a sign on a left-factor vacuum. -/
theorem tenY_right_unit (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    (b y : B) (s : ℤ) :
    TensorVA.tenY V W (V.vacuum ⊗ₜ[ℂ] b) s (V.vacuum ⊗ₜ[ℂ] y) =
      V.vacuum ⊗ₜ[ℂ] W.Y b s y := by
  have hΘ : TensorVA.kappaTen V W 1 (V.vacuum ⊗ₜ[ℂ] y) = V.vacuum ⊗ₜ[ℂ] y := by
    rw [TensorVA.kappaTen_tmul, (TensorVA.parGr V).koszulOp_homog 1
      (show V.vacuum ∈ (TensorVA.parGr V).parity 0 from V.vacuum_parity),
      koszul_zero_right, one_smul]
  rw [TensorVA.tenY_tmul_apply, hΘ, sub_self, map_zero, add_zero, ← two_smul ℂ,
    map_smul, smul_smul, show ((2 : ℂ)⁻¹ * 2) = 1 by norm_num, one_smul,
    TensorVA.rawCoeff_tmul]
  rw [finsum_eq_single _ 0 (fun m hm => by
    rw [DSMor.Y_vacuum_applySVA, if_neg hm, TensorProduct.zero_tmul])]
  rw [sub_zero, DSMor.Y_vacuum_applySVA, if_pos rfl]

end UnitField

/-- Each pair embeds as a vertex subalgebra, coefficient by coefficient. -/
theorem ghostEmbed_Y (a : Fin 3) (x y : SympFerm.FockSF) (s : ℤ) :
    sl2GhostSVA.Y (ghostEmbed a x) s (ghostEmbed a y) =
      ghostEmbed a (Ghost.YGh x s y) := by
  unfold ghostEmbed
  split_ifs
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      ((x ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s
      ((y ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] SympFerm.vacSF) = _
    rw [tenY_left_unit ghostPairSVA Ghost.bcGhostSVA]
    change TensorVA.tenY Ghost.bcGhostSVA Ghost.bcGhostSVA
      (x ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s (y ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ]
      SympFerm.vacSF = _
    rw [tenY_left_unit Ghost.bcGhostSVA Ghost.bcGhostSVA]
    rfl
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      ((SympFerm.vacSF ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s
      ((SympFerm.vacSF ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] SympFerm.vacSF) = _
    rw [tenY_left_unit ghostPairSVA Ghost.bcGhostSVA]
    change TensorVA.tenY Ghost.bcGhostSVA Ghost.bcGhostSVA
      (Ghost.bcGhostSVA.vacuum ⊗ₜ[ℂ] x) s
      (Ghost.bcGhostSVA.vacuum ⊗ₜ[ℂ] y) ⊗ₜ[ℂ]
      SympFerm.vacSF = _
    rw [tenY_right_unit Ghost.bcGhostSVA Ghost.bcGhostSVA]
    rfl
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      (ghostPairSVA.vacuum ⊗ₜ[ℂ] x) s (ghostPairSVA.vacuum ⊗ₜ[ℂ] y) = _
    rw [tenY_right_unit ghostPairSVA Ghost.bcGhostSVA]
    rfl

/-- Each pair embedding preserves all vertex-algebra products. -/
theorem ghostEmbed_mode (a : Fin 3) (x y : SympFerm.FockSF) (n : ℤ) :
    mode (sl2GhostSVA.Y (ghostEmbed a x)) n (ghostEmbed a y) =
      ghostEmbed a (mode (Ghost.YGh x) n y) :=
  ghostEmbed_Y a x y (-n - 1)

end VOA.Sl2SemiInfinite
