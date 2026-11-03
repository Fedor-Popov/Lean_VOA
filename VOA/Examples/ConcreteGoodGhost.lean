/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteGoodInterpreted
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Algebra.DirectSum.Finsupp

/-!
# The ghost form and the ghost `R`-grading

The ghost Fock space `FockSF` of one `bc` pair is the exterior algebra on the creation modes
`(k, a) : ℕ × Fin 2` (`a = 0`: `b_{-k-1}`, weight `k + 1`, ghost number `-1`; `a = 1`: `c_{-k}`,
weight `k`, ghost number `+1`). Mathlib's monomial basis `Basis.ExteriorAlgebra` (indexed by finite
sets of modes, in lexicographic order) makes it a space with a basis, and every basis monomial is
one of the repository's words `stWordSF` (`fockBasis_eq_word`).

* `basisForm b w` (generic): the form in which the basis `b` is orthogonal with
  `‖b s‖² = w s`; `basisForm_pos` for `w > 0`; `basisDeg` (pieces spanned by basis vectors of one
  index) is orthogonal and spanning.
* `fockForm w`, `fockDeg`: the ghost form and grading of one pair. The `2R` coordinate of a
  monomial counts its modes other than `c_0`, each with `R = 1/2` (Beem–Garner, Remark 3.6:
  `η⁺ = b`, `η⁻ = ∂c`, so `c_0` carries no `R`); the ghost number and the conformal weight are the
  repository's `ghNum`, `ghWeight`.
* `ghostForm w` on `Sl2GhostSpace = (FockSF ⊗ FockSF) ⊗ FockSF` and `ghostForm_pos`
  (**discharges `hG` for every positive weight function**), and `ghostRGrading w`
  (**discharges `GhostRGrading`**).
* `standardGhostForm`: `w ≡ 1`, i.e. monomials orthonormal: the convention `b_n† = c_{-n}`.
* `bgGhostForm`: Beem–Garner's normalization (`η⁺ = b`, `η⁻ = ∂c`): mode norms `n` for `b_{-n}`
  and `1/n` for `c_{-n}`, multiplicative on monomials; `bgGhostForm_pos`.

Everything is proved outright. **Scope:** which `w` makes the remaining Kähler relation
`InterpretedKahlerAnticomm` and the conjugation data hold is not addressed here. The relation
`(𝐐⁻)† = S⁺ - Q⁺` that defines the derived `𝐐⁺` depends on `w`; Beem–Garner's second differential
is adjoint-related to `𝐐⁻` for *their* form, `bgGhostForm` (up to the overall sign convention
`c = ±1`, which does not affect the Kähler relation). With `standardGhostForm` the derived `𝐐⁺`
is in general a different operator.
-/

namespace VOA.ConcreteHodge

open VOA.SympFerm VOA.Ghost Sl2SemiInfinite
open scoped TensorProduct DirectSum

noncomputable section

universe u v

/-! ### Generic: the form of a weighted orthogonal basis -/

section BasisForm

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {κ : Type v}

/-- The weighted standard form `w · z̄ z'` on `ℂ`. -/
def stdForm (w : ℝ) : SesqForm ℂ where
  toFun a b := (w : ℂ) * (starRingEnd ℂ) a * b
  add_left _ _ _ := by simp only [map_add]; ring
  smul_left _ _ _ := by simp only [smul_eq_mul, map_mul]; ring
  add_right _ _ _ := by ring
  smul_right _ _ _ := by simp only [smul_eq_mul]; ring

theorem stdForm_pos {w : ℝ} (hw : 0 < w) : IsPosOn (stdForm w) ⊤ := by
  intro z _ hz
  refine ⟨w * Complex.normSq z, mul_pos hw (Complex.normSq_pos.mpr hz), ?_⟩
  change (w : ℂ) * (starRingEnd ℂ) z * z = _
  rw [mul_assoc, mul_comm ((starRingEnd ℂ) z), Complex.mul_conj]
  push_cast; ring

open Classical in
/-- **The form of a weighted orthogonal basis**: `b` orthogonal, `‖b s‖² = w s`. -/
def basisForm (b : Module.Basis κ ℂ V) (w : κ → ℝ) : SesqForm V :=
  (orthSum (fun s => stdForm (w s))).comap
    ((finsuppLEquivDirectSum ℂ ℂ κ).toLinearMap ∘ₗ b.repr.toLinearMap)

theorem basisForm_pos (b : Module.Basis κ ℂ V) (w : κ → ℝ) (hw : ∀ s, 0 < w s) :
    IsPosOn (basisForm b w) ⊤ := by
  classical
  apply SesqForm.isPosOn_comap _ (isPosOn_orthSum _ fun s => stdForm_pos (hw s))
  exact (finsuppLEquivDirectSum ℂ ℂ κ).injective.comp b.repr.injective

theorem basisForm_basis_ne (b : Module.Basis κ ℂ V) (w : κ → ℝ) {s t : κ} (hst : s ≠ t) :
    basisForm b w (b s) (b t) = 0 := by
  classical
  change (orthSum (fun s : κ => stdForm (w s))).toFun
    (finsuppLEquivDirectSum ℂ ℂ κ (b.repr (b s)))
    (finsuppLEquivDirectSum ℂ ℂ κ (b.repr (b t))) = 0
  rw [b.repr_self, b.repr_self, finsuppLEquivDirectSum_single, finsuppLEquivDirectSum_single,
    DirectSum.lof_eq_of, DirectSum.lof_eq_of]
  convert orthSum_of_ne (fun s => stdForm (w s)) hst (1 : ℂ) (1 : ℂ)

/-- The pieces spanned by the basis vectors of one index. -/
def basisDeg {ι : Type*} (b : Module.Basis κ ℂ V) (f : κ → ι) (i : ι) : Submodule ℂ V :=
  Submodule.span ℂ (b '' {s | f s = i})

theorem basis_mem_basisDeg {ι : Type*} (b : Module.Basis κ ℂ V) (f : κ → ι) (s : κ) :
    b s ∈ basisDeg b f (f s) :=
  Submodule.subset_span ⟨s, rfl, rfl⟩

theorem basisDeg_orth {ι : Type*} (b : Module.Basis κ ℂ V) (w : κ → ℝ) (f : κ → ι) :
    ∀ i j, i ≠ j → ∀ x ∈ basisDeg b f i, ∀ y ∈ basisDeg b f j, basisForm b w x y = 0 := by
  intro i j hij x hx y hy
  refine sesq_span_left _ (fun x hx => ?_) x hx
  refine sesq_span_right _ (fun y hy => ?_) y hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  refine basisForm_basis_ne b w fun hst => hij ?_
  rw [← hs, ← ht, hst]

theorem basisDeg_span {ι : Type*} (b : Module.Basis κ ℂ V) (f : κ → ι) :
    iSup (basisDeg b f) = ⊤ := by
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  exact Submodule.mem_iSup_of_mem (f s) (basis_mem_basisDeg b f s)

theorem basisDeg_le {ι : Type*} (b : Module.Basis κ ℂ V) (f : κ → ι) (F : ι → Submodule ℂ V)
    (hF : ∀ s, b s ∈ F (f s)) (i : ι) : basisDeg b f i ≤ F i := by
  rw [basisDeg, Submodule.span_le]
  rintro _ ⟨s, hs, rfl⟩
  exact hs ▸ hF s

end BasisForm

/-! ### The monomial basis of one ghost pair -/

/-- Modes, linearly ordered lexicographically. -/
abbrev ModeIdx := Lex (ℕ × Fin 2)

/-- The basis of single modes of `SFModes`. -/
def sfBasis : Module.Basis ModeIdx ℂ SFModes :=
  (Finsupp.basisSingleOne).reindex toLex

theorem sfBasis_apply (p : ModeIdx) : sfBasis p = Finsupp.single (ofLex p) (1 : ℂ) := by
  simp [sfBasis, Module.Basis.reindex_apply]

/-- **The monomial basis of `FockSF`.** -/
def fockBasis : Module.Basis (Finset ModeIdx) ℂ FockSF := sfBasis.ExteriorAlgebra

theorem prod_ofFn_eq_stWordSF : ∀ (n : ℕ) (e : Fin n → ModeIdx),
    (List.ofFn fun i => ExteriorAlgebra.ι ℂ (sfBasis (e i))).prod =
      stWordSF (List.ofFn fun i => ofLex (e i))
  | 0, _ => by simp
  | n + 1, e => by
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, stWordSF_cons,
        prod_ofFn_eq_stWordSF n (fun i => e i.succ), sfBasis_apply]

/-- The word of a basis monomial: its modes in increasing lexicographic order. -/
def fockWord (s : Finset ModeIdx) : SFWord :=
  List.ofFn fun i => ofLex ((Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.prodEquiv.symm s).2) i)

/-- Every basis monomial is one of the repository's words. -/
theorem fockBasis_eq_word (s : Finset ModeIdx) : fockBasis s = stWordSF (fockWord s) := by
  rw [fockBasis, ExteriorAlgebra.basis_apply]
  exact prod_ofFn_eq_stWordSF s.card
    (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.prodEquiv.symm s).2)

theorem fockWord_length (s : Finset ModeIdx) : (fockWord s).length = s.card := by
  simp [fockWord]

theorem fockWord_empty : fockWord ∅ = [] :=
  List.eq_nil_of_length_eq_zero (by rw [fockWord_length, Finset.card_empty])

/-- `2R` of one mode: `0` for `c_0`, `1` otherwise. -/
def modeR (p : ℕ × Fin 2) : ℤ := if p = (0, 1) then 0 else 1

/-- `2R` of a word. -/
def wordR (l : SFWord) : ℤ := (l.map modeR).sum

/-- The index `((2R, gh), weight)` of a basis monomial. -/
def fockIndex (s : Finset ModeIdx) : (ℤ × ℤ) × ℂ :=
  ((wordR (fockWord s), ghNum (fockWord s)), (ghWeight (fockWord s) : ℂ))

/-- The `R`-grading of one ghost pair. -/
def fockDeg : (ℤ × ℤ) × ℂ → Submodule ℂ FockSF := basisDeg fockBasis fockIndex

/-- The ghost form of one pair, for a weight function on monomials. -/
def fockForm (w : Finset ModeIdx → ℝ) : SesqForm FockSF := basisForm fockBasis w

theorem fockDeg_le_weight (i : (ℤ × ℤ) × ℂ) : fockDeg i ≤ bcGhostSVA.grading (wtIndex i) :=
  basisDeg_le fockBasis fockIndex (fun i => bcGhostSVA.grading (wtIndex i))
    (fun s => by rw [fockBasis_eq_word]; exact stWordSF_mem_gradingGh _) i

theorem fockDeg_le_ghost (i : (ℤ × ℤ) × ℂ) : fockDeg i ≤ ghostGrading (ghIndex i) :=
  basisDeg_le fockBasis fockIndex (fun i => ghostGrading (ghIndex i))
    (fun s => by rw [fockBasis_eq_word]; exact stWordSF_mem_ghostGrading _) i

/-! ### Three pairs -/

/-- **The ghost form** on `Sl2GhostSpace = (FockSF ⊗ FockSF) ⊗ FockSF`. -/
def ghostForm (w : Finset ModeIdx → ℝ) : SesqForm Sl2GhostSpace :=
  ((fockForm w).tensor (fockForm w)).tensor (fockForm w)

/-- **Positivity of the ghost form** (the input `hG`), for every positive weight function. -/
theorem ghostForm_pos (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s) :
    IsPosOn (ghostForm w) ⊤ :=
  SesqForm.isPosOn_tensor _ _ (SesqForm.isPosOn_tensor _ _ (basisForm_pos _ _ hw)
    (basisForm_pos _ _ hw)) (basisForm_pos _ _ hw)

/-- The ghost `R`-grading on three pairs. -/
def ghostDeg : (ℤ × ℤ) × ℂ → Submodule ℂ Sl2GhostSpace :=
  tensorDeg (tensorDeg fockDeg fockDeg) fockDeg

theorem ghostDeg_le_weight (i : (ℤ × ℤ) × ℂ) :
    ghostDeg i ≤ sl2GhostSVA.grading (wtIndex i) := by
  refine tensorDeg_le wtIndex _ _ ghostPairSVA.grading bcGhostSVA.grading sl2GhostSVA.grading
    ?_ ?_ fockDeg_le_weight i
  · intro k k' x y hx hy
    exact TensorVA.tmul_mem_tenGrading ghostPairSVA bcGhostSVA hx (by rwa [add_sub_cancel_left])
  · intro j
    refine tensorDeg_le wtIndex _ _ bcGhostSVA.grading bcGhostSVA.grading ghostPairSVA.grading
      ?_ fockDeg_le_weight fockDeg_le_weight j
    intro k k' x y hx hy
    exact TensorVA.tmul_mem_tenGrading bcGhostSVA bcGhostSVA hx (by rwa [add_sub_cancel_left])

theorem ghostDeg_le_ghost (i : (ℤ × ℤ) × ℂ) : ghostDeg i ≤ sl2GhostGrading (ghIndex i) := by
  refine tensorDeg_le ghIndex _ _ ghostPairGrading ghostGrading sl2GhostGrading
    (fun k k' x y hx hy => tmul_mem_tensorGhostGrading _ _ hx hy) ?_ fockDeg_le_ghost i
  intro j
  exact tensorDeg_le ghIndex _ _ ghostGrading ghostGrading ghostPairGrading
    (fun k k' x y hx hy => tmul_mem_tensorGhostGrading _ _ hx hy) fockDeg_le_ghost
    fockDeg_le_ghost j

/-- **The ghost `R`-grading input**, orthogonal for `ghostForm w` (any `w`). -/
def ghostRGrading (w : Finset ModeIdx → ℝ) : GhostRGrading (ghostForm w) where
  deg := ghostDeg
  span := tensorDeg_span _ _ (tensorDeg_span _ _ (basisDeg_span _ _) (basisDeg_span _ _))
    (basisDeg_span _ _)
  orth := tensorDeg_orth _ _ _ _ (tensorDeg_orth _ _ _ _ (basisDeg_orth _ _ _)
    (basisDeg_orth _ _ _)) (basisDeg_orth _ _ _)
  le_weight := ghostDeg_le_weight
  le_ghost := ghostDeg_le_ghost

/-- The standard ghost form: monomials orthonormal (`b_n† = c_{-n}`). -/
def standardGhostForm : SesqForm Sl2GhostSpace := ghostForm fun _ => 1

theorem standardGhostForm_pos : IsPosOn standardGhostForm ⊤ :=
  ghostForm_pos _ fun _ => one_pos

/-- The Beem–Garner norm of one creation mode. With `η⁺ = b`, `η⁻ = ∂c`,
`{η^a_m, η^b_n} = m Ω^{ab} δ_{m+n,0}` and `(η^a_{-n})† = ±Ω_{ab} η^b_n`, one finds
`‖b_{-n}|0⟩‖² = n` and `‖c_{-n}|0⟩‖² = 1/n` (`n ≥ 1`); `c_0` does not occur on relative states
and is given norm `1`. Mode `(k, 0)` is `b_{-k-1}`, mode `(k, 1)` is `c_{-k}`. -/
def bgModeNorm (p : ℕ × Fin 2) : ℝ :=
  if p.2 = 0 then (p.1 : ℝ) + 1 else if p.1 = 0 then 1 else 1 / (p.1 : ℝ)

theorem bgModeNorm_pos (p : ℕ × Fin 2) : 0 < bgModeNorm p := by
  unfold bgModeNorm
  split_ifs with h1 h2
  · positivity
  · exact one_pos
  · have : (0 : ℝ) < p.1 := by exact_mod_cast Nat.pos_of_ne_zero h2
    positivity

/-- The Beem–Garner weight of a monomial: the product of its mode norms. -/
def bgGhostWeight (s : Finset ModeIdx) : ℝ := ∏ p ∈ s, bgModeNorm (ofLex p)

theorem bgGhostWeight_pos (s : Finset ModeIdx) : 0 < bgGhostWeight s :=
  Finset.prod_pos fun _ _ => bgModeNorm_pos _

/-- **The Beem–Garner-normalized ghost form** (monomials orthogonal, multiplicative mode
norms `n` for `b_{-n}` and `1/n` for `c_{-n}`), and its positivity. -/
def bgGhostForm : SesqForm Sl2GhostSpace := ghostForm bgGhostWeight

theorem bgGhostForm_pos : IsPosOn bgGhostForm ⊤ := ghostForm_pos _ bgGhostWeight_pos

end

end VOA.ConcreteHodge
