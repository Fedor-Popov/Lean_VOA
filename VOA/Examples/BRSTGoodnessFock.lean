/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteGoodGenerators
import VOA.Examples.Sl2SemiInfiniteGhostCAR
import VOA.Examples.Sl2SemiInfiniteContractions
import VOA.Examples.Sl2SemiInfiniteGhostModes

/-!
# The ghost `R`-grading is a word grading; ghost modes shift it

The ghost grading `fockDeg` of `ConcreteGoodGhost` is defined from Mathlib's *sorted* monomial
basis. Here it is identified with the grading spanned by **all** words of the repository
(`fockDeg_eq_wordDeg`), using three diagonal derivations (`2R`, ghost number, weight) whose joint
eigenvalues separate the basis monomials. Consequences, all proved outright:

* `creBase_mem_fockDeg`, `annBase_mem_fockDeg` — a creation (contraction) operator shifts the
  index `((2R, gh), weight)` by `+modeIdx p` (`-modeIdx p`);
* `ghField_mem_fockDeg` — every coefficient `ghField e j` of the `b`/`c` fields of one pair shifts
  the index by `ghShift e j`;
* `parityInvol_mem_fockDeg` and the pair version — the Koszul operators preserve the pieces;
* `ghostMode_mem_ghostDeg` — on the three-pair space every mode of every ghost generator
  shifts `ghostDeg` by `ghShift`;
* `antighostZeroShift` — **discharges `AntighostZeroShift`**.
-/

namespace VOA.ConcreteHodge

open VOA.SympFerm VOA.Ghost Sl2SemiInfinite
open scoped TensorProduct

noncomputable section

/-! ### Generic: diagonal operators read off basis coordinates -/

section Diagonal

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {κ : Type v}

theorem basis_repr_of_diag (b : Module.Basis κ ℂ V) (D : V →ₗ[ℂ] V) (μ : κ → ℂ)
    (hD : ∀ s, D (b s) = μ s • b s) (x : V) (s : κ) :
    b.repr (D x) s = μ s * b.repr x s := by
  classical
  have h : (Finsupp.lapply s ∘ₗ b.repr.toLinearMap ∘ₗ D) =
      μ s • (Finsupp.lapply s ∘ₗ b.repr.toLinearMap) := by
    refine b.ext fun t => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hD,
      LinearEquiv.map_smul, b.repr_self, Finsupp.lapply_apply, LinearMap.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs with h
    · subst h; ring
    · simp
  exact LinearMap.congr_fun h x

theorem basis_eigen_of_mem_support (b : Module.Basis κ ℂ V) (D : V →ₗ[ℂ] V) (μ : κ → ℂ)
    (hD : ∀ s, D (b s) = μ s • b s) {x : V} {c : ℂ} (hx : D x = c • x) {s : κ}
    (hs : b.repr x s ≠ 0) : μ s = c := by
  have h := basis_repr_of_diag b D μ hD x s
  rw [hx, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  exact (mul_right_cancel₀ hs h).symm

end Diagonal

/-! ### The word grading of one pair -/

/-- The index `((2R, gh), weight)` of one creation mode. -/
def modeIdx (p : ℕ × Fin 2) : (ℤ × ℤ) × ℂ :=
  ((modeR p, ghCharge p.2), ((ghModeWt p : ℕ) : ℂ))

/-- The index of a word. -/
def wordIdx (l : SFWord) : (ℤ × ℤ) × ℂ := ((wordR l, ghNum l), ((ghWeight l : ℕ) : ℂ))

@[simp] theorem wordIdx_nil : wordIdx [] = 0 := by
  simp [wordIdx, wordR, ghNum, ghWeight]

@[simp] theorem wordIdx_cons (p : ℕ × Fin 2) (l : SFWord) :
    wordIdx (p :: l) = modeIdx p + wordIdx l := by
  simp only [wordIdx, wordR, List.map_cons, List.sum_cons, ghNum_cons, ghWeight_cons,
    modeIdx, Prod.mk_add_mk, Nat.cast_add]

theorem fockIndex_eq (s : Finset ModeIdx) : fockIndex s = wordIdx (fockWord s) := rfl

/-- The span of all words of index `i`. -/
def wordDeg (i : (ℤ × ℤ) × ℂ) : Submodule ℂ FockSF :=
  Submodule.span ℂ (stWordSF '' {l | wordIdx l = i})

theorem stWordSF_mem_wordDeg (l : SFWord) : stWordSF l ∈ wordDeg (wordIdx l) :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

/-- The `2R` derivation. -/
def NR : Module.End ℂ FockSF := derivOf (diagMap fun p => ((modeR p : ℤ) : ℂ))

theorem NR_stWordSF (l : SFWord) : NR (stWordSF l) = ((wordR l : ℤ) : ℂ) • stWordSF l := by
  rw [NR, derivOf_diag_stWordSF, sum_map_intCast]
  rfl

theorem fockBasis_eigen_NR (s : Finset ModeIdx) :
    NR (fockBasis s) = ((fockIndex s).1.1 : ℂ) • fockBasis s := by
  rw [fockBasis_eq_word, NR_stWordSF]; rfl

theorem fockBasis_eigen_Ngh (s : Finset ModeIdx) :
    Ngh (fockBasis s) = ((fockIndex s).1.2 : ℂ) • fockBasis s := by
  rw [fockBasis_eq_word, Ngh_stWordSF]; rfl

theorem fockBasis_eigen_L0 (s : Finset ModeIdx) :
    L0Gh (fockBasis s) = (fockIndex s).2 • fockBasis s := by
  rw [fockBasis_eq_word, L0Gh_stWordSF]; rfl

/-- A joint eigenvector with eigenvalues `i` lies in `fockDeg i`. -/
theorem mem_fockDeg_of_eigen {i : (ℤ × ℤ) × ℂ} {x : FockSF}
    (h1 : NR x = ((i.1.1 : ℤ) : ℂ) • x) (h2 : Ngh x = ((i.1.2 : ℤ) : ℂ) • x)
    (h3 : L0Gh x = i.2 • x) : x ∈ fockDeg i := by
  rw [fockDeg, basisDeg, Module.Basis.mem_span_image]
  intro s hs
  have hs' : fockBasis.repr x s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have e1 := basis_eigen_of_mem_support fockBasis NR _ fockBasis_eigen_NR h1 hs'
  have e2 := basis_eigen_of_mem_support fockBasis Ngh _ fockBasis_eigen_Ngh h2 hs'
  have e3 := basis_eigen_of_mem_support fockBasis L0Gh _ fockBasis_eigen_L0 h3 hs'
  have e1' : (fockIndex s).1.1 = i.1.1 := by exact_mod_cast e1
  have e2' : (fockIndex s).1.2 = i.1.2 := by exact_mod_cast e2
  exact Prod.ext (Prod.ext e1' e2') e3

theorem wordDeg_le_fockDeg (i : (ℤ × ℤ) × ℂ) : wordDeg i ≤ fockDeg i := by
  rw [wordDeg, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : wordIdx l = i := hl
  subst hl'
  refine mem_fockDeg_of_eigen ?_ ?_ ?_
  · exact NR_stWordSF l
  · exact Ngh_stWordSF l
  · exact L0Gh_stWordSF l

theorem fockDeg_le_wordDeg (i : (ℤ × ℤ) × ℂ) : fockDeg i ≤ wordDeg i := by
  refine basisDeg_le fockBasis fockIndex wordDeg (fun s => ?_) i
  rw [fockBasis_eq_word, fockIndex_eq]
  exact stWordSF_mem_wordDeg _

/-- **The sorted-basis grading is the all-words grading.** -/
theorem fockDeg_eq_wordDeg (i : (ℤ × ℤ) × ℂ) : fockDeg i = wordDeg i :=
  le_antisymm (fockDeg_le_wordDeg i) (wordDeg_le_fockDeg i)

theorem creBase_mem_wordDeg (p : ℕ × Fin 2) {i : (ℤ × ℤ) × ℂ} {x : FockSF}
    (hx : x ∈ wordDeg i) : creBase p x ∈ wordDeg (i + modeIdx p) := by
  rw [wordDeg] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      have hl' : wordIdx l = i := hl
      subst hl'
      rw [creBase_stWordSF, add_comm, ← wordIdx_cons]
      exact stWordSF_mem_wordDeg _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem annBase_stWordSF_mem_wordDeg (p : ℕ × Fin 2) (l : SFWord) :
    annBase p (stWordSF l) ∈ wordDeg (wordIdx l - modeIdx p) := by
  induction l with
  | nil => rw [annBase_stWordSF_nil]; exact Submodule.zero_mem _
  | cons q rest ih =>
      rw [annBase_stWordSF_cons]
      refine Submodule.sub_mem _ ?_ ?_
      · by_cases h : p = q
        · subst h
          rw [if_pos rfl, one_smul, wordIdx_cons, add_sub_cancel_left]
          exact stWordSF_mem_wordDeg rest
        · rw [if_neg h, zero_smul]
          exact Submodule.zero_mem _
      · rw [show CliffordAlgebra.ι QSF (Finsupp.single q (1 : ℂ)) * annBase p (stWordSF rest)
            = creBase q (annBase p (stWordSF rest)) from by rw [creBase, LinearMap.mulLeft_apply]]
        have := creBase_mem_wordDeg q ih
        rwa [wordIdx_cons, show modeIdx q + wordIdx rest - modeIdx p =
          wordIdx rest - modeIdx p + modeIdx q by abel]

theorem annBase_mem_wordDeg (p : ℕ × Fin 2) {i : (ℤ × ℤ) × ℂ} {x : FockSF}
    (hx : x ∈ wordDeg i) : annBase p x ∈ wordDeg (i - modeIdx p) := by
  rw [wordDeg] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      have hl' : wordIdx l = i := hl
      subst hl'
      exact annBase_stWordSF_mem_wordDeg p l
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem creBase_mem_fockDeg (p : ℕ × Fin 2) {i : (ℤ × ℤ) × ℂ} {x : FockSF}
    (hx : x ∈ fockDeg i) : creBase p x ∈ fockDeg (i + modeIdx p) := by
  rw [fockDeg_eq_wordDeg] at hx ⊢; exact creBase_mem_wordDeg p hx

theorem annBase_mem_fockDeg (p : ℕ × Fin 2) {i : (ℤ × ℤ) × ℂ} {x : FockSF}
    (hx : x ∈ fockDeg i) : annBase p x ∈ fockDeg (i - modeIdx p) := by
  rw [fockDeg_eq_wordDeg] at hx ⊢; exact annBase_mem_wordDeg p hx

/-- The shift of the index by the coefficient `ghField e j` (`z`-exponent `j`). -/
def ghShift (e : Fin 2) (j : ℤ) : (ℤ × ℤ) × ℂ :=
  if 0 ≤ j then modeIdx (j.toNat, e) else -modeIdx ((-j - 1).toNat, e + 1)

theorem ghField_mem_fockDeg (e : Fin 2) (j : ℤ) {i : (ℤ × ℤ) × ℂ} {x : FockSF}
    (hx : x ∈ fockDeg i) : ghField e j x ∈ fockDeg (i + ghShift e j) := by
  unfold ghField ghShift
  split_ifs with hj
  · exact creBase_mem_fockDeg _ hx
  · rw [← sub_eq_add_neg]; exact annBase_mem_fockDeg _ hx

/-! ### Parity -/

theorem fockDeg_le_evenOdd (i : (ℤ × ℤ) × ℂ) :
    fockDeg i ≤ CliffordAlgebra.evenOdd QSF ((i.1.2 : ℤ) : ZMod 2) :=
  (fockDeg_le_ghost i).trans (ghostGrading_le_evenOdd _)

/-- A Koszul operator preserves every piece of a grading refining the parity. -/
theorem koszulOp_mem_of_le_parity {E : Type*} [AddCommGroup E] [Module ℂ E]
    (P : ParityGrading E) (q : ZMod 2) {S : Submodule ℂ E} {r : ZMod 2}
    (hS : S ≤ P.parity r) {x : E} (hx : x ∈ S) : P.koszulOp q x ∈ S := by
  rw [P.koszulOp_homog q (hS hx)]
  exact Submodule.smul_mem _ _ hx

theorem bcKoszul_mem_fockDeg (q : ZMod 2) {i : (ℤ × ℤ) × ℂ} {x : FockSF}
    (hx : x ∈ fockDeg i) : (TensorVA.parGr bcGhostSVA).koszulOp q x ∈ fockDeg i :=
  koszulOp_mem_of_le_parity (TensorVA.parGr bcGhostSVA) q (fockDeg_le_evenOdd i) hx

theorem pairDeg_le_parity (i : (ℤ × ℤ) × ℂ) :
    tensorDeg fockDeg fockDeg i ≤ ghostPairSVA.parity ((i.1.2 : ℤ) : ZMod 2) := by
  refine le_trans ?_ (ghostPairGrading_le_parity i.1.2)
  exact tensorDeg_le ghIndex _ _ ghostGrading ghostGrading ghostPairGrading
    (fun k k' x y hx hy => tmul_mem_tensorGhostGrading _ _ hx hy) fockDeg_le_ghost
    fockDeg_le_ghost i

theorem pairKoszul_mem (q : ZMod 2) {i : (ℤ × ℤ) × ℂ} {x : GhostPairSpace}
    (hx : x ∈ tensorDeg fockDeg fockDeg i) :
    (TensorVA.parGr ghostPairSVA).koszulOp q x ∈ tensorDeg fockDeg fockDeg i :=
  koszulOp_mem_of_le_parity (TensorVA.parGr ghostPairSVA) q (pairDeg_le_parity i) hx

/-! ### Generic: tensor maps shift tensor gradings -/

section TensorShift

universe u v w

variable {ι : Type w} [AddCommGroup ι]
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : Type v} [AddCommGroup W] [Module ℂ W]

theorem tensorDeg_map_shift (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W)
    (T : V →ₗ[ℂ] V) (S : W →ₗ[ℂ] W) (δ₁ δ₂ : ι)
    (hT : ∀ i, ∀ x ∈ dV i, T x ∈ dV (i + δ₁)) (hS : ∀ i, ∀ y ∈ dW i, S y ∈ dW (i + δ₂))
    (a : ι) :
    ∀ z ∈ tensorDeg dV dW a, TensorProduct.map T S z ∈ tensorDeg dV dW (a + (δ₁ + δ₂)) := by
  refine tensorDeg_induction dV dW a
    (fun z => TensorProduct.map T S z ∈ tensorDeg dV dW (a + (δ₁ + δ₂)))
    (by simp) (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
    (fun c x hx => by simpa only [map_smul] using Submodule.smul_mem _ c hx) ?_
  intro b x hx y hy
  rw [TensorProduct.map_tmul]
  have e : b + δ₁ + (a - b + δ₂) = a + (δ₁ + δ₂) := by abel
  simpa only [e] using tmul_mem_tensorDeg dV dW (hT b x hx) (hS _ y hy)

end TensorShift

/-! ### Ghost modes on the three pairs -/

/-- A mode of a ghost generator (pair `a`, species `e`) on the three-pair space. -/
abbrev gMode (a : Fin 3) (e : Fin 2) (m : ℤ) : Module.End ℂ Sl2GhostSpace :=
  mode (sl2GhostSVA.Y (ghostGenerator a e)) m

theorem YGh_single_gen (e : Fin 2) : YGh (stWordSF [((0, e) : ℕ × Fin 2)]) = ghField e := by
  rw [YGh_word, ghostWord_single_field]

theorem single_odd (e : Fin 2) : stWordSF [((0, e) : ℕ × Fin 2)] ∈ bcGhostSVA.parity 1 :=
  stWordSF_mem_evenOdd [((0, e) : ℕ × Fin 2)]

theorem gMode_tmul_zero (e : Fin 2) (m : ℤ) (x y z : FockSF) :
    gMode 0 e m ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) = (ghField e (-m - 1) x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z := by
  change TensorVA.tenY ghostPairSVA bcGhostSVA
    ((stWordSF [((0, e) : ℕ × Fin 2)] ⊗ₜ[ℂ] vacSF) ⊗ₜ[ℂ] bcGhostSVA.vacuum) (-m - 1)
    ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) = _
  rw [tenY_left_unit ghostPairSVA bcGhostSVA]
  change TensorVA.tenY bcGhostSVA bcGhostSVA
    (stWordSF [((0, e) : ℕ × Fin 2)] ⊗ₜ[ℂ] bcGhostSVA.vacuum) (-m - 1) (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z = _
  rw [tenY_left_unit bcGhostSVA bcGhostSVA]
  change YGh (stWordSF [((0, e) : ℕ × Fin 2)]) (-m - 1) x ⊗ₜ[ℂ] y ⊗ₜ[ℂ] z = _
  rw [YGh_single_gen]

theorem gMode_tmul_one (e : Fin 2) (m : ℤ) (x y z : FockSF) :
    gMode 1 e m ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) =
      ((TensorVA.parGr bcGhostSVA).koszulOp 1 x ⊗ₜ[ℂ] ghField e (-m - 1) y) ⊗ₜ[ℂ] z := by
  change TensorVA.tenY ghostPairSVA bcGhostSVA
    ((vacSF ⊗ₜ[ℂ] stWordSF [((0, e) : ℕ × Fin 2)]) ⊗ₜ[ℂ] bcGhostSVA.vacuum) (-m - 1)
    ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) = _
  rw [tenY_left_unit ghostPairSVA bcGhostSVA]
  change TensorVA.tenY bcGhostSVA bcGhostSVA
    (bcGhostSVA.vacuum ⊗ₜ[ℂ] stWordSF [((0, e) : ℕ × Fin 2)]) (-m - 1) (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z = _
  rw [tenY_right_unit_field bcGhostSVA bcGhostSVA (single_odd e), TensorVA.rgtF_tmul]
  change ((TensorVA.parGr bcGhostSVA).koszulOp 1 x ⊗ₜ[ℂ]
    YGh (stWordSF [((0, e) : ℕ × Fin 2)]) (-m - 1) y) ⊗ₜ[ℂ] z = _
  rw [YGh_single_gen]

theorem gMode_tmul_two (e : Fin 2) (m : ℤ) (w : GhostPairSpace) (z : FockSF) :
    gMode 2 e m (w ⊗ₜ[ℂ] z) =
      (TensorVA.parGr ghostPairSVA).koszulOp 1 w ⊗ₜ[ℂ] ghField e (-m - 1) z := by
  change TensorVA.tenY ghostPairSVA bcGhostSVA
    ((vacSF ⊗ₜ[ℂ] vacSF) ⊗ₜ[ℂ] stWordSF [((0, e) : ℕ × Fin 2)]) (-m - 1) (w ⊗ₜ[ℂ] z) = _
  rw [show (vacSF ⊗ₜ[ℂ] vacSF : GhostPairSpace) = ghostPairSVA.vacuum from rfl,
    tenY_right_unit_field ghostPairSVA bcGhostSVA (single_odd e), TensorVA.rgtF_tmul]
  change (TensorVA.parGr ghostPairSVA).koszulOp 1 w ⊗ₜ[ℂ]
    YGh (stWordSF [((0, e) : ℕ × Fin 2)]) (-m - 1) z = _
  rw [YGh_single_gen]

theorem gMode_zero_eq (e : Fin 2) (m : ℤ) : gMode 0 e m = TensorProduct.map
    (TensorProduct.map (ghField e (-m - 1)) LinearMap.id) LinearMap.id := by
  apply TensorProduct.ext'; intro w z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => rw [TensorProduct.add_tmul, map_add, map_add, hw, hw']
  | tmul x y => rw [gMode_tmul_zero]; simp only [TensorProduct.map_tmul, LinearMap.id_apply]

theorem gMode_one_eq (e : Fin 2) (m : ℤ) : gMode 1 e m = TensorProduct.map
    (TensorProduct.map ((TensorVA.parGr bcGhostSVA).koszulOp 1) (ghField e (-m - 1)))
    LinearMap.id := by
  apply TensorProduct.ext'; intro w z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => rw [TensorProduct.add_tmul, map_add, map_add, hw, hw']
  | tmul x y => rw [gMode_tmul_one]; simp only [TensorProduct.map_tmul, LinearMap.id_apply]

theorem gMode_two_eq (e : Fin 2) (m : ℤ) : gMode 2 e m = TensorProduct.map
    ((TensorVA.parGr ghostPairSVA).koszulOp 1) (ghField e (-m - 1)) := by
  apply TensorProduct.ext'; intro w z
  rw [gMode_tmul_two, TensorProduct.map_tmul]

theorem ghostMode_zero_mem (e : Fin 2) (m : ℤ) {i : (ℤ × ℤ) × ℂ}
    {x : Sl2GhostSpace} (hx : x ∈ ghostDeg i) :
    gMode 0 e m x ∈ ghostDeg (i + ghShift e (-m - 1)) := by
  rw [gMode_zero_eq]
  have := tensorDeg_map_shift (tensorDeg fockDeg fockDeg) fockDeg _ LinearMap.id
    (ghShift e (-m - 1) + 0) 0
    (tensorDeg_map_shift fockDeg fockDeg _ LinearMap.id (ghShift e (-m - 1)) 0
      (fun i x hx => ghField_mem_fockDeg e _ hx)
      (fun i y hy => by rw [add_zero]; exact hy))
    (fun i y hy => by rw [add_zero]; exact hy) i x hx
  simpa only [add_zero] using this

theorem ghostMode_one_mem (e : Fin 2) (m : ℤ) {i : (ℤ × ℤ) × ℂ}
    {x : Sl2GhostSpace} (hx : x ∈ ghostDeg i) :
    gMode 1 e m x ∈ ghostDeg (i + ghShift e (-m - 1)) := by
  rw [gMode_one_eq]
  have := tensorDeg_map_shift (tensorDeg fockDeg fockDeg) fockDeg _ LinearMap.id
    (0 + ghShift e (-m - 1)) 0
    (tensorDeg_map_shift fockDeg fockDeg _ _ 0 (ghShift e (-m - 1))
      (fun i x hx => by rw [add_zero]; exact bcKoszul_mem_fockDeg 1 hx)
      (fun i y hy => ghField_mem_fockDeg e _ hy))
    (fun i y hy => by rw [add_zero]; exact hy) i x hx
  simpa only [add_zero, zero_add] using this

theorem ghostMode_two_mem (e : Fin 2) (m : ℤ) {i : (ℤ × ℤ) × ℂ}
    {x : Sl2GhostSpace} (hx : x ∈ ghostDeg i) :
    gMode 2 e m x ∈ ghostDeg (i + ghShift e (-m - 1)) := by
  rw [gMode_two_eq]
  have := tensorDeg_map_shift (tensorDeg fockDeg fockDeg) fockDeg _ _ 0 (ghShift e (-m - 1))
    (fun i x hx => by rw [add_zero]; exact pairKoszul_mem 1 hx)
    (fun i y hy => ghField_mem_fockDeg e _ hy) i x hx
  simpa only [zero_add] using this

/-- **Every ghost mode shifts the three-pair `R`-grading** by `ghShift`. -/
theorem ghostMode_mem_ghostDeg (a : Fin 3) (e : Fin 2) (m : ℤ) {i : (ℤ × ℤ) × ℂ}
    {x : Sl2GhostSpace} (hx : x ∈ ghostDeg i) :
    gMode a e m x ∈ ghostDeg (i + ghShift e (-m - 1)) := by
  fin_cases a
  · exact ghostMode_zero_mem e m hx
  · exact ghostMode_one_mem e m hx
  · exact ghostMode_two_mem e m hx

/-! ### The antighost zero modes -/

theorem ghShift_b_zero : ghShift 0 (-1) = ((0, -1), 0) := by
  simp [ghShift, modeIdx, modeR, ghCharge, ghModeWt, ghWt]

/-- **`AntighostZeroShift` holds.** -/
theorem antighostZeroShift : AntighostZeroShift := by
  intro a i y hy
  have h := ghostMode_mem_ghostDeg a 0 0 hy
  rw [show (-(0 : ℤ) - 1) = -1 by norm_num, ghShift_b_zero] at h
  have e : ghDown i = i + ((0, -1), 0) := by
    obtain ⟨⟨j, g⟩, h⟩ := i
    simp only [ghDown, Prod.mk_add_mk, add_zero]
    rfl
  rw [e]
  exact h

end

end VOA.ConcreteHodge
