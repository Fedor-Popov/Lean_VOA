/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTGoodnessGhostCurrent
import VOA.Examples.BRSTGoodnessShift

/-!
# The fine ghost grading, the `c₀`-number, and goodness of the cubic ghost charge

The ghost `R`-grading gives `c₀` the value `R = 0`. The cubic ghost charge `Q_gh` is then **not**
homogeneous of `R`-degree `±1/2`: its terms containing `c₀` or `b₀` preserve `R`. Beem–Garner's
shortening holds only on relative states. The clean way to see it is to refine the index by the
number of `c₀` modes:

* `fockDegF`, `ghostDegF` — the **fine** grading, indexed by `κF = ((ℤ × ℤ) × ℂ) × ℤ`
  (`((2R, gh), weight)` and the number of `c₀`'s). It is the monomial-basis grading
  (`fockDegF_eq_basisDeg`), hence orthogonal for every ghost form (`ghostDegF_orth`), and
  it refines `ghostDeg` (`ghostDeg_le_coarsen`, `ghostDegF_le_ghostDeg`).
* `ghostYCoeff_shifts` — every coefficient of every ghost generator shifts the fine index by
  `ghShiftF`; `ghostCurrentCoeff_shifts` — every coefficient of the ghost current shifts it by a
  sum `ghShiftF 0 m + ghShiftF 1 (s - m)`.
* `piRp` — the projection `R' = R + (number of c₀)/2`, in which **every** ghost creation mode
  has `R' = 1/2`. `cubicCharge_shifts`: the cubic ghost charge shifts `2R'` by exactly `±1`
  (and the ghost number by `1`, the weight by `0`), on the whole ghost space.
* `Nc0` — the `c₀`-number operator `Σ_a c₀ᵃ b₀ᵃ`; `Nc0_eigen`: it acts on the fine piece `k`
  as the scalar `k.2`.

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open VOA.SympFerm VOA.Ghost Sl2SemiInfinite
open scoped TensorProduct

noncomputable section

/-- The fine index: `((2R, gh), weight)` and the number of `c₀` modes. -/
abbrev KF := ((ℤ × ℤ) × ℂ) × ℤ

/-- The fine index of one creation mode. -/
def modeIdxF (p : ℕ × Fin 2) : KF := (modeIdx p, if p = (0, 1) then 1 else 0)

/-- The fine index of a word. -/
def wordIdxF (l : SFWord) : KF := (wordIdx l, (l.count (0, 1) : ℤ))

@[simp] theorem wordIdxF_cons (p : ℕ × Fin 2) (l : SFWord) :
    wordIdxF (p :: l) = modeIdxF p + wordIdxF l := by
  simp only [wordIdxF, modeIdxF, wordIdx_cons, Prod.mk_add_mk, List.count_cons]
  congr 1
  by_cases h : p = (0, 1)
  · subst h; simp; ring
  · simp [h]

/-- The fine grading of one pair: the span of the words of a given fine index. -/
def fockDegF (k : KF) : Submodule ℂ FockSF := Submodule.span ℂ (stWordSF '' {l | wordIdxF l = k})

theorem stWordSF_mem_fockDegF (l : SFWord) : stWordSF l ∈ fockDegF (wordIdxF l) :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

theorem creBase_mem_fockDegF (p : ℕ × Fin 2) {k : KF} {x : FockSF} (hx : x ∈ fockDegF k) :
    creBase p x ∈ fockDegF (k + modeIdxF p) := by
  rw [fockDegF] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      have hl' : wordIdxF l = k := hl
      subst hl'
      rw [creBase_stWordSF, add_comm, ← wordIdxF_cons]
      exact stWordSF_mem_fockDegF _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem annBase_stWordSF_mem_fockDegF (p : ℕ × Fin 2) (l : SFWord) :
    annBase p (stWordSF l) ∈ fockDegF (wordIdxF l - modeIdxF p) := by
  induction l with
  | nil => rw [annBase_stWordSF_nil]; exact Submodule.zero_mem _
  | cons q rest ih =>
      rw [annBase_stWordSF_cons]
      refine Submodule.sub_mem _ ?_ ?_
      · by_cases h : p = q
        · subst h
          rw [if_pos rfl, one_smul, wordIdxF_cons, add_sub_cancel_left]
          exact stWordSF_mem_fockDegF rest
        · rw [if_neg h, zero_smul]
          exact Submodule.zero_mem _
      · rw [show CliffordAlgebra.ι QSF (Finsupp.single q (1 : ℂ)) * annBase p (stWordSF rest)
            = creBase q (annBase p (stWordSF rest)) from by rw [creBase, LinearMap.mulLeft_apply]]
        have := creBase_mem_fockDegF q ih
        rwa [wordIdxF_cons, show modeIdxF q + wordIdxF rest - modeIdxF p =
          wordIdxF rest - modeIdxF p + modeIdxF q by abel]

theorem annBase_mem_fockDegF (p : ℕ × Fin 2) {k : KF} {x : FockSF} (hx : x ∈ fockDegF k) :
    annBase p x ∈ fockDegF (k - modeIdxF p) := by
  rw [fockDegF] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      have hl' : wordIdxF l = k := hl
      subst hl'
      exact annBase_stWordSF_mem_fockDegF p l
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-! ### Identification with the monomial-basis grading -/

/-- The `c₀`-counting derivation. -/
def NC : Module.End ℂ FockSF := derivOf (diagMap fun p => if p = (0, 1) then 1 else 0)

theorem sum_indicator_eq_count (l : SFWord) :
    (l.map fun p : ℕ × Fin 2 => if p = (0, 1) then (1 : ℂ) else 0).sum =
      ((l.count (0, 1) : ℤ) : ℂ) := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      rw [List.map_cons, List.sum_cons, ih, List.count_cons]
      by_cases h : p = (0, 1)
      · subst h; simp; ring
      · simp [h]

theorem NC_stWordSF (l : SFWord) : NC (stWordSF l) = ((l.count (0, 1) : ℤ) : ℂ) • stWordSF l := by
  rw [NC, derivOf_diag_stWordSF, sum_indicator_eq_count]

/-- The fine index of a basis monomial. -/
def fockIndexF (s : Finset ModeIdx) : KF := wordIdxF (fockWord s)

theorem fockBasis_eigen_NC (s : Finset ModeIdx) :
    NC (fockBasis s) = ((fockIndexF s).2 : ℂ) • fockBasis s := by
  rw [fockBasis_eq_word, NC_stWordSF]; rfl

theorem mem_basisDegF_of_eigen {k : KF} {x : FockSF}
    (h1 : NR x = ((k.1.1.1 : ℤ) : ℂ) • x) (h2 : Ngh x = ((k.1.1.2 : ℤ) : ℂ) • x)
    (h3 : L0Gh x = k.1.2 • x) (h4 : NC x = ((k.2 : ℤ) : ℂ) • x) :
    x ∈ basisDeg fockBasis fockIndexF k := by
  rw [basisDeg, Module.Basis.mem_span_image]
  intro s hs
  have hs' : fockBasis.repr x s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have e1 := basis_eigen_of_mem_support fockBasis NR _ fockBasis_eigen_NR h1 hs'
  have e2 := basis_eigen_of_mem_support fockBasis Ngh _ fockBasis_eigen_Ngh h2 hs'
  have e3 := basis_eigen_of_mem_support fockBasis L0Gh _ fockBasis_eigen_L0 h3 hs'
  have e4 := basis_eigen_of_mem_support fockBasis NC _ fockBasis_eigen_NC h4 hs'
  have e1' : (fockIndex s).1.1 = k.1.1.1 := by exact_mod_cast e1
  have e2' : (fockIndex s).1.2 = k.1.1.2 := by exact_mod_cast e2
  have e4' : (fockIndexF s).2 = k.2 := by exact_mod_cast e4
  exact Prod.ext (Prod.ext (Prod.ext e1' e2') e3) e4'

/-- **The fine word grading is the monomial-basis grading.** -/
theorem fockDegF_eq_basisDeg (k : KF) : fockDegF k = basisDeg fockBasis fockIndexF k := by
  apply le_antisymm
  · rw [fockDegF, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : wordIdxF l = k := hl
    subst hl'
    exact mem_basisDegF_of_eigen (NR_stWordSF l) (Ngh_stWordSF l) (L0Gh_stWordSF l)
      (NC_stWordSF l)
  · refine basisDeg_le fockBasis fockIndexF fockDegF (fun s => ?_) k
    rw [fockBasis_eq_word]
    exact stWordSF_mem_fockDegF _

theorem fockDegF_orth (w : Finset ModeIdx → ℝ) :
    ∀ k k', k ≠ k' → ∀ x ∈ fockDegF k, ∀ y ∈ fockDegF k', fockForm w x y = 0 := by
  intro k k' hkk' x hx y hy
  rw [fockDegF_eq_basisDeg] at hx hy
  exact basisDeg_orth fockBasis w fockIndexF k k' hkk' x hx y hy

theorem fockDegF_span : iSup fockDegF = ⊤ := by
  have h : fockDegF = basisDeg fockBasis fockIndexF := funext fockDegF_eq_basisDeg
  rw [h]; exact basisDeg_span _ _

/-! ### Coarsening to the `R`-grading -/

/-- The projection to the `R`-index. -/
abbrev fstF : KF →+ (ℤ × ℤ) × ℂ := AddMonoidHom.fst _ _

theorem fockDeg_le_coarsen (i : (ℤ × ℤ) × ℂ) :
    fockDeg i ≤ ⨆ (k : KF) (_ : fstF k = i), fockDegF k := by
  rw [fockDeg_eq_wordDeg, wordDeg, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : wordIdx l = i := hl
  exact Submodule.mem_iSup_of_mem (wordIdxF l)
    (Submodule.mem_iSup_of_mem hl' (stWordSF_mem_fockDegF l))

theorem fockDegF_le_fockDeg (k : KF) : fockDegF k ≤ fockDeg (fstF k) := by
  rw [fockDeg_eq_wordDeg, fockDegF, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have hl' : wordIdxF l = k := hl
  subst hl'
  exact stWordSF_mem_wordDeg l

/-! ### Single-pair field coefficients and parity -/

/-- The fine shift of the coefficient `ghField e j`. -/
def ghShiftF (e : Fin 2) (j : ℤ) : KF :=
  if 0 ≤ j then modeIdxF (j.toNat, e) else -modeIdxF ((-j - 1).toNat, e + 1)

theorem ghField_mem_fockDegF (e : Fin 2) (j : ℤ) {k : KF} {x : FockSF}
    (hx : x ∈ fockDegF k) : ghField e j x ∈ fockDegF (k + ghShiftF e j) := by
  unfold ghField ghShiftF
  split_ifs with hj
  · exact creBase_mem_fockDegF _ hx
  · rw [← sub_eq_add_neg]; exact annBase_mem_fockDegF _ hx

theorem fockDegF_le_evenOdd (k : KF) :
    fockDegF k ≤ CliffordAlgebra.evenOdd QSF ((k.1.1.2 : ℤ) : ZMod 2) :=
  (fockDegF_le_fockDeg k).trans (fockDeg_le_evenOdd _)

theorem bcKoszul_mem_fockDegF (q : ZMod 2) {k : KF} {x : FockSF} (hx : x ∈ fockDegF k) :
    (TensorVA.parGr bcGhostSVA).koszulOp q x ∈ fockDegF k :=
  koszulOp_mem_of_le_parity (TensorVA.parGr bcGhostSVA) q (fockDegF_le_evenOdd k) hx

/-- The pair-level fine grading. -/
abbrev pairDegF : KF → Submodule ℂ GhostPairSpace := tensorDeg fockDegF fockDegF

theorem pairDegF_le_pairDeg (k : KF) : pairDegF k ≤ tensorDeg fockDeg fockDeg (fstF k) :=
  tensorDeg_le fstF _ _ fockDeg fockDeg _ (fun _ _ _ _ hx hy => tmul_mem_tensorDeg _ _ hx hy)
    fockDegF_le_fockDeg fockDegF_le_fockDeg k

theorem pairKoszul_memF (q : ZMod 2) {k : KF} {x : GhostPairSpace} (hx : x ∈ pairDegF k) :
    (TensorVA.parGr ghostPairSVA).koszulOp q x ∈ pairDegF k :=
  koszulOp_mem_of_le_parity (TensorVA.parGr ghostPairSVA) q
    ((pairDegF_le_pairDeg k).trans (pairDeg_le_parity _)) hx

/-! ### Three pairs -/

/-- **The fine ghost grading** on the three pairs. -/
def ghostDegF : KF → Submodule ℂ Sl2GhostSpace := tensorDeg pairDegF fockDegF

theorem ghostDegF_le_ghostDeg (k : KF) : ghostDegF k ≤ ghostDeg (fstF k) :=
  tensorDeg_le fstF _ _ _ fockDeg _ (fun _ _ _ _ hx hy => tmul_mem_tensorDeg _ _ hx hy)
    pairDegF_le_pairDeg fockDegF_le_fockDeg k

theorem ghostDeg_le_coarsen (i : (ℤ × ℤ) × ℂ) :
    ghostDeg i ≤ ⨆ (k : KF) (_ : fstF k = i), ghostDegF k :=
  tensorDeg_le_coarsen fstF _ _ _ _
    (tensorDeg_le_coarsen fstF _ _ _ _ fockDeg_le_coarsen fockDeg_le_coarsen)
    fockDeg_le_coarsen i

theorem ghostDegF_orth (w : Finset ModeIdx → ℝ) :
    ∀ k k', k ≠ k' → ∀ x ∈ ghostDegF k, ∀ y ∈ ghostDegF k', ghostForm w x y = 0 :=
  tensorDeg_orth _ _ _ _ (tensorDeg_orth _ _ _ _ (fockDegF_orth w) (fockDegF_orth w))
    (fockDegF_orth w)

theorem ghostDegF_span : iSup ghostDegF = ⊤ :=
  tensorDeg_span _ _ (tensorDeg_span _ _ fockDegF_span fockDegF_span) fockDegF_span

theorem ghostModeF_zero_mem (e : Fin 2) (m : ℤ) {k : KF} {x : Sl2GhostSpace}
    (hx : x ∈ ghostDegF k) : gMode 0 e m x ∈ ghostDegF (k + ghShiftF e (-m - 1)) := by
  rw [gMode_zero_eq]
  have := tensorDeg_map_shift pairDegF fockDegF _ LinearMap.id
    (ghShiftF e (-m - 1) + 0) 0
    (tensorDeg_map_shift fockDegF fockDegF _ LinearMap.id (ghShiftF e (-m - 1)) 0
      (fun i x hx => ghField_mem_fockDegF e _ hx)
      (fun i y hy => by rw [add_zero]; exact hy))
    (fun i y hy => by rw [add_zero]; exact hy) k x hx
  simpa only [add_zero] using this

theorem ghostModeF_one_mem (e : Fin 2) (m : ℤ) {k : KF} {x : Sl2GhostSpace}
    (hx : x ∈ ghostDegF k) : gMode 1 e m x ∈ ghostDegF (k + ghShiftF e (-m - 1)) := by
  rw [gMode_one_eq]
  have := tensorDeg_map_shift pairDegF fockDegF _ LinearMap.id
    (0 + ghShiftF e (-m - 1)) 0
    (tensorDeg_map_shift fockDegF fockDegF _ _ 0 (ghShiftF e (-m - 1))
      (fun i x hx => by rw [add_zero]; exact bcKoszul_mem_fockDegF 1 hx)
      (fun i y hy => ghField_mem_fockDegF e _ hy))
    (fun i y hy => by rw [add_zero]; exact hy) k x hx
  simpa only [add_zero, zero_add] using this

theorem ghostModeF_two_mem (e : Fin 2) (m : ℤ) {k : KF} {x : Sl2GhostSpace}
    (hx : x ∈ ghostDegF k) : gMode 2 e m x ∈ ghostDegF (k + ghShiftF e (-m - 1)) := by
  rw [gMode_two_eq]
  have := tensorDeg_map_shift pairDegF fockDegF _ _ 0 (ghShiftF e (-m - 1))
    (fun i x hx => by rw [add_zero]; exact pairKoszul_memF 1 hx)
    (fun i y hy => ghField_mem_fockDegF e _ hy) k x hx
  simpa only [zero_add] using this

theorem ghostModeF_mem (a : Fin 3) (e : Fin 2) (m : ℤ) {k : KF} {x : Sl2GhostSpace}
    (hx : x ∈ ghostDegF k) : gMode a e m x ∈ ghostDegF (k + ghShiftF e (-m - 1)) := by
  fin_cases a
  · exact ghostModeF_zero_mem e m hx
  · exact ghostModeF_one_mem e m hx
  · exact ghostModeF_two_mem e m hx

/-- Every coefficient of a ghost generator field shifts the fine grading exactly. -/
theorem ghostYCoeff_shifts (a : Fin 3) (e : Fin 2) (j : ℤ) :
    ShiftsInto ghostDegF (sl2GhostSVA.Y (ghostGenerator a e) j) (· = ghShiftF e j) := by
  refine ShiftsInto.of_exact fun k x hx => ?_
  have h := ghostModeF_mem a e (-j - 1) hx
  have e1 : -(-j - 1) - 1 = j := by ring
  rw [e1] at h
  simpa only [gMode, mode_apply, e1] using h

/-! ### The ghost current and the cubic charge -/

/-- The shifts of the `s`-th coefficient of a ghost bilinear. -/
def bilinPred (s : ℤ) (δ : KF) : Prop := ∃ m : ℤ, δ = ghShiftF 0 m + ghShiftF 1 (s - m)

theorem bilinear_coeff_shifts (c b : Fin 3) (s : ℤ) :
    ShiftsInto ghostDegF (sl2GhostSVA.Y (ghostBilinear c b) s) (bilinPred s) := by
  intro k x hx
  have hY : sl2GhostSVA.Y (ghostBilinear c b) s x =
      mode (sl2GhostSVA.Y (ghostBilinear c b)) (-s - 1) x := by
    rw [mode_apply, show -(-s - 1) - 1 = s by ring]
  rw [hY, ghostBilinear, TranslationCovariant.normal_product_mode
    translationCovariant_sl2GhostSVA (bGhost_odd c) (cGhost_odd b) (-s - 1) x]
  refine finsum_induction (fun y => y ∈ shiftTarget ghostDegF (bilinPred s) k)
    (Submodule.zero_mem _) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun m => ?_)
  simp only [normalOrderedε_apply, show -(-s - 1) - 1 - m = s - m by ring]
  have hb := ghostYCoeff_shifts c 0 m
  have hc := ghostYCoeff_shifts b 1 (s - m)
  simp only [ghostGenerator_zero, ghostGenerator_one] at hb hc
  split_ifs
  · rw [Module.End.mul_apply]
    have h := (hc.comp hb) k x hx
    refine shiftTarget_mono ?_ k h
    rintro δ ⟨a₁, a₂, h1, h2, rfl⟩
    exact ⟨m, by rw [h1, h2, add_comm]⟩
  · rw [LinearMap.smul_apply, Module.End.mul_apply]
    refine Submodule.smul_mem _ _ ?_
    have h := (hb.comp hc) k x hx
    refine shiftTarget_mono ?_ k h
    rintro δ ⟨a₁, a₂, h1, h2, rfl⟩
    exact ⟨m, by rw [h1, h2]⟩

/-- **Every coefficient of the ghost current** shifts by `ghShiftF 0 m + ghShiftF 1 (s - m)`. -/
theorem ghostCurrentCoeff_shifts (a : Fin 3) (s : ℤ) :
    ShiftsInto ghostDegF (sl2GhostSVA.Y (ghostCurrent a) s) (bilinPred s) := by
  have h : sl2GhostSVA.Y (ghostCurrent a) s = ghostYCoeff s (ghostCurrent a) := rfl
  rw [h, ghostCurrent, map_sum]
  refine ShiftsInto.sum _ fun b _ => ?_
  rw [map_sum]
  refine ShiftsInto.sum _ fun c _ => ?_
  rw [map_smul]
  exact (bilinear_coeff_shifts c b s).smul _

/-- The projection `((2R, gh), weight, n_{c₀}) ↦ ((2R + n_{c₀}, gh), weight)`: in `R'`, every
ghost creation mode, `c₀` included, has `R' = 1/2`. -/
def piRp : KF →+ (ℤ × ℤ) × ℂ where
  toFun k := ((k.1.1.1 + k.2, k.1.1.2), k.1.2)
  map_zero' := rfl
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
    congr 2
    ring

@[simp] theorem piRp_apply (k : KF) : piRp k = ((k.1.1.1 + k.2, k.1.1.2), k.1.2) := rfl

theorem piRp_modeIdxF (p : ℕ × Fin 2) :
    piRp (modeIdxF p) = ((1, ghCharge p.2), ((ghModeWt p : ℕ) : ℂ)) := by
  simp only [piRp_apply, modeIdxF, modeIdx, modeR]
  by_cases h : p = (0, 1)
  · simp [h]
  · simp [h]

theorem piRp_ghShiftF (e : Fin 2) (j : ℤ) :
    piRp (ghShiftF e j) = ((if 0 ≤ j then 1 else -1, ghCharge e), (j : ℂ) + (ghWt e : ℂ)) := by
  unfold ghShiftF
  split_ifs with hj
  · rw [piRp_modeIdxF]
    simp only [ghModeWt]
    push_cast
    rw [show ((j.toNat : ℕ) : ℂ) = (j : ℂ) by exact_mod_cast Int.toNat_of_nonneg hj]
  · rw [map_neg, piRp_modeIdxF]
    simp only [ghModeWt, Prod.neg_mk]
    have hj' : (((-j - 1).toNat : ℕ) : ℂ) = ((-j - 1 : ℤ) : ℂ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega)
    push_cast
    rw [hj']
    fin_cases e
    · simp [ghCharge, ghWt, show (0 : Fin 2) + 1 = 1 from rfl] <;> ring
    · simp [ghCharge, ghWt, show (1 : Fin 2) + 1 = 0 from rfl] <;> ring

/-- The good shifts: `2R'` by `±1`, ghost number by `+1`, weight by `0`. -/
def GoodRp (δ : KF) : Prop := piRp δ = ((1, 1), 0) ∨ piRp δ = ((-1, 1), 0)

theorem goodRp_triple (m m' : ℤ) :
    GoodRp (ghShiftF 1 m + (ghShiftF 0 m' + ghShiftF 1 (-1 - m - m'))) := by
  unfold GoodRp
  have key : piRp (ghShiftF 1 m + (ghShiftF 0 m' + ghShiftF 1 (-1 - m - m'))) =
      (((if 0 ≤ m then 1 else -1) + ((if 0 ≤ m' then 1 else -1) +
        (if 0 ≤ -1 - m - m' then 1 else -1)), 1), 0) := by
    rw [map_add, map_add, piRp_ghShiftF, piRp_ghShiftF, piRp_ghShiftF]
    simp only [Prod.mk_add_mk]
    refine Prod.ext (Prod.ext rfl ?_) ?_
    · simp [ghCharge]
    · simp [ghWt]; push_cast; ring
  rw [key]
  split_ifs <;> first | omega | (left; norm_num; done) | (right; norm_num; done)

/-- The shifts of the cubic summand `c_m J_{-1-m}`. -/
theorem cubic_term_good (m : ℤ) :
    ∀ δ, addPred (· = ghShiftF 1 m) (bilinPred (-1 - m)) δ → GoodRp δ := by
  rintro δ ⟨a₁, a₂, rfl, ⟨m', rfl⟩, rfl⟩
  have h := goodRp_triple m m'
  rwa [show -1 - m - m' = -1 - m - m' by ring] at h

/-- **The cubic ghost charge is `R'`-good on the whole ghost space.** -/
theorem cubicCharge_shifts :
    ShiftsInto ghostDegF (mode (sl2GhostSVA.Y ghostBRSTState) 0) GoodRp := by
  have h : mode (sl2GhostSVA.Y ghostBRSTState) 0 = ghostYCoeff (-1) ghostBRSTState := rfl
  rw [h, ghostBRSTState, map_smul, map_sum]
  refine ShiftsInto.smul (ShiftsInto.sum _ fun a _ => ?_) _
  intro k x hx
  change mode (sl2GhostSVA.Y (mode (sl2GhostSVA.Y (cGhost a)) (-1) (ghostCurrent a))) 0 x ∈ _
  rw [TranslationCovariant.normal_product_mode translationCovariant_sl2GhostSVA
    (cGhost_odd a) (ghostCurrent_even a) 0 x]
  refine finsum_induction (fun y => y ∈ shiftTarget ghostDegF GoodRp k)
    (Submodule.zero_mem _) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun m => ?_)
  simp only [normalOrderedε_apply, show -(0 : ℤ) - 1 - m = -1 - m by ring]
  have hc := ghostYCoeff_shifts a 1 m
  have hJ := ghostCurrentCoeff_shifts a (-1 - m)
  simp only [ghostGenerator_one] at hc
  split_ifs
  · rw [Module.End.mul_apply]
    have h := (hJ.comp hc) k x hx
    refine shiftTarget_mono ?_ k h
    rintro δ ⟨a₁, a₂, h1, h2, rfl⟩
    exact cubic_term_good m _ ⟨a₂, a₁, h2, h1, add_comm _ _⟩
  · rw [LinearMap.smul_apply, Module.End.mul_apply]
    refine Submodule.smul_mem _ _ ?_
    have h := (hc.comp hJ) k x hx
    exact shiftTarget_mono (cubic_term_good m) k h

/-! ### The `c₀`-number operator -/

/-- `c₀ b₀` on one pair. -/
def nc0 : Module.End ℂ FockSF := creBase (0, 1) ∘ₗ annBase (0, 1)

theorem nc0_stWordSF (l : SFWord) :
    nc0 (stWordSF l) = ((l.count (0, 1) : ℤ) : ℂ) • stWordSF l := by
  induction l with
  | nil =>
      simp only [nc0, LinearMap.coe_comp, Function.comp_apply]
      rw [annBase_stWordSF_nil, map_zero]
      simp
  | cons q rest ih =>
      simp only [nc0, LinearMap.coe_comp, Function.comp_apply] at ih ⊢
      rw [annBase_stWordSF_cons, map_sub, map_smul]
      have hswap : creBase (0, 1) (CliffordAlgebra.ι QSF (Finsupp.single q (1 : ℂ)) *
          annBase (0, 1) (stWordSF rest)) =
          -(CliffordAlgebra.ι QSF (Finsupp.single q (1 : ℂ)) *
            creBase (0, 1) (annBase (0, 1) (stWordSF rest))) := by
        simp only [creBase, LinearMap.mulLeft_apply, ← mul_assoc]
        rw [ι_mul_ι_eq_neg, neg_mul]
      rw [hswap, ih, mul_smul_comm, ← stWordSF_cons, creBase_stWordSF, sub_neg_eq_add,
        List.count_cons]
      by_cases h : q = (0, 1)
      · subst h
        rw [if_pos rfl, one_smul]
        simp only [beq_self_eq_true, if_true]
        push_cast
        rw [add_smul, one_smul, add_comm]
      · rw [if_neg (fun h' => h h'.symm), zero_smul, zero_add]
        simp [h]

theorem nc0_eigen {k : KF} {x : FockSF} (hx : x ∈ fockDegF k) :
    nc0 x = ((k.2 : ℤ) : ℂ) • x := by
  rw [fockDegF] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      have hl' : wordIdxF l = k := hl
      subst hl'
      exact nc0_stWordSF l
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

/-- The `c₀`-number operator on the three pairs. -/
def Nc0 : Module.End ℂ Sl2GhostSpace := ∑ a : Fin 3, gMode a 1 (-1) ∘ₗ gMode a 0 0

theorem koszul_twice {E : Type*} [AddCommGroup E] [Module ℂ E] (P : ParityGrading E)
    {r : ZMod 2} {x : E} (hx : x ∈ P.parity r) : P.koszulOp 1 (P.koszulOp 1 x) = x := by
  rw [P.koszulOp_homog 1 hx, map_smul, P.koszulOp_homog 1 hx, smul_smul, koszul_mul_self,
    one_smul]

theorem ghField_c_zero : ghField 1 (-(-1 : ℤ) - 1) = creBase (0, 1) := by
  rw [show -(-1 : ℤ) - 1 = 0 by norm_num, ghField, if_pos le_rfl]; rfl

theorem ghField_b_zero : ghField 0 (-(0 : ℤ) - 1) = annBase (0, 1) := by
  rw [show -(0 : ℤ) - 1 = -1 by norm_num, ghField, if_neg (by norm_num)]; rfl

theorem Nc0_tmul {kx ky kz : KF} {x y z : FockSF} (hx : x ∈ fockDegF kx) (hy : y ∈ fockDegF ky)
    (hz : z ∈ fockDegF kz) :
    Nc0 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) = (((kx + ky + kz).2 : ℤ) : ℂ) • ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) := by
  have hxp := fockDegF_le_evenOdd kx hx
  have hyp := fockDegF_le_evenOdd ky hy
  have hxyp : x ⊗ₜ[ℂ] y ∈ ghostPairSVA.parity _ :=
    pairDeg_le_parity (kx.1 + ky.1) (tmul_mem_tensorDeg fockDeg fockDeg
      (fockDegF_le_fockDeg kx hx) (fockDegF_le_fockDeg ky hy))
  simp only [Nc0, Fin.sum_univ_three, LinearMap.add_apply, LinearMap.coe_comp,
    Function.comp_apply]
  rw [gMode_tmul_zero, gMode_tmul_zero, gMode_tmul_one, gMode_tmul_one, gMode_tmul_two,
    gMode_tmul_two, TensorVA.koszulOp_one, TensorVA.koszulOp_one, ghField_c_zero, ghField_b_zero]
  rw [← TensorVA.koszulOp_one, ← TensorVA.koszulOp_one,
    koszul_twice (TensorVA.parGr bcGhostSVA) hxp,
    koszul_twice (TensorVA.parGr ghostPairSVA) hxyp]
  have h1 := nc0_eigen hx
  have h2 := nc0_eigen hy
  have h3 := nc0_eigen hz
  simp only [nc0, LinearMap.coe_comp, Function.comp_apply] at h1 h2 h3
  rw [h1, h2, h3]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← add_smul]
  congr 1
  simp only [Prod.snd_add]
  push_cast
  ring

/-- **`Nc0` acts on the fine piece `k` as the scalar `k.2`.** -/
theorem Nc0_eigen {k : KF} {x : Sl2GhostSpace} (hx : x ∈ ghostDegF k) :
    Nc0 x = ((k.2 : ℤ) : ℂ) • x := by
  refine tensorDeg_induction pairDegF fockDegF k (fun x => Nc0 x = ((k.2 : ℤ) : ℂ) • x)
    (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, smul_add])
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul, hx, smul_comm]) ?_ x hx
  intro b w hw z hz
  refine tensorDeg_induction fockDegF fockDegF b
    (fun w => Nc0 (w ⊗ₜ[ℂ] z) = ((k.2 : ℤ) : ℂ) • (w ⊗ₜ[ℂ] z))
    (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [TensorProduct.add_tmul, map_add, hx, hy, smul_add])
    (fun c x hx => by
      beta_reduce at hx ⊢; rw [← TensorProduct.smul_tmul', map_smul, hx, smul_comm]) ?_ w hw
  intro c x hx y hy
  rw [Nc0_tmul hx hy hz]
  congr 3
  abel

end

end VOA.ConcreteHodge
