/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.GhostConjChain

/-!
# The ghost conjugation `ρ_G` and the ghost bilinear form `B_G`, constructed

On the three-pair ghost Fock space `Sl2GhostSpace = (FockSF ⊗ FockSF) ⊗ FockSF` this file
constructs Beem–Garner's ghost conjugation, normalized so that its square is `1`.

* `colConj a = reverse ∘ map (genMap a) ∘ conj` — on one colour, the **antilinear
  anti-automorphism** of the exterior algebra with
  `b^a_{-n} ↦ -n w_a c^a_{-n}`, `c^a_{-n} ↦ -(n w_a)⁻¹ b^a_{-n}` (`n ≥ 1`), `c^a_0 ↦ c^a_0`,
  `w_e = w_f = 1`, `w_h = 2` (the colour factor of `bgColourWeight`); `conj` is coordinatewise
  conjugation in the monomial basis, which fixes every word (`basisConj_stWordSF`, from Mathlib's
  sign rule for products of basis monomials).
* `ghostConj = Sop ∘ (colConj 0 ⊗ colConj 1 ⊗ colConj 2)`, with `Sop` the cross-colour Koszul
  sign `(-1)^{p₀p₁ + p₀p₂ + p₁p₂}` (built from the parity involutions): the anti-automorphism of
  the whole three-colour ghost algebra. On word tensors it is explicit (`ghostConj_W`).
* `B_G (z, y) = ⟨i^{2R} ρ_G z, y⟩` (`ghostB`), so that `P = i^{2R} B_G(ρ_G ·, ·)` holds by
  construction.

Proved outright:
* `ghostConj_sq` — `ρ_G² = 1` on the whole ghost space;
* `ghostConj_deg` — `ρ_G` maps the `c₀`-free fine piece `k` to the piece `conjF k`;
* `ghostB_P_eq` — `P = i^{2R} B_G(ρ_G ·, ·)` on every fine ghost piece.

The compact conjugation of the ghost current zero modes, and with it the full ghost factor of the
Beem–Garner data, is proved in `GhostConjJ0`.

Numerically (truncated model of the actual complex, relative weights `≤ 4`), with `κ = 1` the
corrected
`ρ_D` and `B_E` (`GhostConjChain`) hold for `ρ_M ⊗ ρ_G`, `B_M ⊗ B_G`; the ghost modes satisfy
`B_G(b^a_k y, y') = i (-1)^{gh y} B_G(y, b^a_{-k} y')` and the same for `c^a_k` (`k ≠ 0`). The
per-colour reversal **without** the cross-colour sign fails `ρ_D`.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### Generic: maps defined on a basis -/

section Generic

variable {ι V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Coordinatewise complex conjugation in a basis. -/
def basisConj (b : Module.Basis ι ℂ V) : V →ₗ⋆[ℂ] V where
  toFun x := b.repr.symm (Finsupp.mapRange (starRingEnd ℂ) (map_zero _) (b.repr x))
  map_add' x y := by
    rw [map_add, Finsupp.mapRange_add (map_add _), map_add]
  map_smul' c x := by
    have h : Finsupp.mapRange (starRingEnd ℂ) (map_zero _) (b.repr (c • x)) =
        (starRingEnd ℂ) c • Finsupp.mapRange (starRingEnd ℂ) (map_zero _) (b.repr x) := by
      ext i; simp
    rw [h, map_smul]

@[simp] theorem basisConj_basis (b : Module.Basis ι ℂ V) (i : ι) : basisConj b (b i) = b i := by
  simp [basisConj]

/-- The antilinear map sending `b i` to `f i`. -/
def basisSemi (b : Module.Basis ι ℂ V) (f : ι → V) : V →ₗ⋆[ℂ] V :=
  (b.constr ℂ f).comp (basisConj b)

@[simp] theorem basisSemi_basis (b : Module.Basis ι ℂ V) (f : ι → V) (i : ι) :
    basisSemi b f (b i) = f i := by
  simp [basisSemi, Module.Basis.constr_basis]

/-- The diagonal linear map `b i ↦ d i • b i`. -/
def basisDiag (b : Module.Basis ι ℂ V) (d : ι → ℂ) : V →ₗ[ℂ] V := b.constr ℂ fun i => d i • b i

@[simp] theorem basisDiag_basis (b : Module.Basis ι ℂ V) (d : ι → ℂ) (i : ι) :
    basisDiag b d (b i) = d i • b i := by
  simp [basisDiag, Module.Basis.constr_basis]

/-- A pure tensor of two span elements lies in every submodule containing the pure tensors of the
spanning vectors. -/
theorem tmul_mem_of_span (S : Submodule ℂ (V ⊗[ℂ] W)) {A : Set V} {B : Set W}
    (h : ∀ x ∈ A, ∀ z ∈ B, x ⊗ₜ[ℂ] z ∈ S) {x : V} (hx : x ∈ Submodule.span ℂ A) {z : W}
    (hz : z ∈ Submodule.span ℂ B) : x ⊗ₜ[ℂ] z ∈ S := by
  have hle : Submodule.map₂ (TensorProduct.mk ℂ V W) (Submodule.span ℂ A)
      (Submodule.span ℂ B) ≤ S := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨x, hx, z, hz, rfl⟩
    exact h x hx z hz
  exact hle (Submodule.apply_mem_map₂ _ hx hz)

/-- A tensor grading of two spanned gradings is spanned by the pure tensors of the spanning
vectors with the right total index. -/
theorem tensorDeg_le_span {ι' κV κW : Type*} [AddCommGroup ι']
    (dV : ι' → Submodule ℂ V) (dW : ι' → Submodule ℂ W) (fV : κV → V) (fW : κW → W)
    (iV : κV → ι') (iW : κW → ι')
    (hV : ∀ a, dV a ≤ Submodule.span ℂ (fV '' {i | iV i = a}))
    (hW : ∀ a, dW a ≤ Submodule.span ℂ (fW '' {j | iW j = a})) (k : ι') :
    tensorDeg dV dW k ≤ Submodule.span ℂ
      ((fun p : κV × κW => fV p.1 ⊗ₜ[ℂ] fW p.2) '' {p | iV p.1 + iW p.2 = k}) := by
  intro z hz
  refine tensorDeg_induction dV dW k _ (Submodule.zero_mem _)
    (fun x y hx hy => Submodule.add_mem _ hx hy) (fun c x hx => Submodule.smul_mem _ c hx)
    ?_ z hz
  intro b x hx y hy
  refine tmul_mem_of_span _ (fun x hx z hz => ?_) (hV b hx) (hW (k - b) hy)
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hz
  refine Submodule.subset_span ⟨(i, j), ?_, rfl⟩
  have hi' : iV i = b := hi
  have hj' : iW j = k - b := hj
  change iV i + iW j = k
  rw [hi', hj']
  abel

end Generic

/-! ### One colour: the swap of modes -/

/-- The `b ↔ c` swap of creation modes: `b_{-n} = (n - 1, 0) ↔ c_{-n} = (n, 1)`, `c_0` fixed. -/
def swapMode (p : ℕ × Fin 2) : ℕ × Fin 2 :=
  if p.2 = 0 then (p.1 + 1, 1) else if p.1 = 0 then (0, 1) else (p.1 - 1, 0)

theorem swapMode_swapMode (p : ℕ × Fin 2) : swapMode (swapMode p) = p := by
  obtain ⟨k, e⟩ := p
  fin_cases e
  · simp [swapMode]
  · rcases k with _ | k
    · simp [swapMode]
    · simp [swapMode]

/-- The colour factor: `2` on `h`, `1` on `e`, `f`. -/
def colourW (a : Fin 3) : ℝ := if a = 2 then 2 else 1

theorem colourW_pos (a : Fin 3) : 0 < colourW a := by
  unfold colourW; split_ifs <;> norm_num

/-- The coefficient of one mode under `ρ_G`: `b_{-n} ↦ -n w c_{-n}`, `c_{-n} ↦ -(n w)⁻¹ b_{-n}`,
`c_0 ↦ c_0`. -/
def modeCoef (a : Fin 3) (p : ℕ × Fin 2) : ℝ :=
  if p.2 = 0 then -(((p.1 : ℝ) + 1) * colourW a)
  else if p.1 = 0 then 1 else -(1 / ((p.1 : ℝ) * colourW a))

theorem modeCoef_swap_mul (a : Fin 3) (p : ℕ × Fin 2) :
    modeCoef a (swapMode p) * modeCoef a p = 1 := by
  have hw := (colourW_pos a).ne'
  obtain ⟨k, e⟩ := p
  fin_cases e
  · simp only [swapMode, modeCoef]
    simp
    field_simp
  · rcases k with _ | k
    · simp [swapMode, modeCoef]
    · simp only [swapMode, modeCoef]
      simp
      field_simp

/-! ### One colour: the index of a monomial -/

theorem wordIdxF_nil' : wordIdxF [] = 0 := by
  simp [wordIdxF, wordIdx, wordR, ghNum, ghWeight]

theorem wordIdxF_eq_sum (l : SFWord) : wordIdxF l = (l.map modeIdxF).sum := by
  induction l with
  | nil => simp [wordIdxF_nil']
  | cons p l ih => rw [wordIdxF_cons, ih, List.map_cons, List.sum_cons]

/-- The fine index of a monomial is the sum of the indices of its modes. -/
theorem fockIndexF_eq_sum (s : Finset ModeIdx) :
    fockIndexF s = ∑ p ∈ s, modeIdxF (ofLex p) := by
  unfold fockIndexF fockWord
  rw [wordIdxF_eq_sum, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rw [← Finset.sum_coe_sort s]
  exact Fintype.sum_equiv (Finset.orderIsoOfFin s rfl).toEquiv _ _
    (fun i => by rw [← Finset.coe_orderIsoOfFin_apply]; rfl)

theorem modeIdxF_snd_nonneg (p : ℕ × Fin 2) : 0 ≤ (modeIdxF p).2 := by
  unfold modeIdxF; split_ifs <;> norm_num

theorem fockIndexF_snd_nonneg (s : Finset ModeIdx) : 0 ≤ (fockIndexF s).2 := by
  rw [fockIndexF_eq_sum, Prod.snd_sum]
  exact Finset.sum_nonneg fun p _ => modeIdxF_snd_nonneg _

/-- A monomial with no `c₀` has no `(0, 1)` mode. -/
theorem not_c0_of_snd_zero {s : Finset ModeIdx} (h : (fockIndexF s).2 = 0) :
    ∀ p ∈ s, ofLex p ≠ (0, 1) := by
  intro p hp hc
  rw [fockIndexF_eq_sum, Prod.snd_sum] at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun q _ => modeIdxF_snd_nonneg (ofLex q)).mp h p hp
  rw [hc] at h0
  simp [modeIdxF] at h0

/-- `conjF` as an additive map. -/
def conjHom : KF →+ KF where
  toFun := conjF
  map_zero' := by simp [conjF, conjIdx]
  map_add' := conjF_add

theorem modeIdxF_swapMode (p : ℕ × Fin 2) (hp : p ≠ (0, 1)) :
    modeIdxF (swapMode p) = conjF (modeIdxF p) := by
  obtain ⟨k, e⟩ := p
  fin_cases e
  · simp [swapMode, modeIdxF, modeIdx, modeR, ghCharge, ghModeWt, ghWt, conjF, conjIdx]
  · rcases k with _ | k
    · exact absurd rfl hp
    · simp [swapMode, modeIdxF, modeIdx, modeR, ghCharge, ghModeWt, ghWt, conjF, conjIdx]

/-! ### Three colours: the monomial basis and the fine pieces -/

/-- The index set of the monomial basis of the three-pair space. -/
abbrev GIdx := (Finset ModeIdx × Finset ModeIdx) × Finset ModeIdx

/-- The monomial basis of `Sl2GhostSpace`. -/
def ghostBasis : Module.Basis GIdx ℂ Sl2GhostSpace :=
  (fockBasis.tensorProduct fockBasis).tensorProduct fockBasis

theorem ghostBasis_apply (i : GIdx) :
    ghostBasis i = (fockBasis i.1.1 ⊗ₜ[ℂ] fockBasis i.1.2) ⊗ₜ[ℂ] fockBasis i.2 := by
  simp [ghostBasis, Module.Basis.tensorProduct_apply']

/-- The fine index of a three-colour monomial. -/
def ghostIdx (i : GIdx) : KF := fockIndexF i.1.1 + fockIndexF i.1.2 + fockIndexF i.2

theorem fockDegF_le_span (k : KF) :
    fockDegF k ≤ Submodule.span ℂ (fockBasis '' {s | fockIndexF s = k}) := by
  rw [fockDegF_eq_basisDeg]; exact le_rfl

/-- **Every fine ghost piece is spanned by basis monomials of that fine index.** -/
theorem ghostDegF_le_span (k : KF) :
    ghostDegF k ≤ Submodule.span ℂ (ghostBasis '' {i | ghostIdx i = k}) := by
  have hpair : ∀ b, pairDegF b ≤ Submodule.span ℂ
      ((fun p : Finset ModeIdx × Finset ModeIdx => fockBasis p.1 ⊗ₜ[ℂ] fockBasis p.2) ''
        {p | fockIndexF p.1 + fockIndexF p.2 = b}) :=
    tensorDeg_le_span fockDegF fockDegF fockBasis fockBasis fockIndexF fockIndexF
      fockDegF_le_span fockDegF_le_span
  have h := tensorDeg_le_span pairDegF fockDegF
    (fun p : Finset ModeIdx × Finset ModeIdx => fockBasis p.1 ⊗ₜ[ℂ] fockBasis p.2) fockBasis
    (fun p => fockIndexF p.1 + fockIndexF p.2) fockIndexF hpair fockDegF_le_span k
  refine h.trans (Submodule.span_mono ?_)
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, hi, by rw [ghostBasis_apply]⟩

/-- Extending a statement from the basis monomials of index `k` to the fine piece `k`. -/
theorem ghostDegF_induction {k : KF} (Φ : Sl2GhostSpace → Prop) (h0 : Φ 0)
    (hadd : ∀ x y, Φ x → Φ y → Φ (x + y)) (hsmul : ∀ (c : ℂ) x, Φ x → Φ (c • x))
    (hb : ∀ i, ghostIdx i = k → Φ (ghostBasis i)) {y : Sl2GhostSpace} (hy : y ∈ ghostDegF k) :
    Φ y := by
  have hy' := ghostDegF_le_span k hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact hb i hi
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

theorem ghostIdx_snd_zero {i : GIdx} (h : (ghostIdx i).2 = 0) :
    (fockIndexF i.1.1).2 = 0 ∧ (fockIndexF i.1.2).2 = 0 ∧ (fockIndexF i.2).2 = 0 := by
  have h0 := fockIndexF_snd_nonneg i.1.1
  have h1 := fockIndexF_snd_nonneg i.1.2
  have h2 := fockIndexF_snd_nonneg i.2
  simp only [ghostIdx, Prod.snd_add] at h
  omega

/-! ### The algebraic conjugation -/

abbrev sfGen (p : ℕ × Fin 2) : SFModes := Finsupp.single p 1

theorem fockBasis_singleton (q : ModeIdx) :
    fockBasis {q} = CliffordAlgebra.ι QSF (sfGen (ofLex q)) := by
  rw [fockBasis, ExteriorAlgebra.basis_apply_ofCard sfBasis (Finset.card_singleton q)]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply]
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply, Finset.orderEmbOfFin_singleton, sfBasis_apply]

theorem stWordSF_eq_int_basis (l : SFWord) :
    ∃ (c : ℤ) (s : Finset ModeIdx), stWordSF l = (c : ℂ) • fockBasis s := by
  induction l with
  | nil => exact ⟨1, ∅, by rw [fockBasis_eq_word, fockWord_empty]; simp⟩
  | cons p l ih =>
      obtain ⟨c, s, hs⟩ := ih
      rw [stWordSF_cons, hs, mul_smul_comm,
        show CliffordAlgebra.ι QSF (Finsupp.single p 1) = fockBasis {toLex p} from
          (fockBasis_singleton _).symm]
      let S1 : Set.powersetCard ModeIdx 1 := ⟨{toLex p}, Finset.card_singleton _⟩
      let S2 : Set.powersetCard ModeIdx s.card := ⟨s, rfl⟩
      by_cases h : Disjoint (S1 : Finset ModeIdx) S2
      · have := ExteriorAlgebra.basis_mul_of_disjoint sfBasis S1 S2 h
        refine ⟨c * ((Set.powersetCard.permOfDisjoint h).sign : ℤ),
          ((Set.powersetCard.disjUnion h : Set.powersetCard ModeIdx _) : Finset ModeIdx), ?_⟩
        change (c : ℂ) • (sfBasis.ExteriorAlgebra S1 * sfBasis.ExteriorAlgebra S2) = _
        rw [this, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        push_cast
        rfl
      · have := ExteriorAlgebra.basis_mul_of_not_disjoint sfBasis S1 S2 h
        refine ⟨0, ∅, ?_⟩
        change (c : ℂ) • (sfBasis.ExteriorAlgebra S1 * sfBasis.ExteriorAlgebra S2) = _
        rw [this]; simp


theorem basisConj_stWordSF (l : SFWord) : basisConj fockBasis (stWordSF l) = stWordSF l := by
  obtain ⟨c, s, hs⟩ := stWordSF_eq_int_basis l
  rw [hs, LinearMap.map_smulₛₗ, basisConj_basis, map_intCast]

theorem stWordSF_eq_prod (l : SFWord) :
    stWordSF l = (l.map fun p => CliffordAlgebra.ι QSF (sfGen p)).prod := by
  induction l with
  | nil => simp
  | cons p l ih => rw [stWordSF_cons, ih, List.map_cons, List.prod_cons]

def genMap (a : Fin 3) : SFModes →ₗ[ℂ] SFModes :=
  Finsupp.lsum ℂ fun p => ((modeCoef a p : ℝ) : ℂ) • Finsupp.lsingle (swapMode p)

theorem genMap_gen (a : Fin 3) (p : ℕ × Fin 2) :
    genMap a (sfGen p) = ((modeCoef a p : ℝ) : ℂ) • sfGen (swapMode p) := by
  simp [genMap, sfGen]

def algMap (a : Fin 3) : FockSF →ₐ[ℂ] FockSF := ExteriorAlgebra.map (genMap a)

theorem algMap_ι (a : Fin 3) (p : ℕ × Fin 2) :
    algMap a (CliffordAlgebra.ι QSF (sfGen p)) =
      ((modeCoef a p : ℝ) : ℂ) • CliffordAlgebra.ι QSF (sfGen (swapMode p)) := by
  rw [algMap, ExteriorAlgebra.map_apply_ι, genMap_gen, map_smul]

def coefProd (a : Fin 3) (l : SFWord) : ℝ := (l.map (modeCoef a)).prod

theorem algMap_stWordSF (a : Fin 3) (l : SFWord) :
    algMap a (stWordSF l) = ((coefProd a l : ℝ) : ℂ) • stWordSF (l.map swapMode) := by
  induction l with
  | nil => simp [coefProd]
  | cons p l ih =>
      rw [stWordSF_cons, map_mul, algMap_ι, ih, List.map_cons, stWordSF_cons, smul_mul_smul_comm]
      simp [coefProd, List.map_cons, List.prod_cons]

theorem reverse_stWordSF (l : SFWord) :
    CliffordAlgebra.reverse (stWordSF l) = stWordSF l.reverse := by
  rw [stWordSF_eq_prod, stWordSF_eq_prod, show (l.map fun p => CliffordAlgebra.ι QSF (sfGen p)) =
    (l.map sfGen).map (CliffordAlgebra.ι QSF) by rw [List.map_map]; rfl,
    CliffordAlgebra.reverse_prod_map_ι, ← List.map_reverse, ← List.map_reverse, List.map_map]
  rfl

/-- The one-colour conjugation: the antilinear anti-automorphism. -/
def colConj (a : Fin 3) : FockSF →ₗ⋆[ℂ] FockSF :=
  (CliffordAlgebra.reverse.comp (algMap a).toLinearMap).comp (basisConj fockBasis)

/-- The swapped reversed word. -/
def swapRev (l : SFWord) : SFWord := (l.map swapMode).reverse

theorem colConj_stWordSF (a : Fin 3) (l : SFWord) :
    colConj a (stWordSF l) = ((coefProd a l : ℝ) : ℂ) • stWordSF (swapRev l) := by
  simp only [colConj, LinearMap.comp_apply, basisConj_stWordSF, AlgHom.toLinearMap_apply,
    algMap_stWordSF, map_smul, reverse_stWordSF, swapRev]

theorem swapRev_swapRev (l : SFWord) : swapRev (swapRev l) = l := by
  simp [swapRev, List.map_reverse, List.map_map, Function.comp_def, swapMode_swapMode]

theorem length_swapRev (l : SFWord) : (swapRev l).length = l.length := by simp [swapRev]

theorem coefProd_swapRev (a : Fin 3) (l : SFWord) : coefProd a (swapRev l) * coefProd a l = 1 := by
  unfold coefProd swapRev
  rw [List.map_reverse, List.prod_reverse, List.map_map]
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, Function.comp_apply]
      have h := modeCoef_swap_mul a p
      calc _ = (modeCoef a (swapMode p) * modeCoef a p) *
          ((l.map (modeCoef a ∘ swapMode)).prod * (l.map (modeCoef a)).prod) := by ring
        _ = 1 := by rw [h, ih, one_mul]

theorem colConj_sq (a : Fin 3) (x : FockSF) : colConj a (colConj a x) = x := by
  have hx : x ∈ Submodule.span ℂ (Set.range fockBasis) := by
    rw [fockBasis.span_eq]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      rw [fockBasis_eq_word, colConj_stWordSF, LinearMap.map_smulₛₗ, colConj_stWordSF,
        swapRev_swapRev, smul_smul, Complex.conj_ofReal, ← Complex.ofReal_mul, mul_comm,
        coefProd_swapRev, Complex.ofReal_one, one_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hx, Complex.conj_conj]

/-! ### Three colours -/

abbrev Kf : Module.End ℂ FockSF := (TensorVA.parGr Ghost.bcGhostSVA).koszulOp 1

theorem Kf_stWordSF (l : SFWord) :
    Kf (stWordSF l) = koszul 1 ((l.length : ℕ) : ZMod 2) • stWordSF l :=
  ParityGrading.koszulOp_homog _ 1 (stWordSF_mem_evenOdd l)

/-- A word tensor. -/
def W3 (l0 l1 l2 : SFWord) : Sl2GhostSpace :=
  (stWordSF l0 ⊗ₜ[ℂ] stWordSF l1) ⊗ₜ[ℂ] stWordSF l2

/-- The parity involution of colour `0`. -/
def pi0 : Module.End ℂ Sl2GhostSpace :=
  TensorProduct.map (TensorProduct.map Kf LinearMap.id) LinearMap.id
/-- The parity involution of colour `1`. -/
def pi1 : Module.End ℂ Sl2GhostSpace :=
  TensorProduct.map (TensorProduct.map LinearMap.id Kf) LinearMap.id
/-- The parity involution of colour `2`. -/
def pi2 : Module.End ℂ Sl2GhostSpace := TensorProduct.map LinearMap.id Kf

/-- `(1 + A + B - AB)/2`, which is `(-1)^{pq}` when `A = (-1)^p`, `B = (-1)^q`. -/
def crossOp (A B : Module.End ℂ Sl2GhostSpace) : Module.End ℂ Sl2GhostSpace :=
  (1 / 2 : ℂ) • (1 + A + B - A * B)

/-- The cross-colour Koszul sign operator. -/
def Sop : Module.End ℂ Sl2GhostSpace := crossOp pi0 pi1 * crossOp pi0 pi2 * crossOp pi1 pi2

theorem crossScalar (p q : ZMod 2) :
    (1 / 2 : ℂ) * (1 + koszul 1 p + koszul 1 q - koszul 1 p * koszul 1 q) = koszul p q := by
  rcases zmod2_cases p with rfl | rfl <;> rcases zmod2_cases q with rfl | rfl <;>
    norm_num [koszul, parSign]

theorem crossOp_W {A B : Module.End ℂ Sl2GhostSpace} {x : Sl2GhostSpace} {p q : ZMod 2}
    (hA : A x = koszul 1 p • x) (hB : B x = koszul 1 q • x) :
    crossOp A B x = koszul p q • x := by
  simp only [crossOp, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    Module.End.one_apply, Module.End.mul_apply, hA, hB, map_smul]
  rw [← crossScalar p q]
  module

/-- The parity of a word tensor's colours. -/
abbrev len2 (l : SFWord) : ZMod 2 := ((l.length : ℕ) : ZMod 2)

theorem pi0_W (l0 l1 l2 : SFWord) : pi0 (W3 l0 l1 l2) = koszul 1 (len2 l0) • W3 l0 l1 l2 := by
  simp [pi0, W3, Kf_stWordSF, TensorProduct.smul_tmul']
theorem pi1_W (l0 l1 l2 : SFWord) : pi1 (W3 l0 l1 l2) = koszul 1 (len2 l1) • W3 l0 l1 l2 := by
  simp [pi1, W3, Kf_stWordSF, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
theorem pi2_W (l0 l1 l2 : SFWord) : pi2 (W3 l0 l1 l2) = koszul 1 (len2 l2) • W3 l0 l1 l2 := by
  simp [pi2, W3, Kf_stWordSF, TensorProduct.tmul_smul]

theorem len2_swapRev (l : SFWord) : len2 (swapRev l) = len2 l := by
  simp only [len2, length_swapRev]

/-- The cross sign of three colour parities. -/
def cross3 (p0 p1 p2 : ZMod 2) : ℂ := koszul p0 p1 * koszul p0 p2 * koszul p1 p2

theorem Sop_W (l0 l1 l2 : SFWord) :
    Sop (W3 l0 l1 l2) = cross3 (len2 l0) (len2 l1) (len2 l2) • W3 l0 l1 l2 := by
  have h12 := crossOp_W (pi1_W l0 l1 l2) (pi2_W l0 l1 l2)
  simp only [Sop, Module.End.mul_apply, h12, map_smul,
    crossOp_W (pi0_W l0 l1 l2) (pi2_W l0 l1 l2), crossOp_W (pi0_W l0 l1 l2) (pi1_W l0 l1 l2),
    smul_smul, cross3]
  congr 1
  ac_rfl

/-- The three-colour tensor of the one-colour conjugations. -/
def T3 : Sl2GhostSpace →ₗ⋆[ℂ] Sl2GhostSpace :=
  TensorProduct.map (TensorProduct.map (colConj 0) (colConj 1)) (colConj 2)

/-- The ghost conjugation (algebraic). -/
def ghostConj : Sl2GhostSpace →ₗ⋆[ℂ] Sl2GhostSpace := Sop.comp T3

/-- The real coefficient of the conjugation on a word tensor. -/
def wcoef (l0 l1 l2 : SFWord) : ℂ :=
  ((coefProd 0 l0 * coefProd 1 l1 * coefProd 2 l2 : ℝ) : ℂ) * cross3 (len2 l0) (len2 l1) (len2 l2)

theorem ghostConj_W (l0 l1 l2 : SFWord) :
    ghostConj (W3 l0 l1 l2) = wcoef l0 l1 l2 • W3 (swapRev l0) (swapRev l1) (swapRev l2) := by
  have key : T3 (W3 l0 l1 l2) = ((coefProd 0 l0 * coefProd 1 l1 * coefProd 2 l2 : ℝ) : ℂ) •
      W3 (swapRev l0) (swapRev l1) (swapRev l2) := by
    simp only [T3, W3, TensorProduct.map_tmul, colConj_stWordSF, TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_smul]
    rw [show ((coefProd 0 l0 * coefProd 1 l1 * coefProd 2 l2 : ℝ) : ℂ) =
      ((coefProd 2 l2 : ℝ) : ℂ) * (((coefProd 1 l1 : ℝ) : ℂ) * ((coefProd 0 l0 : ℝ) : ℂ)) by
        push_cast; ring]
  rw [ghostConj, LinearMap.comp_apply, key, map_smul, Sop_W, smul_smul]
  simp only [wcoef, len2_swapRev]

theorem conj_koszul (p q : ZMod 2) : (starRingEnd ℂ) (koszul p q) = koszul p q := by
  rcases zmod2_cases (p * q) with h | h <;> simp [koszul, parSign, h]

theorem conj_wcoef (l0 l1 l2 : SFWord) : (starRingEnd ℂ) (wcoef l0 l1 l2) = wcoef l0 l1 l2 := by
  simp only [wcoef, cross3, map_mul, Complex.conj_ofReal, conj_koszul]

theorem wcoef_swapRev_mul (l0 l1 l2 : SFWord) :
    wcoef (swapRev l0) (swapRev l1) (swapRev l2) * wcoef l0 l1 l2 = 1 := by
  simp only [wcoef, len2_swapRev, cross3]
  have h0 := coefProd_swapRev 0 l0
  have h1 := coefProd_swapRev 1 l1
  have h2 := coefProd_swapRev 2 l2
  have k01 := koszul_mul_self (len2 l0) (len2 l1)
  have k02 := koszul_mul_self (len2 l0) (len2 l2)
  have k12 := koszul_mul_self (len2 l1) (len2 l2)
  have e : ((coefProd 0 (swapRev l0) * coefProd 1 (swapRev l1) * coefProd 2 (swapRev l2) : ℝ) : ℂ) *
      ((coefProd 0 l0 * coefProd 1 l1 * coefProd 2 l2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    rw [show coefProd 0 (swapRev l0) * coefProd 1 (swapRev l1) * coefProd 2 (swapRev l2) *
      (coefProd 0 l0 * coefProd 1 l1 * coefProd 2 l2) = (coefProd 0 (swapRev l0) * coefProd 0 l0) *
      (coefProd 1 (swapRev l1) * coefProd 1 l1) * (coefProd 2 (swapRev l2) * coefProd 2 l2) by ring,
      h0, h1, h2]
    simp
  linear_combination (koszul (len2 l0) (len2 l1) * koszul (len2 l0) (len2 l2) *
      koszul (len2 l1) (len2 l2)) ^ 2 * e +
    (koszul (len2 l0) (len2 l2) * koszul (len2 l1) (len2 l2)) ^ 2 * k01 +
    (koszul (len2 l1) (len2 l2)) ^ 2 * k02 + k12

theorem ghostBasis_eq_W3 (i : GIdx) :
    ghostBasis i = W3 (fockWord i.1.1) (fockWord i.1.2) (fockWord i.2) := by
  rw [ghostBasis_apply, W3, fockBasis_eq_word, fockBasis_eq_word, fockBasis_eq_word]

/-- `ρ_G² = 1` (algebraic conjugation). -/
theorem ghostConj_sq (x : Sl2GhostSpace) : ghostConj (ghostConj x) = x := by
  have hx : x ∈ Submodule.span ℂ (Set.range ghostBasis) := by
    rw [ghostBasis.span_eq]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [ghostBasis_eq_W3, ghostConj_W, LinearMap.map_smulₛₗ, ghostConj_W, swapRev_swapRev,
        swapRev_swapRev, swapRev_swapRev, smul_smul, conj_wcoef, mul_comm, wcoef_swapRev_mul,
        one_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hx, Complex.conj_conj]

theorem mem_fockWord {p : ℕ × Fin 2} {s : Finset ModeIdx} (hp : p ∈ fockWord s) : toLex p ∈ s := by
  unfold fockWord at hp
  rw [List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  have := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
    (Set.powersetCard.prodEquiv.symm s).2 _).mp ⟨i, rfl⟩
  simpa using this

theorem wordIdxF_swapRev {l : SFWord} (h : ∀ p ∈ l, p ≠ (0, 1)) :
    wordIdxF (swapRev l) = conjF (wordIdxF l) := by
  rw [wordIdxF_eq_sum, wordIdxF_eq_sum, swapRev, List.map_reverse, List.sum_reverse,
    List.map_map]
  change _ = conjHom _
  rw [map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun q hq => ?_
  exact modeIdxF_swapMode q (h q hq)

theorem W3_mem_ghostDegF (l0 l1 l2 : SFWord) :
    W3 l0 l1 l2 ∈ ghostDegF (wordIdxF l0 + wordIdxF l1 + wordIdxF l2) :=
  tmul_mem_tensorDeg pairDegF fockDegF
    (tmul_mem_tensorDeg fockDegF fockDegF (stWordSF_mem_fockDegF l0) (stWordSF_mem_fockDegF l1))
    (stWordSF_mem_fockDegF l2)

theorem fockWord_c0free {s : Finset ModeIdx} (h : (fockIndexF s).2 = 0) :
    ∀ p ∈ fockWord s, p ≠ (0, 1) := fun _ hp => not_c0_of_snd_zero h _ (mem_fockWord hp)

/-- `ρ_G` maps the `c₀`-free fine piece `k` to `conjF k` (algebraic conjugation). -/
theorem ghostConj_deg (k : KF) (hk : k.2 = 0) (y : Sl2GhostSpace) (hy : y ∈ ghostDegF k) :
    ghostConj y ∈ ghostDegF (conjF k) := by
  refine ghostDegF_induction (fun y => ghostConj y ∈ ghostDegF (conjF k))
    (by simp) (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
    (fun c x hx => by simpa only [LinearMap.map_smulₛₗ] using Submodule.smul_mem _ _ hx) ?_ hy
  intro i hi
  obtain ⟨h0, h1, h2⟩ := ghostIdx_snd_zero (hi ▸ hk)
  rw [ghostBasis_eq_W3, ghostConj_W]
  refine Submodule.smul_mem _ _ ?_
  have h := W3_mem_ghostDegF (swapRev (fockWord i.1.1)) (swapRev (fockWord i.1.2))
    (swapRev (fockWord i.2))
  rwa [wordIdxF_swapRev (fockWord_c0free h0), wordIdxF_swapRev (fockWord_c0free h1),
    wordIdxF_swapRev (fockWord_c0free h2), ← conjF_add, ← conjF_add,
    show wordIdxF (fockWord i.1.1) + wordIdxF (fockWord i.1.2) + wordIdxF (fockWord i.2) = k
      from hi] at h

/-! ### The ghost bilinear form -/

/-- The diagonal operator `i^{2R}` on monomials. -/
def ghostIR : Module.End ℂ Sl2GhostSpace :=
  basisDiag ghostBasis fun i => Complex.I ^ (ghostIdx i).1.1.1

theorem ghostIR_eigen {k : KF} {y : Sl2GhostSpace} (hy : y ∈ ghostDegF k) :
    ghostIR y = Complex.I ^ k.1.1.1 • y := by
  refine ghostDegF_induction (fun y => ghostIR y = Complex.I ^ k.1.1.1 • y) (by simp)
    (fun x y hx hy => by simp only at hx hy ⊢; rw [map_add, hx, hy, smul_add])
    (fun c x hx => by simp only at hx ⊢; rw [map_smul, hx, smul_comm]) ?_ hy
  intro i hi
  rw [ghostIR, basisDiag_basis, hi]

/-- **The ghost bilinear form** `B_G(z, y) = ⟨i^{2R} ρ_G z, y⟩`. -/
def ghostB : LinearMap.BilinForm ℂ Sl2GhostSpace :=
  LinearMap.mk₂ ℂ (fun z y => bgPG (ghostIR (ghostConj z)) y)
    (fun z z' y => by beta_reduce; rw [map_add, map_add, SesqForm.add_left])
    (fun c z y => by
      beta_reduce
      rw [LinearMap.map_smulₛₗ, map_smul, SesqForm.smul_left, Complex.conj_conj, smul_eq_mul])
    (fun z y y' => by beta_reduce; rw [SesqForm.add_right])
    (fun c z y => by beta_reduce; rw [SesqForm.smul_right, smul_eq_mul])

theorem ghostB_apply (z y : Sl2GhostSpace) : ghostB z y = bgPG (ghostIR (ghostConj z)) y := rfl

theorem I_zpow_mul_conj (N : ℤ) : Complex.I ^ N * (starRingEnd ℂ) (Complex.I ^ N) = 1 := by
  rw [map_zpow₀, Complex.conj_I, ← mul_zpow, mul_neg, Complex.I_mul_I, neg_neg, one_zpow]

/-- **`P = i^{2R} B_G(ρ_G ·, ·)`** on every fine ghost piece. -/
theorem ghostB_P_eq (k : KF) (y : Sl2GhostSpace) (hy : y ∈ ghostDegF k) (y' : Sl2GhostSpace) :
    bgPG y y' = Complex.I ^ k.1.1.1 * ghostB (ghostConj y) y' := by
  rw [ghostB_apply, ghostConj_sq, ghostIR_eigen hy, SesqForm.smul_left, ← mul_assoc,
    I_zpow_mul_conj, one_mul]

end

end VOA.ConcreteHodge
