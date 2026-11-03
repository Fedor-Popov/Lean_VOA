/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualSymA

/-!
# From the `R = r` layer of `A` to `gr_r A`

* `grMapA hA r : A → gr_r A` — project onto the layers of `R = r` (all weights) and take the
  class modulo `F_{r-1}`; injective on those layers (`grMapA_injOn`);
* `grMapA_aPos` — it intertwines the degree-preserving positive modes with the induced action
  `grRho`;
* `PiR hA r = grMapA ⊗ 1 : A ⊗ B → gr_r A ⊗ B` — injective on `tensorDeg aDeg bDeg ((2r,0), w)`
  (`PiR_injOn`), intertwining `aPos ⊗ 1` with `grRho ⊗ 1` and `1 ⊗ J^c_n` with itself, and landing
  in `tensorWeight (grDeg r) bWeight n` on `tensorDeg aDeg bDeg ((2r,0), n)`;
* `ev_mem` — the symbol evaluation maps `matterDeg i` into `tensorDeg aDeg bDeg i`.

Everything is proved outright from `hA`.
-/

set_option linter.deprecated false

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.LeeYangTransferAssembly VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval
open MvPolynomial AffineVOA
open scoped TensorProduct

noncomputable section

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

theorem aDeg_le_aFil (r : ℕ) {i : (ℤ × ℤ) × ℂ} (hi : i.1 = (2 * (r : ℤ), 0)) :
    aDeg i ≤ aFil r := by
  refine iSup_le fun m => iSup_le fun p => iSup_le fun h => ?_
  subst h
  have hp : p = r := by
    have := congrArg Prod.fst hi
    simp only [layerIndex] at this
    omega
  subst hp
  rintro _ ⟨x, hx, rfl⟩
  exact Submodule.mem_iSup_of_mem m (GradedFlag.layer_le_pieceIn affineFlag m _ p hx)

/-- The `R = r` part of an index-wise map into `gr_r A`. -/
def grPiece (r : ℕ) (i : (ℤ × ℤ) × ℂ) : aDeg i →ₗ[ℂ] GrA r :=
  if h : i.1 = (2 * (r : ℤ), 0) then
    (grKer r).mkQ ∘ₗ Submodule.inclusion (aDeg_le_aFil r h)
  else 0

/-- `A → gr_r A`: the class of the `R = r` component. -/
def grMapA (r : ℕ) : ASpace →ₗ[ℂ] GrA r :=
  DirectSum.toModule ℂ _ _ (grPiece r) ∘ₗ (internalEquiv (aDeg_isInternal hA)).symm.toLinearMap

theorem grMapA_of_mem (r : ℕ) {i : (ℤ × ℤ) × ℂ} (hi : i.1 = (2 * (r : ℤ), 0)) {x : ASpace}
    (hx : x ∈ aDeg i) :
    grMapA hA r x = (grKer r).mkQ ⟨x, aDeg_le_aFil r hi hx⟩ := by
  simp only [grMapA, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [internalEquiv_symm_of_mem _ hx, ← DirectSum.lof_eq_of ℂ, DirectSum.toModule_lof, grPiece,
    dif_pos hi]
  rfl

theorem grMapA_of_mem_ne (r : ℕ) {i : (ℤ × ℤ) × ℂ} (hi : i.1 ≠ (2 * (r : ℤ), 0)) {x : ASpace}
    (hx : x ∈ aDeg i) : grMapA hA r x = 0 := by
  simp only [grMapA, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [internalEquiv_symm_of_mem _ hx, ← DirectSum.lof_eq_of ℂ, DirectSum.toModule_lof, grPiece,
    dif_neg hi]
  rfl

/-- The layers of `R = r` (all weights). -/
def SR (r : ℕ) : Submodule ℂ ASpace :=
  ⨆ (i : (ℤ × ℤ) × ℂ) (_ : i.1 = (2 * (r : ℤ), 0)), aDeg i

theorem SR_le_aFil (r : ℕ) : SR r ≤ aFil r :=
  iSup_le fun _ => iSup_le fun hi => aDeg_le_aFil r hi

theorem grMapA_of_SR (r : ℕ) {x : ASpace} (hx : x ∈ SR r) :
    grMapA hA r x = (grKer r).mkQ ⟨x, SR_le_aFil r hx⟩ := by
  induction hx using Submodule.iSup_induction' with
  | mem i y hy =>
      by_cases hi : i.1 = (2 * (r : ℤ), 0)
      · rw [iSup_pos hi] at hy
        exact grMapA_of_mem hA r hi hy
      · rw [iSup_neg hi, Submodule.mem_bot] at hy
        subst hy
        rw [map_zero]
        exact (map_zero _).symm
  | zero => rw [map_zero]; exact (map_zero _).symm
  | add x y hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← map_add]
      rfl

/-- **`grMapA` is injective on the layers of `R = r`.** -/
theorem grMapA_injOn (r : ℕ) {x : ASpace} (hx : x ∈ SR r) (h0 : grMapA hA r x = 0) : x = 0 := by
  rw [grMapA_of_SR hA r hx, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  have hlt : x ∈ aFilLT r := h0
  refine eq_of_iproj_eq (aDeg_isInternal hA) fun j => ?_
  rw [map_zero]
  by_cases hj : j.1 = (2 * (r : ℤ), 0)
  · -- `x` lies in the layers below `r`
    rcases r with _ | r
    · rw [aFilLT, Submodule.mem_bot] at hlt; rw [hlt, map_zero]
    · rw [aFilLT] at hlt
      refine iproj_eq_zero_of_mem_iSup (aDeg_isInternal hA)
        (fun j : (ℤ × ℤ) × ℂ => ∃ s m, s ≤ r ∧ layerIndex s m = j) ?_ ?_
      · refine Submodule.iSup_induction _ (motive := fun x => x ∈ ⨆ (j : (ℤ × ℤ) × ℂ)
          (_ : ∃ s m, s ≤ r ∧ layerIndex s m = j), aDeg j) hlt ?_ (Submodule.zero_mem _)
          (fun _ _ => Submodule.add_mem _)
        intro m y hy
        have h := piece_le_iSup_layerDeg affineForm affineRealStructure affineFlag hA
          affineGramRefl r m hy
        have hle : (⨆ (s : ℕ) (_ : s ≤ r), aDeg (layerIndex s m)) ≤
            ⨆ (j : (ℤ × ℤ) × ℂ) (_ : ∃ s m, s ≤ r ∧ layerIndex s m = j), aDeg j :=
          iSup_le fun s => iSup_le fun hs =>
            le_iSup_of_le (layerIndex s m) (le_iSup_of_le ⟨s, m, hs, rfl⟩ le_rfl)
        exact hle h
      · rintro ⟨s, m, hs, rfl⟩
        have := congrArg Prod.fst hj
        simp only [layerIndex] at this
        omega
  · exact iproj_eq_zero_of_mem_iSup (aDeg_isInternal hA) _ hx hj

/-- Generic: a vector of a sup of shifted summands minus one component lies in the others. -/
theorem sub_iproj_mem_ne {ι : Type*} [AddCommGroup ι] [DecidableEq ι] {E : Type*}
    [AddCommGroup E] [Module ℂ E] {L : ι → Submodule ℂ E} (hI : DirectSum.IsInternal L)
    {P : ι → Prop} {i e : ι} {y : E} (hy : y ∈ ⨆ (δ : ι) (_ : P δ), L (i + δ)) :
    y - iproj hI (i + e) y ∈ ⨆ (j : ι) (_ : ∃ δ, P δ ∧ δ ≠ e ∧ j = i + δ), L j := by
  refine mem_iSup_of_iproj hI _ fun j hj => ?_
  rw [map_sub]
  by_cases hje : j = i + e
  · subst hje; rw [iproj_of_mem_same hI (iproj_mem hI _ _), sub_self]
  · rw [iproj_of_mem_ne hI (Ne.symm hje) (iproj_mem hI _ _), sub_zero]
    refine iproj_eq_zero_of_mem_iSup hI (fun j => ∃ δ, P δ ∧ j = i + δ) ?_ ?_
    · have hle : (⨆ (δ : ι) (_ : P δ), L (i + δ)) ≤
          ⨆ (j : ι) (_ : ∃ δ, P δ ∧ j = i + δ), L j :=
        iSup_le fun δ => iSup_le fun hδ => le_iSup_of_le (i + δ) (le_iSup_of_le ⟨δ, hδ, rfl⟩ le_rfl)
      exact hle hy
    · rintro ⟨δ, hδ, rfl⟩
      exact hj ⟨δ, hδ, fun h => hje (by rw [h]), rfl⟩

theorem aMode_sub_aPos_mem (c : Fin 3) (n : ℕ) (r : ℕ) {i : (ℤ × ℤ) × ℂ}
    (hi : i.1 = (2 * (r : ℤ), 0)) {x : ASpace} (hx : x ∈ aDeg i) :
    aMode c n x - aPos hA c n x ∈ aFilLT r := by
  rw [aPos_of_mem hA c n hx]
  have h := sub_iproj_mem_ne (aDeg_isInternal hA) (e := e0n n) (aMode_shifts hA c n i x hx)
  refine (iSup_le fun j => iSup_le fun hj => ?_ : _ ≤ aFilLT r) h
  obtain ⟨δ, hδ, hne, rfl⟩ := hj
  obtain ⟨d, rfl, hd1, hd0⟩ := modePred_nonneg hδ
  have hd : d = -1 := by
    rcases (show d = -1 ∨ d = 0 by omega) with h | h
    · exact h
    · subst h; exact absurd (by simp) hne
  subst hd
  rcases r with _ | r
  · rw [show aDeg (i + ((2 * -1, 0), ((-(n : ℤ) : ℤ) : ℂ))) =
        layerDeg affineForm affineFlag (i + ((2 * -1, 0), ((-(n : ℤ) : ℤ) : ℂ))) from rfl,
      layerDeg_eq_bot_of affineForm affineFlag]
    · exact bot_le
    · intro t m h
      have := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) h
      simp only [layerIndex, Prod.fst_add, hi] at this
      omega
  · refine (aDeg_le_aFil r ?_).trans le_rfl
    simp only [Prod.fst_add, hi, Prod.mk_add_mk]
    push_cast; ring_nf

theorem grMapA_aPos_of_mem (c : Fin 3) (n : ℕ) (r : ℕ) {i : (ℤ × ℤ) × ℂ}
    (hi : i.1 = (2 * (r : ℤ), 0)) {x : ASpace} (hx : x ∈ aDeg i) :
    grMapA hA r (aPos hA c n x) = grRho r (c, n) (grMapA hA r x) := by
  have hi' : (i + e0n n).1 = (2 * (r : ℤ), 0) := by simp [hi]
  rw [grMapA_of_mem hA r hi' (aPos_mem hA c n hx), grMapA_of_mem hA r hi hx]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, grRho_mk, Submodule.Quotient.eq]
  have h := aMode_sub_aPos_mem hA c n r hi hx
  change (aPos hA c n x - aMode c n x) ∈ aFilLT r
  rw [← neg_sub]
  exact Submodule.neg_mem _ h

/-- **`grMapA` intertwines `aPos` with the induced action on `gr_r A`.** -/
theorem grMapA_aPos (c : Fin 3) (n : ℕ) (r : ℕ) {x : ASpace} (hx : x ∈ SR r) :
    grMapA hA r (aPos hA c n x) = grRho r (c, n) (grMapA hA r x) := by
  induction hx using Submodule.iSup_induction' with
  | mem i y hy =>
      by_cases hi : i.1 = (2 * (r : ℤ), 0)
      · rw [iSup_pos hi] at hy
        exact grMapA_aPos_of_mem hA c n r hi hy
      · rw [iSup_neg hi, Submodule.mem_bot] at hy
        subst hy
        simp
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add, map_add, ihx, ihy, map_add, map_add]

/-! ### `PiR = grMapA ⊗ 1` -/

theorem eq_of_sub_pair {a b : ℤ × ℤ} (h : a - b = (0, 0)) : b = a := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
  exact Prod.ext (by omega) (by omega)

/-- `A ⊗ B → gr_r A ⊗ B`. -/
def PiR (r : ℕ) : ASpace ⊗[ℂ] BSpace →ₗ[ℂ] GrA r ⊗[ℂ] BSpace :=
  TensorProduct.map (grMapA hA r) LinearMap.id

theorem tensorDeg_mem_range (r : ℕ) {w : ℂ} {x : ASpace ⊗[ℂ] BSpace}
    (hx : x ∈ tensorDeg aDeg bDeg ((2 * (r : ℤ), 0), w)) :
    x ∈ LinearMap.range (LinearMap.rTensor BSpace (SR r).subtype) := by
  refine tensorDeg_induction aDeg bDeg _ (fun x => x ∈ LinearMap.range
    (LinearMap.rTensor BSpace (SR r).subtype)) (Submodule.zero_mem _)
    (fun _ _ => Submodule.add_mem _) (fun c _ h => Submodule.smul_mem _ c h) ?_ x hx
  intro b a ha y hy
  by_cases hb : b.1 = (2 * (r : ℤ), 0)
  · exact ⟨⟨a, Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hb ha)⟩ ⊗ₜ[ℂ] y, rfl⟩
  · have hy0 : y = 0 := by
      unfold bDeg trivialDeg at hy
      split_ifs at hy with h
      · exfalso; apply hb
        have := h
        simp only [Prod.fst_sub] at this
        exact eq_of_sub_pair this
      · exact (Submodule.mem_bot ℂ).mp hy
    rw [hy0, TensorProduct.tmul_zero]
    exact Submodule.zero_mem _

/-- **`PiR` is injective on `tensorDeg aDeg bDeg ((2r,0), w)`.** -/
theorem PiR_injOn (r : ℕ) {w : ℂ} {x : ASpace ⊗[ℂ] BSpace}
    (hx : x ∈ tensorDeg aDeg bDeg ((2 * (r : ℤ), 0), w)) (h0 : PiR hA r x = 0) : x = 0 := by
  obtain ⟨x', rfl⟩ := tensorDeg_mem_range r hx
  have hinj : Function.Injective (grMapA hA r ∘ₗ (SR r).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Subtype.ext (grMapA_injOn hA r v.2 hv)
  have h := Module.Flat.rTensor_preserves_injective_linearMap (R := ℂ) (M := BSpace) _ hinj
  have hx' : LinearMap.rTensor BSpace (grMapA hA r ∘ₗ (SR r).subtype) x' = 0 := by
    rw [LinearMap.rTensor_comp_apply]; exact h0
  rw [show x' = 0 from h (by rw [hx', map_zero]), map_zero]

theorem PiR_aPos (r : ℕ) (c : Fin 3) (n : ℕ) {w : ℂ} {x : ASpace ⊗[ℂ] BSpace}
    (hx : x ∈ tensorDeg aDeg bDeg ((2 * (r : ℤ), 0), w)) :
    PiR hA r (TensorProduct.map (aPos hA c n) LinearMap.id x) =
      LinearMap.rTensor BSpace (grRho r (c, n)) (PiR hA r x) := by
  obtain ⟨x', rfl⟩ := tensorDeg_mem_range r hx
  clear hx
  induction x' using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a y =>
      simp only [PiR, LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        Submodule.subtype_apply]
      rw [grMapA_aPos hA c n r a.2]

theorem PiR_bMode (r : ℕ) (c : Fin 3) (n : ℕ) (x : ASpace ⊗[ℂ] BSpace) :
    PiR hA r (TensorProduct.map LinearMap.id (bMode c n) x) =
      LinearMap.lTensor (GrA r) (CyclicEval.bMode (c, n)) (PiR hA r x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a y => rfl

/-- `PiR` lands in the right weight. -/
theorem PiR_weight (r : ℕ) (n0 : ℤ) {x : ASpace ⊗[ℂ] BSpace}
    (hx : x ∈ tensorDeg aDeg bDeg ((2 * (r : ℤ), 0), (n0 : ℂ))) :
    PiR hA r x ∈ tensorWeight (grDeg r) bWeight n0 := by
  refine tensorDeg_induction aDeg bDeg _ (fun x => PiR hA r x ∈ tensorWeight (grDeg r) bWeight n0)
    (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_ x hx
  intro b a ha y hy
  by_cases hb1 : b.1 = (2 * (r : ℤ), 0)
  · by_cases hb : ∃ d : ℤ, b = layerIndex r d
    · obtain ⟨d, rfl⟩ := hb
      have hy' : y ∈ bWeight (n0 - d) := by
        unfold bDeg trivialDeg at hy
        split_ifs at hy with h
        · unfold bWeight
          convert hy using 2
          simp [layerIndex]
        · rw [Submodule.mem_bot] at hy; rw [hy]; exact Submodule.zero_mem _
      have ha' : grMapA hA r a ∈ grDeg r d := by
        rw [grMapA_of_mem hA r rfl ha]
        refine ⟨⟨a, aDeg_le_aFil r rfl ha⟩, ?_, rfl⟩
        have ha2 := ha
        rw [show aDeg (layerIndex r d) = layerDeg affineForm affineFlag (layerIndex r d) from rfl,
          layerDeg_layerIndex] at ha2
        obtain ⟨z, hz, hza⟩ := ha2
        change a ∈ affineFlag.piece r d
        rw [← hza]
        exact GradedFlag.layer_le_pieceIn affineFlag d _ r hz
      rw [PiR, TensorProduct.map_tmul, LinearMap.id_apply]
      exact Submodule.mem_iSup_of_mem d (Submodule.apply_mem_map₂ _ ha' hy')
    · push Not at hb
      have hbot : aDeg b = ⊥ := layerDeg_eq_bot_of affineForm affineFlag (fun t m h => by
        have ht : t = r := by
          have := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) h
          simp only [layerIndex, hb1] at this
          omega
        subst ht
        exact hb m h.symm)
      rw [hbot, Submodule.mem_bot] at ha
      rw [ha, TensorProduct.zero_tmul, map_zero]; exact Submodule.zero_mem _
  · have hy0 : y = 0 := by
      unfold bDeg trivialDeg at hy
      split_ifs at hy with h
      · exfalso; apply hb1
        simp only [Prod.fst_sub] at h
        exact eq_of_sub_pair h
      · exact (Submodule.mem_bot ℂ).mp hy
    rw [hy0, TensorProduct.tmul_zero, map_zero]; exact Submodule.zero_mem _

/-! ### The symbol evaluation preserves the interpreted index -/

theorem rTensor_sum_apply {ι : Type*} (s : Finset ι) (f : ι → Module.End ℂ ASpace)
    (xy : ASpace ⊗[ℂ] BSpace) :
    LinearMap.rTensor BSpace (∑ i ∈ s, f i) xy = ∑ i ∈ s, LinearMap.rTensor BSpace (f i) xy := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.rTensor_add,
        LinearMap.add_apply, ih]

theorem monomial_expOf_cons (q : LexLetter) (l : List LexLetter) :
    (monomial (expOf (q :: l)) (1 : ℂ) : MvPolynomial LexLetter ℂ) =
      X q * monomial (expOf l) 1 := by
  rw [expOf_cons, X, monomial_mul, one_mul]

theorem evalA_word_mem (l : List LexLetter) {j : (ℤ × ℤ) × ℂ} {x : ASpace} (hx : x ∈ aDeg j) :
    (evalA hA (monomial (expOf l) 1) : Module.End ℂ ASpace) x ∈
      aDeg (j + ((2 * (l.length : ℤ), 0), ((enOf (expOf l) : ℕ) : ℂ))) := by
  induction l with
  | nil =>
      have h1 : (monomial (expOf []) (1 : ℂ) : MvPolynomial LexLetter ℂ) = 1 := by
        simp [expOf]
      rw [h1, map_one, Subalgebra.coe_one, Module.End.one_apply]
      convert hx using 2
      ext <;> simp [expOf]
  | cons q l ih =>
      rw [monomial_expOf_cons, map_mul, Subalgebra.coe_mul, evalA_X, Module.End.mul_apply,
        LinearMap.neg_apply]
      have h := aLead_mem hA q ih
      refine Submodule.neg_mem _ ?_
      have e : j + ((2 * ((q :: l).length : ℤ), 0), ((enOf (expOf (q :: l)) : ℕ) : ℂ)) =
          j + ((2 * (l.length : ℤ), 0), ((enOf (expOf l) : ℕ) : ℂ)) + eq q := by
        rw [add_assoc]
        congr 1
        rw [expOf_cons]
        simp only [enOf, map_add, Finsupp.weight_single, smul_eq_mul, one_mul, eq, letterWt,
          List.length_cons]
        ext <;> simp <;> push_cast <;> ring
      rw [e]
      exact h

theorem evalA_monomial_mem (μ : CurrentIndex) {j : (ℤ × ℤ) × ℂ} {x : ASpace} (hx : x ∈ aDeg j) :
    (evalA hA (monomial μ 1) : Module.End ℂ ASpace) x ∈
      aDeg (j + ((2 * (μ.degree : ℤ), 0), ((enOf μ : ℕ) : ℂ))) := by
  have h := evalA_word_mem hA (lexExponentWord μ) hx
  rw [expOf_lexExponentWord] at h
  have hl : (lexExponentWord μ).length = μ.degree := by
    rw [← degree_expOf, expOf_lexExponentWord]
  rwa [hl] at h

/-- **The symbol evaluation preserves the interpreted index.** -/
theorem ev_mem (i : (ℤ × ℤ) × ℂ) :
    ∀ m ∈ matterDeg i, ev hA m ∈ tensorDeg aDeg bDeg i := by
  refine tensorDeg_induction (tensorDeg aDeg bDeg) uDeg i _ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_
  intro b xy hxy u hu
  rw [ev_tmul, evU_apply]
  by_cases hi : ∃ t m, layerIndex t m = i - b
  · obtain ⟨t, m, htm⟩ := hi
    rw [← htm] at hu
    have hsupp := PhiU_support_of_mem hu
    rw [(PhiU u).as_sum, map_sum, AddSubmonoidClass.coe_finset_sum, rTensor_sum_apply]
    refine Submodule.sum_mem _ fun μ hμ => ?_
    obtain ⟨hdeg, hen⟩ := hsupp μ hμ
    rw [show monomial μ (coeff μ (PhiU u)) = coeff μ (PhiU u) • monomial μ 1 by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, Subalgebra.coe_smul,
      LinearMap.rTensor_smul, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    have h := tensorDeg_map_shift aDeg bDeg
      ((evalA hA (monomial μ 1) : Module.End ℂ ASpace)) LinearMap.id
      ((2 * (μ.degree : ℤ), 0), ((enOf μ : ℕ) : ℂ)) 0
      (fun j x hx => evalA_monomial_mem hA μ hx) (fun j y hy => by rwa [add_zero]) b xy hxy
    have e : b + (((2 * (μ.degree : ℤ), 0), ((enOf μ : ℕ) : ℂ)) + 0) = i := by
      rw [add_zero, hdeg]
      have : ((2 * (t : ℤ), 0), ((enOf μ : ℕ) : ℂ)) = i - b := by
        rw [← htm]; simp only [layerIndex]; rw [← hen]; push_cast; rfl
      rw [this]; abel
    rwa [e] at h
  · push Not at hi
    rw [uDeg_eq_bot_of hi, Submodule.mem_bot] at hu
    rw [hu, map_zero, map_zero, ZeroMemClass.coe_zero, LinearMap.rTensor_zero,
      LinearMap.zero_apply]
    exact Submodule.zero_mem _

end

end VOA.KoszulResidual
