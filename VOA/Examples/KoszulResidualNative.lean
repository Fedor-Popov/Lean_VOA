/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualMatter
import VOA.Examples.BRSTConjIdentityGhost

/-!
# The native Koszul differential, its contracting homotopy, and the Koszul Laplacian

On the actual BRST space `Matter ⊗ Ghost`, for a finite set `s` of letters `q = (a, j)`:

* `gAn q`, `gCr q` — the annihilation `c^a_{j+1}` and creation `b^a_{-j-1}` operators of the
  antighost mode `q`, with the CAR `{gAn q, gCr q'} = δ_{qq'}` (`gAn_gCr`);
* `dN s = Σ_{q ∈ s} u_q ⊗ gAn q` — **the native Koszul differential**;
* `hN s = Σ_{q ∈ s} D_q ⊗ gCr q` — **the contracting homotopy**;
* `Nb s = Σ_{q ∈ s} gCr q gAn q` — the antighost number (of the modes in `s`);
* `ΔN s = L_s ⊗ 1 + 1 ⊗ Nb s`.

Proved (pure operator algebra from the Weyl relations of `KoszulResidualMatter` and the ghost CAR):

* `dN_hN_add` — `dN hN + hN dN = ΔN`;
* `dN_dN` — `dN² = 0`;
* `ΔN_dN` — `ΔN dN = dN ΔN`;
* `mDerB_ΔN` — `(D_q ⊗ 1) ΔN = (ΔN + 1)(D_q ⊗ 1)`.

Everything is proved outright from `hA`.
-/

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.LeeYangTransferAssembly
open scoped TensorProduct

noncomputable section

/-! ### The antighost modes -/

/-- The annihilation operator `c^a_{j+1}` of the antighost mode `q = (a, j)`. -/
abbrev gAn (q : LexLetter) : Module.End ℂ Sl2GhostSpace :=
  ConcreteHodge.An (ofLex q).1 ((ofLex q).2, 0)

/-- The creation operator `b^a_{-j-1}` of the antighost mode `q = (a, j)`. -/
abbrev gCr (q : LexLetter) : Module.End ℂ Sl2GhostSpace :=
  ConcreteHodge.Cr (ofLex q).1 ((ofLex q).2, 0)

theorem letter_eq_iff (q q' : LexLetter) :
    ((ofLex q).1 = (ofLex q').1 ∧ (((ofLex q).2, (0 : Fin 2)) = ((ofLex q').2, 0))) ↔ q = q' := by
  constructor
  · rintro ⟨h1, h2⟩
    apply ofLex.injective
    exact Prod.ext h1 (congrArg Prod.fst h2)
  · rintro rfl; exact ⟨rfl, rfl⟩

/-- **The CAR** for the antighost modes. -/
theorem gAn_gCr_apply (q q' : LexLetter) (y : Sl2GhostSpace) :
    gAn q (gCr q' y) = (if q = q' then y else 0) - gCr q' (gAn q y) := by
  have h := An_Cr_anticomm (ofLex q).1 (ofLex q').1 ((ofLex q).2, 0) ((ofLex q').2, 0) y
  rw [eq_sub_iff_add_eq]
  convert h using 1
  by_cases hq : q = q'
  · rw [if_pos hq, if_pos ((letter_eq_iff q q').mpr hq)]
  · rw [if_neg hq, if_neg (fun h' => hq ((letter_eq_iff q q').mp h'))]

theorem gAn_gAn_apply (q q' : LexLetter) (y : Sl2GhostSpace) :
    gAn q (gAn q' y) = -gAn q' (gAn q y) := by
  have h := gMode_anticomm_apply (ofLex q).1 (ofLex q').1 (0 + 1) (0 + 1) ((ofLex q).2 : ℤ)
    ((ofLex q').2 : ℤ) y
  rw [if_neg (by rintro ⟨-, h, -⟩; exact absurd h (by decide))] at h
  exact eq_neg_of_add_eq_zero_left h

theorem gCr_gCr_apply (q q' : LexLetter) (y : Sl2GhostSpace) :
    gCr q (gCr q' y) = -gCr q' (gCr q y) :=
  Cr_Cr_anticomm _ _ _ _ y

/-- The antighost number of the modes in `s`. -/
def Nb (s : Finset LexLetter) : Module.End ℂ Sl2GhostSpace := ∑ q ∈ s, gCr q ∘ₗ gAn q

theorem Nb_apply (s : Finset LexLetter) (y : Sl2GhostSpace) :
    Nb s y = ∑ q ∈ s, gCr q (gAn q y) := by
  simp [Nb, LinearMap.coe_sum]

/-- `[Nb s, gAn q] = -gAn q` for `q ∈ s`. -/
theorem Nb_gAn (s : Finset LexLetter) {q : LexLetter} (hq : q ∈ s) (y : Sl2GhostSpace) :
    Nb s (gAn q y) = gAn q (Nb s y) - gAn q y := by
  rw [Nb_apply, Nb_apply, map_sum]
  have hterm : ∀ p, gCr p (gAn p (gAn q y)) =
      gAn q (gCr p (gAn p y)) - if p = q then gAn p y else 0 := by
    intro p
    rw [gAn_gCr_apply, gAn_gAn_apply, map_neg]
    by_cases hpq : p = q
    · rw [if_pos hpq.symm, if_pos hpq, hpq]; abel
    · rw [if_neg (Ne.symm hpq), if_neg hpq]; abel
  simp only [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq_of_mem' s q _ hq]

/-! ### The native operators on the BRST space -/

section Native

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

/-- **The native Koszul differential** `Σ_{q ∈ s} u_q ⊗ c_{q}`. -/
def dN (s : Finset LexLetter) : Module.End ℂ BRSTSpace :=
  ∑ q ∈ s, TensorProduct.map (mLead hA q) (gAn q)

/-- **The contracting homotopy** `Σ_{q ∈ s} D_q ⊗ b_{q}`. -/
def hN (s : Finset LexLetter) : Module.End ℂ BRSTSpace :=
  ∑ q ∈ s, TensorProduct.map (mDer q) (gCr q)

/-- **The Koszul Laplacian** `L_s ⊗ 1 + 1 ⊗ Nb s`. -/
def ΔN (s : Finset LexLetter) : Module.End ℂ BRSTSpace :=
  TensorProduct.map (mL hA s) LinearMap.id + TensorProduct.map LinearMap.id (Nb s)

theorem mDer_mLead_apply (q q' : LexLetter) (x : MatterSpace) :
    mDer q (mLead hA q' x) = mLead hA q' (mDer q x) + if q = q' then x else 0 := by
  have h := LinearMap.congr_fun (mDer_mLead hA q q') x
  rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply] at h
  rw [h]
  split_ifs <;> rfl

theorem mLead_comm_apply (q q' : LexLetter) (x : MatterSpace) :
    mLead hA q (mLead hA q' x) = mLead hA q' (mLead hA q x) := by
  have h := LinearMap.congr_fun (mLead_comm hA q q') x
  simpa using h

theorem mDer_comm_apply (q q' : LexLetter) (x : MatterSpace) :
    mDer q (mDer q' x) = mDer q' (mDer q x) := by
  have h := LinearMap.congr_fun (mDer_comm q q') x
  simpa using h

theorem mL_apply (s : Finset LexLetter) (x : MatterSpace) :
    mL hA s x = ∑ q ∈ s, mLead hA q (mDer q x) := by
  simp [mL, LinearMap.coe_sum]

/-- The termwise identity behind `dN hN + hN dN = ΔN`. -/
theorem term_identity (q q' : LexLetter) (x : MatterSpace) (y : Sl2GhostSpace) :
    mLead hA q (mDer q' x) ⊗ₜ[ℂ] gAn q (gCr q' y) + mDer q' (mLead hA q x) ⊗ₜ[ℂ] gCr q' (gAn q y) =
      if q = q' then mLead hA q (mDer q x) ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] gCr q (gAn q y) else 0 := by
  rw [gAn_gCr_apply, mDer_mLead_apply]
  by_cases h : q = q'
  · subst h
    simp only [if_true]
    rw [TensorProduct.tmul_sub, TensorProduct.add_tmul]
    abel
  · simp only [if_neg h, if_neg (Ne.symm h), add_zero]
    rw [zero_sub, TensorProduct.tmul_neg]
    abel

/-- **`dN hN + hN dN = ΔN`.** -/
theorem dN_hN_add (s : Finset LexLetter) (v : BRSTSpace) :
    dN hA s (hN s v) + hN s (dN hA s v) = ΔN hA s v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add]; rw [← hv, ← hw]; abel
  | tmul x y =>
      simp only [dN, hN, ΔN, LinearMap.coe_sum, Finset.sum_apply, map_sum,
        TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.id_apply]
      conv_lhs => arg 1; rw [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      simp only [← Finset.sum_add_distrib, term_identity, Finset.sum_ite_eq]
      rw [mL_apply, Nb_apply, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q hq => by rw [if_pos hq]

theorem sum_sum_antisymm {ι M : Type*} [AddCommGroup M] [Module ℂ M] (s : Finset ι)
    (f : ι → ι → M) (hf : ∀ q q', f q q' = -f q' q) : ∑ q ∈ s, ∑ q' ∈ s, f q q' = 0 := by
  have hswap : ∑ q ∈ s, ∑ q' ∈ s, f q q' = -∑ q ∈ s, ∑ q' ∈ s, f q q' := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun q' _ => hf q' q
  have h2 : (2 : ℂ) • ∑ q ∈ s, ∑ q' ∈ s, f q q' = 0 := by
    rw [two_smul]; nth_rewrite 2 [hswap]; rw [add_neg_cancel]
  exact eq_zero_of_smul_eq_zero (by norm_num) h2

/-- **`dN² = 0`.** -/
theorem dN_dN (s : Finset LexLetter) (v : BRSTSpace) : dN hA s (dN hA s v) = 0 := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => rw [map_add, map_add, hv, hw, add_zero]
  | tmul x y =>
      simp only [dN, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul]
      refine sum_sum_antisymm s _ fun q q' => ?_
      rw [mLead_comm_apply, gAn_gAn_apply, TensorProduct.tmul_neg]

/-- `L_s u_q = u_q L_s + u_q` for `q ∈ s`. -/
theorem mL_mLead (s : Finset LexLetter) {q : LexLetter} (hq : q ∈ s) (x : MatterSpace) :
    mL hA s (mLead hA q x) = mLead hA q (mL hA s x) + mLead hA q x := by
  rw [mL_apply, mL_apply, map_sum]
  simp only [mDer_mLead_apply, map_add, mLead_comm_apply hA _ q]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single q (fun b _ hb => by rw [if_neg hb, map_zero])
    (fun h => absurd hq h), if_pos rfl]

/-- `D_q L_s = L_s D_q + D_q`. -/
theorem mDer_mL (s : Finset LexLetter) (q : LexLetter) (x : MatterSpace) :
    mDer q (mL hA s x) = mL hA s (mDer q x) + if q ∈ s then mDer q x else 0 := by
  rw [mL_apply, mL_apply, map_sum]
  simp only [mDer_mLead_apply, mDer_comm_apply q]
  rw [Finset.sum_add_distrib]
  congr 1
  split_ifs with hq
  · rw [Finset.sum_eq_single q (fun b _ hb => by rw [if_neg (Ne.symm hb)])
      (fun h => absurd hq h), if_pos rfl]
  · exact Finset.sum_eq_zero fun b hb => by rw [if_neg (fun e => hq (by rw [e]; exact hb))]

/-- **`ΔN dN = dN ΔN`.** -/
theorem ΔN_dN (s : Finset LexLetter) (v : BRSTSpace) :
    ΔN hA s (dN hA s v) = dN hA s (ΔN hA s v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul x y =>
      simp only [dN, ΔN, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
        LinearMap.add_apply, LinearMap.id_apply, map_add]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [mL_mLead hA s hq, Nb_gAn s hq, TensorProduct.add_tmul, TensorProduct.tmul_sub]
      abel

/-- The derivation `D_q ⊗ 1` on the BRST space. -/
def mDerB (q : LexLetter) : Module.End ℂ BRSTSpace := TensorProduct.map (mDer q) LinearMap.id

/-- **`(D_q ⊗ 1) ΔN = (ΔN + 1)(D_q ⊗ 1)`** for `q ∈ s`. -/
theorem mDerB_ΔN (s : Finset LexLetter) {q : LexLetter} (hq : q ∈ s) (v : BRSTSpace) :
    mDerB q (ΔN hA s v) = ΔN hA s (mDerB q v) + mDerB q v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => rw [map_add, map_add, hv, hw, map_add, map_add]; abel
  | tmul x y =>
      simp only [mDerB, ΔN, TensorProduct.map_tmul, LinearMap.add_apply, LinearMap.id_apply,
        map_add]
      rw [mDer_mL, if_pos hq, TensorProduct.add_tmul]
      abel

theorem hN_eq_sum (s : Finset LexLetter) (v : BRSTSpace) :
    hN s v = ∑ q ∈ s, TensorProduct.map LinearMap.id (gCr q) (mDerB q v) := by
  simp only [hN, mDerB, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]

theorem hN_eq_zero_of (s : Finset LexLetter) {v : BRSTSpace} (h : ∀ q ∈ s, mDerB q v = 0) :
    hN s v = 0 := by
  rw [hN_eq_sum]
  exact Finset.sum_eq_zero fun q hq => by rw [h q hq, map_zero]

end Native

end

end VOA.KoszulResidual
