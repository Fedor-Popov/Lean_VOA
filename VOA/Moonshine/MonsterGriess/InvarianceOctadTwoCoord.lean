/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), file:
  CFSG/Monster/Griess/Invariance/OctadTwoCoord.lean
Original authors (from the `@misc{axiom-cfsg}` citation, "Lean formalization of the
classification of finite simple groups", 2026):
  Cureton, Dean and Ilin, Vasily and Mehta, Bhavik and Voss, Niels and Cabral, Rafael and
  Defant, Colin and Gregory, Erik and Hill, Aaron and Hong, Letong and Hu, Qinheping and Jamner,
  Dustin and Jiang, Albert and Jordan, Tadeusz and Kurghinyan, Andranik and Lau, Kenny and
  Laurent, Jonathan and Liang, David and Limperg, Jannis and Mahns, Simon and Nugent, Brian and
  Olson, Connor and Ono, Ken and Paul, Eric and Rajan, Dhruv and Ram, Karun and Ray, Charlie and
  Siu, Ho Chung and Swaminathan, Ashvin A. and Thorner, Jesse and Tsaplin, Aleksey and Wang,
  Chenkai.
Port to Lean 4.30.0 / Mathlib v4.30.0 for LeanVOA by Fedor K. Popov (with Claude).
Released under the Apache 2.0 license.  Modifications relative to the source are listed in the
"Port notes" section of the module docstring below.
-/
import VOA.Moonshine.MonsterGriess.InvarianceOctadBasic

/-!
# Axiom's Monster port: triality invariance on (octad, octad, pair) triples

For an octad `d` and a pair `p ⊆ supp d` the matrices `(T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩)
(pairVec p j))_{v,w}` are `octZ`, `octD · octP · octD`, `octP` for `j = 0, 1, 2`
(`T_oct_oct_pair_in`, `twoCoef`), they vanish otherwise (`T_oct_oct_pair_out`,
`T_oct_oct_pair_cross`), and conjugation by `octHD d` cycles them (`twoCoef_conj`).  Hence `T`
is `tauB`-invariant on `octSpan × octSpan × pairSpan`.  Summary:
`triality_Griess_octad_two_coordinate_invariance`.

## Port notes
* Namespace `CFSG.Monster.Griess` ↦ `VOA.Moonshine.MonsterGriess` (as in the earlier ports).
  Module-system syntax, `@[expose]` and the source's `attribute [-instance] …` line dropped.
  Bodies verbatim except as listed.
* `OctadInv.qf_basisA_pair`: the source rewrites with Mathlib's `single_mulVec_eq`, absent from
  Mathlib v4.30; re-proved from `Matrix.single_mulVec` (same statement).
* Mathlib drift: `ite_eq_right h` ↦ `if_neg h`.
-/

set_option linter.style.longLine false
set_option linter.style.show false

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin VOA.Moonshine.MonsterGriess.SpinLattice Matrix Module

namespace OctadInv

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

noncomputable def octZ (d : OctadWord) (h : Octad.EvenQuot (octSupp d)) :
    Matrix (Octad.EvenQuot (octSupp d)) (Octad.EvenQuot (octSupp d)) ℚ :=
  diagonal fun v => sgn (bd d v h)

noncomputable def octP (d : OctadWord) (h : Octad.EvenQuot (octSupp d)) :
    Matrix (Octad.EvenQuot (octSupp d)) (Octad.EvenQuot (octSupp d)) ℚ :=
  of fun v w => if w = v + h then 1 else 0

noncomputable def twoCoef (d : OctadWord) (h : Octad.EvenQuot (octSupp d)) :
    Fin 3 → Octad.EvenQuot (octSupp d) → Octad.EvenQuot (octSupp d) → ℚ :=
  ![fun v w => if v = w then sgn (bd d v h) else 0,
    fun v w => if w = v + h then sgn (qd d v + qd d w) else 0,
    fun v w => if w = v + h then 1 else 0]

theorem octZ_apply (d : OctadWord) (h v w : Octad.EvenQuot (octSupp d)) :
    octZ d h v w = twoCoef d h 0 v w := by
  rw [octZ, diagonal_apply]
  rfl

theorem octP_apply (d : OctadWord) (h v w : Octad.EvenQuot (octSupp d)) :
    octP d h v w = twoCoef d h 2 v w := rfl

theorem octD_octP_octD_apply (d : OctadWord) (h v w : Octad.EvenQuot (octSupp d)) :
    (octD d * octP d h * octD d) v w = twoCoef d h 1 v w := by
  rw [octD, signMatrix, mul_diagonal, diagonal_mul, octP, of_apply]
  show _ = if w = v + h then sgn (qd d v + qd d w) else 0
  rw [sgn_add]
  split_ifs <;> ring

theorem octLab_inj {o o' : OctIdx} : octLab o' = octLab o ↔ o' = o := by
  rw [labelIdx_injective.eq_iff]
  simp

theorem inX_sub' (x y : SpaceX) : inX (x - y) = inX x - inX y := by
  show ((0 : symMat), x - y, (0 : SpaceW)) =
    ((0 : symMat), x, (0 : SpaceW)) - ((0 : symMat), y, (0 : SpaceW))
  rw [Prod.mk_sub_mk, Prod.mk_sub_mk, sub_zero, sub_zero]

theorem inX_add' (x y : SpaceX) : inX (x + y) = inX x + inX y := by
  show ((0 : symMat), x + y, (0 : SpaceW)) =
    ((0 : symMat), x, (0 : SpaceW)) + ((0 : symMat), y, (0 : SpaceW))
  rw [Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero]

theorem qf_basisA_pair (c : ShortIdx) {k l : Fin 24} (hkl : k ≠ l) :
    qf c (basisA s(k, l)) = 2 * (uQ c k * uQ c l) := by
  have hs : ∀ a b : Fin 24, (Matrix.single a b (1 : ℚ)) *ᵥ uQ c = Pi.single a (uQ c b) := by
    intro a b
    rw [single_mulVec, one_mul]
    rfl
  rw [qf, coe_basisA, if_neg hkl, add_mulVec, hs, hs, dotProduct_add, dotProduct_single,
    dotProduct_single]
  ring

theorem T_oct_oct_A (o o' : OctIdx) (p : LtPair) :
    T (octVec o) (octVec o') (pairVec p 0) =
      if o' = o then qf (octLab o) (basisA s(p.1.1, p.1.2)) / 8 else 0 := by
  rw [octVec_eq, octVec_eq, pairVec_zero, T_sgl_sgl_A]
  by_cases h : o' = o
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun h' => h (octLab_inj.1 h'))]

theorem T_oct_oct_B (o o' : OctIdx) (p : LtPair) :
    T (octVec o) (octVec o') (pairVec p 1) =
      tau (octLab o) (octLab o') (minusLab p) - tau (octLab o) (octLab o') (plusLab p) := by
  rw [octVec_eq, octVec_eq, pairVec_one, inX_sub', map_sub, T_sgl3, T_sgl3]

theorem T_oct_oct_C (o o' : OctIdx) (p : LtPair) :
    T (octVec o) (octVec o') (pairVec p 2) =
      tau (octLab o) (octLab o') (minusLab p) + tau (octLab o) (octLab o') (plusLab p) := by
  rw [octVec_eq, octVec_eq, pairVec_two, inX_add', map_add, T_sgl3, T_sgl3]

theorem T_oct_oct_A_same (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) (p : LtPair) :
    T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p 0) =
      if v = w then (if p.1.1 ∈ octSupp d ∧ p.1.2 ∈ octSupp d then
        sgn (bd d v (Octad.cls (octSupp d) {p.1.1, p.1.2})) else 0) else 0 := by
  rw [T_oct_oct_A]
  have hiff : (⟨d, w⟩ : OctIdx) = ⟨d, v⟩ ↔ v = w := by
    rw [Sigma.mk.inj_iff]
    simp only [heq_eq_eq, true_and]
    exact eq_comm
  by_cases hvw : v = w
  · rw [if_pos (hiff.2 hvw), if_pos hvw, qf_basisA_pair _ p.2.ne, uQ_mul_uQ_oct]
    by_cases hkl : p.1.1 ∈ octSupp d ∧ p.1.2 ∈ octSupp d
    · rw [if_pos hkl, if_pos hkl.1, if_pos hkl.2,
        bd_pair d v p.2.ne hkl.1 hkl.2, sgn_add]
      ring
    · rw [if_neg hkl]
      by_cases hk : p.1.1 ∈ octSupp d
      · have hl : p.1.2 ∉ octSupp d := fun hl => hkl ⟨hk, hl⟩
        rw [if_neg hl]
        ring
      · rw [if_neg hk]
        ring
  · rw [if_neg (fun h => hvw (hiff.1 h)), if_neg hvw]

theorem oct_add_oct (d : C) (n n' : ZMod 2) : d + n • ΩC + (d + n' • ΩC) = (n + n') • ΩC := by
  rw [add_add_add_comm, add_self_F2, zero_add, add_smul]

theorem cocode_add_cocode (θ x y : Cocode) : θ + x + (θ + y) = x + y := by
  rw [add_add_add_comm, add_self_F2, zero_add]

theorem fst_eq_octLab_add_iff (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) (m : ZMod 2)
    (ζ : Cocode) :
    ((m • ΩC, ζ) : C × Cocode) = (octLab ⟨d, v⟩).1 + (octLab ⟨d, w⟩).1 ↔
      m = qd d v + qd d w ∧ ζ = Submodule.Quotient.mk (Octad.ind (octRep d v)) +
        Submodule.Quotient.mk (Octad.ind (octRep d w)) := by
  rw [octLab_fst, octLab_fst, Prod.mk_add_mk, Prod.mk.injEq, oct_add_oct, cocode_add_cocode,
    smul_ΩC_inj, nOct_octRep, nOct_octRep]

theorem fst_ne_octLab_add {d d' : OctadWord} (hne : d ≠ d') (v : Octad.EvenQuot (octSupp d))
    (w : Octad.EvenQuot (octSupp d')) (m : ZMod 2) (ζ : Cocode) :
    ((m • ΩC, ζ) : C × Cocode) ≠ (octLab ⟨d, v⟩).1 + (octLab ⟨d', w⟩).1 := by
  intro h
  rw [octLab_fst, octLab_fst, Prod.mk_add_mk, Prod.mk.injEq] at h
  have h1 := h.1
  have e : (d : C) + (d' : C) = (m + nOct (octRep d v) + nOct (octRep d' w)) • ΩC := by
    rw [add_smul, add_smul, h1]
    have e' : (d : C) + nOct (octRep d v) • ΩC + ((d' : C) + nOct (octRep d' w) • ΩC) +
        nOct (octRep d v) • ΩC + nOct (octRep d' w) • ΩC =
        (d : C) + d' + (nOct (octRep d v) • ΩC + nOct (octRep d v) • ΩC) +
          (nOct (octRep d' w) • ΩC + nOct (octRep d' w) • ΩC) := by abel
    rw [e', add_self_F2, add_self_F2, add_zero, add_zero]
  exact hne (octad_eq_of_add_eq_smul e).1

theorem pair_octLab_same (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) :
    pair (octLab ⟨d, w⟩).1.1 (octLab ⟨d, v⟩).1.2 = 0 := by
  simp only [octLab_fst]
  rw [pair_add_smul_ΩC_thetaD, θ_self, P_oct, pair_oct_ind (octRep_subset d v) (octRep_even d v),
    pair_ΩC_ind (octRep_even d v)]
  simp

theorem ind_octRep_apply_of_notMem (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) {i : Fin 24}
    (hi : i ∉ octSupp d) : Octad.ind (octRep d v) i = 0 := by
  rw [Octad.ind_apply, if_neg fun h => hi (octRep_subset d v h)]

theorem deltaPair_eq_iff (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) {k l : Fin 24}
    (hkl : k ≠ l) (hk : k ∈ octSupp d) (hl : l ∈ octSupp d) :
    deltaPair k l = Submodule.Quotient.mk (Octad.ind (octRep d v)) +
        Submodule.Quotient.mk (Octad.ind (octRep d w)) ↔
      w = v + Octad.cls (octSupp d) {k, l} := by
  have hpair := Octad.ind_mem_evenSubsets (pair_subset_octSupp hk hl) (even_card_pair hkl)
  have hx : Octad.ind (octRep d v) + Octad.ind (octRep d w) + Octad.ind {k, l} ∈
      Octad.evenSubsets (octSupp d) :=
    add_mem (add_mem (ind_mem_octRep d v) (ind_mem_octRep d w)) hpair
  have e : Octad.mk (octSupp d) ⟨_, hx⟩ = v + w + Octad.cls (octSupp d) {k, l} := by
    calc Octad.mk (octSupp d) ⟨_, hx⟩ =
        Octad.mk (octSupp d) ⟨Octad.ind (octRep d v), ind_mem_octRep d v⟩ +
          Octad.mk (octSupp d) ⟨Octad.ind (octRep d w), ind_mem_octRep d w⟩ +
          Octad.mk (octSupp d) ⟨Octad.ind {k, l}, hpair⟩ := by
          rw [← map_add, ← map_add]
          rfl
      _ = v + w + Octad.cls (octSupp d) {k, l} := by
          rw [octMk_octRep, octMk_octRep,
            octMk_eq_cls (pair_subset_octSupp hk hl) (even_card_pair hkl)]
  have hcoc : (Submodule.Quotient.mk (Octad.ind (octRep d v) + Octad.ind (octRep d w) +
      Octad.ind {k, l}) : Cocode) = Submodule.Quotient.mk (Octad.ind (octRep d v)) +
        Submodule.Quotient.mk (Octad.ind (octRep d w)) + deltaPair k l := by
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, ind_pair hkl]
    rfl
  calc deltaPair k l = Submodule.Quotient.mk (Octad.ind (octRep d v)) +
        Submodule.Quotient.mk (Octad.ind (octRep d w)) ↔
      Submodule.Quotient.mk (Octad.ind (octRep d v)) +
        Submodule.Quotient.mk (Octad.ind (octRep d w)) + deltaPair k l = 0 :=
        eq_comm.trans (eq_iff_add_eq_zero_F2 _ _)
    _ ↔ (Submodule.Quotient.mk (Octad.ind (octRep d v) + Octad.ind (octRep d w) +
        Octad.ind {k, l}) : Cocode) = 0 := by rw [hcoc]
    _ ↔ Octad.mk (octSupp d) ⟨_, hx⟩ = 0 := mk_eq_zero_iff_octMk_eq_zero ⟨_, hx⟩
    _ ↔ w = v + Octad.cls (octSupp d) {k, l} := by rw [e, add_add_eq_zero_iff_F2]

theorem deltaPair_ne_of_out (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) {k l : Fin 24}
    (hkl : k ≠ l) (hout : ¬(k ∈ octSupp d ∧ l ∈ octSupp d)) :
    deltaPair k l ≠ Submodule.Quotient.mk (Octad.ind (octRep d v)) +
        Submodule.Quotient.mk (Octad.ind (octRep d w)) := by
  intro h
  have h' := (eq_comm.trans (eq_iff_add_eq_zero_F2 _ _)).1 h
  have hcoc : Submodule.Quotient.mk (Octad.ind (octRep d v)) +
      Submodule.Quotient.mk (Octad.ind (octRep d w)) + deltaPair k l =
      (Submodule.Quotient.mk (Octad.ind (octRep d v) + Octad.ind (octRep d w) +
        (Pi.single k 1 + Pi.single l 1)) : Cocode) := by
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add]
    rfl
  rw [hcoc, Submodule.Quotient.mk_eq_zero] at h'
  refine not_mem_C_of_outside hkl (fun i hi => ?_) hout h'
  rw [Pi.add_apply, Pi.add_apply, ind_octRep_apply_of_notMem d v hi,
    ind_octRep_apply_of_notMem d w hi, zero_add, zero_add]

theorem minusLab_fst' (p : LtPair) :
    (minusLab p).1 = ((0 : ZMod 2) • ΩC, deltaPair p.1.1 p.1.2) := by
  rw [minusLab_fst, zero_smul]

theorem plusLab_fst' (p : LtPair) : (plusLab p).1 = ((1 : ZMod 2) • ΩC, deltaPair p.1.1 p.1.2) := by
  rw [plusLab_fst, one_smul]

theorem tau_oct_oct_pair_in (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) (p : LtPair)
    (hk : p.1.1 ∈ octSupp d) (hl : p.1.2 ∈ octSupp d) (z : ShortIdx) (m : ZMod 2)
    (hz : z.1 = (m • ΩC, deltaPair p.1.1 p.1.2)) :
    tau (octLab ⟨d, v⟩) (octLab ⟨d, w⟩) z =
      if w = v + Octad.cls (octSupp d) {p.1.1, p.1.2} then
        (if m = qd d v + qd d w then 1 else 0) else 0 := by
  rw [tau_eq, hz, pair_octLab_same, sgn_zero]
  have key : ((m • ΩC, deltaPair p.1.1 p.1.2) : C × Cocode) =
      (octLab ⟨d, v⟩).1 + (octLab ⟨d, w⟩).1 ↔
      m = qd d v + qd d w ∧ w = v + Octad.cls (octSupp d) {p.1.1, p.1.2} := by
    rw [fst_eq_octLab_add_iff, deltaPair_eq_iff d v w p.2.ne hk hl]
  by_cases hw : w = v + Octad.cls (octSupp d) {p.1.1, p.1.2}
  · rw [if_pos hw]
    by_cases hm : m = qd d v + qd d w
    · rw [if_pos (key.2 ⟨hm, hw⟩), if_pos hm]
    · rw [if_neg (fun h => hm (key.1 h).1), if_neg hm]
  · rw [if_neg hw, if_neg (fun h => hw (key.1 h).2)]

theorem tau_oct_oct_pair_out (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) (p : LtPair)
    (hout : ¬(p.1.1 ∈ octSupp d ∧ p.1.2 ∈ octSupp d)) (z : ShortIdx) (m : ZMod 2)
    (hz : z.1 = (m • ΩC, deltaPair p.1.1 p.1.2)) :
    tau (octLab ⟨d, v⟩) (octLab ⟨d, w⟩) z = 0 := by
  rw [tau_eq, hz, if_neg fun h =>
    deltaPair_ne_of_out d v w p.2.ne hout ((fst_eq_octLab_add_iff d v w m _).1 h).2]

theorem tau_oct_oct_cross {d d' : OctadWord} (hne : d ≠ d') (v : Octad.EvenQuot (octSupp d))
    (w : Octad.EvenQuot (octSupp d')) (z : ShortIdx) (m : ZMod 2) (ζ : Cocode)
    (hz : z.1 = (m • ΩC, ζ)) : tau (octLab ⟨d, v⟩) (octLab ⟨d', w⟩) z = 0 := by
  rw [tau_eq, hz, if_neg (fst_ne_octLab_add hne v w m ζ)]

private theorem ite_sub_ite (t : ZMod 2) :
    ((if 0 = t then 1 else 0) - (if 1 = t then 1 else 0) : ℚ) = sgn t := by
  rcases zmod2_cases t with rfl | rfl
  · rw [if_pos rfl, if_neg (by decide), sub_zero, sgn_zero]
  · rw [if_neg (by decide), if_pos rfl]
    norm_num [sgn]

private theorem ite_add_ite (t : ZMod 2) :
    ((if 0 = t then 1 else 0) + (if 1 = t then 1 else 0) : ℚ) = 1 := by
  rcases zmod2_cases t with rfl | rfl
  · rw [if_pos rfl, if_neg (by decide), add_zero]
  · rw [if_neg (by decide), if_pos rfl, zero_add]

theorem T_oct_oct_pair_in (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) (p : LtPair)
    (hk : p.1.1 ∈ octSupp d) (hl : p.1.2 ∈ octSupp d) (j : Fin 3) :
    T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p j) =
      twoCoef d (Octad.cls (octSupp d) {p.1.1, p.1.2}) j v w := by
  have hm := tau_oct_oct_pair_in d v w p hk hl (minusLab p) 0 (minusLab_fst' p)
  have hp := tau_oct_oct_pair_in d v w p hk hl (plusLab p) 1 (plusLab_fst' p)
  fin_cases j
  · show T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p 0) =
      if v = w then sgn (bd d v (Octad.cls (octSupp d) {p.1.1, p.1.2})) else 0
    rw [T_oct_oct_A_same, if_pos (⟨hk, hl⟩ : p.1.1 ∈ octSupp d ∧ p.1.2 ∈ octSupp d)]
  · show T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p 1) =
      if w = v + Octad.cls (octSupp d) {p.1.1, p.1.2} then sgn (qd d v + qd d w) else 0
    rw [T_oct_oct_B, hm, hp]
    by_cases hw : w = v + Octad.cls (octSupp d) {p.1.1, p.1.2}
    · rw [if_pos hw, if_pos hw, if_pos hw, ite_sub_ite]
    · rw [if_neg hw, if_neg hw, if_neg hw, sub_zero]
  · show T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p 2) =
      if w = v + Octad.cls (octSupp d) {p.1.1, p.1.2} then 1 else 0
    rw [T_oct_oct_C, hm, hp]
    by_cases hw : w = v + Octad.cls (octSupp d) {p.1.1, p.1.2}
    · rw [if_pos hw, if_pos hw, if_pos hw, ite_add_ite]
    · rw [if_neg hw, if_neg hw, if_neg hw, add_zero]

theorem T_oct_oct_pair_out (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) (p : LtPair)
    (hout : ¬(p.1.1 ∈ octSupp d ∧ p.1.2 ∈ octSupp d)) (j : Fin 3) :
    T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p j) = 0 := by
  have hm := tau_oct_oct_pair_out d v w p hout (minusLab p) 0 (minusLab_fst' p)
  have hp := tau_oct_oct_pair_out d v w p hout (plusLab p) 1 (plusLab_fst' p)
  fin_cases j
  · show T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p 0) = 0
    rw [T_oct_oct_A_same, if_neg hout]
    split_ifs <;> rfl
  · show T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p 1) = 0
    rw [T_oct_oct_B, hm, hp, sub_zero]
  · show T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p 2) = 0
    rw [T_oct_oct_C, hm, hp, add_zero]

theorem T_oct_oct_pair_cross {o o' : OctIdx} (hne : o.1 ≠ o'.1) (p : LtPair) (j : Fin 3) :
    T (octVec o) (octVec o') (pairVec p j) = 0 := by
  obtain ⟨d, v⟩ := o
  obtain ⟨d', w⟩ := o'
  have hne' : d ≠ d' := hne
  have hm := tau_oct_oct_cross hne' v w (minusLab p) 0 _ (minusLab_fst' p)
  have hp := tau_oct_oct_cross hne' v w (plusLab p) 1 _ (plusLab_fst' p)
  fin_cases j
  · show T (octVec ⟨d, v⟩) (octVec ⟨d', w⟩) (pairVec p 0) = 0
    rw [T_oct_oct_A, if_neg]
    intro h
    exact hne' (congrArg Sigma.fst h).symm
  · show T (octVec ⟨d, v⟩) (octVec ⟨d', w⟩) (pairVec p 1) = 0
    rw [T_oct_oct_B, hm, hp, sub_zero]
  · show T (octVec ⟨d, v⟩) (octVec ⟨d', w⟩) (pairVec p 2) = 0
    rw [T_oct_oct_C, hm, hp, add_zero]

theorem conj_zero (d : OctadWord) (h v w : Octad.EvenQuot (octSupp d)) :
    ∑ x, ∑ y, octHD d v x * octHD d w y * (if y = x + h then sgn (qd d x + qd d y) else 0) =
      if v = w then sgn (bd d v h) else 0 := by
  have hx : ∀ x, ∑ y, octHD d v x * octHD d w y *
      (if y = x + h then sgn (qd d x + qd d y) else 0) =
      (64 : ℚ)⁻¹ * sgn (bd d w h) * sgn (bd d (v + w) x) := by
    intro x
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [octHD_apply, octHD_apply, qd_add, map_add (bd d w) x h, map_add (bd d) v w,
      LinearMap.add_apply]
    have e : bd d v x + qd d x + (bd d w x + bd d w h) + (qd d x + qd d h + bd d x h) +
        (qd d x + (qd d x + qd d h + bd d x h)) = bd d w h + (bd d v x + bd d w x) := by
      linear_combination (2 * qd d x + qd d h + bd d x h) * two_eq_zero'
    have e2 := congrArg sgn e
    simp only [sgn_add] at e2 ⊢
    linear_combination (64 : ℚ)⁻¹ * e2
  rw [Finset.sum_congr rfl fun x _ => hx x, ← Finset.mul_sum, sum_sgn_bd]
  by_cases hvw : v = w
  · rw [if_pos ((eq_iff_add_eq_zero_F2 v w).1 hvw), if_pos hvw, hvw]
    ring
  · rw [if_neg (fun h' => hvw ((eq_iff_add_eq_zero_F2 v w).2 h')), if_neg hvw,
      mul_zero]

theorem conj_one (d : OctadWord) (h v w : Octad.EvenQuot (octSupp d)) :
    ∑ x, ∑ y, octHD d v x * octHD d w y * (if y = x + h then 1 else 0) =
      if w = v + h then sgn (qd d v + qd d w) else 0 := by
  have hx : ∀ x, ∑ y, octHD d v x * octHD d w y * (if y = x + h then 1 else 0) =
      (64 : ℚ)⁻¹ * sgn (bd d w h + qd d h) * sgn (bd d (v + w + h) x) := by
    intro x
    simp only [mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [octHD_apply, octHD_apply, qd_add, map_add (bd d w) x h, map_add (bd d) (v + w) h,
      map_add (bd d) v w, LinearMap.add_apply, LinearMap.add_apply, bd_comm d h x]
    have e : bd d v x + qd d x + (bd d w x + bd d w h + (qd d x + qd d h + bd d x h)) =
        bd d w h + qd d h + (bd d v x + bd d w x + bd d x h) := by
      linear_combination (qd d x) * two_eq_zero'
    have e2 := congrArg sgn e
    simp only [sgn_add] at e2 ⊢
    linear_combination (64 : ℚ)⁻¹ * e2
  rw [Finset.sum_congr rfl fun x _ => hx x, ← Finset.mul_sum, sum_sgn_bd]
  by_cases hw : w = v + h
  · rw [if_pos (add_add_eq_zero_iff_F2.2 hw), if_pos hw]
    have e : bd d w h + qd d h = qd d v + qd d w := by
      rw [hw, qd_add, map_add (bd d) v h, LinearMap.add_apply, bd_self]
      linear_combination (-(qd d v)) * two_eq_zero'
    rw [e]
    ring
  · rw [if_neg (fun h' => hw (add_add_eq_zero_iff_F2.1 h')), if_neg hw, mul_zero]

theorem conj_two (d : OctadWord) (h v w : Octad.EvenQuot (octSupp d)) :
    ∑ x, ∑ y, octHD d v x * octHD d w y * (if x = y then sgn (bd d x h) else 0) =
      if w = v + h then 1 else 0 := by
  have hx : ∀ x, ∑ y, octHD d v x * octHD d w y * (if x = y then sgn (bd d x h) else 0) =
      (64 : ℚ)⁻¹ * sgn (bd d (v + w + h) x) := by
    intro x
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [octHD_apply, octHD_apply, map_add (bd d) (v + w) h, map_add (bd d) v w,
      LinearMap.add_apply, LinearMap.add_apply, bd_comm d h x]
    have e : bd d v x + qd d x + (bd d w x + qd d x) + bd d x h =
        bd d v x + bd d w x + bd d x h := by
      linear_combination (qd d x) * two_eq_zero'
    have e2 := congrArg sgn e
    simp only [sgn_add] at e2 ⊢
    linear_combination (64 : ℚ)⁻¹ * e2
  rw [Finset.sum_congr rfl fun x _ => hx x, ← Finset.mul_sum, sum_sgn_bd]
  by_cases hw : w = v + h
  · rw [if_pos (add_add_eq_zero_iff_F2.2 hw), if_pos hw]
    norm_num
  · rw [if_neg (fun h' => hw (add_add_eq_zero_iff_F2.1 h')), if_neg hw, mul_zero]

theorem twoCoef_conj (d : OctadWord) (h v w : Octad.EvenQuot (octSupp d)) (j : Fin 3) :
    ∑ x, ∑ y, octHD d v x * octHD d w y * twoCoef d h (j + 1) x y = twoCoef d h j v w := by
  fin_cases j
  · exact conj_zero d h v w
  · exact conj_one d h v w
  · exact conj_two d h v w

theorem T_tauB_oct_oct_pair (o o' : OctIdx) (p : LtPair) (j : Fin 3) :
    T (tauB (octVec o)) (tauB (octVec o')) (tauB (pairVec p j)) =
      T (octVec o) (octVec o') (pairVec p j) := by
  obtain ⟨d, v⟩ := o
  obtain ⟨d', w⟩ := o'
  rw [tauB_octVec, tauB_octVec, tauB_pairVec, T_sum_sum]
  by_cases hd : d = d'
  · subst hd
    by_cases hkl : p.1.1 ∈ octSupp d ∧ p.1.2 ∈ octSupp d
    · simp only [T_oct_oct_pair_in d _ _ p hkl.1 hkl.2]
      exact twoCoef_conj d _ v w j
    · simp only [T_oct_oct_pair_out d _ _ p hkl, mul_zero, Finset.sum_const_zero]
  · have hne : (⟨d, v⟩ : OctIdx).1 ≠ (⟨d', w⟩ : OctIdx).1 := hd
    rw [T_oct_oct_pair_cross hne]
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    rw [T_oct_oct_pair_cross (show (⟨d, x⟩ : OctIdx).1 ≠ (⟨d', y⟩ : OctIdx).1 from hd), mul_zero]

end OctadInv

open OctadInv

theorem triality_Griess_octad_two_coordinate_invariance :
    (∀ u ∈ octSpan, ∀ v ∈ octSpan, ∀ w ∈ pairSpan,
      T (tauB u) (tauB v) (tauB w) = T u v w ∧
        T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w) ∧
    (∀ (d : OctadWord) (p : LtPair), p.1.1 ∈ octSupp d → p.1.2 ∈ octSupp d →
      ∀ v w : Octad.EvenQuot (octSupp d),
        T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p 0) =
            octZ d (Octad.cls (octSupp d) {p.1.1, p.1.2}) v w ∧
        T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p 1) =
            (octD d * octP d (Octad.cls (octSupp d) {p.1.1, p.1.2}) * octD d) v w ∧
        T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p 2) =
            octP d (Octad.cls (octSupp d) {p.1.1, p.1.2}) v w) ∧
    (∀ o o' : OctIdx, o.1 ≠ o'.1 → ∀ (p : LtPair) (j : Fin 3),
      T (octVec o) (octVec o') (pairVec p j) = 0) ∧
    (∀ (d : OctadWord) (p : LtPair), ¬(p.1.1 ∈ octSupp d ∧ p.1.2 ∈ octSupp d) →
      ∀ (v w : Octad.EvenQuot (octSupp d)) (j : Fin 3),
        T (octVec ⟨d, v⟩) (octVec ⟨d, w⟩) (pairVec p j) = 0) := by
  have hT : ∀ u ∈ octSpan, ∀ v ∈ octSpan, ∀ w ∈ pairSpan,
      T (tauB u) (tauB v) (tauB w) = T u v w := by
    intro u hu v hv w hw
    refine T_comp_eq_of_span (tauB : SpaceB →ₗ[ℚ] SpaceB) ?_ hu hv hw
    rintro _ ⟨o, rfl⟩ _ ⟨o', rfl⟩ _ ⟨⟨p, j⟩, rfl⟩
    exact T_tauB_oct_oct_pair o o' p j
  refine ⟨fun u hu v hv w hw => ⟨hT u hu v hv w hw,
    T_tauB_symm_of_tauB (fun _ h => tauB_symm_mem_octSpan h) (fun _ h => tauB_symm_mem_octSpan h)
      (fun _ h => tauB_symm_mem_pairSpan h) hT hu hv hw⟩,
    fun d p hk hl v w => ?_, fun o o' hne p j => T_oct_oct_pair_cross hne p j,
    fun d p hout v w j => T_oct_oct_pair_out d v w p hout j⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [octZ_apply]
    exact T_oct_oct_pair_in d v w p hk hl 0
  · rw [octD_octP_octD_apply]
    exact T_oct_oct_pair_in d v w p hk hl 1
  · rw [octP_apply]
    exact T_oct_oct_pair_in d v w p hk hl 2

end VOA.Moonshine.MonsterGriess
