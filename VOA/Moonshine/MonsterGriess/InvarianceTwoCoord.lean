/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), files:
  CFSG/Monster/Spin/Pairing.lean (only `thetaD_ΩC`)
  CFSG/Monster/Griess/Invariance/TwoCoord/Triangle.lean
  CFSG/Monster/Griess/Invariance/TwoCoord/Values.lean
  CFSG/Monster/Griess/Invariance/TwoCoord.lean
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
import VOA.Moonshine.MonsterGriess.InvarianceDiagonal

/-!
# Axiom's Monster port: triality invariance on the two-coordinate sector `VABCD`

`VABCD` is the span of the triality basis vectors indexed by `Fin 24 ⊕ (LtPair × Fin 3)` (the
diagonal units and the pair triples).  The values of the trilinear form `T` on these basis
vectors are computed in closed form (`T_tbasis_twoIdx`, `twoCoordValue`; the pair-triangle
combinatorics is `IsPairTriangle`, `trace_basisA_mul3`, `deltaPair_eq_add_iff`), and they are
invariant under the index shift induced by `tauB` (`twoCoordValue_twoShift`).  Hence
`T (tauB u) (tauB v) (tauB w) = T u v w` for `u, v, w ∈ VABCD` (`T_tauB_of_mem_VABCD`).  Summary:
`triality_Griess_two_coordinate_sector_invariance`.

## Port notes
* Namespaces `CFSG.Monster.Griess`, `CFSG.Monster.Spin` ↦ `VOA.Moonshine.MonsterGriess`,
  `VOA.Moonshine.MonsterGriess.Spin` (as in the earlier ports).  Module-system syntax,
  `@[expose]` and the source's `attribute [-instance] …` lines dropped.  The three source files
  are concatenated; bodies verbatim except as listed.
* `Spin.thetaD_ΩC` (from `Spin/Pairing.lean`, not ported earlier) added verbatim.
* The private `TwoCoordInvariance.zmod2_cases` occurs in both `Triangle.lean` and `Values.lean`;
  in this single file it is declared once.
* Mathlib drift: `ite_eq_left h` ↦ `if_pos h`, `ite_eq_right h` ↦ `if_neg h`.
* Short names also declared elsewhere in `VOA/` in unrelated, unimported namespaces (no clash,
  not renamed): `pc`, `pc_zero`, `xv`.  `TwoCoordInvariance.inX_add` coexists with
  `inX_add` of `GriessGrading.lean`, as in the source.
-/

set_option linter.style.longLine false
set_option linter.style.show false

noncomputable section

/-! ### From `CFSG/Monster/Spin/Pairing.lean` -/

namespace VOA.Moonshine.MonsterGriess.Spin

open VOA.Moonshine.MonsterGriess.Code

theorem thetaD_ΩC : thetaD ΩC = 0 :=
  (thetaD_unique fun u => by rw [pair_zero_right, θ_ΩC_left]).symm

end VOA.Moonshine.MonsterGriess.Spin

/-! ### From `CFSG/Monster/Griess/Invariance/TwoCoord/Triangle.lean` -/

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin Matrix

abbrev ltEdge (p : LtPair) : Sym2 (Fin 24) := s(p.1.1, p.1.2)

def IsPairTriangle (p q r : LtPair) : Prop :=
  ∃ i j k : Fin 24, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    ltEdge p = s(i, j) ∧ ltEdge q = s(i, k) ∧ ltEdge r = s(j, k)

noncomputable instance (p q r : LtPair) : Decidable (IsPairTriangle p q r) := Classical.dec _

theorem IsPairTriangle.swap12 {p q r : LtPair} (h : IsPairTriangle p q r) :
    IsPairTriangle q p r := by
  obtain ⟨i, j, k, hij, hik, hjk, hp, hq, hr⟩ := h
  exact ⟨i, k, j, hik, hij, Ne.symm hjk, hq, hp, hr.trans Sym2.eq_swap⟩

theorem IsPairTriangle.cycle {p q r : LtPair} (h : IsPairTriangle p q r) :
    IsPairTriangle q r p := by
  obtain ⟨i, j, k, hij, hik, hjk, hp, hq, hr⟩ := h
  exact ⟨k, i, j, Ne.symm hik, Ne.symm hjk, hij, hq.trans Sym2.eq_swap, hr.trans Sym2.eq_swap, hp⟩

namespace TwoCoordInvariance

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem ltEdge_not_isDiag (p : LtPair) : ¬ (ltEdge p).IsDiag := by
  rw [Sym2.mk_isDiag_iff]
  exact p.2.ne

theorem ltEdge_injective : Function.Injective ltEdge := by
  intro p q h
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ltPair_eq h1 h2
  · have h3 : q.1.2 < q.1.1 := by
      rw [← h1, ← h2]
      exact p.2
    exact absurd q.2 (lt_asymm h3)

private theorem ind3 (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] :
    (if a then (1 : ℚ) else 0) * (if b then 1 else 0) * (if c then 1 else 0) =
      if a ∧ b ∧ c then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp [ha, hb, hc]

theorem walk_unique {p q : LtPair} {i j k : Fin 24} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hp : ltEdge p = s(i, j)) (hq : ltEdge q = s(i, k)) {a b c : Fin 24}
    (h1 : s(a, b) = ltEdge p) (h2 : s(b, c) = ltEdge q) : a = j ∧ b = i ∧ c = k := by
  rw [hp] at h1
  rw [hq] at h2
  have hb : b = i := by
    have hb1 : b = i ∨ b = j := Sym2.mem_iff.1 (h1 ▸ Sym2.mem_mk_right a b)
    have hb2 : b = i ∨ b = k := Sym2.mem_iff.1 (h2 ▸ Sym2.mem_mk_left b c)
    rcases hb1 with hb1 | hb1
    · exact hb1
    · rcases hb2 with hb2 | hb2
      · exact hb2
      · exact absurd (hb1.symm.trans hb2) hjk
  subst hb
  have ha : a = j := by
    rcases Sym2.eq_iff.1 h1 with ⟨h, h'⟩ | ⟨h, -⟩
    · exact absurd h' hij
    · exact h
  have hc : c = k := by
    rcases Sym2.eq_iff.1 h2 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hik
  exact ⟨ha, rfl, hc⟩

theorem isPairTriangle_of_walk {p q r : LtPair} {a b c : Fin 24} (h1 : s(a, b) = ltEdge p)
    (h2 : s(b, c) = ltEdge q) (h3 : s(c, a) = ltEdge r) : IsPairTriangle p q r := by
  have hab : a ≠ b := fun h => ltEdge_not_isDiag p (h1 ▸ Sym2.mk_isDiag_iff.2 h)
  have hbc : b ≠ c := fun h => ltEdge_not_isDiag q (h2 ▸ Sym2.mk_isDiag_iff.2 h)
  have hca : c ≠ a := fun h => ltEdge_not_isDiag r (h3 ▸ Sym2.mk_isDiag_iff.2 h)
  exact ⟨b, a, c, Ne.symm hab, hbc, Ne.symm hca, h1.symm.trans Sym2.eq_swap, h2.symm,
    h3.symm.trans Sym2.eq_swap⟩

theorem trace_basisA_mul3 (p q r : LtPair) :
    trace ((basisA (ltEdge p) : Matrix (Fin 24) (Fin 24) ℚ) *
      (basisA (ltEdge q) : Matrix (Fin 24) (Fin 24) ℚ) *
      (basisA (ltEdge r) : Matrix (Fin 24) (Fin 24) ℚ)) = if IsPairTriangle p q r then 1 else 0 := by
  have e : trace ((basisA (ltEdge p) : Matrix (Fin 24) (Fin 24) ℚ) *
      (basisA (ltEdge q) : Matrix (Fin 24) (Fin 24) ℚ) *
      (basisA (ltEdge r) : Matrix (Fin 24) (Fin 24) ℚ)) = ∑ a, ∑ c, ∑ b,
        if s(a, b) = ltEdge p ∧ s(b, c) = ltEdge q ∧ s(c, a) = ltEdge r then (1 : ℚ) else 0 := by
    simp only [trace, diag, mul_apply, basisA_apply, Finset.sum_mul, ind3]
  rw [e]
  by_cases h : IsPairTriangle p q r
  · rw [if_pos h]
    obtain ⟨i, j, k, hij, hik, hjk, hp, hq, hr⟩ := h
    have uniq := @walk_unique p q i j k hij hik hjk hp hq
    rw [Finset.sum_eq_single j, Finset.sum_eq_single k, Finset.sum_eq_single i]
    · rw [if_pos ⟨Sym2.eq_swap.trans hp.symm, hq.symm, Sym2.eq_swap.trans hr.symm⟩]
    · intro b _ hb
      exact if_neg fun h' => hb (uniq h'.1 h'.2.1).2.1
    · intro h'
      exact absurd (Finset.mem_univ _) h'
    · intro c _ hc
      refine Finset.sum_eq_zero fun b _ => if_neg fun h' => hc ?_
      exact (uniq h'.1 h'.2.1).2.2
    · intro h'
      exact absurd (Finset.mem_univ _) h'
    · intro a _ ha
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun b _ => if_neg fun h' => ?_
      exact ha (uniq h'.1 h'.2.1).1
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun b _ => if_neg fun h' => h ?_
    exact isPairTriangle_of_walk h'.1 h'.2.1 h'.2.2

def edgeVec (p : LtPair) : Fin 24 → ZMod 2 := Pi.single p.1.1 1 + Pi.single p.1.2 1

theorem edgeVec_apply (p : LtPair) (k : Fin 24) :
    edgeVec p k = if k ∈ ltEdge p then 1 else 0 := by
  have hne : p.1.1 ≠ p.1.2 := p.2.ne
  simp only [edgeVec, Pi.add_apply, Pi.single_apply, Sym2.mem_iff]
  by_cases h1 : k = p.1.1
  · have h2 : k ≠ p.1.2 := fun h2 => hne (h1.symm.trans h2)
    simp [h1, hne]
  · by_cases h2 : k = p.1.2
    · simp [h2, Ne.symm hne]
    · simp [h1, h2]

private theorem sum3_ind_zero (x y z : Prop) [Decidable x] [Decidable y] [Decidable z] :
    ((if x then (1 : ZMod 2) else 0) + (if y then 1 else 0) + (if z then 1 else 0) = 0) ↔
      ((x ↔ y) ↔ ¬ z) := by
  by_cases hx : x <;> by_cases hy : y <;> by_cases hz : z <;> simp only [hx, hy, hz] <;> decide

theorem isPairTriangle_of_forall {p q r : LtPair}
    (h : ∀ k, ((k ∈ ltEdge p ↔ k ∈ ltEdge q) ↔ k ∉ ltEdge r)) : IsPairTriangle p q r := by
  have hab : p.1.1 ≠ p.1.2 := p.2.ne
  have hpa : p.1.1 ∈ ltEdge p := Sym2.mem_mk_left _ _
  have hpb : p.1.2 ∈ ltEdge p := Sym2.mem_mk_right _ _
  have memp : ∀ k, k ∈ ltEdge p ↔ k = p.1.1 ∨ k = p.1.2 := fun k => Sym2.mem_iff
  have ha := h p.1.1
  have hb := h p.1.2
  simp only [hpa, hpb, true_iff] at ha hb
  by_cases haq : p.1.1 ∈ ltEdge q
  · have har : p.1.1 ∉ ltEdge r := ha.1 haq
    by_cases hbq : p.1.2 ∈ ltEdge q
    ·
      exfalso
      have hbr : p.1.2 ∉ ltEdge r := hb.1 hbq
      have hq : ltEdge q = s(p.1.1, p.1.2) := (Sym2.mem_and_mem_iff hab).1 ⟨haq, hbq⟩
      have hc : r.1.1 ∈ ltEdge r := Sym2.mem_mk_left _ _
      have hca : r.1.1 ≠ p.1.1 := fun e => har (e ▸ hc)
      have hcb : r.1.1 ≠ p.1.2 := fun e => hbr (e ▸ hc)
      have hcp : r.1.1 ∉ ltEdge p := fun e => ((memp _).1 e).elim hca hcb
      have hcq : r.1.1 ∉ ltEdge q := by
        rw [hq]
        exact hcp
      exact ((h r.1.1).1 (iff_of_false hcp hcq)) hc
    · have hbr : p.1.2 ∈ ltEdge r := by
        by_contra hbr
        exact hbq (hb.2 hbr)
      set c := Sym2.Mem.other haq with hc_def
      have hq : s(p.1.1, c) = ltEdge q := Sym2.other_spec haq
      have hcq : c ∈ ltEdge q := Sym2.other_mem haq
      have hca : c ≠ p.1.1 := Sym2.other_ne (ltEdge_not_isDiag q) haq
      have hcb : c ≠ p.1.2 := fun e => hbq (e ▸ hcq)
      have hcp : c ∉ ltEdge p := fun e => ((memp _).1 e).elim hca hcb
      have hcr : c ∈ ltEdge r := by
        by_contra hcr
        exact hcp (((h c).2 hcr).2 hcq)
      have hr : ltEdge r = s(p.1.2, c) := (Sym2.mem_and_mem_iff (Ne.symm hcb)).1 ⟨hbr, hcr⟩
      exact ⟨p.1.1, p.1.2, c, hab, Ne.symm hca, Ne.symm hcb, rfl, hq.symm, hr⟩
  · have har : p.1.1 ∈ ltEdge r := by
      by_contra har
      exact haq (ha.2 har)
    by_cases hbq : p.1.2 ∈ ltEdge q
    ·
      set c := Sym2.Mem.other hbq with hc_def
      have hq : s(p.1.2, c) = ltEdge q := Sym2.other_spec hbq
      have hcq : c ∈ ltEdge q := Sym2.other_mem hbq
      have hcb : c ≠ p.1.2 := Sym2.other_ne (ltEdge_not_isDiag q) hbq
      have hca : c ≠ p.1.1 := fun e => haq (e ▸ hcq)
      have hcp : c ∉ ltEdge p := fun e => ((memp _).1 e).elim hca hcb
      have hcr : c ∈ ltEdge r := by
        by_contra hcr
        exact hcp (((h c).2 hcr).2 hcq)
      have hr : ltEdge r = s(p.1.1, c) := (Sym2.mem_and_mem_iff (Ne.symm hca)).1 ⟨har, hcr⟩
      exact ⟨p.1.2, p.1.1, c, Ne.symm hab, Ne.symm hcb, Ne.symm hca, Sym2.eq_swap, hq.symm, hr⟩
    ·
      exfalso
      have hbr : p.1.2 ∈ ltEdge r := by
        by_contra hbr
        exact hbq (hb.2 hbr)
      have hr : ltEdge r = s(p.1.1, p.1.2) := (Sym2.mem_and_mem_iff hab).1 ⟨har, hbr⟩
      have hc : q.1.1 ∈ ltEdge q := Sym2.mem_mk_left _ _
      have hca : q.1.1 ≠ p.1.1 := fun e => haq (e ▸ hc)
      have hcb : q.1.1 ≠ p.1.2 := fun e => hbq (e ▸ hc)
      have hcp : q.1.1 ∉ ltEdge p := fun e => ((memp _).1 e).elim hca hcb
      have hcr : q.1.1 ∉ ltEdge r := by
        rw [hr]
        exact hcp
      exact (((h q.1.1).2 hcr).2 hc) |> hcp

theorem forall_of_isPairTriangle {p q r : LtPair} (h : IsPairTriangle p q r) (k : Fin 24) :
    ((k ∈ ltEdge p ↔ k ∈ ltEdge q) ↔ k ∉ ltEdge r) := by
  obtain ⟨i, j, l, hij, hil, hjl, hp, hq, hr⟩ := h
  rw [hp, hq, hr, Sym2.mem_iff, Sym2.mem_iff, Sym2.mem_iff]
  by_cases hi : k = i
  · subst hi
    simp [hij, hil]
  · by_cases hj : k = j
    · subst hj
      simp [hi, hjl]
    · by_cases hl : k = l
      · subst hl
        simp [hi, hj]
      · simp [hi, hj, hl]

theorem edgeVec_sum_eq_zero_iff (p q r : LtPair) :
    edgeVec p + edgeVec q + edgeVec r = 0 ↔ IsPairTriangle p q r := by
  constructor
  · intro h
    refine isPairTriangle_of_forall fun k => ?_
    have hk := congrFun h k
    simp only [Pi.add_apply, Pi.zero_apply, edgeVec_apply] at hk
    exact (sum3_ind_zero _ _ _).1 hk
  · intro h
    funext k
    simp only [Pi.add_apply, Pi.zero_apply, edgeVec_apply]
    exact (sum3_ind_zero _ _ _).2 (forall_of_isPairTriangle h k)

theorem hammingNorm_edgeVec_sum_le (p q r : LtPair) :
    hammingNorm (edgeVec p + edgeVec q + edgeVec r) ≤ 6 := by
  refine le_trans (Finset.card_le_card ?_)
    (Finset.card_le_six (a := p.1.1) (b := p.1.2) (c := q.1.1) (d := q.1.2) (e := r.1.1)
      (f := r.1.2))
  intro k hk
  rw [Finset.mem_filter] at hk
  by_contra hk'
  apply hk.2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hk'
  simp [edgeVec, h1, h2, h3, h4, h5, h6]

theorem edgeVec_sum_mem_C_iff (p q r : LtPair) :
    edgeVec p + edgeVec q + edgeVec r ∈ C ↔ edgeVec p + edgeVec q + edgeVec r = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ C.zero_mem⟩
  by_contra h0
  have := eight_le_wt h h0
  have := hammingNorm_edgeVec_sum_le p q r
  omega

theorem deltaPair_eq_mk (p : LtPair) :
    deltaPair p.1.1 p.1.2 = Submodule.Quotient.mk (edgeVec p) := rfl

private theorem zmod2_sub_eq_add : ∀ a b : ZMod 2, a - b = a + b := by decide

theorem deltaPair_eq_add_iff (p q r : LtPair) :
    deltaPair r.1.1 r.1.2 = deltaPair p.1.1 p.1.2 + deltaPair q.1.1 q.1.2 ↔
      IsPairTriangle p q r := by
  rw [deltaPair_eq_mk, deltaPair_eq_mk, deltaPair_eq_mk, ← Submodule.Quotient.mk_add,
    Submodule.Quotient.eq]
  have e : edgeVec r - (edgeVec p + edgeVec q) = edgeVec p + edgeVec q + edgeVec r := by
    funext k
    simp only [Pi.sub_apply, Pi.add_apply, zmod2_sub_eq_add]
    ring
  rw [e, edgeVec_sum_mem_C_iff, edgeVec_sum_eq_zero_iff]

theorem pair_ΩC_deltaPair (p : LtPair) : pair ΩC (deltaPair p.1.1 p.1.2) = 0 := by
  rw [deltaPair_eq_mk, pair_mk, edgeVec, dotProduct_add, dotProduct_single, dotProduct_single,
    coe_ΩC]
  simp only [Ω, mul_one]
  decide

end TwoCoordInvariance

end VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/Griess/Invariance/TwoCoord/Values.lean` -/

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin VOA.Moonshine.MonsterGriess.SpinLattice Matrix

namespace TwoCoordInvariance

open DiagonalInvariance

def pc (p : LtPair) (μ : ZMod 2) : ShortIdx :=
  if μ = 0 then labelIdx (.inl p) else labelIdx (.inr (.inl p))

theorem pc_zero (p : LtPair) : pc p 0 = labelIdx (.inl p) := if_pos rfl

theorem pc_one (p : LtPair) : pc p 1 = labelIdx (.inr (.inl p)) := if_neg (by decide)

theorem pc_fst (p : LtPair) (μ : ZMod 2) : (pc p μ).1 = (μ • ΩC, deltaPair p.1.1 p.1.2) := by
  rcases zmod2_cases μ with rfl | rfl
  · rw [pc_zero, zero_smul]
    exact coordOf_rMinus p.1.1 p.1.2
  · rw [pc_one, one_smul]
    refine (coordOf_rPlus p.1.1 p.1.2).trans ?_
    rw [thetaD_ΩC, zero_add]

theorem pc_inj {p q : LtPair} {μ ν : ZMod 2} : pc p μ = pc q ν ↔ p = q ∧ μ = ν := by
  constructor
  · intro h
    rcases zmod2_cases μ with rfl | rfl <;> rcases zmod2_cases ν with rfl | rfl <;>
      simp only [pc_zero, pc_one] at h <;> have h' := labelIdx_injective h <;> simp_all
  · rintro ⟨rfl, rfl⟩
    rfl

theorem pc_zero_ne_one (p q : LtPair) : pc p 0 ≠ pc q 1 := fun h =>
  absurd (pc_inj.1 h).2 (by decide)

theorem pc_one_ne_zero (p q : LtPair) : pc p 1 ≠ pc q 0 := fun h =>
  absurd (pc_inj.1 h).2 (by decide)

abbrev Ap (p : LtPair) : symMat := basisA (ltEdge p)

def xv (p : LtPair) (s : ℚ) : SpaceX := Pi.single (pc p 0) 1 + s • Pi.single (pc p 1) 1

theorem tbasis_pair_zero' (p : LtPair) : tbasis (.inr (.inl (p, 0))) = inA (Ap p) :=
  tbasis_pair_zero p

theorem tbasis_pair_one' (p : LtPair) : tbasis (.inr (.inl (p, 1))) = inX (xv p (-1)) := by
  have hXm : Xlift (rMinus p.1.1 p.1.2) = Pi.single (labelIdx (.inl p)) 1 :=
    Xlift_labelElt (.inl p)
  have hXp : Xlift (rPlus p.1.1 p.1.2) = Pi.single (labelIdx (.inr (.inl p))) 1 :=
    Xlift_labelElt (.inr (.inl p))
  rw [tbasis_pair_one, hXm, hXp, xv, pc_zero, pc_one, neg_one_smul, ← sub_eq_add_neg]

theorem tbasis_pair_two' (p : LtPair) : tbasis (.inr (.inl (p, 2))) = inX (xv p 1) := by
  have hXm : Xlift (rMinus p.1.1 p.1.2) = Pi.single (labelIdx (.inl p)) 1 :=
    Xlift_labelElt (.inl p)
  have hXp : Xlift (rPlus p.1.1 p.1.2) = Pi.single (labelIdx (.inr (.inl p))) 1 :=
    Xlift_labelElt (.inr (.inl p))
  rw [tbasis_pair_two, hXm, hXp, xv, pc_zero, pc_one, one_smul]

theorem inX_add (x y : SpaceX) : inX (x + y) = inX x + inX y :=
  Prod.ext (zero_add (0 : symMat)).symm (Prod.ext rfl (zero_add (0 : SpaceW)).symm)

theorem qf_add (c : ShortIdx) (M N : Matrix (Fin 24) (Fin 24) ℚ) :
    qf c (M + N) = qf c M + qf c N := by
  simp only [qf, add_mulVec, dotProduct_add]

theorem qf_Ap (c : ShortIdx) (p : LtPair) : qf c (Ap p) = 2 * (uQ c p.1.1 * uQ c p.1.2) := by
  rw [Ap, coe_basisA_ltPair, qf_add, qf_single, qf_single]
  ring

theorem vMinus_mul_vMinus {a b i j : Fin 24} (hab : a < b) (hij : i < j) :
    vMinus a b i * vMinus a b j = if i = a ∧ j = b then -16 else 0 := by
  rw [vMinus_apply, vMinus_apply]
  by_cases h1 : i = a
  · subst h1
    have hji : j ≠ i := (ne_of_lt hij).symm
    by_cases h2 : j = b
    · subst h2
      simp [hji, (ne_of_lt hab)]
    · simp [hji, h2]
  · by_cases h3 : i = b
    · subst h3
      have hja : j ≠ a := fun h => lt_asymm hab (h ▸ hij)
      have hjb : j ≠ i := (ne_of_lt hij).symm
      simp [h1, hja, hjb]
    · simp [h1, h3]

theorem vPlus_mul_vPlus {a b i j : Fin 24} (hab : a < b) (hij : i < j) :
    vPlus a b i * vPlus a b j = if i = a ∧ j = b then 16 else 0 := by
  rw [vPlus_apply, vPlus_apply]
  by_cases h1 : i = a
  · subst h1
    have hji : j ≠ i := (ne_of_lt hij).symm
    by_cases h2 : j = b
    · subst h2
      simp [hji, (ne_of_lt hab)]
    · simp [hji, h2]
  · by_cases h3 : i = b
    · subst h3
      have hja : j ≠ a := fun h => lt_asymm hab (h ▸ hij)
      have hjb : j ≠ i := (ne_of_lt hij).symm
      simp [h1, hja, hjb]
    · simp [h1, h3]

theorem ltPair_eq_iff (p q : LtPair) : (p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) ↔ p = q :=
  ⟨fun h => ltPair_eq h.1 h.2, fun h => h ▸ ⟨rfl, rfl⟩⟩

theorem qf_pc_zero_Ap (q p : LtPair) : qf (pc q 0) (Ap p) = if p = q then -32 else 0 := by
  rw [qf_Ap, pc_zero, uQ_mul_uQ_labelIdx]
  change 2 * ((vMinus q.1.1 q.1.2 p.1.1 * vMinus q.1.1 q.1.2 p.1.2 : ℤ) : ℚ) = _
  rw [vMinus_mul_vMinus q.2 p.2]
  by_cases h : p = q
  · rw [if_pos ((ltPair_eq_iff p q).2 h), if_pos h]
    norm_num
  · rw [if_neg (fun h' => h ((ltPair_eq_iff p q).1 h')), if_neg h]
    norm_num

theorem qf_pc_one_Ap (q p : LtPair) : qf (pc q 1) (Ap p) = if p = q then 32 else 0 := by
  rw [qf_Ap, pc_one, uQ_mul_uQ_labelIdx]
  change 2 * ((vPlus q.1.1 q.1.2 p.1.1 * vPlus q.1.1 q.1.2 p.1.2 : ℤ) : ℚ) = _
  rw [vPlus_mul_vPlus q.2 p.2]
  by_cases h : p = q
  · rw [if_pos ((ltPair_eq_iff p q).2 h), if_pos h]
    norm_num
  · rw [if_neg (fun h' => h ((ltPair_eq_iff p q).1 h')), if_neg h]
    norm_num

theorem T_inX_single3 (c₁ c₂ c₃ : ShortIdx) :
    T (inX (Pi.single c₁ 1)) (inX (Pi.single c₂ 1)) (inX (Pi.single c₃ 1)) = tau c₁ c₂ c₃ := by
  have h := sum3_single c₁ c₂ c₃ 1 1 1
  simp only [one_smul, one_mul] at h
  rw [T_XXX, h]

theorem T_inX_single2_inA (a b : ShortIdx) (A : symMat) :
    T (inX (Pi.single a 1)) (inX (Pi.single b 1)) (inA A) = if b = a then qf a A / 8 else 0 := by
  have h := sum_single_mul_single a b 1 1 (fun c => qf c A)
  simp only [one_smul, one_mul] at h
  rw [T_XXA, h]
  split_ifs <;> ring

theorem ΩC_ne_zero : ΩC ≠ 0 := fun h => by
  have h' := congrArg μ₀ h
  rw [μ₀_ΩC, map_zero] at h'
  exact absurd h' (by decide)

theorem tau_pc (p q r : LtPair) (μ₁ μ₂ μ₃ : ZMod 2) :
    tau (pc p μ₁) (pc q μ₂) (pc r μ₃) = if μ₃ = μ₁ + μ₂ ∧ IsPairTriangle p q r then 1 else 0 := by
  have hc : (pc r μ₃).1 = (pc p μ₁).1 + (pc q μ₂).1 ↔ μ₃ = μ₁ + μ₂ ∧ IsPairTriangle p q r := by
    rw [pc_fst, pc_fst, pc_fst, Prod.mk_add_mk, Prod.mk.injEq, ← add_smul,
      smul_left_inj ΩC_ne_zero, deltaPair_eq_add_iff]
  unfold tau
  by_cases h : μ₃ = μ₁ + μ₂ ∧ IsPairTriangle p q r
  · rw [if_pos (hc.2 h), if_pos h, pc_fst q μ₂, pc_fst p μ₁]
    change sgn (pair (μ₂ • ΩC) (deltaPair p.1.1 p.1.2)) = 1
    rw [pair_smul_left, pair_ΩC_deltaPair, mul_zero, sgn_zero]
  · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]

theorem tau_pc_of_eq (p q r : LtPair) {μ₁ μ₂ μ₃ : ZMod 2} (h : μ₃ = μ₁ + μ₂) :
    tau (pc p μ₁) (pc q μ₂) (pc r μ₃) = if IsPairTriangle p q r then 1 else 0 := by
  rw [tau_pc]
  by_cases ht : IsPairTriangle p q r
  · rw [if_pos ⟨h, ht⟩, if_pos ht]
  · rw [if_neg (fun h' => ht h'.2), if_neg ht]

theorem tau_pc_of_ne (p q r : LtPair) {μ₁ μ₂ μ₃ : ZMod 2} (h : μ₃ ≠ μ₁ + μ₂) :
    tau (pc p μ₁) (pc q μ₂) (pc r μ₃) = 0 := by
  rw [tau_pc, if_neg (fun h' => h h'.1)]

theorem T_Ap3 (p q r : LtPair) :
    T (inA (Ap p)) (inA (Ap q)) (inA (Ap r)) = if IsPairTriangle p q r then 4 else 0 := by
  rw [T_AAA, trace_basisA_mul3]
  split_ifs <;> ring

theorem T_xv2_Ap (p q r : LtPair) (s s' : ℚ) :
    T (inX (xv q s)) (inX (xv r s')) (inA (Ap p)) =
      if p = q ∧ q = r then 4 * (s * s' - 1) else 0 := by
  simp only [xv, inX_add, smul_inX, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    T_inX_single2_inA, smul_eq_mul]
  rw [if_neg (pc_zero_ne_one r q), if_neg (pc_one_ne_zero r q)]
  by_cases hrq : r = q
  · subst hrq
    rw [if_pos rfl, if_pos rfl, qf_pc_zero_Ap, qf_pc_one_Ap]
    by_cases hp : p = r
    · rw [if_pos hp, if_pos hp, if_pos ⟨hp, rfl⟩]
      ring
    · rw [if_neg hp, if_neg hp, if_neg (fun h => hp h.1)]
      ring
  · have h0 : ¬ pc r 0 = pc q 0 := fun h => hrq (pc_inj.1 h).1
    have h1 : ¬ pc r 1 = pc q 1 := fun h => hrq (pc_inj.1 h).1
    rw [if_neg h0, if_neg h1, if_neg (fun h => hrq (h.2.symm))]
    ring

theorem T_xv3 (p q r : LtPair) (s₁ s₂ s₃ : ℚ) :
    T (inX (xv p s₁)) (inX (xv q s₂)) (inX (xv r s₃)) =
      if IsPairTriangle p q r then 1 + s₁ * s₂ + s₁ * s₃ + s₂ * s₃ else 0 := by
  have t000 := tau_pc_of_eq p q r (μ₁ := 0) (μ₂ := 0) (μ₃ := 0) (by decide)
  have t001 := tau_pc_of_ne p q r (μ₁ := 0) (μ₂ := 0) (μ₃ := 1) (by decide)
  have t010 := tau_pc_of_ne p q r (μ₁ := 0) (μ₂ := 1) (μ₃ := 0) (by decide)
  have t011 := tau_pc_of_eq p q r (μ₁ := 0) (μ₂ := 1) (μ₃ := 1) (by decide)
  have t100 := tau_pc_of_ne p q r (μ₁ := 1) (μ₂ := 0) (μ₃ := 0) (by decide)
  have t101 := tau_pc_of_eq p q r (μ₁ := 1) (μ₂ := 0) (μ₃ := 1) (by decide)
  have t110 := tau_pc_of_eq p q r (μ₁ := 1) (μ₂ := 1) (μ₃ := 0) (by decide)
  have t111 := tau_pc_of_ne p q r (μ₁ := 1) (μ₂ := 1) (μ₃ := 1) (by decide)
  simp only [xv, inX_add, smul_inX, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    T_inX_single3, smul_eq_mul, t000, t001, t010, t011, t100, t101, t110, t111]
  split_ifs <;> ring

theorem T_inA_inX_inA (A A' : symMat) (x : SpaceX) : T (inA A) (inX x) (inA A') = 0 := by
  rw [T_swap23, T_AAX]

theorem T_inX_inA_inA (A A' : symMat) (x : SpaceX) : T (inX x) (inA A) (inA A') = 0 := by
  rw [T_cycle, T_AAX]

theorem T_Ap_xv2 (p q r : LtPair) (s s' : ℚ) :
    T (inA (Ap p)) (inX (xv q s)) (inX (xv r s')) =
      if p = q ∧ q = r then 4 * (s * s' - 1) else 0 := by
  rw [T_cycle, T_xv2_Ap]

theorem T_xv_Ap_xv (p q r : LtPair) (s s' : ℚ) :
    T (inX (xv p s)) (inA (Ap q)) (inX (xv r s')) =
      if p = q ∧ q = r then 4 * (s * s' - 1) else 0 := by
  rw [T_swap23, T_xv2_Ap]
  exact ite_cond_congr (propext ⟨fun h => ⟨h.1.symm, h.1.trans h.2⟩,
    fun h => ⟨h.1.symm, h.1.trans h.2⟩⟩)

theorem T_xv2_Ap' (p q r : LtPair) (s s' : ℚ) :
    T (inX (xv p s)) (inX (xv q s')) (inA (Ap r)) =
      if p = q ∧ q = r then 4 * (s * s' - 1) else 0 := by
  rw [T_xv2_Ap]
  refine ite_cond_congr (propext ⟨fun h => ⟨h.2, h.2.symm.trans h.1.symm⟩, fun h => ⟨?_, h.1⟩⟩)
  exact (h.1.trans h.2).symm

theorem T_diag_tbasis (k : Fin 24) (y z : TIdx) :
    T (tbasis (.inl k)) (tbasis y) (tbasis z) = diagEig k y * (if y = z then tnorm y else 0) := by
  have e : tbasis (.inl k) = inA (basisA s(k, k)) := tbasis_diag k
  calc T (tbasis (.inl k)) (tbasis y) (tbasis z) =
        bform (gmul (inA (basisA s(k, k))) (tbasis y)) (tbasis z) := by rw [e]; rfl
    _ = diagEig k y * (if y = z then tnorm y else 0) := by
        rw [gmul_Ekk_tbasis, map_smul, LinearMap.smul_apply, bform_tbasis, smul_eq_mul]

end TwoCoordInvariance

end VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/Griess/Invariance/TwoCoord.lean` -/

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin Matrix DiagonalInvariance TwoCoordInvariance

abbrev TwoIdx : Type := Fin 24 ⊕ (LtPair × Fin 3)

def twoIdx : TwoIdx → TIdx
  | .inl i => .inl i
  | .inr x => .inr (.inl x)

def VABCD : Submodule ℚ SpaceB :=
  Submodule.span ℚ (Set.range fun x : TwoIdx => tbasis (twoIdx x))

def diagPairVal (k : Fin 24) (p : LtPair) : ℚ :=
  4 * ((if p.1.1 = k then 1 else 0) + (if p.1.2 = k then 1 else 0))

def pairTripleVal (x y z : LtPair × Fin 3) : ℚ :=
  if x.1 = y.1 ∧ y.1 = z.1 ∧ x.2 ≠ y.2 ∧ y.2 ≠ z.2 ∧ x.2 ≠ z.2 then -8
  else if x.2 = y.2 ∧ y.2 = z.2 ∧ IsPairTriangle x.1 y.1 z.1 then 4 else 0

def twoCoordValue : TwoIdx → TwoIdx → TwoIdx → ℚ
  | .inl i, .inl j, .inl k => if i = j ∧ j = k then 4 else 0
  | .inl k, .inr x, .inr y => if x = y then diagPairVal k x.1 else 0
  | .inr x, .inl k, .inr y => if x = y then diagPairVal k x.1 else 0
  | .inr x, .inr y, .inl k => if x = y then diagPairVal k x.1 else 0
  | .inr x, .inr y, .inr z => pairTripleVal x y z
  | _, _, _ => 0

namespace TwoCoordInvariance

theorem T_diag_diag_diag (k i j : Fin 24) :
    T (tbasis (.inl k)) (tbasis (.inl i)) (tbasis (.inl j)) = if k = i ∧ i = j then 4 else 0 := by
  rw [T_diag_tbasis]
  simp only [diagEig, tnorm, Sum.inl.injEq]
  by_cases h1 : i = k
  · subst h1
    by_cases h2 : i = j
    · simp [h2]
    · simp [h2]
  · simp [h1, Ne.symm h1]

theorem T_diag_diag_pair (k i : Fin 24) (x : LtPair × Fin 3) :
    T (tbasis (.inl k)) (tbasis (.inl i)) (tbasis (.inr (.inl x))) = 0 := by
  rw [T_diag_tbasis, if_neg (by simp), mul_zero]

theorem T_diag_pair_diag (k : Fin 24) (x : LtPair × Fin 3) (j : Fin 24) :
    T (tbasis (.inl k)) (tbasis (.inr (.inl x))) (tbasis (.inl j)) = 0 := by
  rw [T_diag_tbasis, if_neg (by simp), mul_zero]

theorem T_diag_pair_pair (k : Fin 24) (x y : LtPair × Fin 3) :
    T (tbasis (.inl k)) (tbasis (.inr (.inl x))) (tbasis (.inr (.inl y))) =
      if x = y then diagPairVal k x.1 else 0 := by
  rw [T_diag_tbasis]
  obtain ⟨p, m⟩ := x
  by_cases h : (p, m) = y
  · rw [if_pos (by rw [h]), if_pos h]
    simp only [diagEig, tnorm, diagPairVal]
    ring
  · rw [if_neg (fun h' => h (by simpa using h')), if_neg h, mul_zero]

theorem tbasis_pair_eq (p : LtPair) (m : Fin 3) :
    tbasis (.inr (.inl (p, m))) = ![inA (Ap p), inX (xv p (-1)), inX (xv p 1)] m := by
  rcases m with ⟨_ | _ | _ | m, hm⟩
  · exact tbasis_pair_zero' p
  · exact tbasis_pair_one' p
  · exact tbasis_pair_two' p
  · omega

theorem T_tbasis_pair3 (x y z : LtPair × Fin 3) :
    T (tbasis (.inr (.inl x))) (tbasis (.inr (.inl y))) (tbasis (.inr (.inl z))) =
      pairTripleVal x y z := by
  obtain ⟨p, m⟩ := x
  obtain ⟨q, m'⟩ := y
  obtain ⟨r, m''⟩ := z
  rw [tbasis_pair_eq, tbasis_pair_eq, tbasis_pair_eq]
  fin_cases m <;> fin_cases m' <;> fin_cases m'' <;>
    simp [pairTripleVal, T_Ap3, T_AAX, T_inA_inX_inA, T_inX_inA_inA, T_Ap_xv2, T_xv_Ap_xv,
      T_xv2_Ap', T_xv3] <;> norm_num

end TwoCoordInvariance

theorem T_tbasis_twoIdx (x y z : TwoIdx) :
    T (tbasis (twoIdx x)) (tbasis (twoIdx y)) (tbasis (twoIdx z)) = twoCoordValue x y z := by
  rcases x with k | x <;> rcases y with i | y <;> rcases z with j | z
  · exact T_diag_diag_diag k i j
  · exact T_diag_diag_pair k i z
  · exact T_diag_pair_diag k y j
  · exact T_diag_pair_pair k y z
  · exact (T_swap12 _ _ _).trans (T_diag_pair_diag i x j)
  · exact (T_swap12 _ _ _).trans (T_diag_pair_pair i x z)
  · exact (T_cycle2 _ _ _).trans (T_diag_pair_pair j x y)
  · exact T_tbasis_pair3 x y z

theorem twoCoordValue_swap12 (x y z : TwoIdx) : twoCoordValue y x z = twoCoordValue x y z := by
  rw [← T_tbasis_twoIdx, ← T_tbasis_twoIdx, T_swap12]

theorem twoCoordValue_cycle (x y z : TwoIdx) : twoCoordValue y z x = twoCoordValue x y z := by
  rw [← T_tbasis_twoIdx, ← T_tbasis_twoIdx, ← T_cycle]

def twoShift : TwoIdx → TwoIdx
  | .inl i => .inl i
  | .inr (p, m) => .inr (p, m + 1)

theorem tauB_tbasis_twoIdx (x : TwoIdx) :
    tauB (tbasis (twoIdx x)) = tbasis (twoIdx (twoShift x)) := by
  rcases x with i | ⟨p, m⟩
  · exact tauB_diag i
  · exact tauB_pair p m

theorem twoShift_twoShift_twoShift (x : TwoIdx) : twoShift (twoShift (twoShift x)) = x := by
  rcases x with i | ⟨p, m⟩
  · rfl
  · simp only [twoShift, add_assoc]
    rw [show (1 + (1 + 1) : Fin 3) = 0 from rfl, add_zero]

theorem tauB_symm_tbasis_twoIdx (x : TwoIdx) :
    tauB.symm (tbasis (twoIdx x)) = tbasis (twoIdx (twoShift (twoShift x))) := by
  rw [LinearEquiv.symm_apply_eq, tauB_tbasis_twoIdx, twoShift_twoShift_twoShift]

theorem twoCoordValue_twoShift (x y z : TwoIdx) :
    twoCoordValue (twoShift x) (twoShift y) (twoShift z) = twoCoordValue x y z := by
  rcases x with i | ⟨p, m⟩ <;> rcases y with j | ⟨q, m'⟩ <;> rcases z with k | ⟨r, m''⟩ <;>
    simp [twoShift, twoCoordValue, pairTripleVal]

theorem tbasis_twoIdx_mem_VABCD (x : TwoIdx) : tbasis (twoIdx x) ∈ VABCD :=
  Submodule.subset_span ⟨x, rfl⟩

theorem tauB_mem_VABCD {u : SpaceB} (hu : u ∈ VABCD) : tauB u ∈ VABCD := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [tauB_tbasis_twoIdx]
    exact tbasis_twoIdx_mem_VABCD _
  | zero => rw [map_zero]; exact VABCD.zero_mem
  | add u u' _ _ h h' => rw [map_add]; exact VABCD.add_mem h h'
  | smul t u _ h => rw [map_smul]; exact VABCD.smul_mem t h

theorem tauB_symm_mem_VABCD {u : SpaceB} (hu : u ∈ VABCD) : tauB.symm u ∈ VABCD := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [tauB_symm_tbasis_twoIdx]
    exact tbasis_twoIdx_mem_VABCD _
  | zero => rw [map_zero]; exact VABCD.zero_mem
  | add u u' _ _ h h' => rw [map_add]; exact VABCD.add_mem h h'
  | smul t u _ h => rw [map_smul]; exact VABCD.smul_mem t h

theorem T_tauB_of_mem_VABCD {u v w : SpaceB} (hu : u ∈ VABCD) (hv : v ∈ VABCD)
    (hw : w ∈ VABCD) : T (tauB u) (tauB v) (tauB w) = T u v w := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      induction hw using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨c, rfl⟩ := hz
        rw [tauB_tbasis_twoIdx, tauB_tbasis_twoIdx, tauB_tbasis_twoIdx, T_tbasis_twoIdx,
          T_tbasis_twoIdx, twoCoordValue_twoShift]
      | zero => simp only [map_zero]
      | add w w' _ _ h h' => simp only [map_add, h, h']
      | smul t w _ h => simp only [map_smul, h]
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add v v' _ _ h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | smul t v _ h => simp only [map_smul, LinearMap.smul_apply, h]
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add u u' _ _ h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | smul t u _ h => simp only [map_smul, LinearMap.smul_apply, h]

theorem T_tauB_symm_of_mem_VABCD {u v w : SpaceB} (hu : u ∈ VABCD) (hv : v ∈ VABCD)
    (hw : w ∈ VABCD) : T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w := by
  have h := T_tauB_of_mem_VABCD (tauB_symm_mem_VABCD hu) (tauB_symm_mem_VABCD hv)
    (tauB_symm_mem_VABCD hw)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem triality_Griess_two_coordinate_sector_invariance :
    (∀ u v w : SpaceB, u ∈ VABCD → v ∈ VABCD → w ∈ VABCD →
      T (tauB u) (tauB v) (tauB w) = T u v w) ∧
    (∀ u v w : SpaceB, u ∈ VABCD → v ∈ VABCD → w ∈ VABCD →
      T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w) ∧
    (∀ u : SpaceB, u ∈ VABCD → tauB u ∈ VABCD ∧ tauB.symm u ∈ VABCD) ∧
    (∀ x y z : TwoIdx,
      T (tbasis (twoIdx x)) (tbasis (twoIdx y)) (tbasis (twoIdx z)) = twoCoordValue x y z) ∧
    (∀ x y z : TwoIdx, twoCoordValue y x z = twoCoordValue x y z ∧
      twoCoordValue y z x = twoCoordValue x y z) ∧
    (∀ i : Fin 24, T (tbasis (.inl i)) (tbasis (.inl i)) (tbasis (.inl i)) = 4) ∧
    (∀ (k : Fin 24) (p : LtPair) (m : Fin 3),
      T (tbasis (.inl k)) (tbasis (.inr (.inl (p, m)))) (tbasis (.inr (.inl (p, m)))) =
        4 * ((if p.1.1 = k then 1 else 0) + (if p.1.2 = k then 1 else 0))) ∧
    (∀ p : LtPair,
      T (tbasis (.inr (.inl (p, 0)))) (tbasis (.inr (.inl (p, 1)))) (tbasis (.inr (.inl (p, 2)))) =
        -8) ∧
    (∀ (p q r : LtPair) (m : Fin 3), IsPairTriangle p q r →
      T (tbasis (.inr (.inl (p, m)))) (tbasis (.inr (.inl (q, m)))) (tbasis (.inr (.inl (r, m)))) =
        4) := by
  refine ⟨fun _ _ _ hu hv hw => T_tauB_of_mem_VABCD hu hv hw,
    fun _ _ _ hu hv hw => T_tauB_symm_of_mem_VABCD hu hv hw,
    fun _ hu => ⟨tauB_mem_VABCD hu, tauB_symm_mem_VABCD hu⟩, T_tbasis_twoIdx,
    fun x y z => ⟨twoCoordValue_swap12 x y z, twoCoordValue_cycle x y z⟩, fun i => ?_,
    fun k p m => ?_, fun p => ?_, fun p q r m h => ?_⟩
  · rw [T_diag_diag_diag, if_pos ⟨rfl, rfl⟩]
  · rw [T_diag_pair_pair, if_pos rfl]
    rfl
  · rw [T_tbasis_pair3, pairTripleVal, if_pos ⟨rfl, rfl, (by decide : (0 : Fin 3) ≠ 1),
      (by decide : (1 : Fin 3) ≠ 2), (by decide : (0 : Fin 3) ≠ 2)⟩]
  · have hne : ¬ (p = q ∧ q = r ∧ m ≠ m ∧ m ≠ m ∧ m ≠ m) := fun h' => h'.2.2.1 rfl
    rw [T_tbasis_pair3, pairTripleVal, if_neg hne, if_pos ⟨rfl, rfl, h⟩]

end VOA.Moonshine.MonsterGriess
