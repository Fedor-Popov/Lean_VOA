/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoAMProof

/-!
# A finite Virasoro-coordinate reifier for the lattice triplet `W(2)`

This file is an independent consumer of the negative-mode recursion proved in
`TripletWpTwoAMProof`.  It supplies the other input needed to turn the twelve weight-ten
Virasoro words in the Adamovic--Milas certificate into finite polynomial identities:

* the exact vacuum formula for every negative background-charge Virasoro mode; and
* a small syntax of polynomials in the invariant rank-one coordinates
  `A_i = vVar (alphaP 2) i`, together with a proved evaluator for negative Virasoro modes.

Thus evaluating a Virasoro word is computation on a finite list.  No PBW principle, quotient,
or coordinate identity is assumed here.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.WpTwoVirasoroCoords

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp
open VOA.LatGen.WpC2

private noncomputable abbrev Ltwo : IntegralLattice := latP 2
private abbrev alphaTwo : Ltwo.carrier := alphaP 2
private noncomputable abbrev ATwo (i : ℕ) : FockN (rank Ltwo) := vVar Ltwo alphaTwo i
private noncomputable def aTwo : Fin (rank Ltwo) := ⟨0, by rw [rank_latP]; norm_num⟩

/-! ## The negative-mode vacuum formula -/

/-- Two negative rank-one orthonormal oscillators, expressed in the invariant lattice-direction
coordinates.  The factor `1/4` is `1 / <alpha,alpha>` at `p = 2`. -/
theorem oscN_pair_neg_vacuum_eq_ATwo (i j : ℕ) :
    oscN (rank Ltwo) 1 aTwo (-((i : ℤ) + 1))
        (oscN (rank Ltwo) 1 aTwo (-((j : ℤ) + 1)) (vacuumN (rank Ltwo)))
      = (1 / 4 : ℂ) • (ATwo i * ATwo j) := by
  letI : Unique (Fin (rank Ltwo)) :=
    { default := aTwo
      uniq := fun a => Fin.ext (by
        have ha : a.val < 1 := by
          rw [← rank_latP 2]
          exact a.isLt
        change a.val = 0
        omega) }
  have hc := sum_chargeCoord Ltwo (latP_posDef 2 (by norm_num)) alphaTwo alphaTwo
  rw [Fintype.sum_unique, latP_form_alpha] at hc
  norm_num at hc
  have hc' : chargeCoord Ltwo alphaTwo aTwo * chargeCoord Ltwo alphaTwo aTwo = 4 := by
    simpa using hc
  rw [oscN_apply_neg (rank Ltwo) 1 aTwo (by omega),
    oscN_apply_neg (rank Ltwo) 1 aTwo (by omega), vacuumN, mul_one,
    ATwo, ATwo, vVar, vVar, Fintype.sum_unique]
  norm_num
  have hdefault : (default : Fin (rank Ltwo)) = aTwo := Subsingleton.elim _ _
  simp only [hdefault]
  simp only [MvPolynomial.smul_eq_C_mul]
  ring_nf
  rw [show MvPolynomial.C (chargeCoord Ltwo alphaTwo aTwo) ^ 2 =
      MvPolynomial.C (4 : ℂ) by
    rw [← map_pow]
    congr 1
    simpa [pow_two] using hc']
  have hquarter :
      (MvPolynomial.C (1 / 4 : ℂ) : FockN (rank Ltwo)) * MvPolynomial.C 4 = 1 := by
    rw [← map_mul]
    norm_num
  calc
    MvPolynomial.X (i, aTwo) * MvPolynomial.X (j, aTwo) =
        MvPolynomial.X (i, aTwo) * MvPolynomial.X (j, aTwo) *
          (MvPolynomial.C (1 / 4 : ℂ) * MvPolynomial.C 4) := by rw [hquarter, mul_one]
    _ = MvPolynomial.X (i, aTwo) * MvPolynomial.X (j, aTwo) *
          MvPolynomial.C (1 / 4 : ℂ) * MvPolynomial.C 4 := by ring

/-- A Sugawara summand on the vacuum is nonzero only in the finite creation--creation window. -/
theorem sugTermN_neg_vacuum_support (n : ℕ) (j : ℤ) :
    sugTermN (rank Ltwo) 1 aTwo (-(n : ℤ)) j (vacuumN (rank Ltwo)) ≠ 0 →
      -(n : ℤ) < j ∧ j < 0 := by
  intro hj
  have hjneg : j < 0 := by
    by_contra h
    rw [sugTermN_apply, if_neg (by omega),
      oscN_vacuum (rank Ltwo) 1 aTwo j (by omega), map_zero] at hj
    exact hj rfl
  refine ⟨?_, hjneg⟩
  by_contra h
  rw [sugTermN_apply, if_pos hjneg,
    oscN_vacuum (rank Ltwo) 1 aTwo (-(n : ℤ) - j) (by omega), map_zero] at hj
  exact hj rfl

/-- Evaluation of one term in the finite creation--creation window. -/
theorem sugTermN_neg_vacuum_window (n i : ℕ) (hi : i < n - 1) :
    sugTermN (rank Ltwo) 1 aTwo (-(n : ℤ)) (-((i : ℤ) + 1))
        (vacuumN (rank Ltwo))
      = (1 / 4 : ℂ) • (ATwo i * ATwo (n - 2 - i)) := by
  rw [sugTermN_apply, if_pos (by omega)]
  have hidx : -(n : ℤ) - -((i : ℤ) + 1) = -(((n - 2 - i : ℕ) : ℤ) + 1) := by
    omega
  rw [hidx, oscN_pair_neg_vacuum_eq_ATwo]

/-- The pure Sugawara contribution to `L_{-n}|0>` in invariant rank-one coordinates. -/
theorem LvirN_neg_vacuum_eq_ATwo_sum (n : ℕ) (hn : 1 ≤ n) :
    LvirN (rank Ltwo) 1 (-(n : ℤ)) (vacuumN (rank Ltwo))
      = (1 / 8 : ℂ) • ∑ i ∈ Finset.range (n - 1), ATwo i * ATwo (n - 2 - i) := by
  classical
  letI : Unique (Fin (rank Ltwo)) :=
    { default := aTwo
      uniq := fun a => Fin.ext (by
        have ha : a.val < 1 := by
          rw [← rank_latP 2]
          exact a.isLt
        change a.val = 0
        omega) }
  let emb : ℕ ↪ ℤ :=
    ⟨fun i => -((i : ℤ) + 1), by
      intro a b hab
      push_cast at hab
      omega⟩
  have hsupp : Function.support (fun j : ℤ =>
      sugTermN (rank Ltwo) 1 aTwo (-(n : ℤ)) j (vacuumN (rank Ltwo))) ⊆
        (Finset.range (n - 1)).map emb := by
    intro j hj
    rw [Function.mem_support] at hj
    obtain ⟨hlo, hhi⟩ := sugTermN_neg_vacuum_support n j hj
    change j ∈ (Finset.range (n - 1)).map emb
    rw [Finset.mem_map]
    refine ⟨(-j - 1).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · change -((((-j - 1).toNat : ℕ) : ℤ) + 1) = j
      omega
  rw [LvirN_apply, Fintype.sum_unique]
  have hdefault : (default : Fin (rank Ltwo)) = aTwo := Subsingleton.elim _ _
  rw [hdefault, LvirNa_apply']
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp, Finset.sum_map]
  have hterms :
      (∑ i ∈ Finset.range (n - 1),
          sugTermN (rank Ltwo) 1 aTwo (-(n : ℤ)) (emb i) (vacuumN (rank Ltwo)))
        = ∑ i ∈ Finset.range (n - 1), (1 / 4 : ℂ) •
            (ATwo i * ATwo (n - 2 - i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simpa [emb] using sugTermN_neg_vacuum_window n i hi
  rw [hterms, ← Finset.smul_sum]
  norm_num
  module

/-- The background oscillator contribution to `L^lambda_{-n}|0>`. -/
theorem bgOsc_lamP_two_neg_vacuum (n : ℕ) (hn : 1 ≤ n) :
    BgA.bgOsc Ltwo (lamP 2) (-(n : ℤ)) (vacuumN (rank Ltwo))
      = (1 / 4 : ℂ) • ATwo (n - 1) := by
  rw [lamP, WpTwoAMCoords.bgOsc_latBg_apply,
    show -(n : ℤ) = -(((n - 1 : ℕ) : ℤ) + 1) by omega,
    WpTwoAMCoords.chargeOsc_neg_vacuum_eq_vVar, cP]
  norm_num

/-- **Closed negative-mode vacuum formula.**  For `n >= 1`,

`L^lambda_{-n}|0> = 1/8 sum_{i<n-1} A_i A_{n-2-i} + (n-1)/4 A_{n-1}`.

The case `n=1` says that translation kills the vacuum. -/
theorem LSecBg_neg_vacuum_eq_ATwo (n : ℕ) (hn : 1 ≤ n) :
    BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ)) (vacuumN (rank Ltwo))
      = (1 / 8 : ℂ) • ∑ i ∈ Finset.range (n - 1), ATwo i * ATwo (n - 2 - i)
        + (((n - 1 : ℕ) : ℂ) / 4) • ATwo (n - 1) := by
  rw [WpTwoAMProof.LSecBg_zero_eq, LinearMap.sub_apply, LinearMap.smul_apply,
    LvirN_neg_vacuum_eq_ATwo_sum n hn, bgOsc_lamP_two_neg_vacuum n hn]
  push_cast [Nat.cast_sub hn]
  module

/-- Cross-check against the independent translation-descendant construction in `AMProof`.
Both formulas are proved from the repository operators and hence agree without a coordinate
assumption. -/
theorem ATwo_vacuum_sum_eq_translation (hp : 1 ≤ 2) (n : ℕ) (hn : 2 ≤ n) :
    (1 / 8 : ℂ) • ∑ i ∈ Finset.range (n - 1), ATwo i * ATwo (n - 2 - i)
        + (((n - 1 : ℕ) : ℂ) / 4) • ATwo (n - 1)
      = (((n - 2).factorial : ℂ)⁻¹) •
          ((BgA.LSecBg Ltwo (lamP 2) 0 (-1) ^ (n - 2))
            ((1 / 8 : ℂ) • ATwo 0 ^ 2 + (1 / 4 : ℂ) • ATwo 1)) := by
  rw [← LSecBg_neg_vacuum_eq_ATwo n (by omega),
    WpTwoAMProof.LSecBg_neg_vacuum hp n hn]

/-! ## A finite polynomial syntax and proved Virasoro evaluator -/

/-- A word `[i_1,...,i_r]` denotes `A_{i_1} ... A_{i_r}`. -/
noncomputable def evalAWord : List ℕ → FockN (rank Ltwo)
  | [] => vacuumN (rank Ltwo)
  | i :: is => ATwo i * evalAWord is

/-- A finite polynomial is represented by a list of coefficient/word pairs. -/
abbrev APolyTwo := List (ℂ × List ℕ)

/-- Evaluation of the finite coordinate syntax in the actual Fock polynomial ring. -/
noncomputable def evalAPoly (P : APolyTwo) : FockN (rank Ltwo) :=
  (P.map fun t => t.1 • evalAWord t.2).sum

/-- Prefix every monomial by one coordinate `A_i`. -/
def prependA (i : ℕ) (P : APolyTwo) : APolyTwo :=
  P.map fun t => (t.1, i :: t.2)

/-- Multiply every coefficient by `c`. -/
def scaleAPoly (c : ℂ) (P : APolyTwo) : APolyTwo :=
  P.map fun t => (c * t.1, t.2)

@[simp] theorem evalAPoly_nil : evalAPoly [] = 0 := by simp [evalAPoly]

@[simp] theorem evalAPoly_append (P Q : APolyTwo) :
    evalAPoly (P ++ Q) = evalAPoly P + evalAPoly Q := by
  simp [evalAPoly, List.map_append, List.sum_append]

@[simp] theorem evalAPoly_singleton (c : ℂ) (w : List ℕ) :
    evalAPoly [(c, w)] = c • evalAWord w := by simp [evalAPoly]

theorem eval_prependA (i : ℕ) (P : APolyTwo) :
    evalAPoly (prependA i P) = ATwo i * evalAPoly P := by
  induction P with
  | nil => simp [prependA]
  | cons t P ih =>
      rcases t with ⟨c, w⟩
      change c • evalAWord (i :: w) + evalAPoly (prependA i P) =
        ATwo i * (c • evalAWord w + evalAPoly P)
      rw [evalAWord, ih, mul_add, mul_smul_comm]

theorem eval_scaleAPoly (c : ℂ) (P : APolyTwo) :
    evalAPoly (scaleAPoly c P) = c • evalAPoly P := by
  induction P with
  | nil => simp [scaleAPoly]
  | cons t P ih =>
      rcases t with ⟨d, w⟩
      change (c * d) • evalAWord w + evalAPoly (scaleAPoly c P) =
        c • (d • evalAWord w + evalAPoly P)
      rw [ih, smul_add, smul_smul]

/-- The syntax of the closed negative-mode vacuum formula. -/
noncomputable def virVacAPoly (n : ℕ) : APolyTwo :=
  ((List.range (n - 1)).map fun i => ((1 / 8 : ℂ), [i, n - 2 - i]))
    ++ [((((n - 1 : ℕ) : ℂ) / 4), [n - 1])]

theorem eval_virVacAPoly (n : ℕ) :
    evalAPoly (virVacAPoly n) =
      (1 / 8 : ℂ) • ∑ i ∈ Finset.range (n - 1), ATwo i * ATwo (n - 2 - i)
        + (((n - 1 : ℕ) : ℂ) / 4) • ATwo (n - 1) := by
  rw [virVacAPoly, evalAPoly_append, evalAPoly_singleton]
  simp only [evalAWord]
  have hsum :
      evalAPoly ((List.range (n - 1)).map fun i => ((1 / 8 : ℂ), [i, n - 2 - i]))
        = (1 / 8 : ℂ) • ∑ i ∈ Finset.range (n - 1), ATwo i * ATwo (n - 2 - i) := by
    rw [evalAPoly, List.map_map]
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [evalAWord, vacuumN]
  rw [hsum]
  simp [vacuumN]

/-- Syntactic action of `L^lambda_{-n}` on one coordinate word. -/
noncomputable def virActWord (n : ℕ) : List ℕ → APolyTwo
  | [] => virVacAPoly n
  | i :: is => prependA i (virActWord n is) ++ [(((i : ℂ) + 1), (i + n) :: is)]

/-- Syntactic action on a finite linear combination. -/
noncomputable def virActPoly (n : ℕ) (P : APolyTwo) : APolyTwo :=
  P.flatMap fun t => scaleAPoly t.1 (virActWord n t.2)

/-- Correctness of the word evaluator.  The inductive step is exactly the independently proved
negative Virasoro--Heisenberg recurrence. -/
theorem eval_virActWord (n : ℕ) (hn : 1 ≤ n) (w : List ℕ) :
    evalAPoly (virActWord n w) =
      BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ)) (evalAWord w) := by
  induction w with
  | nil =>
      rw [virActWord, eval_virVacAPoly, evalAWord]
      exact (LSecBg_neg_vacuum_eq_ATwo n hn).symm
  | cons i is ih =>
      rw [virActWord, evalAPoly_append, eval_prependA, ih, evalAPoly_singleton, evalAWord]
      exact (WpTwoAMProof.LSecBg_neg_mul_ATwo n hn i (evalAWord is)).symm

/-- Correctness of the polynomial evaluator. -/
theorem eval_virActPoly (n : ℕ) (hn : 1 ≤ n) (P : APolyTwo) :
    evalAPoly (virActPoly n P) =
      BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ)) (evalAPoly P) := by
  induction P with
  | nil => simp [virActPoly, map_zero]
  | cons t P ih =>
      rcases t with ⟨c, w⟩
      change evalAPoly (scaleAPoly c (virActWord n w) ++ virActPoly n P) =
        BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ))
          (c • evalAWord w + evalAPoly P)
      rw [evalAPoly_append, eval_scaleAPoly, eval_virActWord n hn w, ih, map_add, map_smul]

/-- Recursively reify a positive Virasoro word. -/
noncomputable def reifyVirWord : List ℕ → APolyTwo
  | [] => [(1, [])]
  | n :: ns => virActPoly n (reifyVirWord ns)

/-- The Fock-space recursion mirrored by `reifyVirWord`. -/
noncomputable def virWordFockTwo : List ℕ → FockN (rank Ltwo)
  | [] => vacuumN (rank Ltwo)
  | n :: ns => BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ)) (virWordFockTwo ns)

/-- Evaluation of a positive-mode syntax word is the actual recursively applied Virasoro word. -/
theorem eval_reifyVirWord (ns : List ℕ) (hpos : ∀ n ∈ ns, 1 ≤ n) :
    evalAPoly (reifyVirWord ns) = virWordFockTwo ns := by
  induction ns with
  | nil => simp [reifyVirWord, evalAPoly, evalAWord, virWordFockTwo]
  | cons n ns ih =>
      rw [reifyVirWord, virWordFockTwo, eval_virActPoly n (hpos n (by simp))]
      exact congrArg _ (ih fun m hm => hpos m (by simp [hm]))

/-- The recursive Fock word is the neutral-sector realization of the ambient Virasoro word. -/
theorem virWordTwo_eq_fock (hp : 1 ≤ 2) : ∀ ns : List ℕ,
    virWordTwo hp ns = latStateGen Ltwo (virWordFockTwo ns) 0
  | [] => rfl
  | n :: ns => by
      rw [virWordTwo_cons, virWordFockTwo, virWordTwo_eq_fock hp ns,
        tripletLatticeVOA_L]
      change BgA.LBg Ltwo (lamP 2) (-(n : ℤ))
          (mkEα Ltwo 0 (virWordFockTwo ns)) =
        mkEα Ltwo 0
          (BgA.LSecBg Ltwo (lamP 2) 0 (-(n : ℤ)) (virWordFockTwo ns))
      rw [BgA.LBg_mkEα Ltwo (latP_posDef 2 hp)]

/-- The finite reifier computes the ambient Virasoro word used by the AM certificate. -/
theorem virWordTwo_eq_reified (hp : 1 ≤ 2) (ns : List ℕ) (hpos : ∀ n ∈ ns, 1 ≤ n) :
    virWordTwo hp ns = latStateGen Ltwo (evalAPoly (reifyVirWord ns)) 0 := by
  rw [eval_reifyVirWord ns hpos]
  exact virWordTwo_eq_fock hp ns

/-! ### The twelve words in the AM certificate -/

/-- The eleven deep Virasoro words, as one finite coordinate syntax value. -/
noncomputable def amTwoRemainderAPoly : APolyTwo :=
    scaleAPoly (128 / 35 : ℂ) (reifyVirWord [10])
  ++ scaleAPoly (-27232 / 525 : ℂ) (reifyVirWord [8, 2])
  ++ scaleAPoly (-12308 / 525 : ℂ) (reifyVirWord [7, 3])
  ++ scaleAPoly (20896 / 525 : ℂ) (reifyVirWord [6, 4])
  ++ scaleAPoly (-106816 / 1575 : ℂ) (reifyVirWord [6, 2, 2])
  ++ scaleAPoly (18544 / 1575 : ℂ) (reifyVirWord [5, 5])
  ++ scaleAPoly (-59392 / 1575 : ℂ) (reifyVirWord [5, 3, 2])
  ++ scaleAPoly (-752 / 525 : ℂ) (reifyVirWord [4, 4, 2])
  ++ scaleAPoly (1688 / 525 : ℂ) (reifyVirWord [4, 3, 3])
  ++ scaleAPoly (-512 / 63 : ℂ) (reifyVirWord [4, 2, 2, 2])
  ++ scaleAPoly (832 / 315 : ℂ) (reifyVirWord [3, 3, 2, 2])

/-- All eleven deep words in `amTwoRemainder` are evaluated by the finite reifier. -/
theorem amTwoRemainder_eq_reified (hp : 1 ≤ 2) :
    amTwoRemainder hp = latStateGen Ltwo (evalAPoly amTwoRemainderAPoly) 0 := by
  rw [amTwoRemainder,
    virWordTwo_eq_reified hp [10] (by norm_num),
    virWordTwo_eq_reified hp [8, 2] (by norm_num),
    virWordTwo_eq_reified hp [7, 3] (by norm_num),
    virWordTwo_eq_reified hp [6, 4] (by norm_num),
    virWordTwo_eq_reified hp [6, 2, 2] (by norm_num),
    virWordTwo_eq_reified hp [5, 5] (by norm_num),
    virWordTwo_eq_reified hp [5, 3, 2] (by norm_num),
    virWordTwo_eq_reified hp [4, 4, 2] (by norm_num),
    virWordTwo_eq_reified hp [4, 3, 3] (by norm_num),
    virWordTwo_eq_reified hp [4, 2, 2, 2] (by norm_num),
    virWordTwo_eq_reified hp [3, 3, 2, 2] (by norm_num),
    amTwoRemainderAPoly]
  simp only [evalAPoly_append, eval_scaleAPoly, latStateGen_add_boson,
    latStateGen_smul_boson]

/-- The exceptional twelfth word `L(-2)^5|0>` is evaluated by the same reifier. -/
theorem omegaPowAmb_five_eq_reified (hp : 1 ≤ 2) :
    omegaPowAmb 2 hp 5 =
      latStateGen Ltwo (evalAPoly (reifyVirWord [2, 2, 2, 2, 2])) 0 := by
  rw [← virWordTwo_two_pow_five hp,
    virWordTwo_eq_reified hp [2, 2, 2, 2, 2] (by norm_num)]

end VOA.LatGen.WpTwoVirasoroCoords

section AxiomAudit
#print axioms VOA.LatGen.WpTwoVirasoroCoords.LSecBg_neg_vacuum_eq_ATwo
#print axioms VOA.LatGen.WpTwoVirasoroCoords.eval_virActPoly
#print axioms VOA.LatGen.WpTwoVirasoroCoords.virWordTwo_eq_reified
#print axioms VOA.LatGen.WpTwoVirasoroCoords.amTwoRemainder_eq_reified
end AxiomAudit
