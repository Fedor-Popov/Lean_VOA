/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpSimplicity
import VOA.Examples.TripletWpTwoAMSparseBridge
import VOA.Examples.TripletWpTwoZhuSparseCompute
import VOA.Examples.TripletWpZhuScreening

/-!
# Sparse semantics for the lattice W(2) Zhu certificate

The executable current recurrence uses *formal-distribution coefficient indices*, while Zhu's
formulas use VOA mode indices.  This file makes the conversion explicit:

`u₍n₎v = (Y(u))_{-n-1} v`.

In particular, a Zhu circle mode `n=i-2` is evaluated at coefficient `1-i`, and the three modes
`-1,0,1` in left Zhu multiplication by `ω` are evaluated at coefficients `0,-1,-2`.
Keeping this conversion in `zhuModeActSparseQ` prevents the two index conventions from being
silently interchanged in an executable certificate.
-/

namespace VOA.LatGen.WpTwoZhuSparseSemantics

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.SparseRational
open VOA.LatGen VOA.LatGen.Triplet VOA.LatGen.Wp
open VOA.LatGen.WpC2 VOA.LatGen.WpTwoAMClose
open VOA.LatGen.WpTwoAMAssembly
open VOA.LatGen.WpTwoVirasoroCoords
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoAMSparseBridge
open VOA.LatGen.WpTwoZhuSparseCompute

private noncomputable abbrev Ltwo : IntegralLattice := latP 2

/-- Public evaluation of canonical rational sparse polynomials in the rank-one invariant
coordinates. -/
noncomputable def evalZhuSparseQ (P : SparseRational.Poly ℕ) : FockN (rank Ltwo) :=
  evalSparse sparseATwo P

@[simp] theorem evalZhuSparseQ_nil : evalZhuSparseQ [] = 0 := by
  simp [evalZhuSparseQ, evalSparse]

theorem evalZhuSparseQ_addQ (P Q : SparseRational.Poly ℕ) :
    evalZhuSparseQ (addQ P Q) = evalZhuSparseQ P + evalZhuSparseQ Q := by
  simpa only [evalZhuSparseQ] using evalSparse_addQ sparseATwo P Q

theorem evalZhuSparseQ_scaleQ (q : ℚ) (P : SparseRational.Poly ℕ) :
    evalZhuSparseQ (scaleQ q P) = (q : ℂ) • evalZhuSparseQ P := by
  unfold evalZhuSparseQ
  rw [evalSparse_scaleQ, algebraMap_rat_mul_fock]

theorem evalZhuSparseQ_sumQ (Ps : List (SparseRational.Poly ℕ)) :
    evalZhuSparseQ (sumQ Ps) = (Ps.map evalZhuSparseQ).sum := by
  simpa only [evalZhuSparseQ] using evalSparse_sumQ sparseATwo Ps

/-- The sparse evaluator agrees with the existing certified current evaluator.  The latter uses
an implementation-private name for the coordinate family, so this lemma is deliberately stated
only through the public evaluator. -/
theorem evalZhuSparseQ_aWordAct (is : List ℕ) (s : ℤ) (w : ℕ)
    (P : SparseRational.Poly ℕ)
    (hP : evalZhuSparseQ P ∈ gradingWN (rank Ltwo) w) :
    evalZhuSparseQ (aWordActSparseQ is s w P) =
      AWordField is s (evalZhuSparseQ P) := by
  unfold evalZhuSparseQ at hP ⊢
  exact evalSparse_aWordActSparseQ is s w P hP

private theorem evalZhuSparseQ_cons (word : List ℕ) (q : ℚ)
    (P : SparseRational.Poly ℕ) :
    evalZhuSparseQ ((word, q) :: P) =
      (q : ℂ) • evalAWord word + evalZhuSparseQ P := by
  unfold evalZhuSparseQ
  change algebraMap ℚ (FockN (rank Ltwo)) q * evalWord sparseATwo word +
      evalSparse sparseATwo P = (q : ℂ) • evalAWord word + evalSparse sparseATwo P
  rw [evalWord_ATwo', algebraMap_rat_mul_fock]

/-- Evaluation of the public sparse state/coefficient action.  The grading hypothesis is exactly
the one used by the bounded current recurrence. -/
theorem eval_zhuStateActSparseQ (P : SparseRational.Poly ℕ) (coefficient : ℤ)
    (rightWeight : ℕ) (Q : SparseRational.Poly ℕ)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) rightWeight) :
    evalZhuSparseQ (zhuStateActSparseQ P coefficient rightWeight Q) =
      (YN (rank Ltwo) 1 (evalZhuSparseQ P)) coefficient (evalZhuSparseQ Q) := by
  induction P with
  | nil =>
      simp [zhuStateActSparseQ, bindQ, sumQ, evalZhuSparseQ_nil, map_zero]
  | cons t P ih =>
      rcases t with ⟨word, q⟩
      have ha' := evalSparse_aWordActSparseQ word coefficient rightWeight Q (by
        exact hQ)
      have htail :
          (P.map fun t => evalSparse sparseATwo
            (scaleQ t.2
              (aWordActSparseQ t.1 coefficient rightWeight Q))).sum =
            evalZhuSparseQ (zhuStateActSparseQ P coefficient rightWeight Q) := by
        unfold evalZhuSparseQ zhuStateActSparseQ
        rw [evalSparse_bindQ]
      rw [zhuStateActSparseQ, evalZhuSparseQ]
      rw [evalSparse_bindQ]
      simp only [List.map_cons, List.sum_cons]
      rw [evalSparse_scaleQ, ha', algebraMap_rat_mul_fock,
        htail, ih]
      rw [evalZhuSparseQ_cons, map_add, map_smul, YN_evalAWord]
      change (q : ℂ) • AWordField word coefficient (evalZhuSparseQ Q) +
          (YN (rank Ltwo) 1 (evalZhuSparseQ P)) coefficient
            (evalZhuSparseQ Q) = _
      rfl

/-- Evaluation of the public VOA-mode wrapper.  The definition in the compute file owns the
conversion `mode ↦ -mode-1`. -/
theorem eval_voaModeActSparseQ (P : SparseRational.Poly ℕ) (n : ℤ)
    (rightWeight : ℕ) (Q : SparseRational.Poly ℕ)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) rightWeight) :
    evalZhuSparseQ (voaModeActSparseQ P n rightWeight Q) =
      mode (YN (rank Ltwo) 1 (evalZhuSparseQ P)) n (evalZhuSparseQ Q) := by
  rw [voaModeActSparseQ, eval_zhuStateActSparseQ P (-n - 1) rightWeight Q hQ]
  rfl

/-- Exact Fock semantics of the sparse circle evaluator. -/
theorem eval_circleSparseQ (leftWeight : ℕ) (P : SparseRational.Poly ℕ)
    (rightWeight : ℕ) (Q : SparseRational.Poly ℕ)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) rightWeight) :
    evalZhuSparseQ (circleSparseQ leftWeight P rightWeight Q) =
      ∑ i ∈ Finset.range (leftWeight + 1),
        ((Nat.choose leftWeight i : ℚ) : ℂ) •
          mode (YN (rank Ltwo) 1 (evalZhuSparseQ P)) ((i : ℤ) - 2)
            (evalZhuSparseQ Q) := by
  unfold evalZhuSparseQ circleSparseQ
  rw [evalSparse_sumQ, List.map_map]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  apply Finset.sum_congr rfl
  intro i hi
  change evalSparse sparseATwo
      (scaleQ (Nat.choose leftWeight i : ℚ)
        (voaModeActSparseQ P ((i : ℤ) - 2) rightWeight Q)) = _
  rw [evalSparse_scaleQ, algebraMap_rat_mul_fock]
  congr 1
  change evalZhuSparseQ (voaModeActSparseQ P ((i : ℤ) - 2) rightWeight Q) = _
  exact eval_voaModeActSparseQ P ((i : ℤ) - 2) rightWeight Q hQ

/-- A neutral lattice mode is computed by the rank-one Heisenberg field. -/
theorem tripletLatticeVOA_smul_neutral (hp : 1 ≤ 2)
    (P Q : FockN (rank Ltwo)) (n : ℤ) :
    (tripletLatticeVOA 2 hp).smul (latStateGen Ltwo P 0) n (latStateGen Ltwo Q 0) =
      latStateGen Ltwo (mode (YN (rank Ltwo) 1 P) n Q) 0 := by
  rw [PreVertexAlgebra.smul_def, tripletLatticeVOA_Y, mode_apply]
  change YfullGen Ltwo (latP_even 2) (latP_posDef 2 hp) (mkEα Ltwo 0 P) (-n - 1)
      (mkEα Ltwo 0 Q) = mkEα Ltwo 0 ((YN (rank Ltwo) 1 P) (-n - 1) Q)
  exact WpTwoAMCoords.YfullGen_neutralFieldLift
    (latP_even 2) (latP_posDef 2 hp) P (-n - 1) Q

@[simp] theorem evalZhuSparseQ_vacuumSparseQ :
    evalZhuSparseQ vacuumSparseQ = vacuumN (rank Ltwo) := by
  rw [evalZhuSparseQ, vacuumSparseQ, evalSparse_normalizeQ]
  simp [evalRaw, evalWord, vacuumN]

private theorem evalWord_sparseATwo_append (u v : List ℕ) :
    evalWord sparseATwo (u ++ v) =
      evalWord sparseATwo u * evalWord sparseATwo v := by
  simp [evalWord, List.map_append]

private theorem evalZhuSparseQ_mulMonomial (word : List ℕ) (q : ℚ)
    (Q : SparseRational.Poly ℕ) :
    evalZhuSparseQ
        (bindQ Q fun v r => normalizeQ [(q * r, word ++ v)]) =
      (q : ℂ) • evalAWord word * evalZhuSparseQ Q := by
  induction Q with
  | nil => simp [bindQ, sumQ, evalZhuSparseQ_nil]
  | cons t Q ih =>
      rcases t with ⟨v, r⟩
      have htail :
          (Q.map fun t => evalSparse sparseATwo
            (normalizeQ [(q * t.2, word ++ t.1)])).sum =
            evalZhuSparseQ
              (bindQ Q fun v r => normalizeQ [(q * r, word ++ v)]) := by
        unfold evalZhuSparseQ
        rw [evalSparse_bindQ]
      rw [evalZhuSparseQ, evalSparse_bindQ]
      simp only [List.map_cons, List.sum_cons]
      rw [evalSparse_normalizeQ, htail]
      simp only [evalRaw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      rw [map_mul, evalWord_sparseATwo_append, evalWord_ATwo', evalWord_ATwo']
      rw [mul_assoc, algebraMap_rat_mul_fock r, algebraMap_rat_mul_fock q]
      change (q : ℂ) • (r : ℂ) • (evalAWord word * evalAWord v) +
          evalZhuSparseQ
            (bindQ Q fun v r => normalizeQ [(q * r, word ++ v)]) = _
      rw [ih, evalZhuSparseQ_cons]
      simp only [mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [mul_comm (q : ℂ) (r : ℂ)]

/-- Sparse multiplication evaluates as ordinary multiplication in the commutative Fock ring. -/
theorem evalZhuSparseQ_mulSparseQ (P Q : SparseRational.Poly ℕ) :
    evalZhuSparseQ (mulSparseQ P Q) =
      evalZhuSparseQ P * evalZhuSparseQ Q := by
  induction P with
  | nil => simp [mulSparseQ, bindQ, sumQ, evalZhuSparseQ_nil]
  | cons t P ih =>
      rcases t with ⟨word, q⟩
      have htail :
          (P.map fun t => evalSparse sparseATwo
            (bindQ Q fun v r => normalizeQ [(t.2 * r, t.1 ++ v)])).sum =
            evalZhuSparseQ (mulSparseQ P Q) := by
        unfold evalZhuSparseQ mulSparseQ
        rw [evalSparse_bindQ]
      rw [mulSparseQ, evalZhuSparseQ, evalSparse_bindQ]
      simp only [List.map_cons, List.sum_cons]
      rw [htail]
      change evalZhuSparseQ
            (bindQ Q fun v r => normalizeQ [(q * r, word ++ v)]) +
          evalZhuSparseQ (mulSparseQ P Q) = _
      rw [evalZhuSparseQ_mulMonomial, ih, evalZhuSparseQ_cons]
      rw [add_mul, smul_mul_assoc]

/-! ### Certified negative-Virasoro semantics

The positional sparse recurrence below is deliberately proved equivalent to the existing
`virActWord` recurrence.  In particular, it makes no appeal to the discovery-time Python
calculation: Lean replays every shifted current index and coefficient.
-/

private def shiftWordRawQ (mode : ℕ) (word : List ℕ) (q : ℚ) : RawPoly ℕ :=
  (List.range word.length).map fun position =>
    (q * ((word[position]! + 1 : ℕ) : ℚ),
      word.set position (word[position]! + mode))

private def shiftWordRecQ (mode : ℕ) : List ℕ → ℚ → RawPoly ℕ
  | [], _ => []
  | i :: is, q =>
      (q * (i + 1 : ℕ), (i + mode) :: is) ::
        (shiftWordRecQ mode is q).map fun t => (t.1, i :: t.2)

private theorem shiftWordRawQ_eq_rec (mode : ℕ) (word : List ℕ) (q : ℚ) :
    shiftWordRawQ mode word q = shiftWordRecQ mode word q := by
  induction word with
  | nil => simp [shiftWordRawQ, shiftWordRecQ]
  | cons i is ih =>
      rw [shiftWordRawQ, List.length_cons, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.getElem!_cons_zero, List.set_cons_zero]
      rw [shiftWordRecQ, ← ih]
      congr 1
      rw [shiftWordRawQ, List.map_map]
      apply List.map_congr_left
      intro position hp
      have hpos : position < is.length := by simpa using List.mem_range.mp hp
      simp [hpos]

private theorem eval_virVacuumSparseQ (mode : ℕ) :
    evalSparse sparseATwo (virVacuumSparseQ mode) = evalAPoly (virVacAPoly mode) := by
  rw [virVacuumSparseQ, evalSparse_normalizeQ,
    evalRaw_ATwo'_eq_evalAPoly_complexifyRawQ]
  congr 1
  simp [complexifyRawQ, virVacAPoly, List.map_append, Function.comp_def]

private theorem evalRaw_prepend (i : ℕ) (P : RawPoly ℕ) :
    evalRaw sparseATwo (P.map fun t => (t.1, i :: t.2)) =
      vVar Ltwo (alphaP 2) i * evalRaw sparseATwo P := by
  induction P with
  | nil => simp [evalRaw]
  | cons t P ih =>
      rcases t with ⟨q, w⟩
      change algebraMap ℚ (FockN Ltwo.rank) q * evalWord sparseATwo (i :: w) +
          evalRaw sparseATwo (P.map fun t => (t.1, i :: t.2)) =
        vVar Ltwo (alphaP 2) i *
          (algebraMap ℚ (FockN Ltwo.rank) q * evalWord sparseATwo w +
            evalRaw sparseATwo P)
      rw [ih, evalWord_ATwo']
      change algebraMap ℚ (FockN Ltwo.rank) q * evalAWord (i :: w) + _ = _
      rw [evalAWord, evalWord_ATwo']
      ring

private theorem eval_shiftWordRec_one_plus_vac (mode : ℕ) : ∀ word : List ℕ,
    evalAWord word * evalSparse sparseATwo (virVacuumSparseQ mode) +
        evalRaw sparseATwo (shiftWordRecQ mode word 1) =
      evalAPoly (virActWord mode word)
  | [] => by
      rw [shiftWordRecQ, eval_virVacuumSparseQ]
      simp [evalAWord, evalRaw, virActWord, vacuumN]
  | i :: is => by
      rw [shiftWordRecQ]
      change evalAWord (i :: is) * evalSparse sparseATwo (virVacuumSparseQ mode) +
          (algebraMap ℚ (FockN Ltwo.rank) (1 * (i + 1 : ℕ)) *
              evalWord sparseATwo ((i + mode) :: is) +
            evalRaw sparseATwo
              ((shiftWordRecQ mode is 1).map fun t => (t.1, i :: t.2))) = _
      rw [evalRaw_prepend, evalWord_ATwo', evalAWord]
      rw [virActWord, evalAPoly_append, eval_prependA, evalAPoly_singleton]
      rw [algebraMap_rat_mul_fock]
      push_cast
      simp only [one_mul]
      have hmul := congrArg
        (fun x : FockN Ltwo.rank => vVar Ltwo (alphaP 2) i * x)
        (eval_shiftWordRec_one_plus_vac mode is)
      dsimp only at hmul
      rw [mul_add] at hmul
      linear_combination hmul

private theorem eval_shiftWordRecQ (mode : ℕ) (word : List ℕ) (q : ℚ) :
    evalRaw sparseATwo (shiftWordRecQ mode word q) =
      (q : ℂ) • evalRaw sparseATwo (shiftWordRecQ mode word 1) := by
  induction word with
  | nil => simp [shiftWordRecQ, evalRaw]
  | cons i is ih =>
      rw [shiftWordRecQ]
      conv_rhs => rw [shiftWordRecQ]
      change algebraMap ℚ (FockN Ltwo.rank) (q * (i + 1 : ℕ)) *
            evalWord sparseATwo ((i + mode) :: is) +
          evalRaw sparseATwo
            ((shiftWordRecQ mode is q).map fun t => (t.1, i :: t.2)) =
        (q : ℂ) •
          (algebraMap ℚ (FockN Ltwo.rank) (1 * (i + 1 : ℕ)) *
              evalWord sparseATwo ((i + mode) :: is) +
            evalRaw sparseATwo
              ((shiftWordRecQ mode is 1).map fun t => (t.1, i :: t.2)))
      rw [evalRaw_prepend, evalRaw_prepend, ih]
      simp only [map_mul, Nat.cast_add, Nat.cast_one, algebraMap_rat_mul_fock]
      rw [smul_add, smul_mul_assoc, mul_smul_comm]
      congr 1
      norm_num

private theorem evalRaw_virShiftRawQ (mode : ℕ) : ∀ P : SparseRational.Poly ℕ,
    evalRaw sparseATwo (virShiftRawQ mode P) =
      (P.map fun t => (t.2 : ℂ) •
        evalRaw sparseATwo (shiftWordRecQ mode t.1 1)).sum
  | [] => by simp [virShiftRawQ, evalRaw]
  | (word, q) :: P => by
      change evalRaw sparseATwo
          (shiftWordRawQ mode word q ++ virShiftRawQ mode P) = _
      rw [evalRaw_append, shiftWordRawQ_eq_rec, eval_shiftWordRecQ,
        evalRaw_virShiftRawQ mode P]
      rfl

private theorem eval_virActSparseQ_aux (mode : ℕ) (hmode : 1 ≤ mode) :
    ∀ P : SparseRational.Poly ℕ,
      evalSparse sparseATwo P * evalSparse sparseATwo (virVacuumSparseQ mode) +
          (P.map fun t => (t.2 : ℂ) •
            evalRaw sparseATwo (shiftWordRecQ mode t.1 1)).sum =
        BgA.LSecBg Ltwo (lamP 2) 0 (-(mode : ℤ)) (evalSparse sparseATwo P)
  | [] => by simp [evalSparse, map_zero]
  | (word, q) :: P => by
      rw [evalSparse]
      simp only [List.map_cons, List.sum_cons]
      rw [evalWord_ATwo', algebraMap_rat_mul_fock]
      change ((q : ℂ) • evalAWord word + evalSparse sparseATwo P) *
            evalSparse sparseATwo (virVacuumSparseQ mode) +
          ((q : ℂ) • evalRaw sparseATwo (shiftWordRecQ mode word 1) +
            (P.map fun t => (t.2 : ℂ) •
              evalRaw sparseATwo (shiftWordRecQ mode t.1 1)).sum) =
        BgA.LSecBg Ltwo (lamP 2) 0 (-(mode : ℤ))
          ((q : ℂ) • evalAWord word + evalSparse sparseATwo P)
      rw [map_add, map_smul]
      have hword := eval_shiftWordRec_one_plus_vac mode word
      rw [eval_virActWord mode hmode word] at hword
      rw [add_mul, smul_mul_assoc]
      have hq := congrArg (fun x : FockN Ltwo.rank => (q : ℂ) • x) hword
      dsimp only at hq
      rw [smul_add] at hq
      linear_combination hq + eval_virActSparseQ_aux mode hmode P

/-- The executable sparse recurrence for `L_{-mode}` has the exact Fock-space semantics of the
negative Virasoro mode. -/
theorem evalZhuSparseQ_virActSparseQ (mode : ℕ) (hmode : 1 ≤ mode)
    (P : SparseRational.Poly ℕ) :
    evalZhuSparseQ (virActSparseQ mode P) =
      BgA.LSecBg Ltwo (lamP 2) 0 (-(mode : ℤ)) (evalZhuSparseQ P) := by
  rw [virActSparseQ, evalZhuSparseQ_addQ, evalZhuSparseQ_mulSparseQ]
  change evalSparse sparseATwo P * evalSparse sparseATwo (virVacuumSparseQ mode) +
      evalSparse sparseATwo (normalizeQ (virShiftRawQ mode P)) = _
  rw [evalSparse_normalizeQ, evalRaw_virShiftRawQ]
  simpa only [evalZhuSparseQ] using eval_virActSparseQ_aux mode hmode P

/-- Reifying a positive Virasoro word in sparse rational coordinates evaluates to the recursive
Fock-space Virasoro word. -/
theorem evalZhuSparseQ_reifyVirWordSparseQ (parts : List ℕ)
    (hpos : ∀ n ∈ parts, 1 ≤ n) :
    evalZhuSparseQ (reifyVirWordSparseQ parts) = virWordFockTwo parts := by
  induction parts with
  | nil =>
      simp [reifyVirWordSparseQ, virWordFockTwo, evalZhuSparseQ_vacuumSparseQ]
  | cons n parts ih =>
      rw [reifyVirWordSparseQ, List.foldr_cons, virWordFockTwo,
        evalZhuSparseQ_virActSparseQ n (hpos n (by simp))]
      exact congrArg _ (ih fun m hm => hpos m (by simp [hm]))

/-- The Newton recurrence used by the rational checker evaluates to the actual Schur state. -/
theorem evalZhuSparseQ_schurSparseQ (n : ℕ) :
    evalZhuSparseQ (schurSparseQ n) = vSchur Ltwo sparseAlphaTwo n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [schurSparseQ, evalZhuSparseQ_vacuumSparseQ, vSchur_zero, vacuumN]
      | succ N =>
          rw [schurSparseQ, evalZhuSparseQ_scaleQ, evalZhuSparseQ_sumQ,
            vSchur_succ]
          have hcoeff : (((1 / (N + 1 : ℚ)) : ℚ) : ℂ) =
              ((N + 1 : ℂ)⁻¹) := by
            push_cast
            rw [one_div]
          rw [hcoeff]
          congr 1
          rw [List.map_map]
          rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
          apply Finset.sum_congr rfl
          intro i hi
          change evalZhuSparseQ
              (mulSparseQ (normalizeQ [(1, [i])]) (schurSparseQ (N - i))) = _
          rw [evalZhuSparseQ_mulSparseQ]
          have hsingle :
              evalZhuSparseQ (normalizeQ [(1, [i])]) =
                vVar Ltwo sparseAlphaTwo i := by
            rw [evalZhuSparseQ, evalSparse_normalizeQ]
            simp [evalRaw, evalWord_ATwo', evalAWord, vacuumN]
          rw [hsingle, ih (N - i) (by omega)]

/-- The literal 33-term rational coordinate is the already certified double-screening Schur
state.  This deliberately reuses `screened_eq_ledger`; no second screening computation is hidden
in the Zhu assembly. -/
theorem evalZhuSparseQ_qTwoSparseQ :
    evalZhuSparseQ qTwoSparseQ =
      (2 : ℂ) • (vSchur Ltwo sparseAlphaTwo 3 * vSchur Ltwo sparseAlphaTwo 7) +
        (-8 : ℂ) • (vSchur Ltwo sparseAlphaTwo 4 * vSchur Ltwo sparseAlphaTwo 6) +
          (6 : ℂ) • (vSchur Ltwo sparseAlphaTwo 5 * vSchur Ltwo sparseAlphaTwo 5) := by
  rw [screened_eq_ledger]
  simp only [evalZhuSparseQ, qTwoSparseQ, screenedLedger, evalSparse, evalAPoly,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    evalWord_ATwo', algebraMap_rat_mul_fock]
  norm_num
  module

/-- Coordinate transport for the intrinsic screened state used by the Zhu `O` certificate. -/
theorem qwpSqNegTwoAlphaTriplet_coe_eq_eval_qTwoSparseQ (hp : 1 ≤ 2) :
    ((qwpSqNegTwoAlphaTriplet 2 hp : (tripletW 2 hp).carrier) :
        LatModuleGen (latP 2)) =
      latStateGen Ltwo (evalZhuSparseQ qTwoSparseQ) 0 := by
  rw [qwpSqNegTwoAlphaTriplet_coe, Qwp_sq_neg_two_eq_schur hp,
    evalZhuSparseQ_qTwoSparseQ]

/-- Semantic equality between the sparse circle and an intrinsic Frenkel--Zhu residue.  The
right grading hypothesis is required only by the executable bounded field evaluator. -/
theorem coe_Pres_eq_eval_zhuCircleSparseQ (hp : 1 ≤ 2) (leftWeight rightWeight : ℕ)
    (P Q : SparseRational.Poly ℕ) (x y : (tripletW 2 hp).carrier)
    (hx : (x : LatModuleGen (latP 2)) = latStateGen Ltwo (evalZhuSparseQ P) 0)
    (hy : (y : LatModuleGen (latP 2)) = latStateGen Ltwo (evalZhuSparseQ Q) 0)
    (hQ : evalZhuSparseQ Q ∈ gradingWN (rank Ltwo) rightWeight) :
    ((Pres (tripletWVOA 2 hp) leftWeight x y 0 : (tripletW 2 hp).carrier) :
        LatModuleGen (latP 2)) =
      latStateGen Ltwo (evalZhuSparseQ
        (circleSparseQ leftWeight P rightWeight Q)) 0 := by
  rw [Pres, Nat.add_zero]
  simp only [Submodule.coe_sum, Submodule.coe_smul, smul_coe, hx, hy]
  rw [eval_circleSparseQ leftWeight P rightWeight Q hQ]
  have hmap :
      latStateGen Ltwo
          (∑ i ∈ Finset.range (leftWeight + 1),
            ((Nat.choose leftWeight i : ℚ) : ℂ) •
              mode (YN (rank Ltwo) 1 (evalZhuSparseQ P)) ((i : ℤ) - 2)
                (evalZhuSparseQ Q)) 0 =
        ∑ i ∈ Finset.range (leftWeight + 1),
          latStateGen Ltwo
            (((Nat.choose leftWeight i : ℚ) : ℂ) •
              mode (YN (rank Ltwo) 1 (evalZhuSparseQ P)) ((i : ℤ) - 2)
                (evalZhuSparseQ Q)) 0 := by
    induction Finset.range (leftWeight + 1) using Finset.induction with
    | empty => simp [latStateGen]
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, latStateGen_add_boson, ih]
  rw [hmap]
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i ≤ leftWeight := by
    rw [Finset.mem_range] at hi
    omega
  simp only [Nat.cast_zero, add_zero, sub_zero]
  rw [cbz_natCast_eq_choose hil,
    tripletLatticeVOA_smul_neutral, latStateGen_smul_boson]
  congr 1

/-! ## Intrinsic states attached to the typed certificate descriptors -/

/-- Domain condition for a Virasoro descriptor.  The closed negative-mode recurrence is proved
for genuine negative modes `L_{-n}`, hence `n ≥ 1`; the two screening descriptors need no extra
condition. -/
def _root_.VOA.LatGen.WpTwoZhuSparseCompute.ZhuStateDesc.Valid :
    ZhuStateDesc → Prop
  | .vir parts => ∀ n ∈ parts, 1 ≤ n
  | .h => True
  | .l3h => True

noncomputable instance (d : ZhuStateDesc) : Decidable d.Valid :=
  Classical.propDecidable _

/-- Interpret a sparse certificate state descriptor as an intrinsic state of `W(2)`. -/
noncomputable def _root_.VOA.LatGen.WpTwoZhuSparseCompute.ZhuStateDesc.intrinsic
    (hp : 1 ≤ 2) :
    ZhuStateDesc → (tripletW 2 hp).carrier
  | .vir parts => ⟨virWordTwo hp parts, virWordTwo_mem_carrier hp parts⟩
  | .h => genH 2 hp
  | .l3h => (tripletWVOA 2 hp).L (-3) (genH 2 hp)

theorem virWordTwo_mem_grading_sum (hp : 1 ≤ 2) : ∀ parts : List ℕ,
    (⟨virWordTwo hp parts, virWordTwo_mem_carrier hp parts⟩ :
        (tripletW 2 hp).carrier) ∈
      (tripletWVOA 2 hp).grading (parts.sum : ℤ)
  | [] => by simpa using (tripletWVOA 2 hp).vacuum_mem
  | n :: parts => by
      have ih := virWordTwo_mem_grading_sum hp parts
      have h := (tripletWVOA 2 hp).smul_mem_grading
        (tripletWVOA 2 hp).conformal_mem ih (-(n : ℤ) + 1)
      have heq :
          (⟨virWordTwo hp (n :: parts), virWordTwo_mem_carrier hp (n :: parts)⟩ :
              (tripletW 2 hp).carrier) =
            (tripletWVOA 2 hp).smul (tripletWVOA 2 hp).conformalVector
              (-(n : ℤ) + 1)
              ⟨virWordTwo hp parts, virWordTwo_mem_carrier hp parts⟩ := by
        apply Subtype.ext
        rw [smul_coe, tripletWVOA_conformalVector_coe]
        rfl
      rw [heq]
      convert h using 1
      simp
      congr 1
      ring

/-- The intrinsic state attached to a descriptor has exactly the advertised conformal weight. -/
theorem _root_.VOA.LatGen.WpTwoZhuSparseCompute.ZhuStateDesc.intrinsic_mem_grading
    (hp : 1 ≤ 2) (d : ZhuStateDesc) :
    d.intrinsic hp ∈ (tripletWVOA 2 hp).grading (d.weight : ℤ) := by
  cases d with
  | vir parts => exact virWordTwo_mem_grading_sum hp parts
  | h =>
      change genH 2 hp ∈ (tripletWVOA 2 hp).grading 3
      exact Htrip_mem_grading 2 hp
  | l3h =>
      have hH : genH 2 hp ∈ (tripletWVOA 2 hp).grading 3 :=
        Htrip_mem_grading 2 hp
      have h := (tripletWVOA 2 hp).smul_mem_grading
        (tripletWVOA 2 hp).conformal_mem hH (-2)
      simpa [ZhuStateDesc.intrinsic, VertexOperatorAlgebra.L_def] using h

/-- Projecting the neutral charge coordinate of an ambient triplet weight-`k` state lands in the
ordinary bosonic weight-`k` space. -/
theorem neutralCoord_mem_gradingZN_of_mem_gradTrip (k : ℤ)
    {x : LatModuleGen Ltwo} (hx : x ∈ gradTrip 2 k) :
    coordEα Ltwo 0 x ∈ gradingZN (rank Ltwo) k := by
  rw [gradTrip_eq_iSup] at hx
  refine Submodule.iSup_induction
    (fun β : Ltwo.carrier => bigradα Ltwo (k - qZP 2 β, β))
    (motive := fun y => coordEα Ltwo 0 y ∈ gradingZN (rank Ltwo) k)
    hx ?_ ?_ ?_
  · intro β y hy
    obtain ⟨P, hP, rfl⟩ := hy
    rw [mkEα_apply, coordEα_apply]
    by_cases hβ : (0 : Ltwo.carrier) = β
    · subst β
      rw [if_pos rfl]
      change P ∈ gradingZN (rank Ltwo) (k - qZP 2 0) at hP
      rw [qZP_zero] at hP
      simpa using hP
    · rw [if_neg hβ]
      exact Submodule.zero_mem _
  · change coordEα Ltwo 0 (0 : LatModuleGen Ltwo) ∈ gradingZN (rank Ltwo) k
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

/-- A valid descriptor's intrinsic `W(2)` state is exactly the neutral lattice lift of its
executable sparse coordinate. -/
theorem _root_.VOA.LatGen.WpTwoZhuSparseCompute.ZhuStateDesc.intrinsic_coe_eq_eval
    (hp : 1 ≤ 2) (d : ZhuStateDesc) (hd : d.Valid) :
    ((d.intrinsic hp : (tripletW 2 hp).carrier) : LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ d.eval) 0 := by
  cases d with
  | vir parts =>
      simp only [ZhuStateDesc.Valid] at hd
      change virWordTwo hp parts =
        latStateGen Ltwo (evalZhuSparseQ (reifyVirWordSparseQ parts)) 0
      rw [evalZhuSparseQ_reifyVirWordSparseQ parts hd]
      exact virWordTwo_eq_fock hp parts
  | h =>
      change Htrip 2 = latStateGen Ltwo (evalZhuSparseQ hThreeSparseQ) 0
      rw [Htrip, Screen.Hscr_eq Ltwo (alphaP 2) 2 hp (latP_form_alpha 2),
        cocycle_two, one_smul, hThreeSparseQ, evalZhuSparseQ,
        evalSparse_sThreeSparseQ]
  | l3h =>
      change (tripletLatticeVOA 2 hp).L (-3) (Htrip 2) =
        latStateGen Ltwo
          (evalZhuSparseQ (virActSparseQ 3 hThreeSparseQ)) 0
      rw [tripletLatticeVOA_L, evalZhuSparseQ_virActSparseQ 3 (by omega),
        hThreeSparseQ, evalZhuSparseQ, evalSparse_sThreeSparseQ,
        Htrip, Screen.Hscr_eq Ltwo (alphaP 2) 2 hp (latP_form_alpha 2),
        cocycle_two, one_smul]
      change BgA.LBg Ltwo (lamP 2) (-3)
          (mkEα Ltwo 0 (vSchur Ltwo (alphaP 2) 3)) =
        mkEα Ltwo 0
          (BgA.LSecBg Ltwo (lamP 2) 0 (-3) (vSchur Ltwo (alphaP 2) 3))
      rw [BgA.LBg_mkEα Ltwo (latP_posDef 2 hp)]

/-- The sparse coordinate of a valid descriptor has the advertised bosonic weight. -/
theorem _root_.VOA.LatGen.WpTwoZhuSparseCompute.ZhuStateDesc.eval_mem_gradingWN
    (hp : 1 ≤ 2) (d : ZhuStateDesc) (hd : d.Valid) :
    evalZhuSparseQ d.eval ∈ gradingWN (rank Ltwo) d.weight := by
  have hIntrinsic := d.intrinsic_mem_grading hp
  change ((d.intrinsic hp : (tripletW 2 hp).carrier) : LatModuleGen Ltwo) ∈
    gradTrip 2 (d.weight : ℤ) at hIntrinsic
  have hcoord := neutralCoord_mem_gradingZN_of_mem_gradTrip
    (d.weight : ℤ) hIntrinsic
  rw [d.intrinsic_coe_eq_eval hp hd, latStateGen,
    coordEα_apply, if_pos rfl] at hcoord
  rw [gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at hcoord
  exact hcoord

section AxiomAudit
#print axioms eval_zhuStateActSparseQ
#print axioms eval_voaModeActSparseQ
#print axioms eval_circleSparseQ
#print axioms coe_Pres_eq_eval_zhuCircleSparseQ
#print axioms ZhuStateDesc.intrinsic_mem_grading
#print axioms evalZhuSparseQ_virActSparseQ
#print axioms ZhuStateDesc.intrinsic_coe_eq_eval
#print axioms ZhuStateDesc.eval_mem_gradingWN
end AxiomAudit

end VOA.LatGen.WpTwoZhuSparseSemantics
