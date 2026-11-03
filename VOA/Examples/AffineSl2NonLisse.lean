/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2Presentation
import VOA.Examples.AffineSl2HarmonicNorm
import VOA.Modules.FiniteGenerationProof
import VOA.Modularity.C2GradedVanishing

/-!
# The admissible affine `sl2` example is not C2-cofinite

This file proves the lower bound which is deliberately absent from
`Examples.AffineSl2Presentation`: the classes of the horizontal highest vectors
`e_{-1}^r 1` survive in the C2 quotient of the simple affine VOA at level `-4/3`.

The proof does not assume exactness of the full symbol presentation.  It uses only the weaker
extremal-weight argument.  The canonical invariant form detects `e_{-1}^r 1` against
`f_{-1}^r 1`.  A homogeneous C2 generator of conformal weight `r` has factors of total weight
`r-1`, hence horizontal charge at most `2(r-1)`, and therefore pairs trivially with the charge
`-2r` detector.  The same form kills the maximal ideal, so the detector descends through the
simple quotient.  Distinct conformal weights then give an infinite linearly independent tower.

Together with `Sl2Pres.etingofFinite_simpleSl2QL'`, this gives the strict formal benchmark
`not C2Cofinite and EtingofFinite`.  The repository does not define associated varieties or
quasi-lisseness itself, so this file does not promote Etingof finiteness to a quasi-lisse theorem.
-/

namespace VOA.Sl2NonLisse

open scoped BigOperators
open VOA.VertexOperatorAlgebra
open VOA.AffineVOA
open VOA.AffineVOA.Inst
open VOA.AffineVOA.HarmonicNorm
open VOA.Sl2Sing
open VOA.QuasiLisseSl2
open VOA.Sl2Pres
open VOA.LiRadical

noncomputable section

local notation "kk" => (-4 / 3 : ℂ)
local notation "W43" => affineSl2QL
local notation "I43" => QuotVOA.maxGradedIdeal W43
local notation "L43" => simpleSl2QL

/-- Horizontal `h_0`-charge of an affine current colour. -/
def colourCharge : Fin 3 → ℤ := ![2, -2, 0]

/-- Horizontal charge of a creation word. -/
def wordCharge : List (Fin 3 × ℕ) → ℤ
  | [] => 0
  | ai :: rest => colourCharge ai.1 + wordCharge rest

/-- The empty creation word is the vacuum and has zero horizontal Cartan
charge. This is the base case of the charge calculation for current words. -/
@[simp] theorem wordCharge_nil : wordCharge ([] : List (Fin 3 × ℕ)) = 0 := rfl

/-- Adding a current changes horizontal charge by its colour charge: plus
two for e, minus two for f, and zero for h. Its negative mode index changes
conformal weight but does not change this horizontal charge contribution. -/
@[simp] theorem wordCharge_cons (ai : Fin 3 × ℕ) (rest : List (Fin 3 × ℕ)) :
    wordCharge (ai :: rest) = colourCharge ai.1 + wordCharge rest := rfl

/-- Every current contributes at most two units of horizontal charge, while it contributes at
least one unit of conformal weight. -/
theorem wordCharge_le_twice_wordDeg : ∀ l : List (Fin 3 × ℕ),
    wordCharge l ≤ 2 * wordDegA l
  | [] => by simp [wordCharge, wordDegA]
  | ai :: rest => by
      have ih := wordCharge_le_twice_wordDeg rest
      have hc : colourCharge ai.1 ≤ 2 := by
        rcases ai with ⟨a, n⟩
        fin_cases a <;> norm_num [colourCharge]
      rw [wordCharge_cons, wordDegA_cons]
      have hn : (0 : ℤ) ≤ ai.2 := Int.natCast_nonneg _
      omega

/-- A creation word is an `h_0` eigenvector of its combinatorial charge. -/
theorem H0_wordStateA (k : ℂ) : ∀ l : List (Fin 3 × ℕ),
    J k colH 0 (wordStateA k l) = (wordCharge l : ℂ) • wordStateA k l
  | [] => by simp [wordStateA_nil, wordCharge_nil, H_vac0]
  | ai :: rest => by
      obtain ⟨a, n⟩ := ai
      rw [wordStateA_cons]
      fin_cases a
      · change J k colH 0 (J k colE (-((n : ℤ)) - 1) (wordStateA k rest)) =
          ((2 + wordCharge rest : ℤ) : ℂ) •
            J k colE (-((n : ℤ)) - 1) (wordStateA k rest)
        rw [HEs k 0 (-((n : ℤ)) - 1) (-((n : ℤ)) - 1) (by ring),
          H0_wordStateA k rest, map_smul]
        rw [← add_smul]
        congr 1
        push_cast
        ring
      · change J k colH 0 (J k colF (-((n : ℤ)) - 1) (wordStateA k rest)) =
          ((-2 + wordCharge rest : ℤ) : ℂ) •
            J k colF (-((n : ℤ)) - 1) (wordStateA k rest)
        rw [HFs k 0 (-((n : ℤ)) - 1) (-((n : ℤ)) - 1) (by ring),
          H0_wordStateA k rest, map_smul]
        rw [← sub_smul]
        congr 1
        push_cast
        ring
      · change J k colH 0 (J k colH (-((n : ℤ)) - 1) (wordStateA k rest)) =
          ((0 + wordCharge rest : ℤ) : ℂ) •
            J k colH (-((n : ℤ)) - 1) (wordStateA k rest)
        rw [HHs k 0 (-((n : ℤ)) - 1) (by omega), H0_wordStateA k rest]
        simp

/-- The lowest harmonic has horizontal charge `-2r`. -/
theorem H0_fHarmonic (k : ℂ) (r : ℕ) :
    J k colH 0 (fHarmonic k r) = (-2 * (r : ℂ)) • fHarmonic k r := by
  induction r with
  | zero => simp [H_vac0]
  | succ r ih =>
      rw [fHarmonic_succ, HFs k 0 (-1) (-1) (by norm_num), ih, map_smul]
      rw [← sub_smul]
      congr 1
      push_cast
      ring

/-- Horizontal charge is additive under every vertex-algebra mode. -/
theorem H0_smul_of_eigen {k : ℂ} (hk : k + 2 ≠ 0) {u v : WakModule k}
    {cu cv : ℂ} (hu : J k colH 0 u = cu • u) (hv : J k colH 0 v = cv • v)
    (n : ℤ) :
    J k colH 0 ((affineSl2VOA_closed k hk).smul u n v) =
      (cu + cv) • (affineSl2VOA_closed k hk).smul u n v := by
  have h := (affineSl2VOA_closed k hk).zeroMode_isDerivation
    (currentState k colH) u v n
  rw [smul_currentState_eq_J, smul_currentState_eq_J, smul_currentState_eq_J,
    hu, hv, (affineSl2VOA_closed k hk).smul_smul_right,
    (affineSl2VOA_closed k hk).smul_smul_left] at h
  rw [add_smul]
  exact sub_eq_iff_eq_add.mp h

/-- The highest harmonic has conformal weight `r`. -/
theorem eHarmonic_mem_grading {k : ℂ} (hk : k + 2 ≠ 0) (r : ℕ) :
    eHarmonic k r ∈ (affineSl2VOA_closed k hk).grading (r : ℤ) := by
  induction r with
  | zero =>
      rw [eHarmonic_zero,
        show vacuumA k = (affineSl2VOA_closed k hk).vacuum from rfl]
      exact (affineSl2VOA_closed k hk).vacuum_mem_grading_zero
  | succ r ih =>
      rw [eHarmonic_succ]
      rw [← smul_currentState_eq_J k hk colE (-1) (eHarmonic k r)]
      have h := (affineSl2VOA_closed k hk).smul_mem_grading
        (currentState_mem_grading k hk colE) ih (-1)
      have heq : (1 : ℤ) + (r : ℤ) - (-1) - 1 = ((r + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rwa [heq] at h

/-- The lowest harmonic has conformal weight `r`. -/
theorem fHarmonic_mem_grading {k : ℂ} (hk : k + 2 ≠ 0) (r : ℕ) :
    fHarmonic k r ∈ (affineSl2VOA_closed k hk).grading (r : ℤ) := by
  induction r with
  | zero =>
      rw [fHarmonic_zero,
        show vacuumA k = (affineSl2VOA_closed k hk).vacuum from rfl]
      exact (affineSl2VOA_closed k hk).vacuum_mem_grading_zero
  | succ r ih =>
      rw [fHarmonic_succ]
      rw [← smul_currentState_eq_J k hk colF (-1) (fHarmonic k r)]
      have h := (affineSl2VOA_closed k hk).smul_mem_grading
        (currentState_mem_grading k hk colF) ih (-1)
      have heq : (1 : ℤ) + (r : ℤ) - (-1) - 1 = ((r + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rwa [heq] at h

/-- The invariant-form detector of the `r`-th harmonic kills every exact-degree C2 generator
made from two creation words.  The strict inequality is the one-unit C2 degree shift. -/
theorem form_fHarmonic_word_O₂_zero (r : ℕ) (l₁ l₂ : List (Fin 3 × ℕ))
    (hpq : wordDegA l₁ + wordDegA l₂ + 1 = (r : ℤ)) :
    LQ43.formAdm.form (fHarmonic kk r)
      ((W43).smul (wordStateA kk l₁) (-2) (wordStateA kk l₂)) = 0 := by
  have hcharge₁ := wordCharge_le_twice_wordDeg l₁
  have hcharge₂ := wordCharge_le_twice_wordDeg l₂
  have hlt : wordCharge l₁ + wordCharge l₂ < 2 * (r : ℤ) := by omega
  have heig := H0_smul_of_eigen hkQL
    (H0_wordStateA kk l₁) (H0_wordStateA kk l₂) (-2)
  have heig' :
      J kk colH 0 ((W43).smul (wordStateA kk l₁) (-2) (wordStateA kk l₂)) =
        ((wordCharge l₁ : ℂ) + (wordCharge l₂ : ℂ)) •
          (W43).smul (wordStateA kk l₁) (-2) (wordStateA kk l₂) := by
    exact heig
  have hadj := LQ43.weightOne_adj
    (canonicalInvariantForm_isFullyInvariant
      LQ43.vacuum_ne_zero LQ43.quasiPrimary)
    (currentState_mem_grading kk admLevel_noncritical colH)
    (LQ43.quasiPrimary _
      (currentState_mem_grading kk admLevel_noncritical colH))
    0 (fHarmonic kk r)
      ((W43).smul (wordStateA kk l₁) (-2) (wordStateA kk l₂))
  rw [LQ43.smul_currentState_adm, neg_zero, LQ43.smul_currentState_adm,
    H0_fHarmonic, heig'] at hadj
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hadj
  have hfac :
      (((wordCharge l₁ + wordCharge l₂ : ℤ) : ℂ) - 2 * (r : ℂ)) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_lt hlt))
  have hadj' :
      (-2 * (r : ℂ)) * LQ43.formAdm.form (fHarmonic kk r)
          ((W43).smul (wordStateA kk l₁) (-2) (wordStateA kk l₂)) =
        -(((wordCharge l₁ : ℂ) + (wordCharge l₂ : ℂ)) *
          LQ43.formAdm.form (fHarmonic kk r)
            ((W43).smul (wordStateA kk l₁) (-2) (wordStateA kk l₂))) := by
    exact hadj
  have hmul :
      (((wordCharge l₁ + wordCharge l₂ : ℤ) : ℂ) - 2 * (r : ℂ)) *
        LQ43.formAdm.form (fHarmonic kk r)
          ((W43).smul (wordStateA kk l₁) (-2) (wordStateA kk l₂)) = 0 := by
    rw [Int.cast_add]
    linear_combination hadj'
  exact (mul_eq_zero.mp hmul).resolve_left hfac

/-- The word calculation extends linearly to arbitrary homogeneous factors. -/
theorem form_fHarmonic_hspan_O₂_zero (r : ℕ) {p q : ℤ}
    {u v : WakModule kk} (hu : u ∈ HSpan kk p) (hv : v ∈ HSpan kk q)
    (hpq : p + q + 1 = (r : ℤ)) :
    LQ43.formAdm.form (fHarmonic kk r) ((W43).smul u (-2) v) = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l₁, hl₁, rfl⟩ := hx
      induction hv using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨l₂, hl₂, rfl⟩ := hy
          exact form_fHarmonic_word_O₂_zero r l₁ l₂ (by omega)
      | zero => simp
      | add x y _ _ ihx ihy =>
          rw [(W43).smul_add_right, map_add, ihx, ihy, add_zero]
      | smul c x _ ih =>
          rw [(W43).smul_smul_right, map_smul, ih, smul_zero]
  | zero => simp
  | add x y _ _ ihx ihy =>
      rw [(W43).smul_add_left, map_add, ihx, ihy, add_zero]
  | smul c x _ ih =>
      rw [(W43).smul_smul_left, map_smul, ih, smul_zero]

/-- The harmonic detector kills the whole universal C2 span.  For the degree-`r` component this
is the horizontal extremal-charge argument; all other components vanish by conformal-weight
orthogonality. -/
theorem form_fHarmonic_O₂_zero (r : ℕ) {x : WakModule kk} (hx : x ∈ O₂ W43) :
    LQ43.formAdm.form (fHarmonic kk r) x = 0 := by
  rw [O₂_eq_span_homGen] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨p, q, u, v, hu, hv, rfl⟩ := hz
      by_cases hpq : p + q + 1 = (r : ℤ)
      · exact form_fHarmonic_hspan_O₂_zero r
          (gradingZA_le_hspan kk p hu) (gradingZA_le_hspan kk q hv) hpq
      · exact InvariantForm.orthogonal_of_ne LQ43.formAdm (Ne.symm hpq)
          (fHarmonic_mem_grading admLevel_noncritical r) (gen_mem_grading W43 hu hv)
  | zero => rw [map_zero]
  | add x y _ _ ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | smul c x _ ih => rw [map_smul, ih, smul_zero]

/-- The canonical pairing of opposite horizontal harmonics is nonzero at level `-4/3`, in every
rank. -/
theorem form_fHarmonic_eHarmonic_ne_zero (r : ℕ) :
    LQ43.formAdm.form (fHarmonic kk r) (eHarmonic kk r) ≠ 0 := by
  rw [form_fHarmonic_eHarmonic admLevel_noncritical LQ43.formAdm
    (canonicalInvariantForm_isFullyInvariant LQ43.vacuum_ne_zero LQ43.quasiPrimary)
    (canonicalInvariantForm_normalized LQ43.vacuum_ne_zero LQ43.quasiPrimary)
    LQ43.quasiPrimary]
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero r (by norm_num : (-1 : ℂ) ≠ 0))
      (by exact_mod_cast Nat.factorial_ne_zero r))
    (Finset.prod_ne_zero_iff.mpr (fun j hj => by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      have hjnonneg : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      linarith))

/-- Every C2 vector in the simple quotient has a C2 lift in the universal affine VOA.  This is
surjectivity on the relation span, proved generator by generator; it is not injectivity of C2
functoriality. -/
theorem exists_O₂_lift {y : WakModule kk ⧸ I43} (hy : y ∈ O₂ L43) :
    ∃ x : WakModule kk, x ∈ O₂ W43 ∧ (I43).mkQ x = y := by
  rw [O₂] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, b, rfl⟩ := hz
      obtain ⟨u, rfl⟩ := (I43).mkQ_surjective a
      obtain ⟨v, rfl⟩ := (I43).mkQ_surjective b
      refine ⟨(W43).smul u (-2) v, Submodule.subset_span ⟨u, v, rfl⟩, ?_⟩
      exact (QuotVOA.quotientVOA_mkQ_smul
        (QuotVOA.maxGradedIdeal_isIdeal W43)
        (QuotVOA.maxGradedIdeal_isGradedIdeal W43) u (-2) v).symm
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
      obtain ⟨x', hx'O, hx'⟩ := hx
      obtain ⟨y', hy'O, hy'⟩ := hy
      refine ⟨x' + y', Submodule.add_mem _ hx'O hy'O, ?_⟩
      rw [map_add, hx', hy']
  | smul c x _ hx =>
      obtain ⟨x', hx'O, hx'⟩ := hx
      refine ⟨c • x', Submodule.smul_mem _ c hx'O, ?_⟩
      rw [map_smul, hx']

/-- The image of the highest harmonic in the simple affine VOA. -/
def eHarmonicL (r : ℕ) : WakModule kk ⧸ I43 := (I43).mkQ (eHarmonic kk r)

/-- The simple-quotient harmonic remains homogeneous of weight `r`. -/
theorem eHarmonicL_mem_grading (r : ℕ) : eHarmonicL r ∈ (L43).grading (r : ℤ) :=
  QuotVOA.quotientVOA_mkQ_grading
    (QuotVOA.maxGradedIdeal_isIdeal W43)
    (QuotVOA.maxGradedIdeal_isGradedIdeal W43)
    (eHarmonic_mem_grading admLevel_noncritical r)

/-- No highest harmonic class lies in C2 of the simple quotient.  The maximal ideal occurs in
the second argument of the invariant form, exactly matching Li's right radical. -/
theorem eHarmonicL_not_mem_O₂ (r : ℕ) : eHarmonicL r ∉ O₂ L43 := by
  intro hO
  obtain ⟨x, hxO, hxq⟩ := exists_O₂_lift hO
  have hdiff : eHarmonic kk r - x ∈ I43 := by
    rw [← Submodule.ker_mkQ I43, LinearMap.mem_ker, map_sub, hxq, eHarmonicL, sub_self]
  have hrad : eHarmonic kk r - x ∈ SingVec.rightRadical LQ43.formAdm := by
    have hfull : LQ43.formAdm.IsFullyInvariant :=
      canonicalInvariantForm_isFullyInvariant LQ43.vacuum_ne_zero LQ43.quasiPrimary
    have hnorm : LQ43.formAdm.Normalized :=
      canonicalInvariantForm_normalized LQ43.vacuum_ne_zero LQ43.quasiPrimary
    rw [LiRadical.rightRadical_eq_maxGradedIdeal hfull hnorm]
    exact hdiff
  have hzero := (SingVec.mem_rightRadical.mp hrad) (fHarmonic kk r)
  have hxzero := form_fHarmonic_O₂_zero r hxO
  rw [map_sub, hxzero, sub_zero] at hzero
  exact form_fHarmonic_eHarmonic_ne_zero r hzero

/-- The C2 classes of the simple-quotient highest harmonics are linearly independent. -/
theorem eHarmonicL_C₂_linearIndependent :
    LinearIndependent ℂ (fun r : ℕ => mk₂ L43 (eHarmonicL r)) := by
  apply mk₂_linearIndependent_of_notMem L43 (fun r : ℕ => (r : ℤ))
  · intro a b hab
    exact Int.ofNat_injective hab
  · exact eHarmonicL_mem_grading
  · exact eHarmonicL_not_mem_O₂

/-- In the universal C2 algebra the `r`-th harmonic is exactly the `r`-th power of the current
symbol. -/
theorem mk₂_eHarmonic_eq_eV_pow (r : ℕ) :
    mk₂ W43 (eHarmonic kk r) = (Sl2Pres.eV) ^ r := by
  induction r with
  | zero =>
      rw [eHarmonic_zero,
        show vacuumA kk = (W43).vacuum from rfl, pow_zero, A₂_one_eq]
  | succ r ih =>
      rw [eHarmonic_succ]
      have hmode : J kk colE (-1) (eHarmonic kk r) =
          (W43).smul (currentState kk colE) (-1) (eHarmonic kk r) := by
        exact (smul_currentState_eq_J kk hkQL colE (-1) (eHarmonic kk r)).symm
      rw [hmode]
      change mk₂ W43 (poissonMul W43 (currentState kk colE) (eHarmonic kk r)) = _
      rw [← A₂_mul_mk, ih, pow_succ']
      rfl

/-- The concrete harmonic tower is the requested symbol tower
`symbolAlgL(e^r)`; no injectivity of the full symbol map is used. -/
theorem symbolAlgL_e_pow_eq_harmonic (r : ℕ) :
    Sl2Pres.symbolAlgL (eSym ^ r) = mk₂ L43 (eHarmonicL r) := by
  rw [map_pow, Sl2Pres.symbolAlgL_eSym, Sl2Pres.eL, ← map_pow,
    ← mk₂_eHarmonic_eq_eV_pow, Sl2Pres.A₂QL_mk₂]
  rfl

/-- The weaker lower bound actually needed here: the symbol classes
`[e^r]`, `r ∈ ℕ`, are linearly independent. -/
theorem symbolAlgL_e_pow_linearIndependent :
    LinearIndependent ℂ (fun r : ℕ => Sl2Pres.symbolAlgL (eSym ^ r)) := by
  simpa only [symbolAlgL_e_pow_eq_harmonic] using eHarmonicL_C₂_linearIndependent

/-- `L_{-4/3}(sl2)` is unconditionally not C2-cofinite. -/
theorem not_C2Cofinite_simpleSl2QL : ¬ C2Cofinite L43 := by
  intro hfin
  rw [C2Cofinite] at hfin
  haveI : Module.Finite ℂ (A₂ L43) := hfin
  haveI : Finite ℕ := symbolAlgL_e_pow_linearIndependent.finite
  exact not_finite ℕ

/-- The strict Etingof-finite benchmark currently formalized in the repository:
infinite-dimensional C2 algebra, but finite-dimensional zeroth Poisson homology.  This is the
algebraic input used for the quasi-lisse row, not a formal associated-variety theorem. -/
theorem strictEtingofFinite_simpleSl2QL :
    ¬ C2Cofinite L43 ∧ EtingofFinite L43 :=
  ⟨not_C2Cofinite_simpleSl2QL, Sl2Pres.etingofFinite_simpleSl2QL'⟩

end

end VOA.Sl2NonLisse

#print axioms VOA.Sl2NonLisse.form_fHarmonic_word_O₂_zero
#print axioms VOA.Sl2NonLisse.form_fHarmonic_O₂_zero
#print axioms VOA.Sl2NonLisse.exists_O₂_lift
#print axioms VOA.Sl2NonLisse.eHarmonicL_not_mem_O₂
#print axioms VOA.Sl2NonLisse.symbolAlgL_e_pow_linearIndependent
#print axioms VOA.Sl2NonLisse.not_C2Cofinite_simpleSl2QL
#print axioms VOA.Sl2NonLisse.strictEtingofFinite_simpleSl2QL
