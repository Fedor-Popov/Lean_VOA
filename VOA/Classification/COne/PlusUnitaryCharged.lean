/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusUnitaryCert

/-!
# An executable evaluator on the charged sectors of `V_{2m}`

`PlusC2Eval.lean` computes products of charge-`0` states of the lattice VOA `V_{2m}` by
kernel-reducible list operations.  On a charged sector `M(1) ⊗ e^δ` a neutral state acts through
the Heisenberg module whose zero mode `h(0)` is the scalar `c = ⟨δ, ĥ⟩` (`chargeCoord`).  This file
extends the evaluator to that module, keeping `c` **symbolic**: a charged raw polynomial is a
`RawPoly ℕ` in which the variable `0` stands for `c` and the variable `i + 1` for the oscillator
`x_i = h(−i−1)`.  Identities between such polynomials are then polynomial identities in `c` and
the `x_i`, checkable by `decide +kernel`, valid uniformly in the lattice.

## Main results
* `evRc_wordActC` — the executable `wordActC` computes the shifted word fields `wordS c` (the
  normal-ordered products of the shifted generator fields `genS c i`).
* `V2m_smul_evRc` — for a neutral polynomial state `Q` and a charged polynomial state `P`,
  `(Q ⊗ e⁰)₍ₙ₎(P ⊗ e^δ) = polyActC Q (−n−1) w P ⊗ e^δ`, with `c = chargeCoord δ`.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne.PlusUnitary

open VOA HeisenbergN MvPolynomial VOA.SparseRational VOA.LatGen VOA.LatGen.Triplet
  VOA.IntegralLattice PlusC2Eval

/-! ## §1  The executable layer (variable `0` = `c`, variable `i + 1` = `x_i`) -/

/-- Multiply every word by the raw variable `j`. -/
def prependC (j : ℕ) (P : RawPoly ℕ) : RawPoly ℕ := P.map fun t => (t.1, j :: t.2)

/-- `h(n) = n·∂/∂x_{n−1}` on one charged word (`n ≥ 1`; the raw variable of `x_{n−1}` is `n`). -/
def annC (n : ℕ) : List ℕ → RawPoly ℕ
  | [] => []
  | j :: is => (if n = j then [((n : ℚ), is)] else []) ++ prependC j (annC n is)

/-- `Y(x_i, z)_s` on one charged word: the zero mode multiplies by `c`. -/
def fActWC (i : ℕ) (s : ℤ) (w : List ℕ) : RawPoly ℕ :=
  if fMode i s < 0 then [(fCoeff i s, ((-fMode i s - 1).toNat + 1) :: w)]
  else if fMode i s = 0 then [(fCoeff i s, 0 :: w)]
  else scaleR (fCoeff i s) (annC (fMode i s).toNat w)

/-- `Y(x_i, z)_s` on a charged raw polynomial. -/
def fActC (i : ℕ) (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.flatMap fun t => scaleR t.1 (fActWC i s t.2)

/-- The oscillator weight of a charged word (the variable `c` has weight `0`). -/
def wWtC : List ℕ → ℕ
  | [] => 0
  | 0 :: is => wWtC is
  | (j + 1) :: is => j + 1 + wWtC is

/-- `Y(x_{i₁}⋯x_{i_k}𝟙, z)_s` (a neutral word, in the neutral encoding) on a charged raw
polynomial all of whose words have oscillator weight `w`. -/
def wordActC : List ℕ → ℤ → ℕ → RawPoly ℕ → RawPoly ℕ
  | [], s, _, P => if s = 0 then P else []
  | i :: is, s, w, P =>
      (intRange (-((i + 1 + w : ℕ) : ℤ))
          ((max (-1) (((wWt is + w : ℕ) : ℤ) + s)) + ((i + 1 + w : ℕ) : ℤ) + 1).toNat).flatMap
        fun m =>
          if 0 ≤ m then fActC i m (wordActC is (s - m) w P)
          else wordActC is (s - m) ((((i + 1 + w : ℕ) : ℤ) + m).toNat) (fActC i m P)

/-- `Y(Q, z)_s P` for a neutral raw polynomial state `Q` on a charged raw polynomial `P`. -/
def polyActC (Q : RawPoly ℕ) (s : ℤ) (w : ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  Q.flatMap fun t => scaleR t.1 (wordActC t.2 s w P)

/-! ## §2  Semantics -/

variable {r : ℕ} (a : Fin r) (c : ℂ)

/-- The values of the raw variables: `0 ↦ c`, `i + 1 ↦ x_i`. -/
noncomputable def xvc : ℕ → FockN r
  | 0 => MvPolynomial.C c
  | i + 1 => X (i, a)

/-- The value of a charged raw polynomial. -/
noncomputable abbrev evRc (P : RawPoly ℕ) : FockN r := evalRaw (xvc a c) P

theorem evalWordC_cons (j : ℕ) (w : List ℕ) :
    evalWord (xvc a c) (j :: w) = xvc a c j * evalWord (xvc a c) w := by
  simp [evalWord]

theorem evalWordC_nil : evalWord (xvc a c) [] = (1 : FockN r) := by simp [evalWord]

theorem evRc_nil : evRc a c ([] : RawPoly ℕ) = 0 := by simp [evalRaw]

theorem evRc_cons (q : ℚ) (w : List ℕ) (P : RawPoly ℕ) :
    evRc a c ((q, w) :: P) = ((q : ℂ)) • evalWord (xvc a c) w + evRc a c P := by
  simp [evalRaw, MvPolynomial.smul_eq_C_mul]

theorem evRc_append (P Q : RawPoly ℕ) : evRc a c (P ++ Q) = evRc a c P + evRc a c Q :=
  evalRaw_append _ P Q

theorem evRc_flatMap {ι : Type*} (l : List ι) (f : ι → RawPoly ℕ) :
    evRc a c (l.flatMap f) = (l.map fun x => evRc a c (f x)).sum := by
  induction l with
  | nil => simp [evalRaw]
  | cons x xs ih => rw [List.flatMap_cons, evRc_append, ih, List.map_cons, List.sum_cons]

theorem evRc_scaleR (q : ℚ) (P : RawPoly ℕ) : evRc a c (scaleR q P) = ((q : ℂ)) • evRc a c P := by
  rw [scaleR, evRc, evalRaw_scale, algebraMap_rat_mul]

theorem evRc_prependC (j : ℕ) : ∀ P : RawPoly ℕ, evRc a c (prependC j P) = xvc a c j * evRc a c P
  | [] => by simp [prependC, evalRaw]
  | (q, w) :: P => by
    change evRc a c ((q, j :: w) :: prependC j P) = _
    rw [evRc_cons, evRc_cons, evRc_prependC j P, mul_add, mul_smul_comm, evalWordC_cons]

theorem evRc_normR (P : RawPoly ℕ) : evRc a c (normR P) = evRc a c P := by
  rw [normR, evRc, evalRaw_toRaw, evalSparse_normalizeQ]

theorem oscN_pos_C_mul (n : ℕ) (hn : 1 ≤ n) (q : FockN r) :
    oscN r 1 a (n : ℤ) (MvPolynomial.C c * q) = MvPolynomial.C c * oscN r 1 a (n : ℤ) q := by
  rw [oscN_pos _ _ _ (by omega : (0 : ℤ) < n)]
  simp only [LinearMap.smul_apply, pderivLMN_apply, one_smul, Derivation.leibniz, smul_eq_mul,
    MvPolynomial.pderiv_C, mul_zero, add_zero]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  ring

theorem evRc_annC (n : ℕ) (hn : 1 ≤ n) : ∀ w : List ℕ,
    evRc a c (annC n w) = oscN r 1 a (n : ℤ) (evalWord (xvc a c) w)
  | [] => by rw [annC, evRc_nil, evalWordC_nil, oscN_pos_one a n hn]
  | 0 :: is => by
    rw [annC, if_neg (by omega), List.nil_append, evRc_prependC, evRc_annC n hn is,
      evalWordC_cons]
    exact (oscN_pos_C_mul a c n hn _).symm
  | (j + 1) :: is => by
    rw [annC, evRc_append, evRc_prependC, evRc_annC n hn is, evalWordC_cons]
    change _ = oscN r 1 a (n : ℤ) (X (j, a) * evalWord (xvc a c) is)
    rw [oscN_pos_X_mul a n hn]
    change _ + X (j, a) * _ = _
    by_cases h : n = j + 1
    · rw [if_pos h, if_pos h, evRc_cons, evRc_nil, add_zero]
      congr 2
    · rw [if_neg h, if_neg h, evRc_nil, zero_add]

/-! ## §3  The shifted generator fields -/

/-- `Y(x_i, z)` on the Heisenberg module with `h(0) = c`. -/
noncomputable def genS (i : ℕ) : FormalDist (Module.End ℂ (FockN r)) := fun s =>
  genFieldN r 1 a i s + (if fMode i s = 0 then (((fCoeff i s : ℚ) : ℂ) * c) • LinearMap.id else 0)

theorem genS_apply (i : ℕ) (s : ℤ) (q : FockN r) :
    genS a c i s q = genFieldN r 1 a i s q +
      (if fMode i s = 0 then (((fCoeff i s : ℚ) : ℂ) * c) • q else 0) := by
  rw [genS, LinearMap.add_apply]
  split_ifs <;> simp

theorem genS_isField (i : ℕ) : IsField (genS a c i) := by
  intro x
  obtain ⟨B, hB⟩ := genFieldN_isField r 1 a i x
  refine ⟨min B (-(i : ℤ) - 1), fun n hn => ?_⟩
  rw [genS_apply, hB n (by omega), zero_add, if_neg (by simp only [fMode]; omega)]

theorem genS_gradedField (i : ℕ) : GradedFieldN r (genS a c i) ((i : ℤ) + 1) := by
  intro j w p hp
  rw [genS_apply]
  refine Submodule.add_mem _ (genFieldN_gradedField r 1 a i j w p hp) ?_
  split_ifs with h
  · have hj : (i : ℤ) + 1 + w + j = w := by simp only [fMode] at h; omega
    rw [hj]
    exact Submodule.smul_mem _ _ (mem_gradingZN_of_gradingWN hp)
  · exact Submodule.zero_mem _

theorem evRc_fActWC (i : ℕ) (s : ℤ) (w : List ℕ) :
    evRc a c (fActWC i s w) = genS a c i s (evalWord (xvc a c) w) := by
  rw [genS_apply, genFieldN_coeff, LinearMap.smul_apply, ← fCoeff_cast]
  rw [fActWC]
  by_cases hneg : fMode i s < 0
  · have hm : -(s + (i : ℤ)) - 1 = fMode i s := rfl
    rw [if_pos hneg, if_neg (by omega), add_zero, evRc_cons, evRc_nil, add_zero, hm,
      oscN_apply_neg _ _ _ hneg, evalWordC_cons]
    rfl
  · rw [if_neg hneg]
    by_cases hzero : fMode i s = 0
    · have hm : -(s + (i : ℤ)) - 1 = fMode i s := rfl
      rw [if_pos hzero, if_pos hzero, evRc_cons, evRc_nil, add_zero, hm, hzero, oscN_zero,
        LinearMap.zero_apply, smul_zero, zero_add, evalWordC_cons, mul_smul]
      change _ = _ • (c • _)
      rw [show xvc a c 0 = MvPolynomial.C c from rfl, ← MvPolynomial.smul_eq_C_mul]
    · have hm : -(s + (i : ℤ)) - 1 = fMode i s := rfl
      rw [if_neg hzero, if_neg hzero, add_zero, evRc_scaleR, evRc_annC a c (fMode i s).toNat (by omega),
        show (((fMode i s).toNat : ℕ) : ℤ) = fMode i s by omega, hm]

theorem evRc_fActC (i : ℕ) (s : ℤ) : ∀ P : RawPoly ℕ,
    evRc a c (fActC i s P) = genS a c i s (evRc a c P)
  | [] => by simp [fActC, evalRaw]
  | (q, w) :: P => by
    change evRc a c (scaleR q (fActWC i s w) ++ fActC i s P) = _
    rw [evRc_append, evRc_scaleR, evRc_fActWC, evRc_fActC i s P, evRc_cons, map_add, map_smul]

/-! ## §4  Shifted word fields -/

/-- The right-nested normal-ordered product of the shifted generator fields. -/
noncomputable def wordFS : List ℕ → {f : FormalDist (Module.End ℂ (FockN r)) // IsField f}
  | [] => ⟨idFieldN r, idFieldN_isField r⟩
  | i :: is => ⟨nprod (genS_isField a c i) (wordFS is).2, (genS_isField a c i).nprod (wordFS is).2⟩

/-- The shifted field of a word state. -/
noncomputable def wordS (is : List ℕ) : FormalDist (Module.End ℂ (FockN r)) := (wordFS a c is).1

theorem wordS_isField (is : List ℕ) : IsField (wordS a c is) := (wordFS a c is).2

theorem wordS_graded : ∀ is : List ℕ, GradedFieldN r (wordS a c is) (wWt is : ℤ)
  | [] => idFieldN_gradedField r
  | i :: is => by
    have h := GradedFieldN.nprod (genS_isField a c i) (wordS_isField a c is) (genS_gradedField a c i)
      (wordS_graded is)
    rw [show (wWt (i :: is) : ℤ) = (i : ℤ) + 1 + (wWt is : ℤ) by simp [wWt]]
    exact h

theorem evalWordC_mem_grading : ∀ is : List ℕ, evalWord (xvc a c) is ∈ gradingWN r (wWtC is)
  | [] => by rw [evalWordC_nil, wWtC]; exact vacuumN_mem_gradingWN r
  | 0 :: is => by
    rw [evalWordC_cons, wWtC, show xvc a c 0 = MvPolynomial.C c from rfl,
      ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (evalWordC_mem_grading is)
  | (j + 1) :: is => by
    rw [evalWordC_cons, wWtC, mem_gradingWN]
    have hi := wordStateN_mem_gradingWN [(j, a)]
    simp only [wordStateN_cons, wordStateN_nil, mul_one, VOA.LatGen.wordWt_cons,
      VOA.LatGen.wordWt_nil] at hi
    have his := evalWordC_mem_grading is
    rw [mem_gradingWN] at hi his
    exact hi.mul his

/-- A charged raw polynomial all of whose words have oscillator weight `w` has weight `w`. -/
theorem evRc_mem_grading {w : ℕ} : ∀ P : RawPoly ℕ, (∀ t ∈ P, wWtC t.2 = w) →
    evRc a c P ∈ gradingWN r w
  | [], _ => by rw [evRc_nil]; exact Submodule.zero_mem _
  | (q, v) :: P, h => by
    rw [evRc_cons]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (evRc_mem_grading P fun t ht => h t
      (List.mem_cons_of_mem _ ht))
    have := h (q, v) List.mem_cons_self
    rw [← this]
    exact evalWordC_mem_grading a c v

/-- **The charged word-field evaluator is correct.** -/
theorem evRc_wordActC : ∀ (is : List ℕ) (s : ℤ) (w : ℕ) (P : RawPoly ℕ),
    evRc a c P ∈ gradingWN r w → evRc a c (wordActC is s w P) = wordS a c is s (evRc a c P)
  | [], s, w, P, _ => by
    rw [wordActC]
    change evRc a c (if s = 0 then P else []) = idFieldN r s (evRc a c P)
    rw [idFieldN_apply]
    by_cases hs : s = 0
    · rw [if_pos hs, if_pos hs, LinearMap.id_apply]
    · rw [if_neg hs, if_neg hs, evRc_nil, LinearMap.zero_apply]
  | i :: is, s, w, P, hP => by
    have hnp : wordS a c (i :: is) = nprod (genS_isField a c i) (wordS_isField a c is) := rfl
    rw [wordActC, evRc_flatMap, hnp,
      WpTwoAMProof.nprod_apply_grading_bounded (genS_isField a c i) (wordS_isField a c is)
        (i + 1) (wWt is) (by exact_mod_cast genS_gradedField a c i) (wordS_graded a c is) s hP]
    have hN : (-((i + 1 + w : ℕ) : ℤ)) +
        ((((max (-1) (((wWt is + w : ℕ) : ℤ) + s)) + ((i + 1 + w : ℕ) : ℤ) + 1).toNat : ℕ) : ℤ) - 1 =
          max (-1) (((wWt is + w : ℕ) : ℤ) + s) := by
      have h0 := le_max_left (-1 : ℤ) (((wWt is + w : ℕ) : ℤ) + s)
      rw [Int.toNat_of_nonneg (by push_cast at h0 ⊢; omega)]; ring
    rw [show Finset.Icc (-((i + 1 + w : ℕ) : ℤ)) (max (-1) (((wWt is + w : ℕ) : ℤ) + s)) =
        Finset.Icc (-((i + 1 + w : ℕ) : ℤ)) ((-((i + 1 + w : ℕ) : ℤ)) +
          ((((max (-1) (((wWt is + w : ℕ) : ℤ) + s)) + ((i + 1 + w : ℕ) : ℤ) + 1).toNat : ℕ) : ℤ) - 1)
        from by rw [hN],
      sum_Icc_intRange]
    congr 1
    apply List.map_congr_left
    intro m _
    rw [normalOrdered_apply]
    by_cases hm0 : 0 ≤ m
    · rw [if_pos hm0, if_pos hm0, Module.End.mul_apply, evRc_fActC, evRc_wordActC is (s - m) w P hP]
    · rw [if_neg hm0, if_neg hm0, Module.End.mul_apply]
      have hgrade := (genS_gradedField a c i).mem_gradingZN m (w : ℤ)
        (mem_gradingZN_of_gradingWN hP)
      have hnext : evRc a c (fActC i m P) ∈ gradingWN r ((((i + 1 + w : ℕ) : ℤ) + m).toNat) := by
        rw [evRc_fActC]
        by_cases hd : 0 ≤ ((i + 1 + w : ℕ) : ℤ) + m
        · rw [show ((i : ℤ) + 1 + (w : ℤ) + m) = ((i + 1 + w : ℕ) : ℤ) + m by push_cast; ring,
            gradingZN_of_nonneg hd] at hgrade
          exact hgrade
        · have hd' : (i : ℤ) + 1 + (w : ℤ) + m < 0 := by push_cast at hd; omega
          rw [gradingZN_of_neg hd', Submodule.mem_bot] at hgrade
          rw [hgrade]; exact Submodule.zero_mem _
      rw [evRc_wordActC is (s - m) _ (fActC i m P) hnext, evRc_fActC]

/-! ## §5  The lattice side: neutral fields on a charged sector -/

section Lattice

variable {L : IntegralLattice}

/-- A lattice field restricts on the sector `M(1) ⊗ e^δ` to the Fock field `f`. -/
def ChargedLift (δ : L.carrier) (F : FormalDist (Module.End ℂ (LatModuleGen L)))
    (f : FormalDist (Module.End ℂ (FockN (rank L)))) : Prop :=
  ∀ (j : ℤ) (q : FockN (rank L)), F j (latStateGen L q δ) = latStateGen L (f j q) δ

theorem genFieldLatGen_chargedLift (a : Fin (rank L)) (i : ℕ) (δ : L.carrier) :
    ChargedLift δ (genFieldLatGen L a i) (genS a (chargeCoord L δ a) i) := by
  intro j q
  change ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (alphaLatGen L a)) j) (latStateGen L q δ) = _
  rw [VertexOperatorAlgebra.deriv_pow_apply, ← Int.cast_smul_eq_zsmul ℂ, LinearMap.smul_apply,
    LinearMap.smul_apply, alphaLatGen_tmul, genS_apply, genFieldN_coeff, LinearMap.smul_apply,
    currentN_apply, latStateGen_add_boson, latStateGen_csmul, smul_add, smul_add, smul_smul]
  have hiff : (j + (i : ℤ) = -1) ↔ fMode i j = 0 := by simp only [fMode]; omega
  congr 1
  · rw [mul_comm]
  · by_cases h : j + (i : ℤ) = -1
    · rw [if_pos h, if_pos (hiff.mp h), latStateGen_csmul, fCoeff_cast]
      simp only [smul_smul]
      congr 1
      ring
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h')), smul_zero]
      simp [latStateGen]

theorem ChargedLift.nprod {δ : L.carrier} {F G : FormalDist (Module.End ℂ (LatModuleGen L))}
    {f g : FormalDist (Module.End ℂ (FockN (rank L)))}
    (hF : ChargedLift δ F f) (hG : ChargedLift δ G g)
    (hFfield : IsField F) (hGfield : IsField G) (hffield : IsField f) (hgfield : IsField g) :
    ChargedLift δ (VOA.nprod hFfield hGfield) (VOA.nprod hffield hgfield) := by
  intro s q
  have hno : ∀ m : ℤ, normalOrdered F G m (s - m) (latStateGen L q δ) =
      mkEα L δ (normalOrdered f g m (s - m) q) := by
    intro m
    simp only [normalOrdered_apply]
    by_cases hm : 0 ≤ m
    · rw [if_pos hm, Module.End.mul_apply, if_pos hm, Module.End.mul_apply, hG, hF]; rfl
    · rw [if_neg hm, Module.End.mul_apply, if_neg hm, Module.End.mul_apply, hF, hG]; rfl
  rw [nprod_apply, nprod_apply, finsum_congr hno,
    ← map_finsum (mkEα L δ) (normalOrdered_diag_support_finite hffield hgfield s q)]
  rfl

theorem YwordLatGen_chargedLift (a : Fin (rank L)) (δ : L.carrier) :
    ∀ l : List ℕ, ChargedLift δ (YwordLatGen L (l.map fun i => (i, a)) 0)
      (wordS a (chargeCoord L δ a) l)
  | [] => by
    intro j q
    rw [List.map_nil, YwordLatGen_nil, Yeαvec_zero_apply]
    change _ = latStateGen L (idFieldN (rank L) j q) δ
    rw [idFieldN_apply]
    split_ifs
    · rfl
    · simp [latStateGen]
  | i :: is => by
    rw [List.map_cons, YwordLatGen_cons]
    exact (genFieldLatGen_chargedLift a i δ).nprod (YwordLatGen_chargedLift a δ is)
      (genFieldLatGen_isField L a i) (YwordLatGen_isField L _ 0)
      (genS_isField a _ i) (wordS_isField a _ is)

theorem wordStateN_map (a : Fin (rank L)) :
    ∀ l : List ℕ, wordStateN (l.map fun i => (i, a)) = evalWord (xv a) l
  | [] => by rw [List.map_nil, wordStateN_nil, evalWord_nil]
  | i :: is => by rw [List.map_cons, wordStateN_cons, wordStateN_map a is, evalWord_cons]

end Lattice

/-! ## §6  Products in `V_{2m}` -/

theorem V2m_smul_word_charged (m : ℕ) (hm : 1 ≤ m) (v : List ℕ) (n : ℤ) (δ : (latP m).carrier)
    (q : FockN (rank (latP m))) :
    (V2m m hm).smul (latStateGen (latP m) (evalWord (xv (LatMod.a0 m)) v) 0) n (latStateGen (latP m) q δ) =
      latStateGen (latP m) (wordS (LatMod.a0 m) (chargeCoord (latP m) δ (LatMod.a0 m)) v (-n - 1) q) δ := by
  rw [PreVertexAlgebra.smul_def, mode_apply]
  have hw : latStateGen (latP m) (evalWord (xv (LatMod.a0 m)) v) 0 =
      wordStateLatGen (latP m) (v.map fun i => (i, LatMod.a0 m)) 0 := by
    rw [wordStateLatGen_eq, wordStateN_map]; rfl
  rw [hw]
  change YfullGen (latP m) (latP_even m) (latP_posDef m hm) _ (-n - 1) _ = _
  rw [YfullGen_word]
  exact YwordLatGen_chargedLift (LatMod.a0 m) δ v (-n - 1) q

/-- **The charged evaluator computes `V_{2m}` products** `(Q ⊗ e⁰)₍ₙ₎(P ⊗ e^δ)`, `c = ⟨δ, ĥ⟩`. -/
theorem V2m_smul_evRc (m : ℕ) (hm : 1 ≤ m) (Q P : RawPoly ℕ) (n : ℤ) (w : ℕ) (δ : (latP m).carrier)
    (hP : ∀ t ∈ P, wWtC t.2 = w) :
    (V2m m hm).smul (latStateGen (latP m) (evR (LatMod.a0 m) Q) 0) n
        (latStateGen (latP m) (evRc (LatMod.a0 m) (chargeCoord (latP m) δ (LatMod.a0 m)) P) δ) =
      latStateGen (latP m) (evRc (LatMod.a0 m) (chargeCoord (latP m) δ (LatMod.a0 m))
        (polyActC Q (-n - 1) w P)) δ := by
  induction Q with
  | nil =>
    rw [evR_nil, polyActC, List.flatMap_nil, evRc_nil]
    simp [latStateGen]
  | cons t Q ih =>
    rcases t with ⟨q, v⟩
    change _ = latStateGen (latP m) (evRc _ _ (scaleR q (wordActC v (-n - 1) w P) ++ polyActC Q (-n - 1) w P)) δ
    rw [evR_cons, latStateGen_add_boson, latStateGen_csmul, PreVertexAlgebra.smul_add_left,
      PreVertexAlgebra.smul_smul_left, ih, V2m_smul_word_charged, evRc_append, evRc_scaleR,
      evRc_wordActC _ _ v (-n - 1) w P (evRc_mem_grading _ _ P hP), latStateGen_add_boson,
      latStateGen_csmul]

end VOA.Classification.COne.PlusUnitary
