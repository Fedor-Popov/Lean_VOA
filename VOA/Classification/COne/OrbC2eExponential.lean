import VOA.Classification.COne.OrbC2cCharged

/-! # Certified charged-left lattice products

The raw variable 0 denotes the left charge coordinate, and variable i+1
denotes h(-i-1). Unlike the neutral-left evaluator, this computes the
exponential field on arbitrary oscillator-dressed charged states.
The semantic bridge retains the actual lattice cocycle and charge shift.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

namespace VOA.Classification.COne.OrbC2e
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary LatMod

/-- Newton recursion for the creation exponential, with symbolic left charge. -/
def schurR : ℕ → RawPoly ℕ
  | 0 => [(1, [])]
  | n+1 => normR (scaleR ((n+1 : ℚ)⁻¹)
      ((List.range (n+1)).flatMap fun i =>
        prependC 0 (prependC (i+1) (schurR (n-i)))))

/-- Exponential dressing on one word; no homogeneity hypothesis is needed. -/
def expWordR : List ℕ → ℤ → RawPoly ℕ
  | [], s => if 0 ≤ s then schurR s.toNat else []
  | 0 :: w, s => prependC 0 (expWordR w s)
  | (i+1) :: w, s => normR (prependC (i+1) (expWordR w s) ++
      scaleR (-1) (prependC 0 (expWordR w (s+i+1))))

def expPolyR (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  normR (P.flatMap fun t => scaleR t.1 (expWordR t.2 s))

theorem evRc_flatMap_range {r : ℕ} (a : Fin r) (c : ℂ)
    (n : ℕ) (f : ℕ → RawPoly ℕ) :
    evRc a c ((List.range n).flatMap f) = ∑ i ∈ Finset.range n, evRc a c (f i) := by
  induction n with
  | zero => simp [evRc_nil]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      evRc_append, ih, Finset.sum_range_succ]

/-- The executable creation coefficients equal the actual vector Schur states. -/
theorem evRc_schurR (m : ℕ) (β : (latP m).carrier) (n : ℕ) :
    evRc (a0 m) (chargeCoord (latP m) β (a0 m)) (schurR n) =
      vSchur (latP m) β n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [schurR, evRc_cons, evRc_nil, evalWordC_nil, vSchur_zero]
    | succ n =>
      rw [schurR, evRc_normR, evRc_scaleR, evRc_flatMap_range, vSchur_succ]
      push_cast
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [evRc_prependC, evRc_prependC, ih (n-i) (by omega), PlusC2.vVar_rankOne]
      simp only [xvc, MvPolynomial.smul_eq_C_mul]
      ring

theorem EEVec_X_mul (L : IntegralLattice) (β : L.carrier)
    (a : Fin (rank L)) (i : ℕ) (s : ℤ) (p : FockN (rank L)) :
    EEVec L β s (X (i,a) * p) =
      X (i,a) * EEVec L β s p - chargeCoord L β a • EEVec L β (s+i+1) p := by
  have h := congrArg (fun f : Module.End ℂ (FockN (rank L)) => f p)
    (alphaFieldGen_comm_EEVec L a β (i : ℤ) s)
  rw [if_neg (by omega)] at h
  simp only [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, currentN_apply] at h
  have ho (q : FockN (rank L)) :
      oscN (rank L) 1 a (-(i : ℤ)-1) q = X (i,a) * q := by
    rw [oscN_apply_neg _ _ _ (by omega)]
    simp
  rw [ho, ho] at h
  linear_combination -h

/-- Correctness on a word, including the annihilation contribution. -/
theorem evRc_expWordR (m : ℕ) (β : (latP m).carrier) :
    ∀ (w : List ℕ) (s : ℤ),
      evRc (a0 m) (chargeCoord (latP m) β (a0 m)) (expWordR w s) =
        EEVec (latP m) β s
          (evalWord (xvc (a0 m) (chargeCoord (latP m) β (a0 m))) w)
  | [], s => by
    rw [evalWordC_nil, show (1 : FockN _) = vacuumN _ from rfl,
      EEVec_vacuum, expWordR]
    split_ifs
    · exact evRc_schurR m β _
    · exact evRc_nil _ _
  | 0 :: w, s => by
    rw [expWordR, evRc_prependC, evRc_expWordR m β w s, evalWordC_cons]
    simp only [xvc, ← MvPolynomial.smul_eq_C_mul, map_smul]
  | (i+1) :: w, s => by
    rw [expWordR, evRc_normR, evRc_append, evRc_prependC, evRc_scaleR,
      evRc_prependC, evRc_expWordR m β w s, evRc_expWordR m β w (s+i+1),
      evalWordC_cons]
    simp only [xvc, Rat.cast_neg, Rat.cast_one, neg_one_smul,
      ← MvPolynomial.smul_eq_C_mul, ← sub_eq_add_neg]
    exact (EEVec_X_mul _ _ _ _ _ _).symm

/-- Certified exponential action on any polynomial, including mixed weights. -/
theorem evRc_expPolyR (m : ℕ) (β : (latP m).carrier) (s : ℤ) (P : RawPoly ℕ) :
    evRc (a0 m) (chargeCoord (latP m) β (a0 m)) (expPolyR s P) =
      EEVec (latP m) β s (evRc (a0 m) (chargeCoord (latP m) β (a0 m)) P) := by
  rw [expPolyR, evRc_normR, evRc_flatMap]
  induction P with
  | nil => simp [evRc_nil]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    rw [List.map_cons, List.sum_cons, evRc_cons, map_add, map_smul,
      evRc_scaleR, evRc_expWordR, ih]

/-- Charged-left, charged-right product in the actual lattice VOA.
Both the cocycle and the output charge are explicit. -/
theorem V2m_charge_smul_evRc (m : ℕ) (hm : 1 ≤ m)
    (β γ : (latP m).carrier) (n : ℤ) (P : RawPoly ℕ) :
    (V2m m hm).smul (latChargeGen (latP m) β) n
      (latStateGen (latP m) (evRc (a0 m) (chargeCoord (latP m) β (a0 m)) P) γ) =
    latticeCocycle (latP m) β γ • latStateGen (latP m)
      (evRc (a0 m) (chargeCoord (latP m) β (a0 m))
        (expPolyR (-n-1-(latP m).form β γ) P)) (β+γ) := by
  rw [V2m, latVOA_smul_latChargeGen_state, evRc_expPolyR]

/-- All pure exponential products, at every integral mode. -/
theorem V2m_charge_smul_charge (m : ℕ) (hm : 1 ≤ m)
    (β γ : (latP m).carrier) (n : ℤ) :
    (V2m m hm).smul (latChargeGen (latP m) β) n (latChargeGen (latP m) γ) =
    latticeCocycle (latP m) β γ • latStateGen (latP m)
      (evRc (a0 m) (chargeCoord (latP m) β (a0 m))
        (if 0 ≤ -n-1-(latP m).form β γ then
          schurR (-n-1-(latP m).form β γ).toNat else [])) (β+γ) := by
  rw [V2m, show latChargeGen (latP m) γ =
    latStateGen (latP m) (vacuumN _) γ from rfl,
    latVOA_smul_latChargeGen_state, EEVec_vacuum]
  split_ifs
  · rw [evRc_schurR]
  · rw [evRc_nil]

end VOA.Classification.COne.OrbC2e
