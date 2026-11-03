import VOA.Classification.COne.OrbOctaRCAdjoint
import VOA.Classification.COne.OrbOctaRCExp
import VOA.Classification.COne.OrbRat4Normal

/-! Exact rational evaluation of the charged Hermitian probes. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.SparseRational HeisenbergN MvPolynomial OrbSpan OrbRat4
  PlusC2Eval PlusUnitary PlusC2 OrbC2e OrbC2g OrbC2h

def wordNorm : List ℕ → ℕ
  | [] => 1
  | 0 :: w => wordNorm w
  | (i + 1) :: w => wordNorm w * ((i + 1) * (w.count (i + 1) + 1))

theorem fw_oscExp {r : ℕ} (a : Fin r) (w : List ℕ) :
    fw (oscExp a w) = wordNorm w := by
  induction w with
  | nil => simp [oscExp, fw, wordNorm]
  | cons i w ih =>
    cases i with
    | zero => exact ih
    | succ i => rw [oscExp, add_comm, fw_add_single, ih, oscExp_apply]; rfl

theorem oscillators_count (w : List ℕ) (i : ℕ) :
    (oscillators w).count i = w.count (i + 1) := by
  induction w with
  | nil => rfl
  | cons j w ih => cases j <;> simp [oscillators, ih, List.count_cons]

theorem oscExp_apply_other {r : ℕ} (a b : Fin r) (hb : b ≠ a) (i : ℕ) (w : List ℕ) :
    oscExp a w (i, b) = 0 := by
  induction w with
  | nil => rfl
  | cons j w ih => cases j <;> simp [oscExp, ih, hb]

theorem oscExp_eq_iff {r : ℕ} (a : Fin r) (w v : List ℕ) :
    oscExp a w = oscExp a v ↔ (oscillators w).Perm (oscillators v) := by
  constructor
  · intro h
    apply List.perm_iff_count.mpr
    intro i
    rw [oscillators_count, oscillators_count]
    simpa only [oscExp_apply] using congrArg (fun μ => μ (i, a)) h
  · intro h
    ext ⟨i, b⟩
    by_cases hb : b = a
    · subst b
      rw [oscExp_apply, oscExp_apply, ← oscillators_count, ← oscillators_count]
      exact List.perm_iff_count.mp h i
    · rw [oscExp_apply_other _ _ hb, oscExp_apply_other _ _ hb]

theorem fockForm_word {r : ℕ} (a : Fin r) (c : ℂ) (hc : starRingEnd ℂ c = c)
    (w v : List ℕ) :
    fockForm (evalWord (xvc a c) w) (evalWord (xvc a c) v) =
      if (oscillators w).Perm (oscillators v) then
        (wordNorm w : ℂ) * c ^ (w.count 0 + v.count 0) else 0 := by
  rw [evalWord_xvc, evalWord_xvc, C_mul_monomial, C_mul_monomial,
    mul_one, mul_one, fockForm_monomial, fw_oscExp]
  simp only [oscExp_eq_iff, map_pow, hc, pow_add, mul_assoc]

/-- The even and odd powers of the charge coordinate are retained separately. -/
def pairTerm (t u : ℚ × List ℕ) : ℚ × ℚ :=
  if (oscillators t.2).Perm (oscillators u.2) then
    let n := t.2.count 0 + u.2.count 0
    let q := t.1 * u.1 * wordNorm t.2 * 2 ^ (n / 2)
    if n % 2 = 0 then (q, 0) else (0, q)
  else (0, 0)

noncomputable def pairValue (c : ℂ) : (ℚ × ℚ) →+ ℂ where
  toFun p := (p.1 : ℂ) + c * (p.2 : ℂ)
  map_zero' := by simp
  map_add' := by intros; simp; ring

theorem power_two_reduce (c : ℂ) (hc : c * c = ((2 : ℚ) : ℂ)) (n : ℕ) :
    c ^ n = (2 : ℂ) ^ (n / 2) * (if n % 2 = 0 then 1 else c) := by
  have hc' : c ^ 2 = 2 := by simpa only [pow_two, Rat.cast_ofNat] using hc
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  calc
    c ^ n = c ^ (n % 2 + 2 * (n / 2)) := by rw [Nat.mod_add_div]
    _ = c ^ (n % 2) * (c ^ 2) ^ (n / 2) := by rw [pow_add, pow_mul]
    _ = _ := by rcases hn with hn | hn <;> simp [hn, hc', mul_comm]

theorem pairTerm_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) (hr : starRingEnd ℂ c = c)
    (t u : ℚ × List ℕ) :
    fockForm ((t.1 : ℂ) • evalWord (xvc a c) t.2)
      ((u.1 : ℂ) • evalWord (xvc a c) u.2) = pairValue c (pairTerm t u) := by
  rw [(fockForm (r := r)).map_smul (t.1 : ℂ) (evalWord (xvc a c) t.2),
    LinearMap.smul_apply, LinearMap.map_smulₛₗ, fockForm_word _ _ hr]
  simp only [smul_eq_mul, map_ratCast]
  by_cases hp : (oscillators t.2).Perm (oscillators u.2)
  · simp only [pairTerm, if_pos hp, pairValue, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [power_two_reduce _ hc]
    split_ifs <;> push_cast <;> ring
  · simp [pairTerm, hp, pairValue]

def pairRaw (P Q : RawPoly ℕ) : ℚ × ℚ :=
  (P.flatMap fun t => Q.map fun u => pairTerm t u).sum

theorem pairRaw_append (P Q R : RawPoly ℕ) :
    pairRaw (P ++ Q) R = pairRaw P R + pairRaw Q R := by
  simp [pairRaw]

theorem pairRaw_nil (P : RawPoly ℕ) : pairRaw [] P = 0 := by
  simp [pairRaw]

theorem pairRaw_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) (hr : starRingEnd ℂ c = c)
    (P Q : RawPoly ℕ) :
    fockForm (evRc a c P) (evRc a c Q) = pairValue c (pairRaw P Q) := by
  induction P with
  | nil => simp [pairRaw, evRc_nil]
  | cons t P ih =>
    rw [evRc_cons, map_add, LinearMap.add_apply, ih]
    simp only [pairRaw, List.flatMap_cons, List.sum_append, map_add] at *
    congr 1
    clear ih
    induction Q with
    | nil => simp [evRc_nil]
    | cons u Q ihQ =>
      rw [evRc_cons, map_add, pairTerm_sound _ _ hc hr, ihQ]
      simp

theorem lattice_pair_right_sector (L : VOA.IntegralLattice)
    (x : VOA.LatGen.LatModuleGen L) (d : L.carrier) (p : FockN (VOA.IntegralLattice.rank L)) :
    latForm L x (VOA.LatGen.latStateGen L p d) = fockForm (latE L x d) p := by
  classical
  simp only [latForm_apply, latPair, latE_latStateGen]
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro hd
    rw [Finsupp.notMem_support_iff.mp hd]
    simp

theorem sector_form (d e : ℤ)
    (p q : FockN (VOA.IntegralLattice.rank (VOA.LatGen.Triplet.latP 1))) :
    (v2mVirUnitary 1 le_rfl).form (sector d p) (sector e q) =
      if e = d then fockForm p q else 0 := by
  change latForm (VOA.LatGen.Triplet.latP 1) (VOA.LatGen.latStateGen _ p d)
    (VOA.LatGen.latStateGen _ q e) = _
  rw [lattice_pair_right_sector, latE_latStateGen]
  split_ifs <;> simp_all

theorem cα_real : starRingEnd ℂ (PlusC2.cα 1) = PlusC2.cα 1 := by
  simp [PlusC2.cα, VOA.LatGen.chargeCoord, Complex.conj_ofReal]

theorem sector_pairRaw (d : ℤ) (P Q : RawPoly ℕ) :
    (v2mVirUnitary 1 le_rfl).form
      (sector d (evRc (LatMod.a0 1) (PlusC2.cα 1) P))
      (sector d (evRc (LatMod.a0 1) (PlusC2.cα 1) Q)) =
        pairValue (PlusC2.cα 1) (pairRaw P Q) := by
  rw [sector_form, if_pos rfl]
  exact pairRaw_sound _ _ charge_square_two cα_real _ _

end VOA.Classification.COne.OrbOctaRC
