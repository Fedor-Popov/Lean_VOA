import VOA.DeligneAudit.D4FusionContactAllMModelDegreeBound
import VOA.DeligneAudit.D4FusionContactM2Dimension
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleComponentActual
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleActual

/-! Two facts about the commutative model ideals. (1) The concrete m=2 ideal
`m2ModelIdeal` lies in `AllM.modelIdeal 2`: each of the seven m=2 seeds is a
nonzero multiple of an admissible all-m seed coefficient, and the derivations
agree. (2) For every m, `AllM.modelIdeal m` is homogeneous for the current
weight (mode index): every generator is weighted homogeneous, so each weighted
component of an ideal member stays in the ideal. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules (modeWeight)
noncomputable section

/-- The current weight as an integer weight (mode index). -/
abbrev cw (m : ℕ) : Vars m → ℤ := modeWeight m (fun _ => 0) 1

/-- Binomial coefficients of a power of a linear power series. -/
theorem coeff_linear_pow {R : Type*} [CommRing R] (A B : R) (r s : ℕ) :
    PowerSeries.coeff s ((PowerSeries.C A + PowerSeries.C B * PowerSeries.X) ^ r) =
      (r.choose s : R) * A ^ (r - s) * B ^ s := by
  rw [add_comm, add_pow, map_sum]
  have hterm : ∀ k ∈ Finset.range (r + 1),
      PowerSeries.coeff s ((PowerSeries.C B * PowerSeries.X) ^ k * PowerSeries.C A ^ (r - k) *
        (r.choose k : PowerSeries R)) =
        if s = k then (r.choose k : R) * A ^ (r - k) * B ^ k else 0 := by
    intro k _
    have he : (PowerSeries.C B * PowerSeries.X) ^ k * PowerSeries.C A ^ (r - k) *
        (r.choose k : PowerSeries R) =
        PowerSeries.C ((r.choose k : R) * A ^ (r - k) * B ^ k) * PowerSeries.X ^ k := by
      simp only [mul_pow, map_mul, map_pow, map_natCast]
      ring
    rw [he, PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range] at h
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul]

theorem current_two (a : Fin 9) :
    AllM.current 2 a = PowerSeries.C (MvPolynomial.X (a, 0)) +
      PowerSeries.C (MvPolynomial.X (a, 1)) * PowerSeries.X := by
  ext n
  rw [AllM.current, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X]
  rcases n with _ | _ | n <;> simp [modeX]

theorem allm_seedPoly_two (b : Bool) (r s : ℕ) (h : 1 ≤ r ∧ AllM.seedThreshold 2 b < r + s) :
    AllM.seedPoly 2 ⟨(b, r, s), h⟩ = (r.choose s : MvPolynomial (Vars 2) ℂ) *
      MvPolynomial.X (AllM.seedColor b, 0) ^ (r - s) *
        MvPolynomial.X (AllM.seedColor b, 1) ^ s := by
  change PowerSeries.coeff s (AllM.current 2 (AllM.seedColor b) ^ r) = _
  rw [current_two, coeff_linear_pow]

theorem mem_of_natCast_mul {σ : Type*} {I : Ideal (MvPolynomial σ ℂ)}
    {p : MvPolynomial σ ℂ} {c : ℕ} (hc : c ≠ 0) (h : (c : MvPolynomial σ ℂ) * p ∈ I) :
    p ∈ I := by
  have h1 := I.mul_mem_left (MvPolynomial.C ((c : ℂ)⁻¹)) h
  rwa [← mul_assoc, ← map_natCast (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ) c,
    ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hc), map_one, one_mul] at h1

theorem seed_two_mem (c : ℕ) (hc : c ≠ 0) (b : Bool) (r s : ℕ)
    (h : 1 ≤ r ∧ AllM.seedThreshold 2 b < r + s) (p : MvPolynomial (Vars 2) ℂ)
    (hp : (c : MvPolynomial (Vars 2) ℂ) * p = (r.choose s : MvPolynomial (Vars 2) ℂ) *
      MvPolynomial.X (AllM.seedColor b, 0) ^ (r - s) *
        MvPolynomial.X (AllM.seedColor b, 1) ^ s) :
    p ∈ AllM.candidateIdeal 2 := by
  apply mem_of_natCast_mul hc
  rw [hp, ← allm_seedPoly_two b r s h]
  exact AllM.seed_mem_candidate 2 ⟨(b, r, s), h⟩

/-- Each m=2 seed is a nonzero multiple of an admissible all-m seed coefficient. -/
theorem m2_seedPoly_mem (j : Fin 7) : seedPoly j ∈ AllM.candidateIdeal 2 := by
  fin_cases j
  · exact seed_two_mem 1 (by norm_num) false 3 0 (by decide) _
      (by simp [seedPoly, seedList, polyWord, AllM.seedColor]; ring)
  · exact seed_two_mem 2 (by norm_num) false 2 1 (by decide) _
      (by simp [seedPoly, seedList, polyWord, AllM.seedColor]; ring)
  · exact seed_two_mem 1 (by norm_num) false 2 2 (by decide) _
      (by simp [seedPoly, seedList, polyWord, AllM.seedColor]; ring)
  · exact seed_two_mem 1 (by norm_num) true 5 0 (by decide) _
      (by simp [seedPoly, seedList, polyWord, AllM.seedColor]; ring)
  · exact seed_two_mem 4 (by norm_num) true 4 1 (by decide) _
      (by simp [seedPoly, seedList, polyWord, AllM.seedColor]; ring)
  · exact seed_two_mem 3 (by norm_num) true 3 2 (by decide) _
      (by simp [seedPoly, seedList, polyWord, AllM.seedColor]; ring)
  · exact seed_two_mem 1 (by norm_num) true 3 3 (by decide) _
      (by simp [seedPoly, seedList, polyWord, AllM.seedColor]; ring)

theorem allm_derivWord_mem {m : ℕ} {p : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ AllM.candidateIdeal m) (l : List (AllM.DerivIndex m)) :
    AllM.derivWord m l p ∈ AllM.candidateIdeal m := by
  induction l with
  | nil => exact hp
  | cons d l ih => exact AllM.candidateIdeal_deriv m d ih

theorem m2_derivWord_eq (l : List DerivIndex) (p : MvPolynomial (Vars 2) ℂ) :
    derivWord l p = AllM.derivWord 2 l p := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      change candidateDeriv d (derivWord l p) = AllM.candidateDeriv 2 d (AllM.derivWord 2 l p)
      rw [ih]
      cases d <;> rfl

theorem candidateIdeal_le_allM : candidateIdeal ≤ AllM.candidateIdeal 2 := by
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨l, j⟩, rfl⟩
  change derivWord l (seedPoly j) ∈ _
  rw [m2_derivWord_eq]
  exact allm_derivWord_mem (m2_seedPoly_mem j) l

/-- MAIN (1): the concrete m=2 model ideal lies in the all-m model ideal. -/
theorem m2ModelIdeal_le_allM : m2ModelIdeal ≤ AllM.modelIdeal 2 :=
  sup_le_sup_right candidateIdeal_le_allM _

/-! ### Current-weight homogeneity of the all-m model ideal -/

theorem allm_seedPoly_graded (m : ℕ) (j : AllM.SeedIndex m) :
    (AllM.seedPoly m j).IsWeightedHomogeneous (cw m) (j.val.2.2 : ℤ) := by
  have h := AllMCountResearch.LeviRules.color_seed_graded ℂ m (fun _ => 0) 1
    (AllM.seedColor j.val.1) j.val.2.1 j.val.2.2
  have he : ((j.val.2.1 : ℤ) * (fun _ : Fin 9 => (0 : ℤ)) (AllM.seedColor j.val.1) +
      1 * (j.val.2.2 : ℤ)) = (j.val.2.2 : ℤ) := by simp
  rw [he] at h
  exact h

theorem allm_candidateDeriv_graded (m : ℕ) (d : AllM.DerivIndex m)
    {p : MvPolynomial (Vars m) ℂ} {n : ℤ} (hp : p.IsWeightedHomogeneous (cw m) n) :
    ∃ n', (AllM.candidateDeriv m d p).IsWeightedHomogeneous (cw m) n' := by
  cases d with
  | inl x =>
      have h := AllMCountResearch.LeviRules.deriv_graded ℂ m (fun _ => 0) 1 0
        (Fin.castAdd 8 x.1) x.2.val (fun _ => Or.inr (by simp)) hp
      rw [AllMCountResearch.LeviRules.deriv_g0] at h
      exact ⟨_, h⟩
  | inr x =>
      have h := AllMCountResearch.LeviRules.deriv_graded ℂ m (fun _ => 0) 1 0
        (Fin.natAdd 10 x.1) x.2.val (fun _ => Or.inr (by simp)) hp
      rw [AllMCountResearch.LeviRules.deriv_contact] at h
      exact ⟨_, h⟩

theorem allm_derivWord_graded (m : ℕ) (j : AllM.SeedIndex m) :
    ∀ l : List (AllM.DerivIndex m),
      ∃ n, (AllM.derivWord m l (AllM.seedPoly m j)).IsWeightedHomogeneous (cw m) n := by
  intro l
  induction l with
  | nil => exact ⟨_, allm_seedPoly_graded m j⟩
  | cons d l ih =>
      obtain ⟨n, hn⟩ := ih
      exact allm_candidateDeriv_graded m d hn

theorem polyWord_graded (m : ℕ) (l : List (Vars m)) :
    (polyWord l).IsWeightedHomogeneous (cw m) ((l.map fun x => (x.2.val : ℤ)).sum) := by
  induction l with
  | nil => simpa [polyWord] using MvPolynomial.isWeightedHomogeneous_one ℂ (cw m)
  | cons x l ih =>
      have h := (MvPolynomial.isWeightedHomogeneous_X ℂ (cw m) x).mul ih
      change (MvPolynomial.X x * polyWord l).IsWeightedHomogeneous _ _
      convert h using 1
      simp [modeWeight]

/-- The generators of the all-m model ideal, as one family. -/
def modelGen (m : ℕ) :
    (List (AllM.DerivIndex m) × AllM.SeedIndex m) ⊕
      {l : List (Vars m) // 2 * m + 1 ≤ l.length} → MvPolynomial (Vars m) ℂ :=
  Sum.elim (fun x => AllM.derivWord m x.1 (AllM.seedPoly m x.2)) (fun l => polyWord l.val)

theorem modelIdeal_eq_span (m : ℕ) :
    AllM.modelIdeal m = Ideal.span (Set.range (modelGen m)) := by
  rw [AllM.modelIdeal, AllM.candidateIdeal, highWordIdeal, ← Ideal.span_union, modelGen,
    Set.Sum.elim_range]
  congr 2
  ext p
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩
  · rintro ⟨⟨l, hl⟩, rfl⟩
    exact ⟨l, hl, rfl⟩

theorem modelGen_graded (m : ℕ) (i) :
    ∃ n, (modelGen m i).IsWeightedHomogeneous (cw m) n := by
  rcases i with ⟨l, j⟩ | ⟨l, _⟩
  · exact allm_derivWord_graded m j l
  · exact ⟨_, polyWord_graded m l⟩

/-- MAIN (2): every current-weight component of a model-ideal member is a member. -/
theorem modelIdeal_component_mem (m : ℕ) {p : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ AllM.modelIdeal m) (n : ℤ) :
    MvPolynomial.weightedHomogeneousComponent (cw m) n p ∈ AllM.modelIdeal m := by
  rw [modelIdeal_eq_span] at hp ⊢
  have h := AllMCountResearch.LeviRules.ideal_component_mem_matching_span (cw m) (modelGen m)
    (fun i => (modelGen_graded m i).choose) (fun i => (modelGen_graded m i).choose_spec) hp n
  have h2 : MvPolynomial.weightedHomogeneousComponent (cw m) n p ∈
      (Ideal.span (Set.range (modelGen m))).restrictScalars ℂ := by
    refine (Submodule.span_le.mpr ?_) h
    rintro _ ⟨i, e, -, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  exact h2

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.m2ModelIdeal_le_allM
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.modelIdeal_component_mem
