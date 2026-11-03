import VOA.Classification.COne.OrbIcoWJetDP
import VOA.Classification.COne.OrbIcoWJetAlong
import VOA.Classification.COne.OrbIcoWJetMain

/-! Actual coefficient-sequence specialization from exact undivided jet certificates. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoW
open OrbOdd Polynomial Filter Topology

/-- Every earlier coefficient retains the precision required by a later recurrence. -/
theorem precision_earlier (self : Bool) (n j : ℕ) (hj : j<n) :
    precisionBefore self n ≤ precisionAfter self j := by
  cases self <;> simp only [precisionBefore,precisionAfter,denominatorOrder,
    Bool.false_eq_true,if_false,if_true]
  all_goals split_ifs <;> omega

/-- Every stored denominator pivot leaves at least two retained jet coefficients. -/
theorem precision_pivot (self : Bool) (n : ℕ) :
    denominatorOrder self n < precisionBefore self n+1 := by
  cases self <;> simp only [precisionBefore,denominatorOrder,Bool.false_eq_true,if_false,if_true]
  all_goals split_ifs <;> omega

theorem JetApproxAlong.list_sum {l : Filter ℂ} {d : ℕ} {α : Type*}
    (xs : List α) (f : α → ℂ → ℂ) (p : α → ℂ[X])
    (h : ∀ i ∈ xs, JetApproxAlong l d (f i) (p i)) :
    JetApproxAlong l d (fun t => (xs.map (fun i => f i t)).sum) ((xs.map p).sum) := by
  induction xs with
  | nil => simpa using JetApproxAlong.polynomial d (0 : ℂ[X])
  | cons i xs ih =>
    simpa only [List.map_cons,List.sum_cons] using JetApproxAlong.add
      (h i (by simp)) (ih (by intro j hj; exact h j (by simp [hj])))

theorem coeff_jetSum_foldl {α : Type*} (P : ℕ) (xs : List α) (J : α → Jet)
    (a : Jet) {k : ℕ} (hk : k≤P) :
    (zp ((xs.map J).foldl (jetAdd P) a)).coeff k =
      (zp a).coeff k+((xs.map (fun i => (zp (J i)).coeff k)).sum) := by
  induction xs generalizing a with
  | nil => simp
  | cons i xs ih =>
    simp only [List.map_cons,List.foldl_cons,ih,coeff_jetAdd P a (J i) hk,
      List.sum_cons,add_assoc]

theorem coeff_jetSum {α : Type*} (P : ℕ) (xs : List α) (J : α → Jet)
    {k : ℕ} (hk : k≤P) :
    (zp (jetSum P (xs.map J))).coeff k = ((xs.map (fun i => (zp (J i)).coeff k)).sum) := by
  simpa only [jetSum,coeff_jetSum_foldl P xs J (jetZero P) hk,zp_jetZero,Polynomial.coeff_zero,zero_add]

theorem coeff_list_sum {α : Type*} (xs : List α) (p : α → ℂ[X]) (k : ℕ) :
    ((xs.map p).sum).coeff k = (xs.map (fun i => (p i).coeff k)).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih => simp [ih]

/-- Exact stored undivided recurrences leave only order-P+1 polynomial error. -/
theorem jet_recurrence_remainder (self : Bool) (n : ℕ) (hn0 : 1≤n)
    (hn : n≤channelBound self) : Polynomial.X^(precisionBefore self n+1) ∣
      zp (coefficientJets self n 0)*zp (valueJets self n)+
        (((List.range (min 6 n)).map fun q =>
          zp (coefficientJets self (n-(q+1)) (q+1))*zp (valueJets self (n-(q+1)))).sum) := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro k hk
  have hk' : k≤precisionBefore self n := by omega
  have h := congrArg (fun J => (zp J).coeff k) (jet_recurrence_holds self n hn0 hn)
  simp only [JetRecurrence] at h
  rw [coeff_jetAdd _ _ _ hk',coeff_jetMul _ _ _ hk',
    coeff_jetSum _ _ _ hk',zp_jetZero,Polynomial.coeff_zero] at h
  simpa only [Polynomial.coeff_add,coeff_list_sum,coeff_jetMul _ _ _ hk'] using h

/-- The actual undivided recurrence in the positive-width form used by the cache. -/
def widthSequenceError (self : Bool) (F : ℕ → ℂ → ℂ) (n : ℕ) (t : ℂ) : ℂ :=
  widthAt self n 0 t*F n t+
    ((List.range (min 6 n)).map fun q =>
      widthAt self (n-(q+1)) (q+1) t*F (n-(q+1)) t).sum

/-- The finite normalized sequence is determined across every actual resonance
by the undivided recurrence and the exact jet certificates. -/
theorem widthSequence_jetApprox (self : Bool) (F : ℕ → ℂ → ℂ)
    {l : Filter ℂ} (hl : l≤𝓝[≠] (1 : ℂ))
    (hzero : ∀ᶠ t in l, F 0 t=1)
    (hrec : ∀ n, 1≤n → n≤channelBound self → ∀ᶠ t in l, widthSequenceError self F n t=0)
    (n : ℕ) (hn : n≤channelBound self) :
    JetApproxAlongPL l (precisionAfter self n+1) (F n) (valueJets self n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n=0
    · subst n
      have hp : zp (valueJets self 0)=(1 : ℂ[X]) := by
        cases self <;> simp [valueJets,vacValueTable,selfValueTable,zp]
      rw [JetApproxAlongPL,hp]
      have h := JetApproxAlong.polynomial (l := l) (precisionAfter self 0+1) (1 : ℂ[X])
      apply h.congr
      filter_upwards [hzero] with t ht
      simpa using ht.symm
    · let P := precisionBefore self n
      let d := P+1
      let D := zp (coefficientJets self n 0)
      let J := zp (valueJets self n)
      let f : ℕ → ℂ → ℂ := fun q t => widthAt self (n-(q+1)) (q+1) t*F (n-(q+1)) t
      let p : ℕ → ℂ[X] := fun q =>
        zp (coefficientJets self (n-(q+1)) (q+1))*zp (valueJets self (n-(q+1)))
      have hproducts : ∀ q∈List.range (min 6 n), JetApproxAlong l d (f q) (p q) := by
        intro q hq
        have hq' : q < min 6 n := List.mem_range.mp hq
        have hj : n-(q+1)<n := by omega
        have hjn : n-(q+1)≤channelBound self := by omega
        have hprec := precision_earlier self n (n-(q+1)) hj
        have hw : JetApprox (precisionBefore self (n-(q+1))+1)
            (widthAt self (n-(q+1)) (q+1))
            (zp (coefficientJets self (n-(q+1)) (q+1))) := by
          rw [coefficientJets_correct self _ _ hjn]
          exact widthAt_jetApprox _ _ _ _ (by omega)
        have hbefore : P≤precisionBefore self (n-(q+1)) :=
          hprec.trans (Nat.sub_le _ _)
        have hw' := (hw.along hl).weaken (e := d) (by change P+1≤_; omega)
        have hf := (ih _ hj hjn).weaken (e := d) (by change P+1≤_; omega)
        exact hw'.mul hf
      have hs := JetApproxAlong.list_sum (List.range (min 6 n)) f p hproducts
      have hden : JetApproxAlong l d (widthAt self n 0) D := by
        apply JetApprox.along _ hl
        dsimp [d,P,D]
        rw [coefficientJets_correct self n 0 hn]
        exact widthAt_jetApprox _ _ _ _ (by omega)
      have hJ := JetApproxAlong.polynomial (l := l) d J
      have hr := hs.neg.sub (hden.mul hJ)
      have hrem : Polynomial.X^d ∣ -((List.range (min 6 n)).map p).sum-D*J := by
        have h := dvd_neg.mpr (jet_recurrence_remainder self n (by omega) hn)
        convert h using 1 <;> dsimp [d,P,D,J,p] <;> ring
      have hr0 := hr.of_remainder (q := 0) (by simpa only [sub_zero] using hrem)
      have herr : JetApproxAlong l d (fun t => widthAt self n 0 t*(F n t-J.eval (t-1))) 0 := by
        apply hr0.congr
        filter_upwards [hrec n (by omega) hn] with t ht
        dsimp [widthSequenceError] at ht
        dsimp [f]
        linear_combination -ht
      have hpiv := jet_pivot_holds self n (by omega) hn
      have hbefore : ∀ i<denominatorOrder self n, D.coeff i=0 := by
        intro i hi
        dsimp [D]
        rw [coeff_zp]
        exact_mod_cast hpiv.1 ⟨i,hi⟩
      have hpivot : D.coeff (denominatorOrder self n)≠0 := by
        dsimp [D]
        rw [coeff_zp]
        exact_mod_cast hpiv.2
      have hv : denominatorOrder self n<d := precision_pivot self n
      have hresult := JetApproxAlong.cancel_pivot hl hden hv hbefore hpivot herr
      convert hresult using 1
      dsimp [d,P,precisionAfter]
      omega

/-- Every actual finite sequence satisfying the recurrence has the certified limit. -/
theorem widthSequence_tendsto (self : Bool) (F : ℕ → ℂ → ℂ)
    {l : Filter ℂ} (hl : l≤𝓝[≠] (1 : ℂ))
    (hzero : ∀ᶠ t in l, F 0 t=1)
    (hrec : ∀ n, 1≤n → n≤channelBound self → ∀ᶠ t in l, widthSequenceError self F n t=0)
    (n : ℕ) (hn : n≤channelBound self) :
    Tendsto (F n) l (𝓝 ((((valueJets self n)[0]?).getD 0 : ℚ) : ℂ)) := by
  have h := widthSequence_jetApprox self F hl hzero hrec n hn
  simpa only [← Polynomial.coeff_zero_eq_eval_zero,coeff_zp] using h.tendsto (by omega) hl

/-- The seven-channel actual recurrence equals the cached positive-width form. -/
theorem widthSequenceError_eq_fin (self : Bool) (F : ℕ → ℂ → ℂ) (n : ℕ) (t : ℂ) :
    widthSequenceError self F n t =
      ∑ q : Fin 7, (if (q : ℕ)≤n then widthAt self (n-q) q t*F (n-q) t else 0) := by
  by_cases hn : n<6
  · interval_cases n <;> simp [widthSequenceError,Fin.sum_univ_succ,List.range_succ] <;> ring
  · have hm : min 6 n=6 := min_eq_left (by omega)
    have h1 : 1≤n := by omega
    have h2 : 2≤n := by omega
    have h3 : 3≤n := by omega
    have h4 : 4≤n := by omega
    have h5 : 5≤n := by omega
    have h6 : 6≤n := by omega
    simp [widthSequenceError,hm,Fin.sum_univ_succ,List.range_succ,h1,h2,h3,h4,h5,h6]
    simp only [← Nat.succ_le_iff,h1,h2,h3,h4,h5,h6,if_true]

end VOA.Classification.COne.OrbIcoW
