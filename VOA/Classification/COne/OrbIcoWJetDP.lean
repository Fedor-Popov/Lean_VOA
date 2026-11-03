import VOA.Classification.COne.OrbIcoWJetH

/-! Continuous-remainder semantics for every stage of the exact width recursion. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoW
open OrbOdd Polynomial Filter Topology

@[simp] theorem zp_jetZero (P : ℕ) : zp (jetZero P)=0 := by
  apply Polynomial.ext
  intro n
  simp [coeff_zp,jetZero]

theorem JetApproxPL.zero (P : ℕ) : JetApproxPL (P+1) (fun _ => 0) (jetZero P) := by
  rw [JetApproxPL,zp_jetZero]
  simpa using JetApprox.polynomial (P+1) (0 : ℂ[X])

theorem JetApproxPL.constant (P : ℕ) (c : ℚ) :
    JetApproxPL (P+1) (fun _ => (c : ℂ)) (jetCut P [c]) := by
  apply JetApproxPL.cut
  change JetApprox (P+1) (fun _ => (c : ℂ)) (zp [c])
  simpa [zp] using JetApprox.polynomial (P+1) (Polynomial.C (c : ℂ))

theorem JetApproxPL.scale {P : ℕ} {f : ℂ → ℂ} {J : Jet}
    (c : ℚ) (h : JetApproxPL (P+1) f J) :
    JetApproxPL (P+1) (fun t => (c : ℂ)*f t) (jetScale c J) := by
  change JetApprox (P+1) _ (zp (pscaleL c J))
  rw [zp_pscaleL]
  exact JetApprox.scale c h

/-- The finite jet sum has the same continuous-remainder semantics as the scalar sum. -/
theorem JetApproxPL.foldl {α : Type*} (P : ℕ) (xs : List α)
    (f : α → ℂ → ℂ) (J : α → Jet) {a : Jet} {v : ℂ → ℂ}
    (hv : JetApproxPL (P+1) v a)
    (h : ∀ i ∈ xs, JetApproxPL (P+1) (f i) (J i)) :
    JetApproxPL (P+1) (fun t => v t+(xs.map (fun i => f i t)).sum)
      ((xs.map J).foldl (jetAdd P) a) := by
  induction xs generalizing a v with
  | nil => simpa using hv
  | cons i xs ih =>
    have hi := h i (by simp)
    have hx : ∀ j ∈ xs, JetApproxPL (P+1) (f j) (J j) := by
      intro j hj
      exact h j (by simp [hj])
    simpa only [List.map_cons,List.foldl_cons,List.sum_cons,add_assoc] using
      ih (hv.add hi) hx

theorem JetApproxPL.sum {α : Type*} (P : ℕ) (xs : List α)
    (f : α → ℂ → ℂ) (J : α → Jet)
    (h : ∀ i ∈ xs, JetApproxPL (P+1) (f i) (J i)) :
    JetApproxPL (P+1) (fun t => (xs.map (fun i => f i t)).sum) (jetSum P (xs.map J)) := by
  simpa only [zero_add,jetSum] using JetApproxPL.foldl P xs f J (JetApproxPL.zero P) h

theorem identity_jetApprox (P : ℕ) : JetApproxPL (P+1) (fun t : ℂ => t) [1,1] := by
  have h := JetApprox.polynomial (P+1) (zp [1,1])
  convert h using 1
  funext t
  simp [zp]

/-- Every scalar bracket is evaluated by its certified finite jet. -/
theorem scalarBracket_jetApprox (P : ℕ) (self : Bool) (n q r j : ℕ) :
    JetApproxPL (P+1)
      (fun t => scalarBracket (widthH t) (if self then widthH t else 0) n q r j)
      (jetBracket P self n q r j) := by
  have hK : JetApproxPL (P+1) (fun t => if self then widthH t else 0) (jetK P self) := by
    cases self <;> simp only [jetK,Bool.false_eq_true,if_false,if_true]
    · exact JetApproxPL.zero P
    · exact widthH_jetApprox P
  have hc := JetApproxPL.constant P ((j : ℚ)-2*((n+q : ℕ) : ℚ))
  have hs := ((widthH_jetApprox P).scale ((r-j : ℕ)+1)).add (hK.scale (-1))
  have h := hs.add hc
  convert h using 1
  funext t
  simp only [scalarBracket]
  push_cast
  ring

@[simp] theorem jetSource_length (P : ℕ) (self : Bool) (n r : ℕ) (A : List (List Jet)) :
    (jetSource P self n r A).length=7 := by simp [jetSource]

@[simp] theorem jetStep_length (P : ℕ) (self : Bool) (n r : ℕ) (A : List (List Jet)) :
    (jetStep P self n r A).length=7 := by simp [jetStep]

@[simp] theorem jetRows_length (P : ℕ) (self : Bool) (n r : ℕ) :
    (jetRows P self n r).length=r+1 := by
  induction r with
  | zero => simp [jetRows]
  | succ r ih => simp [jetRows,ih]

theorem jetRows_last (P : ℕ) (self : Bool) (n r : ℕ) :
    ((jetRows P self n (r+1))[r+1]?).getD [] =
      jetStep P self n (r+1) (jetRows P self n r) := by
  simp [jetRows,List.getElem?_append,jetRows_length]

/-- The actual source projection is the sum of the certified bracket jets. -/
theorem scalarSource_jetApprox (P : ℕ) (self : Bool) (n r q : ℕ) (hq : q<7)
    (A : ℂ → List (List ℂ)) (B : List (List Jet))
    (h : ∀ j<r, ∀ k<7, JetApproxPL (P+1)
      (fun t => ((((A t)[j]?).getD [])[k]?).getD 0)
      ((((B[j]?).getD [])[k]?).getD [])) :
    JetApproxPL (P+1)
      (fun t => (((scalarSource (widthH t) (if self then widthH t else 0) n r (A t))[q]?).getD 0))
      (((jetSource P self n r B)[q]?).getD []) := by
  simp only [scalarSource,jetSource,List.getElem?_map,List.getElem?_range hq,
    Option.map_some,Option.getD_some]
  apply JetApproxPL.sum
  intro j hj
  have hjr : j<r := List.mem_range.mp hj
  have hfirst := ((scalarBracket_jetApprox P self n q r j).mul (h j hjr q hq)).scale
    ((-1 : ℚ)^(r-j))
  have hsecond : JetApproxPL (P+1)
      (fun t => if r-j=2 ∧ 0<q then ((((A t)[j]?).getD [])[q-1]?).getD 0 else 0)
      (if r-j=2 ∧ 0<q then (((B[j]?).getD [])[q-1]?).getD [] else jetZero P) := by
    by_cases he : r-j=2 ∧ 0<q
    · simp only [he,if_true]
      exact h j hjr (q-1) (by omega)
    · simp only [he,if_false]
      exact JetApproxPL.zero P
  simpa only [Rat.cast_pow,Rat.cast_neg,Rat.cast_one,mul_assoc] using hfirst.add hsecond

/-- One divided BSA stage preserves the full certified precision. -/
theorem scalarStep_jetApprox (P : ℕ) (self : Bool) (n r q : ℕ) (hq : q<7)
    (A : ℂ → List (List ℂ)) (B : List (List Jet))
    (h : ∀ j<r, ∀ k<7, JetApproxPL (P+1)
      (fun t => ((((A t)[j]?).getD [])[k]?).getD 0)
      ((((B[j]?).getD [])[k]?).getD [])) :
    JetApproxPL (P+1)
      (fun t => (((scalarStep (widthH t) (if self then widthH t else 0) t n r (A t))[q]?).getD 0))
      (((jetStep P self n r B)[q]?).getD []) := by
  have hs := scalarSource_jetApprox P self n r q hq A B h
  have hf := ((identity_jetApprox P).mul hs).scale (-1/((r : ℚ)*(13-(r : ℚ))))
  have hca (t : ℂ) : q<(scalarSource (widthH t) (if self then widthH t else 0) n r (A t)).length := by simpa using hq
  have hcb : q<(jetSource P self n r B).length := by simpa using hq
  simp only [scalarStep,jetStep,List.getElem?_map,
    List.getElem?_eq_getElem (hca _),List.getElem?_eq_getElem hcb,
    Option.map_some,Option.getD_some] at hs hf ⊢
  convert hf using 1
  funext t
  push_cast
  ring

/-- Every cached scalar row has the exact finite rational jet stored by jetRows. -/
theorem scalarRows_jetApprox (P : ℕ) (self : Bool) (n r j q : ℕ) (hj : j≤r) (hq : q<7) :
    JetApproxPL (P+1)
      (fun t => ((((scalarRows (widthH t) (if self then widthH t else 0) t n r)[j]?).getD [])[q]?).getD 0)
      (((((jetRows P self n r)[j]?).getD [])[q]?).getD []) := by
  induction r generalizing j q with
  | zero =>
    have he : j=0 := by omega
    subst j
    simp only [scalarRows_zero _ _ _ _ _ hq,jetRows,List.getElem?_cons_zero,Option.getD_some,
      List.getElem?_map,List.getElem?_range hq,Option.map_some,Option.getD_some]
    split_ifs
    · simpa only [Rat.cast_one] using JetApproxPL.constant P 1
    · exact JetApproxPL.zero P
  | succ r ih =>
    by_cases hjr : j≤r
    · have hA : (fun t => ((((scalarRows (widthH t) (if self then widthH t else 0) t n (r+1))[j]?).getD [])[q]?).getD 0) =
          (fun t => ((((scalarRows (widthH t) (if self then widthH t else 0) t n r)[j]?).getD [])[q]?).getD 0) := by
        funext t
        rw [scalarRows_earlier _ _ _ _ _ j (by omega),scalarRows_earlier _ _ _ _ _ j hjr]
      have hB : (((((jetRows P self n (r+1))[j]?).getD [])[q]?).getD []) =
          (((((jetRows P self n r)[j]?).getD [])[q]?).getD []) := by
        rw [jetRows,List.getElem?_append_left (by rw [jetRows_length]; omega)]
      rw [hA,hB]
      exact ih j q hjr hq
    · have he : j=r+1 := by omega
      subst j
      simp only [scalarRows_last,jetRows_last]
      apply scalarStep_jetApprox P self n (r+1) q hq
      intro j hj q hq
      exact ih j q (by omega) hq

/-- The actual width-six coefficient functions have the certified all-order jets. -/
theorem widthAt_jetApprox (P : ℕ) (self : Bool) (n q : ℕ) (hq : q<7) :
    JetApproxPL (P+1) (widthAt self n q)
      (((widthCoefficients P self n)[q]?).getD []) := by
  apply scalarSource_jetApprox P self n 13 q hq
  intro j hj k hk
  exact scalarRows_jetApprox P self n 12 j k (by omega) hk

end VOA.Classification.COne.OrbIcoW
