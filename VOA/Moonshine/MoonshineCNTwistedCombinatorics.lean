import VOA.Moonshine.MoonshineCNReplicationFormal

/-!
# Graded words and multisets: the two character identities

Letters `i : ι` carry a degree in `ℕ × ℕ` with positive first coordinate and finite fibres
(`GradedLetters`), and a weight `wt i ∈ ℂ`.  Words (lists) and multisets of letters get the additive
degree and the multiplicative weight.  For each degree `γ` there are finitely many words and
multisets of degree `γ`, and the weighted counts satisfy

* `W(γ) = [γ = 0] + Σ_δ ℓ(δ) W(γ − δ)` (split off the first letter; `wordCount_eq`), i.e.
  `W · (1 − ℓ) = 1` as two-variable power series (`wordSeries_mul_one_sub_letterSeries`);
* `γ₁ M(γ) = Σ_ε M(γ − ε) P(ε)` with `P(ε) = Σ_{k ≥ 1, k·deg i = ε} (deg i)₁ wt(i)^k`
  (`firstDegree_mul_msetCount_eq`), i.e. `D M = M · P` with `D = p ∂/∂p`
  (`eulerDeriv_msetSeries`).

The second identity is the logarithm-free plethystic exponential; its proof removes `k` copies of
a letter from a multiset.  No vertex algebra is used in this file.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open Finset

/-! ### Bigraded series and convolution -/

/-- The two-variable series `Σ f(A, N) p^A q^N`. -/
def bigradedSeries (f : ℕ × ℕ → ℂ) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.mk fun A => PowerSeries.mk fun N => f (A, N)

@[simp] theorem coeff_bigradedSeries (f : ℕ × ℕ → ℂ) (A N : ℕ) :
    PowerSeries.coeff N (PowerSeries.coeff A (bigradedSeries f)) = f (A, N) := by
  simp [bigradedSeries]

/-- Convolution of bigraded coefficient functions. -/
def bigradedConv (f g : ℕ × ℕ → ℂ) (γ : ℕ × ℕ) : ℂ :=
  ∑ a ∈ antidiagonal γ.1, ∑ n ∈ antidiagonal γ.2, f (a.1, n.1) * g (a.2, n.2)

theorem bigradedSeries_ext {F G : PowerSeries (PowerSeries ℂ)}
    (h : ∀ A N, PowerSeries.coeff N (PowerSeries.coeff A F) =
      PowerSeries.coeff N (PowerSeries.coeff A G)) : F = G :=
  PowerSeries.ext fun A => PowerSeries.ext fun N => h A N

theorem bigradedSeries_mul (f g : ℕ × ℕ → ℂ) :
    bigradedSeries f * bigradedSeries g = bigradedSeries (bigradedConv f g) := by
  refine bigradedSeries_ext fun A N => ?_
  rw [coeff_bigradedSeries, PowerSeries.coeff_mul, map_sum, bigradedConv]
  refine sum_congr rfl fun a _ => ?_
  rw [PowerSeries.coeff_mul]
  simp

theorem one_eq_bigradedSeries :
    (1 : PowerSeries (PowerSeries ℂ)) = bigradedSeries fun γ => if γ = 0 then 1 else 0 := by
  refine bigradedSeries_ext fun A N => ?_
  rw [coeff_bigradedSeries]
  by_cases hA : A = 0 <;> by_cases hN : N = 0 <;>
    simp [PowerSeries.coeff_one, hA, hN, Prod.ext_iff]

theorem eulerDeriv_bigradedSeries (f : ℕ × ℕ → ℂ) :
    eulerDeriv (bigradedSeries f) = bigradedSeries fun γ => (γ.1 : ℂ) * f γ := by
  refine bigradedSeries_ext fun A N => ?_
  rw [coeff_eulerDeriv, coeff_bigradedSeries,
    show ((A : ℕ) : PowerSeries ℂ) = PowerSeries.C (A : ℂ) from (map_natCast _ A).symm,
    PowerSeries.coeff_C_mul, coeff_bigradedSeries]

theorem bigradedConv_congr {f f' g : ℕ × ℕ → ℂ} {γ : ℕ × ℕ}
    (h : ∀ δ, δ.1 ≤ γ.1 → δ.2 ≤ γ.2 → f δ = f' δ) :
    bigradedConv f g γ = bigradedConv f' g γ := by
  refine sum_congr rfl fun a ha => sum_congr rfl fun n hn => ?_
  rw [mem_antidiagonal] at ha hn
  rw [h _ (by simp only; omega) (by simp only; omega)]

theorem bigradedConv_comm (f g : ℕ × ℕ → ℂ) (γ : ℕ × ℕ) :
    bigradedConv f g γ = bigradedConv g f γ := by
  unfold bigradedConv
  rw [← Nat.sum_antidiagonal_swap]
  refine sum_congr rfl fun a _ => ?_
  rw [← Nat.sum_antidiagonal_swap]
  refine sum_congr rfl fun n _ => ?_
  simp [mul_comm]

/-- A single antidiagonal sum with an indicator in the first slot. -/
theorem sum_antidiagonal_ite_fst (M x : ℕ) (h : ℕ × ℕ → ℂ) :
    ∑ a ∈ antidiagonal M, (if a.1 = x then h a else 0) =
      if x ≤ M then h (x, M - x) else 0 := by
  by_cases hx : x ≤ M
  · rw [if_pos hx, sum_eq_single (x, M - x)]
    · simp
    · rintro ⟨a, b⟩ hab hne
      rw [mem_antidiagonal] at hab
      change a + b = M at hab
      rw [if_neg]
      intro h1
      change a = x at h1
      exact hne (Prod.ext h1 (show b = M - x by omega))
    · intro hn
      exact absurd (mem_antidiagonal.mpr (show x + (M - x) = M by omega)) hn
  · rw [if_neg hx]
    refine sum_eq_zero fun a ha => if_neg ?_
    rw [mem_antidiagonal] at ha
    omega

/-- Shifted sums are convolutions: `Σ_x [d x ≤ γ] f x F(γ − d x) = (φ ⋆ F)(γ)` with
`φ(δ) = Σ_{d x = δ} f x`. -/
theorem sum_shift_eq_bigradedConv {κ : Type*} (S : Finset κ) (d : κ → ℕ × ℕ) (f : κ → ℂ)
    (F : ℕ × ℕ → ℂ) (γ : ℕ × ℕ) :
    ∑ x ∈ S, (if (d x).1 ≤ γ.1 ∧ (d x).2 ≤ γ.2 then f x * F (γ - d x) else 0) =
      bigradedConv (fun δ => ∑ x ∈ S, if d x = δ then f x else 0) F γ := by
  unfold bigradedConv
  simp only [sum_mul]
  have hswap : ∀ a ∈ antidiagonal γ.1, ∑ n ∈ antidiagonal γ.2, ∑ x ∈ S,
      (if d x = (a.1, n.1) then f x else 0) * F (a.2, n.2) =
      ∑ x ∈ S, ∑ n ∈ antidiagonal γ.2, (if d x = (a.1, n.1) then f x else 0) * F (a.2, n.2) :=
    fun a _ => sum_comm
  rw [sum_congr rfl hswap, sum_comm]
  refine sum_congr rfl fun x _ => ?_
  have hcond : ∀ a n : ℕ × ℕ, (if d x = (a.1, n.1) then f x else 0) * F (a.2, n.2) =
      if n.1 = (d x).2 then (if a.1 = (d x).1 then f x * F (a.2, n.2) else 0) else 0 := by
    intro a n
    by_cases h1 : a.1 = (d x).1 <;> by_cases h2 : n.1 = (d x).2 <;>
      simp [Prod.ext_iff, h1, h2, eq_comm]
  symm
  simp only [hcond, sum_antidiagonal_ite_fst γ.2 (d x).2]
  by_cases h2 : (d x).2 ≤ γ.2
  · simp only [h2, if_true, sum_antidiagonal_ite_fst γ.1 (d x).1, and_true]
    by_cases h1 : (d x).1 ≤ γ.1
    · simp only [h1, if_true]
      rfl
    · simp only [h1, if_false]
  · simp only [h2, if_false, sum_const_zero, and_false]

theorem prod_add_tsub_cancel_left (a b : ℕ × ℕ) : a + b - a = b :=
  Prod.ext (by simp) (by simp)

theorem prod_add_tsub_cancel_right (a b : ℕ × ℕ) : a + b - b = a :=
  Prod.ext (by simp) (by simp)

/-! ### Graded letters -/

/-- Letters graded by `ℕ × ℕ`, with positive first degree and finite fibres. -/
structure GradedLetters (ι : Type*) where
  deg : ι → ℕ × ℕ
  deg_pos : ∀ i, 1 ≤ (deg i).1
  finite_fiber : ∀ γ, {i | deg i = γ}.Finite

namespace GradedLetters

variable {ι : Type*} (L : GradedLetters ι)

theorem finite_le (γ : ℕ × ℕ) : {i | (L.deg i).1 ≤ γ.1 ∧ (L.deg i).2 ≤ γ.2}.Finite := by
  refine ((range (γ.1 + 1) ×ˢ range (γ.2 + 1) : Finset (ℕ × ℕ)).finite_toSet.biUnion
    fun δ _ => L.finite_fiber δ).subset fun i hi => ?_
  simp only [Set.mem_setOf_eq] at hi
  refine Set.mem_biUnion (x := L.deg i) ?_ rfl
  simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
  omega

/-- The letters of degree at most `γ` (componentwise). -/
def lowerLetters (γ : ℕ × ℕ) : Finset ι := (L.finite_le γ).toFinset

theorem mem_lowerLetters {γ : ℕ × ℕ} {i : ι} :
    i ∈ L.lowerLetters γ ↔ (L.deg i).1 ≤ γ.1 ∧ (L.deg i).2 ≤ γ.2 := by
  simp [lowerLetters]

/-! #### Words -/

/-- The degree of a word. -/
def listDeg (w : List ι) : ℕ × ℕ := (w.map L.deg).sum

@[simp] theorem listDeg_nil : L.listDeg [] = 0 := rfl

@[simp] theorem listDeg_cons (i : ι) (w : List ι) :
    L.listDeg (i :: w) = L.deg i + L.listDeg w := by
  simp [listDeg]

theorem finite_wordFiber (γ : ℕ × ℕ) : {w : List ι | L.listDeg w = γ}.Finite := by
  suffices h : ∀ n, ∀ γ : ℕ × ℕ, γ.1 = n → {w : List ι | L.listDeg w = γ}.Finite from h _ γ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro γ hγ
    have hsub : {w : List ι | L.listDeg w = γ} ⊆ {[]} ∪
        ⋃ i ∈ {i | (L.deg i).1 ≤ γ.1 ∧ (L.deg i).2 ≤ γ.2},
          List.cons i '' {w | L.listDeg w = γ - L.deg i} := by
      rintro (_ | ⟨i, w⟩) hw
      · exact Or.inl rfl
      · right
        simp only [Set.mem_setOf_eq, listDeg_cons] at hw
        refine Set.mem_biUnion (x := i) ?_ ⟨w, ?_, rfl⟩
        · simp only [Set.mem_setOf_eq, ← hw, Prod.fst_add, Prod.snd_add]
          omega
        · simp only [Set.mem_setOf_eq, ← hw, prod_add_tsub_cancel_left]
    refine ((Set.finite_singleton _).union ((L.finite_le γ).biUnion fun i hi =>
      (ih _ ?_ _ rfl).image _)).subset hsub
    have := L.deg_pos i
    simp only [Set.mem_setOf_eq] at hi
    rw [Prod.fst_sub]
    omega

/-- The finitely many words of degree `γ`. -/
def wordFiber (γ : ℕ × ℕ) : Finset (List ι) := (L.finite_wordFiber γ).toFinset

theorem mem_wordFiber {γ : ℕ × ℕ} {w : List ι} : w ∈ L.wordFiber γ ↔ L.listDeg w = γ := by
  simp [wordFiber]

/-- The weighted count `W(γ) = Σ_{deg w = γ} Π wt`. -/
def wordCount (wt : ι → ℂ) (γ : ℕ × ℕ) : ℂ := ∑ w ∈ L.wordFiber γ, (w.map wt).prod

/-- The weighted count of letters of degree `δ`. -/
def letterCount (wt : ι → ℂ) (δ : ℕ × ℕ) : ℂ :=
  ∑ i ∈ L.lowerLetters δ, if L.deg i = δ then wt i else 0

/-- Splitting off the first letter. -/
theorem wordCount_eq (wt : ι → ℂ) (γ : ℕ × ℕ) :
    L.wordCount wt γ = (if γ = 0 then 1 else 0) +
      ∑ i ∈ L.lowerLetters γ, wt i * L.wordCount wt (γ - L.deg i) := by
  classical
  unfold wordCount
  rw [← sum_filter_add_sum_filter_not (L.wordFiber γ) (fun w => w = [])]
  congr 1
  · by_cases hγ : γ = 0
    · rw [if_pos hγ, sum_eq_single []]
      · simp
      · intro w hw hne
        exact absurd (mem_filter.mp hw).2 hne
      · intro h
        exact (h (mem_filter.mpr ⟨(L.mem_wordFiber (γ := γ) (w := [])).mpr
          (by rw [hγ, listDeg_nil]), rfl⟩)).elim
    · rw [if_neg hγ]
      refine sum_eq_zero fun w hw => ?_
      obtain ⟨hw1, rfl⟩ := mem_filter.mp hw
      exact (hγ (by rw [← L.mem_wordFiber.mp hw1, listDeg_nil])).elim
  · simp only [mul_sum]
    rw [sum_sigma']
    symm
    refine sum_bij (fun x _ => x.1 :: x.2) ?_ ?_ ?_ ?_
    · rintro ⟨i, w⟩ hx
      rw [mem_sigma, L.mem_lowerLetters, L.mem_wordFiber] at hx
      dsimp only at hx
      refine mem_filter.mpr ⟨L.mem_wordFiber.mpr ?_, List.cons_ne_nil _ _⟩
      rw [listDeg_cons, hx.2]
      refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub,
        Prod.snd_sub] <;> omega
    · rintro ⟨i, w⟩ _ ⟨j, v⟩ _ h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · intro w hw
      obtain ⟨hw1, hne⟩ := mem_filter.mp hw
      obtain ⟨i, v, rfl⟩ := List.exists_cons_of_ne_nil hne
      rw [L.mem_wordFiber, listDeg_cons] at hw1
      refine ⟨⟨i, v⟩, ?_, rfl⟩
      rw [mem_sigma, L.mem_lowerLetters, L.mem_wordFiber, ← hw1]
      refine ⟨?_, (prod_add_tsub_cancel_left _ _).symm⟩
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    · rintro ⟨i, w⟩ _
      simp

/-! #### Multisets -/

/-- The degree of a multiset. -/
def msetDeg (m : Multiset ι) : ℕ × ℕ := (m.map L.deg).sum

@[simp] theorem msetDeg_zero : L.msetDeg 0 = 0 := rfl

@[simp] theorem msetDeg_cons (i : ι) (m : Multiset ι) :
    L.msetDeg (i ::ₘ m) = L.deg i + L.msetDeg m := by
  simp [msetDeg]

@[simp] theorem msetDeg_add (m m' : Multiset ι) :
    L.msetDeg (m + m') = L.msetDeg m + L.msetDeg m' := by
  simp [msetDeg]

@[simp] theorem msetDeg_replicate (k : ℕ) (i : ι) :
    L.msetDeg (Multiset.replicate k i) = k • L.deg i := by
  simp [msetDeg, Multiset.map_replicate, Multiset.sum_replicate]

theorem card_le_msetDeg (m : Multiset ι) : Multiset.card m ≤ (L.msetDeg m).1 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons i m ih =>
      rw [Multiset.card_cons, msetDeg_cons, Prod.fst_add]
      have := L.deg_pos i
      omega

theorem finite_msetFiber (γ : ℕ × ℕ) : {m : Multiset ι | L.msetDeg m = γ}.Finite := by
  suffices h : ∀ n, ∀ γ : ℕ × ℕ, γ.1 = n → {m : Multiset ι | L.msetDeg m = γ}.Finite from
    h _ γ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro γ hγ
    have hsub : {m : Multiset ι | L.msetDeg m = γ} ⊆ {0} ∪
        ⋃ i ∈ {i | (L.deg i).1 ≤ γ.1 ∧ (L.deg i).2 ≤ γ.2},
          Multiset.cons i '' {m | L.msetDeg m = γ - L.deg i} := by
      intro m hm
      rcases Multiset.empty_or_exists_mem m with rfl | ⟨i, hi⟩
      · exact Or.inl rfl
      · right
        obtain ⟨m', rfl⟩ := Multiset.exists_cons_of_mem hi
        simp only [Set.mem_setOf_eq, msetDeg_cons] at hm
        refine Set.mem_biUnion (x := i) ?_ ⟨m', ?_, rfl⟩
        · simp only [Set.mem_setOf_eq, ← hm, Prod.fst_add, Prod.snd_add]
          omega
        · simp only [Set.mem_setOf_eq, ← hm, prod_add_tsub_cancel_left]
    refine ((Set.finite_singleton _).union ((L.finite_le γ).biUnion fun i hi =>
      (ih _ ?_ _ rfl).image _)).subset hsub
    have := L.deg_pos i
    simp only [Set.mem_setOf_eq] at hi
    rw [Prod.fst_sub]
    omega

/-- The finitely many multisets of degree `γ`. -/
def msetFiber (γ : ℕ × ℕ) : Finset (Multiset ι) := (L.finite_msetFiber γ).toFinset

theorem mem_msetFiber {γ : ℕ × ℕ} {m : Multiset ι} : m ∈ L.msetFiber γ ↔ L.msetDeg m = γ := by
  simp [msetFiber]

/-- The weighted count `M(γ) = Σ_{deg m = γ} Π wt`. -/
def msetCount (wt : ι → ℂ) (γ : ℕ × ℕ) : ℂ := ∑ m ∈ L.msetFiber γ, (m.map wt).prod

/-- `P(ε) = Σ_{k ≥ 1, k · deg i = ε} (deg i)₁ wt(i)^k`. -/
def powerSumCount (wt : ι → ℂ) (ε : ℕ × ℕ) : ℂ :=
  ∑ x ∈ L.lowerLetters ε ×ˢ Icc 1 ε.1,
    if x.2 • L.deg x.1 = ε then ((L.deg x.1).1 : ℂ) * wt x.1 ^ x.2 else 0

theorem msetDeg_le_of_le {m m' : Multiset ι} (h : m ≤ m') :
    (L.msetDeg m).1 ≤ (L.msetDeg m').1 ∧ (L.msetDeg m).2 ≤ (L.msetDeg m').2 := by
  obtain ⟨t, rfl⟩ := Multiset.le_iff_exists_add.mp h
  simp

/-- Multisets of degree `γ` containing `k` copies of `i` are `replicate k i` plus a multiset of
degree `γ − k · deg i`. -/
theorem sum_msetFiber_count_ge [DecidableEq ι] (wt : ι → ℂ) (γ : ℕ × ℕ) (i : ι) (k : ℕ) :
    ∑ m ∈ (L.msetFiber γ).filter (fun m => k ≤ m.count i), (m.map wt).prod =
      if (k • L.deg i).1 ≤ γ.1 ∧ (k • L.deg i).2 ≤ γ.2 then
        wt i ^ k * L.msetCount wt (γ - k • L.deg i) else 0 := by
  classical
  split_ifs with hle
  · unfold msetCount
    rw [mul_sum]
    symm
    refine sum_bij (fun m' _ => m' + Multiset.replicate k i) ?_ ?_ ?_ ?_
    · intro m' hm'
      rw [L.mem_msetFiber] at hm'
      refine mem_filter.mpr ⟨L.mem_msetFiber.mpr ?_, ?_⟩
      · rw [msetDeg_add, hm', msetDeg_replicate]
        refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub,
          Prod.snd_sub] <;> omega
      · simp
    · intro a _ b _ h
      exact add_right_cancel h
    · intro m hm
      obtain ⟨hm1, hk⟩ := mem_filter.mp hm
      rw [L.mem_msetFiber] at hm1
      have hrep : Multiset.replicate k i ≤ m := Multiset.le_count_iff_replicate_le.mp hk
      refine ⟨m - Multiset.replicate k i, ?_, tsub_add_cancel_of_le hrep⟩
      rw [L.mem_msetFiber]
      have h2 := congrArg L.msetDeg (tsub_add_cancel_of_le hrep)
      rw [msetDeg_add, hm1, msetDeg_replicate] at h2
      rw [← h2, prod_add_tsub_cancel_right]
    · intro m' _
      rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate,
        mul_comm]
  · refine sum_eq_zero fun m hm => ?_
    exfalso
    obtain ⟨hm1, hk⟩ := mem_filter.mp hm
    rw [L.mem_msetFiber] at hm1
    have h := L.msetDeg_le_of_le (Multiset.le_count_iff_replicate_le.mp hk)
    rw [msetDeg_replicate, hm1] at h
    exact hle h

/-- The plethystic identity, coefficientwise: `γ₁ M(γ) = Σ_ε M(γ − ε) P(ε)`. -/
theorem firstDegree_mul_msetCount_eq (wt : ι → ℂ) (γ : ℕ × ℕ) :
    (γ.1 : ℂ) * L.msetCount wt γ = bigradedConv (L.msetCount wt) (L.powerSumCount wt) γ := by
  classical
  -- the first degree of a multiset as a weighted count of copies
  have hdeg : ∀ m ∈ L.msetFiber γ, (γ.1 : ℂ) =
      ∑ x ∈ L.lowerLetters γ ×ˢ Icc 1 γ.1,
        if x.2 ≤ m.count x.1 then ((L.deg x.1).1 : ℂ) else 0 := by
    intro m hm
    rw [L.mem_msetFiber] at hm
    rw [sum_product]
    have hcount : ∀ i ∈ L.lowerLetters γ, (∑ k ∈ Icc 1 γ.1,
        if k ≤ m.count i then ((L.deg i).1 : ℂ) else 0) = (m.count i : ℂ) * (L.deg i).1 := by
      intro i _
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      have hc : m.count i ≤ γ.1 := (Multiset.count_le_card i m).trans
        (hm ▸ L.card_le_msetDeg m)
      have hfil : (Icc 1 γ.1).filter (fun k => k ≤ m.count i) = Icc 1 (m.count i) := by
        ext k
        simp only [mem_filter, mem_Icc]
        omega
      rw [hfil, Nat.card_Icc, Nat.add_sub_cancel]
    rw [sum_congr rfl hcount]
    have hsub : m.toFinset ⊆ L.lowerLetters γ := by
      intro i hi
      rw [L.mem_lowerLetters, ← hm]
      have := L.msetDeg_le_of_le (Multiset.singleton_le.mpr (Multiset.mem_toFinset.mp hi))
      simpa [msetDeg] using this
    rw [← sum_subset hsub (fun i _ hi => by
      rw [Multiset.count_eq_zero.mpr (fun h => hi (Multiset.mem_toFinset.mpr h))]; simp)]
    have h1 : (γ.1 : ℂ) = ((m.map fun i => (L.deg i).1).sum : ℕ) := by
      rw [← hm, msetDeg, Multiset.fst_sum, Multiset.map_map]
      rfl
    rw [h1, Finset.sum_multiset_map_count]
    push_cast
    simp
  -- left side as a sum over letters and copy numbers
  have hlhs : (γ.1 : ℂ) * L.msetCount wt γ = ∑ x ∈ L.lowerLetters γ ×ˢ Icc 1 γ.1,
      ((L.deg x.1).1 : ℂ) *
        ∑ m ∈ (L.msetFiber γ).filter (fun m => x.2 ≤ m.count x.1), (m.map wt).prod := by
    unfold msetCount
    rw [mul_sum]
    have hstep : ∀ m ∈ L.msetFiber γ, (γ.1 : ℂ) * (m.map wt).prod =
        ∑ x ∈ L.lowerLetters γ ×ˢ Icc 1 γ.1,
          (if x.2 ≤ m.count x.1 then ((L.deg x.1).1 : ℂ) else 0) * (m.map wt).prod := by
      intro m hm
      rw [hdeg m hm, sum_mul]
    rw [sum_congr rfl hstep, sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum, sum_filter]
    refine sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  rw [hlhs]
  simp only [sum_msetFiber_count_ge]
  have hrhs := sum_shift_eq_bigradedConv (L.lowerLetters γ ×ˢ Icc 1 γ.1)
    (fun x => x.2 • L.deg x.1) (fun x => ((L.deg x.1).1 : ℂ) * wt x.1 ^ x.2) (L.msetCount wt) γ
  rw [bigradedConv_comm, bigradedConv_congr (f' := fun δ =>
    ∑ x ∈ L.lowerLetters γ ×ˢ Icc 1 γ.1, if x.2 • L.deg x.1 = δ then
      ((L.deg x.1).1 : ℂ) * wt x.1 ^ x.2 else 0)]
  · rw [← hrhs]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  · intro δ h1 h2
    unfold powerSumCount
    refine sum_subset (fun x hx => ?_) (fun x hx hx' => ?_)
    · rw [mem_product, L.mem_lowerLetters, mem_Icc] at hx ⊢
      omega
    · rw [if_neg]
      intro h
      apply hx'
      rw [mem_product, mem_Icc] at hx
      rw [mem_product, L.mem_lowerLetters, mem_Icc, ← h]
      have hk := hx.2.1
      have hp := L.deg_pos x.1
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      exact ⟨⟨Nat.le_mul_of_pos_left _ hk, Nat.le_mul_of_pos_left _ hk⟩, hk,
        Nat.le_mul_of_pos_right _ hp⟩

/-! #### The two character identities as power series -/

/-- The word series `Σ_γ W(γ) x^γ`. -/
def wordSeries (wt : ι → ℂ) : PowerSeries (PowerSeries ℂ) := bigradedSeries (L.wordCount wt)

/-- The letter series `Σ_γ ℓ(γ) x^γ`. -/
def letterSeries (wt : ι → ℂ) : PowerSeries (PowerSeries ℂ) := bigradedSeries (L.letterCount wt)

/-- The multiset series `Σ_γ M(γ) x^γ`. -/
def msetSeries (wt : ι → ℂ) : PowerSeries (PowerSeries ℂ) := bigradedSeries (L.msetCount wt)

/-- The power-sum series `Σ_γ P(γ) x^γ`. -/
def powerSumSeries (wt : ι → ℂ) : PowerSeries (PowerSeries ℂ) := bigradedSeries (L.powerSumCount wt)

theorem wordSeries_mul_one_sub_letterSeries (wt : ι → ℂ) :
    L.wordSeries wt * (1 - L.letterSeries wt) = 1 := by
  rw [mul_sub, mul_one, sub_eq_iff_eq_add, wordSeries, letterSeries, bigradedSeries_mul,
    one_eq_bigradedSeries]
  refine bigradedSeries_ext fun A N => ?_
  rw [map_add, map_add, coeff_bigradedSeries, coeff_bigradedSeries, coeff_bigradedSeries,
    wordCount_eq, bigradedConv_comm]
  congr 1
  have h := sum_shift_eq_bigradedConv (L.lowerLetters (A, N)) L.deg wt (L.wordCount wt) (A, N)
  rw [bigradedConv_congr (f' := fun δ => ∑ x ∈ L.lowerLetters (A, N),
    if L.deg x = δ then wt x else 0), ← h]
  · refine sum_congr rfl fun i hi => ?_
    rw [if_pos (L.mem_lowerLetters.mp hi)]
  · intro δ h1 h2
    unfold letterCount
    refine sum_subset (fun i hi => ?_) (fun i hi hi' => ?_)
    · rw [L.mem_lowerLetters] at hi ⊢
      omega
    · rw [if_neg]
      rintro rfl
      exact hi' (L.mem_lowerLetters.mpr ⟨le_rfl, le_rfl⟩)

theorem eulerDeriv_msetSeries (wt : ι → ℂ) :
    eulerDeriv (L.msetSeries wt) = L.msetSeries wt * L.powerSumSeries wt := by
  rw [msetSeries, powerSumSeries, eulerDeriv_bigradedSeries, bigradedSeries_mul]
  congr 1
  funext γ
  exact L.firstDegree_mul_msetCount_eq wt γ

end GradedLetters

/-! ### From the two identities to the twisted denominator identity -/

/-- If `B (1 − u) = 1` and `D B = B P` then `D u = (1 − u) P`. -/
theorem eulerDeriv_eq_of_inverse {B u P : PowerSeries (PowerSeries ℂ)} (h1 : B * (1 - u) = 1)
    (h2 : eulerDeriv B = B * P) : eulerDeriv u = (1 - u) * P := by
  have h3 := congrArg eulerDeriv h1
  rw [eulerDeriv_mul, eulerDeriv_one, eulerDeriv_sub, eulerDeriv_one, h2] at h3
  linear_combination (-(1 - u)) * h3 + (P * (1 - u) - eulerDeriv u) * h1

end VOA.Moonshine.ConwayNorton
