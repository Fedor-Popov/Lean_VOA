import VOA.DeligneAudit.SL4TStratumOrbitCount
import VOA.DeligneAudit.SL4TDoubledSiteCatalog

/-!
# Site words and the multi-doubled word catalog

A site word has `k` doubled sites, each one of the ten surviving pairs of middle-site states,
followed by `n` simple sites, each one of the four states. The multi-doubled catalog is the
list of the data of all words, in catalog order: every catalog sum is the sum over all words.
The data of a word are its block parameters, which depend only on its colour content (the
number of positions of each block colour), and its double and triple counts; the triple
count is the number of doubled sites made of two characteristic roots.

Conversely, every pair of colours is one of the ten surviving pairs and every colour is a
state, so a site colour multiplicity function with two positions at each doubled site and one
at each simple site is the multiplicity function of a unique word. The selected doubled sites
of the multiplicity function are the triples of the word, and its colour content is that of
the word.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- The sum of a function over a flattened list. -/
theorem list_map_flatMap_sum {ι α : Type*} (l : List ι) (f : ι → List α) (F : α → ℕ) :
    ((l.flatMap f).map F).sum = (l.map fun i => ((f i).map F).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- The middle-flag block colour of a middle-site state. -/
def mixedBStateColour : MixedBState → Fin 4
  | .s1 => 0
  | .d1 => 1
  | .s2 => 2
  | .d2 => 3

theorem mixedBStateColour_order (i : Fin 4) : mixedBStateColour (mixedBOrder i) = i := by
  fin_cases i <;> rfl

theorem mixedBOrder_stateColour (s : MixedBState) : mixedBOrder (mixedBStateColour s) = s := by
  cases s <;> rfl

/-- The colour multiplicities of a simple site. -/
def simpleSiteColourCount (i c : Fin 4) : ℕ := if i = c then 1 else 0

/-- The colour multiplicities of a doubled site with one of the ten surviving pairs. -/
def doubledSiteColourCount (i : Fin 10) (c : Fin 4) : ℕ :=
  simpleSiteColourCount (mixedBStateColour (doubledSitePairStates i).1) c +
    simpleSiteColourCount (mixedBStateColour (doubledSitePairStates i).2) c

/-- Words with `k` doubled sites followed by `n` simple sites. -/
abbrev SiteWord (k n : ℕ) := (Fin k → Fin 10) × (Fin n → Fin 4)

/-- The catalog data of a word of simple sites. -/
def simpleSiteWordData : (n : ℕ) → (Fin n → Fin 4) → MixedParams × MixedCellCounts
  | 0, _ => (mixedEmptyParams, (0, 0))
  | n + 1, w => mixedBPrepend (mixedBOrder (w 0)) (simpleSiteWordData n (Fin.tail w))

/-- The catalog data of a word. -/
def siteWordData : (k n : ℕ) → SiteWord k n → MixedParams × MixedCellCounts
  | 0, n, w => simpleSiteWordData n w.2
  | k + 1, n, w => doubledSitePrepend (doubledSitePairStates (w.1 0))
      (siteWordData k n (Fin.tail w.1, w.2))

/-! ## Catalog sums are word sums -/

/-- A sum over tuples of length `n + 1` splits off the first entry. -/
theorem sum_tuple_succ {β : Type*} [Fintype β] (n : ℕ) (G : (Fin (n + 1) → β) → ℕ) :
    ∑ w, G w = ∑ a : β, ∑ w : Fin n → β, G (Fin.cons a w) := by
  rw [← (Fin.consEquiv fun _ => β).sum_comp, Fintype.sum_prod_type]
  rfl

theorem mixedCellCatalog_zero_map_sum (n : ℕ) (F : MixedParams × MixedCellCounts → ℕ) :
    ((mixedCellCatalog 0 n).map F).sum = ∑ w : Fin n → Fin 4, F (simpleSiteWordData n w) := by
  induction n generalizing F with
  | zero =>
      simp [mixedCellCatalog, mixedACellCatalog, simpleSiteWordData]
  | succ n ih =>
      rw [mixedCellCatalog, list_map_flatMap_sum, sum_tuple_succ, Fin.sum_univ_four,
        show List.range 4 = [0, 1, 2, 3] from rfl]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        simpleSiteWordData, Fin.cons_zero, Fin.tail_cons]
      simp only [show (0 : ℕ) < 4 by decide, show (1 : ℕ) < 4 by decide,
        show (2 : ℕ) < 4 by decide, show (3 : ℕ) < 4 by decide, dif_pos, List.map_map]
      rw [ih, ih, ih, ih]
      simp only [Function.comp_def, add_assoc]
      rfl

theorem multiDoubledSiteCellCatalog_map_sum (k n : ℕ) (F : MixedParams × MixedCellCounts → ℕ) :
    ((multiDoubledSiteCellCatalog k n).map F).sum =
      ∑ w : SiteWord k n, F (siteWordData k n w) := by
  induction k generalizing F with
  | zero =>
      rw [multiDoubledSiteCellCatalog, mixedCellCatalog_zero_map_sum, Fintype.sum_prod_type]
      simp [siteWordData]
  | succ k ih =>
      rw [multiDoubledSiteCellCatalog, list_map_flatMap_sum, doubledSitePairs_indexed,
        List.map_map, Fintype.sum_prod_type, sum_tuple_succ, Fin.sum_univ_def]
      congr 1
      apply List.map_congr_left
      intro a _
      simp only [Function.comp_apply, List.map_map]
      rw [ih, Fintype.sum_prod_type]
      rfl

/-! ## Closed forms of the word data -/

/-- The colour content of a word. -/
def siteWordContent {k n : ℕ} (w : SiteWord k n) (c : Fin 4) : ℕ :=
  ∑ a, doubledSiteColourCount (w.1 a) c + ∑ b, simpleSiteColourCount (w.2 b) c

/-- The doubled sites of a word made of two characteristic roots. -/
def siteWordTriples {k n : ℕ} (w : SiteWord k n) : ℕ :=
  ∑ a, doubledSiteTripleCount (doubledSitePairStates (w.1 a))

/-- Block parameters with zero outer label determined by a colour content. -/
def mixedParamsOfContent (v : Fin 4 → ℕ) : MixedParams :=
  ⟨0, ((v 0 + v 1 + v 2 + v 3 : ℕ) : ℤ), 0, ((v 2 + v 3 : ℕ) : ℤ), 0, (v 1 : ℤ), (v 2 : ℤ)⟩

theorem mixedBPrevious_ofContent (v : Fin 4 → ℕ) (i : Fin 4) :
    mixedBPrevious (mixedParamsOfContent v) (mixedBOrder i) =
      mixedParamsOfContent (fun c => v c + simpleSiteColourCount i c) := by
  fin_cases i <;>
    simp [mixedBPrevious, mixedParamsOfContent, mixedBOrder, simpleSiteColourCount] <;> omega

theorem mixedParamsOfContent_injective : Function.Injective mixedParamsOfContent := by
  intro v v' h
  simp only [mixedParamsOfContent, MixedParams.mk.injEq, true_and] at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  funext c
  fin_cases c <;> simp <;> omega

theorem simpleSiteWordData_params (n : ℕ) (w : Fin n → Fin 4) :
    (simpleSiteWordData n w).1 =
      mixedParamsOfContent (fun c => ∑ b, simpleSiteColourCount (w b) c) := by
  induction n with
  | zero => simp [simpleSiteWordData, mixedEmptyParams, mixedParamsOfContent]
  | succ n ih =>
      simp only [simpleSiteWordData, mixedBPrepend]
      rw [ih, mixedBPrevious_ofContent]
      congr 1
      funext c
      rw [Fin.sum_univ_succ]
      simp only [Fin.tail]
      ring

theorem simpleSiteWordData_triples (n : ℕ) (w : Fin n → Fin 4) :
    (simpleSiteWordData n w).2.2 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [simpleSiteWordData, mixedBPrepend]
      simp [mixedCellShift, ih]

theorem siteWordData_params (k n : ℕ) (w : SiteWord k n) :
    (siteWordData k n w).1 = mixedParamsOfContent (siteWordContent w) := by
  induction k with
  | zero =>
      rw [siteWordData, simpleSiteWordData_params]
      congr 1
      funext c
      simp [siteWordContent]
  | succ k ih =>
      rw [siteWordData, doubledSitePrepend]
      dsimp only
      rw [ih, ← mixedBOrder_stateColour (doubledSitePairStates (w.1 0)).2,
        mixedBPrevious_ofContent, ← mixedBOrder_stateColour (doubledSitePairStates (w.1 0)).1,
        mixedBPrevious_ofContent]
      congr 1
      funext c
      simp only [siteWordContent, Fin.sum_univ_succ, doubledSiteColourCount, Fin.tail]
      ring

theorem siteWordData_triples (k n : ℕ) (w : SiteWord k n) :
    (siteWordData k n w).2.2 = siteWordTriples w := by
  induction k with
  | zero =>
      rw [siteWordData, simpleSiteWordData_triples]
      simp [siteWordTriples]
  | succ k ih =>
      rw [siteWordData, doubledSitePrepend]
      simp only [mixedCellShift]
      rw [ih]
      simp only [siteWordTriples, Fin.sum_univ_succ, Fin.tail]
      ring

/-- Catalog fibers are catalog sums restricted to a block. -/
theorem mixedCatalogFiber_map_sum (q : MixedParams) (l : List (MixedParams × MixedCellCounts))
    (g : MixedCellCounts → ℕ) :
    ((mixedCatalogFiber q l).map g).sum = (l.map fun c => if c.1 = q then g c.2 else 0).sum := by
  induction l with
  | nil => rfl
  | cons c l ih =>
      by_cases h : c.1 = q
      · simp only [mixedCatalogFiber, List.filterMap_cons, h, if_true, List.map_cons,
          List.sum_cons] at ih ⊢
        rw [ih]
      · simp only [mixedCatalogFiber, List.filterMap_cons, h, if_false, List.map_cons,
          List.sum_cons, zero_add] at ih ⊢
        exact ih

/-! ## Decoding site colour multiplicities -/

/-- Every two-element multiset of colours is one of the ten surviving pairs. -/
theorem exists_doubledSiteColourCount (v : Fin 4 → ℕ) (hv : ∑ c, v c = 2) :
    ∃ i : Fin 10, doubledSiteColourCount i = v := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℕ, v = ![a, b, c, d] :=
    ⟨v 0, v 1, v 2, v 3, by funext x; fin_cases x <;> rfl⟩
  simp [Fin.sum_univ_four] at hv
  have ha : a ≤ 2 := by omega
  have hb : b ≤ 2 := by omega
  have hc : c ≤ 2 := by omega
  obtain rfl : d = 2 - a - b - c := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first | omega | decide

/-- Every colour is a simple-site state. -/
theorem exists_simpleSiteColourCount (v : Fin 4 → ℕ) (hv : ∑ c, v c = 1) :
    ∃ i : Fin 4, simpleSiteColourCount i = v := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℕ, v = ![a, b, c, d] :=
    ⟨v 0, v 1, v 2, v 3, by funext x; fin_cases x <;> rfl⟩
  simp [Fin.sum_univ_four] at hv
  have ha : a ≤ 1 := by omega
  have hb : b ≤ 1 := by omega
  have hc : c ≤ 1 := by omega
  obtain rfl : d = 1 - a - b - c := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first | omega | decide

/-- A pair is a triple exactly when it has no position of the non-characteristic colours. -/
theorem doubledSiteTripleCount_eq (i : Fin 10) :
    doubledSiteTripleCount (doubledSitePairStates i) =
      if doubledSiteColourCount i 0 = 0 ∧ doubledSiteColourCount i 2 = 0 then 1 else 0 := by
  fin_cases i <;> decide

/-- Decode the colour multiplicities of a doubled site. -/
def doubledSiteIndexOf (v : Fin 4 → ℕ) : Fin 10 := by
  classical
  exact if h : ∃ i, doubledSiteColourCount i = v then h.choose else 0

/-- Decode the colour multiplicities of a simple site. -/
def simpleSiteIndexOf (v : Fin 4 → ℕ) : Fin 4 := by
  classical
  exact if h : ∃ i, simpleSiteColourCount i = v then h.choose else 0

theorem doubledSiteIndexOf_spec (v : Fin 4 → ℕ) (hv : ∑ c, v c = 2) :
    doubledSiteColourCount (doubledSiteIndexOf v) = v := by
  classical
  have h := exists_doubledSiteColourCount v hv
  unfold doubledSiteIndexOf
  rw [dif_pos h]
  exact h.choose_spec

theorem simpleSiteIndexOf_spec (v : Fin 4 → ℕ) (hv : ∑ c, v c = 1) :
    simpleSiteColourCount (simpleSiteIndexOf v) = v := by
  classical
  have h := exists_simpleSiteColourCount v hv
  unfold simpleSiteIndexOf
  rw [dif_pos h]
  exact h.choose_spec

/-- The word of a site colour multiplicity function. -/
def siteWordOf (k n : ℕ) {S : ℕ} (hS : S = k + n) (m : Fin S → Fin 4 → ℕ) : SiteWord k n :=
  (fun a => doubledSiteIndexOf (m ⟨a.val, by omega⟩),
    fun b => simpleSiteIndexOf (m ⟨k + b.val, by omega⟩))

/-- Split a sum over the sites into the doubled and the simple sites. -/
theorem sum_sites_split (k n : ℕ) {S : ℕ} (hS : S = k + n) (f : Fin S → ℕ) :
    ∑ a, f a = ∑ a : Fin k, f ⟨a.val, by omega⟩ + ∑ b : Fin n, f ⟨k + b.val, by omega⟩ := by
  rw [Fintype.sum_equiv (finCongr hS) f (fun b => f ((finCongr hS).symm b))
    (fun x => by simp), Fin.sum_univ_add]
  rfl

end

end VOA.DeligneAudit.SL4T
