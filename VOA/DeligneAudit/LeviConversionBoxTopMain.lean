import VOA.DeligneAudit.LeviConversionBoxTopCoeff

/-! Universal top-contraction decomposition and Corollary C'. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V]
  [Module A V] [Module ℂ V]

private theorem uncontracted_sum (xs : List ℕ)
    (T : Finset (Fin xs.length)) :
    ((splitAt (List.finRange xs.length) T).1.map xs.get).sum =
      ∑ i ∈ (Finset.univ : Finset (Fin xs.length)) \ T, xs.get i := by
  let ps := (List.finRange xs.length).filter fun i => i ∉ T
  have hnd : ps.Nodup := (List.nodup_finRange xs.length).filter _
  have hset : ps.toFinset = (Finset.univ : Finset (Fin xs.length)) \ T := by
    ext i
    simp [ps]
  have h := List.sum_toFinset xs.get hnd
  simpa only [splitAt, ps, hset] using h.symm

omit [Algebra ℂ A] in
/-- The universal finite decomposition in Corollary C'.  The `a` modes
commute pairwise; no commutation among `b` modes is required here. -/
theorem box_top_decomposition (a b : ℕ → A)
    (haa : ∀ i j, a i * a j = a j * a i)
    (k s : ℕ) (xs ys : List ℕ) (R : A) (v : V) :
    BoxTopDecomposition a b k s xs ys R v := by
  let L := xs ++ List.replicate k 0
  let x : Fin L.length → ℕ := L.get
  let S : Finset (Finset (Fin L.length)) :=
    (Finset.univ : Finset (Fin L.length)).powersetCard k
  let Z := zeroPositions x
  let g : Finset (Fin L.length) → A := positionalTopTerm a b s L
  let B : A := (ys.map b).prod
  let y : V := (B * R) • v
  let c : ℂ := (Nat.choose (xs.count 0 + k) k : ℂ)
  let zsum := ∑ T ∈ S.filter (fun T => T ⊆ Z), g T
  let nsum := ∑ T ∈ S.filter (fun T => ¬ T ⊆ Z), g T
  have hfilter : S.filter (fun T => T ⊆ Z) = Z.powersetCard k := by
    ext T
    simp only [Finset.mem_filter, S, Finset.mem_powersetCard]
    simpa only [Finset.subset_univ, true_and] using
      (and_comm : T.card = k ∧ T ⊆ Z ↔ T ⊆ Z ∧ T.card = k)
  have hcard : (S.filter (fun T => T ⊆ Z)).card =
      Nat.choose (xs.count 0 + k) k := by
    rw [hfilter, zero_contraction_count]
    rw [show Z.card = xs.count 0 + k from appended_zero_positions_card xs k]
  have hzero (T : Finset (Fin L.length)) (hT : T ∈ S)
      (hz : T ⊆ Z) : g T • y = boxTarget a b k s xs ys R v := by
    have ha := selected_aWord_zero a haa xs k T hT hz
    have hb := selected_bWord_zero b L k T hT hz
    have ha' : aWord a ((splitAt (List.finRange L.length) T).1.map L.get) =
        aWord a xs := by simpa only [L] using ha
    simp [g, positionalTopTerm, y, B, boxTarget, ha', hb, mul_assoc, mul_smul]
  have hzsum : zsum • y = c • boxTarget a b k s xs ys R v := by
    dsimp only [zsum]
    rw [Finset.sum_smul]
    have hsum : (∑ T ∈ S.filter (fun T => T ⊆ Z), g T • y) =
        ∑ _T ∈ S.filter (fun T => T ⊆ Z),
          boxTarget a b k s xs ys R v := by
      apply Finset.sum_congr rfl
      intro T hT
      exact hzero T (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hT).2
    rw [hsum]
    rw [Finset.sum_const, hcard]
    exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm
  have hn (T : Finset (Fin L.length)) (hT : T ∈ S)
      (hnot : ¬ T ⊆ Z) : g T • y ∈ lowerModeSpan a b xs R v := by
    let p := splitAt (List.finRange L.length) T
    let zs := p.1.map L.get
    let ls := p.2.map L.get
    have hdegree := appended_nonzero_lowers_original xs k T hT hnot
    have hsmall : zs.sum < xs.sum := by
      rw [show zs.sum = ∑ i ∈ (Finset.univ : Finset (Fin L.length)) \ T,
        L.get i from uncontracted_sum L T]
      exact hdegree
    have h := coeff_bWord_lower_mem a b xs zs ls [] ys R v hsmall s
    simpa [g, positionalTopTerm, y, B, p, zs, ls, mul_assoc, mul_smul]
      using h
  have hnsum : nsum • y ∈ lowerModeSpan a b xs R v := by
    dsimp only [nsum]
    rw [Finset.sum_smul]
    apply (lowerModeSpan a b xs R v).sum_mem
    intro T hT
    exact hn T (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hT).2
  have hsplit : topSum a b k s L = zsum + nsum := by
    simpa [L, S, Z, g, zsum, nsum, x] using
      topSum_zero_nonzero_split a b k s L
  change topSum a b k s L • y - c • boxTarget a b k s xs ys R v ∈
    lowerModeSpan a b xs R v
  rw [hsplit, add_smul, hzsum]
  simpa using hnsum

/-- Corollary C': top conversion modulo the higher Wick terms, with the
finite top decomposition discharged under commuting `a` modes. -/
theorem box_conversion (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (haa : ∀ i j, a i * a j = a j * a i)
    (k s : ℕ) (xs ys : List ℕ) (R : A) (v : V)
    (hRf : ∀ i, R * f i = f i * R)
    (hkill : PowerSeries.coeff s (fCurrent f ^ k) • v = 0)
    (hscalar : ∀ c : ℂ, ∀ w : V, (algebraMap ℂ A c) • w = c • w)
    (N : Submodule ℂ V)
    (hHigher : ∀ p ∈ choices (xs ++ List.replicate k 0), p.2.length < k →
      conversionTerm f a b k s p • (((ys.map b).prod * R) • v) ∈ N) :
    boxTarget a b k s xs ys R v ∈ lowerModeSpan a b xs R v ⊔ N := by
  exact box_conversion_of_higher_terms f a b hfa hfb hab k s xs ys R v
    hRf hkill hscalar N hHigher (box_top_decomposition a b haa k s xs ys R v)

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.box_top_decomposition
#print axioms VOA.DeligneAudit.LeviConversion.box_conversion
