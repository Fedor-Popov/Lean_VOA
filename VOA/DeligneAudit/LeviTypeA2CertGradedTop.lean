import VOA.DeligneAudit.LeviTypeA2CertGradedPositions

/-! The top Wick contraction preserves both radical counts and degree. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V]
  [Module A V] [Module ℂ V]

/-- The top Wick decomposition with its lower terms in one graded key. -/
def GradedBoxTopDecomposition (a b : ℕ → A) (k s : ℕ)
    (xs ys : List ℕ) (R : A) (v : V) : Prop :=
  let c : ℂ := (Nat.choose (xs.count 0 + k) k : ℂ)
  topSum a b k s (xs ++ List.replicate k 0) •
      (((ys.map b).prod * R) • v) -
    c • boxTarget a b k s xs ys R v ∈
      gradedLowerModeSpan a b xs ys k (xs.sum + ys.sum + s) R v

theorem box_top_decomposition_graded (a b : ℕ → A)
    (haa : ∀ i j, a i * a j = a j * a i)
    (k s : ℕ) (xs ys : List ℕ) (R : A) (v : V) :
    GradedBoxTopDecomposition a b k s xs ys R v := by
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
      (hnot : ¬ T ⊆ Z) :
      g T • y ∈ gradedLowerModeSpan a b xs ys k
        (xs.sum + ys.sum + s) R v := by
    let p := splitAt (List.finRange L.length) T
    let zs := p.1.map L.get
    let ls := p.2.map L.get
    have hdegree := appended_nonzero_lowers_original xs k T hT hnot
    have hsmall : zs.sum < xs.sum := by
      have hsum : zs.sum =
          ∑ i ∈ (Finset.univ : Finset (Fin L.length)) \ T, L.get i := by
        let ps := (List.finRange L.length).filter fun i => i ∉ T
        have hnd : ps.Nodup := (List.nodup_finRange L.length).filter _
        have hset : ps.toFinset =
            (Finset.univ : Finset (Fin L.length)) \ T := by
          ext i
          simp [ps]
        have h := List.sum_toFinset L.get hnd
        simpa only [splitAt, ps, hset] using h.symm
      rw [hsum]
      exact hdegree
    have hsplit := splitAt_mode_length_sum L T
    have hsel := splitAt_selected_length (List.finRange L.length)
      (List.nodup_finRange L.length) T
      (by simpa only [List.toFinset_finRange] using
        (Finset.mem_powersetCard.mp hT).1)
    have hls : ls.length = k := by
      simpa [ls, p, L, S] using
        (show (p.2.map L.get).length = k by
          simpa [p, List.length_map] using
            (hsel.trans (Finset.mem_powersetCard.mp hT).2))
    have hzs : zs.length = xs.length := by
      have hlen := hsplit.1
      change zs.length + ls.length = L.length at hlen
      simp only [L, List.length_append, List.length_replicate] at hlen
      omega
    have hsum : zs.sum + ls.sum = xs.sum := by
      have hs := hsplit.2
      change zs.sum + ls.sum = L.sum at hs
      simpa [L, List.sum_append] using hs
    have h := coeff_bWord_graded_mem a b xs ys zs ls [] k s
      (xs.sum + ys.sum + s) R v hsmall hzs (by simpa using hls) (by
        simp only [List.sum_nil]
        omega)
    simpa [g, positionalTopTerm, y, B, p, zs, ls, mul_assoc, mul_smul]
      using h
  have hnsum : nsum • y ∈ gradedLowerModeSpan a b xs ys k
      (xs.sum + ys.sum + s) R v := by
    dsimp only [nsum]
    rw [Finset.sum_smul]
    apply (gradedLowerModeSpan a b xs ys k (xs.sum + ys.sum + s) R v).sum_mem
    intro T hT
    exact hn T (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hT).2
  have hsplit : topSum a b k s L = zsum + nsum := by
    simpa [L, S, Z, g, zsum, nsum, x] using
      topSum_zero_nonzero_split a b k s L
  change topSum a b k s L • y - c • boxTarget a b k s xs ys R v ∈
    gradedLowerModeSpan a b xs ys k (xs.sum + ys.sum + s) R v
  rw [hsplit, add_smul, hzsum]
  simpa using hnsum

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.box_top_decomposition_graded
