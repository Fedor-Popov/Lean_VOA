import VOA.DeligneAudit.DeligneFusionCL

/-!
# `CLCount` — the Chari–Loktev family has the Gelfand–Tsetlin graded count

`qbinomCoeff (B + ℓ) ℓ d` counts weakly monotone `ℓ`-tuples with entries `≤ B` and sum `d`
(`ncard_dec`, by the Pascal rule splitting off the maximal entry), and `CLIdx N d` decomposes
into products of three such boxes matching `gl3Hilb (2N) N 0` term by term.
-/

namespace VOA.DeligneAudit.CL

open VOA.DeligneAudit.A2

noncomputable section

/-- Weakly decreasing `ℓ`-tuples with entries `≤ B` and sum `d`. -/
def Dec (B ℓ d : ℕ) : Set (List ℕ) :=
  {s | s.Pairwise (· ≥ ·) ∧ s.length = ℓ ∧ (∀ x ∈ s, x ≤ B) ∧ s.sum = d}

theorem Dec_finite (B ℓ d : ℕ) : (Dec B ℓ d).Finite :=
  (finite_lists ℓ B).subset fun s hs => ⟨hs.2.1.le, hs.2.2.1⟩

theorem qbinomCoeff_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → ∀ N, qbinomCoeff n k N = 0
  | 0, k + 1, _, N => by simp [qbinomCoeff]
  | n + 1, k + 1, h, N => by
      rw [qbinomCoeff, qbinomCoeff_eq_zero_of_lt (by omega), qbinomCoeff_eq_zero_of_lt (by omega)]
      simp

theorem Dec_zero (B d : ℕ) : Dec B 0 d = if d = 0 then {[]} else ∅ := by
  ext s
  simp only [Dec, Set.mem_setOf_eq, List.length_eq_zero_iff]
  split_ifs with hd
  · subst hd; constructor
    · rintro ⟨-, rfl, -, -⟩; rfl
    · rintro rfl; simp
  · simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, rfl, -, rfl⟩; exact hd rfl

/-- The Pascal split by the maximal (first) entry. -/
theorem Dec_succ (B ℓ d : ℕ) :
    Dec B (ℓ + 1) d = (if B ≤ d then List.cons B '' Dec B ℓ (d - B) else ∅) ∪
      (if 1 ≤ B then Dec (B - 1) (ℓ + 1) d else ∅) := by
  ext s
  constructor
  · rintro ⟨hp, hl, hB, hs⟩
    obtain ⟨x, t, rfl⟩ : ∃ x t, s = x :: t := by
      cases s with
      | nil => simp at hl
      | cons x t => exact ⟨x, t, rfl⟩
    rw [List.pairwise_cons] at hp
    have hxB := hB x List.mem_cons_self
    by_cases hx : x = B
    · subst hx
      left
      rw [List.sum_cons] at hs
      rw [if_pos (by omega)]
      exact ⟨t, ⟨hp.2, by simpa using hl, fun y hy => hp.1 y hy, by omega⟩, rfl⟩
    · right
      rw [if_pos (by omega)]
      refine ⟨List.pairwise_cons.mpr hp, hl, fun y hy => ?_, hs⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := hp.1 y hy; omega
  · rintro (h | h)
    · split_ifs at h with hBd
      · obtain ⟨t, ⟨hp, hl, hB, hs⟩, rfl⟩ := h
        refine ⟨List.pairwise_cons.mpr ⟨fun y hy => hB y hy, hp⟩, by simp [hl], fun y hy => ?_, ?_⟩
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact le_rfl
          · exact hB y hy
        · rw [List.sum_cons, hs]; omega
      · exact absurd h (Set.notMem_empty _)
    · split_ifs at h with hB1
      · obtain ⟨hp, hl, hB, hs⟩ := h
        exact ⟨hp, hl, fun y hy => by have := hB y hy; omega, hs⟩
      · exact absurd h (Set.notMem_empty _)

theorem Dec_disjoint (B ℓ d : ℕ) :
    Disjoint (if B ≤ d then List.cons B '' Dec B ℓ (d - B) else ∅)
      (if 1 ≤ B then Dec (B - 1) (ℓ + 1) d else ∅) := by
  rw [Set.disjoint_left]
  intro s h1 h2
  split_ifs at h1 h2
  all_goals first | exact absurd h1 (Set.notMem_empty _) | exact absurd h2 (Set.notMem_empty _) | skip
  obtain ⟨t, -, rfl⟩ := h1
  have := h2.2.2.1 B List.mem_cons_self
  omega

/-- **Box count**: `|Dec B ℓ d| = qbinomCoeff (B + ℓ) ℓ d`. -/
theorem ncard_dec : ∀ ℓ B d : ℕ, (Dec B ℓ d).ncard = qbinomCoeff (B + ℓ) ℓ d
  | 0, B, d => by
      rw [Dec_zero]; split_ifs with hd <;> simp [qbinomCoeff, hd]
  | ℓ + 1, B, d => by
      have hs : (if B ≤ d then List.cons B '' Dec B ℓ (d - B) else ∅).Finite := by
        split_ifs
        · exact (Dec_finite _ _ _).image _
        · exact Set.finite_empty
      have ht : (if 1 ≤ B then Dec (B - 1) (ℓ + 1) d else ∅).Finite := by
        split_ifs
        · exact Dec_finite _ _ _
        · exact Set.finite_empty
      rw [Dec_succ, Set.ncard_union_eq (Dec_disjoint B ℓ d) hs ht]
      rw [show B + (ℓ + 1) = (B + ℓ) + 1 by ring, qbinomCoeff, show B + ℓ - ℓ = B by omega]
      congr 1
      · split_ifs with h
        · rw [Set.ncard_image_of_injective _ List.cons_injective, ncard_dec ℓ B (d - B)]
        · simp
      · split_ifs with h
        · rw [ncard_dec (ℓ + 1) (B - 1) d, show B - 1 + (ℓ + 1) = B + ℓ by omega]
        · rw [Set.ncard_empty, show B = 0 by omega, zero_add,
            qbinomCoeff_eq_zero_of_lt (by omega)]

/-! ## Increasing boxes -/

/-- Weakly increasing `ℓ`-tuples with entries `≤ B` and sum `d` (the `BoxT` version). -/
def Inc (B ℓ d : ℕ) : Set (List ℕ) := {s | BoxT (B : ℤ) s ∧ s.length = ℓ ∧ s.sum = d}

theorem Inc_eq_image (B ℓ d : ℕ) : Inc B ℓ d = List.reverse '' Dec B ℓ d := by
  ext s
  constructor
  · rintro ⟨⟨hp, hB⟩, hl, hs⟩
    refine ⟨s.reverse, ⟨?_, by simpa using hl, fun x hx => ?_, by simpa using hs⟩, by simp⟩
    · rw [List.pairwise_reverse]; exact hp
    · have := hB x (List.mem_reverse.mp hx); omega
  · rintro ⟨t, ⟨hp, hl, hB, hs⟩, rfl⟩
    refine ⟨⟨?_, fun x hx => ?_⟩, by simpa using hl, by simpa using hs⟩
    · rw [List.pairwise_reverse]; exact hp
    · have := hB x (List.mem_reverse.mp hx); omega

theorem ncard_inc (B ℓ d : ℕ) : (Inc B ℓ d).ncard = qbinomCoeff (B + ℓ) ℓ d := by
  rw [Inc_eq_image, Set.ncard_image_of_injective _ List.reverse_injective, ncard_dec]

theorem Inc_finite (B ℓ d : ℕ) : (Inc B ℓ d).Finite := by
  rw [Inc_eq_image]; exact (Dec_finite B ℓ d).image _

/-- A `BoxT` list with negative bound is empty. -/
theorem boxT_nil_of_neg {B : ℤ} {s : List ℕ} (h : BoxT B s) (hB : B < 0) : s = [] := by
  cases s with
  | nil => rfl
  | cons x t => have := h.2 x List.mem_cons_self; omega

/-! ## Fibres of `CLIdx` -/

/-- The fibre key `(|b|, |c|, |a|, Σb, Σb + Σc)`. -/
def key (i : List ℕ × List ℕ × List ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (i.2.1.length, i.2.2.length, i.1.length, i.2.1.sum, i.2.1.sum + i.2.2.sum)

/-- The count of one fibre. -/
def fib (N d : ℕ) (x : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ :=
  if x.2.2.2.1 ≤ x.2.2.2.2 ∧ x.2.2.2.2 ≤ d then
    qbinomCoeff N x.1 x.2.2.2.1 * qbinomCoeff N x.2.1 (x.2.2.2.2 - x.2.2.2.1) *
      qbinomCoeff (N + x.2.1 - x.1) x.2.2.1 (d - x.2.2.2.2)
  else 0

theorem fiber_ncard (N d : ℕ) (x : ℕ × ℕ × ℕ × ℕ × ℕ) (h1 : x.1 ≤ N) (h2 : x.2.1 ≤ N) :
    {i | i ∈ CLIdx N d ∧ key i = x}.ncard = fib N d x := by
  obtain ⟨l12, l22, l11, j, k⟩ := x
  simp only at h1 h2
  unfold fib
  simp only
  by_cases hjk : j ≤ k ∧ k ≤ d
  · rw [if_pos hjk]
    by_cases h11 : l11 ≤ N + l22 - l12
    · have hset : {i | i ∈ CLIdx N d ∧ key i = (l12, l22, l11, j, k)} =
          Inc (N + l22 - l12 - l11) l11 (d - k) ×ˢ (Inc (N - l12) l12 j ×ˢ Inc (N - l22) l22 (k - j)) := by
        ext ⟨a, b, c⟩
        simp only [Set.mem_setOf_eq, CLIdx, Adm, tdeg, key, Inc, Set.mem_prod, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨⟨hb, hc, ha⟩, hd⟩, rfl, rfl, rfl, rfl, hk⟩
          refine ⟨⟨?_, rfl, by omega⟩, ⟨?_, rfl, rfl⟩, ⟨?_, rfl, by omega⟩⟩
          · convert ha using 1; push_cast; omega
          · convert hb using 1; push_cast; omega
          · convert hc using 1; push_cast; omega
        · rintro ⟨⟨ha, rfl, hsa⟩, ⟨hb, rfl, rfl⟩, ⟨hc, rfl, hsc⟩⟩
          refine ⟨⟨⟨?_, ?_, ?_⟩, by omega⟩, rfl, rfl, rfl, rfl, by omega⟩
          · convert hb using 1; push_cast; omega
          · convert hc using 1; push_cast; omega
          · convert ha using 1; push_cast; omega
      rw [hset, Set.ncard_prod, Set.ncard_prod, ncard_inc, ncard_inc, ncard_inc,
        show N + l22 - l12 - l11 + l11 = N + l22 - l12 by omega, show N - l12 + l12 = N by omega,
        show N - l22 + l22 = N by omega]
      ring
    · rw [qbinomCoeff_eq_zero_of_lt (n := N + l22 - l12) (k := l11) (by omega), mul_zero, Set.ncard_eq_zero (Set.Finite.subset
        (CLIdx_finite N d) fun i hi => hi.1)]
      ext ⟨a, b, c⟩
      simp only [Set.mem_setOf_eq, CLIdx, Adm, key, Set.mem_empty_iff_false, iff_false, not_and,
        Prod.mk.injEq]
      rintro ⟨⟨hb, hc, ha⟩, -⟩ rfl rfl rfl
      have := boxT_nil_of_neg ha (by push_cast; omega)
      subst this; simp at h11
  · rw [if_neg hjk, Set.ncard_eq_zero (Set.Finite.subset (CLIdx_finite N d) fun i hi => hi.1)]
    ext ⟨a, b, c⟩
    simp only [Set.mem_setOf_eq, CLIdx, tdeg, key, Set.mem_empty_iff_false, iff_false, not_and,
      Prod.mk.injEq]
    rintro ⟨-, hd⟩ - - - rfl rfl
    omega

/-! ## Summing the fibres -/

theorem adm_bounds {N d : ℕ} {a b c : List ℕ} (h : (a, b, c) ∈ CLIdx N d) :
    b.length ≤ N ∧ c.length ≤ N ∧ a.length ≤ 2 * N ∧ b.sum ≤ d ∧ b.sum + c.sum ≤ d := by
  obtain ⟨⟨hb, hc, ha⟩, hd⟩ := h
  dsimp only at hb hc ha hd
  unfold tdeg at hd; dsimp only at hd
  have lenb : b.length ≤ N := by
    rcases b with _ | ⟨x, b'⟩
    · simp
    · have := hb.2 x List.mem_cons_self; simp only [List.length_cons] at this ⊢; push_cast at this; omega
  have lenc : c.length ≤ N := by
    rcases c with _ | ⟨x, c'⟩
    · simp
    · have := hc.2 x List.mem_cons_self; simp only [List.length_cons] at this ⊢; push_cast at this; omega
  have lena : a.length ≤ 2 * N := by
    rcases a with _ | ⟨x, a'⟩
    · simp
    · have := ha.2 x List.mem_cons_self; simp only [List.length_cons] at this ⊢; push_cast at this
      omega
  exact ⟨lenb, lenc, lena, by omega, by omega⟩

/-- The key range. -/
def keyRange (N d : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ Finset.range (2 * N + 1) ×ˢ
    Finset.range (d + 1) ×ˢ Finset.range (d + 1)

theorem ncard_CLIdx_eq_sum (N d : ℕ) :
    (CLIdx N d).ncard = ∑ x ∈ keyRange N d, fib N d x := by
  classical
  have hfin := CLIdx_finite N d
  rw [Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_card_fiberwise (f := key) (t := keyRange N d) ?_]
  · refine Finset.sum_congr rfl fun x hx => ?_
    simp only [keyRange, Finset.mem_product, Finset.mem_range] at hx
    rw [← fiber_ncard N d x (by omega) (by omega), ← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [Set.Finite.mem_toFinset]
  · rintro ⟨a, b, c⟩ hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hi
    obtain ⟨h1, h2, h3, h4, h5⟩ := adm_bounds hi
    simp only [Finset.mem_coe, key, keyRange, Finset.mem_product, Finset.mem_range]
    omega

/-! ## Matching the Gelfand–Tsetlin sum -/

theorem sum_Icc_reflect {M : Type*} [AddCommMonoid M] (a n : ℕ) (F : ℕ → M) :
    ∑ m ∈ Finset.Icc a (a + n), F m = ∑ l ∈ Finset.range (n + 1), F (a + n - l) := by
  rw [show Finset.Icc a (a + n) = Finset.Ico a (a + n + 1) by ext; simp,
    Finset.sum_Ico_eq_sum_range, show a + n + 1 - a = n + 1 by omega,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_range] at hl
  congr 1; omega

theorem gl2Hilb_eq (N l12 l22 x : ℕ) (h1 : l12 ≤ N) (h2 : l22 ≤ N) :
    gl2Hilb (2 * N - l12) (N - l22) x =
      ∑ l11 ∈ Finset.range (2 * N + 1), qbinomCoeff (N + l22 - l12) l11 x := by
  rw [gl2Hilb, show 2 * N - l12 = (N - l22) + (N + l22 - l12) by omega, sum_Icc_reflect]
  rw [show N - l22 + (N + l22 - l12) - (N - l22) = N + l22 - l12 by omega]
  have hsub : Finset.range (N + l22 - l12 + 1) ⊆ Finset.range (2 * N + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub ?_]
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    congr 1; omega
  · intro l hl hnot
    simp only [Finset.mem_range] at hl hnot
    exact qbinomCoeff_eq_zero_of_lt (by omega) x

theorem conv_conv_eq (f g h : ℕ → ℕ) (d : ℕ) :
    conv (conv f g) h d = ∑ k ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
      if j ≤ k then f j * g (k - j) * h (d - k) else 0 := by
  unfold conv
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [Finset.sum_mul, ← Finset.sum_subset (Finset.range_subset_range.mpr (show k + 1 ≤ d + 1 by omega))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [if_pos (by omega)]
  · intro j _ hj
    simp only [Finset.mem_range] at hj
    rw [if_neg (by omega)]

/-- **`CLCount` holds for every `N`.** -/
theorem clCount (N : ℕ) : CLCount N := by
  intro d
  rw [ncard_CLIdx_eq_sum, demazureHilb, gl3Hilb, show 2 * N = N + N by ring, sum_Icc_reflect,
    show (0 : ℕ) = 0 + 0 from rfl]
  simp only [keyRange, Finset.sum_product]
  refine Finset.sum_congr rfl fun l12 hl12 => ?_
  rw [Finset.mem_range] at hl12
  rw [show Finset.Icc (0 + 0) N = Finset.Icc 0 (0 + N) by simp, sum_Icc_reflect]
  refine Finset.sum_congr rfl fun l22 hl22 => ?_
  rw [Finset.mem_range] at hl22
  rw [show N + N - (N + N - l12) = l12 by omega, show N - (0 + 0) = N by omega,
    show N + N - N = N by omega, show 0 + N - l22 = N - l22 by omega,
    show N - (N - l22) = l22 by omega, conv_conv_eq]
  rw [show N + N - l12 = 2 * N - l12 by ring]
  simp only [gl2Hilb_eq N l12 l22 _ (by omega) (by omega), Finset.mul_sum]
  have ite_sum' : ∀ (c : Prop) [Decidable c] (F : ℕ → ℕ),
      (if c then ∑ i ∈ Finset.range (2 * N + 1), F i else 0) =
        ∑ i ∈ Finset.range (2 * N + 1), if c then F i else 0 := by
    intro c _ F; split_ifs <;> simp
  simp only [ite_sum']
  -- RHS is `Σ_z Σ_y Σ_x`; bring it to `Σ_x Σ_y Σ_z`
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun y _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mem_range] at hx
  unfold fib
  simp only
  by_cases hyx : y ≤ x
  · rw [if_pos ⟨hyx, by omega⟩, if_pos hyx]
  · rw [if_neg (fun h => hyx h.1), if_neg hyx]

/-- **U7 from CL-V alone.** -/
theorem demazureRealization_of_independence (N : ℕ) (hi : CLIndependence N) :
    A2.DemazureRealization N :=
  demazureRealization_of_CL N (clCount N) hi

/-- **`Mchar N 0 = demazureHilbSeries N` from CL spanning and CL-V.** -/
theorem Mchar_eq_of_spanning_independence (N : ℕ) (hs : CLSpanning N) (hi : CLIndependence N) :
    SectorWeyl.Mchar N 0 = A2.demazureHilbSeries N :=
  Mchar_eq_of_CL N hs (clCount N) hi

end

end VOA.DeligneAudit.CL

section AxiomAudit
#print axioms VOA.DeligneAudit.CL.ncard_dec
#print axioms VOA.DeligneAudit.CL.clCount
#print axioms VOA.DeligneAudit.CL.demazureRealization_of_independence
#print axioms VOA.DeligneAudit.CL.Mchar_eq_of_spanning_independence
end AxiomAudit
