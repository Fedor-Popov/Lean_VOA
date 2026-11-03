import VOA.DeligneAudit.D4LeviKSRzHsymmVectors

/-! Zero-based mode allocations are exactly the vectors of fixed total. -/

namespace VOA.DeligneAudit.D4Levi

theorem rz_zero_alloc_mem_iff (k s : ℕ) (ys : List ℕ) :
    ys ∈ modeAllocations (List.replicate k 0) s ↔
      ys.length = k ∧ ys.sum = s := by
  induction k generalizing s ys with
  | zero =>
      cases ys with
      | nil =>
          by_cases hs : s = 0
          · subst s; simp [modeAllocations]
          · simp [modeAllocations, hs, eq_comm]
      | cons y ys =>
          by_cases hs : s = 0 <;> simp [modeAllocations, hs]
  | succ k ih =>
      cases ys with
      | nil =>
          simp only [List.replicate_succ, modeAllocations,
            List.mem_flatMap, List.mem_map]
          simp
      | cons y ys =>
          simp only [List.replicate_succ, modeAllocations,
            List.mem_flatMap, List.mem_map]
          constructor
          · rintro ⟨q, hq, zs, hzs, heq⟩
            have hqsum := Finset.mem_antidiagonal.mp
              (Finset.mem_toList.mp hq)
            have hrest := (ih q.2 zs).mp hzs
            simp only [List.cons.injEq] at heq
            rcases heq with ⟨hy, hys⟩
            subst y
            subst ys
            simp only [List.length_cons, List.sum_cons]
            omega
          · rintro ⟨hlen, hsum⟩
            have hyslen : ys.length = k := by simpa using hlen
            have hq : (y, ys.sum) ∈ Finset.antidiagonal s := by
              apply Finset.mem_antidiagonal.mpr
              simpa using hsum
            exact ⟨(y, ys.sum), Finset.mem_toList.mpr hq, ys,
              (ih ys.sum ys).mpr ⟨hyslen, rfl⟩, by simp⟩

theorem rz_zero_alloc_nodup (k s : ℕ) :
    (modeAllocations (List.replicate k 0) s).Nodup := by
  induction k generalizing s with
  | zero =>
      by_cases hs : s = 0 <;> simp [modeAllocations, hs]
  | succ k ih =>
      simp only [List.replicate_succ, modeAllocations]
      apply List.nodup_flatMap.mpr
      constructor
      · intro q hq
        exact (ih q.2).map (by
          intro x y hxy
          exact (List.cons.inj hxy).2)
      · apply (Finset.nodup_toList (Finset.antidiagonal s)).imp
        intro q r hne ys hysq hysr
        obtain ⟨zs, hzs, heq⟩ := List.mem_map.mp hysq
        obtain ⟨ts, hts, heq'⟩ := List.mem_map.mp hysr
        have hqsum := (rz_zero_alloc_mem_iff k q.2 zs).mp hzs
        have hrsum := (rz_zero_alloc_mem_iff k r.2 ts).mp hts
        have hh : (q.1 :: zs) = (r.1 :: ts) := by
          simpa using heq.trans heq'.symm
        have hhead : q.1 = r.1 := (List.cons.inj hh).1
        have htail : zs = ts := (List.cons.inj hh).2
        apply hne
        apply Prod.ext hhead
        calc
          q.2 = zs.sum := hqsum.2.symm
          _ = ts.sum := by rw [htail]
          _ = r.2 := hrsum.2

theorem rz_sum_ofFn (k : ℕ) (e : Fin k → ℕ) :
    (List.ofFn e).sum = ∑ i, e i := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ]
      congr 1
      exact ih (fun i => e i.succ)

theorem rz_zero_alloc_finset_eq_image (k s : ℕ) :
    (modeAllocations (List.replicate k 0) s).toFinset =
      Finset.univ.image
        (fun e : {e : Fin k → ℕ // ∑ i, e i = s} => List.ofFn e.1) := by
  classical
  ext ys
  simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hys
    obtain ⟨hlen, hsum⟩ := (rz_zero_alloc_mem_iff k s ys).mp hys
    induction ys using List.ofFnRec with
    | _ n e =>
        simp only [List.length_ofFn] at hlen
        subst n
        refine ⟨⟨e, ?_⟩, rfl⟩
        simpa [rz_sum_ofFn] using hsum
  · rintro ⟨e, rfl⟩
    apply (rz_zero_alloc_mem_iff k s (List.ofFn e.1)).mpr
    simpa [rz_sum_ofFn] using e.2

theorem rz_zero_alloc_sum_eq_vector_sum {A : Type*} [AddCommMonoid A]
    (k s : ℕ) (f : List ℕ → A) :
    ((modeAllocations (List.replicate k 0) s).map f).sum =
      ∑ e : {e : Fin k → ℕ // ∑ i, e i = s}, f (List.ofFn e.1) := by
  classical
  rw [← List.sum_toFinset _ (rz_zero_alloc_nodup k s)]
  rw [rz_zero_alloc_finset_eq_image]
  rw [Finset.sum_image]
  intro e he e' he' h
  apply Subtype.ext
  exact List.ofFn_injective h

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_zero_alloc_mem_iff
#print axioms VOA.DeligneAudit.D4Levi.rz_zero_alloc_nodup
#print axioms VOA.DeligneAudit.D4Levi.rz_sum_ofFn
#print axioms VOA.DeligneAudit.D4Levi.rz_zero_alloc_finset_eq_image
#print axioms VOA.DeligneAudit.D4Levi.rz_zero_alloc_sum_eq_vector_sum
