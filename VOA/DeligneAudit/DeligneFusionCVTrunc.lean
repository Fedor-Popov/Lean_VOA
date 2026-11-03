import VOA.DeligneAudit.DeligneFusionCVBound

/-!
# Truncated Weyl modules are Chari–Venkatesh modules of balanced partitions

For an `sl₂[t]` highest-weight vector `y` with `F₀^{λ+1} y = 0` and `F_j y = 0` for `j ≥ r₀`, CV's relations
for the balanced partition `bal λ r₀` (`λ` split into `min(λ, r₀)` parts differing by at most one) hold
(`tw_cvrel`): every CV region lies in the Garland region `s + r ≥ λ + 1` or in the pigeonhole region
`s > (r₀ − 1) r` (`bal_region`).  Hence `dim F-span(y) ≤ ∏(ξⱼ+1)` (`tw_bound`).
-/

namespace VOA.DeligneAudit.CVsl2

open VOA.DeligneAudit.CVPart

universe u

/-- The balanced partition of `λ` into `min(λ, r₀)` parts. -/
def bal (lam r0 : ℕ) : List ℕ :=
  if lam < r0 then List.replicate lam 1
  else List.replicate (lam % r0) (lam / r0 + 1) ++ List.replicate (r0 - lam % r0) (lam / r0)

theorem bal_le (lam r0 : ℕ) : ∀ x ∈ bal lam r0, x ≤ lam / r0 + 1 := by
  intro x hx
  unfold bal at hx
  split_ifs at hx with h
  · rw [List.eq_of_mem_replicate hx]; exact Nat.le_add_left _ _
  · rcases List.mem_append.mp hx with hx | hx <;> rw [List.eq_of_mem_replicate hx]
    exact Nat.le_succ _

theorem bal_ge (lam r0 : ℕ) (hr : 1 ≤ r0) (h : r0 ≤ lam) :
    (bal lam r0).length = r0 ∧ ∀ x ∈ bal lam r0, lam / r0 ≤ x := by
  unfold bal
  rw [if_neg (by omega)]
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [List.length_append, List.length_replicate]
    have := Nat.mod_lt lam (show 0 < r0 by omega); omega
  · rcases List.mem_append.mp hx with hx | hx <;> rw [List.eq_of_mem_replicate hx]; omega

theorem bal_sum (lam r0 : ℕ) (hr : 1 ≤ r0) : (bal lam r0).sum = lam := by
  unfold bal
  split_ifs with h
  · simp
  · simp only [List.sum_append, List.sum_replicate, smul_eq_mul]
    have h1 := Nat.div_add_mod lam r0
    have h2 := Nat.mod_lt lam (show 0 < r0 by omega)
    nlinarith [Nat.sub_add_cancel h2.le]

theorem bal_sorted (lam r0 : ℕ) : (bal lam r0).Pairwise (· ≥ ·) := by
  unfold bal
  split_ifs
  · exact rep_sorted _ _
  · refine sorted_app (rep_sorted _ _) (rep_sorted _ _) fun x hx y hy => ?_
    rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]; omega

theorem bal_pos (lam r0 : ℕ) (hr : 1 ≤ r0) : ∀ x ∈ bal lam r0, 1 ≤ x := by
  intro x hx
  unfold bal at hx
  split_ifs at hx with h
  · rw [List.eq_of_mem_replicate hx]
  · have : 1 ≤ lam / r0 := (Nat.one_le_div_iff (by omega)).mpr (by omega)
    rcases List.mem_append.mp hx with hx | hx <;> rw [List.eq_of_mem_replicate hx] <;> omega

theorem take_sum_le (l : List ℕ) (M k : ℕ) (h : ∀ x ∈ l, x ≤ M) : (l.take k).sum ≤ k * M := by
  induction l generalizing k with
  | nil => simp
  | cons x l ih =>
      rcases k with _ | k
      · simp
      · simp only [List.take_succ_cons, List.sum_cons]
        have := ih k (fun y hy => h y (List.mem_cons_of_mem _ hy))
        have := h x List.mem_cons_self
        rw [Nat.succ_mul]; omega

theorem sum_ge_len (l : List ℕ) (m : ℕ) (h : ∀ x ∈ l, m ≤ x) : l.length * m ≤ l.sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.length_cons, List.sum_cons, Nat.succ_mul]
      have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      have := h x List.mem_cons_self
      omega

theorem drop_sum_ge (l : List ℕ) (m k : ℕ) (h : ∀ x ∈ l, m ≤ x) : (l.length - k) * m ≤ (l.drop k).sum := by
  have := sum_ge_len (l.drop k) m (fun x hx => h x (List.mem_of_mem_drop hx))
  rwa [List.length_drop] at this

/-- Every CV region of `bal λ r₀` lies in the Garland or the pigeonhole region. -/
theorem bal_region (lam r0 : ℕ) (hr0 : 1 ≤ r0) {r s k : ℕ} (hr : 1 ≤ r)
    (h : 1 + r * k + T k (bal lam r0) ≤ s + r) : lam + 1 ≤ s + r ∨ (r0 - 1) * r < s := by
  have hsplit : (bal lam r0).sum = ((bal lam r0).take k).sum + T k (bal lam r0) := by
    rw [T, ← List.sum_append, List.take_append_drop]
  rw [bal_sum lam r0 hr0] at hsplit
  rcases Nat.lt_or_ge r (lam / r0 + 1) with hq | hq
  · right
    have hlr : r0 ≤ lam := by
      by_contra hc
      have : lam / r0 = 0 := Nat.div_eq_of_lt (by omega)
      omega
    obtain ⟨hlen, hge⟩ := bal_ge lam r0 hr0 hlr
    have hd := drop_sum_ge (bal lam r0) (lam / r0) k hge
    rw [hlen] at hd
    have h1 : (r0 - k) * r ≤ (r0 - k) * (lam / r0) := Nat.mul_le_mul_left _ (by omega)
    change (r0 - k) * (lam / r0) ≤ T k (bal lam r0) at hd
    have hT : (r0 - k) * r ≤ T k (bal lam r0) := h1.trans hd
    rcases Nat.lt_or_ge k r0 with hk | hk
    · have e : r * k + (r0 - k) * r = (r0 - 1) * r + r := by
        obtain ⟨j, rfl⟩ : ∃ j, r0 = k + j + 1 := ⟨r0 - k - 1, by omega⟩
        rw [show k + j + 1 - k = j + 1 by omega, show k + j + 1 - 1 = k + j by omega]; ring
      linarith
    · have : (r0 - 1) * r + r ≤ r * k := by
        calc (r0 - 1) * r + r = r0 * r := by rw [← Nat.succ_mul]; congr 1; omega
          _ ≤ k * r := Nat.mul_le_mul_right r hk
          _ = r * k := mul_comm _ _
      omega
  · left
    have ht := take_sum_le (bal lam r0) (lam / r0 + 1) k (bal_le lam r0)
    have : k * (lam / r0 + 1) ≤ r * k := by rw [mul_comm r]; exact Nat.mul_le_mul_left _ hq
    omega

/-- **Truncated Weyl modules satisfy CV's relations for the balanced partition.** -/
theorem tw_cvrel {V : Type u} [AddCommGroup V] [Module ℂ V] {E H F : ℕ → Module.End ℂ V}
    (hS : SL2 E H F) {y : V} (hE : ∀ s, E s y = 0) (hH : ∀ p, 1 ≤ p → H p y = 0) {lam r0 : ℕ}
    (hr0 : 1 ≤ r0) (hF0 : (F 0 ^ (lam + 1)) y = 0) (htr : ∀ j, r0 ≤ j → F j y = 0) :
    CVRel F (bal lam r0) y := by
  intro r s k hr h
  rcases bal_region lam r0 hr0 hr h with hg | hp
  · have hEF' : ∀ k, E 1 * F k - F k * E 1 = H (k + 1) := fun k => by rw [hS.hEF 1 k, add_comm]
    exact Garland.garland hEF' (fun m k => hS.hHF (m + 1) k) hS.hFF (hE 1)
      (fun m => hH (m + 1) (by omega)) r hr hF0 s (by omega)
  · exact Q_high hS.hFF htr r s hp

/-- **The truncated Weyl bound**: `dim F-span(y) ≤ ∏ (bal λ r₀ + 1)`. -/
theorem tw_bound {V : Type u} [AddCommGroup V] [Module ℂ V] {E H F : ℕ → Module.End ℂ V}
    (hS : SL2 E H F) {y : V} (hE : ∀ s, E s y = 0) (hH : ∀ p, 1 ≤ p → H p y = 0)
    (hH0 : ∃ c : ℂ, H 0 y = c • y) {lam r0 : ℕ} (hr0 : 1 ≤ r0) (hF0 : (F 0 ^ (lam + 1)) y = 0)
    (htr : ∀ j, r0 ≤ j → F j y = 0) :
    FiniteDimensional ℂ (Fspan F y) ∧
      Module.finrank ℂ (Fspan F y) ≤ ((bal lam r0).map (· + 1)).prod :=
  cv_bound (bal lam r0) (bal_sorted lam r0) (bal_pos lam r0 hr0) V E H F hS y hE hH hH0
    (tw_cvrel hS hE hH hr0 hF0 htr)

end VOA.DeligneAudit.CVsl2

section AxiomAudit
#print axioms VOA.DeligneAudit.CVsl2.tw_bound
end AxiomAudit
