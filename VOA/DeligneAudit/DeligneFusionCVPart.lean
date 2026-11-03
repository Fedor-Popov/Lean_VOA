import Mathlib

/-!
# Partition combinatorics for the Chari–Venkatesh recursion

A partition is a weakly decreasing list of positive integers.  With `ℓ ≥ 2` parts it has the shape
`P μ c a b = μ ++ a^{c+1} ++ [b]` (`μ` the parts `> a`, `b ≤ a`; `shape_exists`).  CV's partitions:

* `Pp = μ ++ [a+1] ++ a^c ++ [b−1]` (`ξ⁺`: one unit moves from the last part to the first `a`);
* `Pm = μ ++ a^c ++ [a−b]` (`ξ⁻`).

Tail sums `T k ξ = Σ_{j>k} ξ_j`:
* `T_plus`: `T k ξ⁺ = T k ξ`, or `g < k ≤ ℓ−1` with `T k ξ⁺ + 1 = T k ξ = (ℓ−1−k)a + b`;
* `T_minus`: `T k ξ⁻ + 2b = T k ξ` for `k ≤ ℓ − 2`, and `T k ξ⁻ = 0` for `k ≥ ℓ − 1`;
* `arith_plus`: the case split of CV Prop. 6.4;
* `prod_split`: `∏(ξ+1) = ∏(ξ⁺+1) + ∏(ξ⁻+1)`.
-/

namespace VOA.DeligneAudit.CVPart

/-- `T k ξ = Σ_{j > k} ξ_j`. -/
def T (k : ℕ) (ξ : List ℕ) : ℕ := (ξ.drop k).sum

theorem T_append (k : ℕ) (l₁ l₂ : List ℕ) : T k (l₁ ++ l₂) = T k l₁ + T (k - l₁.length) l₂ := by
  simp [T, List.drop_append]

theorem T_replicate (j n a : ℕ) : T j (List.replicate n a) = (n - j) * a := by
  simp [T, List.drop_replicate]

theorem T_single (j b : ℕ) : T j [b] = if j = 0 then b else 0 := by
  rcases j with _ | j <;> simp [T]

theorem T_nil (j : ℕ) : T j [] = 0 := by simp [T]

theorem T_of_le (k : ℕ) (l : List ℕ) (h : l.length ≤ k) : T k l = 0 := by
  simp [T, List.drop_eq_nil_of_le h]

/-- The shape `μ ++ a^{c+1} ++ [b]`. -/
def P (μ : List ℕ) (c a b : ℕ) : List ℕ := μ ++ (List.replicate (c + 1) a ++ [b])

/-- `ξ⁺`. -/
def Pp (μ : List ℕ) (c a b : ℕ) : List ℕ :=
  μ ++ ([a + 1] ++ (List.replicate c a ++ (if b = 1 then [] else [b - 1])))

/-- `ξ⁻`. -/
def Pm (μ : List ℕ) (c a b : ℕ) : List ℕ := μ ++ (List.replicate c a ++ (if a = b then [] else [a - b]))

theorem T_tail1 (j b : ℕ) (hb : 1 ≤ b) : T j (if b = 1 then [] else [b - 1]) = if j = 0 then b - 1 else 0 := by
  split_ifs with h1 h2 <;> simp_all [T_nil, T_single]

theorem T_tail2 (j a b : ℕ) (hab : b ≤ a) :
    T j (if a = b then [] else [a - b]) = if j = 0 then a - b else 0 := by
  split_ifs with h1 h2 <;> simp_all [T_nil, T_single]

theorem length_P (μ : List ℕ) (c a b : ℕ) : (P μ c a b).length = μ.length + c + 2 := by
  simp [P]; ring

theorem T_rep_tail (m n a : ℕ) (tail : List ℕ) :
    T m (List.replicate n a ++ tail) = (n - m) * a + T (m - n) tail := by
  rw [T_append, T_replicate, List.length_replicate]

variable (μ : List ℕ) (c a b : ℕ)

theorem T_P_low (k : ℕ) (hk : k ≤ μ.length) : T k (P μ c a b) = T k μ + ((c + 1) * a + b) := by
  rw [P, T_append, T_rep_tail, show k - μ.length = 0 by omega, Nat.sub_zero, Nat.zero_sub, T_single]
  simp

theorem T_P_mid (m : ℕ) (hm : m ≤ c + 1) : T (μ.length + m) (P μ c a b) = (c + 1 - m) * a + b := by
  rw [P, T_append, T_rep_tail, T_of_le _ μ (by omega), show μ.length + m - μ.length = m by omega,
    show m - (c + 1) = 0 by omega, T_single]
  simp

theorem T_P_high (k : ℕ) (hk : μ.length + c + 2 ≤ k) : T k (P μ c a b) = 0 :=
  T_of_le _ _ (by rw [length_P]; exact hk)

variable {b} (hb : 1 ≤ b)
include hb

omit hb in
theorem length_Pp_le : (Pp μ c a b).length ≤ μ.length + c + 2 := by
  simp only [Pp, List.length_append, List.length_singleton, List.length_replicate]
  split_ifs <;> simp <;> omega

theorem T_Pp_low (k : ℕ) (hk : k ≤ μ.length) : T k (Pp μ c a b) = T k μ + ((c + 1) * a + b) := by
  rw [Pp, T_append, show k - μ.length = 0 by omega, T_append, T_single, if_pos rfl,
    List.length_singleton, Nat.zero_sub, T_rep_tail, T_tail1 _ _ hb]
  simp only [Nat.sub_zero, Nat.zero_sub, if_true]
  ring_nf; omega

theorem T_Pp_mid (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ c + 1) :
    T (μ.length + m) (Pp μ c a b) = (c + 1 - m) * a + (b - 1) := by
  rw [Pp, T_append, T_of_le _ μ (by omega), show μ.length + m - μ.length = m by omega, T_append,
    T_single, if_neg (by omega), List.length_singleton, T_rep_tail, T_tail1 _ _ hb,
    show m - 1 - c = 0 by omega, show c - (m - 1) = c + 1 - m by omega]
  simp

theorem T_Pp_high (k : ℕ) (hk : μ.length + c + 2 ≤ k) : T k (Pp μ c a b) = 0 :=
  T_of_le _ _ ((length_Pp_le μ c a).trans hk)

omit hb

variable (hab : b ≤ a)
include hab

theorem T_Pm_low (k : ℕ) (hk : k ≤ μ.length) : T k (Pm μ c a b) = T k μ + (c * a + (a - b)) := by
  rw [Pm, T_append, show k - μ.length = 0 by omega, T_rep_tail, T_tail2 _ _ _ hab]
  simp

theorem T_Pm_mid (m : ℕ) (hm : m ≤ c) : T (μ.length + m) (Pm μ c a b) = (c - m) * a + (a - b) := by
  rw [Pm, T_append, T_of_le _ μ (by omega), show μ.length + m - μ.length = m by omega, T_rep_tail,
    T_tail2 _ _ _ hab, show m - c = 0 by omega]
  simp

omit hab in
theorem T_Pm_high (k : ℕ) (hk : μ.length + c + 1 ≤ k) : T k (Pm μ c a b) = 0 := by
  apply T_of_le
  simp only [Pm, List.length_append, List.length_replicate]
  split_ifs <;> simp <;> omega

omit hab

/-- Tail sums of `ξ⁺`. -/
theorem T_plus (hb : 1 ≤ b) (k : ℕ) :
    T k (Pp μ c a b) = T k (P μ c a b) ∨
      (μ.length < k ∧ k ≤ μ.length + c + 1 ∧ T k (Pp μ c a b) + 1 = T k (P μ c a b) ∧
        T k (P μ c a b) = (μ.length + c + 1 - k) * a + b ∧
        T (k - 1) (P μ c a b) = T k (P μ c a b) + a) := by
  rcases Nat.lt_or_ge μ.length k with hk | hk
  · rcases Nat.lt_or_ge (μ.length + c + 1) k with hk2 | hk2
    · left; rw [T_Pp_high μ c a hb k (by omega), T_P_high μ c a b k (by omega)]
    · right
      obtain ⟨m, rfl⟩ : ∃ m, k = μ.length + m := ⟨k - μ.length, by omega⟩
      refine ⟨hk, hk2, ?_, ?_, ?_⟩
      · rw [T_Pp_mid μ c a hb m (by omega) (by omega), T_P_mid μ c a b m (by omega)]; omega
      · rw [T_P_mid μ c a b m (by omega), show μ.length + c + 1 - (μ.length + m) = c + 1 - m by omega]
      · rw [show μ.length + m - 1 = μ.length + (m - 1) by omega, T_P_mid μ c a b (m - 1) (by omega),
          T_P_mid μ c a b m (by omega), show c + 1 - (m - 1) = (c + 1 - m) + 1 by omega]
        ring
  · left; rw [T_Pp_low μ c a hb k hk, T_P_low μ c a b k hk]

/-- Tail sums of `ξ⁻`. -/
theorem T_minus (hab : b ≤ a) (k : ℕ) :
    (k ≤ μ.length + c → T k (Pm μ c a b) + 2 * b = T k (P μ c a b)) ∧
      (μ.length + c + 1 ≤ k → T k (Pm μ c a b) = 0) := by
  refine ⟨fun hk => ?_, fun hk => T_Pm_high μ c a k hk⟩
  rcases Nat.lt_or_ge μ.length k with hgk | hgk
  · obtain ⟨m, rfl⟩ : ∃ m, k = μ.length + m := ⟨k - μ.length, by omega⟩
    rw [T_Pm_mid μ c a hab m (by omega), T_P_mid μ c a b m (by omega),
      show c + 1 - m = (c - m) + 1 by omega]
    ring_nf; omega
  · rw [T_Pm_low μ c a hab k hgk, T_P_low μ c a b k hgk]
    ring_nf; omega

/-- The case split of CV Prop. 6.4. -/
theorem arith_plus (μ : List ℕ) (c a b : ℕ) (hb : 1 ≤ b) (hab : b ≤ a) {r s k : ℕ} (hr : 1 ≤ r)
    (h : 1 + r * k + T k (Pp μ c a b) ≤ s + r) :
    (∃ k', 1 + r * k' + T k' (P μ c a b) ≤ s + r) ∨ (μ.length + c) * r + b ≤ s := by
  rcases T_plus μ c a hb k with he | ⟨hk1, hk2, h1, h2, h3⟩
  · exact Or.inl ⟨k, by rw [← he]; exact h⟩
  · by_cases h' : 1 + r * k + T k (P μ c a b) ≤ s + r
    · exact Or.inl ⟨k, h'⟩
    · have hs : s + r = r * k + T k (P μ c a b) := by omega
      rcases Nat.lt_or_ge a r with har | har
      · left
        refine ⟨k - 1, ?_⟩
        rw [h3]
        have : r * k = r * (k - 1) + r := by
          rw [← Nat.mul_succ]; congr 1; omega
        omega
      · right
        obtain ⟨n, hn⟩ : ∃ n, μ.length + c + 1 - k = n := ⟨_, rfl⟩
        rw [h2, hn] at hs
        have hk : k = μ.length + c + 1 - n := by omega
        have : n * r ≤ n * a := Nat.mul_le_mul_left n har
        have hkn : k + n = μ.length + c + 1 := by omega
        have e : r * k + n * r = (μ.length + c) * r + r := by
          calc r * k + n * r = r * (k + n) := by ring
            _ = (μ.length + c) * r + r := by rw [hkn]; ring
        nlinarith

/-- `∏(ξ+1) = ∏(ξ⁺+1) + ∏(ξ⁻+1)`. -/
theorem prod_split (μ : List ℕ) (c a b : ℕ) (hb : 1 ≤ b) (hab : b ≤ a) :
    ((P μ c a b).map (· + 1)).prod = ((Pp μ c a b).map (· + 1)).prod + ((Pm μ c a b).map (· + 1)).prod := by
  have e1 : ((if b = 1 then [] else [b - 1] : List ℕ).map (· + 1)).prod = b := by
    split_ifs with h <;> simp [h]; omega
  have e2 : ((if a = b then [] else [a - b] : List ℕ).map (· + 1)).prod = a - b + 1 := by
    split_ifs with h <;> simp [h]
  simp only [P, Pp, Pm, List.map_append, List.prod_append, List.map_replicate, List.prod_replicate,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, e1, e2, pow_succ]
  obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
  rw [show b + d - b = d by omega]
  ring

theorem sum_Pp (μ : List ℕ) (c a b : ℕ) (hb : 1 ≤ b) : (Pp μ c a b).sum = (P μ c a b).sum := by
  have : (if b = 1 then [] else [b - 1] : List ℕ).sum = b - 1 := by split_ifs with h <;> simp [h]
  simp only [P, Pp, List.sum_append, List.sum_replicate, List.sum_cons, List.sum_nil, this, smul_eq_mul]
  ring_nf; omega

theorem sum_Pm (μ : List ℕ) (c a b : ℕ) (hab : b ≤ a) :
    (Pm μ c a b).sum + 2 * b = (P μ c a b).sum := by
  have : (if a = b then [] else [a - b] : List ℕ).sum = a - b := by split_ifs with h <;> simp [h]
  simp only [P, Pm, List.sum_append, List.sum_replicate, List.sum_cons, List.sum_nil, this, smul_eq_mul]
  ring_nf; omega

/-! ## Shapes, sortedness and the induction measure -/

/-- Every weakly decreasing list with at least two entries has the shape `P μ c a b`. -/
theorem shape_exists : ∀ (ξ : List ℕ), ξ.Pairwise (· ≥ ·) → 2 ≤ ξ.length →
    ∃ μ c a b, ξ = P μ c a b ∧ (∀ x ∈ μ, a < x) ∧ b ≤ a
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | [x, y], hs, _ => ⟨[], 0, x, y, rfl, by simp, by simpa using hs⟩
  | (x :: y :: z :: t), hs, _ => by
      obtain ⟨μ, c, a, b, he, hμ, hab⟩ := shape_exists (y :: z :: t) hs.of_cons (by simp)
      have hxa : a ≤ x := by
        have : a ∈ y :: z :: t := by rw [he]; simp [P]
        exact List.rel_of_pairwise_cons hs this
      rcases Nat.lt_or_ge a x with h | h
      · exact ⟨x :: μ, c, a, b, by rw [he]; rfl, fun w hw => by
          rcases List.mem_cons.mp hw with rfl | hw
          · exact h
          · exact hμ w hw, hab⟩
      · have hx : x = a := le_antisymm h hxa
        subst hx
        have hμ0 : μ = [] := by
          rcases μ with _ | ⟨m, μ'⟩
          · rfl
          · exfalso
            have hm : m ∈ y :: z :: t := by rw [he]; simp [P]
            have := List.rel_of_pairwise_cons hs hm
            have := hμ m (by simp)
            omega
        subst hμ0
        refine ⟨[], c + 1, x, b, ?_, by simp, hab⟩
        rw [he]; simp [P, List.replicate_succ]

variable (μ : List ℕ) (c a b : ℕ)

theorem P_sorted_parts (hs : (P μ c a b).Pairwise (· ≥ ·)) : μ.Pairwise (· ≥ ·) := by
  simp only [P] at hs; exact (List.pairwise_append.mp hs).1

theorem P_pos (hp : ∀ x ∈ P μ c a b, 1 ≤ x) : (∀ x ∈ μ, 1 ≤ x) ∧ 1 ≤ a ∧ 1 ≤ b := by
  refine ⟨fun x hx => hp x (by simp [P, hx]), hp a (by simp [P]), hp b (by simp [P])⟩

theorem sorted_app {l1 l2 : List ℕ} (h1 : l1.Pairwise (· ≥ ·)) (h2 : l2.Pairwise (· ≥ ·))
    (h : ∀ x ∈ l1, ∀ y ∈ l2, y ≤ x) : (l1 ++ l2).Pairwise (· ≥ ·) :=
  List.pairwise_append.mpr ⟨h1, h2, fun x hx y hy => h x hx y hy⟩

theorem rep_sorted (n a : ℕ) : (List.replicate n a).Pairwise (· ≥ ·) :=
  List.pairwise_replicate.mpr (Or.inr le_rfl)

theorem ite_sorted (p : Prop) [Decidable p] (z : ℕ) : (if p then [] else [z]).Pairwise (· ≥ ·) := by
  split_ifs <;> simp

theorem mem_ite {p : Prop} [Decidable p] {z y : ℕ} (hy : y ∈ (if p then [] else [z])) : y = z := by
  split_ifs at hy <;> simp_all

theorem Pp_sorted (hs : μ.Pairwise (· ≥ ·)) (hμ : ∀ x ∈ μ, a < x) (hab : b ≤ a) :
    (Pp μ c a b).Pairwise (· ≥ ·) := by
  have hr : (List.replicate c a ++ (if b = 1 then [] else [b - 1])).Pairwise (· ≥ ·) :=
    sorted_app (rep_sorted c a) (ite_sorted _ _) fun x hx y hy => by
      rw [List.eq_of_mem_replicate hx, mem_ite hy]; omega
  have hle : ∀ y ∈ List.replicate c a ++ (if b = 1 then [] else [b - 1]), y ≤ a := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · rw [List.eq_of_mem_replicate hy]
    · rw [mem_ite hy]; omega
  refine sorted_app hs (sorted_app (by simp) hr fun x hx y hy => ?_) fun x hx y hy => ?_
  · rw [List.mem_singleton.mp hx]; have := hle y hy; omega
  · have := hμ x hx
    rcases List.mem_append.mp hy with hy | hy
    · rw [List.mem_singleton.mp hy]; omega
    · have := hle y hy; omega

theorem Pm_sorted (hs : μ.Pairwise (· ≥ ·)) (hμ : ∀ x ∈ μ, a < x) :
    (Pm μ c a b).Pairwise (· ≥ ·) := by
  have hle : ∀ y ∈ List.replicate c a ++ (if a = b then [] else [a - b]), y ≤ a := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · rw [List.eq_of_mem_replicate hy]
    · rw [mem_ite hy]; omega
  refine sorted_app hs (sorted_app (rep_sorted c a) (ite_sorted _ _) fun x hx y hy => ?_)
    fun x hx y hy => ?_
  · rw [List.eq_of_mem_replicate hx, mem_ite hy]; omega
  · have := hμ x hx; have := hle y hy; omega

theorem Pp_pos (hμp : ∀ x ∈ μ, 1 ≤ x) (ha : 1 ≤ a) (hb : 1 ≤ b) : ∀ x ∈ Pp μ c a b, 1 ≤ x := by
  intro x hx
  simp only [Pp, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl | hx | hx
  · exact hμp x hx
  · omega
  · rw [List.eq_of_mem_replicate hx]; exact ha
  · by_cases h : b = 1
    · simp [h] at hx
    · rw [if_neg h, List.mem_singleton] at hx; omega

theorem Pm_pos (hμp : ∀ x ∈ μ, 1 ≤ x) (ha : 1 ≤ a) (hab : b ≤ a) : ∀ x ∈ Pm μ c a b, 1 ≤ x := by
  intro x hx
  simp only [Pm, List.mem_append] at hx
  rcases hx with hx | hx | hx
  · exact hμp x hx
  · rw [List.eq_of_mem_replicate hx]; exact ha
  · by_cases h : a = b
    · simp [h] at hx
    · rw [if_neg h, List.mem_singleton] at hx; omega

/-- The induction measure for `ξ⁺`: same sum; shorter, or same length with smaller last part. -/
theorem Pp_measure (hb : 1 ≤ b) :
    (Pp μ c a b).length < (P μ c a b).length ∨
      ((Pp μ c a b).length = (P μ c a b).length ∧
        T ((Pp μ c a b).length - 1) (Pp μ c a b) < T ((P μ c a b).length - 1) (P μ c a b)) := by
  rw [length_P]
  by_cases h1 : b = 1
  · left; simp [Pp, h1]; omega
  · right
    have hl : (Pp μ c a b).length = μ.length + c + 2 := by simp [Pp, h1]; ring
    refine ⟨hl, ?_⟩
    rw [hl, show μ.length + c + 2 - 1 = μ.length + (c + 1) by omega,
      T_Pp_mid μ c a hb (c + 1) (by omega) le_rfl, T_P_mid μ c a b (c + 1) le_rfl]
    simp; omega

theorem length_Pm_lt (hab : b ≤ a) : (Pm μ c a b).length < (P μ c a b).length := by
  rw [length_P]; simp only [Pm, List.length_append, List.length_replicate]
  split_ifs <;> simp <;> omega

end VOA.DeligneAudit.CVPart
