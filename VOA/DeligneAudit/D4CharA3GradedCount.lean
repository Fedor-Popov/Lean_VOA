import VOA.DeligneAudit.D4CharA3ProjectedSteps

/-! The original sl4 key multiplicities sum degreewise to the GL4 branching character. -/

namespace VOA.DeligneAudit.D4Char

open A3Sector

noncomputable section

theorem a3GradedKey_sum_le (a b c N : ℕ) :
    (∑ k ∈ a3KeyBox a b c, a3GradedKeyContribution a b c N k) ≤
      gl4Hilb (a + b + c) (b + c) c 0 N := by
  classical
  let J := (a3KeyBox a b c).filter fun k =>
    k.degree ≤ N ∧ k.d₁ ≤ a ∧ k.d₂ ≤ b ∧ k.d₃ ≤ c
  let encode := fun k : A3RadicalKey => (((k.d₁, k.d₂), k.d₃), k.degree)
  let B := ((Finset.range (a + 1) ×ˢ Finset.range (b + 1)) ×ˢ
    Finset.range (c + 1)) ×ˢ Finset.range (N + 1)
  let value := fun t : ((ℕ × ℕ) × ℕ) × ℕ =>
    A2.gl3Hilb (b + c + t.1.1.1) (c + t.1.1.2) t.1.2 (N - t.2) *
      (a3ThreeBoxKeyTriples a b c t.1.1.1 t.1.1.2 t.1.2 t.2).card
  have he : (∑ k ∈ a3KeyBox a b c, a3GradedKeyContribution a b c N k) =
      ∑ k ∈ J, value (encode k) := by
    simp only [J, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hd : k.degree ≤ N
    · by_cases hs : k.d₁ ≤ a ∧ k.d₂ ≤ b ∧ k.d₃ ≤ c <;>
        simp [a3GradedKeyContribution, a3EffectiveMultiplicity, value, encode, hd, hs]
    · simp [a3GradedKeyContribution, hd]
  have hi : Set.InjOn encode (J : Set A3RadicalKey) := by
    intro k hk l hl heq
    obtain ⟨x, y, z, d⟩ := k
    obtain ⟨u, v, w, e⟩ := l
    simpa [encode, Prod.mk.injEq, A3RadicalKey.mk.injEq, and_assoc] using heq
  have hs : J.image encode ⊆ B := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨_, hd, hx, hy, hz⟩ := Finset.mem_filter.mp hk
    simpa only [B, encode, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]
      using And.intro (And.intro (And.intro hx hy) hz) hd
  rw [he, ← Finset.sum_image (f := value) hi]
  calc
    (∑ t ∈ J.image encode, value t) ≤ ∑ t ∈ B, value t :=
      Finset.sum_le_sum_of_subset hs
    _ = gl4Hilb (a + b + c) (b + c) c 0 N := by
      rw [gl4Hilb_eq_box_branch]
      simp only [B, Finset.sum_product, value, A2.conv]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro d hd
      exact Nat.mul_comm _ _

theorem a3GradedKey_enum_sum_le (a b c N : ℕ) :
    (∑ i : Fin (a3KeyBox a b c).card,
      a3GradedKeyContribution a b c N (a3KeyEnum a b c i)) ≤
        gl4Hilb (a + b + c) (b + c) c 0 N := by
  classical
  have he : Finset.univ.image (a3KeyEnum a b c) = a3KeyBox a b c := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ a3KeyEnum_mem a b c i,
      fun hk => a3KeyEnum_cover a b c k hk⟩
  rw [← Finset.sum_image (f := a3GradedKeyContribution a b c N)
    (a3KeyEnum_injective a b c).injOn, he]
  exact a3GradedKey_sum_le a b c N

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.a3GradedKey_sum_le
#print axioms VOA.DeligneAudit.D4Char.a3GradedKey_enum_sum_le
