import VOA.DeligneAudit.D4CharA2ProjectedSteps

/-! Summing the exact A2 key degrees gives the GL3 branching character. -/

namespace VOA.DeligneAudit.D4Char

open A3Sector

noncomputable section

theorem a2GradedKey_sum_le (p q N : ℕ) :
    (∑ k ∈ a2KeyBox p q, a2GradedKeyContribution p q N k) ≤
      A2.gl3Hilb (p + q) q 0 N := by
  classical
  let J := (a2KeyBox p q).filter fun k => k.degree ≤ N ∧ k.d₂ ≤ q
  let encode := fun k : A2RadicalKey => ((k.d₁, k.d₂), k.degree)
  let B := (Finset.range (p + 1) ×ˢ Finset.range (q + 1)) ×ˢ Finset.range (N + 1)
  let value := fun t : (ℕ × ℕ) × ℕ =>
    A2.gl2Hilb (q + t.1.1) t.1.2 (N - t.2) *
      (a2TwoBoxKeyPairs p q t.1.1 t.1.2 t.2).card
  have he : (∑ k ∈ a2KeyBox p q, a2GradedKeyContribution p q N k) =
      ∑ k ∈ J, value (encode k) := by
    simp only [J, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hd : k.degree ≤ N <;> by_cases hb : k.d₂ ≤ q <;>
      simp [a2GradedKeyContribution, a2EffectiveMultiplicity, value, encode, hd, hb]
  have hi : Set.InjOn encode (J : Set A2RadicalKey) := by
    intro k hk l hl heq
    obtain ⟨a, b, d⟩ := k
    obtain ⟨x, y, e⟩ := l
    simpa [encode, Prod.mk.injEq, A2RadicalKey.mk.injEq, and_assoc] using heq
  have hs : J.image encode ⊆ B := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hbox, hd, hb⟩ := Finset.mem_filter.mp hk
    obtain ⟨i, rfl⟩ := a2KeyEnum_cover p q k hbox
    have ha := a2KeyEnum_first_le p q i
    simpa only [B, encode, Finset.mem_product, Finset.mem_range,
      Nat.lt_succ_iff] using And.intro (And.intro ha hb) hd
  rw [he, ← Finset.sum_image (f := value) hi]
  calc
    (∑ t ∈ J.image encode, value t) ≤ ∑ t ∈ B, value t :=
      Finset.sum_le_sum_of_subset hs
    _ = A2.gl3Hilb (p + q) q 0 N := by
      rw [gl3Hilb_eq_box_branch]
      simp only [B, Finset.sum_product, value, A2.conv]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      exact Nat.mul_comm _ _

theorem a2GradedKey_enum_sum_le (p q N : ℕ) :
    (∑ i : Fin (a2KeyBox p q).card,
      a2GradedKeyContribution p q N (a2KeyEnum p q i)) ≤
        A2.gl3Hilb (p + q) q 0 N := by
  classical
  have he : Finset.univ.image (a2KeyEnum p q) = a2KeyBox p q := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ a2KeyEnum_mem p q i,
      fun hk => a2KeyEnum_cover p q k hk⟩
  rw [← Finset.sum_image (f := a2GradedKeyContribution p q N)
    (a2KeyEnum_injective p q).injOn, he]
  exact a2GradedKey_sum_le p q N

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.a2GradedKey_sum_le
#print axioms VOA.DeligneAudit.D4Char.a2GradedKey_enum_sum_le
