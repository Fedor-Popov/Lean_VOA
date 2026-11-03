import VOA.DeligneAudit.D4LeviKSBoxCountSum

/-! The 29^m count in the same ordered enumeration as the rank filtration. -/

namespace VOA.DeligneAudit.D4Levi

theorem keyEnum_injective (m : ℕ) : Function.Injective (keyEnum m) := by
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hless := keyEnum_descending m i j hlt
    exact False.elim ((keyLess_irrefl m (keyEnum m i)) (by simpa [hij] using hless))
  · exact heq
  · have hless := keyEnum_descending m j i hgt
    exact False.elim ((keyLess_irrefl m (keyEnum m i)) (by simpa [hij] using hless))

theorem ksBoxCount_enum_sum (m : ℕ) :
    (∑ i : Fin (globalKeyBox m).card,
      keyOrbitLength m (keyEnum m i) * ksBoxCount m (keyEnum m i)) ≤
        29 ^ m := by
  classical
  have himage : (Finset.univ.image (keyEnum m)) = globalKeyBox m := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact keyEnum_mem m i
    · intro hk
      obtain ⟨i, hi⟩ := keyEnum_cover m k hk
      exact ⟨i, hi⟩
  have heq :
      (∑ i : Fin (globalKeyBox m).card,
        keyOrbitLength m (keyEnum m i) * ksBoxCount m (keyEnum m i)) =
      ∑ k ∈ globalKeyBox m, keyOrbitLength m k * ksBoxCount m k := by
    calc
      (∑ i : Fin (globalKeyBox m).card,
        keyOrbitLength m (keyEnum m i) * ksBoxCount m (keyEnum m i)) =
          ∑ k ∈ Finset.univ.image (keyEnum m),
            keyOrbitLength m k * ksBoxCount m k :=
        (Finset.sum_image (s := Finset.univ) (g := keyEnum m)
          (f := fun k => keyOrbitLength m k * ksBoxCount m k)
          (keyEnum_injective m).injOn).symm
      _ = ∑ k ∈ globalKeyBox m, keyOrbitLength m k * ksBoxCount m k := by
        rw [himage]
  rw [heq]
  exact ksBoxCount_global_sum m

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.keyEnum_injective
#print axioms VOA.DeligneAudit.D4Levi.ksBoxCount_enum_sum
