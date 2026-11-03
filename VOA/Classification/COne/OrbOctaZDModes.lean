import VOA.Classification.COne.OrbOctaZDGrading

/-! Higher circle relations and top-channel descent in the zero conformal fiber. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbOcta OrbC2b OrbC2c OrbOctaZC OrbOctaR

noncomputable local instance : Fintype octa :=
  @Fintype.ofFinite _ (Finite.of_equiv (Equiv.Perm (Fin 4)) octa_group.some.symm.toEquiv)

theorem q24_negative_modes {d : ℕ} (hd : 0 < d)
    {a b : (orbifold octa).carrier} (ha : a ∈ W.grading d)
    (hinit : ∀ k : ℤ, -1 ≤ k → k < d → q24L (mk W (W.smul a k b)) = 0) :
    ∀ m : ℕ, q24L (mk W (W.smul a (-((m : ℤ) + 1)) b)) = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => exact hinit (-1) le_rfl (by omega)
    | succ m =>
      have h := congrArg q24L ((mk_eq_zero_iff W).mpr (Hres_mem_O W ha b m 0))
      simp only [Hres, Gres, add_zero, map_sum, map_smul, map_zero] at h
      rw [Finset.sum_range_succ'] at h
      have hz : ∑ j ∈ Finset.range d,
          cbz (d : ℤ) ((j + 1 : ℕ) : ℤ) •
            q24L (mk W (W.smul a (((j + 1 : ℕ) : ℤ) - ((2 + m : ℕ) : ℤ)) b)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjd := Finset.mem_range.mp hj
        have hk : q24L (mk W (W.smul a
            (((j + 1 : ℕ) : ℤ) - ((2 + m : ℕ) : ℤ)) b)) = 0 := by
          by_cases hk : -1 ≤ (((j + 1 : ℕ) : ℤ) - ((2 + m : ℕ) : ℤ))
          · exact hinit _ hk (by omega)
          · have he : (((j + 1 : ℕ) : ℤ) - ((2 + m : ℕ) : ℤ)) =
                -(((m - j : ℕ) : ℤ) + 1) := by omega
            rw [he]
            exact ih (m - j) (by omega)
        rw [hk, smul_zero]
      rw [hz, zero_add] at h
      simpa only [Nat.cast_zero, cbz_zero, one_smul, zero_sub, Nat.cast_add,
        Nat.cast_ofNat, Nat.cast_one, add_assoc, add_comm, add_left_comm] using h

/-- Top products require only lower-weight vanishing and the corresponding mode identity. -/
theorem q24_top {F G : P3} {s t : ℕ}
    (hF : IsS4Inv F) (hG : IsS4Inv G)
    (hs : F.IsHomogeneous s) (ht : G.IsHomogeneous t)
    (hbelow : ∀ d : ℤ, 0 < d → d < ((s + t : ℕ) : ℤ) ^ 2 →
      ∀ y ∈ W.grading d, q24L (mk W y) = 0)
    (hm : q24L (mk W (W.smul (Tav F) (-((2 * s * t : ℕ) : ℤ) - 1) (Tav G))) = 0) :
    q24L (mk W (Tav (F * G))) = 0 := by
  obtain ⟨c, hc⟩ := T2_top F G s t hs ht
  have hav := average_lowerDesc octa hc
  rw [map_sub, map_smul, average_smul_T2 hF hG] at hav
  have ha : OrbC2.average octa (T2 (F * G)) = Tav (F * G) := rfl
  rw [ha] at hav
  have h := q24_lowerDesc hbelow hav
  simpa only [map_sub, map_smul, hm, smul_zero, sub_zero] using h

end VOA.Classification.COne.OrbOctaZD
