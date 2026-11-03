import VOA.Classification.COne.OrbIcoSDesc

/-! Existence of both icosahedral mode remainders in the intrinsic Virasoro error space.
The coefficients are not identified in this module. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoS
open VOA VertexOperatorAlgebra OrbSpan OrbC2b OrbC2c OrbIco

/-- The two explicit towers at weight 2r, together with discarded descendants. -/
def remainderSpace (r : ℕ) : Submodule ℂ (orbifold ico).carrier :=
  (Submodule.span ℂ {((Wi.L (-2)) ^ r) Wi.vacuum} ⊔
    Submodule.span ℂ {((Wi.L (-2)) ^ (r - 18)) Xico}) ⊔
      (virError Wi Wi.vacuum ⊔ virError Wi Xico)

theorem grading_mem_remainderSpace (r : ℕ) (hr : 18 ≤ r) (hmax : r < 50)
    {v : (orbifold ico).carrier} (hv : v ∈ Wi.grading (2 * r)) :
    v ∈ remainderSpace r := by
  have hs := grading_lt_100 (2 * r) (by omega) hv
  have hproject : ∀ z ∈ twoSeedSpan, piHom Wi (2 * r) z ∈ remainderSpace r := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨ks, rfl | rfl⟩ := hz
      · have h := OrbOctaR.project_word_mem Wi Wi.vacuum_mem r ks
        simp only [zero_add] at h
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h
        rw [← huv]
        exact Submodule.add_mem_sup (Submodule.mem_sup_left hu) (Submodule.mem_sup_left hv)
      · have h := OrbOctaR.project_word_mem Wi Xico_grading (r - 18) ks
        rw [show (36 : ℤ) + 2 * (r - 18 : ℕ) = 2 * r by omega] at h
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h
        rw [← huv]
        exact Submodule.add_mem_sup (Submodule.mem_sup_right hu) (Submodule.mem_sup_right hv)
    | zero => simp
    | add z t _ _ hz ht => rw [map_add]; exact Submodule.add_mem _ hz ht
    | smul c z _ hz => rw [map_smul]; exact Submodule.smul_mem _ c hz
  simpa only [piHom_of_mem Wi hv] using hproject v hs

/-- Existence is unconditional; numerical identification is a separate step. -/
theorem mode_remainder_exists (r : ℕ) (hr : 18 ≤ r) (hmax : r < 50) :
    ∃ a b : ℂ,
      Wi.smul Xico (71 - 2 * r) Xico -
        (a • ((Wi.L (-2)) ^ r) Wi.vacuum + b • ((Wi.L (-2)) ^ (r - 18)) Xico) ∈
          virError Wi Wi.vacuum ⊔ virError Wi Xico := by
  have hg : Wi.smul Xico (71 - 2 * r) Xico ∈ Wi.grading (2 * r) := by
    have h := Wi.smul_mem_grading Xico_grading Xico_grading (71 - 2 * r)
    rwa [show (36 : ℤ) + 36 - (71 - 2 * r) - 1 = 2 * r by ring] at h
  have hm := grading_mem_remainderSpace r hr hmax hg
  obtain ⟨s, hs, e, he, hse⟩ := Submodule.mem_sup.mp hm
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hs
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
  refine ⟨a, b, ?_⟩
  rw [← hse, ← huv, add_sub_cancel_left]
  exact he

theorem weight74_remainder_exists : ∃ a b : ℂ,
    OrbXu.modeSymbol Wi Xico (-3) 37 19 a b ∈
      virError Wi Wi.vacuum ⊔ virError Wi Xico := by
  simpa [OrbXu.modeSymbol, sub_sub] using mode_remainder_exists 37 (by decide) (by decide)

theorem weight76_remainder_exists : ∃ a b : ℂ,
    OrbXu.modeSymbol Wi Xico (-5) 38 20 a b ∈
      virError Wi Wi.vacuum ⊔ virError Wi Xico := by
  simpa [OrbXu.modeSymbol, sub_sub] using mode_remainder_exists 38 (by decide) (by decide)

end VOA.Classification.COne.OrbIcoS
