import VOA.Classification.COne.OrbOctaRSpan

/-! State-level existence of the two coefficients at weights 32 and 34.
The values of these coefficients are not asserted in this file. -/

set_option Elab.async false

noncomputable section
namespace VOA.Classification.COne.OrbOctaR
open VOA VertexOperatorAlgebra OrbSpan OrbOcta OrbC2b OrbC2c

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (A : VertexOperatorAlgebra V)

def wordWeight (ks : List ℕ) : ℕ := (ks.map (fun k => k + 1)).sum

theorem virWord_grading {d : ℤ} {v : V} (hv : v ∈ A.grading d) (ks : List ℕ) :
    virWord A ks v ∈ A.grading (d + wordWeight ks) := by
  induction ks with
  | nil => simpa [virWord, wordWeight] using hv
  | cons k ks ih =>
    have h := L_mem_grading_conv A ih (-(k : ℤ) - 1)
    have he : d + (wordWeight (k :: ks) : ℤ) =
        (d + wordWeight ks) - (-(k : ℤ) - 1) := by
      simp only [wordWeight, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
      omega
    rw [he]
    exact h

/-- Projecting a word to the right weight leaves one pure L(-2) tower or an error. -/
theorem project_word_mem {d : ℤ} {v : V} (hv : v ∈ A.grading d)
    (r : ℕ) (ks : List ℕ) :
    piHom A (d + 2 * r) (virWord A ks v) ∈
      Submodule.span ℂ {((A.L (-2)) ^ r) v} ⊔ virError A v := by
  have hg := virWord_grading A hv ks
  by_cases he : d + (wordWeight ks : ℤ) = d + 2 * r
  · rw [piHom_of_mem A (he ▸ hg)]
    by_cases hb : ∃ k ∈ ks, k ≠ 1
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨⟨ks, hb⟩, rfl⟩)
    · have hall : ∀ k ∈ ks, k = 1 := by simpa using hb
      have hks := List.eq_replicate_length.mpr hall
      have hw : wordWeight ks = 2 * ks.length := by
        conv_lhs => rw [hks]
        simp [wordWeight, List.map_replicate, List.sum_replicate, Nat.mul_comm]
      have hlen : ks.length = r := by rw [hw] at he; omega
      rw [hks, hlen, ← L_neg_two_pow_eq_virWord]
      exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
  · rw [piHom_of_mem_ne A he hg]
    exact Submodule.zero_mem _

end General

/-- The two explicit towers at weight 2r, together with discarded descendants. -/
def remainderSpace (r : ℕ) : Submodule ℂ (orbifold octa).carrier :=
  (Submodule.span ℂ {((W.L (-2)) ^ r) W.vacuum} ⊔
    Submodule.span ℂ {((W.L (-2)) ^ (r - 8)) X}) ⊔
      (virError W W.vacuum ⊔ virError W X)

theorem grading_mem_remainderSpace (r : ℕ) (hr : 8 ≤ r) (hmax : r < 18)
    {v : (orbifold octa).carrier} (hv : v ∈ W.grading (2 * r)) :
    v ∈ remainderSpace r := by
  have hs := grading_lt_36 (2 * r) (by omega) hv
  have hproject : ∀ z ∈ twoSeedSpan, piHom W (2 * r) z ∈ remainderSpace r := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨ks, rfl | rfl⟩ := hz
      · have h := project_word_mem W W.vacuum_mem r ks
        simp only [zero_add] at h
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h
        rw [← huv]
        exact Submodule.add_mem_sup (Submodule.mem_sup_left hu) (Submodule.mem_sup_left hv)
      · have h := project_word_mem W X_grading (r - 8) ks
        rw [show (16 : ℤ) + 2 * (r - 8 : ℕ) = 2 * r by omega] at h
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h
        rw [← huv]
        exact Submodule.add_mem_sup (Submodule.mem_sup_right hu) (Submodule.mem_sup_right hv)
    | zero => simp
    | add z t _ _ hz ht => rw [map_add]; exact Submodule.add_mem _ hz ht
    | smul c z _ hz => rw [map_smul]; exact Submodule.smul_mem _ c hz
  simpa only [piHom_of_mem W hv] using hproject v hs

/-- Existence is unconditional; numerical identification is a separate step. -/
theorem mode_remainder_exists (r : ℕ) (hr : 8 ≤ r) (hmax : r < 18) :
    ∃ a b : ℂ,
      W.smul X (31 - 2 * r) X -
        (a • ((W.L (-2)) ^ r) W.vacuum + b • ((W.L (-2)) ^ (r - 8)) X) ∈
          virError W W.vacuum ⊔ virError W X := by
  have hg : W.smul X (31 - 2 * r) X ∈ W.grading (2 * r) := by
    have h := W.smul_mem_grading X_grading X_grading (31 - 2 * r)
    rwa [show (16 : ℤ) + 16 - (31 - 2 * r) - 1 = 2 * r by ring] at h
  have hm := grading_mem_remainderSpace r hr hmax hg
  obtain ⟨s, hs, e, he, hse⟩ := Submodule.mem_sup.mp hm
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hs
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
  refine ⟨a, b, ?_⟩
  rw [← hse, ← huv, add_sub_cancel_left]
  exact he

theorem weight32_remainder_exists : ∃ a b : ℂ,
    W.smul X (-1) X -
      (a • ((W.L (-2)) ^ 16) W.vacuum + b • ((W.L (-2)) ^ 8) X) ∈
        virError W W.vacuum ⊔ virError W X := by
  simpa using mode_remainder_exists 16 (by decide) (by decide)

theorem weight34_remainder_exists : ∃ a b : ℂ,
    W.smul X (-3) X -
      (a • ((W.L (-2)) ^ 17) W.vacuum + b • ((W.L (-2)) ^ 9) X) ∈
        virError W W.vacuum ⊔ virError W X := by
  simpa using mode_remainder_exists 17 (by decide) (by decide)

end VOA.Classification.COne.OrbOctaR
