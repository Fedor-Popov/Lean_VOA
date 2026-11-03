import VOA.DeligneAudit.DeligneFusionD1SiteGCyclic

/-!
# Actual current-degree pieces of the explicit one-site model

Degree zero is the coadjoint summand, degree one is the extra line, and
higher current-degree words vanish. These are direct statements about the
constructed current action, without any Demazure-character identification.
-/

namespace VOA.DeligneAudit.D1SiteG

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.SectorLoop
open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.SectorGraded

noncomputable section

local notation "deg" => VOA.DeligneAudit.SectorGraded.wordDeg

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ)
variable (hJ : JacobiCoord f) (hskew : ∀ a b c, f a b c = -f b a c)

theorem word_positive_fst (c₀ : Fin n) (l : List (Fin n × ℕ))
    (hd : 1 ≤ deg l) : (wordOp (rep f hJ hskew) l (w c₀)).1 = 0 := by
  induction l with
  | nil => simp [VOA.DeligneAudit.SectorGraded.wordDeg] at hd
  | cons a l ih =>
      rcases a with ⟨c, r⟩
      rcases r with _ | r
      · change coOp f c (wordOp (rep f hJ hskew) l (w c₀)).1 = 0
        rw [ih (by simpa [VOA.DeligneAudit.SectorGraded.wordDeg] using hd), map_zero]
      · rcases r with _ | r <;> rfl

theorem word_zero_snd (c₀ : Fin n) (l : List (Fin n × ℕ))
    (hd : deg l = 0) : (wordOp (rep f hJ hskew) l (w c₀)).2 = 0 := by
  cases l with
  | nil => rfl
  | cons a l =>
      rcases a with ⟨c, r⟩
      have hr : r = 0 := by
        change r + deg l = 0 at hd
        omega
      subst r
      rfl

theorem word_high_snd (c₀ : Fin n) (l : List (Fin n × ℕ))
    (hd : 2 ≤ deg l) : (wordOp (rep f hJ hskew) l (w c₀)).2 = 0 := by
  cases l with
  | nil => simp [VOA.DeligneAudit.SectorGraded.wordDeg] at hd
  | cons a l =>
      rcases a with ⟨c, r⟩
      rcases r with _ | r
      · rfl
      · rcases r with _ | r
        · change (wordOp (rep f hJ hskew) l (w c₀)).1 c = 0
          have hl : 1 ≤ deg l := by
            change 2 ≤ 1 + deg l at hd
            omega
          rw [word_positive_fst f hJ hskew c₀ l hl]
          rfl
        · rfl

theorem word_high_zero (c₀ : Fin n) (l : List (Fin n × ℕ))
    (hd : 2 ≤ deg l) : wordOp (rep f hJ hskew) l (w c₀) = 0 := by
  exact Prod.ext (word_positive_fst f hJ hskew c₀ l (by omega))
    (word_high_snd f hJ hskew c₀ l hd)

theorem cycDeg_high (c₀ : Fin n) (d : ℕ) (hd : 2 ≤ d) :
    cycDeg (rep f hJ hskew) (w c₀) d = ⊥ := by
  apply bot_unique
  rw [cycDeg, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  rw [word_high_zero f hJ hskew c₀ l (by omega)]
  exact Submodule.zero_mem _

theorem cycDeg_one (c₀ : Fin n) :
    cycDeg (rep f hJ hskew) (w c₀) 1 = Submodule.span ℂ {vac n} := by
  apply le_antisymm
  · rw [cycDeg, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    let u := wordOp (rep f hJ hskew) l (w c₀)
    have hu : u.1 = 0 := word_positive_fst f hJ hskew c₀ l (by omega)
    have he : u = u.2 • vac n := by
      apply Prod.ext
      · simpa [vac] using hu
      · simp [vac]
    change u ∈ _
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · rw [Submodule.span_le]
    rintro _ rfl
    apply Submodule.subset_span
    exact ⟨[(c₀, 1)], rfl, (oneOp_w c₀).symm⟩

theorem cycDeg_zero_le (c₀ : Fin n) :
    cycDeg (rep f hJ hskew) (w c₀) 0 ≤ LinearMap.range (inCo (n := n)) := by
  rw [cycDeg, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  refine ⟨(wordOp (rep f hJ hskew) l (w c₀)).1, ?_⟩
  apply Prod.ext
  · rfl
  · exact (word_zero_snd f hJ hskew c₀ l hl).symm

theorem cycDeg_zero (c₀ : Fin n) (depth : ℕ)
    (hcyc : ∀ c, (Pi.single c 1 : Co n) ∈ slotWords f c₀ depth) :
    cycDeg (rep f hJ hskew) (w c₀) 0 = LinearMap.range (inCo (n := n)) := by
  apply le_antisymm (cycDeg_zero_le f hJ hskew c₀)
  have hc : (coCyclic f c₀).map inCo ≤ cycDeg (rep f hJ hskew) (w c₀) 0 := by
    rw [coCyclic, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨v, ⟨l, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨l.map (fun c => (c, 0)), ?_, ?_⟩
    · simp [VOA.DeligneAudit.SectorGraded.wordDeg, List.map_map, Function.comp_def]
    · exact (word_zero f hJ hskew l (Pi.single c₀ 1)).symm
  rw [coCyclic_top f c₀ depth hcyc, Submodule.map_top] at hc
  exact hc

theorem finrank_cycDeg_one (c₀ : Fin n) :
    Module.finrank ℂ (cycDeg (rep f hJ hskew) (w c₀) 1) = 1 := by
  rw [cycDeg_one f hJ hskew c₀]
  apply finrank_span_singleton
  intro hz
  have h := congrArg Prod.snd hz
  simp [vac] at h

theorem finrank_cycDeg_zero (c₀ : Fin n) (depth : ℕ)
    (hcyc : ∀ c, (Pi.single c 1 : Co n) ∈ slotWords f c₀ depth) :
    Module.finrank ℂ (cycDeg (rep f hJ hskew) (w c₀) 0) = n := by
  rw [cycDeg_zero f hJ hskew c₀ depth hcyc]
  calc
    Module.finrank ℂ (LinearMap.range (inCo (n := n))) =
        Module.finrank ℂ (Co n) :=
      LinearMap.finrank_range_of_inj (by
        intro a b hab
        exact congrArg Prod.fst hab)
    _ = n := by simp [Co, Module.finrank_fintype_fun_eq_card]

theorem finrank_cycDeg_high (c₀ : Fin n) (d : ℕ) (hd : 2 ≤ d) :
    Module.finrank ℂ (cycDeg (rep f hJ hskew) (w c₀) d) = 0 := by
  rw [cycDeg_high f hJ hskew c₀ d hd]
  exact finrank_bot _ _

end

end VOA.DeligneAudit.D1SiteG

#print axioms VOA.DeligneAudit.D1SiteG.cycDeg_high
#print axioms VOA.DeligneAudit.D1SiteG.cycDeg_one
#print axioms VOA.DeligneAudit.D1SiteG.cycDeg_zero
#print axioms VOA.DeligneAudit.D1SiteG.finrank_cycDeg_zero
#print axioms VOA.DeligneAudit.D1SiteG.finrank_cycDeg_one
