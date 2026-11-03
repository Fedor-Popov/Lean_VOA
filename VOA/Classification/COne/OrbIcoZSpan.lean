import VOA.Classification.COne.OrbIcoMain
import VOA.Classification.COne.OrbZhuTower

/-! The actual icosahedral Zhu algebra is spanned by its two conformal towers.
This uses homogeneous Zhu descent and needs no finiteness or rationality hypothesis. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbZhu OrbSpan OrbIco OrbC2c

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

/-- Full towers, with no finite truncation built into the definition. -/
def zhuTowerSpan {ι : Type*} (s : ι → V) : Submodule ℂ (A W) :=
  Submodule.span ℂ (Set.range fun p : ι × ℕ => (omegaL W ^ p.2) (mk W (s p.1)))

theorem zhuTowerSpan_of_C2 {ι : Type*} (s : ι → V) (k : ι → ℤ)
    (hs : ∀ i, s i ∈ W.grading (k i))
    (hspan : towerSpan W (fun i => mk₂ W (s i)) = ⊤) :
    zhuTowerSpan W s = ⊤ := by
  classical
  let lift : ι × ℕ → V := fun p => ((W.L (-2)) ^ p.2) (s p.1)
  let S : Set V := Set.range lift
  have hShom : ∀ x ∈ S, IsHomog W x := by
    rintro _ ⟨p, rfl⟩
    exact ⟨_, L_neg_two_pow_mem_grading W (hs p.1) p.2⟩
  have hfun : (fun p : ι × ℕ => mk₂ W (lift p)) =
      (fun p : ι × ℕ => (exceptionalConformalEnd W ^ p.2) (mk₂ W (s p.1))) := by
    funext p
    exact (exceptionalConformalEnd_pow_mk W p.2 (s p.1)).symm
  have htop₂ : (⊤ : Submodule ℂ V) = Submodule.span ℂ S ⊔ O₂ W := by
    have hmap : (Submodule.span ℂ S).map (O₂ W).mkQ = ⊤ := by
      rw [Submodule.map_span]
      have himg : (O₂ W).mkQ '' S =
          Set.range fun p : ι × ℕ => mk₂ W (lift p) := by
        ext y
        constructor
        · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
          exact ⟨p, rfl⟩
        · rintro ⟨p, rfl⟩
          exact ⟨lift p, ⟨p, rfl⟩, rfl⟩
      rw [himg, hfun]
      exact hspan
    have hh := congrArg (Submodule.comap (O₂ W).mkQ) hmap
    simpa only [Submodule.comap_map_mkQ, Submodule.comap_top, sup_comm] using hh.symm
  have htop := span_sup_O_eq_top W S hShom htop₂
  have hpow (i : ι) (n : ℕ) : mk W (lift (i, n)) ∈ zhuTowerSpan W s := by
    have hn := mk_L_neg_two_pow_mem W (hs i) n
    apply (show towerSub W (mk W (s i)) (n + 1) ≤ zhuTowerSpan W s from ?_) hn
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨(i, j), rfl⟩
  have hS : ∀ y ∈ Submodule.span ℂ S, mk W y ∈ zhuTowerSpan W s := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      exact hpow p.1 p.2
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  apply top_unique
  intro q _
  obtain ⟨x, rfl⟩ := (O W).mkQ_surjective q
  have hx : x ∈ Submodule.span ℂ S ⊔ O W := by rw [← htop]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have hz0 : mk W z = 0 := (mk_eq_zero_iff W).mpr hz
  change mk W (y + z) ∈ zhuTowerSpan W s
  rw [map_add, hz0, add_zero]
  exact hS y hy

end General

def icoSeeds (b : Bool) : (orbifold ico).carrier := if b then Xico else Wi.vacuum

theorem icoSeeds_grading (b : Bool) : icoSeeds b ∈ Wi.grading (if b then 36 else 0) := by
  cases b
  · exact Wi.vacuum_mem
  · exact Xico_grading

/-- The actual, untruncated Zhu tower span is unconditional. -/
theorem ico_zhuTowerSpan_eq_top : zhuTowerSpan Wi icoSeeds = ⊤ := by
  apply zhuTowerSpan_of_C2 Wi icoSeeds (fun b => if b then 36 else 0) icoSeeds_grading
  have h := OrbXu.orbifold_twoTowers_of_primary ico Xico icoPrimaryReduction_std
  rw [OrbXu.twoTowers_eq_towerSpan] at h
  simpa only [icoSeeds, apply_ite] using h

end VOA.Classification.COne.OrbIcoZ
