import VOA.Classification.COne.OrbIcoVSeedMap
import VOA.Classification.COne.FeiginFuchsLower

/-! Any proper highest-weight map at c=1,h=36 which kills the first-row
BSA source has the full contravariant radical as its kernel in each level.
This compares the genuine Fock and actual VOA realizations. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA InverseDS.VirasoroVerma
open scoped Classical

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem map_killed_singularMap_zero (c h : ℂ) (n : ℕ) (v : Verma c h)
    (hv : v ∈ sortedSpan c h n)
    (h₁ : vermaMode c h 1 v=0) (h₂ : vermaMode c h 2 v=0)
    (f : Verma c h →ₗ[ℂ] V) (Lm : ℤ → Module.End ℂ V)
    (hmode : ∀ k u, f (vermaMode c h k u) = Lm k (f u)) (hz : f v=0) :
    f.comp (vermaSingularMap c h n v hv h₁ h₂) = 0 := by
  have hd (w : List ℕ) : f (vermaDescendant c h w v)=0 := by
    induction w with
    | nil => exact hz
    | cons i w ih =>
      change f (vermaMode c h (-(i:ℤ)-1) _)=0
      rw [hmode, ih, map_zero]
  apply (vermaSortedBasis c (h+(n:ℂ))).ext
  intro w
  rw [LinearMap.comp_apply, vermaSortedBasis_apply, vermaSingularMap,
    verma_universalMap_word, LinearMap.zero_apply]
  exact hd w.val

theorem c_one_thirteen_positive :
    vermaMode 1 36 1 (vermaBSASource 1 36 1 13 13)=0 ∧
    vermaMode 1 36 2 (vermaBSASource 1 36 1 13 13)=0 := by
  have he := vermaBSASource_one_two_all (1:ℂ) 13 one_ne_zero (by norm_num)
  have transfer (c h : ℂ) (hc : c=1) (hh : h=36)
      (he : vermaMode c h 1 (vermaBSASource c h 1 13 13)=0 ∧
        vermaMode c h 2 (vermaBSASource c h 1 13 13)=0) :
      vermaMode 1 36 1 (vermaBSASource 1 36 1 13 13)=0 ∧
        vermaMode 1 36 2 (vermaBSASource 1 36 1 13 13)=0 := by
    subst c
    subst h
    exact he
  exact transfer _ _ (by norm_num [vermaBSACharge]) (by norm_num [vermaBSAWeight]) he

theorem killed_bsa_kernel_eq_radicalLevel (c h : ℂ) (hc : c=1) (hh : h=36)
    (f : Verma c h →ₗ[ℂ] V) (Lm : ℤ → Module.End ℂ V)
    (hmode : ∀ k u, f (vermaMode c h k u)=Lm k (f u))
    (hker : LinearMap.ker f ≤ vermaRadical c h)
    (hz : f (vermaBSASource c h 1 13 13)=0) (m : ℕ) :
    sortedSpan c h (13+m) ⊓ LinearMap.ker f = vermaRadicalLevel c h (13+m) := by
  have hpos : vermaMode c h 1 (vermaBSASource c h 1 13 13)=0 ∧
      vermaMode c h 2 (vermaBSASource c h 1 13 13)=0 := by
    subst c
    subst h
    exact c_one_thirteen_positive
  let v := vermaBSASource c h 1 13 13
  have hv : v ∈ sortedSpan c h 13 := vermaBSASource_mem_level _ _ _ _ _
  have hne : v ≠ 0 := vermaBSASource_ne_zero _ _ _ _ one_ne_zero (by norm_num)
  let S := vermaSingularMap c h 13 v hv hpos.1 hpos.2
  let D := (sortedSpan c (h+13) m).map S
  let K := sortedSpan c h (13+m) ⊓ LinearMap.ker f
  have hD : Module.finrank ℂ D = Fintype.card (VermaPartitions m) :=
    vermaSingularMap_level_finrank c h 13 m v hv hne hpos.1 hpos.2
  have hDK : D ≤ K := by
    rintro x ⟨u,hu,rfl⟩
    refine ⟨(vermaSingularMap_mem_level_iff c h 13 m v hv hne hpos.1 hpos.2 u).mpr hu, ?_⟩
    exact LinearMap.congr_fun (map_killed_singularMap_zero c h 13 v hv hpos.1 hpos.2
      f Lm hmode hz) u
  have hKR : K ≤ vermaRadicalLevel c h (13+m) := by
    rintro x ⟨hx,hf⟩
    exact ⟨hx,hker hf⟩
  have hR : Module.finrank ℂ (vermaRadicalLevel c h (13+m)) ≤
      Fintype.card (VermaPartitions m) := by
    subst c
    subst h
    convert FFLower.radical_bound 6 m using 1 <;> norm_num
  have hdim := Submodule.finrank_mono hDK
  rw [hD] at hdim
  exact Submodule.eq_of_le_of_finrank_le hKR (hR.trans hdim)

end VOA.Classification.COne.OrbIcoV
