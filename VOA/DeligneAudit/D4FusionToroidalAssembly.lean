import VOA.DeligneAudit.D4FusionToroidalAssemblyTransfer

/-! The Kus–Littelmann rank squeeze, conditional on a finite graded rank bound. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {F : Type*} [AddCommGroup F] [Module ℂ F]

private theorem wordOpT_map {m : ℕ}
    (ρG : ToroidalModule D4sector.f m
      (Gr D4sector.f (ravFam D4sector m 0) m))
    (ρF : ToroidalModule D4sector.f m F)
    (φ : Gr D4sector.f (ravFam D4sector m 0) m →ₗ[ℂ] F)
    (heq : ∀ c i s x, φ (ρG.op c i s x) = ρF.op c i s (φ x))
    (l : List (TLtr 28)) (x) :
    φ (wordOpT ρG l x) = wordOpT ρF l (φ x) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      change φ (ρG.op a.1 a.2.1 a.2.2 (wordOpT ρG l x)) = _
      rw [heq, ih]
      rfl

private theorem wordOpT_mem_zero {m : ℕ} (ρF : ToroidalModule D4sector.f m F)
    (F₀ : Submodule ℂ F) (hst : ∀ c s, F₀ ≤ F₀.comap (ρF.op c 0 s))
    (l : List (TLtr 28)) (v : F) (hv : v ∈ F₀)
    (hl : uDeg l = 0) : wordOpT ρF l v ∈ F₀ := by
  induction l with
  | nil => simpa [wordOpT] using hv
  | cons a l ih =>
      have ha : a.2.1 = 0 := by simpa [uDeg] using (Nat.add_eq_zero_iff.mp hl).1
      have ht : uDeg l = 0 := by simpa [uDeg] using (Nat.add_eq_zero_iff.mp hl).2
      simpa [wordOpT, ha] using hst a.1 a.2.2 (ih ht)

private theorem symbol_uDeg (m : ℕ) : ∀ l : List (Ltr 28),
    uDeg (symbolLetters m l) = symbolDegree m l
  | [] => rfl
  | _ :: l => by simp [symbolLetters, symbolDegree, uDeg, symbol_uDeg m l]

private theorem zeroClass_word_mem {m : ℕ} (hm : 1 ≤ m)
    (ρF : ToroidalModule D4sector.f m F) (vF : F)
    (φ : Gr D4sector.f (ravFam D4sector m 0) m →ₗ[ℂ] F)
    (hgen : φ (grGenerator D4sector.f (ravFam D4sector m 0) m) = vF)
    (heq : ∀ c i s x, φ ((grToroidal_D4 m hm).op c i s x) =
      ρF.op c i s (φ x))
    (F₀ : Submodule ℂ F) (hv : vF ∈ F₀)
    (hst : ∀ c s, F₀ ≤ F₀.comap (ρF.op c 0 s))
    (l : List (Ltr 28)) :
    φ (zeroClass D4sector.f (ravFam D4sector m 0) m
      (wordOp (univRepG D4sector.f (ravFam D4sector m 0)) l
        (wUG D4sector.f (ravFam D4sector m 0)))) ∈ F₀ := by
  let R := ravFam D4sector m 0
  let f := D4sector.f
  have hw : wUG f R ∈ TU f R m 0 := by rw [TU_zero]; trivial
  by_cases hd : symbolDegree m l = 0
  · have hword : zeroClass f R m (wordOp (univRepG f R) l (wUG f R)) =
        wordOpT (grToroidal_D4 m hm) (symbolLetters m l)
          (grGenerator f R m) := by
      have hh := wordOpT_gr f R m (highModeShift_D4 R m hm) hm l 0 (wUG f R) hw
      have hg : gradedSingle f R m (0 + symbolDegree m l)
          (wordOp (univRepG f R) l (wUG f R))
          (word_mem_shift f R m (highModeShift_D4 R m hm) hm l 0 (wUG f R) hw) =
          gradedSingle f R m 0 (wordOp (univRepG f R) l (wUG f R))
            (by rw [TU_zero]; trivial) := by
        apply Subtype.ext
        simp [gradedSingle, hd]
      calc
        _ = (grKernel f R m).mkQ (gradedSingle f R m 0
            (wordOp (univRepG f R) l (wUG f R))
              (by rw [TU_zero]; trivial)) := rfl
        _ = (grKernel f R m).mkQ (gradedSingle f R m
            (0 + symbolDegree m l) (wordOp (univRepG f R) l (wUG f R))
              (word_mem_shift f R m (highModeShift_D4 R m hm) hm l 0
                (wUG f R) hw)) := congrArg _ hg.symm
        _ = _ := by simpa [grGenerator, grToroidal_D4] using hh.symm
    rw [hword, wordOpT_map (grToroidal_D4 m hm) ρF φ heq, hgen]
    exact wordOpT_mem_zero ρF F₀ hst _ _ hv ((symbol_uDeg m l).trans hd)
  · have hshift := word_mem_shift f R m (highModeShift_D4 R m hm) hm l
      0 (wUG f R) hw
    have htu : wordOp (univRepG f R) l (wUG f R) ∈ TU f R m 1 :=
      TU_mono f R m (by omega : 1 ≤ 0 + symbolDegree m l) hshift
    have hk : wordOp (univRepG f R) l (wUG f R) ∈
        LinearMap.ker (zeroClass f R m) := by
      rw [zeroClass_ker]
      exact htu
    change zeroClass f R m _ = 0 at hk
    rw [hk, map_zero]
    exact F₀.zero_mem

private theorem zero_image_le {m : ℕ} (hm : 1 ≤ m)
    (ρF : ToroidalModule D4sector.f m F) (vF : F)
    (φ : Gr D4sector.f (ravFam D4sector m 0) m →ₗ[ℂ] F)
    (hgen : φ (grGenerator D4sector.f (ravFam D4sector m 0) m) = vF)
    (heq : ∀ c i s x, φ ((grToroidal_D4 m hm).op c i s x) =
      ρF.op c i s (φ x))
    (F₀ : Submodule ℂ F) (hv : vF ∈ F₀)
    (hst : ∀ c s, F₀ ≤ F₀.comap (ρF.op c 0 s)) :
    Gzero D4sector.f (ravFam D4sector m 0) m ≤ F₀.comap φ := by
  rintro y ⟨x, rfl⟩
  change φ (zeroClass D4sector.f (ravFam D4sector m 0) m x) ∈ F₀
  have hs : Submodule.span ℂ (Set.range fun l : List (Ltr 28) =>
      wordOp (univRepG D4sector.f (ravFam D4sector m 0)) l
        (wUG D4sector.f (ravFam D4sector m 0))) ≤
      F₀.comap (φ.comp (zeroClass D4sector.f (ravFam D4sector m 0) m)) := by
    rw [Submodule.span_le]
    rintro z ⟨l, rfl⟩
    exact zeroClass_word_mem hm ρF vF φ hgen heq F₀ hv hst l
  have htop : ⊤ ≤ F₀.comap (φ.comp
      (zeroClass D4sector.f (ravFam D4sector m 0) m)) := by
    calc
      ⊤ = Submodule.span ℂ (Set.range fun l : List (Ltr 28) =>
          wordOp (univRepG D4sector.f (ravFam D4sector m 0)) l
            (wUG D4sector.f (ravFam D4sector m 0))) :=
        (D4FusionContact.Polynomial.universal_word_span D4sector.f
          (ravFam D4sector m 0)).symm
      _ ≤ _ := hs
  exact htop (by trivial)

/-- KL-G: the rank squeeze given finite graded rank and symbol equivariance. -/
theorem assembly_rank {m : ℕ} (hm : 1 ≤ m)
    [FiniteDimensional ℂ (UModG D4sector.f (ravFam D4sector m 0))]
    [FiniteDimensional ℂ (Gr D4sector.f (ravFam D4sector m 0) m)]
    [FiniteDimensional ℂ F]
    (ρF : ToroidalModule D4sector.f m F) (vF : F)
    (φ : Gr D4sector.f (ravFam D4sector m 0) m →ₗ[ℂ] F)
    (hgen : φ (grGenerator D4sector.f (ravFam D4sector m 0) m) = vF)
    (heq : ∀ c i s x, φ ((grToroidal_D4 m hm).op c i s x) =
      ρF.op c i s (φ x))
    (hsurj : Function.Surjective φ)
    (F₀ : Submodule ℂ F) (hv : vF ∈ F₀)
    (hst : ∀ c s, F₀ ≤ F₀.comap (ρF.op c 0 s))
    (hgr : Module.finrank ℂ (Gr D4sector.f (ravFam D4sector m 0) m) ≤
      Module.finrank ℂ (UModG D4sector.f (ravFam D4sector m 0)))
    (hU : Module.finrank ℂ (UModG D4sector.f (ravFam D4sector m 0)) ≤ 29 ^ m)
    (hF : 29 ^ m ≤ Module.finrank ℂ F)
    (hF₀ : Module.finrank ℂ F₀ ≤ 28 ^ m) :
    Module.finrank ℂ (FusionToroidal.truncMod D4sector.f
      (ravFam D4sector m 0) m) ≤ 28 ^ m := by
  have hrank : Module.finrank ℂ (Gr D4sector.f (ravFam D4sector m 0) m) =
      Module.finrank ℂ F :=
    Nat.le_antisymm (hgr.trans (hU.trans hF))
      (LinearMap.finrank_le_finrank_of_surjective hsurj)
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hsurj
  have hsub := zero_image_le hm ρF vF φ hgen heq F₀ hv hst
  let ψ : Gzero D4sector.f (ravFam D4sector m 0) m →ₗ[ℂ] F₀ :=
    (φ.comp (Gzero D4sector.f (ravFam D4sector m 0) m).subtype).codRestrict
      F₀ (fun x => hsub x.property)
  have hψ : Function.Injective ψ := by
    intro x y hxy
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hxy
  calc
    _ = Module.finrank ℂ (Gzero D4sector.f (ravFam D4sector m 0) m) :=
      (truncEquivZero D4sector.f (ravFam D4sector m 0) m).finrank_eq
    _ ≤ Module.finrank ℂ F₀ := LinearMap.finrank_le_finrank_of_injective hψ
    _ ≤ 28 ^ m := hF₀

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.assembly_rank
