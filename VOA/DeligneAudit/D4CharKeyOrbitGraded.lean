import VOA.DeligneAudit.D4CharQuotientGrading
import VOA.DeligneAudit.D4CharGradedAssembly

/-! The sharp graded GL4 bound on each supported D4 higher-key quotient. -/

namespace VOA.DeligneAudit.D4Char

open SectorWeyl UnivG DeligneSector.D4 D4Levi

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem finite_iSup_rank (m L : ℕ) (O : Fin m → Submodule ℂ V)
    (hb : ∀ j, FiniteDimensional ℂ (O j) ∧ Module.finrank ℂ (O j) ≤ L) :
    FiniteDimensional ℂ (⨆ j, O j : Submodule ℂ V) ∧
      Module.finrank ℂ (⨆ j, O j : Submodule ℂ V) ≤ L * m := by
  have hs (s : Finset (Fin m)) :
      FiniteDimensional ℂ (s.sup O : Submodule ℂ V) ∧
        Module.finrank ℂ (s.sup O : Submodule ℂ V) ≤ ∑ j ∈ s, L := by
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.sup_empty]
        exact ⟨inferInstance, by simp⟩
    | @insert j s hj ih =>
        haveI := (hb j).1
        haveI := ih.1
        rw [Finset.sup_insert, Finset.sum_insert hj]
        exact ⟨inferInstance,
          (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
            (Nat.add_le_add (hb j).2 ih.2)⟩
  have hh := hs Finset.univ
  have he : (Finset.univ : Finset (Fin m)).sup O = ⨆ j, O j := by
    simp [Finset.sup_eq_iSup]
  rw [he] at hh
  refine ⟨hh.1, ?_⟩
  simpa [Nat.mul_comm] using hh.2

theorem supported_key_dominant (m : ℕ) (k : RadicalKey)
    (hs : ksCorrectedSupported m k) : ∀ i : Fin 3, 0 ≤ keyLabel m i k := by
  obtain ⟨he, hu, hup, hy, hz⟩ := hs
  intro i
  fin_cases i <;> simp [keyLabel, he, hu, hup] <;> omega

theorem supported_key_weight (m : ℕ) (k : RadicalKey)
    (hs : ksCorrectedSupported m k) :
    keyWeight m k = A3Sector.weightABC (ksKeyClass m k 0)
      (ksKeyClass m k 1 + ksKeyClass m k 2) (ksKeyClass m k 0) := by
  obtain ⟨he, hu, hup, hy, hz⟩ := hs
  funext i
  fin_cases i <;>
    simp [A3Sector.weightABC, keyWeight, keyLabel, ksKeyClass, he, hu, hup] <;> omega

theorem supported_key_cyclic_graded (ρ : CurrentModule D4sector.f V) (w : V)
    (m : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (hs : ksCorrectedSupported m k)
    {v : V} (hv : v ∈ keyLayer ρ w k) (d : ℕ) :
    let C := cycDeg (keyQuotCurrent ρ w m k) ((higherOrbit ρ w m k).mkQ v) d
    FiniteDimensional ℂ C ∧
      Module.finrank ℂ C ≤ leviClassHilb (ksKeyClass m k) d := by
  have hr := key_localWeyl_quot ρ w m h k (supported_key_dominant m k hs) hv
  rw [supported_key_weight m k hs] at hr
  have hh := a3_all_weight_graded_bound _ _ _ _ _ hr d
  dsimp only
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  unfold leviClassHilb
  congr 1 <;> omega

def d4RestrictedGrading (ρ : CurrentModule D4sector.f V) (g : CurrentGrading ρ) :
    CurrentGrading (leviCurrent ρ) where
  piece := g.piece
  proj := g.proj
  proj_mem := g.proj_mem
  proj_piece := g.proj_piece
  op_piece a r d v hv := (g.piece (r + d)).smul_mem (leviSign a : ℂ)
    (g.op_piece (leviColour a) r d v hv)

theorem higherOrbit_projection (R : RelSpec 28) (m : ℕ) (k : RadicalKey) (N : ℕ) :
    (higherOrbit (univRepG D4sector.f R) (wUG D4sector.f R) m k).map
      (projUG D4sector.f R N) ≤
        higherOrbit (univRepG D4sector.f R) (wUG D4sector.f R) m k := by
  rw [higherOrbit, Submodule.map_iSup]
  apply iSup_le
  intro j
  rw [projUG_keyOrbit]
  exact le_iSup_of_le j ((gradedKeyOrbit_le _ _ _ _).trans inf_le_right)

def universalKeyGrading (R : RelSpec 28) (m : ℕ) (k : RadicalKey) :
    CurrentGrading (keyQuotCurrent (univRepG D4sector.f R) (wUG D4sector.f R) m k) :=
  quotientCurrentGrading
    (d4RestrictedGrading _ (universalCurrentGrading (f := D4sector.f) R))
    (higherOrbit (univRepG D4sector.f R) (wUG D4sector.f R) m k)
    (higherOrbit_levi_inv _ _ m k) (higherOrbit_projection R m k)

theorem universal_key_orbit_graded_bound (m N : ℕ) (k : RadicalKey)
    (hs : ksCorrectedSupported m k) (hd : k.degree ≤ N) :
    let ρ := univRepG D4sector.f (ravFam D4sector m 0)
    let w := wUG D4sector.f (ravFam D4sector m 0)
    let F := higherOrbit ρ w m k
    let S := keyLayer ρ w k
    let O := (gradedKeyOrbit ρ w k N).map F.mkQ
    FiniteDimensional ℂ O ∧ Module.finrank ℂ O ≤
      leviClassHilb (ksKeyClass m k) (N - k.degree) *
        Module.finrank ℂ (S ⧸ F.comap S.subtype) := by
  let R := ravFam D4sector m 0
  let ρ := univRepG D4sector.f R
  let w := wUG D4sector.f R
  let F := higherOrbit ρ w m k
  let S := keyLayer ρ w k
  let Q := keyQuotCurrent ρ w m k
  let qg := universalKeyGrading R m k
  let r := Module.finrank ℂ (S ⧸ F.comap S.subtype)
  have h := univG_sat D4sector.f R
  obtain ⟨v, hv⟩ := keyOrbit_map_eq_basis_orbits ρ w m h k
  have he : (gradedKeyOrbit ρ w k N).map F.mkQ =
      ⨆ j : Fin r, cycDeg Q (F.mkQ (v j : UModG D4sector.f R)) (N - k.degree) := by
    rw [← projUG_keyOrbit R k N]
    have hc := quotient_projection_commute
      (d4RestrictedGrading ρ (universalCurrentGrading R)) F
      (higherOrbit_levi_inv ρ w m k) (higherOrbit_projection R m k)
      (keyOrbit ρ w k) N
    change ((keyOrbit ρ w k).map (projUG D4sector.f R N)).map F.mkQ =
      ((keyOrbit ρ w k).map F.mkQ).map (qg.proj N) at hc
    rw [hc, hv, Submodule.map_iSup]
    congr 1
    funext j
    exact currentGrading_cyclic_shift qg k.degree N
      ⟨v j, keyLayer_le_exact_degree ρ w k (v j).property, rfl⟩ hd
  dsimp only
  rw [he]
  exact finite_iSup_rank r _ _ (fun j =>
    supported_key_cyclic_graded ρ w m h k hs (v j).property (N - k.degree))

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.finite_iSup_rank
#print axioms VOA.DeligneAudit.D4Char.supported_key_dominant
#print axioms VOA.DeligneAudit.D4Char.supported_key_weight
#print axioms VOA.DeligneAudit.D4Char.supported_key_cyclic_graded
#print axioms VOA.DeligneAudit.D4Char.higherOrbit_projection
#print axioms VOA.DeligneAudit.D4Char.universal_key_orbit_graded_bound
