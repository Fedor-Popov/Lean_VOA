import VOA.Classification.COne.OrbIcoVActualKernel
import VOA.Examples.VirasoroVermaUniformStraightening

/-! A genuine Virasoro C2 functional on every Verma module, obtained by
uniform PBW transport of the actual spin-six probe. Its negative-mode
law is independent of charge and highest weight. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco
  InverseDS.VirasoroVerma

def uniformTransport (c h c' h' : ℂ) : Verma c h ≃ₗ[ℂ] Verma c' h' :=
  (vermaSortedBasis c h).repr.trans (vermaSortedBasis c' h').repr.symm

theorem uniformTransport_word (c h c' h' : ℂ) (w : List ℕ) :
    uniformTransport c h c' h' (negWord c h w) = negWord c' h' w := by
  apply (vermaSortedBasis c' h').repr.injective
  change (vermaSortedBasis c' h').repr
    ((vermaSortedBasis c' h').repr.symm ((vermaSortedBasis c h).repr (negWord c h w))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact verma_negWord_coordinates_independent c h c' h' w

theorem uniformTransport_creation (c h c' h' : ℂ) (i : ℕ) (v : Verma c h) :
    uniformTransport c h c' h' (vermaMode c h (-(i:ℤ)-1) v) =
      vermaMode c' h' (-(i:ℤ)-1) (uniformTransport c h c' h' v) := by
  have he : (uniformTransport c h c' h').toLinearMap.comp (vermaMode c h (-(i:ℤ)-1)) =
      (vermaMode c' h' (-(i:ℤ)-1)).comp (uniformTransport c h c' h').toLinearMap := by
    apply (vermaSortedBasis c h).ext
    intro w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, vermaSortedBasis_apply]
    rw [← negWord_cons, uniformTransport_word, uniformTransport_word, negWord_cons]
  exact LinearMap.congr_fun he v

def uniformProbe (c h : ℂ) : Verma c h →ₗ[ℂ] ℂ :=
  (OrbIcoS.neutralProbe Xico)⁻¹ •
    (sixthProbe.comp (seedMap Wi 36 Xico OrbIcoZ.X_primary)).comp
      (uniformTransport c h Wi.centralCharge ((36:ℤ):ℂ)).toLinearMap

theorem uniformProbe_highest (c h : ℂ) : uniformProbe c h (highestVector c h)=1 := by
  change (OrbIcoS.neutralProbe Xico)⁻¹ *
    sixthProbe (seedMap Wi 36 Xico OrbIcoZ.X_primary
      (uniformTransport c h Wi.centralCharge ((36:ℤ):ℂ) (negWord c h []))) = 1
  rw [uniformTransport_word, seedMap_word]
  change (OrbIcoS.neutralProbe Xico)⁻¹ * sixthProbe Xico = 1
  rw [sixthProbe_Xico, inv_mul_cancel₀ neutralProbe_Xico_ne_zero]

theorem uniformProbe_creation (c h : ℂ) (i : ℕ) (v : Verma c h) :
    uniformProbe c h (vermaMode c h (-(i:ℤ)-1) v) =
      (if i=1 then (1/2:ℂ) else 0) * uniformProbe c h v := by
  change (OrbIcoS.neutralProbe Xico)⁻¹ *
    sixthProbe (seedMap Wi 36 Xico OrbIcoZ.X_primary
      (uniformTransport c h Wi.centralCharge ((36:ℤ):ℂ)
        (vermaMode c h (-(i:ℤ)-1) v))) = _
  rw [uniformTransport_creation, seedMap_mode, sixthProbe_L]
  change _ = (if i=1 then (1/2:ℂ) else 0) *
    ((OrbIcoS.neutralProbe Xico)⁻¹ * _)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  ring

def wordProbe (w : List ℕ) : ℂ :=
  (w.map fun i => if i=1 then (1/2:ℂ) else 0).prod

theorem uniformProbe_word (c h : ℂ) (w : List ℕ) :
    uniformProbe c h (negWord c h w) = wordProbe w := by
  induction w with
  | nil => exact uniformProbe_highest c h
  | cons i w ih =>
    rw [negWord_cons, uniformProbe_creation, ih]
    rfl

theorem wordProbe_odd (w : List ℕ) (hw : energyHW w % 2 = 1) : wordProbe w = 0 := by
  by_contra hn
  have hall : ∀ i ∈ w, i=1 := by
    intro i hi
    by_contra hn1
    have hz : (0:ℂ) ∈ w.map (fun i => if i=1 then (1/2:ℂ) else 0) :=
      List.mem_map.mpr ⟨i,hi,by simp [hn1]⟩
    exact hn (List.prod_eq_zero_iff.mpr hz)
  have hm : w.map (fun i => i+1) = w.map (fun _ => 2) := by
    apply List.map_congr_left
    intro i hi
    rw [hall i hi]
  simp only [energyHW, hm, List.map_const', List.sum_replicate, nsmul_eq_mul, Nat.cast_id] at hw
  omega

theorem uniformProbe_odd_level (c h : ℂ) (N : ℕ) (hN : N%2=1)
    (v : Verma c h) (hv : v ∈ sortedSpan c h N) : uniformProbe c h v = 0 := by
  obtain ⟨a,rfl⟩ := exists_vermaLevelState c h N v hv
  simp only [vermaLevelState, map_sum, map_smul, uniformProbe_word]
  apply Finset.sum_eq_zero
  intro w hw
  rw [wordProbe_odd w.val (by simpa [w.property.2] using hN), smul_zero]

theorem uniformProbe_s13_zero (c h t : ℂ) :
    uniformProbe c h (vermaBSASource c h t 13 13)=0 :=
  uniformProbe_odd_level c h 13 (by norm_num) _ (vermaBSASource_mem_level _ _ _ _ _)

end VOA.Classification.COne.OrbIcoV
