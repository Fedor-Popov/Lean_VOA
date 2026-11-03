/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVacuumFourShift
import VOA.Examples.VirasoroMinimalFusionArithmetic
import VOA.Examples.VirasoroMinimalThreeVacuum

/-!
# Nonzero vacuum singular states at every coprime M(p,4) charge

The proved integer-continuant product prevents terminal cancellation for
every odd p. Prime-power nonresonance constructs the actual preterminal
sequence. The Ward identities proved earlier kill its terminal source
by L1 and L2, while the continuant proves that its vacuum projection is
nonzero. This gives actual Gram determinant roots, not simple roots or
new rigidity theorems.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- At the rational vacuum parameter the incoming and field weights
coincide with the explicit weight used in the quartic recurrence. -/
theorem minimalFour_weights (p : ℕ) (hp : 3≤p) :
    fusionKacWeight ((p-1:ℕ):ℂ) 0 ((4:ℂ)/(p:ℂ))=vacuumFourWeight p ∧
    vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))=vacuumFourWeight p := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hs : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by exact_mod_cast Int.ofNat_sub (by omega : 1≤p)
  constructor
  · unfold fusionKacWeight vacuumFourWeight
    rw [hs]
    field_simp
    ring
  · unfold vermaBSAWeight vacuumFourWeight
    norm_num
    field_simp
    ring

/-- At odd labels every interior diagonal is nonzero because four is a
prime power. This supplies all divisions in the actual finite construction. -/
theorem minimalFour_diagonal (p r : ℕ) (hp : 3≤p) (ho : Odd p)
    (hr : 0<r) (hrN : r<(p-1)*3) :
    wardBSASourceDiagonal 0 (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))) ((4:ℂ)/(p:ℂ))
      4 r 4 (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))+4)≠0 := by
  have hcop : Nat.Coprime p 4 := by simpa using ho.coprime_two_right.pow_right 2
  have hh := minimal_fusion_diagonal_prime_power p 4 r (by omega) (by omega)
    hcop (by decide) hr hrN
  have hw := minimal_fusion_weight_zero p 4 (by omega) (by omega)
  have hb := (minimalFour_weights p hp).1.trans (minimalFour_weights p hp).2.symm
  norm_num only [Nat.cast_ofNat] at hw hh
  rw [hw,hb] at hh
  exact hh

/-- The source has its prescribed initial resonance at level zero.
This is the equation allowing the actual highest vector as leading input. -/
theorem minimalFour_diagonal_initial (p : ℕ) (hp : 3≤p) :
    wardBSASourceDiagonal 0 (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))) ((4:ℂ)/(p:ℂ))
      4 0 4 (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))+4)=0 := by
  have hh := wardBSASourceDiagonal_label_initial (p-1) 4 ((4:ℂ)/(p:ℂ)) (by omega)
    (minimal_fusion_parameter_ne_zero p 4 (by omega) (by omega))
  have hw := minimal_fusion_weight_zero p 4 (by omega) (by omega)
  have hb := (minimalFour_weights p hp).1.trans (minimalFour_weights p hp).2.symm
  norm_num only [Nat.cast_ofNat] at hw hh
  rw [hw,hb] at hh
  exact hh

/-- The second resonance is exactly level 3(p-1). It is left undivided
in the finite construction and becomes the singular source. -/
theorem minimalFour_diagonal_terminal (p : ℕ) (hp : 3≤p) :
    wardBSASourceDiagonal 0 (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))) ((4:ℂ)/(p:ℂ))
      4 ((p-1)*3) 4 (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))+4)=0 := by
  have hh := wardBSASourceDiagonal_label_terminal (p-1) 4 ((4:ℂ)/(p:ℂ)) (by omega)
    (minimal_fusion_parameter_ne_zero p 4 (by omega) (by omega))
  have hw := minimal_fusion_weight_zero p 4 (by omega) (by omega)
  have hb := (minimalFour_weights p hp).1.trans (minimalFour_weights p hp).2.symm
  norm_num only [Nat.cast_ofNat] at hw hh
  rw [hw,hb] at hh
  exact hh

/-- An actual normalized coefficient sequence exists at every odd label;
its source vanishes at all levels before the candidate singular level. -/
theorem exists_minimalFour_vacuum_kernel (p : ℕ) (hp : 3≤p) (ho : Odd p) :
    ∃ f : wardSequenceSpace (vermaBSACharge ((4:ℂ)/(p:ℂ))) 0,
      f.val 0=highestVector (vermaBSACharge ((4:ℂ)/(p:ℂ))) 0 ∧
      ∀ r<(p-1)*3,
        (wardSourceAt (vermaBSACharge ((4:ℂ)/(p:ℂ))) 0
          (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))) ((4:ℂ)/(p:ℂ))
          (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))) 4 f).val r=0 := by
  refine exists_ward_partial_kernel (vermaBSACharge ((4:ℂ)/(p:ℂ))) 0
    (wardSourceAt (vermaBSACharge ((4:ℂ)/(p:ℂ))) 0
      (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))) ((4:ℂ)/(p:ℂ))
      (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))) 4)
    (fun r => wardBSASourceDiagonal 0 (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ)))
      ((4:ℂ)/(p:ℂ)) 4 r 4 (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))+4))
    ((p-1)*3) ?_ ?_ ?_ ?_ (fusionLeadingState _ _)
  · exact fun r f hf => wardSourceAt_diagonal _ _ _ _ _ _ r f hf
  · exact fun r f hf => wardSourceAt_below _ _ _ _ _ _ r f hf
  · exact minimalFour_diagonal_initial p hp
  · exact fun r hr hrN => minimalFour_diagonal p r hp ho hr hrN

/-- Every normalized preterminal solution has a nonzero actual vacuum
projection at the terminal level. The cancellation is
excluded by the proved integer four-step product and its two base values. -/
theorem minimalFour_terminal_survival (p : ℕ) (hp : 3≤p) (ho : Odd p)
    (f : wardSequenceSpace (vermaBSACharge ((4:ℂ)/(p:ℂ))) 0)
    (h0 : f.val 0=highestVector (vermaBSACharge ((4:ℂ)/(p:ℂ))) 0)
    (hf : ∀ r<(p-1)*3,
      (wardSourceAt (vermaBSACharge ((4:ℂ)/(p:ℂ))) 0
        (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))) ((4:ℂ)/(p:ℂ))
        (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))) 4 f).val r=0) :
    vacuumProjection (vermaBSACharge ((4:ℂ)/(p:ℂ)))
      ((wardSourceAt (vermaBSACharge ((4:ℂ)/(p:ℂ))) 0
        (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))) ((4:ℂ)/(p:ℂ))
        (vermaBSAWeight 4 ((4:ℂ)/(p:ℂ))) 4 f).val ((p-1)*3))≠0 := by
  apply vacuumProjection_ne_zero_of_survival
  simp only [(minimalFour_weights p hp).2] at hf ⊢
  have hM := fourTerminalIndex_eq p hp ho
  have hM2 : 2≤fourTerminalIndex p := by omega
  have hk : fourTerminalIndex p-2+2=fourTerminalIndex p := by omega
  have ht : 2*(((fourTerminalIndex p-2:ℕ):ℂ)+2)=3*((p:ℂ)-1) := by
    have he : 2*(fourTerminalIndex p-2)+4+3=3*p := by omega
    have he' : 2*((fourTerminalIndex p-2:ℕ):ℂ)+4+3=3*(p:ℂ) := by exact_mod_cast he
    linear_combination he'
  have hh := vacuumFour_terminal_ne_zero_of_integer
    (vermaBSACharge ((4:ℂ)/(p:ℂ))) (p:ℤ)
    (by exact_mod_cast (by omega : p≠0)) f (fourTerminalIndex p-2)
    (by simpa only [Int.cast_natCast] using ht) (by simp [h0])
    (fun j hj hjM => by
      simpa only [Int.cast_natCast] using hf (2*j) (by omega))
    (by rw [hk]; exact fourTerminalInteger_ne_zero p hp ho)
  have hr : 2*(fourTerminalIndex p-2+2)=(p-1)*3 := by omega
  simpa only [hr,Int.cast_natCast] using hh

/-- At every coprime M(p,4) parameter there is an actual nonzero vacuum
singular state of weight 3(p-1). Both positive Ward equations and survival
in the vacuum quotient are proved, not assumed. -/
theorem minimalFour_nonzero_vacuum_singular (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 4) :
    ∃ v : VirUniv (vermaBSACharge ((4:ℂ)/(p:ℂ))),
      v∈gradingVir (vermaBSACharge ((4:ℂ)/(p:ℂ))) (((p-1)*3:ℕ):ℤ) ∧
      v≠0 ∧ Lop (vermaBSACharge ((4:ℂ)/(p:ℂ))) 1 v=0 ∧
      Lop (vermaBSACharge ((4:ℂ)/(p:ℂ))) 2 v=0 := by
  have ho : Odd p := Nat.coprime_two_right.mp
    ((Nat.coprime_pow_right_iff (by omega : 0<2) p 2).mp (by simpa using hcop))
  have hp3 : 3≤p := by obtain ⟨a,ha⟩ := ho; omega
  obtain ⟨f,h0,hf⟩ := exists_minimalFour_vacuum_kernel p hp3 ho
  let t : ℂ := 4/(p:ℂ)
  let b : ℂ := vermaBSAWeight 4 t
  let S := wardSourceAt (vermaBSACharge t) 0 b t b 4 f
  have ht : t≠0 := minimal_fusion_parameter_ne_zero p 4 (by omega) (by omega)
  have hd := fun r hr hrN => minimalFour_diagonal p r hp3 ho hr hrN
  have hz := minimalFour_diagonal_terminal p hp3
  have h1 := nonresonant_terminal_L1 0 b t 4 ((p-1)*3) ht (by omega) f hf hd (by omega) hz
  have h2 := nonresonant_terminal_L2 0 b t 4 ((p-1)*3) ht (by omega) f hf hd (by omega) hz
  refine ⟨vacuumProjection (vermaBSACharge t) (S.val ((p-1)*3)),
    vacuumProjection_level _ _ _ (S.property _),
    minimalFour_terminal_survival p hp3 ho f h0 hf,?_,?_⟩
  · rw [← vacuumProjection_mode,h1,map_zero]
  · rw [← vacuumProjection_mode,h2,map_zero]

/-- The actual partition Gram determinant vanishes at every coprime
M(p,4) charge at weight 3(p-1). This is a root theorem, with no claim
that the root is simple or that its norm derivative is nonzero. -/
theorem partitionDeterminant_minimal_four_root (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 4) :
    ((VirDeformModes.NormalOrdering.partitionGramPolynomial ((p-1)*3)).det).eval
      (minimalCentralCharge p 4 : ℂ)=0 := by
  obtain ⟨v,hv,hn,h1,h2⟩ := minimalFour_nonzero_vacuum_singular p hp hcop
  have hh := VirDeformModes.NormalOrdering.partitionDeterminant_eval_zero_of_singular
    (vermaBSACharge ((4:ℂ)/(p:ℂ))) (n:=(p-1)*3) (by omega) ⟨v,hv⟩
    (by intro hz; exact hn (congrArg Subtype.val hz)) h1 h2
  have hc := minimal_fusion_charge p 4 (by omega : 0<p) (by omega : 0<4)
  norm_num only [Nat.cast_ofNat] at hc
  rw [hc] at hh
  exact hh

end VOA.InverseDS.VirasoroVerma
