import VOA.DeligneAudit.D4LeviKSRzGraded

/-! The source and two brackets driving f₃ polarization of U and U'. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- The source is killed by every f₃ current mode. -/
theorem fThree_source_mode_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (s : ℕ) : ρ.op (17 : Fin 28) s w = 0 := by
  have hh := VOA.DeligneAudit.A3Sector.a3_simple_conversion_kill
    (leviCurrent ρ) w 0 m 0 (source_localWeyl ρ w m h)
    0 1 s (by omega)
      (by simp [VOA.DeligneAudit.A3Sector.weightABC])
  simpa [VOA.DeligneAudit.LeviConversion.fCurrent, leviCurrent,
    leviColour, leviSign, VOA.DeligneAudit.A3Sector.simpleF] using hh

/-- The f₃ current changes X into minus U'. -/
theorem fThree_x_comm (r s : ℕ) :
    ρ.op (17 : Fin 28) r * ρ.op (22 : Fin 28) s -
      ρ.op (22 : Fin 28) s * ρ.op (17 : Fin 28) r =
        -ρ.op (25 : Fin 28) (r + s) := by
  ext v
  have hc := ρ.comm (17 : Fin 28) (22 : Fin 28) r s v
  change ρ.op (17 : Fin 28) r (ρ.op (22 : Fin 28) s v) -
    ρ.op (22 : Fin 28) s (ρ.op (17 : Fin 28) r v) = _
  rw [hc]
  change (∑ c : Fin 28,
    fD4 (lowerColour 0) (radicalColour 1) c • ρ.op c (r + s) v) = _
  have hcoef (c : Fin 28) :
      fD4 (lowerColour 0) (radicalColour 1) c =
        if c = radicalColour 3 then (-1 : ℂ) else 0 := by
    simpa [lowerAction] using lower_coefficient 0 1 c
  simp only [hcoef, ite_smul, neg_one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [radicalColour]

/-- The f₃ current changes U into minus Y. -/
theorem fThree_u_comm (r s : ℕ) :
    ρ.op (17 : Fin 28) r * ρ.op (24 : Fin 28) s -
      ρ.op (24 : Fin 28) s * ρ.op (17 : Fin 28) r =
        -ρ.op (26 : Fin 28) (r + s) := by
  ext v
  have hc := ρ.comm (17 : Fin 28) (24 : Fin 28) r s v
  change ρ.op (17 : Fin 28) r (ρ.op (24 : Fin 28) s v) -
    ρ.op (24 : Fin 28) s (ρ.op (17 : Fin 28) r v) = _
  rw [hc]
  change (∑ c : Fin 28,
    fD4 (lowerColour 0) (radicalColour 2) c • ρ.op c (r + s) v) = _
  have hcoef (c : Fin 28) :
      fD4 (lowerColour 0) (radicalColour 2) c =
        if c = radicalColour 4 then (-1 : ℂ) else 0 := by
    simpa [lowerAction] using lower_coefficient 0 2 c
  simp only [hcoef, ite_smul, neg_one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [radicalColour]

/-- The first polarization identity replaces a U'U pair by XY modulo an f₃ image. -/
theorem fThree_uup_polarization
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r t u : ℕ) :
    ρ.op (25 : Fin 28) (r + t) (ρ.op (24 : Fin 28) u w) =
      -ρ.op (17 : Fin 28) r
        (ρ.op (22 : Fin 28) t (ρ.op (24 : Fin 28) u w)) -
      ρ.op (22 : Fin 28) t (ρ.op (26 : Fin 28) (r + u) w) := by
  have hx := congrArg (fun T : Module.End ℂ V =>
    T (ρ.op (24 : Fin 28) u w)) (fThree_x_comm ρ r t)
  have hu := congrArg (fun T : Module.End ℂ V => T w)
    (fThree_u_comm ρ r u)
  have hzero := fThree_source_mode_zero ρ w m h r
  have hu' : ρ.op (17 : Fin 28) r (ρ.op (24 : Fin 28) u w) =
      -ρ.op (26 : Fin 28) (r + u) w := by
    simpa [LinearMap.sub_apply, Module.End.mul_apply, hzero]
      using hu
  have hx' : ρ.op (17 : Fin 28) r
      (ρ.op (22 : Fin 28) t (ρ.op (24 : Fin 28) u w)) -
      ρ.op (22 : Fin 28) t
        (ρ.op (17 : Fin 28) r (ρ.op (24 : Fin 28) u w)) =
      -ρ.op (25 : Fin 28) (r + t) (ρ.op (24 : Fin 28) u w) := by
    simpa [LinearMap.sub_apply, Module.End.mul_apply] using hx
  rw [hu'] at hx'
  simp only [map_neg] at hx'
  simp only [sub_neg_eq_add] at hx'
  calc
    _ = -(ρ.op (17 : Fin 28) r
        (ρ.op (22 : Fin 28) t (ρ.op (24 : Fin 28) u w)) +
          ρ.op (22 : Fin 28) t (ρ.op (26 : Fin 28) (r + u) w)) := by
      rw [hx']
      simp
    _ = _ := by abel

/-- One U'U pair is absorbed by higher XU and XY keys. -/
theorem uup_pair_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r t u : ℕ) :
    ρ.op (25 : Fin 28) (r + t) (ρ.op (24 : Fin 28) u w) ∈
      higherOrbit ρ w m ⟨0, 0, 1, 1, 0, 0, r + t + u⟩ := by
  let K : RadicalKey := ⟨0, 0, 1, 1, 0, 0, r + t + u⟩
  let N := higherOrbit ρ w m K
  have hxu : keyLess m K (wordKey [(1, t), (2, u)]) := by
    left
    simp [K, keyHeight, wordKey]
  have hxy : keyLess m K (wordKey [(1, t), (4, r + u)]) := by
    simp [K, keyLess, keyHeight, wordKey]
    omega
  have hxu_mem : ρ.op (22 : Fin 28) t (ρ.op (24 : Fin 28) u w) ∈ N := by
    have hh := keyOrbit_le_higher ρ w m K
      (wordKey [(1, t), (2, u)]) hxu
      (keyLayer_le_orbit ρ w _
        (radicalWord_mem_key ρ w [(1, t), (2, u)]))
    simpa [N, radicalWord, wordOp, radicalColour] using hh
  have hf : ρ.op (17 : Fin 28) r
      (ρ.op (22 : Fin 28) t (ρ.op (24 : Fin 28) u w)) ∈ N := by
    exact higherOrbit_full_levi_inv ρ w m K (17 : Fin 28)
      ⟨7, rfl⟩ r hxu_mem
  have hxy_mem : ρ.op (22 : Fin 28) t
      (ρ.op (26 : Fin 28) (r + u) w) ∈ N := by
    have hh := keyOrbit_le_higher ρ w m K
      (wordKey [(1, t), (4, r + u)]) hxy
      (keyLayer_le_orbit ρ w _
        (radicalWord_mem_key ρ w [(1, t), (4, r + u)]))
    simpa [N, radicalWord, wordOp, radicalColour] using hh
  rw [fThree_uup_polarization ρ w m h r t u]
  exact N.sub_mem (N.neg_mem hf) hxy_mem

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fThree_source_mode_zero
#print axioms VOA.DeligneAudit.D4Levi.fThree_x_comm
#print axioms VOA.DeligneAudit.D4Levi.fThree_u_comm
#print axioms VOA.DeligneAudit.D4Levi.fThree_uup_polarization
#print axioms VOA.DeligneAudit.D4Levi.uup_pair_higher
