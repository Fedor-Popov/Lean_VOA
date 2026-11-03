import VOA.Filtered.AffineSl2UniversalLiPBW
import VOA.Filtered.LiC2Bridge

/-! # Faithfulness and Li compatibility of the explicit Wakimoto realization -/
namespace VOA.AffineSl2GeneralRigidity
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CurrentLi
open VOA.AffineSl2UniversalC2PBW VOA.AffineSl2PBWWakimotoReduction
open VOA.AffineSl2WakimotoLiLeading
noncomputable section
variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The explicit Wakimoto map is faithful, by the proved polynomial triangularity. -/
theorem vacuumToWak_injective : Function.Injective (vacuumToWak k hk) := by
  apply LinearMap.injective_of_linearIndependent (currentPBWBasis k hk).span_eq
  have h := wakimotoOrderedCreationState_linearIndependent k
  convert h using 1
  funext mu
  rw [Function.comp_apply,currentPBWBasis_eq_orderedCreationState]
  exact (wakimotoOrderedCreationState_eq k hk mu).symm

/-- The Wakimoto realization preserves every actual Li depth threshold. -/
theorem vacuumToWak_mem_freeLiAtLeast (p : ℕ) {x : WakModule k}
    (hx : x ∈ liFiltration (universal k hk) p) :
    vacuumToWak k hk x ∈ freeLiAtLeast p := by
  rw [liFiltration_eq_orderedDepthSpan k hk p] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨mu,hmu,rfl⟩ := hx
      rw [orderedCreationState_eq_wordStateA,vacuumToWak_wordStateA]
      apply freeLiAtLeast_mono (d := p) (e := wordFreeLiDegree (orderedPBWColorWord mu))
      · simpa only [orderedCreationDepth_eq_pairsLevel,wordFreeLiDegree,pairsLevel] using hmu
      · exact wakimotoWordState_mem_freeLiAtLeast k _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- A C2-zero state has Wakimoto polynomial supported in positive jet depth. -/
theorem vacuumToWak_mem_freeLiAtLeast_one_of_mem_O₂ {x : WakModule k}
    (hx : x ∈ O₂ (universal k hk)) : vacuumToWak k hk x ∈ freeLiAtLeast 1 :=
  vacuumToWak_mem_freeLiAtLeast k hk 1 (by rwa [liFiltration_one_eq_O₂])

end
end VOA.AffineSl2GeneralRigidity
