/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSAWardTransport

/-!
# The BSA word recursion on actual descendant coefficient sequences

The restricted commutator system is constructed from the actual operators.
A seed with the specified weight and zero positive Ward defects therefore
has terminal BSA output with zero positive defects. Neither existence of
such a nonzero seed nor nonvanishing of the output is asserted here.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- The integer-indexed operators required for BSA transport. Indices above
two are set to zero because they are unused; this is deliberately NOT a
claimed full Virasoro representation. Negative indices are all actual
constructed descendants, and indices zero, one and two are W, P and Q. -/
noncomputable def wardTransportMode (c h b : ℂ) : ℤ → Module.End ℂ (ℂ → wardSequenceSpace c h)
  | .ofNat 0 => wardWeight c h
  | .ofNat 1 => wardP c h b
  | .ofNat 2 => wardQ c h b
  | .ofNat (_+3) => 0
  | .negSucc 0 => wardA c h b
  | .negSucc (n+1) => wardNegative c h b n

/-- The actual modes satisfy all commutators used by the BSA proof. No
negative-negative identity or higher positive action is needed. -/
theorem wardTransportMode_comm (c h b : ℂ) (m n : ℤ) (hm : 0≤m) (hm2 : m≤2) (hn : n<0) :
    ⁅wardTransportMode c h b m,wardTransportMode c h b n⁆=
      ((m:ℂ)-(n:ℂ)) • wardTransportMode c h b (m+n)+
      (if m+n=0 then c*((m:ℂ)^3-(m:ℂ))/12 else 0) • LinearMap.id := by
  obtain ⟨k,rfl⟩ := Int.eq_negSucc_of_lt_zero hn
  interval_cases m
  · cases k with
    | zero => convert wardWeight_A c h b using 1 <;> norm_num [wardTransportMode] <;> module
    | succ k => convert wardWeight_negative c h b k using 1 <;> norm_num [wardTransportMode] <;> module
  · cases k with
    | zero =>
      rw [show (1:ℤ)+Int.negSucc 0=0 by decide]
      convert wardP_A c h b using 1 <;> norm_num [wardTransportMode]
    | succ k =>
      have hi : (1:ℤ)+Int.negSucc (k+1)=Int.negSucc k := by omega
      rw [hi]
      cases k with
      | zero => convert wardP_B c h b using 1 <;> norm_num [wardTransportMode] <;> module
      | succ k => convert wardP_negative c h b k using 1 <;> norm_num [wardTransportMode] <;> module
  · cases k with
    | zero =>
      rw [show (2:ℤ)+Int.negSucc 0=1 by decide]
      convert wardQ_A c h b using 1 <;> norm_num [wardTransportMode]
    | succ k =>
      cases k with
      | zero =>
        rw [show (2:ℤ)+Int.negSucc (0+1)=0 by decide]
        convert wardQ_B c h b using 1 <;> norm_num [wardTransportMode] <;> module
      | succ k =>
        have hi : (2:ℤ)+Int.negSucc (k+1+1)=Int.negSucc k := by omega
        rw [hi]
        cases k with
        | zero => convert wardQ_negative_one c h b using 1 <;> norm_num [wardTransportMode] <;> module
        | succ k => convert wardQ_negative c h b k using 1 <;> norm_num [wardTransportMode] <;> module

/-- Package the already proved actual commutators with a weight-a seed
whose first two Ward defects vanish. The only seed assumptions are displayed;
no singular-state or rigidity conclusion is included among them. -/
noncomputable def wardTransportSystem (c h b a : ℂ) (f : ℂ → wardSequenceSpace c h)
    (h0 : wardWeight c h f=a • f) (h1 : wardP c h b f=0) (h2 : wardQ c h b f=0) :
    BSAWardTransport.System (ℂ → wardSequenceSpace c h) c a where
  mode := wardTransportMode c h b
  seed := f
  seed_zero := h0
  seed_one := h1
  seed_two := h2
  comm_law m n hm hm2 hn v := by
    have hh := congrArg (fun T : Module.End ℂ (ℂ → wardSequenceSpace c h) => T v)
      (wardTransportMode_comm c h b m n hm hm2 hn)
    change wardTransportMode c h b m (wardTransportMode c h b n v)-
      wardTransportMode c h b n (wardTransportMode c h b m v)=_ at hh
    simpa only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,add_assoc] using
      (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

/-- The explicit terminal BSA expression in actual descendant operators.
Its parameters include the seed equations, so existence and nonvanishing
of a suitable primary seed remain separate mathematical obligations. -/
noncomputable def wardBSATerminal (h b t : ℂ) (N : ℕ)
    (f : ℂ → wardSequenceSpace (vermaBSACharge t) h)
    (h0 : wardWeight (vermaBSACharge t) h f=vermaBSAWeight N t • f)
    (h1 : wardP (vermaBSACharge t) h b f=0) (h2 : wardQ (vermaBSACharge t) h b f=0) :=
  BSAWardTransport.transportSource
    (wardTransportSystem _ h b (vermaBSAWeight N t) f h0 h1 h2) t N N

/-- BSA transport kills both positive Ward defects on the terminal output
at the generic (1,N) curve. This is a conditional covariance theorem, not
a statement that the output or its vacuum image is nonzero. -/
theorem wardBSATerminal_positive (h b t : ℂ) (N : ℕ) (ht : t≠0) (hN : 3≤N)
    (f : ℂ → wardSequenceSpace (vermaBSACharge t) h)
    (h0 : wardWeight (vermaBSACharge t) h f=vermaBSAWeight N t • f)
    (h1 : wardP (vermaBSACharge t) h b f=0) (h2 : wardQ (vermaBSACharge t) h b f=0) :
    wardP (vermaBSACharge t) h b (wardBSATerminal h b t N f h0 h1 h2)=0 ∧
    wardQ (vermaBSACharge t) h b (wardBSATerminal h b t N f h0 h1 h2)=0 := by
  constructor
  · exact BSAWardTransport.transportSource_L1_terminal t N
      (wardTransportSystem _ h b (vermaBSAWeight N t) f h0 h1 h2) ht (by omega)
  · exact BSAWardTransport.transportSource_L2_terminal t N
      (wardTransportSystem _ h b (vermaBSAWeight N t) f h0 h1 h2) ht hN

/-- Every transported terminal output has the expected field weight a+N.
This uses the actual weight operator, independently of nonvanishing. -/
theorem wardBSATerminal_weight (h b t : ℂ) (N : ℕ)
    (f : ℂ → wardSequenceSpace (vermaBSACharge t) h)
    (h0 : wardWeight (vermaBSACharge t) h f=vermaBSAWeight N t • f)
    (h1 : wardP (vermaBSACharge t) h b f=0) (h2 : wardQ (vermaBSACharge t) h b f=0) :
    wardWeight (vermaBSACharge t) h (wardBSATerminal h b t N f h0 h1 h2)=
      (vermaBSAWeight N t+(N:ℂ)) • wardBSATerminal h b t N f h0 h1 h2 :=
  BSAWardTransport.transportSource_L0
    (wardTransportSystem _ h b (vermaBSAWeight N t) f h0 h1 h2) t N N
    (fun j => BSAWardTransport.transportState_L0
      (wardTransportSystem _ h b (vermaBSAWeight N t) f h0 h1 h2) t N j)
end VOA.InverseDS.VirasoroVerma
