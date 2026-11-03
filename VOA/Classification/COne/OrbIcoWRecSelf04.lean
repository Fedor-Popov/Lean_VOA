import VOA.Classification.COne.OrbIcoWRecSelf03
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
namespace VOA.Classification.COne.OrbIcoW
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem self17_jet_recurrence : JetRecurrence true 17 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem self17_jet_pivot : JetPivot true 17 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem self18_jet_recurrence : JetRecurrence true 18 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem self18_jet_pivot : JetPivot true 18 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem self19_jet_recurrence : JetRecurrence true 19 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem self19_jet_pivot : JetPivot true 19 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem self20_jet_recurrence : JetRecurrence true 20 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem self20_jet_pivot : JetPivot true 20 := by decide +kernel
end VOA.Classification.COne.OrbIcoW
