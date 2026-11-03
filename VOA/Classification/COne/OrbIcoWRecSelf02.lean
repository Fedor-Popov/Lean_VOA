import VOA.Classification.COne.OrbIcoWRecSelf01
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
namespace VOA.Classification.COne.OrbIcoW
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem self09_jet_recurrence : JetRecurrence true 9 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem self09_jet_pivot : JetPivot true 9 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem self10_jet_recurrence : JetRecurrence true 10 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem self10_jet_pivot : JetPivot true 10 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem self11_jet_recurrence : JetRecurrence true 11 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem self11_jet_pivot : JetPivot true 11 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem self12_jet_recurrence : JetRecurrence true 12 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem self12_jet_pivot : JetPivot true 12 := by decide +kernel
end VOA.Classification.COne.OrbIcoW
