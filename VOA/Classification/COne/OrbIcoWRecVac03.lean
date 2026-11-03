import VOA.Classification.COne.OrbIcoWRecVac02
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
namespace VOA.Classification.COne.OrbIcoW
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac13_jet_recurrence : JetRecurrence false 13 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac13_jet_pivot : JetPivot false 13 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac14_jet_recurrence : JetRecurrence false 14 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac14_jet_pivot : JetPivot false 14 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac15_jet_recurrence : JetRecurrence false 15 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac15_jet_pivot : JetPivot false 15 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac16_jet_recurrence : JetRecurrence false 16 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac16_jet_pivot : JetPivot false 16 := by decide +kernel
end VOA.Classification.COne.OrbIcoW
