import VOA.Classification.COne.OrbIcoWRecVac03
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
namespace VOA.Classification.COne.OrbIcoW
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac17_jet_recurrence : JetRecurrence false 17 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac17_jet_pivot : JetPivot false 17 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac18_jet_recurrence : JetRecurrence false 18 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac18_jet_pivot : JetPivot false 18 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac19_jet_recurrence : JetRecurrence false 19 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac19_jet_pivot : JetPivot false 19 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Exact truncated convolution, including resonant cancellation.
theorem vac20_jet_recurrence : JetRecurrence false 20 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Constant pivot, or first-order pivot at a certified simple resonance.
theorem vac20_jet_pivot : JetPivot false 20 := by decide +kernel
end VOA.Classification.COne.OrbIcoW
