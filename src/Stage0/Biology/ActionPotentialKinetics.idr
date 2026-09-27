module Stage0.Biology.ActionPotentialKinetics

import Stage0.BoxInt
import Stage1.UnixelFraction
import Stage0.OnSeq.FusedStream
import Data.Fuel
import Data.List
import Data.Fin
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. LAW 38: DISCRETE HODGKIN-HUXLEY ACTION POTENTIALS
------------------------------------------------------------------------

||| Discrete Membrane Potential and Gating State:
|||   membranePotential : V (mV) tokens (-70 resting, +30 peak)
|||   mGate : Sodium activation particle (0..100)
|||   hGate : Sodium inactivation particle (0..100)
|||   nGate : Potassium activation particle (0..100)
public export
record NeuronMembrane where
  constructor MkNeuron
  voltage : BoxInt
  mGate   : BoxInt
  hGate   : BoxInt
  nGate   : BoxInt

public export
Eq NeuronMembrane where
  (MkNeuron v1 m1 h1 n1) == (MkNeuron v2 m2 h2 n2) =
    v1 == v2 && m1 == m2 && h1 == h2 && n1 == n2

------------------------------------------------------------------------
-- 2. DISCRETE ACTION POTENTIAL STEPPING
------------------------------------------------------------------------

||| Evaluates discrete membrane depolarization and repolarization step:
public export
stepActionPotential : NeuronMembrane -> (injectedCurrent : BoxInt) -> NeuronMembrane
stepActionPotential (MkNeuron v m h n) inj =
  let -- Depolarization trigger when threshold (V >= -55) is exceeded
      depolarizing = v + inj >= intToBoxInt (-55)

      -- Fast sodium channel opening (m surges, h slowly closes)
      m' = if depolarizing then intToBoxInt 90 else intToBoxInt 10
      h' = if v >= intToBoxInt 0 then intToBoxInt 10 else intToBoxInt 80

      -- Delayed potassium rectifier opening (n opens at positive voltage)
      n' = if v >= intToBoxInt 0 then intToBoxInt 85 else intToBoxInt 20

      -- Net voltage update
      v' = if depolarizing && h' > intToBoxInt 50 then
             v + intToBoxInt 100 -- Rapid upstroke from -70 mV to +30 mV
           else if n' > intToBoxInt 50 then
             v - intToBoxInt 60 -- Delayed rectifier repolarization down to resting
           else
             v + inj
  in MkNeuron v' m' h' n'

------------------------------------------------------------------------
-- 3. FORMAL INVARIANT AUDIT
------------------------------------------------------------------------

||| Audits Law 38 (Discrete Hodgkin-Huxley Action Potential):
||| 1. Resting state: V = -70 mV.
||| 2. Threshold stimulus (+20 mV current) triggers depolarization upstroke (V > 0).
||| 3. Subsequent potassium rectifier surge repolarizes back towards resting potential.
public export
auditActionPotentialKineticsProof : Bool
auditActionPotentialKineticsProof =
  let resting = MkNeuron (intToBoxInt (-70)) (intToBoxInt 10) (intToBoxInt 80) (intToBoxInt 20)
      spike1 = stepActionPotential resting (intToBoxInt 20)
      spike2 = stepActionPotential spike1 (intToBoxInt 0)

      tSpikeUp = voltage spike1 > intToBoxInt 0
      tRepolarize = voltage spike2 < voltage spike1
  in tSpikeUp && tRepolarize

------------------------------------------------------------------------
-- 4. DEFORESTED ACTION POTENTIAL KINETIC STREAMS
------------------------------------------------------------------------

||| Zero-allocation action potential simulation accumulating total membrane voltage flux using fusedHylomorphism.
public export covering
fusedComputeMembraneVoltageFlux : Data.Fuel.Fuel -> NeuronMembrane -> List BoxInt -> BoxInt
fusedComputeMembraneVoltageFlux f initialNeuron currents =
  Stage0.OnSeq.FusedStream.fusedHylomorphism f
    (\(n, currs) => case currs of
                      [] => Done
                      inj :: rest =>
                        let n' = stepActionPotential n inj
                        in Yield (voltage n') (n', rest))
    (\v, acc => v + acc)
    (intToBoxInt 0)
    (initialNeuron, currents)
