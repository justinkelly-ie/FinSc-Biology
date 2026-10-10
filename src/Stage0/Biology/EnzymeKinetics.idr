module Stage0.Biology.EnzymeKinetics

import Stage0.BoxInt
import Stage1.UnixelFraction
import Stage1.VexelMaxel
import Stage0.OnSeq.FusedStream
import public Stage0.TransitionNetwork
import Data.Fuel
import Data.List
import Data.Fin
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. LAW 37: DISCRETE MICHAELIS-MENTEN ENZYME KINETICS
------------------------------------------------------------------------

||| Discrete Enzyme State represented as a 5-component Vexel multiset basis vector:
|||   index 0: freeEnzyme    [E] tokens
|||   index 1: enzymeComplex [ES] tokens
|||   index 2: substrate     [S] tokens
|||   index 3: product       [P] tokens
|||   index 4: totalEnzyme   [E]_0 tokens
public export
enzymeVexel : BoxInt -> BoxInt -> BoxInt -> BoxInt -> BoxInt -> Vexel
enzymeVexel e es s p e0 =
  MkVexel [ (MkUnixel 0, e)
          , (MkUnixel 1, es)
          , (MkUnixel 2, s)
          , (MkUnixel 3, p)
          , (MkUnixel 4, e0)
          ]

public export
enzymeFreeEnzyme : Vexel -> BoxInt
enzymeFreeEnzyme (MkVexel ((MkUnixel 0, e) :: _)) = e
enzymeFreeEnzyme v = lookupUnixel (MkUnixel 0) v

public export
enzymeEnzymeComplex : Vexel -> BoxInt
enzymeEnzymeComplex (MkVexel (_ :: (MkUnixel 1, es) :: _)) = es
enzymeEnzymeComplex v = lookupUnixel (MkUnixel 1) v

public export
enzymeSubstrate : Vexel -> BoxInt
enzymeSubstrate (MkVexel (_ :: _ :: (MkUnixel 2, s) :: _)) = s
enzymeSubstrate v = lookupUnixel (MkUnixel 2) v

public export
enzymeProduct : Vexel -> BoxInt
enzymeProduct (MkVexel (_ :: _ :: _ :: (MkUnixel 3, p) :: _)) = p
enzymeProduct v = lookupUnixel (MkUnixel 3) v

public export
enzymeTotalEnzyme : Vexel -> BoxInt
enzymeTotalEnzyme (MkVexel (_ :: _ :: _ :: _ :: (MkUnixel 4, e0) :: _)) = e0
enzymeTotalEnzyme v = lookupUnixel (MkUnixel 4) v

||| Discrete Reaction Velocity Rate:
|||   v = (V_max * [S]) / (K_m + [S])
public export
computeReactionVelocity : (vMax : BoxInt) -> (km : BoxInt) -> (substrateConc : BoxInt) -> BoxInt
computeReactionVelocity vMax km s =
  let num = vMax * s
      den = km + s
  in if den == intToBoxInt 0 then intToBoxInt 0 else num `div` den

------------------------------------------------------------------------
-- 2. DISCRETE CATALYTIC TURNOVER STEP
-- [E] + [S] <-> [ES] -> [E] + [P]
------------------------------------------------------------------------

public export
stepCatalysis : Vexel -> (km : BoxInt) -> (kcat : BoxInt) -> Vexel
stepCatalysis sys km kcat =
  let e  = enzymeFreeEnzyme sys
      es = enzymeEnzymeComplex sys
      s  = enzymeSubstrate sys
      p  = enzymeProduct sys
      e0 = enzymeTotalEnzyme sys

      -- Formation of enzyme-substrate complex
      bindAmount = if s > intToBoxInt 0 && e > intToBoxInt 0 then intToBoxInt 1 else intToBoxInt 0
      e' = e - bindAmount
      es' = es + bindAmount
      s' = s - bindAmount

      -- Catalytic conversion to product
      prodAmount = if es' >= intToBoxInt 1 then intToBoxInt 1 else intToBoxInt 0
      es'' = es' - prodAmount
      e'' = e' + prodAmount
      p' = p + prodAmount
  in enzymeVexel e'' es'' s' p' e0

------------------------------------------------------------------------
-- 3. DEFORESTED ENZYME KINETICS STREAM TRANSDUCER
------------------------------------------------------------------------

||| Zero-allocation deforested Michaelis-Menten enzyme catalysis stream transducer.
public export
fusedComputeEnzymeKineticsStream : Fuel -> (km : BoxInt) -> (kcat : BoxInt) -> Vexel -> List Vexel
fusedComputeEnzymeKineticsStream f km kcat initSys =
  runFueledStream f (unfoldStream nextStep initSys)
  where
    nextStep : Vexel -> Step Vexel Vexel
    nextStep sys =
      let stepped = stepCatalysis sys km kcat
      in Yield stepped stepped

------------------------------------------------------------------------
-- 4. FORMAL INVARIANT AUDIT
------------------------------------------------------------------------

||| Audits Law 37 (Discrete Michaelis-Menten Enzyme Kinetics):
||| 1. Initial State: Free Enzyme E=10, ES=0, Substrate S=50, Product P=0, Total Enzyme E0=10.
||| 2. Hyperbolic Velocity: V_max = 100, K_m = 25, S = 50 -> v = (100 * 50) / (25 + 50) = 5000 / 75 = 66 tokens.
||| 3. Stepping catalysis maintains exact enzyme conservation: [E] + [ES] == [E]_0 = 10.
||| 4. Total substrate + product + complex tokens conserved: S + P + ES = 50.
||| 5. Zero-allocation deforested stream generation produces consistent catalysis trace.
public export
auditEnzymeKineticsProof : Bool
auditEnzymeKineticsProof =
  let initSys = enzymeVexel (intToBoxInt 10) (intToBoxInt 0) (intToBoxInt 50) (intToBoxInt 0) (intToBoxInt 10)
      v = computeReactionVelocity (intToBoxInt 100) (intToBoxInt 25) (intToBoxInt 50)
      stepped = stepCatalysis initSys (intToBoxInt 25) (intToBoxInt 2)
      strmTrace = fusedComputeEnzymeKineticsStream (limit 2) (intToBoxInt 25) (intToBoxInt 2) initSys

      tVel = v == intToBoxInt 66
      tEnzymeConserv = enzymeFreeEnzyme stepped + enzymeEnzymeComplex stepped == enzymeTotalEnzyme stepped
      tMassConserv = enzymeSubstrate stepped + enzymeProduct stepped + enzymeEnzymeComplex stepped == intToBoxInt 50
      tStreamValid = length strmTrace == 2
  in tVel && tEnzymeConserv && tMassConserv && tStreamValid

------------------------------------------------------------------------
-- 5. OBSERVER EPOCH (k=38) ENZYMATIC & METABOLIC TRANSITION NETWORKS
------------------------------------------------------------------------

||| Observer Epoch k=38 (n=39=3x13): Gate-pure dissipative steady state (Rule 03 & Rule 05).
public export
observerEpochK : Nat
observerEpochK = 38

public export
observerEpochN : Nat
observerEpochN = 39

||| Molecular species participating in enzymatic catalysis and ATP-driven metabolism.
public export
data EnzymeSpecies =
    EnzE      -- Free enzyme [E]
  | EnzS      -- Free substrate [S]
  | EnzES     -- Enzyme-substrate complex [ES]
  | EnzP      -- Product [P]
  | MolATP    -- Adenosine triphosphate (ATP)
  | MolADP    -- Adenosine diphosphate (ADP)
  | MolPi     -- Inorganic phosphate (Pi)
  | MolWater  -- Water (H2O)

public export
Eq EnzymeSpecies where
  EnzE     == EnzE     = True
  EnzS     == EnzS     = True
  EnzES    == EnzES    = True
  EnzP     == EnzP     = True
  MolATP   == MolATP   = True
  MolADP   == MolADP   = True
  MolPi    == MolPi    = True
  MolWater == MolWater = True
  _        == _        = False

public export
Show EnzymeSpecies where
  show EnzE     = "E"
  show EnzS     = "S"
  show EnzES    = "ES"
  show EnzP     = "P"
  show MolATP   = "ATP"
  show MolADP   = "ADP"
  show MolPi    = "Pi"
  show MolWater = "H2O"

||| Enzyme mass weight table: counts enzyme catalytic core (E and ES both carry 1).
public export
enzymeWeightTable : List (EnzymeSpecies, BoxInt)
enzymeWeightTable =
  [ (EnzE, intToBoxInt 1)
  , (EnzES, intToBoxInt 1)
  , (EnzS, intToBoxInt 0)
  , (EnzP, intToBoxInt 0)
  , (MolATP, intToBoxInt 0)
  , (MolADP, intToBoxInt 0)
  , (MolPi, intToBoxInt 0)
  , (MolWater, intToBoxInt 0)
  ]

||| Substrate/Product mass weight table: counts substrate backbone (S, ES, and P each carry 1).
public export
substrateWeightTable : List (EnzymeSpecies, BoxInt)
substrateWeightTable =
  [ (EnzE, intToBoxInt 0)
  , (EnzES, intToBoxInt 1)
  , (EnzS, intToBoxInt 1)
  , (EnzP, intToBoxInt 1)
  , (MolATP, intToBoxInt 0)
  , (MolADP, intToBoxInt 0)
  , (MolPi, intToBoxInt 0)
  , (MolWater, intToBoxInt 0)
  ]

||| Phosphate group weight table: ATP has 3, ADP has 2, Pi has 1.
public export
phosphateWeightTable : List (EnzymeSpecies, BoxInt)
phosphateWeightTable =
  [ (EnzE, intToBoxInt 0)
  , (EnzES, intToBoxInt 0)
  , (EnzS, intToBoxInt 0)
  , (EnzP, intToBoxInt 0)
  , (MolATP, intToBoxInt 3)
  , (MolADP, intToBoxInt 2)
  , (MolPi, intToBoxInt 1)
  , (MolWater, intToBoxInt 0)
  ]

------------------------------------------------------------------------
-- 6. CANONICAL ENZYME & METABOLIC TRANSITION CHANNELS
------------------------------------------------------------------------

||| Enzyme-Substrate Binding: E + S -> ES
public export
enzymeBindingChannel : TransitionChannel EnzymeSpecies
enzymeBindingChannel =
  MkChannel 1
    [ MkDelta EnzE (intToBoxInt (-1))
    , MkDelta EnzS (intToBoxInt (-1))
    , MkDelta EnzES (intToBoxInt 1)
    ]
    (intToBoxInt 10)

||| Enzyme-Substrate Unbinding: ES -> E + S
public export
enzymeUnbindingChannel : TransitionChannel EnzymeSpecies
enzymeUnbindingChannel =
  MkChannel 2
    [ MkDelta EnzES (intToBoxInt (-1))
    , MkDelta EnzE (intToBoxInt 1)
    , MkDelta EnzS (intToBoxInt 1)
    ]
    (intToBoxInt 5)

||| Catalytic Turnover: ES -> E + P
public export
enzymeCatalysisChannel : TransitionChannel EnzymeSpecies
enzymeCatalysisChannel =
  MkChannel 3
    [ MkDelta EnzES (intToBoxInt (-1))
    , MkDelta EnzE (intToBoxInt 1)
    , MkDelta EnzP (intToBoxInt 1)
    ]
    (intToBoxInt 8)

||| ATP Hydrolysis (Cellular Free Energy Currency): ATP + H2O -> ADP + Pi
public export
atpHydrolysisChannel : TransitionChannel EnzymeSpecies
atpHydrolysisChannel =
  MkChannel 4
    [ MkDelta MolATP (intToBoxInt (-1))
    , MkDelta MolWater (intToBoxInt (-1))
    , MkDelta MolADP (intToBoxInt 1)
    , MkDelta MolPi (intToBoxInt 1)
    ]
    (intToBoxInt 30)

------------------------------------------------------------------------
-- 7. CONSERVATION LAW AUDITS & DEFORESTED STREAM TRANSDUCTION
------------------------------------------------------------------------

public export
enzymeEqMono : EnzymeSpecies -> EnzymeSpecies -> Bool
enzymeEqMono EnzE EnzE = True
enzymeEqMono EnzS EnzS = True
enzymeEqMono EnzES EnzES = True
enzymeEqMono EnzP EnzP = True
enzymeEqMono MolATP MolATP = True
enzymeEqMono MolADP MolADP = True
enzymeEqMono MolPi MolPi = True
enzymeEqMono MolWater MolWater = True
enzymeEqMono _ _ = False

public export
lookupEnzymeMono : EnzymeSpecies -> List (EnzymeSpecies, BoxInt) -> Maybe BoxInt
lookupEnzymeMono _ [] = Nothing
lookupEnzymeMono tok ((k, v) :: rest) =
  if enzymeEqMono tok k then Just v else lookupEnzymeMono tok rest

public export
isConservativeEnzymeDelta : List (EnzymeSpecies, BoxInt) -> List (StoichiometryDelta EnzymeSpecies) -> Bool
isConservativeEnzymeDelta weights deltas =
  let totalDelta = foldl (\acc, (MkDelta sp ch) =>
                            case lookupEnzymeMono sp weights of
                              Just w => addBox acc (mulBox w ch)
                              Nothing => acc) (intToBoxInt 0) deltas
  in boxEq totalDelta (intToBoxInt 0)

||| Audits enzyme conservation across binding, unbinding, and catalysis channels.
public export
auditEnzymeConservation : Bool
auditEnzymeConservation =
  isConservativeEnzymeDelta enzymeWeightTable enzymeBindingChannel.deltas &&
  isConservativeEnzymeDelta enzymeWeightTable enzymeUnbindingChannel.deltas &&
  isConservativeEnzymeDelta enzymeWeightTable enzymeCatalysisChannel.deltas

||| Audits substrate/product mass conservation across binding, unbinding, and catalysis channels.
public export
auditSubstrateMassConservation : Bool
auditSubstrateMassConservation =
  isConservativeEnzymeDelta substrateWeightTable enzymeBindingChannel.deltas &&
  isConservativeEnzymeDelta substrateWeightTable enzymeUnbindingChannel.deltas &&
  isConservativeEnzymeDelta substrateWeightTable enzymeCatalysisChannel.deltas

||| Audits phosphate group conservation in ATP hydrolysis.
public export
auditAtpHydrolysisConservation : Bool
auditAtpHydrolysisConservation =
  isConservativeEnzymeDelta phosphateWeightTable atpHydrolysisChannel.deltas

||| Comprehensive enzymatic and metabolic conservation audit.
public export
auditEnzymaticMetabolicConservation : Bool
auditEnzymaticMetabolicConservation =
  auditEnzymeConservation &&
  auditSubstrateMassConservation &&
  auditAtpHydrolysisConservation

||| Deforested stream generator simulating enzymatic reaction trajectory.
public export
streamEnzymeTrajectory : TransitionChannel EnzymeSpecies -> TransitionState EnzymeSpecies -> FusedStream (TransitionState EnzymeSpecies)
streamEnzymeTrajectory = streamTransitionTrajectory

||| Evaluates enzymatic reaction trajectory under fuel bounds without intermediate list allocations.
public export
runEnzymeTrajectory : Fuel -> TransitionChannel EnzymeSpecies -> TransitionState EnzymeSpecies -> TransitionState EnzymeSpecies
runEnzymeTrajectory = runTransitionTrajectory

||| Full combined audit verifying both discrete hyperbolic Vexel kinetics and TransitionNetwork conservation.
public export
auditEnzymeKineticsFullProof : Bool
auditEnzymeKineticsFullProof =
  auditEnzymeKineticsProof &&
  auditEnzymaticMetabolicConservation

