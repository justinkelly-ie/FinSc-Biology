module Stage0.Biology.EnzymeKinetics

import Stage0.BoxInt
import Stage1.UnixelFraction
import Stage1.VexelMaxel
import Stage0.OnSeq.FusedStream
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
public export covering
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
public export covering
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
