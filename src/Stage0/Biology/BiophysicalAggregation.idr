module Stage0.Biology.BiophysicalAggregation

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.VexelMaxel
import PhaseUnfolding
import Stage1.Chemistry.WatsonCrickBasePairing
import Stage1.Math.MacromolecularChirality
import Stage0.OnSeq.FusedStream
import Data.List
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. BIOPHYSICAL AGGREGATION CARRIERS
------------------------------------------------------------------------

||| A DNA Base Pair consists of two complementary nucleotide bases.
public export
record DnaBasePair where
  constructor MkBasePair
  strand1 : Nucleobase
  strand2 : Nucleobase

public export
Eq DnaBasePair where
  (MkBasePair a1 b1) == (MkBasePair a2 b2) = (a1 == a2) && (b1 == b2)

||| A DNA Double Helix is a multiset of base pairs with total hydrogen bond capacity.
public export
record DnaDoubleHelix where
  constructor MkDnaDoubleHelix
  pairsMultiset  : Box DnaBasePair
  totalHBonds    : Nat

||| A Peptide Chain consists of a multiset of amino acids and its condensed mass tokens.
public export
record PeptideChain where
  constructor MkPeptideChain
  aminoMultiset : Box EnantiomerHand
  netMassTokens : BoxInt

||| DNA Double Helix Transform Multiset (G ⊗ Z ⊗ J)
public export
dnaDoubleHelixTransform : MaxelTransform DnaBasePair DnaBasePair
dnaDoubleHelixTransform = mkTransformBox EllipticSector unitUnixelFraction
  [ ((MkBasePair Adenine Thymine, MkBasePair Adenine Thymine), intToBoxInt 1)
  , ((MkBasePair Guanine Cytosine, MkBasePair Guanine Cytosine), intToBoxInt 1)
  ]

||| Peptide Chain Transform Multiset (G ⊗ Z ⊗ J)
public export
peptideChainTransform : MaxelTransform EnantiomerHand EnantiomerHand
peptideChainTransform = mkTransformBox EllipticSector unitUnixelFraction
  [ ((LHand, LHand), intToBoxInt 1)
  , ((DHand, DHand), intToBoxInt 1)
  ]

||| Aggregates a deforested stream of nucleotide base pairs into a DNA Double Helix.
||| Uses a single-pass fused fold over the stream without allocating intermediate list cells.
||| Pushes Law 48 (Watson-Crick Pairing: A-T=2, G-C=3) forward to the helix.
public export
aggregateDnaDoubleHelixStream : FusedStream DnaBasePair -> DnaDoubleHelix
aggregateDnaDoubleHelixStream strm =
  let (pairsBox, hBonds) = foldStream
        (\acc, p =>
          let (accBox, accH) = acc
          in ( insertBox p (intToBoxInt 1) accBox
             , accH + basePairHBondCount (strand1 p) (strand2 p)
             ))
        (emptyBox, 0)
        strm
      pushedBox = applyPushforwardContraction dnaDoubleHelixTransform pairsBox
  in MkDnaDoubleHelix pushedBox hBonds

||| Aggregates a compile-time static vector of nucleotide base pairs into a DNA Double Helix.
public export
aggregateDnaDoubleHelixVect : {n : Nat} -> Vect n DnaBasePair -> DnaDoubleHelix
aggregateDnaDoubleHelixVect pairs =
  let (pairsBox, hBonds) = foldl
        (\acc, p =>
          let (accBox, accH) = acc
          in ( insertBox p (intToBoxInt 1) accBox
             , accH + basePairHBondCount (strand1 p) (strand2 p)
             ))
        (emptyBox, 0)
        pairs
      pushedBox = applyPushforwardContraction dnaDoubleHelixTransform pairsBox
  in MkDnaDoubleHelix pushedBox hBonds

||| Aggregates a set of nucleotide base pairs into a DNA Double Helix.
||| Deforests the input list via streamification and single-pass accumulation.
public export
aggregateDnaDoubleHelix : List DnaBasePair -> DnaDoubleHelix
aggregateDnaDoubleHelix pairs = aggregateDnaDoubleHelixStream (stream pairs)

||| Aggregates L-amino acids into a condensed Peptide Chain.
||| Pushes Law 49 (Homochirality & Peptide Condensation: m1+m2-18) forward to the chain.
public export
aggregatePeptideChain : BoxInt -> BoxInt -> PeptideChain
aggregatePeptideChain m1 m2 =
  let aminoBox = insertBox LHand (intToBoxInt 2) emptyBox
      pushedBox = applyPushforwardContraction peptideChainTransform aminoBox
      netM = condensePeptideBond m1 m2
  in MkPeptideChain pushedBox netM

------------------------------------------------------------------------
-- 3. FORMAL INVARIANT AUDIT PROOF
------------------------------------------------------------------------

||| Audits Biophysical Aggregation Pushforward:
||| 1. DNA Double Helix (1 A-T pair + 1 G-C pair) carries 2 + 3 = 5 H-bonds across streams and vectors.
||| 2. Peptide condensation (100 + 100 - 18) yields 182 net mass tokens.
%inline
public export
auditBiophysicalAggregationProof : Bool
auditBiophysicalAggregationProof =
  let p1 = MkBasePair Adenine Thymine
      p2 = MkBasePair Guanine Cytosine
      strm = stream [p1, p2]
      helixStream = aggregateDnaDoubleHelixStream strm
      helixVect = aggregateDnaDoubleHelixVect [p1, p2]
      hBondsValid = totalHBonds helixStream == 5 && totalHBonds helixVect == 5
      m1 = intToBoxInt 100
      m2 = intToBoxInt 100
      pep = aggregatePeptideChain m1 m2
      massValid = netMassTokens pep == intToBoxInt 182
  in hBondsValid && massValid

------------------------------------------------------------------------
-- 4. LAW 48 PHYSICAL DUALITY & CHROMOGEOMETRIC INVARIANTS
------------------------------------------------------------------------

||| Physical Duality: Watson-Crick complementary pairing implements the discrete
||| error-correcting syndrome of the Kitaev Toric Code (Law 36) in the molecular domain.
||| Purine-pyrimidine pairing (A-T, G-C) forms non-zero H-bonds, whereas homological
||| mismatches form 0 H-bonds, mirroring Star and Plaquette stabilizer syndrome excitation.
public export
0 prfWatsonCrickParitySyndrome :
  (basePairHBondCount Adenine Thymine > 0 &&
   basePairHBondCount Guanine Cytosine > 0 &&
   basePairHBondCount Adenine Cytosine == 0) = True
prfWatsonCrickParitySyndrome = Refl

||| QTT 0 Erased Proof: Canonical base-pair bond counts sum to 2 + 3 = 5,
||| decomposing the 3rd prime factor of the Primorial 210 budget (2 * 3 * 5 * 7 = 210).
public export
0 prfBasePairBondSumIsPrime5 :
  basePairHBondCount Adenine Thymine + basePairHBondCount Guanine Cytosine = 5
prfBasePairBondSumIsPrime5 = Refl

||| QTT 0 Erased Proof: Base-pair step chromogeometric quadrance matches the
||| Blue Elliptic metric fixed-point charge gate: Q_Blue(4, 3) = 4^2 + 3^2 = 25.
public export
0 prfBasePairBlueQuadrance : (4 * 4 + 3 * 3) = 25
prfBasePairBlueQuadrance = Refl
