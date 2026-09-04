{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.FosterEquivalence (fosterPropEqCalc, parseFosterPropEq, FosterPropEq(..)) where

import Data.Char (toLower,toUpper)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.Util
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.Util.LanguageClasses

{-| An extended system for propositional logic extending ZachPropEq with
units and zeros (identity and domination laws) for conjunction and disjunction.
-}

data FosterPropEq = AndComm      | CommAnd 
                 | OrComm       | CommOr
                 | IffComm      | CommIff
                 | DNRep        | RepDN
                 | MCRep        | RepMC
                 | MCRep2       | RepMC2
                 | BiExRep      | RepBiEx
                 | AndAssoc     | AssocAnd
                 | OrAssoc      | AssocOr
                 | AndIdem      | IdemAnd
                 | OrIdem       | IdemOr
                 | OrDistL      | DistOrL
                 | OrDistR      | DistOrR
                 | AndDistL     | DistAndL
                 | AndDistR     | DistAndR
                 | AndAbsorb1   | AbsorbAnd1
                 | AndAbsorb2   | AbsorbAnd2
                 | AndAbsorb3   | AbsorbAnd3
                 | AndAbsorb4   | AbsorbAnd4
                 | OrAbsorb1    | AbsorbOr1
                 | OrAbsorb2    | AbsorbOr2
                 | OrAbsorb3    | AbsorbOr3
                 | OrAbsorb4    | AbsorbOr4
                 | NCRep        | RepNC
                 | DM1 | DM2 | DM3 | DM4
                 | AndUnit1 | AndUnit2 | RepAndUnit1 | RepAndUnit2
                 | OrUnit1  | OrUnit2  | RepOrUnit1  | RepOrUnit2
                 | AndZero1 | AndZero2 | RepAndZero1 | RepAndZero2
                 | OrZero1  | OrZero2  | RepOrZero1  | RepOrZero2
                 | NegTop | RepNegTop | NegBot | RepNegBot
                 | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
    deriving (Eq)

instance Show FosterPropEq where
        show AndComm = "Comm"
        show CommAnd = "Comm"
        show OrComm  = "Comm"
        show CommOr  = "Comm"
        show IffComm = "Comm"
        show CommIff = "Comm"
        show DNRep   = "DN"
        show RepDN   = "DN"
        show MCRep   = "Cond"
        show RepMC   = "Cond"
        show MCRep2  = "Cond"
        show RepMC2  = "Cond"
        show NCRep = "Cond"
        show RepNC = "Cond"
        show BiExRep = "Bicond"
        show RepBiEx = "Bicond"
        show DM1     = "DeM"
        show DM2     = "DeM"
        show DM3     = "DeM"
        show DM4     = "DeM"
        show AndAssoc = "Assoc"
        show AssocAnd = "Assoc"
        show OrAssoc  = "Assoc"
        show AssocOr = "Assoc"
        show AndIdem = "Id"
        show IdemAnd = "Id"
        show OrIdem = "Id"
        show IdemOr = "Id"
        show OrDistL = "Dist"
        show DistOrL = "Dist"
        show AndDistL = "Dist"
        show DistAndL = "Dist"
        show OrDistR = "Dist"
        show DistOrR = "Dist"
        show AndDistR = "Dist"
        show DistAndR = "Dist"
        show AndAbsorb1 = "Abs"
        show AbsorbAnd1 = "Abs"
        show AndAbsorb2 = "Abs"
        show AbsorbAnd2 = "Abs"
        show AndAbsorb3 = "Abs"
        show AbsorbAnd3 = "Abs"
        show AndAbsorb4 = "Abs"
        show AbsorbAnd4 = "Abs"
        show OrAbsorb1 = "Abs"
        show AbsorbOr1 = "Abs"
        show OrAbsorb2 = "Abs"
        show AbsorbOr2 = "Abs"
        show OrAbsorb3 = "Abs"
        show AbsorbOr3 = "Abs"
        show OrAbsorb4 = "Abs"
        show AbsorbOr4 = "Abs"
        show AndUnit1    = "Unit"
        show RepAndUnit1 = "Unit"
        show AndUnit2    = "Unit"
        show RepAndUnit2 = "Unit"
        show OrUnit1     = "Unit"
        show RepOrUnit1  = "Unit"
        show OrUnit2     = "Unit"
        show RepOrUnit2  = "Unit"
        show AndZero1    = "Zero"
        show RepAndZero1 = "Zero"
        show AndZero2    = "Zero"
        show RepAndZero2 = "Zero"
        show OrZero1     = "Zero"
        show RepOrZero1  = "Zero"
        show OrZero2     = "Zero"
        show RepOrZero2  = "Zero"
        show NegTop    = "Neg"
        show RepNegTop = "Neg"
        show NegBot    = "Neg"
        show RepNegBot = "Neg"
        show (Pr _) = "Pr"

instance Inference FosterPropEq PurePropLexicon (Form Bool) where
        ruleOf AndComm = andCommutativity !! 0
        ruleOf CommAnd = andCommutativity !! 1
        ruleOf OrComm = orCommutativity !! 0
        ruleOf CommOr = orCommutativity !! 1
        ruleOf IffComm = iffCommutativity !! 0 
        ruleOf CommIff = iffCommutativity !! 1
        ruleOf DNRep = doubleNegation !! 0
        ruleOf RepDN = doubleNegation !! 1
        ruleOf MCRep = materialConditional !! 0
        ruleOf RepMC = materialConditional !! 1
        ruleOf MCRep2 = materialConditional !! 2
        ruleOf RepMC2 = materialConditional !! 3
        ruleOf BiExRep = biconditionalExchange !! 0
        ruleOf AndAssoc = andAssociativity !! 0
        ruleOf AssocAnd = andAssociativity !! 1
        ruleOf OrAssoc = orAssociativity !! 0 
        ruleOf AssocOr = orAssociativity !! 1
        ruleOf AndIdem = andIdempotence !! 0
        ruleOf IdemAnd = andIdempotence !! 1
        ruleOf OrIdem = orIdempotence !! 0
        ruleOf IdemOr = orIdempotence !! 1
        ruleOf OrDistL = orDistributivity !! 0
        ruleOf DistOrL = orDistributivity !! 1
        ruleOf OrDistR = orDistributivity !! 2
        ruleOf DistOrR = orDistributivity !! 3
        ruleOf AndDistL = andDistributivity !! 0
        ruleOf DistAndL = andDistributivity !! 1
        ruleOf AndDistR = andDistributivity !! 2
        ruleOf DistAndR = andDistributivity !! 3
        ruleOf AndAbsorb1 = andAbsorption !! 0
        ruleOf AbsorbAnd1 = andAbsorption !! 1
        ruleOf AndAbsorb2 = andAbsorption !! 2
        ruleOf AbsorbAnd2 = andAbsorption !! 3
        ruleOf AndAbsorb3 = andAbsorption !! 4
        ruleOf AbsorbAnd3 = andAbsorption !! 5
        ruleOf AndAbsorb4 = andAbsorption !! 6
        ruleOf AbsorbAnd4 = andAbsorption !! 7
        ruleOf OrAbsorb1 = orAbsorption !! 0
        ruleOf AbsorbOr1 = orAbsorption !! 1
        ruleOf OrAbsorb2 = orAbsorption !! 2
        ruleOf AbsorbOr2 = orAbsorption !! 3
        ruleOf OrAbsorb3 = orAbsorption !! 4
        ruleOf AbsorbOr3 = orAbsorption !! 5
        ruleOf OrAbsorb4 = orAbsorption !! 6
        ruleOf AbsorbOr4 = orAbsorption !! 7
        ruleOf NCRep = negatedConditional !! 0
        ruleOf RepNC = negatedConditional !! 1
        ruleOf RepBiEx = biconditionalExchange !! 1
        ruleOf DM1 = deMorgansLaws !! 0
        ruleOf DM2 = deMorgansLaws !! 1
        ruleOf DM3 = deMorgansLaws !! 2
        ruleOf DM4 = deMorgansLaws !! 3
        ruleOf AndUnit1    = andUnit !! 0
        ruleOf RepAndUnit1 = andUnit !! 1
        ruleOf AndUnit2    = andUnit !! 2
        ruleOf RepAndUnit2 = andUnit !! 3
        ruleOf OrUnit1     = orUnit !! 0
        ruleOf RepOrUnit1  = orUnit !! 1
        ruleOf OrUnit2     = orUnit !! 2
        ruleOf RepOrUnit2  = orUnit !! 3
        ruleOf AndZero1    = andZero !! 0
        ruleOf RepAndZero1 = andZero !! 1
        ruleOf AndZero2    = andZero !! 2
        ruleOf RepAndZero2 = andZero !! 3
        ruleOf OrZero1     = orZero !! 0
        ruleOf RepOrZero1  = orZero !! 1
        ruleOf OrZero2     = orZero !! 2
        ruleOf RepOrZero2  = orZero !! 3
        ruleOf NegTop    = negatedConstants !! 0
        ruleOf RepNegTop = negatedConstants !! 1
        ruleOf NegBot    = negatedConstants !! 2
        ruleOf RepNegBot = negatedConstants !! 3
        ruleOf (Pr _) = axiom

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

        isPremise (Pr _) = True
        isPremise _ = False

parseFosterPropEq :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [FosterPropEq]
parseFosterPropEq rtc = do 
        r <- choice (map (try . caseInsensitiveString) ["Comm", "DN", "Cond", "Bicond", "DeM", "Assoc", "Abs", "Id", "Dist", "PR", "Unit", "Zero", "Neg"])
        return $ case map toLower r of
            "comm"-> [AndComm,CommAnd,OrComm,CommOr,IffComm,CommIff]
            "dn" -> [DNRep,RepDN]
            "cond" -> [MCRep,MCRep2,RepMC,RepMC2, NCRep, RepNC]
            "bicond" -> [BiExRep,RepBiEx]
            "assoc" -> [AndAssoc, AssocAnd, OrAssoc, AssocOr]
            "id" -> [AndIdem,IdemAnd,OrIdem,IdemOr]
            "abs" -> [AndAbsorb1,AbsorbAnd1,OrAbsorb1,AbsorbOr1
                     ,AndAbsorb2,AbsorbAnd2,OrAbsorb2,AbsorbOr2
                     ,AndAbsorb3,AbsorbAnd3,OrAbsorb3,AbsorbOr3
                     ,AndAbsorb4,AbsorbAnd4,OrAbsorb4,AbsorbOr4
                     ]
            "dist" -> [OrDistR, DistOrR, AndDistR, DistAndR, OrDistL,DistOrL,AndDistL,DistAndL]
            "dem" -> [DM1,DM2,DM3,DM4]
            "unit" -> [AndUnit1, RepAndUnit1, AndUnit2, RepAndUnit2, OrUnit1, RepOrUnit1, OrUnit2, RepOrUnit2]
            "zero"  -> [AndZero1, RepAndZero1, AndZero2, RepAndZero2, OrZero1, RepOrZero1, OrZero2, RepOrZero2]
            "neg"  -> [NegTop, RepNegTop, NegBot, RepNegBot]
            "pr" -> [Pr (problemPremises rtc)]
    where caseInsensitiveChar c = char (toLower c) <|> char (toUpper c)
          caseInsensitiveString s = try (mapM caseInsensitiveChar s) <?> "\"" ++ s ++ "\""

parseFosterPropEqProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine FosterPropEq PurePropLexicon (Form Bool)]
parseFosterPropEqProof rtc = toDeductionHilbertImplicit (parseFosterPropEq rtc) (purePropFormulaParser thomasBolducZachOpts)

fosterPropEqCalc = mkNDCalc 
    { ndRenderer = NoRender
    , ndParseProof = parseFosterPropEqProof
    , ndProcessLine = hoProcessLineHilbertImplicit
    , ndProcessLineMemo = Just hoProcessLineHilbertImplicitMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser thomasBolducZachOpts)
    , ndParseForm = (purePropFormulaParser thomasBolducZachOpts)
    , ndNotation = dropBotRight . dropOuterParens 
    }

dropBotRight s = case (break (== '⊢') s) of
      (a,"⊢ ⊥") -> a ++ "⊢ ?"
      _ -> s