module Main where

import Data.Foldable

import qualified TPTP
import Formula

-- returns (formula, max function symbol id)
parseTPTP :: FilePath -> IO Formula
parseTPTP file = do
    (phi, _) <- parse file
    return phi
    where
     parse = TPTP.parseFile $ TPTP.FormulaStruct {
          TPTP.tMinSymbol = Formula.tMinSymbol
        , TPTP.tVar = \_ i -> tvar i
        , TPTP.tFun = \s i args -> tfun (Symbol s i) args
        , TPTP.tPred = \s i args -> Atom (Symbol s i, args)
        , TPTP.tEqual = fEqual
        , TPTP.tTrue = fTop
        , TPTP.tFalse = fBottom
        , TPTP.tNeg = (`Impl` fBottom)
        , TPTP.tImpl = Impl
        , TPTP.tAssume = flip (foldr' Impl)
        , TPTP.tAnd = And
        , TPTP.tOr = Or
        , TPTP.tAll = flip (foldr' Forall)
        , TPTP.tEx = flip (foldr' Exists)
     }

main :: IO ()
main = do
     s <- getLine
     print (read s :: Formula)
     main
