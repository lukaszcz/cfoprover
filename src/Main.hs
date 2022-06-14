module Main where

import Data.Foldable

import qualified TPTP
import Formula

-- returns (formula, max function symbol id)
parseTPTP :: FilePath -> IO (Formula, Int)
parseTPTP file = do
    (phi, s) <- parse file
    return (phi, TPTP.predsNum s)
    where
     parse = TPTP.parseFile $ TPTP.FormulaStruct {
          TPTP.tVar = \_ i -> tvar i
        , TPTP.tFun = \s i args -> tfun (Symbol s i) args
        , TPTP.tPred = \s i args -> Atom (Symbol s i, args)
        , TPTP.tEqual = \x y -> Atom (Symbol "=" 0, [x, y])
        , TPTP.tTrue = Impl (Atom (Symbol "False" 1, [])) (Atom (Symbol "False" 1, []))
        , TPTP.tFalse = Atom (Symbol "False" 1, [])
        , TPTP.tNeg = \x -> Impl x (Atom (Symbol "False" 1, []))
        , TPTP.tImpl = Impl
        , TPTP.tAssume = flip (foldr' Impl)
        , TPTP.tAnd = And
        , TPTP.tOr = Or
        , TPTP.tAll = flip (foldr' Forall)
        , TPTP.tEx = flip (foldr' Exists)
     }

main :: IO ()
main = putStrLn "CProver"
