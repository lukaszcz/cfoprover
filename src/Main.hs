module Main where

import Data.Foldable

import qualified TPTP
import Formula

parseTPTP :: FilePath -> IO Formula
parseTPTP file = do
    (phi, s) <- parse file
    return phi
    where
     parse = TPTP.parseFile $ TPTP.FormulaStruct {
          TPTP.tVar = \_ i -> tvar i
        , TPTP.tFun = \_ i args -> tfun i args
        , TPTP.tPred = \_ i args -> Atom (i, args)
        , TPTP.tEqual = \x y -> Atom (0, [x, y])
        , TPTP.tTrue = Impl (Atom (1, [])) (Atom (1, []))
        , TPTP.tFalse = Atom (1, [])
        , TPTP.tNeg = \x -> Impl x (Atom (1, []))
        , TPTP.tImpl = Impl
        , TPTP.tAssume = \ts x -> case ts of
                                    [] -> x
                                    t:ts' -> foldr' Impl t ts'
        , TPTP.tAnd = And
        , TPTP.tOr = Or
        , TPTP.tAll = \ss x -> Forall 0 x
        , TPTP.tEx = \ss x -> Exists 0 x
     }

main :: IO ()
main = putStrLn "CProver"
