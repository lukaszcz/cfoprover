module Main where

import Options.Applicative.Simple
import System.IO
import System.TimeIt

import qualified TPTP
import qualified Search
import Formula

tptpSig :: TPTP.FormulaSig Term Formula
tptpSig = TPTP.FormulaStruct {
          TPTP.tMinSymbol = Formula.tMinSymbol
        , TPTP.tVar = \_ i -> tvar i
        , TPTP.tFun = \s i args -> tfun (Symbol s i) args
        , TPTP.tPred = \s i args -> Atom (Symbol s i, args)
        , TPTP.tEqual = fEqual
        , TPTP.tTrue = fTop
        , TPTP.tFalse = fBottom
        , TPTP.tNeg = (`Impl` fBottom)
        , TPTP.tImpl = Impl
        , TPTP.tAssume = flip (foldr Impl)
        , TPTP.tAnd = And
        , TPTP.tOr = Or
        , TPTP.tAll = flip (foldr Forall)
        , TPTP.tEx = flip (foldr Exists)
     }

-- returns (formula, max function symbol id)
parseTPTPFile :: FilePath -> IO Formula
parseTPTPFile file = do
  (phi, _) <- TPTP.parseFile tptpSig file
  return phi

parseTPTP :: String -> IO Formula
parseTPTP s = do
  (phi, _) <- TPTP.parse tptpSig s
  return phi

data Options = Options
  { tptp :: Bool
  , interactive :: Bool
  , produceProof :: Bool
  , fileName :: String
  }

doSearch :: Options -> Formula -> IO ()
doSearch opts phi = timeIt $ do
  if produceProof opts then
    print (go 2 :: PTerm)
  else
    (go 2 :: ()) `seq` putStrLn "success"
  where
    sig = createSignature phi
    go n =
      case Search.search sig n phi of
        [] -> go (n + 1)
        x:_ -> x

repl :: Options -> IO ()
repl opts = do
  putStr "> "
  hFlush stdout
  done <- isEOF
  if done then
    return ()
  else do
    s <- getLine
    phi <- if tptp opts then parseTPTP s else return $ read s
    doSearch opts phi
    repl opts

batch :: Options -> IO ()
batch opts = do
  phi <-
    if fileName opts == "" then do
      s <- getContents
      if tptp opts then parseTPTP s else return $ read s
    else
      if tptp opts then
        parseTPTPFile (fileName opts)
      else do
        s <- readFile (fileName opts)
        return $ read s
  doSearch opts phi

main :: IO ()
main = do
  (opts,()) <- simpleOptions "0.1"
                            "cprover"
                            "An experimental connection-driven prover for first-order logic"
                            (Options <$>
                            switch (long "tptp") <*>
                            switch (short 'i' <> long "interactive") <*>
                            switch (short 'p' <> long "proof") <*>
                            argument str (metavar "FILE" <> value ""))
                            empty
  if interactive opts then
    repl opts
  else
    batch opts
