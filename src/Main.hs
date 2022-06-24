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
  , measureTime :: Bool
  , fileName :: String
  }

doSearch :: Options -> Formula -> IO ()
doSearch opts phi = (if measureTime opts then timeIt else id) $ do
  if produceProof opts then
    case Search.searchIter sig phi :: [PTerm] of
      [] -> putStrLn "failure"
      x:_ -> print x
  else
    case Search.searchIter sig phi :: [()] of
      [] -> putStrLn "failure"
      _ -> putStrLn "success"
  where
    sig = createSignature phi

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
batch opts
  | tptp opts = do
    phi <-
      if fileName opts == "" then do
        getContents >>= parseTPTP
      else
        parseTPTPFile (fileName opts)
    doSearch opts phi
  | fileName opts == "" = go stdin
  | otherwise = withFile (fileName opts) ReadMode go
  where
    go h = do
      done <- hIsEOF h
      if done then
        return ()
      else do
        s <- hGetLine h
        doSearch opts (read s)
        go h

main :: IO ()
main = do
  (opts,()) <- simpleOptions "0.1"
                            "cfoprover"
                            "An experimental connection-driven prover for intuitionistic first-order logic"
                            (Options <$>
                            switch (long "tptp") <*>
                            switch (short 'i' <> long "interactive") <*>
                            switch (short 'p' <> long "proof") <*>
                            switch (short 't' <> long "time") <*>
                            argument str (metavar "FILE" <> value ""))
                            empty
  if interactive opts then
    repl opts
  else
    batch opts
