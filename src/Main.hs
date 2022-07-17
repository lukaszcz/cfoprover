module Main where

import Options.Applicative.Simple
import Control.Monad
import System.IO
import System.TimeIt

import qualified TPTP
import qualified Search
import Types

tptpSig :: TPTP.FormulaSig Term Formula
tptpSig = TPTP.FormulaStruct {
          TPTP.tMinSymbol = Types.tMinSymbol
        , TPTP.tVar = \_ i -> tvar i
        , TPTP.tFun = \s i args -> tfun (Symbol s i) args
        , TPTP.tPred = \s i args -> Atomic (Atom (Symbol s i) args)
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

setEncoding :: Options -> Handle -> IO ()
setEncoding opts h =
  when (optEncoding opts /= "") $ do
    enc <- mkTextEncoding (optEncoding opts)
    hSetEncoding h enc

parseTPTP :: Handle -> IO (Either String Formula)
parseTPTP h = do
  r <- TPTP.parseHandle tptpSig h
  case r of
    Left e -> return $ Left e
    Right (phi, _) -> return $ Right phi

readTPTP :: String -> IO (Either String Formula)
readTPTP s = do
  r <- TPTP.parse tptpSig s
  case r of
    Left e -> return $ Left e
    Right (phi, _) -> return $ Right phi

data Options = Options
  { optVerbose :: Bool
  , optInteractive :: Bool
  , optProduceProof :: Bool
  , optMeasureTime :: Bool
  , optComplete :: Bool
  , optCheckType :: Bool
  , optTPTP :: Bool
  , optEncoding :: String
  , optFileName :: String
  }

createSearchOptions :: Options -> Search.Options
createSearchOptions opts = Search.defaultOptions {
  Search.optComplete = optComplete opts
}

doSearch :: Options -> Formula -> IO ()
doSearch opts phi = (if optMeasureTime opts then timeIt else id) $ do
  when (optVerbose opts) $
    putStrLn ("Proving: " ++ show phi)
  if optProduceProof opts || optCheckType opts then do
    r <- goSearch :: IO [PTerm]
    case r of
      [] -> putStrLn "failure"
      x:_ -> do
        if optProduceProof opts then print x else putStrLn "success"
        when (optCheckType opts && not (check x phi)) $
          putStrLn "typecheck failure"
  else do
    r <- goSearch :: IO [()]
    case r of
      [] -> putStrLn "failure"
      _ -> putStrLn "success"
  where
    sig = createSignature phi
    goSearch :: Proof p => IO [p]
    goSearch =
      if optVerbose opts then
        Search.searchIterVerbose (createSearchOptions opts) sig phi
      else
        return $ Search.searchIter (createSearchOptions opts) sig phi

repl :: Options -> IO ()
repl opts = do
  putStr "> "
  hFlush stdout
  done <- isEOF
  if done then
    return ()
  else do
    s <- getLine
    if optTPTP opts then do
      r <- readTPTP s
      case r of
        Left e -> putStrLn $ "parse error: " ++ e
        Right phi -> doSearch opts phi
    else
      case readFormula s of
        Left (ReadError pos e) -> putStrLn $ show (snd pos) ++ ": parse error: " ++ e
        Right phi -> doSearch opts phi
    repl opts

batch :: Options -> IO ()
batch opts
  | optTPTP opts = do
    r <-
      if optFileName opts == "" then do
        parseTPTPFile stdin
      else
        withFile (optFileName opts) ReadMode parseTPTPFile
    case r of
      Left e -> putStrLn $ "parse error: " ++ e
      Right phi -> doSearch opts phi
  | optFileName opts == "" = parseFile stdin
  | otherwise = withFile (optFileName opts) ReadMode parseFile
  where
    parseTPTPFile h = do
      setEncoding opts h
      parseTPTP h
    parseFile h = do
      setEncoding opts h
      go h 1
    go h ln = do
      done <- hIsEOF h
      if done then
        return ()
      else do
        s <- hGetLine h
        case readFormula s of
          Left (ReadError pos e) -> putStrLn $ show ln ++ ":" ++ show (snd pos) ++ ": parse error: " ++ e
          Right phi -> doSearch opts phi
        go h (ln + 1)

main :: IO ()
main = do
  (opts,()) <- simpleOptions "0.1"
                            "cfoProver"
                            "An experimental connection-driven prover for intuitionistic first-order logic."
                            (Options <$>
                            switch (short 'v' <> long "verbose") <*>
                            switch (short 'i' <> long "interactive") <*>
                            switch (short 'p' <> long "proof") <*>
                            switch (short 't' <> long "time") <*>
                            switch (short 'c' <> long "complete") <*>
                            switch (long "typecheck") <*>
                            switch (long "tptp") <*>
                            option str (short 'e' <> long "encoding" <> value "") <*>
                            argument str (metavar "FILE" <> value ""))
                            empty
  if optInteractive opts then
    repl opts
  else
    batch opts
