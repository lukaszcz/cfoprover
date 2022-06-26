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

parseTPTPFile :: FilePath -> IO (Either String Formula)
parseTPTPFile file = do
  r <- TPTP.parseFile tptpSig file
  case r of
    Left e -> return $ Left e
    Right (phi, _) -> return $ Right phi

parseTPTP :: String -> IO (Either String Formula)
parseTPTP s = do
  r <- TPTP.parse tptpSig s
  case r of
    Left e -> return $ Left e
    Right (phi, _) -> return $ Right phi

data Options = Options
  { tptp :: Bool
  , interactive :: Bool
  , produceProof :: Bool
  , measureTime :: Bool
  , complete :: Bool
  , fileName :: String
  }

createSearchOptions :: Options -> Search.Options
createSearchOptions opts = Search.defaultOptions {
  Search.optComplete = complete opts
}

doSearch :: Options -> Formula -> IO ()
doSearch opts phi = (if measureTime opts then timeIt else id) $ do
  if produceProof opts then
    case Search.searchIter (createSearchOptions opts) sig phi :: [PTerm] of
      [] -> putStrLn "failure"
      x:_ -> print x
  else
    case Search.searchIter Search.defaultOptions sig phi :: [()] of
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
    if tptp opts then do
      r <- parseTPTP s
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
  | tptp opts = do
    r <-
      if fileName opts == "" then do
        getContents >>= parseTPTP
      else
        parseTPTPFile (fileName opts)
    case r of
      Left e -> putStrLn $ "parse error: " ++ e
      Right phi -> doSearch opts phi
  | fileName opts == "" = go stdin 1
  | otherwise = withFile (fileName opts) ReadMode (`go` 1)
  where
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
                            "cfoprover"
                            "An experimental connection-driven prover for intuitionistic first-order logic"
                            (Options <$>
                            switch (long "tptp") <*>
                            switch (short 'i' <> long "interactive") <*>
                            switch (short 'p' <> long "proof") <*>
                            switch (short 't' <> long "time") <*>
                            switch (short 'c' <> long "complete") <*>
                            argument str (metavar "FILE" <> value ""))
                            empty
  if interactive opts then
    repl opts
  else
    batch opts
