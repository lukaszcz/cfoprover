module Prover.Parser(readFormula, Position, ReadError(..)) where

import Control.Monad.Except
import Control.Monad.State
import Control.Unification
import Data.Bifunctor
import Data.Char
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap

import Prover.Types

-- (line, char)
type Position = (Int, Int)
-- (position, remaining input)
type Input = (Position, String)

data ReadError = ReadError {rPosition :: Position, rMessage :: String}
data ReadState = ReadState {rSyms :: HashMap String Int, rSymId :: Int}

type ReadMonad a = ExceptT ReadError (State ReadState) a

readError :: String -> Input -> ReadMonad a
readError msg i = throwError $ ReadError (fst i) msg

newSymbol :: String -> ReadMonad Symbol
newSymbol s = do
  rs <- get
  let id = rSymId rs
  put rs {rSyms = HashMap.insert s id (rSyms rs), rSymId = id + 1}
  return $ Symbol s id

getSymbol :: String -> ReadMonad Symbol
getSymbol s = do
  rs <- get
  case HashMap.lookup s (rSyms rs) of
    Just id -> return $ Symbol s id
    Nothing -> newSymbol s

withNewSymbol :: String -> (Symbol -> ReadMonad a) -> ReadMonad a
withNewSymbol s f = do
  rs <- get
  let id = rSymId rs
  put rs {rSyms = HashMap.insert s id (rSyms rs), rSymId = id + 1}
  r <- f (Symbol s id)
  case HashMap.lookup s (rSyms rs) of
    Just id' -> state (\rs' -> ((), rs'{rSyms = HashMap.insert s id' (rSyms rs')}))
    Nothing -> return ()
  return r

skipWhitespace :: Input -> Input
skipWhitespace ((l, _), '\n' : s) = skipWhitespace ((l+1, 0), s)
skipWhitespace ((l, n), c : s) | isSpace c = skipWhitespace ((l, n+1), s)
skipWhitespace i = i

readLexeme :: Input -> Maybe (String, Input)
readLexeme s =
  let ((l,n),s1) = skipWhitespace s in
  case s1 of
    '&' : s' -> Just ("and", ((l,n+1),s'))
    '|' : s' -> Just ("or", ((l,n+1),s'))
    '/' : '\\' : s' -> Just ("and", ((l,n+2),s'))
    '\\' : '/' : s' -> Just ("or", ((l,n+2),s'))
    '-' : '>' : s' -> Just ("->", ((l,n+2),s'))
    '<' : '-' : '>' : s' -> Just ("<->", ((l,n+3),s'))
    '~' : s' -> Just ("not", ((l,n+1),s'))
    '⊥' : s' -> Just ("false", ((l,n+1),s'))
    '⊤' : s' -> Just ("true", ((l,n+1),s'))
    '∧' : s' -> Just ("and", ((l,n+1),s'))
    '∨' : s' -> Just ("or", ((l,n+1),s'))
    '→' : s' -> Just ("->", ((l,n+1),s'))
    '∀' : s' -> Just ("forall", ((l,n+1),s'))
    '∃' : s' -> Just ("exists", ((l,n+1),s'))
    s'@(c : _) | isAlpha c -> Just $ readIdent ((l,n),s')
    c : s' -> Just ([c], ((l,n+1),s'))
    _ -> Nothing
  where
    readIdent ((l,n),c:s)
      | isAlphaNum c || c == '_' || c == '-' || c == '\'' =
        let (s1, out) = readIdent ((l,n+1),s)
         in (c : s1, out)
    readIdent s = ("", s)

readTerm :: Input -> ReadMonad (Term, Input)
readTerm s =
  case readLexeme s of
    Just (sf, s') -> do
      sym <- getSymbol sf
      (args, s'') <- readArgs readTerm s'
      return (UTerm (Fun sym args), s'')
    _ -> readError "expected a term" s

readArgs :: (Input -> ReadMonad (a, Input)) -> Input -> ReadMonad ([a], Input)
readArgs f s =
  case readLexeme s of
    Just ("(", s1) -> go s1
    _ -> return ([], s)
  where
    go s0 = do
      (t, s1) <- f s0
      case readLexeme s1 of
        Just (",", s2) -> do
          (ts, s3) <- go s2
          return (t : ts, s3)
        Just (")", s2) -> return ([t], s2)
        _ -> readError "expected ')'" s0

readAtom :: Input -> ReadMonad (Formula, Input)
readAtom s =
  case readLexeme s of
    Just ("(", s') -> do
      (r, s'') <- readFormula' s'
      case readLexeme s'' of
        Just (")", s3) -> return (r, s3)
        _ -> readError "expected ')'" s''
    Just ("true", s') -> return (fTop, s')
    Just ("false", s') -> return (fBottom, s')
    Just (sf, s') -> do
      sym <- getSymbol sf
      (args, s'') <- readArgs readTerm s'
      return (Atomic (Atom sym args), s'')
    _ -> readError "expected an atom" s

readNegQuant :: Input -> ReadMonad (Formula, Input)
readNegQuant s =
  case readLexeme s of
    Just ("not", s1) -> do
      (r, s2) <- readNegQuant s1
      return (Impl r fBottom, s2)
    Just ("forall", s1) -> go Forall s1
    Just ("exists", s1) -> go Exists s1
    _ -> readAtom s
  where
    go q s1 =
      case readLexeme s1 of
        Just (x, s2) ->
          withNewSymbol x $ \sym -> do
            case readLexeme s2 of
              Just (".", s3) -> do
                (r, s4) <- readFormula' s3
                return (q x (abstract sym r), s4)
              _ -> do
                (r, s3) <- readNegQuant s2
                return (q x (abstract sym r), s3)
        _ -> readError "expected variable name" s1

readConjunction :: Input -> ReadMonad (Formula, Input)
readConjunction s = do
  (a1, s1) <- readNegQuant s
  case readLexeme s1 of
    Just ("and", s2) -> do
      (a2, s3) <- readConjunction s2
      return (And a1 a2, s3)
    _ -> return (a1, s1)

readDisjunction :: Input -> ReadMonad (Formula, Input)
readDisjunction s = do
  (a1, s1) <- readConjunction s
  case readLexeme s1 of
    Just ("or", s2) -> do
      (a2, s3) <- readDisjunction s2
      return (Or a1 a2, s3)
    _ -> return (a1, s1)

readImplication :: Input -> ReadMonad (Formula, Input)
readImplication s = do
  (a1, s1) <- readDisjunction s
  case readLexeme s1 of
    Just ("->", s2) -> do
      (a2, s3) <- readImplication s2
      return (Impl a1 a2, s3)
    _ -> return (a1, s1)

readEquivalence :: Input -> ReadMonad (Formula, Input)
readEquivalence s = do
  (a1, s1) <- readImplication s
  case readLexeme s1 of
    Just ("<->", s2) -> do
      (a2, s3) <- readEquivalence s2
      return (And (Impl a1 a2) (Impl a2 a1), s3)
    _ -> return (a1, s1)

readFormula' :: Input -> ReadMonad (Formula, Input)
readFormula' = readEquivalence

readFormula'' :: String -> Either ReadError (Formula, Input)
readFormula'' s =
  evalState (runExceptT $ readFormula' ((1,1),s)) (ReadState HashMap.empty tMinSymbol)

readFormula :: String -> Either ReadError Formula
readFormula s = case readFormula'' s of
                  Left e -> Left e
                  Right (_, (p, s)) | s /= "" -> Left $ ReadError p "input remaining"
                  Right (phi, _) -> Right phi

instance Read Formula where
  readsPrec _ s = case readFormula'' s of
                    Left e -> error $ show (rPosition e) ++ ": " ++ rMessage e
                    Right x -> [second snd x]
