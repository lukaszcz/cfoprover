{-|
  Conversion from the TPTP format
-}
module TPTP(parse, parseText, parseHandle, parseFile, FormulaSig(..), TPTPState(..)) where

import System.IO
import Control.Monad
import Control.Monad.State
import Data.Functor
import Data.Foldable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text,pack,unpack)
import qualified Data.Text.IO
import qualified Data.List.NonEmpty
import Data.TPTP.Parse.Text
import Data.TPTP

data FormulaSig a b = FormulaStruct {
      tMinSymbol :: Int
    , tVar :: String -> Int -> a
    , tFun :: String -> Int -> [a] -> a
    , tPred :: String -> Int -> [a] -> b
    , tEqual :: a -> a -> b
    , tTrue :: b
    , tFalse :: b
    , tNeg :: b -> b
    , tImpl :: b -> b -> b
    , tAssume :: [b] -> b -> b
    , tAnd :: b -> b -> b
    , tOr :: b -> b -> b
    , tAll :: [String] -> b -> b
    , tEx :: [String] -> b -> b
    }

-- | map names to identifier numbers
data TPTPState = TPTPState {
      symbolsNum :: Int
    , preds :: HashMap String Int
    , funs :: HashMap String Int
    }

parse :: FormulaSig a b -> String -> IO (b, TPTPState)
parse s = parseText s . pack

parseText :: FormulaSig a b -> Text -> IO (b, TPTPState)
parseText s = translate s . readTPTP

parseHandle :: FormulaSig a b -> Handle -> IO (b, TPTPState)
parseHandle s h = Data.Text.IO.hGetContents h >>= parseText s

parseFile :: FormulaSig a b -> FilePath -> IO (b, TPTPState)
parseFile s p = withFile p ReadMode (parseHandle s)

--------------------------------------------------------------------------------------

readTPTP :: Text -> [Unit]
readTPTP txt = case parseTPTPOnly txt of
                 Right tptp -> units tptp
                 Left s -> error ("cannot parse file: " ++ s)

translate :: FormulaSig a b -> [Unit] -> IO (b, TPTPState)
translate s units = do
  units' <- flattenUnits units
  let axioms = mapM (translateUnit s) (filter (not . isConj) units')
  let conjectures = mapM (translateUnit s) (filter isConj units')
  let result = do
        l1 <- axioms
        l2 <- conjectures
        case l2 of
          [] -> error "no conjectures found"
          h:t -> return (tAssume s l1 (foldl' (tAnd s) h t))
  return $ runTranslator (tMinSymbol s) result
    where
      isConj (Unit _ (Formula (Standard Conjecture) _) _) = True
      isConj _ = False

flattenUnits :: [Unit] -> IO [Unit]
flattenUnits l = mapM flattenUnit l <&> concat

flattenUnit :: Unit -> IO [Unit]
flattenUnit u@Unit {} = return [u]
flattenUnit (Include (Atom txt) Nothing) = withFile (unpack txt) ReadMode act
    where
      act = flattenUnits <=< (fmap readTPTP . Data.Text.IO.hGetContents)
flattenUnit (Include _ (Just _)) =
    error "unsupported include statement"

--------------------------------------------------------------------------------------

type Translator = State TPTPState

runTranslator :: Int -> Translator a -> (a, TPTPState)
runTranslator n tr = runState tr (TPTPState n HashMap.empty HashMap.empty)

getIdent :: Translator Int
getIdent = do
  s <- get
  let i = symbolsNum s
  put (s{symbolsNum = i + 1})
  return i

addPred :: String -> Translator Int
addPred name = do
  s <- get
  case HashMap.lookup name (preds s) of
    Just k -> return k
    Nothing -> do
      k <- getIdent
      put (s{preds = HashMap.insert name k (preds s)})
      return k

addFun :: String -> Translator Int
addFun name = do
  s <- get
  case HashMap.lookup name (funs s) of
    Just k -> return k
    Nothing -> do
      k <- getIdent
      put (s{funs = HashMap.insert name k (funs s)})
      return k

--------------------------------------------------------------------------------------

data Vars = Vars {
      varsNum :: Int
    , vars :: HashMap String Int
    }

translateUnit :: FormulaSig a b -> Unit -> Translator b
translateUnit s (Unit (Left (Atom _)) (Formula (Standard _) (FOF formula)) _) =
    translateFormula s (Vars 0 HashMap.empty) formula
translateUnit _ _ = error "unsupported declaration"

translateFormula :: FormulaSig a b -> Vars -> UnsortedFirstOrder -> Translator b
translateFormula s _ (Atomic (Predicate (Reserved (Standard Tautology)) _)) =
    return $ tTrue s
translateFormula s _ (Atomic (Predicate (Reserved (Standard Falsum)) _)) =
    return $ tFalse s
translateFormula s v (Atomic (Predicate (Defined (Atom txt)) args)) = do
  let name = unpack txt
  n <- addPred name
  translatePred s v name n args
translateFormula s v (Atomic (Equality left sign right)) = do
  l <- translateTerm s v left
  r <- translateTerm s v right
  if sign == Positive then
      return (tEqual s l r)
  else
      return (tNeg s (tEqual s l r))
translateFormula s v (Negated formula) = translateFormula s v formula <&> tNeg s
translateFormula s v (Connected left conn right) = translateConnective s v conn left right
translateFormula s v (Quantified quant nlst body) = do
  let vs = map fst (Data.List.NonEmpty.toList nlst)
  let vs' = map (\(Var txt) -> unpack txt) vs
  let q = case quant of
            Forall -> tAll s
            Exists -> tEx s
  let v' = Vars {
             varsNum = varsNum v + length vs
           , vars = foldr (uncurry HashMap.insert) (vars v) (zip vs' [varsNum v..])
           }
  b <- translateFormula s v' body
  return (q vs' b)
translateFormula _ _ _ = error "unsupported formula"

translateConnective :: FormulaSig a b -> Vars -> Connective ->
                       UnsortedFirstOrder -> UnsortedFirstOrder -> Translator b
translateConnective s v Conjunction left right = do
    l <- translateFormula s v left
    r <- translateFormula s v right
    return (tAnd s l r)
translateConnective s v Disjunction left right = do
    l <- translateFormula s v left
    r <- translateFormula s v right
    return (tOr s l r)
translateConnective s v Implication left right = do
    l <- translateFormula s v left
    r <- translateFormula s v right
    return (tImpl s l r)
translateConnective s v Equivalence left right = do
    l <- translateFormula s v left
    r <- translateFormula s v right
    return (tAnd s (tImpl s l r) (tImpl s r l))
translateConnective s v ExclusiveOr left right = do
    l <- translateFormula s v left
    r <- translateFormula s v right
    return (tAnd s (tOr s l r) (tNeg s (tAnd s r l)))
translateConnective s v NegatedConjunction left right = do
    l <- translateFormula s v left
    r <- translateFormula s v right
    return (tNeg s $ tAnd s l r)
translateConnective s v NegatedDisjunction left right = do
    l <- translateFormula s v left
    r <- translateFormula s v right
    return (tNeg s $ tOr s l r)
translateConnective s v ReversedImplication left right = do
    l <- translateFormula s v left
    r <- translateFormula s v right
    return (tImpl s r l)

translatePred :: FormulaSig a b -> Vars -> String -> Int -> [Term] -> Translator b
translatePred s v name n args = do
  as <- mapM (translateTerm s v) args
  return (tPred s name n as)

translateTerm :: FormulaSig a b -> Vars -> Term -> Translator a
translateTerm s v (Function (Defined (Atom txt)) args) = do
  let name = unpack txt
  n <- addFun name
  translateFunc s v name n args
translateTerm s v (Variable (Var txt)) =
    let name = unpack txt in
    case HashMap.lookup name (vars v) of
      Just n -> return (tVar s name n)
      Nothing -> error "ubound variable"
translateTerm _ _ _ = error "unsupported term"

translateFunc :: FormulaSig a b -> Vars -> String -> Int -> [Term] -> Translator a
translateFunc s v name n args = do
  as <- mapM (translateTerm s v) args
  return (tFun s name n as)
