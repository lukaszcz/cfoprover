{-# LANGUAGE DeriveTraversable, FlexibleInstances, UnicodeSyntax #-}
module Formula where

import Data.Functor
import Data.Char
import Data.List as List
import Data.List.Extras.Pair
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap

import Control.Monad
import Control.Monad.State
import Control.Unification
import Control.Unification.IntVar

{------------------------------------}
{- Terms & formulas -}

data Symbol = Symbol { sname :: String, sid :: Int }

instance Eq Symbol where
    s1 == s2 = sid s1 == sid s2

-- terms and formulas use 0-based de-Bruijn indices
data TermF t = Var Int | Fun Symbol [t] deriving (Eq, Functor, Foldable, Traversable)

instance Unifiable TermF where
    zipMatch (Var x) (Var y)
        | x == y = Just $ Var x
    zipMatch (Fun f1 args1) (Fun f2 args2)
        | f1 == f2 = fmap (Fun f1) (pairWith (curry Right) args1 args2)
    zipMatch _ _ = Nothing

type Term = UTerm TermF IntVar

varOccurs :: Int -> Term -> Bool
varOccurs n (UTerm (Var m)) = n == m
varOccurs n (UTerm (Fun _ args)) = any (varOccurs n) args
varOccurs _ _ = False

instance Eq Term where
    UVar v1 == UVar v2 = v1 == v2
    UTerm t1 == UTerm t2 = t1 == t2
    _ == _ = False

tvar :: Int -> Term
tvar x = UTerm $ Var x

tfun :: Symbol -> [Term] -> Term
tfun f args = UTerm $ Fun f args

type Atom = (Symbol, [Term])

data Formula = Atom Atom
            | Impl Formula Formula
            | And Formula Formula
            | Or Formula Formula
            | Forall String Formula
            | Exists String Formula

mapAtoms' :: (Int -> [String] -> Atom -> Atom) -> Int -> [String] -> Formula -> Formula
mapAtoms' f n env (Atom a) = Atom (f n env a)
mapAtoms' f n env (Impl x y) = Impl (mapAtoms' f n env x) (mapAtoms' f n env y)
mapAtoms' f n env (And x y) = And (mapAtoms' f n env x) (mapAtoms' f n env y)
mapAtoms' f n env (Or x y) = Or (mapAtoms' f n env x) (mapAtoms' f n env y)
mapAtoms' f n env (Forall s x) = Forall s (mapAtoms' f (n + 1) (s:env) x)
mapAtoms' f n env (Exists s x) = Exists s (mapAtoms' f (n + 1) (s:env) x)

mapAtoms :: (Int -> [String] -> Atom -> Atom) -> Formula -> Formula
mapAtoms f = mapAtoms' f 0 []

{----------------------------------------------------------------------------}
{- standard symbols & formulas -}

sBottom :: Symbol
sBottom = Symbol "False" 0

aBottom :: Atom
aBottom = (sBottom, [])

fBottom :: Formula
fBottom = Atom aBottom

sTop :: Symbol
sTop = Symbol "True" 1

aTop :: Atom
aTop = (sTop, [])

fTop :: Formula
fTop = Atom aTop

sEquality :: Symbol
sEquality = Symbol "=" 2

aEqual :: Term -> Term -> Atom
aEqual t1 t2 = (sEquality, [t1, t2])

fEqual :: Term -> Term -> Formula
fEqual t1 t2 = Atom (aEqual t1 t2)

tMinSymbol :: Int
tMinSymbol = 3

{------------------------------------------------------------------}
{- substitution -}

class Substitutable a where
    -- nsubst n env t -> substitute variable with index (x + n) by (env !! x)
    nsubst :: Int -> [Term] -> a -> a

subst :: Substitutable a => [Term] -> a -> a
subst [] x = x
subst env x = nsubst 0 env x

class Abstractable a where
    -- nabstract n f t -> change function f into variable n
    nabstract :: Int -> Symbol -> a -> a

abstract :: Abstractable a => Symbol -> a -> a
abstract = nabstract 0

instance Substitutable Term where
    nsubst n env (UTerm (Var x)) | x >= n = env !! (x - n)
    nsubst n env (UTerm (Fun f args)) = UTerm $ Fun f (map (nsubst n env) args)
    nsubst _ _ t = t

instance Abstractable Term where
    nabstract n s (UTerm (Fun f [])) | f == s = UTerm (Var n)
    nabstract n s (UTerm (Fun f args)) = UTerm (Fun f (map (nabstract n s) args))
    nabstract _ _ t = t

instance Substitutable Atom where
    nsubst n env (s, args) = (s, map (nsubst n env) args)

instance Abstractable Atom where
    nabstract n s (s', args) = (s', map (nabstract n s) args)

instance Substitutable Formula where
    nsubst n env = mapAtoms (\m _ -> nsubst (n + m) env)

instance Abstractable Formula where
    nabstract n s = mapAtoms (\m _ -> nabstract (n + m) s)

instance Eq Formula where
    (Atom (s1, args1)) == (Atom (s2, args2)) = s1 == s2 && args1 == args2
    (Impl a1 b1) == (Impl a2 b2) = a1 == a2 && b1 == b2
    (And a1 b1) == (And a2 b2) = a1 == a2 && b1 == b2
    (Or a1 b1) == (Or a2 b2) = a1 == a2 && b1 == b2
    (Forall _ a1) == (Forall _ a2) = a1 == a2
    (Exists _ a1) == (Exists _ a2) = a1 == a2
    _ == _ = False

{-------------------------------------------------------------------}
{- show & read formulas -}

showsTerm :: Term -> ShowS
showsTerm (UVar v) = showString "?" . shows (getVarID v)
showsTerm (UTerm (Var x)) = showString "_?v" . shows x
showsTerm (UTerm (Fun s args)) = showString (sname s) . sargs
    where
        sargs =
            if null args then
                id
            else
                showChar '(' .
                foldl (\a x -> a . showString "," . showsTerm x) (showsTerm (head args)) (tail args) .
                showChar ')'

showTerm :: Term -> String
showTerm t = showsTerm t ""

showsFormula :: [String] -> Int -> Formula -> ShowS
showsFormula env _ (Atom (s, args)) =
    showsTerm (UTerm (Fun s (map (subst (map (\x -> tfun (Symbol x 0) []) env)) args)))
showsFormula env p (Impl a b) = showParen (p > impl_prec) $
    showsFormula env (impl_prec+1) a . showString " → " .
    showsFormula env impl_prec b
    where impl_prec = 5
showsFormula env p (And a b) = showParen (p > and_prec) $
    showsFormula env (and_prec+1) a . showString " ∧ " .
    showsFormula env (and_prec+1) b
    where and_prec = 6
showsFormula env p (Or a b) = showParen (p > or_prec) $
    showsFormula env (or_prec+1) a . showString " ∨ " .
    showsFormula env (or_prec+1) b
    where or_prec = 6
showsFormula env p (Forall s a) = showParen (p > forall_prec) $
    showString "∀" . showString s . showsFormula (s:env) forall_prec a
    where forall_prec = 7
showsFormula env p (Exists s a) = showParen (p > exists_prec) $
    showString "∃" . showString s . showsFormula (s:env) exists_prec a
    where exists_prec = 7

instance Show Formula where
    showsPrec = showsFormula []

readError :: String -> String -> a
readError msg s = error $ msg ++ ": " ++ take 10 s ++ " (...)"

data ReadState = ReadState { rSyms :: HashMap String Int, rSymId :: Int }

newSymbol :: String -> State ReadState Symbol
newSymbol s = do
    rs <- get
    let id = rSymId rs
    put rs{ rSyms = HashMap.insert s id (rSyms rs), rSymId = id + 1 }
    return $ Symbol s id

getSymbol :: String -> State ReadState Symbol
getSymbol s = do
    rs <- get
    case HashMap.lookup s (rSyms rs) of
        Just id -> return $ Symbol s id
        Nothing -> newSymbol s

skipWhitespace :: String -> String
skipWhitespace (c:s) | isSpace c = skipWhitespace s
skipWhitespace s = s

readLexeme :: String -> Maybe (String, String)
readLexeme s =
    case skipWhitespace s of
        '&':s' -> Just ("and", s')
        '|':s' -> Just ("or", s')
        '/':'\\':s' -> Just ("and", s')
        '\\':'/':s' -> Just ("or", s')
        '-':'>':s' -> Just ("->", s')
        '∧':s' -> Just ("and", s')
        '∨':s' -> Just ("or", s')
        '→':s' -> Just ("->", s')
        '∀':s' -> Just ("forall", s')
        '∃':s' -> Just ("exists", s')
        s'@(c:_) | isAlpha c -> Just $ readIdent s'
        c:s' -> Just ([c],s')
        _ -> Nothing
    where
        readIdent (c:s) | isAlphaNum c || c == '_' =
            let (s1,s2) = readIdent s in
            (c:s1,s2)
        readIdent s = ("",s)

readTerm :: String -> State ReadState (Term, String)
readTerm s =
    case readLexeme s of
        Just (sf,s') -> do
            sym <- getSymbol sf
            (args, s'') <- readArgs readTerm s'
            return (UTerm (Fun sym args), s'')
        _ -> readError "expected a term" s

readArgs :: (String -> State ReadState (a, String)) -> String -> State ReadState ([a], String)
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
                    return (t:ts, s3)
                Just (")", s2) -> return ([t], s2)
                _ -> readError "expected ')'" s0

readAtom :: String -> State ReadState (Formula, String)
readAtom s =
    case readLexeme s of
        Just ("(",s') -> do
            (r,s'') <- readFormula s'
            case readLexeme s'' of
                Just (")",s3) -> return (r, s3)
                _ -> readError "expected ')'" s''
        Just ("false",s') -> return (fBottom, s')
        Just (sf,s') -> do
            sym <- getSymbol sf
            (args, s'') <- readArgs readTerm s'
            return (Atom (sym, args), s'')
        _ -> readError "expected an atom" s

readQuantifier :: String -> State ReadState (Formula, String)
readQuantifier s =
    case readLexeme s of
        Just ("forall",s1) -> go Forall s1
        Just ("exists",s1) -> go Exists s1
        _ -> readAtom s
    where
        go q s1 =
            case readLexeme s1 of
                Just (x,s2) -> do
                    sym <- newSymbol x
                    case readLexeme s2 of
                        Just (".",s3) -> do
                            (r,s4) <- readFormula s3
                            return (q x (abstract sym r), s4)
                        _ -> do
                            (r,s3) <- readQuantifier s2
                            return (q x (abstract sym r), s3)
                _ -> readError "expected variable name" s1

readConjunction :: String -> State ReadState (Formula, String)
readConjunction s = do
    (a1, s1) <- readQuantifier s
    case readLexeme s1 of
        Just ("and",s2) -> do
            (a2,s3) <- readConjunction s2
            return (And a1 a2, s3)
        _ -> return (a1, s1)

readDisjunction :: String -> State ReadState (Formula, String)
readDisjunction s = do
    (a1, s1) <- readConjunction s
    case readLexeme s1 of
        Just ("or",s2) -> do
            (a2,s3) <- readDisjunction s2
            return (Or a1 a2, s3)
        _ -> return (a1, s1)

readImplication :: String -> State ReadState (Formula, String)
readImplication s = do
    (a1, s1) <- readDisjunction s
    case readLexeme s1 of
        Just ("->",s2) -> do
            (a2,s3) <- readImplication s2
            return (Impl a1 a2, s3)
        _ -> return (a1, s1)

readFormula :: String -> State ReadState (Formula, String)
readFormula = readImplication

instance Read Formula where
    readsPrec _ s = [evalState (readFormula s) (ReadState HashMap.empty tMinSymbol)]

{-------------------------------------------------------------------}
{- proof terms -}

data Idx = ILeft | IRight
data Elim p = EApp p | EAApp Term | EProj Idx

instance Substitutable a => Substitutable (Elim a) where
    nsubst n env (EApp x) = EApp (nsubst n env x)
    nsubst n env (EAApp t) = EAApp (nsubst n env t)
    nsubst _ _ e@(EProj _) = e

class Proof p where
    mkVar :: Symbol -> p
    mkLam :: Symbol -> Formula -> p -> p
    mkApp :: p -> p -> p
    mkConj :: p -> p -> p
    mkProj :: Idx -> p -> p
    mkInj :: Idx -> Formula -> p -> p
    mkCase :: p -> p -> p -> p
    mkALam :: Symbol -> p -> p
    mkAApp :: p -> Term -> p
    mkExIntro :: Formula -> Term -> p -> p
    mkExElim :: p -> p -> p
    mkElim :: Symbol -> [Elim p] -> p
    mkElim s elims = mk (mkVar s) elims
        where
          mk p [] = p
          mk p (EApp p' : es) = mk (mkApp p p') es
          mk p (EAApp t : es) = mk (mkAApp p t) es
          mk p (EProj i : es) = mk (mkProj i p) es
    applyTermBindings :: Monad m => (Term -> m Term) -> p -> m p

instance Proof () where
    mkVar _ = ()
    mkLam _ _ _ = ()
    mkApp _ _ = ()
    mkConj _ _ = ()
    mkProj _ _ = ()
    mkInj _ _ _ = ()
    mkCase _ _ _ = ()
    mkALam _ _ = ()
    mkAApp _ _ = ()
    mkExIntro _ _ _ = ()
    mkExElim _ _ = ()
    mkElim _ _ = ()
    applyTermBindings _ _ = return ()

data PTerm = PVar Symbol
           | Lambda Symbol Formula PTerm
           | App PTerm PTerm
           | Conj PTerm PTerm
           | Proj Idx PTerm
           | Inj Idx Formula PTerm -- Inj ILeft a t :: a
           | Case PTerm PTerm PTerm
           | ALambda Symbol PTerm
           | AApp PTerm Term
           | ExIntro Formula Term PTerm -- ExIntro a tt t :: a
           | ExElim PTerm PTerm

mapTerms :: Monad m => (Term -> m Term) -> PTerm -> m PTerm
mapTerms _ x@(PVar _) = return x
mapTerms f (Lambda s phi x) = mapTerms f x <&> Lambda s phi
mapTerms f (App x y) = do
    x' <- mapTerms f x
    y' <- mapTerms f y
    return $ App x' y'
mapTerms f (Conj x y) = do
    x' <- mapTerms f x
    y' <- mapTerms f y
    return $ Conj x' y'
mapTerms f (Proj idx x) = mapTerms f x <&> Proj idx
mapTerms f (Inj idx phi x) = mapTerms f x <&> Inj idx phi
mapTerms f (Case x y z) =  do
    x' <- mapTerms f x
    y' <- mapTerms f y
    z' <- mapTerms f z
    return $ Case x' y' z'
mapTerms f (ALambda s x) = mapTerms f x <&> ALambda s
mapTerms f (AApp x t) = do
    x' <- mapTerms f x
    t' <- f t
    return $ AApp x' t'
mapTerms f (ExIntro phi t x) =  do
    x' <- mapTerms f x
    t' <- f t
    return $ ExIntro phi t' x'
mapTerms f (ExElim x y) =  do
    x' <- mapTerms f x
    y' <- mapTerms f y
    return $ ExElim x' y'

instance Proof PTerm where
    mkVar = PVar
    mkLam = Lambda
    mkApp = App
    mkConj = Conj
    mkProj = Proj
    mkInj = Inj
    mkCase = Case
    mkALam = ALambda
    mkAApp = AApp
    mkExIntro = ExIntro
    mkExElim = ExElim
    applyTermBindings = mapTerms

instance Show PTerm where
    showsPrec _ (PVar s) = showString (sname s)
    showsPrec d (Lambda s phi p) = showParen (d > lambda_prec) $
        showString "λ" . showString (sname s) . showString " : " . shows phi .
        showString " . " . showsPrec lambda_prec p
        where lambda_prec = 0
    showsPrec d (App p1 p2) = showParen (d > app_prec) $
        showsPrec app_prec p1 . showString " " . showsPrec (app_prec + 1) p2
        where app_prec = 5
    showsPrec _ (Conj p1 p2) =
        showString "(" . showsPrec app_prec p1 . showString ", " .
        showsPrec app_prec p2 . showString ")"
        where app_prec = 5
    showsPrec d (Proj idx p) = showParen (d > app_prec) $
        showString (case idx of ILeft -> "π1 "; IRight -> "π2 ") .
        showsPrec (app_prec + 1) p
        where app_prec = 5
    showsPrec d (Inj idx _ p) = showParen (d > app_prec) $
        showString (case idx of ILeft -> "in1 "; IRight -> "in2 ") .
        showsPrec (app_prec + 1) p
        where app_prec = 5
    showsPrec d (Case p p1 p2) = showParen (d > lambda_prec) $
        showString "case " . showsPrec app_prec p . showString " of " .
        showsPrec lambda_prec p1 . showString " | " . showsPrec lambda_prec p2
        where app_prec = 5
              lambda_prec = 0
    showsPrec d (ALambda s p) = showParen (d > lambda_prec) $
        showString "Λ" . showString (sname s) .
        showString " . " . showsPrec lambda_prec p
        where lambda_prec = 0
    showsPrec d (AApp p t) = showParen (d > app_prec) $
        showsPrec app_prec p . showString " " . showsTerm t
        where app_prec = 5
    showsPrec _ (ExIntro _ t p) =
        showString "[" . showsTerm t . showString ", " .
        showsPrec lambda_prec p . showString "]"
        where lambda_prec = 0
    showsPrec d (ExElim p1 p2) = showParen (d > lambda_prec) $
        showString "let " . showsPrec app_prec p1 . showString " be " .
        showsPrec lambda_prec p2
        where app_prec = 5
              lambda_prec = 0

{------------------------------------}
{- Proof checking -}

infer' :: [(Symbol, Formula)] -> PTerm -> Maybe Formula
infer' env (PVar s) = List.lookup s env
infer' env (Lambda s a t) = do
    b <- infer' ((s,a):env) t
    return $ Impl a b
infer' env (App t1 t2) = do
    a <- infer' env t1
    case a of
      Impl a1 a2 -> do
          b <- infer' env t2
          guard $ b == a1
          return a2
      _ -> Nothing
infer' env (Conj t1 t2) = do
    a <- infer' env t1
    b <- infer' env t2
    return (And a b)
infer' env (Proj i t) = do
    a <- infer' env t
    case a of
        And a1 a2 -> case i of
          ILeft -> return a1
          IRight -> return a2
        _ -> Nothing
infer' env (Inj i a t) = do
    b <- infer' env t
    case i of
      ILeft -> return (Or b a)
      IRight -> return (Or a b)
infer' env (Case t0 t1 t2) = do
    a <- infer' env t0
    case a of
        Or a1 a2 -> do
            b1 <- infer' env t1
            b2 <- infer' env t2
            case (b1, b2) of
                (Impl a1' b1', Impl a2' b2')
                    | a1 == a1' && a2 == a2' && b1' == b2' -> return b1'
                _ -> Nothing
        _ -> Nothing
infer' env (ALambda s t) = do
    a <- infer' env t
    return (Forall (sname s) (abstract s a))
infer' env (AApp t tt) = do
    a <- infer' env t
    case a of
        Forall _ a' -> return $ subst [tt] a'
        _ -> Nothing
infer' env (ExIntro a0@(Exists _ a) tt t) = do
    a' <- infer' env t
    guard $ subst [tt] a == a'
    return a0
infer' _ ExIntro {} = Nothing
infer' env (ExElim t t') = do
    a <- infer' env t
    case a of
        Exists _ a' -> do
            b <- infer' env t'
            case b of
                Forall _ (Impl b1 b2) | b1 == a' -> return b2
                _ -> Nothing
        _ -> Nothing

infer :: PTerm -> Maybe Formula
infer = infer' []

check :: PTerm -> Formula -> Bool
check t a = case infer t of
  Nothing -> False
  Just a' -> a == a'

{------------------------------------}
{- Optimized formula representation -}

data CElims =
      Elims Int [Elim PFormula]
    | ECase Int [Elim PFormula] Idx Formula [Eliminator] Formula [Eliminator] CElims
    | EEx Int [Elim PFormula] Formula [Eliminator] CElims

data Eliminator = Eliminator {
      target :: Atom
    , elims :: CElims
    , bindersNum :: Int
    , cost :: Int
    }

data PFormula = PAtom Atom
              | PImpl (Formula, [Eliminator]) PFormula
              | PAnd PFormula PFormula
              | POr Formula PFormula PFormula
              | PForall String PFormula
              | PExists String Formula PFormula

instance Substitutable CElims where
    nsubst n env (Elims k es) = Elims k (map (nsubst n env) es)
    nsubst n env (ECase k es i a eas b ebs cs) =
        ECase k (map (nsubst n env) es) i
            (nsubst (n + k) env a) (map (nsubst (n + k) env) eas)
            (nsubst (n + k) env b) (map (nsubst (n + k) env) ebs)
            (nsubst (n + k) env cs)
    nsubst n env (EEx k es a eas cs) =
        EEx k (map (nsubst n env) es)
            (nsubst (n + k + 1) env a)
            (map (nsubst (n + k + 1) env) eas)
            (nsubst (n + k + 1) env cs)

instance Substitutable Eliminator where
    nsubst n env e = e{ target = nsubst n env (target e)
                      , elims = nsubst n env (elims e) }

instance Substitutable PFormula where
    nsubst n env (PAtom a) = PAtom $ nsubst n env a
    nsubst n env (PImpl (phi, elims) a) =
        PImpl (nsubst n env phi, map (nsubst n env) elims) (nsubst n env a)
    nsubst n env (PAnd a b) = PAnd (nsubst n env a) (nsubst n env b)
    nsubst n env (POr phi a b) = POr (nsubst n env phi) (nsubst n env a) (nsubst n env b)
    nsubst n env (PForall s a) = PForall s (nsubst (n + 1) env a)
    nsubst n env (PExists s phi a) = PExists s (nsubst n env phi) (nsubst (n + 1) env a)

shift :: Substitutable t => Int -> t -> t
shift 0 = id
shift k = subst (map (\n -> tvar (n + k)) [0,1..])

prependElim :: Elim PFormula -> CElims -> CElims
prependElim e (Elims k es) = Elims k (shift k e : es)
prependElim e (ECase k es idx a1 es1 a2 es2 elims) = ECase k (shift k e : es) idx a1 es1 a2 es2 elims
prependElim e (EEx k es a eas elims) = EEx k (shift k e : es) a eas elims

prependForallElim :: CElims -> CElims
prependForallElim (Elims k es) = Elims (k + 1) (EAApp (tvar 0) : es)
prependForallElim (ECase k es idx a1 es1 a2 es2 elims) = ECase (k + 1) (EAApp (tvar 0) : es) idx a1 es1 a2 es2 elims
prependForallElim (EEx k es a eas elims) = EEx (k + 1) (EAApp (tvar 0) : es) a eas elims

compileFormula :: Formula -> PFormula
compileFormula (Atom a) = PAtom a
compileFormula (Impl a b) = PImpl (a, compileElims a) (compileFormula b)
compileFormula (And a b) = PAnd (compileFormula a) (compileFormula b)
compileFormula phi@(Or a b) = POr phi (compileFormula a) (compileFormula b)
compileFormula (Forall s a) = PForall s (compileFormula a)
compileFormula (Exists s a) = PExists s a (compileFormula a)

compileElims :: Formula -> [Eliminator]
compileElims (Atom a) = [Eliminator {target = a, elims = Elims 0 [], bindersNum = 0, cost = 0}]
compileElims (Impl a b) =
    map (\e -> e{
          elims = prependElim (EApp (compileFormula a)) (elims e)
        , cost = cost e + 10 })
        (compileElims b)
compileElims (And a b) =
    map (\e -> e{elims = prependElim (EProj ILeft) (elims e)}) (compileElims a) ++
    map (\e -> e{elims = prependElim (EProj IRight) (elims e)}) (compileElims b)
compileElims (Or a b) =
    map (\e -> e{ elims = ECase 0 [] ILeft a eas b ebs (elims e)
                , cost = cost e + 10 }) eas ++
    map (\e -> e{ elims = ECase 0 [] IRight b ebs a eas (elims e)
                , cost = cost e + 10 }) ebs
    where
        eas = compileElims a
        ebs = compileElims b
compileElims (Forall _ a) =
    map (\e -> e{ elims = prependForallElim (elims e)
                , bindersNum = bindersNum e + 1
                , cost = cost e +
                    if any (varOccurs (bindersNum e)) (snd (target e)) then 1 else 5 })
        (compileElims a)
compileElims (Exists _ a) =
    map (\e -> e{elims = EEx 0 [] a eas (elims e), bindersNum = bindersNum e + 1}) eas
    where
        eas = compileElims a
