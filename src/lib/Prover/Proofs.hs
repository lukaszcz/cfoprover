module Prover.Proofs where

import Control.Monad
import qualified Data.List as List
import Prover.Types

data Idx = ILeft | IRight

data Elim p = EApp p | EAApp Term | EProj Idx

instance Substitutable a => Substitutable (Elim a) where
  nsubst n env (EApp x) = EApp (nsubst n env x)
  nsubst n env (EAApp t) = EAApp (nsubst n env t)
  nsubst _ _ e@(EProj _) = e

class Show p => Proof p where
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
  mkExfalso :: Formula -> p -> p
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
  mkExfalso _ _ = ()
  mkElim _ _ = ()
  applyTermBindings _ _ = return ()

data PTerm
  = PVar Symbol
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
  | Exfalso Formula PTerm

mapTerms :: Monad m => (Term -> m Term) -> PTerm -> m PTerm
mapTerms _ x@(PVar _) = pure x
mapTerms f (Lambda s phi x) = Lambda s <$> mapTermsInFormula f phi <*> mapTerms f x
mapTerms f (App x y) = App <$> mapTerms f x <*> mapTerms f y
mapTerms f (Conj x y) = Conj <$> mapTerms f x <*> mapTerms f y
mapTerms f (Proj idx x) = Proj idx <$> mapTerms f x
mapTerms f (Inj idx phi x) = Inj idx <$> mapTermsInFormula f phi <*> mapTerms f x
mapTerms f (Case x y z) = Case <$> mapTerms f x <*> mapTerms f y <*> mapTerms f z
mapTerms f (ALambda s x) = ALambda s <$> mapTerms f x
mapTerms f (AApp x t) = AApp <$> mapTerms f x <*> f t
mapTerms f (ExIntro phi t x) = ExIntro <$> mapTermsInFormula f phi <*> f t <*> mapTerms f x
mapTerms f (ExElim x y) = ExElim <$> mapTerms f x <*> mapTerms f y
mapTerms f (Exfalso phi x) = Exfalso <$> mapTermsInFormula f phi <*> mapTerms f x

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
  mkExfalso = Exfalso
  applyTermBindings = mapTerms

instance Show PTerm where
  showsPrec _ (PVar s) = shows s
  showsPrec d (Lambda s phi p) =
    showParen (d > lambda_prec) $
      showString "λ" . shows s . showString " : " . shows phi
        . showString " . "
        . showsPrec lambda_prec p
    where
      lambda_prec = 0
  showsPrec d (App p1 p2) =
    showParen (d > app_prec) $
      showsPrec app_prec p1 . showString " " . showsPrec (app_prec + 1) p2
    where
      app_prec = 5
  showsPrec _ (Conj p1 p2) =
    showString "(" . showsPrec app_prec p1 . showString ", "
      . showsPrec app_prec p2
      . showString ")"
    where
      app_prec = 5
  showsPrec d (Proj idx p) =
    showParen (d > app_prec) $
      showString (case idx of ILeft -> "π1 "; IRight -> "π2 ")
        . showsPrec (app_prec + 1) p
    where
      app_prec = 5
  showsPrec d (Inj idx _ p) =
    showParen (d > app_prec) $
      showString (case idx of ILeft -> "in1 "; IRight -> "in2 ")
        . showsPrec (app_prec + 1) p
    where
      app_prec = 5
  showsPrec d (Case p p1 p2) =
    showParen (d > lambda_prec) $
      showString "case " . showsPrec (app_prec + 1) p . showString " { "
        . showsPrec lambda_prec p1
        . showString " | "
        . showsPrec lambda_prec p2
        . showString " }"
    where
      app_prec = 5
      lambda_prec = 0
  showsPrec d (ALambda s p) =
    showParen (d > lambda_prec) $
      showString "Λ" . shows s
        . showString " . "
        . showsPrec lambda_prec p
    where
      lambda_prec = 0
  showsPrec d (AApp p t) =
    showParen (d > app_prec) $
      showsPrec app_prec p . showString " " . showsTerm t
    where
      app_prec = 5
  showsPrec _ (ExIntro _ t p) =
    showString "[" . showsTerm t . showString ", "
      . showsPrec lambda_prec p
      . showString "]"
    where
      lambda_prec = 0
  showsPrec d (ExElim p1 p2) =
    showParen (d > lambda_prec) $
      showString "let " . showsPrec app_prec p1 . showString " be "
        . showsPrec lambda_prec p2
    where
      app_prec = 5
      lambda_prec = 0
  showsPrec d (Exfalso _ p) =
    showParen (d > app_prec) $
      showString "exfalso " . showsPrec (app_prec + 1) p
    where
      app_prec = 5

{------------------------------------}
{- proof checking -}

infer' :: [(Symbol, Formula)] -> PTerm -> Maybe Formula
infer' env (PVar s) = List.lookup s env
infer' env (Lambda s a t) = do
  b <- infer' ((s, a) : env) t
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
    ILeft ->
      case a of
        Or b' _ | b == b' -> return a
        _ -> Nothing
    IRight ->
      case a of
        Or _ b' | b == b' -> return a
        _ -> Nothing
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
infer' env (ExIntro phi@(Exists _ a) tt t) = do
  a' <- infer' env t
  guard $ subst [tt] a == a'
  return phi
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
infer' env (Exfalso phi t) = do
  a <- infer' env t
  if a == fBottom then Just phi else Nothing

infer :: PTerm -> Maybe Formula
infer = infer' []

check :: PTerm -> Formula -> Bool
check t a = case infer t of
  Nothing -> False
  Just a' -> a == a'
