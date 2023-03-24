{-# DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Extraction where

import Test.QuickCheck
import Control.Monad
import GHC.Generics

data NamedPattern = NVar String | NBot | NSym String | NImp NamedPattern NamedPattern | NApp NamedPattern NamedPattern | NExs String NamedPattern
  deriving (Eq, Show)

namedPrimitive :: NamedPattern -> Bool
namedPrimitive (NVar _) = True
namedPrimitive NBot = True
namedPrimitive (NSym _) = True
namedPrimitive _ = False

-- instance Show NamedPattern where
--   show (NVar s) = "V " ++ s ++ ""
--   show NBot = "⊥"
--   show (NSym s) = s
--   show (NImp ph1 ph2) = (if not $ namedPrimitive ph1 then "(" else "") ++ show ph1 ++ (if not $ namedPrimitive ph1 then ")" else "") ++ " → " ++ (if not $ namedPrimitive ph2 then "(" else "") ++ show ph2 ++ (if not $ namedPrimitive ph2 then ")" else "")
--   show (NApp ph1 ph2) = (if not $ namedPrimitive ph1 then "(" else "") ++ show ph1 ++ (if not $ namedPrimitive ph1 then ")" else "") ++ " $ " ++ (if not $ namedPrimitive ph2 then "(" else "") ++ show ph2 ++ (if not $ namedPrimitive ph2 then ")" else "")
--   show (NExs x ph) = "∃" ++ x ++ ".(" ++ show ph ++ ")"

data NamelessPattern = Var String | Bound Int | Bot | Sym String | Imp NamelessPattern NamelessPattern | App NamelessPattern NamelessPattern | Exs NamelessPattern
  deriving (Eq, Show, Generic)

namelessPrimitive :: NamelessPattern -> Bool
namelessPrimitive (Var _) = True
namelessPrimitive Bot = True
namelessPrimitive (Sym _) = True
namelessPrimitive (Bound _) = True
namelessPrimitive _ = False

-- instance Show NamelessPattern where
--   show (Var s) = "FV " ++ s ++ ""
--   show (Bound n) = "BV " ++ show n ++ ""
--   show Bot = "⊥"
--   show (Sym s) = s
--   show (Imp ph1 ph2) = (if not $ namelessPrimitive ph1 then "(" else "") ++ show ph1 ++ (if not $ namelessPrimitive ph1 then ")" else "") ++ " → " ++ (if not $ namelessPrimitive ph2 then "(" else "") ++ show ph2 ++ (if not $ namelessPrimitive ph2 then ")" else "")
--   show (App ph1 ph2) = (if not $ namelessPrimitive ph1 then "(" else "") ++ show ph1 ++ (if not $ namelessPrimitive ph1 then ")" else "") ++ " $ " ++ (if not $ namelessPrimitive ph2 then "(" else "") ++ show ph2 ++ (if not $ namelessPrimitive ph2 then ")" else "")
--   show (Exs ph) = "∃.(" ++ show ph ++ ")"

subst :: NamelessPattern -> String -> NamelessPattern -> NamelessPattern
subst (Var s) x ph
  | s == x    = ph
  | otherwise = Var s
subst (Imp ph1 ph2) x ps = Imp (subst ph1 x ps) (subst ph2 x ps)
subst (App ph1 ph2) x ps = App (subst ph1 x ps) (subst ph2 x ps)
subst (Exs ph) x ps = Exs (subst ph x ps)
subst x _ _ = x

bsubst :: NamelessPattern -> Int -> NamelessPattern -> NamelessPattern
bsubst (Bound n) x ph
  | n == x    = ph
  | n < x     = Bound n
  | n > x     = Bound (n - 1)
bsubst (Imp ph1 ph2) x ps = Imp (bsubst ph1 x ps) (bsubst ph2 x ps)
bsubst (App ph1 ph2) x ps = App (bsubst ph1 x ps) (bsubst ph2 x ps)
bsubst (Exs ph) x ps = Exs (bsubst ph (x + 1) ps)
bsubst x _ _ = x

type State = [String]

fresh :: State -> String
fresh l
  | null l    = "X"
  | otherwise = maximum l ++ "X"

translate :: State -> NamelessPattern -> Maybe NamedPattern
translate st (Var s)       = Just (NVar s)
translate st (Bound x)     = Nothing
translate _  (Sym s)       = Just (NSym s)
translate _  Bot           = Just NBot
translate st (Imp ph1 ph2) = let (ph1', ph2') = (translate st ph1, translate st ph2) in NImp <$> ph1' <*> ph2'
translate st (App ph1 ph2) = let (ph1', ph2') = (translate st ph1, translate st ph2) in NApp <$> ph1' <*> ph2'
translate st (Exs ph) = NExs y <$> translate st' (bsubst ph 0 (Var y))
  where
    y = fresh st
    st' = st ++ [y]


patt1 :: NamelessPattern
patt1 = Imp (Var "X") (Exs (Imp (Bound 0) (Exs (Imp (Bound 0) (Imp (Bound 1) (Var "X"))))))

npatt1 :: NamedPattern
npatt1 = NImp (NVar "X") (NExs "XX" (NImp (NVar "XX") (NExs "XXX" (NImp (NVar "XXX") (NImp (NVar "XX") (NVar "X"))))))

patt1_subst :: NamelessPattern
patt1_subst = subst patt1 "X" (Exs (Bound 0))

rename :: NamedPattern -> String -> String -> NamedPattern
rename (NVar s) x ph
  | s == x    = NVar ph
  | otherwise = NVar s
rename (NImp ph1 ph2) x ps = NImp (rename ph1 x ps) (rename ph2 x ps)
rename (NApp ph1 ph2) x ps = NApp (rename ph1 x ps) (rename ph2 x ps)
rename (NExs y ph) x ps
  | x /= y    = NExs y (rename ph x ps)
  | otherwise = NExs y ph
rename x _ _ = x

nSubstStateful :: State -> NamedPattern -> String -> NamedPattern -> NamedPattern
nSubstStateful st (NVar s) x ph
  | s == x    = ph
  | otherwise = NVar s
nSubstStateful st (NImp ph1 ph2) x ps = NImp (nSubstStateful st ph1 x ps) (nSubstStateful st ph2 x ps)
nSubstStateful st (NApp ph1 ph2) x ps = NApp (nSubstStateful st ph1 x ps) (nSubstStateful st ph2 x ps)
nSubstStateful st (NExs y ph) x ps = NExs z (nSubstStateful st' (rename ph y z) x ps)
  where
    z = fresh st
    st' = st ++ [z]
nSubstStateful st x _ _ = x

npatt1_subst :: NamedPattern
npatt1_subst = nSubstStateful ["X"] npatt1 "X" (NExs "XXXX" (NVar "XXXX"))

-- This propably won't work
-- Q: Stateful translation, that propagates states? At the end, the final state is returned?

iterateState :: Int -> State -> State
iterateState 0 st = st
iterateState n st = iterateState (n - 1) (st ++ [fresh st])


-- How about named substitutions taking a state + a depth counter as arguments? They will always rename all bound vars!
shift :: State -> NamedPattern -> NamedPattern
shift st (NImp ph1 ph2) = NImp (shift st ph1) (shift st ph2)
shift st (NApp ph1 ph2) = NApp (shift st ph1) (shift st ph2)
shift st (NExs x ph) = NExs z (rename (shift st' ph) x z)
  where
    z = fresh st
    st' = st ++ [z]
shift _ ph = ph

nsubst2 :: State -> NamedPattern -> String -> NamedPattern -> NamedPattern
nsubst2 st (NVar s) x ph
  | s == x    = shift st ph
  | otherwise = NVar s
nsubst2 st (NImp ph1 ph2) x ps = NImp (nsubst2 st ph1 x ps) (nsubst2 st ph2 x ps)
nsubst2 st (NApp ph1 ph2) x ps = NApp (nsubst2 st ph1 x ps) (nsubst2 st ph2 x ps)
nsubst2 st (NExs y ph) x ps = NExs z (nsubst2 st' (rename ph y z) x ps)
  where
    z = fresh st
    st' = st ++ [z]
nsubst2 st x _ _ = x

freeVars :: NamelessPattern -> [String]
freeVars (Imp ph1 ph2) = freeVars ph1 ++ freeVars ph2
freeVars (App ph1 ph2) = freeVars ph1 ++ freeVars ph2
freeVars (Exs ph) = freeVars ph
freeVars (Var x) = [x]
freeVars _ = []

availableVarNames :: [Gen String]
availableVarNames = map (return . (:[])) ['A'..'Z']

availableSymNames :: [Gen String]
availableSymNames = map (return . (:[])) ['a'..'z']

instance Arbitrary NamelessPattern where
  arbitrary :: Gen NamelessPattern
  arbitrary = sized (ph [])
    where ph st 0 = oneof (map (return . Bound) st ++ [liftM Var (oneof availableVarNames), liftM Sym (oneof availableSymNames), return Bot])
          ph st n = oneof [liftM2 Imp (subph st) (subph st), liftM2 App (subph st) (subph st), liftM Exs (subph (0 : map (+1) st))]
            where subph st = ph st (n `div` 2)

  -- shrink :: NamelessPattern -> [NamelessPattern]
  -- shrink (Imp ph1 ph2) = [ph1, ph2] ++ [Imp ph1' ph2' | (ph1', ph2') <- shrink (ph1, ph2)]
  -- shrink (App ph1 ph2) = [ph1, ph2] ++ [App ph1' ph2' | (ph1', ph2') <- shrink (ph1, ph2)]
  shrink (Exs ph) = [Exs ph' | ph' <- shrink ph]
  shrink x = genericShrink x
  -- shrink ph = [ph]

firstSubst :: NamelessPattern -> NamelessPattern -> String -> Maybe NamedPattern
firstSubst ph ps x = case (translate st ph, translate st ps) of
                        (Just ph', Just ps') -> Just $ nsubst2 st ph' x ps'
                        _ -> Nothing
  where
    st = x : freeVars ph ++ freeVars ps -- we have to include x in the state as discussed (to avoid "freeing" a bound variable)

secondSubst :: NamelessPattern -> NamelessPattern -> String -> Maybe NamedPattern
secondSubst ph ps x = translate st (subst ph x ps) 
  where
    st = x : freeVars ph ++ freeVars ps -- we have to include x in the state as discussed (to avoid "freeing" a bound variable)

data Input = Inp NamelessPattern NamelessPattern String deriving (Show, Eq, Generic)

instance Arbitrary Input where
  arbitrary = do
    ph1 <- arbitrary :: Gen NamelessPattern
    ph2 <- arbitrary :: Gen NamelessPattern
    x <- oneof (availableVarNames ++ map return (freeVars ph1 ++ freeVars ph2)) -- availableVarNames are used if the second list is empty
    return (Inp ph1 ph2 x)
  shrink = genericShrink

prop_subst :: NamelessPattern -> NamelessPattern -> String -> Bool
prop_subst ph ps x = case (translate st ph, translate st ps, translate st (subst ph x ps)) of
                      (Just ph', Just ps', Just res) -> nsubst2 st ph' x ps' == res
                      _ -> False
  where
    st = x : freeVars ph ++ freeVars ps -- we have to include x in the state as discussed (to avoid "freeing" a bound variable)
-- use: quickCheck (withMaxSuccess 1000 prop_subst) for testing

prop_subst2 :: Input -> Bool
prop_subst2 (Inp ph ps x) = case (translate st ph, translate st ps, translate st (subst ph x ps)) of
                              (Just ph', Just ps', Just res) -> nsubst2 st ph' x ps' == res
                              _ -> False
  where
    st = x : freeVars ph ++ freeVars ps -- we have to include x in the state as discussed (to avoid "freeing" a bound variable)