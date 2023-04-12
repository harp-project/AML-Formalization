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

-- translate :: State -> NamelessPattern -> Maybe NamedPattern
-- translate st (Var s)       = Just (NVar s)
-- translate st (Bound x)     = Nothing
-- translate _  (Sym s)       = Just (NSym s)
-- translate _  Bot           = Just NBot
-- translate st (Imp ph1 ph2) = let (ph1', ph2') = (translate st ph1, translate st ph2) in NImp <$> ph1' <*> ph2'
-- translate st (App ph1 ph2) = let (ph1', ph2') = (translate st ph1, translate st ph2) in NApp <$> ph1' <*> ph2'
-- translate st (Exs ph) = NExs y <$> translate st' (bsubst ph 0 (Var y))
--   where
--     y = fresh st
--     st' = st ++ [y]


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
    st' = z : st
nSubstStateful st x _ _ = x

npatt1_subst :: NamedPattern
npatt1_subst = nSubstStateful ["X"] npatt1 "X" (NExs "XXXX" (NVar "XXXX"))

-- This propably won't work
-- Q: Stateful translation, that propagates states? At the end, the final state is returned?

iterateState :: Int -> State -> State
iterateState n st 
  | n <= 0    = st
  | otherwise = iterateState (n - 1) (fresh st : st)


-- How about named substitutions taking a state + a depth counter as arguments? They will always rename all bound vars!
shift :: State -> NamedPattern -> NamedPattern
shift st (NImp ph1 ph2) = NImp (shift st ph1) (shift st ph2)
shift st (NApp ph1 ph2) = NApp (shift st ph1) (shift st ph2)
shift st (NExs x ph) = NExs z (rename (shift st' ph) x z)
  where
    z = fresh st
    st' = z : st
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
    st' = z : st
nsubst2 st x _ _ = x

freeVars :: NamelessPattern -> [String]
freeVars (Imp ph1 ph2) = freeVars ph1 ++ freeVars ph2
freeVars (App ph1 ph2) = freeVars ph1 ++ freeVars ph2
freeVars (Exs ph) = freeVars ph
freeVars (Var x) = [x]
freeVars _ = []

namedFreeVars :: NamedPattern -> [String]
namedFreeVars (NImp ph1 ph2) = namedFreeVars ph1 ++ namedFreeVars ph2
namedFreeVars (NApp ph1 ph2) = namedFreeVars ph1 ++ namedFreeVars ph2
namedFreeVars (NExs x ph) = filter (/=x) (namedFreeVars ph)
namedFreeVars (NVar x) = [x]
namedFreeVars _ = []

--availableVarNames :: [Gen String]
--availableVarNames = map (return . (:[])) ['A'..'Z']

--availableSymNames :: [Gen String]
--availableSymNames = map (return . (:[])) ['a'..'z']

availableVarNames :: Gen String
availableVarNames = liftM (:[]) $ chooseEnum ('A', 'Z')

availableSymNames :: Gen String
availableSymNames = liftM (:[]) $ chooseEnum ('a', 'z')

-- Well-formed generation:
-- instance Arbitrary NamelessPattern where
--   arbitrary :: Gen NamelessPattern
--   arbitrary = sized (ph [])
--     where ph st 0 = oneof (map (return . Bound) st ++ [liftM Var (oneof availableVarNames), liftM Sym (oneof availableSymNames), return Bot])
--           ph st n = oneof [liftM2 Imp (subph st) (subph st), liftM2 App (subph st) (subph st), liftM Exs (subph (0 : map (+1) st))]
--             where subph st = ph st (n `div` 2)

-- Patterns containing only the 0 as dangling
instance Arbitrary NamelessPattern where
  arbitrary :: Gen NamelessPattern
  arbitrary = sized (ph [0..10])
    where ph st 0 = oneof (map (return . Bound) st ++ [liftM Var availableVarNames, liftM Sym availableSymNames, return Bot])
          ph st n = oneof [liftM2 Imp (subph st) (subph st), liftM2 App (subph st) (subph st), liftM Exs (subph (0 : map (+1) st))]
            where subph st = ph st (n `div` 2)

-- Non-well-formed generation
-- instance Arbitrary NamelessPattern where
--   arbitrary :: Gen NamelessPattern
--   arbitrary = sized ph
--     where ph 0 = oneof [liftM Var (oneof availableVarNames), liftM Bound (oneof (map return [1..100])), liftM Sym (oneof availableSymNames), return Bot]
--           ph n = oneof [liftM2 Imp subph subph, liftM2 App subph subph, liftM Exs subph]
--             where subph = ph (n `div` 2)



  -- shrink :: NamelessPattern -> [NamelessPattern]
  -- shrink (Imp ph1 ph2) = [ph1, ph2] ++ [Imp ph1' ph2' | (ph1', ph2') <- shrink (ph1, ph2)]
  -- shrink (App ph1 ph2) = [ph1, ph2] ++ [App ph1' ph2' | (ph1', ph2') <- shrink (ph1, ph2)]
  shrink (Exs ph) = [Exs ph' | ph' <- shrink ph]
  shrink x = genericShrink x
  -- shrink ph = [ph]

-- firstSubst :: NamelessPattern -> NamelessPattern -> String -> Maybe NamedPattern
-- firstSubst ph ps x = case (translate st ph, translate st ps) of
--                         (Just ph', Just ps') -> Just $ nsubst2 st ph' x ps'
--                         _ -> Nothing
--   where
--     st = x : freeVars ph ++ freeVars ps -- we have to include x in the state as discussed (to avoid "freeing" a bound variable)

-- secondSubst :: NamelessPattern -> NamelessPattern -> String -> Maybe NamedPattern
-- secondSubst ph ps x = translate st (subst ph x ps) 
--   where
--     st = x : freeVars ph ++ freeVars ps -- we have to include x in the state as discussed (to avoid "freeing" a bound variable)

-- Inp includes a pattern to substitute in, a pattern to substitute with, a name and an index to substitute
data Input = Inp NamelessPattern NamelessPattern String Int deriving (Show, Eq, Generic)

well_formed :: NamelessPattern -> Int -> Bool
well_formed (Bound x) y = x < y
well_formed (Imp ph1 ph2) y = well_formed ph1 y && well_formed ph2 y
well_formed (App ph1 ph2) y = well_formed ph1 y && well_formed ph2 y
well_formed (Exs ph) y = well_formed ph (y + 1)
well_formed _ _ = True

biggestBound :: NamelessPattern -> Int -- gets the biggest unbound db index
biggestBound (Bound x) = x
biggestBound (Imp ph1 ph2) = max (biggestBound ph1) (biggestBound ph2)
biggestBound (App ph1 ph2) = max (biggestBound ph1) (biggestBound ph2)
biggestBound (Exs ph) = biggestBound ph - 1
biggestBound _ = 0

instance Arbitrary Input where
  arbitrary = do
    ph1 <- arbitrary :: Gen NamelessPattern -- if well-formed ph1 is needed, use `suchThat arbitrary (flip well_formed 0)`
    ph2 <- suchThat arbitrary (flip well_formed 0) :: Gen NamelessPattern
 --   n <- oneof (map return [1..100]) 
    x <- oneof (availableVarNames : map return (freeVars ph1 ++ freeVars ph2)) -- availableVarNames are used if the second list is empty
    return (Inp ph1 ph2 x (biggestBound ph1))
  shrink = genericShrink

-- prop_subst :: NamelessPattern -> NamelessPattern -> String -> Bool
-- prop_subst ph ps x = case (translate st ph, translate st ps, translate st (subst ph x ps)) of
--                       (Just ph', Just ps', Just res) -> nsubst2 st ph' x ps' == res
--                       _ -> False
--   where
--     st = x : freeVars ph ++ freeVars ps -- we have to include x in the state as discussed (to avoid "freeing" a bound variable)
-- use: quickCheck (withMaxSuccess 1000 prop_subst) for testing

-- prop_subst2 :: Input -> Bool
-- prop_subst2 (Inp ph ps x) = case (translate st ph, translate st ps, translate st (subst ph x ps)) of
--                               (Just ph', Just ps', Just res) -> nsubst2 st ph' x ps' == res
--                               _ -> False
--   where
--     st = x : freeVars ph ++ freeVars ps -- we have to include x in the state as discussed (to avoid "freeing" a bound variable)


{-
  translate (ph[n |-> ps]) ?
  
  
  theory ⊢H (instantiate (patt_exists phi) (patt_free_evar y) ---> (patt_exists phi))
  ph.[0 |-> y] ---> ex, ph
                     ^----- new bound variable = fresh st

-- well_formed translate
  translate (ph.[0 |-> y]) st = (translate (ph.[0 |-> fresh st]) (fresh st : st)).[fresh st |-> y]

-- non-well_formed translates
  translate (ph.[0 |-> y]) st = (translate ph st).[fresh st |-> y]

  translate (ph.[0 |-> ps]) st = (translate ph st).[fresh st |-> translate ps st]
  translate (ph.[n |-> ps]) st = (translate ph st).[fresh (iterateState n st) |-> translate ps st]


---> ex fresh st, translate (ph.[0 |-> fresh st])

  translate (ph[0 |-> y] ---> ex, ph) = (translate ph).[? |-> y] ---> ex fresh st, translate ph

  theory ⊢N npatt_imp (rename_free_evar ph y x) (npatt_exists x ph)

-}
translate :: State -> NamelessPattern -> NamedPattern
translate st (Var s)       = NVar s
translate st (Bound x)     = NVar $ fresh (iterateState x st)
translate _  (Sym s)       = NSym s
translate _  Bot           = NBot
translate st (Imp ph1 ph2) = let (ph1', ph2') = (translate st ph1, translate st ph2) in NImp ph1' ph2'
translate st (App ph1 ph2) = let (ph1', ph2') = (translate st ph1, translate st ph2) in NApp ph1' ph2'
translate st (Exs ph) = NExs y $ translate st' (bsubst ph 0 (Var y))
  where
    y = fresh st
    st' = y : st

prop_subst2 :: Input -> Bool
prop_subst2 (Inp ph ps x _) = case (translate st ph, translate st ps, translate st (subst ph x ps)) of
                              (ph', ps', res) -> nsubst2 st ph' x ps' == res
--                              _ -> False
  where
    st = x : freeVars ph ++ freeVars ps -- we have to include x in the state as discussed (to avoid "freeing" a bound variable)


--   translate (ph.[0 |-> y]) st = (translate (ph.[0 |-> fresh st]) (fresh st : st)).[fresh st |-> y]
{-
  Generalize this: can be it proved for any unbound index that is the greatest in the nameless pattern?
    - For this, we need translate to work on non-well-formed patterns
-}
prop_bsubst :: Input -> Bool
prop_bsubst (Inp ph ps _ _) = translate st (bsubst ph 0 ps) == nsubst2 st (translate st (bsubst ph 0 (Var x))) x (translate st ps)
  where
    st' = freeVars ph ++ freeVars ps
    st = x : st'
    x = fresh st'


data AppCtx = Box | LApp AppCtx NamelessPattern | RApp NamelessPattern AppCtx
  deriving (Show, Eq, Generic)

data NAppCtx = NBox | NLApp NAppCtx NamedPattern | NRApp NamedPattern NAppCtx
  deriving (Show, Eq)

substCtx :: AppCtx -> NamelessPattern -> NamelessPattern
substCtx Box ps = ps
substCtx (LApp c ph) ps = App (substCtx c ps) ph
substCtx (RApp ph c) ps = App ph (substCtx c ps)

substNCtx :: NAppCtx -> NamedPattern -> NamedPattern
substNCtx NBox ps = ps
substNCtx (NLApp c ph) ps = NApp (substNCtx c ps) ph
substNCtx (NRApp ph c) ps = NApp ph (substNCtx c ps)

translateCtx :: State -> AppCtx -> NAppCtx
translateCtx st Box         = NBox
translateCtx st (LApp c ph) = NLApp (translateCtx st c) (translate st ph)
translateCtx st (RApp ph c) = NRApp (translate st ph) (translateCtx st c)


instance Arbitrary AppCtx where
  arbitrary :: Gen AppCtx
  arbitrary = sized c
    where c 0 = return Box
          c n = oneof [liftM2 LApp subc (suchThat arbitrary (flip well_formed 0)), liftM2 RApp (suchThat arbitrary (flip well_formed 0)) subc]
            where subc = c (n `div` 2)
  shrink :: AppCtx -> [AppCtx]
  shrink = genericShrink

data InputCtx = InpCtx NamelessPattern AppCtx deriving (Show, Generic)

instance Arbitrary InputCtx where
  arbitrary :: Gen InputCtx
  arbitrary = do
    ph <- suchThat arbitrary (flip well_formed 0) :: Gen NamelessPattern
    c <- arbitrary :: Gen AppCtx
    return (InpCtx ph c)
  
  shrink :: InputCtx -> [InputCtx]
  shrink = genericShrink

prop_subst_ctx :: InputCtx -> Bool
prop_subst_ctx (InpCtx ph c) = translate st (substCtx c ph) == substNCtx (translateCtx st c) (translate st ph)
  where st = freeVars (substCtx c ph)


---------------------------------------------------
---------- translation with whitelists ------------
---------------------------------------------------
{-
  The idea is to have a list of names for all db-indices as a parameter.
-}


standardSubst :: NamedPattern -> String -> NamedPattern -> NamedPattern
standardSubst (NVar s) x ps
  | s == x    = ps
  | otherwise = NVar s
standardSubst (NImp ph1 ph2) x ps = NImp (standardSubst ph1 x ps) (standardSubst ph2 x ps)
standardSubst (NApp ph1 ph2) x ps = NApp (standardSubst ph1 x ps) (standardSubst ph2 x ps)
standardSubst (NExs y ph) x ps
  | x == y = NExs y ph
  | x /= y && elem y (namedFreeVars ps) = let z = fresh (x : namedFreeVars ps ++ namedFreeVars ph) in NExs z (standardSubst (rename ph y z) x ps)
  | otherwise = NExs y (standardSubst ph x ps)
standardSubst x _ _ = x


type Whitelist = [String]

countBinders :: NamelessPattern -> Int
countBinders (Imp ph1 ph2) = countBinders ph1 + countBinders ph2
countBinders (App ph1 ph2) = countBinders ph1 + countBinders ph2
countBinders (Exs ph)      = 1 + countBinders ph
countBinders x             = 0

namify :: State -> Whitelist -> NamelessPattern -> NamedPattern
namify st l (Var s)       = NVar s
namify st l (Bound x)     = NVar $ fresh (iterateState x st) -- A state is still needed to generate names for non-well-formed patterns
namify _  _ (Sym s)       = NSym s
namify _  l Bot           = NBot
namify st l (Imp ph1 ph2) = let (ph1', ph2') = (namify st (take (countBinders ph1) l) ph1, namify st (drop (countBinders ph1) l) ph2) in NImp ph1' ph2'
namify st l (App ph1 ph2) = let (ph1', ph2') = (namify st (take (countBinders ph1) l) ph1, namify st (drop (countBinders ph1) l) ph2) in NApp ph1' ph2'
namify st (y:l) (Exs ph)  = NExs y $ namify st l (bsubst ph 0 (Var y)) -- undefined if there were not enough names


data NamifyInput = NamifyInput NamelessPattern NamelessPattern String Whitelist Whitelist deriving (Show, Eq, Generic)

instance Arbitrary NamifyInput where
  arbitrary = do
    ph1 <- arbitrary :: Gen NamelessPattern -- if well-formed ph1 is needed, use `suchThat arbitrary (flip well_formed 0)`
    ph2 <- suchThat arbitrary (flip well_formed 0) :: Gen NamelessPattern
 --   n <- oneof (map return [1..100]) 
    x <- oneof (availableVarNames : map return (freeVars ph1 ++ freeVars ph2)) -- availableVarNames are used if the second list is empty
    names1 <- suchThat (vectorOf (countBinders ph1) availableVarNames) (all (not . flip elem (x : freeVars ph1 ++ freeVars ph2)))
    names2 <- suchThat (vectorOf (countBinders ph2) availableVarNames) (all (not . flip elem (x : freeVars ph1 ++ freeVars ph2)))
    return (NamifyInput ph1 ph2 x names1 names2)
  shrink = genericShrink

combine :: Whitelist -> Whitelist -> NamelessPattern -> String -> Whitelist
combine names1 names2 (Imp ph1 ph2) x = combine (take (countBinders ph1) names1) names2 ph1 x ++ combine (drop (countBinders ph1) names1) names2 ph2 x
combine names1 names2 (App ph1 ph2) x = combine (take (countBinders ph1) names1) names2 ph1 x ++ combine (drop (countBinders ph1) names1) names2 ph2 x
combine (y:names1) names2 (Exs ph) x  = y : combine names1 names2 ph x
combine names1 names2 (Var y) x
  | x == y    = names2
  | otherwise = names1
combine names1 _ _ _                  = names1

prop_freeSubst :: NamifyInput -> Bool
prop_freeSubst (NamifyInput ph ps x names1 names2) = case (namify st names1 ph, namify st names2 ps, namify st (combine names1 names2 ph x) (subst ph x ps)) of
                                                          (ph', ps', res) -> standardSubst ph' x ps' == res
  where
    st = x : freeVars ph ++ freeVars ps




