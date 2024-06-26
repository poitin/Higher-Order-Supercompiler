module Term where

import Exception
import Prelude hiding ((<>))
import Data.Char
import Data.Maybe
import Data.List
import Data.Tuple
import Data.Foldable
import Control.Monad
import Text.PrettyPrint.HughesPJ as P
import Text.ParserCombinators.Parsec hiding (labels)
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language
import System.IO
import System.Directory

-- terms

data Term = Free String -- free variable
          | Bound Int -- bound variable with de Bruijn index
          | Lambda String Term -- lambda abstraction
          | Con String [Term] -- constructor application
          | Apply Term Term -- application
          | Fun String -- function call
          | Case Term [(String,[String],Term)] -- case expression
          | Let String Term Term -- let expression
          | Unfold Term Term Term -- unfolded term
          | Fold Term -- folded term
 
instance Show Term where
   show t = render $ prettyTerm t

type Prog = (Term,[(String,([String],Term))])

showProg p = renderStyle (Style { lineLength = 100, ribbonsPerLine = 1.1, mode = PageMode }) $ prettyProg p

-- equality of terms

instance Eq Term where
  (==) (Free x) (Free x') = x==x'
  (==) (Bound i) (Bound i') = i==i'
  (==) (Lambda x t) (Lambda x' t') = t==t'
  (==) (Con c ts) (Con c' ts') | c==c' = all (uncurry (==)) (zip ts ts')
  (==) (Apply t u) (Apply t' u') = t==t' && u==u'
  (==) (Fun f) (Fun f') = f==f'
  (==) (Case t bs) (Case t' bs') | matchCase bs bs' = t==t'  && all (\((_,_,t),(_,_,t')) -> t==t') (zip bs bs')
  (==) (Let x t u) (Let x' t' u') = t==t' && u==u'
  (==) t t' = False

-- context surrounding redex

data Context = EmptyCtx
             | ApplyCtx Context Term
             | CaseCtx Context [(String,[String],Term)] deriving Show

-- place term in context

place t EmptyCtx = t
place t (ApplyCtx con u) = place (Apply t u) con
place t (CaseCtx con bs) = place (Case t bs) con

-- redex of a term

redex (Case t bs) = redex t 
redex (Apply t u) = redex t
redex t = t


-- arguments of a function call

args (Apply t u) = args t ++ [u]
args t = []

-- matching branches in case term

matchCase bs bs' = length bs == length bs' && all (\((c,xs,t),(c',xs',t')) -> c == c' && length xs == length xs') (zip bs bs')

-- term renaming

renaming t u = renaming' t u []

renaming' (Free x) (Free x') r = if   x `elem` map fst r || x' `elem` map snd r
                                 then [r | (x,x') `elem` r]
                                 else [(x,x'):r] 
renaming' (Bound i) (Bound i') r | i==i' = [r]
renaming' (Lambda x t) (Lambda x' t') r = renaming' t t' r
renaming' (Con c ts) (Con c' ts') r | c==c' = foldr (\(t,t') rs -> concat [renaming' t t' r | r <- rs]) [r] (zip ts ts')
renaming' (Apply t u) (Apply t' u') r = concat [renaming' u u' r' | r' <- renaming' t t' r]
renaming' (Fun f) (Fun f') r | f==f' = [r]
renaming' (Case t bs) (Case t' bs') r | matchCase bs bs' = foldr (\((c,xs,t),(c',xs',t')) rs -> concat [renaming' t t' r | r <- rs]) (renaming' t t' r) (zip bs bs')
renaming' (Let x t u) (Let x' t' u') r = concat [renaming' u u' r' | r' <- renaming' t t' r]
renaming' t u r = []

-- homeomorphic embedding of terms

embedding t u = couple t u []

embed t u r = couple t u r ++ dive t u r 

couple (Free x) (Free x') r = if   x `elem` map fst r 
                              then [r | (x,x') `elem` r] 
                              else [(x,x'):r]
couple (Bound i) (Bound i') r | i == i' = [r]
couple (Lambda x t) (Lambda x' t') r = couple t t' r
couple (Con c ts) (Con c' ts') r | c==c' = foldr (\(t,t') rs -> concat [embed t t' r | r <- rs]) [r] (zip ts ts')
couple (Apply t u) (Apply t' u') r = concat [couple t t' r' | r' <- embed u u' r]
couple (Fun f) (Fun f') r | f==f' = [r]
couple (Case t bs) (Case t' bs') r | matchCase bs bs' = foldr (\((c,xs,t),(c',xs',t')) rs -> concat [embed t t' r | r <- rs]) (embed t t' r) (zip bs bs')
couple (Let x t u) (Let x' t' u') r = concat [embed u u' r' | r' <- embed t t' r]
couple t t' r = []

dive t (Lambda x t') r = embed (shift 1 t) t' r
dive t (Con c ts) r = concat [embed t t' r | t' <- ts]
dive t (Apply t' u) r = embed t t' r ++ embed t u r
dive t (Case t' bs) r = embed t t' r ++ concatMap (\(c,xs,t') -> embed (shift (length xs) t) t' r) bs
dive t (Let x t' u) r = embed t t' r ++ embed (shift 1 t) u r
dive t t' r = []

-- generalisation of terms

generalise t u fv s1 s2 | not (null (couple t u [])) = generalise' t u fv s1 s2
generalise t u fv s1 s2 = case [x | ((x,t'),(_,u')) <- zip s1 s2, t==t' && u==u'] of
                             (x:_) -> (Free x,s1,s2)
                             [] -> let x = renameVar (fv++map fst s1) "x"
                                   in  (Free x,(x,t):s1,(x,u):s2)

generalise' (Free x) (Free x') fv s1 s2 = (Free x,s1,s2)
generalise' (Bound i) (Bound i') fv s1 s2 = (Bound i,s1,s2)
generalise' (Lambda x t) (Lambda x' t') fv s1 s2 = let x'' = renameVar (fv++map fst s1) x
                                                       (t'',s1',s2') = generalise (concrete x'' t) (concrete x'' t') (x'':fv) s1 s2
                                                   in  (Lambda x (abstract t'' x''),s1',s2')
generalise' (Con c ts) (Con c' ts') fv s1 s2 = let ((s1',s2'),ts'') = mapAccumL (\(s1,s2) (t,t') -> let (t'',s1',s2') = generalise t t' fv s1 s2
                                                                                                    in  ((s1',s2'),t'')) (s1,s2) (zip ts ts')
                                               in  (Con c ts'',s1',s2')
generalise' (Apply t u) (Apply t' u') fv s1 s2 = let (t'',s1',s2') = generalise t t' fv s1 s2
                                                     (u'',s1'',s2'') = generalise u u' fv s1' s2'    
                                                 in  (Apply t'' u'',s1'',s2'')
generalise' (Fun f) (Fun f') fv s1 s2 = (Fun f,s1,s2)
generalise' (Case t bs) (Case t' bs') fv s1 s2 = let (t'',s1',s2') = generalise t t' fv s1 s2
                                                     ((s1'',s2''),bs'') = mapAccumL (\(s1,s2) ((c,xs,t),(c',xs',t')) -> let xs'' = renameVars (fv++map fst s1) xs
                                                                                                                            (t'',s1',s2') = generalise (foldr concrete t xs'') (foldr concrete t' xs'') (xs''++fv) s1 s2
                                                                                                                        in  ((s1',s2'),(c,xs,foldl abstract t'' xs''))) (s1',s2') (zip bs bs')
                                                 in  (Case t'' bs'',s1'',s2'')
generalise' (Let x t u) (Let x' t' u') fv s1 s2 = let x'' = renameVar (fv++map fst s1) x
                                                      (t'',s1',s2') =  generalise t t' fv s1 s2
                                                      (u'',s1'',s2'') = generalise (concrete x'' u) (concrete x'' u') (x'':fv) s1' s2'
                                                  in  (Let x t'' (abstract u'' x''),s1'',s2'')

makeLet s t = foldl (\u (x,t) -> Let x t (abstract u x)) t s

-- program residualisation

residualise t = residualise' (simplify t) (free t) []

residualise' (Free x) fv d = (Free x,d)
residualise' (Bound i) fv d = (Bound i,d)
residualise' (Lambda x t) fv d = let x' = renameVar fv x
                                     (t',d') = residualise' (concrete x' t) (x':fv) d
                                 in  (Lambda x (abstract t' x'),d')
residualise' (Con c ts) fv d = let (d',ts') = mapAccumL (\d t -> let (t',d') = residualise' t fv d
                                                                 in  (d',t')) d ts
                               in  (Con c ts',d')
residualise' (Apply t u) fv d = let (t',d') = residualise' t fv d
                                    (u',d'') = residualise' u fv d'
                                in  (Apply t' u',d'')
residualise' (Fun f) fv d = (Fun f,d)
residualise' (Case t bs) fv d = let (t',d') = residualise' t fv d
                                    (d'',bs') = mapAccumL (\d (c,xs,t) -> let xs' = renameVars fv xs
                                                                              (t',d') = residualise' (foldr concrete t xs') (xs'++fv) d
                                                                          in  (d',(c,xs,foldl abstract t' xs'))) d' bs
                                in  (Case t' bs',d'')
residualise' (Let x t u) fv d = let x' = renameVar fv x
                                    (t',d') = residualise' t fv d
                                    (u',d'') = residualise' (concrete x' u) (x':fv) d'
                                in  (subst t' (abstract u' x'),d'')
residualise' (Unfold t u v) fv d = let Fun f = redex t
                                       xs = free t
                                   in  if   f `elem` map fst d
                                       then (t,d)
                                       else let (v',d') = residualise' v (f:fv) d
                                            in  (t,(f,(xs,foldl abstract v' xs)):d')
residualise' (Fold t) fv d = residualise' t fv d

-- simplify process tree to remove unmatched unfolds

simplify (Free x) = Free x
simplify (Bound i) = Bound i
simplify (Lambda x t) = Lambda x (simplify t)
simplify (Con c ts) = Con c (map simplify ts)
simplify (Apply t u) = Apply (simplify t) (simplify u)
simplify (Fun f) = Fun f
simplify (Case t bs) = Case (simplify t) (map (\(c,xs,t) -> (c,xs,simplify t)) bs)
simplify (Let x t u) = Let x (simplify t) (simplify u)
simplify (Unfold t u v) = if   redex t `elem` folds v 
                          then Unfold t u (simplify v)
                          else simplify v
simplify (Fold t) = Fold (simplify t)

-- evaluate a program

eval (Free x) k d r a = error ("Unbound identifier: "++show (place (Free x) k))
eval (Lambda x t) EmptyCtx d r a = (Lambda x t,r,a)
eval (Lambda x t) (ApplyCtx k u) d r a = eval (subst u t) k d (r+1) a
eval (Lambda x t) (CaseCtx k bs) d r a = error ("Unapplied function in case selector: " ++ show (Lambda x t))
eval (Con c ts) EmptyCtx d r a = let ((r',a'),ts') = mapAccumL (\(r,a) t -> let (t',r',a') = eval t EmptyCtx d r a
                                                                            in  ((r',a'),t')) (r,a) ts
                                 in  (Con c ts',r'+1,a')
eval (Con c ts) (ApplyCtx k u) d r a = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
eval (Con c ts) (CaseCtx k bs) d r a = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                          Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                          Just (c',xs,t) -> eval (foldr subst t ts) k d (r+length ts) (a+1)
eval (Apply t u) k d r a = eval t (ApplyCtx k u) d r a
eval (Fun f) k d r a = case lookup f d of
                          Nothing -> error ("Undefined function: "++f)
                          Just (xs,t)  -> eval (foldr Lambda t xs) k d (r+1) a
eval (Case t bs) k d r a = eval t (CaseCtx k bs) d r a
eval (Let x t u) k d r a = eval (subst t u) k d (r+1) a

-- free variables in a process tree

free t = nub (free' t)

free' (Free x) = [x]
free' (Bound i) = []
free' (Lambda x t) = free' t
free' (Con c ts) = concatMap free' ts
free' (Apply t u) = free' t ++ free' u
free' (Fun f) = []
free' (Case t bs) = free' t ++ concatMap (\(c,xs,t) -> free' t) bs
free' (Let x t u) = free' t  ++ free' u
free' (Unfold t u v) = free' v
free' (Fold t) = free' t

-- folds in a process tree

folds (Free x) = []
folds (Bound i) = []
folds (Lambda x t) = folds t
folds (Con c ts) = concatMap folds ts
folds (Apply t u) = folds t ++ folds u
folds (Fun f) = []
folds (Case t bs) = folds t ++ concatMap (\(c,xs,t) -> folds t) bs
folds (Let x t u) = folds t  ++ folds u
folds (Unfold t u v) = filter (/=redex t) (folds v)
folds (Fold t) = redex t:folds t

-- unfolds in a process tree

unfolds (Free x) = []
unfolds (Bound i) = []
unfolds (Lambda x t) = unfolds t
unfolds (Con c ts) = concatMap unfolds ts
unfolds (Apply t u) = unfolds t ++ unfolds u
unfolds (Fun f) = []
unfolds (Case t bs) = unfolds t ++ concatMap (\(c,xs,t) -> unfolds t) bs
unfolds (Let x t u) = unfolds t  ++ unfolds u
unfolds t@(Unfold _ _ u) = t:unfolds u
unfolds (Fold t) = unfolds t

-- functions in a program

funs (t,d) = funs' d t []

funs' d (Free x) fs = fs
funs' d (Bound i) fs = fs
funs' d (Lambda x t) fs = funs' d t fs
funs' d (Con c ts) fs = foldr (funs' d) fs ts
funs' d (Apply t u) fs = funs' d t (funs' d u fs)
funs' d (Fun f) fs = if   f `elem` fs
                     then fs
                     else case lookup f d of
                             Nothing -> f:fs
                             Just (xs,t)  -> funs' d t (f:fs)
funs' d (Case t bs) fs = foldr (\(_,_,t) fs -> funs' d t fs) (funs' d t fs) bs
funs' d (Let x t u) fs = funs' d t (funs' d u fs)

-- shift global de Bruijn indices by i, where current depth is d

shift = shift' 0

shift' d 0 u = u
shift' d i (Free x) = Free x
shift' d i (Bound i') = if i' >= d then Bound (i'+i) else Bound i'
shift' d i (Lambda x t) = Lambda x (shift' (d+1) i t)
shift' d i (Con c ts) = Con c (map (shift' d i) ts)
shift' d i (Apply t u) = Apply (shift' d i t) (shift' d i u)
shift' d i (Fun f) = Fun f
shift' d i (Case t bs) = Case (shift' d i t) (map (\(c,xs,t) -> (c,xs,shift' (d+length xs) i t)) bs)
shift' d i (Let x t u) = Let x (shift' d i t) (shift' (d+1) i u)
shift' d i (Unfold t u v) = Unfold (shift' d i t) (shift' d i u) (shift' d i v)
shift' d i (Fold t) = Fold (shift' d i t)

-- substitute term t for variable with de Bruijn index i

subst = subst' 0

subst' i t (Free x) = Free x
subst' i t (Bound i')
   | i'<i      = Bound i'
   | i'==i     = shift i t
   | otherwise = Bound (i'-1)
subst' i t (Lambda x t') = Lambda x (subst' (i+1) t t')
subst' i t (Con c ts) = Con c (map (subst' i t) ts)
subst' i t (Apply t' u) = Apply (subst' i t t') (subst' i t u)
subst' i t (Fun f) = Fun f
subst' i t (Case t' bs) = Case (subst' i t t') (map (\(c,xs,u) -> (c,xs,subst' (i+length xs) t u)) bs)
subst' i t (Let x t' u) = Let x (subst' i t t') (subst' (i+1) t u)
subst' i t (Unfold t' u v) = Unfold (subst' i t t') (subst' i t u) (subst' i t v)
subst' i t (Fold t') = Fold (subst' i t t')

-- rename using renaming r

rename r (Free x) = case lookup x r of
                       Just x'  -> Free x'
                       Nothing -> Free x
rename r (Bound i) = Bound i
rename r (Lambda x t) = Lambda x (rename r t)
rename r (Con c ts) = Con c (map (rename r) ts)
rename r (Apply t u) = Apply (rename r t) (rename r u)
rename r (Fun f) = Fun f
rename r (Case t bs) = Case (rename r t) (map (\(c,xs,t) -> (c,xs,rename r t)) bs)
rename r (Let x t u) = Let x (rename r t) (rename r u)
rename r (Unfold t u v) = Unfold (rename r t) (rename r u) (rename r v)
rename r (Fold t) = Fold (rename r t)

-- instantiate using substitution s

instantiate = instantiate' 0

instantiate' d s (Free x) = case lookup x s of
                               Just t  -> shift d t
                               Nothing -> Free x
instantiate' d s (Bound i) = Bound i
instantiate' d s (Lambda x t) = Lambda x (instantiate' (d+1) s t)
instantiate' d s (Con c ts) = Con c (map (instantiate' d s) ts)
instantiate' d s (Apply t u) = Apply (instantiate' d s t) (instantiate' d s u)
instantiate' d s (Fun f) = Fun f
instantiate' d s (Case t bs) = Case (instantiate' d s t) (map (\(c,xs,t) -> (c,xs,instantiate' (d+length xs) s t)) bs)
instantiate' d s (Let x t u) = Let x (instantiate' d s t) (instantiate' (d+1) s u)
instantiate' d s (Unfold t u v) = Unfold (instantiate' d s t) (instantiate' d s u) (instantiate' d s v)
instantiate' d s (Fold t) = Fold (instantiate' d s t)

-- replace variable x with de Bruijn index

abstract = abstract' 0

abstract' i (Free x') x = if x==x' then Bound i else Free x'
abstract' i (Bound i') x = if i'>=i then Bound (i'+1) else Bound i'
abstract' i (Lambda x' t) x = Lambda x' (abstract' (i+1) t x)
abstract' i (Con c ts) x = Con c (map (\t -> abstract' i t x) ts)
abstract' i (Apply t u) x = Apply (abstract' i t x) (abstract' i u x)
abstract' i (Fun f) x = Fun f
abstract' i (Case t bs) x = Case (abstract' i t x) (map (\(c,xs,t) -> (c,xs,abstract' (i+length xs) t x)) bs)
abstract' i (Let x' t u) x = Let x' (abstract' i t x) (abstract' (i+1) u x)
abstract' i (Unfold t u v) x = Unfold (abstract' i t x) (abstract' i u x) (abstract' i v x)
abstract' i (Fold t) x = Fold (abstract' i t x)

-- replace de Bruijn index 0 with variable x

concrete = concrete' 0

concrete' i x (Free x') = Free x'
concrete' i x (Bound i')
   | i'<i = Bound i'
   | i'==i = Free x
   | otherwise = Bound (i'-1)
concrete' i x (Lambda x' t) = Lambda x' (concrete' (i+1) x t)
concrete' i x (Con c ts) = Con c (map (concrete' i x) ts)
concrete' i x (Apply t u) = Apply (concrete' i x t) (concrete' i x u)
concrete' i x (Fun f) = Fun f
concrete' i x (Case t bs) = Case (concrete' i x t) (map (\(c,xs,t) -> (c,xs,concrete' (i+length xs) x t)) bs)
concrete' i x (Let x' t u) = Let x' (concrete' i x t) (concrete' (i+1) x u)
concrete' i x (Unfold t u v) = Unfold (concrete' i x t) (concrete' i x u) (concrete' i x v)
concrete' i x (Fold t) = Fold (concrete' i x t)

-- rename variable x so it does not clash with any of fv

renameVar fv x = if   x `elem` fv
                 then renameVar fv (x++"'")
                 else x

renameVars fv xs = take (length xs) (foldr (\x fv -> let x' = renameVar fv x in x':fv) fv xs)

-- unfold function

unfold (Apply t u) d = Apply (unfold t d) u
unfold (Case t bs) d = Case (unfold t d) bs
unfold (Fun f) d = case lookup f d of
                      Just (xs,t) -> foldr Lambda t xs
                      Nothing -> Fun f
unfold t d = t

-- pretty printing

stripLambda (Lambda x t) = let x' = renameVar (free t) x
                               (xs,u) = stripLambda $ concrete x' t
                           in  (x':xs,u)
stripLambda t = ([],t)

blank = P.space

prettyCon t@(Con c ts)
   | isNat t   = int $ con2nat t
   | isList t  = brackets $ hcat $ punctuate comma $ map prettyTerm $ con2list t
   | null ts   = text c
   | otherwise = text c <> parens (hcat $ punctuate comma $ map prettyTerm ts)

prettyVar x = let (s1,s2) = span (/= '\'') x
              in  if null s2 then text s1 else text s1 <> int (length s2)

prettyTerm (Free x) = prettyVar x
prettyTerm (Bound i) = text "#" <> int i
prettyTerm t@(Lambda _ _) = let (xs,t') = stripLambda t
                            in  text "\\" <> hsep (map prettyVar xs) <> text "." <> prettyTerm t'
prettyTerm t@(Con c ts) = prettyCon t
prettyTerm t@(Apply _ _) = prettyApp t where
   prettyApp (Apply t u) = prettyApp t <+> prettyAtom u
   prettyApp t = prettyAtom t
prettyTerm (Fun f) = prettyVar f
prettyTerm (Case t (b:bs)) = 
   hang (text "case" <+> prettyAtom t <+> text "of") 1 (blank <+> prettyBranch b $$ vcat (map ((text "|" <+>).prettyBranch) bs)) where
   prettyBranch (c,[],t) = text c <+> text "->" <+> prettyTerm t
   prettyBranch (c,xs,t) = let xs' = renameVars (free t) xs
                               t' = foldr concrete t xs'
                           in  text c <> parens(hcat $ punctuate comma $ map prettyVar xs') <+> text "->" <+> prettyTerm t' $$ empty
prettyTerm (Let x t u) = let x' = renameVar (free u) x
                         in  (text "let" <+> prettyVar x' <+> text "=" <+> prettyTerm t) $$ (text "in" <+> prettyTerm (concrete x' u))
prettyTerm (Unfold t u v) = prettyAtom t <+> text "=" <+> prettyTerm v
prettyTerm (Fold t) = prettyTerm t

prettyAtom (Free x) = prettyVar x
prettyAtom t@(Con c ts) = prettyCon t
prettyAtom (Fun f) = prettyVar f 
prettyAtom t = parens $ prettyTerm t

prettyProg (t,d) = let d' = [f | f <- d, fst f `elem` funs (t,d)]          
                   in  prettyEnv (("main",([],t)):d')


prettyEnv xs = vcat (punctuate semi $ map (\(f,(xs,t)) -> prettyVar f <+> hsep (map prettyVar xs) <+> equals <+> prettyTerm (foldr concrete t xs)) xs)

isList (Con "Nil" []) = True
isList (Con "Cons" [h,t]) = isList t
isList _ = False

list2con [] = Con "Nil" []
list2con (h:t) = Con "Cons" [h,list2con t]

con2list (Con "Nil" [])  = []
con2list (Con "Cons" [h,t]) = h:con2list t

range2con m n = if    m > n 
                then Con "Nil" []
                else Con "Cons" [nat2con m,range2con (m+1) n]

isNat (Con "Zero" []) = True
isNat (Con "Succ" [n]) = isNat n
isNat _ = False

nat2con 0 = Con "Zero" []
nat2con n = Con "Succ" [nat2con $ n-1]

con2nat (Con "Zero" [])  = 0
con2nat (Con "Succ" [n]) = 1+con2nat n

-- lexing and parsing

potDef = emptyDef
         { commentStart    = "/*"
         , commentEnd      = "*/"
         , commentLine     = "--"
         , nestedComments  = True
         , identStart      = lower
         , identLetter     = letter <|> digit <|> oneOf "_'"
         , reservedNames   = ["import", "case","of","let","in","letrec","ALL","EX","ANY"]
         , reservedOpNames = ["~","/\\","\\/","<=>","=>"]
         , caseSensitive   = True
         }

lexer = T.makeTokenParser potDef

symbol     = T.symbol lexer
bracks     = T.parens lexer
semic      = T.semi lexer
comm       = T.comma lexer
identifier = T.identifier lexer
reserved   = T.reserved lexer
reservedOp = T.reservedOp lexer
natural    = T.natural lexer

con = do
      c <- upper
      cs <- many letter
      spaces
      return (c:cs)

makeProg ds = let fs = map fst ds
                  ds' =  map (\(f,(xs,t)) -> (f,(xs,foldl abstract (makeFun fs t) xs))) ds
              in  case lookup "main" ds' of
                     Nothing -> error "No main function"
                     Just (xs,t) -> (t,delete ("main",(xs,t)) ds')

makeFun fs (Free x) = if x `elem` fs then Fun x else Free x
makeFun fs (Bound i) = Bound i
makeFun fs (Lambda x t) = Lambda x (makeFun fs t)
makeFun fs (Con c ts) = Con c (map (makeFun fs) ts)
makeFun fs (Apply t u) = Apply (makeFun fs t) (makeFun fs u)
makeFun fs (Fun f) = Fun f
makeFun fs (Case t bs) = Case (makeFun fs t) (map (\(c,xs,t) -> (c,xs,makeFun fs t)) bs)
makeFun fs (Let x t u) = Let x (makeFun fs t) (makeFun fs u)

modul = do
        fs <- many imp
        ds <- sepBy1 fundef semic
        return (fs,ds)

imp = do
      reserved "import"
      con

fundef = do
         f <- identifier
         xs <- many identifier
         symbol "="
         e <- term
         return (f,(xs,e))

term =     do
           a <- atom
           as <- many atom
           return (foldl Apply a as)
       <|> do
           symbol "\\"
           xs <- many1 identifier
           symbol "->"
           t <- term
           return (foldr (\x t->Lambda x (abstract t x)) t xs)
       <|> do
           reserved "case"
           t <- term
           reserved "of"
           bs <- sepBy1 branch (symbol "|")
           return (Case t bs)

atom =     do Free <$> identifier
       <|> do
           c <- con
           ts <- option [] (bracks (sepBy1 term comm))
           return (Con c ts) 
       <|> do 
           m <- natural
           option (nat2con m) (do symbol ".." 
                                  range2con m <$> natural)
       <|> do
           symbol "["
           ts <- sepBy term comm
           symbol "]"
           return (list2con ts)
       <|> bracks term

branch = do
         c <- con
         xs <- option [] (bracks (sepBy1 identifier comm))
         symbol "->"
         t <- term
         return (c,xs,foldl abstract t xs)

parseTerm = parse term "Parse error"

parseModule = parse modul "Parse error"