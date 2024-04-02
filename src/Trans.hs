-- Module Trans: program transformation

module Trans where

import Term
import Exception
import Prelude hiding ((<>))
import Data.Maybe
import Data.List
import Data.Tuple
             
-- supercompiler

super (t,d) = let (t',d') = returnval (trans 1 t EmptyCtx (free t) [] [] [] d [])
              in  residualise t'

-- function: trans n t k fv m s1 s2 d
-- n: transformation level
-- t: current term
-- k: context
-- fv: free variables
-- m: memoised terms
-- s1: generalisation environment
-- s2: generalisation environment
-- d: function definitions

trans 0 t k fv m s1 s2 d1 d2 = return (place t k,[])

trans n (Free x) (CaseCtx k bs) fv m s1 s2 d1 d2 = let bs' = map (\(c,xs,t) -> (c,xs,instantiate [(x,foldl abstract (Con c (map Free xs)) xs)] t)) bs
                                                   in  do
                                                       (bs'',d2') <- transBranches n bs' k fv m s1 s2 d1 d2
                                                       return (Case (Free x) bs'',d2')
trans n (Free x) k fv m s1 s2 d1 d2 = transCtx n (Free x) k fv m s1 s2 d1 d2
trans n (Lambda x t) EmptyCtx fv m s1 s2 d1 d2 = let x' = renameVar fv x
                                                 in  do
                                                     (t',d2') <- trans n (concrete x' t) EmptyCtx (x':fv) m s1 s2 d1 d2
                                                     return (Lambda x' (abstract t' x'),d2')
trans n (Lambda x t) (ApplyCtx k u) fv m s1 s2 d1 d2 = trans n (subst u t) k fv m s1 s2 d1 d2
trans n (Lambda x t) (CaseCtx k bs) fv m s1 s2 d1 d2 = error "Unapplied function in case selector"
trans n (Con c ts) EmptyCtx fv m s1 s2 d1 d2 = do
                                               (ts',d2') <- transArgs n ts fv m s1 s2 d1 d2
                                               return (Con c ts',d2')
trans n (Con c ts) (ApplyCtx k u) fv m s1 s2 d1 d2 = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
trans n (Con c ts) (CaseCtx k bs) fv m s1 s2 d1 d2 = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                                        Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                                        Just (c',xs,t) -> trans n (foldr subst t ts) k fv m s1 s2 d1 d2
trans n (Apply t u) k fv m s1 s2 d1 d2 = trans n t (ApplyCtx k u) fv m s1 s2 d1 d2
trans n (Case t bs) k fv m s1 s2 d1 d2 = trans n t (CaseCtx k bs) fv m s1 s2 d1 d2
trans n (Fun f) k fv m s1 s2 d1 d2 = fold n (place (Fun f) k) fv m s1 s2 d1 d2
trans n (Let x t u) k fv m s1 s2 d1 d2 = trans n (subst t u) k fv m s1 s2 d1 d2
trans n (Unfold t u) k fv m s1 s2 d1 d2 = fold n (place (Unfold t u) k) fv m s1 s2 d1 d2
trans n (Fold t u) k fv m s1 s2 d1 d2 = do
                                        (t',_) <- trans (n-1) u k fv [] [] [] d1 []
                                        fold n t' fv m s1 s2 d1 d2

transArgs n [] fv m s1 s2 d1 d2 = return ([],d2)
transArgs n (t:ts) fv m s1 s2 d1 d2 = do
                                      (t',d2') <- trans n t EmptyCtx fv m s1 s2 d1 d2
                                      (ts',d2'') <- transArgs n ts fv m s1 s2 d1 d2'
                                      return (t':ts',d2'')
transBranches n [] k fv m s1 s2 d1 d2 = return ([],d2)
transBranches n ((c,xs,t):bs) k fv m s1 s2 d1 d2 = let xs' = renameVars fv xs
                                                   in do
                                                      (t',d2') <- trans n (foldr concrete t xs') k (xs'++fv) m s1 s2 d1 d2
                                                      (bs',d2'') <- transBranches n bs k fv m s1 s2 d1 d2'
                                                      return ((c,xs,foldl abstract t' xs'):bs',d2'')

-- auxiliary function: transCtx n t k fv m s1 s2 d
-- n: transformation level
-- t: current term
-- k: context
-- fv: free variables
-- m: memoised terms
-- s1: generalisation environment
-- s2: generalisation environment
-- d: function definitions

transCtx n t EmptyCtx fv m s1 s2 d1 d2 = return (t,d2)
transCtx n t (ApplyCtx k u) fv m s1 s2 d1 d2 = do
                                               (u',d2') <- trans n u EmptyCtx fv m s1 s2 d1 d2
                                               transCtx n (Apply t u') k fv m s1 s2 d1 d2'
transCtx n t (CaseCtx k bs) fv m s1 s2 d1 d2 = do
                                               (bs',d2') <- transBranches n bs k fv m s1 s2 d1 d2
                                               return (Case t bs',d2')

transGen n (t,[],[]) fv m s1 s2 d1 d2 = trans n t EmptyCtx fv m s1 s2 d1 d2
transGen n (t,(x,t'):s1',(_,t''):s2') fv m s1 s2 d1 d2 = case [x' | (x',u) <- s1, (x'',u') <- s2, x'==x'' && u==t' && u'==t''] of
                                                            (x':_) -> transGen n (rename [(x,x')] t,s1',s2') (x':fv) m s1 s2 d1 d2
                                                            [] -> do
                                                                  (u,d2') <- trans n t' EmptyCtx fv m s1 s2 d1 d2
                                                                  (u',d2'') <- transGen n (t,s1',s2') (x:fv) m ((x,t'):s1) ((x,t''):s2) d1 d2'
                                                                  return (Let x u (abstract u' x),d2'')

transFold n [] fv m s1 s2 d1 d2 = return ([],d2)
transFold n ((x,t):s) fv m s1 s2 d1 d2 = do
                                         (t',d2') <- trans n t EmptyCtx fv m s1 s2 d1 d2
                                         (s',d2'') <- transFold n s fv m s1 s2 d1 d2'
                                         return ((x,t'):s',d2'')

fold n t fv m s1 s2 d1 d2 = case [(f,xs,t') | (f,(xs,t')) <- m, r <- embedding t' t] of
                              ((f,xs,t'):_) -> let (u,s1',s2') = generalise [] t' t fv [] [] []
                                               in  case renaming t' u of
                                                      [] -> throw (t',(u,s1',s2'))
                                                      (r:rs) -> do
                                                                (s,d2') <- transFold n s2' fv m s1 s2 d1 d2
                                                                return (Fold (instantiate s (rename r (foldl (\t x -> Apply t (Free x)) (Fun f) xs))) t,d2')
                              [] -> case [rename r u | (f,(t',u)) <- d2, r <- renaming t' t] of
                                       (u':_) -> return (u',d2)
                                       [] -> let f = renameVar (map fst m ++ map fst d1 ++ map fst d2) "f"
                                                 xs = free t
                                                 t' = foldl (\t x -> Apply t (Free x)) (Fun f) xs
                                                 handler (t',(u,s1',s2')) = if   t==t'
                                                                            then transGen n (u,s1',s2') fv m s1 s2 d1 d2                                                                
                                                                            else throw (t',(u,s1',s2'))
                                             in  do
                                                 (u',d2') <- handle (trans n (unfold t d1) EmptyCtx fv ((f,(xs,t)):m) s1 s2 d1 d2) handler
                                                 return (if Fun f `elem` folds u' then (Unfold t' u',(f,(t,Unfold t' u')):d2') else (u',d2'))