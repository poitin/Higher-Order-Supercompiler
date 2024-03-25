-- Module Trans: program transformation

module Trans where

import Term
import Exception
import Prelude hiding ((<>))
import Data.Maybe
import Data.List
import Data.Tuple
             
-- supercompiler

super (t,d) = let t' = returnval (trans 1 t EmptyCtx (free t) [] [] [] d)
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

trans 0 t k fv m s1 s2 d = return (place t k)

trans n (Free x) (CaseCtx k bs) fv m s1 s2 d = do
                                               bs' <- mapM (\(c,xs,t) -> let xs' = renameVars fv xs
                                                                             t' = place (foldr concrete t xs') k                                                                      
                                                                             u = subst (Con c (map Free xs')) (abstract t' x)
                                                                         in do
                                                                            u' <- trans n u EmptyCtx (xs'++fv) m s1 s2 d
                                                                            return (c,xs,foldl abstract u' xs')) bs
                                               return (Case (Free x) bs')
trans n (Free x) k fv m s1 s2 d = transCtx n (Free x) k fv m s1 s2 d
trans n (Lambda x t) EmptyCtx fv m s1 s2 d = let x' = renameVar fv x
                                             in  do
                                                 t' <- trans n (concrete x' t) EmptyCtx (x':fv) m s1 s2 d
                                                 return (Lambda x' (abstract t' x'))
trans n (Lambda x t) (ApplyCtx k u) fv m s1 s2 d = trans n (subst u t) k fv m s1 s2 d
trans n (Lambda x t) (CaseCtx k bs) fv m s1 s2 d = error "Unapplied function in case selector"
trans n (Con c ts) EmptyCtx fv m s1 s2 d = do
                                           ts' <- mapM (\t -> trans n t EmptyCtx fv m s1 s2 d) ts
                                           return (Con c ts')
trans n (Con c ts) (ApplyCtx k u) fv m s1 s2 d = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
trans n (Con c ts) (CaseCtx k bs) fv m s1 s2 d = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                                    Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                                    Just (c',xs,t) -> trans n (foldr subst t ts) k fv m s1 s2 d
trans n (Apply t u) k fv m s1 s2 d = trans n t (ApplyCtx k u) fv m s1 s2 d
trans n (Case t bs) k fv m s1 s2 d = trans n t (CaseCtx k bs) fv m s1 s2 d
trans n (Fun f) k fv m s1 s2 d = fold n (place (Fun f) k) fv m s1 s2 d
trans n (Let x t u) k fv m s1 s2 d = trans n (subst t u) k fv m s1 s2 d
trans n (Unfold t u) k fv m s1 s2 d = fold n (place (Unfold t u) k) fv m s1 s2 d
trans n (Fold t u) k fv m s1 s2 d = do
                                    t' <- trans (n-1) u k fv [] [] [] d
                                    fold n t' fv m s1 s2 d

-- auxiliary function: transCtx n t k fv m s1 s2 d
-- n: transformation level
-- t: current term
-- k: context
-- fv: free variables
-- m: memoised terms
-- s1: generalisation environment
-- s2: generalisation environment
-- d: function definitions

transCtx n t EmptyCtx fv m s1 s2 d = return t
transCtx n t (ApplyCtx k u) fv m s1 s2 d = do
                                           u' <- trans n u EmptyCtx fv m s1 s2 d
                                           transCtx n (Apply t u') k fv m s1 s2 d
transCtx n t (CaseCtx k bs) fv m s1 s2 d = do
                                           bs' <- mapM (\(c,xs,t) -> let xs' = renameVars fv xs
                                                                     in do
                                                                        t' <- trans n (foldr concrete t xs') k (xs'++fv) m s1 s2 d
                                                                        return (c,xs,foldl abstract t' xs')) bs
                                           return (Case t bs')

transGen n (t,[],[]) fv m s1 s2 d = trans n t EmptyCtx fv m s1 s2 d
transGen n (t,(x,t'):s1',(_,t''):s2') fv m s1 s2 d = case [x' | (x',u) <- s1, (x'',u') <- s2, x'==x'' && u==t' && u'==t''] of
                                                        (x':_) -> transGen n (rename [(x,x')] t,s1',s2') (x':fv) m s1 s2 d
                                                        [] -> do
                                                              u <- trans n t' EmptyCtx fv m s1 s2 d
                                                              u' <- transGen n (t,s1',s2') (x:fv) m ((x,t'):s1) ((x,t''):s2) d
                                                              return (Let x u (abstract u' x))

fold n t fv m s1 s2 d = case [(f,xs,t') | (f,(xs,t')) <- m, r <- embedding t' t] of
                           ((f,xs,t'):_) -> let (u,s1',s2') = generalise [] t' t fv [] [] []
                                            in  case renaming t' u of
                                                   [] -> throw (t',(u,s1',s2'))
                                                   (r:rs) -> do
                                                             s <- mapM (\(x,t) -> do
                                                                                  t' <- trans n t EmptyCtx fv m s1 s2 d
                                                                                  return (x,t')) s2'
                                                             return (Fold (instantiate s (rename r (foldl (\t x -> Apply t (Free x)) (Fun f) xs))) t)
                           [] -> let f = renameVar (map fst m ++ map fst d) "g"
                                     xs = free t
                                     handler (t',(u,s1',s2')) = if   t==t'
                                                                 then transGen n (u,s1',s2') fv m s1 s2 d                                                                 
                                                                 else throw (t',(u,s1',s2'))
                                  in  do
                                      u' <- handle (trans n (unfold t d) EmptyCtx fv ((f,(xs,t)):m) s1 s2 d) handler
                                      return (if Fun f `elem` folds u' then Unfold (foldl (\t x -> Apply t (Free x)) (Fun f) xs) u' else u')
