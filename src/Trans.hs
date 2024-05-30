-- Module Trans: program transformation

module Trans where

import Term
import Exception
import Prelude hiding ((<>))
import Data.Maybe
import Data.List
import Data.Tuple
             
-- supercompiler

super (t,d) = let t' = returnval (sup t EmptyCtx (free t) [] [] [] d [])
              in  residualise t'

-- function: sup t k fv m s1 s2 d e
-- t: current term
-- k: context
-- fv: free variables
-- m: memoised terms
-- s1: generalisation environment
-- s2: generalisation environment
-- d: function definitions
-- e: previously transformed terms

sup (Free x) (CaseCtx k bs) fv m s1 s2 d e = let bs' = map (\(c,xs,t) -> (c,xs,instantiate [(x,foldl abstract (Con c (map Free xs)) xs)] t)) bs
                                             in  do
                                                 bs'' <- supBranches bs' k fv m s1 s2 d e
                                                 return (Case (Free x) bs'')
sup (Free x) k fv m s1 s2 d e = supCtx (Free x) k fv m s1 s2 d e
sup (Lambda x t) EmptyCtx fv m s1 s2 d e = let x' = renameVar fv x
                                           in  do
                                               t' <- sup (concrete x' t) EmptyCtx (x':fv) m s1 s2 d e
                                               return (Lambda x' (abstract t' x'))
sup (Lambda x t) (ApplyCtx k u) fv m s1 s2 d e = sup (subst u t) k fv m s1 s2 d e
sup (Lambda x t) (CaseCtx k bs) fv m s1 s2 d e = error "Unapplied function in case selector"
sup (Con c ts) EmptyCtx fv m s1 s2 d e = do
                                         ts' <- supArgs ts fv m s1 s2 d e
                                         return (Con c ts')
sup (Con c ts) (ApplyCtx k u) fv m s1 s2 d e = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
sup (Con c ts) (CaseCtx k bs) fv m s1 s2 d e = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                                  Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                                  Just (c',xs,t) -> sup (foldr subst t ts) k fv m s1 s2 d e
sup (Apply t u) k fv m s1 s2 d e = sup t (ApplyCtx k u) fv m s1 s2 d e
sup (Case t bs) k fv m s1 s2 d e = sup t (CaseCtx k bs) fv m s1 s2 d e
sup (Fun f) k fv m s1 s2 d e = let t = place (Fun f) k
                               in  case [rename r u | u@(Unfold _ t' _) <- e, r <- renaming t' t] of
                                      (u:_) -> return u
                                      [] -> fold t fv m s1 s2 d e
sup (Let x t u) k fv m s1 s2 d e = let x' = renameVar fv x
                                   in  do
                                       t' <- sup t EmptyCtx fv m s1 s2 d e
                                       u' <- sup (concrete x' u) k (x':fv) m s1 s2 d (unfolds t'++e)
                                       return (Let x t' (abstract u' x'))

supArgs [] fv m s1 s2 d e = return []
supArgs (t:ts) fv m s1 s2 d e = do
                                t' <- sup t EmptyCtx fv m s1 s2 d e
                                ts' <- supArgs ts fv m s1 s2 d (unfolds t'++e)
                                return (t':ts')

supBranches [] k fv m s1 s2 d e = return []
supBranches ((c,xs,t):bs) k fv m s1 s2 d e = let xs' = renameVars fv xs
                                             in do
                                                t' <- sup (foldr concrete t xs') k (xs'++fv) m s1 s2 d e
                                                bs' <- supBranches bs k fv m s1 s2 d (unfolds t'++e)
                                                return ((c,xs,foldl abstract t' xs'):bs')

supCtx t EmptyCtx fv m s1 s2 d e = return t
supCtx t (ApplyCtx k u) fv m s1 s2 d e = do
                                         u' <- sup u EmptyCtx fv m s1 s2 d e
                                         supCtx (Apply t u') k fv m s1 s2 d (unfolds u'++e)
supCtx t (CaseCtx k bs) fv m s1 s2 d e = do
                                         bs' <- supBranches bs k fv m s1 s2 d e
                                         return (Case t bs')

supFold [] fv m s1 s2 d e = return []
supFold ((x,t):s) fv m s1 s2 d e = do
                                   t' <- sup t EmptyCtx fv m s1 s2 d e
                                   s' <- supFold s fv m s1 s2 d (unfolds t'++e)
                                   return ((x,t'):s')

fold t fv m s1 s2 d e = case [(u,t',r) | (u,t') <- m, r <- embedding t' t] of
                           ((u,t',r):_) -> let (u',s1',s2') = generalise t' t fv s1 s2
                                           in  case renaming t' (rename r u') of
                                                  [] -> throw (u,(u',s1',s2'))
                                                  (r:_) -> do
                                                           s <- supFold s2' fv m s1 s2 d e
                                                           return (Fold (instantiate s (rename r u)))
                           [] -> let f = renameVar (fv ++ [f | (Unfold t _ _) <- e, let Fun f = redex t]) "f"
                                     xs = free t
                                     u = foldl (\t x -> Apply t (Free x)) (Fun f) xs
                                     handler (u',(t',s1',s2')) = if   u==u'
                                                                 then sup (makeLet s1' t') EmptyCtx (f:fv) m (s1++s1') (s2++s2') d e                                                               
                                                                 else throw (u',(t',s1',s2'))
                                   in  do
                                       t' <- handle (sup (unfold t d) EmptyCtx (f:fv) ((u,t):m) s1 s2 d e) handler
                                       return (Unfold u t t')

