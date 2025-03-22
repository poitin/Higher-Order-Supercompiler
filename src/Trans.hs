-- Module Trans: program transformation

module Trans where

import Term
import Exception
import Prelude hiding ((<>))
import Data.Maybe
import Data.List
import Data.Tuple

-- supercompiler

super (t,d) = let t' = returnval (sup t EmptyCtx (free t) [] d [])
              in  residualise t'

-- function: sup t k fv m d e
-- t: current term
-- k: context
-- fv: free variables
-- m: memoised terms
-- d: function definitions
-- e: previously transformed terms

sup (Free x) (CaseCtx k bs) fv m d e = let bs' = map (\(c,xs,t) -> (c,xs,instantiate [(x,foldl abstract (Con c (map Free xs)) xs)] t)) bs
                                       in  do
                                           bs'' <- supBranches bs' k fv m d e
                                           return (Case (Free x) bs'')
sup (Free x) k fv m d e = supCtx (Free x) k fv m d e
sup (Lambda x t) EmptyCtx fv m d e = let x' = renameVar fv x
                                     in  do
                                         t' <- sup (concrete x' t) EmptyCtx (x':fv) m d e
                                         return (Lambda x' (abstract t' x'))
sup (Lambda x t) (ApplyCtx k u) fv m d e = sup (subst u t) k fv m d e
sup (Lambda x t) (CaseCtx k bs) fv m d e = error "Unapplied function in case selector"
sup (Con c ts) EmptyCtx fv m d e = do
                                   ts' <- supArgs ts fv m d e
                                   return (Con c ts')
sup (Con c ts) (ApplyCtx k u) fv m d e = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
sup (Con c ts) (CaseCtx k bs) fv m d e = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                            Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                            Just (c',xs,t) -> sup (foldr subst t ts) k fv m d e
sup (Apply t u) k fv m d e = sup t (ApplyCtx k u) fv m d e
sup (Case t bs) k fv m d e = sup t (CaseCtx k bs) fv m d e
sup (Fun f) k fv m d e = let t = place (Fun f) k
                             in  case [rename (fromJust r) u | u@(Unfold _ t' _) <- e, let r = renaming t' t, isJust r] of
                                    (u:_) -> return u
                                    [] -> fold t fv m d e

supArgs [] fv m d e = return []
supArgs (t:ts) fv m d e = do
                          t' <- sup t EmptyCtx fv m d e
                          ts' <- supArgs ts fv m d (unfolds t'++e)
                          return (t':ts')

supBranches [] k fv m d e = return []
supBranches ((c,xs,t):bs) k fv m d e = let xs' = renameVars fv xs
                                       in do
                                          t' <- sup (foldr concrete t xs') k (xs'++fv) m d e
                                          bs' <- supBranches bs k fv m d (unfolds t'++e)
                                          return ((c,xs,foldl abstract t' xs'):bs')

supCtx t EmptyCtx fv m d e = return t
supCtx t (ApplyCtx k u) fv m d e = do
                                   u' <- sup u EmptyCtx fv m d e
                                   supCtx (Apply t u') k fv m d (unfolds u'++e)
supCtx t (CaseCtx k bs) fv m d e = do
                                   bs' <- supBranches bs k fv m d e
                                   return (Case t bs')

supLet [] t fv m d e = return t
supLet ((x,t):s') u fv m d e = do
                               t'' <- sup t EmptyCtx fv m d e
                               u' <- supLet s' u (x:fv) m d (unfolds t''++e)
                               return (Let x t'' (abstract u' x))

fold t fv m d e = case [(u,t') | (u,t') <- m, couple t' t] of
                     ((u,t'):_) -> let (u',s1,s2) = generalise t' t fv [] []
                                   in  case renaming t' u' of
                                          Nothing -> throw (u,(u',s1))
                                          Just r -> supLet s2 (Fold (rename r u)) fv m d e
                     [] -> let f = renameVar (fv ++ [f | (Unfold t _ _) <- e, let Fun f = redex t]) "f"
                               xs = free t
                               u = foldl (\t x -> Apply t (Free x)) (Fun f) xs
                               handler (u',(t',s')) = if   u==u'
                                                      then do
                                                           t'' <- sup t' EmptyCtx (fv++map fst s') m d e
                                                           supLet s' t'' (f:fv) m d (unfolds t''++e)                                                    
                                                      else throw (u',(t',s'))
                            in  do
                                t' <- handle (sup (unfold t d) EmptyCtx (f:fv) ((u,t):m) d e) handler
                                return (Unfold u t t')
