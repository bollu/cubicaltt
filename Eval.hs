{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Eval where

import Data.List
import Data.Maybe (fromMaybe)
import Data.Map (Map,(!),mapWithKey,assocs,filterWithKey
                ,elems,intersectionWith,intersection,keys
                ,member,notMember,empty)
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Connections as C
import CTT

-----------------------------------------------------------------------
-- Lookup functions

look :: String -> Env -> Val
look x (Env (Upd y rho,v:vs,fs,os)) | x == y = v
                                    | otherwise = look x (Env (rho,vs,fs,os))
look x r@(Env (Def _ decls rho,vs,fs,C.Nameless os)) = case lookup x decls of
  Just (_,t) -> eval r t
  Nothing    -> look x (Env (rho,vs,fs,C.Nameless os))
look x (Env (Sub _ rho,vs,_:fs,os)) = look x (Env (rho,vs,fs,os))
look x (Env (Empty,_,_,_)) = error $ "look: not found " ++ show x

lookType :: String -> Env -> Val
lookType x (Env (Upd y rho,v:vs,fs,os))
  | x /= y        = lookType x (Env (rho,vs,fs,os))
  | VVar _ a <- v = a
  | otherwise     = error ""
lookType x r@(Env (Def _ decls rho,vs,fs,os)) = case lookup x decls of
  Just (a,_) -> eval r a
  Nothing -> lookType x (Env (rho,vs,fs,os))
lookType x (Env (Sub _ rho,vs,_:fs,os)) = lookType x (Env (rho,vs,fs,os))
lookType x (Env (Empty,_,_,_))          = error $ "lookType: not found " ++ show x

lookName :: C.Name -> Env -> C.Formula
lookName i (Env (Upd _ rho,v:vs,fs,os)) = lookName i (Env (rho,vs,fs,os))
lookName i (Env (Def _ _ rho,vs,fs,os)) = lookName i (Env (rho,vs,fs,os))
lookName i (Env (Sub j rho,vs,phi:fs,os)) | i == j    = phi
                                          | otherwise = lookName i (Env (rho,vs,fs,os))
lookName i _ = error $ "lookName: not found " ++ show i


  -----------------------------------------------------------------------
-- Nominal instances

instance C.Nominal Ctxt where
  support _ = []
  act e _   = e
  swap e _  = e

instance C.Nominal Env where
  support (Env (rho,vs,fs,os)) = C.support (rho,vs,fs,os)
  act (Env (rho,vs,fs,os)) iphi = Env $ C.act (rho,vs,fs,os) iphi
  swap (Env (rho,vs,fs,os)) ij = Env $ C.swap (rho,vs,fs,os) ij

instance C.Nominal Val where
  support v = case v of
    VU                      -> []
    Ter _ e                 -> C.support e
    VPi u v                 -> C.support [u,v]
    --VComp a u ts            -> C.support (a,u,ts)
    -- VPathP a v0 v1          -> C.support [a,v0,v1]
    -- VPLam i v               -> i `delete` C.support v
    VSigma u v              -> C.support (u,v)
    VPair u v               -> C.support (u,v)
    VFst u                  -> C.support u
    VSnd u                  -> C.support u
    VCon _ vs               -> C.support vs
    VPCon _ a vs phis       -> C.support (a,vs,phis)
    -- VHComp a u ts           -> C.support (a,u,ts)
    VVar _ v                -> C.support v
    VOpaque _ v             -> C.support v
    VApp u v                -> C.support (u,v)
    VLam _ u v              -> C.support (u,v)
    -- VAppFormula u phi       -> C.support (u,phi)
    VSplit u v              -> C.support (u,v)
    -- VGlue a ts              -> C.support (a,ts)
    -- VGlueElem a ts          -> C.support (a,ts)
    -- VUnGlueElem a ts        -> C.support (a,ts)
    -- VCompU a ts             -> C.support (a,ts)
    -- VUnGlueElemU a b es     -> C.support (a,b,es)
    -- VIdPair u us            -> C.support (u,us)
    VId a u v               -> C.support (a,u,v)
    VIdJ a u c d x p        -> C.support [a,u,c,d,x,p]

  act u (i, phi) | i `notElem` C.support u = u
                 | otherwise =
    let acti :: C.Nominal a => a -> a
        acti u = C.act u (i, phi)
        sphi = C.support phi
    in case u of
         VU           -> VU
         Ter t e      -> Ter t (acti e)
         VPi a f      -> VPi (acti a) (acti f)
         -- VComp a v ts -> compLine (acti a) (acti v) (acti ts)
         -- VPathP a u v -> VPathP (acti a) (acti u) (acti v)
         -- VPLam j v | j == i -> u
         --           | j `notElem` sphi -> VPLam j (acti v)
         --           | otherwise -> VPLam k (acti (v `C.swap` (j,k)))
         --      where k = C.fresh (v,C.Atom i,phi)
         VSigma a f              -> VSigma (acti a) (acti f)
         VPair u v               -> VPair (acti u) (acti v)
         VFst u                  -> fstVal (acti u)
         VSnd u                  -> sndVal (acti u)
         VCon c vs               -> VCon c (acti vs)
         -- VPCon c a vs phis       -> pcon c (acti a) (acti vs) (acti phis)
         -- VHComp a u us           -> hComp (acti a) (acti u) (acti us)
         VVar x v                -> VVar x (acti v)
         VOpaque x v             -> VOpaque x (acti v)
         -- VAppFormula u psi       -> acti u @@ acti psi
         VApp u v                -> app (acti u) (acti v)
         VLam x t u              -> VLam x (acti t) (acti u)
         VSplit u v              -> app (acti u) (acti v)
         -- VGlue a ts              -> glue (acti a) (acti ts)
         -- VGlueElem a ts          -> glueElem (acti a) (acti ts)
         -- VUnGlueElem a ts        -> unglueElem (acti a) (acti ts)
         -- VUnGlueElemU a b es     -> unGlueU (acti a) (acti b) (acti es)
         -- VCompU a ts             -> compUniv (acti a) (acti ts)
         -- VIdPair u us            -> VIdPair (acti u) (acti us)
         VId a u v               -> VId (acti a) (acti u) (acti v)
         -- VIdJ a u c d x p        ->
         --   idJ (acti a) (acti u) (acti c) (acti d) (acti x) (acti p)

  -- This increases efficiency as it won't trigger computation.
  swap u ij@(i,j) =
    let sw :: C.Nominal a => a -> a
        sw u = C.swap u ij
    in case u of
         VU                      -> VU
         Ter t e                 -> Ter t (sw e)
         VPi a f                 -> VPi (sw a) (sw f)
         -- VComp a v ts            -> VComp (sw a) (sw v) (sw ts)
         -- VPathP a u v            -> VPathP (sw a) (sw u) (sw v)
         -- VPLam k v               -> VPLam (C.swapName k ij) (sw v)
         VSigma a f              -> VSigma (sw a) (sw f)
         VPair u v               -> VPair (sw u) (sw v)
         VFst u                  -> VFst (sw u)
         VSnd u                  -> VSnd (sw u)
         VCon c vs               -> VCon c (sw vs)
         VPCon c a vs phis       -> VPCon c (sw a) (sw vs) (sw phis)
         -- VHComp a u us           -> VHComp (sw a) (sw u) (sw us)
         VVar x v                -> VVar x (sw v)
         VOpaque x v             -> VOpaque x (sw v)
         -- VAppFormula u psi       -> VAppFormula (sw u) (sw psi)
         VApp u v                -> VApp (sw u) (sw v)
         VLam x u v              -> VLam x (sw u) (sw v)
         VSplit u v              -> VSplit (sw u) (sw v)
         -- VGlue a ts              -> VGlue (sw a) (sw ts)
         -- VGlueElem a ts          -> VGlueElem (sw a) (sw ts)
         -- VUnGlueElem a ts        -> VUnGlueElem (sw a) (sw ts)
         -- VUnGlueElemU a b es     -> VUnGlueElemU (sw a) (sw b) (sw es)
         -- VCompU a ts             -> VCompU (sw a) (sw ts)
         -- VIdPair u us            -> VIdPair (sw u) (sw us)
         VId a u v               -> VId (sw a) (sw u) (sw v)
         VIdJ a u c d x p        ->
           VIdJ (sw a) (sw u) (sw c) (sw d) (sw x) (sw p)

-----------------------------------------------------------------------
-- The evaluator

eval :: Env -> Ter -> Val
eval rho@(Env (_,_,_,C.Nameless os)) v = case v of
  U                   -> VU
  App r s             -> app (eval rho r) (eval rho s)
  Var i
    | i `Set.member` os -> VOpaque i (lookType i rho)
    | otherwise       -> look i rho
  Pi t@(Lam _ a _)    -> VPi (eval rho a) (eval rho t)
  Sigma t@(Lam _ a _) -> VSigma (eval rho a) (eval rho t)
  Pair a b            -> VPair (eval rho a) (eval rho b)
  Fst a               -> fstVal (eval rho a)
  Snd a               -> sndVal (eval rho a)
  Where t decls       -> eval (defWhere decls rho) t
  Con name ts         -> VCon name (map (eval rho) ts)
  -- PCon name a ts phis ->
  --   pcon name (eval rho a) (map (eval rho) ts) (map (evalFormula rho) phis)
  Lam{}               -> Ter v rho
  Split{}             -> Ter v rho
  Sum{}               -> Ter v rho
  -- HSum{}              -> Ter v rho
  Undef{}             -> Ter v rho
  Hole{}              -> Ter v rho
  -- PathP a e0 e1       -> VPathP (eval rho a) (eval rho e0) (eval rho e1)
  -- PLam i t            -> let j = C.fresh rho
  --                        in VPLam j (eval (sub (i,C.Atom j) rho) t)
  -- AppFormula e phi    -> eval rho e @@ evalFormula rho phi
  -- Comp a t0 ts        ->
  --   compLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  -- HComp a t0 ts       ->
  --   hComp (eval rho a) (eval rho t0) (evalSystem rho ts)
  -- Fill a t0 ts        ->
  --   fillLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  -- Glue a ts           -> glue (eval rho a) (evalSystem rho ts)
  -- GlueElem a ts       -> glueElem (eval rho a) (evalSystem rho ts)
  -- UnGlueElem a ts     -> unglueElem (eval rho a) (evalSystem rho ts)
  Id a r s            -> VId (eval rho a) (eval rho r) (eval rho s)
  -- IdPair b ts         -> VIdPair (eval rho b) (evalSystem rho ts)
  -- IdJ a t c d x p     -> idJ (eval rho a) (eval rho t) (eval rho c)
  --                            (eval rho d) (eval rho x) (eval rho p)
  _                   -> error $ "Cannot evaluate " ++ show v

evals :: Env -> [(Ident,Ter)] -> [(Ident,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

evalFormula :: Env -> C.Formula -> C.Formula
evalFormula rho phi = case phi of
  C.Atom i         -> lookName i rho
  C.NegAtom i      -> C.negFormula (lookName i rho)
  phi1 C.:/\: phi2 -> evalFormula rho phi1 `C.andFormula` evalFormula rho phi2
  phi1 C.:\/: phi2 -> evalFormula rho phi1 `C.orFormula` evalFormula rho phi2
  _              -> phi

evalSystem :: Env -> C.System Ter -> C.System Val
evalSystem rho ts =
  let out = concat [ let betas = C.meetss [ C.invFormula (lookName i rho) d
                                        | (i,d) <- assocs alpha ]
                     in [ (beta,eval (rho `C.face` beta) talpha) | beta <- betas ]
                   | (alpha,talpha) <- assocs ts ]
  in C.mkSystem out

app :: Val -> Val -> Val
app u v = case (u,v) of
  (Ter (Lam x _ t) e,_)               -> eval (upd (x,v) e) t
  (Ter (Split _ _ _ nvs) e,VCon c vs) -> case lookupBranch c nvs of
    Just (OBranch _ xs t) -> eval (upds (zip xs vs) e) t
    _     -> error $ "app: missing case in split for " ++ c
  -- (Ter (Split _ _ _ nvs) e,VPCon c _ us phis) -> case lookupBranch c nvs of
  --   Just (PBranch _ xs is t) -> eval (subs (zip is phis) (upds (zip xs us) e)) t
  --   _ -> error $ "app: missing case in split for " ++ c
  -- (Ter (Split _ _ ty hbr) e,VHComp a w ws) -> case eval e ty of
  --   VPi _ f -> let j   = C.fresh (e,v)
  --                  wsj = Map.map (@@ j) ws
  --                  w'  = app u w
  --                  ws' = mapWithKey (\alpha -> app (u `C.face` alpha)) wsj
  --                  -- a should be constant
  --              in comp j (app f (fill j a w wsj)) w' ws'
  --   _ -> error $ "app: Split annotation not a Pi type " ++ show u
  (Ter Split{} _,_) | isNeutral v         -> VSplit u v
  -- (VComp (VPLam i (VPi a f)) li0 ts,vi1) ->
  --   let j       = C.fresh (u,vi1)
  --       (aj,fj) = (a,f) `C.swap` (i,j)
  --       tsj     = Map.map (@@ j) ts
  --       v       = transFillNeg j aj vi1
  --       vi0     = transNeg j aj vi1
  --   in comp j (app fj v) (app li0 vi0)
  --             (intersectionWith app tsj (C.border v tsj))
  -- _ | isNeutral u       -> VApp u v
  -- _                     -> error $ "app \n  " ++ show u ++ "\n  " ++ show v

fstVal, sndVal :: Val -> Val
fstVal (VPair a b)     = a
fstVal u | isNeutral u = VFst u
fstVal u               = error $ "fstVal: " ++ show u ++ " is not neutral."
sndVal (VPair a b)     = b
sndVal u | isNeutral u = VSnd u
sndVal u               = error $ "sndVal: " ++ show u ++ " is not neutral."

-- infer the type of a neutral value
inferType :: Val -> Val
inferType v = case v of
  VVar _ t -> t
  VOpaque _ t -> t
  Ter (Undef _ t) rho -> eval rho t
  VFst t -> case inferType t of
    VSigma a _ -> a
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSnd t -> case inferType t of
    VSigma _ f -> app f (VFst t)
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSplit s@(Ter (Split _ _ t _) rho) v1 -> case eval rho t of
    VPi _ f -> app f v1
    ty      -> error $ "inferType: Pi type expected for split annotation in "
               ++ show v ++ ", got " ++ show ty
  VApp t0 t1 -> case inferType t0 of
    VPi _ f -> app f t1
    ty      -> error $ "inferType: expected Pi type for " ++ show v
               ++ ", got " ++ show ty
  -- VAppFormula t phi -> case inferType t of
  --   VPathP a _ _ -> a @@ phi
  --   ty         -> error $ "inferType: expected PathP type for " ++ show v
  --                 ++ ", got " ++ show ty
--  VComp a _ _ -> a @@ C.One
--  VUnGlueElem _ b _  -> b   -- This is wrong! Store the type??
--  VUnGlueElemU _ b _ -> b
  VIdJ _ _ c _ x p -> app (app c x) p
  _ -> error $ "inferType: not neutral " ++ show v

-- (@@) :: C.ToFormula a => Val -> a -> Val
-- -- (VPLam i u) @@ phi         = u `C.act` (i,C.toFormula phi)
-- v@(Ter Hole{} _) @@ phi    = VAppFormula v (C.toFormula phi)
-- -- v @@ phi | isNeutral v     = case (inferType v,C.toFormula phi) of
-- --   (VPathP _ a0 _,C.Dir 0) -> a0
-- --   (VPathP _ _ a1,C.Dir 1) -> a1
-- --   _                    -> VAppFormula v (C.toFormula phi)
-- v @@ phi                   = error $ "(@@): " ++ show v ++ " should be neutral."
-- 
-- Applying a *C.fresh* name.
-- (@@@) :: Val -> C.Name -> Val
-- (VPLam i u) @@@ j = u `C.swap` (i,j)
-- v @@@ j           = VAppFormula v (C.toFormula j)


-------------------------------------------------------------------------------
-- Composition and filling

-- comp :: C.Name -> Val -> Val -> C.System Val -> Val
-- comp i a u ts | C.eps `member` ts = (ts ! C.eps) `C.face` (i C.~> 1)
-- comp i a u ts = case a of
--   -- VPathP p v0 v1 -> let j = C.fresh (C.Atom i,a,u,ts)
--   --                   in VPLam j $ comp i (p @@ j) (u @@ j) $
--   --                        C.insertsSystem [(j C.~> 0,v0),(j C.~> 1,v1)] (Map.map (@@ j) ts)
--   -- VId b v0 v1 -> case u of
--   --   VIdPair r _ | all isIdPair (elems ts) ->
--   --     let j = C.fresh (C.Atom i,a,u,ts)
--   --         VIdPair z _ @@@ phi = z @@ phi
--   --         sys (VIdPair _ ws)  = ws
--   --         w = VPLam j $ comp i b (r @@ j) $
--   --                         C.insertsSystem [(j C.~> 0,v0),(j C.~> 1,v1)]
--   --                           (Map.map (@@@ j) ts)
--   --     in VIdPair w (C.joinSystem (Map.map sys (ts `C.face` (i C.~> 1))))
--   --   _ -> VComp (VPLam i a) u (Map.map (VPLam i) ts)
--   VSigma a f -> VPair ui1 comp_u2
--     where (t1s, t2s) = (Map.map fstVal ts, Map.map sndVal ts)
--           (u1,  u2)  = (fstVal u, sndVal u)
--           fill_u1    = fill i a u1 t1s
--           ui1        = comp i a u1 t1s
--           comp_u2    = comp i (app f fill_u1) u2 t2s
--   VPi{} -> VComp (VPLam i a) u (Map.map (VPLam i) ts)
--   VU -> compUniv u (Map.map (VPLam i) ts)
--   -- VCompU a es | not (isNeutralU i es u ts)  -> compU i a es u ts
--   -- VGlue b equivs | not (isNeutralGlue i equivs u ts) -> compGlue i b equivs u ts
--   Ter (Sum _ _ nass) env -> case u of
--     VCon n us | all isCon (elems ts) -> case lookupLabel n nass of
--       Just as -> let tsus = C.transposeSystemAndList (Map.map unCon ts) us
--                  in VCon n $ comps i as env tsus
--       Nothing -> error $ "comp: missing constructor in labelled sum " ++ n
--     -- _ -> VComp (VPLam i a) u (Map.map (VPLam i) ts)
--   -- Ter (HSum _ _ nass) env -> compHIT i a u ts
--   -- _ -> VComp (VPLam i a) u (Map.map (VPLam i) ts)

-- compNeg :: C.Name -> Val -> Val -> C.System Val -> Val
-- compNeg i a u ts = comp i (a `C.sym` i) u (ts `C.sym` i)
-- 
-- compLine :: Val -> Val -> C.System Val -> Val
-- compLine a u ts = comp i (a @@ i) u (Map.map (@@ i) ts)
--   where i = C.fresh (a,u,ts)
-- 
-- compConstLine :: Val -> Val -> C.System Val -> Val
-- compConstLine a u ts = comp i a u (Map.map (@@ i) ts)
--   where i = C.fresh (a,u,ts)
-- 
-- comps :: C.Name -> [(Ident,Ter)] -> Env -> [(C.System Val,Val)] -> [Val]
-- comps i []         _ []         = []
-- comps i ((x,a):as) e ((ts,u):tsus) =
--   let v   = fill i (eval e a) u ts
--       vi1 = comp i (eval e a) u ts
--       vs  = comps i as (upd (x,v) e) tsus
--   in vi1 : vs
-- comps _ _ _ _ = error "comps: different lengths of types and values"
-- 
-- fill :: C.Name -> Val -> Val -> C.System Val -> Val
-- fill i a u ts =
--   comp j (a `C.conj` (i,j)) u (C.insertSystem (i C.~> 0) u (ts `C.conj` (i,j)))
--   where j = C.fresh (C.Atom i,a,u,ts)
-- 
-- fillNeg :: C.Name -> Val -> Val -> C.System Val -> Val
-- fillNeg i a u ts = (fill i (a `C.sym` i) u (ts `C.sym` i)) `C.sym` i
-- 
-- fillLine :: Val -> Val -> C.System Val -> Val
-- fillLine a u ts = VPLam i $ fill i (a @@ i) u (Map.map (@@ i) ts)
--   where i = C.fresh (a,u,ts)

-- fills :: C.Name -> [(Ident,Ter)] -> Env -> [(C.System Val,Val)] -> [Val]
-- fills i []         _ []         = []
-- fills i ((x,a):as) e ((ts,u):tsus) =
--   let v  = fill i (eval e a) ts u
--       vs = fills i as (Upd e (x,v)) tsus
--   in v : vs
-- fills _ _ _ _ = error "fills: different lengths of types and values"


-----------------------------------------------------------
-- Transport and squeeze (defined using comp)

-- trans :: C.Name -> Val -> Val -> Val
-- trans i v0 v1 = comp i v0 v1 empty
-- 
-- transNeg :: C.Name -> Val -> Val -> Val
-- transNeg i a u = trans i (a `C.sym` i) u
-- 
-- transLine :: Val -> Val -> Val
-- transLine u v = trans i (u @@ i) v
--   where i = C.fresh (u,v)
-- 
-- transNegLine :: Val -> Val -> Val
-- transNegLine u v = transNeg i (u @@ i) v
--   where i = C.fresh (u,v)
-- 
-- -- TODO: define in terms of comps?
-- transps :: C.Name -> [(Ident,Ter)] -> Env -> [Val] -> [Val]
-- transps i []         _ []     = []
-- transps i ((x,a):as) e (u:us) =
--   let v   = transFill i (eval e a) u
--       vi1 = trans i (eval e a) u
--       vs  = transps i as (upd (x,v) e) us
--   in vi1 : vs
-- transps _ _ _ _ = error "transps: different lengths of types and values"
-- 
-- transFill :: C.Name -> Val -> Val -> Val
-- transFill i a u = fill i a u empty
-- 
-- transFillNeg :: C.Name -> Val -> Val -> Val
-- transFillNeg i a u = (transFill i (a `C.sym` i) u) `C.sym` i

-- Given u of type a "squeeze i a u" connects in the direction i
-- trans i a u(i=0) to u(i=1)
-- squeeze :: C.Name -> Val -> Val -> Val
-- squeeze i a u = comp j (a `C.disj` (i,j)) u $ C.mkSystem [ (i C.~> 1, ui1) ]
--   where j   = C.fresh (C.Atom i,a,u)
--         ui1 = u `C.face` (i C.~> 1)
-- 
-- squeezes :: C.Name -> [(Ident,Ter)] -> Env -> [Val] -> [Val]
-- squeezes i xas e us = comps j xas (e `C.disj` (i,j)) us'
--   where j   = C.fresh (us,e,C.Atom i)
--         us' = [ (C.mkSystem [(i C.~> 1, u `C.face` (i C.~> 1))],u) | u <- us ]
-- 

-------------------------------------------------------------------------------
-- | Id

-- idJ :: Val -> Val -> Val -> Val -> Val -> Val -> Val
-- idJ a v c d x p = case p of
--   VIdPair w ws -> comp i (app (app c (w @@ i)) w') d
--                     (C.border d (C.shape ws))
--     where w' = VIdPair (VPLam j $ w @@ (C.Atom i C.:/\: C.Atom j))
--                   (C.insertSystem (i C.~> 0) v ws)
--           i:j:_ = C.freshs [a,v,c,d,x,p]
--   _ -> VIdJ a v c d x p

-- isIdPair :: Val -> Bool
-- isIdPair VIdPair{} = True
-- isIdPair _         = False


-------------------------------------------------------------------------------
-- | HITs

-- pcon :: LIdent -> Val -> [Val] -> [C.Formula] -> Val
-- pcon c a@(Ter (HSum _ _ lbls) rho) us phis = case lookupPLabel c lbls of
--   Just (tele,is,ts) | C.eps `member` vs -> vs ! C.eps
--                     | otherwise       -> VPCon c a us phis
--     where rho' = subs (zip is phis) (updsTele tele us rho)
--           vs   = evalSystem rho' ts
--   Nothing           -> error "pcon"
-- pcon c a us phi     = VPCon c a us phi

-- compHIT :: C.Name -> Val -> Val -> C.System Val -> Val
-- compHIT i a u us
--   | isNeutral u || isNeutralSystem us =
--       VComp (VPLam i a) u (Map.map (VPLam i) us)
--   | otherwise =
--       hComp (a `C.face` (i C.~> 1)) (transpHIT i a u) $
--         mapWithKey (\alpha uAlpha ->
--                      VPLam i $ squeezeHIT i (a `C.face` alpha) uAlpha) us

-- Given u of type a(i=0), transpHIT i a u is an element of a(i=1).
-- transpHIT :: C.Name -> Val -> Val -> Val
-- transpHIT i a@(Ter (HSum _ _ nass) env) u =
--  let j = C.fresh (a,u)
--      aij = C.swap a (i,j)
--  in
--  case u of
--   VCon n us -> case lookupLabel n nass of
--     Just as -> VCon n (transps i as env us)
--     Nothing -> error $ "transpHIT: missing constructor in labelled sum " ++ n
--   VPCon c _ ws0 phis -> case lookupLabel c nass of
--     Just as -> pcon c (a `C.face` (i C.~> 1)) (transps i as env ws0) phis
--     Nothing -> error $ "transpHIT: missing path constructor " ++ c
--   VHComp _ v vs ->
--     hComp (a `C.face` (i C.~> 1)) (transpHIT i a v) $
--       mapWithKey (\alpha vAlpha ->
--                    VPLam j $ transpHIT j (aij `C.face` alpha) (vAlpha @@ j)) vs
--   _ -> error $ "transpHIT: neutral " ++ show u
-- 
-- given u(i) of type a(i) "squeezeHIT i a u" connects in the direction i
-- transHIT i a u(i=0) to u(i=1) in a(1)
-- squeezeHIT :: C.Name -> Val -> Val -> Val
-- squeezeHIT i a@(Ter (HSum _ _ nass) env) u =
--  let j = C.fresh (a,u)
--  in
--  case u of
--   VCon n us -> case lookupLabel n nass of
--     Just as -> VCon n (squeezes i as env us)
--     Nothing -> error $ "squeezeHIT: missing constructor in labelled sum " ++ n
--   VPCon c _ ws0 phis -> case lookupLabel c nass of
--     Just as -> pcon c (a `C.face` (i C.~> 1)) (squeezes i as env ws0) phis
--     Nothing -> error $ "squeezeHIT: missing path constructor " ++ c
--   VHComp _ v vs -> hComp (a `C.face` (i C.~> 1)) (squeezeHIT i a v) $
--       mapWithKey
--         (\alpha vAlpha -> case Map.lookup i alpha of
--           Nothing   -> VPLam j $ squeezeHIT i (a `C.face` alpha) (vAlpha @@ j)
--           Just C.Zero -> VPLam j $ transpHIT i
--                          (a `C.face` (Map.delete i alpha)) (vAlpha @@ j)
--           Just C.One  -> vAlpha)
--         vs
--   _ -> error $ "squeezeHIT: neutral " ++ show u
-- 
-- hComp :: Val -> Val -> C.System Val -> Val
-- hComp a u us | C.eps `member` us = (us ! C.eps) @@ C.One
--              | otherwise       = VHComp a u us

-------------------------------------------------------------------------------
-- | Glue

-- An equivalence for a type a is a triple (t,f,p) where
-- t : U
-- f : t -> a
-- p : (x : a) -> isContr ((y:t) * Id a x (f y))
-- with isContr c = (z : c) * ((z' : C) -> Id c z z')

-- Extraction functions for getting a, f, s and t:
equivDom :: Val -> Val
equivDom = fstVal

equivFun :: Val -> Val
equivFun = fstVal . sndVal

equivContr :: Val -> Val
equivContr =  sndVal . sndVal

-- glue :: Val -> C.System Val -> Val
-- glue b ts | C.eps `member` ts = equivDom (ts ! C.eps)
--           | otherwise       = VGlue b ts
-- 
-- glueElem :: Val -> C.System Val -> Val
-- glueElem v us | C.eps `member` us = us ! C.eps
-- glueElem v us = VGlueElem v us
-- 
-- unglueElem :: Val -> C.System Val -> Val
-- unglueElem w isos | C.eps `member` isos = app (equivFun (isos ! C.eps)) w
--                   | otherwise         = case w of
--                                           VGlueElem v us -> v
--                                           _ -> VUnGlueElem w isos
-- 
-- unGlue :: Val -> Val -> C.System Val -> Val
-- unGlue w b equivs | C.eps `member` equivs = app (equivFun (equivs ! C.eps)) w
--                   | otherwise           = case w of
--                                             VGlueElem v us -> v
--                                             _ -> error ("unglue: neutral" ++ show w)

isNeutralGlue :: C.Name -> C.System Val -> Val -> C.System Val -> Bool
isNeutralGlue i equivs u0 ts = (C.eps `notMember` equivsi0 && isNeutral u0) ||
  any (\(alpha,talpha) ->
           C.eps `notMember` (equivs `C.face` alpha) && isNeutral talpha)
    (assocs ts)
  where equivsi0 = equivs `C.face` (i C.~> 0)

-- this is exactly the same as isNeutralGlue?
isNeutralU :: C.Name -> C.System Val -> Val -> C.System Val -> Bool
isNeutralU i eqs u0 ts = (C.eps `notMember` eqsi0 && isNeutral u0) ||
  any (\(alpha,talpha) ->
           C.eps `notMember` (eqs `C.face` alpha) && isNeutral talpha)
    (assocs ts)
  where eqsi0 = eqs `C.face` (i C.~> 0)

-- -- Extend the system ts to a total element in b given q : isContr b
-- extend :: Val -> Val -> C.System Val -> Val
-- extend b q ts = comp i b (fstVal q) ts'
--   where i = C.fresh (b,q,ts)
--         ts' = mapWithKey
--                 (\alpha tAlpha -> app ((sndVal q) `C.face` alpha) tAlpha @@ i) ts
-- 
-- psi/b corresponds to ws
-- b0    corresponds to wi0
-- a0    corresponds to vi0
-- psi/a corresponds to vs
-- a1'   corresponds to vi1'
-- equivs' corresponds to delta
-- ti1'  corresponds to usi1'
-- compGlue :: C.Name -> Val -> C.System Val -> Val -> C.System Val -> Val
-- compGlue i a equivs wi0 ws = glueElem vi1 usi1
--   where ai1 = a `C.face` (i C.~> 1)
--         vs  = mapWithKey
--                 (\alpha wAlpha ->
--                   unGlue wAlpha (a `C.face` alpha) (equivs `C.face` alpha)) ws
-- 
--         vsi1 = vs `C.face` (i C.~> 1) -- same as: C.border vi1 vs
--         vi0  = unGlue wi0 (a `C.face` (i C.~> 0)) (equivs `C.face` (i C.~> 0)) -- in a(i0)
-- 
--         vi1'  = comp i a vi0 vs           -- in a(i1)
-- 
--         equivsI1 = equivs `C.face` (i C.~> 1)
--         equivs'  = filterWithKey (\alpha _ -> i `notMember` alpha) equivs
-- 
--         us'    = mapWithKey (\gamma equivG ->
--                    fill i (equivDom equivG) (wi0 `C.face` gamma) (ws `C.face` gamma))
--                  equivs'
--         usi1'  = mapWithKey (\gamma equivG ->
--                    comp i (equivDom equivG) (wi0 `C.face` gamma) (ws `C.face` gamma))
--                  equivs'
-- 
--         -- path in ai1 between vi1 and f(i1) usi1' on equivs'
--         ls'    = mapWithKey (\gamma equivG ->
--                    pathComp i (a `C.face` gamma) (vi0 `C.face` gamma)
--                      (equivFun equivG `app` (us' ! gamma)) (vs `C.face` gamma))
--                  equivs'
-- 
--         fibersys = intersectionWith VPair usi1' ls' -- on equivs'
-- 
--         wsi1 = ws `C.face` (i C.~> 1)
--         fibersys' = mapWithKey
--           (\gamma equivG ->
--             let fibsgamma = intersectionWith (\ x y -> VPair x (constPath y))
--                               (wsi1 `C.face` gamma) (vsi1 `C.face` gamma)
--             in extend (mkFiberType (ai1 `C.face` gamma) (vi1' `C.face` gamma) equivG)
--                  (app (equivContr equivG) (vi1' `C.face` gamma))
--                  (fibsgamma `C.unionSystem` (fibersys `C.face` gamma))) equivsI1
-- 
--         vi1 = compConstLine ai1 vi1'
--                 (Map.map sndVal fibersys' `C.unionSystem` Map.map constPath vsi1)
-- 
--         usi1 = Map.map fstVal fibersys'

-- mkFiberType :: Val -> Val -> Val -> Val
-- mkFiberType a x equiv = eval rho $
--   Sigma $ Lam "y" tt (PathP (PLam (C.Name "_") ta) tx (App tf ty))
--   where [ta,tx,ty,tf,tt] = map Var ["a","x","y","f","t"]
--         rho = upds [("a",a),("x",x),("f",equivFun equiv)
--                    ,("t",equivDom equiv)] emptyEnv
-- 
-- Assumes u' : A is a solution of us + (i0 -> u0)
-- The output is an L-path in A(i1) between comp i u0 us and u'(i1)
-- pathComp :: C.Name -> Val -> Val -> Val -> C.System Val -> Val
-- pathComp i a u0 u' us = VPLam j $ comp i a u0 us'
--   where j   = C.fresh (C.Atom i,a,us,u0,u')
--         us' = C.insertsSystem [(j C.~> 1, u')] us
-- 
-------------------------------------------------------------------------------
-- | Composition in the Universe

-- any path between types define an equivalence
-- eqFun :: Val -> Val -> Val
-- eqFun = transNegLine
-- 
-- unGlueU :: Val -> Val -> C.System Val -> Val
-- unGlueU w b es | C.eps `Map.member` es = eqFun (es ! C.eps) w
--                | otherwise           = case w of
--                                         VGlueElem v us   -> v
--                                         _ -> VUnGlueElemU w b es
-- 
-- compUniv :: Val -> C.System Val -> Val
-- compUniv b es | C.eps `Map.member` es = (es ! C.eps) @@ C.One
--               | otherwise           = VCompU b es
-- 
-- compU :: C.Name -> Val -> C.System Val -> Val -> C.System Val -> Val
-- compU i a eqs wi0 ws = glueElem vi1 usi1
--   where ai1 = a `C.face` (i C.~> 1)
--         vs  = mapWithKey
--                 (\alpha wAlpha ->
--                   unGlueU wAlpha (a `C.face` alpha) (eqs `C.face` alpha)) ws
-- 
--         vsi1 = vs `C.face` (i C.~> 1) -- same as: C.border vi1 vs
--         vi0  = unGlueU wi0 (a `C.face` (i C.~> 0)) (eqs `C.face` (i C.~> 0)) -- in a(i0)
-- 
--         vi1'  = comp i a vi0 vs           -- in a(i1)
-- 
--         eqsI1 = eqs `C.face` (i C.~> 1)
--         eqs'  = filterWithKey (\alpha _ -> i `notMember` alpha) eqs
-- 
--         us'    = mapWithKey (\gamma eqG ->
--                    fill i (eqG @@ C.One) (wi0 `C.face` gamma) (ws `C.face` gamma))
--                  eqs'
--         usi1'  = mapWithKey (\gamma eqG ->
--                    comp i (eqG @@ C.One) (wi0 `C.face` gamma) (ws `C.face` gamma))
--                  eqs'
-- 
--         -- path in ai1 between vi1 and f(i1) usi1' on eqs'
--         ls'    = mapWithKey (\gamma eqG ->
--                    pathComp i (a `C.face` gamma) (vi0 `C.face` gamma)
--                      (eqFun eqG (us' ! gamma)) (vs `C.face` gamma))
--                  eqs'
-- 
--         fibersys = intersectionWith (\ x y -> (x,y)) usi1' ls' -- on eqs'
-- 
--         wsi1 = ws `C.face` (i C.~> 1)
--         fibersys' = mapWithKey
--           (\gamma eqG ->
--             let fibsgamma = intersectionWith (\ x y -> (x,constPath y))
--                               (wsi1 `C.face` gamma) (vsi1 `C.face` gamma)
--             in lemEq eqG (vi1' `C.face` gamma)
--                      (fibsgamma `C.unionSystem` (fibersys `C.face` gamma))) eqsI1
-- 
--         vi1 = compConstLine ai1 vi1'
--                 (Map.map snd fibersys' `C.unionSystem` Map.map constPath vsi1)
-- 
--         usi1 = Map.map fst fibersys'

-- lemEq :: Val -> Val -> C.System (Val,Val) -> (Val,Val)
-- lemEq eq b aps = (a,VPLam i (compNeg j (eq @@ j) p1 thetas'))
--  where
--    i:j:_ = C.freshs (eq,b,aps)
--    ta = eq @@ C.One
--    p1s = mapWithKey (\alpha (aa,pa) ->
--               let eqaj = (eq `C.face` alpha) @@ j
--                   ba = b `C.face` alpha
--               in comp j eqaj (pa @@ i)
--                    (C.mkSystem [ (i C.~>0,transFill j eqaj ba)
--                              , (i C.~>1,transFillNeg j eqaj aa)])) aps
--    thetas = mapWithKey (\alpha (aa,pa) ->
--               let eqaj = (eq `C.face` alpha) @@ j
--                   ba = b `C.face` alpha
--               in fill j eqaj (pa @@ i)
--                    (C.mkSystem [ (i C.~>0,transFill j eqaj ba)
--                              , (i C.~>1,transFillNeg j eqaj aa)])) aps
-- 
--    a  = comp i ta (trans i (eq @@ i) b) p1s
--    p1 = fill i ta (trans i (eq @@ i) b) p1s
-- 
--    thetas' = C.insertsSystem [ (i C.~> 0,transFill j (eq @@ j) b)
--                            , (i C.~> 1,transFillNeg j (eq @@ j) a)] thetas
-- 
-- Old version:
-- This version triggers the following error when checking the normal form of corrUniv:
-- Parsed "examples/nunivalence2.ctt" successfully!
-- Resolver failed: Cannot resolve name !3 at position (7,30062) in module nunivalence2
-- compU :: Name -> Val -> C.System Val -> Val -> C.System Val -> Val
-- compU i b es wi0 ws = glueElem vi1'' usi1''
--   where bi1 = b `C.face` (i C.~> 1)
--         vs   = mapWithKey (\alpha wAlpha ->
--                  unGlueU wAlpha (b `C.face` alpha) (es `C.face` alpha)) ws
--         vsi1 = vs `C.face` (i C.~> 1) -- same as: C.border vi1 vs
--         vi0  = unGlueU wi0 (b `C.face` (i C.~> 0)) (es `C.face` (i C.~> 0)) -- in b(i0)

--         v    = fill i b vi0 vs           -- in b
--         vi1  = comp i b vi0 vs           -- is v `C.face` (i C.~> 1) in b(i1)

--         esI1 = es `C.face` (i C.~> 1)
--         es'  = filterWithKey (\alpha _ -> i `Map.notMember` alpha) es
--         es'' = filterWithKey (\alpha _ -> alpha `Map.notMember` es) esI1

--         us'    = mapWithKey (\gamma eGamma ->
--                    fill i (eGamma @@ C.One) (wi0 `C.face` gamma) (ws `C.face` gamma))
--                  es'
--         usi1'  = mapWithKey (\gamma eGamma ->
--                    comp i (eGamma @@ C.One) (wi0 `C.face` gamma) (ws `C.face` gamma))
--                  es'

--         ls'    = mapWithKey (\gamma eGamma ->
--                      pathComp i (b `C.face` gamma) (v `C.face` gamma)
--                        (transNegLine eGamma (us' ! gamma)) (vs `C.face` gamma))
--                    es'

--         vi1' = compLine (constPath bi1) vi1
--                  (ls' `C.unionSystem` Map.map constPath vsi1)

--         wsi1 = ws `C.face` (i C.~> 1)

--         -- for gamma in es'', (i1) gamma is in es, so wsi1 gamma
--         -- is in the domain of isoGamma
--         uls'' = mapWithKey (\gamma eGamma ->
--                   isoToEquivU (bi1 `C.face` gamma) eGamma
--                     ((usi1' `C.face` gamma) `C.unionSystem` (wsi1 `C.face` gamma))
--                     (vi1' `C.face` gamma))
--                   es''

--         vsi1' = Map.map constPath $ C.border vi1' es' `C.unionSystem` vsi1

--         vi1'' = compLine (constPath bi1) vi1'
--                   (Map.map snd uls'' `C.unionSystem` vsi1')

--         usi1'' = Map.mapWithKey (\gamma _ ->
--                      if gamma `Map.member` usi1' then usi1' ! gamma
--                      else fst (uls'' ! gamma))
--                   esI1

-- IsoToEquiv, takes a line eq in U, a system us and a value v, s.t. f us =
-- C.border v. Outputs (u,p) s.t. C.border u = us and a path p between v
-- and f u, where f is transNegLine eq
-- isoToEquivU :: Val -> Val -> C.System Val -> Val -> (Val, Val)
-- isoToEquivU b eq us v = (u, VPLam i theta)
--   where i:j:_   = C.freshs (b,eq,us,v)
--         ej      = eq @@ j
--         a       = eq @@ C.One
--         ws      = mapWithKey (\alpha uAlpha ->
--                                    transFillNeg j (ej `C.face` alpha) uAlpha) us
--         u       = comp j ej v ws
--         w       = fill j ej v ws
--         xs      = C.insertSystem (i C.~> 0) w $
--                   C.insertSystem (i C.~> 1) (transFillNeg j ej u) $ ws
--         theta   = compNeg j ej u xs

-- Old version:
-- isoToEquivU :: Val -> Val -> System Val -> Val -> (Val, Val)
-- isoToEquivU b eq us v = (u, VPLam i theta'')
--   where i:j:_   = C.freshs (b,eq,us,v)
--         a       = eq @@ C.One
--         g       = transLine
--         f       = transNegLine
--         s e y   = VPLam j $ compNeg i (e @@ i) (trans i (e @@ i) y)
--                     (C.mkSystem [(j C.~> 0, transFill j (e @@ j) y)
--                               ,(j C.~> 1, transFillNeg j (e @@ j)
--                                           (trans j (e @@ j) y))])
--         t e x   = VPLam j $ comp i (e @@ i) (transNeg i (e @@ i) x)
--                     (C.mkSystem [(j C.~> 0, transFill j (e @@ j)
--                                           (transNeg j (e @@ j) x))
--                               ,(j C.~> 1, transFillNeg j (e @@ j) x)])
--         gv      = g eq v
--         us'     = mapWithKey (\alpha uAlpha ->
--                                    t (eq `C.face` alpha) uAlpha @@ i) us
--         theta   = fill i a gv us'
--         u       = comp i a gv us'  -- Same as "theta `C.face` (i C.~> 1)"
--         ws      = C.insertSystem (i C.~> 0) gv $
--                   C.insertSystem (i C.~> 1) (t eq u @@ j) $
--                   mapWithKey
--                     (\alpha uAlpha ->
--                       t (eq `C.face` alpha) uAlpha @@ (C.Atom i :/\: C.Atom j)) us
--         theta'  = compNeg j a theta ws
--         xs      = C.insertSystem (i C.~> 0) (s eq v @@ j) $
--                   C.insertSystem (i C.~> 1) (s eq (f eq u) @@ j) $
--                   mapWithKey
--                     (\alpha uAlpha ->
--                        s (eq `C.face` alpha) (f (eq `C.face` alpha) uAlpha) @@ j) us
--         theta'' = comp j b (f eq theta') xs


-------------------------------------------------------------------------------
-- | Conversion

class Convertible a where
  conv :: [String] -> a -> a -> Bool

isCompSystem :: (C.Nominal a, Convertible a) => [String] -> C.System a -> Bool
isCompSystem ns ts = and [ conv ns (getFace alpha beta) (getFace beta alpha)
                         | (alpha,beta) <- C.allCompatible (keys ts) ]
    where getFace a b = C.face (ts ! a) (b `C.minus` a)

instance Convertible Env where
  conv ns (Env (rho1,vs1,fs1,os1)) (Env (rho2,vs2,fs2,os2)) =
      conv ns (rho1,vs1,fs1,os1) (rho2,vs2,fs2,os2)

instance Convertible Val where
  conv ns u v | u == v    = True
              | otherwise =
    let j = C.fresh (u,v)
    in case (u,v) of
      (Ter (Lam x a u) e,Ter (Lam x' a' u') e') ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (eval (upd (x,v) e) u) (eval (upd (x',v) e') u')
      (Ter (Lam x a u) e,u') ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (eval (upd (x,v) e) u) (app u' v)
      (u',Ter (Lam x a u) e) ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (app u' v) (eval (upd (x,v) e) u)
      (Ter (Split _ p _ _) e,Ter (Split _ p' _ _) e') -> (p == p') && conv ns e e'
      (Ter (Sum p _ _) e,Ter (Sum p' _ _) e')         -> (p == p') && conv ns e e'
      -- (Ter (HSum p _ _) e,Ter (HSum p' _ _) e')       -> (p == p') && conv ns e e'
      (Ter (Undef p _) e,Ter (Undef p' _) e') -> p == p' && conv ns e e'
      (Ter (Hole p) e,Ter (Hole p') e') -> p == p' && conv ns e e'
      -- (Ter Hole{} e,_) -> True
      -- (_,Ter Hole{} e') -> True
      (VPi u v,VPi u' v') ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv ns u u' && conv (n:ns) (app v w) (app v' w)
      (VSigma u v,VSigma u' v') ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv ns u u' && conv (n:ns) (app v w) (app v' w)
      (VCon c us,VCon c' us')   -> (c == c') && conv ns us us'
      (VPCon c v us phis,VPCon c' v' us' phis') ->
        (c == c') && conv ns (v,us,phis) (v',us',phis')
      (VPair u v,VPair u' v')    -> conv ns u u' && conv ns v v'
      (VPair u v,w)              -> conv ns u (fstVal w) && conv ns v (sndVal w)
      (w,VPair u v)              -> conv ns (fstVal w) u && conv ns (sndVal w) v
      (VFst u,VFst u')           -> conv ns u u'
      (VSnd u,VSnd u')           -> conv ns u u'
      (VApp u v,VApp u' v')      -> conv ns u u' && conv ns v v'
      (VSplit u v,VSplit u' v')  -> conv ns u u' && conv ns v v'
      (VOpaque x _, VOpaque x' _) -> x == x'
      (VVar x _, VVar x' _)       -> x == x'
      -- (VPathP a b c,VPathP a' b' c') -> conv ns a a' && conv ns b b' && conv ns c c'
      -- (VPLam i a,VPLam i' a')    -> conv ns (a `C.swap` (i,j)) (a' `C.swap` (i',j))
      -- (VPLam i a,p')             -> conv ns (a `C.swap` (i,j)) (p' @@ j)
      -- (p,VPLam i' a')            -> conv ns (p @@ j) (a' `C.swap` (i',j))
      -- (VAppFormula u x,VAppFormula u' x') -> conv ns (u,x) (u',x')
      -- (VComp a u ts,VComp a' u' ts')      -> conv ns (a,u,ts) (a',u',ts')
      -- (VHComp a u ts,VHComp a' u' ts')    -> conv ns (a,u,ts) (a',u',ts')
      -- (VGlue v equivs,VGlue v' equivs')   -> conv ns (v,equivs) (v',equivs')
      -- (VGlueElem (VUnGlueElem b equivs) ts,g) -> conv ns (C.border b equivs,b) (ts,g)
      -- (g,VGlueElem (VUnGlueElem b equivs) ts) -> conv ns (C.border b equivs,b) (ts,g)
      -- (VGlueElem (VUnGlueElemU b _ equivs) ts,g) -> conv ns (C.border b equivs,b) (ts,g)
      -- (g,VGlueElem (VUnGlueElemU b _ equivs) ts) -> conv ns (C.border b equivs,b) (ts,g)
      -- (VGlueElem u us,VGlueElem u' us')   -> conv ns (u,us) (u',us')
      -- (VUnGlueElemU u _ _,VUnGlueElemU u' _ _) -> conv ns u u'
      -- (VUnGlueElem u _,VUnGlueElem u' _) -> conv ns u u'
      -- (VCompU u es,VCompU u' es')              -> conv ns (u,es) (u',es')
      -- (VIdPair v vs,VIdPair v' vs')          -> conv ns (v,vs) (v',vs')
      (VId a u v,VId a' u' v')               -> conv ns (a,u,v) (a',u',v')
      (VIdJ a u c d x p,VIdJ a' u' c' d' x' p') ->
        conv ns [a,u,c,d,x,p] [a',u',c',d',x',p']
      _                                      -> False

instance Convertible Ctxt where
  conv _ _ _ = True

instance Convertible () where
  conv _ _ _ = True

instance (Convertible a, Convertible b) => Convertible (a, b) where
  conv ns (u, v) (u', v') = conv ns u u' && conv ns v v'

instance (Convertible a, Convertible b, Convertible c)
      => Convertible (a, b, c) where
  conv ns (u, v, w) (u', v', w') = conv ns (u,(v,w)) (u',(v',w'))

instance (Convertible a,Convertible b,Convertible c,Convertible d)
      => Convertible (a,b,c,d) where
  conv ns (u,v,w,x) (u',v',w',x') = conv ns (u,v,(w,x)) (u',v',(w',x'))

instance Convertible a => Convertible [a] where
  conv ns us us' = length us == length us' &&
                  and [conv ns u u' | (u,u') <- zip us us']

instance Convertible a => Convertible (C.System a) where
  conv ns ts ts' = keys ts == keys ts' &&
                   and (elems (intersectionWith (conv ns) ts ts'))

instance Convertible C.Formula where
  conv _ phi psi = C.dnf phi == C.dnf psi

instance Convertible (C.Nameless a) where
  conv _ _ _ = True

-------------------------------------------------------------------------------
-- | Normalization

class Normal a where
  normal :: [String] -> a -> a

instance Normal Env where
  normal ns (Env (rho,vs,fs,os)) = Env (normal ns (rho,vs,fs,os))

instance Normal Val where
  normal ns v = case v of
    VU                  -> VU
    Ter (Lam x t u) e   ->
      let w = eval e t
          v@(VVar n _) = mkVarNice ns x w
      in VLam n (normal ns w) $ normal (n:ns) (eval (upd (x,v) e) u)
    Ter t e             -> Ter t (normal ns e)
    VPi u v             -> VPi (normal ns u) (normal ns v)
    VSigma u v          -> VSigma (normal ns u) (normal ns v)
    VPair u v           -> VPair (normal ns u) (normal ns v)
    VCon n us           -> VCon n (normal ns us)
    VPCon n u us phis   -> VPCon n (normal ns u) (normal ns us) phis
    -- VPathP a u0 u1      -> VPathP (normal ns a) (normal ns u0) (normal ns u1)
    -- VPLam i u           -> VPLam i (normal ns u)
    -- VComp u v vs        -> VComp (normal ns u) (normal ns v) (normal ns vs)
    -- VHComp u v vs       -> VHComp (normal ns u) (normal ns v) (normal ns vs)
    -- VGlue u equivs      -> VGlue (normal ns u) (normal ns equivs)
    -- VGlueElem u us      -> VGlueElem (normal ns u) (normal ns us)
    -- VUnGlueElem u us    -> VUnGlueElem (normal ns u) (normal ns us)
    -- VUnGlueElemU e u us -> VUnGlueElemU (normal ns e) (normal ns u) (normal ns us)
    -- VCompU a ts         -> VCompU (normal ns a) (normal ns ts)
    VVar x t            -> VVar x (normal ns t)
    VFst t              -> VFst (normal ns t)
    VSnd t              -> VSnd (normal ns t)
    VSplit u t          -> VSplit (normal ns u) (normal ns t)
    VApp u v            -> VApp (normal ns u) (normal ns v)
    -- VAppFormula u phi   -> VAppFormula (normal ns u) (normal ns phi)
    VId a u v           -> VId (normal ns a) (normal ns u) (normal ns v)
    -- VIdPair u us        -> VIdPair (normal ns u) (normal ns us)
    -- VIdJ a u c d x p    -> VIdJ (normal ns a) (normal ns u) (normal ns c)
    --                             (normal ns d) (normal ns x) (normal ns p)
    _                   -> v

instance Normal (C.Nameless a) where
  normal _ = id

instance Normal Ctxt where
  normal _ = id

instance Normal C.Formula where
  normal _ = C.fromDNF . C.dnf

instance Normal a => Normal (Map k a) where
  normal ns = Map.map (normal ns)

instance (Normal a,Normal b) => Normal (a,b) where
  normal ns (u,v) = (normal ns u,normal ns v)

instance (Normal a,Normal b,Normal c) => Normal (a,b,c) where
  normal ns (u,v,w) = (normal ns u,normal ns v,normal ns w)

instance (Normal a,Normal b,Normal c,Normal d) => Normal (a,b,c,d) where
  normal ns (u,v,w,x) =
    (normal ns u,normal ns v,normal ns w, normal ns x)

instance Normal a => Normal [a] where
  normal ns = map (normal ns)
