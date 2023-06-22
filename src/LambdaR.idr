module LambdaR

import LambdaB
import Data.Nat

public export
Entail : {g : Cx} -> {t : U} -> (phi : IC g -> Type) -> (psi, psi' : IC (CCx g t) -> Type) -> Type
Entail phi psi psi' = (gam : IC g) -> (x : IU t) -> phi gam -> psi (gam, x) -> psi' (gam, x)

mutual
  -- Refinement typing with a pre- and a post-condition.
  data RTm : (g : Cx) -> (IC g -> Type)
          -> (t : U)  -> (IC (CCx g t) -> Type) -> Type where
    RVAR  : (i : Ix g t) -> RTm g phi t (\g_nu => snd g_nu = IIx i (fst g_nu))
    RUNIT : RTm g phi One (\g_nu => snd g_nu = ())
    RTT   : RTm g phi Two (\g_nu => snd g_nu = True)
    RFF   : RTm g phi Two (\g_nu => snd g_nu = False)
    RZE   : RTm g phi N   (\g_nu => snd g_nu = 0)
    RSU   : (n : RTm g phi N psi)
         -> RTm g phi N (\g_nu => snd g_nu = S (iTm (Er n) (fst g_nu)))
    RIF   : (c : RTm g phi Two ksi)
         -> (RTm g (\g => (phi g, iTm (Er c) g = True )) t psi)
         -> (RTm g (\g => (phi g, iTm (Er c) g = False)) t psi)
         -> RTm g phi t psi
    RLET  : {0 ksi : IC (CCx g s) -> Type} -> {0 psi : IC (CCx g t) -> Type}
         -> (e1 : RTm g phi s ksi)
         -> (e2 : RTm (CCx g s) (\gs => (phi (fst gs), ksi gs)) t (\gs_nu => psi (fst (fst gs_nu),snd gs_nu)))
         -> RTm g phi t psi
    RPRD  : (e1 : RTm g phi s psi1)
         -> (e2 : RTm g phi t psi2)
         -> RTm g phi (Prod s t) (\g_nu => snd g_nu = ( iTm (Er e1) (fst g_nu)
                                                      , iTm (Er e2) (fst g_nu)))
    RFST  : (e : RTm g phi (Prod s t) psi)
         -> RTm g phi s (\g_nu => snd g_nu = fst (iTm (Er e) (fst g_nu)))
    RSND  : (e : RTm g phi (Prod s t) psi)
         -> RTm g phi t (\g_nu => snd g_nu = snd (iTm (Er e) (fst g_nu)))
    RAPP  : (f : RTmF g phi s ksi t psi)
         -> (e : RTm g phi s ksi)
         -> RTm g phi t (\g_t => psi ((fst g_t, iTm (Er e) (fst g_t)), snd g_t))
    RBOP  : (o : Op)
         -> {0 psi1, psi2 : IC (CCx g (opL o)) -> Type}
         -> (e1 : RTm g phi (opL o) psi1)
         -> (e2 : RTm g phi (opL o) psi2)
         -> RTm g phi (opR o) (\g_nu => snd g_nu = iOp o (iTm (Er e1) (fst g_nu))
                                                         (iTm (Er e2) (fst g_nu)))
    RSUB  : (e : RTm g phi t psi)
         -> (0 psi' : IC (CCx g t) -> Type)  -- TODO make implicit?
         -> Entail {g} {t} phi psi psi'
         -> RTm g phi t psi'

  data RTmF : (g : Cx) -> (IC g -> Type)
           -> (s : U) -> (IC (CCx g s) -> Type)
           -> (t : U) -> (IC ((CCx (CCx g s) t)) -> Type) -> Type where
    RFUN   : RTm (CCx g s) ksi t psi
          -> RTmF g phi s ksi t psi

  -- Erasure.
  Er : RTm g phi t psi -> Tm g t
  Er (RVAR i)       = VAR i
  Er  RUNIT         = UNIT
  Er  RTT           = TT
  Er  RFF           = FF
  Er  RZE           = ZE
  Er (RSU n)        = SU (Er n)
  Er (RIF c e1 e2)  = IF (Er c) (Er e1) (Er e2)
  Er (RLET e1 e2)   = LET (Er e1) (Er e2)
  Er (RPRD e1 e2)   = PRD (Er e1) (Er e2)
  Er (RFST e)       = FST (Er e)
  Er (RSND e)       = SND (Er e)
  Er (RAPP f e)     = APP (ErF f) (Er e)
  Er (RBOP o e1 e2) = BOP o (Er e1) (Er e2)
  Er (RSUB e _ _)   = (Er e)

  ErF: RTmF g phi s ksi t psi -> TmF g s t
  ErF (RFUN e) = FUN (Er e)

weakAdmissibleF : (f : RTmF g phi s ksi t psi)
               -> (wk : (gam : IC g) -> phi' gam -> phi gam)
               -> (f' : RTmF g phi' s ksi t psi ** ErF f = ErF f')
weakAdmissibleF (RFUN f) wk = (RFUN f ** Refl)

weakAdmissible : (e : RTm g phi t psi)
              -> (wk : (gam : IC g) -> phi' gam -> phi gam)
              -> (e' : RTm g phi' t psi ** Er {phi} e = Er {phi=phi'} e')
weakAdmissible (RVAR i)           wk = (RVAR {phi=phi'} i ** Refl)
weakAdmissible  RUNIT             wk = (RUNIT ** Refl)
weakAdmissible  RTT               wk = (RTT ** Refl)
weakAdmissible  RFF               wk = (RFF ** Refl)
weakAdmissible  RZE               wk = (RZE ** Refl)
weakAdmissible (RSU n)            wk =
  let (n' ** prf) = weakAdmissible n wk in
  rewrite prf in
  (RSU n' ** Refl)
weakAdmissible (RIF c x y)        wk =
  let (c' ** prfc) = weakAdmissible c wk in
  let (x' ** prfx) = weakAdmissible x {phi' = \g => (phi' g, iTm (Er c) g = True)}
                                    (\gam, (pg', e) => (wk gam pg', e)) in
  let (y' ** prfy) = weakAdmissible y {phi' = \g => (phi' g, iTm (Er c) g = False)}
                                    (\gam, (pg', e) => (wk gam pg', e)) in
  -- not sure why is this special
  (RIF c' (rewrite sym prfc in x') (rewrite sym prfc in y') ** IFhelper prfc prfx prfy)
weakAdmissible (RLET {ksi} e1 e2) wk =
  let (e1' ** prf1) = weakAdmissible e1 wk in
  let (e2' ** prf2) = weakAdmissible e2 {phi' = \gs' => (phi' (fst gs'), ksi gs')}
                                     (\(g1,s1),(pprf,kprf) => (wk g1 pprf, kprf)) in
  (RLET e1' e2' ** rewrite prf1 in rewrite prf2 in Refl)
weakAdmissible (RPRD e1 e2)       wk =
  let (e1' ** prf1) = weakAdmissible e1 wk in
  let (e2' ** prf2) = weakAdmissible e2 wk in
  rewrite prf1 in
  rewrite prf2 in
  (RPRD e1' e2' ** Refl)
weakAdmissible (RFST e)           wk =
  let (e' ** prf) = weakAdmissible e wk in
  rewrite prf in
  (RFST e' ** Refl)
weakAdmissible (RSND e)           wk =
  let (e' ** prf) = weakAdmissible e wk in
  rewrite prf in
  (RSND e' ** Refl)
weakAdmissible (RAPP f e)         wk =
  let (f' ** prff) = weakAdmissibleF f wk in
  let (e' ** prfe) = weakAdmissible e wk in
  rewrite prff in
  rewrite prfe in
  (RAPP f' e' ** Refl)
weakAdmissible (RBOP o e1 e2)     wk =
  let (e1' ** prf1) = weakAdmissible e1 wk in
  let (e2' ** prf2) = weakAdmissible e2 wk in
  rewrite prf1 in
  rewrite prf2 in
  (RBOP o e1' e2' ** Refl)
weakAdmissible (RSUB e psi f)     wk =
  let (e' ** prf) = weakAdmissible e wk in
  rewrite prf in
  (RSUB e' psi (\gam, x, prf1, prf2 => f gam x (wk gam prf1) prf2) ** Refl)

RONE : RTm g phi N (\g_nu => snd g_nu = 1)
RONE = RSU RZE

RTWO : RTm g phi N (\g_nu => snd g_nu = 2)
RTWO = RSU RONE

RTHREE : RTm g phi N (\g_nu => snd g_nu = 3)
RTHREE = RSU RTWO

-- \x.x+1
Rf0 : RTmF ECx (Kc ()) N (\g_nu => LT (snd g_nu) 2) N (\gt_nu => LT (snd gt_nu) 4)
Rf0 = RFUN $ RSUB (RBOP OpPlus (RVAR Top) RONE)
                  _ -- (\gt_nu => LT (snd gt_nu) 4)
                  (\(_,x), y, x2, ey => rewrite ey in
                                        rewrite plusCommutative x 1 in
                                        LTESucc $ lteSuccRight x2)

Ex0 : Tm ECx N
Ex0 = APP f0 ONE

REx0 : RTm ECx (Kc ()) N (\g_nu => LT (snd g_nu) 5)
REx0 = RSUB (RAPP {psi = \g_nu => LT (snd g_nu) 4}
                  Rf0
                  (RSUB RONE
                        (\g_nu => LT (snd g_nu) 2)
                        (\(),x,(),ex => rewrite ex in reflexive)
                   )
            )
            (\g_nu => LT (snd g_nu) 5)
            (\(),x,(),xprf => lteSuccRight xprf)

baseTypeSoundness : (e : Tm g t) -> IC g -> IU t
baseTypeSoundness = iTm

baseTypeSoundnessF : (e : TmF g s t) -> IC g -> (IU s -> IU t)
baseTypeSoundnessF = iTmf

mutual
  refSoundness : {gam : IC g} ->
                 (e : RTm g phi t psi)
              -> (phi gam -> psi (gam, iTm (Er e) gam))
  refSoundness (RVAR _)       _      = Refl
  refSoundness  RUNIT         _      = Refl
  refSoundness  RTT           _      = Refl
  refSoundness  RFF           _      = Refl
  refSoundness  RZE           _      = Refl
  refSoundness (RSU _)        _      = Refl
  refSoundness (RIF c e1 e2)  phiprf with (iTm (Er c) gam) proof eq
   refSoundness (RIF c e1 e2)  phiprf | True  = refSoundness e1 (phiprf, eq)
   refSoundness (RIF c e1 e2)  phiprf | False = refSoundness e2 (phiprf, eq)
  refSoundness (RLET e1 e2)   phiprf = refSoundness e2 (phiprf, refSoundness e1 phiprf)
  refSoundness (RPRD _ _)     _      = Refl
  refSoundness (RFST _)       _      = Refl
  refSoundness (RSND _)       _      = Refl
  refSoundness (RAPP f e)     phiprf = refSoundnessF f (iTm (Er e) gam) phiprf (refSoundness e phiprf)
  refSoundness (RBOP _ _ _)   _      = Refl
  refSoundness (RSUB e _ sub) phiprf = sub gam (iTm (Er e) gam) phiprf (refSoundness e phiprf)

  refSoundnessF :{gam : IC g} ->
                 (f : RTmF g phi s ksi t psi) ->
                 (x : IU s) -> phi gam -> ksi (gam,x) -> psi ((gam,x), iTmf (ErF f) gam x)
  refSoundnessF (RFUN e) x _ = refSoundness e

refSoundness' : (e : RTm ECx (Kc ()) t psi) -> psi (() , iTm (Er e) ())
refSoundness' e = refSoundness e ()

mutual
  refCompleteness : (e : Tm g t)
                 -> ((gam : IC g) -> phi gam -> psi (gam, iTm e gam))
                 -> (e' : RTm g phi t psi ** Er e' = e)
  refCompleteness (VAR x)     prf = (RSUB (RVAR x) psi
                                          (\gam,x,p,ex => rewrite ex in prf gam p)
                                       ** Refl)
  refCompleteness  UNIT       prf = (RSUB RUNIT psi
                                          (\gam,(),p,ex => rewrite ex in prf gam p)
                                       ** Refl)
  refCompleteness  TT         prf = (RSUB RTT psi
                                          (\gam,x,p,ex => rewrite ex in prf gam p)
                                       ** Refl)
  refCompleteness  FF         prf = (RSUB RFF psi
                                          (\gam,x,p,ex => rewrite ex in prf gam p)
                                       ** Refl)
  refCompleteness  ZE         prf = (RSUB RZE psi
                                          (\gam,x,p,ex => rewrite ex in prf gam p)
                                       ** Refl)
  refCompleteness (SU x)      prf =
    let (e' ** ep) = refCompleteness {psi=Kc ()} x (\_,_ => ()) in
    (RSUB (RSU e') psi
          (\gam,x,p,ex => rewrite ex in rewrite ep in prf gam p)
       ** rewrite ep in Refl)
  refCompleteness (IF c tt tf)  prf =
    let (c' ** ec)  = refCompleteness {psi=Kc ()} c (\_,_=>())
        (tt' ** et) = refCompleteness tt {phi = \gam=>(phi gam,iTm c gam = True)} {psi}
                        (\gam,(pg,ic) => replace {p = \z=>psi (gam, ifThenElse z (iTm tt gam)
                                                                                 (iTm tf gam))}
                                                 ic
                                                 (prf gam pg))
        (tf' ** ef) = refCompleteness tf {phi = \gam=>(phi gam,iTm c gam = False)}
                        (\gam,(pg,ic) => replace {p = \z=>psi (gam, ifThenElse z (iTm tt gam)
                                                                                 (iTm tf gam))}
                                                 ic
                                                 (prf gam pg))
     in
    (RIF c' (rewrite ec in tt') (rewrite ec in tf') **
      rewrite ec in rewrite et in rewrite ef in Refl)
  refCompleteness (LET s t)   prf =
    let (s' ** es) = refCompleteness {psi = \gam_x => snd gam_x = iTm s (fst gam_x)} s (\_,_ => Refl)
        (t' ** et) = refCompleteness {phi = \gam_x => (phi (fst gam_x), snd gam_x = iTm s (fst gam_x))}
                                     {psi = \gamz_q => psi (fst (fst gamz_q),snd gamz_q)} t
                                     (\(ig,is),(pig,eis) => replace {p = \z => psi (ig, iTm t (ig,z))}
                                                                    (sym eis)
                                                                    (prf ig pig))
     in
    (RLET s' t' ** rewrite es in rewrite et in Refl)
  refCompleteness (PRD s t)   prf =
    let (s' ** es) = refCompleteness {psi=Kc ()} s (\_,_=>())
        (t' ** et) = refCompleteness {psi=Kc ()} t (\_,_=>())
     in
    (RSUB (RPRD s' t') psi
          (\gam,x,pg,ex => rewrite ex in rewrite es in rewrite et in prf gam pg)
      ** rewrite es in rewrite et in Refl)
  refCompleteness (FST s)     prf =
    let (s' ** es) = refCompleteness {psi=Kc ()} s (\_,_=>()) in
    (RSUB (RFST s') psi
          (\gam,x,pg,ex => rewrite ex in rewrite es in prf gam pg)
      ** rewrite es in Refl)
  refCompleteness (SND s)     prf =
    let (s' ** es) = refCompleteness {psi=Kc ()} s (\_,_=>()) in
    (RSUB (RSND s') psi
          (\gam,x,pg,ex => rewrite ex in rewrite es in prf gam pg)
      ** rewrite es in Refl)
  refCompleteness (APP f q)   prf =
    let (f' ** ef) = refCompletenessF {ksi = \gam_s => snd gam_s = iTm q (fst gam_s)}
                                      {psi = \gams_t => snd gams_t = iTmf f (fst (fst gams_t)) (snd (fst gams_t))}
                                      f
                                      (\gam,x,ex => rewrite ex in Refl)
        (q' ** eq) = refCompleteness {psi = \gam_s => snd gam_s = iTm q (fst gam_s)}
                                     q
                                     (\gam,pg => Refl)
     in
    (RSUB (RAPP f' q') psi (\gam,x,pg,ex => rewrite ex in rewrite eq in prf gam pg)
       ** rewrite ef in rewrite eq in Refl)
  refCompleteness (BOP o s t) prf =
   let (s' ** es) = refCompleteness {psi=Kc ()} s (\_,_=>())
       (t' ** et) = refCompleteness {psi=Kc ()} t (\_,_=>())
    in
   (RSUB (RBOP o s' t') psi (\gam,x,pg,ex => rewrite ex in rewrite es in rewrite et in prf gam pg)
      ** rewrite es in rewrite et in Refl)

  refCompletenessF : (f : TmF g s t)
                  -> ((gam : IC g) -> (x : IU s) -> ksi (gam,x) -> psi ((gam,x),iTmf f gam x))
                  -> (f' : RTmF g phi s ksi t psi ** ErF f' = f)
  refCompletenessF (FUN s) prf =
    let (s' ** es) = refCompleteness {psi} {phi=ksi} s (\(gam,s),p => prf gam s p) in
    (RFUN s' ** rewrite es in Refl)

preInv : (e : Tm g t) -> (e' : RTm g phi t (phi . Builtin.fst) ** Er e' = e)
preInv e = refCompleteness e (\gam,pg=>pg)

consistency : (e : RTm g phi t (Kc Void)) -> Not (ig : IC g ** phi ig)
consistency e (ig ** pig) = refSoundness e pig

wp : (IC (CCx g t) -> Type) -> Tm g t -> (IC g -> Type)
wp = subst

wpF : (IC (CCx (CCx g s) t) -> Type) -> TmF g s t -> (IC (CCx g s) -> Type)
wpF phi (FUN e) = subst phi e

wpCompleteness : (e : RTm g phi t psi)
               -> (gam : IC g)
               -> (phi gam -> wp psi (Er e) gam)
wpCompleteness e gam = refSoundness e

wpSoundness : (e : Tm g t)
           -> (psi : IC (CCx g t) -> Type)
           -> (e' : RTm g (wp psi e) t psi ** Er e' = e)
wpSoundness e psi = refCompleteness e (\gam, pg => pg)
