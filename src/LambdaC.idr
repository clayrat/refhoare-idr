module LambdaC

import Data.Nat
import LambdaB
import LambdaR

mutual
  data ATm : Cx -> U -> Type where
    AVAR  : Ix g t -> ATm g t
    AUNIT : ATm g One
    ATT   : ATm g Two
    AFF   : ATm g Two
    AZE   : ATm g N
    ASU   : ATm g N -> ATm g N
    AIF   : ATm g Two -> ATm g t -> ATm g t -> ATm g t
    ALET  : {s : _} ->
            ATm g s -> ATm (CCx g s) t -> ATm g t
    APRD  : ATm g s -> ATm g t -> ATm g (Prod s t)
    AFST  : ATm g (Prod s t) -> ATm g s
    ASND  : ATm g (Prod s t) -> ATm g t
    AAPP  : {s, t : _} -> {ksi : _} -> {psi : _} ->
            ATmF g s ksi t psi -> ATm g s -> ATm g t
    ABOP  : (o : Op) -> ATm g (opL o) -> ATm g (opL o) -> ATm g (opR o)

  data ATmF : (g : Cx) -> (s : U) -> (ksi : IC (CCx g s) -> Type)
                       -> (t : U) -> (psi : IC ((CCx (CCx g s) t)) -> Type) -> Type where
    AFUN : ATm (CCx g s) t -> ATmF g s ksi t psi

delta : ATmF g s ksi t psi -> IC g -> IU s -> IU t

mutual
 iATm : ATm g t -> IC g -> IU t
 iATm (AVAR i)      = IIx i
 iATm  AUNIT        = Kc ()
 iATm  ATT          = Kc True
 iATm  AFF          = Kc False
 iATm  AZE          = Kc 0
 iATm (ASU n)       = Sc (Kc S) (iATm n)
 iATm (AIF c tt ft) = \r => if iATm c r then iATm tt r else iATm ft r
 iATm (ALET p q)    = Sc (curry (iATm q)) (iATm p)
 iATm (APRD p q)    = \r => (iATm p r, iATm q r)
 iATm (AFST p)      = fst . iATm p
 iATm (ASND p)      = snd . iATm p
 iATm (AAPP f s)    = Sc (iATmF f) (iATm s)
 iATm (ABOP o l r)  = Sc (Sc (Kc (iOp o)) (iATm l)) (iATm r)

 iATmF : ATmF g s ksi t psi -> IC g -> IU s -> IU t
 iATmF = delta

substC : (phi : IC (CCx g t) -> Type) -> ATm g t -> (IC g -> Type)
substC phi e ig = phi (ig, iATm e ig)

mutual
  -- Compositional HL.
  data CTm : (g : Cx) -> (IC g -> Type) -> (t : U) -> (IC (CCx g t) -> Type) -> Type where
    CVAR   : (i : Ix g t) -> CTm g phi t (\g_nu => snd g_nu = IIx i (fst g_nu))
    CUNIT  : CTm g phi One (\g_nu => snd g_nu = ())
    CTT    : CTm g phi Two (\g_nu => snd g_nu = True)
    CFF    : CTm g phi Two (\g_nu => snd g_nu = False)
    CZE    : CTm g phi N (\g_nu => snd g_nu = 0 )
    CSU    : (n : CTm g phi N psi)
          -> CTm g phi N (\g_nu => snd g_nu = S (iATm (ErC n) (fst g_nu)))
    CIF    : (c : CTm g phi Two ksi)
          -> CTm g (\gam => (phi gam, iATm (ErC c) gam = True)) t psi
          -> CTm g (\gam => (phi gam, iATm (ErC c) gam = False)) t psi
          -> CTm g phi t psi
    CLET   : {s : _} ->
             {0 ksi : IC (CCx g s) -> Type} -> {0 psi : IC (CCx g t) -> Type} ->
             (e1 : CTm g phi s ksi)
          -> (e2 : CTm (CCx g s) (\g_s => (phi (fst g_s), snd g_s = iATm (ErC e1) (fst g_s))) t (\gs_t => psi (fst (fst gs_t), snd gs_t)))
          -> CTm g phi t psi
    CPRD   : (e1 : CTm g phi s psi1)
          -> (e2 : CTm g phi t psi2)
          -> CTm g phi (Prod s t) (\g_nu => snd g_nu = (iATm (ErC e1) (fst g_nu), iATm (ErC e2) (fst g_nu)))
    CFST   : (e : CTm g phi (Prod s t) psi)
          -> CTm g phi s (\g_nu => snd g_nu = fst (iATm (ErC e) (fst g_nu)))
    CSND   : (e : CTm g phi (Prod s t) psi)
          -> CTm g phi t (\g_nu => snd g_nu = snd (iATm (ErC e) (fst g_nu)))
    CAPP   : {s, t : _} ->
             {ksi : IC (CCx g s) -> Type} ->
             {psi : IC ((CCx (CCx g s) t)) -> Type} ->
             (f : CTmF g phi s ksi t psi)
          -> (e : CTm g phi s ksi)
          -> CTm g phi t (\g_t => (is : IU s ** (ksi (fst g_t, is), psi ((fst g_t, is), snd g_t))))
    CBOP   : (o : Op)
          -> {0 psi1, psi2 : IC (CCx g (opL o)) -> Type}
          -> (e1 : CTm g phi (opL o) psi1)
          -> (e2 : CTm g phi (opL o) psi2)
          -> CTm g phi (opR o) (\g_nu => snd g_nu = iOp o (iATm (ErC e1) (fst g_nu))
                                                         (iATm (ErC e2) (fst g_nu)))
    CSUB   : (e : CTm g phi t psi)
          -> (0 psi' : IC (CCx g t) -> Type)  -- TODO make implicit?
          -> Entail {g} {t} phi psi psi'
          -> CTm g phi t psi'

  data CTmF : (g : Cx) -> (IC g -> Type)
           -> (s : U) -> (IC (CCx g s) -> Type)
           -> (t : U) -> (IC (CCx (CCx g s) t) -> Type) -> Type where
    CFUN   : CTm (CCx g s) (\g_s => (phi (fst g_s), ksi g_s)) t psi
          -> CTmF g phi s ksi t psi

  ErC : CTm g phi t psi -> ATm g t
  ErC (CVAR i)       = AVAR i
  ErC  CUNIT         = AUNIT
  ErC  CTT           = ATT
  ErC  CFF           = AFF
  ErC  CZE           = AZE
  ErC (CSU n)        = ASU (ErC n)
  ErC (CIF c e1 e2)  = AIF (ErC c) (ErC e1) (ErC e2)
  ErC (CLET e1 e2)   = ALET (ErC e1) (ErC e2)
  ErC (CPRD e1 e2)   = APRD (ErC e1) (ErC e2)
  ErC (CFST e)       = AFST (ErC e)
  ErC (CSND e)       = ASND (ErC e)
  ErC (CAPP f e)     = AAPP (ErCF f) (ErC e)
  ErC (CBOP o e1 e2) = ABOP o (ErC e1) (ErC e2)
  ErC (CSUB e _ _)   = ErC e

  ErCF : CTmF g phi s ksi t psi
      -> ATmF g s ksi t psi
  ErCF (CFUN e) = AFUN (ErC e)

0 mkC : ATmF g s ksi t psi -> Type
mkC f = {gam : IC g} -> (x : IU s) -> ksi (gam,x) -> psi ((gam,x),delta f gam x)

deltaEq : {0 gam : IC g} ->
          (e : ATm (CCx g s) t)
       -> (x : IU s)
       -> delta (AFUN e) gam x = iATm e (gam , x)
deltaEq e x = believe_me ()

mutual
  refCSoundness : {gam : IC g}
               -> (e : CTm g phi t psi)
               -> (phi gam -> psi (gam, iATm (ErC e) gam))
  refCSoundness (CVAR _)      _       = Refl
  refCSoundness  CUNIT        _       = Refl
  refCSoundness  CTT          _       = Refl
  refCSoundness  CFF          _       = Refl
  refCSoundness  CZE          _       = Refl
  refCSoundness (CSU _)       _       = Refl
  refCSoundness (CIF c e1 e2) phiprf with (iATm (ErC c) gam) proof cond
    refCSoundness (CIF c e1 e2) phiprf | True  = refCSoundness e1 (phiprf, cond)
    refCSoundness (CIF c e1 e2) phiprf | False = refCSoundness e2 (phiprf, cond)
  refCSoundness (CLET e1 e2) phiprf   = refCSoundness e2 (phiprf, Refl)
  refCSoundness (CPRD _ _)   _        = Refl
  refCSoundness (CFST _)     _        = Refl
  refCSoundness (CSND _)     _        = Refl
  refCSoundness (CAPP f e)   phiprf   =
    (iATm (ErC e) gam
      ** (refCSoundness e phiprf, refCSoundnessF f (iATm (ErC e) gam) phiprf $
                                  refCSoundness e phiprf))
  refCSoundness (CBOP _ _ _) _        = Refl
  refCSoundness (CSUB e _ sub) phiprf = sub gam (iATm (ErC e) gam) phiprf $
                                          refCSoundness e phiprf

  refCSoundnessF : {gam : IC g}
                -> (f : CTmF g phi s ksi t psi)
                -> (x : IU s) -> phi gam -> ksi (gam,x) -> psi ((gam,x) , iATmF (ErCF f) gam x)
  refCSoundnessF (CFUN e) x phiprf ksiprf =
    replace {p = \z => psi ((gam,x),z)} (sym $ deltaEq (ErC e) x) $
      refCSoundness e (phiprf, ksiprf)

refCSoundness' : (e : CTm ECx (Kc ()) t psi)
              -> psi ((), iATm (ErC e) ())
refCSoundness' e = refCSoundness e ()

pre : (psi : IC (CCx g t) -> Type) -> (e : ATm g t) -> (IC g -> Type)
pre psi (ASU e)          ig = (pre (Kc ()) e ig, substC psi (ASU e) ig)
pre psi (AIF c e1 e2)    ig = (pre (Kc ()) c ig, ifThenElse (iATm c ig) (pre psi e1 ig) (pre psi e2 ig))
pre psi (ALET e1 e2)     ig = (pre (Kc ()) e1 ig, pre (\gs_t => psi (fst (fst gs_t), snd gs_t)) e2 (ig, iATm e1 ig))
pre psi (APRD e1 e2)     ig = (pre (Kc ()) e1 ig, pre (Kc ()) e2 ig, substC psi (APRD e1 e2) ig)
pre psi (AFST e)         ig = (pre (Kc ()) e ig, substC psi (AFST e) ig)
pre psi (ASND e)         ig = (pre (Kc ()) e ig, substC psi (ASND e) ig)
pre _   (AAPP {ksi} f e) ig = pre ksi e ig
pre psi (ABOP o e1 e2)   ig = (pre (Kc ()) e1 ig, pre (Kc ()) e2 ig, substC psi (ABOP o e1 e2) ig)
pre psi  e               ig = substC psi e ig  -- It's just subst for the rest

0 preF : {0 ksi : IC (CCx g s) -> Type} ->
         {0 psi : IC ((CCx (CCx g s) t)) -> Type} ->
         ATmF g s ksi t psi
     -> (IC (CCx g s) -> Type)
preF (AFUN e) ig = (ksi ig, pre psi e ig)

mutual
  vc : {g : Cx} ->
       (phi : IC g -> Type) -> (psi : IC (CCx g t) -> Type) -> ATm g t -> Type
  vc phi psi  (ASU e)          = vc phi (Kc ()) e
  vc phi psi  (AIF c e1 e2)    = ( vc phi (Kc ()) c
                                 , vc (\gam => (phi gam, iATm c gam = True)) psi e1
                                 , vc (\gam => (phi gam, iATm c gam = False)) psi e2)
  vc phi psi  (ALET {s} e1 e2) = ( vc phi (Kc ()) e1
                                 , vc (\gam_s => (phi (fst gam_s), snd gam_s = iATm e1 (fst gam_s)))
                                      (\gams_t => psi ((fst (fst gams_t), snd gams_t))) e2)
  vc phi psi  (APRD e1 e2)     = (vc phi (Kc ()) e1, vc phi (Kc ()) e2)
  vc phi psi  (AFST e)         = vc phi (Kc ()) e
  vc phi psi  (ASND e)         = vc phi (Kc ()) e
  vc phi psi' (AAPP {s} {t} {ksi} {psi} f e) = ( vcF phi f
                                           , vc phi ksi e
                                           , (gam : IC g) -> (is : IU s) -> (it : IU t)
                                              -> phi gam -> ksi (gam, is) -> psi ((gam, is), it) -> psi' (gam, it))
  vc phi psi (ABOP o e1 e2)    = (vc phi (Kc ()) e1, vc phi (Kc ()) e2)
  vc _   _    _                = ()

  vcF : {g : _} -> {s : _} -> {psi : _} -> {ksi : _} ->
        (phi : IC g -> Type) -> ATmF g s ksi t psi -> Type
  vcF phi (AFUN e) = ( (gam : IC g) -> (is : IU s) -> phi gam -> ksi (gam, is) -> pre psi e (gam, is)
                     , vc (\gam_s => (phi (fst gam_s), ksi gam_s)) psi e)

AONE, ATWO, ATHREE : ATm g N
AONE = ASU AZE
ATWO = ASU AONE
ATHREE = ASU ATWO

CONE : CTm g phi N (\gn => snd gn = 1)
CONE = CSU CZE

CTWO : CTm g phi N (\gn => snd gn = 2)
CTWO = CSU CONE

Cf0 : CTmF f phi N (\gn => LT (snd gn) 2) N (\gn => LT (snd gn) 4)
Cf0 = CFUN $ CSUB (CBOP OpPlus (CVAR Top) CONE)
                  _ --(\gn => LT (snd gn) 4)
                  (\(g,x),n,(_,prf),en => rewrite en in
                                          rewrite plusCommutative x 1 in
                                          LTESucc $ lteSuccRight prf)

CEx0 : CTm g phi N (\gn => LT (snd gn) 5)
CEx0 = CSUB (CAPP Cf0 $ CSUB CONE
                             _ --(\gn => LT (snd gn) 2)
                             (\g,n,_,en => rewrite en in reflexive))
            _ --(\gn => LT (snd gn) 5)
            (\gam,x,_,(_ ** (_, prfx)) => lteSuccRight prfx)

Af0 : ATmF g N (\gn => LT (snd gn) 2) N  (\gn => LT (snd gn) 4)
Af0 = AFUN (ABOP OpPlus (AVAR Top) AONE)

AEx0 : ATm g N
AEx0 = AAPP Af0 AONE

0 PreAEx0 : () -> Type
PreAEx0 = pre {g = ECx} (\gn => LT (snd gn) 5) AEx0

0 VcAEx0 : Type
VcAEx0 = vc {g = ECx} (Kc ()) (\gn => LT (snd gn) 5) AEx0

AEx1 : ATm g N
AEx1 = AAPP Af0 ATWO

0 PreAEx1 : () -> Type
PreAEx1 = pre {g = ECx} (\gn => LT (snd gn) 5) AEx1

0 VcAEx1 : Type
VcAEx1 = vc {g = ECx} (Kc ()) (\gn => LT (snd gn) 5) AEx1

AEx2 : ATm g N
AEx2 = ABOP OpPlus AEx0 ATWO

0 PreAEx2 : () -> Type
PreAEx2 = pre {g = ECx} (\gn => LT (snd gn) 6) AEx2

0 VcAEx2 : {g : Cx} -> Type
VcAEx2 = vc {g} (\_ => mkC {g} Af0) (\gn => LT (snd gn) 6) AEx2

0 CEx2Phi : IC g -> Type
CEx2Phi gam = mkC {g} Af0

CEx2 : {0 g : Cx} -> CTm g (CEx2Phi {g}) N (\gn => LT (snd gn) 6)
CEx2 = CSUB (CBOP OpPlus CEx0 CTWO)
            _ --(\gn => LT (snd gn) 6)
            (\gam,x,prf,ex => rewrite ex in
                              plusLteMonotoneRight 2 _ _ $
                              prf _ reflexive)

AEx3 : ATm g N
AEx3 = ABOP OpPlus AEx0 AEx2

0 PreAEx3 : () -> Type
PreAEx3 = pre {g = ECx} (\gn => LT (snd gn) 10) AEx3

PreAEx3prf : CEx2Phi {g=ECx} () -> PreAEx3 ()
PreAEx3prf prf = ( ((),reflexive)
                 , ( (((),reflexive), ((((),()),()),()))
                   , plusLteMonotone (prf _ reflexive) $
                     plusLteMonotoneRight 2 _ _ $
                     lteSuccLeft $ prf _ reflexive
                   )
                 )

0 VcAEx3 : {g : Cx} -> Type
VcAEx3 = vc {g=ECx} (CEx2Phi {g=ECx}) (\gn => LT (snd gn) 10) AEx3

VcAEx3prf : VcAEx3
VcAEx3prf = (((\(),x,prf,lx => ( (),(((),())
                               , plusLteMonotoneRight 1 _ _ $
                                 lteSuccRight lx)
                               )
              , ((),())
              )
             , ((), \(),_,_,_,_,_ => ())
             )
            , (( ( \(),x,prf,lx => ( (),((),())
                                   , plusLteMonotoneRight 1 _ _ $
                                   lteSuccRight lx)

                 , ((),()))
               , ((),\(),_,_,_,_,_ => ())
               ),())
            )

preMono : {gam : IC g} -> {0 psi1, psi2 : IC (CCx g t) -> Type}
       -> (e : ATm g t)
       -> ((it : IU t) -> psi1 (gam,it) -> psi2 (gam,it))
       -> (pre psi1 e gam -> pre psi2 e gam)
preMono (AVAR i)          psi1psi2 p                     = psi1psi2 (IIx i gam) p
preMono  AUNIT            psi1psi2 p                     = psi1psi2 () p
preMono  ATT              psi1psi2 p                     = psi1psi2 True p
preMono  AFF              psi1psi2 p                     = psi1psi2 False p
preMono  AZE              psi1psi2 p                     = psi1psi2 0 p
preMono (ASU e)           psi1psi2 (pre, psi1prf)        = (pre, (psi1psi2 (S (iATm e gam)) psi1prf))
preMono (AIF c e1 e2)     psi1psi2 (pre, pre') with (iATm c gam)
  preMono (AIF c e1 e2)     psi1psi2 (pre, pre') | True  = (pre, preMono e1 psi1psi2 pre')
  preMono (AIF c e1 e2)     psi1psi2 (pre, pre') | False = (pre, preMono e2 psi1psi2 pre')
preMono (ALET e1 e2)      psi1psi2 (pre1, pre2)          = (pre1, (preMono e2 psi1psi2 pre2))
preMono (APRD e1 e2)      psi1psi2 (pre1, pre2, psi1prf) = (pre1, pre2 , (psi1psi2 (iATm e1 gam, iATm e2 gam) psi1prf))
preMono (AFST e)          psi1psi2 (pre, psi1prf)        = (pre, psi1psi2 (fst (iATm e gam)) psi1prf)
preMono (ASND e)          psi1psi2 (pre, psi1prf)        = (pre, psi1psi2 (snd (iATm e gam)) psi1prf)
preMono (AAPP (AFUN f) e) psi1psi2 pre                   = pre
preMono (ABOP o e1 e2)    psi1psi2 (pre1, pre2, psi1prf) = (pre1, pre2, psi1psi2 (iOp o (iATm e1 gam) (iATm e2 gam)) psi1prf)

mutual
  vcMono : {g : Cx} ->
           {0 phi1, phi2 : IC g -> Type} ->
           {0 psi1, psi2 : IC (CCx g t) -> Type}
        -> (e : ATm g t)
        -> ((ig : IC g) -> (phi2 ig -> phi1 ig, (it : IU t) -> phi2 ig -> psi1 (ig,it) -> psi2 (ig,it)))
        -> (vc phi1 psi1 e -> vc phi2 psi2 e)
  vcMono (AVAR i)       _    _              = ()
  vcMono  AUNIT         _    _              = ()
  vcMono  ATT           _    _              = ()
  vcMono  AFF           _    _              = ()
  vcMono  AZE           _    _              = ()
  vcMono (ASU e)        prf  vc             = vcMono {psi1 = Kc ()} e (\g => (fst (prf g), \_,_ => Kc ())) vc
  vcMono (AIF c e1 e2)  prf (vcC, vc1, vc2) =
    ( vcMono c (\ig => (fst (prf ig), \_,_,_ => ())) vcC
    , vcMono e1 (\ig => ( \p_ct => (fst (prf ig) (Builtin.fst p_ct), Builtin.snd p_ct)
                        , \it,p_ct,psi1prf => snd (prf ig) it (Builtin.fst p_ct) psi1prf
                        )) vc1
    , vcMono e2 (\ig => ( \p_cf => (fst (prf ig) (Builtin.fst p_cf), Builtin.snd p_cf)
                        , \it,p_cf,psi1prf => snd (prf ig) it (Builtin.fst p_cf) psi1prf
                        )) vc2
    )
  vcMono (ALET e1 e2)   prf (vc1, vc2)      =
    ( vcMono e1 (\ig => (fst (prf ig), \_,_,_ => ())) vc1
    , vcMono e2 (\(ig,is) => ( \p_is => (fst (prf ig) (Builtin.fst p_is), Builtin.snd p_is)
                             , \it,p_is,psi1prf => snd (prf ig) it (Builtin.fst p_is) psi1prf)) vc2
    )
  vcMono (APRD e1 e2)   prf (vc1, vc2)      =
    ( vcMono e1 (\ig => (fst (prf ig), \_,_,_ => ())) vc1
    , vcMono e2 (\ig => (fst (prf ig), \_,_,_ => ())) vc2
    )
  vcMono (AFST e)       prf  vc             = vcMono {psi1 = Kc ()} e (\ig => (fst (prf ig), \_,_,_ => ())) vc
  vcMono (ASND e)       prf  vc             = vcMono {psi1 = Kc ()} e (\ig => (fst (prf ig), \_,_,_ => ())) vc
  vcMono (AAPP f e)     prf (vcF, vcE, vcR) =
    ( vcFMono f (\ig => fst (prf ig)) vcF
    , vcMono e (\ig => (fst (prf ig), \_,_,kp => kp)) vcE
    , \ig,is,it,phi2prf,psiprf,ksiprf =>
        snd (prf ig) it phi2prf $
          vcR ig is it (fst (prf ig) phi2prf) psiprf ksiprf
    )
  vcMono (ABOP o e1 e2) prf (vc1, vc2)      =
    ( vcMono e1 (\ig => (fst (prf ig), \_,_,_ => ())) vc1
    , vcMono e2 (\ig => (fst (prf ig), \_,_,_ => ())) vc2
    )

  vcFMono : {g : Cx} -> {s : U} ->
            {0 phi1, phi2 : IC g -> Type} ->
            {0 ksi : IC (CCx g s) -> Type} ->
            {0 psi : IC (CCx (CCx g s) t) -> Type} ->
            (f : ATmF g s ksi t psi)
         -> ((ig : IC g) -> phi2 ig -> phi1 ig)
         -> (vcF phi1 f -> vcF phi2 f)
  vcFMono (AFUN e) phi2phi1 (p, vcE) =
    (\g,s,phi2prf,ksiprf => p g s (phi2phi1 g phi2prf) ksiprf
    , vcMono e (\(ig,is) => (\p_k => (phi2phi1 ig (Builtin.fst p_k), Builtin.snd p_k), \_,_,pp => pp))
               vcE
    )
