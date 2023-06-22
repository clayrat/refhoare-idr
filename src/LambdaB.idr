module LambdaB

public export
data U = One | Two | N | Prod U U

public export
IU : U -> Type
IU One        = ()
IU Two        = Bool
IU N          = Nat
IU (Prod s t) = (IU s, IU t)

public export
data Cx = ECx | CCx Cx U

public export
IC : Cx -> Type
IC  ECx      = ()
IC (CCx g s) = (IC g, IU s)

public export
data Ix : Cx -> U -> Type where
  Top :           Ix (CCx g t) t
  Pop : Ix g t -> Ix (CCx g s) t

public export
IIx : Ix g t -> IC g -> IU t
IIx  Top    (_ , s) = s
IIx (Pop i) (g', _) = IIx i g'

public export
Kc : a -> b -> a
Kc = const

public export
Sc : {0 a : Type} -> {0 b : a -> Type} -> {0 c : (x : a) -> b x -> Type}
  -> (f : (x : a) -> (y : b x) -> c x y)
  -> (g : (x : a) -> b x)
  -> (x : a) -> c x (g x)
Sc f g x = f x (g x)

public export
data Op = OpPlus | OpMinus | OpLt | OpEq | OpAnd

public export
opL : Op -> U
opL OpPlus  = N
opL OpMinus = N
opL OpLt    = N
opL OpEq    = N
opL OpAnd   = Two

public export
opR : Op -> U
opR OpPlus  = N
opR OpMinus = N
opR OpLt    = Two
opR OpEq    = Two
opR OpAnd   = Two

mutual
  public export
  data Tm : Cx -> U -> Type where
    VAR  : Ix g t -> Tm g t
    UNIT : Tm g One
    TT   : Tm g Two
    FF   : Tm g Two
    ZE   : Tm g N
    SU   : Tm g N -> Tm g N
    IF   : Tm g Two -> Tm g t -> Tm g t -> Tm g t
    LET  : Tm g s -> Tm (CCx g s) t -> Tm g t
    PRD  : Tm g s -> Tm g t -> Tm g (Prod s t)
    FST  : Tm g (Prod s t) -> Tm g s
    SND  : Tm g (Prod s t) -> Tm g t
    APP  : TmF g s t -> Tm g s -> Tm g t
    BOP  : (o : Op) -> Tm g (opL o) -> Tm g (opL o) -> Tm g (opR o)

  public export
  data TmF : Cx -> U -> U -> Type where
    FUN : Tm (CCx g s) t -> TmF g s t

export
IFhelper : {0 t : U} -> {c, c1 : Tm g Two} -> {x, x1, y, y1 : Tm g t} ->
           c = c1 -> x = x1 -> y = y1 -> IF c x y = IF c1 x1 y1
IFhelper Refl Refl Refl = Refl

public export
iOp : (o : Op) -> IU (opL o) -> IU (opL o) -> IU (opR o)
iOp OpPlus  = (+)
iOp OpMinus = minus
iOp OpLt    = (<)
iOp OpEq    = (==)
iOp OpAnd   = \b1,b2 => b1 && b2

mutual
  public export
  iTm : Tm g t -> IC g -> IU t
  iTm (VAR x)       = IIx x
  iTm  UNIT         = Kc ()
  iTm  TT           = Kc True
  iTm  FF           = Kc False
  iTm  ZE           = Kc 0
  iTm (SU e)        = Sc (Kc S) (iTm e)
  iTm (IF c e1 e2)  = \g => ifThenElse (iTm c g) (iTm e1 g) (iTm e2 g)
  iTm (LET e1 e2)   = Sc (curry (iTm e2)) (iTm e1)
  iTm (PRD e1 e2)   = \g => (iTm e1 g, iTm e2 g)
  iTm (FST e)       = fst . iTm e
  iTm (SND e)       = snd . iTm e
  iTm (APP f e)     = Sc (iTmf f) (iTm e)
  iTm (BOP o e1 e2) = \g => iOp o (iTm e1 g) (iTm e2 g)

  public export
  iTmf : TmF g s t -> IC g -> IU s -> IU t
  iTmf (FUN e) = curry (iTm e)

public export
ONE,TWO,THREE,FOUR,FIVE,SIX,SEVEN,EIGHT : Tm g N
ONE   = SU ZE
TWO   = SU ONE
THREE = SU TWO
FOUR  = SU THREE
FIVE  = SU FOUR
SIX   = SU FIVE
SEVEN = SU SIX
EIGHT = SU SEVEN

public export
-- \x.x+1
f0 : TmF g N N
f0 = FUN (BOP OpPlus (VAR Top) ONE)

I_f0 : IC g -> Nat -> Nat
I_f0 = iTmf f0

public export
subst : (phi : IC (CCx g t) -> Type) -> (e : Tm g t) -> IC g -> Type
subst phi e = Sc (curry phi) (iTm e)
