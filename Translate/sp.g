#  Converted by AH, 4-Jul-19
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Append, ClassicalStandardGenerators, Evaluate,
#  Factorial, GF, Integers, Internal_StandardPresentationForSp, IsEven, IsOdd,
#  IsPrimePower, LHS, Ngens, PrimitiveElement, RHS, SLPGroup,
#  SpConvertToStandard, SpPresentation, SpPresentationToStandard,
#  SpStandardToPresentation, Sp_PresentationForN, Sp_PresentationForN1,
#  Universe, phi, tau

#  Defines: Internal_StandardPresentationForSp, Order_Sp_N, Order_Sp_N1,
#  SpConvertToStandard, SpGenerators, SpPresentation, SpPresentationToStandard,
#  SpStandardToPresentation, Sp_PresentationForN, Sp_PresentationForN1

DeclareGlobalFunction("SpStandardToPresentation");

DeclareGlobalFunction("SpPresentationToStandard");

DeclareGlobalFunction("SpConvertToStandard");

#  Forward declaration of SpStandardToPresentation
#  Forward declaration of SpPresentationToStandard
#  Forward declaration of SpConvertToStandard
SpGenerators:=function(d,q)
local S,U,V,varZ,delta,sigma,tau;
  S:=ClassicalStandardGenerators("Sp",d,q);
  varZ:=S[1];
  V:=S[2];
  tau:=S[3];
  delta:=S[4];
  U:=S[5];
  sigma:=S[6];
  sigma:=((sigma^(V^2))^(varZ^-1));
  return [varZ,V,tau,delta^-1,U,sigma];
end;

Sp_PresentationForN1:=function(n,q)
local F,OMIT,R1,Rels,S,U,V,varZ,m,phi;
  #was: F:=SLPGroup(3);
  F:=FreeGroup("U","V","Z"); # deal with SLP later
  U:=F.1;
  V:=F.2;
  varZ:=F.3;

  #was: R1:=PresentationForSn(n);
  #was: S:=R1.val1;
  #was: R1:=R1.val2;
  R1:=PresentationForSn(n);
  S:=FreeGroupOfFpGroup(R1);
  R1:=RelatorsOfFpFGroup(R1);

  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V]);
  #was: Rels:=List(R1,r->phi(r));
  Rels:=List(R1,r->Image(phi,r));
  OMIT:=true;
  if not OMIT then
    # rewritten select statement
    if IsOddInt(q) then
      m:=4;
    else
      m:=2;
    fi;
    Add(Rels,varZ^m);
  fi;
  if n > 2 then
    #was: Add(Rels,Comm(varZ,U^V));
    Add(Rels,Comm(varZ,U^V)));
  fi;
  if n > 3 then
    #was: Add(Rels,Comm(varZ,V*U));
    Add(Rels,Comm(varZ,V*U));
  fi;
  #was:Add(Rels,Comm(varZ,varZ^U));
  Add(Rels,Comm(varZ,varZ^U));
  #was: return rec(val1:=F, val2:=Rels);
  return F/Rels;
end;

Order_Sp_N1:=function(n,q)
if IsEvenInt(q) then
    return 2^n*Factorial(n);
  else
    return 4^n*Factorial(n);
  fi;
end;

#   presentation for D_{2(q-1)} wr Sym (n) for q even or Q_{2(q-1)} wr Sym (n)
#  for q odd
Sp_PresentationForN:=function(n,q)
local F,OMIT,R1,Rels,S,U,V,varZ,delta,e,f,p,phi;
  #was: e:=IsPrimePower(q);
  #was: f:=e.val1;
  #was: p:=e.val2;
  #was: e:=e.val3;
  f:=Factors(q);
  p:=f[1];
  e:=Length(f);
  f:=Set(f)=[p];
  #was: F:=SLPGroup(4);
  F:=FreeGroup("U","V","Z","delta"); # deal with SLP later
  U:=F.1;
  V:=F.2;
  varZ:=F.3;
  delta:=F.4;
  #was: R1:=Sp_PresentationForN1(n,q);
  #was: S:=R1.val1;
  #was: R1:=R1.val2;
  R1:=Sp_PresentationForN1(n,q);
  S:=FreeGroupOfFpGroup(R1);
  R1:=RelatorsOfFpFGroup(R1);

  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V,varZ]);
  #was: R1:=List(R1,r->phi(r));
  R1:=List(R1,r->Image(phi,r));
  Rels:=[];
  OMIT:=true;
  if not OMIT then
    if IsEvenInt(q) then
      #was: Add(Rels,delta^(q-1)=1);
      Add(Rels,delta^(q-1));
    else
      #was: Add(Rels,varZ^2=delta^(QuoInt((q-1),2)));
      Add(Rels,varZ^2/(delta^(QuoInt((q-1),2))));
    fi;
    #was:Add(Rels,delta^varZ=delta^-1);
    Add(Rels,delta^varZ/delta^-1);
  fi;
  if n > 2 then
    #was: Add(Rels,Comm(delta,U^V)=1);
    Add(Rels,Comm(delta,U^V));
  fi;
  if n > 3 then
    #was: Add(Rels,Comm(delta,V*U)=1);
    Add(Rels,Comm(delta,V*U));
  fi;
  #was: Add(Rels,Comm(varZ,delta^U)=1);
  Add(Rels,Comm(varZ,delta^U));
  #was: Add(Rels,Comm(delta,delta^U)=1);
  Add(Rels,Comm(delta,delta^U));
  #was: Rels:=Concatenation(List(Rels,r->LHS(r)*RHS(r)^-1),R1);
  # but not needed any longer, as we did so when collecting relators
  #was: return rec(val1:=F, val2:=Rels);
  return F/Rels;
end;

Order_Sp_N:=function(n,q)
  return (2*(q-1))^n*Factorial(n);
end;

SpPresentation:=function(d,q)
local Delta,F,I,R1,R2,R3,Rels,S,U,V,W,varZ,a,b,delta,e,f,n,p,phi,sigma,tau,w,wm1;
  Assert(1,IsPrimePower(q));
  Assert(1,d > 2);
  Assert(1,IsEvenInt(d));
  n:=QuoInt(d,2);
  #was: e:=IsPrimePower(q);
  #was: f:=e.val1;
  #was: p:=e.val2;
  #was: e:=e.val3;
  f:=Factors(q);
  p:=f[1];
  e:=Length(f);
  f:=Set(f)=[p];
  #was: F:=SLPGroup(6);
  F:=FreeGroup("Z","V","tau","delta","U","sigma"); # deal with SLP later
  varZ:=F.1;
  V:=F.2;
  tau:=F.3;
  delta:=F.4;
  U:=F.5;
  sigma:=F.6;
  #   we don't need delta if e = 1 but it makes presentation consistent for all
  #  q
  Rels:=[];
  if e=1 then
    w:=PrimitiveElement(GF(p));
    #was I:=Integers();
    #was: a:=(w-w^2)*FORCEOne(I);
    a:=Int(w-w^2);
    #was: b:=(w-1)*FORCEOne(I);
    b:=Int(w-1);
    #was: wm1:=(w^-1)*FORCEOne(I);
    wm1:=Int(w^-1);
    #was Add(Rels,delta=(tau^a)^varZ*tau^(wm1)*(tau^b)^varZ*tau^-1);
    Add(Rels,delta/((tau^a)^varZ*tau^(wm1)*(tau^b)^varZ*tau^-1));
  fi;
  #   presentation for D_{2(q-1)} wr Sym (n) for q even or Q_{2(q-1)} wr Sym
  #  (n) for q odd
  if e=1 then
    #was: R1:=Sp_PresentationForN1(n,q);
    #was: S:=R1.val1;
    #was: R1:=R1.val2;
    R1:=Sp_PresentationForN1(n,q);
    S:=FreeGroupOfFpGroup(R1);
    R1:=RelatorsOfFpFGroup(R1);

    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [U,V,varZ]);
  else
    #was: R1:=Sp_PresentationForN(n,q);
    #was: S:=R1.val1;
    #was: R1:=R1.val2;
    R1:=Sp_PresentationForN1(n,q);
    S:=FreeGroupOfFpGroup(R1);
    R1:=RelatorsOfFpFGroup(R1);

    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [U,V,varZ,delta]);
  fi;
  #was: R1:=List(R1,r->phi(r));
  R1:=List(R1,r->Image(phi,r));
  #   centraliser of tau
  #was: Add(Rels,Comm(tau,varZ^U)=1);
  Add(Rels,Comm(tau,varZ^U));
  if n > 2 then
    Add(Rels,Comm(tau,U^V)=1);
  fi;
  if n > 3 and IsEvenInt(q) then
    Add(Rels,Comm(tau,V*U)=1);
  fi;
  if IsOddInt(q) then
    Add(Rels,Comm(tau,varZ^2)=1);
  fi;
  if e > 1 then
    Add(Rels,Comm(tau,delta^U)=1);
  fi;
  #   centraliser of sigma
  Add(Rels,Comm(sigma,varZ*U*varZ^-1)=1);
  if n > 2 then
    Add(Rels,Comm(sigma,varZ^(V^2))=1);
    if e > 1 then
      Add(Rels,Comm(sigma,delta^(V^2))=1);
    fi;
  fi;
  if n > 3 then
    Add(Rels,Comm(sigma,U^(V^2))=1);
  fi;
  if n > 4 then
    Add(Rels,Comm(sigma,V*U*U^V)=1);
  fi;
  if IsOddInt(q) and e=1 then
    Add(Rels,Comm(sigma,Comm(varZ^2,U))=1);
  fi;
  if e > 1 then
    Add(Rels,Comm(sigma,delta*delta^V)=1);
  fi;
  #   presentation for SL(2, q) on <delta, tau, Z>
  #was: R2:=PresentationForSL2(p,e);
  #was: S:=R2.val1;
  #was: R2:=R2.val2;
  R2:=PresentationForSL2(p,e);
  S:=FreeGroupOfFpGroup(R2);
  R2:=RelatorsOfFpFGroup(R2);
  if e=1 then
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [tau,varZ]);
  else
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [delta,tau,varZ]);
  fi;
  #was: R2:=List(R2,r->phi(r));
  R2:=List(R2,r->Image(phi,r));
  #   presentation for SL(2, q) on <Delta, sigma, W>
  # rewritten select statement
  if IsEvenInt(q) then
    W:=U;
  else
    W:=U*varZ^2;
  fi;
  #was: R3:=PresentationForSL2(p,e);
  #was: S:=R3.val1;
  #was: R3:=R3.val2;
  R3:=PresentationForSL2(p,e);
  S:=FreeGroupOfFpGroup(R3);
  R3:=RelatorsOfFpFGroup(R3);
  if e=1 then
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [sigma,W]);
  else
    lvarDelta:=Comm(U,delta);
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [lvarDelta,sigma,W]);
  fi;
  #was: R3:=List(R3,r->phi(r));
  R3:=List(R3,r->Image(phi,r));
  #   Steinberg relations
  if n > 2 then
    Add(Rels,Comm(sigma,sigma^V)=sigma^(V*U));
    Add(Rels,Comm(sigma,sigma^(V*U))=1);
    Add(Rels,Comm(sigma,sigma^(U*V))=1);
  fi;
  if n > 3 then
    Add(Rels,Comm(sigma,sigma^(V^2))=1);
  fi;
  if IsOddInt(q) then
    Add(Rels,Comm(sigma,sigma^varZ)=(tau^2)^(varZ*U));
  else
    Add(Rels,Comm(sigma,sigma^varZ)=1);
  fi;
  Add(Rels,Comm(sigma,tau)=1);
  Add(Rels,Comm(sigma,tau^U)=sigma^(varZ^U)*tau^-1);
  if n > 2 then
    Add(Rels,Comm(sigma,tau^(V^2))=1);
  fi;
  Add(Rels,Comm(tau,tau^U)=1);
  Rels:=Concatenation(List(Rels,r->LHS(r)*RHS(r)^-1),R1,R2,R3);
  return rec(val1:=F,
    val2:=Rels);
end;

#  ///////////////////////////////////////////////////////////////////////
#     standard presentation for Sp(d, q)                                //
#                                                                       //
#     Input two parameters to compute this presentation of Sp(d, q)     //
#       d = dimension                                                   //
#       q = field order                                                 //
#                                                                       //
#     July 2018                                                         //
#  ///////////////////////////////////////////////////////////////////////
Internal_StandardPresentationForSp:=function(d,q)
#  -> ,GrpSLP ,[ ,]  return standard presentation for Sp ( d , q ) ; if
#  Projective := true , then return presentation for PSp ( n , q )
local Presentation,Projective;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  if not d > 2 and IsEvenInt(d) then
    Error("Degree must be at least 4 and even");
  fi;
  if not IsPrimePower(q) then
    Error("Field size is not valid");
  fi;
  return Internal_StandardPresentationForSp(d,GF(q)
   :Presentation:=Presentation,Projective:=Projective);
end;

Internal_StandardPresentationForSp:=function(d,K)
#  -> ,GrpSLP ,[ ,]  return standard presentation for Sp ( n , K ) ; if
#  Projective := true , then return presentation for PSp ( n , K )
local P,Presentation,Projective,R,Rels,S,V,varZ,q;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  if not d > 2 and IsEvenInt(d) then
    Error("Degree must be at least 4 and even");
  fi;
  q:=Size(K);
  #was: R:=SpPresentation(d,q);
  #was: P:=R.val1;
  #was: R:=R.val2;
  R:=SpPresentation(d,q);
  P:=FreeGroupOfFpGroup(R);
  R:=RelatorsOfFpFGroup(R);
  #   add relation for PSp (d, q)
  if IsOddInt(q) and Projective then
    varZ:=P.1;
    V:=P.2;
    Add(R,(varZ*V)^d);
  fi;
  if Presentation then
    return rec(val1:=P,
      val2:=R);
  fi;
  #was: Rels:=SpConvertToStandard(QuoInt(d,2),q,R);
  #was: S:=Rels.val1;
  #was: Rels:=Rels.val2;
  Rels:=SpConvertToStandard(QuoInt(d,2),q,R);
  S:=FreeGroupOfFpGroup(Rels);
  Rels:=RelatorsOfFpFGroup(Rels);
  Rels:=Filtered(Rels,w->w<>w^0);
  #was: return rec(val1:=S, val2:=Rels);
  return S/Rels;
end;

#   relations are on presentation generators;
#  convert to relations on standard generators 
InstallGlobalFunction(SpConvertToStandard,
function(d,q,Rels)
local A,B,C,Rels,T,U,W,tau;
  A:=SpStandardToPresentation(d,q);
  Rels:=Evaluate(Rels,A);
  B:=SpPresentationToStandard(d,q);
  C:=Evaluate(B,A);
  U:=Universe(C);
  W:=Universe(Rels);
  tau:=GroupHomomorphismByImages(U,W,
    GeneratorsOfGroup(U),List([1..Ngens(W)],i->W.i));
  T:=List([1..Ngens(W)],i->W.i^-1*tau(C[i]));
  Rels:=Concatenation(Rels,T);
  return rec(val1:=W,
    val2:=Rels);
end);

#   express presentation generators as words in standard generators 
InstallGlobalFunction(SpStandardToPresentation,
function(d,q)
local W;
  #was: W:=SLPGroup(6);
  F:=FreeGroup("Z","V","tau","delta","U","sigma"); # deal with SLP later
  #   sequence [Z, V, tau, delta, U, sigma]
  return [W.1,W.2,W.3,W.4^-1,W.5,(W.6^(W.2^2))^(W.1^-1)];
end);

#   express standard generators as words in presentation generators 
InstallGlobalFunction(SpPresentationToStandard,
function(d,q)
local W;
  #was: W:=SLPGroup(6);
  F:=FreeGroup("s","V","t","delta","U","x"); # deal with SLP later
  #   [s, V, t, delta, U, x]
  return [W.1,W.2,W.3,W.4^-1,W.5,(W.6^W.1)^(W.2^-2)];
end);


