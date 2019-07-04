#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Append, ClassicalStandardGenerators, Evaluate,
#  Factorial, GF, Integers, IsEven, IsOdd, IsPrimePower, LHS, Ngens,
#  PrimitiveElement, RHS, SLPGroup, SpConvertToStandard, SpPresentation,
#  SpPresentationToStandard, SpStandardToPresentation, Sp_PresentationForN,
#  Sp_PresentationForN1, StandardPresentationForSp, Universe, phi, tau

#  Defines: Order_Sp_N, Order_Sp_N1, SpConvertToStandard, SpGenerators,
#  SpPresentation, SpPresentationToStandard, SpStandardToPresentation,
#  Sp_PresentationForN, Sp_PresentationForN1, StandardPresentationForSp

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
  F:=SLPGroup(3);
  U:=F.1;
  V:=F.2;
  varZ:=F.3;
  # =v= MULTIASSIGN =v=
  R1:=PresentationForSn(n);
  S:=R1.val1;
  R1:=R1.val2;
  # =^= MULTIASSIGN =^=
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V]);
  Rels:=List(R1,r->phi(r));
  OMIT:=true;
  if not OMIT then
    # rewritten select statement
    if IsOddInt(q) then
      m:=4;
    else
      m:=2;
    fi;
    Append(TILDERels,varZ^m);
  fi;
  if n > 2 then
    Append(TILDERels,Tuple([varZ,U^V]));
  fi;
  if n > 3 then
    Append(TILDERels,Tuple([varZ,V*U]));
  fi;
  Append(TILDERels,Tuple([varZ,varZ^U]));
  return rec(val1:=F,
    val2:=Rels);
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
  # =v= MULTIASSIGN =v=
  e:=IsPrimePower(q);
  f:=e.val1;
  p:=e.val2;
  e:=e.val3;
  # =^= MULTIASSIGN =^=
  F:=SLPGroup(4);
  U:=F.1;
  V:=F.2;
  varZ:=F.3;
  delta:=F.4;
  # =v= MULTIASSIGN =v=
  R1:=Sp_PresentationForN1(n,q);
  S:=R1.val1;
  R1:=R1.val2;
  # =^= MULTIASSIGN =^=
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V,varZ]);
  R1:=List(R1,r->phi(r));
  Rels:=[];
  OMIT:=true;
  if not OMIT then
    if IsEvenInt(q) then
      Append(TILDERels,delta^(q-1)=1);
    else
      Append(TILDERels,varZ^2=delta^(QuoInt((q-1),2)));
    fi;
    Append(TILDERels,delta^varZ=delta^-1);
  fi;
  if n > 2 then
    Append(TILDERels,Tuple([delta,U^V])=1);
  fi;
  if n > 3 then
    Append(TILDERels,Tuple([delta,V*U])=1);
  fi;
  Append(TILDERels,Tuple([varZ,delta^U])=1);
  Append(TILDERels,Tuple([delta,delta^U])=1);
  Rels:=Concatenation(List(Rels,r->LHS(r)*RHS(r)^-1),R1);
  return rec(val1:=F,
    val2:=Rels);
end;

Order_Sp_N:=function(n,q)
return (2*(q-1))^n*Factorial(n);
end;

SpPresentation:=function(d,q)
local 
   Delta,F,I,R1,R2,R3,Rels,S,U,V,W,varZ,a,b,delta,e,f,n,p,phi,sigma,tau,w,wm1;
  Assert(1,IsPrimePower(q));
  Assert(1,d > 2);
  Assert(1,IsEvenInt(d));
  n:=QuoInt(d,2);
  # =v= MULTIASSIGN =v=
  e:=IsPrimePower(q);
  f:=e.val1;
  p:=e.val2;
  e:=e.val3;
  # =^= MULTIASSIGN =^=
  F:=SLPGroup(6);
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
    I:=Integers();
    a:=(w-w^2)*FORCEOne(I);
    b:=(w-1)*FORCEOne(I);
    wm1:=(w^-1)*FORCEOne(I);
    Append(TILDERels,delta=(tau^a)^varZ*tau^(wm1)*(tau^b)^varZ*tau^-1);
  fi;
  #   presentation for D_{2(q-1)} wr Sym (n) for q even or Q_{2(q-1)} wr Sym
  #  (n) for q odd
  if e=1 then
    # =v= MULTIASSIGN =v=
    R1:=Sp_PresentationForN1(n,q);
    S:=R1.val1;
    R1:=R1.val2;
    # =^= MULTIASSIGN =^=
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [U,V,varZ]);
  else
    # =v= MULTIASSIGN =v=
    R1:=Sp_PresentationForN(n,q);
    S:=R1.val1;
    R1:=R1.val2;
    # =^= MULTIASSIGN =^=
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [U,V,varZ,delta]);
  fi;
  R1:=List(R1,r->phi(r));
  #   centraliser of tau
  Append(TILDERels,Tuple([tau,varZ^U])=1);
  if n > 2 then
    Append(TILDERels,Tuple([tau,U^V])=1);
  fi;
  if n > 3 and IsEvenInt(q) then
    Append(TILDERels,Tuple([tau,V*U])=1);
  fi;
  if IsOddInt(q) then
    Append(TILDERels,Tuple([tau,varZ^2])=1);
  fi;
  if e > 1 then
    Append(TILDERels,Tuple([tau,delta^U])=1);
  fi;
  #   centraliser of sigma
  Append(TILDERels,Tuple([sigma,varZ*U*varZ^-1])=1);
  if n > 2 then
    Append(TILDERels,Tuple([sigma,varZ^(V^2)])=1);
    if e > 1 then
      Append(TILDERels,Tuple([sigma,delta^(V^2)])=1);
    fi;
  fi;
  if n > 3 then
    Append(TILDERels,Tuple([sigma,U^(V^2)])=1);
  fi;
  if n > 4 then
    Append(TILDERels,Tuple([sigma,V*U*U^V])=1);
  fi;
  if IsOddInt(q) and e=1 then
    Append(TILDERels,Tuple([sigma,Tuple([varZ^2,U])])=1);
  fi;
  if e > 1 then
    Append(TILDERels,Tuple([sigma,delta*delta^V])=1);
  fi;
  #   presentation for SL(2, q) on <delta, tau, Z>
  # =v= MULTIASSIGN =v=
  R2:=PresentationForSL2(p,e);
  S:=R2.val1;
  R2:=R2.val2;
  # =^= MULTIASSIGN =^=
  if e=1 then
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [tau,varZ]);
  else
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [delta,tau,varZ]);
  fi;
  R2:=List(R2,r->phi(r));
  #   presentation for SL(2, q) on <Delta, sigma, W>
  # rewritten select statement
  if IsEvenInt(q) then
    W:=U;
  else
    W:=U*varZ^2;
  fi;
  # =v= MULTIASSIGN =v=
  R3:=PresentationForSL2(p,e);
  S:=R3.val1;
  R3:=R3.val2;
  # =^= MULTIASSIGN =^=
  if e=1 then
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [sigma,W]);
  else
    lvarDelta:=Tuple([U,delta]);
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [lvarDelta,sigma,W]);
  fi;
  R3:=List(R3,r->phi(r));
  #   Steinberg relations
  if n > 2 then
    Append(TILDERels,Tuple([sigma,sigma^V])=sigma^(V*U));
    Append(TILDERels,Tuple([sigma,sigma^(V*U)])=1);
    Append(TILDERels,Tuple([sigma,sigma^(U*V)])=1);
  fi;
  if n > 3 then
    Append(TILDERels,Tuple([sigma,sigma^(V^2)])=1);
  fi;
  if IsOddInt(q) then
    Append(TILDERels,Tuple([sigma,sigma^varZ])=(tau^2)^(varZ*U));
  else
    Append(TILDERels,Tuple([sigma,sigma^varZ])=1);
  fi;
  Append(TILDERels,Tuple([sigma,tau])=1);
  Append(TILDERels,Tuple([sigma,tau^U])=sigma^(varZ^U)*tau^-1);
  if n > 2 then
    Append(TILDERels,Tuple([sigma,tau^(V^2)])=1);
  fi;
  Append(TILDERels,Tuple([tau,tau^U])=1);
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
StandardPresentationForSp:=function(d,q)
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
  return StandardPresentationForSp(d,GF(q)
   :Presentation:=Presentation,Projective:=Projective);
end;

StandardPresentationForSp:=function(d,K)
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
  # =v= MULTIASSIGN =v=
  R:=SpPresentation(d,q);
  P:=R.val1;
  R:=R.val2;
  # =^= MULTIASSIGN =^=
  #   add relation for PSp (d, q)
  if IsOddInt(q) and Projective then
    varZ:=P.1;
    V:=P.2;
    Append(TILDER,(varZ*V)^d);
  fi;
  if Presentation then
    return rec(val1:=P,
      val2:=R);
  fi;
  # =v= MULTIASSIGN =v=
  Rels:=SpConvertToStandard(QuoInt(d,2),q,R);
  S:=Rels.val1;
  Rels:=Rels.val2;
  # =^= MULTIASSIGN =^=
  Rels:=Filtered(Rels,w->w<>w^0);
  return rec(val1:=S,
    val2:=Rels);
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
  W:=SLPGroup(6);
  #   sequence [Z, V, tau, delta, U, sigma]
  return [W.1,W.2,W.3,W.4^-1,W.5,(W.6^(W.2^2))^(W.1^-1)];
end);

#   express standard generators as words in presentation generators 
InstallGlobalFunction(SpPresentationToStandard,
function(d,q)
local W;
  W:=SLPGroup(6);
  #   [s, V, t, delta, U, x]
  return [W.1,W.2,W.3,W.4^-1,W.5,(W.6^W.1)^(W.2^-2)];
end);


