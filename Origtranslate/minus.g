#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Append, Characteristic, ClassicalStandardGenerators,
#  ClassicalStandardPresentation, Evaluate, Factorial, GF, GL, Identity,
#  IsEven, IsOdd, IsPrimePower, LHS, Log, MatrixAlgebra, Minus6Presentation,
#  MinusConvertToStandard, MinusDeltaMatrix, MinusEvenDeltaMatrix,
#  MinusGeneratorOfCentre, MinusPresentationToStandard,
#  MinusStandardToPresentation, Minus_PresentationForN,
#  Minus_PresentationForN1, Ngens, PrimitiveElement, RHS, SLPGroup,
#  Setup_MinusPresentation, StandardPresentationForSU, Universe, Zero, eta,
#  phi, tau

#  Defines: Minus6Presentation, MinusConvertToStandard, MinusDeltaMatrix,
#  MinusEvenDeltaMatrix, MinusGeneratorOfCentre, MinusGenerators,
#  MinusPresentation, MinusPresentationToStandard, MinusStandardToPresentation,
#  Minus_OrderN, Minus_Order_N1, Minus_PresentationForN,
#  Minus_PresentationForN1, Setup_MinusPresentation

DeclareGlobalFunction("MinusGeneratorOfCentre");

DeclareGlobalFunction("MinusConvertToStandard");

DeclareGlobalFunction("MinusPresentationToStandard");

DeclareGlobalFunction("MinusStandardToPresentation");

#  Forward declaration of MinusGeneratorOfCentre
#  Forward declaration of MinusConvertToStandard
#  Forward declaration of MinusPresentationToStandard
#  Forward declaration of MinusStandardToPresentation
MinusDeltaMatrix:=function(d,q,w,i)
local A,B,C,MA,delta,n,psi,w0;
  w0:=w^(q+1);
  psi:=w^(QuoInt((q+1),2));
  Assert(1,psi=-(w^(QuoInt((q^2+q),2))));
  Assert(1,psi^q=-psi);
  MA:=MatrixAlgebra(GF(q),d);
  A:=(w^(q-1)+w^(1-q))/2;
  B:=psi*(w^(1-q)-w^(q-1))/2;
  C:=psi^-1*(w^(1-q)-w^(q-1))/2;
  delta:=Identity(MA);
  n:=QuoInt((d-2),2);
  delta[2*i-1][2*i-1]:=w0^-1;
  delta[2*i][2*i]:=w0;
  delta[d-1][d-1]:=A;
  delta[d-1][d]:=-C;
  delta[d][d-1]:=-B;
  delta[d][d]:=A;
  return delta*FORCEOne(GL(d,q));
end;

MinusEvenDeltaMatrix:=function(d,q,w,i)
local A,B,C,MA,delta,n,w0;
  w0:=w^(q+1);
  MA:=MatrixAlgebra(GF(q),d);
  A:=(w^(1-q)+w^(q-1)+1);
  B:=(w^(1)+w^(q));
  C:=(w^(-1)+w^(-q));
  delta:=Identity(MA);
  n:=QuoInt((d-2),2);
  delta[2*i-1][2*i-1]:=w0^-1;
  delta[2*i][2*i]:=w0;
  delta[d-1][d-1]:=A;
  delta[d-1][d]:=C;
  delta[d][d-1]:=B;
  delta[d][d]:=1;
  return delta*FORCEOne(GL(d,q));
end;

MinusGenerators:=function(d,q)
local B,varE,MA,U,V,delta,gens,i,n,s,sigma,tau,w,z;
  if d=4 then
    return ClassicalStandardGenerators("Omega-",d,q);
  fi;
  MA:=MatrixAlgebra(GF(q),d);
  varE:=GF(q^2);
  w:=PrimitiveElement(varE);
  i:=1;
  if IsEvenInt(q) then
    delta:=MinusEvenDeltaMatrix(d,q,w,i);
  else
    delta:=MinusDeltaMatrix(d,q,w,i);
  fi;
  n:=QuoInt((d-2),2);
  z:=Zero(MA);
  z[1][2]:=1;
  z[2][1]:=1;
  for i in [3..d-1] do
    z[i][i]:=1;
  od;
  if IsOddInt(q) then
    z[d-1][d-1]:=-1;
  else
    B:=w+w^q;
    z[d][d-1]:=B;
  fi;
  z[d][d]:=1;
  tau:=Identity(MA);
  if IsOddInt(q) then
    s:=1;
    tau[1][1]:=1;
    tau[1][2]:=s^2;
    tau[1][d-1]:=s;
    tau[d-1][d-1]:=1;
    tau[d-1][2]:=2*s;
  else
    B:=w+w^q;
    tau[1][1]:=1;
    tau[1][2]:=1;
    tau[1][d-1]:=1;
    tau[d][d]:=1;
    tau[d][2]:=B;
  fi;
  s:=1;
  sigma:=Zero(MA);
  sigma[1][1]:=1;
  sigma[1][3]:=s;
  sigma[4][4]:=1;
  sigma[4][2]:=-s;
  for i in Concatenation([2,3],[5..d]) do
    sigma[i][i]:=1;
  od;
  U:=Zero(MA);
  U[1][3]:=1;
  U[3][1]:=-1;
  U[2][4]:=1;
  U[4][2]:=-1;
  for i in [5..d] do
    U[i][i]:=1;
  od;
  V:=Zero(MA);
  for i in [1..n-1] do
    V[2*i-1][2*i+1]:=1;
    V[2*i][2*i+2]:=1;
  od;
  V[d-3][1]:=(-1)^(n-1);
  V[d-2][2]:=(-1)^(n-1);
  for i in [d-1..d] do
    V[i][i]:=1;
  od;
  gens:=List([z,tau,sigma,delta,U,V],x->x*FORCEOne(GL(d,q)));
  return rec(val1:=gens,
    val2:=varE,
    val3:=w);
end;

Minus6Presentation:=function(q)
local N,Q,R,S,U,d,delta,eta,images,sigma,tau,z;
  d:=4;
  # =v= MULTIASSIGN =v=
  R:=StandardPresentationForSU(d,q:Presentation:=true);
  Q:=R.val1;
  R:=R.val2;
  # =^= MULTIASSIGN =^=
  N:=SLPGroup(5);
  z:=N.1;
  tau:=N.2;
  sigma:=N.3;
  delta:=N.4;
  U:=N.5;
  if IsOddInt(q) then
    images:=[U,z*U^2,sigma,delta*(delta^-1)^U,z*U^2,tau^-1,delta];
  else
    images:=[U,z,sigma,delta*(delta^-1)^U,z,tau^1,delta];
  fi;
  eta:=GroupHomomorphismByImages(Q,N,
    GeneratorsOfGroup(Q),images);
  S:=List(R,r->eta(r));
  if IsOddInt(q) then
    Append(TILDES,delta^(QuoInt((q^2-1),2)));
  fi;
  return rec(val1:=N,
    val2:=S);
end;

Minus_PresentationForN1:=function(d,q)
local F,OMIT,R,R1,Rels,S,U,V,m,n,phi,z;
  F:=SLPGroup(3);
  z:=F.1;
  U:=F.2;
  V:=F.3;
  m:=QuoInt((d-2),2);
  if IsOddInt(q) then
    # =v= MULTIASSIGN =v=
    R:=SignedPermutations(m);
    S:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  elif IsEvenInt(q) then
    # =v= MULTIASSIGN =v=
    R:=PresentationForSn(m);
    S:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  fi;
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V]);
  R:=List(R,r->phi(r));
  n:=QuoInt(d,2);
  R1:=[];
  Append(TILDER1,Tuple([z,U^V])=1);
  if n > 4 then
    Append(TILDER1,Tuple([z,V*U^-1])=1);
  fi;
  OMIT:=true;
  if not OMIT then
    Append(TILDER1,z^2=1);
    Append(TILDER1,Tuple([z,z^U])=1);
    if IsOddInt(q) then
      Append(TILDER1,Tuple([z,U^2])=1);
    fi;
  fi;
  Rels:=Concatenation(List(R1,r->LHS(r)*RHS(r)^-1),R);
  return rec(val1:=F,
    val2:=Rels);
end;

Minus_Order_N1:=function(d,q)
local n;
  n:=QuoInt(d,2);
  if IsOddInt(q) then
    return 2^(2*n-3)*Factorial(n-1);
  else
    return 2^(n-1)*Factorial(n-1);
  fi;
end;

Minus_PresentationForN:=function(d,q)
local F,OMIT,R,R1,Rels,S,U,V,delta,n,phi,z;
  F:=SLPGroup(4);
  delta:=F.1;
  z:=F.2;
  U:=F.3;
  V:=F.4;
  # =v= MULTIASSIGN =v=
  R:=Minus_PresentationForN1(d,q);
  S:=R.val1;
  R:=R.val2;
  # =^= MULTIASSIGN =^=
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [z,U,V]);
  R:=List(R,r->phi(r));
  n:=QuoInt(d,2);
  R1:=[];
  Append(TILDER1,Tuple([delta,U^V])=1);
  if n > 4 then
    Append(TILDER1,Tuple([delta,V*U^-1])=1);
  fi;
  OMIT:=true;
  if not OMIT then
    if IsOddInt(q) then
      Append(TILDER1,U^2=(delta*(delta^-1)^U)^(QuoInt((q-1),2)));
    fi;
    Append(TILDER1,Tuple([delta,z^U])=delta^(q-1));
    if IsOddInt(q) then
      Append(TILDER1,delta^(QuoInt((q^2-1),2))=1);
    else
      Append(TILDER1,delta^((q^2-1))=1);
    fi;
    Append(TILDER1,Tuple([delta,delta^U])=1);
    Append(TILDER1,delta^z=delta^-1);
    Append(TILDER1,Tuple([delta^(q-1),U])=1);
  fi;
  Rels:=Concatenation(List(R1,r->LHS(r)*RHS(r)^-1),R);
  return rec(val1:=F,
    val2:=Rels);
end;

Minus_OrderN:=function(d,q)
local n;
  n:=QuoInt(d,2);
  if IsOddInt(q) then
    return (q+1)*(q-1)^(n-1)*2^(n-2)*Factorial(n-1);
  else
    return (q+1)*(q-1)^(n-1)*2^(n-1)*Factorial(n-1);
  fi;
end;

Setup_MinusPresentation:=function(d,q)
local F,OMIT,R,R1,R2,R3,R4,R5,Rels,S,U,V,W,delta,e,f,n,p,phi,sigma,tau,z;
  if d=6 then
    return Minus6Presentation(q);
  fi;
  F:=SLPGroup(6);
  z:=F.1;
  tau:=F.2;
  sigma:=F.3;
  delta:=F.4;
  U:=F.5;
  V:=F.6;
  # =v= MULTIASSIGN =v=
  e:=IsPrimePower(q);
  f:=e.val1;
  p:=e.val2;
  e:=e.val3;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  R:=Minus_PresentationForN(d,q);
  S:=R.val1;
  R:=R.val2;
  # =^= MULTIASSIGN =^=
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [delta,z,U,V]);
  R:=List(R,r->phi(r));
  n:=QuoInt(d,2);
  R1:=[];
  #   centraliser of sigma in N
  Append(TILDER1,Tuple([sigma,z^(V^2)])=1);
  Append(TILDER1,Tuple([sigma,delta^(V^2)])=1);
  OMIT:=true;
  if not OMIT then
    Append(TILDER1,Tuple([sigma,delta*delta^U])=1);
    Append(TILDER1,Tuple([sigma,z*z^U*U])=1);
  fi;
  if n > 4 then
    Append(TILDER1,Tuple([sigma,U^(V^2)])=1);
  fi;
  #   elements generate the same group but for odd q reflects direct product
  if n > 5 then
    if IsOddInt(q) then
      Append(TILDER1,Tuple([sigma,V*U^-1*(U^-1)^V])=1);
    else
      Append(TILDER1,Tuple([sigma,V*U*U^V])=1);
    fi;
  fi;
  R2:=[];
  #   centraliser of tau in N
  Append(TILDER2,Tuple([tau,U^V])=1);
  if n > 4 then
    Append(TILDER2,Tuple([tau,V*U^-1])=1);
  fi;
  if IsEvenInt(q) then
    Append(TILDER2,Tuple([tau,delta^(V^2)*(delta^-1)^(V)])=1);
  fi;
  # =v= MULTIASSIGN =v=
  R3:=Minus6Presentation(q);
  S:=R3.val1;
  R3:=R3.val2;
  # =^= MULTIASSIGN =^=
  phi:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [z,tau,sigma,delta,U]);
  R3:=List(R3,r->phi(r));
  R4:=[];
  Append(TILDER4,Tuple([sigma,sigma^V])=sigma^(V*U^-1));
  Append(TILDER4,Tuple([sigma,sigma^(V*U^-1)])=1);
  W:=U^(V*U^-1);
  Append(TILDER4,Tuple([sigma,sigma^W])=1);
  if n > 4 then
    Append(TILDER4,Tuple([sigma,sigma^(V^2)])=1);
  fi;
  R5:=[];
  Append(TILDER5,Tuple([sigma^V,tau])=1);
  Rels:=Concatenation(List(Concatenation(R1,R2,R4,R5),r->LHS(r)*RHS(r)^-1),R,R3)
   ;
  return rec(val1:=F,
    val2:=Rels);
end;

MinusPresentation:=function(d,q)
local P,Presentation,Projective,Q,R,Rels,S,n,z;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  Assert(1,d >= 4);
  Assert(1,IsEvenInt(d));
  n:=QuoInt(d,2);
  if d=4 then
    # =v= MULTIASSIGN =v=
    R:=ClassicalStandardPresentation("SL",2,q^2:Projective:=true);
    Q:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
    Q:=SLPGroup(5);
    if IsEvenInt(q) then
      R:=Evaluate(R,[Q.1^Q.2,Q.1^Q.2,Q.1,Q.3]);
      Append(TILDER,(Q.1*Q.1^Q.2*Q.1)*Q.2^-1);
    else
      R:=Evaluate(R,List([1,1,2,3],i->Q.i));
    fi;
    Append(TILDER,Q.4);
    Append(TILDER,Q.5);
    return rec(val1:=Q,
      val2:=R);
  fi;
  # =v= MULTIASSIGN =v=
  R:=Setup_MinusPresentation(d,q);
  P:=R.val1;
  R:=R.val2;
  # =^= MULTIASSIGN =^=
  if Projective and IsOddInt(n) and q mod 4=3 then
    z:=MinusGeneratorOfCentre(d,q,P);
    Append(TILDER,z);
  fi;
  if Presentation then
    return rec(val1:=P,
      val2:=R);
  fi;
  #   do conversion
  # =v= MULTIASSIGN =v=
  Rels:=MinusConvertToStandard(d,q,R);
  S:=Rels.val1;
  Rels:=Rels.val2;
  # =^= MULTIASSIGN =^=
  Rels:=Filtered(Rels,w->w<>w^0);
  return rec(val1:=S,
    val2:=Rels);
end;

#   relations are on presentation generators;
#  convert to relations on standard generators 
InstallGlobalFunction(MinusConvertToStandard,
function(d,q,Rels)
local A,B,C,Rels,T,U,W,tau;
  A:=MinusStandardToPresentation(d,q);
  Rels:=Evaluate(Rels,A);
  B:=MinusPresentationToStandard(d,q);
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
InstallGlobalFunction(MinusStandardToPresentation,
function(d,q)
local Delta,F,U,V,W,delta,m,p,s,sigma,t,tau,w,w0,x,z;
  Assert(1,IsEvenInt(d) and d > 4);
  W:=SLPGroup(5);
  if IsOddInt(q) then
    s:=W.1;
    t:=W.2;
  else
    t:=W.1;
    s:=W.2;
    #   correct discrepancy between published s and code s
    s:=s^t;
  fi;
  delta:=W.3;
  U:=W.4;
  V:=W.5;
  z:=s^V;
  # rewritten select statement
  if d mod 4=2 then
    tau:=(t^V)^-1;
  else
    tau:=(t^V);
  fi;
  if IsOddInt(q) then
    lvarDelta:=(delta^V)^(QuoInt((q^2-1),2)-q);
  else
    lvarDelta:=(delta^-1)^V;
  fi;
  p:=Characteristic(GF(q));
  if IsOddInt(p) then
    sigma:=Tuple([tau,tau^(z*U)])^(QuoInt((p-1),2));
  else
    F:=GF(q^2);
    w:=PrimitiveElement(F);
    w0:=w^(q+1);
    m:=Log(w0,w^2+w^(2*q));
    x:=Tuple([tau^delta,tau^U])^(z*U);
    sigma:=x^(lvarDelta^(q-m));
  fi;
  if d=6 then
    return [z,tau,sigma,lvarDelta,U,U];
  else
    return [z,tau,sigma,lvarDelta,U,V];
  fi;
end);

#   express standard generators as words in presentation generators 
InstallGlobalFunction(MinusPresentationToStandard,
function(d,q)
local Delta,U,V,W,delta,s,sigma,t,tau,z;
  Assert(1,IsEvenInt(d) and d > 4);
  W:=SLPGroup(6);
  z:=W.1;
  tau:=W.2;
  sigma:=W.3;
  lvarDelta:=W.4;
  U:=W.5;
  V:=W.6;
  # rewritten select statement
  if d mod 4=0 then
    t:=tau^(V^-1);
  else
    t:=(tau^-1)^(V^-1);
  fi;
  if IsOddInt(q) then
    delta:=(lvarDelta^(V^-1))^(QuoInt((q^2-1),2)-q);
  else
    delta:=(lvarDelta^-1)^(V^-1);
  fi;
  s:=z^(V^-1);
  if IsEvenInt(q) then
    #   correct discrepancy between published s and code s
    s:=s^(t^-1);
    return [t,s,delta,U,V];
  else
    return [s,t,delta,U,V];
  fi;
end);

#   generator of centre as word in presentation generators
InstallGlobalFunction(MinusGeneratorOfCentre,
function(d,q,F)
local V,delta,n,z;
  Assert(1,IsEvenInt(d) and d > 4);
  n:=QuoInt(d,2);
  if IsOddInt(n) and q mod 4=3 then
    delta:=F.4;
    if d=6 then
      V:=F.5;
    else
      V:=F.6;
    fi;
    z:=V^(n-1)*delta^(QuoInt((q^2-1),4));
  else
    z:=F.0;
  fi;
  return z;
end);


