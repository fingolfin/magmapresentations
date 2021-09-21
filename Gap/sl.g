#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Append, Characteristic, ClassicalStandardGenerators,
#  Degree, Evaluate, Factorial, GF, Gcd, Integers,
#  Internal_StandardPresentationForSL, IsEven, IsOdd, IsPrime, 
#  LHS, MatrixAlgebra, Ngens, PresentationForN, PrimitiveElement, RHS,
#  SLConvertToStandard, SLGeneratorOfCentre, SLPGroup, SLPresentation,
#  SLPresentationToStandard, SLStandardToPresentation, Universe, Zero, phi, tau

#  Defines: Internal_StandardPresentationForSL, PresentationForN,
#  SLConvertToStandard, SLGeneratorOfCentre, SLGenerators, SLPresentation,
#  SLPresentationToStandard, SLStandardToPresentation, SL_Order_NSubgroup

DeclareGlobalFunction("SLConvertToStandard");

DeclareGlobalFunction("SLPresentationToStandard");

DeclareGlobalFunction("SLStandardToPresentation");

DeclareGlobalFunction("SLGeneratorOfCentre");

#  Forward declaration of SLConvertToStandard
#  Forward declaration of SLPresentationToStandard
#  Forward declaration of SLStandardToPresentation
#  Forward declaration of SLGeneratorOfCentre
SLGenerators:=function(d,q)
local MA,S,V,e,f,i,p;
  if d=2 then
    p:=PrimeBase(q);
    e:=LogInt(q,p);
    if q<>p^e then Error("<q> is not a prime power");fi;
    return SL2Generators(p,e);
  fi;
  S:=ClassicalStandardGenerators("SL",d,q);
  MA:=MatrixAlgebra(GF(q),d);
  V:=Zero(MA);
  for i in [1..d-1] do
    V[i][i+1]:=1;
  od;
  V[d][1]:=(-1)^(d-1);
  S[2]:=V;
  S[4]:=S[4]^-1;
  return S;
end;

#   presentation for extension of direct product of
#   d - 1 copies of Z_{q - 1} by a copy of Sym (d)
PresentationForN:=function(d,q)
local F,OMIT,R,Rels,S,U,V,delta,tau;
  F:=SLPGroup(3);
  U:=F.1;
  V:=F.2;
  delta:=F.3;
  if IsEvenInt(q) then
    # =v= MULTIASSIGN =v=
  Error("MULTI");
    R:=PresentationForSn(d);
    S:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    R:=SignedPermutations(d);
    S:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  fi;
  tau:=GroupHomomorphismByImages(S,F,
    GeneratorsOfGroup(S),
    [U,V]);
  R:=List(R,r->tau(r));
  Rels:=[];
  if d > 3 then
    Append(TILDERels,Tuple([delta,U^(V^2)])=1);
  fi;
  if d > 4 then
    Append(TILDERels,Tuple([delta,V*U*U^V])=1);
  fi;
  Append(TILDERels,delta*delta^V=delta^(V*U));
  Append(TILDERels,Tuple([delta,delta^V])=1);
  if d > 3 then
    Append(TILDERels,Tuple([delta,delta^(V^2)])=1);
  fi;
  OMIT:=true;
  if not OMIT then
    Append(TILDERels,delta^U=delta^-1);
    if IsEvenInt(q) then
      Append(TILDERels,delta^(q-1)=1);
    else
      Append(TILDERels,delta^(QuoInt((q-1),2))=U^2);
    fi;
  fi;
  Rels:=Concatenation(List(Rels,r->LHS(r)*RHS(r)^-1),R);
  return rec(val1:=F,
    val2:=Rels);
end;

SL_Order_NSubgroup:=function(d,q)
return (q-1)^(d-1)*Factorial(d);
end;

#   return presentation for SL(d, q)
SLPresentation:=function(d,q)
local F,I,R1,R2,Rels,S,U,V,a,b,delta,e,f,p,phi,tau,w,wm1;
  Assert(1,d > 2);
  p:=PrimeBase(q);
  e:=LogInt(q,p);
  if q<>p^e then Error("<q> is not a prime power");fi;
  F:=SLPGroup(4);
  U:=F.1;
  V:=F.2;
  tau:=F.3;
  delta:=F.4;
  Rels:=[];
  #   we don't need delta if e = 1 but it makes presentation consistent for all
  #  q
  if e=1 then
    w:=PrimitiveElement(GF(p));
    I:=Integers();
    a:=(w-w^2)*FORCEOne(I);
    b:=(w-1)*FORCEOne(I);
    wm1:=(w^-1)*FORCEOne(I);
    Append(TILDERels,delta=(tau^a)^U*tau^(wm1)*(tau^b)^U*tau^-1);
  fi;
  if IsPrimeInt(q) then
    if q=2 then
      # =v= MULTIASSIGN =v=
  Error("MULTI");
      R1:=PresentationForSn(d);
      S:=R1.val1;
      R1:=R1.val2;
      # =^= MULTIASSIGN =^=
    else
      # =v= MULTIASSIGN =v=
      R1:=SignedPermutations(d);
      S:=R1.val1;
      R1:=R1.val2;
      # =^= MULTIASSIGN =^=
    fi;
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [U,V]);
  else
    # =v= MULTIASSIGN =v=
    R1:=PresentationForN(d,q);
    S:=R1.val1;
    R1:=R1.val2;
    # =^= MULTIASSIGN =^=
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [U,V,delta]);
  fi;
  R1:=List(R1,r->phi(r));
  # =v= MULTIASSIGN =v=
  Error("MULTI");
  R2:=PresentationForSL2@(p,e);
  S:=R2.val1;
  R2:=R2.val2;
  # =^= MULTIASSIGN =^=
  if e=1 then
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [tau,U]);
  else
    phi:=GroupHomomorphismByImages(S,F,
      GeneratorsOfGroup(S),
      [delta,tau,U]);
  fi;
  R2:=List(R2,r->phi(r));
  #   centraliser of tau
  if d > 3 then
    Append(TILDERels,Tuple([tau,U^(V^2)])=1);
  fi;
  if d > 4 then
    if e > 1 then
      Append(TILDERels,Tuple([tau,V*U*U^V])=1);
    else
      Append(TILDERels,Tuple([tau,V*U^-1*(U^-1)^V])=1);
    fi;
  fi;
  if e > 1 then
    Append(TILDERels,Tuple([tau,delta*(delta^2)^V])=1);
    if d > 3 then
      Append(TILDERels,Tuple([tau,delta^(V^2)])=1);
    fi;
  fi;
  #   Steinberg relations
  Append(TILDERels,Tuple([tau,tau^V])=tau^(U^V));
  Append(TILDERels,Tuple([tau,tau^(U^V)])=1);
  Append(TILDERels,Tuple([tau,tau^(U*V)])=1);
  if d > 3 then
    Append(TILDERels,Tuple([tau,tau^(V^2)])=1);
  fi;
  #   one additional relation needed for this special case
  if d=3 and q=4 then
    Append(TILDERels,Tuple([tau,tau^(delta*V)])=tau^(delta*U^V));
    #   Append (~Rels, (tau, tau^(delta * U^V)) = 1);
    #   Append (~Rels, (tau, tau^(delta * U * V)) = 1);
  fi;
  Rels:=Concatenation(List(Rels,r->LHS(r)*RHS(r)^-1),R1,R2);
  return rec(val1:=F,
    val2:=Rels);
end;

#  ///////////////////////////////////////////////////////////////////////
#     Short presentation for SL(d, q)                                   //
#                                                                       //
#     Input two parameters to compute this presentation of SL(d, q)     //
#       d = dimension                                                   //
#       q = field order                                                 //

#     November 2017
#  ///////////////////////////////////////////////////////////////////////
Internal_StandardPresentationForSL:=function(d,q)
#  -> ,GrpSLP ,[ ,]  return standard presentation for SL ( d , q ) ; if
#  projective , then return standard presentation for PSL ( d , q )
local Presentation,Projective;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  if not d > 1 then
    Error("Degree must be at least 2");
  fi;
  if not IsPrimePowerInt(q) then
    Error("Field size is not valid");
  fi;
  return Internal_StandardPresentationForSL(d,GF(q)
   :Presentation:=Presentation,Projective:=Projective);
end;

Internal_StandardPresentationForSL:=function(d,K)
#  -> ,GrpSLP ,[ ,]  return standard presentation for SL ( d , K ) ; if
#  projective , then return standard presentation for PSL ( d , K )
local P,Presentation,Projective,R,Rels,S,e,p,q,z;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  if not d > 1 then
    Error("Degree must be at least 2");
  fi;
  q:=Size(K);
  p:=Characteristic(K);
  e:=Degree(K);
  if d=2 then
    # =v= MULTIASSIGN =v=
  Error("MULTI");
    R:=PresentationForSL2@(p,e:Projective:=Projective);
    P:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    R:=SLPresentation(d,q);
    P:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
    if Projective and Gcd(d,q-1) > 1 then
      z:=SLGeneratorOfCentre(d,q,P);
      R:=Concatenation(R,[z]);
    fi;
  fi;
  if Presentation then
    return rec(val1:=P,
      val2:=R);
  fi;
  # =v= MULTIASSIGN =v=
  Rels:=SLConvertToStandard(d,q,R);
  S:=Rels.val1;
  Rels:=Rels.val2;
  # =^= MULTIASSIGN =^=
  Rels:=Filtered(Rels,w->w<>w^0);
  return rec(val1:=S,
    val2:=Rels);
end;

#  don't know if this is really necessary
#  I need this function to get the list of letters of the words for MappedWord (see below)
WriteGenerators:=function(R)
local fam, F;
  fam:=FamilyObj(R[1]);
  F:=fam!.freeGroup;
  return GeneratorsOfGroup(F);
end;


#   relations are on presentation generators;
#  convert to relations on 4 standard generators 
InstallGlobalFunction(SLConvertToStandard,
function(d,q,Rels)
local A,B,C,Rels,T,U,W,tau;
  A:=SLStandardToPresentation(d,q);
  # was "Rels:=Evaluate(Rels,A);"
  Rels:=List(Rels, w -> MappedWord(w, WriteGenerators(Rels), A));
  B:=SLPresentationToStandard(d,q);
  # was "C:=Evaluate(B,A);"
  C:=List(B, w -> MappedWord(w, WriteGenerators(B), A));
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
InstallGlobalFunction(SLStandardToPresentation,
function(d,q)
local P,S,U,V,V_p,delta,tau;
  S:=SLPGroup(4);
  if d=2 then
    if IsPrimeInt(q) then
      P:=[S.3,S.2,S.0,S.0];
    else
      P:=[S.4^-1,S.3,S.2,S.0];
    fi;
    return P;
  fi;
  U:=S.1;
  V:=S.2;
  tau:=S.3;
  delta:=S.4;
  if IsOddInt(d) and IsOddInt(q) then
    V_p:=V^-1*(U^-1*V)^(d-1);
  else
    V_p:=V^(d-1);
  fi;
  return [U,V_p,tau,delta^-1];
end);

#   express standard generators as words in presentation generators 
InstallGlobalFunction(SLPresentationToStandard,
function(d,q)
local I,P,S,U,V,V_s,delta,tau,w,x,y;
  if d=2 then
    if IsPrimeInt(q) then
      P:=SLPGroup(2);
      w:=PrimitiveElement(GF(q));
      I:=Integers();
      x:=(w^-1)*FORCEOne(I)-1;
      y:=(w^-2-w^-1)*FORCEOne(I);
      U:=P.2;
      tau:=P.1;
      delta:=(tau^-1*(tau^x)^U*tau^(w*FORCEOne(I))*(tau^-y)^U)^-1;
      S:=[P.2,P.2,P.1,delta];
    else
      P:=SLPGroup(3);
      S:=[P.3,P.3,P.2,P.1^-1];
    fi;
    return S;
  fi;
  P:=SLPGroup(4);
  U:=P.1;
  V:=P.2;
  tau:=P.3;
  delta:=P.4;
  if IsOddInt(d) and IsOddInt(q) then
    V_s:=(V*U^-1)^(d-1)*V^-1;
  else
    V_s:=V^(d-1);
  fi;
  return [U,V_s,tau,delta^-1];
end);

#   construct generator of centre as SLP in presentation generators
InstallGlobalFunction(SLGeneratorOfCentre,
function(d,q,W)
local U,V,delta,m,z;
  Assert(1,d > 2);
  m:=QuoInt((d-1)*(q-1),Gcd(d,q-1));
  U:=W.1;
  V:=W.2;
  delta:=W.4;
  z:=(delta*U*V^-1)^m;
  return z;
end);


