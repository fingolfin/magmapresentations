#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Evaluate, Gcd, IsEven, IsOdd, IsPrimePower, Ngens,
#  SLPGroup, SUConvertToStandard, SUGeneratorOfCentre,
#  SUPresentationToStandard, SUStandardToPresentation,
#  StandardPresentationForSU, Universe, Valuation, tau

#  Defines: SUConvertToStandard, SUGeneratorOfCentre, SUGenerators,
#  SUPresentationToStandard, SUStandardToPresentation, 
 StandardPresentationForSU

DeclareGlobalFunction("SUConvertToStandard");

DeclareGlobalFunction("SUStandardToPresentation");

DeclareGlobalFunction("SUPresentationToStandard");

DeclareGlobalFunction("SUGeneratorOfCentre");

#  ///////////////////////////////////////////////////////////////////////
#     standard presentation for SU(n, q)                                //
#                                                                       //
#     Input two parameters to compute this presentation of SU(n, q)     //
#       n = dimension                                                   //
#       q = field order                                                 //
#                                                                       //
#     July 2018                                                         //
#  ///////////////////////////////////////////////////////////////////////
#  Forward declaration of SUConvertToStandard
#  Forward declaration of SUStandardToPresentation
#  Forward declaration of SUPresentationToStandard
#  Forward declaration of SUGeneratorOfCentre
SUGenerators:=function(d,q)
if d=3 then
    return SU3Generators(q);
  elif IsOddInt(d) then
    return OddSUGenerators(d,q);
  else
    return EvenSUGenerators(d,q);
  fi;
end;

StandardPresentationForSU:=function(d,F)
#  -> ,GrpSLP ,[ ,]  return standard presentation for SU ( d , F ) ; if
#  Projective := true , then return presentation for PSU ( d , F )
local Presentation,Projective;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  if not d > 2 then
    Error("Degree must be at least 3");
  fi;
  return StandardPresentationForSU(d,Size(F)
   :Projective:=Projective,Presentation:=Presentation);
end;

StandardPresentationForSU:=function(d,q)
#  -> ,GrpSLP ,[ ,]  return standard presentation for SU ( d , q ) ; if
#  Projective := true , then return presentation for PSU ( d , q )
local P,Presentation,Projective,R,Rels,S,z;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=false;
  fi;
  if not d > 2 then
    Error("Degree must be at least 3");
  fi;
  if not IsPrimePower(q) then
    Error("Field size is not valid");
  fi;
  if d=3 and q=2 then
    return SU32Presentation(:Projective:=Projective);
  elif IsOddInt(d) then
    # =v= MULTIASSIGN =v=
    R:=OddSUPresentation(d,q);
    P:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    R:=EvenSUPresentation(d,q);
    P:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  fi;
  if Projective and Gcd(d,q+1) > 1 then
    z:=SUGeneratorOfCentre(d,q,P);
    R:=Concatenation(R,[z]);
  fi;
  if Presentation then
    return rec(val1:=P,
      val2:=R);
  fi;
  # =v= MULTIASSIGN =v=
  Rels:=SUConvertToStandard(d,q,R);
  S:=Rels.val1;
  Rels:=Rels.val2;
  # =^= MULTIASSIGN =^=
  Rels:=Filtered(Rels,w->w<>w^0);
  return rec(val1:=S,
    val2:=Rels);
end;

#   relations are on presentation generators;
#  convert to relations on standard generators 
InstallGlobalFunction(SUConvertToStandard,
function(d,q,Rels)
local A,B,C,Rels,T,U,W,tau;
  if d=3 and q=2 then
    return rec(val1:=Universe(Rels),
      val2:=Rels);
  fi;
  A:=SUStandardToPresentation(d,q);
  Rels:=Evaluate(Rels,A);
  B:=SUPresentationToStandard(d,q);
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

#   return presentation generators as words in standard generators
InstallGlobalFunction(SUStandardToPresentation,
function(d,q)
local Delta,Gamma,P,S,U,V,W,varZ,delta,rest,s,sigma,t,tau,v,x,y;
  W:=SLPGroup(7);
  S:=List([1..7],i->W.i);
  if IsEvenInt(d) then
    varZ:=S[1];
    varZ:=varZ^-1;
    V:=S[2];
    tau:=S[3];
    tau:=tau^-1;
    delta:=S[4];
    delta:=delta^-1;
    U:=S[5];
    sigma:=S[6];
    sigma:=sigma^(V^2);
    lvarDelta:=S[7]^(V^2);
    lvarDelta:=lvarDelta^-1;
    P:=[varZ,V,tau,delta,U,sigma,lvarDelta];
  else
    if d=3 then
      rest:=List([1..3],i->W.0);
      #   sequence [v, tau, Delta, t]
      if IsOddInt(q) then
        return Concatenation([S[6],S[3],S[7],(S[7]^-1)^(QuoInt((q+1),2))*S[1]]
         ,rest);
      else
        return Concatenation([S[6],S[3],S[7],S[1]],rest);
      fi;
    fi;
    y:=S[7];
    V:=S[2];
    U:=S[5];
    tau:=S[3];
    x:=S[6];
    s:=S[1];
    lvarGamma:=(y^V)^-1;
    v:=x^V;
    # rewritten select statement
    if IsEvenInt(q) then
      t:=s;
    else
      t:=lvarGamma^(QuoInt((q^2+q),2))*s^-1;
    fi;
    sigma:=Tuple([v^(t*U),v^t])^t;
    #   return [Gamma, t, U, V, sigma, tau, v]
    P:=[lvarGamma,t,U,V,sigma,tau^-1,x^V];
  fi;
  return P;
end);

#   return standard generators as sequence [s, V, t, delta, U, x, y]
InstallGlobalFunction(SUPresentationToStandard,
function(d,q)
local Delta,Gamma,P,S,U,V,W,varZ,delta,sigma,t,tau,v;
  if d=3 then
    W:=SLPGroup(4);
    P:=List([1..4],i->W.i);
    if IsOddInt(q) then
      return [P[3]^(QuoInt((q+1),2))*P[4],P[1]^0,P[2],P[3]^(q+1),P[1]^0,P[1]
       ,P[3]];
    else
      return [P[4],P[4]^0,P[2],P[3]^(q+1),P[3]^0,P[1],P[3]];
    fi;
  fi;
  W:=SLPGroup(7);
  P:=List([1..7],i->W.i);
  if IsEvenInt(d) then
    varZ:=P[1];
    varZ:=varZ^-1;
    V:=P[2];
    tau:=P[3];
    tau:=tau^-1;
    delta:=P[4];
    delta:=delta^-1;
    U:=P[5];
    sigma:=P[6];
    sigma:=sigma^(V^-2);
    lvarDelta:=P[7]^(V^-2);
    lvarDelta:=lvarDelta^-1;
    S:=[varZ,V,tau,delta,U,sigma,lvarDelta];
  else
    lvarGamma:=P[1];
    t:=P[2];
    U:=P[3];
    V:=P[4];
    sigma:=P[5];
    tau:=P[6];
    v:=P[7];
    # rewritten select statement
    if IsEvenInt(q) then
      varZ:=t;
    else
      varZ:=(lvarGamma^-1)^(QuoInt((q^2+q),2))*t;
    fi;
    S:=[varZ^-1,V,tau^-1,lvarGamma^-(q+1),U,v^(V^-1),(lvarGamma^-1)^(V^-1)];
  fi;
  return S;
end);

#   construct generator of centre of SU(d, q) as SLP in presentation generators
InstallGlobalFunction(SUGeneratorOfCentre,
function(d,q,F)
local Delta,Gamma,U,V,varZ,a,b,n,t,z;
  if Gcd(d,q+1)=1 then
    return F.0;
  fi;
  n:=QuoInt(d,2);
  if IsOddInt(d) then
    if d=3 then
      z:=F.3^(QuoInt((q^2-1),3));
      return z;
    fi;
    lvarGamma:=F.1;
    t:=F.2;
    V:=F.4;
    # rewritten select statement
    if IsEvenInt(q) then
      varZ:=t;
    else
      varZ:=t*lvarGamma^(QuoInt((q+1),2));
    fi;
    z:=(lvarGamma*varZ*V)^(QuoInt(2*n*(q+1),Gcd(q+1,2*n+1)));
  else
    varZ:=F.1;
    U:=F.5;
    V:=F.2;
    lvarDelta:=F.7;
    a:=Valuation(q+1,2);
    b:=Valuation(n,2);
    if a > b then
      z:=varZ^2*(lvarDelta^(q-1)*U*V^-1)^(QuoInt((n-1)*(q+1),(2*Gcd(q+1,n))));
    else
      z:=(lvarDelta^(q-1)*U*V^-1)^(QuoInt((n-1)*(q+1),Gcd(q+1,n)));
    fi;
  fi;
  return z;
end);


