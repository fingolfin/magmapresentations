#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Append, Coefficients, Eltseq, FreeGroup, GF, GL,
#  Integers, IsEven, IsSquare, LHS, Log, MinimalPolynomial, Modified_CR,
#  PrimitiveElement, RHS, SL2_even, SL2_odd, SL2_special, SLPGroup

#  Defines: CR, Modified_CR, PresentationForSL2, SL2Generators, SL2_even,
#  SL2_odd, SL2_special, Zassenhaus

#  $Id:: sl2q.m 2340 2012-09-30 01:03:09Z eobr007                             
 $:
#   Campbell, Robertson, Williams J. Austral. Math. Soc. 1990
#   Campbell and Robertson, BLMS 1980
#   generators for SL(2, p^e) 
SL2Generators:=function(p,e)
local F,varZ,delta,tau,w;
  F:=GF(p,e);
  w:=PrimitiveElement(F);
  delta:=[w^-1,0,0,w^1]*FORCEOne(GL(2,F));
  tau:=[1,1,0,1]*FORCEOne(GL(2,F));
  varZ:=[0,1,-1,0]*FORCEOne(GL(2,F));
  if e=1 then
    return [tau,varZ];
  else
    return [delta,tau,varZ];
  fi;
end;

#   presentation for SL(2, p^e); p odd
#   Projective = true: return presentation for PSL
SL2_odd:=function(p,e)
local B,varE,I,K,Projective,Q,Rels,U,c,delta,f,i,m,q,tau,tau1,w;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  K:=GF(p,e);
  q:=p^e;
  w:=PrimitiveElement(K);
  I:=Integers();
  Q:=SLPGroup(3);
  # Implicit generator Assg from previous line.
  delta:=Q.1;
  tau:=Q.2;
  U:=Q.3;
  Rels:=[];
  varE:=SubStructure(K,w^2);
  c:=Eltseq(w*FORCEOne(varE)^1);
  c:=List(c,x->x*FORCEOne(I));
  tau1:=Product(List([0..e-1],i->(tau^(delta^(i)))^c[i+1]));
  Rels:=Concatenation(Rels,[tau^p=1,Comm(tau,tau1])=1,Tuple([tau1,tau^delta)
   =1,(tau1*U*delta)^3=1]);
  if Projective then
    Rels:=Concatenation(Rels,[(tau*U)^3=1,(U*delta)
     ^2=1,U^2=1,delta^(QuoInt((q-1),2))=1]);
  else
    Rels:=Concatenation(Rels,[(tau*U^-1)^3=U^2,(U*delta)
     ^2=U^2,U^4=1,delta^(QuoInt((q-1),2))=U^2]);
  fi;
  if IsSquare(1+w^1) then
    m:=Log(w^2,1+w^1);
    Add(Rels,tau^(delta^m)=tau*tau1);
    Add(Rels,tau1^(delta^m)=tau1*tau^delta);
  else
    m:=Log(w^2,(1+w^-1));
    Add(Rels,tau1^(delta^m)=tau*tau1);
    Add(Rels,tau^(delta^(m+1))=tau1*tau^delta);
  fi;
  f:=MinimalPolynomial(w^1,GF(p));
  c:=Coefficients(f);
  c:=List(c,x->x*FORCEOne(I));
  B:=[tau,tau1];
  for i in [2..e] do
    B[i+1]:=B[i-1]^delta;
  od;
  Add(Rels,Product(List([0..e],i->B[i+1]^c[i+1])));
  Rels:=List(Rels,r->LHS(r)*RHS(r)^-1);
  return rec(val1:=Q,
    val2:=Rels);
end;

#   special presentation for SL(2, p^e) when p^e mod 4 = 3
SL2_special:=function(p,e)
local B,varE,I,K,Projective,Q,Rels,U,c,delta,f,i,m,q,r,tau,tau1,w;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  K:=GF(p,e);
  q:=p^e;
  w:=PrimitiveElement(K);
  I:=Integers();
  if IsSquare(1+w^1) then
    m:=Log(w^2,1+w^1);
    r:=QuoInt((q+1),4);
  else
    m:=Log(w^2,(1+w^-1));
    r:=QuoInt((q-3),4);
  fi;
  Q:=SLPGroup(3);
  # Implicit generator Assg from previous line.
  delta:=Q.1;
  tau:=Q.2;
  U:=Q.3;
  Rels:=[Comm(tau,tau^(delta^(QuoInt((q+1),4))))=1,tau^(delta^m)
   =Comm(tau^-1,delta^r)];
  if Projective then
    Rels:=Concatenation(Rels,[(tau*U)^3=1,(U*delta)
     ^2=1,U^2=1,delta^(QuoInt((q-1),2))=tau^p]);
  else
    Rels:=Concatenation(Rels,[(tau*U^-1)^3=U^2,(U*delta)
     ^2=U^2,U^4=1,delta^(QuoInt((q-1),2))=tau^p*U^2]);
  fi;
  varE:=SubStructure(K,w^2);
  c:=Eltseq(w*FORCEOne(varE)^1);
  c:=List(c,x->x*FORCEOne(I));
  tau1:=Product(List([0..e-1],i->(tau^(delta^(i)))^c[i+1]));
  f:=MinimalPolynomial(w^1,GF(p));
  c:=Coefficients(f);
  c:=List(c,x->x*FORCEOne(I));
  B:=[tau,tau1];
  for i in [2..e] do
    B[i+1]:=B[i-1]^delta;
  od;
  Add(Rels,Product(List([0..e],i->B[i+1]^c[i+1])));
  Rels:=List(Rels,r->LHS(r)*RHS(r)^-1);
  return rec(val1:=Q,
    val2:=Rels);
end;

#   presentation for SL(2, 2^e) where e > 1 
SL2_even:=function(p,e)
local B,varE,F,I,Rels,U,c,delta,f,i,m,q,tau,u,w;
  Assert(1,p=2);
  q:=2^e;
  varE:=GF(2,e);
  w:=PrimitiveElement(varE);
  F:=SLPGroup(3);
  # Implicit generator Assg from previous line.
  delta:=F.1;
  tau:=F.2;
  U:=F.3;
  B:=[tau];
  for i in [1..e] do
    B[i+1]:=B[i]^delta;
  od;
  f:=MinimalPolynomial(w^2,GF(2));
  c:=Coefficients(f);
  I:=Integers();
  u:=List(c,x->x*FORCEOne(I));
  m:=Log(w^2,1+w^2);
  Rels:=[Product(List([0..e],i->B[i+1]^u[i+1])),(U*tau)^3,U^2,(U*delta)
   ^2,tau^2,(tau*delta)^(q-1),tau^(delta^m)*Comm(tau,delta)^-1];
  return rec(val1:=F,
    val2:=Rels);
end;

#   Zassenhaus presentation for SL (2, p) where p is not 17 
Zassenhaus:=function(p)
if p=2 then
    return SubGroup(s,t,[s^p=1,t^2,(s*t)^3]);
  elif p=3 then
    return SubGroup(s,t,[s^p=1,t^4,(t*s^-1*t^-1*s^-1*t*s^-1)]);
  elif p<>17 then
    return SubGroup(s,t,[s^p=(s*t)^3,Comm(t^2,s),t^4,(s^2*t*s^(QuoInt((p^2+1)
     ,2))*t)^3]);
  fi;
end;

#   Campbell Robertson presentation for SL(2, p)
CR:=function(p)
local F,G,k,x,y;
  if p=2 then
    return SubGroup(s,t,[s^2=1,t^2,(s*t)^3]);
  fi;
  k:=QuoInt(p,3);
  F:=FreeGroup(2);
  # Implicit generator Assg from previous line.
  y:=F.1;
  x:=F.2;
  G:=F/[x^2/((x*y)^3),
    (x*y^4*x*y^(QuoInt((p+1),2)))^2*y^p*x^(2*k)];
  return G;
end;

#   Campbell Robertson presentation for SL(2, p) modified for our generators 
Modified_CR:=function(p)
local F,Projective,Rels,a,b,k,r;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  F:=SLPGroup(2);
  # Implicit generator Assg from previous line.
  a:=F.1;
  b:=F.2;
  if p=2 then
    return rec(val1:=F,
      val2:=[a^2,b^2,(a*b)^3]);
  fi;
  r:=p mod 3;
  k:=QuoInt(p,3);
  if r=1 then
    Rels:=[b^-2*(b*(a*b^2))^3,(b*(a*b^2)^4*b*(a*b^2)^(QuoInt((p+1),2)))
     ^2*(a*b^2)^p*b^(2*k)];
  else
    Rels:=[b^2*(b^-1*a)^3,(b^-1*a^4*b^-1*a^(QuoInt((p+1),2)))^2*a^p*(b^-1)^(2*k)
     ];
  fi;
  if Projective then
    Rels:=Concatenation(Rels,[b^2]);
  fi;
  return rec(val1:=F,
    val2:=Rels);
end;

#   presentation for SL(2, p^e) 
PresentationForSL2:=function(p,e)
local Projective,Q,R;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  if e=1 then
    # =v= MULTIASSIGN =v=
    R:=Modified_CR(p:Projective:=Projective);
    Q:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  elif IsEvenInt(p) then
    # =v= MULTIASSIGN =v=
    R:=SL2_even(p,e);
    Q:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  elif p^e mod 4=3 then
    # =v= MULTIASSIGN =v=
    R:=SL2_special(p,e:Projective:=Projective);
    Q:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    R:=SL2_odd(p,e:Projective:=Projective);
    Q:=R.val1;
    R:=R.val2;
    # =^= MULTIASSIGN =^=
  fi;
  return rec(val1:=Q,
    val2:=R);
end;

#  
#  SetGlobalTCParameters (:Hard, CosetLimit := 10^8, Print := 10^6);
#  for p in [2,3,5,7,11,13,17,19,23,29,31] do
#  for e in [1..6] do
#  p, e;
#  Q, R := PresentationForSL2 (p, e);
#  // ToddCoxeter (Q, sub <Q |>:Hard:=true, Workspace:=10^8);
#  X := SL2Generators (p, e);
#  Y := Evaluate (R, X);
#  assert #Set (Y) eq 1;
#  F := SLPToFP (Q, R);
#  if e eq 1 then
#  I := CosetImage (F, sub<F| >);
#  else
#  I := CosetImage (F, sub<F| F.1, F.2>);
#  end if;
#  RandomSchreier (I);
#  CompositionFactors (I);
#  assert #I in {#SL(2, p^e), #PSL(2, p^e)};
#  end for;
#  end for;
#  


