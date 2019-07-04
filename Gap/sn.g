#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: Append, FPGroup, FreeGroup, IsEven, IsOdd, LHS,
#  PresentationForSn, RHS, Relations, Rewrite, SLPGroup, Sym, tau

#  Defines: PresentationForAn, PresentationForSn

#   presentation for Sym (d) defined on (1, 2) and (1..n)
PresentationForSn:=function(d)
local F,Rels,S,U,V,i,tau;
  # note that SLP option does not make sense here
  F:=FreeGroup("U","V");
  U:=F.1; #   (1, 2)
  V:=F.2; #   (1,2, ..., d)
  Rels:=[];
  Add(Rels,U^2);
  if d=1 then
    Rels:=[U,V];
    return F/[U,
      V];
  elif d=2 then
    Rels:=[U/V,U^2];
    return F/Rels;
  else
    Add(Rels,V^d);
    Add(Rels,(U*V)^(d-1));
    Add(Rels,Comm(U,V)^3);
  fi;
  for i in [2..(QuoInt(d,2))] do
    Add(Rels,Comm(U,V^i)^2);
  od;
  return F/Rels;
end;

#PresentationForAn:=function(d)
#local A,Rels,S,T,W,tau;
#  S:=PresentationForSn(d:SLP:=false);
#  if IsEvenInt(d) then
#    W:=S.1*S.2;
#    T:=(S.2*S.2^S.1)^-1;
#  fi;
#  A:=SubStructure(S,W,#TODO CLOSURE
#    T);
#  Rewrite(S,TILDEA:Simplify:=false);
#  S:=SymmetricGroup(d);
#  W:=S.1*S.2;
#  T:=(S.2*S.2^S.1)^-1;
#  A:=SubStructure(S,W,#TODO CLOSURE
#    T);
#  A:=FPGroup(A);
#  Rels:=Relations(A);
#  S:=SLPGroup(2);
#  tau:=GroupHomomorphismByImages(A,S,
#    GeneratorsOfGroup(A),[S.1,S.2]);
#  Rels:=List(Rels,r->LHS(r)*RHS(r)^-1);
#  Rels:=List(Rels,r->tau(r));
#  return rec(val1:=S,
#    val2:=Rels);
#end;

#   presentation for Alt (n)
PresentationForAn:=function(n)
local F,a,b,A,Rels,S,tau;
  F:=FreeGroup("a","b");
  a:=F.1;b:=F.2;
  if IsOddInt(n) then
    #   n odd: a=(1,2,3), b=(1,2,...,n), 
    A:=F/Concatenation([a^3,b^n,(a*b^2)^(QuoInt((n-1),2))],
      List([2..n-2],j->((b*a)^j*b^-j)^2));
  else
    #   n even: a=(1,2,3), b=(2,...,n) 
    A:=F/Concatenation([a^3,b^(n-1),(b^2*a^-1)^(QuoInt(n,2)),(b*a^-1)^(n-1)],
     List([1..QuoInt(n,2)-1],j->((b^-1*a*b^-1)^j*(b^2*a^-1)^j)^2),
     List([1..QuoInt(n,2)-2],j->((b^-1*a*b^-1)^j*(a^-1*b^2)^j*a^-1)^2));
  fi;
  return A;
end;


