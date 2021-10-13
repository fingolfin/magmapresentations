
SUElements:=function()
local Q,R,S,d,q;
  for d in [3..dim_limit] do
    for q in [2..field_limit] do
      if Size(DuplicateFreeList(Factors(p))) > 1 then
        Print(d," ",q,"\n");
        R:=ClassicalStandardPresentation("SU",d,q:PresentationGenerators:=false)
         ;
        Q:=FreeGroupOfFpGroup(R);
         R := RelatorsOfFpGroup(R);
        S:=ClassicalStandardGenerators("SU",d,q);
        # was "Assert(1,Size(Set(Evaluate(R,S)))=1);"
        Assert(1,Size(Set(List(R, w-> MappedWord(w, GeneratorsOfGroup(Q), S))))=1);
      fi;
    od;
  od;
  return true;
end;

TestSUEven:=function(list_a,list_b)
local Delta,F,I,K,Presentation,Projective,U,V,varZ,d,delta,n,q,sigma,tau;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  for d in list_a do
    Assert(1,IsEvenInt(d));
    n:=QuoInt(d,2);
    for q in list_b do
      F:=ClassicalStandardPresentation("SU",d,q:Projective:=Projective,
       PresentationGenerators:=Presentation);
      varZ:=F.1;
      V:=F.2;
      tau:=F.3;
      delta:=F.4;
      U:=F.5;
      sigma:=F.6;
      lvarDelta:=F.7;
      if d=4 then
        #   K := sub < F | [Z, V, U, delta, sigma, tau]>;
        #   maximal x^a y^b L(2, q^2)
        ## TODO SubStructure
        K:=SubStructure(F,V,#TODO CLOSURE
          tau,delta,sigma,lvarDelta);
      else
        if Presentation then
          if d=6 then
              ## TODO SubStructure
            K:=SubStructure(F,[varZ,U,lvarDelta^(V^-2),sigma^(V^(n-2)),sigma]);
          else
              ## TODO SubStructure
            K:=SubStructure(F,[varZ,U,U^(V^-2)*V,lvarDelta,lvarDelta^(V^-2)
             ,delta,tau,sigma^(V^(n-2)),sigma]);
          fi;
        else
            ## TODO SubStructure
          K:=SubStructure(F,[varZ,U,U^(V^-2)
           *V,lvarDelta,delta,tau,sigma^(V^(n-2)),sigma]);
        fi;
      fi;
      ## TODO Lots of things to fix here
      I:=CosetImage(F,K);
      if Degree(I) < 10^7 then
        RandomSchreier(I);
        CompositionFactors(I);
        #  USECODE:assert #SU(d, q) mod #I eq 0; #SU(d, q) div #I in {1..Gcd
        #  (d, q + 1)};
      fi;
    od;
  od;
  return true;
end;

TestSUOdd:=function(list_a,list_b)
local
   Delta,F,Gamma,I,K,Presentation,Projective,Q,R,U,V,varX,varZ,d,n,phi,q,sigma,
   t,tau,v,words;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  for d in list_a do
    Assert(1,IsOddInt(d));
    n:=QuoInt(d,2);
    for q in list_b do
      if d=3 then
        R:=ClassicalStandardPresentation("SU",d,q:Projective:=Projective,
         PresentationGenerators:=true);
        Q:=R.FreeGroupOfFpGroup(R);
        R:=RelatorsOfFpGroup(R);
      else
        R:=ClassicalStandardPresentation("SU",d,q:Projective:=Projective,
         PresentationGenerators:=Presentation);
        Q:=R.FreeGroupOfFpGroup(R);
        R:=RelatorsOfFpGroup(R);
      fi;
      F:=Q/R;
      if d > 3 then
        varX:=List([1..Size(GeneratorsOfGroup(F))],i->F.i);
        if not Presentation then
          words:=SUStandardToPresentation(d,q);
          varX:=Evaluate(words,List([1..Size(GeneratorsOfGroup(Q))],i->Q.i));
          phi:=GroupHomomorphismByImages(Q,F,
            GeneratorsOfGroup(Q),List([1..7],i->F.i));
          varX:=List(varX,x->ImagesRepresentative(phi,x));
        fi;
        lvarGamma:=varX[1];
        t:=varX[2];
        U:=varX[3];
        V:=varX[4];
        sigma:=varX[5];
        tau:=varX[6];
        v:=varX[7];
        if IsEvenInt(q) then
          varZ:=t;
        else
          varZ:=(lvarGamma^-1)^(QuoInt((q^2+q),2))*t;
        fi;
        lvarDelta:=lvarGamma*(lvarGamma^-1)^U;
      fi;
      if d=3 then
        #   index q^3 + 1
        #   standard? K := sub<F | F.3, F.6, F.7>;
        ## TODO SubStructure
        K:=SubStructure(F,F.1,#TODO CLOSURE
          F.3);
      elif d=5 then
        #   p^k * SU(d-2, q)
        ## TODO SubStructure
        K:=SubStructure(F,lvarGamma,#TODO CLOSURE
          V*(U^V^-1),List([lvarGamma,t,tau,v],x->x^U),sigma);
      else
        #   d >= 7
        #   SU(d-1, q)
        #   K := sub < F | [ Z, V, U, Delta, sigma, Gamma ]>;
        #   p^k * SU(d-2, q)
        ## TODO SubStructure
        K:=SubStructure(F,lvarGamma,#TODO CLOSURE
          V*U,U^V,List([lvarGamma,t,tau,v],x->x^U),sigma);
      fi;
      ## TODO Lots of things to change here
      I:=CosetImage(F,K);
      RandomSchreier(I);
      #   assert Degree (I) eq q^d - 1;
      CompositionFactors(I);
      #  USECODE:assert #SU(d, q) mod #I eq 0; #SU(d, q) div #I in {1..Gcd (d,
      #  q + 1)};
      #   assert #I eq #SU(d, q) or #I eq #SU(d, q) div 2;
    od;
  od;
  return true;
end;

TestSU:=function(list_a,list_b)
local Presentation,Projective,d,f,q;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  for d in list_a do
    for q in list_b do
      if IsEvenInt(d) then
        f:=TestSUEven([d],[q]:Presentation:=Presentation,Projective:=Projective)
         ;
      else
        f:=TestSUOdd([d],[q]:Presentation:=Presentation,Projective:=Projective)
         ;
      fi;
    od;
  od;
  return true;
end;

PlusElements:=function()
local varE,Q,R,d,q;
  for d in [4,4+2..dim_limit] do
    for q in [2..field_limit] do
      if Size(DuplicateFreeList(Factors(p))) > 1 then
        Print(d," ",q,"\n");
        R:=ClassicalStandardPresentation("Omega+",d,
         q:PresentationGenerators:=false);
        Q:=FreeGroupOfFpGroup(R);
        R:=RelatorsOfFpGroup(R);
        varE:=ClassicalStandardGenerators("Omega+",d,q);
        # was "Assert(1,Size(Set(Evaluate(R,varE)))=1);"
        Assert(1,Size(Set(List(R, w-> MappedWord(w, GeneratorsOfGroup(Q), varE))))=1);
      fi;
    od;
  od;
  return true;
end;

MinusElements:=function()
local varE,Q,R,d,q;
  for d in [4,4+2..dim_limit] do
    for q in [2..field_limit] do
      if Size(DuplicateFreeList(Factors(p))) > 1 then
        Print(d," ",q,"\n");
        R:=ClassicalStandardPresentation("Omega-",d,
         q:PresentationGenerators:=false);
        Q:=FreeGroupOfFpGroup(R);
        R:=RelatorsOfFpGroup(R);
        varE:=ClassicalStandardGenerators("Omega-",d,q);
        # was "Assert(1,Size(Set(Evaluate(R,varE)))=1);"
        Assert(1,Size(Set(List(R, w-> MappedWord(w, GeneratorsOfGroup(Q), varE))))=1);
      fi;
    od;
  od;
  return true;
end;

OmegaElements:=function()
local varE,Q,R,d,q;
  for d in [3,3+2..dim_limit] do
    for q in [3..field_limit] do
      if Size(DuplicateFreeList(Factors(p))) > 1 and IsOddInt(q) then
        Print(d," ",q,"\n");
        R:=ClassicalStandardPresentation("Omega",d,
         q:PresentationGenerators:=false);
        R:=RelatorsOfFpGroup(R);
        varE:=ClassicalStandardGenerators("Omega",d,q);
        Assert(1,Size(Set(Evaluate(R,varE)))=1);
      fi;
    od;
  od;
  return true;
end;
