#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.5, 11/5/18 by AH

#  Global Variables used: ClassicalStandardGenerators,
#  ClassicalStandardPresentation, CompositionFactors, CosetImage, Degree,
#  Evaluate, IsEven, IsOdd, IsPrimePower, Ngens, RandomSchreier, SLPToFP, Set,
#  SetGlobalTCParameters, Sp, TestPlusEven, TestPlusOdd, TestSUEven, TestSUOdd,
#  phi

#  Defines: MinusElements, OmegaElements, PlusElements, SLElements, SUElements,
#  SpElements, TestMinus, TestOmega, TestPlus, TestPlusEven, TestPlusOdd,
#  TestSL, TestSU, TestSUEven, TestSUOdd, TestSp, dim_limit, field_limit

#   usually subgroups chosen for coset enumeration are maximal of smallest index
## TODO Don't know what this does
SetGlobalTCParameters(:CosetLimit:=10^7,Hard:=true,Print:=10^6);
dim_limit:=20;
#   max dimension
field_limit:=100;
#   max size of field
#   Presentation = false: presentation rewritten on standard generators
#   Presentation = true: presentation listed in paper
#   Projective = true: presentation for group modulo its centre
#   do matrices satisfy presentation?
SLElements:=function()
local Q,R,S,d,q;
  for d in [2..dim_limit] do
    for q in [2..field_limit] do
      if Size(DuplicateFreeList(Factors(q))) > 1 then
        Print(d," ",q,"\n");
        R:=ClassicalStandardPresentation("SL",d,q:PresentationGenerators:=false)
         ;
        Q:=FreeGroupOfFpGroup(R);
        R:=RelatorsOfFpGroup(R);
        S:=ClassicalStandardGenerators("SL",d,q);
        # was "Assert(1,Size(Set(Evaluate(R,S)))=1);"
        Assert(1,Size(Set(List(R, w-> MappedWord(w, GeneratorsOfGroup(Q), S))))=1);
      fi;
    od;
  od;
  return true;
end;

#   coset enumerations
TestSL:=function(a_list,b_list)
local DD,F,I,K,Presentation,Projective,QQ,U,V,d,delta,e,f,p,q,tau;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  for d in a_list do
    for q in b_list do
      DD:=d;
      QQ:=q;
      Print("\n D = ",d,"q = ",q,"\n");
      if d=2 then
        F:=ClassicalStandardPresentation("SL",d,q:Projective:=Projective,
         PresentationGenerators:=false);
      else
        F:=ClassicalStandardPresentation("SL",d,q:Projective:=Projective,
         PresentationGenerators:=Presentation);
      fi;
      e := Factors(q);
      if Size(DuplicateFreeList(e)) > 1 then
          f := false;
      else
          f := true;
          p := e[1];
          e := Size(e);
      fi;
      U:=F.1;
      V:=F.2;
      tau:=F.3;
      delta:=F.4;
      if d=2 then
          ## TODO SubStructure
        K:=SubStructure(F,tau,#TODO CLOSURE
          delta);
      else
          ## TODO SubStructure
        #   max? subgroup containing SL(d - 1, q)
        K:=SubStructure(F,U,#TODO CLOSURE
          tau,V*U^(V^-1),delta,delta^(V^-1),tau^(V^-1));
      fi;
      ## TODO Lots of this to change here
      I:=CosetImage(F,SubStructure(F,K));
      if Degree(I) < 10^7 then
        RandomSchreier(I);
        CompositionFactors(I);
        if d=2 then
          Assert(1,Degree(I)=q+1);
        else
          Assert(1,(q^d-1) mod Degree(I)=0);
          #   else assert Degree (I) eq (q^d - 1);
        fi;
      fi;
      ## TODO Up to here
    od;
  od;
  return true;
end;

SpElements:=function()
local R,S,d,Q,q;
  for d in [4,4+2..dim_limit] do
    for q in [2..field_limit] do
      if Size(DuplicateFreeList(Factors(p))) > 1 then
        R:=ClassicalStandardPresentation("Sp",d,q:PresentationGenerators:=false)
         ;
        Q:=FreeGroupOfFpGroup(R);
        R:=RelatorsOfFpGroup(R);
        S:=ClassicalStandardGenerators("Sp",d,q);
        Print(d," ",q,"\n");
        # was "Assert(1,Size(Set(Evaluate(R,S)))=1);"
        Assert(1,Size(Set(List(R, w-> MappedWord(w, GeneratorsOfGroup(Q), S))))=1);
      fi;
    od;
  od;
  return true;
end;

#  don't know if this is really necessary
#  I need this function to get the list of letters of the words for MappedWord (see below)
WriteGenerators:=function(R)
local fam, F;
  fam:=FamilyObj(R[1]);
  F:=fam!.freeGroup;
  return GeneratorsOfGroup(F);
end;


TestSp:=function(list_a,list_b)
local
   F,I,K,Presentation,Projective,Q,R,U,V,varX,varZ,d,delta,e,f,m,p,phi,q,sigma,
   tau,words;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  for d in list_a do
    for q in list_b do
        e := Factors(q);
        if Size(DuplicateFreeList(e)) > 1 then
            f := false;
        else
            f := true;
            p := e[1];
            e := Size(e);
        fi;
      R:=ClassicalStandardPresentation("Sp",d,q:Projective:=Projective,
       PresentationGenerators:=Presentation);
      Q:=FreeGroupOfFpGroup(R);
      R:=RelatorsOfFpGroup(R);
      F:=Q/R;
      if Presentation then
        varZ:=F.1;
        V:=F.2;
        tau:=F.3;
        delta:=F.4;
        U:=F.5;
        sigma:=F.6;
      else
        words:=SpStandardToPresentation(d,q);
        # was "varX:=Evaluate(words,List([1..Size(GeneratorsOfGroup(Q))],i->Q.i));"
        varX:=List(words,w-> MappedWord(w, WriteGenerators(words), List([1..Size(GeneratorsOfGroup(Q))],i->Q.i)));
        phi:=GroupHomomorphismByImages(Q,F,
          GeneratorsOfGroup(Q),List([1..Size(GeneratorsOfGroup(F))],i->F.i));
        varX:=List(varX,x->Image(phi,x));
        varZ:=varX[1];
        V:=varX[2];
        tau:=varX[3];
        delta:=varX[4];
        U:=varX[5];
        sigma:=varX[6];
      fi;
      if d=4 then
          # TODO SubStructure
        K:=SubStructure(F,varZ,#TODO CLOSURE
          tau,delta,delta^(V),sigma);
      else
          # TODO SubStructure
        m:=(QuoInt(d,2))-1;
        K:=SubStructure(F,U,#TODO CLOSURE
          (V*U)^(V^-1),varZ,tau,delta,delta^(V^(m)),sigma,sigma^(V^(m)));
      fi;
      ## TODO Lots of things to change here
      I:=CosetImage(F,K);
      if Degree(I) < 10^7 then
        RandomSchreier(I);
        Assert(1,Size(I)=Size(SP(d,q)) or Size(I)=QuoInt(Size(SP(d,q)),2));
        CompositionFactors(I);
      fi;
    od;
  od;
  return true;
end;

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
          varX:=List(varX,x->Image(phi,x));
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

TestOmega:=function(list_a,list_b)
local
   Delta,F,I,K,Presentation,Projective,Q,R,U,V,varX,varZ,d,phi,q,sigma,tau,
   words;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  for d in list_a do
    Assert(1,IsOddInt(d));
    for q in list_b do
      Assert(1,IsOddInt(q));
      R:=ClassicalStandardPresentation("Omega",d,q:Projective:=Projective,
       PresentationGenerators:=Presentation);
      Q:=FreeGroupOfFpGroup(R);
     R:=RelatorsOfFpGroup(R);
      F:=Q/R;
      if d=3 then
          # TODO SubStructure
        K:=SubStructure(F,F.2,#TODO CLOSURE
          F.3);
      else
        if Presentation=false then
          words:=OmegaStandardToPresentation(d,q);
          # was "varX:=Evaluate(words,List([1..Size(GeneratorsOfGroup(Q))],i->Q.i));"
          varX:=List(words,w-> MappedWord(w, WriteGenerators(words), List([1..Size(GeneratorsOfGroup(Q))],i->Q.i)));
          phi:=GroupHomomorphismByImages(Q,F,
            GeneratorsOfGroup(Q),List([1..Size(GeneratorsOfGroup(F))],i->F.i));
          varX:=List(varX,x->Image(phi,x));
          lvarDelta:=varX[1];
          varZ:=varX[2];
          tau:=varX[3];
          sigma:=varX[4];
          U:=varX[5];
          V:=varX[6];
        else
          lvarDelta:=F.1;
          varZ:=F.2;
          tau:=F.3;
          sigma:=F.4;
          U:=F.5;
          V:=F.6;
        fi;
        #   SOPlus (d - 1, q).2
        # TODO SubStructure
        K:=SubStructure(F,lvarDelta,#TODO CLOSURE
          varZ,sigma,U,V);
      fi;
      # TODO Lots of things to change here
      I:=CosetImage(F,K);
      RandomSchreier(I);
      CompositionFactors(I);
    od;
  od;
  return true;
end;

TestMinus:=function(list_a,list_b)
local
   Delta,F,I,K,Presentation,Projective,Q,R,U,V,varX,d,phi,q,sigma,tau,words,z;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  for d in list_a do
    Assert(1,IsEvenInt(d));
    for q in list_b do
      R:=ClassicalStandardPresentation("Omega-",d,
       q:PresentationGenerators:=Presentation,Projective:=Projective);
      Q:=FreeGroupOfFpGroup(R);
     R:=RelatorsOfFpGroup(R);
      F:=Q/R;
      if d=4 then
          ## TODO SubStructure
        K:=SubStructure(F,List([2..5],i->F.i));
      else
        if Presentation then
          z:=F.1;
          sigma:=F.3;
          tau:=F.2;
          U:=F.5;
          lvarDelta:=F.4;
          if d=6 then
            V:=F.0;
          else
            V:=F.6;
          fi;
        else
          words:=MinusStandardToPresentation(d,q);
          # was "varX:=Evaluate(words,List([1..Size(GeneratorsOfGroup(Q))],i->Q.i));"
          varX:=List(words,w-> MappedWord(w, WriteGenerators(words), List([1..Size(GeneratorsOfGroup(Q))],i->Q.i)));
          phi:=GroupHomomorphismByImages(Q,F,
            GeneratorsOfGroup(Q),List([1..Size(GeneratorsOfGroup(F))],i->F.i));
          varX:=List(varX,x->Image(phi,x));
          z:=varX[1];
          sigma:=varX[3];
          tau:=varX[2];
          U:=varX[5];
          lvarDelta:=varX[4];
          if d=6 then
            V:=varX[1]^0;
          else
            V:=varX[6];
          fi;
        fi;
        if d=6 then
            ## TODO SubStructure
          K:=SubStructure(F,lvarDelta,#TODO CLOSURE
            sigma,tau,lvarDelta^U,V*U^-1);
        else
            ## TODO SubStructure
          K:=SubStructure(F,lvarDelta,#TODO CLOSURE
            sigma,tau,lvarDelta^U,z^U,tau^U,U^V,V*U^-1);
        fi;
      fi;
      # TODO Lots of things to change
      I:=CosetImage(F,K);
      RandomSchreier(I);
      CompositionFactors(I);
    od;
  od;
  return true;
end;

TestPlusOdd:=function(list_a,list_b)
local
   Delta,F,I,K,Presentation,Projective,Q,R,U,V,varX,varZ,d,phi,q,sigma,words;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  for d in list_a do
    Assert(1,IsEvenInt(d));
    for q in list_b do
      Assert(1,IsOddInt(q));
      R:=ClassicalStandardPresentation("Omega+",d,
       q:PresentationGenerators:=Presentation,Projective:=Projective);
      Q:=FreeGroupOfFpGroup(R);
      R:=RelatorsOfFpGroup(R);
      F:=Q/R;
      if d=4 then
          # TODO SubStructure
        K:=SubStructure(F,List([1,3,5,6,7],i->F.i));
      else
        if Presentation then
          lvarDelta:=F.1;
          sigma:=F.2;
          varZ:=F.3;
          U:=F.4;
          V:=F.5;
        else
          words:=PlusStandardToPresentation(d,q);
          # was "varX:=Evaluate(words,List([1..Size(GeneratorsOfGroup(Q))],i->Q.i));"
          varX:=List(words,w-> MappedWord(w, WriteGenerators(words), List([1..Size(GeneratorsOfGroup(Q))],i->Q.i)));
          phi:=GroupHomomorphismByImages(Q,F,
            GeneratorsOfGroup(Q),List([1..Size(GeneratorsOfGroup(F))],i->F.i));
          varX:=List(varX,x->Image(phi,x));
          lvarDelta:=varX[1];
          sigma:=varX[2];
          varZ:=varX[3];
          U:=varX[4];
          V:=varX[5];
        fi;
        # TODO SubStructure
        K:=SubStructure(F,U^V,#TODO CLOSURE
          varZ^V,sigma^V,lvarDelta^V,(sigma^(varZ^V))^V,V*U,sigma,lvarDelta);
      fi;
      #TODO Lots of things to change here
      I:=CosetImage(F,K);
      RandomSchreier(I);
      CompositionFactors(I);
    od;
  od;
  return true;
end;

TestPlusEven:=function(list_a,list_b)
local Delta,F,I,K,Presentation,Q,R,U,V,varX,varZ,d,delta,phi,q,sigma,words;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  for d in list_a do
    Assert(1,IsEvenInt(d));
    for q in list_b do
      Assert(1,IsEvenInt(q));
      R:=ClassicalStandardPresentation("Omega+",d,
       q:PresentationGenerators:=Presentation);
      Q:=FreeGroupOfFpGroup(R);
      R:=RelatorsOfFpGroup(R);
      F:=Q/R;
      if d=4 then
          # TODO SubStructure
        K:=SubStructure(F,List([1,3,5,6,7],i->F.i));
      else
        if Presentation then
          delta:=F.1;
          sigma:=F.2;
          varZ:=F.3;
          U:=F.4;
          V:=F.5;
        else
          words:=PlusStandardToPresentation(d,q);
          # was "varX:=Evaluate(words,List([1..Size(GeneratorsOfGroup(Q))],i->Q.i));"
          varX:=List(words,w-> MappedWord(w, WriteGenerators(words), List([1..Size(GeneratorsOfGroup(Q))],i->Q.i)));
          phi:=GroupHomomorphismByImages(Q,F,
            GeneratorsOfGroup(Q),List([1..Size(GeneratorsOfGroup(F))],i->F.i));
          varX:=List(varX,x->Image(phi,x));
          delta:=varX[1];
          sigma:=varX[2];
          varZ:=varX[3];
          U:=varX[4];
          V:=varX[5];
        fi;
        lvarDelta:=delta*(delta^-1)^U;
        #TODO SubStructure
        K:=SubStructure(F,U^V,#TODO CLOSURE
          varZ^V,sigma^V,lvarDelta^V,(sigma^(varZ^V))^V,V*U,sigma,lvarDelta);
      fi;
      # TODO Lots of things to change here
      I:=CosetImage(F,K);
      RandomSchreier(I);
      CompositionFactors(I);
    od;
  od;
  return true;
end;

TestPlus:=function(list_a,list_b)
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
      if IsEvenInt(q) then
        f:=TestPlusEven([d],[q]:Presentation:=Presentation);
      else
        f:=TestPlusOdd([d],[q]
         :Presentation:=Presentation,Projective:=Projective);
      fi;
    od;
  od;
  return true;
end;
