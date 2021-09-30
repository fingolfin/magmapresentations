#   usually subgroups chosen for coset enumeration are maximal of smallest index ## TODO Don't know what this does

#SetGlobalTCParameters(:CosetLimit:=10^7,Hard:=true,Print:=10^6);
LoadPackage("ace");
TCENUM:=ACETCENUM;

dim_limit:=20;
#   max dimension
field_limit:=100;
#   max size of field
#   Presentation = false: presentation rewritten on standard generators
#   Presentation = true: presentation listed in paper
#   Projective = true: presentation for group modulo its centre
#   do matrices satisfy presentation?
#   coset enumerations
TestSL:=function(a_list,b_list)
local DD,F,I,K,Presentation,Projective,QQ,U,V,d,delta,e,f,p,q,tau,gens;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  if Projective then Print("Doing Projective\n");fi;
  if Presentation then Print("Doing Presentation\n");fi;
  for d in a_list do
    for q in b_list do
      DD:=d;
      QQ:=q;
      Print(" D = ",d,", q = ",q,"\n");
      if d=2 then
        F:=ClassicalStandardPresentation("SL",d,q:Projective:=Projective,
         PresentationGenerators:=false);
        gens:=ClassicalStandardGenerators("SL",d,q:Projective:=Projective,
         PresentationGenerators:=false);
      else
        F:=ClassicalStandardPresentation("SL",d,q:Projective:=Projective,
         PresentationGenerators:=Presentation);
        gens:=ClassicalStandardGenerators("SL",d,q:Projective:=Projective,
         PresentationGenerators:=Presentation);
      fi;

      # verify relators
      U:=FreeGeneratorsOfFpGroup(F);
      V:=List(RelatorsOfFpGroup(F),
        x->MappedWord(x,FreeGeneratorsOfFpGroup(F),gens));
      V:=Unique(Filtered(V,x->not IsOne(x)));
      if Length(V)>0 and (Projective=false or ForAny(V,x->x<>x^0*x[1][1])) then
        Error("Relators don't hold");
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
        K:=Subgroup(F,[tau,delta]);
      else
          ## TODO SubStructure
        #   max? subgroup containing SL(d - 1, q)
        K:=Subgroup(F,[U,tau,V*U^(V^-1),delta,delta^(V^-1),tau^(V^-1)]);
      fi;
      ## TODO Lots of this to change here
      I:=Range(FactorCosetAction(F,K:max:=10^7,Wo:=10^8,Hard:=true));
      if NrMovedPoints(I) < 10^7 then
        Size(I);
        if d=2 then
          Assert(1,NrMovedPoints(I)=q+1);
        else
          Assert(1,(q^d-1) mod NrMovedPoints(I)=0);
          #   else assert Degree (I) eq (q^d - 1);
        fi;
      fi;
      ## TODO Up to here
    od;
  od;
  return true;
end;

TestSp:=function(list_a,list_b)
local
   F,I,K,Presentation,Projective,Q,R,U,V,varX,varZ,d,delta,e,f,m,p,phi,q,sigma,
   tau,words,gens;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  if Projective then Print("Doing Projective\n");fi;
  if Presentation then Print("Doing Presentation\n");fi;
  for d in list_a do
    for q in list_b do
      Print(" D = ",d,", q = ",q,"\n");
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
      gens:=ClassicalStandardGenerators("Sp",d,q:Projective:=Projective,
       PresentationGenerators:=Presentation);
      Q:=FreeGroupOfFpGroup(R);
      R:=RelatorsOfFpGroup(R);
      F:=Q/R;

      # verify relators
      U:=FreeGeneratorsOfFpGroup(F);
      V:=List(RelatorsOfFpGroup(F),
        x->MappedWord(x,FreeGeneratorsOfFpGroup(F),gens));
      V:=Unique(Filtered(V,x->not IsOne(x)));
      if Length(V)>0 and (Projective=false or ForAny(V,x->x<>x^0*x[1][1])) then
        Error("Relators don't hold");
      fi;

      if Presentation then
        varZ:=F.1;
        V:=F.2;
        tau:=F.3;
        delta:=F.4;
        U:=F.5;
        sigma:=F.6;
      else
        words:=SpStandardToPresentation@(d,q);
        # was "varX:=Evaluate(words,List([1..Size(GeneratorsOfGroup(Q))],i->Q.i));"
        gens:=GeneratorsOfGroup(FamilyObj(words)!.wholeGroup);
        varX:=List(words,w->MappedWord(w, gens, GeneratorsOfGroup(Q)));
        phi:=GroupHomomorphismByImages(Q,F,
          GeneratorsOfGroup(Q),GeneratorsOfGroup(F));
        varX:=List(varX,x->ImagesRepresentative(phi,x));
        varZ:=varX[1];
        V:=varX[2];
        tau:=varX[3];
        delta:=varX[4];
        U:=varX[5];
        sigma:=varX[6];
      fi;
      if d=4 then
          # TODO SubStructure
        K:=SubgroupNC(F,[varZ,tau,delta,delta^(V),sigma]);
      else
          # TODO SubStructure
        m:=(QuoInt(d,2))-1;
        K:=SubgroupNC(F,
          [U,(V*U)^(V^-1),varZ,tau,delta,delta^(V^(m)),sigma,sigma^(V^(m))]);
      fi;
      ## TODO Lots of things to change here
      I:=Range(FactorCosetAction(F,K:max:=10^7,Wo:=10^8,Hard:=true));
      if NrMovedPoints(I) < 10^7 then
        Size(I);
        Assert(1,Size(I)=Size(SP(d,q)) or Size(I)=QuoInt(Size(SP(d,q)),2));
      fi;
    od;
  od;
  return true;
end;


TestPlusOdd:=function(list_a,list_b)
local lvarDelta,F,I,K,Presentation,Projective,Q,R,U,V,varX,varZ,d,phi,q,
  sigma,words,gens;

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
        K:=Subgroup(F,GeneratorsOfGroup(F){[1,3,5,6,7]});
      else
        if Presentation then
          lvarDelta:=F.1;
          sigma:=F.2;
          varZ:=F.3;
          U:=F.4;
          V:=F.5;
        else
          words:=PlusStandardToPresentation@(d,q);
          # was "varX:=Evaluate(words,List([1..Size(GeneratorsOfGroup(Q))],i->Q.i));"
          gens:=GeneratorsOfGroup(FamilyObj(words)!.wholeGroup);
          varX:=List(words,
            w-> MappedWord(w, gens, GeneratorsOfGroup(Q)));
          phi:=GroupHomomorphismByImages(Q,F,
            GeneratorsOfGroup(Q),GeneratorsOfGroup(F));
          varX:=List(varX,x->ImagesRepresentative(phi,x));
          lvarDelta:=varX[1];
          sigma:=varX[2];
          varZ:=varX[3];
          U:=varX[4];
          V:=varX[5];
        fi;
        K:=Subgroup(F, [U^V,varZ^V,sigma^V,lvarDelta^V,
          (sigma^(varZ^V))^V,V*U,sigma,lvarDelta]);
      fi;
      gens:=ClassicalStandardGenerators("Omega+",d,q:Projective:=Projective,
       PresentationGenerators:=Presentation);

      # verify relators
      U:=FreeGeneratorsOfFpGroup(F);
      V:=List(RelatorsOfFpGroup(F),
        x->MappedWord(x,FreeGeneratorsOfFpGroup(F),gens));
      V:=Unique(Filtered(V,x->not IsOne(x)));
      if Length(V)>0 and (Projective=false or ForAny(V,x->x<>x^0*x[1][1])) then
        Error("Relators don't hold");
      fi;

      I:=Range(FactorCosetAction(F,K:max:=10^7,Wo:=10^8,Hard:=true));
      Size(I);
    od;
  od;
  return true;
end;

TestPlusEven:=function(list_a,list_b)
local lvarDelta,F,I,K,Presentation,Q,R,U,V,varX,varZ,d,delta,phi,q,sigma,
  gens,words;
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
        K:=SubgroupNC(F,GeneratorsOfGroup(F){[1,3,5,6,7]});
      else
        if Presentation then
          delta:=F.1;
          sigma:=F.2;
          varZ:=F.3;
          U:=F.4;
          V:=F.5;
        else
          words:=PlusStandardToPresentation@(d,q);
          # was "varX:=Evaluate(words,List([1..Size(GeneratorsOfGroup(Q))],i->Q.i));"
          gens:=GeneratorsOfGroup(FamilyObj(words)!.wholeGroup);
          varX:=List(words,w-> MappedWord(w, gens, GeneratorsOfGroup(Q)));
          phi:=GroupHomomorphismByImages(Q,F,
            GeneratorsOfGroup(Q),GeneratorsOfGroup(F));
          varX:=List(varX,x->ImagesRepresentative(phi,x));
          delta:=varX[1];
          sigma:=varX[2];
          varZ:=varX[3];
          U:=varX[4];
          V:=varX[5];
        fi;
        lvarDelta:=delta*(delta^-1)^U;
        K:=Subgroup(F,[U^V,varZ^V,sigma^V,lvarDelta^V,
          (sigma^(varZ^V))^V,V*U,sigma,lvarDelta]);
      fi;
      gens:=ClassicalStandardGenerators("Omega+",d,q:
       PresentationGenerators:=Presentation);

      # verify relators
      U:=FreeGeneratorsOfFpGroup(F);
      V:=List(RelatorsOfFpGroup(F),
        x->MappedWord(x,FreeGeneratorsOfFpGroup(F),gens));
      V:=Unique(Filtered(V,x->not IsOne(x)));
      if Length(V)>0 then
        Error("Relators don't hold");
      fi;
      I:=Range(FactorCosetAction(F,K:max:=10^7,Wo:=10^8,Hard:=true));
      Size(I);

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
  if Projective then Print("Doing Projective\n");fi;
  if Presentation then Print("Doing Presentation\n");fi;
  for d in list_a do
    for q in list_b do
      Print(" D = ",d,", q = ",q,"\n");
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

TestMinus:=function(list_a,list_b)
local lvarDelta,F,I,K,Presentation,Projective,Q,R,U,V,varX,d,phi,q,
  gens,sigma,tau,words,z;
  Presentation:=ValueOption("Presentation");
  if Presentation=fail then
    Presentation:=true;
  fi;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  if Projective then Print("Doing Projective\n");fi;
  if Presentation then Print("Doing Presentation\n");fi;
  for d in list_a do
    Assert(1,IsEvenInt(d));
    for q in list_b do
      Print(" D = ",d,", q = ",q,"\n");
      R:=ClassicalStandardPresentation("Omega-",d, q:
        PresentationGenerators:=Presentation,Projective:=Projective);
      Q:=FreeGroupOfFpGroup(R);
      R:=RelatorsOfFpGroup(R);
      F:=Q/R;
      if d=4 then
        K:=SubgroupNC(F,GeneratorsOfGroup(F){[2..5]});
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
          words:=MinusStandardToPresentation@(d,q);
          # was "varX:=Evaluate(words,List([1..Size(GeneratorsOfGroup(Q))],i->Q.i));"
          gens:=GeneratorsOfGroup(FamilyObj(words)!.wholeGroup);
          varX:=List(words,w-> MappedWord(w, gens, GeneratorsOfGroup(Q)));
          phi:=GroupHomomorphismByImages(Q,F,
            GeneratorsOfGroup(Q),GeneratorsOfGroup(F));
          varX:=List(varX,x->ImagesRepresentative(phi,x));
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
          K:=SubgroupNC(F,[lvarDelta,sigma,tau,lvarDelta^U,V*U^-1]);
        else
          K:=SubgroupNC(F,[lvarDelta,sigma,tau,lvarDelta^U,
            z^U,tau^U,U^V,V*U^-1]);
        fi;
      fi;

      # verify relators
      U:=FreeGeneratorsOfFpGroup(F);
      V:=List(RelatorsOfFpGroup(F),
        x->MappedWord(x,FreeGeneratorsOfFpGroup(F),gens));
      V:=Unique(Filtered(V,x->not IsOne(x)));
      if Length(V)>0 then
        Error("Relators don't hold");
      fi;
      I:=Range(FactorCosetAction(F,K:max:=10^7,Wo:=10^8,Hard:=true));
      Size(I);
    od;
  od;
  return true;
end;

