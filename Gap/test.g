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
