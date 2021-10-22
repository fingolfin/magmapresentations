InstallOtherMethod(IsomorphismFpGroup,"classical simple",true,
  [IsGroup and IsFinite and IsSimpleGroup,IsString],100,
function(g,s)
local type,d,q,h,maz,hom,iso,fp,p;
  if ValueOption(NO_PRECOMPUTED_DATA_OPTION)=true then
    TryNextMethod();
  fi;
  d:=DataAboutSimpleGroup(g);
  if d.idSimple.series="L" then
    type:="SL";d:=d.idSimple.parameter;
    q:=d[2];d:=d[1];
  elif d.idSimple.series="S" then
    type:="Sp";d:=d.idSimple.parameter;
    q:=d[2];d:=d[1];
  elif d.idSimple.series="U" then
    type:="SU";d:=d.idSimple.parameter;
    q:=d[2];d:=d[1];
  elif d.idSimple.series="O+" then
    type:="Omega+";d:=d.idSimple.parameter;
    q:=d[2];d:=d[1];
  elif d.idSimple.series="O-" then
    type:="Omega-";d:=d.idSimple.parameter;
    q:=d[2];d:=d[1];
  elif d.idSimple.series="O" then
    type:="Omega";d:=d.idSimple.parameter;
    q:=d[2];d:=d[1];
  else
    TryNextMethod();
  fi;
  maz:=ClassicalStandardGenerators(type,d,q:PresentationGenerators:=true);
  fp:=ClassicalStandardPresentation(type,d,q:
    Projective:=true,PresentationGenerators:=true);
  h:=Group(maz);
  hom:=SparseActionHomomorphism(h,[One(h)[1]],OnLines);
  p:=List(maz,x->ImagesRepresentative(hom,x));
  h:=Group(p);
  IsSimpleGroup(h);
  Print("build classical group\n");
  iso:=IsomorphismGroups(h,g);
  SetSize(fp,Size(g));
  iso:=GroupHomomorphismByImages(fp,g,GeneratorsOfGroup(fp),
    List(p,x->ImagesRepresentative(iso,x)));
  hom:=InverseGeneralMapping(iso);
  SetIsBijective(hom,true);
  return hom;
end);
