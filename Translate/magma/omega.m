/////////////////////////////////////////////////////////////////////////
//   Short presentation for Omega^\epsilon(d, q)                       //
//                                                                     //
//   Input two parameters to compute this presentation of Omega(d, q)     //
//     d = dimension                                                   //
//     q = field order                                                 //
// 
//   November 2017
/////////////////////////////////////////////////////////////////////////

import "plus.m": PlusPresentation;
import "minus.m": MinusPresentation;
import "circle.m": OmegaPresentation;

intrinsic Internal_StandardPresentationForOmega (d :: RngIntElt, F :: FldFin: 
     Projective := false, Presentation := false, Type := "Omega+") -> GrpSLP, []
{return standard presentation for Omega(d, F)} 
  
   require d gt 2: "Degree must be at least 3";
   return Internal_StandardPresentationForOmega(d, #F : Projective := Projective, 
	Presentation := Presentation, Type := Type);
end intrinsic;
 
intrinsic Internal_StandardPresentationForOmega (d :: RngIntElt, q :: RngIntElt: 
     Projective := false, Presentation := false, Type := "Omega+") -> GrpSLP, []
{return standard presentation for Omega(d, q)} 
  
   require IsPrimePower (q): "Field size is not valid";

   if Type eq "Omega" then 
      require IsOdd (d) and d ge 3: "Degree must be odd and at least 3";
      require IsOdd (q): "Field size must be odd";
      return OmegaPresentation (d, q: Presentation := Presentation);
   elif Type eq "Omega+" then
      require IsEven (d) and d ge 4: "Degree must be even and at least 4";
      return PlusPresentation (d, q: Projective := Projective, Presentation := Presentation);
   elif Type eq "Omega-" then
      require IsEven (d) and d ge 4: "Degree must be even and at least 4";
      return MinusPresentation (d, q: Projective := Projective, Presentation := Presentation);
   else 
     error "Invalid input";
   end if;
end intrinsic;
