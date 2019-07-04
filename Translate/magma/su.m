/////////////////////////////////////////////////////////////////////////
//   standard presentation for SU(n, q)                                //
//                                                                     //
//   Input two parameters to compute this presentation of SU(n, q)     //
//     n = dimension                                                   //
//     q = field order                                                 //
//                                                                     //
//   July 2018                                                         //
/////////////////////////////////////////////////////////////////////////

import "even-su.m": EvenSUPresentation, EvenSUGenerators;
import "odd-su.m": OddSUPresentation, OddSUGenerators;
import "su3.m": SU32Presentation, SU3Generators;

forward SUConvertToStandard, SUStandardToPresentation, SUPresentationToStandard, 
 SUGeneratorOfCentre ;

SUGenerators := function (d, q)
   if d eq 3 then return SU3Generators (q); 
   elif IsOdd (d) then return OddSUGenerators (d, q);
   else return EvenSUGenerators (d, q);
   end if;
end function;
 
intrinsic Internal_StandardPresentationForSU (d:: RngIntElt, F :: FldFin: 
      Projective := false, Presentation := false) -> GrpSLP, [] 
{return standard presentation for SU (d, F); if Projective is true, 
 then return presentation for PSU (d, F)}

   require d gt 2: "Degree must be at least 3"; 
   return Internal_StandardPresentationForSU(d, #F : Projective := Projective, Presentation := Presentation);
end intrinsic;

intrinsic Internal_StandardPresentationForSU (d:: RngIntElt, q :: RngIntElt: 
      Projective := false, Presentation := false) -> GrpSLP, [] 
{return standard presentation for SU (d, q); if Projective is true, 
 then return presentation for PSU (d, q)}
  
   require d gt 2: "Degree must be at least 3"; 
   require IsPrimePower (q): "Field size is not valid";

   if d eq 3 and q eq 2 then 
      return SU32Presentation (: Projective := Projective);
   elif IsOdd (d) then
      P, R := OddSUPresentation (d, q);
   else
      P, R := EvenSUPresentation (d, q);
   end if;

   if Projective and Gcd (d, q + 1) gt 1 then 
      z := SUGeneratorOfCentre (d, q, P);
      R cat:= [z];
   end if;

   if Presentation then return P, R; end if;

   S, Rels := SUConvertToStandard (d, q, R);
   Rels := [w : w in Rels | w ne w^0];
   return S, Rels;
end intrinsic;

/* relations are on presentation generators;
   convert to relations on standard generators */

SUConvertToStandard := function (d, q, Rels)
   if d eq 3 and q eq 2 then return Universe (Rels), Rels; end if;
   A := SUStandardToPresentation (d, q);
   Rels := Evaluate (Rels, A);
   B := SUPresentationToStandard (d, q);
   C := Evaluate (B, A);
   U := Universe (C);
   W := Universe (Rels);
   tau := hom <U -> W | [W.i:i in [1..Ngens (W)]]>;
   T := [W.i^-1 * tau (C[i]): i in [1..Ngens (W)]];
   Rels cat:= T;
   return W, Rels;
end function;

// return presentation generators as words in standard generators 

SUStandardToPresentation := function (d, q)
   W := SLPGroup (7);
   S := [W.i: i in [1..7]];
   if IsEven (d) then 
      Z := S[1]; Z := Z^-1;
      V := S[2];
      tau := S[3]; tau := tau^-1;
      delta := S[4]; delta := delta^-1;
      U := S[5];
      sigma := S[6]; sigma := sigma^(V^2);
      Delta := S[7]^(V^2); Delta := Delta^-1;
      P := [Z, V, tau, delta, U, sigma, Delta];
   else
      if d eq 3 then
         rest := [W.0: i in [1..3]];
         // sequence [v, tau, Delta, t] 
         if IsOdd (q) then
            return [S[6], S[3], S[7], (S[7]^-1)^((q + 1) div 2) * S[1]] cat rest;
         else
            return [S[6], S[3], S[7], S[1]] cat rest;
         end if;
      end if;
      y := S[7]; V := S[2]; U := S[5]; tau := S[3]; x := S[6]; s := S[1]; 
      Gamma := (y^V)^-1;
      v := x^V;
      t := IsEven (q) select s else Gamma^((q^2 + q) div 2) * s^-1; 
      sigma := (v^(t * U), v^t)^t;
      // return [Gamma, t, U, V, sigma, tau, v]
      P := [Gamma, t, U, V, sigma, tau^-1, x^V];
   end if;
   return P;
end function;

// return standard generators as sequence [s, V, t, delta, U, x, y] 

SUPresentationToStandard := function (d, q)
   if d eq 3 then
      W := SLPGroup (4);
      P := [W.i: i in [1..4]];
      if IsOdd (q) then
         return [P[3]^((q + 1) div 2) * P[4],
                 P[1]^0, P[2], P[3]^(q + 1), P[1]^0, P[1], P[3]];
      else
         return [P[4], P[4]^0, P[2], P[3]^(q+1), P[3]^0, P[1], P[3]];
      end if;
   end if;

   W := SLPGroup (7);
   P := [W.i: i in [1..7]];
   if IsEven (d) then 
      Z := P[1]; Z := Z^-1;
      V := P[2];
      tau := P[3]; tau := tau^-1;
      delta := P[4]; delta := delta^-1;
      U := P[5];
      sigma := P[6]; sigma := sigma^(V^-2);
      Delta := P[7]^(V^-2); Delta := Delta^-1;
      S := [Z, V, tau, delta, U, sigma, Delta];
   else
      Gamma := P[1]; t := P[2]; U := P[3]; V := P[4]; 
      sigma := P[5]; tau := P[6]; v := P[7];
      Z := IsEven (q) select t else (Gamma^-1)^((q^2 + q) div 2) * t; 
      S := [Z^-1, V, tau^-1, Gamma^-(q + 1), U, v^(V^-1), (Gamma^-1)^(V^-1)];
   end if;
   return S;
end function;

// construct generator of centre of SU(d, q) as SLP in presentation generators 

SUGeneratorOfCentre := function (d, q, F)
   if Gcd (d, q + 1) eq 1 then return F.0; end if;
   n := d div 2;
   if IsOdd (d) then
      if d eq 3 then z := F.3^((q^2 - 1) div 3); return z; end if;
      Gamma := F.1; t := F.2; V := F.4;
      Z := IsEven (q) select t else t * Gamma^((q + 1) div 2);
      z := (Gamma * Z * V)^(2 * n * (q + 1) div Gcd (q + 1, 2*n + 1));
   else
      Z := F.1; U := F.5; V := F.2; Delta := F.7; 
      a := Valuation (q + 1, 2);
      b := Valuation (n, 2);
      if a gt b then 
         z := Z^2 * (Delta^(q - 1) * U * V^-1)^((n - 1) * (q + 1)  div (2 * Gcd (q + 1, n)));
      else
         z := (Delta^(q - 1) * U * V^-1)^((n - 1) * (q + 1)  div Gcd (q + 1, n));
      end if;
   end if;
   return z;
end function;
