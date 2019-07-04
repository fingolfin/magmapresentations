import "sn.m": PresentationForSn;
import "sl2q.m": PresentationForSL2;
import "su3.m": SU3Presentation, SU32Presentation;

OddSUGenerators := function (d, q)
   assert IsOdd (d);

   MA := MatrixAlgebra (GF (q^2), d);
   F := GF (q^2);
   w := PrimitiveElement (F);

   // define tau 
   tau := Identity (MA);
   psi := IsEven (q) select 1 else w^((q + 1) div 2);
   tau[1,2] := -psi;

   // define Gamma 
   Gamma := [w^-1, w^q] cat [1: i in [3..d - 1]] cat [w^(1-q)];
   Gamma := DiagonalMatrix (Gamma);
   
   // define t
   t := Zero (MA);
   t[1,2] := 1; t[2][1] := 1; t[d,d] := -1;
   for i in [3 .. d - 1] do t[i, i] := 1; end for;

   // define v 
   alpha := 1;
   if IsEven (q) then
      phi := Trace(w, GF(q))^(-1) * w;
      assert phi eq w / (w + w^q);
   else
      phi := -1/2;
   end if;
   gamma := phi * alpha^(1 + q); 
   v := Zero (MA);
   v[1,1] := 1; v[1,2] := gamma; v[1,d] := alpha;
   for i in [2 .. d] do v[i, i] := 1; end for;
   v[d,2] := -alpha^q; 
   
   // U and V 
   S := ClassicalStandardGenerators ("SU", d, q);
   U := S[5];
   V := S[2];

   S := ClassicalStandardGenerators ("SU", d - 1, q);
   x := S[6]^(S[2]^2);
   sigma := Zero (MA);
   InsertBlock (~sigma, x, 1, 1);
   sigma[d,d] := 1;

   return [GL(d, q^2) | Gamma, t, U, V, sigma, tau, v];
end function;

Odd_SU_PresentationForN := function (n, q)
   F := SLPGroup (4);
   Gamma := F.1; t := F.2; U := F.3; V := F.4;

   Rels := [];

   S, R := PresentationForSn (n);
   tau := hom<S-> F | U, V>;
   R := [tau (r): r in R];
   
   OMIT := true;
   if not OMIT then 
      Append (~Rels, Gamma^(q^2 - 1) = 1);
      Append (~Rels, t^2 = 1);
      Append (~Rels, Gamma^t = Gamma^-q);
   end if;

   if n gt 2 then 
      Append (~Rels, (Gamma, U^V) = 1);
      Append (~Rels, (t, U^V) = 1);
   end if;
   if n gt 3 then 
      Append (~Rels, (Gamma, V * U) = 1);
      Append (~Rels, (t, V * U) = 1);
   end if;
   Append (~Rels, (Gamma, Gamma^U) = 1);
   Append (~Rels, (t, t^U) = 1);
   Append (~Rels, (Gamma, t^U) = 1);
   Rels := [LHS (r) * RHS (r)^-1: r in Rels] cat R;
   return F, Rels;
end function;

Order_Odd_SU_N := function (n, q)
   a := (q^2 - 1) * 2;
   return a^n * Factorial (n);
end function;

OddSUPresentation := function (d, q: Projective := false)
   assert IsOdd (d) and d ge 3;
   n := d div 2;
   if d eq 3 then
      if q eq 2 then 
         return SU32Presentation (: Projective := Projective);
      else 
         return SU3Presentation (q); 
      end if;
   end if;

   f, p, e := IsPrimePower (q);
   K := GF (q^2);
   w := PrimitiveElement (K);

   F := SLPGroup (7);
   Gamma := F.1; t := F.2; U := F.3; V := F.4; sigma := F.5; tau := F.6; v := F.7;
   Delta := Gamma * (Gamma^-1)^U;
   
   R := [];

   // centraliser of v 
   if n gt 2 then Append (~R, (U^V, v) = 1); end if;
   if n gt 3 then Append (~R, (V * U, v) = 1); end if;
   if IsEven (q) then 
      Append (~R, (t^U, v) = 1);
   else 
      m := (q^2 - 1) div 2;
      Append (~R, (t^U * Delta^m, v) = 1);
   end if;

   if n eq 2 and q mod 3 eq 1 then 
      Append (~R, (Gamma^(q - 1) * (Gamma^U)^3 * (t, Gamma^-1)^U, v) = 1);
   else 
      Append (~R, (Gamma^(q - 1) * (Gamma^U)^3, v) = 1);
   end if;

   if n gt 2 then 
      Append (~R, (Gamma^U * (Gamma^-1)^(V^2), v) = 1);
   end if;

   if IsEven (q) then
      Z := t; 
   else 
      Z := t * Gamma^((q + 1) div 2);
   end if;

   // centraliser of sigma 
   OMIT := true;
   if not OMIT then 
      if n gt 3 then Append (~R, (U^(V^2), sigma) = 1); end if;
      if n gt 4 then Append (~R, (V * U * U^V, sigma) = 1); end if;
      if n gt 2 then 
         Append (~R, (Gamma^(V^2), sigma) = 1); 
         Append (~R, (t^(V^2), sigma) = 1); 
      end if;
   end if;
   if IsEven (q) then 
      Append (~R, (U^t, sigma) = 1); 
   else 
      Append (~R, (U^t * Z^2, sigma) = 1); 
   end if; 
   Append (~R, (Gamma * Gamma^U, sigma) = 1); 

   Q, R_N := Odd_SU_PresentationForN (n, q);
   phi := hom<Q-> F | Gamma, t, U, V>;
   R_N := [phi (r): r in R_N];

   // tau = tau^-1 in char 2 
   Q, R_SU3 := SU3Presentation (q);
   if q eq 2 then
      phi := hom<Q-> F | v, v^(Gamma^U), Gamma^-1, t>;
   else 
      phi := hom<Q-> F | v, tau^-1, Gamma^-1, t>;
   end if;

   R_SU3 := [phi (r): r in R_SU3];

   Q, R_SL2 := PresentationForSL2 (p, 2 * e);
   W := IsEven (q) select U else U * Z^2;
   phi := hom<Q-> F | Delta, sigma, W>;
   R_SL2 := [phi (r): r in R_SL2];

   // Steinberg relations 
   R4 := [];
   Append (~R4, (v, v^U) = (sigma^-1)^(t^U));
   if q eq 4 then 
      Append (~R4, (v, v^(Gamma * U)) = sigma^(Gamma^7 * t^U)); 
      Append (~R4, (v^Gamma, sigma) = 1);
   end if;
   Append (~R4, (v, sigma) = 1);

   if IsOdd (q) then    
      a := (w^(-(q + 1) div 2)) / 2;
      r := Log (a);
      rhs := sigma^(Gamma^r * Z^U) * (v^-1)^U;
   else  
      a := w^q / (w + w^q);
      r := Log (a);
      rhs := sigma^(Gamma^r * Z^U) * (v^U);
   end if;
   Append (~R4, (v, sigma^U) = rhs);

   if q eq 2 then
      Append (~R4, (v, sigma^(Gamma * U)) = sigma^(Gamma * Z^U) * v^(U^(Gamma^-1)));
   end if;

   if n gt 2 then Append (~R4, (v, sigma^V) = 1); end if;
   Append (~R4, (v, tau^U) = 1); 
  
   // Steinberg relations for SU(2n, q) 
   R3 := [];
   Append (~R3, (sigma, tau) = 1);

   if IsEven (q) then 
      Append (~R3, (sigma, sigma^Z) = 1);
   else 
      Append (~R3, (sigma, sigma^Z) = (tau^2)^(Z * U));
   end if;

   if (q ne 3) then 
      E<w> := GF(q^2);
      w0 := w^(q+1);
      a := w^(2 * q) + w^2;
      m := Log (w0, a);
      Append (~R3, (sigma^Delta, sigma^Z) = tau^(Z * U * Delta^m));
   else
      Append (~R3, (sigma^Delta, sigma^Z) = 1);
   end if;

   Append (~R3, (sigma, tau^Z) = sigma^Z * (tau^-1)^(Z * U));

   // additional relation needed for SU(6, 2) -- probably only #2 required 
   if (n eq 3 and q eq 2) then
      Append (~R3, (sigma, sigma^(U^V * Delta)) = 1);
      Append (~R3, (sigma, sigma^(V * Delta)) = sigma^(V * U * Delta^-1));
   end if;

   if n gt 2 then 
      Append (~R3, (sigma, sigma^(U^V)) = 1);
      Append (~R3, (sigma, sigma^V) = sigma^(V * U));
   end if;
   if n lt 4 then  Append (~R3, (tau, tau^U) = 1); end if;
   if n eq 3 then Append (~R3, (tau, sigma^V) = 1); end if;
   if n gt 3 then Append (~R3, (sigma, sigma^(V^2)) = 1); end if;

   Rels := [LHS (r) * RHS (r)^-1: r in R cat R3 cat R4] cat R_SU3 cat R_SL2 cat R_N;
   return F, Rels;
end function;
