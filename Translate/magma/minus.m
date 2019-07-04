import "sn.m": PresentationForSn;
import "signed.m": SignedPermutations;

forward MinusGeneratorOfCentre;
forward MinusConvertToStandard, MinusPresentationToStandard, MinusStandardToPresentation;

MinusDeltaMatrix := function (d, q, w, i)
   w0 := w^(q + 1);
   psi := w^((q + 1) div 2);
   assert psi eq -(w^((q^2 + q) div 2));
   assert psi^q eq -psi;
   MA := MatrixAlgebra (GF(q), d);
   A := (w^(q - 1) + w^(1 - q)) / 2;
   B := psi * (w^(1-q) - w^(q - 1))/ 2; 
   C := psi^-1 * (w^(1 - q) - w^(q - 1)) / 2;
   delta := Identity (MA);
   n := (d - 2) div 2;
   delta[2 * i - 1, 2 * i - 1] := w0^-1;
   delta[2 * i, 2 * i] := w0;

   delta[d - 1, d - 1] := A;
   delta[d - 1, d] := -C;
   delta[d, d - 1] := -B;
   delta[d, d] := A;

   return GL(d, q)!delta;
end function;

MinusEvenDeltaMatrix := function (d, q, w, i)
   w0 := w^(q + 1);
   MA := MatrixAlgebra (GF(q), d);
   A := (w^(1 - q) + w^(q - 1) + 1);
   B := (w^(1) + w^(q));
   C := (w^(-1) + w^(-q));
   delta := Identity (MA);
   n := (d - 2) div 2;
   delta[2 * i - 1, 2 * i - 1] := w0^-1;
   delta[2 * i, 2 * i] := w0;
   delta[d - 1, d - 1] := A;
   delta[d - 1, d] := C;
   delta[d, d - 1] := B;
   delta[d, d] := 1;
   return GL(d, q)!delta;
end function;

MinusGenerators := function (d, q)

   if d eq 4 then 
      return ClassicalStandardGenerators ("Omega-", d, q);
   end if;

   MA := MatrixAlgebra (GF(q), d);
   E := GF (q^2);
   w := PrimitiveElement (E);

   i := 1;
   if IsEven (q) then 
      delta := MinusEvenDeltaMatrix (d, q, w, i);
   else 
      delta := MinusDeltaMatrix (d, q, w, i);
   end if;

   n := (d - 2) div 2;
   z := Zero (MA);
   z[1,2] := 1;
   z[2,1] := 1;
   for i in [3..d - 1] do z[i,i] := 1; end for;
   if IsOdd (q) then 
      z[d - 1, d - 1] := -1;
   else  
      B := w + w^q; 
      z[d, d-1] := B;
   end if;
   z[d, d] := 1;

   tau := Identity (MA);
   if IsOdd (q) then
      s := 1;
      tau[1,1] := 1; tau[1,2] := s^2; tau[1,d - 1] := s;
      tau[d - 1, d - 1] := 1; tau[d - 1, 2] := 2 * s;
   else 
      B := w + w^q;
      tau[1,1] := 1; tau[1,2] := 1; tau[1,d - 1] := 1;
      tau[d, d] := 1; tau[d, 2] := B;
   end if;

   s := 1;
   sigma := Zero (MA);
   sigma[1,1] := 1; sigma[1,3] := s;
   sigma[4,4] := 1; sigma[4,2] := -s;
   for i in [2,3] cat [5..d] do sigma[i,i] := 1; end for;

   U := Zero (MA);
   U[1,3] := 1; U[3,1] := -1; U[2,4] := 1; U[4,2] := -1;
   for i in [5..d] do U[i,i] := 1; end for;

   V := Zero (MA);
   for i in [1..n - 1] do
      V[2 * i - 1, 2 * i + 1] := 1;
      V[2 * i, 2 * i + 2] := 1;
   end for;
   V[d - 3, 1] := (-1)^(n - 1);
   V[d - 2, 2] := (-1)^(n - 1);
   for i in [d - 1..d] do V[i,i] := 1; end for;
   gens := [GL(d, q) ! x : x in [z, tau, sigma, delta, U, V]];
   return gens, E, w;
end function;

Minus6Presentation := function (q)
   d := 4;
   Q, R := Internal_StandardPresentationForSU (d, q: Presentation := true);
   
   N := SLPGroup (5);
   z := N.1; tau := N.2; sigma := N.3; delta := N.4; U := N.5; 
   
   if IsOdd (q) then 
      images := [U, z * U^2, sigma, delta * (delta^-1)^U, z * U^2, tau^-1, delta];
   else 
      images := [U, z, sigma, delta * (delta^-1)^U, z, tau^1, delta];
   end if;
   
   eta := hom<Q-> N | images>;
   S := [eta (r): r in R];
   if IsOdd (q) then 
      Append (~S, delta^((q^2 - 1) div 2));
   end if;
   return N, S;
end function;

Minus_PresentationForN1 := function (d, q)
   F := SLPGroup (3);
   z := F.1; U := F.2; V := F.3;

   m := (d - 2) div 2;
   if IsOdd (q) then 
      S, R := SignedPermutations (m);
   elif IsEven (q) then  
      S, R := PresentationForSn (m);
   end if;
   phi := hom<S-> F | U, V>;
   R := [phi (r): r in R];

   n := d div 2;
   R1 := [];
   Append (~R1, (z, U^V) = 1);
   if n gt 4 then Append (~R1, (z, V * U^-1) = 1); end if;
   OMIT := true;
   if not OMIT then 
      Append (~R1, z^2 = 1);
      Append (~R1, (z, z^U) = 1);
      if IsOdd (q) then 
         Append (~R1, (z, U^2) = 1);
      end if;
   end if;

   Rels := [LHS (r) * RHS (r)^-1: r in R1] cat R;
   return F, Rels;
end function;

Minus_Order_N1 := function (d, q)
   n := d div 2;
   if IsOdd (q) then 
      return 2^(2*n - 3) * Factorial (n - 1);
   else 
      return 2^(n - 1) * Factorial (n - 1);
    end if;
end function;

Minus_PresentationForN := function (d, q) 
   F := SLPGroup (4);
   delta := F.1; z := F.2; U := F.3; V := F.4;
   S, R := Minus_PresentationForN1 (d, q);
   phi := hom<S-> F | z, U, V>;
   R := [phi (r): r in R];
   n := d div 2;
   R1 := [];
   Append (~R1, (delta, U^V) = 1);
   if n gt 4 then Append (~R1, (delta, V * U^-1) = 1); end if;

   OMIT := true;
   if not OMIT then 
      if IsOdd (q) then 
         Append (~R1, U^2 = (delta * (delta^-1)^U)^((q - 1) div 2));
      end if;
      Append (~R1, (delta, z^U) = delta^(q - 1));
      if IsOdd (q) then 
         Append (~R1, delta^((q^2 - 1) div 2) = 1);
      else 
         Append (~R1, delta^((q^2 - 1)) = 1);
      end if;
      Append (~R1, (delta, delta^U) = 1);
      Append (~R1, delta^z = delta^-1);
      Append (~R1, (delta^(q - 1), U) = 1);
   end if;
   
   Rels := [LHS (r) * RHS (r)^-1: r in R1] cat R;
   return F, Rels;
end function;

Minus_OrderN := function (d, q)
   n := d div 2;
   if IsOdd (q) then 
      return (q + 1) * (q-1)^(n-1) * 2^(n-2) * Factorial (n - 1);
   else 
      return (q + 1) * (q-1)^(n-1) * 2^(n-1) * Factorial (n - 1);
   end if;
end function;

Setup_MinusPresentation := function (d, q)
   if d eq 6 then
      return Minus6Presentation (q);
   end if;

   F := SLPGroup (6);
   z := F.1; tau := F.2; sigma := F.3; delta := F.4; U := F.5; V := F.6;

   f, p, e := IsPrimePower (q);

   S, R := Minus_PresentationForN (d, q);
   phi := hom<S-> F | delta, z, U, V>;
   R := [phi (r): r in R];
   n := d div 2;

   R1 := [];
   // centraliser of sigma in N 
   Append (~R1, (sigma, z^(V^2)) = 1);
   Append (~R1, (sigma, delta^(V^2)) = 1);
   OMIT := true;
   if not OMIT then 
      Append (~R1, (sigma, delta * delta^U) = 1);
      Append (~R1, (sigma, z * z^U * U) = 1);
   end if;
   if n gt 4 then Append (~R1, (sigma, U^(V^2)) = 1); end if;
   // elements generate the same group but for odd q reflects direct product
   if n gt 5 then 
      if IsOdd (q) then 
         Append (~R1, (sigma, V * U^-1 * (U^-1)^V) = 1); 
      else 
         Append (~R1, (sigma, V * U * U^V) = 1); 
      end if;
   end if;
   
   R2 := [];
   // centraliser of tau in N 
   Append (~R2, (tau, U^V) = 1);
   if n gt 4 then Append (~R2, (tau, V * U^-1) = 1); end if;
   if IsEven (q) then 
      Append (~R2, (tau, delta^(V^2) * (delta^-1)^(V)) = 1);
   end if;
   
   S, R3 := Minus6Presentation (q);
   phi := hom<S-> F | z, tau, sigma, delta, U>;
   R3 := [phi (r): r in R3];

   R4 := [];
   Append (~R4, (sigma, sigma^V) = sigma^(V * U^-1));
   Append (~R4, (sigma, sigma^(V * U^-1)) = 1);
   W := U^(V * U^-1);
   Append (~R4, (sigma, sigma^W) = 1);
   if n gt 4 then Append (~R4, (sigma, sigma^(V^2)) = 1); end if;

   R5 := [];
   Append (~R5, (sigma^V, tau) = 1);

   Rels := [LHS (r) * RHS (r)^-1: r in R1 cat R2 cat R4 cat R5] cat R cat R3;
   return F, Rels;
end function;

MinusPresentation := function (d, q: Projective := false, Presentation := false)
   assert d ge 4;
   assert IsEven (d);
   n := d div 2;

   if d eq 4 then
      Q, R := ClassicalStandardPresentation ("SL", 2, q^2: Projective := true);
      Q := SLPGroup (5);
      if IsEven (q) then
         R := Evaluate (R, [Q.1^Q.2, Q.1^Q.2, Q.1, Q.3]);
         Append (~R, (Q.1 * Q.1^Q.2 * Q.1) * Q.2^-1);
      else
         R := Evaluate (R, [Q.i: i in [1, 1, 2, 3]]);
      end if;
      Append (~R, Q.4);
      Append (~R, Q.5);
      return Q, R;
   end if;

   P, R := Setup_MinusPresentation (d, q);
   if Projective and IsOdd (n) and q mod 4 eq 3 then
      z := MinusGeneratorOfCentre (d, q, P);
      Append (~R, z);
   end if;
   if Presentation then return P, R; end if;

   // do conversion 
   S, Rels := MinusConvertToStandard (d, q, R);
   Rels := [w : w in Rels | w ne w^0];
   return S, Rels;
end function;

/* relations are on presentation generators;
   convert to relations on standard generators */

MinusConvertToStandard := function (d, q, Rels)
   A := MinusStandardToPresentation (d, q);
   Rels := Evaluate (Rels, A);
   B := MinusPresentationToStandard (d, q);
   C := Evaluate (B, A);
   U := Universe (C);
   W := Universe (Rels);
   tau := hom <U -> W | [W.i:i in [1..Ngens (W)]]>;
   T := [W.i^-1 * tau (C[i]): i in [1..Ngens (W)]];
   Rels cat:= T;
   return W, Rels;
end function;

/* express presentation generators as words in standard generators */

MinusStandardToPresentation := function (d, q)
   assert IsEven (d) and d gt 4;
   W := SLPGroup (5);
   if IsOdd (q) then 
      s := W.1; t := W.2; 
   else
      t := W.1; s := W.2; 
      // correct discrepancy between published s and code s 
      s := s^t; 
   end if;
   delta := W.3; U := W.4; V := W.5;

   z := s^V;
   tau := d mod 4 eq 2 select (t^V)^-1 else (t^V);

   if IsOdd (q) then
      Delta := (delta^V)^((q^2 - 1) div 2 - q);
   else
      Delta := (delta^-1)^V;
   end if;

   p := Characteristic (GF(q));
   if IsOdd (p) then
      sigma := (tau, tau^(z * U))^((p - 1) div 2);
   else
      F := GF(q^2);
      w := PrimitiveElement (F);
      w0 := w^(q + 1);
      m := Log (w0, w^2 + w^(2 * q));
      x := (tau^delta, tau^U)^(z * U);
      sigma := x^(Delta^(q-m));
   end if;

   if d eq 6 then 
      return [z, tau, sigma, Delta, U, U];
   else 
      return [z, tau, sigma, Delta, U, V];
   end if;
end function;

/* express standard generators as words in presentation generators */

MinusPresentationToStandard := function (d, q)
   assert IsEven (d) and d gt 4;
   W := SLPGroup (6);
   z := W.1; tau := W.2; sigma := W.3; Delta := W.4; U := W.5; V := W.6;

   t := d mod 4 eq 0 select tau^(V^-1) else (tau^-1)^(V^-1);

   if IsOdd (q) then
      delta := (Delta^(V^-1))^((q^2 - 1) div 2 - q);
   else
      delta := (Delta^-1)^(V^-1);
   end if;

   s := z^(V^-1);
   if IsEven (q) then 
      // correct discrepancy between published s and code s 
      s := s^(t^-1); 
      return [t, s, delta, U, V];
   else 
      return [s, t, delta, U, V];
   end if;
end function;

// generator of centre as word in presentation generators 

MinusGeneratorOfCentre := function (d, q, F) 
   assert IsEven (d) and d gt 4;
   n := d div 2;
   if IsOdd (n) and q mod 4 eq 3 then
      delta := F.4; 
      if d eq 6 then V := F.5; else V := F.6; end if;
      z := V^(n - 1) * delta^((q^2 - 1) div 4);
   else
      z := F.0;
   end if;
   return z;
end function;
